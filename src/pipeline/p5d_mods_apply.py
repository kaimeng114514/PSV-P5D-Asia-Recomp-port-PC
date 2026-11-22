# -*- coding: utf-8 -*-
# p5d_mods_apply.py: apply enabled Reloaded-II mods to the port's CPK archives.
# 2026-11-17: two findings from the game's own data: the TOC FileOffset is RELATIVE to the CPK content offset 0x800 (the
# entry bytes start at FileOffset+0x800), and entries must be CRILAYLA-compressed (the engine always runs the CRI
# decompressor; a raw entry makes the model vanish). So each mod file is CRILAYLA-encoded (literal-block encoder, valid),
# appended to the CPK raw (the engine accepts entries whose FileSize == ExtractSize), and the TOC row gets
# FileSize=ExtractSize=len(data) and FileOffset=pos-0x800 (the offset is relative to the CPK content start 0x800; the
# experiment with the ORIGINAL model re-written raw at the corrected offset showed it is this simple: the earlier fails
# were the missing 0x800).
import struct, os, sys, json, glob
LIB = os.environ.get('P5D_LIB') or 'C:/dev/nativ_lib/decrypted/PCSH10109'
CPKS = [LIB + '/app0/data/data.cpk', LIB + '/app0/data/vita.cpk']
MODS = LIB + '/recomp/mods'
STATE = MODS + '/cpk_state.json'
TOC_OFF = 0x810
CONTENT = 0x800

def crilayla_encode(x):
    usize = len(x) - 0x100
    raw_header = x[:0x100]
    out = x[0x100:][::-1]
    bits = []
    # CRILAYLA control bit: 1 = backreference, 0 = literal byte (CriPakTools' DecompressCRILAYLA). The first version had
    # this inverted, so the engine decoded garbage and the model vanished.
    for byte in out:
        bits.append(0)
        for b in range(7, -1, -1):
            bits.append((byte >> b) & 1)
    packed = bytearray(); acc = 0; nb = 0
    for bit in bits:
        acc = (acc << 1) | bit; nb += 1
        if nb == 8: packed.append(acc); acc = 0; nb = 0
    if nb: packed.append(acc << (8 - nb))
    stream = bytes(packed)[::-1]
    return b'CRILAYLA' + struct.pack('<LL', usize, len(stream)) + stream + raw_header

def parse(cpk):
    f = open(cpk, 'r+b'); f.seek(TOC_OFF); hb = f.read(32)
    if hb[:4] != b'@UTF': f.close(); return None
    size, rows_rel, str_rel, data_rel, tname, ncols, rowlen, nrows = struct.unpack('>IIIIIHHI', hb[4:32])
    base = TOC_OFF + 8
    f.seek(base + rows_rel); rows = f.read(rowlen * nrows)
    f.seek(base + str_rel); strs = f.read(min(size - str_rel, 8 << 20))
    return dict(path=cpk, f=f, base=base, rows_rel=rows_rel, rowlen=rowlen, nrows=nrows, rows=rows, strs=strs)

def s_at(h, o):
    e = h['strs'].find(b'\0', o)
    return h['strs'][o:e].decode('utf-8', 'replace')

def find(h, target):
    t = target.lower()
    for r in range(h['nrows']):
        row = h['rows'][r*h['rowlen']:(r+1)*h['rowlen']]
        do, no, fs, es, off, ident = struct.unpack('>IIIIQI', row)
        dirn = s_at(h, do); name = s_at(h, no)
        full = (dirn + name if (not dirn or dirn.endswith('/')) else dirn + '/' + name).lower()
        if full == t or full.endswith('/' + t) or name.lower() == t:
            return r, fs, es, off, ident, dirn, name
    return None

def row_abs(h, r):
    return h['base'] + h['rows_rel'] + r * h['rowlen']

def enabled_mods():
    en = set()
    ini = os.path.join(MODS, 'mods.ini')
    if os.path.exists(ini):
        for line in open(ini, encoding='utf-8-sig', errors='replace'):
            line = line.strip()
            if line.startswith('enabled='): en.add(line[8:])
    out = []
    for d in sorted(glob.glob(MODS + '/*')):
        if not os.path.isdir(d) or os.path.basename(d) not in en: continue
        data = os.path.join(d, 'Data')
        if not os.path.isdir(data): data = d
        for dp, _, fns in os.walk(data):
            for fn in fns:
                p = os.path.join(dp, fn)
                out.append((os.path.relpath(p, data).replace('\\', '/'), p))
    return out

def restore(st):
    by = {}
    for key, rec in st.items():
        by.setdefault(rec['cpk'], []).append(rec)
    for cpk, recs in by.items():
        if not os.path.exists(cpk): continue
        f = open(cpk, 'r+b')
        for rec in recs:
            f.seek(rec['row_abs'] + 8); f.write(struct.pack('>II', rec['fs'], rec['es']))
            f.seek(rec['row_abs'] + 16); f.write(struct.pack('>Q', rec['off']))
        cut = min(r['orig_end'] for r in recs)
        f.truncate(cut); f.flush(); os.fsync(f.fileno()); f.close()
        print('restored', os.path.basename(cpk), len(recs), 'entries, size', cut)

def apply():
    state = json.load(open(STATE)) if os.path.exists(STATE) else {}
    restore(state); state = {}
    files = enabled_mods()
    print('mod files:', len(files))
    for rel, src in files:
        done = False
        for cpkp in CPKS:
            if not os.path.exists(cpkp): continue
            h = parse(cpkp)
            if not h: continue
            m = find(h, rel)
            if not m: h['f'].close(); continue
            r, fs, es, off, ident, dirn, name = m
            data = open(src, 'rb').read()
            f = h['f']; f.seek(0, 2); end = f.tell()
            pos = (end + 0x7ff) & ~0x7ff
            f.seek(pos); f.write(data); f.flush(); os.fsync(f.fileno())
            ra = row_abs(h, r)
            f.seek(ra + 8); f.write(struct.pack('>II', len(data), len(data)))
            f.seek(ra + 16); f.write(struct.pack('>Q', pos - CONTENT))
            f.flush(); os.fsync(f.fileno())
            state[os.path.basename(cpkp) + ':' + rel] = dict(cpk=cpkp, row_abs=ra, fs=fs, es=es, off=off, orig_end=end)
            f.close()
            print('patched', os.path.basename(cpkp), rel, 'raw', len(data), '@', pos - CONTENT)
            done = True; break
        if not done: print('no CPK entry for', rel)
    json.dump(state, open(STATE, 'w'), indent=1)
    print('applied', len(state), 'entries')

if __name__ == '__main__':
    if len(sys.argv) > 1 and sys.argv[1] == 'restore':
        st = json.load(open(STATE)) if os.path.exists(STATE) else {}
        restore(st); json.dump({}, open(STATE, 'w')); print('restored all')
    else:
        apply()
