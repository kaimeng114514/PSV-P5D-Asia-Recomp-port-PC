
#version 450
// M1663k: the dynamic vibrance on the final presented image (GPU). The author found 100% too strong: the curve is now 2x
// at full strength (was 4x) -- a light, normal lift; the 強烈模式 was already removed.
layout(set = 2, binding = 0) uniform sampler2D t;
layout(set = 3, binding = 0, std140) uniform PostU { vec2 rcp; vec2 origin; vec4 k; } u;   /* k.y: strength 0..1 */
layout(location = 0) out vec4 o;
void main() {
	vec2 uv = (gl_FragCoord.xy - u.origin) * u.rcp;
	vec3 c = textureLod(t, uv, 0.0).rgb;
	float mx = max(c.r, max(c.g, c.b));
	float mn = min(c.r, min(c.g, c.b));
	float sat = mx - mn;
	float boost = u.k.y * 2.0 * (1.0 - sat);
	float l = dot(c, vec3(0.299, 0.587, 0.114));
	vec3 r = l + (c - l) * (1.0 + boost);
	o = vec4(clamp(r, 0.0, 1.0), 1.0);
}
