#!/usr/bin/env python3
"""Generates kendrah-icon.svg and kendrah-banner.svg (text converted to outlines, so no font is needed to view them).
Needs: fontTools and DejaVu fonts (fonts-dejavu-core). Usage: python3 make_brand.py"""
from fontTools.ttLib import TTFont
from fontTools.pens.svgPathPen import SVGPathPen
from fontTools.pens.transformPen import TransformPen

FD = "/usr/share/fonts/truetype/dejavu/"
BOLD, MONO, MONOB = FD + "DejaVuSans-Bold.ttf", FD + "DejaVuSansMono.ttf", FD + "DejaVuSansMono-Bold.ttf"
CYAN, VIOLET, AMBER = "#22d3ee", "#a78bfa", "#fb923c"

def text_path(fontfile, text, size, x, y, spacing=0.0):
    f = TTFont(fontfile); gs = f.getGlyphSet(); cmap = f.getBestCmap(); upm = f["head"].unitsPerEm
    s = size / upm; pen = SVGPathPen(gs); cx = x
    for ch in text:
        g = cmap[ord(ch)]
        pen_t = TransformPen(pen, (s, 0, 0, -s, cx, y))
        gs[g].draw(pen_t)
        cx += gs[g].width * s + spacing
    return pen.getCommands(), cx

def width(fontfile, text, size, spacing=0.0):
    return text_path(fontfile, text, size, 0, 0, spacing)[1] - spacing

MARK = f'''<g fill="none" stroke-width="58" stroke-linecap="round" stroke-linejoin="round">
<path d="M176 256L338 126" stroke="{VIOLET}"/><path d="M176 256L338 386" stroke="{AMBER}"/><path d="M176 124V388" stroke="{CYAN}"/></g>
<circle cx="176" cy="256" r="17" fill="#0b1020"/><circle cx="176" cy="256" r="8" fill="#ffffff"/>'''

icon = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 512 512" width="512" height="512" role="img" aria-label="K.E.N.D.R.A.H icon">
<title>K.E.N.D.R.A.H</title>
<defs><linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#121a33"/><stop offset="1" stop-color="#070a16"/></linearGradient>
<radialGradient id="gl" cx="0.7" cy="0.3" r="0.7"><stop offset="0" stop-color="{VIOLET}" stop-opacity="0.22"/><stop offset="1" stop-color="{VIOLET}" stop-opacity="0"/></radialGradient></defs>
<rect width="512" height="512" rx="116" fill="url(#bg)"/><rect width="512" height="512" rx="116" fill="url(#gl)"/>
<rect x="6" y="6" width="500" height="500" rx="110" fill="none" stroke="#ffffff" stroke-opacity="0.10" stroke-width="3"/>
<g transform="translate(34 0)">{MARK}</g>
</svg>
'''
open("kendrah-icon.svg", "w").write(icon)

W, H = 1280, 360
title, tx = text_path(BOLD, "K.E.N.D.R.A.H", 74, 228, 192, 3)
tw = width(BOLD, "K.E.N.D.R.A.H", 74, 3)
sub, _ = text_path(MONO, "Unified Spectrum Programming Language", 27, 230, 246, 0.6)
chips = ""; cx = 230
for label, col in (("hardware", CYAN), ("application", VIOLET), ("declarative", AMBER)):
    w = width(MONO, label, 17, 0.5) + 52
    p, _ = text_path(MONO, label, 17, cx + 36, 306, 0.5)
    chips += f'<rect x="{cx}" y="282" width="{w:.0f}" height="34" rx="17" fill="#ffffff" fill-opacity="0.06" stroke="{col}" stroke-opacity="0.75"/><circle cx="{cx+19}" cy="299" r="5" fill="{col}"/><path d="{p}" fill="#c9d1d9"/>'
    cx += w + 14
code = ""
for i, (t, col) in enumerate((("@layer(hardware)", CYAN), ("@layer(application)", VIOLET), ("@layer(declarative)", AMBER))):
    p, _ = text_path(MONOB, t, 20, 936, 120 + i * 62, 0)
    code += f'<rect x="912" y="{92+i*62}" width="300" height="46" rx="12" fill="#ffffff" fill-opacity="0.05" stroke="{col}" stroke-opacity="0.55"/><rect x="912" y="{92+i*62}" width="6" height="46" rx="3" fill="{col}"/><path d="{p}" fill="{col}"/>'
    if i < 2: code += f'<path d="M1062 {138+i*62}V{154+i*62}" stroke="#8b949e" stroke-opacity="0.5" stroke-width="2" stroke-dasharray="3 3"/>'
banner = f'''<svg xmlns="http://www.w3.org/2000/svg" viewBox="0 0 {W} {H}" width="{W}" height="{H}" role="img" aria-label="K.E.N.D.R.A.H - Unified Spectrum Programming Language">
<title>K.E.N.D.R.A.H - Unified Spectrum Programming Language</title>
<defs><linearGradient id="bg" x1="0" y1="0" x2="1" y2="1"><stop offset="0" stop-color="#0b1020"/><stop offset="1" stop-color="#151b33"/></linearGradient>
<radialGradient id="g1" cx="0.12" cy="0.5" r="0.5"><stop offset="0" stop-color="{CYAN}" stop-opacity="0.16"/><stop offset="1" stop-color="{CYAN}" stop-opacity="0"/></radialGradient>
<radialGradient id="g2" cx="0.9" cy="0.5" r="0.5"><stop offset="0" stop-color="{AMBER}" stop-opacity="0.14"/><stop offset="1" stop-color="{AMBER}" stop-opacity="0"/></radialGradient>
<linearGradient id="bar" x1="0" y1="0" x2="1" y2="0"><stop offset="0" stop-color="{CYAN}"/><stop offset="0.5" stop-color="{VIOLET}"/><stop offset="1" stop-color="{AMBER}"/></linearGradient>
<pattern id="grid" width="40" height="40" patternUnits="userSpaceOnUse"><path d="M40 0H0V40" fill="none" stroke="#ffffff" stroke-opacity="0.04"/></pattern></defs>
<rect width="{W}" height="{H}" rx="26" fill="url(#bg)"/><rect width="{W}" height="{H}" rx="26" fill="url(#grid)"/>
<rect width="{W}" height="{H}" rx="26" fill="url(#g1)"/><rect width="{W}" height="{H}" rx="26" fill="url(#g2)"/>
<rect x="0" y="{H-8}" width="{W}" height="8" fill="url(#bar)" opacity="0.9"/>
<g transform="translate(52 76) scale(0.3906)"><rect width="512" height="512" rx="116" fill="#070a16"/><rect x="6" y="6" width="500" height="500" rx="110" fill="none" stroke="#ffffff" stroke-opacity="0.12" stroke-width="3"/><g transform="translate(34 0)">{MARK}</g></g>
<path d="{title}" fill="#f0f6fc"/><rect x="230" y="212" width="{tw:.0f}" height="3" rx="1.5" fill="url(#bar)"/>
<path d="{sub}" fill="#8b949e"/>
{chips}
{code}
</svg>
'''
open("kendrah-banner.svg", "w").write(banner)
print("ok", len(icon), len(banner))
