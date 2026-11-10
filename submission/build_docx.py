# Build submission/PROPOSAL.docx from PROPOSAL.md: the same four sample
# sections on one A4 page. Layout matches the PDF in structure, not in points:
# the DOCX uses 9mm top/bottom margins and 9.6pt body type (the PDF's CSS uses
# 12mm and 10.1pt), tuned so both render as exactly one page.
#
# Usage: python submission/build_docx.py
# Then:  powershell -NoProfile -ExecutionPolicy Bypass -File submission/docx_pages.ps1 -Docx <docx-path> -Pdf <pdf-path>

import io
import os
import re

from docx import Document
from docx.enum.text import WD_ALIGN_PARAGRAPH
from docx.oxml import OxmlElement
from docx.oxml.ns import qn
from docx.shared import Mm, Pt, RGBColor

ROOT = os.path.dirname(os.path.dirname(os.path.abspath(__file__)))
SOURCE = os.path.join(ROOT, 'PROPOSAL.md')
TARGET = os.path.join(ROOT, 'submission', 'PROPOSAL.docx')

BODY_FONT = 'Microsoft YaHei'
BODY_PT = 9.6
TITLE_PT = 18
HEADING_PT = 12.2


def set_font(run, name=BODY_FONT, size=BODY_PT, bold=None):
    run.font.name = name
    run.font.size = Pt(size)
    if bold is not None:
        run.font.bold = bold
    r_pr = run._element.get_or_add_rPr()
    fonts = r_pr.find(qn('w:rFonts'))
    if fonts is None:
        fonts = OxmlElement('w:rFonts')
        r_pr.append(fonts)
    fonts.set(qn('w:ascii'), name)
    fonts.set(qn('w:hAnsi'), name)
    fonts.set(qn('w:eastAsia'), name)


def add_runs(paragraph, text):
    """Split on `code` and **bold** and style each run."""
    for token in re.split(r'(`[^`]+`|\*\*[^*]+\*\*)', text):
        if not token:
            continue
        if token.startswith('`') and token.endswith('`'):
            run = paragraph.add_run(token[1:-1])
            set_font(run, 'Consolas', BODY_PT - 0.5)
        elif token.startswith('**') and token.endswith('**'):
            run = paragraph.add_run(token[2:-2])
            set_font(run, BODY_FONT, BODY_PT, bold=True)
        else:
            run = paragraph.add_run(token)
            set_font(run)


def bottom_border(paragraph):
    p_pr = paragraph._p.get_or_add_pPr()
    borders = OxmlElement('w:pBdr')
    bottom = OxmlElement('w:bottom')
    bottom.set(qn('w:val'), 'single')
    bottom.set(qn('w:sz'), '2')
    bottom.set(qn('w:space'), '1')
    bottom.set(qn('w:color'), 'BBBBBB')
    borders.append(bottom)
    p_pr.append(borders)


def build():
    doc = Document()
    section = doc.sections[0]
    section.page_width = Mm(210)
    section.page_height = Mm(297)
    section.top_margin = Mm(9)
    section.bottom_margin = Mm(9)
    section.left_margin = Mm(14)
    section.right_margin = Mm(14)

    normal = doc.styles['Normal']
    normal.font.name = BODY_FONT
    normal.font.size = Pt(BODY_PT)
    normal.element.rPr.rFonts.set(qn('w:eastAsia'), BODY_FONT)
    normal.paragraph_format.space_before = Pt(0)
    normal.paragraph_format.space_after = Pt(0)
    normal.paragraph_format.line_spacing = 0.95

    lines = io.open(SOURCE, encoding='utf-8').read().split('\n')
    for line in lines:
        text = line.rstrip()
        if not text:
            continue
        if text.startswith('# '):
            paragraph = doc.add_paragraph()
            paragraph.paragraph_format.space_after = Pt(5)
            run = paragraph.add_run(text[2:].strip())
            set_font(run, BODY_FONT, TITLE_PT, bold=True)
        elif text.startswith('## '):
            paragraph = doc.add_paragraph()
            paragraph.paragraph_format.space_before = Pt(6)
            paragraph.paragraph_format.space_after = Pt(1)
            paragraph.paragraph_format.keep_with_next = True
            run = paragraph.add_run(text[3:].strip())
            set_font(run, BODY_FONT, HEADING_PT, bold=True)
            bottom_border(paragraph)
        elif re.match(r'\d+\.\s', text):
            paragraph = doc.add_paragraph(style='List Number')
            paragraph.paragraph_format.left_indent = Mm(3.5)
            paragraph.paragraph_format.first_line_indent = Mm(-2.5)
            paragraph.paragraph_format.space_before = Pt(0)
            paragraph.paragraph_format.space_after = Pt(1)
            # The List Number style supplies the number; keeping the markdown
            # marker would print "1. 1." in front of every item.
            add_runs(paragraph, re.sub(r'^\d+\.\s+', '', text))
        elif text.startswith('- '):
            paragraph = doc.add_paragraph(style='List Bullet')
            paragraph.paragraph_format.left_indent = Mm(3.5)
            paragraph.paragraph_format.first_line_indent = Mm(-2.5)
            paragraph.paragraph_format.space_before = Pt(0)
            paragraph.paragraph_format.space_after = Pt(1)
            add_runs(paragraph, text[2:].strip())
        else:
            paragraph = doc.add_paragraph()
            paragraph.paragraph_format.space_after = Pt(2.5)
            add_runs(paragraph, text)

    doc.save(TARGET)
    print('wrote', TARGET)


if __name__ == '__main__':
    build()
