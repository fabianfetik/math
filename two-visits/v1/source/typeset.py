"""Generate portable article TeX from manuscript.md using Pandoc.

Run this script from any directory. The sibling manuscript and figures are
the complete inputs. Compile paper.tex with pdflatex from this directory.
"""
from pathlib import Path
import re
import subprocess

ROOT = Path(__file__).resolve().parent

PREAMBLE = r'''% Generated from the accompanying manuscript.md by typeset.py.
\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[a4paper,margin=25mm]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage{graphicx,longtable,booktabs,array,calc}
\usepackage[hidelinks,pdfencoding=auto,hypertexnames=false]{hyperref}
\hypersetup{
  pdftitle={@@TITLE@@},
  pdfauthor={@@AUTHOR@@}
}
\urlstyle{same}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\setlength{\emergencystretch}{1.5em}
\setlength{\LTpre}{0.7em}
\setlength{\LTpost}{0.7em}
\widowpenalty=10000
\clubpenalty=10000
\allowdisplaybreaks[1]
\title{@@TITLE@@}
\author{@@AUTHOR@@}
\date{}
\begin{document}
\maketitle
'''

def convert(markdown):
    result = subprocess.run(
        ['pandoc', '--from=markdown+tex_math_single_backslash', '--to=latex',
         '--wrap=none', '--no-highlight'],
        input=markdown, capture_output=True, text=True, check=True)
    if result.stderr.strip():
        raise RuntimeError(result.stderr)
    return result.stdout


def read_manuscript(source):
    """Read the title, author, abstract, body and references from one source."""
    front, remainder = source.split('## Abstract\n\n', 1)
    header = re.fullmatch(r'# ([^\n]+)\n\n([^\n]+)', front.strip())
    if header is None:
        raise ValueError('Expected a title and author before the abstract')
    title, author = header.groups()
    abstract, remainder = remainder.split('\n## Introduction', 1)
    body, reference_text = ('## Introduction' + remainder).split('\n## References\n\n', 1)
    parts = re.split(r'^- \[([A-Z][A-Za-z0-9+]*)\] ', reference_text, flags=re.M)
    if parts[0].strip() or len(parts) < 3:
        raise ValueError('Expected labelled reference entries')
    references = {}
    for label, text in zip(parts[1::2], parts[2::2]):
        if label in references or not text.strip():
            raise ValueError('Duplicate or empty reference: ' + label)
        references[label] = text.strip()
    return title, author, abstract.strip(), body, references


def cite_references(body, references):
    """Convert labelled citations, including multiple labels and location notes."""
    def citation(match):
        fields = [field.strip() for field in match.group(1).split(',')]
        if fields[0] not in references:
            if re.fullmatch(r'[A-Z]{2,}\+?\d{2,4}', fields[0]):
                raise ValueError('Unknown reference: ' + fields[0])
            return match.group(0)
        if all(field in references for field in fields):
            return r'\cite{' + ','.join('ref:' + field for field in fields) + '}'
        if len(fields) != 2 or re.fullmatch(r'[A-Z]{2,}\+?\d{2,4}', fields[1]):
            raise ValueError('Invalid citation: ' + match.group(0))
        note = convert(fields[1]).strip()
        return r'\cite[' + note + ']{ref:' + fields[0] + '}'
    return re.sub(r'(?<!\\)\[([^\]\n]+)\]', citation, body)


def main():
    source = (ROOT / 'manuscript.md').read_text(encoding='utf-8')
    title, author, abstract, body, references = read_manuscript(source)
    preamble = PREAMBLE.replace('@@TITLE@@', convert(title).strip())
    preamble = preamble.replace('@@AUTHOR@@', convert(author).strip())
    body = cite_references(body, references)
    body = body.replace('figures/repair-example.svg', 'figures/repair-example.pdf')
    body = body.replace('∎', r'\(\square\)')
    # Promote section levels and let LaTeX supply the existing section numbers.
    body = re.sub(r'^(#{2,4}) (\d+(?:\.\d+)*\. )?',
                  lambda m: m.group(1)[1:] + ' ', body, flags=re.M)
    tex = convert(body)
    tex = tex.replace(r'\section{Introduction}', r'\section*{Introduction}')
    tex = tex.replace(r'\subsection{Proof overview}', r'\subsection*{Proof overview}')
    tex = re.sub(r'\\subsection\{(Lemma [^\n]+)\}', r'\\subsection*{\1}', tex)
    tex = tex.replace(r'\subsubsection{', r'\subsection*{')

    def display(match):
        math = match.group(1).strip() + '\n'
        tag = re.search(r'\\tag\{(\d+\.\d+)\}', math)
        if tag:
            return '\\begin{equation}\n' + math + '\\label{eq:' + tag.group(1) + '}\n\\end{equation}'
        return match.group(0)

    tex = re.sub(r'\\\[(.*?)\\\]', display, tex, flags=re.S)
    # Keep a display in the paragraph that introduces it. A blank paragraph
    # would permit a page break between a short lead-in and its equation.
    tex = tex.replace('\n\n\\[\n', '\n\\[\n')
    tex = tex.replace('\n\n\\begin{equation}\n', '\n\\begin{equation}\n')
    tex = re.sub(r'(?<![\w\\])\((\d+\.\d+)\)', r'\\eqref{eq:\1}', tex)
    tex = tex.replace(r'\includegraphics{figures/repair-example.pdf}',
                      r'\includegraphics[width=\linewidth]{figures/repair-example.pdf}')
    # Both tables are short; keep each complete instead of splitting longtables.
    tex = tex.replace(r'\begin{longtable}[]', '\\begin{center}\n\\begin{tabular}')
    tex = tex.replace(r'\endhead', '')
    tex = re.sub(r'\\bottomrule\\noalign\{\}\s*\\endlastfoot', '', tex)
    tex = tex.replace(r'\end{longtable}', '\\bottomrule\n\\end{tabular}\n\\end{center}')
    # The short calendar pseudocode should remain a complete block.
    tex = re.sub(r'\\begin\{verbatim\}.*?\\end\{verbatim\}',
                 lambda m: '\\noindent\\begin{minipage}{\\linewidth}\n' +
                 m.group(0) + '\n\\end{minipage}', tex, flags=re.S)
    # Distinguish mathematical theorem statements from ordinary paragraph emphasis.
    for name in ('Theorem A', 'Theorem B', 'Corollary C'):
        pattern = r'\\textbf\{' + name + r' \(([^}]+)\)\.\} ([^\n]+)'
        tex = re.sub(pattern, lambda m: '\\begin{quote}\n\\begin{minipage}{\\linewidth}\n\\textbf{' + name +
                     ' (' + m.group(1) + ').} ' + m.group(2) +
                     '\n\\end{minipage}\n\\end{quote}', tex)
    widest = max(references, key=len)
    bibliography = '\\begin{thebibliography}{' + widest + '}\n'
    for label, text in references.items():
        bibliography += '\\bibitem[' + label + ']{ref:' + label + '}\n' + convert(text)
    bibliography += '\\end{thebibliography}\n\\end{document}\n'
    output = preamble + '\\begin{abstract}\n' + convert(abstract) + '\\end{abstract}\n' + tex + bibliography
    (ROOT / 'paper.tex').write_text(output, encoding='utf-8')
    print('Generated portable paper.tex')


if __name__ == '__main__':
    main()
