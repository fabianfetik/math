#!/usr/bin/env python3
"""Typeset the Markdown article with Pandoc, pdfLaTeX and the supplied vector figures."""

from collections import Counter
from pathlib import Path
import re
import subprocess


HERE = Path(__file__).resolve().parent
SOURCE = HERE / "source"
FIGURE = re.compile(r"^!\[([^\n]+)\]\(figures/(fig[1-8]-[a-z0-9-]+)\.svg\)$", re.M)
TAG = re.compile(r"\\tag\{([A-Za-z0-9]+)\}")
STATEMENT = re.compile(
    r"^\\textbf\{(?:"
    r"(?:Theorem|Lemma|Proposition|Corollary) (?:[A-Z]\.)?\d+[^{}\n]*"
    r"|[^{}\n]+(?:[Ll]emma|Corollary)"
    r"|Universal absorbing core|Robust fractional matching|External Matching Input"
    r")\.\}",
    re.M,
)
LABELLED_PARAGRAPH = re.compile(
    r"^\\textbf\{(?:Proof(?:\.|:[^{}\n]+)|Use of AI tools\.|License\.)\}",
    re.M,
)
PREAMBLE = r"""
\documentclass[11pt,a4paper]{article}
\usepackage[T1]{fontenc}
\usepackage[utf8]{inputenc}
\usepackage{lmodern}
\usepackage[a4paper,margin=25mm]{geometry}
\usepackage{amsmath,amssymb,amsthm}
\usepackage{microtype}
\usepackage{graphicx,longtable,booktabs,array,calc,float}
\usepackage[font=small,labelfont=bf]{caption}
\usepackage[hidelinks,pdfencoding=auto]{hyperref}
\input{glyphtounicode}
\pdfgentounicode=1
\pdfsuppressptexinfo=15
\pdfinfoomitdate=1
\pdftrailerid{}
\input{font-licenses.tex}
\hypersetup{pdftitle={@@TITLE@@},pdfauthor={@@AUTHOR@@}}
\urlstyle{same}
\providecommand{\tightlist}{\setlength{\itemsep}{0pt}\setlength{\parskip}{0pt}}
\setcounter{secnumdepth}{4}
\setlength{\emergencystretch}{2em}
\setlength{\LTpre}{0.7em}
\setlength{\LTpost}{0.7em}
\setlength{\textfloatsep}{16pt plus 3pt minus 3pt}
\setlength{\intextsep}{14pt plus 3pt minus 2pt}
\newcommand{\statementstart}{\par\addvspace{6pt plus 1pt minus 1pt}\noindent}
\newcommand{\labelledparagraphstart}{\par\addvspace{3pt plus 1pt minus 1pt}\noindent}
\renewcommand{\topfraction}{0.88}
\renewcommand{\bottomfraction}{0.80}
\renewcommand{\textfraction}{0.10}
\renewcommand{\floatpagefraction}{0.68}
\widowpenalty=10000
\clubpenalty=10000
\allowdisplaybreaks[1]
\title{@@DISPLAY_TITLE@@}
\author{@@AUTHOR@@}
\date{@@DATE@@}
\begin{document}
\maketitle
"""


def convert(markdown):
    result = subprocess.run(
        ["pandoc", "--from=markdown+tex_math_single_backslash",
         "--to=latex", "--wrap=none", "--no-highlight"],
        input=markdown, text=True, capture_output=True, check=True,
    )
    if result.stderr.strip():
        raise ValueError(result.stderr.strip())
    return result.stdout.strip()


def parse_front(front):
    fields = [line.strip() for line in front.splitlines() if line.strip() and not line.startswith(">")]
    if len(fields) != 3 or not fields[0].startswith("# "):
        raise ValueError("Expected a title, author and date")
    title, author, date = fields
    title = convert(title[2:])
    return {"TITLE": title, "DISPLAY_TITLE": title.replace(": ", r":\\", 1),
            "AUTHOR": convert(author), "DATE": convert(date)}


def replace_headings(body):
    def appendix(match):
        prefix = r"\appendix" if match[1] == "A" else ""
        return "\n" + prefix + "\n\n## " + match[2]

    body = re.sub(r"^## Appendix ([A-Z])\. (.*)$", appendix, body, flags=re.M)
    body = re.sub(r"^(#{2,5}) (?:[A-Z]|\d+)(?:\.\d+)* (.*)$", r"\1 \2", body, flags=re.M)
    return re.sub(r"^(#{2,5}) ", lambda m: m[1][1:] + " ", body, flags=re.M)


def latex_article(markdown):
    front, remainder = markdown.split("## Abstract\n\n", 1)
    abstract, body = remainder.split("\n## 1 Introduction\n", 1)
    body, reference_text = ("## 1 Introduction\n" + body).split("\n## References\n\n", 1)
    parts = re.split(r"^- \[([A-Z][A-Za-z0-9]+)\] ", reference_text, flags=re.M)
    if parts[0].strip() or len(parts) % 2 == 0:
        raise ValueError("Expected a list of named references")
    pairs = [(label, text.strip()) for label, text in zip(parts[1::2], parts[2::2])]
    references = dict(pairs)
    if len(pairs) != len(references):
        raise ValueError("Duplicate bibliography keys")

    def cite(match):
        key, detail = match[1], match[2]
        if key not in references:
            return match[0]
        note = f"[{convert(detail)}]" if detail else ""
        return f"\\cite{note}{{{key}}}"

    body = re.sub(r"(?<![\\!])\[([A-Z][A-Za-z0-9]+)(?:, ([^\]\n]+))?\](?!\()",
                  cite, body)
    captions = {}

    def place_figure(match):
        caption, name = match.groups()
        number = int(name[3])
        if number in captions or not (SOURCE / "figures" / f"{name}.pdf").is_file():
            raise ValueError(f"Duplicate or missing figure {name}")
        captions[number] = name
        # Keep Markdown captions in the article and size the figure at the text width.
        # Place the switch and endpoint illustrations before the arguments that follow.
        placement = "H" if number in (4, 5) else "!htbp"
        return (rf"\begin{{figure}}[{placement}]" + "\n" +
                r"\centering" + "\n" +
                rf"\includegraphics[width=\linewidth]{{figures/{name}.pdf}}" + "\n" +
                rf"\caption{{{convert(caption)}}}" + "\n" +
                rf"\label{{fig:{name}}}" + "\n" +
                r"\end{figure}")

    body = FIGURE.sub(place_figure, body)
    if list(captions) != list(range(1, 9)):
        raise ValueError("Expected figures 1 through 8 in reading order")
    body = re.sub(r"\bFigure ([1-8])\b",
                  lambda m: rf"\autoref{{fig:{captions[int(m[1])]}}}", body)
    latex = convert(replace_headings(body))
    latex = STATEMENT.sub(lambda match: r"\statementstart" + match[0], latex)
    latex = LABELLED_PARAGRAPH.sub(lambda match: r"\labelledparagraphstart" + match[0], latex)
    for heading in ("Acknowledgements", "Declarations"):
        latex = latex.replace(rf"\section{{{heading}}}", rf"\section*{{{heading}}}")
    closing = r"\section*{Acknowledgements}"
    if latex.count(closing) != 1:
        raise ValueError("Expected one acknowledgements heading")
    latex = latex.replace(closing, r"\begin{samepage}" + "\n" + closing, 1)

    # Keep each equation's selected tag and give it a stable anchor in the TeX source.
    tags = TAG.findall(latex)
    repeated = [tag for tag, count in Counter(tags).items() if count != 1]
    if repeated:
        raise ValueError(f"Repeated equation tags {repeated}")
    def numbered_display(match):
        math = match[1]
        tag = TAG.search(math)
        if tag is None:
            return match[0]
        # amsmath requires a tag on the enclosing equation, outside any split.
        math = TAG.sub("", math, count=1).strip()
        return (r"\begin{equation}" + "\n" + math + "\n"
                + tag[0] + rf"\label{{eq:{tag[1]}}}" + "\n" + r"\end{equation}")

    latex = re.sub(r"(?<!\\)\\\[(.*?)(?<!\\)\\\]", numbered_display, latex, flags=re.S)
    if latex.count(r"\label{eq:") != len(tags):
        raise ValueError("Every equation tag must belong to a displayed equation")
    header = PREAMBLE
    for key, value in parse_front(front).items():
        header = header.replace(f"@@{key}@@", value)
    bibliography = "\n".join(
        rf"\bibitem[{key}]{{{key}}}" + "\n" + convert(entry) for key, entry in pairs
    )
    return (header + "\\begin{abstract}\n" + convert(abstract) + "\n\\end{abstract}\n"
            + latex + "\n\\end{samepage}\n\\clearpage\n"
            + "\\begin{thebibliography}{" + max(references, key=len) + "}\n"
            + "\\small\n\\setlength{\\itemsep}{0pt plus 1pt}\n"
            + bibliography + "\n\\end{thebibliography}\n\\end{document}\n")


if __name__ == "__main__":
    article = (HERE / "manuscript.md").read_text(encoding="utf-8")
    (SOURCE / "paper.tex").write_text(latex_article(article), encoding="utf-8")
