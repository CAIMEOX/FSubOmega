#!/usr/bin/env python3
from pathlib import Path
import re
import shutil
import subprocess
import tempfile
import xml.etree.ElementTree as ET


ASSETS = Path(__file__).resolve().parent
PANELS = (
    ("syntax-kinding", "Syntax, contexts, kinding, and beta conversion"),
    ("subtyping", "The nine declarative subtyping rules"),
    ("typing", "The six typing rules and the old-language fragment"),
)
SVG = "http://www.w3.org/2000/svg"


def run(*args: str, cwd: Path) -> str:
    result = subprocess.run(args, cwd=cwd, text=True, capture_output=True)
    if result.returncode:
        raise SystemExit(result.stdout + result.stderr)
    return result.stdout + result.stderr


def describe_svg(path: Path, description: str) -> None:
    """Add accessible descriptions without changing the rendered geometry."""
    ET.register_namespace("", SVG)
    ET.register_namespace("xlink", "http://www.w3.org/1999/xlink")
    tree = ET.parse(path)
    root = tree.getroot()
    root.set("role", "img")
    root.set("aria-labelledby", "title description")
    title = ET.Element(f"{{{SVG}}}title", {"id": "title"})
    title.text = description
    desc = ET.Element(f"{{{SVG}}}desc", {"id": "description"})
    desc.text = "Full F-sub-omega with beta conversion. Generated from assets/rules.tex using mathpartir."
    root.insert(0, title)
    root.insert(1, desc)
    if root.findall(f".//{{{SVG}}}text") or root.findall(f".//{{{SVG}}}image"):
        raise SystemExit(f"Expected vector outlines without font or bitmap dependencies: {path}")
    tree.write(path, encoding="utf-8", xml_declaration=True)


def main() -> None:
    for command in ("pdflatex", "pdfinfo", "pdftocairo"):
        if shutil.which(command) is None:
            raise SystemExit(f"Missing {command}; see the rule-assets build instructions in README.md.")

    with tempfile.TemporaryDirectory(prefix="fsubomega-rules-") as directory:
        work = Path(directory)
        shutil.copyfile(ASSETS / "rules.tex", work / "rules.tex")
        outputs = []
        for theme in ("light", "dark"):
            name = f"rules-{theme}"
            source = (r"\def\RulesDark{1}" if theme == "dark" else "") + r"\input{rules.tex}"
            run("pdflatex", "-interaction=nonstopmode", "-halt-on-error", "-file-line-error",
                "-no-shell-escape", f"-jobname={name}", source, cwd=work)
            log = (work / f"{name}.log").read_text(errors="replace")
            if "Overfull \\hbox" in log or "Overfull \\vbox" in log:
                raise SystemExit(f"LaTeX overflow in {theme} rendering:\n{log}")

            info = run("pdfinfo", f"{name}.pdf", cwd=work)
            pages = re.search(r"^Pages:\s+(\d+)\s*$", info, re.MULTILINE)
            if pages is None or int(pages.group(1)) != len(PANELS):
                raise SystemExit(f"Expected {len(PANELS)} pages ({theme}):\n{info}")
            for number, (panel, description) in enumerate(PANELS, start=1):
                svg = work / f"{theme}-{number}.svg"
                run("pdftocairo", "-svg", "-f", str(number), "-l", str(number),
                    f"{name}.pdf", str(svg), cwd=work)
                describe_svg(svg, description)
                outputs.append((svg, ASSETS / f"{panel}-{theme}.svg"))

        # Publish only after both themes compile and all SVGs validate.
        outputs.append((work / "rules-light.pdf", ASSETS / "rules.pdf"))
        for source, target in outputs:
            shutil.copyfile(source, target)
            print(target.relative_to(ASSETS.parent))


if __name__ == "__main__":
    main()
