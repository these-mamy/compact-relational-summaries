#!/usr/bin/env bash
set -euo pipefail

script_dir="$(cd "$(dirname "${BASH_SOURCE[0]}")" && pwd)"
repo_root="$(cd "$script_dir/../.." && pwd)"
source_tex="$script_dir/pr-1-vs-main-highlighted.tex"
build_dir="$repo_root/doc/build/review"
build_tex="$build_dir/pr-1-vs-main-highlighted.tex"

for required_tool in latexmk kpsewhich sed; do
  if ! command -v "$required_tool" >/dev/null 2>&1; then
    printf 'Required tool not found: %s\n' "$required_tool" >&2
    exit 1
  fi
done

roman_font="$(kpsewhich lmroman10-regular.otf)"
roman_bold_font="$(kpsewhich lmroman10-bold.otf)"
roman_italic_font="$(kpsewhich lmroman10-italic.otf)"
roman_bold_italic_font="$(kpsewhich lmroman10-bolditalic.otf)"
sans_font="$(kpsewhich lmsans10-regular.otf)"
sans_bold_font="$(kpsewhich lmsans10-bold.otf)"
sans_italic_font="$(kpsewhich lmsans10-oblique.otf)"
sans_bold_italic_font="$(kpsewhich lmsans10-boldoblique.otf)"
math_font="$(kpsewhich latinmodern-math.otf)"

if [[ -z "$roman_font" || -z "$roman_bold_font" ||
      -z "$roman_italic_font" || -z "$roman_bold_italic_font" ||
      -z "$sans_font" || -z "$sans_bold_font" ||
      -z "$sans_italic_font" || -z "$sans_bold_italic_font" ||
      -z "$math_font" ]]; then
  printf 'Latin Modern OpenType fonts were not found by kpsewhich.\n' >&2
  exit 1
fi

mkdir -p "$build_dir"

sed \
  -e "s#\\\\setmainfont{Latin Modern Roman}#\\\\setmainfont[Path=$(dirname "$roman_font")/,BoldFont=$(basename "$roman_bold_font"),ItalicFont=$(basename "$roman_italic_font"),BoldItalicFont=$(basename "$roman_bold_italic_font")]{$(basename "$roman_font")}#" \
  -e "s#\\\\setsansfont{Latin Modern Sans}#\\\\setsansfont[Path=$(dirname "$sans_font")/,BoldFont=$(basename "$sans_bold_font"),ItalicFont=$(basename "$sans_italic_font"),BoldItalicFont=$(basename "$sans_bold_italic_font")]{$(basename "$sans_font")}#" \
  -e "s#\\\\setmathfont{Latin Modern Math}#\\\\setmathfont[Path=$(dirname "$math_font")/]{$(basename "$math_font")}#" \
  "$source_tex" > "$build_tex"

latexmk \
  -norc \
  -xelatex \
  -interaction=nonstopmode \
  -halt-on-error \
  -outdir="$build_dir" \
  "$build_tex"

printf 'Built %s\n' "$build_dir/pr-1-vs-main-highlighted.pdf"
