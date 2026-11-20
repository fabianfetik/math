#!/bin/sh
set -eu

if [ "$#" -ne 2 ]; then
    printf 'Usage: sh check.sh LEAN_PROJECT CERTIFICATE.json\n' >&2
    exit 2
fi

source_dir=$(CDPATH= cd -- "$(dirname -- "$0")" && pwd)
lean_project=$(CDPATH= cd -- "$1" && pwd)
certificate=$(python3 -B -c 'from pathlib import Path; import sys; print(Path(sys.argv[1]).resolve(strict=True))' "$2")
work=$(mktemp -d)
trap 'rm -rf -- "$work"' EXIT
cp "$source_dir/HeightSevenCertificate.lean" "$work/"
python3 -B "$source_dir/json_to_lean.py" "$certificate" "$work/HeightSevenData.lean"

cd "$lean_project"
lake env sh -ec '
    export LEAN_PATH="$1${LEAN_PATH:+:$LEAN_PATH}"
    lean --root="$1" -o "$1/HeightSevenCertificate.olean" "$1/HeightSevenCertificate.lean"
    lean --root="$1" "$1/HeightSevenData.lean"
' sh "$work"
