#!/usr/bin/env python3
"""Check Jekyll output and copy files; all rendering belongs to Jekyll."""

import argparse
import datetime
import hashlib
from html.parser import HTMLParser
import json
from pathlib import Path, PurePosixPath
import re
import shutil
import sys
from urllib.parse import unquote, urljoin, urlsplit


ROOT = Path(__file__).resolve().parents[2]
BUILD = ROOT / ".build"
SITE = BUILD / "site"
REPOSITORY = BUILD / "repository"


def require(condition, message):
    if not condition:
        raise ValueError(message)


def safe_path(base, relative):
    path = PurePosixPath(relative)
    require(not path.is_absolute() and ".." not in path.parts, f"Unsafe path: {relative}")
    target = base.joinpath(*path.parts)
    require(target.resolve().is_relative_to(base.resolve()), f"Path escapes {base}: {relative}")
    return target


def digest(path):
    with path.open("rb") as stream:
        return hashlib.file_digest(stream, "sha256").hexdigest()


def read_catalogue(path):
    with path.open(encoding="utf-8") as stream:
        catalogue = json.load(stream)
    require(catalogue["works"], "No works in the catalogue")
    require(re.fullmatch(r"/[a-zA-Z0-9_/-]+", catalogue["baseurl"]), "Invalid project baseurl")
    require(".." not in catalogue["baseurl"].split("/"), "Unsafe project baseurl")
    work_keys, dois = set(), set()
    for work in catalogue["works"]:
        key = work["key"]
        require(re.fullmatch(r"[a-z0-9]+(?:-[a-z0-9]+)*", key), f"Invalid work key: {key}")
        require(key not in work_keys, f"Duplicate work: {key}")
        work_keys.add(key)
        require(work["url"] == f"/{key}/", f"Unexpected work URL: {work['url']}")
        require(work["concept_doi"].startswith("10."), f"Missing concept DOI for {key}")
        versions = set()
        for release in work["releases"]:
            version = release["version"]
            label = f"{key} {version}"
            require(re.fullmatch(r"v[1-9][0-9]*", version), f"Invalid version: {label}")
            require(version not in versions, f"Duplicate release: {label}")
            versions.add(version)
            require(release["work"] == key, f"Wrong work identity: {label}")
            for field in ("title", "date", "status", "summary", "abstract", "doi", "zenodo_url", "material_note"):
                require(isinstance(release[field], str) and release[field].strip(), f"Missing {field}: {label}")
            datetime.date.fromisoformat(release["date"])
            subjects = release["subjects"]
            require(isinstance(subjects, list) and all(isinstance(code, str) for code in subjects), f"Invalid subjects: {label}")
            require(len(set(subjects)) == len(subjects), f"Duplicate subjects: {label}")
            require(all(code in catalogue["subjects"] for code in subjects), f"Unknown subject category: {label}")
            require(release["authors"], f"No authors: {label}")
            for author in release["authors"]:
                require(author["name"].strip(), f"Missing author name: {label}")
                require(author["citation_name"].strip(), f"Missing citation author name: {label}")
                require(
                    author["orcid"] is None or author["orcid"].startswith("https://orcid.org/"),
                    f"Invalid author ORCID: {label}",
                )
            require(re.fullmatch(r"10\.5281/zenodo\.[0-9]+", release["doi"]), f"Invalid Zenodo DOI: {label}")
            require(release["doi"] not in dois, f"DOI reused by different releases: {label}")
            dois.add(release["doi"])
            require(release["doi"] != work["concept_doi"], f"Concept DOI used as version DOI: {label}")
            record_id = release["doi"].split("zenodo.", 1)[1]
            require(release["zenodo_url"] == f"https://zenodo.org/records/{record_id}", f"DOI/record mismatch: {label}")
            for artifact, extension in (("pdf", ".pdf"), ("package", ".zip")):
                path = safe_path(ROOT, release[artifact])
                require(path.name.endswith(f"-{version}{extension}"), f"Unversioned {artifact}: {label}")
                expected = release[f"{artifact}_sha256"]
                require(re.fullmatch(r"[0-9a-f]{64}", expected), f"Invalid {artifact} SHA-256: {label}")
                # Complete ZIPs may be external; any local copy must still match.
                if artifact == "pdf" or path.exists():
                    require(path.is_file(), f"Missing {artifact}: {release[artifact]}")
                    require(digest(path) == expected, f"SHA-256 mismatch: {release[artifact]}")
            ref = release["source_ref"]
            require(re.fullmatch(r"[0-9a-f]{40}", ref) or ref == f"{key}-{version}", f"Unpinned source reference: {label}")
            require(safe_path(ROOT, release["source_root"]).is_dir(), f"Missing source directory: {label}")
            require(release["materials"], f"No browsable material: {label}")
            for material in release["materials"]:
                require(material["label"] and material["description"], f"Incomplete material entry: {label}")
                source = safe_path(ROOT, material["path"])
                require(material["kind"] in ("file", "directory"), f"Invalid material kind: {label}")
                exists = source.is_file() if material["kind"] == "file" else source.is_dir()
                require(exists, f"Missing material: {material['path']}")
            github_release = release["github_release_url"]
            github_package = release["github_package_url"]
            require(bool(github_release) == bool(github_package), f"Incomplete GitHub mirror: {label}")
            if github_release:
                repository = catalogue["repository_url"]
                tag = f"{key}-{version}"
                require(github_release == f"{repository}/releases/tag/{tag}", f"Wrong GitHub release URL: {label}")
                require(
                    github_package == f"{repository}/releases/download/{tag}/{Path(release['package']).name}",
                    f"Wrong GitHub package URL: {label}",
                )
        require(work["current"] in versions, f"Current release not found: {key}")
    return catalogue


def expected_readmes(catalogue):
    return {"README.md"} | {f"{work['key']}/README.md" for work in catalogue["works"]}


def check_generated_readmes(catalogue, directory):
    expected = expected_readmes(catalogue)
    actual = {path.relative_to(directory).as_posix() for path in directory.rglob("README.md")}
    require(actual == expected, f"Generated README set differs: missing={expected-actual}, extra={actual-expected}")
    for relative in sorted(expected):
        text = safe_path(directory, relative).read_text(encoding="utf-8")
        require("{%" not in text and "{{" not in text, f"Unrendered Liquid in {relative}")
        require("<html" not in text.lower() and "<!doctype" not in text.lower(), f"HTML instead of Markdown: {relative}")
        require(text.startswith("<!-- Generated"), f"Missing generated-file notice: {relative}")
        if relative == "README.md":
            headings = re.findall(r"(?m)^#{1,6} \[.+\]\(([^)\n]+)\)[ \t]*$", text)
            paths = [urlsplit(url).path for url in headings]
            expected_paths = [catalogue["baseurl"].rstrip("/") + work["url"] for work in catalogue["works"]]
            require(
                len(paths) == len(expected_paths) and set(paths) == set(expected_paths),
                "The root README must link every work exactly once in its publication list",
            )
            for work in catalogue["works"]:
                require(f"]({work['key']}/)" in text, f"Missing material README link: {work['key']}")
    return expected


def prepare():
    generated = SITE / "_repository"
    catalogue = read_catalogue(generated / "catalogue.json")
    check_generated_readmes(catalogue, generated)
    for work in catalogue["works"]:
        for release in work["releases"]:
            destination = safe_path(SITE, release["pdf"])
            destination.parent.mkdir(parents=True, exist_ok=True)
            shutil.copyfile(safe_path(ROOT, release["pdf"]), destination)
    if REPOSITORY.exists():
        shutil.rmtree(REPOSITORY)
    shutil.move(str(generated), REPOSITORY)
    preview_root = BUILD / "preview"
    preview_root.mkdir(exist_ok=True)
    relative_mount = PurePosixPath(catalogue["baseurl"].strip("/"))
    # The final component intentionally points outside preview/ into site/.
    mount = safe_path(preview_root, relative_mount.parent.as_posix()) / relative_mount.name
    mount.parent.mkdir(parents=True, exist_ok=True)
    if mount.is_symlink():
        mount.unlink()
    require(not mount.exists(), f"Unexpected preview path: {mount}")
    mount.symlink_to(SITE, target_is_directory=True)
    print(f"Built {len(catalogue['works'])} work pages; output: .build/site/")


class PageLinks(HTMLParser):
    def __init__(self):
        super().__init__(convert_charrefs=True)
        self.ids = set()
        self.links = []

    def handle_starttag(self, tag, attrs):
        attrs = dict(attrs)
        if "id" in attrs:
            self.ids.add(attrs["id"])
        for key in ("href", "src"):
            if attrs.get(key):
                self.links.append(attrs[key])


def check_site(catalogue):
    baseurl = catalogue["baseurl"].rstrip("/")
    pages = {}
    for path in SITE.rglob("*.html"):
        parser = PageLinks()
        parser.feed(path.read_text(encoding="utf-8"))
        pages[path] = parser
    for path, parser in pages.items():
        relative = path.relative_to(SITE).as_posix()
        public_path = baseurl + "/" + relative
        if public_path.endswith("/index.html"):
            public_path = public_path[:-10]
        for href in parser.links:
            parsed = urlsplit(href)
            # Outbound services are checked at publication, not on each offline build.
            if parsed.scheme or parsed.netloc:
                continue
            resolved = urlsplit(urljoin(public_path, href))
            require(resolved.path.startswith(baseurl + "/"), f"Link leaves Pages baseurl: {relative}: {href}")
            target = safe_path(SITE, unquote(resolved.path[len(baseurl) + 1:]))
            if target.is_dir():
                target /= "index.html"
            require(target.is_file(), f"Broken local link: {relative}: {href}")
            if resolved.fragment and target in pages:
                require(unquote(resolved.fragment) in pages[target].ids, f"Missing fragment: {relative}: {href}")
        text = path.read_text(encoding="utf-8")
        for block in re.findall(r'<script type="application/ld\+json">(.*?)</script>', text, re.S):
            json.loads(block)
    for work in catalogue["works"]:
        require((SITE / work["key"] / "index.html").is_file(), f"Missing work page: {work['key']}")
        for release in work["releases"]:
            target = safe_path(SITE, release["pdf"])
            require(target.is_file() and digest(target) == release["pdf_sha256"], f"Published PDF differs: {release['pdf']}")
    require(not (SITE / "_repository").exists(), "Internal README outputs leaked into the website")


def main():
    parser = argparse.ArgumentParser(description=__doc__)
    parser.add_argument("operation", choices=("prepare", "update", "check"))
    operation = parser.parse_args().operation
    if operation == "prepare":
        prepare()
        return
    catalogue = read_catalogue(REPOSITORY / "catalogue.json")
    readmes = check_generated_readmes(catalogue, REPOSITORY)
    check_site(catalogue)
    if operation == "update":
        for relative in sorted(readmes):
            shutil.copyfile(safe_path(REPOSITORY, relative), safe_path(ROOT, relative))
            print(f"Updated {relative}")
    else:
        for relative in sorted(readmes):
            target = safe_path(ROOT, relative)
            require(target.is_file(), f"Missing tracked README: {relative}; run make update")
            require(
                target.read_bytes() == safe_path(REPOSITORY, relative).read_bytes(),
                f"Stale README: {relative}; run make update",
            )
        print("Metadata, artifact hashes, local links, structured data and generated READMEs match.")


if __name__ == "__main__":
    try:
        main()
    except (ValueError, KeyError, OSError) as error:
        print(f"Publication check failed: {error}", file=sys.stderr)
        sys.exit(1)
