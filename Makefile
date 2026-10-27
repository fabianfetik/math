.DEFAULT_GOAL := help

# Official actions/jekyll-build-pages v1.0.13, pinned for local and CI use.
JEKYLL_IMAGE := ghcr.io/actions/jekyll-build-pages@sha256:6791ebfd912185ed59bfb5fb102664fa872496b79f87ff8b9cfba292a7345041
PORT ?= 4000

.PHONY: help build update check preview clean

help:
	@printf '%s\n' \
	  'make build    Build the site and Markdown outputs in .build/' \
	  'make update   Build and copy generated repository READMEs into place' \
	  'make check    Build and check metadata, files, local links and READMEs' \
	  'make preview  Build and serve http://127.0.0.1:4000/math/' \
	  'make clean    Remove only the ignored .build/ directory'

build:
	@mkdir -p .build/site
	@docker run --rm --network none --read-only \
	  --user "$$(id -u):$$(id -g)" \
	  --env JEKYLL_ENV=production --env TZ=UTC \
	  --tmpfs /tmp:rw,nosuid,size=64m \
	  --mount "type=bind,source=$(CURDIR)/publishing/site,target=/source,readonly" \
	  --mount "type=bind,source=$(CURDIR)/.build/site,target=/output" \
	  --entrypoint jekyll "$(JEKYLL_IMAGE)" \
	  build --source /source --destination /output --strict_front_matter
	@python3 publishing/tools/publication.py prepare

update: build
	@python3 publishing/tools/publication.py update

check: build
	@python3 publishing/tools/publication.py check

preview: build
	python3 -m http.server "$(PORT)" --bind 127.0.0.1 --directory .build/preview

clean:
	rm -rf -- .build
