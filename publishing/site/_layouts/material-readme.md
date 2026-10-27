{% assign paper = site.papers | where: "key", page.work_key | first -%}
{% assign release = paper.releases | where: "version", paper.current | first -%}
<!-- Generated from publishing/site/ by Jekyll. Run make update; edit the catalogue or templates. -->
# {{ release.title }}

{% for author in release.authors %}{{ author.name }}{% unless forloop.last %}, {% endunless %}{% endfor %} · {{ release.status }} · {{ release.date | date: "%-d %B %Y" }} · {{ release.version }}{% if release.subjects.size > 0 %} · {{ release.subjects | join: " / " }}{% endif %}

{% if paper.header_image -%}
<img src="../publishing/site{{ paper.header_image.path | escape }}" alt="" width="600">

{% endif -%}
{{ release.summary }}

{% include links.liquid paper=paper release=release format="readme-paper" %}

## Supplementary material

{% include links.liquid release=release format="readme-material" %}

| Material | Contents |
| --- | --- |
{% for item in release.materials -%}
| [{{ item.label | replace: "|", "&#124;" }}]({{ site.repository_url }}/{% if item.kind == "file" %}blob{% else %}tree{% endif %}/{{ release.source_ref }}/{{ item.path }}) | {{ item.description | replace: "|", "&#124;" }} |
{% endfor %}

{{ release.material_note }}

For the complete release, including any bundled data archives, use the ZIP.
The package READMEs and manifests describe that complete download.

## Citation

{% for author in release.authors %}{{ author.citation_name }}{% unless forloop.last %}, {% endunless %}{% endfor %} ({{ release.date | date: "%Y" }}). *{{ release.title }}* ({{ release.version }}). Zenodo. [https://doi.org/{{ release.doi }}](https://doi.org/{{ release.doi }})

{% if paper.releases.size > 1 %}
## Release history

| Release | Published | PDF | Archive |
| --- | --- | --- | --- |
{% assign history = paper.releases | sort: "date" | reverse -%}
{% for previous in history -%}
| {{ previous.version }} | {{ previous.date | date: "%-d %B %Y" }} | [PDF {{ previous.version }}]({{ previous.pdf | absolute_url }}) | [Zenodo](https://doi.org/{{ previous.doi }}) |
{% endfor %}
{% endif %}
## License

The article, documentation and supporting data are licensed under
[CC BY 4.0](https://creativecommons.org/licenses/by/4.0/); supplied software and
local Lean sources are licensed under MIT. The complete package contains the
precise license allocation and full texts.
