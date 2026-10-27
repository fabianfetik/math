### [{{ include.release.title }}]({{ include.paper.url | absolute_url }})

{{ include.release.status }} · {{ include.release.date | date: "%-d %B %Y" }} · {{ include.release.version }}{% if include.release.subjects.size > 0 %} · {{ include.release.subjects | join: " / " }}{% endif %}

{{ include.release.summary }}

{% include links.liquid paper=include.paper release=include.release format="readme-overview" %}
