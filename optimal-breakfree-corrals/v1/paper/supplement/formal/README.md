# Height-seven certificate check

The check takes the supplied [JSON certificate](../examples/height-seven.json)
and a built Lean project. Run it with Python 3, a POSIX shell and the toolchain
specified by the project's Lean pin.

    sh check.sh /path/to/lean-project /path/to/height-seven.json

The helper reads the JSON fields and supplies typed values to Lean. Lean
checks the header and dimensions, the seven increasing row lists from the
one-swap construction, the gap permutations and the arrivals from the
stored shifts modulo 91. Each accepted arrival list gives the sites of its
recorded row with their multiplicities. A successful run prints the axiom
report for `HeightSevenCertificate.supplied_checked`.

The Python helper handles JSON parsing and emission of the typed values.
The Lean theorem certifies those values for this example.
