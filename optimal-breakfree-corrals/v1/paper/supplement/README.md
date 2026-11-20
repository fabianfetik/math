# Software and formal evidence

The Python constructor returns physical rows, gap permutations and shifts.
The checker reconstructs their cyclic partial sums and checks the gap
permutations and complete site occupation. The finite controls compare the
supplied height-seven example and test rejection of damaged certificates.
The general construction is proved in the article.

From the article directory, run the Python checks.

```sh
python3 -B supplement/software/smoke_test.py
python3 -B supplement/software/construct.py 7 | python3 -B supplement/software/verify.py -
```

The [height-seven Lean check](formal/README.md) verifies the imported values
of the [supplied certificate](examples/height-seven.json). Run it from the
article directory in the source package after building the pinned Lean
project.

    sh supplement/formal/check.sh ../lean supplement/examples/height-seven.json

The [formal scope](../FORMAL-SCOPE.md) and [statement map](../CLAIM-MAP.md)
give the precise claims and premises for the Lean development. The software
and local Lean sources are supplied under the [MIT license](licenses/MIT.txt).
