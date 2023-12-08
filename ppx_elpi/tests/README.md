## Usage

To add a new test

```shell
touch test_XXX.ml
touch test_XXX.expected.ml
touch test_XXX.expected.elpi
dune runtest --auto-promote # promotes the dune file
```

As a template for `test_XXX.ml` you should use `test_simple_adt.ml``

To run tests and acknowledge a change
```shell
dune runtest --auto-promote # promotes the output
```
