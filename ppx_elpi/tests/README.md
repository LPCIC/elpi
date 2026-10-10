## Usage

To add a new test

```shell
touch test_XXX.ml
touch test_XXX.expected.ml
touch test_XXX.expected.elpi
make tests-ppx PROMOTE=true # promotes the dune file
```

As a template for `test_XXX.ml` you should use `test_simple_adt.ml``

To run tests and acknowledge a change
```shell
make tests-ppx PROMOTE=true # promotes the output
```

## Structure of a test

`test_XXX.ml` derives some types and declares the builtins, then ends with
`Ppx_tests_lib.check_declarations builtin` (the declarations type check) or
`Ppx_tests_lib.run_program builtin program` (the program is run too). The code
shared by all tests, including the recording of exceptions in the output so
that it is promoted even if the test fails, is in `ppx_tests_lib.ml`.
