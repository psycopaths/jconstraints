# jConstraints
*jConstraints* is a library for modeling expressions and for interacting with constraint solvers.

## Building and Installing

* In the *jConstraints* folder, run `./gradlew build`.
* If the compilation was successful, the *jConstraints* library is located at
  `jconstraints-core/build/libs/jconstraints-core-[VERSION].jar`.
* A fat JAR containing all dependencies can be found at: `build/libs/jconstraints-core-[VERSION]-all.jar`.

## Solver Bindings

*jConstraints* does not come with constraint solvers. In order to use it, you will have to install one of the plugins
that connect to constraint solvers.

### Z3 Solver Plugin

jconstraints-z3 supports setting some of the options in z3
via constructor parameters or configuration options:

    z3.timeout=[timeout in millis]
    z3.options=[option1]=[value1];[option2]=[value2];...

Example:

    z3.timeout=2
    z3.options=smt.mbqi=true;smt.macro-finder=true

## About this fork ##
*jConstraints* has been founded by the [psycopaths](https://github.com/psycopaths).
We forked the original library and maintain it now in this fork.
