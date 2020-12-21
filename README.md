# jConstraints #
*jConstraints* is a library for modeling expressions
and for interacting with constraint solvers.

## Dependencies ##

* [ANTLR v3][1]
* [Guava 14.0.1][7]

ANTLR is distributed under the terms of the
[BSD license][3]. Guava is distributed under
the terms of the [Apache License 2.0][8].


## Building and Installing ##

* In the *jConstraints* folder, run `./gradlew jar`
* If the compilation was successful, the *jConstraints*
  library can be found in the JAR file
  `build/libs/jconstraints-[VERSION].jar`

* You might run `./gradlew shadowJar` to get a fat JAR containing
  all dependencies. It should be found as: `build/libs/jconstraints-[VERSION]-all.jar`


## How To Use ##

*jConstraints* does not come with constraint solvers.
In order to use it, you will have to install one
of the plugins that connect to constraint solvers.
On the [*tudo-aqua org*][9], you can find *jConstraints*
plugins for, e.g. Z3.

[1]: http://www.antlr3.org/
[3]: http://www.antlr3.org/license.html
[7]: https://code.google.com/p/guava-libraries/
[8]: http://www.apache.org/licenses/LICENSE-2.0
[9]: https://github.com/tudo-aqua


## About this fork ##
*jConstraints* has been founded by the [psycopaths](https://github.com/psycopaths).
We forked the original library and maintain it now in this fork.
