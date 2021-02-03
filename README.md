jConstraints-z3: Installation Guide and Manual
==============================================

*jConstraints-z3* is a plugin for
[jConstraints][0], adding support for Z3 as a
constraint solver.

Dependencies
==============================================

As of today, jconstraints-z3 ships with the [z3-turnkey artifacts](https://github.com/tudo-aqua/z3-turnkey).
It should no longer be required to install Z3 natively, if the shadow jar is run.


Building and Installing
==============================================

`./gradlew clean test jar shadowJar` should be enough.
We recommend to use the shadowJar in projects as it includes the solvers.


Building and Installing jConstraints-z3
----------------------------------------------

* In the *jConstraints-z3* folder, run `mvn install`
* If the compilation was successful, the *jConstraints-z3*
  library can be found in the JAR file
  `target/jconstraints-z3-[VERSION].jar`
* jConstraints loads extensions automatically from the
  `~/.jconstraints/extensions` folder in the user's home
  directory. Create this directory and copy
  `com.microsoft.z3.jar` (from Z3, see above) and
  `jConstraints-z3-[version].jar` into this folder.


Configuration
----------------------------------------------

jconstraints-z3 supports setting some of the options in z3
via constructor parameters or configuration options:

    z3.timeout=[timeout in millis]
    z3.options=[option1]=[value1];[option2]=[value2];...

Example:

    z3.timeout=2
    z3.options=smt.mbqi=true;smt.macro-finder=true

[0]: https://github.com/tudo-aqua/jconstraints

