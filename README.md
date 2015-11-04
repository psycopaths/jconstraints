jConstraints-z3: Installation Guide and Manual
==============================================

*jConstraints-z3* is a plugin for 
[jConstraints][0], adding Z3 as a 
constraint solver.

Dependencies
==============================================

* [Z3 4.3+][4]

Z3 is not distributed along with *jConstraints-z3*, but is
available at [The Z3 Theorem Prover][4]'s website.


Building and Installing
==============================================

Building and Installing Z3
----------------------------------------------
**Note**: Installing Z3 requires `git` and `python`
and `maven` to be installed and to reside in your `PATH`
environment variable.

The following instructions are taken from Leonardo de 
Moura's [blog][5].

First, we have to clone Z3:

```bash
git clone https://github.com/Z3Prover/z3.git
```

**Obtaining Z3 without Git:** If you do not have Git, you can also
download a source archive from [Z3's website][9].

Next, we generate a Z3 Makefile with the `--java` option.

```bash
python scripts/mk_make.py --java
```

Now, we build Z3

```bash
cd build
make all
```

Make sure to install `libz3.so` and `libz3java.so` (extension `.dylib`
in OSX) to a global library folder or to one that is contained in your
`java.library.path` property (the `LD_LIBRARY_PATH` in Bash).

Install the `com.microsoft.z3.jar` file from the `build` directory of
your Z3 working copy into the local Maven directory:

```bash
mvn install:install-file -Dfile=com.microsoft.z3.jar -DgroupId=com.microsoft -DartifactId=z3 -Dversion=0.9 -Dpackaging=jar
```


Building and Installing jConstraints-z3
----------------------------------------------

* In the *jConstraints-z3* folder, run `mvn install`
* If the compilation was successful, the *jConstraints-z3*
  library can be found in the JAR file
  `target/jconstraints-[VERSION].jar`
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

[0]: https://bitbucket.org/psycopaths/jconstraints
[4]: https://github.com/Z3Prover/z3
[5]: http://research.microsoft.com/en-us/um/people/leonardo/blog/2012/12/10/z3-for-java.html
[9]: https://github.com/Z3Prover/z3/releases
