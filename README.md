jConstraints-z3: Installation Guide and Manual
==============================================

*jConstraints-z3* is a plugin for 
[jConstraints][0], adding Z3 as a 
constraint solver.

Dependencies
==============================================

* [Z3 4.3+][2]

Z3 is not distributed along with *jpf-constraints-z3*, 
but is available free of charge
for non-commercial purposes under the terms of the 
[Microsoft Research License Agreement][4]. 


Building and Installing
==============================================

Building and Installing Z3
----------------------------------------------
**Note**: Installing Z3 requires `git` and `python`
and `maven` to be installed and to reside in your `PATH`
environment variable.

The following instructions are taken from Leonardo de 
Moura's [blog][5].

First, we have to clone the unstable branch from codeplex.
CodePlex requires git 1.7.10 or later to avoid HTTPS cloning errors. 

	#!bash
	#git clone https://git01.codeplex.com/z3 -b unstable

**Obtaining Z3 without Git:** If you do not have Git,
or if your version of Git is too old in order to work
with the Z3 CodePlex repository, you can also download
the source archive from [CodePlex][9]. Be sure to
select the ***unstable*** branch, then click "Download".

Next, we generate the Z3 make file with the option --java.

	#!bash
	#python scripts/mk_make.py --java

Now, we build Z3

	#!bash
	#cd build
	#make all

Make sure to install `libz3.so` and `libz3java.so` (extension 
`.dylib` in OSX) to a global library folder or to one that is
contained in your java.library.path property.

Install the
`com.microsoft.z3.jar` file from the `build` directory
of your Z3 working copy into the local Maven directory:

	#!bash
	# mvn install:install-file -Dfile=com.microsoft.z3.jar -DgroupId=com.microsoft -DartifactId=z3 -Dversion=0.9 -Dpackaging=jar


Building and Installing jConstraints-z3
----------------------------------------------

* In the *jConstraints-z3* folder, run `mvn install`
* If the compilation was successful, the *jConstraints-z3*
  library can be found in the JAR file
  `target/jconstraints-[VERSION].jar`
* jConstraints loads extensions automatically from the
  `~/.jconstraints/extensions` folder in a users home
  directory. Create this directory and copy
  `com.microsoft.z3.jar` (from Z3, see above) and
  `jConstraints-z3-[version].jar` into this folder.   


Configuration
----------------------------------------------

jconstraints-z3 supports setting some of the options in z3
via constructor parameters or configuration options:

	#!bash
	# z3.timeout=[timeout in millis]
	# z3.options=[option1]=[value1];[option2]=[value2];...

Example:

	#!bash
	# z3.timeout=2
	# z3.options=smt.mbqi=true;smt.macro-finder=true


[0]: https://bitbucket.org/psycopaths/jconstraints
[2]: http://z3.codeplex.com/
[4]: http://z3.codeplex.com/license
[5]: http://research.microsoft.com/en-us/um/people/leonardo/blog/2012/12/10/z3-for-java.html
[9]: http://z3.codeplex.com/SourceControl/latest#
