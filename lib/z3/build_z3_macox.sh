Z3_GIT_LOCATION='/tmp/psyco_build_sideproducts/git_z3/'

mkdir -p ${Z3_GIT_LOCATION}

while [[ $# -gt 0 ]]
do
key="$1"

case $key in
    -s|--show)
    SHOW="YES"
    shift
    ;;
    -t|--tag)
    TAG="$2"
    shift # past argument
    ;;
    *)
    echo 'unknown Option, allowed is -s to show tags or -t XXX for building tag XXX'      # unknown option
    ;;
esac
shift # past argument or value
done
git -C $Z3_GIT_LOCATION fetch || git clone git@github.com:Z3Prover/z3.git $Z3_GIT_LOCATION

if [ -n "${TAG}" ]; then
	echo 'Building for tag ${TAG}'
	git -C $Z3_GIT_LOCATION checkout tags/${TAG}
else
	if [ -n "${SHOW}" ]; then
		echo 'The following Tags are avilable'
		git -C ${Z3_GIT_LOCATION} tag
		exit
	else
		echo 'Build current Z3 HEAD-SNAPSHOT'
		git -C ${Z3_GIT_LOCATION} pull
	fi
fi

git -C ${Z3_GIT_LOCATION} pull || git clone git@github.com:Z3Prover/z3.git ${Z3_GIT_LOCATION}

pushd ${Z3_GIT_LOCATION};
	python scripts/mk_make.py --java
popd;
pushd ${Z3_GIT_LOCATION}/build;
	make
	sudo make install
	mkdir -p ~/Library/Java/Extensions/
	cp libz3* ~/Library/Java/Extensions/
	if [ -n "${TAG}" ]; then
		mvn install:install-file -Dfile=com.microsoft.z3.jar -DgroupId=com.microsoft -DartifactId=z3 -Dversion=${TAG} -Dpackaging=jar
	else
		mvn install:install-file -Dfile=com.microsoft.z3.jar -DgroupId=com.microsoft -DartifactId=z3 -Dversion=HEAD-SNAPSHOT -Dpackaging=jar
	fi
popd;
