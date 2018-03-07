#/usr/bin/env bash

set -e

# Number of threads make will use: make -j$makeThreads
makeThreads=4

originalDir=`pwd`
# Make sure user ends up in the directory he started.
trap "cd \"$originalDir\"" EXIT

# Assume this script is located in the Equations directory.
equationsDir=`dirname "$0"`
cd "$equationsDir"

# Absolute path to Equations.
equationsDir=`pwd` # Hack alert: not all Unix systems have readlink.

# Absolute path to custom HoTT.
hottDir="$equationsDir"/custom-HoTT

usageExit() {
  echo "Usage: $0 [HoTT|Eq|Ex]" >&2
  echo "  HoTT  builds custom HoTT" >&2
  echo "  Eq    builds Equations (depends on custom HoTT)." >&2
  echo "  Ex    builds Equations and examples (depends on custom HoTT)." >&2
  exit 1
}

# Naive way of checking whether the custom HoTT exists.
doesCustomHoTTExist() {
  if [ -e "$hottDir" ]; then
    return 0
  fi
  return 1
}

cloneHoTTIfNotThere() {
  if ! doesCustomHoTTExist; then
    git clone https://github.com/HoTT/HoTT.git "$hottDir"
  fi
}

symlinkIfNotThere() {
  if [ -e "$2" ]; then
    return 0
  fi
  cmd="ln -s"
  echo $cmd "$1" "$2"
  $cmd "$1" "$2"
}

createHoTTSymlinks() {
  # The following symlinks are used to "cheat" make.
  symlinkIfNotThere "$hottDir"/hoqtop "$hottDir"/coqtop
  symlinkIfNotThere "$hottDir"/hoqtop.byte "$hottDir"/coqtop.byte
  symlinkIfNotThere "$hottDir"/hoqc "$hottDir"/coqc
  symlinkIfNotThere "$hottDir"/hoqchk "$hottDir"/coqchk
  symlinkIfNotThere "$hottDir"/hoqdep "$hottDir"/coqdep

  # These files should be in HoTT, not in Equations...
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Logic/EqdepFacts.v \
    "$hottDir"/coq/theories/Logic/EqdepFacts.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Logic/Eqdep.v \
    "$hottDir"/coq/theories/Logic/Eqdep.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Logic/JMeq.v \
    "$hottDir"/coq/theories/Logic/JMeq.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Logic/ProofIrrelevance.v \
    "$hottDir"/coq/theories/Logic/ProofIrrelevance.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Program/Equality.v \
    "$hottDir"/coq/theories/Program/Equality.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Init/Wf.v \
    "$hottDir"/coq/theories/Init/Wf.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Relations/Relation_Definitions.v \
    "$hottDir"/coq/theories/Relations/Relation_Definitions.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Relations/Relation_Operators.v \
    "$hottDir"/coq/theories/Relations/Relation_Operators.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Relations/Operators_Properties.v \
    "$hottDir"/coq/theories/Relations/Operators_Properties.v
  symlinkIfNotThere "$equationsDir"/theories/LibHoTT/Relations/Relations.v \
    "$hottDir"/coq/theories/Relations/Relations.v
}

buildFromHoTTDir() {
  cmd="./hoqtop -boot"
  echo $cmd "$@"
  $cmd "$@"
}

makeCoq() {
  if [ ! -e "$hottDir"/coq-HoTT/Makefile ]; then
    git clone -b hott-port-master https://github.com/andreaslyn/coq.git "$hottDir"/coq-HoTT
    cd "$hottDir"/coq-HoTT
    ./configure -local
  fi
  git -C "$hottDir"/coq-HoTT checkout hott-port-master
  make -C "$hottDir"/coq-HoTT clean
  make -C "$hottDir"/coq-HoTT -j$makeThreads \
    coqlight coqide plugins/extraction/extraction_plugin.cmxs
}

makeHoTT() {
  cd "$hottDir"
  if [ ! -e Makefile ]; then
    ./autogen.sh
    ./configure COQBIN="$hottDir/coq-HoTT/bin/"
  fi
  make -C "$hottDir" clean
  make -C "$hottDir" -j$makeThreads
  git -C "$hottDir"/coq-HoTT checkout hott-port-master
}

buildCustomHoTTFiles() {
  cd "$hottDir"

  # The Extraction.v is by built by the wrong coq. We must build it with hoq.
  buildFromHoTTDir -native-compiler -compile coq/plugins/extraction/Extraction.v

  # Build the symlinks.
  buildFromHoTTDir -compile coq/theories/Logic/EqdepFacts.v
  buildFromHoTTDir -compile coq/theories/Logic/Eqdep.v
  buildFromHoTTDir -compile coq/theories/Logic/JMeq.v
  buildFromHoTTDir -compile coq/theories/Logic/ProofIrrelevance.v
  buildFromHoTTDir -compile coq/theories/Program/Equality.v
  buildFromHoTTDir -compile coq/theories/Init/Wf.v
  buildFromHoTTDir -compile coq/theories/Relations/Relation_Definitions.v
  buildFromHoTTDir -compile coq/theories/Relations/Relation_Operators.v
  buildFromHoTTDir -compile coq/theories/Relations/Operators_Properties.v
  buildFromHoTTDir -compile coq/theories/Relations/Relations.v
}

buildHoTT() {
  cloneHoTTIfNotThere
  makeCoq
  makeHoTT
  createHoTTSymlinks
  buildCustomHoTTFiles
}

requireCustomHoTT() {
  if ! doesCustomHoTTExist; then
    echo Custom HoTT was not found. >&2
    usageExit
  fi
}

createEquationsMakefileIfNotThere() {
  cd "$equationsDir"
  if [ -e Makefile ]; then
    return 0
  fi
  echo "$hottDir"/coq-HoTT/bin/coq_makefile \-f _CoqProject \-o Makefile
  "$hottDir"/coq-HoTT/bin/coq_makefile -f _CoqProject -o Makefile
}

buildEquations() {
  requireCustomHoTT
  createEquationsMakefileIfNotThere
  OCAMLFIND_IGNORE_DUPS_IN="$hottDir"/coq-HoTT/plugins/derive \
    make -C "$equationsDir" COQBIN="$hottDir/"
}

buildExamples() {
  buildEquations
  OCAMLFIND_IGNORE_DUPS_IN="$hottDir"/coq-HoTT/plugins/derive \
    make -C "$equationsDir/examples" COQBIN="$hottDir/"
}

if [ "$1" = Eq ]; then
  buildEquations
elif [ "$1" = Ex ]; then
  buildExamples
elif [ "$1" = HoTT ]; then
  buildHoTT
else
  usageExit
fi
