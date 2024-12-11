#!/bin/bash
set -e

while getopts ":j" option; do
    echo "Option: $option"
    case $option in
        j)
            echo "Bypassing the generation of the extended fuzzer and just compiling the fuzzer."
            just_compile=true
            shift $((OPTIND-1));;
        \?) # incorrect option
        echo "Error: Invalid option $OPTARG" >&2
        exit;;
   esac
done

# Validate the number of arguments
if [ $# -ne 1 ]; then
    echo "Error: Running the script requires passing the strategy name as an argument."
    echo "Usage: $0 <strategy>"
    exit 1
fi

fuzzer=$1

# Validate the fuzzer name by looking up `*Fuzzer.v` in `Strategies` directory
if [ ! -f "Strategies/$fuzzer"".v" ]; then
    echo "Error: The fuzzer name is invalid."
    # Provide a list of valid fuzzers
    echo "Valid fuzzers are:"
    for f in Strategies/*Fuzzer.v; do
        echo "  - $(basename $f .v)"
    done
    exit 1
fi

qc_path=$OPAM_SWITCH_PREFIX"/lib/coq/user-contrib/QuickChick"

# Build the fuzzer


# 1. Generate extended version of the fuzzer
fuzzer_path=$fuzzer"_test_runner.ml"
extended_fuzzer_path=$fuzzer"_test_runner_ext.ml"
extended_mli_path=$fuzzer"_test_runner_ext.mli"
stub_path=$qc_path"/Stub.ml"


if [ ! $just_compile ]; then
    ## 1.1. Copy the stub to the extended fuzzer
    cp $stub_path $extended_fuzzer_path &&
    echo $'\n\n(* -----(Stub Ends)----- *)\n\n' >> $extended_fuzzer_path &&
    ## 1.2. Add the fuzzer to the extended fuzzer
    cat $fuzzer_path >> $extended_fuzzer_path &&
    ## 1.3. Create the extended mli file
    touch $extended_mli_path &&
    ocamlc -c $extended_mli_path

    # 2. Build the fuzzer
    ## 2.1. Make it tail recursive
    $qc_path"/cmdprefix.pl" $fuzzer"_test_runner_ext.ml" &&
    $qc_path"/cmdsuffix.pl" $fuzzer"_test_runner_ext.ml"
fi
## 2.2. Run ocaml compiler
ocamlfind ocamlopt -ccopt -Wno-error=implicit-function-declaration -afl-instrument -linkpkg -package unix -package str -package coq-core.plugins.extraction -thread -rectypes -w a -o $fuzzer"_exec" $fuzzer"_test_runner_ext.ml" $qc_path"/SHM.c" &&
ocamlfind ocamlopt -ccopt -Wno-error=implicit-function-declaration -linkpkg -package unix -package str -rectypes -w a -I . -o main_exec $qc_path"/Main.ml" $qc_path"/SHM.c"