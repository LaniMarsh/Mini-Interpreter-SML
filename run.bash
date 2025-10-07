#!/bin/bash

defaultSML=/home/akeen/public/ml/bin/sml
expected_source=evaluator.sml


if [ ! -f ${expected_source} ]; then
   echo "must provide source file '${expected_source}'"
   exit 1
fi

if [ -z ${SML} ]; then
   echo "SML not set: using default of ${defaultSML}"
   SML=${defaultSML}
fi

if [ ! -f ${SML} ]; then
   echo "${SML} does not exist"
   exit 1
fi

${SML} &> tmp << END
val devnull = Posix.FileSys.openf ("/dev/null", Posix.FileSys.O_WRONLY, Posix.FileSys.O.trunc);
val sout = Posix.IO.dup(Posix.FileSys.stdout);
Posix.IO.dup2 {old=devnull, new=Posix.FileSys.stdout};

use "ast.sml";
use "exceptions.sml";

use "${expected_source}";

Control.Print.printDepth := 0;
Control.Print.printLength := 0;

use "test_scaffold.sml";
Posix.IO.dup2 {old=sout, new=Posix.FileSys.stdout};

use "tests.sml";
END

grep -v -e "GC #" -e "Standard ML" -e "autoloading" -e "unit" -e "Warning" -e "dummy" -e "library" -e "FD" -e '^- $' -e "stdin" -e "opening" -e "^val prog" tmp
rm tmp
