#!/bin/bash

# Run this script as `./create-output.sh > output.txt 2>&1`

# How we want to call our executable, 
# possibly with some command line parameters
EXEC_PROGRAM="./a.out "

# Timestamp for starting this script
date

MACHINE=""
# Display machine name if uname command is available
if hash uname 2>/dev/null; then
  uname -a
  MACHINE=`uname -a`
fi

# Display user name if id command is available
if hash id 2>/dev/null; then
  id
fi

# delete a.out, do not give any errors if it does not exist
rm ./a.out 2>/dev/null

echo "====================================================="
echo "1. If the section below is empty, the program compiles "
echo "   without warnings with -Wall -Wextra flags"
echo "====================================================="

g++ -g -std=c++11 -Wall -Wextra -Wno-sign-compare *.cpp

echo "====================================================="
echo "2. If the section below is empty or has the expected output "
echo "    the program puns and produces correct output"
echo "====================================================="

# Execute program
$EXEC_PROGRAM

echo "====================================================="
echo "3. If the section below is empty, then there are no clang-tidy warnings "
echo "   (ignore warnings from system headers, such as \"13554 warnings generated.\")"
echo "====================================================="

if hash clang-tidy 2>/dev/null; then
  clang-tidy *.cpp -- -std=c++11
else
  echo "WARNING: clang-tidy not available."
fi

echo "====================================================="
echo "4. If the section below is empty, clang-format does not find any formatting issues"
echo "   You can fix formatting errors using \"clang-format -i <filename>\" on command line"
echo "====================================================="

if hash clang-format 2>/dev/null; then
  # different LLVMs have slightly different configurations which can break things, so regenerate
  echo "# generated using: clang-format -style=llvm -dump-config > .clang-format" > .clang-format
  clang-format -style=llvm -dump-config >> .clang-format
  for f in ./*.cpp; do
    echo "Running clang-format on $f"
    clang-format $f | diff $f -
  done
else
  echo "WARNING: clang-format not available"
fi

echo "====================================================="
echo "5. If there are any memory leaks, it should be in the output below"
echo "====================================================="

rm ./a.out 2>/dev/null

g++ -std=c++11 -fsanitize=address -fno-omit-frame-pointer -g *.cpp
# Execute program
$EXEC_PROGRAM > /dev/null 2> /dev/null


echo "====================================================="
echo "6. Using valgrind to check for memory leaks"
echo "   Check for \"definitely lost\" in the output below"
echo "====================================================="

rm ./a.out 2>/dev/null

if hash valgrind 2>/dev/null; then
  g++ -g -std=c++11 *.cpp
  # redirect program output to /dev/null will running valgrind
  valgrind --log-file="valgrind-output.txt" $EXEC_PROGRAM > /dev/null 2>/dev/null
  cat valgrind-output.txt
  rm valgrind-output.txt 2>/dev/null
else
  echo "WARNING: valgrind not available"
fi


# Remove the executable
rm -rf ./a.out* 2>/dev/null

date

echo "====================================================="
echo "To create an output.txt file with all the output from this script"
echo "Run the below command"
echo "      ./create-output.sh > output.txt 2>&1 "
echo "====================================================="
