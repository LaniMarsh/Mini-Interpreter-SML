#!/bin/bash

# First, check for syntax errors by running hw3.sml through the SML interpreter
syntax_check=$(sml evaluator.sml </dev/null 2>&1)
# Check if there was any error in the syntax check
if echo "$syntax_check" | grep -q "Uncaught"; then
  echo "Syntax error detected in assignemnt:"
  echo "$syntax_check"
  exit 1
fi

# If no syntax errors, proceed to run the Python script
output=$(python3 run.py)

# Get the number of lines in the output
# usually this would be used to truncate the file
# to only the functions that have been implemented
# going to ignore that for this asgn
output_lines=$(cat correct | wc -l)

# Check if 'run.py' poduced any output
if [[ -z "$output" ]]; then
  echo "Error: 'run.py' produced no output!"
  exit 1
fi

# Check if 'correct' file exists
if [[ ! -f correct ]]; then
  echo "'correct' file not found!"
  exit 1
fi

diff -y -B -s -W 120 <(head -n "$output_lines" correct) <(echo "$output")