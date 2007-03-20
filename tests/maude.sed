#! /bin/sed
# Sanitize the output of maude, different give slightly different output.
/^rewrites: [[:digit:]][[:digit:]]*/ d
/^states: [[:digit:]][[:digit:]]*/ d
s/^search \[[[:digit:]]\]/search/
