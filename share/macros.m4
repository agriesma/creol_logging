dnl
dnl macros.m4 -- Macros used to enerate interpreters.
dnl
dnl Copyright (c) 2007, 2008
dnl
dnl The purpose of this file is to create the files `interpreter.maude'
dnl and `modelchecker.maude'.  These files have to be processed with
dnl m4, with either one of `CREOL' or `MODELCHECK' defined.
dnl
dnl See the lines below for its license
dnl
changecom`'dnl
define(`KIND', ifdef(`TIME', `real-time ')ifdef(`MODELCHECK', `model-checker', `interpreter'))dnl
dnl
dnl The macro STEP is used to indicate that the specified transition
dnl may be both an equation (this is the case for model checking,
dnl or a rule (in the interpreter).
dnl $1 is the pre-condition of the rule.
dnl $2 is the post-condition of the rule.
dnl $3 is an annotation.  It must not be empty, and usually contains at
dnl    least the label.
define(`STEP',dnl
ifdef(`MODELCHECK',dnl
`eq
  $1
  =
  $2
  $3 .',dnl
`rl
  $1
  =>
  $2
  $3 .'))dnl
dnl
dnl The macro CSTEP is used to indicate that the specified transition
dnl may be both a conditional equation (this is the case for model checking),
dnl or a conditional rule (in the interpreter).
dnl $1 is the pre-condition of the rule.
dnl $2 is the post-condition of the rule.
dnl $3 is the condition.
dnl $4 is an annotation.  It must not be empty, and usually contains at
dnl    least the label.
define(`CSTEP',dnl
ifdef(`MODELCHECK',dnl
`ceq
  $1
  =
  $2
  if $3
  $4 .',dnl
`crl
  $1
  =>
  $2
  if $3
  $4 .'))dnl
dnl
dnl These macros are used to evaluate non-guard expressions.
dnl
define(`EVAL',     `EVALGUARD($1, $2, noMsg, $3)')dnl
define(`EVALLIST', `EVALGUARDLIST($1, $2, noMsg, $3)')dnl
define(`EVALSET',  `EVALGUARDSET($1, $2, noMsg, $3)')dnl
define(`EVALMAP',  `EVALGUARDMAP($1, $2, noMsg, $3)')dnl
dnl
dnl These macros are used to evaluate guard expressions.
dnl $1 is the expression,
dnl $2 is the state valuation,
dnl $3 is the message queue, and
dnl $4 is the current time.
dnl
ifdef(`TIME',dnl
`define(`EVALGUARD', evalGuard($1, $2, $3, $4))dnl
define(`EVALGUARDLIST', evalGuardList($1, $2, $3, $4))dnl
define(`EVALGUARDSET', evalGuardSet($1, $2, $3, $4))dnl
define(`EVALGUARDMAP', evalGuardMap($1, $2, $3, $4))dnl
define(`ENABLED', enabled($1, $2, $3, $4))dnl
define(`READY', ready($1, $2, $3, $4))',dnl
`define(`EVALGUARD', evalGuard($1, $2, $3))dnl
define(`EVALGUARDLIST', evalGuardList($1, $2, $3))dnl
define(`EVALGUARDSET', evalGuardSet($1, $2, $3))dnl
define(`EVALGUARDMAP', evalGuardMap($1, $2, $3))dnl
define(`ENABLED', enabled($1, $2, $3))dnl
define(`READY', ready($1, $2, $3))')