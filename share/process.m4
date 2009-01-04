fmod CREOL-PROCESS is

  protecting CREOL-STM-LIST .

  sort Process .

  op idle : -> Process [ctor `format' (!b o)] .  
  op notFound : -> Process [ctor `format' (!b o)] .  
  op {_|_} : Subst StmtList -> Process [ctor `format' (r o r o r o)] . 

  var L : Subst .
  eq { L | noStmt } = idle . --- if ".label" is needed this is dangerous!
  eq idle = { noSubst | noStmt } [nonexec metadata "Causes infinite loops."] .

endfm

view Process from TRIV to CREOL-PROCESS is
  sort Elt to Process .
endv


*** Specifies a process pool, here a multiset of Processes
***
fmod CREOL-PROCESS-POOL is

ifdef(`EXPERIMENTAL',dnl
    protecting MULTISET{Process} * (sort MSet{Process} to MProc,
                                    sort NeMSet{Process} to NeMProc,
                                    op empty : -> MSet{Process} to noProc) .
,
    protecting CREOL-PROCESS .

    sort MProc .
    subsort Process < MProc .
    op noProc : -> MProc [ctor] .
    op _`,'_ : MProc MProc -> MProc
        [ctor assoc comm id: noProc prec 41 ``format'' (d r os d)] .
)

endfm
