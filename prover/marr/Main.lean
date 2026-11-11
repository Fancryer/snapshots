import Marr

/-- Print the axioms that the checked facts depend on, so that the build log
records which theorems are proved and on what they rest. -/
def main : IO Unit := do
  IO.println "Mårran core: syntactic facts about freeze"
  IO.println "----------------------------------------------"
  IO.println "frozen_freeze        : freeze always yields a frozen term"
  IO.println "frozen_freezeStmt    : ... a frozen statement"
  IO.println "frozen_freezeBlock   : ... a frozen block"
  IO.println "frozen_freeze_id     : freeze is the identity on frozen terms"
  IO.println "frozen_freezeBlock_id: ... on frozen blocks"
  IO.println "bindingsOf_freezeStmt: freezing preserves the bound names"
  IO.println "frozen_fv_subset     : fv (freeze t) is a subset of fv t"
  IO.println ""
  IO.println "These are the syntactic lemmas used by the paper's"
  IO.println "freeze-typing and snapshot lemmas.  Isolation, preservation,"
  IO.println "effect soundness and referential transparency are proved on"
  IO.println "paper, not here."
