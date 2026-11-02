import Mortality

/-!
Run this file with `lake env lean AxiomAudit.lean` to print the axiom profiles
of the principal paper-facing and analytic endpoints.
-/

#print axioms Mortality.SourceMachine.KorecPrimeSystem.existsForEverySpan
#print axioms Mortality.SourceMachine.LeanWangMortality.mortality_iff_evalDom_unconditional
#print axioms Mortality.PaperTheorem.variableMatrix_primrec
#print axioms Mortality.PaperTheorem.no_computable_matrix_decider
#print axioms Mortality.PaperTheorem.paper_result
