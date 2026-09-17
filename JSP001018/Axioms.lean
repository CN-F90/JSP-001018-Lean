import JSP001018.Util
import JSP001018.Arith
import JSP001018.Family
import JSP001018.Sequence
import JSP001018

/-!
# Axiom audit

`#print axioms` lists every axiom the kernel had to trust in order to accept the
declaration (and everything it transitively depends on).  We expect only the two
foundational items that Lean always admits — `propext` and `Classical.choice`
(from the `classical` block) — and *no* user-introduced axiom.
-/

#print axioms JSP001018.erdos_1213
#print axioms JSP001018.erdos_1213_nonvacuous

-- Supporting declarations, for completeness
#print axioms ListUtil.bounded_nodup_length_le
#print axioms JSP001018.length_famList
#print axioms JSP001018.nodup_famList
#print axioms JSP001018.famList_mem_spec
#print axioms JSP001018.length_lower
#print axioms JSP001018.isum_cap_le
#print axioms JSP001018.weight_bound
