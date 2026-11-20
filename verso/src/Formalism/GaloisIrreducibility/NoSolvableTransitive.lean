import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OrbitSubSum
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.RestrictRoots
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.LemmaAOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.IrredOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PermSubSumInv
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.ResiduesLe
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.FewLargeParts
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.BlockBoundOfOrbits
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.OneNonUnit
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PowerPCycle
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.AltNotSolvable
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.NoSolvableOf
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.PrimitiveOfPCycle
import Formalism.GaloisIrreducibility.GaloisIrreducibilityProofs.JordanPrime

namespace Formalism.GaloisIrreducibility

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem lemmaA : LemmaA := lemmaAOf_statement orbit_subset_sum restrict_roots_to_subfield

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem irred : Irred := irreducible_of_galois_conditions lemmaA
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem permSubSumInv : PermSubSumInv := permutation_subset_sum_invariant

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem residuesLe : ResiduesLe := residues_count_le
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem bbAtMostThree : BBAtMostThree := block_bound_of_orbits few_large_cycle_parts
/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem cardGL : CardGL := by
  intro K _ _ _ N
  have hinj : Function.Injective
      (fun g : GL (Fin N) K => fun i j : Fin N => (g : Matrix (Fin N) (Fin N) K) i j) := by
    intro g h hgh
    apply Units.ext
    exact Matrix.ext fun i j => congrFun (congrFun hgh i) j
  refine le_trans (Fintype.card_le_of_injective _ hinj) (le_of_eq ?_)
  rw [Fintype.card_fun, Fintype.card_fun, Fintype.card_fin, ← pow_mul, sq]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem primitiveOfPCycle : PrimitiveOfPCycle := primitive_of_p_cycle
/- English proof (translation)
A detailed English derivation is pending.
-/
theorem jordanPrime : JordanPrime := jordan_prime_cycle_theorem

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem noSolvableTransitive : NoSolvableTransitive :=
  no_solvable_subgroup_of power_of_p_cycle primitive_of_p_cycle jordan_prime_cycle_theorem alternating_group_not_solvable

end Formalism.GaloisIrreducibility
