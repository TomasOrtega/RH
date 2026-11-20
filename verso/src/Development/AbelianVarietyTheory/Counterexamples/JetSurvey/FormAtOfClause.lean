import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ETExSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.EtValLink
import Formalism.LocalToGlobal.ProjectiveLattices.Adm3OfExtension

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.EtaValuationTest

open Formalism.MainNotions Formalism.BasicNotions NumberField IsDedekindDomain Formalism.MainNotions.ModuliIntegralCharts.H1

variable {D : Formalism.BasicNotions.D7} {B : WeightFamilies.Prov D} {P : ModuliIntegralCharts.Prov D} {j : ℕ}

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Consider separately whether the proposition holds or fails. Establish an intermediate fact. Reduce the claim to the hypotheses of an applicable result.

By extensionality, compare the relevant components. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Simplify using the standard rewrite rules. Establish an intermediate fact.

Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem phiC_nonneg (X : WeightAlgebra.PJ D B P j) (la : HeightOneSpectrum (𝓞 B.KO)) (y : X.Pt la) : 0 ≤ X.phiC la y := by
  unfold WeightAlgebra.PJ.phiC
  split_ifs
  · refine mul_nonneg (Nat.cast_nonneg _) (Real.sInf_nonneg ?_)
    rintro x ⟨l, -, hl, rfl⟩
    by_cases h0 : (P.loc X.dat (WeightAlgebra.resCh la)).beS (X.pt66 la y) = 0
    · rw [h0, map_zero]
    · refine (hl _ (fun a => ?_) h0).le
      obtain ⟨ι, _, b, hb⟩ := (P.loc X.dat (WeightAlgebra.resCh la)).be_posDef (X.pt66 la y)
      show 0 ≤ (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a
      by_cases hc : (fun i => ((b.repr a i : ℤ) : ℝ)) = 0
      · have : a = 0 := by
          apply b.repr.injective
          ext i
          have := congrFun hc i
          simpa using this
        simp [this]
      · have h1 := hb _ hc
        have h2 : (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a =
            ∑ i, ∑ k, ((b.repr a i : ℤ) : ℝ) * ((b.repr a k : ℤ) : ℝ) *
              (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (b i) (b k) := by
          conv_lhs => rw [← b.sum_repr a]
          simp only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring
        rw [h2]; exact h1.le
  · exact le_rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem zero (X : WeightAlgebra.PJ D B P j) (i : ℕ) : EtVal X i 0 := by
  intro la y
  rw [map_zero, X.vAt_zero]; exact le_top

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
