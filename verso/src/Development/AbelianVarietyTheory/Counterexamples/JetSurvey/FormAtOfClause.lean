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
Unfold `WeightAlgebra.PJ.phiC`. Use `split_ifs`. Use `mul_nonneg (Nat.cast_nonneg _) (Real.sInf_nonneg ?_)` and prove the remaining obligations. Introduce and unpack `x ⟨l, -, hl, rfl⟩`. Distinguish the cases in `h0 : (P.loc X.dat (WeightAlgebra.resCh la)).beS (X.pt66 la y) = 0`.

Rewrite using `[h0, map_zero]`. Use `(hl _ (fun a => ?_) h0).le` and prove the remaining obligations. Take `⟨ι, _, b, hb⟩` from `(P.loc X.dat (WeightAlgebra.resCh la)).be_posDef (X.pt66 la y)`. Use `show 0 ≤ (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a`. Distinguish the cases in `hc : (fun i => ((b.repr a i : ℤ) : ℝ)) = 0`.

Establish `: a = 0`. Apply `b.repr.injective` to reduce the goal to its premises. Use extensionality with `i`. Use `congrFun hc i` as an intermediate fact. Simplify using `using this`.

Simplify using `[this]`. Establish `h1` using `hb _ hc`. Establish `h2 : (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) a a = ∑ i, ∑ k, ((b.repr a i : ℤ) : ℝ) * ((b.repr a k : ℤ) : ℝ) * (P.loc X.dat (WeightAlgebra.resCh la)).be (X.pt66 la y) (b i) (b k)` using `by conv_lhs => rw [← b.sum_repr a]`. Simplify using `only [map_sum, map_zsmul, LinearMap.sum_apply, LinearMap.smul_apply, zsmul_eq_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => by ring`. Rewrite using `[h2]`. Conclude with `h1.le`. Conclude with `le_rfl`.
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
Introduce `la y`. Rewrite using `[map_zero, X.vAt_zero]`. Conclude with `le_top`.
-/
theorem zero (X : WeightAlgebra.PJ D B P j) (i : ℕ) : EtVal X i 0 := by
  intro la y
  rw [map_zero, X.vAt_zero]; exact le_top

/- English proof (translation)
Use `(X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)` and prove the remaining obligations. Conclude with `EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))`.
-/
theorem mem_Mlat (X : WeightAlgebra.PJ D B P j) (i : ℕ) (η : B.Cusp j (Formalism.L2.Pj.wEt D j i)) (h : EtVal X i η) :
    η ∈ B.Mlat j _ := by
  refine (X.Mlat_eq _ η).2 fun la y => le_trans ?_ (h la y)
  exact EReal.coe_nonneg.2 (mul_nonneg (by positivity) (phiC_nonneg X la y))

end GlobalTheory.EtaValuationTest
