import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HodgeLowerBound.StatementsHodgeFibreSteps
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.LowerBoundFree
open scoped Matrix

namespace PlueckerExpand

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)] {Ω : Type} [Field Ω]

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩`.
-/
theorem isValueAt_intCast (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (n : ℤ) :
    IsValueAt y (n : Ω) z (n : ℂ) :=
  ⟨0, C n, 1, isMultiHomog_C_zero n, isMultiHomog_one, by simp, by simp, by simp, by simp⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using LineFlag.isValueAt_zero' y z`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `LineFlag.isValueAt_add (h a) ih`.
-/
theorem isValueAt_finsetSum {α : Type} (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (s : Finset α)
    (f : α → Ω) (v : α → ℂ) (h : ∀ i, IsValueAt y (f i) z (v i)) :
    IsValueAt y (∑ i ∈ s, f i) z (∑ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using LineFlag.isValueAt_zero' y z
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact LineFlag.isValueAt_add (h a) ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using isValueAt_one_self y z`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.prod_insert ha]`. Conclude with `LineFlag.isValueAt_mul (h a) ih`.
-/
theorem isValueAt_finsetProd {α : Type} (y : (Σ k, ι k) → Ω) (z : (Σ k, ι k) → ℂ) (s : Finset α)
    (f : α → Ω) (v : α → ℂ) (h : ∀ i, IsValueAt y (f i) z (v i)) :
    IsValueAt y (∏ i ∈ s, f i) z (∏ i ∈ s, v i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using isValueAt_one_self y z
  | insert a s ha ih =>
    rw [Finset.prod_insert ha, Finset.prod_insert ha]
    exact LineFlag.isValueAt_mul (h a) ih

end PlueckerExpand

/- English proof (translation)
Introduce `K _ ι _ Ω _ E _ _ y c b N r φ bfr z V A Az hz hV hA`. Use `choose v0 hv0 hVeq using fun q => (hV q).2`. Use `set P : ℂ := ∏ k, z ⟨k, c k⟩ ^ b k with hP`. Use `⟨fun q hq => ?_, fun q σ => ?_, ?_⟩` and prove the remaining obligations. Establish `h0 : φ (bfr ∘ q) = 0` using `φ.map_eq_zero_of_not_injective _ fun hinj => hq fun a a' h => hinj (by simp [h])`.

Establish `hval : IsValueAt y (φ (bfr ∘ q) * twistFactor y c b) z 0`. Rewrite using `[h0, zero_mul]`. Conclude with `LineFlag.isValueAt_zero' y z`. Rewrite using `[hVeq q, LineFlag.isValueAt_unique hz (hv0 q) hval, zero_mul]`. Establish `hperm : φ (bfr ∘ (q ∘ σ)) * twistFactor y c b = ((Equiv.Perm.sign σ : ℤ) : Ω) * (φ (bfr ∘ q) * twistFactor y c b)`.

Rewrite using `[show bfr ∘ (q ∘ σ) = (bfr ∘ q) ∘ σ from rfl, φ.map_perm, Units.smul_def, zsmul_eq_mul, mul_assoc]`. Establish `hval` using `LineFlag.isValueAt_mul (PlueckerExpand.isValueAt_intCast y z (Equiv.Perm.sign σ : ℤ)) (hv0 q)`. Rewrite `hval` using `[← hperm]`. Rewrite using `[hVeq (q ∘ σ), hVeq q, LineFlag.isValueAt_unique hz (hv0 (q ∘ σ)) hval, mul_assoc]`. Use `⟨∑ q, (∏ a, Az (q a) a) * v0 q, ?_, ?_⟩` and prove the remaining obligations.

Establish `hexp : φ (fun a => ∑ q, A q a • bfr q) = ∑ q : Fin r → Fin N, (∏ a, A (q a) a) * φ (bfr ∘ q)`. Use `φ.toMultilinearMap.map_sum (fun a q => A q a • bfr q)` as an intermediate fact. Simplify using `only [AlternatingMap.coe_multilinearMap] at this`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations.

Establish `h2` using `φ.toMultilinearMap.map_smul_univ (fun a => A (q a) a) (fun a => bfr (q a))`. Simplify using `only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2`. Conclude with `h2`. Rewrite using `[hexp, Finset.sum_mul]`. Use `PlueckerExpand.isValueAt_finsetSum y z _ _ _ fun q => ?_` and prove the remaining obligations.

Rewrite using `[mul_assoc]`. Conclude with `LineFlag.isValueAt_mul (PlueckerExpand.isValueAt_finsetProd y z _ _ _ fun a => hA (q a) a) (hv0 q)`. Rewrite using `[Finset.mul_sum]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hVeq q]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem PlueckerExpand.proof : PlueckerExpand.Statement := by
  intro K _ ι _ Ω _ E _ _ y c b N r φ bfr z V A Az hz hV hA
  choose v0 hv0 hVeq using fun q => (hV q).2
  set P : ℂ := ∏ k, z ⟨k, c k⟩ ^ b k with hP
  refine ⟨fun q hq => ?_, fun q σ => ?_, ?_⟩
  · have h0 : φ (bfr ∘ q) = 0 := φ.map_eq_zero_of_not_injective _ fun hinj => hq fun a a' h => hinj (by simp [h])
    have hval : IsValueAt y (φ (bfr ∘ q) * twistFactor y c b) z 0 := by
      rw [h0, zero_mul]; exact LineFlag.isValueAt_zero' y z
    rw [hVeq q, LineFlag.isValueAt_unique hz (hv0 q) hval, zero_mul]
  · have hperm : φ (bfr ∘ (q ∘ σ)) * twistFactor y c b =
        ((Equiv.Perm.sign σ : ℤ) : Ω) * (φ (bfr ∘ q) * twistFactor y c b) := by
      rw [show bfr ∘ (q ∘ σ) = (bfr ∘ q) ∘ σ from rfl, φ.map_perm, Units.smul_def, zsmul_eq_mul, mul_assoc]
    have hval := LineFlag.isValueAt_mul (PlueckerExpand.isValueAt_intCast y z (Equiv.Perm.sign σ : ℤ)) (hv0 q)
    rw [← hperm] at hval
    rw [hVeq (q ∘ σ), hVeq q, LineFlag.isValueAt_unique hz (hv0 (q ∘ σ)) hval, mul_assoc]
  · refine ⟨∑ q, (∏ a, Az (q a) a) * v0 q, ?_, ?_⟩
    · have hexp : φ (fun a => ∑ q, A q a • bfr q) = ∑ q : Fin r → Fin N, (∏ a, A (q a) a) * φ (bfr ∘ q) := by
        have := φ.toMultilinearMap.map_sum (fun a q => A q a • bfr q)
        simp only [AlternatingMap.coe_multilinearMap] at this
        rw [this]
        refine Finset.sum_congr rfl fun q _ => ?_
        have h2 := φ.toMultilinearMap.map_smul_univ (fun a => A (q a) a) (fun a => bfr (q a))
        simp only [AlternatingMap.coe_multilinearMap, smul_eq_mul] at h2
        exact h2
      rw [hexp, Finset.sum_mul]
      refine PlueckerExpand.isValueAt_finsetSum y z _ _ _ fun q => ?_
      rw [mul_assoc]
      exact LineFlag.isValueAt_mul
        (PlueckerExpand.isValueAt_finsetProd y z _ _ _ fun a => hA (q a) a) (hv0 q)
    · rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun q _ => ?_
      rw [hVeq q]; ring

end GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.LowerBoundFree
