import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StSmallSetTubeVolume
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StPrimeTubeVolume
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial MeasureTheory ComplexSets

noncomputable section

/- English proof (translation)
Introduce `x hx`. Establish `hle : I ≤ RingHom.ker (MvPolynomial.eval x)` using `fun q hq => (RingHom.mem_ker).2 (hx q hq)`. Establish `: (RingHom.ker (MvPolynomial.eval x)).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨P, hP, hPle⟩` from `Ideal.exists_minimalPrimes_le hle`. Conclude with `Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)`.
-/
theorem zeroSet_subset_biUnion_minimalPrimes {n : ℕ} (I : Ideal (MvPolynomial (Fin n) ℂ)) :
    zeroSet I ⊆ ⋃ P ∈ I.minimalPrimes, zeroSet P := by
  intro x hx
  have hle : I ≤ RingHom.ker (MvPolynomial.eval x) := fun q hq => (RingHom.mem_ker).2 (hx q hq)
  have : (RingHom.ker (MvPolynomial.eval x)).IsPrime := RingHom.ker_isPrime _
  obtain ⟨P, hP, hPle⟩ := Ideal.exists_minimalPrimes_le hle
  exact Set.mem_biUnion hP fun q hq => (RingHom.mem_ker).1 (hPle hq)

/- English proof (translation)
Proceed by induction on `x using WithBot.recBotCoe with`. Consider the case `bot => simp at h0`. Consider the case `coe e`. Proceed by induction on `e using ENat.recTopCoe with`. Consider the case `top => simp at h`.

Consider the case `coe m`. Establish `hm : m < d` using `by exact_mod_cast h`. Use `⟨by omega, ?_⟩` and prove the remaining obligations. Rewrite using `[← WithBot.coe_natCast]`. Conclude with `WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))`.
-/
theorem withBot_enat_le_pred {x : WithBot ℕ∞} {d : ℕ} (h0 : 0 ≤ x) (h : x < (d : WithBot ℕ∞)) :
    0 < d ∧ x ≤ ((d - 1 : ℕ) : WithBot ℕ∞) := by
  induction x using WithBot.recBotCoe with
  | bot => simp at h0
  | coe e =>
    induction e using ENat.recTopCoe with
    | top => simp at h
    | coe m =>
      have hm : m < d := by exact_mod_cast h
      refine ⟨by omega, ?_⟩
      rw [← WithBot.coe_natCast]
      exact WithBot.coe_le_coe.2 (by exact_mod_cast (by omega : m ≤ d - 1))

/- English proof (translation)
Establish `hprime : P.IsPrime` using `hP.1.1`. Establish `hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I)` using `ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)`. Establish `hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P)` using `ringKrullDim_nonneg_of_nontrivial`. Take `⟨hd, hk⟩` from `withBot_enat_le_pred hnn (hle.trans_lt hdim)`. Take `⟨C, hC, hCr⟩` from `h n (d - 1) P K hprime hk hK`.

Use `⟨C, hC, fun r hr => ?_⟩` and prove the remaining obligations. Establish `he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d` using `by omega`. Simplify `hCr r hr` using `[he]`.
-/
theorem minimalPrime_tube_bound (h : PrimeTubeVolume.Statement) {n d : ℕ}
    {I : Ideal (MvPolynomial (Fin n) ℂ)} {K : Set (Fin n → ℂ)}
    (hdim : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) < (d : ℕ)) (hK : IsCompact K)
    {P : Ideal (MvPolynomial (Fin n) ℂ)} (hP : P ∈ I.minimalPrimes) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
      volume (Metric.thickening r (zeroSet P ∩ K)) ≤
        ENNReal.ofReal (C * r ^ ((2 * n + 2 : ℤ) - 2 * d)) := by
  have hprime : P.IsPrime := hP.1.1
  have hle : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ I) :=
    ringKrullDim_le_of_surjective (Ideal.Quotient.factor hP.1.2) (Ideal.Quotient.factor_surjective hP.1.2)
  have hnn : 0 ≤ ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ P) := ringKrullDim_nonneg_of_nontrivial
  obtain ⟨hd, hk⟩ := withBot_enat_le_pred hnn (hle.trans_lt hdim)
  obtain ⟨C, hC, hCr⟩ := h n (d - 1) P K hprime hk hK
  refine ⟨C, hC, fun r hr => ?_⟩
  have he : ((2 * n : ℤ) - 2 * ((d - 1 : ℕ) : ℤ)) = (2 * n + 2 : ℤ) - 2 * d := by omega
  simpa [he] using hCr r hr

/- English proof (translation)
Introduce `n d I K hdim hK`. Use `set e : ℤ := (2 * n + 2 : ℤ) - 2 * d`. Establish `key : ∀ F : Finset (Ideal (MvPolynomial (Fin n) ℂ)), (↑F : Set _) ⊆ I.minimalPrimes → ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1, volume (Metric.thickening r (⋃ P ∈ F, zeroSet P ∩ K)) ≤ ENNReal.ofReal (C * r ^ e)`. Introduce `F`. Proceed by induction on `F using Finset.induction_on with`.

Consider the case `empty`. Introduce `_`. Conclude with `⟨0, le_rfl, fun r _ => by simp⟩`. Consider the case `insert a F ha ih`. Introduce `hsub`.

Take `⟨C₁, hC₁, h₁⟩` from `ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))`. Take `⟨C₂, hC₂, h₂⟩` from `minimalPrime_tube_bound h hdim hK (hsub (Finset.mem_insert_self a F))`. Use `⟨C₂ + C₁, add_nonneg hC₂ hC₁, fun r hr => ?_⟩` and prove the remaining obligations. Establish `hre : 0 ≤ r ^ e` using `zpow_nonneg hr.1.le e`. Rewrite using `[Finset.set_biUnion_insert, Metric.thickening_union, add_mul, ENNReal.ofReal_add (mul_nonneg hC₂ hre) (mul_nonneg hC₁ hre)]`.

Conclude with `(measure_union_le _ _).trans (add_le_add (h₂ r hr) (h₁ r hr))`. Take `⟨F, hF⟩` from `(Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).exists_finset_coe`. Take `⟨C, hC, hCr⟩` from `key F hF.le`. Use `⟨C, hC, fun r hr => le_trans (measure_mono (Metric.thickening_subset_of_subset r ?_)) (hCr r hr)⟩` and prove the remaining obligations. Introduce `x ⟨hxI, hxK⟩`.

Take `⟨P, hP, hxP⟩` from `Set.mem_iUnion₂.1 (zeroSet_subset_biUnion_minimalPrimes I hxI)`. Rewrite `hP` using `[← hF]`. Conclude with `Set.mem_iUnion₂.2 ⟨P, hP, hxP, hxK⟩`.
-/
theorem SmallSetTubeVolume.proof (h : PrimeTubeVolume.Statement) : SmallSetTubeVolume.Statement := by
  intro n d I K hdim hK
  set e : ℤ := (2 * n + 2 : ℤ) - 2 * d
  have key : ∀ F : Finset (Ideal (MvPolynomial (Fin n) ℂ)), (↑F : Set _) ⊆ I.minimalPrimes →
      ∃ C : ℝ, 0 ≤ C ∧ ∀ r ∈ Set.Ioc (0 : ℝ) 1,
        volume (Metric.thickening r (⋃ P ∈ F, zeroSet P ∩ K)) ≤ ENNReal.ofReal (C * r ^ e) := by
    intro F
    induction F using Finset.induction_on with
    | empty =>
      intro _
      exact ⟨0, le_rfl, fun r _ => by simp⟩
    | insert a F ha ih =>
      intro hsub
      obtain ⟨C₁, hC₁, h₁⟩ := ih (fun x hx => hsub (Finset.mem_insert_of_mem hx))
      obtain ⟨C₂, hC₂, h₂⟩ := minimalPrime_tube_bound h hdim hK (hsub (Finset.mem_insert_self a F))
      refine ⟨C₂ + C₁, add_nonneg hC₂ hC₁, fun r hr => ?_⟩
      have hre : 0 ≤ r ^ e := zpow_nonneg hr.1.le e
      rw [Finset.set_biUnion_insert, Metric.thickening_union, add_mul,
        ENNReal.ofReal_add (mul_nonneg hC₂ hre) (mul_nonneg hC₁ hre)]
      exact (measure_union_le _ _).trans (add_le_add (h₂ r hr) (h₁ r hr))
  obtain ⟨F, hF⟩ := (Ideal.finite_minimalPrimes_of_isNoetherianRing _ I).exists_finset_coe
  obtain ⟨C, hC, hCr⟩ := key F hF.le
  refine ⟨C, hC, fun r hr => le_trans (measure_mono (Metric.thickening_subset_of_subset r ?_)) (hCr r hr)⟩
  intro x ⟨hxI, hxK⟩
  obtain ⟨P, hP, hxP⟩ := Set.mem_iUnion₂.1 (zeroSet_subset_biUnion_minimalPrimes I hxI)
  rw [← hF] at hP
  exact Set.mem_iUnion₂.2 ⟨P, hP, hxP, hxK⟩

end

end GroundTheory.Heights₂.Heights
