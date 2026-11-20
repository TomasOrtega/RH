import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.CrystallinePeriods.RingIface
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Development.AbelianVarietyTheory.CrystallinePeriods.CrisLoc
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

noncomputable section

namespace GlobalTheory.DenomCris

variable {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [Algebra ℤ_[l] O]

/- English proof (translation)
Take `⟨e, -, hne⟩` from `GlobalTheory.CrisLoc.exists_root_ne_one l`. Use `haveI : Nontrivial (Per.Fl l) := ⟨e, 1, hne⟩`. Rewrite using `[map_one]`. Conclude with `one_ne_zero`.
-/
theorem cc_one : WittVector.constantCoeff (1 : Ainf l) ≠ 0 := by
  obtain ⟨e, -, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
  haveI : Nontrivial (Per.Fl l) := ⟨e, 1, hne⟩
  rw [map_one]
  exact one_ne_zero

/- English proof (translation)
Rewrite using `[map_mul]`. Conclude with `mul_ne_zero hx hy`.
-/
theorem cc_mul {x y : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (hy : WittVector.constantCoeff y ≠ 0) :
    WittVector.constantCoeff (x * y) ≠ 0 := by
  rw [map_mul]
  exact mul_ne_zero hx hy

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `cc_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `cc_mul ih hx`.
-/
theorem cc_pow {x : Ainf l} (hx : WittVector.constantCoeff x ≠ 0) (n : ℕ) :
    WittVector.constantCoeff (x ^ n) ≠ 0 := by
  induction n with
  | zero => rw [pow_zero]; exact cc_one
  | succ n ih => rw [pow_succ]; exact cc_mul ih hx

/- English proof (translation)
Proceed by induction on `r using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, cc_one, 0, by simp⟩`. Consider the case `tmul o y`. Take `⟨e, he, hne⟩` from `GlobalTheory.CrisLoc.exists_root_ne_one l`. Take `⟨n, a, ha⟩` from `GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne y`.

Use `⟨(Per.tm e - 1) ^ n, cc_pow (GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne) n, o ⊗ₜ a, ?_⟩` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Express the relevant statement in the definitionally equal form `o ⊗ₜ[ℤ_[l]] (algebraMap (Per.Acris l) (Per.Bcris l) (algebraMap (Ainf l) (Per.Acris l) ((Per.tm e - 1) ^ n)) * y) = o ⊗ₜ[ℤ_[l]] algebraMap (Per.Acris l) (Per.Bcris l) a`. Rewrite using `[map_pow, map_pow, mul_comm, ha]`. Consider the case `add r₁ r₂ h₁ h₂`.

Take `⟨s₁, hs₁, a₁, e₁⟩` from `h₁`. Take `⟨s₂, hs₂, a₂, e₂⟩` from `h₂`. Use `⟨s₁ * s₂, cc_mul hs₁ hs₂, ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) * a₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) * a₂, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s)` using `fun s => rfl`. Establish `hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) = ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂))`.

Rewrite using `[map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[hm, map_add, map_mul (toOB l O), map_mul (toOB l O), hc, hc, ← e₁, ← e₂]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_eq_toOB (r : OB l O) : ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ a : OCr l O,
    ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) * r = toOB l O a := by
  induction r using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul o y =>
    obtain ⟨e, he, hne⟩ := GlobalTheory.CrisLoc.exists_root_ne_one l
    obtain ⟨n, a, ha⟩ := GlobalTheory.CrisLoc.exists_mul_pow_eq l e he hne y
    refine ⟨(Per.tm e - 1) ^ n, cc_pow (GlobalTheory.CrisLoc.constantCoeff_root_ne_zero l e hne) n, o ⊗ₜ a, ?_⟩
    rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    change o ⊗ₜ[ℤ_[l]] (algebraMap (Per.Acris l) (Per.Bcris l)
      (algebraMap (Ainf l) (Per.Acris l) ((Per.tm e - 1) ^ n)) * y) =
      o ⊗ₜ[ℤ_[l]] algebraMap (Per.Acris l) (Per.Bcris l) a
    rw [map_pow, map_pow, mul_comm, ha]
  | add r₁ r₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, a₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, a₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) * a₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) * a₂, ?_⟩
    have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
        (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [hm, map_add, map_mul (toOB l O), map_mul (toOB l O), hc, hc, ← e₁, ← e₂]
    ring

/- English proof (translation)
Introduce `l _ O K _ _ _ _ _ _ G _ _ T b`. Establish `hsm : ∀ (r : OCr l O) (z : TW (OCr l O) T), TWincl (toOB l O) T (r • z) = toOB l O r • TWincl (toOB l O) T z`. Introduce `r z`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul x t => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]`. Consider the case `add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]`. Establish `hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) = (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s)` using `fun s => rfl`. Proceed by induction on `b using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨1, cc_one, 0, by simp⟩`.

Consider the case `tmul r t`. Take `⟨s, hs, a, e⟩` from `exists_mul_eq_toOB r`. Conclude with `⟨s, hs, a ⊗ₜ t, by rw [TensorProduct.smul_tmul', smul_eq_mul, e]; rfl⟩`. Consider the case `add b₁ b₂ h₁ h₂`. Take `⟨s₁, hs₁, β₁, e₁⟩` from `h₁`.

Take `⟨s₂, hs₂, β₂, e₂⟩` from `h₂`. Use `⟨s₁ * s₂, cc_mul hs₁ hs₂, ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) • β₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) • β₂, ?_⟩` and prove the remaining obligations. Establish `hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) = ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) * ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂))`. Rewrite using `[map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]`. Rewrite using `[map_add, hsm, hsm, hc, hc, ← e₁, ← e₂, smul_smul, smul_smul, hm, smul_add, mul_comm (_ ⊗ₜ[ℤ_[l]] _)]`.
-/
theorem exists_smul_eq_TWincl : ∀ {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Field K] [Algebra ℚ_[l] K] [Algebra O K] [TopologicalSpace K] {G : Type} [Group G] [TopologicalSpace G] (T : LocLat G ℚ_[l] K O) (b : TW (OB l O) T), ∃ s : Ainf l, WittVector.constantCoeff s ≠ 0 ∧ ∃ β : TW (OCr l O) T, ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) : OB l O) • b = TWincl (toOB l O) T β := by
  intro l _ O K _ _ _ _ _ _ G _ _ T b
  have hsm : ∀ (r : OCr l O) (z : TW (OCr l O) T),
      TWincl (toOB l O) T (r • z) = toOB l O r • TWincl (toOB l O) T z := by
    intro r z
    induction z using TensorProduct.induction_on with
    | zero => simp
    | tmul x t => simp [TWincl, TensorProduct.smul_tmul', TensorProduct.map_tmul]
    | add z₁ z₂ h₁ h₂ => rw [smul_add, map_add, h₁, h₂, map_add, smul_add]
  have hc : ∀ s, toOB l O ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s) =
      (1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s) := fun s => rfl
  induction b using TensorProduct.induction_on with
  | zero => exact ⟨1, cc_one, 0, by simp⟩
  | tmul r t =>
    obtain ⟨s, hs, a, e⟩ := exists_mul_eq_toOB r
    exact ⟨s, hs, a ⊗ₜ t, by rw [TensorProduct.smul_tmul', smul_eq_mul, e]; rfl⟩
  | add b₁ b₂ h₁ h₂ =>
    obtain ⟨s₁, hs₁, β₁, e₁⟩ := h₁
    obtain ⟨s₂, hs₂, β₂, e₂⟩ := h₂
    refine ⟨s₁ * s₂, cc_mul hs₁ hs₂,
      ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₂) • β₁ + ((1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l s₁) • β₂, ?_⟩
    have hm : ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l (s₁ * s₂)) : OB l O) =
        ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₁)) *
          ((1 : O) ⊗ₜ[ℤ_[l]] acrisToBcris l (ainfToAcris l s₂)) := by
      rw [map_mul, map_mul, Algebra.TensorProduct.tmul_mul_tmul, one_mul]
    rw [map_add, hsm, hsm, hc, hc, ← e₁, ← e₂, smul_smul, smul_smul, hm, smul_add, mul_comm (_ ⊗ₜ[ℤ_[l]] _)]

end GlobalTheory.DenomCris
