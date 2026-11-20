import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.TwoMulChainStartIndexAddOneOfOdd

open Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds GlobalTheory.MainTerm Classical

namespace GlobalTheory.MainTerm.Axis

variable {C : Type} [Field C] {ι ι' : Type}

def VanishesOnFirstAxis (F : MvPowerSeries (ι ⊕ ι') C) : Prop :=
  ∀ μ : ι ⊕ ι' →₀ ℕ, (∀ b, μ (Sum.inr b) = 0) → MvPowerSeries.coeff μ F = 0

/- English proof (translation)
Introduce `μ hμ`. Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => ?_` and prove the remaining obligations. Establish `hp'` using `Finset.HasAntidiagonal.mem_antidiagonal.1 hp`. Rewrite using `[h p.2, mul_zero]`.

Introduce `b`. Establish `h1` using `hμ b`. Rewrite `h1` using `[← hp', Finsupp.add_apply]`. Use linear arithmetic over natural numbers and integers.
-/
theorem VanishesOnFirstAxis.mul_left {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (G : MvPowerSeries (ι ⊕ ι') C) : VanishesOnFirstAxis (G * F) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_mul]
  refine Finset.sum_eq_zero fun p hp => ?_
  have hp' := Finset.HasAntidiagonal.mem_antidiagonal.1 hp
  rw [h p.2, mul_zero]
  intro b
  have h1 := hμ b
  rw [← hp', Finsupp.add_apply] at h1
  omega

/- English proof (translation)
Introduce `μ hμ`. Rewrite using `[map_smul, h μ hμ, smul_zero]`.
-/
theorem VanishesOnFirstAxis.smul {F : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (c : C) : VanishesOnFirstAxis (c • F) := by
  intro μ hμ
  rw [map_smul, h μ hμ, smul_zero]

/- English proof (translation)
Introduce `μ hμ`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_eq_zero fun x _ => h x μ hμ`.
-/
theorem VanishesOnFirstAxis.sum {α : Type} (s : Finset α) {F : α → MvPowerSeries (ι ⊕ ι') C}
    (h : ∀ x, VanishesOnFirstAxis (F x)) : VanishesOnFirstAxis (∑ x ∈ s, F x) := by
  intro μ hμ
  rw [map_sum]
  exact Finset.sum_eq_zero fun x _ => h x μ hμ

/- English proof (translation)
Introduce `μ hμ`. Rewrite using `[MvPowerSeries.coeff_X, if_neg]`. Introduce `h`. Establish `h1` using `hμ b`. Rewrite `h1` using `[h]`.

Simplify using `at h1`.
-/
theorem vanishes_X_inr (b : ι') :
    VanishesOnFirstAxis (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C) := by
  intro μ hμ
  rw [MvPowerSeries.coeff_X, if_neg]
  intro h
  have h1 := hμ b
  rw [h] at h1
  simp at h1

/- English proof (translation)
Take `⟨K, rfl⟩` from `hd`. Rewrite using `[mul_comm]`. Conclude with `h.mul_left K`.
-/
theorem VanishesOnFirstAxis.of_dvd {F G : MvPowerSeries (ι ⊕ ι') C} (h : VanishesOnFirstAxis F)
    (hd : F ∣ G) : VanishesOnFirstAxis G := by
  obtain ⟨K, rfl⟩ := hd
  rw [mul_comm]
  exact h.mul_left K

/- English proof (translation)
The claim follows from `(VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ => ((vanishes_X_inr b).mul_left _).smul _).smul _`.
-/
theorem vanishes_mainM [Fintype ι] [Fintype ι'] (V : VF C) (i : ℕ) (Φ : ι' → ι → C) :
    VanishesOnFirstAxis (mainM V i Φ) :=
  (VanishesOnFirstAxis.sum _ fun b => VanishesOnFirstAxis.sum _ fun _ =>
    ((vanishes_X_inr b).mul_left _).smul _).smul _

/- English proof (translation)
Introduce `μ hμ`. Unfold `RowData.hM hPullW`. Rewrite using `[MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by`. Introduce `w`. Simplify using `[map_sum]))]`.

Use `finsum_eq_zero_of_forall_eq_zero fun ν => ?_` and prove the remaining obligations. Distinguish the cases in `hν : ∀ w ∈ ν.support, w.1 = g`. Rewrite using `[X.hL_axes g _ _ ν (Or.inl hν), zero_smul]`. Use `push Not at hν`. Take `⟨w, hw, hg⟩` from `hν`.

Establish `h1 : VanishesOnFirstAxis ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) + ∑ b : ι', toW (1 - g) (v' b) w • (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C))`. Establish `h0 : ∀ c, toW g (e c) w = 0` using `fun c => by simp [toW, hg]`. Simplify using `only [h0, zero_smul, Finset.sum_const_zero, zero_add]`. Conclude with `VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _`. Rewrite using `[h1.of_dvd _ μ hμ, smul_zero]`.

Unfold `Finsupp.prod`. Conclude with `(dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)`.
-/
theorem vanishes_hM {V : VF C} {d : ℕ} [NeZero d] {I J : Fin 2 → Type} [∀ g, Fintype (I g)]
    [∀ g, Fintype (J g)] (X : RowData C V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    [Fintype ι] [Fintype ι'] (e : ι → I g → C) (v' : ι' → I (1 - g) → C) :
    VanishesOnFirstAxis (X.hM g a i e v') := by
  intro μ hμ
  unfold RowData.hM hPullW
  rw [MvPowerSeries.coeff_subst (MvPowerSeries.hasSubst_of_constantCoeff_zero (by
    intro w
    simp [map_sum]))]
  refine finsum_eq_zero_of_forall_eq_zero fun ν => ?_
  by_cases hν : ∀ w ∈ ν.support, w.1 = g
  · rw [X.hL_axes g _ _ ν (Or.inl hν), zero_smul]
  · push Not at hν
    obtain ⟨w, hw, hg⟩ := hν
    have h1 : VanishesOnFirstAxis
        ((∑ c : ι, toW g (e c) w • (MvPowerSeries.X (Sum.inl c) : MvPowerSeries (ι ⊕ ι') C)) +
          ∑ b : ι', toW (1 - g) (v' b) w •
            (MvPowerSeries.X (Sum.inr b) : MvPowerSeries (ι ⊕ ι') C)) := by
      have h0 : ∀ c, toW g (e c) w = 0 := fun c => by simp [toW, hg]
      simp only [h0, zero_smul, Finset.sum_const_zero, zero_add]
      exact VanishesOnFirstAxis.sum _ fun b => (vanishes_X_inr b).smul _
    rw [h1.of_dvd _ μ hμ, smul_zero]
    unfold Finsupp.prod
    exact (dvd_pow_self _ (Finsupp.mem_support_iff.1 hw)).trans (Finset.dvd_prod_of_mem _ hw)

/- English proof (translation)
Introduce `C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ`. Rewrite using `[map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]`.
-/
theorem coeff_hM_sub_mainM_eq_zero : ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d]
    (I J : Fin 2 → Type) [∀ g, Fintype (I g)] [∀ g, Fintype (J g)] (X : RowData C V d I J)
    (g : Fin 2) (a : ZMod d) (i : ℕ) (ι ι' : Type) [Fintype ι] [Fintype ι'] (e : ι → I g → C)
    (v' : ι' → I (1 - g) → C) (Φ : ι' → ι → C) (μ : ι ⊕ ι' →₀ ℕ), (∀ b, μ (Sum.inr b) = 0) →
    MvPowerSeries.coeff μ (X.hM g a i e v' - mainM V i Φ) = 0 := by
  intro C _ V d _ I J _ _ X g a i ι ι' _ _ e v' Φ μ hμ
  rw [map_sub, vanishes_hM X g a i e v' μ hμ, vanishes_mainM V i Φ μ hμ, sub_zero]

end GlobalTheory.MainTerm.Axis
