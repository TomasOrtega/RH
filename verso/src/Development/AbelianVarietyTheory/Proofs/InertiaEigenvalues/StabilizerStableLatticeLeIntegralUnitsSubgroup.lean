import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ComapInlMemStLat

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

variable {O E A : Type} [CommRing O] [Field E] [CommRing A] [Algebra O A] [Algebra E A]

/- English proof (translation)
Use `haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1`. Set `f : Module.End O L` to `(LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)`. Take `⟨p, hp, hpf⟩` from `LinearMap.exists_monic_and_aeval_eq_zero O f`. Establish `hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro y`. Simplify using the standard rewrite rules. Consider the case `succ n ih`. Introduce `y`.

Rewrite using `[pow_succ', Module.End.mul_apply]`. Express the relevant statement in the definitionally equal form `t * (((f ^ n) y : L) : A) = _`. Rewrite using `[ih, pow_succ', mul_assoc]`. Establish `hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y`. Introduce `y`.

Rewrite using `[aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]`. Use `Finset.sum_congr rfl fun n _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]`. Establish `hkill : ∀ y ∈ L, aeval t p * y = 0`. Introduce `y hy`.

Use `hev ⟨y, hy⟩` as an intermediate fact. Rewrite `this` using `[hpf]`. Simplify using `using this.symm`. Establish `hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0`. Introduce `z hz`.

Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy => exact hkill y hy`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]`. Consider the case `smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]`.

Establish `h1 : aeval t p = 0`. Use `hall 1 (by rw [hL.2]; trivial)` as an intermediate fact. Simplify using `using this`. Conclude with `⟨p, hp, by rw [← aeval_def]; exact h1⟩`.
-/
theorem isIntegral_of_mul_mem_lat {L : Submodule O A} (hL : IsLat O E L) (t : A)
    (ht : ∀ y ∈ L, t * y ∈ L) : IsIntegral O t := by
  haveI : Module.Finite O L := Module.Finite.iff_fg.mpr hL.1
  let f : Module.End O L := (LinearMap.mulLeft O t).restrict (fun y hy => ht y hy)
  obtain ⟨p, hp, hpf⟩ := LinearMap.exists_monic_and_aeval_eq_zero O f
  have hpow : ∀ (n : ℕ) (y : L), (((f ^ n) y : L) : A) = t ^ n * y := by
    intro n
    induction n with
    | zero => intro y; simp
    | succ n ih =>
      intro y
      rw [pow_succ', Module.End.mul_apply]
      change t * (((f ^ n) y : L) : A) = _
      rw [ih, pow_succ', mul_assoc]
  have hev : ∀ y : L, ((aeval f p y : L) : A) = aeval t p * y := by
    intro y
    rw [aeval_eq_sum_range, aeval_eq_sum_range, Finset.sum_mul, LinearMap.sum_apply, Submodule.coe_sum]
    refine Finset.sum_congr rfl fun n _ => ?_
    rw [LinearMap.smul_apply, Submodule.coe_smul, hpow, smul_mul_assoc]
  have hkill : ∀ y ∈ L, aeval t p * y = 0 := by
    intro y hy
    have := hev ⟨y, hy⟩
    rw [hpf] at this
    simpa using this.symm
  have hall : ∀ z ∈ Submodule.span E (L : Set A), aeval t p * z = 0 := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem y hy => exact hkill y hy
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, hx, hy, add_zero]
    | smul e x _ hx => rw [mul_smul_comm, hx, smul_zero]
  have h1 : aeval t p = 0 := by
    have := hall 1 (by rw [hL.2]; trivial)
    simpa using this
  exact ⟨p, hp, by rw [← aeval_def]; exact h1⟩

/- English proof (translation)
Introduce `t ht`. Establish `key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A)`. Introduce `s hs y hy`. Establish `he : mulLat O (s : A) (L : Submodule O A) = L`. Rewrite using `[← stLat_smul_val, hs]`.

Rewrite using `[← he]`. Conclude with `⟨y, hy, rfl⟩`. Establish `ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L` using `inv_mem ht`. Conclude with `⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht), isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩`.
-/
theorem stabilizer_le_intUnits (O E A : Type) [CommRing O] [Field E] [CommRing A] [Algebra O A]
    [Algebra E A] (g : A) (L : stLat O E g) : MulAction.stabilizer Aˣ L ≤ intUnits O A := by
  intro t ht
  have key : ∀ s : Aˣ, s • L = L → ∀ y ∈ (L : Submodule O A), (s : A) * y ∈ (L : Submodule O A) := by
    intro s hs y hy
    have he : mulLat O (s : A) (L : Submodule O A) = L := by
      rw [← stLat_smul_val, hs]
    rw [← he]
    exact ⟨y, hy, rfl⟩
  have ht' : t⁻¹ ∈ MulAction.stabilizer Aˣ L := inv_mem ht
  exact ⟨isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t ht),
    isIntegral_of_mul_mem_lat (E := E) L.2.1 _ (key t⁻¹ ht')⟩

end GlobalTheory.UnitLemma
