import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NotCompactOfMEqOne
import Development.AbelianVarietyTheory.Definitions.Divisors.InfUniv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GroupObjectLiftDividedPowers
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TensorModOfTmul
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.UPel.Sm GlobalTheory.Cris GlobalTheory.DeRham
open scoped TensorProduct
open IsLocalRing
universe u

namespace GlobalTheory

/- English proof (translation)
Use `set v : ℕ := (PadicInt.toZModPow k z).val with hv`. Establish `hmem : z - (v : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p` using `p) k) := by`. Rewrite using `[RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]`. Rewrite `hmem` using `[PadicInt.ker_toZModPow, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `hmem`.

Establish `hz : z = (v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y` using `by rw [← hy]; ring`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem padicInt_ringHom_eq_val {p : ℕ} [Fact p.Prime] {B : Type*} [Ring B] (k : ℕ) (hB : (p : B) ^ k = 0)
    (f : ℤ_[p] →+* B) (z : ℤ_[p]) : f z = (((PadicInt.toZModPow k z).val : ℕ) : B) := by
  set v : ℕ := (PadicInt.toZModPow k z).val with hv
  have hmem : z - (v : ℤ_[p]) ∈ RingHom.ker (PadicInt.toZModPow (p := p) k) := by
    rw [RingHom.mem_ker, map_sub, map_natCast, hv, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZModPow, Ideal.mem_span_singleton] at hmem
  obtain ⟨y, hy⟩ := hmem
  have hz : z = (v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y := by rw [← hy]; ring
  calc f z = f ((v : ℤ_[p]) + (p : ℤ_[p]) ^ k * y) := by rw [← hz]
    _ = (v : B) := by rw [map_add, map_mul, map_pow, map_natCast, map_natCast, hB, zero_mul, add_zero]

/- English proof (translation)
Introduce `p _ D C _ k hk H _ _ ρ s`. Establish `hdvd : ringChar C ∣ p ^ k` using `ringChar.dvd (by rw [Nat.cast_pow]; exact hk)`. Set `ιp : ℤ_[p] →+* C` to `(ZMod.castHom hdvd C).comp (PadicInt.toZModPow k)`. Set `g : ℤ_[p] →+* Module.End C H` to `(algebraMap C (Module.End C H)).comp ιp`. Set `Φ : D.O ⊗[ℤ] ℤ_[p] →ₐ[ℤ] Module.End C H` to `Algebra.TensorProduct.lift ρ.toIntAlgHom g.toIntAlgHom (fun c z => by show Commute (ρ c) (algebraMap C (Module.End C H) (ιp z))`.

Conclude with `Algebra.commute_algebraMap_right _ _)`. Establish `hΦ : ∀ c z, Φ (c ⊗ₜ z) = ρ c * algebraMap C (Module.End C H) (ιp z)`. Introduce `c z`. Simplify using `[Φ, g]`. Establish `hind : ∀ P : Module.End C H → Prop, P 0 → (∀ a b, P a → P b → P (a + b)) → (∀ c r, P (ρ c * algebraMap C (Module.End C H) r)) → ∀ t, P (Φ t)`.

Introduce `P h0 hadd hgen t`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simpa using h0`. Consider the case `tmul c z => rw [hΦ]`. Conclude with `hgen c (ιp z)`.

Consider the case `add a b ha hb => rw [map_add]`. Conclude with `hadd _ _ ha hb`. Set `Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H` to `(Φ : D.O ⊗[ℤ] ℤ_[p] →+* Module.End C H).comp (s.symm : _ →+* _)`. Establish `hΨ : ∀ M, Ψ M = Φ (s.symm M)` using `fun M => rfl`. Use `⟨Ψ, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `c`. Rewrite using `[hΨ, AlgEquiv.symm_apply_apply, hΦ, map_one, map_one, _root_.mul_one]`. Introduce `T hT M`. Rewrite using `[hΨ]`. Use `hind (fun A => A * T = T * A) (by simp) (fun a b ha hb => by rw [_root_.add_mul, _root_.mul_add, ha, hb]) (fun c r => ?_) _` and prove the remaining obligations.

Rewrite using `[_root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, hT, _root_.mul_assoc]`. Introduce `N hN M x hx`. Rewrite using `[hΨ]`. Use `hind (fun A => ∀ x ∈ N, A x ∈ N) (by simp) (fun a b ha hb x hx => ?_) (fun c r x hx => ?_) _ x hx` and prove the remaining obligations. Rewrite using `[LinearMap.add_apply]`.

Conclude with `N.add_mem (ha x hx) (hb x hx)`. Rewrite using `[Module.End.mul_apply, Module.algebraMap_end_apply]`. Conclude with `hN c _ (N.smul_mem r hx)`. Introduce `y N hN`. Establish `hpk : (p : Module.End C H) ^ k = 0`.

Rewrite using `[← map_natCast (algebraMap C (Module.End C H)), ← map_pow, hk, map_zero]`. Establish `hright : ∀ z : ℤ_[p], ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) x ∈ N`. Introduce `z x hx`. Set `f : ℤ_[p] →+* Module.End C H` to `(Ψ.comp (Matrix.scalar (Fin D.m))).comp Algebra.TensorProduct.includeRight.toRingHom`. Establish `hf : Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) = f z` using `rfl`.

Rewrite using `[hf, padicInt_ringHom_eq_val k hpk f z, Module.End.natCast_apply]`. Conclude with `N.nsmul_mem hx _`. Establish `hleft : ∀ a : 𝓞 D.F, ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p]))) x ∈ N`. Introduce `a x hx`. Establish `h1 : Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p])) = algebraMap (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) a`.

Rewrite using `[Matrix.algebraMap_eq_diagonal]`. Both sides reduce to the same expression. Establish `h2 : s.symm (algebraMap (𝓞 D.F) _ a) = algebraMap (𝓞 D.F) D.O a ⊗ₜ[ℤ] (1 : ℤ_[p])`. Rewrite using `[AlgEquiv.commutes]`. Both sides reduce to the same expression.

Rewrite using `[h1, hΨ, h2, hΦ, map_one, map_one, _root_.mul_one]`. Conclude with `hN a x hx`. Introduce `x hx`. Proceed by induction on `y using TensorProduct.induction_on generalizing x with`. Consider the case `zero => simpa using N.zero_mem`.

Consider the case `tmul a z`. Establish `: (a ⊗ₜ[ℤ] z : 𝓞 D.F ⊗[ℤ] ℤ_[p]) = (a ⊗ₜ[ℤ] (1 : ℤ_[p])) * ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]`. Rewrite using `[this, map_mul, map_mul, Module.End.mul_apply]`. Conclude with `hleft a _ (hright z x hx)`.

Consider the case `add a b ha hb => rw [map_add, map_add, LinearMap.add_apply]`. Conclude with `N.add_mem (ha x hx) (hb x hx)`.
-/
theorem exists_matrix_action_of_splitting : ∀ (p : ℕ) [Fact p.Prime] (D : GlobalTheory.UPel.HT.Datum p) (C : Type) [CommRing C] (k : ℕ), (p : C) ^ k = 0 →
  ∀ (H : Type u) [AddCommGroup H] [Module C H] (ρ : D.O →+* Module.End C H)
  (s : (D.O ⊗[ℤ] ℤ_[p]) ≃ₐ[𝓞 D.F] Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])),
  ∃ Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H,
    (∀ c, Ψ (s (c ⊗ₜ 1)) = ρ c) ∧
    (∀ T : Module.End C H, (∀ c, ρ c * T = T * ρ c) → ∀ M, Ψ M * T = T * Ψ M) ∧
    (∀ N : Submodule C H, (∀ c, ∀ x ∈ N, ρ c x ∈ N) → ∀ M, ∀ x ∈ N, Ψ M x ∈ N) ∧
    ∀ y (N : Submodule C H), (∀ a, ∀ x ∈ N, ρ (algebraMap (𝓞 D.F) D.O a) x ∈ N) → ∀ x ∈ N, Ψ (Matrix.scalar _ y) x ∈ N := by
  intro p _ D C _ k hk H _ _ ρ s
  have hdvd : ringChar C ∣ p ^ k := ringChar.dvd (by rw [Nat.cast_pow]; exact hk)
  let ιp : ℤ_[p] →+* C := (ZMod.castHom hdvd C).comp (PadicInt.toZModPow k)
  let g : ℤ_[p] →+* Module.End C H := (algebraMap C (Module.End C H)).comp ιp
  let Φ : D.O ⊗[ℤ] ℤ_[p] →ₐ[ℤ] Module.End C H :=
    Algebra.TensorProduct.lift ρ.toIntAlgHom g.toIntAlgHom
      (fun c z => by
        show Commute (ρ c) (algebraMap C (Module.End C H) (ιp z))
        exact Algebra.commute_algebraMap_right _ _)
  have hΦ : ∀ c z, Φ (c ⊗ₜ z) = ρ c * algebraMap C (Module.End C H) (ιp z) := by
    intro c z; simp [Φ, g]

  have hind : ∀ P : Module.End C H → Prop, P 0 → (∀ a b, P a → P b → P (a + b)) →
      (∀ c r, P (ρ c * algebraMap C (Module.End C H) r)) → ∀ t, P (Φ t) := by
    intro P h0 hadd hgen t
    induction t using TensorProduct.induction_on with
    | zero => simpa using h0
    | tmul c z => rw [hΦ]; exact hgen c (ιp z)
    | add a b ha hb => rw [map_add]; exact hadd _ _ ha hb
  let Ψ : Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p]) →+* Module.End C H :=
    (Φ : D.O ⊗[ℤ] ℤ_[p] →+* Module.End C H).comp (s.symm : _ →+* _)
  have hΨ : ∀ M, Ψ M = Φ (s.symm M) := fun M => rfl
  refine ⟨Ψ, ?_, ?_, ?_, ?_⟩
  · intro c
    rw [hΨ, AlgEquiv.symm_apply_apply, hΦ, map_one, map_one, _root_.mul_one]
  · intro T hT M
    rw [hΨ]
    refine hind (fun A => A * T = T * A) (by simp) (fun a b ha hb => by rw [_root_.add_mul, _root_.mul_add, ha, hb])
      (fun c r => ?_) _
    rw [_root_.mul_assoc, Algebra.commutes, ← _root_.mul_assoc, hT, _root_.mul_assoc]
  · intro N hN M x hx
    rw [hΨ]
    refine hind (fun A => ∀ x ∈ N, A x ∈ N) (by simp) (fun a b ha hb x hx => ?_) (fun c r x hx => ?_) _ x hx
    · rw [LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)
    · rw [Module.End.mul_apply, Module.algebraMap_end_apply]
      exact hN c _ (N.smul_mem r hx)
  · intro y N hN
    have hpk : (p : Module.End C H) ^ k = 0 := by
      rw [← map_natCast (algebraMap C (Module.End C H)), ← map_pow, hk, map_zero]
    have hright : ∀ z : ℤ_[p], ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) x ∈ N := by
      intro z x hx
      let f : ℤ_[p] →+* Module.End C H :=
        (Ψ.comp (Matrix.scalar (Fin D.m))).comp Algebra.TensorProduct.includeRight.toRingHom
      have hf : Ψ (Matrix.scalar (Fin D.m) ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z)) = f z := rfl
      rw [hf, padicInt_ringHom_eq_val k hpk f z, Module.End.natCast_apply]
      exact N.nsmul_mem hx _
    have hleft : ∀ a : 𝓞 D.F, ∀ x ∈ N, Ψ (Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p]))) x ∈ N := by
      intro a x hx
      have h1 : Matrix.scalar (Fin D.m) (a ⊗ₜ[ℤ] (1 : ℤ_[p])) =
          algebraMap (𝓞 D.F) (Matrix (Fin D.m) (Fin D.m) (𝓞 D.F ⊗[ℤ] ℤ_[p])) a := by
        rw [Matrix.algebraMap_eq_diagonal]; rfl
      have h2 : s.symm (algebraMap (𝓞 D.F) _ a) = algebraMap (𝓞 D.F) D.O a ⊗ₜ[ℤ] (1 : ℤ_[p]) := by
        rw [AlgEquiv.commutes]; rfl
      rw [h1, hΨ, h2, hΦ, map_one, map_one, _root_.mul_one]
      exact hN a x hx
    intro x hx
    induction y using TensorProduct.induction_on generalizing x with
    | zero => simpa using N.zero_mem
    | tmul a z =>
      have : (a ⊗ₜ[ℤ] z : 𝓞 D.F ⊗[ℤ] ℤ_[p]) = (a ⊗ₜ[ℤ] (1 : ℤ_[p])) * ((1 : 𝓞 D.F) ⊗ₜ[ℤ] z) := by
        rw [Algebra.TensorProduct.tmul_mul_tmul, _root_.mul_one, _root_.one_mul]
      rw [this, map_mul, map_mul, Module.End.mul_apply]
      exact hleft a _ (hright z x hx)
    | add a b ha hb => rw [map_add, map_add, LinearMap.add_apply]; exact N.add_mem (ha x hx) (hb x hx)

end GlobalTheory
