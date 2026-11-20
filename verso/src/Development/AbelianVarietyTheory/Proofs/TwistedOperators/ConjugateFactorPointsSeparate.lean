import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CentralizerTensorForms
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.NotCompactOfIdempotent

noncomputable section

open GlobalTheory.RegSS GlobalTheory.IndefiniteRowSideFullHecke.CentralizerTensorForms
open scoped TensorProduct

namespace GlobalTheory.RegSS

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite F (A ⧸ m) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap (Ideal.Quotient.mkₐ_surjective F m)`. Conclude with `⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩`.
-/
theorem nonempty_algHom_algebraicClosure (F A : Type) [Field F] [CommRing A] [Algebra F A]
    [Module.Finite F A] [Nontrivial A] : Nonempty (A →ₐ[F] AlgebraicClosure F) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ F m).toLinearMap (Ideal.Quotient.mkₐ_surjective F m)
  exact ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] AlgebraicClosure F).comp (Ideal.Quotient.mkₐ F m)⟩

/- English proof (translation)
Proceed by induction on `x with`. Consider the case `zero => exact ⟨0, 0, by simp⟩`. Consider the case `tmul p y`. Take `⟨e, rfl⟩` from `(TensorProduct.rid F E).symm.surjective y`. Use `⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩` and prove the remaining obligations.

Establish `hs` using `b.sum_repr e`. Rewrite `hs` using `[Fin.sum_univ_two]`. Rewrite using `[TensorProduct.rid_symm_apply, TensorProduct.smul_tmul, TensorProduct.smul_tmul, ← TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul', ← TensorProduct.add_tmul, hs]`. Consider the case `add x y hx hy`. Take `⟨p, q, rfl⟩` from `hx`.

Take `⟨p', q', rfl⟩` from `hy`. Conclude with `⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩`.
-/
theorem exists_eq_tmul_add_tmul {F E P : Type} [Field F] [CommRing E] [Algebra F E] [CommRing P]
    [Algebra F P] (b : Module.Basis (Fin 2) F E) (x : P ⊗[F] (E ⊗[F] F)) :
    ∃ p q : P, x = p ⊗ₜ (b 0 ⊗ₜ (1 : F)) + q ⊗ₜ (b 1 ⊗ₜ (1 : F)) := by
  induction x with
  | zero => exact ⟨0, 0, by simp⟩
  | tmul p y =>
    obtain ⟨e, rfl⟩ := (TensorProduct.rid F E).symm.surjective y
    refine ⟨b.repr e 0 • p, b.repr e 1 • p, ?_⟩
    have hs := b.sum_repr e
    rw [Fin.sum_univ_two] at hs
    rw [TensorProduct.rid_symm_apply, TensorProduct.smul_tmul, TensorProduct.smul_tmul,
      ← TensorProduct.tmul_add, TensorProduct.smul_tmul', TensorProduct.smul_tmul',
      ← TensorProduct.add_tmul, hs]
  | add x y hx hy =>
    obtain ⟨p, q, rfl⟩ := hx
    obtain ⟨p', q', rfl⟩ := hy
    exact ⟨p + p', q + q', by simp only [TensorProduct.add_tmul]; abel⟩

/- English proof (translation)
Introduce `F E _ _ _ _ σ hσ P _ _ _ k K _ _ ⟨e⟩`. Use `haveI := quad_finite hσ`. Use `haveI := quad_nontrivial hσ`. Take `⟨b, d, hb0, hb1, hd, hbb⟩` from `quad_exists_basis hσ`. Set `pr : ∀ i, P →ₐ[F] K i` to `fun i => (Pi.evalAlgHom F K i).comp e.toAlgHom`.

Establish `hpr : ∀ i p, pr i p = e p i` using `fun _ _ => rfl`. Use `haveI : ∀ i, Module.Finite F (K i) := fun i => Module.Finite.of_surjective (pr i).toLinearMap fun y => by`. Take `⟨p, hp⟩` from `e.surjective (Pi.single i y)`. Conclude with `⟨p, by simp [hpr, hp]⟩`. Set `χ : ∀ i, K i ⊗[F] E →ₐ[F] AlgebraicClosure F` to `fun i => (nonempty_algHom_algebraicClosure F (K i ⊗[F] E)).some`.

Set `π : ∀ i, P ⊗[F] (E ⊗[F] F) →ₐ[F] K i ⊗[F] E` to `fun i => Algebra.TensorProduct.map (pr i) (Algebra.TensorProduct.rid F F E).toAlgHom`. Establish `hπ : ∀ i p (y : E), π i (p ⊗ₜ (y ⊗ₜ (1 : F))) = e p i ⊗ₜ y` using `fun i p y => by`. Simplify using `[π, hpr]`. Establish `hc : ∀ (p : P) (y : E), tConj3 P σ F (p ⊗ₜ (y ⊗ₜ (1 : F))) = p ⊗ₜ (σ y ⊗ₜ (1 : F))` using `fun p y => by simp [tConj3]`. Use `⟨fun i => (χ i).comp (π i), fun x hx => ?_, fun i hi x hx => ?_⟩` and prove the remaining obligations.

Take `⟨p, q, rfl⟩` from `exists_eq_tmul_add_tmul b x`. Establish `key : ∀ i, e p i = 0 ∧ e q i = 0` using `fun i => by`. Take `⟨h1, h2⟩` from `hx i`. Establish `hm : (e q i ⊗ₜ[F] b 1 : K i ⊗[F] E) = (e q i ⊗ₜ[F] 1) * (1 ⊗ₜ[F] b 1)` using `by simp`. Simplify using `only [AlgHom.comp_apply, map_add, hc, hπ, hb0, hb1, map_one, TensorProduct.tmul_neg, map_neg] at h1 h2`.

Rewrite `h1`, `h2` using `[hm, map_mul]`. Establish `hδ : χ i (1 ⊗ₜ[F] b 1) ≠ 0` using `fun h0 => by`. Establish `: χ i (1 ⊗ₜ[F] b 1) * χ i (1 ⊗ₜ[F] b 1) = algebraMap F _ d`. Rewrite using `[← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hbb, mul_one, ← Algebra.TensorProduct.algebraMap_apply', AlgHom.commutes]`. Rewrite `this` using `[h0, zero_mul]`.

Conclude with `hd ((map_eq_zero _).1 this.symm)`. Establish `inj : ∀ y : K i, χ i (y ⊗ₜ[F] 1) = 0 → y = 0` using `fun y hy => (map_eq_zero ((χ i).comp Algebra.TensorProduct.includeLeft : K i →ₐ[F] _)).1 hy`. Use `⟨inj _ (by linear_combination (h1 + h2) / 2), inj _ ?_⟩` and prove the remaining obligations. Conclude with `(mul_eq_zero.1 (by linear_combination (h1 - h2) / 2)).resolve_right hδ`. Establish `hp : p = 0` using `e.injective (by rw [map_zero]; exact funext fun i => (key i).1)`.

Establish `hq : q = 0` using `e.injective (by rw [map_zero]; exact funext fun i => (key i).2)`. Simplify using `[hp, hq]`. Establish `h0 : π i x = 0`. Assume the negation of the conclusion as `h0`. Take `⟨y, hy⟩` from `hi.mul_inv_cancel h0`.

Use `congrArg (χ i) hy` as an intermediate fact. Rewrite `this` using `[map_mul, show χ i (π i x) = 0 from hx, zero_mul, map_one]`. Conclude with `zero_ne_one this`. Establish `h1 : π i (tConj3 P σ F x) = tConj (K i) σ (π i x)`. Take `⟨p, q, rfl⟩` from `exists_eq_tmul_add_tmul b x`.

Simplify using `only [map_add, hc, hπ, tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]`. Rewrite using `[AlgHom.comp_apply, h1, h0, map_zero, map_zero]`.
-/
theorem separatingPoints : SeparatingPoints := by
  intro F E _ _ _ _ σ hσ P _ _ _ k K _ _ ⟨e⟩
  haveI := quad_finite hσ
  haveI := quad_nontrivial hσ
  obtain ⟨b, d, hb0, hb1, hd, hbb⟩ := quad_exists_basis hσ
  let pr : ∀ i, P →ₐ[F] K i := fun i => (Pi.evalAlgHom F K i).comp e.toAlgHom
  have hpr : ∀ i p, pr i p = e p i := fun _ _ => rfl
  haveI : ∀ i, Module.Finite F (K i) := fun i =>
    Module.Finite.of_surjective (pr i).toLinearMap fun y => by
      obtain ⟨p, hp⟩ := e.surjective (Pi.single i y)
      exact ⟨p, by simp [hpr, hp]⟩
  let χ : ∀ i, K i ⊗[F] E →ₐ[F] AlgebraicClosure F := fun i =>
    (nonempty_algHom_algebraicClosure F (K i ⊗[F] E)).some
  let π : ∀ i, P ⊗[F] (E ⊗[F] F) →ₐ[F] K i ⊗[F] E := fun i =>
    Algebra.TensorProduct.map (pr i) (Algebra.TensorProduct.rid F F E).toAlgHom
  have hπ : ∀ i p (y : E), π i (p ⊗ₜ (y ⊗ₜ (1 : F))) = e p i ⊗ₜ y := fun i p y => by
    simp [π, hpr]
  have hc : ∀ (p : P) (y : E), tConj3 P σ F (p ⊗ₜ (y ⊗ₜ (1 : F))) = p ⊗ₜ (σ y ⊗ₜ (1 : F)) :=
    fun p y => by simp [tConj3]
  refine ⟨fun i => (χ i).comp (π i), fun x hx => ?_, fun i hi x hx => ?_⟩
  · obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
    have key : ∀ i, e p i = 0 ∧ e q i = 0 := fun i => by
      obtain ⟨h1, h2⟩ := hx i
      have hm : (e q i ⊗ₜ[F] b 1 : K i ⊗[F] E) = (e q i ⊗ₜ[F] 1) * (1 ⊗ₜ[F] b 1) := by simp
      simp only [AlgHom.comp_apply, map_add, hc, hπ, hb0, hb1, map_one, TensorProduct.tmul_neg,
        map_neg] at h1 h2
      rw [hm, map_mul] at h1 h2
      have hδ : χ i (1 ⊗ₜ[F] b 1) ≠ 0 := fun h0 => by
        have : χ i (1 ⊗ₜ[F] b 1) * χ i (1 ⊗ₜ[F] b 1) = algebraMap F _ d := by
          rw [← map_mul, Algebra.TensorProduct.tmul_mul_tmul, hbb, mul_one,
            ← Algebra.TensorProduct.algebraMap_apply', AlgHom.commutes]
        rw [h0, zero_mul] at this
        exact hd ((map_eq_zero _).1 this.symm)
      have inj : ∀ y : K i, χ i (y ⊗ₜ[F] 1) = 0 → y = 0 := fun y hy =>
        (map_eq_zero ((χ i).comp Algebra.TensorProduct.includeLeft : K i →ₐ[F] _)).1 hy
      refine ⟨inj _ (by linear_combination (h1 + h2) / 2), inj _ ?_⟩
      exact (mul_eq_zero.1 (by linear_combination (h1 - h2) / 2)).resolve_right hδ
    have hp : p = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).1)
    have hq : q = 0 := e.injective (by rw [map_zero]; exact funext fun i => (key i).2)
    simp [hp, hq]
  · have h0 : π i x = 0 := by
      by_contra h0
      obtain ⟨y, hy⟩ := hi.mul_inv_cancel h0
      have := congrArg (χ i) hy
      rw [map_mul, show χ i (π i x) = 0 from hx, zero_mul, map_one] at this
      exact zero_ne_one this
    have h1 : π i (tConj3 P σ F x) = tConj (K i) σ (π i x) := by
      obtain ⟨p, q, rfl⟩ := exists_eq_tmul_add_tmul b x
      simp only [map_add, hc, hπ, tConj, Algebra.TensorProduct.map_tmul, AlgHom.id_apply]
    rw [AlgHom.comp_apply, h1, h0, map_zero, map_zero]

end GlobalTheory.RegSS
