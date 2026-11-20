import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.RelevantZeroGramTerms
import Formalism.LocalToGlobal.HermitianForms.IsLocBasis
import Formalism.LocalToGlobal.Columns.PolyFnLemmas
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf

open Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.Forms Formalism.UG Matrix NumberField IsDedekindDomain
open scoped InnerProductSpace TensorProduct

namespace GlobalTheory.ValueSpaceCoordinates

/- English proof (translation)
Establish `hanti : Antitone lam.natW`. Introduce `i j hij`. Establish `h` using `lam.anti hij`. Simplify using `only [DomWeight.natW]`. Conclude with `Int.toNat_le_toNat (by omega)`.

Establish `hw` using `Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti`. Express the relevant statement in the definitionally equal form `p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp`. Express the relevant statement in the definitionally equal form `Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW`. Rewrite `hp`, the goal using `[← hw]`. Conclude with `Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp`.
-/
theorem rowAct_mem_delSq {n : ℕ} (lam : DomWeight n) (g : Matrix (Fin n) (Fin n) ℂ)
    (p : MvPolynomial (Fin n × Fin n) ℂ) (hp : p ∈ delSq ℂ n lam) :
    Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ delSq ℂ n lam := by
  have hanti : Antitone lam.natW := by
    intro i j hij
    have h := lam.anti hij
    simp only [DomWeight.natW]
    exact Int.toNat_le_toNat (by omega)
  have hw := Formalism.L2.Col.dualWeyl_eq_weyl ℂ (le_rfl : n ≤ n) lam.natW hanti
  change p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW at hp
  change Formalism.GradedWeylDivisibility.rowAct ℂ g p ∈ Formalism.GradedWeylDivisibility.weyl ℂ n n le_rfl lam.natW
  rw [← hw] at hp ⊢
  exact Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ n n lam.natW g p hp

/- English proof (translation)
Establish `key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `n) g).toRingHom = MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `c`. Simplify using `[Formalism.GradedWeylDivisibility.rowAct]`. Introduce `v`.

Simplify using `[Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]`. Simplify using `using RingHom.congr_fun key p`.
-/
theorem eval_rowAct {n : ℕ} (g x : Matrix (Fin n) (Fin n) ℂ) (p : MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : Fin n × Fin n => x v.1 v.2) (Formalism.GradedWeylDivisibility.rowAct ℂ g p) =
      MvPolynomial.eval (fun v : Fin n × Fin n => (g * x) v.1 v.2) p := by
  have key : (MvPolynomial.eval fun v : Fin n × Fin n => x v.1 v.2).comp
      (Formalism.GradedWeylDivisibility.rowAct ℂ (n := n) g).toRingHom =
      MvPolynomial.eval fun v : Fin n × Fin n => (g * x) v.1 v.2 := by
    apply MvPolynomial.ringHom_ext
    · intro c
      simp [Formalism.GradedWeylDivisibility.rowAct]
    · intro v
      simp [Formalism.GradedWeylDivisibility.rowAct, Matrix.mul_apply]
  simpa using RingHom.congr_fun key p

/- English proof (translation)
Unfold `Formalism.L2.Forms.ten`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.eval_rename]`. Both sides reduce to the same expression.
-/
theorem eval_ten {ι : Type} [Fintype ι] {n : ℕ} (x : ι → Matrix (Fin n) (Fin n) ℂ)
    (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    MvPolynomial.eval (fun v : ι × Fin n × Fin n => x v.1 v.2.1 v.2.2) (ten f) =
      ∏ τ, MvPolynomial.eval (fun v : Fin n × Fin n => x τ v.1 v.2) (f τ) := by
  unfold Formalism.L2.Forms.ten
  rw [map_prod]
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [MvPolynomial.eval_rename]
  rfl

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[eval_ten (fun τ => (A * B) τ * y.1 τ) f, eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]`. Simplify using `only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow, Finset.prod_mul_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fnOf_mul_ten {ι : Type} [Fintype ι] {n : ℕ} (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ)
    (A B : ι → Matrix (Fin n) (Fin n) ℂ) (f : ι → MvPolynomial (Fin n × Fin n) ℂ) :
    fnOf G s (A * B) (ten f) =
      (∏ τ, (A τ).det ^ s τ) • fnOf G s B (ten fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ)) := by
  ext y
  simp only [fnOf, LinearMap.coe_mk, AddHom.coe_mk, Pi.smul_apply, smul_eq_mul]
  rw [eval_ten (fun τ => (A * B) τ * y.1 τ) f,
    eval_ten (fun τ => B τ * y.1 τ) (fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ))]
  simp only [eval_rowAct, Pi.mul_apply, Matrix.mul_assoc, Matrix.det_mul, mul_zpow,
    Finset.prod_mul_distrib]
  ring

/- English proof (translation)
Unfold `CSpan`. Rewrite using `[Submodule.map_span, Submodule.span_le]`. Introduce and unpack `_ ⟨q, ⟨f, hf, rfl⟩, rfl⟩`. Rewrite using `[SetLike.mem_coe, fnOf_mul_ten]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))`.
-/
theorem map_fnOf_mul_le {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)
    (G : ι → Matrix (Fin n) (Fin n) ℂ) (s : ι → ℤ) (A B : ι → Matrix (Fin n) (Fin n) ℂ) :
    (CSpan lam).map (fnOf G s (A * B)) ≤ (CSpan lam).map (fnOf G s B) := by
  unfold CSpan
  rw [Submodule.map_span, Submodule.span_le]
  rintro _ ⟨q, ⟨f, hf, rfl⟩, rfl⟩
  rw [SetLike.mem_coe, fnOf_mul_ten]
  exact Submodule.smul_mem _ _ (Submodule.mem_map_of_mem (Submodule.subset_span
    ⟨fun τ => Formalism.GradedWeylDivisibility.rowAct ℂ (A τ) (f τ), fun τ => rowAct_mem_delSq (lam τ) (A τ) (f τ) (hf τ), rfl⟩))

/- English proof (translation)
Introduce `ι _ n lam G M hM`. Establish `hinv : (fun τ => (M τ)⁻¹) * M = 1`. Use function extensionality and compare the values at `τ`. Simplify using `only [Pi.mul_apply, Pi.one_apply]`. Conclude with `Matrix.nonsing_inv_mul (M τ) (hM τ)`.

Unfold `ValC`. Apply `le_antisymm` to reduce the goal to its premises. Establish `h` using `map_fnOf_mul_le lam G (shiftOf lam) M 1`. Rewrite `h` using `[mul_one]`. Then use the resulting hypothesis. Establish `h` using `map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M`.

Rewrite `h` using `[hinv]`. Then use the resulting hypothesis.
-/
theorem map_fnOf_eq_ValC :
    ∀ (ι : Type) [Fintype ι] (n : ℕ) (lam : ι → DomWeight n) (G M : ι → Matrix (Fin n) (Fin n) ℂ), (∀ τ, IsUnit (M τ).det) → (CSpan lam).map (fnOf G (shiftOf lam) M) = ValC G lam := by
  intro ι _ n lam G M hM
  have hinv : (fun τ => (M τ)⁻¹) * M = 1 := by
    funext τ
    simp only [Pi.mul_apply, Pi.one_apply]
    exact Matrix.nonsing_inv_mul (M τ) (hM τ)
  unfold ValC
  apply le_antisymm
  · have h := map_fnOf_mul_le lam G (shiftOf lam) M 1
    rwa [mul_one] at h
  · have h := map_fnOf_mul_le lam G (shiftOf lam) (fun τ => (M τ)⁻¹) M
    rwa [hinv] at h

end GlobalTheory.ValueSpaceCoordinates
