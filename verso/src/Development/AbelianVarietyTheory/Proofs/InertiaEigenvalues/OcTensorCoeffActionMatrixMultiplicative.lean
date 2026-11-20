import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Development.AbelianVarietyTheory.Definitions.Foundations.HTBasis
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.ExpStar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoeAlgebraMapOC

noncomputable section

namespace GlobalTheory.Cyc.Decomp

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.MainNotions.LocalSituation GlobalTheory.Cyc TensorProduct

/- English proof (translation)
Establish `hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t)`. Introduce `a x t`. Rewrite using `[hs, hs, smul_smul, smul_smul, mul_comm]`. Use `⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`.

Simplify using `only [hA, Matrix.add_apply, add_smul, map_add, Finsupp.add_apply]`. Use extensionality with `i j`. Establish `hx : (x • a) • b j = x • (a • b j)`. Rewrite using `[Algebra.smul_def, mul_smul, ← hs]`. Simplify using `only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]`.

Use extensionality with `i j`. Rewrite using `[hA, one_smul, Module.Basis.repr_self]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Simplify using `[Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]`. Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, hA, mul_smul]`. Use `conv_lhs => rw [← b.sum_repr (a' • b j)]`. Rewrite using `[Finset.smul_sum]`.

Simplify using `only [hc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_mul, hA]`. Conclude with `Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem actMat_props {Z O N C : Type} [CommRing Z] [CommRing O] [Algebra Z O] [AddCommGroup N]
    [Module O N] [Module Z N] (hs : ∀ (x : Z) (t : N), x • t = algebraMap Z O x • t)
    [CommRing C] (φ : Z →+* C) {d : ℕ} (b : Module.Basis (Fin d) Z N)
    (A : O → Matrix (Fin d) (Fin d) C) (hA : ∀ a i j, A a i j = φ (b.repr (a • b j) i)) :
    (∀ a a', A (a + a') = A a + A a') ∧ (∀ (x : Z) a, A (x • a) = φ x • A a) ∧ A 1 = 1 ∧
      ∀ a a', A (a * a') = A a * A a' := by
  have hc : ∀ (a : O) (x : Z) (t : N), a • (x • t) = x • (a • t) := by
    intro a x t
    rw [hs, hs, smul_smul, smul_smul, mul_comm]
  refine ⟨fun a a' => ?_, fun x a => ?_, ?_, fun a a' => ?_⟩
  · ext i j
    simp only [hA, Matrix.add_apply, add_smul, map_add, Finsupp.add_apply]
  · ext i j
    have hx : (x • a) • b j = x • (a • b j) := by
      rw [Algebra.smul_def, mul_smul, ← hs]
    simp only [hA, Matrix.smul_apply, hx, map_smul, Finsupp.smul_apply, smul_eq_mul, map_mul]
  · ext i j
    rw [hA, one_smul, Module.Basis.repr_self]
    by_cases h : i = j
    · subst h
      simp
    · simp [Finsupp.single_apply, Matrix.one_apply, h, Ne.symm h]
  · ext i j
    rw [Matrix.mul_apply, hA, mul_smul]
    conv_lhs => rw [← b.sum_repr (a' • b j)]
    rw [Finset.smul_sum]
    simp only [hc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply,
      smul_eq_mul, map_mul, hA]
    exact Finset.sum_congr rfl fun k _ => mul_comm _ _

variable {l : ℕ} [Fact l.Prime]

/- English proof (translation)
Simplify using `only [lam, kap_add, add_smul, Finset.sum_add_distrib]`.
-/
theorem lamMul_lam_add {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (x y : OCO LL) :
    lam o A (x + y) = lam o A x + lam o A y := by
  simp only [lam, kap_add, add_smul, Finset.sum_add_distrib]

/- English proof (translation)
Simplify using `only [lam, kap_zero, zero_smul, Finset.sum_const_zero]`.
-/
theorem lamMul_lam_zero {LL : FinExt l} {f d : ℕ} (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL))
    (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) :
    lam o A 0 = 0 := by
  simp only [lam, kap_zero, zero_smul, Finset.sum_const_zero]

/- English proof (translation)
Introduce `l _ K LL T d f M A o h`. Use `letI := zlMod LL T`. Take `⟨b, -, hA⟩` from `h`. Set `φ : ℤ_[l] →+* PadicComplex l` to `(algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom`. Establish `hφ : ∀ x, φ x = zC x` using `fun _ => rfl`.

Take `⟨Pa, Ps, P1, Pm⟩` from `actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T) (fun _ _ => rfl) φ b A (fun a i j => hA a i j)`. Establish `hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k)`. Introduce `a`. Establish `e` using `map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ`. Simplify using `only [AddMonoidHom.mk'_apply, o.sum_repr] at e`.

Rewrite using `[e]`. Simplify using `only [Ps, hφ]`. Establish `ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a`. Introduce `c a`. Rewrite using `[hsum a, Finset.smul_sum]`.

Simplify using `only [lam, kap_tmul, mul_smul]`. Use `⟨ht, P1, Pm, fun x y => ?_⟩` and prove the remaining obligations. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp [lamMul_lam_zero]`. Consider the case `tmul c a`.

Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp [lamMul_lam_zero]`. Consider the case `tmul c' a'`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]`. Both sides reduce to the same expression.

Consider the case `add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]`. Consider the case `add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]`.
-/
theorem lam_mul_of_isMat : ∀ (l : ℕ) [Fact l.Prime] (K LL : FinExt l) (T : LocLat ↥(GK K) ℚ_[l] ↥LL.1 ↥(OL LL)) (d f : ℕ) (M : GQ l → Matrix (Fin d) (Fin d) (PadicComplex l)) (A : ↥(OL LL) → Matrix (Fin d) (Fin d) (PadicComplex l)) (o : Module.Basis (Fin f) ℤ_[l] ↥(OL LL)), IsMat K LL T M A → (∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a) ∧ A 1 = 1 ∧ (∀ a b, A (a * b) = A a * A b) ∧ ∀ x y : OCO LL, lam o A (x * y) = lam o A x * lam o A y := by
  intro l _ K LL T d f M A o h
  letI := zlMod LL T
  obtain ⟨b, -, hA⟩ := h
  let φ : ℤ_[l] →+* PadicComplex l := (algebraMap ℚ_[l] (PadicComplex l)).comp PadicInt.Coe.ringHom
  have hφ : ∀ x, φ x = zC x := fun _ => rfl
  obtain ⟨Pa, Ps, P1, Pm⟩ := actMat_props (Z := ℤ_[l]) (O := ↥(OL LL)) (N := ↥T.L.T)
    (fun _ _ => rfl) φ b A (fun a i j => hA a i j)
  have hsum : ∀ a, A a = ∑ k, zC (o.repr a k) • A (o k) := by
    intro a
    have e := map_sum (AddMonoidHom.mk' A Pa) (fun k => o.repr a k • o k) Finset.univ
    simp only [AddMonoidHom.mk'_apply, o.sum_repr] at e
    rw [e]
    simp only [Ps, hφ]
  have ht : ∀ (c : OC l) (a : ↥(OL LL)), lam o A (c ⊗ₜ[ℤ_[l]] a) = (c : PadicComplex l) • A a := by
    intro c a
    rw [hsum a, Finset.smul_sum]
    simp only [lam, kap_tmul, mul_smul]
  refine ⟨ht, P1, Pm, fun x y => ?_⟩
  induction x using TensorProduct.induction_on with
  | zero => simp [lamMul_lam_zero]
  | tmul c a =>
    induction y using TensorProduct.induction_on with
    | zero => simp [lamMul_lam_zero]
    | tmul c' a' =>
      rw [Algebra.TensorProduct.tmul_mul_tmul, ht, ht, ht, Pm, smul_mul_smul_comm]
      rfl
    | add y₁ y₂ h₁ h₂ => rw [mul_add, lamMul_lam_add, lamMul_lam_add, h₁, h₂, mul_add]
  | add x₁ x₂ h₁ h₂ => rw [add_mul, lamMul_lam_add, lamMul_lam_add, h₁, h₂, add_mul]

end GlobalTheory.Cyc.Decomp
