import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.LinearDescent
import Development.AbelianVarietyTheory.Definitions.Divisors.GaloisRepOfPolarizedCuspidal
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MulMat
open NumberField GlobalTheory.UnitaryBC IsDedekindDomain Matrix Polynomial GlobalTheory.CuspRep Formalism.UG GlobalTheory.BCT
open scoped Classical

noncomputable section

namespace GlobalTheory.TwLat

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem betaSym_expand {K : GlobalTheory.UnitLemma.UQ} {B : GlobalTheory.UnitLemma.InvAlg K} {m : ℕ}
    (b : Module.Basis (Fin m) K.E B.A) (f : B.A →ₗ[K.E] K.E) (a : B.A) :
    f a = ∑ k, b.repr a k * f (b k) := by
  calc f a = f (∑ k, b.repr a k • b k) := by rw [b.sum_repr]
    _ = ∑ k, b.repr a k * f (b k) := by rw [map_sum]; simp only [map_smul, smul_eq_mul]

/- English proof (translation)
Establish `h` using `Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) y`. Rewrite using `[h, RingEquiv.apply_symm_apply]`.
-/
theorem betaSym_trace_sigma {K : GlobalTheory.UnitLemma.UQ} (B : GlobalTheory.UnitLemma.InvAlg K) (y : B.A) :
    Algebra.trace K.E B.A (B.σ y) = K.c (Algebra.trace K.E B.A y) := by
  have h := Algebra.trace_eq_of_equiv_equiv K.c B.σ (by ext e; simp [B.σ_alg]) y
  rw [h, RingEquiv.apply_symm_apply]

/- English proof (translation)
Introduce `E _ _ _ w K e he B m b u β hnd hG hsym`. Set `f : B.A → (B.A →ₗ[K.E] K.E)` to `fun z => (Algebra.trace K.E B.A).comp ((LinearMap.mulRight K.E (B.σ z)).comp (LinearMap.mulLeft K.E β))`. Establish `hf : ∀ y z, f z y = Algebra.trace K.E B.A (β * y * B.σ z)` using `fun y z => rfl`. Establish `hsgn : ((-1 : B.A) ^ (m - 1)) = algebraMap K.E B.A ((-1) ^ (m - 1))` using `by simp`. Use `set x : B.A := B.σ β - β * ((-1) ^ (m - 1) * u) with hx`.

Establish `h1 : ∀ i j, Algebra.trace K.E B.A (x * b j * B.σ (b i)) = 0`. Introduce `i j`. Establish `h` using `congrFun (congrFun hsym i) j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply, Matrix.transpose_apply, gram, mulMat, Matrix.of_apply, LinearMap.toMatrix_apply, LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm] at h`. Establish `hA : Algebra.trace K.E B.A (B.σ β * b j * B.σ (b i)) = K.c (Algebra.trace K.E B.A (β * b i * B.σ (b j)))`.

Rewrite using `[← betaSym_trace_sigma B]`. Use `congr 1`. Rewrite using `[map_mul, map_mul, B.σ_σ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hB : Algebra.trace K.E B.A (β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i)) = (-1) ^ (m - 1) * ∑ k, b.repr (u * b j) k * Algebra.trace K.E B.A (β * b k * B.σ (b i))`.

Establish `: β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) = ((-1 : K.E) ^ (m - 1)) • (β * (u * b j) * B.σ (b i))`. Rewrite using `[Algebra.smul_def, ← hsgn]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, map_smul, smul_eq_mul, ← hf, betaSym_expand b (f (b i)) (u * b j)]`. Both sides reduce to the same expression.

Establish `hsub : x * b j * B.σ (b i) = B.σ β * b j * B.σ (b i) - β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i)`. Rewrite using `[hx]`. Expand and normalize the polynomial expressions, which then agree. Apply `e.injective` to reduce the goal to its premises. Rewrite using `[hsub, map_sub, hA, hB, map_sub e, map_zero, he, h, map_mul e, map_sum e, map_pow, map_neg, map_one]`.

Simplify using `only [map_mul e]`. Rewrite using `[sub_eq_zero]`. Use `congr 1`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Establish `h2 : ∀ i a, Algebra.trace K.E B.A (x * B.σ (b i) * a) = 0`. Introduce `i a`. Establish `h` using `betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (x * B.σ (b i)))) a`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h`. Rewrite using `[h]`.

Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[show x * B.σ (b i) * b j = x * b j * B.σ (b i) by ring, h1, mul_zero]`. Establish `h3 : ∀ a, Algebra.trace K.E B.A (x * a) = 0`. Introduce `a`.

Establish `hs : ∀ i, Algebra.trace K.E B.A (B.σ (x * a) * b i) = 0`. Introduce `i`. Establish `h` using `h2 i a`. Rewrite `h` using `[show x * B.σ (b i) * a = B.σ (B.σ (x * a) * b i) by rw [map_mul, B.σ_σ]; ring, betaSym_trace_sigma]`. Conclude with `(map_eq_zero_iff K.c K.c.injective).mp h`.

Establish `h4` using `betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (B.σ (x * a)))) 1`. Simplify using `only [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, hs, mul_zero, Finset.sum_const_zero, betaSym_trace_sigma] at h4`. Conclude with `(map_eq_zero_iff K.c K.c.injective).mp h4`. Establish `hx0 : x = 0` using `hnd.1 x (fun n => by simpa [Algebra.traceForm_apply] using h3 n)`. Use `⟨by rw [hx] at hx0; exact sub_eq_zero.mp hx0, ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hβ`. Establish `hinj : ¬ Function.Injective (LinearMap.mulLeft K.E β)`. Introduce `hi`. Establish `hs` using `(LinearMap.injective_iff_surjective (f := LinearMap.mulLeft K.E β)).mp hi`. Take `⟨a, ha⟩` from `hs 1`.

Establish `ha' : β * a = 1` using `ha`. Conclude with `hβ ⟨⟨β, a, ha', by rw [mul_comm]; exact ha'⟩, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha0, hβa⟩ : ∃ a, a ≠ 0 ∧ β * a = 0 := by`. Rewrite `hinj` using `[injective_iff_map_eq_zero]`. Use `push_neg at hinj`.

Take `⟨a, h, ha⟩` from `hinj`. Conclude with `⟨a, ha, h⟩`. Set `v : Fin m → w.adicCompletion E` to `fun i => e (b.repr a i)`. Establish `hv : Matrix.vecMul v (gram e b β) = 0`. Use function extensionality and compare the values at `j`.

Establish `h` using `betaSym_expand b (f (b j)) a`. Simplify using `only [hf] at h`. Simplify using `only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm, v, Pi.zero_apply]`. Repeatedly rewrite using `[← map_mul e]`. Rewrite using `[← map_sum e, ← h, hβa]`.

Simplify using the standard rewrite rules. Establish `hvz : v = 0`. Establish `hdet` using `(Matrix.isUnit_iff_isUnit_det _).mp hG`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]`.

Use `_ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]`. Apply `ha0` to reduce the goal to its premises. Establish `hr : b.repr a = 0`. Use extensionality with `i`. Establish `h` using `congrFun hvz i`.

Simplify `h` using `[v]`. Simplify using `using hr`.
-/
theorem betaSym : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (w : Pl E) (K : GlobalTheory.UnitLemma.UQ) (e : K.E ≃+* w.adicCompletion E), (∀ x, e (K.c x) = cj w (e x)) → ∀ (B : GlobalTheory.UnitLemma.InvAlg K) (m : ℕ) (b : Module.Basis (Fin m) K.E B.A) (u β : B.A), (Algebra.traceForm K.E B.A).Nondegenerate → IsUnit (GlobalTheory.TwLat.gram e b β) → (cj w).mapMatrix (GlobalTheory.TwLat.gram e b β) = (-1 : w.adicCompletion E) ^ (m - 1) • ((GlobalTheory.TwLat.gram e b β)ᵀ * GlobalTheory.TwLat.mulMat e b u) → B.σ β = β * ((-1) ^ (m - 1) * u) ∧ IsUnit β := by
  intro E _ _ _ w K e he B m b u β hnd hG hsym

  let f : B.A → (B.A →ₗ[K.E] K.E) := fun z =>
    (Algebra.trace K.E B.A).comp ((LinearMap.mulRight K.E (B.σ z)).comp (LinearMap.mulLeft K.E β))
  have hf : ∀ y z, f z y = Algebra.trace K.E B.A (β * y * B.σ z) := fun y z => rfl
  have hsgn : ((-1 : B.A) ^ (m - 1)) = algebraMap K.E B.A ((-1) ^ (m - 1)) := by simp
  set x : B.A := B.σ β - β * ((-1) ^ (m - 1) * u) with hx
  have h1 : ∀ i j, Algebra.trace K.E B.A (x * b j * B.σ (b i)) = 0 := by
    intro i j
    have h := congrFun (congrFun hsym i) j
    simp only [RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, Matrix.mul_apply,
      Matrix.transpose_apply, gram, mulMat, Matrix.of_apply, LinearMap.toMatrix_apply,
      LinearMap.mulLeft_apply, GlobalTheory.UnitLemma.InvAlg.herm] at h
    have hA : Algebra.trace K.E B.A (B.σ β * b j * B.σ (b i)) =
        K.c (Algebra.trace K.E B.A (β * b i * B.σ (b j))) := by
      rw [← betaSym_trace_sigma B]; congr 1; rw [map_mul, map_mul, B.σ_σ]; ring
    have hB : Algebra.trace K.E B.A (β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i)) =
        (-1) ^ (m - 1) * ∑ k, b.repr (u * b j) k * Algebra.trace K.E B.A (β * b k * B.σ (b i)) := by
      have : β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) = ((-1 : K.E) ^ (m - 1)) • (β * (u * b j) * B.σ (b i)) := by
        rw [Algebra.smul_def, ← hsgn]; ring
      rw [this, map_smul, smul_eq_mul, ← hf, betaSym_expand b (f (b i)) (u * b j)]
      rfl
    have hsub : x * b j * B.σ (b i) = B.σ β * b j * B.σ (b i) - β * ((-1) ^ (m - 1) * u) * b j * B.σ (b i) := by
      rw [hx]; ring
    apply e.injective
    rw [hsub, map_sub, hA, hB, map_sub e, map_zero, he, h, map_mul e, map_sum e, map_pow, map_neg, map_one]
    simp only [map_mul e]
    rw [sub_eq_zero]; congr 1; refine Finset.sum_congr rfl fun k _ => ?_; ring
  have h2 : ∀ i a, Algebra.trace K.E B.A (x * B.σ (b i) * a) = 0 := by
    intro i a
    have h := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (x * B.σ (b i)))) a
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply] at h
    rw [h]
    apply Finset.sum_eq_zero
    intro j _
    rw [show x * B.σ (b i) * b j = x * b j * B.σ (b i) by ring, h1, mul_zero]
  have h3 : ∀ a, Algebra.trace K.E B.A (x * a) = 0 := by
    intro a
    have hs : ∀ i, Algebra.trace K.E B.A (B.σ (x * a) * b i) = 0 := by
      intro i
      have h := h2 i a
      rw [show x * B.σ (b i) * a = B.σ (B.σ (x * a) * b i) by rw [map_mul, B.σ_σ]; ring,
        betaSym_trace_sigma] at h
      exact (map_eq_zero_iff K.c K.c.injective).mp h
    have h4 := betaSym_expand b ((Algebra.trace K.E B.A).comp (LinearMap.mulLeft K.E (B.σ (x * a)))) 1
    simp only [LinearMap.comp_apply, LinearMap.mulLeft_apply, mul_one, hs, mul_zero, Finset.sum_const_zero,
      betaSym_trace_sigma] at h4
    exact (map_eq_zero_iff K.c K.c.injective).mp h4
  have hx0 : x = 0 := hnd.1 x (fun n => by simpa [Algebra.traceForm_apply] using h3 n)
  refine ⟨by rw [hx] at hx0; exact sub_eq_zero.mp hx0, ?_⟩
  by_contra hβ
  have hinj : ¬ Function.Injective (LinearMap.mulLeft K.E β) := by
    intro hi
    have hs := (LinearMap.injective_iff_surjective (f := LinearMap.mulLeft K.E β)).mp hi
    obtain ⟨a, ha⟩ := hs 1
    have ha' : β * a = 1 := ha
    exact hβ ⟨⟨β, a, ha', by rw [mul_comm]; exact ha'⟩, rfl⟩
  obtain ⟨a, ha0, hβa⟩ : ∃ a, a ≠ 0 ∧ β * a = 0 := by
    rw [injective_iff_map_eq_zero] at hinj
    push_neg at hinj
    obtain ⟨a, h, ha⟩ := hinj
    exact ⟨a, ha, h⟩
  let v : Fin m → w.adicCompletion E := fun i => e (b.repr a i)
  have hv : Matrix.vecMul v (gram e b β) = 0 := by
    funext j
    have h := betaSym_expand b (f (b j)) a
    simp only [hf] at h
    simp only [Matrix.vecMul, dotProduct, gram, Matrix.of_apply, GlobalTheory.UnitLemma.InvAlg.herm, v, Pi.zero_apply]
    simp_rw [← map_mul e]
    rw [← map_sum e, ← h, hβa]
    simp
  have hvz : v = 0 := by
    have hdet := (Matrix.isUnit_iff_isUnit_det _).mp hG
    calc v = Matrix.vecMul v (gram e b β * (gram e b β)⁻¹) := by
          rw [Matrix.mul_nonsing_inv _ hdet, Matrix.vecMul_one]
      _ = 0 := by rw [← Matrix.vecMul_vecMul, hv, Matrix.zero_vecMul]
  apply ha0
  have hr : b.repr a = 0 := by
    ext i
    have h := congrFun hvz i
    simpa [v] using h
  simpa using hr

end GlobalTheory.TwLat
