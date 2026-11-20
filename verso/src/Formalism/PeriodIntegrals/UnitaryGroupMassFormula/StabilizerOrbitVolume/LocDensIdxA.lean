import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.LocDensIdxH

noncomputable section

namespace PI.VolStabSW

open scoped TensorProduct
open NumberField IsDedekindDomain Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

namespace IdxHW

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {d : ℕ}
  (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (σ : E →ₐ[F] E)

/- English proof (translation)
Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r e`. Establish `hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e`. Simplify using `[sigR, Algebra.TensorProduct.map_tmul]`.

Rewrite using `[hs]`. Simplify using `only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply, smul_eq_mul]`. Establish `he : σ e = ∑ l, b.repr e l • σ (b l)`. Establish `h` using `congrArg σ (b.sum_repr e)`. Rewrite `h` using `[map_sum]`.

Simplify using `only [map_smul] at h`. Conclude with `h.symm`. Rewrite using `[he, map_sum]`. Simplify using `only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, map_sum, map_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations.

Expand and normalize the polynomial expressions, which then agree. Consider the case `add x y hx hy`. Rewrite using `[map_add, map_add, Finsupp.add_apply, hx, hy, map_add]`. Simplify using `only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]`.
-/
theorem crd_sigR (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (sigR (Fv F v) σ y) k =
      ∑ l, algebraMap F (Fv F v) (b.repr (σ (b l)) k) *
        (Algebra.TensorProduct.basis (Fv F v) b).repr y l := by
  induction y using TensorProduct.induction_on with
  | zero => simp
  | tmul r e =>
    have hs : sigR (Fv F v) σ (r ⊗ₜ[F] e) = r ⊗ₜ[F] σ e := by
      simp [sigR, Algebra.TensorProduct.map_tmul]
    rw [hs]
    simp only [Algebra.TensorProduct.basis_repr_tmul, Finsupp.smul_apply, Finsupp.mapRange_apply,
      smul_eq_mul]
    have he : σ e = ∑ l, b.repr e l • σ (b l) := by
      have h := congrArg σ (b.sum_repr e)
      rw [map_sum] at h
      simp only [map_smul] at h
      exact h.symm
    rw [he, map_sum]
    simp only [map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul,
      map_sum, map_mul, Finset.mul_sum]
    refine Finset.sum_congr rfl fun l _ => ?_
    ring
  | add x y hx hy =>
    rw [map_add, map_add, Finsupp.add_apply, hx, hy, map_add]
    simp only [Finsupp.add_apply, mul_add, Finset.sum_add_distrib]

/- English proof (translation)
The claim follows from `(algebraMap F (FiniteAdeleRing (𝓞 F) F) x).eventually`.
-/
theorem eventually_int (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F :=
  (algebraMap F (FiniteAdeleRing (𝓞 F) F) x).eventually

end IdxHW

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨r, hr⟩ : ∃ r : Fin 2, (C - 1) r 0 ≠ 0 ∨ (C - 1) r 1 ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Apply `hC` to reduce the goal to its premises. Establish `: C - 1 = 0`.

Use extensionality with `i j`. Use `fin_cases j`. Conclude with `(h i).1`. Conclude with `(h i).2`. Conclude with `sub_eq_zero.1 this`.

Establish `hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → algebraMap F K ((C - 1) r 0) * x 0 + algebraMap F K ((C - 1) r 1) * x 1 = 0`. Introduce `K _ _ x hx`. Establish `h` using `congrFun hx r`. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at h`. Simplify using `only [Matrix.sub_apply, Matrix.one_apply, map_sub]`.

Apply the tactic sequence `fin_cases r <;> simp at h ⊢ <;> linear_combination h`. Establish `hrowu` using `hrow F u (by simpa using hCu)`. Simplify using `only [Algebra.algebraMap_self, RingHom.id_apply] at hrowu`. Distinguish the cases in `hβ : (C - 1) r 1 ≠ 0`. Use `⟨0, 1, by decide, ?_, -((C - 1) r 0) / (C - 1) r 1, fun K _ _ x hx => ?_⟩` and prove the remaining obligations.

Introduce `h0`. Apply `hu` to reduce the goal to its premises. Establish `h1 : u 1 = 0`. Rewrite `hrowu` using `[h0, mul_zero, zero_add]`. Conclude with `(mul_eq_zero.1 hrowu).resolve_left hβ`.

Use extensionality with `i`. Use `fin_cases i`. Conclude with `h0`. Conclude with `h1`. Establish `h` using `hrow K x hx`.

Establish `hβK : algebraMap F K ((C - 1) r 1) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap F K).injective]`. Conclude with `hβ`. Rewrite using `[map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `h`. Use `push Not at hβ`. Establish `hα : (C - 1) r 0 ≠ 0` using `hr.resolve_right (by rw [hβ]; exact fun h => h rfl)`. Establish `hu0 : u 0 = 0`. Rewrite `hrowu` using `[hβ, zero_mul, add_zero]`.

Conclude with `(mul_eq_zero.1 hrowu).resolve_left hα`. Use `⟨1, 0, by decide, ?_, 0, fun K _ _ x hx => ?_⟩` and prove the remaining obligations. Introduce `h1`. Apply `hu` to reduce the goal to its premises. Use extensionality with `i`.

Use `fin_cases i`. Conclude with `hu0`. Conclude with `h1`. Establish `h` using `hrow K x hx`. Rewrite `h` using `[hβ, map_zero, zero_mul, add_zero]`.

Establish `hαK : algebraMap F K ((C - 1) r 0) ≠ 0`. Rewrite using `[Ne, map_eq_zero_iff _ (algebraMap F K).injective]`. Conclude with `hα`. Rewrite using `[map_zero, zero_mul]`. Conclude with `(mul_eq_zero.1 h).resolve_left hαK`.
-/
theorem fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  classical
  obtain ⟨r, hr⟩ : ∃ r : Fin 2, (C - 1) r 0 ≠ 0 ∨ (C - 1) r 1 ≠ 0 := by
    by_contra h
    push Not at h
    apply hC
    have : C - 1 = 0 := by
      ext i j
      fin_cases j
      · exact (h i).1
      · exact (h i).2
    exact sub_eq_zero.1 this
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
        algebraMap F K ((C - 1) r 0) * x 0 + algebraMap F K ((C - 1) r 1) * x 1 = 0 := by
    intro K _ _ x hx
    have h := congrFun hx r
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at h
    simp only [Matrix.sub_apply, Matrix.one_apply, map_sub]
    fin_cases r <;> simp at h ⊢ <;> linear_combination h
  have hrowu := hrow F u (by simpa using hCu)
  simp only [Algebra.algebraMap_self, RingHom.id_apply] at hrowu
  by_cases hβ : (C - 1) r 1 ≠ 0
  · refine ⟨0, 1, by decide, ?_, -((C - 1) r 0) / (C - 1) r 1, fun K _ _ x hx => ?_⟩
    · intro h0
      apply hu
      have h1 : u 1 = 0 := by
        rw [h0, mul_zero, zero_add] at hrowu
        exact (mul_eq_zero.1 hrowu).resolve_left hβ
      ext i
      fin_cases i
      · exact h0
      · exact h1
    · have h := hrow K x hx
      have hβK : algebraMap F K ((C - 1) r 1) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hβ
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  · push Not at hβ
    have hα : (C - 1) r 0 ≠ 0 := hr.resolve_right (by rw [hβ]; exact fun h => h rfl)
    have hu0 : u 0 = 0 := by
      rw [hβ, zero_mul, add_zero] at hrowu
      exact (mul_eq_zero.1 hrowu).resolve_left hα
    refine ⟨1, 0, by decide, ?_, 0, fun K _ _ x hx => ?_⟩
    · intro h1
      apply hu
      ext i
      fin_cases i
      · exact hu0
      · exact h1
    · have h := hrow K x hx
      rw [hβ, map_zero, zero_mul, add_zero] at h
      have hαK : algebraMap F K ((C - 1) r 0) ≠ 0 := by
        rw [Ne, map_eq_zero_iff _ (algebraMap F K).injective]; exact hα
      rw [map_zero, zero_mul]
      exact (mul_eq_zero.1 h).resolve_left hαK

end PI.VolStabSW
