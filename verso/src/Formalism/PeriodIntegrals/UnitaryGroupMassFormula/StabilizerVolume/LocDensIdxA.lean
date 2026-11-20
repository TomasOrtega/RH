import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerVolume.LocDensIdxH

noncomputable section

namespace PI.VolStabS

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
Use `filter_upwards [(IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x).compl_mem_cofinite] with v hv`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Establish `hv' : v.valuation F x ≤ 1`. Simplify `hv` using `[IsDedekindDomain.HeightOneSpectrum.Support]`. Conclude with `(IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).le.trans hv'`.
-/
theorem eventually_int (x : F) :
    ∀ᶠ v in cofinite, algebraMap F (Fv F v) x ∈ v.adicCompletionIntegers F := by
  filter_upwards [(IsDedekindDomain.HeightOneSpectrum.Support.finite (𝓞 F) x).compl_mem_cofinite] with v hv
  rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
  have hv' : v.valuation F x ≤ 1 := by
    simpa [IsDedekindDomain.HeightOneSpectrum.Support] using hv
  exact (IsDedekindDomain.HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v x).le.trans hv'

end IdxHW

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, (C - 1) i ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hC` to reduce the goal to its premises. Use extensionality with `a c`.

Use `congrFun (h a) c` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`. Establish `hab : (C - 1) i 0 ≠ 0 ∨ (C - 1) i 1 ≠ 0`. Assume the negation of the conclusion as `h`. Use `push_neg at h`.

Apply `hi` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Conclude with `h.1`. Conclude with `h.2`.

Establish `hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → algebraMap F K ((C - 1) i 0) * x 0 + algebraMap F K ((C - 1) i 1) * x 1 = 0`. Introduce `K _ _ x hx`. Use `congrFun hx i` as an intermediate fact. Simplify using `only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at this`. Apply the tactic sequence `fin_cases i <;> simp [Matrix.sub_apply, Matrix.one_apply] at this ⊢ <;> linear_combination this`.

Establish `key : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x 0 * algebraMap F K (u 1) = x 1 * algebraMap F K (u 0)`. Introduce `K _ _ x hx`. Establish `E1` using `hrow K x hx`. Establish `E2 : algebraMap F K ((C - 1) i 0) * algebraMap F K (u 0) + algebraMap F K ((C - 1) i 1) * algebraMap F K (u 1) = 0`. Use `hrow F u (by simpa using hCu)` as an intermediate fact.

Use `congrArg (algebraMap F K) this` as an intermediate fact. Simplify `this` using `[map_add, map_mul]`. Break down `hab with ha | hb` into its components or cases. Establish `hA : algebraMap F K ((C - 1) i 0) ≠ 0` using `(map_ne_zero _).2 ha`. Apply `mul_left_cancel₀ hA` to reduce the goal to its premises.

Take the linear combination `algebraMap F K (u 1) * E1 - x 1 * E2`. Establish `hB : algebraMap F K ((C - 1) i 1) ≠ 0` using `(map_ne_zero _).2 hb`. Apply `mul_left_cancel₀ hB` to reduce the goal to its premises. Take the linear combination `x 0 * E2 - algebraMap F K (u 0) * E1`. Distinguish the cases in `hu0 : u 0 ≠ 0`.

Use `⟨0, 1, by decide, hu0, u 1 / u 0, fun K _ _ x hx => ?_⟩` and prove the remaining obligations. Establish `h1` using `key K x hx`. Establish `hu0' : algebraMap F K (u 0) ≠ 0` using `(map_ne_zero _).2 hu0`. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `-h1`. Use `push_neg at hu0`. Establish `hu1 : u 1 ≠ 0`. Introduce `h1`. Apply `hu` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Use `fin_cases j`. Conclude with `hu0`. Conclude with `h1`. Use `⟨1, 0, by decide, hu1, u 0 / u 1, fun K _ _ x hx => ?_⟩` and prove the remaining obligations.

Establish `h1` using `key K x hx`. Establish `hu1' : algebraMap F K (u 1) ≠ 0` using `(map_ne_zero _).2 hu1`. Rewrite using `[map_div₀]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h1`.
-/
theorem fix2 {F : Type} [Field F] (C : Matrix (Fin 2) (Fin 2) F) (hC : C ≠ 1) (u : Fin 2 → F)
    (hu : u ≠ 0) (hCu : Matrix.mulVec C u = u) :
    ∃ k0 k1 : Fin 2, k0 ≠ k1 ∧ u k0 ≠ 0 ∧ ∃ ρ : F, ∀ (K : Type) [Field K] [Algebra F K]
      (x : Fin 2 → K), Matrix.mulVec (C.map (algebraMap F K)) x = x → x k1 = algebraMap F K ρ * x k0 := by
  obtain ⟨i, hi⟩ : ∃ i, (C - 1) i ≠ 0 := by
    by_contra h
    push_neg at h
    apply hC
    ext a c
    have := congrFun (h a) c
    simpa [sub_eq_zero] using this
  have hab : (C - 1) i 0 ≠ 0 ∨ (C - 1) i 1 ≠ 0 := by
    by_contra h
    push_neg at h
    apply hi
    funext j
    fin_cases j
    · exact h.1
    · exact h.2
  have hrow : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
      algebraMap F K ((C - 1) i 0) * x 0 + algebraMap F K ((C - 1) i 1) * x 1 = 0 := by
    intro K _ _ x hx
    have := congrFun hx i
    simp only [Matrix.mulVec, dotProduct, Fin.sum_univ_two, Matrix.map_apply] at this
    fin_cases i <;> simp [Matrix.sub_apply, Matrix.one_apply] at this ⊢ <;> linear_combination this
  have key : ∀ (K : Type) [Field K] [Algebra F K] (x : Fin 2 → K),
      Matrix.mulVec (C.map (algebraMap F K)) x = x →
      x 0 * algebraMap F K (u 1) = x 1 * algebraMap F K (u 0) := by
    intro K _ _ x hx
    have E1 := hrow K x hx
    have E2 : algebraMap F K ((C - 1) i 0) * algebraMap F K (u 0) +
        algebraMap F K ((C - 1) i 1) * algebraMap F K (u 1) = 0 := by
      have := hrow F u (by simpa using hCu)
      have := congrArg (algebraMap F K) this
      simpa [map_add, map_mul] using this
    rcases hab with ha | hb
    · have hA : algebraMap F K ((C - 1) i 0) ≠ 0 := (map_ne_zero _).2 ha
      apply mul_left_cancel₀ hA
      linear_combination algebraMap F K (u 1) * E1 - x 1 * E2
    · have hB : algebraMap F K ((C - 1) i 1) ≠ 0 := (map_ne_zero _).2 hb
      apply mul_left_cancel₀ hB
      linear_combination x 0 * E2 - algebraMap F K (u 0) * E1
  by_cases hu0 : u 0 ≠ 0
  · refine ⟨0, 1, by decide, hu0, u 1 / u 0, fun K _ _ x hx => ?_⟩
    have h1 := key K x hx
    have hu0' : algebraMap F K (u 0) ≠ 0 := (map_ne_zero _).2 hu0
    rw [map_div₀]
    field_simp
    linear_combination -h1
  · push_neg at hu0
    have hu1 : u 1 ≠ 0 := by
      intro h1
      apply hu
      funext j
      fin_cases j
      · exact hu0
      · exact h1
    refine ⟨1, 0, by decide, hu1, u 0 / u 1, fun K _ _ x hx => ?_⟩
    have h1 := key K x hx
    have hu1' : algebraMap F K (u 1) ≠ 0 := (map_ne_zero _).2 hu1
    rw [map_div₀]
    field_simp
    linear_combination h1

end PI.VolStabS
