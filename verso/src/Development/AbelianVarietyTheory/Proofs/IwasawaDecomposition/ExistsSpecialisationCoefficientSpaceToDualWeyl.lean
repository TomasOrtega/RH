import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IncludeLInjective
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT Formalism.IndefR.NX GlobalTheory.HeightCounting GlobalTheory.HeightCounting.FormsStep NumberField IsDedekindDomain Polynomial
open scoped TensorProduct

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [DecidableEq ι] {n : ℕ}

noncomputable def specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) :
    Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K :=
  MvPolynomial.aeval fun v => if v.1 = τ₀ then MvPolynomial.X v.2 else MvPolynomial.C (y v)

/- English proof (translation)
Establish `h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom = MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v)`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using `[specAt]`. Introduce `v`.

Apply the tactic sequence `by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]`. Conclude with `congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h`.
-/
theorem eval_specAt (τ₀ : ι) (y : ι × Fin n × Fin n → K) (z : Fin n × Fin n → K) (w : Formalism.L2.DIV.Pol K ι n) :
    MvPolynomial.eval z (specAt τ₀ y w) =
      MvPolynomial.eval (fun v => if v.1 = τ₀ then z v.2 else y v) w := by
  have h : (MvPolynomial.eval z).comp (specAt τ₀ y).toRingHom =
      MvPolynomial.eval (fun v : ι × Fin n × Fin n => if v.1 = τ₀ then z v.2 else y v) := by
    apply MvPolynomial.ringHom_ext
    · intro r; simp [specAt]
    · intro v
      by_cases hv : v.1 = τ₀ <;> simp [specAt, hv]
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →+* K => f w) h

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `hw` to reduce the goal to its premises. Apply `MvPolynomial.funext` to reduce the goal to its premises. Introduce `z`.

Use `congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)` as an intermediate fact. Rewrite `this` using `[eval_specAt, map_zero]`. Rewrite using `[map_zero, ← this]`. Use `congr 2`. Use function extensionality and compare the values at `v`.

Use `split_ifs with hv`. Take `⟨a, b⟩` from `v`. Simplify using `only at hv`. Substitute `hv` using the available equality. Both sides reduce to the same expression.

Both sides reduce to the same expression.
-/
theorem exists_specAt_ne [Infinite K] (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n) (hw : w ≠ 0) :
    ∃ y, specAt τ₀ y w ≠ 0 := by
  by_contra h
  push_neg at h
  apply hw
  apply MvPolynomial.funext
  intro z
  have := congrArg (MvPolynomial.eval (fun v : Fin n × Fin n => z (τ₀, v))) (h z)
  rw [eval_specAt, map_zero] at this
  rw [map_zero, ← this]
  congr 2
  funext v
  split_ifs with hv
  · obtain ⟨a, b⟩ := v; simp only at hv; subst hv; rfl
  · rfl

/- English proof (translation)
Unfold `specAt Formalism.GradedWeylDivisibility.blockEmb`. Rewrite using `[MvPolynomial.aeval_rename]`. Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `only [Function.comp_def, if_true]`.

Conclude with `MvPolynomial.aeval_X_left_apply F`. Simplify using `only [Function.comp_def, h, if_false]`. Establish `hh : (MvPolynomial.aeval (R` using `K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom = MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using the standard rewrite rules. Introduce `v`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh`.
-/
theorem specAt_blockEmb (τ₀ : ι) (y : ι × Fin n × Fin n → K) (τ : ι) (F : MvPolynomial (Fin n × Fin n) K) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockEmb K τ F) =
      if τ = τ₀ then F else MvPolynomial.C (MvPolynomial.eval (fun v => y (τ, v)) F) := by
  unfold specAt Formalism.GradedWeylDivisibility.blockEmb
  rw [MvPolynomial.aeval_rename]
  split_ifs with h
  · subst h
    simp only [Function.comp_def, if_true]
    exact MvPolynomial.aeval_X_left_apply F
  · simp only [Function.comp_def, h, if_false]
    have hh : (MvPolynomial.aeval (R := K) fun x : Fin n × Fin n => (MvPolynomial.C (y (τ, x)) : MvPolynomial (Fin n × Fin n) K)).toRingHom =
        MvPolynomial.C.comp (MvPolynomial.eval fun v => y (τ, v)) := by
      apply MvPolynomial.ringHom_ext
      · intro r; simp
      · intro v; simp
    exact congrArg (fun f : MvPolynomial (Fin n × Fin n) K →+* MvPolynomial (Fin n × Fin n) K => f F) hh

end GlobalTheory.SpecFactor

namespace GlobalTheory.SpecFactor

open MvPolynomial

variable {K : Type} [Field K] {ι : Type} [Fintype ι] [DecidableEq ι] {n : ℕ}

/- English proof (translation)
Unfold `Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP`. Proceed by induction on `hP using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨F, hF, rfl⟩` from `hx`. Rewrite using `[map_prod]`.

Simplify using `only [specAt_blockEmb]`. Rewrite using `[Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]`. Establish `: ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) = MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i))`. Rewrite using `[map_prod]`. Use `Finset.prod_congr rfl fun i hi => ?_` and prove the remaining obligations.

Rewrite using `[if_neg (by simpa using hi)]`. Rewrite using `[this, ← MvPolynomial.smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ (hF τ₀)`. Consider the case `zero => simp`. Consider the case `add x z _ _ hx hz => rw [map_add]`.

Conclude with `Submodule.add_mem _ hx hz`. Consider the case `smul a x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem specAt_mem (lam : ι → DomWeight n) (τ₀ : ι) (y : ι × Fin n × Fin n → K) (P : Formalism.L2.DIV.Pol K ι n)
    (hP : P ∈ Formalism.L2.DIV.VV K lam) : specAt τ₀ y P ∈ nablaSq K n (lam τ₀) := by
  unfold Formalism.L2.DIV.VV Formalism.GradedWeylDivisibility.tensorLat at hP
  induction hP using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨F, hF, rfl⟩ := hx
    rw [map_prod]
    simp only [specAt_blockEmb]
    rw [Fintype.prod_eq_mul_prod_compl τ₀, if_pos rfl, mul_comm]
    have : ∏ i ∈ ({τ₀}ᶜ : Finset ι), (if i = τ₀ then F i else
        MvPolynomial.C (MvPolynomial.eval (fun v => y (i, v)) (F i))) =
        MvPolynomial.C (∏ i ∈ ({τ₀}ᶜ : Finset ι), MvPolynomial.eval (fun v => y (i, v)) (F i)) := by
      rw [map_prod]
      refine Finset.prod_congr rfl fun i hi => ?_
      rw [if_neg (by simpa using hi)]
    rw [this, ← MvPolynomial.smul_eq_C_mul]
    exact Submodule.smul_mem _ _ (hF τ₀)
  | zero => simp
  | add x z _ _ hx hz => rw [map_add]; exact Submodule.add_mem _ hx hz
  | smul a x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

/- English proof (translation)
Establish `h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n` using `n) (fun τ => if τ = τ₀ then M else 1)) = (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce and unpack `⟨τ, a, b⟩`. Distinguish the cases in `hτ : τ = τ₀`. Substitute `hτ` using the available equality.

Simplify using `[specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]`. Simplify using `only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul, MvPolynomial.aeval_C, Matrix.one_apply]`. Rewrite using `[Finset.sum_eq_single a]`. Simplify using `[hτ]`. Introduce `c _ hc`.

Simplify using `[Ne.symm hc]`. Simplify using the standard rewrite rules. Conclude with `congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h`.
-/
theorem specAt_blockAct (τ₀ : ι) (y : ι × Fin n × Fin n → K) (M : Matrix (Fin n) (Fin n) K)
    (P : Formalism.L2.DIV.Pol K ι n) :
    specAt τ₀ y (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) =
      Formalism.GradedWeylDivisibility.rowAct K M (specAt τ₀ y P) := by
  have h : (specAt τ₀ y).comp (Formalism.GradedWeylDivisibility.blockAct K (n := n) (fun τ => if τ = τ₀ then M else 1)) =
      (Formalism.GradedWeylDivisibility.rowAct K M).comp (specAt τ₀ y) := by
    apply MvPolynomial.algHom_ext
    rintro ⟨τ, a, b⟩
    by_cases hτ : τ = τ₀
    · subst hτ
      simp [specAt, Formalism.GradedWeylDivisibility.blockAct, Formalism.GradedWeylDivisibility.rowAct]
    · simp only [AlgHom.comp_apply, Formalism.GradedWeylDivisibility.blockAct, specAt, MvPolynomial.aeval_X, hτ, if_false, map_sum, map_mul,
        MvPolynomial.aeval_C, Matrix.one_apply]
      rw [Finset.sum_eq_single a]
      · simp [hτ]
      · intro c _ hc; simp [Ne.symm hc]
      · simp
  exact congrArg (fun f : Formalism.L2.DIV.Pol K ι n →ₐ[K] MvPolynomial (Fin n × Fin n) K => f P) h

end GlobalTheory.SpecFactor

/- English proof (translation)
Introduce `K _ _ n ι _ _ lam τ₀ w _ hw`. Take `⟨y, hy⟩` from `GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw`. Conclude with `⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy, fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP, fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩`.
-/
theorem GlobalTheory.specialise_factor : ∀ (K : Type) [Field K] [Infinite K] (n : ℕ) (ι : Type) [Fintype ι] [DecidableEq ι]
    (lam : ι → DomWeight n) (τ₀ : ι) (w : Formalism.L2.DIV.Pol K ι n), w ∈ Formalism.L2.DIV.VV K lam → w ≠ 0 →
    ∃ φ : Formalism.L2.DIV.Pol K ι n →ₗ[K] MvPolynomial (Fin n × Fin n) K, φ w ≠ 0 ∧
      (∀ P ∈ Formalism.L2.DIV.VV K lam, φ P ∈ nablaSq K n (lam τ₀)) ∧
      ∀ (M : Matrix (Fin n) (Fin n) K) (P : Formalism.L2.DIV.Pol K ι n),
        φ (Formalism.GradedWeylDivisibility.blockAct K (fun τ => if τ = τ₀ then M else 1) P) = Formalism.GradedWeylDivisibility.rowAct K M (φ P) := by
  intro K _ _ n ι _ _ lam τ₀ w _ hw
  obtain ⟨y, hy⟩ := GlobalTheory.SpecFactor.exists_specAt_ne τ₀ w hw
  exact ⟨(GlobalTheory.SpecFactor.specAt τ₀ y).toLinearMap, hy,
    fun P hP => GlobalTheory.SpecFactor.specAt_mem lam τ₀ y P hP,
    fun M P => GlobalTheory.SpecFactor.specAt_blockAct τ₀ y M P⟩
