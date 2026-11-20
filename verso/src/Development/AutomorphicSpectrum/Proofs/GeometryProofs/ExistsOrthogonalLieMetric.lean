import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.SlopeBoundSt
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.ArchBetween
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.BdryChart
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.ClopenCondOnto
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.BlowupProjections.BlowupProjStatement
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieMetricStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueAct
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.ExistsLieModel
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.MetricOrth

/- English proof (translation)
Establish `hinj : Function.Injective φ`. Rewrite using `[RingHom.injective_iff_ker_eq_bot]`. Use `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_` and prove the remaining obligations. Rewrite using `[eq_bot_iff]`. Introduce `n hn`.

Establish `h0 : φ (algebraMap ℤ (𝓞 E) n) = 0` using `hn`. Establish `h1 : (n : ℂ) = 0` using `by simpa using h0`. Establish `h2 : n = 0` using `by exact_mod_cast h1`. Simplify using `[h2]`. Use `⟨IsFractionRing.lift hinj, ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Simplify using the standard rewrite rules.
-/
theorem exists_ext (E : Type) [Field E] [NumberField E] (φ : 𝓞 E →+* ℂ) :
    ∃ τ : E →+* ℂ, τ.comp (algebraMap (𝓞 E) E) = φ := by
  have hinj : Function.Injective φ := by
    rw [RingHom.injective_iff_ker_eq_bot]
    refine Ideal.eq_bot_of_comap_eq_bot (R := ℤ) ?_
    rw [eq_bot_iff]
    intro n hn
    have h0 : φ (algebraMap ℤ (𝓞 E) n) = 0 := hn
    have h1 : (n : ℂ) = 0 := by simpa using h0
    have h2 : n = 0 := by exact_mod_cast h1
    simp [h2]
  refine ⟨IsFractionRing.lift hinj, ?_⟩
  ext a
  simp

def resEquiv (E : Type) [Field E] [NumberField E] : (E →+* ℂ) ≃ (𝓞 E →+* ℂ) :=
  Equiv.ofBijective (fun τ => τ.comp (algebraMap (𝓞 E) E))
    ⟨fun τ τ' h => IsFractionRing.injective_comp_algebraMap (A := 𝓞 E) h, fun φ => exists_ext E φ⟩

instance fintypeIntEmb (E : Type) [Field E] [NumberField E] : Fintype (𝓞 E →+* ℂ) := Fintype.ofEquiv _ (resEquiv E)

/- English proof (translation)
Set `Ix` to `Module.Free.ChooseBasisIndex ℤ (𝓞 E)`. Set `b` to `RingOfIntegers.basis E`. Set `T` to `𝓞 E →+* ℂ`. Establish `hcard : Fintype.card Ix = Fintype.card (E →ₐ[ℚ] ℂ)`. Rewrite using `[AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]`.

Set `e₁ : Ix ≃ (E →ₐ[ℚ] ℂ)` to `Fintype.equivOfCardEq hcard`. Set `e₂ : Ix ≃ T` to `(e₁.trans (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm).trans (resEquiv E)`. Set `N : Matrix Ix Ix ℂ` to `Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₁`. Establish `hN : N.det ≠ 0`. Introduce `h`.

Establish `h1` using `Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₁`. Establish `h2` using `Algebra.discr_not_zero_of_basis ℚ (integralBasis E)`. Apply `h2` to reduce the goal to its premises. Establish `: algebraMap ℚ ℂ (Algebra.discr ℚ (integralBasis E)) = 0`. Rewrite using `[h1]`.

Use `show N.det ^ 2 = 0`. Rewrite using `[h]`. Simplify using the standard rewrite rules. Simplify using `using this`. Set `A : Matrix T Ix ℂ` to `Matrix.of fun σ a => σ (b a)`.

Establish `hA : A = Nᵀ.submatrix e₂.symm (Equiv.refl Ix)`. Use extensionality with `σ a`. Take `⟨j, rfl⟩` from `e₂.surjective σ`. Simplify using `only [A, Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.transpose_apply, N, Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply, Equiv.refl_apply, Equiv.refl_symm, Equiv.symm_symm]`. Simplify using `[e₂, resEquiv, b, integralBasis_apply]`.

Both sides reduce to the same expression. Establish `hNu : IsUnit Nᵀ.det`. Rewrite using `[Matrix.det_transpose]`. Conclude with `isUnit_iff_ne_zero.2 hN`. Set `B : Matrix Ix T ℂ` to `(Nᵀ)⁻¹.submatrix (Equiv.refl Ix) e₂.symm`.

Establish `hAB : A * B = 1`. Rewrite using `[hA, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hNu, Matrix.submatrix_one_equiv]`. Establish `hBA : B * A = 1` using `(Matrix.mul_eq_one_comm_of_equiv e₂.symm).1 hAB`. Establish `hAB' : ∀ σ τ, ∑ a, B a τ * σ (b a) = (1 : Matrix T T ℂ) σ τ` using `fun σ τ => by`. Rewrite using `[← hAB, Matrix.mul_apply]`.

Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Establish `hBA' : ∀ a c, ∑ τ : T, B a τ * τ (b c) = (1 : Matrix Ix Ix ℂ) a c` using `fun a c => by`. Rewrite using `[← hBA, Matrix.mul_apply]`. Both sides reduce to the same expression. Establish `hcc : ∀ τ : T, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ` using `fun τ => by`.

Use extensionality with `x`. Simplify using the standard rewrite rules. Set `cj : T ≃ T` to `⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩`. Set `B' : Matrix Ix T ℂ` to `Matrix.of fun a τ => starRingEnd ℂ (B a (cj τ))`. Establish `hAB2 : A * B' = 1`.

Use extensionality with `σ τ`. Establish `h1` using `congrArg (starRingEnd ℂ) (hAB' (cj σ) (cj τ))`. Establish `h2 : (1 : Matrix T T ℂ) (cj σ) (cj τ) = (1 : Matrix T T ℂ) σ τ`. Simplify using `[Matrix.one_apply, cj.injective.eq_iff]`. Rewrite `h1` using `[h2, map_sum]`.

Rewrite using `[Matrix.mul_apply]`. Establish `h3 : starRingEnd ℂ ((1 : Matrix T T ℂ) σ τ) = (1 : Matrix T T ℂ) σ τ`. Apply the tactic sequence `by_cases h : σ = τ <;> simp [Matrix.one_apply, h]`. Rewrite `h1` using `[h3]`. Rewrite using `[← h1]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Simplify using `only [A, B', Matrix.of_apply, map_mul]`. Establish `: starRingEnd ℂ ((cj σ) (b a)) = σ (b a)` using `by show starRingEnd ℂ (starRingEnd ℂ (σ (b a))) = _`. Simplify using the standard rewrite rules. Rewrite using `[this, mul_comm]`.

Establish `hB' : B' = B`. Combine the equalities or inequalities in the displayed calculation. Use `⟨Ix, inferInstance, fun a => b a, fun τ a => B a τ, fun a => b.repr 1 a, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `τ`. Rewrite using `[hAB' τ τ]`.

Simplify using the standard rewrite rules. Introduce `σ τ h`. Rewrite using `[hAB' σ τ]`. Simplify using `[Matrix.one_apply, h]`. Introduce `τ a`.

Use `congrFun (congrFun hB' a) (cj τ)` as an intermediate fact. Simplify using `only [B', Matrix.of_apply] at this`. Establish `h2 : cj (cj τ) = τ` using `hcc τ`. Rewrite `this` using `[h2]`. Conclude with `this`.

Conclude with `b.sum_repr 1`. Introduce `a`. Establish `h1 : ∀ τ : T, (1 : ℂ) = ∑ c, (b.repr 1 c : ℂ) * τ (b c)` using `fun τ => by`. Use `congrArg τ (b.sum_repr 1)` as an intermediate fact. Simplify using `using this.symm`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => by ring`. Use `_ = (b.repr 1 a : ℂ) := by`.

Simplify using `only [hBA', Matrix.one_apply]`. Simplify using the standard rewrite rules.
-/
theorem exists_coeff (E : Type) [Field E] [NumberField E] :
    ∃ (Ix : Type) (_ : Fintype Ix) (α : Ix → 𝓞 E) (d : (𝓞 E →+* ℂ) → Ix → ℂ) (m : Ix → ℤ),
      (∀ τ : 𝓞 E →+* ℂ, ∑ a, d τ a * τ (α a) = 1) ∧
      (∀ σ τ : 𝓞 E →+* ℂ, σ ≠ τ → ∑ a, d τ a * σ (α a) = 0) ∧
      (∀ (τ : 𝓞 E →+* ℂ) a, starRingEnd ℂ (d τ a) = d ((starRingEnd ℂ).comp τ) a) ∧
      (∑ a, m a • α a = 1) ∧ ∀ a, ∑ τ, d τ a = m a := by
  classical
  let Ix := Module.Free.ChooseBasisIndex ℤ (𝓞 E)
  let b := RingOfIntegers.basis E
  let T := 𝓞 E →+* ℂ
  have hcard : Fintype.card Ix = Fintype.card (E →ₐ[ℚ] ℂ) := by
    rw [AlgHom.card, ← RingOfIntegers.rank, Module.finrank_eq_card_chooseBasisIndex]
  let e₁ : Ix ≃ (E →ₐ[ℚ] ℂ) := Fintype.equivOfCardEq hcard
  let e₂ : Ix ≃ T := (e₁.trans (RingHom.equivRatAlgHom (R := E) (S := ℂ)).symm).trans (resEquiv E)
  let N : Matrix Ix Ix ℂ := Algebra.embeddingsMatrixReindex ℚ ℂ (integralBasis E) e₁
  have hN : N.det ≠ 0 := by
    intro h
    have h1 := Algebra.discr_eq_det_embeddingsMatrixReindex_pow_two ℚ ℂ (integralBasis E) e₁
    have h2 := Algebra.discr_not_zero_of_basis ℚ (integralBasis E)
    apply h2
    have : algebraMap ℚ ℂ (Algebra.discr ℚ (integralBasis E)) = 0 := by
      rw [h1]; show N.det ^ 2 = 0; rw [h]; simp
    simpa using this
  let A : Matrix T Ix ℂ := Matrix.of fun σ a => σ (b a)
  have hA : A = Nᵀ.submatrix e₂.symm (Equiv.refl Ix) := by
    ext σ a
    obtain ⟨j, rfl⟩ := e₂.surjective σ
    simp only [A, Matrix.of_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.transpose_apply, N,
      Algebra.embeddingsMatrixReindex, Algebra.embeddingsMatrix, Matrix.reindex_apply, Equiv.refl_apply,
      Equiv.refl_symm, Equiv.symm_symm]
    simp [e₂, resEquiv, b, integralBasis_apply]
    rfl
  have hNu : IsUnit Nᵀ.det := by
    rw [Matrix.det_transpose]; exact isUnit_iff_ne_zero.2 hN
  let B : Matrix Ix T ℂ := (Nᵀ)⁻¹.submatrix (Equiv.refl Ix) e₂.symm
  have hAB : A * B = 1 := by
    rw [hA, Matrix.submatrix_mul_equiv, Matrix.mul_nonsing_inv _ hNu, Matrix.submatrix_one_equiv]
  have hBA : B * A = 1 := (Matrix.mul_eq_one_comm_of_equiv e₂.symm).1 hAB
  have hAB' : ∀ σ τ, ∑ a, B a τ * σ (b a) = (1 : Matrix T T ℂ) σ τ := fun σ τ => by
    rw [← hAB, Matrix.mul_apply]
    exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  have hBA' : ∀ a c, ∑ τ : T, B a τ * τ (b c) = (1 : Matrix Ix Ix ℂ) a c := fun a c => by
    rw [← hBA, Matrix.mul_apply]
    rfl
  have hcc : ∀ τ : T, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := fun τ => by
    ext x; simp
  let cj : T ≃ T := ⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩
  let B' : Matrix Ix T ℂ := Matrix.of fun a τ => starRingEnd ℂ (B a (cj τ))
  have hAB2 : A * B' = 1 := by
    ext σ τ
    have h1 := congrArg (starRingEnd ℂ) (hAB' (cj σ) (cj τ))
    have h2 : (1 : Matrix T T ℂ) (cj σ) (cj τ) = (1 : Matrix T T ℂ) σ τ := by
      simp [Matrix.one_apply, cj.injective.eq_iff]
    rw [h2, map_sum] at h1
    rw [Matrix.mul_apply]
    have h3 : starRingEnd ℂ ((1 : Matrix T T ℂ) σ τ) = (1 : Matrix T T ℂ) σ τ := by
      by_cases h : σ = τ <;> simp [Matrix.one_apply, h]
    rw [h3] at h1
    rw [← h1]
    refine Finset.sum_congr rfl fun a _ => ?_
    simp only [A, B', Matrix.of_apply, map_mul]
    have : starRingEnd ℂ ((cj σ) (b a)) = σ (b a) := by
      show starRingEnd ℂ (starRingEnd ℂ (σ (b a))) = _
      simp
    rw [this, mul_comm]
  have hB' : B' = B := by
    calc B' = (B * A) * B' := by rw [hBA, Matrix.one_mul]
      _ = B * (A * B') := Matrix.mul_assoc _ _ _
      _ = B := by rw [hAB2, Matrix.mul_one]
  refine ⟨Ix, inferInstance, fun a => b a, fun τ a => B a τ, fun a => b.repr 1 a, ?_, ?_, ?_, ?_, ?_⟩
  · intro τ
    rw [hAB' τ τ]; simp
  · intro σ τ h
    rw [hAB' σ τ]; simp [Matrix.one_apply, h]
  · intro τ a
    have := congrFun (congrFun hB' a) (cj τ)
    simp only [B', Matrix.of_apply] at this
    have h2 : cj (cj τ) = τ := hcc τ
    rw [h2] at this
    exact this
  · exact b.sum_repr 1
  · intro a
    have h1 : ∀ τ : T, (1 : ℂ) = ∑ c, (b.repr 1 c : ℂ) * τ (b c) := fun τ => by
      have := congrArg τ (b.sum_repr 1)
      simpa using this.symm
    calc ∑ τ : T, B a τ = ∑ τ : T, B a τ * ∑ c, (b.repr 1 c : ℂ) * τ (b c) :=
          Finset.sum_congr rfl fun τ _ => by rw [← h1 τ, _root_.mul_one]
      _ = ∑ c, (b.repr 1 c : ℂ) * ∑ τ : T, B a τ * τ (b c) := by
          simp only [Finset.mul_sum]
          rw [Finset.sum_comm]
          exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun τ _ => by ring
      _ = (b.repr 1 a : ℂ) := by
          simp only [hBA', Matrix.one_apply]
          simp

/- English proof (translation)
Use `⟨{ inner := fun x y => ∑ τ, core.inner (P τ x) (P τ y) conj_inner_symm := ?_ re_inner_nonneg := ?_ add_left := ?_ smul_left := ?_ definite := ?_ }, fun _ _ => rfl⟩` and prove the remaining obligations. Introduce `x y`. Simplify using `only [map_sum]`. Conclude with `Finset.sum_congr rfl fun τ _ => core.conj_inner_symm _ _`. Introduce `x`.

Simplify using `only [map_sum]`. Conclude with `Finset.sum_nonneg fun τ _ => core.re_inner_nonneg _`. Introduce `x y z`. Simplify using `only [map_add, core.add_left, Finset.sum_add_distrib]`. Introduce `x y r`.

Simplify using `only [map_smul, core.smul_left, Finset.mul_sum]`. Introduce `x hx`. Establish `h1 : ∑ τ, RCLike.re (core.inner (P τ x) (P τ x)) = 0`. Use `congrArg RCLike.re hx` as an intermediate fact. Simplify `this` using `only [map_sum, map_zero]`.

Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg fun τ _ => core.re_inner_nonneg (P τ x)).1 h1`. Establish `h3 : ∀ τ, P τ x = 0`. Introduce `τ`. Apply `core.definite` to reduce the goal to its premises. Establish `hc` using `core.conj_inner_symm (P τ x) (P τ x)`.

Apply `Complex.ext` to reduce the goal to its premises. Simplify using `using h2 τ (Finset.mem_univ _)`. Use `congrArg Complex.im hc` as an intermediate fact. Simplify using `at this`. Simplify using the standard rewrite rules.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: x = ∑ τ, P τ x`. Use `congrArg (fun f : V →ₗ[ℂ] V => f x) hP` as an intermediate fact. Simplify `this.symm` using `[LinearMap.sum_apply]`. Rewrite using `[this]`.

Conclude with `Finset.sum_eq_zero fun τ _ => h3 τ`.
-/
theorem core_sum {V : Type} [AddCommGroup V] [Module ℂ V] {T : Type} [Fintype T] (core : InnerProductSpace.Core ℂ V)
    (P : T → V →ₗ[ℂ] V) (hP : ∑ τ, P τ = 1) :
    ∃ core' : InnerProductSpace.Core ℂ V, ∀ x y, core'.inner x y = ∑ τ, core.inner (P τ x) (P τ y) := by
  refine ⟨{ inner := fun x y => ∑ τ, core.inner (P τ x) (P τ y)
            conj_inner_symm := ?_
            re_inner_nonneg := ?_
            add_left := ?_
            smul_left := ?_
            definite := ?_ }, fun _ _ => rfl⟩
  · intro x y
    simp only [map_sum]
    exact Finset.sum_congr rfl fun τ _ => core.conj_inner_symm _ _
  · intro x
    simp only [map_sum]
    exact Finset.sum_nonneg fun τ _ => core.re_inner_nonneg _
  · intro x y z
    simp only [map_add, core.add_left, Finset.sum_add_distrib]
  · intro x y r
    simp only [map_smul, core.smul_left, Finset.mul_sum]
  · intro x hx
    have h1 : ∑ τ, RCLike.re (core.inner (P τ x) (P τ x)) = 0 := by
      have := congrArg RCLike.re hx
      simpa only [map_sum, map_zero] using this
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun τ _ => core.re_inner_nonneg (P τ x)).1 h1
    have h3 : ∀ τ, P τ x = 0 := by
      intro τ
      apply core.definite
      have hc := core.conj_inner_symm (P τ x) (P τ x)
      apply Complex.ext
      · simpa using h2 τ (Finset.mem_univ _)
      · have := congrArg Complex.im hc
        simp at this
        simp
        linarith
    have : x = ∑ τ, P τ x := by
      have := congrArg (fun f : V →ₗ[ℂ] V => f x) hP
      simpa [LinearMap.sum_apply] using this.symm
    rw [this]
    exact Finset.sum_eq_zero fun τ _ => h3 τ

/- English proof (translation)
Establish `h` using `core.smul_left 0 y 0`. Simplify using `using h`.
-/
theorem core_zero_left {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (y : V) :
    core.inner 0 y = 0 := by
  have h := core.smul_left 0 y 0
  simpa using h

/- English proof (translation)
Rewrite using `[← core.conj_inner_symm, core_zero_left, map_zero]`.
-/
theorem core_zero_right {V : Type} [AddCommGroup V] [Module ℂ V] (core : InnerProductSpace.Core ℂ V) (x : V) :
    core.inner x 0 = 0 := by
  rw [← core.conj_inner_symm, core_zero_left, map_zero]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using core_zero_left core y`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]`.
-/
theorem core_sum_left {V : Type} [AddCommGroup V] [Module ℂ V] {Ix : Type} (core : InnerProductSpace.Core ℂ V)
    (s : Finset Ix) (f : Ix → ℂ) (u : Ix → V) (y : V) :
    core.inner (∑ a ∈ s, f a • u a) y = ∑ a ∈ s, starRingEnd ℂ (f a) * core.inner (u a) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using core_zero_left core y
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha, core.add_left, core.smul_left, ih]

/- English proof (translation)
Rewrite using `[core_sum_left]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← core.conj_inner_symm, core_sum_left, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, Complex.conj_conj, core.conj_inner_symm]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem core_expand {V : Type} [AddCommGroup V] [Module ℂ V] {Ix : Type} [Fintype Ix]
    (core : InnerProductSpace.Core ℂ V) (f g : Ix → ℂ) (u w : Ix → V) :
    core.inner (∑ a, f a • u a) (∑ b, g b • w b) =
      ∑ a, ∑ b, starRingEnd ℂ (f a) * g b * core.inner (u a) (w b) := by
  rw [core_sum_left]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [← core.conj_inner_symm, core_sum_left, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun b _ => ?_
  rw [map_mul, Complex.conj_conj, core.conj_inner_symm]
  ring

section Geo

open AlgebraicGeometry CategoryTheory

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {G : Over X} [GrpObj G] {ξ : Sp Ω ⟶ X}
  {Li : Type} [AddCommGroup Li] [Module Ω Li]

/- English proof (translation)
Take `⟨hs, v, ⟨ht, hv⟩, hw⟩` from `h`. Use `haveI := act.hom r`. Use `⟨hs, v ≫ act.act r, ⟨ht.comp_monHom _, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hρ r e, Over.comp_left, hv, Over.comp_left]`. Conclude with `Category.assoc _ _ _`.

Rewrite using `[Over.comp_left, hw, Over.comp_left]`. Conclude with `Category.assoc _ _ _`.
-/
theorem valAt_act (M : LieModel G ξ Li) {O : Type} [CommRing O] (act : OAct O G) (ρ : O →+* Module.End Ω Li)
    (hρ : M.IsActOf act.act ρ) (z : Sp ℂ ⟶ X) (r : O) {e : Li} {w : epsAt z ⟶ G} (h : M.ValAt z e w) :
    M.ValAt z (ρ r e) (w ≫ act.act r) := by
  obtain ⟨hs, v, ⟨ht, hv⟩, hw⟩ := h
  haveI := act.hom r
  refine ⟨hs, v ≫ act.act r, ⟨ht.comp_monHom _, ?_⟩, ?_⟩
  · rw [hρ r e, Over.comp_left, hv, Over.comp_left]
    exact Category.assoc _ _ _
  · rw [Over.comp_left, hw, Over.comp_left]
    exact Category.assoc _ _ _

/- English proof (translation)
Apply `Mz.inj` to reduce the goal to its premises. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[Mz.smul, hρz r x]`. Conclude with `h.2 r`.
-/
theorem eig_act {V : Type} [AddCommGroup V] [Module ℂ V] {z : Sp ℂ ⟶ X} (Mz : LieModel G z V) {O : Type} [CommRing O]
    (act : OAct O G) (ρz : O →+* Module.End ℂ V) (hρz : Mz.IsActOf act.act ρz) {τ : O →+* ℂ} {x : V}
    (h : IsLieEigen act z τ (Mz.pt x)) (r : O) : ρz r x = τ r • x := by
  apply Mz.inj
  apply Over.OverMorphism.ext
  rw [Mz.smul, hρz r x]
  exact h.2 r

/- English proof (translation)
Take `⟨Ix, _, α, d, m, hd1, hd0, hdc, hm1, hm2⟩` from `exists_coeff E`. Set `c : Ix → Ix → ℂ` to `fun a b => ∑ τ, starRingEnd ℂ (d τ a) * d τ b`. Establish `hcc : ∀ τ : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ` using `fun τ => by`. Use extensionality with `x`. Simplify using the standard rewrite rules.

Set `cj : (𝓞 E →+* ℂ) ≃ (𝓞 E →+* ℂ)` to `⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩`. Establish `hc : ∀ a b, starRingEnd ℂ (c a b) = c a b`. Introduce `a b`. Simplify using `only [c, map_sum, map_mul, Complex.conj_conj]`. Use `Fintype.sum_equiv cj _ _ fun τ => ?_` and prove the remaining obligations.

Use `show d τ a * starRingEnd ℂ (d τ b) = starRingEnd ℂ (d (cj τ) a) * d (cj τ) b`. Establish `h1 : d (cj τ) a = starRingEnd ℂ (d τ a)` using `(hdc τ a).symm`. Establish `h2 : d (cj τ) b = starRingEnd ℂ (d τ b)` using `(hdc τ b).symm`. Rewrite using `[h1, h2, Complex.conj_conj]`. Set `ip' : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ` to `fun z v w => ∑ a, ∑ b, c a b * h₀.ip z (v ≫ act.act (α a)) (w ≫ act.act (α b))`.

Establish `hsum : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρz : 𝓞 E →+* Module.End ℂ V), ∑ τ, ∑ a, d τ a • ρz (α a) = 1`. Introduce `V _ _ ρz`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, hm2, Int.cast_smul_eq_zsmul]`. Rewrite using `[← map_one ρz, ← hm1, map_sum]`.

Simplify using `only [map_zsmul]`. Establish `key : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V) (ρz : 𝓞 E →+* Module.End ℂ V), Mz.IsActOf act.act ρz → ∀ core : InnerProductSpace.Core ℂ V, (∀ a b, core.inner a b = h₀.ip z (Mz.pt a) (Mz.pt b)) → ∀ x x', ip' z (Mz.pt x) (Mz.pt x') = ∑ τ, core …`. Introduce `z V _ _ Mz ρz hρz core hcore x x'`. Establish `h1 : ∀ τ, core.inner ((∑ a, d τ a • ρz (α a)) x) ((∑ a, d τ a • ρz (α a)) x') = ∑ a, ∑ b, starRingEnd ℂ (d τ a) * d τ b * core.inner (ρz (α a) x) (ρz (α b) x')`. Introduce `τ`.

Rewrite using `[← core_expand]`. Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply]`. Simplify using `only [h1]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[hcore, hρz (α a) x, hρz (α b) x', ← Finset.sum_mul]`. Use `⟨{ ip := ip', herm := ?_, conj := ?_, cont := ?_ }, ?_⟩` and prove the remaining obligations. Introduce `z V _ _ Mz`.

Take `⟨ρz, hρz, -⟩` from `lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add`. Take `⟨core, hcore⟩` from `h₀.herm z V Mz`. Take `⟨core', h'⟩` from `core_sum core (fun τ => ∑ a, d τ a • ρz (α a)) (hsum ρz)`. Conclude with `⟨core', fun a b => (h' a b).trans (key z V Mz ρz hρz core hcore a b).symm⟩`. Introduce `z v w v' w' hv hw show ip' _ v' w' = starRingEnd ℂ (ip' z v w)`.

Simplify using `only [ip', map_sum, map_mul, hc]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use `congr 1`. Conclude with `h₀.conj z _ _ _ _ (by rw [Over.comp_left, hv, Over.comp_left, Category.assoc]) (by rw [Over.comp_left, hw, Over.comp_left, Category.assoc])`. Introduce `a b choose F hF1 hF2 using fun i j => h₀.cont (ρ (α i) a) (ρ (α j) b)`.

Use `⟨fun w => ∑ i, ∑ j, c i j * F i j w, ?_, ?_⟩` and prove the remaining obligations. Use `continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ => continuousOn_const.mul ((hF1 i j).mono ?_)` and prove the remaining obligations. Introduce and unpack `w ⟨z, va, vb, hw, ha, hb⟩`. Conclude with `⟨z, va ≫ act.act (α i), vb ≫ act.act (α j), hw, valAt_act M act ρ hρ z _ ha, valAt_act M act ρ hρ z _ hb⟩`. Introduce `z w va vb hw ha hb`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hF2 i j z w _ _ hw (valAt_act M act ρ hρ z _ ha) (valAt_act M act ρ hρ z _ hb)]`. Introduce `z τ τ' v w hne hv hw`. Take `⟨V, _, _, ⟨Mz⟩⟩` from `lieModel_exists X G ℂ z`. Take `⟨ρz, hρz, -⟩` from `lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add`.

Take `⟨core, hcore⟩` from `h₀.herm z V Mz`. Take `⟨x, rfl⟩` from `Mz.onto v hv.1`. Take `⟨x', rfl⟩` from `Mz.onto w hw.1`. Establish `hP : ∀ (σ υ : 𝓞 E →+* ℂ) (u : V), IsLieEigen act z υ (Mz.pt u) → σ ≠ υ → (∑ a, d σ a • ρz (α a)) u = 0`. Introduce `σ υ u hu hne'`.

Simplify using `only [LinearMap.sum_apply, LinearMap.smul_apply, eig_act Mz act ρz hρz hu, smul_smul]`. Rewrite using `[← Finset.sum_smul, hd0 υ σ hne'.symm, zero_smul]`. Use `show ip' z _ _ = 0`. Rewrite using `[key z V Mz ρz hρz core hcore x x']`. Use `Finset.sum_eq_zero fun σ _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hσ : σ = τ`. Rewrite using `[hP σ τ' x' hw (hσ ▸ hne), core_zero_right]`. Rewrite using `[hP σ τ x hv hσ, core_zero_left]`.
-/
theorem exists_orth (E : Type) [Field E] [NumberField E] [IsCommMonObj G] {K : Type} {J : K → Type}
    {y : (Σ k, J k) → Ω} (M : LieModel G ξ Li) (act : OAct (𝓞 E) G) (ρ : 𝓞 E →+* Module.End Ω Li)
    (hρ : M.IsActOf act.act ρ) (h₀ : LieMetric M y) : ∃ h : LieMetric M y, h.Orth act := by
  obtain ⟨Ix, _, α, d, m, hd1, hd0, hdc, hm1, hm2⟩ := exists_coeff E
  let c : Ix → Ix → ℂ := fun a b => ∑ τ, starRingEnd ℂ (d τ a) * d τ b
  have hcc : ∀ τ : 𝓞 E →+* ℂ, (starRingEnd ℂ).comp ((starRingEnd ℂ).comp τ) = τ := fun τ => by
    ext x; simp
  let cj : (𝓞 E →+* ℂ) ≃ (𝓞 E →+* ℂ) := ⟨fun τ => (starRingEnd ℂ).comp τ, fun τ => (starRingEnd ℂ).comp τ, hcc, hcc⟩
  have hc : ∀ a b, starRingEnd ℂ (c a b) = c a b := by
    intro a b
    simp only [c, map_sum, map_mul, Complex.conj_conj]
    refine Fintype.sum_equiv cj _ _ fun τ => ?_
    show d τ a * starRingEnd ℂ (d τ b) = starRingEnd ℂ (d (cj τ) a) * d (cj τ) b
    have h1 : d (cj τ) a = starRingEnd ℂ (d τ a) := (hdc τ a).symm
    have h2 : d (cj τ) b = starRingEnd ℂ (d τ b) := (hdc τ b).symm
    rw [h1, h2, Complex.conj_conj]
  let ip' : ∀ z : Sp ℂ ⟶ X, (epsAt z ⟶ G) → (epsAt z ⟶ G) → ℂ := fun z v w =>
    ∑ a, ∑ b, c a b * h₀.ip z (v ≫ act.act (α a)) (w ≫ act.act (α b))
  have hsum : ∀ {V : Type} [AddCommGroup V] [Module ℂ V] (ρz : 𝓞 E →+* Module.End ℂ V),
      ∑ τ, ∑ a, d τ a • ρz (α a) = 1 := by
    intro V _ _ ρz
    rw [Finset.sum_comm]
    simp only [← Finset.sum_smul, hm2, Int.cast_smul_eq_zsmul]
    rw [← map_one ρz, ← hm1, map_sum]
    simp only [map_zsmul]
  have key : ∀ (z : Sp ℂ ⟶ X) (V : Type) [AddCommGroup V] [Module ℂ V] (Mz : LieModel G z V)
      (ρz : 𝓞 E →+* Module.End ℂ V), Mz.IsActOf act.act ρz → ∀ core : InnerProductSpace.Core ℂ V,
      (∀ a b, core.inner a b = h₀.ip z (Mz.pt a) (Mz.pt b)) → ∀ x x',
      ip' z (Mz.pt x) (Mz.pt x') =
        ∑ τ, core.inner ((∑ a, d τ a • ρz (α a)) x) ((∑ a, d τ a • ρz (α a)) x') := by
    intro z V _ _ Mz ρz hρz core hcore x x'
    have h1 : ∀ τ, core.inner ((∑ a, d τ a • ρz (α a)) x) ((∑ a, d τ a • ρz (α a)) x') =
        ∑ a, ∑ b, starRingEnd ℂ (d τ a) * d τ b * core.inner (ρz (α a) x) (ρz (α b) x') := by
      intro τ
      rw [← core_expand]
      simp only [LinearMap.sum_apply, LinearMap.smul_apply]
    simp only [h1]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [hcore, hρz (α a) x, hρz (α b) x', ← Finset.sum_mul]
  refine ⟨{ ip := ip', herm := ?_, conj := ?_, cont := ?_ }, ?_⟩
  · intro z V _ _ Mz
    obtain ⟨ρz, hρz, -⟩ := lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add
    obtain ⟨core, hcore⟩ := h₀.herm z V Mz
    obtain ⟨core', h'⟩ := core_sum core (fun τ => ∑ a, d τ a • ρz (α a)) (hsum ρz)
    exact ⟨core', fun a b => (h' a b).trans (key z V Mz ρz hρz core hcore a b).symm⟩
  · intro z v w v' w' hv hw
    show ip' _ v' w' = starRingEnd ℂ (ip' z v w)
    simp only [ip', map_sum, map_mul, hc]
    refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun b _ => ?_
    congr 1
    exact h₀.conj z _ _ _ _ (by rw [Over.comp_left, hv, Over.comp_left, Category.assoc])
      (by rw [Over.comp_left, hw, Over.comp_left, Category.assoc])
  · intro a b
    choose F hF1 hF2 using fun i j => h₀.cont (ρ (α i) a) (ρ (α j) b)
    refine ⟨fun w => ∑ i, ∑ j, c i j * F i j w, ?_, ?_⟩
    · refine continuousOn_finset_sum _ fun i _ => continuousOn_finset_sum _ fun j _ =>
        continuousOn_const.mul ((hF1 i j).mono ?_)
      rintro w ⟨z, va, vb, hw, ha, hb⟩
      exact ⟨z, va ≫ act.act (α i), vb ≫ act.act (α j), hw, valAt_act M act ρ hρ z _ ha,
        valAt_act M act ρ hρ z _ hb⟩
    · intro z w va vb hw ha hb
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      rw [hF2 i j z w _ _ hw (valAt_act M act ρ hρ z _ ha) (valAt_act M act ρ hρ z _ hb)]
  · intro z τ τ' v w hne hv hw
    obtain ⟨V, _, _, ⟨Mz⟩⟩ := lieModel_exists X G ℂ z
    obtain ⟨ρz, hρz, -⟩ := lieModel_exists_unique_act X G ℂ z V Mz (𝓞 E) act.act act.hom act.one act.mul act.add
    obtain ⟨core, hcore⟩ := h₀.herm z V Mz
    obtain ⟨x, rfl⟩ := Mz.onto v hv.1
    obtain ⟨x', rfl⟩ := Mz.onto w hw.1
    have hP : ∀ (σ υ : 𝓞 E →+* ℂ) (u : V), IsLieEigen act z υ (Mz.pt u) → σ ≠ υ →
        (∑ a, d σ a • ρz (α a)) u = 0 := by
      intro σ υ u hu hne'
      simp only [LinearMap.sum_apply, LinearMap.smul_apply, eig_act Mz act ρz hρz hu, smul_smul]
      rw [← Finset.sum_smul, hd0 υ σ hne'.symm, zero_smul]
    show ip' z _ _ = 0
    rw [key z V Mz ρz hρz core hcore x x']
    refine Finset.sum_eq_zero fun σ _ => ?_
    by_cases hσ : σ = τ
    · rw [hP σ τ' x' hw (hσ ▸ hne), core_zero_right]
    · rw [hP σ τ x hv hσ, core_zero_left]

end Geo

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐`. Use `haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth`. Establish `hch : CharZero Ω` using `(RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance`. Take `⟨h₀⟩` from `GlobalTheory.T.exists_lie_metric 𝔐.X Ω K J y 𝔐.ξ hch 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.Li 𝔐.M`. Conclude with `exists_orth E 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act h₀`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l) (c : Coeff l) (Y : Model Xo c (algebraMap (𝓞 c.F) c.F)) (S : Finset ℕ) (Ω : Type) [Field Ω] (K : Type) [Fintype K] (J : K → Type) [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (𝔐 : HodgeCpt Y S y), ∃ h : LieMetric 𝔐.M y, h.Orth 𝔐.t.act := by
  intro E _ _ _ H D l Xo c Y S Ω _ K _ J _ y 𝔐
  haveI : Smooth 𝔐.t.G.hom := 𝔐.t.semi.smooth
  have hch : CharZero Ω := (RingHom.charZero_iff 𝔐.cst.injective).1 inferInstance
  obtain ⟨h₀⟩ := GlobalTheory.T.exists_lie_metric 𝔐.X Ω K J y 𝔐.ξ hch 𝔐.all 𝔐.tie 𝔐.t.G 𝔐.Li 𝔐.M
  exact exists_orth E 𝔐.M 𝔐.t.act 𝔐.ρ 𝔐.act h₀

end GlobalTheory.CompanionTheory.Ar.MetricOrth
