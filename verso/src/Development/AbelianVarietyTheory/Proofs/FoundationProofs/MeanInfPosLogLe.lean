import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

namespace GlobalTheory.ArchMean

/- English proof (translation)
Use `haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M`. Use `haveI : CharZero K := algebraRat.charZero K`. Rewrite using `[← Finset.sum_fiberwise (s := Finset.univ) (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => F φ) (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]`.

Use `congr 2`. Use `letI : Algebra K ℂ := φ.toRingHom.toAlgebra`. Use `haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm`. Rewrite using `[← AlgHom.card K M ℂ, ← Finset.card_univ]`. Use `symm`.

Use `Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_` and prove the remaining obligations. Introduce `ψ _`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use extensionality with `a`. Conclude with `ψ.commutes a`.

Introduce `a _ b _ h`. Conclude with `AlgHom.restrictScalars_injective ℚ h`. Introduce `ρ hρ`. Establish `h` using `(Finset.mem_filter.1 hρ).2`. Conclude with `⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a }, Finset.mem_univ _, rfl⟩`.
-/
theorem sum_comp_algHom (K M : Type) [Field K] [Field M] [Algebra ℚ K] [Algebra ℚ M] [Algebra K M]
    [IsScalarTower ℚ K M] [FiniteDimensional ℚ K] [FiniteDimensional ℚ M]
    (F : (K →ₐ[ℚ] ℂ) → ℝ) :
    ∑ ρ : M →ₐ[ℚ] ℂ, F (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) =
      (Module.finrank K M : ℝ) * ∑ φ : K →ₐ[ℚ] ℂ, F φ := by
  haveI : FiniteDimensional K M := FiniteDimensional.right ℚ K M
  haveI : CharZero K := algebraRat.charZero K
  rw [← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun ρ : M →ₐ[ℚ] ℂ => ρ.comp (IsScalarTower.toAlgHom ℚ K M)), Finset.mul_sum]
  refine Finset.sum_congr rfl fun φ _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => F φ)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 2
  letI : Algebra K ℂ := φ.toRingHom.toAlgebra
  haveI : IsScalarTower ℚ K ℂ := IsScalarTower.of_algebraMap_eq fun q => (φ.commutes q).symm
  rw [← AlgHom.card K M ℂ, ← Finset.card_univ]
  symm
  refine Finset.card_bij (fun ψ _ => ψ.restrictScalars ℚ) ?_ ?_ ?_
  · intro ψ _
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    ext a
    exact ψ.commutes a
  · intro a _ b _ h
    exact AlgHom.restrictScalars_injective ℚ h
  · intro ρ hρ
    have h := (Finset.mem_filter.1 hρ).2
    exact ⟨{ ρ.toRingHom with commutes' := fun a => DFunLike.congr_fun h a },
      Finset.mem_univ _, rfl⟩

/- English proof (translation)
Establish `h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ)` using `Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl`. Rewrite using `[h1, ← Finset.sum_fiberwise (s := Finset.univ) (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl (g := fun _ => f v) (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]`. Use `congr 1`.

Use `InfinitePlace.card_filter_mk_eq v` as an intermediate fact. Rewrite `this` using `[IsTotallyComplex.mult_eq]`. Conclude with `this` after adjusting the coercions.
-/
theorem sum_algHom_eq (K : Type) [Field K] [NumberField K] [IsTotallyComplex K]
    (f : InfinitePlace K → ℝ) :
    ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom) = 2 * ∑ v, f v := by
  have h1 : ∑ φ : K →ₐ[ℚ] ℂ, f (InfinitePlace.mk φ.toRingHom)
      = ∑ φ : K →+* ℂ, f (InfinitePlace.mk φ) :=
    Fintype.sum_equiv (RingHom.equivRatAlgHom (R := K) (S := ℂ)).symm _ _ fun _ => rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ)
    (g := fun φ : K →+* ℂ => InfinitePlace.mk φ), Finset.mul_sum]
  refine Finset.sum_congr rfl fun v _ => ?_
  rw [Finset.sum_congr rfl (g := fun _ => f v)
    (fun ρ hρ => by rw [(Finset.mem_filter.1 hρ).2]), Finset.sum_const, nsmul_eq_mul]
  congr 1
  have := InfinitePlace.card_filter_mk_eq v
  rw [IsTotallyComplex.mult_eq] at this
  exact_mod_cast this

/- English proof (translation)
Establish `hw' : ∀ i, (0 : ℝ) ≤ w i` using `fun i => by exact_mod_cast hw i`. Establish `h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤ ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖)`. Use `(norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))` and prove the remaining obligations. Establish `h` using `Real.mul_self_sqrt (hw' i)`. Rewrite using `[norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]`.

Take the linear combination `(-(‖a i‖ * ‖b i‖)) * h`. Establish `h2` using `Finset.sum_mul_sq_le_sq_mul_sq Finset.univ (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)`. Simplify using `only [mul_pow, Real.sq_sqrt (hw' _)] at h2`. Establish `h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤ (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2` using `(pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2`. Establish `h4` using `(Real.posLog_le_posLog (by positivity) h3).trans Real.posLog_mul`.

Rewrite `h4` using `[Real.posLog_pow]`. Move the coercions through the operations in `at h4`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem posLog_sum_le {ι : Type} [Fintype ι] (w : ι → ℚ) (hw : ∀ i, 0 ≤ w i) (a b : ι → ℂ) :
    Real.posLog ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      (Real.posLog (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) + Real.posLog (∑ i, (w i : ℝ) * ‖b i‖ ^ 2)) / 2 := by
  have hw' : ∀ i, (0 : ℝ) ≤ w i := fun i => by exact_mod_cast hw i
  have h1 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ≤
      ∑ i, (Real.sqrt (w i) * ‖a i‖) * (Real.sqrt (w i) * ‖b i‖) := by
    refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun i _ => ?_))
    have h := Real.mul_self_sqrt (hw' i)
    rw [norm_mul, norm_mul, Complex.norm_ratCast, abs_of_nonneg (hw' i)]
    linear_combination (-(‖a i‖ * ‖b i‖)) * h
  have h2 := Finset.sum_mul_sq_le_sq_mul_sq Finset.univ
    (fun i => Real.sqrt (w i) * ‖a i‖) (fun i => Real.sqrt (w i) * ‖b i‖)
  simp only [mul_pow, Real.sq_sqrt (hw' _)] at h2
  have h3 : ‖∑ i, (w i : ℂ) * (a i * b i)‖ ^ 2 ≤
      (∑ i, (w i : ℝ) * ‖a i‖ ^ 2) * ∑ i, (w i : ℝ) * ‖b i‖ ^ 2 :=
    (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
  have h4 := (Real.posLog_le_posLog (by positivity) h3).trans Real.posLog_mul
  rw [Real.posLog_pow] at h4
  push_cast at h4
  linarith

/- English proof (translation)
Introduce `K _ _ _ σ x M _ _ ι _ w z hσ hw hx`. Set `σ' : K →+* M` to `σ.codRestrict M hσ`. Use `letI : Algebra K M := σ'.toAlgebra`. Use `haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)`. Set `j : M →ₐ[ℚ] ℂ` to `((starRingEnd ℂ).toRatAlgHom).comp M.val`.

Establish `hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M` using `fun y => by`. Establish `: j y ∈ j.fieldRange` using `⟨y, rfl⟩`. Conclude with `(@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this`. Set `c : M →ₐ[ℚ] M` to `(j.toRingHom.codRestrict M hj).toRatAlgHom`. Establish `hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ)` using `fun _ => rfl`.

Establish `hcc : ∀ y, c (c y) = y` using `fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])`. Establish `hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i))`. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `σ x = M.val _`. Rewrite using `[hx, map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_ratCast]`. Both sides reduce to the same expression. Use `set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA`. Establish `hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c)` using `fun ρ => by`.

Use extensionality with `y`. Simplify using `[hcc]`. Establish `hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ` using `Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl`. Establish `h1` using `sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)`. Establish `h2` using `sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)`.

Establish `h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ = 2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖`. Rewrite using `[← h2]`. Use `Finset.sum_congr rfl fun φ _ => ?_` and prove the remaining obligations. Rewrite using `[InfinitePlace.norm_embedding_eq, InfinitePlace.apply]`. Both sides reduce to the same expression.

Establish `h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖ ≤ ∑ ρ, A ρ`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum fun ρ _ => ?_` and prove the remaining obligations. Establish `: (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i)))`. Express the relevant statement in the definitionally equal form `ρ (algebraMap K M x) = _`.

Rewrite using `[hxM, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_ratCast]`. Rewrite using `[this]`. Conclude with `posLog_sum_le w hw _ _`.

Use `_ = ∑ ρ, A ρ := by`. Rewrite using `[← Finset.sum_div, Finset.sum_add_distrib, hsum]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h4` using `[h1, h3]`. Establish `hK : (0 : ℝ) < Module.finrank ℚ K` using `by exact_mod_cast Module.finrank_pos`.

Establish `hM : (0 : ℝ) < Module.finrank ℚ M` using `by exact_mod_cast Module.finrank_pos`. Establish `ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M`. Conclude with `Module.finrank_mul_finrank ℚ K M` after adjusting the coercions. Unfold `Formalism.PairingDivisionLocalBalance.meanInf`. Rewrite using `[le_div_iff₀ hM, ← ht]`.

Use `le_trans (le_of_eq ?_) h4` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts.
-/
theorem meanInf_posLog_le :
    ∀ (K : Type) [Field K] [NumberField K] [IsTotallyComplex K] (σ : K →+* ℂ) (x : K) (M : IntermediateField ℚ ℂ) [FiniteDimensional ℚ M] [IsGalois ℚ M] (ι : Type) [Fintype ι] (w : ι → ℚ) (z : ι → M), (∀ a, σ a ∈ M) → (∀ i, 0 ≤ w i) → σ x = ∑ i, (w i : ℂ) * ((z i : ℂ) * starRingEnd ℂ (z i : ℂ)) → Formalism.PairingDivisionLocalBalance.meanInf K (fun v => Real.posLog ‖v.embedding x‖) ≤ (∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2)) / (Module.finrank ℚ M : ℝ) := by
  intro K _ _ _ σ x M _ _ ι _ w z hσ hw hx
  let σ' : K →+* M := σ.codRestrict M hσ
  letI : Algebra K M := σ'.toAlgebra
  haveI : IsScalarTower ℚ K M := IsScalarTower.of_algebraMap_eq' (Subsingleton.elim _ _)
  let j : M →ₐ[ℚ] ℂ := ((starRingEnd ℂ).toRatAlgHom).comp M.val
  have hj : ∀ y : M, starRingEnd ℂ (y : ℂ) ∈ M := fun y => by
    have : j y ∈ j.fieldRange := ⟨y, rfl⟩
    exact (@AlgHom.fieldRange_of_normal ℚ ℂ _ _ _ M (IsGalois.to_normal (F := ℚ) (E := M)) j).le this
  let c : M →ₐ[ℚ] M := (j.toRingHom.codRestrict M hj).toRatAlgHom
  have hc : ∀ y : M, (c y : ℂ) = starRingEnd ℂ (y : ℂ) := fun _ => rfl
  have hcc : ∀ y, c (c y) = y := fun y => Subtype.ext (by rw [hc, hc, Complex.conj_conj])
  have hxM : algebraMap K M x = ∑ i, (w i : M) * (z i * c (z i)) := by
    apply Subtype.ext
    change σ x = M.val _
    rw [hx, map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_mul, map_mul, map_ratCast]
    rfl
  set A : (M →ₐ[ℚ] ℂ) → ℝ := fun ρ => Real.posLog (∑ i, (w i : ℝ) * ‖ρ (z i)‖ ^ 2) with hA
  have hinv : Function.Involutive (fun ρ : M →ₐ[ℚ] ℂ => ρ.comp c) := fun ρ => by
    ext y
    simp [hcc]
  have hsum : ∑ ρ : M →ₐ[ℚ] ℂ, A (ρ.comp c) = ∑ ρ, A ρ :=
    Fintype.sum_equiv hinv.toPerm _ _ fun _ => rfl
  have h1 := sum_comp_algHom K M (fun φ => Real.posLog ‖φ x‖)
  have h2 := sum_algHom_eq K (fun v => Real.posLog ‖v.embedding x‖)
  have h3 : ∑ φ : K →ₐ[ℚ] ℂ, Real.posLog ‖φ x‖ =
      2 * ∑ v : InfinitePlace K, Real.posLog ‖v.embedding x‖ := by
    rw [← h2]
    refine Finset.sum_congr rfl fun φ _ => ?_
    rw [InfinitePlace.norm_embedding_eq, InfinitePlace.apply]
    rfl
  have h4 : ∑ ρ : M →ₐ[ℚ] ℂ, Real.posLog ‖(ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x‖
      ≤ ∑ ρ, A ρ := by
    calc _ ≤ ∑ ρ : M →ₐ[ℚ] ℂ, (A ρ + A (ρ.comp c)) / 2 := by
          refine Finset.sum_le_sum fun ρ _ => ?_
          have : (ρ.comp (IsScalarTower.toAlgHom ℚ K M)) x
              = ∑ i, (w i : ℂ) * (ρ (z i) * ρ (c (z i))) := by
            change ρ (algebraMap K M x) = _
            rw [hxM, map_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [map_mul, map_mul, map_ratCast]
          rw [this]
          exact posLog_sum_le w hw _ _
      _ = ∑ ρ, A ρ := by
          rw [← Finset.sum_div, Finset.sum_add_distrib, hsum]; ring
  rw [h1, h3] at h4
  have hK : (0 : ℝ) < Module.finrank ℚ K := by exact_mod_cast Module.finrank_pos
  have hM : (0 : ℝ) < Module.finrank ℚ M := by exact_mod_cast Module.finrank_pos
  have ht : (Module.finrank ℚ K : ℝ) * Module.finrank K M = Module.finrank ℚ M := by
    exact_mod_cast Module.finrank_mul_finrank ℚ K M
  unfold Formalism.PairingDivisionLocalBalance.meanInf
  rw [le_div_iff₀ hM, ← ht]
  refine le_trans (le_of_eq ?_) h4
  field_simp

end GlobalTheory.ArchMean
