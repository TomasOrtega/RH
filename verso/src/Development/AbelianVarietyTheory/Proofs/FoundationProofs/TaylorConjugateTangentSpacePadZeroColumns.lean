import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.DifferentiableComb
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.TaylorCoeffConjugateSeries
open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.GalTheta
open scoped BigOperators

namespace GlobalTheory.ConjRestrict

/- English proof (translation)
Establish `h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α` using `by simp`. Establish `h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') = Finsupp.toMultiset (Finsupp.embDomain e α)`. Rewrite using `[← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]`. Establish `h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial`. Rewrite using `[← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp), Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]`.

Rewrite using `[coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3, List.map_map]`. Both sides reduce to the same expression.
-/
theorem coeff_taylorDir_embDomain {σ σ' W : Type*} [Fintype σ] [Fintype σ'] [NormedAddCommGroup W]
    [NormedSpace ℂ W] (e : σ ↪ σ') (u : σ' → W) {f : W → ℂ} (hf : AnalyticAt ℂ f 0) (α : σ →₀ ℕ) :
    MvPowerSeries.coeff α (taylorDir (fun i => u (e i)) f) =
      MvPowerSeries.coeff (Finsupp.embDomain e α) (taylorDir u f) := by
  have h1 : ((α.toMultiset.toList : List σ) : Multiset σ) = Finsupp.toMultiset α := by simp
  have h2 : ((α.toMultiset.toList.map e : List σ') : Multiset σ') =
      Finsupp.toMultiset (Finsupp.embDomain e α) := by
    rw [← Multiset.map_coe, h1, Finsupp.toMultiset_map, Finsupp.embDomain_eq_mapDomain]
  have h3 : ∏ i, ((Finsupp.embDomain e α) i).factorial = ∏ i, (α i).factorial := by
    rw [← Finsupp.prod_fintype (Finsupp.embDomain e α) (fun _ n => n.factorial) (by simp),
      Finsupp.prod_embDomain, Finsupp.prod_fintype _ _ (by simp)]
  rw [coeff_taylorDir_eq_lineDerivList _ hf h1, coeff_taylorDir_eq_lineDerivList _ hf h2, h3,
    List.map_map]
  rfl

def colEmb (D : D7) (N N' m : ℕ) :
    D.what₂.Tau × Fin N' × Fin N ↪ D.what₂.Tau × Fin N' × Fin (N + m) :=
  ⟨fun k => (k.1, k.2.1, Fin.castAdd m k.2.2), by
    rintro ⟨a, b, c⟩ ⟨a', b', c'⟩ h
    simp only [Prod.mk.injEq, Fin.castAdd_inj] at h
    simp [h]⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem colEmb_apply (D : D7) (N N' m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    colEmb D N N' m k = (k.1, k.2.1, Fin.castAdd m k.2.2) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `τ a i`. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[pad_left]`. Simplify using `[coordV, colEmb_apply]`. Rewrite using `[pad_right]`.

Establish `: Fin.natAdd N i ≠ Fin.castAdd m k.2.2`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Use `k.2.2.2` as an intermediate fact. Simplify using `at *`.

Use linear arithmetic over natural numbers and integers. Simplify using `[coordV, colEmb_apply, this]`.
-/
theorem pad_coordV (D : D7) {N N' : ℕ} (m : ℕ) (k : D.what₂.Tau × Fin N' × Fin N) :
    pad D m (coordV D k) = coordV D (colEmb D N N' m k) := by
  funext τ a i
  refine Fin.addCases (fun i => ?_) (fun i => ?_) i
  · rw [pad_left]; simp [coordV, colEmb_apply]
  · rw [pad_right]
    have : Fin.natAdd N i ≠ Fin.castAdd m k.2.2 := by
      intro h
      have := congrArg Fin.val h
      have := k.2.2.2
      simp at *
      omega
    simp [coordV, colEmb_apply, this]

/- English proof (translation)
Establish `han : AnalyticAt ℂ G 0` using `SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)`. Rewrite using `[ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]`. Establish `h` using `taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N'))) (coordV D) han`. Simplify using `only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h`. Rewrite using `[h]`.
-/
theorem taylor_pad (D : D7) {N N' : ℕ} (m : ℕ) {G : VC D (N + m) N' → ℂ} (hG : Differentiable ℂ G)
    (α : Mono D N N') :
    Formalism.MainNotions.TaylorLogMetric.taylor D (fun z : VC D N N' => G (pad D m z)) α =
      Formalism.MainNotions.TaylorLogMetric.taylor D G (Finsupp.embDomain (colEmb D N N' m) α) := by
  have han : AnalyticAt ℂ G 0 :=
    SCV.analyticAt_iff_eventually_differentiableAt.2 (Filter.Eventually.of_forall hG)
  rw [ConjSeries.taylor_eq_coeff, ConjSeries.taylor_eq_coeff, ← coeff_taylorDir_embDomain _ _ han]
  have h := taylorDir_comp_clm (LinearMap.toContinuousLinearMap (padL D m (N := N) (N' := N')))
    (coordV D) han
  simp only [LinearMap.coe_toContinuousLinearMap', padL_apply, pad_coordV] at h
  rw [h]

/- English proof (translation)
Rewrite using `[mono, Finsupp.prod_embDomain]`. Simplify using `[mono, colEmb_apply]`.
-/
theorem mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (α : Mono D N N') (z : VC D N N') :
    mono D (Finsupp.embDomain (colEmb D N N' m) α) (pad D m z) = mono D α z := by
  rw [mono, Finsupp.prod_embDomain]
  simp [mono, colEmb_apply]

/- English proof (translation)
Rewrite using `[Finsupp.mem_range_embDomain_iff]`. Introduce and unpack `⟨τ, a, i⟩ hk`. Use `revert hk`. Use `Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i` and prove the remaining obligations. Use `absurd (Finset.prod_eq_zero hk ?_) h` and prove the remaining obligations.

Establish `: β (τ, a, Fin.natAdd N i) ≠ 0` using `Finsupp.mem_support_iff.1 hk`. Simplify using `[this]`.
-/
theorem mem_range_of_mono_pad (D : D7) {N N' : ℕ} (m : ℕ) (β : Mono D (N + m) N') (z : VC D N N')
    (h : mono D β (pad D m z) ≠ 0) : β ∈ Set.range (Finsupp.embDomain (colEmb D N N' m)) := by
  rw [Finsupp.mem_range_embDomain_iff]
  rintro ⟨τ, a, i⟩ hk
  revert hk
  refine Fin.addCases (fun i _ => ⟨(τ, a, i), rfl⟩) (fun i hk => ?_) i
  refine absurd (Finset.prod_eq_zero hk ?_) h
  have : β (τ, a, Fin.natAdd N i) ≠ 0 := Finsupp.mem_support_iff.1 hk
  simp [this]

/- English proof (translation)
Introduce `D N N' m M ρ G hG`. Use function extensionality and compare the values at `z`. Simplify using `only [fnConj]`. Rewrite using `[← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z)) (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]`. Simplify using `only [taylor_pad D m hG, mono_pad]`.
-/
theorem fnConj_pad : ∀ (D : D7) (N N' m : ℕ) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (G : VC D (N + m) N' → ℂ), Differentiable ℂ G → fnConj D M ρ (fun z : VC D N N' => G (pad D m z)) = fun z => fnConj D M ρ G (pad D m z) := by
  intro D N N' m M ρ G hG
  funext z
  simp only [fnConj]
  rw [← (Finsupp.embDomain_injective (colEmb D N N' m)).tsum_eq
    (f := fun β => ρ (TaylorLogMetric.liftM M (Formalism.MainNotions.TaylorLogMetric.taylor D G β)) * mono D β (pad D m z))
    (fun β hβ => mem_range_of_mono_pad D m β z (right_ne_zero_of_mul hβ))]
  simp only [taylor_pad D m hG, mono_pad]

end GlobalTheory.ConjRestrict
