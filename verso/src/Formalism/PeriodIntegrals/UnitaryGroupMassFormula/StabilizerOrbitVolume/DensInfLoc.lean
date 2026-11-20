import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.StabilizerOrbitVolume.DensInfSt

noncomputable section

namespace PI.VolStabSW

open MeasureTheory Topology

def LinDens : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)) (ν : Measure (Fin m → ℝ)), μ.IsAddHaarMeasure →
    ν.IsAddHaarMeasure → ∀ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A →
      DensAll μ A id ν Set.univ

def ChangeVar : Prop :=
  ∀ (n m : ℕ) (μ : Measure (Fin n → ℝ)), μ.IsAddHaarMeasure →
    ∀ (f : (Fin n → ℝ) → (Fin m → ℝ)), ContDiff ℝ 1 f → ∀ x0,
      Function.Surjective (fderiv ℝ f x0) →
      ∃ N, IsOpen N ∧ x0 ∈ N ∧ ∃ A : (Fin n → ℝ) →L[ℝ] (Fin m → ℝ), Function.Surjective A ∧
        ∀ φ : (Fin n → ℝ) → ℝ, Continuous φ → HasCompactSupport φ → tsupport φ ⊆ N →
          ∃ G : (Fin n → ℝ) → ℝ, Continuous G ∧ HasCompactSupport G ∧
            ∀ S : Set (Fin m → ℝ), IsCompact S →
              ∫ v in f ⁻¹' S, φ v ∂μ = ∫ v in A ⁻¹' S, G v ∂μ

/- English proof (translation)
Introduce `n m μ ν hμ hν f hf x0 hx0`. Take `⟨N, hN, hxN, A, hA, hG⟩` from `h2 n m μ hμ f hf x0 hx0`. Use `⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩` and prove the remaining obligations. Take `⟨G, hGc, hGs, hGe⟩` from `hG φ hc hs hφ`. Take `⟨g, hgc, hg⟩` from `h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)`.

Use `⟨g, hgc, fun S hS => ?_⟩` and prove the remaining obligations. Use `hg S hS` as an intermediate fact. Simplify using `only [Set.image_id] at this ⊢`. Rewrite using `[hGe S hS, this]`.
-/
theorem submLocal_of (h1 : LinDens) (h2 : ChangeVar) : SubmLocal := by
  intro n m μ ν hμ hν f hf x0 hx0
  obtain ⟨N, hN, hxN, A, hA, hG⟩ := h2 n m μ hμ f hf x0 hx0
  refine ⟨N, hN, hxN, fun φ hc hs hφ => ?_⟩
  obtain ⟨G, hGc, hGs, hGe⟩ := hG φ hc hs hφ
  obtain ⟨g, hgc, hg⟩ := h1 n m μ ν hμ hν A hA G hGc hGs (Set.subset_univ _)
  refine ⟨g, hgc, fun S hS => ?_⟩
  have := hg S hS
  simp only [Set.image_id] at this ⊢
  rw [hGe S hS, this]

/- English proof (translation)
Introduce `n m μ ν hμ hν f hf`. Conclude with `densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx`.
-/
theorem submDens_of_local (h : SubmLocal) : SubmDens := by
  intro n m μ ν hμ hν f hf
  exact densAll_of_local fun x hx => h n m μ ν hμ hν f hf x hx

/- English proof (translation)
Introduce `n m μ ν hμ hν A hA φ hc hs _`. Take `⟨B, hB⟩` from `A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)`. Establish `hRI : Function.RightInverse B A` using `fun y => by`. Simplify using `using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB`. Set `T` to `ContinuousLinearEquiv.equivOfRightInverse A B hRI`.

Set `K` to `A.ker`. Set `lam : Measure K` to `Measure.addHaar`. Establish `hT1 : ∀ x, (T x).1 = A x` using `fun x => rfl`. Establish `hμT : (μ.map T).IsAddHaarMeasure` using `T.isAddHaarMeasure_map μ`. Take `⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam)` from `⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩`.

Set `H : (Fin m → ℝ) × K → ℝ` to `fun w => φ (T.symm w)`. Establish `hHc : Continuous H` using `hc.comp T.symm.continuous`. Establish `hHs : HasCompactSupport H` using `hs.comp_homeomorph T.symm.toHomeomorph`. Set `s : Set K` to `Prod.snd '' tsupport H`. Establish `hsc : IsCompact s` using `hHs.image continuous_snd`.

Set `ψ : (Fin m → ℝ) → ℝ` to `fun y => ∫ k in s, H (y, k) ∂lam`. Establish `hψc : Continuous ψ` using `continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc`. Establish `hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y`. Introduce `y`. Use `(setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm` and prove the remaining obligations.

Apply `image_eq_zero_of_notMem_tsupport` to reduce the goal to its premises. Introduce `h'`. Conclude with `hk ⟨(y, k), h', rfl⟩`. Use `⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩` and prove the remaining obligations. Establish `hSm : MeasurableSet S` using `hS.isClosed.measurableSet`.

Simplify using `only [Set.image_id]`. Set `Q : (Fin m → ℝ) × K → ℝ` to `(Prod.fst ⁻¹' S).indicator H`. Establish `hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v)`. Introduce `v`. Simplify using `only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]`.

Both sides reduce to the same expression. Establish `hQi : Integrable Q (ν.prod lam)` using `(hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)`. Rewrite using `[← integral_indicator (hSm.preimage A.continuous.measurable)]`. Repeatedly rewrite using `[hQ]`. Establish `e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T)`.

Rewrite using `[show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]`. Both sides reduce to the same expression. Rewrite using `[e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul, ← integral_indicator hSm, ← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `y`.

Distinguish the cases in `hy : y ∈ S`. Simplify using `only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]`. Simplify using `[Q, Set.indicator, hy]`.
-/
theorem linDens_holds : LinDens := by
  intro n m μ ν hμ hν A hA φ hc hs _
  obtain ⟨B, hB⟩ := A.exists_rightInverse_of_surjective (LinearMap.range_eq_top.2 hA)
  have hRI : Function.RightInverse B A := fun y => by
    simpa using congrArg (fun L : (Fin m → ℝ) →L[ℝ] (Fin m → ℝ) => L y) hB
  let T := ContinuousLinearEquiv.equivOfRightInverse A B hRI
  let K := A.ker
  let lam : Measure K := Measure.addHaar
  have hT1 : ∀ x, (T x).1 = A x := fun x => rfl
  have hμT : (μ.map T).IsAddHaarMeasure := T.isAddHaarMeasure_map μ
  obtain ⟨c, hsm⟩ : ∃ c : ENNReal, μ.map T = c • (ν.prod lam) :=
    ⟨_, Measure.isAddLeftInvariant_eq_smul _ _⟩
  let H : (Fin m → ℝ) × K → ℝ := fun w => φ (T.symm w)
  have hHc : Continuous H := hc.comp T.symm.continuous
  have hHs : HasCompactSupport H := hs.comp_homeomorph T.symm.toHomeomorph
  let s : Set K := Prod.snd '' tsupport H
  have hsc : IsCompact s := hHs.image continuous_snd
  let ψ : (Fin m → ℝ) → ℝ := fun y => ∫ k in s, H (y, k) ∂lam
  have hψc : Continuous ψ :=
    continuous_parametric_integral_of_continuous (f := fun y k => H (y, k)) hHc hsc
  have hψ : ∀ y, ∫ k, H (y, k) ∂lam = ψ y := by
    intro y
    refine (setIntegral_eq_integral_of_forall_compl_eq_zero fun k hk => ?_).symm
    apply image_eq_zero_of_notMem_tsupport
    intro h'
    exact hk ⟨(y, k), h', rfl⟩
  refine ⟨fun y => c.toReal * ψ y, continuous_const.mul hψc, fun S hS => ?_⟩
  have hSm : MeasurableSet S := hS.isClosed.measurableSet
  simp only [Set.image_id]
  let Q : (Fin m → ℝ) × K → ℝ := (Prod.fst ⁻¹' S).indicator H
  have hQ : ∀ v, (A ⁻¹' S).indicator φ v = Q (T v) := by
    intro v
    simp only [Q, Set.indicator, H, ContinuousLinearEquiv.symm_apply_apply]
    rfl
  have hQi : Integrable Q (ν.prod lam) :=
    (hHc.integrable_of_hasCompactSupport hHs).indicator (measurable_fst hSm)
  rw [← integral_indicator (hSm.preimage A.continuous.measurable)]
  simp_rw [hQ]
  have e2 : ∫ v, Q (T v) ∂μ = ∫ w, Q w ∂(μ.map T) := by
    rw [show (μ.map T) = μ.map T.toHomeomorph.toMeasurableEquiv from rfl, integral_map_equiv]
    rfl
  rw [e2, hsm, integral_smul_measure, integral_prod _ hQi, smul_eq_mul,
    ← integral_indicator hSm, ← integral_const_mul]
  congr 1
  funext y
  by_cases hy : y ∈ S
  · simp only [Q, Set.indicator, Set.mem_preimage, hy, if_true, ← hψ y]
  · simp [Q, Set.indicator, hy]

end PI.VolStabSW
