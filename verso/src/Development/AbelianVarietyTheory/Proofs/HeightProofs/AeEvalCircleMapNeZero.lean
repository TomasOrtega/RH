import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.CastAddNeNatAdd
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegralLogNormLeHalfLogIntegralSq

open MeasureTheory Metric NumberField ReciprocityTheory.ChartRestriction.G.T0 ReciprocityTheory.MultiplicativeHeights
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero`. Introduce `f hf`. Use `Filter.Eventually.of_forall fun x => ?_` and prove the remaining obligations.

Rewrite `hf`, the goal using `[MvPolynomial.eq_C_of_isEmpty f]`. Simplify using `using hf`. Consider the case `succ m ih`. Introduce `f hf`. Use `set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef`.

Establish `hP : P ≠ 0`. Introduce `h`. Apply `hf` to reduce the goal to its premises. Conclude with `(MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hP (Polynomial.ext fun k => by simpa using h k)`. Establish `h1` using `ih _ hk`. Use `set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0`.

Establish `he : MeasurePreserving e volume volume` using `volume_preserving_piFinSuccAbove _ 0`. Establish `hcont : Continuous fun (x : Fin (m + 1) → ℝ) => MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f` using `(MvPolynomial.continuous_eval f).comp (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))`. Establish `hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) | MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0}` using `(hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl`. Establish `key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))), MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0`. Rewrite using `[Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]`.

Rewrite using `[Measure.ae_ae_comm (p := fun y s => MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]`. Use `filter_upwards [h1] with s hs`. Use `set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw`. Establish `hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0`. Introduce `h`.

Apply `hs` to reduce the goal to its premises. Use `congrArg (fun q => Polynomial.coeff q k) h` as an intermediate fact. Simplify `this` using `[Polynomial.coeff_map]`. Establish `hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite` using `Polynomial.finite_setOfPred_isRoot hQ`. Establish `hnull` using `(hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero (volume : Measure ℝ)`.

Rewrite `hnull` using `[measure_eq_zero_iff_ae_notMem]`. Use `filter_upwards [hnull] with y hy`. Establish `hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) = Fin.cons (circleMap 0 1 y) w`. Establish `: (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s`. Simplify using `[e, MeasurableEquiv.piFinSuccAbove_symm_apply]`.

Both sides reduce to the same expression. Rewrite using `[this]`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `cases i using Fin.cases <;> simp [hw]`. Rewrite using `[hc, MvPolynomial.eval_eq_eval_mv_eval']`.

Conclude with `hy`. Use `he.quasiMeasurePreserving.ae key` as an intermediate fact. Use `filter_upwards [this] with x hx`. Simplify using `using hx`.
-/
theorem ae_eval_circleMap_ne_zero : ∀ (m : ℕ) (f : MvPolynomial (Fin m) ℂ), f ≠ 0 →
    ∀ᵐ x ∂(volume : Measure (Fin m → ℝ)),
      MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f ≠ 0 := by
  intro m
  induction m with
  | zero =>
    intro f hf
    refine Filter.Eventually.of_forall fun x => ?_
    rw [MvPolynomial.eq_C_of_isEmpty f] at hf ⊢
    simpa using hf
  | succ m ih =>
    intro f hf
    set P := MvPolynomial.finSuccEquiv ℂ m f with hPdef
    have hP : P ≠ 0 := by
      intro h
      apply hf
      exact (MvPolynomial.finSuccEquiv ℂ m).injective (by rw [← hPdef, h, map_zero])
    obtain ⟨k, hk⟩ : ∃ k, P.coeff k ≠ 0 := by
      by_contra h
      push Not at h
      exact hP (Polynomial.ext fun k => by simpa using h k)
    have h1 := ih _ hk
    set e := MeasurableEquiv.piFinSuccAbove (fun _ : Fin (m + 1) => ℝ) 0
    have he : MeasurePreserving e volume volume := volume_preserving_piFinSuccAbove _ 0
    have hcont : Continuous fun (x : Fin (m + 1) → ℝ) =>
        MvPolynomial.eval (fun i => circleMap 0 1 (x i)) f :=
      (MvPolynomial.continuous_eval f).comp
        (continuous_pi fun i => (continuous_circleMap 0 1).comp (continuous_apply i))
    have hmeas : MeasurableSet {z : ℝ × (Fin m → ℝ) |
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0} :=
      (hcont.measurable.comp e.symm.measurable) (measurableSet_singleton 0).compl
    have key : ∀ᵐ z ∂(volume : Measure (ℝ × (Fin m → ℝ))),
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm z i)) f ≠ 0 := by
      rw [Measure.volume_eq_prod, Measure.ae_prod_iff_ae_ae hmeas]
      rw [Measure.ae_ae_comm (p := fun y s =>
        MvPolynomial.eval (fun i => circleMap 0 1 (e.symm (y, s) i)) f ≠ 0) hmeas]
      filter_upwards [h1] with s hs
      set w : Fin m → ℂ := fun i => circleMap 0 1 (s i) with hw
      have hQ : Polynomial.map (MvPolynomial.eval w) P ≠ 0 := by
        intro h
        apply hs
        have := congrArg (fun q => Polynomial.coeff q k) h
        simpa [Polynomial.coeff_map] using this
      have hfin : ({y : ℂ | Polynomial.eval y (Polynomial.map (MvPolynomial.eval w) P) = 0}).Finite :=
        Polynomial.finite_setOfPred_isRoot hQ
      have hnull := (hfin.countable.preimage_circleMap 0 one_ne_zero).measure_zero
        (volume : Measure ℝ)
      rw [measure_eq_zero_iff_ae_notMem] at hnull
      filter_upwards [hnull] with y hy
      have hc : (fun i => circleMap 0 1 ((e.symm (y, s) : Fin (m + 1) → ℝ) i)) =
          Fin.cons (circleMap 0 1 y) w := by
        have : (e.symm (y, s) : Fin (m + 1) → ℝ) = Fin.cons y s := by
          simp [e, MeasurableEquiv.piFinSuccAbove_symm_apply]; rfl
        rw [this]
        funext i
        cases i using Fin.cases <;> simp [hw]
      rw [hc, MvPolynomial.eval_eq_eval_mv_eval']
      exact hy
    have := he.quasiMeasurePreserving.ae key
    filter_upwards [this] with x hx
    simpa using hx

/- English proof (translation)
Use `NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)` as an intermediate fact. Use `set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) := Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ`. Establish `hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K), IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0`. Rewrite using `[ae_all_iff]`. Introduce `a`.

Rewrite using `[ae_all_iff]`. Introduce `p`. Distinguish the cases in `hp : IsMultiHomogeneous a p ∧ p ≠ 0`. Establish `hm : IsMultiHomogeneous a (MvPolynomial.map sg p)` using `fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)`. Establish `hm0 : MvPolynomial.map sg p ≠ 0` using `fun h0 => hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))`.

Use `filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _`. Rewrite `hz` using `[MvPolynomial.eval_map]`. Then use the resulting hypothesis. Conclude with `Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp`. Rewrite using `[ae_all_iff]`. Introduce `p`.

Distinguish the cases in `hp : p = 0`. Conclude with `Filter.Eventually.of_forall fun z h => absurd hp h`. Use `set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t => MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ`. Establish `hφc : Continuous φ`. Establish `: φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p)`.

Use function extensionality and compare the values at `t`. Rewrite using `[MvPolynomial.eval_map]`. Rewrite using `[this]`. Conclude with `(MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)`. Use `set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) := fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT`.

Establish `hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) => T x.2 x.1`. Use `continuous_pi fun i => ?_` and prove the remaining obligations. Conclude with `(continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) => (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)`. Establish `hTμ : ∀ θ, MeasurePreserving (T θ) μ μ` using `fun θ => measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _`. Use `set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K := MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq`.

Establish `hq0 : q ≠ 0`. Introduce `h`. Apply `hp` to reduce the goal to its premises. Use `MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_ (by rw [map_zero]; exact h)` and prove the remaining obligations. Introduce and unpack `⟨a, b⟩ ⟨c, d⟩ h`.

Simplify using `using h`. Establish `h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0` using `by filter_upwards [hgen] with t ht`. Establish `hq' : NPB.psi sg (blockPoint t) q ≠ 0` using `fun h0 => hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))`. Use `filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ`. Rewrite `hθ` using `[NPB.eval_psi, hq, MvPolynomial.eval₂_rename]`.

Use `hθ using 1` and compare the differences between its conclusion and the goal. Simplify using `only [hφ]`. Use `congr 1`. Rewrite `h1` using `[Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0) ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)]`. Establish `: (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot` using `ae_neBot.2 (NeZero.ne _)`.

Take `⟨θ, hθ⟩` from `h1.exists`. Establish `h2 : ∀ᵐ t ∂μ, φ t ≠ 0`. Rewrite using `[← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0) (hTμ θ).measurable.aemeasurable (hφc.measurable (measurableSet_singleton 0).compl)]`. Conclude with `hθ`. Use `filter_upwards [h2] with t ht _ using ht`.
-/
theorem ae_eval₂_ne_zero_pi_toSphere (K : Type) [Field K] [Countable K] (sg : K →+* ℂ)
    (D N : ℕ) :
    ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D =>
      (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere),
      ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 →
        MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0 := by
  have := NPB.countable_mvPoly (σ := Fin D × Fin (N + 1)) (R := K)
  set μ : Measure (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    Measure.pi fun _ : Fin D => (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere with hμ
  have hgen : ∀ᵐ z ∂μ, ∀ (a : Fin D → ℕ) (p : MvPolynomial (Fin D × Fin (N + 1)) K),
      IsMultiHomogeneous a p → p ≠ 0 → MvPolynomial.eval₂ sg (blockPoint z) p ≠ 0 := by
    rw [ae_all_iff]; intro a
    rw [ae_all_iff]; intro p
    by_cases hp : IsMultiHomogeneous a p ∧ p ≠ 0
    · have hm : IsMultiHomogeneous a (MvPolynomial.map sg p) :=
        fun s hs => hp.1 s (MvPolynomial.support_map_subset _ _ hs)
      have hm0 : MvPolynomial.map sg p ≠ 0 := fun h0 =>
        hp.2 (MvPolynomial.map_injective sg sg.injective (by rw [h0, map_zero]))
      filter_upwards [ae_toSphere D (N + 1) a _ hm0 hm] with z hz _ _
      rwa [MvPolynomial.eval_map] at hz
    · exact Filter.Eventually.of_forall fun z h1 h2 => absurd ⟨h1, h2⟩ hp
  rw [ae_all_iff]; intro p
  by_cases hp : p = 0
  · exact Filter.Eventually.of_forall fun z h => absurd hp h
  set φ : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → ℂ := fun t =>
    MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p with hφ
  have hφc : Continuous φ := by
    have : φ = fun t => MvPolynomial.eval (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) (MvPolynomial.map sg p) := by
      funext t; rw [MvPolynomial.eval_map]
    rw [this]
    exact (MvPolynomial.continuous_eval _).comp (continuous_pi fun q => by fun_prop)
  set T : (Fin (N + 1 + D) → ℝ) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) → (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) :=
    fun θ t i => sphereRotation (θ (Fin.natAdd (N + 1) i)) (t i) with hT
  have hTc : Continuous fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
      T x.2 x.1 := by
    refine continuous_pi fun i => ?_
    exact (continuous_sphereRotation (E := EuclideanSpace ℂ (Fin (N + 1)))).comp
      (f := fun x : (Fin D → sphere (0 : EuclideanSpace ℂ (Fin (N + 1))) 1) × (Fin (N + 1 + D) → ℝ) =>
        (x.2 (Fin.natAdd (N + 1) i), x.1 i)) (by fun_prop)
  have hTμ : ∀ θ, MeasurePreserving (T θ) μ μ := fun θ =>
    measurePreserving_pi _ _ fun i => measurePreserving_sphereRotation (volume : Measure (EuclideanSpace ℂ (Fin (N + 1)))) _
  set q : MvPolynomial (Fin (D + 1) × Fin (N + 1)) K :=
    MvPolynomial.rename (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) p with hq
  have hq0 : q ≠ 0 := by
    intro h
    apply hp
    refine MvPolynomial.rename_injective (fun r : Fin D × Fin (N + 1) => (r.1.succ, r.2)) ?_
      (by rw [map_zero]; exact h)
    rintro ⟨a, b⟩ ⟨c, d⟩ h
    simpa using h
  have h1 : ∀ᵐ t ∂μ, ∀ᵐ θ ∂(volume : Measure (Fin (N + 1 + D) → ℝ)), φ (T θ t) ≠ 0 := by
    filter_upwards [hgen] with t ht
    have hq' : NPB.psi sg (blockPoint t) q ≠ 0 := fun h0 =>
      hq0 (NPB.psi_injective sg (blockPoint t) ht (by rw [h0, map_zero]))
    filter_upwards [ae_eval_circleMap_ne_zero _ _ hq'] with θ hθ
    rw [NPB.eval_psi, hq, MvPolynomial.eval₂_rename] at hθ
    convert hθ using 1
    simp only [hφ]
    congr 1
  rw [Measure.ae_ae_comm (p := fun t θ => φ (T θ t) ≠ 0)
    ((hφc.comp hTc).measurable (measurableSet_singleton 0).compl)] at h1
  have : (ae (volume : Measure (Fin (N + 1 + D) → ℝ))).NeBot := ae_neBot.2 (NeZero.ne _)
  obtain ⟨θ, hθ⟩ := h1.exists
  have h2 : ∀ᵐ t ∂μ, φ t ≠ 0 := by
    rw [← (hTμ θ).map_eq, ae_map_iff (p := fun x => φ x ≠ 0)
      (hTμ θ).measurable.aemeasurable
      (hφc.measurable (measurableSet_singleton 0).compl)]
    exact hθ
  filter_upwards [h2] with t ht _ using ht

end GlobalTheory
