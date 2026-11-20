import Mathlib

noncomputable section

namespace PI.AprimeInfG

open MeasureTheory Set
open scoped ENNReal

/- English proof (translation)
Use `⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩` and prove the remaining obligations. Use `symm`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]`. Establish `e : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s = Set.univ.pi fun v => Set.univ.pi fun a => s ⟨v, a⟩`.

Use extensionality with `z`. Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]`. Conclude with `Iff.rfl`. Rewrite using `[e, Measure.pi_pi]`. Repeatedly rewrite using `[Measure.pi_pi]`.

Rewrite using `[Fintype.prod_sigma]`.
-/
theorem measurePreserving_piCurry_symm {V : Type} [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    {X : ∀ v, α v → Type} [∀ v a, MeasurableSpace (X v a)] (μ : ∀ v a, Measure (X v a))
    [∀ v a, SigmaFinite (μ v a)] :
    MeasurePreserving (MeasurableEquiv.piCurry X).symm (Measure.pi fun v => Measure.pi fun a => μ v a)
      (Measure.pi fun p : Σ v, α v => μ p.1 p.2) := by
  refine ⟨(MeasurableEquiv.piCurry X).symm.measurable, ?_⟩
  symm
  refine Measure.pi_eq fun s hs => ?_
  rw [Measure.map_apply (MeasurableEquiv.piCurry X).symm.measurable (MeasurableSet.univ_pi hs)]
  have e : (MeasurableEquiv.piCurry X).symm ⁻¹' Set.univ.pi s =
      Set.univ.pi fun v => Set.univ.pi fun a => s ⟨v, a⟩ := by
    ext z
    simp only [Set.mem_preimage, Set.mem_univ_pi, Sigma.forall, MeasurableEquiv.coe_piCurry_symm]
    exact Iff.rfl
  rw [e, Measure.pi_pi]
  simp_rw [Measure.pi_pi]
  rw [Fintype.prod_sigma]

/- English proof (translation)
Set `F : (∀ v, EuclideanSpace ℝ (α v)) →ₗ[ℝ] EuclideanSpace ℝ (Σ v, α v)` to `{ toFun := fun z => WithLp.toLp 2 (fun p : Σ v, α v => z p.1 p.2) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hFn : ∀ z, ‖F z‖ ^ 2 = ∑ v, ‖z v‖ ^ 2`. Introduce `z`. Rewrite using `[EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]`. Use `Finset.sum_congr rfl fun v _ => ?_` and prove the remaining obligations.

Rewrite using `[EuclideanSpace.norm_sq_eq]`. Both sides reduce to the same expression. Establish `hF : MeasurePreserving F (Measure.pi fun v => volume) volume`. Establish `h1` using `measurePreserving_pi (fun v => (volume : Measure (EuclideanSpace ℝ (α v)))) (fun v => (volume : Measure (α v → ℝ))) (fun v => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (α v))`. Establish `h2` using `measurePreserving_piCurry_symm (X := fun v (_ : α v) => ℝ) (fun _ _ => (volume : Measure ℝ))`.

Establish `h3` using `PiLp.volume_preserving_toLp (Σ v, α v)`. Simplify using `only [← MeasureTheory.volume_pi] at h2`. Conclude with `(h3.comp (h2.comp h1))`. Establish `hGn : ∀ x, ‖F (T x)‖ = ‖x‖`. Introduce `x`.

Use `hFn (T x)` as an intermediate fact. Rewrite `this` using `[hn x]`. Conclude with `(sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this`. Set `G : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Σ v, α v)` to `⟨F ∘ₗ T, hGn⟩`. Establish `hFi : Function.Injective F`.

Introduce `z z' h`. Use function extensionality and compare the values at `v`. Use extensionality with `a`. Use `congrArg (fun w : EuclideanSpace ℝ (Σ v, α v) => w ⟨v, a⟩) h` as an intermediate fact. Conclude with `this`.

Establish `hFs : Function.Surjective F`. Introduce `w`. Conclude with `⟨fun v => WithLp.toLp 2 (fun a => w ⟨v, a⟩), rfl⟩`. Establish `hGs : Function.Surjective G` using `(hFs.comp hbij.2)`. Set `Ge` to `LinearIsometryEquiv.ofSurjective G hGs`.

Establish `hGe : MeasurePreserving Ge volume volume` using `Ge.measurePreserving`. Set `Fe : (∀ v, EuclideanSpace ℝ (α v)) ≃ᵐ EuclideanSpace ℝ (Σ v, α v)` to `{ toEquiv := Equiv.ofBijective F ⟨hFi, hFs⟩ measurable_toFun := hF.measurable measurable_invFun := by`. Establish `: ⇑(Equiv.ofBijective F ⟨hFi, hFs⟩).symm = fun (w : EuclideanSpace ℝ (Σ v, α v)) (v : V) => (WithLp.toLp 2 (fun a => w ⟨v, a⟩) : EuclideanSpace ℝ (α v))`. Use function extensionality and compare the values at `w`. Apply `(Equiv.ofBijective F ⟨hFi, hFs⟩).injective` to reduce the goal to its premises.

Rewrite using `[Equiv.apply_symm_apply]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `measurable_pi_lambda _ fun v => (PiLp.volume_preserving_toLp (α v)).measurable.comp (measurable_pi_lambda _ fun a => (measurable_pi_apply _).comp (PiLp.volume_preserving_ofLp _).measurable) }`. Establish `hFe : MeasurePreserving Fe (Measure.pi fun v => volume) volume` using `hF`.

Establish `key` using `hFe.symm.comp hGe`. Use `key using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x`. Use `show T x = Fe.symm (F (T x))`. Conclude with `(Fe.symm_apply_apply (T x)).symm`.
-/
theorem measurePreserving_of_normSq {ι V : Type} [Fintype ι] [Fintype V] {α : V → Type} [∀ v, Fintype (α v)]
    (T : EuclideanSpace ℝ ι →ₗ[ℝ] (∀ v, EuclideanSpace ℝ (α v))) (hbij : Function.Bijective T)
    (hn : ∀ x, ∑ v, ‖T x v‖ ^ 2 = ‖x‖ ^ 2) :
    MeasurePreserving T volume (Measure.pi fun _ => volume) := by

  let F : (∀ v, EuclideanSpace ℝ (α v)) →ₗ[ℝ] EuclideanSpace ℝ (Σ v, α v) :=
    { toFun := fun z => WithLp.toLp 2 (fun p : Σ v, α v => z p.1 p.2)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hFn : ∀ z, ‖F z‖ ^ 2 = ∑ v, ‖z v‖ ^ 2 := by
    intro z
    rw [EuclideanSpace.norm_sq_eq, Fintype.sum_sigma]
    refine Finset.sum_congr rfl fun v _ => ?_
    rw [EuclideanSpace.norm_sq_eq]
    rfl
  have hF : MeasurePreserving F (Measure.pi fun v => volume) volume := by
    have h1 := measurePreserving_pi (fun v => (volume : Measure (EuclideanSpace ℝ (α v))))
      (fun v => (volume : Measure (α v → ℝ)))
      (fun v => EuclideanSpace.volume_preserving_symm_measurableEquiv_toLp (α v))
    have h2 := measurePreserving_piCurry_symm (X := fun v (_ : α v) => ℝ) (fun _ _ => (volume : Measure ℝ))
    have h3 := PiLp.volume_preserving_toLp (Σ v, α v)
    simp only [← MeasureTheory.volume_pi] at h2
    exact (h3.comp (h2.comp h1))
  have hGn : ∀ x, ‖F (T x)‖ = ‖x‖ := by
    intro x
    have := hFn (T x)
    rw [hn x] at this
    exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 this
  let G : EuclideanSpace ℝ ι →ₗᵢ[ℝ] EuclideanSpace ℝ (Σ v, α v) := ⟨F ∘ₗ T, hGn⟩
  have hFi : Function.Injective F := by
    intro z z' h
    funext v
    ext a
    have := congrArg (fun w : EuclideanSpace ℝ (Σ v, α v) => w ⟨v, a⟩) h
    exact this
  have hFs : Function.Surjective F := by
    intro w
    exact ⟨fun v => WithLp.toLp 2 (fun a => w ⟨v, a⟩), rfl⟩
  have hGs : Function.Surjective G := (hFs.comp hbij.2)
  let Ge := LinearIsometryEquiv.ofSurjective G hGs
  have hGe : MeasurePreserving Ge volume volume := Ge.measurePreserving
  let Fe : (∀ v, EuclideanSpace ℝ (α v)) ≃ᵐ EuclideanSpace ℝ (Σ v, α v) :=
    { toEquiv := Equiv.ofBijective F ⟨hFi, hFs⟩
      measurable_toFun := hF.measurable
      measurable_invFun := by
        have : ⇑(Equiv.ofBijective F ⟨hFi, hFs⟩).symm =
            fun (w : EuclideanSpace ℝ (Σ v, α v)) (v : V) => (WithLp.toLp 2 (fun a => w ⟨v, a⟩) : EuclideanSpace ℝ (α v)) := by
          funext w
          apply (Equiv.ofBijective F ⟨hFi, hFs⟩).injective
          rw [Equiv.apply_symm_apply]
          rfl
        rw [this]
        exact measurable_pi_lambda _ fun v =>
          (PiLp.volume_preserving_toLp (α v)).measurable.comp
            (measurable_pi_lambda _ fun a => (measurable_pi_apply _).comp (PiLp.volume_preserving_ofLp _).measurable) }
  have hFe : MeasurePreserving Fe (Measure.pi fun v => volume) volume := hF
  have key := hFe.symm.comp hGe
  convert key using 1
  funext x
  show T x = Fe.symm (F (T x))
  exact (Fe.symm_apply_apply (T x)).symm

def piProdEquiv {V : Type} (A B : V → Type) [∀ v, MeasurableSpace (A v)] [∀ v, MeasurableSpace (B v)] :
    (∀ v, A v × B v) ≃ᵐ (∀ v, A v) × (∀ v, B v) where
  toFun z := (fun v => (z v).1, fun v => (z v).2)
  invFun p v := (p.1 v, p.2 v)
  left_inv _ := rfl
  right_inv _ := rfl
  measurable_toFun := (measurable_pi_lambda _ fun v => measurable_fst.comp (measurable_pi_apply v)).prodMk
    (measurable_pi_lambda _ fun v => measurable_snd.comp (measurable_pi_apply v))
  measurable_invFun := measurable_pi_lambda _ fun v =>
    ((measurable_pi_apply v).comp measurable_fst).prodMk ((measurable_pi_apply v).comp measurable_snd)

/- English proof (translation)
The claim follows from `(piProdEquiv A B).measurable map_eq := by refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi) ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm …`.
-/
theorem measurePreserving_piProdEquiv {V : Type} [Fintype V] (A B : V → Type) [∀ v, MeasurableSpace (A v)]
    [∀ v, MeasurableSpace (B v)] (μ : ∀ v, Measure (A v)) (ν : ∀ v, Measure (B v)) [∀ v, SigmaFinite (μ v)]
    [∀ v, SigmaFinite (ν v)] :
    MeasurePreserving (piProdEquiv A B) (Measure.pi fun v => (μ v).prod (ν v))
      ((Measure.pi fun v => μ v).prod (Measure.pi fun v => ν v)) where
  measurable := (piProdEquiv A B).measurable
  map_eq := by
    refine (Measure.FiniteSpanningSetsIn.ext ?_ (isPiSystem_pi.prod isPiSystem_pi)
      ((Measure.FiniteSpanningSetsIn.pi fun i ↦ (μ i).toFiniteSpanningSetsIn).prod
      (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn))) ?_).symm
    · refine (generateFrom_eq_prod generateFrom_pi generateFrom_pi ?_ ?_).symm
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (μ i).toFiniteSpanningSetsIn)).isCountablySpanning
      · exact (Measure.FiniteSpanningSetsIn.pi (fun i ↦ (ν i).toFiniteSpanningSetsIn)).isCountablySpanning
    · rintro _ ⟨s, ⟨s, _, rfl⟩, ⟨_, ⟨t, _, rfl⟩, rfl⟩⟩
      rw [MeasurableEquiv.map_apply]
      rw [show (piProdEquiv A B) ⁻¹' (Set.univ.pi s ×ˢ Set.univ.pi t) =
          (Set.univ.pi fun i ↦ s i ×ˢ t i) by
          ext; simp [Set.mem_pi, forall_and, piProdEquiv]]
      simp_rw [Measure.pi_pi, Measure.prod_prod, Measure.pi_pi, Finset.prod_mul_distrib]

end PI.AprimeInfG
