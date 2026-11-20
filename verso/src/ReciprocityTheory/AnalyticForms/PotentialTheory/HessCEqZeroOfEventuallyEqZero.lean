import ReciprocityTheory.AnalyticForms.PotentialTheory.IsPotentialPullbackStatement
import ReciprocityTheory.AnalyticForms.PlurisubharmonicFunctions.PartsSt

namespace ReciprocityTheory.AnForm.M.PLAux

open MeasureTheory FinHolAtlas Filter Topology
open scoped ContDiff

noncomputable section

variable {e : ℕ} {X : Type} [TopologicalSpace X]

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem smooth_continuous {A : FinHolAtlas e X} {f : X → ℝ} (hf : A.Smooth f) : Continuous f := by
  rw [continuous_iff_continuousAt]
  intro p
  obtain ⟨j, hj⟩ := A.cover p
  have h1 : ContinuousAt (f ∘ (A.chart j).symm) (A.chart j p) := by
    refine (hf j).continuousOn.continuousAt ?_
    simp only [Set.preimage_univ, Set.inter_univ]
    exact (A.chart j).open_target.mem_nhds ((A.chart j).map_source hj)
  refine (h1.comp ((A.chart j).continuousAt hj)).congr ?_
  filter_upwards [(A.chart j).open_source.mem_nhds hj] with q hq
  simp [(A.chart j).left_inv hq]

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem smoothOn_mul {A : FinHolAtlas e X} {U : Set X} {f g : X → ℝ} (hf : A.SmoothOn U f)
    (hg : A.SmoothOn U g) : A.SmoothOn U (fun x => f x * g x) := fun j => (hf j).mul (hg j)

/- English proof (translation)
Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending.
-/
theorem smooth_sum {A : FinHolAtlas e X} {ι : Type} (s : Finset ι) {f : ι → X → ℝ}
    (hf : ∀ i ∈ s, A.Smooth (f i)) : A.Smooth (fun x => ∑ i ∈ s, f i x) := fun j =>
  ContDiffOn.sum fun i hi => hf i hi j

/- English proof (translation)
Replace the relevant objects with their definitions. Replace the relevant objects with their definitions. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mInt_congr {A : FinHolAtlas e X} {Φ Ψ : Fin e → LocPot X} {g g' : X → ℝ}
    (h : ∀ j, ∀ y ∈ (A.chart j).target,
      g ((A.chart j).symm y) * locDens A Φ j y = g' ((A.chart j).symm y) * locDens A Ψ j y) :
    mInt A Φ g = mInt A Ψ g' := by
  unfold mInt
  split_ifs with hP
  · unfold integralWith
    refine Finset.sum_congr rfl fun j _ => ?_
    refine setIntegral_congr_fun (A.chart j).open_target.measurableSet fun y hy => ?_
    simp only [mul_assoc]
    rw [h j y hy]
  · rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Simplify using the standard rewrite rules. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem mInt_zero_fun (A : FinHolAtlas e X) (Φ : Fin e → LocPot X) {g : X → ℝ}
    (hg : ∀ x, g x = 0) : mInt A Φ g = 0 := by
  unfold mInt
  split_ifs
  · simp [integralWith, hg]
  · rfl

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem hessC_congr_eventuallyEq {D : ℕ} {f g : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : f =ᶠ[𝓝 y] g) : hessC f y = hessC g y := by
  have h2 : fderiv ℝ (fderiv ℝ f) y = fderiv ℝ (fderiv ℝ g) y := h.fderiv.fderiv_eq
  ext i j
  simp [hessC, h2]

/- English proof (translation)
Replace the relevant objects with their definitions. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument. A detailed English derivation is pending.
-/
theorem maDens_congr_germ {D : ℕ} {φ ψ : Fin D → (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : ∀ i, φ i =ᶠ[𝓝 y] ψ i) : maDens φ y = maDens ψ y := by
  unfold maDens
  congr 3
  funext k
  exact hessC_congr_eventuallyEq (h k)

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. By extensionality, compare the relevant components.

Simplify using the standard rewrite rules.
-/
theorem hessC_eq_zero_of_eventuallyEq_zero {D : ℕ} {f : (Fin D → ℂ) → ℝ} {y : Fin D → ℂ}
    (h : f =ᶠ[𝓝 y] fun _ => 0) : hessC f y = 0 := by
  have h1 : fderiv ℝ f =ᶠ[𝓝 y] fderiv ℝ (fun _ : Fin D → ℂ => (0 : ℝ)) := h.fderiv
  have h2 : fderiv ℝ (fderiv ℝ f) y = 0 := by
    rw [h1.fderiv_eq]
    simp
  ext i j
  simp [hessC, h2]

/- English proof (translation)
Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules.
-/
theorem maDens_cons_eq_zero {n : ℕ} {f : (Fin (n + 1) → ℂ) → ℝ}
    {φ : Fin n → (Fin (n + 1) → ℂ) → ℝ} {y : Fin (n + 1) → ℂ} (h : f =ᶠ[𝓝 y] fun _ => 0) :
    maDens (Fin.cons f φ) y = 0 := by
  have hc : (fun k => hessC ((Fin.cons f φ : Fin (n + 1) → (Fin (n + 1) → ℂ) → ℝ) k) y) =
      Fin.cons (hessC f y) (fun k => hessC (φ k) y) := by
    funext k
    refine Fin.cases ?_ (fun k => ?_) k <;> simp
  unfold maDens
  rw [hc, ReciprocityTheory.AnForm.A.mdisc_cons_eq_sum, hessC_eq_zero_of_eventuallyEq_zero h]
  simp

/- English proof (translation)
Replace the relevant objects with their definitions. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem locDens_cons_ofFun_eq_zero {A : FinHolAtlas (e + 1) X} (v : X → ℝ)
    (Φ : Fin e → LocPot X) (j : Fin A.n) {y : Fin (e + 1) → ℂ} (hy : y ∈ (A.chart j).target)
    (hv : (A.chart j).symm y ∉ tsupport v) :
    locDens A (Fin.cons (LocPot.ofFun v) Φ) j y = 0 := by
  unfold locDens
  have hfam : (fun i y' => ((Fin.cons (LocPot.ofFun v) Φ : Fin (e + 1) → LocPot X) i).φ
      ((A.chart j).symm y) ((A.chart j).symm y')) =
      Fin.cons (fun y' => v ((A.chart j).symm y'))
        (fun i y' => (Φ i).φ ((A.chart j).symm y) ((A.chart j).symm y')) := by
    funext i
    refine Fin.cases ?_ (fun k => ?_) i <;> rfl
  rw [hfam]
  apply maDens_cons_eq_zero
  have hO : IsOpen ((A.chart j).target ∩ (A.chart j).symm ⁻¹' (tsupport v)ᶜ) :=
    (A.chart j).continuousOn_symm.isOpen_inter_preimage (A.chart j).open_target
      (isClosed_tsupport v).isOpen_compl
  filter_upwards [hO.mem_nhds ⟨hy, hv⟩] with y' hy'
  exact image_eq_zero_of_notMem_tsupport hy'.2

/- English proof (translation)
Establish an intermediate fact. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem volume_coord_eq_zero {n : ℕ} (i : Fin n) : volume {y : Fin n → ℂ | y i = 0} = 0 := by
  have : {y : Fin n → ℂ | y i = 0} = Function.eval i ⁻¹' {0} := rfl
  rw [this, volume_pi]
  exact Measure.pi_eval_preimage_null _ (measure_singleton 0)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Simplify to obtain the desired conclusion from the available facts.
-/
theorem ae_coord_ne_zero {n : ℕ} : ∀ᵐ y : Fin n → ℂ, ∀ i, y i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  rw [ae_iff]
  simpa using volume_coord_eq_zero i

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
theorem contDiffOn_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {U : Set X} (hU : IsOpen U) {f : X → ℝ} (hf : A.SmoothOn U f) :
    ContDiffOn ℝ ∞ (f ∘ ψ.symm) (ψ.target ∩ ψ.symm ⁻¹' U) := by
  intro y hy
  refine ContDiffAt.contDiffWithinAt ?_
  obtain ⟨a, ha⟩ := A.cover (ψ.symm y)
  have h1 : ContDiffAt ℝ ∞ (f ∘ (A.chart a).symm) (A.chart a (ψ.symm y)) := by
    have hO' : IsOpen ((A.chart a).target ∩ (A.chart a).symm ⁻¹' U) :=
      (A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target hU
    refine (hf a).contDiffAt (hO'.mem_nhds ⟨(A.chart a).map_source ha, ?_⟩)
    simpa [(A.chart a).left_inv ha] using hy.2
  have h2 : ContDiffAt ℝ ∞ (A.chart a ∘ ψ.symm) y :=
    ((hψ a).2 y ⟨hy.1, ha⟩).contDiffAt.restrict_scalars ℝ
  refine (h1.comp y h2).congr_of_eventuallyEq ?_
  have hN : ψ.target ∩ ψ.symm ⁻¹' (A.chart a).source ∈ 𝓝 y :=
    (ψ.continuousOn_symm.isOpen_inter_preimage ψ.open_target (A.chart a).open_source).mem_nhds
      ⟨hy.1, ha⟩
  filter_upwards [hN] with y' hy'
  simp [(A.chart a).left_inv hy'.2]

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem analyticAt_compat {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) (a : Fin A.n) {p : X} (hpa : p ∈ (A.chart a).source)
    (hpψ : p ∈ ψ.source) : AnalyticAt ℂ (ψ ∘ (A.chart a).symm) (A.chart a p) :=
  (hψ a).1 _ ⟨(A.chart a).map_source hpa, by simpa [(A.chart a).left_inv hpa] using hpψ⟩

def chartPush (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (F : (Fin e → ℂ) → ℝ) : X → ℝ :=
  ψ.source.indicator (F ∘ ψ)

def chartExt (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (v : X → ℝ) : (Fin e → ℂ) → ℝ :=
  ψ.target.indicator (v ∘ ψ.symm)

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem chartPush_symm (ψ : OpenPartialHomeomorph X (Fin e → ℂ)) (F : (Fin e → ℂ) → ℝ)
    {y : Fin e → ℂ} (hy : y ∈ ψ.target) : chartPush ψ F (ψ.symm y) = F y := by
  simp [chartPush, Set.indicator_of_mem (ψ.map_target hy), ψ.right_inv hy]

/- English proof (translation)
Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails. Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem chartPush_eq_zero (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} {p : X}
    (hp : p ∉ ψ.symm '' tsupport F) : chartPush ψ F p = 0 := by
  unfold chartPush
  by_cases hs : p ∈ ψ.source
  · rw [Set.indicator_of_mem hs]
    by_contra hne
    exact hp ⟨ψ p, subset_tsupport _ hne, ψ.left_inv hs⟩
  · exact Set.indicator_of_notMem hs _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem isCompact_symm_image {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} {F : (Fin e → ℂ) → ℝ}
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    IsCompact (ψ.symm '' tsupport F) :=
  hK.image_of_continuousOn (ψ.continuousOn_symm.mono hKt)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the negation of the conclusion and derive a contradiction. A detailed English derivation is pending.
-/
theorem tsupport_chartPush [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.symm '' tsupport F := by
  refine closure_minimal (fun p hp => ?_) (isCompact_symm_image hK hKt).isClosed
  by_contra h
  exact hp (chartPush_eq_zero ψ h)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem tsupport_chartPush_source [T2Space X] (ψ : OpenPartialHomeomorph X (Fin e → ℂ))
    {F : (Fin e → ℂ) → ℝ} (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) :
    tsupport (chartPush ψ F) ⊆ ψ.source := by
  refine (tsupport_chartPush ψ hK hKt).trans ?_
  rintro _ ⟨y, hy, rfl⟩
  exact ψ.map_target (hKt hy)

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Consider separately whether the proposition holds or fails. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Extract witnesses or component facts from the available result.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem smooth_chartPush [T2Space X] {A : FinHolAtlas e X} {ψ : OpenPartialHomeomorph X (Fin e → ℂ)}
    (hψ : IsCompatChart A ψ) {F : (Fin e → ℂ) → ℝ} (hF : ContDiff ℝ ∞ F)
    (hK : IsCompact (tsupport F)) (hKt : tsupport F ⊆ ψ.target) : A.Smooth (chartPush ψ F) := by
  intro a y hy
  refine ContDiffAt.contDiffWithinAt ?_
  set C := ψ.symm '' tsupport F
  have hC : IsClosed C := (isCompact_symm_image hK hKt).isClosed
  by_cases hs : (A.chart a).symm y ∈ ψ.source
  · have hya : (A.chart a).symm y ∈ (A.chart a).source := (A.chart a).map_target hy.1
    have h2 : ContDiffAt ℝ ∞ (ψ ∘ (A.chart a).symm) y := by
      have := (analyticAt_compat hψ a hya hs).contDiffAt (n := ∞)
      rw [(A.chart a).right_inv hy.1] at this
      exact this.restrict_scalars ℝ
    refine (hF.contDiffAt.comp y h2).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' ψ.source ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        ψ.open_source).mem_nhds ⟨hy.1, hs⟩
    filter_upwards [hN] with y' hy'
    simp only [chartPush, Function.comp_apply]
    rw [Set.indicator_of_mem (show (A.chart a).symm y' ∈ ψ.source from hy'.2)]
    rfl
  · have hnC : (A.chart a).symm y ∉ C := fun h => hs (by
      obtain ⟨z, hz, hzz⟩ := h
      rw [← hzz]; exact ψ.map_target (hKt hz))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    have hN : (A.chart a).target ∩ (A.chart a).symm ⁻¹' Cᶜ ∈ 𝓝 y :=
      ((A.chart a).continuousOn_symm.isOpen_inter_preimage (A.chart a).open_target
        hC.isOpen_compl).mem_nhds ⟨hy.1, hnC⟩
    filter_upwards [hN] with y' hy'
    exact chartPush_eq_zero ψ hy'.2

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Consider separately whether the proposition holds or fails.

Rewrite the conclusion using the stated equalities. Assume the negation of the conclusion and derive a contradiction. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Consider separately whether the proposition holds or fails. Establish an intermediate fact. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Simplify using the standard rewrite rules.

Establish an intermediate fact. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. A detailed English derivation is pending.
-/
theorem contDiff_chartExt [T2Space X] [CompactSpace X] {A : FinHolAtlas e X}
    {ψ : OpenPartialHomeomorph X (Fin e → ℂ)} (hψ : IsCompatChart A ψ) {v : X → ℝ}
    (hv : A.Smooth v) (hvs : tsupport v ⊆ ψ.source) :
    ContDiff ℝ ∞ (chartExt ψ v) ∧ IsCompact (ψ '' tsupport v) ∧
      tsupport (chartExt ψ v) ⊆ ψ '' tsupport v := by
  have hK : IsCompact (ψ '' tsupport v) :=
    (isClosed_tsupport v).isCompact.image_of_continuousOn (ψ.continuousOn.mono hvs)
  have hsupp : ∀ y, y ∉ ψ '' tsupport v → chartExt ψ v y = 0 := by
    intro y hy
    unfold chartExt
    by_cases ht : y ∈ ψ.target
    · rw [Set.indicator_of_mem ht]
      by_contra hne
      exact hy ⟨ψ.symm y, subset_tsupport _ hne, ψ.right_inv ht⟩
    · exact Set.indicator_of_notMem ht _
  refine ⟨?_, hK, closure_minimal (fun y hy => by_contra fun h => hy (hsupp y h)) hK.isClosed⟩
  rw [contDiff_iff_contDiffAt]
  intro y
  by_cases ht : y ∈ ψ.target
  · have h1 := contDiffOn_compat hψ isOpen_univ hv
    simp only [Set.preimage_univ, Set.inter_univ] at h1
    refine (h1.contDiffAt (ψ.open_target.mem_nhds ht)).congr_of_eventuallyEq ?_
    filter_upwards [ψ.open_target.mem_nhds ht] with y' hy'
    simp [chartExt, Set.indicator_of_mem hy']
  · have hy : y ∉ ψ '' tsupport v := by
      rintro ⟨p, hp, rfl⟩; exact ht (ψ.map_source (hvs hp))
    refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
    filter_upwards [hK.isClosed.isOpen_compl.mem_nhds hy] with y' hy'
    exact hsupp y' hy'

end

end ReciprocityTheory.AnForm.M.PLAux
