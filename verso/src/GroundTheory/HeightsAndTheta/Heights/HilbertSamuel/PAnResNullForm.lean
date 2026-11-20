import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsAnResNullForm
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsNonvanishingDense
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterRedC
import ReciprocityTheory.AnalyticForms.PotentialTheory.AnalyticSubsetChartLocal
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.ArakelovGeometry ReciprocityTheory.AnForm.M MeasureTheory Filter Topology Set

noncomputable section

namespace AnResNullForm

set_option linter.unusedSectionVars false

variable {K : Type} [Fintype K] {ι : K → Type} [∀ k, Fintype (ι k)]

/- English proof (translation)
Take `⟨c1, hc1, rfl⟩` from `h1`. Take `⟨c2, hc2, rfl⟩` from `h2`. Conclude with `⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩`.
-/
theorem sameOrbit_trans_nf {a b c : (Σ k, ι k) → ℂ} (h1 : SameOrbit a b) (h2 : SameOrbit b c) :
    SameOrbit a c := by
  obtain ⟨c1, hc1, rfl⟩ := h1
  obtain ⟨c2, hc2, rfl⟩ := h2
  exact ⟨fun k => c1 k * c2 k, fun k => mul_ne_zero (hc1 k) (hc2 k), by funext q; simp [mul_assoc]⟩

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Use `⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Simplify using `[← mul_assoc, inv_mul_cancel₀ (hc q.1)]`.
-/
theorem sameOrbit_symm_nf {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) : SameOrbit b a := by
  obtain ⟨c, hc, rfl⟩ := h
  refine ⟨fun k => (c k)⁻¹, fun k => inv_ne_zero (hc k), ?_⟩
  funext q
  simp [← mul_assoc, inv_mul_cancel₀ (hc q.1)]

/- English proof (translation)
Simplify using `only [ofPred_forall]`. Apply the tactic sequence `refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;> fun_prop`.
-/
theorem isClosed_blockProportional :
    IsClosed {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
  simp only [ofPred_forall]
  refine isClosed_iInter fun k => isClosed_iInter fun i => isClosed_iInter fun i' => isClosed_eq ?_ ?_ <;>
    fun_prop

/- English proof (translation)
Take `⟨c, -, rfl⟩` from `h`. Introduce `k i i'`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem blockProportional_of_sameOrbit {a b : (Σ k, ι k) → ℂ} (h : SameOrbit a b) :
    ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩ := by
  obtain ⟨c, -, rfl⟩ := h
  intro k i i'
  ring

/- English proof (translation)
Use `choose p hp using hb`. Use `⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩` and prove the remaining obligations. Introduce `h0`. Take `⟨i, hi⟩` from `ha k`. Establish `h1` using `h k i (p k)`.

Break down `div_eq_zero_iff.1 h0 with h0 | h0` into its components or cases. Rewrite `h1` using `[h0, zero_mul]`. Conclude with `hi ((mul_eq_zero_iff_right (hp k)).1 h1)`. Conclude with `hp k h0`. Use function extensionality and compare the values at `⟨k, i⟩ show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩`.

Rewrite using `[div_mul_eq_mul_div, eq_div_iff (hp k)]`. Conclude with `h k i (p k)`.
-/
theorem sameOrbit_of_blockProportional {a b : (Σ k, ι k) → ℂ} (ha : ∀ k, ∃ i, a ⟨k, i⟩ ≠ 0)
    (hb : ∀ k, ∃ i, b ⟨k, i⟩ ≠ 0) (h : ∀ k (i i' : ι k), a ⟨k, i⟩ * b ⟨k, i'⟩ = a ⟨k, i'⟩ * b ⟨k, i⟩) :
    SameOrbit a b := by
  choose p hp using hb
  refine ⟨fun k => a ⟨k, p k⟩ / b ⟨k, p k⟩, fun k => ?_, ?_⟩
  · intro h0
    obtain ⟨i, hi⟩ := ha k
    have h1 := h k i (p k)
    rcases div_eq_zero_iff.1 h0 with h0 | h0
    · rw [h0, zero_mul] at h1
      exact hi ((mul_eq_zero_iff_right (hp k)).1 h1)
    · exact hp k h0
  · funext ⟨k, i⟩
    show a ⟨k, i⟩ = a ⟨k, p k⟩ / b ⟨k, p k⟩ * b ⟨k, i⟩
    rw [div_mul_eq_mul_div, eq_div_iff (hp k)]
    exact h k i (p k)

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Rewrite using `[eval_smul_of_isMultiHomog hG, mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]`.
-/
theorem eval_eq_zero_iff_of_sameOrbit {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG)
    {z z' : (Σ k, ι k) → ℂ} (h : SameOrbit z z') :
    eval z (map (Int.castRingHom ℂ) G) = 0 ↔ eval z' (map (Int.castRingHom ℂ) G) = 0 := by
  obtain ⟨c, hc, rfl⟩ := h
  rw [eval_smul_of_isMultiHomog hG,
    mul_eq_zero_iff_left (Finset.prod_ne_zero_iff.mpr fun k _ => pow_ne_zero _ (hc k))]

variable {P J : Ideal (MRing ι)} {e : ℕ}

/- English proof (translation)
Take `⟨j, hj⟩` from `R.A.cover y`. Rewrite using `[continuousAt_pi]`. Introduce `p`. Establish `hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x` using `⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩`. Establish `h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y)` using `(R.holo x p j _ hya).continuousAt`.

Establish `h2` using `h1.comp ((R.A.chart j).continuousAt hj)`. Use `h2.congr ?_` and prove the remaining obligations. Use `filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'`. Simplify using `[(R.A.chart j).left_inv hy']`.
-/
theorem continuousAt_lift (R : AnRes P J e) (x y : R.X) (hy : y ∈ R.U x) : ContinuousAt (R.lift x) y := by
  obtain ⟨j, hj⟩ := R.A.cover y
  rw [continuousAt_pi]
  intro p
  have hya : R.A.chart j y ∈ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' R.U x :=
    ⟨(R.A.chart j).map_source hj, by simpa [(R.A.chart j).left_inv hj] using hy⟩
  have h1 : ContinuousAt ((fun y' => R.lift x y' p) ∘ (R.A.chart j).symm) (R.A.chart j y) :=
    (R.holo x p j _ hya).continuousAt
  have h2 := h1.comp ((R.A.chart j).continuousAt hj)
  refine h2.congr ?_
  filter_upwards [(R.A.chart j).open_source.mem_nhds hj] with y' hy'
  simp [(R.A.chart j).left_inv hy']

/- English proof (translation)
Introduce `x`. Use `⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G), fun _ j y hy => ?_, ?_⟩` and prove the remaining obligations. Conclude with `analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G`. Use extensionality with `y`. Simplify using `only [mem_inter_iff, mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h0, hy⟩`. Conclude with `⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩`. Introduce and unpack `⟨hy, h0⟩`. Conclude with `⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩`.
-/
theorem isAnalyticSubset (R : AnRes P J e) {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) :
    R.A.IsAnalyticSubset {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} := by
  intro x
  refine ⟨R.U x, R.isOpen_U x, R.mem_U x, 1, fun _ y => eval (R.lift x y) (map (Int.castRingHom ℂ) G),
    fun _ j y hy => ?_, ?_⟩
  · exact analyticAt_eval_comp (F := fun y' => R.lift x ((R.A.chart j).symm y')) (fun p => R.holo x p j y hy) G
  · ext y
    simp only [mem_inter_iff, mem_ofPred_eq]
    constructor
    · rintro ⟨h0, hy⟩
      exact ⟨hy, fun _ => (eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).2 h0⟩
    · rintro ⟨hy, h0⟩
      exact ⟨(eval_eq_zero_iff_of_sameOrbit hG (R.compat x y y ⟨hy, R.mem_U y⟩)).1 (h0 0), hy⟩

/- English proof (translation)
Use `set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS`. Assume the negation of the conclusion as `hne`. Take `⟨x0, hx0⟩` from `nonempty_iff_ne_empty.2 hne`. Take `⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J` from `by by_contra! hall`. Take `⟨j, hj⟩` from `R.A.cover x0`.

Establish `hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source))` using `((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2 (isOpen_interior.inter (R.A.chart j).open_source)`. Establish `hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source))` using `hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩`. Establish `hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆ (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J}`. Introduce and unpack `_ ⟨y, ⟨hyW, hys⟩, rfl⟩`. Conclude with `⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩`.

Conclude with `hpos.ne' (measure_mono_null hsub (R.null j))`. Use `set z := R.lift x x with hzdef`. Establish `hzP : z ∈ mcPts P` using `R.mem x x (R.mem_U x)`. Use `set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC`. Establish `hCc : IsClosed C`.

Simplify using `only [hC, ofPred_forall]`. Conclude with `isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _) continuous_const`. Establish `hzC : z ∉ C` using `fun h => hxJ ⟨hzP.1, h⟩`. Use `set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT`. Establish `hzT : z ∈ closure T`.

Rewrite using `[mem_closure_iff_nhds]`. Introduce `t ht`. Take `⟨w, ⟨hwt, hwC⟩, hw⟩` from `mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ) (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))`. Conclude with `⟨w, hwt, hw, hwC⟩`. Establish `hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z'` using `fun z' => by`.

Distinguish the cases in `h : z' ∈ T`. Take `⟨x', hx'⟩` from `R.surj z' h.1.1 (fun hJ => h.2 hJ.2)`. Conclude with `⟨x', fun _ => hx'⟩`. Conclude with `⟨x, fun h' => absurd h' h⟩`. Use `choose xc hxc using hex`.

Establish `hxcW : ∀ z' ∈ T, xc z' ∉ interior S` using `fun z' hz' hW => hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))`. Establish `: NeBot (𝓝[T] z)` using `mem_closure_iff_nhdsWithin_neBot.1 hzT`. Take `⟨x', hx'⟩` from `exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))`. Establish `hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) | ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩}`. Use `isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)` and prove the remaining obligations.

Take `⟨u, hu, v, hv, huv⟩` from `mem_nhds_prod_iff.1 ht`. Establish `hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x'` using `inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)`. Establish `hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z)` using `mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)`. Take `⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩` from `clusterPt_iff_nonempty.1 hx' hU hV`. Use `⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩` and prove the remaining obligations.

Conclude with `blockProportional_of_sameOrbit (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))`. Establish `horb : SameOrbit (R.lift x' x') z` using `sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop`. Establish `hxx' : x = x'` using `R.inj x x' hxJ (sameOrbit_symm_nf horb)`. Substitute `hxx'` using the available equality. Take `⟨_, hyW, z', hz'T, rfl⟩` from `clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW) (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) : xc '' T ∈ map xc (𝓝[T] z))`.

Conclude with `hxcW z' hz'T hyW`.
-/
theorem interior_eq_empty (hND : NonvanishingDense.Statement) (R : AnRes P J e) (hP : IsArithVar P (e + 1))
    {G : MRing ι} {dG : K → ℕ} (hG : IsMultiHomog G dG) (hGP : G ∉ P) :
    interior {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} = ∅ := by
  set S := {x | eval (R.lift x x) (map (Int.castRingHom ℂ) G) = 0} with hS
  by_contra hne
  obtain ⟨x0, hx0⟩ := nonempty_iff_ne_empty.2 hne

  obtain ⟨x, hxW, hxJ⟩ : ∃ x ∈ interior S, R.lift x x ∉ mcPts J := by
    by_contra! hall
    obtain ⟨j, hj⟩ := R.A.cover x0
    have hopen : IsOpen (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      ((R.A.chart j).isOpen_image_iff_of_subset_source inter_subset_right).2
        (isOpen_interior.inter (R.A.chart j).open_source)
    have hpos : 0 < volume (R.A.chart j '' (interior S ∩ (R.A.chart j).source)) :=
      hopen.measure_pos volume ⟨R.A.chart j x0, x0, ⟨hx0, hj⟩, rfl⟩
    have hsub : R.A.chart j '' (interior S ∩ (R.A.chart j).source) ⊆
        (R.A.chart j).target ∩ (R.A.chart j).symm ⁻¹' {x | R.lift x x ∈ mcPts J} := by
      rintro _ ⟨y, ⟨hyW, hys⟩, rfl⟩
      exact ⟨(R.A.chart j).map_source hys, by simpa [(R.A.chart j).left_inv hys] using hall y hyW⟩
    exact hpos.ne' (measure_mono_null hsub (R.null j))
  set z := R.lift x x with hzdef
  have hzP : z ∈ mcPts P := R.mem x x (R.mem_U x)

  set C := {z' : (Σ k, ι k) → ℂ | ∀ f ∈ J, eval z' (map (Int.castRingHom ℂ) f) = 0} with hC
  have hCc : IsClosed C := by
    simp only [hC, ofPred_forall]
    exact isClosed_iInter fun f => isClosed_iInter fun _ => isClosed_eq (MvPolynomial.continuous_eval _)
      continuous_const
  have hzC : z ∉ C := fun h => hxJ ⟨hzP.1, h⟩
  set T := {z' | z' ∈ mcPts P ∧ eval z' (map (Int.castRingHom ℂ) G) ≠ 0} ∩ Cᶜ with hT
  have hzT : z ∈ closure T := by
    rw [mem_closure_iff_nhds]
    intro t ht
    obtain ⟨w, ⟨hwt, hwC⟩, hw⟩ :=
      mem_closure_iff_nhds.1 (hND K ι P (e + 1) G hP hGP hzP) (t ∩ Cᶜ)
        (inter_mem ht (hCc.isOpen_compl.mem_nhds hzC))
    exact ⟨w, hwt, hw, hwC⟩

  have hex : ∀ z', ∃ x', z' ∈ T → SameOrbit (R.lift x' x') z' := fun z' => by
    by_cases h : z' ∈ T
    · obtain ⟨x', hx'⟩ := R.surj z' h.1.1 (fun hJ => h.2 hJ.2)
      exact ⟨x', fun _ => hx'⟩
    · exact ⟨x, fun h' => absurd h' h⟩
  choose xc hxc using hex
  have hxcW : ∀ z' ∈ T, xc z' ∉ interior S := fun z' hz' hW =>
    hz'.1.2 ((eval_eq_zero_iff_of_sameOrbit hG (hxc z' hz')).1 (show xc z' ∈ S from interior_subset hW))
  have : NeBot (𝓝[T] z) := mem_closure_iff_nhdsWithin_neBot.1 hzT
  obtain ⟨x', hx'⟩ := exists_clusterPt_of_compactSpace (map xc (𝓝[T] z))

  have hprop : (R.lift x' x', z) ∈ {q : ((Σ k, ι k) → ℂ) × ((Σ k, ι k) → ℂ) |
      ∀ k (i i' : ι k), q.1 ⟨k, i⟩ * q.2 ⟨k, i'⟩ = q.1 ⟨k, i'⟩ * q.2 ⟨k, i⟩} := by
    refine isClosed_blockProportional.closure_subset (mem_closure_iff_nhds.2 fun t ht => ?_)
    obtain ⟨u, hu, v, hv, huv⟩ := mem_nhds_prod_iff.1 ht
    have hU : R.U x' ∩ R.lift x' ⁻¹' u ∈ 𝓝 x' :=
      inter_mem ((R.isOpen_U x').mem_nhds (R.mem_U x')) (continuousAt_lift R x' x' (R.mem_U x') hu)
    have hV : xc '' (v ∩ T) ∈ map xc (𝓝[T] z) :=
      mem_map.2 (mem_of_superset (inter_mem_nhdsWithin T hv) fun z' hz' => ⟨z', ⟨hz'.2, hz'.1⟩, rfl⟩)
    obtain ⟨_, ⟨hyU, hyu⟩, z', ⟨hz'v, hz'T⟩, rfl⟩ := clusterPt_iff_nonempty.1 hx' hU hV
    refine ⟨(R.lift x' (xc z'), z'), huv ⟨hyu, hz'v⟩, ?_⟩
    exact blockProportional_of_sameOrbit
      (sameOrbit_trans_nf (R.compat x' (xc z') (xc z') ⟨hyU, R.mem_U _⟩) (hxc z' hz'T))
  have horb : SameOrbit (R.lift x' x') z :=
    sameOrbit_of_blockProportional (R.mem x' x' (R.mem_U x')).1 hzP.1 hprop
  have hxx' : x = x' := R.inj x x' hxJ (sameOrbit_symm_nf horb)
  subst hxx'
  obtain ⟨_, hyW, z', hz'T, rfl⟩ :=
    clusterPt_iff_nonempty.1 hx' (isOpen_interior.mem_nhds hxW)
      (mem_map.2 (mem_of_superset self_mem_nhdsWithin fun z' hz' => ⟨z', hz', rfl⟩) :
        xc '' T ∈ map xc (𝓝[T] z))
  exact hxcW z' hz'T hyW

end AnResNullForm

/- English proof (translation)
Introduce `e K _ ι _ P J R G dG hP hG hGP j`. Establish `h` using `analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG) (AnResNullForm.interior_eq_empty hND R hP hG hGP) j`. Use `measure_mono_null ?_ h` and prove the remaining obligations. Introduce and unpack `a ⟨ha, haS⟩`. Conclude with `⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩`.
-/
theorem AnResNullForm.proof (hND : NonvanishingDense.Statement) : AnResNullForm.Statement := by
  intro e K _ ι _ P J R G dG hP hG hGP j
  have h := analyticNull R.A _ (AnResNullForm.isAnalyticSubset R hG)
    (AnResNullForm.interior_eq_empty hND R hP hG hGP) j
  refine measure_mono_null ?_ h
  rintro a ⟨ha, haS⟩
  exact ⟨(R.A.chart j).symm a, ⟨haS, (R.A.chart j).map_target ha⟩, (R.A.chart j).right_inv ha⟩

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
