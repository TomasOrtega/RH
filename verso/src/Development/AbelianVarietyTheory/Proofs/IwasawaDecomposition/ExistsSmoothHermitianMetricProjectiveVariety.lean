import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.PolyRep
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.GoodTopChernForm
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ChernWeilNumbers
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AntisymmFibrePointTwo
import ReciprocityTheory.AnalyticForms.AnalyticCharts.Partition
open AlgebraicGeometry MvPolynomial GlobalTheory GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.FlagBundle GlobalTheory.HermFrame GlobalTheory.GoodMetric
open ReciprocityTheory.L2DbarEstimates (V)

set_option autoImplicit false
noncomputable section
open Topology Filter
open scoped ContDiff Matrix ComplexOrder

namespace GlobalTheory.GoodMetric.SmoothMetric

/- English proof (translation)
Use `haveI := CxPts.compactSpace σ X.isProjOver`. Establish `hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y` using `fun y => by`. Take `⟨c, hc⟩` from `AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y`. Conclude with `⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩`. Use `choose c hcy hcW using hc`.

Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover (fun y => (c y).e.source) (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)`. Set `pt : Fin t.card → CxPts X.str σ` to `fun j => (t.equivFin.symm j).1`. Set `Lc` to `EuclideanSpace.equiv (Fin X.dim) ℂ`. Set `L` to `Lc.toHomeomorph`. Set `e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ)` to `fun j => (c (pt j)).e.transHomeomorph L`.

Establish `hcov : ∀ y, ∃ j, y ∈ (e j).source`. Introduce `y`. Take `⟨x, hx, hy⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ y))`. Use `⟨t.equivFin ⟨x, hx⟩, ?_⟩` and prove the remaining obligations. Simplify `hy` using `[e, pt]`.

Establish `htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source)`. Introduce `i j`. Establish `ho` using `isOpen_over (c (pt i)).e (c (pt j)).e.open_source`. Establish `hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm) ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)` using `contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)`. Establish `h2` using `(Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)`.

Use `h2.congr_mono ?_ ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `[e, L, Lc]`. Introduce `v hv`. Simplify `hv` using `[e, L, Lc]`.

Introduce `v hv`. Simplify using `using hv`. Take `⟨χ, h0, h1, hs, hd⟩` from `ReciprocityTheory.AnForm.exists_chart_partition e hcov htr`. Use `⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩` and prove the remaining obligations. Take `⟨i, hi⟩` from `hcov y`.

Establish `hi' : y ∈ (c (pt i)).e.source` using `hi`. Use `cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'` and prove the remaining obligations. Establish `h3` using `(hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)`. Use `h3.congr_mono ?_ Set.inter_subset_left` and prove the remaining obligations. Introduce `v hv`.

Simplify using `[e, L, Lc]`.
-/
theorem exists_partition {F : Type} [Field F] (σ : F →+* ℂ) (X : Var F)
    (W : CxPts X.str σ → Set (CxPts X.str σ)) (hWo : ∀ y, IsOpen (W y)) (hW : ∀ y, y ∈ W y) :
    ∃ (n : ℕ) (pt : Fin n → CxPts X.str σ) (χ : Fin n → CxPts X.str σ → ℝ),
      (∀ j y, 0 ≤ χ j y) ∧ (∀ y, ∑ j, χ j y = 1) ∧ (∀ j, tsupport (χ j) ⊆ W (pt j)) ∧
      ∀ j y, CInfAt (χ j) y := by
  classical
  haveI := CxPts.compactSpace σ X.isProjOver
  have hc : ∀ y, ∃ c : AlgChart X.str σ X.dim, y ∈ c.e.source ∧ c.e.source ⊆ W y := fun y => by
    obtain ⟨c, hc⟩ := AlgChart.exists_mem_source (p := X.str) (σ := σ) (D := X.dim) y
    exact ⟨c.restr (W y) (hWo y), ⟨hc, hW y⟩, Set.inter_subset_right⟩
  choose c hcy hcW using hc
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover (fun y => (c y).e.source)
    (fun y => (c y).e.open_source) (fun y _ => Set.mem_iUnion.2 ⟨y, hcy y⟩)
  let pt : Fin t.card → CxPts X.str σ := fun j => (t.equivFin.symm j).1
  let Lc := EuclideanSpace.equiv (Fin X.dim) ℂ
  let L := Lc.toHomeomorph
  let e : Fin t.card → OpenPartialHomeomorph (CxPts X.str σ) (Fin X.dim → ℂ) :=
    fun j => (c (pt j)).e.transHomeomorph L
  have hcov : ∀ y, ∃ j, y ∈ (e j).source := by
    intro y
    obtain ⟨x, hx, hy⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ y))
    refine ⟨t.equivFin ⟨x, hx⟩, ?_⟩
    simpa [e, pt] using hy
  have htr : ∀ i j, ContDiffOn ℝ ∞ (e j ∘ (e i).symm) ((e i).target ∩ (e i).symm ⁻¹' (e j).source) := by
    intro i j
    have ho := isOpen_over (c (pt i)).e (c (pt j)).e.open_source
    have hg : ContDiffOn ℂ ∞ ((c (pt j)).e ∘ (c (pt i)).e.symm)
        ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source) :=
      contDiffOn_euclidean.2 fun a => ReciprocityTheory.L2DbarEstimates.contDiffOn_of_differentiableOn _ _ _ ho
        (differentiableOn_euclidean.1 ((c (pt i)).holo_trans (c (pt j))) a)
    have h2 := (Lc.contDiff.restrict_scalars ℝ).comp_contDiffOn
      ((hg.restrict_scalars ℝ).comp (Lc.symm.contDiff.restrict_scalars ℝ).contDiffOn
        (s := Lc.symm ⁻¹' ((c (pt i)).e.target ∩ (c (pt i)).e.symm ⁻¹' (c (pt j)).e.source)) ?_)
    · refine h2.congr_mono ?_ ?_
      · intro v hv
        simp [e, L, Lc]
      · intro v hv
        simpa [e, L, Lc] using hv
    · intro v hv
      simpa using hv
  obtain ⟨χ, h0, h1, hs, hd⟩ := ReciprocityTheory.AnForm.exists_chart_partition e hcov htr
  refine ⟨t.card, pt, χ, h0, h1, fun j => (hs j).trans (hcW (pt j)), fun j y => ?_⟩
  obtain ⟨i, hi⟩ := hcov y
  have hi' : y ∈ (c (pt i)).e.source := hi
  refine cInfAt_of_chart (c (pt i)).e.open_source (c (pt i)) ?_ hi' hi'
  have h3 := (hd j i).comp (Lc.contDiff.restrict_scalars ℝ).contDiffOn
    (s := (c (pt i)).e.target) (fun v hv => by simpa [e, L, Lc] using hv)
  refine h3.congr_mono ?_ Set.inter_subset_left
  intro v hv
  simp [e, L, Lc]

end GlobalTheory.GoodMetric.SmoothMetric

namespace GlobalTheory.GoodMetric.SmoothMetric

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using cInfAt_const (p := X.str) 0 y`. Consider the case `insert a s ha ih`. Repeatedly rewrite using `[Finset.sum_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem cInfAt_sum {F : Type} [Field F] {σ : F →+* ℂ} {X : Var F} {κ : Type}
    (s : Finset κ) (f : κ → CxPts X.str σ → ℝ) {y : CxPts X.str σ} (h : ∀ j ∈ s, CInfAt (f j) y) :
    CInfAt (fun z => ∑ j ∈ s, f j z) y := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using cInfAt_const (p := X.str) 0 y
  | insert a s ha ih =>
    simp_rw [Finset.sum_insert ha]
    exact (h a (Finset.mem_insert_self a s)).add (ih fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Introduce `F _ σ X ι _ m E`. Use `choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)`. Take `⟨n, pt, χ, h0, h1, hs, hd⟩` from `exists_partition σ X (fun y => ptsIn X.str σ (U y)) (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))`. Set `T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ` to `fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)`. Establish `hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y), Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹)` using `fun j y hy B hB => (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB`.

Establish `hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y), Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹)` using `fun j y hy => hpar j y (subset_tsupport _ hy)`. Use `⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `y _ B hB τ`. Choose the witnesses or unpack the hypotheses as in `⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by`. Assume the negation of the conclusion as `hne`.

Simplify using `only [not_exists, not_not] at hne`. Use `h1 y` as an intermediate fact. Simplify using `[hne] at this`. Establish `hpos : 0 < χ j y` using `lt_of_le_of_ne (h0 j y) (Ne.symm hj)`. Take `⟨ψ, hψ⟩` from `exists_ratVal_hom (X := X) (σ := σ) y`.

Establish `hdet` using `((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ`. Establish `hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef` using `Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_univ j)]`. Use `hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)` and prove the remaining obligations. Conclude with `(Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))`.

Introduce `y _ B hB τ i k`. Establish `key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y`. Introduce `g`. Establish `e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) = fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k)`. Use function extensionality and compare the values at `z`.

Rewrite using `[Matrix.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]`. Rewrite using `[e]`. Use `cInfAt_sum _ _ fun j _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hy : y ∈ tsupport (χ j)`. Establish `hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2)` using `mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)`. Establish `hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l))` using `ContDiff.sum fun l _ => (contDiff_apply ℝ ℂ _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _))`. Use `((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG)) (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)` and prove the remaining obligations. Simplify using `[T, Matrix.mul_apply, Mat.map]`.

Establish `hz : χ j =ᶠ[𝓝 y] fun _ => 0`. Rewrite `hy` using `[tsupport, ← Set.mem_compl_iff]`. Use `filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'`. Conclude with `Function.notMem_support.1 fun h => hz' (subset_closure h)`. Use `(cInfAt_const (p := X.str) 0 y).congr ?_` and prove the remaining obligations.

Use `filter_upwards [hz] with z hz'`. Simplify using `[hz']`. Conclude with `⟨key Complex.reCLM, key Complex.imCLM⟩`. Introduce `y _ B hB B' hB' τ`. Take `⟨ψ, hψ⟩` from `exists_ratVal_hom (X := X) (σ := σ) y`.

Establish `hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹)` using `(Fr.mem_iff hB).1 hB'`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : χ j y = 0`. Simplify using `[hj]`.

Establish `e` using `Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ`. Rewrite `e` using `[mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul]`. Simplify using `only [T]`. Rewrite using `[e, Pi.mul_apply, Matrix.conjTranspose_mul]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`.
-/
theorem exists_isMetricOn_top : ∀ (F : Type) [Field F] (σ : F →+* ℂ) (X : Var F) (ι : Type) [Fintype ι] (m : ι → ℕ)
    (E : Fr (ratOf X) m 0), ∃ H : Mat m X.Fn → CxPts X.str σ → Mat m ℂ, IsMetricOn E ⊤ H := by
  intro F _ σ X ι _ m E
  classical
  choose U A hz hA hU using fun y : CxPts X.str σ => E.loc (under y)
  obtain ⟨n, pt, χ, h0, h1, hs, hd⟩ := exists_partition σ X (fun y => ptsIn X.str σ (U y))
    (fun y => isOpen_ptsIn _) (fun y => mem_ptsIn.2 (hz y))
  let T : Fin n → Mat m X.Fn → CxPts X.str σ → Mat m ℂ := fun j B z => (B * (A (pt j))⁻¹).map (ratVal · z)

  have hpar : ∀ j y, y ∈ tsupport (χ j) → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy B hB =>
    (hU (pt j) (under y) (mem_ptsIn.1 (hs j hy)) B).1 hB
  have hpar' : ∀ j y, χ j y ≠ 0 → ∀ B ∈ E.S (under y),
      Par 0 ((ratOf X).O (under y)).toSubring (B * (A (pt j))⁻¹) := fun j y hy =>
    hpar j y (subset_tsupport _ hy)
  refine ⟨fun B z τ => ∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ), ⟨?_, ?_, ?_⟩⟩
  · intro y _ B hB τ
    obtain ⟨j, hj⟩ : ∃ j, χ j y ≠ 0 := by
      by_contra hne
      simp only [not_exists, not_not] at hne
      have := h1 y
      simp [hne] at this
    have hpos : 0 < χ j y := lt_of_le_of_ne (h0 j y) (Ne.symm hj)
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hdet := ((hpar' j y hj B hB).map_of (ratVal · y) ψ hψ).det_ne τ
    have hPD : (((χ j y : ℝ) : ℂ) • (T j B y τ * (T j B y τ)ᴴ)).PosDef :=
      Matrix.PosDef.smul (Matrix.PosDef.mul_conjTranspose_self _ (Matrix.vecMul_injective_iff_isUnit.2
        ((Matrix.isUnit_iff_isUnit_det _).2 hdet.isUnit))) (by exact_mod_cast hpos)
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ j)]
    refine hPD.add_posSemidef (Matrix.posSemidef_sum _ fun i _ => ?_)
    exact (Matrix.posSemidef_self_mul_conjTranspose _).smul (Complex.zero_le_real.2 (h0 i y))
  · intro y _ B hB τ i k
    have key : ∀ g : ℂ →L[ℝ] ℝ, CInfAt (fun z =>
        g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) y := by
      intro g
      have e : (fun z => g ((∑ j, ((χ j z : ℝ) : ℂ) • (T j B z τ * (T j B z τ)ᴴ)) i k)) =
          fun z => ∑ j ∈ Finset.univ, χ j z * g ((T j B z τ * (T j B z τ)ᴴ) i k) := by
        funext z
        rw [Matrix.sum_apply, map_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [Matrix.smul_apply, smul_eq_mul, ← Complex.real_smul, map_smul, smul_eq_mul]
      rw [e]
      refine cInfAt_sum _ _ fun j _ => ?_
      by_cases hy : y ∈ tsupport (χ j)
      · have hr (x : Fin (m τ) × Fin (m τ)) : RegAt (under y) ((B * (A (pt j))⁻¹) τ x.1 x.2) :=
          mem_O_ratOf.1 ((hpar j y hy B hB τ).1 _ _)
        have hG : ContDiff ℝ (⊤ : ℕ∞) fun w : Fin (m τ) × Fin (m τ) → ℂ => ∑ l, w (i, l) * star (w (k, l)) :=
          ContDiff.sum fun l _ => (contDiff_apply ℝ ℂ _).mul (Complex.conjCLE.contDiff.comp (contDiff_apply ℝ ℂ _))
        refine ((hd j y).comp₂ (cInfAt_ratVal hr (g.contDiff.comp hG))
          (contDiff_fst.mul contDiff_snd)).congr (Eventually.of_forall fun z => ?_)
        simp [T, Matrix.mul_apply, Mat.map]
      · have hz : χ j =ᶠ[𝓝 y] fun _ => 0 := by
          rw [tsupport, ← Set.mem_compl_iff] at hy
          filter_upwards [isClosed_closure.isOpen_compl.mem_nhds hy] with z hz'
          exact Function.notMem_support.1 fun h => hz' (subset_closure h)
        refine (cInfAt_const (p := X.str) 0 y).congr ?_
        filter_upwards [hz] with z hz'
        simp [hz']
    exact ⟨key Complex.reCLM, key Complex.imCLM⟩
  · intro y _ B hB B' hB' τ
    obtain ⟨ψ, hψ⟩ := exists_ratVal_hom (X := X) (σ := σ) y
    have hBB : Par 0 ((ratOf X).O (under y)).toSubring (B' * B⁻¹) := (Fr.mem_iff hB).1 hB'
    simp only [Finset.mul_sum, Finset.sum_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    by_cases hj : χ j y = 0
    · simp [hj]
    have e := Par.map_mul_of hBB (hpar' j y hj B hB) (ratVal · y) ψ hψ
    rw [mul_assoc, ← mul_assoc B⁻¹, Mat.inv_mul (Fr.det_ne hB), one_mul] at e
    simp only [T]
    rw [e, Pi.mul_apply, Matrix.conjTranspose_mul]
    simp only [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]

end GlobalTheory.GoodMetric.SmoothMetric
