import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.GroupDict
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsSheetCover
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.StatementsProved
import GroundTheory.HeightsAndTheta.Heights.CountingLowerBound.Assembly
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.LatNormGrLatNeZeroOfSpan
open NumberField Matrix MeasureTheory Filter Topology GlobalTheory.CompanionTheory.Ar GlobalTheory.CompanionTheory.Ar.Cusp ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor GroundTheory.Heights₂.Heights.FiniteCovolume
open scoped ENNReal InnerProductSpace

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.Cusp.PeriodOfRiem

section Lattice

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ]

/- English proof (translation)
Establish `h : star (∑ i, r i • w i) = ∑ i, (r i : ℂ) • star (w i)`. Use extensionality with `a`. Simplify using `[star_sum, Finset.sum_apply]`. Unfold `hermForm`. Rewrite using `[h, Matrix.mulVec_sum, dotProduct_sum, Complex.im_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]`.
-/
theorem im_herm_sum (Hm : Matrix (Fin g) (Fin g) ℂ) (z : Fin g → ℂ) {N : Type} [Fintype N] (r : N → ℝ)
    (w : N → Fin g → ℂ) :
    (hermForm Hm z (∑ i, r i • w i)).im = ∑ i, r i * (hermForm Hm z (w i)).im := by
  have h : star (∑ i, r i • w i) = ∑ i, (r i : ℂ) • star (w i) := by
    ext a
    simp [star_sum, Finset.sum_apply]
  unfold hermForm
  rw [h, Matrix.mulVec_sum, dotProduct_sum, Complex.im_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Matrix.mulVec_smul, dotProduct_smul, smul_eq_mul, Complex.im_ofReal_mul]

/- English proof (translation)
Set `b` to `Module.finBasis ℤ Λ`. Establish `hdual : ∀ j, ∃ y, ∀ x, form y x = b.coord j x` using `fun j => by`. Take `⟨y, hy⟩` from `hu.2 (b.coord j)`. Conclude with `⟨y, fun x => by rw [hy]⟩`. Establish `hli : LinearIndependent ℝ (fun i => Q (b i))`.

Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `r hr0 j`. Take `⟨y, hy⟩` from `hdual j`. Establish `h1` using `im_herm_sum Hm (Q y) r (fun i => Q (b i))`. Rewrite `h1` using `[hr0]`.

Simplify using `only [him, hy] at h1`. Simplify `h1.symm` using `[hermForm, Finsupp.single_apply]`. Establish `hcard : Fintype.card (Fin (Module.finrank ℤ Λ)) = Module.finrank ℝ (Fin g → ℂ)`. Simplify using `[hr, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]`. Establish `hspan` using `hli.span_eq_top_of_card_eq_finrank' hcard`.

Set `c` to `Module.Basis.mk hli hspan.ge`. Establish `hc : ∀ i, c i = Q (b i)` using `fun i => by simp [c]`. Establish `hrange : Q.range.toIntSubmodule = Submodule.span ℤ (Set.range c)`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, rfl⟩`.

Rewrite using `[← b.sum_repr x, map_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, ← hc]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨b i, (hc i).symm⟩`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `z hz`.

Use `b.ext_elem fun j => ?_` and prove the remaining obligations. Take `⟨y, hy⟩` from `hdual j`. Establish `h1` using `him y z`. Rewrite `h1` using `[hz, hy]`. Establish `h2 : ((b.coord j z : ℤ) : ℝ) = 0`.

Rewrite using `[← h1]`. Simplify using `[hermForm]`. Simplify using `using h2`. Establish `hd : DiscreteTopology (Submodule.span ℤ (Set.range c))` using `inferInstance`. Rewrite `hd` using `[← hrange]`.

Conclude with `hd`. Rewrite using `[eq_top_iff, ← hspan]`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `⟨b i, rfl⟩`.
-/
theorem lat_of_herm [Module.Free ℤ Λ] [Module.Finite ℤ Λ] (hr : Module.finrank ℤ Λ = 2 * g)
    (form : Λ →ₗ[ℤ] Λ →ₗ[ℤ] ℤ) (hu : Function.Bijective form) (Q : Λ →+ (Fin g → ℂ))
    (Hm : Matrix (Fin g) (Fin g) ℂ)
    (him : ∀ x y, (hermForm Hm (Q x) (Q y)).im = (form x y : ℝ)) :
    Function.Injective Q ∧ DiscreteTopology Q.range ∧ Submodule.span ℝ (Set.range Q) = ⊤ := by
  classical
  let b := Module.finBasis ℤ Λ
  have hdual : ∀ j, ∃ y, ∀ x, form y x = b.coord j x := fun j => by
    obtain ⟨y, hy⟩ := hu.2 (b.coord j)
    exact ⟨y, fun x => by rw [hy]⟩
  have hli : LinearIndependent ℝ (fun i => Q (b i)) := by
    rw [Fintype.linearIndependent_iff]
    intro r hr0 j
    obtain ⟨y, hy⟩ := hdual j
    have h1 := im_herm_sum Hm (Q y) r (fun i => Q (b i))
    rw [hr0] at h1
    simp only [him, hy] at h1
    simpa [hermForm, Finsupp.single_apply] using h1.symm
  have hcard : Fintype.card (Fin (Module.finrank ℤ Λ)) = Module.finrank ℝ (Fin g → ℂ) := by
    simp [hr, Module.finrank_pi_fintype, Complex.finrank_real_complex, mul_comm]
  have hspan := hli.span_eq_top_of_card_eq_finrank' hcard
  let c := Module.Basis.mk hli hspan.ge
  have hc : ∀ i, c i = Q (b i) := fun i => by simp [c]
  have hrange : Q.range.toIntSubmodule = Submodule.span ℤ (Set.range c) := by
    apply le_antisymm
    · rintro _ ⟨x, rfl⟩
      rw [← b.sum_repr x, map_sum]
      refine Submodule.sum_mem _ fun i _ => ?_
      rw [map_zsmul, ← hc]
      exact Submodule.smul_mem _ _ (Submodule.subset_span (Set.mem_range_self i))
    · rw [Submodule.span_le]
      rintro _ ⟨i, rfl⟩
      exact ⟨b i, (hc i).symm⟩
  refine ⟨?_, ?_, ?_⟩
  · rw [injective_iff_map_eq_zero]
    intro z hz
    refine b.ext_elem fun j => ?_
    obtain ⟨y, hy⟩ := hdual j
    have h1 := him y z
    rw [hz, hy] at h1
    have h2 : ((b.coord j z : ℤ) : ℝ) = 0 := by
      rw [← h1]; simp [hermForm]
    simpa using h2
  · have hd : DiscreteTopology (Submodule.span ℤ (Set.range c)) := inferInstance
    rw [← hrange] at hd
    exact hd
  · rw [eq_top_iff, ← hspan]
    refine Submodule.span_mono ?_
    rintro _ ⟨i, rfl⟩
    exact ⟨b i, rfl⟩

/- English proof (translation)
Establish `h : star (W *ᵥ y') = W.map star *ᵥ star y'`. Use extensionality with `a`. Simplify using `[mulVec, dotProduct, star_sum]`. Unfold `hermForm`. Rewrite using `[h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y, Matrix.vecMul_transpose, ]`.
-/
theorem herm_change (Hm W : Matrix (Fin g) (Fin g) ℂ) (y y' : Fin g → ℂ) :
    hermForm (Wᵀ * Hm * W.map star) y y' = hermForm Hm (W *ᵥ y) (W *ᵥ y') := by
  have h : star (W *ᵥ y') = W.map star *ᵥ star y' := by
    ext a
    simp [mulVec, dotProduct, star_sum]
  unfold hermForm
  rw [h, ← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Matrix.dotProduct_mulVec y, Matrix.vecMul_transpose,
    ]

/- English proof (translation)
Establish `h1 : (W.map star)ᴴ = Wᵀ`. Use extensionality with `a b`. Simplify using `[conjTranspose_apply]`. Establish `h2 : (Wᵀ)ᴴ = W.map star`. Use extensionality with `a b`.

Simplify using `[conjTranspose_apply]`. Unfold `Matrix.IsHermitian`. Rewrite using `[conjTranspose_mul, conjTranspose_mul, h1, h2, hH.eq, Matrix.mul_assoc]`.
-/
theorem herm_change_isHermitian {Hm : Matrix (Fin g) (Fin g) ℂ} (hH : Hm.IsHermitian)
    (W : Matrix (Fin g) (Fin g) ℂ) : (Wᵀ * Hm * W.map star).IsHermitian := by
  have h1 : (W.map star)ᴴ = Wᵀ := by
    ext a b; simp [conjTranspose_apply]
  have h2 : (Wᵀ)ᴴ = W.map star := by
    ext a b; simp [conjTranspose_apply]
  unfold Matrix.IsHermitian
  rw [conjTranspose_mul, conjTranspose_mul, h1, h2, hH.eq, Matrix.mul_assoc]

end Lattice

section Diff

variable {X : Type} [NormedAddCommGroup X] [NormedSpace ℂ X]

/- English proof (translation)
Proceed by induction on `u using Finset.induction_on with`. Consider the case `empty => simpa using differentiableOn_const (c := (1 : ℂ))`. Consider the case `insert a u ha ih`. Simplify using `only [Finset.prod_insert ha]`. Conclude with `(h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))`.
-/
theorem diffOn_fprod {ι : Type} (u : Finset ι) {f : ι → X → ℂ} {s : Set X}
    (h : ∀ i ∈ u, DifferentiableOn ℂ (f i) s) : DifferentiableOn ℂ (fun x => ∏ i ∈ u, f i x) s := by
  classical
  induction u using Finset.induction_on with
  | empty => simpa using differentiableOn_const (c := (1 : ℂ))
  | insert a u ha ih =>
    simp only [Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

/- English proof (translation)
Simplify using `only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]`. Use `DifferentiableOn.fun_sum fun σ _ => ?_` and prove the remaining obligations. Conclude with `(differentiableOn_const _).mul (diffOn_fprod Finset.univ fun i _ => hm (σ i) i)`.
-/
theorem diffOn_det {k : ℕ} {s : Set X} (m : X → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) : DifferentiableOn ℂ (fun x => (m x).det) s := by
  simp only [Matrix.det_apply, Units.smul_def, zsmul_eq_mul]
  refine DifferentiableOn.fun_sum fun σ _ => ?_
  exact (differentiableOn_const _).mul (diffOn_fprod Finset.univ fun i _ => hm (σ i) i)

/- English proof (translation)
Simplify using `only [Matrix.adjugate_apply]`. Use `diffOn_det _ fun a c => ?_` and prove the remaining obligations. Distinguish the cases in `ha : a = j`. Substitute `ha` using the available equality. Simplify using `using differentiableOn_const _`.

Simplify `hm a c` using `[Matrix.updateRow_ne ha]`.
-/
theorem diffOn_adjugate {k : ℕ} {s : Set X} (m : X → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (i j : Fin k) :
    DifferentiableOn ℂ (fun x => (m x).adjugate i j) s := by
  simp only [Matrix.adjugate_apply]
  refine diffOn_det _ fun a c => ?_
  by_cases ha : a = j
  · subst ha
    simpa using differentiableOn_const _
  · simpa [Matrix.updateRow_ne ha] using hm a c

/- English proof (translation)
Introduce `i j`. Simplify using `only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]`. Conclude with `((diffOn_det m hm).inv hd).mul (diffOn_adjugate m hm i j)`.
-/
theorem diffOn_inv {k : ℕ} {s : Set X} (m : X → Matrix (Fin k) (Fin k) ℂ)
    (hm : ∀ i j, DifferentiableOn ℂ (fun x => m x i j) s) (hd : ∀ x ∈ s, (m x).det ≠ 0) :
    ∀ i j, DifferentiableOn ℂ (fun x => (m x)⁻¹ i j) s := by
  intro i j
  simp only [Matrix.inv_def, Matrix.smul_apply, Ring.inverse_eq_inv', smul_eq_mul]
  exact ((diffOn_det m hm).inv hd).mul (diffOn_adjugate m hm i j)

end Diff

section Frames

variable {g : ℕ} {Λ : Type} [AddCommGroup Λ]

/- English proof (translation)
Establish `h1 : IsUnit (Matrix.of v)` using `Matrix.linearIndependent_rows_iff_isUnit.1 h`. Establish `h2 : (Matrix.of fun a j => v j a) = (Matrix.of v)ᵀ` using `rfl`. Rewrite using `[h2, det_transpose]`. Conclude with `((Matrix.isUnit_iff_isUnit_det _).1 h1).ne_zero`.
-/
theorem det_ne_of_li {v : Fin g → Fin g → ℂ} (h : LinearIndependent ℂ v) :
    (Matrix.of fun a j => v j a).det ≠ 0 := by
  have h1 : IsUnit (Matrix.of v) := Matrix.linearIndependent_rows_iff_isUnit.1 h
  have h2 : (Matrix.of fun a j => v j a) = (Matrix.of v)ᵀ := rfl
  rw [h2, det_transpose]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 h1).ne_zero

/- English proof (translation)
Establish `hC : Submodule.span ℂ (Set.range Q) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `z _`. Establish `h1 : z ∈ Submodule.span ℝ (Set.range Q)` using `by rw [h]; trivial`. Conclude with `Submodule.span_le_restrictScalars ℝ ℂ _ h1`.

Take `⟨b, hbS, hspan, hli⟩` from `exists_linearIndependent ℂ (Set.range Q)`. Set `bb` to `Module.Basis.mk hli (by simp [hspan, hC])`. Use `haveI : Fintype b := Module.Basis.fintypeIndexOfRankLtAleph0 bb (Module.rank_lt_aleph0 ℂ _)`. Establish `hcard : Fintype.card b = g` using `by simpa using (Module.finrank_eq_card_basis bb).symm`. Set `e : Fin g ≃ b` to `(Fintype.equivFinOfCardEq hcard).symm`.

Use `choose y hy using fun i : b => hbS i.2`. Use `⟨fun j => y (e j), ?_⟩` and prove the remaining obligations. Establish `h2 : (fun j => Q (y (e j))) = (Subtype.val : b → (Fin g → ℂ)) ∘ e`. Use function extensionality and compare the values at `j`. Simplify using `[hy]`.

Rewrite using `[h2]`. Conclude with `hli.comp _ e.injective`.
-/
theorem exists_period_frame (Q : Λ →+ (Fin g → ℂ)) (h : Submodule.span ℝ (Set.range Q) = ⊤) :
    ∃ x : Fin g → Λ, LinearIndependent ℂ (fun j => Q (x j)) := by
  classical
  have hC : Submodule.span ℂ (Set.range Q) = ⊤ := by
    rw [eq_top_iff]
    intro z _
    have h1 : z ∈ Submodule.span ℝ (Set.range Q) := by rw [h]; trivial
    exact Submodule.span_le_restrictScalars ℝ ℂ _ h1
  obtain ⟨b, hbS, hspan, hli⟩ := exists_linearIndependent ℂ (Set.range Q)
  let bb := Module.Basis.mk hli (by simp [hspan, hC])
  haveI : Fintype b := Module.Basis.fintypeIndexOfRankLtAleph0 bb (Module.rank_lt_aleph0 ℂ _)
  have hcard : Fintype.card b = g := by simpa using (Module.finrank_eq_card_basis bb).symm
  let e : Fin g ≃ b := (Fintype.equivFinOfCardEq hcard).symm
  choose y hy using fun i : b => hbS i.2
  refine ⟨fun j => y (e j), ?_⟩
  have h2 : (fun j => Q (y (e j))) = (Subtype.val : b → (Fin g → ℂ)) ∘ e := by
    funext j
    simp [hy]
  rw [h2]
  exact hli.comp _ e.injective

end Frames

section Eigen

variable {E : Type} [Field E] [NumberField E] {g : ℕ}

/- English proof (translation)
Use extensionality with `x`. Simplify using `[HT.eigSp, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero]`.
-/
theorem eigSp_bridge (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (s : E →+* ℂ) :
    HT.eigSp B s = GlobalTheory.CompanionTheory.Ar.eigSp B (s.comp (algebraMap (𝓞 E) E)) := by
  ext x
  simp [HT.eigSp, GlobalTheory.CompanionTheory.Ar.eigSp, Submodule.mem_iInf, sub_eq_zero]

/- English proof (translation)
Set `bs` to `fun s : E →+* ℂ => Module.finBasis ℂ (HT.eigSp B s)`. Set `es` to `fun s : E →+* ℂ => Finite.equivFinOfCardEq (hdim s).symm`. Set `u : Fin g → Fin g → ℂ` to `fun i => (bs (ty i) (es (ty i) ⟨i, rfl⟩) : Fin g → ℂ)`. Establish `hu : ∀ i, u i ∈ HT.eigSp B (ty i)` using `fun i => (bs (ty i) _).2`. Establish `hsub : ∀ (s : E →+* ℂ) (i : {i // ty i = s}), u i = (bs s (es s i) : Fin g → ℂ)`.

Introduce and unpack `s ⟨i, rfl⟩`. Both sides reduce to the same expression. Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `c hc i₀`.

Take `⟨s, hs⟩ : ∃ s, ty i₀ = s` from `⟨_, rfl⟩`. Establish `h1 : ∑ i, c i • HT.eigProj B s (u i) = 0`. Use `congrArg (HT.eigProj B s) hc` as an intermediate fact. Simplify `this` using `[map_sum]`. Establish `h2 : ∀ i, HT.eigProj B s (u i) = if ty i = s then u i else 0`.

Introduce `i`. Use `split_ifs with h`. Conclude with `HT.LatBasic.eigProj_of_mem (h ▸ hu i)`. Conclude with `HT.LatBasic.eigProj_of_ne (Ne.symm h) (hu i)`. Establish `h3 : ∑ i : {i // ty i = s}, c i • u i = 0`.

Rewrite using `[← Finset.sum_subtype (Finset.univ.filter fun i => ty i = s) (by simp) (fun i => c i • u i), Finset.sum_filter]`. Use `Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1` and prove the remaining obligations. Rewrite using `[h2]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hli : LinearIndependent ℂ (fun i : {i // ty i = s} => (bs s (es s i) : Fin g → ℂ))` using `((bs s).linearIndependent.comp _ (es s).injective).map' (HT.eigSp B s).subtype (Submodule.ker_subtype _)`.

Establish `h4 : ∑ i : {i // ty i = s}, c i • (bs s (es s i) : Fin g → ℂ) = 0`. Rewrite using `[← h3]`. Conclude with `Finset.sum_congr rfl fun i _ => by rw [hsub]`. Conclude with `Fintype.linearIndependent_iff.1 hli (fun i => c i) h4 ⟨i₀, hs⟩`.
-/
theorem exists_adapted (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ))
    (hdim : ∀ s : E →+* ℂ, Module.finrank ℂ (HT.eigSp B s) = Nat.card {i // ty i = s}) :
    ∃ u : Fin g → Fin g → ℂ, (∀ i, u i ∈ HT.eigSp B (ty i)) ∧ LinearIndependent ℂ u := by
  classical
  let bs := fun s : E →+* ℂ => Module.finBasis ℂ (HT.eigSp B s)
  let es := fun s : E →+* ℂ => Finite.equivFinOfCardEq (hdim s).symm
  let u : Fin g → Fin g → ℂ := fun i => (bs (ty i) (es (ty i) ⟨i, rfl⟩) : Fin g → ℂ)
  have hu : ∀ i, u i ∈ HT.eigSp B (ty i) := fun i => (bs (ty i) _).2
  have hsub : ∀ (s : E →+* ℂ) (i : {i // ty i = s}), u i = (bs s (es s i) : Fin g → ℂ) := by
    rintro s ⟨i, rfl⟩
    rfl
  refine ⟨u, hu, ?_⟩
  rw [Fintype.linearIndependent_iff]
  intro c hc i₀
  obtain ⟨s, hs⟩ : ∃ s, ty i₀ = s := ⟨_, rfl⟩
  have h1 : ∑ i, c i • HT.eigProj B s (u i) = 0 := by
    have := congrArg (HT.eigProj B s) hc
    simpa [map_sum] using this
  have h2 : ∀ i, HT.eigProj B s (u i) = if ty i = s then u i else 0 := by
    intro i
    split_ifs with h
    · exact HT.LatBasic.eigProj_of_mem (h ▸ hu i)
    · exact HT.LatBasic.eigProj_of_ne (Ne.symm h) (hu i)
  have h3 : ∑ i : {i // ty i = s}, c i • u i = 0 := by
    rw [← Finset.sum_subtype (Finset.univ.filter fun i => ty i = s) (by simp) (fun i => c i • u i),
      Finset.sum_filter]
    refine Eq.trans (Finset.sum_congr rfl fun i _ => ?_) h1
    rw [h2]
    split_ifs <;> simp
  have hli : LinearIndependent ℂ (fun i : {i // ty i = s} => (bs s (es s i) : Fin g → ℂ)) :=
    ((bs s).linearIndependent.comp _ (es s).injective).map' (HT.eigSp B s).subtype (Submodule.ker_subtype _)
  have h4 : ∑ i : {i // ty i = s}, c i • (bs s (es s i) : Fin g → ℂ) = 0 := by
    rw [← h3]
    exact Finset.sum_congr rfl fun i _ => by rw [hsub]
  exact Fintype.linearIndependent_iff.1 hli (fun i => c i) h4 ⟨i₀, hs⟩

/- English proof (translation)
Establish `hcol : ∀ y : Fin g → ℂ, W *ᵥ y = ∑ i, y i • (fun a => W a i)`. Introduce `y`. Use extensionality with `a`. Simplify using `[mulVec, dotProduct, Finset.sum_apply, mul_comm]`. Establish `hz : z = W *ᵥ (h *ᵥ z)` using `by rw [mulVec_mulVec, hWh, one_mulVec]`.

Establish `hB : B c z = W *ᵥ (fun i => ty i (c : E) * (h *ᵥ z) i)` using `by conv_lhs => rw [hz, hcol]`. Rewrite using `[map_sum, hcol]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, HT.LatBasic.mem_eigSp.1 (hv j) c, smul_smul, mul_comm]`. Rewrite using `[hB, mulVec_mulVec, hhW, one_mulVec]`.
-/
theorem frame_type (B : 𝓞 E →+* Module.End ℂ (Fin g → ℂ)) (ty : Fin g → (E →+* ℂ))
    (W h : Matrix (Fin g) (Fin g) ℂ) (hWh : W * h = 1) (hhW : h * W = 1)
    (hv : ∀ i, (fun a => W a i) ∈ HT.eigSp B (ty i)) (c : 𝓞 E) (z : Fin g → ℂ) (i : Fin g) :
    (h *ᵥ B c z) i = ty i (c : E) * (h *ᵥ z) i := by
  have hcol : ∀ y : Fin g → ℂ, W *ᵥ y = ∑ i, y i • (fun a => W a i) := by
    intro y
    ext a
    simp [mulVec, dotProduct, Finset.sum_apply, mul_comm]
  have hz : z = W *ᵥ (h *ᵥ z) := by rw [mulVec_mulVec, hWh, one_mulVec]
  have hB : B c z = W *ᵥ (fun i => ty i (c : E) * (h *ᵥ z) i) := by
    conv_lhs => rw [hz, hcol]
    rw [map_sum, hcol]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [map_smul, HT.LatBasic.mem_eigSp.1 (hv j) c, smul_smul, mul_comm]
  rw [hB, mulVec_mulVec, hhW, one_mulVec]

end Eigen

section Family

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {g n : ℕ} {Λ : Type} [AddCommGroup Λ] [Module (𝓞 E) Λ]

/- English proof (translation)
Set `M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun t => Matrix.of fun a j => (R t).P (x j) a`. Establish `hM : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U` using `fun i j => differentiableOn_pi.1 (hP (x j)) i`. Establish `hinv` using `diffOn_inv M hM hdet`. Establish `key : ∀ t ∈ U, (R t).B c u = ∑ j, ((M t)⁻¹ *ᵥ u) j • (R t).P (c • x j)`. Introduce `t ht`.

Establish `hu : u = ∑ j, ((M t)⁻¹ *ᵥ u) j • (R t).P (x j)`. Establish `h1 : M t *ᵥ ((M t)⁻¹ *ᵥ u) = u`. Rewrite using `[mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet t ht)), one_mulVec]`. Use `conv_lhs => rw [← h1]`. Use extensionality with `i`.

Simplify using `[mulVec, dotProduct, M, Finset.sum_apply, mul_comm]`. Use `conv_lhs => rw [hu]`. Simplify using `only [map_sum, map_smul, (R t).act]`. Use `DifferentiableOn.congr ?_ key` and prove the remaining obligations. Use `DifferentiableOn.fun_sum fun j _ => ?_` and prove the remaining obligations.

Establish `hc : DifferentiableOn ℂ (fun t => ((M t)⁻¹ *ᵥ u) j) U`. Simplify using `only [mulVec, dotProduct]`. Conclude with `DifferentiableOn.fun_sum fun k _ => (hinv j k).mul_const _`. Conclude with `hc.smul (hP _)`.
-/
theorem act_diff (R : (Fin n → ℂ) → RiemLat E g Λ) (U : Set (Fin n → ℂ)) (x : Fin g → Λ)
    (hP : ∀ y, DifferentiableOn ℂ (fun t => (R t).P y) U)
    (hdet : ∀ t ∈ U, (Matrix.of fun a j => (R t).P (x j) a).det ≠ 0) (c : 𝓞 E) (u : Fin g → ℂ) :
    DifferentiableOn ℂ (fun t => (R t).B c u) U := by
  let M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun a j => (R t).P (x j) a
  have hM : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) U := fun i j => differentiableOn_pi.1 (hP (x j)) i
  have hinv := diffOn_inv M hM hdet
  have key : ∀ t ∈ U, (R t).B c u = ∑ j, ((M t)⁻¹ *ᵥ u) j • (R t).P (c • x j) := by
    intro t ht
    have hu : u = ∑ j, ((M t)⁻¹ *ᵥ u) j • (R t).P (x j) := by
      have h1 : M t *ᵥ ((M t)⁻¹ *ᵥ u) = u := by
        rw [mulVec_mulVec, mul_nonsing_inv _ (isUnit_iff_ne_zero.2 (hdet t ht)), one_mulVec]
      conv_lhs => rw [← h1]
      ext i
      simp [mulVec, dotProduct, M, Finset.sum_apply, mul_comm]
    conv_lhs => rw [hu]
    simp only [map_sum, map_smul, (R t).act]
  refine DifferentiableOn.congr ?_ key
  refine DifferentiableOn.fun_sum fun j _ => ?_
  have hc : DifferentiableOn ℂ (fun t => ((M t)⁻¹ *ᵥ u) j) U := by
    simp only [mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun k _ => (hinv j k).mul_const _
  exact hc.smul (hP _)

/- English proof (translation)
Simplify using `only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]`. Use `DifferentiableOn.fun_sum fun k _ => ?_` and prove the remaining obligations. Establish `hc : DifferentiableOn ℂ (fun _ : Fin n → ℂ => s (HT.dualInt E k)) U` using `differentiableOn_const _`. Conclude with `hc.smul (act_diff R U x hP hdet _ u)`.
-/
theorem proj_diff (R : (Fin n → ℂ) → RiemLat E g Λ) (U : Set (Fin n → ℂ)) (x : Fin g → Λ)
    (hP : ∀ y, DifferentiableOn ℂ (fun t => (R t).P y) U)
    (hdet : ∀ t ∈ U, (Matrix.of fun a j => (R t).P (x j) a).det ≠ 0) (s : E →+* ℂ) (u : Fin g → ℂ) :
    DifferentiableOn ℂ (fun t => HT.eigProj (R t).B s u) U := by
  simp only [HT.eigProj, LinearMap.sum_apply, LinearMap.smul_apply]
  refine DifferentiableOn.fun_sum fun k _ => ?_
  have hc : DifferentiableOn ℂ (fun _ : Fin n → ℂ => s (HT.dualInt E k)) U := differentiableOn_const _
  exact hc.smul (act_diff R U x hP hdet _ u)

end Family

end GlobalTheory.CompanionTheory.Ar.Cusp.PeriodOfRiem

namespace GlobalTheory.CompanionTheory.Ar.Cusp

open PeriodOfRiem

/- English proof (translation)
Introduce `E _ _ _ H D g n ty V R hty hV hF hR t₀ ht₀`. Establish `hPd` using `hF.2`. Establish `hlat : Submodule.span ℝ (Set.range (R t₀).P) = ⊤` using `by haveI := (R t₀).free haveI := (R t₀).fin`. Conclude with `(lat_of_herm (R t₀).rank (R t₀).form (R t₀).unimod (R t₀).P (R t₀).Hm (R t₀).im).2.2`. Take `⟨x, hx⟩` from `exists_period_frame (R t₀).P hlat`.

Establish `hdim : ∀ s : E →+* ℂ, Module.finrank ℂ (HT.eigSp (R t₀).B s) = Nat.card {i // ty i = s}`. Introduce `s`. Rewrite using `[eigSp_bridge, (hR t₀ ht₀).2 s]`. Use `split_ifs with h`. Conclude with `((hty s).1 h).symm`.

Conclude with `((hty s).2 h).symm`. Take `⟨u, hu, hul⟩` from `exists_adapted (R t₀).B ty hdim`. Set `M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun t => Matrix.of fun a j => (R t).P (x j) a`. Establish `hMd : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) V` using `fun i j => differentiableOn_pi.1 (hPd (x j)) i`. Set `V1 : Set (Fin n → ℂ)` to `V ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ`.

Establish `hV1 : IsOpen V1` using `(diffOn_det M hMd).continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton`. Establish `hPd1 : ∀ y, DifferentiableOn ℂ (fun t => (R t).P y) V1` using `fun y => (hPd y).mono Set.inter_subset_left`. Establish `hv : ∀ i, DifferentiableOn ℂ (fun t => HT.eigProj (R t).B (ty i) (u i)) V1` using `fun i => proj_diff R V1 x hPd1 (fun t ht => ht.2) (ty i) (u i)`. Set `Wm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun t => Matrix.of fun a i => HT.eigProj (R t).B (ty i) (u i) a`. Establish `hWd : ∀ a i, DifferentiableOn ℂ (fun t => Wm t a i) V1` using `fun a i => differentiableOn_pi.1 (hv i) a`.

Set `V' : Set (Fin n → ℂ)` to `V1 ∩ (fun t => (Wm t).det) ⁻¹' {0}ᶜ`. Establish `hV' : IsOpen V'` using `(diffOn_det Wm hWd).continuousOn.isOpen_inter_preimage hV1 isOpen_compl_singleton`. Establish `hM0 : (M t₀).det ≠ 0` using `det_ne_of_li hx`. Establish `hW0 : (Wm t₀).det ≠ 0`. Establish `h1 : Wm t₀ = Matrix.of fun a i => u i a`.

Use extensionality with `a i`. Simplify using `only [Wm, Matrix.of_apply, HT.LatBasic.eigProj_of_mem (hu i)]`. Rewrite using `[h1]`. Conclude with `det_ne_of_li hul`. Set `h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ` to `fun t => (Wm t)⁻¹`.

Set `Pf : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ))` to `fun t => (Matrix.mulVecLin (h t)).toAddMonoidHom.comp (R t).P`. Establish `hPf : ∀ t y, Pf t y = h t *ᵥ (R t).P y` using `fun _ _ => rfl`. Establish `hU : ∀ t ∈ V', IsUnit (Wm t).det` using `fun t ht => isUnit_iff_ne_zero.2 ht.2`. Establish `hWh : ∀ t ∈ V', Wm t * h t = 1` using `fun t ht => mul_nonsing_inv _ (hU t ht)`. Establish `hhW : ∀ t ∈ V', h t * Wm t = 1` using `fun t ht => nonsing_inv_mul _ (hU t ht)`.

Establish `hhd : ∀ a b, DifferentiableOn ℂ (fun t => h t a b) V'` using `diffOn_inv Wm (fun a i => (hWd a i).mono Set.inter_subset_left) (fun t ht => ht.2)`. Use `⟨V', Pf, h, hV', ⟨⟨ht₀, hM0⟩, hW0⟩, fun t ht => ht.1.1, ⟨?_, ?_⟩, hhd, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Establish `htV : t ∈ V` using `ht.1.1`. Establish `hpres : ∀ y y', hermForm ((Wm t)ᵀ * (R t).Hm * (Wm t).map star) (Pf t y) (Pf t y') = hermForm (R t).Hm ((R t).P y) ((R t).P y')`.

Introduce `y y'`. Rewrite using `[herm_change, hPf, hPf, mulVec_mulVec, mulVec_mulVec, hWh t ht, one_mulVec, one_mulVec]`. Establish `him : ∀ y y', (hermForm ((Wm t)ᵀ * (R t).Hm * (Wm t).map star) (Pf t y) (Pf t y')).im = ((R t).form y y' : ℝ)` using `fun y y' => by`. Rewrite using `[hpres]`. Conclude with `(R t).im y y'`.

Use `haveI := (R t).free`. Use `haveI := (R t).fin`. Take `⟨i1, i2, i3⟩` from `lat_of_herm (R t).rank (R t).form (R t).unimod (Pf t) _ him`. Use `⟨?_, i1, i2, i3, _, herm_change_isHermitian (R t).herm (Wm t), ?_, fun y y' => ?_⟩` and prove the remaining obligations. Introduce `c y i`.

Rewrite using `[hPf, hPf, (R t).act]`. Conclude with `frame_type (R t).B ty (Wm t) (h t) (hWh t ht) (hhW t ht) (fun i => HT.LatBasic.eigProj_mem _ _ _) c _ i`. Introduce `z hz`. Rewrite using `[herm_change]`. Use `(R t).pos _ fun h0 => hz ?_` and prove the remaining obligations.

Use `congrArg (fun w => h t *ᵥ w) h0` as an intermediate fact. Simplify `this` using `[mulVec_mulVec, hhW t ht]`. Rewrite using `[him, (hR t htV).1]`. Introduce `y`. Rewrite using `[differentiableOn_pi]`.

Introduce `a`. Simplify using `only [hPf, mulVec, dotProduct]`. Conclude with `DifferentiableOn.fun_sum fun b _ => (hhd a b).mul (differentiableOn_pi.1 ((hPd1 y).mono Set.inter_subset_left) b)`. Introduce `t ht`. Conclude with `⟨(Matrix.isUnit_nonsing_inv_det_iff).2 (hU t ht), fun y => rfl⟩`.
-/
theorem period_of_riem : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (g n : ℕ) (ty : Fin g → (E →+* ℂ)) (V : Set (Fin n → ℂ)) (R : (Fin n → ℂ) → RiemLat E g D.La), IsTypeFn H D.p D.q ty → IsOpen V → IsHolFam V R → (∀ t ∈ V, (R t).form = D.EF ∧ ∀ s : E →+* ℂ, Module.finrank ℂ (eigSp (R t).B (s.comp (algebraMap (𝓞 E) E))) = if s (H.rt : E) = H.rt0 then D.p else D.q) → ∀ t₀ ∈ V, ∃ (V' : Set (Fin n → ℂ)) (P : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ))) (h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ), IsOpen V' ∧ t₀ ∈ V' ∧ V' ⊆ V ∧ IsHolPeriods D ty V' P ∧ (∀ a b, DifferentiableOn ℂ (fun t => h t a b) V') ∧ ∀ t ∈ V', IsUnit (h t).det ∧ ∀ x, P t x = h t *ᵥ (R t).P x := by
  intro E _ _ _ H D g n ty V R hty hV hF hR t₀ ht₀
  classical
  have hPd := hF.2
  have hlat : Submodule.span ℝ (Set.range (R t₀).P) = ⊤ := by
    haveI := (R t₀).free
    haveI := (R t₀).fin
    exact (lat_of_herm (R t₀).rank (R t₀).form (R t₀).unimod (R t₀).P (R t₀).Hm (R t₀).im).2.2
  obtain ⟨x, hx⟩ := exists_period_frame (R t₀).P hlat
  have hdim : ∀ s : E →+* ℂ, Module.finrank ℂ (HT.eigSp (R t₀).B s) = Nat.card {i // ty i = s} := by
    intro s
    rw [eigSp_bridge, (hR t₀ ht₀).2 s]
    split_ifs with h
    · exact ((hty s).1 h).symm
    · exact ((hty s).2 h).symm
  obtain ⟨u, hu, hul⟩ := exists_adapted (R t₀).B ty hdim
  let M : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun a j => (R t).P (x j) a
  have hMd : ∀ i j, DifferentiableOn ℂ (fun t => M t i j) V := fun i j => differentiableOn_pi.1 (hPd (x j)) i
  let V1 : Set (Fin n → ℂ) := V ∩ (fun t => (M t).det) ⁻¹' {0}ᶜ
  have hV1 : IsOpen V1 := (diffOn_det M hMd).continuousOn.isOpen_inter_preimage hV isOpen_compl_singleton
  have hPd1 : ∀ y, DifferentiableOn ℂ (fun t => (R t).P y) V1 := fun y => (hPd y).mono Set.inter_subset_left
  have hv : ∀ i, DifferentiableOn ℂ (fun t => HT.eigProj (R t).B (ty i) (u i)) V1 := fun i =>
    proj_diff R V1 x hPd1 (fun t ht => ht.2) (ty i) (u i)
  let Wm : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => Matrix.of fun a i => HT.eigProj (R t).B (ty i) (u i) a
  have hWd : ∀ a i, DifferentiableOn ℂ (fun t => Wm t a i) V1 := fun a i => differentiableOn_pi.1 (hv i) a
  let V' : Set (Fin n → ℂ) := V1 ∩ (fun t => (Wm t).det) ⁻¹' {0}ᶜ
  have hV' : IsOpen V' := (diffOn_det Wm hWd).continuousOn.isOpen_inter_preimage hV1 isOpen_compl_singleton
  have hM0 : (M t₀).det ≠ 0 := det_ne_of_li hx
  have hW0 : (Wm t₀).det ≠ 0 := by
    have h1 : Wm t₀ = Matrix.of fun a i => u i a := by
      ext a i
      simp only [Wm, Matrix.of_apply, HT.LatBasic.eigProj_of_mem (hu i)]
    rw [h1]
    exact det_ne_of_li hul
  let h : (Fin n → ℂ) → Matrix (Fin g) (Fin g) ℂ := fun t => (Wm t)⁻¹
  let Pf : (Fin n → ℂ) → (D.La →+ (Fin g → ℂ)) := fun t => (Matrix.mulVecLin (h t)).toAddMonoidHom.comp (R t).P
  have hPf : ∀ t y, Pf t y = h t *ᵥ (R t).P y := fun _ _ => rfl
  have hU : ∀ t ∈ V', IsUnit (Wm t).det := fun t ht => isUnit_iff_ne_zero.2 ht.2
  have hWh : ∀ t ∈ V', Wm t * h t = 1 := fun t ht => mul_nonsing_inv _ (hU t ht)
  have hhW : ∀ t ∈ V', h t * Wm t = 1 := fun t ht => nonsing_inv_mul _ (hU t ht)
  have hhd : ∀ a b, DifferentiableOn ℂ (fun t => h t a b) V' :=
    diffOn_inv Wm (fun a i => (hWd a i).mono Set.inter_subset_left) (fun t ht => ht.2)
  refine ⟨V', Pf, h, hV', ⟨⟨ht₀, hM0⟩, hW0⟩, fun t ht => ht.1.1, ⟨?_, ?_⟩, hhd, ?_⟩
  · intro t ht
    have htV : t ∈ V := ht.1.1
    have hpres : ∀ y y', hermForm ((Wm t)ᵀ * (R t).Hm * (Wm t).map star) (Pf t y) (Pf t y') =
        hermForm (R t).Hm ((R t).P y) ((R t).P y') := by
      intro y y'
      rw [herm_change, hPf, hPf, mulVec_mulVec, mulVec_mulVec, hWh t ht, one_mulVec, one_mulVec]
    have him : ∀ y y', (hermForm ((Wm t)ᵀ * (R t).Hm * (Wm t).map star) (Pf t y) (Pf t y')).im =
        ((R t).form y y' : ℝ) := fun y y' => by
      rw [hpres]
      exact (R t).im y y'
    haveI := (R t).free
    haveI := (R t).fin
    obtain ⟨i1, i2, i3⟩ := lat_of_herm (R t).rank (R t).form (R t).unimod (Pf t) _ him
    refine ⟨?_, i1, i2, i3, _, herm_change_isHermitian (R t).herm (Wm t), ?_, fun y y' => ?_⟩
    · intro c y i
      rw [hPf, hPf, (R t).act]
      exact frame_type (R t).B ty (Wm t) (h t) (hWh t ht) (hhW t ht)
        (fun i => HT.LatBasic.eigProj_mem _ _ _) c _ i
    · intro z hz
      rw [herm_change]
      refine (R t).pos _ fun h0 => hz ?_
      have := congrArg (fun w => h t *ᵥ w) h0
      simpa [mulVec_mulVec, hhW t ht] using this
    · rw [him, (hR t htV).1]
  · intro y
    rw [differentiableOn_pi]
    intro a
    simp only [hPf, mulVec, dotProduct]
    exact DifferentiableOn.fun_sum fun b _ => (hhd a b).mul
      (differentiableOn_pi.1 ((hPd1 y).mono Set.inter_subset_left) b)
  · intro t ht
    exact ⟨(Matrix.isUnit_nonsing_inv_det_iff).2 (hU t ht), fun y => rfl⟩

end GlobalTheory.CompanionTheory.Ar.Cusp
