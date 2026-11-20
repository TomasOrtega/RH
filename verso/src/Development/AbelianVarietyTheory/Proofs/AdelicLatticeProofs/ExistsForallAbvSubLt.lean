import Mathlib

open NumberField IsDedekindDomain
open scoped Matrix WithZero

namespace GlobalTheory.LocalQuad.Approx

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in

/- English proof (translation)
Use `haveI := Fintype.ofFinite ι`. Take `⟨x, hx⟩` from `(AbsoluteValue.denseRange_algebraMap_pi h hv).exists_dist_lt (fun i ↦ WithAbs.toAbs (v i) (z i)) hε`. Use `⟨x, fun i ↦ ?_⟩` and prove the remaining obligations. Establish `hi` using `(dist_pi_lt_iff hε).1 hx i`. Rewrite `hi` using `[dist_eq_norm, WithAbs.norm_eq_abv]`.

Use `hi using 2` and compare the differences between its conclusion and the goal. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt {F : Type*} [Field F] {ι : Type*} [Finite ι]
    {v : ι → AbsoluteValue F ℝ} (h : ∀ i, (v i).IsNontrivial)
    (hv : Pairwise fun i j ↦ ¬(v i).IsEquiv (v j)) (z : ι → F) {ε : ℝ} (hε : 0 < ε) :
    ∃ x : F, ∀ i, v i (z i - x) < ε := by
  classical
  haveI := Fintype.ofFinite ι
  obtain ⟨x, hx⟩ := (AbsoluteValue.denseRange_algebraMap_pi h hv).exists_dist_lt
    (fun i ↦ WithAbs.toAbs (v i) (z i)) hε
  refine ⟨x, fun i ↦ ?_⟩
  have hi := (dist_pi_lt_iff hε).1 hx i
  rw [dist_eq_norm, WithAbs.norm_eq_abv] at hi
  convert hi using 2
  rfl

variable {F : Type} [Field F] [NumberField F]

noncomputable def abv (T : Finset (HeightOneSpectrum (𝓞 F))) :
    T ⊕ (F →+* ℝ) → AbsoluteValue F ℝ
  | Sum.inl v => NumberField.HeightOneSpectrum.adicAbv F v.1
  | Sum.inr σ => (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
The claim follows from `(FinitePlace.norm_embedding v.1 x).symm`.
-/
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_inl (T : Finset (HeightOneSpectrum (𝓞 F))) (v : T) (x : F) :
    _root_.GlobalTheory.LocalQuad.Approx.abv T (Sum.inl v) x = ‖algebraMap F (v.1.adicCompletion F) x‖ :=
  (FinitePlace.norm_embedding v.1 x).symm

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Break down `i with v | σ` into its components or cases. Take `⟨r, hrv, hr0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot`. Use `⟨algebraMap (𝓞 F) F r, (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr0, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `NumberField.HeightOneSpectrum.adicAbv F v.1 _ ≠ 1`. Rewrite using `[← FinitePlace.norm_embedding]`.

Conclude with `((FinitePlace.norm_lt_one_iff_mem F v.1 r).2 hrv).ne`. Conclude with `(InfinitePlace.mk (Complex.ofRealHom.comp σ)).isNontrivial`.
-/
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial (T : Finset (HeightOneSpectrum (𝓞 F)))
    (i : T ⊕ (F →+* ℝ)) : (_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsNontrivial := by
  rcases i with v | σ
  · obtain ⟨r, hrv, hr0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot v.1.ne_bot
    refine ⟨algebraMap (𝓞 F) F r, (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 F) F)).2 hr0, ?_⟩
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ ≠ 1
    rw [← FinitePlace.norm_embedding]
    exact ((FinitePlace.norm_lt_one_iff_mem F v.1 r).2 hrv).ne
  · exact (InfinitePlace.mk (Complex.ofRealHom.comp σ)).isNontrivial

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Introduce `hE`. Establish `h2` using `(hE.le_one_iff (x := (2 : F))).1 (by simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v 2)`. Express the relevant statement in the definitionally equal form `InfinitePlace.mk (Complex.ofRealHom.comp σ) 2 ≤ 1 at h2`. Rewrite `h2` using `[InfinitePlace.apply]`. Establish `hσ2 : σ 2 = 2` using `map_ofNat σ 2`.

Simplify using `only [RingHom.comp_apply, hσ2] at h2`. Evaluate the numerical expressions using `at h2`.
-/
private theorem not_isEquiv_adicAbv_real_place (v : HeightOneSpectrum (𝓞 F)) (σ : F →+* ℝ) :
    ¬(NumberField.HeightOneSpectrum.adicAbv F v).IsEquiv
      (InfinitePlace.mk (Complex.ofRealHom.comp σ)).1 := by
  intro hE
  have h2 := (hE.le_one_iff (x := (2 : F))).1
    (by simpa using NumberField.HeightOneSpectrum.adicAbv_natCast_le_one F v 2)
  change InfinitePlace.mk (Complex.ofRealHom.comp σ) 2 ≤ 1 at h2
  rw [InfinitePlace.apply] at h2
  have hσ2 : σ 2 = 2 := map_ofNat σ 2
  simp only [RingHom.comp_apply, hσ2] at h2
  norm_num at h2

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in
/- English proof (translation)
Introduce and unpack `(v | σ) (w | τ) hne hE`. Establish `hvw : v.1 ≠ w.1` using `fun h ↦ hne (congrArg Sum.inl (Subtype.ext h))`. Establish `hle : ¬v.1.asIdeal ≤ w.1.asIdeal` using `fun hle ↦ hvw (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le w.1.isPrime.ne_top hle))`. Take `⟨r, hrv, hrw⟩` from `Set.not_subset.1 hle`. Establish `h1` using `hE.lt_one_iff (x := algebraMap (𝓞 F) F r)`.

Express the relevant statement in the definitionally equal form `NumberField.HeightOneSpectrum.adicAbv F v.1 _ < 1 ↔ NumberField.HeightOneSpectrum.adicAbv F w.1 _ < 1 at h1`. Rewrite `h1` using `[← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding, FinitePlace.norm_lt_one_iff_mem, FinitePlace.norm_lt_one_iff_mem]`. Conclude with `hrw (h1.1 hrv)`. Conclude with `not_isEquiv_adicAbv_real_place v.1 τ hE`. Conclude with `not_isEquiv_adicAbv_real_place w.1 σ hE.symm`.

Establish `hmk` using `(InfinitePlace.eq_iff_isEquiv (w := InfinitePlace.mk (Complex.ofRealHom.comp σ)) (v := InfinitePlace.mk (Complex.ofRealHom.comp τ))).2 hE`. Rewrite `hmk` using `[InfinitePlace.mk_eq_iff]`. Establish `key : Complex.ofRealHom.comp σ = Complex.ofRealHom.comp τ`. Break down `hmk with h | h` into its components or cases. Conclude with `h`.

Rewrite using `[← h]`. Use extensionality with `x`. Simplify using `[ComplexEmbedding.conjugate_coe_eq]`. Apply `hne` to reduce the goal to its premises. Use `congr 1`.

Use extensionality with `x`. Simplify using `using congrArg (fun φ : F →+* ℂ ↦ φ x) key`.
-/
theorem _root_.GlobalTheory.LocalQuad.Approx.abv_pairwise (T : Finset (HeightOneSpectrum (𝓞 F))) :
    Pairwise fun i j ↦ ¬(_root_.GlobalTheory.LocalQuad.Approx.abv T i).IsEquiv
      (_root_.GlobalTheory.LocalQuad.Approx.abv T j) := by
  rintro (v | σ) (w | τ) hne hE
  · have hvw : v.1 ≠ w.1 := fun h ↦ hne (congrArg Sum.inl (Subtype.ext h))
    have hle : ¬v.1.asIdeal ≤ w.1.asIdeal := fun hle ↦
      hvw (HeightOneSpectrum.ext (v.1.isMaximal.eq_of_le w.1.isPrime.ne_top hle))
    obtain ⟨r, hrv, hrw⟩ := Set.not_subset.1 hle
    have h1 := hE.lt_one_iff (x := algebraMap (𝓞 F) F r)
    change NumberField.HeightOneSpectrum.adicAbv F v.1 _ < 1 ↔
      NumberField.HeightOneSpectrum.adicAbv F w.1 _ < 1 at h1
    rw [← FinitePlace.norm_embedding, ← FinitePlace.norm_embedding,
      FinitePlace.norm_lt_one_iff_mem, FinitePlace.norm_lt_one_iff_mem] at h1
    exact hrw (h1.1 hrv)
  · exact not_isEquiv_adicAbv_real_place v.1 τ hE
  · exact not_isEquiv_adicAbv_real_place w.1 σ hE.symm
  · have hmk := (InfinitePlace.eq_iff_isEquiv (w := InfinitePlace.mk (Complex.ofRealHom.comp σ))
      (v := InfinitePlace.mk (Complex.ofRealHom.comp τ))).2 hE
    rw [InfinitePlace.mk_eq_iff] at hmk
    have key : Complex.ofRealHom.comp σ = Complex.ofRealHom.comp τ := by
      rcases hmk with h | h
      · exact h
      · rw [← h]
        ext x
        simp [ComplexEmbedding.conjugate_coe_eq]
    apply hne
    congr 1
    ext x
    simpa using congrArg (fun φ : F →+* ℂ ↦ φ x) key

end GlobalTheory.LocalQuad.Approx

open NumberField IsDedekindDomain in
open scoped Matrix WithZero in
variable {F : Type} [Field F] [NumberField F] in

/- English proof (translation)
Rewrite using `[Metric.denseRange_iff]`. Introduce and unpack `⟨a, b⟩ r hr`. Establish `hr2 : 0 < r / 2` using `half_pos hr`. Use `choose y hy using fun v : T ↦ (HeightOneSpectrum.denseRange_algebraMap (K := F) v.1).exists_dist_lt (a v) hr2`. Use `choose q hq using fun σ : F →+* ℝ ↦ exists_rat_btwn (show b σ - r / 2 < b σ + r / 2 by linarith)`.

Set `z : T ⊕ (F →+* ℝ) → F` to `fun i ↦ match i with`. Consider the case `Sum.inl v => y v`. Consider the case `Sum.inr σ => (q σ : F)`. Take `⟨x, hx⟩` from `_root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt (_root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial T) (_root_.GlobalTheory.LocalQuad.Approx.abv_pairwise T) z hr2`. Use `⟨x, ?_⟩` and prove the remaining obligations.

Rewrite using `[Prod.dist_eq, max_lt_iff]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[dist_pi_lt_iff hr]`. Introduce `v`. Establish `hxv` using `hx (Sum.inl v)`.

Rewrite `hxv` using `[_root_.GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[dist_pi_lt_iff hr]`. Introduce `σ`. Establish `hxσ` using `hx (Sum.inr σ)`.

Express the relevant statement in the definitionally equal form `InfinitePlace.mk (Complex.ofRealHom.comp σ) ((q σ : F) - x) < r / 2 at hxσ`. Rewrite `hxσ` using `[InfinitePlace.apply]`. Simplify using `only [RingHom.comp_apply, map_sub, map_ratCast, Complex.ofRealHom_eq_coe] at hxσ`. Rewrite `hxσ` using `[← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]`. Rewrite using `[Real.dist_eq]`.

Establish `hqσ` using `hq σ`. Rewrite `hxσ`, the goal using `[abs_lt]`. Apply the tactic sequence `constructor <;> linarith [hxσ.1, hxσ.2, hqσ.1, hqσ.2]`.
-/
theorem _root_.GlobalTheory.LocalQuad.denseRange_finite_real (F : Type) [Field F] [NumberField F]
    (T : Finset (HeightOneSpectrum (𝓞 F))) :
    DenseRange (fun x : F =>
      ((fun v : T => algebraMap F (v.1.adicCompletion F) x, fun σ : F →+* ℝ => σ x) :
        ((v : T) → v.1.adicCompletion F) × ((F →+* ℝ) → ℝ))) := by
  classical
  rw [Metric.denseRange_iff]
  rintro ⟨a, b⟩ r hr
  have hr2 : 0 < r / 2 := half_pos hr
  choose y hy using fun v : T ↦
    (HeightOneSpectrum.denseRange_algebraMap (K := F) v.1).exists_dist_lt (a v) hr2
  choose q hq using fun σ : F →+* ℝ ↦ exists_rat_btwn (show b σ - r / 2 < b σ + r / 2 by linarith)
  let z : T ⊕ (F →+* ℝ) → F := fun i ↦ match i with
    | Sum.inl v => y v
    | Sum.inr σ => (q σ : F)
  obtain ⟨x, hx⟩ := _root_.GlobalTheory.LocalQuad.Approx.exists_forall_abv_sub_lt
    (_root_.GlobalTheory.LocalQuad.Approx.abv_isNontrivial T)
    (_root_.GlobalTheory.LocalQuad.Approx.abv_pairwise T) z hr2
  refine ⟨x, ?_⟩
  rw [Prod.dist_eq, max_lt_iff]
  constructor
  · rw [dist_pi_lt_iff hr]
    intro v
    have hxv := hx (Sum.inl v)
    rw [_root_.GlobalTheory.LocalQuad.Approx.abv_inl, map_sub, ← dist_eq_norm] at hxv
    calc dist (a v) (algebraMap F (v.1.adicCompletion F) x)
        ≤ dist (a v) (algebraMap F (v.1.adicCompletion F) (y v)) +
          dist (algebraMap F (v.1.adicCompletion F) (y v)) (algebraMap F (v.1.adicCompletion F) x) :=
          dist_triangle _ _ _
      _ < r / 2 + r / 2 := add_lt_add (hy v) hxv
      _ = r := add_halves r
  · rw [dist_pi_lt_iff hr]
    intro σ
    have hxσ := hx (Sum.inr σ)
    change InfinitePlace.mk (Complex.ofRealHom.comp σ) ((q σ : F) - x) < r / 2 at hxσ
    rw [InfinitePlace.apply] at hxσ
    simp only [RingHom.comp_apply, map_sub, map_ratCast, Complex.ofRealHom_eq_coe] at hxσ
    rw [← Complex.ofReal_ratCast, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs] at hxσ
    rw [Real.dist_eq]
    have hqσ := hq σ
    rw [abs_lt] at hxσ ⊢
    constructor <;> linarith [hxσ.1, hxσ.2, hqσ.1, hqσ.2]
