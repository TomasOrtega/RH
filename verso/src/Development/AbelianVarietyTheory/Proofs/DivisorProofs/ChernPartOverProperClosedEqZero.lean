import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ExistsIsFlagBundleRankOne
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.RegularAlteration
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OfSwap2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.L2DbarChartMeasureTransfer
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecialFibreNotInClosureOfValuationRing
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
import ReciprocityTheory.AnalyticForms.AnalyticCharts.NullZero
open NumberField MvPolynomial Filter Topology Formalism.BasicNotions Formalism.MainNotions Formalism.DegreeFormula GlobalTheory.FlagPoly GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.CovTest GlobalTheory.Published
open CategoryTheory AlgebraicGeometry ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.ArInt
open scoped Classical
open MeasureTheory GlobalTheory.CxPts GlobalTheory.ChartGlue GlobalTheory.Points
open scoped ENNReal

noncomputable section

namespace GlobalTheory.ChernNull

open Set CxPts
open ReciprocityTheory.ChartRestriction.G.DVR.FlatBC (algX)

/- English proof (translation)
Use `letI := f.toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin D) k) R := hf`. Take `⟨Q, hQ, r, hr⟩` from `(WeilIntegral.isAlgebraic_of_etale (MvPolynomial (Fin D) k) R g).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hg)`. Conclude with `⟨Q, hQ, r, hr⟩`.
-/
theorem exists_poly_dvd {k R : Type} [CommRing k] [IsDomain k] [CommRing R] [IsDomain R] {D : ℕ}
    (f : MvPolynomial (Fin D) k →+* R) (hf : f.Etale) (g : R) (hg : g ≠ 0) :
    ∃ Q : MvPolynomial (Fin D) k, Q ≠ 0 ∧ ∃ r : R, f Q = g * r := by
  letI := f.toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin D) k) R := hf
  obtain ⟨Q, hQ, r, hr⟩ := (WeilIntegral.isAlgebraic_of_etale (MvPolynomial (Fin D) k) R g).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hg)
  exact ⟨Q, hQ, r, hr⟩

/- English proof (translation)
Proceed by induction on `P using MvPolynomial.induction_on`. Use `next a =>`. Simplify using `only [MvPolynomial.eval_C]`. Conclude with `analyticAt_const`. Use `next p q hp hq =>`.

Simplify using `only [map_add]`. Conclude with `hp.add hq`. Use `next p i hp =>`. Simplify using `only [map_mul, MvPolynomial.eval_X]`. Conclude with `hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z)`.
-/
theorem analyticAt_eval {D : ℕ} (P : MvPolynomial (Fin D) ℂ) (z : Fin D → ℂ) :
    AnalyticAt ℂ (fun w : Fin D → ℂ => MvPolynomial.eval w P) z := by
  induction P using MvPolynomial.induction_on
  next a =>
    simp only [MvPolynomial.eval_C]
    exact analyticAt_const
  next p q hp hq =>
    simp only [map_add]
    exact hp.add hq
  next p i hp =>
    simp only [map_mul, MvPolynomial.eval_X]
    exact hp.mul ((ContinuousLinearMap.proj (R := ℂ) (φ := fun _ : Fin D => ℂ) i).analyticAt z)

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨w, hw⟩ : ∃ w, MvPolynomial.eval w P ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Conclude with `hP (MvPolynomial.funext fun x => by simpa using h x)`. Establish `h0` using `ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ (fun z _ => analyticAt_eval P z) ⟨w, mem_univ _, hw⟩`.

Establish `hs : {z : Fin D → ℂ | z ∈ univ ∧ MvPolynomial.eval z P = 0} = {z : Fin D → ℂ | MvPolynomial.eval z P = 0}`. Use extensionality with `z`. Simplify using the standard rewrite rules. Establish `hT : MeasurableSet {z : Fin D → ℂ | MvPolynomial.eval z P = 0}` using `(isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet`. Rewrite `h0` using `[hs]`.

Rewrite `h0` using `[← (volume_preserving_ofLp_complex (Fin D)).measure_preimage hT.nullMeasurableSet]`. Use `measure_mono_null (fun v hv => ?_) h0` and prove the remaining obligations. Conclude with `hv`.
-/
theorem volume_poly_zero (D : ℕ) (P : MvPolynomial (Fin D) ℂ) (hP : P ≠ 0) :
    volume {v : ReciprocityTheory.L2DbarEstimates.V D | MvPolynomial.eval (fun a => v a) P = 0} = 0 := by
  obtain ⟨w, hw⟩ : ∃ w, MvPolynomial.eval w P ≠ 0 := by
    by_contra h
    push_neg at h
    exact hP (MvPolynomial.funext fun x => by simpa using h x)
  have h0 := ReciprocityTheory.AnForm.volume_zero_set_of_analyticOnNhd isOpen_univ isPreconnected_univ
    (fun z _ => analyticAt_eval P z) ⟨w, mem_univ _, hw⟩
  have hs : {z : Fin D → ℂ | z ∈ univ ∧ MvPolynomial.eval z P = 0} =
      {z : Fin D → ℂ | MvPolynomial.eval z P = 0} := by
    ext z
    simp
  have hT : MeasurableSet {z : Fin D → ℂ | MvPolynomial.eval z P = 0} :=
    (isClosed_eq (MvPolynomial.continuous_eval P) continuous_const).measurableSet
  rw [hs] at h0
  rw [← (volume_preserving_ofLp_complex (Fin D)).measure_preimage hT.nullMeasurableSet] at h0
  refine measure_mono_null (fun v hv => ?_) h0
  exact hv

/- English proof (translation)
Use `h.isDomain` as an intermediate fact. Use `h.finite` as an intermediate fact. Establish `hk : RingHom.ker σ = ⊥` using `Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by`. Use extensionality with `n`. Simplify using `[Ideal.mem_comap, RingHom.mem_ker])`.

Use `(injective_iff_map_eq_zero σ).2 fun a ha => ?_` and prove the remaining obligations. Establish `: a ∈ RingHom.ker σ` using `ha`. Rewrite `this` using `[hk, Ideal.mem_bot]`. Then use the resulting hypothesis.
-/
theorem injective_of_arithVar {k : Type} [CommRing k] {X : Scheme.{0}} {p : X ⟶ Sp k} {D : ℕ}
    (h : IsArithVar p D) (σ : k →+* ℂ) : Function.Injective σ := by
  have := h.isDomain
  have := h.finite
  have hk : RingHom.ker σ = ⊥ := Ideal.eq_bot_of_comap_eq_bot (R := ℤ) (by
    ext n
    simp [Ideal.mem_comap, RingHom.mem_ker])
  refine (injective_iff_map_eq_zero σ).2 fun a ha => ?_
  have : a ∈ RingHom.ker σ := ha
  rwa [hk, Ideal.mem_bot] at this

/- English proof (translation)
Establish `hgU : genericPoint X ∈ U` using `((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)`. Set `W : X.Opens` to `U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩`. Take `⟨g, hgW, hgm⟩` from `hU.exists_basicOpen_le (V := W) ⟨genericPoint X, ⟨hgU, hgen⟩⟩ hgU`. Use `⟨g, fun e => ?_, fun z _ hz hzg => (hgW hzg).2 hz⟩` and prove the remaining obligations. Rewrite `hgm` using `[e, X.basicOpen_zero]`.

Conclude with `hgm`.
-/
theorem exists_sec_vanish {X : Scheme.{0}} [IsIntegral X] {U : X.Opens} (hU : IsAffineOpen U)
    (hne : (U : Set X).Nonempty) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z) :
    ∃ g : Γ(X, U), g ≠ 0 ∧ ∀ z ∈ U, z ∈ Z → z ∉ X.basicOpen g := by
  have hgU : genericPoint X ∈ U :=
    ((genericPoint_spec X).mem_open_set_iff U.isOpen).2 (by simpa using hne)
  let W : X.Opens := U ⊓ ⟨Zᶜ, hZ.isOpen_compl⟩
  obtain ⟨g, hgW, hgm⟩ := hU.exists_basicOpen_le (V := W) ⟨genericPoint X, ⟨hgU, hgen⟩⟩ hgU
  refine ⟨g, fun e => ?_, fun z _ hz hzg => (hgW hzg).2 hz⟩
  rw [e, X.basicOpen_zero] at hgm
  exact hgm

/- English proof (translation)
Break down `c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩` into its components or cases. Simplify using `[hs]`. Establish `hne : (c.U : Set X).Nonempty` using `⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩`. Use `haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩`. Use `h.isDomain` as an intermediate fact.

Take `⟨g, hg0, hgZ⟩` from `exists_sec_vanish c.affine hne hZ hgen`. Take `⟨Q, hQ, r, hQr⟩` from `exists_poly_dvd _ c.etale g hg0`. Establish `hP : MvPolynomial.map σ Q ≠ 0` using `fun e => hQ (MvPolynomial.map_injective σ (injective_of_arithVar h σ) (by rw [e, map_zero]))`. Use `measure_mono_null ?_ (volume_poly_zero D _ hP)` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨hys, hyZ⟩, rfl⟩`.

Establish `hyU` using `c.source_subset hys`. Establish `hgy : ev p σ c.U g y = 0`. Assume the negation of the conclusion as `hne'`. Conclude with `hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))`. Establish `hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) = MvPolynomial.eval₂Hom σ (fun a => c.e y a)`.

Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)` and prove the remaining obligations. Simplify using `[← ev_eq hyU, ev_algX hyU]`. Simplify using `[← ev_eq hyU, c.apply_eq y hys]`. Use `congrArg (fun F => F Q) hcomp` as an intermediate fact. Simplify using `only [RingHom.comp_apply] at this`.

Use `show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0`. Rewrite using `[MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy, zero_mul]`.
-/
theorem chart_null {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k}
    {D : ℕ} (h : IsArithVar p D) {Z : Set X} (hZ : IsClosed Z) (hgen : genericPoint X ∉ Z)
    (σ : k →+* ℂ) (c : AlgChart p σ D) :
    volume (c.e '' (c.e.source ∩ {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z})) = 0 := by
  rcases c.e.source.eq_empty_or_nonempty with hs | ⟨y0, hy0⟩
  · simp [hs]
  have hne : (c.U : Set X).Nonempty := ⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩
  haveI : Nonempty c.U := ⟨⟨_, mem_ptsIn.1 (c.source_subset hy0)⟩⟩
  have := h.isDomain
  obtain ⟨g, hg0, hgZ⟩ := exists_sec_vanish c.affine hne hZ hgen
  obtain ⟨Q, hQ, r, hQr⟩ := exists_poly_dvd _ c.etale g hg0
  have hP : MvPolynomial.map σ Q ≠ 0 := fun e =>
    hQ (MvPolynomial.map_injective σ (injective_of_arithVar h σ) (by rw [e, map_zero]))
  refine measure_mono_null ?_ (volume_poly_zero D _ hP)
  rintro _ ⟨y, ⟨hys, hyZ⟩, rfl⟩
  have hyU := c.source_subset hys
  have hgy : ev p σ c.U g y = 0 := by
    by_contra hne'
    exact hgZ _ (mem_ptsIn.1 hyU) hyZ (mem_ptsIn.1 ((mem_ptsIn_basicOpen hyU g).2 hne'))
  have hcomp : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p c.U) c.x) =
      MvPolynomial.eval₂Hom σ (fun a => c.e y a) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun a => ?_)
    · simp [← ev_eq hyU, ev_algX hyU]
    · simp [← ev_eq hyU, c.apply_eq y hys]
  have := congrArg (fun F => F Q) hcomp
  simp only [RingHom.comp_apply] at this
  show MvPolynomial.eval (fun a => c.e y a) (MvPolynomial.map σ Q) = 0
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← this, hQr, map_mul, ← ev_eq hyU, hgy,
    zero_mul]

/- English proof (translation)
Introduce `k _ X _ p D h Z hZ hgen σ B φ ε`. Establish `hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z}`. Establish `: {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ`. Use extensionality with `y`. Simplify using `[mem_ptsIn]`.

Rewrite using `[this]`. Conclude with `(isOpen_ptsIn _).measurableSet.compl`. Conclude with `GlueCoverNull.glueMeas_null _ _ hA fun c => chart_null h hZ hgen σ c`.
-/
theorem chernPart_over_closed : ∀ {k : Type} [CommRing k] {X : Scheme.{0}} [IsIntegral X] {p : X ⟶ Sp k} {D : ℕ}, IsArithVar p D → ∀ (Z : Set X), IsClosed Z → genericPoint X ∉ Z → ∀ (σ : k →+* ℂ) {B : LB X} (φ : Weight p σ B) (ε : ℤˣ), φ.chernPart D ε {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} = 0 := by
  intro k _ X _ p D h Z hZ hgen σ B φ ε
  have hA : MeasurableSet {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} := by
    have : {y : CxPts p σ | y.1 (IsLocalRing.closedPoint ℂ) ∈ Z} =
        (ptsIn p σ ⟨Zᶜ, hZ.isOpen_compl⟩)ᶜ := by
      ext y
      simp [mem_ptsIn]
    rw [this]
    exact (isOpen_ptsIn _).measurableSet.compl
  exact GlueCoverNull.glueMeas_null _ _ hA fun c => chart_null h hZ hgen σ c

end GlobalTheory.ChernNull
