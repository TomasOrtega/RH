import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsNeZeroIsStandardSmoothOfRelativeDimension
import ReciprocityTheory.SemistableReduction.AeBlockSphereEvalNeZero
import Development.AbelianVarietyTheory.Proofs.CovolumeBounds.IntegrableMonomialMulConjComplexGaussian
open NumberField Formalism.BasicNotions Formalism.MainNotions ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.Mean4 GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.HeightParts
open AlgebraicGeometry CategoryTheory MeasureTheory Set GlobalTheory.ShFam GlobalTheory.ChernReg GlobalTheory.CxPts GlobalTheory.TrueGeo ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ShFam.Pad GlobalTheory.Toroidal GlobalTheory.ProjVar Formalism.L2.Pj Formalism.L2.Geo GlobalTheory

namespace GlobalTheory.BoundaryNull

open GlobalTheory.CxPts ReciprocityTheory.ChartRestriction.G.DVR.FlatBC

section General

variable {k : Type} [Field k] {Y : Scheme.{0}} [IsIntegral Y] {p : Y ⟶ Sp k} {σ : k →+* ℂ} {d : ℕ}

/- English proof (translation)
Establish `hyU` using `ch.source_subset hys`. Establish `e : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p ch.U) ch.x) = MvPolynomial.eval₂Hom σ (WithLp.ofLp (ch.e y))`. Use `MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_C]`. Rewrite using `[← ev_eq hyU, ev_algX hyU]`.

Simplify using `only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_X']`. Rewrite using `[← ev_eq hyU, ← ch.apply_eq y hys i]`. Rewrite using `[MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← e]`. Both sides reduce to the same expression.
-/
theorem evHom_eval₂Hom (ch : AlgChart p σ d) {y : CxPts p σ} (hys : y ∈ ch.e.source)
    (r : MvPolynomial (Fin d) k) :
    evHom (ch.source_subset hys) (MvPolynomial.eval₂Hom (algX p ch.U) ch.x r) =
      MvPolynomial.eval (WithLp.ofLp (ch.e y)) (MvPolynomial.map σ r) := by
  have hyU := ch.source_subset hys
  have e : (evHom hyU).comp (MvPolynomial.eval₂Hom (algX p ch.U) ch.x) =
      MvPolynomial.eval₂Hom σ (WithLp.ofLp (ch.e y)) := by
    refine MvPolynomial.ringHom_ext (fun a => ?_) (fun i => ?_)
    · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_C]
      rw [← ev_eq hyU, ev_algX hyU]
    · simp only [RingHom.coe_comp, Function.comp_apply, MvPolynomial.eval₂Hom_X']
      rw [← ev_eq hyU, ← ch.apply_eq y hys i]
  rw [MvPolynomial.eval_map, ← MvPolynomial.coe_eval₂Hom, ← e]
  rfl

/- English proof (translation)
Distinguish the cases in `hU : (ch.U : Set Y).Nonempty`. Use `swap`. Establish `: ch.e.source = ∅` using `eq_empty_of_forall_notMem fun y hy => hU ⟨_, mem_ptsIn.1 (ch.source_subset hy)⟩`. Simplify using `[this]`. Use `haveI : Nonempty ch.U := hU.to_subtype`.

Establish `hgU : genericPoint Y ∈ ch.U` using `((genericPoint_spec Y).mem_open_set_iff ch.U.isOpen).2 (by simpa using hU)`. Take `⟨g, hgle, hgmem⟩` from `ch.affine.exists_basicOpen_le (V := ⟨Zᶜ, hZ.isOpen_compl⟩) ⟨genericPoint Y, hg⟩ hgU`. Establish `hg0 : g ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hgmem`.

Use `letI : Algebra (MvPolynomial (Fin d) k) Γ(Y, ch.U) := (MvPolynomial.eval₂Hom (algX p ch.U) ch.x).toAlgebra`. Use `haveI : Algebra.Etale (MvPolynomial (Fin d) k) Γ(Y, ch.U) := ch.etale`. Take `⟨r, hr, c, hc⟩` from `((AffinePoints.faithfulSMul_and_isAlgebraic_of_etale (MvPolynomial (Fin d) k) Γ(Y, ch.U)).2.isAlgebraic g).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hg0)`. Establish `hq : MvPolynomial.map σ r ≠ 0` using `fun h => hr (MvPolynomial.map_injective σ σ.injective (h.trans (map_zero _).symm))`. Establish `hsub : ch.e '' ({y : CxPts p σ | Cartier.under y ∈ Z} ∩ ch.e.source) ⊆ WithLp.ofLp ⁻¹' {z : Fin d → ℂ | MvPolynomial.eval z (MvPolynomial.map σ r) = 0}`.

Introduce and unpack `_ ⟨y, ⟨hyZ, hys⟩, rfl⟩`. Establish `hyU` using `ch.source_subset hys`. Establish `hev : ev p σ ch.U g y = 0`. Assume the negation of the conclusion as `h`. Establish `h'` using `(mem_ptsIn_basicOpen hyU g).2 h`.

Conclude with `hgle (mem_ptsIn.1 h') hyZ`. Establish `h2 : MvPolynomial.eval₂Hom (algX p ch.U) ch.x r = g * c` using `hc`. Use `show MvPolynomial.eval _ _ = 0`. Rewrite using `[← evHom_eval₂Hom ch hys, h2, map_mul, ← ev_eq hyU, hev, zero_mul]`. Use `measure_mono_null hsub ?_` and prove the remaining obligations.

Rewrite using `[(volume_preserving_ofLp_complex (Fin d)).measure_preimage (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet.nullMeasurableSet]`. Use `ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d _ hq` as an intermediate fact. Rewrite `this` using `[MeasureTheory.ae_iff]`. Simplify using `using this`.
-/
theorem volume_chart_image_closed (ch : AlgChart p σ d) {Z : Set Y} (hZ : IsClosed Z)
    (hg : genericPoint Y ∉ Z) :
    MeasureTheory.volume (ch.e '' ({y : CxPts p σ | Cartier.under y ∈ Z} ∩ ch.e.source)) = 0 := by
  by_cases hU : (ch.U : Set Y).Nonempty
  swap
  · have : ch.e.source = ∅ :=
      eq_empty_of_forall_notMem fun y hy => hU ⟨_, mem_ptsIn.1 (ch.source_subset hy)⟩
    simp [this]
  haveI : Nonempty ch.U := hU.to_subtype
  have hgU : genericPoint Y ∈ ch.U :=
    ((genericPoint_spec Y).mem_open_set_iff ch.U.isOpen).2 (by simpa using hU)
  obtain ⟨g, hgle, hgmem⟩ := ch.affine.exists_basicOpen_le (V := ⟨Zᶜ, hZ.isOpen_compl⟩)
    ⟨genericPoint Y, hg⟩ hgU
  have hg0 : g ≠ 0 := by
    rintro rfl
    simp at hgmem
  letI : Algebra (MvPolynomial (Fin d) k) Γ(Y, ch.U) :=
    (MvPolynomial.eval₂Hom (algX p ch.U) ch.x).toAlgebra
  haveI : Algebra.Etale (MvPolynomial (Fin d) k) Γ(Y, ch.U) := ch.etale
  obtain ⟨r, hr, c, hc⟩ := ((AffinePoints.faithfulSMul_and_isAlgebraic_of_etale
    (MvPolynomial (Fin d) k) Γ(Y, ch.U)).2.isAlgebraic g).exists_nonzero_dvd
    (mem_nonZeroDivisors_of_ne_zero hg0)
  have hq : MvPolynomial.map σ r ≠ 0 := fun h =>
    hr (MvPolynomial.map_injective σ σ.injective (h.trans (map_zero _).symm))
  have hsub : ch.e '' ({y : CxPts p σ | Cartier.under y ∈ Z} ∩ ch.e.source) ⊆
      WithLp.ofLp ⁻¹' {z : Fin d → ℂ | MvPolynomial.eval z (MvPolynomial.map σ r) = 0} := by
    rintro _ ⟨y, ⟨hyZ, hys⟩, rfl⟩
    have hyU := ch.source_subset hys
    have hev : ev p σ ch.U g y = 0 := by
      by_contra h
      have h' := (mem_ptsIn_basicOpen hyU g).2 h
      exact hgle (mem_ptsIn.1 h') hyZ
    have h2 : MvPolynomial.eval₂Hom (algX p ch.U) ch.x r = g * c := hc
    show MvPolynomial.eval _ _ = 0
    rw [← evHom_eval₂Hom ch hys, h2, map_mul, ← ev_eq hyU, hev, zero_mul]
  refine measure_mono_null hsub ?_
  rw [(volume_preserving_ofLp_complex (Fin d)).measure_preimage
    (isClosed_eq (MvPolynomial.continuous_eval _) continuous_const).measurableSet.nullMeasurableSet]
  have := ReciprocityTheory.MultiplicativeHeights.ae_eval_ne_zero_of_ne_zero_fin d _ hq
  rw [MeasureTheory.ae_iff] at this
  simpa using this

end General

end GlobalTheory.BoundaryNull

namespace GlobalTheory.BoundaryNull

/- English proof (translation)
Introduce `D O x P _ _ _ c σ ch`. Establish `h` using `volume_chart_image_closed ch (Cartier.CartierDiv.supp (bdPull O.Φ c)).isClosed (Cartier.CartierDiv.genericPoint_notMem_supp _)`. Establish `e : (offBd O.Φ c σ)ᶜ = {y | Cartier.under y ∈ Cartier.CartierDiv.supp (bdPull O.Φ c)}`. Use extensionality with `y`. Simplify using `only [offBd, mem_compl_iff, mem_setOf_eq, not_not]`.

Conclude with `(mem_supp_bdPull O.Φ c _).symm`. Rewrite using `[e]`. Conclude with `h`.
-/
theorem volume_chart_image_compl_offBd : OnCore fun D O _ _ => ∀ c (σ : D.what₂.LL →+* ℂ)
    (ch : AlgChart (O.var c).str σ (O.var c).dim),
    MeasureTheory.volume (ch.e '' ((offBd O.Φ c σ)ᶜ ∩ ch.e.source)) = 0 := by
  intro D O x P _ _ _ c σ ch
  have h := volume_chart_image_closed ch (Cartier.CartierDiv.supp (bdPull O.Φ c)).isClosed
    (Cartier.CartierDiv.genericPoint_notMem_supp _)
  have e : (offBd O.Φ c σ)ᶜ =
      {y | Cartier.under y ∈ Cartier.CartierDiv.supp (bdPull O.Φ c)} := by
    ext y
    simp only [offBd, mem_compl_iff, mem_setOf_eq, not_not]
    exact (mem_supp_bdPull O.Φ c _).symm
  rw [e]
  exact h

end GlobalTheory.BoundaryNull
