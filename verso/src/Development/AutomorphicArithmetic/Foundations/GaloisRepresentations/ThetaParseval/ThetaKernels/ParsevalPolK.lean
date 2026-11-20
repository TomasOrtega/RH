import Development.WeilBound.ThetaLifts.Reductions.WeilPairs.ParsevalPol
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ParsevalRationalPairing

set_option synthInstance.maxHeartbeats 200000

section
open scoped TensorProduct Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes MeasureTheory
open GlobalTheory.WeilM GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels
open Formalism.IndefR.DatumF
noncomputable section
namespace PositivityTheory.ThKW.AdelicSchwartzProperties
open PositivityTheory.ThKW.ModulusFactorDefinition PositivityTheory.ThKW.ModulusDerivativeNormalisation GlobalTheory.ThetaTransform
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
open scoped Pointwise in
/- English proof (translation)
Take `⟨μW, 𝓕W, hμW, h𝓕W⟩` from `GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)`. Take `⟨i1, i2, -, -, -, -⟩` from `GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS (nT + nT)`. Use `haveI := i1`. Use `haveI := i2`. Use `haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F`.

Use `haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F`. Use `haveI : BorelSpace (AF F) := ⟨rfl⟩`. Establish `hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _` using `BorelSpace.measurable_eq`. Use `letI mP : MeasurableSpace (VA F N) := borel _`. Use `haveI : BorelSpace (VA F N) := ⟨rfl⟩`.

Use `haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩`. Set `ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N` to `{ e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }`. Set `me : WOF F E nS (nT + nT) ≃ᵐ VA F N` to `ca.toHomeomorph.toMeasurableEquiv`. Establish `hme : ∀ w, me w = e w` using `fun _ => rfl`. Establish `into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)`.

Introduce and unpack `_ ⟨x, rfl⟩`. Take `⟨y, z, h⟩` from `hrat x`. Conclude with `(GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩`. Establish `onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT)`. Introduce `p hp`.

Take `⟨y, z, rfl⟩` from `(GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp`. Take `⟨x, hx⟩` from `hrat' y z`. Establish `: e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x` using `by rw [← hx]; exact e.symm_apply_apply _`. Rewrite using `[show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]`. Conclude with `⟨x, rfl⟩`.

Establish `hν : (μW.map me).IsAddHaarMeasure` using `ca.isAddHaarMeasure_map μW`. Establish `h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me)`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW` using `(MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving`. Establish `hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W` using `Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩`.

Rewrite using `[hpre]`. Conclude with `h𝓕W.nullMeasurableSet.preimage hqmp`. Rewrite using `[me.measurableEmbedding.ae_map_iff] filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩`. Use `⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩` and prove the remaining obligations. Use `show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x`.

Rewrite using `[map_add]`. Introduce `p q hpq`. Set `g : ratLF F E nS (nT + nT)` to `⟨e.symm p, onto' p p.2⟩`. Set `h : ratLF F E nS (nT + nT)` to `⟨e.symm q, onto' q q.2⟩`. Establish `hgh : g ≠ h`.

Introduce `eq`. Apply `hpq` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq` as an intermediate fact. Simplify `this` using `[g, h]`.

Establish `himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)), (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W)`. Introduce `r k hk`. Rewrite using `[← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]`. Use `Set.image_congr fun w _ => ?_` and prove the remaining obligations. Use `show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)`.

Rewrite using `[map_add, hk, LinearEquiv.apply_symm_apply]`. Use `show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)`. Rewrite using `[himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply, me.preimage_image]`. Conclude with `h𝓕W.aedisjoint hgh`. Establish `key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ → ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧ ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N), ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) = (c : ℂ) * ∫ x, Φ₁ x * st …`.

Introduce and unpack `m rfl`. Conclude with `_root_.PositivityTheory.ThKW.ParsevalPolarization.parseval_rational_pairing hB N (μW.map me) hν (me '' 𝓕W) h𝓕`. Take `⟨μN, c, hμN, hc, hK⟩` from `key _ hb`. Use `⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]`.

Both sides reduce to the same expression.
-/
theorem parseval_pol_k {σ : E →ₐ[F] E} {B : Base F E} (hB : _root_.UpperTheory.TP.W.GoodK σ B) {nS nT : ℕ} (N : ℕ)
    (e : WOF F E nS (nT + nT) ≃ₗ[AF F] VA F N) (hec : Continuous e) (hes : Continuous e.symm)
    (hrat : ∀ x : Matrix (Fin (nT + nT)) (Fin nS) E, ∃ y z : Fin N → F,
        e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z))
    (hrat' : ∀ y z : Fin N → F, ∃ x : Matrix (Fin (nT + nT)) (Fin nS) E, e (ratWF x) = (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z)) :
    ∃ (μN : Measure (Fin N → AF F)) (μW : Measure (WOF F E nS (nT + nT))) (𝓕W : Set (WOF F E nS (nT + nT))) (c : ℝ),
      μN.IsAddHaarMeasure ∧ μW.IsAddHaarMeasure ∧ IsAddFundamentalDomain (ratLF F E nS (nT + nT)) 𝓕W μW ∧ 0 < c ∧
      ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
        ∫ w in 𝓕W, thV B.ψ Φ₁ (e w) * starRingEnd ℂ (thV B.ψ Φ₂ (e w)) ∂μW =
          (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μN := by
  obtain ⟨μW, 𝓕W, hμW, h𝓕W⟩ := GlobalTheory.TowerFD.exists_fd_any F E nS (nT + nT)
  obtain ⟨i1, i2, -, -, -, -⟩ := GlobalTheory.T.rationalMatrices_discrete_cocompact_adelicMatrixSpace F E nS (nT + nT)
  haveI := i1
  haveI := i2
  haveI : LocallyCompactSpace (AF F) := GlobalTheory.AdelicUnitaryTop.locallyCompact_adele F
  haveI : SecondCountableTopology (AF F) := GlobalTheory.AdelicUnitaryTop.secondCountable_adele F
  haveI : BorelSpace (AF F) := ⟨rfl⟩
  have hb : (MeasurableSpace.pi : MeasurableSpace (Fin N → AF F)) = borel _ := BorelSpace.measurable_eq
  letI mP : MeasurableSpace (VA F N) := borel _
  haveI : BorelSpace (VA F N) := ⟨rfl⟩
  haveI : BorelSpace (WOF F E nS (nT + nT)) := ⟨rfl⟩
  let ca : WOF F E nS (nT + nT) ≃ₜ+ VA F N :=
    { e.toAddEquiv with continuous_toFun := hec, continuous_invFun := hes }
  let me : WOF F E nS (nT + nT) ≃ᵐ VA F N := ca.toHomeomorph.toMeasurableEquiv
  have hme : ∀ w, me w = e w := fun _ => rfl
  have into : ∀ g ∈ ratLF F E nS (nT + nT), e g ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N) := by
    rintro _ ⟨x, rfl⟩
    obtain ⟨y, z, h⟩ := hrat x
    exact (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).2 ⟨y, z, h⟩
  have onto' : ∀ p ∈ GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N), e.symm p ∈ ratLF F E nS (nT + nT) := by
    intro p hp
    obtain ⟨y, z, rfl⟩ := (GlobalTheory.WeilUnitaryTransport.mem_ratPair_iff _).1 hp
    obtain ⟨x, hx⟩ := hrat' y z
    have : e.symm (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) = ratWF x := by rw [← hx]; exact e.symm_apply_apply _
    rw [show ((fun i => algebraMap F (AF F) (y i)), fun i => algebraMap F (AF F) (z i)) =
      (GlobalTheory.SWQ.rat y, GlobalTheory.SWQ.rat z) from rfl, this]
    exact ⟨x, rfl⟩
  have hν : (μW.map me).IsAddHaarMeasure := ca.isAddHaarMeasure_map μW
  have h𝓕 : IsAddFundamentalDomain (GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (me '' 𝓕W) (μW.map me) := by
    refine ⟨?_, ?_, ?_⟩
    · have hqmp : Measure.QuasiMeasurePreserving me.symm (μW.map me) μW :=
        (MeasurePreserving.mk me.symm.measurable (MeasurableEquiv.map_symm_map me)).quasiMeasurePreserving
      have hpre : me '' 𝓕W = me.symm ⁻¹' 𝓕W :=
        Set.ext fun y => ⟨by rintro ⟨w, hw, rfl⟩; simpa using hw, fun hy => ⟨me.symm y, hy, me.apply_symm_apply y⟩⟩
      rw [hpre]
      exact h𝓕W.nullMeasurableSet.preimage hqmp
    · rw [me.measurableEmbedding.ae_map_iff]
      filter_upwards [h𝓕W.ae_covers] with x ⟨g, hg⟩
      refine ⟨⟨e g, into g g.2⟩, g +ᵥ x, hg, ?_⟩
      show e ((g : WOF F E nS (nT + nT)) + x) = e g + e x
      rw [map_add]
    · intro p q hpq
      let g : ratLF F E nS (nT + nT) := ⟨e.symm p, onto' p p.2⟩
      let h : ratLF F E nS (nT + nT) := ⟨e.symm q, onto' q q.2⟩
      have hgh : g ≠ h := by
        intro eq
        apply hpq
        apply Subtype.ext
        have := congrArg (fun t : ratLF F E nS (nT + nT) => e (t : WOF F E nS (nT + nT))) eq
        simpa [g, h] using this
      have himg : ∀ (r : GlobalTheory.WeilUnitaryTransport.ratPair F (Fin N)) (k : ratLF F E nS (nT + nT)),
          (k : WOF F E nS (nT + nT)) = e.symm r → r +ᵥ me '' 𝓕W = me '' (k +ᵥ 𝓕W) := by
        intro r k hk
        rw [← Set.image_vadd, ← Set.image_vadd, Set.image_image, Set.image_image]
        refine Set.image_congr fun w _ => ?_
        show (r : VA F N) + e w = e ((k : WOF F E nS (nT + nT)) + w)
        rw [map_add, hk, LinearEquiv.apply_symm_apply]
      show MeasureTheory.AEDisjoint (μW.map me) (p +ᵥ me '' 𝓕W) (q +ᵥ me '' 𝓕W)
      rw [himg p g rfl, himg q h rfl, MeasureTheory.AEDisjoint, ← Set.image_inter me.injective, me.map_apply,
        me.preimage_image]
      exact h𝓕W.aedisjoint hgh
  have key : ∀ m : MeasurableSpace (Fin N → AF F), m = borel _ →
      ∃ (μ : @Measure _ m) (c : ℝ), @Measure.IsAddHaarMeasure _ _ _ m μ ∧ 0 < c ∧
        ∀ Φ₁ ∈ schA F (Fin N), ∀ Φ₂ ∈ schA F (Fin N),
          ∫ w in me '' 𝓕W, thV B.ψ Φ₁ w * starRingEnd ℂ (thV B.ψ Φ₂ w) ∂(μW.map me) =
            (c : ℂ) * ∫ x, Φ₁ x * starRingEnd ℂ (Φ₂ x) ∂μ := by
    rintro m rfl
    exact _root_.PositivityTheory.ThKW.ParsevalPolarization.parseval_rational_pairing hB N (μW.map me) hν (me '' 𝓕W) h𝓕
  obtain ⟨μN, c, hμN, hc, hK⟩ := key _ hb
  refine ⟨μN, μW, 𝓕W, c, hμN, hμW, h𝓕W, hc, fun Φ₁ hΦ₁ Φ₂ hΦ₂ => ?_⟩
  rw [← hK Φ₁ hΦ₁ Φ₂ hΦ₂, MeasurableEquiv.restrict_map, MeasurableEquiv.preimage_image, integral_map_equiv]
  rfl
end PositivityTheory.ThKW.AdelicSchwartzProperties
end
end
