import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsLevMeas
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TransferOn
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CartFrSgn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HarishChandraFinite
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.AdmissibleDiscreteSeriesOfHasParam
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.HarishChandraModulesOn
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.HasDRepIffHasDerivAt
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisGeometry₂.HoweUnram
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ThetaChainStageFiniteLevelEqProductLocalLevelsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.TwistedChainCoefficientSupportedPrincipalLevelStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.IntegralSplitFinitePlaceFubiniStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ConjPlEqCP
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FlatIntegrandLocalFactorSplitsTwistPlaceStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum
open scoped TensorProduct InnerProductSpace ComplexConjugate
open GlobalTheory.ChainOnto GlobalTheory.ChainTw
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (SplitProj IsProjAt IsIdemOf LiftsChar rdA grpCo frCo gAt)
open GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection (Blocks parahoric datum)
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.ChainTw.Peel

/- English proof (translation)
Introduce `hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz hlev`. Establish `hhaar : s.ν.IsHaarMeasure`. Take `⟨hr, -, hfl⟩` from `hs`. Conclude with `hfl.haar`. Establish `: BorelSpace (GA D s.V)` using `⟨rfl⟩`.

Take `⟨-, hmO, hlevIff, -, -, -⟩` from `GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs`. Establish `hmL : MeasurableSet (levSet s)` using `(GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs).1`. Use `set F := flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z with hF`. Establish `hloc` using `GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz`. Use `choose J μ ζ hJo hμ hμJ hζi hζ1 hJiff hζv hFx using hloc`.

Establish `hQPg : ∀ PP ∈ w.Q, PP ∈ c.Pg` using `fun PP h => by rw [hw.union]; exact Finset.mem_union_right _ h`. Establish `hQS : ∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∈ c.S` using `fun PP h => Finset.mem_image_of_mem _ (hQPg PP h)`. Establish `hinj` using `GlobalTheory.LevelPlaces.injOn_under D c hw.com`. Set `cond : Pl D.host.E → GA D s.V → Prop` to `fun PP g => gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L`. Set `ET : Finset (Pl D.host.E) → Set (GA D s.V)` to `fun T => intOff c s ∩ {g | ∀ PP ∈ T, cond PP g}`.

Establish `hET : ∀ T, T ⊆ w.Q → MeasurableSet (ET T)`. Introduce `T hT`. Establish `e : {g : GA D s.V | ∀ PP ∈ T, cond PP g} = ⋂ PP ∈ T, {g | cond PP g}` using `by ext g; simp`. Use `hmO.inter ?_` and prove the remaining obligations. Rewrite using `[e]`.

Use `Finset.measurableSet_biInter T fun PP hPP => ?_` and prove the remaining obligations. Establish `e2 : {g : GA D s.V | cond PP g} = (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F))) ⁻¹' (J PP (hT hPP) : Set _)`. Use extensionality with `g`. Conclude with `hJiff PP (hT hPP) g`. Rewrite using `[e2]`.

Conclude with `((hJo PP (hT hPP)).preimage (GlobalTheory.AdelicU.continuous_proj D.sp.cm.sig s.V.gram _)).measurableSet`. Establish `hgAt : ∀ (v v' : HeightOneSpectrum (𝓞 D.host.F)), v' ≠ v → ∀ (x : GA D s.V) y, gAt s.V (.inl v') (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = gAt s.V (.inl v') x`. Introduce `v v' hne x y`. Use `show GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y)) = GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' x)`. Rewrite using `[map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]`.

Establish `hOff : ∀ v ∈ c.S, ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ intOff c s ↔ x ∈ intOff c s`. Introduce `v hv x y`. Use `forall_congr' fun v' => imp_congr_right fun hv' => ?_` and prove the remaining obligations. Establish `hne : v' ≠ v` using `fun h => hv' (h ▸ hv)`. Rewrite using `[map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]`.

Establish `key : ∀ T : Finset (Pl D.host.E), T ⊆ w.Q → IntegrableOn F (ET w.Q) s.ν → IntegrableOn F (ET (w.Q \ T)) s.ν ∧ (z = (D.R.t : ℝ) / 2 → ∫ g in ET (w.Q \ T), F g ∂s.ν = (∏ PP ∈ T, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) * ∫ g in ET w.Q, F g ∂s.ν)`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro _ h; refine ⟨by simpa using h, fun _ => by simp⟩`. Consider the case `insert PP T hPT ih`.

Introduce `hsub hint`. Establish `hPP : PP ∈ w.Q` using `hsub (Finset.mem_insert_self _ _)`. Take `⟨ih1, ih2⟩` from `ih ((Finset.subset_insert _ _).trans hsub) hint`. Use `set v := PP.under (𝓞 D.host.F) with hvdef`. Establish `hE' : MeasurableSet (ET (w.Q \ insert PP T))` using `hET _ Finset.sdiff_subset`.

Establish `hinv : ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ ET (w.Q \ insert PP T) ↔ x ∈ ET (w.Q \ insert PP T)`. Introduce `x y`. Use `and_congr (hOff v (hQS PP hPP) x y) (forall₂_congr fun PP' hPP' => ?_)` and prove the remaining obligations. Establish `hne : PP'.under (𝓞 D.host.F) ≠ v`. Introduce `h`.

Establish `h1` using `Finset.mem_sdiff.1 hPP'`. Conclude with `h1.2 (hinj (hQPg PP' h1.1) (hQPg PP hPP) h ▸ Finset.mem_insert_self _ _)`. Use `show gAt s.V (.inl (PP'.under (𝓞 D.host.F))) (x * _) ∈ _ ↔ gAt s.V (.inl (PP'.under (𝓞 D.host.F))) x ∈ _`. Rewrite using `[hgAt v _ hne]`. Establish `hset : ET (w.Q \ insert PP T) ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ J PP hPP} = ET (w.Q \ T)`.

Use extensionality with `g`. Simplify using `only [ET, Set.mem_inter_iff, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h1, h2⟩, h3⟩`. Use `⟨h1, fun PP' hPP' => ?_⟩` and prove the remaining obligations.

Distinguish the cases in `he : PP' = PP`. Substitute `he` using the available equality. Conclude with `(hJiff PP' hPP g).2 h3`. Use `h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => ?_⟩)` and prove the remaining obligations. Break down `Finset.mem_insert.1 h with h | h` into its components or cases.

Conclude with `he h`. Conclude with `(Finset.mem_sdiff.1 hPP').2 h`. Introduce and unpack `⟨h1, h2⟩`. Use `⟨⟨h1, fun PP' hPP' => h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => (Finset.mem_sdiff.1 hPP').2 (Finset.mem_insert_of_mem h)⟩)⟩, (hJiff PP hPP g).1 (h2 PP ?_)⟩` and prove the remaining obligations. Conclude with `Finset.mem_sdiff.2 ⟨hPP, hPT⟩`.

Establish `hFx' : ∀ x ∈ ET (w.Q \ insert PP T), GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v x = 1 → ∀ y, F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = ζ PP hPP y * F x` using `fun x hx h1 y => hFx PP hPP x hx.1 h1 y`. Establish `hfub` using `GlobalTheory.T.integral_split_finite_place_fubini D s.V s.ν hhaar v (μ PP hPP) (hμ PP hPP) (J PP hPP) (hJo PP hPP) (hμJ PP hPP) (ET (w.Q \ insert PP T)) hE' hinv F (ζ PP hPP) (hζi PP hPP) (hζ1 PP hPP) hFx' (by rw [hset]; exact ih1)`. Use `⟨hfub.1, fun hz2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hfub.2, hset, ih2 hz2, hζv PP hPP hz2, Finset.prod_insert hPT]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsub : levSet s ⊆ ET w.Q` using `fun g hg => ⟨((hlevIff g).1 hg).1, fun PP hPP => ((hlevIff g).1 hg).2 _ (hQS PP hPP)⟩`. Establish `hzero : ∀ g ∈ ET w.Q \ levSet s, F g = 0`. Introduce and unpack `g ⟨⟨h1, h2⟩, h3⟩`. Assume the negation of the conclusion as `hne`. Apply `h3` to reduce the goal to its premises.

Use `(hlevIff g).2 ⟨h1, fun v hv => ?_⟩` and prove the remaining obligations. Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hv`. Rewrite `hPP` using `[hw.union]`. Break down `Finset.mem_union.1 hPP with hP | hP` into its components or cases. Establish `hc : coefW p.ω m X (p.pt φ) g ≠ 0`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Simplify using `only [hF, flatInt, GlobalTheory.Core.Rk.IP.integrand]`. Rewrite using `[show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g from rfl, h0, zero_mul, zero_mul]`. Conclude with `GlobalTheory.T.twistedChain_coefficient_supported_principal_level D hgap c w hw k hk s s' hs hs' p hp m X hX φ g hc _ (by simp only [Twist.S₀, Finset.coe_image]; exact Set.mem_image_of_mem _ hP)`.

Conclude with `h2 PP hP`. Establish `hintR : IntegrableOn F (ET w.Q) s.ν` using `hlev.of_forall_diff_eq_zero (hET _ subset_rfl) hzero`. Establish `hR` using `key w.Q subset_rfl hintR`. Establish `hE0 : ET (w.Q \ w.Q) = intOff c s`. Use extensionality with `g`.

Simplify using `[ET]`. Rewrite `hR` using `[hE0]`. Use `⟨hR.1, fun hz2 => ?_⟩` and prove the remaining obligations. Rewrite using `[hR.2 hz2, setIntegral_eq_of_subset_of_forall_diff_eq_zero (hET _ subset_rfl) hsub hzero]`. Both sides reduce to the same expression.
-/
theorem qPeel_holds : GlobalTheory.Published.UnramifiedDoublingGL → GlobalTheory.Published.CuspRapidDecay → ∀ D : D7, QPeel D := by
  intro hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz hlev
  classical
  have hhaar : s.ν.IsHaarMeasure := by
    obtain ⟨hr, -, hfl⟩ := hs
    exact hfl.haar
  have : BorelSpace (GA D s.V) := ⟨rfl⟩
  obtain ⟨-, hmO, hlevIff, -, -, -⟩ := GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs
  have hmL : MeasurableSet (levSet s) := (GlobalTheory.T.thetaChainStage_finiteLevel_eq_product_localLevels D c w hw k hk.le s hs).1
  set F := flatInt p m X a φ (PiLocalization₂.val u₁ v₁) (PiLocalization₂.val u₂ v₂) z with hF
  have hloc := GlobalTheory.T.flatIntegrand_localFactor_splits_twistPlace hU hC D hgap c w hw k hk s s' hs hs' p hp m X hX a ha u₁ u₂ φ hq v₁ hv₁ v₂ hv₂ z hz
  choose J μ ζ hJo hμ hμJ hζi hζ1 hJiff hζv hFx using hloc

  have hQPg : ∀ PP ∈ w.Q, PP ∈ c.Pg := fun PP h => by rw [hw.union]; exact Finset.mem_union_right _ h
  have hQS : ∀ PP ∈ w.Q, PP.under (𝓞 D.host.F) ∈ c.S := fun PP h => Finset.mem_image_of_mem _ (hQPg PP h)
  have hinj := GlobalTheory.LevelPlaces.injOn_under D c hw.com

  let cond : Pl D.host.E → GA D s.V → Prop := fun PP g => gAt s.V (.inl (PP.under (𝓞 D.host.F))) g ∈ Lev.levG s.V s.β s.L
  let ET : Finset (Pl D.host.E) → Set (GA D s.V) := fun T => intOff c s ∩ {g | ∀ PP ∈ T, cond PP g}
  have hET : ∀ T, T ⊆ w.Q → MeasurableSet (ET T) := by
    intro T hT
    have e : {g : GA D s.V | ∀ PP ∈ T, cond PP g} = ⋂ PP ∈ T, {g | cond PP g} := by ext g; simp
    refine hmO.inter ?_
    rw [e]
    refine Finset.measurableSet_biInter T fun PP hPP => ?_
    have e2 : {g : GA D s.V | cond PP g} = (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram (PP.under (𝓞 D.host.F))) ⁻¹' (J PP (hT hPP) : Set _) := by
      ext g; exact hJiff PP (hT hPP) g
    rw [e2]
    exact ((hJo PP (hT hPP)).preimage (GlobalTheory.AdelicU.continuous_proj D.sp.cm.sig s.V.gram _)).measurableSet

  have hgAt : ∀ (v v' : HeightOneSpectrum (𝓞 D.host.F)), v' ≠ v → ∀ (x : GA D s.V) y,
      gAt s.V (.inl v') (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = gAt s.V (.inl v') x := by
    intro v v' hne x y
    show GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y)) =
      GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v' (GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v' x)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]
  have hOff : ∀ v ∈ c.S, ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ intOff c s ↔ x ∈ intOff c s := by
    intro v hv x y
    refine forall_congr' fun v' => imp_congr_right fun hv' => ?_
    have hne : v' ≠ v := fun h => hv' (h ▸ hv)
    rw [map_mul, GlobalTheory.AdelicU.proj_emb_ne _ _ hne, mul_one]

  have key : ∀ T : Finset (Pl D.host.E), T ⊆ w.Q → IntegrableOn F (ET w.Q) s.ν →
      IntegrableOn F (ET (w.Q \ T)) s.ν ∧ (z = (D.R.t : ℝ) / 2 → ∫ g in ET (w.Q \ T), F g ∂s.ν =
        (∏ PP ∈ T, blockL c k PP * (zinv PP D.R.t ((k + 1) * D.R.t) : ℂ)) * ∫ g in ET w.Q, F g ∂s.ν) := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _ h; refine ⟨by simpa using h, fun _ => by simp⟩
    | insert PP T hPT ih =>
      intro hsub hint
      have hPP : PP ∈ w.Q := hsub (Finset.mem_insert_self _ _)
      obtain ⟨ih1, ih2⟩ := ih ((Finset.subset_insert _ _).trans hsub) hint
      set v := PP.under (𝓞 D.host.F) with hvdef
      have hE' : MeasurableSet (ET (w.Q \ insert PP T)) := hET _ Finset.sdiff_subset
      have hinv : ∀ (x : GA D s.V) y, x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y ∈ ET (w.Q \ insert PP T) ↔
          x ∈ ET (w.Q \ insert PP T) := by
        intro x y
        refine and_congr (hOff v (hQS PP hPP) x y) (forall₂_congr fun PP' hPP' => ?_)
        have hne : PP'.under (𝓞 D.host.F) ≠ v := by
          intro h
          have h1 := Finset.mem_sdiff.1 hPP'
          exact h1.2 (hinj (hQPg PP' h1.1) (hQPg PP hPP) h ▸ Finset.mem_insert_self _ _)
        show gAt s.V (.inl (PP'.under (𝓞 D.host.F))) (x * _) ∈ _ ↔ gAt s.V (.inl (PP'.under (𝓞 D.host.F))) x ∈ _
        rw [hgAt v _ hne]
      have hset : ET (w.Q \ insert PP T) ∩ {g | GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v g ∈ J PP hPP} = ET (w.Q \ T) := by
        ext g
        simp only [ET, Set.mem_inter_iff, Set.mem_setOf_eq]
        constructor
        · rintro ⟨⟨h1, h2⟩, h3⟩
          refine ⟨h1, fun PP' hPP' => ?_⟩
          by_cases he : PP' = PP
          · subst he; exact (hJiff PP' hPP g).2 h3
          · refine h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1, fun h => ?_⟩)
            rcases Finset.mem_insert.1 h with h | h
            · exact he h
            · exact (Finset.mem_sdiff.1 hPP').2 h
        · rintro ⟨h1, h2⟩
          refine ⟨⟨h1, fun PP' hPP' => h2 PP' (Finset.mem_sdiff.2 ⟨(Finset.mem_sdiff.1 hPP').1,
            fun h => (Finset.mem_sdiff.1 hPP').2 (Finset.mem_insert_of_mem h)⟩)⟩, (hJiff PP hPP g).1 (h2 PP ?_)⟩
          exact Finset.mem_sdiff.2 ⟨hPP, hPT⟩
      have hFx' : ∀ x ∈ ET (w.Q \ insert PP T), GlobalTheory.AdelicU.proj D.sp.cm.sig s.V.gram v x = 1 → ∀ y,
          F (x * GlobalTheory.AdelicU.emb D.sp.cm.sig s.V.gram v y) = ζ PP hPP y * F x :=
        fun x hx h1 y => hFx PP hPP x hx.1 h1 y
      have hfub := GlobalTheory.T.integral_split_finite_place_fubini D s.V s.ν hhaar v (μ PP hPP) (hμ PP hPP) (J PP hPP) (hJo PP hPP) (hμJ PP hPP)
        (ET (w.Q \ insert PP T)) hE' hinv F (ζ PP hPP) (hζi PP hPP) (hζ1 PP hPP) hFx' (by rw [hset]; exact ih1)
      refine ⟨hfub.1, fun hz2 => ?_⟩
      rw [hfub.2, hset, ih2 hz2, hζv PP hPP hz2, Finset.prod_insert hPT]
      ring

  have hsub : levSet s ⊆ ET w.Q := fun g hg => ⟨((hlevIff g).1 hg).1, fun PP hPP => ((hlevIff g).1 hg).2 _ (hQS PP hPP)⟩
  have hzero : ∀ g ∈ ET w.Q \ levSet s, F g = 0 := by
    rintro g ⟨⟨h1, h2⟩, h3⟩
    by_contra hne
    apply h3
    refine (hlevIff g).2 ⟨h1, fun v hv => ?_⟩
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hv
    rw [hw.union] at hPP
    rcases Finset.mem_union.1 hPP with hP | hP
    · have hc : coefW p.ω m X (p.pt φ) g ≠ 0 := by
        intro h0
        apply hne
        simp only [hF, flatInt, GlobalTheory.Core.Rk.IP.integrand]
        rw [show GlobalTheory.Core.Rk.IP.wcoef p.ω m X (p.pt φ) (p.pt φ) g = coefW p.ω m X (p.pt φ) g from rfl, h0, zero_mul, zero_mul]
      exact GlobalTheory.T.twistedChain_coefficient_supported_principal_level D hgap c w hw k hk s s' hs hs' p hp m X hX φ g hc _
        (by simp only [Twist.S₀, Finset.coe_image]; exact Set.mem_image_of_mem _ hP)
    · exact h2 PP hP
  have hintR : IntegrableOn F (ET w.Q) s.ν := hlev.of_forall_diff_eq_zero (hET _ subset_rfl) hzero
  have hR := key w.Q subset_rfl hintR
  have hE0 : ET (w.Q \ w.Q) = intOff c s := by
    ext g; simp [ET]
  rw [hE0] at hR
  refine ⟨hR.1, fun hz2 => ?_⟩
  rw [hR.2 hz2, setIntegral_eq_of_subset_of_forall_diff_eq_zero (hET _ subset_rfl) hsub hzero]
  rfl

end GlobalTheory.ChainTw.Peel
