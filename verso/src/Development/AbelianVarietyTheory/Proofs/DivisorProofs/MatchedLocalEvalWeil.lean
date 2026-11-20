import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsMaxThOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneMemFinPt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchimedeanLevelSubgroupClosedMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicGroupTopologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiscreteTopologyRationalUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsFundamentalDomain
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsOfMemSpanImage
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaLocalGlobalStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedPairThetaExistsDataStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentNonvanishingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentRegularStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MatchedThetaDescentSmoothStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LevelSubgroupOpenNeighbourhoodStatement
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped TensorProduct Topology

noncomputable section

namespace GlobalTheory.ThKAdmPrime

open MeasureTheory

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v K hKv hKc hKO Φ hΦ`. Use `set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hD`. Take `⟨i1, i2, i3, i4⟩` from `GlobalTheory.T.unitary_adelic_group_topology F E σ (a + a') G.W.J`. Use `haveI := i1`. Use `haveI := i2`.

Use `haveI := i3`. Use `haveI := i4`. Use `haveI := GlobalTheory.T.discreteTopology_rational_unitary F E σ (a + a') G.W.J`. Use `haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩`. Take `⟨𝓕, h𝓕⟩` from `GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)`.

Establish `hμ : (Measure.haar : Measure (UA σ G.W.J)).IsHaarMeasure` using `inferInstance`. Take `⟨L, hL, P, hPΦ, -, -, -, hPL, -⟩` from `GlobalTheory.T.matched_theta_descent_nonvanishing hKP F E σ B a a' G X om om' R Rf hM _ 𝓕 hμ h𝓕 ⟨Φ, hΦ⟩`. Establish `hΦL : ∀ l ∈ L, om' (1, l) Φ = Φ`. Introduce `l hl`. Establish `h` using `hPL ⟨Φ, hΦ⟩ l hl`.

Rewrite `h` using `[hPΦ]`. Conclude with `h`. Take `⟨m, τ, hτ, Q, hQΦ, -, -, -, hQT, -, -⟩` from `GlobalTheory.T.matched_theta_descent_regular hKP F E σ B a a' G X om om' R Rf hM _ 𝓕 hμ h𝓕 ⟨Φ, hΦ⟩`. Establish `hΦτ : GlobalTheory.ThKAdm.HasTypes B om' τ Φ`. Establish `h` using `hQT ⟨Φ, hΦ⟩`.

Rewrite `h` using `[hQΦ]`. Conclude with `h`. Take `⟨T, hTint, x₀, hx₀⟩` from `hΦτ`. Establish `hfinPt : ∀ g ∈ UAt σ G.W (evFin F v), g ∈ GlobalTheory.ThKAdm.FinPt σ G.W`. Introduce `g hg u hu`.

Use `hg u ?_` and prove the remaining obligations. Establish `hu' : u.2 = 0` using `hu`. Express the relevant statement in the definitionally equal form `(Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) u.2 = 0`. Rewrite using `[hu', map_zero]`. Take `⟨-, -, hcomm⟩` from `GlobalTheory.kInf_one_mul_commute_finPt F E σ (a + a') G.W B.emb`.

Establish `hmul : ∀ g h : UA σ G.W.J, ∀ Ψ, om' (1, g * h) Ψ = om' (1, g) (om' (1, h) Ψ)`. Introduce `g h Ψ`. Establish `e : ((1 : UA σ G.V'.J), g * h) = (1, g) * (1, h)` using `by simp`. Rewrite using `[e, map_mul]`. Both sides reduce to the same expression.

Use `set L' := Subgroup.closure ((K : Set (UA σ G.W.J)) ∪ {l | l ∈ L ∧ ∀ h ∈ UAt σ G.W (evFin F v), l * h = h * l}) with hL'`. Establish `hL'lev : GlobalTheory.ThKAdm.IsLevel G.W L'` using `GlobalTheory.T.level_subgroup_open_neighbourhood F E σ (a + a') G.W v L K hL hKv hKO`. Use `set A : Set (Fn F a' (a + a')) := {Ψ | Ψ ∈ D ∧ (∀ l ∈ L', om' (1, l) Ψ = Ψ) ∧ GlobalTheory.ThKAdm.HasTypes B om' τ Ψ} with hA`. Establish `hfin` using `GlobalTheory.T.matched_theta_descent_smooth hKP F E σ B a a' G X om om' R Rf hM L' hL'lev m τ hτ`. Establish `lin` using `GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM`.

Establish `hfg : (Submodule.span ℂ (G.M'.I om' '' A)).FG` using `Module.Finite.iff_fg.1 hfin`. Take `⟨s', hs'A, hs'span⟩` from `(Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg`. Take `⟨t, htA, hts'⟩` from `Finset.subset_set_image_iff.1 hs'A`. Establish `htD : ∀ x ∈ (t : Set (Fn F a' (a + a'))), x ∈ D` using `fun x hx => (htA hx).1`. Use `⟨t, htD, ?_⟩` and prove the remaining obligations.

Introduce `Ψ hΨ hΨK`. Establish `hΨD : Ψ ∈ D`. Use `Submodule.span_le.2 ?_ hΨ` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `(GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).1 v g.1 g.2 Φ hΦ`.

Establish `hΨL' : ∀ l ∈ L', om' (1, l) Ψ = Ψ`. Set `St : Subgroup (UA σ G.W.J)` to `{ carrier := {l | om' (1, l) Ψ = Ψ} one_mem' := by show om' (1, 1) Ψ = Ψ`. Rewrite using `[show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]`. Both sides reduce to the same expression. Use the proof step `mul_mem' := by`.

Introduce `x y hx hy`. Use `show om' (1, x * y) Ψ = Ψ`. Rewrite using `[hmul, hy, hx]`. Use the proof step `inv_mem' := by`. Introduce `x hx`.

Use `show om' (1, x⁻¹) Ψ = Ψ`. Use `conv_lhs => rw [← (show om' (1, x) Ψ = Ψ from hx)]`. Rewrite using `[← hmul, inv_mul_cancel, show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]`. Use `rfl }`. Establish `hle : L' ≤ St`.

Rewrite using `[hL', Subgroup.closure_le]`. Introduce and unpack `l (hl | ⟨hlL, hlc⟩)`. Conclude with `hΨK l hl`. Use `show om' (1, l) Ψ = Ψ`. Establish `hgen : ∀ y ∈ Submodule.span ℂ (Set.range fun g : UAtSub σ G.W (evFin F v) => om' (1, g.1) Φ), om' (1, l) y = y`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨g, rfl⟩` from `hy`. Rewrite using `[← hmul, hlc g.1 g.2, hmul, hΦL l hlL]`.

Consider the case `zero => exact map_zero _`. Consider the case `add x y _ _ hx hy => rw [map_add, hx, hy]`. Consider the case `smul c x _ hx => rw [map_smul, hx]`. Conclude with `hgen Ψ hΨ`. Conclude with `fun l hl => hle hl`.

Establish `hΨτ : GlobalTheory.ThKAdm.HasTypes B om' τ Ψ`. Establish `key : ∀ y ∈ Submodule.span ℂ (Set.range fun g : UAtSub σ G.W (evFin F v) => om' (1, g.1) Φ), ∃ T' : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] Fn F a' (a + a'), (∀ k ∈ KInf σ G.W B.emb, ∀ x, T' (τ k x) = om' (1, k) (T' x)) ∧ T' x₀ = y`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨g, rfl⟩` from `hy`. Use `⟨(om' (1, g.1)).comp T, fun k hk x => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply]`. Rewrite using `[hTint k hk x, ← hmul, ← hmul, hcomm g.1 (hfinPt g.1 g.2) k hk]`. Simplify using `only [LinearMap.comp_apply, hx₀]`.

Consider the case `zero => exact ⟨0, fun k _ x => by simp, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨T1, h1, e1⟩` from `hx`. Take `⟨T2, h2, e2⟩` from `hy`. Conclude with `⟨T1 + T2, fun k hk z => by simp [h1 k hk z, h2 k hk z], by simp [e1, e2]⟩`.

Consider the case `smul c x _ hx`. Take `⟨T1, h1, e1⟩` from `hx`. Conclude with `⟨c • T1, fun k hk z => by simp [h1 k hk z], by simp [e1]⟩`. Take `⟨T', hT', e⟩` from `key Ψ hΨ`. Conclude with `⟨T', hT', x₀, e⟩`.

Establish `hΨA : Ψ ∈ A` using `⟨hΨD, hΨL', hΨτ⟩`. Establish `h1 : G.M'.I om' Ψ ∈ Submodule.span ℂ (G.M'.I om' '' (Submodule.span ℂ (t : Set (Fn F a' (a + a'))) : Set _))`. Establish `h0 : G.M'.I om' Ψ ∈ Submodule.span ℂ (G.M'.I om' '' A)` using `Submodule.subset_span ⟨Ψ, hΨA, rfl⟩`. Rewrite `h0` using `[hs'span, ← hts', Finset.coe_image]`. Conclude with `Submodule.span_mono (Set.image_mono Submodule.subset_span) h0`.

Establish `hle : Submodule.span ℂ (t : Set (Fn F a' (a + a'))) ≤ D` using `Submodule.span_le.2 htD`. Take `⟨w, hw, hIw⟩` from `GlobalTheory.ThetaFacCompl.exists_of_mem_span_image D _ (G.M'.I om') lin hle h1`. Use `⟨w, hw, ?_⟩` and prove the remaining obligations. Establish `e : Ψ - w = Ψ + (-1 : ℂ) • w` using `by rw [neg_one_smul, sub_eq_add_neg]`. Rewrite using `[e, lin Ψ hΨD w (hle hw) (-1), hIw, neg_one_smul, add_neg_cancel]`.
-/
theorem admissible_mod_ker : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Base F E) (a a' : ℕ) (G : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Geo σ a a') (X : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Chars F E) (om : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V G.W) (om' : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Rep σ G.V' G.W) (R : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.RealMaps F a a') (Rf : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.FinMaps F a a'), GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.IsMatched B G X om om' R Rf → ∀ (v : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.Pl F) (K : Subgroup (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)),
    (∀ g ∈ K, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v)) → IsCompact (K : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J)) →
    (∃ O : Set (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J), IsOpen O ∧ (1 : GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UA σ G.W.J) ∈ O ∧
      ∀ g ∈ O, g ∈ GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.UAt σ G.W (GlobalTheory.AdelicU.evFin F v) → g ∈ K) →
    ∀ Φ ∈ (GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁), ∃ s : Finset (GlobalTheory.ThK.Fn F a' (a + a')), (↑s ⊆ ((GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁) : Set (GlobalTheory.ThK.Fn F a' (a + a')))) ∧
      ∀ Ψ ∈ Submodule.span ℂ (Set.range fun g : GlobalTheory.ThK.UAtSub σ G.W (GlobalTheory.AdelicU.evFin F v) => om' (1, g.1) Φ),
        (∀ k ∈ K, om' (1, k) Ψ = Ψ) → ∃ Ψ₀ ∈ Submodule.span ℂ (s : Set (GlobalTheory.ThK.Fn F a' (a + a'))), G.M'.I om' (Ψ - Ψ₀) = 0 := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' R Rf hM v K hKv hKc hKO Φ hΦ
  classical
  set D := GlobalTheory.ThK.PolData B G.M' ⊓ G.M'.So B.ψ B.τ₁ with hD
  obtain ⟨i1, i2, i3, i4⟩ := GlobalTheory.T.unitary_adelic_group_topology F E σ (a + a') G.W.J
  haveI := i1; haveI := i2; haveI := i3; haveI := i4
  haveI := GlobalTheory.T.discreteTopology_rational_unitary F E σ (a + a') G.W.J
  haveI : BorelSpace (UA σ G.W.J) := ⟨rfl⟩
  obtain ⟨𝓕, h𝓕⟩ := GlobalTheory.FundDomDiscrete.exists_isFundamentalDomain (ratU σ G.W.J) (Measure.haar)
  have hμ : (Measure.haar : Measure (UA σ G.W.J)).IsHaarMeasure := inferInstance

  obtain ⟨L, hL, P, hPΦ, -, -, -, hPL, -⟩ :=
    GlobalTheory.T.matched_theta_descent_nonvanishing hKP F E σ B a a' G X om om' R Rf hM _ 𝓕 hμ h𝓕 ⟨Φ, hΦ⟩
  have hΦL : ∀ l ∈ L, om' (1, l) Φ = Φ := by
    intro l hl
    have h := hPL ⟨Φ, hΦ⟩ l hl
    rw [hPΦ] at h
    exact h

  obtain ⟨m, τ, hτ, Q, hQΦ, -, -, -, hQT, -, -⟩ :=
    GlobalTheory.T.matched_theta_descent_regular hKP F E σ B a a' G X om om' R Rf hM _ 𝓕 hμ h𝓕 ⟨Φ, hΦ⟩
  have hΦτ : GlobalTheory.ThKAdm.HasTypes B om' τ Φ := by
    have h := hQT ⟨Φ, hΦ⟩
    rw [hQΦ] at h
    exact h
  obtain ⟨T, hTint, x₀, hx₀⟩ := hΦτ

  have hfinPt : ∀ g ∈ UAt σ G.W (evFin F v), g ∈ GlobalTheory.ThKAdm.FinPt σ G.W := by
    intro g hg u hu
    refine hg u ?_
    have hu' : u.2 = 0 := hu
    change (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.evalV F v) u.2 = 0
    rw [hu', map_zero]
  obtain ⟨-, -, hcomm⟩ := GlobalTheory.kInf_one_mul_commute_finPt F E σ (a + a') G.W B.emb
  have hmul : ∀ g h : UA σ G.W.J, ∀ Ψ, om' (1, g * h) Ψ = om' (1, g) (om' (1, h) Ψ) := by
    intro g h Ψ
    have e : ((1 : UA σ G.V'.J), g * h) = (1, g) * (1, h) := by simp
    rw [e, map_mul]
    rfl

  set L' := Subgroup.closure ((K : Set (UA σ G.W.J)) ∪
    {l | l ∈ L ∧ ∀ h ∈ UAt σ G.W (evFin F v), l * h = h * l}) with hL'
  have hL'lev : GlobalTheory.ThKAdm.IsLevel G.W L' := GlobalTheory.T.level_subgroup_open_neighbourhood F E σ (a + a') G.W v L K hL hKv hKO
  set A : Set (Fn F a' (a + a')) :=
    {Ψ | Ψ ∈ D ∧ (∀ l ∈ L', om' (1, l) Ψ = Ψ) ∧ GlobalTheory.ThKAdm.HasTypes B om' τ Ψ} with hA
  have hfin := GlobalTheory.T.matched_theta_descent_smooth hKP F E σ B a a' G X om om' R Rf hM L' hL'lev m τ hτ
  have lin := GlobalTheory.T.matched_pair_theta_local_global hKP F E σ B a a' G X om om' R Rf hM

  have hfg : (Submodule.span ℂ (G.M'.I om' '' A)).FG := Module.Finite.iff_fg.1 hfin
  obtain ⟨s', hs'A, hs'span⟩ := (Submodule.fg_span_iff_fg_span_finset_subset _).1 hfg
  obtain ⟨t, htA, hts'⟩ := Finset.subset_set_image_iff.1 hs'A
  have htD : ∀ x ∈ (t : Set (Fn F a' (a + a'))), x ∈ D := fun x hx => (htA hx).1
  refine ⟨t, htD, ?_⟩
  intro Ψ hΨ hΨK

  have hΨD : Ψ ∈ D := by
    refine Submodule.span_le.2 ?_ hΨ
    rintro _ ⟨g, rfl⟩
    exact (GlobalTheory.T.matched_pair_theta_exists_data hKP F E σ B a a' G X om om' R Rf hM).1 v g.1 g.2 Φ hΦ

  have hΨL' : ∀ l ∈ L', om' (1, l) Ψ = Ψ := by
    let St : Subgroup (UA σ G.W.J) :=
      { carrier := {l | om' (1, l) Ψ = Ψ}
        one_mem' := by
          show om' (1, 1) Ψ = Ψ
          rw [show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
          rfl
        mul_mem' := by
          intro x y hx hy
          show om' (1, x * y) Ψ = Ψ
          rw [hmul, hy, hx]
        inv_mem' := by
          intro x hx
          show om' (1, x⁻¹) Ψ = Ψ
          conv_lhs => rw [← (show om' (1, x) Ψ = Ψ from hx)]
          rw [← hmul, inv_mul_cancel, show ((1 : UA σ G.V'.J), (1 : UA σ G.W.J)) = 1 from rfl, map_one]
          rfl }
    have hle : L' ≤ St := by
      rw [hL', Subgroup.closure_le]
      rintro l (hl | ⟨hlL, hlc⟩)
      · exact hΨK l hl
      · show om' (1, l) Ψ = Ψ
        have hgen : ∀ y ∈ Submodule.span ℂ (Set.range fun g : UAtSub σ G.W (evFin F v) => om' (1, g.1) Φ),
            om' (1, l) y = y := by
          intro y hy
          induction hy using Submodule.span_induction with
          | mem y hy =>
            obtain ⟨g, rfl⟩ := hy
            rw [← hmul, hlc g.1 g.2, hmul, hΦL l hlL]
          | zero => exact map_zero _
          | add x y _ _ hx hy => rw [map_add, hx, hy]
          | smul c x _ hx => rw [map_smul, hx]
        exact hgen Ψ hΨ
    exact fun l hl => hle hl

  have hΨτ : GlobalTheory.ThKAdm.HasTypes B om' τ Ψ := by
    have key : ∀ y ∈ Submodule.span ℂ (Set.range fun g : UAtSub σ G.W (evFin F v) => om' (1, g.1) Φ),
        ∃ T' : EuclideanSpace ℂ (Fin m) →ₗ[ℂ] Fn F a' (a + a'),
          (∀ k ∈ KInf σ G.W B.emb, ∀ x, T' (τ k x) = om' (1, k) (T' x)) ∧ T' x₀ = y := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨g, rfl⟩ := hy
        refine ⟨(om' (1, g.1)).comp T, fun k hk x => ?_, ?_⟩
        · simp only [LinearMap.comp_apply]
          rw [hTint k hk x, ← hmul, ← hmul, hcomm g.1 (hfinPt g.1 g.2) k hk]
        · simp only [LinearMap.comp_apply, hx₀]
      | zero => exact ⟨0, fun k _ x => by simp, by simp⟩
      | add x y _ _ hx hy =>
        obtain ⟨T1, h1, e1⟩ := hx
        obtain ⟨T2, h2, e2⟩ := hy
        exact ⟨T1 + T2, fun k hk z => by simp [h1 k hk z, h2 k hk z], by simp [e1, e2]⟩
      | smul c x _ hx =>
        obtain ⟨T1, h1, e1⟩ := hx
        exact ⟨c • T1, fun k hk z => by simp [h1 k hk z], by simp [e1]⟩
    obtain ⟨T', hT', e⟩ := key Ψ hΨ
    exact ⟨T', hT', x₀, e⟩
  have hΨA : Ψ ∈ A := ⟨hΨD, hΨL', hΨτ⟩
  have h1 : G.M'.I om' Ψ ∈ Submodule.span ℂ (G.M'.I om' '' (Submodule.span ℂ (t : Set (Fn F a' (a + a'))) : Set _)) := by
    have h0 : G.M'.I om' Ψ ∈ Submodule.span ℂ (G.M'.I om' '' A) := Submodule.subset_span ⟨Ψ, hΨA, rfl⟩
    rw [hs'span, ← hts', Finset.coe_image] at h0
    exact Submodule.span_mono (Set.image_mono Submodule.subset_span) h0
  have hle : Submodule.span ℂ (t : Set (Fn F a' (a + a'))) ≤ D := Submodule.span_le.2 htD
  obtain ⟨w, hw, hIw⟩ := GlobalTheory.ThetaFacCompl.exists_of_mem_span_image D _ (G.M'.I om') lin hle h1
  refine ⟨w, hw, ?_⟩
  have e : Ψ - w = Ψ + (-1 : ℂ) • w := by rw [neg_one_smul, sub_eq_add_neg]
  rw [e, lin Ψ hΨD w (hle hw) (-1), hIw, neg_one_smul, add_neg_cancel]

end GlobalTheory.ThKAdmPrime
