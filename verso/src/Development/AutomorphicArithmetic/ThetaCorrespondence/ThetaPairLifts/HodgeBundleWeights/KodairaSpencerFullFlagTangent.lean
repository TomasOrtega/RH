import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.TamagawaNumberSpecialUnitary
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZero
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.Hypotheses2
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.HodgeBundleWeights.KodairaSpencerPairingSymmetric
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsGroupLiftKodairaSpencerZeroStatement

section
set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
noncomputable section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj GlobalTheory.DeRham GlobalTheory.Cris
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.KSFull
end GlobalTheory.KSFull
namespace GlobalTheory.KSFull
/- English proof (translation)
Introduce `PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS`. Take `⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩` from `hKS`. Use `⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩` and prove the remaining obligations. Establish `P` using `PP.p5`. Establish `hU` using `GlobalTheory.ObjDim.isAbelianScheme Xo.univ`.

Establish `hg` using `GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ`. Establish `hA` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ`. Establish `gA` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg`. Establish `hA'` using `GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'`. Establish `gA'` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg`.

Use `haveI : IsCommMonObj A := hA.comm`. Take `⟨a', ha'⟩` from `GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'`. Take `⟨a, ha⟩` from `GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ`. Establish `hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left` using `fun z => by`. Apply `hπ'.1.hom_ext` to reduce the goal to its premises.

Rewrite using `[Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]`. Rewrite using `[Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]`. Take `⟨ψ₀, hpol₀, hiso, hperf, hlag⟩` from `GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ`. Take `rfl : ψ = ψ₀` from `IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀`. Establish `hadj` using `GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol`.

Establish `hK` using `GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'`. Take `⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩` from `GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha`. Choose the witnesses or unpack the hypotheses as in `rfl : ub = ub₀ := by`. Use function extensionality and compare the values at `σ k`. Apply `ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ` to reduce the goal to its premises.

Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(ub σ k).left ≫ π = (ub₀ σ k).left ≫ π`. Rewrite using `[hu, hu₀]`. Establish `hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2)` using `fun k => hl k.1 k.2`. Take `⟨hspan, hind⟩` from `GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hl'`.

Set `χ : (E →+* ℂ) → 𝓞 E →+* K` to `fun σ => (algebraMap c.F K).comp (embK c σ)`. Establish `heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A` using `fun k z => by`. Use `a.hom z` as an intermediate fact. Rewrite using `[act_apply]`. Establish `h1` using `(hl' k).push (a.act z)`.

Rewrite `h1` using `[he₀]`. Conclude with `h1.sub_mem ((hl' k).smul _)`. Establish `hsym` using `_root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol`. Use `isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_` and prove the remaining obligations. Establish `key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))), GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1` using `fun τ j => by`.

Take `⟨w, hw, hr⟩` from `hM τ j`. Rewrite `hr` using `[eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw]`. Then use the resulting hypothesis. Introduce and unpack `⟨σ, j⟩ hσ`. Establish `hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H`. Rewrite using `[(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]`.

Conclude with `hσ`. It suffices to establish `∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')), GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j`. Introduce `σ' e'`. Substitute `e'` using the available equality. Conclude with `key ⟨conjEmb σ, hτ⟩`.

Introduce and unpack `⟨σ, j⟩ -`. Conclude with `GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift h a a' hc z hw) χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ (fun z => by`. Simplify using `only [χ, RingHom.comp_apply]`. Rewrite using `[← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j`.
-/
theorem kodaira_spencer_full : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  intro PP E _ _ _ H Dw l Xo c K _ _ y x' _ _ hKS
  obtain ⟨A, _, A', _, π, π', i, h, ψ, ub, hb, hπ, hπ', e, hpol, hu, hl, hM⟩ := hKS
  refine ⟨A, inferInstance, A', inferInstance, π, π', i, h, hπ, hπ', e, ?_⟩
  have P := PP.p5
  have hU := GlobalTheory.ObjDim.isAbelianScheme Xo.univ
  have hg := GlobalTheory.ObjDim.smoothOfRelativeDimension Xo.univ
  have hA := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ
  have gA := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ.1 hg
  have hA' := GlobalTheory.PolPull.isAbelianScheme_of_isGrpPullback hU hπ'
  have gA' := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback hπ'.1 hg
  haveI : IsCommMonObj A := hA.comm
  obtain ⟨a', ha'⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ'
  obtain ⟨a, ha⟩ := GlobalTheory.T.exists_ringAction_of_isGrpPullback Xo.univ.t.act hπ
  have hc : ∀ z, (a.act z).left ≫ i = i ≫ (a'.act z).left := fun z => by
    apply hπ'.1.hom_ext
    · rw [Category.assoc, Category.assoc, ha' z, ← Category.assoc i π', e, ha z]
    · rw [Category.assoc, Category.assoc, Over.w, h.1.w, ← Category.assoc, Over.w]
  obtain ⟨ψ₀, hpol₀, hiso, hperf, hlag⟩ := GlobalTheory.T.exists_polarizationCrystalForm_perfect_selfAnnihilating P Xo hπ
  obtain rfl : ψ = ψ₀ := IsPolForm.unique P.1 hA gA (pull_isLB Xo.univ.t.PP.isLB π) hpol hpol₀
  have hadj := GlobalTheory.T.polarizationCrystalForm_adjoint_conj_action P Xo hπ a ha hpol
  have hK := GlobalTheory.DeRham.ksRegular_of_isAbelianScheme P h hA' gA'
  obtain ⟨ub₀, hu₀, ht₀, he₀, hbasis₀⟩ := GlobalTheory.T.exists_frame_tangentVectors_of_isGrpPullback y hπ a ha
  obtain rfl : ub = ub₀ := by
    funext σ k
    apply ReciprocityTheory.ChartRestriction.G.PullbackSections.push_inj hπ
    apply Over.OverMorphism.ext
    change (ub σ k).left ≫ π = (ub₀ σ k).left ≫ π
    rw [hu, hu₀]
  have hl' : ∀ k : (Σ σ : E →+* ℂ, Fin (Dw.mult σ)), IsLieImage (hb k) (ub k.1 k.2) := fun k => hl k.1 k.2
  obtain ⟨hspan, hind⟩ := GlobalTheory.T.frameLifts_basis_deRhamHomology_mod_hodgeFiltration P y hπ ub hu hb hl'
  let χ : (E →+* ℂ) → 𝓞 E →+* K := fun σ => (algebraMap c.F K).comp (embK c σ)
  have heig : ∀ k (z : 𝓞 E), act (dp0 K) (𝟙 _) a z (hb k) - χ k.1 z • hb k ∈ Fil A := fun k z => by
    have := a.hom z
    rw [act_apply]
    have h1 := (hl' k).push (a.act z)
    rw [he₀] at h1
    exact h1.sub_mem ((hl' k).smul _)
  have hsym := _root_.GlobalTheory.T.kodairaSpencer_pairing_symmetric PP E H Dw l Xo K y.x x' A A' π π' i h ψ hπ hπ' e hpol
  refine isKSValue_one_of_rows h ψ hiso hlag hperf hpol.isAlt hsym ub hb hl' hspan
    (fun σ => σ ∈ GlobalTheory.FlagTan.psiSet H) conjEmb
    (fun σ hσ => ((GlobalTheory.FlagTan.isHalf_psiSet H) σ).1 hσ) ?_ ?_
  ·
    have key : ∀ (τ : GlobalTheory.FlagTan.psiSet H) (j : Fin (Dw.mult (conjEmb τ.1))),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨conjEmb τ.1, j⟩ 1 := fun τ j => by
      obtain ⟨w, hw, hr⟩ := hM τ j
      rwa [eq_one_of_isLieComb_zero (fun b => ht₀ τ.1 b) hw] at hr
    rintro ⟨σ, j⟩ hσ
    have hτ : conjEmb σ ∈ GlobalTheory.FlagTan.psiSet H := by
      rw [(GlobalTheory.FlagTan.isHalf_psiSet H) (conjEmb σ), GlobalTheory.AllWt.conjEmb_conjEmb]
      exact hσ
    suffices ∀ σ' (_ : conjEmb (conjEmb σ) = σ') (j' : Fin (Dw.mult σ')),
        GlobalTheory.FlagTan.IsKSRow h ψ hb ⟨σ', j'⟩ 1 from this σ (GlobalTheory.AllWt.conjEmb_conjEmb σ) j
    intro σ' e'
    subst e'
    exact key ⟨conjEmb σ, hτ⟩
  ·
    rintro ⟨σ, j⟩ -
    exact GlobalTheory.KSExist.ksRow_exists_lieComb h a (fun z => H.bar z) ψ hiso hlag hperf hadj hK
      (fun z f w hw => GlobalTheory.T.isKodairaSpencerValue_endomorphism_lift h a a' hc z hw)
      χ ub hb hspan hind heig hbasis₀ (conjEmb σ) σ
      (fun z => by
        simp only [χ, RingHom.comp_apply]
        rw [← conj_embK' c (conjEmb σ) z, GlobalTheory.AllWt.conjEmb_conjEmb]) j
end GlobalTheory.KSFull
end
end

section
open NumberField ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open AlgebraicGeometry CategoryTheory MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Apply the tactic sequence `first | exact @_root_.GlobalTheory.KSFull.kodaira_spencer_full | exact _root_.GlobalTheory.KSFull.kodaira_spencer_full | (intros; apply _root_.GlobalTheory.KSFull.kodaira_spencer_full <;> assumption)`.
-/
theorem _root_.GlobalTheory.T.kodaira_spencer_full_flag_tangent : _root_.GlobalTheory.CovTop.Hypotheses'' → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) (K : Type) [Field K] [Algebra c.F K] (y : FrPt Xo c K) (x' : Sp (DualNumber K) ⟶ Xo.X), 1 ≤ Dw.p + Dw.q → GlobalTheory.FlagTan.IsTanX y x' → GlobalTheory.FlagTan.IsKS (GlobalTheory.FlagTan.psiSet H) y x' 0 → ∃ (A : Over (Sp K)) (_ : GrpObj A) (A' : Over (Sp (DualNumber K))) (_ : GrpObj A') (π : A.left ⟶ Xo.univ.t.G.left) (π' : A'.left ⟶ Xo.univ.t.G.left) (i : A.left ⟶ A'.left) (h : IsGrpPullback A A' (GlobalTheory.DeRham.epsRed K) i), IsGrpPullback A Xo.univ.t.G y.x π ∧ IsGrpPullback A' Xo.univ.t.G x' π' ∧ i ≫ π' = π ∧ ∀ f ∈ GlobalTheory.DeRham.Fil A, GlobalTheory.DeRham.IsKSValue h f 1 := by
  first | exact @_root_.GlobalTheory.KSFull.kodaira_spencer_full | exact _root_.GlobalTheory.KSFull.kodaira_spencer_full | (intros; apply _root_.GlobalTheory.KSFull.kodaira_spencer_full <;> assumption)
end
