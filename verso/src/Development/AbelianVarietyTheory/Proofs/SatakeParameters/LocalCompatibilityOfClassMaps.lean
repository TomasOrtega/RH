import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.CenLocOfCenReal
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
import Formalism.LocalToGlobal.NormalizedHeckeFactors.TypesDefs
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTypeGroupBlockLift
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RankOneLocalComponentDet
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.UnrAtOfMulLeft
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.TameBlockTypeAtSplitPlace
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsSplitPlOfNotIsConjPl
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsAdelicUnitaryTrivialOutsideSplitPlaceLocEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SplitPlaceLocalComponentExistsUniqueClassStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LiftThroughCompletionIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceUnitsCharacterEqOfAgreeOnField
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SplitPlaceCompletionIsoPreservesValuation
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DiagUniformiserConjTransposeInvMemUpperParahoric
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockCharacterEqInvAtTransposeInvLowerBlockDet
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.NotAdmissibleWithAmbientTop
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.PadicIntGLSmulMemPrincipalCongruenceFixed
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsTameInflationCharacterOfPadicIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIrreducibleSmoothPullbackPadicRingIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsParahoricTypeVectorOfBlockTypeVectorPadicIsoStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.BlockLiftActionOnPrincipalCongruenceFixedVectorsStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsotypicLocalComponentFixedStatement
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LocalLanglandsSplitQpStatement
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.TypeRec GlobalTheory.GLq GlobalTheory.GLp GlobalTheory.SerSys
attribute [local instance] GlobalTheory.TypeRec.factG

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open Formalism.L2.Host

namespace GlobalTheory.LocCompTy

open GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin GlobalTheory.PendOf

/- English proof (translation)
Establish `: NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h)`. Use `sSup_le fun S' hS' => ?_` and prove the remaining obligations. Introduce `y hy`. Conclude with `le_sSup hS' (hS'.1.1.stable h y hy)`. Conclude with `this hf`.
-/
theorem rt_mem_isoTyp {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ} (a : NG.AlgWt L n)
    (S : Submodule ℂ (GAf L n → a.W)) (h : GAf L n) {f : GAf L n → a.W}
    (hf : f ∈ NG.isoTyp a.ρ S) : NG.rt L n h f ∈ NG.isoTyp a.ρ S := by
  have : NG.isoTyp a.ρ S ≤ (NG.isoTyp a.ρ S).comap (NG.rt L n h) := by
    refine sSup_le fun S' hS' => ?_
    intro y hy
    exact le_sSup hS' (hS'.1.1.stable h y hy)
  exact this hf

set_option maxHeartbeats 1000000 in
/- English proof (translation)
Take `⟨ψ₀, ξ, hψ, hξ, hlev⟩` from `P.H.level.uni i j hj k v s hsw`. Establish `hcv` using `GlobalTheory.SplitConjVal.valuation_eq s c hcont hci`. Take `⟨h1, h2⟩` from `GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh`. Take `⟨i1, -⟩` from `GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹ (by`. Use `(GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Conclude with `map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)`. Establish `huni : NG.UniRT s D.R.r (s.loc D.R.nV x)`. Use `⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩, fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)`.

Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)`. Use `h2 a b hb split_ifs at this with e` as an intermediate fact. Rewrite `ha` using `[e]`. Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[sub_zero]`. Then use the resulting hypothesis.

Use `h2 a b hb split_ifs at this with e` as an intermediate fact. Rewrite `hlt` using `[e]`. Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[sub_zero]`. Then use the resulting hypothesis. Substitute `he` using the available equality.

Use `h2 a a ha` as an intermediate fact. Use `split_ifs at this with e`. Conclude with `this`. Conclude with `absurd rfl e`. Establish `hxJ : x ∈ (P.M.loc i).J` using `(hlev.mem x hx).2 huni`.

Establish `hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ`. Rewrite using `[← (P.M.loc i).real_range]`. Conclude with `LinearMap.mem_range_self _ _`. Establish `hrt` using `hTS.2 ⟨x, hxJ⟩`. Set `h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E)` to `Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)`.

Establish `hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t` using `hh`. Establish `hdet` using `GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'`. Establish `hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0`. Introduce `h0`. Rewrite `hdet` using `[h0, mul_zero, zero_sub, Valuation.map_neg, map_one]`.

Conclude with `lt_irrefl _ hdet`. Establish `hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) = (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det`. Set `e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val}` to `{ toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩ invFun := fun y => ⟨y.1.val - D.R.r, by`. Establish `h1` using `y.1.2`. Establish `h2` using `y.2`.

Express the relevant statement in the definitionally equal form `y.1.val < D.R.r + D.R.t at h1`. Use the proof step `omega⟩`. Use `left_inv := fun a => by ext; simp`. Use `right_inv := fun y => by ext; simp; have := y.2; omega }`. Rewrite using `[NG.detDD, ← Matrix.det_submatrix_equiv_self e]`.

Rewrite using `[show c _ = c.toRingHom _ from rfl, RingHom.map_det]`. Use `congr 1`. Establish `hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0` using `fun h0 => hne2 (by rw [← hc_det, h0, map_zero])`. Set `u` to `Units.mk0 _ hF0`. Establish `hchr` using `hlev.chr x hxJ hx u rfl`.

Establish `hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1` using `hψ.1 _ (by`. Unfold `NG.supDiag`. Use `Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Use `h2 p q h.2 split_ifs at this with e` as an intermediate fact.

Rewrite `h` using `[e]`. Use linear arithmetic over natural numbers and integers. Rewrite `this` using `[sub_zero]`. Then use the resulting hypothesis. Rewrite using `[map_zero]`. Conclude with `zero_lt_one)`.

Establish `hμ : GlobalTheory.NPin.IsComp (P.tp.tup (D.nd.mu i) j) s.w ((P.tp.tup (D.nd.mu i) j).loc s.w)` using `⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩`. Establish `hξμ` using `GlobalTheory.ConjDense.eq_of_agree s c hcont hci ((P.tp.tup (D.nd.mu i) j).loc s.w) ξ hμ.1 hξ.1 (fun k => by rw [hξ.2 k, hμ.2 k]) u`. Establish `hbc : GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h = ((((P.tp.tup (D.nd.mu i) j).loc s.w) (Units.map c.toMonoidHom u) : ℂˣ) : ℂ)` using `GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)`. Express the relevant statement in the definitionally equal form `_ = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h • _`. Rewrite using `[hbc, ← hξμ, hrt, hchr, hsup, one_mul]`.
-/
theorem blockEig (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D) (i : D.nd.Loc) (PI : D.naut.AV i)
    (k : Fin 2) (v : D.nd.PlG k) (j : Fin D.R.m) (hj : j.1 + 1 = D.nd.j i) (s : SplitPlace D.host.E)
    (hsw : s.w = D.naut.plGw k v) (c : s.v.adicCompletion (maximalRealSubfield D.host.E) ≃+* s.w.adicCompletion D.host.E)
    (hcont : Continuous c) (hci : ∀ x : D.host.E, c (s.i x) = algebraMap D.host.E (s.w.adicCompletion D.host.E) x)
    (F : D.what₂.Mt (D.nd.mu i) (D.nd.j i)) (x : GAf D.host.E D.R.nV) (hx : TrivOutside {s.v} x)
    (hh : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
      GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t) :
    NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w)
      (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) • (P.M.loc i).real F := by
  obtain ⟨ψ₀, ξ, hψ, hξ, hlev⟩ := P.H.level.uni i j hj k v s hsw
  have hcv := GlobalTheory.SplitConjVal.valuation_eq s c hcont hci
  obtain ⟨h1, h2⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x) hh
  obtain ⟨i1, -⟩ := GlobalTheory.BlockConj.facts_of_mem s D.R.r D.R.t c hcv (s.loc D.R.nV x)⁻¹
    (by
      have := (GlobalTheory.BlockType.blockGrp _ _ _).inv_mem hh
      convert this using 1
      exact map_inv (Matrix.GeneralLinearGroup.map (n := Fin (D.R.r + D.R.t)) c.toRingHom) _)
  have huni : NG.UniRT s D.R.r (s.loc D.R.nV x) := by
    refine ⟨⟨GlobalTheory.BlockConj.mem_GLint_of (fun a b => ?_) (fun a b => ?_), fun a b ha hb => ?_⟩,
      fun a b ha hb => ⟨fun hlt => ?_, fun he => ?_⟩⟩
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (h1 a b)
    · exact (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).2 (i1 a b)
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at ha; omega
      · rwa [sub_zero] at this
    · have := h2 a b hb
      split_ifs at this with e
      · rw [e] at hlt; omega
      · rwa [sub_zero] at this
    · subst he
      have := h2 a a ha
      split_ifs at this with e
      · exact this
      · exact absurd rfl e
  have hxJ : x ∈ (P.M.loc i).J := (hlev.mem x hx).2 huni
  have hTS : (P.M.loc i).real F ∈ NG.TypeSp (P.M.loc i).wt.ρ (P.M.loc i).J (P.M.loc i).χ := by
    rw [← (P.M.loc i).real_range]; exact LinearMap.mem_range_self _ _
  have hrt := hTS.2 ⟨x, hxJ⟩
  let h : GL (Fin (D.R.r + D.R.t)) (s.w.adicCompletion D.host.E) :=
    Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)
  have hh' : h ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := hh
  have hdet := GlobalTheory.BlockConjDet.val_det_mul_sub_one_lt hh'
  have hne2 : (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det ≠ 0 := by
    intro h0
    rw [h0, mul_zero, zero_sub, Valuation.map_neg, map_one] at hdet
    exact lt_irrefl _ hdet
  have hc_det : c (NG.detDD s D.R.r (s.loc D.R.nV x)) =
      (h.val.submatrix (Fin.natAdd D.R.r) (Fin.natAdd D.R.r)).det := by
    let e : Fin D.R.t ≃ {y : Fin D.R.nV // D.R.r ≤ y.val} :=
      { toFun := fun a => ⟨Fin.natAdd D.R.r a, by simp⟩
        invFun := fun y => ⟨y.1.val - D.R.r, by
          have h1 := y.1.2; have h2 := y.2; change y.1.val < D.R.r + D.R.t at h1; omega⟩
        left_inv := fun a => by ext; simp
        right_inv := fun y => by ext; simp; have := y.2; omega }
    rw [NG.detDD, ← Matrix.det_submatrix_equiv_self e]
    rw [show c _ = c.toRingHom _ from rfl, RingHom.map_det]
    congr 1
  have hF0 : NG.detDD s D.R.r (s.loc D.R.nV x) ≠ 0 := fun h0 => hne2 (by rw [← hc_det, h0, map_zero])
  let u := Units.mk0 _ hF0
  have hchr := hlev.chr x hxJ hx u rfl
  have hsup : ψ₀ (NG.supDiag s D.R.r (s.loc D.R.nV x)) = 1 := hψ.1 _ (by
    unfold NG.supDiag
    refine Valuation.map_sum_lt _ one_ne_zero fun p _ => Valuation.map_sum_lt _ one_ne_zero fun q _ => ?_
    split_ifs with h
    · have := h2 p q h.2
      split_ifs at this with e
      · rw [e] at h; omega
      · rwa [sub_zero] at this
    · rw [map_zero]; exact zero_lt_one)
  have hμ : GlobalTheory.NPin.IsComp (P.tp.tup (D.nd.mu i) j) s.w ((P.tp.tup (D.nd.mu i) j).loc s.w) :=
    ⟨GlobalTheory.HeckeComp.smooth_loc _ _, fun _ => rfl⟩
  have hξμ := GlobalTheory.ConjDense.eq_of_agree s c hcont hci ((P.tp.tup (D.nd.mu i) j).loc s.w) ξ hμ.1 hξ.1
    (fun k => by rw [hξ.2 k, hμ.2 k]) u
  have hbc : GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h =
      ((((P.tp.tup (D.nd.mu i) j).loc s.w) (Units.map c.toMonoidHom u) : ℂˣ) : ℂ) :=
    GlobalTheory.BlockType.blockChar_eq _ _ _ (by rw [← hc_det]; rfl)
  change _ = GlobalTheory.BlockType.blockChar ((P.tp.tup (D.nd.mu i) j).loc s.w) h • _
  rw [hbc, ← hξμ, hrt, hchr, hsup, one_mul]

set_option maxHeartbeats 2000000 in
/- English proof (translation)
Establish `hjr` using `D.nd.j_range i`. Set `j0 : Fin D.R.m` to `⟨D.nd.j i - 1, by omega⟩`. Establish `hj0 : j0.1 + 1 = D.nd.j i` using `by simp only [j0]; omega`. Establish `hsp : IsSplitPl D.host w` using `hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v`. Take `⟨s, hs⟩` from `GlobalTheory.TypeBlockPf.splitAt D _ hsp`.

Substitute `hs` using the available equality. Establish `htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w)` using `GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))`. Take `⟨χ, hχ⟩` from `GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame`. Use `⟨_, χ, hχ, GlobalTheory.T.local_langlands_split_qp hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ, -⟩` from `GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s`.

Establish `hσ' : IsLocS (n` using `D.R.nV) (P.H.av.S i Q) s σ := hσ`. Use `⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩` and prove the remaining obligations. Apply `(P.T.e s.w).injective` to reduce the goal to its premises. Rewrite using `[hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]`. Conclude with `P.au _ _ _ _ s _ hσ'`.

Take `⟨c, T, hc, hci, -, -, -⟩` from `hσ`. Use `set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ`. Establish `hT : ∀ F, F ∈ D.naut.typeV i Q ↔ (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q)` using `fun F => by`. Rewrite using `[P.H.av.typeV]`. Conclude with `Submodule.mem_comap`.

Set `J` to `{φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x → ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q), φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}`. Set `ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V)` to `LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)`. Establish `hpar : ∀ (φ : J) (F : D.naut.typeV i Q), IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F))`. Introduce `φ F`. Use `GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_` and prove the remaining obligations.

Use `GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_` and prove the remaining obligations. Take `⟨x, hx, hxe⟩` from `GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)`. Establish `hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h`. Rewrite using `[hxe]`. Conclude with `Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)`.

Establish `hF` using `(hT F).1 F.2`. Establish `hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈ GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t` using `by rw [hmap]; exact hh`. Establish `h3` using `φ.2 x hx _ hF`. Rewrite `h3` using `[blockEig hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul]`. Rewrite using `[← hmap]`.

Conclude with `h3.symm`. Establish `hinj : Function.Injective ι`. Rewrite using `[← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]`. Introduce `F hF`. Assume the negation of the conclusion as `hne`.

Establish `h1 : (P.M.loc i).real F ≠ 0` using `fun h0 => hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))`. Take `⟨φ, hφ, hφe⟩` from `GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _ ((hT F).1 F.2) h1`. Conclude with `hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)`. Use `⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩` and prove the remaining obligations. Establish `hzc : ∀ b, a * b = b * a` using `fun b => (Subalgebra.mem_center_iff.1 ha b).symm`.

Establish `hcz` using `GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc`. Take `⟨L, hLift, hCL⟩` from `hCen i`. Establish `e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) = actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F)`. Rewrite using `[NTypes.onMt, dif_pos hcz]`. Conclude with `hCL ⟨_, hcz⟩ F`.

Set `g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd` to `fun h => Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h`. Establish `hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) = ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F)`. Unfold `actSum Formalism.MainNotions.ArithmeticCylinders.atPlace`. Rewrite using `[MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F)) (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]`. Conclude with `Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)`.

Establish `hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧ IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧ NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F)` using `fun h => GlobalTheory.T.lift_through_completion_iso hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g]) (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])`. Use `choose xs hxs using hg`. Establish `hF` using `(hT F).1 F.2`. Establish `e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) = ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F)`. Rewrite using `[e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]`.

Establish `hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q`. Rewrite using `[hT, e1]`. Conclude with `Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)`. Use `⟨hmem, fun φ => ?_⟩` and prove the remaining obligations. Establish `hu` using `(hpar φ F).1`.

Express the relevant statement in the definitionally equal form `φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) = actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))`. Rewrite using `[e1, map_sum, actTop, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]`. Use `congr 1`.

Conclude with `GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1`.
-/
theorem compAt (hPr : GlobalTheory.NRows.Hypotheses₂) (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D)
    (hCen : GlobalTheory.HeightCounting.Up.CenLoc D P.M) (i : D.nd.Loc) (k : Fin 2) (v : D.nd.PlG k) (w : PlE D.host)
    (hw : w = D.naut.plGw k v) (e : ℚ_[D.host.g k] ≃+* w.adicCompletion D.host.E) (he : Continuous e)
    (rcw : ∀ n, QRep (D.host.g k) n → D.naut.LP w)
    (hrc : ∀ n (σ : GlobalTheory.SmGL.IrrRep (GL (Fin n) (w.adicCompletion D.host.E))) (π : QRep (D.host.g k) n),
      Nonempty (π ≅ Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom))) →
      P.T.e w (rcw n π) = GlobalTheory.CuspRep.ParLaws.locRec hL (D.nd.plOm.2 w) (GlobalTheory.LocLanglands.cls σ)) :
    ∃ (μ : ℚ_[D.host.g k]ˣ →* ℂˣ) (χ : (ZMod (D.host.g k))ˣ →* ℂˣ), TamePart μ χ ∧
      D.naut.locG (D.naut.muC i) w = rcw 1 (Rep.of (Model.detRep 1 μ)) ∧
      ∀ Q : D.naut.AV i, ∃ π : QRep (D.host.g k) D.R.nV, IrrSm π ∧ D.naut.locV i Q w = rcw D.R.nV π ∧
        ActsThrough π D.R.r D.R.t χ (D.naut.typeV i Q)
          fun a => D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) := by
  classical
  have hjr := D.nd.j_range i
  let j0 : Fin D.R.m := ⟨D.nd.j i - 1, by omega⟩
  have hj0 : j0.1 + 1 = D.nd.j i := by simp only [j0]; omega
  have hsp : IsSplitPl D.host w := hw ▸ GlobalTheory.FixedPlaceSplit.isSplitPl_plGw D k v
  obtain ⟨s, hs⟩ := GlobalTheory.TypeBlockPf.splitAt D _ hsp
  subst hs
  have htame : GlobalTheory.SplitWeil.IsTame ((P.tp.tup (D.nd.mu i) j0).loc s.w) :=
    GlobalTheory.MuTameQS.isTame_loc (GlobalTheory.MuTameQS.tameAt_mul ((P.cf.isMu0 j0).tame _) (P.tp.xi_tame _ _))
  obtain ⟨χ, hχ⟩ := GlobalTheory.T.exists_tameInflationCharacter_of_padic_iso _ _ e he _ htame
  refine ⟨_, χ, hχ, GlobalTheory.T.local_langlands_split_qp hPr hL D P i j0 hj0 k s.w e rcw hrc, fun Q => ?_⟩
  obtain ⟨σ, hσ, -⟩ := GlobalTheory.T.splitPlaceLocalComponent_exists_unique_class D.host.E D.R.nV (P.H.av.rep i Q) s
  have hσ' : IsLocS (n := D.R.nV) (P.H.av.S i Q) s σ := hσ
  refine ⟨Rep.of (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)), GlobalTheory.T.isIrreducibleSmooth_pullback_padic_ringIso _ _ e he _ σ, ?_, ?_⟩
  · apply (P.T.e s.w).injective
    rw [hrc _ σ _ ⟨CategoryTheory.Iso.refl _⟩, D.nbc.embAV_loc, P.H.emb]
    exact P.au _ _ _ _ s _ hσ'
  obtain ⟨c, T, hc, hci, -, -, -⟩ := hσ
  set ξ := (P.tp.tup (D.nd.mu i) j0).loc s.w with hξ
  have hT : ∀ F, F ∈ D.naut.typeV i Q ↔
      (P.M.loc i).real F ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q) := fun F => by
    rw [P.H.av.typeV]; exact Submodule.mem_comap
  let J := {φ : (GAf D.host.E D.R.nV → (P.M.loc i).wt.W) →ₗ[ℂ] σ.V // ∀ x, TrivOutside {s.v} x →
    ∀ f' ∈ NG.isoTyp (P.M.loc i).wt.ρ (P.H.av.S i Q),
      φ (NG.rt D.host.E D.R.nV x f') = σ.ρ (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) (φ f')}
  let ι : D.naut.typeV i Q →ₗ[ℂ] (J → σ.V) :=
    LinearMap.pi fun φ => φ.1.comp ((P.M.loc i).real.comp (D.naut.typeV i Q).subtype)
  have hpar : ∀ (φ : J) (F : D.naut.typeV i Q),
      IsParVec (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t χ (φ.1 ((P.M.loc i).real F)) := by
    intro φ F
    refine GlobalTheory.T.isParahoricTypeVector_of_blockTypeVector_padic_iso _ _ e he ξ χ hχ D.R.r D.R.t σ.V σ.ρ _ ?_
    refine GlobalTheory.BlockType.isBlockVec_of (r := D.R.r) (t := D.R.t) ξ σ.ρ _ fun h hh => ?_
    obtain ⟨x, hx, hxe⟩ := GlobalTheory.SplitLift.exists_trivOutside_loc_eq D.R.nV s
      (Matrix.GeneralLinearGroup.map c.symm.toRingHom h)
    have hmap : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) = h := by
      rw [hxe]; exact Units.ext (Matrix.ext fun a b => c.apply_symm_apply _)
    have hF := (hT F).1 F.2
    have hh2 : Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x) ∈
        GlobalTheory.BlockType.blockGrp (s.w.adicCompletion D.host.E) D.R.r D.R.t := by rw [hmap]; exact hh
    have h3 := φ.2 x hx _ hF
    rw [blockEig hL D P i Q k v j0 hj0 s hw c hc hci F x hx hh2, map_smul] at h3
    rw [← hmap]; exact h3.symm
  have hinj : Function.Injective ι := by
    rw [← LinearMap.ker_eq_bot, Submodule.eq_bot_iff]
    intro F hF
    by_contra hne
    have h1 : (P.M.loc i).real F ≠ 0 := fun h0 =>
      hne (Subtype.ext ((P.M.loc i).real_inj (h0.trans (map_zero _).symm)))
    obtain ⟨φ, hφ, hφe⟩ := GlobalTheory.T.isotypic_local_component_fixed D.host.E D.R.nV (P.M.loc i).wt (P.H.av.S i Q) (P.H.av.irr i Q) s σ hσ' c hc hci _
      ((hT F).1 F.2) h1
    exact hφ (congrFun (LinearMap.mem_ker.1 hF) ⟨φ, hφe⟩)
  refine ⟨J, ι, hinj, fun F φ => hpar φ F, fun a ha F => ?_⟩
  have hzc : ∀ b, a * b = b * a := fun b => (Subalgebra.mem_center_iff.1 ha b).symm
  have hcz := GlobalTheory.SeriesSupportTest.atPlace_central D k v a hzc
  obtain ⟨L, hLift, hCL⟩ := hCen i
  have e0 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) := by
    rw [NTypes.onMt, dif_pos hcz]; exact hCL ⟨_, hcz⟩ F
  let g : GL (Fin D.R.r) (ZMod (D.host.g k)) → G0g D.nd := fun h =>
    Pi.mulSingle (M := fun kv : (Σ k : Fin 2, D.nd.PlG k) => GL (Fin D.R.r) (ZMod (D.host.g kv.1))) ⟨k, v⟩ h
  have hsum : actSum D L (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) ((P.M.loc i).real F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) := by
    unfold actSum Formalism.MainNotions.ArithmeticCylinders.atPlace
    rw [MonoidAlgebra.coeff_ofCoeff, Finsupp.sum_mapDomain_index
      (h := fun g c => c • NG.rt D.host.E D.R.nV (L g) ((P.M.loc i).real F))
      (fun _ => zero_smul _ _) (fun _ _ _ => add_smul _ _ _)]
    exact Finsupp.sum_fintype _ _ (fun _ => zero_smul _ _)
  have hg : ∀ h, ∃ x : GAf D.host.E D.R.nV, TrivOutside {s.v} x ∧
      IsLiftN h (Matrix.GeneralLinearGroup.map c.toRingHom (s.loc D.R.nV x)) ∧
      NG.rt D.host.E D.R.nV (L (g h)) ((P.M.loc i).real F) = NG.rt D.host.E D.R.nV x ((P.M.loc i).real F) := fun h =>
    GlobalTheory.T.lift_through_completion_iso hL D P i Q k v s hw c hc hci L hLift F F.2 h (g h) (by simp [g])
      (fun kv hkv => by simp [g, Pi.mulSingle_eq_of_ne hkv])
  choose xs hxs using hg
  have hF := (hT F).1 F.2
  have e1 : (P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F) =
      ∑ h, a.coeff h • NG.rt D.host.E D.R.nV (xs h) ((P.M.loc i).real F) := by
    rw [e0, hsum]; exact Finset.sum_congr rfl fun h _ => by rw [(hxs h).2.2]
  have hmem : D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F ∈ D.naut.typeV i Q := by
    rw [hT, e1]
    exact Submodule.sum_mem _ fun h _ => Submodule.smul_mem _ _ (rt_mem_isoTyp _ _ _ hF)
  refine ⟨hmem, fun φ => ?_⟩
  have hu := (hpar φ F).1
  change φ.1 ((P.M.loc i).real (D.ntypes.onMt (D.nd.mu i) (D.nd.j i) (Formalism.MainNotions.ArithmeticCylinders.atPlace D k v a) F)) =
    actTop (σ.ρ.comp (Matrix.GeneralLinearGroup.map e.toRingHom)) D.R.r D.R.t a (φ.1 ((P.M.loc i).real F))
  rw [e1, map_sum, actTop, LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun h _ => ?_
  rw [map_smul, φ.2 _ (hxs h).1 _ hF, LinearMap.smul_apply, MonoidHom.comp_apply]
  congr 1
  exact GlobalTheory.T.blockLift_action_on_principalCongruenceFixedVectors _ _ e he D.R.r D.R.t σ.V σ.ρ _ hu h _ (hxs h).2.1

/- English proof (translation)
Introduce `hPr hL D P I rc hRc hCM hCen`. Conclude with `⟨hCM, fun i k v => compAt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v) fun n σ π h => hRc k v n σ π h⟩`.
-/
theorem main : GlobalTheory.NRows.Hypotheses₂ → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : GlobalTheory.NPin.Pin hL D) (I : Ident D) (rc : GlobalTheory.SerSys.Corr D), IsRc hL P.T I rc → (∀ k v, IsClassMap D.naut.lpDim (rc k v)) → GlobalTheory.HeightCounting.Up.CenLoc D P.M → LocComp D rc := by
  intro hPr hL D P I rc hRc hCM hCen
  exact ⟨hCM, fun i k v => compAt hPr hL D P hCen i k v _ rfl (I.i k v) (I.cont k v) (rc k v)
    fun n σ π h => hRc k v n σ π h⟩

end GlobalTheory.LocCompTy
