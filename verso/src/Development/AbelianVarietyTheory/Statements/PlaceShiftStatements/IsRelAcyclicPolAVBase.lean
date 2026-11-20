import Mathlib
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.AmpleVanishingSym
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IffAmpleVanishing
import Development.AbelianVarietyTheory.Proofs.ThetaLawProofs.ExistsLeNatCastNeZero
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.PolBaseChangeOfRelAmpleLocal

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.CxForm (IsRelAcyclic)
open GlobalTheory GlobalTheory.AbLaw GlobalTheory.RelAcyclicAmple
open scoped CategoryTheory.Obj

attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AmpleSymModel

/- English proof (translation)
Assemble the required witnesses or components as `⟨(WeierstrassCurve.ellPolAV W).isAb, WeierstrassCurve.ellPolAV_g W, (WeierstrassCurve.ellPolAV W).isLB, (WeierstrassCurve.ellPolAV W).ample, (WeierstrassCurve.ellPolAV W).sym⟩`.
-/
theorem hyp_ell {K : Type} [Field K] (W : WeierstrassCurve K) [W.IsElliptic] :
    IsAbelianScheme (WeierstrassCurve.ellPolAV W).A ∧ (WeierstrassCurve.ellPolAV W).g = 1 ∧
      (WeierstrassCurve.ellPolAV W).L.IsLB ∧
      Out.RelAmple (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).L ∧
      Out.Sym (WeierstrassCurve.ellPolAV W).A (WeierstrassCurve.ellPolAV W).L :=
  ⟨(WeierstrassCurve.ellPolAV W).isAb, WeierstrassCurve.ellPolAV_g W, (WeierstrassCurve.ellPolAV W).isLB,
    (WeierstrassCurve.ellPolAV W).ample, (WeierstrassCurve.ellPolAV W).sym⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [isUnit_iff_ne_zero] norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩`.
-/
theorem isElliptic_complex : (⟨0, 0, 1, -1, 0⟩ : WeierstrassCurve ℂ).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    norm_num [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨by rw [isUnit_iff_ne_zero] have h : (27 : K) = 1 := by have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2 linear_combination 13 * h2 simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈] rw [h] norm_num⟩`.
-/
theorem isElliptic_char_two (K : Type) [Field K] [CharP K 2] :
    (⟨0, 0, 1, 0, 0⟩ : WeierstrassCurve K).IsElliptic :=
  ⟨by
    rw [isUnit_iff_ne_zero]
    have h : (27 : K) = 1 := by
      have h2 : (2 : K) = 0 := CharP.cast_eq_zero K 2
      linear_combination 13 * h2
    simp only [WeierstrassCurve.Δ, WeierstrassCurve.b₂, WeierstrassCurve.b₄, WeierstrassCurve.b₆, WeierstrassCurve.b₈]
    rw [h]
    norm_num⟩

/- English proof (translation)
Introduce `U _ κ _ _ W hW hWU n`. Distinguish the cases in `hU : U = ⊤`. Substitute `hU` using the available equality. Conclude with `(cechComplex_exactAt_succ_iff_cube _ n).2 (PolVanishing.exactAt_secCube_pw abelianSchemeLaws_all.1 K P l κ W hl hW hWU (n + 2))`. Establish `hb : U = ⊥`.

Use `eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim` and prove the remaining obligations. Establish `: Subsingleton (Sp K)` using `inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Rewrite using `[Subsingleton.elim y x]` and apply the resulting hypothesis. Substitute `hb` using the available equality. Use `HomologicalComplex.ExactAt.of_isZero ?_` and prove the remaining obligations.

Rewrite using `[cechLB_X, ModuleCat.isZero_iff_subsingleton]`. Use `⟨fun a b => funext fun s => ?_⟩` and prove the remaining obligations. Use `SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim` and prove the remaining obligations. Take `⟨i, hi⟩` from `Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)`. Use `(biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)` and prove the remaining obligations.

Simplify using the standard rewrite rules.
-/
theorem isRelAcyclic_pw (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) (l : ℤ) (hl : 1 ≤ l) :
    IsRelAcyclic P.A.hom P.A.hom (AbLaw.pw P.L l) := by
  intro U _ κ _ _ W hW hWU n
  by_cases hU : U = ⊤
  · subst hU
    exact (cechComplex_exactAt_succ_iff_cube _ n).2
      (PolVanishing.exactAt_secCube_pw abelianSchemeLaws_all.1 K P l κ W hl hW hWU (n + 2))
  · have hb : U = ⊥ := by
      refine eq_bot_iff.2 fun x hx => (hU (eq_top_iff.2 fun y _ => ?_)).elim
      have : Subsingleton (Sp K) := inferInstanceAs (Subsingleton (PrimeSpectrum K))
      rwa [Subsingleton.elim y x]
    subst hb
    refine HomologicalComplex.ExactAt.of_isZero ?_
    rw [cechLB_X, ModuleCat.isZero_iff_subsingleton]
    refine ⟨fun a b => funext fun s => ?_⟩
    refine SecOnR.ext_of_cover _ (I := PEmpty) (fun i => i.elim) (fun i => i.elim) ?_ fun i => i.elim
    obtain ⟨i, hi⟩ := Finset.card_pos.1 (by rw [s.2]; exact Nat.succ_pos _ : 0 < s.1.card)
    refine (biInf_le W hi).trans (((le_iSup W i).trans hWU.le).trans ?_)
    simp

/- English proof (translation)
Establish `h` using `isRelAcyclic_pw K P 1 le_rfl`. Rewrite `h` using `[AbLaw.pw_one]`. Then use the resulting hypothesis.
-/
theorem isRelAcyclic_polAV (K : Type) [Field K] [IsAlgClosed K] (P : Out.PolAV (Sp K)) :
    IsRelAcyclic P.A.hom P.A.hom P.L := by
  have h := isRelAcyclic_pw K P 1 le_rfl
  rwa [AbLaw.pw_one] at h

/- English proof (translation)
Introduce `k _ S _ p A _ hA L hL hamp hsym U hU κ _ _ W hW hWU n`. Use `haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `t : Spec (CommRingCat.of Γ(S, U)) ⟶ S` to `hU.fromSpec`. Establish `h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t` using `IsPullback.of_hasPullback _ _`. Take `⟨hproj, hsm, -, -⟩` from `AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp Γ(S, U) t _ _ _ h`.

Use `haveI : Flat (pullback.snd A.hom t) := inferInstance`. Establish `hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)`. Rewrite using `[Scheme.Pullback.range_fst, hU.range_fromSpec]`.

Both sides reduce to the same expression. Establish `hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange` using `fun i => hrange ▸ (le_iSup W i).trans hWU.le`. Take `⟨e⟩` from `cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle`. Use `HomologicalComplex.ExactAt.of_iso ?_ e` and prove the remaining obligations. Use `(cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_` and prove the remaining obligations.

Use `cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _ (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n` and prove the remaining obligations. Introduce `P hP`. Use `letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P`. Set `χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P)` to `(algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)`. Use `⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]`. Introduce `κ' _ _ D' hD' hc' m`. Use `hA.proper` as an intermediate fact. Set `B` to `(Over.pullback t).obj A`. Establish `hB : IsAbelianScheme B` using `isAbelianScheme_pullback_obj t A hA`.

Establish `: IsProper B.hom` using `hB.proper`. Establish `hLB : (L.pull (pullback.fst A.hom t)).IsLB` using `LB.isLB_pull hL _`. Establish `hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t))` using `AmpleBaseChange.relAmple_of_isPullback hL hamp h`. Establish `hsB : Out.Sym B (L.pull (pullback.fst A.hom t))` using `PolBaseChange.sym_pull (isGrpPullback_pullback A t) hsym`. Set `A₀` to `(Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B`.

Establish `hA₀ : IsAbelianScheme A₀` using `isAbelianScheme_pullback_obj _ B hB`. Establish `hamp₀` using `AmpleBaseChange.relAmple_of_isPullback hLB hampB (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))`. Establish `hs₀` using `PolBaseChange.sym_pull (isGrpPullback_pullback B (Spec.map (CommRingCat.ofHom χ))) hsB`. Conclude with `AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ hs₀ ⊤ (isAffineOpen_top _) κ' D' hD' (by rw [hc', Scheme.Hom.preimage_top]) m`. Rewrite using `[← Scheme.Hom.preimage_iSup, hWU, ← hrange]`.

Conclude with `Scheme.Hom.preimage_opensRange _`.
-/
theorem isRelAcyclic_of_sym (AV : GlobalTheory.AmpleSym.AmpleVanishingSym) :
    ∀ (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] (p : S ⟶ Sp k) (A : Over S) [GrpObj A],
      IsAbelianScheme A → ∀ L : LB A.left, L.IsLB → Out.RelAmple A L → Out.Sym A L →
      IsRelAcyclic (A.hom ≫ p) A.hom L := by
  intro k _ S _ p A _ hA L hL hamp hsym U hU κ _ _ W hW hWU n
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      have := hA.proper
      let B := (Over.pullback t).obj A
      have hB : IsAbelianScheme B := isAbelianScheme_pullback_obj t A hA
      have : IsProper B.hom := hB.proper
      have hLB : (L.pull (pullback.fst A.hom t)).IsLB := LB.isLB_pull hL _
      have hampB : Out.RelAmple B (L.pull (pullback.fst A.hom t)) := AmpleBaseChange.relAmple_of_isPullback hL hamp h
      have hsB : Out.Sym B (L.pull (pullback.fst A.hom t)) :=
        PolBaseChange.sym_pull (isGrpPullback_pullback A t) hsym
      let A₀ := (Over.pullback (Spec.map (CommRingCat.ofHom χ))).obj B
      have hA₀ : IsAbelianScheme A₀ := isAbelianScheme_pullback_obj _ B hB
      have hamp₀ := AmpleBaseChange.relAmple_of_isPullback hLB hampB
        (IsPullback.of_hasPullback B.hom (Spec.map (CommRingCat.ofHom χ)))
      have hs₀ := PolBaseChange.sym_pull (isGrpPullback_pullback B (Spec.map (CommRingCat.ofHom χ))) hsB
      exact AV _ A₀ hA₀ _ (LB.isLB_pull hLB _) hamp₀ hs₀ ⊤ (isAffineOpen_top _) κ' D' hD'
        (by rw [hc', Scheme.Hom.preimage_top]) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

def polPull {S : Scheme.{0}} (P : Out.PolAV S) {R : Type} [CommRing R] (f : Sp R ⟶ S) : Out.PolAV (Sp R) :=
  have h := isGrpPullback_pullback P.A f
  have hL' := pull_isLB P.isLB (pullback.fst P.A.hom f)
  have := P.isAb.proper
  { A := (Over.pullback f).obj P.A
    isAb := isAbelianScheme_pullback_obj f P.A P.isAb
    g := P.g
    smoothDim := (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback h.1 P.smoothDim
    L := P.L.pull (pullback.fst P.A.hom f)
    isLB := hL'
    rigid := PolBaseChange.rigidified_pull h P.rigid
    sym := PolBaseChange.sym_pull h P.sym
    ample := AmpleBaseChange.relAmple_of_isPullback P.isLB P.ample h.1
    ktriv := by
      obtain ⟨w, hw⟩ := PolBaseChange.lbIso_refl hL'
      exact kTriv_pull h P.isLB hL' ((isGen_iff w).1 hw) P.ktriv }

/- English proof (translation)
Introduce `U hU κ _ _ W hW hWU n`. Set `A` to `Q.A`. Set `L : LB A.left` to `Q.L`. Establish `hA : IsAbelianScheme A` using `Q.isAb`. Establish `hL : L.IsLB` using `Q.isLB`.

Establish `hamp : Out.RelAmple A L` using `Q.ample`. Use `haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `t : Spec (CommRingCat.of Γ(S, U)) ⟶ S` to `hU.fromSpec`. Establish `h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t` using `IsPullback.of_hasPullback _ _`. Take `⟨hproj, hsm, -, -⟩` from `AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp Γ(S, U) t _ _ _ h`.

Use `haveI : Flat (pullback.snd A.hom t) := inferInstance`. Establish `hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U`. Use extensionality with `x`. Express the relevant statement in the definitionally equal form `x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)`. Rewrite using `[Scheme.Pullback.range_fst, hU.range_fromSpec]`.

Both sides reduce to the same expression. Establish `hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange` using `fun i => hrange ▸ (le_iSup W i).trans hWU.le`. Take `⟨e⟩` from `cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle`. Use `HomologicalComplex.ExactAt.of_iso ?_ e` and prove the remaining obligations. Use `(cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_` and prove the remaining obligations.

Use `cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _ (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n` and prove the remaining obligations. Introduce `P hP`. Use `letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P`. Set `χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P)` to `(algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)`. Use `⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]`. Introduce `κ' _ _ D' hD' hc' m`. Conclude with `isRelAcyclic_polAV _ (polPull (polPull Q t) (Spec.map (CommRingCat.ofHom χ))) ⊤ (isAffineOpen_top _) κ' D' hD' (hc'.trans (Scheme.Hom.preimage_top _).symm) m`. Rewrite using `[← Scheme.Hom.preimage_iSup, hWU, ← hrange]`. Conclude with `Scheme.Hom.preimage_opensRange _`.
-/
theorem isRelAcyclic_polAV_base (k : Type) [CommRing k] (S : Scheme.{0}) [IsLocallyNoetherian S] (p : S ⟶ Sp k)
    (Q : Out.PolAV S) : IsRelAcyclic (Q.A.hom ≫ p) Q.A.hom Q.L := by
  intro U hU κ _ _ W hW hWU n
  let A := Q.A
  let L : LB A.left := Q.L
  have hA : IsAbelianScheme A := Q.isAb
  have hL : L.IsLB := Q.isLB
  have hamp : Out.RelAmple A L := Q.ample
  haveI : IsNoetherianRing Γ(S, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let t : Spec (CommRingCat.of Γ(S, U)) ⟶ S := hU.fromSpec
  have h : IsPullback (pullback.fst A.hom t) (pullback.snd A.hom t) A.hom t := IsPullback.of_hasPullback _ _
  obtain ⟨hproj, hsm, -, -⟩ := AmpleBaseChange.isProjBy_smooth_isProper_geometricallyIntegral S A L hA hL hamp
    Γ(S, U) t _ _ _ h
  haveI : Flat (pullback.snd A.hom t) := inferInstance
  have hrange : (pullback.fst A.hom t).opensRange = A.hom ⁻¹ᵁ U := by
    ext x
    change x ∈ Set.range (pullback.fst A.hom t) ↔ A.hom x ∈ (U : Set S)
    rw [Scheme.Pullback.range_fst, hU.range_fromSpec]
    rfl
  have hle : ∀ i, W i ≤ (pullback.fst A.hom t).opensRange := fun i =>
    hrange ▸ (le_iSup W i).trans hWU.le
  obtain ⟨e⟩ := cechLB_pull_iso_of_isOpenImmersion k A.left (A.hom ≫ p) L _ (pullback.fst A.hom t) κ W hL hle
  refine HomologicalComplex.ExactAt.of_iso ?_ e
  refine (cechLB_exactAt_succ_iff (pullback.snd A.hom t) _ _ _ n).1 ?_
  refine cechLB_exactAt_succ_of_fibres Γ(S, U) _ (pullback.snd A.hom t) hproj _ (LB.isLB_pull hL _) ?_ κ _
    (fun i => (hW i).preimage_of_isOpenImmersion _ (hle i)) ?_ n
  · intro P hP
    letI : Field (Γ(S, U) ⧸ P) := Ideal.Quotient.field P
    let χ : Γ(S, U) →+* AlgebraicClosure (Γ(S, U) ⧸ P) :=
      (algebraMap (Γ(S, U) ⧸ P) (AlgebraicClosure (Γ(S, U) ⧸ P))).comp (Ideal.Quotient.mk P)
    refine ⟨AlgebraicClosure (Γ(S, U) ⧸ P), inferInstance, χ, ?_, ?_⟩
    · rw [RingHom.ker_comp_of_injective _ (algebraMap (Γ(S, U) ⧸ P) _).injective, Ideal.mk_ker]
    · intro κ' _ _ D' hD' hc' m
      exact isRelAcyclic_polAV _ (polPull (polPull Q t) (Spec.map (CommRingCat.ofHom χ))) ⊤ (isAffineOpen_top _) κ' D' hD'
        (hc'.trans (Scheme.Hom.preimage_top _).symm) m
  · rw [← Scheme.Hom.preimage_iSup, hWU, ← hrange]
    exact Scheme.Hom.preimage_opensRange _

end GlobalTheory.AmpleSymModel
