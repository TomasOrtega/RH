import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.PerpIffOrth
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.ActMass
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RightActionThreeFamilies
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.NilradicalLatticeZMemSpan
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RowFrameCoherence.Torsor
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.WittFlags

noncomputable section

open scoped Classical
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.HidaSetting Formalism.L2.SG.TermOp Formalism.L2.SG.PackageTie2
  Formalism.L2.SG.Full

namespace Formalism.L2.SG.Pf.FibreCounting

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Count

variable {D : D7} {X : HidaSetting D} {Y : Full X} {u u' : D.what₂.Word}

/- English proof (translation)
Set `q : {Λ // Λ ∈ Y.what₂ u'}` to `⟨Λ', hΛ'⟩`. Establish `e1` using `Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN q)`. Establish `e2` using `Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q)`. Conclude with `Finite.of_equiv _ (e2.symm.trans e1)`.
-/
theorem autLz_finite (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) {Λ' : Submodule (𝓞 D.host.E) (VS D).V}
    (hΛ' : Λ' ∈ Y.what₂ u') : Finite (autLz D (X.Fu u') Λ') := by
  let q : {Λ // Λ ∈ Y.what₂ u'} := ⟨Λ', hΛ'⟩
  have e1 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN q)
  have e2 := Equiv.ofBijective _ (Formalism.L2.SG.Pf.Act.gamL_levi_bij (Y.cs u') Y.TR Y.hK hN q)
  exact Finite.of_equiv _ (e2.symm.trans e1)

/- English proof (translation)
Use `haveI := autLz_finite hN s₀.mem'`. Establish `hex : ∀ s : {s : TT Y u u' // s.toTerm = s₀.toTerm}, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V, c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧ (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧ ∃ n ∈ NLam s₀.lam (lf D …` using `fun s => fib_c s.2.symm`. Set `cf : {s : TT Y u u' // s.toTerm = s₀.toTerm} → (VS D).V ≃ₗ[D.host.E] (VS D).V` to `fun s => (hex s).choose`. Establish `hcf : ∀ s, _` using `fun s => (hex s).choose_spec`. Set `f : {s : TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam'` to `fun s => ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩`.

Use `⟨f, fun s s' hss => ?_, fun φ => ?_⟩` and prove the remaining obligations. Establish `hq` using `sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1 (congrArg Subtype.val hss)`. Take `⟨n, hn, ν, hν, he⟩` from `(hcf s).2.2.2`. Take `⟨n', hn', ν', hν', he'⟩` from `(hcf s').2.2.2`. Conclude with `Subtype.ext (eq_of_dec s.2.symm s'.2.symm hn hn' hν hν' (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1 (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)`.

Take `⟨φ, hφ⟩` from `φ`. Take `⟨g, hg⟩` from `(Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s₀.lam', s₀.mem'⟩).2 ⟨φ, hφ⟩`. Establish `hc₁s : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ stabF D (X.Fu u')` using `Formalism.L2.SG.Pf.Act.isoG_stab g.1`. Establish `hc₁ : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `hc₁s.1`. Establish `hc₁fix : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a`.

Introduce `a`. Use `Fin.lastCases ?_ (fun i => ?_) a` and prove the remaining obligations. Establish `hz : (X.Fu u').z = X.zu u'` using `X.flagZVector u'`. Simplify using `only [FlagG.fvec, Fin.snoc_last]`. Rewrite using `[hz]`.

Conclude with `Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)`. Establish `he : (X.Fu u').e i = X.eX i` using `congrFun (X.Fu_e u') i`. Simplify using `only [FlagG.fvec, Fin.snoc_castSucc]`. Rewrite using `[he]`. Conclude with `Formalism.L2.SG.Pf.Act.isoG_e g.1 i`.

Establish `hc₁g : Formalism.HermitianLatticesTheory.gmap (Formalism.L2.SG.Pf.Act.isoG g.1) s₀.lam' = s₀.lam'` using `Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s₀.lam', s₀.mem'⟩ g`. Establish `hφ' : ⇑(Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) hc₁s) = φ` using `congrArg Subtype.val hg`. Use `set c₁ := Formalism.L2.SG.Pf.Act.isoG g.1 with hc₁def`. Establish `hA₁ : IsAutLam (VS D) s₀.lam' c₁` using `⟨hc₁, hc₁g⟩`. Take `⟨x, hx⟩` from `Formalism.L2.SG.Pf.ratPt_holds D X c₁⁻¹ (Subgroup.inv_mem _ hc₁)`.

Establish `hβ : c₁⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s₀.lam' (lf D (X.Fu u'))`. Use `⟨Formalism.L2.SG.Pf.isAutLam_inv hA₁, fun a => inv_fix (X.Fu u') hc₁fix a, ?_⟩` and prove the remaining obligations. Use `inv_fix (X.Fu u') hc₁fix (Fin.last _)` as an intermediate fact. Simplify `this` using `[FlagG.fvec]`. Use `set s₁ := Formalism.L2.SG.Pf.SatGramActR.tmap x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ with hs₁`.

Establish `ht : s₁.toTerm = s₀.toTerm` using `Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ hx s₀`. Establish `hcls` using `Formalism.L2.SG.Pf.SatGramActR.tmap_cls x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ hβ`. Take `⟨n₁, hn₁, n₁', hn₁', hlin⟩` from `lin_of_cls s₁ _ hcls`. Establish `hν₁ : c₁ * n₁' * c₁⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u'))` using `Formalism.L2.SG.Pf.nlam_conj hA₁ (fun a => (hc₁fix a).symm) hn₁'`. Establish `hlin' : s₁.lin = n₁ * s₀.lin * (c₁ * n₁' * c₁⁻¹) * c₁`.

Rewrite using `[hlin]`. Use `show n₁ * (s₀.lin * c₁⁻¹⁻¹) * n₁' = _`. Use `group`. Use `⟨⟨s₁, ht⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Take `⟨n, hn, ν, hν, he⟩` from `(hcf ⟨s₁, ht⟩).2.2.2`.

Establish `hwd` using `wd (F := X.Fu u) hn hn₁ hν hν₁ (hcf ⟨s₁, ht⟩).1 hc₁ (hcf ⟨s₁, ht⟩).2.1 hc₁g (hcf ⟨s₁, ht⟩).2.2.1 hc₁fix (he.symm.trans hlin')`. Use `show indQ (X.Fu u') (cf ⟨s₁, ht⟩) (hcf ⟨s₁, ht⟩).1 (hcf ⟨s₁, ht⟩).2.2.1 = φ`. Rewrite using `[← hφ']`. Use function extensionality and compare the values at `w`. Proceed by induction on `w using Submodule.Quotient.induction_on with`.

Consider the case `H y`. Rewrite using `[indQ_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq]`. Conclude with `hwd y y.2`.
-/
theorem fib_bij (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) (s₀ : TT Y u u') :
    ∃ f : {s : TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam', Function.Bijective f := by
  haveI := autLz_finite hN s₀.mem'
  have hex : ∀ s : {s : TT Y u u' // s.toTerm = s₀.toTerm}, ∃ c : (VS D).V ≃ₗ[D.host.E] (VS D).V,
      c ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT ∧ Formalism.HermitianLatticesTheory.gmap c s₀.lam' = s₀.lam' ∧
      (∀ a, c ((X.Fu u').fvec a) = (X.Fu u').fvec a) ∧
      ∃ n ∈ NLam s₀.lam (lf D (X.Fu u)), ∃ ν ∈ NLam s₀.lam' (lf D (X.Fu u')),
        (s : TT Y u u').lin = n * s₀.lin * ν * c :=
    fun s => fib_c s.2.symm
  let cf : {s : TT Y u u' // s.toTerm = s₀.toTerm} → (VS D).V ≃ₗ[D.host.E] (VS D).V := fun s => (hex s).choose
  have hcf : ∀ s, _ := fun s => (hex s).choose_spec
  let f : {s : TT Y u u' // s.toTerm = s₀.toTerm} → autLz D (X.Fu u') s₀.lam' := fun s =>
    ⟨indQ (X.Fu u') (cf s) (hcf s).1 (hcf s).2.2.1, indQ_mem (X.Fu u') _ _ _ (hcf s).2.1⟩
  refine ⟨f, fun s s' hss => ?_, fun φ => ?_⟩
  · have hq := sub_mem_of_indQ (X.Fu u') (hcf s).1 (hcf s).2.2.1 (hcf s').1 (hcf s').2.2.1
      (congrArg Subtype.val hss)
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf s).2.2.2
    obtain ⟨n', hn', ν', hν', he'⟩ := (hcf s').2.2.2
    exact Subtype.ext (eq_of_dec s.2.symm s'.2.symm hn hn' hν hν' (hcf s).1 (hcf s').1 (hcf s).2.1 (hcf s').2.1
      (hcf s).2.2.1 (hcf s').2.2.1 he he' hq)
  · obtain ⟨φ, hφ⟩ := φ
    obtain ⟨g, hg⟩ := (Formalism.L2.SG.Pf.Act.gamL_autLz_bij (Y.cs u') Y.hK hN ⟨s₀.lam', s₀.mem'⟩).2 ⟨φ, hφ⟩
    have hc₁s : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ stabF D (X.Fu u') := Formalism.L2.SG.Pf.Act.isoG_stab g.1
    have hc₁ : Formalism.L2.SG.Pf.Act.isoG g.1 ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hc₁s.1
    have hc₁fix : ∀ a, Formalism.L2.SG.Pf.Act.isoG g.1 ((X.Fu u').fvec a) = (X.Fu u').fvec a := by
      intro a
      refine Fin.lastCases ?_ (fun i => ?_) a
      · have hz : (X.Fu u').z = X.zu u' := X.flagZVector u'
        simp only [FlagG.fvec, Fin.snoc_last]
        rw [hz]
        exact Formalism.L2.SG.Pf.Act.isoG_fix g.1 _ (Or.inr rfl)
      · have he : (X.Fu u').e i = X.eX i := congrFun (X.Fu_e u') i
        simp only [FlagG.fvec, Fin.snoc_castSucc]
        rw [he]
        exact Formalism.L2.SG.Pf.Act.isoG_e g.1 i
    have hc₁g : Formalism.HermitianLatticesTheory.gmap (Formalism.L2.SG.Pf.Act.isoG g.1) s₀.lam' = s₀.lam' :=
      Formalism.L2.SG.Pf.Act.isoG_lat (Y.cs u') ⟨s₀.lam', s₀.mem'⟩ g
    have hφ' : ⇑(Formalism.L2.SG.Pf.Act.indW (Formalism.L2.SG.Pf.Act.isoG g.1) hc₁s) = φ := congrArg Subtype.val hg
    set c₁ := Formalism.L2.SG.Pf.Act.isoG g.1 with hc₁def
    have hA₁ : IsAutLam (VS D) s₀.lam' c₁ := ⟨hc₁, hc₁g⟩
    obtain ⟨x, hx⟩ := Formalism.L2.SG.Pf.ratPt_holds D X c₁⁻¹ (Subgroup.inv_mem _ hc₁)
    have hβ : c₁⁻¹ ∈ Formalism.L2.SG.Saturated.AutF s₀.lam' (lf D (X.Fu u')) := by
      refine ⟨Formalism.L2.SG.Pf.isAutLam_inv hA₁, fun a => inv_fix (X.Fu u') hc₁fix a, ?_⟩
      have := inv_fix (X.Fu u') hc₁fix (Fin.last _)
      simpa [FlagG.fvec] using this
    set s₁ := Formalism.L2.SG.Pf.SatGramActR.tmap x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ with hs₁
    have ht : s₁.toTerm = s₀.toTerm := Formalism.L2.SG.Pf.SatGramActR.toTerm_tmap _ _ _ hx s₀
    have hcls := Formalism.L2.SG.Pf.SatGramActR.tmap_cls x c₁⁻¹ Formalism.L2.SG.Pf.SatGramActR.autFConjN_holds hx s₀ hβ
    obtain ⟨n₁, hn₁, n₁', hn₁', hlin⟩ := lin_of_cls s₁ _ hcls
    have hν₁ : c₁ * n₁' * c₁⁻¹ ∈ NLam s₀.lam' (lf D (X.Fu u')) :=
      Formalism.L2.SG.Pf.nlam_conj hA₁ (fun a => (hc₁fix a).symm) hn₁'
    have hlin' : s₁.lin = n₁ * s₀.lin * (c₁ * n₁' * c₁⁻¹) * c₁ := by
      rw [hlin]
      show n₁ * (s₀.lin * c₁⁻¹⁻¹) * n₁' = _
      group
    refine ⟨⟨s₁, ht⟩, Subtype.ext ?_⟩
    obtain ⟨n, hn, ν, hν, he⟩ := (hcf ⟨s₁, ht⟩).2.2.2
    have hwd := wd (F := X.Fu u) hn hn₁ hν hν₁ (hcf ⟨s₁, ht⟩).1 hc₁ (hcf ⟨s₁, ht⟩).2.1 hc₁g
      (hcf ⟨s₁, ht⟩).2.2.1 hc₁fix (he.symm.trans hlin')
    show indQ (X.Fu u') (cf ⟨s₁, ht⟩) (hcf ⟨s₁, ht⟩).1 (hcf ⟨s₁, ht⟩).2.2.1 = φ
    rw [← hφ']
    funext w
    induction w using Submodule.Quotient.induction_on with
    | H y =>
      rw [indQ_mk, Formalism.L2.SG.Pf.Act.indW_mk, Submodule.Quotient.eq]
      exact hwd y y.2

/- English proof (translation)
Introduce `t _`. Take `⟨s₀, hs₀⟩` from `Formalism.L2.SG.Pf.Act.liftOnto (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D) (fun n hn => Formalism.L2.SG.Pf.ratPt_holds D X n hn) Y u u' (Formalism.L2.SG.Pf.toTermRel_holds X u u' (X.Fu u) (X.Fu u')) t`. Substitute `hs₀` using the available equality. Use `haveI := autLz_finite hN s₀.mem'`. Take `⟨f, hf⟩` from `fib_bij hN s₀`.

Set `e` to `Equiv.ofBijective f hf`. Use `haveI : Finite {s : TT Y u u' // s.toTerm = s₀.toTerm} := Finite.of_equiv _ e.symm`. Use `haveI : Fintype {s : TT Y u u' // s.toTerm = s₀.toTerm} := Fintype.ofFinite _`. Establish `hw : ∀ s : {s : TT Y u u' // s.toTerm = s₀.toTerm}, Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = Formalism.MainNotions.S.wRow D (X.Fu u') s₀.lam'` using `fun s => by`. Rewrite using `[lam'_eq s.2.symm]`.

Establish `hpos : 0 < Nat.card (autLz D (X.Fu u') s₀.lam')` using `by haveI : Nonempty (autLz D (X.Fu u') s₀.lam') := ⟨f ⟨s₀, rfl⟩⟩`. Conclude with `Nat.card_pos`. Use `show ∑' s : {s : TT Y u u' // s.toTerm = s₀.toTerm}, Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1`. Rewrite using `[tsum_fintype, Finset.sum_congr rfl (fun s _ => hw s), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Unfold `Formalism.MainNotions.S.wRow`.

Rewrite using `[← Nat.card_eq_fintype_card, Nat.card_congr e]`. Conclude with `mul_inv_cancel₀ (by exact_mod_cast hpos.ne')`.
-/
theorem liftMassC_of (hN : Formalism.L2.SG.PoincareInHH.Cut.NeatKu X u' Y.hK) : Formalism.L2.SG.Pf.RowForm.LiftMassC X Y u u' := by
  intro t _
  obtain ⟨s₀, hs₀⟩ := Formalism.L2.SG.Pf.Act.liftOnto (Formalism.L2.SG.Pf.WittFlags.LatIso_holds D)
    (fun n hn => Formalism.L2.SG.Pf.ratPt_holds D X n hn) Y u u'
    (Formalism.L2.SG.Pf.toTermRel_holds X u u' (X.Fu u) (X.Fu u')) t
  subst hs₀
  haveI := autLz_finite hN s₀.mem'
  obtain ⟨f, hf⟩ := fib_bij hN s₀
  let e := Equiv.ofBijective f hf
  haveI : Finite {s : TT Y u u' // s.toTerm = s₀.toTerm} := Finite.of_equiv _ e.symm
  haveI : Fintype {s : TT Y u u' // s.toTerm = s₀.toTerm} := Fintype.ofFinite _
  have hw : ∀ s : {s : TT Y u u' // s.toTerm = s₀.toTerm},
      Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = Formalism.MainNotions.S.wRow D (X.Fu u') s₀.lam' := fun s => by
    rw [lam'_eq s.2.symm]
  have hpos : 0 < Nat.card (autLz D (X.Fu u') s₀.lam') := by
    haveI : Nonempty (autLz D (X.Fu u') s₀.lam') := ⟨f ⟨s₀, rfl⟩⟩
    exact Nat.card_pos
  show ∑' s : {s : TT Y u u' // s.toTerm = s₀.toTerm}, Formalism.MainNotions.S.wRow D (X.Fu u') s.1.lam' = 1
  rw [tsum_fintype, Finset.sum_congr rfl (fun s _ => hw s), Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  unfold Formalism.MainNotions.S.wRow
  rw [← Nat.card_eq_fintype_card, Nat.card_congr e]
  exact mul_inv_cancel₀ (by exact_mod_cast hpos.ne')

end Count

end Formalism.L2.SG.Pf.FibreCounting
