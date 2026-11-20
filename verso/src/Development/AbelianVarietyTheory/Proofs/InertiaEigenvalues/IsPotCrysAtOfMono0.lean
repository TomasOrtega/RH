import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsAttachedHodge
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CrystallineSumsTwistsCharactersExpectedJumps
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RestrictCrystallineDeRhamFiniteExt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallyNatCastNotMem
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCompNormEq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsConjugateDualTwistByTwistOfConjSelfDualStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HostEtaTildeCharacterExists
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsPlaceOverMoveValConjPl
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharExponentOfInfinityTypeStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsCsdOfCharOfRes
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.Mono0OfLpDimEqOne
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsEquivOfMapEq
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NotNonemptyZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIntSubMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOne
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitSumTensorDualOfWachMonoidal
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.JumpDictCrysAtOfWeights
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.LpCharCompatibilities
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.AbsPowOneNotIsAlgRat
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharpolySmulOfProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ResiduallyFiniteUnitOff
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsUnitaryRationalInfTypeSubgroupAndInfTypeUnique
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LocalGlobalAboveL
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ColRepSemisimple

noncomputable section

namespace GlobalTheory.TripleLocal

open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal NumberField IsDedekindDomain Polynomial Formalism.L2.Host
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.GalOfCusp GlobalTheory.HeightCounting
open GlobalTheory.RowTie (WDTie)
open Matrix (GeneralLinearGroup)

section Twist

variable {Γ k : Type} [Group Γ] [Field k] {a : ℕ}

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, h]`.
-/
theorem coe_scalar (u : kˣ) : ((GeneralLinearGroup.scalar (Fin a) u : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) =
    (u : k) • (1 : Matrix (Fin a) (Fin a) k) := by
  ext i j
  by_cases h : i = j <;> simp [GeneralLinearGroup.scalar, Matrix.diagonal, Matrix.one_apply, h]

def twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) : Γ →* GL (Fin a) k where
  toFun g := GeneralLinearGroup.scalar (Fin a) (c g) * r g
  map_one' := by simp
  map_mul' g h := by
    rw [map_mul, map_mul, map_mul]
    have e : GeneralLinearGroup.scalar (Fin a) (c h) * r g = r g * GeneralLinearGroup.scalar (Fin a) (c h) := by
      apply Units.ext
      rw [Units.val_mul, Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, Matrix.mul_one]
    simp only [mul_assoc]
    rw [← mul_assoc (GeneralLinearGroup.scalar (Fin a) (c h)), e, mul_assoc]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `((GeneralLinearGroup.scalar (Fin a) (c g) * r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = _`. Rewrite using `[Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem coe_twistBy (c : Γ →* kˣ) (r : Γ →* GL (Fin a) k) (g : Γ) :
    (twistBy c r g : Matrix (Fin a) (Fin a) k) = (c g : k) • (r g : Matrix (Fin a) (Fin a) k) := by
  change ((GeneralLinearGroup.scalar (Fin a) (c g) * r g : GL (Fin a) k) : Matrix (Fin a) (Fin a) k) = _
  rw [Units.val_mul, coe_scalar, Matrix.smul_mul, Matrix.one_mul]

end Twist

section G
variable {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω] {l : ℕ} [Fact l.Prime] {a : ℕ}

/- English proof (translation)
Take `⟨ψ, h1, h2⟩` from `GlobalTheory.PolChar.exists_compNorm_eq hν`. Use `⟨_, IsConjDualBy.isPolarized (m := 0) (χ := ψ) ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`. Conclude with `GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual hc ν`. Simplify using `using h2`.
-/
theorem isPolarized_twist {π : CuspSub E a} (hc : π.IsCsd) {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) :
    ∃ ψ, IsPolarized (π.twist ν) ψ := by
  obtain ⟨ψ, h1, h2⟩ := GlobalTheory.PolChar.exists_compNorm_eq hν
  refine ⟨_, IsConjDualBy.isPolarized (m := 0) (χ := ψ) ?_ ?_⟩
  · rw [h1]; exact GlobalTheory.T.isConjugateDualTwistBy_twist_of_conjSelfDual hc ν
  · simpa using h2

/- English proof (translation)
Establish `h` using `(CG.hasInfChar_ofChar χ τ).twist χ'`. Rewrite `h` using `[CG.twist_ofChar, Multiset.map_singleton]`. Use `h.infChar_eq` as an intermediate fact. Rewrite `this` using `[CG.infChar_ofChar]`. Simplify using `using this`.
-/
theorem expo_mul (χ χ' : HChar E) (τ : E →+* ℂ) : expo (χ * χ') τ = expo χ τ + expo χ' τ := by
  have h := (CG.hasInfChar_ofChar χ τ).twist χ'
  rw [CG.twist_ofChar, Multiset.map_singleton] at h
  have := h.infChar_eq
  rw [CG.infChar_ofChar] at this
  simpa using this

/- English proof (translation)
Use `expo_mul χ χ⁻¹ τ` as an intermediate fact. Rewrite `this` using `[mul_inv_cancel, CG.expo_one]`. Take the linear combination `-this`.
-/
theorem expo_inv (χ : HChar E) (τ : E →+* ℂ) : expo χ⁻¹ τ = -expo χ τ := by
  have := expo_mul χ χ⁻¹ τ
  rw [mul_inv_cancel, CG.expo_one] at this
  linear_combination -this

/- English proof (translation)
Take `⟨hu, he⟩` from `CGTrueModel.locPar_unr hL ν h (hν.1 w)`. Take `⟨c1, c2, c3⟩` from `WD.lpUnr_spec (h := h) {1} (by simp)`. Establish `hy : ParLaws.locPar hL (CG.ofChar ν) h = (WD.lpUnr h {1}).lpTw s`. Rewrite using `[WD.unr_eq_lpUnr _ hu, WD.unr_eq_lpUnr ((WD.lpUnr h {1}).lpTw s) ((WD.unr_tw _ _).2 c1), WD.frobEig_tw _ _ c1, he, c2]`. Use `congr 1`.

Simplify using `only [Multiset.map_singleton, one_mul]`. Use `congr 1`. Rewrite using `[Units.val_inv_eq_inv_val, hν.2.1 w, Complex.cpow_neg, inv_inv]`. Both sides reduce to the same expression. Rewrite using `[ParLaws.locPar_twist hL hF, hy, (WD.lpChar_laws (ParLaws.locPar hL π h) (ParLaws.locPar hL π h) (WD.lpUnr h {1}) s).2.2.1, (WD.lpChar_laws (ParLaws.locPar hL π h) (ParLaws.locPar hL π h) (WD.lpUnr h {1}) s).2.2.2.2.2 c1 (by simpa using c3) c2]`.
-/
theorem locPar_twist_abs (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (π : CG E a)
    {ν : HChar E} {s : ℝ} (hν : ν.IsAbsPow s) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) :
    ParLaws.locPar hL (π.twist ν) h = (ParLaws.locPar hL π h).lpTw s := by
  obtain ⟨hu, he⟩ := CGTrueModel.locPar_unr hL ν h (hν.1 w)
  obtain ⟨c1, c2, c3⟩ := WD.lpUnr_spec (h := h) {1} (by simp)
  have hy : ParLaws.locPar hL (CG.ofChar ν) h = (WD.lpUnr h {1}).lpTw s := by
    rw [WD.unr_eq_lpUnr _ hu, WD.unr_eq_lpUnr ((WD.lpUnr h {1}).lpTw s) ((WD.unr_tw _ _).2 c1), WD.frobEig_tw _ _ c1, he, c2]
    congr 1
    simp only [Multiset.map_singleton, one_mul]
    congr 1
    rw [Units.val_inv_eq_inv_val, hν.2.1 w, Complex.cpow_neg, inv_inv]
    rfl
  rw [ParLaws.locPar_twist hL hF, hy, (WD.lpChar_laws (ParLaws.locPar hL π h) (ParLaws.locPar hL π h) (WD.lpUnr h {1}) s).2.2.1,
    (WD.lpChar_laws (ParLaws.locPar hL π h) (ParLaws.locPar hL π h) (WD.lpUnr h {1}) s).2.2.2.2.2 c1 (by simpa using c3) c2]

/- English proof (translation)
Establish `key : ∀ W, IsInv (twistBy c ρ) W ↔ IsInv ρ W` using `fun W => forall_congr' fun g => forall₂_congr fun v _ => by`. Rewrite using `[coe_twistBy, Matrix.smul_mulVec, W.smul_mem_iff (c g).ne_zero]`. Conclude with `fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩`.
-/
theorem isSSRep_twistBy {Γ K : Type} [Group Γ] [Field K] {n : ℕ} (c : Γ →* Kˣ) {ρ : Γ →* GL (Fin n) K} (hs : IsSSRep ρ) :
    IsSSRep (twistBy c ρ) := by
  have key : ∀ W, IsInv (twistBy c ρ) W ↔ IsInv ρ W := fun W => forall_congr' fun g => forall₂_congr fun v _ => by
    rw [coe_twistBy, Matrix.smul_mulVec, W.smul_mem_iff (c g).ne_zero]
  exact fun W hW => (hs W ((key W).1 hW)).imp fun W' h' => ⟨(key W').2 h'.1, h'.2⟩

/- English proof (translation)
Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E a π w`. Rewrite using `[H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]`. Conclude with `congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm`.
-/
theorem wdOf_eq_locPar (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) {π : CuspSub E a}
    {χ : HChar (maximalRealSubfield E)} {ι : Qbar l ≃+* ℂ} {r : G E Ω →* GL (Fin a) (Qbar l)} {wt : ℤ}
    {HT : (E →+* Qbar l) → Multiset ℤ} (H : IsGalRepOf π χ ι r wt HT) {w : HeightOneSpectrum (𝓞 E)}
    (hl : ((l : ℕ) : 𝓞 E) ∉ w.asIdeal) {A : ValuationSubring Ω} (h : IsPlaceOver A w) :
    wdOf h hl ι r = (ParLaws.locPar hL (CG.mk π) h).lpTw ((1 - (a : ℝ)) / 2) := by
  obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E a π w
  rw [H.wdOf_eq hl (ParLaws.isRec_locRec hL h) hσ]
  exact congrArg (fun x : WD h => x.lpTw _) (ParLaws.locPar_mk hL hσ h).symm

/- English proof (translation)
Establish `htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace = ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace`. Introduce `g`. Use `congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 h)) (hc.matrix_trace) (hc'.matrix_trace) ?_) g` and prove the remaining obligations. Introduce and unpack `σ ⟨w, hw, B, hB, hσ⟩`. Establish `e` using `not_not.1 hw B σ hB hσ`.

Use `show Matrix.trace _ = Matrix.trace _`. Break down `Nat.eq_zero_or_pos a with ha | ha` into its components or cases. Substitute `ha` using the available equality. Simplify using `[Matrix.trace]`. Use `haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩`.

Rewrite using `[Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]`. Conclude with `GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' hs hs' htr`.
-/
theorem conj_of_frob (hD : ∀ S : Set (HeightOneSpectrum (𝓞 E)), S.Finite → Dense {g : G E Ω | ∃ w ∉ S, ∃ B : ValuationSubring Ω,
      IsPlaceOver (F := E) B w ∧ IsFrob (F := E) B (normV w) g})
    {r r' : G E Ω →* GL (Fin a) (Qbar l)} (hc : Continuous fun g => (r g : Matrix (Fin a) (Fin a) (Qbar l)))
    (hc' : Continuous fun g => (r' g : Matrix (Fin a) (Fin a) (Qbar l))) (hs : IsSSRep r) (hs' : IsSSRep r')
    (h : ∀ᶠ w : HeightOneSpectrum (𝓞 E) in Filter.cofinite, ∀ (B : ValuationSubring Ω) (g : G E Ω),
      IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g →
      (r g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly = (r' g : Matrix (Fin a) (Fin a) (Qbar l)).charpoly) :
    ∃ A : GL (Fin a) (Qbar l), ∀ g, r' g = A * r g * A⁻¹ := by
  have htr : ∀ g, ((r g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace =
      ((r' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)).trace := by
    intro g
    refine congrFun (Continuous.ext_on (hD _ (Filter.eventually_cofinite.1 h))
      (hc.matrix_trace) (hc'.matrix_trace) ?_) g
    rintro σ ⟨w, hw, B, hB, hσ⟩
    have e := not_not.1 hw B σ hB hσ
    show Matrix.trace _ = Matrix.trace _
    rcases Nat.eq_zero_or_pos a with ha | ha
    · subst ha
      simp [Matrix.trace]
    · haveI : Nonempty (Fin a) := ⟨⟨0, ha⟩⟩
      rw [Matrix.trace_eq_neg_charpoly_coeff, Matrix.trace_eq_neg_charpoly_coeff, e]
  exact GlobalTheory.TraceConj.conj_of_trace_eq _ _ a r r' hs hs' htr

/- English proof (translation)
Take `⟨L₁, r₁, m₁, hp₁⟩` from `hr`. Take `⟨L₂, c₂, m₂, hc₂⟩` from `hc`. Establish `l₁ : L₁.1 ≤ (supExt L₁ L₂).1` using `le_sup_left`. Establish `l₂ : L₂.1 ≤ (supExt L₁ L₂).1` using `le_sup_right`. Establish `m₁'` using `m₁.enlarge l₁`.

Establish `m₂'` using `m₂.enlarge l₂`. Take `⟨K', hK, hcr⟩` from `(local_ext P Bw l₁ r₁).2.2.1.2 hp₁`. Establish `hq` using `(local_ext P Bw l₂ c₂).1.2 hc₂`. Use `set L := supExt L₁ L₂ with hL`. Use `set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'`.

Use `set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'`. Set `d : ↥Gw →* (↥L.1)ˣ` to `Matrix.GeneralLinearGroup.det.comp c₂'`. Establish `hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1)` using `fun g => by`. Express the relevant statement in the definitionally equal form `_ = Matrix.det _`. Rewrite using `[Matrix.det_fin_one]`.

Establish `hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l)` using `fun g => by`. Establish `e` using `congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2`. Rewrite using `[← hd]`. Use `e.trans ?_` and prove the remaining obligations. Rewrite using `[MonoidHom.comp_apply, coe_scalar]`.

Simplify using the standard rewrite rules. Establish `hM : IsModel Bw (twistBy c r) L (twistBy d r₁')`. Use `⟨m₁'.1, ?_⟩` and prove the remaining obligations. Use extensionality with `g i j`. Establish `e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) = (r g : Matrix (Fin a) (Fin a) (Om l)) i j` using `congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2`.

Express the relevant statement in the definitionally equal form `algebraMap ↥L.1 (Om l) (((twistBy d r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) = ((twistBy c r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j`. Rewrite using `[coe_twistBy, coe_twistBy, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, e]`. Conclude with `congrArg₂ (· * ·) (hcd g) rfl`. Use `⟨L, _, hM, K', hK, ?_⟩` and prove the remaining obligations. Set `θ : ↥(GK K') →* (↥L.1)ˣ` to `(d.comp Bw.e.symm.toMonoidHom).comp (Subgroup.inclusion (GK_le hK))`.

Use `(GlobalTheory.TopSteps.CrysRules.isCrys_iff T K' L _ _ θ (fun g x => ?_) ?_).1 hcr` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Bw.repE L (twistBy d r₁') _ x = _ • Bw.repE L r₁' _ x`. Rewrite using `[GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, coe_twistBy, Matrix.smul_mulVec]`. Both sides reduce to the same expression. Establish `h1` using `GlobalTheory.Per.TiedRestrict.isCrys_restrict hK (Bw.repE L c₂') T hq`.

Use `GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K') (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) h1` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(Bw.repE L c₂' _ x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0`. Rewrite using `[GlobalTheory.ConjLocal.repE_apply]`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]`. Conclude with `congrArg (· * x 0) (hd (Bw.e.symm (Subgroup.inclusion (GK_le hK) g)))`.
-/
theorem potCrys_twistBy {P : LocPrime l} {AI : LocAinf l P} (T : LocTied l P AI) {Gw : Subgroup (Ω ≃ₐ[E] Ω)} {O : Type} [CommRing O]
    [Algebra ℤ_[l] O] [TopologicalSpace O] (Bw : LocBridge l E Ω Gw O) (c : ↥Gw →* (Om l)ˣ) (r : ↥Gw →* GL (Fin a) (Om l))
    (hr : IsPotCrysAt P Bw r) (hc : IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp c)) :
    IsPotCrysAt P Bw (twistBy c r) := by
  obtain ⟨L₁, r₁, m₁, hp₁⟩ := hr
  obtain ⟨L₂, c₂, m₂, hc₂⟩ := hc
  have l₁ : L₁.1 ≤ (supExt L₁ L₂).1 := le_sup_left
  have l₂ : L₂.1 ≤ (supExt L₁ L₂).1 := le_sup_right
  have m₁' := m₁.enlarge l₁
  have m₂' := m₂.enlarge l₂
  obtain ⟨K', hK, hcr⟩ := (local_ext P Bw l₁ r₁).2.2.1.2 hp₁
  have hq := (local_ext P Bw l₂ c₂).1.2 hc₂
  set L := supExt L₁ L₂ with hL
  set r₁' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₁).toRingHom r₁ with hr₁'
  set c₂' := Formalism.MainNotions.N.mapRep (IntermediateField.inclusion l₂).toRingHom c₂ with hc₂'
  let d : ↥Gw →* (↥L.1)ˣ := Matrix.GeneralLinearGroup.det.comp c₂'
  have hd : ∀ g, ((c₂' g : GL (Fin 1) ↥L.1) : Matrix (Fin 1) (Fin 1) ↥L.1) 0 0 = (d g : ↥L.1) := fun g => by
    change _ = Matrix.det _
    rw [Matrix.det_fin_one]
  have hcd : ∀ g, ((d g : ↥L.1) : Om l) = (c g : Om l) := fun g => by
    have e := congrArg (fun f : ↥Gw →* GL (Fin 1) (Om l) => ((f g : GL (Fin 1) (Om l)) : Matrix (Fin 1) (Fin 1) (Om l)) 0 0) m₂'.2
    rw [← hd]
    refine e.trans ?_
    rw [MonoidHom.comp_apply, coe_scalar]
    simp
  have hM : IsModel Bw (twistBy c r) L (twistBy d r₁') := by
    refine ⟨m₁'.1, ?_⟩
    ext g i j
    have e : algebraMap ↥L.1 (Om l) (((r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
        (r g : Matrix (Fin a) (Fin a) (Om l)) i j :=
      congrArg (fun f : ↥Gw →* GL (Fin a) (Om l) => ((f g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j) m₁'.2
    change algebraMap ↥L.1 (Om l) (((twistBy d r₁' g : GL (Fin a) ↥L.1) : Matrix (Fin a) (Fin a) ↥L.1) i j) =
      ((twistBy c r g : GL (Fin a) (Om l)) : Matrix (Fin a) (Fin a) (Om l)) i j
    rw [coe_twistBy, coe_twistBy, Matrix.smul_apply, Matrix.smul_apply, smul_eq_mul, smul_eq_mul, map_mul, e]
    exact congrArg₂ (· * ·) (hcd g) rfl
  refine ⟨L, _, hM, K', hK, ?_⟩
  let θ : ↥(GK K') →* (↥L.1)ˣ := (d.comp Bw.e.symm.toMonoidHom).comp (Subgroup.inclusion (GK_le hK))
  refine (GlobalTheory.TopSteps.CrysRules.isCrys_iff T K' L _ _ θ (fun g x => ?_) ?_).1 hcr
  · change Bw.repE L (twistBy d r₁') _ x = _ • Bw.repE L r₁' _ x
    rw [GlobalTheory.ConjLocal.repE_apply, GlobalTheory.ConjLocal.repE_apply, coe_twistBy, Matrix.smul_mulVec]
    rfl
  · have h1 := GlobalTheory.Per.TiedRestrict.isCrys_restrict hK (Bw.repE L c₂') T hq
    refine GlobalTheory.Cmp.WachMonoidal.isCrys_of_equiv (P.PD K') (LinearEquiv.funUnique (Fin 1) ↥L.1 ↥L.1) (fun g x => ?_) h1
    change (Bw.repE L c₂' _ x) 0 = ((θ g : (↥L.1)ˣ) : ↥L.1) * x 0
    rw [GlobalTheory.ConjLocal.repE_apply]
    simp only [Matrix.mulVec, dotProduct, Finset.univ_unique, Finset.sum_singleton]
    exact congrArg (· * x 0) (hd (Bw.e.symm (Subgroup.inclusion (GK_le hK) g)))

/- English proof (translation)
Take `⟨χ, hχ⟩` from `hp`. Establish `hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg` using `(CG.isRegAlg_ofChar ψ).2 hr`. Take `⟨r, wt, HT, H⟩` from `hG E Ω l ι 1 le_rfl _ χ hreg hχ`. Establish `hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l))` using `Units.continuous_val.comp H.cont`. Establish `hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r`.

Use extensionality with `g i j`. Rewrite using `[MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]`. Rewrite using `[Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]`. Express the relevant statement in the definitionally equal form `Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _`. Rewrite using `[Matrix.det_fin_one]`.

Establish `hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x` using `GeneralLinearGroup.continuous_det`. Use `⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩` and prove the remaining obligations. Take `⟨y1, y2⟩` from `CGTrueModel.locPar_unr hL ψ hB (hu w)`. Establish `e1 : wdOf hB hl ι r = ParLaws.locPar hL (CG.ofChar ψ) hB`. Rewrite using `[wdOf_eq_locPar hL hF H hl hB, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]`.

Both sides reduce to the same expression. Establish `f` using `frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg`. Rewrite `f` using `[e1, y2]`. Establish `h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0)`. Simplify using `[Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]`.

Rewrite `f` using `[h1]`. Establish `f2` using `congrArg (fun p => p.coeff 0) f`. Simplify using `at f2`. Express the relevant statement in the definitionally equal form `ι (Matrix.det _) = _`. Rewrite using `[Matrix.det_fin_one]`.

Conclude with `f2.trans (Units.val_inv_eq_inv_val _).symm`. Take `⟨σ, hσ, -⟩` from `LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w`. Establish `hc` using `(H.above P AI hT w A h O Bw hj).crys σ hσ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL h) (ParLaws.toRep σ)).1 (by`. Rewrite using `[← ParLaws.locPar_mk hL hσ h]`. Conclude with `(CGTrueModel.locPar_unr hL ψ h (hu w)).1))`.

Establish `e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F` using `E) A).subtype) = r.comp (Dec (F := E) A).subtype := by`. Rewrite using `[← MonoidHom.comp_assoc, hsc]`. Rewrite using `[e]`. Conclude with `hc`.
-/
theorem exists_char (hL : GlobalTheory.Published.LocalLanglandsGL) (hF : GlobalTheory.Published.AutomorphicFormsFiniteGL) (hG : GlobalTheory.Published.GaloisRepOfPolarizedCuspidal)
    (ι : Qbar l ≃+* ℂ) (ψ : HChar E) (hu : ∀ v, ψ.UnrAt v) (hr : ∀ τ, ∃ n : ℤ, expo ψ τ = n)
    (hp : ∃ χ, IsPolarized ((CuspSub.triv E (le_refl 1)).twist ψ) χ) :
    ∃ c : G E Ω →* (Qbar l)ˣ, Continuous c ∧
      (∀ (w : HeightOneSpectrum (𝓞 E)), ((l : ℕ) : 𝓞 E) ∉ w.asIdeal → ∀ (B : ValuationSubring Ω) (g : G E Ω),
        IsPlaceOver (F := E) B w → IsFrob (F := E) B (normV w) g → ι (c g : Qbar l) = (((ψ.val w)⁻¹ : ℂˣ) : ℂ)) ∧
      ∀ (P : LocPrime l) (AI : LocAinf l P), Nonempty (LocTied l P AI) →
      ∀ (w : HeightOneSpectrum (𝓞 E)) (A : ValuationSubring Ω), IsPlaceOver A w →
      ∀ (O : Type) [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
        (Bw : LocBridge l E Ω (Dec (F := E) A) O), Pst.Induces Bw →
        IsCrysAt P Bw ((GeneralLinearGroup.scalar (Fin 1)).comp (c.comp (Dec (F := E) A).subtype)) := by
  obtain ⟨χ, hχ⟩ := hp
  have hreg : (CG.mk ((CuspSub.triv E (le_refl 1)).twist ψ)).IsRegAlg := (CG.isRegAlg_ofChar ψ).2 hr
  obtain ⟨r, wt, HT, H⟩ := hG E Ω l ι 1 le_rfl _ χ hreg hχ
  have hcr : Continuous fun g => (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) := Units.continuous_val.comp H.cont
  have hsc : (GeneralLinearGroup.scalar (Fin 1)).comp (Matrix.GeneralLinearGroup.det.comp r) = r := by
    ext g i j
    rw [MonoidHom.comp_apply, coe_scalar, Subsingleton.elim i 0, Subsingleton.elim j 0]
    rw [Matrix.smul_apply, Matrix.one_apply_eq, smul_eq_mul, mul_one]
    change Matrix.det (r g : Matrix (Fin 1) (Fin 1) (Qbar l)) = _
    rw [Matrix.det_fin_one]
  have hdet : Continuous fun x : GL (Fin 1) (Qbar l) => Matrix.GeneralLinearGroup.det x := GeneralLinearGroup.continuous_det
  refine ⟨MonoidHom.comp Matrix.GeneralLinearGroup.det r, hdet.comp H.cont, fun w hl B g hB hg => ?_, fun P AI hT w A h O _ _ _ Bw hj => ?_⟩
  · obtain ⟨y1, y2⟩ := CGTrueModel.locPar_unr hL ψ hB (hu w)
    have e1 : wdOf hB hl ι r = ParLaws.locPar hL (CG.ofChar ψ) hB := by
      rw [wdOf_eq_locPar hL hF H hl hB, show (1 - ((1 : ℕ) : ℝ)) / 2 = 0 by norm_num, WD.lpTw_zero]
      rfl
    have f := frobEig_wdOf hl ι hcr (e1 ▸ y1) hB hg
    rw [e1, y2] at f
    have h1 : (r g : Matrix (Fin 1) (Fin 1) (Qbar l)).charpoly = X - C ((r g : Matrix (Fin 1) (Fin 1) (Qbar l)) 0 0) := by
      simp [Matrix.charpoly, Matrix.det_fin_one, Matrix.charmatrix_apply]
    rw [h1] at f
    have f2 := congrArg (fun p => p.coeff 0) f
    simp at f2
    change ι (Matrix.det _) = _
    rw [Matrix.det_fin_one]
    exact f2.trans (Units.val_inv_eq_inv_val _).symm
  · obtain ⟨σ, hσ, -⟩ := LocEx.exists_isLocComp hF E 1 ((CuspSub.triv E (le_refl 1)).twist ψ) w
    have hc := (H.above P AI hT w A h O Bw hj).crys σ hσ ((ParLaws.unr_iff (ParLaws.isRec_locRec hL h) (ParLaws.toRep σ)).1 (by
      rw [← ParLaws.locPar_mk hL hσ h]
      exact (CGTrueModel.locPar_unr hL ψ h (hu w)).1))
    have e : (GeneralLinearGroup.scalar (Fin 1)).comp ((Matrix.GeneralLinearGroup.det.comp r).comp (Dec (F := E) A).subtype) =
        r.comp (Dec (F := E) A).subtype := by
      rw [← MonoidHom.comp_assoc, hsc]
    rw [e]
    exact hc

end G

/- English proof (translation)
The claim follows from `host_isCMField D.host; ∃ ξ : HChar D.host.E, (∀ v, ξ.UnrAt v) ∧ (CG.ofChar ξ).IsCsd ∧ (CG.ofChar ξ⁻¹).IsCsd ∧ ∀ τ, ∃ n : ℤ, expo ξ τ = n + 1 / 2 := by have := host_isCMField D.host obtain ⟨ξ, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host have hneg : (-1 : ℂˣ)⁻¹ = -1 := inv_e …`.
-/
theorem exists_halfChar (D : D7) : haveI := host_isCMField D.host; ∃ ξ : HChar D.host.E, (∀ v, ξ.UnrAt v) ∧
    (CG.ofChar ξ).IsCsd ∧ (CG.ofChar ξ⁻¹).IsCsd ∧ ∀ τ, ∃ n : ℤ, expo ξ τ = n + 1 / 2 := by
  have := host_isCMField D.host
  obtain ⟨ξ, h⟩ := GlobalTheory.Mem.EtaT.etaT_exists D.R D.host
  have hneg : (-1 : ℂˣ)⁻¹ = -1 := inv_eq_of_mul_eq_one_left (by simp)
  refine ⟨ξ, h.unr, isCsd_ofChar_of_res _ _ (Or.inr h.res), isCsd_ofChar_of_res _ _ (Or.inr ⟨fun v k => ?_, fun w k => ?_⟩), fun τ => ?_⟩
  · have e1 := h.res.1 v k
    have e2 : (ξ⁻¹.resFin v) k = ((ξ.resFin v) k)⁻¹ := by
      simp only [HChar.resFin, MonoidHom.finset_prod_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaFin
    split_ifs
    · rw [← inv_zpow, hneg]
    · exact inv_one
  · have e1 := h.res.2 w k
    have e2 : (ξ⁻¹.resInf w) k = ((ξ.resInf w) k)⁻¹ := by
      simp only [HChar.resInf, MonoidHom.finset_prod_apply, ← Finset.prod_inv_distrib]
      rfl
    rw [e2, e1]
    unfold etaInf
    split_ifs
    · exact hneg
    · exact inv_one
  · have hI : Function.Injective fun i => InfinitePlace.mk (embPsi D.host i) := fun i j e => by
      rcases InfinitePlace.mk_eq_iff.1 e with e | e
      · exact GlobalTheory.HalfIntChars.embPsi_inj D.host e
      · exact (GlobalTheory.HalfIntChars.embPsi_ne_conj D.host j i (e.symm.trans (RingHom.ext fun x => rfl))).elim
    obtain ⟨ρ, b, rfl⟩ := GlobalTheory.JumpDictionaryFoundation.exists_embOver D τ
    have h3 := (GlobalTheory.T.heckeChar_exponent_of_infinityType _ ξ).2.2 _ _ _ hI h.inf (D.eTau ρ)
    cases b
    · exact ⟨0, by rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ false = embPsi D.host (D.eTau ρ) from rfl, h3.1]; simp⟩
    · refine ⟨-1, ?_⟩
      rw [show GlobalTheory.IndefiniteRowSideFullHecke.JumpDictionary.embOver D ρ true = ComplexEmbedding.conjugate (embPsi D.host (D.eTau ρ)) from
        RingHom.ext (GlobalTheory.JumpDictionaryFoundation.embOver_true_apply D ρ), h3.2]
      norm_num

end GlobalTheory.TripleLocal

end
