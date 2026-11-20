import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.DoubleCosetSingleUnfolding
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.RegroupPfUnfold

noncomputable section

open scoped Classical ComplexConjugate ENNReal NNReal
open MeasureTheory

namespace Formalism.L2.SG.Pf.RegroupPf

open Formalism.L2.SG.FoldBound Formalism.L2.SG.PoincareSeriesSquareIntegrable NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

section Defs

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

def aC (ρ : cs.Cl) : X.B.I.Gf := (cs.h ρ : X.B.I.Gf) * X.xu u

def TermOn (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl) : Prop :=
  cs.lamOf ρ = t.lam ∧ cs'.lamOf ρ' = t.lam' ∧
    kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt ∈ X.K2

def Fterm (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (T' : Cu X u' hK) (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl)
    (x : X.B.I.Ginf) : ℂ :=
  conj (Ph X u hK T (x, aC cs ρ)) * Ph X u' hK T' (t.pt⁻¹ * (x, aC cs ρ))

def GamCol (ρ : cs.Cl) (ρ' : cs'.Cl) : Set X.B.I.GA :=
  {γ | γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I ∧ kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) γ ∈ X.K2}

def colRel (ρ : cs.Cl) (ρ' : cs'.Cl) : Setoid (GamCol cs cs' ρ ρ') where
  r a b := (a : X.B.I.GA)⁻¹ * b ∈ Srat X u'
  iseqv := ⟨fun a => by simp,
    fun {a b} h => by
      have := Subgroup.inv_mem _ h
      simpa [mul_inv_rev] using this,
    fun {a b c} h1 h2 => by
      have := Subgroup.mul_mem _ h1 h2
      simpa [mul_assoc] using this⟩

abbrev ColCl (ρ : cs.Cl) (ρ' : cs'.Cl) : Type := Quotient (colRel cs cs' ρ ρ')

def ColCl.pt {ρ : cs.Cl} {ρ' : cs'.Cl} (c : ColCl cs cs' ρ ρ') : X.B.I.GA :=
  ((Quotient.out c : GamCol cs cs' ρ ρ') : X.B.I.GA)

def SupportReindex (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA) : Prop :=
  ∀ (T' : Cu X u' hK) (ρ : cs.Cl) (y : X.B.I.Ginf),
    (∑' δ : Dt', Ph X u' hK T' ((δ : X.B.I.GA) * (y, aC cs ρ))) =
        ∑ ρ', ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ)) ∧
      (∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * (y, aC cs ρ))‖ₑ) =
        ∑ ρ', ∑' c : ColCl cs cs' ρ ρ', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ

variable (F0) in

def SlabAbs (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA) : Prop :=
  ∀ (Ωs : cs.Cl → Set X.B.I.Ginf), (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ)) →
  ∀ (T : Cu X u hK) (T' : Cu X u' hK) (ρ : cs.Cl),
    ∫⁻ y in Ωs ρ, ‖Ph X u hK T (y, aC cs ρ)‖ₑ * ∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * (y, aC cs ρ))‖ₑ
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤

variable (F0 F0') in

def OrbitUnfold (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (Ωs : cs.Cl → Set X.B.I.Ginf), (∀ ρ, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (NOcol F0 cs ρ) (Ωs ρ)) →
  ∀ (T : Cu X u hK) (T' : Cu X u' hK) (ρ : cs.Cl) (ρ' : cs'.Cl),
    ∫⁻ y in Ωs ρ, ‖Ph X u hK T (y, aC cs ρ)‖ₑ *
        ∑' c : ColCl cs cs' ρ ρ', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ →
    IntegrableOn (fun y => conj (Ph X u hK T (y, aC cs ρ)) *
        ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ)))
      (Ωs ρ) (Formalism.L2.SG.ProjRows.muInf X.B.I) ∧
    ∫ y in Ωs ρ, conj (Ph X u hK T (y, aC cs ρ)) *
        ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∑' t : GTerm X u u' F0 F0' what₂ rows',
        if TermOn cs cs' t ρ ρ' then ∫ x in FundOf t, Fterm cs hK T T' t ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)
        else 0

variable (F0 F0') in

def TermVal (hK : X.LevelSubgroupCharacter) : Prop :=
  ∀ (T : Cu X u hK) (T' : Cu X u' hK) (t : GTerm X u u' F0 F0' what₂ rows') (ρ : cs.Cl) (ρ' : cs'.Cl),
    TermOn cs cs' t ρ ρ' →
    ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        ∫ x in FundOf t, Fterm cs hK T T' t ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      inner ℂ (blk cs cs' FdN FdN' t ρ ρ' (sharp hK cs' T' ρ')) (sharp hK cs T ρ)

end Defs

section TermValPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut Matrix

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

variable (X u) in

/- English proof (translation)
Unfold `Formalism.L2.SG.HidaSetting.HidaSetting.psiFinU Formalism.L2.SG.HidaSetting.psiFin`. Establish `hf : X.B.I.fmat 1 = 1` using `by simp [Formalism.MainNotions.S.AutInst.fmat]`. Establish `h0 : ∀ a, Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a)) (X.B.I.fmat 1 *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (Formalism.L2.SG.HidaSetting.nxt X.eR (X.zR u) a)) = 0`. Introduce `a`. Rewrite using `[hf, Matrix.one_mulVec]`.

Unfold `Formalism.L2.SG.HidaSetting.nxt`. Use `split_ifs with h`. Rewrite using `[hA_f_e X, if_neg]`. Introduce `hc`. Use `congrArg Fin.val hc` as an intermediate fact.

Simplify using `at this`. Conclude with `adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a`. Simplify using `only [h0, Finset.sum_const_zero, Formalism.L2.SG.HidaSetting.divN, mul_zero]`. Conclude with `X.psiEf_int 0 (zero_mem _)`.
-/
theorem psiFinU_one : X.psiFinU u 1 = 1 := by
  unfold Formalism.L2.SG.HidaSetting.HidaSetting.psiFinU Formalism.L2.SG.HidaSetting.psiFin
  have hf : X.B.I.fmat 1 = 1 := by simp [Formalism.MainNotions.S.AutInst.fmat]
  have h0 : ∀ a, Formalism.L2.SG.HidaSetting.hA X.B.I (Formalism.L2.SG.HidaSetting.incl X.B.I (X.fR a))
      (X.B.I.fmat 1 *ᵥ Formalism.L2.SG.HidaSetting.incl X.B.I (Formalism.L2.SG.HidaSetting.nxt X.eR (X.zR u) a)) = 0 := by
    intro a
    rw [hf, Matrix.one_mulVec]
    unfold Formalism.L2.SG.HidaSetting.nxt
    split_ifs with h
    · rw [hA_f_e X, if_neg]
      intro hc
      have := congrArg Fin.val hc
      simp at this
    · exact adelicHermitian_hyperbolicF_anisotropic_eq_zero X u a
  simp only [h0, Finset.sum_const_zero, Formalism.L2.SG.HidaSetting.divN, mul_zero]
  exact X.psiEf_int 0 (zero_mem _)

/- English proof (translation)
Take `⟨h1, _hmul, hinv, hchi, hnorm⟩` from `hK`. Establish `hk'` using `hinv k hk`. Establish `hn1 : X.chi2 1 ≠ 0`. Introduce `h0`. Use `hnorm 1 h1` as an intermediate fact.

Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hone : X.chi2 1 = 1`. Establish `e1` using `hchi 1 h1 1 h1`. Rewrite `e1` using `[one_mul]`.

Establish `: X.chi2 1 * (X.chi2 1 - 1) = 0` using `by rw [mul_sub, mul_one, ← e1, sub_self]`. Break down `mul_eq_zero.mp this with h | h` into its components or cases. Conclude with `absurd h hn1`. Conclude with `sub_eq_zero.mp h`. Establish `hprod : X.chi2 k⁻¹ * X.chi2 k = 1`.

Rewrite using `[← hchi _ hk' _ hk, inv_mul_cancel, hone]`. Establish `hnk : ‖X.chi2 k‖ = 1` using `hnorm k hk`. Establish `hne : X.chi2 k ≠ 0`. Introduce `h0`. Rewrite `hnk` using `[h0, norm_zero]`.

Conclude with `zero_ne_one hnk`. Establish `hc : conj (X.chi2 k) * X.chi2 k = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnk]`. Evaluate the numerical expressions. Conclude with `mul_right_cancel₀ hne (hprod.trans hc.symm)`.
-/
theorem quadratic_character_inv (hK : X.LevelSubgroupCharacter) (k : X.B.I.Gf) (hk : k ∈ X.K2) : X.chi2 k⁻¹ = conj (X.chi2 k) := by
  obtain ⟨h1, _hmul, hinv, hchi, hnorm⟩ := hK
  have hk' := hinv k hk
  have hn1 : X.chi2 1 ≠ 0 := by
    intro h0
    have := hnorm 1 h1
    rw [h0, norm_zero] at this
    exact zero_ne_one this
  have hone : X.chi2 1 = 1 := by
    have e1 := hchi 1 h1 1 h1
    rw [one_mul] at e1
    have : X.chi2 1 * (X.chi2 1 - 1) = 0 := by rw [mul_sub, mul_one, ← e1, sub_self]
    rcases mul_eq_zero.mp this with h | h
    · exact absurd h hn1
    · exact sub_eq_zero.mp h
  have hprod : X.chi2 k⁻¹ * X.chi2 k = 1 := by
    rw [← hchi _ hk' _ hk, inv_mul_cancel, hone]
  have hnk : ‖X.chi2 k‖ = 1 := hnorm k hk
  have hne : X.chi2 k ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hnk
    exact zero_ne_one hnk
  have hc : conj (X.chi2 k) * X.chi2 k = 1 := by
    rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hnk]
    norm_num
  exact mul_right_cancel₀ hne (hprod.trans hc.symm)

/- English proof (translation)
Establish `h1 : (1 : X.B.I.Gf) ∈ X.NfinU u`. Simplify using `[Formalism.L2.SG.HidaSetting.HidaSetting.NfinU, Formalism.L2.SG.HidaSetting.Nfin, Formalism.L2.SG.Pf.unitaryCongruence.fmat_one]`. Establish `hdec : IsDec X u ((h : X.B.I.Gf) * X.xu u * k) 1 h k` using `⟨h1, hk, by rw [one_mul]⟩`. Establish `hex : ∃ n h' k', IsDec X u ((x, (h : X.B.I.Gf) * X.xu u * k) : X.B.I.GA).2 n h' k'` using `⟨1, h, k, hdec⟩`. Establish `hPh : Ph X u hK T (x, (h : X.B.I.Gf) * X.xu u * k) = phVal X u hK T x hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec.choose` using `dif_pos hex`.

Rewrite using `[hPh, hWD T x _ _ _ _ _ _ _ hex.choose_spec.choose_spec.choose_spec hdec]`. Simplify using `only [phVal, psiFinU_one, one_mul]`.
-/
theorem ph_col (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (T : Cu X u hK) (x : X.B.I.Ginf) (h : Hfin X u)
    (k : X.B.I.Gf) (hk : k ∈ X.K2) :
    Ph X u hK T (x, (h : X.B.I.Gf) * X.xu u * k) =
      X.chi2 k * (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) (X.Wu u x) (1, h) := by
  have h1 : (1 : X.B.I.Gf) ∈ X.NfinU u := by
    simp [Formalism.L2.SG.HidaSetting.HidaSetting.NfinU, Formalism.L2.SG.HidaSetting.Nfin, Formalism.L2.SG.Pf.unitaryCongruence.fmat_one]
  have hdec : IsDec X u ((h : X.B.I.Gf) * X.xu u * k) 1 h k := ⟨h1, hk, by rw [one_mul]⟩
  have hex : ∃ n h' k', IsDec X u ((x, (h : X.B.I.Gf) * X.xu u * k) : X.B.I.GA).2 n h' k' := ⟨1, h, k, hdec⟩
  have hPh : Ph X u hK T (x, (h : X.B.I.Gf) * X.xu u * k) =
      phVal X u hK T x hex.choose hex.choose_spec.choose hex.choose_spec.choose_spec.choose := dif_pos hex
  rw [hPh, hWD T x _ _ _ _ _ _ _ hex.choose_spec.choose_spec.choose_spec hdec]
  simp only [phVal, psiFinU_one, one_mul]

/- English proof (translation)
Simplify using `[sharp, InnerProductSpace.toDual_symm_apply]`.
-/
theorem inner_sharp (hK : X.LevelSubgroupCharacter) (T : Cu X u hK) (ρ : cs.Cl) (ξ : X.Vpi u) :
    inner ℂ (sharp hK cs T ρ) ξ = (T : X.Vpi u →ₗ[ℂ] (Hinf X u × Hfin X u → ℂ)) ξ (1, cs.h ρ) := by
  simp [sharp, InnerProductSpace.toDual_symm_apply]

/- English proof (translation)
Introduce `T T' t ρ ρ' ht`. Establish `hk` using `ht.2.2`. Use `FiniteDimensional.complete ℂ (X.Vpi u)` as an intermediate fact. Use `set k := kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt with hkdef`. Establish `hF : ∀ x, Fterm cs hK T T' t ρ x = conj (X.chi2 k) * (inner ℂ (X.Wu u x) (sharp hK cs T ρ) * inner ℂ (sharp hK cs' T' ρ') (X.Wu u' (t.pt.1⁻¹ * x)))`.

Introduce `x`. Unfold `Fterm aC`. Establish `e1 : Ph X u hK T (x, (cs.h ρ : X.B.I.Gf) * X.xu u) = inner ℂ (sharp hK cs T ρ) (X.Wu u x)`. Use `ph_col hK hWD T x (cs.h ρ) 1 (one_mem_level_subgroup X)` as an intermediate fact. Rewrite `this` using `[mul_one]`.

Rewrite using `[this, chi2_apply_one X hK, one_mul, inner_sharp]`. Establish `e2 : t.pt⁻¹ * ((x, (cs.h ρ : X.B.I.Gf) * X.xu u) : X.B.I.GA) = (t.pt.1⁻¹ * x, (cs'.h ρ' : X.B.I.Gf) * X.xu u' * k⁻¹)`. Use `Prod.ext rfl ?_` and prove the remaining obligations. Simplify using `only [Prod.snd_mul, Prod.snd_inv, hkdef, kOf]`. Use `group`.

Rewrite using `[e1, e2, ph_col hK hWD' T' _ (cs'.h ρ') k⁻¹ (hK.2.2.1 _ hk), quadratic_character_inv hK k hk, ← inner_sharp cs' hK T' ρ', ← inner_conj_symm (X.Wu u x)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hint` using `hOI t`. Unfold `OOInt at hint`. Use `set μ := Formalism.L2.SG.ProjRows.muInf X.B.I`.

Establish `hint' : IntegrableOn (fun x => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x)) (sharp hK cs' T' ρ')) (FundOf t) μ` using `(ContinuousLinearMap.apply ℂ (X.Vpi u) (sharp hK cs' T' ρ')).integrable_comp hint`. Simplify using `only [hF]`. Rewrite using `[integral_const_mul]`. Establish `hb : blk cs cs' FdN FdN' t ρ ρ' = ((scl FdN FdN' (X` using `X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • (X.chi2 k • OOt t) := by`. Unfold `blk`.

Conclude with `if_pos ht`. Rewrite using `[hb, _root_.smul_apply, _root_.smul_apply, inner_smul_left, inner_smul_left, Complex.conj_ofReal]`. Use `congr 2`. Unfold `OOt OO`. Rewrite using `[ContinuousLinearMap.integral_apply hint, ← inner_conj_symm, ← integral_inner hint', ← integral_conj]`.

Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [rankOneInnerOperator_apply, inner_smul_right, map_mul, inner_conj_symm]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem termVal_of (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hWD' : PhWellDef X u' hK)
    (hOI : OOIntAll X u u' F0 F0' what₂ rows') : TermVal F0 F0' cs cs' FdN FdN' hK := by
  intro T T' t ρ ρ' ht
  have hk := ht.2.2
  have := FiniteDimensional.complete ℂ (X.Vpi u)
  set k := kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) t.pt with hkdef
  have hF : ∀ x, Fterm cs hK T T' t ρ x = conj (X.chi2 k) *
      (inner ℂ (X.Wu u x) (sharp hK cs T ρ) * inner ℂ (sharp hK cs' T' ρ') (X.Wu u' (t.pt.1⁻¹ * x))) := by
    intro x
    unfold Fterm aC
    have e1 : Ph X u hK T (x, (cs.h ρ : X.B.I.Gf) * X.xu u) = inner ℂ (sharp hK cs T ρ) (X.Wu u x) := by
      have := ph_col hK hWD T x (cs.h ρ) 1 (one_mem_level_subgroup X)
      rw [mul_one] at this
      rw [this, chi2_apply_one X hK, one_mul, inner_sharp]
    have e2 : t.pt⁻¹ * ((x, (cs.h ρ : X.B.I.Gf) * X.xu u) : X.B.I.GA) =
        (t.pt.1⁻¹ * x, (cs'.h ρ' : X.B.I.Gf) * X.xu u' * k⁻¹) := by
      refine Prod.ext rfl ?_
      simp only [Prod.snd_mul, Prod.snd_inv, hkdef, kOf]
      group
    rw [e1, e2, ph_col hK hWD' T' _ (cs'.h ρ') k⁻¹ (hK.2.2.1 _ hk), quadratic_character_inv hK k hk,
      ← inner_sharp cs' hK T' ρ', ← inner_conj_symm (X.Wu u x)]
    ring
  have hint := hOI t
  unfold OOInt at hint
  set μ := Formalism.L2.SG.ProjRows.muInf X.B.I
  have hint' : IntegrableOn (fun x => rk1 (X.Wu u x) (X.Wu u' (t.pt.1⁻¹ * x)) (sharp hK cs' T' ρ'))
      (FundOf t) μ :=
    (ContinuousLinearMap.apply ℂ (X.Vpi u) (sharp hK cs' T' ρ')).integrable_comp hint
  simp only [hF]
  rw [integral_const_mul]
  have hb : blk cs cs' FdN FdN' t ρ ρ' =
      ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) • (X.chi2 k • OOt t) := by
    unfold blk; exact if_pos ht
  rw [hb, _root_.smul_apply, _root_.smul_apply, inner_smul_left, inner_smul_left,
    Complex.conj_ofReal]
  congr 2
  unfold OOt OO
  rw [ContinuousLinearMap.integral_apply hint, ← inner_conj_symm, ← integral_inner hint', ← integral_conj]
  refine integral_congr_ae (ae_of_all _ fun x => ?_)
  simp only [rankOneInnerOperator_apply, inner_smul_right, map_mul, inner_conj_symm]
  ring

end TermValPf

section Reindex

variable {G : Type*} [Group G] {M : Type*} [AddCommMonoid M] [TopologicalSpace M]

/- English proof (translation)
Take `⟨hDΓ, hU⟩` from `hD`. Establish `hex : ∀ i, ∃ q : S × D, ((q.1 : G) * (q.2 : G)) = (p i)⁻¹` using `fun i => (hU _ (Γ.inv_mem (hp i))).exists`. Use `choose q hq using hex`. Establish `hFq : ∀ i, F ((q i).2 : G) = F (p i)⁻¹`. Introduce `i`.

Rewrite using `[← hq i, hF _ (q i).1.2]`. Establish `hinjq : Function.Injective (fun i => (q i).2)`. Introduce `i j hij`. Apply `hinj` to reduce the goal to its premises. Establish `hd : ((q i).2 : G) = ((q j).2 : G)` using `congrArg Subtype.val hij`.

Establish `ej' : p j = (((q j).1 : G) * ((q j).2 : G))⁻¹` using `by rw [hq j, inv_inv]`. Establish `e3 : (p i)⁻¹ * p j = ((q i).1 : G) * ((q j).1 : G)⁻¹`. Rewrite using `[← hq i, ej', hd]`. Use `group`. Rewrite using `[e3]`.

Conclude with `S.mul_mem (q i).1.2 (S.inv_mem (q j).1.2)`. Establish `hsupp : Function.support (fun δ : D => F δ) ⊆ Set.range (fun i => (q i).2)`. Introduce `δ hδ`. Take `⟨i, hi⟩` from `hcov δ (hDΓ δ.2) hδ`. Use `⟨i, ?_⟩` and prove the remaining obligations.

Establish `huq` using `(hU _ (Γ.inv_mem (hp i))).unique (y₁ := q i) (y₂ := ((⟨(δ * p i)⁻¹, S.inv_mem hi⟩ : S), δ)) (hq i) (by show (δ * p i)⁻¹ * (δ : G) = (p i)⁻¹ group)`. Conclude with `congrArg Prod.snd huq`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem reindex_tsum (Γ S : Subgroup G) (D : Set G) (hD : Formalism.L2.SG.FoldBound.IsRightTransversal Γ S D)
    {I : Type*} (p : I → G) (hp : ∀ i, p i ∈ Γ) (hinj : ∀ i j, (p i)⁻¹ * p j ∈ S → i = j)
    (F : G → M) (hF : ∀ s ∈ S, ∀ γ, F (s * γ) = F γ) (hcov : ∀ γ ∈ Γ, F γ ≠ 0 → ∃ i, γ * p i ∈ S) :
    ∑' δ : D, F δ = ∑' i, F (p i)⁻¹ := by
  obtain ⟨hDΓ, hU⟩ := hD
  have hex : ∀ i, ∃ q : S × D, ((q.1 : G) * (q.2 : G)) = (p i)⁻¹ :=
    fun i => (hU _ (Γ.inv_mem (hp i))).exists
  choose q hq using hex
  have hFq : ∀ i, F ((q i).2 : G) = F (p i)⁻¹ := by
    intro i
    rw [← hq i, hF _ (q i).1.2]
  have hinjq : Function.Injective (fun i => (q i).2) := by
    intro i j hij
    apply hinj
    have hd : ((q i).2 : G) = ((q j).2 : G) := congrArg Subtype.val hij
    have ej' : p j = (((q j).1 : G) * ((q j).2 : G))⁻¹ := by rw [hq j, inv_inv]
    have e3 : (p i)⁻¹ * p j = ((q i).1 : G) * ((q j).1 : G)⁻¹ := by
      rw [← hq i, ej', hd]
      group
    rw [e3]
    exact S.mul_mem (q i).1.2 (S.inv_mem (q j).1.2)
  have hsupp : Function.support (fun δ : D => F δ) ⊆ Set.range (fun i => (q i).2) := by
    intro δ hδ
    obtain ⟨i, hi⟩ := hcov δ (hDΓ δ.2) hδ
    refine ⟨i, ?_⟩
    have huq := (hU _ (Γ.inv_mem (hp i))).unique (y₁ := q i)
      (y₂ := ((⟨(δ * p i)⁻¹, S.inv_mem hi⟩ : S), δ)) (hq i) (by
        show (δ * p i)⁻¹ * (δ : G) = (p i)⁻¹
        group)
    exact congrArg Prod.snd huq
  calc ∑' δ : D, F δ = ∑' i, F ((q i).2 : G) := (Function.Injective.tsum_eq hinjq hsupp).symm
    _ = ∑' i, F (p i)⁻¹ := tsum_congr hFq

end Reindex

section SupportPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

def ColUniq : Prop :=
  ∀ (ρ : cs.Cl) (ρ₁ ρ₂ : cs'.Cl) (γ₁ γ₂ : X.B.I.GA), γ₁ ∈ GamCol cs cs' ρ ρ₁ → γ₂ ∈ GamCol cs cs' ρ ρ₂ →
    γ₁⁻¹ * γ₂ ∈ Srat X u' → ρ₁ = ρ₂

def ColCover : Prop :=
  ∀ (ρ : cs.Cl) (δ : X.B.I.GA), δ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I →
    (∃ n h k, IsDec X u' (δ.2 * aC cs ρ) n h k) → ∃ (ρ' : cs'.Cl) (γ : X.B.I.GA), γ ∈ GamCol cs cs' ρ ρ' ∧ δ * γ ∈ Srat X u'

/- English proof (translation)
Introduce `T' ρ y`. Use `set x : X.B.I.GA := (y, aC cs ρ) with hx`. Set `I` to `Σ ρ' : cs'.Cl, ColCl cs cs' ρ ρ'`. Set `p : I → X.B.I.GA` to `fun i => ColCl.pt cs cs' i.2`. Establish `hp : ∀ i, p i ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I` using `fun i => (Quotient.out i.2).2.1`.

Establish `hinj : ∀ i j, (p i)⁻¹ * p j ∈ Srat X u' → i = j`. Introduce and unpack `⟨ρ₁, c₁⟩ ⟨ρ₂, c₂⟩ h`. Establish `e` using `hU ρ ρ₁ ρ₂ _ _ (Quotient.out c₁).2 (Quotient.out c₂).2 h`. Substitute `e` using the available equality. Establish `: c₁ = c₂`.

Rewrite using `[← Quotient.out_eq c₁, ← Quotient.out_eq c₂]`. Conclude with `Quotient.sound h`. Rewrite using `[this]`. Establish `hcov : ∀ (F : X.B.I.GA → ℂ), (∀ γ, F γ ≠ 0 → ∃ n h k, IsDec X u' (γ.2 * aC cs ρ) n h k) → ∀ γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, F γ ≠ 0 → ∃ i, γ * p i ∈ Srat X u'`. Introduce `F hF γ hγ hne`.

Take `⟨ρ', γ', hγ', hs⟩` from `hC ρ γ hγ (hF γ hne)`. Use `⟨⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩, ?_⟩` and prove the remaining obligations. Establish `hr : (colRel cs cs' ρ ρ') ⟨γ', hγ'⟩ (Quotient.out (Quotient.mk (colRel cs cs' ρ ρ') ⟨γ', hγ'⟩))` using `Quotient.exact (Quotient.out_eq _).symm`. Establish `: γ * p ⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩ = (γ * γ') * (γ'⁻¹ * p ⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩)` using `by group`. Rewrite using `[this]`.

Conclude with `(Srat X u').mul_mem hs hr`. Establish `hsupp : ∀ γ, Ph X u' hK T' (γ * x) ≠ 0 → ∃ n h k, IsDec X u' (γ.2 * aC cs ρ) n h k`. Introduce `γ hne`. Assume the negation of the conclusion as `hn`. Conclude with `hne (ph_eq_zero X u' hK T' _ hn)`.

Establish `hinvF : ∀ s ∈ Srat X u', ∀ γ, Ph X u' hK T' (s * γ * x) = Ph X u' hK T' (γ * x)`. Introduce `s hs γ`. Rewrite using `[mul_assoc, hinv T' s hs]`. Establish `h1` using `reindex_tsum _ (Srat X u') Dt' hD' p hp hinj (fun γ => Ph X u' hK T' (γ * x)) hinvF (hcov _ hsupp)`. Establish `h2` using `reindex_tsum _ (Srat X u') Dt' hD' p hp hinj (fun γ => ‖Ph X u' hK T' (γ * x)‖ₑ) (fun s hs γ => congrArg (‖·‖ₑ) (hinvF s hs γ)) (fun γ hγ hne => hcov (fun γ => Ph X u' hK T' (γ * x)) hsupp γ hγ (by`.

Introduce `h0`. Apply `hne` to reduce the goal to its premises. Simplify using `only [h0, enorm_zero]))`. Establish `hfin : ∑' i, ‖Ph X u' hK T' ((p i)⁻¹ * x)‖ₑ ≠ ⊤`. Rewrite using `[← h2]`.

Establish `e : ∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * x)‖ₑ = ENNReal.ofReal (∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * x)‖)`. Rewrite using `[ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum T' x)]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `ENNReal.ofReal_ne_top`.

Establish `hsI : Summable fun i => Ph X u' hK T' ((p i)⁻¹ * x)`. Use `Summable.of_nnnorm ?_` and prove the remaining obligations. Conclude with `ENNReal.tsum_coe_ne_top_iff_summable.1 hfin`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[h1]`.

Rewrite using `[hsI.tsum_sigma, tsum_fintype]`. Rewrite using `[h2, ENNReal.tsum_sigma', tsum_fintype]`.
-/
theorem supportReindex_of (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA) (hD' : IsReps X u' Dt')
    (hinv : ∀ (T' : Cu X u' hK), ∀ s ∈ Srat X u', ∀ y, Ph X u' hK T' (s * y) = Ph X u' hK T' y)
    (hsum : ∀ (T' : Cu X u' hK) x, Summable fun δ : Dt' => ‖Ph X u' hK T' ((δ : X.B.I.GA) * x)‖)
    (hU : ColUniq cs cs') (hC : ColCover cs cs') : SupportReindex cs cs' hK Dt' := by
  intro T' ρ y
  set x : X.B.I.GA := (y, aC cs ρ) with hx
  let I := Σ ρ' : cs'.Cl, ColCl cs cs' ρ ρ'
  let p : I → X.B.I.GA := fun i => ColCl.pt cs cs' i.2
  have hp : ∀ i, p i ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I := fun i => (Quotient.out i.2).2.1
  have hinj : ∀ i j, (p i)⁻¹ * p j ∈ Srat X u' → i = j := by
    rintro ⟨ρ₁, c₁⟩ ⟨ρ₂, c₂⟩ h
    have e := hU ρ ρ₁ ρ₂ _ _ (Quotient.out c₁).2 (Quotient.out c₂).2 h
    subst e
    have : c₁ = c₂ := by
      rw [← Quotient.out_eq c₁, ← Quotient.out_eq c₂]
      exact Quotient.sound h
    rw [this]
  have hcov : ∀ (F : X.B.I.GA → ℂ), (∀ γ, F γ ≠ 0 → ∃ n h k, IsDec X u' (γ.2 * aC cs ρ) n h k) →
      ∀ γ ∈ Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I, F γ ≠ 0 → ∃ i, γ * p i ∈ Srat X u' := by
    intro F hF γ hγ hne
    obtain ⟨ρ', γ', hγ', hs⟩ := hC ρ γ hγ (hF γ hne)
    refine ⟨⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩, ?_⟩
    have hr : (colRel cs cs' ρ ρ') ⟨γ', hγ'⟩ (Quotient.out (Quotient.mk (colRel cs cs' ρ ρ') ⟨γ', hγ'⟩)) :=
      Quotient.exact (Quotient.out_eq _).symm
    have : γ * p ⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩ = (γ * γ') * (γ'⁻¹ * p ⟨ρ', Quotient.mk _ ⟨γ', hγ'⟩⟩) := by group
    rw [this]
    exact (Srat X u').mul_mem hs hr
  have hsupp : ∀ γ, Ph X u' hK T' (γ * x) ≠ 0 → ∃ n h k, IsDec X u' (γ.2 * aC cs ρ) n h k := by
    intro γ hne
    by_contra hn
    exact hne (ph_eq_zero X u' hK T' _ hn)
  have hinvF : ∀ s ∈ Srat X u', ∀ γ, Ph X u' hK T' (s * γ * x) = Ph X u' hK T' (γ * x) := by
    intro s hs γ; rw [mul_assoc, hinv T' s hs]
  have h1 := reindex_tsum _ (Srat X u') Dt' hD' p hp hinj (fun γ => Ph X u' hK T' (γ * x)) hinvF
    (hcov _ hsupp)
  have h2 := reindex_tsum _ (Srat X u') Dt' hD' p hp hinj (fun γ => ‖Ph X u' hK T' (γ * x)‖ₑ)
    (fun s hs γ => congrArg (‖·‖ₑ) (hinvF s hs γ))
    (fun γ hγ hne => hcov (fun γ => Ph X u' hK T' (γ * x)) hsupp γ hγ (by
      intro h0; apply hne; simp only [h0, enorm_zero]))
  have hfin : ∑' i, ‖Ph X u' hK T' ((p i)⁻¹ * x)‖ₑ ≠ ⊤ := by
    rw [← h2]
    have e : ∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * x)‖ₑ =
        ENNReal.ofReal (∑' δ : Dt', ‖Ph X u' hK T' ((δ : X.B.I.GA) * x)‖) := by
      rw [ENNReal.ofReal_tsum_of_nonneg (fun _ => norm_nonneg _) (hsum T' x)]
      simp
    rw [e]
    exact ENNReal.ofReal_ne_top
  have hsI : Summable fun i => Ph X u' hK T' ((p i)⁻¹ * x) := by
    refine Summable.of_nnnorm ?_
    exact ENNReal.tsum_coe_ne_top_iff_summable.1 hfin
  refine ⟨?_, ?_⟩
  · rw [h1]
    rw [hsI.tsum_sigma, tsum_fintype]
  · rw [h2, ENNReal.tsum_sigma', tsum_fintype]

end SupportPf

section OrbitPf

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.PoincareInHH.Cut Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (cs : ColSys X u what₂) (cs' : ColSys X u' rows')

variable (F0 F0') in

def OrbitAlg : Prop :=
  ∀ (ρ : cs.Cl) (ρ' : cs'.Cl), ∃ (N : Subgroup X.B.I.Ginf) (lift : N → X.B.I.GA),
    (N : Set X.B.I.Ginf) = NOcol F0 cs ρ ∧ Countable N ∧ Countable (ColCl cs cs' ρ ρ') ∧
    (∀ n, (lift n).1 = n) ∧ lift 1 = 1 ∧ (∀ n m, lift (n * m) = lift n * lift m) ∧
    (∀ n, lift n ∈ Srat X u) ∧ (∀ n, (aC cs ρ)⁻¹ * (lift n).2 * aC cs ρ ∈ X.K2) ∧
    (∀ c : ColCl cs cs' ρ ρ', ∃ t : GTerm X u u' F0 F0' what₂ rows', TermOn cs cs' t ρ ρ' ∧
      ∃ n : N, (lift n * t.pt)⁻¹ * ColCl.pt cs cs' c ∈ Srat X u') ∧
    (∀ (t t' : GTerm X u u' F0 F0' what₂ rows') (n : N), TermOn cs cs' t ρ ρ' → TermOn cs cs' t' ρ ρ' →
      (lift n * t.pt)⁻¹ * t'.pt ∈ Srat X u' → t = t') ∧
    (∀ t : GTerm X u u' F0 F0' what₂ rows', TermOn cs cs' t ρ ρ' →
      ROinf t = {y | ∃ n : N, (n : X.B.I.Ginf) = y ∧ (lift n * t.pt)⁻¹ * t.pt ∈ Srat X u'})

/- English proof (translation)
Conclude with `(colRel cs cs' ρ ρ').iseqv.symm (@Quotient.mk_out _ (colRel cs cs' ρ ρ') γ)`.
-/
theorem rel_out {ρ : cs.Cl} {ρ' : cs'.Cl} (γ : GamCol cs cs' ρ ρ') :
    (γ : X.B.I.GA)⁻¹ * ColCl.pt cs cs' (Quotient.mk (colRel cs cs' ρ ρ') γ) ∈ Srat X u' := by
  exact (colRel cs cs' ρ ρ').iseqv.symm (@Quotient.mk_out _ (colRel cs cs' ρ ρ') γ)

/- English proof (translation)
Introduce `Ωs hΩ T T' ρ ρ' hbound`. Take `⟨N, lift, hNset, hNc, hCc, hl1, hlone, hlmul, hlS, hlK, hcov, huniq, hstab⟩` from `hOA ρ ρ'`. Use `set a := aC cs ρ with ha`. Establish `hmemG : ∀ (n : N) (γ : GamCol cs cs' ρ ρ'), lift n * (γ : X.B.I.GA) ∈ GamCol cs cs' ρ ρ'`. Introduce `n γ`.

Use `⟨(Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem (Subgroup.mem_inf.1 (hlS n)).1 γ.2.1, ?_⟩` and prove the remaining obligations. Establish `e : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) (lift n * (γ : X.B.I.GA)) = (a⁻¹ * (lift n).2 * a) * kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) (γ : X.B.I.GA)`. Simplify using `only [kOf, Prod.snd_mul, ha, aC]`. Use `group`. Rewrite using `[e]`.

Conclude with `hK.2.1 _ (hlK n) _ γ.2.2`. Set `act : N → ColCl cs cs' ρ ρ' → ColCl cs cs' ρ ρ'` to `fun n c => Quotient.mk _ ⟨lift n * ColCl.pt cs cs' c, hmemG n (Quotient.out c)⟩`. Establish `hact_pt : ∀ n c, (lift n * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' (act n c) ∈ Srat X u'` using `fun n c => rel_out cs cs' ⟨lift n * ColCl.pt cs cs' c, hmemG n (Quotient.out c)⟩`. Establish `h1 : ∀ c, act 1 c = c`. Introduce `c`.

Use `conv_rhs => rw [← Quotient.out_eq c]`. Apply `Quotient.sound` to reduce the goal to its premises. Use `show (lift 1 * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' c ∈ Srat X u'`. Rewrite using `[hlone, one_mul, inv_mul_cancel]`. Conclude with `(Srat X u').one_mem`.

Establish `hmul : ∀ n m c, act (n * m) c = act n (act m c)`. Introduce `n m c`. Apply `Quotient.sound` to reduce the goal to its premises. Use `show (lift (n * m) * ColCl.pt cs cs' c)⁻¹ * (lift n * ColCl.pt cs cs' (act m c)) ∈ Srat X u'`. Establish `e : (lift (n * m) * ColCl.pt cs cs' c)⁻¹ * (lift n * ColCl.pt cs cs' (act m c)) = (lift m * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' (act m c)`.

Rewrite using `[hlmul]`. Use `group`. Rewrite using `[e]`. Conclude with `hact_pt m c`. Set `F : ColCl cs cs' ρ ρ' → X.B.I.Ginf → ℂ` to `fun c y => conj (Ph X u hK T (y, a)) * Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, a))`.

Establish `hFm : ∀ c, Measurable (F c)`. Introduce `c`. Use `(Complex.continuous_conj.measurable.comp ((hm T).comp measurable_prodMk_right)).mul ?_` and prove the remaining obligations. Conclude with `(hm' T').comp ((measurable_const_mul _).comp measurable_prodMk_right)`. Establish `hPh'rel : ∀ (γ δ : X.B.I.GA), γ⁻¹ * δ ∈ Srat X u' → ∀ x, Ph X u' hK T' (δ⁻¹ * x) = Ph X u' hK T' (γ⁻¹ * x)`.

Introduce `γ δ h x`. Establish `e : δ⁻¹ * x = (γ⁻¹ * δ)⁻¹ * (γ⁻¹ * x)` using `by group`. Rewrite using `[e, hinv' T' _ ((Srat X u').inv_mem h)]`. Establish `hFeq : ∀ (n : N) c y, F (act n c) y = F c ((n : X.B.I.Ginf)⁻¹ * y)`. Introduce `n c y`.

Use `set κ := a⁻¹ * (lift n).2 * a with hκ`. Establish `hκK : κ ∈ X.K2` using `hlK n`. Establish `e1 : (((n : X.B.I.Ginf)⁻¹ * y, a) : X.B.I.GA) = (lift n)⁻¹ * (y, a) * (1, κ)`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `[hl1 n]`.

Simplify using `only [Prod.snd_mul, Prod.snd_inv, hκ]`. Use `group`. Establish `hn : conj (X.chi2 κ) * X.chi2 κ = 1`. Rewrite using `[mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hK.2.2.2.2 κ hκK]`. Simplify using the standard rewrite rules.

Simplify using `only [F]`. Rewrite using `[e1, ph_right_K X u hK hWD T _ κ hκK, hinv T _ ((Srat X u).inv_mem (hlS n)), show (ColCl.pt cs cs' c)⁻¹ * ((lift n)⁻¹ * (y, a) * (1, κ)) = ((ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a)) * (1, κ) by group, ph_right_K X u' hK hWD' T' _ κ hκK, hPh'rel (lift n * ColCl.pt cs cs' c) (Co …`. Establish `e2 : (lift n * ColCl.pt cs cs' c)⁻¹ * ((y, a) : X.B.I.GA) = (ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a)` using `by group`. Rewrite using `[e2]`. Take the linear combination `(-(conj (Ph X u hK T (y, a)) * Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a)))) * hn`.

Set `J` to `{t : GTerm X u u' F0 F0' what₂ rows' // TermOn cs cs' t ρ ρ'}`. Establish `hptG : ∀ t : J, t.1.pt ∈ GamCol cs cs' ρ ρ'` using `fun t => ⟨ratLink_mem X t.1.rep.2.1, t.2.2.2⟩`. Set `r : J → ColCl cs cs' ρ ρ'` to `fun t => Quotient.mk _ ⟨t.1.pt, hptG t⟩`. Establish `hr : ∀ t : J, (t.1.pt)⁻¹ * ColCl.pt cs cs' (r t) ∈ Srat X u'` using `fun t => rel_out cs cs' ⟨t.1.pt, hptG t⟩`. Establish `hcov' : ∀ c, ∃ j n, act n (r j) = c`.

Introduce `c`. Take `⟨t, ht, n, hn⟩` from `hcov c`. Use `⟨⟨t, ht⟩, n, ?_⟩` and prove the remaining obligations. Use `conv_rhs => rw [← Quotient.out_eq c]`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `show (lift n * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ColCl.pt cs cs' c ∈ Srat X u'`. Establish `e : (lift n * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ColCl.pt cs cs' c = ((t.pt)⁻¹ * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ((lift n * t.pt)⁻¹ * ColCl.pt cs cs' c)` using `by group`. Rewrite using `[e]`. Conclude with `(Srat X u').mul_mem ((Srat X u').inv_mem (hr ⟨t, ht⟩)) hn`. Establish `hrel_act : ∀ (n : N) (j j' : J), act n (r j) = r j' → (lift n * j.1.pt)⁻¹ * j'.1.pt ∈ Srat X u'`.

Introduce `n j j' h`. Establish `h2 : (colRel cs cs' ρ ρ') ⟨lift n * ColCl.pt cs cs' (r j), hmemG n (Quotient.out (r j))⟩ (Quotient.out (r j'))`. Use `Quotient.exact (h.trans (Quotient.out_eq (r j')).symm)` as an intermediate fact. Conclude with `this`. Establish `h3 : (lift n * ColCl.pt cs cs' (r j))⁻¹ * ColCl.pt cs cs' (r j') ∈ Srat X u'` using `h2`.

Establish `e : (lift n * j.1.pt)⁻¹ * j'.1.pt = ((j.1.pt)⁻¹ * ColCl.pt cs cs' (r j)) * ((lift n * ColCl.pt cs cs' (r j))⁻¹ * ColCl.pt cs cs' (r j')) * ((j'.1.pt)⁻¹ * ColCl.pt cs cs' (r j'))⁻¹` using `by group`. Rewrite using `[e]`. Conclude with `(Srat X u').mul_mem ((Srat X u').mul_mem (hr j) h3) ((Srat X u').inv_mem (hr j'))`. Establish `huniq' : ∀ j j' n, act n (r j) = r j' → j = j'`. Introduce `j j' n h`.

Conclude with `Subtype.ext (huniq j.1 j'.1 n j.2 j'.2 (hrel_act n j j' h))`. Establish `hfund : ∀ t : J, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t.1) (FundOf t.1)`. Introduce `t`. Establish `h` using `hFE t.1`. Unfold `FundOf`.

Rewrite using `[dif_pos h]`. Conclude with `h.choose_spec`. Establish `hstabJ : ∀ (t : J) (n : N), act n (r t) = r t ↔ (n : X.B.I.Ginf) ∈ ROinf t.1`. Introduce `t n`. Rewrite using `[hstab t.1 t.2]`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `⟨n, rfl, hrel_act n t t h⟩`. Introduce and unpack `⟨n', hn', h⟩`. Establish `hnn : n' = n` using `Subtype.ext hn'`.

Substitute `hnn` using the available equality. Apply `Quotient.sound` to reduce the goal to its premises. Use `show (lift n' * ColCl.pt cs cs' (r t))⁻¹ * t.1.pt ∈ Srat X u'`. Establish `e : (lift n' * ColCl.pt cs cs' (r t))⁻¹ * t.1.pt = ((t.1.pt)⁻¹ * ColCl.pt cs cs' (r t))⁻¹ * ((lift n' * t.1.pt)⁻¹ * t.1.pt)` using `by group`. Rewrite using `[e]`.

Conclude with `(Srat X u').mul_mem ((Srat X u').inv_mem (hr t)) h`. Use `hNc` as an intermediate fact. Use `hCc` as an intermediate fact. Establish `hΩ'` using `hΩ ρ`. Establish `hNmem : ∀ s, s ∈ NOcol F0 cs ρ ↔ s ∈ N` using `by intro s; rw [← hNset]; rfl`.

Establish `hint : ∫⁻ y in Ωs ρ, ∑' c, ‖F c y‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤`. Use `lt_of_le_of_lt (le_of_eq ?_) hbound` and prove the remaining obligations. Use `lintegral_congr fun y => ?_` and prove the remaining obligations. Simplify using `only [F, enorm_mul, RCLike.enorm_conj]`. Rewrite using `[ENNReal.tsum_mul_left]`.

Take `⟨hI, hE⟩` from `orbit_unfold (Formalism.L2.SG.ProjRows.muInf X.B.I) N act h1 hmul F hFm hFeq (Ωs ρ) hΩ'.1 (fun x => by`. Take `⟨s, hs, hsx⟩` from `hΩ'.2.1 x`. Conclude with `⟨⟨s, (hNmem s).1 hs⟩, hsx⟩)`. Use the proof step `(fun x hx n hnx => Subtype.ext (hΩ'.2.2 x hx n ((hNmem n).2 n.2) hnx))`. Use `r hcov' huniq' (fun t => FundOf t.1) (fun t => (hfund t).1)`.

Use the proof step `(fun t x => by`. Take `⟨s, hs, hsx⟩` from `(hfund t).2.1 x`. Establish `hsN : s ∈ N`. Rewrite `hs` using `[hstab t.1 t.2]`. Take `⟨n, rfl, -⟩` from `hs`.

Conclude with `n.2`. Conclude with `⟨⟨s, hsN⟩, (hstabJ t ⟨s, hsN⟩).2 hs, hsx⟩)`. Use the proof step `(fun t x hx n hn hnx => Subtype.ext ((hfund t).2.2 x hx n ((hstabJ t n).1 hn) hnx))`. Use `hint`. Establish `hL : (fun y => conj (Ph X u hK T (y, aC cs ρ)) * ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))) = fun y => ∑' c, F c y`.

Use function extensionality and compare the values at `y`. Rewrite using `[← tsum_mul_left]`. Rewrite using `[hL]`. Use `⟨hI, ?_⟩` and prove the remaining obligations. Rewrite using `[hE]`.

Establish `hterm : ∀ t : J, ∫ y in FundOf t.1, F (r t) y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) = ∫ x in FundOf t.1, Fterm cs hK T T' t.1 ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)`. Introduce `t`. Use `integral_congr_ae (ae_of_all _ fun x => ?_)` and prove the remaining obligations. Simplify using `only [F, Fterm]`. Rewrite using `[hPh'rel t.1.pt (ColCl.pt cs cs' (r t)) (hr t)]`.

Rewrite using `[tsum_congr hterm]`. Establish `hsub` using `tsum_subtype {t : GTerm X u u' F0 F0' what₂ rows' | TermOn cs cs' t ρ ρ'} (fun t => ∫ x in FundOf t, Fterm cs hK T T' t ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I))`. Use `hsub.trans (tsum_congr fun t => ?_)` and prove the remaining obligations. Simplify using `only [Set.indicator_apply, Set.mem_ofPred_eq]`.
-/
theorem orbitUnfold_of (hK : X.LevelSubgroupCharacter) (hWD : PhWellDef X u hK) (hWD' : PhWellDef X u' hK)
    (hFE : FundExists X u u' F0 F0' what₂ rows')
    (hinv : ∀ (T : Cu X u hK), ∀ s ∈ Srat X u, ∀ y, Ph X u hK T (s * y) = Ph X u hK T y)
    (hinv' : ∀ (T' : Cu X u' hK), ∀ s ∈ Srat X u', ∀ y, Ph X u' hK T' (s * y) = Ph X u' hK T' y)
    (hm : ∀ (T : Cu X u hK), Measurable (Ph X u hK T)) (hm' : ∀ (T' : Cu X u' hK), Measurable (Ph X u' hK T'))
    (hOA : OrbitAlg F0 F0' cs cs') : OrbitUnfold F0 F0' cs cs' hK := by
  intro Ωs hΩ T T' ρ ρ' hbound
  obtain ⟨N, lift, hNset, hNc, hCc, hl1, hlone, hlmul, hlS, hlK, hcov, huniq, hstab⟩ := hOA ρ ρ'
  set a := aC cs ρ with ha
  have hmemG : ∀ (n : N) (γ : GamCol cs cs' ρ ρ'), lift n * (γ : X.B.I.GA) ∈ GamCol cs cs' ρ ρ' := by
    intro n γ
    refine ⟨(Formalism.MainNotions.LeviCoordinates.rr_GF X.B.I).mul_mem (Subgroup.mem_inf.1 (hlS n)).1 γ.2.1, ?_⟩
    have e : kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) (lift n * (γ : X.B.I.GA)) =
        (a⁻¹ * (lift n).2 * a) * kOf X u u' (cs.h ρ : X.B.I.Gf) (cs'.h ρ' : X.B.I.Gf) (γ : X.B.I.GA) := by
      simp only [kOf, Prod.snd_mul, ha, aC]; group
    rw [e]
    exact hK.2.1 _ (hlK n) _ γ.2.2
  let act : N → ColCl cs cs' ρ ρ' → ColCl cs cs' ρ ρ' := fun n c =>
    Quotient.mk _ ⟨lift n * ColCl.pt cs cs' c, hmemG n (Quotient.out c)⟩
  have hact_pt : ∀ n c, (lift n * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' (act n c) ∈ Srat X u' :=
    fun n c => rel_out cs cs' ⟨lift n * ColCl.pt cs cs' c, hmemG n (Quotient.out c)⟩
  have h1 : ∀ c, act 1 c = c := by
    intro c
    conv_rhs => rw [← Quotient.out_eq c]
    apply Quotient.sound
    show (lift 1 * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' c ∈ Srat X u'
    rw [hlone, one_mul, inv_mul_cancel]
    exact (Srat X u').one_mem
  have hmul : ∀ n m c, act (n * m) c = act n (act m c) := by
    intro n m c
    apply Quotient.sound
    show (lift (n * m) * ColCl.pt cs cs' c)⁻¹ * (lift n * ColCl.pt cs cs' (act m c)) ∈ Srat X u'
    have e : (lift (n * m) * ColCl.pt cs cs' c)⁻¹ * (lift n * ColCl.pt cs cs' (act m c)) =
        (lift m * ColCl.pt cs cs' c)⁻¹ * ColCl.pt cs cs' (act m c) := by
      rw [hlmul]; group
    rw [e]
    exact hact_pt m c
  let F : ColCl cs cs' ρ ρ' → X.B.I.Ginf → ℂ := fun c y =>
    conj (Ph X u hK T (y, a)) * Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, a))
  have hFm : ∀ c, Measurable (F c) := by
    intro c
    refine (Complex.continuous_conj.measurable.comp ((hm T).comp measurable_prodMk_right)).mul ?_
    exact (hm' T').comp ((measurable_const_mul _).comp measurable_prodMk_right)
  have hPh'rel : ∀ (γ δ : X.B.I.GA), γ⁻¹ * δ ∈ Srat X u' → ∀ x,
      Ph X u' hK T' (δ⁻¹ * x) = Ph X u' hK T' (γ⁻¹ * x) := by
    intro γ δ h x
    have e : δ⁻¹ * x = (γ⁻¹ * δ)⁻¹ * (γ⁻¹ * x) := by group
    rw [e, hinv' T' _ ((Srat X u').inv_mem h)]
  have hFeq : ∀ (n : N) c y, F (act n c) y = F c ((n : X.B.I.Ginf)⁻¹ * y) := by
    intro n c y
    set κ := a⁻¹ * (lift n).2 * a with hκ
    have hκK : κ ∈ X.K2 := hlK n
    have e1 : (((n : X.B.I.Ginf)⁻¹ * y, a) : X.B.I.GA) = (lift n)⁻¹ * (y, a) * (1, κ) := by
      refine Prod.ext ?_ ?_
      · simp [hl1 n]
      · simp only [Prod.snd_mul, Prod.snd_inv, hκ]; group
    have hn : conj (X.chi2 κ) * X.chi2 κ = 1 := by
      rw [mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq, hK.2.2.2.2 κ hκK]; simp
    simp only [F]
    rw [e1, ph_right_K X u hK hWD T _ κ hκK, hinv T _ ((Srat X u).inv_mem (hlS n)),
      show (ColCl.pt cs cs' c)⁻¹ * ((lift n)⁻¹ * (y, a) * (1, κ)) =
        ((ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a)) * (1, κ) by group,
      ph_right_K X u' hK hWD' T' _ κ hκK,
      hPh'rel (lift n * ColCl.pt cs cs' c) (ColCl.pt cs cs' (act n c)) (hact_pt n c), map_mul]
    have e2 : (lift n * ColCl.pt cs cs' c)⁻¹ * ((y, a) : X.B.I.GA) =
        (ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a) := by group
    rw [e2]
    linear_combination (-(conj (Ph X u hK T (y, a)) * Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (lift n)⁻¹ * (y, a)))) * hn

  let J := {t : GTerm X u u' F0 F0' what₂ rows' // TermOn cs cs' t ρ ρ'}
  have hptG : ∀ t : J, t.1.pt ∈ GamCol cs cs' ρ ρ' :=
    fun t => ⟨ratLink_mem X t.1.rep.2.1, t.2.2.2⟩
  let r : J → ColCl cs cs' ρ ρ' := fun t => Quotient.mk _ ⟨t.1.pt, hptG t⟩
  have hr : ∀ t : J, (t.1.pt)⁻¹ * ColCl.pt cs cs' (r t) ∈ Srat X u' := fun t => rel_out cs cs' ⟨t.1.pt, hptG t⟩
  have hcov' : ∀ c, ∃ j n, act n (r j) = c := by
    intro c
    obtain ⟨t, ht, n, hn⟩ := hcov c
    refine ⟨⟨t, ht⟩, n, ?_⟩
    conv_rhs => rw [← Quotient.out_eq c]
    apply Quotient.sound
    show (lift n * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ColCl.pt cs cs' c ∈ Srat X u'
    have e : (lift n * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ColCl.pt cs cs' c =
        ((t.pt)⁻¹ * ColCl.pt cs cs' (r ⟨t, ht⟩))⁻¹ * ((lift n * t.pt)⁻¹ * ColCl.pt cs cs' c) := by group
    rw [e]
    exact (Srat X u').mul_mem ((Srat X u').inv_mem (hr ⟨t, ht⟩)) hn
  have hrel_act : ∀ (n : N) (j j' : J), act n (r j) = r j' → (lift n * j.1.pt)⁻¹ * j'.1.pt ∈ Srat X u' := by
    intro n j j' h
    have h2 : (colRel cs cs' ρ ρ') ⟨lift n * ColCl.pt cs cs' (r j), hmemG n (Quotient.out (r j))⟩
        (Quotient.out (r j')) := by
      have := Quotient.exact (h.trans (Quotient.out_eq (r j')).symm)
      exact this
    have h3 : (lift n * ColCl.pt cs cs' (r j))⁻¹ * ColCl.pt cs cs' (r j') ∈ Srat X u' := h2
    have e : (lift n * j.1.pt)⁻¹ * j'.1.pt =
        ((j.1.pt)⁻¹ * ColCl.pt cs cs' (r j)) * ((lift n * ColCl.pt cs cs' (r j))⁻¹ * ColCl.pt cs cs' (r j')) *
          ((j'.1.pt)⁻¹ * ColCl.pt cs cs' (r j'))⁻¹ := by group
    rw [e]
    exact (Srat X u').mul_mem ((Srat X u').mul_mem (hr j) h3) ((Srat X u').inv_mem (hr j'))
  have huniq' : ∀ j j' n, act n (r j) = r j' → j = j' := by
    intro j j' n h
    exact Subtype.ext (huniq j.1 j'.1 n j.2 j'.2 (hrel_act n j j' h))
  have hfund : ∀ t : J, Formalism.L2.SG.HidaSetting.IsSFund X.B.I (ROinf t.1) (FundOf t.1) := by
    intro t
    have h := hFE t.1
    unfold FundOf
    rw [dif_pos h]
    exact h.choose_spec
  have hstabJ : ∀ (t : J) (n : N), act n (r t) = r t ↔ (n : X.B.I.Ginf) ∈ ROinf t.1 := by
    intro t n
    rw [hstab t.1 t.2]
    constructor
    · intro h
      exact ⟨n, rfl, hrel_act n t t h⟩
    · rintro ⟨n', hn', h⟩
      have hnn : n' = n := Subtype.ext hn'
      subst hnn
      apply Quotient.sound
      show (lift n' * ColCl.pt cs cs' (r t))⁻¹ * t.1.pt ∈ Srat X u'
      have e : (lift n' * ColCl.pt cs cs' (r t))⁻¹ * t.1.pt =
          ((t.1.pt)⁻¹ * ColCl.pt cs cs' (r t))⁻¹ * ((lift n' * t.1.pt)⁻¹ * t.1.pt) := by group
      rw [e]
      exact (Srat X u').mul_mem ((Srat X u').inv_mem (hr t)) h
  have := hNc
  have := hCc
  have hΩ' := hΩ ρ
  have hNmem : ∀ s, s ∈ NOcol F0 cs ρ ↔ s ∈ N := by intro s; rw [← hNset]; rfl
  have hint : ∫⁻ y in Ωs ρ, ∑' c, ‖F c y‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    refine lt_of_le_of_lt (le_of_eq ?_) hbound
    refine lintegral_congr fun y => ?_
    simp only [F, enorm_mul, RCLike.enorm_conj]
    rw [ENNReal.tsum_mul_left]
  obtain ⟨hI, hE⟩ := orbit_unfold (Formalism.L2.SG.ProjRows.muInf X.B.I) N act h1 hmul F hFm hFeq (Ωs ρ) hΩ'.1
    (fun x => by
      obtain ⟨s, hs, hsx⟩ := hΩ'.2.1 x
      exact ⟨⟨s, (hNmem s).1 hs⟩, hsx⟩)
    (fun x hx n hnx => Subtype.ext (hΩ'.2.2 x hx n ((hNmem n).2 n.2) hnx))
    r hcov' huniq' (fun t => FundOf t.1) (fun t => (hfund t).1)
    (fun t x => by
      obtain ⟨s, hs, hsx⟩ := (hfund t).2.1 x
      have hsN : s ∈ N := by
        rw [hstab t.1 t.2] at hs
        obtain ⟨n, rfl, -⟩ := hs
        exact n.2
      exact ⟨⟨s, hsN⟩, (hstabJ t ⟨s, hsN⟩).2 hs, hsx⟩)
    (fun t x hx n hn hnx => Subtype.ext ((hfund t).2.2 x hx n ((hstabJ t n).1 hn) hnx))
    hint
  have hL : (fun y => conj (Ph X u hK T (y, aC cs ρ)) *
      ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))) = fun y => ∑' c, F c y := by
    funext y
    rw [← tsum_mul_left]
  rw [hL]
  refine ⟨hI, ?_⟩
  rw [hE]
  have hterm : ∀ t : J, ∫ y in FundOf t.1, F (r t) y ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) =
      ∫ x in FundOf t.1, Fterm cs hK T T' t.1 ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    intro t
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    simp only [F, Fterm]
    rw [hPh'rel t.1.pt (ColCl.pt cs cs' (r t)) (hr t)]
  rw [tsum_congr hterm]
  have hsub := tsum_subtype {t : GTerm X u u' F0 F0' what₂ rows' | TermOn cs cs' t ρ ρ'}
    (fun t => ∫ x in FundOf t, Fterm cs hK T T' t ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I))
  refine hsub.trans (tsum_congr fun t => ?_)
  simp only [Set.indicator_apply, Set.mem_ofPred_eq]

end OrbitPf

section Asm

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut

variable {D : D7} {X : Formalism.L2.SG.HidaSetting.HidaSetting D} {u u' : D.what₂.Word}
  {F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)} {F0' : FlagG (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)}
  {what₂ rows' : Finset (Submodule (𝓞 D.host.E) (VS D).V)}
  (TR : TypedRed X) (cs : ColSys X u what₂) (cs' : ColSys X u' rows') (FdN FdN' : Set X.B.I.Ginf)

/- English proof (translation)
Establish `hs` using `(summable_blk_of_abs TR cs cs' FdN FdN' hA ρ ρ').hasSum`. Establish `h1` using `hs.mapL (ContinuousLinearMap.apply ℂ (X.Vpi u) (sharp hK cs' T' ρ'))`. Establish `h2` using `h1.mapL (innerSL ℂ (sharp hK cs T ρ))`. Establish `h3` using `h2.map (starRingEnd ℂ) Complex.continuous_conj`. Establish `e : ∀ v : X.Vpi u, inner ℂ v (sharp hK cs T ρ) = starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ) v)`.

Introduce `v`. Rewrite using `[innerSL_apply_apply, inner_conj_symm]`. Establish `h3' : HasSum (fun t : GTerm X u u' F0 F0' what₂ rows' => starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ) (blk cs cs' FdN FdN' t ρ ρ' (sharp hK cs' T' ρ')))) (starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ) ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' …` using `h3`. Rewrite using `[e, ← h3'.tsum_eq, ← tsum_mul_left]`. Use `congr 1`.

Use function extensionality and compare the values at `t`. Rewrite using `[← e]`. Distinguish the cases in `ht : TermOn cs cs' t ρ ρ'`. Rewrite using `[if_pos ht, hTV T T' t ρ ρ' ht]`. Rewrite using `[if_neg ht, mul_zero]`.

Establish `: blk cs cs' FdN FdN' t ρ ρ' = 0` using `by unfold blk; exact if_neg ht`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem inner_tsum_blk (hK : X.LevelSubgroupCharacter) (hA : AbsConvT F0 F0' TR cs cs' FdN FdN')
    (hTV : TermVal F0 F0' cs cs' FdN FdN' hK) (T : Cu X u hK) (T' : Cu X u' hK) (ρ : cs.Cl) (ρ' : cs'.Cl) :
    inner ℂ ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' T' ρ'))
        (sharp hK cs T ρ) =
      ((scl FdN FdN' (X := X) (u := u) (u' := u') * X.volK2 : ℝ) : ℂ) *
        ∑' t : GTerm X u u' F0 F0' what₂ rows', (if TermOn cs cs' t ρ ρ' then
          ∫ x in FundOf t, Fterm cs hK T T' t ρ x ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) else 0) := by
  have hs := (summable_blk_of_abs TR cs cs' FdN FdN' hA ρ ρ').hasSum
  have h1 := hs.mapL (ContinuousLinearMap.apply ℂ (X.Vpi u) (sharp hK cs' T' ρ'))
  have h2 := h1.mapL (innerSL ℂ (sharp hK cs T ρ))
  have h3 := h2.map (starRingEnd ℂ) Complex.continuous_conj
  have e : ∀ v : X.Vpi u, inner ℂ v (sharp hK cs T ρ) =
      starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ) v) := by
    intro v; rw [innerSL_apply_apply, inner_conj_symm]
  have h3' : HasSum (fun t : GTerm X u u' F0 F0' what₂ rows' =>
      starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ) (blk cs cs' FdN FdN' t ρ ρ' (sharp hK cs' T' ρ'))))
      (starRingEnd ℂ (innerSL ℂ (sharp hK cs T ρ)
        ((∑' t : GTerm X u u' F0 F0' what₂ rows', blk cs cs' FdN FdN' t ρ ρ') (sharp hK cs' T' ρ')))) := h3
  rw [e, ← h3'.tsum_eq, ← tsum_mul_left]
  congr 1
  funext t
  rw [← e]
  by_cases ht : TermOn cs cs' t ρ ρ'
  · rw [if_pos ht, hTV T T' t ρ ρ' ht]
  · rw [if_neg ht, mul_zero]
    have : blk cs cs' FdN FdN' t ρ ρ' = 0 := by unfold blk; exact if_neg ht
    rw [this]; simp

/- English proof (translation)
Introduce `Ωs hΩ T T' ρ`. Establish `hPs : ∀ y, Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u) = ∑ ρ', ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))` using `fun y => (hSR T' ρ y).1`. Establish `hfin : ∀ ρ' : cs'.Cl, ∫⁻ y in Ωs ρ, ‖Ph X u hK T (y, aC cs ρ)‖ₑ * ∑' c : ColCl cs cs' ρ ρ', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤`. Introduce `ρ'`. Use `lt_of_le_of_lt (lintegral_mono fun y => ?_) (hSA Ωs hΩ T T' ρ)` and prove the remaining obligations.

Rewrite using `[(hSR T' ρ y).2]`. Conclude with `mul_le_mul_of_nonneg_left (Finset.single_le_sum (f := fun ρ'' => ∑' c : ColCl cs cs' ρ ρ'', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ) (fun _ _ => zero_le) (Finset.mem_univ ρ')) zero_le`. Establish `hOU'` using `fun ρ' => hOU Ωs hΩ T T' ρ ρ' (hfin ρ')`. Establish `hL : (∫ y in Ωs ρ, conj (Ph X u hK T (y, (cs.h ρ : X.B.I.Gf) * X.xu u)) * Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)) = ∑ ρ', ∫ y in Ωs ρ, conj (Ph X u hK T (y, aC cs ρ)) * ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs …`. Rewrite using `[← integral_finset_sum _ (fun ρ' _ => (hOU' ρ').1)]`.

Use `integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)` and prove the remaining obligations. Apply the tactic sequence `try dsimp only`. Rewrite using `[hPs y, Finset.mul_sum]`. Both sides reduce to the same expression. Rewrite using `[hL, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun ρ' _ => ?_` and prove the remaining obligations. Rewrite using `[inner_tsum_blk TR cs cs' FdN FdN' hK hA hTV T T' ρ ρ', ← (hOU' ρ').2, Complex.ofReal_mul]`.
-/
theorem regroup_of (hK : X.LevelSubgroupCharacter) (Dt' : Set X.B.I.GA) (hA : AbsConvT F0 F0' TR cs cs' FdN FdN')
    (hSR : SupportReindex cs cs' hK Dt') (hSA : SlabAbs F0 cs hK Dt' (u' := u')) (hOU : OrbitUnfold F0 F0' cs cs' hK)
    (hTV : TermVal F0 F0' cs cs' FdN FdN' hK) :
    Regroup F0 F0' cs cs' FdN FdN' hK Dt' := by
  intro Ωs hΩ T T' ρ
  have hPs : ∀ y, Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u) =
      ∑ ρ', ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ)) :=
    fun y => (hSR T' ρ y).1
  have hfin : ∀ ρ' : cs'.Cl, ∫⁻ y in Ωs ρ, ‖Ph X u hK T (y, aC cs ρ)‖ₑ *
        ∑' c : ColCl cs cs' ρ ρ', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ
      ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) < ⊤ := by
    intro ρ'
    refine lt_of_le_of_lt (lintegral_mono fun y => ?_) (hSA Ωs hΩ T T' ρ)
    rw [(hSR T' ρ y).2]
    exact mul_le_mul_of_nonneg_left (Finset.single_le_sum
      (f := fun ρ'' => ∑' c : ColCl cs cs' ρ ρ'', ‖Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))‖ₑ)
      (fun _ _ => zero_le) (Finset.mem_univ ρ')) zero_le
  have hOU' := fun ρ' => hOU Ωs hΩ T T' ρ ρ' (hfin ρ')
  have hL : (∫ y in Ωs ρ, conj (Ph X u hK T (y, (cs.h ρ : X.B.I.Gf) * X.xu u)) *
          Pser X u' hK Dt' T' (y, (cs.h ρ : X.B.I.Gf) * X.xu u) ∂(Formalism.L2.SG.ProjRows.muInf X.B.I)) =
      ∑ ρ', ∫ y in Ωs ρ, conj (Ph X u hK T (y, aC cs ρ)) *
          ∑' c : ColCl cs cs' ρ ρ', Ph X u' hK T' ((ColCl.pt cs cs' c)⁻¹ * (y, aC cs ρ))
            ∂(Formalism.L2.SG.ProjRows.muInf X.B.I) := by
    rw [← integral_finset_sum _ (fun ρ' _ => (hOU' ρ').1)]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    try dsimp only
    rw [hPs y, Finset.mul_sum]
    rfl
  rw [hL, Finset.mul_sum]
  refine Finset.sum_congr rfl fun ρ' _ => ?_
  rw [inner_tsum_blk TR cs cs' FdN FdN' hK hA hTV T T' ρ ρ', ← (hOU' ρ').2, Complex.ofReal_mul]

end Asm

section Closed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

open Formalism.L2.SG.PoincareInHH.PoincareSetting Formalism.L2.SG.TermOp.KExpCut Formalism.L2.SG.Full

def Hyps {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word) : Prop :=
  X.LevelSubgroupNormalized ∧
    Formalism.L2.SG.WuDecay.FoldOK X u Y.hK ∧ Formalism.L2.SG.WuDecay.FoldOK X u' Y.hK ∧
    InHH X u Y.hK ∧ InHH X u' Y.hK ∧
    FundExists X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') ∧
    OOIntAll X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') ∧
    OOFundIndep X u u' (X.Fu u) (X.Fu u') (Y.what₂ u) (Y.what₂ u') ∧
    AmpWellDef (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') ∧
    AbsConvT (X.Fu u) (X.Fu u') Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u')

def SupportReindexC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → SupportReindex (Y.cs u) (Y.cs u') Y.hK (Y.Dt u')

def SlabAbsC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → SlabAbs (X.Fu u) (Y.cs u) Y.hK (Y.Dt u') (u' := u')

def OrbitUnfoldC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → OrbitUnfold (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') Y.hK

def TermValC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → TermVal (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK

/- English proof (translation)
Unfold `Formalism.L2.SG.Pf.Slab.RegroupC`. Introduce `D X Y u u' hL hF hF' hI hI' hFE hOI hOF hAW hA`. Establish `hH : Hyps X Y u u'` using `⟨hL, hF, hF', hI, hI', hFE, hOI, hOF, hAW, hA⟩`. Conclude with `regroup_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u') hA (h1 D X Y u u' hH) (h2 D X Y u u' hH) (h3 D X Y u u' hH) (h4 D X Y u u' hH)`.
-/
theorem regroupC_of (h1 : SupportReindexC) (h2 : SlabAbsC) (h3 : OrbitUnfoldC) (h4 : TermValC) :
    Formalism.L2.SG.Pf.Slab.RegroupC := by
  unfold Formalism.L2.SG.Pf.Slab.RegroupC
  intro D X Y u u' hL hF hF' hI hI' hFE hOI hOF hAW hA
  have hH : Hyps X Y u u' := ⟨hL, hF, hF', hI, hI', hFE, hOI, hOF, hAW, hA⟩
  exact regroup_of Y.TR (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (Y.Dt u') hA (h1 D X Y u u' hH)
    (h2 D X Y u u' hH) (h3 D X Y u u' hH) (h4 D X Y u u' hH)

def PhWellDefC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u : D.what₂.Word), X.LevelSubgroupNormalized → PhWellDef X u Y.hK

/- English proof (translation)
Unfold `TermValC`. Introduce `D X Y u u' hH`. Take `⟨hL, -, -, -, -, -, hOI, -, -, -⟩` from `hH`. Conclude with `termVal_of (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (h D X Y u hL) (h D X Y u' hL) hOI`.
-/
theorem termValC_of (h : PhWellDefC) : TermValC := by
  unfold TermValC
  intro D X Y u u' hH
  obtain ⟨hL, -, -, -, -, -, hOI, -, -, -⟩ := hH
  exact termVal_of (Y.cs u) (Y.cs u') (Y.FN u) (Y.FN u') Y.hK (h D X Y u hL) (h D X Y u' hL) hOI

/- English proof (translation)
The claim follows from `regroupC_of h1 h2 h3 (termValC_of hW)`.
-/
theorem regroupC_of' (hW : PhWellDefC) (h1 : SupportReindexC) (h2 : SlabAbsC) (h3 : OrbitUnfoldC) :
    Formalism.L2.SG.Pf.Slab.RegroupC := regroupC_of h1 h2 h3 (termValC_of hW)

def ColUniqC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → ColUniq (Y.cs u) (Y.cs u')

def ColCoverC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → ColCover (Y.cs u) (Y.cs u')

/- English proof (translation)
Unfold `SupportReindexC`. Introduce `D X Y u u' hH`. Establish `hH'` using `hH`. Take `⟨-, -, hF', -, hI', -, -, -, -, -⟩` from `hH'`. Take `⟨-, Ω₀, a, hc, -, hT⟩` from `hF'`.

Conclude with `supportReindex_of (Y.cs u) (Y.cs u') Y.hK (Y.Dt u') (Y.reps u') (fun T' => ((hT T').1 Ω₀ hc subset_rfl).2.1) (fun T' => (hI' T' (Y.Dt u') (Y.reps u')).1) (h1 D X Y u u' hH) (h2 D X Y u u' hH)`.
-/
theorem supportReindexC_of (h1 : ColUniqC) (h2 : ColCoverC) : SupportReindexC := by
  unfold SupportReindexC
  intro D X Y u u' hH
  have hH' := hH
  obtain ⟨-, -, hF', -, hI', -, -, -, -, -⟩ := hH'
  obtain ⟨-, Ω₀, a, hc, -, hT⟩ := hF'
  exact supportReindex_of (Y.cs u) (Y.cs u') Y.hK (Y.Dt u') (Y.reps u')
    (fun T' => ((hT T').1 Ω₀ hc subset_rfl).2.1)
    (fun T' => (hI' T' (Y.Dt u') (Y.reps u')).1) (h1 D X Y u u' hH) (h2 D X Y u u' hH)

/- English proof (translation)
The claim follows from `regroupC_of' hW (supportReindexC_of hU hC) h2 h3`.
-/
theorem regroupC_of'' (hW : PhWellDefC) (hU : ColUniqC) (hC : ColCoverC) (h2 : SlabAbsC) (h3 : OrbitUnfoldC) :
    Formalism.L2.SG.Pf.Slab.RegroupC := regroupC_of' hW (supportReindexC_of hU hC) h2 h3

def OrbitAlgC : Prop :=
  ∀ (D : D7) (X : Formalism.L2.SG.HidaSetting.HidaSetting D) (Y : Full X) (u u' : D.what₂.Word),
    Hyps X Y u u' → OrbitAlg (X.Fu u) (X.Fu u') (Y.cs u) (Y.cs u')

/- English proof (translation)
Unfold `OrbitUnfoldC`. Introduce `D X Y u u' hH`. Establish `hH'` using `hH`. Take `⟨hL, hF, hF', -, -, hFE, -, -, -, -⟩` from `hH'`. Take `⟨-, Ω₀, a, hc, -, hT⟩` from `hF`.

Take `⟨-, Ω₀', a', hc', -, hT'⟩` from `hF'`. Conclude with `orbitUnfold_of (Y.cs u) (Y.cs u') Y.hK (hW D X Y u hL) (hW D X Y u' hL) hFE (fun T => ((hT T).1 Ω₀ hc subset_rfl).2.1) (fun T' => ((hT' T').1 Ω₀' hc' subset_rfl).2.1) (fun T => ((hT T).1 Ω₀ hc subset_rfl).1) (fun T' => ((hT' T').1 Ω₀' hc' subset_rfl).1) (hO D X Y u u' hH)`.
-/
theorem orbitUnfoldC_of (hW : PhWellDefC) (hO : OrbitAlgC) : OrbitUnfoldC := by
  unfold OrbitUnfoldC
  intro D X Y u u' hH
  have hH' := hH
  obtain ⟨hL, hF, hF', -, -, hFE, -, -, -, -⟩ := hH'
  obtain ⟨-, Ω₀, a, hc, -, hT⟩ := hF
  obtain ⟨-, Ω₀', a', hc', -, hT'⟩ := hF'
  exact orbitUnfold_of (Y.cs u) (Y.cs u') Y.hK (hW D X Y u hL) (hW D X Y u' hL) hFE
    (fun T => ((hT T).1 Ω₀ hc subset_rfl).2.1) (fun T' => ((hT' T').1 Ω₀' hc' subset_rfl).2.1)
    (fun T => ((hT T).1 Ω₀ hc subset_rfl).1) (fun T' => ((hT' T').1 Ω₀' hc' subset_rfl).1)
    (hO D X Y u u' hH)

/- English proof (translation)
The claim follows from `regroupC_of'' hW hU hC hS (orbitUnfoldC_of hW hO)`.
-/
theorem regrouping_of_closed_lemmas (hW : PhWellDefC) (hU : ColUniqC) (hC : ColCoverC) (hS : SlabAbsC) (hO : OrbitAlgC) :
    Formalism.L2.SG.Pf.Slab.RegroupC := regroupC_of'' hW hU hC hS (orbitUnfoldC_of hW hO)

end Closed

end Formalism.L2.SG.Pf.RegroupPf
