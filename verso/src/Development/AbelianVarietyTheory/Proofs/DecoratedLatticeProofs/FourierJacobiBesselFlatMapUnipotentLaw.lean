import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.ExistsUnitarySupportedAtPlaceOfMulEqIdem
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.PlacesToAdeles
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.SingleMemIdAt
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SplitPlaceLocalGroupElementsJacobiBesselStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.WeilCharacterSplitPlaceExistsContinuousNontrivia
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemFlagUnipotentRadicalOfBesselNormalFrameLocalStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.BesselCharacterLocalElementEqSimpleEntrySumStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum MeasureTheory Matrix ValuativeRel GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.LocMod GlobalTheory.StepData

namespace GlobalTheory.FlatFBUnip

/- English proof (translation)
Use `Subgroup.closure_induction (p := fun g _ => Matrix.GeneralLinearGroup.det g = 1) ?_ ?_ ?_ ?_ hg` and prove the remaining obligations. Introduce `g hg`. Establish `hb : (g.val).BlockTriangular (lev p)` using `fun r s h => by`. Rewrite using `[hg r s h.le, Matrix.one_apply_ne]`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ h`. Use `ext`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, hb.det, Units.val_one]`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `: g.val.toSquareBlock (lev p) a = 1`.

Use extensionality with `⟨i, hi⟩ ⟨j, hj⟩`. Simplify using `only [Matrix.toSquareBlock_def, Matrix.of_apply]`. Rewrite using `[hg i j (by rw [hi, hj])]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne]`. Introduce `e`. Conclude with `h (congrArg Subtype.val e)`. Rewrite using `[this, Matrix.det_one]`.

Conclude with `map_one _`. Introduce `x y _ _ hx hy`. Rewrite using `[map_mul, hx, hy, one_mul]`. Introduce `x _ hx`. Rewrite using `[map_inv, hx, inv_one]`.
-/
theorem det_of_mem_N {k : Type} [Field k] {n : Type} [Fintype n] [DecidableEq n] {c p : ℕ} {g : GL (n ⊕ Fin c) k}
    (hg : g ∈ N k n c p) : Matrix.GeneralLinearGroup.det g = 1 := by
  refine Subgroup.closure_induction (p := fun g _ => Matrix.GeneralLinearGroup.det g = 1) ?_ ?_ ?_ ?_ hg
  · intro g hg
    have hb : (g.val).BlockTriangular (lev p) := fun r s h => by
      rw [hg r s h.le, Matrix.one_apply_ne]
      rintro rfl; exact lt_irrefl _ h
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, hb.det, Units.val_one]
    refine Finset.prod_eq_one fun a _ => ?_
    have : g.val.toSquareBlock (lev p) a = 1 := by
      ext ⟨i, hi⟩ ⟨j, hj⟩
      simp only [Matrix.toSquareBlock_def, Matrix.of_apply]
      rw [hg i j (by rw [hi, hj])]
      by_cases h : i = j
      · subst h; simp
      · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne]; intro e; exact h (congrArg Subtype.val e)
    rw [this, Matrix.det_one]
  · exact map_one _
  · intro x y _ _ hx hy; rw [map_mul, hx, hy, one_mul]
  · intro x _ hx; rw [map_inv, hx, inv_one]

end GlobalTheory.FlatFBUnip

namespace GlobalTheory.FlatFBUnip

/- English proof (translation)
Introduce `D hFL hOm k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ hC hB Tm hTm u hu Φ Φ' hΦ`. Take `⟨v, ε, hv, hε⟩` from `p.split.2.2`. Establish `hF` using `(hFL ψ (· = v)).2 σ J B st`. Take `⟨g, hg, -⟩` from `((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B.V (n ⊕ Fin c) FV).1 (embA n u)`. Establish `hgN : g ∈ flagN B.d` using `GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal D k p σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg`.

Establish `hgP : g ∈ GlobalTheory.FinPl.grpAt B.V (· = v)`. Establish `hS` using `hg.1`. Take `rfl` from `GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hv`. Rewrite `hS` using `[SuppAt, hε]`. Simplify using `only [← GlobalTheory.FinPl.Model.mem_idAt_iff] at hS`.

Rewrite using `[GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]`. Introduce `i j`. Establish `h1` using `hS i j`. Rewrite `h1` using `[Matrix.sub_apply, ← Ideal.Quotient.eq]`. Establish `: Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D (· = v)) ((1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D)) i j) = (1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D (· = v))) i j`.

Apply the tactic sequence `by_cases h : i = j <;> simp [Matrix.one_apply, h]`. Rewrite `h1` using `[this]`. Conclude with `h1`. Establish `hdet : Matrix.GeneralLinearGroup.det (embA n u) = 1` using `det_of_mem_N hu`. Take `⟨-, -, -, -, hcomp⟩` from `GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std`.

Take `⟨μS, hμS⟩` from `hcomp st.χV`. Take `⟨μT, hμT⟩` from `hcomp st.χW`. Establish `h1 : p.IsLoc FW (1 : GA D J.W) 1`. Use `⟨fun i j => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[mt_one]`.

Rewrite using `[mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, FW.βγ]`. Establish `hΦ'' : Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin (c + 1)) k)) : ℂˣ) : ℂ) • om μS⁻¹ 1 (embA n u) Φ.1`. Use function extensionality and compare the values at `t`. Simplify using `only [om, hdet, map_one, Units.val_one, nabs, Real.one_rpow, inv_one, one_mul, one_smul, Pi.smul_apply, Matrix.mul_one, hΦ t]`. Evaluate the numerical expressions.

Establish `hω` using `hOm k p ψ J.W B.V st.χV st.χW st.om st.weil μS μT hμS hμT (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) FW FV Tm hTm 1 1 g (embA n u) h1 hg Φ Φ' hΦ''`. Establish `heq` using `hF.equiv (Tm Φ) (hTm.theta Φ) g hgN hgP 1 (one_mem _)`. Rewrite `heq` using `[map_one, mul_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one]`. Rewrite using `[← hω, heq, GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum D k p ψ ψk hχ σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg]`. Simplify using `only [Module.End.one_apply]`.

Use `congr 1`. Rewrite using `[AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]`. Both sides reduce to the same expression.
-/
theorem unip_law : ∀ (D : D7), GlobalTheory.FinPl.FlatLaws D → OmLoc D → ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [MeasurableSpace k] [BorelSpace k] (p : Place D k) (ψ : AddChar (AF D.host.F) ℂ) (ψk : AddChar k Circle), p.IsChar ψ ψk → ∀ (σ : ℕ) (J : JacLev D (σ + 1)) (B : BesLev D σ) (st : StepFB ψ J B) (s : k), s ≠ 0 → ∀ (n n' : Type) [Fintype n] [DecidableEq n] [Fintype n'] [DecidableEq n'] (c : ℕ) (G₀ : Frame k J.W₀.rank n') (FW : Frame k J.W.rank (n' ⊕ Fin (c + 1))) (FA : Frame k B.A.rank n) (F₀ : Frame k B.V₀.rank (n ⊕ Unit)) (FV : Frame k B.V.rank (n ⊕ Fin c)), p.IsJacFrame J s (-p.xi ^ 2 * p.hz B) G₀ FW → p.IsCoreFrame B (s * p.xi) FA F₀ → p.IsBesFrame B (s * p.xi) FA FV → ∀ Tm, p.IsModel ψ FW FV Tm → ∀ u : GL (Fin c) k, embA n u ∈ N k n c (σ + 1) → ∀ (Φ Φ' : SB (Matrix (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) k)), (∀ t, Φ'.1 t = Φ.1 (((embA n u)⁻¹).val * t)) → flatFB st (Tm Φ') = (ψk (-simpleSum (embA n u)) : ℂ) • flatFB st (Tm Φ) := by
  intro D hFL hOm k _ _ _ _ _ _ p ψ ψk hχ σ J B st s hs n n' _ _ _ _ c G₀ FW FA F₀ FV hJ hC hB Tm hTm u hu Φ Φ' hΦ
  obtain ⟨v, ε, hv, hε⟩ := p.split.2.2
  have hF := (hFL ψ (· = v)).2 σ J B st
  obtain ⟨g, hg, -⟩ := ((GlobalTheory.T.splitPlace_localGroupElements_jacobi_bessel D k p).1 B.V (n ⊕ Fin c) FV).1 (embA n u)
  have hgN : g ∈ flagN B.d := GlobalTheory.T.mem_flagUnipotentRadical_of_besselNormalFrameLocal D k p σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg
  have hgP : g ∈ GlobalTheory.FinPl.grpAt B.V (· = v) := by
    have hS := hg.1
    obtain rfl := GlobalTheory.AdelicU.Supp.isPlaceIdem_iff.1 hv
    rw [SuppAt, hε] at hS
    simp only [← GlobalTheory.FinPl.Model.mem_idAt_iff] at hS
    rw [GlobalTheory.FinPl.grpAt, GlobalTheory.FinPl.congGrp, MonoidHom.mem_ker, Units.ext_iff, ← Matrix.ext_iff]
    intro i j
    have h1 := hS i j
    rw [Matrix.sub_apply, ← Ideal.Quotient.eq] at h1
    have : Ideal.Quotient.mk (GlobalTheory.FinPl.idAt D (· = v)) ((1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D)) i j) =
        (1 : Matrix (Fin B.V.rank) (Fin B.V.rank) (AE D ⧸ GlobalTheory.FinPl.idAt D (· = v))) i j := by
      by_cases h : i = j <;> simp [Matrix.one_apply, h]
    rw [this] at h1
    exact h1
  have hdet : Matrix.GeneralLinearGroup.det (embA n u) = 1 := det_of_mem_N hu
  obtain ⟨-, -, -, -, hcomp⟩ := GlobalTheory.LocChar.weil_char_split D k p ψ st.weil.std
  obtain ⟨μS, hμS⟩ := hcomp st.χV
  obtain ⟨μT, hμT⟩ := hcomp st.χW
  have h1 : p.IsLoc FW (1 : GA D J.W) 1 := by
    refine ⟨fun i j => ?_, ?_⟩
    · simp [mt_one]
    · rw [mt_one, Matrix.map_one _ (map_zero p.π) (map_one p.π), Units.val_one, Matrix.mul_one, FW.βγ]
  have hΦ'' : Φ'.1 = (((μS * μT⁻¹) (Matrix.GeneralLinearGroup.det (1 : GL (n' ⊕ Fin (c + 1)) k)) : ℂˣ) : ℂ) •
      om μS⁻¹ 1 (embA n u) Φ.1 := by
    funext t
    simp only [om, hdet, map_one, Units.val_one, nabs, Real.one_rpow, inv_one, one_mul, one_smul, Pi.smul_apply,
      Matrix.mul_one, hΦ t]
    norm_num
  have hω := hOm k p ψ J.W B.V st.χV st.χW st.om st.weil μS μT hμS hμT (n ⊕ Fin c) (n' ⊕ Fin (c + 1)) FW FV Tm hTm
    1 1 g (embA n u) h1 hg Φ Φ' hΦ''
  have heq := hF.equiv (Tm Φ) (hTm.theta Φ) g hgN hgP 1 (one_mem _)
  rw [map_one, mul_one, Prod.mk_one_one, map_one, Prod.mk_one_one, map_one] at heq
  rw [← hω, heq, GlobalTheory.T.besselCharacter_localElement_eq_simpleEntrySum D k p ψ ψk hχ σ B (s * p.xi) n c FA FV hB g (embA n u) hu hg]
  simp only [Module.End.one_apply]
  congr 1
  rw [AddChar.map_neg_eq_inv, Circle.coe_inv_eq_conj]
  rfl

end GlobalTheory.FlatFBUnip
