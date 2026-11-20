import Mathlib
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.StepUnfold
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.UnitaryAdelicInfFinSplitPeriodsUnimodular
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.ClassFunctionSumIntegral
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ContinuousReGLSymm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InfOfMulFinOf
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.KerFockMovedReal
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FrChInv
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFockFrameChangeLastColumnDefinitePair
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaGridCharactersArchExponentsGapGtRank
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField MeasureTheory GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.StdFrames GlobalTheory.RowClaim GlobalTheory.DefStep
open GlobalTheory.IndefiniteRowSideFullHecke.ClassFunctionSumIntegral (IsOpenCompactLevel)
open scoped ComplexOrder Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField borelKw borelSpaceKw
open GlobalTheory.FockFrameChange GlobalTheory.FockReal

noncomputable section

namespace GlobalTheory.ColKer

open GlobalTheory.Chain.StepVac in

/- English proof (translation)
Take `⟨n, hn, ho⟩` from `hL.xi_fin t`. Establish `h0` using `GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ`. Take `⟨θ, hθ⟩ : ∃ θ, IsInfFam (D` from `D) θ := by`. Take `⟨_, _, hθ, _⟩` from `h0`. Conclude with `hθ`.

Use `hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)` as an intermediate fact. Rewrite `this` using `[add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply]`. Conclude with `this`.
-/
theorem mu_exp {D : D7} {T : Type} {L : LevCh D T} {μ₀ : T} (hL : L.Is μ₀) (t : T) (j : ℕ) (hj : j < D.R.m)
    (τ : D.what₂.Tau) : HasInfExp D (L.mu t (j + 1)) τ (-(D.hc τ).e ⟨j, hj⟩) := by
  obtain ⟨n, hn, ho⟩ := hL.xi_fin t
  have h0 := GlobalTheory.HeckeInfExp.hasInfExp_of_chrEq D _ _ _ (hL.mu0 ⟨j, hj⟩) (hasInfQ_tau (L.C.isMu0 ⟨j, hj⟩).inf) τ
  obtain ⟨θ, hθ⟩ : ∃ θ, IsInfFam (D := D) θ := by
    obtain ⟨_, _, hθ, _⟩ := h0
    exact hθ
  have := hasInfExp_mul h0 (hasInfExp_of_order hθ (hL.xi t) hn ho τ)
  rw [add_zero, Formalism.L2.Host.eExp, Equiv.symm_apply_apply] at this
  exact this

variable {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc}

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Use `show Formalism.UG.bc (θ τ) (infHom V g) = 1`. Rewrite using `[show infHom V g = 1 from hg, map_one]`.
-/
theorem realGL_fin (θ : InfFam D) (V : HSp D) {g : GA D V} (hg : g ∈ GfC V) : GlobalTheory.CoefModel.realGL θ V g = 1 := by
  funext τ
  show Formalism.UG.bc (θ τ) (infHom V g) = 1
  rw [show infHom V g = 1 from hg, map_one]

/- English proof (translation)
Use `conv_rhs => rw [← infOf_mul_finOf V h]`. Rewrite using `[map_mul, realGL_fin θ V (finOf V h).2, mul_one]`.
-/
theorem realGL_infOf (θ : InfFam D) (V : HSp D) (h : GA D V) :
    GlobalTheory.CoefModel.realGL θ V (infOf V h : GA D V) = GlobalTheory.CoefModel.realGL θ V h := by
  conv_rhs => rw [← infOf_mul_finOf V h]
  rw [map_mul, realGL_fin θ V (finOf V h).2, mul_one]

/- English proof (translation)
Simplify using `only [realIn, MonoidHom.pi_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply, Pi.evalMonoidHom_apply, Units.val_mul, Matrix.det_mul, inv_inv]`. Rewrite using `[mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]`.
-/
theorem det_realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (g : GA D (G.V X))
    (τ : D.what₂.Tau) :
    ((realIn θ fr X g τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det =
      ((GlobalTheory.CoefModel.realGL θ (G.V X) g τ : GL (Fin (G.V X).rank) ℂ) : Matrix (Fin (G.V X).rank) (Fin (G.V X).rank) ℂ).det := by
  simp only [realIn, MonoidHom.pi_apply, MonoidHom.comp_apply, MulEquiv.coe_toMonoidHom, MulAut.conj_apply,
    Pi.evalMonoidHom_apply, Units.val_mul, Matrix.det_mul, inv_inv]
  rw [mul_comm, ← mul_assoc, ← Matrix.det_mul, Units.mul_inv, Matrix.det_one, one_mul]

/- English proof (translation)
Simplify using `only [← Matrix.coe_units_inv, ← Units.val_mul]`. Use `congr 1`. Use `group`.
-/
theorem conj_frame {n : ℕ} (O F c : GL (Fin n) ℂ) :
    ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ)) *
      ((F⁻¹ * c * F : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) *
      ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))⁻¹ =
        (O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (c : Matrix (Fin n) (Fin n) ℂ) * (O : Matrix (Fin n) (Fin n) ℂ) := by
  simp only [← Matrix.coe_units_inv, ← Units.val_mul]
  congr 1
  group

/- English proof (translation)
Rewrite using `[← Matrix.transpose_mul, ← Matrix.transpose_mul]`. Use `congr 1`. Simplify using `only [← Matrix.coe_units_inv, ← Units.val_mul]`. Use `congr 1`. Use `group`.
-/
theorem transp_frame {n : ℕ} (O F c : GL (Fin n) ℂ) :
    (((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))⁻¹)ᵀ *
      ((((F⁻¹ * c * F)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ))ᵀ *
      ((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (F : Matrix (Fin n) (Fin n) ℂ))ᵀ =
        (((O : Matrix (Fin n) (Fin n) ℂ)⁻¹ * (c : Matrix (Fin n) (Fin n) ℂ) * (O : Matrix (Fin n) (Fin n) ℂ))⁻¹)ᵀ := by
  rw [← Matrix.transpose_mul, ← Matrix.transpose_mul]
  congr 1
  simp only [← Matrix.coe_units_inv, ← Units.val_mul]
  congr 1
  group

/- English proof (translation)
Unfold `realChar`. Use `Finset.prod_congr rfl fun τ _ => ?_` and prove the remaining obligations. Rewrite using `[det_realIn, det_realIn, ← realGL_infOf W.θ _ h]`. Both sides reduce to the same expression.
-/
theorem realChar_top (W : G.Weil) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (t : T) (j : ℕ)
    (e₁ e₂ : D.what₂.Tau → ℤ) (k : GA D (G.V (.top j))) (h : GA D (G.V (.top (j + 1)))) :
    realChar W (Pair.top t j) e₁ e₂ k (infOf _ h) =
      ∏ τ, ((realIn W.θ fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^ e₂ τ *
        ((realIn W.θ fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ e₁ τ := by
  unfold realChar
  refine Finset.prod_congr rfl fun τ _ => ?_
  rw [det_realIn, det_realIn, ← realGL_infOf W.θ _ h]
  rfl

/- English proof (translation)
Simplify using `[realIn]`.
-/
theorem coe_realIn (θ : InfFam D) (fr : ∀ X : Node, GL (Fin (G.V X).rank) D.host.E) (X : Node) (g : GA D (G.V X))
    (τ : D.what₂.Tau) :
    realIn θ fr X g τ = (frGL fr X τ)⁻¹ * GlobalTheory.CoefModel.realGL θ (G.V X) g τ * frGL fr X τ := by
  simp [realIn]

/- English proof (translation)
Establish `hO : ∀ X, DefNode D.R.m X → ∀ τ, IsUnit (W.onb X τ).det` using `fun X hX τ => by`. Establish `e` using `congrArg Matrix.det (onb_def hL W hX τ)`. Rewrite `e` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_one]`. Conclude with `isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e⟩`. Establish `hn` using `DefPair.nodes (show DefPair D.R.m (Pair.top t j) from hj)`.

Establish `hid : ⇑(opp (Pair.top t j)) = (id : ℂ → ℂ)` using `rfl`. Unfold `GlobalTheory.AvgCol.frCh GlobalTheory.AvgCol.frChInv realSubst`. Rewrite using `[substF_mul, substF_mul]`. Use `congrArg₂ (fun A B => GlobalTheory.CompactHowe.substF A B Q) (funext fun τ => ?_) (funext fun τ => ?_)` and prove the remaining obligations. Rewrite using `[hid, Matrix.map_id, coe_realIn]`.

Establish `eC : compAt W.θ τ (Formalism.L2.Theta.mt (G.pT (Pair.top t j)) (G.toPair (Pair.top t j) k ↑(infOf _ h)).2) = ((GlobalTheory.CoefModel.realGL W.θ _ h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) : Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ)`. Rewrite using `[← realGL_infOf]`. Both sides reduce to the same expression. Rewrite using `[eC]`. Conclude with `(conj_frame (Matrix.nonsingInvUnit _ (hO _ hn.2 τ)) (frGL N.fr _ τ) _).symm`.

Rewrite using `[hid, Matrix.map_id, coe_realIn]`. Conclude with `(transp_frame (Matrix.nonsingInvUnit _ (hO _ hn.1 τ)) (frGL N.fr _ τ) (GlobalTheory.CoefModel.realGL W.θ (G.V (.top j)) k τ)).symm`.
-/
theorem realSubst_top {μ₀ : T} (hL : L.Is μ₀) (W : G.Weil) {U : Set T} (N : Std G U) (t : T) (j : ℕ)
    (hj : j + 1 ≤ D.R.m) (k : GA D (G.V (.top j))) (h : GA D (G.V (.top (j + 1))))
    (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) :
    realSubst W W.onb (Pair.top t j) k (infOf _ h) Q =
      GlobalTheory.AvgCol.frCh W N j (GlobalTheory.CompactHowe.substF
        (fun τ => ((realIn W.θ N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
        (fun τ => (((realIn W.θ N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
          Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
        (GlobalTheory.AvgCol.frChInv W N j Q)) := by
  have hO : ∀ X, DefNode D.R.m X → ∀ τ, IsUnit (W.onb X τ).det := fun X hX τ => by
    have e := congrArg Matrix.det (onb_def hL W hX τ)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_one] at e
    exact isUnit_iff_exists_inv.2 ⟨_, by rw [mul_comm]; exact e⟩
  have hn := DefPair.nodes (show DefPair D.R.m (Pair.top t j) from hj)
  have hid : ⇑(opp (Pair.top t j)) = (id : ℂ → ℂ) := rfl
  unfold GlobalTheory.AvgCol.frCh GlobalTheory.AvgCol.frChInv realSubst
  rw [substF_mul, substF_mul]
  refine congrArg₂ (fun A B => GlobalTheory.CompactHowe.substF A B Q) (funext fun τ => ?_) (funext fun τ => ?_)
  · rw [hid, Matrix.map_id, coe_realIn]
    have eC : compAt W.θ τ (Formalism.L2.Theta.mt (G.pT (Pair.top t j)) (G.toPair (Pair.top t j) k ↑(infOf _ h)).2) =
        ((GlobalTheory.CoefModel.realGL W.θ _ h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
          Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ) := by
      rw [← realGL_infOf]; rfl
    rw [eC]
    exact (conj_frame (Matrix.nonsingInvUnit _ (hO _ hn.2 τ)) (frGL N.fr _ τ) _).symm
  · rw [hid, Matrix.map_id, coe_realIn]
    exact (transp_frame (Matrix.nonsingInvUnit _ (hO _ hn.1 τ)) (frGL N.fr _ τ) (GlobalTheory.CoefModel.realGL W.θ (G.V (.top j)) k τ)).symm

open GlobalTheory.SignedHC in

/- English proof (translation)
Establish `hj' : j + 1 ≤ D.R.m` using `hj`. Establish `r0` using `rank_top G (j := j) (by omega)`. Establish `r1` using `rank_top G (j := j + 1) hj'`. Establish `h0` using `isHC_top D sc.cGap τ (j := j) (by omega) r0`. Establish `h1` using `isHC_top D sc.cGap τ hj' r1`.

Establish `hE` using `h0.1.card_entries.trans h0.2.1`. Establish `hF` using `h1.1.card_entries.trans h1.2.1`. Establish `e0 : entries (Node.par D sc.cGap (.top j) τ) = (num D sc.cGap τ).weightX j` using `entries_plus _`. Establish `e1 : entries (Node.par D sc.cGap (.top (j + 1)) τ) = (num D sc.cGap τ).weightX (j + 1)` using `entries_plus _`. Establish `w0 : ∀ r, ((wt G (.top j) τ).w r : ℚ) = highestWeight _ hE r` using `fun r => wtOf_cast hE h0.2.2 r`.

Establish `w1 : ∀ r, ((wt G (.top (j + 1)) τ).w r : ℚ) = highestWeight _ hF r` using `fun r => wtOf_cast hF h1.2.2 r`. Establish `hb : (G.V (.top (j + 1))).rank = (G.V (.top j)).rank + (D.R.t + 1)`. Rewrite using `[r0, r1]`. Simplify using `only [rankX]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨v1, v2⟩` from `highestWeight_below hb (-((num D sc.cGap τ).e (j + 1) : ℚ)) hE (by rw [e0, e1, GridData.weightX_succ]; rfl) (fun x hx y hy => by rw [e0] at hx; exact weightX_above D sc.cGap τ hj' hx hy) hF`. Establish `ha : 0 < (G.V (.top j)).rank` using `r0 ▸ rankX_pos D j`. Establish `hce : (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩` using `num_e D sc.cGap τ (l := j + 1) (by omega) hj'`. Establish `hS1 : (wt G (.top (j + 1)) τ).detShift = (wt G (.top (j + 1)) τ).w ⟨(G.V (.top (j + 1))).rank - 1, by omega⟩`. Rewrite using `[DomWeight.detShift, dif_pos (by omega)]`.

Establish `hS0 : (wt G (.top j) τ).detShift = (wt G (.top j) τ).w ⟨(G.V (.top j)).rank - 1, by omega⟩`. Rewrite using `[DomWeight.detShift, dif_pos ha]`. Establish `d1 : (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = -((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top j)).rank : ℚ) / 2`. Rewrite using `[hS1, w1, v2 _ (by simp only; omega), hce]`. Use `⟨d1, ?_⟩` and prove the remaining obligations.

Establish `hlt : (G.V (.top j)).rank - 1 < (G.V (.top (j + 1))).rank` using `by omega`. Establish `hν : nuEnd G (.top t j) τ = (wt G (.top (j + 1)) τ).natW ⟨(G.V (.top j)).rank - 1, hlt⟩`. Simplify using `only [nuEnd, dif_pos hlt]`. Establish `hanti : (wt G (.top (j + 1)) τ).detShift ≤ (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩`. Rewrite using `[hS1]; exact (wt G (.top (j + 1)) τ).anti (Fin.mk_le_mk.2 (by omega))`.

Establish `hnat : ((nuEnd G (.top t j) τ : ℕ) : ℤ) = (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ - (wt G (.top (j + 1)) τ).detShift`. Rewrite using `[hν, DomWeight.natW, Int.toNat_of_nonneg (by omega)]`. Establish `hc : (G.V (.top j)).rank - 1 < (G.V (.top j)).rank` using `by omega`. Establish `ew : (((wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ : ℤ) : ℚ) = highestWeight _ hE ⟨(G.V (.top j)).rank - 1, hc⟩ - ((D.R.t + 1 : ℕ) : ℚ) / 2`. Rewrite using `[w1, ← v1]`.

Both sides reduce to the same expression. Establish `hrk : ((G.V (.top (j + 1))).rank : ℚ) = (G.V (.top j)).rank + (D.R.t + 1)`. Rewrite using `[hb]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[Int.cast_sub, hnat, Int.cast_sub, ew, d1, hS0, w0, hrk]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem detShift_top (G : GridData L sc) (t : T) (j : ℕ) (hj : j < D.R.m) (τ : D.what₂.Tau) :
    (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = -((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top j)).rank : ℚ) / 2 ∧
    (((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift : ℤ) : ℚ) =
      -(-((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top (j + 1))).rank : ℚ) / 2) := by
  have hj' : j + 1 ≤ D.R.m := hj
  have r0 := rank_top G (j := j) (by omega)
  have r1 := rank_top G (j := j + 1) hj'
  have h0 := isHC_top D sc.cGap τ (j := j) (by omega) r0
  have h1 := isHC_top D sc.cGap τ hj' r1
  have hE := h0.1.card_entries.trans h0.2.1
  have hF := h1.1.card_entries.trans h1.2.1
  have e0 : entries (Node.par D sc.cGap (.top j) τ) = (num D sc.cGap τ).weightX j := entries_plus _
  have e1 : entries (Node.par D sc.cGap (.top (j + 1)) τ) = (num D sc.cGap τ).weightX (j + 1) := entries_plus _
  have w0 : ∀ r, ((wt G (.top j) τ).w r : ℚ) = highestWeight _ hE r := fun r => wtOf_cast hE h0.2.2 r
  have w1 : ∀ r, ((wt G (.top (j + 1)) τ).w r : ℚ) = highestWeight _ hF r := fun r => wtOf_cast hF h1.2.2 r
  have hb : (G.V (.top (j + 1))).rank = (G.V (.top j)).rank + (D.R.t + 1) := by
    rw [r0, r1]; simp only [rankX]; ring
  obtain ⟨v1, v2⟩ := highestWeight_below hb (-((num D sc.cGap τ).e (j + 1) : ℚ)) hE
    (by rw [e0, e1, GridData.weightX_succ]; rfl)
    (fun x hx y hy => by rw [e0] at hx; exact weightX_above D sc.cGap τ hj' hx hy) hF
  have ha : 0 < (G.V (.top j)).rank := r0 ▸ rankX_pos D j
  have hce : (((num D sc.cGap τ).e (j + 1) : ℤ) : ℚ) = (D.hc τ).e ⟨j, hj⟩ := num_e D sc.cGap τ (l := j + 1) (by omega) hj'
  have hS1 : (wt G (.top (j + 1)) τ).detShift = (wt G (.top (j + 1)) τ).w ⟨(G.V (.top (j + 1))).rank - 1, by omega⟩ := by
    rw [DomWeight.detShift, dif_pos (by omega)]
  have hS0 : (wt G (.top j) τ).detShift = (wt G (.top j) τ).w ⟨(G.V (.top j)).rank - 1, by omega⟩ := by
    rw [DomWeight.detShift, dif_pos ha]
  have d1 : (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = -((D.hc τ).e ⟨j, hj⟩ : ℚ) + ((G.V (.top j)).rank : ℚ) / 2 := by
    rw [hS1, w1, v2 _ (by simp only; omega), hce]
  refine ⟨d1, ?_⟩
  have hlt : (G.V (.top j)).rank - 1 < (G.V (.top (j + 1))).rank := by omega
  have hν : nuEnd G (.top t j) τ = (wt G (.top (j + 1)) τ).natW ⟨(G.V (.top j)).rank - 1, hlt⟩ := by
    simp only [nuEnd, dif_pos hlt]
  have hanti : (wt G (.top (j + 1)) τ).detShift ≤ (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ := by
    rw [hS1]; exact (wt G (.top (j + 1)) τ).anti (Fin.mk_le_mk.2 (by omega))
  have hnat : ((nuEnd G (.top t j) τ : ℕ) : ℤ) =
      (wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ - (wt G (.top (j + 1)) τ).detShift := by
    rw [hν, DomWeight.natW, Int.toNat_of_nonneg (by omega)]
  have hc : (G.V (.top j)).rank - 1 < (G.V (.top j)).rank := by omega
  have ew : (((wt G (.top (j + 1)) τ).w ⟨(G.V (.top j)).rank - 1, hlt⟩ : ℤ) : ℚ) =
      highestWeight _ hE ⟨(G.V (.top j)).rank - 1, hc⟩ - ((D.R.t + 1 : ℕ) : ℚ) / 2 := by
    rw [w1, ← v1]
    rfl
  have hrk : ((G.V (.top (j + 1))).rank : ℚ) = (G.V (.top j)).rank + (D.R.t + 1) := by
    rw [hb]; push_cast; ring
  rw [Int.cast_sub, hnat, Int.cast_sub, ew, d1, hS0, w0, hrk]
  push_cast
  ring

/- English proof (translation)
Introduce `D T L sc G W U S μ₀ hL j hj t d hd Q x k hk h`. Establish `hp : DefPair D.R.m (Pair.top t j)` using `show j + 1 ≤ D.R.m by omega`. Establish `hh : ((finOf _ h : GA D (G.V (.top (j + 1)))) * (infOf _ h : GA D (G.V (.top (j + 1))))) = h`. Rewrite using `[← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2]`. Conclude with `infOf_mul_finOf _ h`.

Establish `hr0 : Even (G.V (.top j)).rank` using `by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j`. Establish `hr1 : Even (G.V (.top (j + 1))).rank` using `by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)`. Establish `hS : G.chrS (.top t j) = L.mu t (j + 1)`. Simplify using `only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]`. Establish `hT : G.chrT (.top t j) = L.mu t (j + 1)`.

Simplify using `only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]`. Use `set a : D.what₂.Tau → ℚ := fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ) with ha_def`. Establish `ha : ∀ τ, HasInfExp D (G.chrS (.top t j)) τ (a τ)` using `fun τ => by rw [hS]; exact mu_exp hL t j hj τ`. Establish `hb : ∀ τ, HasInfExp D (G.chrT (.top t j)) τ (a τ)` using `fun τ => by rw [hT]; exact mu_exp hL t j hj τ`. Establish `he₁ : ∀ τ, (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) = a τ + sgnP (Pair.top t j) * (G.pS (.top t j)).rank / 2` using `fun τ => by`.

Rewrite using `[(detShift_top G t j hj τ).1]`. Simplify using `only [sgnP, one_mul, a]`. Establish `he₂ : ∀ τ, ((((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) : ℤ) : ℚ) = -(a τ + sgnP (Pair.top t j) * (G.pT (.top t j)).rank / 2)` using `fun τ => by`. Rewrite using `[(detShift_top G t j hj τ).2]`. Simplify using `only [sgnP, one_mul, a]`.

Use `show W.ker (.top t j) _ ((x : GA D (G.V (.top j))) * k) h = _`. Use `conv_lhs => rw [← hh]`. Establish `key` using `ker_fock_moved_real (p := Pair.top t j) hL W S t hp d hd a a ha hb _ _ he₁ he₂ k hk (infOf _ h) (infOf _ h).2 Q (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1))))`. Rewrite using `[key, realChar_top W S.N.fr t j, realSubst_top hL W S.N t j hp k h Q]`.
-/
theorem kerA_col_mul_real : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {G : GridData L sc} {W : G.Weil} {U : Set T}
    (S : GridChoice W U) {μ0 : T}, L.Is μ0 → ∀ (j : ℕ), j < D.R.m → ∀ (t : T) (d : FinDatum G t (.top t j)), S.Z.HasVec d →
    ∀ (Q : PolF D (G.V (.top (j + 1))).rank (G.V (.top j)).rank) (x : FinPt G (.top j)) (k : GA D (G.V (.top j))),
    k ∈ GinfC (G.V (.top j)) → ∀ (h : GA D (G.V (.top (j + 1)))),
      W.kerA (.col t j) (W.fock (.top t j) (movedVec t S d) Q) ((x : GA D (G.V (.top j))) * k) h =
        (∏ τ, ((realIn W.θ S.N.fr (.top j) k τ : GL (Fin (G.V (.top j)).rank) ℂ) :
              Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ).det ^
                ((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) *
            ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
              Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ).det ^ (wt G (.top (j + 1)) τ).detShift) *
          W.ker (.top t j) (W.fock (.top t j) (movedVec t S d) (GlobalTheory.AvgCol.frCh W S.N j
            (GlobalTheory.CompactHowe.substF
              (fun τ => ((realIn W.θ S.N.fr (.top (j + 1)) h τ : GL (Fin (G.V (.top (j + 1))).rank) ℂ) :
                Matrix (Fin (G.V (.top (j + 1))).rank) (Fin (G.V (.top (j + 1))).rank) ℂ))
              (fun τ => (((realIn W.θ S.N.fr (.top j) k τ)⁻¹ : GL (Fin (G.V (.top j)).rank) ℂ) :
                Matrix (Fin (G.V (.top j)).rank) (Fin (G.V (.top j)).rank) ℂ)ᵀ)
              (GlobalTheory.AvgCol.frChInv W S.N j Q))))
            (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1)))) := by
  intro D T L sc G W U S μ₀ hL j hj t d hd Q x k hk h
  have hp : DefPair D.R.m (Pair.top t j) := show j + 1 ≤ D.R.m by omega
  have hh : ((finOf _ h : GA D (G.V (.top (j + 1)))) * (infOf _ h : GA D (G.V (.top (j + 1))))) = h := by
    rw [← GlobalTheory.AdelicSplit.commute_GinfC_GfC _ (infOf _ h).2 (finOf _ h).2]
    exact infOf_mul_finOf _ h
  have hr0 : Even (G.V (.top j)).rank := by rw [rank_top G (j := j) (by omega)]; exact rankX_even D j
  have hr1 : Even (G.V (.top (j + 1))).rank := by rw [rank_top G (j := j + 1) (by omega)]; exact rankX_even D (j + 1)
  have hS : G.chrS (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrS, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pS, Nat.not_odd_iff_even.2 hr0, if_false]
  have hT : G.chrT (.top t j) = L.mu t (j + 1) := by
    simp only [GridData.chrT, Formalism.IndefR.Lift.attChr, GridData.chr, GridData.pT, Nat.not_odd_iff_even.2 hr1, if_false]
  set a : D.what₂.Tau → ℚ := fun τ => -((D.hc τ).e ⟨j, hj⟩ : ℚ) with ha_def
  have ha : ∀ τ, HasInfExp D (G.chrS (.top t j)) τ (a τ) := fun τ => by rw [hS]; exact mu_exp hL t j hj τ
  have hb : ∀ τ, HasInfExp D (G.chrT (.top t j)) τ (a τ) := fun τ => by rw [hT]; exact mu_exp hL t j hj τ
  have he₁ : ∀ τ, (((wt G (.top (j + 1)) τ).detShift : ℤ) : ℚ) =
      a τ + sgnP (Pair.top t j) * (G.pS (.top t j)).rank / 2 := fun τ => by
    rw [(detShift_top G t j hj τ).1]; simp only [sgnP, one_mul, a]
  have he₂ : ∀ τ, ((((nuEnd G (.top t j) τ : ℤ) - (wt G (.top j) τ).detShift) : ℤ) : ℚ) =
      -(a τ + sgnP (Pair.top t j) * (G.pT (.top t j)).rank / 2) := fun τ => by
    rw [(detShift_top G t j hj τ).2]; simp only [sgnP, one_mul, a]
  show W.ker (.top t j) _ ((x : GA D (G.V (.top j))) * k) h = _
  conv_lhs => rw [← hh]
  have key := ker_fock_moved_real (p := Pair.top t j) hL W S t hp d hd a a ha hb _ _ he₁ he₂ k hk (infOf _ h) (infOf _ h).2 Q
    (x : GA D (G.V (.top j))) (finOf _ h : GA D (G.V (.top (j + 1))))
  rw [key, realChar_top W S.N.fr t j, realSubst_top hL W S.N t j hp k h Q]

end GlobalTheory.ColKer

end
