import Mathlib
import Formalism.SharpRestriction.InertJacobiLevels.AsmIface
import Formalism.LocalToGlobal.GlobalTheory.IsResidueClassZero
import Formalism.SharpRestriction.GrowthBounds.SmallOrderPrimes
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.PairRowIffQdRows
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.DisjointExceptional
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.ThinScalesIffHostBound
open Formalism.BasicNotions Formalism.BasicNotions.LevelStarExponents Formalism.MainNotions Formalism.MainNotions.Inhab Formalism.L2.GlobalTheoryTheory GlobalTheory.EX NumberField

noncomputable section

namespace GlobalTheory.EX

abbrev baseOfParams {D : D7} (L : SizeData₂ D) : Arith.Base :=
  { R := D.R, sc := L.sc, q := D.host.q, d := D.host.d, cls := D.host.cls, TT := D.host.TT, Sc := L.Sc, eta := L.etaSz }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem kapISet_eq_loc {D : D7} (L : SizeData₂ D) (K : G.Consts) (p n' : ℕ) (TT : Finset (Fin n')) (a b : Fin n' → ℤ) :
    G.kapISet L K p n' TT a b = Arith.Loc.kapISet (baseOfParams L) K p n' TT a b := rfl

/- English proof (translation)
Establish `hb' : X.bs = Arith.bsH` using `by funext h t; exact hb h t`. Establish `hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI`. Use function extensionality and compare the values at `p n' TT a b`. Rewrite using `[hk p n' TT a b, kapISet_eq_loc]`. Both sides reduce to the same expression.

Unfold `G.Sig G.goodReps G.reps G.kapv G.kapLoc`. Rewrite using `[hb', hk']`. Both sides reduce to the same expression.
-/
theorem sig_eq_loc {D : D7} {L : SizeData₂ D} (X : G.Inst D L) (K : G.Consts) (hk : G.KapIDef X K)
    (hb : ∀ h t, X.bs h t = Arith.bsH h t) (a b : G.HH D → ℤ) (p : ℕ) :
    G.Sig X K a b p =
      Arith.Loc.Sig (baseOfParams L) (Arith.ins (baseOfParams L) K 1) K a b (G.hP D p) p := by
  have hb' : X.bs = Arith.bsH := by funext h t; exact hb h t
  have hk' : X.kapI = (Arith.ins (baseOfParams L) K 1).kapI := by
    funext p n' TT a b
    rw [hk p n' TT a b, kapISet_eq_loc]; rfl
  unfold G.Sig G.goodReps G.reps G.kapv G.kapLoc
  rw [hb', hk']
  rfl

/- English proof (translation)
Introduce `C cD ch p R H a b M c u0 _ hV hF hC h0 hW`. Establish `hcl : p.D.host.cls = H.cls` using `hF.cls_eq`. Take `⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩` from `hF`. Substitute `hR` using the available equality. Establish `hTT' : p.D.host.TT = H.TT` using `Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT`.

Establish `hh' : ∀ l, G.hP p.D l = hPH H l` using `fun l => Formalism.HC.Frame.A.val_injective _ (hh l)`. Establish `ha : G.aL p.L = a`. Use function extensionality and compare the values at `t`. Unfold `G.aL`. Use `split_ifs with h`.

Conclude with `(hw ⟨t, h⟩ t rfl).1`. Conclude with `(h0 t (hTT' ▸ h)).1.symm`. Establish `hb : G.bL p.L = b`. Use function extensionality and compare the values at `t`. Unfold `G.bL`.

Use `split_ifs with h`. Conclude with `(hw ⟨t, h⟩ t rfl).2`. Conclude with `(h0 t (hTT' ▸ h)).2.symm`. Establish `hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ))`. Rewrite using `[p.L.Sc_eq, hV.Del_eq]`.

Use `push_cast`. Both sides reduce to the same expression. Establish `key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A), p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) → (let B : Arith.Base` using `{ R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta } open Classical in ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l * (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) …`. Introduce `q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW`. Take `rfl : G.hP p.D = hf` from `funext e6`.

Substitute `e1 e2 e0 e3 e4 e5` using the available equality. Unfold `Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands`. Simplify using `only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]`. Conclude with `hW`. Rewrite using `[ha, hb]`.

Conclude with `key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW`.
-/
theorem wreq_of_wok : ∀ (C : FC) (cD ch : ℝ) (p : Pt C) (R : Ranks) (H : Host R) (a b : R.A → ℤ) (M : ℕ) (c : Fin M → Fin (R.k - 2) → Bool) (u0 : ℕ), Std C → Val C cD ch p.L → p.From H a b c u0 → CanonInst p.ta.Gx → (∀ t, t ∉ H.TT → a t = 0 ∧ b t = 0) → WOK p.L.sc cD ch C.GK H a b → Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK (G.aL p.L) (G.bL p.L) := by
  intro C cD ch p R H a b M c u0 _ hV hF hC h0 hW
  have hcl : p.D.host.cls = H.cls := hF.cls_eq
  obtain ⟨hR, hTT, -, hq, hd, -, -, -, -, -, hh, hw, -⟩ := hF
  subst hR
  have hTT' : p.D.host.TT = H.TT :=
    Finset.image_injective (Formalism.HC.Frame.A.val_injective _) hTT
  have hh' : ∀ l, G.hP p.D l = hPH H l := fun l => Formalism.HC.Frame.A.val_injective _ (hh l)
  have ha : G.aL p.L = a := by
    funext t
    unfold G.aL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).1
    · exact (h0 t (hTT' ▸ h)).1.symm
  have hb : G.bL p.L = b := by
    funext t
    unfold G.bL
    split_ifs with h
    · exact (hw ⟨t, h⟩ t rfl).2
    · exact (h0 t (hTT' ▸ h)).2.symm
  have hS : p.L.Sc = (p.D.R.k : ℝ) * (4 * (Delv p.L.sc cD : ℝ)) := by
    rw [p.L.Sc_eq, hV.Del_eq]; push_cast; rfl
  have key : ∀ (q d : ℕ) (cl : ℕ → PrimeClass) (TT : Finset (p.D.R.A)) (Sc eta : ℝ) (hf : ℕ → p.D.R.A),
      p.D.host.q = q → p.D.host.d = d → p.D.host.cls = cl → p.D.host.TT = TT → p.L.Sc = Sc → p.L.etaSz = eta → (∀ l, G.hP p.D l = hf l) →
      (let B : Arith.Base := { R := p.D.R, sc := p.L.sc, q := q, d := d, cls := cl, TT := TT, Sc := Sc, eta := eta }
       open Classical in
       ∑ l ∈ (Finset.range ⌈p.L.sc.X'⌉₊).filter (fun l => Arith.Loc.Cand B C.GK (hf l) l), Real.log l / l *
        (2 * (if p.L.sc.x ^ (-p.L.sc.eps) < Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l then (1 : ℝ) else 0) +
          4 * Arith.Loc.Sig B (Arith.ins B C.GK 1) C.GK a b (hf l) l) ≤ p.L.sc.x ^ (-9 : ℝ)) →
      Formalism.MainNotions.AuxBlock8.WReq p.ta.Gx C.GK a b := by
    intro q d cl TT Sc eta hf e1 e2 e0 e3 e4 e5 e6 hW
    obtain rfl : G.hP p.D = hf := funext e6
    subst e1 e2 e0 e3 e4 e5
    unfold Formalism.MainNotions.AuxBlock8.WReq Formalism.MainNotions.AuxBlock8.cands
    simp only [sig_eq_loc p.ta.Gx C.GK p.xa.ex.kapI_def hC.1]
    exact hW
  rw [ha, hb]
  exact key _ _ _ _ _ _ _ hq hd hcl hTT' hS hV.eta_eq hh' hW

end GlobalTheory.EX

end
