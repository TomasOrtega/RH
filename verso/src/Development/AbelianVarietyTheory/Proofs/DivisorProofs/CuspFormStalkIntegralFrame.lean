import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PhiAt
import Development.AbelianVarietyTheory.Definitions.Divisors.PolyBetween
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaExponentsDominantLastEntryOneDegree
import Development.AbelianVarietyTheory.Definitions.Divisors.MulSmulIdemMem
import Development.AbelianVarietyTheory.Definitions.Divisors.CovolXOfCovol
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralFramePointStalkCompatStatement
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop GlobalTheory.BigTop
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistVal

open GlobalTheory.FlatTw GlobalTheory.FlatLine GlobalTheory.AllWt

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ} {U : ∀ σ : c.F →+* ℂ, Unf Xo c σ r} {x : ℝ}
  {Z : Comp Xo c} {T : CDVR} {io : c.F →+* T.Fr} (y' : IntFr Xo c T io)

/- English proof (translation)
Establish `e` using `evI_mul y' (idem Z) (idem Z)`. Rewrite `e` using `[idem_mul_idem]`. Conclude with `mul_left_cancel₀ h (by rw [mul_one]; exact e.symm)`.
-/
theorem evI_idem_eq_one (h : evI y' (idem Z) ≠ 0) : evI y' (idem Z) = 1 := by
  have e := evI_mul y' (idem Z) (idem Z)
  rw [idem_mul_idem] at e
  exact mul_left_cancel₀ h (by rw [mul_one]; exact e.symm)

/- English proof (translation)
Establish `e : evI y' s.sig * evI y' s.inv = 1` using `by rw [← evI_mul, s.mul_inv, he]`. Establish `h1 : evI y' s.sig ≠ 0` using `left_ne_zero_of_mul_eq_one e`. Establish `h2 : evI y' s.inv ≠ 0` using `right_ne_zero_of_mul_eq_one e`. Use `⟨h1, h2, ?_⟩` and prove the remaining obligations. Rewrite using `[← vV_mul h1 h2, e]`.

Simplify using `[vV]`.
-/
theorem val_inv {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1) :
    evI y' s.sig ≠ 0 ∧ evI y' s.inv ≠ 0 ∧ vV T.V (evI y' s.sig) + vV T.V (evI y' s.inv) = 0 := by
  have e : evI y' s.sig * evI y' s.inv = 1 := by rw [← evI_mul, s.mul_inv, he]
  have h1 : evI y' s.sig ≠ 0 := left_ne_zero_of_mul_eq_one e
  have h2 : evI y' s.inv ≠ 0 := right_ne_zero_of_mul_eq_one e
  refine ⟨h1, h2, ?_⟩
  rw [← vV_mul h1 h2, e]
  simp [vV]

/- English proof (translation)
Use `show vV T.V (evI y' (s.sig * t.sig)) = 0`. Rewrite using `[evI_mul, vV_mul (val_inv y' s he).1 (val_inv y' t he).1, hs, ht, add_zero]`.
-/
theorem val_mul {G₀ G₁ : WTZ E} (s : TwSec U x Z G₀) (t : TwSec U x Z G₁) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (ht : vV T.V (evI y' t.sig) = 0) : vV T.V (evI y' (s.mul t).sig) = 0 := by
  show vV T.V (evI y' (s.sig * t.sig)) = 0
  rw [evI_mul, vV_mul (val_inv y' s he).1 (val_inv y' t he).1, hs, ht, add_zero]

/- English proof (translation)
Establish `h` using `(val_inv y' s he).2.2`. Use `show vV T.V (evI y' s.inv) = 0`. Use linear arithmetic over natural numbers and integers.
-/
theorem val_symm {G₀ : WTZ E} (s : TwSec U x Z G₀) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : vV T.V (evI y' s.symm.sig) = 0 := by
  have h := (val_inv y' s he).2.2
  show vV T.V (evI y' s.inv) = 0
  omega

/- English proof (translation)
The claim follows from `| 0 => ⟨(s.mul s.symm).copy (by rw [add_neg_cancel, Nat.cast_zero, zero_mul, wtOf_zero]), val_mul y' s s.symm he hs (val_symm y' s he hs)⟩ | n + 1 => by obtain ⟨t, ht⟩ := exists_pow s he hs n exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero]; push_cast; ring_nf), val_mul y' t s …`.
-/
theorem exists_pow {e : ℤ} (s : TwSec U x Z (wtOf Dw 0 e)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) : ∀ n : ℕ, ∃ t : TwSec U x Z (wtOf Dw 0 ((n : ℤ) * e)),
      vV T.V (evI y' t.sig) = 0
  | 0 => ⟨(s.mul s.symm).copy (by rw [add_neg_cancel, Nat.cast_zero, zero_mul, wtOf_zero]),
      val_mul y' s s.symm he hs (val_symm y' s he hs)⟩
  | n + 1 => by
    obtain ⟨t, ht⟩ := exists_pow s he hs n
    exact ⟨(t.mul s).copy (by rw [← wtOf_add, add_zero]; push_cast; ring_nf), val_mul y' t s he ht hs⟩

/- English proof (translation)
Break down `Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩` into its components or cases. Take `⟨t, ht⟩` from `exists_pow y' s he hs n`. Conclude with `⟨t.copy (by rw [mul_one]), ht⟩`. Establish `hneg : -wtOf Dw 0 1 = wtOf Dw 0 (-1)` using `neg_eq_of_add_eq_zero_right (by rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero])`. Take `⟨t, ht⟩` from `exists_pow y' (s.symm.copy hneg) he (val_symm y' s he hs) n`.

Conclude with `⟨t.copy (by rw [mul_neg_one]), ht⟩`.
-/
theorem exists_zpow (s : TwSec U x Z (wtOf Dw 0 1)) (he : evI y' (idem Z) = 1)
    (hs : vV T.V (evI y' s.sig) = 0) (k : ℤ) : ∃ t : TwSec U x Z (wtOf Dw 0 k), vV T.V (evI y' t.sig) = 0 := by
  rcases Int.eq_nat_or_neg k with ⟨n, rfl | rfl⟩
  · obtain ⟨t, ht⟩ := exists_pow y' s he hs n
    exact ⟨t.copy (by rw [mul_one]), ht⟩
  · have hneg : -wtOf Dw 0 1 = wtOf Dw 0 (-1) :=
      neg_eq_of_add_eq_zero_right (by rw [← wtOf_add, add_zero, add_neg_cancel, wtOf_zero])
    obtain ⟨t, ht⟩ := exists_pow y' (s.symm.copy hneg) he (val_symm y' s he hs) n
    exact ⟨t.copy (by rw [mul_neg_one]), ht⟩

end GlobalTheory.TwistVal

set_option maxHeartbeats 2000000 in

/- English proof (translation)
Introduce `hP hD hS hF`. Establish `A` using `GlobalTheory.T.integral_frame_point_stalk hP hD hS hF`. Establish `B` using `GlobalTheory.T.integral_frame_point_stalk_compat hP hD hS hF`. Unfold `Covers Lifts at *`. Use `(A.and B).imp fun Fm CH _ h => ?_` and prove the remaining obligations.

Take `⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩` from `h`. Use `⟨C1, h1, ?_⟩` and prove the remaining obligations. Take `⟨x0, hx0⟩` from `e1.and e2`. Use `⟨x0, fun x hx hle ι p hp i hi Y hY Z TF la w m _ f hf y T io y' g hg hpt hf0 => ?_⟩` and prove the remaining obligations. Take `⟨hA, hB⟩` from `hx0 x hx hle ι p hp`.

Establish `hfi : GlobalTheory.FlatLine.idem Z * f = f` using `GlobalTheory.FlatLine.idem_mul_eq (e := exZ _ (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m)) ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩`. Establish `hid : evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0` using `fun h0 => hf0 (by rw [← hfi, evI_mul, h0, zero_mul])`. Establish `he` using `GlobalTheory.TwistVal.evI_idem_eq_one y' hid`. Take `⟨t1, ht1⟩` from `hA i hi Y hY Z TF y T io y' g hg hpt hid`. Take `⟨t2, ht2⟩` from `hB i hi Y hY Z TF y T io y' g hg hpt hid (-w)`.

Take `⟨tk, htk⟩` from `GlobalTheory.TwistVal.exists_zpow y' t1 he ht1 (-m)`. Set `z` to `t2.mul tk`. Establish `hz` using `GlobalTheory.TwistVal.val_mul y' t2 tk he ht2 htk`. Establish `hw : AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m + (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) (-w)) 0 + AllWt.wtOf (dat p i) 0 (-m)) = AllWt.wtOf (dat p i) la 0`. Rewrite using `[← AllWt.wtOf_add, ← AllWt.wtOf_add]`.

Use `congr 1`. Use function extensionality and compare the values at `τ j`. Simplify using `[GlobalTheory.FlatLine.parWt]`. Expand and normalize the polynomial expressions, which then agree. Establish `hmem` using `z.cusp_sig _ (AllWt.even_wtOf _ _) f hf`.

Rewrite `hmem` using `[hw]`. Use `⟨⟨f * z.sig, hmem⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show evI y' (f * z.sig) ≠ 0`. Rewrite using `[evI_mul]`. Conclude with `mul_ne_zero hf0 (GlobalTheory.TwistVal.val_inv y' z he).1`.

Use `show vV T.V (evI y' (f * z.sig)) = vV T.V (evI y' f)`. Rewrite using `[evI_mul, vV_mul hf0 (GlobalTheory.TwistVal.val_inv y' z he).1, hz, add_zero]`.
-/
theorem GlobalTheory.TwistVal.twist_keeps_val : Hypotheses2 → DeepGood → Size → FlatDeg → Covers fun Fm x _ ι p i Y PP _ => ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (TF : TorFlag Y.d.Xo₂ Y.d.c₂) (la : AllWt.Weight (dat p i)) (w : AllWt.Psi p.T.Q.H → ℤ) (m : ℤ), 4 ∣ m → ∀ f ∈ AllWt.cuspOn Y.U Z (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m), ∀ (y : Y₀ TF.X Z) (T : CDVR) (io : Y.d.c₂.F →+* T.Fr) (y' : IntFr Y.d.Xo₂ Y.d.c₂ T io) (g : (Y₀ TF.X Z).presheaf.stalk y →+* T.V), IsLocalHom g → (letI := io.toAlgebra; TF.X.ptY y'.1 = Spec.map (CommRingCat.ofHom ((algebraMap T.V T.Fr).comp g)) ≫ (Y₀ TF.X Z).fromSpecStalk y ≫ inc₀ TF.X Z) → evI y' f ≠ 0 → ∃ f' : Cusp Z Y.U la, evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂)) ≠ 0 ∧ vV T.V (evI y' ((f' : Rul Y.d.Xo₂ Y.d.c₂))) = vV T.V (evI y' f) := by
  intro hP hD hS hF
  have A := GlobalTheory.T.integral_frame_point_stalk hP hD hS hF
  have B := GlobalTheory.T.integral_frame_point_stalk_compat hP hD hS hF
  unfold Covers Lifts at *
  refine (A.and B).imp fun Fm CH _ h => ?_
  obtain ⟨⟨C1, h1, e1⟩, ⟨C2, h2, e2⟩⟩ := h
  refine ⟨C1, h1, ?_⟩
  obtain ⟨x0, hx0⟩ := e1.and e2
  refine ⟨x0, fun x hx hle ι p hp i hi Y hY Z TF la w m _ f hf y T io y' g hg hpt hf0 => ?_⟩
  obtain ⟨hA, hB⟩ := hx0 x hx hle ι p hp
  have hfi : GlobalTheory.FlatLine.idem Z * f = f :=
    GlobalTheory.FlatLine.idem_mul_eq (e := exZ _ (AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m))
      ⟨AllWt.cuspW_le_secZ _ hf.1, hf.2⟩
  have hid : evI y' (GlobalTheory.FlatLine.idem Z) ≠ 0 := fun h0 => hf0 (by rw [← hfi, evI_mul, h0, zero_mul])
  have he := GlobalTheory.TwistVal.evI_idem_eq_one y' hid
  obtain ⟨t1, ht1⟩ := hA i hi Y hY Z TF y T io y' g hg hpt hid
  obtain ⟨t2, ht2⟩ := hB i hi Y hY Z TF y T io y' g hg hpt hid (-w)
  obtain ⟨tk, htk⟩ := GlobalTheory.TwistVal.exists_zpow y' t1 he ht1 (-m)
  let z := t2.mul tk
  have hz := GlobalTheory.TwistVal.val_mul y' t2 tk he ht2 htk
  have hw : AllWt.wtOf (dat p i) (la + GlobalTheory.FlatLine.parWt (dat p i) w) m +
      (AllWt.wtOf (dat p i) (GlobalTheory.FlatLine.parWt (dat p i) (-w)) 0 + AllWt.wtOf (dat p i) 0 (-m)) =
      AllWt.wtOf (dat p i) la 0 := by
    rw [← AllWt.wtOf_add, ← AllWt.wtOf_add]
    congr 1
    · funext τ j
      simp [GlobalTheory.FlatLine.parWt]
    · ring
  have hmem := z.cusp_sig _ (AllWt.even_wtOf _ _) f hf
  rw [hw] at hmem
  refine ⟨⟨f * z.sig, hmem⟩, ?_, ?_⟩
  · show evI y' (f * z.sig) ≠ 0
    rw [evI_mul]
    exact mul_ne_zero hf0 (GlobalTheory.TwistVal.val_inv y' z he).1
  · show vV T.V (evI y' (f * z.sig)) = vV T.V (evI y' f)
    rw [evI_mul, vV_mul hf0 (GlobalTheory.TwistVal.val_inv y' z he).1, hz, add_zero]

end
