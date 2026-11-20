import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IwahoriFactorisation.TwistedConjugationNorms.LocalMatchingOfAssemblyHypotheses
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedIwahoriContractionHolds
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriContraction
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IwahoriAndMaximalCompactCriteria
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDiagUnit
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsNormalisedThetaSub
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PlaceConjugationPropertiesCmFieldStatement

open Matrix ValuativeRel
open GlobalTheory.CompanionTheory.TwContraction

namespace GlobalTheory.CompanionTheory.ThetaContraction

section Step

variable {F : Type} [Field F] {n : ℕ}

def sg (F : Type) [Field F] {n : ℕ} (i l : Fin n) : F := (-1) ^ ((i : ℕ) + l)

/- English proof (translation)
Rewrite using `[sg, ← pow_add]`. Conclude with `Even.neg_one_pow ⟨_, rfl⟩`.
-/
theorem sg_mul_self (i l : Fin n) : sg F i l * sg F i l = 1 := by
  rw [sg, ← pow_add]
  exact Even.neg_one_pow ⟨_, rfl⟩

/- English proof (translation)
Rewrite using `[sg]`. Conclude with `Even.neg_one_pow ⟨_, rfl⟩`.
-/
theorem sg_self (i : Fin n) : sg F i i = 1 := by
  rw [sg]
  exact Even.neg_one_pow ⟨_, rfl⟩

/- English proof (translation)
Simplify using `[sg]`.
-/
theorem map_sg (c : F →+* F) (i l : Fin n) : c (sg F i l) = sg F i l := by
  simp [sg]

/- English proof (translation)
Use `set P' : Matrix (Fin n) (Fin n) F := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hP'`. Establish `h1 : (1 + T) * P' = 1`. Rewrite using `[← hP, hP', ← Units.val_mul, mul_inv_cancel]`. Both sides reduce to the same expression. Establish `h2 : P' = 1 - T * P'`.

Rewrite `h1` using `[add_mul, one_mul]`. Conclude with `eq_sub_of_add_eq h1`. Establish `h3 : P' = 1 - T + T * T * P'`. Combine the equalities or inequalities in the displayed calculation. Establish `hent : P' l.rev i.rev = (1 - T + T * T * P') l.rev i.rev` using `congrFun (congrFun h3 _) _`.

Rewrite using `[GlobalTheory.ThetaPull.thetaGL_apply, ← hP', hent, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub, mul_add, mul_sub]`. Use `congr 2`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, mul_one]`.

Conclude with `sg_self i`. Establish `h' : l.rev ≠ i.rev` using `fun e => h (Fin.rev_injective e).symm`. Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h', map_zero, mul_zero]`.
-/
theorem theta_expand (c : F →+* F) (p : GL (Fin n) F) (T : Matrix (Fin n) (Fin n) F)
    (hP : (p : Matrix (Fin n) (Fin n) F) = 1 + T) (i l : Fin n) :
    (GlobalTheory.CuspRep.thetaGL n c p).val i l = (1 : Matrix (Fin n) (Fin n) F) i l -
      sg F i l * c (T l.rev i.rev) +
      sg F i l * c ((T * T * ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)) l.rev i.rev) := by
  set P' : Matrix (Fin n) (Fin n) F := ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) with hP'
  have h1 : (1 + T) * P' = 1 := by
    rw [← hP, hP', ← Units.val_mul, mul_inv_cancel]
    rfl
  have h2 : P' = 1 - T * P' := by
    rw [add_mul, one_mul] at h1
    exact eq_sub_of_add_eq h1
  have h3 : P' = 1 - T + T * T * P' := by
    calc P' = 1 - T * P' := h2
      _ = 1 - T * (1 - T * P') := by rw [← h2]; exact h2
      _ = 1 - T + T * T * P' := by noncomm_ring
  have hent : P' l.rev i.rev = (1 - T + T * T * P') l.rev i.rev := congrFun (congrFun h3 _) _
  rw [GlobalTheory.ThetaPull.thetaGL_apply, ← hP', hent, Matrix.add_apply, Matrix.sub_apply, map_add, map_sub,
    mul_add, mul_sub]
  congr 2
  · by_cases h : i = l
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one, mul_one]
      exact sg_self i
    · have h' : l.rev ≠ i.rev := fun e => h (Fin.rev_injective e).symm
      rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h', map_zero, mul_zero]

variable [ValuativeRel F]

/- English proof (translation)
Establish `hI : g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := by rw [← hU]; exact hgU`. Establish `hρ1' : ρ ≤ 1` using `hρ1.le`. Use `set C : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hCdef`. Set `d : Fin n → F` to `fun i => C i i`. Establish `hd : ∀ i, valuation F (d i) = 1` using `fun i => val_diag_of_mem_iwahori hI i`.

Establish `hd0 : ∀ i, d i ≠ 0` using `fun i h => by`. Use `hd i` as an intermediate fact. Rewrite `this` using `[h, map_zero]`. Conclude with `zero_ne_one this`. Establish `hsgv : ∀ i l : Fin n, valuation F (sg F i l) = 1` using `fun i l => by`.

Rewrite using `[sg, map_pow, Valuation.map_neg, map_one, one_pow]`. Establish `hev : ∀ i, valuation F (e i) ≠ 0` using `fun i => (Valuation.ne_zero_iff _).2 (he i)`. Establish `hq : ∀ i l, i < l → valuation F (e i / e l) ≤ ρ` using `fun i l h => by`. Rewrite using `[map_div₀, div_le_iff₀ (zero_lt_iff.2 (hev l))]`. Conclude with `hc i l h`.

Use `set s : ℕ := max j 1 with hs`. Establish `hs1 : 1 ≤ s` using `le_max_right _ _`. Establish `hjs : j ≤ s` using `le_max_left _ _`. Establish `hsj : s ≤ j + 1` using `max_le (Nat.le_succ j) (Nat.le_add_left 1 j)`. Establish `hlow : ∀ i l, l < i → valuation F (C i l) ≤ ρ ^ s` using `fun i l h => by`.

Break down `max_choice j 1 with h' | h'` into its components or cases. Rewrite using `[hs, h']`. Conclude with `hgD i l h.ne'`. Rewrite using `[hs, h', pow_one]`. Conclude with `hunif _ (hI.2 i l h)`.

Set `T : Matrix (Fin n) (Fin n) F` to `fun i l => if l < i then sg F l.rev i.rev * c (C l.rev i.rev / d l.rev) else if i < l then (e i / e l) * (C i l / d l) else 0`. Establish `hTlo : ∀ i l, l < i → T i l = sg F l.rev i.rev * c (C l.rev i.rev / d l.rev)` using `fun i l h => if_pos h`. Establish `hTup : ∀ i l, i < l → T i l = (e i / e l) * (C i l / d l)` using `fun i l h => by show (if l < i then _ else _) = _`. Rewrite using `[if_neg (not_lt.2 h.le), if_pos h]`. Establish `hTd : ∀ i, T i i = 0` using `fun i => by show (if i < i then _ else _) = _`.

Rewrite using `[if_neg (lt_irrefl i), if_neg (lt_irrefl i)]`. Establish `hTlov : ∀ i l, l < i → valuation F (T i l) ≤ ρ ^ s` using `fun i l h => by`. Rewrite using `[hTlo i l h, map_mul, hsgv, one_mul, hcv, map_div₀, hd, div_one]`. Conclude with `hlow _ _ (Fin.rev_lt_rev.2 h)`. Establish `hTupv : ∀ i l, i < l → valuation F (T i l) ≤ ρ ^ (j + 1)` using `fun i l h => by`.

Rewrite using `[hTup i l h, map_mul, map_div₀ _ (C i l), hd, div_one, pow_succ']`. Conclude with `mul_le_mul' (hq i l h) (hgD i l h.ne)`. Establish `hT : Dp ρ s T` using `fun i l => by`. Break down `lt_trichotomy i l with h | h | h` into its components or cases. Conclude with `(hTupv i l h).trans (pow_le_pow_right_of_le_one' hρ1' hsj)`.

Substitute `h` using the available equality. Rewrite using `[hTd, map_zero]`. Conclude with `zero_le'`. Conclude with `hTlov i l h`. Establish `hρs : ρ ^ s ≤ ρ`.

Combine the equalities or inequalities in the displayed calculation. Use `set P : Matrix (Fin n) (Fin n) F := 1 + T with hP`. Establish `hPd : ∀ i, P i i = 1` using `fun i => by`. Rewrite using `[hP, Matrix.add_apply, Matrix.one_apply_eq, hTd, add_zero]`. Establish `hPo : ∀ i l, i ≠ l → P i l = T i l` using `fun i l h => by`.

Rewrite using `[hP, Matrix.add_apply, Matrix.one_apply_ne h, zero_add]`. Establish `hPint : ∀ i l, valuation F (P i l) ≤ 1` using `fun i l => by`. Distinguish the cases in `h : i = l`. Substitute `h` using the available equality. Rewrite using `[hPd, map_one]`.

Rewrite using `[hPo i l h]`. Conclude with `(hT i l).trans (hρs.trans hρ1')`. Establish `hPlow : ∀ i l, l < i → valuation F (P i l) < 1` using `fun i l h => by`. Rewrite using `[hPo i l h.ne']`. Conclude with `lt_of_le_of_lt ((hT i l).trans hρs) hρ1`.

Establish `hPdet : valuation F P.det = 1`. Establish `h1` using `val_det_sub_prod_lt P hPint hPlow`. Rewrite `h1` using `[Finset.prod_congr rfl fun i _ => hPd i, Finset.prod_const_one]`. Use `Valuation.map_eq_of_sub_lt (valuation F) (x := (1 : F)) (y := P.det) (by rwa [map_one])` as an intermediate fact. Rewrite `this` using `[map_one]`. Then use the resulting hypothesis.

Establish `hPne : P.det ≠ 0` using `fun h => by`. Rewrite `hPdet` using `[h, map_zero]`. Conclude with `zero_ne_one hPdet`. Set `p : GL (Fin n) F` to `Matrix.GeneralLinearGroup.mkOfDetNeZero P hPne`. Establish `hpv : (p : Matrix (Fin n) (Fin n) F) = P` using `rfl`.

Establish `hpI : p ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := ⟨mem_unitGL_of p hPint hPdet, hPlow⟩`. Establish `hpU : p ∈ U`. Rewrite using `[← SetLike.mem_coe, hU]`. Conclude with `hpI`. Establish `hxinv : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Matrix.diagonal fun i => (e i)⁻¹`.

Rewrite using `[Matrix.coe_units_inv, hx]`. Use `Matrix.inv_eq_left_inv ?_` and prove the remaining obligations. Rewrite using `[Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `inv_mul_cancel₀ (he i)`. Set `q : GL (Fin n) F` to `x⁻¹ * p * x`. Use `set Q : Matrix (Fin n) (Fin n) F := (q : Matrix (Fin n) (Fin n) F) with hQdef`. Establish `hQ : ∀ i l, Q i l = (e i)⁻¹ * P i l * e l` using `fun i l => by show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l = _`. Rewrite using `[Units.val_mul, Units.val_mul, hxinv, hx, hpv, Matrix.mul_diagonal, Matrix.diagonal_mul]`.

Establish `hQd : ∀ i, Q i i = 1` using `fun i => by`. Rewrite using `[hQ, hPd, mul_one, inv_mul_cancel₀ (he i)]`. Establish `hQup : ∀ i l, i < l → Q i l = C i l / d l` using `fun i l h => by`. Rewrite using `[hQ, hPo i l h.ne, hTup i l h]`. Establish `h1` using `he i`.

Establish `h2` using `he l`. Clear the denominators using the available nonvanishing facts. Establish `hQlow : ∀ i l, l < i → valuation F (Q i l) ≤ ρ * ρ ^ s` using `fun i l h => by`. Rewrite using `[hQ, hPo i l h.ne', show (e i)⁻¹ * T i l * e l = (e l / e i) * T i l by`. Rewrite using `[div_eq_mul_inv]`.

Use the proof step `ring, map_mul]`. Conclude with `mul_le_mul' (hq l i h) (hTlov i l h)`. Establish `hQint : ∀ i l, valuation F (Q i l) ≤ 1` using `fun i l => by`. Break down `lt_trichotomy i l with h | h | h` into its components or cases. Rewrite using `[hQup i l h, map_div₀, hd, div_one]`.

Conclude with `mem_unitGL_entries hI.1 i l`. Substitute `h` using the available equality. Rewrite using `[hQd, map_one]`. Use `(hQlow i l h).trans ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Establish `hQdet : valuation F Q.det = 1`. Establish `: Q.det = P.det` using `by show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = _`. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hpv]`. Establish `h3 : (x : Matrix (Fin n) (Fin n) F).det * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1`. Rewrite using `[← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]`.

Simplify using the standard rewrite rules. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `hPdet`. Establish `hqU : q ∈ U`.

Establish `: q ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := ⟨mem_unitGL_of q hQint hQdet, fun i l h => lt_of_le_of_lt (hQlow i l h) (lt_of_le_of_lt (mul_le_mul' le_rfl hρs) (by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← SetLike.mem_coe, hU]`. Conclude with `this`. Set `T' : Matrix (Fin n) (Fin n) F` to `fun i l => - (sg F i l * c (T l.rev i.rev))`.

Establish `hT'v : ∀ i l, valuation F (T' i l) = valuation F (T l.rev i.rev)` using `fun i l => by show valuation F (- (sg F i l * c (T l.rev i.rev))) = _`. Rewrite using `[Valuation.map_neg, map_mul, hsgv, one_mul, hcv]`. Establish `hT' : Dp ρ s T'` using `fun i l => by`. Rewrite using `[hT'v]`. Conclude with `hT _ _`.

Establish `hT'd : ∀ i, T' i i = 0` using `fun i => by show - (sg F i i * c (T i.rev i.rev)) = 0`. Rewrite using `[hTd, map_zero, mul_zero, neg_zero]`. Establish `hT'lo : ∀ i l, l < i → T' i l = - (C i l / d i)` using `fun i l h => by show - (sg F i l * c (T l.rev i.rev)) = _`. Rewrite using `[hTlo _ _ (Fin.rev_lt_rev.2 h), Fin.rev_rev, Fin.rev_rev, map_mul, map_sg, hcc, ← mul_assoc, sg_mul_self, one_mul]`. Establish `hT'up : ∀ i l, i < l → valuation F (T' i l) ≤ ρ ^ (j + 1)` using `fun i l h => by`.

Rewrite using `[hT'v]`. Conclude with `hTupv _ _ (Fin.rev_lt_rev.2 h)`. Establish `hp0 : Dp ρ 0 ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)` using `fun a b => by`. Rewrite using `[pow_zero]`. Establish `: p⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := by`.

Rewrite using `[← hU]`. Conclude with `U.inv_mem hpU`. Conclude with `mem_unitGL_entries this.1 a b`. Set `W : Matrix (Fin n) (Fin n) F` to `T * T * ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)`. Establish `hW : Dp ρ (s + s + 0) W` using `(hT.mul hT).mul hp0`.

Set `D : Matrix (Fin n) (Fin n) F` to `fun i l => sg F i l * c (W l.rev i.rev)`. Establish `hD : Dp ρ (s + s + 0) D` using `fun i l => by show valuation F (sg F i l * c (W l.rev i.rev)) ≤ _`. Rewrite using `[map_mul, hsgv, one_mul, hcv]`. Conclude with `hW _ _`. Establish `hθ : ((GlobalTheory.CuspRep.thetaGL n c p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + T' + D`.

Use extensionality with `i l`. Rewrite using `[theta_expand c p T hpv i l, Matrix.add_apply, Matrix.add_apply]`. Use `show _ = (1 : Matrix (Fin n) (Fin n) F) i l + - (sg F i l * c (T l.rev i.rev)) + sg F i l * c (W l.rev i.rev)`. Rewrite using `[sub_eq_add_neg]`. Set `Dg : Matrix (Fin n) (Fin n) F` to `Matrix.diagonal d`.

Set `Co : Matrix (Fin n) (Fin n) F` to `C - Dg`. Establish `hC0 : Dp ρ 0 C` using `fun a b => by`. Rewrite using `[pow_zero]`. Conclude with `mem_unitGL_entries hI.1 a b`. Establish `hCo : Dp ρ j Co` using `fun i l => by`.

Distinguish the cases in `h : i = l`. Substitute `h show valuation F (C i i - Dg i i) ≤ _` using the available equality. Rewrite using `[show Dg i i = C i i from Matrix.diagonal_apply_eq _ _, sub_self, map_zero]`. Conclude with `zero_le'`. Use `show valuation F (C i l - Dg i l) ≤ _`.

Rewrite using `[show Dg i l = 0 from Matrix.diagonal_apply_ne _ h, sub_zero]`. Conclude with `hgD i l h`. Set `B : Matrix (Fin n) (Fin n) F` to `C + Dg * T' - Q * Dg`. Establish `hBe : ∀ i l, B i l = C i l + d i * T' i l - Q i l * d l` using `fun i l => by show (C + Dg * T' - Q * Dg) i l = _`. Rewrite using `[Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]`.

Establish `hB : Dp ρ (j + 1) B` using `fun i l => by`. Rewrite using `[hBe]`. Break down `lt_trichotomy i l with h | h | h` into its components or cases. Rewrite using `[hQup i l h, div_mul_cancel₀ _ (hd0 l), add_sub_cancel_left, map_mul, hd, one_mul]`. Conclude with `hT'up i l h`.

Substitute `h` using the available equality. Rewrite using `[hT'd, hQd, mul_zero, add_zero, one_mul]`. Use `show valuation F (C i i - C i i) ≤ _`. Rewrite using `[sub_self, map_zero]`. Conclude with `zero_le'`.

Rewrite using `[hT'lo i l h, mul_neg, mul_div_cancel₀ _ (hd0 i), add_neg_cancel, zero_sub, Valuation.map_neg, map_mul, hd, mul_one]`. Use `(hQlow i l h).trans ?_` and prove the remaining obligations. Rewrite using `[← pow_succ']`. Conclude with `pow_le_pow_right_of_le_one' hρ1' (Nat.succ_le_succ hjs)`. Set `R : Matrix (Fin n) (Fin n) F` to `B + Co * T' + C * D`.

Establish `hR : Dp ρ (j + 1) R` using `(hB.add ((hCo.mul hT').mono hρ1' (Nat.add_le_add_left hs1 j))).add ((hC0.mul hD).mono hρ1' (by omega))`. Establish `hid : C * (1 + T' + D) = Q * Dg + R` using `by show C * (1 + T' + D) = Q * Dg + (C + Dg * T' - Q * Dg + (C - Dg) * T' + C * D) noncomm_ring`. Establish `hw : x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p = q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p)` using `by show _ = (x⁻¹ * p * x)⁻¹ * _ group`. Use `⟨p, hpU, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hw]`.

Conclude with `U.mul_mem (U.inv_mem hqU) (U.mul_mem hgU (hθU p hpU))`. Introduce `i l hil`. Rewrite using `[hw]`. Establish `hval : ((q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p) : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = Dg + ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R`. Rewrite using `[Units.val_mul, Units.val_mul, hθ]`.

Use `show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C * (1 + T' + D)) = _`. Rewrite using `[hid, mul_add, ← mul_assoc]`. Use `congr 1`. Use `show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F) * Dg = Dg`. Rewrite using `[← Units.val_mul, inv_mul_cancel]`.

Simplify using the standard rewrite rules. Rewrite using `[hval, Matrix.add_apply, show Dg i l = 0 from Matrix.diagonal_apply_ne _ hil, zero_add]`. Establish `hq0 : Dp ρ 0 ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)` using `fun a b => by`. Rewrite using `[pow_zero]`. Establish `: q⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := by`.

Rewrite using `[← hU]`. Conclude with `U.inv_mem hqU`. Conclude with `mem_unitGL_entries this.1 a b`. Use `(hq0.mul hR) i l` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis.
-/
theorem step (U : Subgroup (GL (Fin n) F)) (hU : (U : Set (GL (Fin n) F)) = PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F)
    (c : F →+* F) (hcv : ∀ a, valuation F (c a) = valuation F a) (hcc : ∀ a, c (c a) = a)
    (hθU : ∀ g ∈ U, GlobalTheory.CuspRep.thetaGL n c g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (j : ℕ) (g : GL (Fin n) F) (hgU : g ∈ U)
    (hgD : ∀ i l, i ≠ l → valuation F ((g : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j) :
    ∃ p ∈ U, x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p ∈ U ∧
      ∀ i l, i ≠ l → valuation F (((x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p :
        GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ (j + 1) := by
  have hI : g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by rw [← hU]; exact hgU
  have hρ1' : ρ ≤ 1 := hρ1.le
  set C : Matrix (Fin n) (Fin n) F := (g : Matrix (Fin n) (Fin n) F) with hCdef
  let d : Fin n → F := fun i => C i i
  have hd : ∀ i, valuation F (d i) = 1 := fun i => val_diag_of_mem_iwahori hI i
  have hd0 : ∀ i, d i ≠ 0 := fun i h => by
    have := hd i
    rw [h, map_zero] at this
    exact zero_ne_one this
  have hsgv : ∀ i l : Fin n, valuation F (sg F i l) = 1 := fun i l => by
    rw [sg, map_pow, Valuation.map_neg, map_one, one_pow]
  have hev : ∀ i, valuation F (e i) ≠ 0 := fun i => (Valuation.ne_zero_iff _).2 (he i)
  have hq : ∀ i l, i < l → valuation F (e i / e l) ≤ ρ := fun i l h => by
    rw [map_div₀, div_le_iff₀ (zero_lt_iff.2 (hev l))]
    exact hc i l h
  set s : ℕ := max j 1 with hs
  have hs1 : 1 ≤ s := le_max_right _ _
  have hjs : j ≤ s := le_max_left _ _
  have hsj : s ≤ j + 1 := max_le (Nat.le_succ j) (Nat.le_add_left 1 j)
  have hlow : ∀ i l, l < i → valuation F (C i l) ≤ ρ ^ s := fun i l h => by
    rcases max_choice j 1 with h' | h'
    · rw [hs, h']; exact hgD i l h.ne'
    · rw [hs, h', pow_one]; exact hunif _ (hI.2 i l h)
  let T : Matrix (Fin n) (Fin n) F := fun i l =>
    if l < i then sg F l.rev i.rev * c (C l.rev i.rev / d l.rev)
    else if i < l then (e i / e l) * (C i l / d l) else 0
  have hTlo : ∀ i l, l < i → T i l = sg F l.rev i.rev * c (C l.rev i.rev / d l.rev) :=
    fun i l h => if_pos h
  have hTup : ∀ i l, i < l → T i l = (e i / e l) * (C i l / d l) := fun i l h => by
    show (if l < i then _ else _) = _
    rw [if_neg (not_lt.2 h.le), if_pos h]
  have hTd : ∀ i, T i i = 0 := fun i => by
    show (if i < i then _ else _) = _
    rw [if_neg (lt_irrefl i), if_neg (lt_irrefl i)]
  have hTlov : ∀ i l, l < i → valuation F (T i l) ≤ ρ ^ s := fun i l h => by
    rw [hTlo i l h, map_mul, hsgv, one_mul, hcv, map_div₀, hd, div_one]
    exact hlow _ _ (Fin.rev_lt_rev.2 h)
  have hTupv : ∀ i l, i < l → valuation F (T i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hTup i l h, map_mul, map_div₀ _ (C i l), hd, div_one, pow_succ']
    exact mul_le_mul' (hq i l h) (hgD i l h.ne)
  have hT : Dp ρ s T := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · exact (hTupv i l h).trans (pow_le_pow_right_of_le_one' hρ1' hsj)
    · subst h; rw [hTd, map_zero]; exact zero_le'
    · exact hTlov i l h
  have hρs : ρ ^ s ≤ ρ := by
    calc ρ ^ s ≤ ρ ^ 1 := pow_le_pow_right_of_le_one' hρ1' hs1
      _ = ρ := pow_one ρ
  set P : Matrix (Fin n) (Fin n) F := 1 + T with hP
  have hPd : ∀ i, P i i = 1 := fun i => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_eq, hTd, add_zero]
  have hPo : ∀ i l, i ≠ l → P i l = T i l := fun i l h => by
    rw [hP, Matrix.add_apply, Matrix.one_apply_ne h, zero_add]
  have hPint : ∀ i l, valuation F (P i l) ≤ 1 := fun i l => by
    by_cases h : i = l
    · subst h; rw [hPd, map_one]
    · rw [hPo i l h]; exact (hT i l).trans (hρs.trans hρ1')
  have hPlow : ∀ i l, l < i → valuation F (P i l) < 1 := fun i l h => by
    rw [hPo i l h.ne']
    exact lt_of_le_of_lt ((hT i l).trans hρs) hρ1
  have hPdet : valuation F P.det = 1 := by
    have h1 := val_det_sub_prod_lt P hPint hPlow
    rw [Finset.prod_congr rfl fun i _ => hPd i, Finset.prod_const_one] at h1
    have := Valuation.map_eq_of_sub_lt (valuation F) (x := (1 : F)) (y := P.det) (by rwa [map_one])
    rwa [map_one] at this
  have hPne : P.det ≠ 0 := fun h => by
    rw [h, map_zero] at hPdet
    exact zero_ne_one hPdet
  let p : GL (Fin n) F := Matrix.GeneralLinearGroup.mkOfDetNeZero P hPne
  have hpv : (p : Matrix (Fin n) (Fin n) F) = P := rfl
  have hpI : p ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := ⟨mem_unitGL_of p hPint hPdet, hPlow⟩
  have hpU : p ∈ U := by
    rw [← SetLike.mem_coe, hU]
    exact hpI
  have hxinv : ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) =
      Matrix.diagonal fun i => (e i)⁻¹ := by
    rw [Matrix.coe_units_inv, hx]
    refine Matrix.inv_eq_left_inv ?_
    rw [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext i
    exact inv_mul_cancel₀ (he i)
  let q : GL (Fin n) F := x⁻¹ * p * x
  set Q : Matrix (Fin n) (Fin n) F := (q : Matrix (Fin n) (Fin n) F) with hQdef
  have hQ : ∀ i l, Q i l = (e i)⁻¹ * P i l * e l := fun i l => by
    show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) i l = _
    rw [Units.val_mul, Units.val_mul, hxinv, hx, hpv, Matrix.mul_diagonal, Matrix.diagonal_mul]
  have hQd : ∀ i, Q i i = 1 := fun i => by
    rw [hQ, hPd, mul_one, inv_mul_cancel₀ (he i)]
  have hQup : ∀ i l, i < l → Q i l = C i l / d l := fun i l h => by
    rw [hQ, hPo i l h.ne, hTup i l h]
    have h1 := he i
    have h2 := he l
    field_simp
  have hQlow : ∀ i l, l < i → valuation F (Q i l) ≤ ρ * ρ ^ s := fun i l h => by
    rw [hQ, hPo i l h.ne', show (e i)⁻¹ * T i l * e l = (e l / e i) * T i l by
      rw [div_eq_mul_inv]; ring, map_mul]
    exact mul_le_mul' (hq l i h) (hTlov i l h)
  have hQint : ∀ i l, valuation F (Q i l) ≤ 1 := fun i l => by
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, map_div₀, hd, div_one]
      exact mem_unitGL_entries hI.1 i l
    · subst h; rw [hQd, map_one]
    · refine (hQlow i l h).trans ?_
      calc ρ * ρ ^ s ≤ 1 * 1 := mul_le_mul' hρ1' (hρs.trans hρ1')
        _ = 1 := one_mul 1
  have hQdet : valuation F Q.det = 1 := by
    have : Q.det = P.det := by
      show ((x⁻¹ * p * x : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = _
      rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hpv]
      have h3 : (x : Matrix (Fin n) (Fin n) F).det * ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det = 1 := by
        rw [← Matrix.det_mul, ← Units.val_mul, mul_inv_cancel]
        simp
      calc _ = P.det * ((x : Matrix (Fin n) (Fin n) F).det *
            ((x⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F).det) := by ring
        _ = P.det := by rw [h3, mul_one]
    rw [this]; exact hPdet
  have hqU : q ∈ U := by
    have : q ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := ⟨mem_unitGL_of q hQint hQdet, fun i l h =>
      lt_of_le_of_lt (hQlow i l h) (lt_of_le_of_lt (mul_le_mul' le_rfl hρs) (by
        calc ρ * ρ ≤ ρ * 1 := mul_le_mul' le_rfl hρ1'
          _ = ρ := mul_one ρ
          _ < 1 := hρ1 |>.trans_le le_rfl))⟩
    rw [← SetLike.mem_coe, hU]
    exact this

  let T' : Matrix (Fin n) (Fin n) F := fun i l => - (sg F i l * c (T l.rev i.rev))
  have hT'v : ∀ i l, valuation F (T' i l) = valuation F (T l.rev i.rev) := fun i l => by
    show valuation F (- (sg F i l * c (T l.rev i.rev))) = _
    rw [Valuation.map_neg, map_mul, hsgv, one_mul, hcv]
  have hT' : Dp ρ s T' := fun i l => by
    rw [hT'v]; exact hT _ _
  have hT'd : ∀ i, T' i i = 0 := fun i => by
    show - (sg F i i * c (T i.rev i.rev)) = 0
    rw [hTd, map_zero, mul_zero, neg_zero]
  have hT'lo : ∀ i l, l < i → T' i l = - (C i l / d i) := fun i l h => by
    show - (sg F i l * c (T l.rev i.rev)) = _
    rw [hTlo _ _ (Fin.rev_lt_rev.2 h), Fin.rev_rev, Fin.rev_rev, map_mul, map_sg, hcc, ← mul_assoc,
      sg_mul_self, one_mul]
  have hT'up : ∀ i l, i < l → valuation F (T' i l) ≤ ρ ^ (j + 1) := fun i l h => by
    rw [hT'v]
    exact hTupv _ _ (Fin.rev_lt_rev.2 h)
  have hp0 : Dp ρ 0 ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
    rw [pow_zero]
    have : p⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
      rw [← hU]; exact U.inv_mem hpU
    exact mem_unitGL_entries this.1 a b
  let W : Matrix (Fin n) (Fin n) F := T * T * ((p⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F)
  have hW : Dp ρ (s + s + 0) W := (hT.mul hT).mul hp0
  let D : Matrix (Fin n) (Fin n) F := fun i l => sg F i l * c (W l.rev i.rev)
  have hD : Dp ρ (s + s + 0) D := fun i l => by
    show valuation F (sg F i l * c (W l.rev i.rev)) ≤ _
    rw [map_mul, hsgv, one_mul, hcv]
    exact hW _ _
  have hθ : ((GlobalTheory.CuspRep.thetaGL n c p : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) = 1 + T' + D := by
    ext i l
    rw [theta_expand c p T hpv i l, Matrix.add_apply, Matrix.add_apply]
    show _ = (1 : Matrix (Fin n) (Fin n) F) i l + - (sg F i l * c (T l.rev i.rev)) +
      sg F i l * c (W l.rev i.rev)
    rw [sub_eq_add_neg]
  let Dg : Matrix (Fin n) (Fin n) F := Matrix.diagonal d
  let Co : Matrix (Fin n) (Fin n) F := C - Dg
  have hC0 : Dp ρ 0 C := fun a b => by
    rw [pow_zero]
    exact mem_unitGL_entries hI.1 a b
  have hCo : Dp ρ j Co := fun i l => by
    by_cases h : i = l
    · subst h
      show valuation F (C i i - Dg i i) ≤ _
      rw [show Dg i i = C i i from Matrix.diagonal_apply_eq _ _, sub_self, map_zero]
      exact zero_le'
    · show valuation F (C i l - Dg i l) ≤ _
      rw [show Dg i l = 0 from Matrix.diagonal_apply_ne _ h, sub_zero]
      exact hgD i l h
  let B : Matrix (Fin n) (Fin n) F := C + Dg * T' - Q * Dg
  have hBe : ∀ i l, B i l = C i l + d i * T' i l - Q i l * d l := fun i l => by
    show (C + Dg * T' - Q * Dg) i l = _
    rw [Matrix.sub_apply, Matrix.add_apply, Matrix.diagonal_mul, Matrix.mul_diagonal]
  have hB : Dp ρ (j + 1) B := fun i l => by
    rw [hBe]
    rcases lt_trichotomy i l with h | h | h
    · rw [hQup i l h, div_mul_cancel₀ _ (hd0 l), add_sub_cancel_left, map_mul, hd, one_mul]
      exact hT'up i l h
    · subst h
      rw [hT'd, hQd, mul_zero, add_zero, one_mul]
      show valuation F (C i i - C i i) ≤ _
      rw [sub_self, map_zero]
      exact zero_le'
    · rw [hT'lo i l h, mul_neg, mul_div_cancel₀ _ (hd0 i),
        add_neg_cancel, zero_sub, Valuation.map_neg, map_mul, hd, mul_one]
      refine (hQlow i l h).trans ?_
      rw [← pow_succ']
      exact pow_le_pow_right_of_le_one' hρ1' (Nat.succ_le_succ hjs)
  let R : Matrix (Fin n) (Fin n) F := B + Co * T' + C * D
  have hR : Dp ρ (j + 1) R :=
    (hB.add ((hCo.mul hT').mono hρ1' (Nat.add_le_add_left hs1 j))).add
      ((hC0.mul hD).mono hρ1' (by omega))
  have hid : C * (1 + T' + D) = Q * Dg + R := by
    show C * (1 + T' + D) = Q * Dg + (C + Dg * T' - Q * Dg + (C - Dg) * T' + C * D)
    noncomm_ring
  have hw : x⁻¹ * p⁻¹ * x * g * GlobalTheory.CuspRep.thetaGL n c p =
      q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p) := by
    show _ = (x⁻¹ * p * x)⁻¹ * _
    group
  refine ⟨p, hpU, ?_, ?_⟩
  · rw [hw]
    exact U.mul_mem (U.inv_mem hqU) (U.mul_mem hgU (hθU p hpU))
  · intro i l hil
    rw [hw]
    have hval : ((q⁻¹ * (g * GlobalTheory.CuspRep.thetaGL n c p) : GL (Fin n) F) :
        Matrix (Fin n) (Fin n) F) = Dg + ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * R := by
      rw [Units.val_mul, Units.val_mul, hθ]
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (C * (1 + T' + D)) = _
      rw [hid, mul_add, ← mul_assoc]
      congr 1
      show ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) * (q : Matrix (Fin n) (Fin n) F) * Dg = Dg
      rw [← Units.val_mul, inv_mul_cancel]
      simp
    rw [hval, Matrix.add_apply, show Dg i l = 0 from Matrix.diagonal_apply_ne _ hil, zero_add]
    have hq0 : Dp ρ 0 ((q⁻¹ : GL (Fin n) F) : Matrix (Fin n) (Fin n) F) := fun a b => by
      rw [pow_zero]
      have : q⁻¹ ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
        rw [← hU]; exact U.inv_mem hqU
      exact mem_unitGL_entries this.1 a b
    have := (hq0.mul hR) i l
    rwa [zero_add] at this

end Step

section Main

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]
  {n : ℕ}

/- English proof (translation)
Establish `hUI : ∀ g, g ∈ U ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := fun g => by`. Rewrite using `[← hU]`. Both sides reduce to the same expression. Set `f : GL (Fin n) F → GL (Fin n) F` to `fun m => x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m`. Establish `hf : Continuous f` using `((continuous_const.mul continuous_inv).mul continuous_const).mul (GlobalTheory.ThetaPull.continuous_thetaGL c hcont)`.

Set `S : ℕ → Set (GL (Fin n) F)` to `fun j => {m | m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧ f m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧ ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}`. Establish `hclosedI : IsClosed (PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F) := hcpt.isClosed`. Establish `hSc : ∀ j, IsClosed (S j)` using `fun j => by`. Establish `h1 : IsClosed {m : GL (Fin n) F | ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}`. Simplify using `only [Set.setOf_forall]`.

Use `isClosed_iInter fun i => isClosed_iInter fun l => isClosed_iInter fun _ => ?_` and prove the remaining obligations. Establish `hcont : Continuous fun m : GL (Fin n) F => (f m : Matrix (Fin n) (Fin n) F) i l` using `(Units.continuous_val.comp hf).matrix_elem i l`. Conclude with `(IsNonarchimedeanLocalField.isCompact_closedBall F (ρ ^ j)).isClosed.preimage hcont`. Conclude with `hclosedI.inter ((hclosedI.preimage hf).inter h1)`. Establish `hSn : ∀ j, (S j).Nonempty`.

Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Take `⟨a, ha, b, hb, rfl⟩` from `hδ`. Establish `hfa : f a = b * GlobalTheory.CuspRep.thetaGL n c a` using `by show x⁻¹ * a⁻¹ * (a * x * b) * _ = _ group`.

Establish `hfaI : f a ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) F := by`. Rewrite using `[hfa, ← hUI]`. Conclude with `U.mul_mem ((hUI _).2 hb) (hθU _ ((hUI _).2 ha))`. Use `⟨a, ha, hfaI, fun i l _ => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_zero]`.

Conclude with `mem_unitGL_entries hfaI.1 i l`. Consider the case `succ j ih`. Take `⟨m, hm, hfm, hD⟩` from `ih`. Take `⟨p, hp, hcU, hcD⟩` from `step U hU c hcv hcc hθU ρ hρ1 hunif e he hc x hx j (f m) ((hUI _).2 hfm) hD`. Establish `hfmp : f (m * p) = x⁻¹ * p⁻¹ * x * f m * GlobalTheory.CuspRep.thetaGL n c p` using `by show x⁻¹ * (m * p)⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c (m * p) = x⁻¹ * p⁻¹ * x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m) * _`.

Rewrite using `[map_mul]`. Use `group`. Use `⟨m * p, (hUI _).1 (U.mul_mem ((hUI _).2 hm) hp), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hfmp]`. Conclude with `(hUI _).1 hcU`.

Rewrite using `[hfmp]`. Conclude with `hcD`. Establish `hSd : ∀ j, S (j + 1) ⊆ S j` using `fun j m hm => ⟨hm.1, hm.2.1, fun i l h => (hm.2.2 i l h).trans (pow_le_pow_right_of_le_one' hρ1.le (Nat.le_succ j))⟩`. Establish `hS0 : IsCompact (S 0)` using `hcpt.of_isClosed_subset (hSc 0) fun m hm => hm.1`. Take `⟨m, hm⟩` from `IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn hS0 hSc`.

Establish `hm' : ∀ j, m ∈ S j` using `Set.mem_iInter.1 hm`. Establish `: MulArchimedean (ValueGroupWithZero F)` using `ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance`. Use `⟨m, (hm' 0).1, f m, (hm' 0).2.1, fun i l hil => ?_, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`. Establish `hv : valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≠ 0` using `(Valuation.ne_zero_iff _).2 h0`.

Take `⟨j, hj⟩` from `exists_pow_lt₀ hρ1 (Units.mk0 _ hv)`. Conclude with `absurd ((hm' j).2.2 i l hil) (not_le.2 hj)`. Use `show _ = x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m) group`.
-/
theorem contraction (U : Subgroup (GL (Fin n) F))
    (hU : (U : Set (GL (Fin n) F)) = PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F)
    (hcpt : IsCompact (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F))
    (c : F →+* F) (hcc : ∀ a, c (c a) = a) (hcv : ∀ a, valuation F (c a) = valuation F a)
    (hcont : Continuous c) (hθU : ∀ g ∈ U, GlobalTheory.CuspRep.thetaGL n c g ∈ U)
    (ρ : ValueGroupWithZero F) (hρ1 : ρ < 1)
    (hunif : ∀ a : F, valuation F a < 1 → valuation F a ≤ ρ)
    (e : Fin n → F) (he : ∀ i, e i ≠ 0)
    (hc : ∀ i l, i < l → valuation F (e i) ≤ ρ * valuation F (e l))
    (x : GL (Fin n) F) (hx : (x : Matrix (Fin n) (Fin n) F) = Matrix.diagonal e)
    (δ : GL (Fin n) F) (hδ : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble F x) :
    ∃ m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F, ∃ t ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F,
      (∀ i l, i ≠ l → (t : Matrix (Fin n) (Fin n) F) i l = 0) ∧
      m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m = x * t := by
  have hUI : ∀ g, g ∈ U ↔ g ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := fun g => by
    rw [← hU]; rfl
  let f : GL (Fin n) F → GL (Fin n) F := fun m =>
    x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m
  have hf : Continuous f :=
    ((continuous_const.mul continuous_inv).mul continuous_const).mul
      (GlobalTheory.ThetaPull.continuous_thetaGL c hcont)
  let S : ℕ → Set (GL (Fin n) F) := fun j =>
    {m | m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧ f m ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F ∧
      ∀ i l, i ≠ l → valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j}
  have hclosedI : IsClosed (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F) := hcpt.isClosed
  have hSc : ∀ j, IsClosed (S j) := fun j => by
    have h1 : IsClosed {m : GL (Fin n) F | ∀ i l, i ≠ l →
        valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≤ ρ ^ j} := by
      simp only [Set.setOf_forall]
      refine isClosed_iInter fun i => isClosed_iInter fun l => isClosed_iInter fun _ => ?_
      have hcont : Continuous fun m : GL (Fin n) F => (f m : Matrix (Fin n) (Fin n) F) i l :=
        (Units.continuous_val.comp hf).matrix_elem i l
      exact (IsNonarchimedeanLocalField.isCompact_closedBall F (ρ ^ j)).isClosed.preimage hcont
    exact hclosedI.inter ((hclosedI.preimage hf).inter h1)
  have hSn : ∀ j, (S j).Nonempty := by
    intro j
    induction j with
    | zero =>
      obtain ⟨a, ha, b, hb, rfl⟩ := hδ
      have hfa : f a = b * GlobalTheory.CuspRep.thetaGL n c a := by
        show x⁻¹ * a⁻¹ * (a * x * b) * _ = _
        group
      have hfaI : f a ∈ PositivityTheory.Rg.Tf.Loc.iwahori (m := n) F := by
        rw [hfa, ← hUI]
        exact U.mul_mem ((hUI _).2 hb) (hθU _ ((hUI _).2 ha))
      refine ⟨a, ha, hfaI, fun i l _ => ?_⟩
      rw [pow_zero]
      exact mem_unitGL_entries hfaI.1 i l
    | succ j ih =>
      obtain ⟨m, hm, hfm, hD⟩ := ih
      obtain ⟨p, hp, hcU, hcD⟩ := step U hU c hcv hcc hθU ρ hρ1 hunif e he hc x hx j (f m)
        ((hUI _).2 hfm) hD
      have hfmp : f (m * p) = x⁻¹ * p⁻¹ * x * f m * GlobalTheory.CuspRep.thetaGL n c p := by
        show x⁻¹ * (m * p)⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c (m * p) =
          x⁻¹ * p⁻¹ * x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m) * _
        rw [map_mul]
        group
      refine ⟨m * p, (hUI _).1 (U.mul_mem ((hUI _).2 hm) hp), ?_, ?_⟩
      · rw [hfmp]; exact (hUI _).1 hcU
      · rw [hfmp]; exact hcD
  have hSd : ∀ j, S (j + 1) ⊆ S j := fun j m hm => ⟨hm.1, hm.2.1, fun i l h =>
    (hm.2.2 i l h).trans (pow_le_pow_right_of_le_one' hρ1.le (Nat.le_succ j))⟩
  have hS0 : IsCompact (S 0) := hcpt.of_isClosed_subset (hSc 0) fun m hm => hm.1
  obtain ⟨m, hm⟩ := IsCompact.nonempty_iInter_of_sequence_nonempty_isCompact_isClosed S hSd hSn hS0 hSc
  have hm' : ∀ j, m ∈ S j := Set.mem_iInter.1 hm
  have : MulArchimedean (ValueGroupWithZero F) :=
    ValuativeRel.isRankLeOne_iff_mulArchimedean.mp inferInstance
  refine ⟨m, (hm' 0).1, f m, (hm' 0).2.1, fun i l hil => ?_, ?_⟩
  · by_contra h0
    have hv : valuation F ((f m : Matrix (Fin n) (Fin n) F) i l) ≠ 0 := (Valuation.ne_zero_iff _).2 h0
    obtain ⟨j, hj⟩ := exists_pow_lt₀ hρ1 (Units.mk0 _ hv)
    exact absurd ((hm' j).2.2 i l hil) (not_le.2 hj)
  · show _ = x * (x⁻¹ * m⁻¹ * δ * GlobalTheory.CuspRep.thetaGL n c m)
    group

end Main

section Local

open NumberField IsDedekindDomain GlobalTheory.BCT GlobalTheory.UnitaryBC Formalism.UG
open scoped Classical

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Establish `hsg : ∀ i l : Fin n, Valued.v ((-1 : w.adicCompletion E) ^ ((i : ℕ) + l)) = 1` using `fun i l => by`. Rewrite using `[map_pow, Valuation.map_neg, map_one, one_pow]`. Take `⟨h1, h2, h3⟩` from `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg`. Take `⟨-, -, h4⟩` from `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g⁻¹).1.1 (inv_mem hg)`. Use `(GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨fun i l => ?_, fun i l => ?_, fun i l h => ?_⟩` and prove the remaining obligations.

Rewrite using `[GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]`. Conclude with `h2 _ _`. Rewrite using `[← map_inv, GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv, inv_inv]`. Conclude with `h1 _ _`. Rewrite using `[GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]`.

Conclude with `h4 _ _ (Fin.rev_lt_rev.2 h)`.
-/
theorem thetaGL_mem_iwGL {w : Pl E} (c : w.adicCompletion E →+* w.adicCompletion E)
    (hcv : ∀ x, Valued.v (c x) = Valued.v x) (n : ℕ) (g : GLw n w) (hg : g ∈ iwGL n w) :
    GlobalTheory.CuspRep.thetaGL n c g ∈ iwGL n w := by
  have hsg : ∀ i l : Fin n, Valued.v ((-1 : w.adicCompletion E) ^ ((i : ℕ) + l)) = 1 := fun i l => by
    rw [map_pow, Valuation.map_neg, map_one, one_pow]
  obtain ⟨h1, h2, h3⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g).1.1 hg
  obtain ⟨-, -, h4⟩ := (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n g⁻¹).1.1 (inv_mem hg)
  refine (GlobalTheory.CompanionTheory.IwEntries.iwGL_KGL_entries E w n _).1.2 ⟨fun i l => ?_, fun i l => ?_, fun i l h => ?_⟩
  · rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]
    exact h2 _ _
  · rw [← map_inv, GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv, inv_inv]
    exact h1 _ _
  · rw [GlobalTheory.ThetaPull.thetaGL_apply, map_mul, hsg, one_mul, hcv]
    exact h4 _ _ (Fin.rev_lt_rev.2 h)

/- English proof (translation)
Introduce `E _ _ _ hU w hw ϖ hϖ n y hy δ hδ`. Take `⟨hcont, hcc, hcv, -⟩` from `GlobalTheory.T.placeConjugation_properties_cmField E hU w`. Establish `hθ : GlobalTheory.BCT.thL n w = GlobalTheory.CuspRep.thetaGL n (GlobalTheory.BCT.cj w)` using `if_neg hw`. Establish `hEq : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))`. Establish `: (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible` using `Valuation.Compatible.ofValuation _`.

Conclude with `ValuativeRel.isEquiv _ _`. Establish `hvF : ∀ a, valuation (w.adicCompletion E) (GlobalTheory.BCT.cj w a) = valuation (w.adicCompletion E) a` using `fun a => le_antisymm ((hEq _ _).2 (hcv a).le) ((hEq _ _).2 (hcv a).ge)`. Establish `hIU : ((GlobalTheory.BCT.iwGL n w : Subgroup _) : Set (GlobalTheory.BCT.GLw n w)) = PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) (w.adicCompletion E) := by`. Use extensionality with `g`. Conclude with `(GlobalTheory.CompanionTheory.IwContract.mem_iwahori_iff).symm`.

Establish `hcpt : IsCompact (PositivityTheory.Rg.Tf.Loc.iwahori (m` using `n) (w.adicCompletion E)) := by`. Rewrite using `[← hIU]`. Conclude with `GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _`. Take `⟨u, hu⟩` from `WithZero.ne_zero_iff_exists.1 ((Valuation.ne_zero_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).2 ϖ.ne_zero)`. Establish `hu1 : Multiplicative.toAdd u = -1`.

Use `hϖ.1` as an intermediate fact. Rewrite `this` using `[GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm]`. Use linear arithmetic over natural numbers and integers. Establish `hρ1 : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1`. Use `(GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 ?_` and prove the remaining obligations.

Rewrite using `[← hu, ← WithZero.coe_one, WithZero.coe_lt_coe]`. Express the relevant statement in the definitionally equal form `Multiplicative.toAdd u < 0`. Use linear arithmetic over natural numbers and integers. Establish `hunif : ∀ a : w.adicCompletion E, valuation (w.adicCompletion E) a < 1 → valuation (w.adicCompletion E) a ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E)`. Introduce `a ha`.

Establish `ha'` using `(GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w a).1 ha`. Use `(hEq _ _).2 ?_` and prove the remaining obligations. Distinguish the cases in `h0 : Valued.v a = 0`. Rewrite using `[h0]`. Conclude with `zero_le'`.

Take `⟨b, hb⟩` from `WithZero.ne_zero_iff_exists.1 h0`. Rewrite `ha'` using `[← hb, ← WithZero.coe_one, WithZero.coe_lt_coe]`. Rewrite using `[← hb, ← hu, WithZero.coe_le_coe]`. Express the relevant statement in the definitionally equal form `Multiplicative.toAdd b < 0 at ha'`. Express the relevant statement in the definitionally equal form `Multiplicative.toAdd b ≤ Multiplicative.toAdd u`.

Use linear arithmetic over natural numbers and integers. Set `e : Fin n → w.adicCompletion E` to `fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)`. Establish `he : ∀ i, e i ≠ 0` using `fun i => Units.ne_zero _`. Establish `hc : ∀ i l, i < l → valuation (w.adicCompletion E) (e i) ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) * valuation (w.adicCompletion E) (e l)`. Introduce `i l h`.

Take `⟨b, hb⟩` from `Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)`. Establish `hyi : y i = y l + ((b + 1 : ℕ) : ℤ)` using `by push_cast; omega`. Establish `hei : e i = e l * (ϖ : w.adicCompletion E) ^ (b + 1)` using `by show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) = ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _`. Rewrite using `[hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]`. Rewrite using `[hei, map_mul, map_pow, mul_comm]`.

Use `mul_le_mul' ?_ le_rfl` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Establish `hx : ((GlobalTheory.BCT.tdiag ϖ y : GlobalTheory.BCT.GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) = Matrix.diagonal e`. Rewrite using `[GlobalTheory.BCT.tdiag, GlobalTheory.SmGL.val_diagT]`. Establish `hδ' : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (GlobalTheory.BCT.tdiag ϖ y)`.

Establish `h : ∃ x ∈ GlobalTheory.BCT.iwGL n w, ∃ z ∈ GlobalTheory.BCT.iwGL n w, δ = x * GlobalTheory.BCT.tdiag ϖ y * z`. Assume the negation of the conclusion as `h`. Conclude with `hδ (if_neg h)`. Take `⟨a, ha, b, hb, e'⟩` from `h`. Conclude with `⟨a, by rw [← hIU]; exact ha, b, by rw [← hIU]; exact hb, e'⟩`.

Take `⟨m, hm, t, ht, hoff, h⟩` from `contraction (GlobalTheory.BCT.iwGL n w) hIU hcpt (GlobalTheory.BCT.cj w) hcc hvF hcont (fun g hg => thetaGL_mem_iwGL _ hcv n g hg) _ hρ1 hunif e he hc _ hx δ hδ'`. Use `⟨m, by rw [← SetLike.mem_coe, hIU]; exact hm, t, ⟨hoff, fun i => ?_⟩, by rw [hθ]; exact h⟩` and prove the remaining obligations. Conclude with `hEq.eq_one_iff_eq_one.1 (val_diag_of_mem_iwahori ht i)`.
-/
theorem contr_tw : PositivityTheory.Rg.Bc.ArchbcB.B.M4.Tw.P_contr_tw := by
  intro E _ _ _ hU w hw ϖ hϖ n y hy δ hδ
  obtain ⟨hcont, hcc, hcv, -⟩ := GlobalTheory.T.placeConjugation_properties_cmField E hU w
  have hθ : GlobalTheory.BCT.thL n w = GlobalTheory.CuspRep.thetaGL n (GlobalTheory.BCT.cj w) := if_neg hw
  have hEq : (ValuativeRel.valuation (w.adicCompletion E)).IsEquiv
      (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))) := by
    have : (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ))).Compatible :=
      Valuation.Compatible.ofValuation _
    exact ValuativeRel.isEquiv _ _
  have hvF : ∀ a, valuation (w.adicCompletion E) (GlobalTheory.BCT.cj w a) = valuation (w.adicCompletion E) a :=
    fun a => le_antisymm ((hEq _ _).2 (hcv a).le) ((hEq _ _).2 (hcv a).ge)
  have hIU : ((GlobalTheory.BCT.iwGL n w : Subgroup _) : Set (GlobalTheory.BCT.GLw n w)) =
      PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E) := by
    ext g
    exact (GlobalTheory.CompanionTheory.IwContract.mem_iwahori_iff).symm
  have hcpt : IsCompact (PositivityTheory.Rg.Tf.Loc.iwahori (m := n) (w.adicCompletion E)) := by
    rw [← hIU]
    exact GlobalTheory.SmGL.IwahoriOnto.isCompact_iwahori _ _
  obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1
    ((Valuation.ne_zero_iff (Valued.v : Valuation (w.adicCompletion E) (WithZero (Multiplicative ℤ)))).2 ϖ.ne_zero)
  have hu1 : Multiplicative.toAdd u = -1 := by
    have := hϖ.1
    rw [GlobalTheory.CompanionTheory.UnitaryCorrection.ordL_of_eq hu.symm] at this
    omega
  have hρ1 : valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) < 1 := by
    refine (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w _).2 ?_
    rw [← hu, ← WithZero.coe_one, WithZero.coe_lt_coe]
    change Multiplicative.toAdd u < 0
    omega
  have hunif : ∀ a : w.adicCompletion E, valuation (w.adicCompletion E) a < 1 →
      valuation (w.adicCompletion E) a ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) := by
    intro a ha
    have ha' := (GlobalTheory.CompanionTheory.IwEntries.rel_lt_one_iff w a).1 ha
    refine (hEq _ _).2 ?_
    by_cases h0 : Valued.v a = 0
    · rw [h0]; exact zero_le'
    · obtain ⟨b, hb⟩ := WithZero.ne_zero_iff_exists.1 h0
      rw [← hb, ← WithZero.coe_one, WithZero.coe_lt_coe] at ha'
      rw [← hb, ← hu, WithZero.coe_le_coe]
      change Multiplicative.toAdd b < 0 at ha'
      change Multiplicative.toAdd b ≤ Multiplicative.toAdd u
      omega
  let e : Fin n → w.adicCompletion E := fun i => ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E)
  have he : ∀ i, e i ≠ 0 := fun i => Units.ne_zero _
  have hc : ∀ i l, i < l → valuation (w.adicCompletion E) (e i) ≤
      valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) * valuation (w.adicCompletion E) (e l) := by
    intro i l h
    obtain ⟨b, hb⟩ := Int.eq_ofNat_of_zero_le (show 0 ≤ y i - y l - 1 by have := hy h; omega)
    have hyi : y i = y l + ((b + 1 : ℕ) : ℤ) := by push_cast; omega
    have hei : e i = e l * (ϖ : w.adicCompletion E) ^ (b + 1) := by
      show ((ϖ ^ y i : (w.adicCompletion E)ˣ) : w.adicCompletion E) =
        ((ϖ ^ y l : (w.adicCompletion E)ˣ) : w.adicCompletion E) * _
      rw [hyi, _root_.zpow_add, Units.val_mul, zpow_natCast, Units.val_pow_eq_pow_val]
    rw [hei, map_mul, map_pow, mul_comm]
    refine mul_le_mul' ?_ le_rfl
    calc valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ (b + 1)
        ≤ valuation (w.adicCompletion E) (ϖ : w.adicCompletion E) ^ 1 :=
          pow_le_pow_right_of_le_one' hρ1.le (Nat.succ_le_succ (Nat.zero_le b))
      _ = _ := pow_one _
  have hx : ((GlobalTheory.BCT.tdiag ϖ y : GlobalTheory.BCT.GLw n w) : Matrix (Fin n) (Fin n) (w.adicCompletion E)) =
      Matrix.diagonal e := by
    rw [GlobalTheory.BCT.tdiag, GlobalTheory.SmGL.val_diagT]
  have hδ' : δ ∈ PositivityTheory.Rg.Tf.Loc.iwDouble (w.adicCompletion E) (GlobalTheory.BCT.tdiag ϖ y) := by
    have h : ∃ x ∈ GlobalTheory.BCT.iwGL n w, ∃ z ∈ GlobalTheory.BCT.iwGL n w, δ = x * GlobalTheory.BCT.tdiag ϖ y * z := by
      by_contra h
      exact hδ (if_neg h)
    obtain ⟨a, ha, b, hb, e'⟩ := h
    exact ⟨a, by rw [← hIU]; exact ha, b, by rw [← hIU]; exact hb, e'⟩
  obtain ⟨m, hm, t, ht, hoff, h⟩ := contraction (GlobalTheory.BCT.iwGL n w) hIU hcpt (GlobalTheory.BCT.cj w) hcc hvF hcont
    (fun g hg => thetaGL_mem_iwGL _ hcv n g hg) _ hρ1 hunif e he hc _ hx δ hδ'
  refine ⟨m, by rw [← SetLike.mem_coe, hIU]; exact hm, t, ⟨hoff, fun i => ?_⟩, by rw [hθ]; exact h⟩
  exact hEq.eq_one_iff_eq_one.1 (val_diag_of_mem_iwahori ht i)

end Local

end GlobalTheory.CompanionTheory.ThetaContraction
