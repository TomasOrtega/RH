import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.UnderTie
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.XiEntryInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ChartPointRightTranslateByLevelCoupledStep
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IntegralAtOfAdelicIntegralAt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.XiAtCongInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.MemIntegralGLPrincipalCongruenceOfColsCong
import Formalism.LocalToGlobal.Columns.QthExistsBound
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.Ker Formalism.L2.DIV GlobalTheory.TwU GlobalTheory.TwV
open scoped TensorProduct
open GlobalTheory.TopStep

noncomputable section

namespace GlobalTheory.LevFrames

open Matrix

section Core

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {N : ℕ}

/- English proof (translation)
Use `GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) h` as an intermediate fact. Simplify using `using this`.
-/
theorem intAtA_neg' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) :
    IntAtA (F := F) P (-a) := by
  have := GlobalTheory.CplPt.intAtA_mul (GlobalTheory.CplPt.intAtA_int (F := F) (P := P) (-1)) h
  simpa using this

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1`. Consider the case `succ m ih => rw [pow_succ]`. Conclude with `GlobalTheory.CplPt.intAtA_mul ih h`.
-/
theorem intAtA_pow' (P : HeightOneSpectrum (𝓞 E)) {a : E ⊗[F] FiniteAdeleRing (𝓞 F) F} (h : IntAtA (F := F) P a) (m : ℕ) :
    IntAtA (F := F) P (a ^ m) := by
  induction m with
  | zero => simpa using GlobalTheory.CplPt.intAtA_int (F := F) (P := P) 1
  | succ m ih => rw [pow_succ]; exact GlobalTheory.CplPt.intAtA_mul ih h

/- English proof (translation)
Establish `hq : ((qOf Q : ℕ) : E) ≠ 0`. Establish `: qOf Q ≠ 0` using `fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)`. Conclude with `this` after adjusting the coercions. Use `set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi`. Use `set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd`.

Establish `hdq : d * qi = 1`. Rewrite using `[hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]`. Establish `hd : IntAtA (F` using `F) Q d := by`. Use `GlobalTheory.CplPt.intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)` as an intermediate fact. Simplify `this` using `[hdd]`.

Use `set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm`. Use `set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm`. Use `set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm`. Use `set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh`. Establish `hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1`.

Rewrite using `[hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]`. Both sides reduce to the same expression. Establish `key : (1 + Am) * (1 + Mh) = 1 + Bm`. Rewrite using `[hMh', hAm, hBm, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul]`. Use `congr 1`.

Rewrite using `[map_mul, map_inv]`. Use `group`. Establish `e1 : Mh = Bm - Am - Am * Mh`. Establish `e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh` using `by noncomm_ring`. Rewrite `e0` using `[key]`.

Conclude with `e0.trans (by noncomm_ring)`. Establish `hA : ∀ i j, IntAtA (F` using `F) Q (qi * Am i j) := fun i j => h i j`. Establish `hB : ∀ i j, IntAtA (F` using `F) Q (qi * Bm i j) := fun i j => h₁ i j`. Establish `step : ∀ m : ℕ, (∀ i j, IntAtA (F` using `F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by`. Introduce `m hm i j`.

Establish `e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) + -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)))`. Establish `es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j)`. Rewrite using `[Finset.mul_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Take the linear combination `(d ^ m * qi * Am i l * Mh l j) * hdq`.

Rewrite using `[es]`. Use `conv_lhs => rw [e1]`. Simplify using `only [Matrix.sub_apply, Matrix.mul_apply (M := Am)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`.

Conclude with `GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hB i j)) (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hA i j)))) (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_sum _ _ fun l _ => GlobalTheory.CplP …`. Establish `desc : ∀ m : ℕ, (∀ i j, IntAtA (F` using `F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => intro hm i j`.

Simplify using `using hm i j`. Consider the case `succ m ih => intro hm`. Conclude with `ih (step m hm)`. Take `⟨J, hJ⟩` from `qth_bound Q Mm`. Establish `hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ)`.

Establish `h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1` using `by rw [pow_one]; exact Ideal.absNorm_mem _`. Use `(Q.intValuation_le_pow_iff_mem _ 1).2 h0` as an intermediate fact. Rewrite `this` using `[← HeightOneSpectrum.valuation_of_algebraMap (K := E)]`. Simplify using `using this`. Establish `hbig : ∀ i j, IntAtA (F` using `F) Q (d ^ (J + 1) * (qi * Mh i j)) := by`.

Introduce `i j`. Establish `e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j)`. Rewrite using `[hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]`. Use `congr 1`. Rewrite using `[pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]`.

Rewrite using `[e]`. Use `GlobalTheory.CplPt.intAtA_of_intAt ((qth_intAt_iff Q _).2 ?_)` and prove the remaining obligations. Rewrite using `[map_mul, map_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]`.

Establish `: (J : ℤ) ≤ (n : ℤ) * J` using `by exact_mod_cast Nat.le_mul_of_pos_left J hn`. Rewrite using `[nsmul_eq_mul]`. Use `push_cast`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hfin` using `desc (J + 1) hbig a b`.

Use `show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)`. Use `GlobalTheory.RatInt.intAt_of_intAtA (F := F) Q _ ?_` and prove the remaining obligations. Establish `e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b` using `by rw [map_mul, hMh, Matrix.map_apply]`. Rewrite using `[e3]`. Conclude with `hfin`.
-/
theorem core [StarRing E] (Q : HeightOneSpectrum (𝓞 E)) (n : ℕ) (hn : 1 ≤ n)
    (y : GL (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F)) (G G₁ : GL (Fin N) E)
    (h : CongAt Q n (y⁻¹ * ratA F G)) (h₁ : CongAt Q n (y⁻¹ * ratA F G₁)) (a b : Fin N) :
    IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * (((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1) a b) := by
  have hq : ((qOf Q : ℕ) : E) ≠ 0 := by
    have : qOf Q ≠ 0 := fun h0 => Q.ne_bot (Ideal.absNorm_eq_zero_iff.1 h0)
    exact_mod_cast this
  set qi := iA F E (((qOf Q : ℕ) : E) ^ n)⁻¹ with hqi
  set d := iA F E (((qOf Q : ℕ) : E) ^ n) with hdd
  have hdq : d * qi = 1 := by
    rw [hqi, hdd, ← map_mul, mul_inv_cancel₀ (pow_ne_zero _ hq), map_one]
  have hd : IntAtA (F := F) Q d := by
    have := GlobalTheory.CplPt.intAtA_int (F := F) (P := Q) (((qOf Q : ℕ) : 𝓞 E) ^ n)
    simpa [hdd] using this
  set Am : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hAm
  set Bm : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := ((y⁻¹ * ratA F G₁ : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 with hBm
  set Mm : Matrix (Fin N) (Fin N) E := ((G⁻¹ * G₁ : GL (Fin N) E) : Matrix (Fin N) (Fin N) E) - 1 with hMm
  set Mh : Matrix (Fin N) (Fin N) (E ⊗[F] FiniteAdeleRing (𝓞 F) F) := Mm.map (iA F E) with hMh
  have hMh' : Mh = ((ratA F (G⁻¹ * G₁) : GL (Fin N) _) : Matrix (Fin N) (Fin N) _) - 1 := by
    rw [hMh, hMm, Matrix.map_sub _ (map_sub _), Matrix.map_one _ (map_zero _) (map_one _)]
    rfl
  have key : (1 + Am) * (1 + Mh) = 1 + Bm := by
    rw [hMh', hAm, hBm, add_sub_cancel, add_sub_cancel, add_sub_cancel, ← Units.val_mul]
    congr 1
    rw [map_mul, map_inv]
    group
  have e1 : Mh = Bm - Am - Am * Mh := by
    have e0 : Mh = (1 + Am) * (1 + Mh) - 1 - Am - Am * Mh := by noncomm_ring
    rw [key] at e0
    exact e0.trans (by noncomm_ring)
  have hA : ∀ i j, IntAtA (F := F) Q (qi * Am i j) := fun i j => h i j
  have hB : ∀ i j, IntAtA (F := F) Q (qi * Bm i j) := fun i j => h₁ i j
  have step : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ (m + 1) * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j)) := by
    intro m hm i j
    have e2 : d ^ m * (qi * Mh i j) = d ^ m * (qi * Bm i j) + -(d ^ m * (qi * Am i j)) +
        -(∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j))) := by
      have es : ∑ l, (qi * Am i l) * (d ^ (m + 1) * (qi * Mh l j)) = d ^ m * (qi * ∑ l, Am i l * Mh l j) := by
        rw [Finset.mul_sum, Finset.mul_sum]
        refine Finset.sum_congr rfl fun l _ => ?_
        linear_combination (d ^ m * qi * Am i l * Mh l j) * hdq
      rw [es]
      conv_lhs => rw [e1]
      simp only [Matrix.sub_apply, Matrix.mul_apply (M := Am)]
      ring
    rw [e2]
    exact GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_add (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hB i j))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_mul (intAtA_pow' Q hd m) (hA i j))))
      (intAtA_neg' Q (GlobalTheory.CplPt.intAtA_sum _ _ fun l _ => GlobalTheory.CplPt.intAtA_mul (hA i l) (hm l j)))
  have desc : ∀ m : ℕ, (∀ i j, IntAtA (F := F) Q (d ^ m * (qi * Mh i j))) → ∀ i j, IntAtA (F := F) Q (qi * Mh i j) := by
    intro m
    induction m with
    | zero => intro hm i j; simpa using hm i j
    | succ m ih => intro hm; exact ih (step m hm)
  obtain ⟨J, hJ⟩ := qth_bound Q Mm
  have hqv : Q.valuation E ((qOf Q : ℕ) : E) ≤ WithZero.exp (-1 : ℤ) := by
    have h0 : ((qOf Q : ℕ) : 𝓞 E) ∈ Q.asIdeal ^ 1 := by rw [pow_one]; exact Ideal.absNorm_mem _
    have := (Q.intValuation_le_pow_iff_mem _ 1).2 h0
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := E)] at this
    simpa using this
  have hbig : ∀ i j, IntAtA (F := F) Q (d ^ (J + 1) * (qi * Mh i j)) := by
    intro i j
    have e : d ^ (J + 1) * (qi * Mh i j) = iA F E (((qOf Q : ℕ) : E) ^ (n * J) * Mm i j) := by
      rw [hMh, Matrix.map_apply, hdd, hqi, ← map_pow, ← map_mul, ← map_mul]
      congr 1
      rw [pow_succ, mul_assoc, mul_inv_cancel_left₀ (pow_ne_zero _ hq), ← pow_mul]
    rw [e]
    refine GlobalTheory.CplPt.intAtA_of_intAt ((qth_intAt_iff Q _).2 ?_)
    rw [map_mul, map_pow]
    calc Q.valuation E ((qOf Q : ℕ) : E) ^ (n * J) * Q.valuation E (Mm i j) ≤ WithZero.exp (-1 : ℤ) ^ (n * J) * WithZero.exp (J : ℤ) :=
          mul_le_mul' (pow_le_pow_left₀ zero_le hqv _) (hJ i j)
      _ ≤ 1 := by
          rw [← WithZero.exp_nsmul, ← WithZero.exp_add, ← WithZero.exp_zero, WithZero.exp_le_exp]
          have : (J : ℤ) ≤ (n : ℤ) * J := by exact_mod_cast Nat.le_mul_of_pos_left J hn
          rw [nsmul_eq_mul]
          push_cast
          linarith
  have hfin := desc (J + 1) hbig a b
  show IntAt Q ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b)
  refine GlobalTheory.RatInt.intAt_of_intAtA (F := F) Q _ ?_
  have e3 : iA F E ((((qOf Q : ℕ) : E) ^ n)⁻¹ * Mm a b) = qi * Mh a b := by rw [map_mul, hMh, Matrix.map_apply]
  rw [e3]
  exact hfin

end Core

section Seam

open Formalism.L2.Ker Formalism.MainNotions

variable {D : D7} {X : Fields} (s : Seam D X)

/- English proof (translation)
Take `⟨r, c, hc, e⟩` from `h`. Use `set f := RingOfIntegers.mapRingEquiv s.iE`. Use `⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩` and prove the remaining obligations. Use `(mem_seamP s P (f.symm c)).2 hm` as an intermediate fact. Rewrite `this` using `[show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c]`. Then use the resulting hypothesis.

Apply `s.iE.injective` to reduce the goal to its premises. Rewrite using `[map_mul]`. Establish `h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w`. Introduce `w`. Establish `h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x)` using `fun x => rfl`.

Rewrite using `[h2, f.apply_symm_apply]`. Rewrite using `[h1, h1, e]`.
-/
theorem intAt_of_seamP (P : HeightOneSpectrum (𝓞 X.E)) (z : X.E) (h : IntAt (seamP s P) (s.iE z)) : IntAt P z := by
  obtain ⟨r, c, hc, e⟩ := h
  set f := RingOfIntegers.mapRingEquiv s.iE
  refine ⟨f.symm r, f.symm c, fun hm => hc ?_, ?_⟩
  · have := (mem_seamP s P (f.symm c)).2 hm
    rwa [show (RingOfIntegers.mapRingEquiv s.iE) (f.symm c) = c from f.apply_symm_apply c] at this
  · apply s.iE.injective
    rw [map_mul]
    have h1 : ∀ w : 𝓞 D.host.E, s.iE (algebraMap (𝓞 X.E) X.E (f.symm w)) = algebraMap (𝓞 D.host.E) D.host.E w := by
      intro w
      have h2 : ∀ x : 𝓞 X.E, s.iE (algebraMap (𝓞 X.E) X.E x) = algebraMap (𝓞 D.host.E) D.host.E (f x) := fun x => rfl
      rw [h2, f.apply_symm_apply]
    rw [h1, h1, e]

end Seam

attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D L hT Gi Gl Kc Y cX ex t u μ St A a j hj β x x₁ κ hx p p₁ hp hp₁ P g hg`. Establish `hD : 1 ≤ (t.cst μ).D P` using `(t.idx_ok μ).cst_ok.D_pos P`. Use `set F₀ := frsF t.sel (t.tup μ) p P with hF₀`. Use `set F₁ := frsF t.sel (t.tup μ) p₁ P with hF₁`. Establish `hX : NearAt (seamP t.seam P.1) ((t.cst μ).D P) ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) * ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))) (seamGL t.seam F₀ * seamGL t.seam g.1)` using `GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) hg (GlobalTheory.CplPt.seamGL_int t.seam g)`.

Establish `e : ratA D.host.F (A.crd j hj) * x₁.1 * ratA D.host.F (A.fb j hj β P) = (ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) * ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P))`. Rewrite using `[hx]`. Use `group`. Establish `hX₁` using `hp₁.frame P`. Rewrite `hX₁` using `[e, ← hF₁]`.

Establish `hc` using `core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ hX hX₁`. Use `set C₀ := g.1⁻¹ * F₀⁻¹ * F₁ with hC₀`. Establish `hM : (seamGL t.seam F₀ * seamGL t.seam g.1)⁻¹ * seamGL t.seam F₁ = seamGL t.seam C₀`. Rewrite using `[hC₀, map_mul, map_mul, map_inv, map_inv, _root_.mul_inv_rev]`. Simplify using `only [hM] at hc`.

Establish `hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ * (C₀ (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N j)) l))`. Introduce `s l`. Establish `hc'` using `hc l s`. Rewrite `hc'` using `[GlobalTheory.TwU.MidIndep.qOf_seamP]`. Use `intAt_of_seamP t.seam P.1 _ ?_` and prove the remaining obligations.

Use `hc' using 1` and compare the differences between its conclusion and the goal. Establish `hm` using `congrFun (seamGL_mulVec t.seam C₀ (Pi.single s 1)) l`. Establish `hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N _)) j)) = Pi.single s (1 : D.host.E)`. Use function extensionality and compare the values at `j`. Rewrite using `[Pi.single_apply, Pi.single_apply]`.

Apply the tactic sequence `split_ifs <;> simp`. Rewrite `hm` using `[hs1, Matrix.mulVec_single_one]`. Rewrite using `[map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]`. Distinguish the cases in `h : l = s`. Substitute `h` using the available equality.

Simplify using `[Matrix.col_apply]`. Simplify using `[h, Matrix.col_apply]`. Take `⟨hk, hpc⟩` from `GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 ((t.cst μ).D P) C₀ hD hcol`. Use `⟨⟨C₀, hk⟩, hpc, fun a' b' => ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `GlobalTheory.CplPt.intAtA_of_intAt (F := D.host.F) (hc a' b')`.

Use `h1 using 2` and compare the differences between its conclusion and the goal. Rewrite using `[map_mul (iA D.host.F D.host.E), Matrix.sub_apply, Matrix.sub_apply, map_sub (iA D.host.F D.host.E), GlobalTheory.CplPt.ratA_apply, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Use `show F₁ = F₀ * (g.1 * C₀)`. Rewrite using `[hC₀]`.

Use `group`.
-/
theorem frames_lev : ∀ {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : G.Inst D L} {Gl : G.LatInst D} {Kc : G.Consts} {Y : DivX D}
    {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {t : KerEntTied ex} {u : D.what₂.Word} {μ : D.what₂.Tup} {St : ChainCharts D u μ}
    (A : AdData t u μ St) (a : 𝓞 D.host.E) (j : ℕ) (hj : j ≤ D.R.m) (β : (St j hj).Ch) (x x₁ : UA D j hj)
    (κ : GL (Fin (D.R.N j)) (D.host.E ⊗[D.host.F] FiniteAdeleRing (𝓞 D.host.F) D.host.F)), x₁.1 = x.1 * κ →
    ∀ (p p₁ : ChPt (R := D.R) t.sel (t.tup μ) (t.word u) j), IsPtAd A a j hj β x p → IsPtAd A a j hj β x₁ p₁ →
    ∀ (P : SB t μ) (g : GLint t.X.E (D.R.N j) P.1), InFrame t.seam (A.fb j hj β) (t.cst μ).D P κ g.1 →
    ∃ C : GLint t.X.E (D.R.N j) P.1, C ∈ GlobalTheory.TopStep.prinCong (D.R.N j) P.1 ((t.cst μ).D P) ∧
      CongAt (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) (ratA D.host.F (seamGL t.seam C.1)) ∧
      frsF t.sel (t.tup μ) p₁ P = frsF t.sel (t.tup μ) p P * (g * C).1 := by
  intro D L hT Gi Gl Kc Y cX ex t u μ St A a j hj β x x₁ κ hx p p₁ hp hp₁ P g hg
  have hD : 1 ≤ (t.cst μ).D P := (t.idx_ok μ).cst_ok.D_pos P
  set F₀ := frsF t.sel (t.tup μ) p P with hF₀
  set F₁ := frsF t.sel (t.tup μ) p₁ P with hF₁
  have hX : NearAt (seamP t.seam P.1) ((t.cst μ).D P)
      ((ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)))
      (seamGL t.seam F₀ * seamGL t.seam g.1) :=
    GlobalTheory.CplPt.nearAt_mul_int _ (hp.frame P) hg (GlobalTheory.CplPt.seamGL_int t.seam g)
  have e : ratA D.host.F (A.crd j hj) * x₁.1 * ratA D.host.F (A.fb j hj β P) =
      (ratA D.host.F (A.crd j hj) * x.1 * ratA D.host.F (A.fb j hj β P)) *
        ((ratA D.host.F (A.fb j hj β P))⁻¹ * κ * ratA D.host.F (A.fb j hj β P)) := by
    rw [hx]; group
  have hX₁ := hp₁.frame P
  rw [e, ← hF₁] at hX₁
  have hc := core (F := D.host.F) (seamP t.seam P.1) ((t.cst μ).D P) hD _ _ _ hX hX₁
  set C₀ := g.1⁻¹ * F₀⁻¹ * F₁ with hC₀
  have hM : (seamGL t.seam F₀ * seamGL t.seam g.1)⁻¹ * seamGL t.seam F₁ = seamGL t.seam C₀ := by
    rw [hC₀, map_mul, map_mul, map_inv, map_inv, _root_.mul_inv_rev]
  simp only [hM] at hc
  have hcol : ∀ s l, IntAt P.1 (((qOf P.1 : t.X.E) ^ (t.cst μ).D P)⁻¹ *
      (C₀ (Pi.single s (1 : t.X.E)) l - (Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N j)) l)) := by
    intro s l
    have hc' := hc l s
    rw [GlobalTheory.TwU.MidIndep.qOf_seamP] at hc'
    refine intAt_of_seamP t.seam P.1 _ ?_
    convert hc' using 1
    have hm := congrFun (seamGL_mulVec t.seam C₀ (Pi.single s 1)) l
    have hs1 : (fun j => t.seam.iE ((Pi.single s (1 : t.X.E) : Sp t.X.E (D.R.N _)) j)) = Pi.single s (1 : D.host.E) := by
      funext j
      rw [Pi.single_apply, Pi.single_apply]
      split_ifs <;> simp
    rw [hs1, Matrix.mulVec_single_one] at hm
    rw [map_mul, map_inv₀, map_pow, map_natCast, map_sub, ← hm, Matrix.sub_apply, Matrix.one_apply, Pi.single_apply]
    by_cases h : l = s
    · subst h; simp [Matrix.col_apply]
    · simp [h, Matrix.col_apply]
  obtain ⟨hk, hpc⟩ := GlobalTheory.CongOne.mem_glint_prinCong_of_cols P.1 ((t.cst μ).D P) C₀ hD hcol
  refine ⟨⟨C₀, hk⟩, hpc, fun a' b' => ?_, ?_⟩
  · have h1 := GlobalTheory.CplPt.intAtA_of_intAt (F := D.host.F) (hc a' b')
    convert h1 using 2
    rw [map_mul (iA D.host.F D.host.E), Matrix.sub_apply, Matrix.sub_apply, map_sub (iA D.host.F D.host.E), GlobalTheory.CplPt.ratA_apply,
      Matrix.one_apply, Matrix.one_apply]
    split_ifs <;> simp
  · show F₁ = F₀ * (g.1 * C₀)
    rw [hC₀]
    group

end GlobalTheory.LevFrames
