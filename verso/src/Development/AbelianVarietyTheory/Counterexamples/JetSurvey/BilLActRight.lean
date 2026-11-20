import Mathlib
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.CIndFrFix

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.TwistCheck

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB ReciprocityTheory.ChartRestriction.G.TB.LogPf
open Formalism.MainNotions.ModuliIntegralCharts.H1.CIndFrFix

variable {S : Type} [CommRing S] [Algebra ℚ S] {d : ℕ}

/- English proof (translation)
The claim follows from `constantCoeff_prim _`.
-/
theorem cc_log (G : FGLaw S d) (i : Fin d) : constantCoeff (logOf G i) = 0 := constantCoeff_prim _

/- English proof (translation)
Establish `hx : ∀ h : PS S 1 d, ev (n` using `1) ![pt S d 0, 0] (ev (n := 2) ![G.F] h) = h := by`. Introduce `h`. Rewrite using `[ev_ev cz1 (czFF G)]`. Establish `: (fun j i => ev (n` using `1) ![pt S d 0, 0] ((![G.F] : Fin 1 → Pt S 2 d) j i)) = fun j => pt S (n := 1) d j := by`. Use function extensionality and compare the values at `j i`.

Use `fin_cases j`. Use `show ev (n := 1) ![pt S d 0, 0] (G.F i) = X ((0 : Fin 1), i)`. Rewrite using `[← G.unit i]`. Use `conv_lhs => rw [← G.comm i, ev_ev cz1 czSw]`. Use `congr 1`.

Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X cz1]`. Rewrite using `[this, ev_pt]`. Establish `h1 : ∀ b, ∑ e, pderiv S ((0 : Fin 1), e) g * Jac G e b = C (constantCoeff (pderiv S ((0 : Fin 1), b) g))`. Introduce `b`.

Use `congrArg (fun f => ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), b) f)) hg` as an intermediate fact. Simplify using `only [map_add, d_evF, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ez_y, ev_sum cz1, ev_mul cz1, hx] at this`. Conclude with `this`. Establish `h2 : ∀ a, pderiv S ((0 : Fin 1), a) g = ∑ b, C (constantCoeff (pderiv S ((0 : Fin 1), b) g)) * Om G b a`. Introduce `a`.

Establish `e1 : pderiv S ((0 : Fin 1), a) g = ∑ e, pderiv S ((0 : Fin 1), e) g * (JM G * Om G) e a`. Rewrite using `[mul_om]`. Simplify using `[Matrix.one_apply]`. Rewrite using `[e1]`. Simplify using `only [Matrix.mul_apply, Finset.mul_sum]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← h1 b, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun e _ => ?_` and prove the remaining obligations. Simplify using `only [JM, Matrix.of_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : constantCoeff g = 0`. Use `congrArg constantCoeff hg` as an intermediate fact. Rewrite `this` using `[map_add, cc_ev (czFF G), cc_ev czX, cc_ev czY]`. Simplify using `using this`.

Rewrite using `[← sub_eq_zero]`. Establish `hd : ∀ v, pderiv S v (g - ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j) = 0`. Introduce and unpack `⟨j, c⟩`. Take `rfl : j = 0` from `Subsingleton.elim _ _`. Rewrite using `[map_sub, map_sum, h2 c, sub_eq_zero]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, pderiv_logOf]`. Rewrite using `[eq_C_of_pderiv_zero hd]`. Simplify using `[h0, cc_log]`.
-/
theorem additive_eq (G : FGLaw S d) (g : PS S 1 d)
    (hg : ev (n := 2) ![G.F] g = ev (n := 2) ![pt S d 0] g + ev (n := 2) ![pt S d 1] g) :
    g = ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j := by
  have hx : ∀ h : PS S 1 d, ev (n := 1) ![pt S d 0, 0] (ev (n := 2) ![G.F] h) = h := by
    intro h
    rw [ev_ev cz1 (czFF G)]
    have : (fun j i => ev (n := 1) ![pt S d 0, 0] ((![G.F] : Fin 1 → Pt S 2 d) j i)) = fun j => pt S (n := 1) d j := by
      funext j i
      fin_cases j
      show ev (n := 1) ![pt S d 0, 0] (G.F i) = X ((0 : Fin 1), i)
      rw [← G.unit i]
      conv_lhs => rw [← G.comm i, ev_ev cz1 czSw]
      congr 1
      funext j c
      fin_cases j <;> simp [pt_apply, ev_X cz1]
    rw [this, ev_pt]
  have h1 : ∀ b, ∑ e, pderiv S ((0 : Fin 1), e) g * Jac G e b = C (constantCoeff (pderiv S ((0 : Fin 1), b) g)) := by
    intro b
    have := congrArg (fun f => ev (n := 1) ![pt S d 0, 0] (pderiv S ((1 : Fin 2), b) f)) hg
    simp only [map_add, d_evF, pderiv_second_ev_first_point_eq_zero, d_evY, zero_add, ez_y, ev_sum cz1, ev_mul cz1, hx] at this
    exact this
  have h2 : ∀ a, pderiv S ((0 : Fin 1), a) g =
      ∑ b, C (constantCoeff (pderiv S ((0 : Fin 1), b) g)) * Om G b a := by
    intro a
    have e1 : pderiv S ((0 : Fin 1), a) g = ∑ e, pderiv S ((0 : Fin 1), e) g * (JM G * Om G) e a := by
      rw [mul_om]; simp [Matrix.one_apply]
    rw [e1]
    simp only [Matrix.mul_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← h1 b, Finset.sum_mul]
    refine Finset.sum_congr rfl fun e _ => ?_
    simp only [JM, Matrix.of_apply]; ring
  have h0 : constantCoeff g = 0 := by
    have := congrArg constantCoeff hg
    rw [map_add, cc_ev (czFF G), cc_ev czX, cc_ev czY] at this
    simpa using this
  rw [← sub_eq_zero]
  have hd : ∀ v, pderiv S v (g - ∑ j, C (constantCoeff (pderiv S ((0 : Fin 1), j) g)) * logOf G j) = 0 := by
    rintro ⟨j, c⟩
    obtain rfl : j = 0 := Subsingleton.elim _ _
    rw [map_sub, map_sum, h2 c, sub_eq_zero]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← smul_eq_C_mul, ← smul_eq_C_mul, Derivation.map_smul, pderiv_logOf]
  rw [eq_C_of_pderiv_zero hd]
  simp [h0, cc_log]

/- English proof (translation)
Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]`. Simplify using the standard rewrite rules.
-/
theorem cc_pderiv (f : PS S 1 d) (j : Fin d) :
    constantCoeff (pderiv S ((0 : Fin 1), j) f) = coeff (Finsupp.single ((0 : Fin 1), j) 1) f := by
  rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add]; simp

/- English proof (translation)
Establish `hA : CZ (![A.act a] : Fin 1 → Pt S 1 d)` using `CZ.cons (A.const a) CZ.nil`. Establish `hc : ∀ l : Fin 2, ∀ c, constantCoeff (comp1 (A.act a) (pt S (n` using `2) d l) c) = 0 := fun l c => by`. Rewrite using `[comp1, cc_ev (CZ.cons (cc_pt l) CZ.nil)]`. Conclude with `A.const a c`. Establish `hP : CZ (![comp1 (A.act a) (pt S (n` using `2) d 0), comp1 (A.act a) (pt S d 1)] : Fin 2 → Pt S 2 d) := CZ.cons (hc 0) (CZ.cons (hc 1) CZ.nil)`.

Establish `hadd : ev (n` using `2) ![G.F] (ev (n := 1) ![A.act a] (logOf G i)) = ev (n := 2) ![pt S d 0] (ev (n := 1) ![A.act a] (logOf G i)) + ev (n := 2) ![pt S d 1] (ev (n := 1) ![A.act a] (logOf G i)) := by`. Establish `h` using `congrArg (ev (n := 2) ![comp1 (A.act a) (pt S (n := 2) d 0), comp1 (A.act a) (pt S d 1)]) (logOf_add G i)`. Rewrite `h` using `[ev_add hP, ev_ev hP (czFF G), ev_ev hP czX, ev_ev hP czY]`. Rewrite using `[ev_ev (czFF G) hA, ev_ev czX hA, ev_ev czY hA]`. Use `h using 2` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `j c fin_cases j`. Use `congrFun (A.hom a) c` as an intermediate fact. Simplify using `only [comp1] at this`. Rewrite `this` using `[addPt]`. Conclude with `this`.

Use `congr 1`. Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Simplify using `[pt_apply, ev_X hP, comp1]`. Use `congr 1`.

Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Simplify using `[pt_apply, ev_X hP, comp1]`. Rewrite using `[additive_eq G _ hadd]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Use `congr 2`. Rewrite using `[pderiv_ev hA, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]`. Establish `hO : ∀ c, constantCoeff (Om G i c) = if i = c then 1 else 0` using `fun c => by`. Use `congrFun (congrFun (cc_om G) i) c` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`.

Simplify using `only [map_mul, cc_ev hA, pderiv_logOf, hO, cc_pderiv]`. Simplify using `[dLin]`.
-/
theorem log_act {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (i : Fin d) :
    ev (n := 1) ![A.act a] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * logOf G j := by
  have hA : CZ (![A.act a] : Fin 1 → Pt S 1 d) := CZ.cons (A.const a) CZ.nil
  have hc : ∀ l : Fin 2, ∀ c, constantCoeff (comp1 (A.act a) (pt S (n := 2) d l) c) = 0 := fun l c => by
    rw [comp1, cc_ev (CZ.cons (cc_pt l) CZ.nil)]; exact A.const a c
  have hP : CZ (![comp1 (A.act a) (pt S (n := 2) d 0), comp1 (A.act a) (pt S d 1)] : Fin 2 → Pt S 2 d) :=
    CZ.cons (hc 0) (CZ.cons (hc 1) CZ.nil)
  have hadd : ev (n := 2) ![G.F] (ev (n := 1) ![A.act a] (logOf G i)) =
      ev (n := 2) ![pt S d 0] (ev (n := 1) ![A.act a] (logOf G i)) +
        ev (n := 2) ![pt S d 1] (ev (n := 1) ![A.act a] (logOf G i)) := by
    have h := congrArg (ev (n := 2) ![comp1 (A.act a) (pt S (n := 2) d 0), comp1 (A.act a) (pt S d 1)]) (logOf_add G i)
    rw [ev_add hP, ev_ev hP (czFF G), ev_ev hP czX, ev_ev hP czY] at h
    rw [ev_ev (czFF G) hA, ev_ev czX hA, ev_ev czY hA]
    convert h using 2
    · funext j c
      fin_cases j
      have := congrFun (A.hom a) c
      simp only [comp1] at this
      rw [addPt] at this
      exact this
    · congr 1; funext j c; fin_cases j; simp [pt_apply, ev_X hP, comp1]
    · congr 1; funext j c; fin_cases j; simp [pt_apply, ev_X hP, comp1]
  rw [additive_eq G _ hadd]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 2
  rw [pderiv_ev hA, Fintype.sum_prod_type, Fin.sum_univ_one, map_sum]
  have hO : ∀ c, constantCoeff (Om G i c) = if i = c then 1 else 0 := fun c => by
    have := congrFun (congrFun (cc_om G) i) c
    simpa [Matrix.one_apply] using this
  simp only [map_mul, cc_ev hA, pderiv_logOf, hO, cc_pderiv]
  simp [dLin]

/- English proof (translation)
Simplify using `only [bilL, ev_sum ha, smul_eq_C_mul, ev_mul ha, ev_C ha, lg, ev_ev ha czX, ev_ev ha czY]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `congr 3 <;> funext j c <;> fin_cases j <;> simp [pt_apply, ev_X ha]`.
-/
theorem ev_bilL {n : ℕ} (G : FGLaw S d) (cc : Fin d → Fin d → S) {a : Fin 2 → Pt S n d} (ha : CZ a) :
    ev a (bilL G cc) = ∑ i, ∑ l, C (cc i l) * (ev ![a 0] (logOf G i) * ev ![a 1] (logOf G l)) := by
  simp only [bilL, ev_sum ha, smul_eq_C_mul, ev_mul ha, ev_C ha, lg, ev_ev ha czX, ev_ev ha czY]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun l _ => ?_
  congr 3 <;> funext j c <;> fin_cases j <;> simp [pt_apply, ev_X ha]

/- English proof (translation)
Establish `hA : CZ (![A.act a] : Fin 1 → Pt S 1 d)` using `CZ.cons (A.const a) CZ.nil`. Establish `hl : CZ (![pt S (n` using `2) d l] : Fin 1 → Pt S 2 d) := CZ.cons (cc_pt l) CZ.nil`. Establish `h` using `congrArg (ev (n := 2) ![pt S d l]) (log_act G A a i)`. Rewrite `h` using `[ev_ev hl hA]`. Simplify using `only [ev_sum hl, ev_mul hl, ev_C hl] at h`.

Use `h using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem log_act_at {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (l : Fin 2) (i : Fin d) :
    ev (n := 2) ![comp1 (A.act a) (pt S d l)] (logOf G i) = ∑ j, C (dLin (A.act a) i j) * lg G l j := by
  have hA : CZ (![A.act a] : Fin 1 → Pt S 1 d) := CZ.cons (A.const a) CZ.nil
  have hl : CZ (![pt S (n := 2) d l] : Fin 1 → Pt S 2 d) := CZ.cons (cc_pt l) CZ.nil
  have h := congrArg (ev (n := 2) ![pt S d l]) (log_act G A a i)
  rw [ev_ev hl hA] at h
  simp only [ev_sum hl, ev_mul hl, ev_C hl] at h
  convert h using 2
  · funext j c; fin_cases j; rfl
  · rfl

/- English proof (translation)
Establish `hP : CZ (![comp1 (A.act a) (pt S (n` using `2) d 0), pt S d 1] : Fin 2 → Pt S 2 d) := CZ.cons (fun c => by rw [comp1, cc_ev czX]; exact A.const a c) czY`. Rewrite using `[ev_bilL G cc hP]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply, Matrix.transpose_apply, Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [lg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bilL_act_left {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
      bilL G ((dLin (A.act a)).transpose * Matrix.of cc) := by
  have hP : CZ (![comp1 (A.act a) (pt S (n := 2) d 0), pt S d 1] : Fin 2 → Pt S 2 d) :=
    CZ.cons (fun c => by rw [comp1, cc_ev czX]; exact A.const a c) czY
  rw [ev_bilL G cc hP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply, Matrix.transpose_apply,
    Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [lg]; ring

/- English proof (translation)
Establish `hP : CZ (![pt S (n` using `2) d 0, comp1 (A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) := CZ.cons (cc_pt 0) (CZ.cons (fun c => by rw [comp1, cc_ev czY]; exact A.const b c) CZ.nil)`. Rewrite using `[ev_bilL G cc hP]`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply, Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [lg]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bilL_act_right {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (b : O) (cc : Fin d → Fin d → S) :
    ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) =
      bilL G (Matrix.of cc * dLin (A.act b)) := by
  have hP : CZ (![pt S (n := 2) d 0, comp1 (A.act b) (pt S d 1)] : Fin 2 → Pt S 2 d) :=
    CZ.cons (cc_pt 0) (CZ.cons (fun c => by rw [comp1, cc_ev czY]; exact A.const b c) CZ.nil)
  rw [ev_bilL G cc hP]
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, log_act_at, bilL, Matrix.mul_apply,
    Matrix.of_apply, smul_eq_C_mul, map_sum, map_mul, Finset.sum_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun j _ => ?_
  simp only [lg]; ring

/- English proof (translation)
Establish `hO : ∀ a c, constantCoeff (Om G a c) = if a = c then 1 else 0` using `fun a c => by`. Use `congrFun (congrFun (cc_om G) a) c` as an intermediate fact. Simplify `this` using `[Matrix.one_apply]`. Simplify using `only [bilL, lg, map_sum, Derivation.map_smul, Derivation.leibniz, smul_eq_mul, d_evX, d_evY, pderiv_second_ev_first_point_eq_zero, pderiv_first_ev_second_point_eq_zero, pderiv_logOf, mul_zero, add_zero, zero_add, map_add, map_mul, constantCoeff_smul, cc_ev czX, cc_ev czY, hO]`. Simplify using the standard rewrite rules.
-/
theorem bilL_mixed (G : FGLaw S d) (cc : Fin d → Fin d → S) (i l : Fin d) :
    constantCoeff (pderiv S ((0 : Fin 2), i) (pderiv S ((1 : Fin 2), l) (bilL G cc))) = cc i l := by
  have hO : ∀ a c, constantCoeff (Om G a c) = if a = c then 1 else 0 := fun a c => by
    have := congrFun (congrFun (cc_om G) a) c
    simpa [Matrix.one_apply] using this
  simp only [bilL, lg, map_sum, Derivation.map_smul, Derivation.leibniz, smul_eq_mul, d_evX, d_evY, pderiv_second_ev_first_point_eq_zero, pderiv_first_ev_second_point_eq_zero,
    pderiv_logOf, mul_zero, add_zero, zero_add, map_add, map_mul, constantCoeff_smul, cc_ev czX, cc_ev czY, hO]
  simp

/- English proof (translation)
Introduce `c c' h` and use `by funext i l rw [← bilL_mixed G c, h, bilL_mixed]`.
-/
theorem bilL_injective (G : FGLaw S d) : Function.Injective (bilL G) := fun c c' h => by
  funext i l
  rw [← bilL_mixed G c, h, bilL_mixed]

/- English proof (translation)
Rewrite using `[bilL_act_left, bilL_act_right]`. Conclude with `⟨fun h => by rw [h], fun h => bilL_injective G h⟩`.
-/
theorem balanced_iff {O : Type} [CommRing O] (G : FGLaw S d) (A : OAct O G) (a b : O) (cc : Fin d → Fin d → S) :
    (dLin (A.act a)).transpose * Matrix.of cc = Matrix.of cc * dLin (A.act b) ↔
      ev (n := 2) ![comp1 (A.act a) (pt S d 0), pt S d 1] (bilL G cc) =
        ev (n := 2) ![pt S d 0, comp1 (A.act b) (pt S d 1)] (bilL G cc) := by
  rw [bilL_act_left, bilL_act_right]
  exact ⟨fun h => by rw [h], fun h => bilL_injective G h⟩

end GlobalTheory.TwistCheck
