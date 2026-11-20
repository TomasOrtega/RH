import Formalism.LocalToGlobal.CharacterGerms.ConstantZeroDoubleMultiplicationPair
import Formalism.LocalToGlobal.CharacterGerms.RowTiePGmExLem

set_option autoImplicit false

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds.MulLFrob

open Formalism.L2.FormalSeriesBounds Formalism.L2.FormalSeriesBounds.PartialDerivEval Formalism.L2.FormalSeriesBounds.FirstUnitSeriesIntegrality ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ MvPowerSeries

variable {C : Type} [Field C] [CharZero C] {dd : ℕ}

/- English proof (translation)
Unfold `ev`. Rewrite using `[Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![P] : Fin 1 → Pt C n dd) p.1 p.2) (fun p => by obtain ⟨k, j⟩ := p; fin_cases k; exact hP j) f q, Fintype.sum_prod_type, Fin.sum_univ_one]`. Both sides reduce to the same expression.
-/
theorem pderiv_eval_single {n : ℕ} {P : Pt C n dd} (hP : ∀ j, constantCoeff (P j) = 0) (f : PS C 1 dd)
    (q : Fin n × Fin dd) :
    pderiv C q (ev ![P] f) = ∑ j, ev ![P] (pderiv C ((0 : Fin 1), j) f) * pderiv C q (P j) := by
  unfold ev
  rw [Formalism.G.LogCR.pderiv_subst (a := fun p : Fin 1 × Fin dd => (![P] : Fin 1 → Pt C n dd) p.1 p.2)
    (fun p => by obtain ⟨k, j⟩ := p; fin_cases k; exact hP j) f q, Fintype.sum_prod_type, Fin.sum_univ_one]
  rfl

/- English proof (translation)
Unfold `ev`. Establish `: (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X`. Use function extensionality and compare the values at `p`. Take `⟨k, j⟩` from `p`. Use `fin_cases k`.

Both sides reduce to the same expression. Rewrite using `[this, subst_self]`. Both sides reduce to the same expression.
-/
theorem germEval_oneStandardPoint_self (f : PS C 1 dd) : ev (n := 1) ![pt C dd 0] f = f := by
  unfold ev
  have : (fun p : Fin 1 × Fin dd => (![pt C dd 0] : Fin 1 → Pt C 1 dd) p.1 p.2) = X := by
    funext p; obtain ⟨k, j⟩ := p; fin_cases k; rfl
  rw [this, subst_self]; rfl

/- English proof (translation)
Unfold `ev`. Establish `: (fun p : Fin 1 × Fin dd => (![(0 : Pt C n dd)] : Fin 1 → Pt C n dd) p.1 p.2) = 0`. Use function extensionality and compare the values at `p`. Take `⟨k, j⟩` from `p`. Use `fin_cases k`.

Both sides reduce to the same expression. Rewrite using `[this, subst_zero_eq_C_constantCoeff, show algebraMap C C = RingHom.id C from rfl, map_id]`. Both sides reduce to the same expression.
-/
theorem ev_zero_pt {n : ℕ} (f : PS C 1 dd) : ev (n := n) ![(0 : Pt C n dd)] f = MvPowerSeries.C (constantCoeff f) := by
  unfold ev
  have : (fun p : Fin 1 × Fin dd => (![(0 : Pt C n dd)] : Fin 1 → Pt C n dd) p.1 p.2) = 0 := by
    funext p; obtain ⟨k, j⟩ := p; fin_cases k; rfl
  rw [this, subst_zero_eq_C_constantCoeff, show algebraMap C C = RingHom.id C from rfl, map_id]
  rfl

/- English proof (translation)
Use `show pderiv C q (X (k, j)) = _`. Rewrite using `[pderiv_X, Pi.single_apply]`.
-/
theorem pderiv_pt {n : ℕ} (q : Fin n × Fin dd) (k : Fin n) (j : Fin dd) :
    pderiv C q (pt C dd k j) = if (k, j) = q then 1 else 0 := by
  show pderiv C q (X (k, j)) = _
  rw [pderiv_X, Pi.single_apply]

/- English proof (translation)
The claim follows from `z0_p0 _ fun j => z0_pt 0 j`.
-/
theorem constant_zero_first_then_zero : Z0 (![pt C (n := 1) dd 0, 0] : Fin 2 → Pt C 1 dd) :=
  z0_p0 _ fun j => z0_pt 0 j

/- English proof (translation)
Rewrite using `[← G.comm i, ev_ev (z0_pp 1 0) constant_zero_first_then_zero]`. Establish `e : (fun k j => ev (n` using `1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) = ![0, pt C dd 0] := by`. Use function extensionality and compare the values at `k j`. Use `fin_cases k`. Conclude with `ev_X constant_zero_first_then_zero 1 j`.

Conclude with `ev_X constant_zero_first_then_zero 0 j`. Rewrite using `[e]`. Conclude with `G.unit i`.
-/
theorem formalGroupLaw_ev_x_zero (G : FGLaw C dd) (i : Fin dd) : ev (n := 1) ![pt C dd 0, 0] (G.F i) = X ((0 : Fin 1), i) := by
  rw [← G.comm i, ev_ev (z0_pp 1 0) constant_zero_first_then_zero]
  have e : (fun k j => ev (n := 1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1, pt C dd 0] : Fin 2 → Pt C 2 dd) k j)) =
      ![0, pt C dd 0] := by
    funext k j
    fin_cases k
    · exact ev_X constant_zero_first_then_zero 1 j
    · exact ev_X constant_zero_first_then_zero 0 j
  rw [e]; exact G.unit i

def JF (G : FGLaw C dd) : Matrix (Fin dd) (Fin dd) (PS C 1 dd) :=
  fun k i => ev (n := 1) ![pt C dd 0, 0] (pderiv C ((1 : Fin 2), i) (G.F k))

def Jac (P : Pt C 1 dd) : Matrix (Fin dd) (Fin dd) (PS C 1 dd) :=
  fun k i => pderiv C ((0 : Fin 1), i) (P k)

def cmp (P : Pt C 1 dd) (A : Matrix (Fin dd) (Fin dd) (PS C 1 dd)) : Matrix (Fin dd) (Fin dd) (PS C 1 dd) :=
  fun k i => ev ![P] (A k i)

/- English proof (translation)
Use function extensionality and compare the values at `k i`. Simplify using `only [cmp, Matrix.mul_apply]`. Rewrite using `[ev_sum (z0_1 P hP)]`. Conclude with `Finset.sum_congr rfl fun j _ => ev_mul (z0_1 P hP) _ _`.
-/
theorem cmp_mul {P : Pt C 1 dd} (hP : ∀ j, constantCoeff (P j) = 0) (A B : Matrix (Fin dd) (Fin dd) (PS C 1 dd)) :
    cmp P (A * B) = cmp P A * cmp P B := by
  funext k i
  simp only [cmp, Matrix.mul_apply]
  rw [ev_sum (z0_1 P hP)]
  exact Finset.sum_congr rfl fun j _ => ev_mul (z0_1 P hP) _ _

/- English proof (translation)
Use function extensionality and compare the values at `k i`. Simplify using `only [cmp, Matrix.one_apply]`. Use `split_ifs`. Conclude with `ev_one _`. Rewrite using `[show (0 : PS C 1 dd) = MvPowerSeries.C 0 from (map_zero _).symm, ev_C]`.
-/
theorem cmp_one (P : Pt C 1 dd) : cmp P (1 : Matrix (Fin dd) (Fin dd) (PS C 1 dd)) = 1 := by
  funext k i
  simp only [cmp, Matrix.one_apply]
  split_ifs
  · exact ev_one _
  · rw [show (0 : PS C 1 dd) = MvPowerSeries.C 0 from (map_zero _).symm, ev_C]

/- English proof (translation)
Use function extensionality and compare the values at `k i`. Establish `hAdd : addOf Y.B.G.F (pt C (n` using `2) dd 0) (pt C dd 1) = Y.B.G.F :=`. Use function extensionality and compare the values at `fun j => PartialDerivEval.eval_points_two _`. Establish `h1` using `Y.lg_add k`. Rewrite `h1` using `[hAdd]`.

Establish `h2` using `congrArg (pderiv C ((1 : Fin 2), i)) h1`. Establish `hd0 : ∀ g : PS C 1 dd, pderiv C ((1 : Fin 2), i) (ev (n` using `2) ![pt C dd 0] g) = 0 := by`. Introduce `g`. Rewrite using `[pderiv_eval_single (P := pt C (n := 2) dd 0) (fun j => z0_pt 0 j)]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[pderiv_pt, if_neg (fun h => absurd (Prod.mk.inj h).1 (by decide)), mul_zero]`. Establish `hd1 : ∀ g : PS C 1 dd, pderiv C ((1 : Fin 2), i) (ev (n` using `2) ![pt C dd 1] g) = ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) g) := by`. Introduce `g`. Rewrite using `[pderiv_eval_single (P := pt C (n := 2) dd 1) (fun j => z0_pt 1 j), Finset.sum_eq_single i (fun j _ hj => by rw [pderiv_pt, if_neg (fun h => hj (Prod.mk.inj h).2), mul_zero]) (fun h => absurd (Finset.mem_univ i) h), pderiv_pt, if_pos rfl, mul_one]`. Rewrite `h2` using `[map_add, pderiv_eval_single (P := Y.B.G.F) Y.B.G.const, hd0, hd1, zero_add]`.

Establish `h3` using `congrArg (ev (n := 1) ![pt C dd 0, 0]) h2`. Rewrite `h3` using `[ev_sum constant_zero_first_then_zero]`. Establish `hL : ∀ j, ev (n` using `1) ![pt C dd 0, 0] (ev ![Y.B.G.F] (pderiv C ((0 : Fin 1), j) (Y.lg k))) = pderiv C ((0 : Fin 1), j) (Y.lg k) := by`. Introduce `j`. Rewrite using `[ev_ev (z0_1 _ Y.B.G.const) constant_zero_first_then_zero]`.

Establish `e : (fun k' j' => ev (n` using `1) ![pt C dd 0, 0] ((![Y.B.G.F] : Fin 1 → Pt C 2 dd) k' j')) = ![pt C dd 0] := by`. Use function extensionality and compare the values at `k' j'`. Use `fin_cases k'`. Conclude with `formalGroupLaw_ev_x_zero Y.B.G j'`. Rewrite using `[e, germEval_oneStandardPoint_self]`.

Establish `hR : ∀ g : PS C 1 dd, ev (n` using `1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] g) = MvPowerSeries.C (constantCoeff g) := by`. Introduce `g`. Rewrite using `[ev_ev (z0_1 (pt C (n := 2) dd 1) (fun j => z0_pt 1 j)) constant_zero_first_then_zero]`. Establish `e : (fun k' j' => ev (n` using `1) ![pt C dd 0, 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k' j')) = ![(0 : Pt C 1 dd)] := by`. Use function extensionality and compare the values at `k' j'`.

Use `fin_cases k'`. Conclude with `ev_X constant_zero_first_then_zero 1 j'`. Rewrite using `[e, ev_zero_pt]`. Simplify using `only [ev_mul constant_zero_first_then_zero, hL] at h3`. Rewrite `h3` using `[hR]`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Simplify using `only [Jac, JF]`. Rewrite using `[h3]`. Establish `hc : constantCoeff (pderiv C ((0 : Fin 1), i) (Y.lg k)) = if k = i then 1 else 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add, Y.lg_lin k _ (by simp), coeff_X]`.

Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hki, if_neg (fun h => hki (by`. Use `(Finsupp.single_left_inj one_ne_zero).1 h` as an intermediate fact.

Conclude with `(Prod.mk.inj this).2.symm)), zero_mul]`. Rewrite using `[hc]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem JL_JF {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) :
    Jac Y.lg * JF Y.B.G = 1 := by
  funext k i
  have hAdd : addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) = Y.B.G.F :=
    funext fun j => PartialDerivEval.eval_points_two _
  have h1 := Y.lg_add k
  rw [hAdd] at h1
  have h2 := congrArg (pderiv C ((1 : Fin 2), i)) h1
  have hd0 : ∀ g : PS C 1 dd, pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 0] g) = 0 := by
    intro g
    rw [pderiv_eval_single (P := pt C (n := 2) dd 0) (fun j => z0_pt 0 j)]
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_pt, if_neg (fun h => absurd (Prod.mk.inj h).1 (by decide)), mul_zero]
  have hd1 : ∀ g : PS C 1 dd, pderiv C ((1 : Fin 2), i) (ev (n := 2) ![pt C dd 1] g) =
      ev (n := 2) ![pt C dd 1] (pderiv C ((0 : Fin 1), i) g) := by
    intro g
    rw [pderiv_eval_single (P := pt C (n := 2) dd 1) (fun j => z0_pt 1 j),
      Finset.sum_eq_single i (fun j _ hj => by rw [pderiv_pt, if_neg (fun h => hj (Prod.mk.inj h).2), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), pderiv_pt, if_pos rfl, mul_one]
  rw [map_add, pderiv_eval_single (P := Y.B.G.F) Y.B.G.const, hd0, hd1, zero_add] at h2
  have h3 := congrArg (ev (n := 1) ![pt C dd 0, 0]) h2
  rw [ev_sum constant_zero_first_then_zero] at h3
  have hL : ∀ j, ev (n := 1) ![pt C dd 0, 0] (ev ![Y.B.G.F] (pderiv C ((0 : Fin 1), j) (Y.lg k))) =
      pderiv C ((0 : Fin 1), j) (Y.lg k) := by
    intro j
    rw [ev_ev (z0_1 _ Y.B.G.const) constant_zero_first_then_zero]
    have e : (fun k' j' => ev (n := 1) ![pt C dd 0, 0] ((![Y.B.G.F] : Fin 1 → Pt C 2 dd) k' j')) =
        ![pt C dd 0] := by
      funext k' j'
      fin_cases k'
      exact formalGroupLaw_ev_x_zero Y.B.G j'
    rw [e, germEval_oneStandardPoint_self]
  have hR : ∀ g : PS C 1 dd, ev (n := 1) ![pt C dd 0, 0] (ev ![pt C (n := 2) dd 1] g) =
      MvPowerSeries.C (constantCoeff g) := by
    intro g
    rw [ev_ev (z0_1 (pt C (n := 2) dd 1) (fun j => z0_pt 1 j)) constant_zero_first_then_zero]
    have e : (fun k' j' => ev (n := 1) ![pt C dd 0, 0]
        ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k' j')) = ![(0 : Pt C 1 dd)] := by
      funext k' j'; fin_cases k'; exact ev_X constant_zero_first_then_zero 1 j'
    rw [e, ev_zero_pt]
  simp only [ev_mul constant_zero_first_then_zero, hL] at h3
  rw [hR] at h3
  rw [Matrix.mul_apply, Matrix.one_apply]
  simp only [Jac, JF]
  rw [h3]
  have hc : constantCoeff (pderiv C ((0 : Fin 1), i) (Y.lg k)) = if k = i then 1 else 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply, coeff_pderiv, zero_add,
      Y.lg_lin k _ (by simp), coeff_X]
    by_cases hki : k = i
    · subst hki; simp
    · rw [if_neg hki, if_neg (fun h => hki (by
        have := (Finsupp.single_left_inj one_ne_zero).1 h
        exact (Prod.mk.inj this).2.symm)), zero_mul]
  rw [hc]
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[zero_nsmul]`. Use `show ev (n := 1) ![(0 : Pt C 1 dd)] (Y.lg k) = 0`. Rewrite using `[ev_zero_pt]`.

Establish `: constantCoeff (Y.lg k) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply, Y.lg_lin k 0 (by simp), coeff_zero_X]`. Rewrite using `[this, map_zero]`. Consider the case `succ n ih`. Establish `hA : Z0 (![mulL Y.B.G.F n, pt C (n` using `1) dd 0] : Fin 2 → Pt C 1 dd) := fun k' j => by fin_cases k'`.

Conclude with `multiplication_constantCoeff_zero Y.B.G n j`. Conclude with `z0_pt 0 j`. Establish `hAdd : addOf Y.B.G.F (pt C (n` using `2) dd 0) (pt C dd 1) = Y.B.G.F :=`. Use function extensionality and compare the values at `fun j => PartialDerivEval.eval_points_two _`. Establish `h1` using `congrArg (ev ![mulL Y.B.G.F n, pt C (n := 1) dd 0]) (Y.lg_add k)`.

Rewrite `h1` using `[hAdd, ev_add hA, ev_ev (z0_1 _ Y.B.G.const) hA, ev_ev (z0_1 _ (fun j => z0_pt 0 j)) hA, ev_ev (z0_1 _ (fun j => z0_pt 1 j)) hA]`. Establish `e1 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n` using `1) dd 0] ((![Y.B.G.F] : Fin 1 → Pt C 2 dd) k' j)) = ![mulL Y.B.G.F (n + 1)] := by`. Use function extensionality and compare the values at `k' j`. Use `fin_cases k'`. Both sides reduce to the same expression.

Establish `e2 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n` using `1) dd 0] ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k' j)) = ![mulL Y.B.G.F n] := by`. Use function extensionality and compare the values at `k' j`. Use `fin_cases k'`. Conclude with `ev_X hA 0 j`. Establish `e3 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n` using `1) dd 0] ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k' j)) = ![pt C (n := 1) dd 0] := by`.

Use function extensionality and compare the values at `k' j`. Use `fin_cases k'`. Conclude with `ev_X hA 1 j`. Rewrite `h1` using `[e1, e2, e3, germEval_oneStandardPoint_self, ih]`. Rewrite using `[h1, succ_nsmul]`.
-/
theorem lg_mulL {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (n : ℕ) (k : Fin dd) :
    ev (n := 1) ![mulL Y.B.G.F n] (Y.lg k) = n • Y.lg k := by
  induction n with
  | zero =>
    rw [zero_nsmul]
    show ev (n := 1) ![(0 : Pt C 1 dd)] (Y.lg k) = 0
    rw [ev_zero_pt]
    have : constantCoeff (Y.lg k) = 0 := by
      rw [← coeff_zero_eq_constantCoeff_apply, Y.lg_lin k 0 (by simp), coeff_zero_X]
    rw [this, map_zero]
  | succ n ih =>
    have hA : Z0 (![mulL Y.B.G.F n, pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := fun k' j => by
      fin_cases k'
      · exact multiplication_constantCoeff_zero Y.B.G n j
      · exact z0_pt 0 j
    have hAdd : addOf Y.B.G.F (pt C (n := 2) dd 0) (pt C dd 1) = Y.B.G.F :=
      funext fun j => PartialDerivEval.eval_points_two _
    have h1 := congrArg (ev ![mulL Y.B.G.F n, pt C (n := 1) dd 0]) (Y.lg_add k)
    rw [hAdd, ev_add hA, ev_ev (z0_1 _ Y.B.G.const) hA, ev_ev (z0_1 _ (fun j => z0_pt 0 j)) hA,
      ev_ev (z0_1 _ (fun j => z0_pt 1 j)) hA] at h1
    have e1 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n := 1) dd 0]
        ((![Y.B.G.F] : Fin 1 → Pt C 2 dd) k' j)) = ![mulL Y.B.G.F (n + 1)] := by
      funext k' j; fin_cases k'; rfl
    have e2 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n := 1) dd 0]
        ((![pt C (n := 2) dd 0] : Fin 1 → Pt C 2 dd) k' j)) = ![mulL Y.B.G.F n] := by
      funext k' j; fin_cases k'; exact ev_X hA 0 j
    have e3 : (fun k' j => ev ![mulL Y.B.G.F n, pt C (n := 1) dd 0]
        ((![pt C (n := 2) dd 1] : Fin 1 → Pt C 2 dd) k' j)) = ![pt C (n := 1) dd 0] := by
      funext k' j; fin_cases k'; exact ev_X hA 1 j
    rw [e1, e2, e3, germEval_oneStandardPoint_self, ih] at h1
    rw [h1, succ_nsmul]

/- English proof (translation)
Use function extensionality and compare the values at `k i`. Establish `h` using `congrArg (pderiv C ((0 : Fin 1), i)) (lg_mulL Y n k)`. Rewrite `h` using `[pderiv_eval_single (multiplication_constantCoeff_zero Y.B.G n), map_nsmul]`. Rewrite using `[Matrix.mul_apply, Matrix.smul_apply]`. Conclude with `h`.
-/
theorem jac_mulL {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (n : ℕ) :
    cmp (mulL Y.B.G.F n) (Jac Y.lg) * Jac (mulL Y.B.G.F n) = n • Jac Y.lg := by
  funext k i
  have h := congrArg (pderiv C ((0 : Fin 1), i)) (lg_mulL Y n k)
  rw [pderiv_eval_single (multiplication_constantCoeff_zero Y.B.G n), map_nsmul] at h
  rw [Matrix.mul_apply, Matrix.smul_apply]
  exact h

/- English proof (translation)
Rewrite using `[Matrix.det_apply]`. Use `intS_sum _ fun s _ => ?_` and prove the remaining obligations. Establish `hp : IntS V (∏ i, M (s i) i)` using `Finset.prod_induction _ (IntS V) (fun a b ha hb => intS_mul ha hb) intS_one fun i _ => hM _ _`. Break down `Int.units_eq_one_or (Equiv.Perm.sign s) with h | h` into its components or cases. Rewrite using `[h, one_smul]`.

Conclude with `hp`. Rewrite using `[h, Units.neg_smul, one_smul]`. Conclude with `intS_neg hp`.
-/
theorem intS_det {V : VF C} {σ : Type} (M : Matrix (Fin dd) (Fin dd) (MvPowerSeries σ C))
    (hM : ∀ k i, IntS V (M k i)) : IntS V M.det := by
  rw [Matrix.det_apply]
  refine intS_sum _ fun s _ => ?_
  have hp : IntS V (∏ i, M (s i) i) :=
    Finset.prod_induction _ (IntS V) (fun a b ha hb => intS_mul ha hb) intS_one fun i _ => hM _ _
  rcases Int.units_eq_one_or (Equiv.Perm.sign s) with h | h
  · rw [h, one_smul]; exact hp
  · rw [h, Units.neg_smul, one_smul]; exact intS_neg hp

/- English proof (translation)
Rewrite using `[Matrix.adjugate_apply]`. Use `intS_det _ fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`. Rewrite using `[Pi.single_apply]`.

Use `split_ifs`. Conclude with `intS_one`. Conclude with `intS_zero`. Conclude with `hM _ _`.
-/
theorem intS_adj {V : VF C} {σ : Type} (M : Matrix (Fin dd) (Fin dd) (MvPowerSeries σ C))
    (hM : ∀ k i, IntS V (M k i)) (k i : Fin dd) : IntS V (M.adjugate k i) := by
  rw [Matrix.adjugate_apply]
  refine intS_det _ fun a b => ?_
  rw [Matrix.updateRow_apply]
  split_ifs
  · rw [Pi.single_apply]; split_ifs
    · exact intS_one
    · exact intS_zero
  · exact hM _ _

/- English proof (translation)
Unfold `JF`. Rewrite using `[constantCoeff_ev constant_zero_first_then_zero]`. Establish `hA : Z0 (![(0 : Pt C 1 dd), pt C (n` using `1) dd 0] : Fin 2 → Pt C 1 dd) := fun k' j => by fin_cases k'`. Conclude with `map_zero _`. Conclude with `z0_pt 0 j`.

Establish `h` using `congrArg (pderiv C ((0 : Fin 1), i)) (G.unit k)`. Rewrite `h` using `[pderiv_eval_pair hA]`. Establish `h0 : ∀ j, pderiv C ((0 : Fin 1), i) ((0 : Pt C 1 dd) j) = 0` using `fun j => map_zero _`. Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, mul_zero, Finset.sum_const_zero, zero_add, pderiv_pt, pderiv_X] at h`. Rewrite `h` using `[Finset.sum_eq_single i (fun x _ hx => by rw [if_neg (by simp [hx]), mul_zero]) (fun h' => absurd (Finset.mem_univ i) h'), if_pos rfl, mul_one]`.

Establish `h2` using `congrArg constantCoeff h`. Rewrite `h2` using `[constantCoeff_ev hA]`. Rewrite using `[h2, Pi.single_apply]`. Distinguish the cases in `hki : k = i`. Substitute `hki` using the available equality.

Simplify using the standard rewrite rules. Rewrite using `[if_neg (fun h' => hki (Prod.mk.inj h').2), if_neg hki, map_zero]`.
-/
theorem JF_const (G : FGLaw C dd) (k i : Fin dd) :
    constantCoeff (JF G k i) = if k = i then 1 else 0 := by
  unfold JF
  rw [constantCoeff_ev constant_zero_first_then_zero]
  have hA : Z0 (![(0 : Pt C 1 dd), pt C (n := 1) dd 0] : Fin 2 → Pt C 1 dd) := fun k' j => by
    fin_cases k'
    · exact map_zero _
    · exact z0_pt 0 j
  have h := congrArg (pderiv C ((0 : Fin 1), i)) (G.unit k)
  rw [pderiv_eval_pair hA] at h
  have h0 : ∀ j, pderiv C ((0 : Fin 1), i) ((0 : Pt C 1 dd) j) = 0 := fun j => map_zero _
  simp only [Matrix.cons_val_zero, Matrix.cons_val_one, h0, mul_zero, Finset.sum_const_zero, zero_add,
    pderiv_pt, pderiv_X] at h
  rw [Finset.sum_eq_single i (fun x _ hx => by rw [if_neg (by simp [hx]), mul_zero])
    (fun h' => absurd (Finset.mem_univ i) h'), if_pos rfl, mul_one] at h
  have h2 := congrArg constantCoeff h
  rw [constantCoeff_ev hA] at h2
  rw [h2, Pi.single_apply]
  by_cases hki : k = i
  · subst hki; simp
  · rw [if_neg (fun h' => hki (Prod.mk.inj h').2), if_neg hki, map_zero]

/- English proof (translation)
Use `intS_ev constant_zero_first_then_zero (fun k' j => ?_) (intS_pderiv (Y.intF k) _)` and prove the remaining obligations. Use `fin_cases k'`. Conclude with `intS_X _`. Conclude with `intS_zero`.
-/
theorem JF_int {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (k i : Fin dd) :
    IntS V (JF Y.B.G k i) := by
  refine intS_ev constant_zero_first_then_zero (fun k' j => ?_) (intS_pderiv (Y.intF k) _)
  fin_cases k'
  · exact intS_X _
  · exact intS_zero

/- English proof (translation)
Establish `h1 : JF Y.B.G * Jac Y.lg = 1` using `mul_eq_one_comm.1 (JL_JF Y)`. Use `set δ := (JF Y.B.G).det with hδ`. Establish `hδ0 : constantCoeff δ = 1`. Rewrite using `[hδ, RingHom.map_det]`. Establish `: (constantCoeff : MvPowerSeries (Fin 1 × Fin dd) C →+* C).mapMatrix (JF Y.B.G) = 1`.

Use extensionality with `k' i'`. Rewrite using `[RingHom.mapMatrix_apply, Matrix.map_apply, JF_const, Matrix.one_apply]`. Rewrite using `[this, Matrix.det_one]`. Establish `hδi : IntS V δ` using `intS_det _ (JF_int Y)`. Establish `hw : δ * δ⁻¹ = 1` using `MvPowerSeries.mul_inv_cancel δ (by rw [hδ0]; exact one_ne_zero)`.

Establish `hwi : IntS V δ⁻¹` using `intS_of_mul_eq_one hw hδ0 hδi`. Establish `hadj : (JF Y.B.G).adjugate = δ • Jac Y.lg`. Rewrite using `[← Matrix.mul_one (JF Y.B.G).adjugate, ← h1, ← Matrix.mul_assoc, Matrix.adjugate_mul, Matrix.smul_mul, Matrix.one_mul]`. Establish `e : Jac Y.lg k i = δ⁻¹ * (JF Y.B.G).adjugate k i`. Rewrite using `[hadj, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm δ⁻¹ δ, hw, one_mul]`.

Rewrite using `[e]`. Conclude with `intS_mul hwi (intS_adj _ (JF_int Y) k i)`.
-/
theorem JL_int {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (k i : Fin dd) :
    IntS V (Jac Y.lg k i) := by
  have h1 : JF Y.B.G * Jac Y.lg = 1 := mul_eq_one_comm.1 (JL_JF Y)
  set δ := (JF Y.B.G).det with hδ
  have hδ0 : constantCoeff δ = 1 := by
    rw [hδ, RingHom.map_det]
    have : (constantCoeff : MvPowerSeries (Fin 1 × Fin dd) C →+* C).mapMatrix (JF Y.B.G) = 1 := by
      ext k' i'
      rw [RingHom.mapMatrix_apply, Matrix.map_apply, JF_const, Matrix.one_apply]
    rw [this, Matrix.det_one]
  have hδi : IntS V δ := intS_det _ (JF_int Y)
  have hw : δ * δ⁻¹ = 1 := MvPowerSeries.mul_inv_cancel δ (by rw [hδ0]; exact one_ne_zero)
  have hwi : IntS V δ⁻¹ := intS_of_mul_eq_one hw hδ0 hδi
  have hadj : (JF Y.B.G).adjugate = δ • Jac Y.lg := by
    rw [← Matrix.mul_one (JF Y.B.G).adjugate, ← h1, ← Matrix.mul_assoc, Matrix.adjugate_mul,
      Matrix.smul_mul, Matrix.one_mul]
  have e : Jac Y.lg k i = δ⁻¹ * (JF Y.B.G).adjugate k i := by
    rw [hadj, Matrix.smul_apply, smul_eq_mul, ← mul_assoc, mul_comm δ⁻¹ δ, hw, one_mul]
  rw [e]
  exact intS_mul hwi (intS_adj _ (JF_int Y) k i)

/- English proof (translation)
Establish `h1 : cmp (mulL Y.B.G.F n) (Jac Y.lg) * cmp (mulL Y.B.G.F n) (JF Y.B.G) = 1`. Rewrite using `[← cmp_mul (multiplication_constantCoeff_zero Y.B.G n), JL_JF, cmp_one]`. Establish `h2` using `mul_eq_one_comm.1 h1`. Rewrite using `[← Matrix.one_mul (Jac (mulL Y.B.G.F n)), ← h2, Matrix.mul_assoc, jac_mulL, Matrix.mul_smul]`.
-/
theorem jac_l {V : VF C} {O : Type} [CommRing O] [StarRing O] (Y : FBChart C V O dd) (n : ℕ) :
    Jac (mulL Y.B.G.F n) = n • (cmp (mulL Y.B.G.F n) (JF Y.B.G) * Jac Y.lg) := by
  have h1 : cmp (mulL Y.B.G.F n) (Jac Y.lg) * cmp (mulL Y.B.G.F n) (JF Y.B.G) = 1 := by
    rw [← cmp_mul (multiplication_constantCoeff_zero Y.B.G n), JL_JF, cmp_one]
  have h2 := mul_eq_one_comm.1 h1
  rw [← Matrix.one_mul (Jac (mulL Y.B.G.F n)), ← h2, Matrix.mul_assoc, jac_mulL, Matrix.mul_smul]

end Formalism.L2.FormalSeriesBounds.MulLFrob

namespace Formalism.L2.FormalSeriesBounds

open MulLFrob MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

/- English proof (translation)
Introduce `C _ _ V O _ _ dd Y k μ hμ`. Take `⟨i, hi⟩` from `hμ`. Establish `hl` using `V.l_prime`. Establish `hm0 : μ ((0 : Fin 1), i) ≠ 0` using `fun h => hi (h ▸ dvd_zero _)`. Use `set ν := μ - Finsupp.single ((0 : Fin 1), i) 1 with hν`.

Establish `hνμ : ν + Finsupp.single ((0 : Fin 1), i) 1 = μ`. Rewrite using `[hν]`. Use `tsub_add_cancel_of_le ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_le_iff]`. Use linear arithmetic over natural numbers and integers.

Establish `hνi : ν ((0 : Fin 1), i) + 1 = μ ((0 : Fin 1), i)`. Rewrite using `[← hνμ, Finsupp.add_apply, Finsupp.single_eq_same]`. Establish `hJ` using `congrFun (congrFun (jac_l Y V.l) k) i`. Establish `hc` using `congrArg (coeff ν) hJ`. Simplify using `only [Jac] at hc`.

Rewrite `hc` using `[coeff_pderiv, hνμ, Matrix.smul_apply, map_nsmul]`. Establish `hI : IntS V ((cmp (mulL Y.B.G.F V.l) (JF Y.B.G) * Jac Y.lg) k i)`. Rewrite using `[Matrix.mul_apply]`. Use `PartialDerivEval.intS_sum _ fun j _ => PartialDerivEval.intS_mul ?_ (JL_int Y j i)` and prove the remaining obligations. Use `PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)` and prove the remaining obligations.

Use `fin_cases k'`. Conclude with `FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l j'`. Establish `hmm : V.MM (coeff μ (mulL Y.B.G.F V.l k) * ((ν ((0 : Fin 1), i) : C) + 1))`. Rewrite using `[hc, nsmul_eq_mul]`. Conclude with `GmExArith.mm_mul_int GmExArith.mm_l (hI ν)`.

Establish `hcop : IsCoprime ((V.l : ℕ) : ℤ) ((μ ((0 : Fin 1), i) : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hi)`. Take `⟨a, b, hab⟩` from `hcop`. Establish `hab' : (a : C) * (V.l : C) + (b : C) * ((μ ((0 : Fin 1), i) : ℕ) : C) = 1`. Use `congrArg (Int.cast : ℤ → C) hab` as an intermediate fact. Move the coercions through the operations in `at this`.

Conclude with `this`. Establish `hmC : ((ν ((0 : Fin 1), i) : C) + 1) = ((μ ((0 : Fin 1), i) : ℕ) : C)`. Rewrite using `[← hνi]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite `hmm` using `[hmC]`. Establish `hcint : V.Ge 0 (coeff μ (mulL Y.B.G.F V.l k))` using `FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l k μ`. Establish `e : coeff μ (mulL Y.B.G.F V.l k) = (a : C) * ((V.l : C) * coeff μ (mulL Y.B.G.F V.l k)) + (b : C) * (coeff μ (mulL Y.B.G.F V.l k) * ((μ ((0 : Fin 1), i) : ℕ) : C))`. Take the linear combination `(coeff μ (mulL Y.B.G.F V.l k)) * hab'.symm`. Rewrite using `[e]`.

Conclude with `GmExArith.mm_add (GmExArith.mm_int_mul (GmExArith.ge_intCast' a) (GmExArith.mm_mul_int GmExArith.mm_l hcint)) (GmExArith.mm_int_mul (GmExArith.ge_intCast' b) hmm)`.
-/
theorem mulLFrob_holds : MulLFrobSt := by
  intro C _ _ V O _ _ dd Y k μ hμ
  obtain ⟨i, hi⟩ := hμ
  have hl := V.l_prime
  have hm0 : μ ((0 : Fin 1), i) ≠ 0 := fun h => hi (h ▸ dvd_zero _)
  set ν := μ - Finsupp.single ((0 : Fin 1), i) 1 with hν
  have hνμ : ν + Finsupp.single ((0 : Fin 1), i) 1 = μ := by
    rw [hν]; refine tsub_add_cancel_of_le ?_
    rw [Finsupp.single_le_iff]; omega
  have hνi : ν ((0 : Fin 1), i) + 1 = μ ((0 : Fin 1), i) := by
    rw [← hνμ, Finsupp.add_apply, Finsupp.single_eq_same]
  have hJ := congrFun (congrFun (jac_l Y V.l) k) i
  have hc := congrArg (coeff ν) hJ
  simp only [Jac] at hc
  rw [coeff_pderiv, hνμ, Matrix.smul_apply, map_nsmul] at hc
  have hI : IntS V ((cmp (mulL Y.B.G.F V.l) (JF Y.B.G) * Jac Y.lg) k i) := by
    rw [Matrix.mul_apply]
    refine PartialDerivEval.intS_sum _ fun j _ => PartialDerivEval.intS_mul ?_ (JL_int Y j i)
    refine PartialDerivEval.intS_ev (PartialDerivEval.z0_1 _ (FirstUnitSeriesIntegrality.multiplication_constantCoeff_zero Y.B.G V.l)) (fun k' j' => ?_) (JF_int Y k j)
    fin_cases k'
    exact FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l j'
  have hmm : V.MM (coeff μ (mulL Y.B.G.F V.l k) * ((ν ((0 : Fin 1), i) : C) + 1)) := by
    rw [hc, nsmul_eq_mul]
    exact GmExArith.mm_mul_int GmExArith.mm_l (hI ν)
  have hcop : IsCoprime ((V.l : ℕ) : ℤ) ((μ ((0 : Fin 1), i) : ℕ) : ℤ) :=
    Nat.isCoprime_iff_coprime.2 ((Nat.Prime.coprime_iff_not_dvd hl).2 hi)
  obtain ⟨a, b, hab⟩ := hcop
  have hab' : (a : C) * (V.l : C) + (b : C) * ((μ ((0 : Fin 1), i) : ℕ) : C) = 1 := by
    have := congrArg (Int.cast : ℤ → C) hab
    push_cast at this
    exact this
  have hmC : ((ν ((0 : Fin 1), i) : C) + 1) = ((μ ((0 : Fin 1), i) : ℕ) : C) := by
    rw [← hνi]; push_cast; ring
  rw [hmC] at hmm

  have hcint : V.Ge 0 (coeff μ (mulL Y.B.G.F V.l k)) := FirstUnitSeriesIntegrality.mulL_int Y.B.G Y.intF V.l k μ
  have e : coeff μ (mulL Y.B.G.F V.l k) = (a : C) * ((V.l : C) * coeff μ (mulL Y.B.G.F V.l k)) +
      (b : C) * (coeff μ (mulL Y.B.G.F V.l k) * ((μ ((0 : Fin 1), i) : ℕ) : C)) := by
    linear_combination (coeff μ (mulL Y.B.G.F V.l k)) * hab'.symm
  rw [e]
  exact GmExArith.mm_add (GmExArith.mm_int_mul (GmExArith.ge_intCast' a) (GmExArith.mm_mul_int GmExArith.mm_l hcint))
    (GmExArith.mm_int_mul (GmExArith.ge_intCast' b) hmm)

end Formalism.L2.FormalSeriesBounds
