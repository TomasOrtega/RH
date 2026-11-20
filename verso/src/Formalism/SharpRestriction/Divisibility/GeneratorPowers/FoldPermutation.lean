import Formalism.SharpRestriction.Divisibility.GeneratorPowers.FormalGroupCopies
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.DofComm
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.TaylorDiscriminants.WickVanishing.GaugeTrans

set_option autoImplicit false

noncomputable section

namespace Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation

open MvPowerSeries Formalism.L2.Pj ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ ReciprocityTheory.ChartRestriction.G.TB
open Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupOnCopies Formalism.MainNotions.ModuliIntegralCharts.H1.PartialDerivativeExponent Formalism.MainNotions.ModuliIntegralCharts.H1.FormalGroupCopies

variable {k : Type} [CommRing k] {d : ℕ}

def embP {n' n : ℕ} (e : Fin n' → Fin n) : Fin n' → Pt k n d := fun b => pt k d (e b)

/- English proof (translation)
Introduce `j i`. Simplify using `[embP, pt]`.
-/
theorem cz_embP {n' n : ℕ} (e : Fin n' → Fin n) : LogPf.CZ (embP (k := k) (d := d) e) := by
  intro j i
  simp [embP, pt]

/- English proof (translation)
Introduce `j i`. Apply the tactic sequence `fin_cases j <;> simp [pt]`.
-/
theorem cz_ptz {n : ℕ} (b : Fin n) : LogPf.CZ (![pt k d b, 0] : Fin 2 → Pt k n d) := by
  intro j i
  fin_cases j <;> simp [pt]

/- English proof (translation)
Establish `h0 : constantCoeff (f - C (constantCoeff f)) = 0` using `by simp`. Establish `e1 : f = C (constantCoeff f) + (f - C (constantCoeff f))` using `by ring`. Use `conv_lhs => rw [e1]`. Rewrite using `[LogPf.ev_add ha, LogPf.ev_C ha, map_add, LogPf.constantCoeff_ev ha h0, add_zero, constantCoeff_C]`.
-/
theorem cc_ev {m n : ℕ} {a : Fin m → Pt k n d} (ha : LogPf.CZ a) (f : PS k m d) :
    constantCoeff (ev a f) = constantCoeff f := by
  have h0 : constantCoeff (f - C (constantCoeff f)) = 0 := by simp
  have e1 : f = C (constantCoeff f) + (f - C (constantCoeff f)) := by ring
  conv_lhs => rw [e1]
  rw [LogPf.ev_add ha, LogPf.ev_C ha, map_add, LogPf.constantCoeff_ev ha h0, add_zero, constantCoeff_C]

/- English proof (translation)
Rewrite using `[LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]`. Simplify using `[embP, LogPf.pderiv_pt]`. Introduce `p _ hp`. Rewrite using `[show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]`. Introduce `hc`.

Apply `hp` to reduce the goal to its premises. Establish `h1 : e p.1 = e b` using `congrArg Prod.fst hc`. Establish `h2 : p.2 = j` using `congrArg Prod.snd hc`. Conclude with `Prod.ext (he h1) h2`. Simplify using the standard rewrite rules.
-/
theorem pderiv_embP {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (g : PS k n' d) (b : Fin n')
    (j : Fin d) : pderiv k (e b, j) (ev (embP e) g) = ev (embP e) (pderiv k (b, j) g) := by
  classical
  rw [LogPf.pderiv_ev (cz_embP e), Finset.sum_eq_single (b, j)]
  · simp [embP, LogPf.pderiv_pt]
  · intro p _ hp
    rw [show embP (k := k) (d := d) e p.1 p.2 = pt k d (e p.1) p.2 from rfl, LogPf.pderiv_pt, if_neg, mul_zero]
    intro hc
    apply hp
    have h1 : e p.1 = e b := congrArg Prod.fst hc
    have h2 : p.2 = j := congrArg Prod.snd hc
    exact Prod.ext (he h1) h2
  · simp

/- English proof (translation)
Use `LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_` and prove the remaining obligations. Rewrite using `[show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]`. Introduce `h`. Conclude with `hc b (congrArg Prod.fst h)`.
-/
theorem pderiv_ev_embP_of_notMem_range {n' n : ℕ} (e : Fin n' → Fin n) (g : PS k n' d) (c : Fin n) (hc : ∀ b, e b ≠ c)
    (j : Fin d) : pderiv k (c, j) (ev (embP e) g) = 0 := by
  classical
  refine LogPf.pderiv_ev_zero (cz_embP e) g (c, j) fun b i => ?_
  rw [show embP (k := k) (d := d) e b i = pt k d (e b) i from rfl, LogPf.pderiv_pt, if_neg]
  intro h
  exact hc b (congrArg Prod.fst h)

/- English proof (translation)
Rewrite using `[LogPf.ev_ev (cz_embP e) (cz_ptz b)]`. Use `congr 1`. Use function extensionality and compare the values at `q i`. Use `fin_cases q`. Simplify using `[LogPf.ev_X (cz_embP e), embP, pt]`.

Simplify using `[LogPf.ev_zero' (cz_embP e)]`.
-/
theorem ev_ptz {n' n : ℕ} (e : Fin n' → Fin n) (b : Fin n') (X : PS k 2 d) :
    ev ![pt k d (e b), 0] X = ev (embP e) (ev ![pt k d b, 0] X) := by
  rw [LogPf.ev_ev (cz_embP e) (cz_ptz b)]
  congr 1
  funext q i
  fin_cases q
  · simp [LogPf.ev_X (cz_embP e), embP, pt]
  · simp [LogPf.ev_zero' (cz_embP e)]

/- English proof (translation)
Unfold `DofN`. Rewrite using `[LogPf.ev_sum (cz_embP e)]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]`.
-/
theorem dofN_embP (F : Fin d → PS k 2 d) {n' n : ℕ} (e : Fin n' → Fin n) (he : Function.Injective e) (b : Fin n')
    (u : Fin d → k) (g : PS k n' d) : DofN F (e b) u (ev (embP e) g) = ev (embP e) (DofN F b u g) := by
  unfold DofN
  rw [LogPf.ev_sum (cz_embP e)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_sum (cz_embP e), pderiv_embP e he]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [LogPf.ev_mul (cz_embP e), LogPf.ev_C (cz_embP e), ev_ptz]

section Comm

def cB (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) : Fin n × Fin d → PS k n d := fun t =>
  if t.1 = b then ev (embP (fun _ : Fin 1 => b)) (WickVanishing.Nab.co G u ((0 : Fin 1), t.2)) else 0

/- English proof (translation)
Introduce `x y _`. Conclude with `Subsingleton.elim x y`.
-/
theorem inj1 {n : ℕ} (b : Fin n) : Function.Injective (fun _ : Fin 1 => b) := by
  intro x y _
  exact Subsingleton.elim x y

/- English proof (translation)
Unfold `DofN WickVanishing.Nab.vf cB`. Rewrite using `[Fintype.sum_prod_type, Finset.sum_eq_single b]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[if_pos rfl]`. Use `congr 1`.

Unfold `WickVanishing.Nab.co`. Rewrite using `[LogPf.ev_sum (cz_embP _)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]`. Use `congr 1`.

Conclude with `ev_ptz (fun _ : Fin 1 => b) 0 _`. Introduce `c _ hc`. Conclude with `Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]`. Simplify using the standard rewrite rules.
-/
theorem dofN_vf (G : FGLaw k d) {n : ℕ} (b : Fin n) (u : Fin d → k) (g : PS k n d) :
    DofN G.F b u g = WickVanishing.Nab.vf (cB G b u) g := by
  classical
  unfold DofN WickVanishing.Nab.vf cB
  rw [Fintype.sum_prod_type, Finset.sum_eq_single b]
  · refine Finset.sum_congr rfl fun j _ => ?_
    rw [if_pos rfl]
    congr 1
    unfold WickVanishing.Nab.co
    rw [LogPf.ev_sum (cz_embP _)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [LogPf.ev_mul (cz_embP _), LogPf.ev_C (cz_embP _)]
    congr 1
    exact ev_ptz (fun _ : Fin 1 => b) 0 _
  · intro c _ hc
    exact Finset.sum_eq_zero fun j _ => by rw [if_neg hc, zero_mul]
  · simp

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h1 : t.1 = 0` using `Subsingleton.elim _ _`. Establish `hp : (embP (k` using `k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by`. Use function extensionality and compare the values at `j`. Rewrite using `[Subsingleton.elim j 0]`.

Both sides reduce to the same expression. Simplify using `only [cB, if_pos h1, hp, LogPf.ev_pt]`. Rewrite using `[show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]`.
-/
theorem cB_one (G : FGLaw k d) (u : Fin d → k) : cB G (0 : Fin 1) u = WickVanishing.Nab.co G u := by
  funext t
  have h1 : t.1 = 0 := Subsingleton.elim _ _
  have hp : (embP (k := k) (d := d) (fun _ : Fin 1 => (0 : Fin 1))) = fun j => pt k (n := 1) d j := by
    funext j
    rw [Subsingleton.elim j 0]
    rfl
  simp only [cB, if_pos h1, hp, LogPf.ev_pt]
  rw [show t = ((0 : Fin 1), t.2) from Prod.ext h1 rfl]

/- English proof (translation)
Unfold `cB`. Use `split_ifs`. Unfold `DofN`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Rewrite using `[pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]`.

Unfold `DofN`. Simplify using the standard rewrite rules.
-/
theorem dofN_cB_ne (G : FGLaw k d) {n : ℕ} (b c : Fin n) (hbc : b ≠ c) (u v : Fin d → k) (t : Fin n × Fin d) :
    DofN G.F b u (cB G c v t) = 0 := by
  unfold cB
  split_ifs
  · unfold DofN
    refine Finset.sum_eq_zero fun j _ => ?_
    rw [pderiv_ev_embP_of_notMem_range _ _ b (fun _ => Ne.symm hbc) j, mul_zero]
  · unfold DofN
    simp

/- English proof (translation)
Rewrite using `[dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]`. Establish `hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) = fun _ => (0 : PS k n d)`. Use function extensionality and compare the values at `t`. Rewrite using `[← dofN_vf G b, ← dofN_vf G b']`. Distinguish the cases in `hb : b = b'`.

Rewrite using `[← hb]`. Establish `hE : ∀ (w : Fin d → k) (X : PS k 1 d), DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X)` using `fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X`. Unfold `cB`. Distinguish the cases in `ht : t.1 = b`. Rewrite using `[if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1), dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]`.

Rewrite using `[if_neg ht, if_neg ht]`. Unfold `DofN`. Simplify using the standard rewrite rules. Rewrite using `[dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]`. Rewrite using `[hz, WickVanishing.Nab.vf_zeroc]`.
-/
theorem dofN_comm (G : FGLaw k d) {n : ℕ} (b b' : Fin n) (u v : Fin d → k) (g : PS k n d) :
    DofN G.F b u (DofN G.F b' v g) = DofN G.F b' v (DofN G.F b u g) := by
  classical
  rw [dofN_vf G b, dofN_vf G b', dofN_vf G b', dofN_vf G b, ← sub_eq_zero, WickVanishing.Nab.vf_comm]
  have hz : (fun t => WickVanishing.Nab.vf (cB G b u) (cB G b' v t) - WickVanishing.Nab.vf (cB G b' v) (cB G b u t)) =
      fun _ => (0 : PS k n d) := by
    funext t
    rw [← dofN_vf G b, ← dofN_vf G b']
    by_cases hb : b = b'
    · rw [← hb]
      have hE : ∀ (w : Fin d → k) (X : PS k 1 d),
          DofN G.F b w (ev (embP (fun _ : Fin 1 => b)) X) = ev (embP (fun _ : Fin 1 => b)) (DofN G.F 0 w X) :=
        fun w X => dofN_embP G.F (fun _ : Fin 1 => b) (inj1 b) 0 w X
      unfold cB
      by_cases ht : t.1 = b
      · rw [if_pos ht, if_pos ht, hE, hE, ← LogPf.ev_sub (cz_embP _), dofN_vf G (0 : Fin 1),
          dofN_vf G (0 : Fin 1), cB_one, cB_one, WickVanishing.Nab.co_bracket G u v, LogPf.ev_zero' (cz_embP _)]
      · rw [if_neg ht, if_neg ht]
        unfold DofN
        simp
    · rw [dofN_cB_ne G b b' hb, dofN_cB_ne G b' b (Ne.symm hb), sub_zero]
  rw [hz, WickVanishing.Nab.vf_zeroc]

end Comm

section Fold

variable {n' n : ℕ} (F : Fin d → PS k 2 d)
  (hF : ∀ (b b' : Fin n) (v v' : Fin d → k) (G : PS k n d), DofN F b v (DofN F b' v' G) = DofN F b' v' (DofN F b v G))
  (e : Fin n' → Fin n) (he : Function.Injective e) {ι ι' : Type} [Fintype ι] [Fintype ι']
  (cp : ι → Fin n) (u : ι → Fin d → k) (cp' : ι' → Fin n') (u' : ι' → Fin d → k) (φ : ι' → ι)
  (hφ : Function.Injective φ) (hcp : ∀ l, cp (φ l) = e (cp' l)) (hu : ∀ l, u (φ l) = u' l)
include hF he hφ hcp hu

end Fold

section Val

variable {R : Type} [CommRing R] {O : Type} [CommRing O] [StarRing O] (B : FB R d O) (K : Type) [CommRing K]
  [Algebra ℚ K] [Algebra R K]

end Val

end Formalism.MainNotions.ModuliIntegralCharts.H1.FoldPermutation
