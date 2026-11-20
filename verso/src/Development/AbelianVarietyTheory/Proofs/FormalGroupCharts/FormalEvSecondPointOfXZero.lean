import Mathlib
import Development.AbelianVarietyTheory.Proofs.FormalGroupCharts.ConstantCoeffEv

set_option autoImplicit false

noncomputable section

open MvPowerSeries ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.FormalLog

variable {k : Type} [CommRing k] {d : ℕ}

/- English proof (translation)
Use `show constantCoeff (X (j, i) : PS k n d) = 0`. Simplify using the standard rewrite rules.
-/
theorem cc_pt {n : ℕ} (j : Fin n) (i : Fin d) : constantCoeff (pt k (n := n) d j i) = 0 := by
  show constantCoeff (X (j, i) : PS k n d) = 0
  simp

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem cc_zero {n : ℕ} (i : Fin d) : constantCoeff ((0 : Pt k n d) i) = 0 := by simp

/- English proof (translation)
Introduce `j` and use `j.elim0`.
-/
theorem CZ.nil {n : ℕ} : CZ (![] : Fin 0 → Pt k n d) := fun j => j.elim0

/- English proof (translation)
Introduce `j i`. Use `Fin.cases ?_ (fun j => ?_) j` and prove the remaining obligations. Simplify using `using hp i`. Simplify using `using ha j i`.
-/
theorem CZ.cons {m n : ℕ} {p : Pt k n d} {a : Fin m → Pt k n d} (hp : ∀ i, constantCoeff (p i) = 0) (ha : CZ a) :
    CZ (Matrix.vecCons p a) := by
  intro j i
  refine Fin.cases ?_ (fun j => ?_) j
  · simpa using hp i
  · simpa using ha j i

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pt_apply {n : ℕ} (j : Fin n) (i : Fin d) : pt k (n := n) d j i = (X (j, i) : PS k n d) := rfl

variable (G : FGLaw k d)

/- English proof (translation)
The claim follows from `G.const`.
-/
theorem cz_F : ∀ i, constantCoeff (G.F i) = 0 := G.const

/- English proof (translation)
Establish `hz : CZ (![pt k (n` using `1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)`. Establish `hs : CZ (![pt k (n` using `2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)`. Establish `h` using `congrArg (ev (n := 1) ![pt k d 0, 0]) (G.comm i)`. Rewrite `h` using `[ev_ev hz hs]`. Establish `e : (fun j c => ev (n` using `1) ![pt k d 0, 0] ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j c)) = (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := by`.

Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X hz]`. Rewrite `h` using `[e, G.unit]`. Conclude with `h.symm`.
-/
theorem formalGroupLaw_ev_x_zero (i : Fin d) : ev (n := 1) ![pt k d 0, 0] (G.F i) = (X ((0 : Fin 1), i) : PS k 1 d) := by
  have hz : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)
  have hs : CZ (![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 0) CZ.nil)
  have h := congrArg (ev (n := 1) ![pt k d 0, 0]) (G.comm i)
  rw [ev_ev hz hs] at h
  have e : (fun j c => ev (n := 1) ![pt k d 0, 0] ((![pt k (n := 2) d 1, pt k d 0] : Fin 2 → Pt k 2 d) j c)) =
      (![0, pt k (n := 1) d 0] : Fin 2 → Pt k 1 d) := by
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X hz]
  rw [e, G.unit] at h
  exact h.symm

/- English proof (translation)
Rewrite using `[pderiv_ev ha]`. Simplify using `[h]`.
-/
theorem pderiv_ev_zero {m n : ℕ} {a : Fin m → Pt k n d} (ha : CZ a) (f : PS k m d) (v : Fin n × Fin d)
    (h : ∀ j i, pderiv k v (a j i) = 0) : pderiv k v (ev a f) = 0 := by
  rw [pderiv_ev ha]; simp [h]

/- English proof (translation)
Rewrite using `[pt_apply, pderiv_X]`. Simplify using `[Pi.single_apply, eq_comm]`.
-/
theorem pderiv_pt {n : ℕ} (v : Fin n × Fin d) (j : Fin n) (i : Fin d) :
    pderiv k v (pt k (n := n) d j i) = if (j, i) = v then 1 else 0 := by
  classical
  rw [pt_apply, pderiv_X]
  simp [Pi.single_apply, eq_comm]

def Jac : Fin d → Fin d → PS k 1 d := fun i b => ev (n := 1) ![pt k d 0, 0] (pderiv k ((1 : Fin 2), b) (G.F i))

def Ar : Fin d → Fin d → PS k 2 d := fun i b => pderiv k ((1 : Fin 2), b) (G.F i)

section Fams

/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)`.
-/
theorem cz1 : CZ (![pt k (n := 1) d 0, 0] : Fin 2 → Pt k 1 d) := CZ.cons (cc_pt 0) (CZ.cons cc_zero CZ.nil)
/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 1) CZ.nil`.
-/
theorem czY : CZ (![pt k (n := 2) d 1] : Fin 1 → Pt k 2 d) := CZ.cons (cc_pt 1) CZ.nil
/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) (CZ.cons cc_zero CZ.nil))`.
-/
theorem czZ : CZ (![pt k (n := 2) d 0, pt k d 1, 0] : Fin 3 → Pt k 2 d) :=
  CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) (CZ.cons cc_zero CZ.nil))
/- English proof (translation)
The claim follows from `CZ.cons G.const CZ.nil`.
-/
theorem czFF : CZ (![G.F] : Fin 1 → Pt k 2 d) := CZ.cons G.const CZ.nil
/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)`.
-/
theorem cz01 : CZ (![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 0) (CZ.cons (cc_pt 1) CZ.nil)
/- English proof (translation)
The claim follows from `CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)`.
-/
theorem cz12 : CZ (![pt k (n := 3) d 1, pt k d 2] : Fin 2 → Pt k 3 d) := CZ.cons (cc_pt 1) (CZ.cons (cc_pt 2) CZ.nil)

end Fams

/- English proof (translation)
Rewrite using `[ev_ev czY cz1]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X czY, ev_zero' czY]`.
-/
theorem formal_ev_second_point_of_x_zero (g : PS k 2 d) :
    ev (n := 2) ![pt k d 1] (ev (n := 1) ![pt k d 0, 0] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czY cz1]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czY, ev_zero' czY]

/- English proof (translation)
Rewrite using `[ev_ev czZ cz12]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X czZ]`.
-/
theorem ev_z_yz (g : PS k 2 d) :
    ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] g) = ev (n := 2) ![pt k d 1, 0] g := by
  rw [ev_ev czZ cz12]
  congr 1
  funext j c
  fin_cases j <;> simp [pt_apply, ev_X czZ]

/- English proof (translation)
Rewrite using `[← formal_ev_second_point_of_x_zero, formalGroupLaw_ev_x_zero, ev_X czY]`. Both sides reduce to the same expression.
-/
theorem formalGroupLaw_ev_y_zero (c : Fin d) : ev (n := 2) ![pt k d 1, 0] (G.F c) = (X ((1 : Fin 2), c) : PS k 2 d) := by
  rw [← formal_ev_second_point_of_x_zero, formalGroupLaw_ev_x_zero, ev_X czY]; rfl

/- English proof (translation)
Use `set aL : Fin 2 → Pt k 3 d := ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] with haL`. Use `set aR : Fin 2 → Pt k 3 d := ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] with haR`. Establish `hL : CZ aL` using `CZ.cons (fun l => constantCoeff_ev cz01 (G.const l)) (CZ.cons (cc_pt 2) CZ.nil)`. Establish `hR : CZ aR` using `CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (G.const l)) CZ.nil)`. Establish `dL : pderiv k ((2 : Fin 3), b) (ev aL (G.F i)) = ev aL (pderiv k ((1 : Fin 2), b) (G.F i))`.

Rewrite using `[pderiv_ev hL, Fintype.sum_prod_type, Fin.sum_univ_two]`. Apply the tactic sequence `have h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aL 0 c) = 0 := fun c => pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])`. Simplify using `only [h0, mul_zero, Finset.sum_const_zero, zero_add]`. Simplify using `[haL, pderiv_pt]`. Establish `dR : pderiv k ((2 : Fin 3), b) (ev aR (G.F i)) = ∑ c, ev aR (pderiv k ((1 : Fin 2), c) (G.F i)) * ev (n` using `3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := by`.

Rewrite using `[pderiv_ev hR, Fintype.sum_prod_type, Fin.sum_univ_two]`. Establish `h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 0 c) = 0` using `fun c => by simp [haR, pderiv_pt]`. Establish `h1 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 1 c) = ev (n` using `3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := fun c => by`. Simplify using `only [haR, Matrix.cons_val_one, Matrix.cons_val_zero]`. Rewrite using `[pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]`.

Simplify using `[pderiv_pt]`. Simplify using `only [h0, h1, mul_zero, Finset.sum_const_zero, zero_add]`. Establish `h` using `congrArg (fun g => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) g)) (G.assoc i)`. Use `beta_reduce at h`. Rewrite `h` using `[dL, dR, ev_sum czZ]`.

Establish `eL : ∀ g : PS k 2 d, ev (n` using `2) ![pt k d 0, pt k d 1, 0] (ev aL g) = ev (n := 2) ![G.F, 0] g := by`. Introduce `g`. Rewrite using `[ev_ev czZ hL]`. Use `congr 1`. Use function extensionality and compare the values at `j c`.

Use `fin_cases j`. Use `show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (G.F c)) = G.F c`. Rewrite using `[ev_ev czZ cz01]`. Establish `: (fun j c => ev (n` using `2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) = fun j => pt k (n := 2) d j := by`. Apply the tactic sequence `funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]`.

Rewrite using `[this, ev_pt]`. Simplify using `[haL, pt_apply, ev_X czZ]`. Establish `eR : ∀ g : PS k 2 d, ev (n` using `2) ![pt k d 0, pt k d 1, 0] (ev aR g) = g := by`. Introduce `g`. Rewrite using `[ev_ev czZ hR]`.

Use `conv_rhs => rw [← ev_pt g]`. Use `congr 1`. Use function extensionality and compare the values at `j c`. Use `fin_cases j`. Simplify using `[haR, pt_apply, ev_X czZ]`.

Use `show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) = X ((1 : Fin 2), c)`. Rewrite using `[ev_z_yz, formalGroupLaw_ev_y_zero]`. Establish `eJ : ev (n` using `2) ![G.F] (Jac G i b) = ev (n := 2) ![G.F, 0] (pderiv k ((1 : Fin 2), b) (G.F i)) := by`. Rewrite using `[Jac, ev_ev (czFF G) cz1]`. Use `congr 1`.

Use function extensionality and compare the values at `j c`. Apply the tactic sequence `fin_cases j <;> simp [pt_apply, ev_X (czFF G), ev_zero' (czFF G)]`. Rewrite `h` using `[eL, ← eJ]`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Rewrite using `[ev_mul czZ, eR, ev_z_yz, ← formal_ev_second_point_of_x_zero]`. Both sides reduce to the same expression.
-/
theorem jac_F (i b : Fin d) :
    ev (n := 2) ![G.F] (Jac G i b) = ∑ c, Ar G i c * ev (n := 2) ![pt k d 1] (Jac G c b) := by
  set aL : Fin 2 → Pt k 3 d := ![fun l => ev (n := 3) ![pt k d 0, pt k d 1] (G.F l), pt k d 2] with haL
  set aR : Fin 2 → Pt k 3 d := ![pt k d 0, fun l => ev (n := 3) ![pt k d 1, pt k d 2] (G.F l)] with haR
  have hL : CZ aL := CZ.cons (fun l => constantCoeff_ev cz01 (G.const l)) (CZ.cons (cc_pt 2) CZ.nil)
  have hR : CZ aR := CZ.cons (cc_pt 0) (CZ.cons (fun l => constantCoeff_ev cz12 (G.const l)) CZ.nil)
  have dL : pderiv k ((2 : Fin 3), b) (ev aL (G.F i)) = ev aL (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [pderiv_ev hL, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aL 0 c) = 0 := fun c =>
      pderiv_ev_zero cz01 _ _ (fun j l => by fin_cases j <;> simp [pderiv_pt])
    simp only [h0, mul_zero, Finset.sum_const_zero, zero_add]
    simp [haL, pderiv_pt]
  have dR : pderiv k ((2 : Fin 3), b) (ev aR (G.F i)) = ∑ c, ev aR (pderiv k ((1 : Fin 2), c) (G.F i)) *
      ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := by
    rw [pderiv_ev hR, Fintype.sum_prod_type, Fin.sum_univ_two]
    have h0 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 0 c) = 0 := fun c => by simp [haR, pderiv_pt]
    have h1 : ∀ c, pderiv k ((2 : Fin 3), b) (aR 1 c) =
        ev (n := 3) ![pt k d 1, pt k d 2] (pderiv k ((1 : Fin 2), b) (G.F c)) := fun c => by
      simp only [haR, Matrix.cons_val_one, Matrix.cons_val_zero]
      rw [pderiv_ev cz12, Fintype.sum_prod_type, Fin.sum_univ_two]
      simp [pderiv_pt]
    simp only [h0, h1, mul_zero, Finset.sum_const_zero, zero_add]
  have h := congrArg (fun g => ev (n := 2) ![pt k d 0, pt k d 1, 0] (pderiv k ((2 : Fin 3), b) g)) (G.assoc i)
  beta_reduce at h
  rw [dL, dR, ev_sum czZ] at h
  have eL : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aL g) = ev (n := 2) ![G.F, 0] g := by
    intro g
    rw [ev_ev czZ hL]
    congr 1
    funext j c
    fin_cases j
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 0, pt k d 1] (G.F c)) = G.F c
      rw [ev_ev czZ cz01]
      have : (fun j c => ev (n := 2) ![pt k d 0, pt k d 1, 0] ((![pt k (n := 3) d 0, pt k d 1] : Fin 2 → Pt k 3 d) j c)) =
          fun j => pt k (n := 2) d j := by
        funext j c; fin_cases j <;> simp [pt_apply, ev_X czZ]
      rw [this, ev_pt]
    · simp [haL, pt_apply, ev_X czZ]
  have eR : ∀ g : PS k 2 d, ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev aR g) = g := by
    intro g
    rw [ev_ev czZ hR]
    conv_rhs => rw [← ev_pt g]
    congr 1
    funext j c
    fin_cases j
    · simp [haR, pt_apply, ev_X czZ]
    · show ev (n := 2) ![pt k d 0, pt k d 1, 0] (ev (n := 3) ![pt k d 1, pt k d 2] (G.F c)) = X ((1 : Fin 2), c)
      rw [ev_z_yz, formalGroupLaw_ev_y_zero]
  have eJ : ev (n := 2) ![G.F] (Jac G i b) = ev (n := 2) ![G.F, 0] (pderiv k ((1 : Fin 2), b) (G.F i)) := by
    rw [Jac, ev_ev (czFF G) cz1]
    congr 1
    funext j c
    fin_cases j <;> simp [pt_apply, ev_X (czFF G), ev_zero' (czFF G)]
  rw [eL, ← eJ] at h
  rw [h]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [ev_mul czZ, eR, ev_z_yz, ← formal_ev_second_point_of_x_zero]
  rfl

end GlobalTheory.FormalLog
