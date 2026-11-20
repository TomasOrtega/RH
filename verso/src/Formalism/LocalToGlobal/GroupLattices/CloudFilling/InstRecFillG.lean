import Formalism.LocalToGlobal.GroupLattices.CloudFilling.ExistsPowOrbRep
import Formalism.SharpRestriction.GrowthBounds.DefsInst

noncomputable section

namespace Formalism.L2.G

open Formalism.BasicNotions Formalism.FrobeniusOrbits Formalism.MainNotions.G Formalism.MainNotions.Inhab

variable {D : D7}

def cutJ (D : D7) (j : ℕ) : ℕ := max 1 (min j D.R.m)

/- English proof (translation)
Use `D.R.two_le_m` as an intermediate fact. Unfold `cutJ`. Use linear arithmetic over natural numbers and integers.
-/
theorem cutJ_mem (D : D7) (j : ℕ) : 1 ≤ cutJ D j ∧ cutJ D j ≤ D.R.m := by
  have := D.R.two_le_m
  unfold cutJ
  omega

/- English proof (translation)
Use `Finset.mem_Icc.1 hj` as an intermediate fact. Unfold `cutJ`. Use linear arithmetic over natural numbers and integers.
-/
theorem cutJ_of_mem {j : ℕ} (hj : j ∈ SizeData₂.lifts D) : cutJ D j = j := by
  have := Finset.mem_Icc.1 hj
  unfold cutJ
  omega

open Classical in

def offRec (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) : ℝ :=
  wj D (cutJ D j) (tauOf D z) - (if z.1 = false ∧ z.2 ∈ D.host.TT then (bL L z.2 : ℝ) else 0)

/- English proof (translation)
Establish `hz' : z.1 = false ∧ z.2 ∈ D.host.TT` using `hz`. Establish `h0 : (D.eTau (tauOf D z) : D.R.GG) = D.R.tau1 z.2`. Rewrite using `[eTau_tauOf, ← plGG_false]`. Use `congr 1`. Conclude with `Prod.ext hz'.1 rfl`.

Establish `h1` using `L.win_top (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z) ⟨z.2, hz'.2⟩ h0`. Establish `h2 : bL L z.2 = L.bT ⟨z.2, hz'.2⟩` using `by unfold bL; rw [dif_pos hz'.2]`. Unfold `offRec`. Rewrite using `[if_pos hz', h2]`. Apply the tactic sequence `constructor <;> linarith [h1.1, h1.2]`.
-/
theorem offRec_top (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsTopPl D z) :
    L.sc.b' / L.sc.x ≤ offRec L j z ∧ offRec L j z ≤ L.sc.b' / L.sc.x + L.etaSz := by
  have hz' : z.1 = false ∧ z.2 ∈ D.host.TT := hz
  have h0 : (D.eTau (tauOf D z) : D.R.GG) = D.R.tau1 z.2 := by
    rw [eTau_tauOf, ← plGG_false]
    congr 1
    exact Prod.ext hz'.1 rfl
  have h1 := L.win_top (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z) ⟨z.2, hz'.2⟩ h0
  have h2 : bL L z.2 = L.bT ⟨z.2, hz'.2⟩ := by unfold bL; rw [dif_pos hz'.2]
  unfold offRec
  rw [if_pos hz', h2]
  constructor <;> linarith [h1.1, h1.2]

/- English proof (translation)
Establish `hz' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT)` using `hz.1`. Establish `h1` using `L.win_thin (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z) (by`. Rewrite using `[eTau_tauOf]`. Conclude with `⟨Formalism.MainNotions.Inhab.plGG_mem_Psi D z, fun h => hz.1 ((plGG_top_iff D z).1 h), fun h => hz.2 ((plGG_thick_iff D z).1 h)⟩)`. Unfold `offRec`.

Rewrite using `[if_neg hz', sub_zero]`. Conclude with `h1`.
-/
theorem offRec_thin (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsThinPl D z) :
    L.sc.w'' D.R.n ≤ offRec L j z ∧ offRec L j z ≤ L.sc.w'' D.R.n + L.etaSz := by
  have hz' : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := hz.1
  have h1 := L.win_thin (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z)
    (by
      rw [eTau_tauOf]
      exact ⟨Formalism.MainNotions.Inhab.plGG_mem_Psi D z, fun h => hz.1 ((plGG_top_iff D z).1 h),
        fun h => hz.2 ((plGG_thick_iff D z).1 h)⟩)
  unfold offRec
  rw [if_neg hz', sub_zero]
  exact h1

/- English proof (translation)
Establish `ht : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT)` using `fun h => by`. Establish `h1` using `h.1`. Rewrite `h1` using `[hz.1]`. Conclude with `Bool.noConfusion h1`. Establish `h1` using `L.win_thick (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z) (by rw [eTau_tauOf]; exact (plGG_thick_iff D z).2 hz)`.

Unfold `offRec`. Rewrite using `[if_neg ht, sub_zero]`. Conclude with `h1`.
-/
theorem offRec_thick (L : SizeData₂ D) (j : ℕ) (z : Bool × HH D) (hz : IsThickPl D z) :
    L.sc.b ≤ offRec L j z ∧ offRec L j z ≤ L.sc.b + L.etaSz + 1 := by
  have ht : ¬ (z.1 = false ∧ z.2 ∈ D.host.TT) := fun h => by
    have h1 := h.1
    rw [hz.1] at h1
    exact Bool.noConfusion h1
  have h1 := L.win_thick (cutJ D j) (cutJ_mem D j).1 (cutJ_mem D j).2 (tauOf D z)
    (by rw [eTau_tauOf]; exact (plGG_thick_iff D z).2 hz)
  unfold offRec
  rw [if_neg ht, sub_zero]
  exact h1

def instRec (L : SizeData₂ D) (K : Consts) (Ce : ℝ) : Inst D L where
  bs := bsH D.R.toFrame
  bs_orb := bsH_orb D.R.toFrame
  bs_step := bsH_step D.R.toFrame
  off := offRec L
  off_top := offRec_top L
  off_thin := offRec_thin L
  off_thick := offRec_thick L
  kapI := fun p n' TT a b => sInf (kapISet L K p n' TT a b)
  ep := fun p => ⌈Ce * (D.R.f : ℝ) * (D.R.k : ℝ) ^ 2 * Real.logb p L.sc.a⌉₊

/- English proof (translation)
Introduce `j hj τ z h`. Rewrite using `[eq_tauOf D τ z h]`. Use `show _ + offRec L j z = _`. Unfold `offRec`. Rewrite using `[cutJ_of_mem hj]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem instRec_fill (L : SizeData₂ D) (K : Consts) (Ce : ℝ) :
    ∀ j ∈ SizeData₂.lifts D, ∀ (τ : D.what₂.Tau) (z : Bool × HH D), (D.eTau τ : D.R.GG) = plGG D z →
      fill (instRec L K Ce) (bL L) j z = wj D j τ := by
  intro j hj τ z h
  rw [eq_tauOf D τ z h]
  show _ + offRec L j z = _
  unfold offRec
  rw [cutJ_of_mem hj]
  ring

/- English proof (translation)
Unfold `fillG`. Rewrite using `[instRec_fill L K Ce j hj (D.eTau.symm (tau1P D.R.toFrame t)) (false, t) (by rw [Equiv.apply_symm_apply, plGG_false]; rfl)]`.
-/
theorem instRec_fillG (L : SizeData₂ D) (K : Consts) (Ce : ℝ) (j : ℕ) (hj : j ∈ SizeData₂.lifts D) (t : HH D) :
    fillG (instRec L K Ce) (bL L) j (false, t) = wj D j (D.eTau.symm (tau1P D.R.toFrame t)) - kaJ D j := by
  unfold fillG
  rw [instRec_fill L K Ce j hj (D.eTau.symm (tau1P D.R.toFrame t)) (false, t)
    (by rw [Equiv.apply_symm_apply, plGG_false]; rfl)]

/- English proof (translation)
Establish `hs : stepP D p = hP D p`. Unfold `stepP`. Rewrite using `[if_neg (fun h : D.host.cls p = PrimeClass.signal => by`. Establish `hc' : D.host.cls p = PrimeClass.inertClass` using `hc`. Rewrite `h` using `[hc']`.

Conclude with `PrimeClass.noConfusion h)]`. Unfold `reps`. Rewrite using `[hs]`. Simplify using `[instRec]`.
-/
theorem reps_instRec (L : SizeData₂ D) (K : Consts) (Ce : ℝ) {p : ℕ} (hc : IsResidueClassZero D p) :
    ((reps (instRec L K Ce) p : Finset (HH D)) : Set (HH D)) = Set.range (bsH D.R.toFrame (hP D p)) := by
  have hs : stepP D p = hP D p := by
    unfold stepP
    rw [if_neg (fun h : D.host.cls p = PrimeClass.signal => by
      have hc' : D.host.cls p = PrimeClass.inertClass := hc
      rw [hc'] at h; exact PrimeClass.noConfusion h)]
  unfold reps
  rw [hs]
  simp [instRec]

end Formalism.L2.G
