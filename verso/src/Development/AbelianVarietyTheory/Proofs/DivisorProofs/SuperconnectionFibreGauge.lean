import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConnFormSmul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicConnectionAddSection
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DbarEqZeroOfHolomorphic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionContDiffOn
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SuperconnectionSmul

set_option autoImplicit false
noncomputable section
open Matrix Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe
open scoped ContDiff

namespace GlobalTheory.TorsionForm.FibreSq

open GlobalTheory.TorsionForm

section Abstract

variable {V K : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] [Fintype K] {m : ℕ}

def foOp (c : K → V → ℂ) (ε : K → Ext m →L[ℂ] Ext m) (v : K → V → V) (Z : V → Ext m →L[ℂ] Ext m)
    (t : V → Ext m) (P : V) : Ext m :=
  ∑ k, c k P • ε k (fderiv ℝ t P (v k P)) + Z P (t P)

def foComm (c : K → V → ℂ) (ε : K → Ext m →L[ℂ] Ext m) (v : K → V → V) (ρ : V → ℂ) (P : V)
    (w : Ext m) : Ext m :=
  ∑ k, (c k P * fderiv ℝ ρ P (v k P)) • ε k w

/- English proof (translation)
Establish `h1` using `hρ.hasFDerivAt.clm_apply hv.hasFDerivAt`. Establish `h2` using `hc.hasFDerivAt.mul h1`. Establish `h3 : HasFDerivAt (fun Q => ε (s Q)) ((ε.restrictScalars ℝ).comp (fderiv ℝ s P)) P` using `(ε.restrictScalars ℝ).hasFDerivAt.comp P hs.hasFDerivAt`. Establish `h4 : HasFDerivAt (fun Q => (c Q * fderiv ℝ ρ Q (v Q)) • ε (s Q)) _ P` using `h2.smul h3`. Use `⟨h4.differentiableAt, fun w => ?_⟩` and prove the remaining obligations.

Rewrite using `[h4.fderiv]`. Simplify using `only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars', ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply, Pi.mul_apply, smul_eq_mul]`. Use `module`.
-/
theorem hasFDerivAt_foComm_term (c : V → ℂ) (ε : Ext m →L[ℂ] Ext m) (v : V → V) (ρ : V → ℂ)
    (s : V → Ext m) (P : V) (hρ : DifferentiableAt ℝ (fderiv ℝ ρ) P) (hs : DifferentiableAt ℝ s P)
    (hc : DifferentiableAt ℝ c P) (hv : DifferentiableAt ℝ v P) :
    DifferentiableAt ℝ (fun Q => (c Q * fderiv ℝ ρ Q (v Q)) • ε (s Q)) P ∧ ∀ w,
      fderiv ℝ (fun Q => (c Q * fderiv ℝ ρ Q (v Q)) • ε (s Q)) P w =
        (fderiv ℝ c P w * fderiv ℝ ρ P (v P)) • ε (s P) +
        (c P * fderiv ℝ (fderiv ℝ ρ) P w (v P)) • ε (s P) +
        (c P * fderiv ℝ ρ P (fderiv ℝ v P w)) • ε (s P) +
        (c P * fderiv ℝ ρ P (v P)) • ε (fderiv ℝ s P w) := by
  have h1 := hρ.hasFDerivAt.clm_apply hv.hasFDerivAt
  have h2 := hc.hasFDerivAt.mul h1
  have h3 : HasFDerivAt (fun Q => ε (s Q)) ((ε.restrictScalars ℝ).comp (fderiv ℝ s P)) P :=
    (ε.restrictScalars ℝ).hasFDerivAt.comp P hs.hasFDerivAt
  have h4 : HasFDerivAt (fun Q => (c Q * fderiv ℝ ρ Q (v Q)) • ε (s Q)) _ P := h2.smul h3
  refine ⟨h4.differentiableAt, fun w => ?_⟩
  rw [h4.fderiv]
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_restrictScalars',
    ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.flip_apply, Pi.mul_apply, smul_eq_mul]
  module

/- English proof (translation)
The claim follows from `DifferentiableAt.fun_sum fun k _ => (hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ hs (hc k) (hv k)).1`.
-/
theorem differentiableAt_foComm (c : K → V → ℂ) (ε : K → Ext m →L[ℂ] Ext m) (v : K → V → V)
    (ρ : V → ℂ) (s : V → Ext m) (P : V) (hρ : DifferentiableAt ℝ (fderiv ℝ ρ) P)
    (hs : DifferentiableAt ℝ s P) (hc : ∀ k, DifferentiableAt ℝ (c k) P)
    (hv : ∀ k, DifferentiableAt ℝ (v k) P) :
    DifferentiableAt ℝ (fun Q => foComm c ε v ρ Q (s Q)) P :=
  DifferentiableAt.fun_sum fun k _ =>
    (hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ hs (hc k) (hv k)).1

/- English proof (translation)
Establish `hρ' : DifferentiableAt ℝ (fderiv ℝ ρ) P` using `(hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)`. Establish `hsymm` using `hρ.isSymmSndFDerivAt (by simp)`. Establish `hd : ∀ w, fderiv ℝ (fun Q => foComm c ε v ρ Q (s Q)) P w = ∑ k, ((c k P * fderiv ℝ (fderiv ℝ ρ) P w (v k P)) • ε k (s P) + (c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P w))`. Introduce `w`. Unfold `foComm`.

Rewrite using `[fderiv_fun_sum fun k _ => (hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ' hs (hc k) (hv k)).1, ContinuousLinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[(hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ' hs (hc k) (hv k)).2, h4]`. Consider the cases of `hk : vt k`. Simplify using `[h3 k hk]`.

Simplify using `[h1 k hk]`. Use `set X : Ext m := ∑ j, ∑ k, (c j P * c k P * fderiv ℝ (fderiv ℝ ρ) P (v j P) (v k P)) • ε j (ε k (s P)) with hX`. Establish `hX0 : X = 0`. Establish `: X = -X` using `by conv_rhs => rw [hX, Finset.sum_comm]`. Rewrite using `[hX, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[hsymm (v k P) (v j P), mul_comm (c k P)]`. Consider the cases of `hk : vt k`.

Rewrite using `[h5 j k hk, smul_neg]`. Consider the cases of `hj : vt j`. Rewrite using `[h5 k j hj, smul_neg, neg_neg]`. Simplify using `[h2 j k hj hk]`. Establish `h2X : (2 : ℂ) • X = 0` using `by rw [two_smul]; nth_rewrite 1 [this]; simp`.

Simplify using `using h2X`. Establish `hY : ∀ k, (c k P * fderiv ℝ ρ P (v k P)) • ε k (foOp c ε v Z s P) + (∑ j, c j P • ε j ((c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P (v j P))) + Z P ((c k P * fderiv ℝ ρ P (v k P)) • ε k (s P))) = 0`. Introduce `k`. Consider the cases of `hk : vt k`. Simplify using `only [foOp, map_add, map_sum, map_smul, h5 _ k hk, h6 k hk, smul_add, Finset.smul_sum, smul_neg, Finset.sum_neg_distrib, smul_comm (c _ P) (c k P * _)]`.

Normalize the expressions using the abelian group laws. Simplify using `[h1 k hk]`. Establish `e : foOp c ε v Z (fun Q => foComm c ε v ρ Q (s Q)) P = X + ∑ k, (∑ j, c j P • ε j ((c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P (v j P))) + Z P ((c k P * fderiv ℝ ρ P (v k P)) • ε k (s P)))`. Rewrite using `[foOp, Finset.sum_add_distrib, Finset.sum_comm, ← add_assoc, hX, ← Finset.sum_add_distrib]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hd, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Simplify using `only [map_add, map_smul, smul_add, smul_smul, mul_assoc]`. Rewrite using `[foComm, map_sum]`.

Rewrite using `[e, hX0, zero_add, foComm, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_eq_zero fun k _ => hY k`.
-/
theorem foComm_anticomm (c : K → V → ℂ) (ε : K → Ext m →L[ℂ] Ext m) (v : K → V → V)
    (Z : V → Ext m →L[ℂ] Ext m) (ρ : V → ℂ) (s : V → Ext m) (P : V) (vt : K → Bool)
    (hρ : ContDiffAt ℝ 2 ρ P) (hs : DifferentiableAt ℝ s P) (hc : ∀ k, DifferentiableAt ℝ (c k) P)
    (hv : ∀ k, DifferentiableAt ℝ (v k) P)
    (h1 : ∀ k, vt k = true → fderiv ℝ ρ P (v k P) = 0)
    (h2 : ∀ j k, vt j = true → vt k = true → fderiv ℝ (fderiv ℝ ρ) P (v j P) (v k P) = 0)
    (h3 : ∀ k, vt k = false → fderiv ℝ (c k) P = 0)
    (h4 : ∀ k w, fderiv ℝ ρ P (fderiv ℝ (v k) P w) = 0)
    (h5 : ∀ j k, vt k = false → ∀ w, ε j (ε k w) = -ε k (ε j w))
    (h6 : ∀ k, vt k = false → ∀ w, Z P (ε k w) = -ε k (Z P w)) :
    foComm c ε v ρ P (foOp c ε v Z s P) + foOp c ε v Z (fun Q => foComm c ε v ρ Q (s Q)) P = 0 := by
  have hρ' : DifferentiableAt ℝ (fderiv ℝ ρ) P :=
    (hρ.fderiv_right (m := 1) (by norm_num)).differentiableAt (by norm_num)
  have hsymm := hρ.isSymmSndFDerivAt (by simp)
  have hd : ∀ w, fderiv ℝ (fun Q => foComm c ε v ρ Q (s Q)) P w =
      ∑ k, ((c k P * fderiv ℝ (fderiv ℝ ρ) P w (v k P)) • ε k (s P) +
        (c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P w)) := by
    intro w
    unfold foComm
    rw [fderiv_fun_sum fun k _ =>
      (hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ' hs (hc k) (hv k)).1,
      ContinuousLinearMap.sum_apply]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [(hasFDerivAt_foComm_term (c k) (ε k) (v k) ρ s P hρ' hs (hc k) (hv k)).2, h4]
    cases hk : vt k
    · simp [h3 k hk]
    · simp [h1 k hk]

  set X : Ext m := ∑ j, ∑ k,
    (c j P * c k P * fderiv ℝ (fderiv ℝ ρ) P (v j P) (v k P)) • ε j (ε k (s P)) with hX
  have hX0 : X = 0 := by
    have : X = -X := by
      conv_rhs => rw [hX, Finset.sum_comm]
      rw [hX, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      rw [hsymm (v k P) (v j P), mul_comm (c k P)]
      cases hk : vt k
      · rw [h5 j k hk, smul_neg]
      · cases hj : vt j
        · rw [h5 k j hj, smul_neg, neg_neg]
        · simp [h2 j k hj hk]
    have h2X : (2 : ℂ) • X = 0 := by rw [two_smul]; nth_rewrite 1 [this]; simp
    simpa using h2X
  have hY : ∀ k, (c k P * fderiv ℝ ρ P (v k P)) • ε k (foOp c ε v Z s P) +
      (∑ j, c j P • ε j ((c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P (v j P))) +
        Z P ((c k P * fderiv ℝ ρ P (v k P)) • ε k (s P))) = 0 := by
    intro k
    cases hk : vt k
    · simp only [foOp, map_add, map_sum, map_smul, h5 _ k hk, h6 k hk, smul_add, Finset.smul_sum,
        smul_neg, Finset.sum_neg_distrib, smul_comm (c _ P) (c k P * _)]
      abel
    · simp [h1 k hk]
  have e : foOp c ε v Z (fun Q => foComm c ε v ρ Q (s Q)) P = X +
      ∑ k, (∑ j, c j P • ε j ((c k P * fderiv ℝ ρ P (v k P)) • ε k (fderiv ℝ s P (v j P))) +
        Z P ((c k P * fderiv ℝ ρ P (v k P)) • ε k (s P))) := by
    rw [foOp, Finset.sum_add_distrib, Finset.sum_comm, ← add_assoc, hX, ← Finset.sum_add_distrib]
    congr 1
    · refine Finset.sum_congr rfl fun j _ => ?_
      rw [hd, map_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun k _ => ?_
      simp only [map_add, map_smul, smul_add, smul_smul, mul_assoc]
    · rw [foComm, map_sum]
  rw [e, hX0, zero_add, foComm, ← Finset.sum_add_distrib]
  exact Finset.sum_eq_zero fun k _ => hY k

end Abstract

abbrev Idx (n g : ℕ) : Type := (Fin n × Bool × Bool) ⊕ ((Fin g × Bool) ⊕ (Fin g × Fin g × Bool))

def half (d r : Bool) : ℂ := if r then (if d then Complex.I / 2 else -(Complex.I / 2)) else 1 / 2

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {g n : ℕ}

def scC (n : ℕ) (τ : E → Matrix (Fin g) (Fin g) ℂ) (u : ℝ) : Idx n g → Pt E g → ℂ
  | .inl (_, d, r) => fun _ => half d r
  | .inr (.inl (_, r)) => fun _ => (Real.sqrt u : ℂ) * half true r
  | .inr (.inr (a, c, r)) => fun P => -((Real.sqrt u : ℂ) * (2 * imPart τ P.1 a c)) * half false r

def scE (n g : ℕ) : Idx n g → Ext (n + n + g) →L[ℂ] Ext (n + n + g)
  | .inl (i, d, _) => wedgeL (if d then dtb g i else dt g i)
  | .inr (.inl (a, _)) => wedgeL (dzb n a)
  | .inr (.inr (_, c, _)) => contrL (dzb n c)

def scV (τ : E → Matrix (Fin g) (Fin g) ℂ) (β : Fin n → E) : Idx n g → Pt E g → Pt E g
  | .inl (i, _, r) => fun P => if r then Complex.I • hor τ P (β i) else hor τ P (β i)
  | .inr (.inl (a, r)) => fun _ => if r then Complex.I • vert E a else vert E a
  | .inr (.inr (a, _, r)) => fun _ => if r then Complex.I • vert E a else vert E a

def connFormL (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) :
    Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  ∑ a, ∑ c, ((Matrix.of fun a e => d01 (fun b' => imPart τ b' a e) b v) * (imPart τ b)⁻¹) a c •
    (wedgeL (dzb n c)).comp (contrL (dzb n a))

/- English proof (translation)
Simplify using `[connFormL, connForm, ContinuousLinearMap.sum_apply]`.
-/
theorem connFormL_apply (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) (w : Ext (n + n + g)) :
    connFormL τ b v w = connForm τ b v w := by
  simp [connFormL, connForm, ContinuousLinearMap.sum_apply]

def scZ (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (P : Pt E g) :
    Ext (n + n + g) →L[ℂ] Ext (n + n + g) :=
  ∑ i, (d10 (fun Q => (Real.log (h Q) : ℂ)) P (hor τ P (β i)) • wedgeL (dt g i) +
      (wedgeL (dtb g i)).comp (connFormL τ P.1 (β i))) -
    (Real.sqrt u : ℂ) • ∑ a, ∑ c, (2 * imPart τ P.1 a c *
      d10 (fun Q => (Real.log (h Q) : ℂ)) P (vert E a)) • contrL (dzb n c)

/- English proof (translation)
Simplify using `only [d10, half]`. Simplify using `only [Bool.false_eq_true, if_false, if_true]`. Use `module`.
-/
theorem dholo_half {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (f : Pt E g → W) (P v : Pt E g) :
    d10 f P v = half false false • fderiv ℝ f P v + half false true • fderiv ℝ f P (Complex.I • v) := by
  simp only [d10, half]; simp only [Bool.false_eq_true, if_false, if_true]; module

/- English proof (translation)
Simplify using `only [d01, half]`. Simplify using `only [Bool.false_eq_true, if_false, if_true]`. Use `module`.
-/
theorem dbar_half {W : Type} [NormedAddCommGroup W] [NormedSpace ℂ W] (f : Pt E g → W) (P v : Pt E g) :
    d01 f P v = half true false • fderiv ℝ f P v + half true true • fderiv ℝ f P (Complex.I • v) := by
  simp only [d01, half]; simp only [Bool.false_eq_true, if_false, if_true]; module

/- English proof (translation)
Simplify using `only [Gauge.commOp, foComm, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool, scC, scE, scV, dholo_half, dbar_half, wedgeL_apply, contrL_apply, Bool.false_eq_true, if_true, if_false, smul_eq_mul, smul_add, smul_neg, Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_d …`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by module`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => by module`.

Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by module`.
-/
theorem commOp_eq (τ : E → Matrix (Fin g) (Fin g) ℂ) (β : Fin n → E) (u : ℝ) (ρ : Pt E g → ℂ)
    (P : Pt E g) (w : Ext (n + n + g)) :
    Gauge.commOp τ β u ρ P w = foComm (scC n τ u) (scE n g) (scV τ β) ρ P w := by
  simp only [Gauge.commOp, foComm, Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_bool,
    scC, scE, scV, dholo_half, dbar_half, wedgeL_apply, contrL_apply, Bool.false_eq_true, if_true, if_false,
    smul_eq_mul, smul_add, smul_neg, Finset.smul_sum, sub_eq_add_neg, ← Finset.sum_neg_distrib]
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by module
  congr 1
  · exact Finset.sum_congr rfl fun i _ => by module
  · exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by module

/- English proof (translation)
Establish `e1 : nablaE τ h β t P = ∑ i, (∑ d, ∑ r, scC n τ u (.inl (i, d, r)) P • scE n g (.inl (i, d, r)) (fderiv ℝ t P (scV τ β (.inl (i, d, r)) P))) + ∑ i, (d10 (fun Q => (Real.log (h Q) : ℂ)) P (hor τ P (β i)) • wedge (dt g i) (t P) + wedge (dtb g i) (connForm τ P.1 (β i) (t P)))`. Rewrite using `[nablaE, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [pointDifference, dholo_half t, dbar_half t, Fintype.sum_bool, scC, scE, scV, wedgeL_apply, Bool.false_eq_true, if_true, if_false, wedge_add, wedge_smul]`. Use `module`.

Establish `e2 : (Real.sqrt u : ℂ) • dbarV t P = ∑ a, ∑ r, scC n τ u (.inr (.inl (a, r))) P • scE n g (.inr (.inl (a, r))) (fderiv ℝ t P (scV τ β (.inr (.inl (a, r))) P))`. Rewrite using `[dbarV, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [dbar_half t, Fintype.sum_bool, scC, scE, scV, wedgeL_apply, Bool.false_eq_true, if_true, if_false, wedge_add, wedge_smul]`. Use `module`.

Establish `e3 : (Real.sqrt u : ℂ) • dbarAdj τ h t P = ∑ a, ∑ c, ∑ r, scC n τ u (.inr (.inr (a, c, r))) P • scE n g (.inr (.inr (a, c, r))) (fderiv ℝ t P (scV τ β (.inr (.inr (a, c, r))) P)) - (Real.sqrt u : ℂ) • ∑ a, ∑ c, (2 * imPart τ P.1 a c * d10 (fun Q => (Real.log (h Q) : ℂ)) P (vert E …`. Rewrite using `[dbarAdj, ← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations.

Simplify using `only [pointDifference, dholo_half t, Fintype.sum_bool, scC, scE, scV, contrL_apply, Bool.false_eq_true, if_true, if_false, contr_add, contr_smul]`. Use `module`. Rewrite using `[superconn, smul_add, e1, e2, e3]`. Simplify using `only [foOp, Fintype.sum_sum_type, Fintype.sum_prod_type, scZ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, wedgeL_apply, contrL_apply, connFormL_apply]`. Normalize the expressions using the abelian group laws.
-/
theorem superconn_eq (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (t : Pt E g → Ext (n + n + g)) (P : Pt E g) :
    superconn τ h β u t P = foOp (scC n τ u) (scE n g) (scV τ β) (scZ τ h β u) t P := by
  have e1 : nablaE τ h β t P = ∑ i, (∑ d, ∑ r, scC n τ u (.inl (i, d, r)) P •
      scE n g (.inl (i, d, r)) (fderiv ℝ t P (scV τ β (.inl (i, d, r)) P))) +
      ∑ i, (d10 (fun Q => (Real.log (h Q) : ℂ)) P (hor τ P (β i)) • wedge (dt g i) (t P) +
        wedge (dtb g i) (connForm τ P.1 (β i) (t P))) := by
    rw [nablaE, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [pointDifference, dholo_half t, dbar_half t, Fintype.sum_bool, scC, scE, scV, wedgeL_apply,
      Bool.false_eq_true, if_true, if_false, wedge_add, wedge_smul]
    module
  have e2 : (Real.sqrt u : ℂ) • dbarV t P = ∑ a, ∑ r, scC n τ u (.inr (.inl (a, r))) P •
      scE n g (.inr (.inl (a, r))) (fderiv ℝ t P (scV τ β (.inr (.inl (a, r))) P)) := by
    rw [dbarV, Finset.smul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    simp only [dbar_half t, Fintype.sum_bool, scC, scE, scV, wedgeL_apply,
      Bool.false_eq_true, if_true, if_false, wedge_add, wedge_smul]
    module
  have e3 : (Real.sqrt u : ℂ) • dbarAdj τ h t P =
      ∑ a, ∑ c, ∑ r, scC n τ u (.inr (.inr (a, c, r))) P •
        scE n g (.inr (.inr (a, c, r))) (fderiv ℝ t P (scV τ β (.inr (.inr (a, c, r))) P)) -
      (Real.sqrt u : ℂ) • ∑ a, ∑ c, (2 * imPart τ P.1 a c *
        d10 (fun Q => (Real.log (h Q) : ℂ)) P (vert E a)) • contr (dzb n c) (t P) := by
    rw [dbarAdj, ← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Finset.sum_neg_distrib, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [pointDifference, dholo_half t, Fintype.sum_bool, scC, scE, scV, contrL_apply,
      Bool.false_eq_true, if_true, if_false, contr_add, contr_smul]
    module
  rw [superconn, smul_add, e1, e2, e3]
  simp only [foOp, Fintype.sum_sum_type, Fintype.sum_prod_type, scZ, ContinuousLinearMap.sub_apply,
    ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, wedgeL_apply, contrL_apply, connFormL_apply]
  abel

/- English proof (translation)
Introduce `e`. Use `congrArg Fin.val e` as an intermediate fact. Establish `hi` using `i.2`. Apply the tactic sequence `cases d <;> simp [dt, dtb, dzb] at this <;> omega`.
-/
theorem base_ne (i : Fin n) (d : Bool) (a : Fin g) : (if d then dtb g i else dt g i) ≠ dzb n a := by
  intro e
  have := congrArg Fin.val e
  have hi := i.2
  cases d <;> simp [dt, dtb, dzb] at this <;> omega

/- English proof (translation)
Rewrite using `[FlatAcyc.wedge_contr_of_ne hij, neg_neg]`.
-/
theorem contr_wedge_of_ne {m : ℕ} {i j : Fin m} (hij : i ≠ j) (w : Ext m) :
    contr j (wedge i w) = -wedge i (contr j w) := by
  rw [FlatAcyc.wedge_contr_of_ne hij, neg_neg]

/- English proof (translation)
Take `⟨i, d, r⟩` from `k`. Break down `j with ⟨i', d', r'⟩ | ⟨a, r'⟩ | ⟨a, c, r'⟩` into its components or cases. Conclude with `FlatAcyc.wedge_wedge _ _ _`. Conclude with `FlatAcyc.wedge_wedge _ _ _`. Conclude with `contr_wedge_of_ne (base_ne i d c) w`.
-/
theorem scE_anticomm (j : Idx n g) (k : Fin n × Bool × Bool) (w : Ext (n + n + g)) :
    scE n g j (scE n g (.inl k) w) = -scE n g (.inl k) (scE n g j w) := by
  obtain ⟨i, d, r⟩ := k
  rcases j with ⟨i', d', r'⟩ | ⟨a, r'⟩ | ⟨a, c, r'⟩
  · exact FlatAcyc.wedge_wedge _ _ _
  · exact FlatAcyc.wedge_wedge _ _ _
  · exact contr_wedge_of_ne (base_ne i d c) w

/- English proof (translation)
Simplify using `only [connFormL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use `congr 1`. Establish `: contrL (dzb n a) (wedgeL i w) = -wedgeL i (contrL (dzb n a) w)` using `contr_wedge_of_ne (hi a) w`. Rewrite using `[this, map_neg]`.

Simplify using `only [wedgeL_apply]`. Rewrite using `[FlatAcyc.wedge_wedge, neg_neg]`.
-/
theorem connFormL_wedge (τ : E → Matrix (Fin g) (Fin g) ℂ) (b v : E) {i : Fin (n + n + g)}
    (hi : ∀ a, i ≠ dzb n a) (w : Ext (n + n + g)) :
    connFormL τ b v (wedgeL i w) = wedgeL i (connFormL τ b v w) := by
  simp only [connFormL, ContinuousLinearMap.sum_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.comp_apply, map_sum, map_smul]
  refine Finset.sum_congr rfl fun a _ => Finset.sum_congr rfl fun c _ => ?_
  congr 1
  have : contrL (dzb n a) (wedgeL i w) = -wedgeL i (contrL (dzb n a) w) := contr_wedge_of_ne (hi a) w
  rw [this, map_neg]
  simp only [wedgeL_apply]
  rw [FlatAcyc.wedge_wedge, neg_neg]

/- English proof (translation)
Take `⟨i, d, r⟩` from `k`. Establish `hi` using `base_ne (g := g) i d`. Simplify using `only [scE]`. Generalize the expression as in `(if d then dtb g i else dt g i) = e at hi`. Establish `h1 : ∀ j x, wedgeL j (wedgeL e x) = -wedgeL e (wedgeL j x)` using `fun j x => FlatAcyc.wedge_wedge _ _ _`.

Establish `h2 : ∀ c x, contrL (dzb n c) (wedgeL e x) = -wedgeL e (contrL (dzb n c) x)` using `fun c x => contr_wedge_of_ne (hi c) x`. Simplify using `only [scZ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, connFormL_wedge τ _ _ hi, h1, h2, map_sub, map_sum, map_add, map_smul, smul_neg, Finset.sum_neg_distrib, Finset. …`. Normalize the expressions using the abelian group laws.
-/
theorem scZ_anticomm (τ : E → Matrix (Fin g) (Fin g) ℂ) (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ)
    (P : Pt E g) (k : Fin n × Bool × Bool) (w : Ext (n + n + g)) :
    scZ τ h β u P (scE n g (.inl k) w) = -scE n g (.inl k) (scZ τ h β u P w) := by
  obtain ⟨i, d, r⟩ := k
  have hi := base_ne (g := g) i d
  simp only [scE]
  generalize (if d then dtb g i else dt g i) = e at hi
  have h1 : ∀ j x, wedgeL j (wedgeL e x) = -wedgeL e (wedgeL j x) := fun j x =>
    FlatAcyc.wedge_wedge _ _ _
  have h2 : ∀ c x, contrL (dzb n c) (wedgeL e x) = -wedgeL e (contrL (dzb n c) x) := fun c x =>
    contr_wedge_of_ne (hi c) x
  simp only [scZ, ContinuousLinearMap.sub_apply, ContinuousLinearMap.sum_apply,
    ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply,
    connFormL_wedge τ _ _ hi, h1, h2, map_sub, map_sum, map_add, map_smul, smul_neg,
    Finset.sum_neg_distrib, Finset.sum_add_distrib]
  abel

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun y => f (b, y)) ((fderiv ℝ f (b, z)).comp (ContinuousLinearMap.inr ℝ E (Fin g → ℂ))) z` using `hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right b z)`. Establish `h2 : HasFDerivAt (fun y => f (b, y)) (0 : (Fin g → ℂ) →L[ℝ] W) z`. Simplify using `only [hf]`. Conclude with `hasFDerivAt_const x z`. Establish `h3` using `congrArg (fun L => L w.2) (h1.unique h2)`.

Establish `e : w = (0, w.2)` using `Prod.ext hw rfl`. Rewrite using `[e]`. Simplify using `using h3`.
-/
theorem fderiv_vert_eq_zero {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Pt E g → W}
    {b : E} {x : W} (hf : ∀ y, f (b, y) = x) {z : Fin g → ℂ} (hd : DifferentiableAt ℝ f (b, z))
    {w : Pt E g} (hw : w.1 = 0) : fderiv ℝ f (b, z) w = 0 := by
  have h1 : HasFDerivAt (fun y => f (b, y))
      ((fderiv ℝ f (b, z)).comp (ContinuousLinearMap.inr ℝ E (Fin g → ℂ))) z :=
    hd.hasFDerivAt.comp z (hasFDerivAt_prodMk_right b z)
  have h2 : HasFDerivAt (fun y => f (b, y)) (0 : (Fin g → ℂ) →L[ℝ] W) z := by
    simp only [hf]; exact hasFDerivAt_const x z
  have h3 := congrArg (fun L => L w.2) (h1.unique h2)
  have e : w = (0, w.2) := Prod.ext hw rfl
  rw [e]
  simpa using h3

/- English proof (translation)
Establish `h1 : HasFDerivAt (fun Q => (v Q).1) _ P` using `hd.hasFDerivAt.fst`. Establish `h2 : HasFDerivAt (fun Q => (v Q).1) (0 : Pt E g →L[ℝ] E) P`. Simplify using `only [hv]`. Conclude with `hasFDerivAt_const x P`. Simplify using `using congrArg (fun L => L w) (h1.unique h2)`.
-/
theorem fderiv_fst_eq_zero {v : Pt E g → Pt E g} {x : E} (hv : ∀ Q, (v Q).1 = x) {P : Pt E g}
    (hd : DifferentiableAt ℝ v P) (w : Pt E g) : (fderiv ℝ v P w).1 = 0 := by
  have h1 : HasFDerivAt (fun Q => (v Q).1) _ P := hd.hasFDerivAt.fst
  have h2 : HasFDerivAt (fun Q => (v Q).1) (0 : Pt E g →L[ℝ] E) P := by
    simp only [hv]; exact hasFDerivAt_const x P
  simpa using congrArg (fun L => L w) (h1.unique h2)

/- English proof (translation)
Break down `k with ⟨a, r⟩ | ⟨a, c, r⟩` into its components or cases. Apply the tactic sequence `exact ⟨if r then Complex.I • vert E a else vert E a, by cases r <;> simp [vert], rfl⟩`. Apply the tactic sequence `exact ⟨if r then Complex.I • vert E a else vert E a, by cases r <;> simp [vert], rfl⟩`.
-/
theorem scV_vert (τ : E → Matrix (Fin g) (Fin g) ℂ) (β : Fin n → E)
    (k : (Fin g × Bool) ⊕ (Fin g × Fin g × Bool)) :
    ∃ w : Pt E g, w.1 = 0 ∧ scV τ β (.inr k) = fun _ => w := by
  rcases k with ⟨a, r⟩ | ⟨a, c, r⟩
  · exact ⟨if r then Complex.I • vert E a else vert E a, by cases r <;> simp [vert], rfl⟩
  · exact ⟨if r then Complex.I • vert E a else vert E a, by cases r <;> simp [vert], rfl⟩

/- English proof (translation)
Break down `k with ⟨i, d, r⟩ | k` into its components or cases. Consider the cases of `r`. Conclude with `⟨β i, fun Q => by simp [scV, hor]⟩`. Conclude with `⟨Complex.I • β i, fun Q => by simp [scV, hor]⟩`. Take `⟨w, hw, e⟩` from `scV_vert τ β k`.

Conclude with `⟨0, fun Q => by rw [e]; exact hw⟩`.
-/
theorem scV_fst (τ : E → Matrix (Fin g) (Fin g) ℂ) (β : Fin n → E) (k : Idx n g) :
    ∃ x, ∀ Q, (scV τ β k Q).1 = x := by
  rcases k with ⟨i, d, r⟩ | k
  · cases r
    · exact ⟨β i, fun Q => by simp [scV, hor]⟩
    · exact ⟨Complex.I • β i, fun Q => by simp [scV, hor]⟩
  · obtain ⟨w, hw, e⟩ := scV_vert τ β k
    exact ⟨0, fun Q => by rw [e]; exact hw⟩

variable [FiniteDimensional ℂ E] {B : Set E} {τ : E → Matrix (Fin g) (Fin g) ℂ}

/- English proof (translation)
Break down `k with ⟨i, d, r⟩ | k` into its components or cases. Consider the cases of `r`. Conclude with `SuperconnSmooth.hor_cd hτ (β i)`. Conclude with `(contDiffOn_const (c := Complex.I)).smul (SuperconnSmooth.hor_cd hτ (β i))`. Take `⟨w, -, e⟩` from `scV_vert τ β k`.

Rewrite using `[e]`. Conclude with `contDiffOn_const`.
-/
theorem scV_contDiffOn (hτ : IsPeriodMap B τ) (β : Fin n → E) (k : Idx n g) :
    ContDiffOn ℝ ∞ (scV τ β k) (cov B g) := by
  rcases k with ⟨i, d, r⟩ | k
  · cases r
    · exact SuperconnSmooth.hor_cd hτ (β i)
    · exact (contDiffOn_const (c := Complex.I)).smul (SuperconnSmooth.hor_cd hτ (β i))
  · obtain ⟨w, -, e⟩ := scV_vert τ β k
    rw [e]; exact contDiffOn_const

/- English proof (translation)
Break down `k with ⟨i, d, r⟩ | ⟨a, r⟩ | ⟨a, c, r⟩` into its components or cases. Conclude with `contDiffOn_const`. Conclude with `contDiffOn_const`. Establish `hIm : ContDiffOn ℝ ∞ (fun P : Pt E g => imPart τ P.1 a c) (cov B g)`. Use `Complex.ofRealCLM.contDiff.comp_contDiffOn (GlobalTheory.ThetaMetSmooth.im_smooth hτ a c)` as an intermediate fact.

Simplify `this` using `[imPart, Function.comp_def]`. Conclude with `(contDiffOn_const.mul (contDiffOn_const.mul hIm)).neg.mul contDiffOn_const`.
-/
theorem scC_contDiffOn (hτ : IsPeriodMap B τ) (u : ℝ) (k : Idx n g) :
    ContDiffOn ℝ ∞ (scC n τ u k) (cov B g) := by
  rcases k with ⟨i, d, r⟩ | ⟨a, r⟩ | ⟨a, c, r⟩
  · exact contDiffOn_const
  · exact contDiffOn_const
  · have hIm : ContDiffOn ℝ ∞ (fun P : Pt E g => imPart τ P.1 a c) (cov B g) := by
      have := Complex.ofRealCLM.contDiff.comp_contDiffOn (GlobalTheory.ThetaMetSmooth.im_smooth hτ a c)
      simpa [imPart, Function.comp_def] using this
    exact (contDiffOn_const.mul (contDiffOn_const.mul hIm)).neg.mul contDiffOn_const

/- English proof (translation)
Introduce `E _ _ _ g n B τ h β u ρ s hτ hh hpos hρ hs b hb hρ1 z`. Establish `hU` using `SuperconnSmooth.isOpen_cov (g := g) hτ`. Establish `hnhds : ∀ y, cov B g ∈ 𝓝 ((b, y) : Pt E g)` using `fun y => hU.mem_nhds ⟨hb, trivial⟩`. Establish `hdiff : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Pt E g → W}, ContDiffOn ℝ ∞ f (cov B g) → ∀ y, DifferentiableAt ℝ f (b, y)` using `fun hf y => (hf.contDiffAt (hnhds y)).differentiableAt (by simp)`. Establish `hBs` using `hdiff (SuperconnSmooth.superconn_contDiffOn E g n B τ h β u s hτ hh hpos hs) z`.

Establish `hdρ : ContDiffOn ℝ ∞ (fderiv ℝ ρ) (cov B g)` using `hρ.fderiv_of_isOpen (m := ∞) hU (by simp)`. Establish `hc` using `fun k => hdiff (scC_contDiffOn (n := n) hτ u k) z`. Establish `hv` using `fun k => hdiff (scV_contDiffOn hτ β k) z`. Establish `hvert : ∀ y (w : Pt E g), w.1 = 0 → fderiv ℝ ρ (b, y) w = 0` using `fun y w hw => fderiv_vert_eq_zero hρ1 (hdiff hρ y) hw`. Establish `hφ` using `differentiableAt_foComm (scC n τ u) (scE n g) (scV τ β) ρ s (b, z) (hdiff hdρ z) (hdiff hs z) hc hv`.

Establish `key` using `foComm_anticomm (scC n τ u) (scE n g) (scV τ β) (scZ τ h β u) ρ s (b, z) Sum.isRight ((hρ.contDiffAt (hnhds z)).of_le (by norm_cast)) (hdiff hs z) hc hv ?_ ?_ ?_ ?_ ?_ ?_`. Establish `hρBs : DifferentiableAt ℝ (fun Q => ρ Q • superconn τ h β u s Q) (b, z)` using `(hdiff hρ z).smul hBs`. Simplify using `only [commOp_eq]`. Rewrite using `[superconn_add τ h β u hρBs hφ, Gauge.superconn_smul E g n τ h β u ρ _ _ (hdiff hρ z) hBs, hρ1, one_smul, add_assoc (superconn τ h β u _ _), commOp_eq, superconn_eq τ h β u s, superconn_eq τ h β u (fun Q => foComm _ _ _ _ _ _), key, add_zero]`. Introduce and unpack `(k | k) hk`.

Simplify using `at hk`. Take `⟨w, hw, e⟩` from `scV_vert τ β k`. Rewrite using `[e]`. Conclude with `hvert z w hw`. Apply the tactic sequence `rintro (j | j) (k | k) hj hk <;> try simp at hj hk`.

Take `⟨w, hw, e⟩` from `scV_vert τ β j`. Take `⟨w', hw', e'⟩` from `scV_vert τ β k`. Rewrite using `[e, e']`. Establish `h1` using `((hdiff hdρ z).hasFDerivAt.clm_apply (hasFDerivAt_const w' (b, z))).fderiv`. Establish `h2` using `fderiv_vert_eq_zero (f := fun Q => fderiv ℝ ρ Q w') (fun y => hvert y w' hw') ((hdiff hdρ z).clm_apply (differentiableAt_const w')) hw`.

Rewrite `h2` using `[h1]`. Simplify using `using h2`. Introduce and unpack `(⟨i, d, r⟩ | k) hk`. Conclude with `fderiv_const_apply _`. Simplify using `at hk`.

Introduce `k w`. Take `⟨x, hx⟩` from `scV_fst τ β k`. Conclude with `hvert z _ (fderiv_fst_eq_zero hx (hv k) w)`. Introduce and unpack `j (k | k) hk w`. Conclude with `scE_anticomm j k w`.

Simplify using `at hk`. Introduce and unpack `(k | k) hk w`. Conclude with `scZ_anticomm τ h β u _ k w`. Simplify using `at hk`.
-/
theorem superconn_sq_fibre : ∀ (E : Type) [NormedAddCommGroup E] [NormedSpace ℂ E]
    [FiniteDimensional ℂ E] (g n : ℕ) (B : Set E) (τ : E → Matrix (Fin g) (Fin g) ℂ)
    (h : Pt E g → ℝ) (β : Fin n → E) (u : ℝ) (ρ : Pt E g → ℂ) (s : Pt E g → Ext (n + n + g)),
    IsPeriodMap B τ → ContDiffOn ℝ ∞ h (cov B g) → (∀ P ∈ cov B g, 0 < h P) →
    ContDiffOn ℝ ∞ ρ (cov B g) → ContDiffOn ℝ ∞ s (cov B g) → ∀ b ∈ B, (∀ y, ρ (b, y) = 1) → ∀ z,
      superconn τ h β u (fun Q => ρ Q • superconn τ h β u s Q + Gauge.commOp τ β u ρ Q (s Q)) (b, z) =
        superconn τ h β u (superconn τ h β u s) (b, z) := by
  intro E _ _ _ g n B τ h β u ρ s hτ hh hpos hρ hs b hb hρ1 z
  have hU := SuperconnSmooth.isOpen_cov (g := g) hτ
  have hnhds : ∀ y, cov B g ∈ 𝓝 ((b, y) : Pt E g) := fun y => hU.mem_nhds ⟨hb, trivial⟩
  have hdiff : ∀ {W : Type} [NormedAddCommGroup W] [NormedSpace ℝ W] {f : Pt E g → W},
      ContDiffOn ℝ ∞ f (cov B g) → ∀ y, DifferentiableAt ℝ f (b, y) := fun hf y =>
    (hf.contDiffAt (hnhds y)).differentiableAt (by simp)
  have hBs := hdiff (SuperconnSmooth.superconn_contDiffOn E g n B τ h β u s hτ hh hpos hs) z
  have hdρ : ContDiffOn ℝ ∞ (fderiv ℝ ρ) (cov B g) := hρ.fderiv_of_isOpen (m := ∞) hU (by simp)
  have hc := fun k => hdiff (scC_contDiffOn (n := n) hτ u k) z
  have hv := fun k => hdiff (scV_contDiffOn hτ β k) z
  have hvert : ∀ y (w : Pt E g), w.1 = 0 → fderiv ℝ ρ (b, y) w = 0 := fun y w hw =>
    fderiv_vert_eq_zero hρ1 (hdiff hρ y) hw
  have hφ := differentiableAt_foComm (scC n τ u) (scE n g) (scV τ β) ρ s (b, z) (hdiff hdρ z)
    (hdiff hs z) hc hv
  have key := foComm_anticomm (scC n τ u) (scE n g) (scV τ β) (scZ τ h β u) ρ s (b, z) Sum.isRight
    ((hρ.contDiffAt (hnhds z)).of_le (by norm_cast)) (hdiff hs z) hc hv ?_ ?_ ?_ ?_ ?_ ?_
  · have hρBs : DifferentiableAt ℝ (fun Q => ρ Q • superconn τ h β u s Q) (b, z) :=
      (hdiff hρ z).smul hBs
    simp only [commOp_eq]
    rw [superconn_add τ h β u hρBs hφ, Gauge.superconn_smul E g n τ h β u ρ _ _ (hdiff hρ z) hBs,
      hρ1, one_smul, add_assoc (superconn τ h β u _ _), commOp_eq, superconn_eq τ h β u s,
      superconn_eq τ h β u (fun Q => foComm _ _ _ _ _ _), key, add_zero]
  · rintro (k | k) hk
    · simp at hk
    · obtain ⟨w, hw, e⟩ := scV_vert τ β k
      rw [e]; exact hvert z w hw
  · rintro (j | j) (k | k) hj hk <;> try simp at hj hk
    obtain ⟨w, hw, e⟩ := scV_vert τ β j
    obtain ⟨w', hw', e'⟩ := scV_vert τ β k
    rw [e, e']
    have h1 := ((hdiff hdρ z).hasFDerivAt.clm_apply (hasFDerivAt_const w' (b, z))).fderiv
    have h2 := fderiv_vert_eq_zero (f := fun Q => fderiv ℝ ρ Q w') (fun y => hvert y w' hw')
      ((hdiff hdρ z).clm_apply (differentiableAt_const w')) hw
    rw [h1] at h2
    simpa using h2
  · rintro (⟨i, d, r⟩ | k) hk
    · exact fderiv_const_apply _
    · simp at hk
  · intro k w
    obtain ⟨x, hx⟩ := scV_fst τ β k
    exact hvert z _ (fderiv_fst_eq_zero hx (hv k) w)
  · rintro j (k | k) hk w
    · exact scE_anticomm j k w
    · simp at hk
  · rintro (k | k) hk w
    · exact scZ_anticomm τ h β u _ k w
    · simp at hk

end GlobalTheory.TorsionForm.FibreSq
