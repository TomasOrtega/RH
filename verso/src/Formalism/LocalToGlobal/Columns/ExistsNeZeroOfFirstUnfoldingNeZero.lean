import Formalism.LocalToGlobal.Columns.ChainTwAux
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.KerHypAll
import Formalism.LocalToGlobal.KernelLattices.KernelLocalFactors.ThDistC

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section TwE1J

variable {E K : Type} [Field E] [NumberField E] [StarRing E] [Field K] {P : HeightOneSpectrum (𝓞 E)}

/- English proof (translation)
Establish `hru : IsUnit (redP P u)`. Establish `h1 : redP P u * redP P u⁻¹ = 1` using `by rw [← reduction_mul hu hu', mul_inv_cancel₀ hu0, redP_one]`. Conclude with `isUnit_iff_exists_inv.2 ⟨_, h1⟩`. Distinguish the cases in `hy : IntAt P y`. Rewrite using `[reduction_mul hy hu, IsUnit.mul_iff]`.

Conclude with `⟨fun h => h.1, fun h => ⟨h, hru⟩⟩`. Establish `hyu : ¬ IntAt P (y * u)` using `fun h => hy (by`. Establish `e : y = (y * u) * u⁻¹` using `by field_simp`. Rewrite using `[e]`. Conclude with `h.mul hu')`.

Rewrite using `[reduction_eq_zero_of_not_integral P hy, reduction_eq_zero_of_not_integral P hyu]`.
-/
theorem isUnit_reduction_mul_iff₂ {u y : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) :
    IsUnit (redP P (y * u)) ↔ IsUnit (redP P y) := by
  have hru : IsUnit (redP P u) := by
    have h1 : redP P u * redP P u⁻¹ = 1 := by rw [← reduction_mul hu hu', mul_inv_cancel₀ hu0, redP_one]
    exact isUnit_iff_exists_inv.2 ⟨_, h1⟩
  by_cases hy : IntAt P y
  · rw [reduction_mul hy hu, IsUnit.mul_iff]
    exact ⟨fun h => h.1, fun h => ⟨h, hru⟩⟩
  · have hyu : ¬ IntAt P (y * u) := fun h => hy (by
      have e : y = (y * u) * u⁻¹ := by field_simp
      rw [e]; exact h.mul hu')
    rw [reduction_eq_zero_of_not_integral P hy, reduction_eq_zero_of_not_integral P hyu]

/- English proof (translation)
Unfold `LocE.vP`. Use `congr 1`. Use function extensionality and compare the values at `z`. Establish `e : a * u / (q : E) ^ z = a / (q : E) ^ z * u` using `by ring`. Rewrite using `[e, isUnit_reduction_mul_iff₂ hu0 hu hu']`.
-/
theorem valuationAt_mul_unit (q : ℕ) {a u : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹) : LocE.vP P q (a * u) = LocE.vP P q a := by
  unfold LocE.vP
  congr 1
  funext z
  have e : a * u / (q : E) ^ z = a / (q : E) ^ z * u := by ring
  rw [e, isUnit_reduction_mul_iff₂ hu0 hu hu']

/- English proof (translation)
Unfold `LocE.locChar at ha ⊢`. Rewrite using `[valuationAt_mul_unit q hu0 hu hu']`. Establish `h1` using `left_ne_zero_of_mul ha`. Establish `h2` using `right_ne_zero_of_mul ha`. Use `mul_ne_zero h1 ?_` and prove the remaining obligations.

Establish `hU : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a))`. Assume the negation of the conclusion as `hn`. Unfold `LocE.unitV at h2`. Rewrite `h2` using `[dif_neg hn]`. Conclude with `h2 rfl`.

Establish `hU' : IsUnit (redP P (a * u / (q : E) ^ LocE.vP P q a))`. Establish `e : a * u / (q : E) ^ LocE.vP P q a = a / (q : E) ^ LocE.vP P q a * u` using `by ring`. Rewrite using `[e, isUnit_reduction_mul_iff₂ hu0 hu hu']`. Conclude with `hU`. Unfold `LocE.unitV`.

Rewrite using `[dif_pos hU']`. Conclude with `Units.ne_zero _`.
-/
theorem twLocChar_mul_unit (q : ℕ) (cq : K) (χ : (𝓞 E ⧸ P.asIdeal)ˣ →* Kˣ) {a u : E} (hu0 : u ≠ 0) (hu : IntAt P u) (hu' : IntAt P u⁻¹)
    (ha : LocE.locChar (P := P) q cq χ a ≠ 0) : LocE.locChar (P := P) q cq χ (a * u) ≠ 0 := by
  unfold LocE.locChar at ha ⊢
  rw [valuationAt_mul_unit q hu0 hu hu']
  have h1 := left_ne_zero_of_mul ha
  have h2 := right_ne_zero_of_mul ha
  refine mul_ne_zero h1 ?_
  have hU : IsUnit (redP P (a / (q : E) ^ LocE.vP P q a)) := by
    by_contra hn
    unfold LocE.unitV at h2
    rw [dif_neg hn] at h2
    exact h2 rfl
  have hU' : IsUnit (redP P (a * u / (q : E) ^ LocE.vP P q a)) := by
    have e : a * u / (q : E) ^ LocE.vP P q a = a / (q : E) ^ LocE.vP P q a * u := by ring
    rw [e, isUnit_reduction_mul_iff₂ hu0 hu hu']
    exact hU
  unfold LocE.unitV
  rw [dif_pos hU']
  exact Units.ne_zero _

/- English proof (translation)
Unfold `Loc.E1`. Simplify using `only [Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun t _ => by ring`.
-/
theorem firstUnfolding_const_mul {n' c' n c : ℕ} (psi : E → K) (vals : Finset E) (wt C : K) (Φ : Loc.SF E K (n' + c') (n + c))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) :
    Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt (fun x => C * Φ x) xj = C * Loc.E1 psi vals wt Φ xj := by
  unfold Loc.E1
  simp only [Finset.mul_sum]
  exact Finset.sum_congr rfl fun t _ => by ring

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Use `push Not at hn`. Apply `h` to reduce the goal to its premises. Unfold `Loc.E1`. Simplify using `[hn]`.
-/
theorem exists_ne_zero_of_firstUnfolding_ne_zero {n' c' n c : ℕ} (psi : E → K) (vals : Finset E) (wt : K) (Φ : Loc.SF E K (n' + c') (n + c))
    (xj : (Fin n' → E) →ₗ[E] (Fin n → E)) (h : Loc.E1 (n' := n') (c' := c') (n := n) (c := c) psi vals wt Φ xj ≠ 0) : ∃ x, Φ x ≠ 0 := by
  by_contra hn
  push Not at hn
  apply h
  unfold Loc.E1
  simp [hn]

end TwE1J

section TwE1JMain

variable {X : Fields} {Pr : Primes X} {R : Ranks} {Ch : Chars X Pr R.m}
  {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)} {S : Set ℕ}
  {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)}

/- English proof (translation)
Unfold `PhiAt`. Rewrite using `[if_neg hP]`.
-/
theorem twPhiAt_Q (sharp : Bool) (i : ℕ) {P : HeightOneSpectrum (𝓞 X.E)} (hP : P ∉ Pr.vGs) :
    PhiAt (Pr := Pr) (R := R) Ch mu sharp i P = LocE.PhiQ (qOf P) (resChar (mu : Chr X.F X.E X.K) P) R.k R.r (cOf R i) (R.N i)
      (cOf R (i + 1)) (R.N (i + 1)) := by
  unfold PhiAt
  rw [if_neg hP]

def twOmS (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1)) : X.K :=
  muAt Ch sel mu c i P (LinearEquiv.det hal : X.Eˣ) * (muAt Ch sel mu c i P (LinearEquiv.det g : X.Eˣ))⁻¹ *
    c.sq P ^ (-(LocE.vP P.1 (qOf P.1) (LinearEquiv.det hal : X.Eˣ)) * ((R.N (i + 1) + cOf R (i + 1) : ℕ) : ℤ)) *
    c.sq P ^ (LocE.vP P.1 (qOf P.1) (LinearEquiv.det g : X.Eˣ) * ((R.N i + cOf R i : ℕ) : ℤ))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twOmPhi_eq (c : LocCst X (rowSG Pr sel mu)) (i : ℕ) (P : rowSG Pr sel mu) (hal : AutY X R i) (g : AutY X R (i + 1))
    (x : HomE X.E (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1))) :
    omPhi Ch sel mu c i P hal g x = twOmS (Ch := Ch) c i P hal g * PhiAt Ch mu c.sharp i P.1 (g.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) :=
  rfl

/- English proof (translation)
Establish `hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1))`. Rewrite using `[← twJat_Q cst.sharp (i + 1) hP]`. Conclude with `hκ`. Establish `hr` using `R.two_le_m`. Establish `hlaw : ∀ g : AutY X R (i + 1), g ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) → ∀ y, PhiAt Ch mu cst.sharp i P.1 (g.toLinearMap ∘ₗ y) = ((LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det g : X.Eˣ) : X.E) * LocE.lamQB (resChar (mu : Chr X. …`.

Introduce `g hg y`. Rewrite using `[twPhiAt_Q cst.sharp i hP]`. Establish `e1 : g.toLinearMap ∘ₗ y = g.toLinearMap ∘ₗ y ∘ₗ (1 : AutY X R i).toLinearMap` using `LinearMap.ext fun _ => rfl`. Rewrite using `[e1]`. Use `Formalism.L2.Ker.phiQ_law_lam (ciQ_mem P.1) hd.2 _ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) (R.k + i) (R.k + (i + 1)) (by omega) (by omega) ?_ ?_ ?_ ?_ (Subgroup.one_mem _) hg y` and prove the remaining obligations.

Unfold `Ranks.N; have := Nat.le_mul_of_pos_right i (show 0 < R.t + 1 by omega); omega`. Unfold `Ranks.N; have := Nat.le_mul_of_pos_right (i + 1) (show 0 < R.t + 1 by omega); omega`. Unfold `cOf Ranks.r`. Use linear arithmetic over natural numbers and integers. Unfold `cOf Ranks.r`.

Use linear arithmetic over natural numbers and integers. Take `⟨A₀, B₀, hH⟩` from `H`. Use `⟨A₀, B₀, fun A' B' hA hB hz => ?_⟩` and prove the remaining obligations. Establish `hne` using `hH A' B' hA hB`. Take `⟨xj, hxj⟩` from `Function.ne_iff.1 hne`.

Use `set c' : LocCst X (rowSG Pr sel mu) := { cst with A := A', B := B' } with hc'`. Use `set Ψ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) := fun x => PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) with hΨ`. Establish `hOm0 : omPhi Ch sel mu c' i P hal h = fun x => twOmS (Ch` using `Ch) c' i P hal h * Ψ x := funext fun x => twOmPhi_eq c' i P hal h x`. Use `set F : X.K := (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det κ⁻¹ : X.Eˣ) : X.E) * LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + (i + 1)) (R.N (i + 1)) κ⁻¹.toLinearMap) * (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det (1 : AutY X R …`. Establish `hOm1 : omPhi Ch sel mu c' i P hal (h * κ) = fun x => (twOmS (Ch` using `Ch) c' i P hal (h * κ) * F) * Ψ x := by`.

Use function extensionality and compare the values at `x`. Rewrite using `[twOmPhi_eq c' i P hal (h * κ) x, mul_assoc]`. Use `congr 1`. Establish `e2 : (h * κ).symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap = κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap)` using `LinearMap.ext fun _ => rfl`. Rewrite using `[e2]`.

Conclude with `hlaw κ⁻¹ (inv_mem hJ) _`. Establish `hE0 : E1at Ch sel mu c' i P hal h xj = twOmS (Ch` using `Ch) c' i P hal h * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B) (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by`. Unfold `E1at`. Rewrite using `[hOm0, firstUnfolding_const_mul]`. Establish `hE1 : E1at Ch sel mu c' i P hal (h * κ) xj = (twOmS (Ch` using `Ch) c' i P hal (h * κ) * F) * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B) (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by`.

Unfold `E1at`. Rewrite using `[hOm1, firstUnfolding_const_mul]`. Establish `h0` using `hE0 ▸ hxj`. Establish `hS` using `right_ne_zero_of_mul h0`. Establish `hM` using `left_ne_zero_of_mul h0`.

Take `⟨x0, hx0⟩` from `exists_ne_zero_of_firstUnfolding_ne_zero _ _ _ Ψ xj hS`. Establish `hF : F ≠ 0`. Introduce `hF0`. Apply `hx0` to reduce the goal to its premises. Establish `e3 : h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap = κ.toLinearMap ∘ₗ (κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap))` using `LinearMap.ext fun v => by simp`.

Use `show PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap) = 0`. Rewrite using `[e3, hlaw κ hJ, hlaw κ⁻¹ (inv_mem hJ), ← hFdef, hF0, zero_mul, mul_zero]`. Establish `hMk : twOmS (Ch` using `Ch) c' i P hal (h * κ) ≠ 0 := by`. Unfold `twOmS at hM ⊢`. Establish `hA1` using `left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))`.

Establish `hA2` using `right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))`. Establish `hA3` using `right_ne_zero_of_mul (left_ne_zero_of_mul hM)`. Establish `hκG : κ ∈ GLint X.E (R.N (i + 1) + cOf R (i + 1)) P.1` using `hJ.1`. Establish `hmu : muAt Ch sel mu c' i P (LinearEquiv.det (h * κ) : X.Eˣ) ≠ 0`. Establish `e4 : ((LinearEquiv.det (h * κ) : X.Eˣ) : X.E) = ((LinearEquiv.det h : X.Eˣ) : X.E) * ((LinearEquiv.det κ : X.Eˣ) : X.E)`.

Rewrite using `[map_mul, Units.val_mul]`. Rewrite using `[e4]`. Conclude with `twLocChar_mul_unit _ _ _ (Units.ne_zero _) (Formalism.L2.Ker.intAt_det κ hκG) (Formalism.L2.Ker.intAt_det_inv κ hκG) (fun h0 => hA2 (by unfold muAt; rw [h0, inv_zero]))`. Use `mul_ne_zero (mul_ne_zero (mul_ne_zero hA1 (inv_ne_zero hmu)) hA3) (zpow_ne_zero _ hsq)` and prove the remaining obligations. Establish `hz'` using `congrFun hz xj`.

Rewrite `hz'` using `[hE1]`. Conclude with `mul_ne_zero (mul_ne_zero hMk hF) hS hz'`.
-/
theorem firstUnfoldingNe_mul_parahoric {i : ℕ} (hi : i + 2 ≤ R.m) {P : rowSG Pr sel mu} (hP : P.1 ∉ Pr.vGs) (hd : TwDegOne X P.1) (hsq : cst.sq P ≠ 0)
    {hal : AutY X R i} {h κ : AutY X R (i + 1)} (hκ : κ ∈ Jat (Pr := Pr) cst.sharp (i + 1) P.1)
    (H : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h) : FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal (h * κ) := by
  have hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) := by
    rw [← twJat_Q cst.sharp (i + 1) hP]; exact hκ
  have hr := R.two_le_m

  have hlaw : ∀ g : AutY X R (i + 1), g ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) →
      ∀ y, PhiAt Ch mu cst.sharp i P.1 (g.toLinearMap ∘ₗ y) =
        ((LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det g : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + (i + 1)) (R.N (i + 1)) g.toLinearMap) *
        (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det (1 : AutY X R i) : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + i) (R.N i) (1 : AutY X R i).toLinearMap)) *
        PhiAt Ch mu cst.sharp i P.1 y := by
    intro g hg y
    rw [twPhiAt_Q cst.sharp i hP]
    have e1 : g.toLinearMap ∘ₗ y = g.toLinearMap ∘ₗ y ∘ₗ (1 : AutY X R i).toLinearMap := LinearMap.ext fun _ => rfl
    rw [e1]
    refine Formalism.L2.Ker.phiQ_law_lam (ciQ_mem P.1) hd.2 _ R.k R.r (cOf R i) (R.N i) (cOf R (i + 1)) (R.N (i + 1)) (R.k + i) (R.k + (i + 1))
      (by omega) (by omega) ?_ ?_ ?_ ?_ (Subgroup.one_mem _) hg y
    · unfold Ranks.N; have := Nat.le_mul_of_pos_right i (show 0 < R.t + 1 by omega); omega
    · unfold Ranks.N; have := Nat.le_mul_of_pos_right (i + 1) (show 0 < R.t + 1 by omega); omega
    · unfold cOf Ranks.r; omega
    · unfold cOf Ranks.r; omega
  obtain ⟨A₀, B₀, hH⟩ := H
  refine ⟨A₀, B₀, fun A' B' hA hB hz => ?_⟩
  have hne := hH A' B' hA hB
  obtain ⟨xj, hxj⟩ := Function.ne_iff.1 hne
  set c' : LocCst X (rowSG Pr sel mu) := { cst with A := A', B := B' } with hc'

  set Ψ : Loc.SF X.E X.K (R.N i + cOf R i) (R.N (i + 1) + cOf R (i + 1)) :=
    fun x => PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) with hΨ
  have hOm0 : omPhi Ch sel mu c' i P hal h = fun x => twOmS (Ch := Ch) c' i P hal h * Ψ x := funext fun x => twOmPhi_eq c' i P hal h x
  set F : X.K := (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det κ⁻¹ : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + (i + 1)) (R.N (i + 1)) κ⁻¹.toLinearMap) *
        (LocE.unitV (resChar (mu : Chr X.F X.E X.K) P.1) ((LinearEquiv.det (1 : AutY X R i) : X.Eˣ) : X.E) *
          LocE.lamQB (resChar (mu : Chr X.F X.E X.K) P.1) (R.k + i) (R.N i) (1 : AutY X R i).toLinearMap) with hFdef
  have hOm1 : omPhi Ch sel mu c' i P hal (h * κ) = fun x => (twOmS (Ch := Ch) c' i P hal (h * κ) * F) * Ψ x := by
    funext x
    rw [twOmPhi_eq c' i P hal (h * κ) x, mul_assoc]
    congr 1
    have e2 : (h * κ).symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap = κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x ∘ₗ hal.toLinearMap) :=
      LinearMap.ext fun _ => rfl
    rw [e2]
    exact hlaw κ⁻¹ (inv_mem hJ) _
  have hE0 : E1at Ch sel mu c' i P hal h xj = twOmS (Ch := Ch) c' i P hal h * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B)
      (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by
    unfold E1at
    rw [hOm0, firstUnfolding_const_mul]
  have hE1 : E1at Ch sel mu c' i P hal (h * κ) xj = (twOmS (Ch := Ch) c' i P hal (h * κ) * F) * Loc.E1 (c'.psi P) (LocE.valsQ X.E (qOf P.1) c'.A c'.B)
      (((qOf P.1 : X.K) ^ c'.B)⁻¹) Ψ xj := by
    unfold E1at
    rw [hOm1, firstUnfolding_const_mul]
  have h0 := hE0 ▸ hxj
  have hS := right_ne_zero_of_mul h0
  have hM := left_ne_zero_of_mul h0

  obtain ⟨x0, hx0⟩ := exists_ne_zero_of_firstUnfolding_ne_zero _ _ _ Ψ xj hS
  have hF : F ≠ 0 := by
    intro hF0
    apply hx0
    have e3 : h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap = κ.toLinearMap ∘ₗ (κ⁻¹.toLinearMap ∘ₗ (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap)) :=
      LinearMap.ext fun v => by simp
    show PhiAt Ch mu cst.sharp i P.1 (h.symm.toLinearMap ∘ₗ x0 ∘ₗ hal.toLinearMap) = 0
    rw [e3, hlaw κ hJ, hlaw κ⁻¹ (inv_mem hJ), ← hFdef, hF0, zero_mul, mul_zero]

  have hMk : twOmS (Ch := Ch) c' i P hal (h * κ) ≠ 0 := by
    unfold twOmS at hM ⊢
    have hA1 := left_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))
    have hA2 := right_ne_zero_of_mul (left_ne_zero_of_mul (left_ne_zero_of_mul hM))
    have hA3 := right_ne_zero_of_mul (left_ne_zero_of_mul hM)
    have hκG : κ ∈ GLint X.E (R.N (i + 1) + cOf R (i + 1)) P.1 := hJ.1
    have hmu : muAt Ch sel mu c' i P (LinearEquiv.det (h * κ) : X.Eˣ) ≠ 0 := by
      have e4 : ((LinearEquiv.det (h * κ) : X.Eˣ) : X.E) = ((LinearEquiv.det h : X.Eˣ) : X.E) * ((LinearEquiv.det κ : X.Eˣ) : X.E) := by
        rw [map_mul, Units.val_mul]
      rw [e4]
      exact twLocChar_mul_unit _ _ _ (Units.ne_zero _) (Formalism.L2.Ker.intAt_det κ hκG) (Formalism.L2.Ker.intAt_det_inv κ hκG) (fun h0 => hA2 (by unfold muAt; rw [h0, inv_zero]))
    refine mul_ne_zero (mul_ne_zero (mul_ne_zero hA1 (inv_ne_zero hmu)) hA3) (zpow_ne_zero _ hsq)
  have hz' := congrFun hz xj
  rw [hE1] at hz'
  exact mul_ne_zero (mul_ne_zero hMk hF) hS hz'

variable (Ch sel mu cst) in

def UnfoldingNonvanishingLeftCoset (m2 : ℕ) : Prop :=
  ∀ i, i < m2 → ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → TwDegOne X P.1 → ∀ (hal : AutY X R i) (h r : AutY X R (i + 1)),
    r ∈ Loc.R1 X.E (R.N (i + 1)) (cOf R (i + 1)) → TwBdd (Pr := Pr) i P.1 hal → TwBdd (Pr := Pr) (i + 1) P.1 h →
      TwBdd (Pr := Pr) (i + 1) P.1 (r * h) → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal h → FiniteSumNonzeroLargeDepth Ch sel mu cst i P hal (r * h)

/- English proof (translation)
Introduce `i hi P hP hd hal h h' hbal hb hb' hs hne`. Take `⟨r, hr, κ, hκ, rfl⟩` from `hs`. Establish `hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1))`. Rewrite using `[← twJat_Q cst.sharp (i + 1) hP]`. Conclude with `hκ`.

Establish `hstd : ∀ (g : AutY X R (i + 1)), g ∈ stabL X.E _ (stdAt X.E (R.N (i + 1) + cOf R (i + 1)) P.1) → ∀ x, x ∈ lamYat (Pr` using `Pr) (R := R) (i + 1) P.1 → g x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 := fun g hg x hx => by`. Rewrite `hx`, the goal using `[twLamQ_mem hP]`. Conclude with `(twStd_mem _).1 ((hg x).2 ((twStd_mem _).2 hx))`. Establish `hbrh : TwBdd (Pr` using `Pr) (i + 1) P.1 (r * h) := by`. Introduce `x hx`.

Establish `e : r * h = (r * h * κ) * κ⁻¹` using `by rw [mul_assoc, mul_inv_cancel, mul_one]`. Rewrite using `[e]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show κ ((r * h * κ)⁻¹ x) ∈ _`. Conclude with `hstd κ hJ.1 _ (hb' x hx).1`.

Use `show ((qOf P.1 : X.E) ^ (i + 1)) • (r * h * κ) (κ⁻¹ x) ∈ _`. Conclude with `(hb' _ (hstd κ⁻¹ (inv_mem hJ.1) x hx)).2`. Establish `h1` using `HL i hi P hP hd hal h r hr hbal hb hbrh hne`. Conclude with `firstUnfoldingNe_mul_parahoric (by omega) hP hd (hsq P hP) hκ h1`.
-/
theorem doubleCoset_of_leftR1 {m2 : ℕ} (hm : R.m = m2 + 2) (hsq : ∀ P : rowSG Pr sel mu, P.1 ∉ Pr.vGs → cst.sq P ≠ 0)
    (HL : UnfoldingNonvanishingLeftCoset Ch sel mu cst m2) : UnfoldingNonvanishingDoubleCoset Ch sel mu cst m2 := by
  intro i hi P hP hd hal h h' hbal hb hb' hs hne
  obtain ⟨r, hr, κ, hκ, rfl⟩ := hs
  have hJ : κ ∈ LocE.JQ P.1 (qOf P.1) (R.k + (i + 1)) (R.N (i + 1)) (cOf R (i + 1)) := by
    rw [← twJat_Q cst.sharp (i + 1) hP]; exact hκ

  have hstd : ∀ (g : AutY X R (i + 1)), g ∈ stabL X.E _ (stdAt X.E (R.N (i + 1) + cOf R (i + 1)) P.1) →
      ∀ x, x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 → g x ∈ lamYat (Pr := Pr) (R := R) (i + 1) P.1 := fun g hg x hx => by
    rw [twLamQ_mem hP] at hx ⊢
    exact (twStd_mem _).1 ((hg x).2 ((twStd_mem _).2 hx))
  have hbrh : TwBdd (Pr := Pr) (i + 1) P.1 (r * h) := by
    intro x hx
    have e : r * h = (r * h * κ) * κ⁻¹ := by rw [mul_assoc, mul_inv_cancel, mul_one]
    rw [e]
    refine ⟨?_, ?_⟩
    · show κ ((r * h * κ)⁻¹ x) ∈ _
      exact hstd κ hJ.1 _ (hb' x hx).1
    · show ((qOf P.1 : X.E) ^ (i + 1)) • (r * h * κ) (κ⁻¹ x) ∈ _
      exact (hb' _ (hstd κ⁻¹ (inv_mem hJ.1) x hx)).2
  have h1 := HL i hi P hP hd hal h r hr hbal hb hbrh hne
  exact firstUnfoldingNe_mul_parahoric (by omega) hP hd (hsq P hP) hκ h1

end TwE1JMain

end Formalism.L2.Col
