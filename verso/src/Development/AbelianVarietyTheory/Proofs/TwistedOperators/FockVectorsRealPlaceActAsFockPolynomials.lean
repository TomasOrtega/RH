import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.L2UnitaryRepresentationData
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOneP

noncomputable section

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum
open Formalism.IndefR.Mult (DSModel dualPar parA parB)
open Formalism.MainNotions.SchurIrreducible (AdmGK ARi ARiiiUp ARiiiDown ARiiiLine DiscreteSeriesBlattner admQ5)
open GlobalTheory.IndefiniteRowSideFullHecke.ThetaSourceAction hiding Mat
open GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix (SignCompat plainMat barMat)
open GlobalTheory.IndefiniteRowSideFullHecke.RestrictedTensorSplitting (fockIp)
open GlobalTheory.Chain (signed)
open GlobalTheory.Chain.RealIt (LPol locS locT IsPolyIso)
open MeasureTheory Matrix
open scoped TensorProduct InnerProductSpace ComplexConjugate
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.ArchRec

namespace GlobalTheory.ArchRec.SideAt

def dI {p q : ℕ} (x : Ix p q → ℝ) : Mat p q := Matrix.diagonal fun j => (x j : ℂ) * Complex.I

/- English proof (translation)
Unfold `Jm Formalism.UG.Jpq`. Use extensionality with `a b`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem jm_eq (p q : ℕ) : Jm p q = Matrix.diagonal fun a : Ix p q => if a.isLeft then (1 : ℂ) else -1 := by
  unfold Jm Formalism.UG.Jpq
  ext a b
  rcases a with a | a <;> rcases b with b | b <;> simp [Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

/- English proof (translation)
Use `show (dI x)ᴴ * Jm p q + Jm p q * dI x = 0`. Rewrite using `[jm_eq]`. Use extensionality with `a b`. Simplify using `only [dI, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.add_apply, Matrix.diagonal_apply, Matrix.zero_apply]`. Apply the tactic sequence `split_ifs <;> simp [Complex.ext_iff]`.
-/
theorem dI_mem {p q : ℕ} (x : Ix p q → ℝ) : dI x ∈ upq p q := by
  show (dI x)ᴴ * Jm p q + Jm p q * dI x = 0
  rw [jm_eq]
  ext a b
  simp only [dI, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, Matrix.add_apply,
    Matrix.diagonal_apply, Matrix.zero_apply]
  split_ifs <;> simp [Complex.ext_iff]

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [dI, Matrix.sum_apply, Matrix.smul_apply, Eab, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg hab, eq_comm]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j _`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`.

Conclude with `hab rfl`.
-/
theorem dI_eq_sum {p q : ℕ} (x : Ix p q → ℝ) : dI x = ∑ j, ((x j : ℂ) * Complex.I) • Eab j j := by
  ext a b
  simp only [dI, Matrix.sum_apply, Matrix.smul_apply, Eab, Matrix.single_apply, Matrix.diagonal_apply, smul_eq_mul,
    mul_ite, mul_one, mul_zero]
  by_cases hab : a = b
  · subst hab
    simp
  · rw [if_neg hab, eq_comm]
    apply Finset.sum_eq_zero
    intro j _
    rw [if_neg]
    rintro ⟨rfl, rfl⟩
    exact hab rfl

/- English proof (translation)
Unfold `wtSub`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`.
-/
theorem mem_wtSub {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V] (a : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (v : V) : v ∈ wtSub a μ ↔ ∀ j, a (Eab j j) v = ((μ j : ℚ) : ℂ) • v := by
  unfold wtSub
  simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]

/- English proof (translation)
Establish `hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * l)) * h s) 0 t`. Introduce `t`. Establish `h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * l)) (-(((1 : ℝ) : ℂ) * l)) t` using `((hasDerivAt_id t).ofReal_comp.mul_const l).neg`. Establish `h2` using `h1.cexp.mul (hd t)`. Conclude with `h2.congr_deriv (by push_cast; ring)`.

Establish `hc` using `is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0`. Simplify using `only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, neg_zero, Complex.exp_zero] at hc`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]`. Use `_ = Complex.exp l * h 0 := by rw [hc]`.
-/
theorem eq_exp_mul {h : ℝ → ℂ} {l : ℂ} (hd : ∀ t, HasDerivAt h (l * h t) t) : h 1 = Complex.exp l * h 0 := by
  have hg : ∀ t : ℝ, HasDerivAt (fun s : ℝ => Complex.exp (-((s : ℂ) * l)) * h s) 0 t := by
    intro t
    have h1 : HasDerivAt (fun s : ℝ => -((s : ℂ) * l)) (-(((1 : ℝ) : ℂ) * l)) t :=
      ((hasDerivAt_id t).ofReal_comp.mul_const l).neg
    have h2 := h1.cexp.mul (hd t)
    exact h2.congr_deriv (by push_cast; ring)
  have hc := is_const_of_deriv_eq_zero (fun t => (hg t).differentiableAt) (fun t => (hg t).deriv) 1 0
  simp only [Complex.ofReal_one, Complex.ofReal_zero, one_mul, zero_mul, neg_zero, Complex.exp_zero] at hc
  calc h 1 = Complex.exp l * (Complex.exp (-l) * h 1) := by
        rw [← mul_assoc, ← Complex.exp_add, add_neg_cancel, Complex.exp_zero, one_mul]
    _ = Complex.exp l * h 0 := by rw [hc]

/- English proof (translation)
Establish `htr : (dI x).trace = ∑ j, (x j : ℂ) * Complex.I` using `Matrix.trace_diagonal _`. Rewrite using `[htr, dI_eq_sum x, map_sum, LinearMap.sum_apply]`. Simplify using `only [map_smul, LinearMap.smul_apply, hw, smul_smul, ← Finset.sum_smul, ← add_smul]`. Use `congr 1`. Use `push_cast`.

Rewrite using `[Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem a_dI_add_trace_smul_of_weight {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (c : ℚ) (v : V)
    (hw : ∀ j, a (Eab j j) v = ((μ j : ℚ) : ℂ) • v) (x : Ix p q → ℝ) :
    a (dI x) v + ((c : ℂ) * (dI x).trace) • v =
      (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) • v := by
  have htr : (dI x).trace = ∑ j, (x j : ℂ) * Complex.I := Matrix.trace_diagonal _
  rw [htr, dI_eq_sum x, map_sum, LinearMap.sum_apply]
  simp only [map_smul, LinearMap.smul_apply, hw, smul_smul, ← Finset.sum_smul, ← add_smul]
  congr 1
  push_cast
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

/- English proof (translation)
Establish `hd : dI (Pi.single j (1 : ℝ) : Ix p q → ℝ) = Complex.I • Eab j j`. Rewrite using `[dI_eq_sum, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Pi.single_apply, hb]`.

Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`. Establish `h1` using `h (Pi.single j (1 : ℝ) : Ix p q → ℝ)`. Establish `htr : (Eab j j).trace = 1`. Unfold `Eab`.

Simplify using the standard rewrite rules. Establish `hs : ∑ j', ((μ j' + c : ℚ) : ℝ) * ((Pi.single j (1 : ℝ) : Ix p q → ℝ) j') = ((μ j + c : ℚ) : ℝ)`. Simplify using `[Pi.single_apply]`. Rewrite `h1` using `[hd, map_smul, LinearMap.smul_apply, Matrix.trace_smul, htr, hs]`. Establish `h2 : Complex.I • a (Eab j j) v = Complex.I • (((μ j : ℚ) : ℂ) • v)`.

Rewrite using `[eq_sub_of_add_eq h1, ← sub_smul, smul_smul]`. Use `congr 1`. Use `push_cast`. Simplify using `only [smul_eq_mul, mul_one]`. Expand and normalize the polynomial expressions, which then agree.

Conclude with `smul_right_injective V Complex.I_ne_zero h2`.
-/
private theorem a_Eab_diag_of_dI_add_trace_smul {p q : ℕ} {V : Type} [AddCommGroup V] [Module ℂ V]
    (a : Mat p q →ₗ[ℂ] Module.End ℂ V) (μ : Ix p q → ℚ) (c : ℚ) (v : V)
    (h : ∀ x : Ix p q → ℝ, a (dI x) v + ((c : ℂ) * (dI x).trace) • v =
      (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) • v) (j : Ix p q) :
    a (Eab j j) v = ((μ j : ℚ) : ℂ) • v := by
  have hd : dI (Pi.single j (1 : ℝ) : Ix p q → ℝ) = Complex.I • Eab j j := by
    rw [dI_eq_sum, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_apply, hb]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have h1 := h (Pi.single j (1 : ℝ) : Ix p q → ℝ)
  have htr : (Eab j j).trace = 1 := by
    unfold Eab
    simp
  have hs : ∑ j', ((μ j' + c : ℚ) : ℝ) * ((Pi.single j (1 : ℝ) : Ix p q → ℝ) j') = ((μ j + c : ℚ) : ℝ) := by
    simp [Pi.single_apply]
  rw [hd, map_smul, LinearMap.smul_apply, Matrix.trace_smul, htr, hs] at h1
  have h2 : Complex.I • a (Eab j j) v = Complex.I • (((μ j : ℚ) : ℂ) • v) := by
    rw [eq_sub_of_add_eq h1, ← sub_smul, smul_smul]
    congr 1
    push_cast
    simp only [smul_eq_mul, mul_one]
    ring
  exact smul_right_injective V Complex.I_ne_zero h2

/- English proof (translation)
Establish `hρ1 : ∀ F, ρ 1 F = F` using `fun F => by rw [map_one, Module.End.one_apply]`. Establish `hlin : ∀ (g : G) (w : ℂ) (P : MvPolynomial ι ℂ) (z : Z), ρ g (pt (w • P)) z = w * ρ g (pt P) z`. Introduce `g w P z`. Rewrite using `[map_smul, map_smul, Pi.smul_apply, smul_eq_mul]`. Establish `flow : ∀ Y ∈ upq p q, ∀ (w : ℂ) (P : MvPolynomial ι ℂ), κ (w • P) = a Y (κ P) + ((c : ℂ) * Y.trace) • κ P → ρ (at' (NormedSpace.exp ((1 : ℝ) • φ Y))) (pt P) = Complex.exp w • pt P`.

Introduce `Y hY w P hw`. Take `⟨P'', h1, h2⟩` from `hder Y hY P`. Establish `hP : P'' = w • P` using `κ.injective (h1.trans hw.symm)`. Substitute `hP` using the available equality. Use function extensionality and compare the values at `z`.

Establish `hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ρ (at' (NormedSpace.exp (s • φ Y))) (pt P) z) (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) t`. Introduce `t`. Establish `h3 : HasDerivAt (fun s : ℝ => ρ (at' (NormedSpace.exp ((t + s) • φ Y))) (pt P) z) (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) 0`. Establish `h4` using `h2 (at' (NormedSpace.exp (t • φ Y))) z`. Rewrite `h4` using `[hlin]`.

Simplify `h4` using `only [← hadd Y hY t]`. Establish `h5 : HasDerivAt (fun u : ℝ => ρ (at' (NormedSpace.exp ((t + (u - t)) • φ Y))) (pt P) z) (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) t` using `HasDerivAt.comp_sub_const t t (f := fun s : ℝ => ρ (at' (NormedSpace.exp ((t + s) • φ Y))) (pt P) z) (by rw [sub_self]; exact h3)`. Establish `e : ∀ u : ℝ, t + (u - t) = u` using `fun u => by ring`. Simplify `h5` using `only [e]`. Establish `h6` using `eq_exp_mul hF`.

Use `beta_reduce at h6`. Rewrite using `[h6, hzero Y hY, hρ1, Pi.smul_apply, smul_eq_mul]`. Use `⟨fun Y hY P P' => ?_, fun μ P => ?_⟩` and prove the remaining obligations. Take `⟨P'', h1, h2⟩` from `hder Y hY P`. Establish `h0 : ∀ z, HasDerivAt (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) (pt P'' z) 0`.

Introduce `z`. Use `h2 1 z` as an intermediate fact. Simplify `this` using `only [one_mul, hρ1]`. Prove the components needed by the constructor for the conclusion. Introduce `hP`.

Establish `: pt P' = pt P''` using `funext fun z => (hP z).unique (h0 z)`. Rewrite using `[hpt this]`. Conclude with `h1`. Introduce `hk`. Establish `: P' = P''` using `κ.injective (hk.trans h1.symm)`.

Substitute `this` using the available equality. Conclude with `h0`. Rewrite using `[mem_wtSub]`. Prove the components needed by the constructor for the conclusion. Introduce `hw x`.

Establish `hx1` using `hexp x 1`. Simplify using `only [one_mul] at hx1`. Use `show ρ (at' (φ _)) (pt P) = _`. Rewrite using `[hx1]`. Apply `flow _ (dI_mem x)` to reduce the goal to its premises.

Rewrite using `[map_smul, a_dI_add_trace_smul_of_weight a μ c (κ P) hw x]`. Introduce `hall`. Apply `a_Eab_diag_of_dI_add_trace_smul a μ c (κ P)` to reduce the goal to its premises. Introduce `x`. Take `⟨P'', h1, h2⟩` from `hder (dI x) (dI_mem x) P`.

Establish `h0 : ∀ z, HasDerivAt (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ (dI x)))) (pt P) z) (pt P'' z) 0`. Introduce `z`. Use `h2 1 z` as an intermediate fact. Simplify `this` using `only [one_mul, hρ1]`. Use `set w : ℂ := (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) with hwdef`.

Establish `hfun : ∀ z, (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ (dI x)))) (pt P) z) = fun t : ℝ => Complex.exp ((t : ℂ) * w) * pt P z`. Introduce `z`. Use function extensionality and compare the values at `t`. Rewrite using `[← hexp x t]`. Use `congrFun (hall (fun j => t * x j)) z` as an intermediate fact.

Rewrite `this` using `[Pi.smul_apply, smul_eq_mul]`. Rewrite using `[this, hwdef]`. Use `congr 2`. Use `push_cast`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hderw : ∀ z, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * w) * pt P z) (w * pt P z) 0`. Introduce `z`. Use `(((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp).mul_const (pt P z)` as an intermediate fact.

Conclude with `this.congr_deriv (by simp)`. Establish `hP : pt P'' = pt (w • P)`. Use function extensionality and compare the values at `z`. Use `h0 z` as an intermediate fact. Rewrite `this` using `[hfun z]`.

Rewrite using `[this.unique (hderw z), map_smul, Pi.smul_apply, smul_eq_mul]`. Rewrite using `[← h1, hpt hP, map_smul]`.
-/
theorem side_of {ι σ Z G : Type} [Monoid G] {n p q : ℕ} (ρ : G →* Module.End ℂ (Z → ℂ)) (at' : Mn n → G)
    (pt : MvPolynomial ι ℂ →ₗ[ℂ] (Z → ℂ)) (hpt : Function.Injective pt)
    (κ : MvPolynomial ι ℂ ≃ₗ[ℂ] MvPolynomial σ ℂ) (φ : Mat p q → Mn n) (c : ℚ)
    (a : Mat p q →ₗ[ℂ] Module.End ℂ (MvPolynomial σ ℂ))
    (hexp : ∀ (x : Ix p q → ℝ) (t : ℝ),
      φ (Matrix.diagonal fun j => Complex.exp (((t * x j : ℝ) : ℂ) * Complex.I)) = NormedSpace.exp (t • φ (dI x)))
    (hadd : ∀ Y ∈ upq p q, ∀ s t : ℝ,
      at' (NormedSpace.exp ((s + t) • φ Y)) = at' (NormedSpace.exp (s • φ Y)) * at' (NormedSpace.exp (t • φ Y)))
    (hzero : ∀ Y ∈ upq p q, at' (NormedSpace.exp ((0 : ℝ) • φ Y)) = 1)
    (hder : ∀ Y ∈ upq p q, ∀ P, ∃ P', κ P' = a Y (κ P) + ((c : ℂ) * Y.trace) • κ P ∧
      ∀ g z, HasDerivAt (fun t : ℝ => ρ (g * at' (NormedSpace.exp (t • φ Y))) (pt P) z) (ρ g (pt P') z) 0) :
    Side (fun g F => ρ (at' g) F) pt κ φ c a := by
  have hρ1 : ∀ F, ρ 1 F = F := fun F => by rw [map_one, Module.End.one_apply]
  have hlin : ∀ (g : G) (w : ℂ) (P : MvPolynomial ι ℂ) (z : Z), ρ g (pt (w • P)) z = w * ρ g (pt P) z := by
    intro g w P z
    rw [map_smul, map_smul, Pi.smul_apply, smul_eq_mul]
  have flow : ∀ Y ∈ upq p q, ∀ (w : ℂ) (P : MvPolynomial ι ℂ),
      κ (w • P) = a Y (κ P) + ((c : ℂ) * Y.trace) • κ P →
      ρ (at' (NormedSpace.exp ((1 : ℝ) • φ Y))) (pt P) = Complex.exp w • pt P := by
    intro Y hY w P hw
    obtain ⟨P'', h1, h2⟩ := hder Y hY P
    have hP : P'' = w • P := κ.injective (h1.trans hw.symm)
    subst hP
    funext z
    have hF : ∀ t : ℝ, HasDerivAt (fun s : ℝ => ρ (at' (NormedSpace.exp (s • φ Y))) (pt P) z)
        (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) t := by
      intro t
      have h3 : HasDerivAt (fun s : ℝ => ρ (at' (NormedSpace.exp ((t + s) • φ Y))) (pt P) z)
          (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) 0 := by
        have h4 := h2 (at' (NormedSpace.exp (t • φ Y))) z
        rw [hlin] at h4
        simpa only [← hadd Y hY t] using h4
      have h5 : HasDerivAt (fun u : ℝ => ρ (at' (NormedSpace.exp ((t + (u - t)) • φ Y))) (pt P) z)
          (w * ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) t :=
        HasDerivAt.comp_sub_const t t (f := fun s : ℝ => ρ (at' (NormedSpace.exp ((t + s) • φ Y))) (pt P) z)
          (by rw [sub_self]; exact h3)
      have e : ∀ u : ℝ, t + (u - t) = u := fun u => by ring
      simpa only [e] using h5
    have h6 := eq_exp_mul hF
    beta_reduce at h6
    rw [h6, hzero Y hY, hρ1, Pi.smul_apply, smul_eq_mul]
  refine ⟨fun Y hY P P' => ?_, fun μ P => ?_⟩
  · obtain ⟨P'', h1, h2⟩ := hder Y hY P
    have h0 : ∀ z, HasDerivAt (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ Y))) (pt P) z) (pt P'' z) 0 := by
      intro z
      have := h2 1 z
      simpa only [one_mul, hρ1] using this
    constructor
    · intro hP
      have : pt P' = pt P'' := funext fun z => (hP z).unique (h0 z)
      rw [hpt this]
      exact h1
    · intro hk
      have : P' = P'' := κ.injective (hk.trans h1.symm)
      subst this
      exact h0
  · rw [mem_wtSub]
    constructor
    · intro hw x
      have hx1 := hexp x 1
      simp only [one_mul] at hx1
      show ρ (at' (φ _)) (pt P) = _
      rw [hx1]
      apply flow _ (dI_mem x)
      rw [map_smul, a_dI_add_trace_smul_of_weight a μ c (κ P) hw x]
    · intro hall
      apply a_Eab_diag_of_dI_add_trace_smul a μ c (κ P)
      intro x
      obtain ⟨P'', h1, h2⟩ := hder (dI x) (dI_mem x) P
      have h0 : ∀ z, HasDerivAt (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ (dI x)))) (pt P) z) (pt P'' z) 0 := by
        intro z
        have := h2 1 z
        simpa only [one_mul, hρ1] using this
      set w : ℂ := (((∑ j, ((μ j + c : ℚ) : ℝ) * x j : ℝ) : ℂ) * Complex.I) with hwdef
      have hfun : ∀ z, (fun t : ℝ => ρ (at' (NormedSpace.exp (t • φ (dI x)))) (pt P) z) =
          fun t : ℝ => Complex.exp ((t : ℂ) * w) * pt P z := by
        intro z
        funext t
        rw [← hexp x t]
        have := congrFun (hall (fun j => t * x j)) z
        rw [Pi.smul_apply, smul_eq_mul] at this
        rw [this, hwdef]
        congr 2
        push_cast
        simp only [Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => ?_
        ring
      have hderw : ∀ z, HasDerivAt (fun t : ℝ => Complex.exp ((t : ℂ) * w) * pt P z) (w * pt P z) 0 := by
        intro z
        have := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.mul_const w).cexp).mul_const (pt P z)
        exact this.congr_deriv (by simp)
      have hP : pt P'' = pt (w • P) := by
        funext z
        have := h0 z
        rw [hfun z] at this
        rw [this.unique (hderw z), map_smul, Pi.smul_apply, smul_eq_mul]
      rw [← h1, hpt hP, map_smul]

/- English proof (translation)
Rewrite using `[jm_eq, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]`. Unfold `Formalism.REAL.Jm`. Use `congr 1`. Use function extensionality and compare the values at `a`. Establish `ha` using `h (e.symm a)`.

Rewrite `ha` using `[Equiv.apply_symm_apply]`. Simplify using `[Function.comp, ha]`.
-/
theorem jm_reindex {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) :
    Formalism.REAL.Jm ε = Matrix.reindex e e (Jm p q) := by
  rw [jm_eq, Matrix.reindex_apply, Matrix.submatrix_diagonal_equiv]
  unfold Formalism.REAL.Jm
  congr 1
  funext a
  have ha := h (e.symm a)
  rw [Equiv.apply_symm_apply] at ha
  simp [Function.comp, ha]

/- English proof (translation)
Establish `hY' : Yᴴ * Jm p q + Jm p q * Y = 0` using `hY`. Establish `h1 : (Y.map (starRingEnd ℂ))ᴴ = Yᵀ`. Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `h2 : (Yᴴ)ᵀ = Y.map (starRingEnd ℂ)`.

Use extensionality with `a b`. Simplify using `[Matrix.conjTranspose_apply]`. Establish `hJ : (Jm p q)ᵀ = Jm p q`. Rewrite using `[jm_eq]`. Conclude with `Matrix.diagonal_transpose _`.

Use `congrArg Matrix.transpose hY'` as an intermediate fact. Rewrite `this` using `[Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, h2, hJ, Matrix.transpose_zero]`. Use `show (Y.map (starRingEnd ℂ))ᴴ * Jm p q + Jm p q * Y.map (starRingEnd ℂ) = 0`. Rewrite using `[h1, add_comm]`. Conclude with `this`.
-/
theorem bar_mem {p q : ℕ} {Y : Mat p q} (hY : Y ∈ upq p q) : Y.map (starRingEnd ℂ) ∈ upq p q := by
  have hY' : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  have h1 : (Y.map (starRingEnd ℂ))ᴴ = Yᵀ := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have h2 : (Yᴴ)ᵀ = Y.map (starRingEnd ℂ) := by
    ext a b
    simp [Matrix.conjTranspose_apply]
  have hJ : (Jm p q)ᵀ = Jm p q := by
    rw [jm_eq]
    exact Matrix.diagonal_transpose _
  have := congrArg Matrix.transpose hY'
  rw [Matrix.transpose_add, Matrix.transpose_mul, Matrix.transpose_mul, h2, hJ, Matrix.transpose_zero] at this
  show (Y.map (starRingEnd ℂ))ᴴ * Jm p q + Jm p q * Y.map (starRingEnd ℂ) = 0
  rw [h1, add_comm]
  exact this

/- English proof (translation)
Establish `key : ∀ Y' : Mat p q, Y' ∈ upq p q → (Matrix.reindex e e Y')ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Matrix.reindex e e Y' = 0`. Introduce `Y' hY'`. Establish `hY'' : Y'ᴴ * Jm p q + Jm p q * Y' = 0` using `hY'`. Rewrite using `[jm_reindex h, Matrix.conjTranspose_reindex]`. Simplify using `only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]`.

Rewrite using `[show (Y'ᴴ * Jm p q).submatrix e.symm e.symm + (Jm p q * Y').submatrix e.symm e.symm = (Y'ᴴ * Jm p q + Jm p q * Y').submatrix e.symm e.symm from rfl, hY'']`. Both sides reduce to the same expression. Consider the cases of `br`. Conclude with `key Y hY`. Conclude with `key _ (bar_mem hY)`.
-/
theorem phi_mem {p q n : ℕ} {ε : Fin n → Bool} {e : Ix p q ≃ Fin n} (h : SignCompat ε e) (br : Bool)
    {Y : Mat p q} (hY : Y ∈ upq p q) : (phi br e Y)ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * phi br e Y = 0 := by
  have key : ∀ Y' : Mat p q, Y' ∈ upq p q →
      (Matrix.reindex e e Y')ᴴ * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * Matrix.reindex e e Y' = 0 := by
    intro Y' hY'
    have hY'' : Y'ᴴ * Jm p q + Jm p q * Y' = 0 := hY'
    rw [jm_reindex h, Matrix.conjTranspose_reindex]
    simp only [Matrix.reindex_apply, Matrix.submatrix_mul_equiv]
    rw [show (Y'ᴴ * Jm p q).submatrix e.symm e.symm + (Jm p q * Y').submatrix e.symm e.symm =
      (Y'ᴴ * Jm p q + Jm p q * Y').submatrix e.symm e.symm from rfl, hY'']
    rfl
  cases br
  · exact key Y hY
  · exact key _ (bar_mem hY)

/- English proof (translation)
Take `⟨hu, hG, -⟩` from `hf`. Establish `hd : IsUnit fr.det` using `(Matrix.isUnit_iff_isUnit_det fr).mp hu`. Establish `hX` using `phi_mem h br hY`. Unfold `phiFr`. Rewrite using `[← hG]`.

Establish `h1 : (fr⁻¹)ᴴ * frᴴ = 1`. Rewrite using `[← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]`. Establish `h2 : fr * fr⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hd`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]`.

Use `_ = 0 := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]`.
-/
theorem phiFr_mem {p q n : ℕ} {G s fr : Mn n} {ε : Fin n → Bool} (hf : IsFrameOf G s ε fr) {e : Ix p q ≃ Fin n}
    (h : SignCompat ε e) (br : Bool) {Y : Mat p q} (hY : Y ∈ upq p q) :
    (phiFr fr br e Y)ᴴ * G + G * phiFr fr br e Y = 0 := by
  obtain ⟨hu, hG, -⟩ := hf
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hu
  have hX := phi_mem h br hY
  unfold phiFr
  rw [← hG]
  have h1 : (fr⁻¹)ᴴ * frᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, Matrix.mul_nonsing_inv _ hd, Matrix.conjTranspose_one]
  have h2 : fr * fr⁻¹ = 1 := Matrix.mul_nonsing_inv _ hd
  calc (fr⁻¹ * phi br e Y * fr)ᴴ * (frᴴ * Formalism.REAL.Jm ε * fr) + frᴴ * Formalism.REAL.Jm ε * fr * (fr⁻¹ * phi br e Y * fr)
      = frᴴ * ((phi br e Y)ᴴ * ((fr⁻¹)ᴴ * frᴴ) * Formalism.REAL.Jm ε + Formalism.REAL.Jm ε * (fr * fr⁻¹) * phi br e Y) * fr := by
        simp only [Matrix.conjTranspose_mul, Matrix.mul_add, Matrix.add_mul, Matrix.mul_assoc]
    _ = 0 := by rw [h1, h2, Matrix.mul_one, Matrix.mul_one, hX, Matrix.mul_zero, Matrix.zero_mul]

/- English proof (translation)
Establish `hd : IsUnit fr.det` using `(Matrix.isUnit_iff_isUnit_det fr).mp hf`. Unfold `phiFr`. Rewrite using `[show fr * (fr⁻¹ * phi br e Y * fr) * fr⁻¹ = (fr * fr⁻¹) * phi br e Y * (fr * fr⁻¹) by`. Simplify using `only [Matrix.mul_assoc]]`. Rewrite using `[Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem conj_phiFr {p q n : ℕ} {fr : Mn n} (hf : IsUnit fr) (e : Ix p q ≃ Fin n) (br : Bool) (Y : Mat p q) :
    fr * phiFr fr br e Y * fr⁻¹ = phi br e Y := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hf
  unfold phiFr
  rw [show fr * (fr⁻¹ * phi br e Y * fr) * fr⁻¹ = (fr * fr⁻¹) * phi br e Y * (fr * fr⁻¹) by
    simp only [Matrix.mul_assoc]]
  rw [Matrix.mul_nonsing_inv _ hd, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hd : IsUnit fr.det` using `(Matrix.isUnit_iff_isUnit_det fr).mp hf`. Unfold `phiFr`. Rewrite using `[Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]`.
-/
theorem trace_phiFr {p q n : ℕ} {fr : Mn n} (hf : IsUnit fr) (e : Ix p q ≃ Fin n) (br : Bool) (Y : Mat p q) :
    (phiFr fr br e Y).trace = (phi br e Y).trace := by
  have hd : IsUnit fr.det := (Matrix.isUnit_iff_isUnit_det fr).mp hf
  unfold phiFr
  rw [Matrix.trace_mul_comm, ← Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hd, Matrix.one_mul]

/- English proof (translation)
Unfold `Matrix.trace`. Simplify using `only [Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]`. Conclude with `e.symm.sum_comp (fun a => Y a a)`.
-/
theorem trace_reindex {p q n : ℕ} (e : Ix p q ≃ Fin n) (Y : Mat p q) : (Matrix.reindex e e Y).trace = Y.trace := by
  unfold Matrix.trace
  simp only [Matrix.reindex_apply, Matrix.diag_apply, Matrix.submatrix_apply]
  exact e.symm.sum_comp (fun a => Y a a)

/- English proof (translation)
Establish `hY' : Yᴴ * Jm p q + Jm p q * Y = 0` using `hY`. Establish `hJJ : Jm p q * Jm p q = 1`. Rewrite using `[jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h1 : Jm p q * Yᴴ * Jm p q = -Y`. Use `congrArg (Jm p q * ·) hY'` as an intermediate fact. Simplify using `only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hJJ, Matrix.one_mul] at this`. Conclude with `eq_neg_of_add_eq_zero_left this`.

Establish `h2 : -Y.trace = star Y.trace`. Rewrite using `[← Matrix.trace_neg, ← h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul, Matrix.trace_conjTranspose]`. Establish `h3 : (Y.map (starRingEnd ℂ)).trace = starRingEnd ℂ Y.trace`. Simplify using `[Matrix.trace, map_sum]`. Rewrite using `[h3, h2]`.

Both sides reduce to the same expression.
-/
theorem trace_bar {p q : ℕ} {Y : Mat p q} (hY : Y ∈ upq p q) : (Y.map (starRingEnd ℂ)).trace = -Y.trace := by
  have hY' : Yᴴ * Jm p q + Jm p q * Y = 0 := hY
  have hJJ : Jm p q * Jm p q = 1 := by
    rw [jm_eq, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    split_ifs <;> simp
  have h1 : Jm p q * Yᴴ * Jm p q = -Y := by
    have := congrArg (Jm p q * ·) hY'
    simp only [Matrix.mul_add, Matrix.mul_zero, ← Matrix.mul_assoc, hJJ, Matrix.one_mul] at this
    exact eq_neg_of_add_eq_zero_left this
  have h2 : -Y.trace = star Y.trace := by
    rw [← Matrix.trace_neg, ← h1, Matrix.trace_mul_comm, ← Matrix.mul_assoc, hJJ, Matrix.one_mul,
      Matrix.trace_conjTranspose]
  have h3 : (Y.map (starRingEnd ℂ)).trace = starRingEnd ℂ Y.trace := by
    simp [Matrix.trace, map_sum]
  rw [h3, h2]
  rfl

/- English proof (translation)
Apply the tactic sequence `cases br <;>`. Apply the tactic sequence `simp only [phi, cjc, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat, Bool.false_eq_true, ite_false, ite_true, Matrix.reindex_apply] <;>`. Apply the tactic sequence `ext a b <;>`. Apply the tactic sequence `simp [Matrix.diagonal_apply, Matrix.submatrix_apply, Matrix.map_apply, apply_ite] <;>`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem phi_diagonal {p q n : ℕ} (e : Ix p q ≃ Fin n) (br : Bool) (d : Ix p q → ℂ) :
    phi br e (Matrix.diagonal d) = Matrix.diagonal fun a => cjc br (d (e.symm a)) := by
  cases br <;>
    simp only [phi, cjc, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.plainMat, GlobalTheory.IndefiniteRowSideFullHecke.BarMatrix.barMat, Bool.false_eq_true, ite_false,
      ite_true, Matrix.reindex_apply] <;>
    ext a b <;>
    simp [Matrix.diagonal_apply, Matrix.submatrix_apply, Matrix.map_apply, apply_ite] <;>
    split_ifs <;> simp_all

/- English proof (translation)
Unfold `phiFr`. Rewrite using `[show dI x = Matrix.diagonal (fun j => (x j : ℂ) * Complex.I) from rfl, phi_diagonal, phi_diagonal, ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_conj' _ _ hf, ← Matrix.diagonal_smul, Matrix.exp_diagonal]`. Use `congr 3`. Use function extensionality and compare the values at `a`. Rewrite using `[Pi.coe_exp, Pi.smul_apply, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]`.

Consider the cases of `br`. Simplify using `only [cjc, Bool.false_eq_true, ↓reduceIte]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [cjc, ↓reduceIte]`. Rewrite using `[← Complex.exp_conj]`. Use `congr 1`. Simplify using `only [map_mul, Complex.conj_ofReal, Complex.conj_I]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem phiFr_exp {p q n : ℕ} {fr : Mn n} (hf : IsUnit fr) (e : Ix p q ≃ Fin n) (br : Bool) (x : Ix p q → ℝ) (t : ℝ) :
    phiFr fr br e (Matrix.diagonal fun j => Complex.exp (((t * x j : ℝ) : ℂ) * Complex.I)) =
      NormedSpace.exp (t • phiFr fr br e (dI x)) := by
  unfold phiFr
  rw [show dI x = Matrix.diagonal (fun j => (x j : ℂ) * Complex.I) from rfl, phi_diagonal, phi_diagonal,
    ← Matrix.smul_mul, ← Matrix.mul_smul, Matrix.exp_conj' _ _ hf, ← Matrix.diagonal_smul, Matrix.exp_diagonal]
  congr 3
  funext a
  rw [Pi.coe_exp, Pi.smul_apply, ← Complex.exp_eq_exp_ℂ, Complex.real_smul]
  cases br
  · simp only [cjc, Bool.false_eq_true, ↓reduceIte]
    congr 1
    push_cast
    ring
  · simp only [cjc, ↓reduceIte]
    rw [← Complex.exp_conj]
    congr 1
    simp only [map_mul, Complex.conj_ofReal, Complex.conj_I]
    push_cast
    ring

/- English proof (translation)
Introduce `D ψ θ S T ω τ hθ sS frS εS sT frT εT hfS hfT aS aT pt hpt hL p q r s e e' hS hT κ hκ`. Unfold `LieAt DerAll at hL`. Unfold `IsPolyIso at hκ`. Establish `L : ∀ {V : HSp D} {X : Mn V.rank}, X ∈ lieAt V τ → ∀ t : ℝ, atTau θ V τ (NormedSpace.exp (t • X)) = oneP θ V τ X t`. Introduce `V X hX t`.

Establish `hex` using `GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t`. Take `⟨h0, -, huniq⟩` from `GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ (GlobalTheory.Mem.Lift.exp_mem hX t)`. Establish `hc : ∃ x, IsAtTau θ V τ (NormedSpace.exp (t • X)) x` using `⟨_, hex⟩`. Unfold `atTau`. Rewrite using `[dif_pos hc]`.

Conclude with `(huniq _ hc.choose_spec).trans (huniq _ hex).symm`. Establish `memS : ∀ Y ∈ upq p q, phiFr frS true e Y ∈ lieAt S τ` using `fun Y hY => phiFr_mem hfS hS true hY`. Establish `memT : ∀ Y ∈ upq r s, phiFr frT false e' Y ∈ lieAt T τ` using `fun Y hY => phiFr_mem hfT hT false hY`. Establish `huS : IsUnit frS` using `hfS.1`. Establish `huT : IsUnit frT` using `hfT.1`.

Prove the components needed by the constructor for the conclusion. Use `side_of (ω.comp (MonoidHom.inl _ _)) (atTau θ S τ) pt hpt κ (phiFr frS true e) aT (fockAct1 p q r s) (fun x t => phiFr_exp huS e true x t) ?_ ?_ ?_` and prove the remaining obligations. Introduce `Y hY s' t`. Rewrite using `[L (memS Y hY), L (memS Y hY), L (memS Y hY)]`. Conclude with `GlobalTheory.Mem.Lift.oneP_add hθ (memS Y hY) s' t`.

Introduce `Y hY`. Rewrite using `[L (memS Y hY)]`. Conclude with `GlobalTheory.Mem.Lift.oneP_zero hθ`. Introduce `Y hY P`. Establish `hbar : (phi true e Y).map (starRingEnd ℂ) = Matrix.reindex e e Y` using `by show (Matrix.reindex e e (Y.map (starRingEnd ℂ))).map (starRingEnd ℂ) = Matrix.reindex e e Y`.

Use extensionality with `a b`. Simplify using the standard rewrite rules. Establish `htr : (phiFr frS true e Y).trace = -Y.trace`. Rewrite using `[trace_phiFr huS]`. Conclude with `(trace_reindex e (Y.map (starRingEnd ℂ))).trans (trace_bar hY)`.

Use `⟨locS εS εT ((frS * phiFr frS true e Y * frS⁻¹).map (starRingEnd ℂ)) P - ((aT : ℂ) * (phiFr frS true e Y).trace) • P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_phiFr huS, hbar, map_sub, map_smul, hκ.1, htr, mul_neg, neg_smul, sub_neg_eq_add]`. Introduce `g z`. Use `(hL.1 _ (memS Y hY) P).1 (g, 1) z` as an intermediate fact. Simplify `this` using `only [MonoidHom.comp_apply, MonoidHom.inl_apply, L (memS Y hY), Prod.mk_mul_mk, mul_one]`.

Use `side_of (ω.comp (MonoidHom.inr _ _)) (atTau θ T τ) pt hpt κ (phiFr frT false e') aS (fockAct2 p q r s) (fun x t => phiFr_exp huT e' false x t) ?_ ?_ ?_` and prove the remaining obligations. Introduce `Y hY s' t`. Rewrite using `[L (memT Y hY), L (memT Y hY), L (memT Y hY)]`. Conclude with `GlobalTheory.Mem.Lift.oneP_add hθ (memT Y hY) s' t`. Introduce `Y hY`.

Rewrite using `[L (memT Y hY)]`. Conclude with `GlobalTheory.Mem.Lift.oneP_zero hθ`. Introduce `Y hY P`. Establish `hpl : phi false e' Y = Matrix.reindex e' e' Y` using `rfl`. Establish `htr : (phiFr frT false e' Y).trace = Y.trace`.

Rewrite using `[trace_phiFr huT, hpl]`. Conclude with `trace_reindex e' Y`. Use `⟨locT εS εT (frT * phiFr frT false e' Y * frT⁻¹) P + ((aS : ℂ) * (phiFr frT false e' Y).trace) • P, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[conj_phiFr huT, hpl, map_add, map_smul, hκ.2, htr]`. Introduce `g z`.

Use `(hL.2 _ (memT Y hY) P).1 (1, g) z` as an intermediate fact. Simplify `this` using `only [MonoidHom.comp_apply, MonoidHom.inr_apply, L (memT Y hY), Prod.mk_mul_mk, one_mul]`.
-/
theorem side_at : ∀ (D : D7) (ψ : AddChar (AF D.host.F) ℂ) (θ : InfFam D) (S T : HSp D) (ω : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)) (τ : D.what₂.Tau), IsInfFam θ → ∀ (sS frS : Mn S.rank) (εS : Fin S.rank → Bool) (sT frT : Mn T.rank) (εT : Fin T.rank → Bool), IsFrameOf (gramAt D S τ) sS εS frS → IsFrameOf (gramAt D T τ) sT εT frT → ∀ (aS aT : ℚ) (pt : LPol T.rank S.rank →ₗ[ℂ] (WO S T → ℂ)), Function.Injective pt → LieAt ψ θ τ ω εS frS εT frT aS aT pt → ∀ (p q r s : ℕ) (e : Ix p q ≃ Fin S.rank) (e' : Ix r s ≃ Fin T.rank), SignCompat εS e → SignCompat εT e' → ∀ κ : LPol T.rank S.rank ≃ₗ[ℂ] Pol p q r s, IsPolyIso εS εT e e' κ → Side (actSrc θ ω τ) pt κ (phiFr frS true e) aT (fockAct1 p q r s) ∧ Side (actTgt θ ω τ) pt κ (phiFr frT false e') aS (fockAct2 p q r s) := by
  intro D ψ θ S T ω τ hθ sS frS εS sT frT εT hfS hfT aS aT pt hpt hL p q r s e e' hS hT κ hκ
  unfold LieAt DerAll at hL
  unfold IsPolyIso at hκ
  have L : ∀ {V : HSp D} {X : Mn V.rank}, X ∈ lieAt V τ → ∀ t : ℝ,
      atTau θ V τ (NormedSpace.exp (t • X)) = oneP θ V τ X t := by
    intro V X hX t
    have hex := GlobalTheory.Mem.Lift.isAtTau_oneP hθ hX t
    obtain ⟨h0, -, huniq⟩ := GlobalTheory.PointAtPlace.existsUnique_isAtTau V τ θ hθ _ (GlobalTheory.Mem.Lift.exp_mem hX t)
    have hc : ∃ x, IsAtTau θ V τ (NormedSpace.exp (t • X)) x := ⟨_, hex⟩
    unfold atTau
    rw [dif_pos hc]
    exact (huniq _ hc.choose_spec).trans (huniq _ hex).symm
  have memS : ∀ Y ∈ upq p q, phiFr frS true e Y ∈ lieAt S τ := fun Y hY => phiFr_mem hfS hS true hY
  have memT : ∀ Y ∈ upq r s, phiFr frT false e' Y ∈ lieAt T τ := fun Y hY => phiFr_mem hfT hT false hY
  have huS : IsUnit frS := hfS.1
  have huT : IsUnit frT := hfT.1
  constructor
  · refine side_of (ω.comp (MonoidHom.inl _ _)) (atTau θ S τ) pt hpt κ (phiFr frS true e) aT (fockAct1 p q r s)
      (fun x t => phiFr_exp huS e true x t) ?_ ?_ ?_
    · intro Y hY s' t
      rw [L (memS Y hY), L (memS Y hY), L (memS Y hY)]
      exact GlobalTheory.Mem.Lift.oneP_add hθ (memS Y hY) s' t
    · intro Y hY
      rw [L (memS Y hY)]
      exact GlobalTheory.Mem.Lift.oneP_zero hθ
    · intro Y hY P
      have hbar : (phi true e Y).map (starRingEnd ℂ) = Matrix.reindex e e Y := by
        show (Matrix.reindex e e (Y.map (starRingEnd ℂ))).map (starRingEnd ℂ) = Matrix.reindex e e Y
        ext a b
        simp
      have htr : (phiFr frS true e Y).trace = -Y.trace := by
        rw [trace_phiFr huS]
        exact (trace_reindex e (Y.map (starRingEnd ℂ))).trans (trace_bar hY)
      refine ⟨locS εS εT ((frS * phiFr frS true e Y * frS⁻¹).map (starRingEnd ℂ)) P -
        ((aT : ℂ) * (phiFr frS true e Y).trace) • P, ?_, ?_⟩
      · rw [conj_phiFr huS, hbar, map_sub, map_smul, hκ.1, htr, mul_neg, neg_smul, sub_neg_eq_add]
      · intro g z
        have := (hL.1 _ (memS Y hY) P).1 (g, 1) z
        simpa only [MonoidHom.comp_apply, MonoidHom.inl_apply, L (memS Y hY), Prod.mk_mul_mk, mul_one] using this
  · refine side_of (ω.comp (MonoidHom.inr _ _)) (atTau θ T τ) pt hpt κ (phiFr frT false e') aS (fockAct2 p q r s)
      (fun x t => phiFr_exp huT e' false x t) ?_ ?_ ?_
    · intro Y hY s' t
      rw [L (memT Y hY), L (memT Y hY), L (memT Y hY)]
      exact GlobalTheory.Mem.Lift.oneP_add hθ (memT Y hY) s' t
    · intro Y hY
      rw [L (memT Y hY)]
      exact GlobalTheory.Mem.Lift.oneP_zero hθ
    · intro Y hY P
      have hpl : phi false e' Y = Matrix.reindex e' e' Y := rfl
      have htr : (phiFr frT false e' Y).trace = Y.trace := by
        rw [trace_phiFr huT, hpl]
        exact trace_reindex e' Y
      refine ⟨locT εS εT (frT * phiFr frT false e' Y * frT⁻¹) P +
        ((aS : ℂ) * (phiFr frT false e' Y).trace) • P, ?_, ?_⟩
      · rw [conj_phiFr huT, hpl, map_add, map_smul, hκ.2, htr]
      · intro g z
        have := (hL.2 _ (memT Y hY) P).1 (1, g) z
        simpa only [MonoidHom.comp_apply, MonoidHom.inr_apply, L (memT Y hY), Prod.mk_mul_mk, one_mul] using this

end GlobalTheory.ArchRec.SideAt

end
