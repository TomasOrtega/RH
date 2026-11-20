import Mathlib
import Formalism.LocalRingCardinality.DataTheta

noncomputable section
namespace GlobalTheory.FockTensor
open Formalism.BasicNotions.TH Matrix

def sgnIx {p q : ℕ} : Ix p q → ℂ
  | .inl _ => 1
  | .inr _ => -1

/- English proof (translation)
Apply the tactic sequence `cases a <;> simp [sgnIx]`.
-/
theorem sgnIx_mul_self {p q : ℕ} (a : Ix p q) : sgnIx a * sgnIx a = 1 := by
  cases a <;> simp [sgnIx]

/- English proof (translation)
Apply the tactic sequence `cases a <;> simp [sgnIx]`.
-/
theorem star_sgnIx {p q : ℕ} (a : Ix p q) : star (sgnIx a) = sgnIx a := by
  cases a <;> simp [sgnIx]

/- English proof (translation)
Unfold `Jm Formalism.UG.Jpq`. Apply the tactic sequence `ext (i | i) (j | j) <;> simp [sgnIx, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp`.
-/
theorem Jm_eq_diagonal (p q : ℕ) : Jm p q = Matrix.diagonal sgnIx := by
  unfold Jm Formalism.UG.Jpq
  ext (i | i) (j | j) <;> simp [sgnIx, Matrix.diagonal_apply, Matrix.one_apply] <;> split_ifs <;> simp

/- English proof (translation)
Unfold `adjZ`. Rewrite using `[Jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjZ_apply {p q : ℕ} (Z : Mat p q) (a b : Ix p q) :
    adjZ Z a b = sgnIx a * sgnIx b * star (Z b a) := by
  unfold adjZ
  rw [Jm_eq_diagonal, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply]
  ring

/- English proof (translation)
Use extensionality with `a b`. Rewrite using `[adjZ_apply, adjZ_apply, star_mul', star_mul', star_sgnIx, star_sgnIx, star_star]`. Establish `ha` using `sgnIx_mul_self a`. Establish `hb` using `sgnIx_mul_self b`. Take the linear combination `(sgnIx b * sgnIx b * Z a b) * ha + Z a b * hb`.
-/
theorem adjZ_adjZ {p q : ℕ} (Z : Mat p q) : adjZ (adjZ Z) = Z := by
  ext a b
  rw [adjZ_apply, adjZ_apply, star_mul', star_mul', star_sgnIx, star_sgnIx, star_star]
  have ha := sgnIx_mul_self a
  have hb := sgnIx_mul_self b
  linear_combination (sgnIx b * sgnIx b * Z a b) * ha + Z a b * hb

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [adjZ_apply, Matrix.add_apply, star_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjZ_add {p q : ℕ} (Y Z : Mat p q) : adjZ (Y + Z) = adjZ Y + adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.add_apply, star_add]
  ring

/- English proof (translation)
Use extensionality with `a b`. Simplify using `only [adjZ_apply, Matrix.smul_apply, smul_eq_mul, star_mul']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjZ_smul {p q : ℕ} (c : ℂ) (Z : Mat p q) : adjZ (c • Z) = star c • adjZ Z := by
  ext a b
  simp only [adjZ_apply, Matrix.smul_apply, smul_eq_mul, star_mul']
  ring

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[adjZ_apply]`. Simplify using `only [Eab, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]`. Distinguish the cases in `h : a = j ∧ b = i`. Take `⟨rfl, rfl⟩` from `h`.

Rewrite using `[if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, star_one]`. Expand and normalize the polynomial expressions, which then agree. Establish `h' : ¬ (b = i ∧ a = j)` using `fun h'' => h ⟨h''.2, h''.1⟩`. Rewrite using `[if_neg h, if_neg h', star_zero]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem adjZ_Eab {p q : ℕ} (a b : Ix p q) : adjZ (Eab a b) = (sgnIx a * sgnIx b) • Eab b a := by
  ext i j
  rw [adjZ_apply]
  simp only [Eab, Matrix.smul_apply, Matrix.single_apply, smul_eq_mul]
  by_cases h : a = j ∧ b = i
  · obtain ⟨rfl, rfl⟩ := h
    rw [if_pos ⟨rfl, rfl⟩, if_pos ⟨rfl, rfl⟩, star_one]
    ring
  · have h' : ¬ (b = i ∧ a = j) := fun h'' => h ⟨h''.2, h''.1⟩
    rw [if_neg h, if_neg h', star_zero]
    ring

/- English proof (translation)
Rewrite using `[Jm_eq_diagonal, Matrix.diagonal_mul_diagonal]`. Establish `h : (fun a : Ix p q => sgnIx a * sgnIx a) = fun _ => 1` using `funext sgnIx_mul_self`. Rewrite using `[h, Matrix.diagonal_one]`.
-/
private theorem Jm_mul_JmRealPlaceTaylor (p q : ℕ) : Jm p q * Jm p q = 1 := by
  rw [Jm_eq_diagonal, Matrix.diagonal_mul_diagonal]
  have h : (fun a : Ix p q => sgnIx a * sgnIx a) = fun _ => 1 := funext sgnIx_mul_self
  rw [h, Matrix.diagonal_one]

/- English proof (translation)
Establish `hJ` using `Jm_mul_JmRealPlaceTaylor p q`. Use `show Zᴴ * Jm p q + Jm p q * Z = 0 ↔ _`. Unfold `adjZ`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `h2 : Jm p q * (Zᴴ * Jm p q + Jm p q * Z) = 0` using `by rw [h, mul_zero]`. Rewrite `h2` using `[mul_add, ← mul_assoc, ← mul_assoc, hJ, one_mul]`. Conclude with `eq_neg_of_add_eq_zero_left h2`. Introduce `h`. Establish `h2 : Jm p q * (Jm p q * Zᴴ * Jm p q) = Jm p q * (-Z)` using `by rw [h]`.

Rewrite `h2` using `[← mul_assoc, ← mul_assoc, hJ, one_mul, mul_neg]`. Rewrite using `[h2]`. Normalize the expressions using the abelian group laws.
-/
theorem mem_upq_iff {p q : ℕ} (Z : Mat p q) : Z ∈ upq p q ↔ adjZ Z = -Z := by
  have hJ := Jm_mul_JmRealPlaceTaylor p q
  show Zᴴ * Jm p q + Jm p q * Z = 0 ↔ _
  unfold adjZ
  constructor
  · intro h
    have h2 : Jm p q * (Zᴴ * Jm p q + Jm p q * Z) = 0 := by rw [h, mul_zero]
    rw [mul_add, ← mul_assoc, ← mul_assoc, hJ, one_mul] at h2
    exact eq_neg_of_add_eq_zero_left h2
  · intro h
    have h2 : Jm p q * (Jm p q * Zᴴ * Jm p q) = Jm p q * (-Z) := by rw [h]
    rw [← mul_assoc, ← mul_assoc, hJ, one_mul, mul_neg] at h2
    rw [h2]
    abel

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> exact h`.
-/
private theorem sameBlock_symm_twisted_operators {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : sameBlock b a := by
  cases a <;> cases b <;> exact h

/- English proof (translation)
Establish `h' : ∀ a b, ¬ sameBlock a b → Z a b = 0` using `h`. Introduce `a b hab`. Establish `hba : ¬ sameBlock b a` using `fun hs => hab (sameBlock_symm_twisted_operators hs)`. Rewrite using `[adjZ_apply, h' b a hba, star_zero, mul_zero]`.
-/
theorem isKC_adjZ {p q : ℕ} {Z : Mat p q} (h : IsKC Z) : IsKC (adjZ Z) := by
  have h' : ∀ a b, ¬ sameBlock a b → Z a b = 0 := h
  intro a b hab
  have hba : ¬ sameBlock b a := fun hs => hab (sameBlock_symm_twisted_operators hs)
  rw [adjZ_apply, h' b a hba, star_zero, mul_zero]

/- English proof (translation)
Introduce `i j hij`. Simplify using `only [Eab, Matrix.single_apply]`. Rewrite using `[if_neg]`. Introduce and unpack `⟨rfl, rfl⟩`. Conclude with `hij h`.
-/
theorem isKC_Eab {p q : ℕ} {a b : Ix p q} (h : sameBlock a b) : IsKC (Eab a b) := by
  intro i j hij
  simp only [Eab, Matrix.single_apply]
  rw [if_neg]
  rintro ⟨rfl, rfl⟩
  exact hij h

/- English proof (translation)
Apply the tactic sequence `cases a <;> trivial`.
-/
theorem sameBlock_self {p q : ℕ} (a : Ix p q) : sameBlock a a := by
  cases a <;> trivial

/- English proof (translation)
Apply the tactic sequence `cases a <;> cases b <;> trivial`.
-/
theorem sameBlock_of_posC {p q : ℕ} {a b : Ix p q} (h : posC a b) : sameBlock a b := by
  cases a <;> cases b <;> trivial

/- English proof (translation)
Use `⟨(1 / 2 : ℂ) • Z + (-1 / 2 : ℂ) • adjZ Z, ?_, (-Complex.I / 2) • Z + (-Complex.I / 2) • adjZ Z, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]`. Establish `h1 : star (1 / 2 : ℂ) = 1 / 2` using `by simp`. Establish `h2 : star (-1 / 2 : ℂ) = -1 / 2` using `by simp`. Rewrite using `[h1, h2]`.

Use `module`. Rewrite using `[mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]`. Establish `h3 : star (-Complex.I / 2) = Complex.I / 2` using `by simp`. Rewrite using `[h3]`. Use `module`.

Rewrite using `[smul_add, smul_smul, smul_smul]`. Establish `h4 : Complex.I * (-Complex.I / 2) = 1 / 2`. Put the polynomial expressions in normal form. Rewrite using `[Complex.I_sq]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[h4]`. Use `module`.
-/
theorem exists_upq_add {p q : ℕ} (Z : Mat p q) :
    ∃ X ∈ upq p q, ∃ Y ∈ upq p q, Z = X + Complex.I • Y := by
  refine ⟨(1 / 2 : ℂ) • Z + (-1 / 2 : ℂ) • adjZ Z, ?_,
    (-Complex.I / 2) • Z + (-Complex.I / 2) • adjZ Z, ?_, ?_⟩
  · rw [mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]
    have h1 : star (1 / 2 : ℂ) = 1 / 2 := by simp
    have h2 : star (-1 / 2 : ℂ) = -1 / 2 := by simp
    rw [h1, h2]
    module
  · rw [mem_upq_iff, adjZ_add, adjZ_smul, adjZ_smul, adjZ_adjZ]
    have h3 : star (-Complex.I / 2) = Complex.I / 2 := by simp
    rw [h3]
    module
  · rw [smul_add, smul_smul, smul_smul]
    have h4 : Complex.I * (-Complex.I / 2) = 1 / 2 := by
      ring_nf
      rw [Complex.I_sq]
      ring
    rw [h4]
    module

/- English proof (translation)
Establish `h0 : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y (t - t)`. Rewrite using `[sub_self]` and apply the resulting hypothesis. Establish `h1` using `HasDerivAt.comp_sub_const t t h0`. Establish `h2` using `((πU.π (T.expt (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1`. Simplify using `only [ContinuousLinearMap.coe_restrictScalars'] at h2`.

Use `h2 using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `s`. Establish `e : T.expt (s • Y) = T.expt (t • Y) * T.expt ((s - t) • Y)`. Establish `hs : t + (s - t) = s` using `by ring`. Rewrite using `[← T.expt_add Y hY, hs]`.

Simplify using `only [Function.comp, e, map_mul]`. Both sides reduce to the same expression.
-/
theorem hasDerivAt_orbit {p q : ℕ} {T : GrpData p q} (πU : URep T) {Y : Mat p q} (hY : Y ∈ upq p q)
    {x y : πU.H} (h : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y 0) (t : ℝ) :
    HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) (πU.π (T.expt (t • Y)) y) t := by
  have h0 : HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) x) y (t - t) := by
    rwa [sub_self]
  have h1 := HasDerivAt.comp_sub_const t t h0
  have h2 := ((πU.π (T.expt (t • Y))).restrictScalars ℝ).hasFDerivAt.comp_hasDerivAt t h1
  simp only [ContinuousLinearMap.coe_restrictScalars'] at h2
  convert h2 using 1
  funext s
  have e : T.expt (s • Y) = T.expt (t • Y) * T.expt ((s - t) • Y) := by
    have hs : t + (s - t) = s := by ring
    rw [← T.expt_add Y hY, hs]
  simp only [Function.comp, e, map_mul]
  rfl

/- English proof (translation)
Set `e : πU.H →ₗᵢ[ℂ] πU.H` to `⟨(πU.π g : πU.H →ₗ[ℂ] πU.H), πU.isom g⟩`. Conclude with `e.inner_map_map x y`.
-/
theorem inner_pi_pi {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) (πU.π g y) = inner ℂ x y := by
  let e : πU.H →ₗᵢ[ℂ] πU.H := ⟨(πU.π g : πU.H →ₗ[ℂ] πU.H), πU.isom g⟩
  exact e.inner_map_map x y

/- English proof (translation)
Establish `e : πU.π g (πU.π g⁻¹ y) = y` using `by show (πU.π g * πU.π g⁻¹) y = y`. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Establish `h` using `inner_pi_pi πU g x (πU.π g⁻¹ y)`. Rewrite `h` using `[e]`. Then use the resulting hypothesis.
-/
theorem inner_pi_left {p q : ℕ} {T : GrpData p q} (πU : URep T) (g : T.G) (x y : πU.H) :
    inner ℂ (πU.π g x) y = inner ℂ x (πU.π g⁻¹ y) := by
  have e : πU.π g (πU.π g⁻¹ y) = y := by
    show (πU.π g * πU.π g⁻¹) y = y
    rw [← map_mul]
    simp
  have h := inner_pi_pi πU g x (πU.π g⁻¹ y)
  rwa [e] at h

end GlobalTheory.FockTensor
