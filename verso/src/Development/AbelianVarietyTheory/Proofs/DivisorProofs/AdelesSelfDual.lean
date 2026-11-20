import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointsNonemptyUnitaryRankOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEigenbasisPsiInfinitePlaceDistinctRoots
open Matrix NumberField GlobalTheory.LKTrip GlobalTheory.LKRes GlobalTheory.LKMid GlobalTheory.LKCount GlobalTheory.LKCx
open scoped TensorProduct Classical

namespace GlobalTheory.LKMid.CentPos

/- English proof (translation)
Use `set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)`. Use `set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)`. Establish `h1 : Zi * Zm = 1` using `by simp [Zi, Zm, ← Units.val_mul]`. Establish `h2 : Zm * Zi = 1` using `by simp [Zi, Zm, ← Units.val_mul]`. Establish `hD : Zi * M = diagonal lam * Zi`.

Combine the equalities or inequalities in the displayed calculation. Establish `hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j`. Introduce `a ha j`. Establish `e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a)`. Rewrite using `[mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]`.

Use `congrFun e j` as an intermediate fact. Rewrite `this` using `[mulVec_diagonal, Pi.smul_apply, smul_eq_mul]`. Then use the resulting hypothesis. Establish `hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a`. Introduce `a`. Rewrite using `[mulVec_mulVec, h2, one_mulVec]`.

Use `set u' := Zi *ᵥ u`. Use `set w' := Zi *ᵥ w`. Establish `hu'0 : u' ≠ 0`. Introduce `h`. Apply `hu0` to reduce the goal to its premises.

Rewrite using `[← hback u]`. Use `show Zm *ᵥ u' = 0`. Rewrite using `[h, mulVec_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by`. Assume the negation of the conclusion as `h`.

Use `push_neg at h`. Conclude with `hu'0 (funext h)`. Establish `hlam0 : lam i0 = μ` using `mul_right_cancel₀ hi0 (hcoord u hu i0)`. Use `⟨w' i0 / u' i0, ?_⟩` and prove the remaining obligations. Establish `hw' : w' = (w' i0 / u' i0) • u'`.

Use function extensionality and compare the values at `j`. Rewrite using `[Pi.smul_apply, smul_eq_mul]`. Distinguish the cases in `hj : j = i0`. Substitute `hj` using the available equality. Clear the denominators using the available nonvanishing facts.

Establish `hne : lam j - μ ≠ 0`. Introduce `h`. Apply `hj` to reduce the goal to its premises. Apply `hlam` to reduce the goal to its premises. Rewrite using `[hlam0]`.

Conclude with `sub_eq_zero.1 h`. Establish `hu0j : u' j = 0`. Use `hcoord u hu j` as an intermediate fact. Establish `h' : (lam j - μ) * u' j = 0` using `by rw [sub_mul]; exact sub_eq_zero.2 this`. Conclude with `(mul_eq_zero.1 h').resolve_left hne`.

Establish `hw0j : w' j = 0`. Use `hcoord w hw j` as an intermediate fact. Establish `h' : (lam j - μ) * w' j = 0` using `by rw [sub_mul]; exact sub_eq_zero.2 this`. Conclude with `(mul_eq_zero.1 h').resolve_left hne`. Rewrite using `[hu0j, hw0j, mul_zero]`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem eq_smul_of_eigen {n : ℕ} (M : Matrix (Fin n) (Fin n) ℂ) (Z : GL (Fin n) ℂ) (lam : Fin n → ℂ)
    (hlam : Function.Injective lam) (hZ : M * (Z : Matrix (Fin n) (Fin n) ℂ) = (Z : Matrix (Fin n) (Fin n) ℂ) * diagonal lam)
    (μ : ℂ) (u w : Fin n → ℂ) (hu : M *ᵥ u = μ • u) (hw : M *ᵥ w = μ • w) (hu0 : u ≠ 0) :
    ∃ l : ℂ, w = l • u := by
  set Zm : Matrix (Fin n) (Fin n) ℂ := (Z : Matrix (Fin n) (Fin n) ℂ)
  set Zi : Matrix (Fin n) (Fin n) ℂ := ((Z⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ)
  have h1 : Zi * Zm = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have h2 : Zm * Zi = 1 := by simp [Zi, Zm, ← Units.val_mul]
  have hD : Zi * M = diagonal lam * Zi := by
    calc Zi * M = Zi * (M * Zm) * Zi := by rw [Matrix.mul_assoc, Matrix.mul_assoc, h2, Matrix.mul_one]
      _ = Zi * (Zm * diagonal lam) * Zi := by rw [hZ]
      _ = diagonal lam * Zi := by rw [← Matrix.mul_assoc, h1, Matrix.one_mul]
  have hcoord : ∀ a : Fin n → ℂ, M *ᵥ a = μ • a → ∀ j, lam j * (Zi *ᵥ a) j = μ * (Zi *ᵥ a) j := by
    intro a ha j
    have e : diagonal lam *ᵥ (Zi *ᵥ a) = μ • (Zi *ᵥ a) := by
      rw [mulVec_mulVec, ← hD, ← mulVec_mulVec, ha, mulVec_smul]
    have := congrFun e j
    rwa [mulVec_diagonal, Pi.smul_apply, smul_eq_mul] at this
  have hback : ∀ a : Fin n → ℂ, Zm *ᵥ (Zi *ᵥ a) = a := by
    intro a; rw [mulVec_mulVec, h2, one_mulVec]
  set u' := Zi *ᵥ u
  set w' := Zi *ᵥ w
  have hu'0 : u' ≠ 0 := by
    intro h; apply hu0; rw [← hback u]; show Zm *ᵥ u' = 0; rw [h, mulVec_zero]
  obtain ⟨i0, hi0⟩ : ∃ i0, u' i0 ≠ 0 := by
    by_contra h; push_neg at h; exact hu'0 (funext h)
  have hlam0 : lam i0 = μ := mul_right_cancel₀ hi0 (hcoord u hu i0)
  refine ⟨w' i0 / u' i0, ?_⟩
  have hw' : w' = (w' i0 / u' i0) • u' := by
    funext j
    rw [Pi.smul_apply, smul_eq_mul]
    by_cases hj : j = i0
    · subst hj; field_simp
    · have hne : lam j - μ ≠ 0 := by
        intro h; apply hj; apply hlam; rw [hlam0]; exact sub_eq_zero.1 h
      have hu0j : u' j = 0 := by
        have := hcoord u hu j
        have h' : (lam j - μ) * u' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      have hw0j : w' j = 0 := by
        have := hcoord w hw j
        have h' : (lam j - μ) * w' j = 0 := by rw [sub_mul]; exact sub_eq_zero.2 this
        exact (mul_eq_zero.1 h').resolve_left hne
      rw [hu0j, hw0j, mul_zero]
  calc w = Zm *ᵥ w' := (hback w).symm
    _ = Zm *ᵥ ((w' i0 / u' i0) • u') := by rw [← hw']
    _ = (w' i0 / u' i0) • u := by rw [mulVec_smul, hback u]

/- English proof (translation)
Establish `hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β` using `hy.2`. Establish `hgu : IsUnit (G.gram v).det` using `isUnit_iff_ne_zero.mpr (G.gram_det v)`. Establish `hgg : G.gram v * (G.gram v)⁻¹ = 1` using `Matrix.mul_nonsing_inv _ hgu`. Establish `hgg' : (G.gram v)⁻¹ * G.gram v = 1` using `Matrix.nonsing_inv_mul _ hgu`. Establish `hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹`.

Introduce `x`. Establish `e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v` using `G.psi_star v x`. Rewrite using `[e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]`. Establish `hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 = algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C)`. Apply `(Units.mul_right_inj (y.1 * P.β)).mp` to reduce the goal to its premises.

Rewrite using `[Units.val_mul, ← Algebra.smul_def]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [mul_assoc]`. Use `_ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by`. Rewrite using `[hsim, ← Algebra.smul_def]`.

Simplify using `only [smul_mul_assoc]`. Use `_ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]`. Use `_ = _ := by rw [mul_smul_comm, mul_assoc]`. Rewrite using `[hH]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hgg', mul_one, map_mul, map_mul]`. Use `_ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by`. Rewrite using `[hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]`. Use `_ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]`.
-/
theorem cent_form_law {p : ℕ} [Fact p.Prime] (G : HTGroup p) (P : Pair G) (v : InfinitePlace G.F)
    (y : G.Cˣ × ℚˣ) (hy : y ∈ P.cent) :
    (G.psi v (y.1 : G.C))ᴴ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) * G.psi v (y.1 : G.C) =
      (((y.2 : ℚˣ) : ℚ) : ℂ) • (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
  have hsim : (y.1 : G.C) * P.β * sh G y.1 = algebraMap ℚ G.C (y.2 : ℚ) * P.β := hy.2
  have hgu : IsUnit (G.gram v).det := isUnit_iff_ne_zero.mpr (G.gram_det v)
  have hgg : G.gram v * (G.gram v)⁻¹ = 1 := Matrix.mul_nonsing_inv _ hgu
  have hgg' : (G.gram v)⁻¹ * G.gram v = 1 := Matrix.nonsing_inv_mul _ hgu
  have hH : ∀ x : G.C, (G.psi v x)ᴴ = G.gram v * G.psi v (sh G x) * (G.gram v)⁻¹ := by
    intro x
    have e : G.psi v (sh G x) = (G.gram v)⁻¹ * (G.psi v x)ᴴ * G.gram v := G.psi_star v x
    rw [e, ← mul_assoc, ← mul_assoc, hgg, one_mul, mul_assoc, hgg, mul_one]
  have hu : sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 =
      algebraMap ℚ G.C (y.2 : ℚ) * ((P.β⁻¹ : G.Cˣ) : G.C) := by
    apply (Units.mul_right_inj (y.1 * P.β)).mp
    rw [Units.val_mul, ← Algebra.smul_def]
    calc (y.1 : G.C) * P.β * (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1)
        = ((y.1 : G.C) * P.β * sh G (y.1 : G.C)) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1 := by
          simp only [mul_assoc]
      _ = (y.2 : ℚ) • ((P.β : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
          rw [hsim, ← Algebra.smul_def]; simp only [smul_mul_assoc]
      _ = (y.2 : ℚ) • ((y.1 : G.C) * P.β * ((P.β⁻¹ : G.Cˣ) : G.C)) := by
          rw [Units.mul_inv, one_mul, mul_assoc, Units.mul_inv, mul_one]
      _ = _ := by rw [mul_smul_comm, mul_assoc]
  rw [hH]
  calc G.gram v * G.psi v (sh G (y.1 : G.C)) * (G.gram v)⁻¹ * (G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) *
        G.psi v (y.1 : G.C)
      = G.gram v * (G.psi v (sh G (y.1 : G.C)) * ((G.gram v)⁻¹ * G.gram v) *
          G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) * G.psi v (y.1 : G.C)) := by simp only [mul_assoc]
    _ = G.gram v * G.psi v (sh G (y.1 : G.C) * ((P.β⁻¹ : G.Cˣ) : G.C) * y.1) := by
        rw [hgg', mul_one, map_mul, map_mul]
    _ = G.gram v * (((y.2 : ℚˣ) : ℚ) • G.psi v ((P.β⁻¹ : G.Cˣ) : G.C)) := by
        rw [hu, map_mul, RingHom.map_rat_algebraMap, ← Algebra.smul_def]
    _ = _ := by rw [mul_smul_comm, Rat.cast_smul_eq_qsmul]

end GlobalTheory.LKMid.CentPos

namespace GlobalTheory.LKMid

open GlobalTheory.LKMid.CentPos in

/- English proof (translation)
Introduce `p _ G P μ _ hm y hy`. Take `⟨v, -, x, hx, hpos⟩` from `hm`. Use `set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef`. Use `set M := G.psi v (P.γ : G.C) with hMdef`. Use `set Y := G.psi v (y.1 : G.C) with hYdef`.

Establish `hc : (y.1 : G.C) * P.γ = P.γ * y.1`. Use `congrArg Units.val hy.1` as an intermediate fact. Simplify using `using this`. Establish `hMY : M * Y = Y * M` using `by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]`. Establish `hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H` using `cent_form_law G P v y hy`.

Take `⟨Z, lam, hinj, -, hZ⟩` from `psi_eigenbasis p G P v`. Establish `hx0 : x ≠ 0` using `by rintro rfl; simp at hpos`. Establish `hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x)`. Rewrite using `[mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]`. Take `⟨l, hl⟩` from `eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0`.

Establish `key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x)`. Rewrite using `[star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]`. Simplify using `only [hHdef, Matrix.mul_assoc]`. Rewrite `key` using `[hform, hl]`. Simplify using `only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key`.

Use `set q := star x ⬝ᵥ (H *ᵥ x) with hq`. Establish `hq0 : q ≠ 0` using `by intro h; rw [h] at hpos; simp at hpos`. Establish `hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ)`. Rewrite `key` using `[← mul_assoc]`. Use `mul_right_cancel₀ hq0 key` as an intermediate fact.

Rewrite `this` using `[mul_comm]`. Conclude with `this`. Establish `hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ)` using `by simp`. Establish `hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ)`. Establish `: (star l * l).re = Complex.normSq l`.

Rewrite using `[mul_comm, Complex.star_def, Complex.mul_conj]`. Simplify using the standard rewrite rules. Rewrite `this` using `[hs]`. Establish `h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ)` using `by simp`. Rewrite using `[← h2, this]`.

Conclude with `Complex.normSq_nonneg l`. Establish `hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ)` using `by exact_mod_cast hnn`. Conclude with `lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))`.
-/
theorem cent_sim_pos : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := by
  intro p _ G P μ _ hm y hy
  obtain ⟨v, -, x, hx, hpos⟩ := hm
  set H := G.gram v * G.psi v ((P.β⁻¹ : G.Cˣ) : G.C) with hHdef
  set M := G.psi v (P.γ : G.C) with hMdef
  set Y := G.psi v (y.1 : G.C) with hYdef
  have hc : (y.1 : G.C) * P.γ = P.γ * y.1 := by
    have := congrArg Units.val hy.1; simpa using this
  have hMY : M * Y = Y * M := by rw [hMdef, hYdef, ← map_mul, ← map_mul, hc]
  have hform : Yᴴ * H * Y = (((y.2 : ℚˣ) : ℚ) : ℂ) • H := cent_form_law G P v y hy
  obtain ⟨Z, lam, hinj, -, hZ⟩ := psi_eigenbasis p G P v
  have hx0 : x ≠ 0 := by rintro rfl; simp at hpos
  have hYx : M *ᵥ (Y *ᵥ x) = μ • (Y *ᵥ x) := by
    rw [mulVec_mulVec, hMY, ← mulVec_mulVec, hx, mulVec_smul]
  obtain ⟨l, hl⟩ := eq_smul_of_eigen M Z lam hinj hZ μ x (Y *ᵥ x) hx hYx hx0
  have key : star (Y *ᵥ x) ⬝ᵥ (H *ᵥ (Y *ᵥ x)) = star x ⬝ᵥ ((Yᴴ * H * Y) *ᵥ x) := by
    rw [star_mulVec, mulVec_mulVec, dotProduct_mulVec, dotProduct_mulVec, vecMul_vecMul]
    simp only [hHdef, Matrix.mul_assoc]
  rw [hform, hl] at key
  simp only [Matrix.smul_mulVec, mulVec_smul, star_smul, dotProduct_smul, smul_dotProduct, smul_eq_mul] at key
  set q := star x ⬝ᵥ (H *ᵥ x) with hq
  have hq0 : q ≠ 0 := by intro h; rw [h] at hpos; simp at hpos
  have hs : star l * l = (((y.2 : ℚˣ) : ℚ) : ℂ) := by
    rw [← mul_assoc] at key; have := mul_right_cancel₀ hq0 key; rw [mul_comm] at this; exact this
  have hsre : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = ((y.2 : ℚˣ) : ℚ) := by simp
  have hnn : (0 : ℝ) ≤ (((y.2 : ℚˣ) : ℚ) : ℝ) := by
    have : (star l * l).re = Complex.normSq l := by
      rw [mul_comm, Complex.star_def, Complex.mul_conj]; simp
    rw [hs] at this
    have h2 : ((((y.2 : ℚˣ) : ℚ) : ℂ)).re = (((y.2 : ℚˣ) : ℚ) : ℝ) := by simp
    rw [← h2, this]; exact Complex.normSq_nonneg l
  have hnn' : (0 : ℚ) ≤ ((y.2 : ℚˣ) : ℚ) := by exact_mod_cast hnn
  exact lt_of_le_of_ne hnn' (Ne.symm (y.2.ne_zero))

/- English proof (translation)
The claim follows from `cent_sim_pos`.
-/
example : ∀ (p : ℕ) [Fact p.Prime] (G : HTGroup p) (P : Pair G) (μ : ℂ), G.a = 1 → P.Mark μ →
    ∀ y ∈ P.cent, 0 < ((y.2 : ℚˣ) : ℚ) := cent_sim_pos

end GlobalTheory.LKMid
