import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LocalNewformFunction

open Matrix Formalism.IndefR.Datum
open scoped ComplexOrder MatrixOrder

namespace GlobalTheory.CartanRefl

/- English proof (translation)
Set `U : Matrix (Fin k) (Fin k) ℂ` to `hG.eigenvectorUnitary.1`. Establish `h1 : U * star U = 1` using `hG.eigenvectorUnitary.2.2`. Establish `h2 : star U * U = 1` using `hG.eigenvectorUnitary.2.1`. Establish `hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U`. Use `hG.spectral_theorem` as an intermediate fact.

Rewrite `this` using `[Unitary.conjStarAlgAut_apply]`. Conclude with `this`. Establish `hne : ∀ i, hG.eigenvalues i ≠ 0` using `fun i hi => by`. Rewrite `hd` using `[hG.det_eq_prod_eigenvalues]`. Conclude with `hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))`.

Establish `mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) = U * diagonal (fun i => a i * b i) * star U` using `fun a b => by`. Combine the equalities or inequalities in the displayed calculation. Set `e : Fin k → ℝ` to `fun i => if 0 < hG.eigenvalues i then 1 else -1`. Establish `he : ∀ i, (e i : ℂ) * e i = 1` using `fun i => by`. Apply the tactic sequence `simp only [e]; split_ifs <;> simp`.

Establish `hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U`. Simplify using `[Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc, Pi.star_def]`. Use `⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mul]`. Simplify using `only [he, diagonal_one, Matrix.mul_one, h1]`.

Rewrite using `[hh] conv_lhs => rw [hs] conv_rhs => rw [hs]`. Rewrite using `[mul, mul]`. Use `congr 3`. Use function extensionality and compare the values at `i`. Rewrite using `[mul_right_comm, he, one_mul]`.

Use `conv => arg 1`. Use `arg 1`. Rewrite using `[hs]`. Rewrite using `[mul]`. Establish `hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef`.

Rewrite using `[Matrix.posDef_diagonal_iff]`. Introduce `i`. Rewrite using `[← Complex.ofReal_mul, Complex.zero_lt_real]`. Simplify using `only [e]`. Use `split_ifs with h`.

Simplify using `using h`. Use `lt_of_le_of_ne (not_lt.1 h) (hne i)` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hu : IsUnit (star U)` using `⟨⟨star U, U, h2, h1⟩, rfl⟩`. Use `hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)` as an intermediate fact.

Rewrite `this` using `[Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose]`. Then use the resulting hypothesis. Introduce `u hu`. Take `⟨v, rfl⟩ : ∃ v, u = U * v * star U` from `⟨star U * u * U, by`. Combine the equalities or inequalities in the displayed calculation. Establish `cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U` using `fun a b => by`.

Combine the equalities or inequalities in the displayed calculation. Establish `inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b` using `fun a b h => by`. Establish `key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a` using `fun a => by`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← key a, h, key]`.

Establish `hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v`. Apply `inj` to reduce the goal to its premises. Rewrite using `[← cm, ← cm, ← hs, hu]`. Rewrite using `[cm, cm]`. Use `congr 2`.

Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hv i) j`. Rewrite `hij`, the goal using `[mul_diagonal, diagonal_mul]`. Distinguish the cases in `h0 : v i j = 0`. Simplify using `[h0]`.

Establish `: hG.eigenvalues j = hG.eigenvalues i`. Rewrite `hij` using `[mul_comm]`. Conclude with `mul_right_cancel₀ h0 hij` after adjusting the coercions. Simplify using `only [e, this, mul_comm]`.
-/
theorem exists_sign {k : ℕ} {G : Matrix (Fin k) (Fin k) ℂ} (hG : G.IsHermitian) (hd : G.det ≠ 0) :
    ∃ s, IsCartanInv G s ∧ ∀ u, u * G = G * u → u * s = s * u := by
  classical
  let U : Matrix (Fin k) (Fin k) ℂ := hG.eigenvectorUnitary.1
  have h1 : U * star U = 1 := hG.eigenvectorUnitary.2.2
  have h2 : star U * U = 1 := hG.eigenvectorUnitary.2.1
  have hs : G = U * diagonal (fun i => (hG.eigenvalues i : ℂ)) * star U := by
    have := hG.spectral_theorem
    rw [Unitary.conjStarAlgAut_apply] at this
    exact this
  have hne : ∀ i, hG.eigenvalues i ≠ 0 := fun i hi => by
    rw [hG.det_eq_prod_eigenvalues] at hd
    exact hd (Finset.prod_eq_zero (Finset.mem_univ i) (by simp [hi]))
  have mul : ∀ a b : Fin k → ℂ, (U * diagonal a * star U) * (U * diagonal b * star U) =
      U * diagonal (fun i => a i * b i) * star U := fun a b => by
    calc _ = U * (diagonal a * (star U * U) * diagonal b) * star U := by simp only [Matrix.mul_assoc]
      _ = _ := by rw [h2, Matrix.mul_one, diagonal_mul_diagonal]
  let e : Fin k → ℝ := fun i => if 0 < hG.eigenvalues i then 1 else -1
  have he : ∀ i, (e i : ℂ) * e i = 1 := fun i => by
    simp only [e]; split_ifs <;> simp
  have hh : (U * diagonal (fun i => (e i : ℂ)) * star U)ᴴ = U * diagonal (fun i => (e i : ℂ)) * star U := by
    simp [Matrix.conjTranspose_mul, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.mul_assoc,
      Pi.star_def]
  refine ⟨U * diagonal (fun i => (e i : ℂ)) * star U, ⟨?_, ?_, ?_⟩, ?_⟩
  · rw [mul]
    simp only [he, diagonal_one, Matrix.mul_one, h1]
  · rw [hh]
    conv_lhs => rw [hs]
    conv_rhs => rw [hs]
    rw [mul, mul]
    congr 3
    funext i
    rw [mul_right_comm, he, one_mul]
  · conv => arg 1; arg 1; rw [hs]
    rw [mul]
    have hp : (diagonal fun i => (hG.eigenvalues i : ℂ) * e i).PosDef := by
      rw [Matrix.posDef_diagonal_iff]
      intro i
      rw [← Complex.ofReal_mul, Complex.zero_lt_real]
      simp only [e]
      split_ifs with h
      · simpa using h
      · have := lt_of_le_of_ne (not_lt.1 h) (hne i)
        linarith
    have hu : IsUnit (star U) := ⟨⟨star U, U, h2, h1⟩, rfl⟩
    have := hp.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    rwa [Matrix.star_eq_conjTranspose, conjTranspose_conjTranspose, ← Matrix.star_eq_conjTranspose] at this
  · intro u hu
    obtain ⟨v, rfl⟩ : ∃ v, u = U * v * star U := ⟨star U * u * U, by
      calc u = (U * star U) * u * (U * star U) := by rw [h1, Matrix.one_mul, Matrix.mul_one]
        _ = _ := by simp only [Matrix.mul_assoc]⟩
    have cm : ∀ a b : Matrix (Fin k) (Fin k) ℂ, (U * a * star U) * (U * b * star U) = U * (a * b) * star U := fun a b => by
      calc _ = U * (a * (star U * U) * b) * star U := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h2, Matrix.mul_one]
    have inj : ∀ a b : Matrix (Fin k) (Fin k) ℂ, U * a * star U = U * b * star U → a = b := fun a b h => by
      have key : ∀ a : Matrix (Fin k) (Fin k) ℂ, star U * (U * a * star U) * U = a := fun a => by
        calc _ = (star U * U) * a * (star U * U) := by simp only [Matrix.mul_assoc]
          _ = a := by rw [h2, Matrix.one_mul, Matrix.mul_one]
      rw [← key a, h, key]
    have hv : v * diagonal (fun i => (hG.eigenvalues i : ℂ)) = diagonal (fun i => (hG.eigenvalues i : ℂ)) * v := by
      apply inj
      rw [← cm, ← cm, ← hs, hu]
    rw [cm, cm]
    congr 2
    ext i j
    have hij := congrFun (congrFun hv i) j
    rw [mul_diagonal, diagonal_mul] at hij ⊢
    by_cases h0 : v i j = 0
    · simp [h0]
    · have : hG.eigenvalues j = hG.eigenvalues i := by
        rw [mul_comm] at hij
        exact_mod_cast mul_right_cancel₀ h0 hij
      simp only [e, this, mul_comm]

/- English proof (translation)
Establish `hH : (1 + rᴴ * r).PosDef` using `PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)`. Take `⟨C, hC, hCH⟩` from `CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive`. Take `⟨⟨C, B, hCB, hBC⟩, rfl⟩` from `hC`. Simplify using `only [star_eq_conjTranspose] at hCH`. Establish `hCB' : Bᴴ * Cᴴ = 1` using `by rw [← conjTranspose_mul, hCB, conjTranspose_one]`.

Establish `hBC' : Cᴴ * Bᴴ = 1` using `by rw [← conjTranspose_mul, hBC, conjTranspose_one]`. Establish `hr' : rᴴ * rᴴ = 1` using `by rw [← conjTranspose_mul, hr, conjTranspose_one]`. Establish `e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X` using `fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]`. Establish `e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X` using `fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]`. Establish `e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X` using `fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]`.

Establish `e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X` using `fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]`. Establish `e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X` using `fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]`. Establish `e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X` using `fun X => by`. Rewrite using `[← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]`. Establish `hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C`.

Rewrite using `[← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]`. Establish `huu : (C * r * B) * (C * r * B) = 1`. Simplify using `only [Matrix.mul_assoc, e2, e5, hCB]`. Establish `hsu : (C * r * B)ᴴ * (C * r * B) = 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `hu : (C * r * B)ᴴ = C * r * B`. Combine the equalities or inequalities in the displayed calculation. Establish `hG' : (Bᴴ * G * B).IsHermitian` using `isHermitian_conjTranspose_mul_mul B hG`. Establish `hd' : (Bᴴ * G * B).det ≠ 0`. Introduce `h`.

Apply `hd` to reduce the goal to its premises. Establish `: G = Cᴴ * (Bᴴ * G * B) * C` using `by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]`. Rewrite using `[this, det_mul, det_mul, h, mul_zero, zero_mul]`. Establish `hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B)`. Establish `: (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B`.

Simplify using `only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]`. Rewrite `this` using `[hu]`. Use `conv_lhs => rw [← this]`. Rewrite using `[← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]`. Take `⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩` from `exists_sign hG' hd'`.

Establish `hs5` using `hs4 _ hc`. Use `⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation. Establish `hu : IsUnit C` using `⟨⟨C, B, hCB, hBC⟩, rfl⟩`.

Use `hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)` as an intermediate fact. Simplify `this` using `only [Matrix.mul_assoc, e4]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_comm {k : ℕ} {G r : Matrix (Fin k) (Fin k) ℂ} (hG : Gᴴ = G) (hd : G.det ≠ 0)
    (hr : r * r = 1) (hrG : rᴴ * G * r = G) : ∃ s, IsCartanInv G s ∧ s * r = r * s := by
  classical
  have hH : (1 + rᴴ * r).PosDef := PosDef.one.add_posSemidef (posSemidef_conjTranspose_mul_self r)
  obtain ⟨C, hC, hCH⟩ := CStarAlgebra.isStrictlyPositive_iff_eq_star_mul_self.mp hH.isStrictlyPositive
  obtain ⟨⟨C, B, hCB, hBC⟩, rfl⟩ := hC
  simp only [star_eq_conjTranspose] at hCH
  have hCB' : Bᴴ * Cᴴ = 1 := by rw [← conjTranspose_mul, hCB, conjTranspose_one]
  have hBC' : Cᴴ * Bᴴ = 1 := by rw [← conjTranspose_mul, hBC, conjTranspose_one]
  have hr' : rᴴ * rᴴ = 1 := by rw [← conjTranspose_mul, hr, conjTranspose_one]
  have e1 : ∀ X : Matrix (Fin k) (Fin k) ℂ, C * (B * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB, Matrix.one_mul]
  have e2 : ∀ X : Matrix (Fin k) (Fin k) ℂ, B * (C * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC, Matrix.one_mul]
  have e3 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Bᴴ * (Cᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hCB', Matrix.one_mul]
  have e4 : ∀ X : Matrix (Fin k) (Fin k) ℂ, Cᴴ * (Bᴴ * X) = X := fun X => by rw [← Matrix.mul_assoc, hBC', Matrix.one_mul]
  have e5 : ∀ X : Matrix (Fin k) (Fin k) ℂ, r * (r * X) = X := fun X => by rw [← Matrix.mul_assoc, hr, Matrix.one_mul]
  have e6 : ∀ X : Matrix (Fin k) (Fin k) ℂ, rᴴ * (G * (r * X)) = G * X := fun X => by
    rw [← Matrix.mul_assoc, ← Matrix.mul_assoc, hrG]
  have hinv : rᴴ * (Cᴴ * C) * r = Cᴴ * C := by
    rw [← hCH, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, ← Matrix.mul_assoc, hr', Matrix.one_mul, hr, add_comm]
  have huu : (C * r * B) * (C * r * B) = 1 := by
    simp only [Matrix.mul_assoc, e2, e5, hCB]
  have hsu : (C * r * B)ᴴ * (C * r * B) = 1 := by
    calc _ = Bᴴ * (rᴴ * (Cᴴ * C) * r) * B := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = 1 := by rw [hinv]; simp only [Matrix.mul_assoc, e3, hCB]
  have hu : (C * r * B)ᴴ = C * r * B := by
    calc _ = (C * r * B)ᴴ * ((C * r * B) * (C * r * B)) := by rw [huu, Matrix.mul_one]
      _ = _ := by rw [← Matrix.mul_assoc, hsu, Matrix.one_mul]
  have hG' : (Bᴴ * G * B).IsHermitian := isHermitian_conjTranspose_mul_mul B hG
  have hd' : (Bᴴ * G * B).det ≠ 0 := by
    intro h
    apply hd
    have : G = Cᴴ * (Bᴴ * G * B) * C := by simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
    rw [this, det_mul, det_mul, h, mul_zero, zero_mul]
  have hc : (C * r * B) * (Bᴴ * G * B) = (Bᴴ * G * B) * (C * r * B) := by
    have : (C * r * B)ᴴ * (Bᴴ * G * B) * (C * r * B) = Bᴴ * G * B := by
      simp only [conjTranspose_mul, Matrix.mul_assoc, e4, e2, e6]
    rw [hu] at this
    conv_lhs => rw [← this]
    rw [← Matrix.mul_assoc (C * r * B), ← Matrix.mul_assoc (C * r * B), huu, Matrix.one_mul]
  obtain ⟨s, ⟨hs1, hs2, hs3⟩, hs4⟩ := exists_sign hG' hd'
  have hs5 := hs4 _ hc
  refine ⟨B * s * C, ⟨?_, ?_, ?_⟩, ?_⟩
  · calc _ = B * (s * s) * C := by simp only [Matrix.mul_assoc, e1]
      _ = 1 := by rw [hs1, Matrix.mul_one, hBC]
  · calc _ = Cᴴ * (sᴴ * (Bᴴ * G * B) * s) * C := by simp only [conjTranspose_mul, Matrix.mul_assoc]
      _ = G := by rw [hs2]; simp only [Matrix.mul_assoc, e4, hBC, Matrix.mul_one]
  · have hu : IsUnit C := ⟨⟨C, B, hCB, hBC⟩, rfl⟩
    have := hs3.conjTranspose_mul_mul_same (Matrix.mulVec_injective_of_isUnit hu)
    simpa only [Matrix.mul_assoc, e4] using this
  · calc _ = B * (s * (C * r * B)) * C := by simp only [Matrix.mul_assoc, hBC, Matrix.mul_one]
      _ = _ := by rw [← hs5]; simp only [Matrix.mul_assoc, e2]

/- English proof (translation)
Introduce `n G hG hd x hx`. Use `set q := star x ⬝ᵥ G *ᵥ x with hq`. Establish `hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G`. Rewrite using `[vecMulVec_mul]`. Establish `hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x)`.

Rewrite using `[conjTranspose_vecMulVec, star_star]`. Establish `hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G)`. Rewrite using `[vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]`. Establish `hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G)`. Rewrite using `[hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]`.

Establish `hqs : star q = q`. Rewrite using `[hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]`. Generalize the expression as in `Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢`. Establish `hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM, smul_smul, add_assoc, ← add_smul, smul_add]`.

Establish `: -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0` using `by field_simp; ring`. Rewrite using `[this, zero_smul, add_zero]`. Establish `hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M)`. Establish `: star (-2 / q) = -2 / q` using `by rw [star_div₀, hqs]; simp`. Rewrite using `[conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]`.

Take `⟨s, hs, hc⟩` from `exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])`. Use `⟨s, hs, fun c => ?_⟩` and prove the remaining obligations. Establish `hsM : s * M = M * s`. Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, add_right_inj] at hc`. Conclude with `smul_right_injective _ (div_ne_zero (by norm_num) hx) hc`.

Simplify using `only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]`.
-/
theorem exists_cartan_comm_quasiReflection : ∀ (n : ℕ) (G : Matrix (Fin n) (Fin n) ℂ), Gᴴ = G → G.det ≠ 0 → ∀ x : Fin n → ℂ, star x ⬝ᵥ G *ᵥ x ≠ 0 → ∃ s, IsCartanInv G s ∧ ∀ c : ℂ, s * (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) = (1 + c • Matrix.vecMulVec x (star x ᵥ* G)) * s := by
  intro n G hG hd x hx
  set q := star x ⬝ᵥ G *ᵥ x with hq
  have hM : Matrix.vecMulVec x (star x ᵥ* G) = Matrix.vecMulVec x (star x) * G := by
    rw [vecMulVec_mul]
  have hN : (Matrix.vecMulVec x (star x))ᴴ = Matrix.vecMulVec x (star x) := by
    rw [conjTranspose_vecMulVec, star_star]
  have hMM : Matrix.vecMulVec x (star x ᵥ* G) * Matrix.vecMulVec x (star x ᵥ* G) = q • Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [vecMulVec_mul_vecMulVec, hq, dotProduct_mulVec, vecMulVec_smul]
  have hMG : (Matrix.vecMulVec x (star x ᵥ* G))ᴴ * G = G * Matrix.vecMulVec x (star x ᵥ* G) := by
    rw [hM, conjTranspose_mul, hN, hG, Matrix.mul_assoc]
  have hqs : star q = q := by
    rw [hq, ← star_dotProduct_star, star_star, star_mulVec, hG, dotProduct_mulVec]
  generalize Matrix.vecMulVec x (star x ᵥ* G) = M at hMM hMG ⊢
  have hr : (1 + (-2 / q) • M) * (1 + (-2 / q) • M) = 1 := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMM,
      smul_smul, add_assoc, ← add_smul, smul_add]
    have : -2 / q + (-2 / q + -2 / q * (-2 / q * q)) = 0 := by field_simp; ring
    rw [this, zero_smul, add_zero]
  have hrG : (1 + (-2 / q) • M)ᴴ * G = G * (1 + (-2 / q) • M) := by
    have : star (-2 / q) = -2 / q := by rw [star_div₀, hqs]; simp
    rw [conjTranspose_add, conjTranspose_one, conjTranspose_smul, this, Matrix.add_mul, Matrix.mul_add, Matrix.one_mul,
      Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hMG]
  obtain ⟨s, hs, hc⟩ := exists_comm hG hd hr (by rw [hrG, Matrix.mul_assoc, hr, Matrix.mul_one])
  refine ⟨s, hs, fun c => ?_⟩
  have hsM : s * M = M * s := by
    simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul,
      add_right_inj] at hc
    exact smul_right_injective _ (div_ne_zero (by norm_num) hx) hc
  simp only [Matrix.add_mul, Matrix.mul_add, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hsM]

end GlobalTheory.CartanRefl
