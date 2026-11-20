import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.NonsqMul
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.HsLaw

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hD lam y hl hX hX'`. Use `haveI := L.frac`. Establish `h0 : Δ ≠ 0`. Take `⟨u, s, hs, e⟩` from `L.even`. Rewrite using `[e]`.

Conclude with `mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)`. Establish `hN : QuadraticAlgebra.norm (y : Lsq K Δ) ≠ 0` using `(QuadraticAlgebra.isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero`. Use `set l' := lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) with hl'`. Establish `e1 : QuadraticAlgebra.norm (y : Lsq K Δ) • l' = lam * star (y : Lsq K Δ) ^ 2`. Rewrite using `[Algebra.smul_def, QuadraticAlgebra.algebraMap_norm_eq_mul_star, hl']`.

Take the linear combination `(lam * star (y : Lsq K Δ) ^ 2) * y.mul_inv`. Establish `e2` using `congrArg QuadraticAlgebra.trace e1`. Rewrite `e2` using `[map_smul, smul_eq_mul]`. Unfold `eps`. Use `set N := QuadraticAlgebra.norm (y : Lsq K Δ) with hNd`.

Use `set X := 2 + τ + QuadraticAlgebra.trace lam with hXd`. Use `set X' := 2 + τ + QuadraticAlgebra.trace l' with hXd'`. Establish `key : (2 * (lam.re * (y : Lsq K Δ).re - Δ * lam.im * (y : Lsq K Δ).im) + (y : Lsq K Δ).re * (2 + τ)) ^ 2 - ((τ ^ 2 - 4) * Δ) * (y : Lsq K Δ).im ^ 2 = X * X' * N`. Establish `e3 : X' * N = (2 + τ) * N + QuadraticAlgebra.trace (lam * star (y : Lsq K Δ) ^ 2)` using `by rw [← e2, hXd']; ring`. Rewrite using `[mul_assoc X, e3, hXd, hNd]`.

Rewrite `hl` using `[QuadraticAlgebra.norm_def]`. Simplify using `[QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, sq] at hl ⊢`. Take the linear combination `(-4 * Δ * (y : Lsq K Δ).im ^ 2) * hl`. Establish `hP : X * X' * N ≠ 0` using `mul_ne_zero (mul_ne_zero hX hX') hN`. Establish `H` using `hsLaw O K Δ L`.

Establish `h1 : hs (τ ^ 2 - 4) (X * X' * N) * hs Δ (X * X' * N) = 1`. Rewrite using `[H.1 _ _ hD hP, H.1 _ _ h0 hP, ← hsMul O K Δ L _ _ _ hP hD h0, H.1 _ _ hP (mul_ne_zero hD h0)]`. Conclude with `if_pos ⟨_, _, key⟩`. Establish `h2 : hs Δ N = 1` using `if_pos ⟨(y : Lsq K Δ).re, (y : Lsq K Δ).im, by rw [hNd, QuadraticAlgebra.norm_def]; ring⟩`. Rewrite `h1` using `[hsMul O K Δ L _ _ _ hD (mul_ne_zero hX hX') hN, hsMul O K Δ L _ _ _ hD hX hX', hsMul O K Δ L _ _ _ h0 (mul_ne_zero hX hX') hN, hsMul O K Δ L _ _ _ h0 hX hX', h2]`.

Apply the tactic sequence `have hq : ∀ D x : K, hs D x * hs D x = 1 := fun D x => by unfold hs; split_ifs <;> norm_num`. Establish `a` using `hq (τ ^ 2 - 4) X'`. Establish `b` using `hq Δ X'`. Take the linear combination `(-hs (τ ^ 2 - 4) X' * hs Δ X') * h1 + (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X * hs Δ X' * hs Δ X') * a + (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X) * b`.
-/
theorem UpperTheory.V.Z.Sym.Loc.signLaw : UpperTheory.V.Z.Sym.Loc.SignLaw := by
  intro O K _ _ _ _ _ Δ τ L hD lam y hl hX hX'
  haveI := L.frac
  have h0 : Δ ≠ 0 := by
    obtain ⟨u, s, hs, e⟩ := L.even
    rw [e]
    exact mul_ne_zero (u.isUnit.map (algebraMap O K)).ne_zero (pow_ne_zero 2 hs)
  have hN : QuadraticAlgebra.norm (y : Lsq K Δ) ≠ 0 := (QuadraticAlgebra.isUnit_iff_norm_isUnit.1 y.isUnit).ne_zero
  set l' := lam * star (y : Lsq K Δ) * ((y⁻¹ : (Lsq K Δ)ˣ) : Lsq K Δ) with hl'
  have e1 : QuadraticAlgebra.norm (y : Lsq K Δ) • l' = lam * star (y : Lsq K Δ) ^ 2 := by
    rw [Algebra.smul_def, QuadraticAlgebra.algebraMap_norm_eq_mul_star, hl']
    linear_combination (lam * star (y : Lsq K Δ) ^ 2) * y.mul_inv
  have e2 := congrArg QuadraticAlgebra.trace e1
  rw [map_smul, smul_eq_mul] at e2
  unfold eps
  set N := QuadraticAlgebra.norm (y : Lsq K Δ) with hNd
  set X := 2 + τ + QuadraticAlgebra.trace lam with hXd
  set X' := 2 + τ + QuadraticAlgebra.trace l' with hXd'
  have key : (2 * (lam.re * (y : Lsq K Δ).re - Δ * lam.im * (y : Lsq K Δ).im) + (y : Lsq K Δ).re * (2 + τ)) ^ 2 -
      ((τ ^ 2 - 4) * Δ) * (y : Lsq K Δ).im ^ 2 = X * X' * N := by
    have e3 : X' * N = (2 + τ) * N + QuadraticAlgebra.trace (lam * star (y : Lsq K Δ) ^ 2) := by rw [← e2, hXd']; ring
    rw [mul_assoc X, e3, hXd, hNd]
    rw [QuadraticAlgebra.norm_def] at hl
    simp [QuadraticAlgebra.norm_def, QuadraticAlgebra.trace_def, sq] at hl ⊢
    linear_combination (-4 * Δ * (y : Lsq K Δ).im ^ 2) * hl
  have hP : X * X' * N ≠ 0 := mul_ne_zero (mul_ne_zero hX hX') hN
  have H := hsLaw O K Δ L
  have h1 : hs (τ ^ 2 - 4) (X * X' * N) * hs Δ (X * X' * N) = 1 := by
    rw [H.1 _ _ hD hP, H.1 _ _ h0 hP, ← hsMul O K Δ L _ _ _ hP hD h0, H.1 _ _ hP (mul_ne_zero hD h0)]
    exact if_pos ⟨_, _, key⟩
  have h2 : hs Δ N = 1 := if_pos ⟨(y : Lsq K Δ).re, (y : Lsq K Δ).im, by rw [hNd, QuadraticAlgebra.norm_def]; ring⟩
  rw [hsMul O K Δ L _ _ _ hD (mul_ne_zero hX hX') hN, hsMul O K Δ L _ _ _ hD hX hX', hsMul O K Δ L _ _ _ h0 (mul_ne_zero hX hX') hN,
    hsMul O K Δ L _ _ _ h0 hX hX', h2] at h1
  have hq : ∀ D x : K, hs D x * hs D x = 1 := fun D x => by unfold hs; split_ifs <;> norm_num
  have a := hq (τ ^ 2 - 4) X'
  have b := hq Δ X'
  linear_combination (-hs (τ ^ 2 - 4) X' * hs Δ X') * h1 +
    (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X * hs Δ X' * hs Δ X') * a + (hs (τ ^ 2 - 4) X * hs (τ ^ 2 - 4) N * hs Δ X) * b
