import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HermitianTwists.RepNewformOf

open Complex in
/- English proof (translation)
Introduce `hS V _ _ A B C J H hAB hAC hBC hCB h0 hHA hHB hHC hJ0 hJA hJB hJC hex`. Take `⟨x, hx, n, hn⟩` from `hex`. Establish `h1 : (-(Complex.I • (B - C))) * (A + (Complex.I / 2) • (B + C)) - (A + (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C))) = (2 : ℂ) • (A + (Complex.I / 2) • (B + C))`. Use extensionality with `v`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]`.

Apply the tactic sequence `match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf`. Establish `h2 : (-(Complex.I • (B - C))) * (A - (Complex.I / 2) • (B + C)) - (A - (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C))) = (-2 : ℂ) • (A - (Complex.I / 2) • (B + C))`. Use extensionality with `v`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf`.

Establish `h3 : (4 : ℂ) • ((A + (Complex.I / 2) • (B + C)) * (A - (Complex.I / 2) • (B + C))) = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) - (2 : ℂ) • (-(Complex.I • (B - C))))`. Use extensionality with `v`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf`. Establish `h4 : (4 : ℂ) • ((A - (Complex.I / 2) • (B + C)) * (A + (Complex.I / 2) • (B + C))) = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) + (2 : ℂ) • (-(Complex.I • (B - C))))`.

Use extensionality with `v`. Simplify using `only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply, Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]`. Apply the tactic sequence `match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf`. Establish `h5 : ∀ u v, H ((-(Complex.I • (B - C))) u) v = H u ((-(Complex.I • (B - C))) v)`. Introduce `u v`.

Simplify using `only [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, map_neg, map_smulₛₗ, map_sub, hHB, hHC, Complex.conj_I, smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `h6 : ∀ u v, H ((A + (Complex.I / 2) • (B + C)) u) v = -H u ((A - (Complex.I / 2) • (B + C)) v)`. Introduce `u v`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub, map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h7 : ∀ u v, H ((A - (Complex.I / 2) • (B + C)) u) v = -H u ((A + (Complex.I / 2) • (B + C)) v)`. Introduce `u v`. Simplify using `only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub, map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `h8 : (-(Complex.I • (B - C))) x = (n : ℂ) • x`. Rewrite using `[LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, hn, smul_smul, ← neg_smul]`. Use `congr 1`. Put the polynomial expressions in normal form. Simplify using `[Complex.I_sq]`.

Take `⟨y, hy, hc⟩` from `hS V _ _ _ H h1 h2 h3 h4 h0 h5 h6 h7 ⟨x, hx, n, h8⟩`. Establish `eD : ∀ y, B y - C y = Complex.I • (-(Complex.I • (B - C))) y`. Introduce `y`. Rewrite using `[LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_neg, smul_smul, Complex.I_mul_I, neg_one_smul, neg_neg]`. Establish `eL : ∀ y, (A - (Complex.I / 2) • (B + C)) y = 0 → (2 : ℂ) • A y = Complex.I • (B y + C y)`.

Introduce `y h`. Rewrite `h` using `[LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.add_apply]`. Rewrite using `[h]`. Use `module`. Break down `hc with ⟨hW, hL⟩ | ⟨hW, hR⟩ | ⟨hW, hL⟩` into its components or cases.

Use `⟨y, hy, Or.inl ?_, eL y hL⟩` and prove the remaining obligations. Rewrite using `[eD, hW]`. Use `module`. Use `⟨J y, fun h => hy (hJ0 y h), Or.inl ?_, ?_⟩` and prove the remaining obligations. Establish `e` using `eD y`.

Rewrite `e` using `[hW]`. Rewrite using `[hJB, hJC, show -J (B y) - -J (C y) = -J (B y - C y) by rw [map_sub]; abel, e, map_smul, map_smul]`. Use `module`. Rewrite `hR` using `[LinearMap.add_apply, add_eq_zero_iff_eq_neg, LinearMap.smul_apply, LinearMap.add_apply]`. Rewrite using `[hJA, hJB, hJC, hR, map_neg, map_smul, map_add]`.

Use `module`. Use `⟨y, hy, Or.inr ?_, eL y hL⟩` and prove the remaining obligations. Rewrite using `[eD, hW, smul_zero]`.
-/
theorem UpperTheory.V.Af.Rn.lowTwo :
    UpperTheory.V.Af.Rn.Sl2Two → UpperTheory.V.Af.Rn.LowTwo := by
  intro hS V _ _ A B C J H hAB hAC hBC hCB h0 hHA hHB hHC hJ0 hJA hJB hJC hex
  obtain ⟨x, hx, n, hn⟩ := hex
  have h1 : (-(Complex.I • (B - C))) * (A + (Complex.I / 2) • (B + C))
      - (A + (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C)))
      = (2 : ℂ) • (A + (Complex.I / 2) • (B + C)) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h2 : (-(Complex.I • (B - C))) * (A - (Complex.I / 2) • (B + C))
      - (A - (Complex.I / 2) • (B + C)) * (-(Complex.I • (B - C)))
      = (-2 : ℂ) • (A - (Complex.I / 2) • (B + C)) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h3 : (4 : ℂ) • ((A + (Complex.I / 2) • (B + C)) * (A - (Complex.I / 2) • (B + C)))
      = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) - (2 : ℂ) • (-(Complex.I • (B - C)))) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h4 : (4 : ℂ) • ((A - (Complex.I / 2) • (B + C)) * (A + (Complex.I / 2) • (B + C)))
      = -((-(Complex.I • (B - C))) * (-(Complex.I • (B - C))) + (2 : ℂ) • (-(Complex.I • (B - C)))) := by
    ext v
    simp only [LinearMap.sub_apply, LinearMap.add_apply, LinearMap.smul_apply, LinearMap.neg_apply,
      Module.End.mul_apply, map_add, map_sub, map_smul, map_neg, hAB, hAC, hBC, hCB]
    match_scalars <;> ring_nf <;> simp [Complex.I_sq] <;> ring_nf
  have h5 : ∀ u v, H ((-(Complex.I • (B - C))) u) v = H u ((-(Complex.I • (B - C))) v) := by
    intro u v
    simp only [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, map_neg, map_smulₛₗ,
      map_sub, hHB, hHC, Complex.conj_I, smul_eq_mul, RingHom.id_apply]
    ring
  have h6 : ∀ u v, H ((A + (Complex.I / 2) • (B + C)) u) v = -H u ((A - (Complex.I / 2) • (B + C)) v) := by
    intro u v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub,
      map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]
    ring
  have h7 : ∀ u v, H ((A - (Complex.I / 2) • (B + C)) u) v = -H u ((A + (Complex.I / 2) • (B + C)) v) := by
    intro u v
    simp only [LinearMap.add_apply, LinearMap.sub_apply, LinearMap.smul_apply, map_add, map_sub,
      map_smulₛₗ, hHA, hHB, hHC, map_div₀, Complex.conj_I, map_ofNat, smul_eq_mul, RingHom.id_apply]
    ring
  have h8 : (-(Complex.I • (B - C))) x = (n : ℂ) • x := by
    rw [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, hn, smul_smul, ← neg_smul]
    congr 1
    ring_nf
    simp [Complex.I_sq]
  obtain ⟨y, hy, hc⟩ := hS V _ _ _ H h1 h2 h3 h4 h0 h5 h6 h7 ⟨x, hx, n, h8⟩
  have eD : ∀ y, B y - C y = Complex.I • (-(Complex.I • (B - C))) y := by
    intro y
    rw [LinearMap.neg_apply, LinearMap.smul_apply, LinearMap.sub_apply, smul_neg, smul_smul,
      Complex.I_mul_I, neg_one_smul, neg_neg]
  have eL : ∀ y, (A - (Complex.I / 2) • (B + C)) y = 0 → (2 : ℂ) • A y = Complex.I • (B y + C y) := by
    intro y h
    rw [LinearMap.sub_apply, sub_eq_zero, LinearMap.smul_apply, LinearMap.add_apply] at h
    rw [h]
    module
  rcases hc with ⟨hW, hL⟩ | ⟨hW, hR⟩ | ⟨hW, hL⟩
  · refine ⟨y, hy, Or.inl ?_, eL y hL⟩
    rw [eD, hW]
    module
  · refine ⟨J y, fun h => hy (hJ0 y h), Or.inl ?_, ?_⟩
    · have e := eD y
      rw [hW] at e
      rw [hJB, hJC, show -J (B y) - -J (C y) = -J (B y - C y) by rw [map_sub]; abel, e, map_smul, map_smul]
      module
    · rw [LinearMap.add_apply, add_eq_zero_iff_eq_neg, LinearMap.smul_apply, LinearMap.add_apply] at hR
      rw [hJA, hJB, hJC, hR, map_neg, map_smul, map_add]
      module
  · refine ⟨y, hy, Or.inr ?_, eL y hL⟩
    rw [eD, hW, smul_zero]
