import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.NormOneIsCoboundaryUnramifiedQuadratic

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc

/- English proof (translation)
Establish `h` using `L.two.map (algebraMap O K)`. Rewrite `h` using `[map_ofNat]`. Conclude with `h.ne_zero`.
-/
private theorem two_ne {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] {Δ : K} (L : IsLoc O Δ) : (2 : K) ≠ 0 := by
  have h := L.two.map (algebraMap O K)
  rw [map_ofNat] at h
  exact h.ne_zero

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ hL c u hu2 hnu ν hν s hs`. Establish `h2 : (2 : K) ≠ 0` using `two_ne hL`. Establish `ofE_sm : ∀ (r : K) (y : Etau K τ), ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y`. Introduce `r y`. Apply the tactic sequence `ext <;> simp [ofE]`.

Establish `ofE_mul : ∀ x y : Etau K τ, ofE Δ (x * y) = ofE Δ x * ofE Δ y`. Introduce `x y`. Apply the tactic sequence `ext <;> simp [ofE] <;> ring`. Establish `sig_ofE : ∀ y : Etau K τ, sigL (ofE Δ y) = ofE Δ y`. Introduce `y`.

Apply the tactic sequence `ext <;> simp [sigL, ofE]`. Establish `star_ofE : ∀ y : Etau K τ, star (ofE Δ y) = ofE Δ (star y)`. Introduce `y`. Apply the tactic sequence `ext <;> simp [ofE]`. Establish `sig_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), sigL (a • y) = star a • sigL y`.

Introduce `a y`. Apply the tactic sequence `ext <;> simp [sigL]`. Establish `star_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), star (a • y) = a • star y`. Introduce `a y`. Apply the tactic sequence `ext <;> simp <;> ring`.

Establish `hν' : ν * star ν = algebraMap K (Lsq K Δ) (-1)`. Rewrite using `[← algebraMap_norm_eq_mul_star, hν]`. Establish `hus : u * star u = algebraMap K (Etau K τ) 1`. Rewrite using `[← algebraMap_norm_eq_mul_star, hnu]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[sig_sm, sig_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, ← sq, hu2]`. Use `congr 1`. Rewrite using `[map_neg, map_one]`. Expand and normalize the polynomial expressions, which then agree. Introduce `m hm`.

Establish `hd : ν • ofE Δ u * star (sigL (ν • ofE Δ u)) = -1`. Rewrite using `[sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, hus]`. Apply the tactic sequence `ext <;> simp [ofE]`. Establish `hsig : sigL m = -m`. Rewrite using `[hm.m_sig, mul_assoc, hd, mul_neg_one]`.

Establish `hst : star m = -m`. Establish `h` using `hm.m_star`. Rewrite `h` using `[hsig, star_neg]`. Conclude with `neg_eq_iff_eq_neg.mp h`. Establish `e1 : m.re.re = 0`.

Establish `h` using `congrArg (fun y : EL Δ τ => y.re.re) hsig`. Simplify using `[sigL] at h`. Establish `h' : 2 * m.re.re = 0` using `by linear_combination h`. Conclude with `(mul_eq_zero.mp h').resolve_left h2`. Establish `e2 : m.im.re = 0`.

Establish `h` using `congrArg (fun y : EL Δ τ => y.im.re) hsig`. Simplify using `[sigL] at h`. Establish `h' : 2 * m.im.re = 0` using `by linear_combination h`. Conclude with `(mul_eq_zero.mp h').resolve_left h2`. Establish `e3 : 2 * m.re.im = -τ * m.im.im`.

Establish `h` using `congrArg (fun y : EL Δ τ => y.re.im) hst`. Simplify using `at h`. Take the linear combination `h`. Establish `hq : m.im.im ≠ 0`. Introduce `hq0`.

Establish `e4 : m.re.im = 0`. Establish `h' : 2 * m.re.im = 0` using `by rw [e3, hq0, mul_zero]`. Conclude with `(mul_eq_zero.mp h').resolve_left h2`. Establish `hm0 : m = 0`. Use `ext`.

Conclude with `e1`. Conclude with `e4`. Conclude with `e2`. Conclude with `hq0`. Conclude with `not_isUnit_zero (hm0 ▸ hm.m_unit)`.

Use `⟨Units.mk0 (m.im.im / (2 * s)) (div_ne_zero hq (mul_ne_zero h2 hs)), ?_⟩` and prove the remaining obligations. Use `ext`. Simplify using `[ofE, e1]`. Simplify using `[ofE]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e3`. Simplify using `[ofE, e2]`. Simplify using `[ofE]`. Clear the denominators using the available nonvanishing facts. Evaluate the numerical expressions.
-/
theorem UpperTheory.V.Z.Sym.Loc.datFormM : UpperTheory.V.Z.Sym.Loc.DatFormM := by
  intro O K _ _ _ _ _ Δ τ hL c u hu2 hnu ν hν s hs
  have h2 : (2 : K) ≠ 0 := two_ne hL
  have ofE_sm : ∀ (r : K) (y : Etau K τ),
      ofE Δ (algebraMap K (Etau K τ) r * y) = (algebraMap K (Lsq K Δ) r) • ofE Δ y := by
    intro r y
    ext <;> simp [ofE]
  have ofE_mul : ∀ x y : Etau K τ, ofE Δ (x * y) = ofE Δ x * ofE Δ y := by
    intro x y
    ext <;> simp [ofE] <;> ring
  have sig_ofE : ∀ y : Etau K τ, sigL (ofE Δ y) = ofE Δ y := by
    intro y
    ext <;> simp [sigL, ofE]
  have star_ofE : ∀ y : Etau K τ, star (ofE Δ y) = ofE Δ (star y) := by
    intro y
    ext <;> simp [ofE]
  have sig_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), sigL (a • y) = star a • sigL y := by
    intro a y
    ext <;> simp [sigL]
  have star_sm : ∀ (a : Lsq K Δ) (y : EL Δ τ), star (a • y) = a • star y := by
    intro a y
    ext <;> simp <;> ring
  have hν' : ν * star ν = algebraMap K (Lsq K Δ) (-1) := by
    rw [← algebraMap_norm_eq_mul_star, hν]
  have hus : u * star u = algebraMap K (Etau K τ) 1 := by
    rw [← algebraMap_norm_eq_mul_star, hnu]
  refine ⟨?_, ?_⟩
  · rw [sig_sm, sig_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, ← sq, hu2]
    congr 1
    rw [map_neg, map_one]
    ring
  · intro m hm
    have hd : ν • ofE Δ u * star (sigL (ν • ofE Δ u)) = -1 := by
      rw [sig_sm, sig_ofE, star_sm, star_ofE, smul_mul_smul_comm, hν', ← ofE_mul, ← ofE_sm, hus]
      ext <;> simp [ofE]
    have hsig : sigL m = -m := by
      rw [hm.m_sig, mul_assoc, hd, mul_neg_one]
    have hst : star m = -m := by
      have h := hm.m_star
      rw [hsig, star_neg] at h
      exact neg_eq_iff_eq_neg.mp h
    have e1 : m.re.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.re.re) hsig
      simp [sigL] at h
      have h' : 2 * m.re.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e2 : m.im.re = 0 := by
      have h := congrArg (fun y : EL Δ τ => y.im.re) hsig
      simp [sigL] at h
      have h' : 2 * m.im.re = 0 := by linear_combination h
      exact (mul_eq_zero.mp h').resolve_left h2
    have e3 : 2 * m.re.im = -τ * m.im.im := by
      have h := congrArg (fun y : EL Δ τ => y.re.im) hst
      simp at h
      linear_combination h
    have hq : m.im.im ≠ 0 := by
      intro hq0
      have e4 : m.re.im = 0 := by
        have h' : 2 * m.re.im = 0 := by rw [e3, hq0, mul_zero]
        exact (mul_eq_zero.mp h').resolve_left h2
      have hm0 : m = 0 := by
        ext
        · exact e1
        · exact e4
        · exact e2
        · exact hq0
      exact not_isUnit_zero (hm0 ▸ hm.m_unit)
    refine ⟨Units.mk0 (m.im.im / (2 * s)) (div_ne_zero hq (mul_ne_zero h2 hs)), ?_⟩
    ext
    · simp [ofE, e1]
    · simp [ofE]
      field_simp
      linear_combination e3
    · simp [ofE, e2]
    · simp [ofE]
      field_simp
      norm_num
