import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.FixedPointCriteria.Cond

open QuadraticAlgebra UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Loc.PK

/- English proof (translation)
Introduce `O K _ _ _ _ _ Δ τ L hD π n e h x hc`. Use `haveI := L.frac`. Establish `E : (ω - algebraMap O (Etau K τ) h) * (ω - algebraMap O (Etau K τ) h) = algebraMap O (Etau K τ) (π ^ n * π ^ n * e)`. Rewrite using `[hc.om, add_sub_cancel_left]`. Simplify using `only [yy, smul_mul_smul_comm, hc.sq]`.

Simplify using `only [algebraMap_etau (O := O), Algebra.smul_def, map_mul]`. Establish `Er` using `congrArg QuadraticAlgebra.re E`. Establish `Ei` using `congrArg QuadraticAlgebra.im E`. Simplify using `[algebraMap_etau] at Er Ei`. Establish `hτ : τ = 2 * algebraMap O K h` using `by linear_combination Ei`.

Establish `key : τ ^ 2 - 4 = (2 * algebraMap O K π ^ n) ^ 2 * algebraMap O K (e : O)`. Rewrite using `[hτ]`. Take the linear combination `4 * Er`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨r, hr⟩`.

Establish `hq : 2 * algebraMap O K π ^ n ≠ 0`. Introduce `h0`. Apply `hD` to reduce the goal to its premises. Rewrite using `[key, h0]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hsq : (r / (2 * algebraMap O K π ^ n)) ^ 2 = algebraMap O K (e : O)`. Rewrite using `[div_pow, sq r, ← hr, key]`. Conclude with `mul_div_cancel_left₀ _ (pow_ne_zero 2 hq)`. Take `⟨b, hb⟩` from `sq_int L _ _ hsq`. Use `⟨b, IsFractionRing.injective O K ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, hb, ← hsq]`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `⟨b, hb⟩`. Use `⟨2 * algebraMap O K π ^ n * algebraMap O K b, ?_⟩` and prove the remaining obligations. Rewrite using `[key, hb, map_mul]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.isSquare_sq_sub_four_iff_isSquare_unit :
    ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] (Δ τ : K), IsLoc O Δ → τ ^ 2 - 4 ≠ 0 → ∀ (π : O) (n : ℕ) (e : Oˣ) (h : O) (x : Etau K τ), Cond π n e h x → (IsSquare (τ ^ 2 - 4) ↔ IsSquare (e : O)) := by
  intro O K _ _ _ _ _ Δ τ L hD π n e h x hc
  haveI := L.frac
  have E : (ω - algebraMap O (Etau K τ) h) * (ω - algebraMap O (Etau K τ) h) = algebraMap O (Etau K τ) (π ^ n * π ^ n * e) := by
    rw [hc.om, add_sub_cancel_left]
    simp only [yy, smul_mul_smul_comm, hc.sq]
    simp only [algebraMap_etau (O := O), Algebra.smul_def, map_mul]
  have Er := congrArg QuadraticAlgebra.re E
  have Ei := congrArg QuadraticAlgebra.im E
  simp [algebraMap_etau] at Er Ei
  have hτ : τ = 2 * algebraMap O K h := by linear_combination Ei
  have key : τ ^ 2 - 4 = (2 * algebraMap O K π ^ n) ^ 2 * algebraMap O K (e : O) := by
    rw [hτ]
    linear_combination 4 * Er
  constructor
  · rintro ⟨r, hr⟩
    have hq : 2 * algebraMap O K π ^ n ≠ 0 := by
      intro h0
      apply hD
      rw [key, h0]
      ring
    have hsq : (r / (2 * algebraMap O K π ^ n)) ^ 2 = algebraMap O K (e : O) := by
      rw [div_pow, sq r, ← hr, key]
      exact mul_div_cancel_left₀ _ (pow_ne_zero 2 hq)
    obtain ⟨b, hb⟩ := sq_int L _ _ hsq
    refine ⟨b, IsFractionRing.injective O K ?_⟩
    rw [map_mul, hb, ← hsq]
    ring
  · rintro ⟨b, hb⟩
    refine ⟨2 * algebraMap O K π ^ n * algebraMap O K b, ?_⟩
    rw [key, hb, map_mul]
    ring
