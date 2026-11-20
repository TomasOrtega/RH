import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.SphericalCoordinates.AlgebraEquivSetup.CodiffUnit
open NumberField Matrix GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Gen GlobalTheory.LKTrip GlobalTheory.LKGeo UpperTheory.Gal.W2.Seed
open scoped TensorProduct

/- English proof (translation)
Introduce `_ E _ _ _ A`. Take `⟨w, hw⟩ : ∃ w : E, w = (A.ω : E)` from `⟨_, rfl⟩`. Establish `h1 : w + IsCMField.complexConj E w = (A.tr : E)`. Establish `h` using `congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq`. Simplify `h` using `[A.bar_eq, hw]`.

Establish `h2 : w * IsCMField.complexConj E w = (A.nm : E)`. Establish `h` using `congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq`. Simplify `h` using `[A.bar_eq, hw]`. Establish `hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0`. Take the linear combination `w * h1 - h2`.

Establish `him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0`. Introduce `τ h0`. Establish `hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0`. Establish `h` using `congrArg τ hq`. Simplify using `using h`.

Establish `hr : τ w = (((τ w).re : ℝ) : ℂ)` using `Complex.ext (by simp) (by simp [h0])`. Take `⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ)` from `⟨_, hr⟩`. Rewrite `hz` using `[hr']`. Establish `hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0` using `by exact_mod_cast hz`. Establish `hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0` using `by exact_mod_cast A.disc_neg`.

Use polynomial arithmetic with `[sq_nonneg (2 * r - (A.tr : ℝ))]`. Establish `hint : IsIntegral ℚ w` using `Algebra.IsIntegral.isIntegral w`. Establish `hdeg : (minpoly ℚ w).natDegree = 2`. Establish `hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2` using `by compute_degree!`. Establish `hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0`.

Introduce `h`. Rewrite `hpd` using `[h]`. Simplify using `at hpd`. Establish `hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0`. Simplify using `using hq`.

Establish `hle` using `Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0`. Establish `hpos` using `minpoly.natDegree_pos hint`. Establish `hne : (minpoly ℚ w).natDegree ≠ 1`. Introduce `h`. Take `⟨q, hq'⟩` from `minpoly.natDegree_eq_one_iff.1 h`.

Apply `him A.τ₀` to reduce the goal to its premises. Rewrite using `[← hq']`. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Establish `hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2`.

Rewrite using `[IntermediateField.adjoin.finrank hint, hdeg]`. Establish `hmem : w ∈ IntermediateField.adjoin ℚ {w}` using `IntermediateField.mem_adjoin_simple_self ℚ w`. Use `⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩` and prove the remaining obligations. Conclude with `hfr`. Introduce `x hx`.

Rewrite using `[← hw]`. Set `pb` to `IntermediateField.adjoin.powerBasis hint`. Take `⟨f, hf, hfx⟩` from `pb.exists_eq_aeval ⟨x, hx⟩`. Establish `hdim : pb.dim = 2`. Rewrite using `[IntermediateField.adjoin.powerBasis_dim, hdeg]`.

Establish `hf1 : f.natDegree ≤ 1` using `by omega`. Rewrite `hfx` using `[Polynomial.eq_X_add_C_of_natDegree_le_one hf1]`. Use `⟨f.coeff 0, f.coeff 1, ?_⟩` and prove the remaining obligations. Establish `h` using `congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx`. Simplify using `[pb] at h`.

Rewrite using `[h]`. Simplify using `[add_comm]`.
-/
theorem UpperTheory.Gal.W2.Seed.pKqEx :
    TraceType → KqEx := by
  intro _ E _ _ _ A
  obtain ⟨w, hw⟩ : ∃ w : E, w = (A.ω : E) := ⟨_, rfl⟩
  have h1 : w + IsCMField.complexConj E w = (A.tr : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.tr_eq
    simpa [A.bar_eq, hw] using h
  have h2 : w * IsCMField.complexConj E w = (A.nm : E) := by
    have h := congrArg (fun z : 𝓞 E => (z : E)) A.nm_eq
    simpa [A.bar_eq, hw] using h
  have hq : w ^ 2 - (A.tr : E) * w + (A.nm : E) = 0 := by
    linear_combination w * h1 - h2
  have him : ∀ τ : E →+* ℂ, (τ w).im ≠ 0 := by
    intro τ h0
    have hz : (τ w) ^ 2 - (A.tr : ℂ) * τ w + (A.nm : ℂ) = 0 := by
      have h := congrArg τ hq
      simpa using h
    have hr : τ w = (((τ w).re : ℝ) : ℂ) := Complex.ext (by simp) (by simp [h0])
    obtain ⟨r, hr'⟩ : ∃ r : ℝ, τ w = (r : ℂ) := ⟨_, hr⟩
    rw [hr'] at hz
    have hz' : r ^ 2 - (A.tr : ℝ) * r + (A.nm : ℝ) = 0 := by exact_mod_cast hz
    have hd : ((A.tr : ℝ)) ^ 2 - 4 * (A.nm : ℝ) < 0 := by exact_mod_cast A.disc_neg
    nlinarith [sq_nonneg (2 * r - (A.tr : ℝ))]
  have hint : IsIntegral ℚ w := Algebra.IsIntegral.isIntegral w
  have hdeg : (minpoly ℚ w).natDegree = 2 := by
    have hpd : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ).natDegree = 2 := by
      compute_degree!
    have hp0 : (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) ≠ 0 := by
      intro h
      rw [h] at hpd
      simp at hpd
    have hroot : Polynomial.aeval w (Polynomial.X ^ 2 - Polynomial.C (A.tr : ℚ) * Polynomial.X + Polynomial.C (A.nm : ℚ) : Polynomial ℚ) = 0 := by
      simpa using hq
    have hle := Polynomial.natDegree_le_of_dvd (minpoly.dvd ℚ w hroot) hp0
    have hpos := minpoly.natDegree_pos hint
    have hne : (minpoly ℚ w).natDegree ≠ 1 := by
      intro h
      obtain ⟨q, hq'⟩ := minpoly.natDegree_eq_one_iff.1 h
      apply him A.τ₀
      rw [← hq']
      simp
    omega
  have hfr : Module.finrank ℚ (IntermediateField.adjoin ℚ {w}) = 2 := by
    rw [IntermediateField.adjoin.finrank hint, hdeg]
  have hmem : w ∈ IntermediateField.adjoin ℚ {w} := IntermediateField.mem_adjoin_simple_self ℚ w
  refine ⟨(IntermediateField.adjoin ℚ {w}).toSubfield, hw ▸ hmem, ⟨?_, fun τ => ⟨w, hmem, him τ⟩⟩, ?_⟩
  · exact hfr
  · intro x hx
    rw [← hw]
    let pb := IntermediateField.adjoin.powerBasis hint
    obtain ⟨f, hf, hfx⟩ := pb.exists_eq_aeval ⟨x, hx⟩
    have hdim : pb.dim = 2 := by
      rw [IntermediateField.adjoin.powerBasis_dim, hdeg]
    have hf1 : f.natDegree ≤ 1 := by omega
    rw [Polynomial.eq_X_add_C_of_natDegree_le_one hf1] at hfx
    refine ⟨f.coeff 0, f.coeff 1, ?_⟩
    have h := congrArg (fun z : IntermediateField.adjoin ℚ {w} => (z : E)) hfx
    simp [pb] at h
    rw [h]
    simp [add_comm]
