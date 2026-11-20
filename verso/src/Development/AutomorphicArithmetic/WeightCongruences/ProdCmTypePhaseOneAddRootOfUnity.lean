import Mathlib
import Formalism.LocalRingCardinality.DataHost
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.HostFacts
import Development.AutomorphicArithmetic.WeightCongruences.ProdNegOneZpow
import Development.AutomorphicArithmetic.WeightCongruences.RootOfUnityGaloisActionCMDatum

open NumberField IsDedekindDomain Formalism.BasicNotions

/- English proof (translation)
Use `Finset.prod_involution (fun g _ => g * s) (fun g _ => hf g) ?_ (fun _ _ => Finset.mem_univ _) ?_` and prove the remaining obligations. Introduce `g _ _ h`. Apply `hs1` to reduce the goal to its premises. Simplify using `using h`. Introduce `g _`.

Rewrite using `[mul_assoc, hs2, mul_one]`.
-/
private theorem prod_pair {G : Type*} [Group G] [Fintype G] {M : Type*} [CommMonoid M]
    (s : G) (hs1 : s ≠ 1) (hs2 : s * s = 1) (f : G → M) (hf : ∀ g, f g * f (g * s) = 1) :
    ∏ g, f g = 1 := by
  refine Finset.prod_involution (fun g _ => g * s) (fun g _ => hf g) ?_ (fun _ _ => Finset.mem_univ _) ?_
  · intro g _ _ h
    apply hs1
    simpa using h
  · intro g _
    rw [mul_assoc, hs2, mul_one]

/- English proof (translation)
Establish `hn : ‖w‖ = 1`. Establish `h` using `congrArg (‖·‖) hw`. Simplify using `only [norm_pow, norm_one] at h`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg w) hm.ne').1 h`. Establish `hinv : w⁻¹ = (starRingEnd ℂ) w`.

Establish `: Complex.normSq w = 1`. Rewrite using `[Complex.normSq_eq_norm_sq, hn, one_pow]`. Rewrite using `[Complex.inv_def, this, inv_one, Complex.ofReal_one, mul_one]`. Establish `hconj : 1 + w⁻¹ = (starRingEnd ℂ) (1 + w)`. Rewrite using `[hinv, map_add, map_one]`.

Rewrite using `[hconj, Complex.norm_conj]`. Use `set a := 1 + w with ha`. Establish `hna : (‖a‖ : ℂ) ≠ 0`. Conclude with `(norm_ne_zero_iff.mpr hz)` after adjusting the coercions. Rewrite using `[div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
private theorem phase_pair (w : ℂ) (m : ℕ) (hm : 0 < m) (hw : w ^ m = 1) (hz : 1 + w ≠ 0) :
    (1 + w) / ((‖1 + w‖ : ℝ) : ℂ) * ((1 + w⁻¹) / ((‖1 + w⁻¹‖ : ℝ) : ℂ)) = 1 := by
  have hn : ‖w‖ = 1 := by
    have h := congrArg (‖·‖) hw
    simp only [norm_pow, norm_one] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg w) hm.ne').1 h
  have hinv : w⁻¹ = (starRingEnd ℂ) w := by
    have : Complex.normSq w = 1 := by
      rw [Complex.normSq_eq_norm_sq, hn, one_pow]
    rw [Complex.inv_def, this, inv_one, Complex.ofReal_one, mul_one]
  have hconj : 1 + w⁻¹ = (starRingEnd ℂ) (1 + w) := by
    rw [hinv, map_add, map_one]
  rw [hconj, Complex.norm_conj]
  set a := 1 + w with ha
  have hna : (‖a‖ : ℂ) ≠ 0 := by
    exact_mod_cast (norm_ne_zero_iff.mpr hz)
  rw [div_mul_div_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]
  push_cast
  field_simp

/- English proof (translation)
Introduce `R H ι _ eT z hz hzne`. Use `letI : Fintype R.Psi := Fintype.ofEquiv ι eT`. Use `set F : R.Psi → ℂ := fun p => H.emb (p : R.GG) (1 + z) / ((‖H.emb (p : R.GG) (1 + z)‖ : ℝ) : ℂ) with hF`. Express the relevant statement in the definitionally equal form `∏ τ, F (eT τ) = 1`. Rewrite using `[Equiv.prod_comp eT F]`.

Take `⟨m, hm, hzm⟩` from `hz`. Establish `hsg` using `(UpperTheory.rootOfUnity_galois_action_CMDatum R.toFrame H.toHostAx z ⟨m, hm, hzm⟩).2.2`. Use `prod_pair ⟨R.sg, R.sg_mem_Psi⟩ ?_ ?_ F ?_` and prove the remaining obligations. Introduce `h`. Conclude with `R.sg_ne_one (congrArg Subtype.val h)`.

Conclude with `Subtype.ext R.sg_mul_sg`. Introduce `g`. Establish `hz1 : 1 + z ≠ 0`. Introduce `h`. Apply `hzne` to reduce the goal to its premises.

Take the linear combination `h`. Establish `key : H.emb ((g * ⟨R.sg, R.sg_mem_Psi⟩ : R.Psi) : R.GG) (1 + z) = 1 + (H.emb (g : R.GG) z)⁻¹`. Simplify using `only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, Subgroup.coe_mul, map_mul, RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `H.φ₀ ((H.gal.symm (g : R.GG) * H.gal.symm R.sg) (1 + z)) = 1 + (H.φ₀ ((H.gal.symm (g : R.GG)) z))⁻¹`. Rewrite using `[AlgEquiv.mul_apply, map_add, map_one, hsg, map_add, map_one, map_inv₀, map_add, map_one, map_inv₀]`.

Establish `hne : 1 + H.emb (g : R.GG) z ≠ 0`. Establish `: H.emb (g : R.GG) (1 + z) ≠ 0` using `(map_ne_zero _).2 hz1`. Simplify using `using this`. Simplify using `only [hF, key]`. Establish `e1 : H.emb (g : R.GG) (1 + z) = 1 + H.emb (g : R.GG) z` using `by simp`.

Rewrite using `[e1]`. Conclude with `phase_pair _ m hm (by rw [← map_pow, hzm, map_one]) hne`.
-/
theorem UpperTheory.prod_cmType_phase_one_add_rootOfUnity :
    ∀ (R : Ranks) (H : Host R) (ι : Type) [Fintype ι] (eT : ι ≃ R.Psi) (z : H.E), (∃ m : ℕ, 0 < m ∧ z ^ m = 1) → z ≠ -1 →
      ∏ τ, (H.emb ((eT τ : R.Psi) : R.GG) (1 + z) / ((‖H.emb ((eT τ : R.Psi) : R.GG) (1 + z)‖ : ℝ) : ℂ)) = 1 := by
  intro R H ι _ eT z hz hzne
  letI : Fintype R.Psi := Fintype.ofEquiv ι eT
  set F : R.Psi → ℂ := fun p =>
    H.emb (p : R.GG) (1 + z) / ((‖H.emb (p : R.GG) (1 + z)‖ : ℝ) : ℂ) with hF
  change ∏ τ, F (eT τ) = 1
  rw [Equiv.prod_comp eT F]
  obtain ⟨m, hm, hzm⟩ := hz
  have hsg := (UpperTheory.rootOfUnity_galois_action_CMDatum R.toFrame H.toHostAx z ⟨m, hm, hzm⟩).2.2
  refine prod_pair ⟨R.sg, R.sg_mem_Psi⟩ ?_ ?_ F ?_
  · intro h
    exact R.sg_ne_one (congrArg Subtype.val h)
  · exact Subtype.ext R.sg_mul_sg
  · intro g
    have hz1 : 1 + z ≠ 0 := by
      intro h
      apply hzne
      linear_combination h
    have key : H.emb ((g * ⟨R.sg, R.sg_mem_Psi⟩ : R.Psi) : R.GG) (1 + z)
        = 1 + (H.emb (g : R.GG) z)⁻¹ := by
      simp only [Formalism.BasicNotions.Host.emb, Formalism.BasicNotions.Host.sigmaOf, Subgroup.coe_mul, map_mul,
        RingHom.comp_apply]
      change H.φ₀ ((H.gal.symm (g : R.GG) * H.gal.symm R.sg) (1 + z))
        = 1 + (H.φ₀ ((H.gal.symm (g : R.GG)) z))⁻¹
      rw [AlgEquiv.mul_apply, map_add, map_one, hsg, map_add, map_one, map_inv₀, map_add,
        map_one, map_inv₀]
    have hne : 1 + H.emb (g : R.GG) z ≠ 0 := by
      have : H.emb (g : R.GG) (1 + z) ≠ 0 := (map_ne_zero _).2 hz1
      simpa using this
    simp only [hF, key]
    have e1 : H.emb (g : R.GG) (1 + z) = 1 + H.emb (g : R.GG) z := by simp
    rw [e1]
    exact phase_pair _ m hm (by rw [← map_pow, hzm, map_one]) hne
