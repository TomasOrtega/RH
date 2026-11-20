import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.IsCplAtSelf
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsNoetherianRingAdicCompletionOfNoetherian

open IsLocalRing UpperTheory.V.AlgebraTools

/- English proof (translation)
Rewrite using `[AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L, ← Ideal.smul_top_eq_map, AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]`. Both sides reduce to the same expression.
-/
private lemma mem_pow_iff (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (x : AdicCompletion (maximalIdeal L) L) :
    x ∈ maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n ↔
      AdicCompletion.eval (maximalIdeal L) L n x = 0 := by
  rw [AdicCompletion.maximalIdeal_eq_map, ← Ideal.map_pow, ← Submodule.restrictScalars_mem L,
    ← Ideal.smul_top_eq_map,
    AdicCompletion.pow_smul_top_eq_ker_eval (maximalIdeal L).fg_of_isNoetherianRing]
  rfl

/- English proof (translation)
Rewrite `h` using `[mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply, AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Simplify `h` using `[smul_eq_mul, Ideal.mul_top]`.
-/
private lemma strict_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (a : L) (h : algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n) : a ∈ maximalIdeal L ^ n := by
  rw [mem_pow_iff, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply, Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at h
  simpa [smul_eq_mul, Ideal.mul_top] using h

/- English proof (translation)
Take `⟨a, ha⟩` from `Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)`. Use `⟨a, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply, AdicCompletion.of_apply]`. Simplify using the standard rewrite rules.
-/
private lemma dense_loc (L : Type) [CommRing L] [IsNoetherianRing L] [IsLocalRing L] (n : ℕ)
    (b : AdicCompletion (maximalIdeal L) L) :
    ∃ a : L, b - algebraMap L (AdicCompletion (maximalIdeal L) L) a ∈
      maximalIdeal (AdicCompletion (maximalIdeal L) L) ^ n := by
  obtain ⟨a, ha⟩ := Submodule.Quotient.mk_surjective _ (AdicCompletion.eval (maximalIdeal L) L n b)
  refine ⟨a, ?_⟩
  rw [mem_pow_iff, map_sub, ← ha, AdicCompletion.algebraMap_apply, AdicCompletion.eval_apply,
    AdicCompletion.of_apply]
  simp

/- English proof (translation)
Introduce `R _ _ p _`. Set `L` to `Localization.AtPrime p`. Establish `hRB : ∀ r : R, algebraMap R (CplAt R p) r = algebraMap L (CplAt R p) (algebraMap R L r)` using `fun r => IsScalarTower.algebraMap_apply R L (CplAt R p) r`. Use `⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap, IsLocalRing.maximalIdeal_comap]`.

Conclude with `Localization.AtPrime.comap_maximalIdeal`. Introduce `n b`. Take `⟨a', ha'⟩` from `dense_loc L n b`. Take `⟨⟨r, s⟩, rfl⟩` from `IsLocalization.mk'_surjective p.primeCompl a'`. Use `⟨r, s, s.2, ?_⟩` and prove the remaining obligations.

Establish `e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r = algebraMap R (CplAt R p) s * (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s))`. Rewrite using `[mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]`. Rewrite using `[e]`. Conclude with `Ideal.mul_mem_left _ _ ha'`. Introduce `n a ha`.

Rewrite `ha` using `[hRB]`. Establish `h1` using `strict_loc L n _ ha`. Rewrite `h1` using `[← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow, IsLocalization.mem_map_algebraMap_iff p.primeCompl]`. Take `⟨⟨⟨b, hb⟩, s⟩, hx⟩` from `h1`. Simplify using `only [← map_mul] at hx`.

Take `⟨c, hc⟩` from `(IsLocalization.eq_iff_exists p.primeCompl L).1 hx`. Use `⟨c * s, ?_, ?_⟩` and prove the remaining obligations. Conclude with `p.primeCompl.mul_mem c.2 s.2`. Establish `: (c : R) * s * a = c * b`. Rewrite using `[mul_assoc, mul_comm (s : R) a]`.

Conclude with `hc`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ hb`.
-/
theorem UpperTheory.V.AlgebraTools.isCplAt_cplAt :
    ∀ (R : Type) [CommRing R] [IsNoetherianRing R] (p : Ideal R) [p.IsPrime], IsCplAt R p (CplAt R p) := by
  intro R _ _ p _
  let L := Localization.AtPrime p
  have hRB : ∀ r : R, algebraMap R (CplAt R p) r =
      algebraMap L (CplAt R p) (algebraMap R L r) := fun r =>
    IsScalarTower.algebraMap_apply R L (CplAt R p) r
  refine ⟨GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion L (maximalIdeal L), inferInstance, ?_, ?_, ?_⟩
  · rw [IsScalarTower.algebraMap_eq R L (CplAt R p), ← Ideal.comap_comap,
      IsLocalRing.maximalIdeal_comap]
    exact Localization.AtPrime.comap_maximalIdeal
  · intro n b
    obtain ⟨a', ha'⟩ := dense_loc L n b
    obtain ⟨⟨r, s⟩, rfl⟩ := IsLocalization.mk'_surjective p.primeCompl a'
    refine ⟨r, s, s.2, ?_⟩
    have e : algebraMap R (CplAt R p) s * b - algebraMap R (CplAt R p) r =
        algebraMap R (CplAt R p) s *
          (b - algebraMap L (CplAt R p) (IsLocalization.mk' L r s)) := by
      rw [mul_sub, hRB, hRB, ← map_mul, mul_comm (algebraMap R L s), IsLocalization.mk'_spec]
    rw [e]
    exact Ideal.mul_mem_left _ _ ha'
  · intro n a ha
    rw [hRB] at ha
    have h1 := strict_loc L n _ ha
    rw [← Localization.AtPrime.map_eq_maximalIdeal, ← Ideal.map_pow,
      IsLocalization.mem_map_algebraMap_iff p.primeCompl] at h1
    obtain ⟨⟨⟨b, hb⟩, s⟩, hx⟩ := h1
    simp only [← map_mul] at hx
    obtain ⟨c, hc⟩ := (IsLocalization.eq_iff_exists p.primeCompl L).1 hx
    refine ⟨c * s, ?_, ?_⟩
    · exact p.primeCompl.mul_mem c.2 s.2
    · have : (c : R) * s * a = c * b := by
        rw [mul_assoc, mul_comm (s : R) a]
        exact hc
      rw [this]
      exact Ideal.mul_mem_left _ _ hb
