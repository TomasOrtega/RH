import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.InertiaQuadraticRamification.InertSplitAlt

noncomputable section

open NumberField IsDedekindDomain

namespace UpperTheory.Gal.UnramifiedFromSplittingCriterion

/- English proof (translation)
Introduce `h`. Establish `hv : (p : 𝓞 K) ∈ w.asIdeal` using `Ideal.pow_le_self two_ne_zero h`. Establish `hpz : Prime (p : ℤ)` using `Nat.prime_iff_prime_int.mp hp`. Establish `hmax : (Ideal.span {(p : ℤ)}).IsMaximal` using `PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible`. Establish `hP` using `w.isPrime`.

Establish `hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)})` using `(Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)`. Establish `hb : Ideal.span {(p : ℤ)} ≠ ⊥` using `by simpa using hp.ne_zero`. Establish `hun` using `(not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)`. Establish `hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)}` using `hlo.over.symm`. Establish `: Finite (ℤ ⧸ w.asIdeal.under ℤ)` using `Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)`.

Establish `: (w.asIdeal.under ℤ).IsMaximal` using `hu ▸ hmax`. Establish `: Finite (w.asIdeal.under ℤ).ResidueField` using `inferInstance`. Establish `he : w.asIdeal.ramificationIdx ℤ = 1` using `Ideal.ramificationIdx_eq_one_iff.2 hun`. Establish `hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)}`. Rewrite using `[Ideal.map_span]`.

Simplify using the standard rewrite rules. Establish `hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal`. Rewrite using `[hmap, Ideal.span_le]`. Simplify using `using hv`. Rewrite `he` using `[← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb]`.

Use `(Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he` and prove the remaining obligations. Rewrite using `[hmap, Ideal.span_le]`. Simplify using `using h`.
-/
private theorem natCast_notMem_sq {K : Type} [Field K] [NumberField K] {p : ℕ} (hp : p.Prime)
    (hd : ¬ (p : ℤ) ∣ discr K) (w : HeightOneSpectrum (𝓞 K)) : (p : 𝓞 K) ∉ w.asIdeal ^ 2 := by
  intro h
  have hv : (p : 𝓞 K) ∈ w.asIdeal := Ideal.pow_le_self two_ne_zero h
  have hpz : Prime (p : ℤ) := Nat.prime_iff_prime_int.mp hp
  have hmax : (Ideal.span {(p : ℤ)}).IsMaximal := PrincipalIdealRing.isMaximal_of_irreducible hpz.irreducible
  have hP := w.isPrime
  have hlo : w.asIdeal.LiesOver (Ideal.span {(p : ℤ)}) := (Ideal.liesOver_span_iff hP.ne_top hpz).2 (by simpa using hv)
  have hb : Ideal.span {(p : ℤ)} ≠ ⊥ := by simpa using hp.ne_zero
  have hun := (not_dvd_discr_iff_forall_mem K (𝓞 K) hpz).1 hd w.asIdeal hP (by simpa using hv)
  have hu : w.asIdeal.under ℤ = Ideal.span {(p : ℤ)} := hlo.over.symm
  have : Finite (ℤ ⧸ w.asIdeal.under ℤ) := Ideal.finiteQuotientOfFreeOfNeBot _ (hu ▸ hb)
  have : (w.asIdeal.under ℤ).IsMaximal := hu ▸ hmax
  have : Finite (w.asIdeal.under ℤ).ResidueField := inferInstance
  have he : w.asIdeal.ramificationIdx ℤ = 1 := Ideal.ramificationIdx_eq_one_iff.2 hun
  have hmap : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) = Ideal.span {(p : 𝓞 K)} := by
    rw [Ideal.map_span]; simp
  have hle : Ideal.map (algebraMap ℤ (𝓞 K)) (Ideal.span {(p : ℤ)}) ≤ w.asIdeal := by
    rw [hmap, Ideal.span_le]; simpa using hv
  rw [← Ideal.ramificationIdx'_eq_ramificationIdx (Ideal.span {(p : ℤ)}) w.asIdeal hb] at he
  refine (Ideal.ramificationIdx'_ne_one_iff hle).2 ?_ he
  rw [hmap, Ideal.span_le]
  simpa using h

/- English proof (translation)
Introduce `K _ _`. Use `⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩` and prove the remaining obligations. Establish `h1 : p ∣ (discr K).natAbs` using `Int.natCast_dvd.mp hd`. Establish `h2 : 0 < (discr K).natAbs` using `Int.natAbs_pos.mpr (discr_ne_zero K)`. Conclude with `absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)`.
-/
theorem unrLarge : UnrLarge := by
  intro K _ _
  refine ⟨(discr K).natAbs, fun p hp hB w => natCast_notMem_sq hp (fun hd => ?_) w⟩
  have h1 : p ∣ (discr K).natAbs := Int.natCast_dvd.mp hd
  have h2 : 0 < (discr K).natAbs := Int.natAbs_pos.mpr (discr_ne_zero K)
  exact absurd (Nat.le_of_dvd h2 h1) (not_le.mpr hB)

end UpperTheory.Gal.UnramifiedFromSplittingCriterion
