import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RbUVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.FerreroWashington

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V.Base UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws UpperTheory.V.Two
open scoped Classical

/- English proof (translation)
Introduce `F _ _ l hl S`. Establish `hl0 : (l : ℤ) ≠ 0` using `by exact_mod_cast hl.out.ne_zero`. Use `set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef`. Establish `hpp : p.IsPrime` using `(Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)`. Establish `hpb : p ≠ ⊥`.

Rewrite using `[hpdef, Ne, Ideal.span_singleton_eq_bot]`. Conclude with `hl0`. Use `haveI hpm : p.IsMaximal := hpp.isMaximal hpb`. Establish `key` using `Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)`. Rewrite `key` using `[NumberField.RingOfIntegers.rank]`.

Rewrite using `[← key, ← Finset.sum_filter]`. Use `set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg`. Establish `h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I`. Rewrite using `[Finset.sum_image]`. Both sides reduce to the same expression.

Introduce `a _ b _ hab`. Conclude with `HeightOneSpectrum.ext hab`. Establish `h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I`. Rewrite using `[Finset.sum_image]`. Introduce `a _ b _ hab`.

Conclude with `Subtype.ext hab`. Rewrite using `[h1, h2]`. Apply `Finset.sum_le_sum_of_subset_of_nonneg` to reduce the goal to its premises. Introduce `I hI`. Simplify using `only [Finset.mem_image, Finset.mem_filter] at hI`.

Take `⟨v, ⟨_, hv⟩, rfl⟩` from `hI`. Simplify using `only [Finset.mem_image, Finset.mem_univ, true_and]`. Establish `hle : p ≤ Ideal.under ℤ v.asIdeal`. Rewrite using `[hpdef, Ideal.span_le, Set.singleton_subset_iff]`. Simplify `hv` using `[Ideal.under, Ideal.mem_comap]`.

Establish `hne : Ideal.under ℤ v.asIdeal ≠ ⊤` using `(Ideal.IsPrime.under ℤ v.asIdeal).ne_top`. Establish `heq : p = Ideal.under ℤ v.asIdeal` using `hpm.eq_of_le hne hle`. Conclude with `⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩`. Introduce `_ _ _`. Conclude with `Nat.zero_le _`.
-/
theorem UpperTheory.V.Ws.sum_local_degree_above_l_le_finrank :
    ∀ (F : Type) [Field F] [NumberField F] (l : ℕ) [Fact l.Prime] (S : Finset (HeightOneSpectrum (𝓞 F))), (∑ v ∈ S, if ((l : ℕ) : 𝓞 F) ∈ v.asIdeal then locDeg v else 0) ≤ Module.finrank ℚ F := by
  intro F _ _ l hl S
  have hl0 : (l : ℤ) ≠ 0 := by exact_mod_cast hl.out.ne_zero
  set p : Ideal ℤ := Ideal.span {(l : ℤ)} with hpdef
  have hpp : p.IsPrime := (Ideal.span_singleton_prime hl0).2 (Nat.prime_iff_prime_int.mp hl.out)
  have hpb : p ≠ ⊥ := by
    rw [hpdef, Ne, Ideal.span_singleton_eq_bot]
    exact hl0
  haveI hpm : p.IsMaximal := hpp.isMaximal hpb
  have key := Ideal.sum_ramification_inertia_eq_finrank p (𝓞 F)
  rw [NumberField.RingOfIntegers.rank] at key
  rw [← key, ← Finset.sum_filter]
  set g : Ideal (𝓞 F) → ℕ := fun I => I.ramificationIdx ℤ * I.inertiaDeg ℤ with hg
  have h1 : ∑ v ∈ S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal), locDeg v
      = ∑ I ∈ (S.filter (fun v => ((l : ℕ) : 𝓞 F) ∈ v.asIdeal)).image (fun v => v.asIdeal), g I := by
    rw [Finset.sum_image]
    · rfl
    · intro a _ b _ hab
      exact HeightOneSpectrum.ext hab
  have h2 : ∑ q : p.primesOver (𝓞 F), q.1.ramificationIdx ℤ * q.1.inertiaDeg ℤ
      = ∑ I ∈ (Finset.univ : Finset (p.primesOver (𝓞 F))).image Subtype.val, g I := by
    rw [Finset.sum_image]
    intro a _ b _ hab
    exact Subtype.ext hab
  rw [h1, h2]
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro I hI
    simp only [Finset.mem_image, Finset.mem_filter] at hI
    obtain ⟨v, ⟨_, hv⟩, rfl⟩ := hI
    simp only [Finset.mem_image, Finset.mem_univ, true_and]
    have hle : p ≤ Ideal.under ℤ v.asIdeal := by
      rw [hpdef, Ideal.span_le, Set.singleton_subset_iff]
      simpa [Ideal.under, Ideal.mem_comap] using hv
    have hne : Ideal.under ℤ v.asIdeal ≠ ⊤ := (Ideal.IsPrime.under ℤ v.asIdeal).ne_top
    have heq : p = Ideal.under ℤ v.asIdeal := hpm.eq_of_le hne hle
    exact ⟨⟨v.asIdeal, ⟨v.isPrime, ⟨heq⟩⟩⟩, rfl⟩
  · intro _ _ _
    exact Nat.zero_le _
