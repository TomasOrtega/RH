import Development.AutomorphicArithmetic.AutomorphicVarieties.PatchingModules.DeterminantPadicFree.FrameWith

open Matrix IsLocalRing UpperTheory.V.Alg UpperTheory.V.W UpperTheory.V.Pa

/- English proof (translation)
Introduce `K K' _ _ _ j`. Use `haveI := Fintype.ofFinite K`. Use `set p := ringChar K with hpdef`. Use `haveI : CharP K p := ringChar.charP K`. Take `⟨n, hp, hq⟩` from `FiniteField.card K p`.

Use `haveI : Fact p.Prime := ⟨hp⟩`. Use `set e : K →+* PowerSeries K' := j.comp PowerSeries.C`. Use `haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p`. Establish `key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f)`. Introduce `f hf`.

Use `set c := PowerSeries.constantCoeff f with hcdef`. Establish `hc : c ^ (p ^ (n : ℕ)) = c`. Establish `h2` using `congrArg PowerSeries.constantCoeff hf`. Rewrite `h2` using `[map_pow]`. Conclude with `h2`.

Establish `hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c`. Rewrite using `[sub_pow_char_pow, hf, ← map_pow, hc]`. Establish `hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0`. Rewrite using `[map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]`. Establish `hq1 : 1 ≤ p ^ (n : ℕ) - 1`.

Establish `h1 : 2 ≤ p` using `hp.two_le`. Establish `h3 : p ≤ p ^ (n : ℕ)` using `Nat.le_self_pow (PNat.ne_zero n) p`. Use linear arithmetic over natural numbers and integers. Establish `hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0`. Rewrite using `[mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]`.

Break down `mul_eq_zero.mp hprod with h | h` into its components or cases. Conclude with `sub_eq_zero.mp h`. It suffices to derive a contradiction. Establish `h4` using `congrArg PowerSeries.constantCoeff h`. Rewrite `h4` using `[map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero]`.

Conclude with `zero_ne_one (sub_eq_zero.mp h4)`. Use `⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩` and prove the remaining obligations. Establish `ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a)`. Rewrite using `[← map_pow, ← map_pow, ← hq, FiniteField.pow_card]`. Conclude with `key _ ha`.
-/
theorem UpperTheory.V.Pa.Det.constMap :
    ∀ {K K' : Type} [Field K] [Finite K] [Field K'] (j : PowerSeries K →+* PowerSeries K'), ∃ ι : K →+* K', ∀ a, j (PowerSeries.C a) = PowerSeries.C (ι a) := by
  intro K K' _ _ _ j
  classical
  haveI := Fintype.ofFinite K
  set p := ringChar K with hpdef
  haveI : CharP K p := ringChar.charP K
  obtain ⟨n, hp, hq⟩ := FiniteField.card K p
  haveI : Fact p.Prime := ⟨hp⟩
  set e : K →+* PowerSeries K' := j.comp PowerSeries.C
  haveI : CharP (PowerSeries K') p := charP_of_injective_ringHom e.injective p
  have key : ∀ f : PowerSeries K', f ^ (p ^ (n : ℕ)) = f → f = PowerSeries.C (PowerSeries.constantCoeff f) := by
    intro f hf
    set c := PowerSeries.constantCoeff f with hcdef
    have hc : c ^ (p ^ (n : ℕ)) = c := by
      have h2 := congrArg PowerSeries.constantCoeff hf
      rw [map_pow] at h2
      exact h2
    have hd : (f - PowerSeries.C c) ^ (p ^ (n : ℕ)) = f - PowerSeries.C c := by
      rw [sub_pow_char_pow, hf, ← map_pow, hc]
    have hd0 : PowerSeries.constantCoeff (f - PowerSeries.C c) = 0 := by
      rw [map_sub, PowerSeries.constantCoeff_C, hcdef, sub_self]
    have hq1 : 1 ≤ p ^ (n : ℕ) - 1 := by
      have h1 : 2 ≤ p := hp.two_le
      have h3 : p ≤ p ^ (n : ℕ) := Nat.le_self_pow (PNat.ne_zero n) p
      omega
    have hprod : (f - PowerSeries.C c) * ((f - PowerSeries.C c) ^ (p ^ (n : ℕ) - 1) - 1) = 0 := by
      rw [mul_sub, mul_one, ← pow_succ', Nat.sub_add_cancel (by omega), hd, sub_self]
    rcases mul_eq_zero.mp hprod with h | h
    · exact sub_eq_zero.mp h
    · exfalso
      have h4 := congrArg PowerSeries.constantCoeff h
      rw [map_sub, map_pow, hd0, zero_pow (by omega), map_one, map_zero] at h4
      exact zero_ne_one (sub_eq_zero.mp h4)
  refine ⟨PowerSeries.constantCoeff.comp e, fun a => ?_⟩
  have ha : j (PowerSeries.C a) ^ (p ^ (n : ℕ)) = j (PowerSeries.C a) := by
    rw [← map_pow, ← map_pow, ← hq, FiniteField.pow_card]
  exact key _ ha
