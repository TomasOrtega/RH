import Mathlib

namespace GlobalTheory

/- English proof (translation)
Introduce `p _ Ω _ _ hinj v hint hp R hfin hpid`. Establish `hle : ∀ x : R, v (x : Ω) ≤ 1` using `fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by`. Use `⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩` and prove the remaining obligations. Introduce `a b ha hb`.

Simplify using `only [Set.mem_setOf_eq, Subalgebra.coe_add] at *`. Conclude with `lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)`. Simplify using the standard rewrite rules. Introduce `c x hx`. Simplify using `only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpR : ((p : R) : Ω) = (p : Ω)` using `by simp`. Establish `hpP : (p : R) ∈ P` using `by rw [hP, hpR]; exact hp`. Establish `hp0 : (p : Ω) ≠ 0`. Introduce `h`.

Establish `h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0` using `by simp [h]`. Conclude with `(Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)`. Establish `hPprime : P.IsPrime`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `h`.

Establish `h1 : (1 : R) ∈ P` using `h ▸ Submodule.mem_top`. Rewrite `h1` using `[hP]`. Simplify using `at h1`. Introduce `x y hxy`. Rewrite using `[hP, hP]`.

Rewrite `hxy` using `[hP]`. Simplify using `only [Subalgebra.coe_mul, map_mul] at hxy`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Establish `hx1 : v x = 1` using `le_antisymm (hle x) hc.1`.

Establish `hy1 : v y = 1` using `le_antisymm (hle y) hc.2`. Rewrite `hxy` using `[hx1, hy1, one_mul]`. Conclude with `lt_irrefl _ hxy`. Establish `hPne : P ≠ ⊥`. Introduce `h`.

Rewrite `hpP` using `[h, Ideal.mem_bot]`. Apply `hp0` to reduce the goal to its premises. Rewrite using `[← hpR, hpP]`. Both sides reduce to the same expression. Use `haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne`.

Use `set g := Submodule.IsPrincipal.generator P with hgdef`. Establish `hgmem : g ∈ P` using `Submodule.IsPrincipal.generator_mem P`. Establish `hg0 : g ≠ 0`. Introduce `h`. Apply `hPne` to reduce the goal to its premises.

Conclude with `(Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h`. Establish `hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c` using `fun x hx => (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx`. Use `letI : Field (R ⧸ P) := Ideal.Quotient.field P`. Establish `hpk : ((p : ℕ) : R ⧸ P) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hpP`. Establish `hchar : CharP (R ⧸ P) p`. Rewrite using `[← ringChar.eq_iff]`. Break down `(Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h` into its components or cases. Conclude with `absurd h CharP.ringChar_ne_one`.

Conclude with `h`. Establish `hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p]`. Apply `le_antisymm` to reduce the goal to its premises. Apply `IsLocalRing.le_maximalIdeal` to reduce the goal to its premises. Introduce `h`.

Apply `hPprime.ne_top` to reduce the goal to its premises. Rewrite `h`, the goal using `[Ideal.eq_top_iff_one]`. Simplify `h` using `[Ideal.mem_comap]`. Rewrite using `[PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff] show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)`. Rewrite using `[Ideal.mem_comap, map_natCast]`.

Conclude with `hpP`. Use `haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by`. Rewrite using `[hunder]`. Conclude with `Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv`. Use `haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])`.

Use `letI := Fintype.ofFinite (R ⧸ P)`. Take `⟨n, -, hcard⟩` from `FiniteField.card (R ⧸ P) p`. Use `⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩` and prove the remaining obligations. Conclude with `fun h => hg0 (Subtype.ext h)`. Conclude with `(hP g).mp hgmem`.

Take `⟨c, hc⟩` from `hdvd _ hpP`. Establish `: (p : Ω) = (g : Ω) * (c : Ω)` using `by rw [← hpR, hc]; rfl`. Rewrite using `[this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]`. Conclude with `c.2`. Introduce `t ht`.

Establish `hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩`. Rewrite using `[map_pow, ← hcard, FiniteField.pow_card]`. Rewrite `hmk` using `[Ideal.Quotient.eq]`. Take `⟨c, hc⟩` from `hdvd _ hmk`. Establish `: t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω)`.

Use `congrArg (fun x : R => (x : Ω)) hc` as an intermediate fact. Simplify using `using this`. Rewrite using `[this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]`. Conclude with `c.2`.
-/
theorem exists_generator_valuation_prime_dvd_pow_sub_of_finite_padicInt :
  ∀ (p : ℕ) [Fact p.Prime] (Ω : Type) [Field Ω] [Algebra ℤ_[p] Ω], Function.Injective (algebraMap ℤ_[p] Ω) →
  ∀ v : Valuation Ω NNReal, (∀ x : Ω, IsIntegral ℤ_[p] x → v x ≤ 1) → v (p : Ω) < 1 →
  ∀ R : Subalgebra ℤ_[p] Ω, Module.Finite ℤ_[p] R → IsPrincipalIdealRing R →
  ∃ π ∈ R, π ≠ 0 ∧ v π < 1 ∧ (p : Ω) / π ∈ R ∧ ∃ f : ℕ, 0 < f ∧ ∀ t ∈ R, (t ^ p ^ f - t) / π ∈ R := by
  intro p _ Ω _ _ hinj v hint hp R hfin hpid
  have hle : ∀ x : R, v (x : Ω) ≤ 1 := fun x => hint _ ((IsIntegral.of_finite ℤ_[p] x).map R.val)
  obtain ⟨P, hP⟩ : ∃ P : Ideal R, ∀ x, x ∈ P ↔ v (x : Ω) < 1 := by
    refine ⟨{ carrier := {x | v (x : Ω) < 1}, add_mem' := ?_, zero_mem' := ?_, smul_mem' := ?_ }, fun x => Iff.rfl⟩
    · intro a b ha hb
      simp only [Set.mem_setOf_eq, Subalgebra.coe_add] at *
      exact lt_of_le_of_lt (v.map_add _ _) (max_lt ha hb)
    · simp
    · intro c x hx
      simp only [Set.mem_setOf_eq, smul_eq_mul, Subalgebra.coe_mul, map_mul] at *
      calc v (c:Ω) * v x ≤ 1 * v x := mul_le_mul' (hle c) le_rfl
        _ = v x := one_mul _
        _ < 1 := hx
  have hpR : ((p : R) : Ω) = (p : Ω) := by simp
  have hpP : (p : R) ∈ P := by rw [hP, hpR]; exact hp
  have hp0 : (p : Ω) ≠ 0 := by
    intro h
    have h1 : algebraMap ℤ_[p] Ω (p : ℤ_[p]) = algebraMap ℤ_[p] Ω 0 := by simp [h]
    exact (Nat.cast_ne_zero.mpr (Fact.out : p.Prime).ne_zero) (hinj h1)
  have hPprime : P.IsPrime := by
    refine ⟨?_, ?_⟩
    · intro h
      have h1 : (1 : R) ∈ P := h ▸ Submodule.mem_top
      rw [hP] at h1; simp at h1
    · intro x y hxy
      rw [hP, hP]; rw [hP] at hxy
      simp only [Subalgebra.coe_mul, map_mul] at hxy
      by_contra hc
      push_neg at hc
      have hx1 : v x = 1 := le_antisymm (hle x) hc.1
      have hy1 : v y = 1 := le_antisymm (hle y) hc.2
      rw [hx1, hy1, one_mul] at hxy
      exact lt_irrefl _ hxy
  have hPne : P ≠ ⊥ := by
    intro h
    rw [h, Ideal.mem_bot] at hpP
    apply hp0; rw [← hpR, hpP]; rfl
  haveI hPmax : P.IsMaximal := hPprime.isMaximal hPne
  set g := Submodule.IsPrincipal.generator P with hgdef
  have hgmem : g ∈ P := Submodule.IsPrincipal.generator_mem P
  have hg0 : g ≠ 0 := by
    intro h; apply hPne
    exact (Submodule.IsPrincipal.eq_bot_iff_generator_eq_zero P).mpr h
  have hdvd : ∀ x : R, x ∈ P → ∃ c : R, x = g * c := fun x hx =>
    (Submodule.IsPrincipal.mem_iff_generator_dvd P).mp hx

  letI : Field (R ⧸ P) := Ideal.Quotient.field P
  have hpk : ((p : ℕ) : R ⧸ P) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk P), Ideal.Quotient.eq_zero_iff_mem]; exact hpP
  have hchar : CharP (R ⧸ P) p := by
    rw [← ringChar.eq_iff]
    rcases (Nat.dvd_prime (Fact.out : p.Prime)).mp (ringChar.dvd hpk) with h | h
    · exact absurd h CharP.ringChar_ne_one
    · exact h
  have hunder : P.under ℤ_[p] = IsLocalRing.maximalIdeal ℤ_[p] := by
    apply le_antisymm
    · apply IsLocalRing.le_maximalIdeal
      intro h
      apply hPprime.ne_top
      rw [Ideal.eq_top_iff_one] at h ⊢
      simpa [Ideal.mem_comap] using h
    · rw [PadicInt.maximalIdeal_eq_span_p, Ideal.span_le, Set.singleton_subset_iff]
      show (p : ℤ_[p]) ∈ P.comap (algebraMap ℤ_[p] R)
      rw [Ideal.mem_comap, map_natCast]; exact hpP
  haveI : Finite (ℤ_[p] ⧸ P.under ℤ_[p]) := by
    rw [hunder]
    exact Finite.of_equiv (ZMod p) (PadicInt.residueField (p := p)).symm.toEquiv
  haveI : Finite (R ⧸ P) := Module.finite_of_finite (ℤ_[p] ⧸ P.under ℤ_[p])
  letI := Fintype.ofFinite (R ⧸ P)
  obtain ⟨n, -, hcard⟩ := FiniteField.card (R ⧸ P) p
  refine ⟨(g : Ω), g.2, ?_, ?_, ?_, (n : ℕ), n.pos, ?_⟩
  · exact fun h => hg0 (Subtype.ext h)
  · exact (hP g).mp hgmem
  · obtain ⟨c, hc⟩ := hdvd _ hpP
    have : (p : Ω) = (g : Ω) * (c : Ω) := by rw [← hpR, hc]; rfl
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2
  · intro t ht
    have hmk : Ideal.Quotient.mk P (⟨t, ht⟩ ^ p ^ (n : ℕ)) = Ideal.Quotient.mk P ⟨t, ht⟩ := by
      rw [map_pow, ← hcard, FiniteField.pow_card]
    rw [Ideal.Quotient.eq] at hmk
    obtain ⟨c, hc⟩ := hdvd _ hmk
    have : t ^ p ^ (n : ℕ) - t = (g : Ω) * (c : Ω) := by
      have := congrArg (fun x : R => (x : Ω)) hc
      simpa using this
    rw [this, mul_div_cancel_left₀ _ (fun h => hg0 (Subtype.ext h))]
    exact c.2

end GlobalTheory
