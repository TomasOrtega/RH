import Formalism.SharpRestriction.LevelLetterCocycles.TeichOnto

noncomputable section

namespace Formalism.MainNotions.N.Ln03.Pf

open IsLocalRing

namespace ComplMaxPf

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤` using `fun k => Submodule.smul_mono_left (h1 k)`. Establish `m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤` using `fun k => Submodule.smul_mono_left (h2 k)`. Use `{ haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)), prec' := fun f hf => ?_ }` and prove the remaining obligations. Take `⟨L, hL⟩` from `hI.prec' (fun k => f (e * k)) fun {m n} hmn => SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))`. Use `⟨L, fun n => ?_⟩` and prove the remaining obligations.

Establish `hn : n ≤ e * n` using `Nat.le_mul_of_pos_left n he`. Conclude with `(hf hn).trans (SModEq.mono (m2 n) (hL n))`.
-/
theorem isAdicComplete_of_pow {I J : Ideal R} (e : ℕ) (he : 1 ≤ e) (h1 : ∀ k, J ^ (e * k) ≤ I ^ k)
    (h2 : ∀ k, I ^ k ≤ J ^ k) (hI : IsAdicComplete I R) : IsAdicComplete J R := by
  have m1 : ∀ k, (J ^ (e * k) • ⊤ : Submodule R R) ≤ I ^ k • ⊤ := fun k => Submodule.smul_mono_left (h1 k)
  have m2 : ∀ k, (I ^ k • ⊤ : Submodule R R) ≤ J ^ k • ⊤ := fun k => Submodule.smul_mono_left (h2 k)
  refine { haus' := fun x hx => hI.haus' x fun k => SModEq.mono (m1 k) (hx (e * k)),
           prec' := fun f hf => ?_ }
  obtain ⟨L, hL⟩ := hI.prec' (fun k => f (e * k)) fun {m n} hmn =>
    SModEq.mono (m1 m) (hf (Nat.mul_le_mul_left e hmn))
  refine ⟨L, fun n => ?_⟩
  have hn : n ≤ e * n := Nat.le_mul_of_pos_left n he
  exact (hf hn).trans (SModEq.mono (m2 n) (hL n))

end ComplMaxPf

/- English proof (translation)
Introduce `O _ _ _ p hpm hp0 hc`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible O`. Take `⟨e, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ`. Establish `he : 1 ≤ e`. Break down `Nat.eq_zero_or_pos e with rfl | h` into its components or cases.

It suffices to derive a contradiction. Rewrite `hu` using `[pow_zero, mul_one]`. Rewrite `hpm` using `[hu]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit`. Conclude with `h`.

Establish `hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k)` using `fun k => by`. Rewrite using `[hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul, Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]`. Use `ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc` and prove the remaining obligations. Rewrite using `[hIk k]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)`.
-/
theorem complMax_holds : ComplMax := by
  intro O _ _ _ p hpm hp0 hc
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible O
  obtain ⟨e, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hp0 hϖ
  have he : 1 ≤ e := by
    rcases Nat.eq_zero_or_pos e with rfl | h
    · exfalso
      rw [pow_zero, mul_one] at hu
      rw [hu] at hpm
      exact (IsLocalRing.mem_maximalIdeal _).1 hpm u.isUnit
    · exact h
  have hIk : ∀ k, Ideal.span {(p : O)} ^ k = maximalIdeal O ^ (e * k) := fun k => by
    rw [hϖ.maximalIdeal_eq, Ideal.span_singleton_pow, Ideal.span_singleton_pow, hu, mul_pow, ← pow_mul,
      Ideal.span_singleton_mul_left_unit (u.isUnit.pow k)]
  refine ComplMaxPf.isAdicComplete_of_pow e he (fun k => (hIk k).ge) (fun k => ?_) hc
  rw [hIk k]
  exact Ideal.pow_le_pow_right (Nat.le_mul_of_pos_left k he)

end Formalism.MainNotions.N.Ln03.Pf
