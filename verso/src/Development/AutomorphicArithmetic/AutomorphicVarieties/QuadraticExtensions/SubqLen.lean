import Development.AutomorphicArithmetic.AutomorphicVarieties.QuadraticExtensions.ModulusAdjoinISqrtNegPrimes

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum UpperTheory.V.Two
open scoped Pointwise

/- English proof (translation)
Introduce `l _ N Q P _ _ _ _ π j hπ hj htor`. Establish `key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a`. Introduce `a b`. Take `⟨x, rfl⟩` from `Submodule.Quotient.mk_surjective (ZlSub l) a`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective (ZlSub l) b`.

Establish `step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y`. Introduce `x y h`. Distinguish the cases in `hy : y = 0`. Substitute `hy` using the available equality. Use `⟨0, ?_⟩` and prove the remaining obligations.

Rewrite `h` using `[norm_zero]`. Rewrite using `[norm_le_zero_iff.mp h, zero_smul]`. Use `⟨⟨x / y, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[norm_div]`. Conclude with `div_le_one_of_le₀ h (norm_nonneg _)`.

Use `show x = (x / y) * y`. Rewrite using `[div_mul_cancel₀ _ hy]`. Break down `le_total ‖x‖ ‖y‖ with h | h` into its components or cases. Take `⟨c, hc⟩` from `step x y h`. Conclude with `⟨c, Or.inl (by rw [hc]; rfl)⟩`.

Take `⟨c, hc⟩` from `step y x h`. Conclude with `⟨c, Or.inr (by rw [hc]; rfl)⟩`. Establish `hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1`. Introduce `q1 q2`. Take `⟨n1, rfl⟩` from `hπ q1`.

Take `⟨n2, rfl⟩` from `hπ q2`. Take `⟨c, h | h⟩` from `key (n1 : QZ l) (n2 : QZ l)`. Use `⟨c, Or.inl ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`. Use `congr 1`.

Conclude with `Subtype.ext h`. Use `⟨c, Or.inr ?_⟩` and prove the remaining obligations. Rewrite using `[← map_smul]`. Use `congr 1`. Conclude with `Subtype.ext h`.

Establish `hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x}`. Introduce `x y hx`. Take `⟨c, h | h⟩` from `hQ (j y) (j x)`. Rewrite `h` using `[← map_smul]`. Rewrite using `[hj h]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)`. Rewrite `h` using `[← map_smul]`. Establish `hxy` using `hj h`. Distinguish the cases in `hc : IsUnit c`. Take `⟨u, rfl⟩` from `hc`.

Establish `hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x`. Rewrite using `[hxy, smul_smul, Units.inv_mul, one_smul]`. Rewrite using `[hy]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)`. It suffices to derive a contradiction.

Establish `hn : ‖c‖ < 1` using `PadicInt.mem_nonunits.mp hc`. Take `⟨d, rfl⟩` from `(PadicInt.norm_lt_one_iff_dvd c).mp hn`. Apply `hx` to reduce the goal to its premises. Rewrite using `[hxy, mul_comm, mul_smul, htor, smul_zero]`. Break down `subsingleton_or_nontrivial P with hsub | hnt` into its components or cases.

Rewrite using `[Module.length_eq_zero]`. Conclude with `zero_le`. Use `haveI : IsSimpleModule ℤ_[l] P := by`. Rewrite using `[isSimpleModule_iff]`. Use `IsSimpleOrder.mk (fun S => ?_)` and prove the remaining obligations.

Distinguish the cases in `hS : S = ⊥`. Conclude with `Or.inl hS`. Use `right`. Take `⟨x, hxS, hx0⟩` from `(Submodule.ne_bot_iff S).mp hS`. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Conclude with `(Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)`. Rewrite using `[Module.length_eq_one]`.
-/
theorem UpperTheory.V.Two.subqLen :
    ∀ (l : ℕ) [Fact l.Prime] (N : Submodule ℤ_[l] (QZ l)) (Q P : Type) [AddCommGroup Q] [Module ℤ_[l] Q] [AddCommGroup P] [Module ℤ_[l] P] (π : N →ₗ[ℤ_[l]] Q) (j : P →ₗ[ℤ_[l]] Q),
      Function.Surjective π → Function.Injective j → (∀ x : P, (l : ℤ_[l]) • x = 0) → Module.length ℤ_[l] P ≤ 1 := by
  intro l _ N Q P _ _ _ _ π j hπ hj htor
  have key : ∀ a b : QZ l, ∃ c : ℤ_[l], a = c • b ∨ b = c • a := by
    intro a b
    obtain ⟨x, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) a
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective (ZlSub l) b
    have step : ∀ x y : ℚ_[l], ‖x‖ ≤ ‖y‖ → ∃ c : ℤ_[l], x = c • y := by
      intro x y h
      by_cases hy : y = 0
      · subst hy
        refine ⟨0, ?_⟩
        rw [norm_zero] at h
        rw [norm_le_zero_iff.mp h, zero_smul]
      · refine ⟨⟨x / y, ?_⟩, ?_⟩
        · rw [norm_div]
          exact div_le_one_of_le₀ h (norm_nonneg _)
        · show x = (x / y) * y
          rw [div_mul_cancel₀ _ hy]
    rcases le_total ‖x‖ ‖y‖ with h | h
    · obtain ⟨c, hc⟩ := step x y h
      exact ⟨c, Or.inl (by rw [hc]; rfl)⟩
    · obtain ⟨c, hc⟩ := step y x h
      exact ⟨c, Or.inr (by rw [hc]; rfl)⟩
  have hQ : ∀ q1 q2 : Q, ∃ c : ℤ_[l], q1 = c • q2 ∨ q2 = c • q1 := by
    intro q1 q2
    obtain ⟨n1, rfl⟩ := hπ q1
    obtain ⟨n2, rfl⟩ := hπ q2
    obtain ⟨c, h | h⟩ := key (n1 : QZ l) (n2 : QZ l)
    · refine ⟨c, Or.inl ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
    · refine ⟨c, Or.inr ?_⟩
      rw [← map_smul]
      congr 1
      exact Subtype.ext h
  have hP : ∀ x y : P, x ≠ 0 → y ∈ Submodule.span ℤ_[l] {x} := by
    intro x y hx
    obtain ⟨c, h | h⟩ := hQ (j y) (j x)
    · rw [← map_smul] at h
      rw [hj h]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
    · rw [← map_smul] at h
      have hxy := hj h
      by_cases hc : IsUnit c
      · obtain ⟨u, rfl⟩ := hc
        have hy : y = ((u⁻¹ : ℤ_[l]ˣ) : ℤ_[l]) • x := by
          rw [hxy, smul_smul, Units.inv_mul, one_smul]
        rw [hy]
        exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
      · exfalso
        have hn : ‖c‖ < 1 := PadicInt.mem_nonunits.mp hc
        obtain ⟨d, rfl⟩ := (PadicInt.norm_lt_one_iff_dvd c).mp hn
        apply hx
        rw [hxy, mul_comm, mul_smul, htor, smul_zero]
  rcases subsingleton_or_nontrivial P with hsub | hnt
  · rw [Module.length_eq_zero]
    exact zero_le
  · haveI : IsSimpleModule ℤ_[l] P := by
      rw [isSimpleModule_iff]
      refine IsSimpleOrder.mk (fun S => ?_)
      by_cases hS : S = ⊥
      · exact Or.inl hS
      · right
        obtain ⟨x, hxS, hx0⟩ := (Submodule.ne_bot_iff S).mp hS
        rw [eq_top_iff]
        intro y _
        exact (Submodule.span_le.mpr (Set.singleton_subset_iff.mpr hxS)) (hP x y hx0)
    rw [Module.length_eq_one]
