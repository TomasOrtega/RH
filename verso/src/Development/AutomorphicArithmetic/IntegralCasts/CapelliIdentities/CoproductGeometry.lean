import Mathlib

/- English proof (translation)
Introduce `R κ _ _ _ _ m y h1 hm`. Establish `key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) → ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a`. Introduce `T`. Proceed by induction on `T using Finset.induction_on with`. Consider the case `empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩`.

Consider the case `insert b T hb ih`. Introduce `h`. Take `⟨a, ha1, ha0, ha⟩` from `ih (fun s hs => h s (Finset.mem_insert_of_mem hs))`. Use `⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)), le_max_of_le_left ha0, ?_⟩` and prove the remaining obligations. Introduce `s hs`.

Break down `Finset.mem_insert.mp hs with rfl | hs` into its components or cases. Conclude with `le_max_right _ _`. Conclude with `(ha s hs).trans (le_max_left _ _)`. Take `⟨S, hS⟩ : m.FG` from `IsNoetherian.noetherian m`. Take `⟨a, ha1, ha0, ha⟩` from `key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))`.

Establish `hgen : ∀ z ∈ m, ‖y z‖ ≤ a`. Introduce `z hz`. Rewrite `hz` using `[← hS]`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem x hx => exact ha x hx`.

Consider the case `zero => simpa using ha0`. Consider the case `add u v _ _ hu hv`. Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)`. Consider the case `smul r u _ hu`.

Rewrite using `[smul_eq_mul, map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use `⟨a, ha1, ha0, ?_⟩` and prove the remaining obligations. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro x _`. Simplify using `using h1 x`. Consider the case `succ n ih`. Introduce `x hx`. Rewrite `hx` using `[pow_succ]`.

Proceed by induction on `hx using Submodule.mul_induction_on' with`. Consider the case `mem_mul_mem u hu v hv`. Rewrite using `[map_mul, norm_mul, pow_succ]`. Conclude with `mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)`. Consider the case `add u _ v _ hu hv`.

Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)`.
-/
theorem UpperTheory.Reformulated.B.CoproductGeometry.cop_geom :
    ∀ {R κ : Type} [inst : CommRing R] [IsNoetherianRing R]
    [inst_2 : NormedField κ] [IsUltrametricDist κ] (m : Ideal R) (y : R →+* κ),
    (∀ (x : R), ‖(y : R → κ) x‖ ≤ (1 : ℝ)) →
      (∀ x ∈ m, ‖(y : R → κ) x‖ < (1 : ℝ)) →
        ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ (n : ℕ), ∀ x ∈ m ^ n, ‖(y : R → κ) x‖ ≤ a ^ n := by
  intro R κ _ _ _ _ m y h1 hm
  classical
  have key : ∀ T : Finset R, (∀ s ∈ T, ‖y s‖ < 1) →
      ∃ a < (1 : ℝ), (0 : ℝ) ≤ a ∧ ∀ s ∈ T, ‖y s‖ ≤ a := by
    intro T
    induction T using Finset.induction_on with
    | empty => intro _; exact ⟨0, by norm_num, le_rfl, by simp⟩
    | insert b T hb ih =>
      intro h
      obtain ⟨a, ha1, ha0, ha⟩ := ih (fun s hs => h s (Finset.mem_insert_of_mem hs))
      refine ⟨max a ‖y b‖, max_lt ha1 (h b (Finset.mem_insert_self _ _)),
        le_max_of_le_left ha0, ?_⟩
      intro s hs
      rcases Finset.mem_insert.mp hs with rfl | hs
      · exact le_max_right _ _
      · exact (ha s hs).trans (le_max_left _ _)
  obtain ⟨S, hS⟩ : m.FG := IsNoetherian.noetherian m
  obtain ⟨a, ha1, ha0, ha⟩ := key S (fun s hs => hm s (hS ▸ Ideal.subset_span hs))
  have hgen : ∀ z ∈ m, ‖y z‖ ≤ a := by
    intro z hz
    rw [← hS] at hz
    induction hz using Submodule.span_induction with
    | mem x hx => exact ha x hx
    | zero => simpa using ha0
    | add u v _ _ hu hv =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
    | smul r u _ hu =>
      rw [smul_eq_mul, map_mul, norm_mul]
      calc ‖y r‖ * ‖y u‖ ≤ 1 * a := mul_le_mul (h1 r) hu (norm_nonneg _) zero_le_one
        _ = a := one_mul a
  refine ⟨a, ha1, ha0, ?_⟩
  intro n
  induction n with
  | zero => intro x _; simpa using h1 x
  | succ n ih =>
    intro x hx
    rw [pow_succ] at hx
    induction hx using Submodule.mul_induction_on' with
    | mem_mul_mem u hu v hv =>
      rw [map_mul, norm_mul, pow_succ]
      exact mul_le_mul (ih u hu) (hgen v hv) (norm_nonneg _) (pow_nonneg ha0 n)
    | add u _ v _ hu hv =>
      rw [map_add]
      exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hu hv)
