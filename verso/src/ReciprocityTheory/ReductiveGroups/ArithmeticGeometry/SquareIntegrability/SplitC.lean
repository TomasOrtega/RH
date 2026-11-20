import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SquareIntegrability.ExistsMaximal

namespace ReciprocityTheory.ChartRestriction.G.I2

open NumberField Complex
open scoped InnerProductSpace

noncomputable section

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Unfold `PT.la1`. Apply `csInf_le` to reduce the goal to its premises. Conclude with `⟨0, fun t ht => by obtain ⟨y, -, -, rfl⟩ := ht; exact norm_nonneg y⟩`. Conclude with `⟨x, hx, hne, rfl⟩`.
-/
theorem sq_le_Qy_of_le_firstMinimum (X : PT E) {x : Vsp X.dim} (hx : x ∈ X.L) (hne : x ≠ 0) : X.la1 ≤ ‖x‖ := by
  unfold PT.la1
  apply csInf_le
  · exact ⟨0, fun t ht => by obtain ⟨y, -, -, rfl⟩ := ht; exact norm_nonneg y⟩
  · exact ⟨x, hx, hne, rfl⟩

/- English proof (translation)
Unfold `PT.la1 at h`. Take `⟨x, hx, hne'⟩` from `hne`. Take `⟨s, ⟨y, hy, hy0, rfl⟩, hs⟩` from `exists_lt_of_csInf_lt (s := {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}) ⟨‖x‖, x, hx, hne', rfl⟩ h`. Conclude with `⟨y, hy, hy0, hs⟩`.
-/
theorem exists_short (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) {t : ℝ} (h : X.la1 < t) :
    ∃ x ∈ X.L, x ≠ 0 ∧ ‖x‖ < t := by
  unfold PT.la1 at h
  obtain ⟨x, hx, hne'⟩ := hne
  obtain ⟨s, ⟨y, hy, hy0, rfl⟩, hs⟩ := exists_lt_of_csInf_lt (s := {t : ℝ | ∃ x ∈ X.L, x ≠ 0 ∧ t = ‖x‖}) ⟨‖x‖, x, hx, hne', rfl⟩ h
  exact ⟨y, hy, hy0, hs⟩

/- English proof (translation)
Take `⟨x0, hx0, hx0ne⟩` from `hne`. Establish `hfin : Set.Finite {y : Vsp X.dim | y ∈ X.L ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖}`. Apply `(ZSpan.setFinite_inter X.b (Metric.isBounded_closedBall (x := (0 : Vsp X.dim)) (r := ‖x0‖))).subset` to reduce the goal to its premises. Introduce and unpack `y ⟨hy, -, hyn⟩`. Conclude with `⟨mem_closedBall_zero_iff.2 hyn, hy⟩`.

Take `⟨m, hm, hmin⟩` from `Finset.exists_min_image hfin.toFinset (fun y => ‖y‖) ⟨x0, (Set.Finite.mem_toFinset hfin).2 ⟨hx0, hx0ne, le_rfl⟩⟩`. Rewrite `hm` using `[Set.Finite.mem_toFinset]`. Take `⟨-, hm0, hmle⟩` from `hm`. Establish `hpos : 0 < ‖m‖` using `norm_pos_iff.2 hm0`. Use `lt_of_lt_of_le hpos ?_` and prove the remaining obligations.

Unfold `PT.la1`. Use `le_csInf ⟨‖x0‖, x0, hx0, hx0ne, rfl⟩ ?_` and prove the remaining obligations. Introduce and unpack `t ⟨y, hy, hy0, rfl⟩`. Distinguish the cases in `hyle : ‖y‖ ≤ ‖x0‖`. Conclude with `hmin y ((Set.Finite.mem_toFinset hfin).2 ⟨hy, hy0, hyle⟩)`.

Conclude with `le_trans hmle (le_of_lt (not_le.1 hyle))`.
-/
theorem first_minimum_pos (X : PT E) (hne : ∃ x ∈ X.L, x ≠ 0) : 0 < X.la1 := by
  obtain ⟨x0, hx0, hx0ne⟩ := hne
  have hfin : Set.Finite {y : Vsp X.dim | y ∈ X.L ∧ y ≠ 0 ∧ ‖y‖ ≤ ‖x0‖} := by
    apply (ZSpan.setFinite_inter X.b (Metric.isBounded_closedBall (x := (0 : Vsp X.dim))
      (r := ‖x0‖))).subset
    rintro y ⟨hy, -, hyn⟩
    exact ⟨mem_closedBall_zero_iff.2 hyn, hy⟩
  obtain ⟨m, hm, hmin⟩ := Finset.exists_min_image hfin.toFinset (fun y => ‖y‖)
    ⟨x0, (Set.Finite.mem_toFinset hfin).2 ⟨hx0, hx0ne, le_rfl⟩⟩
  rw [Set.Finite.mem_toFinset] at hm
  obtain ⟨-, hm0, hmle⟩ := hm
  have hpos : 0 < ‖m‖ := norm_pos_iff.2 hm0
  refine lt_of_lt_of_le hpos ?_
  unfold PT.la1
  refine le_csInf ⟨‖x0‖, x0, hx0, hx0ne, rfl⟩ ?_
  rintro t ⟨y, hy, hy0, rfl⟩
  by_cases hyle : ‖y‖ ≤ ‖x0‖
  · exact hmin y ((Set.Finite.mem_toFinset hfin).2 ⟨hy, hy0, hyle⟩)
  · exact le_trans hmle (le_of_lt (not_le.1 hyle))

/- English proof (translation)
Establish `hpos : 0 < Fintype.card (Idx X.dim)`. Establish `h` using `X.dim_conj τ`. Rewrite using `[Fintype.card_pos_iff]`. Distinguish the cases in `h0 : 0 < X.dim τ`. Conclude with `⟨⟨τ, ⟨0, h0⟩⟩⟩`.

Conclude with `⟨⟨NumberField.ComplexEmbedding.conjugate τ, ⟨0, by omega⟩⟩⟩`. Conclude with `⟨X.b ⟨0, by omega⟩, Submodule.subset_span (Set.mem_range_self _), X.b.ne_zero _⟩`.
-/
theorem L_ne_zero (X : PT E) (hr : 1 ≤ X.r) (τ : E →+* ℂ) : ∃ x ∈ X.L, x ≠ 0 := by
  have hpos : 0 < Fintype.card (Idx X.dim) := by
    have h := X.dim_conj τ
    rw [Fintype.card_pos_iff]
    by_cases h0 : 0 < X.dim τ
    · exact ⟨⟨τ, ⟨0, h0⟩⟩⟩
    · exact ⟨⟨NumberField.ComplexEmbedding.conjugate τ, ⟨0, by omega⟩⟩⟩
  exact ⟨X.b ⟨0, by omega⟩, Submodule.subset_span (Set.mem_range_self _), X.b.ne_zero _⟩

/- English proof (translation)
Introduce `x hx k hk hkx`. Apply `hs x hx` to reduce the goal to its premises. Establish `h1 : (k • x : Vsp X.dim) ∈ IR I` using `Submodule.subset_span hkx`. Establish `hk' : (k : ℝ) ≠ 0` using `Int.cast_ne_zero.mpr hk`. Establish `h2 : x = (k : ℝ)⁻¹ • (k • x)`.

Rewrite using `[← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ hk']`. Rewrite using `[h2]`. Conclude with `Submodule.smul_mem _ _ h1`.
-/
theorem sat_of_IR {X : PT E} {I : Submodule ℤ (Vsp X.dim)} (hs : ∀ x ∈ X.L, x ∈ IR I → x ∈ I) :
    ∀ x ∈ X.L, ∀ k : ℤ, k ≠ 0 → k • x ∈ I → x ∈ I := by
  intro x hx k hk hkx
  apply hs x hx
  have h1 : (k • x : Vsp X.dim) ∈ IR I := Submodule.subset_span hkx
  have hk' : (k : ℝ) ≠ 0 := Int.cast_ne_zero.mpr hk
  have h2 : x = (k : ℝ)⁻¹ • (k • x) := by
    rw [← Int.cast_smul_eq_zsmul ℝ, inv_smul_smul₀ hk']
  rw [h2]
  exact Submodule.smul_mem _ _ h1

end

end ReciprocityTheory.ChartRestriction.G.I2
