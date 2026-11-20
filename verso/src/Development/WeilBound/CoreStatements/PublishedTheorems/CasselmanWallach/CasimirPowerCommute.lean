import Development.WeilBound.CoreStatements.PublishedTheorems.CasselmanWallach.FunctionalCalculusLaws

noncomputable section

open Matrix Finset ReciprocityTheory.ChartRestriction.DS

namespace PositivityTheory.CW

namespace AdjointWordFiltration

variable {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]

/- English proof (translation)
Unfold `U`. Apply `Submodule.span_mono` to reduce the goal to its premises. Introduce and unpack `x ⟨l, hl, rfl⟩`. Conclude with `⟨l, hl.trans h, rfl⟩`.
-/
theorem U_mono (E : Fin n → Fin n → Module.End ℂ V) {j k : ℕ} (h : j ≤ k) : U E j ≤ U E k := by
  unfold U
  apply Submodule.span_mono
  rintro x ⟨l, hl, rfl⟩
  exact ⟨l, hl.trans h, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨l, le_rfl, rfl⟩`.
-/
theorem word_mem (E : Fin n → Fin n → Module.End ℂ V) (l : List (Fin n × Fin n)) :
    (l.map fun p => E p.1 p.2).prod ∈ U E l.length :=
  Submodule.subset_span ⟨l, le_rfl, rfl⟩

/- English proof (translation)
Unfold `U at hw`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Apply `Submodule.subset_span` to reduce the goal to its premises.

Use `⟨l ++ [(a, b)], by simp; omega, ?_⟩` and prove the remaining obligations. Simplify using `[List.prod_append]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [add_mul]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ c hx`.
-/
theorem mul_E_mem (E : Fin n → Fin n → Module.End ℂ V) (a b : Fin n) {j : ℕ} {w : Module.End ℂ V}
    (hw : w ∈ U E j) : w * E a b ∈ U E (j + 1) := by
  unfold U at hw
  induction hw using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    apply Submodule.subset_span
    refine ⟨l ++ [(a, b)], by simp; omega, ?_⟩
    simp [List.prod_append]
  | zero => simp
  | add x y _ _ hx hy => rw [add_mul]; exact Submodule.add_mem _ hx hy
  | smul c x _ hx => rw [smul_mul_assoc]; exact Submodule.smul_mem _ c hx

/- English proof (translation)
Apply the tactic sequence `unfold adjSign; split_ifs <;> norm_num`.
-/
theorem adjSign_mul_self (ε : Fin n → Bool) (a b : Fin n) : adjSign ε a b * adjSign ε a b = 1 := by
  unfold adjSign; split_ifs <;> norm_num

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil`. Use `⟨1, by simpa using word_mem E [], fun x y => ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Consider the case `cons p t ih`.

Take `⟨w', hw', hw⟩` from `ih`. Use `⟨(starRingEnd ℂ (adjSign ε p.2 p.1)) • (w' * E p.2 p.1), ?_, fun x y => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.smul_mem _ _ (by simpa using mul_E_mem E p.2 p.1 hw')`. Establish `h1` using `hu p.2 p.1 x ((t.map fun p => E p.1 p.2).prod y)`. Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply, inner_smul_left, Complex.conj_conj, Module.End.mul_apply, ← hw, h1, ← mul_assoc, adjSign_mul_self, one_mul]`.
-/
theorem word_adj (ε : Fin n → Bool) (E : Fin n → Fin n → Module.End ℂ V) (hu : IsInfUnitary ε E)
    (l : List (Fin n × Fin n)) :
    ∃ u' ∈ U E l.length, ∀ x y, inner ℂ x ((l.map fun p => E p.1 p.2).prod y) = inner ℂ (u' x) y := by
  induction l with
  | nil =>
    refine ⟨1, by simpa using word_mem E [], fun x y => ?_⟩
    simp
  | cons p t ih =>
    obtain ⟨w', hw', hw⟩ := ih
    refine ⟨(starRingEnd ℂ (adjSign ε p.2 p.1)) • (w' * E p.2 p.1), ?_, fun x y => ?_⟩
    · exact Submodule.smul_mem _ _ (by simpa using mul_E_mem E p.2 p.1 hw')
    · have h1 := hu p.2 p.1 x ((t.map fun p => E p.1 p.2).prod y)
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.smul_apply, inner_smul_left,
        Complex.conj_conj, Module.End.mul_apply, ← hw, h1, ← mul_assoc, adjSign_mul_self, one_mul]

end AdjointWordFiltration

/- English proof (translation)
Introduce `n ε V _ _ E hM k u hu`. Unfold `U at hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`.

Take `⟨u', hu', h⟩` from `AdjointWordFiltration.word_adj ε E hM.uni l`. Conclude with `⟨u', AdjointWordFiltration.U_mono E hl hu', h⟩`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, fun x y => by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x', hx', hx⟩` from `hx`.

Take `⟨y', hy', hy⟩` from `hy`. Conclude with `⟨x' + y', Submodule.add_mem _ hx' hy', fun a b => by`. Simplify using `only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]⟩`. Consider the case `smul c x _ hx`. Take `⟨x', hx', hx⟩` from `hx`.

Use `⟨starRingEnd ℂ c • x', Submodule.smul_mem _ _ hx', fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_conj, hx]`.
-/
theorem adjoint_stable_filtration : FiltrationAdjointStable := by
  intro n ε V _ _ E hM k u hu
  unfold U at hu
  induction hu using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨l, hl, rfl⟩ := hx
    obtain ⟨u', hu', h⟩ := AdjointWordFiltration.word_adj ε E hM.uni l
    exact ⟨u', AdjointWordFiltration.U_mono E hl hu', h⟩
  | zero => exact ⟨0, Submodule.zero_mem _, fun x y => by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨x', hx', hx⟩ := hx
    obtain ⟨y', hy', hy⟩ := hy
    exact ⟨x' + y', Submodule.add_mem _ hx' hy', fun a b => by
      simp only [LinearMap.add_apply, inner_add_left, inner_add_right, hx, hy]⟩
  | smul c x _ hx =>
    obtain ⟨x', hx', hx⟩ := hx
    refine ⟨starRingEnd ℂ c • x', Submodule.smul_mem _ _ hx', fun a b => ?_⟩
    rw [LinearMap.smul_apply, LinearMap.smul_apply, inner_smul_left, inner_smul_right, Complex.conj_conj, hx]

end PositivityTheory.CW

end
