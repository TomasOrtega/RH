import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.Graded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MapRepApply

open IsLocalRing UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement

section

variable {O : Type} [CommRing O] {Γ : Type} [Group Γ] {R : Type} [CommRing R] [Algebra O R] (ρ : Γ →* M4 R)

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨[], by simp, by simp⟩`.
-/
private lemma zm_one : (1 : R) ∈ Submodule.span O (mono ρ 0) :=
  Submodule.subset_span ⟨[], by simp, by simp⟩

/- English proof (translation)
Use `open scoped Pointwise in`. Establish `hsub : mono ρ v * mono ρ w ⊆ mono ρ (v + w)`. Introduce and unpack `_ ⟨a, ⟨L, hL, rfl⟩, b, ⟨M, hM, rfl⟩, rfl⟩`. Conclude with `⟨L ++ M, by simp [hL, hM], by simp⟩`. Establish `h` using `Submodule.mul_mem_mul hx hy`.

Rewrite `h` using `[Submodule.span_mul_span]`. Conclude with `Submodule.span_mono hsub h`.
-/
private lemma zm_mul {v w : ℤ × ℤ} {x y : R} (hx : x ∈ Submodule.span O (mono ρ v))
    (hy : y ∈ Submodule.span O (mono ρ w)) : x * y ∈ Submodule.span O (mono ρ (v + w)) := by
  open scoped Pointwise in
  have hsub : mono ρ v * mono ρ w ⊆ mono ρ (v + w) := by
    rintro _ ⟨a, ⟨L, hL, rfl⟩, b, ⟨M, hM, rfl⟩, rfl⟩
    exact ⟨L ++ M, by simp [hL, hM], by simp⟩
  have h := Submodule.mul_mem_mul hx hy
  rw [Submodule.span_mul_span] at h
  exact Submodule.span_mono hsub h

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using zm_one (O := O) ρ`. Consider the case `succ k ih => rw [pow_succ, succ_nsmul]`. Conclude with `zm_mul ρ ih hx`.
-/
private lemma zm_pow {v : ℤ × ℤ} {x : R} (hx : x ∈ Submodule.span O (mono ρ v)) (k : ℕ) :
    x ^ k ∈ Submodule.span O (mono ρ (k • v)) := by
  induction k with
  | zero => simpa using zm_one (O := O) ρ
  | succ k ih => rw [pow_succ, succ_nsmul]; exact zm_mul ρ ih hx

end

/- English proof (translation)
Introduce `O _ Γ _ R _ _ ρ W c hc hz n hn`. Establish `hmem : ∀ i, W.z i ∈ Submodule.span O (mono ρ (W.wt i))`. Introduce `i`. Take `⟨g, a, b, hzi, hwi⟩` from `hz i`. Rewrite using `[hzi, hwi]`.

Distinguish the cases in `hab : a = b`. Substitute `hab` using the available equality. Establish `h0 : wt a a = 0` using `(wt_eq_zero a a).mpr rfl`. Rewrite using `[h0, Algebra.algebraMap_eq_smul_one]`. Use `Submodule.sub_mem _ (Submodule.subset_span ⟨[(g, a, a)], by simp [h0], by simp⟩) ?_` and prove the remaining obligations.

Conclude with `Submodule.smul_mem _ _ (zm_one ρ)`. Rewrite using `[hc g a b hab, map_zero, sub_zero]`. Conclude with `Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩`. Establish `hall : ∀ t : Finset W.σ, (∏ s ∈ t, W.z s ^ n s) ∈ Submodule.span O (mono ρ (∑ s ∈ t, n s • W.wt s))`. Introduce `t`.

Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using zm_one (O := O) ρ`. Consider the case `@insert a t ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `zm_mul ρ (zm_pow ρ (hmem a) _) ih`.

Establish `h` using `hall n.support`. Rewrite `hn` using `[Finsupp.weight_apply, Finsupp.sum]`. Rewrite `h` using `[hn]`. Conclude with `Algebra.span_le_adjoin O _ h`.
-/
theorem UpperTheory.V.Ws.Po.zMono :
    ∀ (O : Type) [CommRing O] (Γ : Type) [Group Γ] (R : Type) [CommRing R] [Algebra O R] (ρ : Γ →* M4 R) (W : WPres O (ℤ × ℤ) R)
      (c : Γ → Fin 4 → Fin 4 → O), (∀ g a b, a ≠ b → c g a b = 0) →
      (∀ i, ∃ g a b, W.z i = ρ g a b - algebraMap O R (c g a b) ∧ W.wt i = wt a b) →
      ∀ n : W.σ →₀ ℕ, Finsupp.weight W.wt n = 0 → (n.prod fun s k => W.z s ^ k) ∈ Algebra.adjoin O (mono ρ 0) := by
  intro O _ Γ _ R _ _ ρ W c hc hz n hn
  have hmem : ∀ i, W.z i ∈ Submodule.span O (mono ρ (W.wt i)) := by
    intro i
    obtain ⟨g, a, b, hzi, hwi⟩ := hz i
    rw [hzi, hwi]
    by_cases hab : a = b
    · subst hab
      have h0 : wt a a = 0 := (wt_eq_zero a a).mpr rfl
      rw [h0, Algebra.algebraMap_eq_smul_one]
      refine Submodule.sub_mem _ (Submodule.subset_span ⟨[(g, a, a)], by simp [h0], by simp⟩) ?_
      exact Submodule.smul_mem _ _ (zm_one ρ)
    · rw [hc g a b hab, map_zero, sub_zero]
      exact Submodule.subset_span ⟨[(g, a, b)], by simp, by simp⟩
  classical
  have hall : ∀ t : Finset W.σ,
      (∏ s ∈ t, W.z s ^ n s) ∈ Submodule.span O (mono ρ (∑ s ∈ t, n s • W.wt s)) := by
    intro t
    induction t using Finset.induction_on with
    | empty => simpa using zm_one (O := O) ρ
    | @insert a t ha ih =>
      rw [Finset.prod_insert ha, Finset.sum_insert ha]
      exact zm_mul ρ (zm_pow ρ (hmem a) _) ih
  have h := hall n.support
  rw [Finsupp.weight_apply, Finsupp.sum] at hn
  rw [hn] at h
  exact Algebra.span_le_adjoin O _ h
