import Development.AutomorphicArithmetic.AutomorphicVarieties.HermiteNormalForms.SmulNeZeroLat

open NumberField Matrix UpperTheory.V UpperTheory.V.KT
open scoped ComplexOrder

/- English proof (translation)
Introduce `L _ _ N`. Establish `hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j)`. Introduce `w i j`. Conclude with `(continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))`. Establish `htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace`.

Introduce `k hk w`. Conclude with `Finset.sum_nonneg fun i _ => (hk w).diag_nonneg`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ, {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj}`. Use extensionality with `h`.

Simplify using `only [Psd, Set.mem_setOf_eq, Set.mem_iInter]`. Prove the components needed by the constructor for the conclusion. Introduce `hh w x`. Conclude with `(hh w).2 x`. Introduce `hh w`.

Conclude with `⟨mat_herm h w, hh w⟩`. Rewrite using `[hP]`. Use `isClosed_iInter fun w => isClosed_iInter fun x => ?_` and prove the remaining obligations. Use `isClosed_le continuous_const ?_` and prove the remaining obligations. Unfold `Finsupp.sum`.

Use `continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_` and prove the remaining obligations. Conclude with `(continuous_const.mul (hc w i j)).mul continuous_const`. Introduce `c hc k hk w show (mat (c • k) w).PosSemidef`. Rewrite using `[mat_smul]`. Conclude with `(hk w).smul hc.le`.

Introduce `k hk w`. Conclude with `(hk w).posSemidef`. Set `f : HS L N →ₗ[ℝ] ℝ` to `{ toFun := fun h => ∑ w, ((mat h w).trace).re map_add' := by`. Introduce `h k`. Simplify using `only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]`.

Both sides reduce to the same expression. Use the proof step `map_smul' := by`. Introduce `c h`. Simplify using `only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations.

Simplify using `}`. Establish `hf : Continuous f` using `by show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)`. Use `continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_` and prove the remaining obligations. Conclude with `continuous_finset_sum _ fun i _ => hc w i i`. Use `⟨⟨f, hf⟩, ?_⟩` and prove the remaining obligations.

Introduce `k hk hk0`. Establish `hw : ∃ w, mat k w ≠ 0`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Conclude with `hk0 (HS_ext fun w => by rw [hne w, mat_zero])`.

Take `⟨w, hw⟩` from `hw`. Use `show 0 < ∑ w, ((mat k w).trace).re`. Establish `hpos : 0 < ((mat k w).trace).re`. Establish `h1 : 0 ≤ (mat k w).trace` using `htr k hk w`. Establish `h2 : (mat k w).trace ≠ 0` using `fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)`.

Conclude with `(Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1`. Use `lt_of_lt_of_le hpos ?_` and prove the remaining obligations. Use `Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)` and prove the remaining obligations. Conclude with `(Complex.le_def.mp (htr k hk v)).1`.
-/
theorem UpperTheory.V.KT.psdcone :
    ∀ (L : Type) [Field L] [NumberField L] (N : ℕ), IsClosed (Psd L N) ∧ (∀ c : ℝ, 0 < c → ∀ k ∈ Psd L N, c • k ∈ Psd L N) ∧
    Pos L N ⊆ Psd L N ∧ (ConeExtensionAcyclic.posDual (Psd L N)).Nonempty := by
  intro L _ _ N
  have hc : ∀ (w : InfinitePlace L) (i j : Fin N), Continuous (fun h : HS L N => mat h w i j) := by
    intro w i j
    exact (continuous_apply j).comp ((continuous_apply i).comp ((continuous_apply w).comp continuous_subtype_val))
  have htr : ∀ k ∈ Psd L N, ∀ w, 0 ≤ (mat k w).trace := by
    intro k hk w
    exact Finset.sum_nonneg fun i _ => (hk w).diag_nonneg
  refine ⟨?_, ?_, ?_, ?_⟩
  · have hP : Psd L N = ⋂ w : InfinitePlace L, ⋂ x : Fin N →₀ ℂ,
        {h : HS L N | 0 ≤ x.sum fun i xi => x.sum fun j xj => star xi * mat h w i j * xj} := by
      ext h
      simp only [Psd, Set.mem_setOf_eq, Set.mem_iInter]
      constructor
      · intro hh w x
        exact (hh w).2 x
      · intro hh w
        exact ⟨mat_herm h w, hh w⟩
    rw [hP]
    refine isClosed_iInter fun w => isClosed_iInter fun x => ?_
    refine isClosed_le continuous_const ?_
    unfold Finsupp.sum
    refine continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j _ => ?_
    exact (continuous_const.mul (hc w i j)).mul continuous_const
  · intro c hc k hk w
    show (mat (c • k) w).PosSemidef
    rw [mat_smul]
    exact (hk w).smul hc.le
  · intro k hk w
    exact (hk w).posSemidef
  · let f : HS L N →ₗ[ℝ] ℝ :=
      { toFun := fun h => ∑ w, ((mat h w).trace).re
        map_add' := by
          intro h k
          simp only [← Finset.sum_add_distrib, ← Complex.add_re, ← Matrix.trace_add]
          rfl
        map_smul' := by
          intro c h
          simp only [mat_smul, Matrix.trace_smul, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
          refine Finset.sum_congr rfl fun w _ => ?_
          simp }
    have hf : Continuous f := by
      show Continuous (fun h : HS L N => ∑ w, ((mat h w).trace).re)
      refine continuous_finset_sum _ fun w _ => Complex.continuous_re.comp ?_
      exact continuous_finset_sum _ fun i _ => hc w i i
    refine ⟨⟨f, hf⟩, ?_⟩
    intro k hk hk0
    have hw : ∃ w, mat k w ≠ 0 := by
      by_contra hne
      push_neg at hne
      exact hk0 (HS_ext fun w => by rw [hne w, mat_zero])
    obtain ⟨w, hw⟩ := hw
    show 0 < ∑ w, ((mat k w).trace).re
    have hpos : 0 < ((mat k w).trace).re := by
      have h1 : 0 ≤ (mat k w).trace := htr k hk w
      have h2 : (mat k w).trace ≠ 0 := fun h0 => hw (((hk w).trace_eq_zero_iff).mp h0)
      exact (Complex.lt_def.mp (lt_of_le_of_ne h1 (Ne.symm h2))).1
    refine lt_of_lt_of_le hpos ?_
    refine Finset.single_le_sum (f := fun w => ((mat k w).trace).re) (fun v _ => ?_) (Finset.mem_univ w)
    exact (Complex.le_def.mp (htr k hk v)).1
