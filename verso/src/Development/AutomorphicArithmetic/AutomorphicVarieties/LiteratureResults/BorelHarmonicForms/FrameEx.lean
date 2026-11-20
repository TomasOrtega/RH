import Development.AutomorphicArithmetic.AutomorphicVarieties.LiteratureResults.BorelHarmonicForms.DerivativeRightTranslateL2
open NumberField Matrix GlobalTheory.CuspRep GlobalTheory.GKCoh UpperTheory.V.Af UpperTheory.V.AlgRepEndIrreducible UpperTheory.V.Lit UpperTheory.V.Lit.Bor
open scoped TensorProduct

/- English proof (translation)
Take `⟨v, hv⟩` from `LinearMap.BilinForm.exists_orthogonal_basis hs`. Use `⟨_, fun j => (Real.sqrt (B (v j) (v j)))⁻¹ • v j, fun x => ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← v.sum_repr x]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `h0 : 0 < B (v j) (v j)` using `hp _ (v.ne_zero j)`.

Establish `h1 : B (v j) x = v.repr x j * B (v j) (v j)` using `by conv_lhs => rw [← v.sum_repr x]`. Rewrite using `[map_sum, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules. Introduce `k _ hk`. Establish `: B (v j) (v k) = 0` using `hv (Ne.symm hk)`.

Simplify using `[this]`. Simplify using the standard rewrite rules. Establish `h2 : Real.sqrt (B (v j) (v j)) * Real.sqrt (B (v j) (v j)) = B (v j) (v j)` using `Real.mul_self_sqrt h0.le`. Establish `h3 : Real.sqrt (B (v j) (v j)) ≠ 0` using `(Real.sqrt_pos.2 h0).ne'`. Rewrite using `[smul_smul, map_smul, LinearMap.smul_apply, h1, smul_eq_mul]`.

Use `congr 1`. Generalize the expression as in `Real.sqrt (B (v j) (v j)) = s at h2 h3`. Rewrite using `[← h2]`. Clear the denominators using the available nonvanishing facts.
-/
private theorem frame_abs {V : Type} [AddCommGroup V] [Module ℝ V] [FiniteDimensional ℝ V]
    (B : LinearMap.BilinForm ℝ V) (hs : LinearMap.IsSymm B) (hp : ∀ x, x ≠ 0 → 0 < B x x) :
    ∃ (n : ℕ) (e : Fin n → V), ∀ x, x = ∑ j, B (e j) x • e j := by
  obtain ⟨v, hv⟩ := LinearMap.BilinForm.exists_orthogonal_basis hs
  refine ⟨_, fun j => (Real.sqrt (B (v j) (v j)))⁻¹ • v j, fun x => ?_⟩
  conv_lhs => rw [← v.sum_repr x]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h0 : 0 < B (v j) (v j) := hp _ (v.ne_zero j)
  have h1 : B (v j) x = v.repr x j * B (v j) (v j) := by
    conv_lhs => rw [← v.sum_repr x]
    rw [map_sum, Finset.sum_eq_single j]
    · simp
    · intro k _ hk
      have : B (v j) (v k) = 0 := hv (Ne.symm hk)
      simp [this]
    · simp
  have h2 : Real.sqrt (B (v j) (v j)) * Real.sqrt (B (v j) (v j)) = B (v j) (v j) := Real.mul_self_sqrt h0.le
  have h3 : Real.sqrt (B (v j) (v j)) ≠ 0 := (Real.sqrt_pos.2 h0).ne'
  rw [smul_smul, map_smul, LinearMap.smul_apply, h1, smul_eq_mul]
  congr 1
  generalize Real.sqrt (B (v j) (v j)) = s at h2 h3
  rw [← h2]
  field_simp

private noncomputable def trB (E : Type) [Field E] [NumberField E] (a : ℕ) : LinearMap.BilinForm ℝ (Herm E a) :=
  LinearMap.mk₂ ℝ (fun X Y => trF X.1 Y.1)
    (fun X Y Z => by simp [trF, add_mul, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])
    (fun X Y Z => by simp [trF, mul_add, Finset.sum_add_distrib])
    (fun c X Y => by simp [trF, Finset.mul_sum])

/- English proof (translation)
Establish `h : star X.1 = X.1` using `X.2`. Establish `h' : ∀ i j w, X.1 j i w = starRingEnd ℂ (X.1 i j w)` using `fun i j w => by conv_lhs => rw [← h]`. Both sides reduce to the same expression. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Simplify using `only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Complex.re_sum]`.

Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[h' i j w, Complex.mul_conj, Complex.ofReal_re]`.
-/
private theorem trF_self {E : Type} [Field E] [NumberField E] {a : ℕ} (X : Herm E a) :
    trF X.1 X.1 = ∑ w : InfinitePlace E, ∑ i, ∑ j, Complex.normSq (X.1 i j w) := by
  have h : star X.1 = X.1 := X.2
  have h' : ∀ i j w, X.1 j i w = starRingEnd ℂ (X.1 i j w) := fun i j w => by
    conv_lhs => rw [← h]
    rfl
  refine Finset.sum_congr rfl fun w _ => ?_
  simp only [Matrix.trace, Matrix.diag, Matrix.mul_apply, Finset.sum_apply, Pi.mul_apply, Complex.re_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
  rw [h' i j w, Complex.mul_conj, Complex.ofReal_re]

/- English proof (translation)
Introduce `E _ _ _ a`. Use `frame_abs (trB E a) ⟨fun X Y => ?_⟩ fun X hX => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `trF X.1 Y.1 = trF Y.1 X.1`. Simplify using `only [trF, Matrix.trace_mul_comm X.1 Y.1]`. Express the relevant statement in the definitionally equal form `0 < trF X.1 X.1`.

Rewrite using `[trF_self]`. Establish `hn : ∀ w i j, 0 ≤ Complex.normSq (X.1 i j w)` using `fun _ _ _ => Complex.normSq_nonneg _`. Use `lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j) fun h => hX ?_` and prove the remaining obligations. Use `Subtype.ext (Matrix.ext fun i j => funext fun w => ?_)` and prove the remaining obligations. Establish `h1` using `(Finset.sum_eq_zero_iff_of_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h.symm w (Finset.mem_univ _)`.

Establish `h2` using `(Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h1 i (Finset.mem_univ _)`. Establish `h3` using `(Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn w i j).1 h2 j (Finset.mem_univ _)`. Conclude with `Complex.normSq_eq_zero.1 h3`.
-/
theorem UpperTheory.V.Lit.Bor.frameEx :
    UpperTheory.V.Lit.Bor.FrameEx := by
  intro E _ _ _ a
  refine frame_abs (trB E a) ⟨fun X Y => ?_⟩ fun X hX => ?_
  · change trF X.1 Y.1 = trF Y.1 X.1
    simp only [trF, Matrix.trace_mul_comm X.1 Y.1]
  · change 0 < trF X.1 X.1
    rw [trF_self]
    have hn : ∀ w i j, 0 ≤ Complex.normSq (X.1 i j w) := fun _ _ _ => Complex.normSq_nonneg _
    refine lt_of_le_of_ne (Finset.sum_nonneg fun w _ => Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j)
      fun h => hX ?_
    refine Subtype.ext (Matrix.ext fun i j => funext fun w => ?_)
    have h1 := (Finset.sum_eq_zero_iff_of_nonneg fun w _ =>
      Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h.symm w (Finset.mem_univ _)
    have h2 := (Finset.sum_eq_zero_iff_of_nonneg fun i _ => Finset.sum_nonneg fun j _ => hn w i j).1 h1 i (Finset.mem_univ _)
    have h3 := (Finset.sum_eq_zero_iff_of_nonneg fun j _ => hn w i j).1 h2 j (Finset.mem_univ _)
    exact Complex.normSq_eq_zero.1 h3
