import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.TraceFormula.GlobalTraceComparison.TraceAsymptotics.HintSph

noncomputable section

open NumberField IsDedekindDomain Matrix Polynomial Filter Topology
open GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.LFun
open PositivityTheory.Rg.BcB.G8
open UpperTheory.V.Af.Bc (cPl)
open scoped Classical

namespace UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm

section SlopeTestRemainingChoices

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n a b : ℕ}

private def eIdx (h : a + b = n) : Fin a ⊕ Fin b ≃ Fin n := finSumFinEquiv.trans (finCongr h)

private def bm (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : Matrix (Fin n) (Fin n) (w.adicCompletion E) :=
  Matrix.reindex (eIdx h) (eIdx h) (Matrix.fromBlocks m.1.val (m.1.val * X) 0 m.2.val)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem bm_isUnit (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : IsUnit (bm h w m X) := by
  rw [Matrix.isUnit_iff_isUnit_det]
  unfold bm
  rw [Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  exact ((Matrix.isUnit_iff_isUnit_det _).1 m.1.isUnit).mul ((Matrix.isUnit_iff_isUnit_det _).1 m.2.isUnit)

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem blk_val (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X : Matrix (Fin a) (Fin b) (w.adicCompletion E)) : (GlobalTheory.BCT.blk h w m X).val = bm h w m X := by
  show (if hM : IsUnit (bm h w m X) then hM.unit else 1).val = _
  rw [dif_pos (bm_isUnit h w m X)]
  rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions. Simplify using the standard rewrite rules.
-/
private theorem blk_add (h : a + b = n) (w : Pl E) (m : GLw a w × GLw b w)
    (X Y : Matrix (Fin a) (Fin b) (w.adicCompletion E)) :
    GlobalTheory.BCT.blk h w m (X + Y) = GlobalTheory.BCT.blk h w m X * GlobalTheory.BCT.blk h w 1 Y := by
  apply Units.ext
  rw [Units.val_mul, blk_val, blk_val, blk_val]
  unfold bm
  simp [Matrix.reindex_apply, Matrix.submatrix_mul_equiv, Matrix.fromBlocks_multiply, Matrix.mul_add, add_comm]

/- English proof (translation)
Introduce a local definition for the expression. Introduce a local definition for the expression. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Both sides reduce to the same expression.

Both sides reduce to the same expression. Express the relevant assertion in an equivalent form by its definition. Consider separately whether the proposition holds or fails. Substitute using the available equality. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.
-/
private theorem blk_one_mem (h : a + b = n) (w : Pl E) (Y : Matrix (Fin a) (Fin b) (w.adicCompletion E))
    (hY : ∀ i j, Valued.v (Y i j) ≤ 1) : GlobalTheory.BCT.blk h w 1 Y ∈ GlobalTheory.LFun.KGL w n := by
  let Y' : Matrix (Fin a) (Fin b) (Ov E w) := fun i j => ⟨Y i j, hY i j⟩
  let N : Matrix (Fin n) (Fin n) (Ov E w) := Matrix.reindex (eIdx h) (eIdx h) (Matrix.fromBlocks 1 Y' 0 1)
  have hN : IsUnit N := by
    rw [Matrix.isUnit_iff_isUnit_det]
    simp [N, Matrix.det_reindex_self, Matrix.det_fromBlocks_zero₂₁]
  refine ⟨hN.unit, Units.ext ?_⟩
  rw [blk_val]
  refine Matrix.ext fun i j => ?_
  obtain ⟨i, rfl⟩ := (eIdx h).surjective i
  obtain ⟨j, rfl⟩ := (eIdx h).surjective j
  change (Ov E w).subtype (N _ _) = bm h w 1 Y _ _
  rcases i with i | i <;> rcases j with j | j <;> simp [N, bm, Y', Matrix.one_apply]
  · change (((1 : Matrix (Fin a) (Fin a) (Ov E w)) i j : Ov E w) : w.adicCompletion E) = _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hij]
      simp [hij]
  · rfl
  · rfl
  · change (((1 : Matrix (Fin b) (Fin b) (Ov E w)) i j : Ov E w) : w.adicCompletion E) = _
    by_cases hij : i = j
    · subst hij
      rw [Matrix.one_apply_eq]
      simp
    · rw [Matrix.one_apply_ne hij]
      simp [hij]

/- English proof (translation)
Replace the relevant objects with their definitions. Proceed by induction. Treat this case separately. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Treat this case separately. Fix the arbitrary inputs or assume the hypotheses.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem intMat_le (w : Pl E) (Y : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)))
    (hY : Y ∈ intMat a b w) : ∀ i j, Valued.v (Multiplicative.toAdd Y i j) ≤ 1 := by
  unfold intMat at hY
  induction hY using Subgroup.closure_induction with
  | mem x hx => exact hx
  | one => intro i j; simp
  | mul x y _ _ hx hy =>
    intro i j
    simp only [toAdd_mul, Matrix.add_apply]
    exact (Valuation.map_add _ _ _).trans (max_le (hx i j) (hy i j))
  | inv x _ hx =>
    intro i j
    simpa using hx i j

/- English proof (translation)
Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. A detailed English derivation is pending.
-/
private theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have hs : rStab (fun _ : H => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hs, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  rw [finsum_eq_single _ (1 : H ⧸ (⊤ : Subgroup H)) (fun x hx => absurd (Subsingleton.elim _ _) hx)]
  simp

/- English proof (translation)
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. By extensionality, compare the relevant components. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
private theorem supp_fin (h : a + b = n) (w : Pl E) (f : GLw n w → ℂ) (hf : HasCompactSupport f)
    (m : GLw a w × GLw b w) :
    (Function.support fun q : Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w =>
      f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd q.out))).Finite := by
  let ψ : GLw n w → Matrix (Fin a) (Fin b) (w.adicCompletion E) := fun g =>
    (m.1⁻¹).val * Matrix.of fun i j => g.val (eIdx h (Sum.inl i)) (eIdx h (Sum.inr j))
  have hψ : Continuous ψ := by
    refine continuous_const.matrix_mul ?_
    refine continuous_matrix fun i j => ?_
    exact Units.continuous_val.matrix_elem _ _
  have hψb : ∀ X, ψ (GlobalTheory.BCT.blk h w m X) = X := by
    intro X
    have hb : (Matrix.of fun i j => (GlobalTheory.BCT.blk h w m X).val (eIdx h (Sum.inl i)) (eIdx h (Sum.inr j))) =
        m.1.val * X := by
      ext i j
      rw [blk_val]
      simp [bm]
    simp only [ψ]
    rw [hb, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul]
  have hC : IsCompact (ψ '' tsupport f) := hf.isCompact.image hψ
  have hU : ∀ X ∈ ψ '' tsupport f, {Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) |
      ∀ i j, Valued.v ((Y - X) i j) ≤ 1} ∈ 𝓝 X := by
    intro X _
    have h0 : {x : w.adicCompletion E | Valued.v x ≤ 1} ∈ 𝓝 (0 : w.adicCompletion E) :=
      (Valued.mem_nhds_zero).2 ⟨1, fun x hx => show Valued.v x ≤ 1 from le_of_lt (by simpa using hx)⟩
    have : ∀ i j, ∀ᶠ Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) in 𝓝 X, Valued.v ((Y - X) i j) ≤ 1 := by
      intro i j
      have hc : Continuous fun Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (Y - X) i j :=
        (continuous_id.sub continuous_const).matrix_elem i j
      have ht : Tendsto (fun Y : Matrix (Fin a) (Fin b) (w.adicCompletion E) => (Y - X) i j) (𝓝 X) (𝓝 0) := by
        have := hc.tendsto X
        simpa using this
      exact ht h0
    exact eventually_all.2 fun i => eventually_all.2 fun j => this i j
  obtain ⟨t, -, ht⟩ := hC.elim_nhds_subcover _ hU
  refine (t.finite_toSet.image fun X => (QuotientGroup.mk (Multiplicative.ofAdd X) :
    Multiplicative (Matrix (Fin a) (Fin b) (w.adicCompletion E)) ⧸ intMat a b w)).subset ?_
  intro q hq
  have hmem : Multiplicative.toAdd q.out ∈ ψ '' tsupport f :=
    ⟨_, subset_tsupport f hq, hψb _⟩
  obtain ⟨X, hX, hXY⟩ := Set.mem_iUnion₂.1 (ht hmem)
  refine ⟨X, hX, ?_⟩
  rw [← QuotientGroup.out_eq' q]
  refine QuotientGroup.eq.2 (Subgroup.subset_closure ?_)
  intro i j
  have := hXY i j
  simpa [sub_eq_neg_add] using this

end SlopeTestRemainingChoices

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Replace the relevant objects with their definitions.

Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ctSph : CtSph := by
  intro E _ _ _ w n a b h f hf m
  refine ⟨?_, supp_fin h w f hf.1 m⟩
  have hinv := hf.2
  have havg : ∀ y : GLw n w, (avg fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * y * k)) = f y := by
    intro y
    have : (fun k : GlobalTheory.LFun.KGL w n => f ((k : GLw n w)⁻¹ * y * k)) = fun _ => f y := by
      funext k
      rw [(hinv k k.2 _).2, (hinv _ (inv_mem k.2) y).1]
    rw [this, avg_const]
  unfold ct
  simp only [havg]
  rw [hintSph _ (intMat a b w) (fun X => f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd X)))]
  intro k hk x
  show f (GlobalTheory.BCT.blk h w m (Multiplicative.toAdd x + Multiplicative.toAdd k)) = _
  rw [blk_add, (hinv _ (blk_one_mem h w _ (intMat_le w k hk)) _).2]

end UpperTheory.V.Z.Tf.GlobalTraceComparison.Asm
