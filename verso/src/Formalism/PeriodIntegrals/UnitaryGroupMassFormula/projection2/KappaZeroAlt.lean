import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.EmbedMatrixBasisVecApplyOfNotFree
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.AllowColLt

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

/- English proof (translation)
Substitute using the available equality. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Simplify using the standard rewrite rules. Use linear arithmetic over natural numbers and integers. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private theorem det_eq_det_castLE_of_cols_eq_one {k : Type} [Field k] {a t N : ℕ} (hN : a + t = N)
    (K : Matrix (Fin N) (Fin N) k) (h0 : ∀ p q : Fin N, a ≤ q.1 → K p q = if p = q then 1 else 0) :
    K.det = (Matrix.of fun s s' : Fin a =>
      K (Fin.castLE (Nat.le.intro hN) s) (Fin.castLE (Nat.le.intro hN) s')).det := by
  subst hN
  have hK : Matrix.reindex finSumFinEquiv.symm finSumFinEquiv.symm K =
      Matrix.fromBlocks (Matrix.of fun s s' : Fin a => K (Fin.castAdd t s) (Fin.castAdd t s'))
        0 (Matrix.of fun (s : Fin t) (s' : Fin a) => K (Fin.natAdd a s) (Fin.castAdd t s')) 1 := by
    ext (s | s) (s' | s')
    · rfl
    · show K (Fin.castAdd t s) (Fin.natAdd a s') = 0
      rw [h0 (Fin.castAdd t s) (Fin.natAdd a s') (by simp), if_neg]
      intro h
      have := congrArg Fin.val h
      simp only [Fin.val_castAdd, Fin.val_natAdd] at this
      omega
    · rfl
    · show K (Fin.natAdd a s) (Fin.natAdd a s') = (1 : Matrix (Fin t) (Fin t) k) s s'
      rw [h0 (Fin.natAdd a s) (Fin.natAdd a s') (by simp), Matrix.one_apply]
      by_cases h : s = s'
      · subst h
        simp
      · rw [if_neg h, if_neg]
        intro h'
        apply h
        have := congrArg Fin.val h'
        simp only [Fin.val_natAdd] at this
        exact Fin.ext (by omega)
  rw [← Matrix.det_reindex_self finSumFinEquiv.symm K, hK, Matrix.det_fromBlocks_zero₁₂,
    Matrix.det_one, mul_one]
  rfl

/- English proof (translation)
Replace the relevant objects with their definitions. Separate the alternatives or extract the components of the hypothesis. Prove the first alternative. Prove the second alternative. A detailed English derivation is pending.
-/
private theorem allow_mono {k₀ m t a b p q : ℕ} (hab : a ≤ b) (h : PI.OneCosetSharp.Allow k₀ m t a p q) :
    PI.OneCosetSharp.Allow k₀ m t b p q := by
  unfold PI.OneCosetSharp.Allow at h ⊢
  split_ifs at h ⊢
  · exact h
  · exact h
  · rcases h with h | ⟨h1, h2⟩
    · exact Or.inl h
    · exact Or.inr ⟨lt_of_lt_of_le h1 hab, h2⟩

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Replace the chosen expression with an arbitrary variable. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact.

Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify using the standard rewrite rules. Extract witnesses or component facts from the available result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Establish an intermediate fact. Replace the relevant objects with their definitions. Rewrite the conclusion using the stated equalities.

By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Consider separately whether the proposition holds or fails. Prove the first alternative. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Consider separately whether the proposition holds or fails.

Rewrite the indicated hypotheses using the stated equalities. Rewrite the indicated hypotheses using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Establish an intermediate fact. Establish an intermediate fact.

Rewrite the indicated hypotheses using the stated equalities. Replace the relevant objects with their definitions. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
theorem kappaZero : KappaZero := by
  intro k inst ψ₀ χ k₀ m t j n' c n hadm y hy
  obtain ⟨hk, hr⟩ := PI.OneCosetSharp.W.P2.nums_le hadm
  obtain ⟨-, -, -, hj1, -, -, hdom, hcod⟩ := hadm
  have hN : k₀ + m - 1 + (j - 1) * t + t = n + c := by
    rw [hcod]
    obtain ⟨j', rfl⟩ : ∃ j', j = j' + 1 := ⟨j - 1, by omega⟩
    rw [Nat.add_sub_cancel]
    generalize k₀ + m - 1 = r
    ring
  have key : (∀ p', p' < k₀ + m - 1 → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p' p' = 1) ∧
      (∀ p p', p < n + c → p' < k₀ + m - 1 + (j - 1) * t → p ≠ p' → PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p p' ≠ 0 →
        PI.OneCosetSharp.Allow k₀ m t (k₀ + m - 1 + (j - 1) * t) p p') ∧
      (Matrix.of fun s s' : Fin (k₀ + m - 1 + (j - 1) * t) =>
        PI.OneCosetSharp.ent k₀ (c + 1) n' c n y s.1 s'.1).det ≠ 0 := by
    simp only [PI.OneCosetSharp.PhiS] at hy
    split_ifs at hy with hcond
    · refine ⟨hcond.1, hcond.2, fun hdet => hy ?_⟩
      rw [hdet]
      simp [PI.OneCosetSharp.chiV]
    · exact absurd rfl hy
  have hcoord : ∀ (v : Fin (n + c) → k) (l : Fin (n + c)), PI.OneCosetSharp.Loc.atN v l.1 = v l := fun v l => by
    simp only [PI.OneCosetSharp.Loc.atN, dif_pos l.2, Fin.eta]
  obtain ⟨K, hK⟩ : ∃ K : Matrix (Fin (n + c)) (Fin (n + c)) k, ∀ p q, K p q =
      if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1 else if p = q then 1 else 0 :=
    ⟨Matrix.of fun p q => if q.1 < k₀ + m - 1 + (j - 1) * t then PI.OneCosetSharp.ent k₀ (c + 1) n' c n y p.1 q.1
      else if p = q then 1 else 0, fun _ _ => rfl⟩
  have hdetK : K.det ≠ 0 := by
    rw [det_eq_det_castLE_of_cols_eq_one hN K (fun p q hq => by rw [hK, if_neg (not_lt.mpr hq)])]
    refine ne_of_eq_of_ne ?_ key.2.2
    congr 1
    ext s s'
    simp only [Matrix.of_apply]
    rw [hK, if_pos] <;> first | rfl | exact s'.2
  have hA : IsUnit (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm
      (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm).det := by
    rw [Matrix.det_submatrix_equiv_self]
    exact isUnit_iff_ne_zero.mpr hdetK
  obtain ⟨κ, hκ⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), κ.toLinearMap =
      Matrix.toLin' (K.submatrix (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm (PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm) :=
    ⟨Matrix.toLinearEquiv' _ (Matrix.invertibleOfIsUnitDet _ hA), rfl⟩
  have hperm : PI.OneCosetSharp.W.P2.Pm k₀ hk κ = K := by
    unfold PI.OneCosetSharp.W.P2.Pm
    rw [hκ, LinearMap.toMatrix'_toLin']
    ext p q
    simp only [Matrix.submatrix_apply, Equiv.symm_apply_apply]
  refine ⟨κ, ?_, ?_⟩
  · rw [PI.OneCosetSharp.W.P2.injs_iff hk hr κ, hperm, PI.OneCosetSharp.W.P2.mem_alg]
    refine ⟨fun p q hpq => ?_, fun p hp => ?_⟩
    · by_cases hpq' : p = q
      · exact Or.inl (congrArg Fin.val hpq')
      · refine Or.inr ?_
        have hne : p.1 ≠ q.1 := fun h => hpq' (Fin.ext h)
        by_cases hq : q.1 < k₀ + m - 1 + (j - 1) * t
        · rw [hK, if_pos hq] at hpq
          exact allow_mono (Nat.le.intro hN) (key.2.1 p.1 q.1 p.2 hq hne hpq)
        · rw [hK, if_neg hq, if_neg hpq'] at hpq
          exact absurd rfl hpq
    · have hpa : p.1 < k₀ + m - 1 + (j - 1) * t := by omega
      rw [hK, if_pos hpa]
      exact key.1 p.1 hp
  · intro p hp
    have hpa : p < k₀ + m - 1 + (j - 1) * t := by omega
    have hpN : p < n + c := by omega
    funext l
    have hl : PI.OneCosetSharp.LocE.fIdx k₀ c n ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l).1 = l.1 :=
      congrArg Fin.val ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).apply_symm_apply l)
    have e1 := PI.OneCosetSharp.W.P2.ent_eq hk κ ((PI.OneCosetSharp.W.P2.fe k₀ c n hk).symm l) ⟨p, hpN⟩
    rw [hperm, hK, if_pos hpa] at e1
    unfold PI.OneCosetSharp.ent at e1
    rw [hl, hcoord, hcoord] at e1
    exact e1

end PI.OneCosetSharp.W
