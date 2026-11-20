import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ValuationLocalVolumes.SingleMulVec

noncomputable section

namespace PI.OmVe

open PI.VolStabSW Matrix

section gen

variable {K : Type} [CommRing K] (σ : K →+* K) {M : ℕ} (J : Matrix (Fin M) (Fin M) K)

/- English proof (translation)
Distinguish the cases in `h : i = p`. Conclude with `Or.inl h`. Use `right`. Conclude with `(Fin.eq_self_or_eq_succAbove p i).resolve_left h`.
-/
private theorem eq_or_exists_succAbove {n : ℕ} (p i : Fin (n + 1)) :
    i = p ∨ ∃ j, i = p.succAbove j := by
  by_cases h : i = p
  · exact Or.inl h
  · right
    exact (Fin.eq_self_or_eq_succAbove p i).resolve_left h

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hh : ∀ i j, PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j` using `fun i j => congrFun (congrFun h i) j`. Use `⟨?_, fun j => ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `j k show PI.VolStabSW.ffH σ J (X (i₀.succAbove j)) (X (i₀.succAbove k)) = T (i₀.succAbove j) (i₀.succAbove k)`.

Establish `hne : i₀.succAbove j ≠ i₀` using `Fin.succAbove_ne i₀ j`. Rewrite using `[hh]`. Simplify using `[hne.symm]`. Establish `hne : i₀.succAbove j ≠ i₀` using `Fin.succAbove_ne i₀ j`. Rewrite using `[hh, hc]`.

Simplify using `[hne.symm]`. Rewrite using `[hh, hr]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h1, h2, h3⟩`. Use extensionality with `i j`.

Use `show PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j`. Apply the tactic sequence `rcases eq_or_exists_succAbove i₀ i with hi | ⟨i', hi⟩ <;>`. Apply the tactic sequence `rcases eq_or_exists_succAbove i₀ j with hj | ⟨j', hj⟩ <;> rw [hi, hj]`. Rewrite using `[h3, hr]`. Simplify using the standard rewrite rules.

Establish `hne : i₀.succAbove j' ≠ i₀` using `Fin.succAbove_ne i₀ j'`. Rewrite using `[ffH_herm σ J hσ hJ (X (i₀.succAbove j')) (X i₀), h2 j', map_zero, hr]`. Simplify using `[hne.symm]`. Establish `hne : i₀.succAbove i' ≠ i₀` using `Fin.succAbove_ne i₀ i'`. Rewrite using `[h2 i', hc]`.

Simplify using `[hne.symm]`. Establish `hne : i₀.succAbove i' ≠ i₀` using `Fin.succAbove_ne i₀ i'`. Rewrite using `[show PI.VolStabSW.ffH σ J (X (i₀.succAbove i')) (X (i₀.succAbove j')) = T (i₀.succAbove i') (i₀.succAbove j') from congrFun (congrFun h1 i') j']`. Simplify using `[hne.symm]`.
-/
theorem gram_split (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (X : Fin (a' + 1) → Fin M → K) :
    ffGram σ J X = T + Matrix.single i₀ i₀ t ↔
      ffGram σ J (fun j => X (i₀.succAbove j)) = T.submatrix i₀.succAbove i₀.succAbove ∧
        (∀ j, ffH σ J (X (i₀.succAbove j)) (X i₀) = 0) ∧ ffH σ J (X i₀) (X i₀) = t := by
  constructor
  · intro h
    have hh : ∀ i j, PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j :=
      fun i j => congrFun (congrFun h i) j
    refine ⟨?_, fun j => ?_, ?_⟩
    · ext j k
      show PI.VolStabSW.ffH σ J (X (i₀.succAbove j)) (X (i₀.succAbove k)) =
        T (i₀.succAbove j) (i₀.succAbove k)
      have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh]
      simp [hne.symm]
    · have hne : i₀.succAbove j ≠ i₀ := Fin.succAbove_ne i₀ j
      rw [hh, hc]
      simp [hne.symm]
    · rw [hh, hr]
      simp
  · rintro ⟨h1, h2, h3⟩
    ext i j
    show PI.VolStabSW.ffH σ J (X i) (X j) = T i j + Matrix.single i₀ i₀ t i j
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨i', hi⟩ <;>
      rcases eq_or_exists_succAbove i₀ j with hj | ⟨j', hj⟩ <;> rw [hi, hj]
    · rw [h3, hr]
      simp
    · have hne : i₀.succAbove j' ≠ i₀ := Fin.succAbove_ne i₀ j'
      rw [ffH_herm σ J hσ hJ (X (i₀.succAbove j')) (X i₀), h2 j', map_zero, hr]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [h2 i', hc]
      simp [hne.symm]
    · have hne : i₀.succAbove i' ≠ i₀ := Fin.succAbove_ne i₀ i'
      rw [show PI.VolStabSW.ffH σ J (X (i₀.succAbove i')) (X (i₀.succAbove j')) =
          T (i₀.succAbove i') (i₀.succAbove j') from congrFun (congrFun h1 i') j']
      simp [hne.symm]

/- English proof (translation)
Establish `key` using `fun X => gram_split σ J hσ hJ T i₀ hr hc t X`. Apply `Nat.card_congr` to reduce the goal to its premises. Use `{ toFun := fun X => ⟨⟨fun j => X.1 (i₀.succAbove j), ((key X.1).1 X.2.1).1⟩, ⟨X.1 i₀, ((key X.1).1 X.2.1).2.1, ((key X.1).1 X.2.1).2.2, X.2.2⟩⟩ invFun := fun p => ⟨Fin.insertNth (α := fun _ => Fin M → K) i₀ p.2.1 p.1.1, (key _).2 ⟨by simpa [Fin.insertNth_apply_succAbove] using p. …` and prove the remaining obligations. Introduce `X`. Apply `Subtype.ext` to reduce the goal to its premises.

Use function extensionality and compare the values at `i`. Apply the tactic sequence `rcases eq_or_exists_succAbove i₀ i with hi | ⟨j, hi⟩ <;> rw [hi]`. Simplify using `[Fin.insertNth_apply_same]`. Simplify using `[Fin.insertNth_apply_succAbove]`. Introduce and unpack `⟨⟨Y, hY⟩, ⟨x, hx⟩⟩`.

Apply `Sigma.subtype_ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Simplify using `[Fin.insertNth_apply_succAbove]`. Simplify using `[Fin.insertNth_apply_same]`.
-/
theorem card_split [Finite K] (hσ : ∀ x, σ (σ x) = x) (hJ : ∀ i j, σ (J j i) = J i j) {a' : ℕ}
    (T : Matrix (Fin (a' + 1)) (Fin (a' + 1)) K) (i₀ : Fin (a' + 1)) (hr : ∀ j, T i₀ j = 0)
    (hc : ∀ j, T j i₀ = 0) (t : K) (R : (Fin M → K) → Prop) :
    Nat.card {X : Fin (a' + 1) → Fin M → K // ffGram σ J X = T + Matrix.single i₀ i₀ t ∧ R (X i₀)} =
      Nat.card (Σ Y : {Y : Fin a' → Fin M → K // ffGram σ J Y = T.submatrix i₀.succAbove i₀.succAbove},
        {x : Fin M → K // (∀ j, ffH σ J (Y.1 j) x = 0) ∧ ffH σ J x x = t ∧ R x}) := by
  have key := fun X => gram_split σ J hσ hJ T i₀ hr hc t X
  apply Nat.card_congr
  refine
    { toFun := fun X => ⟨⟨fun j => X.1 (i₀.succAbove j), ((key X.1).1 X.2.1).1⟩,
        ⟨X.1 i₀, ((key X.1).1 X.2.1).2.1, ((key X.1).1 X.2.1).2.2, X.2.2⟩⟩
      invFun := fun p => ⟨Fin.insertNth (α := fun _ => Fin M → K) i₀ p.2.1 p.1.1,
        (key _).2 ⟨by simpa [Fin.insertNth_apply_succAbove] using p.1.2,
          fun j => by simpa [Fin.insertNth_apply_succAbove, Fin.insertNth_apply_same]
            using p.2.2.1 j,
          by simpa [Fin.insertNth_apply_same] using p.2.2.2.1⟩,
        by simpa [Fin.insertNth_apply_same] using p.2.2.2.2⟩
      left_inv := ?_
      right_inv := ?_ }
  · intro X
    apply Subtype.ext
    funext i
    rcases eq_or_exists_succAbove i₀ i with hi | ⟨j, hi⟩ <;> rw [hi]
    · simp [Fin.insertNth_apply_same]
    · simp [Fin.insertNth_apply_succAbove]
  · rintro ⟨⟨Y, hY⟩, ⟨x, hx⟩⟩
    apply Sigma.subtype_ext
    · apply Subtype.ext
      funext j
      simp [Fin.insertNth_apply_succAbove]
    · simp [Fin.insertNth_apply_same]

/- English proof (translation)
Set `f : (Fin M → K) →+ (Fin a' → K)` to `AddMonoidHom.mk' (fun x j => PI.VolStabSW.ffH σ J (Y j) x) (fun x y => by`. Use function extensionality and compare the values at `j`. Conclude with `ffH_add_right σ J (Y j) x y)`. Establish `hsurj : Function.Surjective f`. Introduce `v`.

Use `⟨∑ l, (T0⁻¹ *ᵥ v) l • Y l, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `j`. Use `show PI.VolStabSW.ffH σ J (Y j) (∑ l, (T0⁻¹ *ᵥ v) l • Y l) = v j`. Rewrite using `[ffH_sum_right σ J Finset.univ]`. Establish `hT : ∀ l, PI.VolStabSW.ffH σ J (Y j) (Y l) = T0 j l` using `fun l => congrFun (congrFun hY j) l`.

Repeatedly rewrite using `[hT]`. Establish `hinv : T0 *ᵥ (T0⁻¹ *ᵥ v) = v`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T0 hu, Matrix.one_mulVec]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mulVec, dotProduct]`.

Conclude with `Finset.sum_congr rfl (fun l _ => mul_comm _ _)`. Use `_ = v j := by rw [hinv]`. Establish `hker : Nat.card {x : Fin M → K // ∀ j, PI.VolStabSW.ffH σ J (Y j) x = 0} = Nat.card f.ker`. Apply `Nat.card_congr` to reduce the goal to its premises. Conclude with `Equiv.subtypeEquivRight (fun x => by`.

Rewrite using `[AddMonoidHom.mem_ker]`. Conclude with `⟨fun h => by ext j; exact h j, fun h j => congrFun h j⟩)`. Establish `hidx : f.ker.index = Nat.card (Fin a' → K)`. Conclude with `Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv`. Establish `hpow : ∀ n : ℕ, Nat.card (Fin n → K) = Nat.card K ^ n`.

Introduce `n`. Rewrite using `[Nat.card_fun, Nat.card_fin]`. Rewrite using `[hker, ← hpow a', ← hidx, AddSubgroup.card_mul_index, hpow M]`.
-/
theorem card_perp [Finite K] {a' : ℕ} (T0 : Matrix (Fin a') (Fin a') K) (hu : IsUnit T0.det)
    (Y : Fin a' → Fin M → K) (hY : ffGram σ J Y = T0) :
    Nat.card {x : Fin M → K // ∀ j, ffH σ J (Y j) x = 0} * Nat.card K ^ a' = Nat.card K ^ M := by
  classical
  let f : (Fin M → K) →+ (Fin a' → K) :=
    AddMonoidHom.mk' (fun x j => PI.VolStabSW.ffH σ J (Y j) x) (fun x y => by
      funext j
      exact ffH_add_right σ J (Y j) x y)
  have hsurj : Function.Surjective f := by
    intro v
    refine ⟨∑ l, (T0⁻¹ *ᵥ v) l • Y l, ?_⟩
    funext j
    show PI.VolStabSW.ffH σ J (Y j) (∑ l, (T0⁻¹ *ᵥ v) l • Y l) = v j
    rw [ffH_sum_right σ J Finset.univ]
    have hT : ∀ l, PI.VolStabSW.ffH σ J (Y j) (Y l) = T0 j l := fun l => congrFun (congrFun hY j) l
    simp_rw [hT]
    have hinv : T0 *ᵥ (T0⁻¹ *ᵥ v) = v := by
      rw [Matrix.mulVec_mulVec, Matrix.mul_nonsing_inv T0 hu, Matrix.one_mulVec]
    calc ∑ l, (T0⁻¹ *ᵥ v) l * T0 j l = (T0 *ᵥ (T0⁻¹ *ᵥ v)) j := by
          simp only [Matrix.mulVec, dotProduct]
          exact Finset.sum_congr rfl (fun l _ => mul_comm _ _)
      _ = v j := by rw [hinv]
  have hker : Nat.card {x : Fin M → K // ∀ j, PI.VolStabSW.ffH σ J (Y j) x = 0} = Nat.card f.ker := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun x => by
      rw [AddMonoidHom.mem_ker]
      exact ⟨fun h => by ext j; exact h j, fun h j => congrFun h j⟩)
  have hidx : f.ker.index = Nat.card (Fin a' → K) := by
    exact Nat.card_congr (QuotientAddGroup.quotientKerEquivOfSurjective f hsurj).toEquiv
  have hpow : ∀ n : ℕ, Nat.card (Fin n → K) = Nat.card K ^ n := by
    intro n
    rw [Nat.card_fun, Nat.card_fin]
  rw [hker, ← hpow a', ← hidx, AddSubgroup.card_mul_index, hpow M]

/- English proof (translation)
Rewrite using `[← Nat.card_sum]`. Conclude with `Nat.card_congr (((Equiv.subtypeSubtypeEquivSubtypeInter G Q).symm.sumCongr (Equiv.subtypeSubtypeEquivSubtypeInter G (fun x => ¬ Q x)).symm).trans (Equiv.sumCompl (fun y : {x // G x} => Q y.1)))`.
-/
theorem card_and_add {α : Type} [Finite α] (G Q : α → Prop) :
    Nat.card {x // G x ∧ Q x} + Nat.card {x // G x ∧ ¬ Q x} = Nat.card {x // G x} := by
  classical
  rw [← Nat.card_sum]
  exact Nat.card_congr
    (((Equiv.subtypeSubtypeEquivSubtypeInter G Q).symm.sumCongr
      (Equiv.subtypeSubtypeEquivSubtypeInter G (fun x => ¬ Q x)).symm).trans
      (Equiv.sumCompl (fun y : {x // G x} => Q y.1)))

end gen

end PI.OmVe
