import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.MinimalExponentAttained

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

/- English proof (translation)
Introduce `ℓ hℓ s H0 h d U a b hh hH hU ha hab hb hd`. Use `Fact.mk hℓ` as an intermediate fact. Establish `hn0 : n0 ℓ H0 ≤ Nat.log ℓ (2 * h) + 1`. Apply `Nat.sInf_le` to reduce the goal to its premises. Use `show H0 ≤ ℓ ^ (Nat.log ℓ (2 * h) + 1) * (ℓ - 1)`.

Establish `h1 : 2 * h < ℓ ^ (Nat.log ℓ (2 * h) + 1)` using `Nat.lt_pow_succ_log_self hℓ.one_lt _`. Establish `h2 : 1 ≤ ℓ - 1` using `by have := hℓ.two_le; omega`. Use the polynomial consequences of the given equalities and inequalities. Use `⟨by unfold mOf; omega, ?_⟩` and prove the remaining obligations. Generalize the expression as in `mOf ℓ s H0 = m at hd ⊢`.

Establish `hr : ∀ i ∈ Finset.Ico a b, rI ℓ m U i ≤ U.card * (m + Nat.log ℓ (2 * h))`. Introduce `i hi`. Rewrite `hi` using `[Finset.mem_Ico]`. Unfold `rI`. Combine the equalities or inequalities in the displayed calculation.

Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises. Introduce `u hu`. Establish `hu'` using `hU u (Finset.mem_of_mem_erase hu)`. Establish `h1 : padicValInt ℓ (u - i) ≤ Nat.log ℓ (2 * h)`. Unfold `padicValInt`.

Use `le_trans (padicValNat_le_nat_log _) (Nat.log_mono_right ?_)` and prove the remaining obligations. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Use `_ ≤ U.card * (m + Nat.log ℓ (2 * h)) := by`. Rewrite using `[smul_eq_mul]`.

Conclude with `Nat.mul_le_mul_right _ (Finset.card_erase_le)`. Establish `hc : cM ℓ m U a b ≤ (b - a).toNat * (3 + U.card * (m + Nat.log ℓ (2 * h)))`. Unfold `cM`. Combine the equalities or inequalities in the displayed calculation. Apply `Finset.sum_le_card_nsmul` to reduce the goal to its premises.

Introduce `i hi`. Use `hr i hi` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `_ = _ := by rw [Int.card_Ico, smul_eq_mul]`. Unfold `cLL`.

Use linear arithmetic over natural numbers and integers.
-/
theorem ll3 : StatLL3 := by
  intro ℓ hℓ s H0 h d U a b hh hH hU ha hab hb hd
  have := Fact.mk hℓ
  have hn0 : n0 ℓ H0 ≤ Nat.log ℓ (2 * h) + 1 := by
    apply Nat.sInf_le
    show H0 ≤ ℓ ^ (Nat.log ℓ (2 * h) + 1) * (ℓ - 1)
    have h1 : 2 * h < ℓ ^ (Nat.log ℓ (2 * h) + 1) := Nat.lt_pow_succ_log_self hℓ.one_lt _
    have h2 : 1 ≤ ℓ - 1 := by have := hℓ.two_le; omega
    nlinarith
  refine ⟨by unfold mOf; omega, ?_⟩
  generalize mOf ℓ s H0 = m at hd ⊢
  have hr : ∀ i ∈ Finset.Ico a b, rI ℓ m U i ≤ U.card * (m + Nat.log ℓ (2 * h)) := by
    intro i hi
    rw [Finset.mem_Ico] at hi
    unfold rI
    calc ∑ u ∈ U.erase i, (m + padicValInt ℓ (u - i))
        ≤ (U.erase i).card • (m + Nat.log ℓ (2 * h)) := by
          apply Finset.sum_le_card_nsmul
          intro u hu
          have hu' := hU u (Finset.mem_of_mem_erase hu)
          have h1 : padicValInt ℓ (u - i) ≤ Nat.log ℓ (2 * h) := by
            unfold padicValInt
            refine le_trans (padicValNat_le_nat_log _) (Nat.log_mono_right ?_)
            omega
          omega
      _ ≤ U.card * (m + Nat.log ℓ (2 * h)) := by
          rw [smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_erase_le)
  have hc : cM ℓ m U a b ≤ (b - a).toNat * (3 + U.card * (m + Nat.log ℓ (2 * h))) := by
    unfold cM
    calc ∑ i ∈ Finset.Ico a b, (2 + max 1 (rI ℓ m U i))
        ≤ (Finset.Ico a b).card • (3 + U.card * (m + Nat.log ℓ (2 * h))) := by
          apply Finset.sum_le_card_nsmul
          intro i hi
          have := hr i hi
          omega
      _ = _ := by rw [Int.card_Ico, smul_eq_mul]
  unfold cLL
  omega

/- English proof (translation)
Introduce `ℓ hℓ N _ F γ hF0 hanti hstep b hb x`. Use `set M := ℓ ^ (b - 1) with hM`. Set `P : AddSubgroup N` to `(nsmulAddMonoidHom (α := N) (ℓ ^ 2)).range ⊔ F M`. Establish `hP : ∀ v ∈ P, ∃ y : N, ∃ z ∈ F M, v = (ℓ ^ 2) • y + z`. Introduce `v hv`.

Take `⟨p, ⟨y, rfl⟩, z, hz, rfl⟩` from `AddSubgroup.mem_sup.1 hv`. Conclude with `⟨y, z, hz, rfl⟩`. Apply `hP` to reduce the goal to its premises. Set `G : Module.End ℤ N` to `γ.toIntLinearMap`. Set `Y : Module.End ℤ N` to `G - 1`.

Establish `hY : ∀ v, Y v = γ v - v` using `fun v => by simp [Y, G]`. Establish `hYk : ∀ k, (Y ^ k) x ∈ F k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => rw [hF0]`.

Discharge the goal by the elementary cases of `trivial`. Consider the case `succ k ih`. Rewrite using `[pow_succ', Module.End.mul_apply, hY]`. Conclude with `hstep k _ ih`. Establish `hmono : ∀ k, M ≤ k → F k ≤ F M`.

Introduce `k hk`. Proceed by induction on `k, hk using Nat.le_induction with`. Consider the case `base => exact le_refl _`. Consider the case `succ k _ ih => exact le_trans (hanti k) ih`. Establish `hγ : G = Y + 1` using `by simp [Y]`.

Establish `hpow : (⇑γ)^[ℓ ^ b] x = ((Y + 1) ^ (ℓ ^ b)) x`. Rewrite using `[← hγ, Module.End.pow_apply]`. Both sides reduce to the same expression. Rewrite using `[hpow, (Commute.one_right Y).add_pow, Finset.sum_range_succ']`. Simplify using `only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]`.

Rewrite using `[LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_right, LinearMap.sum_apply]`. Apply `AddSubgroup.sum_mem` to reduce the goal to its premises. Introduce `k _`. Establish `hterm : (Y ^ (k + 1) * ((ℓ ^ b).choose (k + 1) : Module.End ℤ N)) x = ((ℓ ^ b).choose (k + 1)) • (Y ^ (k + 1)) x`. Rewrite using `[Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]`.

Rewrite using `[hterm]`. Distinguish the cases in `hk : k + 1 < M`. Take `⟨t, ht⟩` from `binom ℓ hℓ b (k + 1) hb (Nat.succ_pos k) hk`. Apply `AddSubgroup.mem_sup_left` to reduce the goal to its premises. Use `⟨t • (Y ^ (k + 1)) x, ?_⟩` and prove the remaining obligations.

Rewrite using `[ht, mul_smul]`. Both sides reduce to the same expression. Apply `AddSubgroup.mem_sup_right` to reduce the goal to its premises. Conclude with `(F M).nsmul_mem (hmono _ (by omega) (hYk _)) _`.
-/
theorem filtPow : StatFiltPow := by
  intro ℓ hℓ N _ F γ hF0 hanti hstep b hb x

  set M := ℓ ^ (b - 1) with hM
  let P : AddSubgroup N := (nsmulAddMonoidHom (α := N) (ℓ ^ 2)).range ⊔ F M
  have hP : ∀ v ∈ P, ∃ y : N, ∃ z ∈ F M, v = (ℓ ^ 2) • y + z := by
    intro v hv
    obtain ⟨p, ⟨y, rfl⟩, z, hz, rfl⟩ := AddSubgroup.mem_sup.1 hv
    exact ⟨y, z, hz, rfl⟩
  apply hP
  let G : Module.End ℤ N := γ.toIntLinearMap
  let Y : Module.End ℤ N := G - 1
  have hY : ∀ v, Y v = γ v - v := fun v => by simp [Y, G]
  have hYk : ∀ k, (Y ^ k) x ∈ F k := by
    intro k
    induction k with
    | zero => rw [hF0]; trivial
    | succ k ih =>
      rw [pow_succ', Module.End.mul_apply, hY]
      exact hstep k _ ih
  have hmono : ∀ k, M ≤ k → F k ≤ F M := by
    intro k hk
    induction k, hk using Nat.le_induction with
    | base => exact le_refl _
    | succ k _ ih => exact le_trans (hanti k) ih
  have hγ : G = Y + 1 := by simp [Y]
  have hpow : (⇑γ)^[ℓ ^ b] x = ((Y + 1) ^ (ℓ ^ b)) x := by
    rw [← hγ, Module.End.pow_apply]; rfl
  rw [hpow, (Commute.one_right Y).add_pow, Finset.sum_range_succ']
  simp only [one_pow, mul_one, pow_zero, Nat.choose_zero_right, Nat.cast_one]
  rw [LinearMap.add_apply, Module.End.one_apply, add_sub_cancel_right, LinearMap.sum_apply]
  apply AddSubgroup.sum_mem
  intro k _
  have hterm : (Y ^ (k + 1) * ((ℓ ^ b).choose (k + 1) : Module.End ℤ N)) x
      = ((ℓ ^ b).choose (k + 1)) • (Y ^ (k + 1)) x := by
    rw [Module.End.mul_apply, Module.End.natCast_apply, map_nsmul]
  rw [hterm]
  by_cases hk : k + 1 < M
  · obtain ⟨t, ht⟩ := binom ℓ hℓ b (k + 1) hb (Nat.succ_pos k) hk
    apply AddSubgroup.mem_sup_left
    refine ⟨t • (Y ^ (k + 1)) x, ?_⟩
    rw [ht, mul_smul]; rfl
  · apply AddSubgroup.mem_sup_right
    exact (F M).nsmul_mem (hmono _ (by omega) (hYk _)) _

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
