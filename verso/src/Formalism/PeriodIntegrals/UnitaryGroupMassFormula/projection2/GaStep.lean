import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.projection2.MemFlagUnipotent

noncomputable section

namespace PI.OneCosetSharp.W

open Loc LocE

variable {k : Type} [Field k] {n c : ℕ}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem eN_apply (N i : ℕ) (l : Fin N) : eN k N i l = if l.1 = i then 1 else 0 := rfl

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[lowProj_apply₂, projA_apply]`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem XP_AP (w : Fin (n + c) → k) : (XP : (Fin (n + c) → k) →ₗ[k] _) (AP w) = 0 := by
  funext l
  rw [lowProj_apply₂, projA_apply]
  split_ifs <;> rfl

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[lowProj_apply₂, eN_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem lowProj_basisVec_of_le (q : ℕ) (hq : n ≤ q) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = 0 := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Use function extensionality and compare the values at `l`. Rewrite using `[lowProj_apply₂, eN_apply]`. Apply the tactic sequence `split_ifs <;> first | rfl | omega`.
-/
theorem lowProj_basisVec_of_lt (q : ℕ) (hq : q < n) : (XP : (Fin (n + c) → k) →ₗ[k] _) (eN k (n + c) q) = eN k (n + c) q := by
  funext l
  rw [lowProj_apply₂, eN_apply]
  split_ifs <;> first | rfl | omega

/- English proof (translation)
Establish `h` using `lowProj_add_highProj (n := n) (c := c) w`. Rewrite `h` using `[hw, zero_add]`. Then use the resulting hypothesis.
-/
theorem projA_eq_self_of_projX_eq_zero {w : Fin (n + c) → k} (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : AP w = w := by
  have h := lowProj_add_highProj (n := n) (c := c) w
  rwa [hw, zero_add] at h

/- English proof (translation)
Establish `hsum : w = ∑ l : Fin (n + c), w l • PI.OneCosetSharp.Loc.eN k (n + c) l.1`. Use function extensionality and compare the values at `x`. Rewrite using `[Finset.sum_apply, Finset.sum_eq_single x]`. Simplify using `[eN_apply]`. Introduce `b _ hb`.

Establish `hx : x.1 ≠ b.1` using `fun h => hb (Fin.ext h).symm`. Simplify using `[eN_apply, hx]`. Introduce `hx`. Conclude with `absurd (Finset.mem_univ x) hx`. Rewrite using `[hsum, map_sum]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul]`. Distinguish the cases in `hl : l.1 < n`. Establish `h0 : w l = 0`. Establish `h1` using `congrFun hw l`.

Rewrite `h1` using `[lowProj_apply₂, if_pos hl]`. Conclude with `h1`. Rewrite using `[h0, zero_smul, zero_smul]`. Establish `hlt` using `l.2`. Establish `hl' : l.1 = n + (l.1 - n)` using `by omega`.

Rewrite using `[hl', hga (l.1 - n) (by omega)]`.
-/
theorem fix_of_basis (g : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k))
    (hga : ∀ i < c, g (eN k (n + c) (n + i)) = eN k (n + c) (n + i)) (w : Fin (n + c) → k)
    (hw : (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0) : g w = w := by
  have hsum : w = ∑ l : Fin (n + c), w l • PI.OneCosetSharp.Loc.eN k (n + c) l.1 := by
    funext x
    rw [Finset.sum_apply, Finset.sum_eq_single x]
    · simp [eN_apply]
    · intro b _ hb
      have hx : x.1 ≠ b.1 := fun h => hb (Fin.ext h).symm
      simp [eN_apply, hx]
    · intro hx
      exact absurd (Finset.mem_univ x) hx
  rw [hsum, map_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [map_smul]
  by_cases hl : l.1 < n
  · have h0 : w l = 0 := by
      have h1 := congrFun hw l
      rw [lowProj_apply₂, if_pos hl] at h1
      exact h1
    rw [h0, zero_smul, zero_smul]
  · have hlt := l.2
    have hl' : l.1 = n + (l.1 - n) := by omega
    rw [hl', hga (l.1 - n) (by omega)]

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx`. Apply the tactic sequence `split_ifs <;> omega`.
-/
private theorem fIdx_lt_add_of_lt_add {k₀ c n p : ℕ} (hp : p < n + c) : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c := by
  unfold PI.OneCosetSharp.LocE.fIdx
  split_ifs <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
private theorem fIdx_injOn_of_lt_add {k₀ c n p p' : ℕ} (hk : k₀ ≤ n) (hp : p < n + c) (hp' : p' < n + c)
    (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p = PI.OneCosetSharp.LocE.fIdx k₀ c n p') : p = p' := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
private theorem mem_block_of_le_fIdx {k₀ c n p : ℕ} (hk : k₀ ≤ n) (hp : p < n + c)
    (h : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p) : k₀ ≤ p ∧ p < k₀ + c := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.LocE.fIdx at h`. Apply the tactic sequence `split_ifs at h <;> omega`.
-/
private theorem lt_or_le_of_fIdx_lt {k₀ c n p : ℕ} (h : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n) :
    p < k₀ ∨ k₀ + c ≤ p := by
  unfold PI.OneCosetSharp.LocE.fIdx at h
  split_ifs at h <;> omega

/- English proof (translation)
Unfold `PI.OneCosetSharp.Allow`. Use `split_ifs`. Use linear arithmetic over natural numbers and integers. Use `left`. Use linear arithmetic over natural numbers and integers.

Use `left`. Use linear arithmetic over natural numbers and integers.
-/
private theorem allow_of_mem_block_of_le_right {k₀ m t N c p p' : ℕ} (hcm : c + 1 < m) (hp : k₀ ≤ p)
    (hpc : p < k₀ + c) (hp' : k₀ + c ≤ p') : PI.OneCosetSharp.Allow k₀ m t N p p' := by
  unfold PI.OneCosetSharp.Allow
  split_ifs
  · omega
  · left; omega
  · left; omega

/- English proof (translation)
Introduce `k _ k₀ m t j n' c n hadm g hga hfree`. Take `⟨hk₀, -, hm4, hj1, hjm, hc, hn', hn⟩` from `hadm`. Generalize the expression as in `j * t = s at hn`. Generalize the expression as in `(j - 1) * t = s' at hn'`. Establish `hkn : k₀ ≤ n` using `by omega`.

Establish `hcm : c + 1 < m` using `by omega`. Take `⟨B, hB⟩ : ∃ B : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k), ∀ w, B w = AP (g (XP w))` from `⟨AP ∘ₗ g.toLinearMap ∘ₗ XP, fun w => rfl⟩`. Establish `hfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → g w = w` using `fix_of_basis g hga`. Establish `hB0 : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → B w = 0`. Introduce `w hw`.

Rewrite using `[hB, hw]`. Simplify using the standard rewrite rules. Establish `hBB : ∀ w, B (B w) = 0` using `fun w => hB0 _ (by rw [hB]; exact XP_AP _)`. Choose the witnesses or unpack the hypotheses as in `⟨κ, hκ, hκs⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k), (∀ w, κ w = w + B w) ∧ ∀ w, κ.symm w = w - B w := by`. Use `⟨LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B) ?_ ?_, fun w => rfl, fun w => rfl⟩` and prove the remaining obligations.

Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_sub, hBB, add_zero]`. Normalize the expressions using the abelian group laws. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply, map_add, hBB, sub_zero]`.

Normalize the expressions using the abelian group laws. Establish `hg : ∀ v, g v = g (XP v) + AP v`. Introduce `v`. Use `conv_lhs => rw [← lowProj_add_highProj (n := n) (c := c) v]`. Rewrite using `[map_add, hfix _ (XP_AP v)]`.

Establish `hγ : ∀ v, (g * κ⁻¹) v = g (XP v) + AP v - AP (g (XP v))`. Introduce `v`. Use `show g (κ.symm v) = _`. Rewrite using `[hκs, map_sub, hfix (B v) (by rw [hB]; exact XP_AP _), hB, hg v]`. Establish `hγl : ∀ v (l : Fin (n + c)), n ≤ l.1 → (g * κ⁻¹) v l = v l`.

Introduce `v l hl`. Rewrite using `[hγ]`. Simplify using `only [Pi.sub_apply, Pi.add_apply, projA_apply, if_neg (not_lt.mpr hl)]`. Expand and normalize the polynomial expressions, which then agree. Establish `hγfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → (g * κ⁻¹) w = w`.

Introduce `w hw`. Rewrite using `[hγ, hw]`. Simplify using `[projA_eq_self_of_projX_eq_zero hw]`. Establish `hU : PI.OneCosetSharp.Loc.R1cond k n c (g * κ⁻¹)`. Use `⟨fun i v hv => ?_, hγfix _ (lowProj_basisVec_of_le n le_rfl), fun i => ?_⟩` and prove the remaining obligations.

Rewrite `hv`, the goal using `[mem_Ufl]`. Introduce `l hl`. Rewrite using `[hγl v l (by omega)]`. Conclude with `hv l hl`. Rewrite using `[hγfix _ (lowProj_basisVec_of_le (n + i) (Nat.le_add_right n i)), sub_self]`.

Conclude with `Submodule.zero_mem _`. Apply the tactic sequence `have hentry : ∀ p p' (hp : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c), PI.OneCosetSharp.ent k₀ c n c n κ.toLinearMap p p' = (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p') + B (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p'))) …`. Introduce `p p' hp`. Simplify using `only [PI.OneCosetSharp.ent, PI.OneCosetSharp.Loc.atN, dif_pos hp, LinearEquiv.coe_coe, hκ]`. Establish `hBq : ∀ q (hq : q < n + c), B (PI.OneCosetSharp.Loc.eN k (n + c) q) ⟨q, hq⟩ = 0`.

Introduce `q hq`. Distinguish the cases in `h : q < n`. Rewrite using `[hB, projA_apply]`. Conclude with `if_pos h`. Rewrite using `[hB0 _ (lowProj_basisVec_of_le q (not_lt.mp h))]`.

Both sides reduce to the same expression. Use `⟨g * κ⁻¹, mem_flagUnipotent hU, κ, ⟨fun p' hp' => ?_, fun p p' hp hp' hne hent => ?_⟩, by simp⟩` and prove the remaining obligations. Establish `hq` using `fIdx_lt_add_of_lt_add (k₀ := k₀) (show p' < n + c by omega)`. Apply the tactic sequence `rw [hentry p' p' hq, Pi.add_apply, hBq _ hq, add_zero, eN_apply]`. Conclude with `if_pos rfl`.

Establish `hq` using `fIdx_lt_add_of_lt_add (k₀ := k₀) hp`. Establish `hqq : PI.OneCosetSharp.LocE.fIdx k₀ c n p ≠ PI.OneCosetSharp.LocE.fIdx k₀ c n p'` using `fun h => hne (fIdx_injOn_of_lt_add hkn hp hp' h)`. Apply the tactic sequence `rw [hentry p p' hq, Pi.add_apply, eN_apply, Fin.val_mk, if_neg hqq, zero_add] at hent`. Distinguish the cases in `hq'n : PI.OneCosetSharp.LocE.fIdx k₀ c n p' < n`. Rewrite `hent` using `[hB, lowProj_basisVec_of_lt _ hq'n]`.

Break down `lt_or_le_of_fIdx_lt hq'n with h | h` into its components or cases. Take `⟨v, hv⟩` from `hfree p' (by omega) (Or.inl h)`. Rewrite `hent` using `[hv, projA_inX]`. Conclude with `(hent rfl).elim`. Rewrite `hent` using `[projA_apply]`.

Establish `hpn : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p`. Assume the negation of the conclusion as `h'`. Conclude with `hent (if_pos (not_le.mp h'))`. Take `⟨hp1, hp2⟩` from `mem_block_of_le_fIdx hkn hp hpn`. Conclude with `allow_of_mem_block_of_le_right hcm hp1 hp2 h`.

Rewrite `hent` using `[hB0 _ (lowProj_basisVec_of_le _ (not_lt.mp hq'n))]`. Conclude with `(hent rfl).elim`.
-/
theorem gaStep : GaStep := by
  intro k _ k₀ m t j n' c n hadm g hga hfree
  obtain ⟨hk₀, -, hm4, hj1, hjm, hc, hn', hn⟩ := hadm
  generalize j * t = s at hn
  generalize (j - 1) * t = s' at hn'
  have hkn : k₀ ≤ n := by omega
  have hcm : c + 1 < m := by omega
  obtain ⟨B, hB⟩ : ∃ B : (Fin (n + c) → k) →ₗ[k] (Fin (n + c) → k),
      ∀ w, B w = AP (g (XP w)) :=
    ⟨AP ∘ₗ g.toLinearMap ∘ₗ XP, fun w => rfl⟩
  have hfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → g w = w :=
    fix_of_basis g hga
  have hB0 : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → B w = 0 := by
    intro w hw
    rw [hB, hw]
    simp
  have hBB : ∀ w, B (B w) = 0 := fun w => hB0 _ (by rw [hB]; exact XP_AP _)
  obtain ⟨κ, hκ, hκs⟩ : ∃ κ : (Fin (n + c) → k) ≃ₗ[k] (Fin (n + c) → k),
      (∀ w, κ w = w + B w) ∧ ∀ w, κ.symm w = w - B w := by
    refine ⟨LinearEquiv.ofLinear (LinearMap.id + B) (LinearMap.id - B) ?_ ?_, fun w => rfl, fun w => rfl⟩
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_sub, hBB, add_zero]
      abel
    · refine LinearMap.ext fun w => ?_
      simp only [LinearMap.comp_apply, LinearMap.add_apply, LinearMap.sub_apply, LinearMap.id_apply,
        map_add, hBB, sub_zero]
      abel
  have hg : ∀ v, g v = g (XP v) + AP v := by
    intro v
    conv_lhs => rw [← lowProj_add_highProj (n := n) (c := c) v]
    rw [map_add, hfix _ (XP_AP v)]
  have hγ : ∀ v, (g * κ⁻¹) v = g (XP v) + AP v - AP (g (XP v)) := by
    intro v
    show g (κ.symm v) = _
    rw [hκs, map_sub, hfix (B v) (by rw [hB]; exact XP_AP _), hB, hg v]
  have hγl : ∀ v (l : Fin (n + c)), n ≤ l.1 → (g * κ⁻¹) v l = v l := by
    intro v l hl
    rw [hγ]
    simp only [Pi.sub_apply, Pi.add_apply, projA_apply, if_neg (not_lt.mpr hl)]
    ring
  have hγfix : ∀ w, (XP : (Fin (n + c) → k) →ₗ[k] _) w = 0 → (g * κ⁻¹) w = w := by
    intro w hw
    rw [hγ, hw]
    simp [projA_eq_self_of_projX_eq_zero hw]
  have hU : PI.OneCosetSharp.Loc.R1cond k n c (g * κ⁻¹) := by
    refine ⟨fun i v hv => ?_, hγfix _ (lowProj_basisVec_of_le n le_rfl), fun i => ?_⟩
    · rw [mem_Ufl] at hv ⊢
      intro l hl
      rw [hγl v l (by omega)]
      exact hv l hl
    · rw [hγfix _ (lowProj_basisVec_of_le (n + i) (Nat.le_add_right n i)), sub_self]
      exact Submodule.zero_mem _
  have hentry : ∀ p p' (hp : PI.OneCosetSharp.LocE.fIdx k₀ c n p < n + c),
      PI.OneCosetSharp.ent k₀ c n c n κ.toLinearMap p p' =
        (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p') + B (PI.OneCosetSharp.Loc.eN k (n + c) (PI.OneCosetSharp.LocE.fIdx k₀ c n p'))) ⟨_, hp⟩ := by
    intro p p' hp
    simp only [PI.OneCosetSharp.ent, PI.OneCosetSharp.Loc.atN, dif_pos hp, LinearEquiv.coe_coe, hκ]
  have hBq : ∀ q (hq : q < n + c), B (PI.OneCosetSharp.Loc.eN k (n + c) q) ⟨q, hq⟩ = 0 := by
    intro q hq
    by_cases h : q < n
    · rw [hB, projA_apply]
      exact if_pos h
    · rw [hB0 _ (lowProj_basisVec_of_le q (not_lt.mp h))]
      rfl
  refine ⟨g * κ⁻¹, mem_flagUnipotent hU, κ, ⟨fun p' hp' => ?_, fun p p' hp hp' hne hent => ?_⟩, by simp⟩
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) (show p' < n + c by omega)
    rw [hentry p' p' hq, Pi.add_apply, hBq _ hq, add_zero, eN_apply]
    exact if_pos rfl
  · have hq := fIdx_lt_add_of_lt_add (k₀ := k₀) hp
    have hqq : PI.OneCosetSharp.LocE.fIdx k₀ c n p ≠ PI.OneCosetSharp.LocE.fIdx k₀ c n p' := fun h => hne (fIdx_injOn_of_lt_add hkn hp hp' h)
    rw [hentry p p' hq, Pi.add_apply, eN_apply, Fin.val_mk, if_neg hqq, zero_add] at hent
    by_cases hq'n : PI.OneCosetSharp.LocE.fIdx k₀ c n p' < n
    · rw [hB, lowProj_basisVec_of_lt _ hq'n] at hent
      rcases lt_or_le_of_fIdx_lt hq'n with h | h
      · obtain ⟨v, hv⟩ := hfree p' (by omega) (Or.inl h)
        rw [hv, projA_inX] at hent
        exact (hent rfl).elim
      · rw [projA_apply] at hent
        have hpn : n ≤ PI.OneCosetSharp.LocE.fIdx k₀ c n p := by
          by_contra h'
          exact hent (if_pos (not_le.mp h'))
        obtain ⟨hp1, hp2⟩ := mem_block_of_le_fIdx hkn hp hpn
        exact allow_of_mem_block_of_le_right hcm hp1 hp2 h
    · rw [hB0 _ (lowProj_basisVec_of_le _ (not_lt.mp hq'n))] at hent
      exact (hent rfl).elim

end PI.OneCosetSharp.W
