import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ScaledBasisMemChainLattice

open MeasureTheory ValuativeRel Matrix
open scoped Pointwise
open GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.IndefiniteRowSideFullHecke.ExponentTerms GlobalTheory.RootEx.UnfoldShape

noncomputable section
namespace GlobalTheory.RootEx.UnfoldFlag

variable {k : Type} [Field k] [ValuativeRel k] {n : Type} [Fintype n] [DecidableEq n] {c : ℕ}

def flagMat (y : Fin c → (n ⊕ Fin c → k)) : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
  Matrix.of fun r s =>
    Sum.elim (fun s => (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (Sum.inl s)) (fun i => y i r) s

/- English proof (translation)
Use function extensionality and compare the values at `r`. Rewrite using `[inX_apply]`. Simplify using `only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]`. Use `congr 1`. Break down `r with r | l` into its components or cases.

Simplify using `[one_apply]`. Simplify using `[one_apply]`. Conclude with `Finset.sum_congr rfl fun i _ => mul_comm _ _`.
-/
theorem flagMat_mulVec (y : Fin c → (n ⊕ Fin c → k)) (v : n ⊕ Fin c → k) :
    flagMat y *ᵥ v = inX k n c (fun r => v (Sum.inl r)) + ∑ i, v (Sum.inr i) • y i := by
  funext r
  rw [inX_apply]
  simp only [mulVec, dotProduct, flagMat, of_apply, Fintype.sum_sum_type, Sum.elim_inl,
    Sum.elim_inr, Pi.add_apply, Finset.sum_apply, Pi.smul_apply, smul_eq_mul]
  congr 1
  · rcases r with r | l
    · simp [one_apply]
    · simp [one_apply]
  · exact Finset.sum_congr rfl fun i _ => mul_comm _ _

/- English proof (translation)
Introduce `r s hrs`. Break down `s with s | i` into its components or cases. Simplify using `[flagMat]`. Simplify using `only [flagMat, of_apply, Sum.elim_inr]`. Break down `r with r | l` into its components or cases.

Establish `hi : i.val = 0`. Simplify using `only [lev, Sum.elim_inl, Sum.elim_inr] at hrs`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h0 i hi r, one_apply_ne (by simp)]`. Simplify using `only [lev, Sum.elim_inr] at hrs`.

Break down `Nat.lt_or_eq_of_le hrs with h | h` into its components or cases. Rewrite using `[(mem_Yle.mp (hY i)) l h, one_apply_ne (fun e => by simp only [Sum.inr.injEq] at e; subst e; omega)]`. Establish `e : i = l` using `Fin.ext (by omega)`. Substitute `e` using the available equality. Rewrite using `[h1, one_apply_eq]`.
-/
theorem flagMat_uni {y : Fin c → (n ⊕ Fin c → k)} (hY : ∀ i, y i ∈ Yle k n c (i.val + 1))
    (h1 : ∀ i, y i (Sum.inr i) = 1) (h0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0) :
    Radical.Uni (lev 1) (flagMat y) := by
  intro r s hrs
  rcases s with s | i
  · simp [flagMat]
  · simp only [flagMat, of_apply, Sum.elim_inr]
    rcases r with r | l
    · have hi : i.val = 0 := by
        simp only [lev, Sum.elim_inl, Sum.elim_inr] at hrs
        omega
      rw [h0 i hi r, one_apply_ne (by simp)]
    · simp only [lev, Sum.elim_inr] at hrs
      rcases Nat.lt_or_eq_of_le hrs with h | h
      · rw [(mem_Yle.mp (hY i)) l h,
          one_apply_ne (fun e => by simp only [Sum.inr.injEq] at e; subst e; omega)]
      · have e : i = l := Fin.ext (by omega)
        subst e
        rw [h1, one_apply_eq]

/- English proof (translation)
Introduce `k _ _ _ _ n _ _ c hc ϖ hϖ Λ hΛ hfirst`. Establish `hpow : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0` using `fun i => pow_ne_zero _ hϖ`. Establish `hpick : ∀ i : Fin c, ∃ w : n ⊕ Fin c → k, w ∈ Λ ∧ w ∈ Yle k n c (i.val + 1) ∧ w (Sum.inr i) = (ϖ : k) ^ (i.val + 1) ∧ (i.val = 0 → ∀ r, w (Sum.inl r) = 0)`. Introduce `i`. Distinguish the cases in `hi : i.val = 0`.

Establish `e : i = ⟨0, hc⟩` using `Fin.ext hi`. Substitute `e` using the available equality. Use `⟨(ϖ : k) • aux k n (⟨0, hc⟩ : Fin c), hfirst, ?_, ?_, fun _ r => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_Yle]`. Introduce `l hl`.

Establish `hl0 : l ≠ ⟨0, hc⟩` using `fun e => by subst e; simp at hl`. Simplify using `[aux, hl0]`. Simplify using `[aux]`. Simplify using `[aux]`. Establish `hmem : (ϖ : k) ^ (i.val + 1) ∈ (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (R` using `𝒪[k]) (Sum.inr i)) := by`.

Rewrite using `[hΛ i]`. Conclude with `Submodule.mem_span_singleton_self _`. Take `⟨w, hw, hwi⟩` from `Submodule.mem_map.1 hmem`. Conclude with `⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hwi, fun h => absurd h hi⟩`. Use `choose w hwΛ hwY hw1 hw0 using hpick`.

Take `⟨y, hy⟩ : ∃ y : Fin c → (n ⊕ Fin c → k), ∀ i, y i = ((ϖ : k) ^ (i.val + 1))⁻¹ • w i` from `⟨_, fun _ => rfl⟩`. Establish `hyY : ∀ i, y i ∈ Yle k n c (i.val + 1)`. Introduce `i`. Rewrite using `[mem_Yle]`. Introduce `l hl`.

Rewrite using `[hy, Pi.smul_apply, (mem_Yle.mp (hwY i)) l hl, smul_zero]`. Establish `hy1 : ∀ i, y i (Sum.inr i) = 1`. Introduce `i`. Rewrite using `[hy, Pi.smul_apply, hw1, smul_eq_mul, inv_mul_cancel₀ (hpow i)]`. Establish `hy0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0`.

Introduce `i hi r`. Rewrite using `[hy, Pi.smul_apply, hw0 i hi r, smul_zero]`. Establish `hyw : ∀ i, (ϖ : k) ^ (i.val + 1) • y i = w i`. Introduce `i`. Rewrite using `[hy, smul_smul, mul_inv_cancel₀ (hpow i), one_smul]`.

Establish `hU` using `flagMat_uni hyY hy1 hy0`. Establish `hdet : IsUnit (flagMat y).det`. Rewrite using `[hU.det]`. Conclude with `isUnit_one`. Take `⟨g, hg⟩ : ∃ g : GL (n ⊕ Fin c) k, g.val = flagMat y` from `⟨Matrix.nonsingInvUnit _ hdet, rfl⟩`.

Establish `himg : act g (chainLat ϖ c (Λ.comap (inX k n c))) = Λ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `v hv`. Take `⟨u, hu, rfl⟩` from `mem_act.1 hv`. Take `⟨huL, hua⟩` from `mem_chainLat.1 hu`.

Rewrite using `[hg, flagMat_mulVec]`. Use `Λ.add_mem (Submodule.mem_comap.1 huL) (Λ.sum_mem fun i _ => ?_)` and prove the remaining obligations. Take `⟨a, ha⟩` from `hua i`. Rewrite using `[ha, mul_smul, hyw i]`. Conclude with `Λ.smul_mem a (hwΛ i)`.

Establish `hX : ∀ x ∈ Λ.comap (inX k n c), inX k n c x ∈ act g (chainLat ϖ c (Λ.comap (inX k n c)))`. Introduce `x hx`. Use `mem_act.2 ⟨inX k n c x, inX_mem_chainLat.2 hx, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, flagMat_mulVec]`. Simplify using `[inX_apply]`.

Establish `hW : ∀ i, w i ∈ act g (chainLat ϖ c (Λ.comap (inX k n c)))`. Introduce `i`. Use `mem_act.2 ⟨(ϖ : k) ^ (i.val + 1) • aux k n i, scaled_basis_mem_chainLattice ϖ _ i, ?_⟩` and prove the remaining obligations. Rewrite using `[hg, mulVec_smul, ← hyw i]`. Use `congr 1`.

Rewrite using `[aux, mulVec_single_one]`. Both sides reduce to the same expression. Establish `key : ∀ j, j ≤ c → ∀ v ∈ Λ, v ∈ Yle k n c j → v ∈ act g (chainLat ϖ c (Λ.comap (inX k n c)))`. Introduce `j`. Proceed by induction on `j with`.

Consider the case `zero`. Introduce `_ v hv hv0`. Establish `e : v = inX k n c (fun r => v (Sum.inl r))`. Use function extensionality and compare the values at `r`. Break down `r with r | l` into its components or cases.

Simplify using `[inX_apply]`. Simplify using `[inX_apply, (mem_Yle.mp hv0) l (by omega)]`. Rewrite using `[e]`. Apply `hX` to reduce the goal to its premises. Rewrite using `[Submodule.mem_comap, ← e]`.

Conclude with `hv`. Consider the case `succ j ih`. Introduce `hj v hv hvY`. Take `⟨i, hi⟩ : ∃ i : Fin c, i.val = j` from `⟨⟨j, by omega⟩, rfl⟩`. Substitute `hi` using the available equality.

Establish `hmem : v (Sum.inr i) ∈ Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}`. Rewrite using `[← hΛ i]`. Conclude with `Submodule.mem_map_of_mem (Submodule.mem_inf.2 ⟨hv, hvY⟩)`. Take `⟨a, ha⟩` from `Submodule.mem_span_singleton.1 hmem`. Establish `hrest : v - a • w i ∈ Yle k n c i.val`.

Rewrite using `[mem_Yle]`. Introduce `l hl`. Break down `eq_or_ne l i with rfl | hne` into its components or cases. Rewrite using `[Pi.sub_apply, Pi.smul_apply, hw1, ha, sub_self]`. Establish `hne' : l.val ≠ i.val` using `fun h => hne (Fin.ext h)`.

Establish `hl' : i.val + 1 < l.val + 1` using `by omega`. Rewrite using `[Pi.sub_apply, Pi.smul_apply, (mem_Yle.mp hvY) l hl', (mem_Yle.mp (hwY i)) l hl', smul_zero, sub_zero]`. Establish `h1` using `ih (by omega) (v - a • w i) (Λ.sub_mem hv (Λ.smul_mem a (hwΛ i))) hrest`. Establish `h2` using `Submodule.add_mem _ h1 (Submodule.smul_mem _ a (hW i))`. Rewrite `h2` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Introduce `v hv`. Conclude with `key c le_rfl v hv (mem_Yle.2 fun l hl => absurd hl (by have := l.isLt; omega))`. Use `⟨g⁻¹, (Radical.mem_N_iff g⁻¹).2 ?_, ?_⟩` and prove the remaining obligations. Conclude with `Radical.Uni.inv (g := g) (by rw [hg]; exact hU)`. Use `conv_lhs => rw [← himg]`.

Rewrite using `[← act_mul, inv_mul_cancel, act_one]`.
-/
theorem exists_unipotent : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n : Type) [Fintype n] [DecidableEq n] (c : ℕ) (hc : 1 ≤ c) (ϖ : 𝒪[k]), (ϖ : k) ≠ 0 → ∀ Λ : Submodule 𝒪[k] (n ⊕ Fin c → k), (∀ i : Fin c, (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (Sum.inr i)) = Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)}) → (ϖ : k) • aux k n (⟨0, hc⟩ : Fin c) ∈ Λ → ∃ u ∈ N k n c 1, act u Λ = chainLat ϖ c (Λ.comap (inX k n c)) := by
  intro k _ _ _ _ n _ _ c hc ϖ hϖ Λ hΛ hfirst
  have hpow : ∀ i : Fin c, (ϖ : k) ^ (i.val + 1) ≠ 0 := fun i => pow_ne_zero _ hϖ

  have hpick : ∀ i : Fin c, ∃ w : n ⊕ Fin c → k, w ∈ Λ ∧ w ∈ Yle k n c (i.val + 1) ∧
      w (Sum.inr i) = (ϖ : k) ^ (i.val + 1) ∧ (i.val = 0 → ∀ r, w (Sum.inl r) = 0) := by
    intro i
    by_cases hi : i.val = 0
    · have e : i = ⟨0, hc⟩ := Fin.ext hi
      subst e
      refine ⟨(ϖ : k) • aux k n (⟨0, hc⟩ : Fin c), hfirst, ?_, ?_, fun _ r => ?_⟩
      · rw [mem_Yle]
        intro l hl
        have hl0 : l ≠ ⟨0, hc⟩ := fun e => by subst e; simp at hl
        simp [aux, hl0]
      · simp [aux]
      · simp [aux]
    · have hmem : (ϖ : k) ^ (i.val + 1) ∈
          (Λ ⊓ Yle k n c (i.val + 1)).map (LinearMap.proj (R := 𝒪[k]) (Sum.inr i)) := by
        rw [hΛ i]
        exact Submodule.mem_span_singleton_self _
      obtain ⟨w, hw, hwi⟩ := Submodule.mem_map.1 hmem
      exact ⟨w, (Submodule.mem_inf.1 hw).1, (Submodule.mem_inf.1 hw).2, hwi, fun h => absurd h hi⟩
  choose w hwΛ hwY hw1 hw0 using hpick

  obtain ⟨y, hy⟩ : ∃ y : Fin c → (n ⊕ Fin c → k), ∀ i, y i = ((ϖ : k) ^ (i.val + 1))⁻¹ • w i :=
    ⟨_, fun _ => rfl⟩
  have hyY : ∀ i, y i ∈ Yle k n c (i.val + 1) := by
    intro i
    rw [mem_Yle]
    intro l hl
    rw [hy, Pi.smul_apply, (mem_Yle.mp (hwY i)) l hl, smul_zero]
  have hy1 : ∀ i, y i (Sum.inr i) = 1 := by
    intro i
    rw [hy, Pi.smul_apply, hw1, smul_eq_mul, inv_mul_cancel₀ (hpow i)]
  have hy0 : ∀ i : Fin c, i.val = 0 → ∀ r, y i (Sum.inl r) = 0 := by
    intro i hi r
    rw [hy, Pi.smul_apply, hw0 i hi r, smul_zero]
  have hyw : ∀ i, (ϖ : k) ^ (i.val + 1) • y i = w i := by
    intro i
    rw [hy, smul_smul, mul_inv_cancel₀ (hpow i), one_smul]
  have hU := flagMat_uni hyY hy1 hy0
  have hdet : IsUnit (flagMat y).det := by
    rw [hU.det]
    exact isUnit_one
  obtain ⟨g, hg⟩ : ∃ g : GL (n ⊕ Fin c) k, g.val = flagMat y := ⟨Matrix.nonsingInvUnit _ hdet, rfl⟩

  have himg : act g (chainLat ϖ c (Λ.comap (inX k n c))) = Λ := by
    apply le_antisymm
    · intro v hv
      obtain ⟨u, hu, rfl⟩ := mem_act.1 hv
      obtain ⟨huL, hua⟩ := mem_chainLat.1 hu
      rw [hg, flagMat_mulVec]
      refine Λ.add_mem (Submodule.mem_comap.1 huL) (Λ.sum_mem fun i _ => ?_)
      obtain ⟨a, ha⟩ := hua i
      rw [ha, mul_smul, hyw i]
      exact Λ.smul_mem a (hwΛ i)
    · have hX : ∀ x ∈ Λ.comap (inX k n c),
          inX k n c x ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro x hx
        refine mem_act.2 ⟨inX k n c x, inX_mem_chainLat.2 hx, ?_⟩
        rw [hg, flagMat_mulVec]
        simp [inX_apply]
      have hW : ∀ i, w i ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro i
        refine mem_act.2 ⟨(ϖ : k) ^ (i.val + 1) • aux k n i, scaled_basis_mem_chainLattice ϖ _ i, ?_⟩
        rw [hg, mulVec_smul, ← hyw i]
        congr 1
        rw [aux, mulVec_single_one]
        rfl

      have key : ∀ j, j ≤ c → ∀ v ∈ Λ, v ∈ Yle k n c j →
          v ∈ act g (chainLat ϖ c (Λ.comap (inX k n c))) := by
        intro j
        induction j with
        | zero =>
          intro _ v hv hv0
          have e : v = inX k n c (fun r => v (Sum.inl r)) := by
            funext r
            rcases r with r | l
            · simp [inX_apply]
            · simp [inX_apply, (mem_Yle.mp hv0) l (by omega)]
          rw [e]
          apply hX
          rw [Submodule.mem_comap, ← e]
          exact hv
        | succ j ih =>
          intro hj v hv hvY
          obtain ⟨i, hi⟩ : ∃ i : Fin c, i.val = j := ⟨⟨j, by omega⟩, rfl⟩
          subst hi
          have hmem : v (Sum.inr i) ∈ Submodule.span 𝒪[k] {(ϖ : k) ^ (i.val + 1)} := by
            rw [← hΛ i]
            exact Submodule.mem_map_of_mem (Submodule.mem_inf.2 ⟨hv, hvY⟩)
          obtain ⟨a, ha⟩ := Submodule.mem_span_singleton.1 hmem
          have hrest : v - a • w i ∈ Yle k n c i.val := by
            rw [mem_Yle]
            intro l hl
            rcases eq_or_ne l i with rfl | hne
            · rw [Pi.sub_apply, Pi.smul_apply, hw1, ha, sub_self]
            · have hne' : l.val ≠ i.val := fun h => hne (Fin.ext h)
              have hl' : i.val + 1 < l.val + 1 := by omega
              rw [Pi.sub_apply, Pi.smul_apply, (mem_Yle.mp hvY) l hl', (mem_Yle.mp (hwY i)) l hl',
                smul_zero, sub_zero]
          have h1 := ih (by omega) (v - a • w i) (Λ.sub_mem hv (Λ.smul_mem a (hwΛ i))) hrest
          have h2 := Submodule.add_mem _ h1 (Submodule.smul_mem _ a (hW i))
          rwa [sub_add_cancel] at h2
      intro v hv
      exact key c le_rfl v hv (mem_Yle.2 fun l hl => absurd hl (by have := l.isLt; omega))
  refine ⟨g⁻¹, (Radical.mem_N_iff g⁻¹).2 ?_, ?_⟩
  · exact Radical.Uni.inv (g := g) (by rw [hg]; exact hU)
  · conv_lhs => rw [← himg]
    rw [← act_mul, inv_mul_cancel, act_one]

end GlobalTheory.RootEx.UnfoldFlag
