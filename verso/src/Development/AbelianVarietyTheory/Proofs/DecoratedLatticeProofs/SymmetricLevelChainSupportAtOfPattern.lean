import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.AllPositions
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SymmetricChainSupportOneOfPattern
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsRootExchangeParabolicMulPrincipalCongruencStatement

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx GlobalTheory.StepData GlobalTheory.SymChain GlobalTheory.SymSupport

noncomputable section
namespace GlobalTheory.SymSupportP

section Local
variable {k : Type*} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
  {n : Type*} [Fintype n] [DecidableEq n] {c : ℕ}

/- English proof (translation)
Set `P : n ⊕ Fin c → n ⊕ Fin c → Prop` to `fun r s => Sum.elim (fun s => T s ∧ ∃ l : Fin c, r = .inr l ∧ p ≤ l.val + 1) (fun i => lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r) s`. Set `M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k` to `Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s`. Take `⟨u, hu, e⟩` from `exists_mul_KOne hg (M := M) (fun r s => by`. Distinguish the cases in `hP : P r s`. Rewrite using `[Matrix.sub_apply, Valuation.map_sub_swap, show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]`.

Break down `s with s | i` into its components or cases. Take `⟨hT, l, rfl, hl⟩` from `hP`. Simplify using `using h1 l s hT hl`. Conclude with `h2 r i hP`. Rewrite using `[Matrix.sub_apply, show M r s = g.val r s from if_neg hP]`.

Use the proof step `simp)`. Establish `hM : IntM M` using `e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))`. Establish `m2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r → M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)` using `fun r i hl => if_pos hl`. Establish `m1 : ∀ (l : Fin c) s, T s → p ≤ l.val + 1 → M (.inr l) (.inl s) = 0` using `fun l s hT hl => by`. Establish `: M (.inr l) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr l) (.inl s)` using `if_pos ⟨hT, l, rfl, hl⟩`.

Simplify using `using this`. Establish `hd : M.toBlocks₂₂.det = 1`. Rewrite using `[det_of_upperTriangular, Finset.prod_eq_one]`. Introduce `i _`. Simplify `m2 (.inr i) i le_rfl` using `[toBlocks₂₂]`.

Introduce `i j hij`. Use `m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)` as an intermediate fact. Simplify `this` using `[toBlocks₂₂, (show j < i from hij).ne']`. Take `⟨V, hV, hUV⟩` from `exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd`. Set `D : Matrix (Fin c) n k` to `Matrix.of fun l s => if T s then 0 else -(V * M.toBlocks₂₁) l s`.

Establish `hVM : IntM (V * M.toBlocks₂₁)` using `hV.mul fun i j => hM _ _`. Use `⟨u, hu, D, fun i j => ?_, fun l s hT => if_pos hT, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hT : T j`. Simplify using `[D, hT, zero_mem]`. Simplify `neg_mem (hVM i j)` using `[D, hT]`.

Introduce `a b hl hab`. Rewrite using `[Units.val_mul, e]`. Express the relevant statement in the definitionally equal form `(M * (fromBlocks 1 0 D 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) a b = _`. Use `conv_lhs => rw [← fromBlocks_toBlocks M]`. Rewrite using `[fromBlocks_multiply]`.

Break down `b with x | i` into its components or cases. Break down `a with y | l` into its components or cases. Simplify using `at hab`. Establish `hl' : p ≤ l.val + 1` using `by simpa [lev] using hl`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₁, Matrix.add_apply]`.

Distinguish the cases in `hT : T x`. Establish `: (M.toBlocks₂₂ * D) l x = 0`. Rewrite using `[Matrix.mul_apply]`. Conclude with `Finset.sum_eq_zero fun m _ => by simp [D, hT]`. Rewrite using `[this, add_zero]`.

Simplify `m1 l x hT hl'` using `[toBlocks₂₁]`. Establish `: (M.toBlocks₂₂ * D) l x = (M.toBlocks₂₂ * (-(V * M.toBlocks₂₁))) l x`. Simplify using `only [Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun m _ => by simp [D, hT]`. Rewrite using `[this, Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]`.

Simplify using the standard rewrite rules. Break down `a with y | l` into its components or cases. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₁₂]`. Simplify `m2 (.inl y) i hl` using `[toBlocks₁₂]`. Simplify using `only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₂]`.

Simplify `m2 (.inr l) i hl` using `[toBlocks₂₂]`.
-/
theorem exists_factor {g : GL (n ⊕ Fin c) k} (hg : g ∈ KO k _) (p : ℕ) (T : n → Prop)
    (h1 : ∀ l s, T s → p ≤ l.val + 1 → valuation k (g.val (.inr l) (.inl s)) < 1)
    (h2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      valuation k (g.val r (.inr i) - (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i)) < 1) :
    ∃ u ∈ KOne k (n ⊕ Fin c), ∃ D : Matrix (Fin c) n k, IntM D ∧ (∀ l s, T s → D l s = 0) ∧
      ∀ a b, lev p b ≤ lev p a → ¬ (a.isLeft = true ∧ b.isLeft = true) →
        (g * u * lowU D).val a b = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) a b := by
  classical
  let P : n ⊕ Fin c → n ⊕ Fin c → Prop := fun r s =>
    Sum.elim (fun s => T s ∧ ∃ l : Fin c, r = .inr l ∧ p ≤ l.val + 1)
      (fun i => lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r) s
  let M : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k :=
    Matrix.of fun r s => if P r s then (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s else g.val r s
  obtain ⟨u, hu, e⟩ := exists_mul_KOne hg (M := M) (fun r s => by
    by_cases hP : P r s
    · rw [Matrix.sub_apply, Valuation.map_sub_swap,
        show M r s = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r s from if_pos hP]
      rcases s with s | i
      · obtain ⟨hT, l, rfl, hl⟩ := hP
        simpa using h1 l s hT hl
      · exact h2 r i hP
    · rw [Matrix.sub_apply, show M r s = g.val r s from if_neg hP]; simp)
  have hM : IntM M := e ▸ intM_of_mem_KO (mul_mem hg (KOne_le_KO hu))
  have m2 : ∀ r i, lev p (Sum.inr i : n ⊕ Fin c) ≤ lev p r →
      M r (.inr i) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) r (.inr i) :=
    fun r i hl => if_pos hl
  have m1 : ∀ (l : Fin c) s, T s → p ≤ l.val + 1 → M (.inr l) (.inl s) = 0 := fun l s hT hl => by
    have : M (.inr l) (.inl s) = (1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k) (.inr l) (.inl s) :=
      if_pos ⟨hT, l, rfl, hl⟩
    simpa using this
  have hd : M.toBlocks₂₂.det = 1 := by
    rw [det_of_upperTriangular, Finset.prod_eq_one]
    · intro i _
      simpa [toBlocks₂₂] using m2 (.inr i) i le_rfl
    · intro i j hij
      have := m2 (.inr i) j (by simpa [lev] using (show j < i from hij).le)
      simpa [toBlocks₂₂, (show j < i from hij).ne'] using this
  obtain ⟨V, hV, hUV⟩ := exists_int_inv (U := M.toBlocks₂₂) (fun i j => hM _ _) hd
  let D : Matrix (Fin c) n k := Matrix.of fun l s => if T s then 0 else -(V * M.toBlocks₂₁) l s
  have hVM : IntM (V * M.toBlocks₂₁) := hV.mul fun i j => hM _ _
  refine ⟨u, hu, D, fun i j => ?_, fun l s hT => if_pos hT, ?_⟩
  · by_cases hT : T j
    · simp [D, hT, zero_mem]
    · simpa [D, hT] using neg_mem (hVM i j)
  · intro a b hl hab
    rw [Units.val_mul, e]
    change (M * (fromBlocks 1 0 D 1 : Matrix (n ⊕ Fin c) (n ⊕ Fin c) k)) a b = _
    conv_lhs => rw [← fromBlocks_toBlocks M]
    rw [fromBlocks_multiply]
    rcases b with x | i
    · rcases a with y | l
      · simp at hab
      · have hl' : p ≤ l.val + 1 := by simpa [lev] using hl
        simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₁, Matrix.add_apply]
        by_cases hT : T x
        · have : (M.toBlocks₂₂ * D) l x = 0 := by
            rw [Matrix.mul_apply]
            exact Finset.sum_eq_zero fun m _ => by simp [D, hT]
          rw [this, add_zero]
          simpa [toBlocks₂₁] using m1 l x hT hl'
        · have : (M.toBlocks₂₂ * D) l x = (M.toBlocks₂₂ * (-(V * M.toBlocks₂₁))) l x := by
            simp only [Matrix.mul_apply]
            exact Finset.sum_congr rfl fun m _ => by simp [D, hT]
          rw [this, Matrix.mul_neg, ← Matrix.mul_assoc, hUV, Matrix.one_mul]
          simp
    · rcases a with y | l
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₁₂]
        simpa [toBlocks₁₂] using m2 (.inl y) i hl
      · simp only [Matrix.mul_zero, Matrix.mul_one, add_zero, fromBlocks_apply₂₂]
        simpa [toBlocks₂₂] using m2 (.inr l) i hl

end Local

section Main
variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `j c H p hp1 hpc h hh x₀ e hΦ`. Set `o` to `stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)`. Set `o'` to `stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)`. Set `B` to `(typeFrame S.ϖ o).bas`. Set `B'` to `(typeFrame S.ϖ o').bas`.

Establish `hG : B⁻¹ * h * B ∈ KO k _` using `mem_stabLat.1 hh`. Set `Z` to `(B⁻¹).val * affPt p x₀ e * B'.val`. Set `J` to `(S.P.iter t S.μ S.tame (j + 1)).reindex o`. Establish `hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1)) ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0`. Establish `e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt p x₀ e) * B'.val`.

Simplify using `only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]`. Rewrite using `[← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]`. Establish `e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o'` using `rfl`. Rewrite using `[e2, e1]`. Conclude with `hΦ`.

Take `⟨κ₀, hκ, hc⟩` from `exists_match _ _ _ hG _ hΦ'`. Establish `hκ' : κ₀ ∈ J.J` using `hκ`. Establish `hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin c => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r * affPt p x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => (S.ϖ : k) ^ (i.val + 1)) s`. Introduce `r s`. Simplify using `only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]`.

Take `⟨u, hu, D, hD, hD0, hpat⟩` from `exists_factor (mul_mem hG (J.le_KO hκ')) p (fun s => ∃ i, s = .inl (.inl i)) (by`. Introduce and unpack `l _ ⟨i, rfl⟩ hl`. Establish `h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) - Z (.inr l) (.inl (.inl (.inl i)))) < 1` using `hc (.inr l) (.inl (.inl i))`. Establish `hf : ¬ (l.val + 1 < p)` using `by omega`. Rewrite using `[hZ, show affPt p x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free, hf], mul_zero, zero_mul, sub_zero] at h1) (by` and apply the resulting hypothesis.

Introduce `r i hl`. Establish `h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) - Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1` using `hc r (.inl (.inr ⟨i.val, by omega⟩))`. Rewrite `h1` using `[standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ]`. Use `h1 using 3` and compare the differences between its conclusion and the goal. Break down `r with r | r` into its components or cases.

Establish `: ¬ (p < i.val + 1)` using `by simpa [lev] using hl`. Simplify using `[affPt, basePt, Free, this]`. Establish `: ¬ r < i` using `by simpa [lev] using hl`. Distinguish the cases in `hri : r = i`. Substitute `hri` using the available equality.

Simplify using `[affPt, basePt, Free]`. Simplify using `[affPt, basePt, Free, this, hri, Fin.val_inj])`. Establish `hlowK : lowU D ∈ KO k _` using `mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩, intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩`. Establish `hlow : lowU D ∈ J.J`. Use `(hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩` and prove the remaining obligations.

Take `⟨h1, h2⟩` from `mem_KO.1 hlowK`. Conclude with `mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩`. Establish `: (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b)`. Take `⟨a, rfl⟩` from `o.symm.surjective a`. Take `⟨b, rfl⟩` from `o.symm.surjective b`.

Rewrite using `[o.apply_symm_apply, o.apply_symm_apply]`. Apply the tactic sequence `rcases a with a | a <;> rcases b with b | b`. Simplify using `[lowU, Matrix.one_apply]`. Simplify using `[lowU]`. Establish `a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩)` using `o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm`.

Break down `b with (b | b) | b` into its components or cases. Simplify `hD0 a _ ⟨b, rfl⟩` using `[lowU]`. Establish `a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + b.val, by omega⟩)` using `o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm`. Rewrite `hab` using `[a1, a3]`. Conclude with `absurd (show a.val < c + b.val by omega) hab`.

Establish `a6 : o.symm (.inl (.inr b)) = .inr b` using `o.symm_apply_eq.2 rfl`. Rewrite `hab` using `[a1, a6]`. Conclude with `absurd trivial hab`. Simplify using `[lowU, Matrix.one_apply]`. Rewrite using `[reGL_symm_val, submatrix_apply, this]`.

Simplify using `[Matrix.one_apply]`. Set `kap` to `κ₀ * u * lowU D`. Establish `hkap : kap ∈ J.J` using `mul_mem (mul_mem hκ' (J.KOne_le hu)) hlow`. Establish `hbas : (typeFrame S.ϖ (Equiv.refl (XIx (Fin κ) t (j + 1) ⊕ Fin c))).bas = B` using `Units.ext (by rw [typeFrame_val, typeFrame_val])`. Establish `hconj : B⁻¹ * (h * (B * kap * B⁻¹)) * B = B⁻¹ * h * B * κ₀ * u * lowU D`.

Simplify using `only [kap]`. Use `group`. Take `⟨r, hr, u', hu', eq⟩` from `GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence k S.ϖ _ c p (h * (B * kap * B⁻¹)) (by rw [hbas, hconj]`. Conclude with `mul_mem (mul_mem (mul_mem hG (J.le_KO hκ')) (KOne_le_KO hu)) hlowK)`. Use the proof step `(by`.

Introduce `a b hl hab`. Rewrite using `[hbas, hconj, hpat a b hl hab]`. Use the proof step `simp)`. Use `⟨r, hr, u' * (B * kap⁻¹ * B⁻¹), ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(reGL o).symm (B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J`.

Establish `: B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B = (B⁻¹ * u' * B) * kap⁻¹` using `by group`. Rewrite using `[this]`. Rewrite `hu'` using `[hbas]`. Conclude with `mul_mem (J.KOne_le hu') (inv_mem hkap)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem supportAt (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t] (hP : S.Pattern t) :
    S.SupportAt t := by
  intro j c H p hp1 hpc h hh x₀ e hΦ
  let o := stdOrd (Fin κ) t (l := s + 1) (j + 1) c (by omega)
  let o' := stdOrd (Fin κ) t (l := s + 1) j (c + 1) (by omega)
  let B := (typeFrame S.ϖ o).bas
  let B' := (typeFrame S.ϖ o').bas
  have hG : B⁻¹ * h * B ∈ KO k _ := mem_stabLat.1 hh
  let Z := (B⁻¹).val * affPt p x₀ e * B'.val
  let J := (S.P.iter t S.μ S.tame (j + 1)).reindex o
  have hΦ' : (S.P.iter t S.μ S.tame j).Phi t (S.μ (j + 1))
      ((((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o').submatrix ((ixSucc _ t j).trans o) id) ≠ 0 := by
    have e1 : ((B⁻¹ * h * B)⁻¹).val * Z = (B⁻¹).val * ((h⁻¹).val * affPt p x₀ e) * B'.val := by
      simp only [Z, _root_.mul_inv_rev, inv_inv, Units.val_mul, Matrix.mul_assoc]
      rw [← Matrix.mul_assoc B.val, Units.mul_inv, Matrix.one_mul]
    have e2 : ((B⁻¹ * h * B)⁻¹).val * Z.submatrix id o' = (((B⁻¹ * h * B)⁻¹).val * Z).submatrix id o' := rfl
    rw [e2, e1]
    exact hΦ
  obtain ⟨κ₀, hκ, hc⟩ := exists_match _ _ _ hG _ hΦ'
  have hκ' : κ₀ ∈ J.J := hκ
  have hZ : ∀ r s, Z r s = Sum.elim (fun _ => 1) (fun i : Fin c => ((S.ϖ : k) ^ (i.val + 1))⁻¹) r *
      affPt p x₀ e r s * Sum.elim (fun _ => 1) (fun i : Fin (c + 1) => (S.ϖ : k) ^ (i.val + 1)) s := by
    intro r s
    simp only [Z, B, B', typeFrame_val, typeFrame_inv_val, mul_diagonal, diagonal_mul]
  obtain ⟨u, hu, D, hD, hD0, hpat⟩ := exists_factor (mul_mem hG (J.le_KO hκ')) p
    (fun s => ∃ i, s = .inl (.inl i)) (by
      rintro l _ ⟨i, rfl⟩ hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val (.inr l) (.inl (.inl (.inl i))) -
        Z (.inr l) (.inl (.inl (.inl i)))) < 1 := hc (.inr l) (.inl (.inl i))
      have hf : ¬ (l.val + 1 < p) := by omega
      rwa [hZ, show affPt p x₀ e (.inr l) (.inl (.inl (.inl i))) = 0 by simp [affPt, basePt, Free, hf],
        mul_zero, zero_mul, sub_zero] at h1) (by
      intro r i hl
      have h1 : valuation k ((B⁻¹ * h * B * κ₀).val r (o (.inl (.inr ⟨i.val, by omega⟩))) -
        Z r (o' (.inl (.inr ⟨i.castSucc.val, by simp; omega⟩)))) < 1 := hc r (.inl (.inr ⟨i.val, by omega⟩))
      rw [standardOrderExtendedBasis_apply_low_block, standardOrderExtendedBasis_apply_low_block, hZ] at h1
      convert h1 using 3
      rcases r with r | r
      · have : ¬ (p < i.val + 1) := by simpa [lev] using hl
        simp [affPt, basePt, Free, this]
      · have : ¬ r < i := by simpa [lev] using hl
        by_cases hri : r = i
        · subst hri; simp [affPt, basePt, Free]
        · simp [affPt, basePt, Free, this, hri, Fin.val_inj])
  have hlowK : lowU D ∈ KO k _ := mem_KO.2 ⟨intM_fromBlocks.2 ⟨intM_one, intM_zero, hD, intM_one⟩,
      intM_fromBlocks.2 ⟨intM_one, intM_zero, hD.neg, intM_one⟩⟩
  have hlow : lowU D ∈ J.J := by
    refine (hP (j + 1) ((reGL o).symm (lowU D))).2 ⟨?_, fun a b hab => ?_⟩
    · obtain ⟨h1, h2⟩ := mem_KO.1 hlowK
      exact mem_KO.2 ⟨fun a b => h1 _ _, fun a b => by rw [← map_inv]; exact h2 _ _⟩
    · have : (lowU D).val (o a) (o b) = (1 : Matrix _ _ k) (o a) (o b) := by
        obtain ⟨a, rfl⟩ := o.symm.surjective a
        obtain ⟨b, rfl⟩ := o.symm.surjective b
        rw [o.apply_symm_apply, o.apply_symm_apply]
        rcases a with a | a <;> rcases b with b | b
        · simp [lowU, Matrix.one_apply]
        · simp [lowU]
        · have a1 : o.symm (.inr a) = .inl (.inr ⟨a.val, by omega⟩) :=
            o.symm_apply_eq.2 (standardOrderExtendedBasis_apply_low_block _ t _ _ _ a).symm
          rcases b with (b | b) | b
          · simpa [lowU] using hD0 a _ ⟨b, rfl⟩
          · have a3 : o.symm (.inl (.inl (.inr b))) = .inl (.inr ⟨c + b.val, by omega⟩) :=
              o.symm_apply_eq.2 (stdOrd_f _ t _ _ _ b).symm
            rw [a1, a3] at hab
            exact absurd (show a.val < c + b.val by omega) hab
          · have a6 : o.symm (.inl (.inr b)) = .inr b := o.symm_apply_eq.2 rfl
            rw [a1, a6] at hab
            exact absurd trivial hab
        · simp [lowU, Matrix.one_apply]
      rw [reGL_symm_val, submatrix_apply, this]
      simp [Matrix.one_apply]
  let kap := κ₀ * u * lowU D
  have hkap : kap ∈ J.J := mul_mem (mul_mem hκ' (J.KOne_le hu)) hlow
  have hbas : (typeFrame S.ϖ (Equiv.refl (XIx (Fin κ) t (j + 1) ⊕ Fin c))).bas = B :=
    Units.ext (by rw [typeFrame_val, typeFrame_val])
  have hconj : B⁻¹ * (h * (B * kap * B⁻¹)) * B = B⁻¹ * h * B * κ₀ * u * lowU D := by
    simp only [kap]; group
  obtain ⟨r, hr, u', hu', eq⟩ := GlobalTheory.T.exists_rootExchangeParabolic_mul_principalCongruence k S.ϖ _ c p (h * (B * kap * B⁻¹))
    (by rw [hbas, hconj]
        exact mul_mem (mul_mem (mul_mem hG (J.le_KO hκ')) (KOne_le_KO hu)) hlowK)
    (by
      intro a b hl hab
      rw [hbas, hconj, hpat a b hl hab]
      simp)
  refine ⟨r, hr, u' * (B * kap⁻¹ * B⁻¹), ?_, ?_⟩
  · change (reGL o).symm (B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B) ∈ (S.P.iter t S.μ S.tame (j + 1)).J
    have : B⁻¹ * (u' * (B * kap⁻¹ * B⁻¹)) * B = (B⁻¹ * u' * B) * kap⁻¹ := by group
    rw [this]
    rw [hbas] at hu'
    exact mul_mem (J.KOne_le hu') (inv_mem hkap)
  · calc h = (h * (B * kap * B⁻¹)) * (B * kap⁻¹ * B⁻¹) := by group
      _ = _ := by rw [eq]; group

end Main

/- English proof (translation)
Introduce `_ _ _ _ _ s κ S t _ _ hP` and use `supportAt s κ S t hP`.
-/
theorem supportAt_of_pattern : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (s κ : ℕ) (S : SymData k s κ) (t : Type) [Fintype t] [DecidableEq t],
    S.Pattern t → S.SupportAt t :=
  fun _ _ _ _ _ s κ S t _ _ hP => supportAt s κ S t hP

end GlobalTheory.SymSupportP
