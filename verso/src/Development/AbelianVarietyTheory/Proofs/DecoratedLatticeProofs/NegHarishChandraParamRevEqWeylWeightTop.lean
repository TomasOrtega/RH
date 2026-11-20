import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.TopFormula
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.L2.Forms
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Core.Rk.TopParam

def Dset (R : Ranks) (h : HCParam R) : Finset ℚ :=
  (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)) ∪
    Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)

/- English proof (translation)
Establish `hk : 1 ≤ R.k` using `by have := R.m_add_three_le_k; omega`. Unfold `sgHC Dset`. Simplify using `only [add_sub_cancel_left]`. Use `split_ifs with h1 h2 h3`. Simplify using the standard rewrite rules.

Apply `Finset.mem_union_left` to reduce the goal to its premises. Apply `Finset.mem_union_right` to reduce the goal to its premises. Simplify using the standard rewrite rules. Apply `Finset.mem_union_right` to reduce the goal to its premises. Simplify using `only [Finset.mem_biUnion, Finset.mem_univ, true_and, TPar.block, Finset.mem_image, Finset.mem_range]`.

Use `⟨⟨_, h2⟩, (i - (R.k - 1)) % (R.t + 1) - 1, ?_, ?_⟩` and prove the remaining obligations. Use `Nat.mod_lt (i - (R.k-1)) (show 0 < R.t + 1 by omega); omega` as an intermediate fact. Establish `: 1 ≤ (i - (R.k - 1)) % (R.t + 1)` using `Nat.pos_of_ne_zero h3`. Move the coercions through the operations in `[Nat.cast_sub this]`. Expand and normalize the polynomial expressions, which then agree.

It suffices to derive a contradiction. Apply `h2` to reduce the goal to its premises. Unfold `Ranks.N at hi`. Rewrite using `[Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]`. Generalize the expression as in `R.m * (R.t + 1) = P at hi`.

Use linear arithmetic over natural numbers and integers.
-/
theorem sgHC_sub_mem (R : Ranks) (h : HCParam R) (i : ℕ) (hi : i < R.N R.m - 1) :
    sgHC R h i - (R.m * (R.t + 1) / 2 : ℚ) ∈ Dset R h := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold sgHC Dset
  simp only [add_sub_cancel_left]
  split_ifs with h1 h2 h3
  · simp
  · apply Finset.mem_union_left; apply Finset.mem_union_right; simp
  · apply Finset.mem_union_right
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and, TPar.block, Finset.mem_image, Finset.mem_range]
    refine ⟨⟨_, h2⟩, (i - (R.k - 1)) % (R.t + 1) - 1, ?_, ?_⟩
    · have := Nat.mod_lt (i - (R.k-1)) (show 0 < R.t + 1 by omega); omega
    · have : 1 ≤ (i - (R.k - 1)) % (R.t + 1) := Nat.pos_of_ne_zero h3
      push_cast [Nat.cast_sub this]; ring
  · exfalso; apply h2
    unfold Ranks.N at hi
    rw [Nat.div_lt_iff_lt_mul (Nat.succ_pos _)]
    generalize R.m * (R.t + 1) = P at hi
    omega

/- English proof (translation)
Establish `hk : 1 ≤ R.k` using `by have := R.m_add_three_le_k; omega`. Unfold `Dset`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.card_union_le _ _).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Conclude with `Finset.card_image_le.trans (by simp)`.

Conclude with `Finset.card_image_le.trans (by simp)`. Use `(Finset.card_biUnion_le_card_mul _ _ R.t ?_).trans (by simp)` and prove the remaining obligations. Introduce `j _`. Conclude with `Finset.card_image_le.trans (by simp)`. Use `_ = R.N R.m - 1 := by`.

Unfold `Ranks.N`. Establish `: R.m * (R.t + 1) = R.m + R.m * R.t` using `by ring`. Rewrite using `[this]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_Dset_le (R : Ranks) (h : HCParam R) : (Dset R h).card ≤ R.N R.m - 1 := by
  have hk : 1 ≤ R.k := by have := R.m_add_three_le_k; omega
  unfold Dset
  calc _ ≤ (Finset.univ.image h.v ∪ Finset.univ.image (fun j => -h.b j)).card
          + (Finset.univ.biUnion (fun j => TPar.block (-h.e j) R.t)).card := Finset.card_union_le _ _
    _ ≤ ((R.k - 1) + R.m) + R.m * R.t := by
        gcongr
        · refine (Finset.card_union_le _ _).trans (add_le_add ?_ ?_)
          · exact Finset.card_image_le.trans (by simp)
          · exact Finset.card_image_le.trans (by simp)
        · refine (Finset.card_biUnion_le_card_mul _ _ R.t ?_).trans (by simp)
          intro j _
          exact Finset.card_image_le.trans (by simp)
    _ = R.N R.m - 1 := by
        unfold Ranks.N
        have : R.m * (R.t + 1) = R.m + R.m * R.t := by ring
        rw [this]; omega

end GlobalTheory.Core.Rk.TopParam

namespace GlobalTheory.Core.Rk.TopParam

/- English proof (translation)
Introduce `D u M hsg τ i`. Take `⟨hanti, q, hq, hS⟩` from `M.enum τ`. Establish `hdiv : ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℚ) = (D.R.m : ℚ) * (D.R.t + 1) / 2`. Take `⟨a, ha⟩` from `D.R.m_even`. Rewrite using `[Nat.cast_div (by rw [ha]; exact Dvd.intro (a * (D.R.t + 1)) (by ring)) (by norm_num)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hn : ((D.sp.X'.rank : ℕ) : ℚ) = ((D.R.N D.R.m - 1 : ℕ) : ℚ)` using `by rw [rankP D]`. Set `F : Fin D.sp.X'.rank → ℚ` to `fun i => sgHC D.R (D.hcW u τ) (Fin.cast (rankP D) i) - (D.R.m * (D.R.t + 1) / 2 : ℚ)`. Set `G : Fin D.sp.X'.rank → ℚ` to `fun i => -q (Fin.rev i)`.

Establish `hRHS : ∀ i : Fin D.sp.X'.rank, (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℚ) + rhoVec D.sp.X'.rank i = F i`. Introduce `i`. Establish `h1` using `hsg (Fin.cast (rankP D) i) τ`. Simplify using `only [sgT, shW, F]`. Rewrite using `[Int.cast_sub, h1, Int.cast_natCast, hdiv]`.

Simplify using `only [rhoVec, Fin.coe_cast]`. Rewrite using `[hn]`. Expand and normalize the polynomial expressions, which then agree. Establish `hFa : StrictAnti F`. Introduce `i j hij`.

Rewrite using `[← hRHS i, ← hRHS j]`. Establish `h1 : (sgT u τ).w (Fin.cast (rankP D) j) ≤ (sgT u τ).w (Fin.cast (rankP D) i)` using `(sgT u τ).anti (by rw [Fin.le_iff_val_le_val]; simp only [Fin.coe_cast]; exact hij.le)`. Establish `h2 : rhoVec D.sp.X'.rank j < rhoVec D.sp.X'.rank i`. Simplify using `only [rhoVec]; have : (i : ℚ) < j := by exact_mod_cast hij`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h1' : ((sgT u τ).w (Fin.cast (rankP D) j) : ℚ) ≤ (sgT u τ).w (Fin.cast (rankP D) i)` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hGa : StrictAnti G`. Introduce `i j hij`. Establish `h1` using `hanti (Fin.rev_lt_rev.mpr hij)`.

Rewrite `h1` using `[hq, hq]`. Establish `h1' : q (Fin.rev i) < q (Fin.rev j)` using `by exact_mod_cast h1`. Simplify using `only [G]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hFm : ∀ x, F x ∈ Dset D.R (D.hcW u τ)`.

Introduce `x`. Use `sgHC_sub_mem D.R (D.hcW u τ) (Fin.cast (rankP D) x) (Fin.cast (rankP D) x).isLt` as an intermediate fact. Simplify `this` using `[F]`. Establish `hGm : ∀ x, G x ∈ Dset D.R (D.hcW u τ)`. Introduce `x`.

Establish `hmem : (q (Fin.rev x), M.ε τ (Fin.rev x)) ∈ parB (Ptw D) D.R.m τ`. Rewrite using `[hS]`. Conclude with `Finset.mem_image_of_mem _ (Finset.mem_univ _)`. Establish `hodd : ¬ Odd D.R.m` using `Nat.not_odd_iff_even.mpr D.R.m_even`. Simplify using `only [parB, dualPar, TPar.Dpar, Finset.mem_image, hodd, if_false, add_zero] at hmem`.

Take `⟨⟨y1, y2⟩, ⟨⟨z1, z2⟩, hz, hzy⟩, hy⟩` from `hmem`. Simplify using `only [Prod.mk.injEq] at hzy hy`. Take `⟨rfl, rfl⟩` from `hzy`. Establish `hGx : G x = z1` using `by simp only [G]; rw [← hy.1]; ring`. Rewrite using `[hGx]`.

Simplify using `only [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_filter, Prod.mk.injEq, D.hcW_v, D.hcW_b, D.hcW_e] at hz ⊢`. Break down `hz with (⟨a, ha, -⟩ | ⟨a, ha, -⟩) | ⟨a, -, w, hw, hwz, -⟩` into its components or cases. Conclude with `Or.inl (Or.inl ⟨a, ha⟩)`. Conclude with `Or.inl (Or.inr ⟨a, ha⟩)`. Conclude with `Or.inr ⟨a, hwz ▸ hw⟩`.

Establish `hcard : (Dset D.R (D.hcW u τ)).card = D.sp.X'.rank`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[rankP D]`. Conclude with `card_Dset_le _ _`. Establish `hsub : Finset.univ.image F ⊆ Dset D.R (D.hcW u τ)`.

Introduce `y hy`. Take `⟨x, -, rfl⟩` from `Finset.mem_image.mp hy`. Conclude with `hFm x`. Use `Finset.card_le_card hsub` as an intermediate fact. Rewrite `this` using `[Finset.card_image_of_injective _ hFa.injective, Finset.card_univ, Fintype.card_fin]`. Then use the resulting hypothesis.

Establish `hFG : F ∘ Fin.rev = G ∘ Fin.rev`. Establish `e1` using `Finset.orderEmbOfFin_unique hcard (f := F ∘ Fin.rev) (fun x => hFm _) (fun a b hab => hFa (Fin.rev_lt_rev.mpr hab))`. Establish `e2` using `Finset.orderEmbOfFin_unique hcard (f := G ∘ Fin.rev) (fun x => hGm _) (fun a b hab => hGa (Fin.rev_lt_rev.mpr hab))`. Conclude with `e1.trans e2.symm`. Establish `hi` using `congrFun hFG (Fin.rev i)`.

Simplify using `only [Function.comp, Fin.rev_rev, G] at hi`. Rewrite using `[hq]`. Establish `key` using `congrArg (fun x : ℚ => (x : ℝ)) ((hRHS i).trans hi)`. Move the coercions through the operations in `at key`. Rewrite using `[key]`.
-/
theorem neg_lam_rev_eq : ∀ (D : D7) (u : D.what₂.Word) (M : DSModel D.sp.X' (parB (Ptw D) D.R.m)), (∀ (i : Fin (D.R.N D.R.m - 1)) τ, (((D.fm u).sg τ).w i : ℚ) = sgHC D.R (D.hcW u τ) i - rhoVec (D.R.N D.R.m - 1) i) → ∀ τ (i : Fin D.sp.X'.rank), -M.lam τ (Fin.rev i) = (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℝ) + ((rhoVec D.sp.X'.rank i : ℚ) : ℝ) := by
  intro D u M hsg τ i
  obtain ⟨hanti, q, hq, hS⟩ := M.enum τ
  have hdiv : ((D.R.m * (D.R.t + 1) / 2 : ℕ) : ℚ) = (D.R.m : ℚ) * (D.R.t + 1) / 2 := by
    obtain ⟨a, ha⟩ := D.R.m_even
    rw [Nat.cast_div (by rw [ha]; exact Dvd.intro (a * (D.R.t + 1)) (by ring)) (by norm_num)]
    push_cast; ring
  have hn : ((D.sp.X'.rank : ℕ) : ℚ) = ((D.R.N D.R.m - 1 : ℕ) : ℚ) := by rw [rankP D]
  let F : Fin D.sp.X'.rank → ℚ := fun i =>
    sgHC D.R (D.hcW u τ) (Fin.cast (rankP D) i) - (D.R.m * (D.R.t + 1) / 2 : ℚ)
  let G : Fin D.sp.X'.rank → ℚ := fun i => -q (Fin.rev i)
  have hRHS : ∀ i : Fin D.sp.X'.rank,
      (((sgT u τ).w (Fin.cast (rankP D) i) : ℤ) : ℚ) + rhoVec D.sp.X'.rank i = F i := by
    intro i
    have h1 := hsg (Fin.cast (rankP D) i) τ
    simp only [sgT, shW, F]
    rw [Int.cast_sub, h1, Int.cast_natCast, hdiv]
    simp only [rhoVec, Fin.coe_cast]
    rw [hn]; ring
  have hFa : StrictAnti F := by
    intro i j hij
    rw [← hRHS i, ← hRHS j]
    have h1 : (sgT u τ).w (Fin.cast (rankP D) j) ≤ (sgT u τ).w (Fin.cast (rankP D) i) :=
      (sgT u τ).anti (by rw [Fin.le_iff_val_le_val]; simp only [Fin.coe_cast]; exact hij.le)
    have h2 : rhoVec D.sp.X'.rank j < rhoVec D.sp.X'.rank i := by
      simp only [rhoVec]; have : (i : ℚ) < j := by exact_mod_cast hij
      linarith
    have h1' : ((sgT u τ).w (Fin.cast (rankP D) j) : ℚ) ≤ (sgT u τ).w (Fin.cast (rankP D) i) := by exact_mod_cast h1
    linarith
  have hGa : StrictAnti G := by
    intro i j hij
    have h1 := hanti (Fin.rev_lt_rev.mpr hij)
    rw [hq, hq] at h1
    have h1' : q (Fin.rev i) < q (Fin.rev j) := by exact_mod_cast h1
    simp only [G]; linarith
  have hFm : ∀ x, F x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have := sgHC_sub_mem D.R (D.hcW u τ) (Fin.cast (rankP D) x) (Fin.cast (rankP D) x).isLt
    simpa [F] using this
  have hGm : ∀ x, G x ∈ Dset D.R (D.hcW u τ) := by
    intro x
    have hmem : (q (Fin.rev x), M.ε τ (Fin.rev x)) ∈ parB (Ptw D) D.R.m τ := by
      rw [hS]; exact Finset.mem_image_of_mem _ (Finset.mem_univ _)
    have hodd : ¬ Odd D.R.m := Nat.not_odd_iff_even.mpr D.R.m_even
    simp only [parB, dualPar, TPar.Dpar, Finset.mem_image, hodd, if_false, add_zero] at hmem
    obtain ⟨⟨y1, y2⟩, ⟨⟨z1, z2⟩, hz, hzy⟩, hy⟩ := hmem
    simp only [Prod.mk.injEq] at hzy hy
    obtain ⟨rfl, rfl⟩ := hzy
    have hGx : G x = z1 := by simp only [G]; rw [← hy.1]; ring
    rw [hGx]
    simp only [Dset, Finset.mem_union, Finset.mem_image, Finset.mem_biUnion, Finset.mem_univ, true_and,
      Finset.mem_filter, Prod.mk.injEq, D.hcW_v, D.hcW_b, D.hcW_e] at hz ⊢
    rcases hz with (⟨a, ha, -⟩ | ⟨a, ha, -⟩) | ⟨a, -, w, hw, hwz, -⟩
    · exact Or.inl (Or.inl ⟨a, ha⟩)
    · exact Or.inl (Or.inr ⟨a, ha⟩)
    · exact Or.inr ⟨a, hwz ▸ hw⟩
  have hcard : (Dset D.R (D.hcW u τ)).card = D.sp.X'.rank := by
    apply le_antisymm
    · rw [rankP D]; exact card_Dset_le _ _
    · have hsub : Finset.univ.image F ⊆ Dset D.R (D.hcW u τ) := by
        intro y hy; obtain ⟨x, -, rfl⟩ := Finset.mem_image.mp hy; exact hFm x
      have := Finset.card_le_card hsub
      rwa [Finset.card_image_of_injective _ hFa.injective, Finset.card_univ, Fintype.card_fin] at this
  have hFG : F ∘ Fin.rev = G ∘ Fin.rev := by
    have e1 := Finset.orderEmbOfFin_unique hcard (f := F ∘ Fin.rev) (fun x => hFm _)
      (fun a b hab => hFa (Fin.rev_lt_rev.mpr hab))
    have e2 := Finset.orderEmbOfFin_unique hcard (f := G ∘ Fin.rev) (fun x => hGm _)
      (fun a b hab => hGa (Fin.rev_lt_rev.mpr hab))
    exact e1.trans e2.symm
  have hi := congrFun hFG (Fin.rev i)
  simp only [Function.comp, Fin.rev_rev, G] at hi
  rw [hq]
  have key := congrArg (fun x : ℚ => (x : ℝ)) ((hRHS i).trans hi)
  push_cast at key
  rw [key]

end GlobalTheory.Core.Rk.TopParam
