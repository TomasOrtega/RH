import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.ArchimedeanGelfandKernels.LeftEquivariantFunctions.GelfandFlags.UnitaryMemGLs

noncomputable section

open Matrix Module

namespace PositivityTheory.RgBcC.VC.GFA

open PositivityTheory.RgBcC
open PositivityTheory.RgTw (Mat G)

variable {n : ℕ}

/- English proof (translation)
Use extensionality with `i`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]`.
-/
theorem mulVec_eq_sum (g : Mat n) (c : Fin n → ℂ) : g *ᵥ c = ∑ j, c j • (fun i => g i j) := by
  ext i
  simp [Matrix.mulVec, dotProduct, Finset.sum_apply, mul_comm]

/- English proof (translation)
Take `⟨b₁, hb₁, hspan₁, hli₁'⟩` from `exists_linearIndependent ℂ (W₁ : Set (Fin n → ℂ))`. Establish `hli₁ : LinearIndepOn ℂ id b₁` using `hli₁'`. Establish `hb₁₂ : b₁ ⊆ (W₂ : Set (Fin n → ℂ))` using `hb₁.trans hW`. Use `set b₂ := hli₁.extend hb₁₂ with hb₂def`. Establish `hli₂ : LinearIndepOn ℂ id b₂` using `hli₁.linearIndepOn_extend hb₁₂`.

Establish `hb₂W : b₂ ⊆ (W₂ : Set (Fin n → ℂ))` using `hli₁.extend_subset hb₁₂`. Establish `h12 : b₁ ⊆ b₂` using `hli₁.subset_extend hb₁₂`. Establish `hW₂s : (W₂ : Set (Fin n → ℂ)) ⊆ Submodule.span ℂ b₂` using `hli₁.subset_span_extend hb₁₂`. Use `set B := Module.Basis.extend hli₂ with hBdef`. Establish `h23 : b₂ ⊆ Set.range B` using `by rw [Module.Basis.range_extend]; exact hli₂.subset_extend _`.

Establish `: Finite (hli₂.extend (Set.subset_univ b₂))` using `Module.Finite.finite_basis B`. Use `haveI : Fintype (hli₂.extend (Set.subset_univ b₂)) := Fintype.ofFinite _`. Establish `hcard : Fintype.card (hli₂.extend (Set.subset_univ b₂)) = n`. Rewrite using `[← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]`. Use `set B' := B.reindex (Fintype.equivFinOfCardEq hcard) with hB'def`.

Establish `hrange : Set.range B' = Set.range B`. Rewrite using `[hB'def, Module.Basis.coe_reindex]`. Conclude with `(Fintype.equivFinOfCardEq hcard).symm.surjective.range_comp _`. Use `⟨Matrix.of fun i j => B' j i, fun j => if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← linearIndependent_cols_iff_isUnit]`.

Conclude with `B'.linearIndependent`. Apply the tactic sequence `intro j; dsimp only; split_ifs <;> omega`. Introduce `c`. Establish `e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c`. Rewrite using `[mulVec_eq_sum, Module.Basis.equivFun_symm_apply]`.

Both sides reduce to the same expression. Establish `hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j` using `fun j => by`. Establish `h0` using `congrFun (B'.equivFun.apply_symm_apply c) j`. Rewrite `h0` using `[Module.Basis.equivFun_apply]`. Then use the resulting hypothesis. Establish `hW₁ : W₁ = Submodule.span ℂ (B' '' {j | B' j ∈ b₁})`.

Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `v`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq]`. Prove the components needed by the constructor for the conclusion.

Introduce `hv`. Take `⟨j, hj⟩ : v ∈ Set.range B'` from `hrange ▸ h23 (h12 hv)`. Conclude with `⟨j, hj ▸ hv, hj⟩`. Introduce and unpack `⟨j, hj, rfl⟩`. Conclude with `hj`.

Rewrite using `[e, hW₁, Module.Basis.mem_span_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h j hj`. Assume the negation of the conclusion as `hc`. Establish `hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n))`.

Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff, hr]`. Conclude with `hc`. Establish `h' : B' j ∈ b₁` using `h hm`. Express the relevant statement in the definitionally equal form `(if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0 at hj`. Rewrite `hj` using `[if_pos h']`.

Conclude with `hj rfl`. Introduce `h j hj`. Rewrite `hj` using `[Finset.mem_coe, Finsupp.mem_support_iff, hr]`. Use `show B' j ∈ b₁`. Assume the negation of the conclusion as `hb`.

Use `hj (h j ?_)` and prove the remaining obligations. Use `show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0`. Apply the tactic sequence `rw [if_neg hb]; split_ifs <;> omega`. Introduce `c`. Establish `e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c`.

Rewrite using `[mulVec_eq_sum, Module.Basis.equivFun_symm_apply]`. Both sides reduce to the same expression. Establish `hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j` using `fun j => by`. Establish `h0` using `congrFun (B'.equivFun.apply_symm_apply c) j`. Rewrite `h0` using `[Module.Basis.equivFun_apply]`. Then use the resulting hypothesis.

Establish `hW₂ : W₂ = Submodule.span ℂ (B' '' {j | B' j ∈ b₂})`. Combine the equalities or inequalities in the displayed calculation. Use `congr 1`. Use extensionality with `v`. Simplify using `only [Set.mem_image, Set.mem_ofPred_eq]`.

Prove the components needed by the constructor for the conclusion. Introduce `hv`. Take `⟨j, hj⟩ : v ∈ Set.range B'` from `hrange ▸ h23 hv`. Conclude with `⟨j, hj ▸ hv, hj⟩`. Introduce and unpack `⟨j, hj, rfl⟩`.

Conclude with `hj`. Rewrite using `[e, hW₂, Module.Basis.mem_span_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h j hj`. Assume the negation of the conclusion as `hc`.

Establish `hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n))`. Rewrite using `[Finset.mem_coe, Finsupp.mem_support_iff, hr]`. Conclude with `hc`. Establish `h' : B' j ∈ b₂` using `h hm`. Express the relevant statement in the definitionally equal form `(if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2 at hj`.

Distinguish the cases in `h1 : B' j ∈ b₁`. Rewrite using `[if_pos h1] at hj; exact absurd hj (by decide)`. Rewrite using `[if_neg h1, if_pos h'] at hj; exact absurd hj (by decide)`. Introduce `h j hj`. Rewrite `hj` using `[Finset.mem_coe, Finsupp.mem_support_iff, hr]`.

Use `show B' j ∈ b₂`. Assume the negation of the conclusion as `hb`. Establish `hb1 : B' j ∉ b₁` using `fun h1 => hb (h12 h1)`. Use `hj (h j ?_)` and prove the remaining obligations. Use `show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2`.

Rewrite using `[if_neg hb1, if_neg hb]`.
-/
theorem adapted (W₁ W₂ : Submodule ℂ (Fin n → ℂ)) (hW : W₁ ≤ W₂) :
    ∃ (g : Mat n) (blk : Fin n → ℕ), IsUnit g ∧ (∀ j, blk j ≤ 2) ∧
      (∀ c, g *ᵥ c ∈ W₁ ↔ ∀ j, blk j ≠ 0 → c j = 0) ∧ (∀ c, g *ᵥ c ∈ W₂ ↔ ∀ j, blk j = 2 → c j = 0) := by
  classical
  obtain ⟨b₁, hb₁, hspan₁, hli₁'⟩ := exists_linearIndependent ℂ (W₁ : Set (Fin n → ℂ))
  have hli₁ : LinearIndepOn ℂ id b₁ := hli₁'
  have hb₁₂ : b₁ ⊆ (W₂ : Set (Fin n → ℂ)) := hb₁.trans hW
  set b₂ := hli₁.extend hb₁₂ with hb₂def
  have hli₂ : LinearIndepOn ℂ id b₂ := hli₁.linearIndepOn_extend hb₁₂
  have hb₂W : b₂ ⊆ (W₂ : Set (Fin n → ℂ)) := hli₁.extend_subset hb₁₂
  have h12 : b₁ ⊆ b₂ := hli₁.subset_extend hb₁₂
  have hW₂s : (W₂ : Set (Fin n → ℂ)) ⊆ Submodule.span ℂ b₂ := hli₁.subset_span_extend hb₁₂
  set B := Module.Basis.extend hli₂ with hBdef
  have h23 : b₂ ⊆ Set.range B := by rw [Module.Basis.range_extend]; exact hli₂.subset_extend _
  have : Finite (hli₂.extend (Set.subset_univ b₂)) := Module.Finite.finite_basis B
  haveI : Fintype (hli₂.extend (Set.subset_univ b₂)) := Fintype.ofFinite _
  have hcard : Fintype.card (hli₂.extend (Set.subset_univ b₂)) = n := by
    rw [← Module.finrank_eq_card_basis B, Module.finrank_fin_fun]
  set B' := B.reindex (Fintype.equivFinOfCardEq hcard) with hB'def
  have hrange : Set.range B' = Set.range B := by
    rw [hB'def, Module.Basis.coe_reindex]
    exact (Fintype.equivFinOfCardEq hcard).symm.surjective.range_comp _
  refine ⟨Matrix.of fun i j => B' j i, fun j => if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2, ?_, ?_, ?_, ?_⟩
  · rw [← linearIndependent_cols_iff_isUnit]
    exact B'.linearIndependent
  · intro j; dsimp only; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₁ : W₁ = Submodule.span ℂ (B' '' {j | B' j ∈ b₁}) := by
      calc W₁ = Submodule.span ℂ (W₁ : Set (Fin n → ℂ)) := (Submodule.span_eq W₁).symm
        _ = Submodule.span ℂ b₁ := hspan₁.symm
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 (h12 hv)
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₁, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₁ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0 at hj
      rw [if_pos h'] at hj
      exact hj rfl
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₁
      by_contra hb
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) ≠ 0
      rw [if_neg hb]; split_ifs <;> omega
  · intro c
    have e : (Matrix.of fun i j => B' j i) *ᵥ c = B'.equivFun.symm c := by
      rw [mulVec_eq_sum, Module.Basis.equivFun_symm_apply]; rfl
    have hr : ∀ j, B'.repr (B'.equivFun.symm c) j = c j := fun j => by
      have h0 := congrFun (B'.equivFun.apply_symm_apply c) j
      rwa [Module.Basis.equivFun_apply] at h0
    have hW₂ : W₂ = Submodule.span ℂ (B' '' {j | B' j ∈ b₂}) := by
      calc W₂ = Submodule.span ℂ b₂ :=
            le_antisymm (fun x hx => hW₂s hx) (Submodule.span_le.2 hb₂W)
        _ = _ := by
          congr 1
          ext v
          simp only [Set.mem_image, Set.mem_ofPred_eq]
          constructor
          · intro hv
            obtain ⟨j, hj⟩ : v ∈ Set.range B' := hrange ▸ h23 hv
            exact ⟨j, hj ▸ hv, hj⟩
          · rintro ⟨j, hj, rfl⟩; exact hj
    rw [e, hW₂, Module.Basis.mem_span_image]
    constructor
    · intro h j hj
      by_contra hc
      have hm : j ∈ ((B'.repr (B'.equivFun.symm c)).support : Set (Fin n)) := by
        rw [Finset.mem_coe, Finsupp.mem_support_iff, hr]; exact hc
      have h' : B' j ∈ b₂ := h hm
      change (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2 at hj
      by_cases h1 : B' j ∈ b₁
      · rw [if_pos h1] at hj; exact absurd hj (by decide)
      · rw [if_neg h1, if_pos h'] at hj; exact absurd hj (by decide)
    · intro h j hj
      rw [Finset.mem_coe, Finsupp.mem_support_iff, hr] at hj
      show B' j ∈ b₂
      by_contra hb
      have hb1 : B' j ∉ b₁ := fun h1 => hb (h12 h1)
      refine hj (h j ?_)
      show (if B' j ∈ b₁ then 0 else if B' j ∈ b₂ then 1 else 2) = 2
      rw [if_neg hb1, if_neg hb]

end PositivityTheory.RgBcC.VC.GFA
