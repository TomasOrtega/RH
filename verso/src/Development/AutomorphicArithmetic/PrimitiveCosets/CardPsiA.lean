import Development.AutomorphicArithmetic.PrimitiveCosets.CoreAtH
import Formalism.SharpRestriction.RamificationFrobenius.TotientGaloisClasses.FrameFacts
import Mathlib.Analysis.Fourier.FiniteAbelian.PontryaginDuality

open UpperTheory.Comparison₂ Deduction.CH Formalism Formalism.HC Formalism.D5 Formalism.RankGapBounds.WeightedMeanData Formalism.LFunctionChainParameters.WeightedSlopeBounds Formalism.LFunctionChainParameters.characterSumData Formalism.LFunctionChainParameters.ThickSetMeanBounds Formalism.LFunctionChainParameters.LErr
  Formalism.LFunctionChainParameters.LChain Formalism.LFunctionChainParameters.LHost

/- English proof (translation)
Establish `wd : ∀ x y, π x = π y → ψ x = ψ y`. Introduce `x y hxy`. Establish `h0 : π (x - y) = 0` using `by rw [map_sub, hxy, sub_self]`. Combine the equalities or inequalities in the displayed calculation. Set `s` to `Function.surjInv hπ`.

Establish `hs : ∀ q, π (s q) = q` using `Function.surjInv_eq hπ`. Use `⟨{ toFun := fun q => ψ (s q), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩` and prove the remaining obligations. Rewrite using `[wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]`. Introduce `a b`. Rewrite using `[← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])]`.

Use extensionality with `x`. Conclude with `wd _ _ (hs _)`.
-/
private theorem exists_comp_eq {G Q M : Type} [AddCommGroup G] [AddCommGroup Q] [CommGroupWithZero M] (π : G →+ Q)
    (hπ : Function.Surjective π) (ψ : AddChar G M) (h : ∀ x, π x = 0 → ψ x = 1) :
    ∃ χ : AddChar Q M, χ.compAddMonoidHom π = ψ := by
  have wd : ∀ x y, π x = π y → ψ x = ψ y := by
    intro x y hxy
    have h0 : π (x - y) = 0 := by rw [map_sub, hxy, sub_self]
    calc ψ x = ψ (y + (x - y)) := by rw [add_sub_cancel]
      _ = ψ y * ψ (x - y) := AddChar.map_add_eq_mul ψ _ _
      _ = ψ y := by rw [h _ h0, mul_one]
  let s := Function.surjInv hπ
  have hs : ∀ q, π (s q) = q := Function.surjInv_eq hπ
  refine ⟨{ toFun := fun q => ψ (s q), map_zero_eq_one' := ?_, map_add_eq_mul' := ?_ }, ?_⟩
  · rw [wd (s 0) 0 (by rw [hs, map_zero]), AddChar.map_zero_eq_one]
  · intro a b
    rw [← AddChar.map_add_eq_mul, wd (s (a + b)) (s a + s b) (by rw [hs, map_add, hs, hs])]
  · ext x
    exact wd _ _ (hs _)

/- English proof (translation)
Set `π : E0 × H →+ E0 × (H ⧸ A0)` to `(AddMonoidHom.id E0).prodMap (QuotientAddGroup.mk' A0)`. Establish `hπ : Function.Surjective π`. Introduce and unpack `⟨a, q⟩`. Take `⟨b, rfl⟩` from `QuotientAddGroup.mk'_surjective A0 q`. Conclude with `⟨(a, b), rfl⟩`.

Establish `inj : Function.Injective (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π)`. Introduce `χ1 χ2 h`. Use extensionality with `q`. Take `⟨x, rfl⟩` from `hπ q`. Conclude with `DFunLike.congr_fun h x`.

Establish `himg : PsiA A0 = Finset.univ.image (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π)`. Use extensionality with `ψ`. Simplify using `only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Use `exists_comp_eq π hπ ψ fun x hx => ?_` and prove the remaining obligations. Take `⟨a, b⟩` from `x`. Establish `ha : a = 0` using `congrArg Prod.fst hx`. Establish `hb : (QuotientAddGroup.mk' A0 b) = 0` using `congrArg Prod.snd hx`. Rewrite `hb` using `[QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff]`.

Substitute `ha` using the available equality. Conclude with `h b hb`. Introduce and unpack `⟨χ, rfl⟩ s hs show χ (π (0, s)) = 1`. Establish `: π (0, s) = 0`. Simplify using `[π, QuotientAddGroup.eq_zero_iff, hs]`.

Rewrite using `[this, AddChar.map_zero_eq_one]`. Rewrite using `[himg, Finset.card_image_of_injective _ inj, Finset.card_univ, AddChar.card_eq, Fintype.card_prod, AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]`. Simplify using `[E0]`.
-/
private theorem card_PsiA_index {H : Type} [AddCommGroup H] [Fintype H] [DecidableEq H] (A0 : AddSubgroup H) :
    (PsiA A0).card = 4 * A0.index := by
  classical
  let π : E0 × H →+ E0 × (H ⧸ A0) := (AddMonoidHom.id E0).prodMap (QuotientAddGroup.mk' A0)
  have hπ : Function.Surjective π := by
    rintro ⟨a, q⟩
    obtain ⟨b, rfl⟩ := QuotientAddGroup.mk'_surjective A0 q
    exact ⟨(a, b), rfl⟩
  have inj : Function.Injective (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    intro χ1 χ2 h
    ext q
    obtain ⟨x, rfl⟩ := hπ q
    exact DFunLike.congr_fun h x
  have himg : PsiA A0 = Finset.univ.image (fun χ : AddChar (E0 × (H ⧸ A0)) ℂ => χ.compAddMonoidHom π) := by
    ext ψ
    simp only [PsiA, Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image]
    constructor
    · intro h
      refine exists_comp_eq π hπ ψ fun x hx => ?_
      obtain ⟨a, b⟩ := x
      have ha : a = 0 := congrArg Prod.fst hx
      have hb : (QuotientAddGroup.mk' A0 b) = 0 := congrArg Prod.snd hx
      rw [QuotientAddGroup.mk'_apply, QuotientAddGroup.eq_zero_iff] at hb
      subst ha
      exact h b hb
    · rintro ⟨χ, rfl⟩ s hs
      show χ (π (0, s)) = 1
      have : π (0, s) = 0 := by
        simp [π, QuotientAddGroup.eq_zero_iff, hs]
      rw [this, AddChar.map_zero_eq_one]
  rw [himg, Finset.card_image_of_injective _ inj, Finset.card_univ, AddChar.card_eq, Fintype.card_prod,
    AddSubgroup.index_eq_card, Nat.card_eq_fintype_card]
  simp [E0]

/- English proof (translation)
Introduce `φ`. Rewrite using `[card_PsiA_index, φ.index_A0_eq_o]`.
-/
theorem UpperTheory.Comparison₂.card_PsiA :
    ∀ φ : Frame, (PsiA φ.A0).card = 4 * φ.o := by
  intro φ
  rw [card_PsiA_index, φ.index_A0_eq_o]
