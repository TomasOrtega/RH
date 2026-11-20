import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint

namespace GlobalTheory.SumRefinement

/- English proof (translation)
Set `_ : Fintype F` to `Fintype.ofFinite F`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_, finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp), Finset.sum_product, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]`. Introduce `p hp`.

Simplify using `only [Function.mem_support] at hp`. Simplify using `[hp]`.
-/
theorem finsum_fst {X F : Type} [Finite F] (g : X → ℂ) (hg : (Function.support g).Finite) :
    ∑ᶠ p : X × F, g p.1 = (Nat.card F : ℂ) * ∑ᶠ x, g x := by
  classical
  let _ : Fintype F := Fintype.ofFinite F
  rw [finsum_eq_sum_of_support_subset (s := hg.toFinset ×ˢ Finset.univ) _ ?_,
    finsum_eq_sum_of_support_subset (s := hg.toFinset) _ (by simp),
    Finset.sum_product, Finset.mul_sum]
  · refine Finset.sum_congr rfl fun x _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Nat.card_eq_fintype_card]
  · intro p hp
    simp only [Function.mem_support] at hp
    simp [hp]

/- English proof (translation)
Take `⟨-, -, hinv, hfin⟩` from `h`. Use `set e := AddSubgroup.quotientEquivProdOfLE hCB with he`. Establish `hfst : ∀ x : W ⧸ C, (e x).1 = (QuotientAddGroup.mk (Quotient.out x) : W ⧸ B)`. Introduce `x`. Use `conv_lhs => rw [← Quotient.out_eq' x]`.

Both sides reduce to the same expression. Establish `hcong : ∀ u v : W, (QuotientAddGroup.mk u : W ⧸ B) = QuotientAddGroup.mk v → φ u = φ v`. Introduce `u v huv`. Establish `hb : -u + v ∈ B` using `QuotientAddGroup.eq.1 huv`. Establish `h1` using `hinv u (-u + v) hb`.

Rewrite `h1` using `[add_neg_cancel_left]`. Conclude with `h1.symm`. Establish `hval : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1)`. Introduce `x`. Rewrite using `[hfst]`.

Conclude with `hcong _ _ (QuotientAddGroup.out_eq' _).symm`. Establish `: Finite (↥B ⧸ C.addSubgroupOf B)` using `Nat.finite_of_card_ne_zero hi`. Establish `hg : (Function.support fun b : W ⧸ B => φ (Quotient.out b)).Finite`. Use `hfin.subset ?_` and prove the remaining obligations. Introduce `b hb`.

Conclude with `⟨Quotient.out b, hb, QuotientAddGroup.out_eq' b⟩`. Rewrite using `[← finsum_comp_equiv e.symm]`. Repeatedly rewrite using `[hval, Equiv.apply_symm_apply]`. Rewrite using `[finsum_fst (fun b : W ⧸ B => φ (Quotient.out b)) hg]`. Both sides reduce to the same expression.
-/
theorem sum_refine {W : Type} [AddCommGroup W] {A B C : AddSubgroup W} {φ : W → ℂ}
    (h : GlobalTheory.IdxInt.Fine A φ B) (hCB : C ≤ B) (hi : AddSubgroup.relIndex C B ≠ 0) :
    ∑ᶠ (c : W ⧸ C), φ (Quotient.out c) =
      (AddSubgroup.relIndex C B : ℂ) * ∑ᶠ (c : W ⧸ B), φ (Quotient.out c) := by
  classical
  obtain ⟨-, -, hinv, hfin⟩ := h
  set e := AddSubgroup.quotientEquivProdOfLE hCB with he
  have hfst : ∀ x : W ⧸ C, (e x).1 = (QuotientAddGroup.mk (Quotient.out x) : W ⧸ B) := by
    intro x
    conv_lhs => rw [← Quotient.out_eq' x]
    rfl
  have hcong : ∀ u v : W, (QuotientAddGroup.mk u : W ⧸ B) = QuotientAddGroup.mk v → φ u = φ v := by
    intro u v huv
    have hb : -u + v ∈ B := QuotientAddGroup.eq.1 huv
    have h1 := hinv u (-u + v) hb
    rw [add_neg_cancel_left] at h1
    exact h1.symm
  have hval : ∀ x : W ⧸ C, φ (Quotient.out x) = φ (Quotient.out (e x).1) := by
    intro x
    rw [hfst]
    exact hcong _ _ (QuotientAddGroup.out_eq' _).symm
  have : Finite (↥B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero hi
  have hg : (Function.support fun b : W ⧸ B => φ (Quotient.out b)).Finite := by
    refine hfin.subset ?_
    intro b hb
    exact ⟨Quotient.out b, hb, QuotientAddGroup.out_eq' b⟩
  rw [← finsum_comp_equiv e.symm]
  simp_rw [hval, Equiv.apply_symm_apply]
  rw [finsum_fst (fun b : W ⧸ B => φ (Quotient.out b)) hg]
  rfl

end GlobalTheory.SumRefinement
