import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SumRefine

noncomputable section
open scoped Classical

namespace GlobalTheory.IdxInt.Model
open GlobalTheory.IdxInt

variable {W : Type} [AddCommGroup W]

/- English proof (translation)
Take `⟨b, hb⟩` from `QuotientAddGroup.mk_out_eq_add B w`. Rewrite using `[hb]`. Conclude with `h w b b.2`.
-/
lemma out_mk {φ : W → ℂ} {B : AddSubgroup W} (h : ∀ w, ∀ b ∈ B, φ (w + b) = φ w) (w : W) :
    φ (QuotientAddGroup.mk w : W ⧸ B).out = φ w := by
  obtain ⟨b, hb⟩ := QuotientAddGroup.mk_out_eq_add B w
  rw [hb]; exact h w b b.2

/- English proof (translation)
Use `h.2.2.2.subset ?_` and prove the remaining obligations. Introduce `c hc`. Conclude with `⟨c.out, hc, QuotientAddGroup.out_eq' c⟩`.
-/
lemma supp_fin {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    (Function.support fun c : W ⧸ B => φ c.out).Finite := by
  refine h.2.2.2.subset ?_
  intro c hc
  exact ⟨c.out, hc, QuotientAddGroup.out_eq' c⟩

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SumRefinement.sum_refine`. Consider the case `exact _root_.GlobalTheory.SumRefinement.sum_refine`. Consider the case `(apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SumRefinement.sum_refine <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SumRefinement.sum_refine ..)`.
-/
lemma sum_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex B ≠ 0) :
    (∑ᶠ c : W ⧸ C, φ c.out) = (C.relIndex B : ℂ) * ∑ᶠ c : W ⧸ B, φ c.out := by
  first
  | exact @_root_.GlobalTheory.SumRefinement.sum_refine
  | exact _root_.GlobalTheory.SumRefinement.sum_refine
  | (apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply _root_.GlobalTheory.SumRefinement.sum_refine <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SumRefinement.sum_refine <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SumRefinement.sum_refine ..)

/- English proof (translation)
Establish `hC : (B ⊓ B').relIndex A ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero h.2.1 h'.2.1`. Establish `m1` using `AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left h.1`. Establish `m2` using `AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A inf_le_right h'.1`. Establish `i1 : (B ⊓ B').relIndex B ≠ 0` using `fun z => hC (by rw [← m1, z, zero_mul])`. Establish `i2 : (B ⊓ B').relIndex B' ≠ 0` using `fun z => hC (by rw [← m2, z, zero_mul])`.

Establish `s1` using `sum_refine h inf_le_left i1`. Establish `s2` using `sum_refine h' inf_le_right i2`. Establish `c1 : (B.relIndex A : ℂ) ≠ 0` using `by exact_mod_cast h.2.1`. Establish `c2 : (B'.relIndex A : ℂ) ≠ 0` using `by exact_mod_cast h'.2.1`. Establish `c3 : (((B ⊓ B').relIndex B : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast i1`.

Establish `c4 : (((B ⊓ B').relIndex B' : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast i2`. Establish `m : (((B ⊓ B').relIndex B : ℕ) : ℂ) * (B.relIndex A : ℂ) = (((B ⊓ B').relIndex B' : ℕ) : ℂ) * (B'.relIndex A : ℂ)`. Conclude with `m1.trans m2.symm` after adjusting the coercions. Rewrite using `[← mul_div_mul_left _ _ c3, ← s1, ← mul_div_mul_left (∑ᶠ c : W ⧸ B', φ c.out) _ c4, ← s2, m]`.
-/
lemma ratio_eq {A B B' : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (h' : Fine A φ B') :
    (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) = (∑ᶠ c : W ⧸ B', φ c.out) / (B'.relIndex A : ℂ) := by
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero h.2.1 h'.2.1
  have m1 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B A inf_le_left h.1
  have m2 := AddSubgroup.relIndex_mul_relIndex (B ⊓ B') B' A inf_le_right h'.1
  have i1 : (B ⊓ B').relIndex B ≠ 0 := fun z => hC (by rw [← m1, z, zero_mul])
  have i2 : (B ⊓ B').relIndex B' ≠ 0 := fun z => hC (by rw [← m2, z, zero_mul])
  have s1 := sum_refine h inf_le_left i1
  have s2 := sum_refine h' inf_le_right i2
  have c1 : (B.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h.2.1
  have c2 : (B'.relIndex A : ℂ) ≠ 0 := by exact_mod_cast h'.2.1
  have c3 : (((B ⊓ B').relIndex B : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i1
  have c4 : (((B ⊓ B').relIndex B' : ℕ) : ℂ) ≠ 0 := by exact_mod_cast i2
  have m : (((B ⊓ B').relIndex B : ℕ) : ℂ) * (B.relIndex A : ℂ) = (((B ⊓ B').relIndex B' : ℕ) : ℂ) * (B'.relIndex A : ℂ) := by
    exact_mod_cast m1.trans m2.symm
  rw [← mul_div_mul_left _ _ c3, ← s1, ← mul_div_mul_left (∑ᶠ c : W ⧸ B', φ c.out) _ c4, ← s2, m]

/- English proof (translation)
Establish `hn : Nice A φ` using `⟨B, h⟩`. Rewrite using `[cint, dif_pos hn]`. Conclude with `ratio_eq hn.choose_spec h`.
-/
theorem cint_eq {A B : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) :
    cint A φ = (∑ᶠ c : W ⧸ B, φ c.out) / (B.relIndex A : ℂ) := by
  have hn : Nice A φ := ⟨B, h⟩
  rw [cint, dif_pos hn]
  exact ratio_eq hn.choose_spec h

/- English proof (translation)
Use `⟨hB, hi, ?_, ?_⟩` and prove the remaining obligations. Introduce `w b hb`. Simplify using `[ind, B.add_mem_cancel_right hb]`. Use `(Set.finite_singleton (0 : W ⧸ B)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Establish `: w ∈ B` using `by simpa [ind] using hw`. Simplify using `using this`.
-/
lemma fine_ind {A B : AddSubgroup W} (hB : B ≤ A) (hi : B.relIndex A ≠ 0) :
    Fine A (ind (· ∈ B)) B := by
  refine ⟨hB, hi, ?_, ?_⟩
  · intro w b hb
    simp [ind, B.add_mem_cancel_right hb]
  · refine (Set.finite_singleton (0 : W ⧸ B)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    have : w ∈ B := by simpa [ind] using hw
    simpa using this

/- English proof (translation)
Rewrite using `[cint_eq (fine_ind hB hi)]`. Use `congr 1`. Rewrite using `[finsum_eq_single _ (0 : W ⧸ B)]`. Use `out_mk (fine_ind hB hi).2.2.1 0` as an intermediate fact. Simplify using `only [QuotientAddGroup.mk_zero] at this`.

Rewrite using `[this]`. Simplify using `[ind]`. Introduce `c hc`. Establish `: c.out ∉ B` using `fun hm => hc (by`. Rewrite using `[← QuotientAddGroup.out_eq' c]`.

Conclude with `(QuotientAddGroup.eq_zero_iff _).2 hm)`. Simplify using `[ind, this]`.
-/
theorem cint_ind {A B : AddSubgroup W} (hB : B ≤ A) (hi : B.relIndex A ≠ 0) :
    cint A (ind (· ∈ B)) = 1 / (B.relIndex A : ℂ) := by
  rw [cint_eq (fine_ind hB hi)]
  congr 1
  rw [finsum_eq_single _ (0 : W ⧸ B)]
  · have := out_mk (fine_ind hB hi).2.2.1 0
    simp only [QuotientAddGroup.mk_zero] at this
    rw [this]; simp [ind]
  · intro c hc
    have : c.out ∉ B := fun hm => hc (by
      rw [← QuotientAddGroup.out_eq' c]; exact (QuotientAddGroup.eq_zero_iff _).2 hm)
    simp [ind, this]

/- English proof (translation)
Rewrite using `[cint_ind le_rfl (by simp)]; simp`.
-/
theorem cint_self (A : AddSubgroup W) : cint A (ind (· ∈ A)) = 1 := by
  rw [cint_ind le_rfl (by simp)]; simp

/- English proof (translation)
Establish `: (AddSubgroup.zmultiples (2 : ℤ)).relIndex ⊤ = 2`. Rewrite using `[AddSubgroup.relIndex_top_right, Int.index_zmultiples]`. Both sides reduce to the same expression. Rewrite using `[cint_ind le_top (by rw [this]; norm_num), this]; norm_num`.
-/
theorem cint_even : cint (⊤ : AddSubgroup ℤ) (ind (· ∈ AddSubgroup.zmultiples (2 : ℤ))) = 1 / 2 := by
  have : (AddSubgroup.zmultiples (2 : ℤ)).relIndex ⊤ = 2 := by
    rw [AddSubgroup.relIndex_top_right, Int.index_zmultiples]; rfl
  rw [cint_ind le_top (by rw [this]; norm_num), this]; norm_num

/- English proof (translation)
Take `⟨B, hB⟩` from `h`. Establish `hB' : Fine A (fun w => φ (t + w)) B`. Use `⟨hB.1, hB.2.1, fun w b hb => by simp only [← add_assoc]; exact hB.2.2.1 _ b hb, ?_⟩` and prove the remaining obligations. Use `(hB.2.2.2.image (fun c => -(QuotientAddGroup.mk t : W ⧸ B) + c)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`.

Conclude with `⟨_, ⟨t + w, hw, rfl⟩, by simp⟩`. Rewrite using `[cint_eq hB, cint_eq hB']`. Use `congr 1`. Rewrite using `[← finsum_comp_equiv (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) (f := fun c : W ⧸ B => φ c.out)]`. Use `finsum_congr fun c => ?_` and prove the remaining obligations.

Establish `: (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) c = QuotientAddGroup.mk (t + c.out)`. Simplify using the standard rewrite rules. Rewrite using `[this, out_mk hB.2.2.1]`.
-/
theorem cint_translate {A : AddSubgroup W} {φ : W → ℂ} (h : Nice A φ) (t : W) :
    cint A (fun w => φ (t + w)) = cint A φ := by
  obtain ⟨B, hB⟩ := h
  have hB' : Fine A (fun w => φ (t + w)) B := by
    refine ⟨hB.1, hB.2.1, fun w b hb => by simp only [← add_assoc]; exact hB.2.2.1 _ b hb, ?_⟩
    refine (hB.2.2.2.image (fun c => -(QuotientAddGroup.mk t : W ⧸ B) + c)).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    exact ⟨_, ⟨t + w, hw, rfl⟩, by simp⟩
  rw [cint_eq hB, cint_eq hB']
  congr 1
  rw [← finsum_comp_equiv (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) (f := fun c : W ⧸ B => φ c.out)]
  refine finsum_congr fun c => ?_
  have : (Equiv.addLeft (QuotientAddGroup.mk t : W ⧸ B)) c = QuotientAddGroup.mk (t + c.out) := by
    simp
  rw [this, out_mk hB.2.2.1]

/- English proof (translation)
Establish `m1` using `AddSubgroup.relIndex_mul_relIndex C B A hC h.1`. Establish `i1 : C.relIndex B ≠ 0` using `fun z => hi (by rw [← m1, z, zero_mul])`. Use `haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero i1`. Use `⟨hC.trans h.1, hi, fun w b hb => h.2.2.1 w b (hC hb), ?_⟩` and prove the remaining obligations. Set `e` to `AddSubgroup.quotientEquivProdOfLE hC`.

Use `((h.2.2.2.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage e.injective.injOn).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Conclude with `⟨⟨w, hw, rfl⟩, trivial⟩`.
-/
lemma fine_refine {A B C : AddSubgroup W} {φ : W → ℂ} (h : Fine A φ B) (hC : C ≤ B)
    (hi : C.relIndex A ≠ 0) : Fine A φ C := by
  have m1 := AddSubgroup.relIndex_mul_relIndex C B A hC h.1
  have i1 : C.relIndex B ≠ 0 := fun z => hi (by rw [← m1, z, zero_mul])
  haveI : Finite (B ⧸ C.addSubgroupOf B) := Nat.finite_of_card_ne_zero i1
  refine ⟨hC.trans h.1, hi, fun w b hb => h.2.2.1 w b (hC hb), ?_⟩
  let e := AddSubgroup.quotientEquivProdOfLE hC
  refine ((h.2.2.2.prod (Set.finite_univ (α := B ⧸ C.addSubgroupOf B))).preimage
    e.injective.injOn).subset ?_
  rintro _ ⟨w, hw, rfl⟩
  exact ⟨⟨w, hw, rfl⟩, trivial⟩

/- English proof (translation)
Take `⟨B, hB⟩` from `h`. Take `⟨B', hB'⟩` from `h'`. Establish `hC : (B ⊓ B').relIndex A ≠ 0` using `AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1`. Establish `f1` using `fine_refine hB inf_le_left hC`. Establish `f2` using `fine_refine hB' inf_le_right hC`.

Establish `f3 : Fine A (φ + ψ) (B ⊓ B')`. Use `⟨f1.1, hC, fun w b hb => by simp [f1.2.2.1 w b hb, f2.2.2.1 w b hb], ?_⟩` and prove the remaining obligations. Use `(f1.2.2.2.union f2.2.2.2).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Break down `Function.support_add φ ψ hw with h | h` into its components or cases.

Conclude with `Or.inl ⟨w, h, rfl⟩`. Conclude with `Or.inr ⟨w, h, rfl⟩`. Use `⟨⟨_, f3⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[cint_eq f1, cint_eq f2, cint_eq f3, ← add_div, ← finsum_add_distrib (supp_fin f1) (supp_fin f2)]`. Both sides reduce to the same expression.
-/
theorem cint_add {A : AddSubgroup W} {φ ψ : W → ℂ} (h : Nice A φ) (h' : Nice A ψ) :
    Nice A (φ + ψ) ∧ cint A (φ + ψ) = cint A φ + cint A ψ := by
  obtain ⟨B, hB⟩ := h
  obtain ⟨B', hB'⟩ := h'
  have hC : (B ⊓ B').relIndex A ≠ 0 := AddSubgroup.relIndex_inf_ne_zero hB.2.1 hB'.2.1
  have f1 := fine_refine hB inf_le_left hC
  have f2 := fine_refine hB' inf_le_right hC
  have f3 : Fine A (φ + ψ) (B ⊓ B') := by
    refine ⟨f1.1, hC, fun w b hb => by simp [f1.2.2.1 w b hb, f2.2.2.1 w b hb], ?_⟩
    refine (f1.2.2.2.union f2.2.2.2).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    rcases Function.support_add φ ψ hw with h | h
    · exact Or.inl ⟨w, h, rfl⟩
    · exact Or.inr ⟨w, h, rfl⟩
  refine ⟨⟨_, f3⟩, ?_⟩
  rw [cint_eq f1, cint_eq f2, cint_eq f3, ← add_div, ← finsum_add_distrib (supp_fin f1) (supp_fin f2)]
  rfl

end GlobalTheory.IdxInt.Model
