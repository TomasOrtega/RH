import Mathlib
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.SelfDualCovolume

noncomputable section
open scoped BigOperators ComplexConjugate
open Classical

namespace Formalism.L2.PairingIndexBounds.Eq.Sq

open Formalism.L2.Th1.H

variable {V : Type} [AddCommGroup V] [Module ℂ V]

structure SplitTri (H : Sesq V) (α : V → ℂ) (Λ₁ Λ₂ Λ₃ A A' : AddSubgroup V) : Prop where
  meet : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ₁ ∧ x ∈ Λ₂ ∧ x ∈ Λ₃
  dec₁ : ∀ x ∈ Λ₁, ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ₁ ∧ b ∈ Λ₁ ∧ x = a + b
  dec₂ : ∀ x ∈ Λ₂, ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ₂ ∧ b ∈ Λ₂ ∧ x = a + b
  dec₃ : ∀ x ∈ Λ₃, ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ₃ ∧ b ∈ Λ₃ ∧ x = a + b
  isoA : ∀ z y, z ∈ A → y ∈ A → z ∈ Λ₃ → y ∈ Λ₂ → z + y ∈ Λ₁ → psiT H α z y = 1
  isoA' : ∀ z y, z ∈ A' → y ∈ A' → z ∈ Λ₃ → y ∈ Λ₂ → z + y ∈ Λ₁ → psiT H α z y = 1

/- English proof (translation)
Take `⟨b, hbA, b', hb'A', hbΛ, _, hx⟩` from `hd _ h`. Establish `h1 : u - b ∈ A` using `A.sub_mem hu hbA`. Establish `heq : u - b = b' - u'` using `by rw [sub_eq_sub_iff_add_eq_add, hx, add_comm]`. Establish `h2 : u - b ∈ A'` using `by rw [heq]; exact A'.sub_mem hb'A' hu'`. Establish `hub : u - b ∈ Λ` using `hm _ h1 h2`.

Establish `huΛ : u ∈ Λ`. Establish `: u = (u - b) + b` using `by abel`. Rewrite using `[this]`. Conclude with `Λ.add_mem hub hbΛ`. Use `⟨huΛ, ?_⟩` and prove the remaining obligations.

Establish `: u' = (u + u') - u` using `by abel`. Rewrite using `[this]`. Conclude with `Λ.sub_mem h huΛ`.
-/
theorem sep {Λ A A' : AddSubgroup V} (hm : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ)
    (hd : ∀ x ∈ Λ, ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ ∧ b ∈ Λ ∧ x = a + b)
    {u u' : V} (hu : u ∈ A) (hu' : u' ∈ A') (h : u + u' ∈ Λ) : u ∈ Λ ∧ u' ∈ Λ := by
  obtain ⟨b, hbA, b', hb'A', hbΛ, _, hx⟩ := hd _ h
  have h1 : u - b ∈ A := A.sub_mem hu hbA
  have heq : u - b = b' - u' := by rw [sub_eq_sub_iff_add_eq_add, hx, add_comm]
  have h2 : u - b ∈ A' := by rw [heq]; exact A'.sub_mem hb'A' hu'
  have hub : u - b ∈ Λ := hm _ h1 h2
  have huΛ : u ∈ Λ := by
    have : u = (u - b) + b := by abel
    rw [this]; exact Λ.add_mem hub hbΛ
  refine ⟨huΛ, ?_⟩
  have : u' = (u + u') - u := by abel
  rw [this]; exact Λ.sub_mem h huΛ

/- English proof (translation)
Establish `key : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', p.1 + p.2 - (q.1 + q.2) ∈ Λ → p = q`. Introduce `p hp q hq h`. Rewrite `hp`, `hq` using `[Finset.mem_product]`. Establish `hp1` using `AddSubgroup.mem_inf.1 (hR.1 _ hp.1)`. Establish `hq1` using `AddSubgroup.mem_inf.1 (hR.1 _ hq.1)`.

Establish `hp2` using `AddSubgroup.mem_inf.1 (hR'.1 _ hp.2)`. Establish `hq2` using `AddSubgroup.mem_inf.1 (hR'.1 _ hq.2)`. Establish `hs : (p.1 - q.1) + (p.2 - q.2) ∈ Λ`. Establish `: (p.1 - q.1) + (p.2 - q.2) = p.1 + p.2 - (q.1 + q.2)` using `by abel`. Rewrite using `[this]`.

Conclude with `h`. Take `⟨h1, h2⟩` from `sep hm hd (A.sub_mem hp1.2 hq1.2) (A'.sub_mem hp2.2 hq2.2) hs`. Conclude with `Prod.ext (hR.2.1 _ hp.1 _ hq.1 h1) (hR'.2.1 _ hp.2 _ hq.2 h2)`. Use `⟨⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hx`. Rewrite `hp` using `[Finset.mem_product]`. Conclude with `Λ'.add_mem (AddSubgroup.mem_inf.1 (hR.1 _ hp.1)).1 (AddSubgroup.mem_inf.1 (hR'.1 _ hp.2)).1`. Introduce `x hx y hy hxy`. Take `⟨p, hp, rfl⟩` from `Finset.mem_image.1 hx`.

Take `⟨q, hq, rfl⟩` from `Finset.mem_image.1 hy`. Rewrite using `[key p hp q hq hxy]`. Introduce `y hy`. Take `⟨a, haA, b, hbA, haΛ, hbΛ, rfl⟩` from `hd' y hy`. Take `⟨r, hr, har⟩` from `hR.2.2 a (AddSubgroup.mem_inf.2 ⟨haΛ, haA⟩)`.

Take `⟨r', hr', hbr⟩` from `hR'.2.2 b (AddSubgroup.mem_inf.2 ⟨hbΛ, hbA⟩)`. Use `⟨r + r', Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Establish `: a + b - (r + r') = (a - r) + (b - r')` using `by abel`. Rewrite using `[this]`. Conclude with `Λ.add_mem har hbr`.

Introduce `p hp q hq h`. Apply `key p hp q hq` to reduce the goal to its premises. Rewrite using `[h, sub_self]`. Conclude with `Λ.zero_mem`.
-/
theorem reps_sum {Λ Λ' A A' : AddSubgroup V} (hm : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ)
    (hd : ∀ x ∈ Λ, ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ ∧ b ∈ Λ ∧ x = a + b)
    (hd' : ∀ x ∈ Λ', ∃ a ∈ A, ∃ b ∈ A', a ∈ Λ' ∧ b ∈ Λ' ∧ x = a + b)
    {R R' : Finset V} (hR : IsReps Λ (Λ' ⊓ A) R) (hR' : IsReps Λ (Λ' ⊓ A') R') :
    IsReps Λ Λ' ((R ×ˢ R').image fun p => p.1 + p.2) ∧
      ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', p.1 + p.2 = q.1 + q.2 → p = q := by
  have key : ∀ p ∈ R ×ˢ R', ∀ q ∈ R ×ˢ R', p.1 + p.2 - (q.1 + q.2) ∈ Λ → p = q := by
    intro p hp q hq h
    rw [Finset.mem_product] at hp hq
    have hp1 := AddSubgroup.mem_inf.1 (hR.1 _ hp.1)
    have hq1 := AddSubgroup.mem_inf.1 (hR.1 _ hq.1)
    have hp2 := AddSubgroup.mem_inf.1 (hR'.1 _ hp.2)
    have hq2 := AddSubgroup.mem_inf.1 (hR'.1 _ hq.2)
    have hs : (p.1 - q.1) + (p.2 - q.2) ∈ Λ := by
      have : (p.1 - q.1) + (p.2 - q.2) = p.1 + p.2 - (q.1 + q.2) := by abel
      rw [this]; exact h
    obtain ⟨h1, h2⟩ := sep hm hd (A.sub_mem hp1.2 hq1.2) (A'.sub_mem hp2.2 hq2.2) hs
    exact Prod.ext (hR.2.1 _ hp.1 _ hq.1 h1) (hR'.2.1 _ hp.2 _ hq.2 h2)
  refine ⟨⟨?_, ?_, ?_⟩, ?_⟩
  · intro x hx
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    rw [Finset.mem_product] at hp
    exact Λ'.add_mem (AddSubgroup.mem_inf.1 (hR.1 _ hp.1)).1 (AddSubgroup.mem_inf.1 (hR'.1 _ hp.2)).1
  · intro x hx y hy hxy
    obtain ⟨p, hp, rfl⟩ := Finset.mem_image.1 hx
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hy
    rw [key p hp q hq hxy]
  · intro y hy
    obtain ⟨a, haA, b, hbA, haΛ, hbΛ, rfl⟩ := hd' y hy
    obtain ⟨r, hr, har⟩ := hR.2.2 a (AddSubgroup.mem_inf.2 ⟨haΛ, haA⟩)
    obtain ⟨r', hr', hbr⟩ := hR'.2.2 b (AddSubgroup.mem_inf.2 ⟨hbΛ, hbA⟩)
    refine ⟨r + r', Finset.mem_image.2 ⟨(r, r'), Finset.mem_product.2 ⟨hr, hr'⟩, rfl⟩, ?_⟩
    have : a + b - (r + r') = (a - r) + (b - r') := by abel
    rw [this]; exact Λ.add_mem har hbr
  · intro p hp q hq h
    apply key p hp q hq
    rw [h, sub_self]; exact Λ.zero_mem

/- English proof (translation)
Distinguish the cases in `h : ∀ x ∈ R, χ x = 1`. Use `⟨R.card, by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_congr rfl h]`. Simplify using the standard rewrite rules. Use `push Not at h`.

Take `⟨g, hg, hg1⟩` from `h`. Use `⟨0, le_refl _, ?_⟩` and prove the remaining obligations. Establish `hσ : ∀ x ∈ R, ∃ y ∈ R, (g + x) - y ∈ K` using `fun x hx => hc _ (G.add_mem (hRG g hg) (hRG x hx))`. Use `choose! σ hσR hσK using hσ`. Establish `hinj : ∀ x ∈ R, ∀ y ∈ R, σ x = σ y → x = y`.

Introduce `x hx y hy hxy`. Apply `hu x hx y hy` to reduce the goal to its premises. Use `K.sub_mem (hσK x hx) (hσK y hy)` as an intermediate fact. Rewrite `this` using `[hxy]`. Establish `e : g + x - σ y - (g + y - σ y) = x - y` using `by abel`.

Rewrite `this` using `[e]`. Conclude with `this`. Establish `himg : R.image σ = R`. Apply `Finset.eq_of_subset_of_card_le` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hy`. Conclude with `hσR x hx`. Rewrite using `[Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]`. Establish `hsum : χ g * ∑ x ∈ R, χ x = ∑ x ∈ R, χ x`. Rewrite using `[Finset.mul_sum]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun x hx => ?_` and prove the remaining obligations. Rewrite using `[← hmul]`. Establish `e : g + x = σ x + (g + x - σ x)` using `by abel`. Rewrite using `[e, hmul, hK _ (hσK x hx), mul_one]`.

Use `_ = ∑ x ∈ R.image σ, χ x := (Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)).symm`. Use `_ = ∑ x ∈ R, χ x := by rw [himg]`. Establish `h0 : (χ g - 1) * ∑ x ∈ R, χ x = 0` using `by rw [sub_mul, hsum, one_mul, sub_self]`. Break down `mul_eq_zero.1 h0 with h0 | h0` into its components or cases. Conclude with `absurd (sub_eq_zero.1 h0) hg1`.

Simplify using `using h0`.
-/
theorem char_sum {G K : AddSubgroup V} {R : Finset V} (hRG : ∀ x ∈ R, x ∈ G)
    (hu : ∀ x ∈ R, ∀ y ∈ R, x - y ∈ K → x = y) (hc : ∀ y ∈ G, ∃ x ∈ R, y - x ∈ K)
    (χ : V → ℂ) (hmul : ∀ x y, χ (x + y) = χ x * χ y) (hK : ∀ k ∈ K, χ k = 1) :
    ∃ r : ℝ, 0 ≤ r ∧ ∑ x ∈ R, χ x = r := by
  by_cases h : ∀ x ∈ R, χ x = 1
  · refine ⟨R.card, by positivity, ?_⟩
    rw [Finset.sum_congr rfl h]; simp
  · push Not at h
    obtain ⟨g, hg, hg1⟩ := h
    refine ⟨0, le_refl _, ?_⟩
    have hσ : ∀ x ∈ R, ∃ y ∈ R, (g + x) - y ∈ K := fun x hx => hc _ (G.add_mem (hRG g hg) (hRG x hx))
    choose! σ hσR hσK using hσ
    have hinj : ∀ x ∈ R, ∀ y ∈ R, σ x = σ y → x = y := by
      intro x hx y hy hxy
      apply hu x hx y hy
      have := K.sub_mem (hσK x hx) (hσK y hy)
      rw [hxy] at this
      have e : g + x - σ y - (g + y - σ y) = x - y := by abel
      rw [e] at this; exact this
    have himg : R.image σ = R := by
      apply Finset.eq_of_subset_of_card_le
      · intro y hy
        obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hy
        exact hσR x hx
      · rw [Finset.card_image_of_injOn (fun x hx y hy h => hinj x hx y hy h)]
    have hsum : χ g * ∑ x ∈ R, χ x = ∑ x ∈ R, χ x := by
      rw [Finset.mul_sum]
      calc ∑ x ∈ R, χ g * χ x = ∑ x ∈ R, χ (σ x) := by
            refine Finset.sum_congr rfl fun x hx => ?_
            rw [← hmul]
            have e : g + x = σ x + (g + x - σ x) := by abel
            rw [e, hmul, hK _ (hσK x hx), mul_one]
        _ = ∑ x ∈ R.image σ, χ x := (Finset.sum_image (fun x hx y hy h => hinj x hx y hy h)).symm
        _ = ∑ x ∈ R, χ x := by rw [himg]
    have h0 : (χ g - 1) * ∑ x ∈ R, χ x = 0 := by rw [sub_mul, hsum, one_mul, sub_self]
    rcases mul_eq_zero.1 h0 with h0 | h0
    · exact absurd (sub_eq_zero.1 h0) hg1
    · simpa using h0

/- English proof (translation)
Unfold `relIdx at *`. Establish `: Λ.IsFiniteRelIndex Λ'` using `AddSubgroup.isFiniteRelIndex_iff_relIndex_ne_zero.2 h`. Establish `: Λ.IsFiniteRelIndex P` using `AddSubgroup.isFiniteRelIndex_of_le_right Λ hle`. Conclude with `AddSubgroup.relIndex_ne_zero`.
-/
theorem relIdx_le_ne {Λ Λ' P : AddSubgroup V} (h : relIdx Λ Λ' ≠ 0) (hle : P ≤ Λ') : relIdx Λ P ≠ 0 := by
  unfold relIdx at *
  have : Λ.IsFiniteRelIndex Λ' := AddSubgroup.isFiniteRelIndex_iff_relIndex_ne_zero.2 h
  have : Λ.IsFiniteRelIndex P := AddSubgroup.isFiniteRelIndex_of_le_right Λ hle
  exact AddSubgroup.relIndex_ne_zero

def gGrp (Λ₁ Λ₂ Λ₃ A' : AddSubgroup V) : AddSubgroup V where
  carrier := {p | p ∈ Λ₃ ∧ p ∈ A' ∧ ∃ r, r ∈ Λ₂ ∧ r ∈ A' ∧ p + r ∈ Λ₁}
  zero_mem' := ⟨Λ₃.zero_mem, A'.zero_mem, 0, Λ₂.zero_mem, A'.zero_mem, by simp⟩
  add_mem' := by
    rintro a b ⟨ha3, haA, r, hr2, hrA, har⟩ ⟨hb3, hbA, s, hs2, hsA, hbs⟩
    refine ⟨Λ₃.add_mem ha3 hb3, A'.add_mem haA hbA, r + s, Λ₂.add_mem hr2 hs2, A'.add_mem hrA hsA, ?_⟩
    have e : a + b + (r + s) = (a + r) + (b + s) := by abel
    rw [e]; exact Λ₁.add_mem har hbs
  neg_mem' := by
    rintro a ⟨ha3, haA, r, hr2, hrA, har⟩
    refine ⟨Λ₃.neg_mem ha3, A'.neg_mem haA, -r, Λ₂.neg_mem hr2, A'.neg_mem hrA, ?_⟩
    have e : -a + -r = -(a + r) := by abel
    rw [e]; exact Λ₁.neg_mem har

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_gGrp {Λ₁ Λ₂ Λ₃ A' : AddSubgroup V} {p : V} :
    p ∈ gGrp Λ₁ Λ₂ Λ₃ A' ↔ p ∈ Λ₃ ∧ p ∈ A' ∧ ∃ r, r ∈ Λ₂ ∧ r ∈ A' ∧ p + r ∈ Λ₁ := Iff.rfl

/- English proof (translation)
Establish `: r ∈ dualLat H Λ` using `by rw [hsd]; exact hr`. Conclude with `this k hk`.
-/
theorem altE_int {H : Sesq V} {Λ : AddSubgroup V} (hsd : IsSelfDual H Λ) {r k : V} (hr : r ∈ Λ) (hk : k ∈ Λ) :
    ∃ m : ℤ, altE H r k = m := by
  have : r ∈ dualLat H Λ := by rw [hsd]; exact hr
  exact this k hk

/- English proof (translation)
Establish `: 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I)` using `by push_cast; ring`. Rewrite using `[this]`. Conclude with `Complex.exp_int_mul_two_pi_mul_I m`.
-/
theorem exp_int_one (m : ℤ) : Complex.exp (2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ)) = 1 := by
  have : 2 * (Real.pi : ℂ) * Complex.I * ((m : ℝ) : ℂ) = (m : ℂ) * (2 * Real.pi * Complex.I) := by push_cast; ring
  rw [this]; exact Complex.exp_int_mul_two_pi_mul_I m

/- English proof (translation)
Establish `hm₁ : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ₁` using `fun x h h' => (hS.meet x h h').1`. Establish `hm₂ : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ₂` using `fun x h h' => (hS.meet x h h').2.1`. Take `⟨R₂, hR₂⟩` from `(repsExist V Λ₁ (Λ₂ ⊓ A) (relIdx_le_ne hT.i₁₂ inf_le_left)).1`. Take `⟨R₂', hR₂'⟩` from `(repsExist V Λ₁ (Λ₂ ⊓ A') (relIdx_le_ne hT.i₁₂ inf_le_left)).1`. Take `⟨R₃, hR₃⟩` from `(repsExist V Λ₂ (Λ₃ ⊓ A) (relIdx_le_ne hT.i₂₃ inf_le_left)).1`.

Take `⟨R₃', hR₃'⟩` from `(repsExist V Λ₂ (Λ₃ ⊓ A') (relIdx_le_ne hT.i₂₃ inf_le_left)).1`. Take `⟨hS₂, hi₂⟩` from `reps_sum hm₁ hS.dec₁ hS.dec₂ hR₂ hR₂'`. Take `⟨hS₃, hi₃⟩` from `reps_sum hm₂ hS.dec₂ hS.dec₃ hR₃ hR₃'`. Use `⟨_, _, hS₂, hS₃, ?_⟩` and prove the remaining obligations. Establish `hc : ∀ s₁ ∈ R₂, ∃ t : ℝ, 0 ≤ t ∧ ∑ q₂ ∈ R₃', ∑ s₂ ∈ R₂', (if q₂ + s₂ ∈ Λ₁ then Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s₁ q₂ : ℂ)) else 0) = t`.

Introduce `s₁ hs₁`. Establish `hs₁2 : s₁ ∈ Λ₂` using `(AddSubgroup.mem_inf.1 (hR₂.1 _ hs₁)).1`. Use `set χ : V → ℂ := fun p => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s₁ p : ℂ)) with hχ`. Establish `inner : ∀ q₂ ∈ R₃', ∑ s₂ ∈ R₂', (if q₂ + s₂ ∈ Λ₁ then χ q₂ else 0) = if (∃ s₂ ∈ R₂', q₂ + s₂ ∈ Λ₁) then χ q₂ else 0`. Introduce `q₂ _`.

Distinguish the cases in `hex : ∃ s₂ ∈ R₂', q₂ + s₂ ∈ Λ₁`. Take `⟨s, hs, hqs⟩` from `hex`. Rewrite using `[if_pos ⟨s, hs, hqs⟩, Finset.sum_eq_single_of_mem s hs, if_pos hqs]`. Introduce `b hb hne`. Rewrite using `[if_neg]`.

Introduce `hqb`. Apply `hne` to reduce the goal to its premises. Apply `hR₂'.2.1 b hb s hs` to reduce the goal to its premises. Establish `e : b - s = (q₂ + b) - (q₂ + s)` using `by abel`. Rewrite using `[e]`.

Conclude with `Λ₁.sub_mem hqb hqs`. Rewrite using `[if_neg hex]`. Conclude with `Finset.sum_eq_zero fun b hb => if_neg fun h => hex ⟨b, hb, h⟩`. Rewrite using `[Finset.sum_congr rfl inner, ← Finset.sum_filter]`. Use `char_sum (G := gGrp Λ₁ Λ₂ Λ₃ A') (K := Λ₂) ?_ ?_ ?_ χ ?_ ?_` and prove the remaining obligations.

Introduce `x hx`. Take `⟨hxR, s, hs, hxs⟩` from `Finset.mem_filter.1 hx`. Establish `hx3` using `AddSubgroup.mem_inf.1 (hR₃'.1 _ hxR)`. Establish `hs2` using `AddSubgroup.mem_inf.1 (hR₂'.1 _ hs)`. Conclude with `⟨hx3.1, hx3.2, s, hs2.1, hs2.2, hxs⟩`.

Introduce `x hx y hy hxy`. Conclude with `hR₃'.2.1 x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy`. Introduce `y hy`. Take `⟨hy3, hyA, s', hs'2, hs'A, hys⟩` from `mem_gGrp.1 hy`. Take `⟨x, hxR, hyx⟩` from `hR₃'.2.2 y (AddSubgroup.mem_inf.2 ⟨hy3, hyA⟩)`.

Establish `hx3` using `AddSubgroup.mem_inf.1 (hR₃'.1 _ hxR)`. Use `⟨x, Finset.mem_filter.2 ⟨hxR, ?_⟩, hyx⟩` and prove the remaining obligations. Establish `hw2 : s' + (y - x) ∈ Λ₂` using `Λ₂.add_mem hs'2 hyx`. Establish `hwA : s' + (y - x) ∈ A'` using `A'.add_mem hs'A (A'.sub_mem hyA hx3.2)`. Take `⟨s₂, hs₂, hws⟩` from `hR₂'.2.2 _ (AddSubgroup.mem_inf.2 ⟨hw2, hwA⟩)`.

Use `⟨s₂, hs₂, ?_⟩` and prove the remaining obligations. Establish `e : x + s₂ = (y + s') - (s' + (y - x) - s₂)` using `by abel`. Rewrite using `[e]`. Conclude with `Λ₁.sub_mem hys hws`. Introduce `x y`.

Simplify using `only [hχ]`. Rewrite using `[← Complex.exp_add]`. Use `congr 1`. Simplify using `only [altE, map_add, Complex.add_im]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `k hk`. Take `⟨m, hm⟩` from `altE_int hT.sd₂ hs₁2 hk`. Simplify using `only [hχ, hm]`. Conclude with `exp_int_one m`.

Use `choose! t ht0 ht using hc`. Establish `hsum : tripleSum H α Λ₁ ((R₂ ×ˢ R₂').image fun p => p.1 + p.2) ((R₃ ×ˢ R₃').image fun p => p.1 + p.2) = ((∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0) : ℝ) : ℂ)`. Unfold `tripleSum`. Rewrite using `[Finset.sum_image (fun p hp q hq h => hi₃ p hp q hq h)]`. Rewrite using `[Finset.sum_congr rfl fun q _ => Finset.sum_image (fun p hp q hq h => hi₂ p hp q hq h)]`.

Establish `term : ∀ q ∈ R₃ ×ˢ R₃', ∀ s ∈ R₂ ×ˢ R₂', (if q.1 + q.2 + (s.1 + s.2) ∈ Λ₁ then psiT H α (q.1 + q.2) (s.1 + s.2) else 0) = (if q.1 + s.1 ∈ Λ₁ then (1 : ℂ) else 0) * (if q.2 + s.2 ∈ Λ₁ then Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s.1 q.2 : ℂ)) else 0)`. Introduce `q hq s hs`. Rewrite `hq`, `hs` using `[Finset.mem_product]`. Establish `hq1` using `AddSubgroup.mem_inf.1 (hR₃.1 _ hq.1)`. Establish `hq2` using `AddSubgroup.mem_inf.1 (hR₃'.1 _ hq.2)`.

Establish `hs1` using `AddSubgroup.mem_inf.1 (hR₂.1 _ hs.1)`. Establish `hs2` using `AddSubgroup.mem_inf.1 (hR₂'.1 _ hs.2)`. Establish `e : q.1 + q.2 + (s.1 + s.2) = (q.1 + s.1) + (q.2 + s.2)` using `by abel`. Distinguish the cases in `h1 : q.1 + s.1 ∈ Λ₁`. Distinguish the cases in `h2 : q.2 + s.2 ∈ Λ₁`.

Rewrite using `[if_pos (by rw [e]; exact Λ₁.add_mem h1 h2), if_pos h1, if_pos h2, one_mul]`. Rewrite using `[(psiQuadratic V H α Λ₁ Λ₂ Λ₃ hT).1 q.1 hq1.1 s.1 hs1.1 h1 q.2 hq2.1 s.2 hs2.1 h2]`. Rewrite using `[hS.isoA _ _ hq1.2 hs1.2 hq1.1 hs1.1 h1, hS.isoA' _ _ hq2.2 hs2.2 hq2.1 hs2.1 h2, one_mul, one_mul]`. Rewrite using `[if_neg h2, mul_zero, if_neg]`. Introduce `h`.

Rewrite `h` using `[e]`. Conclude with `h2 (sep hm₁ hS.dec₁ (A.add_mem hq1.2 hs1.2) (A'.add_mem hq2.2 hs2.2) h).2`. Rewrite using `[if_neg h1, zero_mul, if_neg]`. Introduce `h`. Rewrite `h` using `[e]`.

Conclude with `h1 (sep hm₁ hS.dec₁ (A.add_mem hq1.2 hs1.2) (A'.add_mem hq2.2 hs2.2) h).1`. Rewrite using `[Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun s hs => term q hq s hs]`. Simplify using `only [Finset.sum_product]`. Use `push_cast`. Use `Finset.sum_congr rfl fun q₁ _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun s₁ hs₁ => ?_` and prove the remaining obligations. Use `split_ifs with h`. Simplify using `only [one_mul]`. Conclude with `ht s₁ hs₁`.

Simplify using the standard rewrite rules. Establish `hnn : 0 ≤ ∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0)` using `Finset.sum_nonneg fun q₁ _ => Finset.sum_nonneg fun s₁ hs₁ => by split_ifs`. Conclude with `ht0 s₁ hs₁`. Conclude with `le_refl _`. Use `set T := ∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0) with hT'`.

Use `set c : ℝ := Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) with hc'`. Establish `hc0 : 0 ≤ c` using `div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))`. Establish `hmu : tripleMu H α Λ₁ Λ₂ Λ₃ ((R₂ ×ˢ R₂').image fun p => p.1 + p.2) ((R₃ ×ˢ R₃').image fun p => p.1 + p.2) = ((c * T : ℝ) : ℂ)`. Unfold `tripleMu`. Rewrite using `[hsum, hc']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h8` using `tripleEighth V H α Λ₁ Λ₂ Λ₃ hT hF _ _ hS₂ hS₃`. Rewrite `h8`, the goal using `[hmu]`. Establish `h8' : (c * T) ^ 8 = 1` using `by exact_mod_cast h8`.

Rewrite using `[(pow_eq_one_iff_of_nonneg (mul_nonneg hc0 hnn) (by norm_num)).1 h8']`. Simplify using the standard rewrite rules.
-/
theorem mu_one_of_split {H : Sesq V} {α : V → ℂ} {Λ₁ Λ₂ Λ₃ A A' : AddSubgroup V}
    (hT : TripleData H α Λ₁ Λ₂ Λ₃) (hS : SplitTri H α Λ₁ Λ₂ Λ₃ A A')
    (hF : ∃ F ∈ fixedBy H α Λ₁, F ≠ 0) :
    ∃ S₂ S₃ : Finset V, IsReps Λ₁ Λ₂ S₂ ∧ IsReps Λ₂ Λ₃ S₃ ∧ tripleMu H α Λ₁ Λ₂ Λ₃ S₂ S₃ = 1 := by
  have hm₁ : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ₁ := fun x h h' => (hS.meet x h h').1
  have hm₂ : ∀ x, x ∈ A → x ∈ A' → x ∈ Λ₂ := fun x h h' => (hS.meet x h h').2.1
  obtain ⟨R₂, hR₂⟩ := (repsExist V Λ₁ (Λ₂ ⊓ A) (relIdx_le_ne hT.i₁₂ inf_le_left)).1
  obtain ⟨R₂', hR₂'⟩ := (repsExist V Λ₁ (Λ₂ ⊓ A') (relIdx_le_ne hT.i₁₂ inf_le_left)).1
  obtain ⟨R₃, hR₃⟩ := (repsExist V Λ₂ (Λ₃ ⊓ A) (relIdx_le_ne hT.i₂₃ inf_le_left)).1
  obtain ⟨R₃', hR₃'⟩ := (repsExist V Λ₂ (Λ₃ ⊓ A') (relIdx_le_ne hT.i₂₃ inf_le_left)).1
  obtain ⟨hS₂, hi₂⟩ := reps_sum hm₁ hS.dec₁ hS.dec₂ hR₂ hR₂'
  obtain ⟨hS₃, hi₃⟩ := reps_sum hm₂ hS.dec₂ hS.dec₃ hR₃ hR₃'
  refine ⟨_, _, hS₂, hS₃, ?_⟩

  have hc : ∀ s₁ ∈ R₂, ∃ t : ℝ, 0 ≤ t ∧
      ∑ q₂ ∈ R₃', ∑ s₂ ∈ R₂', (if q₂ + s₂ ∈ Λ₁ then
        Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s₁ q₂ : ℂ)) else 0) = t := by
    intro s₁ hs₁
    have hs₁2 : s₁ ∈ Λ₂ := (AddSubgroup.mem_inf.1 (hR₂.1 _ hs₁)).1
    set χ : V → ℂ := fun p => Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s₁ p : ℂ)) with hχ
    have inner : ∀ q₂ ∈ R₃', ∑ s₂ ∈ R₂', (if q₂ + s₂ ∈ Λ₁ then χ q₂ else 0) =
        if (∃ s₂ ∈ R₂', q₂ + s₂ ∈ Λ₁) then χ q₂ else 0 := by
      intro q₂ _
      by_cases hex : ∃ s₂ ∈ R₂', q₂ + s₂ ∈ Λ₁
      · obtain ⟨s, hs, hqs⟩ := hex
        rw [if_pos ⟨s, hs, hqs⟩, Finset.sum_eq_single_of_mem s hs, if_pos hqs]
        intro b hb hne
        rw [if_neg]
        intro hqb
        apply hne
        apply hR₂'.2.1 b hb s hs
        have e : b - s = (q₂ + b) - (q₂ + s) := by abel
        rw [e]; exact Λ₁.sub_mem hqb hqs
      · rw [if_neg hex]
        exact Finset.sum_eq_zero fun b hb => if_neg fun h => hex ⟨b, hb, h⟩
    rw [Finset.sum_congr rfl inner, ← Finset.sum_filter]
    refine char_sum (G := gGrp Λ₁ Λ₂ Λ₃ A') (K := Λ₂) ?_ ?_ ?_ χ ?_ ?_
    · intro x hx
      obtain ⟨hxR, s, hs, hxs⟩ := Finset.mem_filter.1 hx
      have hx3 := AddSubgroup.mem_inf.1 (hR₃'.1 _ hxR)
      have hs2 := AddSubgroup.mem_inf.1 (hR₂'.1 _ hs)
      exact ⟨hx3.1, hx3.2, s, hs2.1, hs2.2, hxs⟩
    · intro x hx y hy hxy
      exact hR₃'.2.1 x (Finset.mem_filter.1 hx).1 y (Finset.mem_filter.1 hy).1 hxy
    · intro y hy
      obtain ⟨hy3, hyA, s', hs'2, hs'A, hys⟩ := mem_gGrp.1 hy
      obtain ⟨x, hxR, hyx⟩ := hR₃'.2.2 y (AddSubgroup.mem_inf.2 ⟨hy3, hyA⟩)
      have hx3 := AddSubgroup.mem_inf.1 (hR₃'.1 _ hxR)
      refine ⟨x, Finset.mem_filter.2 ⟨hxR, ?_⟩, hyx⟩
      have hw2 : s' + (y - x) ∈ Λ₂ := Λ₂.add_mem hs'2 hyx
      have hwA : s' + (y - x) ∈ A' := A'.add_mem hs'A (A'.sub_mem hyA hx3.2)
      obtain ⟨s₂, hs₂, hws⟩ := hR₂'.2.2 _ (AddSubgroup.mem_inf.2 ⟨hw2, hwA⟩)
      refine ⟨s₂, hs₂, ?_⟩
      have e : x + s₂ = (y + s') - (s' + (y - x) - s₂) := by abel
      rw [e]; exact Λ₁.sub_mem hys hws
    · intro x y
      simp only [hχ]
      rw [← Complex.exp_add]
      congr 1
      simp only [altE, map_add, Complex.add_im]
      push_cast; ring
    · intro k hk
      obtain ⟨m, hm⟩ := altE_int hT.sd₂ hs₁2 hk
      simp only [hχ, hm]
      exact exp_int_one m
  choose! t ht0 ht using hc

  have hsum : tripleSum H α Λ₁ ((R₂ ×ˢ R₂').image fun p => p.1 + p.2) ((R₃ ×ˢ R₃').image fun p => p.1 + p.2) =
      ((∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0) : ℝ) : ℂ) := by
    unfold tripleSum
    rw [Finset.sum_image (fun p hp q hq h => hi₃ p hp q hq h)]
    rw [Finset.sum_congr rfl fun q _ => Finset.sum_image (fun p hp q hq h => hi₂ p hp q hq h)]
    have term : ∀ q ∈ R₃ ×ˢ R₃', ∀ s ∈ R₂ ×ˢ R₂',
        (if q.1 + q.2 + (s.1 + s.2) ∈ Λ₁ then psiT H α (q.1 + q.2) (s.1 + s.2) else 0) =
        (if q.1 + s.1 ∈ Λ₁ then (1 : ℂ) else 0) *
          (if q.2 + s.2 ∈ Λ₁ then Complex.exp (2 * (Real.pi : ℂ) * Complex.I * (altE H s.1 q.2 : ℂ)) else 0) := by
      intro q hq s hs
      rw [Finset.mem_product] at hq hs
      have hq1 := AddSubgroup.mem_inf.1 (hR₃.1 _ hq.1)
      have hq2 := AddSubgroup.mem_inf.1 (hR₃'.1 _ hq.2)
      have hs1 := AddSubgroup.mem_inf.1 (hR₂.1 _ hs.1)
      have hs2 := AddSubgroup.mem_inf.1 (hR₂'.1 _ hs.2)
      have e : q.1 + q.2 + (s.1 + s.2) = (q.1 + s.1) + (q.2 + s.2) := by abel
      by_cases h1 : q.1 + s.1 ∈ Λ₁
      · by_cases h2 : q.2 + s.2 ∈ Λ₁
        · rw [if_pos (by rw [e]; exact Λ₁.add_mem h1 h2), if_pos h1, if_pos h2, one_mul]
          rw [(psiQuadratic V H α Λ₁ Λ₂ Λ₃ hT).1 q.1 hq1.1 s.1 hs1.1 h1 q.2 hq2.1 s.2 hs2.1 h2]
          rw [hS.isoA _ _ hq1.2 hs1.2 hq1.1 hs1.1 h1, hS.isoA' _ _ hq2.2 hs2.2 hq2.1 hs2.1 h2, one_mul, one_mul]
        · rw [if_neg h2, mul_zero, if_neg]
          intro h
          rw [e] at h
          exact h2 (sep hm₁ hS.dec₁ (A.add_mem hq1.2 hs1.2) (A'.add_mem hq2.2 hs2.2) h).2
      · rw [if_neg h1, zero_mul, if_neg]
        intro h
        rw [e] at h
        exact h1 (sep hm₁ hS.dec₁ (A.add_mem hq1.2 hs1.2) (A'.add_mem hq2.2 hs2.2) h).1
    rw [Finset.sum_congr rfl fun q hq => Finset.sum_congr rfl fun s hs => term q hq s hs]
    simp only [Finset.sum_product]
    push_cast
    refine Finset.sum_congr rfl fun q₁ _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun s₁ hs₁ => ?_
    split_ifs with h
    · simp only [one_mul]; exact ht s₁ hs₁
    · simp
  have hnn : 0 ≤ ∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0) :=
    Finset.sum_nonneg fun q₁ _ => Finset.sum_nonneg fun s₁ hs₁ => by
      split_ifs
      · exact ht0 s₁ hs₁
      · exact le_refl _
  set T := ∑ q₁ ∈ R₃, ∑ s₁ ∈ R₂, (if q₁ + s₁ ∈ Λ₁ then t s₁ else 0) with hT'
  set c : ℝ := Real.sqrt (relIdx Λ₁ Λ₃) / (Real.sqrt (relIdx Λ₁ Λ₂) * Real.sqrt (relIdx Λ₂ Λ₃)) with hc'
  have hc0 : 0 ≤ c := div_nonneg (Real.sqrt_nonneg _) (mul_nonneg (Real.sqrt_nonneg _) (Real.sqrt_nonneg _))
  have hmu : tripleMu H α Λ₁ Λ₂ Λ₃ ((R₂ ×ˢ R₂').image fun p => p.1 + p.2) ((R₃ ×ˢ R₃').image fun p => p.1 + p.2) =
      ((c * T : ℝ) : ℂ) := by
    unfold tripleMu
    rw [hsum, hc']; push_cast; ring
  have h8 := tripleEighth V H α Λ₁ Λ₂ Λ₃ hT hF _ _ hS₂ hS₃
  rw [hmu] at h8 ⊢
  have h8' : (c * T) ^ 8 = 1 := by exact_mod_cast h8
  rw [(pow_eq_one_iff_of_nonneg (mul_nonneg hc0 hnn) (by norm_num)).1 h8']
  simp

end Formalism.L2.PairingIndexBounds.Eq.Sq
