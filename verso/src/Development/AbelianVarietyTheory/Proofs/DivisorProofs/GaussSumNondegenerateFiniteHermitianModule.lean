import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsHeisTrivial
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SumEqZeroAddUnits

open Classical GlobalTheory.FinWeil
open scoped BigOperators

namespace GlobalTheory.HermitianGauss

section Fin

variable {R M : Type} [CommRing R] [AddCommGroup M] [Module R M] [Fintype M]

noncomputable def pts (B : Submodule R M) : Finset M := Finset.univ.filter (· ∈ B)

/- English proof (translation)
Simplify using `[pts]`.
-/
@[simp] theorem mem_pts {B : Submodule R M} {x : M} : x ∈ pts B ↔ x ∈ B := by simp [pts]

/- English proof (translation)
Rewrite using `[← Nat.card_eq_finsetCard]`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_pts)`.
-/
theorem card_pts (B : Submodule R M) : (pts B).card = Nat.card B := by
  rw [← Nat.card_eq_finsetCard]
  exact Nat.card_congr (Equiv.subtypeEquivRight fun x => mem_pts)

/- English proof (translation)
The claim follows from `Finset.card_pos.mpr ⟨0, mem_pts.mpr B.zero_mem⟩`.
-/
theorem card_pts_pos (B : Submodule R M) : 0 < (pts B).card := Finset.card_pos.mpr ⟨0, mem_pts.mpr B.zero_mem⟩

/- English proof (translation)
Rewrite using `[card_pts, card_pts]`. Conclude with `AddSubgroup.card_dvd_of_le (show A.toAddSubgroup ≤ B.toAddSubgroup from h)`.
-/
theorem card_pts_dvd {A B : Submodule R M} (h : A ≤ B) : (pts A).card ∣ (pts B).card := by
  rw [card_pts, card_pts]
  exact AddSubgroup.card_dvd_of_le (show A.toAddSubgroup ≤ B.toAddSubgroup from h)

/- English proof (translation)
Establish `hs : pts A ⊆ pts B` using `fun y hy => mem_pts.mpr (h (mem_pts.mp hy))`. Establish `he` using `Finset.eq_of_subset_of_card_le hs hc`. Use `le_antisymm h fun y hy => ?_` and prove the remaining obligations. Establish `: y ∈ pts A` using `by rw [he]; exact mem_pts.mpr hy`. Conclude with `mem_pts.mp this`.
-/
theorem eq_of_card_pts {A B : Submodule R M} (h : A ≤ B) (hc : (pts B).card ≤ (pts A).card) : A = B := by
  have hs : pts A ⊆ pts B := fun y hy => mem_pts.mpr (h (mem_pts.mp hy))
  have he := Finset.eq_of_subset_of_card_le hs hc
  refine le_antisymm h fun y hy => ?_
  have : y ∈ pts A := by rw [he]; exact mem_pts.mpr hy
  exact mem_pts.mp this

/- English proof (translation)
Use `Finset.sum_nbij' (fun y => y + z) (fun y => y - z) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `a ha`. Conclude with `mem_pts.mpr (B.add_mem (mem_pts.mp ha) hz)`. Introduce `a ha`. Conclude with `mem_pts.mpr (B.sub_mem (mem_pts.mp ha) hz)`.

Introduce `a _`. Conclude with `add_sub_cancel_right a z`. Introduce `a _`. Conclude with `sub_add_cancel a z`. Introduce `a _`.

Both sides reduce to the same expression.
-/
theorem sum_pts_add (B : Submodule R M) (f : M → ℂ) {z : M} (hz : z ∈ B) :
    ∑ y ∈ pts B, f (y + z) = ∑ y ∈ pts B, f y := by
  refine Finset.sum_nbij' (fun y => y + z) (fun y => y - z) ?_ ?_ ?_ ?_ ?_
  · intro a ha; exact mem_pts.mpr (B.add_mem (mem_pts.mp ha) hz)
  · intro a ha; exact mem_pts.mpr (B.sub_mem (mem_pts.mp ha) hz)
  · intro a _; exact add_sub_cancel_right a z
  · intro a _; exact sub_add_cancel a z
  · intro a _; rfl

/- English proof (translation)
Use `split_ifs with h`. Rewrite using `[Finset.sum_congr rfl fun y hy => h y (mem_pts.mp hy)]`. Simplify using the standard rewrite rules. Use `push Not at h`. Take `⟨y0, hy0, hne⟩` from `h`.

Establish `h1 : ∑ y ∈ pts B, f (y + y0) = ∑ y ∈ pts B, f y` using `sum_pts_add B f hy0`. Rewrite `h1` using `[hf]`. Rewrite `h1` using `[← Finset.sum_mul]`. Establish `h2 : (∑ y ∈ pts B, f y) * (f y0 - 1) = 0` using `by rw [mul_sub, h1, mul_one, sub_self]`. Break down `mul_eq_zero.mp h2 with h3 | h3` into its components or cases.

Conclude with `h3`. Conclude with `absurd (sub_eq_zero.mp h3) hne`.
-/
theorem sum_char (B : Submodule R M) (f : M → ℂ) (hf : ∀ a b, f (a + b) = f a * f b) :
    ∑ y ∈ pts B, f y = if ∀ y ∈ B, f y = 1 then ((pts B).card : ℂ) else 0 := by
  split_ifs with h
  · rw [Finset.sum_congr rfl fun y hy => h y (mem_pts.mp hy)]
    simp
  · push Not at h
    obtain ⟨y0, hy0, hne⟩ := h
    have h1 : ∑ y ∈ pts B, f (y + y0) = ∑ y ∈ pts B, f y := sum_pts_add B f hy0
    simp_rw [hf] at h1
    rw [← Finset.sum_mul] at h1
    have h2 : (∑ y ∈ pts B, f y) * (f y0 - 1) = 0 := by rw [mul_sub, h1, mul_one, sub_self]
    rcases mul_eq_zero.mp h2 with h3 | h3
    · exact h3
    · exact absurd (sub_eq_zero.mp h3) hne

/- English proof (translation)
Establish `hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a` using `fun a => Quotient.out_eq a`. Use `Finite.of_injective (fun a : R ⧸ P => (Quotient.out a : R) • x) fun a b hab => ?_` and prove the remaining obligations. Establish `hab' : (Quotient.out a : R) • x = (Quotient.out b : R) • x` using `hab`. Establish `h : (Quotient.out a - Quotient.out b : R) ∈ P`. Rewrite using `[← hP, sub_smul, hab', sub_self]`.

Conclude with `D.zero_mem`. Rewrite using `[← hout a, ← hout b]`. Conclude with `Ideal.Quotient.eq.mpr h`.
-/
theorem finite_quot {D : Submodule R M} {x : M} {P : Ideal R} (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    Finite (R ⧸ P) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  refine Finite.of_injective (fun a : R ⧸ P => (Quotient.out a : R) • x) fun a b hab => ?_
  have hab' : (Quotient.out a : R) • x = (Quotient.out b : R) • x := hab
  have h : (Quotient.out a - Quotient.out b : R) ∈ P := by
    rw [← hP, sub_smul, hab', sub_self]
    exact D.zero_mem
  rw [← hout a, ← hout b]
  exact Ideal.Quotient.eq.mpr h

/- English proof (translation)
Establish `hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a` using `fun a => Quotient.out_eq a`. Combine the equalities or inequalities in the displayed calculation. Use `symm`. Apply `Finset.sum_nbij (fun p => p.2 + (Quotient.out p.1 : R) • x)` to reduce the goal to its premises. Introduce and unpack `⟨q, d⟩ hp`.

Simplify using `only [Finset.mem_product, Finset.mem_univ, true_and, mem_pts] at hp`. Conclude with `mem_pts.mpr (Submodule.add_mem_sup hp (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))`. Introduce and unpack `⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq`. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and, Finset.mem_coe, mem_pts] at h1 h2`. Establish `heq' : d1 + (Quotient.out q1 : R) • x = d2 + (Quotient.out q2 : R) • x` using `heq`.

Establish `hq : q1 = q2`. Establish `hm : (Quotient.out q1 - Quotient.out q2 : R) • x ∈ D`. Establish `e : (Quotient.out q1 : R) • x - (Quotient.out q2 : R) • x = d2 - d1`. Rewrite using `[sub_eq_sub_iff_add_eq_add, add_comm]`. Conclude with `heq'`.

Rewrite using `[sub_smul, e]`. Conclude with `D.sub_mem h2 h1`. Rewrite using `[← hout q1, ← hout q2]`. Conclude with `Ideal.Quotient.eq.mpr ((hP _).mp hm)`. Substitute `hq` using the available equality.

Establish `: d1 = d2` using `add_right_cancel heq'`. Rewrite using `[this]`. Introduce `y hy`. Rewrite `hy` using `[Finset.mem_coe, mem_pts]`. Take `⟨d, hd, z, hz, rfl⟩` from `Submodule.mem_sup.mp hy`.

Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Establish `hmem : (Quotient.out (Ideal.Quotient.mk P a) - a : R) ∈ P` using `Ideal.Quotient.eq.mp (hout _)`. Use `⟨(Ideal.Quotient.mk P a, d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x), ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and, Finset.mem_coe, mem_pts]`. Conclude with `D.sub_mem hd ((hP _).mpr hmem)`.

Use `show d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x + (Quotient.out (Ideal.Quotient.mk P a) : R) • x = d + a • x`. Rewrite using `[sub_smul]`. Normalize the expressions using the abelian group laws. Introduce `p _`. Both sides reduce to the same expression.

Use `_ = _ := Finset.sum_product' _ _ (fun q d => f (d + (Quotient.out q : R) • x))`.
-/
theorem sum_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P)
    {A : Type} [AddCommMonoid A] (f : M → A) :
    ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y = ∑ q : R ⧸ P, ∑ d ∈ pts D, f (d + (Quotient.out q : R) • x) := by
  have hout : ∀ a : R ⧸ P, Ideal.Quotient.mk P (Quotient.out a) = a := fun a => Quotient.out_eq a
  calc ∑ y ∈ pts (D ⊔ Submodule.span R {x}), f y
      = ∑ p ∈ (Finset.univ : Finset (R ⧸ P)) ×ˢ pts D, f (p.2 + (Quotient.out p.1 : R) • x) := by
        symm
        apply Finset.sum_nbij (fun p => p.2 + (Quotient.out p.1 : R) • x)
        · rintro ⟨q, d⟩ hp
          simp only [Finset.mem_product, Finset.mem_univ, true_and, mem_pts] at hp
          exact mem_pts.mpr (Submodule.add_mem_sup hp
            (Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)))
        · rintro ⟨q1, d1⟩ h1 ⟨q2, d2⟩ h2 heq
          simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
            Finset.mem_coe, mem_pts] at h1 h2
          have heq' : d1 + (Quotient.out q1 : R) • x = d2 + (Quotient.out q2 : R) • x := heq
          have hq : q1 = q2 := by
            have hm : (Quotient.out q1 - Quotient.out q2 : R) • x ∈ D := by
              have e : (Quotient.out q1 : R) • x - (Quotient.out q2 : R) • x = d2 - d1 := by
                rw [sub_eq_sub_iff_add_eq_add, add_comm]
                exact heq'
              rw [sub_smul, e]
              exact D.sub_mem h2 h1
            rw [← hout q1, ← hout q2]
            exact Ideal.Quotient.eq.mpr ((hP _).mp hm)
          subst hq
          have : d1 = d2 := add_right_cancel heq'
          rw [this]
        · intro y hy
          rw [Finset.mem_coe, mem_pts] at hy
          obtain ⟨d, hd, z, hz, rfl⟩ := Submodule.mem_sup.mp hy
          obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hz
          have hmem : (Quotient.out (Ideal.Quotient.mk P a) - a : R) ∈ P := Ideal.Quotient.eq.mp (hout _)
          refine ⟨(Ideal.Quotient.mk P a, d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x), ?_, ?_⟩
          · simp only [Finset.coe_product, Set.mem_prod, Finset.coe_univ, Set.mem_univ, true_and,
              Finset.mem_coe, mem_pts]
            exact D.sub_mem hd ((hP _).mpr hmem)
          · show d - (Quotient.out (Ideal.Quotient.mk P a) - a : R) • x
                + (Quotient.out (Ideal.Quotient.mk P a) : R) • x = d + a • x
            rw [sub_smul]
            abel
        · intro p _
          rfl
    _ = _ := Finset.sum_product' _ _ (fun q d => f (d + (Quotient.out q : R) • x))

/- English proof (translation)
Establish `h` using `sum_sup hP (fun _ => (1 : ℕ))`. Simplify `h` using `[Finset.sum_const, Finset.card_univ]`.
-/
theorem card_sup {D : Submodule R M} {x : M} {P : Ideal R} [Fintype (R ⧸ P)] (hP : ∀ r, r • x ∈ D ↔ r ∈ P) :
    (pts (D ⊔ Submodule.span R {x})).card = Fintype.card (R ⧸ P) * (pts D).card := by
  have h := sum_sup hP (fun _ => (1 : ℕ))
  simpa [Finset.sum_const, Finset.card_univ] using h

variable {σ : R →+* R} {β : M → M → ℂ}

def perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y))
    (h0 : ∀ y, β 0 y = 1) (B N : Submodule R M) : Submodule R M where
  carrier := {x | x ∈ B ∧ ∀ y ∈ N, β x y = 1}
  add_mem' := fun {a b} ha hb => ⟨B.add_mem ha.1 hb.1, fun y hy => by rw [hadd, ha.2 y hy, hb.2 y hy, one_mul]⟩
  zero_mem' := ⟨B.zero_mem, fun y _ => h0 y⟩
  smul_mem' := fun r a ha => ⟨B.smul_mem r ha.1, fun y hy => by rw [hadj]; exact ha.2 _ (N.smul_mem _ hy)⟩

/- English proof (translation)
Establish `hr : ∀ a b c, β a (b + c) = β a b * β a c` using `fun a b c => by`. Rewrite using `[hsym a, hadd, hsym b, hsym c]`. Establish `e1 : ∀ y ∈ pts B, ∑ z ∈ pts N, β y z = if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0` using `fun y _ => sum_char N (β y) (hr y)`. Establish `h1 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts N').card : ℂ) * (pts N).card`. Rewrite using `[Finset.sum_congr rfl e1, ← Finset.sum_filter]`.

Establish `hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N'`. Use extensionality with `y`. Simplify using `[pts, hN']`. Rewrite using `[hf, Finset.sum_const, nsmul_eq_mul]`. Establish `e2 : ∀ z ∈ pts N, ∑ y ∈ pts B, β y z = if ∀ y ∈ B, β y z = 1 then ((pts B).card : ℂ) else 0` using `fun z _ => sum_char B (fun y => β y z) (fun a b => hadd a b z)`.

Establish `h2 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts C).card : ℂ) * (pts B).card`. Rewrite using `[Finset.sum_comm, Finset.sum_congr rfl e2, ← Finset.sum_filter]`. Establish `hf : (pts N).filter (fun z => ∀ y ∈ B, β y z = 1) = pts C`. Use extensionality with `z`. Simplify using `only [pts, Finset.mem_filter, Finset.mem_univ, true_and]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hz, h⟩`. Conclude with `(hrad z (hNB hz)).mpr fun y hy => by rw [hsym]; exact h y hy`. Introduce `hz`. Conclude with `⟨hCN hz, fun y hy => by rw [hsym]; exact (hrad z (hNB (hCN hz))).mp hz y hy⟩`.

Rewrite using `[hf, Finset.sum_const, nsmul_eq_mul]`. Conclude with `h2.symm.trans h1` after adjusting the coercions.
-/
theorem card_perp (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    {B C N N' : Submodule R M} (hCN : C ≤ N) (hNB : N ≤ B) (hrad : ∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1)
    (hN' : ∀ x, x ∈ N' ↔ x ∈ B ∧ ∀ y ∈ N, β x y = 1) :
    (pts C).card * (pts B).card = (pts N').card * (pts N).card := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have e1 : ∀ y ∈ pts B, ∑ z ∈ pts N, β y z =
      if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0 := fun y _ => sum_char N (β y) (hr y)
  have h1 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts N').card : ℂ) * (pts N).card := by
    rw [Finset.sum_congr rfl e1, ← Finset.sum_filter]
    have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
      ext y
      simp [pts, hN']
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  have e2 : ∀ z ∈ pts N, ∑ y ∈ pts B, β y z =
      if ∀ y ∈ B, β y z = 1 then ((pts B).card : ℂ) else 0 := fun z _ =>
    sum_char B (fun y => β y z) (fun a b => hadd a b z)
  have h2 : ∑ y ∈ pts B, ∑ z ∈ pts N, β y z = ((pts C).card : ℂ) * (pts B).card := by
    rw [Finset.sum_comm, Finset.sum_congr rfl e2, ← Finset.sum_filter]
    have hf : (pts N).filter (fun z => ∀ y ∈ B, β y z = 1) = pts C := by
      ext z
      simp only [pts, Finset.mem_filter, Finset.mem_univ, true_and]
      constructor
      · rintro ⟨hz, h⟩
        exact (hrad z (hNB hz)).mpr fun y hy => by rw [hsym]; exact h y hy
      · intro hz
        exact ⟨hCN hz, fun y hy => by rw [hsym]; exact (hrad z (hNB (hCN hz))).mp hz y hy⟩
    rw [hf, Finset.sum_const, nsmul_eq_mul]
  exact_mod_cast h2.symm.trans h1

/- English proof (translation)
Establish `hr : ∀ a b c, β a (b + c) = β a b * β a c` using `fun a b c => by`. Rewrite using `[hsym a, hadd, hsym b, hsym c]`. Establish `key : β (w • y) z * β (w • z) y = β z y`. Rewrite using `[hadj w y z, hsym (w • z) y, ← hr, ← add_smul, add_comm (σ w), hw, one_smul, hsym]`. Rewrite using `[smul_add, hadd, hr, hr, ← key]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem quad_add {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (y z : M) :
    β (w • (y + z)) (y + z) = β (w • y) y * β (w • z) z * β z y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have key : β (w • y) z * β (w • z) y = β z y := by
    rw [hadj w y z, hsym (w • z) y, ← hr, ← add_smul, add_comm (σ w), hw, one_smul, hsym]
  rw [smul_add, hadd, hr, hr, ← key]
  ring

/- English proof (translation)
Establish `hne' : (pts B \ pts C).Nonempty`. Assume the negation of the conclusion as `h`. Rewrite `h` using `[Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset]`. Conclude with `hne (le_antisymm hCB fun y hy => mem_pts.mp (h (mem_pts.mpr hy)))`. Take `⟨x, hx, hmin⟩` from `Finset.exists_min_image _ (fun x => (pts (C ⊔ Submodule.span R {x})).card) hne'`.

Rewrite `hx` using `[Finset.mem_sdiff, mem_pts, mem_pts]`. Set `I : Ideal R` to `Submodule.comap (LinearMap.toSpanSingleton R M x) C`. Establish `hI : ∀ r : R, r ∈ I ↔ r • x ∈ C` using `fun r => by`. Simplify using `[I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]`. Use `⟨x, hx.1, hx.2, I, ?_, fun r => (hI r).symm⟩` and prove the remaining obligations.

Rewrite using `[Ideal.isMaximal_iff]`. Use `⟨fun h1 => hx.2 (by simpa using (hI 1).mp h1), fun J r hIJ hr hrJ => ?_⟩` and prove the remaining obligations. Establish `hrx : r • x ∈ pts B \ pts C`. Rewrite using `[Finset.mem_sdiff, mem_pts, mem_pts]`. Conclude with `⟨B.smul_mem r hx.1, fun h => hr ((hI r).mpr h)⟩`.

Establish `h1` using `hmin _ hrx`. Establish `hle : C ⊔ Submodule.span R {r • x} ≤ C ⊔ Submodule.span R {x}`. Use `sup_le_sup_left ?_ C` and prove the remaining obligations. Rewrite using `[Submodule.span_le, Set.singleton_subset_iff]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)`.

Establish `heq` using `eq_of_card_pts hle h1`. Establish `hxm : x ∈ C ⊔ Submodule.span R {r • x}`. Rewrite using `[heq]`. Conclude with `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`. Take `⟨c, hc, z, hz, hcz⟩` from `Submodule.mem_sup.mp hxm`.

Take `⟨s, rfl⟩` from `Submodule.mem_span_singleton.mp hz`. Establish `h2 : (1 - s * r) ∈ I`. Rewrite using `[hI]`. Establish `e : (1 - s * r) • x = c`. Rewrite using `[sub_smul, one_smul, mul_smul, sub_eq_iff_eq_add]`.

Conclude with `hcz.symm`. Rewrite using `[e]`. Conclude with `hc`. Establish `h3` using `J.add_mem (hIJ h2) (J.mul_mem_left s hrJ)`. Simplify using `using h3`.
-/
private theorem exists_mem_not_mem_annihilator_maximal_of_lt {C B : Submodule R M} (hCB : C ≤ B) (hne : C ≠ B) :
    ∃ x ∈ B, x ∉ C ∧ ∃ P : Ideal R, P.IsMaximal ∧ ∀ r : R, r • x ∈ C ↔ r ∈ P := by
  have hne' : (pts B \ pts C).Nonempty := by
    by_contra h
    rw [Finset.not_nonempty_iff_eq_empty, Finset.sdiff_eq_empty_iff_subset] at h
    exact hne (le_antisymm hCB fun y hy => mem_pts.mp (h (mem_pts.mpr hy)))
  obtain ⟨x, hx, hmin⟩ :=
    Finset.exists_min_image _ (fun x => (pts (C ⊔ Submodule.span R {x})).card) hne'
  rw [Finset.mem_sdiff, mem_pts, mem_pts] at hx
  let I : Ideal R := Submodule.comap (LinearMap.toSpanSingleton R M x) C
  have hI : ∀ r : R, r ∈ I ↔ r • x ∈ C := fun r => by
    simp [I, Submodule.mem_comap, LinearMap.toSpanSingleton_apply]
  refine ⟨x, hx.1, hx.2, I, ?_, fun r => (hI r).symm⟩
  rw [Ideal.isMaximal_iff]
  refine ⟨fun h1 => hx.2 (by simpa using (hI 1).mp h1), fun J r hIJ hr hrJ => ?_⟩
  have hrx : r • x ∈ pts B \ pts C := by
    rw [Finset.mem_sdiff, mem_pts, mem_pts]
    exact ⟨B.smul_mem r hx.1, fun h => hr ((hI r).mpr h)⟩
  have h1 := hmin _ hrx
  have hle : C ⊔ Submodule.span R {r • x} ≤ C ⊔ Submodule.span R {x} := by
    refine sup_le_sup_left ?_ C
    rw [Submodule.span_le, Set.singleton_subset_iff]
    exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self x)
  have heq := eq_of_card_pts hle h1
  have hxm : x ∈ C ⊔ Submodule.span R {r • x} := by
    rw [heq]
    exact Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  obtain ⟨c, hc, z, hz, hcz⟩ := Submodule.mem_sup.mp hxm
  obtain ⟨s, rfl⟩ := Submodule.mem_span_singleton.mp hz
  have h2 : (1 - s * r) ∈ I := by
    rw [hI]
    have e : (1 - s * r) • x = c := by
      rw [sub_smul, one_smul, mul_smul, sub_eq_iff_eq_add]
      exact hcz.symm
    rw [e]
    exact hc
  have h3 := J.add_mem (hIJ h2) (J.mul_mem_left s hrJ)
  simpa using h3

/- English proof (translation)
Establish `hr : ∀ a b c, β a (b + c) = β a b * β a c` using `fun a b c => by`. Rewrite using `[hsym a, hadd, hsym b, hsym c]`. Establish `hN0 : ((pts N).card : ℂ) ≠ 0` using `by exact_mod_cast (card_pts_pos N).ne'`. Establish `step1 : ∀ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) = ∑ y ∈ pts B, β (w • y) y` using `fun n hn => sum_pts_add B (fun y => β (w • y) y) (hNB (mem_pts.mp hn))`. Establish `step2 : ∀ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) = β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0)`.

Introduce `y _`. Establish `e : ∀ n ∈ pts N, β (w • (y + n)) (y + n) = β (w • y) y * β y n`. Introduce `n hn`. Rewrite using `[quad_add hσ hw hadd hsym hadj, hQ n (mem_pts.mp hn), mul_one, hsym n y]`. Rewrite using `[Finset.sum_congr rfl e, ← Finset.mul_sum, sum_char N (β y) (hr y)]`.

Apply `mul_left_cancel₀ hN0` to reduce the goal to its premises. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Finset.sum_congr rfl step1, Finset.sum_const, nsmul_eq_mul]`. Use `_ = ∑ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) := Finset.sum_comm`. Use `_ = ∑ y ∈ pts B, β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) := Finset.sum_congr rfl step2`.

Use `_ = ((pts N).card : ℂ) * ∑ y ∈ pts N', β (w • y) y := by`. Rewrite using `[Finset.mul_sum]`. Repeatedly rewrite using `[mul_ite, mul_zero]`. Rewrite using `[← Finset.sum_filter]`. Establish `hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N'`.

Use extensionality with `y`. Simplify using `[pts, hN']`. Rewrite using `[hf]`. Conclude with `Finset.sum_congr rfl fun y _ => mul_comm _ _`.
-/
private theorem sum_pts_eq_sum_pts_orth {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) {B N N' : Submodule R M} (hNB : N ≤ B)
    (hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1) (hQ : ∀ n ∈ N, β (w • n) n = 1) :
    ∑ y ∈ pts B, β (w • y) y = ∑ y ∈ pts N', β (w • y) y := by
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hN0 : ((pts N).card : ℂ) ≠ 0 := by exact_mod_cast (card_pts_pos N).ne'
  have step1 : ∀ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) = ∑ y ∈ pts B, β (w • y) y :=
    fun n hn => sum_pts_add B (fun y => β (w • y) y) (hNB (mem_pts.mp hn))
  have step2 : ∀ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) =
      β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) := by
    intro y _
    have e : ∀ n ∈ pts N, β (w • (y + n)) (y + n) = β (w • y) y * β y n := by
      intro n hn
      rw [quad_add hσ hw hadd hsym hadj, hQ n (mem_pts.mp hn), mul_one, hsym n y]
    rw [Finset.sum_congr rfl e, ← Finset.mul_sum, sum_char N (β y) (hr y)]
  apply mul_left_cancel₀ hN0
  calc ((pts N).card : ℂ) * ∑ y ∈ pts B, β (w • y) y
      = ∑ n ∈ pts N, ∑ y ∈ pts B, β (w • (y + n)) (y + n) := by
        rw [Finset.sum_congr rfl step1, Finset.sum_const, nsmul_eq_mul]
    _ = ∑ y ∈ pts B, ∑ n ∈ pts N, β (w • (y + n)) (y + n) := Finset.sum_comm
    _ = ∑ y ∈ pts B, β (w • y) y * (if ∀ z ∈ N, β y z = 1 then ((pts N).card : ℂ) else 0) :=
        Finset.sum_congr rfl step2
    _ = ((pts N).card : ℂ) * ∑ y ∈ pts N', β (w • y) y := by
        rw [Finset.mul_sum]
        simp_rw [mul_ite, mul_zero]
        rw [← Finset.sum_filter]
        have hf : (pts B).filter (fun y => ∀ z ∈ N, β y z = 1) = pts N' := by
          ext y
          simp [pts, hN']
        rw [hf]
        exact Finset.sum_congr rfl fun y _ => mul_comm _ _

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih => ?_`. Introduce `B C hCB hrad hcard`. Establish `hr : ∀ a b c, β a (b + c) = β a b * β a c` using `fun a b c => by`. Rewrite using `[hsym a, hadd, hsym b, hsym c]`.

Establish `hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1` using `fun c hc y hy => (hrad c (hCB hc)).mp hc y hy`. Establish `hQC : ∀ c ∈ C, β (w • c) c = 1` using `fun c hc => by`. Rewrite using `[hsym]`. Conclude with `hC1 c hc _ (B.smul_mem w (hCB hc))`. Establish `hCpos` using `card_pts_pos C`.

Distinguish the cases in `hBC : C = B`. Substitute `hBC` using the available equality. Establish `hn : n = 1`. Establish `h1 : n * (pts C).card = 1 * (pts C).card` using `by rw [← hcard, one_mul]`. Conclude with `Nat.eq_of_mul_eq_mul_right hCpos h1`.

Substitute `hn` using the available equality. Rewrite using `[Finset.sum_congr rfl fun c hc => hQC c (mem_pts.mp hc)]`. Simplify using the standard rewrite rules. Take `⟨x, hxB, hxC, P, hPm, hP⟩` from `exists_mem_not_mem_annihilator_maximal_of_lt hCB hBC`. Use `haveI : Finite (R ⧸ P) := finite_quot hP`.

Use `letI : Fintype (R ⧸ P) := Fintype.ofFinite _`. Use `set q := Fintype.card (R ⧸ P)`. Establish `hqc : Nat.card (R ⧸ P) = q` using `Nat.card_eq_fintype_card`. Establish `hq2 : 2 ≤ q` using `by haveI : P.IsMaximal := hPm`. Conclude with `Fintype.one_lt_card`.

Take `⟨hlq, hlqσ⟩` from `hlam.2 P hPm inferInstance`. Rewrite `hlq`, `hlqσ` using `[hqc]`. Use `set N := C ⊔ Submodule.span R {x}`. Establish `hNcard : (pts N).card = q * (pts C).card` using `card_sup hP`. Establish `hCN : C ≤ N` using `le_sup_left`.

Establish `hxN : x ∈ N` using `Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)`. Establish `hNB : N ≤ B` using `sup_le hCB (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB)`. Use `set N' := perp hadd hadj h0 B N`. Establish `hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1` using `fun y => Iff.rfl`. Establish `hperp` using `card_perp hadd hsym hCN hNB hrad hN'`.

Establish `hCN' : C ≤ N'` using `fun c hc => (hN' c).mpr ⟨hCB hc, fun z hz => hC1 c hc z (hNB hz)⟩`. Establish `hN'B : N' ≤ B` using `fun y hy => ((hN' y).mp hy).1`. Establish `hBpos` using `card_pts_pos B`. Establish `hnpos : 0 < n`. Break down `Nat.eq_zero_or_pos n with h | h` into its components or cases.

Rewrite `hcard` using `[h, zero_mul]`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hmemN : ∀ z ∈ N, ∃ c ∈ C, ∃ a : R, c + a • x = z`. Introduce `z hz`.

Take `⟨c, hc, y, hy, rfl⟩` from `Submodule.mem_sup.mp hz`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hy`. Conclude with `⟨c, hc, a, rfl⟩`. Distinguish the cases in `hiso : ∀ r : R, β x (r • x) = 1`. Establish `hxN' : x ∈ N'` using `(hN' x).mpr ⟨hxB, fun z hz => by`.

Take `⟨c, hc, a, rfl⟩` from `hmemN z hz`. Rewrite using `[hr, hiso, mul_one, hsym]`. Conclude with `hC1 c hc x hxB⟩`. Establish `hNN' : N ≤ N'` using `sup_le hCN' (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxN')`. Establish `hQN : ∀ z ∈ N, β (w • z) z = 1`.

Introduce `z hz`. Take `⟨c, hc, a, rfl⟩` from `hmemN z hz`. Rewrite using `[quad_add hσ hw hadd hsym hadj, hQC c hc, one_mul, hsym (a • x) c, hC1 c hc _ (B.smul_mem a hxB), mul_one, smul_smul, hadj, smul_smul]`. Conclude with `hiso _`. Take `⟨m, hm⟩` from `card_pts_dvd hNN'`.

Establish `hn : n = q * q * m`. Establish `h1 : (pts C).card * (n * (pts C).card) = q * (pts C).card * m * (q * (pts C).card)`. Rewrite using `[← hcard, hperp, hm, hNcard]`. Establish `h2 : n * ((pts C).card * (pts C).card) = q * q * m * ((pts C).card * (pts C).card)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hCpos hCpos) h2`. Establish `hmpos : 0 < m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Rewrite `hn` using `[h, mul_zero]`. Use linear arithmetic over natural numbers and integers.

Conclude with `h`. Establish `hmn : m < n`. Establish `h4 : 2 * m ≤ q * q * m` using `Nat.mul_le_mul_right m (by nlinarith)`. Use linear arithmetic over natural numbers and integers. Establish `hrad' : ∀ y ∈ N', y ∈ N ↔ ∀ z ∈ N', β y z = 1`.

Introduce `y hy`. Prove the components needed by the constructor for the conclusion. Introduce `hyN z hz`. Rewrite using `[hsym]`. Conclude with `((hN' z).mp hz).2 y hyN`.

Introduce `h`. Establish `hN'' : ∀ u, u ∈ perp hadd hadj h0 B N' ↔ u ∈ B ∧ ∀ z ∈ N', β u z = 1` using `fun u => Iff.rfl`. Establish `h2` using `card_perp hadd hsym hCN' hN'B hrad hN''`. Establish `hNN'' : N ≤ perp hadd hadj h0 B N'` using `fun u hu => (hN'' u).mpr ⟨hNB hu, fun z hz => by rw [hsym]; exact ((hN' z).mp hz).2 u hu⟩`. Establish `hc : (pts (perp hadd hadj h0 B N')).card ≤ (pts N).card`.

Establish `h3 : (pts (perp hadd hadj h0 B N')).card * (pts N').card = (pts N).card * (pts N').card`. Rewrite using `[← h2, hperp, mul_comm]`. Conclude with `(Nat.eq_of_mul_eq_mul_right (card_pts_pos N') h3).le`. Establish `h4` using `eq_of_card_pts hNN'' hc`. Rewrite using `[h4]`.

Conclude with `(hN'' y).mpr ⟨hN'B hy, h⟩`. Take `⟨hs, hl⟩` from `ih m hmn N' N hNN' hrad' (by rw [hm, mul_comm])`. Rewrite using `[sum_pts_eq_sum_pts_orth hσ hw hadd hsym hadj hNB hN' hQN, hs, hNcard, hn]`. Establish `hlq2 : lam q * lam q = q` using `by rw [← sq]; exact hlq`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, hlq2]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, map_mul, mul_pow, mul_pow, hl, hlq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Use `push Not at hiso`. Take `⟨r0, hr0⟩` from `hiso`. Set `χ : R → ℂ` to `fun t => β x (t • x)`. Establish `hχadd : ∀ s t, χ (s + t) = χ s * χ t` using `fun s t => by`.

Simplify using `only [χ]`. Rewrite using `[add_smul, hr]`. Establish `hχ0 : χ 0 = 1`. Simplify using `only [χ]`. Rewrite using `[zero_smul, hsym]`.

Conclude with `h0 x`. Establish `hχP : ∀ t ∈ P, χ t = 1` using `fun t ht => by`. Simplify using `only [χ]`. Rewrite using `[hsym]`. Conclude with `hC1 _ ((hP t).mpr ht) x hxB`.

Establish `hχσ : ∀ t, χ (σ t) = χ t` using `fun t => by`. Simplify using `only [χ]`. Rewrite using `[← hadj, hsym]`. Establish `hσP : ∀ p ∈ P, σ p ∈ P`. Introduce `p hp`.

Assume the negation of the conclusion as `hsp`. Take `⟨y, i, hi, hyi⟩` from `hPm.exists_inv hsp`. Apply `hr0` to reduce the goal to its premises. Use `show χ r0 = 1`. Establish `e1 : r0 = r0 * i + σ (σ (r0 * y) * p)`.

Rewrite using `[map_mul, hσ]`. Take the linear combination `(-r0) * hyi`. Rewrite using `[e1, hχadd, hχP _ (P.mul_mem_left r0 hi), hχσ, hχP _ (P.mul_mem_left _ hp), mul_one]`. Take `⟨hlqv, hex⟩` from `hlqσ hσP`. Establish `hG` using `NormFormGauss.gauss_quotient σ w hσ hw P hPm inferInstance hσP hex χ hχadd hχ0 hχP hχσ ⟨r0, hr0⟩`.

Rewrite `hG` using `[hqc, finsum_eq_sum_of_fintype]`. Establish `hP' : ∀ r, r • x ∈ N' ↔ r ∈ P`. Introduce `r`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Assume the negation of the conclusion as `hrP`. Establish `hsr : σ r ∉ P` using `fun h' => hrP (by rw [← hσ r]; exact hσP _ h')`. Take `⟨y, i, hi, hyi⟩` from `hPm.exists_inv hsr`. Apply `hr0` to reduce the goal to its premises. Use `show χ r0 = 1`.

Establish `e1 : r0 = r0 * i + σ r * (y * r0)` using `by linear_combination (-r0) * hyi`. Rewrite using `[e1, hχadd, hχP _ (P.mul_mem_left r0 hi), one_mul]`. Simplify using `only [χ]`. Rewrite using `[← smul_smul, ← hadj]`. Conclude with `((hN' _).mp h).2 _ (N.smul_mem _ hxN)`.

Introduce `hrP`. Use `(hN' _).mpr ⟨B.smul_mem r hxB, fun z hz => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, a, rfl⟩` from `hmemN z hz`. Rewrite using `[hr, hC1 _ ((hP r).mpr hrP) c (hCB hc), one_mul, hadj, smul_smul]`. Conclude with `hχP _ (P.mul_mem_right a (hσP r hrP))`.

Establish `hsupB : N' ⊔ Submodule.span R {x} = B`. Apply `eq_of_card_pts (sup_le hN'B (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB))` to reduce the goal to its premises. Rewrite using `[card_sup hP']`. Establish `h1 : (pts B).card * (pts C).card = q * (pts N').card * (pts C).card`. Rewrite using `[mul_comm, hperp, hNcard]`.

Expand and normalize the polynomial expressions, which then agree. Conclude with `(Nat.eq_of_mul_eq_mul_right hCpos h1).le`. Take `⟨m, hm⟩` from `card_pts_dvd hCN'`. Establish `hnqm : n = q * m`. Establish `h1 : n * (pts C).card * (pts C).card = q * m * (pts C).card * (pts C).card`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `Nat.eq_of_mul_eq_mul_right hCpos (Nat.eq_of_mul_eq_mul_right hCpos h1)`. Establish `hmpos : 0 < m`. Break down `Nat.eq_zero_or_pos m with h | h` into its components or cases. Rewrite `hnqm` using `[h, mul_zero]`.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `hmn : m < n`. Establish `h4 : 2 * m ≤ q * m` using `Nat.mul_le_mul_right m hq2`. Use linear arithmetic over natural numbers and integers.

Establish `hrad' : ∀ y ∈ N', y ∈ C ↔ ∀ z ∈ N', β y z = 1`. Introduce `y hy`. Prove the components needed by the constructor for the conclusion. Introduce `hyC z hz`. Conclude with `hC1 y hyC z (hN'B hz)`.

Introduce `h`. Use `(hrad y (hN'B hy)).mpr fun b hb => ?_` and prove the remaining obligations. Rewrite `hb` using `[← hsupB]`. Take `⟨d, hd, u, hu, rfl⟩` from `Submodule.mem_sup.mp hb`. Take `⟨a, rfl⟩` from `Submodule.mem_span_singleton.mp hu`.

Rewrite using `[hr, h d hd, one_mul]`. Conclude with `((hN' y).mp hy).2 _ (N.smul_mem a hxN)`. Take `⟨hs, hl⟩` from `ih m hmn N' C hCN' hrad' (by rw [hm, mul_comm])`. Establish `hsum : ∑ y ∈ pts B, β (w • y) y = (∑ d ∈ pts N', β (w • d) d) * ∑ q' : R ⧸ P, χ (w * (Quotient.out q' : R) * σ (Quotient.out q' : R))`. Rewrite using `[← hsupB, sum_sup hP', Finset.sum_comm, Finset.sum_mul_sum]`.

Use `Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun q' _ => ?_` and prove the remaining obligations. Establish `hdN'` using `mem_pts.mp hd`. Rewrite using `[quad_add hσ hw hadd hsym hadj, hsym ((Quotient.out q' : R) • x) d, ((hN' d).mp hdN').2 _ (N.smul_mem _ hxN), mul_one]`. Use `congr 1`. Simplify using `only [χ]`.

Rewrite using `[hsym, hadj, smul_smul, smul_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hsum, hs, hG, hnqm, ← hlqv]`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_mul, mul_pow, hl, hlq]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem gauss_fin {w : R} (hσ : ∀ r, σ (σ r) = r) (hw : w + σ w = 1) {lam : ℕ →* ℂ} (hlam : GoodNorm σ lam)
    (hadd : ∀ x y z, β (x + y) z = β x z * β y z) (hsym : ∀ x y, β x y = β y x)
    (hadj : ∀ (r : R) x y, β (r • x) y = β x (σ r • y)) (h0 : ∀ y, β 0 y = 1) (n : ℕ) :
    ∀ B C : Submodule R M, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → (pts B).card = n * (pts C).card →
      ∑ y ∈ pts B, β (w • y) y = (pts C).card * lam n ∧ lam n ^ 2 = n := by
  induction n using Nat.strong_induction_on with
  | _ n ih => ?_
  intro B C hCB hrad hcard
  have hr : ∀ a b c, β a (b + c) = β a b * β a c := fun a b c => by
    rw [hsym a, hadd, hsym b, hsym c]
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  have hQC : ∀ c ∈ C, β (w • c) c = 1 := fun c hc => by
    rw [hsym]; exact hC1 c hc _ (B.smul_mem w (hCB hc))
  have hCpos := card_pts_pos C
  by_cases hBC : C = B
  · subst hBC
    have hn : n = 1 := by
      have h1 : n * (pts C).card = 1 * (pts C).card := by rw [← hcard, one_mul]
      exact Nat.eq_of_mul_eq_mul_right hCpos h1
    subst hn
    rw [Finset.sum_congr rfl fun c hc => hQC c (mem_pts.mp hc)]
    simp
  obtain ⟨x, hxB, hxC, P, hPm, hP⟩ := exists_mem_not_mem_annihilator_maximal_of_lt hCB hBC
  haveI : Finite (R ⧸ P) := finite_quot hP
  letI : Fintype (R ⧸ P) := Fintype.ofFinite _
  set q := Fintype.card (R ⧸ P)
  have hqc : Nat.card (R ⧸ P) = q := Nat.card_eq_fintype_card
  have hq2 : 2 ≤ q := by
    haveI : P.IsMaximal := hPm
    exact Fintype.one_lt_card
  obtain ⟨hlq, hlqσ⟩ := hlam.2 P hPm inferInstance
  rw [hqc] at hlq hlqσ
  set N := C ⊔ Submodule.span R {x}
  have hNcard : (pts N).card = q * (pts C).card := card_sup hP
  have hCN : C ≤ N := le_sup_left
  have hxN : x ∈ N := Submodule.mem_sup_right (Submodule.mem_span_singleton_self x)
  have hNB : N ≤ B := sup_le hCB (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB)
  set N' := perp hadd hadj h0 B N
  have hN' : ∀ y, y ∈ N' ↔ y ∈ B ∧ ∀ z ∈ N, β y z = 1 := fun y => Iff.rfl
  have hperp := card_perp hadd hsym hCN hNB hrad hN'
  have hCN' : C ≤ N' := fun c hc => (hN' c).mpr ⟨hCB hc, fun z hz => hC1 c hc z (hNB hz)⟩
  have hN'B : N' ≤ B := fun y hy => ((hN' y).mp hy).1
  have hBpos := card_pts_pos B
  have hnpos : 0 < n := by
    rcases Nat.eq_zero_or_pos n with h | h
    · rw [h, zero_mul] at hcard; omega
    · exact h
  have hmemN : ∀ z ∈ N, ∃ c ∈ C, ∃ a : R, c + a • x = z := by
    intro z hz
    obtain ⟨c, hc, y, hy, rfl⟩ := Submodule.mem_sup.mp hz
    obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hy
    exact ⟨c, hc, a, rfl⟩
  by_cases hiso : ∀ r : R, β x (r • x) = 1
  · have hxN' : x ∈ N' := (hN' x).mpr ⟨hxB, fun z hz => by
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [hr, hiso, mul_one, hsym]
      exact hC1 c hc x hxB⟩
    have hNN' : N ≤ N' :=
      sup_le hCN' (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxN')
    have hQN : ∀ z ∈ N, β (w • z) z = 1 := by
      intro z hz
      obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
      rw [quad_add hσ hw hadd hsym hadj, hQC c hc, one_mul, hsym (a • x) c,
        hC1 c hc _ (B.smul_mem a hxB), mul_one, smul_smul, hadj, smul_smul]
      exact hiso _
    obtain ⟨m, hm⟩ := card_pts_dvd hNN'
    have hn : n = q * q * m := by
      have h1 : (pts C).card * (n * (pts C).card) = q * (pts C).card * m * (q * (pts C).card) := by
        rw [← hcard, hperp, hm, hNcard]
      have h2 : n * ((pts C).card * (pts C).card) = q * q * m * ((pts C).card * (pts C).card) := by
        calc n * ((pts C).card * (pts C).card) = (pts C).card * (n * (pts C).card) := by ring
          _ = q * (pts C).card * m * (q * (pts C).card) := h1
          _ = q * q * m * ((pts C).card * (pts C).card) := by ring
      exact Nat.eq_of_mul_eq_mul_right (Nat.mul_pos hCpos hCpos) h2
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hn; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * q * m := Nat.mul_le_mul_right m (by nlinarith)
      omega
    have hrad' : ∀ y ∈ N', y ∈ N ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyN z hz
        rw [hsym]
        exact ((hN' z).mp hz).2 y hyN
      · intro h
        have hN'' : ∀ u, u ∈ perp hadd hadj h0 B N' ↔ u ∈ B ∧ ∀ z ∈ N', β u z = 1 := fun u => Iff.rfl
        have h2 := card_perp hadd hsym hCN' hN'B hrad hN''
        have hNN'' : N ≤ perp hadd hadj h0 B N' := fun u hu =>
          (hN'' u).mpr ⟨hNB hu, fun z hz => by rw [hsym]; exact ((hN' z).mp hz).2 u hu⟩
        have hc : (pts (perp hadd hadj h0 B N')).card ≤ (pts N).card := by
          have h3 : (pts (perp hadd hadj h0 B N')).card * (pts N').card = (pts N).card * (pts N').card := by
            rw [← h2, hperp, mul_comm]
          exact (Nat.eq_of_mul_eq_mul_right (card_pts_pos N') h3).le
        have h4 := eq_of_card_pts hNN'' hc
        rw [h4]
        exact (hN'' y).mpr ⟨hN'B hy, h⟩
    obtain ⟨hs, hl⟩ := ih m hmn N' N hNN' hrad' (by rw [hm, mul_comm])
    rw [sum_pts_eq_sum_pts_orth hσ hw hadd hsym hadj hNB hN' hQN, hs, hNcard, hn]
    have hlq2 : lam q * lam q = q := by rw [← sq]; exact hlq
    refine ⟨?_, ?_⟩
    · rw [map_mul, map_mul, hlq2]
      push_cast
      ring
    · rw [map_mul, map_mul, mul_pow, mul_pow, hl, hlq]
      push_cast
      ring
  · push Not at hiso
    obtain ⟨r0, hr0⟩ := hiso
    let χ : R → ℂ := fun t => β x (t • x)
    have hχadd : ∀ s t, χ (s + t) = χ s * χ t := fun s t => by
      simp only [χ]
      rw [add_smul, hr]
    have hχ0 : χ 0 = 1 := by
      simp only [χ]
      rw [zero_smul, hsym]
      exact h0 x
    have hχP : ∀ t ∈ P, χ t = 1 := fun t ht => by
      simp only [χ]
      rw [hsym]
      exact hC1 _ ((hP t).mpr ht) x hxB
    have hχσ : ∀ t, χ (σ t) = χ t := fun t => by
      simp only [χ]
      rw [← hadj, hsym]
    have hσP : ∀ p ∈ P, σ p ∈ P := by
      intro p hp
      by_contra hsp
      obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsp
      apply hr0
      show χ r0 = 1
      have e1 : r0 = r0 * i + σ (σ (r0 * y) * p) := by
        rw [map_mul, hσ]
        linear_combination (-r0) * hyi
      rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), hχσ, hχP _ (P.mul_mem_left _ hp), mul_one]
    obtain ⟨hlqv, hex⟩ := hlqσ hσP
    have hG := NormFormGauss.gauss_quotient σ w hσ hw P hPm inferInstance hσP hex χ hχadd hχ0 hχP hχσ ⟨r0, hr0⟩
    rw [hqc, finsum_eq_sum_of_fintype] at hG
    have hP' : ∀ r, r • x ∈ N' ↔ r ∈ P := by
      intro r
      constructor
      · intro h
        by_contra hrP
        have hsr : σ r ∉ P := fun h' => hrP (by rw [← hσ r]; exact hσP _ h')
        obtain ⟨y, i, hi, hyi⟩ := hPm.exists_inv hsr
        apply hr0
        show χ r0 = 1
        have e1 : r0 = r0 * i + σ r * (y * r0) := by linear_combination (-r0) * hyi
        rw [e1, hχadd, hχP _ (P.mul_mem_left r0 hi), one_mul]
        simp only [χ]
        rw [← smul_smul, ← hadj]
        exact ((hN' _).mp h).2 _ (N.smul_mem _ hxN)
      · intro hrP
        refine (hN' _).mpr ⟨B.smul_mem r hxB, fun z hz => ?_⟩
        obtain ⟨c, hc, a, rfl⟩ := hmemN z hz
        rw [hr, hC1 _ ((hP r).mpr hrP) c (hCB hc), one_mul, hadj, smul_smul]
        exact hχP _ (P.mul_mem_right a (hσP r hrP))
    have hsupB : N' ⊔ Submodule.span R {x} = B := by
      apply eq_of_card_pts (sup_le hN'B (by rw [Submodule.span_le, Set.singleton_subset_iff]; exact hxB))
      rw [card_sup hP']
      have h1 : (pts B).card * (pts C).card = q * (pts N').card * (pts C).card := by
        rw [mul_comm, hperp, hNcard]
        ring
      exact (Nat.eq_of_mul_eq_mul_right hCpos h1).le
    obtain ⟨m, hm⟩ := card_pts_dvd hCN'
    have hnqm : n = q * m := by
      have h1 : n * (pts C).card * (pts C).card = q * m * (pts C).card * (pts C).card := by
        calc n * (pts C).card * (pts C).card = (pts C).card * (pts B).card := by rw [hcard]; ring
          _ = (pts N').card * (pts N).card := hperp
          _ = q * m * (pts C).card * (pts C).card := by rw [hm, hNcard]; ring
      exact Nat.eq_of_mul_eq_mul_right hCpos (Nat.eq_of_mul_eq_mul_right hCpos h1)
    have hmpos : 0 < m := by
      rcases Nat.eq_zero_or_pos m with h | h
      · rw [h, mul_zero] at hnqm; omega
      · exact h
    have hmn : m < n := by
      have h4 : 2 * m ≤ q * m := Nat.mul_le_mul_right m hq2
      omega
    have hrad' : ∀ y ∈ N', y ∈ C ↔ ∀ z ∈ N', β y z = 1 := by
      intro y hy
      constructor
      · intro hyC z hz
        exact hC1 y hyC z (hN'B hz)
      · intro h
        refine (hrad y (hN'B hy)).mpr fun b hb => ?_
        rw [← hsupB] at hb
        obtain ⟨d, hd, u, hu, rfl⟩ := Submodule.mem_sup.mp hb
        obtain ⟨a, rfl⟩ := Submodule.mem_span_singleton.mp hu
        rw [hr, h d hd, one_mul]
        exact ((hN' y).mp hy).2 _ (N.smul_mem a hxN)
    obtain ⟨hs, hl⟩ := ih m hmn N' C hCN' hrad' (by rw [hm, mul_comm])
    have hsum : ∑ y ∈ pts B, β (w • y) y = (∑ d ∈ pts N', β (w • d) d) *
        ∑ q' : R ⧸ P, χ (w * (Quotient.out q' : R) * σ (Quotient.out q' : R)) := by
      rw [← hsupB, sum_sup hP', Finset.sum_comm, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun d hd => Finset.sum_congr rfl fun q' _ => ?_
      have hdN' := mem_pts.mp hd
      rw [quad_add hσ hw hadd hsym hadj, hsym ((Quotient.out q' : R) • x) d,
        ((hN' d).mp hdN').2 _ (N.smul_mem _ hxN), mul_one]
      congr 1
      simp only [χ]
      rw [hsym, hadj, smul_smul, smul_smul]
      congr 2
      ring
    rw [hsum, hs, hG, hnqm, ← hlqv]
    refine ⟨?_, ?_⟩
    · rw [map_mul]
      push_cast
      ring
    · rw [map_mul, mul_pow, hl, hlq]
      push_cast
      ring

end Fin

/- English proof (translation)
Introduce `R X _ _ _ σ w hσ hw lam hlam β hadd hsym hadj B C hCB hrad n t htB huniq`. Establish `hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1` using `fun c hc y hy => (hrad c (hCB hc)).mp hc y hy`. Set `C' : Submodule R B` to `C.comap B.subtype`. Establish `hC' : ∀ a : B, a ∈ C' ↔ (a : X) ∈ C` using `fun a => Iff.rfl`. Set `e : Fin n → B ⧸ C'` to `fun k => Submodule.Quotient.mk ⟨t k, htB k⟩`.

Establish `he : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Introduce `k l hkl`. Establish `hkl' : (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk ⟨t l, htB l⟩` using `hkl`. Establish `h1 : t k - t l ∈ C`.

Establish `h2` using `(Submodule.Quotient.eq C').mp hkl'`. Rewrite `h2` using `[hC']`. Simplify using `using h2`. Take `⟨k', _, hk'⟩` from `huniq (t k) (htB k)`. Conclude with `(hk' k (by show t k - t k ∈ C; rw [sub_self]; exact C.zero_mem)).trans (hk' l h1).symm`.

Introduce `u`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective C' u`. Take `⟨k, hk, -⟩` from `huniq y y.2`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk y`.

Rewrite using `[Submodule.Quotient.eq, hC', Submodule.coe_sub]`. Establish `h2 : t k - (y : X) = -((y : X) - t k)` using `by abel`. Use `show t k - (y : X) ∈ C`. Rewrite using `[h2]`. Conclude with `C.neg_mem hk`.

Use `haveI : Finite (B ⧸ C') := Finite.of_surjective e he.2`. Use `letI : Fintype (B ⧸ C') := Fintype.ofFinite _`. Establish `hout : ∀ u : B ⧸ C', Submodule.Quotient.mk (Quotient.out u) = u` using `fun u => Quotient.out_eq u`. Establish `hdesc : ∀ a ∈ B, ∀ a' ∈ B, a - a' ∈ C → ∀ b ∈ B, β a b = β a' b`. Introduce `a _ a' _ h b hb`.

Combine the equalities or inequalities in the displayed calculation. Set `β' : B ⧸ C' → B ⧸ C' → ℂ` to `fun u v => β (Quotient.out u : B) (Quotient.out v : B)`. Establish `hrep : ∀ a : B, ((Quotient.out (Submodule.Quotient.mk a : B ⧸ C') : B) : X) - a ∈ C`. Introduce `a`. Establish `h1` using `(Submodule.Quotient.eq C').mp (hout (Submodule.Quotient.mk a))`.

Rewrite `h1` using `[hC']`. Simplify using `using h1`. Establish `hβ' : ∀ a b : B, β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = β a b`. Introduce `a b`. Combine the equalities or inequalities in the displayed calculation.

Establish `hadd' : ∀ u v z : B ⧸ C', β' (u + v) z = β' u z * β' v z`. Introduce `u v z`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective C' u`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective C' v`. Take `⟨c, rfl⟩` from `Submodule.Quotient.mk_surjective C' z`.

Rewrite using `[← Submodule.Quotient.mk_add, hβ', hβ', hβ', Submodule.coe_add, hadd]`. Establish `hsym' : ∀ u v : B ⧸ C', β' u v = β' v u`. Introduce `u v`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective C' u`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective C' v`.

Rewrite using `[hβ', hβ', hsym]`. Establish `hadj' : ∀ (r : R) (u v : B ⧸ C'), β' (r • u) v = β' u (σ r • v)`. Introduce `r u v`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective C' u`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective C' v`.

Rewrite using `[← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hβ', hβ', Submodule.coe_smul, Submodule.coe_smul, hadj]`. Establish `h0' : ∀ v : B ⧸ C', β' 0 v = 1`. Introduce `v`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective C' v`. Rewrite using `[← Submodule.Quotient.mk_zero C', hβ', Submodule.coe_zero]`.

Conclude with `hC1 0 C.zero_mem b b.2`. Establish `hrad' : ∀ u ∈ (⊤ : Submodule R (B ⧸ C')), u ∈ (⊥ : Submodule R (B ⧸ C')) ↔ ∀ v ∈ (⊤ : Submodule R (B ⧸ C')), β' u v = 1`. Introduce `u _`. Take `⟨a, rfl⟩` from `Submodule.Quotient.mk_surjective C' u`. Rewrite using `[Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, hC', hrad a a.2]`.

Prove the components needed by the constructor for the conclusion. Introduce `h v _`. Take `⟨b, rfl⟩` from `Submodule.Quotient.mk_surjective C' v`. Rewrite using `[hβ']`. Conclude with `h b b.2`.

Introduce `h y hy`. Establish `h1` using `h (Submodule.Quotient.mk ⟨y, hy⟩) Submodule.mem_top`. Rewrite `h1` using `[hβ']`. Then use the resulting hypothesis. Establish `hpt : pts (⊤ : Submodule R (B ⧸ C')) = Finset.univ`. Use `ext`.

Simplify using `[pts]`. Establish `hpb : pts (⊥ : Submodule R (B ⧸ C')) = {0}`. Use `ext`. Simplify using `[pts]`. Establish `hcard : (pts (⊤ : Submodule R (B ⧸ C'))).card = n * (pts (⊥ : Submodule R (B ⧸ C'))).card`.

Rewrite using `[hpt, hpb, Finset.card_singleton, mul_one, Finset.card_univ, ← Fintype.card_of_bijective he, Fintype.card_fin]`. Take `⟨hs, hl⟩` from `gauss_fin (w := w) hσ hw hlam hadd' hsym' hadj' h0' n ⊤ ⊥ bot_le hrad' hcard`. Use `⟨?_, hl⟩` and prove the remaining obligations. Rewrite `hs` using `[hpt, hpb, Finset.card_singleton]`. Establish `h1 : ∑ k, β (w • t k) (t k) = ∑ u : B ⧸ C', β' (w • u) u`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Use `show β (w • t k) (t k) = β' (w • Submodule.Quotient.mk ⟨t k, htB k⟩) (Submodule.Quotient.mk ⟨t k, htB k⟩)`. Rewrite using `[← Submodule.Quotient.mk_smul, hβ']`. Both sides reduce to the same expression.

Use `_ = ∑ u : B ⧸ C', β' (w • u) u := he.sum_comp (fun u => β' (w • u) u)`. Rewrite using `[h1, hs]`. Simplify using the standard rewrite rules.
-/
theorem gauss_hermitian : ∀ {R X : Type} [CommRing R] [AddCommGroup X] [Module R X] (σ : R →+* R) (w : R), (∀ r, σ (σ r) = r) → w + σ w = 1 → ∀ lam : ℕ →* ℂ, GoodNorm σ lam → ∀ β : X → X → ℂ, (∀ x y z, β (x + y) z = β x z * β y z) → (∀ x y, β x y = β y x) → (∀ (r : R) x y, β (r • x) y = β x (σ r • y)) → ∀ B C : Submodule R X, C ≤ B → (∀ x ∈ B, x ∈ C ↔ ∀ y ∈ B, β x y = 1) → ∀ (n : ℕ) (t : Fin n → X), (∀ k, t k ∈ B) → (∀ y ∈ B, ∃! k, y - t k ∈ C) → ∑ k, β (w • t k) (t k) = lam n ∧ lam n ^ 2 = n := by
  intro R X _ _ _ σ w hσ hw lam hlam β hadd hsym hadj B C hCB hrad n t htB huniq
  have hC1 : ∀ c ∈ C, ∀ y ∈ B, β c y = 1 := fun c hc y hy => (hrad c (hCB hc)).mp hc y hy
  let C' : Submodule R B := C.comap B.subtype
  have hC' : ∀ a : B, a ∈ C' ↔ (a : X) ∈ C := fun a => Iff.rfl
  let e : Fin n → B ⧸ C' := fun k => Submodule.Quotient.mk ⟨t k, htB k⟩
  have he : Function.Bijective e := by
    constructor
    · intro k l hkl
      have hkl' : (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk ⟨t l, htB l⟩ := hkl
      have h1 : t k - t l ∈ C := by
        have h2 := (Submodule.Quotient.eq C').mp hkl'
        rw [hC'] at h2
        simpa using h2
      obtain ⟨k', _, hk'⟩ := huniq (t k) (htB k)
      exact (hk' k (by show t k - t k ∈ C; rw [sub_self]; exact C.zero_mem)).trans (hk' l h1).symm
    · intro u
      obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective C' u
      obtain ⟨k, hk, -⟩ := huniq y y.2
      refine ⟨k, ?_⟩
      show (Submodule.Quotient.mk ⟨t k, htB k⟩ : B ⧸ C') = Submodule.Quotient.mk y
      rw [Submodule.Quotient.eq, hC', Submodule.coe_sub]
      have h2 : t k - (y : X) = -((y : X) - t k) := by abel
      show t k - (y : X) ∈ C
      rw [h2]
      exact C.neg_mem hk
  haveI : Finite (B ⧸ C') := Finite.of_surjective e he.2
  letI : Fintype (B ⧸ C') := Fintype.ofFinite _
  have hout : ∀ u : B ⧸ C', Submodule.Quotient.mk (Quotient.out u) = u := fun u => Quotient.out_eq u
  have hdesc : ∀ a ∈ B, ∀ a' ∈ B, a - a' ∈ C → ∀ b ∈ B, β a b = β a' b := by
    intro a _ a' _ h b hb
    calc β a b = β (a' + (a - a')) b := by congr 1; abel
      _ = β a' b := by rw [hadd, hC1 _ h b hb, mul_one]
  let β' : B ⧸ C' → B ⧸ C' → ℂ := fun u v => β (Quotient.out u : B) (Quotient.out v : B)
  have hrep : ∀ a : B, ((Quotient.out (Submodule.Quotient.mk a : B ⧸ C') : B) : X) - a ∈ C := by
    intro a
    have h1 := (Submodule.Quotient.eq C').mp (hout (Submodule.Quotient.mk a))
    rw [hC'] at h1
    simpa using h1
  have hβ' : ∀ a b : B, β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b) = β a b := by
    intro a b
    calc β' (Submodule.Quotient.mk a) (Submodule.Quotient.mk b)
        = β a (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) :=
          hdesc _ (Quotient.out (Submodule.Quotient.mk a : B ⧸ C')).2 _ a.2 (hrep a) _
            (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2
      _ = β (Quotient.out (Submodule.Quotient.mk b : B ⧸ C') : B) a := hsym _ _
      _ = β b a := hdesc _ (Quotient.out (Submodule.Quotient.mk b : B ⧸ C')).2 _ b.2 (hrep b) _ a.2
      _ = β a b := hsym _ _
  have hadd' : ∀ u v z : B ⧸ C', β' (u + v) z = β' u z * β' v z := by
    intro u v z
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    obtain ⟨c, rfl⟩ := Submodule.Quotient.mk_surjective C' z
    rw [← Submodule.Quotient.mk_add, hβ', hβ', hβ', Submodule.coe_add, hadd]
  have hsym' : ∀ u v : B ⧸ C', β' u v = β' v u := by
    intro u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [hβ', hβ', hsym]
  have hadj' : ∀ (r : R) (u v : B ⧸ C'), β' (r • u) v = β' u (σ r • v) := by
    intro r u v
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_smul, ← Submodule.Quotient.mk_smul, hβ', hβ', Submodule.coe_smul,
      Submodule.coe_smul, hadj]
  have h0' : ∀ v : B ⧸ C', β' 0 v = 1 := by
    intro v
    obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
    rw [← Submodule.Quotient.mk_zero C', hβ', Submodule.coe_zero]
    exact hC1 0 C.zero_mem b b.2
  have hrad' : ∀ u ∈ (⊤ : Submodule R (B ⧸ C')), u ∈ (⊥ : Submodule R (B ⧸ C')) ↔
      ∀ v ∈ (⊤ : Submodule R (B ⧸ C')), β' u v = 1 := by
    intro u _
    obtain ⟨a, rfl⟩ := Submodule.Quotient.mk_surjective C' u
    rw [Submodule.mem_bot, Submodule.Quotient.mk_eq_zero, hC', hrad a a.2]
    constructor
    · intro h v _
      obtain ⟨b, rfl⟩ := Submodule.Quotient.mk_surjective C' v
      rw [hβ']
      exact h b b.2
    · intro h y hy
      have h1 := h (Submodule.Quotient.mk ⟨y, hy⟩) Submodule.mem_top
      rwa [hβ'] at h1
  have hpt : pts (⊤ : Submodule R (B ⧸ C')) = Finset.univ := by
    ext
    simp [pts]
  have hpb : pts (⊥ : Submodule R (B ⧸ C')) = {0} := by
    ext
    simp [pts]
  have hcard : (pts (⊤ : Submodule R (B ⧸ C'))).card = n * (pts (⊥ : Submodule R (B ⧸ C'))).card := by
    rw [hpt, hpb, Finset.card_singleton, mul_one, Finset.card_univ, ← Fintype.card_of_bijective he,
      Fintype.card_fin]
  obtain ⟨hs, hl⟩ := gauss_fin (w := w) hσ hw hlam hadd' hsym' hadj' h0' n ⊤ ⊥ bot_le hrad' hcard
  refine ⟨?_, hl⟩
  rw [hpt, hpb, Finset.card_singleton] at hs
  have h1 : ∑ k, β (w • t k) (t k) = ∑ u : B ⧸ C', β' (w • u) u := by
    calc ∑ k, β (w • t k) (t k) = ∑ k, β' (w • e k) (e k) := by
          refine Finset.sum_congr rfl fun k _ => ?_
          show β (w • t k) (t k) = β' (w • Submodule.Quotient.mk ⟨t k, htB k⟩) (Submodule.Quotient.mk ⟨t k, htB k⟩)
          rw [← Submodule.Quotient.mk_smul, hβ']
          rfl
      _ = ∑ u : B ⧸ C', β' (w • u) u := he.sum_comp (fun u => β' (w • u) u)
  rw [h1, hs]
  simp

end GlobalTheory.HermitianGauss
