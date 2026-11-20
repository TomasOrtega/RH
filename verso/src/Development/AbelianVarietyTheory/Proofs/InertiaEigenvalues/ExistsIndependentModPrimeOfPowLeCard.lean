import Mathlib
open Polynomial

namespace GlobalTheory

/- English proof (translation)
Establish `hl1 : 1 < l` using `(Fact.out : l.Prime).one_lt`. Establish `hs : (Z.image w).card = Z.card` using `Finset.card_image_of_injOn hinj`. Take `⟨b, hbs, hspan, hli⟩` from `exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)`. Establish `hbfin : b.Finite` using `(Finset.finite_toSet _).subset hbs`. Use `haveI : Fintype b := hbfin.fintype`.

Establish `hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y`. Introduce `y hy`. Establish `hy' : y ∈ Submodule.span (ZMod l) b`. Rewrite using `[hspan]; exact Submodule.subset_span (by exact_mod_cast hy)`. Rewrite `hy'` using `[← Subtype.range_coe (s := b)]`.

Conclude with `(Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'`. Establish `hle : (Z.image w).card ≤ l ^ Fintype.card b`. Establish `h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card`. Apply `Finset.card_le_card` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨f, hf⟩` from `hrange y hy`. Conclude with `Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩`. Combine the equalities or inequalities in the displayed calculation. Establish `hhb : h ≤ Fintype.card b`. Establish `: l ^ h ≤ l ^ Fintype.card b` using `hcard.trans (hs ▸ hle)`.

Conclude with `(Nat.pow_le_pow_iff_right hl1).1 this`. Set `e : Fin h ↪ b` to `(Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding`. Establish `hpre : ∀ c : b, ∃ i ∈ Z, w i = c` using `fun c => Finset.mem_image.1 (hbs c.2)`. Use `choose g hgZ hgw using hpre`. Use `⟨fun a => g (e a), fun a => hgZ _, ?_⟩` and prove the remaining obligations.

Establish `hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q))` using `hli.comp e e.injective`. Use `hli' using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `a`. Conclude with `hgw (e a)`.
-/
theorem exists_linearIndependent_of_pow_le_card_zmod (l : ℕ) [Fact l.Prime] {Q ι : Type} [AddCommGroup Q] [Module (ZMod l) Q]
    (Z : Finset ι) (w : ι → Q) (hinj : Set.InjOn w Z) (h : ℕ) (hcard : l ^ h ≤ Z.card) :
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ LinearIndependent (ZMod l) (fun a => w (x a)) := by
  classical
  have hl1 : 1 < l := (Fact.out : l.Prime).one_lt
  have hs : (Z.image w).card = Z.card := Finset.card_image_of_injOn hinj
  obtain ⟨b, hbs, hspan, hli⟩ := exists_linearIndependent (ZMod l) ((Z.image w : Finset Q) : Set Q)
  have hbfin : b.Finite := (Finset.finite_toSet _).subset hbs
  haveI : Fintype b := hbfin.fintype
  have hrange : ∀ y ∈ Z.image w, ∃ f : b → ZMod l, ∑ c, f c • (c : Q) = y := by
    intro y hy
    have hy' : y ∈ Submodule.span (ZMod l) b := by
      rw [hspan]; exact Submodule.subset_span (by exact_mod_cast hy)
    rw [← Subtype.range_coe (s := b)] at hy'
    exact (Submodule.mem_span_range_iff_exists_fun (ZMod l)).1 hy'
  have hle : (Z.image w).card ≤ l ^ Fintype.card b := by
    have h3 : (Z.image w).card ≤ (Finset.univ.image (fun f : b → ZMod l => ∑ c, f c • (c : Q))).card := by
      apply Finset.card_le_card
      intro y hy
      obtain ⟨f, hf⟩ := hrange y hy
      exact Finset.mem_image.2 ⟨f, Finset.mem_univ _, hf⟩
    calc _ ≤ _ := h3
      _ ≤ (Finset.univ : Finset (b → ZMod l)).card := Finset.card_image_le
      _ = l ^ Fintype.card b := by rw [Finset.card_univ, Fintype.card_fun, ZMod.card]
  have hhb : h ≤ Fintype.card b := by
    have : l ^ h ≤ l ^ Fintype.card b := hcard.trans (hs ▸ hle)
    exact (Nat.pow_le_pow_iff_right hl1).1 this
  let e : Fin h ↪ b := (Fin.castLEEmb hhb).trans (Fintype.equivFin b).symm.toEmbedding
  have hpre : ∀ c : b, ∃ i ∈ Z, w i = c := fun c => Finset.mem_image.1 (hbs c.2)
  choose g hgZ hgw using hpre
  refine ⟨fun a => g (e a), fun a => hgZ _, ?_⟩
  have hli' : LinearIndependent (ZMod l) (fun a => ((e a : b) : Q)) := hli.comp e e.injective
  convert hli' using 1
  funext a
  exact hgw (e a)

/- English proof (translation)
Introduce `l _ V ι _ K' h Z v hl hcard hdist`. Establish `hQ : ∀ y : V ⧸ K', l • y = 0`. Introduce `y`. Proceed by induction on `y using QuotientAddGroup.induction_on with`. Consider the case `H z => rw [← QuotientAddGroup.mk_nsmul, hl z]`.

Both sides reduce to the same expression. Use `letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ`. Establish `hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z`. Introduce `i hi i' hi' he`. Assume the negation of the conclusion as `hne`.

Conclude with `hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)`. Take `⟨x, hxZ, hli⟩` from `exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard`. Use `⟨x, hxZ, ?_⟩` and prove the remaining obligations. Introduce `n hn a`. Establish `hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0` using `(QuotientAddGroup.eq_zero_iff _).2 hn`.

Rewrite `hm` using `[map_sum]`. Simplify using `only [map_nsmul, QuotientAddGroup.mk'_apply] at hm`. Establish `hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0`. Rewrite using `[← hm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[Nat.cast_smul_eq_nsmul]`. Establish `hz` using `Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a`. Conclude with `(ZMod.natCast_eq_zero_iff _ _).1 hz`.
-/
theorem ph_a_basis : ∀ (l : ℕ) [Fact l.Prime] (V ι : Type) [AddCommGroup V] (K' : AddSubgroup V) (h : ℕ)
    (Z : Finset ι) (v : ι → V), (∀ x : V, l • x = 0) → l ^ h ≤ Z.card →
    (∀ i ∈ Z, ∀ i' ∈ Z, i ≠ i' → v i - v i' ∉ K') →
    ∃ x : Fin h → ι, (∀ a, x a ∈ Z) ∧ ∀ n : Fin h → ℕ, ∑ a, n a • v (x a) ∈ K' → ∀ a, l ∣ n a := by
  intro l _ V ι _ K' h Z v hl hcard hdist
  have hQ : ∀ y : V ⧸ K', l • y = 0 := by
    intro y
    induction y using QuotientAddGroup.induction_on with
    | H z => rw [← QuotientAddGroup.mk_nsmul, hl z]; rfl
  letI : Module (ZMod l) (V ⧸ K') := AddCommGroup.zmodModule hQ
  have hinj : Set.InjOn (fun i => (v i : V ⧸ K')) Z := by
    intro i hi i' hi' he
    by_contra hne
    exact hdist i hi i' hi' hne ((QuotientAddGroup.eq_iff_sub_mem).1 he)
  obtain ⟨x, hxZ, hli⟩ := exists_linearIndependent_of_pow_le_card_zmod l Z (fun i => (v i : V ⧸ K')) hinj h hcard
  refine ⟨x, hxZ, ?_⟩
  intro n hn a
  have hm : QuotientAddGroup.mk' K' (∑ a, n a • v (x a)) = 0 := (QuotientAddGroup.eq_zero_iff _).2 hn
  rw [map_sum] at hm
  simp only [map_nsmul, QuotientAddGroup.mk'_apply] at hm
  have hsum : ∑ a, (n a : ZMod l) • ((v (x a) : V ⧸ K')) = 0 := by
    rw [← hm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Nat.cast_smul_eq_nsmul]
  have hz := Fintype.linearIndependent_iff.1 hli (fun a => (n a : ZMod l)) hsum a
  exact (ZMod.natCast_eq_zero_iff _ _).1 hz

end GlobalTheory
