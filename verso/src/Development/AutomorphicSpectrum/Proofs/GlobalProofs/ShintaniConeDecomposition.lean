import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.SiegelKlingenDeligneRibet
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.AbelContinuation
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CongSubgroup

set_option autoImplicit false

noncomputable section

open NumberField NumberField.Units NumberField.Units.dirichletUnitTheorem GlobalTheory.CompanionTheory.Hypotheses₂.Shintani GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

namespace GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones

/- English proof (translation)
Rewrite using `[← Finset.sum_coe_sort s f]`. Conclude with `Equiv.sum_comp s.equivFin.symm (fun y : s => f (y : F))`.
-/
theorem sum_equivFin_symm {F M : Type} [AddCommMonoid M] (s : Finset F) (f : F → M) :
    ∑ i : Fin s.card, f (s.equivFin.symm i : F) = ∑ y ∈ s, f y := by
  rw [← Finset.sum_coe_sort s f]
  exact Equiv.sum_comp s.equivFin.symm (fun y : s => f (y : F))

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨t, ht, rfl⟩`. Use `⟨fun y => if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`.

Simplify using `only [dif_pos hy]`. Conclude with `ht _`. Rewrite using `[← sum_equivFin_symm s (fun y => (if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1 : ℚ) • y)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hm : (s.equivFin.symm i : F) ∈ s` using `(s.equivFin.symm i).2`.

Simplify using `only [dif_pos hm, Subtype.coe_eta, Equiv.apply_symm_apply]`. Rewrite using `[Rat.smul_def]`. Introduce and unpack `⟨t, ht, rfl⟩`. Use `⟨fun i => t (s.equivFin.symm i : F), fun i => ht _ (s.equivFin.symm i).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← sum_equivFin_symm s (fun y => t y • y)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def]`.
-/
theorem openCone_equivFin {F : Type} [Field F] [CharZero F] (s : Finset F) :
    openCone (fun i : Fin s.card => (s.equivFin.symm i : F)) = coneOn s := by
  classical
  ext x
  constructor
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun y => if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1, ?_, ?_⟩
    · intro y hy
      simp only [dif_pos hy]
      exact ht _
    · rw [← sum_equivFin_symm s (fun y => (if h : y ∈ s then t (s.equivFin ⟨y, h⟩) else 1 : ℚ) • y)]
      refine Finset.sum_congr rfl fun i _ => ?_
      have hm : (s.equivFin.symm i : F) ∈ s := (s.equivFin.symm i).2
      simp only [dif_pos hm, Subtype.coe_eta, Equiv.apply_symm_apply]
      rw [Rat.smul_def]
  · rintro ⟨t, ht, rfl⟩
    refine ⟨fun i => t (s.equivFin.symm i : F), fun i => ht _ (s.equivFin.symm i).2, ?_⟩
    rw [← sum_equivFin_symm s (fun y => t y • y)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Rat.smul_def]

/- English proof (translation)
Proceed by induction on `h with`. Consider the case `empty`. Introduce `_`. Conclude with `⟨Empty, inferInstance, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun x hx => hx.elim⟩`. Consider the case `cone s hli hP hQ`.

Introduce `h0`. Establish `hcone` using `openCone_equivFin s`. Use `⟨Unit, inferInstance, fun _ => s.card, fun _ i => (s.equivFin.symm i : F), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `_`. Use `Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)` and prove the remaining obligations.

Introduce and unpack `rfl`. Conclude with `h0 ⟨fun _ => 0, by simp, by simp⟩`. Introduce `_`. Establish `hinj : Function.Injective (fun i : Fin s.card => (⟨(s.equivFin.symm i : F), (s.equivFin.symm i).2⟩ : (s : Set F)))`. Introduce `i j hij`.

Conclude with `s.equivFin.symm.injective (Subtype.ext (congrArg Subtype.val hij))`. Conclude with `LinearIndependent.comp hli _ hinj`. Introduce `_ i`. Conclude with `hP (s.equivFin.symm i).2`. Introduce `_`.

Conclude with `hcone.le`. Introduce `x hx`. Conclude with `⟨(), hcone.ge hx, fun _ _ => rfl⟩`. Consider the case `@union A B _ _ hAB ihA ihB`. Introduce `h0`.

Take `⟨ι₁, f₁, r₁, v₁, hr₁, hl₁, hp₁, hs₁, hu₁⟩` from `ihA (fun h => h0 (Or.inl h))`. Take `⟨ι₂, f₂, r₂, v₂, hr₂, hl₂, hp₂, hs₂, hu₂⟩` from `ihB (fun h => h0 (Or.inr h))`. Use `⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim r₁ r₂, fun c => match c with` and prove the remaining obligations. Consider the case `Sum.inl a => v₁ a`. Consider the case `Sum.inr b => v₂ b, ?_, ?_, ?_, ?_, ?_⟩`.

Introduce and unpack `(a | b)`. Conclude with `hr₁ a`. Conclude with `hr₂ b`. Introduce and unpack `(a | b)`. Conclude with `hl₁ a`.

Conclude with `hl₂ b`. Introduce and unpack `(a | b) i`. Conclude with `hp₁ a i`. Conclude with `hp₂ b i`. Introduce and unpack `(a | b)`.

Conclude with `(hs₁ a).trans Set.subset_union_left`. Conclude with `(hs₂ b).trans Set.subset_union_right`. Introduce and unpack `x (hx | hx)`. Take `⟨a, ha, hu⟩` from `hu₁ x hx`. Use `⟨Sum.inl a, ha, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(a' | b') h'`. Conclude with `congrArg Sum.inl (hu a' h')`. Conclude with `(Set.disjoint_left.mp hAB hx (hs₂ b' h')).elim`. Take `⟨b, hb, hu⟩` from `hu₂ x hx`. Use `⟨Sum.inr b, hb, ?_⟩` and prove the remaining obligations.

Introduce and unpack `(a' | b') h'`. Conclude with `(Set.disjoint_left.mp hAB (hs₁ a' h') hx).elim`. Conclude with `congrArg Sum.inr (hu b' h')`.
-/
theorem tile_family {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F) (h : Tile P Q C) :
    (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) := by
  induction h with
  | empty =>
    intro _
    exact ⟨Empty, inferInstance, fun c => c.elim, fun c => c.elim, fun c => c.elim, fun c => c.elim,
      fun c => c.elim, fun c => c.elim, fun x hx => hx.elim⟩
  | cone s hli hP hQ =>
    intro h0
    have hcone := openCone_equivFin s
    refine ⟨Unit, inferInstance, fun _ => s.card, fun _ i => (s.equivFin.symm i : F), ?_, ?_, ?_, ?_, ?_⟩
    · intro _
      refine Finset.card_pos.mpr (Finset.nonempty_iff_ne_empty.mpr ?_)
      rintro rfl
      exact h0 ⟨fun _ => 0, by simp, by simp⟩
    · intro _
      have hinj : Function.Injective (fun i : Fin s.card => (⟨(s.equivFin.symm i : F), (s.equivFin.symm i).2⟩ : (s : Set F))) := by
        intro i j hij
        exact s.equivFin.symm.injective (Subtype.ext (congrArg Subtype.val hij))
      exact LinearIndependent.comp hli _ hinj
    · intro _ i
      exact hP (s.equivFin.symm i).2
    · intro _
      exact hcone.le
    · intro x hx
      exact ⟨(), hcone.ge hx, fun _ _ => rfl⟩
  | @union A B _ _ hAB ihA ihB =>
    intro h0
    obtain ⟨ι₁, f₁, r₁, v₁, hr₁, hl₁, hp₁, hs₁, hu₁⟩ := ihA (fun h => h0 (Or.inl h))
    obtain ⟨ι₂, f₂, r₂, v₂, hr₂, hl₂, hp₂, hs₂, hu₂⟩ := ihB (fun h => h0 (Or.inr h))
    refine ⟨ι₁ ⊕ ι₂, inferInstance, Sum.elim r₁ r₂,
      fun c => match c with
        | Sum.inl a => v₁ a
        | Sum.inr b => v₂ b, ?_, ?_, ?_, ?_, ?_⟩
    · rintro (a | b)
      · exact hr₁ a
      · exact hr₂ b
    · rintro (a | b)
      · exact hl₁ a
      · exact hl₂ b
    · rintro (a | b) i
      · exact hp₁ a i
      · exact hp₂ b i
    · rintro (a | b)
      · exact (hs₁ a).trans Set.subset_union_left
      · exact (hs₂ b).trans Set.subset_union_right
    · rintro x (hx | hx)
      · obtain ⟨a, ha, hu⟩ := hu₁ x hx
        refine ⟨Sum.inl a, ha, ?_⟩
        rintro (a' | b') h'
        · exact congrArg Sum.inl (hu a' h')
        · exact (Set.disjoint_left.mp hAB hx (hs₂ b' h')).elim
      · obtain ⟨b, hb, hu⟩ := hu₂ x hx
        refine ⟨Sum.inr b, hb, ?_⟩
        rintro (a' | b') h'
        · exact (Set.disjoint_left.mp hAB (hs₁ a' h') hx).elim
        · exact congrArg Sum.inr (hu b' h')

/- English proof (translation)
Introduce `P Q C h` and use `tile_family P Q C h`.
-/
theorem tile_family_closed : ∀ {F : Type} [Field F] [NumberField F] (P : Set F) (Q : Set F → Prop) (C : Set F), Tile P Q C → (0 : F) ∉ C →
    ∃ (ι : Type) (_ : Fintype ι) (r : ι → ℕ) (v : ∀ c, Fin (r c) → F), (∀ c, 0 < r c) ∧
      (∀ c, LinearIndependent ℚ (v c)) ∧ (∀ c i, v c i ∈ P) ∧ (∀ c, openCone (v c) ⊆ C) ∧
      ∀ x ∈ C, ∃! c, x ∈ openCone (v c) :=
  fun P Q C h => tile_family P Q C h

end GlobalTheory.CompanionTheory.Hypotheses₂.Shintani.Cones
