import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
open NumberField Matrix GlobalTheory.Mass Formalism.HermitianLatticesTheory
open scoped ENNReal Classical

namespace GlobalTheory.Mass.Slice

/- English proof (translation)
Establish `h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x` using `Quotient.exact (Quotient.out_eq _)`. Conclude with `MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)`.
-/
theorem exists_smul_eq_out (G : Type) {α : Type} [Group G] [MulAction G α] (x : α) :
    ∃ g : G, g • x = Quotient.out (Quotient.mk (MulAction.orbitRel G α) x) := by
  have h : (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel G α) x)) x :=
    Quotient.exact (Quotient.out_eq _)
  exact MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h)

/- English proof (translation)
Establish `h : (MulAction.orbitRel G α) (g • x) x` using `MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)`. Conclude with `ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv`.
-/
theorem card_stabilizer_smul (G : Type) {α : Type} [Group G] [MulAction G α] (g : G) (x : α) :
    ENat.card (MulAction.stabilizer G (g • x)) = ENat.card (MulAction.stabilizer G x) := by
  have h : (MulAction.orbitRel G α) (g • x) x :=
    MulAction.orbitRel_apply.mpr (MulAction.mem_orbit x g)
  exact ENat.card_congr (MulAction.stabilizerEquivStabilizerOfOrbitRel h).toEquiv

/- English proof (translation)
The claim follows from `ENat.card_congr { toFun := fun a => ⟨(a.1 : G), a.2⟩ invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩ left_inv := fun _ => rfl right_inv := fun _ => rfl }`.
-/
theorem card_stabilizer_subgroup {G α : Type} [Group G] [MulAction G α] (H : Subgroup G) (x : α)
    (h : ∀ g : G, g • x = x → g ∈ H) :
    ENat.card (MulAction.stabilizer H x) = ENat.card (MulAction.stabilizer G x) :=
  ENat.card_congr
    { toFun := fun a => ⟨(a.1 : G), a.2⟩
      invFun := fun a => ⟨⟨a.1, h a.1 a.2⟩, a.2⟩
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl }

/- English proof (translation)
Introduce `G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret`. Set `f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} → {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X}` to `fun q => ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by`. Take `⟨g, hg⟩` from `exists_smul_eq_out G (Quotient.out q.1)`. Rewrite using `[← hg]`. Conclude with `hX g _ (hsub q.2)⟩`.

Establish `hinj : Function.Injective f`. Introduce `a b hab`. Establish `h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1)` using `Quotient.exact (congrArg Subtype.val hab)`. Take `⟨g, hg⟩` from `MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)`. Establish `hgH : g ∈ H` using `hret g _ b.2 (hg ▸ a.2)`.

Establish `h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1)` using `MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)`. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← Quotient.out_eq a.1, ← Quotient.out_eq b.1]`. Conclude with `Quotient.sound h2`. Establish `hsurj : Function.Surjective f`.

Introduce `b`. Take `⟨g, hg⟩` from `hmeet _ b.2`. Take `⟨k, hk⟩` from `exists_smul_eq_out H (g • Quotient.out b.1)`. Use `⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk]`.

Conclude with `hX₀ k _ hg`. Apply `Subtype.ext show Quotient.mk (MulAction.orbitRel G α) (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1` to reduce the goal to its premises. Rewrite using `[← hk]`. Use `conv_rhs => rw [← Quotient.out_eq b.1]`. Apply `Quotient.sound` to reduce the goal to its premises.

Use `MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)` and prove the remaining obligations. Rewrite using `[mul_smul]`. Both sides reduce to the same expression. Unfold `orbSum`. Rewrite using `[← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]`.

Use `tsum_congr fun q => ?_` and prove the remaining obligations. Take `⟨g, hg⟩` from `exists_smul_eq_out G (Quotient.out q.1)`. Establish `e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1` using `hg.symm`. Rewrite using `[e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _ (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]`.
-/
theorem orbSum_restrict : ∀ (G α : Type) [Group G] [MulAction G α] (H : Subgroup G) (X X₀ : Set α) (N : α → ℝ≥0∞), X₀ ⊆ X → Stable G X → Stable H X₀ → (∀ (g : G) x, N (g • x) = N x) → (∀ x ∈ X, ∃ g : G, g • x ∈ X₀) → (∀ (g : G), ∀ x ∈ X₀, g • x ∈ X₀ → g ∈ H) → orbSum H X₀ N = orbSum G X N := by
  intro G α _ _ H X X₀ N hsub hX hX₀ hN hmeet hret
  let f : {q : MulAction.orbitRel.Quotient H α // Quotient.out q ∈ X₀} →
      {q : MulAction.orbitRel.Quotient G α // Quotient.out q ∈ X} := fun q =>
    ⟨Quotient.mk (MulAction.orbitRel G α) (Quotient.out q.1), by
      obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
      rw [← hg]
      exact hX g _ (hsub q.2)⟩
  have hinj : Function.Injective f := by
    intro a b hab
    have h1 : (MulAction.orbitRel G α) (Quotient.out a.1) (Quotient.out b.1) :=
      Quotient.exact (congrArg Subtype.val hab)
    obtain ⟨g, hg⟩ := MulAction.mem_orbit_iff.mp (MulAction.orbitRel_apply.mp h1)
    have hgH : g ∈ H := hret g _ b.2 (hg ▸ a.2)
    have h2 : (MulAction.orbitRel H α) (Quotient.out a.1) (Quotient.out b.1) :=
      MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨⟨g, hgH⟩, hg⟩)
    apply Subtype.ext
    rw [← Quotient.out_eq a.1, ← Quotient.out_eq b.1]
    exact Quotient.sound h2
  have hsurj : Function.Surjective f := by
    intro b
    obtain ⟨g, hg⟩ := hmeet _ b.2
    obtain ⟨k, hk⟩ := exists_smul_eq_out H (g • Quotient.out b.1)
    refine ⟨⟨Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1), ?_⟩, ?_⟩
    · rw [← hk]; exact hX₀ k _ hg
    · apply Subtype.ext
      show Quotient.mk (MulAction.orbitRel G α)
        (Quotient.out (Quotient.mk (MulAction.orbitRel H α) (g • Quotient.out b.1))) = b.1
      rw [← hk]
      conv_rhs => rw [← Quotient.out_eq b.1]
      apply Quotient.sound
      refine MulAction.orbitRel_apply.mpr (MulAction.mem_orbit_iff.mpr ⟨(k : G) * g, ?_⟩)
      rw [mul_smul]; rfl
  unfold orbSum
  rw [← (Equiv.ofBijective f ⟨hinj, hsurj⟩).tsum_eq]
  refine tsum_congr fun q => ?_
  obtain ⟨g, hg⟩ := exists_smul_eq_out G (Quotient.out q.1)
  have e : Quotient.out ((Equiv.ofBijective f ⟨hinj, hsurj⟩) q).1 = g • Quotient.out q.1 := hg.symm
  rw [e, hN, card_stabilizer_smul, card_stabilizer_subgroup H _
    (fun a ha => hret a _ q.2 (by rw [ha]; exact q.2))]

end GlobalTheory.Mass.Slice
