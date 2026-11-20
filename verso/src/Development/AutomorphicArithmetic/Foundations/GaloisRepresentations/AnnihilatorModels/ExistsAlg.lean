import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Establish an intermediate fact.

Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. A detailed English derivation is pending.
-/
private lemma exists_alg {κ B Λ : Type} [Field κ] [CommRing B] [Algebra κ B] [CommRing Λ] [Algebra κ Λ]
    (u : Sp Λ ⟶ Sp B) (h : u ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ)) :
    ∃ ν : B →ₐ[κ] Λ, u = spMap ν.toRingHom := by
  obtain ⟨φ, rfl⟩ : ∃ φ, u = Spec.map φ := ⟨Spec.preimage u, (Spec.map_preimage u).symm⟩
  have hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ Λ := by
    have h' : Spec.map (CommRingCat.ofHom (algebraMap κ B) ≫ φ) =
        Spec.map (CommRingCat.ofHom (algebraMap κ Λ)) := by
      rw [Spec.map_comp]
      exact h
    have h'' := Spec.map_injective h'
    exact congrArg CommRingCat.Hom.hom h''
  refine ⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, ?_⟩
  rfl

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify by unfolding definitions.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Establish an intermediate fact.

Introduce a local definition for the expression. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Prove the components needed by the constructor for the conclusion. Fix the arbitrary inputs or assume the hypotheses.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. By extensionality, compare the relevant components.

Assume the hypotheses and unpack their components. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Establish an intermediate fact.

Simplify by unfolding definitions. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Establish an intermediate fact. Simplify by unfolding definitions.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules. Establish an intermediate fact. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments.

Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify using the standard rewrite rules. Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.infE_of :
    SplitAlg → InfE := by
  intro hS κ _ A _ P d hRep hcard Λ _ _ _ ε g hP hInf
  obtain ⟨B, _, _, hfin, hfree, hrank, i, hmono, hiff⟩ := hRep
  haveI : Mono i := hmono
  have key : ∀ (Λ' : Type) [CommRing Λ'] [Algebra κ Λ'] (ν : B →ₐ[κ] Λ'),
      spMap ν.toRingHom ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ') := by
    intro Λ' _ _ ν
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    congr 2
    ext r
    simp
  have hid : spMap (algebraMap κ κ) = 𝟙 (Sp κ) := by simp [spMap]
  let F : (B →ₐ[κ] κ) → { g // P (𝟙_ (Over (Sp κ))) g } := fun ν =>
    ⟨Over.homMk (U := 𝟙_ (Over (Sp κ))) (V := algPt κ B) (spMap ν.toRingHom)
        (by
          show spMap ν.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _
          rw [key κ ν, hid]) ≫ i,
      (hiff _ _).1 ⟨_, rfl⟩⟩
  have hF : Function.Bijective F := by
    constructor
    · intro ν₁ ν₂ h
      have h1 := congrArg Subtype.val h
      have h2 := (cancel_mono i).1 h1
      have h3 := congrArg CommaMorphism.left h2
      have h4 : CommRingCat.ofHom ν₁.toRingHom = CommRingCat.ofHom ν₂.toRingHom :=
        Spec.map_injective h3
      ext x
      exact congrArg (fun φ => φ.hom x) h4
    · rintro ⟨g₀, hg₀⟩
      obtain ⟨y, hy⟩ := (hiff _ _).2 hg₀
      obtain ⟨ν, hν⟩ := exists_alg (Λ := κ) y.left (by
        rw [hid]
        exact Over.w y)
      refine ⟨ν, Subtype.ext ?_⟩
      show _ ≫ i = g₀
      rw [← hy]
      congr 1
      apply Over.OverMorphism.ext
      simp [hν]
  have hpts : Nat.card (B →ₐ[κ] κ) = Module.finrank κ B := by
    rw [hrank, ← hcard]
    exact Nat.card_congr (Equiv.ofBijective F hF)
  obtain ⟨y, hy⟩ := (hiff _ _).2 hP
  obtain ⟨ν, hν⟩ := exists_alg y.left (Over.w y)
  have hsplit := hS κ B Λ hpts ε ν
  have e1 : spMap ν.toRingHom = spMap (algebraMap κ Λ) ≫ spMap (ε.comp ν).toRingHom := by
    conv_lhs => rw [hsplit]
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rfl
  have e2 : spMap ε.toRingHom ≫ spMap (algebraMap κ Λ) = 𝟙 (Sp κ) := by
    dsimp only [spMap]
    rw [← Spec.map_comp, ← CommRingCat.ofHom_comp]
    rw [show ε.toRingHom.comp (algebraMap κ Λ) = RingHom.id κ from by ext r; simp]
    simp
  have gl : g.left = y.left ≫ i.left := by
    rw [← hy]
    rfl
  have one_l : ∀ T : Over (Sp κ), (1 : T ⟶ A).left = T.hom ≫ η[A].left := by
    intro T
    show (toUnit T ≫ η[A]).left = _
    rw [Over.comp_left]
    congr 1
  have hI : spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left := hInf
  rw [one_l, gl, hν, e1] at hI
  simp only [← Category.assoc, e2, Category.id_comp] at hI
  apply Over.OverMorphism.ext
  rw [one_l, gl, hν, e1, Category.assoc, hI]
  rfl
