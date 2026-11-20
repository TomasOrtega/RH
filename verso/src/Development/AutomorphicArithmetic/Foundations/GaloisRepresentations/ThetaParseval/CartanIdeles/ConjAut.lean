import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.CartanIdeles.SpacesExOf

open scoped nonZeroDivisors Matrix
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.Gal.TP.Skew

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hσ`. Take `⟨_, hE, h2, hconj⟩` from `hσ`. Use `haveI hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2`. Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩`. Establish `hgal : IsGalois F E` using `inferInstance`.

Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`. Establish `hsq : ∀ x, σ (σ x) = x` using `fun x => τ.injective (by rw [hconj, hconj, star_star])`. Establish `hsurj : Function.Surjective σ` using `fun x => ⟨σ x, hsq x⟩`. Set `s : Gal(E/F)` to `AlgEquiv.ofBijective σ ⟨σ.toRingHom.injective, hsurj⟩`. Establish `hs : ∀ x, s x = σ x` using `fun x => rfl`.

Establish `hne : ∃ x, σ x ≠ x`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `IsTotallyComplex.complexEmbedding_not_isReal τ` to reduce the goal to its premises. Use `show star τ = τ`.

Use extensionality with `x`. Use `hconj τ x` as an intermediate fact. Rewrite `this` using `[h x]`. Simplify using `using this.symm`. Take `⟨x, hx⟩` from `hne`.

Establish `hs1 : s ≠ 1` using `fun h => hx (by rw [← hs, h]; rfl)`. Establish `hcard : Fintype.card Gal(E/F) = 2`. Rewrite using `[← h2, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]`. Use `⟨hgal, s, hs, hs1, ?_, ?_, σ x - x, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `y`.

Simplify using `[hs, hsq]`. Introduce `g`. Assume the negation of the conclusion as `hg`. Use `push_neg at hg`. Establish `hle : ({1, s, g} : Finset Gal(E/F)).card ≤ Fintype.card Gal(E/F)` using `Finset.card_le_univ _`.

Rewrite `hle` using `[Finset.card_insert_of_notMem (by simp [hs1.symm, hg.1.symm]), Finset.card_pair hg.2.symm, hcard]`. Use linear arithmetic over natural numbers and integers. Conclude with `sub_ne_zero.mpr hx`. Rewrite using `[map_sub, hsq]`. Normalize the expressions using the abelian group laws.
-/
theorem UpperTheory.Gal.TP.Skew.conjAut :
    UpperTheory.Gal.TP.Skew.ConjAut := by
  classical
  intro F E _ _ _ _ _ σ hσ
  obtain ⟨_, hE, h2, hconj⟩ := hσ
  haveI hfin : FiniteDimensional F E := Module.finite_of_finrank_eq_succ h2
  haveI : Algebra.IsQuadraticExtension F E := ⟨h2⟩
  have hgal : IsGalois F E := inferInstance
  obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
  have hsq : ∀ x, σ (σ x) = x := fun x => τ.injective (by rw [hconj, hconj, star_star])
  have hsurj : Function.Surjective σ := fun x => ⟨σ x, hsq x⟩
  let s : Gal(E/F) := AlgEquiv.ofBijective σ ⟨σ.toRingHom.injective, hsurj⟩
  have hs : ∀ x, s x = σ x := fun x => rfl
  have hne : ∃ x, σ x ≠ x := by
    by_contra h
    push_neg at h
    apply IsTotallyComplex.complexEmbedding_not_isReal τ
    show star τ = τ
    ext x
    have := hconj τ x
    rw [h x] at this
    simpa using this.symm
  obtain ⟨x, hx⟩ := hne
  have hs1 : s ≠ 1 := fun h => hx (by rw [← hs, h]; rfl)
  have hcard : Fintype.card Gal(E/F) = 2 := by
    rw [← h2, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
  refine ⟨hgal, s, hs, hs1, ?_, ?_, σ x - x, ?_, ?_⟩
  · ext y
    simp [hs, hsq]
  · intro g
    by_contra hg
    push_neg at hg
    have hle : ({1, s, g} : Finset Gal(E/F)).card ≤ Fintype.card Gal(E/F) := Finset.card_le_univ _
    rw [Finset.card_insert_of_notMem (by simp [hs1.symm, hg.1.symm]),
      Finset.card_pair hg.2.symm, hcard] at hle
    omega
  · exact sub_ne_zero.mpr hx
  · rw [map_sub, hsq]
    abel
