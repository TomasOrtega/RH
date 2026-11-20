import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.PairCalc
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GeomClausesIff

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Establish `key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq, Category.assoc]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← key, MulEquiv.map_eq_one_iff]`.

Rewrite using `[MulEquiv.map_eq_one_iff]`. Introduce `I`. Unfold `KilledBy`. Use `forall_congr' fun a => imp_congr_right fun _ => ?_` and prove the remaining obligations. Rewrite using `[← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]`.
-/
private theorem pt_core {p : ℕ} [Fact p.Prime] {D : Datum p} {R : Type} [CommRing R] {b : Base D R} {N : ℕ}
    {S S' : Scheme.{0}} {s : S ⟶ Sp R} {s' : S' ⟶ Sp R} {f : S' ⟶ S} {o o' : Obj b N s} {o₁ o₁' : Obj b N s'}
    (m : ObjMap o₁ o f) (m' : ObjMap o₁' o' f) (ψ : o.A ⟶ o'.A) (ψ₁ : o₁.A ⟶ o₁'.A)
    (hsq : m.φ ≫ ψ.left = ψ₁.left ≫ m'.φ) (T : Over S') (g : T ⟶ o₁.A) :
    (g ≫ ψ₁ = 1 ↔ m.ptEquiv T g ≫ ψ = 1) ∧ (g = 1 ↔ m.ptEquiv T g = 1) ∧
      ∀ I : Ideal (𝓞 D.F), KilledBy o₁ I g ↔ KilledBy o I (m.ptEquiv T g) := by
  have key : m'.ptEquiv T (g ≫ ψ₁) = m.ptEquiv T g ≫ ψ := by
    apply Over.OverMorphism.ext
    rw [ObjMap.ptEquiv_left, Over.comp_left, Over.comp_left, ObjMap.ptEquiv_left, Category.assoc, ← hsq,
      Category.assoc]
  refine ⟨?_, ?_, ?_⟩
  · rw [← key, MulEquiv.map_eq_one_iff]
  · rw [MulEquiv.map_eq_one_iff]
  · intro I
    unfold KilledBy
    refine forall_congr' fun a => imp_congr_right fun _ => ?_
    rw [← ObjMap.ptEquiv_act, MulEquiv.map_eq_one_iff]

/- English proof (translation)
Introduce `p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `T T₀ h g g₀ hg₀`. Establish `hw : T₀.hom = eqToHom h ≫ T.hom ≫ f`. Establish `e1` using `Over.w g₀`.

Establish `e2` using `Over.w (m.ptEquiv T g)`. Rewrite `e2` using `[ObjMap.ptEquiv_left]`. Simplify using `only [Category.assoc] at e2`. Rewrite using `[← e1, hg₀]`. Simplify using `only [Category.assoc]`.

Rewrite using `[e2]`. Both sides reduce to the same expression. Take `⟨L, ⟨⟨⟩⟩, hom⟩` from `T₀`. Express the relevant statement in the definitionally equal form `L = T.left at h`. Substitute `h` using the available equality.

Simplify using `only [eqToHom_refl, Category.id_comp] at hw hg₀`. Substitute `hw` using the available equality. Establish `hg : g₀ = m.ptEquiv T g`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[ObjMap.ptEquiv_left, hg₀]`.

Substitute `hg` using the available equality. Conclude with `pt_core m m' ψ ψ₁ hsq T g`. Introduce `r w j htj k _ _ _ x`. Take `⟨h1, h2⟩` from `htj k (x ≫ f)`. Establish `c` using `fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g`.

Use `⟨fun g hg he => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[(c g).2.2 w]`. Take `⟨n, hn⟩` from `he`. Conclude with `h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩`. Rewrite using `[← h2]`.

Conclude with `Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by`. Rewrite using `[(c g).1, (c g).2.2 w]`. Use the proof step `rfl)`.
-/
theorem UpperTheory.Gal.crystallineComparison.Mod.pullKer_of :
    PullKer := by
  intro p _ D R _ b N S S' s s' f o o' o₁ o₁' m m' ψ ψ₁ hsq
  refine ⟨?_, ?_⟩
  · intro T T₀ h g g₀ hg₀
    have hw : T₀.hom = eqToHom h ≫ T.hom ≫ f := by
      have e1 := Over.w g₀
      have e2 := Over.w (m.ptEquiv T g)
      rw [ObjMap.ptEquiv_left] at e2
      simp only [Category.assoc] at e2
      rw [← e1, hg₀]
      simp only [Category.assoc]
      rw [e2]
      rfl
    obtain ⟨L, ⟨⟨⟩⟩, hom⟩ := T₀
    change L = T.left at h
    subst h
    simp only [eqToHom_refl, Category.id_comp] at hw hg₀
    subst hw
    have hg : g₀ = m.ptEquiv T g := by
      apply Over.OverMorphism.ext
      rw [ObjMap.ptEquiv_left, hg₀]
    subst hg
    exact pt_core m m' ψ ψ₁ hsq T g
  · intro r w j htj k _ _ _ x
    obtain ⟨h1, h2⟩ := htj k (x ≫ f)
    have c := fun g => pt_core m m' ψ ψ₁ hsq (Over.mk x) g
    refine ⟨fun g hg he => ?_, ?_⟩
    · rw [(c g).2.2 w]
      obtain ⟨n, hn⟩ := he
      exact h1 _ ((c g).1.mp hg) ⟨n, ((c g).2.2 _).mp hn⟩
    · rw [← h2]
      exact Nat.card_congr ((m.ptEquiv (Over.mk x)).toEquiv.subtypeEquiv fun g => by
        rw [(c g).1, (c g).2.2 w]
        rfl)
