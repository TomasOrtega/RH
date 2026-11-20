import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.OrdReadOf

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.UPel.HT.Hecke GlobalTheory.UPel.HT.ES
open GlobalTheory.IwLevel (InSub IsIsogDeg)
open GlobalTheory.AbDual (evc IsAdditive swap)
attribute [local instance] Ideal.Quotient.field
open UpperTheory.Gal.crystallineComparison UpperTheory.Gal.crystallineComparison.Mod

/- English proof (translation)
Take `⟨φ, rfl⟩ : ∃ φ, u = Spec.map φ` from `⟨Spec.preimage u, (Spec.map_preimage u).symm⟩`. Establish `hφ : φ.hom.comp (algebraMap κ B) = algebraMap κ Λ`. Establish `h' : Spec.map (CommRingCat.ofHom (algebraMap κ B) ≫ φ) = Spec.map (CommRingCat.ofHom (algebraMap κ Λ))`. Rewrite using `[Spec.map_comp]`. Conclude with `h`.

Establish `h''` using `Spec.map_injective h'`. Conclude with `congrArg CommRingCat.Hom.hom h''`. Use `⟨{ toRingHom := φ.hom, commutes' := fun r => RingHom.congr_fun hφ r }, ?_⟩` and prove the remaining obligations. Both sides reduce to the same expression.
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
Introduce `hS κ _ A _ P d hRep hcard Λ _ _ _ ε g hP hInf`. Take `⟨B, _, _, hfin, hfree, hrank, i, hmono, hiff⟩` from `hRep`. Use `haveI : Mono i := hmono`. Establish `key : ∀ (Λ' : Type) [CommRing Λ'] [Algebra κ Λ'] (ν : B →ₐ[κ] Λ'), spMap ν.toRingHom ≫ spMap (algebraMap κ B) = spMap (algebraMap κ Λ')`. Introduce `Λ' _ _ ν`.

Simplify using `only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Use `congr 2`. Use extensionality with `r`. Simplify using the standard rewrite rules.

Establish `hid : spMap (algebraMap κ κ) = 𝟙 (Sp κ)` using `by simp [spMap]`. Set `F : (B →ₐ[κ] κ) → { g // P (𝟙_ (Over (Sp κ))) g }` to `fun ν => ⟨Over.homMk (U := 𝟙_ (Over (Sp κ))) (V := algPt κ B) (spMap ν.toRingHom) (by show spMap ν.toRingHom ≫ spMap (algebraMap κ B) = 𝟙 _`. Rewrite using `[key κ ν, hid]) ≫ i,`. Use the proof step `(hiff _ _).1 ⟨_, rfl⟩⟩`. Establish `hF : Function.Bijective F`.

Prove the components needed by the constructor for the conclusion. Introduce `ν₁ ν₂ h`. Establish `h1` using `congrArg Subtype.val h`. Establish `h2` using `(cancel_mono i).1 h1`. Establish `h3` using `congrArg CommaMorphism.left h2`.

Establish `h4 : CommRingCat.ofHom ν₁.toRingHom = CommRingCat.ofHom ν₂.toRingHom` using `Spec.map_injective h3`. Use extensionality with `x`. Conclude with `congrArg (fun φ => φ.hom x) h4`. Introduce and unpack `⟨g₀, hg₀⟩`. Take `⟨y, hy⟩` from `(hiff _ _).2 hg₀`.

Take `⟨ν, hν⟩` from `exists_alg (Λ := κ) y.left (by`. Rewrite using `[hid]`. Conclude with `Over.w y)`. Use `⟨ν, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show _ ≫ i = g₀`.

Rewrite using `[← hy]`. Use `congr 1`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `[hν]`. Establish `hpts : Nat.card (B →ₐ[κ] κ) = Module.finrank κ B`.

Rewrite using `[hrank, ← hcard]`. Conclude with `Nat.card_congr (Equiv.ofBijective F hF)`. Take `⟨y, hy⟩` from `(hiff _ _).2 hP`. Take `⟨ν, hν⟩` from `exists_alg y.left (Over.w y)`. Establish `hsplit` using `hS κ B Λ hpts ε ν`.

Establish `e1 : spMap ν.toRingHom = spMap (algebraMap κ Λ) ≫ spMap (ε.comp ν).toRingHom` using `by conv_lhs => rw [hsplit] dsimp only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`. Both sides reduce to the same expression. Establish `e2 : spMap ε.toRingHom ≫ spMap (algebraMap κ Λ) = 𝟙 (Sp κ)` using `by dsimp only [spMap]`. Rewrite using `[← Spec.map_comp, ← CommRingCat.ofHom_comp]`.

Rewrite using `[show ε.toRingHom.comp (algebraMap κ Λ) = RingHom.id κ from by ext r; simp]`. Simplify using the standard rewrite rules. Establish `gl : g.left = y.left ≫ i.left`. Rewrite using `[← hy]`. Both sides reduce to the same expression.

Establish `one_l : ∀ T : Over (Sp κ), (1 : T ⟶ A).left = T.hom ≫ η[A].left`. Introduce `T`. Use `show (toUnit T ≫ η[A]).left = _`. Rewrite using `[Over.comp_left]`. Use `congr 1`.

Establish `hI : spMap ε.toRingHom ≫ g.left = (1 : 𝟙_ (Over (Sp κ)) ⟶ A).left` using `hInf`. Rewrite `hI` using `[one_l, gl, hν, e1]`. Simplify using `only [← Category.assoc, e2, Category.id_comp] at hI`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Rewrite using `[one_l, gl, hν, e1, Category.assoc, hI]`.

Both sides reduce to the same expression.
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
