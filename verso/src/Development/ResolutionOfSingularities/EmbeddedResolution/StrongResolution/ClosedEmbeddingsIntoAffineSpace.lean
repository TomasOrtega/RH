import Mathlib
import Development.ResolutionOfSingularities.Foundations.Blowup.BlowupBasic
import Development.ResolutionOfSingularities.EmbeddedResolution.EtaleCoordinates.AffineSpaceCoordinates
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionDescent.AffineResolutionRule
import Development.ResolutionOfSingularities.Foundations.BlowupUniversalProperty
import Development.ResolutionOfSingularities.EmbeddedResolution.ResolutionOfSingularities
universe u

open CategoryTheory AlgebraicGeometry

namespace FunctorialResolution.EmbeddedResolution

/- English proof (translation)
Simplify using the standard rewrite rules. Both sides reduce to the same expression.
-/
private theorem comp_appTop_apply {X Y Z : Scheme.{u}} (f : X ⟶ Y) (g : Y ⟶ Z) (x : Γ(Z, ⊤)) :
    (f ≫ g).appTop x = f.appTop (g.appTop x) := by
  simp
  rfl

/- English proof (translation)
The claim follows from `map_add (CommRingCat.Hom.hom f.appTop) a b`.
-/
private theorem appTop_add {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a + b) = f.appTop a + f.appTop b :=
  map_add (CommRingCat.Hom.hom f.appTop) a b

/- English proof (translation)
The claim follows from `map_sub (CommRingCat.Hom.hom f.appTop) a b`.
-/
private theorem appTop_sub {X Y : Scheme.{u}} (f : X ⟶ Y) (a b : Γ(Y, ⊤)) :
    f.appTop (a - b) = f.appTop a - f.appTop b :=
  map_sub (CommRingCat.Hom.hom f.appTop) a b

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
private theorem appTop_id_apply {X : Scheme.{u}} (x : Γ(X, ⊤)) :
    (𝟙 X : X ⟶ X).appTop x = x := by
  simp

/- English proof (translation)
Take `⟨pr₁, hpr₁, hpr₁c⟩ : ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n)) S, q ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ ∀ a : Fin n, q.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) = …` from `⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) (fun a : ULift.{u} (Fin n) => AffineSpace.coord S (ULift.up (Sum.inl a.down) : ULift.{u} (Fin n ⊕ Fin m))), AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩`. Take `⟨pr₂, hpr₂, hpr₂c⟩ : ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin m)) S, q ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S) = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ ∀ b : Fin m, q.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) = …` from `⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) (fun b : ULift.{u} (Fin m) => AffineSpace.coord S (ULift.up (Sum.inr b.down) : ULift.{u} (Fin n ⊕ Fin m))), AffineSpace.homOfVector_over _ _, fun b => AffineSpace.homOfVector_appTop_coord _ _ _⟩`. Establish `mkHom : ∀ v : ULift.{u} (Fin n ⊕ Fin m) → Γ(AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, ⊤), ∃ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S …` using `fun v => ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) v, AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩`. Take `⟨σ, hσ, hσc⟩` from `mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) (fun b : Fin m => AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) + pr₁.appTop (F b)) i.down)`. Take `⟨σ', hσ', hσ'c⟩` from `mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) (fun b : Fin m => AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) - pr₁.appTop (F b)) i.down)`.

Take `⟨τ, hτ, hτc⟩` from `mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) - pr₂.appTop (G a)) (fun b : Fin m => AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)`. Take `⟨τ', hτ', hτ'c⟩` from `mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) + pr₂.appTop (G a)) (fun b : Fin m => AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)`. Establish `hσinl : ∀ a : Fin n, σ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))` using `fun a => hσc _`. Establish `hσinr : ∀ b : Fin m, σ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) + pr₁.appTop (F b)` using `fun b => hσc _`. Establish `hσ'inl : ∀ a : Fin n, σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))` using `fun a => hσ'c _`.

Establish `hσ'inr : ∀ b : Fin m, σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) - pr₁.appTop (F b)` using `fun b => hσ'c _`. Establish `hτinl : ∀ a : Fin n, τ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) - pr₂.appTop (G a)` using `fun a => hτc _`. Establish `hτinr : ∀ b : Fin m, τ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))` using `fun b => hτc _`. Establish `hτ'inl : ∀ a : Fin n, τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) + pr₂.appTop (G a)` using `fun a => hτ'c _`. Establish `hτ'inr : ∀ b : Fin m, τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))` using `fun b => hτ'c _`.

Establish `hfix₁ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) → (∀ a : Fin n, w.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{ …`. Introduce `w hw hwc x`. Establish `hcomp : w ≫ pr₁ = pr₁`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hpr₁, hw]`.

Introduce and unpack `⟨a⟩`. Rewrite using `[comp_appTop_apply, hpr₁c a, hwc a]`. Rewrite using `[← comp_appTop_apply, hcomp]`. Establish `hfix₂ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) → (∀ b : Fin m, w.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{ …`. Introduce `w hw hwc x`.

Establish `hcomp : w ≫ pr₂ = pr₂`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hpr₂, hw]`. Introduce and unpack `⟨b⟩`. Rewrite using `[comp_appTop_apply, hpr₂c b, hwc b]`.

Rewrite using `[← comp_appTop_apply, hcomp]`. Establish `hσσ' : σ ≫ σ' = 𝟙 _`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hσ', hσ, Category.id_comp]`. Introduce and unpack `⟨a | b⟩`.

Rewrite using `[comp_appTop_apply, hσ'inl a, hσinl a, appTop_id_apply]`. Rewrite using `[comp_appTop_apply, hσ'inr b, appTop_sub, hσinr b, hfix₁ σ hσ hσinl (F b), appTop_id_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `hσ'σ : σ' ≫ σ = 𝟙 _`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, hσ, hσ', Category.id_comp]`. Introduce and unpack `⟨a | b⟩`. Rewrite using `[comp_appTop_apply, hσinl a, hσ'inl a, appTop_id_apply]`. Rewrite using `[comp_appTop_apply, hσinr b, appTop_add, hσ'inr b, hfix₁ σ' hσ' hσ'inl (F b), appTop_id_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hττ' : τ ≫ τ' = 𝟙 _`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hτ', hτ, Category.id_comp]`. Introduce and unpack `⟨a | b⟩`. Rewrite using `[comp_appTop_apply, hτ'inl a, appTop_add, hτinl a, hfix₂ τ hτ hτinr (G a), appTop_id_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[comp_appTop_apply, hτ'inr b, hτinr b, appTop_id_apply]`. Establish `hτ'τ : τ' ≫ τ = 𝟙 _`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hτ, hτ', Category.id_comp]`.

Introduce and unpack `⟨a | b⟩`. Rewrite using `[comp_appTop_apply, hτinl a, appTop_sub, hτ'inl a, hfix₂ τ' hτ' hτ'inr (G a), appTop_id_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[comp_appTop_apply, hτinr b, hτ'inr b, appTop_id_apply]`. Take `⟨D, hDover, hcoordEq⟩ : ∃ d : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, d ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p ∧ ∀ i : ULift.{u} (Fin n ⊕ Fin m), d.appTop (AffineSpace.coord S i) = Sum.elim (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift …` from `⟨AffineSpace.homOfVector p (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))) (fun b : Fin m => e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) i.down), AffineSpace.homOfVector_over …`.

Establish `hDinl : ∀ a : Fin n, D.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))` using `fun a => hcoordEq _`. Establish `hDinr : ∀ b : Fin m, D.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))` using `fun b => hcoordEq _`. Establish `hLpr₁ : L ≫ pr₁ = e₁`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hpr₁, hLover, h₁]`.

Introduce and unpack `⟨a⟩`. Rewrite using `[comp_appTop_apply, hpr₁c a, hLinl a]`. Establish `hLF : ∀ b : Fin m, L.appTop (pr₁.appTop (F b)) = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))`. Introduce `b`. Rewrite using `[← comp_appTop_apply, hLpr₁, hF b]`.

Establish `hDpr₂ : D ≫ pr₂ = e₂`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hpr₂, hDover, h₂]`. Introduce and unpack `⟨b⟩`. Rewrite using `[comp_appTop_apply, hpr₂c b, hDinr b]`.

Establish `hcompG : ∀ a : Fin n, D.appTop (pr₂.appTop (G a)) = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))`. Introduce `a`. Rewrite using `[← comp_appTop_apply, hDpr₂, hG a]`. Establish `hA : L ≫ σ = D`. Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[Category.assoc, hσ, hLover, hDover]`. Introduce and unpack `⟨a | b⟩`. Rewrite using `[comp_appTop_apply, hσinl a, hLinl a, hDinl a]`. Rewrite using `[comp_appTop_apply, hσinr b, appTop_add, hLinr b, hLF b, hDinr b, zero_add]`. Establish `hB : D ≫ τ = R`.

Use `AffineSpace.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, hτ, hDover, hRover]`. Introduce and unpack `⟨a | b⟩`. Rewrite using `[comp_appTop_apply, hτinl a, appTop_sub, hDinl a, hcompG a, hRinl a, sub_self]`. Rewrite using `[comp_appTop_apply, hτinr b, hDinr b, hRinr b]`.

Use `⟨⟨σ ≫ τ, τ' ≫ σ', ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, ← Category.assoc τ τ' σ', hττ', Category.id_comp, hσσ']`. Rewrite using `[Category.assoc, ← Category.assoc σ' σ τ, hσ'σ, Category.id_comp, hτ'τ]`. Use `show (σ ≫ τ) ≫ _ = _`. Rewrite using `[Category.assoc, hτ, hσ]`.

Use `show L ≫ (σ ≫ τ) = R`. Rewrite using `[← Category.assoc, hA, hB]`.
-/
private theorem exists_iso_affineSpace_sum_comp_eq_of_coord {S : Scheme.{u}} (n m : ℕ)
    {Y : Scheme.{u}}
    (p : Y ⟶ S)
    (e₁ : Y ⟶ AffineSpace (ULift.{u} (Fin n)) S)
    (e₂ : Y ⟶ AffineSpace (ULift.{u} (Fin m)) S)
    (h₁ : e₁ ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S) = p)
    (h₂ : e₂ ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S) = p)
    (F : Fin m → Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤))
    (hF : ∀ b : Fin m, e₁.appTop (F b)
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
    (G : Fin n → Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤))
    (hG : ∀ a : Fin n, e₂.appTop (G a)
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (L R : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S)
    (hLover : L ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hRover : R ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p)
    (hLinl : ∀ a : Fin n, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
    (hLinr : ∀ b : Fin m, L.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinl : ∀ a : Fin n, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) = 0)
    (hRinr : ∀ b : Fin m, R.appTop (AffineSpace.coord S
        (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) :
    ∃ Φ : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ≅ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      Φ.hom ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧ L ≫ Φ.hom = R := by
  obtain ⟨pr₁, hpr₁, hpr₁c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin n)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin n)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ a : Fin n, q.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n)))
            = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun a : ULift.{u} (Fin n) =>
          AffineSpace.coord S (ULift.up (Sum.inl a.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun a => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨pr₂, hpr₂, hpr₂c⟩ :
      ∃ q : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ⟶ AffineSpace (ULift.{u} (Fin m)) S,
        q ≫ (AffineSpace (ULift.{u} (Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ b : Fin m, q.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))
            = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
        (fun b : ULift.{u} (Fin m) =>
          AffineSpace.coord S (ULift.up (Sum.inr b.down) : ULift.{u} (Fin n ⊕ Fin m))),
      AffineSpace.homOfVector_over _ _, fun b => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have mkHom : ∀ v : ULift.{u} (Fin n ⊕ Fin m) → Γ(AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S, ⊤),
      ∃ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
            ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
            = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), w.appTop (AffineSpace.coord S i) = v i :=
    fun v => ⟨AffineSpace.homOfVector (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) v,
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  obtain ⟨σ, hσ, hσc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₁.appTop (F b)) i.down)
  obtain ⟨σ', hσ', hσ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n => AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₁.appTop (F b)) i.down)
  obtain ⟨τ, hτ, hτc⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        - pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  obtain ⟨τ', hτ', hτ'c⟩ := mkHom (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
    (fun a : Fin n =>
      AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
        + pr₂.appTop (G a))
    (fun b : Fin m =>
      AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) i.down)
  have hσinl : ∀ a : Fin n,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσc _
  have hσinr : ∀ b : Fin m,
      σ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₁.appTop (F b) := fun b => hσc _
  have hσ'inl : ∀ a : Fin n,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun a => hσ'c _
  have hσ'inr : ∀ b : Fin m,
      σ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₁.appTop (F b) := fun b => hσ'c _
  have hτinl : ∀ a : Fin n,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            - pr₂.appTop (G a) := fun a => hτc _
  have hτinr : ∀ b : Fin m,
      τ.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτc _
  have hτ'inl : ∀ a : Fin n,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))
            + pr₂.appTop (G a) := fun a => hτ'c _
  have hτ'inr : ∀ b : Fin m,
      τ'.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)) :=
    fun b => hτ'c _
  have hfix₁ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ a : Fin n,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin n)) S, ⊤),
        w.appTop (pr₁.appTop x) = pr₁.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₁ = pr₁ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₁, hw]
      · rintro ⟨a⟩
        rw [comp_appTop_apply, hpr₁c a, hwc a]
    rw [← comp_appTop_apply, hcomp]
  have hfix₂ : ∀ w : AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S
        ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
      w ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S)
          = (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) →
      (∀ b : Fin m,
        w.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
          = AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m))) →
      ∀ x : Γ(AffineSpace (ULift.{u} (Fin m)) S, ⊤),
        w.appTop (pr₂.appTop x) = pr₂.appTop x := by
    intro w hw hwc x
    have hcomp : w ≫ pr₂ = pr₂ := by
      refine AffineSpace.hom_ext ?_ ?_
      · rw [Category.assoc, hpr₂, hw]
      · rintro ⟨b⟩
        rw [comp_appTop_apply, hpr₂c b, hwc b]
    rw [← comp_appTop_apply, hcomp]
  have hσσ' : σ ≫ σ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ', hσ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσ'inl a, hσinl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσ'inr b, appTop_sub, hσinr b,
          hfix₁ σ hσ hσinl (F b), appTop_id_apply]
        ring
  have hσ'σ : σ' ≫ σ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hσ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hσ'inl a, appTop_id_apply]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hσ'inr b,
          hfix₁ σ' hσ' hσ'inl (F b), appTop_id_apply]
        ring
  have hττ' : τ ≫ τ' = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ', hτ, Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτ'inl a, appTop_add, hτinl a,
          hfix₂ τ hτ hτinr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτ'inr b, hτinr b, appTop_id_apply]
  have hτ'τ : τ' ≫ τ = 𝟙 _ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hτ', Category.id_comp]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hτ'inl a,
          hfix₂ τ' hτ' hτ'inr (G a), appTop_id_apply]
        ring
      · rw [comp_appTop_apply, hτinr b, hτ'inr b, appTop_id_apply]
  obtain ⟨D, hDover, hcoordEq⟩ :
      ∃ d : Y ⟶ AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S,
        d ≫ (AffineSpace (ULift.{u} (Fin n ⊕ Fin m)) S ↘ S) = p ∧
          ∀ i : ULift.{u} (Fin n ⊕ Fin m), d.appTop (AffineSpace.coord S i)
            = Sum.elim
                (fun a : Fin n =>
                  e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
                (fun b : Fin m =>
                  e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m)))) i.down :=
    ⟨AffineSpace.homOfVector p (fun i : ULift.{u} (Fin n ⊕ Fin m) => Sum.elim
        (fun a : Fin n => e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))))
        (fun b : Fin m => e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))))
        i.down),
      AffineSpace.homOfVector_over _ _, fun i => AffineSpace.homOfVector_appTop_coord _ _ _⟩
  have hDinl : ∀ a : Fin n,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inl a) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := fun a => hcoordEq _
  have hDinr : ∀ b : Fin m,
      D.appTop (AffineSpace.coord S (ULift.up (Sum.inr b) : ULift.{u} (Fin n ⊕ Fin m)))
        = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := fun b => hcoordEq _
  have hLpr₁ : L ≫ pr₁ = e₁ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₁, hLover, h₁]
    · rintro ⟨a⟩
      rw [comp_appTop_apply, hpr₁c a, hLinl a]
  have hLF : ∀ b : Fin m, L.appTop (pr₁.appTop (F b))
      = e₂.appTop (AffineSpace.coord S (ULift.up b : ULift.{u} (Fin m))) := by
    intro b
    rw [← comp_appTop_apply, hLpr₁, hF b]
  have hDpr₂ : D ≫ pr₂ = e₂ := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hpr₂, hDover, h₂]
    · rintro ⟨b⟩
      rw [comp_appTop_apply, hpr₂c b, hDinr b]
  have hcompG : ∀ a : Fin n, D.appTop (pr₂.appTop (G a))
      = e₁.appTop (AffineSpace.coord S (ULift.up a : ULift.{u} (Fin n))) := by
    intro a
    rw [← comp_appTop_apply, hDpr₂, hG a]
  have hA : L ≫ σ = D := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hσ, hLover, hDover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hσinl a, hLinl a, hDinl a]
      · rw [comp_appTop_apply, hσinr b, appTop_add, hLinr b, hLF b, hDinr b, zero_add]
  have hB : D ≫ τ = R := by
    refine AffineSpace.hom_ext ?_ ?_
    · rw [Category.assoc, hτ, hDover, hRover]
    · rintro ⟨a | b⟩
      · rw [comp_appTop_apply, hτinl a, appTop_sub, hDinl a, hcompG a, hRinl a, sub_self]
      · rw [comp_appTop_apply, hτinr b, hDinr b, hRinr b]
  refine ⟨⟨σ ≫ τ, τ' ≫ σ', ?_, ?_⟩, ?_, ?_⟩
  · rw [Category.assoc, ← Category.assoc τ τ' σ', hττ', Category.id_comp, hσσ']
  · rw [Category.assoc, ← Category.assoc σ' σ τ, hσ'σ, Category.id_comp, hτ'τ]
  · show (σ ≫ τ) ≫ _ = _
    rw [Category.assoc, hτ, hσ]
  · show L ≫ (σ ≫ τ) = R
    rw [← Category.assoc, hA, hB]

/- English proof (translation)
Introduce `k hk Y hY p hp n m e₁ he₁ e₂ he₂ h₁ h₂`. Establish `: IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin n)))`. Unfold `affineSpaceIndexedBy`. Use `infer_instance`. Establish `: IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin m)))`.

Unfold `affineSpaceIndexedBy`. Use `infer_instance`. Use `choose F hF using fun b : Fin m => (IsClosedImmersion.isAffine_surjective_of_isAffine e₁).2 (e₂.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up b : ULift.{u} (Fin m))))`. Use `choose G hG using fun a : Fin n => (IsClosedImmersion.isAffine_surjective_of_isAffine e₂).2 (e₁.appTop (AffineSpace.coord (Spec (CommRingCat.of k)) (ULift.up a : ULift.{u} (Fin n))))`. Conclude with `exists_iso_affineSpace_sum_comp_eq_of_coord n m p e₁ e₂ h₁ h₂ F hF G hG (AffineSpace.homOfVector p (coordVectorInl n m e₁)) (AffineSpace.homOfVector p (coordVectorInr n m e₂)) (AffineSpace.homOfVector_over _ _) (AffineSpace.homOfVector_over _ _) (fun a => AffineSpace.homOfVector_ …`.
-/
theorem closedEmbeddingsRelatedByAutomorphism : ClosedEmbeddingsRelatedByAutomorphism.{u} := by
  intro k hk Y hY p hp n m e₁ he₁ e₂ he₂ h₁ h₂
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin n))) := by
    unfold affineSpaceIndexedBy; infer_instance
  have : IsAffine (affineSpaceIndexedBy k (ULift.{u} (Fin m))) := by
    unfold affineSpaceIndexedBy; infer_instance
  choose F hF using fun b : Fin m =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₁).2
      (e₂.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up b : ULift.{u} (Fin m))))
  choose G hG using fun a : Fin n =>
    (IsClosedImmersion.isAffine_surjective_of_isAffine e₂).2
      (e₁.appTop (AffineSpace.coord (Spec (CommRingCat.of k))
        (ULift.up a : ULift.{u} (Fin n))))
  exact exists_iso_affineSpace_sum_comp_eq_of_coord n m p e₁ e₂ h₁ h₂ F hF G hG
    (AffineSpace.homOfVector p (coordVectorInl n m e₁))
    (AffineSpace.homOfVector p (coordVectorInr n m e₂))
    (AffineSpace.homOfVector_over _ _) (AffineSpace.homOfVector_over _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun a => AffineSpace.homOfVector_appTop_coord _ _ _)
    (fun b => AffineSpace.homOfVector_appTop_coord _ _ _)

end FunctorialResolution.EmbeddedResolution
