import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HxiTZeroComb
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT GlobalTheory.KS

namespace GlobalTheory.KS.PowPB

/- English proof (translation)
Unfold `powMap`. Rewrite using `[← Over.comp_left, Pi.lift_π]`. Both sides reduce to the same expression.
-/
theorem powMap_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) (i : Fin m) :
    powMap f φ hφ m ≫ (pr A i).left = (pr A' i).left ≫ φ := by
  unfold powMap
  rw [← Over.comp_left, Pi.lift_π]
  rfl

/- English proof (translation)
Unfold `powMap`. Conclude with `Over.w _`.
-/
theorem powMap_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f) (m : ℕ) :
    powMap f φ hφ m ≫ (pow A m).hom = (pow A' m).hom ≫ f := by
  unfold powMap
  exact Over.w _

/- English proof (translation)
Set `u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m` to `Over.homMk g₁ rfl`. Set `u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m` to `Over.homMk g₂ (by simpa using hh.symm)`. Establish `: u₁ = u₂` using `Pi.hom_ext _ _ (fun i => by`. Use `ext`. Simplify `hi i)` using `[u₁, u₂]`.

Conclude with `congrArg CommaMorphism.left this`.
-/
theorem pow_left_hom_ext {S : Scheme.{0}} {A : Over S} {m : ℕ} {T : Scheme.{0}} (g₁ g₂ : T ⟶ (pow A m).left)
    (hh : g₁ ≫ (pow A m).hom = g₂ ≫ (pow A m).hom) (hi : ∀ i, g₁ ≫ (pr A i).left = g₂ ≫ (pr A i).left) :
    g₁ = g₂ := by
  let u₁ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₁ rfl
  let u₂ : Over.mk (g₁ ≫ (pow A m).hom) ⟶ pow A m := Over.homMk g₂ (by simpa using hh.symm)
  have : u₁ = u₂ := Pi.hom_ext _ _ (fun i => by
    ext
    simpa [u₁, u₂] using hi i)
  exact congrArg CommaMorphism.left this

noncomputable def liftPow {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : T ⟶ (pow A' m).left :=
  (Pi.lift (fun i : Fin m => (Over.homMk (H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w))
    (H.lift_snd _ _ _) : Over.mk b ⟶ A')) : Over.mk b ⟶ pow A' m).left

/- English proof (translation)
Unfold `liftPow`. Conclude with `Over.w _`.
-/
theorem liftPow_w {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) : liftPow H m a b w ≫ (pow A' m).hom = b := by
  unfold liftPow
  exact Over.w _

/- English proof (translation)
Unfold `liftPow`. Rewrite using `[← Over.comp_left, Pi.lift_π]`. Both sides reduce to the same expression.
-/
theorem liftPow_pr {S S' : Scheme.{0}} {A : Over S} {A' : Over S'} {f : S' ⟶ S} {φ : A'.left ⟶ A.left}
    (H : IsPullback φ A'.hom A.hom f) (m : ℕ) {T : Scheme.{0}} (a : T ⟶ (pow A m).left) (b : T ⟶ S')
    (w : a ≫ (pow A m).hom = b ≫ f) (i : Fin m) :
    liftPow H m a b w ≫ (pr A' i).left = H.lift (a ≫ (pr A i).left) b (by rw [Category.assoc, Over.w]; exact w) := by
  unfold liftPow
  rw [← Over.comp_left, Pi.lift_π]
  rfl

/- English proof (translation)
Introduce `S S' A A' f φ hφ H m`. Use `⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩` and prove the remaining obligations. Introduce `s`. Apply `pow_left_hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]`.

Introduce `i`. Rewrite using `[Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]`. Introduce `s`. Conclude with `liftPow_w H m _ _ _`. Introduce `s u h₁ h₂`.

Apply `pow_left_hom_ext` to reduce the goal to its premises. Rewrite using `[h₂, liftPow_w]`. Introduce `i`. Rewrite using `[liftPow_pr]`. Apply `H.hom_ext` to reduce the goal to its premises.

Rewrite using `[H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]`. Rewrite using `[H.lift_snd, Category.assoc, Over.w, h₂]`.
-/
theorem powMap_isPullback : ∀ (S S' : Scheme.{0}) (A : Over S) (A' : Over S') (f : S' ⟶ S) (φ : A'.left ⟶ A.left)
    (hφ : φ ≫ A.hom = A'.hom ≫ f), IsPullback φ A'.hom A.hom f →
    ∀ m : ℕ, IsPullback (powMap f φ hφ m) (pow A' m).hom (pow A m).hom f := by
  intro S S' A A' f φ hφ H m
  refine ⟨⟨powMap_w f φ hφ m⟩, ⟨PullbackCone.IsLimit.mk _ (fun s => liftPow H m s.fst s.snd s.condition) ?_ ?_ ?_⟩⟩
  · intro s
    apply pow_left_hom_ext
    · rw [Category.assoc, powMap_w, ← Category.assoc, liftPow_w, s.condition]
    · intro i
      rw [Category.assoc, powMap_pr, ← Category.assoc, liftPow_pr, H.lift_fst]
  · intro s
    exact liftPow_w H m _ _ _
  · intro s u h₁ h₂
    apply pow_left_hom_ext
    · rw [h₂, liftPow_w]
    · intro i
      rw [liftPow_pr]
      apply H.hom_ext
      · rw [H.lift_fst, Category.assoc, ← powMap_pr f φ hφ, ← Category.assoc, h₁]
      · rw [H.lift_snd, Category.assoc, Over.w, h₂]

end GlobalTheory.KS.PowPB
