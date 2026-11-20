import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RosatiFor
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabComp
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull

set_option autoImplicit false

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.UPel.HT

namespace GlobalTheory.EqLocus

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `Z hZ a b`. Use `⟨Z, 𝟙 Z, hZ, fun k => k.elim0, fun T h _ => ⟨h, by simp, fun g hg => by simpa using hg⟩⟩` and prove the remaining obligations.

Consider the case `succ n ih`. Introduce `Z hZ a b`. Set `e` to `equalizer.ι (a 0) (b 0)`. Establish `hE : IsFinite (equalizer (a 0) (b 0)).hom`. Rewrite using `[← Over.w e]`.

Use `infer_instance`. Take `⟨Y, i', hY, hi', hu⟩` from `ih _ hE (fun k => e ≫ a k.succ) (fun k => e ≫ b k.succ)`. Use `⟨Y, i' ≫ e, hY, ?_, ?_⟩` and prove the remaining obligations. Introduce `k`. Use `Fin.cases ?_ (fun k => ?_) k` and prove the remaining obligations.

Simplify using `only [Category.assoc]`. Rewrite using `[equalizer.condition]`. Simplify `hi' k` using `only [Category.assoc]`. Introduce `T h hh`. Set `l : T ⟶ equalizer (a 0) (b 0)` to `equalizer.lift h (hh 0)`.

Establish `hl : l ≫ e = h` using `equalizer.lift_ι _ _`. Take `⟨h'', hh'', hu''⟩` from `hu T l (fun k => by`. Simplify using `only [← Category.assoc, hl]`. Conclude with `hh k.succ)`. Use `⟨h'', show h'' ≫ i' ≫ e = h by rw [← Category.assoc, hh'', hl], fun g hg => hu'' g ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `g ≫ i' ≫ e = h at hg`. Express the relevant statement in the definitionally equal form `g ≫ i' = l`. Apply `(cancel_mono e).1` to reduce the goal to its premises. Rewrite using `[Category.assoc, hg, hl]`.
-/
theorem exists_fin (H : Scheme.{0}) (G : Over H) [IsSeparated G.hom] :
    ∀ (n : ℕ) (Z : Over H), IsFinite Z.hom → ∀ (a b : Fin n → (Z ⟶ G)),
      ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧ (∀ k, i ≫ a k = i ≫ b k) ∧
        ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) → ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro n
  induction n with
  | zero =>
    intro Z hZ a b
    refine ⟨Z, 𝟙 Z, hZ, fun k => k.elim0, fun T h _ => ⟨h, by simp, fun g hg => by simpa using hg⟩⟩
  | succ n ih =>
    intro Z hZ a b
    let e := equalizer.ι (a 0) (b 0)
    have hE : IsFinite (equalizer (a 0) (b 0)).hom := by
      rw [← Over.w e]
      infer_instance
    obtain ⟨Y, i', hY, hi', hu⟩ := ih _ hE (fun k => e ≫ a k.succ) (fun k => e ≫ b k.succ)
    refine ⟨Y, i' ≫ e, hY, ?_, ?_⟩
    · intro k
      refine Fin.cases ?_ (fun k => ?_) k
      · simp only [Category.assoc]
        rw [equalizer.condition]
      · simpa only [Category.assoc] using hi' k
    · intro T h hh
      let l : T ⟶ equalizer (a 0) (b 0) := equalizer.lift h (hh 0)
      have hl : l ≫ e = h := equalizer.lift_ι _ _
      obtain ⟨h'', hh'', hu''⟩ := hu T l (fun k => by
        simp only [← Category.assoc, hl]
        exact hh k.succ)
      refine ⟨h'', show h'' ≫ i' ≫ e = h by rw [← Category.assoc, hh'', hl], fun g hg => hu'' g ?_⟩
      change g ≫ i' ≫ e = h at hg
      change g ≫ i' = l
      apply (cancel_mono e).1
      rw [Category.assoc, hg, hl]

/- English proof (translation)
Introduce `H Z G hZ hG Ix _ a b`. Take `⟨n, ⟨σ⟩⟩` from `Finite.exists_equiv_fin Ix`. Take `⟨Y, i, hY, hi, hu⟩` from `exists_fin H G n Z hZ (fun k => a (σ.symm k)) (fun k => b (σ.symm k))`. Use `⟨Y, i, hY, fun k => by simpa using hi (σ k), fun T h hh => hu T h (fun k => hh _)⟩` and prove the remaining obligations.
-/
theorem exists_finite_eqLocus : ∀ (H : Scheme.{0}) (Z G : Over H), IsFinite Z.hom → IsSeparated G.hom →
    ∀ (Ix : Type) [Finite Ix] (a b : Ix → (Z ⟶ G)), ∃ (Y : Over H) (i : Y ⟶ Z), IsFinite Y.hom ∧
      (∀ k, i ≫ a k = i ≫ b k) ∧ ∀ (T : Over H) (h : T ⟶ Z), (∀ k, h ≫ a k = h ≫ b k) →
        ∃! h' : T ⟶ Y, h' ≫ i = h := by
  intro H Z G hZ hG Ix _ a b
  obtain ⟨n, ⟨σ⟩⟩ := Finite.exists_equiv_fin Ix
  obtain ⟨Y, i, hY, hi, hu⟩ := exists_fin H G n Z hZ (fun k => a (σ.symm k)) (fun k => b (σ.symm k))
  refine ⟨Y, i, hY, fun k => by simpa using hi (σ k), fun T h hh => hu T h (fun k => hh _)⟩

end GlobalTheory.EqLocus
