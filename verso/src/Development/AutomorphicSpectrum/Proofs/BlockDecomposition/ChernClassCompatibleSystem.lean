import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.ChernSys

/- English proof (translation)
Introduce and unpack `U ⟨z⟩`. Take `⟨x, y, h, -⟩` from `(hpt Y X f 0 U).1 z`. Establish `h1 : IsUnit (l : Γ(U, ⊤))`. Use `hl.map x.appTop.hom` as an intermediate fact. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis.

Rewrite using `[Nat.cast_pow]`. Conclude with `h1.pow n`.
-/
theorem inv_cech (hpt : CrystallineSemistableComparison.E.CechPt) (l : ℕ) {Y X : Scheme.{0}} (f : Y ⟶ X)
    (hl : IsUnit (l : Γ(X, ⊤))) (n : ℕ) : GlobalTheory.EtC.Inv (l ^ n) (cech f) := by
  rintro U ⟨z⟩
  obtain ⟨x, y, h, -⟩ := (hpt Y X f 0 U).1 z
  have h1 : IsUnit (l : Γ(U, ⊤)) := by
    have := hl.map x.appTop.hom
    rwa [map_natCast] at this
  rw [Nat.cast_pow]
  exact h1.pow n

/- English proof (translation)
Introduce `a2 a11 l _ Y X f _ _ hl L`. Establish `hinv` using `inv_cech hpt l f hl`. Establish `hne : ∀ n, NeZero (l ^ n)` using `fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩`. Use `⟨hinv, ?_⟩` and prove the remaining obligations. Establish `hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (cechAug f) (tw (l ^ n) 1) 2)` using `fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2`.

Use `choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)`. Use `⟨⟨x, fun k => ?_⟩, hx⟩` and prove the remaining obligations. Apply `(hb k).1` to reduce the goal to its premises. Establish `e` using `((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L`. Establish `e2` using `pull_red (l ^ (k + 1)) (l ^ k) (cechAug f) 2 1 (x (k + 1))`.

Conclude with `e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))`.
-/
theorem chern_class_compatible_system (hpt : CrystallineSemistableComparison.E.CechPt) : CrystallineSemistableComparison.E.FirstChernCompatibleSystem := by
  intro a2 a11 l _ Y X f _ _ hl L
  have hinv := inv_cech hpt l f hl
  have hne : ∀ n, NeZero (l ^ n) := fun n => ⟨pow_ne_zero _ (Fact.out : l.Prime).ne_zero⟩
  refine ⟨hinv, ?_⟩
  have hb : ∀ n, Function.Bijective (pull (ZMod (l ^ n)) (cechAug f) (tw (l ^ n) 1) 2) :=
    fun n => a2 (ZMod (l ^ n)) f (tw (l ^ n) 1) 2
  choose x hx using fun n => (hb n).2 (c1 (l ^ n) L)
  refine ⟨⟨x, fun k => ?_⟩, hx⟩
  apply (hb k).1
  have e := ((a11 (l ^ (k + 1)) (l ^ k) (pow_dvd_pow l (Nat.le_succ k)) (cech f)).2.1 (hinv (k + 1))).2 L
  have e2 := pull_red (l ^ (k + 1)) (l ^ k) (cechAug f) 2 1 (x (k + 1))
  exact e2.trans ((congrArg _ (hx (k + 1))).trans (e.trans (hx k).symm))

end GlobalTheory.CompanionTheory.ChernSys
