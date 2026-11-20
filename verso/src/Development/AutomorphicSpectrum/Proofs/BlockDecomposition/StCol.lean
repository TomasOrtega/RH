import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.KummerCupProducts.FirstChernCompatibleSystem

set_option backward.isDefEq.respectTransparency false

open CategoryTheory AlgebraicGeometry Opposite CrystallineSemistableComparison CrystallineSemistableComparison.CH CrystallineSemistableComparison.E GlobalTheory.EtC

namespace GlobalTheory.CompanionTheory.EdgeStair

/- English proof (translation)
Introduce `R _ C _ F T hG`. Use `⟨?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `k z`. Use function extensionality and compare the values at `s`. Express the relevant statement in the definitionally equal form `∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T.K 0).map (GlobalTheory.CatH.toLast i s)).hom (T.ι _ (z (GlobalTheory.CatH.face i s))) = T.ι _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)))`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, hG.ι_nat]`. Introduce `s k a`. Use function extensionality and compare the values at `t`.

Express the relevant statement in the definitionally equal form `∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T.K (s + 1)).map (GlobalTheory.CatH.toLast i t)).hom (T.dv s _ (a (GlobalTheory.CatH.face i t))) = T.dv s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) • ((T.K s).map (GlobalTheory.CatH.toLast i t)).hom (a (GlobalTheory.CatH.face i t)))`. Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_zsmul, hG.dv_nat]`. Introduce `k x y h`.

Use function extensionality and compare the values at `s`. Conclude with `hG.inj _ (congrFun h s)`. Introduce `k x`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Establish `hz : ∀ s, ∃ z, T.ι _ z = x s` using `fun s => (hG.ex0 _ (x s)).1 (congrFun h s)`. Use `choose z hz using hz`. Conclude with `⟨z, funext hz⟩`. Introduce and unpack `⟨z, rfl⟩`. Use function extensionality and compare the values at `s`.

Conclude with `(hG.ex0 _ _).2 ⟨_, rfl⟩`. Introduce `s k x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hz : ∀ t, ∃ a, T.dv s _ a = x t` using `fun t => (hG.ex s _ (x t)).1 (congrFun h t)`.

Use `choose a ha using hz`. Conclude with `⟨a, funext ha⟩`. Introduce and unpack `⟨a, rfl⟩`. Use function extensionality and compare the values at `t`. Conclude with `(hG.ex s _ _).2 ⟨_, rfl⟩`.
-/
theorem stCol : CrystallineSemistableComparison.E.StCol := by
  intro R _ C _ F T hG
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro k z
    funext s
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K 0).map (GlobalTheory.CatH.toLast i s)).hom (T.ι _ (z (GlobalTheory.CatH.face i s))) =
      T.ι _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        (F.map (GlobalTheory.CatH.toLast i s)).hom (z (GlobalTheory.CatH.face i s)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.ι_nat]
  · intro s k a
    funext t
    change ∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K (s + 1)).map (GlobalTheory.CatH.toLast i t)).hom (T.dv s _ (a (GlobalTheory.CatH.face i t))) =
      T.dv s _ (∑ i : Fin (k + 2), (-1 : ℤ) ^ (i : ℕ) •
        ((T.K s).map (GlobalTheory.CatH.toLast i t)).hom (a (GlobalTheory.CatH.face i t)))
    rw [map_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [map_zsmul, hG.dv_nat]
  · intro k x y h
    funext s
    exact hG.inj _ (congrFun h s)
  · intro k x
    constructor
    · intro h
      have hz : ∀ s, ∃ z, T.ι _ z = x s := fun s => (hG.ex0 _ (x s)).1 (congrFun h s)
      choose z hz using hz
      exact ⟨z, funext hz⟩
    · rintro ⟨z, rfl⟩
      funext s
      exact (hG.ex0 _ _).2 ⟨_, rfl⟩
  · intro s k x
    constructor
    · intro h
      have hz : ∀ t, ∃ a, T.dv s _ a = x t := fun t => (hG.ex s _ (x t)).1 (congrFun h t)
      choose a ha using hz
      exact ⟨a, funext ha⟩
    · rintro ⟨a, rfl⟩
      funext t
      exact (hG.ex s _ _).2 ⟨_, rfl⟩

end GlobalTheory.CompanionTheory.EdgeStair
