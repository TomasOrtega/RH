import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.IsSelfOf
import Development.AbelianVarietyTheory.Definitions.Jets.TwoPlaces

set_option autoImplicit false

open scoped BigOperators TensorProduct
open Classical NumberField IsDedekindDomain Formalism.L2.FormalSeriesBounds Formalism.IncomingBounds Formalism.L2.Pj Formalism.L2.DIV Formalism.BasicNotions GlobalTheory.RowLaw GlobalTheory.RowAt GlobalTheory.GoodDepth
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ

namespace GlobalTheory.RowAt

/- English proof (translation)
Introduce `C _ V d _ Pl _ Z n m big rk ga nW ν hZ h`. Take `⟨I, J, fI, fJ, X, F, h1, h2, h3⟩` from `h`. Take `⟨z0, hz0⟩` from `hZ`. Take `⟨q, hq⟩ : ∃ q : Pl → Z, ∀ o : Z, q o.1 = o` from `⟨fun o => if h : o ∈ Z then ⟨o, h⟩ else ⟨z0, hz0⟩, fun o => by simp [o.2]⟩`. Use `⟨fun o => I (q o), fun o => J (q o), fun o => fI (q o), fun o => fJ (q o), fun o => X (q o), fun o => F (q o), fun o => h1 (q o), ?_, ?_⟩` and prove the remaining obligations.

Introduce `o ho g s`. Establish `e` using `h2 (q o) (Finset.mem_univ _) g s`. Establish `e' : (q o).1 = o` using `congrArg Subtype.val (hq ⟨o, ho⟩)`. Simplify using `only [e'] at e`. Conclude with `e`.

Introduce `L hA hR hW`. Establish `key` using `h3 (fun o => L o.1) ?_ ?_ ?_`. Rewrite using `[← Finset.sum_coe_sort Z]`. Conclude with `key`. Introduce `o _ p hp`.

Establish `e` using `hA o.1 o.2 p hp`. Establish `gen : ∀ o' : Z, o' = o → p.1.Attains (X o') (F o') p.2 → p.1.Attains (X o) (F o) p.2`. Introduce `o' ho' h'`. Substitute `ho'` using the available equality. Conclude with `h'`.

Conclude with `gen _ (hq o) e`. Rewrite `hR` using `[← Finset.sum_coe_sort Z]`. Use `le_trans (le_of_eq ?_) hR` and prove the remaining obligations. Use `Finset.sum_congr rfl fun o _ => ?_` and prove the remaining obligations. Simplify using `only [(h1 _).1]`.

Introduce `o _ g a k`. Establish `e` using `hW o.1 o.2 g a k`. Establish `gen : ∀ o' : Z, o' = o → ((L o.1).map fun p => p.1.wt (X o') g a k).sum = ga o.1 g a k → ((L o.1).map fun p => p.1.wt (X o) g a k).sum = ga o.1 g a k`. Introduce `o' ho' h'`. Substitute `ho'` using the available equality.

Conclude with `h'`. Conclude with `gen _ (hq o) e`.
-/
theorem supply_extend :
    ∀ (C : Type) [Field C] (V : VF C) (d : ℕ) [NeZero d] (Pl : Type) [Fintype Pl] (Z : Finset Pl) (n m : ℕ) (big : Pl → Fin 2 → ZMod d → Prop) (rk : Pl → Fin 2 → ZMod d → ℕ) (ga : Pl → Fin 2 → ZMod d → ℕ → ℕ) (nW : ℕ) (ν : ℝ), Z.Nonempty → Supply V d Z Finset.univ n m (fun o => big o.1) (fun o => rk o.1) (fun o => ga o.1) nW ν → Supply V d Pl Z n m big rk ga nW ν := by
  intro C _ V d _ Pl _ Z n m big rk ga nW ν hZ h
  obtain ⟨I, J, fI, fJ, X, F, h1, h2, h3⟩ := h
  obtain ⟨z0, hz0⟩ := hZ
  obtain ⟨q, hq⟩ : ∃ q : Pl → Z, ∀ o : Z, q o.1 = o :=
    ⟨fun o => if h : o ∈ Z then ⟨o, h⟩ else ⟨z0, hz0⟩, fun o => by simp [o.2]⟩
  refine ⟨fun o => I (q o), fun o => J (q o), fun o => fI (q o), fun o => fJ (q o), fun o => X (q o),
    fun o => F (q o), fun o => h1 (q o), ?_, ?_⟩
  · intro o ho g s
    have e := h2 (q o) (Finset.mem_univ _) g s
    have e' : (q o).1 = o := congrArg Subtype.val (hq ⟨o, ho⟩)
    simp only [e'] at e
    exact e
  · intro L hA hR hW
    have key := h3 (fun o => L o.1) ?_ ?_ ?_
    · rw [← Finset.sum_coe_sort Z]
      exact key
    · intro o _ p hp
      have e := hA o.1 o.2 p hp
      have gen : ∀ o' : Z, o' = o → p.1.Attains (X o') (F o') p.2 → p.1.Attains (X o) (F o) p.2 := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e
    · rw [← Finset.sum_coe_sort Z] at hR
      refine le_trans (le_of_eq ?_) hR
      refine Finset.sum_congr rfl fun o _ => ?_
      simp only [(h1 _).1]
    · intro o _ g a k
      have e := hW o.1 o.2 g a k
      have gen : ∀ o' : Z, o' = o → ((L o.1).map fun p => p.1.wt (X o') g a k).sum = ga o.1 g a k →
          ((L o.1).map fun p => p.1.wt (X o) g a k).sum = ga o.1 g a k := by
        intro o' ho' h'
        subst ho'
        exact h'
      exact gen _ (hq o) e

end GlobalTheory.RowAt
