import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.CyclicStrongAtCusp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasSupportOfIsSubquotientProdIrr
open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.LocLanglands GlobalTheory.HeckeGal GlobalTheory.LocGL GlobalTheory.GalOfCusp GlobalTheory.GLq
open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.GalCut GlobalTheory.RoadU GlobalTheory.AboveL
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RoadU.TwistSupp

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Rewrite using `[IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]`.
-/
theorem nu_nu_neg (x : IrrGL k) (s : ℂ) : (x.nu s).nu (-s) = x := by
  rw [IrrGL.nu_nu, add_neg_cancel, IrrGL.nu_zero]

/- English proof (translation)
Introduce `x y h` and use `by have := congrArg (fun z : IrrGL k => z.nu (-s)) h simpa only [nu_nu_neg] using this`.
-/
theorem nu_injective (s : ℂ) : Function.Injective fun x : IrrGL k => x.nu s := fun x y h => by
  have := congrArg (fun z : IrrGL k => z.nu (-s)) h
  simpa only [nu_nu_neg] using this

/- English proof (translation)
Unfold `chars`. Rewrite using `[Multiset.map_map]`. Use `Multiset.map_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]`. Conclude with `IrrGL.ofChar_inj.2 (h j)`.
-/
theorem chars_eq_map_nu {n : ℕ} (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j))
    (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ) (h : ∀ j, ξ' j = ξ j * absPow k s) :
    chars ξ' hξ' = (chars ξ hξ).map fun y => y.nu s := by
  unfold chars
  rw [Multiset.map_map]
  refine Multiset.map_congr rfl fun j _ => ?_
  simp only [Function.comp_apply, IrrGL.nu, IrrGL.tw_ofChar]
  exact IrrGL.ofChar_inj.2 (h j)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h y hy z hz e`. Use `h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_` and prove the remaining obligations. Rewrite using `[e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]`. Introduce `h y' hy' z' hz' e`.

Take `⟨y, hy, rfl⟩` from `Multiset.mem_map.1 hy'`. Take `⟨z, hz, rfl⟩` from `Multiset.mem_map.1 hz'`. Use `h y hy z hz (nu_injective s ?_)` and prove the remaining obligations. Simplify using `only`. Rewrite using `[e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]`.
-/
theorem unlinked_map_nu (m : Multiset (IrrGL k)) (s : ℂ) :
    Unlinked (m.map fun y => y.nu s) ↔ Unlinked m := by
  constructor
  · intro h y hy z hz e
    refine h (y.nu s) (Multiset.mem_map_of_mem _ hy) (z.nu s) (Multiset.mem_map_of_mem _ hz) ?_
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]
  · intro h y' hy' z' hz' e
    obtain ⟨y, hy, rfl⟩ := Multiset.mem_map.1 hy'
    obtain ⟨z, hz, rfl⟩ := Multiset.mem_map.1 hz'
    refine h y hy z hz (nu_injective s ?_)
    simp only
    rw [e, IrrGL.nu_nu, IrrGL.nu_nu, add_comm]

/- English proof (translation)
Introduce `k _ _ _ _ _ x n ξ ξ' hξ hξ' s h`. Rewrite using `[chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]`. Use `⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩` and prove the remaining obligations. Establish `H'` using `SupportRing.hasSupport_nu H (-s)`. Rewrite `H'` using `[nu_nu_neg, Multiset.map_map]`.

Simplify `H'` using `only [Function.comp_def, nu_nu_neg, Multiset.map_id']`.
-/
theorem supp_nu_chars : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] [CharZero k] (x : IrrGL k) (n : ℕ) (ξ ξ' : Fin n → (kˣ →* ℂˣ)) (hξ : ∀ j, IsSmoothChar (ξ j)) (hξ' : ∀ j, IsSmoothChar (ξ' j)) (s : ℂ), (∀ j, ξ' j = ξ j * absPow k s) → (HasSupport x.rep (chars ξ hξ) ↔ HasSupport (x.nu s).rep (chars ξ' hξ')) ∧ (Unlinked (chars ξ hξ) ↔ Unlinked (chars ξ' hξ')) := by
  intro k _ _ _ _ _ x n ξ ξ' hξ hξ' s h
  rw [chars_eq_map_nu ξ ξ' hξ hξ' s h, unlinked_map_nu]
  refine ⟨⟨fun H => SupportRing.hasSupport_nu H s, fun H => ?_⟩, Iff.rfl⟩
  have H' := SupportRing.hasSupport_nu H (-s)
  rw [nu_nu_neg, Multiset.map_map] at H'
  simpa only [Function.comp_def, nu_nu_neg, Multiset.map_id'] using H'

end GlobalTheory.RoadU.TwistSupp
