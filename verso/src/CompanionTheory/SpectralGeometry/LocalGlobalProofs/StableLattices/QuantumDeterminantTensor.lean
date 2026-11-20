import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.OmegaMinorStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.StableLattices.HeckeRankOneStatement
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds

noncomputable section

open Finset

namespace GlobalTheory.CompanionTheory.RgExh

open Formalism.REAL (qdet qminor Tm)
open _root_.CompanionTheory.RgExh
open _root_.CompanionTheory.RgExh.Hk

/- English proof (translation)
Unfold `Formalism.REAL.qdet Formalism.REAL.qminor`. Use `Commute.sum_left _ _ _ fun σ _ => ?_` and prove the remaining obligations. Use `Commute.mul_left (Int.cast_commute _ _) ?_` and prove the remaining obligations. Use `Commute.list_prod_left _ _ fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[List.mem_ofFn]`.

Take `⟨k, rfl⟩` from `hx`. Unfold `Formalism.REAL.Tm`. Use `Commute.add_left ?_ (h _ _)` and prove the remaining obligations. Use `split_ifs`. Conclude with `Algebra.commute_algebraMap_left _ _`.

Conclude with `Commute.zero_left _`.
-/
theorem commute_qdet_of {A : Type*} [Ring A] [Algebra ℂ A] {n : ℕ} (E : Fin n → Fin n → A) (T : A)
    (h : ∀ a b, Commute (E a b) T) (u : ℂ) : Commute (qdet E u) T := by
  unfold Formalism.REAL.qdet Formalism.REAL.qminor
  refine Commute.sum_left _ _ _ fun σ _ => ?_
  refine Commute.mul_left (Int.cast_commute _ _) ?_
  refine Commute.list_prod_left _ _ fun x hx => ?_
  rw [List.mem_ofFn] at hx
  obtain ⟨k, rfl⟩ := hx
  unfold Formalism.REAL.Tm
  refine Commute.add_left ?_ (h _ _)
  split_ifs
  · exact Algebra.commute_algebraMap_left _ _
  · exact Commute.zero_left _

/- English proof (translation)
Establish `hc` using `Formalism.REAL.qDetCentral (Module.End ℂ X.V) n X.E X.gl u`. Unfold `Commute SemiconjBy`. Use `LinearMap.ext fun f => funext fun b => ?_` and prove the remaining obligations. Simplify using `only [Module.End.mul_apply, LinearMap.compLeft_apply, Function.comp_apply, om, LinearMap.coe_mk, AddHom.coe_mk, map_sum]`. Conclude with `Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hc a b) (f a)`.
-/
theorem commute_compLeft_om {n : ℕ} (X : GMod n) (u : ℂ) :
    Commute ((qdet X.E u).compLeft (Fin n)) (om X) := by
  have hc := Formalism.REAL.qDetCentral (Module.End ℂ X.V) n X.E X.gl u
  unfold Commute SemiconjBy
  refine LinearMap.ext fun f => funext fun b => ?_
  simp only [Module.End.mul_apply, LinearMap.compLeft_apply, Function.comp_apply, om, LinearMap.coe_mk,
    AddHom.coe_mk, map_sum]
  exact Finset.sum_congr rfl fun a _ => LinearMap.congr_fun (hc a b) (f a)

/- English proof (translation)
Introduce `n X u`. Break down `n with _ | m` into its components or cases. Conclude with `LinearMap.ext fun f => funext fun i => i.elim0`. Establish `hT : ∀ a b, Commute (tensE X a b) (om X)`. Introduce `a b`.

Unfold `Commute SemiconjBy`. Use `LinearMap.ext fun f => funext fun c => ?_` and prove the remaining obligations. Establish `key : ∀ d, X.E a b (X.E d c (f d)) = ((if b = d then X.E a c else 0) - (if c = a then X.E d b else 0)) (f d) + X.E d c (X.E a b (f d))`. Introduce `d`. Establish `h1` using `LinearMap.congr_fun (X.gl a b d c) (f d)`.

Rewrite `h1` using `[LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add]`. Conclude with `h1`. Simplify using `only [Module.End.mul_apply, tensE, eOp, om, LinearMap.add_apply, LinearMap.compLeft_apply, Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, map_sum, map_add]`. Rewrite using `[Finset.sum_congr rfl fun d _ => key d]`. Distinguish the cases in `hca : c = a`.

Substitute `hca` using the available equality. Simplify using `[Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, Finset.sum_sub_distrib]`. Simplify using `only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Normalize the expressions using the abelian group laws. Simplify using `[Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, hca, Finset.sum_sub_distrib]`.

Simplify using `only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Normalize the expressions using the abelian group laws. Establish `hC : Commute (qdet (tensE X) u) (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X)` using `Commute.add_right ((Commute.one_right _).smul_right u) (commute_qdet_of _ _ hT u)`. Establish `hD : Commute ((qdet X.E u).compLeft (Fin (m + 1))) (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X)` using `Commute.add_right ((Commute.one_right _).smul_right u) (commute_compLeft_om X u)`. Rewrite using `[hC.eq, GlobalTheory.T.HeckeRankOne m X u, mul_add, GlobalTheory.T.OmegaMinor m X u, ← hD.eq]`.

Simplify using `only [add_smul, one_smul, mul_add, mul_one]`. Normalize the expressions using the abelian group laws.
-/
theorem qdetTens : QdetTens := by
  intro n X u
  rcases n with _ | m
  · exact LinearMap.ext fun f => funext fun i => i.elim0
  · have hT : ∀ a b, Commute (tensE X a b) (om X) := by
      intro a b
      unfold Commute SemiconjBy
      refine LinearMap.ext fun f => funext fun c => ?_
      have key : ∀ d, X.E a b (X.E d c (f d)) =
          ((if b = d then X.E a c else 0) - (if c = a then X.E d b else 0)) (f d) + X.E d c (X.E a b (f d)) := by
        intro d
        have h1 := LinearMap.congr_fun (X.gl a b d c) (f d)
        rw [LinearMap.sub_apply, Module.End.mul_apply, Module.End.mul_apply, sub_eq_iff_eq_add] at h1
        exact h1
      simp only [Module.End.mul_apply, tensE, eOp, om, LinearMap.add_apply, LinearMap.compLeft_apply,
        Function.comp_apply, LinearMap.coe_mk, AddHom.coe_mk, Pi.add_apply, map_sum, map_add]
      rw [Finset.sum_congr rfl fun d _ => key d]
      by_cases hca : c = a
      · subst hca
        simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
      · simp [Finset.sum_add_distrib, LinearMap.sub_apply, apply_ite, hca, Finset.sum_sub_distrib]
        simp only [ite_apply, LinearMap.zero_apply, Pi.zero_apply, Finset.sum_ite_eq, Finset.mem_univ, if_true]
        abel
    have hC : Commute (qdet (tensE X) u) (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_qdet_of _ _ hT u)
    have hD : Commute ((qdet X.E u).compLeft (Fin (m + 1)))
        (u • (1 : Module.End ℂ (Fin (m + 1) → X.V)) + om X) :=
      Commute.add_right ((Commute.one_right _).smul_right u) (commute_compLeft_om X u)
    rw [hC.eq, GlobalTheory.T.HeckeRankOne m X u, mul_add, GlobalTheory.T.OmegaMinor m X u, ← hD.eq]
    simp only [add_smul, one_smul, mul_add, mul_one]
    abel

end GlobalTheory.CompanionTheory.RgExh
