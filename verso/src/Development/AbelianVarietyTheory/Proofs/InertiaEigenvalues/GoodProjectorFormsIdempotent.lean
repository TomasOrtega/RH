import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.DoubleCosetOperators.NHkRow
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.IntegralHeckeForms NumberField Polynomial Formalism.IndefR.NX
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.GoodSS.Idem

def rhoTw {D : D7} (S : RatDat D.ntw) (j : ℕ) : G0g D.nd →* Module.End D.what₂.LL (S.WL j) where
  toFun g := ((((S.A j).chi (S.eG.symm g))⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • (S.A j).ρ (S.eG.symm g)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul, mul_inv, Units.val_mul]
    rw [smul_mul_smul_comm]

/- English proof (translation)
Introduce `D S j i`. Use `set s := (D.nexp.eAlg i true).coeff.support with hs`. Establish `hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0` using `fun g hg => by`. Establish `h0 : (D.nexp.eAlg i true).coeff g = 0` using `Finsupp.notMem_support_iff.1 hg`. Establish `hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g)`.

Rewrite using `[D.nexp.eAlg_def]`. Both sides reduce to the same expression. Rewrite `h0` using `[hcoef]`. Conclude with `(map_eq_zero_iff _ (readLL0 S i true).injective).1 h0`. Set `rd : ↥D.LL0 →+* FractionRing (D.ntw.O i)` to `readLL0 S i true`.

Establish `hrd : Function.Injective rd` using `(readLL0 S i true).injective`. Set `eL : MonoidAlgebra ↥D.LL0 (G0g D.nd)` to `MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by`. Assume the negation of the conclusion as `h`. Conclude with `hg (hsupp g h))`. Establish `heL : ∀ g, eL.coeff g = D.nexp.eLL0 g` using `fun g => by`.

Simplify using `only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]`. Establish `hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises. Apply `Finsupp.ext` to reduce the goal to its premises. Introduce `g`.

Rewrite using `[MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]`. Both sides reduce to the same expression. Establish `hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd)`. Introduce `x y hxy`. Apply `MonoidAlgebra.ext` to reduce the goal to its premises.

Apply `Finsupp.ext` to reduce the goal to its premises. Introduce `g`. Apply `hrd` to reduce the goal to its premises. Rewrite using `[← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]`. Establish `hidem : eL * eL = eL` using `hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])`.

Set `eLL` to `MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL`. Establish `hP : goodProjW S j D.nexp.eLL0 = MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL`. Rewrite using `[MonoidAlgebra.lift_apply]`. Unfold `goodProjW`. Rewrite using `[finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by`.

Assume the negation of the conclusion as `hgs`. Conclude with `hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]`. Rewrite using `[Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by`. Assume the negation of the conclusion as `hgs`. Apply `Finsupp.mem_support_iff.1 hg` to reduce the goal to its premises.

Simplify using `only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Simplify using `only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul, Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression. Rewrite using `[hP, ← map_mul, ← map_mul, hidem]`.
-/
theorem goodProjW_idem : ∀ (D : D7) (S : RatDat D.ntw) (j : ℕ), D.ntw.Tw →
    goodProjW S j D.nexp.eLL0 * goodProjW S j D.nexp.eLL0 = goodProjW S j D.nexp.eLL0 := by
  intro D S j i
  set s := (D.nexp.eAlg i true).coeff.support with hs
  have hsupp : ∀ g, g ∉ s → D.nexp.eLL0 g = 0 := fun g hg => by
    have h0 : (D.nexp.eAlg i true).coeff g = 0 := Finsupp.notMem_support_iff.1 hg
    have hcoef : (D.nexp.eAlg i true).coeff g = readLL0 S i true (D.nexp.eLL0 g) := by
      rw [D.nexp.eAlg_def]; rfl
    rw [hcoef] at h0
    exact (map_eq_zero_iff _ (readLL0 S i true).injective).1 h0
  let rd : ↥D.LL0 →+* FractionRing (D.ntw.O i) := readLL0 S i true
  have hrd : Function.Injective rd := (readLL0 S i true).injective
  let eL : MonoidAlgebra ↥D.LL0 (G0g D.nd) :=
    MonoidAlgebra.ofCoeff (Finsupp.onFinset s D.nexp.eLL0 fun g hg => by
      by_contra h
      exact hg (hsupp g h))
  have heL : ∀ g, eL.coeff g = D.nexp.eLL0 g := fun g => by
    simp only [eL, MonoidAlgebra.coeff_ofCoeff, Finsupp.onFinset_apply]
  have hmap : MonoidAlgebra.mapRingHom (G0g D.nd) rd eL = D.nexp.eAlg i true := by
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    rw [MonoidAlgebra.coeff_mapRingHom, heL, D.nexp.eAlg_def]
    rfl
  have hinj : Function.Injective (MonoidAlgebra.mapRingHom (G0g D.nd) rd) := by
    intro x y hxy
    apply MonoidAlgebra.ext
    apply Finsupp.ext
    intro g
    apply hrd
    rw [← MonoidAlgebra.coeff_mapRingHom, ← MonoidAlgebra.coeff_mapRingHom, hxy]
  have hidem : eL * eL = eL := hinj (by rw [map_mul, hmap, D.nexp.eAlg_idem])
  let eLL := MonoidAlgebra.mapRingHom (G0g D.nd) (algebraMap ↥D.LL0 D.what₂.LL) eL
  have hP : goodProjW S j D.nexp.eLL0 =
      MonoidAlgebra.lift D.what₂.LL (Module.End D.what₂.LL (S.WL j)) (G0g D.nd) (rhoTw S j) eLL := by
    rw [MonoidAlgebra.lift_apply]
    unfold goodProjW
    rw [finsum_eq_sum_of_support_subset _ (s := s) fun g hg => by
      by_contra hgs
      exact hg (by simp only [hsupp g hgs, IntermediateField.coe_zero, zero_mul, zero_smul])]
    rw [Finsupp.sum_of_support_subset _ (s := s) (fun g hg => by
      by_contra hgs
      apply Finsupp.mem_support_iff.1 hg
      simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, hsupp g hgs, map_zero]) (fun a b => b • rhoTw S j a) (fun _ _ => zero_smul _ _)]
    refine Finset.sum_congr rfl fun g _ => ?_
    simp only [eLL, MonoidAlgebra.coeff_mapRingHom, heL, rhoTw, MonoidHom.coe_mk, OneHom.coe_mk, mul_smul,
      Units.val_inv_eq_inv_val]
    rfl
  rw [hP, ← map_mul, ← map_mul, hidem]

end GlobalTheory.GoodSS.Idem
