import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond

noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabW

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

/- English proof (translation)
Introduce `F _ _ U hU x`. Take `⟨m, hm, hmx⟩` from `PIW.AdelClassFin.DictRing.af_denom x`. Take `⟨N, hN1, hNU⟩` from `PI.InvTopW.finite_neighbourhood_second F U (hU.mem_nhds U.zero_mem)`. Take `⟨β, y, hy, hxy⟩` from `PIW.AdelClassFin.DictRing.af_approx _ hmx (m * N) (Nat.mul_pos hm (by omega))`. Use `⟨(β : F) / (m : F), ?_⟩` and prove the remaining obligations.

Establish `hmF : (m : F) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F))` using `(IsUnit.mk0 _ hmF).map _`. Establish `key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) = (N : FiniteAdeleRing (𝓞 F) F) * y`. Apply `hu.mul_left_cancel` to reduce the goal to its premises. Establish `e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F)` using `map_natCast _ m`.

Establish `e2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) = algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β`. Rewrite using `[← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F]`. Rewrite using `[mul_sub, e2, e1]`. Rewrite using `[hxy]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`. Conclude with `hNU y hy`.
-/
theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom x
  obtain ⟨N, hN1, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F U (hU.mem_nhds U.zero_mem)
  obtain ⟨β, y, hy, hxy⟩ := PIW.AdelClassFin.DictRing.af_approx _ hmx (m * N)
    (Nat.mul_pos hm (by omega))
  refine ⟨(β : F) / (m : F), ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have hu : IsUnit (algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F)) :=
    (IsUnit.mk0 _ hmF).map _
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
      (N : FiniteAdeleRing (𝓞 F) F) * y := by
    apply hu.mul_left_cancel
    have e1 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F) :=
      map_natCast _ m
    have e2 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) *
        algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / (m : F)) =
        algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β := by
      rw [← map_mul, mul_div_cancel₀ _ hmF, IsScalarTower.algebraMap_apply (𝓞 F) F]
    rw [mul_sub, e2, e1]
    rw [hxy]
    push_cast
    ring
  rw [key]
  exact hNU y hy

end PI.VolStabW
