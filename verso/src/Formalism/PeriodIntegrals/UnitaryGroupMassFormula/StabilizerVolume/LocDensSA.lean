import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicClassFiniteness.DictRing
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.InvariantTopologyComparison.FiniteNeighbourhoodSecond

noncomputable section

open IsDedekindDomain NumberField

namespace PI.VolStabS

def SAf : Prop :=
  ∀ (F : Type) [Field F] [NumberField F] (U : AddSubgroup (FiniteAdeleRing (𝓞 F) F)),
    IsOpen (U : Set (FiniteAdeleRing (𝓞 F) F)) →
    ∀ x : FiniteAdeleRing (𝓞 F) F, ∃ a : F, x - algebraMap F (FiniteAdeleRing (𝓞 F) F) a ∈ U

/- English proof (translation)
Introduce `F _ _ U hU x`. Take `⟨N, hN1, hNU⟩` from `PI.InvTopW.finite_neighbourhood_second F (U : Set (FiniteAdeleRing (𝓞 F) F)) (hU.mem_nhds U.zero_mem)`. Take `⟨m, hm, hmx⟩` from `PIW.AdelClassFin.DictRing.af_denom x`. Take `⟨β, y, hy, hxy⟩` from `PIW.AdelClassFin.DictRing.af_approx _ hmx (N * m) (by positivity)`. Use `⟨(β : F) / m, ?_⟩` and prove the remaining obligations.

Establish `hmF : (m : F) ≠ 0` using `by exact_mod_cast hm.ne'`. Establish `e1 : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β = algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F)`. Rewrite using `[IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F)]`. Establish `h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F)` using `map_natCast _ m`. Establish `h2 : (m : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) = algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F)`.

Rewrite using `[← h3, ← map_mul, mul_div_cancel₀ _ hmF]`. Establish `hu : IsUnit (m : FiniteAdeleRing (𝓞 F) F)`. Rewrite using `[← h3]`. Conclude with `(IsUnit.mk0 _ hmF).map _`. Establish `key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) = (N : FiniteAdeleRing (𝓞 F) F) * y`.

Apply `hu.mul_left_cancel` to reduce the goal to its premises. Rewrite using `[mul_sub, h2, hxy, e1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[key]`.

Conclude with `hNU y hy`.
-/
theorem sAf_holds : SAf := by
  intro F _ _ U hU x
  obtain ⟨N, hN1, hNU⟩ := PI.InvTopW.finite_neighbourhood_second F (U : Set (FiniteAdeleRing (𝓞 F) F))
    (hU.mem_nhds U.zero_mem)
  obtain ⟨m, hm, hmx⟩ := PIW.AdelClassFin.DictRing.af_denom x
  obtain ⟨β, y, hy, hxy⟩ := PIW.AdelClassFin.DictRing.af_approx _ hmx (N * m) (by positivity)
  refine ⟨(β : F) / m, ?_⟩
  have hmF : (m : F) ≠ 0 := by exact_mod_cast hm.ne'
  have e1 : algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) β =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) := by
    rw [IsScalarTower.algebraMap_apply (𝓞 F) F (FiniteAdeleRing (𝓞 F) F)]
  have h3 : algebraMap F (FiniteAdeleRing (𝓞 F) F) (m : F) = (m : FiniteAdeleRing (𝓞 F) F) :=
    map_natCast _ m
  have h2 : (m : FiniteAdeleRing (𝓞 F) F) * algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) =
      algebraMap F (FiniteAdeleRing (𝓞 F) F) (β : F) := by
    rw [← h3, ← map_mul, mul_div_cancel₀ _ hmF]
  have hu : IsUnit (m : FiniteAdeleRing (𝓞 F) F) := by
    rw [← h3]
    exact (IsUnit.mk0 _ hmF).map _
  have key : x - algebraMap F (FiniteAdeleRing (𝓞 F) F) ((β : F) / m) =
      (N : FiniteAdeleRing (𝓞 F) F) * y := by
    apply hu.mul_left_cancel
    rw [mul_sub, h2, hxy, e1]
    push_cast
    ring
  rw [key]
  exact hNU y hy

end PI.VolStabS
