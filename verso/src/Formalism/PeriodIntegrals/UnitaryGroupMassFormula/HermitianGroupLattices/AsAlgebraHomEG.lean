import Mathlib
import Formalism.PeriodIntegrals.SameFormAllLevels
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianGroupLattices.StarMapTraceOfPowEqOne

noncomputable section

namespace PI.Dv.GLatHermW

open PI.Dv

variable {K : Type} [Field K] {G : Type} [Group G] [Fintype G]

def cf (T : GoodSet K G) (g : G) : K :=
  ∑ s, ((Module.finrank K (T.W s) : ℕ) : K) / ((Fintype.card G : ℕ) : K) *
    LinearMap.trace K (T.W s) (T.tau s g⁻¹)

/- English proof (translation)
Unfold `eG eS cf`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`.
-/
theorem eG_eq (T : GoodSet K G) : eG T = ∑ g : G, cf T g • MonoidAlgebra.of K G g := by
  unfold eG eS cf
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [Finset.sum_smul]

/- English proof (translation)
Rewrite using `[eG_eq, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, Representation.asAlgebraHom_of]`.
-/
theorem asAlgebraHom_eG {V : Type} [AddCommGroup V] [Module K V] (T : GoodSet K G)
    (ρ : Representation K G V) : ρ.asAlgebraHom (eG T) = ∑ g : G, cf T g • ρ g := by
  rw [eG_eq, map_sum]
  refine Finset.sum_congr rfl fun g _ => ?_
  rw [map_smul, Representation.asAlgebraHom_of]

/- English proof (translation)
Unfold `cf`. Rewrite using `[map_sum, map_sum, star_sum]`. Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, star_mul', star_map_trace_rep σ (T.tau s) g⁻¹, inv_inv]`. Use `congr 1`.

Rewrite using `[map_div₀, map_natCast, map_natCast, star_div₀, star_natCast, star_natCast]`.
-/
theorem star_map_cf (σ : K →+* ℂ) (T : GoodSet K G) (g : G) :
    star (σ (cf T g)) = σ (cf T g⁻¹) := by
  unfold cf
  rw [map_sum, map_sum, star_sum]
  refine Finset.sum_congr rfl fun s _ => ?_
  rw [map_mul, map_mul, star_mul', star_map_trace_rep σ (T.tau s) g⁻¹, inv_inv]
  congr 1
  rw [map_div₀, map_natCast, map_natCast, star_div₀, star_natCast, star_natCast]

end PI.Dv.GLatHermW
