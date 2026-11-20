import Mathlib
import Formalism.PeriodIntegrals.DivisionRowsRationalLattice
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.HermitianGroupLattices.AsAlgebraHomEG

noncomputable section

namespace PI.Dv.GLatHermW

open PI.Dv Formalism.BasicNotions

variable {K : Type} [Field K] [NumberField K] [StarRing K] {G : Type} [Group G] [Fintype G]

/- English proof (translation)
Take `⟨σ0, hσ0⟩` from `hS`. Apply `σ0.injective` to reduce the goal to its premises. Rewrite using `[hσ0, star_map_cf]`.
-/
theorem star_cf (hS : StarIsConj K) (T : GoodSet K G) (g : G) : star (cf T g) = cf T g⁻¹ := by
  obtain ⟨σ0, hσ0⟩ := hS
  apply σ0.injective
  rw [hσ0, star_map_cf]

/- English proof (translation)
Introduce `σ`. Rewrite using `[star_cf hS, star_map_cf]`.
-/
theorem isCM_cf (hS : StarIsConj K) (T : GoodSet K G) (g : G) : IsCM (cf T g) := by
  intro σ
  rw [star_cf hS, star_map_cf]

/- English proof (translation)
Introduce `σ`. Rewrite using `[star_add, map_add, map_add, star_add, ha σ, hb σ]`.
-/
theorem isCM_add {a b : K} (ha : IsCM a) (hb : IsCM b) : IsCM (a + b) := by
  intro σ
  rw [star_add, map_add, map_add, star_add, ha σ, hb σ]

/- English proof (translation)
Introduce `σ`. Rewrite using `[star_zero, map_zero, star_zero]`.
-/
theorem isCM_zero : IsCM (0 : K) := by
  intro σ
  rw [star_zero, map_zero, star_zero]

/- English proof (translation)
Introduce `σ`. Rewrite using `[star_mul', map_mul, map_mul, star_mul', ha σ, hb σ]`.
-/
theorem isCM_mul {a b : K} (ha : IsCM a) (hb : IsCM b) : IsCM (a * b) := by
  intro σ
  rw [star_mul', map_mul, map_mul, star_mul', ha σ, hb σ]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => rw [Finset.sum_empty]`. Conclude with `isCM_zero`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha]`.

Conclude with `isCM_add (hf a (Finset.mem_insert_self a s)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
theorem isCM_sum {ι : Type} (s : Finset ι) (f : ι → K) (hf : ∀ i ∈ s, IsCM (f i)) :
    IsCM (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => rw [Finset.sum_empty]; exact isCM_zero
  | insert a s ha ih =>
    rw [Finset.sum_insert ha]
    exact isCM_add (hf a (Finset.mem_insert_self a s))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `hH`. Use `⟨h1, h2, fun x y => ?_⟩` and prove the remaining obligations. Establish `hinv : ∀ g : G, h (ρ g x) y = h x (ρ g⁻¹ y)`. Introduce `g`. Use `h3 g x (ρ g⁻¹ y)` as an intermediate fact.

Rewrite `this` using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply]`. Then use the resulting hypothesis. Establish `hl : h ((ρ.asAlgebraHom (eG T)) x) y = ∑ g : G, star (cf T g) * h (ρ g x) y`. Rewrite using `[asAlgebraHom_eG, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]`.

Establish `hr : h x ((ρ.asAlgebraHom (eG T)) y) = ∑ g : G, cf T g * h x (ρ g y)`. Rewrite using `[asAlgebraHom_eG, LinearMap.sum_apply, map_sum]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, map_smul, smul_eq_mul]`. Rewrite using `[hl, hr]`.

Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[star_cf hS, hinv]`. Use `_ = ∑ g : G, cf T g * h x (ρ g y) := Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl`.
-/
theorem isHermE_of (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hH : IsGHerm A ρ h) :
    IsHermE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨h1, h2, h3⟩ := hH
  refine ⟨h1, h2, fun x y => ?_⟩
  have hinv : ∀ g : G, h (ρ g x) y = h x (ρ g⁻¹ y) := by
    intro g
    have := h3 g x (ρ g⁻¹ y)
    rwa [← Module.End.mul_apply, ← map_mul, mul_inv_cancel, map_one, Module.End.one_apply] at this
  have hl : h ((ρ.asAlgebraHom (eG T)) x) y = ∑ g : G, star (cf T g) * h (ρ g x) y := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, LinearMap.sum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, LinearMap.map_smulₛₗ, LinearMap.smul_apply, smul_eq_mul, starRingEnd_apply]
  have hr : h x ((ρ.asAlgebraHom (eG T)) y) = ∑ g : G, cf T g * h x (ρ g y) := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, smul_eq_mul]
  rw [hl, hr]
  calc ∑ g : G, star (cf T g) * h (ρ g x) y = ∑ g : G, cf T g⁻¹ * h x (ρ g⁻¹ y) := by
        refine Finset.sum_congr rfl fun g _ => ?_
        rw [star_cf hS, hinv]
    _ = ∑ g : G, cf T g * h x (ρ g y) :=
        Fintype.sum_equiv (Equiv.inv G) _ _ fun g => rfl

/- English proof (translation)
Take `⟨c1, c2, c3⟩` from `hC`. Use `⟨c1, fun i j => ?_, c3⟩` and prove the remaining obligations. Establish `he : A.b.repr ((ρ.asAlgebraHom (eG T)) (A.b j)) i = ∑ g : G, cf T g * A.b.repr (ρ g (A.b j)) i`. Rewrite using `[asAlgebraHom_eG, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations.

Rewrite using `[LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]`. Rewrite using `[he]`. Conclude with `isCM_sum _ _ fun g _ => isCM_mul (isCM_cf hS T g) (c2 g i j)`.
-/
theorem isCMFormE_of (T : GoodSet K G) (A : HLat K) (ρ : Representation K G A.V)
    (h : A.V →ₗ⋆[K] A.V →ₗ[K] K) (hS : StarIsConj K) (hC : IsCMForm A ρ h) :
    IsCMFormE A (ρ.asAlgebraHom (eG T)) h := by
  obtain ⟨c1, c2, c3⟩ := hC
  refine ⟨c1, fun i j => ?_, c3⟩
  have he : A.b.repr ((ρ.asAlgebraHom (eG T)) (A.b j)) i =
      ∑ g : G, cf T g * A.b.repr (ρ g (A.b j)) i := by
    rw [asAlgebraHom_eG, LinearMap.sum_apply, map_sum, Finsupp.finsetSum_apply]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, map_smul, Finsupp.smul_apply, smul_eq_mul]
  rw [he]
  exact isCM_sum _ _ fun g _ => isCM_mul (isCM_cf hS T g) (c2 g i j)

/- English proof (translation)
Introduce `K _ _ _ _ G _ _ T A ρ h hS hH`. Conclude with `⟨isHermE_of T A ρ h hS hH, fun hC => isCMFormE_of T A ρ h hS hC⟩`.
-/
theorem glatHerm : PI.Dv.GLatHerm := by
  intro K _ _ _ _ G _ _ T A ρ h hS hH
  exact ⟨isHermE_of T A ρ h hS hH, fun hC => isCMFormE_of T A ρ h hS hC⟩

end PI.Dv.GLatHermW
