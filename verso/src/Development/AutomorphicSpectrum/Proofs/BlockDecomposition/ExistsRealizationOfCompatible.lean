import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LevelChainValuations.OneSTr

open CrystallineSemistableComparison.Pb.Kap

namespace GlobalTheory.CompanionTheory.KapRho

/- English proof (translation)
Take `⟨e, z, hz⟩` from `hC.lift j x hx`. Use `haveI := hC.fin j`. Establish `hunit : IsUnit (C.ℓ : B)` using `by first`. Consider the case `exact hC.unit`. Consider the case `simpa using hC.unit.map C.ι`.

Consider the case `simpa using hC.unit.map C.o`. Consider the case `simpa using (hC.unit.map C.lam).map C.ι`. Take `⟨u, hu⟩` from `hunit`. Set `w : C.W j` to `((u⁻¹ : Bˣ) : B) ^ e • C.b j z`. Set `bs₀` to `Module.finBasis K (C.V j)`.

Take `⟨g, hg, -⟩` from `hC.basis j bs₀ w`. Set `f : Module.Dual K (C.V j) →+ B` to `{ toFun := fun φ => ∑ t, C.o (φ (bs₀ t)) * g t map_zero' := by simp map_add' := fun φ ψ => by simp [add_mul, Finset.sum_add_distrib] }`. Use `⟨f, fun k φ => ?_, e, z, hz, fun {m} bs => ?_⟩` and prove the remaining obligations. Simplify using `[f, Finset.mul_sum, mul_assoc]`. Establish `key : ∑ s, f (bs.coord s) • C.μ j (bs s) = w`.

Simplify using `only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_smul]`. Rewrite using `[Finset.sum_comm, hg]`. Use `Finset.sum_congr rfl fun t _ => ?_` and prove the remaining obligations. Use `conv_rhs => rw [← bs.sum_repr (bs₀ t)]`. Rewrite using `[map_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun s _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.map_smulₛₗ, smul_smul, Module.Basis.coord_apply, mul_comm]`. Rewrite using `[key, ← hu, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]`.
-/
theorem exists_rho {Λ A B K : Type} [CommRing Λ] [CommRing A] [CommRing B] [Field K]
    (C : Chain.{1} Λ A B K) (hC : C.Good) {j : ℕ} (x : ∀ n, C.S n j) (hx : C.Comp x) :
    ∃ f : Module.Dual K (C.V j) →+ B, C.Rho x f := by
  obtain ⟨e, z, hz⟩ := hC.lift j x hx
  haveI := hC.fin j
  have hunit : IsUnit (C.ℓ : B) := by
    first
    | exact hC.unit
    | simpa using hC.unit.map C.ι
    | simpa using hC.unit.map C.o
    | simpa using (hC.unit.map C.lam).map C.ι
  obtain ⟨u, hu⟩ := hunit
  let w : C.W j := ((u⁻¹ : Bˣ) : B) ^ e • C.b j z
  let bs₀ := Module.finBasis K (C.V j)
  obtain ⟨g, hg, -⟩ := hC.basis j bs₀ w
  let f : Module.Dual K (C.V j) →+ B :=
    { toFun := fun φ => ∑ t, C.o (φ (bs₀ t)) * g t
      map_zero' := by simp
      map_add' := fun φ ψ => by simp [add_mul, Finset.sum_add_distrib] }
  refine ⟨f, fun k φ => ?_, e, z, hz, fun {m} bs => ?_⟩
  · simp [f, Finset.mul_sum, mul_assoc]
  · have key : ∑ s, f (bs.coord s) • C.μ j (bs s) = w := by
      simp only [f, AddMonoidHom.coe_mk, ZeroHom.coe_mk, Finset.sum_smul]
      rw [Finset.sum_comm, hg]
      refine Finset.sum_congr rfl fun t _ => ?_
      conv_rhs => rw [← bs.sum_repr (bs₀ t)]
      rw [map_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun s _ => ?_
      rw [LinearMap.map_smulₛₗ, smul_smul, Module.Basis.coord_apply, mul_comm]
    rw [key, ← hu, smul_smul, ← mul_pow, Units.mul_inv, one_pow, one_smul]

end GlobalTheory.CompanionTheory.KapRho
