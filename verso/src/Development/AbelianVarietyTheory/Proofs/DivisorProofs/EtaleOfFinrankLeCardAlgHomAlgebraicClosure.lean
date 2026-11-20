import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.JoinCastSucc
import ReciprocityTheory.SemistableReduction.TorusL2CauchyInequality
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.FramedLatticeZeroCycleHeight
open NumberField MvPolynomial ReciprocityTheory.MultiplicativeHeights GlobalTheory GlobalTheory.ChowHt GlobalTheory.Adelic GlobalTheory.HSCore GlobalTheory.HSChoice
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open scoped TensorProduct

namespace GlobalTheory

/- English proof (translation)
Introduce `E R _ _ _ _`. Use `⟨inferInstance, card_algHom_le_finrank E R (AlgebraicClosure E), fun hle => ?_⟩` and prove the remaining obligations. Use `set Ω := AlgebraicClosure E`. Use `set S := Ω ⊗[E] R`. Use `set ι := S →ₐ[Ω] Ω`.

Establish `: Fintype ι` using `Fintype.ofFinite ι`. Establish `hcard : Nat.card ι = Nat.card (R →ₐ[E] Ω)` using `(Nat.card_congr (AlgHom.liftEquiv E Ω R Ω)).symm`. Establish `hrank : Module.finrank Ω S = Module.finrank E R` using `Module.finrank_baseChange`. Set `φ : S →ₐ[Ω] (ι → Ω)` to `AlgHom.pi fun f => f`. Establish `hsurj : Function.Surjective φ.toLinearMap`.

Rewrite using `[← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]`. Introduce `g hg`. Establish `hs : ∀ i : ι, (fun j => if i = j then (1 : Ω) else 0) = Pi.single i 1` using `fun i => by`. Use extensionality with `j`. Simplify using `[Pi.single_apply, eq_comm]`.

Establish `hli` using `Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap Ω S Ω) (fun f => g (Pi.single f 1))`. Establish `hc : ∀ f, g (Pi.single f 1) = 0`. Apply `hli` to reduce the goal to its premises. Use `LinearMap.ext fun s => ?_` and prove the remaining obligations. Use `LinearMap.congr_fun hg s` as an intermediate fact.

Simplify using `only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this`. Rewrite using `[LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ g]`. Simplify using `only [hs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `[φ, mul_comm]`.

Use `LinearMap.ext fun x => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.pi_apply_eq_sum_univ g]`. Simplify using `[hs, hc]`. Establish `hinj : Function.Injective φ.toLinearMap`. Establish `hle' : Module.finrank Ω S ≤ Module.finrank Ω (ι → Ω)`.

Rewrite using `[Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard, hrank]`. Conclude with `hle`. Establish `hge : Module.finrank Ω (ι → Ω) ≤ Module.finrank Ω S`. Establish `h` using `LinearMap.finrank_range_le φ.toLinearMap`. Rewrite `h` using `[LinearMap.range_eq_top.mpr hsurj, finrank_top]`. Then use the resulting hypothesis.

Conclude with `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle' hge)).mpr hsurj`. Establish `: IsReduced S` using `isReduced_of_injective φ.toRingHom hinj`. Establish `: IsArtinianRing S` using `.of_finite Ω S`. Establish `hE : Algebra.Etale Ω S`. Establish `(I : MaximalSpectrum S) : Algebra.FormallyEtale Ω (S ⧸ I.asIdeal)`.

Set `` to `Ideal.Quotient.field I.asIdeal`. Conclude with `Algebra.FormallyEtale.of_isSeparable Ω (S ⧸ I.asIdeal)`. Conclude with `⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars Ω).symm, Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩`. Conclude with `Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω`.
-/
theorem etale_of_finrank_le_card_algHom_algebraicClosure : ∀ (E R : Type) [Field E] [CommRing R] [Algebra E R] [Module.Finite E R], Finite (R →ₐ[E] AlgebraicClosure E) ∧ Nat.card (R →ₐ[E] AlgebraicClosure E) ≤ Module.finrank E R ∧ (Module.finrank E R ≤ Nat.card (R →ₐ[E] AlgebraicClosure E) → Algebra.Etale E R) := by
  intro E R _ _ _ _
  refine ⟨inferInstance, card_algHom_le_finrank E R (AlgebraicClosure E), fun hle => ?_⟩
  classical
  set Ω := AlgebraicClosure E
  set S := Ω ⊗[E] R
  set ι := S →ₐ[Ω] Ω
  have : Fintype ι := Fintype.ofFinite ι
  have hcard : Nat.card ι = Nat.card (R →ₐ[E] Ω) :=
    (Nat.card_congr (AlgHom.liftEquiv E Ω R Ω)).symm
  have hrank : Module.finrank Ω S = Module.finrank E R := Module.finrank_baseChange
  let φ : S →ₐ[Ω] (ι → Ω) := AlgHom.pi fun f => f
  have hsurj : Function.Surjective φ.toLinearMap := by
    rw [← LinearMap.dualMap_injective_iff, injective_iff_map_eq_zero]
    intro g hg
    have hs : ∀ i : ι, (fun j => if i = j then (1 : Ω) else 0) = Pi.single i 1 := fun i => by
      ext j; simp [Pi.single_apply, eq_comm]
    have hli := Fintype.linearIndependent_iff.mp (linearIndependent_algHom_toLinearMap Ω S Ω)
      (fun f => g (Pi.single f 1))
    have hc : ∀ f, g (Pi.single f 1) = 0 := by
      apply hli
      refine LinearMap.ext fun s => ?_
      have := LinearMap.congr_fun hg s
      simp only [LinearMap.dualMap_apply, LinearMap.zero_apply] at this
      rw [LinearMap.zero_apply, ← this, LinearMap.pi_apply_eq_sum_univ g]
      simp only [hs, LinearMap.sum_apply, LinearMap.smul_apply, smul_eq_mul]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [φ, mul_comm]
    refine LinearMap.ext fun x => ?_
    rw [LinearMap.pi_apply_eq_sum_univ g]
    simp [hs, hc]
  have hinj : Function.Injective φ.toLinearMap := by
    have hle' : Module.finrank Ω S ≤ Module.finrank Ω (ι → Ω) := by
      rw [Module.finrank_fintype_fun_eq_card, ← Nat.card_eq_fintype_card, hcard, hrank]
      exact hle
    have hge : Module.finrank Ω (ι → Ω) ≤ Module.finrank Ω S := by
      have h := LinearMap.finrank_range_le φ.toLinearMap
      rwa [LinearMap.range_eq_top.mpr hsurj, finrank_top] at h
    exact (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (le_antisymm hle' hge)).mpr hsurj
  have : IsReduced S := isReduced_of_injective φ.toRingHom hinj
  have : IsArtinianRing S := .of_finite Ω S
  have hE : Algebra.Etale Ω S := by
    have (I : MaximalSpectrum S) : Algebra.FormallyEtale Ω (S ⧸ I.asIdeal) := by
      let := Ideal.Quotient.field I.asIdeal
      exact Algebra.FormallyEtale.of_isSeparable Ω (S ⧸ I.asIdeal)
    exact ⟨.of_equiv ((IsArtinianRing.equivPi S).restrictScalars Ω).symm,
      Algebra.FinitePresentation.of_finiteType.mp inferInstance⟩
  exact Algebra.Etale.of_etale_tensorProduct_of_faithfullyFlat Ω

end GlobalTheory
