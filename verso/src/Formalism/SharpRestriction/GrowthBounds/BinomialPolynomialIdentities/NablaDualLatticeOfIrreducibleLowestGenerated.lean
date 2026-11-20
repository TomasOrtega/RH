import Formalism.SharpRestriction.GrowthBounds.BinomialPolynomialIdentities.DualWeightVectorApplyEqZeroOfNeNeg
import Formalism.SharpRestriction.GrowthBounds.RootWeights.DeltaIntegralEnvelopingStable

noncomputable section

open Finset

namespace Formalism.MainNotions.G.ColumnFamilies

open Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees Formalism.MainNotions.G.GLWeightTheory

section

variable {n : ℕ} {O : Type*} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  {V : Type*} [AddCommGroup V] [Module (KK O) V] [Module O V] [IsScalarTower O (KK O) V]

def NSub (E : GLOps n (KK O) V) (x0 : V) : Submodule O (Module.Dual (KK O) V) where
  carrier := {ψ | ∀ u' ∈ UZmon (dualOps E), Oval O (u' ψ x0)}
  zero_mem' := fun u' _ => by rw [map_zero]; exact Oval.zero
  add_mem' := fun {a b} ha hb u' hu => by
    rw [map_add, LinearMap.add_apply]; exact (ha u' hu).add (hb u' hu)
  smul_mem' := fun c ψ hψ u' hu => by
    rw [← algebraMap_smul (KK O) c ψ, map_smul, LinearMap.smul_apply, smul_eq_mul]
    exact Oval.mul ⟨c, rfl⟩ (hψ u' hu)

/- English proof (translation)
Introduce `u hu ψ hψ`. Establish `hψ' : ∀ u' ∈ UZmon (dualOps E), Oval O (u' ψ x0)` using `hψ`. Use `show ∀ u' ∈ UZmon (dualOps E), Oval O (u' (u ψ) x0)`. Introduce `u' hu'`. Establish `hu2 : u ∈ UZmon (dualOps E)` using `Submonoid.subset_closure hu`.

Conclude with `hψ' (u' * u) (Submonoid.mul_mem _ hu' hu2)`.
-/
theorem NSub_stable (E : GLOps n (KK O) V) (x0 : V) : UZStable (O := O) (dualOps E) (NSub (O := O) E x0) := by
  intro u hu ψ hψ
  have hψ' : ∀ u' ∈ UZmon (dualOps E), Oval O (u' ψ x0) := hψ
  show ∀ u' ∈ UZmon (dualOps E), Oval O (u' (u ψ) x0)
  intro u' hu'
  have hu2 : u ∈ UZmon (dualOps E) := Submonoid.subset_closure hu
  exact hψ' (u' * u) (Submonoid.mul_mem _ hu' hu2)

end

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem dualWeight_eq_neg_lowestWeight {n : ℕ} (mu : Fin n → ℤ) : dualWt mu = -lowWt mu := rfl

/- English proof (translation)
Introduce `p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv' hnorm`. Establish `hcz : CharZero (KK O)` using `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`. Take `⟨x0, hx0D, hx0w, hx01, hDel⟩` from `hGen p O S n V E mu v v' hI hv' hnorm`. Establish `hI'` using `hIrr p O S n V E mu v v' hI hv'`. Take `⟨hlow1, hlow2⟩` from `hLow p O S n V E mu v v' hI hv'`.

Establish `hE : (⨆ nu : Fin n → ℤ, weightSp E nu) = ⊤` using `hI.1.2.2`. Establish `hE' : (⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu) = ⊤` using `hI'.1.2.2`. Establish `hN1a : ∀ ψ ∈ otherWts (dualOps E) (dualWt mu), ψ x0 = 0`. Introduce `ψ hψ`. Establish `hle : otherWts (dualOps E) (dualWt mu) ≤ LinearMap.ker (LinearMap.applyₗ x0 : Module.Dual (KK O) V →ₗ[KK O] KK O)`.

Use `iSup₂_le fun nu hnu => ?_` and prove the remaining obligations. Introduce `φ hφ`. Conclude with `dual_weightVector_apply_eq_zero_of_ne_neg E hφ hx0w (fun h => hnu (h.trans (dualWeight_eq_neg_lowestWeight mu).symm))`. Conclude with `hle hψ`. Establish `hN1b : ∀ ψ : Module.Dual (KK O) V, ψ x0 = 0 → ψ ∈ otherWts (dualOps E) (dualWt mu)`.

Introduce `ψ hψ`. Take `⟨y0, F, f, hF, hy0, hf, hs⟩` from `weight_component_decomposition (O := O) (dualOps E) hE' (dualWt mu) ψ`. Establish `hrest` using `sum_other_weights_mem (O := O) (dualOps E) (dualWt mu) F hF f hf`. Establish `hy00 : y0 x0 = 0`. Establish `h1` using `congrArg (fun φ : Module.Dual (KK O) V => φ x0) hs`.

Simplify using `only [LinearMap.add_apply] at h1`. Rewrite `h1` using `[hψ, hN1a _ hrest, add_zero]`. Conclude with `h1.symm`. Establish `hy0z : y0 = 0`. Use extensionality with `x`.

Establish `hx : x ∈ ⨆ nu : Fin n → ℤ, weightSp E nu` using `hE ▸ Submodule.mem_top`. Proceed by induction on `hx using Submodule.iSup_induction' with`. Consider the case `mem nu x hx`. Distinguish the cases in `hnu : nu = lowWt mu`. Substitute `hnu` using the available equality.

Establish `h2 : x - (v' x) • x0 = 0`. Apply `hlow1 _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hx0w))` to reduce the goal to its premises. Rewrite using `[map_sub, map_smul, hx01, smul_eq_mul, mul_one, sub_self]`. Rewrite using `[sub_eq_zero.1 h2, map_smul, hy00, smul_zero, LinearMap.zero_apply]`. Rewrite using `[LinearMap.zero_apply]`.

Use `dual_weightVector_apply_eq_zero_of_ne_neg E hy0 hx (fun h => hnu ?_)` and prove the remaining obligations. Establish `: -lowWt mu = -nu` using `(dualWeight_eq_neg_lowestWeight mu).symm.trans h`. Conclude with `(neg_injective this).symm`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add, ha, hb]`.

Simplify using the standard rewrite rules. Rewrite using `[hs, hy0z, zero_add]`. Conclude with `hrest`. Establish `hNab : Nabla (O` using `O) (dualOps E) (dualWt mu) v' = (NSub (O := O) E x0 : Set _) := by`. Use extensionality with `φ`.

Prove the components needed by the constructor for the conclusion. Introduce `hφ u' hu`. Take `⟨c, hc⟩` from `hφ u' hu`. Use `hN1a _ hc` as an intermediate fact. Rewrite `this` using `[LinearMap.sub_apply, LinearMap.smul_apply, hx01, smul_eq_mul, mul_one, sub_eq_zero]`.

Conclude with `⟨c, this.symm⟩`. Introduce `hφ u' hu`. Take `⟨c, hc⟩` from `hφ u' hu`. Use `⟨c, hN1b _ ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.sub_apply, LinearMap.smul_apply, hx01, smul_eq_mul, mul_one, hc, sub_self]`.

Rewrite using `[hNab]`. Use extensionality with `φ`. Prove the components needed by the constructor for the conclusion. Introduce `hφ x hx`. Rewrite `hx` using `[hDel]`.

Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, rfl⟩` from `hy`. Establish `h1` using `dualLattice_comp_integralMonoid_mem E hE' (NSub (O := O) E x0) (NSub_stable E x0) hu φ hφ`. Establish `h2` using `h1 1 (Submonoid.one_mem _)`.

Conclude with `h2`. Consider the case `zero => rw [map_zero]`. Conclude with `Oval.zero`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `Oval.add ha hb`.

Consider the case `smul c a _ ha`. Rewrite using `[← algebraMap_smul (KK O) c a, map_smul, smul_eq_mul]`. Conclude with `Oval.mul ⟨c, rfl⟩ ha`. Introduce `hφ u' hu`. Conclude with `integral_dual_preserved_by_integralMonoid E hE (Delta (O := O) E v) (delta_integral_enveloping_stable E v) hu φ hφ x0 hx0D`.
-/
theorem nablaDualLattice_of_irreducible_lowest_generated (hIrr : ContragredientIrreducibleGeneratedByHighestWeight) (hLow : DualFunctionalInjectiveOnLowestWeightSpace) (hGen : DeltaGeneratedByLowestWeightVector) : NablaContragredientEqDualLatticeDelta := by
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hv' hnorm
  have hcz : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨x0, hx0D, hx0w, hx01, hDel⟩ := hGen p O S n V E mu v v' hI hv' hnorm
  have hI' := hIrr p O S n V E mu v v' hI hv'
  obtain ⟨hlow1, hlow2⟩ := hLow p O S n V E mu v v' hI hv'
  have hE : (⨆ nu : Fin n → ℤ, weightSp E nu) = ⊤ := hI.1.2.2
  have hE' : (⨆ nu : Fin n → ℤ, weightSp (dualOps E) nu) = ⊤ := hI'.1.2.2

  have hN1a : ∀ ψ ∈ otherWts (dualOps E) (dualWt mu), ψ x0 = 0 := by
    intro ψ hψ
    have hle : otherWts (dualOps E) (dualWt mu) ≤
        LinearMap.ker (LinearMap.applyₗ x0 : Module.Dual (KK O) V →ₗ[KK O] KK O) := by
      refine iSup₂_le fun nu hnu => ?_
      intro φ hφ
      exact dual_weightVector_apply_eq_zero_of_ne_neg E hφ hx0w (fun h => hnu (h.trans (dualWeight_eq_neg_lowestWeight mu).symm))
    exact hle hψ
  have hN1b : ∀ ψ : Module.Dual (KK O) V, ψ x0 = 0 → ψ ∈ otherWts (dualOps E) (dualWt mu) := by
    intro ψ hψ
    obtain ⟨y0, F, f, hF, hy0, hf, hs⟩ := weight_component_decomposition (O := O) (dualOps E) hE' (dualWt mu) ψ
    have hrest := sum_other_weights_mem (O := O) (dualOps E) (dualWt mu) F hF f hf
    have hy00 : y0 x0 = 0 := by
      have h1 := congrArg (fun φ : Module.Dual (KK O) V => φ x0) hs
      simp only [LinearMap.add_apply] at h1
      rw [hψ, hN1a _ hrest, add_zero] at h1
      exact h1.symm
    have hy0z : y0 = 0 := by
      ext x
      have hx : x ∈ ⨆ nu : Fin n → ℤ, weightSp E nu := hE ▸ Submodule.mem_top
      induction hx using Submodule.iSup_induction' with
      | mem nu x hx =>
        by_cases hnu : nu = lowWt mu
        · subst hnu
          have h2 : x - (v' x) • x0 = 0 := by
            apply hlow1 _ (Submodule.sub_mem _ hx (Submodule.smul_mem _ _ hx0w))
            rw [map_sub, map_smul, hx01, smul_eq_mul, mul_one, sub_self]
          rw [sub_eq_zero.1 h2, map_smul, hy00, smul_zero, LinearMap.zero_apply]
        · rw [LinearMap.zero_apply]
          refine dual_weightVector_apply_eq_zero_of_ne_neg E hy0 hx (fun h => hnu ?_)
          have : -lowWt mu = -nu := (dualWeight_eq_neg_lowestWeight mu).symm.trans h
          exact (neg_injective this).symm
      | zero => simp
      | add a b _ _ ha hb => rw [map_add, ha, hb]; simp
    rw [hs, hy0z, zero_add]
    exact hrest
  have hNab : Nabla (O := O) (dualOps E) (dualWt mu) v' = (NSub (O := O) E x0 : Set _) := by
    ext φ
    constructor
    · intro hφ u' hu
      obtain ⟨c, hc⟩ := hφ u' hu
      have := hN1a _ hc
      rw [LinearMap.sub_apply, LinearMap.smul_apply, hx01, smul_eq_mul, mul_one, sub_eq_zero] at this
      exact ⟨c, this.symm⟩
    · intro hφ u' hu
      obtain ⟨c, hc⟩ := hφ u' hu
      refine ⟨c, hN1b _ ?_⟩
      rw [LinearMap.sub_apply, LinearMap.smul_apply, hx01, smul_eq_mul, mul_one, hc, sub_self]
  rw [hNab]
  ext φ
  constructor
  · intro hφ x hx
    rw [hDel] at hx
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨u, hu, rfl⟩ := hy
      have h1 := dualLattice_comp_integralMonoid_mem E hE' (NSub (O := O) E x0) (NSub_stable E x0) hu φ hφ
      have h2 := h1 1 (Submonoid.one_mem _)
      exact h2
    | zero => rw [map_zero]; exact Oval.zero
    | add a b _ _ ha hb => rw [map_add]; exact Oval.add ha hb
    | smul c a _ ha =>
      rw [← algebraMap_smul (KK O) c a, map_smul, smul_eq_mul]
      exact Oval.mul ⟨c, rfl⟩ ha
  · intro hφ u' hu
    exact integral_dual_preserved_by_integralMonoid E hE (Delta (O := O) E v) (delta_integral_enveloping_stable E v) hu φ hφ x0 hx0D

/- English proof (translation)
Apply `Submonoid.closure_le.2` to reduce the goal to its premises. Introduce and unpack `_ ⟨⟨a, b⟩, rfl⟩`. Apply `Submonoid.subset_closure` to reduce the goal to its premises. Simplify using `only [Formalism.MainNotions.G.UZgens, Set.mem_setOf_eq]`. Distinguish the cases in `hab : a = b`.

Substitute `hab` using the available equality. Use `Or.inr ⟨a, 1, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.MainNotions.G.binomE]`. Use `Or.inl ⟨a, b, 1, hab, ?_⟩` and prove the remaining obligations. Simplify using `[Formalism.MainNotions.G.divPowE]`.
-/
theorem rationalMonoid_le_integralMonoid {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V) :
    Umon E ≤ UZmon E := by
  apply Submonoid.closure_le.2
  rintro _ ⟨⟨a, b⟩, rfl⟩
  apply Submonoid.subset_closure
  simp only [Formalism.MainNotions.G.UZgens, Set.mem_setOf_eq]
  by_cases hab : a = b
  · subst hab
    refine Or.inr ⟨a, 1, ?_⟩
    simp [Formalism.MainNotions.G.binomE]
  · refine Or.inl ⟨a, b, 1, hab, ?_⟩
    simp [Formalism.MainNotions.G.divPowE]

/- English proof (translation)
Unfold `Formalism.MainNotions.CovariantDegrees.WeylDualityLattice`. Introduce `p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hH himg`. Establish `hspan : Submodule.span (KK O) (Delta (O` using `O) E v : Set V) = ⊤ := by`. Rewrite using `[eq_top_iff, ← hI.2.2.2]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨u, hu, rfl⟩`. Apply `Submodule.subset_span` to reduce the goal to its premises. Use `show u v ∈ Delta (O := O) E v`. Conclude with `Submodule.subset_span ⟨u, rationalMonoid_le_integralMonoid E hu, rfl⟩`. Establish `hB` using `hBid O V (Delta (O := O) E v) (hFG p O S n V E mu v v' hI hH himg) hspan`.

Rewrite using `[hNab p O S n V E mu v v' hI hH himg]`. Conclude with `hB`.
-/
theorem weylDualityLattice_of_nabla_fg_bidual (D : Formalism.BasicNotions.D7) (hNab : NablaContragredientEqDualLatticeDelta) (hFG : DeltaFinitelyGenerated) (hBid : LatticeBiduality) : WeylDualityLattice D := by
  unfold Formalism.MainNotions.CovariantDegrees.WeylDualityLattice
  intro p _ O _ _ _ _ S n V _ _ _ _ E mu v v' hI hH himg
  have hspan : Submodule.span (KK O) (Delta (O := O) E v : Set V) = ⊤ := by
    rw [eq_top_iff, ← hI.2.2.2]
    refine Submodule.span_le.2 ?_
    rintro x ⟨u, hu, rfl⟩
    apply Submodule.subset_span
    show u v ∈ Delta (O := O) E v
    exact Submodule.subset_span ⟨u, rationalMonoid_le_integralMonoid E hu, rfl⟩
  have hB := hBid O V (Delta (O := O) E v) (hFG p O S n V E mu v v' hI hH himg) hspan
  rw [hNab p O S n V E mu v v' hI hH himg]
  exact hB

end Formalism.MainNotions.G.ColumnFamilies
