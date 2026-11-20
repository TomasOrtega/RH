import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.NonemptyTorusExtensionOfIsAlgClosed
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Definitions.Uniformization.PointEqOfSubsingleton
import Development.AbelianVarietyTheory.BlockTheory.ExistenceTori.GeneratorValues
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsCongOfCongOnFixed
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GaloisOfPrimePowerDegree
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.RangeAlgebraMapEqIInfDiscreteValuationSubring
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIntegralQuotientDominatingValuationSubringStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.AutomorphismCongrOneOnAdjoinRootUniformiserStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj

namespace GlobalTheory.InertiaTameRoot

/- English proof (translation)
Introduce `W _ _ _ _ _ F _ _ _ ϖ hϖ k hk`. Set `K` to `FractionRing W`. Use `letI : Algebra W F := ((algebraMap K F).comp (algebraMap W K)).toAlgebra`. Use `haveI : IsScalarTower W K F := .of_algebraMap_eq fun _ => rfl`. Establish `hk0 : k ≠ 0`.

Introduce and unpack `rfl`. Conclude with `not_isUnit_zero (M₀ := W) (by simpa using hk)`. Set `f : W →+* F` to `algebraMap W F`. Establish `hf : Function.Injective f` using `(algebraMap K F).injective.comp (IsFractionRing.injective W K)`. Take `⟨O, hO⟩` from `(LocalSubring.range f).exists_le_valuationSubring`.

Take `⟨h1, hloc⟩` from `(GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom f O).1 hO`. Establish `h2` using `((GlobalTheory.localSubring_range_le_valuationSubring_iff f O).1 hO).2`. Use `haveI : CharZero K := inferInstance`. Use `haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective`. Use `haveI : IsAlgClosed F := IsAlgClosure.isAlgClosed K`.

Take `⟨π, hπ⟩` from `IsAlgClosed.exists_pow_nat_eq (f ϖ) (Nat.pos_of_ne_zero hk0)`. Use `haveI : NeZero (k : F) := ⟨by exact_mod_cast hk0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot F k`. Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`.

Rewrite `hπ` using `[zero_pow hk0, eq_comm, map_eq_zero_iff f hf]`. Conclude with `hϖ.ne_zero hπ`. Establish `hmin` using `GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := π) hπ`. Establish `hmin'` using `GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := ζ * π) (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ)`. Use `haveI : IsGalois K F := {}`.

Take `⟨g, hg⟩` from `(Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1 (hmin'.trans hmin.symm)`. Express the relevant statement in the definitionally equal form `g π = ζ * π at hg`. Set `S` to `integralClosure W F`. Establish `hc : SMulCommClass (F ≃ₐ[K] F) W F` using `⟨fun g v x => by`. Rewrite using `[← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]`.

Simplify using `only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩`. Use `letI : TopologicalSpace S := ⊥`. Use `haveI : DiscreteTopology S := ⟨rfl⟩`. Use `haveI : ContinuousSMul (F ≃ₐ[K] F) S := by`. Rewrite using `[continuousSMul_iff_stabilizer_isOpen]`.

Introduce `x`. Use `stabilizer_isOpen_of_isIntegral (K := K) (x : F)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]`.

Conclude with `Subtype.ext_iff`. Set `H` to `MulAction.stabilizer (F ≃ₐ[K] F) π`. Establish `hH : IsClosed (H : Set (F ≃ₐ[K] F))` using `H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)`. Use `haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact`. Set `φ : W →+* O` to `f.codRestrict O h1`.

Use `letI : Algebra W O := φ.toAlgebra`. Use `haveI : IsScalarTower W O F := .of_algebraMap_eq fun _ => rfl`. Establish `hSO : ∀ b : F, IsIntegral W b → b ∈ O`. Introduce `b hb`. Take `⟨y, hy⟩` from `(IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hb.tower_top`.

Rewrite using `[← hy]`. Conclude with `y.2`. Set `incl : S →+* O` to `(S.val.toRingHom).codRestrict O (fun b => hSO b b.2)`. Set `Q : Ideal S` to `(maximalIdeal O).comap incl`. Establish `hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1` using `fun b => ValuationSubring.valuation_lt_one_iff O (incl b)`.

Take `⟨a₁, ha₁, a₂, ha₂, hcong⟩` from `GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g (fun b hb => by`. Rewrite using `[hQ]`. Use `GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser W F O h1 h2 ϖ hϖ k hk0 π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))` and prove the remaining obligations. Rewrite using `[← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}), IntermediateField.mem_fixedField_iff]`. Introduce `e he`.

Conclude with `congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))`. Set `σ` to `a₂ * g * a₁`. Establish `hσπ : σ π = a₂ ζ * π`. Establish `e1 : a₁ π = π` using `ha₁`. Establish `e2 : a₂ π = π` using `ha₂`.

Simplify using `only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]`. Establish `hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1` using `fun b hb => (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)`. Use `⟨O, φ, σ.toAlgHom, π, hloc, fun w => rfl, fun x hx => ?_, hπ, ?_⟩` and prove the remaining obligations. Take `⟨s, t, hs, ht, hs1, e⟩` from `GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring W F O h1 h2 x hx`. Express the relevant statement in the definitionally equal form `O.valuation (σ x - x) < 1`.

Establish `hs'` using `hσS s hs`. Establish `ht'` using `hσS t ht`. Establish `htv : O.valuation t ≤ 1` using `(O.valuation_le_one_iff _).mpr (hSO t ht)`. Establish `hσs : O.valuation (σ s) = 1`. Establish `: σ s = s + (σ s - s)` using `by ring`.

Rewrite using `[this, Valuation.map_add_eq_of_lt_left _ (by rw [hs1]; exact hs'), hs1]`. Establish `key : s * σ s * (σ x - x) = s * (σ t - t) - t * (σ s - s)`. Rewrite using `[← e, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hv : O.valuation (s * σ s * (σ x - x)) < 1`.

Rewrite using `[key]`. Use `Valuation.map_sub_lt _ ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, hs1, _root_.one_mul]`. Conclude with `ht'`. Rewrite using `[map_mul]`.

Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' htv) hs'`. Rewrite `hv` using `[map_mul, map_mul, hs1, hσs, _root_.one_mul, _root_.one_mul]`. Then use the resulting hypothesis. Express the relevant statement in the definitionally equal form `IsPrimitiveRoot (σ π / π) k`. Rewrite using `[hσπ, mul_div_cancel_right₀ _ hπ0]`. Conclude with `hζ.map_of_injective a₂.injective`.
-/
theorem exists_inertia_moves_root : ∀ (W : Type) [CommRing W] [IsDomain W] [IsDiscreteValuationRing W] [IsAdicComplete (maximalIdeal W) W] [CharZero W]
    (F : Type) [Field F] [Algebra (FractionRing W) F] [IsAlgClosure (FractionRing W) F] (ϖ : W), Irreducible ϖ →
    ∀ k : ℕ, IsUnit (k : W) → ∃ (O : ValuationSubring F) (φ : W →+* O) (σ : F →ₐ[FractionRing W] F) (π : F),
      IsLocalHom φ ∧ (∀ w, (φ w : F) = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) w)) ∧
      (∀ x ∈ O, O.valuation (σ x - x) < 1) ∧ π ^ k = algebraMap (FractionRing W) F (algebraMap W (FractionRing W) ϖ) ∧
      IsPrimitiveRoot (σ π / π) k := by
  intro W _ _ _ _ _ F _ _ _ ϖ hϖ k hk
  let K := FractionRing W
  letI : Algebra W F := ((algebraMap K F).comp (algebraMap W K)).toAlgebra
  haveI : IsScalarTower W K F := .of_algebraMap_eq fun _ => rfl
  have hk0 : k ≠ 0 := by
    rintro rfl
    exact not_isUnit_zero (M₀ := W) (by simpa using hk)
  let f : W →+* F := algebraMap W F
  have hf : Function.Injective f := (algebraMap K F).injective.comp (IsFractionRing.injective W K)
  obtain ⟨O, hO⟩ := (LocalSubring.range f).exists_le_valuationSubring
  obtain ⟨h1, hloc⟩ := (GlobalTheory.localSubring_range_le_valuationSubring_iff_isLocalHom f O).1 hO
  have h2 := ((GlobalTheory.localSubring_range_le_valuationSubring_iff f O).1 hO).2
  haveI : CharZero K := inferInstance
  haveI : CharZero F := charZero_of_injective_algebraMap (algebraMap K F).injective
  haveI : IsAlgClosed F := IsAlgClosure.isAlgClosed K
  obtain ⟨π, hπ⟩ := IsAlgClosed.exists_pow_nat_eq (f ϖ) (Nat.pos_of_ne_zero hk0)
  haveI : NeZero (k : F) := ⟨by exact_mod_cast hk0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot F k
  have hπ0 : π ≠ 0 := by
    rintro rfl
    rw [zero_pow hk0, eq_comm, map_eq_zero_iff f hf] at hπ
    exact hϖ.ne_zero hπ
  have hmin := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := π) hπ
  have hmin' := GlobalTheory.TameKummer.minpoly_eq K hϖ hk0 (ρ := ζ * π)
    (by rw [mul_pow, hζ.pow_eq_one, _root_.one_mul]; exact hπ)
  haveI : IsGalois K F := {}
  obtain ⟨g, hg⟩ := (Normal.minpoly_eq_iff_mem_orbit (F := K) F (x := ζ * π) (y := π)).1
    (hmin'.trans hmin.symm)
  change g π = ζ * π at hg

  let S := integralClosure W F
  have hc : SMulCommClass (F ≃ₐ[K] F) W F := ⟨fun g v x => by
    rw [← IsScalarTower.algebraMap_smul K v x, ← IsScalarTower.algebraMap_smul K v (g • x)]
    simp only [AlgEquiv.smul_def, Algebra.smul_def, _root_.map_mul, AlgEquiv.commutes]⟩
  letI : TopologicalSpace S := ⊥
  haveI : DiscreteTopology S := ⟨rfl⟩
  haveI : ContinuousSMul (F ≃ₐ[K] F) S := by
    rw [continuousSMul_iff_stabilizer_isOpen]
    intro x
    have := stabilizer_isOpen_of_isIntegral (K := K) (x : F)
    convert this using 1
    ext g
    simp only [SetLike.mem_coe, MulAction.mem_stabilizer_iff]
    exact Subtype.ext_iff
  let H := MulAction.stabilizer (F ≃ₐ[K] F) π
  have hH : IsClosed (H : Set (F ≃ₐ[K] F)) :=
    H.isClosed_of_isOpen (stabilizer_isOpen_of_isIntegral (K := K) π)
  haveI : CompactSpace H := isCompact_iff_compactSpace.mp hH.isCompact
  let φ : W →+* O := f.codRestrict O h1
  letI : Algebra W O := φ.toAlgebra
  haveI : IsScalarTower W O F := .of_algebraMap_eq fun _ => rfl
  have hSO : ∀ b : F, IsIntegral W b → b ∈ O := by
    intro b hb
    obtain ⟨y, hy⟩ := (IsIntegrallyClosed.isIntegral_iff (R := O) (K := F)).mp hb.tower_top
    rw [← hy]
    exact y.2
  let incl : S →+* O := (S.val.toRingHom).codRestrict O (fun b => hSO b b.2)
  let Q : Ideal S := (maximalIdeal O).comap incl
  have hQ : ∀ b : S, b ∈ Q ↔ O.valuation (b : F) < 1 := fun b =>
    ValuationSubring.valuation_lt_one_iff O (incl b)
  obtain ⟨a₁, ha₁, a₂, ha₂, hcong⟩ := GlobalTheory.InertiaMovesRoot.exists_cong_of_cong_on_fixed (R := W) H Q g
    (fun b hb => by
      rw [hQ]
      refine GlobalTheory.T.automorphism_congr_one_on_adjoin_root_uniformiser W F O h1 h2 ϖ hϖ k hk0 π hπ g b ?_ ((O.valuation_le_one_iff _).mpr (hSO b b.2))
      rw [← InfiniteGalois.fixedField_fixingSubgroup (IntermediateField.adjoin K {π}),
        IntermediateField.mem_fixedField_iff]
      intro e he
      exact congrArg Subtype.val (hb e (he ⟨π, IntermediateField.mem_adjoin_simple_self K π⟩)))
  let σ := a₂ * g * a₁
  have hσπ : σ π = a₂ ζ * π := by
    have e1 : a₁ π = π := ha₁
    have e2 : a₂ π = π := ha₂
    simp only [σ, AlgEquiv.mul_apply, e1, hg, map_mul, e2]
  have hσS : ∀ b : F, IsIntegral W b → O.valuation (σ b - b) < 1 := fun b hb =>
    (hQ (σ • ⟨b, hb⟩ - ⟨b, hb⟩)).1 (hcong ⟨b, hb⟩)
  refine ⟨O, φ, σ.toAlgHom, π, hloc, fun w => rfl, fun x hx => ?_, hπ, ?_⟩
  · obtain ⟨s, t, hs, ht, hs1, e⟩ := GlobalTheory.T.exists_integral_quotient_dominating_valuationSubring W F O h1 h2 x hx
    change O.valuation (σ x - x) < 1
    have hs' := hσS s hs
    have ht' := hσS t ht
    have htv : O.valuation t ≤ 1 := (O.valuation_le_one_iff _).mpr (hSO t ht)
    have hσs : O.valuation (σ s) = 1 := by
      have : σ s = s + (σ s - s) := by ring
      rw [this, Valuation.map_add_eq_of_lt_left _ (by rw [hs1]; exact hs'), hs1]
    have key : s * σ s * (σ x - x) = s * (σ t - t) - t * (σ s - s) := by
      rw [← e, map_mul]; ring
    have hv : O.valuation (s * σ s * (σ x - x)) < 1 := by
      rw [key]
      refine Valuation.map_sub_lt _ ?_ ?_
      · rw [map_mul, hs1, _root_.one_mul]; exact ht'
      · rw [map_mul]
        exact lt_of_le_of_lt (mul_le_of_le_one_left' htv) hs'
    rwa [map_mul, map_mul, hs1, hσs, _root_.one_mul, _root_.one_mul] at hv
  · change IsPrimitiveRoot (σ π / π) k
    rw [hσπ, mul_div_cancel_right₀ _ hπ0]
    exact hζ.map_of_injective a₂.injective

end GlobalTheory.InertiaTameRoot
