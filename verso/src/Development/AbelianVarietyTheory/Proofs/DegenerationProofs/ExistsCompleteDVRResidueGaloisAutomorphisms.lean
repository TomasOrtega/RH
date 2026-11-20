import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissiblePadicIntMaximalIdeal
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsCompleteDvrFiniteSubalgebra
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.LN

namespace GlobalTheory

namespace ResidueGalois

/- English proof (translation)
Set `P : Ideal A` to `RingHom.ker p`. Set `Q : Ideal B` to `RingHom.ker q`. Establish `: P.IsPrime` using `RingHom.ker_isPrime p`. Establish `: Q.IsPrime` using `RingHom.ker_isPrime q`. Establish `: Q.LiesOver P` using `⟨by`.

Use extensionality with `x`. Simplify using `only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩`. Set `_ : Algebra (A ⧸ P) k` to `(RingHom.kerLift p).toAlgebra`. Set `_ : Algebra (B ⧸ Q) K` to `(RingHom.kerLift q).toAlgebra`. Set `_ : Algebra (A ⧸ P) K` to `((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra`.

Establish `: IsScalarTower (A ⧸ P) k K` using `.of_algebraMap_eq fun _ => rfl`. Establish `: IsScalarTower (A ⧸ P) (B ⧸ Q) K` using `.of_algebraMap_eq fun x => by`. Take `⟨x, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Conclude with `h x`. Establish `: FaithfulSMul (A ⧸ P) k` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)`.

Establish `: FaithfulSMul (B ⧸ Q) K` using `(faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)`. Establish `: IsFractionRing (A ⧸ P) k` using `IsFractionRing.of_field _ _ fun z => by`. Take `⟨x, rfl⟩` from `hp z`. Conclude with `⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩`. Establish `: IsFractionRing (B ⧸ Q) K` using `IsFractionRing.of_field _ _ fun z => by`.

Take `⟨x, rfl⟩` from `hq z`. Conclude with `⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩`. Establish `hn : Normal k K` using `Ideal.IsFractionRing.normal G P Q k K`. Establish `hs : Algebra.IsSeparable k K` using `inferInstance`. Use `⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩` and prove the remaining obligations.

Take `⟨σ, rfl⟩` from `IsFractionRing.stabilizerHom_surjective G P Q k K τ`. Conclude with `⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩`.
-/
theorem galois_of_isInvariant (A B G : Type) [CommRing A] [CommRing B] [Algebra A B] [Group G]
    [Finite G] [MulSemiringAction G B] [Algebra.IsInvariant A B G] [SMulCommClass G A B]
    (k K : Type) [Field k] [Field K] [Algebra k K] [CharZero k] (p : A →+* k) (q : B →+* K)
    (hp : Function.Surjective p) (hq : Function.Surjective q)
    (h : ∀ x, algebraMap k K (p x) = q (algebraMap A B x)) :
    FiniteDimensional k K ∧ IsGalois k K ∧
      ∀ τ : K ≃ₐ[k] K, ∃ σ : G, ∀ x, q (σ • x) = τ (q x) := by
  let P : Ideal A := RingHom.ker p
  let Q : Ideal B := RingHom.ker q
  have : P.IsPrime := RingHom.ker_isPrime p
  have : Q.IsPrime := RingHom.ker_isPrime q
  have : Q.LiesOver P := ⟨by
    ext x
    simp only [P, Q, Ideal.under, Ideal.mem_comap, RingHom.mem_ker, ← h, map_eq_zero]⟩
  let _ : Algebra (A ⧸ P) k := (RingHom.kerLift p).toAlgebra
  let _ : Algebra (B ⧸ Q) K := (RingHom.kerLift q).toAlgebra
  let _ : Algebra (A ⧸ P) K := ((algebraMap k K).comp (RingHom.kerLift p)).toAlgebra
  have : IsScalarTower (A ⧸ P) k K := .of_algebraMap_eq fun _ => rfl
  have : IsScalarTower (A ⧸ P) (B ⧸ Q) K := .of_algebraMap_eq fun x => by
    obtain ⟨x, rfl⟩ := Ideal.Quotient.mk_surjective x
    exact h x
  have : FaithfulSMul (A ⧸ P) k :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective p)
  have : FaithfulSMul (B ⧸ Q) K :=
    (faithfulSMul_iff_algebraMap_injective _ _).2 (RingHom.kerLift_injective q)
  have : IsFractionRing (A ⧸ P) k := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hp z
    exact ⟨Ideal.Quotient.mk P x, 1, by rw [map_one, div_one]; rfl⟩
  have : IsFractionRing (B ⧸ Q) K := IsFractionRing.of_field _ _ fun z => by
    obtain ⟨x, rfl⟩ := hq z
    exact ⟨Ideal.Quotient.mk Q x, 1, by rw [map_one, div_one]; rfl⟩
  have hn : Normal k K := Ideal.IsFractionRing.normal G P Q k K
  have hs : Algebra.IsSeparable k K := inferInstance
  refine ⟨Ideal.IsFractionRing.finite_of_isInvariant G P Q k K, { }, fun τ => ?_⟩
  obtain ⟨σ, rfl⟩ := IsFractionRing.stabilizerHom_surjective G P Q k K τ
  exact ⟨σ.1, fun x => (IsFractionRing.stabilizerHom_apply_apply_mk G P Q k K σ x).symm⟩

/- English proof (translation)
Use `Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)` as an intermediate fact. Rewrite using `[Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]`.
-/
theorem map_maximalIdeal_le {A B : Type} [CommRing A] [CommRing B] [IsLocalRing A]
    [IsLocalRing B] (f : A →+* B) (hf : f.IsIntegral) :
    (IsLocalRing.maximalIdeal A).map f ≤ IsLocalRing.maximalIdeal B := by
  have := Ideal.isMaximal_comap_of_isIntegral_of_isMaximal' f hf (IsLocalRing.maximalIdeal B)
  rw [Ideal.map_le_iff_le_comap, IsLocalRing.eq_maximalIdeal this]

end ResidueGalois

/- English proof (translation)
Introduce `V V' _ _ _ _ _ _ hV _ hu g hg hfin`. Take `⟨hd, hc, h0⟩` from `(cDvr_iff V).1 hV`. Set `_ : Algebra V V'` to `g.toAlgebra`. Establish `: Module.Finite V V'` using `hfin`. Establish `: FaithfulSMul V V'` using `(faithfulSMul_iff_algebraMap_injective _ _).2 hg`.

Set `K` to `FractionRing V`. Set `K'` to `FractionRing V'`. Set `_ : Algebra K K'` to `FractionRing.liftAlgebra V K'`. Establish `: IsScalarTower V K K'` using `FractionRing.isScalarTower_liftAlgebra V K'`. Establish `: FiniteDimensional K K'` using `inferInstance`.

Establish `: CharZero K` using `IsFractionRing.charZero_of_isFractionRing V`. Set `L` to `IntermediateField.normalClosure K K' (AlgebraicClosure K')`. Establish `: FiniteDimensional K L` using `inferInstance`. Establish `: IsGalois K L` using `inferInstance`. Set `W` to `integralClosure V L`.

Establish `hB : Module.Finite V W` using `IsIntegralClosure.finite V K L _`. Establish `hBd : IsDiscreteValuationRing W` using `ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L`. Establish `: IsFractionRing W L` using `IsIntegralClosure.isFractionRing_of_finite_extension V K L W`. Set `i : V' →ₐ[V] L` to `((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')`. Establish `hi : Function.Injective i` using `(algebraMap K' L).injective.comp (IsFractionRing.injective V' K')`.

Set `j : V' →ₐ[V] W` to `i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i`. Establish `hj : Function.Injective j` using `fun x y h => hi (congrArg Subtype.val h)`. Establish `hjg : ∀ x, j (g x) = algebraMap V W x` using `fun x => j.commutes x`. Establish `hjg' : (j : V' →+* W).comp g = algebraMap V W` using `RingHom.ext hjg`. Establish `hint : ((j : V' →+* W).comp g).IsIntegral`.

Rewrite using `[hjg']`. Conclude with `fun x => Algebra.IsIntegral.isIntegral x`. Establish `: CharZero L` using `charZero_of_injective_algebraMap (algebraMap K L).injective`. Use `⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W), (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W, inferInstance⟩, hj, ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint), ResidueGalois.map_maximalIdeal_le _ h …` and prove the remaining obligations. Introduce `k K₁ _ _ _ p q hp hq h`.

Establish `: CharZero k` using `⟨fun m n hmn => by`. Assume the negation of the conclusion as `hne`. Use `wlog hlt : m < n generalizing m n`. Conclude with `this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))`. Use `((hu (n - m) (by omega)).map p).ne_zero` as an intermediate fact.

Rewrite `this` using `[map_natCast, Nat.cast_sub hlt.le, hmn, sub_self]`. Conclude with `this rfl⟩`. Establish `: Algebra.IsInvariant V W (W ≃ₐ[V] W)` using `Algebra.isInvariant_of_isGalois' V K L W`. Establish `: Finite (W ≃ₐ[V] W)` using `Finite.of_equiv _ (galRestrict V K L W).toEquiv`. Take `⟨h₁, h₂, h₃⟩` from `ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq fun x => (h x).trans (congrArg q (hjg x))`.

Use `⟨h₁, h₂, fun τ => ?_⟩` and prove the remaining obligations. Take `⟨σ, hσ⟩` from `h₃ τ`. Use `⟨σ.toRingEquiv, fun x => ?_, hσ⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `σ (j (g x)) = j (g x)`. Rewrite using `[hjg, AlgEquiv.commutes]`.
-/
theorem exists_cDvr_residue_galois : ∀ (V V' : Type) [CommRing V] [IsDomain V] [IsLocalRing V] [CommRing V'] [IsDomain V'] [IsLocalRing V'], CDvr V → CDvr V' → (∀ n : ℕ, n ≠ 0 → IsUnit (n : V)) → ∀ g : V →+* V', Function.Injective g → g.Finite → ∃ (W : Type) (_ : CommRing W) (_ : IsDomain W) (_ : IsLocalRing W) (j : V' →+* W), CDvr W ∧ Function.Injective j ∧ (IsLocalRing.maximalIdeal V').map j ≤ IsLocalRing.maximalIdeal W ∧ (IsLocalRing.maximalIdeal V).map (j.comp g) ≤ IsLocalRing.maximalIdeal W ∧ ∀ (k K : Type) [Field k] [Field K] [Algebra k K] (p : V →+* k) (q : W →+* K), Function.Surjective p → Function.Surjective q → (∀ x, algebraMap k K (p x) = q (j (g x))) → FiniteDimensional k K ∧ IsGalois k K ∧ ∀ τ : K ≃ₐ[k] K, ∃ σ : W ≃+* W, (∀ x, σ (j (g x)) = j (g x)) ∧ ∀ x, q (σ x) = τ (q x) := by
  intro V V' _ _ _ _ _ _ hV _ hu g hg hfin
  obtain ⟨hd, hc, h0⟩ := (cDvr_iff V).1 hV
  let _ : Algebra V V' := g.toAlgebra
  have : Module.Finite V V' := hfin
  have : FaithfulSMul V V' := (faithfulSMul_iff_algebraMap_injective _ _).2 hg
  let K := FractionRing V
  let K' := FractionRing V'
  let _ : Algebra K K' := FractionRing.liftAlgebra V K'
  have : IsScalarTower V K K' := FractionRing.isScalarTower_liftAlgebra V K'
  have : FiniteDimensional K K' := inferInstance
  have : CharZero K := IsFractionRing.charZero_of_isFractionRing V
  let L := IntermediateField.normalClosure K K' (AlgebraicClosure K')
  have : FiniteDimensional K L := inferInstance
  have : IsGalois K L := inferInstance
  let W := integralClosure V L
  have hB : Module.Finite V W := IsIntegralClosure.finite V K L _
  have hBd : IsDiscreteValuationRing W := ReciprocityTheory.ChartRestriction.G.T0.FiniteAlgebraLocalCompletion.cl_dvr V K L
  have : IsFractionRing W L := IsIntegralClosure.isFractionRing_of_finite_extension V K L W
  let i : V' →ₐ[V] L :=
    ((IsScalarTower.toAlgHom K K' L).restrictScalars V).comp (IsScalarTower.toAlgHom V V' K')
  have hi : Function.Injective i :=
    (algebraMap K' L).injective.comp (IsFractionRing.injective V' K')
  let j : V' →ₐ[V] W := i.codRestrict W fun x => (Algebra.IsIntegral.isIntegral x).map i
  have hj : Function.Injective j := fun x y h => hi (congrArg Subtype.val h)
  have hjg : ∀ x, j (g x) = algebraMap V W x := fun x => j.commutes x
  have hjg' : (j : V' →+* W).comp g = algebraMap V W := RingHom.ext hjg
  have hint : ((j : V' →+* W).comp g).IsIntegral := by
    rw [hjg']
    exact fun x => Algebra.IsIntegral.isIntegral x
  have : CharZero L := charZero_of_injective_algebraMap (algebraMap K L).injective
  refine ⟨W, inferInstance, inferInstance, inferInstance, (j : V' →+* W),
    (cDvr_iff W).2 ⟨hBd, CompleteFiniteExtension.isAdicComplete_of_finite_local V W,
      inferInstance⟩, hj,
    ResidueGalois.map_maximalIdeal_le _ (RingHom.IsIntegral.tower_top g _ hint),
    ResidueGalois.map_maximalIdeal_le _ hint, ?_⟩
  intro k K₁ _ _ _ p q hp hq h
  have : CharZero k := ⟨fun m n hmn => by
    by_contra hne
    wlog hlt : m < n generalizing m n
    · exact this n m hmn.symm (Ne.symm hne) (lt_of_le_of_ne (not_lt.1 hlt) (Ne.symm hne))
    have := ((hu (n - m) (by omega)).map p).ne_zero
    rw [map_natCast, Nat.cast_sub hlt.le, hmn, sub_self] at this
    exact this rfl⟩
  have : Algebra.IsInvariant V W (W ≃ₐ[V] W) := Algebra.isInvariant_of_isGalois' V K L W
  have : Finite (W ≃ₐ[V] W) := Finite.of_equiv _ (galRestrict V K L W).toEquiv
  obtain ⟨h₁, h₂, h₃⟩ := ResidueGalois.galois_of_isInvariant V W (W ≃ₐ[V] W) k K₁ p q hp hq
    fun x => (h x).trans (congrArg q (hjg x))
  refine ⟨h₁, h₂, fun τ => ?_⟩
  obtain ⟨σ, hσ⟩ := h₃ τ
  refine ⟨σ.toRingEquiv, fun x => ?_, hσ⟩
  change σ (j (g x)) = j (g x)
  rw [hjg, AlgEquiv.commutes]

end GlobalTheory
