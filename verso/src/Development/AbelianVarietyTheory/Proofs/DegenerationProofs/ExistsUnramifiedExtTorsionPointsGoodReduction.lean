import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RigidSys
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ThetaCore
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.SabPull
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsDiscreteValuationRingOfMaximalIdealEqSpa
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ValuationRingOfFlatOfFormallyUnramified
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.IsUnitNatCastSections
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.CardTorsionPointsAbelianVarietyStatement

open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.TorsionUnram

/- English proof (translation)
Rewrite using `[← Spec.map_comp]`. Both sides reduce to the same expression.
-/
theorem spMap_comp' {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B)
    (g : B →+* C) : spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [← Spec.map_comp]; rfl

/- English proof (translation)
Set `q` to `RingHom.ker ε`. Establish `hq : q.IsPrime` using `RingHom.ker_isPrime _`. Set `B` to `Localization.AtPrime q`. Set `ρ' : B →+* Ω` to `IsLocalization.lift (M := q.primeCompl) (g := ε) fun y => Ne.isUnit y.2`. Establish `hρ : ρ'.comp (algebraMap W B) = ε` using `IsLocalization.lift_comp _`.

Establish `hρ' : ∀ w, ρ' (algebraMap W B w) = ε w` using `fun w => congr($hρ w)`. Establish `hloc : IsLocalHom ρ'` using `⟨fun b hb => by`. Take `⟨⟨w, s⟩, rfl⟩` from `IsLocalization.mk'_surjective q.primeCompl b`. Use `(IsLocalization.AtPrime.isUnit_mk'_iff B q w s).2 fun hw => hb.ne_zero ?_` and prove the remaining obligations. Establish `h1 : ρ' (IsLocalization.mk' B w s) * ε s = ε w`.

Rewrite using `[← hρ', ← hρ', ← map_mul, IsLocalization.mk'_spec]`. Establish `h2 : ε w = 0` using `hw`. Rewrite `h1` using `[h2]`. Conclude with `(mul_eq_zero.1 h1).resolve_right s.2⟩`. Establish `hTB : IsLocalHom (algebraMap T B)` using `⟨fun t ht => by`.

Use `hε.1 t ?_` and prove the remaining obligations. Use `ht.map ρ'` as an intermediate fact. Rewrite using `[IsScalarTower.algebraMap_apply T W B, hρ'] at this⟩` and apply the resulting hypothesis. Establish `hflat : Module.Flat T B` using `Module.Flat.trans T W B`. Establish `hess : Algebra.EssFiniteType T B` using `Algebra.EssFiniteType.comp T W B`.

Establish `hunr : Algebra.FormallyUnramified T B` using `Algebra.FormallyUnramified.comp T W B`. Take `⟨_, _⟩` from `exists_isDiscreteValuationRing_of_unramified T B`. Establish `halg` using `isAlgebraic_of_flat_of_formallyUnramified T B`. Establish `hff` using `Module.FaithfullyFlat.of_flat_of_isLocalHom (A := T) (B := B)`. Use `letI := j.toAlgebra`.

Establish `: Module.IsTorsionFree T F` using `Module.isTorsionFree_iff_algebraMap_injective.2 hj`. Set `j' : B →ₐ[T] F` to `IsAlgClosed.lift`. Establish `hj' : Function.Injective j'`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`.

Assume the negation of the conclusion as `hb0`. Establish `hne : (RingHom.ker j').comap (algebraMap T B) ≠ ⊥` using `Ideal.comap_ne_bot_of_algebraic_mem hb0 hb (halg.1 b)`. Use `hne (eq_bot_iff.2 fun t ht => ?_)` and prove the remaining obligations. Establish `h : j' (algebraMap T B t) = 0` using `ht`. Rewrite `h` using `[j'.commutes]`.

Conclude with `hj (h.trans (map_zero j).symm)`. Use `⟨B, inferInstance, inferInstance, inferInstance, algebraMap W B, ρ', j'.toRingHom, hloc, hρ, hj', ?_, fun π hπ => ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_eq]`. Conclude with `j'.comp_algebraMap`. Rewrite using `[← IsScalarTower.algebraMap_apply, IsDiscreteValuationRing.irreducible_iff_uniformizer, ← Algebra.FormallyUnramified.map_maximalIdeal (R := T), hπ.maximalIdeal_eq, Ideal.map_span, Set.image_singleton]`.
-/
theorem exists_local_of_etale {T W Ω F : Type} [CommRing T] [IsDomain T] [IsDiscreteValuationRing T]
    [CommRing W] [Algebra T W] [Algebra.Etale T W] [Field Ω] [Field F] [IsAlgClosed F]
    (ε : W →+* Ω) (hε : IsLocalHom (ε.comp (algebraMap T W))) (j : T →+* F)
    (hj : Function.Injective j) :
    ∃ (T' : Type) (_ : CommRing T') (_ : IsDomain T') (_ : IsDiscreteValuationRing T')
      (ψ : W →+* T') (ρ' : T' →+* Ω) (j' : T' →+* F), IsLocalHom ρ' ∧ ρ'.comp ψ = ε ∧
      Function.Injective j' ∧ j'.comp (ψ.comp (algebraMap T W)) = j ∧
      ∀ π : T, Irreducible π → Irreducible (ψ (algebraMap T W π)) := by
  let q := RingHom.ker ε
  have hq : q.IsPrime := RingHom.ker_isPrime _
  let B := Localization.AtPrime q
  let ρ' : B →+* Ω := IsLocalization.lift (M := q.primeCompl) (g := ε)
    fun y => Ne.isUnit y.2
  have hρ : ρ'.comp (algebraMap W B) = ε := IsLocalization.lift_comp _
  have hρ' : ∀ w, ρ' (algebraMap W B w) = ε w := fun w => congr($hρ w)
  have hloc : IsLocalHom ρ' := ⟨fun b hb => by
    obtain ⟨⟨w, s⟩, rfl⟩ := IsLocalization.mk'_surjective q.primeCompl b
    refine (IsLocalization.AtPrime.isUnit_mk'_iff B q w s).2 fun hw => hb.ne_zero ?_
    have h1 : ρ' (IsLocalization.mk' B w s) * ε s = ε w := by
      rw [← hρ', ← hρ', ← map_mul, IsLocalization.mk'_spec]
    have h2 : ε w = 0 := hw
    rw [h2] at h1
    exact (mul_eq_zero.1 h1).resolve_right s.2⟩
  have hTB : IsLocalHom (algebraMap T B) := ⟨fun t ht => by
    refine hε.1 t ?_
    have := ht.map ρ'
    rwa [IsScalarTower.algebraMap_apply T W B, hρ'] at this⟩
  have hflat : Module.Flat T B := Module.Flat.trans T W B
  have hess : Algebra.EssFiniteType T B := Algebra.EssFiniteType.comp T W B
  have hunr : Algebra.FormallyUnramified T B := Algebra.FormallyUnramified.comp T W B
  obtain ⟨_, _⟩ := exists_isDiscreteValuationRing_of_unramified T B
  have halg := isAlgebraic_of_flat_of_formallyUnramified T B
  have hff := Module.FaithfullyFlat.of_flat_of_isLocalHom (A := T) (B := B)
  letI := j.toAlgebra
  have : Module.IsTorsionFree T F := Module.isTorsionFree_iff_algebraMap_injective.2 hj
  let j' : B →ₐ[T] F := IsAlgClosed.lift
  have hj' : Function.Injective j' := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    by_contra hb0
    have hne : (RingHom.ker j').comap (algebraMap T B) ≠ ⊥ :=
      Ideal.comap_ne_bot_of_algebraic_mem hb0 hb (halg.1 b)
    refine hne (eq_bot_iff.2 fun t ht => ?_)
    have h : j' (algebraMap T B t) = 0 := ht
    rw [j'.commutes] at h
    exact hj (h.trans (map_zero j).symm)
  refine ⟨B, inferInstance, inferInstance, inferInstance, algebraMap W B, ρ', j'.toRingHom, hloc, hρ,
    hj', ?_, fun π hπ => ?_⟩
  · rw [← IsScalarTower.algebraMap_eq]
    exact j'.comp_algebraMap
  · rw [← IsScalarTower.algebraMap_apply, IsDiscreteValuationRing.irreducible_iff_uniformizer,
      ← Algebra.FormallyUnramified.map_maximalIdeal (R := T), hπ.maximalIdeal_eq, Ideal.map_span,
      Set.image_singleton]

/- English proof (translation)
Establish `hcl : spMap ρ (IsLocalRing.closedPoint Ω) = IsLocalRing.closedPoint T` using `IsLocalRing.comap_closedPoint ρ`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `S.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (f (g (IsLocalRing.closedPoint Ω)))) isOpen_univ`. Take `⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen`. Use `replace hU : IsAffineOpen U := hU`. Use `replace hV : IsAffineOpen V := hV`.

Establish `hgV : g ⁻¹ᵁ V = ⊤` using `(IsLocalRing.closed_point_mem_iff (R := Ω)).mp hxV`. Establish `hhU : h ⁻¹ᵁ U = ⊤` using `(IsLocalRing.closed_point_mem_iff (R := T)).mp (by`. Establish `: h (spMap ρ (IsLocalRing.closedPoint Ω)) ∈ U`. Establish `e : f (g (IsLocalRing.closedPoint Ω)) = h (spMap ρ (IsLocalRing.closedPoint Ω))` using `congr($w (IsLocalRing.closedPoint Ω))`. Conclude with `e ▸ hxU`.

Rewrite `this` using `[hcl]`. Conclude with `this)`. Take `⟨φ, rfl⟩` from `exists_specMap_fromSpec_eq g hV (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(hgV.ge (Set.mem_univ x) :))`.

Take `⟨α, rfl⟩` from `exists_specMap_fromSpec_eq h hU (by`. Introduce and unpack `_ ⟨x, rfl⟩`. Conclude with `(hhU.ge (Set.mem_univ x) :))`. Rewrite `w` using `[Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj]`. Establish `het` using `f.etale_appLE hU hV hVU`.

Use `algebraize [(f.appLE U V hVU).hom]`. Use `letI : Algebra Γ(S, U) T := α.hom.toAlgebra`. Use `letI : Algebra Γ(S, U) Ω := (ρ.comp α.hom).toAlgebra`. Set `ε : T ⊗[Γ(S, U)] Γ(X, V) →ₐ[Γ(S, U)] Ω` to `Algebra.TensorProduct.productMap ⟨ρ, fun _ => rfl⟩ ⟨φ.hom, fun r ↦ congr($w r)⟩`. Establish `hε₁ : ε.toRingHom.comp (algebraMap T _) = ρ`.

Use extensionality with `t`. Simplify using `[ε]`. Establish `hε₂ : ∀ a, ε (1 ⊗ₜ a) = φ.hom a` using `fun a => by simp [ε]`. Take `⟨T', _, _, _, ψ, ρ', j', h1, h2, h3, h4, h5⟩` from `exists_local_of_etale (T := T) ε.toRingHom (hε₁ ▸ hρ) j hj`. Set `χ : Γ(X, V) →+* T'` to `ψ.comp Algebra.TensorProduct.includeRight.toRingHom`.

Establish `e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom χ = α ≫ CommRingCat.ofHom (ψ.comp (algebraMap T _))`. Use extensionality with `r`. Conclude with `congrArg ψ (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := T) (B := Γ(X, V)) r).symm`. Establish `e₂ : CommRingCat.ofHom χ ≫ CommRingCat.ofHom ρ' = φ`. Use extensionality with `a`.

Conclude with `congr($h2 (1 ⊗ₜ a)).trans (hε₂ a)`. Use `⟨T', _, ‹_›, ‹_›, ψ.comp (algebraMap T _), ρ', j', h1, ?_, h3, h4, h5, Spec.map (CommRingCat.ofHom χ) ≫ hV.fromSpec, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_assoc, h2, hε₁]`. Rewrite using `[← Spec.map_comp_assoc, e₂]`. Rewrite using `[Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, e₁, Spec.map_comp_assoc]`.
-/
theorem exists_lift_one {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] {T Ω F : Type} [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [Field Ω] [Field F] [IsAlgClosed F]
    (ρ : T →+* Ω) (hρ : IsLocalHom ρ) (j : T →+* F) (hj : Function.Injective j)
    (h : Sp T ⟶ S) (g : Sp Ω ⟶ X) (w : g ≫ f = spMap ρ ≫ h) :
    ∃ (T' : Type) (_ : CommRing T') (_ : IsDomain T') (_ : IsDiscreteValuationRing T')
      (σ : T →+* T') (ρ' : T' →+* Ω) (j' : T' →+* F), IsLocalHom ρ' ∧ ρ'.comp σ = ρ ∧
      Function.Injective j' ∧ j'.comp σ = j ∧ (∀ π : T, Irreducible π → Irreducible (σ π)) ∧
      ∃ l : Sp T' ⟶ X, spMap ρ' ≫ l = g ∧ l ≫ f = spMap σ ≫ h := by
  have hcl : spMap ρ (IsLocalRing.closedPoint Ω) =
      IsLocalRing.closedPoint T := IsLocalRing.comap_closedPoint ρ
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ :=
    S.isBasis_affineOpens.exists_subset_of_mem_open
      (Set.mem_univ (f (g (IsLocalRing.closedPoint Ω)))) isOpen_univ
  obtain ⟨_, ⟨V, hV, rfl⟩, hxV, hVU : V ≤ f ⁻¹ᵁ U⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open hxU (f ⁻¹ᵁ U).isOpen
  replace hU : IsAffineOpen U := hU
  replace hV : IsAffineOpen V := hV
  have hgV : g ⁻¹ᵁ V = ⊤ := (IsLocalRing.closed_point_mem_iff (R := Ω)).mp hxV
  have hhU : h ⁻¹ᵁ U = ⊤ := (IsLocalRing.closed_point_mem_iff (R := T)).mp (by
    have : h (spMap ρ (IsLocalRing.closedPoint Ω)) ∈ U := by
      have e : f (g (IsLocalRing.closedPoint Ω)) =
          h (spMap ρ (IsLocalRing.closedPoint Ω)) :=
        congr($w (IsLocalRing.closedPoint Ω))
      exact e ▸ hxU
    rw [hcl] at this
    exact this)
  obtain ⟨φ, rfl⟩ := exists_specMap_fromSpec_eq g hV (by
    rintro _ ⟨x, rfl⟩; exact (hgV.ge (Set.mem_univ x) :))
  obtain ⟨α, rfl⟩ := exists_specMap_fromSpec_eq h hU (by
    rintro _ ⟨x, rfl⟩; exact (hhU.ge (Set.mem_univ x) :))
  rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc,
    ← Spec.map_comp_assoc, cancel_mono, Spec.map_inj] at w
  have het := f.etale_appLE hU hV hVU
  algebraize [(f.appLE U V hVU).hom]
  letI : Algebra Γ(S, U) T := α.hom.toAlgebra
  letI : Algebra Γ(S, U) Ω := (ρ.comp α.hom).toAlgebra
  let ε : T ⊗[Γ(S, U)] Γ(X, V) →ₐ[Γ(S, U)] Ω :=
    Algebra.TensorProduct.productMap ⟨ρ, fun _ => rfl⟩ ⟨φ.hom, fun r ↦ congr($w r)⟩
  have hε₁ : ε.toRingHom.comp (algebraMap T _) = ρ := by
    ext t
    simp [ε]
  have hε₂ : ∀ a, ε (1 ⊗ₜ a) = φ.hom a := fun a => by simp [ε]
  obtain ⟨T', _, _, _, ψ, ρ', j', h1, h2, h3, h4, h5⟩ :=
    exists_local_of_etale (T := T) ε.toRingHom (hε₁ ▸ hρ) j hj
  let χ : Γ(X, V) →+* T' := ψ.comp Algebra.TensorProduct.includeRight.toRingHom
  have e₁ : f.appLE U V hVU ≫ CommRingCat.ofHom χ =
      α ≫ CommRingCat.ofHom (ψ.comp (algebraMap T _)) := by
    ext r
    exact congrArg ψ (Algebra.TensorProduct.tmul_one_eq_one_tmul (A := T) (B := Γ(X, V)) r).symm
  have e₂ : CommRingCat.ofHom χ ≫ CommRingCat.ofHom ρ' = φ := by
    ext a
    exact congr($h2 (1 ⊗ₜ a)).trans (hε₂ a)
  refine ⟨T', _, ‹_›, ‹_›, ψ.comp (algebraMap T _), ρ', j', h1, ?_, h3, h4, h5,
    Spec.map (CommRingCat.ofHom χ) ≫ hV.fromSpec, ?_, ?_⟩
  · rw [← RingHom.comp_assoc, h2, hε₁]
  · rw [← Spec.map_comp_assoc, e₂]
  · rw [Category.assoc, ← hU.SpecMap_appLE_fromSpec f hV hVU, ← Spec.map_comp_assoc, e₁,
      Spec.map_comp_assoc]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨T, _, ‹_›, ‹_›, RingHom.id T, ρ, j, hρ, rfl, hj, rfl, fun _ h => h, by simp⟩`. Consider the case `insert a s _ ih`. Take `⟨T₁, _, _, _, σ₁, ρ₁, j₁, h1, h2, h3, h4, h5, h6⟩` from `ih`. Take `⟨T₂, _, _, _, σ₂, ρ₂, j₂, k1, k2, k3, k4, k5, l, k6, k7⟩` from `exists_lift_one f ρ₁ h1 j₁ h3 (spMap σ₁ ≫ h) (g a) (by rw [w, ← h2, spMap_comp', Category.assoc])`.

Use `⟨T₂, _, ‹_›, ‹_›, σ₂.comp σ₁, ρ₂, j₂, k1, by rw [← RingHom.comp_assoc, k2, h2], k3, by rw [← RingHom.comp_assoc, k4, h4], fun π hπ => k5 _ (h5 π hπ), fun i hi => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `⟨l, k6, by rw [k7, spMap_comp', Category.assoc]⟩`. Take `⟨l₁, e1, e2⟩` from `h6 i hi`. Conclude with `⟨spMap σ₂ ≫ l₁, by rw [← Category.assoc, ← spMap_comp', k2, e1], by rw [Category.assoc, e2, spMap_comp', Category.assoc]⟩`.
-/
theorem exists_lift_finset {X S : Scheme.{0}} (f : X ⟶ S) [Etale f] {T Ω F : Type} [CommRing T]
    [IsDomain T] [IsDiscreteValuationRing T] [Field Ω] [Field F] [IsAlgClosed F]
    (ρ : T →+* Ω) (hρ : IsLocalHom ρ) (j : T →+* F) (hj : Function.Injective j)
    (h : Sp T ⟶ S) {I : Type} (g : I → (Sp Ω ⟶ X)) (w : ∀ i, g i ≫ f = spMap ρ ≫ h)
    (s : Finset I) :
    ∃ (T' : Type) (_ : CommRing T') (_ : IsDomain T') (_ : IsDiscreteValuationRing T')
      (σ : T →+* T') (ρ' : T' →+* Ω) (j' : T' →+* F), IsLocalHom ρ' ∧ ρ'.comp σ = ρ ∧
      Function.Injective j' ∧ j'.comp σ = j ∧ (∀ π : T, Irreducible π → Irreducible (σ π)) ∧
      ∀ i ∈ s, ∃ l : Sp T' ⟶ X, spMap ρ' ≫ l = g i ∧ l ≫ f = spMap σ ≫ h := by
  classical
  induction s using Finset.induction_on with
  | empty => exact ⟨T, _, ‹_›, ‹_›, RingHom.id T, ρ, j, hρ, rfl, hj, rfl, fun _ h => h, by simp⟩
  | insert a s _ ih =>
    obtain ⟨T₁, _, _, _, σ₁, ρ₁, j₁, h1, h2, h3, h4, h5, h6⟩ := ih
    obtain ⟨T₂, _, _, _, σ₂, ρ₂, j₂, k1, k2, k3, k4, k5, l, k6, k7⟩ :=
      exists_lift_one f ρ₁ h1 j₁ h3 (spMap σ₁ ≫ h) (g a)
        (by rw [w, ← h2, spMap_comp', Category.assoc])
    refine ⟨T₂, _, ‹_›, ‹_›, σ₂.comp σ₁, ρ₂, j₂, k1, by rw [← RingHom.comp_assoc, k2, h2], k3,
      by rw [← RingHom.comp_assoc, k4, h4], fun π hπ => k5 _ (h5 π hπ), fun i hi => ?_⟩
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact ⟨l, k6, by rw [k7, spMap_comp', Category.assoc]⟩
    · obtain ⟨l₁, e1, e2⟩ := h6 i hi
      exact ⟨spMap σ₂ ≫ l₁, by rw [← Category.assoc, ← spMap_comp', k2, e1],
        by rw [Category.assoc, e2, spMap_comp', Category.assoc]⟩

/- English proof (translation)
Use `Fintype.ofFinite (Over.mk (spMap ρ) ⟶ X)` as an intermediate fact. Take `⟨T₁, _, _, _, σ, ρ', j', h1, h2, h3, h4, h5, h6⟩` from `exists_lift_finset X.hom ρ hρ _ hj (𝟙 _) (fun i : Over.mk (spMap ρ) ⟶ X => i.left) (fun i => (Over.w i).trans (Category.comp_id _).symm) Finset.univ`. Use `choose l hl hl' using fun i => h6 i (Finset.mem_univ i)`. Set `Φ : (Over.mk (spMap ρ) ⟶ X) → (Over.mk (spMap (algebraMap T F)) ⟶ X)` to `fun i => Over.homMk (spMap j' ≫ l i) (by show (spMap j' ≫ l i) ≫ X.hom = spMap (algebraMap T F)`. Rewrite using `[Category.assoc, hl', Category.comp_id, ← spMap_comp', h4])`.

Establish `hΦ : Function.Injective Φ` using `fun a b hab => by`. Establish `e : l a = l b` using `eq_of_preconnected_of_unramified X.hom ((hl' a).trans (hl' b).symm) (spMap j') congr(($hab).left)`. Conclude with `Over.OverMorphism.ext ((hl a).symm.trans (e ▸ hl b))`. Establish `hΦ'` using `(hΦ.bijective_of_nat_card_le hc).2`. Use `letI := σ.toAlgebra`.

Set `j₁ : T₁ →ₐ[T] F` to `⟨j', fun t => congr($h4 t)⟩`. Set `e : T₁ ≃ₐ[T] j₁.range` to `AlgEquiv.ofInjective j₁ h3`. Use `⟨j₁.range, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e, fun π hπ => ?_, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[← e.commutes]`. Conclude with `(h5 π hπ).map e`.

Take `⟨i, rfl⟩` from `hΦ' x`. Use `⟨spMap e.toRingEquiv.toRingHom ≫ l i, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← spMap_comp']`. Both sides reduce to the same expression.
-/
theorem exists_subalgebra_of_card {T Ω F : Type} [CommRing T] [IsDomain T]
    [IsDiscreteValuationRing T] [Field Ω] [Field F] [IsAlgClosed F] [Algebra T F]
    (X : Over (Sp T)) [Etale X.hom] [IsSeparated X.hom] (ρ : T →+* Ω) (hρ : IsLocalHom ρ)
    (hj : Function.Injective (algebraMap T F)) [Finite (Over.mk (spMap ρ) ⟶ X)]
    [Finite (Over.mk (spMap (algebraMap T F)) ⟶ X)]
    (hc : Nat.card (Over.mk (spMap (algebraMap T F)) ⟶ X) ≤ Nat.card (Over.mk (spMap ρ) ⟶ X)) :
    ∃ (T' : Subalgebra T F) (_ : IsDiscreteValuationRing T'),
      (∀ π : T, Irreducible π → Irreducible (algebraMap T T' π)) ∧
      ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ X,
        ∃ x' : Sp T' ⟶ X.left, spMap (T'.val.toRingHom) ≫ x' = x.left := by
  have := Fintype.ofFinite (Over.mk (spMap ρ) ⟶ X)
  obtain ⟨T₁, _, _, _, σ, ρ', j', h1, h2, h3, h4, h5, h6⟩ :=
    exists_lift_finset X.hom ρ hρ _ hj (𝟙 _) (fun i : Over.mk (spMap ρ) ⟶ X => i.left)
      (fun i => (Over.w i).trans (Category.comp_id _).symm) Finset.univ
  choose l hl hl' using fun i => h6 i (Finset.mem_univ i)
  let Φ : (Over.mk (spMap ρ) ⟶ X) → (Over.mk (spMap (algebraMap T F)) ⟶ X) := fun i =>
    Over.homMk (spMap j' ≫ l i) (by
      show (spMap j' ≫ l i) ≫ X.hom = spMap (algebraMap T F)
      rw [Category.assoc, hl', Category.comp_id, ← spMap_comp', h4])
  have hΦ : Function.Injective Φ := fun a b hab => by
    have e : l a = l b := eq_of_preconnected_of_unramified X.hom ((hl' a).trans (hl' b).symm)
      (spMap j') congr(($hab).left)
    exact Over.OverMorphism.ext ((hl a).symm.trans (e ▸ hl b))
  have hΦ' := (hΦ.bijective_of_nat_card_le hc).2
  letI := σ.toAlgebra
  let j₁ : T₁ →ₐ[T] F := ⟨j', fun t => congr($h4 t)⟩
  let e : T₁ ≃ₐ[T] j₁.range := AlgEquiv.ofInjective j₁ h3
  refine ⟨j₁.range, IsDiscreteValuationRing.RingEquivClass.isDiscreteValuationRing e,
    fun π hπ => ?_, fun x => ?_⟩
  · rw [← e.commutes]
    exact (h5 π hπ).map e
  · obtain ⟨i, rfl⟩ := hΦ' x
    refine ⟨spMap e.toRingEquiv.toRingHom ≫ l i, ?_⟩
    rw [← Category.assoc, ← spMap_comp']
    rfl

noncomputable def torsionEquiv {S : Scheme.{0}} (G : Over S) [GrpObj G] (k : ℕ) (Y : Over S) :
    (Y ⟶ torsion G k) ≃ {x : Y ⟶ G // x ^ k = 1} where
  toFun y := ⟨y ≫ torsion.ι G k, by
    rw [← MulUnramified.comp_mulN, Category.assoc]
    refine (y ≫= pullback.condition).trans ?_
    exact (Category.assoc _ _ _).symm.trans (congrArg (· ≫ η[G]) (toUnit_unique _ (toUnit Y)))⟩
  invFun x := pullback.lift x.1 (toUnit _) (by rw [MulUnramified.comp_mulN, x.2, Hom.one_def])
  left_inv y := pullback.hom_ext (pullback.lift_fst _ _ _) (toUnit_unique _ _)
  right_inv x := Subtype.ext (pullback.lift_fst _ _ _)

/- English proof (translation)
Establish `hB' : IsAbelianScheme ((Over.pullback t).obj G)` using `{ comm := by have := hG.comm; infer_instance smooth := by have := hG.smooth; show Smooth (pullback.snd _ _); infer_instance proper := (hab.ge (Set.mem_univ (t (IsLocalRing.closedPoint K)))) K t ⟨_, rfl⟩ geomConnected := by`. Use `hG.geomConnected` as an intermediate fact. Use `show GeometricallyConnected (pullback.snd _ _)`. Use `infer_instance }`. Establish `hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom` using `(smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback (IsPullback.of_hasPullback _ _) hg`.

Take `⟨e, -⟩` from `exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G t) (𝟙 _) t (Category.id_comp t).symm`. Rewrite using `[Nat.card_congr (torsionEquiv G n _), ← GlobalTheory.T.card_torsion_points_abelianVariety hL.globalFns hL.rigidity K ((Over.pullback t).obj G) g n hB' hg' hn]`. Use `(Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm` and prove the remaining obligations. Use `show x ^ n = 1 ↔ e x ^ n = 1`. Rewrite using `[← map_pow, MulEquiv.map_eq_one_iff]`.
-/
theorem card_torsion (hL : Laws) {S : Scheme.{0}} (G : Over S) [GrpObj G] (hG : IsSemiAbelian G)
    (hab : abLocus G = Set.univ) {g : ℕ} (hg : SmoothOfRelativeDimension g G.hom) {K : Type}
    [Field K] [IsAlgClosed K] (t : Sp K ⟶ S) {n : ℕ} (hn : (n : K) ≠ 0) :
    Nat.card (Over.mk t ⟶ torsion G n) = n ^ (2 * g) := by
  have hB' : IsAbelianScheme ((Over.pullback t).obj G) :=
    { comm := by have := hG.comm; infer_instance
      smooth := by have := hG.smooth; show Smooth (pullback.snd _ _); infer_instance
      proper := (hab.ge (Set.mem_univ (t (IsLocalRing.closedPoint K)))) K t ⟨_, rfl⟩
      geomConnected := by
        have := hG.geomConnected; show GeometricallyConnected (pullback.snd _ _); infer_instance }
  have hg' : SmoothOfRelativeDimension g ((Over.pullback t).obj G).hom :=
    (smoothOfRelativeDimension_isStableUnderBaseChange _).of_isPullback
      (IsPullback.of_hasPullback _ _) hg
  obtain ⟨e, -⟩ := exists_mulEquiv_of_isGrpPullback (isGrpPullback_pullback G t) (𝟙 _) t
    (Category.id_comp t).symm
  rw [Nat.card_congr (torsionEquiv G n _),
    ← GlobalTheory.T.card_torsion_points_abelianVariety hL.globalFns hL.rigidity K ((Over.pullback t).obj G) g n hB' hg' hn]
  refine (Nat.card_congr (e.toEquiv.subtypeEquiv fun x => ?_)).symm
  show x ^ n = 1 ↔ e x ^ n = 1
  rw [← map_pow, MulEquiv.map_eq_one_iff]

end GlobalTheory.TorsionUnram

namespace GlobalTheory

open TorsionUnram in

/- English proof (translation)
Introduce `hL _ T _ _ _ G _ _ hG hab F _ _ _ hj k hk`. Use `hG.smooth` as an intermediate fact. Use `hG.separated` as an intermediate fact. Use `hG.geomConnected` as an intermediate fact. Establish `: ConnectedSpace G.left` using `GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap`.

Take `⟨x₀⟩ : Nonempty G.left` from `inferInstance`. Take `⟨g, hg⟩` from `exists_dim_of_preconnected G.hom x₀`. Establish `het` using `(etale_mulN_torsion_dvr T G k hk inferInstance inferInstance).2`. Establish `hm : IsSeparated ((mulN G k).left ≫ G.hom)` using `by rw [Over.w]; infer_instance`. Establish `hm' : IsSeparated (mulN G k).left` using `IsSeparated.of_comp _ G.hom`.

Establish `hsep : IsSeparated (torsion G k).hom` using `MorphismProperty.of_isPullback (P := @IsSeparated) (MulEtaleDvr.isPullback_torsion G k) hm'`. Set `Ω` to `AlgebraicClosure (IsLocalRing.ResidueField T)`. Set `ρ : T →+* Ω` to `(algebraMap (IsLocalRing.ResidueField T) Ω).comp (IsLocalRing.residue T)`. Establish `hρ : IsLocalHom ρ` using `inferInstance`. Establish `hkΩ : (k : Ω) ≠ 0` using `by simpa using (hk.map ρ).ne_zero`.

Establish `hkF : (k : F) ≠ 0` using `by simpa using (hk.map (algebraMap T F)).ne_zero`. Establish `hk0 : k ^ (2 * g) ≠ 0` using `pow_ne_zero _ (by rintro rfl; simp at hkF)`. Establish `c₁` using `card_torsion hL G hG hab hg (spMap ρ) hkΩ`. Establish `c₂` using `card_torsion hL G hG hab hg (spMap (algebraMap T F)) hkF`. Use `Nat.finite_of_card_ne_zero (c₁ ▸ hk0)` as an intermediate fact.

Use `Nat.finite_of_card_ne_zero (c₂ ▸ hk0)` as an intermediate fact. Take `⟨T', hT', h₁, h₂⟩` from `exists_subalgebra_of_card (torsion G k) ρ hρ hj (c₂.trans c₁.symm).le`. Use `⟨T', hT', h₁, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨y, hy⟩` from `(torsionEquiv G k _).surjective ⟨x, hx⟩`. Take `⟨x', hx'⟩` from `h₂ y`.

Use `⟨x' ≫ (torsion.ι G k).left, ?_⟩` and prove the remaining obligations. Rewrite using `[← Category.assoc, hx']`. Conclude with `congr(($hy).1.left)`.
-/
theorem exists_unramified_torsion_points : Laws → Laws2 → ∀ (T : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] (G : Over (Sp T)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → abLocus G = Set.univ → ∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra T F], Function.Injective (algebraMap T F) → ∀ k : ℕ, IsUnit (k : T) → ∃ (T' : Subalgebra T F) (_ : IsDiscreteValuationRing T'), (∀ π : T, Irreducible π → Irreducible (algebraMap T T' π)) ∧ ∀ x : Over.mk (spMap (algebraMap T F)) ⟶ G, x ^ k = 1 → ∃ x' : Sp T' ⟶ G.left, spMap (T'.val.toRingHom) ≫ x' = x.left := by
  intro hL _ T _ _ _ G _ _ hG hab F _ _ _ hj k hk
  have := hG.smooth
  have := hG.separated
  have := hG.geomConnected
  have : ConnectedSpace G.left := GeometricallyConnected.connectedSpace G.hom G.hom.isOpenMap
  obtain ⟨x₀⟩ : Nonempty G.left := inferInstance
  obtain ⟨g, hg⟩ := exists_dim_of_preconnected G.hom x₀
  have het := (etale_mulN_torsion_dvr T G k hk inferInstance inferInstance).2
  have hm : IsSeparated ((mulN G k).left ≫ G.hom) := by rw [Over.w]; infer_instance
  have hm' : IsSeparated (mulN G k).left := IsSeparated.of_comp _ G.hom
  have hsep : IsSeparated (torsion G k).hom :=
    MorphismProperty.of_isPullback (P := @IsSeparated) (MulEtaleDvr.isPullback_torsion G k) hm'
  let Ω := AlgebraicClosure (IsLocalRing.ResidueField T)
  let ρ : T →+* Ω := (algebraMap (IsLocalRing.ResidueField T) Ω).comp (IsLocalRing.residue T)
  have hρ : IsLocalHom ρ := inferInstance
  have hkΩ : (k : Ω) ≠ 0 := by simpa using (hk.map ρ).ne_zero
  have hkF : (k : F) ≠ 0 := by simpa using (hk.map (algebraMap T F)).ne_zero
  have hk0 : k ^ (2 * g) ≠ 0 := pow_ne_zero _ (by rintro rfl; simp at hkF)
  have c₁ := card_torsion hL G hG hab hg (spMap ρ) hkΩ
  have c₂ := card_torsion hL G hG hab hg (spMap (algebraMap T F)) hkF
  have := Nat.finite_of_card_ne_zero (c₁ ▸ hk0)
  have := Nat.finite_of_card_ne_zero (c₂ ▸ hk0)
  obtain ⟨T', hT', h₁, h₂⟩ := exists_subalgebra_of_card (torsion G k) ρ hρ hj (c₂.trans c₁.symm).le
  refine ⟨T', hT', h₁, fun x hx => ?_⟩
  obtain ⟨y, hy⟩ := (torsionEquiv G k _).surjective ⟨x, hx⟩
  obtain ⟨x', hx'⟩ := h₂ y
  refine ⟨x' ≫ (torsion.ι G k).left, ?_⟩
  rw [← Category.assoc, hx']
  exact congr(($hy).1.left)

end GlobalTheory
