import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsIsCan
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ExistsFactorThroughProjection
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
open GlobalTheory.ThetaTrace GlobalTheory.HkFam GlobalTheory.Frames GlobalTheory.HeckeEx
open GlobalTheory.IndefiniteRowSideFullHecke.FibrePushforwardExistenceTori (IsLinHom IsLieImg IsThGen IsHeckeIsog)

namespace GlobalTheory.SmoothLocalDescent

/- English proof (translation)
Rewrite using `[← sub_eq_zero]`. Apply `IsNilpotent.eq_zero` to reduce the goal to its premises. Rewrite using `[nilpotent_iff_mem_prime]`. Introduce `J hJ`. Use `h (AlgebraicClosure J.ResidueField) ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))` as an intermediate fact.

Rewrite `this` using `[← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero, Ideal.algebraMap_residueField_eq_zero]`. Conclude with `this`.
-/
theorem eq_of_forall_geom {R : Type} [CommRing R] [_root_.IsReduced R] (a b : R)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ : R →+* k), χ a = χ b) : a = b := by
  rw [← sub_eq_zero]
  apply IsNilpotent.eq_zero
  rw [nilpotent_iff_mem_prime]
  intro J hJ
  have := h (AlgebraicClosure J.ResidueField)
    ((algebraMap J.ResidueField _).comp (algebraMap R J.ResidueField))
  rw [← sub_eq_zero, ← map_sub, RingHom.comp_apply, map_eq_zero,
    Ideal.algebraMap_residueField_eq_zero] at this
  exact this

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection`. Consider the case `exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection`. Consider the case `(apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection ..)`.
-/
theorem exists_factor_pi {J : Type} [Fintype J] [DecidableEq J] (A : J → Type)
    [∀ i, CommRing (A i)] {k : Type} [CommRing k] [IsDomain k] (χ : (∀ i, A i) →+* k) :
    ∃ (i : J) (ψ : A i →+* k), ∀ x, χ x = ψ (x i) := by
  first
  | exact @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection
  | (apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> assumption)
  | (intros; apply @_root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.FactorThroughProjection.exists_factor_through_projection ..)

open scoped TensorProduct in

/- English proof (translation)
Use `letI : Algebra R k := χ.toAlgebra`. Use `haveI : Nontrivial (k ⊗[R] S) := inferInstance`. Take `⟨m, hm⟩` from `Ideal.exists_maximal (k ⊗[R] S)`. Use `letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Algebra.FiniteType k (k ⊗[R] S) := inferInstance`.

Use `haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _`. Set `g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k` to `IsAlgClosed.lift`. Use `⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x)`.

Rewrite using `[Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x`. Rewrite using `[e]`. Conclude with `g.commutes (χ x)`.
-/
theorem exists_lift_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [Algebra.FiniteType R S] [Module.FaithfullyFlat R S] (k : Type) [Field k] [IsAlgClosed k]
    (χ : R →+* k) : ∃ χ' : S →+* k, χ'.comp (algebraMap R S) = χ := by
  letI : Algebra R k := χ.toAlgebra
  haveI : Nontrivial (k ⊗[R] S) := inferInstance
  obtain ⟨m, hm⟩ := Ideal.exists_maximal (k ⊗[R] S)
  letI : Field ((k ⊗[R] S) ⧸ m) := Ideal.Quotient.field m
  haveI : Algebra.FiniteType k (k ⊗[R] S) := inferInstance
  haveI : Module.Finite k ((k ⊗[R] S) ⧸ m) := finite_of_finite_type_of_isJacobsonRing k _
  let g : ((k ⊗[R] S) ⧸ m) →ₐ[k] k := IsAlgClosed.lift
  refine ⟨g.toRingHom.comp ((Ideal.Quotient.mk m).comp
    (Algebra.TensorProduct.includeRight (R := R) (A := k) (B := S)).toRingHom), ?_⟩
  ext x
  have e : (1 : k) ⊗ₜ[R] algebraMap R S x = algebraMap k (k ⊗[R] S) (χ x) := by
    rw [Algebra.algebraMap_eq_smul_one, ← TensorProduct.smul_tmul, Algebra.smul_def, _root_.mul_one]
    rfl
  change g (Ideal.Quotient.mk m ((1 : k) ⊗ₜ[R] algebraMap R S x)) = χ x
  rw [e]
  exact g.commutes (χ x)

open scoped TensorProduct in

/- English proof (translation)
Use `haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R S`. Use `haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced S (S ⊗[R] S)`. Establish `key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w`. Use `eq_of_forall_geom _ _ fun k _ _ χ => ?_` and prove the remaining obligations. Use `h k (χ.comp Algebra.TensorProduct.includeLeftRingHom) (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_` and prove the remaining obligations.

Use extensionality with `x`. Express the relevant statement in the definitionally equal form `χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)`. Rewrite using `[Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`. Conclude with `(Algebra.IsEffective.of_faithfullyFlat R S w).1 (by`. Rewrite using `[Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])`.
-/
theorem exists_preimage_of_geom (R S : Type) [CommRing R] [CommRing S] [Algebra R S]
    [_root_.IsReduced R] [Algebra.Smooth R S] [Module.FaithfullyFlat R S] (w : S)
    (h : ∀ (k : Type) [Field k] [IsAlgClosed k] (χ₁ χ₂ : S →+* k),
      χ₁.comp (algebraMap R S) = χ₂.comp (algebraMap R S) → χ₁ w = χ₂ w) :
    ∃ u : R, algebraMap R S u = w := by
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced R S
  haveI := GlobalTheory.isReduced_algebra_of_smooth_of_isReduced S (S ⊗[R] S)
  have key : w ⊗ₜ[R] (1 : S) = (1 : S) ⊗ₜ[R] w := by
    refine eq_of_forall_geom _ _ fun k _ _ χ => ?_
    refine h k (χ.comp Algebra.TensorProduct.includeLeftRingHom)
      (χ.comp (Algebra.TensorProduct.includeRight (R := R) (A := S) (B := S)).toRingHom) ?_
    ext x
    change χ (algebraMap R S x ⊗ₜ[R] (1 : S)) = χ ((1 : S) ⊗ₜ[R] algebraMap R S x)
    rw [Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  exact (Algebra.IsEffective.of_faithfullyFlat R S w).1 (by
    rw [Algebra.TensorProduct.includeLeftSubRight_apply, key, sub_self])

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

/- English proof (translation)
Use `haveI : Algebra.Smooth B (∀ i, A i) := ⟨inferInstance, inferInstance⟩`. Use `haveI : Module.Flat B (∀ i, A i) := inferInstance`. Use `haveI : Module.FaithfullyFlat B (∀ i, A i) := by`. Use `Module.FaithfullyFlat.of_comap_surjective fun p => ?_` and prove the remaining obligations. Take `⟨i, Q, hQ⟩` from `hcov p`.

Use `⟨PrimeSpectrum.comap (Pi.evalRingHom A i) Q, ?_⟩` and prove the remaining obligations. Rewrite using `[← hQ]`. Both sides reduce to the same expression. Establish `key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : (∀ i, A i) →+* Ω), (∀ x : K, χ' (algebraMap B (∀ i, A i) (algebraMap K B x)) = algebraMap K Ω x) → ∃ ρ : B →ₐ[K] Ω, (∀ y, ρ y = χ' (algebraMap B (∀ i, A i) y)) ∧ χ' a = F Ω ρ`. Introduce `Ω _ _ _ χ' hK`.

Take `⟨i, ψ, hψ⟩` from `exists_factor_pi A χ'`. Establish `hB : ∀ y, ψ (algebraMap B (A i) y) = χ' (algebraMap B (∀ i, A i) y)` using `fun y => by`. Rewrite using `[hψ]`. Both sides reduce to the same expression. Establish `hc : ∀ x : K, ψ (algebraMap K (A i) x) = algebraMap K Ω x` using `fun x => by`.

Rewrite using `[IsScalarTower.algebraMap_apply K B (A i), hB, hK]`. Set `ψa : A i →ₐ[K] Ω` to `{ ψ with commutes' := hc }`. Use `⟨ψa.comp (IsScalarTower.toAlgHom K B (A i)), fun y => hB y, ?_⟩` and prove the remaining obligations. Rewrite using `[hψ]`. Conclude with `hval i Ω ψa`.

Take `⟨b, hb⟩` from `exists_preimage_of_geom B (∀ i, A i) a fun k _ _ χ₁ χ₂ h12 => by`. Use `letI : Algebra K k := (χ₁.comp ((algebraMap B (∀ i, A i)).comp (algebraMap K B))).toAlgebra`. Establish `h12' : ∀ y, χ₁ (algebraMap B (∀ i, A i) y) = χ₂ (algebraMap B (∀ i, A i) y)` using `fun y => RingHom.congr_fun h12 y`. Take `⟨ρ₁, hρ₁, e₁⟩` from `key k χ₁ fun x => rfl`. Take `⟨ρ₂, hρ₂, e₂⟩` from `key k χ₂ fun x => (h12' _).symm`.

Establish `: ρ₁ = ρ₂` using `AlgHom.ext fun y => by rw [hρ₁, hρ₂, h12']`. Rewrite using `[e₁, e₂, this]`. Use `⟨b, fun Ω _ _ _ χ => ?_⟩` and prove the remaining obligations. Take `⟨χ', hχ'⟩` from `exists_lift_geom B (∀ i, A i) Ω χ.toRingHom`. Establish `hχ'y : ∀ y, χ' (algebraMap B (∀ i, A i) y) = χ y` using `fun y => RingHom.congr_fun hχ' y`.

Take `⟨ρ, hρ, e⟩` from `key Ω χ' fun x => by rw [hχ'y]; exact χ.commutes x`. Establish `: ρ = χ` using `AlgHom.ext fun y => by rw [hρ, hχ'y]`. Rewrite using `[← this, ← e, ← hb, hρ]`.
-/
theorem exists_of_finite_cover (K B : Type) [CommRing K] [CommRing B] [Algebra K B]
    [_root_.IsReduced B]
    (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω)
    {J : Type} [Fintype J] [DecidableEq J] (A : J → Type) [∀ i, CommRing (A i)]
    [∀ i, Algebra B (A i)] [∀ i, Algebra K (A i)] [∀ i, IsScalarTower K B (A i)]
    [∀ i, Algebra.Smooth B (A i)] (a : ∀ i, A i)
    (hcov : ∀ q : PrimeSpectrum B, ∃ i, q ∈ Set.range (PrimeSpectrum.comap (algebraMap B (A i))))
    (hval : ∀ i (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : A i →ₐ[K] Ω),
      χ' (a i) = F Ω (χ'.comp (IsScalarTower.toAlgHom K B (A i)))) :
    ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  haveI : Algebra.Smooth B (∀ i, A i) := ⟨inferInstance, inferInstance⟩
  haveI : Module.Flat B (∀ i, A i) := inferInstance
  haveI : Module.FaithfullyFlat B (∀ i, A i) := by
    refine Module.FaithfullyFlat.of_comap_surjective fun p => ?_
    obtain ⟨i, Q, hQ⟩ := hcov p
    refine ⟨PrimeSpectrum.comap (Pi.evalRingHom A i) Q, ?_⟩
    rw [← hQ]
    rfl

  have key : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : (∀ i, A i) →+* Ω),
      (∀ x : K, χ' (algebraMap B (∀ i, A i) (algebraMap K B x)) = algebraMap K Ω x) →
      ∃ ρ : B →ₐ[K] Ω, (∀ y, ρ y = χ' (algebraMap B (∀ i, A i) y)) ∧ χ' a = F Ω ρ := by
    intro Ω _ _ _ χ' hK
    obtain ⟨i, ψ, hψ⟩ := exists_factor_pi A χ'
    have hB : ∀ y, ψ (algebraMap B (A i) y) = χ' (algebraMap B (∀ i, A i) y) := fun y => by
      rw [hψ]; rfl
    have hc : ∀ x : K, ψ (algebraMap K (A i) x) = algebraMap K Ω x := fun x => by
      rw [IsScalarTower.algebraMap_apply K B (A i), hB, hK]
    let ψa : A i →ₐ[K] Ω := { ψ with commutes' := hc }
    refine ⟨ψa.comp (IsScalarTower.toAlgHom K B (A i)), fun y => hB y, ?_⟩
    rw [hψ]
    exact hval i Ω ψa
  obtain ⟨b, hb⟩ := exists_preimage_of_geom B (∀ i, A i) a fun k _ _ χ₁ χ₂ h12 => by
    letI : Algebra K k := (χ₁.comp ((algebraMap B (∀ i, A i)).comp (algebraMap K B))).toAlgebra
    have h12' : ∀ y, χ₁ (algebraMap B (∀ i, A i) y) = χ₂ (algebraMap B (∀ i, A i) y) :=
      fun y => RingHom.congr_fun h12 y
    obtain ⟨ρ₁, hρ₁, e₁⟩ := key k χ₁ fun x => rfl
    obtain ⟨ρ₂, hρ₂, e₂⟩ := key k χ₂ fun x => (h12' _).symm
    have : ρ₁ = ρ₂ := AlgHom.ext fun y => by rw [hρ₁, hρ₂, h12']
    rw [e₁, e₂, this]
  refine ⟨b, fun Ω _ _ _ χ => ?_⟩
  obtain ⟨χ', hχ'⟩ := exists_lift_geom B (∀ i, A i) Ω χ.toRingHom
  have hχ'y : ∀ y, χ' (algebraMap B (∀ i, A i) y) = χ y := fun y => RingHom.congr_fun hχ' y
  obtain ⟨ρ, hρ, e⟩ := key Ω χ' fun x => by rw [hχ'y]; exact χ.commutes x
  have : ρ = χ := AlgHom.ext fun y => by rw [hρ, hχ'y]
  rw [← this, ← e, ← hb, hρ]

end GlobalTheory.SmoothLocalDescent

namespace GlobalTheory.SmoothLocalDescent

/- English proof (translation)
Introduce `K B _ _ _ _ F h`. Use `choose B' iR iB iK iT b' hsm hq hval using h`. Use `letI : ∀ q, CommRing (B' q) := iR`. Use `letI : ∀ q, Algebra B (B' q) := iB`. Use `letI : ∀ q, Algebra K (B' q) := iK`.

Use `haveI : ∀ q, IsScalarTower K B (B' q) := iT`. Use `haveI : ∀ q, Algebra.Smooth B (B' q) := hsm`. Set `U : PrimeSpectrum B → Set (PrimeSpectrum B)` to `fun q => Set.range (PrimeSpectrum.comap (algebraMap B (B' q)))`. Establish `hopen : ∀ q, IsOpen (U q)` using `fun q => by`. Use `PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation (R := B) (S := B' q) _ isOpen_univ` as an intermediate fact.

Rewrite `this` using `[Set.image_univ]`. Then use the resulting hypothesis. Take `⟨t, ht⟩` from `isCompact_univ.elim_finite_subcover U hopen (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)`. Conclude with `exists_of_finite_cover K B F (J := t) (fun i => B' i.1) (fun i => b' i.1) (fun q => by`. Take `⟨i, hi, hqi⟩` from `Set.mem_iUnion₂.1 (ht (Set.mem_univ q))`. Conclude with `⟨⟨i, hi⟩, hqi⟩)`.

Use the proof step `(fun i => hval i.1)`.
-/
theorem exists_of_smooth_locally : ∀ (K B : Type) [CommRing K] [CommRing B] [Algebra K B] [IsReduced B] (F : ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω], (B →ₐ[K] Ω) → Ω), (∀ q : PrimeSpectrum B, ∃ (B' : Type) (_ : CommRing B') (_ : Algebra B B') (_ : Algebra K B') (_ : IsScalarTower K B B') (b' : B'), Algebra.Smooth B B' ∧ q ∈ Set.range (PrimeSpectrum.comap (algebraMap B B')) ∧ ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ' : B' →ₐ[K] Ω), χ' b' = F Ω (χ'.comp (IsScalarTower.toAlgHom K B B'))) → ∃ b : B, ∀ (Ω : Type) [Field Ω] [IsAlgClosed Ω] [Algebra K Ω] (χ : B →ₐ[K] Ω), χ b = F Ω χ := by
  intro K B _ _ _ _ F h
  choose B' iR iB iK iT b' hsm hq hval using h
  letI : ∀ q, CommRing (B' q) := iR
  letI : ∀ q, Algebra B (B' q) := iB
  letI : ∀ q, Algebra K (B' q) := iK
  haveI : ∀ q, IsScalarTower K B (B' q) := iT
  haveI : ∀ q, Algebra.Smooth B (B' q) := hsm
  let U : PrimeSpectrum B → Set (PrimeSpectrum B) := fun q =>
    Set.range (PrimeSpectrum.comap (algebraMap B (B' q)))
  have hopen : ∀ q, IsOpen (U q) := fun q => by
    have := PrimeSpectrum.isOpenMap_comap_of_hasGoingDown_of_finitePresentation
      (R := B) (S := B' q) _ isOpen_univ
    rwa [Set.image_univ] at this
  obtain ⟨t, ht⟩ := isCompact_univ.elim_finite_subcover U hopen
    (fun q _ => Set.mem_iUnion.2 ⟨q, hq q⟩)
  classical
  exact exists_of_finite_cover K B F (J := t) (fun i => B' i.1) (fun i => b' i.1)
    (fun q => by
      obtain ⟨i, hi, hqi⟩ := Set.mem_iUnion₂.1 (ht (Set.mem_univ q))
      exact ⟨⟨i, hi⟩, hqi⟩)
    (fun i => hval i.1)

end GlobalTheory.SmoothLocalDescent
