import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods

namespace GlobalTheory

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Establish `: Module.Finite F (A ⧸ m)` using `finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)`. Use `⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L).comp (Ideal.Quotient.mkₐ F m), fun x => ?_⟩` and prove the remaining obligations. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m x)).algHom (IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L)`.
-/
theorem exists_algHom_isAlgebraic_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L] [Algebra F L] :
    ∃ φ : A →ₐ[F] L, ∀ x, IsAlgebraic F (φ x) := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  have : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  refine ⟨(IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L).comp (Ideal.Quotient.mkₐ F m), fun x => ?_⟩
  exact (Algebra.IsAlgebraic.isAlgebraic (R := F) (Ideal.Quotient.mkₐ F m x)).algHom
    (IsAlgClosed.lift : (A ⧸ m) →ₐ[F] L)

/- English proof (translation)
Take `⟨m, hm⟩` from `Ideal.exists_maximal A`. Use `letI : Field (A ⧸ m) := Ideal.Quotient.field m`. Use `haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)`. Use `letI : Algebra F L := σ.toAlgebra`. Set `ψ : (A ⧸ m) →ₐ[F] L` to `IsAlgClosed.lift`.

Use `⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), fun x => ?_⟩` and prove the remaining obligations. Establish `h1 : Ideal.Quotient.mk m (algebraMap F A x) = algebraMap F (A ⧸ m) x` using `rfl`. Simplify using `only [RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.exists_ringHom_extend_of_finiteType (F A L : Type*) [Field F] [CommRing A]
    [Nontrivial A] [Algebra F A] [Algebra.FiniteType F A] [Field L] [IsAlgClosed L]
    (σ : F →+* L) : ∃ φ : A →+* L, ∀ x, φ (algebraMap F A x) = σ x := by
  obtain ⟨m, hm⟩ := Ideal.exists_maximal A
  letI : Field (A ⧸ m) := Ideal.Quotient.field m
  haveI : Module.Finite F (A ⧸ m) := finite_of_finite_type_of_isJacobsonRing F (A ⧸ m)
  letI : Algebra F L := σ.toAlgebra
  let ψ : (A ⧸ m) →ₐ[F] L := IsAlgClosed.lift
  refine ⟨ψ.toRingHom.comp (Ideal.Quotient.mk m), fun x => ?_⟩
  have h1 : Ideal.Quotient.mk m (algebraMap F A x) = algebraMap F (A ⧸ m) x := rfl
  simp only [RingHom.comp_apply, h1, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, AlgHom.commutes]
  rfl

/- English proof (translation)
Take `⟨s, rfl⟩` from `hR`. Use `⟨Algebra.adjoin F (↑(insert u s) : Set L), ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩`. Use `Algebra.adjoin_le fun x hx => ?_` and prove the remaining obligations. Establish `: x ∈ Algebra.adjoin F (↑(insert u s) : Set L)` using `Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))`.

Conclude with `this`. Conclude with `Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_self _ _))`.
-/
theorem exists_fg_subalgebra_over {k L : Type*} [Field k] [Field L] [Algebra k L]
    (F : IntermediateField k L) (R : Subalgebra k L) (hR : R.FG) (u : L) :
    ∃ A : Subalgebra F L, Algebra.FiniteType F A ∧ R ≤ A.restrictScalars k ∧ u ∈ A := by
  classical
  obtain ⟨s, rfl⟩ := hR
  refine ⟨Algebra.adjoin F (↑(insert u s) : Set L), ?_, ?_, ?_⟩
  · exact (Subalgebra.fg_iff_finiteType _).1 ⟨_, rfl⟩
  · refine Algebra.adjoin_le fun x hx => ?_
    have : x ∈ Algebra.adjoin F (↑(insert u s) : Set L) :=
      Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_of_mem (Finset.mem_coe.1 hx)))
    exact this
  · exact Algebra.subset_adjoin (Finset.mem_coe.2 (Finset.mem_insert_self _ _))

/- English proof (translation)
Take `⟨s, hs⟩` from `hR`. Establish `hrL : (r : L) ≠ 0` using `fun h => hr (Subtype.ext h)`. Take `⟨A, hA⟩ : ∃ A : Subalgebra F L, A = Algebra.adjoin F ↑(insert ((r : L)⁻¹) s)` from `⟨_, rfl⟩`. Use `haveI : Algebra.FiniteType F A := (Subalgebra.fg_iff_finiteType A).1 ⟨insert ((r : L)⁻¹) s, hA.symm⟩`. Take `⟨φ, hφ⟩` from `_root_.GlobalTheory.exists_ringHom_extend_of_finiteType F A M σ.toRingHom`.

Establish `hgen : ∀ y ∈ insert ((r : L)⁻¹) s, y ∈ A` using `fun y hy => by`. Rewrite using `[hA]`. Conclude with `Algebra.subset_adjoin (Finset.mem_coe.2 hy)`. Establish `hle : ∀ x ∈ R, x ∈ A`. Introduce `x hx`.

Rewrite `hx` using `[← hs]`. Establish `hsub : Algebra.adjoin k (s : Set L) ≤ A.restrictScalars k` using `Algebra.adjoin_le fun y hy => (Subalgebra.mem_restrictScalars k).2 (hgen y (Finset.mem_insert_of_mem (Finset.mem_coe.1 hy)))`. Conclude with `(Subalgebra.mem_restrictScalars k).1 (hsub hx)`. Set `ι : R →+* A` to `{ toFun := fun x => ⟨x, hle x x.2⟩ map_one' := Subtype.ext (by simp) map_mul' := fun _ _ => Subtype.ext (by simp) map_zero' := Subtype.ext (by simp) map_add' := fun _ _ => Subtype.ext (by simp) }`. Establish `hι : ∀ (x : R) (hx : (x : L) ∈ F), ι x = algebraMap F A ⟨x, hx⟩` using `fun _ _ => Subtype.ext rfl`.

Establish `hcomm : ∀ a : k, φ (ι (algebraMap k R a)) = algebraMap k M a`. Introduce `a`. Establish `h1 : ι (algebraMap k R a) = algebraMap F A (algebraMap k F a)` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `algebraMap k L a = algebraMap F L (algebraMap k F a)`. Conclude with `IsScalarTower.algebraMap_apply k F L a)`.

Rewrite using `[h1, hφ]`. Conclude with `σ.commutes a`. Use `⟨{ toRingHom := φ.comp ι, commutes' := hcomm }, fun x hx => ?_, ?_⟩` and prove the remaining obligations. Use `show φ (ι x) = σ ⟨x, hx⟩`. Rewrite using `[hι x hx, hφ]`.

Both sides reduce to the same expression. Establish `hinv : ι r * ⟨(r : L)⁻¹, hgen _ (Finset.mem_insert_self _ _)⟩ = 1` using `Subtype.ext (by simp [ι, hrL])`. Use `congrArg φ hinv` as an intermediate fact. Rewrite `this` using `[map_mul, map_one]`. Conclude with `left_ne_zero_of_mul_eq_one this`.
-/
private lemma exists_algHom_extend_of_fg_ne_zero {k L M : Type*} [Field k] [Field L] [Algebra k L]
    [Field M] [IsAlgClosed M] [Algebra k M] (F : IntermediateField k L) (σ : F →ₐ[k] M)
    (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ ρ : R →ₐ[k] M, (∀ (x : R) (hx : (x : L) ∈ F), ρ x = σ ⟨x, hx⟩) ∧ ρ r ≠ 0 := by
  classical
  obtain ⟨s, hs⟩ := hR
  have hrL : (r : L) ≠ 0 := fun h => hr (Subtype.ext h)
  obtain ⟨A, hA⟩ : ∃ A : Subalgebra F L, A = Algebra.adjoin F ↑(insert ((r : L)⁻¹) s) := ⟨_, rfl⟩
  haveI : Algebra.FiniteType F A :=
    (Subalgebra.fg_iff_finiteType A).1 ⟨insert ((r : L)⁻¹) s, hA.symm⟩
  obtain ⟨φ, hφ⟩ := _root_.GlobalTheory.exists_ringHom_extend_of_finiteType F A M σ.toRingHom
  have hgen : ∀ y ∈ insert ((r : L)⁻¹) s, y ∈ A := fun y hy => by
    rw [hA]; exact Algebra.subset_adjoin (Finset.mem_coe.2 hy)
  have hle : ∀ x ∈ R, x ∈ A := by
    intro x hx
    rw [← hs] at hx
    have hsub : Algebra.adjoin k (s : Set L) ≤ A.restrictScalars k :=
      Algebra.adjoin_le fun y hy => (Subalgebra.mem_restrictScalars k).2
        (hgen y (Finset.mem_insert_of_mem (Finset.mem_coe.1 hy)))
    exact (Subalgebra.mem_restrictScalars k).1 (hsub hx)
  let ι : R →+* A :=
    { toFun := fun x => ⟨x, hle x x.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun _ _ => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun _ _ => Subtype.ext (by simp) }
  have hι : ∀ (x : R) (hx : (x : L) ∈ F), ι x = algebraMap F A ⟨x, hx⟩ :=
    fun _ _ => Subtype.ext rfl
  have hcomm : ∀ a : k, φ (ι (algebraMap k R a)) = algebraMap k M a := by
    intro a
    have h1 : ι (algebraMap k R a) = algebraMap F A (algebraMap k F a) := Subtype.ext (by
      change algebraMap k L a = algebraMap F L (algebraMap k F a)
      exact IsScalarTower.algebraMap_apply k F L a)
    rw [h1, hφ]
    exact σ.commutes a
  refine ⟨{ toRingHom := φ.comp ι, commutes' := hcomm }, fun x hx => ?_, ?_⟩
  · show φ (ι x) = σ ⟨x, hx⟩
    rw [hι x hx, hφ]
    rfl
  · have hinv : ι r * ⟨(r : L)⁻¹, hgen _ (Finset.mem_insert_self _ _)⟩ = 1 :=
      Subtype.ext (by simp [ι, hrL])
    have := congrArg φ hinv
    rw [map_mul, map_one] at this
    exact left_ne_zero_of_mul_eq_one this

/- English proof (translation)
Use `haveI : IsAlgClosed (algebraicClosure k L) := IsAlgClosure.isAlgClosed k`. Take `⟨ρ₁, hfix, hr₁⟩` from `exists_algHom_extend_of_fg_ne_zero (algebraicClosure k L) (AlgHom.id k _) R hR r hr`. Set `ρ₀ : R →ₐ[k] L` to `(algebraicClosure k L).val.comp ρ₁`. Establish `halg : ∀ x : R, IsAlgebraic k (ρ₀ x)` using `fun x => mem_algebraicClosure_iff.1 (ρ₁ x).2`. Use `haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR`.

Take `⟨t, ht⟩` from `Algebra.FiniteType.out (R := k) (A := R)`. Use `haveI : Finite (ρ₀ '' (t : Set R)) := (t.finite_toSet.image _).to_subtype`. Establish `hfin : FiniteDimensional k (IntermediateField.adjoin k (ρ₀ '' (t : Set R)))` using `IntermediateField.finiteDimensional_adjoin fun y hy => by`. Take `⟨x, -, rfl⟩` from `hy`. Conclude with `(halg x).isIntegral`.

Establish `hmem : ∀ x : R, ρ₀ x ∈ IntermediateField.adjoin k (ρ₀ '' (t : Set R))`. Introduce `x`. Establish `hx : x ∈ Algebra.adjoin k (t : Set R)` using `by rw [ht]; exact Algebra.mem_top`. Establish `h1 : ρ₀ x ∈ Algebra.adjoin k (ρ₀ '' (t : Set R))`. Rewrite using `[← AlgHom.map_adjoin]`.

Conclude with `⟨x, hx, rfl⟩`. Conclude with `IntermediateField.algebra_adjoin_le_adjoin k _ h1`. Use `⟨IntermediateField.adjoin k (ρ₀ '' (t : Set R)), { toFun := fun x => ⟨ρ₀ x, hmem x⟩ map_one' := Subtype.ext (map_one ρ₀) map_mul' := fun x y => Subtype.ext (map_mul ρ₀ x y) map_zero' := Subtype.ext (map_zero ρ₀) map_add' := fun x y => Subtype.ext (map_add ρ₀ x y) commutes' := fun …` and prove the remaining obligations. Establish `h' : ρ₀ r = 0` using `congrArg Subtype.val h`. Conclude with `Subtype.ext h'`.

Establish `hcL : (c : L) ∈ algebraicClosure k L` using `mem_algebraicClosure_iff.2 (hc.algHom R.val) show ((ρ₁ c : algebraicClosure k L) : L) = c`. Rewrite using `[hfix c hcL]`. Both sides reduce to the same expression.
-/
theorem _root_.GlobalTheory.exists_specialisation_finite {k L : Type*} [Field k] [Field L]
    [Algebra k L] [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (r : R) (hr : r ≠ 0) :
    ∃ (K₁ : IntermediateField k L) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      ∀ c : R, IsAlgebraic k c → (ρ c : L) = c := by
  classical
  haveI : IsAlgClosed (algebraicClosure k L) := IsAlgClosure.isAlgClosed k
  obtain ⟨ρ₁, hfix, hr₁⟩ :=
    exists_algHom_extend_of_fg_ne_zero (algebraicClosure k L) (AlgHom.id k _) R hR r hr
  let ρ₀ : R →ₐ[k] L := (algebraicClosure k L).val.comp ρ₁
  have halg : ∀ x : R, IsAlgebraic k (ρ₀ x) := fun x => mem_algebraicClosure_iff.1 (ρ₁ x).2
  haveI : Algebra.FiniteType k R := (Subalgebra.fg_iff_finiteType R).1 hR
  obtain ⟨t, ht⟩ := Algebra.FiniteType.out (R := k) (A := R)
  haveI : Finite (ρ₀ '' (t : Set R)) := (t.finite_toSet.image _).to_subtype
  have hfin : FiniteDimensional k (IntermediateField.adjoin k (ρ₀ '' (t : Set R))) :=
    IntermediateField.finiteDimensional_adjoin fun y hy => by
      obtain ⟨x, -, rfl⟩ := hy
      exact (halg x).isIntegral
  have hmem : ∀ x : R, ρ₀ x ∈ IntermediateField.adjoin k (ρ₀ '' (t : Set R)) := by
    intro x
    have hx : x ∈ Algebra.adjoin k (t : Set R) := by rw [ht]; exact Algebra.mem_top
    have h1 : ρ₀ x ∈ Algebra.adjoin k (ρ₀ '' (t : Set R)) := by
      rw [← AlgHom.map_adjoin]; exact ⟨x, hx, rfl⟩
    exact IntermediateField.algebra_adjoin_le_adjoin k _ h1
  refine ⟨IntermediateField.adjoin k (ρ₀ '' (t : Set R)),
    { toFun := fun x => ⟨ρ₀ x, hmem x⟩
      map_one' := Subtype.ext (map_one ρ₀)
      map_mul' := fun x y => Subtype.ext (map_mul ρ₀ x y)
      map_zero' := Subtype.ext (map_zero ρ₀)
      map_add' := fun x y => Subtype.ext (map_add ρ₀ x y)
      commutes' := fun a => Subtype.ext (ρ₀.commutes a) }, hfin, fun h => hr₁ ?_, fun c hc => ?_⟩
  · have h' : ρ₀ r = 0 := congrArg Subtype.val h
    exact Subtype.ext h'
  · have hcL : (c : L) ∈ algebraicClosure k L := mem_algebraicClosure_iff.2 (hc.algHom R.val)
    show ((ρ₁ c : algebraicClosure k L) : L) = c
    rw [hfix c hcL]
    rfl

/- English proof (translation)
Set `F : IntermediateField k L` to `IntermediateField.adjoin k {(c : L)}`. Set `σ : F →ₐ[k] L` to `(IntermediateField.val _).comp ((RatFunc.algEquivOfTranscendental t ht).toAlgHom.comp (RatFunc.algEquivOfTranscendental (c : L) hc).symm.toAlgHom)`. Establish `hσ : σ (IntermediateField.AdjoinSimple.gen k (c : L)) = t`. Express the relevant statement in the definitionally equal form `((RatFunc.algEquivOfTranscendental t ht) ((RatFunc.algEquivOfTranscendental (c : L) hc).symm (IntermediateField.AdjoinSimple.gen k (c : L))) : L) = t`. Rewrite using `[RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]`.

Take `⟨A, hA, hRA, -⟩` from `exists_fg_subalgebra_over F R hR 0`. Take `⟨φ, hφ⟩` from `exists_ringHom_extend_of_finiteType F A L σ.toRingHom`. Set `ι : R →+* A` to `{ toFun := fun x => ⟨x.1, hRA x.2⟩ map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }`. Use `⟨{ φ.comp ι with commutes' := fun a => ?_ }, ?_⟩` and prove the remaining obligations. Conclude with `(hφ (algebraMap k F a)).trans (σ.commutes a)`.

Conclude with `(hφ (IntermediateField.AdjoinSimple.gen k (c : L))).trans hσ`.
-/
theorem exists_algHom_apply_eq_of_transcendental {k L : Type*} [Field k] [Field L] [Algebra k L]
    [IsAlgClosed L] (R : Subalgebra k L) (hR : R.FG) (c : R) (hc : Transcendental k (c : L))
    (t : L) (ht : Transcendental k t) : ∃ ρ : R →ₐ[k] L, ρ c = t := by
  let F : IntermediateField k L := IntermediateField.adjoin k {(c : L)}
  let σ : F →ₐ[k] L := (IntermediateField.val _).comp
    ((RatFunc.algEquivOfTranscendental t ht).toAlgHom.comp
      (RatFunc.algEquivOfTranscendental (c : L) hc).symm.toAlgHom)
  have hσ : σ (IntermediateField.AdjoinSimple.gen k (c : L)) = t := by
    change ((RatFunc.algEquivOfTranscendental t ht)
      ((RatFunc.algEquivOfTranscendental (c : L) hc).symm
        (IntermediateField.AdjoinSimple.gen k (c : L))) : L) = t
    rw [RatFunc.algEquivOfTranscendental_symm_gen, RatFunc.algEquivOfTranscendental_X]
  obtain ⟨A, hA, hRA, -⟩ := exists_fg_subalgebra_over F R hR 0
  obtain ⟨φ, hφ⟩ := exists_ringHom_extend_of_finiteType F A L σ.toRingHom
  let ι : R →+* A :=
    { toFun := fun x => ⟨x.1, hRA x.2⟩
      map_one' := rfl, map_mul' := fun _ _ => rfl, map_zero' := rfl, map_add' := fun _ _ => rfl }
  refine ⟨{ φ.comp ι with commutes' := fun a => ?_ }, ?_⟩
  · exact (hφ (algebraMap k F a)).trans (σ.commutes a)
  · exact (hφ (IntermediateField.AdjoinSimple.gen k (c : L))).trans hσ

/- English proof (translation)
Introduce `k _ R hR c r hr`. Use `⟨?_, fun S hS hρ => ?_⟩` and prove the remaining obligations. Take `⟨K₁, ρ, hfin, hr₁, hfix⟩` from `_root_.GlobalTheory.exists_specialisation_finite R hR r hr`. Conclude with `⟨K₁, ρ, hfin, hr₁, hfix c⟩`. Assume the negation of the conclusion as `hc`.

Establish `hct : Transcendental k (c : ℂ)` using `fun h => hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)`. Establish `key : ∀ z : ℂ, Transcendental ℚ z → z ∈ S`. Introduce `z hz`. Establish `hzk : Transcendental k z` using `fun h => hz (h.restrictScalars ℚ)`. Set `e₁` to `RatFunc.algEquivOfTranscendental (c : ℂ) hct`.

Set `e₂` to `RatFunc.algEquivOfTranscendental z hzk`. Set `σ : IntermediateField.adjoin k {(c : ℂ)} →ₐ[k] ℂ` to `(IntermediateField.adjoin k {z}).val.comp (e₂.toAlgHom.comp e₁.symm.toAlgHom)`. Establish `hcmem : (c : ℂ) ∈ IntermediateField.adjoin k {(c : ℂ)}` using `IntermediateField.mem_adjoin_simple_self k (c : ℂ)`. Establish `hσ : σ ⟨c, hcmem⟩ = z`. Establish `h1 : e₁.symm ⟨c, hcmem⟩ = RatFunc.X`.

Rewrite using `[AlgEquiv.symm_apply_eq]`. Conclude with `Subtype.ext (RatFunc.algEquivOfTranscendental_X (c : ℂ) hct).symm`. Use `show ((e₂ (e₁.symm ⟨c, hcmem⟩) : IntermediateField.adjoin k {z}) : ℂ) = z`. Rewrite using `[h1]`. Conclude with `RatFunc.algEquivOfTranscendental_X z hzk`.

Take `⟨ρ, hfix, -⟩` from `exists_algHom_extend_of_fg_ne_zero (IntermediateField.adjoin k {(c : ℂ)}) σ R hR 1 one_ne_zero`. Establish `h` using `hρ ρ`. Rewrite `h` using `[hfix c hcmem, hσ]`. Then use the resulting hypothesis. Establish `hcover : (Set.univ : Set ℂ) ⊆ S ∪ {z | IsAlgebraic ℚ z}` using `fun z _ => by`. Distinguish the cases in `h : IsAlgebraic ℚ z`.

Conclude with `Or.inr h`. Conclude with `Or.inl (key z h)`. Conclude with `not_countable_complex ((hS.union (Algebraic.countable ℚ ℂ)).mono hcover)`.
-/
theorem _root_.GlobalTheory.specialisation_numberField_and_countable_values :
    ∀ (k : IntermediateField ℚ ℂ) [FiniteDimensional ℚ k] (R : Subalgebra k ℂ), R.FG →
    ∀ (c r : R), r ≠ 0 →
    (∃ (K₁ : IntermediateField k ℂ) (ρ : R →ₐ[k] K₁), FiniteDimensional k K₁ ∧ ρ r ≠ 0 ∧
      (IsAlgebraic k c → (ρ c : ℂ) = c)) ∧
    (∀ S : Set ℂ, S.Countable → (∀ ρ : R →ₐ[k] ℂ, ρ c ∈ S) → IsAlgebraic k c) := by
  intro k _ R hR c r hr
  refine ⟨?_, fun S hS hρ => ?_⟩
  · obtain ⟨K₁, ρ, hfin, hr₁, hfix⟩ := _root_.GlobalTheory.exists_specialisation_finite R hR r hr
    exact ⟨K₁, ρ, hfin, hr₁, hfix c⟩
  by_contra hc
  have hct : Transcendental k (c : ℂ) := fun h =>
    hc ((isAlgebraic_algHom_iff R.val Subtype.val_injective).1 h)
  have key : ∀ z : ℂ, Transcendental ℚ z → z ∈ S := by
    intro z hz
    have hzk : Transcendental k z := fun h => hz (h.restrictScalars ℚ)
    let e₁ := RatFunc.algEquivOfTranscendental (c : ℂ) hct
    let e₂ := RatFunc.algEquivOfTranscendental z hzk
    let σ : IntermediateField.adjoin k {(c : ℂ)} →ₐ[k] ℂ :=
      (IntermediateField.adjoin k {z}).val.comp (e₂.toAlgHom.comp e₁.symm.toAlgHom)
    have hcmem : (c : ℂ) ∈ IntermediateField.adjoin k {(c : ℂ)} :=
      IntermediateField.mem_adjoin_simple_self k (c : ℂ)
    have hσ : σ ⟨c, hcmem⟩ = z := by
      have h1 : e₁.symm ⟨c, hcmem⟩ = RatFunc.X := by
        rw [AlgEquiv.symm_apply_eq]
        exact Subtype.ext (RatFunc.algEquivOfTranscendental_X (c : ℂ) hct).symm
      show ((e₂ (e₁.symm ⟨c, hcmem⟩) : IntermediateField.adjoin k {z}) : ℂ) = z
      rw [h1]
      exact RatFunc.algEquivOfTranscendental_X z hzk
    obtain ⟨ρ, hfix, -⟩ :=
      exists_algHom_extend_of_fg_ne_zero (IntermediateField.adjoin k {(c : ℂ)}) σ R hR 1 one_ne_zero
    have h := hρ ρ
    rwa [hfix c hcmem, hσ] at h
  have hcover : (Set.univ : Set ℂ) ⊆ S ∪ {z | IsAlgebraic ℚ z} := fun z _ => by
    by_cases h : IsAlgebraic ℚ z
    · exact Or.inr h
    · exact Or.inl (key z h)
  exact not_countable_complex ((hS.union (Algebraic.countable ℚ ℂ)).mono hcover)

end GlobalTheory
