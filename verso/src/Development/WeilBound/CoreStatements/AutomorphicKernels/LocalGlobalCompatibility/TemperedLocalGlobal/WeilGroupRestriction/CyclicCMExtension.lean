import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ChebotarevDegreeOneStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.WeilGroupAtPlaceDenseInDecompositionGroupStatement
import Development.WeilBound.CoreStatements.AutomorphicKernels.LocalGlobalCompatibility.TemperedLocalGlobal.WeilGroupRestriction.IwahoriCompatibilityOfChains

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.ConjugateSelfDual ReciprocityTheory.Gal Polynomial
open GlobalTheory GlobalTheory.GalOfCusp GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.LocLanglands GlobalTheory.LocGL GlobalTheory.Pst GlobalTheory.UnitaryBC GlobalTheory.HeckeGal Neutral.B1 Formalism.L2.Host Formalism.MainNotions.N
open PositivityTheory.Pf1.CLGD.DescRes
open scoped Pointwise

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

open ComplexConjugate

section Restrict

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

abbrev res : (Ω ≃ₐ[E] Ω) →* (Ω ≃ₐ[F] Ω) := AlgEquiv.restrictScalarsHom F

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem res_apply (σ : Ω ≃ₐ[E] Ω) (x : Ω) : res F σ x = σ x := rfl

def liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) : Ω ≃ₐ[E] Ω :=
  { τ.toRingEquiv with commutes' := h }

/- English proof (translation)
The claim follows from `AlgEquiv.ext fun _ ↦ rfl`.
-/
@[simp] theorem res_liftE (τ : Ω ≃ₐ[F] Ω) (h : ∀ e : E, τ (algebraMap E Ω e) = algebraMap E Ω e) :
    res F (liftE F τ h) = τ := AlgEquiv.ext fun _ ↦ rfl

end Restrict

section Descend

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← map_inv]`. Both sides reduce to the same expression.
-/
theorem res_smul (σ : Ω ≃ₐ[E] Ω) (A : ValuationSubring Ω) : res F σ • A = σ • A := by
  ext x
  rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ← map_inv]
  rfl

/- English proof (translation)
Establish `h1 : σ • A = A` using `h`. Use `show res F σ • A = A`. Rewrite using `[res_smul, h1]`.
-/
theorem res_mem_decompositionSubgroup {σ : Ω ≃ₐ[E] Ω} {A : ValuationSubring Ω}
    (h : σ ∈ A.decompositionSubgroup E) : res F σ ∈ A.decompositionSubgroup F := by
  have h1 : σ • A = A := h
  show res F σ • A = A
  rw [res_smul, h1]

/- English proof (translation)
Set `b` to `Module.finBasis F M`. Set `S : Set Ω` to `Set.range fun i ↦ ((b i : M) : Ω)`. Establish `hSf : Finite S` using `Set.finite_range _ |>.to_subtype`. Use `⟨IntermediateField.adjoin E S, ?_, ?_⟩` and prove the remaining obligations. Use `IntermediateField.finiteDimensional_adjoin ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨i, rfl⟩`. Conclude with `hint _ ((IsIntegral.of_finite F (b i)).map M.val)`. Introduce `σ hσ`. Rewrite `hσ`, the goal using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`.

Establish `hb : ∀ i, res F σ ((b i : M) : Ω) = ((b i : M) : Ω)` using `fun i ↦ hσ _ (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)`. Establish `key : ((res F σ).toLinearMap).comp M.val.toLinearMap = M.val.toLinearMap` using `b.ext fun i ↦ by simpa using hb i`. Use `LinearMap.congr_fun key ⟨y, hy⟩` as an intermediate fact. Simplify using `using this`.
-/
theorem exists_finiteDimensional_res_le [FiniteDimensional F E] (M : IntermediateField F Ω) [FiniteDimensional F M]
    (hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x) :
    ∃ M' : IntermediateField E Ω, FiniteDimensional E M' ∧
      ∀ σ ∈ M'.fixingSubgroup, res F σ ∈ M.fixingSubgroup := by
  classical
  let b := Module.finBasis F M
  let S : Set Ω := Set.range fun i ↦ ((b i : M) : Ω)
  have hSf : Finite S := Set.finite_range _ |>.to_subtype
  refine ⟨IntermediateField.adjoin E S, ?_, ?_⟩
  · refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨i, rfl⟩
    exact hint _ ((IsIntegral.of_finite F (b i)).map M.val)
  · intro σ hσ
    rw [IntermediateField.mem_fixingSubgroup_iff] at hσ ⊢
    intro y hy
    have hb : ∀ i, res F σ ((b i : M) : Ω) = ((b i : M) : Ω) := fun i ↦
      hσ _ (IntermediateField.subset_adjoin E S ⟨i, rfl⟩)
    have key : ((res F σ).toLinearMap).comp M.val.toLinearMap = M.val.toLinearMap :=
      b.ext fun i ↦ by simpa using hb i
    have := LinearMap.congr_fun key ⟨y, hy⟩
    simpa using this

/- English proof (translation)
Use `continuous_of_continuousAt_one (res F) ?_` and prove the remaining obligations. Introduce `s hs`. Rewrite `hs` using `[map_one, krullTopology_mem_nhds_one_iff]`. Take `⟨M, hM, hMs⟩` from `hs`. Take `⟨M', hM', hM'le⟩` from `exists_finiteDimensional_res_le F M hint`.

Rewrite using `[Filter.mem_map, krullTopology_mem_nhds_one_iff]`. Conclude with `⟨M', hM', fun σ hσ ↦ hMs (hM'le σ hσ)⟩`.
-/
theorem continuous_res [FiniteDimensional F E] (hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x) :
    Continuous (res F (E := E) (Ω := Ω)) := by
  refine continuous_of_continuousAt_one (res F) ?_
  intro s hs
  rw [map_one, krullTopology_mem_nhds_one_iff] at hs
  obtain ⟨M, hM, hMs⟩ := hs
  obtain ⟨M', hM', hM'le⟩ := exists_finiteDimensional_res_le F M hint
  rw [Filter.mem_map, krullTopology_mem_nhds_one_iff]
  exact ⟨M', hM', fun σ hσ ↦ hMs (hM'le σ hσ)⟩

end Descend

section Descend2

variable (F : Type*) {E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω]
  [IsScalarTower F E Ω]

end Descend2

section Conj

open ComplexConjugate Polynomial

/- English proof (translation)
Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `hx : IsIntegral F x` using `Algebra.IsIntegral.isIntegral x`. Use `set p := minpoly F x with hp`. Use `set p' : Polynomial Ω := p.map (algebraMap F Ω) with hp'`. Establish `hp'0 : p' ≠ 0` using `(minpoly.monic hx).map _ |>.ne_zero`.

Establish `hcard : p'.roots.card = p'.natDegree` using `IsAlgClosed.card_roots_eq_natDegree`. Establish `hroots` using `roots_map_of_injective_of_card_eq_natDegree j.injective hcard`. Establish `hq0 : p'.map j ≠ 0` using `((minpoly.monic hx).map _ |>.map j).ne_zero`. Establish `hcoef : (p'.map j).map (starRingEnd ℂ) = p'.map j`. Simplify using `only [hp', Polynomial.map_map]`.

Use `congrArg (fun f : F →+* ℂ => Polynomial.map f p) ?_` and prove the remaining obligations. Use extensionality with `r`. Simplify using `using hj r`. Establish `hroot : (p'.map j).IsRoot (conj (j x))`. Establish `h0 : (p'.map j).eval (j x) = 0`.

Rewrite using `[Polynomial.eval_map, Polynomial.eval₂_at_apply, hp', Polynomial.eval_map_algebraMap, hp, minpoly.aeval, map_zero]`. Use `congrArg (starRingEnd ℂ) h0` as an intermediate fact. Rewrite `this` using `[map_zero, ← Polynomial.eval_map_apply, hcoef]`. Conclude with `this`. Establish `hmem : conj (j x) ∈ (p'.map j).roots` using `(Polynomial.mem_roots hq0).2 hroot`.

Rewrite `hmem` using `[← hroots, Multiset.mem_map]`. Take `⟨y, -, hy⟩` from `hmem`. Conclude with `⟨y, hy⟩`.
-/
theorem conj_mem_range {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (j : Ω →+* ℂ)
    (hj : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) (x : Ω) :
    ∃ y : Ω, j y = conj (j x) := by
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have hx : IsIntegral F x := Algebra.IsIntegral.isIntegral x
  set p := minpoly F x with hp
  set p' : Polynomial Ω := p.map (algebraMap F Ω) with hp'
  have hp'0 : p' ≠ 0 := (minpoly.monic hx).map _ |>.ne_zero
  have hcard : p'.roots.card = p'.natDegree := IsAlgClosed.card_roots_eq_natDegree
  have hroots := roots_map_of_injective_of_card_eq_natDegree j.injective hcard
  have hq0 : p'.map j ≠ 0 := ((minpoly.monic hx).map _ |>.map j).ne_zero
  have hcoef : (p'.map j).map (starRingEnd ℂ) = p'.map j := by
    simp only [hp', Polynomial.map_map]
    refine congrArg (fun f : F →+* ℂ => Polynomial.map f p) ?_
    ext r
    simpa using hj r
  have hroot : (p'.map j).IsRoot (conj (j x)) := by
    have h0 : (p'.map j).eval (j x) = 0 := by
      rw [Polynomial.eval_map, Polynomial.eval₂_at_apply, hp', Polynomial.eval_map_algebraMap, hp, minpoly.aeval,
        map_zero]
    have := congrArg (starRingEnd ℂ) h0
    rw [map_zero, ← Polynomial.eval_map_apply, hcoef] at this
    exact this
  have hmem : conj (j x) ∈ (p'.map j).roots := (Polynomial.mem_roots hq0).2 hroot
  rw [← hroots, Multiset.mem_map] at hmem
  obtain ⟨y, -, hy⟩ := hmem
  exact ⟨y, hy⟩

/- English proof (translation)
Use `choose g hg using conj_mem_range j hj`. Set `f : Ω →ₐ[F] Ω` to `{ toFun := g map_one' := j.injective (by simp [hg]) map_mul' := fun x y ↦ j.injective (by rw [hg, map_mul, map_mul, map_mul, hg, hg]) map_zero' := j.injective (by simp [hg]) map_add' := fun x y ↦ j.injective (by rw [hg, map_add, map_add, map_add, hg, hg]) commutes' := fun r ↦ j.i …`. Establish `: Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Conclude with `⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f), fun x ↦ hg x⟩`.
-/
theorem exists_conj {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (j : Ω →+* ℂ)
    (hj : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)) :
    ∃ c : Ω ≃ₐ[F] Ω, ∀ x, j (c x) = conj (j x) := by
  choose g hg using conj_mem_range j hj
  let f : Ω →ₐ[F] Ω :=
    { toFun := g
      map_one' := j.injective (by simp [hg])
      map_mul' := fun x y ↦ j.injective (by rw [hg, map_mul, map_mul, map_mul, hg, hg])
      map_zero' := j.injective (by simp [hg])
      map_add' := fun x y ↦ j.injective (by rw [hg, map_add, map_add, map_add, hg, hg])
      commutes' := fun r ↦ j.injective (by rw [hg, hj]) }
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  exact ⟨AlgEquiv.ofBijective f (Algebra.IsAlgebraic.algHom_bijective f), fun x ↦ hg x⟩

end Conj

section CM

open ComplexConjugate

/- English proof (translation)
Set `K` to `IntermediateField.fixedField Hp`. Prove the components needed by the constructor for the conclusion. Introduce `v`. Set `φ : K →+* ℂ` to `v.embedding`. Set `_ : Algebra K ℂ` to `φ.toAlgebra`.

Establish `: Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Establish `: Algebra.IsAlgebraic K Ω` using `Algebra.IsAlgebraic.tower_top (K := F) K`. Set `j : Ω →+* ℂ` to `(IsAlgClosed.lift : Ω →ₐ[K] ℂ).toRingHom`. Establish `hjK : ∀ y : K, j (y : Ω) = φ y` using `fun y ↦ (IsAlgClosed.lift : Ω →ₐ[K] ℂ).commutes y`. Establish `hjF : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)`.

Introduce `x`. Establish `hr` using `IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))`. Rewrite `hr` using `[InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use `RingHom.congr_fun hr x` as an intermediate fact. Simplify `this` using `[ComplexEmbedding.conjugate_coe_eq]`.

Take `⟨c, hcj⟩` from `exists_conj j hjF`. Establish `hcH : c ∈ Hp` using `hc c j hcj`. Rewrite using `[← v.mk_embedding, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`. Use extensionality with `y`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`.

Use `show conj (φ y) = φ y`. Rewrite using `[← hjK, ← hcj]`. Use `congr 1`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 y.2 c hcH`.
-/
theorem isTotallyReal_fixedField {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] [IsTotallyReal F]
    (Hp : Subgroup (Ω ≃ₐ[F] Ω)) (hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ Hp) :
    IsTotallyReal (IntermediateField.fixedField Hp) := by
  let K := IntermediateField.fixedField Hp
  constructor
  intro v
  let φ : K →+* ℂ := v.embedding
  let _ : Algebra K ℂ := φ.toAlgebra
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have : Algebra.IsAlgebraic K Ω := Algebra.IsAlgebraic.tower_top (K := F) K
  let j : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[K] ℂ).toRingHom
  have hjK : ∀ y : K, j (y : Ω) = φ y := fun y ↦ (IsAlgClosed.lift : Ω →ₐ[K] ℂ).commutes y
  have hjF : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x) := by
    intro x
    have hr := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))
    rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hr
    have := RingHom.congr_fun hr x
    simpa [ComplexEmbedding.conjugate_coe_eq] using this
  obtain ⟨c, hcj⟩ := exists_conj j hjF
  have hcH : c ∈ Hp := hc c j hcj
  rw [← v.mk_embedding, InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]
  ext y
  rw [ComplexEmbedding.conjugate_coe_eq]
  show conj (φ y) = φ y
  rw [← hjK, ← hcj]
  congr 1
  exact (IntermediateField.mem_fixedField_iff _ _).1 y.2 c hcH

/- English proof (translation)
Establish `: IsGalois F Ω` using `inferInstance`. Establish `: IsGalois E Ω` using `inferInstance`. Establish `: Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Establish `hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x` using `fun x hx ↦ hx.tower_top`. Use `set H := Hp.comap (res F (E := E) (Ω := Ω)) with hH`.

Establish `hHo' : IsOpen (H : Set (Ω ≃ₐ[E] Ω))` using `hHo.preimage (continuous_res F hint)`. Set `Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω)` to `⟨H, Subgroup.isClosed_of_isOpen H hHo'⟩`. Establish `hfixH : (IntermediateField.fixedField H).fixingSubgroup = H` using `InfiniteGalois.fixingSubgroup_fixedField Hc`. Establish `hfin : FiniteDimensional E (IntermediateField.fixedField H)` using `(InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfixH]; exact hHo')`. Use `⟨hfin, ?_⟩` and prove the remaining obligations.

Set `Hpc : ClosedSubgroup (Ω ≃ₐ[F] Ω)` to `⟨Hp, Subgroup.isClosed_of_isOpen Hp hHo⟩`. Establish `hfixHp : (IntermediateField.fixedField Hp).fixingSubgroup = Hp` using `InfiniteGalois.fixingSubgroup_fixedField Hpc`. Use `set Ep := IntermediateField.fixedField Hp with hEp`. Use `set E' := IntermediateField.fixedField H with hE'`. Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`.

Take `⟨α, hα⟩ : ∃ α : E, α ∉ Set.range (algebraMap F E)` from `by by_contra! h`. Establish `hbt : (⊥ : IntermediateField F E) = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Rewrite using `[IntermediateField.mem_bot]`.

Conclude with `h x`. Rewrite `hbt` using `[IntermediateField.bot_eq_top_iff_finrank_eq_one, h2]`. Evaluate the numerical expressions using `at hbt`. Establish `htop : IntermediateField.adjoin F {α} = ⊤`. Use `(IntermediateField.isSimpleOrder_of_finrank_prime F E (h2 ▸ Nat.prime_two)).eq_bot_or_eq_top (IntermediateField.adjoin F {α})` as an intermediate fact.

Use `this.resolve_left fun h ↦ hα ?_` and prove the remaining obligations. Establish `hm : α ∈ IntermediateField.adjoin F {α}` using `IntermediateField.mem_adjoin_simple_self F α`. Rewrite `hm` using `[h, IntermediateField.mem_bot]`. Conclude with `hm`. Establish `hαint : IsIntegral F α` using `Algebra.IsIntegral.isIntegral α`.

Establish `hfixE : ∀ σ : Ω ≃ₐ[F] Ω, σ (algebraMap E Ω α) = algebraMap E Ω α → ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e`. Introduce `σ hσ e`. Establish `hadj : Algebra.adjoin F {α} = ⊤`. Rewrite using `[← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx ↦ ?_), htop, IntermediateField.top_toSubalgebra]`. Rewrite using `[Set.mem_singleton_iff.1 hx]`.

Conclude with `hαint.isAlgebraic`. Use `AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := (σ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω)) (φ₂ := IsScalarTower.toAlgHom F E Ω) (by` as an intermediate fact. Introduce `x hx`. Rewrite using `[Set.mem_singleton_iff.1 hx]`. Simplify using `using hσ)`.

Simplify using `using congrArg (fun f ↦ f e) this`. Use `set a := algebraMap E Ω α with ha`. Establish `haEp : a ∉ Ep`. Introduce `haE`. Establish `hle : Hp ⊔ Y.fixingSubgroup ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) a`.

Use `sup_le (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)` and prove the remaining obligations. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 haE σ hσ`. Rewrite using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a (hYE α)`.

Establish `hall : ∀ σ : Ω ≃ₐ[F] Ω, σ a = a`. Introduce `σ`. Use `hle (hsup ▸ Subgroup.mem_top σ)` as an intermediate fact. Rewrite `this` using `[MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]`. Then use the resulting hypothesis. Take `⟨y, hy⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 hall`.

Apply `hα` to reduce the goal to its premises. Use `⟨y, (algebraMap E Ω).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, hy]`. Establish `haF : IsIntegral F a` using `(Algebra.IsAlgebraic.isAlgebraic a).isIntegral`. Establish `haint : IsIntegral Ep a` using `haF.tower_top`.

Establish `hdegF : (minpoly F a).natDegree = 2`. Rewrite using `[ha, ← IsScalarTower.toAlgHom_apply F E Ω, minpoly.algHom_eq _ (algebraMap E Ω).injective, ← IntermediateField.adjoin.finrank hαint, htop, IntermediateField.finrank_top', h2]`. Establish `hdeg : (minpoly Ep a).natDegree = 2`. Establish `hdvd` using `minpoly.dvd_map_of_isScalarTower F Ep a`. Establish `hle : (minpoly Ep a).natDegree ≤ 2`.

Use `Polynomial.natDegree_le_of_dvd hdvd ((minpoly.monic haF).map (algebraMap F Ep)).ne_zero` as an intermediate fact. Rewrite `this` using `[Polynomial.natDegree_map, hdegF]`. Then use the resulting hypothesis. Establish `hne1 : (minpoly Ep a).natDegree ≠ 1`. Rewrite using `[Ne, minpoly.natDegree_eq_one_iff]`. Introduce and unpack `⟨y, hy⟩`.

Conclude with `haEp (by rw [← hy]; exact y.2)`. Establish `hpos` using `minpoly.natDegree_pos haint`. Use linear arithmetic over natural numbers and integers. Establish `hfinrank : Module.finrank Ep (IntermediateField.adjoin Ep {a}) = 2`. Rewrite using `[IntermediateField.adjoin.finrank haint, hdeg]`.

Establish `hEpE' : ∀ y ∈ Ep, y ∈ E'`. Introduce `y hy`. Rewrite `hy`, the goal using `[IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`. Conclude with `hy (res F σ) hσ`.

Establish `haE' : a ∈ E'`. Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `σ _`. Conclude with `σ.commutes α`. Establish `hset : ∀ x : Ω, x ∈ E' ↔ x ∈ IntermediateField.adjoin Ep {a}`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Set `L₁` to `(IntermediateField.adjoin Ep {a}).restrictScalars F`. Establish `hx' : x ∈ IntermediateField.fixedField L₁.fixingSubgroup`.

Rewrite using `[IntermediateField.mem_fixedField_iff]`. Introduce `σ hσ`. Establish `hσEp : σ ∈ Hp`. Rewrite using `[← hfixHp, IntermediateField.mem_fixingSubgroup_iff]`. Introduce `y hy`.

Conclude with `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y (IntermediateField.algebraMap_mem (IntermediateField.adjoin Ep {a}) (⟨y, hy⟩ : Ep))`. Establish `hσa : σ a = a` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a (IntermediateField.mem_adjoin_simple_self Ep a)`. Establish `hσE` using `hfixE σ hσa`. Establish `hmem : liftE F σ hσE ∈ H`. Rewrite using `[hH, Subgroup.mem_comap, res_liftE]`.

Conclude with `hσEp`. Conclude with `(IntermediateField.mem_fixedField_iff _ _).1 hx _ hmem`. Rewrite `hx'` using `[InfiniteGalois.fixedField_fixingSubgroup]`. Then use the resulting hypothesis. Introduce `hx`. Set `K' : IntermediateField Ep Ω` to `E'.toSubfield.toIntermediateField (fun y ↦ hEpE' y.1 y.2)`.

Establish `hle : IntermediateField.adjoin Ep {a} ≤ K'` using `IntermediateField.adjoin_simple_le_iff.2 haE'`. Conclude with `hle hx`. Set `ι : Ep →+* E'` to `{ toFun := fun y ↦ ⟨y, hEpE' y y.2⟩, map_one' := rfl, map_mul' := fun _ _ ↦ rfl, map_zero' := rfl, map_add' := fun _ _ ↦ rfl }`. Set `_ : Algebra Ep E'` to `ι.toAlgebra`. Set `jeq : IntermediateField.adjoin Ep {a} ≃+* E'` to `{ toFun := fun y ↦ ⟨y, (hset y).2 y.2⟩, invFun := fun y ↦ ⟨y, (hset y).1 y.2⟩, left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }`.

Establish `hq : Module.finrank Ep E' = 2`. Rewrite using `[← hfinrank]`. Conclude with `(Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl Ep) jeq (by ext; rfl)).symm`. Establish `: IsTotallyReal Ep` using `isTotallyReal_fixedField Hp hc`. Establish `: FiniteDimensional ℚ E'` using `Module.Finite.trans E E'`.

Establish `: Algebra.IsIntegral ℚ E'` using `Algebra.IsIntegral.of_finite ℚ E'`. Establish `: IsTotallyComplex E'` using `isTotallyComplex_of_algebra E E'`. Establish `: Algebra.IsQuadraticExtension Ep E'` using `{ toFree := Module.Free.of_divisionRing Ep E', finrank_eq_two' := hq }`. Conclude with `IsCMField.ofCMExtension Ep E'`.
-/
theorem cm_of_descend (F : Type*) {E Ω : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω]
    [CharZero Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω] [IsTotallyReal F] [IsTotallyComplex E]
    [Algebra.IsQuadraticExtension F E] [IsAlgClosure F Ω] [IsAlgClosure E Ω]
    (Hp : Subgroup (Ω ≃ₐ[F] Ω)) (hHo : IsOpen (Hp : Set (Ω ≃ₐ[F] Ω)))
    (hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ Hp)
    (Y : IntermediateField F Ω) (hYE : ∀ e : E, algebraMap E Ω e ∈ Y) (hsup : Hp ⊔ Y.fixingSubgroup = ⊤) :
    FiniteDimensional E (IntermediateField.fixedField (Hp.comap (res F (E := E) (Ω := Ω)))) ∧
      IsCMField (IntermediateField.fixedField (Hp.comap (res F (E := E) (Ω := Ω)))) := by
  classical
  have : IsGalois F Ω := inferInstance
  have : IsGalois E Ω := inferInstance
  have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
  have hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x := fun x hx ↦ hx.tower_top
  set H := Hp.comap (res F (E := E) (Ω := Ω)) with hH
  have hHo' : IsOpen (H : Set (Ω ≃ₐ[E] Ω)) := hHo.preimage (continuous_res F hint)
  let Hc : ClosedSubgroup (Ω ≃ₐ[E] Ω) := ⟨H, Subgroup.isClosed_of_isOpen H hHo'⟩
  have hfixH : (IntermediateField.fixedField H).fixingSubgroup = H := InfiniteGalois.fixingSubgroup_fixedField Hc
  have hfin : FiniteDimensional E (IntermediateField.fixedField H) :=
    (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfixH]; exact hHo')
  refine ⟨hfin, ?_⟩
  let Hpc : ClosedSubgroup (Ω ≃ₐ[F] Ω) := ⟨Hp, Subgroup.isClosed_of_isOpen Hp hHo⟩
  have hfixHp : (IntermediateField.fixedField Hp).fixingSubgroup = Hp := InfiniteGalois.fixingSubgroup_fixedField Hpc
  set Ep := IntermediateField.fixedField Hp with hEp
  set E' := IntermediateField.fixedField H with hE'
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  obtain ⟨α, hα⟩ : ∃ α : E, α ∉ Set.range (algebraMap F E) := by
    by_contra! h
    have hbt : (⊥ : IntermediateField F E) = ⊤ := by
      rw [eq_top_iff]; intro x _; rw [IntermediateField.mem_bot]; exact h x
    rw [IntermediateField.bot_eq_top_iff_finrank_eq_one, h2] at hbt
    norm_num at hbt
  have htop : IntermediateField.adjoin F {α} = ⊤ := by
    have := (IntermediateField.isSimpleOrder_of_finrank_prime F E (h2 ▸ Nat.prime_two)).eq_bot_or_eq_top
      (IntermediateField.adjoin F {α})
    refine this.resolve_left fun h ↦ hα ?_
    have hm : α ∈ IntermediateField.adjoin F {α} := IntermediateField.mem_adjoin_simple_self F α
    rw [h, IntermediateField.mem_bot] at hm
    exact hm
  have hαint : IsIntegral F α := Algebra.IsIntegral.isIntegral α
  have hfixE : ∀ σ : Ω ≃ₐ[F] Ω, σ (algebraMap E Ω α) = algebraMap E Ω α →
      ∀ e : E, σ (algebraMap E Ω e) = algebraMap E Ω e := by
    intro σ hσ e
    have hadj : Algebra.adjoin F {α} = ⊤ := by
      rw [← IntermediateField.adjoin_toSubalgebra_of_isAlgebraic (fun x hx ↦ ?_), htop,
        IntermediateField.top_toSubalgebra]
      rw [Set.mem_singleton_iff.1 hx]; exact hαint.isAlgebraic
    have := AlgHom.ext_of_adjoin_eq_top hadj (φ₁ := (σ : Ω →ₐ[F] Ω).comp (IsScalarTower.toAlgHom F E Ω))
      (φ₂ := IsScalarTower.toAlgHom F E Ω) (by
        intro x hx; rw [Set.mem_singleton_iff.1 hx]; simpa using hσ)
    simpa using congrArg (fun f ↦ f e) this
  set a := algebraMap E Ω α with ha
  have haEp : a ∉ Ep := by
    intro haE
    have hle : Hp ⊔ Y.fixingSubgroup ≤ MulAction.stabilizer (Ω ≃ₐ[F] Ω) a := by
      refine sup_le (fun σ hσ ↦ ?_) (fun σ hσ ↦ ?_)
      · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact (IntermediateField.mem_fixedField_iff _ _).1 haE σ hσ
      · rw [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def]
        exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a (hYE α)
    have hall : ∀ σ : Ω ≃ₐ[F] Ω, σ a = a := by
      intro σ
      have := hle (hsup ▸ Subgroup.mem_top σ)
      rwa [MulAction.mem_stabilizer_iff, AlgEquiv.smul_def] at this
    obtain ⟨y, hy⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed a).2 hall
    apply hα
    refine ⟨y, (algebraMap E Ω).injective ?_⟩
    rw [← IsScalarTower.algebraMap_apply, hy]
  have haF : IsIntegral F a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have haint : IsIntegral Ep a := haF.tower_top
  have hdegF : (minpoly F a).natDegree = 2 := by
    rw [ha, ← IsScalarTower.toAlgHom_apply F E Ω, minpoly.algHom_eq _ (algebraMap E Ω).injective,
      ← IntermediateField.adjoin.finrank hαint, htop, IntermediateField.finrank_top', h2]
  have hdeg : (minpoly Ep a).natDegree = 2 := by
    have hdvd := minpoly.dvd_map_of_isScalarTower F Ep a
    have hle : (minpoly Ep a).natDegree ≤ 2 := by
      have := Polynomial.natDegree_le_of_dvd hdvd ((minpoly.monic haF).map (algebraMap F Ep)).ne_zero
      rwa [Polynomial.natDegree_map, hdegF] at this
    have hne1 : (minpoly Ep a).natDegree ≠ 1 := by
      rw [Ne, minpoly.natDegree_eq_one_iff]
      rintro ⟨y, hy⟩
      exact haEp (by rw [← hy]; exact y.2)
    have hpos := minpoly.natDegree_pos haint
    omega
  have hfinrank : Module.finrank Ep (IntermediateField.adjoin Ep {a}) = 2 := by
    rw [IntermediateField.adjoin.finrank haint, hdeg]
  have hEpE' : ∀ y ∈ Ep, y ∈ E' := by
    intro y hy
    rw [IntermediateField.mem_fixedField_iff] at hy ⊢
    intro σ hσ
    exact hy (res F σ) hσ
  have haE' : a ∈ E' := by
    rw [IntermediateField.mem_fixedField_iff]
    intro σ _
    exact σ.commutes α
  have hset : ∀ x : Ω, x ∈ E' ↔ x ∈ IntermediateField.adjoin Ep {a} := by
    intro x
    constructor
    · intro hx
      let L₁ := (IntermediateField.adjoin Ep {a}).restrictScalars F
      have hx' : x ∈ IntermediateField.fixedField L₁.fixingSubgroup := by
        rw [IntermediateField.mem_fixedField_iff]
        intro σ hσ
        have hσEp : σ ∈ Hp := by
          rw [← hfixHp, IntermediateField.mem_fixingSubgroup_iff]
          intro y hy
          exact (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ y
            (IntermediateField.algebraMap_mem (IntermediateField.adjoin Ep {a}) (⟨y, hy⟩ : Ep))
        have hσa : σ a = a := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ a
          (IntermediateField.mem_adjoin_simple_self Ep a)
        have hσE := hfixE σ hσa
        have hmem : liftE F σ hσE ∈ H := by
          rw [hH, Subgroup.mem_comap, res_liftE]; exact hσEp
        exact (IntermediateField.mem_fixedField_iff _ _).1 hx _ hmem
      rwa [InfiniteGalois.fixedField_fixingSubgroup] at hx'
    · intro hx
      let K' : IntermediateField Ep Ω := E'.toSubfield.toIntermediateField (fun y ↦ hEpE' y.1 y.2)
      have hle : IntermediateField.adjoin Ep {a} ≤ K' := IntermediateField.adjoin_simple_le_iff.2 haE'
      exact hle hx
  let ι : Ep →+* E' :=
    { toFun := fun y ↦ ⟨y, hEpE' y y.2⟩, map_one' := rfl, map_mul' := fun _ _ ↦ rfl, map_zero' := rfl,
      map_add' := fun _ _ ↦ rfl }
  let _ : Algebra Ep E' := ι.toAlgebra
  let jeq : IntermediateField.adjoin Ep {a} ≃+* E' :=
    { toFun := fun y ↦ ⟨y, (hset y).2 y.2⟩, invFun := fun y ↦ ⟨y, (hset y).1 y.2⟩,
      left_inv := fun _ ↦ rfl, right_inv := fun _ ↦ rfl, map_mul' := fun _ _ ↦ rfl, map_add' := fun _ _ ↦ rfl }
  have hq : Module.finrank Ep E' = 2 := by
    rw [← hfinrank]
    exact (Algebra.finrank_eq_of_equiv_equiv (RingEquiv.refl Ep) jeq (by ext; rfl)).symm
  have : IsTotallyReal Ep := isTotallyReal_fixedField Hp hc
  have : FiniteDimensional ℚ E' := Module.Finite.trans E E'
  have : Algebra.IsIntegral ℚ E' := Algebra.IsIntegral.of_finite ℚ E'
  have : IsTotallyComplex E' := isTotallyComplex_of_algebra E E'
  have : Algebra.IsQuadraticExtension Ep E' := { toFree := Module.Free.of_divisionRing Ep E', finrank_eq_two' := hq }
  exact IsCMField.ofCMExtension Ep E'

end CM

section Split

variable {F E Ω : Type*} [Field F] [Field E] [Field Ω] [Algebra F E] [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω]

/- English proof (translation)
Use `set ι := IsScalarTower.toAlgHom F E Ω`. Take `⟨e₁, he₁⟩` from `hg`. Take `⟨e₂, he₂⟩` from `hτ`. Assume the negation of the conclusion as `hne`. Set `f : Fin 3 → (E →ₐ[F] Ω)` to `![ι, (g : Ω →ₐ[F] Ω).comp ι, (τ : Ω →ₐ[F] Ω).comp ι]`.

Establish `hf : Function.Injective f`. Establish `h01 : ι ≠ (g : Ω →ₐ[F] Ω).comp ι` using `fun h ↦ he₁ (by simpa [ι] using (DFunLike.congr_fun h e₁).symm)`. Establish `h02 : ι ≠ (τ : Ω →ₐ[F] Ω).comp ι` using `fun h ↦ he₂ (by simpa [ι] using (DFunLike.congr_fun h e₂).symm)`. Establish `h12 : (g : Ω →ₐ[F] Ω).comp ι ≠ (τ : Ω →ₐ[F] Ω).comp ι` using `fun h ↦ hne (by simpa [ι] using DFunLike.congr_fun h e)`. Introduce `a b hab`.

Apply the tactic sequence `fin_cases a <;> fin_cases b <;> simp_all [f]`. Establish `hcard` using `Nat.card_le_card_of_injective f hf`. Establish `hle : Nat.card (E →ₐ[F] Ω) ≤ 2` using `h2 ▸ card_algHom_le_finrank (K := F) (M := E) (L := Ω)`. Simplify using `only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard hle`. Use linear arithmetic over natural numbers and integers.
-/
theorem eq_on_of_not_fix [FiniteDimensional F E] (h2 : Module.finrank F E = 2) {g τ : Ω ≃ₐ[F] Ω}
    (hg : ∃ e : E, g (algebraMap E Ω e) ≠ algebraMap E Ω e) (hτ : ∃ e : E, τ (algebraMap E Ω e) ≠ algebraMap E Ω e)
    (e : E) : g (algebraMap E Ω e) = τ (algebraMap E Ω e) := by
  classical
  set ι := IsScalarTower.toAlgHom F E Ω
  obtain ⟨e₁, he₁⟩ := hg
  obtain ⟨e₂, he₂⟩ := hτ
  by_contra hne
  let f : Fin 3 → (E →ₐ[F] Ω) := ![ι, (g : Ω →ₐ[F] Ω).comp ι, (τ : Ω →ₐ[F] Ω).comp ι]
  have hf : Function.Injective f := by
    have h01 : ι ≠ (g : Ω →ₐ[F] Ω).comp ι := fun h ↦ he₁ (by simpa [ι] using (DFunLike.congr_fun h e₁).symm)
    have h02 : ι ≠ (τ : Ω →ₐ[F] Ω).comp ι := fun h ↦ he₂ (by simpa [ι] using (DFunLike.congr_fun h e₂).symm)
    have h12 : (g : Ω →ₐ[F] Ω).comp ι ≠ (τ : Ω →ₐ[F] Ω).comp ι := fun h ↦ hne (by simpa [ι] using DFunLike.congr_fun h e)
    intro a b hab
    fin_cases a <;> fin_cases b <;> simp_all [f]
  have hcard := Nat.card_le_card_of_injective f hf
  have hle : Nat.card (E →ₐ[F] Ω) ≤ 2 := h2 ▸ card_algHom_le_finrank (K := F) (M := E) (L := Ω)
  simp only [Nat.card_eq_fintype_card, Fintype.card_fin] at hcard hle
  omega

end Split

section Places

/- English proof (translation)
Introduce `x`. Use `show A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (w.under (𝓞 F)).asIdeal`. Rewrite using `[IsScalarTower.algebraMap_apply F E Ω]`. Use `h (algebraMap (𝓞 F) (𝓞 E) x)` as an intermediate fact. Rewrite using `[HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]`.

Conclude with `this`.
-/
theorem isPlaceOver_under {F E Ω : Type*} [Field F] [NumberField F] [Field E] [NumberField E] [Field Ω] [Algebra F E]
    [Algebra E Ω] [Algebra F Ω] [IsScalarTower F E Ω] {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
    (h : IsPlaceOver A w) : IsPlaceOver A (w.under (𝓞 F)) := by
  intro x
  show A.valuation (algebraMap F Ω (x : F)) < 1 ↔ x ∈ (w.under (𝓞 F)).asIdeal
  rw [IsScalarTower.algebraMap_apply F E Ω]
  have := h (algebraMap (𝓞 F) (𝓞 E) x)
  rw [HeightOneSpectrum.under_asIdeal, Ideal.mem_comap]
  exact this

/- English proof (translation)
Rewrite using `[valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀, map_eq_zero_iff _ (τ⁻¹).injective]`.
-/
theorem smul_valuation_lt_one_iff {F Ω : Type*} [Field F] [Field Ω] [Algebra F Ω] (τ : Ω ≃ₐ[F] Ω)
    (A : ValuationSubring Ω) (y : Ω) : (τ • A).valuation y < 1 ↔ A.valuation (τ⁻¹ y) < 1 := by
  rw [valuation_lt_one_iff', valuation_lt_one_iff', ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem,
    ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, AlgEquiv.smul_def, AlgEquiv.smul_def, map_inv₀,
    map_eq_zero_iff _ (τ⁻¹).injective]

/- English proof (translation)
Set `F` to `maximalRealSubfield E`. Establish `: IsAlgClosure F Ω` using `IsAlgClosure.ofAlgebraic F E Ω`. Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Assume the negation of the conclusion as `hne`. Take `⟨u, hu, huw⟩` from `hs`.

Take `⟨Au, hAu⟩` from `exists_isPlaceOver Ω u`. Establish `hA' : IsPlaceOver A (w.under (𝓞 F))` using `isPlaceOver_under h`. Establish `hAu' : IsPlaceOver Au (w.under (𝓞 F))` using `huw ▸ isPlaceOver_under hAu`. Take `⟨τ, hτ⟩` from `exists_smul_eq_of_isPlaceOver hA' hAu'`. Establish `hmove : ∃ e : E, g (algebraMap E Ω e) ≠ algebraMap E Ω e` using `⟨e, hne⟩`.

Establish `key : ∀ x : E, A.valuation (τ⁻¹ (algebraMap E Ω x)) < 1 ↔ A.valuation (algebraMap E Ω x) < 1`. Introduce `x`. Distinguish the cases in `hτE : ∀ e : E, τ⁻¹ (algebraMap E Ω e) = algebraMap E Ω e`. Rewrite using `[hτE x]`. Use `push Not at hτE`.

Rewrite using `[eq_on_of_not_fix h2 hτE hmove x]`. Conclude with `valuation_apply_lt_one_iff hg _`. Apply `hu` to reduce the goal to its premises. Use `eq_of_isPlaceOver hAu ?_` and prove the remaining obligations. Introduce `x`.

Rewrite using `[← hτ, smul_valuation_lt_one_iff, key]`. Conclude with `h x`.
-/
theorem fix_of_mem_dec {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) (hs : IsSplitAt w)
    (g : Ω ≃ₐ[maximalRealSubfield E] Ω) (hg : g ∈ Dec (F := maximalRealSubfield E) A) (e : E) :
    g (algebraMap E Ω e) = algebraMap E Ω e := by
  classical
  let F := maximalRealSubfield E
  have : IsAlgClosure F Ω := IsAlgClosure.ofAlgebraic F E Ω
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E
  by_contra hne
  obtain ⟨u, hu, huw⟩ := hs
  obtain ⟨Au, hAu⟩ := exists_isPlaceOver Ω u
  have hA' : IsPlaceOver A (w.under (𝓞 F)) := isPlaceOver_under h
  have hAu' : IsPlaceOver Au (w.under (𝓞 F)) := huw ▸ isPlaceOver_under hAu
  obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver hA' hAu'
  have hmove : ∃ e : E, g (algebraMap E Ω e) ≠ algebraMap E Ω e := ⟨e, hne⟩
  have key : ∀ x : E, A.valuation (τ⁻¹ (algebraMap E Ω x)) < 1 ↔ A.valuation (algebraMap E Ω x) < 1 := by
    intro x
    by_cases hτE : ∀ e : E, τ⁻¹ (algebraMap E Ω e) = algebraMap E Ω e
    · rw [hτE x]
    · push Not at hτE
      rw [eq_on_of_not_fix h2 hτE hmove x]
      exact valuation_apply_lt_one_iff hg _
  apply hu
  refine eq_of_isPlaceOver hAu ?_
  intro x
  rw [← hτ, smul_valuation_lt_one_iff, key]
  exact h x

end Places

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension.Loc

/- English proof (translation)
Assume the negation of the conclusion as `hne`. Establish `hN0 : 0 < N`. Break down `Nat.eq_zero_or_pos N with h0 | h0` into its components or cases. Rewrite `hN` using `[h0, Nat.cast_zero, map_zero]`. Conclude with `absurd hN zero_ne_one`.

Conclude with `h0`. Establish `hfin : IsOfFinOrder r` using `isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN0, hr⟩`. Use `set d := orderOf r with hd_def`. Establish `hd : IsPrimitiveRoot r d` using `IsPrimitiveRoot.orderOf r`. Establish `hdpos : 0 < d` using `hfin.orderOf_pos`.

Establish `hd1 : 1 < d`. Break down `Nat.lt_or_ge 1 d with h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd (orderOf_eq_one_iff.1 (by omega)) hne`. Establish `hdN : d ∣ N` using `orderOf_dvd_of_pow_eq_one hr`.

Establish `hsum` using `hd.geom_sum_eq_zero hd1`. Establish `hvr : A.valuation r ≤ 1`. Assume the negation of the conclusion as `hc`. Establish `h1 : 1 < A.valuation r` using `not_le.mp hc`. Establish `h2 : 1 < A.valuation r ^ N` using `one_lt_pow₀ h1 hN0.ne'`.

Rewrite `h2` using `[← map_pow, hr, map_one]`. Conclude with `lt_irrefl _ h2`. Establish `hterm : ∀ i, A.valuation (1 - r ^ i) < 1`. Introduce `i`. Establish `e : 1 - r ^ i = -((∑ j ∈ Finset.range i, r ^ j) * (r - 1))` using `by rw [geom_sum_mul]; ring`.

Establish `hs : A.valuation (∑ j ∈ Finset.range i, r ^ j) ≤ 1` using `A.valuation.map_sum_le fun j _ ↦ val_pow_le_one hvr j`. Rewrite using `[e, Valuation.map_neg, map_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_left' hs) h`. Establish `hdval : A.valuation (d : Ω) < 1`. Establish `e : (d : Ω) = ∑ i ∈ Finset.range d, (1 - r ^ i)`.

Rewrite using `[Finset.sum_sub_distrib, hsum]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Conclude with `A.valuation.map_sum_lt one_ne_zero fun i _ ↦ hterm i`. Take `⟨e, he⟩` from `hdN`.

Establish `hle : A.valuation (N : Ω) ≤ A.valuation (d : Ω)`. Rewrite using `[he, Nat.cast_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' (valuation_natCast_le_one A e)`. Rewrite `hle` using `[hN]`. Conclude with `absurd (lt_of_le_of_lt hle hdval) (lt_irrefl 1)`.
-/
theorem eq_one_of_val_sub_one_lt {Ω : Type*} [Field Ω] {A : ValuationSubring Ω} {N : ℕ}
    (hN : A.valuation (N : Ω) = 1) {r : Ω} (hr : r ^ N = 1) (h : A.valuation (r - 1) < 1) : r = 1 := by
  by_contra hne
  have hN0 : 0 < N := by
    rcases Nat.eq_zero_or_pos N with h0 | h0
    · rw [h0, Nat.cast_zero, map_zero] at hN; exact absurd hN zero_ne_one
    · exact h0
  have hfin : IsOfFinOrder r := isOfFinOrder_iff_pow_eq_one.2 ⟨N, hN0, hr⟩
  set d := orderOf r with hd_def
  have hd : IsPrimitiveRoot r d := IsPrimitiveRoot.orderOf r
  have hdpos : 0 < d := hfin.orderOf_pos
  have hd1 : 1 < d := by
    rcases Nat.lt_or_ge 1 d with h1 | h1
    · exact h1
    · exact absurd (orderOf_eq_one_iff.1 (by omega)) hne
  have hdN : d ∣ N := orderOf_dvd_of_pow_eq_one hr
  have hsum := hd.geom_sum_eq_zero hd1
  have hvr : A.valuation r ≤ 1 := by
    by_contra hc
    have h1 : 1 < A.valuation r := not_le.mp hc
    have h2 : 1 < A.valuation r ^ N := one_lt_pow₀ h1 hN0.ne'
    rw [← map_pow, hr, map_one] at h2
    exact lt_irrefl _ h2
  have hterm : ∀ i, A.valuation (1 - r ^ i) < 1 := by
    intro i
    have e : 1 - r ^ i = -((∑ j ∈ Finset.range i, r ^ j) * (r - 1)) := by rw [geom_sum_mul]; ring
    have hs : A.valuation (∑ j ∈ Finset.range i, r ^ j) ≤ 1 :=
      A.valuation.map_sum_le fun j _ ↦ val_pow_le_one hvr j
    rw [e, Valuation.map_neg, map_mul]
    exact lt_of_le_of_lt (mul_le_of_le_one_left' hs) h
  have hdval : A.valuation (d : Ω) < 1 := by
    have e : (d : Ω) = ∑ i ∈ Finset.range d, (1 - r ^ i) := by
      rw [Finset.sum_sub_distrib, hsum]; simp
    rw [e]
    exact A.valuation.map_sum_lt one_ne_zero fun i _ ↦ hterm i
  obtain ⟨e, he⟩ := hdN
  have hle : A.valuation (N : Ω) ≤ A.valuation (d : Ω) := by
    rw [he, Nat.cast_mul, map_mul]
    exact mul_le_of_le_one_right' (valuation_natCast_le_one A e)
  rw [hN] at hle
  exact absurd (lt_of_le_of_lt hle hdval) (lt_irrefl 1)

/- English proof (translation)
Introduce `k`. Proceed by induction on `k using Nat.strong_induction_on with`. Consider the case `_ k ih`. Introduce `h`. Distinguish the cases in `hk : k < m`.

Establish `h1 : q ^ k < q ^ m` using `Nat.pow_lt_pow_right hq hk`. Establish `h2` using `Nat.one_le_pow k q (by omega)`. Establish `hlt : q ^ k - 1 < q ^ m - 1` using `by omega`. Establish `h0 : q ^ k - 1 = 0` using `Nat.eq_zero_of_dvd_of_lt h hlt`. Establish `hk1 : q ^ k = 1` using `by omega`.

Break down `Nat.pow_eq_one.1 hk1 with hq1 | hk0` into its components or cases. Use linear arithmetic over natural numbers and integers. Rewrite using `[hk0]`. Conclude with `dvd_zero m`. Use `push Not at hk`.

Establish `h1 : q ^ k = q ^ (k - m) * q ^ m` using `by rw [← pow_add, Nat.sub_add_cancel hk]`. Establish `h2` using `Nat.one_le_pow (k - m) q (by omega)`. Establish `h3` using `Nat.one_le_pow m q (by omega)`. Establish `h4 : q ^ (k - m) ≤ q ^ (k - m) * q ^ m` using `Nat.le_mul_of_pos_right _ h3`. Establish `h5 : q ^ (k - m) * (q ^ m - 1) = q ^ (k - m) * q ^ m - q ^ (k - m)` using `Nat.mul_sub_one _ _`.

Establish `key : q ^ k - 1 = q ^ (k - m) * (q ^ m - 1) + (q ^ (k - m) - 1)`. Rewrite using `[h1, h5]`. Use linear arithmetic over natural numbers and integers. Establish `hd : q ^ m - 1 ∣ q ^ (k - m) - 1` using `(Nat.dvd_add_right (dvd_mul_left _ _)).1 (key ▸ h)`. Use `Nat.dvd_add (ih (k - m) (by omega) hd) (dvd_refl m)` as an intermediate fact.

Rewrite `this` using `[Nat.sub_add_cancel hk]`. Then use the resulting hypothesis.
-/
theorem dvd_of_pow_sub_one_dvd {q m : ℕ} (hq : 1 < q) (hm : 0 < m) :
    ∀ k : ℕ, q ^ m - 1 ∣ q ^ k - 1 → m ∣ k := by
  intro k
  induction k using Nat.strong_induction_on with
  | _ k ih =>
    intro h
    by_cases hk : k < m
    · have h1 : q ^ k < q ^ m := Nat.pow_lt_pow_right hq hk
      have h2 := Nat.one_le_pow k q (by omega)
      have hlt : q ^ k - 1 < q ^ m - 1 := by omega
      have h0 : q ^ k - 1 = 0 := Nat.eq_zero_of_dvd_of_lt h hlt
      have hk1 : q ^ k = 1 := by omega
      rcases Nat.pow_eq_one.1 hk1 with hq1 | hk0
      · omega
      · rw [hk0]; exact dvd_zero m
    · push Not at hk
      have h1 : q ^ k = q ^ (k - m) * q ^ m := by rw [← pow_add, Nat.sub_add_cancel hk]
      have h2 := Nat.one_le_pow (k - m) q (by omega)
      have h3 := Nat.one_le_pow m q (by omega)
      have h4 : q ^ (k - m) ≤ q ^ (k - m) * q ^ m := Nat.le_mul_of_pos_right _ h3
      have h5 : q ^ (k - m) * (q ^ m - 1) = q ^ (k - m) * q ^ m - q ^ (k - m) := Nat.mul_sub_one _ _
      have key : q ^ k - 1 = q ^ (k - m) * (q ^ m - 1) + (q ^ (k - m) - 1) := by
        rw [h1, h5]; omega
      have hd : q ^ m - 1 ∣ q ^ (k - m) - 1 := (Nat.dvd_add_right (dvd_mul_left _ _)).1 (key ▸ h)
      have := Nat.dvd_add (ih (k - m) (by omega) hd) (dvd_refl m)
      rwa [Nat.sub_add_cancel hk] at this

section Deg

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω]

/- English proof (translation)
Establish `: Finite (𝓞 E ⧸ w.asIdeal)` using `w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, normV, ← nsmul_one]`. Conclude with `card_nsmul_eq_zero'`.
-/
theorem natCast_normV_mem (w : HeightOneSpectrum (𝓞 E)) : ((normV w : ℕ) : 𝓞 E) ∈ w.asIdeal := by
  have : Finite (𝓞 E ⧸ w.asIdeal) := w.asIdeal.finiteQuotientOfFreeOfNeBot w.ne_bot
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, normV, ← nsmul_one]
  exact card_nsmul_eq_zero'

/- English proof (translation)
Break down `lt_trichotomy (A.valuation ζ) 1 with hlt | heq | hgt` into its components or cases. Establish `h1 : A.valuation ζ ^ N < 1` using `pow_lt_one₀ zero_le hlt hN.ne'`. Rewrite `h1` using `[← map_pow, hζ, map_one]`. Conclude with `absurd h1 (lt_irrefl 1)`. Conclude with `heq`.

Establish `h1 : 1 < A.valuation ζ ^ N` using `one_lt_pow₀ hgt hN.ne'`. Rewrite `h1` using `[← map_pow, hζ, map_one]`. Conclude with `absurd h1 (lt_irrefl 1)`.
-/
theorem val_eq_one_of_pow {A : ValuationSubring Ω} {N : ℕ} (hN : 0 < N) {ζ : Ω} (hζ : ζ ^ N = 1) :
    A.valuation ζ = 1 := by
  rcases lt_trichotomy (A.valuation ζ) 1 with hlt | heq | hgt
  · have h1 : A.valuation ζ ^ N < 1 := pow_lt_one₀ zero_le hlt hN.ne'
    rw [← map_pow, hζ, map_one] at h1; exact absurd h1 (lt_irrefl 1)
  · exact heq
  · have h1 : 1 < A.valuation ζ ^ N := one_lt_pow₀ hgt hN.ne'
    rw [← map_pow, hζ, map_one] at h1; exact absurd h1 (lt_irrefl 1)

variable [IsAlgClosure E Ω]

/- English proof (translation)
Establish `hq : 1 < normV w` using `one_lt_normV w`. Use `set q := normV w with hq_def`. Use `set N := q ^ m - 1 with hN_def`. Establish `hqm : 1 < q ^ m` using `Nat.one_lt_pow hm.ne' hq`. Establish `hN0 : 0 < N` using `by omega`.

Establish `hqv : A.valuation (q : Ω) < 1`. Use `(h ((normV w : ℕ) : 𝓞 E)).2 (natCast_normV_mem w)` as an intermediate fact. Simplify using `using this`. Establish `hNv : A.valuation (N : Ω) = 1`. Rewrite using `[hN_def, Nat.cast_sub hqm.le, Nat.cast_pow, Nat.cast_one, Valuation.map_sub_eq_of_lt_right, map_one]`.

Rewrite using `[map_pow, map_one]`. Conclude with `pow_lt_one₀ zero_le hqv hm.ne'`. Establish `hζN : ζ ^ N = 1` using `hζ.pow_eq_one`. Establish `hζv : A.valuation ζ = 1` using `val_eq_one_of_pow hN0 hζN`. Establish `hcop : Nat.Coprime N q`.

Establish `hc : Nat.Coprime N (N + 1)` using `Nat.coprime_self_add_right.2 (Nat.coprime_one_right N)`. Establish `e : N + 1 = q ^ m` using `by omega`. Rewrite `hc` using `[e]`. Conclude with `Nat.Coprime.coprime_dvd_right (dvd_pow_self q hm.ne') hc`. Establish `key : ∀ s t : ℕ, s ≤ t → A.valuation (ζ ^ (q ^ s) - ζ ^ (q ^ t)) < 1 → m ∣ t - s`.

Introduce `s t hst hv`. Establish `hqst : q ^ s ≤ q ^ t` using `Nat.pow_le_pow_right (by omega) hst`. Establish `hr : (ζ ^ (q ^ t - q ^ s)) ^ N = 1` using `by rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]`. Establish `e : ζ ^ (q ^ s) - ζ ^ (q ^ t) = -(ζ ^ (q ^ s) * (ζ ^ (q ^ t - q ^ s) - 1))`. Establish `: ζ ^ (q ^ t) = ζ ^ (q ^ s) * ζ ^ (q ^ t - q ^ s)` using `by rw [← pow_add, Nat.add_sub_cancel' hqst]`.

Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Establish `hr1 : A.valuation (ζ ^ (q ^ t - q ^ s) - 1) < 1`. Rewrite `hv` using `[e, Valuation.map_neg, map_mul, map_pow, hζv, one_pow, one_mul]`. Conclude with `hv`.

Establish `hr'` using `eq_one_of_val_sub_one_lt hNv hr hr1`. Establish `hdvd : N ∣ q ^ t - q ^ s` using `(hζ.pow_eq_one_iff_dvd _).1 hr'`. Establish `hsplit : q ^ t - q ^ s = q ^ s * (q ^ (t - s) - 1)`. Rewrite using `[Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hst]`. Rewrite `hdvd` using `[hsplit]`.

Conclude with `dvd_of_pow_sub_one_dvd hq hm _ ((hcop.pow_right s).dvd_of_dvd_mul_left hdvd)`. Take `⟨a, b, hab⟩` from `(mem_Weil h).1 σ.2`. Rewrite using `[deg_eq hab]`. Establish `hc` using `hab.2 ζ (le_of_eq hζv)`. Rewrite `hc` using `[hσ]`.

Break down `le_total b a with hba | hab'` into its components or cases. Take `⟨k, hk⟩` from `key b a hba hc`. Use `⟨k, ?_⟩` and prove the remaining obligations. Establish `: a = b + m * k` using `by omega`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc' : A.valuation (ζ ^ (q ^ a) - ζ ^ (q ^ b)) < 1` using `by rwa [Valuation.map_sub_swap] at hc`. Take `⟨k, hk⟩` from `key a b hab' hc'`. Use `⟨-k, ?_⟩` and prove the remaining obligations.

Establish `: b = a + m * k` using `by omega`. Rewrite using `[this]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem dvd_deg_of_fix {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w) {m : ℕ}
    (hm : 0 < m) {ζ : Ω} (hζ : IsPrimitiveRoot ζ (normV w ^ m - 1)) (σ : Weil h) (hσ : (σ : G E Ω) ζ = ζ) :
    (m : ℤ) ∣ deg σ := by
  have hq : 1 < normV w := one_lt_normV w
  set q := normV w with hq_def
  set N := q ^ m - 1 with hN_def
  have hqm : 1 < q ^ m := Nat.one_lt_pow hm.ne' hq
  have hN0 : 0 < N := by omega
  have hqv : A.valuation (q : Ω) < 1 := by
    have := (h ((normV w : ℕ) : 𝓞 E)).2 (natCast_normV_mem w)
    simpa using this
  have hNv : A.valuation (N : Ω) = 1 := by
    rw [hN_def, Nat.cast_sub hqm.le, Nat.cast_pow, Nat.cast_one, Valuation.map_sub_eq_of_lt_right, map_one]
    rw [map_pow, map_one]; exact pow_lt_one₀ zero_le hqv hm.ne'
  have hζN : ζ ^ N = 1 := hζ.pow_eq_one
  have hζv : A.valuation ζ = 1 := val_eq_one_of_pow hN0 hζN
  have hcop : Nat.Coprime N q := by
    have hc : Nat.Coprime N (N + 1) := Nat.coprime_self_add_right.2 (Nat.coprime_one_right N)
    have e : N + 1 = q ^ m := by omega
    rw [e] at hc
    exact Nat.Coprime.coprime_dvd_right (dvd_pow_self q hm.ne') hc
  have key : ∀ s t : ℕ, s ≤ t → A.valuation (ζ ^ (q ^ s) - ζ ^ (q ^ t)) < 1 → m ∣ t - s := by
    intro s t hst hv
    have hqst : q ^ s ≤ q ^ t := Nat.pow_le_pow_right (by omega) hst
    have hr : (ζ ^ (q ^ t - q ^ s)) ^ N = 1 := by rw [← pow_mul, mul_comm, pow_mul, hζN, one_pow]
    have e : ζ ^ (q ^ s) - ζ ^ (q ^ t) = -(ζ ^ (q ^ s) * (ζ ^ (q ^ t - q ^ s) - 1)) := by
      have : ζ ^ (q ^ t) = ζ ^ (q ^ s) * ζ ^ (q ^ t - q ^ s) := by rw [← pow_add, Nat.add_sub_cancel' hqst]
      rw [this]; ring
    have hr1 : A.valuation (ζ ^ (q ^ t - q ^ s) - 1) < 1 := by
      rw [e, Valuation.map_neg, map_mul, map_pow, hζv, one_pow, one_mul] at hv; exact hv
    have hr' := eq_one_of_val_sub_one_lt hNv hr hr1
    have hdvd : N ∣ q ^ t - q ^ s := (hζ.pow_eq_one_iff_dvd _).1 hr'
    have hsplit : q ^ t - q ^ s = q ^ s * (q ^ (t - s) - 1) := by
      rw [Nat.mul_sub_one, ← pow_add, Nat.add_sub_cancel' hst]
    rw [hsplit] at hdvd
    exact dvd_of_pow_sub_one_dvd hq hm _ ((hcop.pow_right s).dvd_of_dvd_mul_left hdvd)
  obtain ⟨a, b, hab⟩ := (mem_Weil h).1 σ.2
  rw [deg_eq hab]
  have hc := hab.2 ζ (le_of_eq hζv)
  rw [hσ] at hc
  rcases le_total b a with hba | hab'
  · obtain ⟨k, hk⟩ := key b a hba hc
    refine ⟨k, ?_⟩
    have : a = b + m * k := by omega
    rw [this]; push_cast; ring
  · have hc' : A.valuation (ζ ^ (q ^ a) - ζ ^ (q ^ b)) < 1 := by rwa [Valuation.map_sub_swap] at hc
    obtain ⟨k, hk⟩ := key a b hab' hc'
    refine ⟨-k, ?_⟩
    have : b = a + m * k := by omega
    rw [this]; push_cast; ring

end Deg

section Main

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

omit [NumberField E] [IsAlgClosure E Ω] in

/- English proof (translation)
Establish `h1 : (N : Set (G E Ω)) ∈ nhds 1` using `hN.mem_nhds N.one_mem`. Take `⟨M, hM, hle⟩` from `(krullTopology_mem_nhds_one_iff E Ω _).1 h1`. Conclude with `⟨M, hM, hle⟩`.
-/
theorem exists_fd_fix_le (N : Subgroup (G E Ω)) (hN : IsOpen (N : Set (G E Ω))) :
    ∃ M : IntermediateField E Ω, FiniteDimensional E M ∧ M.fixingSubgroup ≤ N := by
  have h1 : (N : Set (G E Ω)) ∈ nhds 1 := hN.mem_nhds N.one_mem
  obtain ⟨M, hM, hle⟩ := (krullTopology_mem_nhds_one_iff E Ω _).1 h1
  exact ⟨M, hM, hle⟩

/- English proof (translation)
Take `⟨α, hα⟩` from `Field.exists_primitive_element E L`. Use `⟨α, fun σ hσ ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[IntermediateField.mem_fixingSubgroup_iff]`. Introduce `x hx`. Establish `hmem : (⟨x, hx⟩ : L) ∈ Algebra.adjoin E {α}`.

Rewrite using `[← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]`. Discharge the goal by the elementary cases of `trivial`. Rewrite `hmem` using `[Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range]`. Take `⟨f, hf⟩` from `hmem`. Establish `hx' : x = Polynomial.aeval (α : Ω) f`.

Establish `h1 : ((Polynomial.aeval α f : L) : Ω) = x` using `by rw [hf]`. Rewrite using `[← h1]`. Conclude with `(Polynomial.aeval_algHom_apply L.val α f).symm`. Rewrite using `[hx']`. Use `conv_rhs => rw [← hσ]`.

Conclude with `(Polynomial.aeval_algHom_apply (σ : Ω →ₐ[E] Ω) (α : Ω) f).symm`.
-/
theorem exists_gen (L : IntermediateField E Ω) [FiniteDimensional E L] :
    ∃ y : Ω, ∀ σ : G E Ω, σ y = y → σ ∈ L.fixingSubgroup := by
  obtain ⟨α, hα⟩ := Field.exists_primitive_element E L
  refine ⟨α, fun σ hσ ↦ ?_⟩
  rw [IntermediateField.mem_fixingSubgroup_iff]
  intro x hx
  have hmem : (⟨x, hx⟩ : L) ∈ Algebra.adjoin E {α} := by
    rw [← IntermediateField.adjoin_simple_toSubalgebra_of_isAlgebraic (Algebra.IsAlgebraic.isAlgebraic α), hα]
    trivial
  rw [Algebra.adjoin_singleton_eq_range_aeval, AlgHom.mem_range] at hmem
  obtain ⟨f, hf⟩ := hmem
  have hx' : x = Polynomial.aeval (α : Ω) f := by
    have h1 : ((Polynomial.aeval α f : L) : Ω) = x := by rw [hf]
    rw [← h1]
    exact (Polynomial.aeval_algHom_apply L.val α f).symm
  rw [hx']
  conv_rhs => rw [← hσ]
  exact (Polynomial.aeval_algHom_apply (σ : Ω →ₐ[E] Ω) (α : Ω) f).symm

/- English proof (translation)
Take `⟨O, hOo, hOV⟩` from `hV`. Use `set p := V.index with hp_def`. Establish `: IsGalois E Ω` using `inferInstance`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed E`.

Establish `: Algebra.IsAlgebraic E Ω` using `IsAlgClosure.isAlgebraic`. Take `⟨L₀, hL₀, hL₀O⟩` from `exists_fd_fix_le O hOo`. Set `L₁` to `IntermediateField.normalClosure E L₀ Ω`. Establish `: FiniteDimensional E L₁` using `inferInstance`. Establish `: IsGalois E L₁` using `inferInstance`.

Establish `hL₀L₁ : L₀ ≤ L₁` using `IntermediateField.le_normalClosure L₀`. Establish `hfixO : ∀ g : G E Ω, g ∈ L₁.fixingSubgroup → g ∈ O` using `fun g hg ↦ hL₀O (IntermediateField.fixingSubgroup_le hL₀L₁ hg)`. Set `φ : Weil h` to `frob h`. Use `set n := orderOf (AlgEquiv.restrictNormalHom L₁ (φ : G E Ω)) with hn_def`. Establish `hnpos : 0 < n` using `orderOf_pos _`.

Establish `hφn : ((φ ^ n : Weil h) : G E Ω) ∈ L₁.fixingSubgroup`. Rewrite using `[← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow, pow_orderOf_eq_one]`. Establish `hpp : 0 < p` using `hp.pos`. Establish `hq : 1 < normV w` using `one_lt_normV w`. Establish `hN1 : 1 < normV w ^ (p * n)` using `Nat.one_lt_pow (Nat.mul_pos hpp hnpos).ne' hq`.

Establish `hN0 : normV w ^ (p * n) - 1 ≠ 0` using `by omega`. Establish `: NeZero ((normV w ^ (p * n) - 1 : ℕ) : Ω)` using `⟨Nat.cast_ne_zero.2 hN0⟩`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (normV w ^ (p * n) - 1)`. Establish `: FiniteDimensional E (IntermediateField.adjoin E {ζ})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral`. Set `L₂` to `IntermediateField.normalClosure E (IntermediateField.adjoin E {ζ}) Ω`.

Set `L` to `L₁ ⊔ L₂`. Establish `: FiniteDimensional E L` using `inferInstance`. Establish `: IsGalois E L` using `inferInstance`. Establish `hζL : ζ ∈ L` using `(le_sup_right : L₂ ≤ L) (IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E ζ))`. Establish `hL₁L : L₁ ≤ L` using `le_sup_left`.

Take `⟨y, hy⟩` from `exists_gen L`. Use `hVn` as an intermediate fact. Establish `hkey : ∀ σ : Weil h, (σ : G E Ω) ∈ L.fixingSubgroup → σ ∈ V`. Introduce `σ hσ`. Establish `hσζ : (σ : G E Ω) ζ = ζ` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ hζL`.

Take `⟨s, hs⟩` from `dvd_deg_of_fix h (Nat.mul_pos hpp hnpos) hζ σ hσζ`. Set `τ : Weil h` to `((φ ^ n) ^ s) ^ p`. Establish `hτV : τ ∈ V` using `V.pow_index_mem _`. Establish `hτdeg : deg τ = deg σ`. Simplify using `only [τ, deg_pow, deg_zpow, φ, deg_frob, hs]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hτL : (τ : G E Ω) ∈ L₁.fixingSubgroup`. Simplify using `only [τ, Subgroup.coe_pow, Subgroup.coe_zpow]`. Conclude with `L₁.fixingSubgroup.pow_mem (L₁.fixingSubgroup.zpow_mem (by simpa using hφn) s) p`.

Establish `hO : ((σ * τ⁻¹ : Weil h) : G E Ω) ∈ O`. Use `hfixO _ ?_` and prove the remaining obligations. Establish `h1 : (σ : G E Ω) ∈ L₁.fixingSubgroup` using `IntermediateField.fixingSubgroup_le hL₁L hσ`. Simplify using `using L₁.fixingSubgroup.mul_mem h1 (L₁.fixingSubgroup.inv_mem hτL)`. Establish `hdeg0 : deg (σ * τ⁻¹) = 0` using `by rw [deg_mul, deg_inv, hτdeg, add_neg_cancel]`.

Use `V.mul_mem (hOV _ hdeg0 hO) hτV` as an intermediate fact. Simplify using `using this`. Set `D` to `Dec (F := E) A`. Set `M : Subgroup (G E Ω)` to `L.fixingSubgroup`. Establish `hMn : M.Normal` using `(InfiniteGalois.normal_iff_isGalois L).2 inferInstance`.

Set `π : G E Ω →* G E Ω ⧸ M` to `QuotientGroup.mk' M`. Set `Kt : Subgroup D` to `(V.map (π.comp (Weil h).subtype)).comap (π.comp D.subtype)`. Establish `hmemKt : ∀ d : D, d ∈ Kt ↔ ∃ τ ∈ V, π τ = π d`. Introduce `d`. Simplify using `[Kt, Subgroup.mem_comap, Subgroup.mem_map]`.

Establish `hMKt : ∀ d : D, (d : G E Ω) ∈ M → d ∈ Kt` using `fun d hd ↦ (hmemKt d).2 ⟨1, V.one_mem, by`. Rewrite using `[OneMemClass.coe_one, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Conclude with `hd⟩`. Establish `hWeilKt : ∀ σ : Weil h, (⟨σ, Weil_le_Dec h σ.2⟩ : D) ∈ Kt ↔ σ ∈ V`. Introduce `σ`.

Rewrite using `[hmemKt]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, hτ, hπ⟩`. Establish `hm : ((τ⁻¹ * σ : Weil h) : G E Ω) ∈ M`. Use `(QuotientGroup.eq (s := M)).1 hπ` as an intermediate fact.

Simplify using `using this`. Use `V.mul_mem hτ (hkey _ hm)` as an intermediate fact. Simplify using `using this`. Introduce `hσ`. Conclude with `⟨σ, hσ, rfl⟩`.

Establish `hdens : ∀ d : D, ∃ ρ : Weil h, π ρ = π d`. Introduce `d`. Take `⟨ρ, hρW, hρy⟩` from `GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h d d.2 y`. Use `⟨⟨ρ, hρW⟩, ?_⟩` and prove the remaining obligations. Use `show π ρ = π d`.

Rewrite using `[QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]`. Apply `hy` to reduce the goal to its premises. Rewrite using `[AlgEquiv.mul_apply, ← hρy, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Establish `hKtn : Kt.Normal`. Prove the components needed by the constructor for the conclusion.

Introduce `k hk d`. Rewrite `hk`, the goal using `[hmemKt]`. Take `⟨τ, hτ, hπ⟩` from `hk`. Take `⟨ρ, hρ⟩` from `hdens d`. Use `⟨ρ * τ * ρ⁻¹, hVn.conj_mem τ hτ ρ, ?_⟩` and prove the remaining obligations.

Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπ, hρ]`. Use `hKtn` as an intermediate fact. Set `f : Weil h →* D ⧸ Kt` to `(QuotientGroup.mk' Kt).comp (Subgroup.inclusion (Weil_le_Dec h))`. Establish `hfsurj : Function.Surjective f`. Introduce `q`.

Take `⟨d, rfl⟩` from `QuotientGroup.mk'_surjective Kt q`. Take `⟨ρ, hρ⟩` from `hdens d`. Use `⟨ρ, ?_⟩` and prove the remaining obligations. Use `show (QuotientGroup.mk' Kt) (Subgroup.inclusion _ ρ) = QuotientGroup.mk' Kt d`. Rewrite using `[QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]`.

Use `hMKt _ ?_` and prove the remaining obligations. Use `(QuotientGroup.eq (s := M)).1 hρ` as an intermediate fact. Simplify using `using this`. Establish `hfker : f.ker = V`. Use extensionality with `σ`.

Rewrite using `[MonoidHom.mem_ker]`. Use `show QuotientGroup.mk' Kt (Subgroup.inclusion _ σ) = 1 ↔ σ ∈ V`. Rewrite using `[QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Conclude with `hWeilKt σ`. Establish `hcard : Nat.card (D ⧸ Kt) = p`.

Establish `: Nat.card (D ⧸ Kt) = f.ker.index` using `(Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv).symm`. Rewrite using `[this, hfker]`. Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `: NeZero p` using `⟨hp.ne_zero⟩`. Set `e : D ⧸ Kt ≃* rootsOfUnity p ℂ` to `mulEquivOfPrimeCardEq hcard (Complex.card_rootsOfUnity p)`.

Set `χ : D →* ℂˣ` to `(rootsOfUnity p ℂ).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Kt))`. Establish `hχ : ∀ d : D, χ d = 1 ↔ d ∈ Kt`. Introduce `d`. Simplify using `only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom, OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]`. Use `⟨y, χ, fun d hd ↦ (hχ d).2 (hMKt d (hy _ hd)), fun σ ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[hχ]`. Conclude with `(hWeilKt σ).symm`.
-/
theorem exists_localChar {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    (V : Subgroup (Weil h)) (hVn : V.Normal) (hp : V.index.Prime) (hV : SmoothSub V) :
    ∃ (y : Ω) (χ : Dec (F := E) A →* ℂˣ), (∀ d : Dec (F := E) A, (d : G E Ω) y = y → χ d = 1) ∧
      ∀ σ : Weil h, σ ∈ V ↔ χ ⟨σ, Weil_le_Dec h σ.2⟩ = 1 := by
  classical
  obtain ⟨O, hOo, hOV⟩ := hV
  set p := V.index with hp_def
  have : IsGalois E Ω := inferInstance
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed E
  have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
  obtain ⟨L₀, hL₀, hL₀O⟩ := exists_fd_fix_le O hOo
  let L₁ := IntermediateField.normalClosure E L₀ Ω
  have : FiniteDimensional E L₁ := inferInstance
  have : IsGalois E L₁ := inferInstance
  have hL₀L₁ : L₀ ≤ L₁ := IntermediateField.le_normalClosure L₀
  have hfixO : ∀ g : G E Ω, g ∈ L₁.fixingSubgroup → g ∈ O := fun g hg ↦
    hL₀O (IntermediateField.fixingSubgroup_le hL₀L₁ hg)

  let φ : Weil h := frob h
  set n := orderOf (AlgEquiv.restrictNormalHom L₁ (φ : G E Ω)) with hn_def
  have hnpos : 0 < n := orderOf_pos _
  have hφn : ((φ ^ n : Weil h) : G E Ω) ∈ L₁.fixingSubgroup := by
    rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, Subgroup.coe_pow, map_pow,
      pow_orderOf_eq_one]

  have hpp : 0 < p := hp.pos
  have hq : 1 < normV w := one_lt_normV w
  have hN1 : 1 < normV w ^ (p * n) := Nat.one_lt_pow (Nat.mul_pos hpp hnpos).ne' hq
  have hN0 : normV w ^ (p * n) - 1 ≠ 0 := by omega
  have : NeZero ((normV w ^ (p * n) - 1 : ℕ) : Ω) := ⟨Nat.cast_ne_zero.2 hN0⟩
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (normV w ^ (p * n) - 1)
  have : FiniteDimensional E (IntermediateField.adjoin E {ζ}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic ζ).isIntegral
  let L₂ := IntermediateField.normalClosure E (IntermediateField.adjoin E {ζ}) Ω
  let L := L₁ ⊔ L₂
  have : FiniteDimensional E L := inferInstance
  have : IsGalois E L := inferInstance
  have hζL : ζ ∈ L := (le_sup_right : L₂ ≤ L)
    (IntermediateField.le_normalClosure _ (IntermediateField.mem_adjoin_simple_self E ζ))
  have hL₁L : L₁ ≤ L := le_sup_left
  obtain ⟨y, hy⟩ := exists_gen L

  have := hVn
  have hkey : ∀ σ : Weil h, (σ : G E Ω) ∈ L.fixingSubgroup → σ ∈ V := by
    intro σ hσ
    have hσζ : (σ : G E Ω) ζ = ζ := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hσ ζ hζL
    obtain ⟨s, hs⟩ := dvd_deg_of_fix h (Nat.mul_pos hpp hnpos) hζ σ hσζ
    let τ : Weil h := ((φ ^ n) ^ s) ^ p
    have hτV : τ ∈ V := V.pow_index_mem _
    have hτdeg : deg τ = deg σ := by
      simp only [τ, deg_pow, deg_zpow, φ, deg_frob, hs]
      push_cast; ring
    have hτL : (τ : G E Ω) ∈ L₁.fixingSubgroup := by
      simp only [τ, Subgroup.coe_pow, Subgroup.coe_zpow]
      exact L₁.fixingSubgroup.pow_mem (L₁.fixingSubgroup.zpow_mem (by simpa using hφn) s) p
    have hO : ((σ * τ⁻¹ : Weil h) : G E Ω) ∈ O := by
      refine hfixO _ ?_
      have h1 : (σ : G E Ω) ∈ L₁.fixingSubgroup := IntermediateField.fixingSubgroup_le hL₁L hσ
      simpa using L₁.fixingSubgroup.mul_mem h1 (L₁.fixingSubgroup.inv_mem hτL)
    have hdeg0 : deg (σ * τ⁻¹) = 0 := by rw [deg_mul, deg_inv, hτdeg, add_neg_cancel]
    have := V.mul_mem (hOV _ hdeg0 hO) hτV
    simpa using this

  let D := Dec (F := E) A
  let M : Subgroup (G E Ω) := L.fixingSubgroup
  have hMn : M.Normal := (InfiniteGalois.normal_iff_isGalois L).2 inferInstance
  let π : G E Ω →* G E Ω ⧸ M := QuotientGroup.mk' M
  let Kt : Subgroup D := (V.map (π.comp (Weil h).subtype)).comap (π.comp D.subtype)
  have hmemKt : ∀ d : D, d ∈ Kt ↔ ∃ τ ∈ V, π τ = π d := by
    intro d
    simp [Kt, Subgroup.mem_comap, Subgroup.mem_map]
  have hMKt : ∀ d : D, (d : G E Ω) ∈ M → d ∈ Kt := fun d hd ↦
    (hmemKt d).2 ⟨1, V.one_mem, by
      rw [OneMemClass.coe_one, map_one, eq_comm, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]; exact hd⟩
  have hWeilKt : ∀ σ : Weil h, (⟨σ, Weil_le_Dec h σ.2⟩ : D) ∈ Kt ↔ σ ∈ V := by
    intro σ
    rw [hmemKt]
    constructor
    · rintro ⟨τ, hτ, hπ⟩
      have hm : ((τ⁻¹ * σ : Weil h) : G E Ω) ∈ M := by
        have := (QuotientGroup.eq (s := M)).1 hπ
        simpa using this
      have := V.mul_mem hτ (hkey _ hm)
      simpa using this
    · intro hσ
      exact ⟨σ, hσ, rfl⟩
  have hdens : ∀ d : D, ∃ ρ : Weil h, π ρ = π d := by
    intro d
    obtain ⟨ρ, hρW, hρy⟩ := GlobalTheory.T.weilGroupAtPlace_dense_in_decompositionGroup E Ω A w h d d.2 y
    refine ⟨⟨ρ, hρW⟩, ?_⟩
    show π ρ = π d
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    apply hy
    rw [AlgEquiv.mul_apply, ← hρy, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
  have hKtn : Kt.Normal := by
    constructor
    intro k hk d
    rw [hmemKt] at hk ⊢
    obtain ⟨τ, hτ, hπ⟩ := hk
    obtain ⟨ρ, hρ⟩ := hdens d
    refine ⟨ρ * τ * ρ⁻¹, hVn.conj_mem τ hτ ρ, ?_⟩
    simp only [Subgroup.coe_mul, Subgroup.coe_inv, map_mul, map_inv, hπ, hρ]
  have := hKtn
  let f : Weil h →* D ⧸ Kt := (QuotientGroup.mk' Kt).comp (Subgroup.inclusion (Weil_le_Dec h))
  have hfsurj : Function.Surjective f := by
    intro q
    obtain ⟨d, rfl⟩ := QuotientGroup.mk'_surjective Kt q
    obtain ⟨ρ, hρ⟩ := hdens d
    refine ⟨ρ, ?_⟩
    show (QuotientGroup.mk' Kt) (Subgroup.inclusion _ ρ) = QuotientGroup.mk' Kt d
    rw [QuotientGroup.mk'_apply, QuotientGroup.mk'_apply, QuotientGroup.eq]
    refine hMKt _ ?_
    have := (QuotientGroup.eq (s := M)).1 hρ
    simpa using this
  have hfker : f.ker = V := by
    ext σ
    rw [MonoidHom.mem_ker]
    show QuotientGroup.mk' Kt (Subgroup.inclusion _ σ) = 1 ↔ σ ∈ V
    rw [QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
    exact hWeilKt σ
  have hcard : Nat.card (D ⧸ Kt) = p := by
    have : Nat.card (D ⧸ Kt) = f.ker.index :=
      (Nat.card_congr (QuotientGroup.quotientKerEquivOfSurjective f hfsurj).toEquiv).symm
    rw [this, hfker]
  have : Fact p.Prime := ⟨hp⟩
  have : NeZero p := ⟨hp.ne_zero⟩
  let e : D ⧸ Kt ≃* rootsOfUnity p ℂ := mulEquivOfPrimeCardEq hcard (Complex.card_rootsOfUnity p)
  let χ : D →* ℂˣ := (rootsOfUnity p ℂ).subtype.comp (e.toMonoidHom.comp (QuotientGroup.mk' Kt))
  have hχ : ∀ d : D, χ d = 1 ↔ d ∈ Kt := by
    intro d
    simp only [χ, MonoidHom.comp_apply, Subgroup.coe_subtype, MulEquiv.coe_toMonoidHom,
      OneMemClass.coe_eq_one, MulEquiv.map_eq_one_iff, QuotientGroup.mk'_apply, QuotientGroup.eq_one_iff]
  refine ⟨y, χ, fun d hd ↦ (hχ d).2 (hMKt d (hy _ hd)), fun σ ↦ ?_⟩
  rw [hχ]
  exact (hWeilKt σ).symm

end Main

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension.Loc

namespace PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

open ComplexConjugate

section Local

variable {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]

/- English proof (translation)
The claim follows from `Loc.exists_localChar h V hVn hp hV`.
-/
theorem exists_localChar {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} (h : IsPlaceOver A w)
    (V : Subgroup (Weil h)) (hVn : V.Normal) (hp : V.index.Prime) (hV : SmoothSub V) :
    ∃ (y : Ω) (χ : Dec (F := E) A →* ℂˣ), (∀ d : Dec (F := E) A, (d : G E Ω) y = y → χ d = 1) ∧
      ∀ σ : Weil h, σ ∈ V ↔ χ ⟨σ, Weil_le_Dec h σ.2⟩ = 1 :=
  Loc.exists_localChar h V hVn hp hV

end Local

section SlopeTestRemainingChoices

/- English proof (translation)
Set `F` to `maximalRealSubfield E`. Establish `: IsAlgClosure F Ω` using `IsAlgClosure.ofAlgebraic F E Ω`. Establish `: IsGalois E Ω` using `inferInstance`. Set `Nc : ClosedSubgroup (G E Ω)` to `⟨N, N.isClosed_of_isOpen hNo⟩`. Set `M` to `IntermediateField.fixedField N`.

Establish `hfixN : M.fixingSubgroup = N` using `InfiniteGalois.fixingSubgroup_fixedField Nc`. Establish `: FiniteDimensional E M` using `(InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfixN]; exact hNo)`. Establish `: IsGalois E M` using `(InfiniteGalois.normal_iff_isGalois _).1 (by rw [hfixN]; exact hN)`. Establish `hfib : ∀ t : HeightOneSpectrum (𝓞 F), {v : HeightOneSpectrum (𝓞 E) | v.under (𝓞 F) = t}.Finite`. Introduce `t`.

Establish `: t.asIdeal.IsMaximal` using `t.isMaximal`. Establish `hP` using `IsDedekindDomain.primesOver_finite t.asIdeal (𝓞 E)`. Use `(hP.preimage (f := fun v : HeightOneSpectrum (𝓞 E) ↦ v.asIdeal) (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)).subset ?_` and prove the remaining obligations. Introduce `v hv`. Simplify using `only [Set.mem_ofPred_eq] at hv`.

Use `⟨v.isPrime, ⟨?_⟩⟩` and prove the remaining obligations. Rewrite using `[← hv]`. Both sides reduce to the same expression. Set `SE : Set (HeightOneSpectrum (𝓞 E))` to `(fun v ↦ v.under (𝓞 F)) ⁻¹' S0`. Establish `hSE : SE.Finite` using `hS0.preimage' (fun t _ ↦ hfib t)`.

Establish `: Finite (G E Ω ⧸ N)` using `Subgroup.quotient_finite_of_isOpen _ hNo`. Establish `: Fintype (G E Ω ⧸ N)` using `Fintype.ofFinite _`. Establish `hch` using `fun q : G E Ω ⧸ N ↦ GlobalTheory.T.chebotarev_degree_one E Ω M (AlgEquiv.restrictNormalHom M q.out) SE hSE`. Use `choose v hvS _ B hB _ σ hσ hσg using hch`. Set `T : Finset (HeightOneSpectrum (𝓞 F))` to `Finset.univ.image (fun q ↦ (v q).under (𝓞 F))`.

Set `Bt : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω` to `fun t ↦ if h : ∃ q, (v q).under (𝓞 F) = t then B h.choose else ⊤`. Establish `hBt : ∀ q, IsPlaceOver (Bt ((v q).under (𝓞 F))) ((v q).under (𝓞 F))`. Introduce `q`. Establish `hex : ∃ q', (v q').under (𝓞 F) = (v q).under (𝓞 F)` using `⟨q, rfl⟩`. Simplify using `only [Bt, dif_pos hex]`.

Use `isPlaceOver_under (F := F) (hB hex.choose)` as an intermediate fact. Rewrite `this` using `[hex.choose_spec]`. Then use the resulting hypothesis. Use `⟨T, Bt, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 ht`.

Conclude with `hvS q`. Introduce `t ht`. Take `⟨q, -, rfl⟩` from `Finset.mem_image.1 ht`. Conclude with `hBt q`. Introduce `g`.

Set `q : G E Ω ⧸ N` to `g`. Use `⟨(v q).under (𝓞 F), Finset.mem_image_of_mem _ (Finset.mem_univ q), σ q, ?_, ?_⟩` and prove the remaining obligations. Establish `h1' : (q.out)⁻¹ * σ q ∈ M.fixingSubgroup`. Rewrite using `[← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hσg q, inv_mul_cancel]`. Establish `h1 : (q.out)⁻¹ * σ q ∈ N` using `hfixN.le h1'`.

Establish `h2 : g⁻¹ * q.out ∈ N` using `(QuotientGroup.eq (s := N)).1 (show (g : G E Ω ⧸ N) = (q.out : G E Ω ⧸ N) from (QuotientGroup.out_eq' q).symm)`. Establish `h3 : g⁻¹ * σ q ∈ N` using `by simpa [mul_assoc] using N.mul_mem h2 h1`. Use `hN.conj_mem _ h3 g` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Take `⟨τ, hτ⟩` from `exists_smul_eq_of_isPlaceOver (hBt q) (isPlaceOver_under (F := F) (hB q))`.

Use `⟨τ, ?_⟩` and prove the remaining obligations. Establish `hd : res F (σ q) • B q = B q` using `res_mem_decompositionSubgroup F (hσ q).1`. Use `show (τ⁻¹ * res F (σ q) * τ) • Bt _ = Bt _`. Rewrite using `[mul_smul, mul_smul, hτ, hd, ← hτ, inv_smul_smul]`.
-/
theorem exists_finite_part_one_idele_split_congruence_quotient {E Ω : Type} [Field E] [NumberField E] [IsCMField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    (N : Subgroup (G E Ω)) (hN : N.Normal) (hNo : IsOpen (N : Set (G E Ω)))
    (S0 : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield E)))) (hS0 : S0.Finite) :
    ∃ (T : Finset (HeightOneSpectrum (𝓞 (maximalRealSubfield E))))
      (B : HeightOneSpectrum (𝓞 (maximalRealSubfield E)) → ValuationSubring Ω),
      (∀ t ∈ T, t ∉ S0) ∧ (∀ t ∈ T, IsPlaceOver (B t) t) ∧
      ∀ g : G E Ω, ∃ t ∈ T, ∃ σ : G E Ω, σ * g⁻¹ ∈ N ∧ ∃ τ : G (maximalRealSubfield E) Ω,
        τ⁻¹ * res (maximalRealSubfield E) σ * τ ∈ Dec (F := maximalRealSubfield E) (B t) := by
  classical
  let F := maximalRealSubfield E
  have : IsAlgClosure F Ω := IsAlgClosure.ofAlgebraic F E Ω
  have : IsGalois E Ω := inferInstance
  let Nc : ClosedSubgroup (G E Ω) := ⟨N, N.isClosed_of_isOpen hNo⟩
  let M := IntermediateField.fixedField N
  have hfixN : M.fixingSubgroup = N := InfiniteGalois.fixingSubgroup_fixedField Nc
  have : FiniteDimensional E M := (InfiniteGalois.isOpen_iff_finite _).1 (by rw [hfixN]; exact hNo)
  have : IsGalois E M := (InfiniteGalois.normal_iff_isGalois _).1 (by rw [hfixN]; exact hN)

  have hfib : ∀ t : HeightOneSpectrum (𝓞 F), {v : HeightOneSpectrum (𝓞 E) | v.under (𝓞 F) = t}.Finite := by
    intro t
    have : t.asIdeal.IsMaximal := t.isMaximal
    have hP := IsDedekindDomain.primesOver_finite t.asIdeal (𝓞 E)
    refine (hP.preimage (f := fun v : HeightOneSpectrum (𝓞 E) ↦ v.asIdeal)
      (fun a _ b _ hab ↦ HeightOneSpectrum.ext hab)).subset ?_
    intro v hv
    simp only [Set.mem_ofPred_eq] at hv
    refine ⟨v.isPrime, ⟨?_⟩⟩
    rw [← hv]
    rfl
  let SE : Set (HeightOneSpectrum (𝓞 E)) := (fun v ↦ v.under (𝓞 F)) ⁻¹' S0
  have hSE : SE.Finite := hS0.preimage' (fun t _ ↦ hfib t)
  have : Finite (G E Ω ⧸ N) := Subgroup.quotient_finite_of_isOpen _ hNo
  have : Fintype (G E Ω ⧸ N) := Fintype.ofFinite _
  have hch := fun q : G E Ω ⧸ N ↦ GlobalTheory.T.chebotarev_degree_one E Ω M (AlgEquiv.restrictNormalHom M q.out) SE hSE
  choose v hvS _ B hB _ σ hσ hσg using hch
  let T : Finset (HeightOneSpectrum (𝓞 F)) := Finset.univ.image (fun q ↦ (v q).under (𝓞 F))
  let Bt : HeightOneSpectrum (𝓞 F) → ValuationSubring Ω := fun t ↦
    if h : ∃ q, (v q).under (𝓞 F) = t then B h.choose else ⊤
  have hBt : ∀ q, IsPlaceOver (Bt ((v q).under (𝓞 F))) ((v q).under (𝓞 F)) := by
    intro q
    have hex : ∃ q', (v q').under (𝓞 F) = (v q).under (𝓞 F) := ⟨q, rfl⟩
    simp only [Bt, dif_pos hex]
    have := isPlaceOver_under (F := F) (hB hex.choose)
    rwa [hex.choose_spec] at this
  refine ⟨T, Bt, ?_, ?_, ?_⟩
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact hvS q
  · intro t ht
    obtain ⟨q, -, rfl⟩ := Finset.mem_image.1 ht
    exact hBt q
  · intro g
    let q : G E Ω ⧸ N := g
    refine ⟨(v q).under (𝓞 F), Finset.mem_image_of_mem _ (Finset.mem_univ q), σ q, ?_, ?_⟩
    · have h1' : (q.out)⁻¹ * σ q ∈ M.fixingSubgroup := by
        rw [← IntermediateField.restrictNormalHom_ker, MonoidHom.mem_ker, map_mul, map_inv, hσg q,
          inv_mul_cancel]
      have h1 : (q.out)⁻¹ * σ q ∈ N := hfixN.le h1'
      have h2 : g⁻¹ * q.out ∈ N :=
        (QuotientGroup.eq (s := N)).1 (show (g : G E Ω ⧸ N) = (q.out : G E Ω ⧸ N) from (QuotientGroup.out_eq' q).symm)
      have h3 : g⁻¹ * σ q ∈ N := by simpa [mul_assoc] using N.mul_mem h2 h1
      have := hN.conj_mem _ h3 g
      simpa [mul_assoc] using this
    · obtain ⟨τ, hτ⟩ := exists_smul_eq_of_isPlaceOver (hBt q) (isPlaceOver_under (F := F) (hB q))
      refine ⟨τ, ?_⟩
      have hd : res F (σ q) • B q = B q := res_mem_decompositionSubgroup F (hσ q).1
      show (τ⁻¹ * res F (σ q) * τ) • Bt _ = Bt _
      rw [mul_smul, mul_smul, hτ, hd, ← hτ, inv_smul_smul]

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `hK1 E Ω _ _ _ _ _ _ A w h hs V hVn hp hV N hN hNo`. Set `F` to `maximalRealSubfield E`. Establish `: IsAlgClosure F Ω` using `IsAlgClosure.ofAlgebraic F E Ω`. Establish `hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x` using `fun x hx ↦ hx.tower_top`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap E Ω).injective`.

Establish `: IsGalois F Ω` using `inferInstance`. Establish `: IsGalois E Ω` using `inferInstance`. Establish `h2 : Module.finrank F E = 2` using `Algebra.IsQuadraticExtension.finrank_eq_two F E`. Take `⟨y, χ, hχy, hχV⟩` from `exists_localChar h V hVn hp hV`. Establish `hfix` using `fix_of_mem_dec h hs`.

Establish `hliftDec : ∀ g : Dec (F` using `F) A, liftE F g.1 (hfix g.1 g.2) ∈ Dec (F := E) A := by`. Introduce `g`. Establish `h1 : (g.1 : Ω ≃ₐ[F] Ω) • A = A` using `g.2`. Use `show liftE F g.1 (hfix g.1 g.2) • A = A`. Rewrite using `[← res_smul F, res_liftE]`.

Conclude with `h1`. Set `χF : Dec (F` to `F) A →* ℂˣ := { toFun := fun g ↦ χ ⟨liftE F g.1 (hfix g.1 g.2), hliftDec g⟩ map_one' := by`. Rewrite using `[← map_one χ]`. Conclude with `congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl))`. Use the proof step `map_mul' := fun a b ↦ by`.

Rewrite using `[← map_mul χ]`. Conclude with `congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)) }`. Establish `hχF : ∀ σ : Weil h, ∀ hm : res F (σ : G E Ω) ∈ Dec (F` using `F) A, χF ⟨res F (σ : G E Ω), hm⟩ = χ ⟨σ, Weil_le_Dec h σ.2⟩ := fun σ hm ↦ congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl))`. Establish `hχFo : IsOpen (χF.ker : Set (Dec (F` using `F) A)) := by`. Set `Oy : Subgroup (G F Ω)` to `(IntermediateField.adjoin F {y}).fixingSubgroup`.

Establish `: Algebra.IsAlgebraic F Ω` using `IsAlgClosure.isAlgebraic`. Establish `: FiniteDimensional F (IntermediateField.adjoin F {y})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral`. Establish `hOy : IsOpen (Oy : Set (G F Ω))` using `IntermediateField.fixingSubgroup_isOpen _`. Use `Subgroup.isOpen_mono (H₁ := Oy.subgroupOf (Dec (F := F) A)) ?_ (hOy.preimage continuous_subtype_val)` and prove the remaining obligations. Introduce `g hg`.

Rewrite `hg` using `[Subgroup.mem_subgroupOf]`. Establish `hgy : (g : G F Ω) y = y` using `(IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y (IntermediateField.mem_adjoin_simple_self F y)`. Conclude with `hχy _ hgy`. Take `⟨T, B, hT0, hTB, hcov⟩` from `exists_finite_part_one_idele_split_congruence_quotient N hN hNo {w.under (𝓞 F)} (Set.finite_singleton _)`. Set `S` to `Option T`.

Set `v : S → HeightOneSpectrum (𝓞 F)` to `fun s ↦ s.elim (w.under (𝓞 F)) (fun t ↦ t.1)`. Set `AA : S → ValuationSubring Ω` to `fun s ↦ s.elim A (fun t ↦ B t.1)`. Establish `hvinj : Function.Injective v`. Introduce and unpack `(_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) hab`. Both sides reduce to the same expression.

Conclude with `absurd hab.symm (hT0 b hb)`. Conclude with `absurd hab (hT0 a ha)`. Simplify using `only [v, Option.elim_some] at hab`. Substitute `hab` using the available equality. Both sides reduce to the same expression.

Establish `hAA : ∀ s, IsPlaceOver (AA s) (v s)`. Introduce and unpack `(_ | ⟨a, ha⟩)`. Conclude with `isPlaceOver_under h`. Conclude with `hTB a ha`. Set `χs : ∀ s, Dec (F` to `F) (AA s) →* ℂˣ := fun s ↦ match s with`.

Consider the case `none => χF`. Consider the case `some _ => 1`. Establish `hχso : ∀ s, IsOpen ((χs s).ker : Set (Dec (F` using `F) (AA s))) := by`. Introduce and unpack `(_ | ⟨a, ha⟩)`. Conclude with `hχFo`.

Use `show IsOpen (((1 : Dec (F := F) (B a) →* ℂˣ).ker : Subgroup _) : Set (Dec (F := F) (B a)))`. Rewrite using `[MonoidHom.ker_one, Subgroup.coe_top]`. Conclude with `isOpen_univ`. Take `⟨ψ, hψo, hψloc, hψc⟩` from `hK1 F Ω S v AA hvinj hAA χs hχso`. Establish `hψA : ∀ g : Dec (F` using `F) A, ψ g = χF g := fun g ↦ hψloc none g`.

Establish `hψB : ∀ t ∈ T, ∀ g ∈ Dec (F` using `F) (B t), ψ g = 1 := fun t ht g hg ↦ hψloc (some ⟨t, ht⟩) ⟨g, hg⟩`. Establish `hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ ψ.ker` using `fun c j hcj ↦ hψc _ (IsTotallyReal.isReal _) c ⟨j, hcj, rfl⟩`. Set `H : Subgroup (G E Ω)` to `ψ.ker.comap (res F (E := E) (Ω := Ω))`. Establish `hmemH : ∀ σ : G E Ω, σ ∈ H ↔ ψ (res F σ) = 1` using `fun σ ↦ Iff.rfl`. Use `⟨H, ⟨inferInstance, hψo.preimage (continuous_res F hint), ?_, ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hfin : Finite (G F Ω ⧸ ψ.ker)` using `Subgroup.quotient_finite_of_isOpen _ hψo`. Set `φ : G E Ω →* ℂˣ` to `ψ.comp (res F)`. Establish `: Finite ψ.range` using `Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv`. Establish `: Finite φ.range` using `Finite.Set.subset (ψ.range : Set ℂˣ) (fun x ⟨g, hg⟩ ↦ ⟨res F g, hg⟩)`. Take `⟨z, hz⟩` from `IsCyclic.exists_generator (α := φ.range)`.

Take `⟨g₀, hg₀⟩` from `z.2`. Use `⟨g₀, ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨k, hk⟩` from `Subgroup.mem_zpowers_iff.1 (hz ⟨φ g, g, rfl⟩)`.

Establish `hφk : φ (g₀ ^ k) = φ g`. Rewrite using `[map_zpow, hg₀]`. Simplify using `using congrArg Subtype.val hk`. Establish `hgk : g * (g₀ ^ k)⁻¹ ∈ H` using `by show φ (g * (g₀ ^ k)⁻¹) = 1`. Rewrite using `[map_mul, map_inv, hφk, mul_inv_cancel]`.

Use `Subgroup.mul_mem_sup hgk (Subgroup.zpow_mem_zpowers g₀ k)` as an intermediate fact. Simplify using `using this`. Introduce `L hL`. Set `Hp : Subgroup (G F Ω)` to `ψ.ker ⊔ L.fixingSubgroup.map (res F (E := E) (Ω := Ω))`. Establish `hcomap : Hp.comap (res F (E` using `E) (Ω := Ω)) = L.fixingSubgroup := by`.

Use extensionality with `σ`. Prove the components needed by the constructor for the conclusion. Introduce `hσ`. Take `⟨a, ha, b, hb, hab⟩` from `Subgroup.mem_sup_of_normal_left.1 (Subgroup.mem_comap.1 hσ)`. Take `⟨τ, hτ, rfl⟩` from `Subgroup.mem_map.1 hb`.

Establish `hres : res F (σ * τ⁻¹) = a` using `by rw [map_mul, map_inv, ← hab, mul_inv_cancel_right]`. Establish `hστ : σ * τ⁻¹ ∈ H` using `by rw [hmemH, hres]; exact (MonoidHom.mem_ker).1 ha`. Use `L.fixingSubgroup.mul_mem (hL hστ) hτ` as an intermediate fact. Simplify using `using this`. Introduce `hσ`.

Conclude with `Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hσ))`. Set `Y : IntermediateField F Ω` to `(⊥ : IntermediateField E Ω).restrictScalars F`. Establish `hYE : ∀ e : E, algebraMap E Ω e ∈ Y` using `fun e ↦ (⊥ : IntermediateField E Ω).algebraMap_mem e`. Establish `: Algebra.IsAlgebraic E Ω` using `IsAlgClosure.isAlgebraic`. Establish `: Algebra.IsAlgebraic ℚ Ω` using `Algebra.IsAlgebraic.trans ℚ E Ω`.

Set `j : Ω →+* ℂ` to `(IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ).toRingHom`. Establish `hjF : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x)`. Introduce `x`. Establish `hr` using `IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))`. Rewrite `hr` using `[InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff]`.

Simplify `RingHom.congr_fun hr x` using `[ComplexEmbedding.conjugate_coe_eq]`. Take `⟨c, hcj⟩` from `exists_conj j hjF`. Establish `hcE : ∃ e : E, c (algebraMap E Ω e) ≠ algebraMap E Ω e` using `by by_contra! hce`. Apply `IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap E Ω))` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `e`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq]`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← hcj, hce e]`. Establish `hsup : Hp ⊔ Y.fixingSubgroup = ⊤`.

Rewrite using `[eq_top_iff]`. Introduce `g _`. Distinguish the cases in `hg : ∀ e : E, g (algebraMap E Ω e) = algebraMap E Ω e`. Use `Subgroup.mem_sup_right ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_)` and prove the remaining obligations. Take `⟨e, rfl⟩` from `IntermediateField.mem_bot.1 (show x ∈ (⊥ : IntermediateField E Ω) from hx)`.

Conclude with `hg e`. Use `push Not at hg`. Establish `hce` using `eq_on_of_not_fix h2 hcE hg`. Establish `h1 : c⁻¹ * g ∈ Y.fixingSubgroup`. Use `(IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_` and prove the remaining obligations.

Take `⟨e, rfl⟩` from `IntermediateField.mem_bot.1 (show x ∈ (⊥ : IntermediateField E Ω) from hx)`. Rewrite using `[AlgEquiv.mul_apply, ← hce e, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]`. Use `Subgroup.mul_mem_sup (Subgroup.mem_sup_left (hc c j hcj) : c ∈ Hp) h1` as an intermediate fact. Simplify using `using this`. Take `⟨-, hcm⟩` from `cm_of_descend F Hp (Subgroup.isOpen_mono le_sup_left hψo) (fun c j hcj ↦ Subgroup.mem_sup_left (hc c j hcj)) Y hYE hsup`.

Rewrite `hcm` using `[hcomap, InfiniteGalois.fixedField_fixingSubgroup]`. Conclude with `hcm`. Rewrite using `[eq_top_iff]`. Introduce `g _`. Take `⟨t, ht, σ, hσN, τ, hτ⟩` from `hcov g`.

Establish `hσH : σ ∈ H`. Rewrite using `[hmemH]`. Establish `h1` using `hψB t ht _ hτ`. Rewrite `h1` using `[map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul]`. Conclude with `h1`.

Establish `hgN : σ⁻¹ * g ∈ N`. Use `hN.conj_mem _ (N.inv_mem hσN) σ⁻¹` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `Subgroup.mul_mem_sup hσH hgN` as an intermediate fact. Simplify using `using this`.

Introduce `σ`. Establish `hm : res F (σ : G E Ω) ∈ Dec (F` using `F) A := res_mem_decompositionSubgroup F (Weil_le_Dec h σ.2)`. Rewrite using `[hχV σ, hmemH, ← hχF σ hm, ← hψA ⟨_, hm⟩]`.
-/
theorem cyclic_cm_extension_prescribed_weil : CyclicCMExtensionExists := by
  intro hK1 E Ω _ _ _ _ _ _ A w h hs V hVn hp hV N hN hNo
  classical
  let F := maximalRealSubfield E
  have : IsAlgClosure F Ω := IsAlgClosure.ofAlgebraic F E Ω
  have hint : ∀ x : Ω, IsIntegral F x → IsIntegral E x := fun x hx ↦ hx.tower_top
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap E Ω).injective
  have : IsGalois F Ω := inferInstance
  have : IsGalois E Ω := inferInstance
  have h2 : Module.finrank F E = 2 := Algebra.IsQuadraticExtension.finrank_eq_two F E

  obtain ⟨y, χ, hχy, hχV⟩ := exists_localChar h V hVn hp hV
  have hfix := fix_of_mem_dec h hs
  have hliftDec : ∀ g : Dec (F := F) A, liftE F g.1 (hfix g.1 g.2) ∈ Dec (F := E) A := by
    intro g
    have h1 : (g.1 : Ω ≃ₐ[F] Ω) • A = A := g.2
    show liftE F g.1 (hfix g.1 g.2) • A = A
    rw [← res_smul F, res_liftE]
    exact h1
  let χF : Dec (F := F) A →* ℂˣ :=
    { toFun := fun g ↦ χ ⟨liftE F g.1 (hfix g.1 g.2), hliftDec g⟩
      map_one' := by
        rw [← map_one χ]
        exact congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl))
      map_mul' := fun a b ↦ by
        rw [← map_mul χ]
        exact congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl)) }
  have hχF : ∀ σ : Weil h, ∀ hm : res F (σ : G E Ω) ∈ Dec (F := F) A,
      χF ⟨res F (σ : G E Ω), hm⟩ = χ ⟨σ, Weil_le_Dec h σ.2⟩ := fun σ hm ↦
    congrArg χ (Subtype.ext (AlgEquiv.ext fun _ ↦ rfl))
  have hχFo : IsOpen (χF.ker : Set (Dec (F := F) A)) := by
    let Oy : Subgroup (G F Ω) := (IntermediateField.adjoin F {y}).fixingSubgroup
    have : Algebra.IsAlgebraic F Ω := IsAlgClosure.isAlgebraic
    have : FiniteDimensional F (IntermediateField.adjoin F {y}) :=
      IntermediateField.adjoin.finiteDimensional (Algebra.IsAlgebraic.isAlgebraic y).isIntegral
    have hOy : IsOpen (Oy : Set (G F Ω)) := IntermediateField.fixingSubgroup_isOpen _
    refine Subgroup.isOpen_mono (H₁ := Oy.subgroupOf (Dec (F := F) A)) ?_ (hOy.preimage continuous_subtype_val)
    intro g hg
    rw [Subgroup.mem_subgroupOf] at hg
    have hgy : (g : G F Ω) y = y :=
      (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg y (IntermediateField.mem_adjoin_simple_self F y)
    exact hχy _ hgy

  obtain ⟨T, B, hT0, hTB, hcov⟩ := exists_finite_part_one_idele_split_congruence_quotient N hN hNo {w.under (𝓞 F)} (Set.finite_singleton _)
  let S := Option T
  let v : S → HeightOneSpectrum (𝓞 F) := fun s ↦ s.elim (w.under (𝓞 F)) (fun t ↦ t.1)
  let AA : S → ValuationSubring Ω := fun s ↦ s.elim A (fun t ↦ B t.1)
  have hvinj : Function.Injective v := by
    rintro (_ | ⟨a, ha⟩) (_ | ⟨b, hb⟩) hab
    · rfl
    · exact absurd hab.symm (hT0 b hb)
    · exact absurd hab (hT0 a ha)
    · simp only [v, Option.elim_some] at hab
      subst hab; rfl
  have hAA : ∀ s, IsPlaceOver (AA s) (v s) := by
    rintro (_ | ⟨a, ha⟩)
    · exact isPlaceOver_under h
    · exact hTB a ha
  let χs : ∀ s, Dec (F := F) (AA s) →* ℂˣ := fun s ↦ match s with
    | none => χF
    | some _ => 1
  have hχso : ∀ s, IsOpen ((χs s).ker : Set (Dec (F := F) (AA s))) := by
    rintro (_ | ⟨a, ha⟩)
    · exact hχFo
    · show IsOpen (((1 : Dec (F := F) (B a) →* ℂˣ).ker : Subgroup _) : Set (Dec (F := F) (B a)))
      rw [MonoidHom.ker_one, Subgroup.coe_top]
      exact isOpen_univ
  obtain ⟨ψ, hψo, hψloc, hψc⟩ := hK1 F Ω S v AA hvinj hAA χs hχso
  have hψA : ∀ g : Dec (F := F) A, ψ g = χF g := fun g ↦ hψloc none g
  have hψB : ∀ t ∈ T, ∀ g ∈ Dec (F := F) (B t), ψ g = 1 := fun t ht g hg ↦ hψloc (some ⟨t, ht⟩) ⟨g, hg⟩
  have hc : ∀ (c : Ω ≃ₐ[F] Ω) (j : Ω →+* ℂ), (∀ x, j (c x) = conj (j x)) → c ∈ ψ.ker := fun c j hcj ↦
    hψc _ (IsTotallyReal.isReal _) c ⟨j, hcj, rfl⟩
  let H : Subgroup (G E Ω) := ψ.ker.comap (res F (E := E) (Ω := Ω))
  have hmemH : ∀ σ : G E Ω, σ ∈ H ↔ ψ (res F σ) = 1 := fun σ ↦ Iff.rfl
  refine ⟨H, ⟨inferInstance, hψo.preimage (continuous_res F hint), ?_, ?_⟩, ?_, ?_⟩
  ·
    have hfin : Finite (G F Ω ⧸ ψ.ker) := Subgroup.quotient_finite_of_isOpen _ hψo
    let φ : G E Ω →* ℂˣ := ψ.comp (res F)
    have : Finite ψ.range := Finite.of_equiv _ (QuotientGroup.quotientKerEquivRange ψ).toEquiv
    have : Finite φ.range := Finite.Set.subset (ψ.range : Set ℂˣ) (fun x ⟨g, hg⟩ ↦ ⟨res F g, hg⟩)
    obtain ⟨z, hz⟩ := IsCyclic.exists_generator (α := φ.range)
    obtain ⟨g₀, hg₀⟩ := z.2
    refine ⟨g₀, ?_⟩
    rw [eq_top_iff]
    intro g _
    obtain ⟨k, hk⟩ := Subgroup.mem_zpowers_iff.1 (hz ⟨φ g, g, rfl⟩)
    have hφk : φ (g₀ ^ k) = φ g := by
      rw [map_zpow, hg₀]
      simpa using congrArg Subtype.val hk
    have hgk : g * (g₀ ^ k)⁻¹ ∈ H := by
      show φ (g * (g₀ ^ k)⁻¹) = 1
      rw [map_mul, map_inv, hφk, mul_inv_cancel]
    have := Subgroup.mul_mem_sup hgk (Subgroup.zpow_mem_zpowers g₀ k)
    simpa using this
  ·
    intro L hL
    let Hp : Subgroup (G F Ω) := ψ.ker ⊔ L.fixingSubgroup.map (res F (E := E) (Ω := Ω))
    have hcomap : Hp.comap (res F (E := E) (Ω := Ω)) = L.fixingSubgroup := by
      ext σ
      constructor
      · intro hσ
        obtain ⟨a, ha, b, hb, hab⟩ := Subgroup.mem_sup_of_normal_left.1 (Subgroup.mem_comap.1 hσ)
        obtain ⟨τ, hτ, rfl⟩ := Subgroup.mem_map.1 hb
        have hres : res F (σ * τ⁻¹) = a := by rw [map_mul, map_inv, ← hab, mul_inv_cancel_right]
        have hστ : σ * τ⁻¹ ∈ H := by rw [hmemH, hres]; exact (MonoidHom.mem_ker).1 ha
        have := L.fixingSubgroup.mul_mem (hL hστ) hτ
        simpa using this
      · intro hσ
        exact Subgroup.mem_comap.2 (Subgroup.mem_sup_right (Subgroup.mem_map_of_mem _ hσ))
    let Y : IntermediateField F Ω := (⊥ : IntermediateField E Ω).restrictScalars F
    have hYE : ∀ e : E, algebraMap E Ω e ∈ Y := fun e ↦ (⊥ : IntermediateField E Ω).algebraMap_mem e
    have : Algebra.IsAlgebraic E Ω := IsAlgClosure.isAlgebraic
    have : Algebra.IsAlgebraic ℚ Ω := Algebra.IsAlgebraic.trans ℚ E Ω
    let j : Ω →+* ℂ := (IsAlgClosed.lift : Ω →ₐ[ℚ] ℂ).toRingHom
    have hjF : ∀ x : F, conj (j (algebraMap F Ω x)) = j (algebraMap F Ω x) := by
      intro x
      have hr := IsTotallyReal.isReal (InfinitePlace.mk (j.comp (algebraMap F Ω)))
      rw [InfinitePlace.isReal_mk_iff, ComplexEmbedding.isReal_iff] at hr
      simpa [ComplexEmbedding.conjugate_coe_eq] using RingHom.congr_fun hr x
    obtain ⟨c, hcj⟩ := exists_conj j hjF
    have hcE : ∃ e : E, c (algebraMap E Ω e) ≠ algebraMap E Ω e := by
      by_contra! hce
      apply IsTotallyComplex.complexEmbedding_not_isReal (j.comp (algebraMap E Ω))
      rw [ComplexEmbedding.isReal_iff]
      ext e
      rw [ComplexEmbedding.conjugate_coe_eq]
      simp only [RingHom.comp_apply]
      rw [← hcj, hce e]
    have hsup : Hp ⊔ Y.fixingSubgroup = ⊤ := by
      rw [eq_top_iff]
      intro g _
      by_cases hg : ∀ e : E, g (algebraMap E Ω e) = algebraMap E Ω e
      · refine Subgroup.mem_sup_right ((IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_)
        obtain ⟨e, rfl⟩ := IntermediateField.mem_bot.1 (show x ∈ (⊥ : IntermediateField E Ω) from hx)
        exact hg e
      · push Not at hg
        have hce := eq_on_of_not_fix h2 hcE hg
        have h1 : c⁻¹ * g ∈ Y.fixingSubgroup := by
          refine (IntermediateField.mem_fixingSubgroup_iff _ _).2 fun x hx ↦ ?_
          obtain ⟨e, rfl⟩ := IntermediateField.mem_bot.1 (show x ∈ (⊥ : IntermediateField E Ω) from hx)
          rw [AlgEquiv.mul_apply, ← hce e, ← AlgEquiv.mul_apply, inv_mul_cancel, AlgEquiv.one_apply]
        have := Subgroup.mul_mem_sup (Subgroup.mem_sup_left (hc c j hcj) : c ∈ Hp) h1
        simpa using this
    obtain ⟨-, hcm⟩ := cm_of_descend F Hp (Subgroup.isOpen_mono le_sup_left hψo)
      (fun c j hcj ↦ Subgroup.mem_sup_left (hc c j hcj)) Y hYE hsup
    rw [hcomap, InfiniteGalois.fixedField_fixingSubgroup] at hcm
    exact hcm
  ·
    rw [eq_top_iff]
    intro g _
    obtain ⟨t, ht, σ, hσN, τ, hτ⟩ := hcov g
    have hσH : σ ∈ H := by
      rw [hmemH]
      have h1 := hψB t ht _ hτ
      rw [map_mul, map_mul, mul_comm, ← mul_assoc, ← map_mul, mul_inv_cancel, map_one, one_mul] at h1
      exact h1
    have hgN : σ⁻¹ * g ∈ N := by
      have := hN.conj_mem _ (N.inv_mem hσN) σ⁻¹
      simpa [mul_assoc] using this
    have := Subgroup.mul_mem_sup hσH hgN
    simpa using this
  ·
    intro σ
    have hm : res F (σ : G E Ω) ∈ Dec (F := F) A := res_mem_decompositionSubgroup F (Weil_le_Dec h σ.2)
    rw [hχV σ, hmemH, ← hχF σ hm, ← hψA ⟨_, hm⟩]

end PositivityTheory.Pf1.CLGD.K.CyclicCMExtension

namespace PositivityTheory.Pf1.CLGD.K

/- English proof (translation)
The claim follows from `CyclicCMExtension.cyclic_cm_extension_prescribed_weil`.
-/
theorem cyclic_cm_extension_prescribed_weil : CyclicCMExtensionExists := CyclicCMExtension.cyclic_cm_extension_prescribed_weil

end PositivityTheory.Pf1.CLGD.K
