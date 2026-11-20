import Mathlib
import GroundTheory.AutomorphicForms.AutomorphicFormSpaces

open NumberField MeasureTheory Topology Set Filter IsDedekindDomain
open scoped NumberField.AdeleRing

namespace GroundTheory.Automorphic

noncomputable section

namespace FourierWhittaker

set_option linter.unusedSectionVars false

variable (K : Type*) [Field K] [NumberField K] (ι : Type*) [Fintype ι]

abbrev vecMeasure : Measure (ι → 𝔸[K]) := Measure.pi fun _ => GroundTheory.Global.adeleMeasure K

def vecDomain : Set (ι → 𝔸[K]) := Set.univ.pi fun _ => GroundTheory.Global.fundamentalSet K

def vecLattice : AddSubgroup (ι → 𝔸[K]) :=
  (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom ι).range

variable {K ι}

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_vecLattice {x : ι → 𝔸[K]} :
    x ∈ vecLattice K ι ↔ ∃ ξ : ι → K, (fun i => algebraMap K 𝔸[K] (ξ i)) = x :=
  Iff.rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨ξ, rfl⟩`.
-/
theorem algebraMap_mem_vecLattice (ξ : ι → K) :
    (fun i => algebraMap K 𝔸[K] (ξ i)) ∈ vecLattice K ι :=
  ⟨ξ, rfl⟩

instance countable_vecLattice : Countable (vecLattice K ι) := by
  have := GroundTheory.Global.countable_numberField K
  have e : (vecLattice K ι : Set (ι → 𝔸[K])) =
      Set.range (AddMonoidHom.compLeft (algebraMap K 𝔸[K]).toAddMonoidHom ι) :=
    AddMonoidHom.coe_range _
  have hc : (vecLattice K ι : Set (ι → 𝔸[K])).Countable := e ▸ Set.countable_range _
  exact hc.to_subtype

/- English proof (translation)
The claim follows from `MeasurableSet.univ_pi fun _ => GroundTheory.Global.measurableSet_fundamentalSet K`.
-/
theorem measurableSet_vecDomain : MeasurableSet (vecDomain K ι) :=
  MeasurableSet.univ_pi fun _ => GroundTheory.Global.measurableSet_fundamentalSet K

/- English proof (translation)
Use `choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)`. Use `⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, ?_, ?_⟩` and prove the remaining obligations. Introduce `p _`. Express the relevant statement in the definitionally equal form `algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K`. Rewrite using `[map_neg, neg_add_eq_sub]`.

Conclude with `hk p`. Introduce and unpack `⟨_, ξ, rfl⟩ h`. Use `Subtype.ext (funext fun p => ?_)` and prove the remaining obligations. Establish `hp : algebraMap K 𝔸[K] (ξ p) + X p ∈ GroundTheory.Global.fundamentalSet K` using `h p (mem_univ p)`. Establish `: -ξ p = k p` using `huniq p (-ξ p) (by show X p - algebraMap K 𝔸[K] (-ξ p) ∈ GroundTheory.Global.fundamentalSet K`.

Rewrite using `[map_neg, sub_neg_eq_add, add_comm])` and apply the resulting hypothesis. Express the relevant statement in the definitionally equal form `algebraMap K 𝔸[K] (ξ p) = algebraMap K 𝔸[K] (-k p)`. Rewrite using `[← this, neg_neg]`.
-/
theorem existsUnique_vadd_mem_vecDomain (X : ι → 𝔸[K]) :
    ∃! g : vecLattice K ι, g +ᵥ X ∈ vecDomain K ι := by
  classical
  choose k hk huniq using fun p => GroundTheory.Global.existsUnique_sub_mem_fundamentalSet K (X p)
  refine ⟨⟨fun p => algebraMap K 𝔸[K] (-k p), fun p => -k p, rfl⟩, ?_, ?_⟩
  · intro p _
    change algebraMap K 𝔸[K] (-k p) + X p ∈ GroundTheory.Global.fundamentalSet K
    rw [map_neg, neg_add_eq_sub]
    exact hk p
  · rintro ⟨_, ξ, rfl⟩ h
    refine Subtype.ext (funext fun p => ?_)
    have hp : algebraMap K 𝔸[K] (ξ p) + X p ∈ GroundTheory.Global.fundamentalSet K := h p (mem_univ p)
    have : -ξ p = k p := huniq p (-ξ p) (by
      show X p - algebraMap K 𝔸[K] (-ξ p) ∈ GroundTheory.Global.fundamentalSet K
      rwa [map_neg, sub_neg_eq_add, add_comm])
    change algebraMap K 𝔸[K] (ξ p) = algebraMap K 𝔸[K] (-k p)
    rw [← this, neg_neg]

/- English proof (translation)
The claim follows from `IsAddFundamentalDomain.mk' measurableSet_vecDomain.nullMeasurableSet existsUnique_vadd_mem_vecDomain`.
-/
theorem isAddFundamentalDomain_vecDomain :
    IsAddFundamentalDomain (vecLattice K ι) (vecDomain K ι) (vecMeasure K ι) :=
  IsAddFundamentalDomain.mk' measurableSet_vecDomain.nullMeasurableSet
    existsUnique_vadd_mem_vecDomain

/- English proof (translation)
Rewrite using `[vecMeasure, vecDomain, Measure.pi_pi]`. Simplify using `[GroundTheory.Global.adeleMeasure_fundamentalSet]`.
-/
theorem vecMeasure_vecDomain : vecMeasure K ι (vecDomain K ι) = 1 := by
  rw [vecMeasure, vecDomain, Measure.pi_pi]
  simp [GroundTheory.Global.adeleMeasure_fundamentalSet]

/- English proof (translation)
Use `⟨Set.univ.pi fun _ => closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)), isCompact_univ_pi fun _ => (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod (GroundTheory.Globa …` and prove the remaining obligations. Introduce `X hX p _`. Conclude with `⟨subset_closure (hX p (mem_univ p)).1, (hX p (mem_univ p)).2⟩`.
-/
theorem exists_isCompact_superset_vecDomain :
    ∃ C, IsCompact C ∧ vecDomain K ι ⊆ C := by
  refine ⟨Set.univ.pi fun _ => closure (GroundTheory.Global.fundamentalSetInfinite K) ×ˢ
    (GroundTheory.Global.integralFiniteAdeles (𝓞 K) K : Set (FiniteAdeleRing (𝓞 K) K)),
    isCompact_univ_pi fun _ => (GroundTheory.Global.isCompact_closure_fundamentalSetInfinite K).prod
      (GroundTheory.Global.isCompact_integralFiniteAdeles K), ?_⟩
  intro X hX p _
  exact ⟨subset_closure (hX p (mem_univ p)).1, (hX p (mem_univ p)).2⟩

/- English proof (translation)
Take `⟨C, hC, hDC⟩` from `exists_isCompact_superset_vecDomain (K := K) (ι := ι)`. Conclude with `hC.closure_of_subset hDC`.
-/
theorem isCompact_closure_vecDomain : IsCompact (closure (vecDomain K ι)) := by
  obtain ⟨C, hC, hDC⟩ := exists_isCompact_superset_vecDomain (K := K) (ι := ι)
  exact hC.closure_of_subset hDC

/- English proof (translation)
Use `set μ := vecMeasure K ι`. Use `set D := vecDomain K ι`. Set `Te : (ι → 𝔸[K]) ≃ₜ (ι → 𝔸[K])` to `{ toEquiv := T.toEquiv, continuous_toFun := hT, continuous_invFun := hT' }`. Establish `hme : MeasurableEmbedding Te` using `Te.measurableEmbedding`. Use `set ν := μ.map Te`.

Establish `: ν.IsAddHaarMeasure` using `T.isAddHaarMeasure_map μ hT hT'`. Establish `himage : T '' D = Te '' D` using `rfl`. Establish `hcl : IsCompact (closure (T '' D))` using `(isCompact_closure_vecDomain.image hT).closure_of_subset (image_mono subset_closure)`. Establish `hνTD : ν (T '' D) = 1`. Rewrite using `[himage, hme.map_apply, Te.preimage_image, vecMeasure_vecDomain]`.

Establish `hμTD : μ (T '' D) = 1`. Rewrite using `[hTD.measure_eq isAddFundamentalDomain_vecDomain, vecMeasure_vecDomain]`. Establish `hscal : ∀ s ⊆ T '' D, ν s = ν.addHaarScalarFactor μ • μ s` using `fun s hs => Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ (hcl.closure_of_subset (hs.trans subset_closure))`. Establish `hc1 : (ν.addHaarScalarFactor μ : ENNReal) = 1`. Use `hscal _ subset_rfl` as an intermediate fact.

Rewrite `this` using `[hνTD, hμTD, ENNReal.smul_def, smul_eq_mul, mul_one]`. Conclude with `this.symm`. Establish `hc : ∀ s ⊆ T '' D, ν s = μ s` using `fun s hs => by`. Rewrite using `[hscal s hs, ENNReal.smul_def, smul_eq_mul, hc1, one_mul]`. Establish `hres : ν.restrict (T '' D) = μ.restrict (T '' D)`.

Use extensionality with `A hA`. Rewrite using `[Measure.restrict_apply hA, Measure.restrict_apply hA]`. Conclude with `hc _ inter_subset_right`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Te.preimage_image]`.

Both sides reduce to the same expression. Use `_ = ∫ y in Te '' D, f y ∂ν := (hme.setIntegral_map f _).symm`. Use `_ = ∫ y in T '' D, f y ∂μ := by rw [← himage, hres]`. Use `_ = ∫ x in D, f x ∂μ := hTD.setIntegral_eq isAddFundamentalDomain_vecDomain fun g x => hf g g.2 x`.
-/
theorem setIntegral_comp_addEquiv (T : (ι → 𝔸[K]) ≃+ (ι → 𝔸[K])) (hT : Continuous T)
    (hT' : Continuous T.symm)
    (hTD : IsAddFundamentalDomain (vecLattice K ι) (T '' vecDomain K ι) (vecMeasure K ι))
    {f : (ι → 𝔸[K]) → ℂ} (hf : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) :
    ∫ x in vecDomain K ι, f (T x) ∂vecMeasure K ι = ∫ x in vecDomain K ι, f x ∂vecMeasure K ι := by
  set μ := vecMeasure K ι
  set D := vecDomain K ι
  let Te : (ι → 𝔸[K]) ≃ₜ (ι → 𝔸[K]) :=
    { toEquiv := T.toEquiv, continuous_toFun := hT, continuous_invFun := hT' }
  have hme : MeasurableEmbedding Te := Te.measurableEmbedding
  set ν := μ.map Te
  have : ν.IsAddHaarMeasure := T.isAddHaarMeasure_map μ hT hT'
  have himage : T '' D = Te '' D := rfl
  have hcl : IsCompact (closure (T '' D)) :=
    (isCompact_closure_vecDomain.image hT).closure_of_subset (image_mono subset_closure)
  have hνTD : ν (T '' D) = 1 := by
    rw [himage, hme.map_apply, Te.preimage_image, vecMeasure_vecDomain]
  have hμTD : μ (T '' D) = 1 := by
    rw [hTD.measure_eq isAddFundamentalDomain_vecDomain, vecMeasure_vecDomain]
  have hscal : ∀ s ⊆ T '' D, ν s = ν.addHaarScalarFactor μ • μ s := fun s hs =>
    Measure.measure_isAddInvariant_eq_smul_of_isCompact_closure ν μ
      (hcl.closure_of_subset (hs.trans subset_closure))
  have hc1 : (ν.addHaarScalarFactor μ : ENNReal) = 1 := by
    have := hscal _ subset_rfl
    rw [hνTD, hμTD, ENNReal.smul_def, smul_eq_mul, mul_one] at this
    exact this.symm
  have hc : ∀ s ⊆ T '' D, ν s = μ s := fun s hs => by
    rw [hscal s hs, ENNReal.smul_def, smul_eq_mul, hc1, one_mul]
  have hres : ν.restrict (T '' D) = μ.restrict (T '' D) := by
    ext A hA
    rw [Measure.restrict_apply hA, Measure.restrict_apply hA]
    exact hc _ inter_subset_right
  calc ∫ x in D, f (T x) ∂μ = ∫ x in Te ⁻¹' (Te '' D), f (Te x) ∂μ := by
        rw [Te.preimage_image]; rfl
    _ = ∫ y in Te '' D, f y ∂ν := (hme.setIntegral_map f _).symm
    _ = ∫ y in T '' D, f y ∂μ := by rw [← himage, hres]
    _ = ∫ x in D, f x ∂μ :=
        hTD.setIntegral_eq isAddFundamentalDomain_vecDomain fun g x => hf g g.2 x

/- English proof (translation)
Establish `himg : T '' vecDomain K ι = T.symm ⁻¹' vecDomain K ι` using `T.toEquiv.image_eq_preimage_symm _`. Establish `hL' : ∀ y, y ∈ vecLattice K ι ↔ T.symm y ∈ vecLattice K ι` using `fun y => by`. Rewrite using `[hL (T.symm y), AddEquiv.apply_symm_apply]`. Use `IsAddFundamentalDomain.mk' ?_ fun x => ?_` and prove the remaining obligations. Rewrite using `[himg]`.

Conclude with `(measurableSet_vecDomain.preimage hT'.measurable).nullMeasurableSet`. Take `⟨g, hg, huniq⟩` from `existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) (T.symm x)`. Use `⟨⟨T g, (hL g).1 g.2⟩, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[himg]`. Express the relevant statement in the definitionally equal form `T.symm (T g + x) ∈ vecDomain K ι`.

Rewrite using `[map_add, AddEquiv.symm_apply_apply]`. Conclude with `hg`. Introduce `g' hg'`. Rewrite `hg'` using `[himg]`. Express the relevant statement in the definitionally equal form `T.symm (g' + x) ∈ vecDomain K ι at hg'`.

Rewrite `hg'` using `[map_add]`. Use `huniq ⟨T.symm g', (hL' g').1 g'.2⟩ hg'` as an intermediate fact. Use `Subtype.ext ?_` and prove the remaining obligations. Rewrite using `[← this]`. Simplify using the standard rewrite rules.
-/
theorem isAddFundamentalDomain_image_of_map_vecLattice (T : (ι → 𝔸[K]) ≃+ (ι → 𝔸[K]))
    (hT' : Continuous T.symm) (hL : ∀ x, x ∈ vecLattice K ι ↔ T x ∈ vecLattice K ι) :
    IsAddFundamentalDomain (vecLattice K ι) (T '' vecDomain K ι) (vecMeasure K ι) := by
  have himg : T '' vecDomain K ι = T.symm ⁻¹' vecDomain K ι := T.toEquiv.image_eq_preimage_symm _
  have hL' : ∀ y, y ∈ vecLattice K ι ↔ T.symm y ∈ vecLattice K ι := fun y => by
    rw [hL (T.symm y), AddEquiv.apply_symm_apply]
  refine IsAddFundamentalDomain.mk' ?_ fun x => ?_
  · rw [himg]
    exact (measurableSet_vecDomain.preimage hT'.measurable).nullMeasurableSet
  · obtain ⟨g, hg, huniq⟩ := existsUnique_vadd_mem_vecDomain (K := K) (ι := ι) (T.symm x)
    refine ⟨⟨T g, (hL g).1 g.2⟩, ?_, ?_⟩
    · rw [himg]
      change T.symm (T g + x) ∈ vecDomain K ι
      rw [map_add, AddEquiv.symm_apply_apply]
      exact hg
    · intro g' hg'
      rw [himg] at hg'
      change T.symm (g' + x) ∈ vecDomain K ι at hg'
      rw [map_add] at hg'
      have := huniq ⟨T.symm g', (hL' g').1 g'.2⟩ hg'
      refine Subtype.ext ?_
      rw [← this]
      simp

section Mat

variable [DecidableEq ι]

def matVec (M : Matrix ι ι K) (x : ι → 𝔸[K]) : ι → 𝔸[K] :=
  (M.map (algebraMap K 𝔸[K])).mulVec x

/- English proof (translation)
Simplify using `[matVec, Matrix.mulVec, dotProduct]`.
-/
theorem matVec_apply (M : Matrix ι ι K) (x : ι → 𝔸[K]) (i : ι) :
    matVec M x i = ∑ j, algebraMap K 𝔸[K] (M i j) * x j := by
  simp [matVec, Matrix.mulVec, dotProduct]

/- English proof (translation)
The claim follows from `Matrix.mulVec_add _ _ _`.
-/
theorem matVec_add (M : Matrix ι ι K) (x y : ι → 𝔸[K]) :
    matVec M (x + y) = matVec M x + matVec M y :=
  Matrix.mulVec_add _ _ _

/- English proof (translation)
Simplify using `[matVec, Matrix.map_mul, Matrix.mulVec_mulVec]`.
-/
theorem matVec_mul (M N : Matrix ι ι K) (x : ι → 𝔸[K]) :
    matVec (M * N) x = matVec M (matVec N x) := by
  simp [matVec, Matrix.map_mul, Matrix.mulVec_mulVec]

/- English proof (translation)
Simplify using `[matVec]`.
-/
theorem matVec_one (x : ι → 𝔸[K]) : matVec (1 : Matrix ι ι K) x = x := by
  simp [matVec]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[matVec_apply, Matrix.mulVec, dotProduct, map_sum]`.
-/
theorem matVec_algebraMap (M : Matrix ι ι K) (ξ : ι → K) :
    matVec M (fun i => algebraMap K 𝔸[K] (ξ i)) = fun i => algebraMap K 𝔸[K] (M.mulVec ξ i) := by
  funext i
  simp [matVec_apply, Matrix.mulVec, dotProduct, map_sum]

/- English proof (translation)
Use `continuous_pi fun i => ?_` and prove the remaining obligations. Repeatedly rewrite using `[matVec_apply]`. Conclude with `continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)`.
-/
theorem continuous_matVec (M : Matrix ι ι K) : Continuous (matVec M) := by
  refine continuous_pi fun i => ?_
  simp_rw [matVec_apply]
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (continuous_apply j)

def matEquiv (M : GL ι K) : (ι → 𝔸[K]) ≃+ (ι → 𝔸[K]) where
  toFun := matVec (M : Matrix ι ι K)
  invFun := matVec ((M⁻¹ : GL ι K) : Matrix ι ι K)
  left_inv x := by rw [← matVec_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, matVec_one]
  right_inv x := by rw [← matVec_mul, ← Matrix.GeneralLinearGroup.coe_mul, mul_inv_cancel,
    Matrix.GeneralLinearGroup.coe_one, matVec_one]
  map_add' := matVec_add _

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem matEquiv_apply (M : GL ι K) (x : ι → 𝔸[K]) :
    matEquiv M x = matVec (M : Matrix ι ι K) x := rfl

/- English proof (translation)
Take `⟨ξ, hξ⟩` from `mem_vecLattice.1 hx`. Rewrite using `[← hξ, matVec_algebraMap]`. Conclude with `algebraMap_mem_vecLattice _`.
-/
theorem matVec_mem_vecLattice (M : Matrix ι ι K) {x : ι → 𝔸[K]} (hx : x ∈ vecLattice K ι) :
    matVec M x ∈ vecLattice K ι := by
  obtain ⟨ξ, hξ⟩ := mem_vecLattice.1 hx
  rw [← hξ, matVec_algebraMap]
  exact algebraMap_mem_vecLattice _

/- English proof (translation)
Use `setIntegral_comp_addEquiv (matEquiv M) (continuous_matVec _) (continuous_matVec _) ?_ hf` and prove the remaining obligations. Use `isAddFundamentalDomain_image_of_map_vecLattice _ (continuous_matVec _) fun x => ⟨fun hx => matVec_mem_vecLattice _ hx, fun hx => ?_⟩` and prove the remaining obligations. Use `matVec_mem_vecLattice ((M⁻¹ : GL ι K) : Matrix ι ι K) hx` as an intermediate fact. Rewrite `this` using `[matEquiv_apply, ← matVec_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel, Matrix.GeneralLinearGroup.coe_one, matVec_one]`. Then use the resulting hypothesis.
-/
theorem setIntegral_comp_matVec (M : GL ι K) {f : (ι → 𝔸[K]) → ℂ}
    (hf : ∀ ξ ∈ vecLattice K ι, ∀ x, f (ξ + x) = f x) :
    ∫ x in vecDomain K ι, f (matVec (M : Matrix ι ι K) x) ∂vecMeasure K ι =
      ∫ x in vecDomain K ι, f x ∂vecMeasure K ι := by
  refine setIntegral_comp_addEquiv (matEquiv M) (continuous_matVec _) (continuous_matVec _) ?_ hf
  refine isAddFundamentalDomain_image_of_map_vecLattice _ (continuous_matVec _) fun x => ⟨fun hx =>
    matVec_mem_vecLattice _ hx, fun hx => ?_⟩
  have := matVec_mem_vecLattice ((M⁻¹ : GL ι K) : Matrix ι ι K) hx
  rwa [matEquiv_apply, ← matVec_mul, ← Matrix.GeneralLinearGroup.coe_mul, inv_mul_cancel,
    Matrix.GeneralLinearGroup.coe_one, matVec_one] at this

end Mat

end FourierWhittaker

end

end GroundTheory.Automorphic
