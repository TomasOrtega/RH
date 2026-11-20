import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalMassOrder.Development
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdelicLocalCompactness.AdeleLC

noncomputable section

namespace LocMassOrdSF

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub Formalism.L2.SG.Measures Formalism.L2.SG.LocVol MeasureTheory
  NumberField IsDedekindDomain Topology Matrix
open scoped TensorProduct

section FvTop

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Establish `: Countable F` using `(Module.finBasis ℚ F).equivFun.injective.countable`. Establish `: TopologicalSpace.SeparableSpace (Fv F v)` using `⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _, IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩`. Conclude with `UniformSpace.secondCountable_of_separable (Fv F v)`.
-/
theorem secondCountable_Fv : SecondCountableTopology (Fv F v) := by
  have : Countable F := (Module.finBasis ℚ F).equivFun.injective.countable
  have : TopologicalSpace.SeparableSpace (Fv F v) :=
    ⟨⟨Set.range (algebraMap F (Fv F v)), Set.countable_range _,
      IsDedekindDomain.HeightOneSpectrum.denseRange_algebraMap F v⟩⟩
  exact UniformSpace.secondCountable_of_separable (Fv F v)

/- English proof (translation)
The claim follows from `(PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))`.
-/
theorem locallyCompact_Fv : LocallyCompactSpace (Fv F v) :=
  (PI.AdicCompletionValuation.isCompact_adicCompletionIntegers F v).locallyCompactSpace_of_mem_nhds_of_addGroup
    ((Valued.isOpen_valuationSubring _).mem_nhds (zero_mem _))

/- English proof (translation)
Simplify using `only [isUnit_iff_ne_zero]`. Conclude with `isOpen_ne`.
-/
theorem isOpen_units_Fv : IsOpen {r : Fv F v | IsUnit r} := by
  simp only [isUnit_iff_ne_zero]
  exact isOpen_ne

end FvTop

section Tens

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Assemble the required witnesses or components as `⟨rfl⟩`.
-/
theorem isModTop_tens : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩

attribute [local instance] isModTop_tens

/- English proof (translation)
The claim follows from `IsModuleTopology.isTopologicalRing R _`.
-/
theorem isTopRing_tens : IsTopologicalRing (R ⊗[F] E) :=
  IsModuleTopology.isTopologicalRing R _

attribute [local instance] isTopRing_tens

/- English proof (translation)
Set `e` to `(Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun`. Conclude with `⟨Fin (Module.finrank F E), inferInstance, ⟨{ toEquiv := e.toEquiv continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩⟩`.
-/
theorem exists_homeomorph_tens :
    ∃ (ι : Type) (_ : Fintype ι), Nonempty (R ⊗[F] E ≃ₜ (ι → R)) := by
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  exact ⟨Fin (Module.finrank F E), inferInstance,
    ⟨{ toEquiv := e.toEquiv
       continuous_toFun := IsModuleTopology.continuous_of_linearMap e.toLinearMap
       continuous_invFun := IsModuleTopology.continuous_of_linearMap e.symm.toLinearMap }⟩⟩

/- English proof (translation)
Take `⟨ι, hι, ⟨h⟩⟩` from `exists_homeomorph_tens (F := F) (E := E) R`. Conclude with `h.isClosedEmbedding.locallyCompactSpace`.
-/
theorem lc_tens [LocallyCompactSpace R] [T2Space R] : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace

/- English proof (translation)
Take `⟨ι, hι, ⟨h⟩⟩` from `exists_homeomorph_tens (F := F) (E := E) R`. Conclude with `h.isEmbedding.t2Space`.
-/
theorem t2_tensor_product [T2Space R] : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isEmbedding.t2Space

/- English proof (translation)
Take `⟨ι, hι, ⟨h⟩⟩` from `exists_homeomorph_tens (F := F) (E := E) R`. Conclude with `h.isInducing.secondCountableTopology`.
-/
theorem sc_tens [SecondCountableTopology R] : SecondCountableTopology (R ⊗[F] E) := by
  obtain ⟨ι, hι, ⟨h⟩⟩ := exists_homeomorph_tens (F := F) (E := E) R
  exact h.isInducing.secondCountableTopology

end Tens

section Free

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

/- English proof (translation)
Introduce `m n _ _ _ _ W hW`. Establish `hker : LinearMap.ker (Matrix.mulVecLin W) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `c hc`. Conclude with `hW c hc`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin W) hker`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin W) = 1`. Rewrite using `[hg, LinearMap.toMatrix'_id]`. Rewrite `h1` using `[LinearMap.toMatrix'_comp, show LinearMap.toMatrix' (Matrix.mulVecLin W) = W from LinearMap.toMatrix'_toLin' W]`. Then use the resulting hypothesis.
-/
theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hker : LinearMap.ker (Matrix.mulVecLin W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c hc
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.mulVecLin W) hker
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : LinearMap.toMatrix' (g ∘ₗ Matrix.mulVecLin W) = 1 := by
    rw [hg, LinearMap.toMatrix'_id]
  rwa [LinearMap.toMatrix'_comp,
    show LinearMap.toMatrix' (Matrix.mulVecLin W) = W from LinearMap.toMatrix'_toLin' W] at h1

/- English proof (translation)
Establish `h1 : (P * W) *ᵥ c = 0`. Rewrite using `[← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).mpr hP`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hu, Units.inv_mul, Matrix.one_mulVec]`.

Use `_ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]`.
-/
theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by
    rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).mpr hP
  calc c = ((↑u⁻¹ : Matrix n n R) * (P * W)) *ᵥ c := by
        rw [← hu, Units.inv_mul, Matrix.one_mulVec]
    _ = 0 := by rw [← Matrix.mulVec_mulVec, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, wMat, crd, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  simp only [Matrix.mulVec, dotProduct, wMat, crd, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul,
    Finsupp.coe_finset_sum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul, Fintype.sum_prod_type]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => ?_
  ring

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h j`. Apply `(Algebra.TensorProduct.basis R b).repr.injective` to reduce the goal to its premises. Use extensionality with `l`. Establish `h1` using `congrFun h (j, l)`.

Rewrite `h1` using `[wMat_mulVec]`. Simplify `h1` using `[crd]`. Introduce `h`. Use function extensionality and compare the values at `q`. Take `⟨j, l⟩` from `q`.

Rewrite using `[wMat_mulVec, h j]`. Simplify using `[crd]`.
-/
theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have h1 := congrFun h (j, l)
    rw [wMat_mulVec] at h1
    simpa [crd] using h1
  · intro h
    funext q
    obtain ⟨j, l⟩ := q
    rw [wMat_mulVec, h j]
    simp [crd]

/- English proof (translation)
Set `B` to `Algebra.TensorProduct.basis R b`. Establish `hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k` using `fun k => Algebra.TensorProduct.basis_apply b k`. Establish `hsum : ∀ g : Fin a → R ⊗[F] E, (∑ i, g i • X i = 0) ↔ ∀ j, ∑ i, g i * X i j = 0`. Introduce `g`. Prove the components needed by the constructor for the conclusion.

Introduce `h j`. Establish `h1` using `congrFun h j`. Simplify `h1` using `[Finset.sum_apply]`. Introduce `h`. Use function extensionality and compare the values at `j`.

Simplify `h j` using `[Finset.sum_apply]`. Rewrite using `[Fintype.linearIndependent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hli c hc`. Rewrite `hc` using `[wMat_mulVec_eq_zero]`.

Establish `h0` using `hli (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) ((hsum _).mpr hc)`. Use function extensionality and compare the values at `q`. Take `⟨i, k⟩` from `q`. Establish `h0' : (∑ k, c (i, k) • B k) = 0`. Establish `h3` using `h0 i`.

Simplify `h3` using `[hBk]`. Establish `h2 : ⇑(B.repr (∑ k, c (i, k) • B k)) = fun k => c (i, k)` using `B.repr_sum_self _`. Rewrite `h2` using `[h0', map_zero]`. Simplify using `using (congrFun h2 k).symm`. Introduce `h g hg i`.

Set `c : Fin a × Fin d → R` to `fun q => B.repr (g q.1) q.2`. Establish `hg' : ∀ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) = g i`. Introduce `i`. Simplify using `only [c, ← hBk]`. Conclude with `B.sum_repr (g i)`.

Establish `hc : wMat b R X *ᵥ c = 0`. Rewrite using `[wMat_mulVec_eq_zero]`. Introduce `j`. Simplify using `only [hg']`. Conclude with `(hsum g).mp hg j`.

Establish `h0` using `h c hc`. Apply `B.repr.injective` to reduce the goal to its premises. Use extensionality with `k`. Establish `h4` using `congrFun h0 (i, k)`. Simplify `h4` using `[c]`.
-/
theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  classical
  let B := Algebra.TensorProduct.basis R b
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply b k
  have hsum : ∀ g : Fin a → R ⊗[F] E, (∑ i, g i • X i = 0) ↔ ∀ j, ∑ i, g i * X i j = 0 := by
    intro g
    constructor
    · intro h j
      have h1 := congrFun h j
      simpa [Finset.sum_apply] using h1
    · intro h
      funext j
      simpa [Finset.sum_apply] using h j
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hli c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hli (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) ((hsum _).mpr hc)
    funext q
    obtain ⟨i, k⟩ := q
    have h0' : (∑ k, c (i, k) • B k) = 0 := by
      have h3 := h0 i
      simpa [hBk] using h3
    have h2 : ⇑(B.repr (∑ k, c (i, k) • B k)) = fun k => c (i, k) := B.repr_sum_self _
    rw [h0', map_zero] at h2
    simpa using (congrFun h2 k).symm
  · intro h g hg i
    let c : Fin a × Fin d → R := fun q => B.repr (g q.1) q.2
    have hg' : ∀ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) = g i := by
      intro i
      simp only [c, ← hBk]
      exact B.sum_repr (g i)
    have hc : wMat b R X *ᵥ c = 0 := by
      rw [wMat_mulVec_eq_zero]
      intro j
      simp only [hg']
      exact (hsum g).mp hg j
    have h0 := h c hc
    apply B.repr.injective
    ext k
    have h4 := congrFun h0 (i, k)
    simpa [c] using h4

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

attribute [local instance] isModTop_tens isTopRing_tens

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)`.
-/
theorem continuous_crd (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

/- English proof (translation)
Use `continuous_matrix fun p q => ?_` and prove the remaining obligations. Conclude with `(continuous_crd b R p.2).comp (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))`.
-/
theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_matrix fun p q => ?_
  exact (continuous_crd b R p.2).comp
    (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))

include b in
/- English proof (translation)
Establish `e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} = ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R, (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r}`. Use extensionality with `X`. Simplify using `only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]`. Rewrite using `[linIndep_iff b]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Take `⟨P, hP⟩` from `hL _ _ _ h`. Conclude with `⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩`. Introduce and unpack `⟨P, hP⟩ c hc`. Conclude with `inj_of_isUnit _ P hP c hc`.

Rewrite using `[e]`. Conclude with `isOpen_iUnion fun P => hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)`.
-/
theorem isOpen_linIndep (hU : IsOpen {r : R | IsUnit r}) (hL : LIP R) {a M : ℕ} :
    IsOpen {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} := by
  have e : {X : Fin a → Fin M → R ⊗[F] E | LinearIndependent (R ⊗[F] E) X} =
      ⋃ P : Matrix (Fin a × Fin d) (Fin M × Fin d) R,
        (fun X => (P * wMat b R X).det) ⁻¹' {r | IsUnit r} := by
    ext X
    simp only [Set.mem_ofPred_eq, Set.mem_iUnion, Set.mem_preimage]
    rw [linIndep_iff b]
    constructor
    · intro h
      obtain ⟨P, hP⟩ := hL _ _ _ h
      exact ⟨P, by rw [hP, Matrix.det_one]; exact isUnit_one⟩
    · rintro ⟨P, hP⟩ c hc
      exact inj_of_isUnit _ P hP c hc
  rw [e]
  exact isOpen_iUnion fun P =>
    hU.preimage ((continuous_const.matrix_mul (continuous_wMat b R)).matrix_det)

end Free

section Fib

/- English proof (translation)
Take `⟨hconc, -, hint⟩` from `h`. Establish `hsub : Uᶜ ⊆ (f ⁻¹' {ι b} ∩ U)ᶜ` using `fun x hx hx' => hx hx'.2`. Establish `hnull : fib b Uᶜ = 0` using `measure_mono_null hsub (hconc b)`. Establish `hK : ∀ K : Set V, IsCompact K → K ⊆ U → fib b K < ⊤`. Introduce `K hKc hKU`.

Take `⟨L, hLc, hKL, hLU⟩` from `exists_compact_between hKc hU hKU`. Take `⟨g, hg1, hg0, hgc, -⟩` from `exists_continuous_one_zero_of_isCompact hKc isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKL)`. Establish `hsupp : Function.support g ⊆ interior L`. Introduce `x hx`. Assume the negation of the conclusion as `hn`.

Conclude with `hx (by simpa using hg0 hn)`. Establish `hts : tsupport g ⊆ U` using `(closure_minimal (hsupp.trans interior_subset) hLc.isClosed).trans hLU`. Establish `hI` using `(hint g g.continuous hgc hts).1 b (Set.mem_univ b)`. Establish `hle` using `hI.measure_norm_ge_lt_top (ε := 1) one_pos`. Use `lt_of_le_of_lt (measure_mono ?_) hle` and prove the remaining obligations.

Introduce `x hx`. Use `show (1 : ℝ) ≤ ‖g x‖`. Rewrite using `[hg1 hx]`. Simplify using the standard rewrite rules. Use `haveI : LocallyCompactSpace U := hU.locallyCompactSpace`.

Set `K : ℕ → Set V` to `fun n => Subtype.val '' compactCovering U n`. Establish `hKc : ∀ n, IsCompact (K n)` using `fun n => (isCompact_compactCovering U n).image continuous_subtype_val`. Establish `hKU : ∀ n, K n ⊆ U`. Introduce `n y hy`. Take `⟨x, -, rfl⟩` from `hy`.

Conclude with `x.2`. Establish `hcov : ∀ x ∈ U, ∃ n, x ∈ K n`. Introduce `x hx`. Take `⟨n, hn⟩` from `exists_mem_compactCovering (⟨x, hx⟩ : U)`. Conclude with `⟨n, ⟨x, hx⟩, hn, rfl⟩`.

Establish `hfin : ∀ n, fib b (K n ∪ Uᶜ) < ⊤` using `fun n => (measure_union_le _ _).trans_lt (ENNReal.add_lt_top.mpr ⟨hK _ (hKc n) (hKU n), by rw [hnull]; exact ENNReal.zero_lt_top⟩)`. Use `haveI : SigmaFinite (fib b) := ⟨⟨{ set := fun n => K n ∪ Uᶜ set_mem := fun _ => Set.mem_univ _ finite := hfin spanning := by`. Use `Set.eq_univ_of_forall fun x => ?_` and prove the remaining obligations. Distinguish the cases in `hx : x ∈ U`. Take `⟨n, hn⟩` from `hcov x hx`.

Conclude with `Set.mem_iUnion.mpr ⟨n, Or.inl hn⟩`. Conclude with `Set.mem_iUnion.mpr ⟨0, Or.inr hx⟩ }⟩⟩`. Use `infer_instance`.
-/
theorem sfinite_of_fib {V X Y : Type} [TopologicalSpace V] [MeasurableSpace V]
    [OpensMeasurableSpace V] [T2Space V] [LocallyCompactSpace V] [SecondCountableTopology V]
    [TopologicalSpace X] [MeasurableSpace X] {μ : Measure V} {f : V → Y} {ι : X → Y}
    {U : Set V} (hU : IsOpen U) {ν : Measure X} {fib : X → Measure V}
    (h : IsFibreFamily μ f ι U ν Set.univ fib) (b : X) : SFinite (fib b) := by
  classical
  obtain ⟨hconc, -, hint⟩ := h
  have hsub : Uᶜ ⊆ (f ⁻¹' {ι b} ∩ U)ᶜ := fun x hx hx' => hx hx'.2
  have hnull : fib b Uᶜ = 0 := measure_mono_null hsub (hconc b)
  have hK : ∀ K : Set V, IsCompact K → K ⊆ U → fib b K < ⊤ := by
    intro K hKc hKU
    obtain ⟨L, hLc, hKL, hLU⟩ := exists_compact_between hKc hU hKU
    obtain ⟨g, hg1, hg0, hgc, -⟩ := exists_continuous_one_zero_of_isCompact hKc
      isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKL)
    have hsupp : Function.support g ⊆ interior L := by
      intro x hx
      by_contra hn
      exact hx (by simpa using hg0 hn)
    have hts : tsupport g ⊆ U :=
      (closure_minimal (hsupp.trans interior_subset) hLc.isClosed).trans hLU
    have hI := (hint g g.continuous hgc hts).1 b (Set.mem_univ b)
    have hle := hI.measure_norm_ge_lt_top (ε := 1) one_pos
    refine lt_of_le_of_lt (measure_mono ?_) hle
    intro x hx
    show (1 : ℝ) ≤ ‖g x‖
    rw [hg1 hx]
    simp
  haveI : LocallyCompactSpace U := hU.locallyCompactSpace
  let K : ℕ → Set V := fun n => Subtype.val '' compactCovering U n
  have hKc : ∀ n, IsCompact (K n) := fun n =>
    (isCompact_compactCovering U n).image continuous_subtype_val
  have hKU : ∀ n, K n ⊆ U := by
    intro n y hy
    obtain ⟨x, -, rfl⟩ := hy
    exact x.2
  have hcov : ∀ x ∈ U, ∃ n, x ∈ K n := by
    intro x hx
    obtain ⟨n, hn⟩ := exists_mem_compactCovering (⟨x, hx⟩ : U)
    exact ⟨n, ⟨x, hx⟩, hn, rfl⟩
  have hfin : ∀ n, fib b (K n ∪ Uᶜ) < ⊤ := fun n =>
    (measure_union_le _ _).trans_lt
      (ENNReal.add_lt_top.mpr ⟨hK _ (hKc n) (hKU n), by rw [hnull]; exact ENNReal.zero_lt_top⟩)
  haveI : SigmaFinite (fib b) := ⟨⟨{
    set := fun n => K n ∪ Uᶜ
    set_mem := fun _ => Set.mem_univ _
    finite := hfin
    spanning := by
      refine Set.eq_univ_of_forall fun x => ?_
      by_cases hx : x ∈ U
      · obtain ⟨n, hn⟩ := hcov x hx
        exact Set.mem_iUnion.mpr ⟨n, Or.inl hn⟩
      · exact Set.mem_iUnion.mpr ⟨0, Or.inr hx⟩ }⟩⟩
  infer_instance

end Fib

section Main

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `first`. Consider the case `infer_instance`. Consider the case `exact Module.Finite.of_restrictScalars_finite ℚ F E`.
-/
theorem finDim_FE : FiniteDimensional F E := by
  first
  | infer_instance
  | exact Module.Finite.of_restrictScalars_finite ℚ F E

/- English proof (translation)
Use `haveI : FiniteDimensional F E := finDim_FE`. Conclude with `isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv v) (lip_field _)`.
-/
theorem isOpen_indep (v : HeightOneSpectrum (𝓞 F)) (n a : ℕ) :
    IsOpen (IndepV (E := E) (n := n) v a) := by
  haveI : FiniteDimensional F E := finDim_FE
  exact isOpen_linIndep (Module.finBasis F E) (Fv F v) (isOpen_units_Fv v) (lip_field _)

end Main

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v _ a T`. Unfold `Formalism.L2.SG.LocVol.omAt`. Use `split_ifs with hT`. Unfold `Formalism.L2.SG.LocVol.omFam split_ifs with hfib`. Use `haveI : FiniteDimensional F E := finDim_FE haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v) haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_pro …`.

Consider the case `exact ⟨le_rfl⟩`. Consider the case `(haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩; infer_instance)`. Conclude with `sfinite_of_fib (isOpen_indep v n a) hfib.choose_spec ⟨T, hT⟩`. Use `infer_instance`. Use `infer_instance`.
-/
theorem orbit_measure_sFinite : LocMassOrdW.OmSF := by
  intro F E _ _ _ _ _ σ n J ψ v _ a T
  unfold Formalism.L2.SG.LocVol.omAt
  split_ifs with hT
  · unfold Formalism.L2.SG.LocVol.omFam
    split_ifs with hfib
    · haveI : FiniteDimensional F E := finDim_FE
      haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v
      haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v
      haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v)
      haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
      haveI : SecondCountableTopology (Fv F v ⊗[F] E) := sc_tens (Fv F v)
      haveI : OpensMeasurableSpace (TupV (E := E) v n a) := by
        first
        | exact ⟨le_rfl⟩
        | (haveI : BorelSpace (Fv F v ⊗[F] E) := ⟨rfl⟩; infer_instance)
      exact sfinite_of_fib (isOpen_indep v n a) hfib.choose_spec ⟨T, hT⟩
    · infer_instance
  · infer_instance

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J ψ v _ r`. Unfold `Formalism.L2.SG.LocVol.sdE`. Use `split_ifs with h`. Use `haveI : FiniteDimensional F E := finDim_FE haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v) haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_pro …`. Use `infer_instance`.
-/
theorem self_dual_measure_sFinite : LocMassOrdW.SdESF := by
  intro F E _ _ _ _ _ σ n J ψ v _ r
  unfold Formalism.L2.SG.LocVol.sdE
  split_ifs with h
  · haveI : FiniteDimensional F E := finDim_FE
    haveI : LocallyCompactSpace (Fv F v) := locallyCompact_Fv v
    haveI : SecondCountableTopology (Fv F v) := secondCountable_Fv v
    haveI : LocallyCompactSpace (Fv F v ⊗[F] E) := lc_tens (Fv F v)
    haveI : T2Space (Fv F v ⊗[F] E) := t2_tensor_product (Fv F v)
    haveI : SecondCountableTopology (Fv F v ⊗[F] E) := sc_tens (Fv F v)
    haveI := h.choose_spec.1
    infer_instance
  · infer_instance

end LocMassOrdSF
