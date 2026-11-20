import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.EmbeddingLinearIndependent
import Formalism.LocalToGlobal.SiegelLatticeTheory.CasimirReductionTheory.OneParameterDerivatives.TauReduction.BlockGramReduction.PacketConditionsClosed

set_option autoImplicit false

noncomputable section

open NumberField Matrix Module MeasureTheory
open scoped ComplexOrder Classical

namespace Formalism.L2.SG.Pf.Tau

open Size Formalism.MainNotions.S

/- English proof (translation)
Simplify using `[Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul]`.
-/
theorem blockDiagonal_mulVec_apply {j : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ]
    (R : κ → Matrix (Fin j) (Fin j) ℂ) (z : Fin j × κ → ℂ) (k : Fin j) (v : κ) :
    (blockDiagonal R *ᵥ z) (k, v) = (R v *ᵥ fun k' => z (k', v)) k := by
  simp [Matrix.mulVec, dotProduct, Fintype.sum_prod_type, blockDiagonal_apply, ite_mul]

/- English proof (translation)
Rewrite using `[LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_blockDiagonal, map_prod]`. Simplify using `[Algebra.norm_complex_apply]`.
-/
theorem det_blockDiagonal_real {j : ℕ} {κ : Type} [Fintype κ] [DecidableEq κ] (R : κ → Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det ((Matrix.toLin' (blockDiagonal R)).restrictScalars ℝ) = ∏ v, Complex.normSq (R v).det := by
  rw [LinearMap.det_restrictScalars, LinearMap.det_toLin', Matrix.det_blockDiagonal, map_prod]
  simp [Algebra.norm_complex_apply]

variable (I : AutInst) (j : ℕ)

def t8Eq : Fin 2 × (Fin j × InfinitePlace I.F) ≃ Fin (2 * I.f * j) :=
  Fintype.equivFinOfCardEq (by simp [card_infinite_places]; ring)

def t8J : (Fin j × InfinitePlace I.F → ℂ) ≃ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  complexToEuclidean (t8Eq I j)

/- English proof (translation)
Rewrite using `[EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]`. Simplify using `only [Real.norm_eq_abs, sq_abs]`. Rewrite using `[← (t8Eq I j).sum_comp]`. Simplify using `[t8J, complexToEuclidean, Fintype.sum_prod_type, Fin.sum_univ_two, Module.Basis.smulTower_repr, Complex.coe_basisOneI_repr, Complex.sq_norm, Complex.normSq_apply, ← sq]`. Simplify using `only [Finset.sum_add_distrib]`.
-/
theorem placeEmbedding_norm_sq (z : Fin j × InfinitePlace I.F → ℂ) : ‖t8J I j z‖ ^ 2 = ∑ q, ‖z q‖ ^ 2 := by
  rw [EuclideanSpace.norm_eq, Real.sq_sqrt (Finset.sum_nonneg fun _ _ => sq_nonneg _)]
  simp only [Real.norm_eq_abs, sq_abs]
  rw [← (t8Eq I j).sum_comp]
  simp [t8J, complexToEuclidean, Fintype.sum_prod_type, Fin.sum_univ_two, Module.Basis.smulTower_repr,
    Complex.coe_basisOneI_repr, Complex.sq_norm, Complex.normSq_apply, ← sq]
  simp only [Finset.sum_add_distrib]

def placeCoordsBasis : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (Fin j × InfinitePlace I.F → ℂ) :=
  (Pi.basis fun _ : Fin j => embeddingBasis I).map (LinearEquiv.curry ℝ ℂ (Fin j) (InfinitePlace I.F)).symm

/- English proof (translation)
Simplify using `[placeCoordsBasis, embeddingBasis, Pi.basis_apply]`. Distinguish the cases in `h : q.1 = p.1`. Rewrite using `[if_pos h]`. Simplify using `[Function.uncurry_def, h]`. Rewrite using `[if_neg h]`.

Simplify using `[Function.uncurry_def, Pi.single_eq_of_ne h]`.
-/
theorem placeCoordsBasis_apply (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) (q : Fin j × InfinitePlace I.F) :
    placeCoordsBasis I j p q = if q.1 = p.1 then I.φ q.2 (integralBasis I.E p.2) else 0 := by
  simp [placeCoordsBasis, embeddingBasis, Pi.basis_apply]
  by_cases h : q.1 = p.1
  · rw [if_pos h]
    simp [Function.uncurry_def, h]
  · rw [if_neg h]
    simp [Function.uncurry_def, Pi.single_eq_of_ne h]

def t8B0 : Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (EuclideanSpace ℝ (Fin (2 * I.f * j))) :=
  (placeCoordsBasis I j).map (t8J I j)

def t8K : ℝ := volume.real (ZSpan.fundamentalDomain (t8B0 I j))

/- English proof (translation)
Unfold `t8K`. Use `haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range (t8B0 I j))) (EuclideanSpace ℝ (Fin (2 * I.f * j))) volume := ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℝ (Fin (2 * I.f * j))) s⟩`. Use `ENNReal.toReal_pos ?_ ?_` and prove the remaining obligations. Conclude with `(ZSpan.isAddFundamentalDomain (t8B0 I j) volume).measure_ne_zero (NeZero.ne volume)`. Conclude with `(ZSpan.fundamentalDomain_isBounded (t8B0 I j)).measure_lt_top.ne`.
-/
theorem integral_covolume_pos : 0 < t8K I j := by
  unfold t8K
  haveI : VAddInvariantMeasure (Submodule.span ℤ (Set.range (t8B0 I j)))
      (EuclideanSpace ℝ (Fin (2 * I.f * j))) volume :=
    ⟨fun c s _ => measure_preimage_add volume (c : EuclideanSpace ℝ (Fin (2 * I.f * j))) s⟩
  refine ENNReal.toReal_pos ?_ ?_
  · exact (ZSpan.isAddFundamentalDomain (t8B0 I j) volume).measure_ne_zero (NeZero.ne volume)
  · exact (ZSpan.fundamentalDomain_isBounded (t8B0 I j)).measure_lt_top.ne

def placeCoords : (Fin j → I.E) →+ (Fin j × InfinitePlace I.F → ℂ) where
  toFun a := fun q => I.φ q.2 (a q.1)
  map_zero' := by
    funext q
    simp
  map_add' a b := by
    funext q
    simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem placeCoords_apply (a : Fin j → I.E) (q : Fin j × InfinitePlace I.F) : placeCoords I j a q = I.φ q.2 (a q.1) := rfl

/- English proof (translation)
Use function extensionality and compare the values at `q`. Rewrite using `[placeCoords_apply, placeCoordsBasis_apply]`. Distinguish the cases in `h : q.1 = p.1`. Simplify using `[h]`. Simplify using `[h, Pi.single_apply]`.
-/
theorem placeCoords_single (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    placeCoords I j (Pi.single p.1 (integralBasis I.E p.2)) = placeCoordsBasis I j p := by
  funext q
  rw [placeCoords_apply, placeCoordsBasis_apply]
  by_cases h : q.1 = p.1
  · simp [h]
  · simp [h, Pi.single_apply]

def t8O : Submodule ℤ (Fin j → I.E) :=
  Submodule.span ℤ (Set.range fun p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E) =>
    Pi.single p.1 (integralBasis I.E p.2))

/- English proof (translation)
Establish `key : ∀ (k : Fin j) (x : 𝓞 I.E), Pi.single k (x : I.E) ∈ t8O I j`. Introduce `k x`. Establish `hx : (x : I.E) = ∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i` using `by conv_lhs => rw [← (RingOfIntegers.basis I.E).sum_repr x]`. Simplify using `[integralBasis_apply]`. Establish `hs : Pi.single k (∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i) = ∑ i, ((RingOfIntegers.basis I.E).repr x i) • (Pi.single k (integralBasis I.E i) : Fin j → I.E)`.

Use function extensionality and compare the values at `k'`. Distinguish the cases in `h : k' = k`. Substitute `h` using the available equality. Simplify using `[Finset.sum_apply]`. Simplify using `[Finset.sum_apply, Pi.single_apply, h]`.

Rewrite using `[hx, hs]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, i⟩, rfl⟩)`. Rewrite using `[← Finset.univ_sum_single a]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `ha k`.

Rewrite using `[← hc]`. Conclude with `key k c`.
-/
theorem mem_integral_vectors (a : Fin j → I.E) (ha : ∀ k, ∃ c : 𝓞 I.E, (c : I.E) = a k) : a ∈ t8O I j := by
  have key : ∀ (k : Fin j) (x : 𝓞 I.E), Pi.single k (x : I.E) ∈ t8O I j := by
    intro k x
    have hx : (x : I.E) = ∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i := by
      conv_lhs => rw [← (RingOfIntegers.basis I.E).sum_repr x]
      simp [integralBasis_apply]
    have hs : Pi.single k (∑ i, ((RingOfIntegers.basis I.E).repr x i) • integralBasis I.E i) =
        ∑ i, ((RingOfIntegers.basis I.E).repr x i) • (Pi.single k (integralBasis I.E i) : Fin j → I.E) := by
      funext k'
      by_cases h : k' = k
      · subst h
        simp [Finset.sum_apply]
      · simp [Finset.sum_apply, Pi.single_apply, h]
    rw [hx, hs]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨k, i⟩, rfl⟩)
  rw [← Finset.univ_sum_single a]
  refine Submodule.sum_mem _ fun k _ => ?_
  obtain ⟨c, hc⟩ := ha k
  rw [← hc]
  exact key k c

variable {I j}

def t8Rl (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    (Fin j × InfinitePlace I.F → ℂ) →ₗ[ℂ] (Fin j × InfinitePlace I.F → ℂ) :=
  Matrix.toLin' (blockDiagonal R)

def t8T (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    EuclideanSpace ℝ (Fin (2 * I.f * j)) →ₗ[ℝ] EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  (t8J I j).toLinearMap ∘ₗ (t8Rl R).restrictScalars ℝ ∘ₗ (t8J I j).symm.toLinearMap

/- English proof (translation)
Unfold `t8T`. Rewrite using `[LinearMap.det_conj]`. Conclude with `det_blockDiagonal_real R`.
-/
theorem blockLinear_det (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    LinearMap.det (t8T R) = ∏ v, Complex.normSq (R v).det := by
  unfold t8T
  rw [LinearMap.det_conj]
  exact det_blockDiagonal_real R

/- English proof (translation)
Rewrite using `[blockLinear_det]`. Conclude with `Finset.prod_ne_zero_iff.2 fun v _ => (Complex.normSq_pos.2 (hR v)).ne'`.
-/
theorem blockLinear_det_ne_zero (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    LinearMap.det (t8T R) ≠ 0 := by
  rw [blockLinear_det]
  exact Finset.prod_ne_zero_iff.2 fun v _ => (Complex.normSq_pos.2 (hR v)).ne'

def t8Th (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) :
    (Fin j → I.E) →+ EuclideanSpace ℝ (Fin (2 * I.f * j)) :=
  ((t8J I j).toLinearMap.toAddMonoidHom.comp ((t8Rl R).toAddMonoidHom)).comp (placeCoords I j)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem blockTransform_apply (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (a : Fin j → I.E) :
    t8Th R a = t8J I j (t8Rl R (placeCoords I j a)) := rfl

/- English proof (translation)
Rewrite using `[blockTransform_apply, placeCoords_single]`. Simplify using `[t8T, t8B0]`.
-/
theorem blockTransform_single (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ)
    (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) :
    t8Th R (Pi.single p.1 (integralBasis I.E p.2)) = t8T R (t8B0 I j p) := by
  rw [blockTransform_apply, placeCoords_single]
  simp [t8T, t8B0]

/- English proof (translation)
Rewrite using `[blockTransform_apply, placeEmbedding_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]`. Simplify using `only [t8Rl, Matrix.toLin'_apply, blockDiagonal_mulVec_apply, placeCoords_apply]`.
-/
theorem blockTransform_norm_sq (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (a : Fin j → I.E) :
    ‖t8Th R a‖ ^ 2 = ∑ v, ∑ k, ‖(R v *ᵥ fun k' => I.φ v (a k')) k‖ ^ 2 := by
  rw [blockTransform_apply, placeEmbedding_norm_sq, Fintype.sum_prod_type, Finset.sum_comm]
  simp only [t8Rl, Matrix.toLin'_apply, blockDiagonal_mulVec_apply, placeCoords_apply]

/- English proof (translation)
Introduce `a b h`. Establish `h1 : t8Rl R (placeCoords I j a) = t8Rl R (placeCoords I j b)` using `(t8J I j).injective h`. Establish `hdet : (blockDiagonal R).det ≠ 0`. Rewrite using `[det_blockDiagonal]`. Conclude with `Finset.prod_ne_zero_iff.2 fun v _ => hR v`.

Establish `hinj : Function.Injective (blockDiagonal R).mulVec` using `Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))`. Establish `h2 : placeCoords I j a = placeCoords I j b` using `hinj h1`. Use function extensionality and compare the values at `k`. Take `⟨v⟩` from `(inferInstance : Nonempty (InfinitePlace I.F))`. Conclude with `(I.φ v).injective (congrFun h2 (k, v))`.
-/
theorem blockTransform_injective (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    Function.Injective (t8Th R) := by
  intro a b h
  have h1 : t8Rl R (placeCoords I j a) = t8Rl R (placeCoords I j b) := (t8J I j).injective h
  have hdet : (blockDiagonal R).det ≠ 0 := by
    rw [det_blockDiagonal]
    exact Finset.prod_ne_zero_iff.2 fun v _ => hR v
  have hinj : Function.Injective (blockDiagonal R).mulVec :=
    Matrix.mulVec_injective_iff_isUnit.2 ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hdet))
  have h2 : placeCoords I j a = placeCoords I j b := hinj h1
  funext k
  obtain ⟨v⟩ := (inferInstance : Nonempty (InfinitePlace I.F))
  exact (I.φ v).injective (congrFun h2 (k, v))

def blockBasis (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    Basis (Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) ℝ (EuclideanSpace ℝ (Fin (2 * I.f * j))) :=
  (t8B0 I j).map ((t8T R).equivOfDetNeZero (blockLinear_det_ne_zero R hR))

/- English proof (translation)
Simplify using `[blockBasis]`.
-/
theorem blockBasis_apply (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0)
    (p : Σ _ : Fin j, Free.ChooseBasisIndex ℤ (𝓞 I.E)) : blockBasis R hR p = t8T R (t8B0 I j p) := by
  simp [blockBasis]

set_option maxRecDepth 20000 in

/- English proof (translation)
Rewrite using `[ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain (blockBasis R hR) volume)]`. Rewrite using `[Measure.real, ZSpan.measure_fundamentalDomain (blockBasis R hR) volume (t8B0 I j)]`. Establish `hb : (t8B0 I j).det ⇑(blockBasis R hR) = LinearMap.det (t8T R)`. Establish `: ⇑(blockBasis R hR) = t8T R ∘ ⇑(t8B0 I j)` using `funext fun p => blockBasis_apply R hR p`. Rewrite using `[this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]`.

Rewrite using `[hb, blockLinear_det, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _), abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]`. Both sides reduce to the same expression.
-/
theorem covolume_blockBasis (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    ZLattice.covolume (Submodule.span ℤ (Set.range (blockBasis R hR))) =
      (∏ v, Complex.normSq (R v).det) * t8K I j := by
  rw [ZLattice.covolume_eq_measure_fundamentalDomain _ volume (ZSpan.isAddFundamentalDomain (blockBasis R hR) volume)]
  rw [Measure.real, ZSpan.measure_fundamentalDomain (blockBasis R hR) volume (t8B0 I j)]
  have hb : (t8B0 I j).det ⇑(blockBasis R hR) = LinearMap.det (t8T R) := by
    have : ⇑(blockBasis R hR) = t8T R ∘ ⇑(t8B0 I j) := funext fun p => blockBasis_apply R hR p
    rw [this, Module.Basis.det_comp, Module.Basis.det_self, mul_one]
  rw [hb, blockLinear_det, ENNReal.toReal_mul, ENNReal.toReal_ofReal (abs_nonneg _),
    abs_of_nonneg (Finset.prod_nonneg fun v _ => Complex.normSq_nonneg _)]
  rfl

/- English proof (translation)
Rewrite using `[t8O, Submodule.map_span, ← Set.range_comp]`. Use `congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun p => ?_))` and prove the remaining obligations. Use `show t8Th R (Pi.single p.1 (integralBasis I.E p.2)) = blockBasis R hR p`. Rewrite using `[blockTransform_single, blockBasis_apply]`.
-/
theorem map_integral_vectors_span (R : InfinitePlace I.F → Matrix (Fin j) (Fin j) ℂ) (hR : ∀ v, (R v).det ≠ 0) :
    (t8O I j).map (t8Th R).toIntLinearMap = Submodule.span ℤ (Set.range (blockBasis R hR)) := by
  rw [t8O, Submodule.map_span, ← Set.range_comp]
  refine congrArg (Submodule.span ℤ) (congrArg Set.range (funext fun p => ?_))
  show t8Th R (Pi.single p.1 (integralBasis I.E p.2)) = blockBasis R hR p
  rw [blockTransform_single, blockBasis_apply]

end Formalism.L2.SG.Pf.Tau
