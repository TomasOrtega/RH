import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.HermitianSpaceBaseLatticeEqFrameLattice
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsOpenIsCompactLevelOffFinEmpty
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIsLatticeFrameIsMajorantFrame
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.AlgebraMapNormTensorEqProdConjugates
import Development.AbelianVarietyTheory.Definitions.Foundations.NormEulerPolySubOneLe
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsGLSubmatrix

noncomputable section

namespace GlobalTheory.Doubling

open scoped TensorProduct NNReal
open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.UG GlobalTheory.AdelicU
open GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups (tensNU)

section Norm

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
  {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R']

/- English proof (translation)
Set `b` to `Module.finBasis F E`. Establish `h : ∀ (y : R ⊗[F] E) i, (Algebra.TensorProduct.basis R' b).repr (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i = φ ((Algebra.TensorProduct.basis R b).repr y i)`. Introduce `y i`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]`. Consider the case `add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]`. Rewrite using `[Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R' b), Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R b), AlgHom.map_det]`. Use `congr 1`. Use extensionality with `i j`.

Rewrite using `[AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul, ← h, map_mul (Algebra.TensorProduct.map φ (AlgHom.id F E))]`. Simplify using `[Algebra.TensorProduct.basis_apply]`.
-/
theorem norm_map (φ : R →ₐ[F] R') (x : R ⊗[F] E) :
    Algebra.norm R' (Algebra.TensorProduct.map φ (AlgHom.id F E) x) = φ (Algebra.norm R x) := by
  classical
  let b := Module.finBasis F E
  have h : ∀ (y : R ⊗[F] E) i, (Algebra.TensorProduct.basis R' b).repr
      (Algebra.TensorProduct.map φ (AlgHom.id F E) y) i = φ ((Algebra.TensorProduct.basis R b).repr y i) := by
    intro y i
    induction y using TensorProduct.induction_on with
    | zero => simp
    | tmul a e => simp [Algebra.TensorProduct.basis_repr_tmul]
    | add x y hx hy => simp only [map_add, Finsupp.add_apply, hx, hy]
  rw [Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R' b),
    Algebra.norm_eq_matrix_det (Algebra.TensorProduct.basis R b), AlgHom.map_det]
  congr 1
  ext i j
  rw [AlgHom.mapMatrix_apply, Matrix.map_apply, Algebra.leftMulMatrix_eq_repr_mul, Algebra.leftMulMatrix_eq_repr_mul,
    ← h, map_mul (Algebra.TensorProduct.map φ (AlgHom.id F E))]
  simp [Algebra.TensorProduct.basis_apply]

/- English proof (translation)
Rewrite using `[Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]`. Use `congr 1`. Use extensionality with `y`. Simplify using `[inclR]`.
-/
theorem norm_inclR (x : E) : Algebra.norm R (inclR (F := F) R x) = algebraMap F R (Algebra.norm F x) := by
  rw [Algebra.norm_apply, Algebra.norm_apply, ← LinearMap.det_baseChange]
  congr 1
  ext y
  simp [inclR]

/- English proof (translation)
The claim follows from `Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := R)) (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ))) x`.
-/
theorem norm_sigR (σ : E →ₐ[F] E) (x : R ⊗[F] E) :
    Algebra.norm R (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x) = Algebra.norm R x :=
  Algebra.norm_eq_of_algEquiv (Algebra.TensorProduct.congr (AlgEquiv.refl (R := R) (A₁ := R))
    (AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ))) x

/- English proof (translation)
Use `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩`. Set `b` to `Algebra.TensorProduct.basis R (Module.finBasis F E)`. Rewrite using `[show (Algebra.norm R : R ⊗[F] E → R) = fun x => (Algebra.leftMulMatrix b x).det from`. Use function extensionality and compare the values at `fun x => Algebra.norm_eq_matrix_det b x]`. Conclude with `(IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det`.
-/
theorem continuous_norm_tens [TopologicalSpace R] [IsTopologicalRing R] :
    Continuous (Algebra.norm R : R ⊗[F] E → R) := by
  classical
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let b := Algebra.TensorProduct.basis R (Module.finBasis F E)
  rw [show (Algebra.norm R : R ⊗[F] E → R) = fun x => (Algebra.leftMulMatrix b x).det from
    funext fun x => Algebra.norm_eq_matrix_det b x]
  exact (IsModuleTopology.continuous_of_linearMap (Algebra.leftMulMatrix b).toLinearMap).matrix_det

/- English proof (translation)
The claim follows from `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩ IsModuleTopology.isTopologicalRing R _`.
-/
theorem isTopologicalRing_tens [TopologicalSpace R] [IsTopologicalRing R] : IsTopologicalRing (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  IsModuleTopology.isTopologicalRing R _

/- English proof (translation)
The claim follows from `haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩ let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)`.
-/
theorem t2Space_tensorProduct_finiteExtension [TopologicalSpace R] [IsTopologicalRing R] [T2Space R] : T2Space (R ⊗[F] E) :=
  haveI : IsModuleTopology R (R ⊗[F] E) := ⟨rfl⟩
  let e := (Algebra.TensorProduct.basis R (Module.finBasis F E)).equivFun
  T2Space.of_injective_continuous e.injective (IsModuleTopology.continuous_of_linearMap e.toLinearMap)

omit [FiniteDimensional F E] in

def extUnit (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) : (R ⊗[F] E)ˣ →* (R' ⊗[F] E)ˣ :=
  Units.map
    { toFun := fun y => 1 - tensNU j hj 1 + tensNU j hj y
      map_one' := sub_add_cancel _ _
      map_mul' := fun a b => by
        have h1 := map_mul (tensNU (E := E) j hj) 1 1
        have h2 := map_mul (tensNU j hj) a 1
        have h3 := map_mul (tensNU j hj) 1 b
        rw [mul_one] at h1 h2
        rw [one_mul] at h3
        rw [map_mul]
        linear_combination h1 - h2 - h3 }

omit [FiniteDimensional F E] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem val_extUnit (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (y : (R ⊗[F] E)ˣ) :
    (extUnit j hj y : R' ⊗[F] E) = 1 - tensNU j hj 1 + tensNU j hj y := rfl

/- English proof (translation)
The claim follows from `haveI := isTopologicalRing_tens (F := F) (E := E) (R := R') Continuous.units_map _ (continuous_const.add (GlobalTheory.AutFunCompare.continuous_tensNU j hj hc))`.
-/
theorem continuous_extUnit [TopologicalSpace R] [IsTopologicalRing R] [TopologicalSpace R'] [IsTopologicalRing R']
    (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (hc : Continuous j) : Continuous (extUnit (E := E) j hj) :=
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := R')
  Continuous.units_map _ (continuous_const.add (GlobalTheory.AutFunCompare.continuous_tensNU j hj hc))

omit [FiniteDimensional F E] in

def conjUnit (σ : E →ₐ[F] E) : (R ⊗[F] E)ˣ →* (R ⊗[F] E)ˣ := Units.map (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ).toMonoidHom

end Norm

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def absEv (v : HeightOneSpectrum (𝓞 F)) : (Fv F v ⊗[F] E)ˣ →* ℝ≥0 :=
  (nnnormHom.toMonoidHom.comp (Algebra.norm (Fv F v))).comp (Units.coeHom _)

def absEw (w : InfinitePlace F) : (w.Completion ⊗[F] E)ˣ →* ℝ≥0 :=
  (powMonoidHom w.mult).comp ((nnnormHom.toMonoidHom.comp (Algebra.norm w.Completion)).comp (Units.coeHom _))

variable {F E}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absEv_apply (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    absEv F E v x = ‖Algebra.norm (Fv F v) x.1‖₊ := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absEw_apply (w : InfinitePlace F) (x : (w.Completion ⊗[F] E)ˣ) :
    absEw F E w x = ‖Algebra.norm w.Completion x.1‖₊ ^ w.mult := rfl

/- English proof (translation)
The claim follows from `(continuous_norm_tens.comp Units.continuous_val).nnnorm`.
-/
theorem continuous_absEv (v : HeightOneSpectrum (𝓞 F)) : Continuous (absEv F E v) :=
  (continuous_norm_tens.comp Units.continuous_val).nnnorm

/- English proof (translation)
The claim follows from `(continuous_norm_tens.comp Units.continuous_val).nnnorm.pow _`.
-/
theorem continuous_absEw (w : InfinitePlace F) : Continuous (absEw F E w) :=
  (continuous_norm_tens.comp Units.continuous_val).nnnorm.pow _

/- English proof (translation)
The claim follows from `congrArg nnnorm (norm_sigR σ x.1)`.
-/
theorem absEv_conjUnit (σ : E →ₐ[F] E) (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    absEv F E v (conjUnit σ x) = absEv F E v x := congrArg nnnorm (norm_sigR σ x.1)

/- English proof (translation)
The claim follows from `congrArg (fun y => ‖y‖₊ ^ w.mult) (norm_sigR σ x.1)`.
-/
theorem absEw_conjUnit (σ : E →ₐ[F] E) (w : InfinitePlace F) (x : (w.Completion ⊗[F] E)ˣ) :
    absEw F E w (conjUnit σ x) = absEw F E w x := congrArg (fun y => ‖y‖₊ ^ w.mult) (norm_sigR σ x.1)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `‖Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a.1)‖₊ = _`. Rewrite using `[Algebra.norm_algebraMap, Module.finrank_baseChange, nnnorm_pow]`.
-/
theorem absEv_algebraMap (v : HeightOneSpectrum (𝓞 F)) (a : (Fv F v)ˣ) :
    absEv F E v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom a) = ‖a.1‖₊ ^ Module.finrank F E := by
  change ‖Algebra.norm (Fv F v) (algebraMap (Fv F v) (Fv F v ⊗[F] E) a.1)‖₊ = _
  rw [Algebra.norm_algebraMap, Module.finrank_baseChange, nnnorm_pow]

/- English proof (translation)
Use `haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩`. Set `s` to `AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)`. Establish `hs : (1 : E ≃ₐ[F] E) ≠ s` using `fun e => by`. Use `h.2.1` as an intermediate fact. Take `⟨τ⟩ : Nonempty (E →+* ℂ)` from `inferInstance`.

Conclude with `InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ)) (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y => (h.2.2.2 τ y).symm.trans (congrArg τ (AlgEquiv.congr_fun e y).symm))))`. Establish `hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s}` using `(Finset.eq_univ_of_card _ (by`. Rewrite using `[Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1])).symm`. Rewrite using `[GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates, hu, Finset.prod_pair hs]`. Use `congr 1`.

Conclude with `DFunLike.congr_fun Algebra.TensorProduct.map_id x`.
-/
theorem algebraMap_norm_eq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {R : Type} [CommRing R] [Algebra F R] (x : R ⊗[F] E) :
    algebraMap R (R ⊗[F] E) (Algebra.norm R x) = x * Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.sigR R σ x := by
  classical
  haveI : Algebra.IsQuadraticExtension F E := ⟨h.2.2.1⟩
  let s := AlgEquiv.ofBijective σ (Algebra.IsAlgebraic.algHom_bijective σ)
  have hs : (1 : E ≃ₐ[F] E) ≠ s := fun e => by
    have := h.2.1
    obtain ⟨τ⟩ : Nonempty (E →+* ℂ) := inferInstance
    exact InfinitePlace.not_isReal_iff_isComplex.2 (IsTotallyComplex.isComplex (InfinitePlace.mk τ))
      (InfinitePlace.isReal_mk_iff.2 (ComplexEmbedding.isReal_iff.2 (RingHom.ext fun y =>
        (h.2.2.2 τ y).symm.trans (congrArg τ (AlgEquiv.congr_fun e y).symm))))
  have hu : (Finset.univ : Finset (E ≃ₐ[F] E)) = {1, s} :=
    (Finset.eq_univ_of_card _ (by
      rw [Finset.card_pair hs, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank, h.2.2.1])).symm
  rw [GlobalTheory.CNorm.algebraMap_norm_tensor_eq_prod_conjugates, hu, Finset.prod_pair hs]
  congr 1
  exact DFunLike.congr_fun Algebra.TensorProduct.map_id x

/- English proof (translation)
Use `h.1` as an intermediate fact. Establish `h1` using `congrArg (fun y => ‖infEmb τ y‖₊) (algebraMap_norm_eq h x.1)`. Simplify using `only [map_mul, ← infEmb_sigR h τ, nnnorm_mul, RCLike.nnnorm_conj] at h1`. Rewrite using `[absEw_apply, InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, sq, ← h1, Algebra.TensorProduct.algebraMap_apply, infEmb_tmul, map_one, mul_one]`. Conclude with `NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm`.
-/
theorem absEw_eq_sq {σ : E →ₐ[F] E} (h : IsCMExt F E σ) {w : InfinitePlace F} (τ : EmbOver E w)
    (x : (w.Completion ⊗[F] E)ˣ) : absEw F E w x = ‖infEmb τ x.1‖₊ ^ 2 := by
  have := h.1
  have h1 := congrArg (fun y => ‖infEmb τ y‖₊) (algebraMap_norm_eq h x.1)
  simp only [map_mul, ← infEmb_sigR h τ, nnnorm_mul, RCLike.nnnorm_conj] at h1
  rw [absEw_apply, InfinitePlace.mult, if_pos (IsTotallyReal.isReal w), pow_one, sq, ← h1,
    Algebra.TensorProduct.algebraMap_apply, infEmb_tmul, map_one, mul_one]
  exact NNReal.eq ((InfinitePlace.Completion.isometry_extensionEmbedding w).norm_map_of_map_zero (map_zero _) _).symm

variable (F E) in

def unitFin (v : HeightOneSpectrum (𝓞 F)) : (AF F ⊗[F] E)ˣ →* (Fv F v ⊗[F] E)ˣ := Units.map (compFin F E v).toMonoidHom

variable (F E) in

def unitInf (w : InfinitePlace F) : (AF F ⊗[F] E)ˣ →* (w.Completion ⊗[F] E)ˣ := Units.map (compInf F E w).toMonoidHom

/- English proof (translation)
The claim follows from `congrArg nnnorm (norm_map (evFin F v) x.1)`.
-/
theorem absEv_unitFin (v : HeightOneSpectrum (𝓞 F)) (x : (AF F ⊗[F] E)ˣ) :
    absEv F E v (unitFin F E v x) = ‖evFin F v (Algebra.norm (AF F) x.1)‖₊ := congrArg nnnorm (norm_map (evFin F v) x.1)

/- English proof (translation)
The claim follows from `congrArg (fun y => ‖y‖₊ ^ w.mult) (norm_map (evInf F w) x.1)`.
-/
theorem absEw_unitInf (w : InfinitePlace F) (x : (AF F ⊗[F] E)ˣ) :
    absEw F E w (unitInf F E w x) = ‖evInf F w (Algebra.norm (AF F) x.1)‖₊ ^ w.mult :=
  congrArg (fun y => ‖y‖₊ ^ w.mult) (norm_map (evInf F w) x.1)

/- English proof (translation)
Establish `key : ∀ y : (AF F ⊗[F] E)ˣ, evFin F v (Algebra.norm (AF F) y.1) ∈ v.adicCompletionIntegers F → absEv F E v (unitFin F E v y) ≤ 1` using `fun y hy => by`. Rewrite using `[absEv_unitFin]`. Conclude with `Valued.toNormedField.norm_le_one_iff.2 hy` after adjusting the coercions. Use `le_antisymm (key x h) ?_` and prove the remaining obligations. Use `key _ h'` as an intermediate fact.

Rewrite `this` using `[map_inv, map_inv, inv_le_one₀ (hom_pos _ _)]`. Then use the resulting hypothesis.
-/
theorem absEv_unitFin_eq_one {v : HeightOneSpectrum (𝓞 F)} {x : (AF F ⊗[F] E)ˣ}
    (h : evFin F v (Algebra.norm (AF F) x.1) ∈ v.adicCompletionIntegers F)
    (h' : evFin F v (Algebra.norm (AF F) x⁻¹.1) ∈ v.adicCompletionIntegers F) : absEv F E v (unitFin F E v x) = 1 := by
  have key : ∀ y : (AF F ⊗[F] E)ˣ, evFin F v (Algebra.norm (AF F) y.1) ∈ v.adicCompletionIntegers F →
      absEv F E v (unitFin F E v y) ≤ 1 := fun y hy => by
    rw [absEv_unitFin]; exact_mod_cast Valued.toNormedField.norm_le_one_iff.2 hy
  refine le_antisymm (key x h) ?_
  have := key _ h'
  rwa [map_inv, map_inv, inv_le_one₀ (hom_pos _ _)] at this

/- English proof (translation)
The claim follows from `(Filter.eventually_cofinite.1 ((Algebra.norm (AF F) x.1).2.2.and (Algebra.norm (AF F) x⁻¹.1).2.2)).subset fun _ hv h => hv (absEv_unitFin_eq_one h.1 h.2)`.
-/
theorem finite_mulSupport_absEv (x : (AF F ⊗[F] E)ˣ) :
    (Function.mulSupport fun v => absEv F E v (unitFin F E v x)).Finite :=
  (Filter.eventually_cofinite.1 ((Algebra.norm (AF F) x.1).2.2.and (Algebra.norm (AF F) x⁻¹.1).2.2)).subset
    fun _ hv h => hv (absEv_unitFin_eq_one h.1 h.2)

variable (F E) in

def absE : (AF F ⊗[F] E)ˣ →* ℝ≥0 where
  toFun x := (∏ w, absEw F E w (unitInf F E w x)) * ∏ᶠ v, absEv F E v (unitFin F E v x)
  map_one' := by simp
  map_mul' x y := by
    simp only [map_mul]
    rw [Finset.prod_mul_distrib, finprod_mul_distrib (finite_mulSupport_absEv x) (finite_mulSupport_absEv y),
      mul_mul_mul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem absE_apply (x : (AF F ⊗[F] E)ˣ) :
    absE F E x = (∏ w, absEw F E w (unitInf F E w x)) * ∏ᶠ v, absEv F E v (unitFin F E v x) := rfl

/- English proof (translation)
Simplify using `only [absE_apply, absEv_unitFin, absEw_unitInf]`. Rewrite using `[show Algebra.norm (AF F) (conjUnit σ x).1 = Algebra.norm (AF F) x.1 from norm_sigR σ x.1]`.
-/
theorem absE_conjUnit (σ : E →ₐ[F] E) (x : (AF F ⊗[F] E)ˣ) : absE F E (conjUnit σ x) = absE F E x := by
  simp only [absE_apply, absEv_unitFin, absEw_unitInf]
  rw [show Algebra.norm (AF F) (conjUnit σ x).1 = Algebra.norm (AF F) x.1 from norm_sigR σ x.1]

/- English proof (translation)
Establish `h0 : Algebra.norm F x.1 ≠ 0` using `Algebra.norm_ne_zero_iff.2 x.ne_zero`. Establish `h1 : Algebra.norm (AF F) (Units.map (inclR (F` using `F) (AF F)).toMonoidHom x).1 = algebraMap F _ (Algebra.norm F x.1) := norm_inclR x.1`. Simplify using `only [absE_apply, absEv_unitFin, absEw_unitInf, h1, AlgHom.commutes]`. Establish `hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) => ‖algebraMap F (Fv F v) (Algebra.norm F x.1)‖₊).Finite`. Simplify `finite_mulSupport_absEv (Units.map (inclR (F := F) (AF F)).toMonoidHom x)` using `only [absEv_unitFin, h1, AlgHom.commutes]`.

Use `NNReal.eq ?_` and prove the remaining obligations. Rewrite using `[NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_one, ← prod_abs_eq_one h0, ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]`. Use `congr 1`. Use `Finset.prod_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[NNReal.coe_pow, coe_nnnorm]`.

Use `congr 1`. Conclude with `InfinitePlace.Completion.norm_coe w _`. Conclude with `NNReal.toRealHom.toMonoidHom.map_finprod hf`.
-/
theorem absE_inclR (x : Eˣ) : absE F E (Units.map (inclR (F := F) (AF F)).toMonoidHom x) = 1 := by
  have h0 : Algebra.norm F x.1 ≠ 0 := Algebra.norm_ne_zero_iff.2 x.ne_zero
  have h1 : Algebra.norm (AF F) (Units.map (inclR (F := F) (AF F)).toMonoidHom x).1 =
    algebraMap F _ (Algebra.norm F x.1) := norm_inclR x.1
  simp only [absE_apply, absEv_unitFin, absEw_unitInf, h1, AlgHom.commutes]
  have hf : (Function.mulSupport fun v : HeightOneSpectrum (𝓞 F) =>
      ‖algebraMap F (Fv F v) (Algebra.norm F x.1)‖₊).Finite := by
    simpa only [absEv_unitFin, h1, AlgHom.commutes] using
      finite_mulSupport_absEv (Units.map (inclR (F := F) (AF F)).toMonoidHom x)
  refine NNReal.eq ?_
  rw [NNReal.coe_mul, NNReal.coe_prod, NNReal.coe_one, ← prod_abs_eq_one h0,
    ← finprod_comp_equiv FinitePlace.equivHeightOneSpectrum.symm]
  congr 1
  · refine Finset.prod_congr rfl fun w _ => ?_
    rw [NNReal.coe_pow, coe_nnnorm]
    congr 1
    exact InfinitePlace.Completion.norm_coe w _
  · exact NNReal.toRealHom.toMonoidHom.map_finprod hf

/- English proof (translation)
The claim follows from `Continuous.units_map _ (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v)) ((RestrictedProduct.continuous_eval v).comp continuous_snd))`.
-/
theorem continuous_unitFin (v : HeightOneSpectrum (𝓞 F)) : Continuous (unitFin F E v) :=
  Continuous.units_map _ (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evFin F v).toLinearMap (map_mul (evFin F v))
    ((RestrictedProduct.continuous_eval v).comp continuous_snd))

/- English proof (translation)
The claim follows from `Continuous.units_map _ (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evInf F w).toLinearMap (map_mul (evInf F w)) ((continuous_apply w).comp continuous_fst))`.
-/
theorem continuous_unitInf (w : InfinitePlace F) : Continuous (unitInf F E w) :=
  Continuous.units_map _ (GlobalTheory.AutFunCompare.continuous_tensNU (E := E) (evInf F w).toLinearMap (map_mul (evInf F w))
    ((continuous_apply w).comp continuous_fst))

/- English proof (translation)
Use `haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)`. Use `continuous_of_continuousAt_one _ ?_` and prove the remaining obligations. Establish `ho : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F}` using `(RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) => Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd`. Establish `h1` using `(ho.preimage ((continuous_norm_tens (F := F) (E := E)).comp Units.continuous_val)).inter (ho.preimage ((continuous_norm_tens (F := F) (E := E)).comp Units.continuous_coe_inv))`. Use `(continuous_finset_prod Finset.univ fun w _ => (continuous_absEw w).comp (continuous_unitInf (E := E) w)).continuousAt.congr ?_` and prove the remaining obligations.

Use `filter_upwards [h1.mem_nhds (x := 1) ⟨fun v => by simp, fun v => by simp⟩] with x hx`. Rewrite using `[absE_apply, finprod_eq_one_of_forall_eq_one fun v => absEv_unitFin_eq_one (hx.1 v) (hx.2 v), mul_one]`. Both sides reduce to the same expression.
-/
theorem continuous_absE : Continuous (absE F E) := by
  haveI := isTopologicalRing_tens (F := F) (E := E) (R := AF F)
  refine continuous_of_continuousAt_one _ ?_
  have ho : IsOpen {a : AF F | ∀ v, evFin F v a ∈ v.adicCompletionIntegers F} :=
    (RestrictedProduct.isOpen_forall_mem fun v : HeightOneSpectrum (𝓞 F) =>
      Valued.isOpen_valuationSubring (v.adicCompletion F)).preimage continuous_snd
  have h1 := (ho.preimage ((continuous_norm_tens (F := F) (E := E)).comp Units.continuous_val)).inter
    (ho.preimage ((continuous_norm_tens (F := F) (E := E)).comp Units.continuous_coe_inv))
  refine (continuous_finset_prod Finset.univ fun w _ =>
    (continuous_absEw w).comp (continuous_unitInf (E := E) w)).continuousAt.congr ?_
  filter_upwards [h1.mem_nhds (x := 1) ⟨fun v => by simp, fun v => by simp⟩] with x hx
  rw [absE_apply, finprod_eq_one_of_forall_eq_one fun v => absEv_unitFin_eq_one (hx.1 v) (hx.2 v), mul_one]
  rfl

/- English proof (translation)
Establish `key : ∀ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R) (ψ : R →ₐ[F] R') (z : AF F ⊗[F] E), Algebra.TensorProduct.map ψ (AlgHom.id F E) (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) …` using `fun φ ψ z => by rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]`. Establish `a : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y` using `GlobalTheory.AutFunCompare.infTens_ext fun w => (key _ _ x).trans ((h1 w).trans (key _ _ y).symm)`. Establish `b : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y` using `GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => (key _ _ x).trans ((h2 v).trans (key _ _ y).symm)`. Use `GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F) (Matrix.of fun _ _ : Fin 1 => (1 + (x - y) : AF F ⊗[F] E)) (by` as an intermediate fact. Use extensionality with `i j`.

Rewrite using `[Subsingleton.elim i j, Matrix.one_apply_eq]`. Conclude with `(show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 + (x - y)) = 1 by simp [a])) (by`. Use extensionality with `i j`. Rewrite using `[Subsingleton.elim i j, Matrix.one_apply_eq]`. Conclude with `(show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (1 + (x - y)) = 1 by simp [b]))`.

Establish `h3 : (1 + (x - y) : AF F ⊗[F] E) = 1` using `congrFun (congrFun this 0) 0`. Conclude with `sub_eq_zero.1 (add_eq_left.1 h3)`.
-/
theorem adele_ext {x y : AF F ⊗[F] E} (h1 : ∀ w, compInf F E w x = compInf F E w y)
    (h2 : ∀ v, compFin F E v x = compFin F E v y) : x = y := by
  have key : ∀ {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : AF F →ₐ[F] R)
      (ψ : R →ₐ[F] R') (z : AF F ⊗[F] E), Algebra.TensorProduct.map ψ (AlgHom.id F E)
        (Algebra.TensorProduct.map φ (AlgHom.id F E) z) = Algebra.TensorProduct.map (ψ.comp φ) (AlgHom.id F E) z :=
    fun φ ψ z => by rw [← AlgHom.comp_apply, ← Algebra.TensorProduct.map_comp, AlgHom.comp_id]
  have a : Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) x = Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) y :=
    GlobalTheory.AutFunCompare.infTens_ext fun w => (key _ _ x).trans ((h1 w).trans (key _ _ y).symm)
  have b : Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) x = Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) y :=
    GlobalTheory.LatticeLocalGlobal.ext_components _ _ fun v => (key _ _ x).trans ((h2 v).trans (key _ _ y).symm)
  have := GlobalTheory.AutFunCounterexample.tens_inj (F := F) (E := E) (A := Ainf F) (B := Af F)
    (Matrix.of fun _ _ : Fin 1 => (1 + (x - y) : AF F ⊗[F] E)) (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact (show Algebra.TensorProduct.map (fstA F) (AlgHom.id F E) (1 + (x - y)) = 1 by simp [a])) (by
      ext i j
      rw [Subsingleton.elim i j, Matrix.one_apply_eq]
      exact (show Algebra.TensorProduct.map (sndA F) (AlgHom.id F E) (1 + (x - y)) = 1 by simp [b]))
  have h3 : (1 + (x - y) : AF F ⊗[F] E) = 1 := congrFun (congrFun this 0) 0
  exact sub_eq_zero.1 (add_eq_left.1 h3)

/- English proof (translation)
The claim follows from `Units.ext (adele_ext (fun w => congrArg Units.val (h1 w)) fun v => congrArg Units.val (h2 v))`.
-/
theorem idele_ext {x y : (AF F ⊗[F] E)ˣ} (h1 : ∀ w, unitInf F E w x = unitInf F E w y)
    (h2 : ∀ v, unitFin F E v x = unitFin F E v y) : x = y :=
  Units.ext (adele_ext (fun w => congrArg Units.val (h1 w)) fun v => congrArg Units.val (h2 v))

def inFin (v : HeightOneSpectrum (𝓞 F)) : Fv F v →ₗ[F] AF F := (LinearMap.inr F (Ainf F) (Af F)).comp (singleFin v)

def inInf (w : InfinitePlace F) : w.Completion →ₗ[F] AF F :=
  (LinearMap.inl F (Ainf F) (Af F)).comp (GlobalTheory.AutFunCompare.sgW w)

/- English proof (translation)
The claim follows from `Prod.ext (mul_zero _).symm (singleFin_mul v a b)`.
-/
theorem inFin_mul (v : HeightOneSpectrum (𝓞 F)) (a b : Fv F v) : inFin v (a * b) = inFin v a * inFin v b :=
  Prod.ext (mul_zero _).symm (singleFin_mul v a b)

/- English proof (translation)
The claim follows from `Prod.ext (GlobalTheory.AutFunCompare.sgW_mul w a b) (mul_zero _).symm`.
-/
theorem inInf_mul (w : InfinitePlace F) (a b : w.Completion) : inInf w (a * b) = inInf w a * inInf w b :=
  Prod.ext (GlobalTheory.AutFunCompare.sgW_mul w a b) (mul_zero _).symm

variable (F E) in

def ideleAt (v : HeightOneSpectrum (𝓞 F)) : (Fv F v ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := extUnit (inFin v) (inFin_mul v)

variable (F E) in

def ideleAtInf (w : InfinitePlace F) : (w.Completion ⊗[F] E)ˣ →* (AF F ⊗[F] E)ˣ := extUnit (inInf w) (inInf_mul w)

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `[val_extUnit, GlobalTheory.AutFunCompare.map_tensNU_self φ j hj h]`.
-/
theorem map_extUnit_self {R R' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] (φ : R' →ₐ[F] R)
    (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, φ (j a) = a) (y : (R ⊗[F] E)ˣ) :
    Algebra.TensorProduct.map φ (AlgHom.id F E) (extUnit j hj y).1 = y.1 := by
  simp [val_extUnit, GlobalTheory.AutFunCompare.map_tensNU_self φ j hj h]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Simplify using `[val_extUnit, GlobalTheory.AutFunCompare.map_tensNU_zero φ j hj h]`.
-/
theorem map_extUnit_zero {R R' R'' : Type} [CommRing R] [Algebra F R] [CommRing R'] [Algebra F R'] [CommRing R'']
    [Algebra F R''] (φ : R' →ₐ[F] R'') (j : R →ₗ[F] R') (hj : ∀ a b, j (a * b) = j a * j b) (h : ∀ a, φ (j a) = 0)
    (y : (R ⊗[F] E)ˣ) : Algebra.TensorProduct.map φ (AlgHom.id F E) (extUnit j hj y).1 = 1 := by
  simp [val_extUnit, GlobalTheory.AutFunCompare.map_tensNU_zero φ j hj h]

section Comp

omit [NumberField E]

/- English proof (translation)
The claim follows from `Units.ext (map_extUnit_self (evFin F v) _ _ (evalV_singleFin_self v) x)`.
-/
@[simp] theorem unitFin_ideleAt_self (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    unitFin F E v (ideleAt F E v x) = x := Units.ext (map_extUnit_self (evFin F v) _ _ (evalV_singleFin_self v) x)

/- English proof (translation)
The claim follows from `Units.ext (map_extUnit_zero (evFin F u) _ _ (evalV_singleFin_ne h) x)`.
-/
theorem unitFin_ideleAt_ne {v u : HeightOneSpectrum (𝓞 F)} (h : u ≠ v) (x : (Fv F v ⊗[F] E)ˣ) :
    unitFin F E u (ideleAt F E v x) = 1 := Units.ext (map_extUnit_zero (evFin F u) _ _ (evalV_singleFin_ne h) x)

/- English proof (translation)
The claim follows from `Units.ext (map_extUnit_zero (evInf F w) _ _ (fun _ => rfl) x)`.
-/
@[simp] theorem unitInf_ideleAt (w : InfinitePlace F) (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) :
    unitInf F E w (ideleAt F E v x) = 1 := Units.ext (map_extUnit_zero (evInf F w) _ _ (fun _ => rfl) x)

/- English proof (translation)
Conclude with `Units.ext (map_extUnit_self (evInf F w) _ _ (fun a => Pi.single_eq_same w a) x)`.
-/
@[simp] theorem unitInf_ideleAtInf_self (w : InfinitePlace F) (x : (w.Completion ⊗[F] E)ˣ) :
    unitInf F E w (ideleAtInf F E w x) = x := by
  classical
  exact Units.ext (map_extUnit_self (evInf F w) _ _ (fun a => Pi.single_eq_same w a) x)

/- English proof (translation)
Conclude with `Units.ext (map_extUnit_zero (evInf F u) _ _ (fun a => Pi.single_eq_of_ne h a) x)`.
-/
theorem unitInf_ideleAtInf_ne {w u : InfinitePlace F} (h : u ≠ w) (x : (w.Completion ⊗[F] E)ˣ) :
    unitInf F E u (ideleAtInf F E w x) = 1 := by
  classical
  exact Units.ext (map_extUnit_zero (evInf F u) _ _ (fun a => Pi.single_eq_of_ne h a) x)

/- English proof (translation)
The claim follows from `Units.ext (map_extUnit_zero (evFin F v) _ _ (fun _ => rfl) x)`.
-/
@[simp] theorem unitFin_ideleAtInf (v : HeightOneSpectrum (𝓞 F)) (w : InfinitePlace F) (x : (w.Completion ⊗[F] E)ˣ) :
    unitFin F E v (ideleAtInf F E w x) = 1 := Units.ext (map_extUnit_zero (evFin F v) _ _ (fun _ => rfl) x)

def charAt (μ : (AF F ⊗[F] E)ˣ →* Circle) (v : HeightOneSpectrum (𝓞 F)) : (Fv F v ⊗[F] E)ˣ →* Circle :=
  μ.comp (ideleAt F E v)

def charAtInf (μ : (AF F ⊗[F] E)ˣ →* Circle) (w : InfinitePlace F) : (w.Completion ⊗[F] E)ˣ →* Circle :=
  μ.comp (ideleAtInf F E w)

end Comp

/- English proof (translation)
The claim follows from `continuous_extUnit _ _ (continuous_const.prodMk (continuous_singleFin v))`.
-/
theorem continuous_ideleAt (v : HeightOneSpectrum (𝓞 F)) : Continuous (ideleAt F E v) :=
  continuous_extUnit _ _ (continuous_const.prodMk (continuous_singleFin v))

/- English proof (translation)
Rewrite using `[absE_apply, finprod_eq_single _ v fun u hu => by rw [unitFin_ideleAt_ne hu, map_one]]`. Simplify using the standard rewrite rules.
-/
theorem absE_ideleAt (v : HeightOneSpectrum (𝓞 F)) (x : (Fv F v ⊗[F] E)ˣ) : absE F E (ideleAt F E v x) = absEv F E v x := by
  rw [absE_apply, finprod_eq_single _ v fun u hu => by rw [unitFin_ideleAt_ne hu, map_one]]
  simp

/- English proof (translation)
Rewrite using `[absE_apply, Finset.prod_eq_single w (fun u _ hu => by rw [unitInf_ideleAtInf_ne hu, map_one]) (by simp)]`. Simplify using the standard rewrite rules.
-/
theorem absE_ideleAtInf (w : InfinitePlace F) (x : (w.Completion ⊗[F] E)ˣ) :
    absE F E (ideleAtInf F E w x) = absEw F E w x := by
  rw [absE_apply, Finset.prod_eq_single w (fun u _ hu => by rw [unitInf_ideleAtInf_ne hu, map_one]) (by simp)]
  simp

/- English proof (translation)
Rewrite using `[absEv_algebraMap, h, ← inv_pow]`. Use `congr 1`. Use `NNReal.eq ?_` and prove the remaining obligations. Rewrite using `[coe_nnnorm, FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]`. Conclude with `congrArg NNReal.toReal (zpow_neg_one _)`.
-/
example (h : Module.finrank F E = 2) (v : HeightOneSpectrum (𝓞 F)) (ϖ : (Fv F v)ˣ)
    (hϖ : Valued.v ϖ.1 = WithZero.exp (-1 : ℤ)) :
    absEv F E v (Units.map (algebraMap (Fv F v) (Fv F v ⊗[F] E)).toMonoidHom ϖ) =
      ((Ideal.absNorm v.asIdeal : ℝ≥0) ^ 2)⁻¹ := by
  rw [absEv_algebraMap, h, ← inv_pow]
  congr 1
  refine NNReal.eq ?_
  rw [coe_nnnorm, FinitePlace.norm_def, hϖ, WithZeroMulInt.toNNReal_neg_apply _ WithZero.exp_ne_zero]
  exact congrArg NNReal.toReal (zpow_neg_one _)

end GlobalTheory.Doubling

end
