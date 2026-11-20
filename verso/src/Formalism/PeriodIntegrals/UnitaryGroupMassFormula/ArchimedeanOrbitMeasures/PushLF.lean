import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.ArchimedeanOrbitMeasures.PushInv

noncomputable section

namespace PI.AprimeInfW

open scoped TensorProduct
open MeasureTheory NumberField Topology Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.TypedSets Matrix

section Lin

def LIP (R : Type) [CommRing R] : Prop :=
  ∀ (m n : Type) [Fintype m] [Fintype n] [DecidableEq m] [DecidableEq n] (W : Matrix m n R),
    (∀ c, W *ᵥ c = 0 → c = 0) → ∃ P : Matrix n m R, P * W = 1

/- English proof (translation)
Introduce `m n _ _ _ _ W hW`. Establish `hk : LinearMap.ker (Matrix.toLin' W) = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `c hc`. Conclude with `hW c (by simpa [Matrix.toLin'_apply] using hc)`.

Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hk`. Use `⟨LinearMap.toMatrix' g, ?_⟩` and prove the remaining obligations. Establish `h1 : Matrix.toLin' (LinearMap.toMatrix' g * W) = LinearMap.id`. Rewrite using `[Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg]`. Establish `h2` using `congrArg LinearMap.toMatrix' h1`.

Rewrite `h2` using `[LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id]`. Then use the resulting hypothesis.
-/
theorem lip_field (K : Type) [Field K] : LIP K := by
  intro m n _ _ _ _ W hW
  have hk : LinearMap.ker (Matrix.toLin' W) = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro c hc
    exact hW c (by simpa [Matrix.toLin'_apply] using hc)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Matrix.toLin' W) hk
  refine ⟨LinearMap.toMatrix' g, ?_⟩
  have h1 : Matrix.toLin' (LinearMap.toMatrix' g * W) = LinearMap.id := by
    rw [Matrix.toLin'_mul, Matrix.toLin'_toMatrix', hg]
  have h2 := congrArg LinearMap.toMatrix' h1
  rwa [LinearMap.toMatrix'_toLin', LinearMap.toMatrix'_id] at h2

/- English proof (translation)
Introduce `m n _ _ _ _ W hW`. Establish `hv : ∀ v, ∃ P : Matrix n m (K v), P * W.map (fun x => x v) = 1`. Introduce `v`. Use `h v m n _ ?_` and prove the remaining obligations. Introduce `c hc`.

Establish `key : W *ᵥ (fun j => Pi.single v (c j)) = 0`. Use function extensionality and compare the values at `i v'`. Simplify using `only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply]`. Distinguish the cases in `hv' : v' = v`. Substitute `hv'` using the available equality.

Use `congrFun hc i` as an intermediate fact. Simplify `this` using `[Matrix.mulVec, dotProduct, Matrix.map_apply]`. Simplify using `[hv']`. Establish `h0` using `hW _ key`. Use function extensionality and compare the values at `j`.

Use `congrFun (congrFun h0 j) v` as an intermediate fact. Simplify using `using this`. Use `choose P hP using hv`. Set `Q : Matrix n m (∀ v, K v)` to `fun i j v => P v i j`. Use `⟨Q, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i j v`. Use `congrFun (congrFun (hP v) i) j` as an intermediate fact. Simplify using `only [Matrix.mul_apply, Matrix.map_apply] at this`. Rewrite using `[Matrix.mul_apply, Finset.sum_apply]`. Use `show ∑ k, P v i k * W k j v = _`.

Rewrite using `[this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
theorem lip_pi {ι : Type} [Fintype ι] [DecidableEq ι] (K : ι → Type) [∀ i, CommRing (K i)]
    (h : ∀ i, LIP (K i)) : LIP (∀ i, K i) := by
  intro m n _ _ _ _ W hW
  have hv : ∀ v, ∃ P : Matrix n m (K v), P * W.map (fun x => x v) = 1 := by
    intro v
    refine h v m n _ ?_
    intro c hc
    have key : W *ᵥ (fun j => Pi.single v (c j)) = 0 := by
      funext i v'
      simp only [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.mul_apply, Pi.zero_apply]
      by_cases hv' : v' = v
      · subst hv'
        have := congrFun hc i
        simpa [Matrix.mulVec, dotProduct, Matrix.map_apply] using this
      · simp [hv']
    have h0 := hW _ key
    funext j
    have := congrFun (congrFun h0 j) v
    simpa using this
  choose P hP using hv
  let Q : Matrix n m (∀ v, K v) := fun i j v => P v i j
  refine ⟨Q, ?_⟩
  funext i j v
  have := congrFun (congrFun (hP v) i) j
  simp only [Matrix.mul_apply, Matrix.map_apply] at this
  rw [Matrix.mul_apply, Finset.sum_apply]
  show ∑ k, P v i k * W k j v = _
  rw [this]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Establish `h1 : (P * W) *ᵥ c = 0` using `by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]`. Take `⟨u, hu⟩` from `(Matrix.isUnit_iff_isUnit_det _).2 hP`. Establish `h2 : ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ ((P * W) *ᵥ c) = c`. Rewrite using `[Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]`. Rewrite using `[← h2, h1, Matrix.mulVec_zero]`.
-/
theorem inj_of_isUnit {R : Type} [CommRing R] {m n : Type} [Fintype m] [Fintype n]
    [DecidableEq n] (W : Matrix m n R) (P : Matrix n m R) (hP : IsUnit (P * W).det)
    (c : n → R) (hc : W *ᵥ c = 0) : c = 0 := by
  have h1 : (P * W) *ᵥ c = 0 := by rw [← Matrix.mulVec_mulVec, hc, Matrix.mulVec_zero]
  obtain ⟨u, hu⟩ := (Matrix.isUnit_iff_isUnit_det _).2 hP
  have h2 : ((u⁻¹ : (Matrix n n R)ˣ) : Matrix n n R) *ᵥ ((P * W) *ᵥ c) = c := by
    rw [Matrix.mulVec_mulVec, ← hu, Units.inv_mul, Matrix.one_mulVec]
  rw [← h2, h1, Matrix.mulVec_zero]

variable {F E : Type} [Field F] [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E)

def crd (R : Type) [CommRing R] [Algebra F R] (y : R ⊗[F] E) (k : Fin d) : R :=
  (Algebra.TensorProduct.basis R b).repr y k

/- English proof (translation)
The claim follows from `IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)`.
-/
theorem continuous_crd (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [FiniteDimensional F E]
    [IsTopologicalRing R] (k : Fin d) : Continuous (fun y : R ⊗[F] E => crd b R y k) :=
  IsModuleTopology.continuous_of_linearMap ((Algebra.TensorProduct.basis R b).coord k)

def wMat (R : Type) [CommRing R] [Algebra F R] {a M : ℕ} (X : Fin a → Fin M → R ⊗[F] E) :
    Matrix (Fin M × Fin d) (Fin a × Fin d) R :=
  fun p q => crd b R (((1 : R) ⊗ₜ[F] b q.2) * X q.1 p.1) p.2

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, wMat, crd, Fintype.sum_prod_type, Finset.sum_mul, smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply, Finsupp.smul_apply, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _`.
-/
theorem wMat_mulVec (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) (j : Fin M) (l : Fin d) :
    (wMat b R X *ᵥ c) (j, l) =
      crd b R (∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j) l := by
  simp only [Matrix.mulVec, dotProduct, wMat, crd, Fintype.sum_prod_type, Finset.sum_mul,
    smul_mul_assoc, map_sum, map_smul, Finsupp.coe_finsetSum, Finset.sum_apply,
    Finsupp.smul_apply, smul_eq_mul]
  exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun k _ => mul_comm _ _

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h j`. Apply `(Algebra.TensorProduct.basis R b).repr.injective` to reduce the goal to its premises. Use extensionality with `l`. Use `congrFun h (j, l)` as an intermediate fact.

Rewrite `this` using `[wMat_mulVec]`. Simplify `this` using `[crd]`. Introduce `h`. Use function extensionality and compare the values at `p`. Rewrite using `[wMat_mulVec, h p.1]`.

Simplify using `[crd]`.
-/
theorem wMat_mulVec_eq_zero (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) (c : Fin a × Fin d → R) :
    wMat b R X *ᵥ c = 0 ↔ ∀ j, ∑ i, (∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) * X i j = 0 := by
  constructor
  · intro h j
    apply (Algebra.TensorProduct.basis R b).repr.injective
    ext l
    have := congrFun h (j, l)
    rw [wMat_mulVec] at this
    simpa [crd] using this
  · intro h
    funext p
    rw [wMat_mulVec, h p.1]
    simp [crd]

/- English proof (translation)
Use `set B := Algebra.TensorProduct.basis R b with hB`. Establish `hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k` using `fun k => Algebra.TensorProduct.basis_apply _ _`. Rewrite using `[Fintype.linearIndependent_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `hX c hc`.

Rewrite `hc` using `[wMat_mulVec_eq_zero]`. Establish `h0` using `hX (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by`. Use function extensionality and compare the values at `j`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]`. Conclude with `hc j)`.

Use function extensionality and compare the values at `p`. Establish `h1` using `h0 p.1`. Establish `h2 : B.equivFun (∑ k, c (p.1, k) • B k) = fun k => c (p.1, k)`. Rewrite using `[← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]`. Simplify using `only [hBk] at h2`.

Rewrite `h2` using `[h1, map_zero]`. Conclude with `(congrFun h2 p.2).symm`. Introduce `hW g hg i`. Establish `hc` using `hW (fun p => B.repr (g p.1) p.2) (by`. Rewrite using `[wMat_mulVec_eq_zero]`.

Introduce `j`. Establish `e : ∀ i, ∑ k, B.repr (g i) k • ((1 : R) ⊗ₜ[F] b k) = g i`. Introduce `i`. Simplify using `only [← hBk]`. Conclude with `B.sum_repr (g i)`.

Simplify using `only [e]`. Use `congrFun hg j` as an intermediate fact. Simplify `this)` using `[Finset.sum_apply, smul_eq_mul]`. Rewrite using `[← B.sum_repr (g i)]`. Simplify using `[fun k => congrFun hc (i, k)]`.
-/
theorem linIndep_iff (R : Type) [CommRing R] [Algebra F R] {a M : ℕ}
    (X : Fin a → Fin M → R ⊗[F] E) :
    LinearIndependent (R ⊗[F] E) X ↔ ∀ c, wMat b R X *ᵥ c = 0 → c = 0 := by
  set B := Algebra.TensorProduct.basis R b with hB
  have hBk : ∀ k, B k = (1 : R) ⊗ₜ[F] b k := fun k => Algebra.TensorProduct.basis_apply _ _
  rw [Fintype.linearIndependent_iff]
  constructor
  · intro hX c hc
    rw [wMat_mulVec_eq_zero] at hc
    have h0 := hX (fun i => ∑ k, c (i, k) • ((1 : R) ⊗ₜ[F] b k)) (by
      funext j
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply]
      exact hc j)
    funext p
    have h1 := h0 p.1
    have h2 : B.equivFun (∑ k, c (p.1, k) • B k) = fun k => c (p.1, k) := by
      rw [← Module.Basis.equivFun_symm_apply, LinearEquiv.apply_symm_apply]
    simp only [hBk] at h2
    rw [h1, map_zero] at h2
    exact (congrFun h2 p.2).symm
  · intro hW g hg i
    have hc := hW (fun p => B.repr (g p.1) p.2) (by
      rw [wMat_mulVec_eq_zero]
      intro j
      have e : ∀ i, ∑ k, B.repr (g i) k • ((1 : R) ⊗ₜ[F] b k) = g i := by
        intro i
        simp only [← hBk]
        exact B.sum_repr (g i)
      simp only [e]
      have := congrFun hg j
      simpa [Finset.sum_apply, smul_eq_mul] using this)
    rw [← B.sum_repr (g i)]
    simp [fun k => congrFun hc (i, k)]

section Top

variable [FiniteDimensional F E] (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R]
  [IsTopologicalRing R]

/- English proof (translation)
Use `continuous_pi fun p => continuous_pi fun q => ?_` and prove the remaining obligations. Conclude with `(continuous_crd b R p.2).comp (continuous_const.mul ((continuous_apply p.1).comp (continuous_apply q.1)))`.
-/
theorem continuous_wMat {a M : ℕ} :
    Continuous (fun X : Fin a → Fin M → R ⊗[F] E => wMat b R X) := by
  refine continuous_pi fun p => continuous_pi fun q => ?_
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

end Top

end Lin

/- English proof (translation)
Conclude with `lip_pi (fun v : InfinitePlace F => v.Completion) (fun v => lip_field _)`.
-/
theorem lip_ainf (F : Type) [Field F] [NumberField F] : LIP (InfiniteAdeleRing F) := by
  classical
  exact lip_pi (fun v : InfinitePlace F => v.Completion) (fun v => lip_field _)

/- English proof (translation)
Use `show IsOpen {y : (v : InfinitePlace F) → v.Completion | IsUnit y}`. Establish `: {y : (v : InfinitePlace F) → v.Completion | IsUnit y} = ⋂ v, (fun y : (v : InfinitePlace F) → v.Completion => y v) ⁻¹' {z | z ≠ 0}`. Use extensionality with `y`. Simplify using `only [Set.mem_iInter, Set.mem_preimage]`. Use `show IsUnit y ↔ ∀ v, y v ≠ 0`.

Rewrite using `[Pi.isUnit_iff]`. Simplify using `only [isUnit_iff_ne_zero]`. Rewrite using `[this]`. Conclude with `isOpen_iInter_of_finite fun v => isOpen_ne.preimage (continuous_apply v)`.
-/
theorem isOpen_units_Ainf (F : Type) [Field F] [NumberField F] : IsOpen {x : InfiniteAdeleRing F | IsUnit x} := by
  show IsOpen {y : (v : InfinitePlace F) → v.Completion | IsUnit y}
  have : {y : (v : InfinitePlace F) → v.Completion | IsUnit y} =
      ⋂ v, (fun y : (v : InfinitePlace F) → v.Completion => y v) ⁻¹' {z | z ≠ 0} := by
    ext y
    simp only [Set.mem_iInter, Set.mem_preimage]
    show IsUnit y ↔ ∀ v, y v ≠ 0
    rw [Pi.isUnit_iff]; simp only [isUnit_iff_ne_zero]
  rw [this]; exact isOpen_iInter_of_finite fun v => isOpen_ne.preimage (continuous_apply v)

/- English proof (translation)
Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Conclude with `isOpen_linIndep (Module.finBasis X.B.I.F X.B.I.E) (Ainf X.B.I.F) (isOpen_units_Ainf _) (lip_ainf _)`.
-/
theorem isOpen_IndI {D : D7} (X : HidaSetting D) : IsOpen (IndI X) := by
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  exact isOpen_linIndep (Module.finBasis X.B.I.F X.B.I.E) (Ainf X.B.I.F) (isOpen_units_Ainf _) (lip_ainf _)

section LC

variable {F E : Type} [Field F] [Field E] [Algebra F E] [FiniteDimensional F E]
variable (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [IsTopologicalRing R]
  [LocallyCompactSpace R] [T2Space R]

instance locallyCompactSpace_tensP : LocallyCompactSpace (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isClosedEmbedding.locallyCompactSpace

instance t2Space_tensorProduct : T2Space (R ⊗[F] E) := by
  obtain ⟨ι, _, ⟨h⟩⟩ := exists_homeomorph_tensP (F := F) (E := E) R
  exact h.isEmbedding.t2Space

end LC

instance t2Space_infiniteAdeleRing_archimedean_orbit_measures (F : Type) [Field F] [NumberField F] : T2Space (InfiniteAdeleRing F) :=
  inferInstanceAs (T2Space (∀ v : InfinitePlace F, v.Completion))

/- English proof (translation)
Introduce `D X u' ψ hT μinf νinf fibInf hP K hK hKU`. Use `haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X`. Take `⟨k, -, hkcl, hKk, hkU⟩` from `exists_compact_closed_between hK (isOpen_IndI X) hKU`. Take `⟨f, hf1, hf0, hfc, -⟩` from `exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl (Set.disjoint_compl_right_iff_subset.mpr hKk)`. Establish `hts : tsupport f ⊆ IndI X`.

Use `(closure_minimal ?_ hkcl).trans hkU` and prove the remaining obligations. Introduce `y hy`. Assume the negation of the conclusion as `h`. Conclude with `hy (hf0 (fun h' => h (interior_subset h')))`. Establish `hI` using `((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 (TI X u' hT) (Set.mem_univ _)`.

Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Set.mem_ofPred_eq]`. Rewrite using `[hf1 hy]`. Simplify using the standard rewrite rules. Use `_ = 1 * fibInf (TI X u' hT) {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm`.

Use `_ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf (TI X u' hT)) := mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1`. Use `_ < ⊤ := hI.lintegral_lt_top`.
-/
theorem lfFib_holds : LFFib := by
  intro D X u' ψ hT μinf νinf fibInf hP K hK hKU
  haveI : FiniteDimensional X.B.I.F X.B.I.E := fd_of X
  obtain ⟨k, -, hkcl, hKk, hkU⟩ := exists_compact_closed_between hK (isOpen_IndI X) hKU
  obtain ⟨f, hf1, hf0, hfc, -⟩ := exists_continuous_one_zero_of_isCompact hK isOpen_interior.isClosed_compl
    (Set.disjoint_compl_right_iff_subset.mpr hKk)
  have hts : tsupport f ⊆ IndI X := by
    refine (closure_minimal ?_ hkcl).trans hkU
    intro y hy
    by_contra h
    exact hy (hf0 (fun h' => h (interior_subset h')))
  have hI := ((hP.2.2.2.2.2.2).2.2 f f.continuous hfc hts).1 (TI X u' hT) (Set.mem_univ _)
  calc fibInf (TI X u' hT) K ≤ fibInf (TI X u' hT) {y | 1 ≤ ENNReal.ofReal (f y)} :=
        measure_mono fun y hy => by
          simp only [Set.mem_ofPred_eq]
          rw [hf1 hy]
          simp
    _ = 1 * fibInf (TI X u' hT) {y | 1 ≤ ENNReal.ofReal (f y)} := (one_mul _).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (f y) ∂(fibInf (TI X u' hT)) :=
        mul_meas_ge_le_lintegral₀ f.continuous.measurable.ennreal_ofReal.aemeasurable 1
    _ < ⊤ := hI.lintegral_lt_top

end PI.AprimeInfW
