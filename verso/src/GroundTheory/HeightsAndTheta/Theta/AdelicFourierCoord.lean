import Mathlib
import CompanionTheory.AutomorphicTheory.UnitriangularMeasure.AdeleCoordinateMeasure.GJGlobalModulus
import GroundTheory.AutomorphicForms.GL2.GJGlobalDefs
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Theta

open GroundTheory.Global GroundTheory.Automorphic.GJMatrix NumberField NumberField.mixedEmbedding
  IsDedekindDomain MeasureTheory Measure Matrix
open scoped NumberField.AdeleRing ENNReal NNReal SchwartzMap Classical

noncomputable section

set_option synthInstance.maxSize 1000
set_option linter.unusedSectionVars false

variable {K : Type*} [Field K] [NumberField K] {ι κ : Type*} [Fintype ι] [Fintype κ]

/- English proof (translation)
Establish `hm : Measurable (fun x : ι → α ↦ x ∘ e)` using `measurable_pi_lambda _ fun k ↦ measurable_pi_apply (e k)`. Use `⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hm (MeasurableSet.univ_pi hs)]`. Establish `hpre : (fun x : ι → α ↦ x ∘ e) ⁻¹' Set.pi Set.univ s = Set.pi Set.univ (fun i ↦ s (e.symm i))`. Use extensionality with `x`.

Simplify using `only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]`. Conclude with `⟨fun h i ↦ by simpa using h (e.symm i), fun h k ↦ by simpa using h (e k)⟩`. Rewrite using `[hpre, Measure.pi_pi]`. Conclude with `Fintype.prod_equiv e.symm _ _ fun _ ↦ rfl`.
-/
theorem measurePreserving_comp_equiv {α : Type*} [MeasurableSpace α] (μ : Measure α)
    [SigmaFinite μ] (e : κ ≃ ι) :
    MeasurePreserving (fun x : ι → α ↦ x ∘ e) (Measure.pi fun _ ↦ μ)
      (Measure.pi fun _ ↦ μ) := by
  have hm : Measurable (fun x : ι → α ↦ x ∘ e) :=
    measurable_pi_lambda _ fun k ↦ measurable_pi_apply (e k)
  refine ⟨hm, (Measure.pi_eq fun s hs ↦ ?_).symm⟩
  rw [Measure.map_apply hm (MeasurableSet.univ_pi hs)]
  have hpre : (fun x : ι → α ↦ x ∘ e) ⁻¹' Set.pi Set.univ s =
      Set.pi Set.univ (fun i ↦ s (e.symm i)) := by
    ext x
    simp only [Set.mem_preimage, Set.mem_univ_pi, Function.comp_apply]
    exact ⟨fun h i ↦ by simpa using h (e.symm i), fun h k ↦ by simpa using h (e k)⟩
  rw [hpre, Measure.pi_pi]
  exact Fintype.prod_equiv e.symm _ _ fun _ ↦ rfl

def adeleInfHom : 𝔸[K] →+* mixedSpace K :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace K).toRingHom.comp
    (RingHom.fst (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K))

def adeleFinHom : 𝔸[K] →+* 𝔸ᶠ[K] :=
  RingHom.snd (InfiniteAdeleRing K) (FiniteAdeleRing (𝓞 K) K)

omit [Fintype ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem infPartPi_eq_adeleInfHom (x : ι → 𝔸[K]) : infPartPi x = fun i ↦ adeleInfHom (x i) := rfl

omit [Fintype ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem finPartPi_eq_adeleFinHom (x : ι → 𝔸[K]) : finPartPi x = fun i ↦ adeleFinHom (x i) := rfl

/- English proof (translation)
Express the relevant statement in the definitionally equal form `homeomorphMixedSpace K (algebraMap K 𝔸[K] k).1 = _`. Simplify using `only [adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]`.
-/
theorem adeleInfHom_algebraMap (k : K) :
    adeleInfHom (algebraMap K 𝔸[K] k) = mixedEmbedding K k := by
  change homeomorphMixedSpace K (algebraMap K 𝔸[K] k).1 = _
  simp only [adeleRing_algebraMap_fst, homeomorphMixedSpace_algebraMap]

/- English proof (translation)
Express the relevant statement in the definitionally equal form `(algebraMap K 𝔸[K] k).2 = _`. Simplify using `only [adeleRing_algebraMap_snd]`.
-/
theorem adeleFinHom_algebraMap (k : K) :
    adeleFinHom (algebraMap K 𝔸[K] k) = algebraMap K 𝔸ᶠ[K] k := by
  change (algebraMap K 𝔸[K] k).2 = _
  simp only [adeleRing_algebraMap_snd]

variable [DecidableEq ι] [DecidableEq κ]

/- English proof (translation)
The claim follows from `funext fun k ↦ RingHom.map_mulVec h M x k`.
-/
theorem map_mulVec_eq {R S : Type*} [CommRing R] [CommRing S] (h : R →+* S) (M : Matrix κ ι R)
    (x : ι → R) : (fun k ↦ h ((M *ᵥ x) k)) = M.map h *ᵥ fun i ↦ h (x i) :=
  funext fun k ↦ RingHom.map_mulVec h M x k

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, h, Matrix.map_one f (map_zero f) (map_one f)]`.
-/
theorem map_mul_map_eq_one {R : Type*} [CommRing R] (f : K →+* R) {A : Matrix κ ι K}
    {B : Matrix ι κ K} (h : A * B = 1) : A.map f * B.map f = 1 := by
  rw [← Matrix.map_mul, h, Matrix.map_one f (map_zero f) (map_one f)]

variable (M : Matrix κ ι K) (N : Matrix ι κ K)

def mulVecHomeomorph (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]
    [IsTopologicalRing R] (hNM : N * M = 1) (hMN : M * N = 1) : (ι → R) ≃ₜ (κ → R) where
  toFun u := M.map (algebraMap K R) *ᵥ u
  invFun u := N.map (algebraMap K R) *ᵥ u
  left_inv u := by
    simp only [Matrix.mulVec_mulVec, map_mul_map_eq_one _ hNM, Matrix.one_mulVec]
  right_inv u := by
    simp only [Matrix.mulVec_mulVec, map_mul_map_eq_one _ hMN, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulVecHomeomorph_apply (R : Type*) [CommRing R] [Algebra K R] [TopologicalSpace R]
    [IsTopologicalRing R] (hNM : N * M = 1) (hMN : M * N = 1) (u : ι → R) :
    mulVecHomeomorph M N R hNM hMN u = M.map (algebraMap K R) *ᵥ u := rfl

def mixedMulVecEquiv (hNM : N * M = 1) (hMN : M * N = 1) :
    (ι → mixedSpace K) ≃L[ℝ] (κ → mixedSpace K) :=
  LinearEquiv.toContinuousLinearEquiv
    { toFun := fun u ↦ M.map (mixedEmbedding K) *ᵥ u
      invFun := fun u ↦ N.map (mixedEmbedding K) *ᵥ u
      map_add' := fun u v ↦ Matrix.mulVec_add _ u v
      map_smul' := fun c u ↦ Matrix.mulVec_smul _ c u
      left_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_mul_map_eq_one _ hNM, Matrix.one_mulVec]
      right_inv := fun u ↦ by
        simp only [Matrix.mulVec_mulVec, map_mul_map_eq_one _ hMN, Matrix.one_mulVec] }

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mixedMulVecEquiv_apply (hNM : N * M = 1) (hMN : M * N = 1) (u : ι → mixedSpace K) :
    mixedMulVecEquiv M N hNM hMN u = M.map (mixedEmbedding K) *ᵥ u := rfl

/- English proof (translation)
Establish `h : (⇑adeleInfHom ∘ ⇑(algebraMap K 𝔸[K])) = mixedEmbedding K`. Use function extensionality and compare the values at `adeleInfHom_algebraMap`. Rewrite using `[infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq, Matrix.map_map, h, mixedMulVecEquiv_apply]`.
-/
theorem infPartPi_mulVec (hNM : N * M = 1) (hMN : M * N = 1) (x : ι → 𝔸[K]) :
    infPartPi (M.map (algebraMap K 𝔸[K]) *ᵥ x) =
      mixedMulVecEquiv M N hNM hMN (infPartPi x) := by
  have h : (⇑adeleInfHom ∘ ⇑(algebraMap K 𝔸[K])) = mixedEmbedding K :=
    funext adeleInfHom_algebraMap
  rw [infPartPi_eq_adeleInfHom, infPartPi_eq_adeleInfHom, map_mulVec_eq, Matrix.map_map, h,
    mixedMulVecEquiv_apply]

/- English proof (translation)
Establish `h : (⇑adeleFinHom ∘ ⇑(algebraMap K 𝔸[K])) = algebraMap K 𝔸ᶠ[K]`. Use function extensionality and compare the values at `adeleFinHom_algebraMap`. Rewrite using `[finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq, Matrix.map_map, h, mulVecHomeomorph_apply]`.
-/
theorem finPartPi_mulVec (hNM : N * M = 1) (hMN : M * N = 1) (x : ι → 𝔸[K]) :
    finPartPi (M.map (algebraMap K 𝔸[K]) *ᵥ x) =
      mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN (finPartPi x) := by
  have h : (⇑adeleFinHom ∘ ⇑(algebraMap K 𝔸[K])) = algebraMap K 𝔸ᶠ[K] :=
    funext adeleFinHom_algebraMap
  rw [finPartPi_eq_adeleFinHom, finPartPi_eq_adeleFinHom, map_mulVec_eq, Matrix.map_map, h,
    mulVecHomeomorph_apply]

/- English proof (translation)
Proceed by induction on `hF using Submodule.span_induction with`. Consider the case `mem G hG`. Take `⟨φ, g, hg, rfl⟩` from `hG`. Establish `h : (fun x ↦ schwartzBruhatTensorPi φ g (M.map (algebraMap K 𝔸[K]) *ᵥ x)) = schwartzBruhatTensorPi (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedMulVecEquiv M N hNM hMN) φ) (g ∘ mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN)`. Use function extensionality and compare the values at `x`.

Simplify using `only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, infPartPi_mulVec M N hNM hMN, finPartPi_mulVec M N hNM hMN]`. Rewrite using `[h]`. Use `schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi K).2 ⟨?_, ?_⟩)` and prove the remaining obligations. Conclude with `((mem_finiteSchwartzBruhatPi K).1 hg).1.comp_continuous (mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN).continuous`. Conclude with `((mem_finiteSchwartzBruhatPi K).1 hg).2.comp_homeomorph (mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN)`.

Consider the case `zero => exact zero_mem _`. Consider the case `add G H _ _ hG hH => exact add_mem hG hH`. Consider the case `smul c G _ hG => exact Submodule.smul_mem _ c hG`.
-/
theorem comp_mulVec_mem_schwartzBruhatPi (hNM : N * M = 1) (hMN : M * N = 1)
    {F : (κ → 𝔸[K]) → ℂ} (hF : F ∈ schwartzBruhatPi K κ) :
    (fun x ↦ F (M.map (algebraMap K 𝔸[K]) *ᵥ x)) ∈ schwartzBruhatPi K ι := by
  induction hF using Submodule.span_induction with
  | mem G hG =>
    obtain ⟨φ, g, hg, rfl⟩ := hG
    have h : (fun x ↦ schwartzBruhatTensorPi φ g (M.map (algebraMap K 𝔸[K]) *ᵥ x)) =
        schwartzBruhatTensorPi
          (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mixedMulVecEquiv M N hNM hMN) φ)
          (g ∘ mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN) := by
      funext x
      simp only [schwartzBruhatTensorPi, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
        Function.comp_apply, infPartPi_mulVec M N hNM hMN, finPartPi_mulVec M N hNM hMN]
    rw [h]
    refine schwartzBruhatTensorPi_mem _ ((mem_finiteSchwartzBruhatPi K).2 ⟨?_, ?_⟩)
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).1.comp_continuous
        (mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN).continuous
    · exact ((mem_finiteSchwartzBruhatPi K).1 hg).2.comp_homeomorph
        (mulVecHomeomorph M N 𝔸ᶠ[K] hNM hMN)
  | zero => exact zero_mem _
  | add G H _ _ hG hH => exact add_mem hG hH
  | smul c G _ hG => exact Submodule.smul_mem _ c hG

omit [Fintype κ] [DecidableEq ι] [DecidableEq κ] in

/- English proof (translation)
Use `set A := M.map (algebraMap K 𝔸[K])`. Use `set B := N.map (algebraMap K 𝔸[K])`. Set `g : GL (Fin n) 𝔸[K]` to `⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, map_mul_map_eq_one _ hNM, Matrix.transpose_one], by rw [← Matrix.transpose_mul, map_mul_map_eq_one _ hMN, Matrix.transpose_one]⟩`. Establish `hdetM : M.det ≠ 0`. Introduce `h`.

Use `congrArg Matrix.det hNM` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, h, mul_zero, Matrix.det_one]`. Conclude with `zero_ne_one this`. Establish `hdet : Matrix.GeneralLinearGroup.det g = IdeleGroup.diagonal K (Units.mk0 M.det hdetM)`. Use `ext`.

Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, IdeleGroup.coe_diagonal, Units.val_mk0]`. Express the relevant statement in the definitionally equal form `(Aᵀ).det = _`. Rewrite using `[Matrix.det_transpose, RingHom.map_det]`. Both sides reduce to the same expression. Establish `hmap` using `GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g`.

Rewrite `hmap` using `[hdet, IdeleGroup.ideleModule_diagonal]`. Establish `hfun : (fun x : Fin n → 𝔸[K] ↦ x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) = fun x ↦ A *ᵥ x`. Use function extensionality and compare the values at `x`. Conclude with `Matrix.vecMul_transpose A x`. Rewrite `hmap` using `[hfun]`.

Use `⟨(continuous_const.matrix_mulVec continuous_id).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[hmap]`. Simplify using the standard rewrite rules.
-/
theorem measurePreserving_mulVec_fin {n : ℕ} (M N : Matrix (Fin n) (Fin n) K) (hNM : N * M = 1)
    (hMN : M * N = 1) :
    MeasurePreserving (fun x : Fin n → 𝔸[K] ↦ M.map (algebraMap K 𝔸[K]) *ᵥ x)
      (adeleMeasurePi K) (adeleMeasurePi K) := by
  set A := M.map (algebraMap K 𝔸[K])
  set B := N.map (algebraMap K 𝔸[K])
  let g : GL (Fin n) 𝔸[K] :=
    ⟨Aᵀ, Bᵀ, by rw [← Matrix.transpose_mul, map_mul_map_eq_one _ hNM, Matrix.transpose_one],
      by rw [← Matrix.transpose_mul, map_mul_map_eq_one _ hMN, Matrix.transpose_one]⟩
  have hdetM : M.det ≠ 0 := by
    intro h
    have := congrArg Matrix.det hNM
    rw [Matrix.det_mul, h, mul_zero, Matrix.det_one] at this
    exact zero_ne_one this
  have hdet : Matrix.GeneralLinearGroup.det g = IdeleGroup.diagonal K (Units.mk0 M.det hdetM) := by
    ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, IdeleGroup.coe_diagonal, Units.val_mk0]
    change (Aᵀ).det = _
    rw [Matrix.det_transpose, RingHom.map_det]
    rfl
  have hmap := GroundTheory.Automorphic.GJGlobal.Modulus.map_vecMul_adeleMeasurePi g
  rw [hdet, IdeleGroup.ideleModule_diagonal] at hmap
  have hfun : (fun x : Fin n → 𝔸[K] ↦ x ᵥ* (g : Matrix (Fin n) (Fin n) 𝔸[K])) =
      fun x ↦ A *ᵥ x := by
    funext x
    exact Matrix.vecMul_transpose A x
  rw [hfun] at hmap
  refine ⟨(continuous_const.matrix_mulVec continuous_id).measurable, ?_⟩
  rw [hmap]
  simp

/- English proof (translation)
Establish `hcard : Fintype.card κ = Fintype.card ι`. Set `e : (ι → K) ≃ₗ[K] (κ → K)` to `LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' N) (by rw [← Matrix.toLin'_mul, hMN, Matrix.toLin'_one]) (by rw [← Matrix.toLin'_mul, hNM, Matrix.toLin'_one])`. Establish `h` using `e.finrank_eq`. Rewrite `h` using `[Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card]`. Conclude with `h.symm`.

Use `set τ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι`. Use `set ρ : κ ≃ Fin (Fintype.card ι) := (Fintype.equivFin κ).trans (finCongr hcard)`. Use `set P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K := M.submatrix ρ.symm τ.symm`. Use `set Q : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K := N.submatrix τ.symm ρ.symm`. Establish `hQP : Q * P = 1`.

Rewrite using `[Matrix.submatrix_mul_equiv, hNM, Matrix.submatrix_one_equiv]`. Establish `hPQ : P * Q = 1`. Rewrite using `[Matrix.submatrix_mul_equiv, hMN, Matrix.submatrix_one_equiv]`. Establish `h1 : MeasurePreserving (fun x : ι → 𝔸[K] ↦ x ∘ τ.symm) (adeleMeasurePi K) (adeleMeasurePi K)` using `measurePreserving_comp_equiv (adeleMeasure K) τ.symm`. Establish `h2` using `measurePreserving_mulVec_fin P Q hQP hPQ`.

Establish `h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[K] ↦ x ∘ ρ) (adeleMeasurePi K) (adeleMeasurePi K)` using `measurePreserving_comp_equiv (adeleMeasure K) ρ`. Establish `hfun : (fun x : ι → 𝔸[K] ↦ M.map (algebraMap K 𝔸[K]) *ᵥ x) = (fun x ↦ x ∘ ρ) ∘ (fun x ↦ P.map (algebraMap K 𝔸[K]) *ᵥ x) ∘ (fun x ↦ x ∘ τ.symm)`. Use function extensionality and compare the values at `x`. Establish `hP : P.map (algebraMap K 𝔸[K]) = (M.map (algebraMap K 𝔸[K])).submatrix ρ.symm τ.symm` using `(Matrix.submatrix_map _ _ _ _).symm`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[hP, Matrix.submatrix_mulVec_equiv]`. Use function extensionality and compare the values at `k`. Simplify using `only [Function.comp_apply, Equiv.symm_apply_apply]`. Use `congr 2`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Rewrite using `[hfun]`. Conclude with `h3.comp (h2.comp h1)`.
-/
theorem measurePreserving_mulVec (hNM : N * M = 1) (hMN : M * N = 1) :
    MeasurePreserving (fun x : ι → 𝔸[K] ↦ M.map (algebraMap K 𝔸[K]) *ᵥ x)
      (adeleMeasurePi K) (adeleMeasurePi K) := by
  have hcard : Fintype.card κ = Fintype.card ι := by
    let e : (ι → K) ≃ₗ[K] (κ → K) := LinearEquiv.ofLinearMap (Matrix.toLin' M) (Matrix.toLin' N)
      (by rw [← Matrix.toLin'_mul, hMN, Matrix.toLin'_one])
      (by rw [← Matrix.toLin'_mul, hNM, Matrix.toLin'_one])
    have h := e.finrank_eq
    rw [Module.finrank_fintype_fun_eq_card, Module.finrank_fintype_fun_eq_card] at h
    exact h.symm
  set τ : ι ≃ Fin (Fintype.card ι) := Fintype.equivFin ι
  set ρ : κ ≃ Fin (Fintype.card ι) := (Fintype.equivFin κ).trans (finCongr hcard)
  set P : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K := M.submatrix ρ.symm τ.symm
  set Q : Matrix (Fin (Fintype.card ι)) (Fin (Fintype.card ι)) K := N.submatrix τ.symm ρ.symm
  have hQP : Q * P = 1 := by
    rw [Matrix.submatrix_mul_equiv, hNM, Matrix.submatrix_one_equiv]
  have hPQ : P * Q = 1 := by
    rw [Matrix.submatrix_mul_equiv, hMN, Matrix.submatrix_one_equiv]
  have h1 : MeasurePreserving (fun x : ι → 𝔸[K] ↦ x ∘ τ.symm) (adeleMeasurePi K)
      (adeleMeasurePi K) := measurePreserving_comp_equiv (adeleMeasure K) τ.symm
  have h2 := measurePreserving_mulVec_fin P Q hQP hPQ
  have h3 : MeasurePreserving (fun x : Fin (Fintype.card ι) → 𝔸[K] ↦ x ∘ ρ) (adeleMeasurePi K)
      (adeleMeasurePi K) := measurePreserving_comp_equiv (adeleMeasure K) ρ
  have hfun : (fun x : ι → 𝔸[K] ↦ M.map (algebraMap K 𝔸[K]) *ᵥ x) =
      (fun x ↦ x ∘ ρ) ∘ (fun x ↦ P.map (algebraMap K 𝔸[K]) *ᵥ x) ∘ (fun x ↦ x ∘ τ.symm) := by
    funext x
    have hP : P.map (algebraMap K 𝔸[K]) = (M.map (algebraMap K 𝔸[K])).submatrix ρ.symm τ.symm :=
      (Matrix.submatrix_map _ _ _ _).symm
    simp only [Function.comp_apply]
    rw [hP, Matrix.submatrix_mulVec_equiv]
    funext k
    simp only [Function.comp_apply, Equiv.symm_apply_apply]
    congr 2
    funext i
    simp
  rw [hfun]
  exact h3.comp (h2.comp h1)

omit [Fintype κ] [DecidableEq κ] in

/- English proof (translation)
Use `set A := M.map (algebraMap K 𝔸[K])`. Use `set B := N.map (algebraMap K 𝔸[K])`. Establish `hpair : ∀ x : ι → 𝔸[K], ∑ i, (A *ᵥ x) i * (Bᵀ *ᵥ y) i = ∑ i, x i * y i`. Introduce `x`. Express the relevant statement in the definitionally equal form `(A *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ y`.

Rewrite using `[Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, map_mul_map_eq_one _ hNM, Matrix.one_mulVec]`. Establish `hmp : MeasurePreserving (fun x : ι → 𝔸[K] ↦ A *ᵥ x) (adeleMeasurePi K) (adeleMeasurePi K)` using `measurePreserving_mulVec M N hNM hMN`. Establish `hemb : MeasurableEmbedding (fun x : ι → 𝔸[K] ↦ A *ᵥ x)` using `(mulVecHomeomorph M N 𝔸[K] hNM hMN).measurableEmbedding`. Rewrite using `[adelicFourierPi, adelicFourierPi, ← hmp.integral_comp hemb (fun u ↦ F u * (adelicChar K (∑ i, u i * (Bᵀ *ᵥ y) i) : ℂ))]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)` and prove the remaining obligations.

Simplify using `only [hpair]`.
-/
theorem adelicFourierPi_comp_mulVec (M N : Matrix ι ι K) (hNM : N * M = 1) (hMN : M * N = 1)
    (F : (ι → 𝔸[K]) → ℂ) (y : ι → 𝔸[K]) :
    adelicFourierPi K (fun x ↦ F (M.map (algebraMap K 𝔸[K]) *ᵥ x)) y =
      adelicFourierPi K F ((N.map (algebraMap K 𝔸[K]))ᵀ *ᵥ y) := by
  set A := M.map (algebraMap K 𝔸[K])
  set B := N.map (algebraMap K 𝔸[K])
  have hpair : ∀ x : ι → 𝔸[K], ∑ i, (A *ᵥ x) i * (Bᵀ *ᵥ y) i = ∑ i, x i * y i := by
    intro x
    change (A *ᵥ x) ⬝ᵥ (Bᵀ *ᵥ y) = x ⬝ᵥ y
    rw [Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec,
      map_mul_map_eq_one _ hNM, Matrix.one_mulVec]
  have hmp : MeasurePreserving (fun x : ι → 𝔸[K] ↦ A *ᵥ x) (adeleMeasurePi K) (adeleMeasurePi K) :=
    measurePreserving_mulVec M N hNM hMN
  have hemb : MeasurableEmbedding (fun x : ι → 𝔸[K] ↦ A *ᵥ x) :=
    (mulVecHomeomorph M N 𝔸[K] hNM hMN).measurableEmbedding
  rw [adelicFourierPi, adelicFourierPi,
    ← hmp.integral_comp hemb (fun u ↦ F u * (adelicChar K (∑ i, u i * (Bᵀ *ᵥ y) i) : ℂ))]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x ↦ ?_)
  simp only [hpair]

end

end GroundTheory.Heights₂.Theta
