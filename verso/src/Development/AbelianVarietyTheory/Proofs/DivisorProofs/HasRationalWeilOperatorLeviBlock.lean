import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ActFromBlocks
open scoped Matrix GlobalTheory.VacAny
open NumberField IsDedekindDomain MeasureTheory Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Rewrite using `[← Matrix.transpose_transpose (hᵀ * g), Matrix.transpose_mul, Matrix.transpose_transpose, hg, Matrix.transpose_one]`.
-/
theorem levi_transpose_mul {R : Type} [CommRing R] {g h : Matrix κ κ R} (hg : gᵀ * h = 1) : hᵀ * g = 1 := by
  rw [← Matrix.transpose_transpose (hᵀ * g), Matrix.transpose_mul, Matrix.transpose_transpose, hg, Matrix.transpose_one]

/- English proof (translation)
Rewrite using `[← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero f) (map_one f)]`.
-/
theorem levi_map {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) {g h : Matrix κ κ R} (hg : gᵀ * h = 1) :
    (g.map f)ᵀ * h.map f = 1 := by
  rw [← Matrix.transpose_map, ← Matrix.map_mul, hg, Matrix.map_one _ (map_zero f) (map_one f)]

/- English proof (translation)
Establish `h1` using `levi_transpose_mul hg`. Establish `e1 : x ⬝ᵥ h *ᵥ w.2 = (hᵀ *ᵥ x) ⬝ᵥ w.2` using `by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]`. Establish `e2 : (g *ᵥ w.1) ⬝ᵥ h *ᵥ w.2 = w.1 ⬝ᵥ w.2`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Establish `e3 : hᵀ *ᵥ (x + g *ᵥ w.1) = hᵀ *ᵥ x + w.1`.

Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Simplify using `only [schr]`. Rewrite using `[e1, e2, e3]`.
-/
theorem schr_mulVec_transpose {R : Type} [CommRing R] [Invertible (2 : R)] (ψ : AddChar R ℂ) {g h : Matrix κ κ R}
    (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) (x : κ → R) :
    schr ψ w Φ (hᵀ *ᵥ x) = schr ψ (g *ᵥ w.1, h *ᵥ w.2) (fun y => Φ (hᵀ *ᵥ y)) x := by
  have h1 := levi_transpose_mul hg
  have e1 : x ⬝ᵥ h *ᵥ w.2 = (hᵀ *ᵥ x) ⬝ᵥ w.2 := by rw [Matrix.dotProduct_mulVec, Matrix.mulVec_transpose]
  have e2 : (g *ᵥ w.1) ⬝ᵥ h *ᵥ w.2 = w.1 ⬝ᵥ w.2 := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  have e3 : hᵀ *ᵥ (x + g *ᵥ w.1) = hᵀ *ᵥ x + w.1 := by
    rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  simp only [schr]
  rw [e1, e2, e3]

/- English proof (translation)
Use function extensionality and compare the values at `x`. Rewrite using `[Matrix.fromBlocks_map, act_fromBlocks, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, Matrix.zero_mulVec, add_zero, zero_add, LinearMap.funLeft_apply, Matrix.transpose_map]`. Conclude with `schr_mulVec_transpose ψ (levi_map (algebraMap F R) hg) w Φ x`.
-/
theorem funLeft_schr_levi {F R : Type} [Field F] [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (w : (κ → R) × (κ → R)) (Φ : (κ → R) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) (schr ψ w Φ) =
      schr ψ (act ((Matrix.fromBlocks g 0 0 h).map (algebraMap F R)) w)
        (LinearMap.funLeft ℂ ℂ (fun x : κ → R => hᵀ.map (algebraMap F R) *ᵥ x) Φ) := by
  funext x
  rw [Matrix.fromBlocks_map, act_fromBlocks, Matrix.map_zero _ (map_zero _), Matrix.zero_mulVec, Matrix.zero_mulVec,
    add_zero, zero_add, LinearMap.funLeft_apply, Matrix.transpose_map]
  exact schr_mulVec_transpose ψ (levi_map (algebraMap F R) hg) w Φ x

/- English proof (translation)
Establish `mem : ∀ (S : X ≃ₜ X), ∀ φ ∈ (SB X : Set (X → ℂ)), φ ∘ S ∈ (SB X : Set (X → ℂ))` using `fun S φ hφ => ⟨hφ.1.comp_continuous S.continuous, hφ.2.comp_homeomorph S⟩`. Use `⟨fun φ hφ => mem T φ hφ, fun φ _ ψ _ e => LinearMap.funLeft_injective_of_surjective _ _ _ T.surjective e, fun φ hφ => ⟨φ ∘ T.symm, mem T.symm φ hφ, ?_⟩⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `[LinearMap.funLeft_apply]`.
-/
theorem bijOn_funLeft_homeomorph {X : Type} [TopologicalSpace X] (T : X ≃ₜ X) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ T) (SB X : Set (X → ℂ)) (SB X : Set (X → ℂ)) := by
  have mem : ∀ (S : X ≃ₜ X), ∀ φ ∈ (SB X : Set (X → ℂ)), φ ∘ S ∈ (SB X : Set (X → ℂ)) :=
    fun S φ hφ => ⟨hφ.1.comp_continuous S.continuous, hφ.2.comp_homeomorph S⟩
  refine ⟨fun φ hφ => mem T φ hφ, fun φ _ ψ _ e => LinearMap.funLeft_injective_of_surjective _ _ _ T.surjective e,
    fun φ hφ => ⟨φ ∘ T.symm, mem T.symm φ hφ, ?_⟩⟩
  funext x
  simp [LinearMap.funLeft_apply]

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ]

def mulVecHomeo {R : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] (M N : Matrix κ κ R)
    (h1 : M * N = 1) (h2 : N * M = 1) : (κ → R) ≃ₜ (κ → R) where
  toFun x := M *ᵥ x
  invFun x := N *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  continuous_toFun := continuous_const.matrix_mulVec continuous_id
  continuous_invFun := continuous_const.matrix_mulVec continuous_id

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]`. Both sides reduce to the same expression.
-/
theorem evI_algebraMap (c : F) : evI F (algebraMap F (AF F) c) = mixedEmbedding F c := by
  rw [InfiniteAdeleRing.mixedEmbedding_eq_algebraMap_comp]; rfl

def evIHom : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem evIHom_apply (a : AF F) : evIHom a = evI F a := rfl

def mulVecR (M : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    (κ → mixedEmbedding.mixedSpace F) →ₗ[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (Matrix.mulVecLin M).restrictScalars ℝ

end GlobalTheory.RatWeilOp

noncomputable section

namespace GlobalTheory.RatWeilOp

variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

def mulVecCLE (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) :
    (κ → mixedEmbedding.mixedSpace F) ≃L[ℝ] (κ → mixedEmbedding.mixedSpace F) :=
  (LinearEquiv.ofLinear (mulVecR M) (mulVecR N)
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, LinearMap.id_coe, id_eq])
    (LinearMap.ext fun x => by
      simp only [mulVecR, LinearMap.coe_comp, Function.comp_apply, LinearMap.coe_restrictScalars, Matrix.mulVecLin_apply,
        Matrix.mulVec_mulVec, h2, Matrix.one_mulVec, LinearMap.id_coe, id_eq])).toContinuousLinearEquiv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulVecCLE_apply (M N : Matrix κ κ (mixedEmbedding.mixedSpace F)) (h1 : M * N = 1) (h2 : N * M = 1) (x) :
    mulVecCLE M N h1 h2 x = M *ᵥ x := rfl

/- English proof (translation)
Establish `h1` using `levi_transpose_mul hg`. Establish `h2 : g * hᵀ = 1` using `(Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1`. Conclude with `⟨by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)], by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]⟩`.
-/
theorem levi_map_mul {R : Type} [CommRing R] (f : F →+* R) {g h : Matrix κ κ F} (hg : gᵀ * h = 1) :
    hᵀ.map f * g.map f = 1 ∧ g.map f * hᵀ.map f = 1 := by
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  exact ⟨by rw [← Matrix.map_mul, h1, Matrix.map_one _ (map_zero f) (map_one f)],
    by rw [← Matrix.map_mul, h2, Matrix.map_one _ (map_zero f) (map_one f)]⟩

/- English proof (translation)
Introduce `i` and use `sum_mem fun j _ => mul_mem (hM i j) (hx j)`.
-/
theorem mulVec_mem_integers (v : Pl F) (M : Matrix κ κ (Fv F v))
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) :
    ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F :=
  fun i => sum_mem fun j _ => mul_mem (hM i j) (hx j)

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Establish `key : (∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F`. Use `⟨fun hx => ?_, mulVec_mem_integers v M hM x⟩` and prove the remaining obligations. Establish `e : x = N *ᵥ (M *ᵥ x)` using `by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]`. Rewrite using `[e]`. Conclude with `mulVec_mem_integers v N hN _ hx`.

Unfold `ind`. Distinguish the cases in `hx : ∀ i, x i ∈ v.adicCompletionIntegers F`. Establish `hx'` using `(key.2 hx)`. Rewrite using `[Set.indicator_of_mem (show M *ᵥ x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'), Set.indicator_of_mem (show x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]`. Both sides reduce to the same expression.

Establish `hx' : ¬ ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F` using `fun h' => hx (key.1 h')`. Rewrite using `[Set.indicator_of_notMem (show M *ᵥ x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'), Set.indicator_of_notMem (show x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]`.
-/
theorem ind_mulVec (v : Pl F) (M N : Matrix κ κ (Fv F v)) (hNM : N * M = 1)
    (hM : ∀ i j, M i j ∈ v.adicCompletionIntegers F) (hN : ∀ i j, N i j ∈ v.adicCompletionIntegers F) (x : κ → Fv F v) :
    ind κ v (M *ᵥ x) = ind κ v x := by
  have key : (∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F := by
    refine ⟨fun hx => ?_, mulVec_mem_integers v M hM x⟩
    have e : x = N *ᵥ (M *ᵥ x) := by rw [Matrix.mulVec_mulVec, hNM, Matrix.one_mulVec]
    rw [e]
    exact mulVec_mem_integers v N hN _ hx
  unfold ind
  by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
  · have hx' := (key.2 hx)
    rw [Set.indicator_of_mem (show M *ᵥ x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_mem (show x ∈ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
    rfl
  · have hx' : ¬ ∀ i, (M *ᵥ x) i ∈ v.adicCompletionIntegers F := fun h' => hx (key.1 h')
    rw [Set.indicator_of_notMem (show M *ᵥ x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx'),
      Set.indicator_of_notMem (show x ∉ {y : κ → Fv F v | ∀ i, y i ∈ v.adicCompletionIntegers F} from hx)]
end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp
variable {κ : Type} [Fintype κ] [DecidableEq κ] {F : Type} [Field F] [NumberField F]

open scoped Classical in

/- English proof (translation)
Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Function.comp_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mulVecCLE_apply]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← evIHom_apply, RingHom.map_mulVec, Matrix.map_map]`. Establish `e : (evIHom ∘ algebraMap F (AF F)) = mixedEmbedding F` using `funext fun c => evI_algebraMap c`. Rewrite using `[e]`. Both sides reduce to the same expression. Use `finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)` and prove the remaining obligations.

Rewrite using `[← AlgHom.coe_toRingHom, RingHom.map_mulVec, Matrix.map_map]`. Establish `e : ((evFin F v : AF F →+* Fv F v) ∘ algebraMap F (AF F)) = algebraMap F (Fv F v)`. Use function extensionality and compare the values at `fun c => (evFin F v).commutes c`. Rewrite using `[e]`. Both sides reduce to the same expression.
-/
theorem funLeft_pure_levi {g h : Matrix κ κ F} (hI1 : hᵀ.map (mixedEmbedding F) * g.map (mixedEmbedding F) = 1)
    (hI2 : g.map (mixedEmbedding F) * hᵀ.map (mixedEmbedding F) = 1) (f : SInf F κ) (φ : ∀ v : Pl F, (κ → Fv F v) → ℂ) :
    LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) =
      GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2) f)
        (fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x) (φ v)) := by
  funext x
  simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, Function.comp_apply,
    SchwartzMap.compCLMOfContinuousLinearEquiv_apply, mulVecCLE_apply]
  congr 1
  · congr 1
    funext i
    rw [← evIHom_apply, RingHom.map_mulVec, Matrix.map_map]
    have e : (evIHom ∘ algebraMap F (AF F)) = mixedEmbedding F := funext fun c => evI_algebraMap c
    rw [e]
    rfl
  · refine finprod_congr fun v => congrArg (φ v) (funext fun i => ?_)
    rw [← AlgHom.coe_toRingHom, RingHom.map_mulVec, Matrix.map_map]
    have e : ((evFin F v : AF F →+* Fv F v) ∘ algebraMap F (AF F)) = algebraMap F (Fv F v) :=
      funext fun c => (evFin F v).commutes c
    rw [e]
    rfl

/- English proof (translation)
Simplify using `only [thetaSum, LinearMap.funLeft_apply]`. Establish `e : ∀ ξ : κ → F, (hᵀ.map (algebraMap F (AF F)) *ᵥ fun i => algebraMap F (AF F) (ξ i)) = fun i => algebraMap F (AF F) ((hᵀ *ᵥ ξ) i)` using `fun ξ => funext fun i => (RingHom.map_mulVec _ _ _ _).symm`. Simplify using `only [e]`. Establish `h1` using `levi_transpose_mul hg`. Establish `h2 : g * hᵀ = 1` using `(Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1`.

Set `eq : (κ → F) ≃ (κ → F)` to `{ toFun := fun ξ => hᵀ *ᵥ ξ, invFun := fun ξ => g *ᵥ ξ, left_inv := fun ξ => by`. Simplify using `only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]`. Use `right_inv := fun ξ => by`. Simplify using `only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] }`. Conclude with `Equiv.tsum_eq eq (fun ξ : κ → F => Φ fun i => algebraMap F (AF F) (ξ i))`.
-/
theorem thetaSum_funLeft_levi {g h : Matrix κ κ F} (hg : gᵀ * h = 1) (Φ : (κ → AF F) → ℂ) :
    thetaSum F (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x) Φ) = thetaSum F Φ := by
  simp only [thetaSum, LinearMap.funLeft_apply]
  have e : ∀ ξ : κ → F, (hᵀ.map (algebraMap F (AF F)) *ᵥ fun i => algebraMap F (AF F) (ξ i)) =
      fun i => algebraMap F (AF F) ((hᵀ *ᵥ ξ) i) := fun ξ => funext fun i => (RingHom.map_mulVec _ _ _ _).symm
  simp only [e]
  have h1 := levi_transpose_mul hg
  have h2 : g * hᵀ = 1 := (Matrix.mul_eq_one_comm_of_card_eq κ κ F rfl).mp h1
  let eq : (κ → F) ≃ (κ → F) :=
    { toFun := fun ξ => hᵀ *ᵥ ξ, invFun := fun ξ => g *ᵥ ξ,
      left_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h2, Matrix.one_mulVec]
      right_inv := fun ξ => by
        simp only [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec] }
  exact Equiv.tsum_eq eq (fun ξ : κ → F => Φ fun i => algebraMap F (AF F) (ξ i))

end GlobalTheory.RatWeilOp

noncomputable section
namespace GlobalTheory.RatWeilOp

open scoped Classical in

/- English proof (translation)
Take `⟨hI1, hI2⟩` from `levi_map_mul (mixedEmbedding F) hg`. Establish `hv : ∀ v : Pl F, (hᵀ.map (algebraMap F (Fv F v))) * g.map (algebraMap F (Fv F v)) = 1 ∧ g.map (algebraMap F (Fv F v)) * hᵀ.map (algebraMap F (Fv F v)) = 1` using `fun v => levi_map_mul _ hg`. Use `⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x), 1, SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2), fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x), one_ne_zero, ?_, fun v => bijOn_fun …` and prove the remaining obligations. Introduce `f`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2).symm f, ?_⟩` and prove the remaining obligations.

Use `DFunLike.ext _ _ fun x => ?_` and prove the remaining obligations. Simplify using `only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply, ContinuousLinearEquiv.symm_apply_apply]`. Establish `hint : ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (h i j) ∈ v.adicCompletionIntegers F ∧ algebraMap F (Fv F v) (g i j) ∈ v.adicCompletionIntegers F` using `eventually_all.2 fun i => eventually_all.2 fun j => (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _) filter_upwards [hint] with v hv'`. Use function extensionality and compare the values at `x`. Conclude with `ind_mulVec v _ _ (hv v).2 (fun i j => (hv' j i).1) (fun i j => (hv' i j).2) x`.
-/
theorem hasOp_levi (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ) (κ : Type) [Fintype κ] [DecidableEq κ]
    (g h : Matrix κ κ F) (hg : gᵀ * h = 1) : HasOp ψ (Matrix.fromBlocks g 0 0 h) := by
  obtain ⟨hI1, hI2⟩ := levi_map_mul (mixedEmbedding F) hg
  have hv : ∀ v : Pl F, (hᵀ.map (algebraMap F (Fv F v))) * g.map (algebraMap F (Fv F v)) = 1 ∧
      g.map (algebraMap F (Fv F v)) * hᵀ.map (algebraMap F (Fv F v)) = 1 := fun v => levi_map_mul _ hg
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => hᵀ.map (algebraMap F (AF F)) *ᵥ x), 1,
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2),
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => hᵀ.map (algebraMap F (Fv F v)) *ᵥ x),
    one_ne_zero, ?_, fun v => bijOn_funLeft_homeomorph (mulVecHomeo _ _ (hv v).1 (hv v).2),
    fun v w φ _ => funLeft_schr_levi _ hg w φ, ?_, fun f φ _ =>
      ⟨funLeft_pure_levi hI1 hI2 f φ, fun w => funLeft_schr_levi ψ hg w _, by rw [thetaSum_funLeft_levi hg, one_mul]⟩⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ (mulVecCLE _ _ hI1 hI2).symm f, ?_⟩
    refine DFunLike.ext _ _ fun x => ?_
    simp only [SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply,
      ContinuousLinearEquiv.symm_apply_apply]
  · have hint : ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (h i j) ∈ v.adicCompletionIntegers F ∧
        algebraMap F (Fv F v) (g i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j =>
        (eventually_algebraMap_mem_integers _).and (eventually_algebraMap_mem_integers _)
    filter_upwards [hint] with v hv'
    funext x
    exact ind_mulVec v _ _ (hv v).2 (fun i j => (hv' j i).1) (fun i j => (hv' i j).2) x

end GlobalTheory.RatWeilOp
