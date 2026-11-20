import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSymp
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.LeviOp

variable {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]`.
-/
theorem map_inv_mul {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A⁻¹.map g * A.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.nonsing_inv_mul A h, Matrix.map_one g (map_zero g) (map_one g)]

/- English proof (translation)
Rewrite using `[← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]`.
-/
theorem map_mul_inv {S : Type} [CommRing S] (g : F →+* S) (A : Matrix κ κ F) (h : IsUnit A.det) :
    A.map g * A⁻¹.map g = 1 := by
  rw [← Matrix.map_mul, Matrix.mul_nonsing_inv A h, Matrix.map_one g (map_zero g) (map_one g)]

/- English proof (translation)
Substitute `hg` using the available equality. Simplify using `[Matrix.mulVec, dotProduct, map_sum, map_mul]`.
-/
theorem hom_mulVec {S T : Type} [CommRing S] [CommRing T] (f : S →+* T) (g : F →+* S) (g' : F →+* T)
    (hg : f.comp g = g') (M : Matrix κ κ F) (x : κ → S) (i : κ) :
    f ((M.map g *ᵥ x) i) = (M.map g' *ᵥ (fun j => f (x j))) i := by
  subst hg
  simp [Matrix.mulVec, dotProduct, map_sum, map_mul]

/- English proof (translation)
Unfold `GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM`. Rewrite using `[Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]`. Apply the tactic sequence `ext k <;> simp [Matrix.transpose_map]`.
-/
theorem spAct_levi {R : Type} [CommRing R] [Algebra F R] (A : Matrix κ κ F) (w : (κ → R) × (κ → R)) :
    GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w =
      (A.map (algebraMap F R) *ᵥ w.1, (A⁻¹.map (algebraMap F R))ᵀ *ᵥ w.2) := by
  unfold GlobalTheory.SympChange.spAct GlobalTheory.SympChange.leviM
  rw [Matrix.fromBlocks_map, Matrix.fromBlocks_mulVec]
  ext k <;> simp [Matrix.transpose_map]

/- English proof (translation)
Rewrite using `[spAct_levi]`. Use function extensionality and compare the values at `x`. Simplify using `only [GlobalTheory.WeilM.schr]`. Establish `h1` using `map_inv_mul (algebraMap F R) A hA`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec, Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`.
-/
theorem schr_levi {R : Type} [CommRing R] [Algebra F R] [Invertible (2 : R)] (ψ : AddChar R ℂ)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (w : (κ → R) × (κ → R)) (φ : (κ → R) → ℂ) :
    (fun x => schr ψ w φ (A⁻¹.map (algebraMap F R) *ᵥ x)) =
      schr ψ (GlobalTheory.SympChange.spAct (GlobalTheory.SympChange.leviM A) w) (fun x => φ (A⁻¹.map (algebraMap F R) *ᵥ x)) := by
  rw [spAct_levi]
  funext x
  simp only [GlobalTheory.WeilM.schr]
  have h1 := map_inv_mul (algebraMap F R) A hA
  rw [Matrix.mulVec_add, Matrix.mulVec_mulVec, h1, Matrix.one_mulVec,
    Matrix.dotProduct_mulVec x, Matrix.vecMul_transpose, Matrix.dotProduct_mulVec, Matrix.vecMul_transpose,
    Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]

def homeo {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S) (A : Matrix κ κ F)
    (hA : IsUnit A.det) : (κ → S) ≃ₜ (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem homeo_apply {S : Type} [CommRing S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) (x : κ → S) : homeo g A hA x = A⁻¹.map g *ᵥ x := rfl

def linEquiv {S : Type} [CommRing S] [Algebra ℝ S] [TopologicalSpace S] [IsTopologicalRing S] (g : F →+* S)
    (A : Matrix κ κ F) (hA : IsUnit A.det) : (κ → S) ≃L[ℝ] (κ → S) where
  toFun x := A⁻¹.map g *ᵥ x
  invFun x := A.map g *ᵥ x
  map_add' x y := Matrix.mulVec_add _ x y
  map_smul' c x := Matrix.mulVec_smul _ c x
  left_inv x := by simp only [Matrix.mulVec_mulVec, map_mul_inv g A hA, Matrix.one_mulVec]
  right_inv x := by simp only [Matrix.mulVec_mulVec, map_inv_mul g A hA, Matrix.one_mulVec]
  continuous_toFun := Continuous.matrix_mulVec continuous_const continuous_id
  continuous_invFun := Continuous.matrix_mulVec continuous_const continuous_id

/- English proof (translation)
Assemble the required witnesses or components as `⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩`.
-/
theorem sb_comp {X : Type} [TopologicalSpace X] (h : X ≃ₜ X) {φ : X → ℂ} (hφ : φ ∈ SB X) : φ ∘ h ∈ SB X :=
  ⟨hφ.1.comp_continuous h.continuous, hφ.2.comp_homeomorph h⟩

variable [NumberField F]

def evIr : AF F →+* mixedEmbedding.mixedSpace F :=
  (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp (RingHom.fst _ _)

/- English proof (translation)
Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply]`. Conclude with `sum_mem fun j _ => mul_mem (hM i j) (hx j)`.
-/
theorem mulVec_mem {v : Pl F} (M : Matrix κ κ F)
    (hM : ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F) (x : κ → Fv F v)
    (hx : ∀ i, x i ∈ v.adicCompletionIntegers F) (i : κ) :
    (M.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F := by
  simp only [Matrix.mulVec, dotProduct, Matrix.map_apply]
  exact sum_mem fun j _ => mul_mem (hM i j) (hx j)

/- English proof (translation)
Simplify using `only [Filter.eventually_all]`. Conclude with `fun i j => (algebraMap F (Af F) (M i j)).2`.
-/
theorem eventually_int (M : Matrix κ κ F) :
    ∀ᶠ v : Pl F in cofinite, ∀ i j, algebraMap F (Fv F v) (M i j) ∈ v.adicCompletionIntegers F := by
  simp only [Filter.eventually_all]
  exact fun i j => (algebraMap F (Af F) (M i j)).2

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ ψ _ _ _ κ _ _ A hA`. Set `gI : F →+* mixedEmbedding.mixedSpace F` to `(evIr (F := F)).comp (algebraMap F (AF F))`. Set `gF : F →+* FiniteAdeleRing (𝓞 F) F` to `(RingHom.snd _ _).comp (algebraMap F (AF F))`. Set `L` to `linEquiv (κ := κ) gI A hA`. Use `⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x), SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `f`. Use `⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩` and prove the remaining obligations. Use `SchwartzMap.ext fun x => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA)`.

Introduce `f g`. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]`. Use `congr 1`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i`.

Establish `hle : schA F κ ≤ (schA F κ).comap (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x))`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, g, hg, rfl⟩`. Use `show _ ∈ schA F κ`. Rewrite using `[key]`.

Conclude with `Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩`. Conclude with `fun Φ hΦ => hle hΦ`. Introduce `w Φ _`. Conclude with `schr_levi ψ A hA w Φ`. Introduce `v`.

Use `le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_` and prove the remaining obligations. Introduce `φ hφ`. Use `⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, Function.comp_apply]`.

Conclude with `congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)`. Introduce `v φ _ h`. Use function extensionality and compare the values at `x`. Use `congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)` as an intermediate fact. Simplify using `only [LinearMap.funLeft_apply, Pi.zero_apply] at this`.

Establish `hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x` using `(homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x`. Rewrite `this` using `[hx]`. Conclude with `this`. Introduce `v w φ _`. Conclude with `schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ`.

Use `filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2`. Use function extensionality and compare the values at `x`. Establish `hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔ ∀ i, x i ∈ v.adicCompletionIntegers F`. Prove the components needed by the constructor for the conclusion. Introduce `h i`.

Establish `e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x)` using `((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm`. Rewrite using `[e]`. Conclude with `mulVec_mem A hA1 _ h i`. Introduce `h i`. Conclude with `mulVec_mem A⁻¹ hA2 x h i`.

Use `show Set.indicator _ _ _ = Set.indicator _ _ _`. Distinguish the cases in `hx : ∀ i, x i ∈ v.adicCompletionIntegers F`. Rewrite using `[Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx), Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx), Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]`.

Introduce `f φ _ _`. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply, Function.comp_apply]`. Use `congr 1`. Use `congr 1`.

Use function extensionality and compare the values at `i`. Conclude with `hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i`. Use `finprod_congr fun v => congrArg (φ v) ?_` and prove the remaining obligations. Use function extensionality and compare the values at `i`. Conclude with `hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v)) (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i`.
-/
theorem hasOp_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    GlobalTheory.SympChange.HasOp ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro f
    refine ⟨SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L.symm f, ?_⟩
    refine SchwartzMap.ext fun x => ?_
    simp
  · have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
        LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) =
          pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA) := by
      intro f g
      funext x
      simp only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply,
        SchwartzMap.compCLMOfContinuousLinearEquiv_apply]
      congr 1
      · congr 1
        funext i
        exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
      · congr 1
        funext i
        exact hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i
    have hle : schA F κ ≤ (schA F κ).comap
        (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x)) := by
      refine Submodule.span_le.2 ?_
      rintro _ ⟨f, g, hg, rfl⟩
      show _ ∈ schA F κ
      rw [key]
      exact Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩
    exact fun Φ hΦ => hle hΦ
  · intro w Φ _
    exact schr_levi ψ A hA w Φ
  · intro v
    refine le_antisymm (Submodule.map_le_iff_le_comap.2 fun φ hφ => sb_comp (homeo _ A hA) hφ) ?_
    intro φ hφ
    refine ⟨φ ∘ (homeo (algebraMap F (Fv F v)) A hA).symm, sb_comp _ hφ, ?_⟩
    funext x
    simp only [LinearMap.funLeft_apply, Function.comp_apply]
    exact congrArg φ ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x)
  · intro v φ _ h
    funext x
    have := congrFun h ((homeo (algebraMap F (Fv F v)) A hA).symm x)
    simp only [LinearMap.funLeft_apply, Pi.zero_apply] at this
    have hx : A⁻¹.map (algebraMap F (Fv F v)) *ᵥ (homeo (algebraMap F (Fv F v)) A hA).symm x = x :=
      (homeo (algebraMap F (Fv F v)) A hA).apply_symm_apply x
    rw [hx] at this
    exact this
  · intro v w φ _
    exact schr_levi (GlobalTheory.LatVac.psiAt ψ v) A hA w φ
  · filter_upwards [eventually_int A, eventually_int A⁻¹] with v hA1 hA2
    funext x
    have hiff : (∀ i, (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) i ∈ v.adicCompletionIntegers F) ↔
        ∀ i, x i ∈ v.adicCompletionIntegers F := by
      constructor
      · intro h i
        have e : x = A.map (algebraMap F (Fv F v)) *ᵥ (A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x) :=
          ((homeo (algebraMap F (Fv F v)) A hA).symm_apply_apply x).symm
        rw [e]
        exact mulVec_mem A hA1 _ h i
      · intro h i
        exact mulVec_mem A⁻¹ hA2 x h i
    show Set.indicator _ _ _ = Set.indicator _ _ _
    by_cases hx : ∀ i, x i ∈ v.adicCompletionIntegers F
    · rw [Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hiff.2 hx),
        Set.indicator_of_mem (show x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
      rfl
    · rw [Set.indicator_of_notMem (show _ ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from mt hiff.1 hx),
        Set.indicator_of_notMem (show x ∉ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from hx)]
  · intro f φ _ _
    funext x
    simp only [LinearMap.funLeft_apply, GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, SchwartzMap.compCLMOfContinuousLinearEquiv_apply,
      Function.comp_apply]
    congr 1
    · congr 1
      funext i
      exact hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i
    · refine finprod_congr fun v => congrArg (φ v) ?_
      funext i
      exact hom_mulVec (evFin F v).toRingHom (algebraMap F (AF F)) (algebraMap F (Fv F v))
        (RingHom.ext fun c => (evFin F v).commutes c) A⁻¹ x i

end GlobalTheory.LeviOp
