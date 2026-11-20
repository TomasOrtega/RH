import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasOpBOfMemClosure
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeylElementOperatorBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForLeviMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilOperatorForUnipotentMatrix
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DarbouxCoordinatesGoodModel

open scoped TensorProduct NNReal Matrix ENNReal
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped GlobalTheory.VacAny

noncomputable section

namespace GlobalTheory.SympChangeBij

open GlobalTheory.SympChange GlobalTheory.LeviOp GlobalTheory.SympUnip GlobalTheory.AdelicSvNQuad GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic

section Levi

variable {F : Type} [Field F] [NumberField F] {κ : Type}

open scoped Classical in

/- English proof (translation)
Set `gI : F →+* mixedEmbedding.mixedSpace F` to `(evIr (F := F)).comp (algebraMap F (AF F))`. Set `gF : F →+* FiniteAdeleRing (𝓞 F) F` to `(RingHom.snd _ _).comp (algebraMap F (AF F))`. Set `L` to `linEquiv (κ := κ) gI A hA`. Establish `key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ), LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) (pureA F f g) = pureA F (SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L f) (g ∘ homeo gF A hA)`. Introduce `f g`.

Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, pureA, Function.comp_apply, homeo_apply, SchwartzMap.compCLMOfContinuousLinearEquiv_apply]`. Use `congr 1`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Conclude with `hom_mulVec evIr (algebraMap F (AF F)) gI rfl A⁻¹ x i`. Use `congr 1`. Use function extensionality and compare the values at `i`. Conclude with `hom_mulVec (RingHom.snd _ _) (algebraMap F (AF F)) gF rfl A⁻¹ x i`. Establish `hle : schA F κ ≤ (schA F κ).comap (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x))`.

Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, g, hg, rfl⟩`. Use `show _ ∈ schA F κ`. Rewrite using `[key]`. Conclude with `Submodule.subset_span ⟨_, _, sb_comp (homeo gF A hA) hg, rfl⟩`.

Conclude with `fun Φ hΦ => hle hΦ`.
-/
theorem levi_mapsTo [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    ∀ Φ ∈ schA F κ, LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x) Φ ∈ schA F κ := by
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  have key : ∀ (f : SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ) (g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ),
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

open scoped Classical in

/- English proof (translation)
Establish `hA' : IsUnit A⁻¹.det` using `Matrix.isUnit_nonsing_inv_det A hA`. Establish `hm'` using `levi_mapsTo A⁻¹ hA'`. Rewrite `hm'` using `[Matrix.nonsing_inv_nonsing_inv A hA]`. Use `bijOn_of_inv _ _ (levi_mapsTo A hA) hm' (fun Φ _ => ?_) (fun Φ _ => ?_)` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Simplify using `only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_inv_mul _ A hA, Matrix.one_mulVec]`. Use function extensionality and compare the values at `x`. Simplify using `only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_mul_inv _ A hA, Matrix.one_mulVec]`.
-/
theorem bijOn_levi [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F) (hA : IsUnit A.det) :
    Set.BijOn (LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x))
      (schA F κ : Set ((κ → AF F) → ℂ)) (schA F κ : Set ((κ → AF F) → ℂ)) := by
  have hA' : IsUnit A⁻¹.det := Matrix.isUnit_nonsing_inv_det A hA
  have hm' := levi_mapsTo A⁻¹ hA'
  rw [Matrix.nonsing_inv_nonsing_inv A hA] at hm'
  refine bijOn_of_inv _ _ (levi_mapsTo A hA) hm' (fun Φ _ => ?_) (fun Φ _ => ?_)
  · funext x
    simp only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_inv_mul _ A hA, Matrix.one_mulVec]
  · funext x
    simp only [LinearMap.funLeft_apply, Matrix.mulVec_mulVec, map_mul_inv _ A hA, Matrix.one_mulVec]

end Levi

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ ψ _ _ _ κ _ _ A hA`. Set `gI : F →+* mixedEmbedding.mixedSpace F` to `(evIr (F := F)).comp (algebraMap F (AF F))`. Set `gF : F →+* FiniteAdeleRing (𝓞 F) F` to `(RingHom.snd _ _).comp (algebraMap F (AF F))`. Set `L` to `linEquiv (κ := κ) gI A hA`. Use `⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x), SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L, fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

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

Conclude with `bijOn_levi A hA`.
-/
theorem hasOpB_levi : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → (∀ᶠ v in cofinite, PsiUnr ψ v) →
    (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) → ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (A : Matrix κ κ F), IsUnit A.det →
    HasOpB ψ (GlobalTheory.SympChange.leviM A) := by
  intro F _ _ ψ _ _ _ κ _ _ A hA
  let gI : F →+* mixedEmbedding.mixedSpace F := (evIr (F := F)).comp (algebraMap F (AF F))
  let gF : F →+* FiniteAdeleRing (𝓞 F) F := (RingHom.snd _ _).comp (algebraMap F (AF F))
  let L := linEquiv (κ := κ) gI A hA
  refine ⟨LinearMap.funLeft ℂ ℂ (fun x : κ → AF F => A⁻¹.map (algebraMap F (AF F)) *ᵥ x),
    SchwartzMap.compCLMOfContinuousLinearEquiv ℂ L,
    fun v => LinearMap.funLeft ℂ ℂ (fun x : κ → Fv F v => A⁻¹.map (algebraMap F (Fv F v)) *ᵥ x),
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
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
  · exact bijOn_levi A hA

open scoped Classical in

/- English proof (translation)
Introduce `F _ _ ψ hψ hunr _ κ _ _ S hS`. Set `A : Matrix κ κ (AF F)` to `-S.map (algebraMap F (AF F))`. Set `Av : ∀ v : Pl F, Matrix κ κ (Fv F v)` to `fun v => -S.map (algebraMap F (Fv F v))`. Establish `hAv : ∀ v, A.map (evFin F v : AF F →+* Fv F v) = Av v` using `fun v => by`. Use `Matrix.ext fun i j => ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `evFin F v (-algebraMap F (AF F) (S i j)) = -algebraMap F (Fv F v) (S i j)`. Rewrite using `[map_neg, AlgHom.commutes]`. Set `q : AF F →+* mixedEmbedding.mixedSpace F` to `(InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1`. Set `hi` to `q (⅟2)`. Set `Ai` to `A.map q`.

Use `⟨mulR ψ (⅟2) A, SchwartzMap.smulLeftCLM ℂ (archMul hi Ai), fun v => mulR (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v), fun f => ?_, mulQ_mem ψ hψ _ A, fun w Φ _ => mulR_schr ψ S hS w Φ, fun v => ?_, fun v φ _ h0 => ?_, fun v w φ _ => mulR_schr _ S hS w φ, ?_, fun f φ _ hφ => ?_, ? …` and prove the remaining obligations. Use `⟨SchwartzMap.smulLeftCLM ℂ (archMul hi (-Ai)) f, SchwartzMap.ext fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_smul, archMul, archMul, eChar_apply, eChar_apply, ← Complex.exp_add, quad_neg, map_neg, neg_neg]`. Rewrite using `[show ∀ a : ℂ, a = 0 → Complex.exp a • f y = f y from fun a ha => by rw [ha, Complex.exp_zero, one_smul]]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hlc` using `psiAt_isLocallyConstant ψ hψ.1 v`. Use `le_antisymm ?_ fun φ hφ => ⟨mulR _ (⅟2) (-Av v) φ, mulR_mem hlc _ _ hφ, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨φ, hφ, rfl⟩`. Conclude with `mulR_mem hlc _ _ hφ`.

Use `mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-Av v) φ` as an intermediate fact. Rewrite `this` using `[neg_neg]`. Then use the resulting hypothesis. Rewrite using `[← mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v) φ]`. Conclude with `(congrArg _ h0).trans (map_zero _)`. Establish `h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F` using `eventually_evFin _`.

Establish `h3 : ∀ᶠ v : Pl F in cofinite, ∀ i j, evFin F v (A i j) ∈ v.adicCompletionIntegers F` using `eventually_all.2 fun i => eventually_all.2 fun j => eventually_evFin (A i j)`. Use `filter_upwards [hunr, h2, h3] with v hv h2 h3`. Use function extensionality and compare the values at `x`. Rewrite using `[mulR_apply]`. Distinguish the cases in `hx : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}`.

Rewrite `h2` using `[GlobalTheory.VacAny.evFin_invOf_two]`. Establish `h4` using `(hv 1).2 (one_mem _) _ (quad_mem (A := Av v) h2 (fun i j => by rw [← hAv v]; exact h3 i j) hx)`. Rewrite `h4` using `[one_mul]`. Rewrite using `[GlobalTheory.LatVac.psiAt_apply, h4, one_mul]`. Rewrite using `[indO, Set.indicator_of_notMem hx, mul_zero]`.

Use function extensionality and compare the values at `x`. Establish `hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite`. Establish `h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F` using `eventually_all.2 fun i => eventually_evFin (x i)`. Establish `h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1` using `by filter_upwards [hφ, h3] with v hv h3`. Rewrite using `[hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]`.

Both sides reduce to the same expression. Conclude with `h4`. Establish `hq : ∀ v : Pl F, evalV F v (p2 (quad (⅟2) A x)) = quad (⅟2) (Av v) fun i => evFin F v (x i)` using `fun v => by`. Use `map_quad (evFin F v : AF F →+* Fv F v) (⅟2) A x` as an intermediate fact. Rewrite `this` using `[hAv]`.

Conclude with `this.trans (congrArg (fun t => quad t (Av v) fun i => evFin F v (x i)) GlobalTheory.VacAny.evFin_invOf_two)`. Take `⟨hs, hp⟩` from `finChar_eq_finprod ψ hψ.1 (p2 (quad (⅟2) A x))`. Simplify using `only [hq] at hs hp`. Establish `h3 : ψ (mk (p1 (quad (⅟2) A x)) 0) = archMul hi Ai fun i => evI F (x i)`. Establish `e1 : evI F (mk (p1 (quad (⅟2) A x)) 0) = quad hi Ai fun i => evI F (x i)` using `map_quad q (⅟2) A x`.

Rewrite using `[hψ.2.2 _ (at_mk _), e1, archMul, eChar_apply]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mulR_apply]`.

Rewrite using `[finprod_mul_distrib hs hfin, ← hp, map_eq_mul ψ, h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `bijOn_of_inv (mulR ψ (⅟2) A) (mulR ψ (⅟2) (-A)) (mulQ_mem ψ hψ _ A) (mulQ_mem ψ hψ _ (-A)) (fun Φ _ => mulR_neg ψ (⅟2) A Φ) (fun Φ _ => by simpa only [neg_neg] using mulR_neg ψ (⅟2) (-A) Φ)`.
-/
theorem hasOpB_unipM : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    (∀ᶠ v in cofinite, PsiUnr ψ v) → (∀ v : Pl F, ∃ x, psiLoc ψ v x ≠ 1) →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (S : Matrix κ κ F), S.transpose = S →
    HasOpB ψ (GlobalTheory.SympChange.unipM S) := by
  intro F _ _ ψ hψ hunr _ κ _ _ S hS
  let A : Matrix κ κ (AF F) := -S.map (algebraMap F (AF F))
  let Av : ∀ v : Pl F, Matrix κ κ (Fv F v) := fun v => -S.map (algebraMap F (Fv F v))
  have hAv : ∀ v, A.map (evFin F v : AF F →+* Fv F v) = Av v := fun v => by
    refine Matrix.ext fun i j => ?_
    change evFin F v (-algebraMap F (AF F) (S i j)) = -algebraMap F (Fv F v) (S i j)
    rw [map_neg, AlgHom.commutes]
  let q : AF F →+* mixedEmbedding.mixedSpace F := (InfiniteAdeleRing.ringEquiv_mixedSpace F).toRingHom.comp p1
  let hi := q (⅟2)
  let Ai := A.map q
  refine ⟨mulR ψ (⅟2) A, SchwartzMap.smulLeftCLM ℂ (archMul hi Ai),
    fun v => mulR (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v), fun f => ?_, mulQ_mem ψ hψ _ A,
    fun w Φ _ => mulR_schr ψ S hS w Φ, fun v => ?_, fun v φ _ h0 => ?_,
    fun v w φ _ => mulR_schr _ S hS w φ, ?_, fun f φ _ hφ => ?_, ?_⟩
  · refine ⟨SchwartzMap.smulLeftCLM ℂ (archMul hi (-Ai)) f, SchwartzMap.ext fun y => ?_⟩
    rw [SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _),
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_smul, archMul, archMul, eChar_apply,
      eChar_apply, ← Complex.exp_add, quad_neg, map_neg, neg_neg]
    rw [show ∀ a : ℂ, a = 0 → Complex.exp a • f y = f y from fun a ha => by rw [ha, Complex.exp_zero, one_smul]]
    push_cast
    ring
  · have hlc := psiAt_isLocallyConstant ψ hψ.1 v
    refine le_antisymm ?_ fun φ hφ => ⟨mulR _ (⅟2) (-Av v) φ, mulR_mem hlc _ _ hφ, ?_⟩
    · rintro _ ⟨φ, hφ, rfl⟩
      exact mulR_mem hlc _ _ hφ
    · have := mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (-Av v) φ
      rwa [neg_neg] at this
  · rw [← mulR_neg (GlobalTheory.LatVac.psiAt ψ v) (⅟2) (Av v) φ]
    exact (congrArg _ h0).trans (map_zero _)
  · have h2 : ∀ᶠ v : Pl F in cofinite, evFin F v (⅟(2 : AF F)) ∈ v.adicCompletionIntegers F := eventually_evFin _
    have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i j, evFin F v (A i j) ∈ v.adicCompletionIntegers F :=
      eventually_all.2 fun i => eventually_all.2 fun j => eventually_evFin (A i j)
    filter_upwards [hunr, h2, h3] with v hv h2 h3
    funext x
    rw [mulR_apply]
    by_cases hx : x ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F}
    · rw [GlobalTheory.VacAny.evFin_invOf_two] at h2
      have h4 := (hv 1).2 (one_mem _) _ (quad_mem (A := Av v) h2 (fun i j => by rw [← hAv v]; exact h3 i j) hx)
      rw [one_mul] at h4
      rw [GlobalTheory.LatVac.psiAt_apply, h4, one_mul]
    · rw [indO, Set.indicator_of_notMem hx, mul_zero]
  · funext x
    have hfin : (Function.mulSupport fun v : Pl F => φ v fun i => evFin F v (x i)).Finite := by
      have h3 : ∀ᶠ v : Pl F in cofinite, ∀ i, evFin F v (x i) ∈ v.adicCompletionIntegers F :=
        eventually_all.2 fun i => eventually_evFin (x i)
      have h4 : ∀ᶠ v : Pl F in cofinite, (φ v fun i => evFin F v (x i)) = 1 := by
        filter_upwards [hφ, h3] with v hv h3
        rw [hv, indO, Set.indicator_of_mem (show _ ∈ {x : κ → Fv F v | ∀ i, x i ∈ v.adicCompletionIntegers F} from h3)]
        rfl
      exact h4
    have hq : ∀ v : Pl F, evalV F v (p2 (quad (⅟2) A x)) = quad (⅟2) (Av v) fun i => evFin F v (x i) := fun v => by
      have := map_quad (evFin F v : AF F →+* Fv F v) (⅟2) A x
      rw [hAv] at this
      exact this.trans (congrArg (fun t => quad t (Av v) fun i => evFin F v (x i)) GlobalTheory.VacAny.evFin_invOf_two)
    obtain ⟨hs, hp⟩ := finChar_eq_finprod ψ hψ.1 (p2 (quad (⅟2) A x))
    simp only [hq] at hs hp
    have h3 : ψ (mk (p1 (quad (⅟2) A x)) 0) = archMul hi Ai fun i => evI F (x i) := by
      have e1 : evI F (mk (p1 (quad (⅟2) A x)) 0) = quad hi Ai fun i => evI F (x i) := map_quad q (⅟2) A x
      rw [hψ.2.2 _ (at_mk _), e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure, mulR_apply]
    rw [finprod_mul_distrib hs hfin, ← hp, map_eq_mul ψ, h3,
      SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
    ring
  · exact bijOn_of_inv (mulR ψ (⅟2) A) (mulR ψ (⅟2) (-A)) (mulQ_mem ψ hψ _ A) (mulQ_mem ψ hψ _ (-A))
      (fun Φ _ => mulR_neg ψ (⅟2) A Φ) (fun Φ _ => by simpa only [neg_neg] using mulR_neg ψ (⅟2) (-A) Φ)

end GlobalTheory.SympChangeBij

open GlobalTheory.SympChange GlobalTheory.SympChangeBij in
open scoped Classical in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco`. Take `⟨G, hGs, hGe⟩` from `GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco`. Take `⟨hunr, hnt⟩` from `GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std`. Establish `hgen : ∀ G ∈ gens (F` using `F) (κ := Fin n × Fin d), HasOpB B.ψ G := by`. Introduce and unpack `G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)`.

Conclude with `hasOpB_levi F B.ψ hB.std hunr hnt _ A hA`. Conclude with `hasOpB_unipM F B.ψ hB.std hunr hnt _ S hS`. Rewrite using `[Set.mem_singleton_iff.mp hG]`. Conclude with `GlobalTheory.T.weyl_element_operator_bijective F B.ψ hB.std hunr hnt _`. Take `⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure, hbij⟩` from `hasOpB_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)`.

Use `⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_, hbij⟩` and prove the remaining obligations. Introduce `u Φ hΦ show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)`. Rewrite using `[hheis _ Φ hΦ, hGe]`. Introduce `v`. Take `⟨hvSB, hvne, θ, hθ, hγ⟩` from `hM.vac v`.

Establish `hevSB : ev v (M.vac v) ∈ SB _` using `by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB`. Take `⟨R, hR0, hR⟩` from `GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v`. Use `⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩` and prove the remaining obligations. Establish `hat : At (evFin F v) γ` using `(GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm`. Establish `h1` using `GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)`.

Establish `heq` using `acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)`. Establish `h3` using `GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))`. Rewrite `h3` using `[locCo_eq M.co co G hGe v γ, ← hloc v _ _ hvSB, heq, map_smul]`. Conclude with `h3`. Use `filter_upwards [hM.std, hind] with v h1 h2`.

Rewrite using `[h1]`. Conclude with `h2`. Introduce `f φ hφ hφv`. Use `hpure f φ hφ ?_` and prove the remaining obligations. Use `filter_upwards [hφv, hM.std] with v h1 h2`.

Rewrite using `[h1, h2]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.SympChangeBij.change_of_coordinates_bij : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (r s r' s' : ℕ), B.IsGood σ → X.IsHerm σ B r s →
    W.IsSkew σ B r' s' → M.IsGood B.ψ →
    ∀ co : Darboux (symp (R := AF F) (cA σ) (-1) (incM F X.J) (incM F W.J)) (Fin n × Fin d),
      (∀ x : Matrix (Fin n) (Fin d) E, ∃ y z : Fin n × Fin d → F,
        co.e (incM F x) = (fun i => algebraMap F (AF F) (y i), fun i => algebraMap F (AF F) (z i))) →
      ∃ (e : Fn F n d →ₗ[ℂ] Fn F n d) (ei : SInf F (Fin n × Fin d) →L[ℂ] SInf F (Fin n × Fin d))
        (ev : ∀ v : Pl F, ((Fin n × Fin d → Fv F v) → ℂ) →ₗ[ℂ] (Fin n × Fin d → Fv F v) → ℂ),
        Function.Surjective ei ∧ (∀ Φ ∈ schA F (Fin n × Fin d), e Φ ∈ schA F (Fin n × Fin d)) ∧
        (∀ u, ∀ Φ ∈ schA F (Fin n × Fin d), e (M.co.rho B.ψ u Φ) = co.rho B.ψ u (e Φ)) ∧
        (∀ v, (SB _).map (ev v) = SB _) ∧
        (∀ v, (⟨co, fun _ => 0, 0, ∅⟩ : Model σ X W).IsVac B.ψ v (ev v (M.vac v))) ∧
        (∀ᶠ v in cofinite, ev v (M.vac v) = Set.indicator {x | ∀ i, x i ∈ v.adicCompletionIntegers F} 1) ∧
        (∀ f φ, (∀ v, φ v ∈ SB _) → (∀ᶠ v in cofinite, φ v = M.vac v) → e (GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure f φ) = GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels.pure (ei f) fun v => ev v (φ v)) ∧
        Set.BijOn e (schA F (Fin n × Fin d) : Set _) (schA F (Fin n × Fin d) : Set _) := by
  intro F E _ _ _ _ _ σ B n d X W M r s r' s' hB _ _ hM co hco
  obtain ⟨G, hGs, hGe⟩ := GlobalTheory.T.rational_darboux_coordinates_compare F E σ n d X.J W.J M.co co hM.rat hco
  obtain ⟨hunr, hnt⟩ := GlobalTheory.T.standard_character_almost_unramified F B.ψ hB.std
  have hgen : ∀ G ∈ gens (F := F) (κ := Fin n × Fin d), HasOpB B.ψ G := by
    rintro G ((⟨A, hA, rfl⟩ | ⟨S, hS, rfl⟩) | hG)
    · exact hasOpB_levi F B.ψ hB.std hunr hnt _ A hA
    · exact hasOpB_unipM F B.ψ hB.std hunr hnt _ S hS
    · rw [Set.mem_singleton_iff.mp hG]; exact GlobalTheory.T.weyl_element_operator_bijective F B.ψ hB.std hunr hnt _
  obtain ⟨e, ei, ev, hsurj, hmaps, hheis, hSB, hinj, hloc, hind, hpure, hbij⟩ :=
    hasOpB_of_mem_closure hgen G (GlobalTheory.T.symplectic_group_generated_by_elementary F _ G hGs)
  refine ⟨e, ei, ev, hsurj, hmaps, ?_, hSB, ?_, ?_, ?_, hbij⟩
  · intro u Φ hΦ
    show e (schr B.ψ (M.co.e u) Φ) = schr B.ψ (co.e u) (e Φ)
    rw [hheis _ Φ hΦ, hGe]
  · intro v
    obtain ⟨hvSB, hvne, θ, hθ, hγ⟩ := hM.vac v
    have hevSB : ev v (M.vac v) ∈ SB _ := by rw [← hSB v]; exact Submodule.mem_map_of_mem hvSB
    obtain ⟨R, hR0, hR⟩ := GlobalTheory.T.exists_complementary_adelicSchwartz_restFunction (F := F) (Fin n × Fin d) v
    refine ⟨hevSB, fun h0 => hvne (hinj v _ hvSB h0), θ, hθ, fun γ hγm => ?_⟩
    have hat : At (evFin F v) γ := (GlobalTheory.LatVac.latAtV_at_stable X W v).1 γ hγm
    have h1 := GlobalTheory.VacBridge.rho_acts_locCo M.co B.ψ v γ hat (M.vac v)
    have heq := acts_unique' v hR0 (hR _ hvSB) h1 (hγ γ hγm)
    have h3 := GlobalTheory.VacBridge.rho_acts_locCo co B.ψ v γ hat (ev v (M.vac v))
    rw [locCo_eq M.co co G hGe v γ, ← hloc v _ _ hvSB, heq, map_smul] at h3
    exact h3
  · filter_upwards [hM.std, hind] with v h1 h2
    rw [h1]; exact h2
  · intro f φ hφ hφv
    refine hpure f φ hφ ?_
    filter_upwards [hφv, hM.std] with v h1 h2
    rw [h1, h2]; rfl
