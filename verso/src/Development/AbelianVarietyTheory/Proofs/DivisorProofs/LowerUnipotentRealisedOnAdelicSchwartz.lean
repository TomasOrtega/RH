import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RealisedOne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationPreservesSchwartz

noncomputable section

open NumberField IsDedekindDomain Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.WeilM GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.AdelicSvN
open scoped Matrix

namespace GlobalTheory.AdelicSvNQuad

open GlobalTheory.HeisSchA GlobalTheory.Published.Metaplectic
open scoped Classical

def quad {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) : R := h * (x ⬝ᵥ (A *ᵥ x))

/- English proof (translation)
Simplify using `[quad, dotProduct, Matrix.mulVec, map_sum]`.
-/
theorem map_quad {R S κ : Type} [CommRing R] [CommRing S] [Fintype κ] (q : R →+* S) (h : R) (A : Matrix κ κ R)
    (x : κ → R) : q (quad h A x) = quad (q h) (A.map q) (fun i => q (x i)) := by
  simp [quad, dotProduct, Matrix.mulVec, map_sum]

/- English proof (translation)
Simplify using `[quad, Matrix.neg_mulVec]`.
-/
theorem quad_neg {R κ : Type} [CommRing R] [Fintype κ] (h : R) (A : Matrix κ κ R) (x : κ → R) :
    quad h (-A) x = -quad h A x := by
  simp [quad, Matrix.neg_mulVec]

/- English proof (translation)
The claim follows from `continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))`.
-/
theorem continuous_quad {R κ : Type} [CommRing R] [TopologicalSpace R] [IsTopologicalRing R] [Fintype κ] (h : R)
    (A : Matrix κ κ R) : Continuous (quad h A) :=
  continuous_const.mul (continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id))

/- English proof (translation)
Establish `hs : u ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ u)`. Rewrite using `[Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]`. Establish `h2 : ⅟(2 : R) * 2 = 1` using `invOf_mul_self _`. Simplify using `only [quad, Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, hs]`. Take the linear combination `(-(x ⬝ᵥ (A *ᵥ u))) * h2`.
-/
theorem quad_add {R κ : Type} [CommRing R] [Invertible (2 : R)] [Fintype κ] (A : Matrix κ κ R) (hA : Aᵀ = A)
    (x u v : κ → R) : quad (⅟2) A x + (x ⬝ᵥ v + ⅟(2 : R) * (u ⬝ᵥ v)) =
      (x ⬝ᵥ (-(A *ᵥ u) + v) + ⅟(2 : R) * (u ⬝ᵥ (-(A *ᵥ u) + v))) + quad (⅟2) A (x + u) := by
  have hs : u ⬝ᵥ (A *ᵥ x) = x ⬝ᵥ (A *ᵥ u) := by
    rw [Matrix.dotProduct_mulVec, ← Matrix.mulVec_transpose, hA, dotProduct_comm]
  have h2 : ⅟(2 : R) * 2 = 1 := invOf_mul_self _
  simp only [quad, Matrix.mulVec_add, dotProduct_add, add_dotProduct, dotProduct_neg, hs]
  linear_combination (-(x ⬝ᵥ (A *ᵥ u))) * h2

variable {F : Type} [Field F] [NumberField F] {κ : Type} [Fintype κ]

def archMul (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F))
    (y : κ → mixedEmbedding.mixedSpace F) : ℂ :=
  eChar (-Algebra.trace ℝ (mixedEmbedding.mixedSpace F) (quad h A y))

/- English proof (translation)
Establish `hp : ∀ i : κ, Function.HasTemperateGrowth fun y : κ → mixedEmbedding.mixedSpace F => y i` using `fun i => (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth`. Establish `hq : Function.HasTemperateGrowth (quad h A)`. Establish `e : quad h A = fun y => h * ∑ i, y i * ∑ j, A i j * y j` using `rfl`. Rewrite using `[e]`. Use `(Function.HasTemperateGrowth.const h).mul (Function.HasTemperateGrowth.sum fun i _ => (hp i).mul ?_)` and prove the remaining obligations.

Conclude with `Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const _).mul (hp j)`. Set `L : mixedEmbedding.mixedSpace F →L[ℝ] ℝ` to `-LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))`. Conclude with `hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.comp hq)`.
-/
theorem archMul_temperate (h : mixedEmbedding.mixedSpace F) (A : Matrix κ κ (mixedEmbedding.mixedSpace F)) :
    Function.HasTemperateGrowth (archMul h A) := by
  have hp : ∀ i : κ, Function.HasTemperateGrowth fun y : κ → mixedEmbedding.mixedSpace F => y i := fun i =>
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : κ => mixedEmbedding.mixedSpace F) i).hasTemperateGrowth
  have hq : Function.HasTemperateGrowth (quad h A) := by
    have e : quad h A = fun y => h * ∑ i, y i * ∑ j, A i j * y j := rfl
    rw [e]
    refine (Function.HasTemperateGrowth.const h).mul (Function.HasTemperateGrowth.sum fun i _ => (hp i).mul ?_)
    exact Function.HasTemperateGrowth.sum fun j _ => (Function.HasTemperateGrowth.const _).mul (hp j)
  let L : mixedEmbedding.mixedSpace F →L[ℝ] ℝ :=
    -LinearMap.toContinuousLinearMap (Algebra.trace ℝ (mixedEmbedding.mixedSpace F))
  exact hasTemperateGrowth_eChar.comp (L.hasTemperateGrowth.comp hq)

def mulQ (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ((κ → AF F) → ℂ) →ₗ[ℂ] ((κ → AF F) → ℂ) where
  toFun φ x := ψ (quad h A x) * φ x
  map_add' φ φ' := funext fun x => mul_add _ _ _
  map_smul' a φ := funext fun x => by
    simp only [Pi.smul_apply, smul_eq_mul, RingHom.id_apply]; ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem mulQ_apply (ψ : AddChar (AF F) ℂ) (h : AF F) (A : Matrix κ κ (AF F)) (φ : (κ → AF F) → ℂ) (x : κ → AF F) :
    mulQ ψ h A φ x = ψ (quad h A x) * φ x := rfl

/- English proof (translation)
Set `e` to `InfiniteAdeleRing.ringEquiv_mixedSpace F`. Set `q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F` to `e.toRingHom.comp p1`. Use `⟨fun z => finChar ψ (quad (p2 h) (A.map p2) z) * g z, ⟨((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_quad _ _)).mul hg.1, hg.2.mul_left⟩, SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)), fun f => funext fun x => ?_⟩` and prove the remaining obligations. Set `y : κ → mixedEmbedding.mixedSpace F` to `fun i => q (x i)`. Set `z : κ → FiniteAdeleRing (𝓞 F) F` to `fun i => p2 (x i)`.

Establish `h3 : ψ (quad h A x) = archMul (q h) (A.map q) y * finChar ψ (quad (p2 h) (A.map p2) z)`. Rewrite using `[map_eq_mul ψ, hψ.2.2 _ (at_mk _)]`. Use `congr 1`. Establish `e1 : evI F (mk (p1 (quad h A x)) 0) = quad (q h) (A.map q) y` using `map_quad q h A x`. Rewrite using `[e1, archMul, eChar_apply]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `congrArg _ (map_quad p2 h A x)`. Express the relevant statement in the definitionally equal form `ψ (quad h A x) * (f y * g z) = SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)) f y * (finChar ψ (quad (p2 h) (A.map p2) z) * g z)`.

Rewrite using `[h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem mulQ_pureA (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F))
    {g : (κ → FiniteAdeleRing (𝓞 F) F) → ℂ} (hg : g ∈ SB (κ → FiniteAdeleRing (𝓞 F) F)) :
    ∃ g' ∈ SB (κ → FiniteAdeleRing (𝓞 F) F), ∃ M : SInf F κ →L[ℂ] SInf F κ,
      ∀ f : SInf F κ, mulQ ψ h A (pureA F f g) = pureA F (M f) g' := by
  let e := InfiniteAdeleRing.ringEquiv_mixedSpace F
  let q : AdeleRing (𝓞 F) F →+* mixedEmbedding.mixedSpace F := e.toRingHom.comp p1
  refine ⟨fun z => finChar ψ (quad (p2 h) (A.map p2) z) * g z,
    ⟨((finChar_isLocallyConstant ψ hψ.1).comp_continuous (continuous_quad _ _)).mul hg.1, hg.2.mul_left⟩,
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)), fun f => funext fun x => ?_⟩
  let y : κ → mixedEmbedding.mixedSpace F := fun i => q (x i)
  let z : κ → FiniteAdeleRing (𝓞 F) F := fun i => p2 (x i)
  have h3 : ψ (quad h A x) = archMul (q h) (A.map q) y * finChar ψ (quad (p2 h) (A.map p2) z) := by
    rw [map_eq_mul ψ, hψ.2.2 _ (at_mk _)]
    congr 1
    · have e1 : evI F (mk (p1 (quad h A x)) 0) = quad (q h) (A.map q) y := map_quad q h A x
      rw [e1, archMul, eChar_apply]
      congr 1
      push_cast
      ring
    · exact congrArg _ (map_quad p2 h A x)
  change ψ (quad h A x) * (f y * g z) =
    SchwartzMap.smulLeftCLM ℂ (archMul (q h) (A.map q)) f y * (finChar ψ (quad (p2 h) (A.map p2) z) * g z)
  rw [h3, SchwartzMap.smulLeftCLM_apply_apply (archMul_temperate _ _), smul_eq_mul]
  ring

/- English proof (translation)
Establish `hle : schA F κ ≤ (schA F κ).comap (mulQ ψ h A)`. Use `Submodule.span_le.mpr ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨f, g, hg, rfl⟩`. Take `⟨g', hg', M, hM⟩` from `mulQ_pureA ψ hψ h A hg`. Conclude with `Submodule.subset_span ⟨M f, g', hg', hM f⟩`.

Conclude with `fun φ hφ => hle hφ`.
-/
theorem mulQ_mem (ψ : AddChar (AF F) ℂ) (hψ : IsStd ψ) (h : AF F) (A : Matrix κ κ (AF F)) :
    ∀ φ ∈ schA F κ, mulQ ψ h A φ ∈ schA F κ := by
  have hle : schA F κ ≤ (schA F κ).comap (mulQ ψ h A) := by
    refine Submodule.span_le.mpr ?_
    rintro _ ⟨f, g, hg, rfl⟩
    obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ h A hg
    exact Submodule.subset_span ⟨M f, g', hg', hM f⟩
  exact fun φ hφ => hle hφ

/- English proof (translation)
Establish `h1 : (1 : Matrix ι ι K).map (algebraMap K R) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0` using `Matrix.map_zero _ (map_zero _)`. Establish `hn : (-C).map (algebraMap K R) = -C.map (algebraMap K R)` using `Matrix.map_neg _ (map_neg _) _`. Simplify using `only [AdelicSvN.act, Matrix.fromBlocks_map, h1, h0, hn, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr, Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]`.
-/
theorem act_unip {K R ι : Type} [Field K] [CommRing R] [Algebra K R] [Fintype ι] [DecidableEq ι] (C : Matrix ι ι K)
    (w : (ι → R) × (ι → R)) :
    AdelicSvN.act (Matrix.fromBlocks 1 0 (-C) 1) w = (w.1, -(C.map (algebraMap K R) *ᵥ w.1) + w.2) := by
  have h1 : (1 : Matrix ι ι K).map (algebraMap K R) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
  have h0 : (0 : Matrix ι ι K).map (algebraMap K R) = 0 := Matrix.map_zero _ (map_zero _)
  have hn : (-C).map (algebraMap K R) = -C.map (algebraMap K R) := Matrix.map_neg _ (map_neg _) _
  simp only [AdelicSvN.act, Matrix.fromBlocks_map, h1, h0, hn, Matrix.fromBlocks_mulVec, Sum.elim_comp_inl, Sum.elim_comp_inr,
    Matrix.one_mulVec, Matrix.zero_mulVec, add_zero, Matrix.neg_mulVec]

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ _ C hC`. Set `A : Matrix κ κ (AF F)` to `C.map (algebraMap F (AF F))`. Establish `hA : Aᵀ = A` using `by rw [← Matrix.transpose_map, hC]`. Use `⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩, fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `x`.

Rewrite using `[mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel, AddChar.map_zero_eq_one, one_mul]`. Take `⟨g', hg', M, hM⟩` from `mulQ_pureA ψ hψ (⅟2) A hg`. Take `⟨T, hT⟩` from `hl g' hg'`. Conclude with `⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩`. Rewrite using `[act_unip, mulQ_apply]`.

Simplify using `only [schr]`. Rewrite using `[mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]`.
-/
theorem realised_unip : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ → ∀ (κ : Type) [Fintype κ]
    [DecidableEq κ] (C : Matrix κ κ F), Cᵀ = C → Realised ψ (Matrix.fromBlocks 1 0 (-C) 1) := by
  intro F _ _ ψ hψ κ _ _ C hC
  let A : Matrix κ κ (AF F) := C.map (algebraMap F (AF F))
  have hA : Aᵀ = A := by rw [← Matrix.transpose_map, hC]
  refine ⟨mulQ ψ (⅟2) A, mulQ_mem ψ hψ _ A, fun φ hφ => ⟨mulQ ψ (⅟2) (-A) φ, mulQ_mem ψ hψ _ _ φ hφ, ?_⟩,
    fun l hl => ⟨l ∘ₗ mulQ ψ (⅟2) A, fun g hg => ?_, fun _ _ => rfl⟩, fun w φ _ => funext fun x => ?_⟩
  · funext x
    rw [mulQ_apply, mulQ_apply, ← mul_assoc, ← AddChar.map_add_eq_mul, quad_neg, add_neg_cancel,
      AddChar.map_zero_eq_one, one_mul]
  · obtain ⟨g', hg', M, hM⟩ := mulQ_pureA ψ hψ (⅟2) A hg
    obtain ⟨T, hT⟩ := hl g' hg'
    exact ⟨T.comp M, fun f => (congrArg l (hM f)).trans (hT (M f))⟩
  · rw [act_unip, mulQ_apply]
    simp only [schr]
    rw [mulQ_apply, ← mul_assoc, ← mul_assoc, ← AddChar.map_add_eq_mul, ← AddChar.map_add_eq_mul, quad_add A hA]

end GlobalTheory.AdelicSvNQuad

end
