import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Definitions.Divisors.IsCompactIsOpenUnitsAt
import Development.AbelianVarietyTheory.Definitions.Divisors.RankEqCardIffExistsFrameMatrixFirstColumnBlock
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsContinuousPadic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRankZetaKernelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSchwartzMembershipCriterion
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearBarModelUnitaryAction
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilRepresentationLocalityUnitaryGroupV
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitDetOfCartan
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalCharacterSmoothUnitary
import Development.AbelianVarietyTheory.Definitions.Divisors.PairsOfSquareTriple
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulMatIntOrbO
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LactMemFullRk
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK
open scoped Classical
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL Formalism.DoubleCosetMeasures.instMeasMat

noncomputable section

namespace GlobalTheory.TranslationGLHaar

open GlobalTheory.SplitFlip

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

def trGL (n : ℕ) : GL (Fin n) k ≃ₜ GL (Fin n) k where
  toFun g := (invT g)⁻¹
  invFun g := (invT g)⁻¹
  left_inv g := Units.ext (by simp only [invT_inv_val, Matrix.transpose_transpose])
  right_inv g := Units.ext (by simp only [invT_inv_val, Matrix.transpose_transpose])
  continuous_toFun := Units.continuous_iff.2 ⟨by
      show Continuous fun g : GL (Fin n) k => ((invT g)⁻¹ : GL (Fin n) k).val
      simp only [invT_inv_val]; exact Units.continuous_val.matrix_transpose, by
      show Continuous fun g : GL (Fin n) k => (((invT g)⁻¹)⁻¹ : GL (Fin n) k).val
      simp only [inv_inv, invT_val]; exact Units.continuous_coe_inv.matrix_transpose⟩
  continuous_invFun := Units.continuous_iff.2 ⟨by
      show Continuous fun g : GL (Fin n) k => ((invT g)⁻¹ : GL (Fin n) k).val
      simp only [invT_inv_val]; exact Units.continuous_val.matrix_transpose, by
      show Continuous fun g : GL (Fin n) k => (((invT g)⁻¹)⁻¹ : GL (Fin n) k).val
      simp only [inv_inv, invT_val]; exact Units.continuous_coe_inv.matrix_transpose⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trGL_val (n : ℕ) (g : GL (Fin n) k) : (trGL n g).val = g.valᵀ := rfl

/- English proof (translation)
The claim follows from `Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, trGL_val, Matrix.det_transpose])`.
-/
theorem gdet_trGL (n : ℕ) (g : GL (Fin n) k) : gdet (trGL n g) = gdet g :=
  Units.ext (by simp [Matrix.GeneralLinearGroup.val_det_apply, trGL_val, Matrix.det_transpose])

/- English proof (translation)
Establish `h1` using `Matrix.rank_mul_le_left (GlobalTheory.FullRankCoinv.Y0 k n d) (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ`. Rewrite `h1` using `[GlobalTheory.FullRankCoinv.LeftScale.Y0_mul_transpose h, Matrix.rank_one, Fintype.card_fin]`. Conclude with `le_antisymm (Matrix.rank_le_height _) h1`.
-/
theorem rank_zeroth_component_eq {n d : ℕ} (h : n ≤ d) : (GlobalTheory.FullRankCoinv.Y0 k n d).rank = n := by
  have h1 := Matrix.rank_mul_le_left (GlobalTheory.FullRankCoinv.Y0 k n d) (GlobalTheory.FullRankCoinv.Y0 k n d)ᵀ
  rw [GlobalTheory.FullRankCoinv.LeftScale.Y0_mul_transpose h, Matrix.rank_one, Fintype.card_fin] at h1
  exact le_antisymm (Matrix.rank_le_height _) h1

/- English proof (translation)
Establish `e : GlobalTheory.FullRankCoinv.lact ν g Ψ = omB ν ν g 1 Ψ`. Use function extensionality and compare the values at `Y`. Simplify using `[GlobalTheory.FullRankCoinv.lact, omB]`. Use `⟨e ▸ omB_mem_SB ν ν g 1 h.1, fun Y hY => ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (g.1ᵀ).det`.

Rewrite using `[Matrix.det_transpose]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _).1 g.isUnit`. Simplify using `only [GlobalTheory.FullRankCoinv.lact]`. Rewrite using `[h.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]), mul_zero]`.
-/
theorem lact_mem_fullRk {n d : ℕ} (ν : kˣ →* ℂˣ) (g : GL (Fin n) k) {Ψ : Matrix (Fin n) (Fin d) k → ℂ}
    (h : Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d) : GlobalTheory.FullRankCoinv.lact ν g Ψ ∈ GlobalTheory.FullRankCoinv.fullRk k n d := by
  have e : GlobalTheory.FullRankCoinv.lact ν g Ψ = omB ν ν g 1 Ψ := by
    funext Y; simp [GlobalTheory.FullRankCoinv.lact, omB]
  refine ⟨e ▸ omB_mem_SB ν ν g 1 h.1, fun Y hY => ?_⟩
  have hu : IsUnit (g.1ᵀ).det := by
    rw [Matrix.det_transpose]; exact (Matrix.isUnit_iff_isUnit_det _).1 g.isUnit
  simp only [GlobalTheory.FullRankCoinv.lact]
  rw [h.2 _ (by rwa [Matrix.rank_mul_eq_right_of_isUnit_det _ _ hu]), mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `Y`. Simplify using `only [omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]`.
-/
theorem omB_one_eq_lact {n d : ℕ} (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ) :
    omB ν α g 1 Ψ = GlobalTheory.FullRankCoinv.lact ν g Ψ := by
  funext Y
  simp only [omB, GlobalTheory.FullRankCoinv.lact, map_one, Units.val_one, apow_one, Matrix.mul_one, mul_one, Fintype.card_fin]

/- English proof (translation)
Simplify using `only [omB, trGL_val, Matrix.transpose_transpose, gdet_trGL, map_one, Units.val_one, apow_one, Matrix.mul_one, mul_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omB_trGL {n d : ℕ} (ν α : kˣ →* ℂˣ) (g : GL (Fin n) k) (Ψ : Matrix (Fin n) (Fin d) k → ℂ)
    (Y : Matrix (Fin n) (Fin d) k) :
    omB ν α (trGL n g) 1 Ψ Y = Ψ (g.val * Y) * ν (gdet g) * apow (gdet g) ((Fintype.card (Fin d) : ℂ) / 2) := by
  simp only [omB, trGL_val, Matrix.transpose_transpose, gdet_trGL, map_one, Units.val_one, apow_one, Matrix.mul_one,
    mul_one]
  ring

variable [MeasurableSpace k] [BorelSpace k]

/- English proof (translation)
Establish `hm : Measurable (trGL n : GL (Fin n) k → GL (Fin n) k)` using `(trGL n).continuous.measurable`. Use `haveI : (μ.map (trGL n)).IsMulLeftInvariant := ⟨fun a => by`. Rewrite using `[Measure.map_map (continuous_mul_left a).measurable hm]`. Establish `e : (fun x => a * x) ∘ (trGL n) = (trGL n) ∘ (fun x => x * trGL n a)`. Use function extensionality and compare the values at `g`.

Apply `Units.ext` to reduce the goal to its premises. Simplify using `only [Function.comp_apply, Units.val_mul, trGL_val, Matrix.transpose_mul, Matrix.transpose_transpose]`. Rewrite using `[e, ← Measure.map_map hm (continuous_mul_right _).measurable, MeasureTheory.map_mul_right_eq_self]⟩`. Use `haveI : IsFiniteMeasureOnCompacts (μ.map (trGL n)) := ⟨fun C hC => by`. Rewrite using `[(trGL n).measurableEmbedding.map_apply]`.

Conclude with `((trGL n).isCompact_preimage.2 hC).measure_lt_top⟩`. Use `haveI : (μ.map (trGL n)).IsOpenPosMeasure := (trGL n).continuous.isOpenPosMeasure_map (trGL n).surjective`. Conclude with `{ toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance, toIsOpenPosMeasure := inferInstance }`.
-/
theorem isHaar_map_trGL (n : ℕ) (μ : Measure (GL (Fin n) k)) [μ.IsHaarMeasure] :
    (μ.map (trGL n)).IsHaarMeasure := by
  have hm : Measurable (trGL n : GL (Fin n) k → GL (Fin n) k) := (trGL n).continuous.measurable
  haveI : (μ.map (trGL n)).IsMulLeftInvariant := ⟨fun a => by
    rw [Measure.map_map (continuous_mul_left a).measurable hm]
    have e : (fun x => a * x) ∘ (trGL n) = (trGL n) ∘ (fun x => x * trGL n a) := by
      funext g; apply Units.ext
      simp only [Function.comp_apply, Units.val_mul, trGL_val, Matrix.transpose_mul, Matrix.transpose_transpose]
    rw [e, ← Measure.map_map hm (continuous_mul_right _).measurable, MeasureTheory.map_mul_right_eq_self]⟩
  haveI : IsFiniteMeasureOnCompacts (μ.map (trGL n)) := ⟨fun C hC => by
    rw [(trGL n).measurableEmbedding.map_apply]
    exact ((trGL n).isCompact_preimage.2 hC).measure_lt_top⟩
  haveI : (μ.map (trGL n)).IsOpenPosMeasure := (trGL n).continuous.isOpenPosMeasure_map (trGL n).surjective
  exact { toIsFiniteMeasureOnCompacts := inferInstance, toIsMulLeftInvariant := inferInstance,
          toIsOpenPosMeasure := inferInstance }

/- English proof (translation)
The claim follows from `(trGL n).measurableEmbedding.integral_map f`.
-/
theorem integral_map_trGL (n : ℕ) (μ : Measure (GL (Fin n) k)) (f : GL (Fin n) k → ℂ) :
    ∫ g, f g ∂(μ.map (trGL n)) = ∫ g, f (trGL n g) ∂μ :=
  (trGL n).measurableEmbedding.integral_map f

end Local

open GlobalTheory.SplitFlip in

/- English proof (translation)
Introduce `hKP F E _ _ _ _ _ σ B a a' G X om om' hT ι hι x hx hint`. Establish `hv : X.Good B.v₁` using `hT.chars.good`. Take `⟨hs, -⟩` from `GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary hKP.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁`. Establish `hP` using `GlobalTheory.ThK.Inhab.pairV' hT`. Establish `hle : a' ≤ a + a'` using `by omega`.

Use `set ν : (Fv F B.v₁)ˣ →* ℂˣ := chrW (X.α / X.β) B.τ₁ with hνdef`. Establish `hs' : GlobalTheory.SmGL.IsSmoothChar ν` using `hs`. Establish `hiff` using `GlobalTheory.SoLocAnyIntertwiner.soLoc_iff hKP F E σ B a a' G X om om' hT ι hι`. Establish `hspanSB : Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) ≤ SB (Fin a' × Fin (a + a') → Fv F B.v₁)` using `Submodule.span_le.2 fun φ h => h.1`. Establish `hxSB` using `hspanSB hx`.

Establish `hvan : ∀ y ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁), Y.rank ≠ a' → ι y Y = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem φ hφ => exact (hiff φ hφ.1).1 hφ`. Consider the case `zero => intro Y _`.

Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz => intro Y hY`. Simplify using `[hy Y hY, hz Y hY]`. Consider the case `smul c y _ hy => intro Y hY`. Simplify using `[hy Y hY]`.

Establish `hfull : ι x ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a')` using `⟨hι.bij.mapsTo hxSB, hvan x hx⟩`. Use `letI : MeasurableSpace (Fv F B.v₁) := borel _`. Use `haveI : BorelSpace (Fv F B.v₁) := ⟨rfl⟩`. Establish `hF : ∀ h : GL (Fin (a + a')) (Fv F B.v₁), smallF (haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a'))) ν (ι x) (GlobalTheory.FullRankCoinv.Y0 (Fv F B.v₁) a' (a + a') * h.val) = 0`. Introduce `h`.

Use `haveI := GlobalTheory.TranslationGLHaar.isHaar_map_trGL a' (haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a')))`. Establish `hY : (GlobalTheory.FullRankCoinv.Y0 (Fv F B.v₁) a' (a + a') * h.val).rank = a'`. Rewrite using `[Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h)]`. Conclude with `GlobalTheory.TranslationGLHaar.rank_zeroth_component_eq hle`. Establish `h1` using `hint ((haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a'))).map (GlobalTheory.TranslationGLHaar.trGL a')) _ hY`.

Rewrite `h1` using `[GlobalTheory.TranslationGLHaar.integral_map_trGL]`. Use `(integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)).trans h1` and prove the remaining obligations. Conclude with `(GlobalTheory.TranslationGLHaar.omB_trGL _ _ g _ _).symm`. Establish `haug : ι x ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν` using `GlobalTheory.T.full_rank_zeta_kernel (Fv F B.v₁) a' (a + a') ν hle hs' (ι x) hfull hF`. Establish `hcm : IsCMExt F E σ` using `hT.base.cm`.

Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Establish `hdet : IsUnit (G.V'.J.map B.τ₁).det` using `GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J B.τ₁ (B.emb w).1 1 one_ne_zero (G.V'.θ w) (by rw [one_smul]; exact hT.geo.hV'.cartan w)`. Establish `herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j` using `fun i j => by`. Rewrite using `[map_one, one_mul]`. Conclude with `hT.geo.hV'.herm i j`.

Set `K` to `GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.V'.J 1 herm hdet`. Establish `hKU : ∀ g, K g ∈ UAt σ G.V' (evFin F B.v₁)` using `fun g => GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.V' 1 herm hdet g`. Establish `hKm : ∀ g, GlobalTheory.KSplit.locMat B.τ₁ 1 (K g) = g` using `fun g => Units.ext (by`. Rewrite using `[GlobalTheory.KSplit.locMat_val, GlobalTheory.SplitUnitLift.liftU_piW]`. Use the proof step `simp)`.

Establish `h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F B.v₁)` using `GlobalTheory.ThK.mem_UAtSub.1 (Subgroup.one_mem _)`. Establish `hgen : ∀ z ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν, ∃ y ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁, Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ}, ι y = z`. Introduce `z hz`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem z hz`.

Take `⟨g, Ψ, hΨ, rfl⟩` from `hz`. Take `⟨ψ, hψ, rfl⟩` from `hι.bij.surjOn hΨ.1`. Establish `hψS : ψ ∈ G.M'.SoLoc B.ψ B.τ₁` using `(hiff ψ hψ).2 hΨ.2`. Take `⟨S, hS⟩` from `GlobalTheory.WeilLocality.locality B G X om om' hT B.v₁ (K g) (hKU g)`. Take `⟨hS1, hA⟩` from `hS ψ hψ`.

Establish `he : ι (S ψ) = GlobalTheory.FullRankCoinv.lact ν g (ι ψ)`. Rewrite using `[GlobalTheory.OppLagr.act_linBar hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP B.v₁ B.τ₁ 1 1 ι hι (K g) (hKU g) 1 h1W ψ hψ (S ψ) hS1 hA, hKm g, map_one]`. Conclude with `GlobalTheory.TranslationGLHaar.omB_one_eq_lact _ _ g _`. Establish `hSS : S ψ ∈ G.M'.SoLoc B.ψ B.τ₁` using `(hiff (S ψ) hS1).2 (fun Y hY => by rw [he]; exact (GlobalTheory.TranslationGLHaar.lact_mem_fullRk ν g hΨ).2 Y hY)`. Conclude with `⟨S ψ - ψ, Submodule.subset_span ⟨K g, hKU g, ψ, hψS, S ψ, hSS, hA, rfl⟩, by rw [map_sub, he]⟩`.

Consider the case `zero => exact ⟨0, Submodule.zero_mem _, map_zero ι⟩`. Consider the case `add z z' _ _ hz hz'`. Take `⟨y, hy, e⟩` from `hz`. Take `⟨y', hy', e'⟩` from `hz'`. Conclude with `⟨y + y', Submodule.add_mem _ hy hy', by rw [map_add, e, e']⟩`.

Consider the case `smul c z _ hz`. Take `⟨y, hy, e⟩` from `hz`. Conclude with `⟨c • y, Submodule.smul_mem _ c hy, by rw [map_smul, e]⟩`. Take `⟨y, hy, hye⟩` from `hgen _ haug`. Establish `hySB : y ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁)`.

Use `(Submodule.span_le.2 ?_) hy` and prove the remaining obligations. Introduce and unpack `_ ⟨g, -, ψ, hψ, ψ', hψ', -, rfl⟩`. Conclude with `Submodule.sub_mem _ hψ'.1 hψ.1`. Establish `hyx : y = x` using `hι.bij.injOn hySB hxSB hye`. Rewrite using `[← hyx]`.

Conclude with `hy`.
-/
theorem ker_fibre_mem_span : GlobalTheory.ThK.KP → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (a a' : ℕ) (G : Geo σ a a') (X : Chars F E) (om : Rep σ G.V G.W) (om' : Rep σ G.V' G.W), IsTriple B G X om om' →
    ∀ ι, G.M'.IsLinBar B.ψ B.τ₁ 1 1 ι →
    ∀ x ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁),
      (∀ [MeasurableSpace (GL (Fin a') (Fv F B.v₁))] [BorelSpace (GL (Fin a') (Fv F B.v₁))] (μ : Measure (GL (Fin a') (Fv F B.v₁))) [μ.IsHaarMeasure], ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁), Y.rank = a' →
        ∫ g, GlobalTheory.SplitFlip.omB (chrW (X.α / X.β) B.τ₁) (chrW X.α B.τ₁) g 1 (ι x) Y ∂μ = 0) →
      x ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁), ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁,
        Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ} := by
  intro hKP F E _ _ _ _ _ σ B a a' G X om om' hT ι hι x hx hint
  have hv : X.Good B.v₁ := hT.chars.good
  obtain ⟨hs, -⟩ := GlobalTheory.ChrWSmooth.chrW_nu_smooth_unitary hKP.base F E σ B a a' G X om om' hT B.v₁ hv B.τ₁
  have hP := GlobalTheory.ThK.Inhab.pairV' hT
  have hle : a' ≤ a + a' := by omega
  set ν : (Fv F B.v₁)ˣ →* ℂˣ := chrW (X.α / X.β) B.τ₁ with hνdef
  have hs' : GlobalTheory.SmGL.IsSmoothChar ν := hs
  have hiff := GlobalTheory.SoLocAnyIntertwiner.soLoc_iff hKP F E σ B a a' G X om om' hT ι hι
  have hspanSB : Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁) ≤ SB (Fin a' × Fin (a + a') → Fv F B.v₁) :=
    Submodule.span_le.2 fun φ h => h.1
  have hxSB := hspanSB hx

  have hvan : ∀ y ∈ Submodule.span ℂ (G.M'.SoLoc B.ψ B.τ₁), ∀ Y : Matrix (Fin a') (Fin (a + a')) (Fv F B.v₁),
      Y.rank ≠ a' → ι y Y = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem φ hφ => exact (hiff φ hφ.1).1 hφ
    | zero => intro Y _; simp
    | add y z _ _ hy hz => intro Y hY; simp [hy Y hY, hz Y hY]
    | smul c y _ hy => intro Y hY; simp [hy Y hY]
  have hfull : ι x ∈ GlobalTheory.FullRankCoinv.fullRk (Fv F B.v₁) a' (a + a') := ⟨hι.bij.mapsTo hxSB, hvan x hx⟩

  letI : MeasurableSpace (Fv F B.v₁) := borel _
  haveI : BorelSpace (Fv F B.v₁) := ⟨rfl⟩
  have hF : ∀ h : GL (Fin (a + a')) (Fv F B.v₁), smallF (haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a'))) ν (ι x)
      (GlobalTheory.FullRankCoinv.Y0 (Fv F B.v₁) a' (a + a') * h.val) = 0 := by
    intro h
    haveI := GlobalTheory.TranslationGLHaar.isHaar_map_trGL a' (haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a')))
    have hY : (GlobalTheory.FullRankCoinv.Y0 (Fv F B.v₁) a' (a + a') * h.val).rank = a' := by
      rw [Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units h)]
      exact GlobalTheory.TranslationGLHaar.rank_zeroth_component_eq hle
    have h1 := hint ((haarVol (GlobalTheory.SplitWeil.KO (Fv F B.v₁) (Fin a'))).map (GlobalTheory.TranslationGLHaar.trGL a')) _ hY
    rw [GlobalTheory.TranslationGLHaar.integral_map_trGL] at h1
    refine (integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)).trans h1
    exact (GlobalTheory.TranslationGLHaar.omB_trGL _ _ g _ _).symm
  have haug : ι x ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν :=
    GlobalTheory.T.full_rank_zeta_kernel (Fv F B.v₁) a' (a + a') ν hle hs' (ι x) hfull hF

  have hcm : IsCMExt F E σ := hT.base.cm
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  have hdet : IsUnit (G.V'.J.map B.τ₁).det :=
    GlobalTheory.SplitUnitLift.isUnit_det_of_cartan G.V'.J B.τ₁ (B.emb w).1 1 one_ne_zero (G.V'.θ w)
      (by rw [one_smul]; exact hT.geo.hV'.cartan w)
  have herm : ∀ i j, σ (G.V'.J j i) = algebraMap F E 1 * G.V'.J i j := fun i j => by
    rw [map_one, one_mul]; exact hT.geo.hV'.herm i j
  let K := GlobalTheory.SplitUnitLift.liftU hcm B.τ₁ G.V'.J 1 herm hdet
  have hKU : ∀ g, K g ∈ UAt σ G.V' (evFin F B.v₁) := fun g =>
    GlobalTheory.SplitUnitLift.liftU_mem_UAt hcm B.τ₁ G.V' 1 herm hdet g
  have hKm : ∀ g, GlobalTheory.KSplit.locMat B.τ₁ 1 (K g) = g := fun g => Units.ext (by
    rw [GlobalTheory.KSplit.locMat_val, GlobalTheory.SplitUnitLift.liftU_piW]; simp)
  have h1W : (1 : UA σ G.W.J) ∈ UAt σ G.W (evFin F B.v₁) :=
    GlobalTheory.ThK.mem_UAtSub.1 (Subgroup.one_mem _)

  have hgen : ∀ z ∈ GlobalTheory.FullRankCoinv.augRk a' (a + a') ν, ∃ y ∈ Submodule.span ℂ {y | ∃ g ∈ UAt σ G.V' (evFin F B.v₁),
      ∃ ψ ∈ G.M'.SoLoc B.ψ B.τ₁, ∃ ψ' ∈ G.M'.SoLoc B.ψ B.τ₁, Acts (evFin F B.v₁) (om' (g, 1)) ψ ψ' ∧ y = ψ' - ψ},
      ι y = z := by
    intro z hz
    induction hz using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨g, Ψ, hΨ, rfl⟩ := hz
      obtain ⟨ψ, hψ, rfl⟩ := hι.bij.surjOn hΨ.1
      have hψS : ψ ∈ G.M'.SoLoc B.ψ B.τ₁ := (hiff ψ hψ).2 hΨ.2
      obtain ⟨S, hS⟩ := GlobalTheory.WeilLocality.locality B G X om om' hT B.v₁ (K g) (hKU g)
      obtain ⟨hS1, hA⟩ := hS ψ hψ
      have he : ι (S ψ) = GlobalTheory.FullRankCoinv.lact ν g (ι ψ) := by
        rw [GlobalTheory.OppLagr.act_linBar hKP.base F E σ B a' (a + a') G.V' G.W G.M' X.α (X.α / X.β) om' _ _ _ _ hP B.v₁ B.τ₁
          1 1 ι hι (K g) (hKU g) 1 h1W ψ hψ (S ψ) hS1 hA, hKm g, map_one]
        exact GlobalTheory.TranslationGLHaar.omB_one_eq_lact _ _ g _
      have hSS : S ψ ∈ G.M'.SoLoc B.ψ B.τ₁ :=
        (hiff (S ψ) hS1).2 (fun Y hY => by rw [he]; exact (GlobalTheory.TranslationGLHaar.lact_mem_fullRk ν g hΨ).2 Y hY)
      exact ⟨S ψ - ψ, Submodule.subset_span ⟨K g, hKU g, ψ, hψS, S ψ, hSS, hA, rfl⟩, by rw [map_sub, he]⟩
    | zero => exact ⟨0, Submodule.zero_mem _, map_zero ι⟩
    | add z z' _ _ hz hz' =>
      obtain ⟨y, hy, e⟩ := hz
      obtain ⟨y', hy', e'⟩ := hz'
      exact ⟨y + y', Submodule.add_mem _ hy hy', by rw [map_add, e, e']⟩
    | smul c z _ hz =>
      obtain ⟨y, hy, e⟩ := hz
      exact ⟨c • y, Submodule.smul_mem _ c hy, by rw [map_smul, e]⟩
  obtain ⟨y, hy, hye⟩ := hgen _ haug
  have hySB : y ∈ SB (Fin a' × Fin (a + a') → Fv F B.v₁) := by
    refine (Submodule.span_le.2 ?_) hy
    rintro _ ⟨g, -, ψ, hψ, ψ', hψ', -, rfl⟩
    exact Submodule.sub_mem _ hψ'.1 hψ.1
  have hyx : y = x := hι.bij.injOn hySB hxSB hye
  rw [← hyx]
  exact hy

end GlobalTheory.TranslationGLHaar
