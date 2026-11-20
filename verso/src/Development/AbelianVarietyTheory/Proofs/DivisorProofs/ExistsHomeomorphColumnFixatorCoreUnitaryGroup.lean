import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsContinuousCoreUnitaryGroupEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCoreIsometryOfFixesIsotropicFrameStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqOfFrameCols
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hF`. Take `⟨e, econt, eprop, erat⟩` from `GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF`. Establish `hJ₀` using `GlobalTheory.UAut.det_isUnit hF.herm₀`. Use `set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0`. Establish `p0Z : p0 * adMat F Z = 1`.

Rewrite using `[hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀, Matrix.map_one _ (map_zero _) (map_one _)]`. Establish `hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z` using `fun g => by`. Rewrite using `[Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]`. Establish `inj : Function.Injective e` using `fun g h hgh => by`. Apply `matHom_injective _ σ J₀` to reduce the goal to its premises.

Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[hrec g, hrec h, hgh]`. Establish `DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 = adMat F (cT (σ : E →+* E) D * J)`. Introduce `x hx`. Establish `h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E))`.

Rewrite using `[Matrix.mul_one]`. Conclude with `(fixG σ J D).inv_mem hx`. Use `GlobalTheory.UAut.form_mul_of_mul_cols h1` as an intermediate fact. Rewrite `this` using `[inv_inv, Formalism.UG.cT_one, Matrix.one_mul]`. Then use the resulting hypothesis. Establish `surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x`.

Introduce `x hx`. Establish `hxC : (matHom _ σ J x).1 * adMat F C = adMat F C` using `(Subgroup.mem_inf.1 hx).1`. Establish `hxD : (matHom _ σ J x).1 * adMat F D = adMat F D` using `(Subgroup.mem_inf.1 hx).2`. Take `⟨g₀, b, h1, h2, -, -⟩` from `GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1`. Establish `hb : b = 0`.

Rewrite using `[h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]`. Establish `aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C` using `(eprop g₀).1`. Establish `aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D` using `(eprop g₀).2.1`. Use `⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[aC, hxC]`.

Rewrite using `[(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]`. Rewrite using `[aD, hxD]`. Set `f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D)` to `e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)`. Establish `fbij : Function.Bijective f` using `⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>`. Set `⟨g, hg⟩` to `surj x.1 x.2`.

Use the proof step `⟨g, Subtype.ext hg⟩⟩`. Set `me` to `MulEquiv.ofBijective f fbij`. Establish `hme : ∀ x, e (me.symm x) = x.1` using `fun x => congrArg Subtype.val (me.apply_symm_apply x)`. Establish `cM : Continuous (matHom (AF F) σ J)` using `(isEmbedding_matHom (AF F) σ J).continuous`. Establish `contInv : Continuous me.symm` using `by haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩ haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _`.

Rewrite using `[(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]`. Prove the components needed by the constructor for the conclusion. Establish `: (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) = fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z` using `funext fun x => by`. Simplify using `only [Function.comp_apply]`. Rewrite using `[hrec, hme]`.

Rewrite using `[this]`. Conclude with `(continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul continuous_const`. Establish `: (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) = fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z` using `funext fun x => by`. Simplify using `only [Function.comp_apply]`. Rewrite using `[← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]`.

Rewrite using `[this]`. Conclude with `(continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul continuous_const`. Use `⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩` and prove the remaining obligations. Introduce `g`. Express the relevant statement in the definitionally equal form `g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J`.

Use `⟨erat g, fun hg => ?_⟩` and prove the remaining obligations. Take `⟨g₀, b, -, -, h3, h4⟩` from `GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1`. Establish `: g₀ = g` using `matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))`. Conclude with `this ▸ h4 hg`.
-/
theorem fixFrames_equiv_core : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∃ e : GAd σ J₀ ≃ₜ* (fixG σ J C ⊓ fixG σ J D : Subgroup (GAd σ J)), ∀ g, g ∈ ratPts σ J₀ ↔ (e g : GAd σ J) ∈ ratPts σ J := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hF
  obtain ⟨e, econt, eprop, erat⟩ := GlobalTheory.T.exists_continuous_core_unitaryGroup_embedding F E σ n J j m C D Z J₀ hF
  have hJ₀ := GlobalTheory.UAut.det_isUnit hF.herm₀
  set p0 : Matrix (Fin m) (Fin n) (AF F ⊗[F] E) := adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) with hp0
  have p0Z : p0 * adMat F Z = 1 := by
    rw [hp0, ← Matrix.map_mul, Matrix.mul_assoc, hF.zz, Matrix.nonsing_inv_mul _ hJ₀,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hrec : ∀ g, (matHom _ σ J₀ g).1 = p0 * (matHom _ σ J (e g)).1 * adMat F Z := fun g => by
    rw [Matrix.mul_assoc, (eprop g).2.2, ← Matrix.mul_assoc, p0Z, Matrix.one_mul]
  have inj : Function.Injective e := fun g h hgh => by
    apply matHom_injective _ σ J₀
    apply Units.ext
    rw [hrec g, hrec h, hgh]
  have DJx : ∀ x ∈ fixG σ J D, adMat F (cT (σ : E →+* E) D * J) * (matHom _ σ J x).1 =
      adMat F (cT (σ : E →+* E) D * J) := by
    intro x hx
    have h1 : (matHom _ σ J x⁻¹).1 * adMat F D = adMat F D * (1 : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) := by
      rw [Matrix.mul_one]; exact (fixG σ J D).inv_mem hx
    have := GlobalTheory.UAut.form_mul_of_mul_cols h1
    rwa [inv_inv, Formalism.UG.cT_one, Matrix.one_mul] at this
  have surj : ∀ x ∈ fixG σ J C ⊓ fixG σ J D, ∃ g, e g = x := by
    intro x hx
    have hxC : (matHom _ σ J x).1 * adMat F C = adMat F C := (Subgroup.mem_inf.1 hx).1
    have hxD : (matHom _ σ J x).1 * adMat F D = adMat F D := (Subgroup.mem_inf.1 hx).2
    obtain ⟨g₀, b, h1, h2, -, -⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF x (Subgroup.mem_inf.1 hx).1
    have hb : b = 0 := by
      rw [h2, DJx x (Subgroup.mem_inf.1 hx).2, ← Matrix.map_mul, hF.dz, Matrix.map_zero _ (map_zero _)]
    have aC : (matHom _ σ J (e g₀)).1 * adMat F C = adMat F C := (eprop g₀).1
    have aD : (matHom _ σ J (e g₀)).1 * adMat F D = adMat F D := (eprop g₀).2.1
    refine ⟨g₀, eq_of_frame_cols F E σ n J j m C D Z J₀ hF _ _ ?_ ?_ ?_⟩
    · rw [aC, hxC]
    · rw [(eprop g₀).2.2, h1, hb, Matrix.mul_zero, add_zero]
    · rw [aD, hxD]
  let f : GAd σ J₀ →* ↥(fixG σ J C ⊓ fixG σ J D) :=
    e.codRestrict _ (fun g => Subgroup.mem_inf.2 ⟨(eprop g).1, (eprop g).2.1⟩)
  have fbij : Function.Bijective f :=
    ⟨fun g h hgh => inj (congrArg Subtype.val hgh), fun x =>
      let ⟨g, hg⟩ := surj x.1 x.2; ⟨g, Subtype.ext hg⟩⟩
  let me := MulEquiv.ofBijective f fbij
  have hme : ∀ x, e (me.symm x) = x.1 := fun x => congrArg Subtype.val (me.apply_symm_apply x)
  have cM : Continuous (matHom (AF F) σ J) := (isEmbedding_matHom (AF F) σ J).continuous
  have contInv : Continuous me.symm := by
    haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
    haveI : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
    rw [(isEmbedding_matHom (AF F) σ J₀).continuous_iff, Units.continuous_iff]
    constructor
    · have : (Units.val ∘ (matHom (AF F) σ J₀ ∘ me.symm)) =
          fun x => p0 * (matHom _ σ J x.1).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]; rw [hrec, hme]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_val.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
    · have : (fun x => (((matHom (AF F) σ J₀ ∘ me.symm) x)⁻¹ : GL _ _).val) =
          fun x => p0 * ((matHom _ σ J x.1)⁻¹ : GL _ _).1 * adMat F Z := funext fun x => by
        simp only [Function.comp_apply]
        rw [← map_inv (matHom _ σ J₀), ← map_inv me.symm, hrec, hme, Subgroup.coe_inv, map_inv]
      rw [this]
      exact (continuous_const.matrix_mul (Units.continuous_coe_inv.comp (cM.comp continuous_subtype_val))).matrix_mul
        continuous_const
  refine ⟨{ toMulEquiv := me, continuous_toFun := continuous_induced_rng.2 econt, continuous_invFun := contInv }, ?_⟩
  intro g
  change g ∈ ratPts σ J₀ ↔ e g ∈ ratPts σ J
  refine ⟨erat g, fun hg => ?_⟩
  obtain ⟨g₀, b, -, -, h3, h4⟩ := GlobalTheory.T.exists_coreIsometry_of_fixes_isotropicFrame F E σ n J j m C D Z J₀ hF (e g) (eprop g).1
  have : g₀ = g := matHom_injective _ σ J₀ (Units.ext (h3.trans (hrec g).symm))
  exact this ▸ h4 hg

end GlobalTheory.SphEis
