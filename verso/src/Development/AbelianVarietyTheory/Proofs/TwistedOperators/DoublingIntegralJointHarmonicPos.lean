import Mathlib
import Formalism.SharpRestriction.Divisibility.SchurIrreducible
import Formalism.LocalToGlobal.BesselHermitianTheta.DefsReal
import Development.AbelianVarietyTheory.Definitions.Foundations.IsFockIPOfFockData
import Development.AbelianVarietyTheory.Proofs.HeightProofs.FiniteDimKStableSubspaceKFiniteLie
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AnalyticOnNhdOrbitPolStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CoverUpqClosureExpTopAndCartanStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockDerivedActionsTensorMembersStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockHarmonicsGradedCompactStableStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InnerExpJointHarmPosStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GlBlockFiniteDimModuleStructureStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialsLocallyFiniteRationalWeightsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommuteStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CasimirCentralAndOnHighestWeightStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DiscreteSeriesIntegrableCoefficientProjectorStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FockModelDualPairCasimirApplyStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CasimirNumberIdentityDualPair
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EmbedsOfLowestTypeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.LowestKTypesJointHarmonicShapeStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoubleCoverUpqKsetGeneratedByExpStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PairKEquivariantOfLieAlgebraCompatStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DoublingCoefficientsVanishOfOneVanishesStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.EqZeroOfPositiveCoeffOrthogonalEmbeddingsStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DerivedAdjointStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerEqOfIrreducibleStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AnalyticOnNhdOrbitOfDerivSeqNormEqStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.InnerCoeffEqOfIsometricAnalyticModulesStatement
open Formalism.BasicNotions.TH Formalism.MainNotions.SchurIrreducible GlobalTheory.FockAlg MeasureTheory Matrix
open GlobalTheory.RealPar.KStabLie

noncomputable section

namespace GlobalTheory.DoublingPos

variable {p q r s : ℕ}

/- English proof (translation)
Use `haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))`. Use `haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`. Use `haveI : SecondCountableTopology ℂᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology`. Use `haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology`. Use `haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology`.

Conclude with `T.emb.secondCountableTopology`.
-/
theorem secondCountable (T : GrpData p q) : SecondCountableTopology T.G := by
  haveI : SecondCountableTopology (Mat p q) := inferInstanceAs (SecondCountableTopology (Ix p q → Ix p q → ℂ))
  haveI : SecondCountableTopology (Mat p q)ᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology ℂᵐᵒᵖ := MulOpposite.opHomeomorph.symm.secondCountableTopology
  haveI : SecondCountableTopology (GL (Ix p q) ℂ) := Units.isEmbedding_embedProduct.secondCountableTopology
  haveI : SecondCountableTopology ℂˣ := Units.isEmbedding_embedProduct.secondCountableTopology
  exact T.emb.secondCountableTopology

/- English proof (translation)
Use `haveI := secondCountable T`. Establish `h : Integrable (fun g => e g • πU.π g x) T.haar`. Use `Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_smul, πU.isom]`. Unfold `opE`.

Rewrite using `[← integral_inner h]`. Simplify using `only [inner_smul_right]`.
-/
theorem inner_opE (T : GrpData p q) (πU : URep T) {e : T.G → ℂ} (hi : Integrable e T.haar)
    (hc : Continuous e) (z x : πU.H) :
    inner ℂ z (opE T πU.π e x) = ∫ g, e g * inner ℂ z (πU.π g x) ∂T.haar := by
  haveI := secondCountable T
  have h : Integrable (fun g => e g • πU.π g x) T.haar := by
    refine Integrable.mono' (hi.norm.mul_const ‖x‖) (hc.smul (πU.cont x)).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_smul, πU.isom]
  unfold opE
  rw [← integral_inner h]
  simp only [inner_smul_right]

/- English proof (translation)
The claim follows from `continuous_const.inner (D.U.cont _)`.
-/
theorem continuous_mcoef {T : GrpData p q} (D : DSRep T) (v : D.HK.V) : Continuous (mcoef D v) :=
  continuous_const.inner (D.U.cont _)

/- English proof (translation)
The claim follows from `continuous_const.mul (continuous_mcoef D v).star`.
-/
theorem continuous_eFun {T : GrpData p q} (D : DSRep T) (v : D.HK.V) : Continuous (eFun D v) :=
  continuous_const.mul (continuous_mcoef D v).star

/- English proof (translation)
Establish `hd : (D.fdeg : ℂ) ≠ 0` using `by exact_mod_cast D.fdeg_pos.ne'`. Establish `h1 : Integrable (fun g => star (mcoef D v g)) T.haar`. Use `h.const_mul (D.fdeg : ℂ)⁻¹` as an intermediate fact. Use `this.congr (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using `only [eFun]`.

Clear the denominators using the available nonvanishing facts. Use `Integrable.mono' h1.norm (continuous_mcoef D v).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Simplify using the standard rewrite rules.
-/
theorem integrable_mcoef {T : GrpData p q} (D : DSRep T) (v : D.HK.V) (h : Integrable (eFun D v) T.haar) :
    Integrable (mcoef D v) T.haar := by
  have hd : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'
  have h1 : Integrable (fun g => star (mcoef D v g)) T.haar := by
    have := h.const_mul (D.fdeg : ℂ)⁻¹
    refine this.congr (Filter.Eventually.of_forall fun g => ?_)
    simp only [eFun]
    field_simp
  refine Integrable.mono' h1.norm (continuous_mcoef D v).aestronglyMeasurable
    (Filter.Eventually.of_forall fun g => ?_)
  simp

def ugk (T : GrpData p q) (πU : URep T) (M : GKMod p q) (j : M.V →ₗ[ℂ] πU.H) (hj : Function.Injective j)
    (hd : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => πU.π (T.expt (t • Y)) (j x)) (j (M.act Y x)) 0) :
    UGKMod p q where
  M := M
  ip := ((innerₛₗ ℂ).comp j).compl₂ j
  herm x y := by simp [inner_conj_symm]
  pos x hx := by
    have : j x ≠ 0 := fun h => hx (hj (by simpa using h))
    have h2 := norm_pos_iff.2 this
    simp only [LinearMap.compl₂_apply, LinearMap.comp_apply, innerₛₗ_apply_apply]
    have h3 := inner_self_eq_norm_sq (𝕜 := ℂ) (j x)
    simp only [RCLike.re_to_complex] at h3
    rw [h3]
    positivity
  adj Z x y := GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt p q T πU M j hd Z x y

def prodAct (M₁ M₂ : GKMod p q) : Mat p q →ₗ[ℂ] Module.End ℂ (M₁.V × M₂.V) where
  toFun Z := (M₁.act Z).prodMap (M₂.act Z)
  map_add' Y Z := by ext <;> simp
  map_smul' c Z := by ext <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem prodAct_apply (M₁ M₂ : GKMod p q) (Z : Mat p q) (w : M₁.V × M₂.V) :
    prodAct M₁ M₂ Z w = (M₁.act Z w.1, M₂.act Z w.2) := rfl

/- English proof (translation)
Introduce `Y Z _ _` and use `M.lie Y Z`.
-/
theorem isKLie (M : GKMod p q) : IsKLieAct M.act := fun Y Z _ _ => M.lie Y Z

/- English proof (translation)
Take `⟨W, hW, hv, hK⟩` from `M.kfin v`. Conclude with `((GlobalTheory.T.glBlock_finiteDim_module_structure p q M.V M.act (isKLie M) W hW hK (fun v _ => M.wts v)).2.2.2 μ v hv h).2.1`.
-/
theorem ofType_of_isHW (M : GKMod p q) {μ : Ix p q → ℚ} {v : M.V} (h : IsHW M.act μ v) : OfType M.act μ v := by
  obtain ⟨W, hW, hv, hK⟩ := M.kfin v
  exact ((GlobalTheory.T.glBlock_finiteDim_module_structure p q M.V M.act (isKLie M) W hW hK (fun v _ => M.wts v)).2.2.2 μ v hv h).2.1

/- English proof (translation)
Simplify using `[wtSub, sub_eq_zero]`.
-/
theorem mem_wtSub {V : Type*} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (v : V) : v ∈ wtSub act μ ↔ ∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v := by
  simp [wtSub, sub_eq_zero]

/- English proof (translation)
Simplify using `[hwSub, mem_wtSub]`.
-/
theorem mem_hwSub {V : Type*} [AddCommGroup V] [Module ℂ V] (act : Mat p q →ₗ[ℂ] Module.End ℂ V)
    (μ : Ix p q → ℚ) (v : V) : v ∈ hwSub act μ ↔
      (∀ a, act (Eab a a) v = ((μ a : ℚ) : ℂ) • v) ∧ ∀ a b, posC a b → act (Eab a b) v = 0 := by
  simp [hwSub, mem_wtSub]

/- English proof (translation)
Take `⟨W₁, hW₁, hv₁, hK₁⟩` from `M₁.kfin v₁`. Take `⟨W₂, hW₂, hv₂, hK₂⟩` from `M₂.kfin v₂`. Establish `hK : KStable (prodAct M₁ M₂) (W₁.prod W₂)` using `fun Z hZ w hw => ⟨hK₁ Z hZ _ hw.1, hK₂ Z hZ _ hw.2⟩`. Use `haveI hW : FiniteDimensional ℂ (W₁.prod W₂) := by`. Conclude with `Module.Finite.iff_fg.2 (Submodule.FG.prod (Module.Finite.iff_fg.1 hW₁) (Module.Finite.iff_fg.1 hW₂))`.

Establish `hlie : IsKLieAct (prodAct M₁ M₂)`. Introduce `Y Z _ _`. Use `LinearMap.ext fun w => ?_` and prove the remaining obligations. Rewrite using `[prodAct_apply, M₁.lie Y Z, M₂.lie Y Z]`. Both sides reduce to the same expression.

Establish `hwt : ∀ w, w ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν`. Introduce and unpack `⟨x, y⟩`. Establish `hx : ((x, 0) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν`. Use `Submodule.iSup_induction _ (motive := fun x => ((x, 0) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν) (M₁.wts x) (fun ν x hx => ?_) (Submodule.zero_mem _) (fun x y hx hy => by simpa using Submodule.add_mem _ hx hy)` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem ν ?_` and prove the remaining obligations.

Rewrite `hx`, the goal using `[mem_wtSub]`. Introduce `a`. Simplify using `[prodAct_apply, hx a]`. Establish `hy : ((0, y) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν`. Use `Submodule.iSup_induction _ (motive := fun x => ((0, x) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν) (M₂.wts y) (fun ν x hx => ?_) (Submodule.zero_mem _) (fun x y hx hy => by simpa using Submodule.add_mem _ hx hy)` and prove the remaining obligations.

Use `Submodule.mem_iSup_of_mem ν ?_` and prove the remaining obligations. Rewrite `hx`, the goal using `[mem_wtSub]`. Introduce `a`. Simplify using `[prodAct_apply, hx a]`. Simplify using `using Submodule.add_mem _ hx hy`.

Establish `hhw : IsHW (prodAct M₁ M₂) μ (v₁, v₂)`. Use `⟨fun h => h₁.1 (congrArg Prod.fst h), ?_⟩` and prove the remaining obligations. Establish `a₁` using `(mem_hwSub _ _ _).1 h₁.2`. Establish `a₂` using `(mem_hwSub _ _ _).1 h₂.2`. Rewrite using `[mem_hwSub]`.

Conclude with `⟨fun a => by simp [prodAct_apply, a₁.1 a, a₂.1 a], fun a b hab => by simp [prodAct_apply, a₁.2 a b hab, a₂.2 a b hab]⟩`. Establish `key` using `((GlobalTheory.T.glBlock_finiteDim_module_structure p q _ _ hlie (W₁.prod W₂) hW hK (fun v _ => hwt v)).2.2.2 μ _ ⟨hv₁, hv₂⟩ hhw).2.2`. Establish `hmin : ∀ N, (v₁, v₂) ∈ N → KStable (prodAct M₁ M₂) N → sInf {N | (v₁, v₂) ∈ N ∧ KStable (prodAct M₁ M₂) N} ≤ N` using `fun N h1 h2 => sInf_le ⟨h1, h2⟩`. Use `⟨sInf {N | (v₁, v₂) ∈ N ∧ KStable (prodAct M₁ M₂) N}, Submodule.finiteDimensional_of_le (hmin (W₁.prod W₂) ⟨hv₁, hv₂⟩ hK), ?_, ?_, hmin, fun U hU hle => ?_⟩` and prove the remaining obligations. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.1`.

Introduce `Z hZ w hw`. Conclude with `Submodule.mem_sInf.2 fun N hN => hN.2 Z hZ w (Submodule.mem_sInf.1 hw N hN)`. Conclude with `(key U hU hle).imp id fun h => le_antisymm hle (hmin U h hU)`.
-/
theorem exists_diag (M₁ M₂ : GKMod p q) {μ : Ix p q → ℚ} {v₁ : M₁.V} {v₂ : M₂.V}
    (h₁ : IsHW M₁.act μ v₁) (h₂ : IsHW M₂.act μ v₂) :
    ∃ E : Submodule ℂ (M₁.V × M₂.V), FiniteDimensional ℂ E ∧ (v₁, v₂) ∈ E ∧ KStable (prodAct M₁ M₂) E ∧
      (∀ N, (v₁, v₂) ∈ N → KStable (prodAct M₁ M₂) N → E ≤ N) ∧
      ∀ U, KStable (prodAct M₁ M₂) U → U ≤ E → U = ⊥ ∨ U = E := by
  obtain ⟨W₁, hW₁, hv₁, hK₁⟩ := M₁.kfin v₁
  obtain ⟨W₂, hW₂, hv₂, hK₂⟩ := M₂.kfin v₂
  have hK : KStable (prodAct M₁ M₂) (W₁.prod W₂) := fun Z hZ w hw => ⟨hK₁ Z hZ _ hw.1, hK₂ Z hZ _ hw.2⟩
  haveI hW : FiniteDimensional ℂ (W₁.prod W₂) := by
    exact Module.Finite.iff_fg.2 (Submodule.FG.prod (Module.Finite.iff_fg.1 hW₁) (Module.Finite.iff_fg.1 hW₂))
  have hlie : IsKLieAct (prodAct M₁ M₂) := by
    intro Y Z _ _
    refine LinearMap.ext fun w => ?_
    rw [prodAct_apply, M₁.lie Y Z, M₂.lie Y Z]
    rfl
  have hwt : ∀ w, w ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν := by
    rintro ⟨x, y⟩
    have hx : ((x, 0) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν := by
      refine Submodule.iSup_induction _ (motive := fun x => ((x, 0) : M₁.V × M₂.V) ∈
        ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν) (M₁.wts x) (fun ν x hx => ?_) (Submodule.zero_mem _)
        (fun x y hx hy => by simpa using Submodule.add_mem _ hx hy)
      refine Submodule.mem_iSup_of_mem ν ?_
      rw [mem_wtSub] at hx ⊢
      intro a
      simp [prodAct_apply, hx a]
    have hy : ((0, y) : M₁.V × M₂.V) ∈ ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν := by
      refine Submodule.iSup_induction _ (motive := fun x => ((0, x) : M₁.V × M₂.V) ∈
        ⨆ ν : Ix p q → ℚ, wtSub (prodAct M₁ M₂) ν) (M₂.wts y) (fun ν x hx => ?_) (Submodule.zero_mem _)
        (fun x y hx hy => by simpa using Submodule.add_mem _ hx hy)
      refine Submodule.mem_iSup_of_mem ν ?_
      rw [mem_wtSub] at hx ⊢
      intro a
      simp [prodAct_apply, hx a]
    simpa using Submodule.add_mem _ hx hy
  have hhw : IsHW (prodAct M₁ M₂) μ (v₁, v₂) := by
    refine ⟨fun h => h₁.1 (congrArg Prod.fst h), ?_⟩
    have a₁ := (mem_hwSub _ _ _).1 h₁.2
    have a₂ := (mem_hwSub _ _ _).1 h₂.2
    rw [mem_hwSub]
    exact ⟨fun a => by simp [prodAct_apply, a₁.1 a, a₂.1 a],
      fun a b hab => by simp [prodAct_apply, a₁.2 a b hab, a₂.2 a b hab]⟩
  have key := ((GlobalTheory.T.glBlock_finiteDim_module_structure p q _ _ hlie (W₁.prod W₂) hW hK (fun v _ => hwt v)).2.2.2 μ _ ⟨hv₁, hv₂⟩ hhw).2.2
  have hmin : ∀ N, (v₁, v₂) ∈ N → KStable (prodAct M₁ M₂) N →
      sInf {N | (v₁, v₂) ∈ N ∧ KStable (prodAct M₁ M₂) N} ≤ N := fun N h1 h2 => sInf_le ⟨h1, h2⟩
  refine ⟨sInf {N | (v₁, v₂) ∈ N ∧ KStable (prodAct M₁ M₂) N},
    Submodule.finiteDimensional_of_le (hmin (W₁.prod W₂) ⟨hv₁, hv₂⟩ hK), ?_, ?_, hmin, fun U hU hle => ?_⟩
  · exact Submodule.mem_sInf.2 fun N hN => hN.1
  · intro Z hZ w hw
    exact Submodule.mem_sInf.2 fun N hN => hN.2 Z hZ w (Submodule.mem_sInf.1 hw N hN)
  · exact (key U hU hle).imp id fun h => le_antisymm hle (hmin U h hU)

/- English proof (translation)
Introduce `hz`. Take `⟨E, hE, hv, hK, hmin, hirr⟩` from `exists_diag M₁ M₂ h₁ h₂`. Set `i₁ : E →ₗ[ℂ] π₁.H` to `j₁ ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ E.subtype`. Set `i₂ : E →ₗ[ℂ] π₂.H` to `j₂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ E.subtype`. Establish `hi₂ : Function.Injective i₂`.

Establish `hU : KStable (prodAct M₁ M₂) (E ⊓ LinearMap.ker (LinearMap.snd ℂ _ _))`. Introduce `Z hZ w hw`. Use `⟨hK Z hZ w hw.1, ?_⟩` and prove the remaining obligations. Establish `: w.2 = 0` using `hw.2`. Express the relevant statement in the definitionally equal form `M₂.act Z w.2 = 0`.

Rewrite using `[this, map_zero]`. Break down `hirr _ hU inf_le_left with h | h` into its components or cases. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `w hw`. Establish `h0 : (w : M₁.V × M₂.V).2 = 0` using `hj₂ (by rw [map_zero]; exact hw)`.

Establish `: (w : M₁.V × M₂.V) ∈ E ⊓ LinearMap.ker (LinearMap.snd ℂ _ _)` using `⟨w.2, h0⟩`. Rewrite `this` using `[h]`. Conclude with `Subtype.ext this`. Rewrite `hv` using `[← h]`. Conclude with `(h₂.1 hv.2).elim`.

Set `a : Mat p q → E →ₗ[ℂ] E` to `fun Z => if h : IsKC Z then (prodAct M₁ M₂ Z).restrict (hK Z h) else 0`. Establish `ha : ∀ Z, IsKC Z → ∀ w : E, (a Z w : M₁.V × M₂.V) = prodAct M₁ M₂ Z w`. Introduce `Z hZ w`. Simplify using `only [a, dif_pos hZ, LinearMap.restrict_coe_apply]`. Establish `heq` using `GlobalTheory.T.pair_kEquivariant_of_lieAlgebra_compat p q T (GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp p q hn T) π₁ π₂ E a i₁ i₂ (by`.

Introduce `Y hY hYK w`. Simplify using `only [i₁, i₂, LinearMap.comp_apply, Submodule.subtype_apply, ha Y hYK]`. Conclude with `⟨hd₁ Y hY _, hd₂ Y hY _⟩)`. Establish `hirr' : ∀ U : Submodule ℂ E, (∀ k ∈ T.Kset, ∀ w ∈ U, ∀ w' : E, π₂.π k (i₂ w) = i₂ w' → w' ∈ U) → U = ⊥ ∨ U = ⊤`. Introduce `U hU`.

Establish `key : ∀ Y ∈ upq p q, IsKC Y → ∀ w ∈ U, a Y w ∈ U`. Introduce `Y hY hYK w hw`. Establish `: i₂ (a Y w) ∈ U.map i₂`. Use `deriv_mem (f := fun t : ℝ => π₂.π (T.expt (t • Y)) (i₂ w)) _ ?_ fun t => ?_` and prove the remaining obligations. Simplify using `only [i₂, LinearMap.comp_apply, Submodule.subtype_apply, ha Y hYK]`.

Conclude with `hd₂ Y hY _`. Take `⟨w', -, h2⟩` from `heq _ (expt_mem T hY hYK t) w`. Conclude with `⟨w', hU _ (expt_mem T hY hYK t) w hw w' h2, h2.symm⟩`. Take `⟨u, hu, hu'⟩` from `this`. Rewrite using `[← hi₂ hu']`.

Conclude with `hu`. Establish `hUK : KStable (prodAct M₁ M₂) (U.map E.subtype)`. Introduce and unpack `Z hZ _ ⟨w, hw, rfl⟩`. Take `⟨X, Y, hX, hXK, hY, hYK, rfl⟩` from `exists_decomp hZ`. Rewrite using `[map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply, ← ha X hXK, ← ha Y hYK]`.

Conclude with `Submodule.add_mem _ ⟨_, key X hX hXK w hw, rfl⟩ (Submodule.smul_mem _ _ ⟨_, key Y hY hYK w hw, rfl⟩)`. Break down `hirr _ hUK (Submodule.map_subtype_le _ _) with h | h` into its components or cases. Use `left`. Apply `Submodule.map_injective_of_injective E.subtype_injective` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_bot]`.

Use `right`. Apply `Submodule.map_injective_of_injective E.subtype_injective` to reduce the goal to its premises. Rewrite using `[h, Submodule.map_subtype_top]`. Establish `hvan` using `GlobalTheory.T.doublingCoefficients_vanish_of_one_vanishes p q T π₁ π₂ E i₁ i₂ hi₂ heq hirr' ⟨_, hv⟩ (fun h => h₁.1 (congrArg (fun w : E => (w : M₁.V × M₂.V).1) h)) hi hz`. Establish `h0` using `GlobalTheory.T.eq_zero_of_positive_coeff_orthogonal_embeddings p q T (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hn T).2 π₁ π₂ E i₁ i₂ hi₂ heq (fun Y hY w => hp₁ Y hY _ (hmin (N₁.comap (LinearMap.fst ℂ _ _)) hN (fun Z hZ w hw => hNK Z hZ _ hw) w.2)) (fun Y hY w => hp₂ …`.

Take `⟨W, hW, hvW, hWK, hWμ⟩` from `ofType_of_isHW M₂ h₂`. Conclude with `⟨W, hW, hmin (W.comap (LinearMap.snd ℂ _ _)) hvW (fun Z hZ w hw => hWK Z hZ _ hw) w.2, hWK, hWμ⟩)) hvan`. Conclude with `hv₁ (LinearMap.congr_fun h0 ⟨_, hv⟩)`.
-/
theorem exists_coeff_ne_zero (hn : 1 ≤ p + q) (T : GrpData p q) (π₁ π₂ : URep T) (M₁ M₂ : GKMod p q)
    (j₁ : M₁.V →ₗ[ℂ] π₁.H) (j₂ : M₂.V →ₗ[ℂ] π₂.H) (hj₂ : Function.Injective j₂)
    (hd₁ : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M₁.act Y x)) 0)
    (hd₂ : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M₂.act Y x)) 0)
    {μ : Ix p q → ℚ} {v₁ : M₁.V} {v₂ : M₂.V} (h₁ : IsHW M₁.act μ v₁) (h₂ : IsHW M₂.act μ v₂)
    (hv₁ : j₁ v₁ ≠ 0) (N₁ : Submodule ℂ M₁.V) (hN : v₁ ∈ N₁) (hNK : KStable M₁.act N₁)
    (hp₁ : ∀ Y ∈ pR p q, ∀ w ∈ N₁, (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).im = 0 ∧
      0 ≤ (inner ℂ (j₁ w) (π₁.π (T.expt Y) (j₁ w))).re)
    (hp₂ : ∀ Y ∈ pR p q, ∀ w, OfType M₂.act μ w → (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).im = 0 ∧
      0 ≤ (inner ℂ (j₂ w) (π₂.π (T.expt Y) (j₂ w))).re)
    (hi : Integrable (fun g => inner ℂ (j₂ v₂) (π₂.π g (j₂ v₂))) T.haar) :
    ¬ ∀ z : π₁.H, ∫ g, inner ℂ z (π₁.π g (j₁ v₁)) * star (inner ℂ (j₂ v₂) (π₂.π g (j₂ v₂))) ∂T.haar = 0 := by
  intro hz
  obtain ⟨E, hE, hv, hK, hmin, hirr⟩ := exists_diag M₁ M₂ h₁ h₂
  let i₁ : E →ₗ[ℂ] π₁.H := j₁ ∘ₗ LinearMap.fst ℂ _ _ ∘ₗ E.subtype
  let i₂ : E →ₗ[ℂ] π₂.H := j₂ ∘ₗ LinearMap.snd ℂ _ _ ∘ₗ E.subtype
  have hi₂ : Function.Injective i₂ := by
    have hU : KStable (prodAct M₁ M₂) (E ⊓ LinearMap.ker (LinearMap.snd ℂ _ _)) := by
      intro Z hZ w hw
      refine ⟨hK Z hZ w hw.1, ?_⟩
      have : w.2 = 0 := hw.2
      change M₂.act Z w.2 = 0
      rw [this, map_zero]
    rcases hirr _ hU inf_le_left with h | h
    · rw [injective_iff_map_eq_zero]
      intro w hw
      have h0 : (w : M₁.V × M₂.V).2 = 0 := hj₂ (by rw [map_zero]; exact hw)
      have : (w : M₁.V × M₂.V) ∈ E ⊓ LinearMap.ker (LinearMap.snd ℂ _ _) := ⟨w.2, h0⟩
      rw [h] at this
      exact Subtype.ext this
    · rw [← h] at hv
      exact (h₂.1 hv.2).elim
  classical
  let a : Mat p q → E →ₗ[ℂ] E := fun Z =>
    if h : IsKC Z then (prodAct M₁ M₂ Z).restrict (hK Z h) else 0
  have ha : ∀ Z, IsKC Z → ∀ w : E, (a Z w : M₁.V × M₂.V) = prodAct M₁ M₂ Z w := by
    intro Z hZ w
    simp only [a, dif_pos hZ, LinearMap.restrict_coe_apply]
  have heq := GlobalTheory.T.pair_kEquivariant_of_lieAlgebra_compat p q T (GlobalTheory.T.doubleCoverUpq_Kset_generated_by_exp p q hn T) π₁ π₂ E a i₁ i₂ (by
    intro Y hY hYK w
    simp only [i₁, i₂, LinearMap.comp_apply, Submodule.subtype_apply, ha Y hYK]
    exact ⟨hd₁ Y hY _, hd₂ Y hY _⟩)
  have hirr' : ∀ U : Submodule ℂ E, (∀ k ∈ T.Kset, ∀ w ∈ U, ∀ w' : E, π₂.π k (i₂ w) = i₂ w' → w' ∈ U) →
      U = ⊥ ∨ U = ⊤ := by
    intro U hU
    have key : ∀ Y ∈ upq p q, IsKC Y → ∀ w ∈ U, a Y w ∈ U := by
      intro Y hY hYK w hw
      have : i₂ (a Y w) ∈ U.map i₂ := by
        refine deriv_mem (f := fun t : ℝ => π₂.π (T.expt (t • Y)) (i₂ w)) _ ?_ fun t => ?_
        · simp only [i₂, LinearMap.comp_apply, Submodule.subtype_apply, ha Y hYK]
          exact hd₂ Y hY _
        · obtain ⟨w', -, h2⟩ := heq _ (expt_mem T hY hYK t) w
          exact ⟨w', hU _ (expt_mem T hY hYK t) w hw w' h2, h2.symm⟩
      obtain ⟨u, hu, hu'⟩ := this
      rw [← hi₂ hu']
      exact hu
    have hUK : KStable (prodAct M₁ M₂) (U.map E.subtype) := by
      rintro Z hZ _ ⟨w, hw, rfl⟩
      obtain ⟨X, Y, hX, hXK, hY, hYK, rfl⟩ := exists_decomp hZ
      rw [map_add, map_smul, LinearMap.add_apply, LinearMap.smul_apply, Submodule.subtype_apply,
        ← ha X hXK, ← ha Y hYK]
      exact Submodule.add_mem _ ⟨_, key X hX hXK w hw, rfl⟩
        (Submodule.smul_mem _ _ ⟨_, key Y hY hYK w hw, rfl⟩)
    rcases hirr _ hUK (Submodule.map_subtype_le _ _) with h | h
    · left
      apply Submodule.map_injective_of_injective E.subtype_injective
      rw [h, Submodule.map_bot]
    · right
      apply Submodule.map_injective_of_injective E.subtype_injective
      rw [h, Submodule.map_subtype_top]
  have hvan := GlobalTheory.T.doublingCoefficients_vanish_of_one_vanishes p q T π₁ π₂ E i₁ i₂ hi₂ heq hirr' ⟨_, hv⟩
    (fun h => h₁.1 (congrArg (fun w : E => (w : M₁.V × M₂.V).1) h)) hi hz
  have h0 := GlobalTheory.T.eq_zero_of_positive_coeff_orthogonal_embeddings p q T (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hn T).2 π₁ π₂ E i₁ i₂ hi₂ heq
    (fun Y hY w => hp₁ Y hY _
      (hmin (N₁.comap (LinearMap.fst ℂ _ _)) hN (fun Z hZ w hw => hNK Z hZ _ hw) w.2))
    (fun Y hY w => hp₂ Y hY _ (by
      obtain ⟨W, hW, hvW, hWK, hWμ⟩ := ofType_of_isHW M₂ h₂
      exact ⟨W, hW, hmin (W.comap (LinearMap.snd ℂ _ _)) hvW (fun Z hZ w hw => hWK Z hZ _ hw) w.2,
        hWK, hWμ⟩)) hvan
  exact hv₁ (LinearMap.congr_fun h0 ⟨_, hv⟩)

variable {T0 : GrpData (p * r + q * s) (p * s + q * r)} {T1 : GrpData p q} {T2 : GrpData r s}

abbrev fockRep (F : FockData T0 T1 T2) : URep T1 where
  H := F.H
  π := F.π.comp (MonoidHom.inl _ _)
  isom _ x := F.isom _ x
  cont x := (F.cont x).comp
    ((GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).1.comp (continuous_id.prodMk continuous_const))

abbrev polMod (p q r s : ℕ) : GKMod p q where
  V := Pol p q r s
  act := fockAct1 p q r s
  lie := (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.1
  kfin v := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).1
  wts v := ((GlobalTheory.T.fock_polynomials_locallyFinite_rationalWeights p q r s).1 v).2

/- English proof (translation)
The claim follows from `(GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1`.
-/
theorem fock_der (F : FockData T0 T1 T2) : ∀ Y ∈ upq p q, ∀ x : (polMod p q r s).V,
    HasDerivAt (fun t : ℝ => (fockRep F).π (T1.expt (t • Y)) (F.ι x)) (F.ι ((polMod p q r s).act Y x)) 0 :=
  (GlobalTheory.T.fock_derived_actions_tensor_members p q r s T0 T1 T2 F).2.1

def sg : Ix p q → ℂ := Sum.elim (fun _ => 1) (fun _ => -1)

/- English proof (translation)
Express the relevant statement in the definitionally equal form `Yᴴ * Jm p q + Jm p q * Y = 0 ↔ _`. Rewrite using `[Jm_eq, ← Matrix.ext_iff]`. Simplify using `only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply, Matrix.zero_apply, sg]`.
-/
theorem mem_upq_iff (Y : Mat p q) : Y ∈ upq p q ↔ ∀ a b, star (Y b a) * sg b + sg a * Y a b = 0 := by
  change Yᴴ * Jm p q + Jm p q * Y = 0 ↔ _
  rw [Jm_eq, ← Matrix.ext_iff]
  simp only [Matrix.add_apply, Matrix.mul_diagonal, Matrix.diagonal_mul, Matrix.conjTranspose_apply,
    Matrix.zero_apply, sg]

/- English proof (translation)
Establish `h` using `lineEquiv_isLeft l`. Apply the tactic sequence `rcases hl : lineEquiv p q r s l with x | x <;> rw [hl] at h <;>`. Apply the tactic sequence `rcases l with ⟨a | a, c | c⟩ <;> simp [linePos] at h <;> simp [sg]`.
-/
theorem sg_lineEquiv (l : Ln p q r s) : sg (lineEquiv p q r s l) = sg l.1 * sg l.2 := by
  have h := lineEquiv_isLeft l
  rcases hl : lineEquiv p q r s l with x | x <;> rw [hl] at h <;>
    rcases l with ⟨a | a, c | c⟩ <;> simp [linePos] at h <;> simp [sg]

/- English proof (translation)
Rewrite `hY`, the goal using `[mem_upq_iff]`. Introduce `a b`. Take `⟨⟨a, c⟩, rfl⟩` from `(lineEquiv p q r s).surjective a`. Take `⟨⟨b, d⟩, rfl⟩` from `(lineEquiv p q r s).surjective b`. Simplify using `only [sg_lineEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply, Matrix.kroneckerMap_apply, Matrix.one_apply]`.

Distinguish the cases in `h : c = d`. Substitute `h` using the available equality. Simplify using `only [if_true, mul_one]`. Take the linear combination `sg c * hY a b`. Simplify using `[h, Ne.symm h]`.
-/
theorem kron_mem {Y : Mat p q} (hY : Y ∈ upq p q) :
    Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)) ∈
      upq (p * r + q * s) (p * s + q * r) := by
  rw [mem_upq_iff] at hY ⊢
  intro a b
  obtain ⟨⟨a, c⟩, rfl⟩ := (lineEquiv p q r s).surjective a
  obtain ⟨⟨b, d⟩, rfl⟩ := (lineEquiv p q r s).surjective b
  simp only [sg_lineEquiv, Matrix.reindex_apply, Matrix.submatrix_apply, Equiv.symm_apply_apply,
    Matrix.kroneckerMap_apply, Matrix.one_apply]
  by_cases h : c = d
  · subst h
    simp only [if_true, mul_one]
    linear_combination sg c * hY a b
  · simp [h, Ne.symm h]

/- English proof (translation)
Establish `hZ` using `kron_mem (r := r) (s := s) hY`. Use `set Z := Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s) (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)) with hZd`. Establish `hact : omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) = fockAct1 p q r s Y`. Rewrite using `[hZd, ← Matrix.reindex_symm, Equiv.symm_apply_apply]`. Both sides reduce to the same expression.

Use `GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq F.H F.H (fun t => F.Om (T0.expt (t • Z))) (fun t => (fockRep F).π (T1.expt (t • Y))) (fun s t => by simp only [T0.expt_add Z hZ, map_mul]) (fun s t => by simp only [T1.expt_add Y hY, map_mul]) (by simp [T0.expt_zero]) (by rw …` as an intermediate fact. Use `F.der Z hZ ((fockAct1 p q r s Y ^ k) P)` as an intermediate fact. Rewrite `this` using `[hact]`. Simplify `this)` using `only [pow_succ', Module.End.mul_apply]`. Use the proof step `(fun k => by`.

Use `fock_der F Y hY ((fockAct1 p q r s Y ^ k) P)` as an intermediate fact. Simplify `this)` using `only [pow_succ', Module.End.mul_apply]`. Use the proof step `(fun k => rfl) (by simpa using (GlobalTheory.T.analyticOnNhd_om_expt_and_iteratedDeriv_zero_eq p q r s T0 T1 T2 F Z hZ P).1 0 trivial)`. Simplify using `using this`.
-/
theorem fock_analytic (F : FockData T0 T1 T2) {Y : Mat p q} (hY : Y ∈ upq p q) (P : Pol p q r s) :
    AnalyticOnNhd ℝ (fun t : ℝ => (fockRep F).π (T1.expt (t • Y)) (F.ι P)) Set.univ := by
  have hZ := kron_mem (r := r) (s := s) hY
  set Z := Matrix.reindex (lineEquiv p q r s) (lineEquiv p q r s)
    (Matrix.kroneckerMap (· * ·) Y (1 : Mat r s)) with hZd
  have hact : omAct p q r s (Matrix.reindex (lineEquiv p q r s).symm (lineEquiv p q r s).symm Z) =
      fockAct1 p q r s Y := by
    rw [hZd, ← Matrix.reindex_symm, Equiv.symm_apply_apply]
    rfl
  have := GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq F.H F.H (fun t => F.Om (T0.expt (t • Z))) (fun t => (fockRep F).π (T1.expt (t • Y)))
    (fun s t => by simp only [T0.expt_add Z hZ, map_mul])
    (fun s t => by simp only [T1.expt_add Y hY, map_mul])
    (by simp [T0.expt_zero]) (by rw [zero_smul, T1.expt_zero, map_one]) (fun t x => (fockRep F).isom _ x)
    (fun k => F.ι ((fockAct1 p q r s Y ^ k) P)) (fun k => F.ι ((fockAct1 p q r s Y ^ k) P))
    (fun k => by
      have := F.der Z hZ ((fockAct1 p q r s Y ^ k) P)
      rw [hact] at this
      simpa only [pow_succ', Module.End.mul_apply] using this)
    (fun k => by
      have := fock_der F Y hY ((fockAct1 p q r s Y ^ k) P)
      simpa only [pow_succ', Module.End.mul_apply] using this)
    (fun k => rfl) (by simpa using (GlobalTheory.T.analyticOnNhd_om_expt_and_iteratedDeriv_zero_eq p q r s T0 T1 T2 F Z hZ P).1 0 trivial)
  simpa using this

/- English proof (translation)
Introduce `Y hY x`. Use `GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq π₁.H π₂.H (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y))) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (fun s t => by simp only [T.expt_add Y hY, map_mul]) (by simp [T.expt_zero]) (by simp [T.expt_ze …` as an intermediate fact. Simplify using `using this`.
-/
theorem analytic_of_isom (T : GrpData p q) (π₁ π₂ : URep T) (M : GKMod p q)
    (j₁ : M.V →ₗ[ℂ] π₁.H) (j₂ : M.V →ₗ[ℂ] π₂.H)
    (hd₁ : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) (j₁ (M.act Y x)) 0)
    (hd₂ : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) (j₂ (M.act Y x)) 0)
    (han : ∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₁.π (T.expt (t • Y)) (j₁ x)) Set.univ)
    (hiso : ∀ x y, inner ℂ (j₁ x) (j₁ y) = inner ℂ (j₂ x) (j₂ y)) :
    ∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => π₂.π (T.expt (t • Y)) (j₂ x)) Set.univ := by
  intro Y hY x
  have := GlobalTheory.T.analyticOnNhd_orbit_of_derivSeq_norm_eq π₁.H π₂.H (fun t => π₁.π (T.expt (t • Y))) (fun t => π₂.π (T.expt (t • Y)))
    (fun s t => by simp only [T.expt_add Y hY, map_mul])
    (fun s t => by simp only [T.expt_add Y hY, map_mul])
    (by simp [T.expt_zero]) (by simp [T.expt_zero]) (fun t x => π₂.isom _ x)
    (fun k => j₁ ((M.act Y ^ k) x)) (fun k => j₂ ((M.act Y ^ k) x))
    (fun k => by simpa only [pow_succ', Module.End.mul_apply] using hd₁ Y hY ((M.act Y ^ k) x))
    (fun k => by simpa only [pow_succ', Module.End.mul_apply] using hd₂ Y hY ((M.act Y ^ k) x))
    (fun k => by rw [norm_eq_sqrt_re_inner (𝕜 := ℂ), norm_eq_sqrt_re_inner (𝕜 := ℂ), hiso])
    (by simpa using han Y hY x 0 trivial)
  simpa using this

/- English proof (translation)
Apply the tactic sequence `rcases h with rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;> first | trivial | exact a.elim0 | exact b.elim0`.
-/
theorem sameBlock_of_compact (h : r = 0 ∨ s = 0) (a b : Ix r s) : sameBlock a b := by
  rcases h with rfl | rfl <;> rcases a with a | a <;> rcases b with b | b <;>
    first | trivial | exact a.elim0 | exact b.elim0

/- English proof (translation)
Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Establish `: S = ⊥` using `(Submodule.eq_bot_iff _).2 hc`. Rewrite `h` using `[this]`. Simplify using `at h`.
-/
theorem exists_isHW {V : Type*} [AddCommGroup V] [Module ℂ V] {S : Submodule ℂ V}
    (h : Module.finrank ℂ S = 1) : ∃ v ∈ S, v ≠ 0 := by
  by_contra hc
  push Not at hc
  have : S = ⊥ := (Submodule.eq_bot_iff _).2 hc
  rw [this] at h
  simp at h

/- English proof (translation)
Establish `h1` using `(GlobalTheory.T.casimir_central_and_on_highestWeight r s V a ha).2 μ v hv`. Establish `h2` using `(GlobalTheory.T.casimir_central_and_on_highestWeight r s W b hb).2 μ w hw`. Simplify using `only [sameBlock_of_compact h, if_true] at h1 h2`. Simplify using `only [casimir, LinearMap.sum_apply, Module.End.mul_apply] at hc ⊢`. Rewrite using `[h1]`.

Rewrite `hc` using `[h2]`. Rewrite using `[smul_left_injective ℂ hw0 hc]`.
-/
theorem casimir_compact (h : r = 0 ∨ s = 0) {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W]
    [Module ℂ W] (a : Mat r s →ₗ[ℂ] Module.End ℂ V) (b : Mat r s →ₗ[ℂ] Module.End ℂ W) (ha : IsLieAct a)
    (hb : IsLieAct b) {μ : Ix r s → ℚ} {v : V} {w : W} (hv : v ∈ hwSub a μ) (hw : w ∈ hwSub b μ) (hw0 : w ≠ 0)
    {c : ℂ} (hc : casimir b w = c • w) : casimir a v = c • v := by
  have h1 := (GlobalTheory.T.casimir_central_and_on_highestWeight r s V a ha).2 μ v hv
  have h2 := (GlobalTheory.T.casimir_central_and_on_highestWeight r s W b hb).2 μ w hw
  simp only [sameBlock_of_compact h, if_true] at h1 h2
  simp only [casimir, LinearMap.sum_apply, Module.End.mul_apply] at hc ⊢
  rw [h1]
  rw [h2] at hc
  rw [smul_left_injective ℂ hw0 hc]

/- English proof (translation)
Use `set F := X.fock p q r s with hF`. Use `set D := X.ds p q lam with hD`. Take `⟨hsp, hK1, -, -⟩` from `GlobalTheory.T.fockHarmonics_graded_compactStable p q r s (jointHarm p q r s) (Or.inr (Or.inr rfl))`. Establish `hspm : ∀ P, P ∈ Submodule.span ℂ (jointHarm p q r s) → P ∈ jointHarm p q r s` using `fun P hP => by`. Rewrite using `[← hsp]`.

Conclude with `hP`. Prove the components needed by the constructor for the conclusion. Take `⟨P, hP, hP0⟩` from `exists_isHW (((H2 p q r s).2.2.2.2.1 _ _).1 hJ)`. Establish `hn0 : ‖F.ι P‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff]`.

Conclude with `fun h => hP0 (F.ι_inj (by rw [h, map_zero]))`. Establish `hc : ((‖F.ι P‖⁻¹ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast inv_ne_zero hn0`. Establish `hQ` using `Submodule.smul_mem _ ((‖F.ι P‖⁻¹ : ℝ) : ℂ) hP`. Use `⟨((‖F.ι P‖⁻¹ : ℝ) : ℂ) • P, hspm _ hQ.2, ⟨smul_ne_zero hc hP0, hQ.1.1⟩, ⟨smul_ne_zero hc hP0, hQ.1.2⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]`.

Conclude with `inv_mul_cancel₀ hn0`. Introduce `Φ v hΦ hv`. Take `⟨hint, hproj⟩` from `GlobalTheory.T.discreteSeries_integrableCoefficient_projector X DualityBasisChange Q6 p q lam hl _ hge le_rfl v hv`. Take `⟨hproj, -⟩` from `hproj (fockRep F)`. Establish `hm` using `integrable_mcoef D v hint`.

Establish `hd : (D.fdeg : ℂ) ≠ 0` using `by exact_mod_cast D.fdeg_pos.ne'`. Establish `hop : ∀ z, inner ℂ z (opE (X.grp p q) (fockRep F).π (eFun D v) (F.ι Φ)) = (D.fdeg : ℂ) * ∫ g, inner ℂ z ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar`. Introduce `z`. Rewrite using `[inner_opE _ (fockRep F) hint (continuous_eFun D v), ← integral_const_mul]`. Use `congr 1`.

Use function extensionality and compare the values at `g`. Simplify using `only [eFun]`. Expand and normalize the polynomial expressions, which then agree. Use `set x₀ := opE (X.grp p q) (fockRep F).π (eFun D v) (F.ι Φ) with hx₀`. Establish `horth : inner ℂ x₀ (F.ι Φ - x₀) = 0` using `(hproj (F.ι Φ)).2 _ (hproj (F.ι Φ)).1`.

Establish `hin : inner ℂ (F.ι Φ) x₀ = ((‖x₀‖ ^ 2 : ℝ) : ℂ)`. Rewrite `horth` using `[inner_sub_right, sub_eq_zero]`. Rewrite using `[← inner_conj_symm, horth, inner_self_eq_norm_sq_to_K]`. Simplify using the standard rewrite rules. Establish `hZ : ∫ g, inner ℂ (F.ι Φ) ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar = ((‖x₀‖ ^ 2 / D.fdeg : ℝ) : ℂ)`.

Rewrite using `[Complex.ofReal_div, ← hin, hop, mul_div_cancel_left₀ _ hd]`. Establish `hΦ0 : F.ι Φ ≠ 0`. Introduce `h`. Use `hΦ.2.2.2` as an intermediate fact. Rewrite `this` using `[h, norm_zero]`.

Conclude with `zero_ne_one this`. Use `⟨?_, hZ, ?_, fun hc => ?_⟩` and prove the remaining obligations. Use `Integrable.mono' hm.norm ((continuous_const.inner ((fockRep F).cont (F.ι Φ))).mul (continuous_mcoef D v).star).aestronglyMeasurable (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul, norm_star]`. Use `mul_le_of_le_one_left (norm_nonneg _) ((norm_inner_le_norm _ _).trans ?_)` and prove the remaining obligations.

Use `(fockRep F).isom g (F.ι Φ)` as an intermediate fact. Rewrite using `[show ‖F.π (g, 1) (F.ι Φ)‖ = ‖F.ι Φ‖ from this, hΦ.2.2.2, mul_one]`. Express the relevant statement in the definitionally equal form `0 < ‖x₀‖`. Rewrite using `[norm_pos_iff]`. Introduce `h0`.

Use `exists_coeff_ne_zero hn (X.grp p q) (fockRep F) D.U (polMod p q r s) D.HK F.ι D.ι D.ι_inj (fock_der F) D.der hΦ.2.1 hv.1 hΦ0 (Submodule.span ℂ (jointHarm p q r s)) (Submodule.subset_span hΦ.1) hK1 (fun Y hY w hw => ?_) (fun Y hY w hw => (DualityBasisChange p q lam hl _ hge le_rfl …` and prove the remaining obligations. Distinguish the cases in `hw0 : w = 0`. Simplify using `[hw0]`. Use `GlobalTheory.T.inner_expt_jointHarm_real_pos p q r s _ _ _ F Y hY w (hspm w hw) hw0` as an intermediate fact. Conclude with `⟨this.1, this.2.le⟩`.

Use `hop z` as an intermediate fact. Rewrite `this` using `[h0, inner_zero_right]`. Conclude with `(mul_eq_zero.1 this.symm).resolve_left hd`. Take `⟨hr', hc', -⟩` from `DS1 r s lam' hl'`. Take `⟨hr, hcD, -⟩` from `DS1 p q lam hl`.

Take `⟨w, hw, hw0⟩` from `exists_isHW hr'`. Establish `h2 : casimir (fockAct2 p q r s) Φ = _` using `casimir_compact hc (fockAct2 p q r s) _ (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 (X.ds r s lam').HK.lie hΦ.2.2.1.2 hw hw0 (hc' w)`. Establish `h1 : casimir (fockAct1 p q r s) Φ = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • Φ`. Rewrite `h2` using `[GlobalTheory.T.fockModel_dualPair_casimir_apply, sub_eq_iff_eq_add, ← add_smul, hnum]`. Rewrite using `[h2]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hirr : IrrGK D.HK` using `(((Q5 p q hn).1 D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩).2`. Take `⟨e, -, hev, he⟩` from `GlobalTheory.T.exists_injective_intertwiner_of_lowest_type Q7 Q8 p q lam hl hgt (ugk _ (fockRep F) (polMod p q r s) F.ι F.ι_inj (fock_der F)) (ugk _ D.U D.HK D.ι D.ι_inj D.der) Φ v hΦ.2.1 hv.1 h1 (hcD v) hirr`.

Set `e' : D.HK.V →ₗ[ℂ] Pol p q r s` to `e`. Establish `hev' : e' v = Φ` using `hev`. Establish `he' : ∀ Z x, e' (D.HK.act Z x) = fockAct1 p q r s Z (e' x)` using `he`. Set `j : D.HK.V →ₗ[ℂ] (fockRep F).H` to `F.ι ∘ₗ e'`. Establish `hj : ∀ x, j x = F.ι (e' x)` using `fun _ => rfl`.

Establish `hdj : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => (fockRep F).π ((X.grp p q).expt (t • Y)) (j x)) (j (D.HK.act Y x)) 0`. Introduce `Y hY x`. Rewrite using `[hj, hj, he']`. Conclude with `fock_der F Y hY _`. Establish `hiso` using `GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq p q D.HK _ _ j D.ι (GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt p q _ _ D.HK j hdj) (GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt p q _ _ D.HK D.ι D.der) D.ι_inj hirr _ v hv.1 hr (by`.

Rewrite using `[hj, hev', inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hΦ.2.2.2, hv.2])`. Establish `han : ∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ (fun t : ℝ => (fockRep F).π ((X.grp p q).expt (t • Y)) (j x)) Set.univ` using `fun Y hY x => fock_analytic F hY _`. Establish `hco` using `GlobalTheory.T.inner_coeff_eq_of_isometric_analytic_modules p q _ (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hn _).1 (fockRep F) D.U D.HK j D.ι hdj D.der han (analytic_of_isom _ (fockRep F) D.U D.HK j D.ι hdj D.der han hiso) hiso`. Establish `hZ1 : ∫ g, inner ℂ (F.ι Φ) ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar = (((D.fdeg)⁻¹ : ℝ) : ℂ)`. Establish `h3` using `(D.schur (D.ι v) (D.ι v)).2`.

Rewrite `h3` using `[hv.2]`. Rewrite using `[show (D.fdeg)⁻¹ = 1 ^ 2 * 1 ^ 2 / D.fdeg by simp, ← h3, ← integral_complex_ofReal]`. Use `congr 1`. Use function extensionality and compare the values at `g`. Use `hco g v v` as an intermediate fact.

Rewrite `this` using `[hj, hev']`. Rewrite using `[this, mcoef, Complex.star_def, Complex.mul_conj']`. Simplify using the standard rewrite rules. Use `⟨?_, hZ1⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `x₀ = F.ι Φ`.

Establish `hx1 : ‖x₀‖ ^ 2 = 1`. Rewrite `hZ` using `[hZ1]`. Establish `h4 : (D.fdeg)⁻¹ = ‖x₀‖ ^ 2 / D.fdeg` using `by exact_mod_cast hZ`. Use `D.fdeg_pos.ne'` as an intermediate fact. Clear denominators, using `at h4` for the nonvanishing conditions.

Conclude with `h4.symm`. Rewrite using `[eq_comm, ← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, horth, inner_sub_right, hin, hx1, inner_self_eq_norm_sq_to_K, hΦ.2.2.2]`. Simplify using the standard rewrite rules.
-/
theorem main_gen (X : ProvA) (H2 : admH2 X) (DS1 : DiscreteSeriesBlattner X) (DualityBasisChange : DiscreteSeriesPositivity X) (Q5 : admQ5 X)
    (Q6 : CoverHaarIntegration X) (Q7 : admQ7) (Q8 : admQ8) (lam : Ix p q → ℚ) (lam' : Ix r s → ℚ) (hn : 1 ≤ p + q)
    (hl : IsParam lam) (hl' : IsParam lam') (hJ : JointShape p q r s (blattner lam) (blattner lam'))
    (hge : GapGe lam (rangeOfSeventhSum p q)) (hgt : GapGt lam (((p + q : ℕ) : ℝ) ^ 3))
    (hnum : normSq lam' - rhoSq (r + s) = normSq lam - rhoSq (p + q) -
      ((p + q : ℕ) : ℚ) * ((r + s : ℕ) : ℚ) * (((r + s : ℕ) : ℚ) - ((p + q : ℕ) : ℚ)) / 4) :
    ARi X lam lam' := by
  set F := X.fock p q r s with hF
  set D := X.ds p q lam with hD
  obtain ⟨hsp, hK1, -, -⟩ := GlobalTheory.T.fockHarmonics_graded_compactStable p q r s (jointHarm p q r s) (Or.inr (Or.inr rfl))
  have hspm : ∀ P, P ∈ Submodule.span ℂ (jointHarm p q r s) → P ∈ jointHarm p q r s := fun P hP => by
    rw [← hsp]; exact hP
  constructor
  · obtain ⟨P, hP, hP0⟩ := exists_isHW (((H2 p q r s).2.2.2.2.1 _ _).1 hJ)
    have hn0 : ‖F.ι P‖ ≠ 0 := by
      rw [norm_ne_zero_iff]
      exact fun h => hP0 (F.ι_inj (by rw [h, map_zero]))
    have hc : ((‖F.ι P‖⁻¹ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast inv_ne_zero hn0
    have hQ := Submodule.smul_mem _ ((‖F.ι P‖⁻¹ : ℝ) : ℂ) hP
    refine ⟨((‖F.ι P‖⁻¹ : ℝ) : ℂ) • P, hspm _ hQ.2, ⟨smul_ne_zero hc hP0, hQ.1.1⟩,
      ⟨smul_ne_zero hc hP0, hQ.1.2⟩, ?_⟩
    rw [map_smul, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    exact inv_mul_cancel₀ hn0
  intro Φ v hΦ hv
  obtain ⟨hint, hproj⟩ := GlobalTheory.T.discreteSeries_integrableCoefficient_projector X DualityBasisChange Q6 p q lam hl _ hge le_rfl v hv
  obtain ⟨hproj, -⟩ := hproj (fockRep F)
  have hm := integrable_mcoef D v hint
  have hd : (D.fdeg : ℂ) ≠ 0 := by exact_mod_cast D.fdeg_pos.ne'
  have hop : ∀ z, inner ℂ z (opE (X.grp p q) (fockRep F).π (eFun D v) (F.ι Φ)) =
      (D.fdeg : ℂ) * ∫ g, inner ℂ z ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar := by
    intro z
    rw [inner_opE _ (fockRep F) hint (continuous_eFun D v), ← integral_const_mul]
    congr 1
    funext g
    simp only [eFun]
    ring
  set x₀ := opE (X.grp p q) (fockRep F).π (eFun D v) (F.ι Φ) with hx₀
  have horth : inner ℂ x₀ (F.ι Φ - x₀) = 0 := (hproj (F.ι Φ)).2 _ (hproj (F.ι Φ)).1
  have hin : inner ℂ (F.ι Φ) x₀ = ((‖x₀‖ ^ 2 : ℝ) : ℂ) := by
    rw [inner_sub_right, sub_eq_zero] at horth
    rw [← inner_conj_symm, horth, inner_self_eq_norm_sq_to_K]
    simp
  have hZ : ∫ g, inner ℂ (F.ι Φ) ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar =
      ((‖x₀‖ ^ 2 / D.fdeg : ℝ) : ℂ) := by
    rw [Complex.ofReal_div, ← hin, hop, mul_div_cancel_left₀ _ hd]
  have hΦ0 : F.ι Φ ≠ 0 := by
    intro h
    have := hΦ.2.2.2
    rw [h, norm_zero] at this
    exact zero_ne_one this
  refine ⟨?_, hZ, ?_, fun hc => ?_⟩
  · refine Integrable.mono' hm.norm
      ((continuous_const.inner ((fockRep F).cont (F.ι Φ))).mul (continuous_mcoef D v).star).aestronglyMeasurable
      (Filter.Eventually.of_forall fun g => ?_)
    rw [norm_mul, norm_star]
    refine mul_le_of_le_one_left (norm_nonneg _) ((norm_inner_le_norm _ _).trans ?_)
    have := (fockRep F).isom g (F.ι Φ)
    rw [show ‖F.π (g, 1) (F.ι Φ)‖ = ‖F.ι Φ‖ from this, hΦ.2.2.2, mul_one]
  · change 0 < ‖x₀‖
    rw [norm_pos_iff]
    intro h0
    refine exists_coeff_ne_zero hn (X.grp p q) (fockRep F) D.U (polMod p q r s) D.HK F.ι D.ι D.ι_inj
      (fock_der F) D.der hΦ.2.1 hv.1 hΦ0 (Submodule.span ℂ (jointHarm p q r s))
      (Submodule.subset_span hΦ.1) hK1 (fun Y hY w hw => ?_)
      (fun Y hY w hw => (DualityBasisChange p q lam hl _ hge le_rfl).1 Y hY _ ⟨w, hw, rfl⟩) hm (fun z => ?_)
    · by_cases hw0 : w = 0
      · simp [hw0]
      · have := GlobalTheory.T.inner_expt_jointHarm_real_pos p q r s _ _ _ F Y hY w (hspm w hw) hw0
        exact ⟨this.1, this.2.le⟩
    · have := hop z
      rw [h0, inner_zero_right] at this
      exact (mul_eq_zero.1 this.symm).resolve_left hd
  · obtain ⟨hr', hc', -⟩ := DS1 r s lam' hl'
    obtain ⟨hr, hcD, -⟩ := DS1 p q lam hl
    obtain ⟨w, hw, hw0⟩ := exists_isHW hr'
    have h2 : casimir (fockAct2 p q r s) Φ = _ := casimir_compact hc (fockAct2 p q r s) _
      (GlobalTheory.T.fockOperators_lie_representation_commute p q r s).2.2.1 (X.ds r s lam').HK.lie hΦ.2.2.1.2 hw hw0 (hc' w)
    have h1 : casimir (fockAct1 p q r s) Φ = (((normSq lam - rhoSq (p + q) : ℚ)) : ℂ) • Φ := by
      rw [GlobalTheory.T.fockModel_dualPair_casimir_apply, sub_eq_iff_eq_add, ← add_smul, hnum] at h2
      rw [h2]
      congr 1
      push_cast
      ring
    have hirr : IrrGK D.HK :=
      (((Q5 p q hn).1 D.U ⟨D.nontriv, D.irred⟩).2.2 D.HK D.ι ⟨D.ι_inj, D.ι_range, D.der⟩).2
    obtain ⟨e, -, hev, he⟩ := GlobalTheory.T.exists_injective_intertwiner_of_lowest_type Q7 Q8 p q lam hl hgt
      (ugk _ (fockRep F) (polMod p q r s) F.ι F.ι_inj (fock_der F)) (ugk _ D.U D.HK D.ι D.ι_inj D.der)
      Φ v hΦ.2.1 hv.1 h1 (hcD v) hirr
    let e' : D.HK.V →ₗ[ℂ] Pol p q r s := e
    have hev' : e' v = Φ := hev
    have he' : ∀ Z x, e' (D.HK.act Z x) = fockAct1 p q r s Z (e' x) := he
    let j : D.HK.V →ₗ[ℂ] (fockRep F).H := F.ι ∘ₗ e'
    have hj : ∀ x, j x = F.ι (e' x) := fun _ => rfl
    have hdj : ∀ Y ∈ upq p q, ∀ x, HasDerivAt (fun t : ℝ => (fockRep F).π ((X.grp p q).expt (t • Y)) (j x))
        (j (D.HK.act Y x)) 0 := by
      intro Y hY x
      rw [hj, hj, he']
      exact fock_der F Y hY _
    have hiso := GlobalTheory.T.inner_eq_of_irrGK_of_inner_hw_eq p q D.HK _ _ j D.ι (GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt p q _ _ D.HK j hdj)
      (GlobalTheory.T.inner_act_eq_inner_act_adjZ_of_hasDerivAt p q _ _ D.HK D.ι D.der) D.ι_inj hirr _ v hv.1 hr (by
        rw [hj, hev', inner_self_eq_norm_sq_to_K, inner_self_eq_norm_sq_to_K, hΦ.2.2.2, hv.2])
    have han : ∀ Y ∈ upq p q, ∀ x, AnalyticOnNhd ℝ
        (fun t : ℝ => (fockRep F).π ((X.grp p q).expt (t • Y)) (j x)) Set.univ :=
      fun Y hY x => fock_analytic F hY _
    have hco := GlobalTheory.T.inner_coeff_eq_of_isometric_analytic_modules p q _ (GlobalTheory.T.coverUpq_closure_exp_top_and_cartan p q hn _).1 (fockRep F) D.U D.HK j D.ι hdj D.der han
      (analytic_of_isom _ (fockRep F) D.U D.HK j D.ι hdj D.der han hiso) hiso
    have hZ1 : ∫ g, inner ℂ (F.ι Φ) ((fockRep F).π g (F.ι Φ)) * star (mcoef D v g) ∂(X.grp p q).haar =
        (((D.fdeg)⁻¹ : ℝ) : ℂ) := by
      have h3 := (D.schur (D.ι v) (D.ι v)).2
      rw [hv.2] at h3
      rw [show (D.fdeg)⁻¹ = 1 ^ 2 * 1 ^ 2 / D.fdeg by simp, ← h3, ← integral_complex_ofReal]
      congr 1
      funext g
      have := hco g v v
      rw [hj, hev'] at this
      rw [this, mcoef, Complex.star_def, Complex.mul_conj']
      simp
    refine ⟨?_, hZ1⟩
    change x₀ = F.ι Φ
    have hx1 : ‖x₀‖ ^ 2 = 1 := by
      rw [hZ1] at hZ
      have h4 : (D.fdeg)⁻¹ = ‖x₀‖ ^ 2 / D.fdeg := by exact_mod_cast hZ
      have := D.fdeg_pos.ne'
      field_simp at h4
      exact h4.symm
    rw [eq_comm, ← sub_eq_zero, ← inner_self_eq_zero (𝕜 := ℂ), inner_sub_left, horth, inner_sub_right, hin,
      hx1, inner_self_eq_norm_sq_to_K, hΦ.2.2.2]
    simp

/- English proof (translation)
Introduce `a b hab`. Use `lt_of_le_of_lt ?_ (h a b hab)` and prove the remaining obligations. Rewrite using `[hn]`. Use `gcongr`. Use linear arithmetic over natural numbers and integers.
-/
theorem gapGt_mono {lam : Ix p q → ℚ} {n t : ℕ} (hn : p + q = n) (h : GapGt lam (((n + t : ℕ) : ℝ) ^ 3)) :
    GapGt lam (((p + q : ℕ) : ℝ) ^ 3) := by
  intro a b hab
  refine lt_of_le_of_lt ?_ (h a b hab)
  rw [hn]
  gcongr
  omega

/- English proof (translation)
Introduce `X _ H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `t al be ga de ⟨hA, hG⟩`. Take `⟨⟨h1, h2, -⟩, h3, -⟩` from `GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA`. Establish `h4` using `(GlobalTheory.CasimirNumber.casimir_number_identity t al be ga de hA).1`.

Establish `e1 : al.length + be.length + (ga.length + de.length) = al.length + be.length + ga.length + de.length` using `by omega`. Establish `e2 : al.length + de.length + t + (ga.length + be.length) = al.length + be.length + ga.length + de.length + t` using `by omega`. Use `main_gen X H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8 _ _ (by have := hA.2.1; omega) h1 h2 h3 ?_ (gapGt_mono e1 hG.1) ?_` and prove the remaining obligations. Unfold `rangeOfSeventhSum`. Rewrite using `[e1]`.

Conclude with `hG.2.2`. Rewrite using `[e1, e2, h4]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `t al be ga de ⟨hA, hG⟩`.

Take `⟨⟨h1, -, h2⟩, -, h3⟩` from `GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA`. Take `⟨h4, h5⟩` from `GlobalTheory.CasimirNumber.casimir_number_identity t al be ga de hA`. Establish `e1 : al.length + be.length + (ga.length + de.length) = al.length + be.length + ga.length + de.length` using `by omega`. Establish `e2 : al.length + de.length + (ga.length + be.length + t) = al.length + be.length + ga.length + de.length + t` using `by omega`. Use `main_gen X H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8 _ _ (by have := hA.2.1; omega) h1 h2 h3 ?_ (gapGt_mono e1 hG.1) ?_` and prove the remaining obligations.

Unfold `rangeOfSeventhSum`. Rewrite using `[e1]`. Conclude with `hG.2.2`. Rewrite using `[e1, e2, h5, h4]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem doubling_pos : ∀ X : ProvA, admH1 X → admH2 X → DiscreteSeriesBlattner X → DiscreteSeriesPositivity X → admQ5 X → CoverHaarIntegration X → admQ7 →
    admQ8 → ArchimedeanRallisFirst X := by
  intro X _ H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8
  constructor
  · rintro t al be ga de ⟨hA, hG⟩
    obtain ⟨⟨h1, h2, -⟩, h3, -⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA
    have h4 := (GlobalTheory.CasimirNumber.casimir_number_identity t al be ga de hA).1
    have e1 : al.length + be.length + (ga.length + de.length) =
      al.length + be.length + ga.length + de.length := by omega
    have e2 : al.length + de.length + t + (ga.length + be.length) =
      al.length + be.length + ga.length + de.length + t := by omega
    refine main_gen X H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8 _ _ (by have := hA.2.1; omega) h1 h2 h3 ?_
      (gapGt_mono e1 hG.1) ?_
    · unfold rangeOfSeventhSum
      rw [e1]
      exact hG.2.2
    · rw [e1, e2, h4]
      push_cast
      ring
  · rintro t al be ga de ⟨hA, hG⟩
    obtain ⟨⟨h1, -, h2⟩, -, h3⟩ := GlobalTheory.T.lowestKTypes_jointHarmonicShape t al be ga de hA
    obtain ⟨h4, h5⟩ := GlobalTheory.CasimirNumber.casimir_number_identity t al be ga de hA
    have e1 : al.length + be.length + (ga.length + de.length) =
      al.length + be.length + ga.length + de.length := by omega
    have e2 : al.length + de.length + (ga.length + be.length + t) =
      al.length + be.length + ga.length + de.length + t := by omega
    refine main_gen X H2 DS1 DualityBasisChange Q5 Q6 Q7 Q8 _ _ (by have := hA.2.1; omega) h1 h2 h3 ?_
      (gapGt_mono e1 hG.1) ?_
    · unfold rangeOfSeventhSum
      rw [e1]
      exact hG.2.2
    · rw [e1, e2, h5, h4]
      push_cast
      ring

end GlobalTheory.DoublingPos

end
