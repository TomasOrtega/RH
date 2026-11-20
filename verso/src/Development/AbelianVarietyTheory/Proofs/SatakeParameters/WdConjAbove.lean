import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.ThetaMod
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Formalism.SharpRestriction.LevelLetterCocycles.SumRepresentations
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PadicHodgePropertiesConjInvariant
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CharpolyWeilDelignePotSemistableEnlargeCoefficie
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsPotentiallySemistableCoefficientFieldEnlarge
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.WeilDeligneParamAboveLIndependentLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsContinuousLadicGalRepModelFiniteExtHost
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsFinitePlaceOverLOfHostEmbeddingQbar
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsCompletionEmbeddingInducingHostEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamGaloisSideIffDeRhamAtLocalEmbedding
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 Formalism.L2.Host Formalism.L2.NT NumberField IsDedekindDomain Polynomial GlobalTheory.HeightCounting GlobalTheory.RowTie GlobalTheory.SplitRead GlobalTheory.NPin
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section
namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc GlobalTheory.Pst

section Local

variable {l : ℕ} [Fact l.Prime] (P : LocPrime l) (ι : Om l ≃+* ℂ)
  {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
  {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)}
  {O : Type} [CommRing O] [Algebra ℤ_[l] O] [TopologicalSpace O]
  (B : LocBridge l E Ω (Dec (F := E) A) O) (h : IsPlaceOver A w) (hj : Induces B)

/- English proof (translation)
Use `haveI := h₁.finite`. Use `haveI := h₂.finite`. Set `f : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1)` to `(e : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]`. Establish `hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v)` using `he`. Set `π : Fin 1 → (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1)` to `fun _ => (e.symm : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]`.

Establish `hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v)`. Introduce `j g v`. Apply `e.injective` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `e (e.symm (ρ₂ g v)) = e (ρ₁ g (e.symm v))`. Rewrite using `[he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]`.

Establish `hsum : ∀ v, ∑ j, (fun _ : Fin 1 => (1 : ↥L.1)) j • f (π j v) = v`. Introduce `v`. Express the relevant statement in the definitionally equal form `∑ _j : Fin 1, (1 : ↥L.1) • e (e.symm v) = v`. Simplify using the standard rewrite rules. Use `BridgeParam.wdPst_eq_of_map P ι B B h hj hj h₁ h₂ rfl (RingHom.id _) (fun _ => rfl) (EnlargeCoeff.dQ P hf) (fun a x => Subtype.ext (EnlargeCoeff.tensQ_smul P (RingHom.id _) (fun a v => e.map_smul a v) a x.1)) (EnlargeCoeff.dQ_mulD P hf) (EnlargeCoeff.dQ_weilD P B h hf) 1 one_ne_z …` and prove the remaining obligations.

Establish `e1 : EnlargeCoeff.dQ P hf (monD P ρ₁ x) = monD P ρ₂ (EnlargeCoeff.dQ P hf x)` using `Subtype.ext (EnlargeCoeff.tensQ_onB P _ _ x.1)`. Conclude with `e1.trans (Subtype.ext (one_smul ↥L.1 (monD P ρ₂ (EnlargeCoeff.dQ P hf x)).1).symm)`. Conclude with `BridgeParam.mem_span_dQ P ι hf (fun _ => 1) π hπ hsum x`.
-/
theorem wdPst_equiv {L : FinExt l} {m : ℕ} {ρ₁ ρ₂ : Representation ↥L.1 ↥(GK B.Kw) (Fin m → ↥L.1)}
    (e : (Fin m → ↥L.1) ≃ₗ[↥L.1] (Fin m → ↥L.1)) (he : ∀ g x, e (ρ₁ g x) = ρ₂ g (e x))
    (h₁ : IsPst P ρ₁) (h₂ : IsPst P ρ₂) :
    wdPst P ι B h hj ρ₁ = wdPst P ι B h hj ρ₂ := by
  haveI := h₁.finite
  haveI := h₂.finite
  let f : (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1) := (e : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]
  have hf : ∀ g v, f (ρ₁ g v) = ρ₂ g (f v) := he
  let π : Fin 1 → (Fin m → ↥L.1) →ₗ[ℚ_[l]] (Fin m → ↥L.1) :=
    fun _ => (e.symm : (Fin m → ↥L.1) →ₗ[↥L.1] (Fin m → ↥L.1)).restrictScalars ℚ_[l]
  have hπ : ∀ j g v, π j (ρ₂ g v) = ρ₁ g (π j v) := by
    intro j g v
    apply e.injective
    change e (e.symm (ρ₂ g v)) = e (ρ₁ g (e.symm v))
    rw [he, LinearEquiv.apply_symm_apply, LinearEquiv.apply_symm_apply]
  have hsum : ∀ v, ∑ j, (fun _ : Fin 1 => (1 : ↥L.1)) j • f (π j v) = v := by
    intro v
    change ∑ _j : Fin 1, (1 : ↥L.1) • e (e.symm v) = v
    simp
  refine BridgeParam.wdPst_eq_of_map P ι B B h hj hj h₁ h₂ rfl (RingHom.id _) (fun _ => rfl)
    (EnlargeCoeff.dQ P hf)
    (fun a x => Subtype.ext (EnlargeCoeff.tensQ_smul P (RingHom.id _) (fun a v => e.map_smul a v) a x.1))
    (EnlargeCoeff.dQ_mulD P hf) (EnlargeCoeff.dQ_weilD P B h hf) 1 one_ne_zero (fun x => ?_) fun x => ?_
  · have e1 : EnlargeCoeff.dQ P hf (monD P ρ₁ x) = monD P ρ₂ (EnlargeCoeff.dQ P hf x) :=
      Subtype.ext (EnlargeCoeff.tensQ_onB P _ _ x.1)
    exact e1.trans (Subtype.ext (one_smul ↥L.1 (monD P ρ₂ (EnlargeCoeff.dQ P hf x)).1).symm)
  · exact BridgeParam.mem_span_dQ P ι hf (fun _ => 1) π hπ hsum x

/- English proof (translation)
Take `⟨L₁, r₁, hm₁, hV₁, e₁⟩` from `wdAt_of_isPstAt ι B h hj hr`. Take `⟨L₃, r₃, hm₃, hV₃, e₃⟩` from `wdAt_of_isPstAt ι B h hj hr'`. Establish `hA : L₁.1 ≤ (supExt L₁ L₃).1` using `le_sup_left`. Establish `hB : L₃.1 ≤ (supExt L₁ L₃).1` using `le_sup_right`. Establish `hm₁' : IsModel B r (supExt L₁ L₃) (mapRep (IntermediateField.inclusion hA).toRingHom r₁)` using `⟨hm₁.1.trans hA, by rw [← hm₁.2]; ext g i j; rfl⟩`.

Take `⟨L₂, hL, r₂, hm₂, e, he⟩` from `GlobalTheory.ConjLocal.exists_conj_model M hc hm₁'`. Establish `hC : L₃.1 ≤ L₂.1` using `hB.trans hL`. Establish `hr₃ : mapRep (IntermediateField.inclusion hC).toRingHom r₃ = r₂` using `IsModel.unique B r' ⟨hm₃.1.trans hC, by rw [← hm₃.2]; ext g i j; rfl⟩ hm₂`. Establish `p₁` using `GlobalTheory.PstExt.isPst_enlarge P B hA r₁ hV₁`. Establish `p₁'` using `GlobalTheory.PstExt.isPst_enlarge P B hL _ p₁`.

Establish `p₃` using `GlobalTheory.PstExt.isPst_enlarge P B hC r₃ hV₃`. Rewrite using `[e₁, e₃, BridgeParam.wdPst_enlarge P ι B h hj hC r₃ hV₃, hr₃, BridgeParam.wdPst_enlarge P ι B h hj hA r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj hL _ p₁]`. Rewrite `p₃` using `[hr₃]`. Conclude with `(wdPst_equiv P ι B h hj e he p₁' p₃).symm`.
-/
theorem wdAt_conj {a : ℕ} (r r' : ↥(Dec (F := E) A) →* GL (Fin a) (Om l)) (M : GL (Fin a) (Om l))
    (hc : ∀ g, r' g = M * r g * M⁻¹) (hr : IsPstAt P B r) (hr' : IsPstAt P B r') :
    wdAt P ι B h hj r' = wdAt P ι B h hj r := by
  obtain ⟨L₁, r₁, hm₁, hV₁, e₁⟩ := wdAt_of_isPstAt ι B h hj hr
  obtain ⟨L₃, r₃, hm₃, hV₃, e₃⟩ := wdAt_of_isPstAt ι B h hj hr'
  have hA : L₁.1 ≤ (supExt L₁ L₃).1 := le_sup_left
  have hB : L₃.1 ≤ (supExt L₁ L₃).1 := le_sup_right
  have hm₁' : IsModel B r (supExt L₁ L₃) (mapRep (IntermediateField.inclusion hA).toRingHom r₁) :=
    ⟨hm₁.1.trans hA, by rw [← hm₁.2]; ext g i j; rfl⟩
  obtain ⟨L₂, hL, r₂, hm₂, e, he⟩ := GlobalTheory.ConjLocal.exists_conj_model M hc hm₁'
  have hC : L₃.1 ≤ L₂.1 := hB.trans hL
  have hr₃ : mapRep (IntermediateField.inclusion hC).toRingHom r₃ = r₂ :=
    IsModel.unique B r' ⟨hm₃.1.trans hC, by rw [← hm₃.2]; ext g i j; rfl⟩ hm₂
  have p₁ := GlobalTheory.PstExt.isPst_enlarge P B hA r₁ hV₁
  have p₁' := GlobalTheory.PstExt.isPst_enlarge P B hL _ p₁
  have p₃ := GlobalTheory.PstExt.isPst_enlarge P B hC r₃ hV₃
  rw [e₁, e₃, BridgeParam.wdPst_enlarge P ι B h hj hC r₃ hV₃, hr₃,
    BridgeParam.wdPst_enlarge P ι B h hj hA r₁ hV₁, BridgeParam.wdPst_enlarge P ι B h hj hL _ p₁]
  rw [hr₃] at p₃
  exact (wdPst_equiv P ι B h hj e he p₁' p₃).symm

end Local
end GlobalTheory.ConjGal

namespace GlobalTheory.ConjGal
open Formalism.BasicNotions.Loc

section W
variable (D : D7) (T : WDTie D.nd D.naut) (W : WDSide D T) (l : ℕ) [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

/- English proof (translation)
Establish `e : (fun g => ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) = fun g => ((Pm⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * (Pm : Matrix (Fin a) (Fin a) (Qbar l))`. Use function extensionality and compare the values at `g`. Rewrite using `[hc]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `(continuous_const.matrix_mul hρ).matrix_mul continuous_const`.
-/
theorem cont_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)))) :
    Continuous (fun g => ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) := by
  have e : (fun g => ((ρ' g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))) = fun g =>
      ((Pm⁻¹ : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) *
        ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l)) * (Pm : Matrix (Fin a) (Fin a) (Qbar l)) := by
    funext g
    rw [hc]
    rfl
  rw [e]
  exact (continuous_const.matrix_mul hρ).matrix_mul continuous_const

/- English proof (translation)
Establish `hρ'` using `cont_conj D l ρ ρ' Pm hc hρ`. Take `⟨LL, Bw, hj, -⟩` from `W.above l ι ρ w hw`. Rewrite using `[GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ' hρ', GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ hρ]`. Prove the components needed by the constructor for the conclusion. Use `(GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm fun g => ?_).1` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `ρ g = Pm * ρ' g * Pm⁻¹`. Rewrite using `[hc]`. Use `group`. Use `(GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm⁻¹ fun g => ?_).1` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹`.

Rewrite using `[hc, inv_inv]`.
-/
theorem dR_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) :
    W.IsdRW l ι ρ' w ↔ W.IsdRW l ι ρ w := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  rw [GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ' hρ',
    GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ Bw hj a ρ hρ]
  constructor
  · refine (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm fun g => ?_).1
    change ρ g = Pm * ρ' g * Pm⁻¹
    rw [hc]
    group
  · refine (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a _ _ Pm⁻¹ fun g => ?_).1
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv]

/- English proof (translation)
Apply `(T.e w).injective` to reduce the goal to its premises. Rewrite using `[W.away l ι ρ' w hw, W.away l ι ρ w hw]`. Conclude with `(GlobalTheory.WeilDeligne.wdOf_eq_of_conj (r := ρ) (ι := ι) hw Pm⁻¹ fun g => by rw [hc]; group).symm`.
-/
theorem wd_conj_away {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) (w : PlE D.host) (hw : w ∉ placesOver D.host.E l) :
    W.wdOf l ι ρ' w = W.wdOf l ι ρ w := by
  apply (T.e w).injective
  rw [W.away l ι ρ' w hw, W.away l ι ρ w hw]
  exact (GlobalTheory.WeilDeligne.wdOf_eq_of_conj (r := ρ) (ι := ι) hw Pm⁻¹ fun g => by rw [hc]; group).symm

/- English proof (translation)
The claim follows from `hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val) ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ B hj m r hr).1 hd)`.
-/
theorem pst_of_dR (hB : GlobalTheory.Published.DeRhamPotSemistable) {m : ℕ} (r : G D.host.E D.nd.Om →* GL (Fin m) (Qbar l))
    (hr : Continuous (fun g => ((r g : GL (Fin m) (Qbar l)) : Matrix (Fin m) (Fin m) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (hd : W.IsdRW l ι r w) {LL : FinExt l}
    (B : LocBridge l D.host.E D.nd.Om (Dec (F := D.host.E) (D.nd.plOm.1 w)) ↥(OL LL)) (hj : GlobalTheory.Pst.Induces B) :
    GlobalTheory.Pst.IsPstAt (D.loc l) B (GlobalTheory.Pst.resDec D.nd.plOm.1 r w) :=
  hB.isPstAt (D.locT l) B _ (hr.comp continuous_subtype_val)
    ((GlobalTheory.DeRhamRead.isdRW_iff_isdRAt D T W l ι w hw _ B hj m r hr).1 hd)

/- English proof (translation)
Establish `hρ'` using `cont_conj D l ρ ρ' Pm hc hρ`. Establish `d'` using `(dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d`. Take `⟨p_power_smul_sub_sum, B1, j1, E1⟩` from `W.above l ι ρ w hw`. Take `⟨logJacobianTwoPoints, B2, j2, E2⟩` from `W.above l ι ρ' w hw`. Establish `tie : Nonempty (LocTied l (D.loc l) (D.locA l))` using `⟨D.locT l⟩`.

Apply `(T.e w).injective` to reduce the goal to its premises. Rewrite using `[E1, E2]`. Establish `p22` using `pst_of_dR D T W l ι hB ρ' hρ' w hw d' B2 j2`. Establish `p21` using `pst_of_dR D T W l ι hB ρ' hρ' w hw d' B1 j1`. Establish `p11` using `pst_of_dR D T W l ι hB ρ hρ w hw d B1 j1`.

Rewrite using `[GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _ B2 B1 (D.nd.plOm.2 w) j2 j1 a _ (hρ'.comp continuous_subtype_val) p22 p21]`. Conclude with `wdAt_conj (D.loc l) ι B1 (D.nd.plOm.2 w) j1 _ _ Pm⁻¹ (fun g => by`. Express the relevant statement in the definitionally equal form `ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹`. Rewrite using `[hc, inv_inv]) p11 p21`.
-/
theorem wd_conj_above (hB : GlobalTheory.Published.DeRhamPotSemistable) {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l))
    (Pm : GL (Fin a) (Qbar l)) (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (w : PlE D.host) (hw : w ∈ placesOver D.host.E l) (d : W.IsdRW l ι ρ w) :
    W.wdOf l ι ρ' w = W.wdOf l ι ρ w := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  have d' := (dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d
  obtain ⟨p_power_smul_sub_sum, B1, j1, E1⟩ := W.above l ι ρ w hw
  obtain ⟨logJacobianTwoPoints, B2, j2, E2⟩ := W.above l ι ρ' w hw
  have tie : Nonempty (LocTied l (D.loc l) (D.locA l)) := ⟨D.locT l⟩
  apply (T.e w).injective
  rw [E1, E2]
  have p22 := pst_of_dR D T W l ι hB ρ' hρ' w hw d' B2 j2
  have p21 := pst_of_dR D T W l ι hB ρ' hρ' w hw d' B1 j1
  have p11 := pst_of_dR D T W l ι hB ρ hρ w hw d B1 j1
  rw [GlobalTheory.Pst.BridgeParam.wdAt_indep_bridge l (D.loc l) (D.locA l) tie ι D.host.E D.nd.Om (D.nd.plOm.1 w) w _ _
    B2 B1 (D.nd.plOm.2 w) j2 j1 a _ (hρ'.comp continuous_subtype_val) p22 p21]
  exact wdAt_conj (D.loc l) ι B1 (D.nd.plOm.2 w) j1 _ _ Pm⁻¹ (fun g => by
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv]) p11 p21

/- English proof (translation)
Establish `hρ'` using `cont_conj D l ρ ρ' Pm hc hρ`. Take `⟨w, hw, hτw⟩` from `GlobalTheory.PlaceOfEmb.exists_place_of_emb D l τ`. Establish `d₁` using `hτ w hτw`. Establish `d₂` using `(dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d₁`. Take `⟨LL, Bw, hj, -⟩` from `W.above l ι ρ w hw`.

Take `⟨L₁, hL₁, ρ₁, c₁, e₁⟩` from `GlobalTheory.CompactRepField.exists_continuous_model D l a ρ hρ Bw.LL`. Take `⟨L₂, hL₂, ρ₂, c₂, e₂⟩` from `GlobalTheory.CompactRepField.exists_continuous_model D l a ρ' hρ' Bw.LL`. Take `⟨τ₁, hτ₁⟩` from `GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₁ hL₁`. Take `⟨τ₂, hτ₂⟩` from `GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₂ hL₂`. Take `⟨-, H⟩` from `W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)`.

Take `⟨-, dd₁, -, J₁⟩` from `H L₁ hL₁ a ρ₁ c₁`. Take `⟨-, dd₂, -, J₂⟩` from `H L₂ hL₂ a ρ₂ c₂`. Rewrite `dd₁`, `J₁` using `[e₁]`. Rewrite `dd₂`, `J₂` using `[e₂]`. Establish `hm₁ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) L₁ (ρ₁.comp (Dec (F` using `D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₁, by rw [← e₁]; rfl⟩`.

Establish `hm₂ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) L₂ (ρ₂.comp (Dec (F` using `D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₂, by rw [← e₂]; rfl⟩`. Establish `k₁` using `(J₁ τ τ₁ hτ₁).2 (dd₁.1 d₁)`. Establish `k₂` using `(J₂ τ τ₂ hτ₂).2 (dd₂.1 d₂)`. Establish `J : GlobalTheory.Pst.IsJumpsAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) τ (W.jumpsW l ι ρ τ)` using `⟨L₁, _, hm₁, dd₁.1 d₁, τ₁, hτ₁, k₁⟩`. Establish `J'` using `(GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) Pm⁻¹ (fun g => by`.

Express the relevant statement in the definitionally equal form `ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹`. Rewrite using `[hc, inv_inv])).2.2.2 τ _ J`. Use extensionality with `c`. Establish `k₃` using `GlobalTheory.Pst.IsJumpsAt.count_eq (D.loc l) hm₂ hτ₂ J' c`. Establish `k₄` using `k₂ c`.

Conclude with `k₄.trans k₃.symm` after adjusting the coercions.
-/
theorem jumps_conj {a : ℕ} (ρ ρ' : G D.host.E D.nd.Om →* GL (Fin a) (Qbar l)) (Pm : GL (Fin a) (Qbar l))
    (hc : ∀ g, ρ' g = Pm⁻¹ * ρ g * Pm)
    (hρ : Continuous (fun g => ((ρ g : GL (Fin a) (Qbar l)) : Matrix (Fin a) (Fin a) (Qbar l))))
    (τ : D.host.E →+* Qbar l)
    (hτ : ∀ w : PlE D.host, (∀ x : 𝓞 D.host.E, ‖τ (x : D.host.E)‖ < 1 ↔ x ∈ w.asIdeal) → W.IsdRW l ι ρ w) :
    W.jumpsW l ι ρ' τ = W.jumpsW l ι ρ τ := by
  have hρ' := cont_conj D l ρ ρ' Pm hc hρ
  obtain ⟨w, hw, hτw⟩ := GlobalTheory.PlaceOfEmb.exists_place_of_emb D l τ
  have d₁ := hτ w hτw
  have d₂ := (dR_conj D T W l ι ρ ρ' Pm hc hρ w hw).2 d₁
  obtain ⟨LL, Bw, hj, -⟩ := W.above l ι ρ w hw
  obtain ⟨L₁, hL₁, ρ₁, c₁, e₁⟩ := GlobalTheory.CompactRepField.exists_continuous_model D l a ρ hρ Bw.LL
  obtain ⟨L₂, hL₂, ρ₂, c₂, e₂⟩ := GlobalTheory.CompactRepField.exists_continuous_model D l a ρ' hρ' Bw.LL
  obtain ⟨τ₁, hτ₁⟩ := GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₁ hL₁
  obtain ⟨τ₂, hτ₂⟩ := GlobalTheory.EmbExt.main D l w _ Bw hj τ hτw L₂ hL₂
  obtain ⟨-, H⟩ := W.loc l ι w hw _ Bw hj ((algebraMap ↥Bw.LL.1 (Om l)).comp Bw.toLL) (fun _ => rfl)
  obtain ⟨-, dd₁, -, J₁⟩ := H L₁ hL₁ a ρ₁ c₁
  obtain ⟨-, dd₂, -, J₂⟩ := H L₂ hL₂ a ρ₂ c₂
  rw [e₁] at dd₁ J₁
  rw [e₂] at dd₂ J₂
  have hm₁ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) L₁
      (ρ₁.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₁, by rw [← e₁]; rfl⟩
  have hm₂ : GlobalTheory.Pst.IsModel Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) L₂
      (ρ₂.comp (Dec (F := D.host.E) (D.nd.plOm.1 w)).subtype) := ⟨hL₂, by rw [← e₂]; rfl⟩
  have k₁ := (J₁ τ τ₁ hτ₁).2 (dd₁.1 d₁)
  have k₂ := (J₂ τ τ₂ hτ₂).2 (dd₂.1 d₂)
  have J : GlobalTheory.Pst.IsJumpsAt (D.loc l) Bw (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w) τ (W.jumpsW l ι ρ τ) :=
    ⟨L₁, _, hm₁, dd₁.1 d₁, τ₁, hτ₁, k₁⟩
  have J' := (GlobalTheory.ConjLocal.local_conj l (D.loc l) D.host.E D.nd.Om _ _ Bw a (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ w)
    (GlobalTheory.Pst.resDec D.nd.plOm.1 ρ' w) Pm⁻¹ (fun g => by
    change ρ' g = Pm⁻¹ * ρ g * Pm⁻¹⁻¹
    rw [hc, inv_inv])).2.2.2 τ _ J
  ext c
  have k₃ := GlobalTheory.Pst.IsJumpsAt.count_eq (D.loc l) hm₂ hτ₂ J' c
  have k₄ := k₂ c
  exact_mod_cast k₄.trans k₃.symm

end W

/- English proof (translation)
Introduce `hB hL D P i a ρ ρ' hρ Pm hc`. Use `⟨fun w hw => ?_, fun w h₁ => ?_, fun τ hτ => ?_⟩` and prove the remaining obligations. Rewrite using `[(P.wdOf i _ ρ' w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1]`. Conclude with `dR_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ w hw`. Rewrite using `[(P.wdOf i _ ρ' w).1, (P.wdOf i _ ρ w).1]`.

Distinguish the cases in `hw : w ∈ placesOver D.host.E (D.nd.l i)`. Establish `d₁` using `(P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))`. Conclude with `wd_conj_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' Pm hc hρ w hw d₁`. Conclude with `wd_conj_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc w hw`. Take `⟨w₀, -, -⟩` from `GlobalTheory.PlaceOfEmb.exists_place_of_emb D (D.nd.l i) τ`.

Rewrite using `[(P.wdOf i _ ρ' w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ]`. Conclude with `jumps_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ τ fun w hw => (P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw)`.
-/
theorem main : GlobalTheory.Published.DeRhamPotSemistable → ∀ (hL : GlobalTheory.Published.LocalLanglandsGL) (D : D7) (P : Pin hL D), ∀ i : D.nd.Loc, (∀ a (ρ ρ' : Formalism.ConjugateSelfDual.G D.host.E D.nd.Om →* GL (Fin a) (Qbar (D.nd.l i))), Formalism.MainNotions.SumRepresentations.At.ContQ D.nd i ρ → ∀ Pm : GL (Fin a) (Qbar (D.nd.l i)), (∀ g, ρ' g = Pm⁻¹ * ρ g * Pm) → (∀ w ∈ placesOver D.host.E (D.nd.l i), D.naut.IsdRW i ρ' w ↔ D.naut.IsdRW i ρ w) ∧ (∀ w, Formalism.MainNotions.SumRepresentations.At.WDok D.nd D.naut i ρ w → D.naut.wdOf i ρ' w = D.naut.wdOf i ρ w) ∧ (∀ τ, (∀ w, InducesW D.nd i τ w → D.naut.IsdRW i ρ w) → D.naut.jumpsW i ρ' τ = D.naut.jumpsW i ρ τ)) := by
  intro hB hL D P i a ρ ρ' hρ Pm hc
  refine ⟨fun w hw => ?_, fun w h₁ => ?_, fun τ hτ => ?_⟩
  · rw [(P.wdOf i _ ρ' w).2.2.2.1, (P.wdOf i _ ρ w).2.2.2.1]
    exact dR_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ w hw
  · rw [(P.wdOf i _ ρ' w).1, (P.wdOf i _ ρ w).1]
    by_cases hw : w ∈ placesOver D.host.E (D.nd.l i)
    · have d₁ := (P.wdOf i _ ρ w).2.2.2.1.1 (h₁.resolve_left (not_not.2 hw))
      exact wd_conj_above D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) hB ρ ρ' Pm hc hρ w hw d₁
    · exact wd_conj_away D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc w hw
  · obtain ⟨w₀, -, -⟩ := GlobalTheory.PlaceOfEmb.exists_place_of_emb D (D.nd.l i) τ
    rw [(P.wdOf i _ ρ' w₀).2.2.2.2 τ, (P.wdOf i _ ρ w₀).2.2.2.2 τ]
    exact jumps_conj D P.T P.wd (D.nd.l i) (D.naut.iotaQC i) ρ ρ' Pm hc hρ τ fun w hw =>
      (P.wdOf i _ ρ w).2.2.2.1.1 (hτ w hw)

end GlobalTheory.ConjGal
