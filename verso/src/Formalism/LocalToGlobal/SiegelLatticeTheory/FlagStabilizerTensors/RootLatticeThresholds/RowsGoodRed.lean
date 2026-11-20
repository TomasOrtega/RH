import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.AllRowsOf
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RowDict
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.EvalTOntoPhi
import Formalism.SharpRestriction.CuspSpanNormBounds.BruhatCellsKronecker.SphericalFunctionConvolutionIdentity
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRMul

noncomputable section

open Formalism.BasicNotions Formalism.MainNotions.ArithmeticCylinders Formalism.L2.SG.RowDict Formalism.L2.SG.AllRowsOf
open scoped InnerProductSpace
open MeasureTheory

namespace Formalism.L2.SG.Pf.RowsGoodRed

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} (X : Formalism.L2.SG.HidaSetting.HidaSetting D)

def VT (t : Tup2 D) : Submodule ℂ (L2X X) :=
  Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X ⊓ LinearMap.ker ((ReT X {t} : L2X X →ₗ[ℂ] L2X X) - LinearMap.id)

def labOf (σ : Fin D.what₂.Drows) : Tup2 D := fun k => D.nd.lab k (D.what₂.ft σ)

def bRow (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (σ : Fin D.what₂.Drows) : L2X X :=
  ((ι (D.sEE (D.what₂.onb σ)) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)

def LabTie (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : Prop :=
  (∀ σ k v, IsLabel D k (D.nd.lab k (D.what₂.ft σ) v)) ∧ (∀ σ, D.ntypes.goodTuple (labOf σ)) ∧
    ∀ σ, bRow X ι σ ∈ VT X (labOf σ)

def ProjT (G : GoodOp X) : Prop :=
  (∀ t : Tup2 D, D.ntypes.goodTuple t → VT X t ≤ goodSub X G) ∧
    ∀ t t' : Tup2 D, t ≠ t' → ∀ φ ∈ VT X t, ∀ φ' ∈ VT X t', ⟪φ, φ'⟫_ℂ = 0

def DcountEq : Prop :=
  ∀ t ∈ labT (D := D), D.ntypes.goodTuple t → dimX X {t} = Module.finrank ℂ (VT X t)

/- English proof (translation)
Take `⟨hl1, hl2, hl3⟩` from `hL`. Use `⟨hl1, hl2, fun t ht hg => ?_⟩` and prove the remaining obligations. Establish `hT'` using `hT`. Take `⟨j, hj⟩` from `hT`. Establish `hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X)` using `fun σ => by`.

Establish `h1` using `hj (D.what₂.onb σ)`. Simplify using `only at h1`. Unfold `bRow`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Establish `hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X))` using `(D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map' (EEC X G).subtype (Submodule.ker_subtype _)`. Establish `hli : LinearIndependent ℂ (bRow X ι)`. Rewrite using `[linearIndependent_iff']`. Introduce `s g hs i hi`. Establish `h0 : conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0`.

Rewrite using `[map_sum]`. Rewrite using `[← hs]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[LinearIsometryEquiv.map_smulₛₗ, conjL_apply, hb σ]`. Simplify using the standard rewrite rules.

Establish `h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0` using `(conjL (muX X)).map_eq_zero_iff.1 h0`. Use `(linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi` as an intermediate fact. Simplify using `using this`. Establish `hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι))`. Introduce `φ hφ`.

Take `⟨F, hF⟩` from `(range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ`. Establish `e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X)` using `by rw [hF]`. Rewrite using `[e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]`. Use `Submodule.sum_mem _ fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[map_smulₛₗ, map_smul, Submodule.coe_smul]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)`. Set `Sf : Finset (Fin D.what₂.Drows)` to `Finset.univ.filter fun σ => labOf σ = t`. Establish `hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ))`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `φ hφ`.

Take `⟨c, hc⟩` from `(Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))`. Use `set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1`. Use `set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2`. Establish `hsplit : φ = φ1 + φ2`. Rewrite using `[← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]`.

Establish `h1V : φ1 ∈ VT X t` using `Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by`. Use `hl3 σ` as an intermediate fact. Rewrite using `[(Finset.mem_filter.1 hσ).2] at this)` and apply the resulting hypothesis. Establish `h2V : φ2 ∈ VT X t`. Use `Submodule.sub_mem _ hφ h1V` as an intermediate fact.

Rewrite `this` using `[hsplit, add_sub_cancel_left]`. Then use the resulting hypothesis. Establish `horth : ⟪φ2, φ2⟫_ℂ = 0` using `by conv_lhs => rw [hφ2]`. Rewrite using `[sum_inner]`. Use `Finset.sum_eq_zero fun σ hσ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]`.

Establish `h20 : φ2 = 0` using `inner_self_eq_zero.1 horth`. Rewrite using `[hsplit, h20, add_zero, hφ1]`. Conclude with `Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨σ, rfl⟩`.

Use `hl3 σ` as an intermediate fact. Rewrite `this` using `[(Finset.mem_filter.1 σ.2).2]`. Then use the resulting hypothesis. Establish `hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ)` using `hli.comp (Subtype.val : Sf → _) Subtype.val_injective`. Rewrite using `[hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]`. Both sides reduce to the same expression.
-/
theorem rowsGood_of (G : GoodOp X) (ι : D.s.HH ≃ₗᵢ[ℂ] Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) (hT : RowDictTie X G ι)
    (hL : LabTie X ι) (hP : ProjT X G) (hD : DcountEq X) : RowsGood X := by
  classical
  obtain ⟨hl1, hl2, hl3⟩ := hL
  refine ⟨hl1, hl2, fun t ht hg => ?_⟩
  have hT' := hT
  obtain ⟨j, hj⟩ := hT
  have hb : ∀ σ, bRow X ι σ = star ((j (D.what₂.onb σ) : EEC X G) : L2X X) := fun σ => by
    have h1 := hj (D.what₂.onb σ)
    simp only at h1
    unfold bRow; rw [h1]; rfl

  have hf : LinearIndependent ℂ (fun σ => ((j (D.what₂.onb σ) : EEC X G) : L2X X)) :=
    (D.what₂.onb.toBasis.linearIndependent.map' j.toLinearEquiv.toLinearMap j.toLinearEquiv.ker).map'
      (EEC X G).subtype (Submodule.ker_subtype _)
  have hli : LinearIndependent ℂ (bRow X ι) := by
    rw [linearIndependent_iff']
    intro s g hs i hi
    have h0 : conjL (muX X) (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 := by
      rw [map_sum]
      rw [← hs]
      refine Finset.sum_congr rfl fun σ _ => ?_
      rw [LinearIsometryEquiv.map_smulₛₗ, conjL_apply, hb σ]
      simp
    have h1 : (∑ i ∈ s, (starRingEnd ℂ (g i)) • ((j (D.what₂.onb i) : EEC X G) : L2X X)) = 0 :=
      (conjL (muX X)).map_eq_zero_iff.1 h0
    have := (linearIndependent_iff'.1 hf) s (fun i => starRingEnd ℂ (g i)) h1 i hi
    simpa using this

  have hspan : ∀ φ ∈ goodSub X G, φ ∈ Submodule.span ℂ (Set.range (bRow X ι)) := by
    intro φ hφ
    obtain ⟨F, hF⟩ := (range_sEE X hT' ⟨φ, hφ.1⟩).1 hφ
    have e : φ = ((ι (D.sEE F) : Formalism.L2.SG.PoincareInHH.PoincareSetting.HHX X) : L2X X) := by rw [hF]
    rw [e, ← D.what₂.onb.sum_repr F, map_sum, map_sum, Submodule.coe_sum]
    refine Submodule.sum_mem _ fun σ _ => ?_
    rw [map_smulₛₗ, map_smul, Submodule.coe_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨σ, rfl⟩)

  let Sf : Finset (Fin D.what₂.Drows) := Finset.univ.filter fun σ => labOf σ = t
  have hEq : VT X t = Submodule.span ℂ (Set.range (fun σ : Sf => bRow X ι σ)) := by
    apply le_antisymm
    · intro φ hφ
      obtain ⟨c, hc⟩ := (Submodule.mem_span_range_iff_exists_fun ℂ).1 (hspan φ (hP.1 t hg hφ))
      set φ1 := ∑ σ ∈ Sf, c σ • bRow X ι σ with hφ1
      set φ2 := ∑ σ ∈ Finset.univ.filter (fun σ => ¬ labOf σ = t), c σ • bRow X ι σ with hφ2
      have hsplit : φ = φ1 + φ2 := by
        rw [← hc, hφ1, hφ2, Finset.sum_filter_add_sum_filter_not]
      have h1V : φ1 ∈ VT X t := Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (by
        have := hl3 σ; rwa [(Finset.mem_filter.1 hσ).2] at this)
      have h2V : φ2 ∈ VT X t := by
        have := Submodule.sub_mem _ hφ h1V
        rwa [hsplit, add_sub_cancel_left] at this
      have horth : ⟪φ2, φ2⟫_ℂ = 0 := by
        conv_lhs => rw [hφ2]
        rw [sum_inner]
        refine Finset.sum_eq_zero fun σ hσ => ?_
        rw [inner_smul_left, hP.2 (labOf σ) t (Finset.mem_filter.1 hσ).2 _ (hl3 σ) _ h2V, mul_zero]
      have h20 : φ2 = 0 := inner_self_eq_zero.1 horth
      rw [hsplit, h20, add_zero, hφ1]
      exact Submodule.sum_mem _ fun σ hσ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨σ, hσ⟩, rfl⟩)
    · rw [Submodule.span_le]
      rintro _ ⟨σ, rfl⟩
      have := hl3 σ
      rwa [(Finset.mem_filter.1 σ.2).2] at this
  have hli' : LinearIndependent ℂ (fun σ : Sf => bRow X ι σ) := hli.comp (Subtype.val : Sf → _) Subtype.val_injective
  rw [hD t ht hg, hEq, finrank_span_eq_card hli', Fintype.card_coe]
  rfl

def EtConv : Prop := ∀ (S S' : Set (Tup2 D)) (φ : L2X X), ReT X S (ReT X S' φ) = ReT X (S ∩ S') φ

def EtEmpty : Prop := ∀ φ : L2X X, ReT X ∅ φ = 0

def EtAdj : Prop := ∀ (S : Set (Tup2 D)) (φ ψ : L2X X), ⟪ReT X S φ, ψ⟫_ℂ = ⟪φ, ReT X S ψ⟫_ℂ

def EtGood (G : GoodOp X) : Prop :=
  ∀ t : Tup2 D, D.ntypes.goodTuple t → ∀ φ : L2X X, G.Rg (ReT X {t} φ) = ReT X {t} φ

/- English proof (translation)
Establish `h2` using `(Submodule.mem_inf.mp h).2`. Rewrite `h2` using `[LinearMap.mem_ker]`. Simplify `h2` using `[sub_eq_zero]`.
-/
theorem mem_VT {t : Tup2 D} {φ : L2X X} (h : φ ∈ VT X t) : ReT X {t} φ = φ := by
  have h2 := (Submodule.mem_inf.mp h).2
  rw [LinearMap.mem_ker] at h2
  simpa [sub_eq_zero] using h2

/- English proof (translation)
Use `⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩` and prove the remaining obligations. Use `Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩` and prove the remaining obligations. Establish `h1` using `hG t ht φ`. Rewrite `h1` using `[mem_VT X hφ]`. Rewrite using `[LinearMap.mem_ker]`.

Simplify `h1` using `[sub_eq_zero]`. Rewrite using `[← mem_VT X hφ, ← mem_VT X hφ', hA, hC]`. Establish `hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅`. Use extensionality with `s`. Simplify using `only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]`.

Introduce and unpack `rfl`. Conclude with `htt`. Rewrite using `[hE0, hE, inner_zero_right]`.
-/
theorem projT_of (G : GoodOp X) (hC : EtConv X) (hE : EtEmpty X) (hA : EtAdj X) (hG : EtGood X G) : ProjT X G := by
  refine ⟨fun t ht φ hφ => ?_, fun t t' htt φ hφ φ' hφ' => ?_⟩
  · refine Submodule.mem_inf.mpr ⟨(Submodule.mem_inf.mp hφ).1, ?_⟩
    have h1 := hG t ht φ
    rw [mem_VT X hφ] at h1
    rw [LinearMap.mem_ker]
    simpa [sub_eq_zero] using h1
  · rw [← mem_VT X hφ, ← mem_VT X hφ', hA, hC]
    have hE0 : ({t} : Set (Tup2 D)) ∩ {t'} = ∅ := by
      ext s
      simp only [Set.mem_inter_iff, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false, not_and]
      rintro rfl
      exact htt
    rw [hE0, hE, inner_zero_right]

/- English proof (translation)
Introduce `φ`. Establish `hES : ∀ g, (ES (D` using `D) ∅).coeff g = 0 := by`. Introduce `g`. Simplify using `[ES]`. Establish `hg : egA X (ES (D` using `D) ∅) = 0 := by`.

Use function extensionality and compare the values at `y`. Simplify using `[egA, hES]`. Establish `he : eT X ∅ = 0`. Use function extensionality and compare the values at `x`. Simplify using `[eT, Formalism.MainNotions.S.AutInst.convF, hg]`.

Unfold `ReT`. Use `split_ifs with h`. Establish `hT` using `(Classical.choose_spec h).2`. Establish `h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0` using `fun x => by`. Rewrite using `[hT x φ, he]`.

Simplify using the standard rewrite rules. Conclude with `inner_self_eq_zero.mp (h0 _)`. Both sides reduce to the same expression.
-/
theorem etEmpty : EtEmpty X := by
  intro φ
  have hES : ∀ g, (ES (D := D) ∅).coeff g = 0 := by
    intro g
    simp [ES]
  have hg : egA X (ES (D := D) ∅) = 0 := by
    funext y
    simp [egA, hES]
  have he : eT X ∅ = 0 := by
    funext x
    simp [eT, Formalism.MainNotions.S.AutInst.convF, hg]
  unfold ReT
  split_ifs with h
  · have hT := (Classical.choose_spec h).2
    have h0 : ∀ x, ⟪x, (Classical.choose h) φ⟫_ℂ = 0 := fun x => by
      rw [hT x φ, he]
      simp
    exact inner_self_eq_zero.mp (h0 _)
  · rfl

/- English proof (translation)
Establish `: X.B.μf.IsMulRightInvariant` using `Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf`. Establish `hK` using `Formalism.L2.SG.Closed.level_subgroup_is_group X`. Establish `hL` using `Formalism.L2.SG.Closed.level_subgroup_properties X`. Establish `he1 : X.B.e 1 ≠ 0`. Rewrite using `[X.e_eq]`.

Establish `h1 : (1 : X.B.I.Gf) ∈ X.K2` using `hK.1`. Rewrite using `[if_pos (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]`. Establish `hc : X.chi2 1 ≠ 0`. Introduce `h0`. Use `hK.2.2.2.2 1 h1` as an intermediate fact.

Rewrite `this` using `[h0, norm_zero]`. Conclude with `zero_ne_one this`. Establish `hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0`. Rewrite using `[Complex.ofReal_ne_zero]`. Conclude with `(ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'`.

Conclude with `div_ne_zero (star_ne_zero.2 hc) hv`. Conclude with `Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm X.B.Re_spec.1.norm (norm_pos_iff.2 he1)`.
-/
theorem invInvariant_muf : X.B.μf.IsInvInvariant := by
  have : X.B.μf.IsMulRightInvariant := Formalism.L2.SG.Closed.GfUnimod_holds X.B.I X.B.μf
  have hK := Formalism.L2.SG.Closed.level_subgroup_is_group X
  have hL := Formalism.L2.SG.Closed.level_subgroup_properties X
  have he1 : X.B.e 1 ≠ 0 := by
    rw [X.e_eq]
    have h1 : (1 : X.B.I.Gf) ∈ X.K2 := hK.1
    rw [if_pos (show (1 : X.B.I.Gf) ∈ Formalism.L2.SG.HidaSetting.K2set X.B.I X.B.g X.e0 X.z0 X.bw from h1)]
    have hc : X.chi2 1 ≠ 0 := by
      intro h0; have := hK.2.2.2.2 1 h1; rw [h0, norm_zero] at this; exact zero_ne_one this
    have hv : ((X.B.μf X.K2).toReal : ℂ) ≠ 0 := by
      rw [Complex.ofReal_ne_zero]; exact (ENNReal.toReal_pos hL.2.2.1.ne' hL.2.2.2.ne).ne'
    exact div_ne_zero (star_ne_zero.2 hc) hv
  exact Formalism.MainNotions.BridgeLemma.inv_invariant_of_bi_invariant X.B.μf (fun g => ‖X.B.e g‖) X.B.e_adm.1.continuous.norm
    X.B.Re_spec.1.norm (norm_pos_iff.2 he1)

def EtSA : Prop := ∀ (S : Set (Tup2 D)) (x : X.B.I.Gf), star (eT X S x⁻¹) = eT X S x

/- English proof (translation)
Use `haveI := invInvariant_muf X`. Introduce `S φ ψ`. Establish `hT` using `reT_spec X (etInt_holds X) S`. Establish `hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ`. Introduce `g`.

Use `Formalism.L2.SG.EvalTOntoPhi.inner_reg X ((1, g⁻¹) : X.B.I.GA) φ ψ` as an intermediate fact. Rewrite using `[this, Prod.inv_mk, inv_one, inv_inv]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← starRingEnd_apply, ← integral_conj]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations.

Use `show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _`. Rewrite using `[map_mul]`. Use `show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ`. Rewrite using `[← hreg g, inner_conj_symm]`. Both sides reduce to the same expression.

Use `_ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by`. Rewrite using `[← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _`. Rewrite using `[inv_inv]`.

Use `_ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by`. Use `integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)` and prove the remaining obligations. Use `show star (eT X S g⁻¹) * _ = _`. Rewrite using `[hSA S g]`. Use `_ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm`.
-/
theorem etAdj_of (hSA : EtSA X) : EtAdj X := by
  haveI := invInvariant_muf X
  intro S φ ψ
  have hT := reT_spec X (etInt_holds X) S
  have hreg : ∀ g : X.B.I.Gf, ⟪X.B.R ((1, g) : X.B.I.GA) φ, ψ⟫_ℂ = ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ := by
    intro g
    have := Formalism.L2.SG.EvalTOntoPhi.inner_reg X ((1, g⁻¹) : X.B.I.GA) φ ψ
    rw [this, Prod.inv_mk, inv_one, inv_inv]
  calc ⟪ReT X S φ, ψ⟫_ℂ = star ⟪ψ, ReT X S φ⟫_ℂ := (inner_conj_symm _ _).symm
    _ = star (∫ g, eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ ∂X.B.μf) := by rw [hT.2]
    _ = ∫ g, star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← starRingEnd_apply, ← integral_conj]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show (starRingEnd ℂ) (eT X S g * ⟪ψ, X.B.R ((1, g) : X.B.I.GA) φ⟫_ℂ) = _
        rw [map_mul]
        show _ = star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ
        rw [← hreg g, inner_conj_symm]
        rfl
    _ = ∫ g, star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        rw [← MeasureTheory.integral_inv_eq_self (fun g => star (eT X S g) * ⟪φ, X.B.R ((1, g⁻¹) : X.B.I.GA) ψ⟫_ℂ) X.B.μf]
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * ⟪φ, X.B.R ((1, g⁻¹⁻¹) : X.B.I.GA) ψ⟫_ℂ = _
        rw [inv_inv]
    _ = ∫ g, eT X S g * ⟪φ, X.B.R ((1, g) : X.B.I.GA) ψ⟫_ℂ ∂X.B.μf := by
        refine integral_congr_ae (Filter.Eventually.of_forall fun g => ?_)
        show star (eT X S g⁻¹) * _ = _
        rw [hSA S g]
    _ = ⟪φ, ReT X S ψ⟫_ℂ := (hT.2 φ ψ).symm

/- English proof (translation)
Introduce `t ht φ`. Establish `h1` using `Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})`. Establish `e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t}`. Rewrite using `[← goodIdempotent_eq, ← ES_good, hEC]`. Use `congr 1`.

Conclude with `Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)`. Rewrite `h1` using `[e]`. Establish `h2` using `isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})`. Conclude with `congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2`.
-/
theorem etGood_of (G : GoodOp X)
    (hEC : ∀ S S' : Set (Tup2 D), X.B.I.convF X.B.μf (egA X (ES S')) (eT X S) = eT X (S' ∩ S)) : EtGood X G := by
  intro t ht φ
  have h1 := Formalism.L2.SG.Pf.AllRowsRMul.isRConvF_conv X G.Rg_spec (reT_spec X (etInt_holds X) {t})
  have e : X.B.I.convF X.B.μf (eg X) (eT X {t}) = eT X {t} := by
    rw [← goodIdempotent_eq, ← ES_good, hEC]
    congr 1
    exact Set.inter_eq_right.2 (Set.singleton_subset_iff.2 ht)
  rw [e] at h1
  have h2 := isRConvF_unique X h1 (reT_spec X (etInt_holds X) {t})
  exact congrArg (fun T : L2X X →L[ℂ] L2X X => T φ) h2

end Formalism.L2.SG.Pf.RowsGoodRed
