import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.FrMIsIsom
import Formalism.LocalToGlobal.SiegelLatticeTheory.HaarTransversals.UnitaryHaarProducts.SCompact

noncomputable section

open MeasureTheory Matrix Topology
open scoped ComplexConjugate ENNReal NNReal

namespace Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH

open Formalism.L2.SG.RealObj Formalism.L2.SG.HidaSetting Formalism.REAL Formalism.L2.SG.RealObj.InfCut.JacobianCoordinates Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames

variable {n r k : ℕ} {ε : Fin n → Bool} {e p : Fin r → Fin n → ℂ} {z : Fin n → ℂ} {T : ℝ}

/- English proof (translation)
Use `set Q : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε} ∩ ((⋂ a, {g | g *ᵥ e a = e a}) ∩ ((⋂ a, {g | g *ᵥ p a = p a}) ∩ {g | g *ᵥ z = z})) with hQ`. Establish `e1 : (HG ε e p z : Set (UJ ε)) = (fun g : UJ ε => Formalism.MainNotions.S.uMat g) ⁻¹' Q`. Use extensionality with `g`. Simplify using `only [coe_HG, HLoc, hQ, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]`. Conclude with `⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩`.

Establish `hQc : IsClosed Q`. Use `(isClosed_eq ((continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id) continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.m …` and prove the remaining obligations. Establish `hzz : hJ ε z z ≠ 0`. Rewrite using `[Fw.zz]`. Conclude with `neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Fw.T_ne)`.

Establish `hQk : IsCompact Q` using `Formalism.L2.SG.Pf.frame_compact ε e p z w Fw.ee Fw.pp Fw.ep Fw.ez Fw.pz hzz Fw.ww Fw.ew Fw.pw Fw.zw hdim.symm hQc (fun g hg => ⟨hg.1, fun a => Set.mem_iInter.1 hg.2.1 a, fun a => Set.mem_iInter.1 hg.2.2.1 a, hg.2.2.2⟩)`. Rewrite using `[e1]`. Conclude with `((Formalism.REAL.uJEmb n ε).1).isCompact_preimage hQk`.
-/
theorem HG_compact {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k) :
    IsCompact (HG ε e p z : Set (UJ ε)) := by
  set Q : Set (Matrix (Fin n) (Fin n) ℂ) := {g | gᴴ * Jm ε * g = Jm ε} ∩ ((⋂ a, {g | g *ᵥ e a = e a}) ∩
    ((⋂ a, {g | g *ᵥ p a = p a}) ∩ {g | g *ᵥ z = z})) with hQ
  have e1 : (HG ε e p z : Set (UJ ε)) = (fun g : UJ ε => Formalism.MainNotions.S.uMat g) ⁻¹' Q := by
    ext g
    simp only [coe_HG, HLoc, hQ, Set.mem_setOf_eq, Set.mem_preimage, Set.mem_inter_iff, Set.mem_iInter]
    exact ⟨fun h => ⟨g.2, h.1, h.2.1, h.2.2⟩, fun h => ⟨h.2.1, h.2.2.1, h.2.2.2⟩⟩
  have hQc : IsClosed Q := by
    refine (isClosed_eq ((continuous_id.matrix_conjTranspose.mul continuous_const).mul continuous_id)
      continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
        continuous_const).inter ((isClosed_iInter fun a => isClosed_eq (continuous_id.matrix_mulVec continuous_const)
          continuous_const).inter (isClosed_eq (continuous_id.matrix_mulVec continuous_const) continuous_const)))
  have hzz : hJ ε z z ≠ 0 := by
    rw [Fw.zz]; exact neg_ne_zero.2 (Complex.ofReal_ne_zero.2 Fw.T_ne)
  have hQk : IsCompact Q := Formalism.L2.SG.Pf.frame_compact ε e p z w Fw.ee Fw.pp Fw.ep Fw.ez Fw.pz hzz Fw.ww Fw.ew Fw.pw
    Fw.zw hdim.symm hQc (fun g hg => ⟨hg.1, fun a => Set.mem_iInter.1 hg.2.1 a,
      fun a => Set.mem_iInter.1 hg.2.2.1 a, hg.2.2.2⟩)
  rw [e1]
  exact ((Formalism.REAL.uJEmb n ε).1).isCompact_preimage hQk

def conjH (h : UJ ε) : UJ ε ≃ₜ UJ ε := (Homeomorph.mulLeft h).trans (Homeomorph.mulRight h⁻¹)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem conjH_apply (h x : UJ ε) : conjH h x = h * x * h⁻¹ := rfl

/- English proof (translation)
Simplify using `[conjH, Homeomorph.mulLeft, Homeomorph.mulRight, mul_assoc]`.
-/
theorem conjH_symm_apply (h x : UJ ε) : (conjH h).symm x = h⁻¹ * x * h := by
  simp [conjH, Homeomorph.mulLeft, Homeomorph.mulRight, mul_assoc]

section Conj

local notation "NS" => (NG ε e z)

/- English proof (translation)
Take `⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩` from `hμ`. Establish `hmeas : Measurable (conjH h)` using `(conjH h).continuous.measurable`. Use `set E := (conjH h).toMeasurableEquiv with hE`. Establish `hEe : ⇑E = ⇑(conjH h)` using `rfl`. Use `⟨⟨?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hEe]`. Conclude with `E.sigmaFinite_map`. Introduce `h0`. Apply `hne` to reduce the goal to its premises. Use `congrArg (fun m : Measure (UJ ε) => m Set.univ) h0` as an intermediate fact.

Simplify using `only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero, Pi.zero_apply] at this`. Conclude with `Measure.measure_univ_eq_zero.1 this`. Rewrite using `[Measure.map_apply hmeas (show MeasurableSet (NLoc ε e z)ᶜ from (NG_closed ε e z).measurableSet.compl)]`. Use `measure_mono_null (s := (conjH h) ⁻¹' (NLoc ε e z)ᶜ) (t := (NLoc ε e z)ᶜ) (fun x hx hxN => hx ?_) hcompl` and prove the remaining obligations. Conclude with `conj_mem ε e p z hh hxN`.

Establish `ht' : h⁻¹ * t * h ∈ NS`. Use `conj_mem ε e p z ((HG ε e p z).inv_mem hh) ht` as an intermediate fact. Simplify using `using this`. Establish `hcomm : (fun x => t * x) ∘ conjH h = conjH h ∘ (fun x => h⁻¹ * t * h * x)`. Use function extensionality and compare the values at `x`.

Simplify using `only [Function.comp_apply, conjH_apply]`. Use `group`. Rewrite using `[Measure.map_map (measurable_const_mul t) hmeas, hcomm, ← Measure.map_map hmeas (measurable_const_mul _), hinv _ ht']`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Rewrite using `[Measure.map_apply hmeas hK.measurableSet]`.

Establish `: (conjH h) ⁻¹' K = (conjH h).symm '' K` using `(congrFun (conjH h).image_symm K).symm`. Rewrite using `[this]`. Conclude with `(hK.image (conjH h).symm.continuous).measure_lt_top`.
-/
theorem map_conj_isHaarS {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε}
    (hh : h ∈ HG ε e p z) : IsHaarS (NLoc ε e z) (μ.map (conjH h)) := by
  obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hμ
  have hmeas : Measurable (conjH h) := (conjH h).continuous.measurable
  set E := (conjH h).toMeasurableEquiv with hE
  have hEe : ⇑E = ⇑(conjH h) := rfl
  refine ⟨⟨?_, ?_, ?_, fun t ht => ?_⟩, ?_⟩
  · rw [← hEe]; exact E.sigmaFinite_map
  · intro h0
    apply hne
    have := congrArg (fun m : Measure (UJ ε) => m Set.univ) h0
    simp only [Measure.map_apply hmeas MeasurableSet.univ, Set.preimage_univ, Measure.coe_zero,
      Pi.zero_apply] at this
    exact Measure.measure_univ_eq_zero.1 this
  · rw [Measure.map_apply hmeas (show MeasurableSet (NLoc ε e z)ᶜ from (NG_closed ε e z).measurableSet.compl)]
    refine measure_mono_null (s := (conjH h) ⁻¹' (NLoc ε e z)ᶜ) (t := (NLoc ε e z)ᶜ)
      (fun x hx hxN => hx ?_) hcompl
    exact conj_mem ε e p z hh hxN
  · have ht' : h⁻¹ * t * h ∈ NS := by
      have := conj_mem ε e p z ((HG ε e p z).inv_mem hh) ht
      simpa using this
    have hcomm : (fun x => t * x) ∘ conjH h = conjH h ∘ (fun x => h⁻¹ * t * h * x) := by
      funext x; simp only [Function.comp_apply, conjH_apply]; group
    rw [Measure.map_map (measurable_const_mul t) hmeas, hcomm,
      ← Measure.map_map hmeas (measurable_const_mul _), hinv _ ht']
  · refine ⟨fun K hK => ?_⟩
    rw [Measure.map_apply hmeas hK.measurableSet]
    have : (conjH h) ⁻¹' K = (conjH h).symm '' K := (congrFun (conjH h).image_symm K).symm
    rw [this]
    exact (hK.image (conjH h).symm.continuous).measure_lt_top

/- English proof (translation)
Use `haveI : LocallyCompactSpace NS := (NG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace`. Use `haveI : SecondCountableTopology NS := Topology.IsEmbedding.subtypeVal.secondCountableTopology`. Establish `hNm : MeasurableSet (NS : Set (UJ ε))` using `(NG_closed ε e z).measurableSet`. Establish `memb : MeasurableEmbedding (Subtype.val : NS → UJ ε)` using `MeasurableEmbedding.subtype_coe hNm`. Use `set m0 : Measure (UJ ε) := (Measure.haar : Measure NS).map Subtype.val with hm0`.

Establish `huniq : ∀ ν : Measure (UJ ε), IsHaarS (NLoc ε e z) ν → ∃ c : ℝ≥0, ν = c • m0`. Introduce `ν hν`. Take `⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩` from `hν`. Use `set ν' : Measure NS := ν.comap Subtype.val with hν'`. Establish `hrestr : ν.restrict (NS : Set (UJ ε)) = ν`.

Apply `Measure.restrict_eq_self_of_ae_mem` to reduce the goal to its premises. Rewrite using `[ae_iff]`. Conclude with `hcompl`. Establish `hmapν : ν'.map Subtype.val = ν`. Rewrite using `[hν', memb.map_comap, Subtype.range_coe, hrestr]`.

Establish `himg : ∀ (t : NS) (A : Set NS), Subtype.val '' ((fun x => t * x) ⁻¹' A) = (fun x => (t : UJ ε) * x) ⁻¹' (Subtype.val '' A)`. Introduce `t A`. Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`.

Conclude with `⟨t * y, hy, rfl⟩`. Introduce and unpack `⟨a, ha, hax⟩`. Establish `hxS : x ∈ NS`. Establish `: x = ((t⁻¹ * a : NS) : UJ ε)`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, hax]`.

Use `group`. Rewrite using `[this]`. Conclude with `(t⁻¹ * a).2`. Use `⟨⟨x, hxS⟩, ?_, rfl⟩` and prove the remaining obligations. Use `show t * ⟨x, hxS⟩ ∈ A`.

Establish `: t * ⟨x, hxS⟩ = a` using `Subtype.ext (by simpa using hax.symm)`. Rewrite using `[this]`. Conclude with `ha`. Establish `hνinv : ν'.IsMulLeftInvariant`. Use `⟨fun t => ?_⟩` and prove the remaining obligations.

Use extensionality with `A hA`. Rewrite using `[Measure.map_apply (measurable_const_mul t) hA, hν', memb.comap_apply, memb.comap_apply, himg, ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]`. Establish `hνfin : IsFiniteMeasureOnCompacts ν'`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Rewrite using `[hν', memb.comap_apply]`.

Conclude with `(hK.image continuous_subtype_val).measure_lt_top`. Establish `hνeq : ν' = ν'.haarScalarFactor Measure.haar • Measure.haar` using `Measure.isMulLeftInvariant_eq_smul ν' Measure.haar`. Use `⟨ν'.haarScalarFactor Measure.haar, ?_⟩` and prove the remaining obligations. Use `conv_lhs => rw [← hmapν, hνeq]`. Rewrite using `[Measure.map_smul]`.

Choose the witnesses or unpack the hypotheses as in `⟨C', hC'c, hC'n⟩ : ∃ C' : Set NS, IsCompact C' ∧ C' ∈ 𝓝 (1 : NS) := by`. Take `⟨C', h1, h2⟩` from `exists_compact_mem_nhds (1 : NS)`. Conclude with `⟨C', h1, h2⟩`. Establish `hC'pos : 0 < (Measure.haar : Measure NS) C'` using `Measure.measure_pos_of_mem_nhds _ hC'n`. Use `set C : Set (UJ ε) := Subtype.val '' C' with hC`.

Establish `hHc` using `HG_compact Fw hdim`. Use `set K : Set (UJ ε) := (fun q : UJ ε × UJ ε => q.1 * q.2 * q.1⁻¹) '' ((HG ε e p z : Set (UJ ε)) ×ˢ C) with hK`. Establish `hKc : IsCompact K` using `(hHc.prod (hC'c.image continuous_subtype_val)).image (by fun_prop)`. Establish `hKN : K ⊆ (NS : Set (UJ ε))`. Introduce and unpack `_ ⟨⟨h', x⟩, ⟨hh', ⟨x', _, rfl⟩⟩, rfl⟩`.

Conclude with `conj_mem ε e p z hh' x'.2`. Establish `hCK : C ⊆ K` using `fun x hx => ⟨(1, x), ⟨(HG ε e p z).one_mem, hx⟩, by simp⟩`. Establish `hKm : MeasurableSet K` using `hKc.isClosed.measurableSet`. Establish `hm0K : m0 K = (Measure.haar : Measure NS) (Subtype.val ⁻¹' K)`. Rewrite using `[hm0, Measure.map_apply measurable_subtype_coe hKm]`.

Establish `hm0pos : 0 < m0 K`. Rewrite using `[hm0K]`. Use `lt_of_lt_of_le hC'pos (measure_mono ?_)` and prove the remaining obligations. Introduce `x hx`. Conclude with `hCK ⟨x, hx, rfl⟩`.

Establish `hm0fin : m0 K < ⊤`. Rewrite using `[hm0K]`. Conclude with `((NG_closed ε e z).isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top`. Establish `hinvK : (conjH h) ⁻¹' K = K`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨h', x'⟩, ⟨hh', hx'⟩, hxe⟩`. Use `⟨(h⁻¹ * h', x'), ⟨(HG ε e p z).mul_mem ((HG ε e p z).inv_mem hh) hh', hx'⟩, ?_⟩` and prove the remaining obligations. Establish `hxe' : h' * x' * h'⁻¹ = h * x * h⁻¹` using `hxe`. Use `show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = x`.

Rewrite using `[show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * x' * h'⁻¹) * h by group, hxe']`. Use `group`. Introduce and unpack `⟨⟨h', x'⟩, ⟨hh', hx'⟩, rfl⟩`. Use `⟨(h * h', x'), ⟨(HG ε e p z).mul_mem hh hh', hx'⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [conjH_apply]`.

Use `group`. Take `⟨c1, h1⟩` from `huniq μ hμ`. Take `⟨c2, h2⟩` from `huniq _ (map_conj_isHaarS hμ hh)`. Establish `hK12 : (μ.map (conjH h)) K = μ K`. Rewrite using `[Measure.map_apply (conjH h).continuous.measurable hKm, hinvK]`.

Establish `hc : (c2 : ℝ≥0∞) = c1`. Establish `e2 : (μ.map (conjH h)) K = c2 * m0 K` using `by conv_lhs => rw [h2]`. Both sides reduce to the same expression. Establish `e1 : μ K = c1 * m0 K` using `by conv_lhs => rw [h1]`. Both sides reduce to the same expression.

Rewrite `hK12` using `[e2, e1]`. Conclude with `(ENNReal.mul_left_inj hm0pos.ne' hm0fin.ne).1 hK12`. Rewrite using `[h2, h1]`. Use `congr 1`. Conclude with `hc` after adjusting the coercions.
-/
theorem conj_haar_eq {w : Fin k → Fin n → ℂ} (Fw : Frm ε e p z w T) (hdim : n = 2 * r + 1 + k)
    {μ : Measure (UJ ε)} (hμ : IsHaarS (NLoc ε e z) μ) {h : UJ ε} (hh : h ∈ HG ε e p z) :
    μ.map (conjH h) = μ := by
  haveI : LocallyCompactSpace NS := (NG_closed ε e z).isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology NS := Topology.IsEmbedding.subtypeVal.secondCountableTopology
  have hNm : MeasurableSet (NS : Set (UJ ε)) := (NG_closed ε e z).measurableSet
  have memb : MeasurableEmbedding (Subtype.val : NS → UJ ε) := MeasurableEmbedding.subtype_coe hNm
  set m0 : Measure (UJ ε) := (Measure.haar : Measure NS).map Subtype.val with hm0

  have huniq : ∀ ν : Measure (UJ ε), IsHaarS (NLoc ε e z) ν → ∃ c : ℝ≥0, ν = c • m0 := by
    intro ν hν
    obtain ⟨⟨hσ, hne, hcompl, hinv⟩, hfin⟩ := hν
    set ν' : Measure NS := ν.comap Subtype.val with hν'
    have hrestr : ν.restrict (NS : Set (UJ ε)) = ν := by
      apply Measure.restrict_eq_self_of_ae_mem
      rw [ae_iff]
      exact hcompl
    have hmapν : ν'.map Subtype.val = ν := by
      rw [hν', memb.map_comap, Subtype.range_coe, hrestr]
    have himg : ∀ (t : NS) (A : Set NS), Subtype.val '' ((fun x => t * x) ⁻¹' A) =
        (fun x => (t : UJ ε) * x) ⁻¹' (Subtype.val '' A) := by
      intro t A
      ext x
      constructor
      · rintro ⟨y, hy, rfl⟩
        exact ⟨t * y, hy, rfl⟩
      · rintro ⟨a, ha, hax⟩
        have hxS : x ∈ NS := by
          have : x = ((t⁻¹ * a : NS) : UJ ε) := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, hax]; group
          rw [this]; exact (t⁻¹ * a).2
        refine ⟨⟨x, hxS⟩, ?_, rfl⟩
        show t * ⟨x, hxS⟩ ∈ A
        have : t * ⟨x, hxS⟩ = a := Subtype.ext (by simpa using hax.symm)
        rw [this]; exact ha
    have hνinv : ν'.IsMulLeftInvariant := by
      refine ⟨fun t => ?_⟩
      ext A hA
      rw [Measure.map_apply (measurable_const_mul t) hA, hν', memb.comap_apply, memb.comap_apply, himg,
        ← Measure.map_apply (measurable_const_mul _) (memb.measurableSet_image.2 hA), hinv _ t.2]
    have hνfin : IsFiniteMeasureOnCompacts ν' := by
      refine ⟨fun K hK => ?_⟩
      rw [hν', memb.comap_apply]
      exact (hK.image continuous_subtype_val).measure_lt_top
    have hνeq : ν' = ν'.haarScalarFactor Measure.haar • Measure.haar :=
      Measure.isMulLeftInvariant_eq_smul ν' Measure.haar
    refine ⟨ν'.haarScalarFactor Measure.haar, ?_⟩
    conv_lhs => rw [← hmapν, hνeq]
    rw [Measure.map_smul]

  obtain ⟨C', hC'c, hC'n⟩ : ∃ C' : Set NS, IsCompact C' ∧ C' ∈ 𝓝 (1 : NS) := by
    obtain ⟨C', h1, h2⟩ := exists_compact_mem_nhds (1 : NS)
    exact ⟨C', h1, h2⟩
  have hC'pos : 0 < (Measure.haar : Measure NS) C' := Measure.measure_pos_of_mem_nhds _ hC'n
  set C : Set (UJ ε) := Subtype.val '' C' with hC
  have hHc := HG_compact Fw hdim
  set K : Set (UJ ε) := (fun q : UJ ε × UJ ε => q.1 * q.2 * q.1⁻¹) '' ((HG ε e p z : Set (UJ ε)) ×ˢ C) with hK
  have hKc : IsCompact K :=
    (hHc.prod (hC'c.image continuous_subtype_val)).image (by fun_prop)
  have hKN : K ⊆ (NS : Set (UJ ε)) := by
    rintro _ ⟨⟨h', x⟩, ⟨hh', ⟨x', _, rfl⟩⟩, rfl⟩
    exact conj_mem ε e p z hh' x'.2
  have hCK : C ⊆ K := fun x hx => ⟨(1, x), ⟨(HG ε e p z).one_mem, hx⟩, by simp⟩
  have hKm : MeasurableSet K := hKc.isClosed.measurableSet
  have hm0K : m0 K = (Measure.haar : Measure NS) (Subtype.val ⁻¹' K) := by
    rw [hm0, Measure.map_apply measurable_subtype_coe hKm]
  have hm0pos : 0 < m0 K := by
    rw [hm0K]
    refine lt_of_lt_of_le hC'pos (measure_mono ?_)
    intro x hx
    exact hCK ⟨x, hx, rfl⟩
  have hm0fin : m0 K < ⊤ := by
    rw [hm0K]
    exact ((NG_closed ε e z).isClosedEmbedding_subtypeVal.isCompact_preimage hKc).measure_lt_top
  have hinvK : (conjH h) ⁻¹' K = K := by
    ext x
    constructor
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, hxe⟩
      refine ⟨(h⁻¹ * h', x'), ⟨(HG ε e p z).mul_mem ((HG ε e p z).inv_mem hh) hh', hx'⟩, ?_⟩
      have hxe' : h' * x' * h'⁻¹ = h * x * h⁻¹ := hxe
      show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = x
      rw [show (h⁻¹ * h') * x' * (h⁻¹ * h')⁻¹ = h⁻¹ * (h' * x' * h'⁻¹) * h by group, hxe']
      group
    · rintro ⟨⟨h', x'⟩, ⟨hh', hx'⟩, rfl⟩
      refine ⟨(h * h', x'), ⟨(HG ε e p z).mul_mem hh hh', hx'⟩, ?_⟩
      simp only [conjH_apply]
      group

  obtain ⟨c1, h1⟩ := huniq μ hμ
  obtain ⟨c2, h2⟩ := huniq _ (map_conj_isHaarS hμ hh)
  have hK12 : (μ.map (conjH h)) K = μ K := by
    rw [Measure.map_apply (conjH h).continuous.measurable hKm, hinvK]
  have hc : (c2 : ℝ≥0∞) = c1 := by
    have e2 : (μ.map (conjH h)) K = c2 * m0 K := by
      conv_lhs => rw [h2]
      rfl
    have e1 : μ K = c1 * m0 K := by
      conv_lhs => rw [h1]
      rfl
    rw [e2, e1] at hK12
    exact (ENNReal.mul_left_inj hm0pos.ne' hm0fin.ne).1 hK12
  rw [h2, h1]
  congr 1
  exact_mod_cast hc

end Conj

end Formalism.L2.SG.RealObj.InfCut.NilradicalHermitianFrames.NH
