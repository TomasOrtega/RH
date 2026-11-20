import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SplitHomeoApply
open MeasureTheory Topology
open scoped ENNReal NNReal Matrix Pointwise

namespace GlobalTheory.CompanionTheory.SplitExtLat

/- English proof (translation)
Introduce `P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hΓ ν _ D hDm hD hD0 hDtop`. Establish `hKc : IsClosed (π.ker : Set P)`. Rewrite using `[MonoidHom.coe_ker]`. Conclude with `isClosed_singleton.preimage hπ`. Use `haveI : LocallyCompactSpace π.ker := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace`.

Use `haveI : SecondCountableTopology π.ker := TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)`. Establish `hcont : ∀ g : P, Continuous (fun m : π.ker => MulAut.conjNormal g m)`. Introduce `g`. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Establish `h1 : (Subtype.val ∘ fun m : π.ker => MulAut.conjNormal g m) = fun m : π.ker => g * (m : P) * g⁻¹`.

Use function extensionality and compare the values at `m`. Simplify using `only [Function.comp_apply, MulAut.conjNormal_apply]`. Rewrite using `[h1]`. Conclude with `(continuous_const.mul continuous_subtype_val).mul continuous_const`. Establish `hsymm : ∀ g : P, ⇑(MulEquiv.symm (MulAut.conjNormal g : MulAut π.ker)) = fun m => MulAut.conjNormal g⁻¹ m`.

Introduce `g`. Use function extensionality and compare the values at `m`. Rewrite using `[MulEquiv.symm_apply_eq]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulAut.conjNormal_apply]`.

Use `group`. Establish `hex : ∀ u : G₁, ∃ c : ℝ≥0, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = c • ν`. Introduce `u`. Use `haveI : (Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν).IsHaarMeasure := MulEquiv.isHaarMeasure_map ν (MulAut.conjNormal (ι u) : MulAut π.ker) (hcont _) (by convert hcont (ι u)⁻¹ using 1; exact hsymm _)`. Conclude with `⟨_, Measure.isMulLeftInvariant_eq_smul _ ν⟩`.

Use `choose a ha using hex`. Establish `hcancel : ∀ b c : ℝ≥0, (b : ℝ≥0∞) * ν D = (c : ℝ≥0∞) * ν D → b = c`. Introduce `b c h`. Conclude with `(ENNReal.mul_left_inj hD0 hDtop.ne).mp h` after adjusting the coercions. Establish `hpre : ∀ v (S : Set π.ker), MeasurableSet S → ν ((fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' S) = (a v : ℝ≥0∞) * ν S`.

Introduce `v S hS`. Rewrite using `[← Measure.map_apply (hcont _).measurable hS, ha v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]`. Establish `hcomp : ∀ u v, (fun m : π.ker => MulAut.conjNormal (ι (u * v)) m) ⁻¹' D = (fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D)`. Introduce `u v`. Use extensionality with `m`.

Simplify using `only [Set.mem_preimage, map_mul, MulAut.mul_apply]`. Establish `hmul : ∀ u v, a (u * v) = a u * a v`. Introduce `u v`. Apply `hcancel` to reduce the goal to its premises. Rewrite using `[← hpre (u * v) D hDm, hcomp, hpre v _ ((hcont _).measurable hDm), hpre u D hDm, ENNReal.coe_mul]`.

Expand and normalize the polynomial expressions, which then agree. Use `haveI : Countable (Γ.subgroupOf π.ker) := by`. Establish `hinj : Function.Injective (fun x : Γ.subgroupOf π.ker => (⟨((x : π.ker) : P), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ))`. Introduce `x y h`. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subtype.mk.injEq] at h`. Conclude with `h`. Conclude with `hinj.countable`. Use `haveI : MeasurableConstSMul (Γ.subgroupOf π.ker) π.ker := ⟨fun c => by show Measurable (fun x : π.ker => (c : π.ker) * x)`.

Conclude with `measurable_id'.const_mul _⟩`. Use `haveI : SMulInvariantMeasure (Γ.subgroupOf π.ker) π.ker ν := ⟨fun c s _ => by show ν ((fun x : π.ker => (c : π.ker) * x) ⁻¹' s) = ν s`. Conclude with `measure_preimage_mul ν _ s⟩`. Establish `hΓ1 : ∀ γ ∈ Γ₁, a γ = 1`. Introduce `γ hγ`.

Establish `hg : ι γ ∈ Γ` using `hΓ γ hγ`. Establish `hqmp : Measure.QuasiMeasurePreserving (fun m : π.ker => MulAut.conjNormal (ι γ) m) ν ν`. Use `⟨(hcont _).measurable, ?_⟩` and prove the remaining obligations. Rewrite using `[ha γ]`. Introduce `s hs`.

Rewrite using `[Measure.smul_apply, hs, smul_zero]`. Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : Γ.subgroupOf π.ker → Γ.subgroupOf π.ker, ∀ s, ((e s : π.ker) : P) = (ι γ)⁻¹ * ((s : π.ker) : P) * ι γ := by`. Use `⟨fun s => ⟨⟨(ι γ)⁻¹ * ((s : π.ker) : P) * ι γ, ?_⟩, ?_⟩, fun s => rfl⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `[MonoidHom.mem_ker.1 (s : π.ker).2]`.

Conclude with `Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Subgroup.mem_subgroupOf.1 s.2)) hg)`. Establish `hebij : Function.Bijective e`. Prove the components needed by the constructor for the conclusion. Introduce `s t hst`. Establish `h1` using `congrArg (fun x : Γ.subgroupOf π.ker => ((x : π.ker) : P)) hst`.

Simplify using `only [he, mul_left_inj, mul_right_inj] at h1`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `h1`. Introduce `t`.

Choose the witnesses or unpack the hypotheses as in `⟨s, hs⟩ : ∃ s : Γ.subgroupOf π.ker, ((s : π.ker) : P) = ι γ * ((t : π.ker) : P) * (ι γ)⁻¹ := by`. Use `⟨⟨⟨ι γ * ((t : π.ker) : P) * (ι γ)⁻¹, ?_⟩, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[MonoidHom.mem_ker]`. Simplify using `[MonoidHom.mem_ker.1 (t : π.ker).2]`. Conclude with `Subgroup.mem_subgroupOf.2 (Γ.mul_mem (Γ.mul_mem hg (Subgroup.mem_subgroupOf.1 t.2)) (Γ.inv_mem hg))`.

Use `⟨s, Subtype.ext (Subtype.ext ?_)⟩` and prove the remaining obligations. Rewrite using `[he, hs]`. Use `group`. Establish `hsemi : ∀ s : Γ.subgroupOf π.ker, Function.Semiconj (fun m : π.ker => MulAut.conjNormal (ι γ) m) (fun x => e s • x) (fun x => s • x)`. Introduce `s x`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [MulAut.conjNormal_apply, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, he]`. Use `group`. Establish `hfd` using `hD.preimage_of_equiv hqmp hebij hsemi`. Establish `hmeq : ν D = ν ((fun m : π.ker => MulAut.conjNormal (ι γ) m) ⁻¹' D)` using `hD.measure_eq hfd`.

Apply `hcancel` to reduce the goal to its premises. Rewrite using `[← hpre γ D hDm, ← hmeq, ENNReal.coe_one, one_mul]`. Establish `hFc : Continuous (fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2)`. Apply `continuous_induced_rng.2` to reduce the goal to its premises. Establish `h1 : (Subtype.val ∘ fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) = fun p => ι p.1 * (p.2 : P) * (ι p.1)⁻¹`.

Use function extensionality and compare the values at `p`. Simplify using `only [Function.comp_apply, MulAut.conjNormal_apply]`. Rewrite using `[h1]`. Conclude with `((hι.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul (hι.comp continuous_fst).inv`. Establish `hE : MeasurableSet ((fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) ⁻¹' D)` using `hFc.measurable hDm`.

Establish `ha_eq : a = fun u => (ν ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) / ν D).toNNReal`. Use function extensionality and compare the values at `u`. Rewrite using `[hpre u D hDm, ENNReal.mul_div_cancel_right hD0 hDtop.ne, ENNReal.toNNReal_coe]`. Establish `hmeas : Measurable a`. Rewrite using `[ha_eq]`.

Conclude with `((measurable_measure_prodMk_left hE).div_const _).ennreal_toNNReal`. Conclude with `⟨{ toFun := a, map_one' := hΓ1 1 Γ₁.one_mem, map_mul' := hmul }, hmeas, hΓ1, fun u => ha u⟩`.
-/
theorem conj_haar_character :
    ∀ (P G₁ : Type) [Group P] [TopologicalSpace P] [IsTopologicalGroup P] [LocallyCompactSpace P] [SecondCountableTopology P] [T2Space P] [MeasurableSpace P] [BorelSpace P] [Group G₁] [TopologicalSpace G₁] [IsTopologicalGroup G₁] [LocallyCompactSpace G₁] [SecondCountableTopology G₁] [T2Space G₁] [MeasurableSpace G₁] [BorelSpace G₁] (ι : G₁ →* P) (π : P →* G₁) (hι : Continuous ι) (hπ : Continuous π) (hπι : ∀ u, π (ι u) = u) (Γ : Subgroup P) (Γ₁ : Subgroup G₁) [Countable Γ] [Countable Γ₁], (∀ u ∈ Γ₁, ι u ∈ Γ) → ∀ (ν : Measure π.ker) [ν.IsHaarMeasure] (D : Set π.ker), MeasurableSet D → IsFundamentalDomain (Γ.subgroupOf π.ker) D ν → ν D ≠ 0 → ν D < ⊤ → ∃ δ : G₁ →* ℝ≥0, Measurable δ ∧ (∀ γ ∈ Γ₁, δ γ = 1) ∧ ∀ u, Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = δ u • ν := by
  intro P G₁ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ ι π hι hπ hπι Γ Γ₁ _ _ hΓ ν _ D hDm hD hD0 hDtop
  classical
  have hKc : IsClosed (π.ker : Set P) := by
    rw [MonoidHom.coe_ker]
    exact isClosed_singleton.preimage hπ
  haveI : LocallyCompactSpace π.ker := hKc.isClosedEmbedding_subtypeVal.locallyCompactSpace
  haveI : SecondCountableTopology π.ker :=
    TopologicalSpace.Subtype.secondCountableTopology (π.ker : Set P)
  have hcont : ∀ g : P, Continuous (fun m : π.ker => MulAut.conjNormal g m) := by
    intro g
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun m : π.ker => MulAut.conjNormal g m) = fun m : π.ker => g * (m : P) * g⁻¹ := by
      funext m
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact (continuous_const.mul continuous_subtype_val).mul continuous_const
  have hsymm : ∀ g : P, ⇑(MulEquiv.symm (MulAut.conjNormal g : MulAut π.ker)) =
      fun m => MulAut.conjNormal g⁻¹ m := by
    intro g
    funext m
    rw [MulEquiv.symm_apply_eq]
    apply Subtype.ext
    simp only [MulAut.conjNormal_apply]
    group
  have hex : ∀ u : G₁, ∃ c : ℝ≥0,
      Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν = c • ν := by
    intro u
    haveI : (Measure.map (fun m : π.ker => MulAut.conjNormal (ι u) m) ν).IsHaarMeasure :=
      MulEquiv.isHaarMeasure_map ν (MulAut.conjNormal (ι u) : MulAut π.ker) (hcont _)
        (by convert hcont (ι u)⁻¹ using 1; exact hsymm _)
    exact ⟨_, Measure.isMulLeftInvariant_eq_smul _ ν⟩
  choose a ha using hex
  have hcancel : ∀ b c : ℝ≥0, (b : ℝ≥0∞) * ν D = (c : ℝ≥0∞) * ν D → b = c := by
    intro b c h
    exact_mod_cast (ENNReal.mul_left_inj hD0 hDtop.ne).mp h
  have hpre : ∀ v (S : Set π.ker), MeasurableSet S →
      ν ((fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹' S) = (a v : ℝ≥0∞) * ν S := by
    intro v S hS
    rw [← Measure.map_apply (hcont _).measurable hS, ha v, Measure.smul_apply, ENNReal.smul_def, smul_eq_mul]
  have hcomp : ∀ u v, (fun m : π.ker => MulAut.conjNormal (ι (u * v)) m) ⁻¹' D =
      (fun m : π.ker => MulAut.conjNormal (ι v) m) ⁻¹'
        ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) := by
    intro u v
    ext m
    simp only [Set.mem_preimage, map_mul, MulAut.mul_apply]
  have hmul : ∀ u v, a (u * v) = a u * a v := by
    intro u v
    apply hcancel
    rw [← hpre (u * v) D hDm, hcomp, hpre v _ ((hcont _).measurable hDm), hpre u D hDm,
      ENNReal.coe_mul]
    ring
  haveI : Countable (Γ.subgroupOf π.ker) := by
    have hinj : Function.Injective (fun x : Γ.subgroupOf π.ker =>
        (⟨((x : π.ker) : P), Subgroup.mem_subgroupOf.1 x.2⟩ : Γ)) := by
      intro x y h
      apply Subtype.ext
      apply Subtype.ext
      simp only [Subtype.mk.injEq] at h
      exact h
    exact hinj.countable
  haveI : MeasurableConstSMul (Γ.subgroupOf π.ker) π.ker :=
    ⟨fun c => by
      show Measurable (fun x : π.ker => (c : π.ker) * x)
      exact measurable_id'.const_mul _⟩
  haveI : SMulInvariantMeasure (Γ.subgroupOf π.ker) π.ker ν :=
    ⟨fun c s _ => by
      show ν ((fun x : π.ker => (c : π.ker) * x) ⁻¹' s) = ν s
      exact measure_preimage_mul ν _ s⟩
  have hΓ1 : ∀ γ ∈ Γ₁, a γ = 1 := by
    intro γ hγ
    have hg : ι γ ∈ Γ := hΓ γ hγ
    have hqmp : Measure.QuasiMeasurePreserving
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) ν ν := by
      refine ⟨(hcont _).measurable, ?_⟩
      rw [ha γ]
      intro s hs
      rw [Measure.smul_apply, hs, smul_zero]
    obtain ⟨e, he⟩ : ∃ e : Γ.subgroupOf π.ker → Γ.subgroupOf π.ker,
        ∀ s, ((e s : π.ker) : P) = (ι γ)⁻¹ * ((s : π.ker) : P) * ι γ := by
      refine ⟨fun s => ⟨⟨(ι γ)⁻¹ * ((s : π.ker) : P) * ι γ, ?_⟩, ?_⟩, fun s => rfl⟩
      · rw [MonoidHom.mem_ker]
        simp [MonoidHom.mem_ker.1 (s : π.ker).2]
      · exact Subgroup.mem_subgroupOf.2
          (Γ.mul_mem (Γ.mul_mem (Γ.inv_mem hg) (Subgroup.mem_subgroupOf.1 s.2)) hg)
    have hebij : Function.Bijective e := by
      constructor
      · intro s t hst
        have h1 := congrArg (fun x : Γ.subgroupOf π.ker => ((x : π.ker) : P)) hst
        simp only [he, mul_left_inj, mul_right_inj] at h1
        apply Subtype.ext
        apply Subtype.ext
        exact h1
      · intro t
        obtain ⟨s, hs⟩ : ∃ s : Γ.subgroupOf π.ker,
            ((s : π.ker) : P) = ι γ * ((t : π.ker) : P) * (ι γ)⁻¹ := by
          refine ⟨⟨⟨ι γ * ((t : π.ker) : P) * (ι γ)⁻¹, ?_⟩, ?_⟩, rfl⟩
          · rw [MonoidHom.mem_ker]
            simp [MonoidHom.mem_ker.1 (t : π.ker).2]
          · exact Subgroup.mem_subgroupOf.2
              (Γ.mul_mem (Γ.mul_mem hg (Subgroup.mem_subgroupOf.1 t.2)) (Γ.inv_mem hg))
        refine ⟨s, Subtype.ext (Subtype.ext ?_)⟩
        rw [he, hs]
        group
    have hsemi : ∀ s : Γ.subgroupOf π.ker, Function.Semiconj
        (fun m : π.ker => MulAut.conjNormal (ι γ) m) (fun x => e s • x) (fun x => s • x) := by
      intro s x
      apply Subtype.ext
      simp only [MulAut.conjNormal_apply, Subgroup.smul_def, smul_eq_mul, Subgroup.coe_mul, he]
      group
    have hfd := hD.preimage_of_equiv hqmp hebij hsemi
    have hmeq : ν D = ν ((fun m : π.ker => MulAut.conjNormal (ι γ) m) ⁻¹' D) :=
      hD.measure_eq hfd
    apply hcancel
    rw [← hpre γ D hDm, ← hmeq, ENNReal.coe_one, one_mul]
  have hFc : Continuous (fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) := by
    apply continuous_induced_rng.2
    have h1 : (Subtype.val ∘ fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) =
        fun p => ι p.1 * (p.2 : P) * (ι p.1)⁻¹ := by
      funext p
      simp only [Function.comp_apply, MulAut.conjNormal_apply]
    rw [h1]
    exact ((hι.comp continuous_fst).mul (continuous_subtype_val.comp continuous_snd)).mul
      (hι.comp continuous_fst).inv
  have hE : MeasurableSet ((fun p : G₁ × π.ker => MulAut.conjNormal (ι p.1) p.2) ⁻¹' D) :=
    hFc.measurable hDm
  have ha_eq : a = fun u =>
      (ν ((fun m : π.ker => MulAut.conjNormal (ι u) m) ⁻¹' D) / ν D).toNNReal := by
    funext u
    rw [hpre u D hDm, ENNReal.mul_div_cancel_right hD0 hDtop.ne, ENNReal.toNNReal_coe]
  have hmeas : Measurable a := by
    rw [ha_eq]
    exact ((measurable_measure_prodMk_left hE).div_const _).ennreal_toNNReal
  exact ⟨{ toFun := a, map_one' := hΓ1 1 Γ₁.one_mem, map_mul' := hmul }, hmeas, hΓ1,
    fun u => ha u⟩

end GlobalTheory.CompanionTheory.SplitExtLat
