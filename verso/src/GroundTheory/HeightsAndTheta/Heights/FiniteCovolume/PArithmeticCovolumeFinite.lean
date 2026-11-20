import Mathlib
import GroundTheory.HeightsAndTheta.Heights.FiniteCovolume.Imports

namespace GroundTheory.Heights₂.Heights.FiniteCovolume

open NumberField GroundTheory.Automorphic Module Matrix Topology MeasureTheory
open scoped Pointwise ComplexOrder ENNReal

noncomputable section

variable {F E : Type*} [Field F] [Field E] [NumberField F] [NumberField E] [Algebra F E]
  [Algebra.IsQuadraticExtension F E] [IsTotallyReal F] [IsTotallyComplex E]
variable {W : Type*} [AddCommGroup W] [Module E W] {ι : Type*} [Fintype ι] [DecidableEq ι]

omit [NumberField F] [IsTotallyReal F] [IsTotallyComplex E] in

/- English proof (translation)
Establish `hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w` using `fun w => (Units.continuous_val.comp ((continuous_apply w).comp (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const`. Use `Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)` and prove the remaining obligations. Conclude with `(hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))`.
-/
theorem continuous_len_invApply {h : HermitianForm F E W} {v : Basis ι E W} (M : Majorant h v)
    (y : InfinitePlace E → ι → ℂ) : Continuous fun g : archUnitary h v => M.len (invApply g y) := by
  have hw : ∀ w, Continuous fun g : archUnitary h v => invApply g y w := fun w =>
    (Units.continuous_val.comp ((continuous_apply w).comp
      (continuous_subtype_val.comp continuous_inv))).matrix_mulVec continuous_const
  refine Real.continuous_sqrt.comp (continuous_finsetSum _ fun w _ => Complex.continuous_re.comp ?_)
  exact (hw w).star.dotProduct (continuous_const.matrix_mulVec (hw w))

/- English proof (translation)
Introduce `μ _ D La hLa`. Take `⟨M⟩` from `h₆`. Take `⟨r, a, ha, har⟩` from `h₅`. Establish `hdeg : finrank ℚ E = 2 * finrank ℚ F`. Rewrite using `[← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E, mul_comm]`.

Establish `ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧ ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r` using `⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩`. Use `set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀`. Use `set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV`. Establish `hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV`. Introduce `γ hγ x hx`.

Establish `hγ' : γ • La = La` using `MulAction.mem_stabilizer_iff.1 hγ`. Use `⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : γ • x ∈ γ • La` using `AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1`. Rewrite `h1` using `[hγ']`. Then use the resulting hypothesis. Rewrite using `[← hx.2.2.1]`.

Conclude with `HermitianForm.mem_unitaryGroup.1 γ.2 x x`. Rewrite using `[GaussianPlane.lineIndex_smul hγ']`. Conclude with `hx.2.2.2`. Take `⟨FD, hFD, hm⟩` from `h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩) hstable ⟨C₀, fun x hx => hx.2.2.2⟩`. Use `⟨FD, hFD, ?_⟩` and prove the remaining obligations.

Use `set B : Set (archUnitary h v) := ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB`. Establish `hBmeas : MeasurableSet B` using `(isOpen_iUnion fun x => isOpen_iUnion fun _ => isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet`. Establish `hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1`. Rewrite using `[Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]`. Use `lintegral_mono fun g => ?_` and prove the remaining obligations.

Distinguish the cases in `hg : g ∈ B`. Rewrite using `[Set.indicator_of_mem hg, Pi.one_apply]`. Take `⟨x₁, hx₁⟩` from `Set.mem_iUnion.1 hg`. Take `⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩` from `Set.mem_iUnion.1 hx₁`. Use `set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}`.

Establish `hSfin : S.Finite` using `(h₉ M La g 1 hLa.isLattice).inter_of_left _`. Take `⟨x, hxS, hxmin⟩` from `Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x))) hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩`. Take `⟨⟨hxLa, hxlt⟩, hx0⟩` from `hxS`. Establish `hshort : ∀ y ∈ La, y ≠ 0 → M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y))`. Introduce `y hy hy0`.

Distinguish the cases in `hylt : M.len (invApply g (vecAt v y)) < 1`. Conclude with `hxmin y ⟨⟨hy, hylt⟩, hy0⟩`. Conclude with `hxlt.le.trans (not_lt.1 hylt)`. Establish `hxVV : x ∈ VV`. Use `⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩` and prove the remaining obligations.

Conclude with `Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)`. Establish `hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty` using `⟨x, hxVV, hxlt⟩`. Unfold `countBelow`. Rewrite using `[← ENat.toENNReal_one, ENat.toENNReal_le]`. Conclude with `Set.one_le_encard_iff_nonempty.2 hne`.

Rewrite using `[Set.indicator_of_notMem hg]`. Conclude with `bot_le`. Take `⟨S, hS, K, hK, hMah⟩` from `h₂ M D 1 one_pos`. Establish `: DiscreteTopology (archLatticeGroup h v La)` using `h₈ La hLa.isLattice`. Establish `: Countable (archLatticeGroup h v La)` using `TopologicalSpace.separableSpace_iff_countable.1 inferInstance`.

Set `c : AddSubgroup W → h.unitaryGroup` to `fun L => if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1`. Use `set K' : Set (archUnitary h v) := ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'`. Establish `hK'c : IsCompact K'` using `hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)`. Establish `hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD`. Introduce and unpack `g ⟨hgFD, hgB⟩`.

Establish `hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x))`. Introduce `x hx hx0`. Assume the negation of the conclusion as `hlt`. Conclude with `hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)`. Take `⟨γ, hγS, hγK⟩` from `hMah La g hLa hlam`.

Establish `hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La` using `⟨γ, rfl⟩`. Establish `hcL : c (γ • La) • La = γ • La`. Simplify using `only [c, dif_pos hL]`. Conclude with `hL.choose_spec`. Establish `hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La`.

Express the relevant statement in the definitionally equal form `(γ⁻¹ * c (γ • La)) • La = La`. Rewrite using `[mul_smul, hcL, inv_smul_smul]`. Use `Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩, ?_, hgFD⟩` and prove the remaining obligations. Use `Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g), Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul]`.

Simplify using `only [map_mul, map_inv]`. Use `group`. Establish `hAlt : μ (FD ∩ Bᶜ) < ⊤`. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
theorem ArithmeticCovolumeFinite.proof (h : HermitianForm F E W) (v : Basis ι E W)
    (h₁ : ScalingLaw.Statement h v) (h₂ : MahlerCompactness.Statement h v)
    (h₃ : ShortVectorIsotropic.Statement h v) (h₄ : ShortestVectorIndex.Statement h v)
    (h₅ : IntegralFamilyBound.Statement E) (h₆ : MajorantExists.Statement h v)
    (h₈ : ArchLatticeDiscrete.Statement h v) (h₉ : LatticePointsBelowFinite.Statement h v) :
    ArithmeticCovolumeFinite.Statement h v := by
  classical
  intro μ _ D La hLa
  obtain ⟨M⟩ := h₆

  obtain ⟨r, a, ha, har⟩ := h₅
  have hdeg : finrank ℚ E = 2 * finrank ℚ F := by
    rw [← Module.finrank_mul_finrank ℚ F E, Algebra.IsQuadraticExtension.finrank_eq_two F E,
      mul_comm]
  have ha' : ∃ b : Fin (2 * finrank ℚ F) → 𝓞 E, LinearIndependent ℚ (fun i => (b i : E)) ∧
      ∀ i (σ : E →+* ℂ), ‖σ (b i)‖ ≤ r :=
    ⟨a ∘ Fin.cast hdeg.symm, ha.comp _ (Fin.cast_injective _), fun i σ => har _ σ⟩
  set C₀ : ℕ := ⌊(r * Real.sqrt (2 * finrank ℚ F)) ^ (2 * finrank ℚ F)⌋₊ with hC₀

  set VV : Set W := {x | x ∈ La ∧ x ≠ 0 ∧ h.toSesq x x = 0 ∧ lineIndex E La x ≤ C₀} with hVV
  have hstable : ∀ γ ∈ latticeStab h La, ∀ x ∈ VV, γ • x ∈ VV := by
    intro γ hγ x hx
    have hγ' : γ • La = La := MulAction.mem_stabilizer_iff.1 hγ
    refine ⟨?_, fun h0 => hx.2.1 ((smul_eq_zero_iff_eq γ).1 h0), ?_, ?_⟩
    · have h1 : γ • x ∈ γ • La := AddSubgroup.smul_mem_pointwise_smul _ _ _ hx.1
      rwa [hγ'] at h1
    · rw [← hx.2.2.1]
      exact HermitianForm.mem_unitaryGroup.1 γ.2 x x
    · rw [GaussianPlane.lineIndex_smul hγ']
      exact hx.2.2.2
  obtain ⟨FD, hFD, hm⟩ := h₁ M μ D La VV hLa (fun x hx => hx.1) (fun x hx => ⟨hx.2.1, hx.2.2.1⟩)
    hstable ⟨C₀, fun x hx => hx.2.2.2⟩
  refine ⟨FD, hFD, ?_⟩

  set B : Set (archUnitary h v) :=
    ⋃ x : W, ⋃ (_ : x ∈ La ∧ x ≠ 0), {g | M.len (invApply g (vecAt v x)) < 1} with hB
  have hBmeas : MeasurableSet B :=
    (isOpen_iUnion fun x => isOpen_iUnion fun _ =>
      isOpen_lt (continuous_len_invApply M _) continuous_const).measurableSet
  have hBle : μ (FD ∩ B) ≤ massBelow M μ FD VV 1 := by
    rw [Set.inter_comm, ← Measure.restrict_apply hBmeas, ← lintegral_indicator_one hBmeas]
    refine lintegral_mono fun g => ?_
    by_cases hg : g ∈ B
    · rw [Set.indicator_of_mem hg, Pi.one_apply]
      obtain ⟨x₁, hx₁⟩ := Set.mem_iUnion.1 hg
      obtain ⟨⟨hx₁La, hx₁0⟩, hx₁lt⟩ := Set.mem_iUnion.1 hx₁
      set S : Set W := {x | x ∈ La ∧ M.len (invApply g (vecAt v x)) < 1} ∩ {x | x ≠ 0}
      have hSfin : S.Finite := (h₉ M La g 1 hLa.isLattice).inter_of_left _
      obtain ⟨x, hxS, hxmin⟩ := Set.exists_min_image S (fun x => M.len (invApply g (vecAt v x)))
        hSfin ⟨x₁, ⟨hx₁La, hx₁lt⟩, hx₁0⟩
      obtain ⟨⟨hxLa, hxlt⟩, hx0⟩ := hxS
      have hshort : ∀ y ∈ La, y ≠ 0 →
          M.len (invApply g (vecAt v x)) ≤ M.len (invApply g (vecAt v y)) := by
        intro y hy hy0
        by_cases hylt : M.len (invApply g (vecAt v y)) < 1
        · exact hxmin y ⟨⟨hy, hylt⟩, hy0⟩
        · exact hxlt.le.trans (not_lt.1 hylt)
      have hxVV : x ∈ VV := by
        refine ⟨hxLa, hx0, h₃ M D La g x hLa hxLa hxlt, ?_⟩
        exact Nat.le_floor (h₄ M r ha' D La g x hLa hxLa hx0 hshort)
      have hne : ({y ∈ VV | M.len (invApply g (vecAt v y)) < 1}).Nonempty := ⟨x, hxVV, hxlt⟩
      unfold countBelow
      rw [← ENat.toENNReal_one, ENat.toENNReal_le]
      exact Set.one_le_encard_iff_nonempty.2 hne
    · rw [Set.indicator_of_notMem hg]
      exact bot_le

  obtain ⟨S, hS, K, hK, hMah⟩ := h₂ M D 1 one_pos
  have : DiscreteTopology (archLatticeGroup h v La) := h₈ La hLa.isLattice
  have : Countable (archLatticeGroup h v La) :=
    TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  let c : AddSubgroup W → h.unitaryGroup := fun L =>
    if hL : ∃ γ : h.unitaryGroup, γ • La = L then hL.choose else 1
  set K' : Set (archUnitary h v) :=
    ⋃ L ∈ S, (fun k => (archEmbed h v (c L))⁻¹ * k) '' K with hK'
  have hK'c : IsCompact K' :=
    hS.isCompact_biUnion fun L _ => hK.image (continuous_const.mul continuous_id)
  have hcover : FD ∩ Bᶜ ⊆ ⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD := by
    rintro g ⟨hgFD, hgB⟩
    have hlam : ∀ x ∈ La, x ≠ 0 → (1 : ℝ) ≤ M.len (invApply g (vecAt v x)) := by
      intro x hx hx0
      by_contra hlt
      exact hgB (Set.mem_iUnion.2 ⟨x, Set.mem_iUnion.2 ⟨⟨hx, hx0⟩, not_le.1 hlt⟩⟩)
    obtain ⟨γ, hγS, hγK⟩ := hMah La g hLa hlam
    have hL : ∃ γ' : h.unitaryGroup, γ' • La = γ • La := ⟨γ, rfl⟩
    have hcL : c (γ • La) • La = γ • La := by
      simp only [c, dif_pos hL]
      exact hL.choose_spec
    have hstab : γ⁻¹ * c (γ • La) ∈ latticeStab h La := by
      change (γ⁻¹ * c (γ • La)) • La = La
      rw [mul_smul, hcL, inv_smul_smul]
    refine Set.mem_iUnion.2 ⟨⟨archEmbed h v (γ⁻¹ * c (γ • La)), Subgroup.mem_map_of_mem _ hstab⟩,
      ?_, hgFD⟩
    refine Set.mem_smul_set.2 ⟨(archEmbed h v (c (γ • La)))⁻¹ * (archEmbed h v γ * g),
      Set.mem_biUnion hγS ⟨_, hγK, rfl⟩, ?_⟩
    rw [Subgroup.smul_def, smul_eq_mul]
    simp only [map_mul, map_inv]
    group
  have hAlt : μ (FD ∩ Bᶜ) < ⊤ := by
    calc μ (FD ∩ Bᶜ) ≤ μ (⋃ δ : archLatticeGroup h v La, δ • K' ∩ FD) := measure_mono hcover
      _ ≤ ∑' δ : archLatticeGroup h v La, μ (δ • K' ∩ FD) := measure_iUnion_le _
      _ = μ K' := (hFD.measure_eq_tsum K').symm
      _ < ⊤ := hK'c.measure_lt_top
  calc μ FD = μ ((FD ∩ B) ∪ (FD ∩ Bᶜ)) := by rw [Set.inter_union_compl]
    _ ≤ μ (FD ∩ B) + μ (FD ∩ Bᶜ) := measure_union_le _ _
    _ < ⊤ := ENNReal.add_lt_top.2 ⟨hBle.trans_lt (hm 1 one_pos).1, hAlt⟩

end

end GroundTheory.Heights₂.Heights.FiniteCovolume
