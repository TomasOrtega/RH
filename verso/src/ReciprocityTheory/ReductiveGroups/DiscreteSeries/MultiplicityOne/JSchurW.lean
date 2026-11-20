import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StSchurW
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JDichoWA
import Formalism.SharpRestriction.CuspSpanNormBounds.BridgeCSchur

noncomputable section

open MeasureTheory Matrix
open scoped InnerProductSpace ENNReal ComplexConjugate

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2

namespace SchurWAux

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_ne (0 : H)`. Use `set b := stdOrthonormalBasis ℂ H`. Establish `hpt : ∀ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ)`. Introduce `g`. Establish `e1 : ∀ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ⟪ρ g v, b i⟫_ℂ * ⟪b i, ρ g v⟫_ℂ`.

Introduce `i`. Rewrite using `[mul_comm]`. Use `congr 1`. Conclude with `inner_conj_symm _ _`. Repeatedly rewrite using `[e1]`.

Rewrite using `[b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, hiso]`. Use `push_cast`. Both sides reduce to the same expression. Establish `hbi : ∀ i, ⟪b i, b i⟫_ℂ = 1`. Introduce `i`.

Rewrite using `[inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]`. Simplify using the standard rewrite rules. Establish `hL : ∫ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ)`. Repeatedly rewrite using `[hpt]`. Simplify using the standard rewrite rules.

Rewrite `hL` using `[integral_finset_sum _ (fun i _ => (h v (b i) v (b i)).1)]`. Establish `e2 : ∀ i, ∫ g, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) / (d : ℂ)`. Introduce `i`. Rewrite using `[(h v (b i) v (b i)).2, hbi, mul_one, inner_self_eq_norm_sq_to_K]`. Use `push_cast`.

Both sides reduce to the same expression. Rewrite `hL` using `[e2]`. Rewrite `hL` using `[Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]`. Establish `hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0`. Establish `: 0 < ‖v‖` using `norm_pos_iff.mpr hv`.

Conclude with `(pow_pos this 2).ne'` after adjusting the coercions. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Rewrite `hL` using `[mul_div_assoc', div_eq_iff hd']`. Conclude with `(mul_right_cancel₀ hv2 (by rw [hL]; ring)).symm`.
-/
theorem fdeg_eq_finrank {G : Type*} [MeasurableSpace G] (μ : Measure G) [IsProbabilityMeasure μ]
    {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℂ H] [FiniteDimensional ℂ H] [Nontrivial H]
    (ρ : G → (H →L[ℂ] H)) (hiso : ∀ g v, ‖ρ g v‖ = ‖v‖) (d : ℝ) (hd : 0 < d)
    (h : ∀ v w v' w' : H, Integrable (fun g => ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ) μ ∧
      ∫ g, ⟪w, ρ g v⟫_ℂ * star ⟪w', ρ g v'⟫_ℂ ∂μ = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ)) :
    (d : ℂ) = (Module.finrank ℂ H : ℂ) := by
  obtain ⟨v, hv⟩ := exists_ne (0 : H)
  set b := stdOrthonormalBasis ℂ H
  have hpt : ∀ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    intro g
    have e1 : ∀ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ = ⟪ρ g v, b i⟫_ℂ * ⟪b i, ρ g v⟫_ℂ := by
      intro i
      rw [mul_comm]
      congr 1
      exact inner_conj_symm _ _
    simp_rw [e1]
    rw [b.sum_inner_mul_inner, inner_self_eq_norm_sq_to_K, hiso]
    push_cast
    rfl
  have hbi : ∀ i, ⟪b i, b i⟫_ℂ = 1 := by
    intro i
    rw [inner_self_eq_norm_sq_to_K, b.orthonormal.1 i]
    simp
  have hL : ∫ g, ∑ i, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) := by
    simp_rw [hpt]
    simp
  rw [integral_finset_sum _ (fun i _ => (h v (b i) v (b i)).1)] at hL
  have e2 : ∀ i, ∫ g, ⟪b i, ρ g v⟫_ℂ * star ⟪b i, ρ g v⟫_ℂ ∂μ = ((‖v‖ ^ 2 : ℝ) : ℂ) / (d : ℂ) := by
    intro i
    rw [(h v (b i) v (b i)).2, hbi, mul_one, inner_self_eq_norm_sq_to_K]
    push_cast
    rfl
  simp_rw [e2] at hL
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hL
  have hv2 : ((‖v‖ ^ 2 : ℝ) : ℂ) ≠ 0 := by
    have : 0 < ‖v‖ := norm_pos_iff.mpr hv
    exact_mod_cast (pow_pos this 2).ne'
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  rw [mul_div_assoc', div_eq_iff hd'] at hL
  exact (mul_right_cancel₀ hv2 (by rw [hL]; ring)).symm

end SchurWAux

/- English proof (translation)
Take `⟨hB2, -⟩` from `h`. Take `⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCpt, -, -, -, hHI, -, -, -, hCW, -⟩` from `hB2`. Introduce `k r Wp _ _ _ D hD v w v' w'`. Break down `subsingleton_or_nontrivial Wp with hW | hW` into its components or cases. Rewrite using `[Subsingleton.elim w 0]`.

Simplify using the standard rewrite rules. Establish `hU : IsClosedSubgroup (UWset k r D.z)` using `hCW k r D.z`. Establish `hμ` using `D.haarW`. Establish `: CompleteSpace Wp` using `FiniteDimensional.complete ℂ Wp`. Set `μ : Measure (MatrixSubsetMeasurability.SG hU)` to `MatrixSubsetMeasurability.nu hU D.μW`.

Establish `: μ.IsMulLeftInvariant` using `MatrixSubsetMeasurability.nu_left hμ`. Establish `: μ.IsInvInvariant` using `MatrixSubsetMeasurability.nu_inv hHI hμ`. Establish `hE` using `MatrixSubsetMeasurability.me_val hU`. Establish `hcpt : IsCompact (Set.univ : Set (MatrixSubsetMeasurability.SG hU))`. Establish `hind : Topology.IsInducing (fun g : MatrixSubsetMeasurability.SG hU => g.1)` using `Topology.IsInducing.subtypeVal`.

Establish `hr : Set.range (fun g : MatrixSubsetMeasurability.SG hU => g.1) = {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z}` using `Subtype.range_coe_subtype`. Rewrite using `[hind.isCompact_iff, Set.image_univ, hr]`. Conclude with `hCpt k r D.z D.z_mem D.T_pos`. Establish `hν1 : μ Set.univ = 1`. Establish `e : ((MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1)) Set.univ = D.μW Set.univ`.

Rewrite using `[MatrixSubsetMeasurability.map_nu hμ]`. Rewrite `e` using `[Measure.map_apply hE.measurable MeasurableSet.univ, Set.preimage_univ]`. Conclude with `e.trans hD.mass`. Establish `: IsProbabilityMeasure μ` using `⟨hν1⟩`. Establish `: μ.IsOpenPosMeasure` using `isOpenPosMeasure_of_mulLeftInvariant_of_compact _ hcpt (by rw [hν1]; exact one_ne_zero)`.

Set `ρ : MatrixSubsetMeasurability.SG hU → (Wp →L[ℂ] Wp)` to `fun g => D.π (MatrixSubsetMeasurability.mat g)`. Establish `h1 : ρ 1 = 1` using `D.π_rep.1`. Establish `hρm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b)` using `fun a b => D.π_rep.2 _ a.2 _ b.2`. Establish `hiso : ∀ g v, ‖ρ g v‖ = ‖v‖` using `fun g v => D.π_unitary _ g.2 v`. Establish `hcont : ∀ v, Continuous fun g => ρ g v` using `fun v => (D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat MatrixSubsetMeasurability.mat_mem).clm_apply continuous_const`.

Establish `hsq : ∀ v w : Wp, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ`. Introduce `v w`. Use `MemLp.of_bound (continuous_const.inner (hcont v)).aestronglyMeasurable (‖w‖ * ‖v‖) (ae_of_all _ fun g => ?_)` and prove the remaining obligations. Conclude with `(norm_inner_le_norm _ _).trans (le_of_eq (by rw [hiso]))`. Establish `hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤` using `fun S hS hst => hD.irr S hS fun g hg v hv => hst (MatrixSubsetMeasurability.mk hU g hg) v hv`.

Establish `hSq : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ` using `⟨h1, hρm, hiso, hcont, hsq⟩`. Take `⟨d, hd, hrel⟩` from `Formalism.MainNotions.BridgeCSchur.schur_orth hSq hirr`. Establish `hdn` using `SchurWAux.fdeg_eq_finrank μ ρ hiso d hd hrel`. Rewrite using `[← MatrixSubsetMeasurability.map_nu (hU := hU) hμ, hE.integral_map, ← hdn]`. Conclude with `(hrel v w v' w').2`.
-/
theorem stSchurW (h : UnitaryGroupStructuralFacts) : StSchurW := by
  obtain ⟨hB2, -⟩ := h
  obtain ⟨-, -, -, -, -, -, -, -, -, -, -, -, -, hCpt, -, -, -, hHI, -, -, -, hCW, -⟩ := hB2
  intro k r Wp _ _ _ D hD v w v' w'
  rcases subsingleton_or_nontrivial Wp with hW | hW
  · rw [Subsingleton.elim w 0]
    simp
  have hU : IsClosedSubgroup (UWset k r D.z) := hCW k r D.z
  have hμ := D.haarW
  have : CompleteSpace Wp := FiniteDimensional.complete ℂ Wp
  let μ : Measure (MatrixSubsetMeasurability.SG hU) := MatrixSubsetMeasurability.nu hU D.μW
  have : μ.IsMulLeftInvariant := MatrixSubsetMeasurability.nu_left hμ
  have : μ.IsInvInvariant := MatrixSubsetMeasurability.nu_inv hHI hμ
  have hE := MatrixSubsetMeasurability.me_val hU
  have hcpt : IsCompact (Set.univ : Set (MatrixSubsetMeasurability.SG hU)) := by
    have hind : Topology.IsInducing (fun g : MatrixSubsetMeasurability.SG hU => g.1) := Topology.IsInducing.subtypeVal
    have hr : Set.range (fun g : MatrixSubsetMeasurability.SG hU => g.1) = {x : Mt k r | (Matrix.of x : Mat k r) ∈ UWset k r D.z} :=
      Subtype.range_coe_subtype
    rw [hind.isCompact_iff, Set.image_univ, hr]
    exact hCpt k r D.z D.z_mem D.T_pos
  have hν1 : μ Set.univ = 1 := by
    have e : ((MatrixSubsetMeasurability.nu hU D.μW).map (fun g : MatrixSubsetMeasurability.SG hU => g.1)) Set.univ = D.μW Set.univ := by
      rw [MatrixSubsetMeasurability.map_nu hμ]
    rw [Measure.map_apply hE.measurable MeasurableSet.univ, Set.preimage_univ] at e
    exact e.trans hD.mass
  have : IsProbabilityMeasure μ := ⟨hν1⟩
  have : μ.IsOpenPosMeasure :=
    isOpenPosMeasure_of_mulLeftInvariant_of_compact _ hcpt (by rw [hν1]; exact one_ne_zero)
  let ρ : MatrixSubsetMeasurability.SG hU → (Wp →L[ℂ] Wp) := fun g => D.π (MatrixSubsetMeasurability.mat g)
  have h1 : ρ 1 = 1 := D.π_rep.1
  have hρm : ∀ a b, ρ (a * b) = (ρ a).comp (ρ b) := fun a b => D.π_rep.2 _ a.2 _ b.2
  have hiso : ∀ g v, ‖ρ g v‖ = ‖v‖ := fun g v => D.π_unitary _ g.2 v
  have hcont : ∀ v, Continuous fun g => ρ g v := fun v =>
    (D.π_cont.comp_continuous MatrixSubsetMeasurability.continuous_mat MatrixSubsetMeasurability.mat_mem).clm_apply continuous_const
  have hsq : ∀ v w : Wp, MemLp (fun g => ⟪w, ρ g v⟫_ℂ) 2 μ := by
    intro v w
    refine MemLp.of_bound (continuous_const.inner (hcont v)).aestronglyMeasurable (‖w‖ * ‖v‖)
      (ae_of_all _ fun g => ?_)
    exact (norm_inner_le_norm _ _).trans (le_of_eq (by rw [hiso]))
  have hirr : ∀ S : Submodule ℂ Wp, IsClosed (S : Set Wp) → (∀ g, ∀ v ∈ S, ρ g v ∈ S) → S = ⊥ ∨ S = ⊤ :=
    fun S hS hst => hD.irr S hS fun g hg v hv => hst (MatrixSubsetMeasurability.mk hU g hg) v hv
  have hSq : Formalism.MainNotions.BridgeCSchur.SqRep μ ρ := ⟨h1, hρm, hiso, hcont, hsq⟩
  obtain ⟨d, hd, hrel⟩ := Formalism.MainNotions.BridgeCSchur.schur_orth hSq hirr
  have hdn := SchurWAux.fdeg_eq_finrank μ ρ hiso d hd hrel
  rw [← MatrixSubsetMeasurability.map_nu (hU := hU) hμ, hE.integral_map, ← hdn]
  exact (hrel v w v' w').2

end ReciprocityTheory.ChartRestriction.DS.Mult1
