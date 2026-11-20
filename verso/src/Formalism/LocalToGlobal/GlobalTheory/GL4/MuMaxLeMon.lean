import Formalism.LocalToGlobal.Columns.MultiFactorialEqTripleProd

open NumberField IsDedekindDomain Module MvPolynomial
open scoped Matrix ComplexOrder

noncomputable section

namespace Formalism.L2.GlobalTheoryTheory.TraceIntegrality

open Formalism.BasicNotions Formalism.L2.DIV Formalism.L2.GlobalTheoryTheory.HLatOps Formalism.HermitianLatticesTheory Formalism.HN Formalism.L2.Forms Formalism.L2.Col

section Gen

variable (K : Type) [Field K] [NumberField K] [StarRing K] [IsTotallyComplex K] {ι : Type} [Fintype ι] {n : ℕ} (lam : ι → DomWeight n)

/- English proof (translation)
Establish `hX' : ∀ v : InfinitePlace K, IsUnit ((fun _ : InfinitePlace K => (monD lam)⁻¹) v).det` using `fun v => (Matrix.isUnit_nonsing_inv_det_iff).mpr (monD_det lam)`. Establish `hφ0 : φ ≠ 0`. Introduce and unpack `rfl`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `y hy`. Take `⟨x, -, rfl⟩` from `Submodule.mem_map.mp hy`. Simplify using the standard rewrite rules. Take `⟨L0, hL0⟩ : ∃ L0 : Submodule (𝓞 K) (MonI lam → K), L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K))` from `⟨_, rfl⟩`. Establish `hmemL0 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) ∈ L0` using `fun m => by`.

Rewrite using `[hL0]`. Conclude with `Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem (Finset.mem_univ m) (Submodule.mem_span_singleton_self _))`. Establish `hmapT : N.map (φ.restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0`. Introduce `y hy`. Take `⟨x, hx, rfl⟩` from `Submodule.mem_map.mp hy`.

Establish `hdec : φ x = ∑ m, (φ x m) • (Pi.single m (1 : K) : MonI lam → K)`. Use extensionality with `m'`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Use `show φ x ∈ _`. Rewrite using `[hdec]`.

Conclude with `Submodule.sum_mem _ fun m _ => Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul (hint x hx m) (hmemL0 m)`. Establish `horth : ∀ s t : MonI lam, s ≠ t → Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single s (1 : K) : MonI lam → K)) (𝓞 K ∙ (Pi.single t (1 : K) : MonI lam → K))`. Introduce `s t hst v x hx y hy`. Take `⟨r, rfl⟩` from `Submodule.mem_span_singleton.mp hx`. Take `⟨r', rfl⟩` from `Submodule.mem_span_singleton.mp hy`.

Simplify using `only [majAt, monH_fcoord]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `m _`. Distinguish the cases in `hm : m = s`. Substitute `hm` using the available equality.

Simplify using `[Pi.single_apply, hst]`. Simplify using `[Pi.single_apply, hm]`. Establish `hline : ∀ m, muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) ≤ -Real.log c0`. Introduce `m`. Use `max_slope_line_neg_log _ _ hX' _ ?_ c0 hc0 fun v => ?_` and prove the remaining obligations.

Simplify using the standard rewrite rules. Rewrite using `[monH_norm, Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]`. Simplify using `using hc m`. Establish `hmain` using `Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' (fun m => 𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) (fun m => Submodule.fg_span_singleton _) horth Finset.univ`. Rewrite `hmain` using `[← hL0]`.

Establish `hL0ne : L0 ≠ ⊥`. Introduce `h`. Apply `hne` to reduce the goal to its premises. Rewrite using `[eq_bot_iff]`. Introduce `y hy`.

Take `⟨x, -, rfl⟩` from `Submodule.mem_map.mp hy`. Establish `h1 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) = 0` using `fun m => by`. Use `hmemL0 m` as an intermediate fact. Rewrite `this` using `[h, Submodule.mem_bot]`. Then use the resulting hypothesis. Rewrite using `[Submodule.mem_bot]`.

Use function extensionality and compare the values at `m`. Conclude with `absurd (h1 m) (by simp)`. Establish `hL0mu : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) L0 ≤ -Real.log c0`. Establish `h2` using `hmain.2.2.2 ((-Real.log c0 - slopeNormalisingConstant K) / 2) (fun m _ _ => by`. Use `hline m` as an intermediate fact.

Rewrite `this` using `[frameB_muMaxDef]`. Use the proof step `linarith) hL0ne`. Rewrite using `[frameB_muMaxDef]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hT` using `Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' hmain.1 hL0ne hI0`.

Establish `hS` using `((Formalism.HN.slopeIneqMean K V κ (MonI lam → K) (MonI lam) b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' φ N hN hne).2 (idealSmul (I : Submodule (𝓞 K) K) L0) (Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg I hmain.1) hmapT).2 …`. Establish `hht : htMap b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) φ ≤ 1 / (nPl K : ℝ) * ∑ v, Real.log (B v)`. Unfold `htMap`. Apply `mul_le_mul_of_nonneg_left _ (by positivity)` to reduce the goal to its premises. Apply `Finset.sum_le_sum` to reduce the goal to its premises.

Introduce `v _`. Establish `hpos` using `Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' v φ hφ0`. Establish `hle : opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ≤ √(B v)`. Apply `Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X _ _ hX φ v _ (Real.sqrt_nonneg _)` to reduce the goal to its premises. Introduce `f`.

Establish `h0 : 0 ≤ normAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v (φ f)` using `Real.sqrt_nonneg _`. Establish `h1 : 0 ≤ normAt b X v f` using `Real.sqrt_nonneg _`. Use `Real.sqrt_le_sqrt (hnorm v f)` as an intermediate fact. Rewrite `this` using `[Real.sqrt_sq h0, Real.sqrt_mul (hB v).le, Real.sqrt_sq h1]`. Then use the resulting hypothesis. Apply `Real.log_le_log (by positivity)` to reduce the goal to its premises.

Combine the equalities or inequalities in the displayed calculation. Combine the linear relations using `[hS, hT, hL0mu, hht]`.
-/
theorem muMax_le_mon {V κ : Type} [AddCommGroup V] [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] [Fintype κ] [DecidableEq κ]
    (b : Basis κ K V) (X : InfinitePlace K → Matrix κ κ ℂ) (hX : ∀ v, IsUnit (X v).det)
    (N : Submodule (𝓞 K) V) (hN : N.FG) (φ : V →ₗ[K] (MonI lam → K)) (hinj : Set.InjOn φ N)
    (hne : N.map (φ.restrictScalars (𝓞 K)) ≠ ⊥)
    (I : FractionalIdeal (nonZeroDivisors (𝓞 K)) K) (hI0 : I ≠ 0)
    (hint : ∀ x ∈ N, ∀ m, φ x m ∈ (I : Submodule (𝓞 K) K))
    (B : InfinitePlace K → ℝ) (hB : ∀ v, 0 < B v)
    (hnorm : ∀ v x, normAt (Pi.basisFun K (MonI lam)) (fun _ => (monD lam)⁻¹) v (φ x) ^ 2 ≤ B v * normAt b X v x ^ 2)
    (c0 : ℝ) (hc0 : 0 < c0) (hc : ∀ m, c0 ≤ monW lam m) :
    muMaxDef b X N ≤ -Real.log c0 - 2 * Real.log (FractionalIdeal.absNorm I : ℝ) / (Module.finrank ℚ K : ℝ)
      + (1 / (nPl K : ℝ)) * ∑ v, Real.log (B v) := by
  have hX' : ∀ v : InfinitePlace K, IsUnit ((fun _ : InfinitePlace K => (monD lam)⁻¹) v).det :=
    fun v => (Matrix.isUnit_nonsing_inv_det_iff).mpr (monD_det lam)
  have hφ0 : φ ≠ 0 := by
    rintro rfl
    apply hne
    rw [eq_bot_iff]
    rintro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    simp
  obtain ⟨L0, hL0⟩ : ∃ L0 : Submodule (𝓞 K) (MonI lam → K),
      L0 = ⨆ m ∈ (Finset.univ : Finset (MonI lam)), (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) := ⟨_, rfl⟩
  have hmemL0 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) ∈ L0 := fun m => by
    rw [hL0]
    exact Submodule.mem_iSup_of_mem m (Submodule.mem_iSup_of_mem (Finset.mem_univ m)
      (Submodule.mem_span_singleton_self _))
  have hmapT : N.map (φ.restrictScalars (𝓞 K)) ≤ idealSmul (I : Submodule (𝓞 K) K) L0 := by
    intro y hy
    obtain ⟨x, hx, rfl⟩ := Submodule.mem_map.mp hy
    have hdec : φ x = ∑ m, (φ x m) • (Pi.single m (1 : K) : MonI lam → K) := by
      ext m'
      simp [Finset.sum_apply, Pi.single_apply]
    show φ x ∈ _
    rw [hdec]
    exact Submodule.sum_mem _ fun m _ => Formalism.LFunctionChainParameters.slopeLatticeData.mem_idealSmul (hint x hx m) (hmemL0 m)
  have horth : ∀ s t : MonI lam, s ≠ t → Formalism.BranchingDeterminantCap.OrthAt (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) (𝓞 K ∙ (Pi.single s (1 : K) : MonI lam → K))
      (𝓞 K ∙ (Pi.single t (1 : K) : MonI lam → K)) := by
    intro s t hst v x hx y hy
    obtain ⟨r, rfl⟩ := Submodule.mem_span_singleton.mp hx
    obtain ⟨r', rfl⟩ := Submodule.mem_span_singleton.mp hy
    simp only [majAt, monH_fcoord]
    apply Finset.sum_eq_zero
    intro m _
    by_cases hm : m = s
    · subst hm
      simp [Pi.single_apply, hst]
    · simp [Pi.single_apply, hm]
  have hline : ∀ m, muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹)
      (𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) ≤ -Real.log c0 := by
    intro m
    refine max_slope_line_neg_log _ _ hX' _ ?_ c0 hc0 fun v => ?_
    · simp
    · rw [monH_norm, Finset.sum_eq_single m (fun b _ hb => by simp [Pi.single_apply, hb]) (by simp)]
      simpa using hc m
  have hmain := Formalism.BranchingDeterminantCap.OrthogonalSumAlt.main (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) hX'
    (fun m => 𝓞 K ∙ (Pi.single m (1 : K) : MonI lam → K)) (fun m => Submodule.fg_span_singleton _) horth
    Finset.univ
  rw [← hL0] at hmain
  have hL0ne : L0 ≠ ⊥ := by
    intro h
    apply hne
    rw [eq_bot_iff]
    intro y hy
    obtain ⟨x, -, rfl⟩ := Submodule.mem_map.mp hy
    have h1 : ∀ m, (Pi.single m (1 : K) : MonI lam → K) = 0 := fun m => by
      have := hmemL0 m
      rwa [h, Submodule.mem_bot] at this
    rw [Submodule.mem_bot]
    funext m
    exact absurd (h1 m) (by simp)
  have hL0mu : muMaxDef (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) L0 ≤ -Real.log c0 := by
    have h2 := hmain.2.2.2 ((-Real.log c0 - slopeNormalisingConstant K) / 2) (fun m _ _ => by
      have := hline m
      rw [frameB_muMaxDef] at this
      linarith) hL0ne
    rw [frameB_muMaxDef]
    linarith
  have hT := Formalism.LFunctionChainParameters.slopeLatticeData.muMaxDef_fractional_le (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX' hmain.1 hL0ne hI0
  have hS := ((Formalism.HN.slopeIneqMean K V κ (MonI lam → K) (MonI lam) b X (Pi.basisFun K (MonI lam))
    (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' φ N hN hne).2 (idealSmul (I : Submodule (𝓞 K) K) L0)
    (Formalism.LFunctionChainParameters.slopeLatticeData.idealSmul_fg I hmain.1) hmapT).2 hinj
  have hht : htMap b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) φ ≤
      1 / (nPl K : ℝ) * ∑ v, Real.log (B v) := by
    unfold htMap
    apply mul_le_mul_of_nonneg_left _ (by positivity)
    apply Finset.sum_le_sum
    intro v _
    have hpos := Formalism.HN.PlaceOperatorNorms.opNormAt_pos b X (Pi.basisFun K (MonI lam))
      (fun _ : InfinitePlace K => (monD lam)⁻¹) hX hX' v φ hφ0
    have hle : opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ≤ √(B v) := by
      apply Formalism.L2.Geo.ExtensionFiltration.opNormAt_le_of_points b X _ _ hX φ v _ (Real.sqrt_nonneg _)
      intro f
      have h0 : 0 ≤ normAt (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v (φ f) :=
        Real.sqrt_nonneg _
      have h1 : 0 ≤ normAt b X v f := Real.sqrt_nonneg _
      have := Real.sqrt_le_sqrt (hnorm v f)
      rwa [Real.sqrt_sq h0, Real.sqrt_mul (hB v).le, Real.sqrt_sq h1] at this
    apply Real.log_le_log (by positivity)
    calc opNormAt b X (Pi.basisFun K (MonI lam)) (fun _ : InfinitePlace K => (monD lam)⁻¹) v φ ^ 2
        ≤ √(B v) ^ 2 := pow_le_pow_left₀ hpos.le hle 2
      _ = B v := Real.sq_sqrt (hB v).le
  linarith [hS, hT, hL0mu, hht]

end Gen

end Formalism.L2.GlobalTheoryTheory.TraceIntegrality

end
