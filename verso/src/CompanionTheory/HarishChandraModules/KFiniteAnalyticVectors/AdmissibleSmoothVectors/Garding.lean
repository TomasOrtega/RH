import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingAvg
import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.GardingBump
import GroundTheory.AutomorphicForms.GKModules.ParametricIntegral

open MeasureTheory Matrix Topology Set Filter
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace Gard

/- English proof (translation)
Use `GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a)) (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp` and prove the remaining obligations. Establish `h : Continuous fun p : P × α => (p.1, q p.2)` using `continuous_fst.prodMk (hq.comp continuous_snd)`. Conclude with `(continuous_iter_partial Φ hΦ k).comp h`.
-/
theorem contDiff_integral_comp {P Q E α : Type*} [NormedAddCommGroup P] [NormedSpace ℝ P] [FiniteDimensional ℝ P]
    [NormedAddCommGroup Q] [NormedSpace ℝ Q] [NormedAddCommGroup E] [NormedSpace ℝ E] [CompleteSpace E]
    [TopologicalSpace α] [T2Space α] [SecondCountableTopology α] [MeasurableSpace α] [OpensMeasurableSpace α]
    (μ : Measure α) [IsFiniteMeasureOnCompacts μ] (Φ : P × Q → E) (hΦ : ContDiff ℝ ∞ Φ) (q : α → Q)
    (hq : Continuous q)
    (hsupp : ∀ y₀ : P, ∃ U ∈ 𝓝 y₀, ∃ C : Set α, IsCompact C ∧ ∀ y ∈ U, ∀ a ∉ C, Φ (y, q a) = 0) :
    ContDiff ℝ ∞ fun y => ∫ a, Φ (y, q a) ∂μ := by
  refine GroundTheory.Automorphic.contDiff_integral_of_iteratedFDeriv (μ := μ) (fun y a => Φ (y, q a))
    (fun a => hΦ.comp (contDiff_id.prodMk contDiff_const)) (fun k => ?_) hsupp
  have h : Continuous fun p : P × α => (p.1, q p.2) := continuous_fst.prodMk (hq.comp continuous_snd)
  exact (continuous_iter_partial Φ hΦ k).comp h

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toM_mul (x y : UJ ε) : toM (x * y) = toM x * toM y := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toM_one : toM (1 : UJ ε) = 1 := rfl

/- English proof (translation)
The claim follows from `(isClosedEmbeddingMatrix n ε).1`.
-/
theorem emb_toM : IsClosedEmbedding (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := (isClosedEmbeddingMatrix n ε).1

/- English proof (translation)
The claim follows from `x.2`.
-/
theorem toM_mem (x : UJ ε) : toM x ∈ UJset ε := x.2

/- English proof (translation)
Establish `: g ∈ Set.range (coeMatrixAlt ε)` using `by rw [range_coeMatrix]; exact hg`. Conclude with `this`.
-/
theorem exists_toM {g : Matrix (Fin n) (Fin n) ℂ} (hg : inUJ ε g) : ∃ x : UJ ε, toM x = g := by
  have : g ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hg
  exact this

/- English proof (translation)
Establish `h1 : kᴴ * k = 1` using `Matrix.mem_unitaryGroup_iff'.1 hk.1`. Unfold `inUJ`. Rewrite using `[Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem inUJ_of_mem_Kset {k : Matrix (Fin n) (Fin n) ℂ} (hk : k ∈ Kset ε) : inUJ ε k := by
  have h1 : kᴴ * k = 1 := Matrix.mem_unitaryGroup_iff'.1 hk.1
  unfold inUJ
  rw [Matrix.mul_assoc, ← hk.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
The claim follows from `Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)`.
-/
theorem toM_inv_of_unitary {k : UJ ε} (hk : toM k ∈ Matrix.unitaryGroup (Fin n) ℂ) : toM k⁻¹ = (toM k)ᴴ :=
  Units.inv_eq_of_mul_eq_one_right (Matrix.mem_unitaryGroup_iff.1 hk)

/- English proof (translation)
Establish `h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1)` using `contDiff_snd.fst.prodMk contDiff_fst`. Establish `h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1`. Use `contDiff_mul.comp h1` as an intermediate fact. Simplify `this` using `only [Function.comp_def]`. Establish `h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1)` using `hf.comp h2`.

Conclude with `h3.smul contDiff_snd.snd`.
-/
theorem contDiff_Phi {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H]
    {f : Matrix (Fin n) (Fin n) ℂ → ℝ} (hf : ContDiff ℝ ∞ f) :
    ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) • p.2.2 := by
  have h1 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => (p.2.1, p.1) :=
    contDiff_snd.fst.prodMk contDiff_fst
  have h2 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => p.2.1 * p.1 := by
    have := contDiff_mul.comp h1
    simpa only [Function.comp_def] using this
  have h3 : ContDiff ℝ ∞ fun p : Matrix (Fin n) (Fin n) ℂ × (Matrix (Fin n) (Fin n) ℂ × H) => f (p.2.1 * p.1) :=
    hf.comp h2
  exact h3.smul contDiff_snd.snd

/- English proof (translation)
Use `⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _, emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Establish `hB` using `hfS _ h`. Use `hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩` and prove the remaining obligations. Establish `hu : IsUnit (toM x⁻¹ * g).det` using `isUnit_iff_ne_zero.2 (hd _ hB)`.

Establish `e : g = toM x * (toM x⁻¹ * g)`. Rewrite using `[← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]`. Use `show g * (toM x⁻¹ * g)⁻¹ = toM x`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem supp_local {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) (g₀ : Matrix (Fin n) (Fin n) ℂ) :
    ∃ U ∈ 𝓝 g₀, ∃ C : Set (UJ ε), IsCompact C ∧ ∀ g ∈ U, ∀ x ∉ C, f (toM x⁻¹ * g) = 0 := by
  refine ⟨Metric.closedBall g₀ 1, Metric.closedBall_mem_nhds _ one_pos, _,
    emb_toM.isCompact_preimage (isCompact_mul_inv (isCompact_closedBall g₀ 1) hS hd), fun g hg x hx => ?_⟩
  by_contra h
  have hB := hfS _ h
  refine hx ⟨(g, toM x⁻¹ * g), ⟨hg, hB⟩, ?_⟩
  have hu : IsUnit (toM x⁻¹ * g).det := isUnit_iff_ne_zero.2 (hd _ hB)
  have e : g = toM x * (toM x⁻¹ * g) := by
    rw [← Matrix.mul_assoc, ← toM_mul, mul_inv_cancel, toM_one, Matrix.one_mul]
  show g * (toM x⁻¹ * g)⁻¹ = toM x
  calc g * (toM x⁻¹ * g)⁻¹ = toM x * (toM x⁻¹ * g) * (toM x⁻¹ * g)⁻¹ := by rw [← e]
    _ = toM x := by rw [Matrix.mul_assoc, Matrix.mul_nonsing_inv _ hu, Matrix.mul_one]

/- English proof (translation)
Establish `hq : Continuous fun x : UJ ε => (toM x⁻¹, v x)` using `(emb_toM.continuous.comp continuous_inv).prodMk hv`. Establish `key` using `contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by`. Take `⟨U, hU, C, hC, h⟩` from `supp_local (ε := ε) hS hd hfS g₀`. Use `⟨U, hU, C, hC, fun g hg x hx => ?_⟩` and prove the remaining obligations. Simplify using `only [h g hg x hx, zero_smul]`.

Simplify `key` using `only`.
-/
theorem contDiff_avg {H : Type*} [NormedAddCommGroup H] [NormedSpace ℝ H] [CompleteSpace H]
    (v : UJ ε → H) (hv : Continuous v) {f : Matrix (Fin n) (Fin n) ℂ → ℝ} {S : Set (Matrix (Fin n) (Fin n) ℂ)}
    (hf : ContDiff ℝ ∞ f) (hS : IsCompact S) (hd : ∀ B ∈ S, B.det ≠ 0) (hfS : ∀ y, f y ≠ 0 → y ∈ S) :
    ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => ∫ x : UJ ε, f (toM x⁻¹ * g) • v x ∂(muG ε) := by
  have hq : Continuous fun x : UJ ε => (toM x⁻¹, v x) := (emb_toM.continuous.comp continuous_inv).prodMk hv
  have key := contDiff_integral_comp (muG ε) _ (contDiff_Phi (H := H) hf) _ hq fun g₀ => by
    obtain ⟨U, hU, C, hC, h⟩ := supp_local (ε := ε) hS hd hfS g₀
    refine ⟨U, hU, C, hC, fun g hg x hx => ?_⟩
    simp only [h g hg x hx, zero_smul]
  simpa only using key

end Gard

open Gard in

/- English proof (translation)
Introduce `n ε H _ _ _ σ hσ Y _ hY v hv`. Take `⟨⟨h1, hm⟩, hiso, hcont⟩` from `hσ`. Set `ρ : UJ ε → H →L[ℂ] H` to `fun x => σ (toM x)`. Establish `hρ : ∀ u, Continuous fun x => ρ x u` using `fun u => (hcont u).comp_continuous emb_toM.continuous toM_mem`. Establish `hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u)` using `fun x y u => by`.

Simplify using `only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]`. Establish `hρ1 : ∀ u, ρ 1 u = u` using `fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]`. Take `⟨V, hV, hclose⟩` from `exists_nhds_close ρ hρ hρ1 Y`. Establish `hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε)` using `inv_mem_nhds_one _ hV`. Rewrite `hVi` using `[emb_toM.isInducing.nhds_eq_comap, mem_comap]`.

Take `⟨W, hW, hWV⟩` from `hVi`. Establish `hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ)` using `(isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)`. Take `⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩` from `exists_bump (inter_mem hW hD)`. Set `w : UJ ε → ℝ` to `fun x => f (toM x⁻¹)`. Establish `hw : Continuous w` using `hf.continuous.comp (emb_toM.continuous.comp continuous_inv)`.

Establish `hc : HasCompactSupport w`. Use `HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h`. Conclude with `hx (hfS _ h)`. Establish `h0 : 0 ≤ w` using `fun x => hf0 _`.

Establish `hw1 : w 1 ≠ 0` using `by simpa only [w, inv_one, toM_one] using hf1`. Take `⟨T, hT⟩` from `exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc`. Establish `hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u)`. Introduce `k hk u`. Take `⟨k', rfl⟩` from `exists_toM (inUJ_of_mem_Kset hk)`.

Rewrite using `[hT, hT]`. Use `T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u` and prove the remaining obligations. Simplify using `only [w, _root_.mul_inv_rev, inv_inv]`. Rewrite using `[← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]`. Establish `hinj : ∀ y ∈ Y, T y = 0 → y = 0`.

Introduce `y hy hTy`. Rewrite `hTy` using `[hT]`. Use `eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy` and prove the remaining obligations. Establish `: x⁻¹ ∈ V⁻¹` using `hWV (hSW (hfS _ hx)).1`. Simplify using `using this`.

Take `⟨u, rfl⟩` from `exists_preimage Y T (hY T hTK) hinj v hv`. Introduce `g₀ _`. Use `⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _, (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩` and prove the remaining obligations. Take `⟨g', rfl⟩` from `exists_toM (ε := ε) hg`. Use `show ρ g' (T u) = _`.

Rewrite using `[hT, apply_alt (muG ε) ρ hρ hmul hw hc]`. Simplify using `only [w, _root_.mul_inv_rev, inv_inv, toM_mul]`.
-/
theorem garding_finite_smooth_vectors : GardingFin := by
  intro n ε H _ _ _ σ hσ Y _ hY v hv
  obtain ⟨⟨h1, hm⟩, hiso, hcont⟩ := hσ
  let ρ : UJ ε → H →L[ℂ] H := fun x => σ (toM x)
  have hρ : ∀ u, Continuous fun x => ρ x u := fun u =>
    (hcont u).comp_continuous emb_toM.continuous toM_mem
  have hmul : ∀ x y u, ρ (x * y) u = ρ x (ρ y u) := fun x y u => by
    simp only [ρ, toM_mul, hm _ (toM_mem x) _ (toM_mem y), ContinuousLinearMap.comp_apply]
  have hρ1 : ∀ u, ρ 1 u = u := fun u => by simp only [ρ, toM_one, h1, one_apply_eq_self]
  obtain ⟨V, hV, hclose⟩ := exists_nhds_close ρ hρ hρ1 Y
  have hVi : V⁻¹ ∈ 𝓝 (1 : UJ ε) := inv_mem_nhds_one _ hV
  rw [emb_toM.isInducing.nhds_eq_comap, mem_comap] at hVi
  obtain ⟨W, hW, hWV⟩ := hVi
  have hD : {y : Matrix (Fin n) (Fin n) ℂ | y.det ≠ 0} ∈ 𝓝 (1 : Matrix (Fin n) (Fin n) ℂ) :=
    (isOpen_ne_fun continuous_id.matrix_det continuous_const).mem_nhds (by simp)
  obtain ⟨f, S, hf, hf0, hf1, hS, hSW, hfS, hfk⟩ := exists_bump (inter_mem hW hD)
  let w : UJ ε → ℝ := fun x => f (toM x⁻¹)
  have hw : Continuous w := hf.continuous.comp (emb_toM.continuous.comp continuous_inv)
  have hc : HasCompactSupport w := by
    refine HasCompactSupport.intro (emb_toM.isCompact_preimage hS).inv fun x hx => ?_
    by_contra h
    exact hx (hfS _ h)
  have h0 : 0 ≤ w := fun x => hf0 _
  have hw1 : w 1 ≠ 0 := by simpa only [w, inv_one, toM_one] using hf1
  obtain ⟨T, hT⟩ := exists_strictHenselian_absolutely_closed_local_ring (muG ε) ρ hρ (fun x u => hiso _ (toM_mem x) u) hw hc
  have hTK : ∀ k ∈ Kset ε, ∀ u, T (σ k u) = σ k (T u) := by
    intro k hk u
    obtain ⟨k', rfl⟩ := exists_toM (inUJ_of_mem_Kset hk)
    rw [hT, hT]
    refine T_comm (muG ε) ρ hρ hmul hw hc h0 hw1 k' (fun x => ?_) u
    simp only [w, _root_.mul_inv_rev, inv_inv]
    rw [← mul_assoc, toM_mul, toM_mul, toM_inv_of_unitary hk.1, hfk _ hk.1]
  have hinj : ∀ y ∈ Y, T y = 0 → y = 0 := by
    intro y hy hTy
    rw [hT] at hTy
    refine eq_zero_of_alt_alt (muG ε) ρ hρ hw hc h0 hw1 y (fun x hx => hclose x ?_ y hy) hTy
    have : x⁻¹ ∈ V⁻¹ := hWV (hSW (hfS _ hx)).1
    simpa using this
  obtain ⟨u, rfl⟩ := exists_preimage Y T (hY T hTK) hinj v hv
  intro g₀ _
  refine ⟨univ, fun g => ∫ x : UJ ε, f (toM x⁻¹ * g) • ρ x u ∂(muG ε), isOpen_univ, mem_univ _,
    (contDiff_avg (fun x => ρ x u) (hρ u) hf hS (fun B hB => (hSW hB).2) hfS).contDiffOn, fun g _ hg => ?_⟩
  obtain ⟨g', rfl⟩ := exists_toM (ε := ε) hg
  show ρ g' (T u) = _
  rw [hT, apply_alt (muG ε) ρ hρ hmul hw hc]
  simp only [w, _root_.mul_inv_rev, inv_inv, toM_mul]

end CompanionTheory.D.gk.admitted
