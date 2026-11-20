import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.InfinitesimalCharacterLimits.InfinitesimalCharacterGlue
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.T2SpaceAdelicGeneralLinearGroupNumberField
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousOfIsOpenStab
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteInterCompact
open scoped Classical
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Rs PositivityTheory.Rg.BcB.SpectralAccumulation

noncomputable section

namespace GlobalTheory.CompanionTheory.FinDisc

/- English proof (translation)
Use `⟨hm, ?_⟩` and prove the remaining obligations. Rewrite using `[eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]`. Establish `h2 : ∀ x, ‖f x‖ₑ ^ ((2 : ENNReal).toReal) = ‖f x‖ₑ ^ (2 : ℕ)`. Introduce `x`. Rewrite using `[ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]`.

Evaluate the numerical expressions. Repeatedly rewrite using `[h2]`. Conclude with `ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf`.
-/
theorem memLp_two_of_lintegral_ne_top {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ}
    (hm : AEStronglyMeasurable f ν) (hf : ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν ≠ ⊤) : MemLp f 2 ν := by
  refine ⟨hm, ?_⟩
  rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (by norm_num) (by norm_num)]
  have h2 : ∀ x, ‖f x‖ₑ ^ ((2 : ENNReal).toReal) = ‖f x‖ₑ ^ (2 : ℕ) := by
    intro x
    rw [ENNReal.toReal_ofNat, ← ENNReal.rpow_natCast]
    norm_num
  simp_rw [h2]
  exact ENNReal.rpow_lt_top_of_nonneg (by norm_num) hf

/- English proof (translation)
Establish `hi : Integrable (fun x => ‖f x‖ ^ 2) ν` using `(memLp_two_iff_integrable_sq_norm hf.1).1 hf`. Rewrite using `[ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`.
-/
theorem ofReal_integral_sq {X : Type*} [MeasurableSpace X] {ν : Measure X} {f : X → ℂ} (hf : MemLp f 2 ν) :
    ENNReal.ofReal (∫ x, ‖f x‖ ^ 2 ∂ν) = ∫⁻ x, ‖f x‖ₑ ^ 2 ∂ν := by
  have hi : Integrable (fun x => ‖f x‖ ^ 2) ν := (memLp_two_iff_integrable_sq_norm hf.1).1 hf
  rw [ofReal_integral_eq_lintegral_ofReal hi (ae_of_all _ fun x => by positivity)]
  congr 1
  funext x
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Establish `hL : ∀ i, MemLp (ψ i) 2 ν` using `fun i => memLp_two_of_lintegral_ne_top (hm i) (by rw [h1 i]; exact ENNReal.one_ne_top)`. Establish `hg : MemLp (fun x => ∑ i, c i * ψ i x) 2 ν`. Use `memLp_finsetSum' (μ := ν) (p := 2) Finset.univ (fun i _ => (hL i).const_mul (c i))` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use extensionality with `x`.

Simplify using `[Finset.sum_apply]`. Establish `hint : ∀ i j, Integrable (fun x => ψ i x * (starRingEnd ℂ) (ψ j x)) ν` using `fun i j => (hL i).integrable_mul (hL j).star`. Establish `hdiag : ∀ i, ∫ x, ψ i x * (starRingEnd ℂ) (ψ i x) ∂ν = 1`. Introduce `i`. Establish `h` using `ofReal_integral_sq (hL i)`.

Rewrite `h` using `[h1 i, ENNReal.ofReal_eq_one]`. Repeatedly rewrite using `[Complex.mul_conj']`. Rewrite using `[show (fun x => ((‖ψ i x‖ : ℂ)) ^ 2) = fun x => (((‖ψ i x‖ ^ 2 : ℝ)) : ℂ) by`. Use extensionality with `x`. Use `push_cast`.

Use the proof step `rfl]`. Rewrite using `[integral_complex_ofReal, h]`. Simplify using the standard rewrite rules. Rewrite using `[← ofReal_integral_sq hg]`. Establish `key : ((∫ x, ‖∑ i, c i * ψ i x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ)`.

Rewrite using `[← integral_complex_ofReal]`. Establish `e1 : ∀ x, (((‖∑ i, c i * ψ i x‖ ^ 2 : ℝ)) : ℂ) = ∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) * (ψ i x * (starRingEnd ℂ) (ψ j x))`. Introduce `x`. Rewrite using `[Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [map_mul]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e1]`. Establish `e2 : ∀ i, ∫ x, ∑ j, (c i * (starRingEnd ℂ) (c j)) * (ψ i x * (starRingEnd ℂ) (ψ j x)) ∂ν = ((‖c i‖ ^ 2 : ℝ) : ℂ)`. Introduce `i`.

Rewrite using `[integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]`. Repeatedly rewrite using `[integral_const_mul]`. Rewrite using `[Finset.sum_eq_single i (fun j _ hji => by rw [h0 i j (Ne.symm hji), mul_zero]) (fun h => absurd (Finset.mem_univ i) h), hdiag i, mul_one, Complex.mul_conj']`. Use `push_cast`. Both sides reduce to the same expression.

Rewrite using `[integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint i j).const_mul _)), Finset.sum_congr rfl (fun i _ => e2 i)]`. Use `push_cast`. Both sides reduce to the same expression. Establish `key' : (∫ x, ‖∑ i, c i * ψ i x‖ ^ 2 ∂ν) = ∑ i, ‖c i‖ ^ 2` using `by exact_mod_cast key`. Rewrite using `[key', ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`.
-/
private theorem orth_sum_lemma {X : Type*} [MeasurableSpace X] {ν : Measure X} {n : ℕ}
    (ψ : Fin n → X → ℂ) (hm : ∀ i, AEStronglyMeasurable (ψ i) ν)
    (h1 : ∀ i, ∫⁻ x, ‖ψ i x‖ₑ ^ 2 ∂ν = 1)
    (h0 : ∀ i j, i ≠ j → ∫ x, ψ i x * (starRingEnd ℂ) (ψ j x) ∂ν = 0) (c : Fin n → ℂ) :
    ∫⁻ x, ‖∑ i, c i * ψ i x‖ₑ ^ 2 ∂ν = ∑ i, ‖c i‖ₑ ^ 2 := by
  have hL : ∀ i, MemLp (ψ i) 2 ν := fun i =>
    memLp_two_of_lintegral_ne_top (hm i) (by rw [h1 i]; exact ENNReal.one_ne_top)
  have hg : MemLp (fun x => ∑ i, c i * ψ i x) 2 ν := by
    have := memLp_finsetSum' (μ := ν) (p := 2) Finset.univ (fun i _ => (hL i).const_mul (c i))
    convert this using 1
    ext x
    simp [Finset.sum_apply]
  have hint : ∀ i j, Integrable (fun x => ψ i x * (starRingEnd ℂ) (ψ j x)) ν := fun i j =>
    (hL i).integrable_mul (hL j).star
  have hdiag : ∀ i, ∫ x, ψ i x * (starRingEnd ℂ) (ψ i x) ∂ν = 1 := by
    intro i
    have h := ofReal_integral_sq (hL i)
    rw [h1 i, ENNReal.ofReal_eq_one] at h
    simp_rw [Complex.mul_conj']
    rw [show (fun x => ((‖ψ i x‖ : ℂ)) ^ 2) = fun x => (((‖ψ i x‖ ^ 2 : ℝ)) : ℂ) by
      ext x; push_cast; rfl]
    rw [integral_complex_ofReal, h]
    simp
  rw [← ofReal_integral_sq hg]
  have key : ((∫ x, ‖∑ i, c i * ψ i x‖ ^ 2 ∂ν : ℝ) : ℂ) = ((∑ i, ‖c i‖ ^ 2 : ℝ) : ℂ) := by
    rw [← integral_complex_ofReal]
    have e1 : ∀ x, (((‖∑ i, c i * ψ i x‖ ^ 2 : ℝ)) : ℂ) =
        ∑ i, ∑ j, (c i * (starRingEnd ℂ) (c j)) * (ψ i x * (starRingEnd ℂ) (ψ j x)) := by
      intro x
      rw [Complex.ofReal_pow, ← Complex.mul_conj', map_sum, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
      simp only [map_mul]
      ring
    simp_rw [e1]
    have e2 : ∀ i, ∫ x, ∑ j, (c i * (starRingEnd ℂ) (c j)) * (ψ i x * (starRingEnd ℂ) (ψ j x)) ∂ν
        = ((‖c i‖ ^ 2 : ℝ) : ℂ) := by
      intro i
      rw [integral_finsetSum _ (fun j _ => (hint i j).const_mul _)]
      simp_rw [integral_const_mul]
      rw [Finset.sum_eq_single i (fun j _ hji => by rw [h0 i j (Ne.symm hji), mul_zero])
        (fun h => absurd (Finset.mem_univ i) h), hdiag i, mul_one, Complex.mul_conj']
      push_cast
      rfl
    rw [integral_finsetSum _ (fun i _ => integrable_finsetSum _ (fun j _ => (hint i j).const_mul _)),
      Finset.sum_congr rfl (fun i _ => e2 i)]
    push_cast
    rfl
  have key' : (∫ x, ‖∑ i, c i * ψ i x‖ ^ 2 ∂ν) = ∑ i, ‖c i‖ ^ 2 := by exact_mod_cast key
  rw [key', ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity)]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]

/- English proof (translation)
Establish `e0 : ∀ y : ENNReal, y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) = y`. Introduce `y`. Rewrite using `[← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]`. Evaluate the numerical expressions. Establish `e0' : ∀ y : ENNReal, (y ^ (1 / 2 : ℝ)) ^ 2 = y` using `fun y => by rw [sq, e0]`.

Establish `hcs` using `ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two (hw.pow_const (1 / 2 : ℝ)) ((hw.pow_const (1 / 2 : ℝ)).mul hh)`. Establish `e1 : ∀ x, w x ^ (1 / 2 : ℝ) * (w x ^ (1 / 2 : ℝ) * h x) = w x * h x`. Introduce `x`. Rewrite using `[← mul_assoc, e0]`. Establish `e2 : ∀ x, (w x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w x`.

Introduce `x`. Rewrite using `[ENNReal.rpow_two, e0']`. Establish `e3 : ∀ x, (w x ^ (1 / 2 : ℝ) * h x) ^ (2 : ℝ) = w x * h x ^ 2`. Introduce `x`. Rewrite using `[ENNReal.rpow_two, mul_pow, e0']`.

Simplify using `only [Pi.mul_apply, e1, e2, e3] at hcs`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem lintegral_mul_sq_le_lemma_2 {X : Type*} [MeasurableSpace X] {ν : Measure X}
    {w h : X → ENNReal} (hw : AEMeasurable w ν) (hh : AEMeasurable h ν) :
    (∫⁻ x, w x * h x ∂ν) ^ 2 ≤ (∫⁻ x, w x ∂ν) * ∫⁻ x, w x * h x ^ 2 ∂ν := by
  have e0 : ∀ y : ENNReal, y ^ (1 / 2 : ℝ) * y ^ (1 / 2 : ℝ) = y := by
    intro y
    rw [← ENNReal.rpow_add_of_nonneg _ _ (by norm_num) (by norm_num)]
    norm_num
  have e0' : ∀ y : ENNReal, (y ^ (1 / 2 : ℝ)) ^ 2 = y := fun y => by rw [sq, e0]
  have hcs := ENNReal.lintegral_mul_le_Lp_mul_Lq ν Real.HolderConjugate.two_two
    (hw.pow_const (1 / 2 : ℝ)) ((hw.pow_const (1 / 2 : ℝ)).mul hh)
  have e1 : ∀ x, w x ^ (1 / 2 : ℝ) * (w x ^ (1 / 2 : ℝ) * h x) = w x * h x := by
    intro x
    rw [← mul_assoc, e0]
  have e2 : ∀ x, (w x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = w x := by
    intro x
    rw [ENNReal.rpow_two, e0']
  have e3 : ∀ x, (w x ^ (1 / 2 : ℝ) * h x) ^ (2 : ℝ) = w x * h x ^ 2 := by
    intro x
    rw [ENNReal.rpow_two, mul_pow, e0']
  simp only [Pi.mul_apply, e1, e2, e3] at hcs
  calc (∫⁻ x, w x * h x ∂ν) ^ 2
      ≤ ((∫⁻ x, w x ∂ν) ^ (1 / 2 : ℝ) * (∫⁻ x, w x * h x ^ 2 ∂ν) ^ (1 / 2 : ℝ)) ^ 2 :=
        pow_le_pow_left₀ (by positivity) hcs 2
    _ = (∫⁻ x, w x ∂ν) * ∫⁻ x, w x * h x ^ 2 ∂ν := by rw [mul_pow, e0', e0']

/- English proof (translation)
Establish `hD : IsCompact ((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K))` using `(hK.prod hK).image (continuous_fst.mul continuous_snd.inv)`. Establish `hfin` using `GlobalTheory.CompanionTheory.ReproBessel.finite_inter_compact Γ hD`. Establish `hSf : {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.Finite` using `(hfin.preimage Subtype.val_injective.injOn).subset (fun η hη => ⟨η.2, hη⟩)`. Use `⟨hSf.toFinset.card, ENNReal.natCast_ne_top _, ?_⟩` and prove the remaining obligations. Introduce `f M z hM hK'`.

Distinguish the cases in `h : ∃ γ0 : Γ, f ((γ0 : G) * z) ≠ 0`. Take `⟨γ0, hγ0⟩` from `h`. Establish `hb : ∀ γ : Γ, f ((γ : G) * z) ≤ {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.indicator (fun _ => M) (γ * γ0⁻¹)`. Introduce `γ`. Distinguish the cases in `hγ : f ((γ : G) * z) = 0`.

Rewrite using `[hγ]`. Check the signs of the components of the expression. Establish `hmem : γ * γ0⁻¹ ∈ {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}`. Establish `e : ((γ * γ0⁻¹ : Γ) : G) = ((γ : G) * z) * ((γ0 : G) * z)⁻¹`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]`.

Conclude with `⟨((γ : G) * z, (γ0 : G) * z), ⟨hK' _ hγ, hK' _ hγ0⟩, e.symm⟩`. Rewrite using `[Set.indicator_of_mem hmem]`. Conclude with `hM _`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[tsum_eq_sum (s := hSf.toFinset) (fun η hη => Set.indicator_of_notMem (fun h => hη ((Set.Finite.mem_toFinset hSf).2 h)) _)]`.

Use `Finset.sum_congr rfl fun η hη => ?_` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem ((Set.Finite.mem_toFinset hSf).1 hη)]`. Use `_ = M * hSf.toFinset.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]`. Simplify using `only [not_exists, not_not] at h`. Simplify using `[h]`.
-/
private theorem tsum_le_count_lemma_3 {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [T2Space G] (Γ : Subgroup G) [DiscreteTopology Γ] {K : Set G} (hK : IsCompact K) :
    ∃ m : ENNReal, m ≠ ⊤ ∧ ∀ (f : G → ENNReal) (M : ENNReal) (z : G), (∀ y, f y ≤ M) →
      (∀ y, f y ≠ 0 → y ∈ K) → ∑' γ : Γ, f ((γ : G) * z) ≤ M * m := by
  have hD : IsCompact ((fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)) :=
    (hK.prod hK).image (continuous_fst.mul continuous_snd.inv)
  have hfin := GlobalTheory.CompanionTheory.ReproBessel.finite_inter_compact Γ hD
  have hSf : {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.Finite :=
    (hfin.preimage Subtype.val_injective.injOn).subset (fun η hη => ⟨η.2, hη⟩)
  refine ⟨hSf.toFinset.card, ENNReal.natCast_ne_top _, ?_⟩
  intro f M z hM hK'
  by_cases h : ∃ γ0 : Γ, f ((γ0 : G) * z) ≠ 0
  · obtain ⟨γ0, hγ0⟩ := h
    have hb : ∀ γ : Γ, f ((γ : G) * z) ≤
        {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.indicator (fun _ => M)
          (γ * γ0⁻¹) := by
      intro γ
      by_cases hγ : f ((γ : G) * z) = 0
      · rw [hγ]
        positivity
      · have hmem : γ * γ0⁻¹ ∈ {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)} := by
          have e : ((γ * γ0⁻¹ : Γ) : G) = ((γ : G) * z) * ((γ0 : G) * z)⁻¹ := by
            simp only [Subgroup.coe_mul, Subgroup.coe_inv, _root_.mul_inv_rev, mul_assoc, mul_inv_cancel_left]
          exact ⟨((γ : G) * z, (γ0 : G) * z), ⟨hK' _ hγ, hK' _ hγ0⟩, e.symm⟩
        rw [Set.indicator_of_mem hmem]
        exact hM _
    calc ∑' γ : Γ, f ((γ : G) * z)
        ≤ ∑' γ : Γ, {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.indicator
            (fun _ => M) (γ * γ0⁻¹) :=
          ENNReal.tsum_le_tsum hb
      _ = ∑' η : Γ, {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.indicator
            (fun _ => M) η :=
          (Equiv.mulRight γ0⁻¹).tsum_eq
            (fun η => {η : Γ | (η : G) ∈ (fun p : G × G => p.1 * p.2⁻¹) '' (K ×ˢ K)}.indicator
              (fun _ => M) η)
      _ = ∑ η ∈ hSf.toFinset, M := by
          rw [tsum_eq_sum (s := hSf.toFinset) (fun η hη =>
            Set.indicator_of_notMem (fun h => hη ((Set.Finite.mem_toFinset hSf).2 h)) _)]
          refine Finset.sum_congr rfl fun η hη => ?_
          rw [Set.indicator_of_mem ((Set.Finite.mem_toFinset hSf).1 hη)]
      _ = M * hSf.toFinset.card := by rw [Finset.sum_const, nsmul_eq_mul, mul_comm]
  · simp only [not_exists, not_not] at h
    simp [h]

/- English proof (translation)
Introduce `E _ _ _ N _ _ μ _ δ α F Ω hαc hαs hδ hF hΩ`. Use `haveI : DiscreteTopology (latticeGL E N) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E N`. Use `haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N`.

Use `haveI : Countable (latticeGL E N) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance`. Take `⟨Mr, hMr⟩` from `hαc.bounded_above_of_compact_support hαs`. Use `set M : ENNReal := ENNReal.ofReal Mr with hMdef`. Establish `hαM : ∀ y, ‖α y‖ₑ ≤ M` using `fun y => by`. Rewrite using `[← ofReal_norm]`.

Conclude with `ENNReal.ofReal_le_ofReal (hMr y)`. Use `set A : ENNReal := ∫⁻ y, ‖α y‖ₑ ∂μ with hAdef`. Establish `hA : A ≠ ⊤` using `(hαc.integrable_of_hasCompactSupport hαs).hasFiniteIntegral.ne`. Take `⟨m, hm, hcount⟩` from `tsum_le_count_lemma_3 (latticeGL E N) ((hΩ.prod hαs.isCompact).image (continuous_fst.mul continuous_snd) : IsCompact ((fun p : GA E N × GA E N => p.1 * p.2) '' (Ω ×ˢ tsupport α)))`. Establish `hpt : ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) → (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) → (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) → (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) → ∀ (v : Fin n → ℂ) (x : GA E N), x ∈ Ω → (∀ i, ∫ …`.

Introduce `n ψ hc hinv h1 h0 v x hx hv`. Use `set c : Fin n → ℂ := fun i => (starRingEnd ℂ) (v i) with hcdef`. Use `set g : GA E N → ℂ := fun z => ∑ i, c i * ψ i z with hg`. Establish `hgc : Continuous g` using `continuous_finsetSum _ fun i _ => continuous_const.mul (hc i)`. Establish `hginv : ∀ γ ∈ latticeGL E N, ∀ z, g (γ * z) = g z`.

Introduce `γ hγ z`. Simplify using `only [hg, hinv _ γ hγ]`. Use `set T : ENNReal := ∑ i, ‖v i‖ₑ ^ 2 with hT`. Establish `hTtop : T ≠ ⊤` using `ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top`. Establish `hstep1 : T ≤ ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ`.

Establish `hint : ∀ i, Integrable (fun y => α y * ψ i (x * y)) μ` using `fun i => (hαc.mul ((hc i).comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport hαs.mul_right`. Establish `e : ∫ y, α y * g (x * y) ∂μ = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)`. Establish `e' : ∀ y, α y * g (x * y) = ∑ i, c i * (α y * ψ i (x * y))`. Introduce `y`. Simplify using `only [hg, Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Repeatedly rewrite using `[e']`. Rewrite using `[integral_finsetSum _ fun i _ => (hint i).const_mul (c i)]`. Repeatedly rewrite using `[integral_const_mul, hv]`. Use `push_cast`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hcdef, mul_comm]`. Conclude with `Complex.mul_conj' (v i)`. Establish `eT : T = ‖((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)‖ₑ`. Rewrite using `[← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity), ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hT]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]`. Combine the equalities or inequalities in the displayed calculation. Establish `hstep2 : (∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ) ^ 2 ≤ A * ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ` using `lintegral_mul_sq_le_lemma_2 (w := fun y => ‖α y‖ₑ) (h := fun y => ‖g (x * y)‖ₑ) hαc.measurable.enorm.aemeasurable (hgc.comp (continuous_const.mul continuous_id)).measurable.enorm.aemeasurable`. Establish `horth : ∫⁻ z in F, ‖g z‖ₑ ^ 2 ∂μ = T`.

Rewrite using `[orth_sum_lemma ψ (fun i => (hc i).aestronglyMeasurable) h1 h0 c, hT]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [hcdef, ← ofReal_norm, Complex.norm_conj]`. Establish `hstep3 : ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ ≤ (M * m) * T`. Establish `e1 : ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ = ∫⁻ z, ‖α (x⁻¹ * z)‖ₑ * ‖g z‖ₑ ^ 2 ∂μ`.

Rewrite using `[← lintegral_mul_left_eq_self (fun z => ‖α (x⁻¹ * z)‖ₑ * ‖g z‖ₑ ^ 2) x]`. Simplify using `only [inv_mul_cancel_left]`. Rewrite using `[e1, hF.lintegral_eq_tsum'']`. Establish `e2 : ∀ γ : latticeGL E N, ∫⁻ z in F, ‖α (x⁻¹ * (γ • z))‖ₑ * ‖g (γ • z)‖ₑ ^ 2 ∂μ = ∫⁻ z in F, ‖α (x⁻¹ * ((γ : GA E N) * z))‖ₑ * ‖g z‖ₑ ^ 2 ∂μ`. Introduce `γ`.

Use `lintegral_congr fun z => ?_` and prove the remaining obligations. Rewrite using `[Subgroup.smul_def, smul_eq_mul, hginv _ γ.2]`. Rewrite using `[tsum_congr e2, ← lintegral_tsum]`. Combine the equalities or inequalities in the displayed calculation. Repeatedly rewrite using `[ENNReal.tsum_mul_right]`.

Use `_ ≤ ∫⁻ z in F, (M * m) * ‖g z‖ₑ ^ 2 ∂μ := by`. Use `lintegral_mono fun z => ?_` and prove the remaining obligations. Use `gcongr`. Use `hcount (fun y => ‖α (x⁻¹ * y)‖ₑ) M z (fun y => hαM _) (fun y hy => ?_)` and prove the remaining obligations. Establish `h1 : α (x⁻¹ * y) ≠ 0` using `fun h => hy (by simp [h])`.

Establish `h2 : x⁻¹ * y ∈ tsupport α` using `subset_tsupport _ h1`. Conclude with `⟨(x, x⁻¹ * y), ⟨hx, h2⟩, mul_inv_cancel_left x y⟩`. Use `_ = (M * m) * ∫⁻ z in F, ‖g z‖ₑ ^ 2 ∂μ := lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)`. Use `_ = (M * m) * T := by rw [horth]`. Introduce `γ`.

Conclude with `((hαc.comp (continuous_const.mul (continuous_const.mul continuous_id))).measurable.enorm.mul (hgc.measurable.enorm.pow_const 2)).aemeasurable`. Distinguish the cases in `hT0 : T = 0`. Rewrite using `[hT0]`. Check the signs of the components of the expression. Establish `hsq : T * T ≤ (A * (M * m)) * T`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `(ENNReal.mul_le_mul_iff_left hT0 hTtop).1 hsq`. Use `⟨μ Ω * ((ENNReal.ofReal δ⁻¹) ^ 2 * (A * (M * m))), ?_, ?_⟩` and prove the remaining obligations. Conclude with `ENNReal.mul_ne_top hΩ.measure_lt_top.ne (ENNReal.mul_ne_top (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top hA (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)))`. Introduce `n ψ hc hinv heig h1 h0`.

Use `choose s hs hseig using heig`. Establish `hpx : ∀ x ∈ Ω, ∑ i, ‖ψ i x‖ₑ ^ 2 ≤ (ENNReal.ofReal δ⁻¹) ^ 2 * (A * (M * m))`. Introduce `x hx`. Establish `hb` using `hpt n ψ hc hinv h1 h0 (fun i => s i * ψ i x) x hx (fun i => hseig i x)`. Combine the equalities or inequalities in the displayed calculation.

Use `Finset.sum_le_sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_pow]`. Use `pow_le_pow_left₀ (by positivity) ?_ 2` and prove the remaining obligations. Rewrite using `[← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), norm_mul]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `hs'` using `hs i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]`. Use `_ ≤ δ⁻¹ * (‖s i‖ * ‖ψ i x‖) := by gcongr`. Use `_ = (ENNReal.ofReal δ⁻¹) ^ 2 * ∑ i, ‖s i * ψ i x‖ₑ ^ 2 := by rw [Finset.mul_sum]`.

Use `_ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem bessel_lintegral_le : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (N : ℕ) [MeasurableSpace (GA E N)] [BorelSpace (GA E N)]
  (μ : Measure (GA E N)) [μ.IsHaarMeasure] (δ : ℝ) (α : GA E N → ℂ) (F Ω : Set (GA E N)),
  Continuous α → HasCompactSupport α → 0 < δ → IsFundamentalDomain (latticeGL E N) F μ → IsCompact Ω →
  ∃ B : ENNReal, B ≠ ⊤ ∧ ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
    (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) →
    (∀ i, ∃ s : ℂ, δ ≤ ‖s‖ ∧ ∀ x, ∫ y, α y * ψ i (x * y) ∂μ = s * ψ i x) →
    (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) →
    (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) →
    ∑ i, ∫⁻ x in Ω, ‖ψ i x‖ₑ ^ 2 ∂μ ≤ B := by
  intro E _ _ _ N _ _ μ _ δ α F Ω hαc hαs hδ hF hΩ
  haveI : DiscreteTopology (latticeGL E N) := GlobalTheory.CuspRep.CuspidalL2GL.discreteTopology_latticeGL
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.secondCountableTopology_GA E N
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.t2Space_GA E N
  haveI := GlobalTheory.CuspRep.CuspidalL2GL.locallyCompactSpace_GA E N
  haveI : Countable (latticeGL E N) := TopologicalSpace.separableSpace_iff_countable.1 inferInstance
  obtain ⟨Mr, hMr⟩ := hαc.bounded_above_of_compact_support hαs
  set M : ENNReal := ENNReal.ofReal Mr with hMdef
  have hαM : ∀ y, ‖α y‖ₑ ≤ M := fun y => by
    rw [← ofReal_norm]
    exact ENNReal.ofReal_le_ofReal (hMr y)
  set A : ENNReal := ∫⁻ y, ‖α y‖ₑ ∂μ with hAdef
  have hA : A ≠ ⊤ := (hαc.integrable_of_hasCompactSupport hαs).hasFiniteIntegral.ne
  obtain ⟨m, hm, hcount⟩ := tsum_le_count_lemma_3 (latticeGL E N) ((hΩ.prod hαs.isCompact).image (continuous_fst.mul continuous_snd) :
      IsCompact ((fun p : GA E N × GA E N => p.1 * p.2) '' (Ω ×ˢ tsupport α)))
  have hpt : ∀ (n : ℕ) (ψ : Fin n → GA E N → ℂ), (∀ i, Continuous (ψ i)) →
      (∀ i, ∀ γ ∈ latticeGL E N, ∀ x, ψ i (γ * x) = ψ i x) →
      (∀ i, (∫⁻ x in F, ‖ψ i x‖ₑ ^ 2 ∂μ) = 1) →
      (∀ i j, i ≠ j → ∫ x in F, ψ i x * (starRingEnd ℂ) (ψ j x) ∂μ = 0) →
      ∀ (v : Fin n → ℂ) (x : GA E N), x ∈ Ω → (∀ i, ∫ y, α y * ψ i (x * y) ∂μ = v i) →
      ∑ i, ‖v i‖ₑ ^ 2 ≤ A * (M * m) := by
    intro n ψ hc hinv h1 h0 v x hx hv
    set c : Fin n → ℂ := fun i => (starRingEnd ℂ) (v i) with hcdef
    set g : GA E N → ℂ := fun z => ∑ i, c i * ψ i z with hg
    have hgc : Continuous g := continuous_finsetSum _ fun i _ => continuous_const.mul (hc i)
    have hginv : ∀ γ ∈ latticeGL E N, ∀ z, g (γ * z) = g z := by
      intro γ hγ z
      simp only [hg, hinv _ γ hγ]
    set T : ENNReal := ∑ i, ‖v i‖ₑ ^ 2 with hT
    have hTtop : T ≠ ⊤ := ENNReal.sum_ne_top.2 fun i _ => ENNReal.pow_ne_top enorm_ne_top
    have hstep1 : T ≤ ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ := by
      have hint : ∀ i, Integrable (fun y => α y * ψ i (x * y)) μ := fun i =>
        (hαc.mul ((hc i).comp (continuous_const.mul continuous_id))).integrable_of_hasCompactSupport
          hαs.mul_right
      have e : ∫ y, α y * g (x * y) ∂μ = ((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ) := by
        have e' : ∀ y, α y * g (x * y) = ∑ i, c i * (α y * ψ i (x * y)) := by
          intro y
          simp only [hg, Finset.mul_sum]
          exact Finset.sum_congr rfl fun i _ => by ring
        simp_rw [e']
        rw [integral_finsetSum _ fun i _ => (hint i).const_mul (c i)]
        simp_rw [integral_const_mul, hv]
        push_cast
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hcdef, mul_comm]
        exact Complex.mul_conj' (v i)
      have eT : T = ‖((∑ i, ‖v i‖ ^ 2 : ℝ) : ℂ)‖ₑ := by
        rw [← ofReal_norm, Complex.norm_real, Real.norm_of_nonneg (by positivity),
          ENNReal.ofReal_sum_of_nonneg (fun i _ => by positivity), hT]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      calc T = ‖∫ y, α y * g (x * y) ∂μ‖ₑ := by rw [e, eT]
        _ ≤ ∫⁻ y, ‖α y * g (x * y)‖ₑ ∂μ := enorm_integral_le_lintegral_enorm _
        _ = ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ := by simp_rw [enorm_mul]
    have hstep2 : (∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ) ^ 2 ≤ A * ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ :=
      lintegral_mul_sq_le_lemma_2 (w := fun y => ‖α y‖ₑ) (h := fun y => ‖g (x * y)‖ₑ)
        hαc.measurable.enorm.aemeasurable
        (hgc.comp (continuous_const.mul continuous_id)).measurable.enorm.aemeasurable
    have horth : ∫⁻ z in F, ‖g z‖ₑ ^ 2 ∂μ = T := by
      rw [orth_sum_lemma ψ (fun i => (hc i).aestronglyMeasurable) h1 h0 c, hT]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hcdef, ← ofReal_norm, Complex.norm_conj]
    have hstep3 : ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ ≤ (M * m) * T := by
      have e1 : ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ = ∫⁻ z, ‖α (x⁻¹ * z)‖ₑ * ‖g z‖ₑ ^ 2 ∂μ := by
        rw [← lintegral_mul_left_eq_self (fun z => ‖α (x⁻¹ * z)‖ₑ * ‖g z‖ₑ ^ 2) x]
        simp only [inv_mul_cancel_left]
      rw [e1, hF.lintegral_eq_tsum'']
      have e2 : ∀ γ : latticeGL E N, ∫⁻ z in F, ‖α (x⁻¹ * (γ • z))‖ₑ * ‖g (γ • z)‖ₑ ^ 2 ∂μ
          = ∫⁻ z in F, ‖α (x⁻¹ * ((γ : GA E N) * z))‖ₑ * ‖g z‖ₑ ^ 2 ∂μ := by
        intro γ
        refine lintegral_congr fun z => ?_
        rw [Subgroup.smul_def, smul_eq_mul, hginv _ γ.2]
      rw [tsum_congr e2, ← lintegral_tsum]
      · calc ∫⁻ z in F, ∑' γ : latticeGL E N, ‖α (x⁻¹ * ((γ : GA E N) * z))‖ₑ * ‖g z‖ₑ ^ 2 ∂μ
            = ∫⁻ z in F, (∑' γ : latticeGL E N, ‖α (x⁻¹ * ((γ : GA E N) * z))‖ₑ) * ‖g z‖ₑ ^ 2 ∂μ := by
              simp_rw [ENNReal.tsum_mul_right]
          _ ≤ ∫⁻ z in F, (M * m) * ‖g z‖ₑ ^ 2 ∂μ := by
              refine lintegral_mono fun z => ?_
              gcongr
              refine hcount (fun y => ‖α (x⁻¹ * y)‖ₑ) M z (fun y => hαM _) (fun y hy => ?_)
              have h1 : α (x⁻¹ * y) ≠ 0 := fun h => hy (by simp [h])
              have h2 : x⁻¹ * y ∈ tsupport α := subset_tsupport _ h1
              exact ⟨(x, x⁻¹ * y), ⟨hx, h2⟩, mul_inv_cancel_left x y⟩
          _ = (M * m) * ∫⁻ z in F, ‖g z‖ₑ ^ 2 ∂μ :=
              lintegral_const_mul' _ _ (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)
          _ = (M * m) * T := by rw [horth]
      · intro γ
        exact ((hαc.comp (continuous_const.mul (continuous_const.mul continuous_id))).measurable.enorm.mul
          (hgc.measurable.enorm.pow_const 2)).aemeasurable
    by_cases hT0 : T = 0
    · rw [hT0]
      positivity
    have hsq : T * T ≤ (A * (M * m)) * T := by
      calc T * T = T ^ 2 := (sq T).symm
        _ ≤ (∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ∂μ) ^ 2 := pow_le_pow_left₀ (by positivity) hstep1 2
        _ ≤ A * ∫⁻ y, ‖α y‖ₑ * ‖g (x * y)‖ₑ ^ 2 ∂μ := hstep2
        _ ≤ A * ((M * m) * T) := mul_le_mul_of_nonneg_left hstep3 (by positivity)
        _ = (A * (M * m)) * T := by ring
    exact (ENNReal.mul_le_mul_iff_left hT0 hTtop).1 hsq
  refine ⟨μ Ω * ((ENNReal.ofReal δ⁻¹) ^ 2 * (A * (M * m))), ?_, ?_⟩
  · exact ENNReal.mul_ne_top hΩ.measure_lt_top.ne (ENNReal.mul_ne_top
      (ENNReal.pow_ne_top ENNReal.ofReal_ne_top) (ENNReal.mul_ne_top hA
        (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hm)))
  intro n ψ hc hinv heig h1 h0
  choose s hs hseig using heig
  have hpx : ∀ x ∈ Ω, ∑ i, ‖ψ i x‖ₑ ^ 2 ≤ (ENNReal.ofReal δ⁻¹) ^ 2 * (A * (M * m)) := by
    intro x hx
    have hb := hpt n ψ hc hinv h1 h0 (fun i => s i * ψ i x) x hx (fun i => hseig i x)
    calc ∑ i, ‖ψ i x‖ₑ ^ 2 ≤ ∑ i, (ENNReal.ofReal δ⁻¹) ^ 2 * ‖s i * ψ i x‖ₑ ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [← mul_pow]
          refine pow_le_pow_left₀ (by positivity) ?_ 2
          rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul (by positivity), norm_mul]
          apply ENNReal.ofReal_le_ofReal
          have hs' := hs i
          calc ‖ψ i x‖ = δ⁻¹ * (δ * ‖ψ i x‖) := by
                rw [← mul_assoc, inv_mul_cancel₀ hδ.ne', one_mul]
            _ ≤ δ⁻¹ * (‖s i‖ * ‖ψ i x‖) := by gcongr
      _ = (ENNReal.ofReal δ⁻¹) ^ 2 * ∑ i, ‖s i * ψ i x‖ₑ ^ 2 := by rw [Finset.mul_sum]
      _ ≤ _ := mul_le_mul_of_nonneg_left hb (by positivity)
  calc ∑ i, ∫⁻ x in Ω, ‖ψ i x‖ₑ ^ 2 ∂μ = ∫⁻ x in Ω, ∑ i, ‖ψ i x‖ₑ ^ 2 ∂μ :=
        (lintegral_finsetSum _ fun i _ => (hc i).measurable.enorm.pow_const 2).symm
    _ ≤ ∫⁻ x in Ω, (ENNReal.ofReal δ⁻¹) ^ 2 * (A * (M * m)) ∂μ := setLIntegral_mono' hΩ.measurableSet hpx
    _ = _ := by rw [setLIntegral_const, mul_comm]

end GlobalTheory.CompanionTheory.FinDisc

end
