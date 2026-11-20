import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.HypJ
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.TensorLocallyCompactRing
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelesLocallyCompactSecondCountable
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.GeomSumIntLe
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.FlowLatticeCountBoundedStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.HyperbolicFundamentalDomainCoverStatement
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section

namespace GlobalTheory.CompanionTheory.SW.IsoCount

/- English proof (translation)
The claim follows from `funext fun i => Matrix.mulVec_smul _ a (X i)`.
-/
theorem actW_smul {F E : Type} [Field F] [Field E] [Algebra F E] (R : Type) [CommRing R] [Algebra F R] (σ : E →ₐ[F] E)
    {M n : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J) (a : R ⊗[F] E) (X : Fin n → Fin M → R ⊗[F] E) :
    actW R σ J h (a • X) = a • actW R σ J h X := funext fun i => Matrix.mulVec_smul _ a (X i)

set_option maxHeartbeats 600000 in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hcm M J hJ hM hfin τ hτ μ 𝓕 hμ h𝓕 Ω hΩ`. Take `⟨⟨_, _, _⟩, -⟩` from `GlobalTheory.CompanionTheory.AdeleTop.adele_top F`. Take `⟨_, _, _, _, hsc, -, -, hB, -⟩` from `GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)`. Use `hB 1 (M + 2)` as an intermediate fact. Take `⟨Y, Kc, hY, hKc, hY1, hmain⟩` from `GlobalTheory.T.hyperbolic_fundamental_domain_cover F E σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕`.

Establish `hc : Continuous fun p : ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E)) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) => fun (_ _ : Fin 1) => hR (AF F) σ (hypJ J) (p.1.2 0) (p.2 0)`. Use `continuous_pi fun _ => continuous_pi fun _ => ?_` and prove the remaining obligations. Simplify using `only [hR, hform]`. Conclude with `continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ => ((hsc.comp ((continuous_apply_apply 0 i).comp continuous_fst.snd)).mul continuous_const).mul ((continuous_apply_apply 0 j).comp continuous_snd)`. Take `⟨x₀, C, hlat⟩` from `GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 _ ((hY.prod hΩ).image hc)`.

Take `⟨C', hC'⟩` from `GlobalTheory.CompanionTheory.Adelic.geom_sum_int (Module.finrank ℚ F) M Module.finrank_pos hM x₀ C`. Use `⟨Kc.toReal * C', fun r hr => ?_⟩` and prove the remaining obligations. Use `set t : AF F ⊗[F] E := ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) with ht`. Use `set Z : Set (Fin 1 → Fin (M + 2) → E) := {X | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} with hZ`. Set `R : Setoid (Fin 1 → Fin (M + 2) → E)` to `MulAction.orbitRel Eˣ _`.

Use `set L : Set (Fin 1 → Fin (M + 2) → E) := {X | X ∈ Z ∧ (Quotient.mk R X).out = X} with hL`. Use `set Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ := fun y => ∑' l : Eˣ, Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y) with hΦ`. Establish `: Countable E` using `Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv`. Establish `: Countable Eˣ` using `Units.val_injective.countable`. Establish `hsm : ∀ (l : E) (X : Fin 1 → Fin (M + 2) → E), ratTup (F` using `F) (AF F) (l • X) = (inclR (F := F) (AF F) l : AF F ⊗[F] E) • ratTup (AF F) X := fun l X =>`.

Use function extensionality and compare the values at `fun a => funext fun i => map_mul _ _ _`. Establish `h1 : cntI σ _ μ 𝓕 Z (fun Y => Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • Y)) ≤ cntI σ _ μ 𝓕 L Φ`. Use `lintegral_mono fun h => ?_` and prove the remaining obligations. Establish `hex : ∀ X : Z, ∃ p : L × Eˣ, (p.2 : E) • p.1.1 = X.1` using `fun X => by`. Choose the witnesses or unpack the hypotheses as in `⟨Y₀, l, hl, hY⟩ : ∃ (Y₀ : Fin 1 → Fin (M + 2) → E) (l : Eˣ), (l : E) • Y₀ = X.1 ∧ (Quotient.mk R Y₀).out = Y₀ := by`.

Take `⟨l, hl⟩ : ∃ l : Eˣ, l • (Quotient.mk R X.1).out = X.1` from `(R.symm (Quotient.mk_out X.1) :)`. Conclude with `⟨_, l, hl, congrArg Quotient.out (Quotient.out_eq _)⟩`. Use `⟨(⟨Y₀, ⟨fun h0 => X.2.1 (by rw [← hl, h0, smul_zero]), ?_⟩, hY⟩, l), hl⟩` and prove the remaining obligations. Establish `h2` using `X.2.2`. Rewrite `h2` using `[← hl]`.

Use function extensionality and compare the values at `a b`. Establish `h3` using `congrFun (congrFun h2 a) b`. Establish `e : gramE σ (hypJ J) ((l : E) • Y₀) a b = σ l * l * gramE σ (hypJ J) Y₀ a b`. Simplify using `only [gramE, hE, hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, RingHom.coe_coe]`. Conclude with `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring`.

Rewrite `h3` using `[e]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (mul_ne_zero ((map_ne_zero σ).2 l.ne_zero) l.ne_zero)`. Use `choose p hp using hex`. Establish `hpi : Function.Injective p` using `fun X X' e => Subtype.ext (by rw [← hp X, e, hp X'])`. Simplify using `only [hΦ, ← ENNReal.tsum_prod]`.

Use `le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hpi _)` and prove the remaining obligations. Rewrite using `[← actW_smul _ _ _ _ (inclR _ _), ← hsm, hp]`. Establish `hm : Measurable Φ` using `Measurable.ennreal_tsum fun l => (measurable_const.indicator hΩ.measurableSet).comp ((continuous_const_smul _).const_smul t).measurable`. Use `h1.trans ((hmain Φ hm (fun l y hl => ?_) (fun j => if (j : ℝ) + Real.log r < x₀ then 0 else ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * ((j : ℝ) + Real.log r)))) (fun j p hp => ?_) L (fun X hX => hX.1) fun X hX X' hX' l e => ?_).trans ?_)` and prove the remaining obligations. Simplify using `only [hΦ, smul_smul (inclR _ _), ← map_mul]`.

Conclude with `(Equiv.mulRight (Units.mk0 l hl)).tsum_eq fun l : Eˣ => Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y)`. Establish `h2` using `hlat ((j : ℝ) + Real.log r)`. Rewrite `h2` using `[Nat.cast_one, mul_one]`. Use `le_trans ?_ h2` and prove the remaining obligations. Set `ι : Eˣ → {X : Fin 1 → Fin 1 → E // X ≠ 0}` to `fun l => ⟨fun _ _ => l, fun h => l.ne_zero (congrFun (congrFun h 0) 0)⟩`.

Establish `hι : Function.Injective ι` using `fun l l' e => Units.ext (congrFun (congrFun (congrArg Subtype.val e) 0) 0)`. Use `le_trans (ENNReal.tsum_le_tsum fun l => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hι _)` and prove the remaining obligations. Distinguish the cases in `hmem : t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • ((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1 ∈ Ω`. Rewrite using `[Set.indicator_of_mem hmem, Set.indicator_of_mem]`. Use `⟨(p, _), ⟨hp, hmem⟩, funext fun a => funext fun b => ?_⟩` and prove the remaining obligations.

Establish `h3` using `hY1 p hp`. Simplify using `only [hR, hform, Pi.smul_apply, smul_eq_mul, ratTup, ι, neg_add, ofAdd_add, map_mul, Units.val_mul, ← ht] at h3 ⊢`. Rewrite using `[← mul_one (_ * _ * _), ← h3, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun j _ => by ring`. Rewrite using `[Set.indicator_of_notMem hmem]`. Conclude with `zero_le`. Establish `hl : l ≠ 0` using `fun h0 => hX'.1.1 (by rw [e, h0, zero_smul])`. Rewrite using `[← hX'.2, ← hX.2]`.

Conclude with `congrArg Quotient.out (Quotient.sound (show R X' X from ⟨Units.mk0 l hl, e.symm⟩))`. Rewrite using `[mul_assoc Kc.toReal, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKc.ne]`. Conclude with `mul_le_mul_right (hC' r hr) _`.
-/
theorem mean_isotropic_count_le : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → FinVol F E σ M J → ∀ τ : Multiplicative ℝ →* (AF F ⊗[F] E)ˣ, IsFlow τ → ∀ (μ : Measure (HA (AF F) σ (hypJ J))) (𝓕 : Set (HA (AF F) σ (hypJ J))), IsHaarH F E σ (M + 2) (hypJ J) μ → IsFDH F E σ (M + 2) (hypJ J) μ 𝓕 → ∀ Ω : Set (Fin 1 → Fin (M + 2) → AF F ⊗[F] E), IsCompact Ω → ∃ C : ℝ, ∀ r : ℝ, 0 < r → cntI σ _ μ 𝓕 {X : Fin 1 → Fin (M + 2) → E | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} (fun Y => (Set.indicator Ω (fun _ => (1 : ℝ≥0∞))) (((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • Y)) ≤ ENNReal.ofReal (C * r ^ (2 * Module.finrank ℚ F * (M + 1))) := by
  intro F E _ _ _ _ _ σ hcm M J hJ hM hfin τ hτ μ 𝓕 hμ h𝓕 Ω hΩ
  obtain ⟨⟨_, _, _⟩, -⟩ := GlobalTheory.CompanionTheory.AdeleTop.adele_top F
  obtain ⟨_, _, _, _, hsc, -, -, hB, -⟩ := GlobalTheory.CompanionTheory.SW.TopK.topTens_props F E σ hcm (AF F)
  have := hB 1 (M + 2)
  obtain ⟨Y, Kc, hY, hKc, hY1, hmain⟩ := GlobalTheory.T.hyperbolic_fundamental_domain_cover F E σ hcm M J hJ hfin τ hτ μ 𝓕 hμ h𝓕
  have hc : Continuous fun p : ((Fin 1 → Fin (M + 2) → AF F ⊗[F] E) × (Fin 1 → Fin (M + 2) → AF F ⊗[F] E)) ×
      (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) => fun (_ _ : Fin 1) => hR (AF F) σ (hypJ J) (p.1.2 0) (p.2 0) := by
    refine continuous_pi fun _ => continuous_pi fun _ => ?_
    simp only [hR, hform]
    exact continuous_finsetSum _ fun i _ => continuous_finsetSum _ fun j _ =>
      ((hsc.comp ((continuous_apply_apply 0 i).comp continuous_fst.snd)).mul continuous_const).mul
        ((continuous_apply_apply 0 j).comp continuous_snd)
  obtain ⟨x₀, C, hlat⟩ := GlobalTheory.T.flow_lattice_count_bounded F E σ hcm τ hτ 1 _ ((hY.prod hΩ).image hc)
  obtain ⟨C', hC'⟩ := GlobalTheory.CompanionTheory.Adelic.geom_sum_int (Module.finrank ℚ F) M Module.finrank_pos hM x₀ C
  refine ⟨Kc.toReal * C', fun r hr => ?_⟩
  set t : AF F ⊗[F] E := ((τ (Multiplicative.ofAdd (-Real.log r)) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) with ht
  set Z : Set (Fin 1 → Fin (M + 2) → E) := {X | X ≠ 0 ∧ gramE σ (hypJ J) X = 0} with hZ
  let R : Setoid (Fin 1 → Fin (M + 2) → E) := MulAction.orbitRel Eˣ _
  set L : Set (Fin 1 → Fin (M + 2) → E) := {X | X ∈ Z ∧ (Quotient.mk R X).out = X} with hL
  set Φ : (Fin 1 → Fin (M + 2) → AF F ⊗[F] E) → ℝ≥0∞ := fun y => ∑' l : Eˣ,
    Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y) with hΦ
  have : Countable E := Countable.of_equiv _ (Module.finBasis ℚ E).equivFun.symm.toEquiv
  have : Countable Eˣ := Units.val_injective.countable
  have hsm : ∀ (l : E) (X : Fin 1 → Fin (M + 2) → E), ratTup (F := F) (AF F) (l • X) =
      (inclR (F := F) (AF F) l : AF F ⊗[F] E) • ratTup (AF F) X := fun l X =>
    funext fun a => funext fun i => map_mul _ _ _
  have h1 : cntI σ _ μ 𝓕 Z (fun Y => Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • Y)) ≤ cntI σ _ μ 𝓕 L Φ := by
    refine lintegral_mono fun h => ?_
    have hex : ∀ X : Z, ∃ p : L × Eˣ, (p.2 : E) • p.1.1 = X.1 := fun X => by
      obtain ⟨Y₀, l, hl, hY⟩ : ∃ (Y₀ : Fin 1 → Fin (M + 2) → E) (l : Eˣ), (l : E) • Y₀ = X.1 ∧
          (Quotient.mk R Y₀).out = Y₀ := by
        obtain ⟨l, hl⟩ : ∃ l : Eˣ, l • (Quotient.mk R X.1).out = X.1 := (R.symm (Quotient.mk_out X.1) :)
        exact ⟨_, l, hl, congrArg Quotient.out (Quotient.out_eq _)⟩
      refine ⟨(⟨Y₀, ⟨fun h0 => X.2.1 (by rw [← hl, h0, smul_zero]), ?_⟩, hY⟩, l), hl⟩
      have h2 := X.2.2
      rw [← hl] at h2
      funext a b
      have h3 := congrFun (congrFun h2 a) b
      have e : gramE σ (hypJ J) ((l : E) • Y₀) a b = σ l * l * gramE σ (hypJ J) Y₀ a b := by
        simp only [gramE, hE, hform, Pi.smul_apply, smul_eq_mul, map_mul, Finset.mul_sum, RingHom.coe_coe]
        exact Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
      rw [e] at h3
      exact (mul_eq_zero.1 h3).resolve_left (mul_ne_zero ((map_ne_zero σ).2 l.ne_zero) l.ne_zero)
    choose p hp using hex
    have hpi : Function.Injective p := fun X X' e => Subtype.ext (by rw [← hp X, e, hp X'])
    simp only [hΦ, ← ENNReal.tsum_prod]
    refine le_trans (le_of_eq (tsum_congr fun X => ?_)) (ENNReal.tsum_comp_le_tsum_of_injective hpi _)
    rw [← actW_smul _ _ _ _ (inclR _ _), ← hsm, hp]
  have hm : Measurable Φ := Measurable.ennreal_tsum fun l =>
    (measurable_const.indicator hΩ.measurableSet).comp ((continuous_const_smul _).const_smul t).measurable
  refine h1.trans ((hmain Φ hm (fun l y hl => ?_) (fun j => if (j : ℝ) + Real.log r < x₀ then 0 else
    ENNReal.ofReal (C * Real.exp (2 * Module.finrank ℚ F * ((j : ℝ) + Real.log r)))) (fun j p hp => ?_) L
    (fun X hX => hX.1) fun X hX X' hX' l e => ?_).trans ?_)
  · simp only [hΦ, smul_smul (inclR _ _), ← map_mul]
    exact (Equiv.mulRight (Units.mk0 l hl)).tsum_eq fun l : Eˣ =>
      Ω.indicator (fun _ => (1 : ℝ≥0∞)) (t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) • y)
  · have h2 := hlat ((j : ℝ) + Real.log r)
    rw [Nat.cast_one, mul_one] at h2
    refine le_trans ?_ h2
    let ι : Eˣ → {X : Fin 1 → Fin 1 → E // X ≠ 0} := fun l => ⟨fun _ _ => l, fun h => l.ne_zero (congrFun (congrFun h 0) 0)⟩
    have hι : Function.Injective ι := fun l l' e => Units.ext (congrFun (congrFun (congrArg Subtype.val e) 0) 0)
    refine le_trans (ENNReal.tsum_le_tsum fun l => ?_) (ENNReal.tsum_comp_le_tsum_of_injective hι _)
    by_cases hmem : t • (inclR (F := F) (AF F) (l : E) : AF F ⊗[F] E) •
        ((τ (Multiplicative.ofAdd (-(j : ℝ))) : (AF F ⊗[F] E)ˣ) : AF F ⊗[F] E) • p.1 ∈ Ω
    · rw [Set.indicator_of_mem hmem, Set.indicator_of_mem]
      refine ⟨(p, _), ⟨hp, hmem⟩, funext fun a => funext fun b => ?_⟩
      have h3 := hY1 p hp
      simp only [hR, hform, Pi.smul_apply, smul_eq_mul, ratTup, ι, neg_add, ofAdd_add, map_mul, Units.val_mul,
        ← ht] at h3 ⊢
      rw [← mul_one (_ * _ * _), ← h3, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun j _ => by ring
    · rw [Set.indicator_of_notMem hmem]
      exact zero_le
  · have hl : l ≠ 0 := fun h0 => hX'.1.1 (by rw [e, h0, zero_smul])
    rw [← hX'.2, ← hX.2]
    exact congrArg Quotient.out (Quotient.sound (show R X' X from ⟨Units.mk0 l hl, e.symm⟩))
  · rw [mul_assoc Kc.toReal, ENNReal.ofReal_mul ENNReal.toReal_nonneg, ENNReal.ofReal_toReal hKc.ne]
    exact mul_le_mul_right (hC' r hr) _

end GlobalTheory.CompanionTheory.SW.IsoCount
