import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsStableGauss
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.NormGroupSignMulAndNegOne
import GroundTheory.LocalFields.UnramifiedNormSurj
import GroundTheory.LocalFields.UnramifiedGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNonarchimedeanLocalFieldSpectralNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RamificationIndexEqOneOfAdjoinRangeEqTopStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnramifiedQuadraticUniformizerTraceNormStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SpectralNormClosedBallIsOpenIsCompactNhdsBasisAlStatement
open GlobalTheory.JR GlobalTheory.JR.WeilQuad Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.UnramInt
open ValuativeRel GroundTheory.LocalField

/- English proof (translation)
Introduce `F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunr h2 hgen`. Use `haveI : FiniteDimensional F L := Module.Finite.trans K L`. Establish `nmulL : ∀ x y : L, spectralNorm F L (x * y) = spectralNorm F L x * spectralNorm F L y` using `fun x y => map_mul (spectralMulAlgNorm F L) x y`. Establish `npowK : ∀ (x : K) (n : ℕ), spectralNorm F K (x ^ n) = spectralNorm F K x ^ n` using `fun x n => map_pow (spectralMulAlgNorm F K) x n`. Establish `ntow : ∀ a : K, spectralNorm F L (algebraMap K L a) = spectralNorm F K a` using `fun a => (spectralNorm.eq_of_tower a).symm`.

Take `⟨vF, hFloc, hFv⟩` from `NormSign.exists_valuativeRel_of_normed F`. Take `⟨vE, hEloc, hEv⟩` from `NormSign.exists_valuativeRel_of_normed E`. Take `⟨vK, tK, hKloc, hKv⟩` from `GlobalTheory.T.exists_localField_structure_spectralNorm F K`. Take `⟨vL, tL, hLloc, hLv⟩` from `GlobalTheory.T.exists_localField_structure_spectralNorm F L`. Use `haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩`.

Use `haveI : ValuativeExtension F K := ⟨fun a b => by`. Rewrite using `[hKv, hFv, spectralNorm_extends, spectralNorm_extends]⟩`. Use `haveI : ValuativeExtension K L := ⟨fun a b => by rw [hLv, hKv, ntow, ntow]⟩`. Establish `heF : ramificationIndex F E = 1`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[E]`.

Take `⟨x, hx⟩` from `hunr (ϖ : E)`. Establish `h1 : (ϖ : E) ≤ᵥ algebraMap F E x` using `by rw [hEv, norm_algebraMap', hx]`. Establish `h2 : algebraMap F E x ≤ᵥ (ϖ : E)` using `by rw [hEv, norm_algebraMap', hx]`. Establish `hv : valuation E (ϖ : E) = valuation E (algebraMap F E x)` using `le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)`. Establish `hord : ord (ϖ : E) = ord (algebraMap F E x)`.

Simplify using `only [ord]`. Rewrite using `[(normalizedValuation_eq_iff (K := E)).2 hv]`. Rewrite `hord` using `[ord_uniformizer hϖ, ord_algebraMap]`. Establish `hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1` using `⟨ord x, hord⟩`. Conclude with `Int.eq_one_of_dvd_one (by positivity) hd` after adjusting the coercions.

Establish `heKL` using `GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt F E K L heF hgen`. Take `⟨ϖ, hϖ0, hϖ1, hϖ1', hN, hunif, htr, hnrm⟩` from `GlobalTheory.T.unramified_quadratic_norm_trace_surjective K L heKL h2`. Establish `hleL : ∀ y : L, y ≤ᵥ 1 ↔ spectralNorm F L y ≤ 1` using `fun y => by rw [hLv, spectralNorm_one]`. Establish `hleK : ∀ s : K, s ≤ᵥ 1 ↔ spectralNorm F K s ≤ 1` using `fun s => by rw [hKv, spectralNorm_one]`. Establish `hgeK : ∀ s : K, (1 : K) ≤ᵥ s ↔ 1 ≤ spectralNorm F K s` using `fun s => by rw [hKv, spectralNorm_one]`.

Establish `hϖlt : spectralNorm F K ϖ < 1` using `lt_of_not_ge fun h => hϖ1' ((hgeK ϖ).2 h)`. Set `O : Subring L` to `{ carrier := {y | spectralNorm F L y ≤ 1} mul_mem' := fun {a b} ha hb => by`. Simplify using `only [Set.mem_setOf_eq] at *`. Rewrite using `[nmulL]`. Conclude with `mul_le_one₀ ha (spectralNorm_nonneg _) hb`.

Use the proof step `one_mem' := by simp [spectralNorm_one]`. Use the proof step `add_mem' := fun {a b} ha hb => (isNonarchimedean_spectralNorm a b).trans (max_le ha hb)`. Use the proof step `zero_mem' := by simp [spectralNorm_zero]`. Use the proof step `neg_mem' := fun {a} ha => by`. Simplify using `only [Set.mem_setOf_eq] at *`.

Rewrite using `[spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)] }` and apply the resulting hypothesis. Establish `hmem : ∀ y : L, y ∈ O ↔ y ≤ᵥ 1` using `fun y => (hleL y).symm`. Use `⟨Units.mk0 ϖ hϖ0, O, rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show spectralNorm F L _ ≤ 1`. Rewrite using `[Units.val_mk0, ntow]`.

Conclude with `hϖlt.le`. Introduce and unpack `⟨z, hz, hz1⟩`. Establish `h` using `congrArg (spectralNorm F L) hz1`. Rewrite `h` using `[nmulL, spectralNorm_one, Units.val_mk0, ntow]`. Establish `hz' : spectralNorm F L z ≤ 1` using `hz`.

Establish `: spectralNorm F K ϖ * spectralNorm F L z < 1` using `lt_of_le_of_lt (mul_le_of_le_one_right (spectralNorm_nonneg _) hz') hϖlt`. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `y hy`. Break down `hunif y ((hmem y).1 hy) with ⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩` into its components or cases. Conclude with `Or.inl ⟨z, (hmem z).2 hz, by rw [Units.val_mk0]; exact hyz⟩`.

Conclude with `Or.inr ⟨z, (hmem z).2 hz, hyz⟩`. Introduce `s hs`. Establish `hs' : s ≤ᵥ 1`. Rewrite using `[hleK, ← ntow]`. Conclude with `hs`.

Take `⟨z, hz, hzs⟩` from `htr s hs'`. Conclude with `⟨z, (hmem z).2 hz, hzs⟩`. Introduce and unpack `s hs ⟨r, hr, hsr⟩`. Establish `hs1 : spectralNorm F K s ≤ 1` using `by rw [← ntow]; exact hs`. Establish `hr1 : spectralNorm F L r ≤ 1` using `hr`.

Establish `h` using `congrArg (spectralNorm F L) hsr`. Rewrite `h` using `[nmulL, spectralNorm_one, ntow]`. Establish `hge : 1 ≤ spectralNorm F K s`. Use polynomial arithmetic with `[spectralNorm_nonneg (K := F) s, spectralNorm_nonneg (K := F) r]`. Take `⟨w, hw, hws⟩` from `hnrm s ((hleK s).2 hs1) ((hgeK s).2 hge)`.

Conclude with `⟨w, (hmem w).2 hw, hws⟩`. Introduce `r hr`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one hr hϖlt`. Use `⟨n, fun z hz => ?_⟩` and prove the remaining obligations. Establish `hz' : spectralNorm F L z ≤ 1` using `hz`.

Rewrite using `[nmulL, ntow, Units.val_mk0, npowK]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (spectralNorm_nonneg _) _) hz') hn`. Introduce `y`. Distinguish the cases in `hy : spectralNorm F L y ≤ 1`. Use `⟨0, ?_⟩ show spectralNorm F L _ ≤ 1` and prove the remaining obligations.

Simplify using `using hy`. Establish `hpos : 0 < spectralNorm F L y` using `lt_of_lt_of_le one_pos (le_of_not_ge hy)`. Take `⟨n, hn⟩` from `exists_pow_lt_of_lt_one (inv_pos.2 hpos) hϖlt`. Use `⟨n, ?_⟩` and prove the remaining obligations. Use `show spectralNorm F L _ ≤ 1`.

Rewrite using `[nmulL, ntow, Units.val_mk0, npowK]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem alg_main : ∀ (F E K L : Type) [NontriviallyNormedField F] [IsUltrametricDist F] [CompleteSpace F]
    [LocallyCompactSpace F] [NontriviallyNormedField E] [NormedAlgebra F E] [IsUltrametricDist E]
    [LocallyCompactSpace E] [Field K] [Field L] [Algebra F K] [Algebra F L] [Algebra K L] [Algebra E L]
    [IsScalarTower F K L] [IsScalarTower F E L] [FiniteDimensional F K] [FiniteDimensional F E]
    [FiniteDimensional K L],
    (∀ y : E, ∃ x : F, ‖y‖ = ‖x‖) → Module.finrank K L = 2 →
    Algebra.adjoin K (Set.range (algebraMap E L)) = ⊤ →
    ∃ (ϖ : Kˣ) (O : Subring L), (O : Set L) = {y | spectralNorm F L y ≤ 1} ∧
      (¬ ∃ y : L, Algebra.norm K y = (ϖ : K)) ∧ algebraMap K L (ϖ : K) ∈ O ∧
      (¬ ∃ z ∈ O, algebraMap K L (ϖ : K) * z = 1) ∧
      (∀ y ∈ O, (∃ z ∈ O, y = algebraMap K L (ϖ : K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧
      (∀ s : K, algebraMap K L s ∈ O → ∃ z ∈ O, Algebra.trace K L z = s) ∧
      (∀ s : K, algebraMap K L s ∈ O → (∃ r ∈ O, algebraMap K L s * r = 1) → ∃ w ∈ O, Algebra.norm K w = s) ∧
      (∀ r : ℝ, 0 < r → ∃ n : ℕ, ∀ z ∈ O, spectralNorm F L (algebraMap K L ((ϖ : K) ^ n) * z) < r) ∧
      ∀ y : L, ∃ n : ℕ, algebraMap K L ((ϖ : K) ^ n) * y ∈ O := by
  intro F E K L _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ hunr h2 hgen
  haveI : FiniteDimensional F L := Module.Finite.trans K L
  have nmulL : ∀ x y : L, spectralNorm F L (x * y) = spectralNorm F L x * spectralNorm F L y :=
    fun x y => map_mul (spectralMulAlgNorm F L) x y
  have npowK : ∀ (x : K) (n : ℕ), spectralNorm F K (x ^ n) = spectralNorm F K x ^ n :=
    fun x n => map_pow (spectralMulAlgNorm F K) x n
  have ntow : ∀ a : K, spectralNorm F L (algebraMap K L a) = spectralNorm F K a :=
    fun a => (spectralNorm.eq_of_tower a).symm
  obtain ⟨vF, hFloc, hFv⟩ := NormSign.exists_valuativeRel_of_normed F
  obtain ⟨vE, hEloc, hEv⟩ := NormSign.exists_valuativeRel_of_normed E
  obtain ⟨vK, tK, hKloc, hKv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F K
  obtain ⟨vL, tL, hLloc, hLv⟩ := GlobalTheory.T.exists_localField_structure_spectralNorm F L
  haveI : ValuativeExtension F E := ⟨fun a b => by rw [hEv, hFv, norm_algebraMap', norm_algebraMap']⟩
  haveI : ValuativeExtension F K := ⟨fun a b => by
    rw [hKv, hFv, spectralNorm_extends, spectralNorm_extends]⟩
  haveI : ValuativeExtension K L := ⟨fun a b => by rw [hLv, hKv, ntow, ntow]⟩
  have heF : ramificationIndex F E = 1 := by
    obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[E]
    obtain ⟨x, hx⟩ := hunr (ϖ : E)
    have h1 : (ϖ : E) ≤ᵥ algebraMap F E x := by rw [hEv, norm_algebraMap', hx]
    have h2 : algebraMap F E x ≤ᵥ (ϖ : E) := by rw [hEv, norm_algebraMap', hx]
    have hv : valuation E (ϖ : E) = valuation E (algebraMap F E x) :=
      le_antisymm ((Valuation.Compatible.vle_iff_le _ _).1 h1) ((Valuation.Compatible.vle_iff_le _ _).1 h2)
    have hord : ord (ϖ : E) = ord (algebraMap F E x) := by
      simp only [ord]
      rw [(normalizedValuation_eq_iff (K := E)).2 hv]
    rw [ord_uniformizer hϖ, ord_algebraMap] at hord
    have hd : ((ramificationIndex F E : ℕ) : ℤ) ∣ 1 := ⟨ord x, hord⟩
    exact_mod_cast Int.eq_one_of_dvd_one (by positivity) hd
  have heKL := GlobalTheory.T.ramificationIndex_eq_one_of_adjoin_range_eq_top_alt F E K L heF hgen
  obtain ⟨ϖ, hϖ0, hϖ1, hϖ1', hN, hunif, htr, hnrm⟩ := GlobalTheory.T.unramified_quadratic_norm_trace_surjective K L heKL h2
  have hleL : ∀ y : L, y ≤ᵥ 1 ↔ spectralNorm F L y ≤ 1 := fun y => by rw [hLv, spectralNorm_one]
  have hleK : ∀ s : K, s ≤ᵥ 1 ↔ spectralNorm F K s ≤ 1 := fun s => by rw [hKv, spectralNorm_one]
  have hgeK : ∀ s : K, (1 : K) ≤ᵥ s ↔ 1 ≤ spectralNorm F K s := fun s => by rw [hKv, spectralNorm_one]
  have hϖlt : spectralNorm F K ϖ < 1 := lt_of_not_ge fun h => hϖ1' ((hgeK ϖ).2 h)
  let O : Subring L :=
    { carrier := {y | spectralNorm F L y ≤ 1}
      mul_mem' := fun {a b} ha hb => by
        simp only [Set.mem_setOf_eq] at *
        rw [nmulL]
        exact mul_le_one₀ ha (spectralNorm_nonneg _) hb
      one_mem' := by simp [spectralNorm_one]
      add_mem' := fun {a b} ha hb => (isNonarchimedean_spectralNorm a b).trans (max_le ha hb)
      zero_mem' := by simp [spectralNorm_zero]
      neg_mem' := fun {a} ha => by
        simp only [Set.mem_setOf_eq] at *
        rwa [spectralNorm_neg (Algebra.IsAlgebraic.isAlgebraic a)] }
  have hmem : ∀ y : L, y ∈ O ↔ y ≤ᵥ 1 := fun y => (hleL y).symm
  refine ⟨Units.mk0 ϖ hϖ0, O, rfl, hN, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · show spectralNorm F L _ ≤ 1
    rw [Units.val_mk0, ntow]
    exact hϖlt.le
  · rintro ⟨z, hz, hz1⟩
    have h := congrArg (spectralNorm F L) hz1
    rw [nmulL, spectralNorm_one, Units.val_mk0, ntow] at h
    have hz' : spectralNorm F L z ≤ 1 := hz
    have : spectralNorm F K ϖ * spectralNorm F L z < 1 :=
      lt_of_le_of_lt (mul_le_of_le_one_right (spectralNorm_nonneg _) hz') hϖlt
    linarith
  · intro y hy
    rcases hunif y ((hmem y).1 hy) with ⟨z, hz, hyz⟩ | ⟨z, hz, hyz⟩
    · exact Or.inl ⟨z, (hmem z).2 hz, by rw [Units.val_mk0]; exact hyz⟩
    · exact Or.inr ⟨z, (hmem z).2 hz, hyz⟩
  · intro s hs
    have hs' : s ≤ᵥ 1 := by
      rw [hleK, ← ntow]
      exact hs
    obtain ⟨z, hz, hzs⟩ := htr s hs'
    exact ⟨z, (hmem z).2 hz, hzs⟩
  · rintro s hs ⟨r, hr, hsr⟩
    have hs1 : spectralNorm F K s ≤ 1 := by rw [← ntow]; exact hs
    have hr1 : spectralNorm F L r ≤ 1 := hr
    have h := congrArg (spectralNorm F L) hsr
    rw [nmulL, spectralNorm_one, ntow] at h
    have hge : 1 ≤ spectralNorm F K s := by
      nlinarith [spectralNorm_nonneg (K := F) s, spectralNorm_nonneg (K := F) r]
    obtain ⟨w, hw, hws⟩ := hnrm s ((hleK s).2 hs1) ((hgeK s).2 hge)
    exact ⟨w, (hmem w).2 hw, hws⟩
  · intro r hr
    obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one hr hϖlt
    refine ⟨n, fun z hz => ?_⟩
    have hz' : spectralNorm F L z ≤ 1 := hz
    rw [nmulL, ntow, Units.val_mk0, npowK]
    exact lt_of_le_of_lt (mul_le_of_le_one_right (pow_nonneg (spectralNorm_nonneg _) _) hz') hn
  · intro y
    by_cases hy : spectralNorm F L y ≤ 1
    · refine ⟨0, ?_⟩
      show spectralNorm F L _ ≤ 1
      simpa using hy
    · have hpos : 0 < spectralNorm F L y := lt_of_lt_of_le one_pos (le_of_not_ge hy)
      obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (inv_pos.2 hpos) hϖlt
      refine ⟨n, ?_⟩
      show spectralNorm F L _ ≤ 1
      rw [nmulL, ntow, Units.val_mk0, npowK]
      calc spectralNorm F K ϖ ^ n * spectralNorm F L y ≤ (spectralNorm F L y)⁻¹ * spectralNorm F L y :=
            mul_le_mul_of_nonneg_right hn.le (spectralNorm_nonneg _)
        _ = 1 := inv_mul_cancel₀ hpos.ne'

end GlobalTheory.JR.UnramInt

namespace GlobalTheory.JR.UnramInt

/- English proof (translation)
Introduce `F E _ _ _ _ U A hK hL`. Use `letI : Field A.K := hK.toField`. Use `letI : Field A.L := hL.toField`. Use `haveI := U.ultraF`. Use `haveI := U.ultraE`.

Use `haveI := U.lcF`. Use `haveI := U.lcE`. Use `haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`. Use `haveI : CompleteSpace F := complete_of_proper`. Use `haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ U.finrank_eq`.

Establish `hKL : Module.finrank A.K A.L = 2` using `by haveI := A.push.symm`. Rewrite using `[← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange, U.finrank_eq]`. Use `haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL`. Use `haveI : FiniteDimensional F A.L := Module.Finite.trans A.K A.L`. Establish `hgen : Algebra.adjoin A.K (Set.range (algebraMap E A.L)) = ⊤` using `by haveI := A.push.symm`.

Rewrite using `[eq_top_iff]`. Introduce `y _`. Take `⟨t, rfl⟩` from `(Algebra.IsPushout.equiv F A.K E A.L).surjective y`. Proceed by induction on `t using TensorProduct.induction_on with`. Consider the case `zero => simp`.

Consider the case `tmul k e`. Rewrite using `[Algebra.IsPushout.equiv_tmul]`. Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (Algebra.subset_adjoin ⟨e, rfl⟩)`. Consider the case `add a b ha hb`. Rewrite using `[map_add]`.

Conclude with `Subalgebra.add_mem _ (ha trivial) (hb trivial)`. Take `⟨ϖ, O, hO, hN, hϖO, hϖu, hunif, htr, hnrm, hsmall, hbig⟩` from `alg_main F E A.K A.L (fun y => U.unram y) hKL hgen`. Take `⟨hop, hcp, hball⟩` from `GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds F A.L`. Establish `hmem : ∀ y : A.L, y ∈ O ↔ spectralNorm F A.L y ≤ 1` using `fun y => by`. Rewrite using `[← SetLike.mem_coe, hO]`.

Both sides reduce to the same expression. Use `⟨ϖ, O, by rw [hO]; exact hop, by rw [hO]; exact hcp, ?_, hN, hϖO, hϖu, hunif, htr, hnrm, ?_, hbig⟩` and prove the remaining obligations. Introduce `y hy`. Establish `hσ : ∀ x : F, starRingAut (algebraMap F A.L x) = algebraMap F A.L x` using `fun x => by`. Rewrite using `[starRingAut_apply, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]`.

Set `σ : A.L ≃ₐ[F] A.L` to `AlgEquiv.ofRingEquiv (f := starRingAut) hσ`. Establish `h` using `spectralNorm_eq_of_equiv σ y`. Rewrite `hy`, the goal using `[hmem]`. Establish `hs : σ y = star y` using `rfl`. Rewrite `h` using `[hs]`.

Rewrite using `[← h]`. Conclude with `hy`. Introduce `V hV`. Take `⟨r, hr, hrV⟩` from `hball V hV`. Take `⟨n, hn⟩` from `hsmall r hr`.

Conclude with `⟨n, fun z hz => hrV _ (hn z hz)⟩`.
-/
theorem main : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E), IsField A.K → IsField A.L → ∃ (ϖ : A.Kˣ) (O : Subring A.L), IsOpen (O : Set A.L) ∧ IsCompact (O : Set A.L) ∧ (∀ y ∈ O, star y ∈ O) ∧ (¬ ∃ y, A.NL y = (ϖ : A.K)) ∧ algebraMap A.K A.L (ϖ : A.K) ∈ O ∧ (¬ ∃ z ∈ O, algebraMap A.K A.L (ϖ : A.K) * z = 1) ∧ (∀ y ∈ O, (∃ z ∈ O, y = algebraMap A.K A.L (ϖ : A.K) * z) ∨ ∃ z ∈ O, y * z = 1) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → ∃ z ∈ O, Algebra.trace A.K A.L z = s) ∧ (∀ s : A.K, algebraMap A.K A.L s ∈ O → (∃ r ∈ O, algebraMap A.K A.L s * r = 1) → ∃ w ∈ O, A.NL w = s) ∧ (∀ U ∈ 𝓝 (0 : A.L), ∃ n : ℕ, ∀ z ∈ O, algebraMap A.K A.L ((ϖ : A.K) ^ n) * z ∈ U) ∧ ∀ y : A.L, ∃ n : ℕ, algebraMap A.K A.L ((ϖ : A.K) ^ n) * y ∈ O := by
  intro F E _ _ _ _ U A hK hL
  letI : Field A.K := hK.toField
  letI : Field A.L := hL.toField
  haveI := U.ultraF
  haveI := U.ultraE
  haveI := U.lcF
  haveI := U.lcE
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : CompleteSpace F := complete_of_proper
  haveI : FiniteDimensional F E := Module.finite_of_finrank_eq_succ U.finrank_eq
  have hKL : Module.finrank A.K A.L = 2 := by
    haveI := A.push.symm
    rw [← (Algebra.IsPushout.equiv F A.K E A.L).toLinearEquiv.finrank_eq, Module.finrank_baseChange,
      U.finrank_eq]
  haveI : FiniteDimensional A.K A.L := Module.finite_of_finrank_eq_succ hKL
  haveI : FiniteDimensional F A.L := Module.Finite.trans A.K A.L
  have hgen : Algebra.adjoin A.K (Set.range (algebraMap E A.L)) = ⊤ := by
    haveI := A.push.symm
    rw [eq_top_iff]
    intro y _
    obtain ⟨t, rfl⟩ := (Algebra.IsPushout.equiv F A.K E A.L).surjective y
    induction t using TensorProduct.induction_on with
    | zero => simp
    | tmul k e =>
      rw [Algebra.IsPushout.equiv_tmul]
      exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ k) (Algebra.subset_adjoin ⟨e, rfl⟩)
    | add a b ha hb =>
      rw [map_add]
      exact Subalgebra.add_mem _ (ha trivial) (hb trivial)
  obtain ⟨ϖ, O, hO, hN, hϖO, hϖu, hunif, htr, hnrm, hsmall, hbig⟩ :=
    alg_main F E A.K A.L (fun y => U.unram y) hKL hgen
  obtain ⟨hop, hcp, hball⟩ := GlobalTheory.T.spectralNorm_closedBall_isOpen_isCompact_nhds F A.L
  have hmem : ∀ y : A.L, y ∈ O ↔ spectralNorm F A.L y ≤ 1 := fun y => by
    rw [← SetLike.mem_coe, hO]
    rfl
  refine ⟨ϖ, O, by rw [hO]; exact hop, by rw [hO]; exact hcp, ?_, hN, hϖO, hϖu, hunif, htr, hnrm, ?_, hbig⟩
  · intro y hy
    have hσ : ∀ x : F, starRingAut (algebraMap F A.L x) = algebraMap F A.L x := fun x => by
      rw [starRingAut_apply, IsScalarTower.algebraMap_apply F A.K A.L, A.star_K]
    let σ : A.L ≃ₐ[F] A.L := AlgEquiv.ofRingEquiv (f := starRingAut) hσ
    have h := spectralNorm_eq_of_equiv σ y
    rw [hmem] at hy ⊢
    have hs : σ y = star y := rfl
    rw [hs] at h
    rw [← h]
    exact hy
  · intro V hV
    obtain ⟨r, hr, hrV⟩ := hball V hV
    obtain ⟨n, hn⟩ := hsmall r hr
    exact ⟨n, fun z hz => hrV _ (hn z hz)⟩

end GlobalTheory.JR.UnramInt
