import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBoundStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RiemannianLieVolumeFormulaStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FormallyUnramifiedRingOfIntegersIffDifferentIdea
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.FinrankEqTwoMulHalfDegree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLatticeStatement
open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

noncomputable section
namespace GlobalTheory.SUVolBound
/- English proof (translation)
The claim follows from `(Module.finBasis ℚ E).equivFun.injective.countable`.
-/
theorem countable_numberField (E : Type) [Field E] [NumberField E] : Countable E :=
  (Module.finBasis ℚ E).equivFun.injective.countable

/- English proof (translation)
Use `haveI := countable_numberField E`. Use `haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))`. Use `haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)`. Establish `hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1`. Introduce and unpack `⟨y, hy⟩`.

Take `⟨γ, -, hγ⟩` from `Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)`. Conclude with `⟨γ, hγ⟩`. Use `choose f hf using hsub`. Use `Function.Injective.countable (f := f) fun a b hab => ?_` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[← hf a, ← hf b, hab]`.
-/
theorem countable_inReal {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ} (Ψ : Finset (E →+* ℂ))
    (G : Matrix (Fin r) (Fin r) E) (Γ : Subgroup (GL (Fin r) E)) : Countable (inReal Ψ G Γ) := by
  haveI := countable_numberField E
  haveI : Countable (Matrix (Fin r) (Fin r) E) := inferInstanceAs (Countable (Fin r → Fin r → E))
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
  have hsub : ∀ y : inReal Ψ G Γ, ∃ γ : GL (Fin r) E, embGL Ψ r γ = (y : realSU Ψ G).1 := by
    rintro ⟨y, hy⟩
    obtain ⟨γ, -, hγ⟩ := Subgroup.mem_map.1 (Subgroup.mem_subgroupOf.1 hy)
    exact ⟨γ, hγ⟩
  choose f hf using hsub
  refine Function.Injective.countable (f := f) fun a b hab => ?_
  apply Subtype.ext; apply Subtype.ext
  rw [← hf a, ← hf b, hab]

/- English proof (translation)
Unfold `tangentHaar`. Rewrite using `[smul_smul]`. Use `congr 1`. Simplify using `only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]`. Conclude with `ENNReal.limsup_const_mul_of_ne_top hc`.
-/
theorem tangentHaar_smul {ι : Type} [Fintype ι] {r : ℕ} (H : Subgroup (ι → GL (Fin r) ℂ)) [LocallyCompactSpace H]
    [MeasurableSpace H] [BorelSpace H] (c : ℝ≥0∞) (hc : c ≠ ⊤) (ν : Measure (ι → Fin r → Fin r → ℂ)) :
    tangentHaar H (c • ν) = c • tangentHaar H ν := by
  unfold tangentHaar
  rw [smul_smul]
  congr 1
  simp only [Measure.smul_apply, smul_eq_mul, mul_div_assoc]
  exact ENNReal.limsup_const_mul_of_ne_top hc

/- English proof (translation)
Distinguish the cases in `h : HasFundamentalDomain G α ν`. Take `⟨s, hs⟩` from `h.ExistsIsFundamentalDomain`. Establish `hs' : IsFundamentalDomain G s (c • ν)` using `hs.mono (Measure.smul_absolutelyContinuous)`. Rewrite using `[hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]`. Establish `h' : ¬ HasFundamentalDomain G α (c • ν)`.

Introduce and unpack `⟨⟨s, hs⟩⟩`. Conclude with `h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩`. Simplify using `[covolume, h, h']`.
-/
theorem covolume_smul {G α : Type*} [Group G] [MulAction G α] [MeasurableSpace α] [Countable G]
    [MeasurableConstSMul G α] (ν : Measure α) [SMulInvariantMeasure G α ν] (c : ℝ≥0∞) (hc : c ≠ 0) :
    covolume G α (c • ν) = c * covolume G α ν := by
  by_cases h : HasFundamentalDomain G α ν
  · obtain ⟨s, hs⟩ := h.ExistsIsFundamentalDomain
    have hs' : IsFundamentalDomain G s (c • ν) := hs.mono (Measure.smul_absolutelyContinuous)
    rw [hs'.covolume_eq_volume, hs.covolume_eq_volume, Measure.smul_apply, smul_eq_mul]
  · have h' : ¬ HasFundamentalDomain G α (c • ν) := by
      rintro ⟨⟨s, hs⟩⟩
      exact h ⟨⟨s, hs.mono (Measure.absolutelyContinuous_smul hc)⟩⟩
    simp [covolume, h, h']

/- English proof (translation)
The claim follows from `|(discr (maximalRealSubfield E) : ℝ)| = rdE E ^ fdeg E := by have hdiff : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ := (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top _ E).1 (by haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := h …`.
-/
theorem abs_discr_real_eq {E : Type} [Field E] [NumberField E] [IsCMField E] (hU : Unr E) :
    |(discr (maximalRealSubfield E) : ℝ)| = rdE E ^ fdeg E := by
  have hdiff : differentIdeal (𝓞 (maximalRealSubfield E)) (𝓞 E) = ⊤ :=
    (GlobalTheory.formallyUnramified_ringOfIntegers_iff_differentIdeal_eq_top _ E).1 (by
      haveI : Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) := hU; infer_instance)
  have h := natAbs_discr_eq_absNorm_differentIdeal_mul_natAbs_discr_pow (maximalRealSubfield E)
    (𝓞 (maximalRealSubfield E)) E (𝓞 E)
  rw [hdiff, Algebra.IsQuadraticExtension.finrank_eq_two] at h
  simp only [Ideal.absNorm_top, one_mul] at h
  have hd : dE E = |(discr (maximalRealSubfield E) : ℝ)| ^ 2 := by
    unfold dE
    rw [← Int.cast_abs, ← Int.cast_abs, Int.abs_eq_natAbs, Int.abs_eq_natAbs, h]
    push_cast; ring
  have hf : 1 ≤ (fdeg E : ℝ) := one_le_field_half_degree
  rw [rootDiscriminant_eq_rpow, hd, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (abs_nonneg _),
    ← Real.rpow_mul (abs_nonneg _)]
  have : (((2 : ℕ) : ℝ) * (1 / (2 * (fdeg E : ℝ))) * (fdeg E : ℝ)) = 1 := by
    field_simp; norm_num
  rw [this, Real.rpow_one]

/- English proof (translation)
Take `⟨e, he, hli⟩` from `GlobalTheory.T.exists_unitary_lie_basis G hΛ.1 hΛ.2.1`. Use `choose N hN hmem using fun i => GlobalTheory.T.integral_multiple_in_lie_lattice G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2`. Use `⟨fun i => (N i : E) • e i, hmem, ?_⟩` and prove the remaining obligations. Set `w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ` to `fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')`. Establish `hw : (fun i => (N i : E) • e i) = w • e`.

Use function extensionality and compare the values at `i`. Use extensionality with `a b`. Simplify using `[w, Algebra.smul_def]`. Rewrite using `[hw]`. Conclude with `hli.units_smul w`.
-/
theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := GlobalTheory.T.exists_unitary_lie_basis G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => GlobalTheory.T.integral_multiple_in_lie_lattice G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
  refine ⟨fun i => (N i : E) • e i, hmem, ?_⟩
  let w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ :=
    fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')
  have hw : (fun i => (N i : E) • e i) = w • e := by
    funext i
    ext a b
    simp [w, Algebra.smul_def]
  rw [hw]
  exact hli.units_smul w

/- English proof (translation)
Introduce `hP E _ _ _ r X Λ x _ _ J s hr hU hΛ hx hs`. Take `⟨e, he, hli⟩` from `exists_lie_basis X.Gm Λ hΛ`. Take `⟨hmult, hP1⟩` from `hP E r X.Gm Λ X.Ψ e J s hr hU hΛ X.cmType he hli hs`. Establish `hlie` using `GlobalTheory.T.riemannian_lie_volume_formula E r X Λ x e hr hU hΛ hx he hli`. Take `⟨hPpos, hPinv⟩` from `GlobalTheory.T.local_factor_product_bound E r hr hmult`.

Use `set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat X.Gm Λ) : ℝ) with hm`. Use `set P : ℝ := ∏' v, locFactor E r v with hPdef`. Use `set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD`. Use `set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ`. Use `set n : ℝ := (r : ℝ) ^ 2 - 1 with hn`.

Use `set μ := tangentHaar (realSU X.Ψ X.Gm) (formLie X.Ψ e) with hμ`. Use `set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ fdeg E * m) with hc`. Establish `hDpos : 0 < D` using `abs_pos.2 (by exact_mod_cast discr_ne_zero _)`. Establish `hm0 : 0 ≤ m` using `Nat.cast_nonneg _`. Establish `hmpos : 0 < m`.

Break down `hm0.lt_or_eq with h | h` into its components or cases. Conclude with `h`. It suffices to derive a contradiction. Rewrite `hP1` using `[← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero]`. Conclude with `zero_ne_one hP1`.

Establish `hr0 : 0 < Real.sqrt r` using `Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))`. Establish `hcpos : c ≠ 0`. Rewrite using `[hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Check the signs of the components of the expression. Establish `hriem : riemHaar X.Ψ X.Gm x = c • μ`.

Unfold `riemHaar`. Rewrite using `[hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]`. Establish `hcov : ∀ j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) = c * covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ`. Introduce `j`. Use `haveI := countable_inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))`.

Rewrite using `[hriem, covolume_smul _ _ hcpos]`. Repeatedly rewrite using `[hcov]`. Rewrite using `[ENNReal.tsum_mul_left]`. Use `set S := ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ with hS`. Establish `ha : 0 < D ^ (-n / 2) * m * P` using `by positivity`.

Establish `hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹)`. Rewrite using `[ENNReal.ofReal_inv_of_pos ha]`. Conclude with `(ENNReal.eq_inv_of_mul_eq_one_left hP1)`. Rewrite using `[hS1, hc, ← ENNReal.ofReal_mul (by positivity)]`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `hDr : D = rdE E ^ fdeg E` using `abs_discr_real_eq hU`. Establish `hrd0 : 0 ≤ rdE E`. Unfold `rdE`. Conclude with `Real.rpow_nonneg (abs_nonneg _) _`. Establish `hDn : D ^ (n / 2) = rdE E ^ ((fdeg E : ℝ) * n / 2)`.

Rewrite using `[hDr, ← Real.rpow_natCast, ← Real.rpow_mul hrd0, mul_div_assoc]`. Establish `key : Real.sqrt r ^ fdeg E * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ fdeg E * P⁻¹`. Rewrite using `[neg_div, Real.rpow_neg hDpos.le]`. Establish `: D ^ (n / 2) ≠ 0` using `(Real.rpow_pos_of_pos hDpos _).ne'`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[key, hDn, mul_pow, mul_assoc]`. Use `gcongr`.
-/
theorem sum_covolume_le : GlobalTheory.Published.TamagawaSpecialUnitary → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (X : Data E r) (Λ : Submodule (𝓞 E) (Fin r → E)) (x : Frame X.Ψ r) [MeasurableSpace (realSU X.Ψ X.Gm)] [BorelSpace (realSU X.Ψ X.Gm)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E)), 2 ≤ r → Unr E → SelfDualLat X.Gm Λ → IsOrth X x → IsSReps X.Gm (Λ : Set (Fin r → E)) 1 s → ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) (riemHaar X.Ψ X.Gm x) ≤ ENNReal.ofReal (rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) * (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E) := by
  intro hP E _ _ _ r X Λ x _ _ J s hr hU hΛ hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis X.Gm Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r X.Gm Λ X.Ψ e J s hr hU hΛ X.cmType he hli hs
  have hlie := GlobalTheory.T.riemannian_lie_volume_formula E r X Λ x e hr hU hΛ hx he hli
  obtain ⟨hPpos, hPinv⟩ := GlobalTheory.T.local_factor_product_bound E r hr hmult
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat X.Gm Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU X.Ψ X.Gm) (formLie X.Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ fdeg E * m) with hc
  have hDpos : 0 < D := abs_pos.2 (by exact_mod_cast discr_ne_zero _)
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr0 : 0 < Real.sqrt r := Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r))
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar X.Ψ X.Gm x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm)
      (riemHaar X.Ψ X.Gm x) = c * covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j)))
      (realSU X.Ψ X.Gm) μ := by
    intro j
    haveI := countable_inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal X.Ψ X.Gm (ratStab X.Gm (Λ : Set (Fin r → E)) (s j))) (realSU X.Ψ X.Gm) μ
    with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have hDr : D = rdE E ^ fdeg E := abs_discr_real_eq hU
  have hrd0 : 0 ≤ rdE E := by
    unfold rdE; exact Real.rpow_nonneg (abs_nonneg _) _
  have hDn : D ^ (n / 2) = rdE E ^ ((fdeg E : ℝ) * n / 2) := by
    rw [hDr, ← Real.rpow_natCast, ← Real.rpow_mul hrd0, mul_div_assoc]
  have key : Real.sqrt r ^ fdeg E * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ fdeg E * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key, hDn, mul_pow, mul_assoc]
  gcongr

end GlobalTheory.SUVolBound
