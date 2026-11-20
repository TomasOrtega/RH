import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.OneMeasureSizes
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TamagawaSpecialUnitary
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsUnitaryLieBasis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralMultipleInLieLattice
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormCmTypeProductSq
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormTraceFormDetIndexStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieLatticeDualIndex
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalFactorProductBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.GramDiagonalSignatureTracelessBasisStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TprodLocalVolumeFactorLeZetaStatement
open NumberField Formalism.BasicNotions Formalism.MainNotions Formalism.L2 Formalism.L2.DIV Formalism.IndefR.Links Formalism.IndefR.FWT GlobalTheory.CovTop

noncomputable section
namespace GlobalTheory.SUVolLower
open IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol
open scoped ENNReal

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
  haveI : Countable (GL (Fin r) E) := Function.Injective.countable
    (f := fun u : GL (Fin r) E => (u : Matrix (Fin r) (Fin r) E)) (fun a b h => Units.ext h)
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
Take `⟨e, he, hli⟩` from `GlobalTheory.suLie_finrank_ge G hΛ.1 hΛ.2.1`. Use `choose N hN hmem using fun i => GlobalTheory.DenClear.exists_natSmul_mem_lieLat G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2`. Use `⟨fun i => (N i : E) • e i, hmem, ?_⟩` and prove the remaining obligations. Set `w : Fin (r ^ 2 - 1) → (maximalRealSubfield E)ˣ` to `fun i => Units.mk0 (N i : maximalRealSubfield E) (by exact_mod_cast (hN i).ne')`. Establish `hw : (fun i => (N i : E) • e i) = w • e`.

Use function extensionality and compare the values at `i`. Use extensionality with `a b`. Simplify using `[w, Algebra.smul_def]`. Rewrite using `[hw]`. Conclude with `hli.units_smul w`.
-/
theorem exists_lie_basis {E : Type} [Field E] [NumberField E] [IsCMField E] {r : ℕ}
    (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (hΛ : SelfDualLat G Λ) :
    ∃ e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E,
      (∀ i, e i ∈ lieLat G Λ) ∧ LinearIndependent (maximalRealSubfield E) e := by
  obtain ⟨e, he, hli⟩ := GlobalTheory.suLie_finrank_ge G hΛ.1 hΛ.2.1
  choose N hN hmem using fun i => GlobalTheory.DenClear.exists_natSmul_mem_lieLat G Λ hΛ.2.2.1 hΛ.2.2.2.1 (e i) (he i).1 (he i).2
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
Rewrite using `[GlobalTheory.T.gram_diagonal_signature_traceless_basis E r G Ψ x p0 e hr hΛ.2.1 hx (fun i => ⟨(he i).1, (he i).2.1⟩) hli]`. Use `congr 1`. Use `congr 1`. Establish `h1` using `GlobalTheory.cm_type_normSq_prod_eq_abs_norm E Ψ hcm (Matrix.of fun i j => Matrix.trace (e i * e j)).det`. Establish `h2` using `GlobalTheory.T.norm_trace_form_det_index E r G Λ e hr hΛ he hli`.

Establish `h3` using `GlobalTheory.lieLat_relIndex_dual E r G Λ hr hU hΛ`. Rewrite `h2` using `[h3]`. Rewrite `h1` using `[h2]`. Move the coercions through the operations in `at h1`. Establish `hn : ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖ = (r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2` using `(sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1`.

Establish `hs : Real.sqrt ((r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E) = Real.sqrt r ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E`. Rewrite using `[Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by positivity)]`. Rewrite using `[hn, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]`.
-/
theorem riemLie_eq (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E)
    (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ)
    (e : Fin (r ^ 2 - 1) → Matrix (Fin r) (Fin r) E) (hr : 2 ≤ r) (hU : Unr E) (hΛ : SelfDualLat G Λ)
    (hcm : ∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ)
    (hx : ∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) =
      Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ))
    (he : ∀ i, e i ∈ lieLat G Λ) (hli : LinearIndependent (maximalRealSubfield E) e) :
    riemLie Ψ G x = ENNReal.ofReal (Real.sqrt r ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E *
      ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ)) •
      formLie Ψ e := by
  rw [GlobalTheory.T.gram_diagonal_signature_traceless_basis E r G Ψ x p0 e hr hΛ.2.1 hx (fun i => ⟨(he i).1, (he i).2.1⟩) hli]
  congr 1
  congr 1
  have h1 := GlobalTheory.cm_type_normSq_prod_eq_abs_norm E Ψ hcm (Matrix.of fun i j => Matrix.trace (e i * e j)).det
  have h2 := GlobalTheory.T.norm_trace_form_det_index E r G Λ e hr hΛ he hli
  have h3 := GlobalTheory.lieLat_relIndex_dual E r G Λ hr hU hΛ
  rw [h3] at h2
  rw [h2] at h1
  push_cast at h1
  have hn : ‖∏ τ : Ψ, τ.1 (Matrix.of fun i j => Matrix.trace (e i * e j)).det‖ =
      (r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E * ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) ^ 2 :=
    (sq_eq_sq₀ (norm_nonneg _) (by positivity)).1 h1
  have hs : Real.sqrt ((r : ℝ) ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E) = Real.sqrt r ^ ReciprocityTheory.ChartRestriction.G.FD.fdeg E := by
    rw [Real.sqrt_eq_iff_mul_self_eq (by positivity) (by positivity), ← mul_pow, Real.mul_self_sqrt (by positivity)]
  rw [hn, Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), hs]

/- English proof (translation)
Establish `hs2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6)`. Use `(hasSum_nat_add_iff' 1).2 hasSum_zeta_two` as an intermediate fact. Simplify using `using this`. Establish `hsi : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i)`. Use `(summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))` as an intermediate fact.

Simplify using `using this`. Establish `hle : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ Real.pi ^ 2 / 6`. Rewrite using `[← hs2.tsum_eq]`. Use `Summable.tsum_le_tsum (fun n => ?_) hsi hs2.summable` and prove the remaining obligations. Establish `h1 : (1 : ℝ) ≤ (n : ℝ) + 1` using `by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]`.

Conclude with `one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hi)`. Establish `hpi` using `Real.pi_lt_d2`. Establish `hpi0` using `Real.pi_pos`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem zeta_le_two (i : ℕ) (hi : 2 ≤ i) : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ 2 := by
  have hs2 : HasSum (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ 2) (Real.pi ^ 2 / 6) := by
    have := (hasSum_nat_add_iff' 1).2 hasSum_zeta_two
    simpa using this
  have hsi : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
    have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
    simpa using this
  have hle : ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ Real.pi ^ 2 / 6 := by
    rw [← hs2.tsum_eq]
    refine Summable.tsum_le_tsum (fun n => ?_) hsi hs2.summable
    have h1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(n.cast_nonneg : (0 : ℝ) ≤ n)]
    exact one_div_le_one_div_of_le (by positivity) (pow_le_pow_right₀ h1 hi)
  have hpi := Real.pi_lt_d2
  have hpi0 := Real.pi_pos
  nlinarith

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
theorem zprod_le (r : ℕ) : ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ 2 ^ r := by
  calc ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i ≤ ∏ _i ∈ Finset.Icc 2 r, (2 : ℝ) :=
        Finset.prod_le_prod (fun i _ => tsum_nonneg fun n => by positivity)
          fun i hi => zeta_le_two i (Finset.mem_Icc.1 hi).1
    _ = 2 ^ (Finset.Icc 2 r).card := Finset.prod_const _
    _ ≤ 2 ^ r := pow_le_pow_right₀ (by norm_num) (by simp)

/- English proof (translation)
Introduce `hP`. Use `⟨1 / 2, by norm_num, by norm_num, ?_⟩` and prove the remaining obligations. Introduce `E _ _ _ r G Λ Ψ x p0 _ _ J s hr hU hΛ hcm hx hs`. Take `⟨e, he, hli⟩` from `exists_lie_basis G Λ hΛ`. Take `⟨hmult, hP1⟩` from `hP E r G Λ Ψ e J s hr hU hΛ hcm he hli hs`.

Establish `hlie` using `riemLie_eq E r G Λ Ψ x p0 e hr hU hΛ hcm hx he hli`. Establish `hPpos` using `(GlobalTheory.EulerLocVol.tprod_locFactor_bound E r hr hmult).1`. Establish `hPle` using `GlobalTheory.T.tprod_local_volume_factor_le_zeta E r hr hmult`. Use `set f := ReciprocityTheory.ChartRestriction.G.FD.fdeg E with hf`. Use `set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex (lieLat G Λ) : ℝ) with hm`.

Use `set P : ℝ := ∏' v, locFactor E r v with hPdef`. Use `set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD`. Use `set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ`. Use `set n : ℝ := (r : ℝ) ^ 2 - 1 with hn`. Use `set μ := tangentHaar (realSU Ψ G) (formLie Ψ e) with hμ`.

Use `set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ f * m) with hc`. Establish `hD1 : 1 ≤ D`. Rewrite using `[hD]`. Establish `h0 : discr (maximalRealSubfield E) ≠ 0` using `discr_ne_zero _`. Establish `: (1 : ℤ) ≤ |discr (maximalRealSubfield E)|` using `Int.one_le_abs h0`.

Conclude with `this` after adjusting the coercions. Establish `hDpos : 0 < D` using `lt_of_lt_of_le one_pos hD1`. Establish `hm0 : 0 ≤ m` using `Nat.cast_nonneg _`. Establish `hmpos : 0 < m`. Break down `hm0.lt_or_eq with h | h` into its components or cases.

Conclude with `h`. It suffices to derive a contradiction. Rewrite `hP1` using `[← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero]`. Conclude with `zero_ne_one hP1`. Establish `hr1 : (1 : ℝ) ≤ Real.sqrt r`.

Rewrite using `[Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ r)`. Establish `hr0 : 0 < Real.sqrt r` using `lt_of_lt_of_le one_pos hr1`. Establish `hcpos : c ≠ 0`. Rewrite using `[hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]`. Check the signs of the components of the expression.

Establish `hriem : riemHaar Ψ G x = c • μ`. Unfold `riemHaar`. Rewrite using `[hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]`. Establish `hcov : ∀ j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) (riemHaar Ψ G x) = c * covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ`. Introduce `j`.

Use `haveI := countable_inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))`. Rewrite using `[hriem, covolume_smul _ _ hcpos]`. Repeatedly rewrite using `[hcov]`. Rewrite using `[ENNReal.tsum_mul_left]`. Use `set S := ∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ with hS`.

Establish `ha : 0 < D ^ (-n / 2) * m * P` using `by positivity`. Establish `hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹)`. Rewrite using `[ENNReal.ofReal_inv_of_pos ha]`. Conclude with `(ENNReal.eq_inv_of_mul_eq_one_left hP1)`. Rewrite using `[hS1, hc, ← ENNReal.ofReal_mul (by positivity)]`.

Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises. Establish `key : Real.sqrt r ^ f * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ f * P⁻¹`. Rewrite using `[neg_div, Real.rpow_neg hDpos.le]`. Establish `: D ^ (n / 2) ≠ 0` using `(Real.rpow_pos_of_pos hDpos _).ne'`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[key]`. Establish `hn0 : 0 ≤ n / 2`. Rewrite using `[hn]`. Establish `: (4 : ℝ) ≤ (r : ℝ) ^ 2`. Establish `: (2 : ℝ) ≤ r` using `by exact_mod_cast hr`.

Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hDn : 1 ≤ D ^ (n / 2)` using `Real.one_le_rpow hD1 hn0`. Establish `hsr : 1 ≤ Real.sqrt r ^ f` using `one_le_pow₀ hr1`. Establish `hZpos : 0 < Z`.

Use `Finset.prod_pos fun i hi => ?_` and prove the remaining obligations. Establish `hi2 : 2 ≤ i` using `(Finset.mem_Icc.1 hi).1`. Establish `hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i)`. Use `(summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))` as an intermediate fact. Simplify using `using this`.

Use `hs'.le_tsum 0 (fun j _ => by positivity)` as an intermediate fact. Establish `h1 : (0 : ℝ) < 1 / (((0 : ℕ) : ℝ) + 1) ^ i` using `by norm_num`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPinv : (Z ^ f)⁻¹ ≤ P⁻¹` using `inv_anti₀ hPpos hPle`. Establish `hZ2 : Z ^ f ≤ (2 ^ r) ^ f` using `pow_le_pow_left₀ hZpos.le (zprod_le r) f`.

Establish `h2 : ((1 : ℝ) / 2) ^ (f * r ^ 2) ≤ (((2 : ℝ) ^ r) ^ f)⁻¹`. Rewrite using `[← pow_mul, one_div, inv_pow]`. Use `inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ?_)` and prove the remaining obligations. Rewrite using `[mul_comm r f]`. Conclude with `Nat.mul_le_mul_left f (by nlinarith)`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem sum_covolume_ge : GlobalTheory.Published.TamagawaSpecialUnitary → ∃ c : ℝ, 0 < c ∧ c ≤ 1 ∧ ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E) (Λ : Submodule (𝓞 E) (Fin r → E)) (Ψ : Finset (E →+* ℂ)) (x : ReciprocityTheory.ChartRestriction.G.FD.Frame Ψ r) (p0 : Ψ → ℕ) [MeasurableSpace (GlobalTheory.SUVol.realSU Ψ G)] [BorelSpace (GlobalTheory.SUVol.realSU Ψ G)] (J : Type) (s : J → Matrix (Fin r) (Fin r) (GlobalTheory.AdLat.RA (maximalRealSubfield E) E)), 2 ≤ r → GlobalTheory.UCls.Unr E → GlobalTheory.UCls.SelfDualLat G Λ → (∀ τ : E →+* ℂ, τ ∈ Ψ ↔ ComplexEmbedding.conjugate τ ∉ Ψ) → (∀ τ : Ψ, ReciprocityTheory.ChartRestriction.G.FD.gram τ.1 G (ReciprocityTheory.ChartRestriction.G.FD.mat x τ) = Matrix.diagonal fun a : Fin r => ((ReciprocityTheory.ChartRestriction.G.FD.sgn (p0 τ) (a : ℕ) : ℝ) : ℂ)) → GlobalTheory.SUVol.IsSReps G (Λ : Set (Fin r → E)) 1 s → ENNReal.ofReal (c ^ (ReciprocityTheory.ChartRestriction.G.FD.fdeg E * r ^ 2)) ≤ ∑' j, MeasureTheory.covolume (GlobalTheory.SUVol.inReal Ψ G (GlobalTheory.SUVol.ratStab G (Λ : Set (Fin r → E)) (s j))) (GlobalTheory.SUVol.realSU Ψ G) (GlobalTheory.SUVol.riemHaar Ψ G x) := by
  intro hP
  refine ⟨1 / 2, by norm_num, by norm_num, ?_⟩
  intro E _ _ _ r G Λ Ψ x p0 _ _ J s hr hU hΛ hcm hx hs
  obtain ⟨e, he, hli⟩ := exists_lie_basis G Λ hΛ
  obtain ⟨hmult, hP1⟩ := hP E r G Λ Ψ e J s hr hU hΛ hcm he hli hs
  have hlie := riemLie_eq E r G Λ Ψ x p0 e hr hU hΛ hcm hx he hli
  have hPpos := (GlobalTheory.EulerLocVol.tprod_locFactor_bound E r hr hmult).1
  have hPle := GlobalTheory.T.tprod_local_volume_factor_le_zeta E r hr hmult
  set f := ReciprocityTheory.ChartRestriction.G.FD.fdeg E with hf
  set m : ℝ := ((Submodule.span (𝓞 (maximalRealSubfield E)) (Set.range e)).toAddSubgroup.relIndex
    (lieLat G Λ) : ℝ) with hm
  set P : ℝ := ∏' v, locFactor E r v with hPdef
  set D : ℝ := |(discr (maximalRealSubfield E) : ℝ)| with hD
  set Z : ℝ := ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i with hZ
  set n : ℝ := (r : ℝ) ^ 2 - 1 with hn
  set μ := tangentHaar (realSU Ψ G) (formLie Ψ e) with hμ
  set c : ℝ≥0∞ := ENNReal.ofReal (Real.sqrt r ^ f * m) with hc
  have hD1 : 1 ≤ D := by
    rw [hD]
    have h0 : discr (maximalRealSubfield E) ≠ 0 := discr_ne_zero _
    have : (1 : ℤ) ≤ |discr (maximalRealSubfield E)| := Int.one_le_abs h0
    exact_mod_cast this
  have hDpos : 0 < D := lt_of_lt_of_le one_pos hD1
  have hm0 : 0 ≤ m := Nat.cast_nonneg _
  have hmpos : 0 < m := by
    rcases hm0.lt_or_eq with h | h
    · exact h
    · exfalso
      rw [← h, mul_zero, zero_mul, ENNReal.ofReal_zero, mul_zero] at hP1
      exact zero_ne_one hP1
  have hr1 : (1 : ℝ) ≤ Real.sqrt r := by
    rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ r)
  have hr0 : 0 < Real.sqrt r := lt_of_lt_of_le one_pos hr1
  have hcpos : c ≠ 0 := by
    rw [hc, ne_eq, ENNReal.ofReal_eq_zero, not_le]; positivity
  have hriem : riemHaar Ψ G x = c • μ := by
    unfold riemHaar
    rw [hlie, tangentHaar_smul _ _ ENNReal.ofReal_ne_top]
  have hcov : ∀ j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G)
      (riemHaar Ψ G x) = c * covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j)))
      (realSU Ψ G) μ := by
    intro j
    haveI := countable_inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))
    rw [hriem, covolume_smul _ _ hcpos]
  simp_rw [hcov]
  rw [ENNReal.tsum_mul_left]
  set S := ∑' j, covolume (inReal Ψ G (ratStab G (Λ : Set (Fin r → E)) (s j))) (realSU Ψ G) μ with hS
  have ha : 0 < D ^ (-n / 2) * m * P := by positivity
  have hS1 : S = ENNReal.ofReal ((D ^ (-n / 2) * m * P)⁻¹) := by
    rw [ENNReal.ofReal_inv_of_pos ha]
    exact (ENNReal.eq_inv_of_mul_eq_one_left hP1)
  rw [hS1, hc, ← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have key : Real.sqrt r ^ f * m * (D ^ (-n / 2) * m * P)⁻¹ = D ^ (n / 2) * Real.sqrt r ^ f * P⁻¹ := by
    rw [neg_div, Real.rpow_neg hDpos.le]
    have : D ^ (n / 2) ≠ 0 := (Real.rpow_pos_of_pos hDpos _).ne'
    field_simp
  rw [key]
  have hn0 : 0 ≤ n / 2 := by
    rw [hn]
    have : (4 : ℝ) ≤ (r : ℝ) ^ 2 := by
      have : (2 : ℝ) ≤ r := by exact_mod_cast hr
      nlinarith
    linarith
  have hDn : 1 ≤ D ^ (n / 2) := Real.one_le_rpow hD1 hn0
  have hsr : 1 ≤ Real.sqrt r ^ f := one_le_pow₀ hr1
  have hZpos : 0 < Z := by
    refine Finset.prod_pos fun i hi => ?_
    have hi2 : 2 ≤ i := (Finset.mem_Icc.1 hi).1
    have hs' : Summable (fun n : ℕ => 1 / ((n : ℝ) + 1) ^ i) := by
      have := (summable_nat_add_iff 1).2 (Real.summable_one_div_nat_pow.2 (by omega : 1 < i))
      simpa using this
    have := hs'.le_tsum 0 (fun j _ => by positivity)
    have h1 : (0 : ℝ) < 1 / (((0 : ℕ) : ℝ) + 1) ^ i := by norm_num
    linarith
  have hPinv : (Z ^ f)⁻¹ ≤ P⁻¹ := inv_anti₀ hPpos hPle
  have hZ2 : Z ^ f ≤ (2 ^ r) ^ f := pow_le_pow_left₀ hZpos.le (zprod_le r) f
  have h2 : ((1 : ℝ) / 2) ^ (f * r ^ 2) ≤ (((2 : ℝ) ^ r) ^ f)⁻¹ := by
    rw [← pow_mul, one_div, inv_pow]
    refine inv_anti₀ (by positivity) (pow_le_pow_right₀ (by norm_num) ?_)
    rw [mul_comm r f]
    exact Nat.mul_le_mul_left f (by nlinarith)
  calc ((1 : ℝ) / 2) ^ (f * r ^ 2) ≤ (((2 : ℝ) ^ r) ^ f)⁻¹ := h2
    _ ≤ (Z ^ f)⁻¹ := inv_anti₀ (by positivity) hZ2
    _ ≤ P⁻¹ := hPinv
    _ = 1 * 1 * P⁻¹ := by ring
    _ ≤ D ^ (n / 2) * Real.sqrt r ^ f * P⁻¹ := by
        gcongr

end GlobalTheory.SUVolLower
