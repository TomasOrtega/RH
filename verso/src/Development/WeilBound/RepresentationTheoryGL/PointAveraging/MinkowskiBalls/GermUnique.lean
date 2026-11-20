import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.GermIntegrals.StepSt

open MeasureTheory GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil GlobalTheory.ThetaGL ValuativeRel PositivityTheory.Tls2.Ming3
open scoped Topology Pointwise

set_option linter.unusedSectionVars false

noncomputable section

namespace PositivityTheory.Rg.Ming.UniqX

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Use extensionality with `y`. Establish `hc : 0 < valuation k (c : k)`. Rewrite using `[zero_lt_iff]`. Simplify using the standard rewrite rules. Simplify using `only [Set.mem_setOf_eq, Set.mem_preimage]`.

Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def, Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, neg_add_eq_sub, inv_mul_le_one₀ hc]`.
-/
theorem valSet_eq (a : k) (c : kˣ) :
    {y : k | valuation k (y - a) ≤ valuation k (c : k)} = (fun y => -a + y) ⁻¹' (c • (𝒪[k] : Set k)) := by
  ext y
  have hc : 0 < valuation k (c : k) := by
    rw [zero_lt_iff]; simp
  simp only [Set.mem_setOf_eq, Set.mem_preimage]
  rw [Set.mem_smul_set_iff_inv_smul_mem, SetLike.mem_coe, Valuation.mem_integer_iff, Units.smul_def,
    Units.val_inv_eq_inv_val, smul_eq_mul, map_mul, map_inv₀, neg_add_eq_sub, inv_mul_le_one₀ hc]

/- English proof (translation)
Rewrite using `[valSet_eq]`. Conclude with `(Valuation.isOpen_integer.smul c).preimage (continuous_const.add continuous_id)`.
-/
theorem isOpen_valSet (a : k) (c : kˣ) : IsOpen {y : k | valuation k (y - a) ≤ valuation k (c : k)} := by
  rw [valSet_eq]
  exact (Valuation.isOpen_integer.smul c).preimage (continuous_const.add continuous_id)

/- English proof (translation)
Take `⟨hH, h1⟩` from `hν`. Use `haveI := hH`. Use `haveI : SecondCountableTopology k := by exact secondCountable k`. Rewrite using `[valSet_eq, measure_preimage_add, ← distribHaarChar_mul, h1, mul_one, nabs, ENNReal.ofReal_coe_nnreal]`.
-/
theorem vol_valSet [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (a : k) (c : kˣ) :
    ν {y : k | valuation k (y - a) ≤ valuation k (c : k)} = ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [valSet_eq, measure_preimage_add, ← distribHaarChar_mul, h1, mul_one, nabs, ENNReal.ofReal_coe_nnreal]

variable {n r : ℕ}

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [ballM, Set.mem_setOf_eq]`. Prove the components needed by the constructor for the conclusion. Introduce `h i _ l _`. Conclude with `h i l`.

Introduce `h i l`. Conclude with `h i (Set.mem_univ _) l (Set.mem_univ _)`.
-/
theorem ballM_eq_pi (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    (ballM c x₀ : Set (Matrix (Fin n) (Fin r) k)) =
      (Set.univ.pi fun i => Set.univ.pi fun l => {y : k | valuation k (y - x₀ i l) ≤ valuation k (c : k)} :
        Set (Fin n → Fin r → k)) := by
  ext x
  simp only [ballM, Set.mem_setOf_eq]
  constructor
  · intro h i _ l _
    exact h i l
  · intro h i l
    exact h i (Set.mem_univ _) l (Set.mem_univ _)

/- English proof (translation)
Rewrite using `[ballM_eq_pi]`. Conclude with `MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet`.
-/
theorem measurableSet_ballM [MeasurableSpace k] [BorelSpace k] (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    MeasurableSet (ballM c x₀) := by
  rw [ballM_eq_pi]
  exact MeasurableSet.univ_pi fun i => MeasurableSet.univ_pi fun l => (isOpen_valSet _ c).measurableSet

/- English proof (translation)
Take `⟨hH, h1⟩` from `hν`. Use `haveI := hH`. Use `haveI : SecondCountableTopology k := by exact secondCountable k`. Rewrite using `[volM, ballM_eq_pi]`. Use `erw [Measure.pi_pi]`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Measure.pi_pi]`. Conclude with `Finset.prod_congr rfl fun l _ => vol_valSet ν ⟨hH, h1⟩ (x₀ i l) c`.
-/
theorem volM_ballM [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) :
    volM ν (Fin n) (Fin r) (ballM c x₀) = ∏ _i : Fin n, ∏ _l : Fin r, ENNReal.ofReal (nabs k c) := by
  obtain ⟨hH, h1⟩ := hν
  haveI := hH
  haveI : SecondCountableTopology k := by exact secondCountable k
  rw [volM, ballM_eq_pi]
  erw [Measure.pi_pi]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [Measure.pi_pi]
  exact Finset.prod_congr rfl fun l _ => vol_valSet ν ⟨hH, h1⟩ (x₀ i l) c

/- English proof (translation)
Establish `hpos : 0 < nabs k c`. Unfold `nabs`. Establish `h : distribHaarChar k c * distribHaarChar k c⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `hne : distribHaarChar k c ≠ 0` using `left_ne_zero_of_mul_eq_one h`.

Conclude with `pos_iff_ne_zero.2 hne` after adjusting the coercions. Rewrite using `[volM_ballM ν hν, ENNReal.toReal_prod]`. Use `Finset.prod_ne_zero_iff.2 fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.toReal_prod]`. Use `Finset.prod_ne_zero_iff.2 fun l _ => ?_` and prove the remaining obligations.

Rewrite using `[ENNReal.toReal_ofReal hpos.le]`. Conclude with `hpos.ne'`.
-/
theorem volM_ballM_ne_zero [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν) (c : kˣ)
    (x₀ : Matrix (Fin n) (Fin r) k) : (volM ν (Fin n) (Fin r) (ballM c x₀)).toReal ≠ 0 := by
  have hpos : 0 < nabs k c := by
    unfold nabs
    have h : distribHaarChar k c * distribHaarChar k c⁻¹ = 1 := by
      rw [← map_mul, mul_inv_cancel, map_one]
    have hne : distribHaarChar k c ≠ 0 := left_ne_zero_of_mul_eq_one h
    exact_mod_cast pos_iff_ne_zero.2 hne
  rw [volM_ballM ν hν, ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun i _ => ?_
  rw [ENNReal.toReal_prod]
  refine Finset.prod_ne_zero_iff.2 fun l _ => ?_
  rw [ENNReal.toReal_ofReal hpos.le]
  exact hpos.ne'

/- English proof (translation)
Rewrite using `[integral_indicator_const _ (measurableSet_ballM c x₀)]`. Simplify using `[Measure.real]`.
-/
theorem integral_ind [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (c : kˣ) (x₀ : Matrix (Fin n) (Fin r) k) :
    ∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r) =
      ((volM ν (Fin n) (Fin r) (ballM c x₀)).toReal : ℂ) := by
  rw [integral_indicator_const _ (measurableSet_ballM c x₀)]
  simp [Measure.real]

/- English proof (translation)
Introduce `_ hx i l` and use `(hx i l).trans hle`.
-/
theorem ballM_mono {c c' : kˣ} (hle : valuation k (c : k) ≤ valuation k (c' : k))
    {x₀ : Matrix (Fin n) (Fin r) k} : ballM c x₀ ⊆ ballM c' x₀ :=
  fun _ hx i l => (hx i l).trans hle

/- English proof (translation)
Break down `le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h | h` into its components or cases. Conclude with `⟨c₁, le_rfl, h⟩`. Conclude with `⟨c₂, h, le_rfl⟩`.
-/
theorem exists_le_both (c₁ c₂ : kˣ) :
    ∃ c : kˣ, valuation k (c : k) ≤ valuation k (c₁ : k) ∧ valuation k (c : k) ≤ valuation k (c₂ : k) := by
  rcases le_total (valuation k (c₁ : k)) (valuation k (c₂ : k)) with h | h
  · exact ⟨c₁, le_rfl, h⟩
  · exact ⟨c₂, h, le_rfl⟩

variable {V W : Type} [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, fun Φ _ => by simp⟩`.
-/
theorem germ_zero [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) : IsGerm ν B x₀ 0 0 :=
  ⟨1, fun Φ _ => by simp⟩

/- English proof (translation)
Take `⟨c₁, e₁⟩` from `h₁`. Take `⟨c₂, e₂⟩` from `h₂`. Take `⟨c, hc₁, hc₂⟩` from `exists_le_both c₁ c₂`. Use `⟨c, fun Φ hΦ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_smul, e₁ Φ (fun x hx => ballM_mono hc₁ (hΦ x hx)), e₂ Φ (fun x hx => ballM_mono hc₂ (hΦ x hx)), smul_add, smul_comm a]`.
-/
theorem germ_comb [MeasurableSpace k] (ν : Measure k) (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V)
    (x₀ : Matrix (Fin n) (Fin r) k) (a : ℂ) {w₁ w₂ : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w₁ v₁) (h₂ : IsGerm ν B x₀ w₂ v₂) : IsGerm ν B x₀ (a • w₁ + w₂) (a • v₁ + v₂) := by
  obtain ⟨c₁, e₁⟩ := h₁
  obtain ⟨c₂, e₂⟩ := h₂
  obtain ⟨c, hc₁, hc₂⟩ := exists_le_both c₁ c₂
  refine ⟨c, fun Φ hΦ => ?_⟩
  rw [map_add, map_smul, e₁ Φ (fun x hx => ballM_mono hc₁ (hΦ x hx)),
    e₂ Φ (fun x hx => ballM_mono hc₂ (hΦ x hx)), smul_add, smul_comm a]

/- English proof (translation)
Take `⟨c₁, hc₁⟩` from `h₁`. Take `⟨c₂, hc₂⟩` from `h₂`. Take `⟨c, hle₁, hle₂⟩` from `exists_le_both c₁ c₂`. Set `Φ : SB (Matrix (Fin n) (Fin r) k)` to `⟨(ballM c x₀).indicator fun _ => (1 : ℂ), ((hb k n r).1 c x₀).2.2.1⟩`. Establish `hsupp : ∀ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 → x ∈ ballM c x₀`.

Introduce `x hx`. Assume the negation of the conclusion as `h`. Conclude with `hx (by simp [Φ, Set.indicator, h])`. Establish `e₁` using `hc₁ Φ fun x hx => ballM_mono hle₁ (hsupp x hx)`. Establish `e₂` using `hc₂ Φ fun x hx => ballM_mono hle₂ (hsupp x hx)`.

Establish `hI : (∫ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ∂volM ν (Fin n) (Fin r)) ≠ 0`. Express the relevant statement in the definitionally equal form `(∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r)) ≠ 0`. Rewrite using `[integral_ind]`. Conclude with `Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c x₀)`. Conclude with `smul_right_injective V hI (e₁.symm.trans e₂)`.
-/
theorem germ_unique (hb : BallSt) [MeasurableSpace k] [BorelSpace k] (ν : Measure k) (hν : IsUnitVol ν)
    (B : SB (Matrix (Fin n) (Fin r) k) →ₗ[ℂ] W →ₗ[ℂ] V) (x₀ : Matrix (Fin n) (Fin r) k) {w : W} {v₁ v₂ : V}
    (h₁ : IsGerm ν B x₀ w v₁) (h₂ : IsGerm ν B x₀ w v₂) : v₁ = v₂ := by
  obtain ⟨c₁, hc₁⟩ := h₁
  obtain ⟨c₂, hc₂⟩ := h₂
  obtain ⟨c, hle₁, hle₂⟩ := exists_le_both c₁ c₂
  let Φ : SB (Matrix (Fin n) (Fin r) k) :=
    ⟨(ballM c x₀).indicator fun _ => (1 : ℂ), ((hb k n r).1 c x₀).2.2.1⟩
  have hsupp : ∀ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ≠ 0 → x ∈ ballM c x₀ := by
    intro x hx
    by_contra h
    exact hx (by simp [Φ, Set.indicator, h])
  have e₁ := hc₁ Φ fun x hx => ballM_mono hle₁ (hsupp x hx)
  have e₂ := hc₂ Φ fun x hx => ballM_mono hle₂ (hsupp x hx)
  have hI : (∫ x, (Φ : Matrix (Fin n) (Fin r) k → ℂ) x ∂volM ν (Fin n) (Fin r)) ≠ 0 := by
    change (∫ x, (ballM c x₀).indicator (fun _ => (1 : ℂ)) x ∂volM ν (Fin n) (Fin r)) ≠ 0
    rw [integral_ind]
    exact Complex.ofReal_ne_zero.2 (volM_ballM_ne_zero ν hν c x₀)
  exact smul_right_injective V hI (e₁.symm.trans e₂)

end PositivityTheory.Rg.Ming.UniqX

namespace PositivityTheory.Rg.Ming

open PositivityTheory.Rg.Ming.UniqX in
/- English proof (translation)
Introduce `hb`. Unfold `UniqSt`. Introduce `k _ _ _ _ _ _ ν hν n r V _ _ W _ _ B x₀ hex`. Use `choose f hf using hex`. Establish `hadd : ∀ w₁ w₂ : W, f (w₁ + w₂) = f w₁ + f w₂`.

Introduce `w₁ w₂`. Establish `h` using `germ_comb ν B x₀ 1 (hf w₁) (hf w₂)`. Rewrite `h` using `[one_smul, one_smul]`. Conclude with `germ_unique hb ν hν B x₀ (hf (w₁ + w₂)) h`. Establish `hsmul : ∀ (a : ℂ) (w : W), f (a • w) = a • f w`.

Introduce `a w`. Establish `h` using `germ_comb ν B x₀ a (hf w) (germ_zero ν B x₀)`. Rewrite `h` using `[add_zero, add_zero]`. Conclude with `germ_unique hb ν hν B x₀ (hf (a • w)) h`. Use `⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun w v => ?_⟩` and prove the remaining obligations.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `germ_unique hb ν hν B x₀ h (hf w)`. Introduce and unpack `rfl`. Conclude with `hf w`.
-/
theorem uniq : BallSt → UniqSt := by
  intro hb
  unfold UniqSt
  intro k _ _ _ _ _ _ ν hν n r V _ _ W _ _ B x₀ hex
  choose f hf using hex
  have hadd : ∀ w₁ w₂ : W, f (w₁ + w₂) = f w₁ + f w₂ := by
    intro w₁ w₂
    have h := germ_comb ν B x₀ 1 (hf w₁) (hf w₂)
    rw [one_smul, one_smul] at h
    exact germ_unique hb ν hν B x₀ (hf (w₁ + w₂)) h
  have hsmul : ∀ (a : ℂ) (w : W), f (a • w) = a • f w := by
    intro a w
    have h := germ_comb ν B x₀ a (hf w) (germ_zero ν B x₀)
    rw [add_zero, add_zero] at h
    exact germ_unique hb ν hν B x₀ (hf (a • w)) h
  refine ⟨{ toFun := f, map_add' := hadd, map_smul' := hsmul }, fun w v => ?_⟩
  constructor
  · intro h
    exact germ_unique hb ν hν B x₀ h (hf w)
  · rintro rfl
    exact hf w

end PositivityTheory.Rg.Ming

end
