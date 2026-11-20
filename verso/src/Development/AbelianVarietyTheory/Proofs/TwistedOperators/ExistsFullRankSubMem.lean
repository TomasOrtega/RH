import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ShearGLTransposeMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartStackDecomposition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartBoundedCoefficients
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankChartShearInvariance
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsNonzeroMinorOfRank
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatPartitionOfUnity
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzBruhatReindexRows
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.PairwiseDisjointCell

open GlobalTheory.WeilM Matrix

noncomputable section

namespace GlobalTheory.SmallRankCoinv
open GlobalTheory.SplitFlip GlobalTheory.LocMod.Inhab ValuativeRel GlobalTheory.RankChart GlobalTheory.RankStrata

/- English proof (translation)
Establish `hb : 0 < valuation k ((ϖ⁻¹ * a : kˣ) : k)` using `zero_lt_iff.2 (by simp)`. Establish `hv0 : 0 < valuation k (ϖ : k)` using `zero_lt_iff.2 (by simp)`. Establish `ha0 : 0 < valuation k (a : k)` using `zero_lt_iff.2 (by simp)`. Establish `hint : ∀ (x : box T R (ϖ⁻¹ * a)) r q, x.1 r q / ((ϖ⁻¹ * a : kˣ) : k) ∈ 𝒪[k]` using `fun x r q => by`. Rewrite using `[Valuation.mem_integer_iff, map_div₀, div_le_one₀ hb]`.

Conclude with `x.2 r q`. Set `φ : box T R (ϖ⁻¹ * a) →+ (T → R → 𝓀[k])` to `{ toFun := fun x r q => IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩ map_zero' := by`. Use function extensionality and compare the values at `r q`. Rewrite using `[Pi.zero_apply, Pi.zero_apply, ← map_zero (IsLocalRing.residue 𝒪[k])]`. Use `congr 1`.

Conclude with `Subtype.ext (by simp)`. Use the proof step `map_add' := fun x y => by`. Use function extensionality and compare the values at `r q`. Rewrite using `[Pi.add_apply, Pi.add_apply, ← map_add]`. Use `congr 1`.

Conclude with `Subtype.ext (by simp [add_div]) }`. Establish `hker : φ.ker ≤ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a))`. Introduce `x hx`. Rewrite using `[AddSubgroup.mem_addSubgroupOf]`. Introduce `r q`.

Establish `h1 : IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩ = 0` using `congrFun (congrFun hx r) q`. Rewrite `h1` using `[IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Establish `h2 : valuation k (x.1 r q / ((ϖ⁻¹ * a : kˣ) : k)) ≤ valuation k (ϖ : k)`. Rewrite using `[hϖ, le_uniformizer_iff]`. Conclude with `h1`.

Rewrite `h2` using `[map_div₀, div_le_iff₀ hb, ← map_mul, ← Units.val_mul, mul_inv_cancel_left]`. Conclude with `h2`. Establish `h1 : Nat.card (box T R (ϖ⁻¹ * a) ⧸ φ.ker) ≤ Nat.card (T → R → 𝓀[k])` using `Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective φ)`. Use `haveI : Finite (box T R (ϖ⁻¹ * a) ⧸ φ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective φ)`. Establish `h2` using `Nat.le_of_dvd Nat.card_pos (AddSubgroup.index_dvd_of_le hker)`.

Use `h2.trans (h1.trans_eq ?_)` and prove the remaining obligations. Simplify using `only [Nat.card_fun, Nat.card_eq_fintype_card, GlobalTheory.SplitWeil.resCard, ← pow_mul, mul_comm]`.
-/
theorem card_box_quot_le {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    (T R : Type) [Fintype T] [DecidableEq T] [Fintype R] [DecidableEq R] {ϖ : kˣ} (hϖ : IsUnif ϖ) (a : kˣ) :
    Nat.card (box T R (ϖ⁻¹ * a) ⧸ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a))) ≤
      GlobalTheory.SplitWeil.resCard k ^ (Fintype.card T * Fintype.card R) := by
  have hb : 0 < valuation k ((ϖ⁻¹ * a : kˣ) : k) := zero_lt_iff.2 (by simp)
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have ha0 : 0 < valuation k (a : k) := zero_lt_iff.2 (by simp)
  have hint : ∀ (x : box T R (ϖ⁻¹ * a)) r q, x.1 r q / ((ϖ⁻¹ * a : kˣ) : k) ∈ 𝒪[k] := fun x r q => by
    rw [Valuation.mem_integer_iff, map_div₀, div_le_one₀ hb]
    exact x.2 r q
  let φ : box T R (ϖ⁻¹ * a) →+ (T → R → 𝓀[k]) :=
    { toFun := fun x r q => IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩
      map_zero' := by
        funext r q
        rw [Pi.zero_apply, Pi.zero_apply, ← map_zero (IsLocalRing.residue 𝒪[k])]
        congr 1
        exact Subtype.ext (by simp)
      map_add' := fun x y => by
        funext r q
        rw [Pi.add_apply, Pi.add_apply, ← map_add]
        congr 1
        exact Subtype.ext (by simp [add_div]) }
  have hker : φ.ker ≤ (box T R a).addSubgroupOf (box T R (ϖ⁻¹ * a)) := by
    intro x hx
    rw [AddSubgroup.mem_addSubgroupOf]
    intro r q
    have h1 : IsLocalRing.residue 𝒪[k] ⟨_, hint x r q⟩ = 0 := congrFun (congrFun hx r) q
    rw [IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one] at h1
    have h2 : valuation k (x.1 r q / ((ϖ⁻¹ * a : kˣ) : k)) ≤ valuation k (ϖ : k) := by
      rw [hϖ, le_uniformizer_iff]; exact h1
    rw [map_div₀, div_le_iff₀ hb, ← map_mul, ← Units.val_mul, mul_inv_cancel_left] at h2
    exact h2
  have h1 : Nat.card (box T R (ϖ⁻¹ * a) ⧸ φ.ker) ≤ Nat.card (T → R → 𝓀[k]) :=
    Nat.card_le_card_of_injective _ (QuotientAddGroup.kerLift_injective φ)
  haveI : Finite (box T R (ϖ⁻¹ * a) ⧸ φ.ker) := Finite.of_injective _ (QuotientAddGroup.kerLift_injective φ)
  have h2 := Nat.le_of_dvd Nat.card_pos (AddSubgroup.index_dvd_of_le hker)
  refine h2.trans (h1.trans_eq ?_)
  simp only [Nat.card_fun, Nat.card_eq_fintype_card, GlobalTheory.SplitWeil.resCard, ← pow_mul, mul_comm]

/- English proof (translation)
Establish `hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k` using `by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])`. Establish `hn : GlobalTheory.SplitWeil.nabs k (ϖ ^ t) = ((GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹) ^ t`. Rewrite using `[← GlobalTheory.GLDoubling.nabs_unif hϖ]`. Simplify using `[GlobalTheory.SplitWeil.nabs]`. Use `set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqd`.

Establish `hq0 : 0 < q` using `by linarith`. Establish `e : ‖apow (ϖ ^ t) ((d : ℂ) / 2)‖ = q ^ (-((t : ℝ) * (d / 2)))`. Rewrite using `[apow, Complex.norm_cpow_eq_rpow_re_of_pos (GlobalTheory.SplitWeil.Model.nabs_pos _), hn, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le]`. Simplify using the standard rewrite rules. Rewrite using `[norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, e, Complex.norm_natCast]`.

Establish `hc' : (c : ℝ) ≤ q ^ ((t : ℝ) * r)`. Rewrite using `[← Nat.cast_mul, Real.rpow_natCast, hqd]`. Conclude with `hc` after adjusting the coercions. Combine the equalities or inequalities in the displayed calculation. Apply `Real.rpow_lt_one_of_one_lt_of_neg hq` to reduce the goal to its premises.

Establish `h1 : (2 * r : ℝ) < d` using `by exact_mod_cast hrd`. Establish `h2 : (0 : ℝ) < t` using `by exact_mod_cast ht`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_scalar_lt_one {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {ϖ : kˣ} (hϖ : IsUnif ϖ) {z : ℂ} (hz : ‖z‖ = 1) {t r d c : ℕ} (ht : 0 < t) (hrd : 2 * r < d)
    (hc : c ≤ GlobalTheory.SplitWeil.resCard k ^ (t * r)) : ‖z ^ t * apow (ϖ ^ t) ((d : ℂ) / 2) * (c : ℂ)‖ < 1 := by
  have hq : (1 : ℝ) < GlobalTheory.SplitWeil.resCard k := by exact_mod_cast (Finite.one_lt_card : 1 < Nat.card 𝓀[k])
  have hn : GlobalTheory.SplitWeil.nabs k (ϖ ^ t) = ((GlobalTheory.SplitWeil.resCard k : ℝ)⁻¹) ^ t := by
    rw [← GlobalTheory.GLDoubling.nabs_unif hϖ]
    simp [GlobalTheory.SplitWeil.nabs]
  set q : ℝ := (GlobalTheory.SplitWeil.resCard k : ℝ) with hqd
  have hq0 : 0 < q := by linarith
  have e : ‖apow (ϖ ^ t) ((d : ℂ) / 2)‖ = q ^ (-((t : ℝ) * (d / 2))) := by
    rw [apow, Complex.norm_cpow_eq_rpow_re_of_pos (GlobalTheory.SplitWeil.Model.nabs_pos _), hn, ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity), Real.inv_rpow hq0.le, ← Real.rpow_neg hq0.le]
    simp
  rw [norm_mul, norm_mul, norm_pow, hz, one_pow, one_mul, e, Complex.norm_natCast]
  have hc' : (c : ℝ) ≤ q ^ ((t : ℝ) * r) := by
    rw [← Nat.cast_mul, Real.rpow_natCast, hqd]; exact_mod_cast hc
  calc _ ≤ q ^ (-((t : ℝ) * (d / 2))) * q ^ ((t : ℝ) * r) := by gcongr
    _ = q ^ (-((t : ℝ) * (d / 2)) + t * r) := (Real.rpow_add hq0 _ _).symm
    _ < 1 := by
      apply Real.rpow_lt_one_of_one_lt_of_neg hq
      have h1 : (2 * r : ℝ) < d := by exact_mod_cast hrd
      have h2 : (0 : ℝ) < t := by exact_mod_cast ht
      nlinarith

/- English proof (translation)
Introduce `k _ _ _ _ R T D _ _ _ _ _ _ _ ν ϖ hϖ hν hRD τ f hf hsupp`. Take `⟨a, ha⟩` from `GlobalTheory.RankChart.bounded_coeff_of_SB k R T D τ f hf hsupp`. Take `⟨b, hb⟩` from `GlobalTheory.RankChart.sb_shear_invariant k R T D f hf`. Establish `hv0 : 0 < valuation k (ϖ : k)` using `zero_lt_iff.2 (by simp)`. Establish `hv1 : valuation k (ϖ : k) ≤ 1` using `hϖ ▸ uniformizer_lt_one.le`.

Establish `hva : ∀ x : k, (valuation k (x : k) ≤ valuation k (((ϖ⁻¹ * a : kˣ)) : k) ↔ valuation k ((ϖ : k) * x) ≤ valuation k (a : k))`. Introduce `x`. Rewrite using `[Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, le_inv_mul_iff₀ hv0]`. Establish `hHH' : box T R a ≤ box T R (ϖ⁻¹ * a)`. Introduce `C hC r q`.

Rewrite using `[hva, map_mul]`. Conclude with `(mul_le_of_le_one_left' hv1).trans (hC r q)`. Establish `hdilmem : ∀ C : Matrix T R k, ((ϖ : k) • C ∈ box T R a ↔ C ∈ box T R (ϖ⁻¹ * a))` using `fun C => forall_congr' fun r => forall_congr' fun q => by rw [hva]; rfl`. Establish `hcard` using `card_box_quot_le T R hϖ a`. Generalize the expression as in `hH : box T R a = H at ha hHH' hdilmem hcard`.

Generalize the expression as in `hH' : box T R (ϖ⁻¹ * a) = H' at hHH' hdilmem hcard`. Generalize the expression as in `hL : box T R b = L at hb`. Use `haveI : Finite (H ⧸ L.addSubgroupOf H) := hH ▸ hL ▸ finite_box (Y := T) (Y' := R) (k := k) a b`. Use `haveI : Finite (H' ⧸ H.addSubgroupOf H') := hH ▸ hH' ▸ finite_box (Y := T) (Y' := R) (k := k) (ϖ⁻¹ * a) a`. Use `letI : Fintype (H ⧸ L.addSubgroupOf H) := Fintype.ofFinite _`.

Use `letI : Fintype (H' ⧸ H.addSubgroupOf H') := Fintype.ofFinite _`. Establish `hinvL : ∀ (Y₁ : Matrix R D k) (C C' : Matrix T R k), C' - C ∈ L → f (stack Y₁ C') = f (stack Y₁ C)`. Introduce `Y₁ C C' h`. Use `hb (stack Y₁ C) (C' - C) h` as an intermediate fact. Rewrite `this` using `[shear_stack, add_sub_cancel]`. Then use the resulting hypothesis.

Take `⟨Ψ₁, hΨ₁, hSB⟩ : ∃ Ψ₁ : Matrix (R ⊕ T) D k → ℂ, (∀ Y, Ψ₁ Y = ∑ q : H ⧸ L.addSubgroupOf H, f (shear ((q.out : H) : Matrix T R k) Y)) ∧ Ψ₁ ∈ SB (Matrix (R ⊕ T) D k)` from `⟨∑ q : H ⧸ L.addSubgroupOf H, omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f, fun Y => by simp [Finset.sum_apply, omB_shearGL], Submodule.sum_mem _ fun q _ => omB_mem_SB ν ν _ _ hf⟩`. Establish `hzero : ∀ Y : Matrix (R ⊕ T) D k, (Y.submatrix Sum.inl τ).det = 0 → Ψ₁ Y = 0`. Introduce `Y hY`. Rewrite using `[hΨ₁]`. Use `Finset.sum_eq_zero fun q _ => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h`. Conclude with `hsupp _ h (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])`. Establish `hA1 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), Ψ₁ (stack Y₁ C) = if C ∈ H then Ψ₁ (stack Y₁ 0) else 0`. Introduce `Y₁ C`. Establish `h` using `sum_shift_out (fun C => f (stack Y₁ C)) H L (fun x y h => hinvL Y₁ x y h) (ha Y₁) C`.

Simplify using `only [hΨ₁, shear_stack, zero_add]`. Conclude with `h`. Establish `hA2 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k), ∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (stack Y₁ (C + ((q'.out : H') : Matrix T R k))) = if C ∈ H' then Ψ₁ (stack Y₁ 0) else 0`. Introduce `Y₁ C`. Rewrite using `[Finset.sum_congr rfl fun q' _ => hA1 Y₁ _]`.

Conclude with `sum_ite_out H H' hHH' _ C`. Take `⟨lam, hlam⟩ : ∃ lam : ℂ, lam = (ν ϖ : ℂ) ^ Fintype.card T * apow (ϖ ^ Fintype.card T) ((Fintype.card D : ℂ) / 2)` from `⟨_, rfl⟩`. Choose the witnesses or unpack the hypotheses as in `⟨n₁, hn₁, hexp⟩ : ∃ n₁ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y, n₁ Y = Ψ₁ Y - lam * Ψ₁ (dil (ϖ : k) Y) + lam * (∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (shear ((q'.out : H') : Matrix T R k) Y) - (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) * Ψ₁ Y) := by`. Use `⟨(Ψ₁ - omB ν ν (dilGL ϖ : GL (R ⊕ T) k) 1 Ψ₁) + lam • ∑ q' : H' ⧸ H.addSubgroupOf H', (omB ν ν (shearGL ((q'.out : H') : Matrix T R k)) 1 Ψ₁ - Ψ₁), ?_, ?_⟩` and prove the remaining obligations. Use `add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q' _ => GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB))` and prove the remaining obligations.

Rewrite using `[← neg_sub]`. Conclude with `Submodule.neg_mem _ (GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB)`. Introduce `Y`. Simplify using `only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, omB_dilGL, omB_shearGL, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hlam, Pi.mul_apply, Pi.natCast_apply]`. Establish `hn₁val : ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → n₁ Y = (1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H')) * Ψ₁ Y`.

Introduce `Y hY`. Rewrite using `[hexp]`. Distinguish the cases in `hd : (Y.submatrix Sum.inl τ).det = 0`. Rewrite using `[hzero Y hd, hzero _ (by rwa [submatrix_inl_eq, toRows₁_dil, ← submatrix_inl_eq]), Finset.sum_eq_zero fun q' _ => hzero _ (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])]`. Expand and normalize the polynomial expressions, which then agree.

Take `⟨C, hC⟩` from `GlobalTheory.RankChart.exists_eq_stack k R T D τ Y hY hd`. Rewrite using `[hC, dil_stack]`. Simplify using `only [shear_stack]`. Rewrite using `[hA2, hA1 _ ((ϖ : k) • C), hdilmem]`. Expand and normalize the polynomial expressions, which then agree.

Choose the witnesses or unpack the hypotheses as in `⟨n₀, hn₀, hn₀val⟩ : ∃ n₀ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y, n₀ Y = Ψ₁ Y - (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) * f Y := by`. Use `⟨∑ q : H ⧸ L.addSubgroupOf H, (omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f - f), Submodule.sum_mem _ fun q _ => GlobalTheory.RankStrata.sub_mem_Nsp ν _ hf, fun Y => ?_⟩` and prove the remaining obligations. Simplify using `only [hΨ₁, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, omB_shearGL]`. Establish `hQ : (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Establish `hlamne : 1 - lam * (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) ≠ 0`.

Rewrite `hcard` using `[Nat.card_eq_fintype_card]`. Establish `hlt` using `norm_scalar_lt_one hϖ hν (Fintype.card_pos (α := T)) hRD hcard`. Rewrite `hlt` using `[← hlam]`. Introduce `h`. Rewrite `hlt` using `[← sub_eq_zero.1 h, norm_one]`.

Conclude with `lt_irrefl _ hlt`. Use `⟨(Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ)⁻¹ • ((1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ • n₁ - n₀), Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hn₁) hn₀), fun Y hY => ?_⟩` and prove the remaining obligations. Simplify using `only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hn₁val Y hY, hn₀val]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem chart_eq_of_rank_le : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (R T D : Type) [Fintype R] [DecidableEq R] [Fintype T] [DecidableEq T] [Fintype D] [DecidableEq D] [Nonempty T] (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * Fintype.card R < Fintype.card D → ∀ (τ : R → D), ∀ f ∈ SB (Matrix (R ⊕ T) D k), (∀ Y : Matrix (R ⊕ T) D k, f Y ≠ 0 → (Y.submatrix Sum.inl τ).det ≠ 0) → ∃ Φ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R → Φ Y = f Y := by
  intro k _ _ _ _ R T D _ _ _ _ _ _ _ ν ϖ hϖ hν hRD τ f hf hsupp
  classical
  obtain ⟨a, ha⟩ := GlobalTheory.RankChart.bounded_coeff_of_SB k R T D τ f hf hsupp
  obtain ⟨b, hb⟩ := GlobalTheory.RankChart.sb_shear_invariant k R T D f hf
  have hv0 : 0 < valuation k (ϖ : k) := zero_lt_iff.2 (by simp)
  have hv1 : valuation k (ϖ : k) ≤ 1 := hϖ ▸ uniformizer_lt_one.le
  have hva : ∀ x : k, (valuation k (x : k) ≤ valuation k (((ϖ⁻¹ * a : kˣ)) : k) ↔
      valuation k ((ϖ : k) * x) ≤ valuation k (a : k)) := by
    intro x
    rw [Units.val_mul, map_mul, map_mul, Units.val_inv_eq_inv_val, map_inv₀, le_inv_mul_iff₀ hv0]
  have hHH' : box T R a ≤ box T R (ϖ⁻¹ * a) := by
    intro C hC r q
    rw [hva, map_mul]
    exact (mul_le_of_le_one_left' hv1).trans (hC r q)
  have hdilmem : ∀ C : Matrix T R k, ((ϖ : k) • C ∈ box T R a ↔ C ∈ box T R (ϖ⁻¹ * a)) := fun C =>
    forall_congr' fun r => forall_congr' fun q => by rw [hva]; rfl
  have hcard := card_box_quot_le T R hϖ a
  generalize hH : box T R a = H at ha hHH' hdilmem hcard
  generalize hH' : box T R (ϖ⁻¹ * a) = H' at hHH' hdilmem hcard
  generalize hL : box T R b = L at hb
  haveI : Finite (H ⧸ L.addSubgroupOf H) := hH ▸ hL ▸ finite_box (Y := T) (Y' := R) (k := k) a b
  haveI : Finite (H' ⧸ H.addSubgroupOf H') := hH ▸ hH' ▸ finite_box (Y := T) (Y' := R) (k := k) (ϖ⁻¹ * a) a
  letI : Fintype (H ⧸ L.addSubgroupOf H) := Fintype.ofFinite _
  letI : Fintype (H' ⧸ H.addSubgroupOf H') := Fintype.ofFinite _

  have hinvL : ∀ (Y₁ : Matrix R D k) (C C' : Matrix T R k), C' - C ∈ L →
      f (stack Y₁ C') = f (stack Y₁ C) := by
    intro Y₁ C C' h
    have := hb (stack Y₁ C) (C' - C) h
    rwa [shear_stack, add_sub_cancel] at this
  obtain ⟨Ψ₁, hΨ₁, hSB⟩ : ∃ Ψ₁ : Matrix (R ⊕ T) D k → ℂ,
      (∀ Y, Ψ₁ Y = ∑ q : H ⧸ L.addSubgroupOf H, f (shear ((q.out : H) : Matrix T R k) Y)) ∧
      Ψ₁ ∈ SB (Matrix (R ⊕ T) D k) :=
    ⟨∑ q : H ⧸ L.addSubgroupOf H, omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f,
      fun Y => by simp [Finset.sum_apply, omB_shearGL],
      Submodule.sum_mem _ fun q _ => omB_mem_SB ν ν _ _ hf⟩
  have hzero : ∀ Y : Matrix (R ⊕ T) D k, (Y.submatrix Sum.inl τ).det = 0 → Ψ₁ Y = 0 := by
    intro Y hY
    rw [hΨ₁]
    refine Finset.sum_eq_zero fun q _ => ?_
    by_contra h
    exact hsupp _ h (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])
  have hA1 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      Ψ₁ (stack Y₁ C) = if C ∈ H then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    have h := sum_shift_out (fun C => f (stack Y₁ C)) H L (fun x y h => hinvL Y₁ x y h) (ha Y₁) C
    simp only [hΨ₁, shear_stack, zero_add]
    exact h
  have hA2 : ∀ (Y₁ : Matrix R D k) (C : Matrix T R k),
      ∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (stack Y₁ (C + ((q'.out : H') : Matrix T R k))) =
        if C ∈ H' then Ψ₁ (stack Y₁ 0) else 0 := by
    intro Y₁ C
    rw [Finset.sum_congr rfl fun q' _ => hA1 Y₁ _]
    exact sum_ite_out H H' hHH' _ C

  obtain ⟨lam, hlam⟩ : ∃ lam : ℂ, lam = (ν ϖ : ℂ) ^ Fintype.card T * apow (ϖ ^ Fintype.card T) ((Fintype.card D : ℂ) / 2) :=
    ⟨_, rfl⟩
  obtain ⟨n₁, hn₁, hexp⟩ : ∃ n₁ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν, ∀ Y, n₁ Y = Ψ₁ Y - lam * Ψ₁ (dil (ϖ : k) Y) +
      lam * (∑ q' : H' ⧸ H.addSubgroupOf H', Ψ₁ (shear ((q'.out : H') : Matrix T R k) Y) -
        (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) * Ψ₁ Y) := by
    refine ⟨(Ψ₁ - omB ν ν (dilGL ϖ : GL (R ⊕ T) k) 1 Ψ₁) +
      lam • ∑ q' : H' ⧸ H.addSubgroupOf H', (omB ν ν (shearGL ((q'.out : H') : Matrix T R k)) 1 Ψ₁ - Ψ₁), ?_, ?_⟩
    · refine add_mem ?_ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q' _ =>
        GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB))
      rw [← neg_sub]
      exact Submodule.neg_mem _ (GlobalTheory.RankStrata.sub_mem_Nsp ν _ hSB)
    · intro Y
      simp only [Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul, Finset.sum_apply, omB_dilGL,
        omB_shearGL, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, hlam,
        Pi.mul_apply, Pi.natCast_apply]
  have hn₁val : ∀ Y : Matrix (R ⊕ T) D k, Y.rank ≤ Fintype.card R →
      n₁ Y = (1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H')) * Ψ₁ Y := by
    intro Y hY
    rw [hexp]
    by_cases hd : (Y.submatrix Sum.inl τ).det = 0
    · rw [hzero Y hd, hzero _ (by rwa [submatrix_inl_eq, toRows₁_dil, ← submatrix_inl_eq]),
        Finset.sum_eq_zero fun q' _ => hzero _ (by rwa [submatrix_inl_eq, toRows₁_shear, ← submatrix_inl_eq])]
      ring
    · obtain ⟨C, hC⟩ := GlobalTheory.RankChart.exists_eq_stack k R T D τ Y hY hd
      rw [hC, dil_stack]
      simp only [shear_stack]
      rw [hA2, hA1 _ ((ϖ : k) • C), hdilmem]
      ring

  obtain ⟨n₀, hn₀, hn₀val⟩ : ∃ n₀ ∈ GlobalTheory.RankStrata.Nsp k (R ⊕ T) D ν,
      ∀ Y, n₀ Y = Ψ₁ Y - (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) * f Y := by
    refine ⟨∑ q : H ⧸ L.addSubgroupOf H, (omB ν ν (shearGL ((q.out : H) : Matrix T R k)) 1 f - f),
      Submodule.sum_mem _ fun q _ => GlobalTheory.RankStrata.sub_mem_Nsp ν _ hf, fun Y => ?_⟩
    simp only [hΨ₁, Finset.sum_apply, Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const,
      Finset.card_univ, nsmul_eq_mul, omB_shearGL]

  have hQ : (Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ) ≠ 0 :=
    Nat.cast_ne_zero.2 Fintype.card_ne_zero
  have hlamne : 1 - lam * (Fintype.card (H' ⧸ H.addSubgroupOf H') : ℂ) ≠ 0 := by
    rw [Nat.card_eq_fintype_card] at hcard
    have hlt := norm_scalar_lt_one hϖ hν (Fintype.card_pos (α := T)) hRD hcard
    rw [← hlam] at hlt
    intro h
    rw [← sub_eq_zero.1 h, norm_one] at hlt
    exact lt_irrefl _ hlt
  refine ⟨(Fintype.card (H ⧸ L.addSubgroupOf H) : ℂ)⁻¹ •
      ((1 - lam * Fintype.card (H' ⧸ H.addSubgroupOf H'))⁻¹ • n₁ - n₀),
    Submodule.smul_mem _ _ (Submodule.sub_mem _ (Submodule.smul_mem _ _ hn₁) hn₀), fun Y hY => ?_⟩
  simp only [Pi.smul_apply, Pi.sub_apply, smul_eq_mul, hn₁val Y hY, hn₀val]
  field_simp
  ring

/- English proof (translation)
Introduce `k _ _ _ _ n d ν ϖ hϖ hν hnd Ψ hΨ`. Establish `piece : ∀ ρ < n, ∀ f : Matrix (Fin n) (Fin d) k → ℂ, f ∈ SB (Matrix (Fin n) (Fin d) k) → ∀ (S : Fin ρ → Fin n) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) → ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = f Y`. Introduce `ρ hρ f hf S τ hS`. Distinguish the cases in `h0 : ∀ Y, f Y = 0`. Conclude with `⟨0, Submodule.zero_mem _, fun Y _ => by simp [h0 Y]⟩`.

Use `push_neg at h0`. Take `⟨Y0, hY0⟩` from `h0`. Establish `hinj : Function.Injective S`. Introduce `i j hij`. Assume the negation of the conclusion as `hne`.

Conclude with `hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))`. Set `e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin n` to `(Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)`. Establish `he' : ∀ i, e'.symm (S i) = Sum.inl i` using `fun i => by`. Rewrite using `[Equiv.symm_apply_eq]`. Simplify using `[e']`.

Use `haveI : Nonempty ↥(Set.range S)ᶜ := by`. Assume the negation of the conclusion as `hne`. Rewrite `hne` using `[not_nonempty_iff]`. Use `Fintype.card_congr e'` as an intermediate fact. Simplify using `at this`.

Use linear arithmetic over natural numbers and integers. Establish `hT` using `GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'`. Take `⟨Φ', hΦ', hΦ'f⟩` from `chart_eq_of_rank_le k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν (by simp only [Fintype.card_fin]; omega) τ (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by`. Use `hS _ hZ` as an intermediate fact. Rewrite using `[Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)` and apply the resulting hypothesis.

Establish `hT2` using `GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm`. Use `⟨_, hT2.2 Φ' hΦ', fun Y hY => ?_⟩` and prove the remaining obligations. Simplify using `only [Equiv.symm_symm]`. Rewrite using `[hΦ'f _ (by rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]; simpa using hY)]`. Simplify using `[Matrix.submatrix_submatrix]`.

Establish `step : ∀ ρ < n, ∀ g ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → g Y = 0) → ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y`. Introduce `ρ hρ g hg hg0`. Use `haveI : T2Space k := by`. Use `letI := IsTopologicalAddGroup.rightUniformSpace k`. Use `haveI := isUniformAddGroup_of_addCommGroup (G := k)`.

Use `infer_instance`. Establish `hsp` using `GlobalTheory.CoverSB.mem_span_of_cover k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d)) (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0}) (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg (fun Y hY => …`. Establish `: ρ ≤ Y.rank`. Assume the negation of the conclusion as `h`. Conclude with `hY (hg0 Y (by omega))`.

Take `⟨S, τ, h⟩` from `GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank k _ _ ρ Y this`. Conclude with `⟨(S, τ), h⟩)`. Use `Submodule.span_induction (p := fun g _ => ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y) ?_ ?_ ?_ ?_ hsp` and prove the remaining obligations. Introduce and unpack `f ⟨hf, i, hi⟩`. Conclude with `piece ρ hρ f hf i.1 i.2 hi`.

Conclude with `⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩`. Introduce and unpack `x y _ _ ⟨Φ, hΦ, h⟩ ⟨Φ', hΦ', h'⟩`. Conclude with `⟨Φ + Φ', Submodule.add_mem _ hΦ hΦ', fun Y hY => by simp [h Y hY, h' Y hY]⟩`. Introduce and unpack `c x _ ⟨Φ, hΦ, h⟩`. Conclude with `⟨c • Φ, Submodule.smul_mem _ c hΦ, fun Y hY => by simp [h Y hY]⟩`.

Establish `ind : ∀ ρ ≤ n, ∃ Ψρ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → Ψρ Y = 0) ∧ Ψ - Ψρ ∈ Nsp k (Fin n) (Fin d) ν`. Introduce `ρ`. Proceed by induction on `ρ with`. Consider the case `zero => intro _; exact ⟨Ψ, hΨ, fun Y h => absurd h (Nat.not_lt_zero _), by simp⟩`. Consider the case `succ ρ ih`.

Introduce `hρ`. Take `⟨Ψρ, hSB, h0, hN⟩` from `ih (by omega)`. Take `⟨Φ, hΦ, hΦe⟩` from `step ρ (by omega) Ψρ hSB h0`. Use `⟨Ψρ - Φ, Submodule.sub_mem _ hSB (Nsp_le_SB _ _ ν hΦ), fun Y hY => ?_, ?_⟩` and prove the remaining obligations. Simplify using `[hΦe Y (by omega)]`.

Establish `: Ψ - (Ψρ - Φ) = (Ψ - Ψρ) + Φ` using `by abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ hN hΦ`. Take `⟨Ψ₀, h1, h2, h3⟩` from `ind n le_rfl`. Use `⟨Ψ₀, h1, fun Y hY => h2 Y (lt_of_le_of_ne ?_ hY), h3⟩` and prove the remaining obligations.

Simplify using `using Matrix.rank_le_card_height Y`.
-/
theorem exists_fullRank_sub_mem : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ)
    (ν : kˣ →* ℂˣ) (ϖ : kˣ), GlobalTheory.SplitFlip.IsUnif ϖ → ‖(ν ϖ : ℂ)‖ = 1 → 2 * n ≤ d + 1 →
    ∀ Ψ ∈ SB (Matrix (Fin n) (Fin d) k), ∃ Ψ₀ ∈ SB (Matrix (Fin n) (Fin d) k), (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≠ n → Ψ₀ Y = 0) ∧
      Ψ - Ψ₀ ∈ Submodule.span ℂ {Z | ∃ g : GL (Fin n) k, ∃ Ψ' ∈ SB (Matrix (Fin n) (Fin d) k), Z = GlobalTheory.SplitFlip.omB ν ν g 1 Ψ' - Ψ'} := by
  intro k _ _ _ _ n d ν ϖ hϖ hν hnd Ψ hΨ
  classical
  have piece : ∀ ρ < n, ∀ f : Matrix (Fin n) (Fin d) k → ℂ, f ∈ SB (Matrix (Fin n) (Fin d) k) →
      ∀ (S : Fin ρ → Fin n) (τ : Fin ρ → Fin d), (∀ Y, f Y ≠ 0 → (Y.submatrix S τ).det ≠ 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = f Y := by
    intro ρ hρ f hf S τ hS
    by_cases h0 : ∀ Y, f Y = 0
    · exact ⟨0, Submodule.zero_mem _, fun Y _ => by simp [h0 Y]⟩
    push_neg at h0
    obtain ⟨Y0, hY0⟩ := h0
    have hinj : Function.Injective S := by
      intro i j hij
      by_contra hne
      exact hS Y0 hY0 (Matrix.det_zero_of_row_eq hne (by ext l; simp [hij]))
    let e' : Fin ρ ⊕ ↥(Set.range S)ᶜ ≃ Fin n :=
      (Equiv.sumCongr (Equiv.ofInjective S hinj) (Equiv.refl _)).trans (Equiv.Set.sumCompl _)
    have he' : ∀ i, e'.symm (S i) = Sum.inl i := fun i => by
      rw [Equiv.symm_apply_eq]; simp [e']
    haveI : Nonempty ↥(Set.range S)ᶜ := by
      by_contra hne
      rw [not_nonempty_iff] at hne
      have := Fintype.card_congr e'
      simp at this
      omega
    have hT := GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin n) (Fin d) ν e'
    obtain ⟨Φ', hΦ', hΦ'f⟩ := chart_eq_of_rank_le k (Fin ρ) (↥(Set.range S)ᶜ) (Fin d) ν ϖ hϖ hν (by simp only [Fintype.card_fin]; omega) τ
      (fun Z => f (Z.submatrix e'.symm id)) (hT.1 f hf) (fun Z hZ => by
        have := hS _ hZ
        rwa [Matrix.submatrix_submatrix, show (e'.symm ∘ S) = Sum.inl from funext he'] at this)
    have hT2 := GlobalTheory.RankStrata.rowRenum_SB_Nsp k (Fin n) (Fin ρ ⊕ ↥(Set.range S)ᶜ) (Fin d) ν e'.symm
    refine ⟨_, hT2.2 Φ' hΦ', fun Y hY => ?_⟩
    simp only [Equiv.symm_symm]
    rw [hΦ'f _ (by rw [show (id : Fin d → Fin d) = ⇑(Equiv.refl (Fin d)) from rfl, Matrix.rank_submatrix]; simpa using hY)]
    simp [Matrix.submatrix_submatrix]
  have step : ∀ ρ < n, ∀ g ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → g Y = 0) →
      ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y := by
    intro ρ hρ g hg hg0
    haveI : T2Space k := by
      letI := IsTopologicalAddGroup.rightUniformSpace k
      haveI := isUniformAddGroup_of_addCommGroup (G := k)
      infer_instance
    have hsp := GlobalTheory.CoverSB.mem_span_of_cover k (Fin n) (Fin d) ((Fin ρ → Fin n) × (Fin ρ → Fin d))
      (fun i => {Y : Matrix (Fin n) (Fin d) k | (Y.submatrix i.1 i.2).det ≠ 0})
      (fun i => isOpen_ne_fun ((continuous_id.matrix_submatrix i.1 i.2).matrix_det) continuous_const) g hg
      (fun Y hY => by
        have : ρ ≤ Y.rank := by
          by_contra h
          exact hY (hg0 Y (by omega))
        obtain ⟨S, τ, h⟩ := GlobalTheory.exists_submatrix_det_ne_zero_of_le_rank k _ _ ρ Y this
        exact ⟨(S, τ), h⟩)
    refine Submodule.span_induction
      (p := fun g _ => ∃ Φ ∈ Nsp k (Fin n) (Fin d) ν, ∀ Y : Matrix (Fin n) (Fin d) k, Y.rank ≤ ρ → Φ Y = g Y)
      ?_ ?_ ?_ ?_ hsp
    · rintro f ⟨hf, i, hi⟩
      exact piece ρ hρ f hf i.1 i.2 hi
    · exact ⟨0, Submodule.zero_mem _, fun _ _ => rfl⟩
    · rintro x y _ _ ⟨Φ, hΦ, h⟩ ⟨Φ', hΦ', h'⟩
      exact ⟨Φ + Φ', Submodule.add_mem _ hΦ hΦ', fun Y hY => by simp [h Y hY, h' Y hY]⟩
    · rintro c x _ ⟨Φ, hΦ, h⟩
      exact ⟨c • Φ, Submodule.smul_mem _ c hΦ, fun Y hY => by simp [h Y hY]⟩
  have ind : ∀ ρ ≤ n, ∃ Ψρ ∈ SB (Matrix (Fin n) (Fin d) k),
      (∀ Y : Matrix (Fin n) (Fin d) k, Y.rank < ρ → Ψρ Y = 0) ∧ Ψ - Ψρ ∈ Nsp k (Fin n) (Fin d) ν := by
    intro ρ
    induction ρ with
    | zero => intro _; exact ⟨Ψ, hΨ, fun Y h => absurd h (Nat.not_lt_zero _), by simp⟩
    | succ ρ ih =>
      intro hρ
      obtain ⟨Ψρ, hSB, h0, hN⟩ := ih (by omega)
      obtain ⟨Φ, hΦ, hΦe⟩ := step ρ (by omega) Ψρ hSB h0
      refine ⟨Ψρ - Φ, Submodule.sub_mem _ hSB (Nsp_le_SB _ _ ν hΦ), fun Y hY => ?_, ?_⟩
      · simp [hΦe Y (by omega)]
      · have : Ψ - (Ψρ - Φ) = (Ψ - Ψρ) + Φ := by abel
        rw [this]; exact Submodule.add_mem _ hN hΦ
  obtain ⟨Ψ₀, h1, h2, h3⟩ := ind n le_rfl
  refine ⟨Ψ₀, h1, fun Y hY => h2 Y (lt_of_le_of_ne ?_ hY), h3⟩
  simpa using Matrix.rank_le_card_height Y

end GlobalTheory.SmallRankCoinv

end
