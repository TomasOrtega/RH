import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsSubringEqOK
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EtaleHermitianPairStructureFactsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIntegralOrInvIsIntegralFiniteExtUltrametricStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentDecompositionOfIntegralityStatement
open GlobalTheory.JR Matrix MeasureTheory Filter Topology
open scoped Pointwise ENNReal NNReal

noncomputable section

namespace GlobalTheory.JR.HeightSquareIntegrable

/- English proof (translation)
Rewrite using `[ENNReal.tsum_eq_iSup_sum]`. Use `iSup_le fun s => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Use `Finset.sum_le_sum_of_subset fun t ht => ?_` and prove the remaining obligations. Conclude with `Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht`.

Use `_ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm`. Use `_ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _`.
-/
theorem tsum_pi_prod_le' {ι : Type} [Fintype ι] {α : ι → Type} (f : ∀ i, α i → ℝ≥0∞) :
    ∑' t : ∀ i, α i, ∏ i, f i (t i) ≤ ∏ i, ∑' x, f i x := by
  classical
  rw [ENNReal.tsum_eq_iSup_sum]
  refine iSup_le fun s => ?_
  calc ∑ t ∈ s, ∏ i, f i (t i)
      ≤ ∑ t ∈ Fintype.piFinset (fun i => s.image (fun t => t i)), ∏ i, f i (t i) := by
        refine Finset.sum_le_sum_of_subset fun t ht => ?_
        exact Fintype.mem_piFinset.2 fun i => Finset.mem_image_of_mem _ ht
    _ = ∏ i, ∑ x ∈ s.image (fun t => t i), f i x := (Finset.prod_univ_sum _ _).symm
    _ ≤ _ := Finset.prod_le_prod' fun i _ => ENNReal.sum_le_tsum _

section Idem
variable {K : Type} [CommRing K] {m : ℕ} {f : Fin m → K}

/- English proof (translation)
Establish `hx : x = ∑ j, f j * x` using `by rw [← Finset.sum_mul, hsum, one_mul]`. Establish `hy : y = ∑ j, f j * y` using `by rw [← Finset.sum_mul, hsum, one_mul]`. Rewrite using `[hx, hy]`. Conclude with `Finset.sum_congr rfl fun j _ => h j`.
-/
theorem eq_of_mul_eq (hsum : ∑ i, f i = 1) {x y : K} (h : ∀ j, f j * x = f j * y) : x = y := by
  have hx : x = ∑ j, f j * x := by rw [← Finset.sum_mul, hsum, one_mul]
  have hy : y = ∑ j, f j * y := by rw [← Finset.sum_mul, hsum, one_mul]
  rw [hx, hy]; exact Finset.sum_congr rfl fun j _ => h j

/- English proof (translation)
Rewrite using `[Finset.mul_sum, Finset.sum_eq_single j]`. Rewrite using `[← mul_assoc, hid]`. Introduce `i _ hij`. Rewrite using `[← mul_assoc, hor j i (Ne.symm hij), zero_mul]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem mul_sum_eq (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (a : Fin m → K) (j : Fin m) : f j * ∑ i, f i * a i = f j * a j := by
  rw [Finset.mul_sum, Finset.sum_eq_single j]
  · rw [← mul_assoc, hid]
  · intro i _ hij; rw [← mul_assoc, hor j i (Ne.symm hij), zero_mul]
  · intro h; exact absurd (Finset.mem_univ j) h

/- English proof (translation)
Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Prove the components needed by the constructor for the conclusion. Introduce `h; exact ⟨x - y, by linear_combination (-1 : K) * h⟩`. Introduce and unpack `⟨a, ha⟩`. Take the linear combination `(-f j) * ha - a * hid j`.
-/
theorem mul_eq_iff_mk (hid : ∀ i, f i * f i = f i) (j : Fin m) (x y : K) :
    f j * x = f j * y ↔
      Ideal.Quotient.mk (Ideal.span {1 - f j}) x = Ideal.Quotient.mk (Ideal.span {1 - f j}) y := by
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
  constructor
  · intro h; exact ⟨x - y, by linear_combination (-1 : K) * h⟩
  · rintro ⟨a, ha⟩; linear_combination (-f j) * ha - a * hid j

/- English proof (translation)
Rewrite using `[mul_eq_iff_mk hid]`. Simplify using `only [map_prod, map_pow]`. Rewrite using `[Finset.prod_eq_single j]`. Use `congr 1`. Rewrite using `[← mul_eq_iff_mk hid]`.

Take the linear combination `(g j - 1) * hid j`. Introduce `i _ hij`. Establish `h1 : Ideal.Quotient.mk (Ideal.span {1 - f j}) (f i * g i + (1 - f i)) = 1`. Rewrite using `[← map_one (Ideal.Quotient.mk (Ideal.span {1 - f j})), ← mul_eq_iff_mk hid]`. Take the linear combination `(g i - 1) * hor j i (Ne.symm hij)`.

Rewrite using `[h1, one_pow]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`.
-/
theorem mul_prod_eq (hid : ∀ i, f i * f i = f i) (hor : ∀ i j, i ≠ j → f i * f j = 0)
    (g : Fin m → K) (k : Fin m → ℕ) (j : Fin m) :
    f j * ∏ i, (f i * g i + (1 - f i)) ^ k i = f j * g j ^ k j := by
  rw [mul_eq_iff_mk hid]; simp only [map_prod, map_pow]
  rw [Finset.prod_eq_single j]
  · congr 1
    rw [← mul_eq_iff_mk hid]; linear_combination (g j - 1) * hid j
  · intro i _ hij
    have h1 : Ideal.Quotient.mk (Ideal.span {1 - f j}) (f i * g i + (1 - f i)) = 1 := by
      rw [← map_one (Ideal.Quotient.mk (Ideal.span {1 - f j})), ← mul_eq_iff_mk hid]
      linear_combination (g i - 1) * hor j i (Ne.symm hij)
    rw [h1, one_pow]
  · intro h; exact absurd (Finset.mem_univ j) h

end Idem

/- English proof (translation)
Introduce `F E _ _ _ _ hU A μ hμ`. Use `haveI := hU.ultraF`. Use `haveI := hU.lcF`. Use `haveI := hU.charZero`. Use `haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F`.

Use `haveI : IsTopologicalAddGroup A.K := IsModuleTopology.topologicalAddGroup F A.K`. Use `haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K`. Set `b` to `Module.finBasis F A.K`. Use `haveI : T2Space A.K := .of_injective_continuous b.equivFun.injective (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)`. Use `haveI : SecondCountableTopology A.K := b.equivFunL.toHomeomorph.secondCountableTopology`.

Take `⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩` from `GlobalTheory.T.etaleHermitianPair_structure_facts F E A`. Take `⟨m, f, hid, hor, hsum, hsc, hvp⟩` from `GlobalTheory.T.idempotent_decomposition_of_integrality F E A (fun k _ _ _ y hy => GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric F k y hy)`. Establish `hOR : ∀ x, x ∈ A.OK ↔ x ∈ R` using `fun x => by rw [← hR, SetLike.mem_coe]`. Establish `hfR : ∀ i, f i ∈ R` using `fun i => by`. Rewrite using `[← hOR, Et.mem_OK_iff_isIntegral]`.

Use `⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩` and prove the remaining obligations. Simplify using `[sq, hid i]`. Take `⟨π, hπ0, hπ1⟩` from `NormedField.exists_norm_lt_one F`. Establish `hπ : π ≠ 0` using `norm_pos_iff.1 hπ0`. Establish `hpp : algebraMap F A.K π * algebraMap F A.K π⁻¹ = 1`.

Rewrite using `[← map_mul, mul_inv_cancel₀ hπ, map_one]`. Establish `hpR : algebraMap F A.K π ∈ R`. Rewrite using `[← hOR, Et.mem_OK_iff_isIntegral]`. Establish `hmem : π ∈ (NormedField.valuation (K` using `F)).integer := by`. Rewrite using `[Valuation.mem_integer_iff, NormedField.valuation_apply]`.

Conclude with `hπ1.le` after adjusting the coercions. Conclude with `(isIntegral_algebraMap (R := (NormedField.valuation (K := F)).integer) (A := A.K) (x := ⟨π, hmem⟩) : _)`. Use `set p := algebraMap F A.K π with hp`. Use `set p' := algebraMap F A.K π⁻¹ with hp'`. Set `u : Fin m → A.Kˣ` to `fun i => ⟨f i * p + (1 - f i), f i * p' + (1 - f i), by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i, by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i⟩`.

Establish `hu : ∀ i, ((u i : A.Kˣ) : A.K) = f i * p + (1 - f i)` using `fun i => rfl`. Establish `huR : ∀ i, ((u i : A.Kˣ) : A.K) ∈ R` using `fun i => by`. Rewrite using `[hu]`. Conclude with `R.add_mem (R.mul_mem (hfR i) hpR) (R.sub_mem R.one_mem (hfR i))`. Use `haveI : μ.IsAddHaarMeasure := hμ`.

Establish `hμO0 : μ A.OK ≠ 0` using `hOo.measure_ne_zero μ ⟨0, (hOR 0).2 R.zero_mem⟩`. Establish `hμOt : μ A.OK ≠ ⊤` using `hOc.measure_lt_top.ne`. Establish `hsmulO : ∀ v : A.Kˣ, (v : A.K) ∈ R → v • A.OK ⊆ A.OK`. Introduce and unpack `v hv _ ⟨y, hy, rfl⟩`. Rewrite `hy`, the goal using `[hOR]`.

Conclude with `R.mul_mem hv hy`. Establish `hle1 : ∀ v : A.Kˣ, (v : A.K) ∈ R → distribHaarChar A.K v ≤ 1`. Introduce `v hv`. Establish `h2 : μ (v • A.OK) ≤ μ A.OK` using `measure_mono (hsmulO v hv)`. Rewrite `h2` using `[← distribHaarChar_mul μ]`.

Establish `h3 : (distribHaarChar A.K v : ℝ≥0∞) ≤ 1`. Rewrite using `[← ENNReal.mul_le_mul_iff_left hμO0 hμOt, one_mul]` and apply the resulting hypothesis. Conclude with `h3` after adjusting the coercions. Establish `hlt1 : ∀ i, distribHaarChar A.K (u i) < 1`. Introduce `i`.

Establish `hsub` using `hsmulO (u i) (huR i)`. Establish `hcl : IsClosed ((u i) • A.OK)` using `(hOc.smul (u i)).isClosed`. Establish `hfi : f i ∉ (u i) • A.OK`. Introduce and unpack `⟨y, hy, hyf⟩`. Establish `hyf' : ((u i : A.Kˣ) : A.K) * y = f i` using `hyf`.

Establish `hy' : y = p' * f i`. Establish `h1 : y = (((u i)⁻¹ : A.Kˣ) : A.K) * f i` using `by rw [← hyf', Units.inv_mul_cancel_left]`. Rewrite using `[h1]`. Use `show (f i * p' + (1 - f i)) * f i = p' * f i`. Take the linear combination `(p' - 1) * hid i`.

Establish `hn : 1 < ‖π⁻¹‖` using `by rw [norm_inv]; exact (one_lt_inv₀ hπ0).2 hπ1`. Conclude with `hsc i π⁻¹ hn (hy' ▸ hy)`. Establish `hopen : IsOpen (A.OK \ (u i) • A.OK)` using `hOo.sdiff hcl`. Establish `hpos : μ (A.OK \ (u i) • A.OK) ≠ 0` using `hopen.measure_ne_zero μ ⟨f i, (hOR _).2 (hfR i), hfi⟩`. Establish `hadd : μ ((u i) • A.OK) + μ (A.OK \ (u i) • A.OK) = μ A.OK`.

Rewrite using `[measure_add_sdiff hcl.measurableSet.nullMeasurableSet, Set.union_eq_right.2 hsub]`. Establish `hlt : μ ((u i) • A.OK) < μ A.OK`. Rewrite using `[← hadd]`. Conclude with `ENNReal.lt_add_right (ne_top_of_le_ne_top hμOt (measure_mono hsub)) hpos`. Rewrite `hlt` using `[← distribHaarChar_mul μ]`.

Establish `h4 : (distribHaarChar A.K (u i) : ℝ≥0∞) < 1`. Assume the negation of the conclusion as `hc`. Establish `hc' : 1 ≤ (distribHaarChar A.K (u i) : ℝ≥0∞)` using `not_lt.1 hc`. Establish `h5 : 1 * μ A.OK ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) * μ A.OK` using `by gcongr`. Rewrite `h5` using `[one_mul]`.

Conclude with `absurd hlt (not_lt.2 h5)`. Conclude with `h4` after adjusting the coercions. Establish `hex : ∀ z : A.K, ∀ i, ∃ n : ℕ, π ^ n • (f i * z) ∈ A.OK`. Introduce `z i`. Establish `ht : Tendsto (fun n : ℕ => π ^ n • (f i * z)) atTop (𝓝 0)`.

Use `(tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).smul_const (f i * z)` as an intermediate fact. Simplify using `using this`. Conclude with `(ht.eventually (hOo.mem_nhds ((hOR 0).2 R.zero_mem))).exists`. Set `N : A.K → Fin m → ℕ` to `fun z i => Nat.find (hex z i)`. Establish `hNspec : ∀ z i, π ^ N z i • (f i * z) ∈ A.OK` using `fun z i => Nat.find_spec (hex z i)`.

Establish `hNmin : ∀ z i, N z i ≠ 0 → π ^ (N z i - 1) • (f i * z) ∉ A.OK` using `fun z i hi => Nat.find_min (hex z i) (Nat.sub_lt (Nat.pos_of_ne_zero hi) one_pos)`. Establish `hsmul : ∀ (k : ℕ) (x : A.K), π ^ k • x = p ^ k * x` using `fun k x => by`. Rewrite using `[Algebra.smul_def, map_pow]`. Establish `hrep : ∀ x : A.K, x = ∑ j, f j * x` using `fun x => by rw [← Finset.sum_mul, hsum, one_mul]`. Establish `hkey : ∀ z : A.K, ∃ s : A.Kˣ, ((s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1) ∧ distribHaarChar A.K s ≤ ∏ i, distribHaarChar A.K (u i) ^ (N z i - 1)`.

Introduce `z`. Use `set n := N z with hn`. Establish `hn0 : ∀ i, π ^ n i • (f i * z) ∈ A.OK` using `fun i => hNspec z i`. Establish `hnmin : ∀ i, n i ≠ 0 → f i * (π ^ (n i - 1) • z) ∉ A.OK` using `fun i hi => by`. Rewrite using `[mul_smul_comm]`.

Conclude with `hNmin z i hi`. Establish `hw : ∀ i, ∃ w ∈ R, n i ≠ 0 → w * (f i * (π ^ (n i - 1) • z)) = f i`. Introduce `i`. Distinguish the cases in `hi : n i = 0`. Conclude with `⟨0, R.zero_mem, fun h => absurd hi h⟩`.

Take `⟨w, hwO, hw⟩` from `hvp i _ (hnmin i hi)`. Conclude with `⟨w, (hOR w).1 hwO, fun _ => hw⟩`. Use `choose w hwR hwf using hw`. Take `⟨a, ha⟩ : ∃ a : Fin m → A.K, ∀ i, a i = if n i = 0 then 1 else w i` from `⟨_, fun i => rfl⟩`. Take `⟨c, hc⟩ : ∃ c : Fin m → A.K, ∀ i, c i = if n i = 0 then 1 else π ^ (n i - 1) • z` from `⟨_, fun i => rfl⟩`.

Establish `haR : ∀ i, a i ∈ R` using `fun i => by`. Rewrite using `[ha]`. Use `split_ifs`. Conclude with `R.one_mem`. Conclude with `hwR i`.

Establish `hac : ∀ i, f i * (a i * c i) = f i` using `fun i => by`. Rewrite using `[ha, hc]`. Use `split_ifs with hi`. Expand and normalize the polynomial expressions, which then agree. Take the linear combination `hwf i hi`.

Take `⟨σ, hσ⟩ : ∃ σ : A.K, σ = ∑ i, f i * a i` from `⟨_, rfl⟩`. Take `⟨σ', hσ'⟩ : ∃ σ' : A.K, σ' = ∑ i, f i * c i` from `⟨_, rfl⟩`. Establish `hfσ : ∀ j, f j * σ = f j * a j` using `fun j => by rw [hσ]; exact mul_sum_eq hid hor a j`. Establish `hfσ' : ∀ j, f j * σ' = f j * c j` using `fun j => by rw [hσ']; exact mul_sum_eq hid hor c j`. Establish `hσσ : σ * σ' = 1`.

Use `eq_of_mul_eq hsum fun j => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Set `σU : A.Kˣ` to `⟨σ, σ', hσσ, by rw [mul_comm]; exact hσσ⟩`. Establish `hσR : σ ∈ R` using `by rw [hσ]; exact R.sum_mem fun i _ => R.mul_mem (hfR i) (haR i)`. Set `q : A.Kˣ` to `∏ i, u i ^ (n i - 1)`.

Establish `hfq : ∀ j, f j * (q : A.K) = f j * p ^ (n j - 1)` using `fun j => by`. Rewrite using `[Units.coe_prod]`. Simplify using `only [Units.val_pow_eq_pow_val]`. Conclude with `mul_prod_eq hid hor (fun _ => p) (fun i => n i - 1) j`. Establish `hqR : (q : A.K) ∈ R`.

Rewrite using `[Units.coe_prod]`. Conclude with `R.prod_mem fun i _ => by rw [Units.val_pow_eq_pow_val]; exact R.pow_mem (huR i) _`. Establish `hsval : ((σU * q : A.Kˣ) : A.K) = σ * q` using `rfl`. Establish `hfs : ∀ j, f j * ((σU * q : A.Kˣ) : A.K) = a j * (f j * p ^ (n j - 1))` using `fun j => by`. Rewrite using `[hsval, ← hfq]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hfs0 : ∀ j, n j = 0 → f j * ((σU * q : A.Kˣ) : A.K) = f j` using `fun j hj => by`. Rewrite using `[hfs, ha, if_pos hj, hj]`. Simplify using the standard rewrite rules. Establish `hfsz : ∀ j, f j * (((σU * q : A.Kˣ) : A.K) * z) = if n j = 0 then f j * z else f j`.

Introduce `j`. Rewrite using `[← mul_assoc, hfs]`. Use `split_ifs with hj`. Rewrite using `[ha, if_pos hj, hj]`. Simplify using the standard rewrite rules.

Establish `h1` using `hwf j hj`. Rewrite `h1` using `[hsmul]`. Rewrite using `[ha, if_neg hj]`. Take the linear combination `h1`. Use `⟨σU * q, ⟨?_, ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[hOR, hsval]`. Conclude with `R.mul_mem hσR hqR`. Rewrite using `[hOR, hrep (((σU * q : A.Kˣ) : A.K) * z)]`. Use `R.sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hfsz]`.

Use `split_ifs with hj`. Establish `h1` using `hn0 j`. Rewrite `h1` using `[hj, pow_zero, one_smul, hOR]`. Conclude with `h1`. Conclude with `hfR j`.

Use `⟨∑ i, f i * (if n i = 0 then 1 else 0), ?_, ∑ i, f i * (if n i = 0 then 0 else 1), ?_, eq_of_mul_eq hsum fun j => ?_⟩` and prove the remaining obligations. Rewrite using `[hOR]`. Use `R.sum_mem fun i _ => R.mul_mem (hfR i) ?_ split_ifs` and prove the remaining obligations. Conclude with `R.one_mem`. Conclude with `R.zero_mem`.

Rewrite using `[hOR]`. Use `R.sum_mem fun i _ => R.mul_mem (hfR i) ?_ split_ifs` and prove the remaining obligations. Conclude with `R.zero_mem`. Conclude with `R.one_mem`. Establish `e1 : ∀ (x y X Y : A.K), f j * (x * X + y * Y) = (f j * x) * X + (f j * y) * Y` using `fun x y X Y => by ring`.

Rewrite using `[e1, mul_sum_eq hid hor, mul_sum_eq hid hor]`. Use `split_ifs with hj`. Rewrite using `[mul_one, mul_zero, zero_mul, add_zero, hfs0 j hj]`. Rewrite using `[mul_zero, zero_mul, zero_add, mul_one, hfsz, if_neg hj]`. Rewrite using `[map_mul, map_prod]`.

Simplify using `only [map_pow]`. Conclude with `mul_le_of_le_one_left zero_le (hle1 σU hσR)`. Use `set C : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i) : ℝ≥0∞) with hCdef`. Use `set D : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i)⁻¹ : ℝ≥0∞) with hDdef`. Establish `hCD : ∀ i, C i * D i = 1` using `fun i => by`.

Simplify using `only [hCdef, hDdef]`. Rewrite using `[← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one]`. Establish `hC1 : ∀ i, C i < 1` using `fun i => ENNReal.coe_lt_one_iff.2 (hlt1 i)`. Establish `hD1 : ∀ i, 1 ≤ D i` using `fun i => by`. Combine the equalities or inequalities in the displayed calculation.

Establish `hpow : ∀ i (k : ℕ), C i ^ (k - 1) ≤ D i * C i ^ k` using `fun i k => by`. Consider the cases of `k with`. Consider the case `zero => simpa using hD1 i`. Consider the case `succ k`. Rewrite using `[Nat.add_sub_cancel, pow_succ, show D i * (C i ^ k * C i) = C i ^ k * (C i * D i) by ring, hCD, mul_one]`.

Set `Q : (Fin m → ℕ) → A.Kˣ` to `fun k => ∏ i, u i ^ k i`. Establish `hfQ : ∀ k j, f j * (Q k : A.K) = f j * p ^ k j` using `fun k j => by`. Simplify using `only [Q]`. Rewrite using `[Units.coe_prod]`. Simplify using `only [Units.val_pow_eq_pow_val]`.

Conclude with `mul_prod_eq hid hor (fun _ => p) k j`. Set `S : (Fin m → ℕ) → Set A.K` to `fun k => {z | (Q k : A.K) * z ∈ A.OK}`. Establish `hzS : ∀ z, z ∈ S (N z)` using `fun z => by show (Q (N z) : A.K) * z ∈ A.OK`. Rewrite using `[hOR, hrep ((Q (N z) : A.K) * z)]`. Use `R.sum_mem fun j _ => ?_` and prove the remaining obligations.

Establish `h1` using `hNspec z j`. Rewrite `h1` using `[hsmul, hOR]`. Establish `e : f j * ((Q (N z) : A.K) * z) = p ^ N z j * (f j * z)`. Rewrite using `[← mul_assoc, hfQ]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `h1`. Establish `hSm : ∀ k, MeasurableSet (S k)` using `fun k => (hOo.preimage (continuous_const_mul _)).measurableSet`. Establish `hμS : ∀ k, μ (S k) = (∏ i, D i ^ k i) * μ A.OK` using `fun k => by`. Establish `hset : S k = (Q k)⁻¹ • A.OK`.

Use extensionality with `z`. Rewrite using `[Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def]`. Both sides reduce to the same expression. Establish `hinv : (Q k)⁻¹ = ∏ i, (u i)⁻¹ ^ k i`. Simplify using `only [Q, ← Finset.prod_inv_distrib, inv_pow]`.

Rewrite using `[hset, ← distribHaarChar_mul μ, hinv]`. Simplify using `only [hDdef, map_prod, map_pow, ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow]`. Use `lt_of_le_of_lt (lintegral_mono (g := fun z => ∑' k : Fin m → ℕ, (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z) fun z => ?_) ?_` and prove the remaining obligations. Take `⟨s, hs, hsle⟩` from `hkey z`. Establish `h1 : (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ≤ ∏ i, C i ^ (N z i - 1)`.

Use `(iInf₂_le s hs).trans ?_` and prove the remaining obligations. Establish `e : A.absK (s : A.K) = distribHaarChar A.K s` using `by simp [Et.absK]`. Rewrite using `[e, ENNReal.ofReal_coe_nnreal]`. Simplify using `only [hCdef]`. Conclude with `hsle` after adjusting the coercions.

Establish `h2 : ∏ i, C i ^ (N z i - 1) ≤ (∏ i, D i) * ∏ i, C i ^ N z i`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_le_prod' fun i _ => hpow i _`. Use `le_trans ?_ (ENNReal.le_tsum (N z))` and prove the remaining obligations. Rewrite using `[Set.indicator_of_mem (hzS z), Finset.prod_pow, ← mul_pow]`.

Conclude with `pow_le_pow_left₀ zero_le (h1.trans h2) 2`. Rewrite using `[lintegral_tsum (fun k => (measurable_const.indicator (hSm k)).aemeasurable)]`. Establish `hterm : ∀ k : Fin m → ℕ, ∫⁻ z, (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z ∂μ = ((∏ i, D i) ^ 2 * μ A.OK) * ∏ i, C i ^ k i`. Introduce `k`. Rewrite using `[lintegral_indicator_const (hSm k), hμS]`.

Establish `e : (∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i = ∏ i, C i ^ k i`. Rewrite using `[← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[sq, mul_assoc, ← mul_pow, hCD, one_pow, mul_one]`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[tsum_congr hterm, ENNReal.tsum_mul_left]`. Use `ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top (ENNReal.prod_lt_top fun i _ => ENNReal.coe_lt_top)) hμOt.lt_top) ?_` and prove the remaining obligations. Use `lt_of_le_of_lt (tsum_pi_prod_le' (fun i (x : ℕ) => C i ^ x)) ?_` and prove the remaining obligations. Use `ENNReal.prod_lt_top fun i _ => ?_` and prove the remaining obligations. Rewrite using `[ENNReal.tsum_geometric]`.

Conclude with `ENNReal.inv_lt_top.2 (tsub_pos_of_lt (hC1 i))`.
-/
theorem height_sq_lintegral_lt_top : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (μ : Measure A.K), μ.IsAddHaarMeasure → ∫⁻ z, (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ^ 2 ∂μ < ⊤ := by
  intro F E _ _ _ _ hU A μ hμ
  classical
  haveI := hU.ultraF; haveI := hU.lcF; haveI := hU.charZero
  haveI : ProperSpace F := .of_nontriviallyNormedField_of_weaklyLocallyCompactSpace F
  haveI : IsTopologicalAddGroup A.K := IsModuleTopology.topologicalAddGroup F A.K
  haveI : ContinuousSMul F A.K := IsModuleTopology.toContinuousSMul F A.K
  let b := Module.finBasis F A.K
  haveI : T2Space A.K := .of_injective_continuous b.equivFun.injective
    (IsModuleTopology.continuous_of_linearMap b.equivFun.toLinearMap)
  haveI : SecondCountableTopology A.K := b.equivFunL.toHomeomorph.secondCountableTopology
  obtain ⟨-, -, -, -, -, -, -, -, -, hOo, hOc, R, hR⟩ := GlobalTheory.T.etaleHermitianPair_structure_facts F E A
  obtain ⟨m, f, hid, hor, hsum, hsc, hvp⟩ :=
    GlobalTheory.T.idempotent_decomposition_of_integrality F E A (fun k _ _ _ y hy => GlobalTheory.T.isIntegral_or_inv_isIntegral_finite_ext_ultrametric F k y hy)
  have hOR : ∀ x, x ∈ A.OK ↔ x ∈ R := fun x => by rw [← hR, SetLike.mem_coe]
  have hfR : ∀ i, f i ∈ R := fun i => by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    refine ⟨Polynomial.X ^ 2 - Polynomial.X, Polynomial.monic_X_pow_sub (by rw [Polynomial.degree_X]; norm_num), ?_⟩
    simp [sq, hid i]
  obtain ⟨π, hπ0, hπ1⟩ := NormedField.exists_norm_lt_one F
  have hπ : π ≠ 0 := norm_pos_iff.1 hπ0
  have hpp : algebraMap F A.K π * algebraMap F A.K π⁻¹ = 1 := by
    rw [← map_mul, mul_inv_cancel₀ hπ, map_one]
  have hpR : algebraMap F A.K π ∈ R := by
    rw [← hOR, Et.mem_OK_iff_isIntegral]
    have hmem : π ∈ (NormedField.valuation (K := F)).integer := by
      rw [Valuation.mem_integer_iff, NormedField.valuation_apply]; exact_mod_cast hπ1.le
    exact (isIntegral_algebraMap (R := (NormedField.valuation (K := F)).integer) (A := A.K) (x := ⟨π, hmem⟩) : _)
  set p := algebraMap F A.K π with hp
  set p' := algebraMap F A.K π⁻¹ with hp'
  let u : Fin m → A.Kˣ := fun i => ⟨f i * p + (1 - f i), f i * p' + (1 - f i),
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i,
    by linear_combination (f i * f i) * hpp + (2 - p - p') * hid i⟩
  have hu : ∀ i, ((u i : A.Kˣ) : A.K) = f i * p + (1 - f i) := fun i => rfl
  have huR : ∀ i, ((u i : A.Kˣ) : A.K) ∈ R := fun i => by
    rw [hu]; exact R.add_mem (R.mul_mem (hfR i) hpR) (R.sub_mem R.one_mem (hfR i))
  haveI : μ.IsAddHaarMeasure := hμ
  have hμO0 : μ A.OK ≠ 0 := hOo.measure_ne_zero μ ⟨0, (hOR 0).2 R.zero_mem⟩
  have hμOt : μ A.OK ≠ ⊤ := hOc.measure_lt_top.ne
  have hsmulO : ∀ v : A.Kˣ, (v : A.K) ∈ R → v • A.OK ⊆ A.OK := by
    rintro v hv _ ⟨y, hy, rfl⟩
    rw [hOR] at hy ⊢
    exact R.mul_mem hv hy
  have hle1 : ∀ v : A.Kˣ, (v : A.K) ∈ R → distribHaarChar A.K v ≤ 1 := by
    intro v hv
    have h2 : μ (v • A.OK) ≤ μ A.OK := measure_mono (hsmulO v hv)
    rw [← distribHaarChar_mul μ] at h2
    have h3 : (distribHaarChar A.K v : ℝ≥0∞) ≤ 1 := by
      rwa [← ENNReal.mul_le_mul_iff_left hμO0 hμOt, one_mul]
    exact_mod_cast h3
  have hlt1 : ∀ i, distribHaarChar A.K (u i) < 1 := by
    intro i
    have hsub := hsmulO (u i) (huR i)
    have hcl : IsClosed ((u i) • A.OK) := (hOc.smul (u i)).isClosed
    have hfi : f i ∉ (u i) • A.OK := by
      rintro ⟨y, hy, hyf⟩
      have hyf' : ((u i : A.Kˣ) : A.K) * y = f i := hyf
      have hy' : y = p' * f i := by
        have h1 : y = (((u i)⁻¹ : A.Kˣ) : A.K) * f i := by rw [← hyf', Units.inv_mul_cancel_left]
        rw [h1]
        show (f i * p' + (1 - f i)) * f i = p' * f i
        linear_combination (p' - 1) * hid i
      have hn : 1 < ‖π⁻¹‖ := by rw [norm_inv]; exact (one_lt_inv₀ hπ0).2 hπ1
      exact hsc i π⁻¹ hn (hy' ▸ hy)
    have hopen : IsOpen (A.OK \ (u i) • A.OK) := hOo.sdiff hcl
    have hpos : μ (A.OK \ (u i) • A.OK) ≠ 0 := hopen.measure_ne_zero μ ⟨f i, (hOR _).2 (hfR i), hfi⟩
    have hadd : μ ((u i) • A.OK) + μ (A.OK \ (u i) • A.OK) = μ A.OK := by
      rw [measure_add_sdiff hcl.measurableSet.nullMeasurableSet, Set.union_eq_right.2 hsub]
    have hlt : μ ((u i) • A.OK) < μ A.OK := by
      rw [← hadd]; exact ENNReal.lt_add_right (ne_top_of_le_ne_top hμOt (measure_mono hsub)) hpos
    rw [← distribHaarChar_mul μ] at hlt
    have h4 : (distribHaarChar A.K (u i) : ℝ≥0∞) < 1 := by
      by_contra hc
      have hc' : 1 ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) := not_lt.1 hc
      have h5 : 1 * μ A.OK ≤ (distribHaarChar A.K (u i) : ℝ≥0∞) * μ A.OK := by gcongr
      rw [one_mul] at h5; exact absurd hlt (not_lt.2 h5)
    exact_mod_cast h4
  have hex : ∀ z : A.K, ∀ i, ∃ n : ℕ, π ^ n • (f i * z) ∈ A.OK := by
    intro z i
    have ht : Tendsto (fun n : ℕ => π ^ n • (f i * z)) atTop (𝓝 0) := by
      have := (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hπ1).smul_const (f i * z)
      simpa using this
    exact (ht.eventually (hOo.mem_nhds ((hOR 0).2 R.zero_mem))).exists

  let N : A.K → Fin m → ℕ := fun z i => Nat.find (hex z i)
  have hNspec : ∀ z i, π ^ N z i • (f i * z) ∈ A.OK := fun z i => Nat.find_spec (hex z i)
  have hNmin : ∀ z i, N z i ≠ 0 → π ^ (N z i - 1) • (f i * z) ∉ A.OK := fun z i hi =>
    Nat.find_min (hex z i) (Nat.sub_lt (Nat.pos_of_ne_zero hi) one_pos)
  have hsmul : ∀ (k : ℕ) (x : A.K), π ^ k • x = p ^ k * x := fun k x => by
    rw [Algebra.smul_def, map_pow]
  have hrep : ∀ x : A.K, x = ∑ j, f j * x := fun x => by rw [← Finset.sum_mul, hsum, one_mul]
  have hkey : ∀ z : A.K, ∃ s : A.Kˣ, ((s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧
      ∃ α ∈ A.OK, ∃ β ∈ A.OK, α * s + β * (s * z) = 1) ∧
      distribHaarChar A.K s ≤ ∏ i, distribHaarChar A.K (u i) ^ (N z i - 1) := by
    intro z
    set n := N z with hn
    have hn0 : ∀ i, π ^ n i • (f i * z) ∈ A.OK := fun i => hNspec z i
    have hnmin : ∀ i, n i ≠ 0 → f i * (π ^ (n i - 1) • z) ∉ A.OK := fun i hi => by
      rw [mul_smul_comm]; exact hNmin z i hi
    have hw : ∀ i, ∃ w ∈ R, n i ≠ 0 → w * (f i * (π ^ (n i - 1) • z)) = f i := by
      intro i
      by_cases hi : n i = 0
      · exact ⟨0, R.zero_mem, fun h => absurd hi h⟩
      · obtain ⟨w, hwO, hw⟩ := hvp i _ (hnmin i hi)
        exact ⟨w, (hOR w).1 hwO, fun _ => hw⟩
    choose w hwR hwf using hw
    obtain ⟨a, ha⟩ : ∃ a : Fin m → A.K, ∀ i, a i = if n i = 0 then 1 else w i := ⟨_, fun i => rfl⟩
    obtain ⟨c, hc⟩ : ∃ c : Fin m → A.K, ∀ i, c i = if n i = 0 then 1 else π ^ (n i - 1) • z :=
      ⟨_, fun i => rfl⟩
    have haR : ∀ i, a i ∈ R := fun i => by
      rw [ha]; split_ifs
      · exact R.one_mem
      · exact hwR i
    have hac : ∀ i, f i * (a i * c i) = f i := fun i => by
      rw [ha, hc]; split_ifs with hi
      · ring
      · linear_combination hwf i hi
    obtain ⟨σ, hσ⟩ : ∃ σ : A.K, σ = ∑ i, f i * a i := ⟨_, rfl⟩
    obtain ⟨σ', hσ'⟩ : ∃ σ' : A.K, σ' = ∑ i, f i * c i := ⟨_, rfl⟩
    have hfσ : ∀ j, f j * σ = f j * a j := fun j => by rw [hσ]; exact mul_sum_eq hid hor a j
    have hfσ' : ∀ j, f j * σ' = f j * c j := fun j => by rw [hσ']; exact mul_sum_eq hid hor c j
    have hσσ : σ * σ' = 1 := by
      refine eq_of_mul_eq hsum fun j => ?_
      calc f j * (σ * σ') = (f j * σ) * σ' := by ring
        _ = a j * (f j * σ') := by rw [hfσ]; ring
        _ = f j * (a j * c j) := by rw [hfσ']; ring
        _ = f j * 1 := by rw [hac, mul_one]
    let σU : A.Kˣ := ⟨σ, σ', hσσ, by rw [mul_comm]; exact hσσ⟩
    have hσR : σ ∈ R := by rw [hσ]; exact R.sum_mem fun i _ => R.mul_mem (hfR i) (haR i)
    let q : A.Kˣ := ∏ i, u i ^ (n i - 1)
    have hfq : ∀ j, f j * (q : A.K) = f j * p ^ (n j - 1) := fun j => by
      rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
      exact mul_prod_eq hid hor (fun _ => p) (fun i => n i - 1) j
    have hqR : (q : A.K) ∈ R := by
      rw [Units.coe_prod]
      exact R.prod_mem fun i _ => by rw [Units.val_pow_eq_pow_val]; exact R.pow_mem (huR i) _
    have hsval : ((σU * q : A.Kˣ) : A.K) = σ * q := rfl
    have hfs : ∀ j, f j * ((σU * q : A.Kˣ) : A.K) = a j * (f j * p ^ (n j - 1)) := fun j => by
      rw [hsval, ← hfq]
      calc f j * (σ * q) = (f j * σ) * q := by ring
        _ = _ := by rw [hfσ]; ring
    have hfs0 : ∀ j, n j = 0 → f j * ((σU * q : A.Kˣ) : A.K) = f j := fun j hj => by
      rw [hfs, ha, if_pos hj, hj]; simp
    have hfsz : ∀ j, f j * (((σU * q : A.Kˣ) : A.K) * z) = if n j = 0 then f j * z else f j := by
      intro j
      rw [← mul_assoc, hfs]
      split_ifs with hj
      · rw [ha, if_pos hj, hj]; simp
      · have h1 := hwf j hj
        rw [hsmul] at h1
        rw [ha, if_neg hj]; linear_combination h1
    refine ⟨σU * q, ⟨?_, ?_, ?_⟩, ?_⟩
    · rw [hOR, hsval]; exact R.mul_mem hσR hqR
    · rw [hOR, hrep (((σU * q : A.Kˣ) : A.K) * z)]
      refine R.sum_mem fun j _ => ?_
      rw [hfsz]; split_ifs with hj
      · have h1 := hn0 j; rw [hj, pow_zero, one_smul, hOR] at h1; exact h1
      · exact hfR j
    · refine ⟨∑ i, f i * (if n i = 0 then 1 else 0), ?_, ∑ i, f i * (if n i = 0 then 0 else 1), ?_,
        eq_of_mul_eq hsum fun j => ?_⟩
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.one_mem
        · exact R.zero_mem
      · rw [hOR]; refine R.sum_mem fun i _ => R.mul_mem (hfR i) ?_
        split_ifs
        · exact R.zero_mem
        · exact R.one_mem
      · have e1 : ∀ (x y X Y : A.K), f j * (x * X + y * Y) = (f j * x) * X + (f j * y) * Y :=
          fun x y X Y => by ring
        rw [e1, mul_sum_eq hid hor, mul_sum_eq hid hor]
        split_ifs with hj
        · rw [mul_one, mul_zero, zero_mul, add_zero, hfs0 j hj]
        · rw [mul_zero, zero_mul, zero_add, mul_one, hfsz, if_neg hj]
    · rw [map_mul, map_prod]; simp only [map_pow]
      exact mul_le_of_le_one_left zero_le (hle1 σU hσR)

  set C : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i) : ℝ≥0∞) with hCdef
  set D : Fin m → ℝ≥0∞ := fun i => (distribHaarChar A.K (u i)⁻¹ : ℝ≥0∞) with hDdef
  have hCD : ∀ i, C i * D i = 1 := fun i => by
    simp only [hCdef, hDdef]
    rw [← ENNReal.coe_mul, ← map_mul, mul_inv_cancel, map_one, ENNReal.coe_one]
  have hC1 : ∀ i, C i < 1 := fun i => ENNReal.coe_lt_one_iff.2 (hlt1 i)
  have hD1 : ∀ i, 1 ≤ D i := fun i => by
    calc (1 : ℝ≥0∞) = C i * D i := (hCD i).symm
      _ ≤ 1 * D i := by gcongr; exact (hC1 i).le
      _ = D i := one_mul _
  have hpow : ∀ i (k : ℕ), C i ^ (k - 1) ≤ D i * C i ^ k := fun i k => by
    cases k with
    | zero => simpa using hD1 i
    | succ k =>
      rw [Nat.add_sub_cancel, pow_succ, show D i * (C i ^ k * C i) = C i ^ k * (C i * D i) by ring,
        hCD, mul_one]
  let Q : (Fin m → ℕ) → A.Kˣ := fun k => ∏ i, u i ^ k i
  have hfQ : ∀ k j, f j * (Q k : A.K) = f j * p ^ k j := fun k j => by
    simp only [Q]; rw [Units.coe_prod]; simp only [Units.val_pow_eq_pow_val]
    exact mul_prod_eq hid hor (fun _ => p) k j
  let S : (Fin m → ℕ) → Set A.K := fun k => {z | (Q k : A.K) * z ∈ A.OK}
  have hzS : ∀ z, z ∈ S (N z) := fun z => by
    show (Q (N z) : A.K) * z ∈ A.OK
    rw [hOR, hrep ((Q (N z) : A.K) * z)]
    refine R.sum_mem fun j _ => ?_
    have h1 := hNspec z j
    rw [hsmul, hOR] at h1
    have e : f j * ((Q (N z) : A.K) * z) = p ^ N z j * (f j * z) := by
      rw [← mul_assoc, hfQ]; ring
    rw [e]; exact h1
  have hSm : ∀ k, MeasurableSet (S k) := fun k =>
    (hOo.preimage (continuous_const_mul _)).measurableSet
  have hμS : ∀ k, μ (S k) = (∏ i, D i ^ k i) * μ A.OK := fun k => by
    have hset : S k = (Q k)⁻¹ • A.OK := by
      ext z; rw [Set.mem_smul_set_iff_inv_smul_mem, inv_inv, Units.smul_def]; rfl
    have hinv : (Q k)⁻¹ = ∏ i, (u i)⁻¹ ^ k i := by
      simp only [Q, ← Finset.prod_inv_distrib, inv_pow]
    rw [hset, ← distribHaarChar_mul μ, hinv]
    simp only [hDdef, map_prod, map_pow, ENNReal.ofNNReal_finsetProd, ENNReal.coe_pow]
  refine lt_of_le_of_lt (lintegral_mono (g := fun z => ∑' k : Fin m → ℕ,
    (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z) fun z => ?_) ?_
  · obtain ⟨s, hs, hsle⟩ := hkey z
    have h1 : (⨅ (s : A.Kˣ) (_ : (s : A.K) ∈ A.OK ∧ (s : A.K) * z ∈ A.OK ∧ ∃ α ∈ A.OK, ∃ β ∈ A.OK,
        α * s + β * (s * z) = 1), ENNReal.ofReal (A.absK s)) ≤ ∏ i, C i ^ (N z i - 1) := by
      refine (iInf₂_le s hs).trans ?_
      have e : A.absK (s : A.K) = distribHaarChar A.K s := by simp [Et.absK]
      rw [e, ENNReal.ofReal_coe_nnreal]
      simp only [hCdef]
      exact_mod_cast hsle
    have h2 : ∏ i, C i ^ (N z i - 1) ≤ (∏ i, D i) * ∏ i, C i ^ N z i := by
      rw [← Finset.prod_mul_distrib]; exact Finset.prod_le_prod' fun i _ => hpow i _
    refine le_trans ?_ (ENNReal.le_tsum (N z))
    rw [Set.indicator_of_mem (hzS z), Finset.prod_pow, ← mul_pow]
    exact pow_le_pow_left₀ zero_le (h1.trans h2) 2
  · rw [lintegral_tsum (fun k => (measurable_const.indicator (hSm k)).aemeasurable)]
    have hterm : ∀ k : Fin m → ℕ, ∫⁻ z, (S k).indicator (fun _ => (∏ i, D i) ^ 2 * ∏ i, (C i ^ k i) ^ 2) z ∂μ
        = ((∏ i, D i) ^ 2 * μ A.OK) * ∏ i, C i ^ k i := by
      intro k
      rw [lintegral_indicator_const (hSm k), hμS]
      have e : (∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i = ∏ i, C i ^ k i := by
        rw [← Finset.prod_mul_distrib]; refine Finset.prod_congr rfl fun i _ => ?_
        rw [sq, mul_assoc, ← mul_pow, hCD, one_pow, mul_one]
      calc _ = (∏ i, D i) ^ 2 * μ A.OK * ((∏ i, (C i ^ k i) ^ 2) * ∏ i, D i ^ k i) := by ring
        _ = _ := by rw [e]
    rw [tsum_congr hterm, ENNReal.tsum_mul_left]
    refine ENNReal.mul_lt_top (ENNReal.mul_lt_top (ENNReal.pow_lt_top
      (ENNReal.prod_lt_top fun i _ => ENNReal.coe_lt_top)) hμOt.lt_top) ?_
    refine lt_of_le_of_lt (tsum_pi_prod_le' (fun i (x : ℕ) => C i ^ x)) ?_
    refine ENNReal.prod_lt_top fun i _ => ?_
    rw [ENNReal.tsum_geometric]
    exact ENNReal.inv_lt_top.2 (tsub_pos_of_lt (hC1 i))

end GlobalTheory.JR.HeightSquareIntegrable
