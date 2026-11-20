import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.HasLevelStd
import Development.AbelianVarietyTheory.Definitions.Divisors.HasQIff
import Development.AbelianVarietyTheory.Definitions.Divisors.JetAnalytic
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastAtEmbeddingRingOps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHilbertEisensteinFourierCoeffFamilyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OmegaFactorPowTwoMul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HasQExpansionOfLevelHilbertEisensteinQuasiPeriodStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSplitOfHilbertLatticeHasLevelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastInverseDifferentElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlgebraicValuationAtLeastRatCastAndExpRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PartialZetaConstTermEqRationalValueStatement
open NumberField UpperHalfPlane GlobalTheory.HilbFam GlobalTheory.QFam
open GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization (Emb Frac latM qPow upperHalf cK omegaFactor IsPartialZeta HasExpansion)
open GlobalTheory.IndefiniteRowSideFullHecke.DefiningCoordinates (iterD partialD)
open scoped Classical MatrixGroups nonZeroDivisors
open GlobalTheory.LatVal (Sz)
open GlobalTheory.LatJet (EisExp IsEis FR)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.1 r s x hrs hx`.
-/
private theorem sz_mono_divisor {r s : ℝ} {x : ℂ} (hrs : r ≤ s)
    (hx : _root_.GlobalTheory.LatVal.Sz l lam r x) :
    _root_.GlobalTheory.LatVal.Sz l lam s x :=
  (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.1 r s x hrs hx

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
/- English proof (translation)
Use `set t : F := ((M * l ^ b : ℕ) : F) with ht_def`. Establish `hdual : ∀ α ∈ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F), t * α ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM (1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F)`. Introduce `α hα`. Rewrite `ht`, the goal using `[_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]`. Establish `h0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `Units.ne_zero _`.

Use `FractionalIdeal.mul_mem_mul ht hα` as an intermediate fact. Rewrite `this` using `[FractionalIdeal.dual_mul_self ℤ ℚ h0]`. Simplify using `using this`. Establish `key : _root_.GlobalTheory.LatVal.Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i (t * ξ) : ℝ) : ℂ)`. Rewrite `hξ` using `[Units.val_mul, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul]`.

Establish `hmul : t * ξ ∈ ({y | _root_.GlobalTheory.LatVal.Sz l lam ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i y : ℝ) : ℂ)} : Set F)`. Use `Submodule.mul_induction_on hξ ?_ ?_` and prove the remaining obligations. Introduce `α hα β hβ show _root_.GlobalTheory.LatVal.Sz l lam _ _`. Rewrite using `[← mul_assoc, map_mul, Complex.ofReal_mul]`. Conclude with `_root_.GlobalTheory.QFam.SzSum.sz_mul (_root_.GlobalTheory.DiffSize.sz_invDiff l lam F _ i (hdual α hα)) (h𝔟 β hβ i)`.

Introduce `y z hy hz show _root_.GlobalTheory.LatVal.Sz l lam _ _`. Rewrite using `[mul_add, map_add, Complex.ofReal_add]`. Conclude with `((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.1 _ _ _ hy hz).1`. Conclude with `hmul`. Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`.

Establish `hMl : M * l ^ b ≠ 0` using `Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)`. Establish `hq : _root_.GlobalTheory.LatVal.Sz l lam b (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ)`. Use `(_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_` and prove the remaining obligations. Rewrite using `[one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.mul (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hM]`. Simplify using the standard rewrite rules.

Establish `heq : ((i ξ : ℝ) : ℂ) = (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ) * ((i (t * ξ) : ℝ) : ℂ)`. Establish `: ((M * l ^ b : ℕ) : ℂ) ≠ 0` using `by exact_mod_cast hMl`. Rewrite using `[ht_def, map_mul, map_natCast, Complex.ofReal_mul, Complex.ofReal_natCast, ← mul_assoc, one_div, Rat.cast_inv, Rat.cast_natCast, inv_mul_cancel₀ this, one_mul]`. Rewrite using `[heq]`. Use `_root_.GlobalTheory.QFam.SzSum.sz_mul hq key` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem valBound_embedding_mem_mul_lemma_2 {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {F : Type} [Field F] [NumberField F] [IsTotallyReal F] [IsGalois ℚ F]
    {𝔞 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F} {ρ₀ : ℝ} {M b : ℕ} (hM : ¬ l ∣ M)
    (ht : ((M * l ^ b : ℕ) : F) ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞)
    (h𝔟 : ∀ β ∈ ((𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i β : ℝ) : ℂ))
    {ξ : F} (hξ : ξ ∈ (((𝔞 * 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
      FractionalIdeal (𝓞 F)⁰ F)) (i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F) :
    _root_.GlobalTheory.LatVal.Sz l lam
      (b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i ξ : ℝ) : ℂ) := by
  set t : F := ((M * l ^ b : ℕ) : F) with ht_def
  have hdual : ∀ α ∈ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      t * α ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM (1 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) := by
    intro α hα
    rw [_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual] at ht ⊢
    have h0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero _
    have := FractionalIdeal.mul_mem_mul ht hα
    rw [FractionalIdeal.dual_mul_self ℤ ℚ h0] at this
    simpa using this
  have key : _root_.GlobalTheory.LatVal.Sz l lam
      ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i (t * ξ) : ℝ) : ℂ) := by
    rw [Units.val_mul, ← FractionalIdeal.mem_coe, FractionalIdeal.coe_mul] at hξ
    have hmul : t * ξ ∈ ({y | _root_.GlobalTheory.LatVal.Sz l lam
        ((padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀) ((i y : ℝ) : ℂ)} : Set F) := by
      refine Submodule.mul_induction_on hξ ?_ ?_
      · intro α hα β hβ
        show _root_.GlobalTheory.LatVal.Sz l lam _ _
        rw [← mul_assoc, map_mul, Complex.ofReal_mul]
        exact _root_.GlobalTheory.QFam.SzSum.sz_mul
          (_root_.GlobalTheory.DiffSize.sz_invDiff l lam F _ i (hdual α hα)) (h𝔟 β hβ i)
      · intro y z hy hz
        show _root_.GlobalTheory.LatVal.Sz l lam _ _
        rw [mul_add, map_add, Complex.ofReal_add]
        exact ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.1 _ _ _ hy hz).1
    exact hmul
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  have hMl : M * l ^ b ≠ 0 := Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)
  have hq : _root_.GlobalTheory.LatVal.Sz l lam b (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ) := by
    refine (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_
    rw [one_div, padicValRat.inv, padicValRat.of_nat, padicValNat.mul
      (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0), padicValNat.prime_pow,
      padicValNat.eq_zero_of_not_dvd hM]
    simp
  have heq : ((i ξ : ℝ) : ℂ) = (((1 / (M * l ^ b : ℕ) : ℚ)) : ℂ) * ((i (t * ξ) : ℝ) : ℂ) := by
    have : ((M * l ^ b : ℕ) : ℂ) ≠ 0 := by exact_mod_cast hMl
    rw [ht_def, map_mul, map_natCast, Complex.ofReal_mul, Complex.ofReal_natCast, ← mul_assoc,
      one_div, Rat.cast_inv, Rat.cast_natCast, inv_mul_cancel₀ this, one_mul]
  rw [heq]
  have := _root_.GlobalTheory.QFam.SzSum.sz_mul hq key
  convert this using 1
  ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
The claim follows from `sz_mono_divisor hr ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.2.1 m)`.
-/
private theorem sz_intCast_of_nonneg {r : ℝ} (hr : 0 ≤ r) (m : ℤ) :
    _root_.GlobalTheory.LatVal.Sz l lam r (m : ℂ) :=
  sz_mono_divisor hr ((_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).2.2.2.2.1 m)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
The claim follows from `(_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).1 r`.
-/
private theorem sz_zero' (r : ℝ) : _root_.GlobalTheory.LatVal.Sz l lam r 0 :=
  (_root_.GlobalTheory.QFam.SzSum.sz_ring l lam).1 r

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
Distinguish the cases in `h : (Function.support f).Finite`. Rewrite using `[finsum_eq_sum f h]`. Conclude with `_root_.GlobalTheory.QFam.SzSum.sz_sum _ fun a _ => hf a`. Rewrite using `[finsum_of_infinite_support h]`. Conclude with `sz_zero' r`.
-/
private theorem sz_finsum {α : Type*} {r : ℝ} {f : α → ℂ}
    (hf : ∀ a, _root_.GlobalTheory.LatVal.Sz l lam r (f a)) :
    _root_.GlobalTheory.LatVal.Sz l lam r (∑ᶠ a, f a) := by
  by_cases h : (Function.support f).Finite
  · rw [finsum_eq_sum f h]
    exact _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun a _ => hf a
  · rw [finsum_of_infinite_support h]
    exact sz_zero' r

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
/- English proof (translation)
Proceed by induction on `t using Finset.induction_on with`. Consider the case `empty => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1`. Consider the case `insert j t hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj]`. Conclude with `_root_.GlobalTheory.QFam.SzSum.sz_mul (hf j (Finset.mem_insert_self j t)) (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))`.
-/
private theorem sz_finset_prod {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {ι : Type*} [DecidableEq ι] (t : Finset ι) {w : ι → ℝ} {f : ι → ℂ}
    (hf : ∀ i ∈ t, _root_.GlobalTheory.LatVal.Sz l lam (w i) (f i)) :
    _root_.GlobalTheory.LatVal.Sz l lam (∑ i ∈ t, w i) (∏ i ∈ t, f i) := by
  induction t using Finset.induction_on with
  | empty => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
  | insert j t hj ih =>
    rw [Finset.prod_insert hj, Finset.sum_insert hj]
    exact _root_.GlobalTheory.QFam.SzSum.sz_mul (hf j (Finset.mem_insert_self j t))
      (ih fun i hi => hf i (Finset.mem_insert_of_mem hi))

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Use `_root_.GlobalTheory.QFam.SzSum.sz_mul ih hx using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sz_pow' {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]}
    {r : ℝ} {x : ℂ} (hx : _root_.GlobalTheory.LatVal.Sz l lam r x) (m : ℕ) :
    _root_.GlobalTheory.LatVal.Sz l lam (m * r) (x ^ m) := by
  induction m with
  | zero => simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
  | succ m ih =>
    rw [pow_succ]
    convert _root_.GlobalTheory.QFam.SzSum.sz_mul ih hx using 1
    push_cast
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
/- English proof (translation)
Establish `hd : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (dual ℤ ℚ 1)⁻¹` using `coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)`. Establish `hd0 : dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `dual_ne_zero ℤ ℚ one_ne_zero`. Establish `hle : spanSingleton (𝓞 F)⁰ t * 𝔞 * ↑(differentIdeal ℤ (𝓞 F)) ≤ 1`. Rewrite using `[hd]`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `spanSingleton_le_iff_mem.mpr ht`. Use `_ = 1 := by rw [dual_mul_self ℤ ℚ h0, mul_inv_cancel₀ hd0]`. Take `⟨I, hI⟩` from `le_one_iff_exists_coeIdeal.mp hle`. Use `⟨Ideal.absNorm I, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`.

Introduce and unpack `rfl`. Rewrite `hI` using `[coeIdeal_bot]`. Use `hI.symm` as an intermediate fact. Simplify using `[mul_eq_zero, spanSingleton_eq_zero_iff, ht0, h0] at this`. Conclude with `(differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) this`.

Use `congrArg absNorm hI` as an intermediate fact. Rewrite `this` using `[coeIdeal_absNorm (R := 𝓞 F) (K := F) I, map_mul, map_mul, absNorm_span_singleton (𝓞 F), coeIdeal_absNorm (R := 𝓞 F) (K := F), absNorm_differentIdeal F (𝓞 F)]`. Rewrite using `[this, Nat.cast_natAbs, Int.cast_abs]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem absNorm_mul_norm_mul_discr_eq_natCast_of_mem_dual {F : Type} [Field F] [NumberField F] (𝔞 : FractionalIdeal (𝓞 F)⁰ F) (h0 : 𝔞 ≠ 0) (t : F) (ht0 : t ≠ 0)
    (ht : t ∈ dual ℤ ℚ 𝔞) : ∃ n : ℕ, n ≠ 0 ∧
      absNorm 𝔞 * |Algebra.norm ℚ t| * |(discr F : ℚ)| = n := by
  have hd : (↑(differentIdeal ℤ (𝓞 F)) : FractionalIdeal (𝓞 F)⁰ F) = (dual ℤ ℚ 1)⁻¹ :=
    coeIdeal_differentIdeal ℤ ℚ F (𝓞 F)
  have hd0 : dual ℤ ℚ (1 : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := dual_ne_zero ℤ ℚ one_ne_zero
  have hle : spanSingleton (𝓞 F)⁰ t * 𝔞 * ↑(differentIdeal ℤ (𝓞 F)) ≤ 1 := by
    rw [hd]
    calc spanSingleton (𝓞 F)⁰ t * 𝔞 * (dual ℤ ℚ 1)⁻¹ ≤ dual ℤ ℚ 𝔞 * 𝔞 * (dual ℤ ℚ 1)⁻¹ := by
          gcongr
          exact spanSingleton_le_iff_mem.mpr ht
      _ = 1 := by rw [dual_mul_self ℤ ℚ h0, mul_inv_cancel₀ hd0]
  obtain ⟨I, hI⟩ := le_one_iff_exists_coeIdeal.mp hle
  refine ⟨Ideal.absNorm I, ?_, ?_⟩
  · rw [Ne, Ideal.absNorm_eq_zero_iff]
    rintro rfl
    rw [coeIdeal_bot] at hI
    have := hI.symm
    simp [mul_eq_zero, spanSingleton_eq_zero_iff, ht0, h0] at this
    exact (differentIdeal_ne_bot (A := ℤ) (B := 𝓞 F)) this
  · have := congrArg absNorm hI
    rw [coeIdeal_absNorm (R := 𝓞 F) (K := F) I, map_mul, map_mul, absNorm_span_singleton (𝓞 F),
      coeIdeal_absNorm (R := 𝓞 F) (K := F), absNorm_differentIdeal F (𝓞 F)] at this
    rw [this, Nat.cast_natAbs, Int.cast_abs]
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
/- English proof (translation)
Establish `hM0 : M ≠ 0` using `by rintro rfl; exact hM (dvd_zero l)`. Establish `hl0 : l ≠ 0` using `hl.out.ne_zero`. Establish `hMl : M * l ^ b ≠ 0` using `Nat.mul_ne_zero hM0 (pow_ne_zero _ hl0)`. Establish `hDn : D.natAbs ≠ 0` using `Int.natAbs_ne_zero.mpr hD`. Establish `hprod : (M * l ^ b) ^ d * D.natAbs ≠ 0` using `Nat.mul_ne_zero (pow_ne_zero _ hMl) hDn`.

Establish `hpos : |(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)| ≠ 0`. Establish `: ((M * l ^ b : ℕ) : ℚ) ≠ 0` using `by exact_mod_cast hMl`. Establish `: (D : ℚ) ≠ 0` using `by exact_mod_cast hD`. Check the signs of the components of the expression. Establish `hA : A = n / (|(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)|)`.

Rewrite using `[eq_div_iff hpos, ← h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hAbs1 : |(((M * l ^ b : ℕ) : ℚ) ^ d)| = (((M * l ^ b : ℕ) ^ d : ℕ) : ℚ)`. Rewrite using `[abs_of_nonneg (by positivity)]; push_cast; ring`. Establish `hAbs2 : |(D : ℚ)| = ((D.natAbs : ℕ) : ℚ)`.

Rewrite using `[Nat.cast_natAbs, Int.cast_abs]`. Establish `hn' : (n : ℚ) ≠ 0` using `by exact_mod_cast hn`. Establish `hprod' : (((M * l ^ b) ^ d * D.natAbs : ℕ) : ℚ) ≠ 0` using `by exact_mod_cast hprod`. Rewrite using `[hA, hAbs1, hAbs2, ← Nat.cast_mul, padicValRat.div hn' hprod', padicValRat.of_nat, padicValRat.of_nat, padicValNat.mul (pow_ne_zero _ hMl) hDn, padicValNat.pow, padicValNat.mul hM0 (pow_ne_zero _ hl0), padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hM]`. Simplify using `only [padicValInt]`.

Use `push_cast`. Establish `h0 : (0 : ℤ) ≤ padicValRat l n` using `by rw [padicValRat.of_nat]; positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
private theorem neg_padicValRat_le_of_mul_eq_natCast {l : ℕ} [hl : Fact l.Prime] {M b d : ℕ} {D : ℤ} {A : ℚ} {n : ℕ} (hn : n ≠ 0)
    (hM : ¬ l ∣ M) (hD : D ≠ 0) (h : A * |(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)| = n) :
    -(padicValRat l A) ≤ d * b + padicValInt l D := by
  have hM0 : M ≠ 0 := by rintro rfl; exact hM (dvd_zero l)
  have hl0 : l ≠ 0 := hl.out.ne_zero
  have hMl : M * l ^ b ≠ 0 := Nat.mul_ne_zero hM0 (pow_ne_zero _ hl0)
  have hDn : D.natAbs ≠ 0 := Int.natAbs_ne_zero.mpr hD
  have hprod : (M * l ^ b) ^ d * D.natAbs ≠ 0 := Nat.mul_ne_zero (pow_ne_zero _ hMl) hDn
  have hpos : |(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)| ≠ 0 := by
    have : ((M * l ^ b : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hMl
    have : (D : ℚ) ≠ 0 := by exact_mod_cast hD
    positivity
  have hA : A = n / (|(((M * l ^ b : ℕ) : ℚ) ^ d)| * |(D : ℚ)|) := by
    rw [eq_div_iff hpos, ← h]; ring
  have hAbs1 : |(((M * l ^ b : ℕ) : ℚ) ^ d)| = (((M * l ^ b : ℕ) ^ d : ℕ) : ℚ) := by
    rw [abs_of_nonneg (by positivity)]; push_cast; ring
  have hAbs2 : |(D : ℚ)| = ((D.natAbs : ℕ) : ℚ) := by
    rw [Nat.cast_natAbs, Int.cast_abs]
  have hn' : (n : ℚ) ≠ 0 := by exact_mod_cast hn
  have hprod' : (((M * l ^ b) ^ d * D.natAbs : ℕ) : ℚ) ≠ 0 := by exact_mod_cast hprod
  rw [hA, hAbs1, hAbs2, ← Nat.cast_mul, padicValRat.div hn' hprod',
    padicValRat.of_nat, padicValRat.of_nat, padicValNat.mul (pow_ne_zero _ hMl) hDn,
    padicValNat.pow, padicValNat.mul hM0 (pow_ne_zero _ hl0), padicValNat.prime_pow,
    padicValNat.eq_zero_of_not_dvd hM]
  simp only [padicValInt]
  push_cast
  have h0 : (0 : ℤ) ≤ padicValRat l n := by rw [padicValRat.of_nat]; positivity
  linarith

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
Rewrite using `[PowerSeries.coeff_mul]`. Conclude with `_root_.GlobalTheory.QFam.SzSum.sz_sum _ fun p _ => _root_.GlobalTheory.QFam.SzSum.sz_mul (hφ p.1) (hψ p.2)`.
-/
private theorem sz_coeff_mul {r s : ℝ} {φ ψ : PowerSeries ℂ}
    (hφ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam r (PowerSeries.coeff n φ))
    (hψ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam s (PowerSeries.coeff n ψ)) (n : ℕ) :
    _root_.GlobalTheory.LatVal.Sz l lam (r + s) (PowerSeries.coeff n (φ * ψ)) := by
  rw [PowerSeries.coeff_mul]
  exact _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun p _ =>
    _root_.GlobalTheory.QFam.SzSum.sz_mul (hφ p.1) (hψ p.2)

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
variable {l : ℕ} [Fact l.Prime] {lam : algebraicClosure ℚ ℂ →+* ℂ_[l]} in
/- English proof (translation)
Proceed by induction on `m generalizing n with`. Consider the case `zero`. Rewrite using `[pow_zero, PowerSeries.coeff_one]`. Use `split_ifs`. Simplify using `using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1`.

Simplify using `using sz_zero' (lam := lam) 0`. Consider the case `succ m ih`. Rewrite using `[pow_succ]`. Use `sz_coeff_mul ih hφ n` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sz_coeff_pow {r : ℝ} {φ : PowerSeries ℂ}
    (hφ : ∀ n, _root_.GlobalTheory.LatVal.Sz l lam r (PowerSeries.coeff n φ)) (m : ℕ)
    (n : ℕ) : _root_.GlobalTheory.LatVal.Sz l lam (m * r) (PowerSeries.coeff n (φ ^ m)) := by
  induction m generalizing n with
  | zero =>
    rw [pow_zero, PowerSeries.coeff_one]
    split_ifs
    · simpa using sz_intCast_of_nonneg (lam := lam) (le_refl (0 : ℝ)) 1
    · simpa using sz_zero' (lam := lam) 0
  | succ m ih =>
    rw [pow_succ]
    have := sz_coeff_mul ih hφ n
    convert this using 1
    push_cast
    ring

open NumberField UpperHalfPlane FractionalIdeal in
open scoped nonZeroDivisors in
open scoped Classical MatrixGroups in

/- English proof (translation)
Introduce `hExp F _ _ _ hd s N L hs hN hL _ z hz l _ lam κ Ch M b e ρ₀ ρ he heC hM hML hρ₀ hρ hCh`. Take `⟨𝔞, 𝔟, x, rfl⟩` from `_root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel F N L hN hL`. Take `⟨Z, a, hZ, ha⟩` from `_root_.GlobalTheory.HilbFam.exists_isCoef hExp F hd 𝔞 𝔟 s hs`. Take `⟨c, hc, hcρ⟩` from `hCh`. Use `⟨_, _root_.GlobalTheory.HilbFam.ExpH.hasQ_hfun F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN (even_two_mul s) ha hL hc, fun n => ?_⟩` and prove the remaining obligations.

Establish `hl0 : l ≠ 0` using `(Fact.out : l.Prime).ne_zero`. Use `set d := Module.finrank ℚ F with hd_def`. Use `set t : F := ((M * l ^ b : ℕ) : F) with ht_def`. Establish `ht : t ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞`. Use `hML` as an intermediate fact.

Simplify using `only [_root_.GlobalTheory.HilbFam.split] at this`. Express the relevant statement in the definitionally equal form `(![0, t] : Fin 2 → F) 0 ∈ _ ∧ (![0, t] : Fin 2 → F) 1 - (![0, t] : Fin 2 → F) 0 * x ∈ _ at this`. Simplify using `using this.2`. Establish `ht0 : t ≠ 0`. Rewrite using `[ht_def]; exact_mod_cast Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)`.

Establish `h𝔟 : ∀ β ∈ ((𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F), ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i β : ℝ) : ℂ)`. Introduce `β hβ i`. Establish `hv : (![β, β * x] : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x`. Simplify using `only [_root_.GlobalTheory.HilbFam.split]`. Express the relevant statement in the definitionally equal form `(![β, β * x] : Fin 2 → F) 0 ∈ _ ∧ (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x ∈ _`.

Simplify using `only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]`. Conclude with `⟨hβ, zero_mem _⟩`. Simplify using `using hρ₀ _ hv i`. Establish `hξ : ∀ ξ, a ξ ≠ 0 → ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ ((i ξ : ℝ) : ℂ)`. Introduce `ξ hξ i`.

Establish `hmem : ξ ∈ (((𝔞 * 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)`. Distinguish the cases in `h0 : ξ = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Conclude with `(ha.2.2.1 ξ h0 hξ).1`.

Conclude with `sz_mono_divisor hρ (valBound_embedding_mem_mul_lemma_2 hM ht h𝔟 hmem i)`. Establish `haξ : ∀ ξ, _root_.GlobalTheory.LatVal.Sz l lam e (a ξ)`. Introduce `ξ`. Distinguish the cases in `h0 : ξ = 0`. Rewrite using `[h0, ha.1, _root_.GlobalTheory.HilbFam.constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ]`.

Conclude with `(_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ (heC _)`. Take `⟨m, hm⟩` from `ha.2.1 ξ h0`. Rewrite using `[hm]`. Conclude with `sz_intCast_of_nonneg (lam := lam) he m` after adjusting the coercions. Establish `hT : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ, ∀ m, _root_.GlobalTheory.LatVal.Sz l lam (e + ∑ i, (μ i : ℝ) * ρ) (_root_.GlobalTheory.HilbFam.ecoef N a x μ m)`.

Introduce `μ m`. Unfold `_root_.GlobalTheory.HilbFam.ecoef`. Use `sz_finsum fun ξ => ?_` and prove the remaining obligations. Rewrite using `[finsum_eq_if]`. Use `split_ifs`.

Distinguish the cases in `h0 : a ξ = 0`. Rewrite using `[h0, zero_mul, zero_mul]`. Conclude with `sz_zero' _`. Establish `hexp : _root_.GlobalTheory.LatVal.Sz l lam 0 (_root_.GlobalTheory.HilbFam.eTr (ξ * x))`. Unfold `_root_.GlobalTheory.HilbFam.eTr`.

Conclude with `(_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).2 _`. Establish `hprod` using `sz_finset_prod (lam := lam) Finset.univ (w := fun i => (μ i : ℝ) * ρ) (f := fun i => ((i ξ : ℝ) : ℂ) ^ μ i) fun i _ => sz_pow' (hξ ξ h0 i) (μ i)`. Use `_root_.GlobalTheory.QFam.SzSum.sz_mul (_root_.GlobalTheory.QFam.SzSum.sz_mul (haξ ξ) hexp) hprod` as an intermediate fact. Simplify using `using this`. Conclude with `sz_zero' _`.

Establish `hω : _root_.GlobalTheory.LatVal.Sz l lam (s * (padicValInt l (discr F) : ℝ) + 2 * s * b * d) ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ (2 * s))`. Rewrite using `[_root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]`. Use `(_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_` and prove the remaining obligations. Establish `h𝔞0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0` using `Units.ne_zero _`. Establish `htd : t ∈ FractionalIdeal.dual ℤ ℚ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)`.

Rewrite using `[← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]`. Conclude with `ht`. Take `⟨k, hk0, hk⟩` from `absNorm_mul_norm_mul_discr_eq_natCast_of_mem_dual _ h𝔞0 t ht0 htd`. Rewrite `hk` using `[ht_def, ← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap]`. Establish `hD : discr F ≠ 0` using `discr_ne_zero F`.

Establish `hv` using `neg_padicValRat_le_of_mul_eq_natCast hk0 hM hD hk`. Establish `hA0 : FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0`. Introduce `h0; rw [h0, zero_mul, zero_mul] at hk; exact hk0 (by exact_mod_cast hk.symm)`. Establish `hD' : |(discr F : ℚ)| ≠ 0` using `by simp [hD]`. Rewrite using `[padicValRat.mul (pow_ne_zero _ hD') (pow_ne_zero _ hA0), padicValRat.pow, padicValRat.pow]`.

Establish `habs : padicValRat l |(discr F : ℚ)| = padicValInt l (discr F)`. Rewrite using `[← Int.cast_abs, padicValRat.of_int]`. Simplify using `only [padicValInt, Int.natAbs_abs]`. Rewrite using `[habs]`. Establish `hv' : -(padicValRat l (FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F)) : ℝ) ≤ d * b + padicValInt l (discr F)`.

Conclude with `hv` after adjusting the coercions. Use `push_cast`. Use the polynomial consequences of the given equalities and inequalities. Unfold `_root_.GlobalTheory.HilbFam.hser`. Rewrite using `[PowerSeries.coeff_smul, map_sum]`.

Simplify using `only [PowerSeries.coeff_smul, smul_eq_mul, zsmul_eq_mul]`. Establish `hsum : _root_.GlobalTheory.LatVal.Sz l lam (e + (∑ i, κ i : ℕ) * ρ) (∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i : ℤ) : ℂ) * PowerSeries.coeff n ((PowerSeries.mk c ^ ∑ i, (κ i - μ i)) * PowerSeries.mk (_root_.GlobalTheory.HilbFam.ec …`. Use `_root_.GlobalTheory.QFam.SzSum.sz_sum _ fun μ hμ => ?_` and prove the remaining obligations. Rewrite `hμ` using `[Finset.mem_Iic]`. Establish `hC` using `sz_coeff_pow (lam := lam) (φ := PowerSeries.mk c) (fun m => by rw [PowerSeries.coeff_mk]; exact hcρ m) (∑ i, (κ i - μ i))`.

Establish `hP` using `sz_coeff_mul hC (ψ := PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ)) (fun m => by rw [PowerSeries.coeff_mk]; exact hT μ m) n`. Use `_root_.GlobalTheory.QFam.SzSum.sz_mul (sz_intCast_of_nonneg (lam := lam) le_rfl (∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i)) hP` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Establish `hnat : ∑ i, (κ i - μ i) + ∑ i, μ i = ∑ i, κ i`. Rewrite using `[← Finset.sum_add_distrib]`.

Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hμ i)`. Rewrite using `[← hnat, ← Finset.sum_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `_root_.GlobalTheory.QFam.SzSum.sz_mul hω hsum` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree.
-/
theorem _root_.GlobalTheory.HilbFam.sz_hfun_coef : _root_.GlobalTheory.LatJet.EisExp →
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], 2 ≤ Module.finrank ℚ F →
    ∀ (s N : ℕ) (L : _root_.GlobalTheory.HilbFam.Lat F), 1 ≤ s → 0 < N → _root_.GlobalTheory.HilbFam.HasLevel N L →
    ∀ [IsGalois ℚ F] (z : ClassGroup (𝓞 F) → ℚ), _root_.GlobalTheory.HilbFam.ZetaVals (2 * s) z →
    ∀ (l : ℕ) [Fact l.Prime] (lam : algebraicClosure ℚ ℂ →+* ℂ_[l]) (κ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ)
      (Ch : ℍ → ℂ) (M b : ℕ) (e ρ₀ ρ : ℝ), 0 ≤ e →
    (∀ C, -(padicValRat l (z C / 2 ^ Module.finrank ℚ F) : ℝ) ≤ e) → ¬ l ∣ M →
    ![0, ((M * l ^ b : ℕ) : F)] ∈ L →
    (∀ v ∈ L, ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F,
      _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i (v 0) : ℝ) : ℂ)) →
    b + (padicValInt l (discr F) : ℝ) / Module.finrank ℚ F + ρ₀ ≤ ρ →
    _root_.GlobalTheory.QFam.QAll (_root_.GlobalTheory.LatVal.Sz l lam ρ) N Ch →
    _root_.GlobalTheory.QFam.QAll (_root_.GlobalTheory.LatVal.Sz l lam
      (e + s * (padicValInt l (discr F) : ℝ) + 2 * s * b * Module.finrank ℚ F +
        (∑ i, κ i : ℕ) * ρ)) N (_root_.GlobalTheory.HilbFam.hfun (2 * s) L κ Ch) := by
  intro hExp F _ _ _ hd s N L hs hN hL _ z hz l _ lam κ Ch M b e ρ₀ ρ he heC hM hML hρ₀ hρ hCh
  obtain ⟨𝔞, 𝔟, x, rfl⟩ := _root_.GlobalTheory.HilbFam.exists_eq_split_of_hasLevel F N L hN hL
  obtain ⟨Z, a, hZ, ha⟩ := _root_.GlobalTheory.HilbFam.exists_isCoef hExp F hd 𝔞 𝔟 s hs
  obtain ⟨c, hc, hcρ⟩ := hCh
  refine ⟨_, _root_.GlobalTheory.HilbFam.ExpH.hasQ_hfun F (2 * s) 𝔞 𝔟 _ a x N κ Ch c hN
    (even_two_mul s) ha hL hc, fun n => ?_⟩
  have hl0 : l ≠ 0 := (Fact.out : l.Prime).ne_zero
  set d := Module.finrank ℚ F with hd_def
  set t : F := ((M * l ^ b : ℕ) : F) with ht_def

  have ht : t ∈ _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM 𝔞 := by
    have := hML
    simp only [_root_.GlobalTheory.HilbFam.split] at this
    change (![0, t] : Fin 2 → F) 0 ∈ _ ∧ (![0, t] : Fin 2 → F) 1 - (![0, t] : Fin 2 → F) 0 * x ∈ _ at this
    simpa using this.2
  have ht0 : t ≠ 0 := by
    rw [ht_def]; exact_mod_cast Nat.mul_ne_zero (by rintro rfl; exact hM (dvd_zero l)) (pow_ne_zero _ hl0)

  have h𝔟 : ∀ β ∈ ((𝔟 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F),
      ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F, _root_.GlobalTheory.LatVal.Sz l lam ρ₀ ((i β : ℝ) : ℂ) := by
    intro β hβ i
    have hv : (![β, β * x] : Fin 2 → F) ∈ _root_.GlobalTheory.HilbFam.split 𝔞 𝔟 x := by
      simp only [_root_.GlobalTheory.HilbFam.split]
      change (![β, β * x] : Fin 2 → F) 0 ∈ _ ∧
        (![β, β * x] : Fin 2 → F) 1 - (![β, β * x] : Fin 2 → F) 0 * x ∈ _
      simp only [Matrix.cons_val_zero, Matrix.cons_val_one, sub_self]
      exact ⟨hβ, zero_mem _⟩
    simpa using hρ₀ _ hv i

  have hξ : ∀ ξ, a ξ ≠ 0 → ∀ i : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F,
      _root_.GlobalTheory.LatVal.Sz l lam ρ ((i ξ : ℝ) : ℂ) := by
    intro ξ hξ i
    have hmem : ξ ∈ (((𝔞 * 𝔟 : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Frac F) : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
      by_cases h0 : ξ = 0
      · rw [h0]; exact zero_mem _
      · exact (ha.2.2.1 ξ h0 hξ).1
    exact sz_mono_divisor hρ (valBound_embedding_mem_mul_lemma_2 hM ht h𝔟 hmem i)

  have haξ : ∀ ξ, _root_.GlobalTheory.LatVal.Sz l lam e (a ξ) := by
    intro ξ
    by_cases h0 : ξ = 0
    · rw [h0, ha.1, _root_.GlobalTheory.HilbFam.constTerm_eq_zetaVal F (2 * s) z _ Z (by omega) hz hZ]
      exact (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ (heC _)
    · obtain ⟨m, hm⟩ := ha.2.1 ξ h0
      rw [hm]
      exact_mod_cast sz_intCast_of_nonneg (lam := lam) he m

  have hT : ∀ μ : _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.Emb F → ℕ, ∀ m,
      _root_.GlobalTheory.LatVal.Sz l lam (e + ∑ i, (μ i : ℝ) * ρ)
        (_root_.GlobalTheory.HilbFam.ecoef N a x μ m) := by
    intro μ m
    unfold _root_.GlobalTheory.HilbFam.ecoef
    refine sz_finsum fun ξ => ?_
    rw [finsum_eq_if]
    split_ifs
    · by_cases h0 : a ξ = 0
      · rw [h0, zero_mul, zero_mul]; exact sz_zero' _
      · have hexp : _root_.GlobalTheory.LatVal.Sz l lam 0 (_root_.GlobalTheory.HilbFam.eTr (ξ * x)) := by
          unfold _root_.GlobalTheory.HilbFam.eTr
          exact (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).2 _
        have hprod := sz_finset_prod (lam := lam) Finset.univ (w := fun i => (μ i : ℝ) * ρ)
          (f := fun i => ((i ξ : ℝ) : ℂ) ^ μ i) fun i _ => sz_pow' (hξ ξ h0 i) (μ i)
        have := _root_.GlobalTheory.QFam.SzSum.sz_mul
          (_root_.GlobalTheory.QFam.SzSum.sz_mul (haξ ξ) hexp) hprod
        simpa using this
    · exact sz_zero' _

  have hω : _root_.GlobalTheory.LatVal.Sz l lam
      (s * (padicValInt l (discr F) : ℝ) + 2 * s * b * d)
      ((_root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.omegaFactor 𝔞 : ℂ) ^ (2 * s)) := by
    rw [_root_.GlobalTheory.HilbFam.omegaFactor_pow_two_mul]
    refine (_root_.GlobalTheory.SizeRat.sz_rat_exp l lam).1 _ _ ?_
    have h𝔞0 : ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) : FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := Units.ne_zero _
    have htd : t ∈ FractionalIdeal.dual ℤ ℚ ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) := by
      rw [← _root_.GlobalTheory.IndefiniteRowSideFullHecke.OmegaFactorization.latM_eq_dual]; exact ht
    obtain ⟨k, hk0, hk⟩ := absNorm_mul_norm_mul_discr_eq_natCast_of_mem_dual _ h𝔞0 t ht0 htd
    rw [ht_def, ← map_natCast (algebraMap ℚ F), Algebra.norm_algebraMap] at hk
    have hD : discr F ≠ 0 := discr_ne_zero F
    have hv := neg_padicValRat_le_of_mul_eq_natCast hk0 hM hD hk
    have hA0 : FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F) ≠ 0 := by
      intro h0; rw [h0, zero_mul, zero_mul] at hk; exact hk0 (by exact_mod_cast hk.symm)
    have hD' : |(discr F : ℚ)| ≠ 0 := by simp [hD]
    rw [padicValRat.mul (pow_ne_zero _ hD') (pow_ne_zero _ hA0), padicValRat.pow, padicValRat.pow]
    have habs : padicValRat l |(discr F : ℚ)| = padicValInt l (discr F) := by
      rw [← Int.cast_abs, padicValRat.of_int]
      simp only [padicValInt, Int.natAbs_abs]
    rw [habs]
    have hv' : -(padicValRat l (FractionalIdeal.absNorm ((𝔞 : (FractionalIdeal (𝓞 F)⁰ F)ˣ) :
        FractionalIdeal (𝓞 F)⁰ F)) : ℝ) ≤ d * b + padicValInt l (discr F) := by
      exact_mod_cast hv
    push_cast
    nlinarith

  unfold _root_.GlobalTheory.HilbFam.hser
  rw [PowerSeries.coeff_smul, map_sum]
  simp only [PowerSeries.coeff_smul, smul_eq_mul, zsmul_eq_mul]
  have hsum : _root_.GlobalTheory.LatVal.Sz l lam (e + (∑ i, κ i : ℕ) * ρ)
      (∑ μ ∈ Finset.Iic κ, ((∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) *
        (-1) ^ μ i : ℤ) : ℂ) * PowerSeries.coeff n ((PowerSeries.mk c ^ ∑ i, (κ i - μ i)) *
          PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ))) := by
    refine _root_.GlobalTheory.QFam.SzSum.sz_sum _ fun μ hμ => ?_
    rw [Finset.mem_Iic] at hμ
    have hC := sz_coeff_pow (lam := lam) (φ := PowerSeries.mk c)
      (fun m => by rw [PowerSeries.coeff_mk]; exact hcρ m) (∑ i, (κ i - μ i))
    have hP := sz_coeff_mul hC (ψ := PowerSeries.mk (_root_.GlobalTheory.HilbFam.ecoef N a x μ))
      (fun m => by rw [PowerSeries.coeff_mk]; exact hT μ m) n
    have := _root_.GlobalTheory.QFam.SzSum.sz_mul (sz_intCast_of_nonneg (lam := lam) le_rfl
      (∏ i, _root_.GlobalTheory.HilbFam.rco (2 * s) (κ i) (μ i) * (-1) ^ μ i)) hP
    convert this using 1
    have hnat : ∑ i, (κ i - μ i) + ∑ i, μ i = ∑ i, κ i := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hμ i)
    rw [← hnat, ← Finset.sum_mul]
    push_cast
    ring
  have := _root_.GlobalTheory.QFam.SzSum.sz_mul hω hsum
  convert this using 1
  ring
