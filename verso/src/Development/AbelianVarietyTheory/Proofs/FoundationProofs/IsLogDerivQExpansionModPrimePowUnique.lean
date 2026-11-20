import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesNotZeroDivisorModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGaussStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponentsStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaDerivationHahnSeriesLeibnizAddConstStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.Glue.DlUniq

variable {Ω : Type} [Field Ω]

/- English proof (translation)
Introduce `r`. Establish `h : ∀ i, ∃ z ∈ A, D.coeff i = (l : Ω) ^ n * z` using `fun i => by`. Take `⟨z, hz, e⟩` from `hD i; exact ⟨z, hz, by simpa using e⟩`. Use `choose z hzA hz using h`. Use `⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support G.isPWO_support r, z ij.1 * G.coeff ij.2, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hzA _) (hG _))`. Rewrite using `[HahnSeries.coeff_mul, sub_zero, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun ij _ => ?_)` and prove the remaining obligations. Rewrite using `[hz, mul_assoc]`.
-/
theorem cg_mul (A : ValuationSubring Ω) (l n : ℕ) (D G : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hG : ∀ r, G.coeff r ∈ A) : ∀ r, CgA A l n ((D * G).coeff r) 0 := by
  intro r
  have h : ∀ i, ∃ z ∈ A, D.coeff i = (l : Ω) ^ n * z := fun i => by
    obtain ⟨z, hz, e⟩ := hD i; exact ⟨z, hz, by simpa using e⟩
  choose z hzA hz using h
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support G.isPWO_support r, z ij.1 * G.coeff ij.2, ?_, ?_⟩
  · exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hzA _) (hG _))
  · rw [HahnSeries.coeff_mul, sub_zero, Finset.mul_sum]
    refine Finset.sum_congr rfl (fun ij _ => ?_)
    rw [hz, mul_assoc]

/- English proof (translation)
Introduce `r`. Take `⟨z, hz, e⟩` from `hD r`. Take `⟨w, hw, e'⟩` from `hE r`. Use `⟨z - w, A.sub_mem hz hw, ?_⟩` and prove the remaining obligations. Rewrite using `[HahnSeries.coeff_sub, sub_zero, mul_sub, ← e, ← e', sub_zero, sub_zero]`.
-/
theorem cg_sub (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (hD : ∀ r, CgA A l n (D.coeff r) 0) (hE : ∀ r, CgA A l n (E.coeff r) 0) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := hD r
  obtain ⟨w, hw, e'⟩ := hE r
  refine ⟨z - w, A.sub_mem hz hw, ?_⟩
  rw [HahnSeries.coeff_sub, sub_zero, mul_sub, ← e, ← e', sub_zero, sub_zero]

/- English proof (translation)
Introduce `r`. Take `⟨z, hz, e⟩` from `h r`. Conclude with `⟨z, hz, by rw [HahnSeries.coeff_sub, sub_zero, e]⟩`.
-/
theorem cg_of (A : ValuationSubring Ω) (l n : ℕ) (D E : HahnSeries ℚ Ω)
    (h : ∀ r, CgA A l n (D.coeff r) (E.coeff r)) : ∀ r, CgA A l n ((D - E).coeff r) 0 := by
  intro r
  obtain ⟨z, hz, e⟩ := h r
  exact ⟨z, hz, by rw [HahnSeries.coeff_sub, sub_zero, e]⟩

/- English proof (translation)
Establish `e1 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k * (θ a * b2 + a * θ b2)`. Rewrite using `[mul_assoc, hL, hC, hL]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k2 * (θ a2 * b + a2 * θ b)`. Rewrite using `[h, mul_assoc, hL, hC, hL]`.

Expand and normalize the polynomial expressions, which then agree. Establish `h0 : HahnSeries.C k * ((θ a * b - a * θ b) * (a2 * b2) - (θ a2 * b2 - a2 * θ b2) * (a * b)) = 0`. Take the linear combination `(-(a2 * b)) * e1 + (a2 * b) * e2 - (θ a2 * b + a2 * θ b) * h`. Break down `mul_eq_zero.mp h0 with h1 | h1` into its components or cases. Conclude with `absurd h1 (HahnSeries.C_ne_zero hk)`.

Conclude with `sub_eq_zero.mp h1`.
-/
theorem key (θ : HahnSeries ℚ Ω → HahnSeries ℚ Ω)
    (hL : ∀ P Q, θ (P * Q) = θ P * Q + P * θ Q) (hC : ∀ c : Ω, θ (HahnSeries.C c) = 0)
    (k k2 : Ω) (hk : k ≠ 0) (a b a2 b2 : HahnSeries ℚ Ω)
    (h : HahnSeries.C k * a * b2 = HahnSeries.C k2 * a2 * b) :
    (θ a * b - a * θ b) * (a2 * b2) = (θ a2 * b2 - a2 * θ b2) * (a * b) := by
  have e1 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k * (θ a * b2 + a * θ b2) := by
    rw [mul_assoc, hL, hC, hL]; ring
  have e2 : θ (HahnSeries.C k * a * b2) = HahnSeries.C k2 * (θ a2 * b + a2 * θ b) := by
    rw [h, mul_assoc, hL, hC, hL]; ring
  have h0 : HahnSeries.C k * ((θ a * b - a * θ b) * (a2 * b2) - (θ a2 * b2 - a2 * θ b2) * (a * b)) = 0 := by
    linear_combination (-(a2 * b)) * e1 + (a2 * b) * e2 - (θ a2 * b + a2 * θ b) * h
  rcases mul_eq_zero.mp h0 with h1 | h1
  · exact absurd h1 (HahnSeries.C_ne_zero hk)
  · exact sub_eq_zero.mp h1

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue.DlUniq

/- English proof (translation)
Rewrite using `[CongruenceSubgroup.Gamma_mem]`. Establish `h` using `ModularGroup.coe_T_zpow (M : ℤ)`. Rewrite `h` using `[zpow_natCast]`. Simplify using `[h]`.
-/
theorem T_pow_mem_Gamma (M : ℕ) : (ModularGroup.T ^ M : SL(2, ℤ)) ∈ CongruenceSubgroup.Gamma M := by
  rw [CongruenceSubgroup.Gamma_mem]
  have h := ModularGroup.coe_T_zpow (M : ℤ)
  rw [zpow_natCast] at h
  simp [h]

/- English proof (translation)
Take `⟨M, hM, h⟩` from `X.level f`. Conclude with `⟨M, hM, h _ (T_pow_mem_Gamma M)⟩`.
-/
theorem mem_KT {Ω : Type} [Field Ω] [Algebra ℚ Ω] {ε : Ω →+* ℂ} (X : Tower Ω ε) (f : X.K) :
    ∃ M : ℕ, 0 < M ∧ f ∈ KT X M := by
  obtain ⟨M, hM, h⟩ := X.level f
  exact ⟨M, hM, h _ (T_pow_mem_Gamma M)⟩

end GlobalTheory.Glue.DlUniq

namespace GlobalTheory.Glue

open GlobalTheory.Glue.DlUniq in

/- English proof (translation)
Introduce `Ω _ _ _ ε X _ l _ A hl n s f φ φ' h1 h2`. Take `⟨hφA, a, b, κ, hκ, hab, hPa, hPb, hφ⟩` from `h1`. Take `⟨hφ'A, a2, b2, κ2, hκ2, hab2, hPa2, hPb2, hφ'⟩` from `h2`. Establish `hth` using `fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q)`. Establish `hK : algebraMap Ω X.K κ * a * b2 = algebraMap Ω X.K κ2 * a2 * b`.

Rewrite using `[← hab, ← hab2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hE : HahnSeries.C κ * X.exp a * X.exp b2 = HahnSeries.C κ2 * X.exp a2 * X.exp b`. Use `congrArg X.exp hK` as an intermediate fact. Simplify using `only [map_mul, AlgHom.commutes] at this`.

Establish `ec : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c` using `fun c => by`. Rewrite using `[HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]`. Simplify using `[HahnSeries.ofPowerSeries_C]`. Rewrite `this` using `[ec, ec]`. Then use the resulting hypothesis. Establish `hkey` using `key (theta s) (fun P Q => (hth P Q).1) (fun c => (hth 0 0).2.2 c) κ κ2 hκ _ _ _ _ hE`.

Use `set P := X.exp a * X.exp b * (X.exp a2 * X.exp b2) with hP`. Establish `hPab` using `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa hPb`. Establish `hPab2` using `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa2 hPb2`. Establish `hPP : Prim A P` using `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPab hPab2`. Take `⟨M, hM, hMK⟩` from `mem_KT X (a * b * (a2 * b2))`.

Establish `hsupp` using `(GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X M hM _).mp hMK`. Establish `hsuppP : ∀ r : ℚ, P.coeff r ≠ 0 → (r * M).den = 1`. Simplify `hsupp` using `[hP, map_mul]`. Establish `hD1` using `cg_mul A l n _ _ (cg_of A l n _ _ hφ) hPab2.1`. Establish `hD2` using `cg_mul A l n _ _ (cg_of A l n _ _ hφ') hPab.1`.

Establish `hdiff` using `cg_sub A l n _ _ hD1 hD2`. Establish `hid : (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a2 * X.exp b2) - (φ' * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) * (X.exp a * X.exp b) = (φ - φ') * P`. Rewrite using `[hP]`. Take the linear combination `(-1 : HahnSeries ℚ Ω) * hkey`. Rewrite `hdiff` using `[hid]`.

Establish `hint : ∀ r, (φ - φ').coeff r ∈ A` using `fun r => by`. Rewrite using `[HahnSeries.coeff_sub]`. Conclude with `sub_mem (hφA r) (hφ'A r)`. Establish `hfin` using `GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow l A hl n M P (φ - φ') hM hPP hsuppP hint hdiff`. Introduce `r`.

Take `⟨z, hz, e⟩` from `hfin r`. Conclude with `⟨z, hz, by rw [← e, HahnSeries.coeff_sub, sub_zero]⟩`.
-/
theorem isDl_unique : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n : ℕ) (s : ℚ) (f : X.K) (φ φ' : HahnSeries ℚ Ω), IsDl X A l n s f φ → IsDl X A l n s f φ' → ∀ r, CgA A l n (φ.coeff r) (φ'.coeff r) := by
  intro Ω _ _ _ ε X _ l _ A hl n s f φ φ' h1 h2
  obtain ⟨hφA, a, b, κ, hκ, hab, hPa, hPb, hφ⟩ := h1
  obtain ⟨hφ'A, a2, b2, κ2, hκ2, hab2, hPa2, hPb2, hφ'⟩ := h2
  have hth := fun P Q => (GlobalTheory.T.thetaDerivationHahnSeries_leibniz_add_const (Ω := Ω) s P Q)

  have hK : algebraMap Ω X.K κ * a * b2 = algebraMap Ω X.K κ2 * a2 * b := by
    rw [← hab, ← hab2]; ring
  have hE : HahnSeries.C κ * X.exp a * X.exp b2 = HahnSeries.C κ2 * X.exp a2 * X.exp b := by
    have := congrArg X.exp hK
    simp only [map_mul, AlgHom.commutes] at this
    have ec : ∀ c : Ω, algebraMap Ω (HahnSeries ℚ Ω) c = HahnSeries.C c := fun c => by
      rw [HahnSeries.algebraMap_apply', PowerSeries.algebraMap_apply]; simp [HahnSeries.ofPowerSeries_C]
    rwa [ec, ec] at this
  have hkey := key (theta s) (fun P Q => (hth P Q).1) (fun c => (hth 0 0).2.2 c) κ κ2 hκ _ _ _ _ hE

  set P := X.exp a * X.exp b * (X.exp a2 * X.exp b2) with hP
  have hPab := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa hPb
  have hPab2 := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPa2 hPb2
  have hPP : Prim A P := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ hPab hPab2
  obtain ⟨M, hM, hMK⟩ := mem_KT X (a * b * (a2 * b2))
  have hsupp := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X M hM _).mp hMK
  have hsuppP : ∀ r : ℚ, P.coeff r ≠ 0 → (r * M).den = 1 := by
    simpa [hP, map_mul] using hsupp
  have hD1 := cg_mul A l n _ _ (cg_of A l n _ _ hφ) hPab2.1
  have hD2 := cg_mul A l n _ _ (cg_of A l n _ _ hφ') hPab.1
  have hdiff := cg_sub A l n _ _ hD1 hD2
  have hid : (φ * X.exp a * X.exp b - (theta s (X.exp a) * X.exp b - X.exp a * theta s (X.exp b))) * (X.exp a2 * X.exp b2) -
      (φ' * X.exp a2 * X.exp b2 - (theta s (X.exp a2) * X.exp b2 - X.exp a2 * theta s (X.exp b2))) * (X.exp a * X.exp b)
      = (φ - φ') * P := by
    rw [hP]; linear_combination (-1 : HahnSeries ℚ Ω) * hkey
  rw [hid] at hdiff
  have hint : ∀ r, (φ - φ').coeff r ∈ A := fun r => by
    rw [HahnSeries.coeff_sub]; exact sub_mem (hφA r) (hφ'A r)
  have hfin := GlobalTheory.T.primitiveHahnSeries_not_zeroDivisor_modPrimePow l A hl n M P (φ - φ') hM hPP hsuppP hint hdiff
  intro r
  obtain ⟨z, hz, e⟩ := hfin r
  exact ⟨z, hz, by rw [← e, HahnSeries.coeff_sub, sub_zero]⟩

end GlobalTheory.Glue
