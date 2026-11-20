import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ApplyEqOfMemAdjoin
import Development.AbelianVarietyTheory.Definitions.Foundations.IsTopWTopWOfExists
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsPrimitiveExpansionQuotientLevelOneStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.PrimitiveHahnSeriesInvertibleModPrimePowStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MulOfIsPrimitiveIntegralHahnGaussStatement
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemTranslationInvariantSubfieldIffExponentsStatement
open scoped MatrixGroups
open GlobalTheory.KZ GlobalTheory.Glue GlobalTheory.K5 GlobalTheory.KummerEisensteinGalois

namespace GlobalTheory.DlEx

variable {Ω : Type} [Field Ω]

def Sp (L : ℕ) (x : HahnSeries ℚ Ω) : Prop := ∀ r : ℚ, x.coeff r ≠ 0 → (r * L).den = 1

/- English proof (translation)
Rewrite `ha`, `hb` using `[Rat.den_eq_one_iff]`. Rewrite using `[← ha, ← hb, ← Int.cast_add]`. Simplify using the standard rewrite rules.
-/
lemma den_add {a b : ℚ} (ha : a.den = 1) (hb : b.den = 1) : (a + b).den = 1 := by
  rw [Rat.den_eq_one_iff] at ha hb
  rw [← ha, ← hb, ← Int.cast_add]; simp

/- English proof (translation)
Rewrite `h` using `[HahnSeries.coeff_mul]`. Take `⟨ij, hij, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Rewrite `hij` using `[Finset.mem_antidiagonal]`. Conclude with `⟨ij.1, ij.2, hij.2.2, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩`.
-/
lemma exists_of_coeff_mul_ne {x y : HahnSeries ℚ Ω} {r : ℚ} (h : (x * y).coeff r ≠ 0) :
    ∃ r₁ r₂, r₁ + r₂ = r ∧ x.coeff r₁ ≠ 0 ∧ y.coeff r₂ ≠ 0 := by
  rw [HahnSeries.coeff_mul] at h
  obtain ⟨ij, hij, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [Finset.mem_antidiagonal] at hij
  exact ⟨ij.1, ij.2, hij.2.2, left_ne_zero_of_mul hne, right_ne_zero_of_mul hne⟩

/- English proof (translation)
Introduce `r hr`. Take `⟨r₁, r₂, rfl, h1, h2⟩` from `exists_of_coeff_mul_ne hr`. Rewrite using `[add_mul]`. Conclude with `den_add (hx _ h1) (hy _ h2)`.
-/
lemma sp_mul {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x * y) := by
  intro r hr
  obtain ⟨r₁, r₂, rfl, h1, h2⟩ := exists_of_coeff_mul_ne hr
  rw [add_mul]; exact den_add (hx _ h1) (hy _ h2)

/- English proof (translation)
Introduce `r hr`. Rewrite `hr` using `[HahnSeries.coeff_sub]`. Distinguish the cases in `h : x.coeff r = 0`. Conclude with `hy r (by intro h'; apply hr; rw [h, h', sub_zero])`. Conclude with `hx r h`.
-/
lemma sp_sub {L : ℕ} {x y : HahnSeries ℚ Ω} (hx : Sp L x) (hy : Sp L y) : Sp L (x - y) := by
  intro r hr
  rw [HahnSeries.coeff_sub] at hr
  by_cases h : x.coeff r = 0
  · exact hy r (by intro h'; apply hr; rw [h, h', sub_zero])
  · exact hx r h

variable [Algebra ℚ Ω]

/- English proof (translation)
Introduce `r hr`. Conclude with `hx r (fun h => hr (by simp [theta, h]))`.
-/
lemma sp_theta {L : ℕ} (s : ℚ) {x : HahnSeries ℚ Ω} (hx : Sp L x) : Sp L (theta s x) := by
  intro r hr
  exact hx r (fun h => hr (by simp [theta, h]))

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_mul]`. Conclude with `Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hx _) (hy _))`.
-/
lemma intA_mul (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x * y).coeff r ∈ A := by
  rw [HahnSeries.coeff_mul]
  exact Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hx _) (hy _))

/- English proof (translation)
Rewrite using `[HahnSeries.coeff_sub]`. Conclude with `sub_mem (hx r) (hy r)`.
-/
lemma intA_sub (A : ValuationSubring Ω) {x y : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hy : ∀ r, y.coeff r ∈ A) (r : ℚ) : (x - y).coeff r ∈ A := by
  rw [HahnSeries.coeff_sub]; exact sub_mem (hx r) (hy r)

/- English proof (translation)
Use `show algebraMap ℚ Ω ((L : ℚ) * r) * x.coeff r ∈ A`. Distinguish the cases in `h : x.coeff r = 0`. Rewrite using `[h, mul_zero]`. Conclude with `zero_mem A`. Establish `hd` using `hs r h`.

Rewrite `hd` using `[Rat.den_eq_one_iff]`. Rewrite using `[mul_comm (L : ℚ) r, ← hd, map_intCast]`. Conclude with `mul_mem (intCast_mem A _) (hx r)`.
-/
lemma intA_theta (A : ValuationSubring Ω) {L : ℕ} {x : HahnSeries ℚ Ω} (hx : ∀ r, x.coeff r ∈ A)
    (hs : Sp L x) (r : ℚ) : (theta (L : ℚ) x).coeff r ∈ A := by
  show algebraMap ℚ Ω ((L : ℚ) * r) * x.coeff r ∈ A
  by_cases h : x.coeff r = 0
  · rw [h, mul_zero]; exact zero_mem A
  · have hd := hs r h
    rw [Rat.den_eq_one_iff] at hd
    rw [mul_comm (L : ℚ) r, ← hd, map_intCast]
    exact mul_mem (intCast_mem A _) (hx r)

end GlobalTheory.DlEx

open GlobalTheory.DlEx in

/- English proof (translation)
Introduce `Ω _ _ _ ε X hj l _ A hl n L f hL hf hfK`. Take `⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, -⟩` from `GlobalTheory.T.exists_primitive_expansion_quotient_level_one ε X hj l A hl f hf`. Establish `hbK : b ∈ KT X L` using `(RingHom.mem_eqLocusField).2 (hbinv _)`. Establish `hcK : algebraMap Ω X.K κ ∈ KT X L` using `(RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)`. Establish `haK : a ∈ KT X L`.

Establish `e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b)`. Rewrite using `[hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]`. Rewrite using `[e]`. Conclude with `(KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)`. Establish `hsa : Sp L (X.exp a)` using `(GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL a).1 haK`.

Establish `hsb : Sp L (X.exp b)` using `(GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL b).1 hbK`. Establish `hP : Prim A (X.exp a * X.exp b)` using `GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ ha hb`. Take `⟨Q, hQA, hQs, hQP⟩` from `GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)`. Establish `hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A` using `intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))`. Establish `hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b))` using `sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))`.

Use `⟨Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)), ⟨intA_mul A hQA hDA, a, b, κ, hκ, hfb, ha, hb, ?_⟩, sp_mul hQs hDs⟩` and prove the remaining obligations. Introduce `r`. Generalize the expression as in `theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢`. Use `choose z hzA hz using hQP`. Establish `e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r`.

Rewrite using `[show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one, HahnSeries.coeff_sub]`. Use `⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r, D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩` and prove the remaining obligations. Rewrite using `[e, HahnSeries.coeff_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun ij _ => ?_)` and prove the remaining obligations. Rewrite using `[HahnSeries.coeff_sub, hz ij.2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.dl_exists : ∀ {Ω : Type} [Field Ω] [Algebra ℚ Ω] [IsAlgClosure ℚ Ω] (ε : Ω →+* ℂ) (X : GlobalTheory.KZ.Tower Ω ε), (∃ φ : ℂ → ℂ, DifferentiableOn ℂ φ Hs ∧ X.an X.jK = (φ : Mero)) →
  ∀ (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), ((l : ℕ) : Ω) ∈ A.nonunits → ∀ (n L : ℕ) (f : X.K), 0 < L → f ≠ 0 → f ∈ KT X L → ∃ φ : HahnSeries ℚ Ω, IsDl X A l n L f φ ∧ ∀ r : ℚ, φ.coeff r ≠ 0 → (r * L).den = 1 := by
  intro Ω _ _ _ ε X hj l _ A hl n L f hL hf hfK
  obtain ⟨a, b, κ, S, hκ, hfb, ha, hb, hbinv, -⟩ := GlobalTheory.T.exists_primitive_expansion_quotient_level_one ε X hj l A hl f hf
  have hbK : b ∈ KT X L := (RingHom.mem_eqLocusField).2 (hbinv _)
  have hcK : algebraMap Ω X.K κ ∈ KT X L := (RingHom.mem_eqLocusField).2 ((X.sl _).commutes κ)
  have haK : a ∈ KT X L := by
    have e : a = (algebraMap Ω X.K κ)⁻¹ * (f * b) := by
      rw [hfb, ← mul_assoc, inv_mul_cancel₀ ((map_ne_zero _).2 hκ), one_mul]
    rw [e]; exact (KT X L).mul_mem ((KT X L).inv_mem hcK) ((KT X L).mul_mem hfK hbK)
  have hsa : Sp L (X.exp a) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL a).1 haK
  have hsb : Sp L (X.exp b) := (GlobalTheory.T.mem_translationInvariantSubfield_iff_exponents ε X L hL b).1 hbK
  have hP : Prim A (X.exp a * X.exp b) := GlobalTheory.T.mul_of_isPrimitiveIntegral_hahn_gauss A _ _ ha hb
  obtain ⟨Q, hQA, hQs, hQP⟩ := GlobalTheory.T.primitive_hahnSeries_invertible_mod_prime_pow l A hl n L (X.exp a * X.exp b) hL hP (sp_mul hsa hsb)
  have hDA : ∀ r, (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)).coeff r ∈ A :=
    intA_sub A (intA_mul A (intA_theta A ha.1 hsa) hb.1) (intA_mul A ha.1 (intA_theta A hb.1 hsb))
  have hDs : Sp L (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)) :=
    sp_sub (sp_mul (sp_theta _ hsa) hsb) (sp_mul hsa (sp_theta _ hsb))
  refine ⟨Q * (theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b)),
    ⟨intA_mul A hQA hDA, a, b, κ, hκ, hfb, ha, hb, ?_⟩, sp_mul hQs hDs⟩
  intro r
  generalize theta (L:ℚ) (X.exp a) * X.exp b - X.exp a * theta (L:ℚ) (X.exp b) = D at hDA ⊢
  choose z hzA hz using hQP
  have e : (Q * D * X.exp a * X.exp b).coeff r - D.coeff r = (D * (Q * (X.exp a * X.exp b) - 1)).coeff r := by
    rw [show Q * D * X.exp a * X.exp b = D * (Q * (X.exp a * X.exp b)) by ring, mul_sub, mul_one,
      HahnSeries.coeff_sub]
  refine ⟨∑ ij ∈ Finset.addAntidiagonal D.isPWO_support (Q * (X.exp a * X.exp b) - 1).isPWO_support r,
    D.coeff ij.1 * z ij.2, Subring.sum_mem A.toSubring (fun ij _ => mul_mem (hDA _) (hzA _)), ?_⟩
  rw [e, HahnSeries.coeff_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl (fun ij _ => ?_)
  rw [HahnSeries.coeff_sub, hz ij.2]; ring
