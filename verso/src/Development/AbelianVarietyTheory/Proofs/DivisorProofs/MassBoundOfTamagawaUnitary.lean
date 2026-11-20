import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.InstMeasurableSpaceRealSU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CovolumeRealSpecialUnitaryEqFlagDomainMassStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ZetaTermTsumLeTwo
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DetEqOneUnitaryPrincipalCongruenceLevelThreeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryDetIsTAStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EquivalenceGeneratedTorusRelStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryFramesStrongApproximationStatement

open NumberField IsDedekindDomain MeasureTheory Matrix GlobalTheory.AdLat GlobalTheory.UCls GlobalTheory.SUVol ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up
open scoped ENNReal

namespace GlobalTheory.UCls

/- English proof (translation)
Introduce `hT E _ _ _ r M h m G Λ Ψ X g x0 FF hr hM hU hSD htor hUA hdist hX`. Use `set Cc : ℝ := ((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E with hCc`. Use `set P0 : ℝ := (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hP0`. Use `set R : ℝ := rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) with hR`. Use `set K : ℝ := (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R * P0 with hK`.

Establish `hCpos : 0 < Cc` using `pow_pos (mul_pos (mul_pos (by positivity) (by positivity)) (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r)))) _`. Establish `hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i` using `Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity`. Establish `hP0nn : 0 ≤ P0` using `pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hprod) _`. Establish `hRnn : 0 ≤ R` using `Real.rpow_nonneg (by unfold rdE; exact Real.rpow_nonneg (by unfold dE; positivity) _) _`. Establish `hP0le : P0 ≤ Cc` using `pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hprod) (GlobalTheory.volumeConstant_le r hr) _`.

Establish `hKnn : 0 ≤ K` using `by positivity`. Establish `hdet : ∀ i, ∀ γ ∈ (X i).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1` using `fun i => GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three E r M (X i) hM (by rw [(hX i).1]; exact (hX i).2.2.2.1)`. Set `cv : Fin m → ℝ≥0∞` to `fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm) (riemHaar (X i).Ψ (X i).Gm (x0 i))`. Establish `hV1 : ∀ i, ENNReal.ofReal Cc * muF (X i) (x0 i) (FF i) = cv i` using `fun i => GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass E r (X i) (x0 i) (FF i) (by omega) (hdet i) (hX i).2.2.2.2.1 (hX i).2.2.2.2.2`. Establish `hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det` using `fun i => GlobalTheory.T.isTA_conj_det_of_isUA_cm E r G (g i) hSD.2.1 (hUA i)`.

Set `f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1` to `fun i => Quot.mk _ ⟨(g i).det, hTA i⟩`. Establish `hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)`. Assume the negation of the conclusion as `hinf`. Rewrite `hinf` using `[not_finite_iff_infinite]`. Establish `h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M = ⊤` using `ENat.card_eq_top_of_infinite`.

Rewrite `htor` using `[h1]`. Conclude with `absurd htor (by simp)`. Establish `hcard : (Finset.univ.image f).card ≤ h`. Establish `h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)` using `by haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)`. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `Finset.card_le_univ _`. Establish `h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} => TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) : ℕ) : ℕ∞) ≤ h`. Rewrite using `[← ENat.card_eq_coe_natCard]`. Conclude with `htor`. Conclude with `h1.trans (by exact_mod_cast h2)`.

Establish `hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K`. Introduce `q hq`. Take `⟨i0, -, hi0⟩` from `Finset.mem_image.1 hq`. Use `GlobalTheory.T.unitary_frames_strong_approximation hT E r M m G Λ Ψ X g x0 _ (g i0) hr hM hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j) (fun i _ => ⟨(hX i).1, (hX i).2.1, (hX i).2.2.1, (hX i).2.2.2.1, (hX i).2.2.2.2.1⟩)` and prove the remaining obligations. Introduce `i hi`.

Establish `hfi : f i0 = f i` using `by rw [hi0, (Finset.mem_filter.1 hi).2]`. Conclude with `GlobalTheory.T.equivalence_generated_torus_rel E r M G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)`. Establish `hsum : ∑ i, cv i ≤ ENNReal.ofReal (h * K)`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f) (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]`. Combine the equalities or inequalities in the displayed calculation.

Establish `hmu : ∀ i, muF (X i) (x0 i) (FF i) = cv i / ENNReal.ofReal Cc`. Introduce `i`. Rewrite using `[ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hCpos).ne' ENNReal.ofReal_ne_top]`. Conclude with `hV1 i`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [hmu, div_eq_mul_inv, Finset.sum_mul]`. Use `_ ≤ ENNReal.ofReal (h * K) * (ENNReal.ofReal Cc)⁻¹ := by gcongr`. Use `_ = ENNReal.ofReal (h * K / Cc) := by rw [ENNReal.ofReal_div_of_pos hCpos, div_eq_mul_inv]`. Use `_ ≤ ENNReal.ofReal (massBd E r M h) := by`. Apply `ENNReal.ofReal_le_ofReal` to reduce the goal to its premises.

Establish `hA : 0 ≤ (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R` using `by positivity`. Establish `hq : P0 / Cc ≤ 1` using `(div_le_one hCpos).2 hP0le`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hK]`. Expand and normalize the polynomial expressions, which then agree.

Use `_ ≤ ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * 1 := mul_le_mul_of_nonneg_left hq hA`. Use `_ ≤ 2 * (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by nlinarith`. Use `_ = massBd E r M h := rfl`.
-/
theorem massBound_of_tamagawa : GlobalTheory.Published.TamagawaSpecialUnitary → GlobalTheory.UCls.MassBound := by
  intro hT E _ _ _ r M h m G Λ Ψ X g x0 FF hr hM hU hSD htor hUA hdist hX
  classical
  set Cc : ℝ := ((2 : ℝ) ^ (r * (r - 1) / 2) * (2 * Real.pi) ^ (r - 1) * Real.sqrt r) ^ fdeg E with hCc
  set P0 : ℝ := (Real.sqrt r * ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i) ^ fdeg E with hP0
  set R : ℝ := rdE E ^ ((fdeg E : ℝ) * ((r : ℝ) ^ 2 - 1) / 2) with hR
  set K : ℝ := (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R * P0 with hK
  have hCpos : 0 < Cc := pow_pos (mul_pos (mul_pos (by positivity) (by positivity))
    (Real.sqrt_pos.2 (by exact_mod_cast (by omega : 0 < r)))) _
  have hprod : 0 ≤ ∏ i ∈ Finset.Icc 2 r, ∑' n : ℕ, 1 / ((n : ℝ) + 1) ^ i :=
    Finset.prod_nonneg fun i _ => tsum_nonneg fun n => by positivity
  have hP0nn : 0 ≤ P0 := pow_nonneg (mul_nonneg (Real.sqrt_nonneg _) hprod) _
  have hRnn : 0 ≤ R := Real.rpow_nonneg (by unfold rdE; exact Real.rpow_nonneg (by unfold dE; positivity) _) _
  have hP0le : P0 ≤ Cc := pow_le_pow_left₀ (mul_nonneg (Real.sqrt_nonneg _) hprod) (GlobalTheory.volumeConstant_le r hr) _
  have hKnn : 0 ≤ K := by positivity
  have hdet : ∀ i, ∀ γ ∈ (X i).Γ, (γ : Matrix (Fin r) (Fin r) E).det = 1 := fun i =>
    GlobalTheory.T.det_eq_one_unitary_principal_congruence_level_three E r M (X i) hM (by rw [(hX i).1]; exact (hX i).2.2.2.1)
  let cv : Fin m → ℝ≥0∞ := fun i => covolume (inReal (X i).Ψ (X i).Gm (X i).Γ) (realSU (X i).Ψ (X i).Gm)
    (riemHaar (X i).Ψ (X i).Gm (x0 i))
  have hV1 : ∀ i, ENNReal.ofReal Cc * muF (X i) (x0 i) (FF i) = cv i := fun i =>
    GlobalTheory.T.covolume_realSpecialUnitary_eq_flagDomain_mass E r (X i) (x0 i) (FF i) (by omega) (hdet i) (hX i).2.2.2.2.1 (hX i).2.2.2.2.2
  have hTA : ∀ i, IsTA (IsCMField.complexConj E) (g i).det := fun i => GlobalTheory.T.isTA_conj_det_of_isUA_cm E r G (g i) hSD.2.1 (hUA i)
  let f : Fin m → Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1 := fun i => Quot.mk _ ⟨(g i).det, hTA i⟩
  have hQfin : Finite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
      TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
    by_contra hinf
    rw [not_finite_iff_infinite] at hinf
    have h1 : torusNo (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M = ⊤ := ENat.card_eq_top_of_infinite
    rw [h1] at htor
    exact absurd htor (by simp)
  have hcard : (Finset.univ.image f).card ≤ h := by
    have h1 : (Finset.univ.image f).card ≤ Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) := by
      haveI := Fintype.ofFinite (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1)
      rw [Nat.card_eq_fintype_card]; exact Finset.card_le_univ _
    have h2 : ((Nat.card (Quot fun a b : {t : RA (maximalRealSubfield E) E // IsTA (IsCMField.complexConj E) t} =>
        TEquiv (IsCMField.complexConj E) G (Λ : Set (Fin r → E)) M a.1 b.1) : ℕ) : ℕ∞) ≤ h := by
      rw [← ENat.card_eq_coe_natCard]; exact htor
    exact h1.trans (by exact_mod_cast h2)
  have hfib : ∀ q ∈ Finset.univ.image f, ∑ i ∈ Finset.univ.filter (fun i => f i = q), cv i ≤ ENNReal.ofReal K := by
    intro q hq
    obtain ⟨i0, -, hi0⟩ := Finset.mem_image.1 hq
    refine GlobalTheory.T.unitary_frames_strong_approximation hT E r M m G Λ Ψ X g x0 _ (g i0) hr hM hU hSD (hUA i0) hUA ?_ (fun i _ j _ => hdist i j)
      (fun i _ => ⟨(hX i).1, (hX i).2.1, (hX i).2.2.1, (hX i).2.2.2.1, (hX i).2.2.2.2.1⟩)
    intro i hi
    have hfi : f i0 = f i := by rw [hi0, (Finset.mem_filter.1 hi).2]
    exact GlobalTheory.T.equivalence_generated_torus_rel E r M G (Λ : Set (Fin r → E)) ⟨(g i0).det, hTA i0⟩ ⟨(g i).det, hTA i⟩ (Quot.eqvGen_exact hfi)
  have hsum : ∑ i, cv i ≤ ENNReal.ofReal (h * K) := by
    rw [← Finset.sum_fiberwise_of_maps_to (s := Finset.univ) (t := Finset.univ.image f) (g := f)
      (fun i _ => Finset.mem_image_of_mem f (Finset.mem_univ i))]
    calc _ ≤ ∑ q ∈ Finset.univ.image f, ENNReal.ofReal K := Finset.sum_le_sum hfib
      _ = ((Finset.univ.image f).card : ℝ≥0∞) * ENNReal.ofReal K := by rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ (h : ℝ≥0∞) * ENNReal.ofReal K := by gcongr
      _ = ENNReal.ofReal (h * K) := by rw [ENNReal.ofReal_mul (p := (h : ℝ)) (by positivity), ENNReal.ofReal_natCast]
  have hmu : ∀ i, muF (X i) (x0 i) (FF i) = cv i / ENNReal.ofReal Cc := by
    intro i
    rw [ENNReal.eq_div_iff (ENNReal.ofReal_pos.2 hCpos).ne' ENNReal.ofReal_ne_top]
    exact hV1 i
  calc ∑ i, muF (X i) (x0 i) (FF i) = (∑ i, cv i) * (ENNReal.ofReal Cc)⁻¹ := by
        simp only [hmu, div_eq_mul_inv, Finset.sum_mul]
    _ ≤ ENNReal.ofReal (h * K) * (ENNReal.ofReal Cc)⁻¹ := by gcongr
    _ = ENNReal.ofReal (h * K / Cc) := by rw [ENNReal.ofReal_div_of_pos hCpos, div_eq_mul_inv]
    _ ≤ ENNReal.ofReal (massBd E r M h) := by
        apply ENNReal.ofReal_le_ofReal
        have hA : 0 ≤ (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by positivity
        have hq : P0 / Cc ≤ 1 := (div_le_one hCpos).2 hP0le
        calc (h : ℝ) * K / Cc = ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * (P0 / Cc) := by
              rw [hK]; ring
          _ ≤ ((h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R) * 1 := mul_le_mul_of_nonneg_left hq hA
          _ ≤ 2 * (h : ℝ) * (M : ℝ) ^ (2 * fdeg E * r ^ 2) * R := by nlinarith
          _ = massBd E r M h := rfl

end GlobalTheory.UCls
