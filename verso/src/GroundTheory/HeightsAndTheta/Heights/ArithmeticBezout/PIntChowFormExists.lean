import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.LinFormOneZero
import GroundTheory.HeightsAndTheta.Heights.ArithmeticBezout.StatementsGenericFibreDim
import GroundTheory.HeightsAndTheta.Heights.ChowForms.Assembly
import GroundTheory.HeightsAndTheta.Heights.ChowForms.PAffineChartTrdeg
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights

namespace ObjectsChow

open MvPolynomial
open ReciprocityTheory.ChartRestriction.G.Geo (MRing PBlk IsArithVar)

/- English proof (translation)
The claim follows from `ChowFormExists.of_affineChartTrdeg AffineChartTrdeg.proof`.
-/
theorem chowFormExists : ChowFormExists.Statement :=
  ChowFormExists.of_affineChartTrdeg AffineChartTrdeg.proof

/- English proof (translation)
Use `⟨∑ m ∈ p.support, monomial m (F (coeff m p)), fun m' => ?_⟩` and prove the remaining obligations. Rewrite using `[coeff_sum]`. Simplify using `only [coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`. Use `split_ifs with h`.

Both sides reduce to the same expression. Rewrite using `[notMem_support_iff.mp h, hF]`.
-/
theorem exists_coeff_eq_apply {σ R S : Type*} [CommSemiring R] [CommSemiring S] (F : R → S) (hF : F 0 = 0)
    (p : MvPolynomial σ R) : ∃ q : MvPolynomial σ S, ∀ m, coeff m q = F (coeff m p) := by
  classical
  refine ⟨∑ m ∈ p.support, monomial m (F (coeff m p)), fun m' => ?_⟩
  rw [coeff_sum]
  simp only [coeff_monomial]
  rw [Finset.sum_ite_eq']
  split_ifs with h
  · rfl
  · rw [notMem_support_iff.mp h, hF]

/- English proof (translation)
Take `⟨d, hd⟩ : ∃ d : ℕ, d = ∏ m ∈ g.support, (g.coeff m).den` from `⟨_, rfl⟩`. Establish `hden : ∀ m, (g.coeff m).den ∣ d`. Introduce `m`. Distinguish the cases in `hm : m ∈ g.support`. Rewrite using `[hd]`.

Conclude with `Finset.dvd_prod_of_mem _ hm`. Rewrite using `[notMem_support_iff.mp hm]`. Simplify using the standard rewrite rules. Establish `hd0 : (d : ℚ) ≠ 0`. Rewrite using `[hd, Nat.cast_ne_zero]`.

Conclude with `Finset.prod_ne_zero_iff.mpr fun m _ => (g.coeff m).den_ne_zero`. Set `F : ℚ → ℤ` to `fun q => ((d / q.den : ℕ) : ℤ) * q.num`. Establish `hF0 : F 0 = 0` using `by simp [F]`. Take `⟨f₀, hf₀⟩ : ∃ f₀ : MvPolynomial σ ℤ, ∀ m, coeff m f₀ = F (g.coeff m)` from `exists_coeff_eq_apply F hF0 g`. Establish `hmap₀ : map (Int.castRingHom ℚ) f₀ = C (d : ℚ) * g`.

Use extensionality with `m`. Rewrite using `[coeff_map, hf₀, coeff_C_mul]`. Take `⟨k, hk⟩` from `hden m`. Simplify using `only [F, eq_intCast, Int.cast_mul, Int.cast_natCast]`. Rewrite using `[hk, Nat.mul_div_cancel_left _ (g.coeff m).den_pos, ← Rat.mul_den_eq_num (g.coeff m)]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hf₀ne : f₀ ≠ 0`. Introduce `h0`. Rewrite `hmap₀` using `[h0, map_zero]`.

Conclude with `mul_ne_zero (C_ne_zero.mpr hd0) hg hmap₀.symm`. Take `⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, c₀ = f₀.support.gcd (fun m => coeff m f₀)` from `⟨_, rfl⟩`. Establish `hc0 : c₀ ≠ 0`. Introduce `h0`. Rewrite `hc₀` using `[h0, eq_comm, Finset.gcd_eq_zero_iff]`.

Apply `hf₀ne` to reduce the goal to its premises. Use extensionality with `m`. Distinguish the cases in `hm : m ∈ f₀.support`. Simplify using `using hc₀ m hm`. Simplify using `using notMem_support_iff.mp hm`.

Establish `hdvd : ∀ m, c₀ ∣ coeff m f₀`. Introduce `m`. Distinguish the cases in `hm : m ∈ f₀.support`. Rewrite using `[hc₀]`. Conclude with `Finset.gcd_dvd hm`.

Rewrite using `[notMem_support_iff.mp hm]`. Conclude with `dvd_zero _`. Take `⟨f, hf⟩ : ∃ f : MvPolynomial σ ℤ, ∀ m, coeff m f = coeff m f₀ / c₀` from `exists_coeff_eq_apply (fun a => a / c₀) (by simp) f₀`. Establish `hf₀eq : f₀ = C c₀ * f`. Use extensionality with `m`.

Rewrite using `[coeff_C_mul, hf, Int.mul_ediv_cancel' (hdvd m)]`. Establish `hc0' : (c₀ : ℚ) ≠ 0` using `by exact_mod_cast hc0`. Use `⟨(d : ℚ) / c₀, div_ne_zero hd0 hc0', f, fun c hc => ?_, ?_⟩` and prove the remaining obligations. Establish `h1 : c * c₀ ∣ 1 * c₀`. Rewrite using `[one_mul]`.

Use `conv_rhs => rw [hc₀]`. Use `Finset.dvd_gcd fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hf₀eq, coeff_C_mul, mul_comm c₀]`. Conclude with `mul_dvd_mul_right (hc m) c₀`. Conclude with `isUnit_of_dvd_one ((mul_dvd_mul_iff_right hc0).mp h1)`.

Establish `h2 : C (c₀ : ℚ) * map (Int.castRingHom ℚ) f = C (d : ℚ) * g`. Rewrite using `[← hmap₀, hf₀eq, map_mul, map_C, eq_intCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0', C_1, one_mul]`. Use `_ = C ((d : ℚ) / c₀) * g := by`.

Rewrite using `[h2, ← mul_assoc, ← C_mul, div_eq_inv_mul]`.
-/
theorem exists_isPrimitive_map_eq_C_mul {σ : Type*} (g : MvPolynomial σ ℚ) (hg : g ≠ 0) :
    ∃ a : ℚ, a ≠ 0 ∧ ∃ f : MvPolynomial σ ℤ, IndefiniteRowSideFullHecke.ArithBezout.IsPrimitive f ∧
      map (Int.castRingHom ℚ) f = C a * g := by
  classical

  obtain ⟨d, hd⟩ : ∃ d : ℕ, d = ∏ m ∈ g.support, (g.coeff m).den := ⟨_, rfl⟩
  have hden : ∀ m, (g.coeff m).den ∣ d := by
    intro m
    by_cases hm : m ∈ g.support
    · rw [hd]; exact Finset.dvd_prod_of_mem _ hm
    · rw [notMem_support_iff.mp hm]; simp
  have hd0 : (d : ℚ) ≠ 0 := by
    rw [hd, Nat.cast_ne_zero]
    exact Finset.prod_ne_zero_iff.mpr fun m _ => (g.coeff m).den_ne_zero

  let F : ℚ → ℤ := fun q => ((d / q.den : ℕ) : ℤ) * q.num
  have hF0 : F 0 = 0 := by simp [F]
  obtain ⟨f₀, hf₀⟩ : ∃ f₀ : MvPolynomial σ ℤ, ∀ m, coeff m f₀ = F (g.coeff m) :=
    exists_coeff_eq_apply F hF0 g
  have hmap₀ : map (Int.castRingHom ℚ) f₀ = C (d : ℚ) * g := by
    ext m
    rw [coeff_map, hf₀, coeff_C_mul]
    obtain ⟨k, hk⟩ := hden m
    simp only [F, eq_intCast, Int.cast_mul, Int.cast_natCast]
    rw [hk, Nat.mul_div_cancel_left _ (g.coeff m).den_pos, ← Rat.mul_den_eq_num (g.coeff m)]
    push_cast
    ring
  have hf₀ne : f₀ ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hmap₀
    exact mul_ne_zero (C_ne_zero.mpr hd0) hg hmap₀.symm

  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℤ, c₀ = f₀.support.gcd (fun m => coeff m f₀) := ⟨_, rfl⟩
  have hc0 : c₀ ≠ 0 := by
    intro h0
    rw [h0, eq_comm, Finset.gcd_eq_zero_iff] at hc₀
    apply hf₀ne
    ext m
    by_cases hm : m ∈ f₀.support
    · simpa using hc₀ m hm
    · simpa using notMem_support_iff.mp hm
  have hdvd : ∀ m, c₀ ∣ coeff m f₀ := by
    intro m
    by_cases hm : m ∈ f₀.support
    · rw [hc₀]; exact Finset.gcd_dvd hm
    · rw [notMem_support_iff.mp hm]; exact dvd_zero _
  obtain ⟨f, hf⟩ : ∃ f : MvPolynomial σ ℤ, ∀ m, coeff m f = coeff m f₀ / c₀ :=
    exists_coeff_eq_apply (fun a => a / c₀) (by simp) f₀
  have hf₀eq : f₀ = C c₀ * f := by
    ext m
    rw [coeff_C_mul, hf, Int.mul_ediv_cancel' (hdvd m)]
  have hc0' : (c₀ : ℚ) ≠ 0 := by exact_mod_cast hc0
  refine ⟨(d : ℚ) / c₀, div_ne_zero hd0 hc0', f, fun c hc => ?_, ?_⟩
  ·
    have h1 : c * c₀ ∣ 1 * c₀ := by
      rw [one_mul]
      conv_rhs => rw [hc₀]
      refine Finset.dvd_gcd fun m _ => ?_
      rw [hf₀eq, coeff_C_mul, mul_comm c₀]
      exact mul_dvd_mul_right (hc m) c₀
    exact isUnit_of_dvd_one ((mul_dvd_mul_iff_right hc0).mp h1)
  · have h2 : C (c₀ : ℚ) * map (Int.castRingHom ℚ) f = C (d : ℚ) * g := by
      rw [← hmap₀, hf₀eq, map_mul, map_C, eq_intCast]
    calc map (Int.castRingHom ℚ) f = C ((c₀ : ℚ)⁻¹) * (C (c₀ : ℚ) * map (Int.castRingHom ℚ) f) := by
          rw [← mul_assoc, ← C_mul, inv_mul_cancel₀ hc0', C_1, one_mul]
      _ = C ((d : ℚ) / c₀) * g := by
          rw [h2, ← mul_assoc, ← C_mul, div_eq_inv_mul]

/- English proof (translation)
Introduce `n e P hP`. Establish `hQ` using `(hG n (e + 1) P hP).1`. Take `⟨g, hg⟩` from `chowFormExists ℚ n (e + 1) (genericIdeal P) hQ (hD n (e + 1) P hP)`. Take `⟨δ, -, hδ⟩` from `ChowFormMultiHomog.full ℚ n (e + 1) (genericIdeal P) g hQ hg`. Take `⟨a, ha, f, hprim, hmap⟩` from `exists_isPrimitive_map_eq_C_mul g hg.1`.

Establish `hC : IsChowForm (genericIdeal P) (e + 1) (map (Int.castRingHom ℚ) f)`. Rewrite using `[hmap]`. Conclude with `isChowForm_C_mul hg ha`. Establish `hH : IsMultiHomog δ (map (Int.castRingHom ℚ) f)`. Rewrite using `[hmap, IsMultiHomog]`.

Simplify using `using (isWeightedHomogeneous_C _ a).mul hδ`. Use `⟨δ, f, hprim, ?_⟩` and prove the remaining obligations. Establish `h` using `hA n e δ P _ hP hC hH`. Rewrite `h` using `[map_map, show (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from RingHom.ext_int _ _]`. Then use the resulting hypothesis.
-/
theorem IntChowFormExists.proof (hA : ChowFormToComplexChowForm.Statement) (hG : GenericFibreIdeal.Statement)
    (hD : GenericFibreDim.Statement) : IntChowFormExists.Statement := by
  intro n e P hP
  have hQ := (hG n (e + 1) P hP).1
  obtain ⟨g, hg⟩ := chowFormExists ℚ n (e + 1) (genericIdeal P) hQ (hD n (e + 1) P hP)
  obtain ⟨δ, -, hδ⟩ := ChowFormMultiHomog.full ℚ n (e + 1) (genericIdeal P) g hQ hg
  obtain ⟨a, ha, f, hprim, hmap⟩ := exists_isPrimitive_map_eq_C_mul g hg.1
  have hC : IsChowForm (genericIdeal P) (e + 1) (map (Int.castRingHom ℚ) f) := by
    rw [hmap]
    exact isChowForm_C_mul hg ha
  have hH : IsMultiHomog δ (map (Int.castRingHom ℚ) f) := by
    rw [hmap, IsMultiHomog]
    simpa using (isWeightedHomogeneous_C _ a).mul hδ
  refine ⟨δ, f, hprim, ?_⟩
  have h := hA n e δ P _ hP hC hH
  rwa [map_map, show (Rat.castHom ℂ).comp (Int.castRingHom ℚ) = Int.castRingHom ℂ from
    RingHom.ext_int _ _] at h

end ObjectsChow

end GroundTheory.Heights₂.Heights
