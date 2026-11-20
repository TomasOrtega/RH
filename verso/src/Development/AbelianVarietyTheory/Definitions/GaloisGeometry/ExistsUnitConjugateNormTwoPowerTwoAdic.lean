import Mathlib
import Formalism.PeriodIntegrals.GoodTwo
import Formalism.EllipticTorsion.EllipticTorsionProofs.Deuring
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral
import Formalism.LocalToGlobal.TorsionIntegrality.UniformGaussModels.StatementH
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ChainPC
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.DyadicStableLattices.ExistsNormEqTwoPow
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsGoodReductionAlgebraicWeierstrassModel

noncomputable section
open scoped ComplexConjugate
open Filter Topology

namespace GlobalTheory.ThLoc.GoodTwo

open PI.GoodTwo

/- English proof (translation)
Introduce `d L _ hd4 hcm`. Take `⟨a, τ, ha, h⟩` from `GlobalTheory.exists_lattice_eq_mul_tau L`. Establish `e : Formalism.L2.Th1.CM.jInv L = (GlobalTheory.latticeCurve L).j`. Rewrite using `[WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄, Formalism.L2.Th1.CM.jInv]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e, GlobalTheory.latticeCurve_j ha h]`. Use `GlobalTheory.isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) ?_ ?_` and prove the remaining obligations. Introduce `m hm`. Establish `him` using `congrArg Complex.im hm`. Simplify using `[Formalism.L2.Th1.CM.omegaK] at him`.

Use linear arithmetic over natural numbers and integers. Introduce `x hx`. Take `⟨m, n, rfl⟩` from `Submodule.mem_span_pair.1 hx`. Take `⟨m', n', h'⟩` from `(h _).1 (hcm _ ((h _).2 ⟨m, n, rfl⟩))`. Use `Submodule.mem_span_pair.2 ⟨m', n', ?_⟩` and prove the remaining obligations.

Simplify using `only [zsmul_eq_mul, mul_one]`. Apply `mul_left_cancel₀ ha` to reduce the goal to its premises. Rewrite using `[h']`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isIntegral_jInv : Formalism.L2.Th1.CM.JInvariantIntegrality := by
  intro d L _ hd4 hcm
  obtain ⟨a, τ, ha, h⟩ := GlobalTheory.exists_lattice_eq_mul_tau L
  have e : Formalism.L2.Th1.CM.jInv L = (GlobalTheory.latticeCurve L).j := by
    rw [WeierstrassCurve.j, Units.val_inv_eq_inv_val, WeierstrassCurve.coe_Δ', GlobalTheory.latticeCurve_Δ, GlobalTheory.latticeCurve_c₄,
      Formalism.L2.Th1.CM.jInv]
    ring
  rw [e, GlobalTheory.latticeCurve_j ha h]
  refine GlobalTheory.isIntegral_modularJ_of_mul_mem (α := Formalism.L2.Th1.CM.omegaK d) ?_ ?_
  · intro m hm
    have him := congrArg Complex.im hm
    simp [Formalism.L2.Th1.CM.omegaK] at him
    omega
  · intro x hx
    obtain ⟨m, n, rfl⟩ := Submodule.mem_span_pair.1 hx
    obtain ⟨m', n', h'⟩ := (h _).1 (hcm _ ((h _).2 ⟨m, n, rfl⟩))
    refine Submodule.mem_span_pair.2 ⟨m', n', ?_⟩
    simp only [zsmul_eq_mul, mul_one]
    apply mul_left_cancel₀ ha
    rw [h']; ring

/- English proof (translation)
The claim follows from `GlobalTheory.MomOne.model_norm_le_one_of_isIntegral ((isIntegral_jInv d L hsq hmod hcm).map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[p]) (RingHom.ext_int _ _))`.
-/
theorem norm_jInv_le_one (d : ℕ) (L : PeriodPair) (hsq : Squarefree d) (hmod : d % 4 = 3) (hcm : Formalism.L2.Th1.CM.HasCMBy d L)
    (p : ℕ) [Fact p.Prime] (ι : ℂ ≃+* ℂ_[p]) : ‖ι (Formalism.L2.Th1.CM.jInv L)‖ ≤ 1 :=
  GlobalTheory.MomOne.model_norm_le_one_of_isIntegral
    ((isIntegral_jInv d L hsq hmod hcm).map_of_comp_eq (RingHom.id ℤ) (ι : ℂ →+* ℂ_[p]) (RingHom.ext_int _ _))

section

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

def RootCubic : Prop :=
  ∀ j r : ℂ_[2], ‖j‖ ≤ 1 → (r + 16) ^ 3 = j * r → ‖r‖ ≤ 1

def UnitOfRoot : Prop :=
  ∀ j r : ℂ_[2], ‖r‖ = 1 → (r + 16) ^ 3 = j * r → ‖j‖ = 1

def UnitChoice : Prop :=
  ∀ d : ℕ, d % 8 = 7 → ∀ (h : ℕ) (x y : ℤ), 0 < h → Odd y →
    x ^ 2 + x * y + (((d + 1) / 4 : ℕ) : ℤ) * y ^ 2 = 2 ^ h → ∀ ι : ℂ ≃+* ℂ_[2],
    ∃ π : ℂ, (π = x + y * omegaK d ∨ π = x + y * conj (omegaK d)) ∧ ‖ι π‖ = 1

def DeuringScale : Prop :=
  ∀ (L : PeriodPair) (ι : ℂ ≃+* ℂ_[2]) (W : WeierstrassCurve ℂ_[2]), W.Δ ≠ 0 →
    W.c₄ ^ 3 = ι (jInv L) * W.Δ →
    ∃ (c : ℂ) (hc : c ≠ 0), W.c₄ / 12 = ι (scalePair L c hc).g₂ ∧ W.c₆ / 216 = ι (scalePair L c hc).g₃

end

namespace HalfW

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

/- English proof (translation)
Introduce `K _ _ _ W g2 g3 hΔ hD hrel`. Establish `hcr` using `W.c_relation`. Take `⟨G2, hG2⟩ : ∃ G2 : K, G2 = W.c₄ / 12` from `⟨_, rfl⟩`. Take `⟨G3, hG3⟩ : ∃ G3 : K, G3 = W.c₆ / 216` from `⟨_, rfl⟩`. Rewrite using `[← hG2, ← hG3]`.

Establish `hc4 : W.c₄ = 12 * G2` using `by rw [hG2]; ring`. Establish `hc6 : W.c₆ = 216 * G3` using `by rw [hG3]; ring`. Establish `hΔG : W.Δ = G2 ^ 3 - 27 * G3 ^ 2`. Establish `h1728 : (1728 : K) ≠ 0` using `by norm_num`. Apply `mul_left_cancel₀ h1728` to reduce the goal to its premises.

Rewrite using `[hcr, hc4, hc6]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hrel` using `[hc4, hΔG]`. Rewrite `hΔ` using `[hΔG]`. Establish `key : G2 ^ 3 * g3 ^ 2 = g2 ^ 3 * G3 ^ 2`.

Establish `h : (46656 : K) ≠ 0` using `by norm_num`. Apply `mul_left_cancel₀ h` to reduce the goal to its premises. Take the linear combination `(-1 : K) * hrel`. Distinguish the cases in `hg2 : g2 = 0`. Substitute `hg2` using the available equality.

Establish `hg3 : g3 ≠ 0`. Introduce and unpack `rfl; exact hD (by ring)`. Establish `hG2z : G2 = 0`. Establish `h0 : (12 * G2) ^ 3 * ((0 : K) ^ 3 - 27 * g3 ^ 2) = 0` using `by rw [hrel]; ring`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases.

Use `pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h` as an intermediate fact. Simplify using `using this`. Conclude with `absurd h hD`. Substitute `hG2z` using the available equality. Establish `hG3 : G3 ≠ 0`.

Introduce and unpack `rfl; exact hΔ (by ring)`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (G3 / g3) (by norm_num : 0 < 6)`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl; exact div_ne_zero hG3 hg3 (by rw [← hu]; ring)`. Conclude with `⟨u, hu0, by ring, by rw [hu, div_mul_cancel₀ _ hg3]⟩`.

Distinguish the cases in `hg3 : g3 = 0`. Substitute `hg3` using the available equality. Establish `hG3z : G3 = 0`. Establish `h0 : g2 ^ 3 * G3 ^ 2 = 0` using `by rw [← key]; ring`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases.

Conclude with `absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h) hg2`. Conclude with `pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h`. Substitute `hG3z` using the available equality. Establish `hG2 : G2 ≠ 0`. Introduce and unpack `rfl; exact hΔ (by ring)`.

Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq (G2 / g2) (by norm_num : 0 < 4)`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl; exact div_ne_zero hG2 hg2 (by rw [← hu]; ring)`. Conclude with `⟨u, hu0, by rw [hu, div_mul_cancel₀ _ hg2], by ring⟩`. Establish `hG2 : G2 ≠ 0`.

Introduce and unpack `rfl`. Establish `h0 : g2 ^ 3 * G3 ^ 2 = 0` using `by rw [← key]; ring`. Establish `hG3 : G3 = 0`. Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h) hg2`.

Conclude with `pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h`. Substitute `hG3; exact hΔ (by ring)` using the available equality. Establish `hG3 : G3 ≠ 0`. Introduce and unpack `rfl`. Establish `h0 : G2 ^ 3 * g3 ^ 2 = 0` using `by rw [key]; ring`.

Break down `mul_eq_zero.1 h0 with h | h` into its components or cases. Conclude with `hG2 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h)`. Conclude with `hg3 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)`. Take `⟨s, hs⟩ : ∃ s : K, s = (G3 / g3) / (G2 / g2)` from `⟨_, rfl⟩`. Establish `hs0 : s ≠ 0`.

Rewrite using `[hs]`. Conclude with `div_ne_zero (div_ne_zero hG3 hg3) (div_ne_zero hG2 hg2)`. Establish `hs2 : s ^ 2 = G2 / g2`. Rewrite using `[hs, div_pow, div_pow, div_pow, div_div_eq_mul_div, div_eq_div_iff (by positivity) hg2]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `(-1 : K) * key`. Take `⟨u, hu⟩` from `IsAlgClosed.exists_pow_nat_eq s (by norm_num : 0 < 2)`. Establish `hu0 : u ≠ 0`. Introduce and unpack `rfl; exact hs0 (by rw [← hu]; ring)`. Use `⟨u, hu0, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[show u ^ 4 = (u ^ 2) ^ 2 by ring, hu, hs2, div_mul_cancel₀ _ hg2]`. Rewrite using `[show u ^ 6 = (u ^ 2) ^ 2 * u ^ 2 by ring, hu, hs2, hs]`. Clear the denominators using the available nonvanishing facts.
-/
theorem twist : Twist := by
  intro K _ _ _ W g2 g3 hΔ hD hrel
  have hcr := W.c_relation
  obtain ⟨G2, hG2⟩ : ∃ G2 : K, G2 = W.c₄ / 12 := ⟨_, rfl⟩
  obtain ⟨G3, hG3⟩ : ∃ G3 : K, G3 = W.c₆ / 216 := ⟨_, rfl⟩
  rw [← hG2, ← hG3]
  have hc4 : W.c₄ = 12 * G2 := by rw [hG2]; ring
  have hc6 : W.c₆ = 216 * G3 := by rw [hG3]; ring
  have hΔG : W.Δ = G2 ^ 3 - 27 * G3 ^ 2 := by
    have h1728 : (1728 : K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h1728
    rw [hcr, hc4, hc6]; ring
  rw [hc4, hΔG] at hrel
  rw [hΔG] at hΔ
  have key : G2 ^ 3 * g3 ^ 2 = g2 ^ 3 * G3 ^ 2 := by
    have h : (46656 : K) ≠ 0 := by norm_num
    apply mul_left_cancel₀ h
    linear_combination (-1 : K) * hrel
  by_cases hg2 : g2 = 0
  · subst hg2
    have hg3 : g3 ≠ 0 := by
      rintro rfl; exact hD (by ring)
    have hG2z : G2 = 0 := by
      have h0 : (12 * G2) ^ 3 * ((0 : K) ^ 3 - 27 * g3 ^ 2) = 0 := by rw [hrel]; ring
      rcases mul_eq_zero.1 h0 with h | h
      · have := pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h
        simpa using this
      · exact absurd h hD
    subst hG2z
    have hG3 : G3 ≠ 0 := by
      rintro rfl; exact hΔ (by ring)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (G3 / g3) (by norm_num : 0 < 6)
    have hu0 : u ≠ 0 := by
      rintro rfl; exact div_ne_zero hG3 hg3 (by rw [← hu]; ring)
    exact ⟨u, hu0, by ring, by rw [hu, div_mul_cancel₀ _ hg3]⟩
  by_cases hg3 : g3 = 0
  · subst hg3
    have hG3z : G3 = 0 := by
      have h0 : g2 ^ 3 * G3 ^ 2 = 0 := by rw [← key]; ring
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h) hg2
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    subst hG3z
    have hG2 : G2 ≠ 0 := by
      rintro rfl; exact hΔ (by ring)
    obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq (G2 / g2) (by norm_num : 0 < 4)
    have hu0 : u ≠ 0 := by
      rintro rfl; exact div_ne_zero hG2 hg2 (by rw [← hu]; ring)
    exact ⟨u, hu0, by rw [hu, div_mul_cancel₀ _ hg2], by ring⟩
  have hG2 : G2 ≠ 0 := by
    rintro rfl
    have h0 : g2 ^ 3 * G3 ^ 2 = 0 := by rw [← key]; ring
    have hG3 : G3 = 0 := by
      rcases mul_eq_zero.1 h0 with h | h
      · exact absurd (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h) hg2
      · exact pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h
    subst hG3; exact hΔ (by ring)
  have hG3 : G3 ≠ 0 := by
    rintro rfl
    have h0 : G2 ^ 3 * g3 ^ 2 = 0 := by rw [key]; ring
    rcases mul_eq_zero.1 h0 with h | h
    · exact hG2 (pow_eq_zero_iff (n := 3) (by norm_num) |>.1 h)
    · exact hg3 (pow_eq_zero_iff (n := 2) (by norm_num) |>.1 h)
  obtain ⟨s, hs⟩ : ∃ s : K, s = (G3 / g3) / (G2 / g2) := ⟨_, rfl⟩
  have hs0 : s ≠ 0 := by
    rw [hs]; exact div_ne_zero (div_ne_zero hG3 hg3) (div_ne_zero hG2 hg2)
  have hs2 : s ^ 2 = G2 / g2 := by
    rw [hs, div_pow, div_pow, div_pow, div_div_eq_mul_div, div_eq_div_iff (by positivity) hg2]
    field_simp
    linear_combination (-1 : K) * key
  obtain ⟨u, hu⟩ := IsAlgClosed.exists_pow_nat_eq s (by norm_num : 0 < 2)
  have hu0 : u ≠ 0 := by
    rintro rfl; exact hs0 (by rw [← hu]; ring)
  refine ⟨u, hu0, ?_, ?_⟩
  · rw [show u ^ 4 = (u ^ 2) ^ 2 by ring, hu, hs2, div_mul_cancel₀ _ hg2]
  · rw [show u ^ 6 = (u ^ 2) ^ 2 * u ^ 2 by ring, hu, hs2, hs]
    field_simp

end HalfW

section

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

/- English proof (translation)
Introduce `L ι W hΔ hj`. Establish `hd : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0` using `Formalism.L2.Th1.F.discNeZero L`. Establish `hdι : ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = (ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2`. Simplify using `[map_sub, map_mul, map_pow, map_ofNat]`. Establish `hd' : (ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2 ≠ 0`.

Rewrite using `[← hdι]`. Conclude with `(map_ne_zero ι).mpr hd`. Establish `hjι : ι (jInv L) = 1728 * (ι L.g₂) ^ 3 / ((ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2)`. Unfold `jInv`. Rewrite using `[map_div₀, hdι]`.

Simplify using `[map_mul, map_pow, map_ofNat]`. Establish `hrel : W.c₄ ^ 3 * ((ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2) = 1728 * (ι L.g₂) ^ 3 * W.Δ`. Rewrite using `[hj, hjι]`. Clear the denominators using the available nonvanishing facts. Take `⟨u, hu, h4, h6⟩` from `hT ℂ_[2] W (ι L.g₂) (ι L.g₃) hΔ hd' hrel`.

Establish `hu' : ι.symm u ≠ 0`. Introduce `h0`. Apply `hu` to reduce the goal to its premises. Use `congrArg ι h0` as an intermediate fact. Simplify using `using this`.

Establish `hc : (ι.symm u)⁻¹ ≠ 0` using `inv_ne_zero hu'`. Establish `hH` using `Formalism.L2.Th1.F.homogeneity L (ι.symm u)⁻¹ hc`. Use `⟨(ι.symm u)⁻¹, hc, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hH.2.2.2.2.2.2.2.2.2.1, h4]`. Simplify using `[map_mul, map_pow, inv_pow, inv_inv]`.

Rewrite using `[hH.2.2.2.2.2.2.2.2.2.2, h6]`. Simplify using `[map_mul, map_pow, inv_pow, inv_inv]`.
-/
theorem deuringScale_of (hT : Twist) : DeuringScale := by
  intro L ι W hΔ hj
  have hd : L.g₂ ^ 3 - 27 * L.g₃ ^ 2 ≠ 0 := Formalism.L2.Th1.F.discNeZero L
  have hdι : ι (L.g₂ ^ 3 - 27 * L.g₃ ^ 2) = (ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2 := by
    simp [map_sub, map_mul, map_pow, map_ofNat]
  have hd' : (ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2 ≠ 0 := by
    rw [← hdι]; exact (map_ne_zero ι).mpr hd
  have hjι : ι (jInv L) = 1728 * (ι L.g₂) ^ 3 / ((ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2) := by
    unfold jInv
    rw [map_div₀, hdι]
    simp [map_mul, map_pow, map_ofNat]
  have hrel : W.c₄ ^ 3 * ((ι L.g₂) ^ 3 - 27 * (ι L.g₃) ^ 2) = 1728 * (ι L.g₂) ^ 3 * W.Δ := by
    rw [hj, hjι]
    field_simp
  obtain ⟨u, hu, h4, h6⟩ := hT ℂ_[2] W (ι L.g₂) (ι L.g₃) hΔ hd' hrel
  have hu' : ι.symm u ≠ 0 := by
    intro h0
    apply hu
    have := congrArg ι h0
    simpa using this
  have hc : (ι.symm u)⁻¹ ≠ 0 := inv_ne_zero hu'
  have hH := Formalism.L2.Th1.F.homogeneity L (ι.symm u)⁻¹ hc
  refine ⟨(ι.symm u)⁻¹, hc, ?_, ?_⟩
  · rw [hH.2.2.2.2.2.2.2.2.2.1, h4]
    simp [map_mul, map_pow, inv_pow, inv_inv]
  · rw [hH.2.2.2.2.2.2.2.2.2.2, h6]
    simp [map_mul, map_pow, inv_pow, inv_inv]

end

section

/- English proof (translation)
The claim follows from `deuringScale_of HalfW.twist`.
-/
theorem deuring_lattice_homothety_two_adic : DeuringScale := deuringScale_of HalfW.twist

end

section

/- English proof (translation)
Establish `h2 : ‖((2 : ℚ_[2]) : ℂ_[2])‖ = 1 / 2`. Rewrite using `[PadicComplex.norm_extends']`. Use `Padic.norm_p (p := 2)` as an intermediate fact. Evaluate the numerical expressions using `at this ⊢`. Conclude with `this`.

Establish `hc : ((2 : ℚ_[2]) : ℂ_[2]) = 2`. Use `PadicComplex.coe_natCast 2 2` as an intermediate fact. Rewrite using `[map_ofNat]`. Simplify using `using this`. Rewrite `h2` using `[hc]`. Then use the resulting hypothesis.
-/
theorem cubic_norm_two : ‖(2 : ℂ_[2])‖ = 1 / 2 := by
  have h2 : ‖((2 : ℚ_[2]) : ℂ_[2])‖ = 1 / 2 := by
    rw [PadicComplex.norm_extends']
    have := Padic.norm_p (p := 2)
    norm_num at this ⊢
    exact this
  have hc : ((2 : ℚ_[2]) : ℂ_[2]) = 2 := by
    have := PadicComplex.coe_natCast 2 2
    rw [map_ofNat]
    simpa using this
  rwa [hc] at h2

/- English proof (translation)
Rewrite using `[show (16 : ℂ_[2]) = 2 ^ 4 by norm_num, norm_pow, cubic_norm_two]`. Evaluate the numerical expressions.
-/
theorem cubic_norm_sixteen : ‖(16 : ℂ_[2])‖ = 1 / 16 := by
  rw [show (16 : ℂ_[2]) = 2 ^ 4 by norm_num, norm_pow, cubic_norm_two]
  norm_num

/- English proof (translation)
Introduce `j r hj h`. Assume the negation of the conclusion as `hr`. Use `push Not at hr`. Establish `h16 : ‖(16 : ℂ_[2])‖ < ‖r‖` using `by rw [cubic_norm_sixteen]; linarith`. Establish `e : ‖r + 16‖ = ‖r‖`.

Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h16.ne', max_eq_left h16.le]`. Establish `hn : ‖r + 16‖ ^ 3 = ‖j‖ * ‖r‖`. Rewrite using `[← norm_pow, h, norm_mul]`. Rewrite `hn` using `[e]`. Establish `hpos : 0 < ‖r‖` using `by linarith`.

Establish `: ‖r‖ ^ 3 ≤ ‖r‖` using `by rw [hn]; exact mul_le_of_le_one_left (norm_nonneg _) hj`. Establish `h2 : 1 < ‖r‖ ^ 2` using `one_lt_pow₀ hr (by norm_num)`. Use polynomial arithmetic with `[mul_lt_mul_of_pos_left h2 hpos]`.
-/
theorem integral_root_cubic_X_add_sixteen_two_adic : RootCubic := by
  intro j r hj h
  by_contra hr
  push Not at hr
  have h16 : ‖(16 : ℂ_[2])‖ < ‖r‖ := by rw [cubic_norm_sixteen]; linarith
  have e : ‖r + 16‖ = ‖r‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h16.ne', max_eq_left h16.le]
  have hn : ‖r + 16‖ ^ 3 = ‖j‖ * ‖r‖ := by
    rw [← norm_pow, h, norm_mul]
  rw [e] at hn
  have hpos : 0 < ‖r‖ := by linarith
  have : ‖r‖ ^ 3 ≤ ‖r‖ := by rw [hn]; exact mul_le_of_le_one_left (norm_nonneg _) hj
  have h2 : 1 < ‖r‖ ^ 2 := one_lt_pow₀ hr (by norm_num)
  nlinarith [mul_lt_mul_of_pos_left h2 hpos]

/- English proof (translation)
Introduce `j r hr h`. Establish `h16 : ‖(16 : ℂ_[2])‖ < ‖r‖` using `by rw [cubic_norm_sixteen, hr]; norm_num`. Establish `e : ‖r + 16‖ = ‖r‖`. Rewrite using `[IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h16.ne', max_eq_left h16.le]`. Establish `hn : ‖r + 16‖ ^ 3 = ‖j‖ * ‖r‖`.

Rewrite using `[← norm_pow, h, norm_mul]`. Rewrite `hn` using `[e, hr]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem unit_root_cubic_forces_unit_jInvariant : UnitOfRoot := by
  intro j r hr h
  have h16 : ‖(16 : ℂ_[2])‖ < ‖r‖ := by rw [cubic_norm_sixteen, hr]; norm_num
  have e : ‖r + 16‖ = ‖r‖ := by
    rw [IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm h16.ne', max_eq_left h16.le]
  have hn : ‖r + 16‖ ^ 3 = ‖j‖ * ‖r‖ := by
    rw [← norm_pow, h, norm_mul]
  rw [e, hr] at hn
  linarith

end

section

open Formalism.L2.Th1.CM (HasCMBy omegaK jInv)
open Formalism.L2.Th1.F (scalePair)

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' (p := 2) ((3:ℕ) : ℚ_[2])`. Rewrite `h` using `[Padic.norm_natCast_eq_one_iff.2 (by norm_num)]`. Rewrite using `[← h]`. Use `congr 1`. Rewrite using `[map_natCast, PadicComplex.coe_natCast]`.

Both sides reduce to the same expression.
-/
theorem norm_three_padicComplex_two : ‖(3 : ℂ_[2])‖ = 1 := by
  have h := PadicComplex.norm_extends' (p := 2) ((3:ℕ) : ℚ_[2])
  rw [Padic.norm_natCast_eq_one_iff.2 (by norm_num)] at h
  rw [← h]
  congr 1
  rw [map_natCast, PadicComplex.coe_natCast]
  rfl

/- English proof (translation)
The claim follows from `Formalism.L2.Th1.F.discNeZero L`.
-/
theorem disc_ne_zero (L : PeriodPair) : disc L ≠ 0 := Formalism.L2.Th1.F.discNeZero L

/- English proof (translation)
Establish `hinv : π⁻¹ ≠ 0` using `inv_ne_zero hπ`. Establish `hH` using `Formalism.L2.Th1.F.homogeneity L π⁻¹ hinv`. Establish `hlat : M.lattice = (scalePair L π⁻¹ hinv).lattice`. Use extensionality with `z`. Rewrite using `[hM z, hH.1 z, inv_inv]`.

Establish `hO` using `Formalism.L2.Th1.F.latticeOnly M (scalePair L π⁻¹ hinv) hlat`. Take `⟨-, -, -, -, -, -, -, hg2, hg3⟩` from `hO`. Take `⟨-, -, -, -, -, -, -, -, -, h2, h3⟩` from `hH`. Unfold `disc`. Rewrite using `[hg2, hg3, h2, h3]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem disc_of_mul (L M : PeriodPair) (π : ℂ) (hπ : π ≠ 0) (hM : ∀ z, z ∈ M.lattice ↔ π * z ∈ L.lattice) :
    disc M = π ^ 12 * disc L := by
  have hinv : π⁻¹ ≠ 0 := inv_ne_zero hπ
  have hH := Formalism.L2.Th1.F.homogeneity L π⁻¹ hinv
  have hlat : M.lattice = (scalePair L π⁻¹ hinv).lattice := by
    ext z
    rw [hM z, hH.1 z, inv_inv]
  have hO := Formalism.L2.Th1.F.latticeOnly M (scalePair L π⁻¹ hinv) hlat
  obtain ⟨-, -, -, -, -, -, -, hg2, hg3⟩ := hO
  obtain ⟨-, -, -, -, -, -, -, -, -, h2, h3⟩ := hH
  unfold disc
  rw [hg2, hg3, h2, h3]
  field_simp

/- English proof (translation)
Introduce `d L hsf hd hL ι`. Take `⟨h, x, y, hh, hy, hxy⟩` from `hN d hsf hd`. Take `⟨π, hπ, hπ1⟩` from `hP d hd h x y hh hy hxy ι`. Take `⟨M, hM0, hMcm, hMidx, hMh⟩` from `hC d L hd hL h x y hy hxy π hπ`. Establish `hd4 : d % 4 = 3` using `by omega`.

Establish `hπ0 : π ≠ 0`. Introduce and unpack `rfl`. Simplify using `at hπ1`. Use `set r : ℕ → ℂ := fun i => disc (M (i + 1)) / disc (M i) with hr_def`. Establish `hcub : ∀ i, i < h → (r i + 16) ^ 3 = jInv (M i) * r i`.

Introduce `i hi`. Establish `e` using `hW (M i) (M (i + 1)) (hMidx i hi)`. Establish `h0` using `disc_ne_zero (M i)`. Simplify using `only [hr_def]`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `e`. Establish `hcubι : ∀ i, i < h → (ι (r i) + 16) ^ 3 = ι (jInv (M i)) * ι (r i)`. Introduce `i hi`. Use `congrArg ι (hcub i hi)` as an intermediate fact. Simplify `this` using `[map_add, map_pow, map_mul, map_ofNat]`.

Establish `hle : ∀ i, i < h → ‖ι (r i)‖ ≤ 1` using `fun i hi => hR _ _ (norm_jInv_le_one d (M i) hsf hd4 (hMcm i) 2 ι) (hcubι i hi)`. Establish `htel : ∀ n, ∏ i ∈ Finset.range n, r i = disc (M n) / disc (M 0)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => simp [div_self (disc_ne_zero (M 0))]`.

Consider the case `succ n ih`. Rewrite using `[Finset.prod_range_succ, ih]`. Simplify using `only [hr_def]`. Use `disc_ne_zero (M n)` as an intermediate fact. Use `disc_ne_zero (M 0)` as an intermediate fact.

Clear the denominators using the available nonvanishing facts. Establish `hprod : ∏ i ∈ Finset.range h, r i = π ^ 12`. Rewrite using `[htel, disc_of_mul L (M h) π hπ0 hMh, hM0]`. Clear denominators, using `[disc_ne_zero L]` for the nonvanishing conditions. Establish `hnorm : ∏ i ∈ Finset.range h, ‖ι (r i)‖ = 1`.

Rewrite using `[← norm_prod, ← map_prod, hprod, map_pow, norm_pow, hπ1, one_pow]`. Take `⟨k, rfl⟩ : ∃ k, h = k + 1` from `⟨h - 1, by omega⟩`. Rewrite `hnorm` using `[Finset.prod_range_succ']`. Establish `hrest : ∏ i ∈ Finset.range k, ‖ι (r (i + 1))‖ ≤ 1` using `Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => hle (i + 1) (by simp at hi; omega))`. Establish `h0le` using `hle 0 (by omega)`.

Establish `hr0 : ‖ι (r 0)‖ = 1`. Use `mul_le_of_le_one_left (norm_nonneg (ι (r 0))) hrest` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion. Use `hU _ _ hr0 (hcubι 0 (by omega))` as an intermediate fact. Rewrite `this` using `[hM0]`. Then use the resulting hypothesis.
-/
theorem jUnit_of (hW : TwoIsog) (hN : NormPow) (hC : Chain) (hR : RootCubic) (hU : UnitOfRoot)
    (hP : UnitChoice) : JUnit := by
  intro d L hsf hd hL ι
  obtain ⟨h, x, y, hh, hy, hxy⟩ := hN d hsf hd
  obtain ⟨π, hπ, hπ1⟩ := hP d hd h x y hh hy hxy ι
  obtain ⟨M, hM0, hMcm, hMidx, hMh⟩ := hC d L hd hL h x y hy hxy π hπ
  have hd4 : d % 4 = 3 := by omega
  have hπ0 : π ≠ 0 := by
    rintro rfl
    simp at hπ1
  set r : ℕ → ℂ := fun i => disc (M (i + 1)) / disc (M i) with hr_def

  have hcub : ∀ i, i < h → (r i + 16) ^ 3 = jInv (M i) * r i := by
    intro i hi
    have e := hW (M i) (M (i + 1)) (hMidx i hi)
    have h0 := disc_ne_zero (M i)
    simp only [hr_def]
    field_simp
    linear_combination e
  have hcubι : ∀ i, i < h → (ι (r i) + 16) ^ 3 = ι (jInv (M i)) * ι (r i) := by
    intro i hi
    have := congrArg ι (hcub i hi)
    simpa [map_add, map_pow, map_mul, map_ofNat] using this
  have hle : ∀ i, i < h → ‖ι (r i)‖ ≤ 1 := fun i hi =>
    hR _ _ (norm_jInv_le_one d (M i) hsf hd4 (hMcm i) 2 ι) (hcubι i hi)

  have htel : ∀ n, ∏ i ∈ Finset.range n, r i = disc (M n) / disc (M 0) := by
    intro n
    induction n with
    | zero => simp [div_self (disc_ne_zero (M 0))]
    | succ n ih =>
      rw [Finset.prod_range_succ, ih]
      simp only [hr_def]
      have := disc_ne_zero (M n)
      have := disc_ne_zero (M 0)
      field_simp
  have hprod : ∏ i ∈ Finset.range h, r i = π ^ 12 := by
    rw [htel, disc_of_mul L (M h) π hπ0 hMh, hM0]
    field_simp [disc_ne_zero L]
  have hnorm : ∏ i ∈ Finset.range h, ‖ι (r i)‖ = 1 := by
    rw [← norm_prod, ← map_prod, hprod, map_pow, norm_pow, hπ1, one_pow]
  obtain ⟨k, rfl⟩ : ∃ k, h = k + 1 := ⟨h - 1, by omega⟩
  rw [Finset.prod_range_succ'] at hnorm
  have hrest : ∏ i ∈ Finset.range k, ‖ι (r (i + 1))‖ ≤ 1 :=
    Finset.prod_le_one (fun _ _ => norm_nonneg _) (fun i hi => hle (i + 1) (by simp at hi; omega))
  have h0le := hle 0 (by omega)
  have hr0 : ‖ι (r 0)‖ = 1 := by
    have := mul_le_of_le_one_left (norm_nonneg (ι (r 0))) hrest
    linarith
  have := hU _ _ hr0 (hcubι 0 (by omega))
  rwa [hM0] at this

/- English proof (translation)
Introduce `d L hsf hd hL ι`. Establish `hj1 : ‖ι (jInv L)‖ = 1` using `hJ d L hsf hd hL ι`. Take `⟨a, ha, hc4, hΔ⟩` from `Formalism.ELL.deuring_model ℂ_[2] norm_three_padicComplex_two (ι (jInv L)) hj1.le`. Establish `hΔ0 : (Formalism.ELL.deuring a).Δ ≠ 0`. Introduce `h0`.

Rewrite `hΔ` using `[h0, norm_zero]`. Evaluate the numerical expressions using `at hΔ`. Take `⟨c, hc, h4, h6⟩` from `hS L ι _ hΔ0 hc4`. Establish `hinv` using `(Formalism.ELL.deuring_invariant ℂ_[2] a).2`. Establish `hc4n : ‖(Formalism.ELL.deuring a).c₄‖ = 1`.

Establish `h` using `congrArg norm hc4`. Rewrite `h` using `[norm_pow, norm_mul, hj1, hΔ, one_mul]`. Conclude with `(pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h`. Establish `hsub : ‖a ^ 3 - 24‖ ≤ 1`. Rewrite using `[sub_eq_add_neg]`.

Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) ha`. Rewrite using `[norm_neg]`. Conclude with `IsUltrametricDist.norm_natCast_le_one ℂ_[2] 24` after adjusting the coercions.

Establish `ha1 : ‖a‖ = 1`. Rewrite `hc4n` using `[hinv, norm_mul]`. Establish `: 1 ≤ ‖a‖`. Combine the equalities or inequalities in the displayed calculation. Conclude with `le_antisymm ha this`.

Use `⟨c, hc, Formalism.ELL.deuring a, ⟨h4, h6⟩, ⟨?_, ?_, ?_, ?_, ?_, hΔ⟩, ?_⟩` and prove the remaining obligations. Conclude with `ha`. Simplify using `[Formalism.ELL.deuring]`. Simplify using `[Formalism.ELL.deuring]`. Simplify using `[Formalism.ELL.deuring]`.

Simplify using `[Formalism.ELL.deuring]`. Conclude with `ha1`.
-/
theorem full_of (hS : DeuringScale) (hJ : JUnit) : Full := by
  intro d L hsf hd hL ι
  have hj1 : ‖ι (jInv L)‖ = 1 := hJ d L hsf hd hL ι
  obtain ⟨a, ha, hc4, hΔ⟩ :=
    Formalism.ELL.deuring_model ℂ_[2] norm_three_padicComplex_two (ι (jInv L)) hj1.le
  have hΔ0 : (Formalism.ELL.deuring a).Δ ≠ 0 := by
    intro h0
    rw [h0, norm_zero] at hΔ
    norm_num at hΔ
  obtain ⟨c, hc, h4, h6⟩ := hS L ι _ hΔ0 hc4
  have hinv := (Formalism.ELL.deuring_invariant ℂ_[2] a).2
  have hc4n : ‖(Formalism.ELL.deuring a).c₄‖ = 1 := by
    have h := congrArg norm hc4
    rw [norm_pow, norm_mul, hj1, hΔ, one_mul] at h
    exact (pow_eq_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 h
  have hsub : ‖a ^ 3 - 24‖ ≤ 1 := by
    rw [sub_eq_add_neg]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ ?_)
    · rw [norm_pow]
      exact pow_le_one₀ (norm_nonneg _) ha
    · rw [norm_neg]
      exact_mod_cast IsUltrametricDist.norm_natCast_le_one ℂ_[2] 24
  have ha1 : ‖a‖ = 1 := by
    rw [hinv, norm_mul] at hc4n
    have : 1 ≤ ‖a‖ := by
      calc (1 : ℝ) = ‖a‖ * ‖a ^ 3 - 24‖ := hc4n.symm
        _ ≤ ‖a‖ * 1 := mul_le_mul_of_nonneg_left hsub (norm_nonneg _)
        _ = ‖a‖ := mul_one _
    exact le_antisymm ha this
  refine ⟨c, hc, Formalism.ELL.deuring a, ⟨h4, h6⟩, ⟨?_, ?_, ?_, ?_, ?_, hΔ⟩, ?_⟩
  · exact ha
  · simp [Formalism.ELL.deuring]
  · simp [Formalism.ELL.deuring]
  · simp [Formalism.ELL.deuring]
  · simp [Formalism.ELL.deuring]
  · exact ha1

/- English proof (translation)
The claim follows from `full_of hT (jUnit_of hW hN hC hR hU hP)`.
-/
theorem full_of_steps (hT : DeuringScale) (hW : TwoIsog) (hN : NormPow) (hC : Chain) (hR : RootCubic)
    (hU : UnitOfRoot) (hP : UnitChoice) : Full :=
  full_of hT (jUnit_of hW hN hC hR hU hP)

end

section

/- English proof (translation)
The claim follows from `full_of_steps deuring_lattice_homothety_two_adic hW hN hC integral_root_cubic_X_add_sixteen_two_adic unit_root_cubic_forces_unit_jInvariant hP`.
-/
theorem full_of_open (hW : TwoIsog) (hN : NormPow) (hC : Chain) (hP : UnitChoice) : Full :=
  full_of_steps deuring_lattice_homothety_two_adic hW hN hC integral_root_cubic_X_add_sixteen_two_adic unit_root_cubic_forces_unit_jInvariant hP

end

section
namespace IsogenyReduction

/- English proof (translation)
Use `set f : ℂ → ℂ := fun z => (z ^ k)⁻¹ with hf`. Use `set A : Set ℂ := (L.lattice : Set ℂ) with hA`. Use `set B : Set ℂ := {z | z - t ∈ L.lattice} with hB`. Establish `hAs : HasSum (f ∘ (Subtype.val : A → ℂ)) (L.G k)`. Use `L.hasSum_sumInvPow 0 hk` as an intermediate fact.

Simplify using `only [sub_zero, PeriodPair.sumInvPow_zero] at this`. Conclude with `this`. Set `e : L.lattice ≃ B` to `{ toFun := fun l => ⟨l.1 - t, by show l.1 - t - t ∈ L.lattice`. Use `L.lattice.sub_mem l.2 h2t` as an intermediate fact. Rewrite using `[show l.1 - 2 * t = l.1 - t - t by ring] at this⟩` and apply the resulting hypothesis.

Use `invFun := fun z => ⟨z.1 + t, by`. Establish `h1 : z.1 - t ∈ L.lattice` using `z.2`. Use `L.lattice.add_mem h1 h2t` as an intermediate fact. Rewrite using `[show z.1 - t + 2 * t = z.1 + t by ring] at this⟩` and apply the resulting hypothesis. Use `left_inv := fun l => by ext; simp`.

Use `right_inv := fun z => by ext; simp }`. Establish `hBs : HasSum (f ∘ (Subtype.val : B → ℂ)) (L.sumInvPow t k)`. Rewrite using `[← e.hasSum_iff]`. Use `L.hasSum_sumInvPow t hk` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use function extensionality and compare the values at `l`. Both sides reduce to the same expression. Establish `hdis : Disjoint A B`. Rewrite using `[Set.disjoint_left]`. Introduce `z hzA hzB`.

Apply `ht` to reduce the goal to its premises. Use `L.lattice.sub_mem hzA hzB` as an intermediate fact. Simplify using `using this`. Establish `hU` using `hAs.add_disjoint hdis hBs`. Establish `hset : (L'.lattice : Set ℂ) = A ∪ B`.

Use extensionality with `z`. Simplify using `only [Set.mem_union, A, B, Set.mem_ofPred_eq, SetLike.mem_coe]`. Conclude with `hL' z`. Rewrite `hU` using `[hasSum_subtype_iff_indicator, ← hset, ← hasSum_subtype_iff_indicator]`. Conclude with `hU.tsum_eq`.
-/
lemma G_split (L L' : PeriodPair) (t : ℂ) (h2t : 2 * t ∈ L.lattice)
    (hL' : ∀ z, z ∈ L'.lattice ↔ (z ∈ L.lattice ∨ z - t ∈ L.lattice)) (ht : t ∉ L.lattice)
    (k : ℕ) (hk : 2 < k) :
    L'.G k = L.G k + L.sumInvPow t k := by
  set f : ℂ → ℂ := fun z => (z ^ k)⁻¹ with hf
  set A : Set ℂ := (L.lattice : Set ℂ) with hA
  set B : Set ℂ := {z | z - t ∈ L.lattice} with hB
  have hAs : HasSum (f ∘ (Subtype.val : A → ℂ)) (L.G k) := by
    have := L.hasSum_sumInvPow 0 hk
    simp only [sub_zero, PeriodPair.sumInvPow_zero] at this
    exact this
  let e : L.lattice ≃ B :=
    { toFun := fun l => ⟨l.1 - t, by
        show l.1 - t - t ∈ L.lattice
        have := L.lattice.sub_mem l.2 h2t
        rwa [show l.1 - 2 * t = l.1 - t - t by ring] at this⟩
      invFun := fun z => ⟨z.1 + t, by
        have h1 : z.1 - t ∈ L.lattice := z.2
        have := L.lattice.add_mem h1 h2t
        rwa [show z.1 - t + 2 * t = z.1 + t by ring] at this⟩
      left_inv := fun l => by ext; simp
      right_inv := fun z => by ext; simp }
  have hBs : HasSum (f ∘ (Subtype.val : B → ℂ)) (L.sumInvPow t k) := by
    rw [← e.hasSum_iff]
    have := L.hasSum_sumInvPow t hk
    convert this using 1
    funext l; rfl
  have hdis : Disjoint A B := by
    rw [Set.disjoint_left]
    intro z hzA hzB
    apply ht
    have := L.lattice.sub_mem hzA hzB
    simpa using this
  have hU := hAs.add_disjoint hdis hBs
  have hset : (L'.lattice : Set ℂ) = A ∪ B := by
    ext z
    simp only [Set.mem_union, A, B, Set.mem_ofPred_eq, SetLike.mem_coe]
    exact hL' z
  rw [hasSum_subtype_iff_indicator, ← hset, ← hasSum_subtype_iff_indicator] at hU
  exact hU.tsum_eq

/- English proof (translation)
Establish `hd : DifferentiableAt ℂ L.weierstrassP z` using `(L.analyticOnNhd_weierstrassP z hz).differentiableAt`. Use `hd.hasDerivAt` as an intermediate fact. Rewrite `this` using `[L.deriv_weierstrassP]`. Then use the resulting hypothesis.
-/
lemma hasDerivAt_P (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    HasDerivAt L.weierstrassP (L.derivWeierstrassP z) z := by
  have hd : DifferentiableAt ℂ L.weierstrassP z :=
    (L.analyticOnNhd_weierstrassP z hz).differentiableAt
  have := hd.hasDerivAt
  rwa [L.deriv_weierstrassP] at this

/- English proof (translation)
The claim follows from `(Formalism.L2.Th1.F.pSecond L z hz).deriv`.
-/
lemma deriv_two (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv L.derivWeierstrassP z = 6 * L.weierstrassP z ^ 2 - L.g₂ / 2 :=
  (Formalism.L2.Th1.F.pSecond L z hz).deriv

/- English proof (translation)
Establish `hev : deriv L.derivWeierstrassP =ᶠ[𝓝 z] fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2` using `by filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using deriv_two L hw`. Rewrite using `[hev.deriv_eq]`. Establish `hP` using `hasDerivAt_P L hz`. Establish `h2 : HasDerivAt (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) (12 * L.weierstrassP z * L.derivWeierstrassP z) z`. Use `((hP.mul hP).const_mul 6).sub_const (L.g₂ / 2)` as an intermediate fact.

Establish `hfun : (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) = fun x => 6 * (L.weierstrassP * L.weierstrassP) x - L.g₂ / 2`. Use function extensionality and compare the values at `w`. Rewrite using `[Pi.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hfun]`.

Conclude with `this.congr_deriv (by ring)`. Conclude with `h2.deriv`.
-/
lemma deriv_three (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv L.derivWeierstrassP) z = 12 * L.weierstrassP z * L.derivWeierstrassP z := by
  have hev : deriv L.derivWeierstrassP =ᶠ[𝓝 z] fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2 := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using deriv_two L hw
  rw [hev.deriv_eq]
  have hP := hasDerivAt_P L hz
  have h2 : HasDerivAt (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2)
      (12 * L.weierstrassP z * L.derivWeierstrassP z) z := by
    have := ((hP.mul hP).const_mul 6).sub_const (L.g₂ / 2)
    have hfun : (fun w => 6 * L.weierstrassP w ^ 2 - L.g₂ / 2) =
        fun x => 6 * (L.weierstrassP * L.weierstrassP) x - L.g₂ / 2 := by
      funext w; rw [Pi.mul_apply]; ring
    rw [hfun]
    exact this.congr_deriv (by ring)
  exact h2.deriv

/- English proof (translation)
Establish `hev : deriv (deriv L.derivWeierstrassP) =ᶠ[𝓝 z] fun w => 12 * L.weierstrassP w * L.derivWeierstrassP w` using `by filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using deriv_three L hw`. Rewrite using `[hev.deriv_eq]`. Establish `hP` using `hasDerivAt_P L hz`. Establish `hQ` using `Formalism.L2.Th1.F.pSecond L z hz`. Establish `h2` using `(hP.const_mul 12).mul hQ`.

Establish `hfun : (fun w => 12 * L.weierstrassP w * L.derivWeierstrassP w) = (fun y => 12 * L.weierstrassP y) * L.derivWeierstrassP`. Use function extensionality and compare the values at `w`. Both sides reduce to the same expression. Rewrite using `[hfun, h2.deriv]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma deriv_four (L : PeriodPair) {z : ℂ} (hz : z ∉ L.lattice) :
    deriv (deriv (deriv L.derivWeierstrassP)) z =
      12 * L.derivWeierstrassP z ^ 2 + 12 * L.weierstrassP z * (6 * L.weierstrassP z ^ 2 - L.g₂ / 2) := by
  have hev : deriv (deriv L.derivWeierstrassP) =ᶠ[𝓝 z]
      fun w => 12 * L.weierstrassP w * L.derivWeierstrassP w := by
    filter_upwards [L.isClosed_lattice.isOpen_compl.mem_nhds hz] with w hw using deriv_three L hw
  rw [hev.deriv_eq]
  have hP := hasDerivAt_P L hz
  have hQ := Formalism.L2.Th1.F.pSecond L z hz
  have h2 := (hP.const_mul 12).mul hQ
  have hfun : (fun w => 12 * L.weierstrassP w * L.derivWeierstrassP w) =
      (fun y => 12 * L.weierstrassP y) * L.derivWeierstrassP := by
    funext w; rfl
  rw [hfun, h2.deriv]
  ring

/- English proof (translation)
Establish `h` using `L.iteratedDeriv_weierstrassPExcept_self t (n := 2)`. Rewrite `h` using `[L.weierstrassPExcept_of_notMem t ht]`. Establish `h2 : iteratedDeriv 2 L.weierstrassP t = deriv L.derivWeierstrassP t`. Rewrite using `[show (2 : ℕ) = 0 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP]`. Rewrite `h` using `[h2, deriv_two L ht]`.

Evaluate the numerical expressions using `[Nat.factorial] at h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sumInvPow_four (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    L.sumInvPow t 4 = (6 * L.weierstrassP t ^ 2 - L.g₂ / 2) / 6 := by
  have h := L.iteratedDeriv_weierstrassPExcept_self t (n := 2)
  rw [L.weierstrassPExcept_of_notMem t ht] at h
  have h2 : iteratedDeriv 2 L.weierstrassP t = deriv L.derivWeierstrassP t := by
    rw [show (2 : ℕ) = 0 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_zero, L.deriv_weierstrassP]
  rw [h2, deriv_two L ht] at h
  norm_num [Nat.factorial] at h
  rw [h]; ring

/- English proof (translation)
Establish `h` using `L.iteratedDeriv_weierstrassPExcept_self t (n := 4)`. Rewrite `h` using `[L.weierstrassPExcept_of_notMem t ht]`. Establish `h2 : iteratedDeriv 4 L.weierstrassP t = deriv (deriv (deriv L.derivWeierstrassP)) t`. Rewrite using `[show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP]`. Rewrite `h` using `[h2, deriv_four L ht]`.

Evaluate the numerical expressions using `[Nat.factorial] at h`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma sumInvPow_six (L : PeriodPair) {t : ℂ} (ht : t ∉ L.lattice) :
    L.sumInvPow t 6 = (12 * L.derivWeierstrassP t ^ 2
      + 12 * L.weierstrassP t * (6 * L.weierstrassP t ^ 2 - L.g₂ / 2)) / 120 := by
  have h := L.iteratedDeriv_weierstrassPExcept_self t (n := 4)
  rw [L.weierstrassPExcept_of_notMem t ht] at h
  have h2 : iteratedDeriv 4 L.weierstrassP t = deriv (deriv (deriv L.derivWeierstrassP)) t := by
    rw [show (4 : ℕ) = 0 + 1 + 1 + 1 + 1 from rfl, iteratedDeriv_succ, iteratedDeriv_succ,
      iteratedDeriv_succ, iteratedDeriv_succ, iteratedDeriv_zero, L.deriv_weierstrassP]
  rw [h2, deriv_four L ht] at h
  norm_num [Nat.factorial] at h
  rw [h]; ring

/- English proof (translation)
Establish `hr : 1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2) * ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) * (g2 ^ 3 - 27 * g3 ^ 2) ^ 2 = 1728 * g2 ^ 3 * ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) * (g2 ^ 3 - 27 * g3 ^ 2)`. Clear the denominators using the available nonvanishing facts. Rewrite using `[hr]`. Substitute `h` using the available equality. Expand and normalize the polynomial expressions, which then agree.
-/
lemma alg (e g2 g3 : ℂ) (h : g3 = 4 * e ^ 3 - g2 * e) (hd : g2 ^ 3 - 27 * g3 ^ 2 ≠ 0) :
    ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2
      + 16 * (g2 ^ 3 - 27 * g3 ^ 2)) ^ 3 =
    1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2) *
      ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) *
      (g2 ^ 3 - 27 * g3 ^ 2) ^ 2 := by
  have hr : 1728 * g2 ^ 3 / (g2 ^ 3 - 27 * g3 ^ 2) *
      ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) *
      (g2 ^ 3 - 27 * g3 ^ 2) ^ 2 = 1728 * g2 ^ 3 *
      ((60 * e ^ 2 - 4 * g2) ^ 3 - 27 * (g3 + 84 * e ^ 3 - 7 * g2 * e) ^ 2) *
      (g2 ^ 3 - 27 * g3 ^ 2) := by
    field_simp
  rw [hr]
  subst h
  ring

end IsogenyReduction

open IsogenyReduction

/- English proof (translation)
Introduce and unpack `L L' ⟨t, ht, h2t, hL'⟩`. Establish `hG4` using `G_split L L' t h2t hL' ht 4 (by norm_num)`. Establish `hG6` using `G_split L L' t h2t hL' ht 6 (by norm_num)`. Establish `hp' : L.derivWeierstrassP t = 0`. Establish `h1 : L.derivWeierstrassP (t - 2 * t) = L.derivWeierstrassP t` using `L.derivWeierstrassP_sub_coe t ⟨2 * t, h2t⟩`.

Rewrite `h1` using `[show t - 2 * t = -t by ring, L.derivWeierstrassP_neg]`. Take the linear combination `(-1 / 2 : ℂ) * h1`. Establish `hrel` using `L.derivWeierstrassP_sq t ht`. Rewrite `hrel` using `[hp']`. Establish `hS4` using `sumInvPow_four L ht`.

Establish `hS6` using `sumInvPow_six L ht`. Rewrite `hS6` using `[hp']`. Use `set e := L.weierstrassP t with he`. Establish `hg2 : L.g₂ = 60 * L.G 4` using `rfl`. Establish `hg3 : L.g₃ = 140 * L.G 6` using `rfl`.

Establish `hg2' : L'.g₂ = 60 * e ^ 2 - 4 * L.g₂` using `by show 60 * L'.G 4 = _`. Rewrite using `[hG4, hS4, hg2]`. Expand and normalize the polynomial expressions, which then agree. Establish `hg3' : L'.g₃ = L.g₃ + 84 * e ^ 3 - 7 * L.g₂ * e` using `by show 140 * L'.G 6 = _`. Rewrite using `[hG6, hS6, hg3, hg2]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hd` using `Formalism.L2.Th1.F.discNeZero L`. Simplify using `only [disc, Formalism.L2.Th1.CM.jInv]`. Rewrite using `[hg2', hg3']`. Conclude with `alg e L.g₂ L.g₃ (by linear_combination hrel) hd`.
-/
theorem twoIsogeny_discriminant_ratio_cubic : TwoIsog := by
  rintro L L' ⟨t, ht, h2t, hL'⟩
  have hG4 := G_split L L' t h2t hL' ht 4 (by norm_num)
  have hG6 := G_split L L' t h2t hL' ht 6 (by norm_num)
  have hp' : L.derivWeierstrassP t = 0 := by
    have h1 : L.derivWeierstrassP (t - 2 * t) = L.derivWeierstrassP t :=
      L.derivWeierstrassP_sub_coe t ⟨2 * t, h2t⟩
    rw [show t - 2 * t = -t by ring, L.derivWeierstrassP_neg] at h1
    linear_combination (-1 / 2 : ℂ) * h1
  have hrel := L.derivWeierstrassP_sq t ht
  rw [hp'] at hrel
  have hS4 := sumInvPow_four L ht
  have hS6 := sumInvPow_six L ht
  rw [hp'] at hS6
  set e := L.weierstrassP t with he
  have hg2 : L.g₂ = 60 * L.G 4 := rfl
  have hg3 : L.g₃ = 140 * L.G 6 := rfl
  have hg2' : L'.g₂ = 60 * e ^ 2 - 4 * L.g₂ := by
    show 60 * L'.G 4 = _
    rw [hG4, hS4, hg2]; ring
  have hg3' : L'.g₃ = L.g₃ + 84 * e ^ 3 - 7 * L.g₂ * e := by
    show 140 * L'.G 6 = _
    rw [hG6, hS6, hg3, hg2]; ring
  have hd := Formalism.L2.Th1.F.discNeZero L
  simp only [disc, Formalism.L2.Th1.CM.jInv]
  rw [hg2', hg3']
  exact alg e L.g₂ L.g₃ (by linear_combination hrel) hd

end

section

open Formalism.L2.Th1.CM (omegaK)

/- English proof (translation)
Establish `h` using `PadicComplex.norm_extends' (p := 2) ((2 : ℕ) : ℚ_[2])`. Establish `h2 : (((2 : ℕ) : ℚ_[2]) : ℂ_[2]) = 2`. Rewrite using `[map_natCast, PadicComplex.coe_natCast]`. Evaluate the numerical expressions. Rewrite `h` using `[h2]`.

Rewrite using `[h]`. Conclude with `Padic.norm_p_lt_one`.
-/
theorem norm_two_lt_one : ‖(2 : ℂ_[2])‖ < 1 := by
  have h := PadicComplex.norm_extends' (p := 2) ((2 : ℕ) : ℚ_[2])
  have h2 : (((2 : ℕ) : ℚ_[2]) : ℂ_[2]) = 2 := by
    rw [map_natCast, PadicComplex.coe_natCast]; norm_num
  rw [h2] at h
  rw [h]
  exact Padic.norm_p_lt_one

/- English proof (translation)
Take `⟨k, rfl⟩` from `hn`. Establish `hk : ‖(2 : ℂ_[2]) * (k : ℂ_[2])‖ < 1`. Rewrite using `[norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `e : ((2 * k + 1 : ℤ) : ℂ_[2]) = 2 * (k : ℂ_[2]) + 1` using `by push_cast; ring`.

Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hk.ne)]`. Rewrite using `[norm_one]`. Conclude with `max_eq_right hk.le`.
-/
theorem norm_odd_eq_one (n : ℤ) (hn : Odd n) : ‖(n : ℂ_[2])‖ = 1 := by
  obtain ⟨k, rfl⟩ := hn
  have hk : ‖(2 : ℂ_[2]) * (k : ℂ_[2])‖ < 1 := by
    rw [norm_mul]
    calc ‖(2 : ℂ_[2])‖ * ‖(k : ℂ_[2])‖ ≤ ‖(2 : ℂ_[2])‖ * 1 :=
          mul_le_mul_of_nonneg_left (IsUltrametricDist.norm_intCast_le_one ℂ_[2] k) (norm_nonneg _)
      _ < 1 := by rw [mul_one]; exact norm_two_lt_one
  have e : ((2 * k + 1 : ℤ) : ℂ_[2]) = 2 * (k : ℂ_[2]) + 1 := by push_cast; ring
  rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_one]; exact hk.ne)]
  rw [norm_one]; exact max_eq_right hk.le

/- English proof (translation)
Simplify using `only [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem omegaK_add_conj (d : ℕ) : omegaK d + conj (omegaK d) = 1 := by
  simp only [omegaK, map_div₀, map_add, map_one, map_mul, Complex.conj_I, Complex.conj_ofReal, map_ofNat]
  ring

/- English proof (translation)
Establish `hs2 : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d`. Rewrite using `[← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]`. Use `push_cast`. Both sides reduce to the same expression. Unfold `omegaK`.

Take the linear combination `((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs2`.
-/
theorem omegaK_sq_four (d : ℕ) : 4 * omegaK d ^ 2 = 4 * omegaK d - (1 + d) := by
  have hs2 : ((Real.sqrt d : ℝ) : ℂ) ^ 2 = d := by
    rw [← Complex.ofReal_pow, Real.sq_sqrt (Nat.cast_nonneg _)]; push_cast; rfl
  unfold omegaK
  linear_combination ((Real.sqrt d : ℝ) : ℂ) ^ 2 * Complex.I_sq - hs2

/- English proof (translation)
Introduce `d hd h x y hh hy hxy ι`. Use `set q := (d + 1) / 4 with hqdef`. Use `set ω := omegaK d with hωdef`. Establish `hs` using `omegaK_add_conj d`. Establish `hc : conj ω = 1 - ω` using `by linear_combination hs`.

Establish `hsq : 4 * ω ^ 2 = 4 * ω - (1 + d)` using `omegaK_sq_four d`. Establish `hq4 : 4 * (q : ℂ) = 1 + d`. Establish `h4 : 4 * q = d + 1` using `by omega`. Use `congrArg (Nat.cast (R := ℂ)) h4` as an intermediate fact. Rewrite `this` using `[Nat.cast_mul, Nat.cast_add]`.

Move the coercions through the operations in `at this`. Take the linear combination `this`. Use `set a := ι ((x : ℂ) + (y : ℂ) * ω) with ha_def`. Use `set b := ι ((x : ℂ) + (y : ℂ) * conj ω) with hb_def`. Establish `hsum : a + b = ((2 * x + y : ℤ) : ℂ_[2])`.

Rewrite using `[ha_def, hb_def, ← map_add, hc, show ((x : ℂ) + y * ω + (x + y * (1 - ω))) = ((2 * x + y : ℤ) : ℂ) by push_cast; ring]`. Conclude with `map_intCast ι _`. Establish `hprod : a * b = 2 ^ h`. Establish `hx` using `congrArg (Int.cast (R := ℂ)) hxy`. Move the coercions through the operations in `at hx`.

Rewrite using `[ha_def, hb_def, ← map_mul, show ((x : ℂ) + y * ω) * (x + y * conj ω) = 2 ^ h by`. Rewrite using `[hc]`. Take the linear combination `hx + (-(y : ℂ) ^ 2 / 4) * hsq + (-(y : ℂ) ^ 2 / 4) * hq4]`. Rewrite using `[map_pow, map_ofNat]`. Establish `hodd : Odd (2 * x + y)`.

Break down `hy with ⟨k, rfl⟩; exact ⟨x + k, by ring⟩` into its components or cases. Establish `hn1 : ‖a + b‖ = 1` using `by rw [hsum]; exact norm_odd_eq_one _ hodd`. Establish `hlt : ‖a‖ * ‖b‖ < 1`. Rewrite using `[← norm_mul, hprod, norm_pow]`. Conclude with `pow_lt_one₀ (norm_nonneg _) norm_two_lt_one hh.ne'`.

Distinguish the cases in `ha : ‖a‖ < 1`. Use `⟨(x : ℂ) + y * conj ω, Or.inr rfl, ?_⟩ show ‖b‖ = 1` and prove the remaining obligations. Establish `e : b = (a + b) + (-a)` using `by ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, hn1]; exact ha.ne'), norm_neg, hn1]`. Conclude with `max_eq_left ha.le`.

Establish `hb : ‖b‖ < 1`. Establish `ha'` using `not_lt.mp ha`. Use polynomial arithmetic with `[norm_nonneg b]`. Use `⟨(x : ℂ) + y * ω, Or.inl rfl, ?_⟩` and prove the remaining obligations. Use `show ‖a‖ = 1`.

Establish `e : a = (a + b) + (-b)` using `by ring`. Rewrite using `[e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, hn1]; exact hb.ne'), norm_neg, hn1]`. Conclude with `max_eq_left hb.le`.
-/
theorem exists_unit_conjugate_norm_two_power_two_adic : UnitChoice := by
  intro d hd h x y hh hy hxy ι
  set q := (d + 1) / 4 with hqdef
  set ω := omegaK d with hωdef
  have hs := omegaK_add_conj d
  have hc : conj ω = 1 - ω := by linear_combination hs
  have hsq : 4 * ω ^ 2 = 4 * ω - (1 + d) := omegaK_sq_four d
  have hq4 : 4 * (q : ℂ) = 1 + d := by
    have h4 : 4 * q = d + 1 := by omega
    have := congrArg (Nat.cast (R := ℂ)) h4
    rw [Nat.cast_mul, Nat.cast_add] at this
    push_cast at this
    linear_combination this
  set a := ι ((x : ℂ) + (y : ℂ) * ω) with ha_def
  set b := ι ((x : ℂ) + (y : ℂ) * conj ω) with hb_def
  have hsum : a + b = ((2 * x + y : ℤ) : ℂ_[2]) := by
    rw [ha_def, hb_def, ← map_add, hc,
      show ((x : ℂ) + y * ω + (x + y * (1 - ω))) = ((2 * x + y : ℤ) : ℂ) by push_cast; ring]
    exact map_intCast ι _
  have hprod : a * b = 2 ^ h := by
    have hx := congrArg (Int.cast (R := ℂ)) hxy
    push_cast at hx
    rw [ha_def, hb_def, ← map_mul,
      show ((x : ℂ) + y * ω) * (x + y * conj ω) = 2 ^ h by
        rw [hc]
        linear_combination hx + (-(y : ℂ) ^ 2 / 4) * hsq + (-(y : ℂ) ^ 2 / 4) * hq4]
    rw [map_pow, map_ofNat]
  have hodd : Odd (2 * x + y) := by
    rcases hy with ⟨k, rfl⟩; exact ⟨x + k, by ring⟩
  have hn1 : ‖a + b‖ = 1 := by rw [hsum]; exact norm_odd_eq_one _ hodd
  have hlt : ‖a‖ * ‖b‖ < 1 := by
    rw [← norm_mul, hprod, norm_pow]
    exact pow_lt_one₀ (norm_nonneg _) norm_two_lt_one hh.ne'
  by_cases ha : ‖a‖ < 1
  · refine ⟨(x : ℂ) + y * conj ω, Or.inr rfl, ?_⟩
    show ‖b‖ = 1
    have e : b = (a + b) + (-a) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, hn1]; exact ha.ne'),
      norm_neg, hn1]
    exact max_eq_left ha.le
  · have hb : ‖b‖ < 1 := by
      have ha' := not_lt.mp ha; nlinarith [norm_nonneg b]
    refine ⟨(x : ℂ) + y * ω, Or.inl rfl, ?_⟩
    show ‖a‖ = 1
    have e : a = (a + b) + (-b) := by ring
    rw [e, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm (by rw [norm_neg, hn1]; exact hb.ne'),
      norm_neg, hn1]
    exact max_eq_left hb.le

end

section

/- English proof (translation)
The claim follows from `full_of_open twoIsogeny_discriminant_ratio_cubic hN hC exists_unit_conjugate_norm_two_power_two_adic`.
-/
theorem full_of_normPow_chain (hN : NormPow) (hC : Chain) : Full :=
  full_of_open twoIsogeny_discriminant_ratio_cubic hN hC exists_unit_conjugate_norm_two_power_two_adic

end

section

/- English proof (translation)
Introduce `d L hd hL h x y hy hN π hπ`. Break down `hπ with hπ | hπ` into its components or cases. Conclude with `ChainBetweenPairs.chain_core d L hd hL h x y hy hN π hπ`. Use `ChainBetweenPairs.chain_core d L hd hL h (x + y) (-y) hy.neg (by rw [← hN]; ring) π ?_` and prove the remaining obligations. Rewrite using `[hπ, ChainBetweenPairs.conj_omega]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem stable_lattice_chain_successive_index_two : Chain := by
  intro d L hd hL h x y hy hN π hπ
  rcases hπ with hπ | hπ
  · exact ChainBetweenPairs.chain_core d L hd hL h x y hy hN π hπ
  · refine ChainBetweenPairs.chain_core d L hd hL h (x + y) (-y) hy.neg (by rw [← hN]; ring) π ?_
    rw [hπ, ChainBetweenPairs.conj_omega]
    push_cast
    ring

end

section

/- English proof (translation)
The claim follows from `full_of_normPow_chain hN stable_lattice_chain_successive_index_two`.
-/
theorem full_of_normPow (hN : NormPow) : Full :=
  full_of_normPow_chain hN stable_lattice_chain_successive_index_two

end

section

/- English proof (translation)
Introduce `d hd h7` and use `AlgebraicValuationTrichotomy.exists_norm_eq_two_pow d hd h7`.
-/
theorem isPrincipal_pow_prime_over_two : NormPow := fun d hd h7 => AlgebraicValuationTrichotomy.exists_norm_eq_two_pow d hd h7

end

/- English proof (translation)
The claim follows from `full_of_normPow isPrincipal_pow_prime_over_two`.
-/
theorem goodModelTwo : Formalism.L2.Th1.Top.GoodModelTwo := full_of_normPow isPrincipal_pow_prime_over_two

end GlobalTheory.ThLoc.GoodTwo
