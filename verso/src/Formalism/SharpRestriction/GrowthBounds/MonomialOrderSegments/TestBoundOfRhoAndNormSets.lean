import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.CgeZeroIffIntegral
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.ProjKeepsLetter
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.AddMemSupportOfMemSupportCoefOut
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.DigitPartMonomial

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

namespace TwistData

variable {K : Type} [Field K] (D : TwistData K)

/- English proof (translation)
Unfold `abelian₂`. Simplify using `only [gaAct_eq_dg, map_sub, fock_sub_right]`.
-/
theorem Lam_sub (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (Z W : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (Z - W) = D.abelian₂ p F Z - D.abelian₂ p F W := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_sub, fock_sub_right]

/- English proof (translation)
Unfold `abelian₂`. Simplify using `only [gaAct_eq_dg, map_smul, fock_smul_right]`.
-/
theorem Lam_smul (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (a : K) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.abelian₂ p F (a • Z) = a * D.abelian₂ p F Z := by
  unfold abelian₂; simp only [gaAct_eq_dg, map_smul, fock_smul_right]

/- English proof (translation)
Unfold `abelian₂`. Rewrite using `[ph_monomial, gaAct_eq_dg, dg_monomial, fock_monomial_right]`.
-/
theorem Lam_monomial (p : ℕ) (F : MvPolynomial (D.OL × Fin D.r) K) (ζ : D.EM) (c : K) :
    D.abelian₂ p F (monomial ζ c) =
      F.coeff (D.phE p ζ) * (D.ga (D.phE p ζ) * c) * (fact (D.phE p ζ) : K) := by
  unfold abelian₂; rw [ph_monomial, gaAct_eq_dg, dg_monomial, fock_monomial_right]

/- English proof (translation)
Use `conv_lhs => rw [Z.as_sum]`. Rewrite using `[map_sum]`. Conclude with `Finset.sum_congr rfl fun ζ _ => D.ph_monomial p ζ _`.
-/
theorem ph_eq_sum (p : ℕ) (Z : MvPolynomial (D.ML × Fin D.r) K) :
    D.ph p Z = ∑ ζ ∈ Z.support, monomial (D.phE p ζ) (Z.coeff ζ) := by
  conv_lhs => rw [Z.as_sum]
  rw [map_sum]
  exact Finset.sum_congr rfl fun ζ _ => D.ph_monomial p ζ _

/- English proof (translation)
Rewrite using `[mem_PolK_iff]`. Introduce `β hβ`. Use `support_monomial_subset hβ` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`. Rewrite using `[this]`.

Conclude with `h`.
-/
theorem monomial_mem_PolK {L : Type} {r : ℕ} (d : L → ℕ) (α : L × Fin r →₀ ℕ) (c : K)
    (h : ∀ i, ldeg α i = d i) : monomial α c ∈ PolK K r d := by
  classical
  rw [mem_PolK_iff]
  intro β hβ
  have := support_monomial_subset hβ
  rw [Finset.mem_singleton] at this
  rw [this]; exact h

/- English proof (translation)
Rewrite using `[ph_eq_sum]`. Conclude with `Submodule.sum_mem _ fun ζ hζ => monomial_mem_PolK _ _ _ (D.ldeg_phE p ζ (hZ ζ hζ))`.
-/
theorem ph_mem_PolK (p : ℕ) {Z : MvPolynomial (D.ML × Fin D.r) K} (hZ : D.Good p Z) :
    D.ph p Z ∈ PolK K D.r D.dO := by
  rw [ph_eq_sum]
  exact Submodule.sum_mem _ fun ζ hζ => monomial_mem_PolK _ _ _ (D.ldeg_phE p ζ (hZ ζ hζ))

/- English proof (translation)
Rewrite using `[ph_eq_sum]`. Conclude with `cge_sum v _ _ fun ζ _ => cge_monomial v _ (hZ ζ)`.
-/
theorem cge_ph (v : AddValuation K (WithTop ℚ)) (p : ℕ) {a : ℝ} {Z : MvPolynomial (D.ML × Fin D.r) K}
    (hZ : cge v a Z) : cge v a (D.ph p Z) := by
  rw [ph_eq_sum]
  exact cge_sum v _ _ fun ζ _ => cge_monomial v _ (hZ ζ)

/- English proof (translation)
Unfold `eC`. Use `lg_ge_one hp hr (2 * D.totDeg)` as an intermediate fact. Check the signs of the components of the expression.
-/
theorem eC_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.eC p C0 := by
  unfold eC
  have := lg_ge_one hp hr (2 * D.totDeg)
  positivity

/- English proof (translation)
Unfold `Dm`. Use `D.eC_nonneg hp hr h1` as an intermediate fact. Conclude with `Finset.sum_nonneg fun j _ => by positivity`.
-/
theorem Dm_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dm p C0 := by
  unfold Dm
  have := D.eC_nonneg hp hr h1
  exact Finset.sum_nonneg fun j _ => by positivity

/- English proof (translation)
Unfold `Dl`. Use `D.eC_nonneg hp hr h1` as an intermediate fact. Establish `h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1`. Establish `: (1 : ℝ) ≤ D.r` using `by exact_mod_cast hr`. Combine the linear equalities and inequalities to obtain the conclusion.

Check the signs of the components of the expression.
-/
theorem Dl_nonneg {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) {C0 : ℝ} (h1 : 1 ≤ C0) : 0 ≤ D.Dl p C0 := by
  unfold Dl
  have := D.eC_nonneg hp hr h1
  have h2 : (0 : ℝ) ≤ (D.r : ℝ) - 1 := by
    have : (1 : ℝ) ≤ D.r := by exact_mod_cast hr
    linarith
  positivity

/- English proof (translation)
Unfold `kapD`. Use `le_trans ?_ (kap_ge_card hp hr D.dO)` and prove the remaining obligations. Establish `h1 : 1 ≤ Fintype.card D.OL`. Rewrite using `[Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]`. Establish `: 1 ≤ D.J * D.r` using `Nat.mul_pos hJ hr`.

Use linear arithmetic over natural numbers and integers. Establish `h2 : (1 : ℝ) ≤ (Fintype.card D.OL : ℝ)` using `by exact_mod_cast h1`. Establish `h3 : (1 : ℝ) ≤ (D.r : ℝ)` using `by exact_mod_cast hr`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem kapD_ge_one {p : ℕ} (hp : 2 ≤ p) (hr : 1 ≤ D.r) (hJ : 1 ≤ D.J) : 1 ≤ D.kapD p := by
  unfold kapD
  refine le_trans ?_ (kap_ge_card hp hr D.dO)
  have h1 : 1 ≤ Fintype.card D.OL := by
    rw [Fintype.card_sum, Fintype.card_prod, Fintype.card_fin, Fintype.card_fin]
    have : 1 ≤ D.J * D.r := Nat.mul_pos hJ hr
    omega
  have h2 : (1 : ℝ) ≤ (Fintype.card D.OL : ℝ) := by exact_mod_cast h1
  have h3 : (1 : ℝ) ≤ (D.r : ℝ) := by exact_mod_cast hr
  nlinarith

end TwistData

section Top

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

/- English proof (translation)
Introduce `hD D hV hc F hF hF0`. Take `⟨Gt, hGt, hval, hle⟩` from `hB hD D hV hc F hF hF0`. Take `⟨Z, hZi, hZg, hZph, hZv⟩` from `hC hD D hV.1 hV.2.1 (fun j m => D.thl j m - 6 * D.c) Gt hGt hval`. Use `⟨Z, hZi, hZg, hZv, ?_⟩` and prove the remaining obligations. Unfold `TwistData.abelian₂`.

Rewrite using `[hZph]`. Conclude with `hle`.
-/
theorem stepBC_of (hB : StepB K v p C0) (hC : StepC K v p) : StepBC K v p C0 := by
  intro hD D hV hc F hF hF0
  obtain ⟨Gt, hGt, hval, hle⟩ := hB hD D hV hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZph, hZv⟩ := hC hD D hV.1 hV.2.1 (fun j m => D.thl j m - 6 * D.c) Gt hGt hval
  refine ⟨Z, hZi, hZg, hZv, ?_⟩
  unfold TwistData.abelian₂
  rw [hZph]; exact hle

/- English proof (translation)
Introduce `hD D hV hH hc F hF hF0`. Take `⟨Z, hZi, hZg, hZy, hZl⟩` from `hBC hD D hV hc F hF hF0`. Take `⟨Om, N2, hN2, hOi, hOg, hOc, hOy, hOl⟩` from `hDEF hD D hV hH hc F hF hF0`. Establish `hp : 2 ≤ p` using `two_le_p hD`. Establish `hr : 1 ≤ D.r` using `hV.1`.

Establish `hJ : 1 ≤ D.J` using `hV.2.1`. Establish `hkap` using `D.kapD_ge_one hp hr hJ`. Establish `hDm` using `D.Dm_nonneg hp hr h1`. Establish `hDl` using `D.Dl_nonneg hp hr h1`. Establish `hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c` using `hc`.

Establish `hG : D.Good p (((p : K) ^ N2) • Om Z)` using `TwistData.Good.smul D (hOg Z hZg) _`. Establish `hGi : Integral v (((p : K) ^ N2) • Om Z)` using `hOi Z hZi hZg`. Use `⟨((p : K) ^ N2) • Om Z, 0, ⟨⟨hGi, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `α hα j m hm a`. Conclude with `(hG α hα).2.1 j m hm a`.

Introduce `j i`. Conclude with `vala_smul _ (hOc Z hZg j i)`. Introduce `j m hm`. Use `vala_smul ((p : K) ^ N2) (hOy Z hZg j m _ hm (hZy j m hm))` as an intermediate fact. Conclude with `vala_mono (by linarith) this`.

Introduce `α hα t a`. Conclude with `(hG α hα).1 t a`. Introduce `α hα`. Simplify using `at hα`. Introduce `α hα`.

Simplify using `at hα`. Introduce `α`. Simplify using `[vR]`. Introduce `α hα`. Conclude with `⟨(hG α hα).2.2.1, fun t => by`.

Use `(hG α hα).2.2.2.1 t` as an intermediate fact. Simplify using `only [ldeg] at this`. Rewrite using `[Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]`. Conclude with `this⟩`. Introduce `α hα`.

Simplify using `at hα`. Rewrite using `[add_zero, ← bge_iff]`. Establish `h2` using `bge_of_cge hD (D.ph_mem_PolK p hG) (D.cge_ph v p ((cge_zero_iff_Integral v _).mpr hGi))`. Use `bge_mono v ?_ h2` and prove the remaining obligations. Establish `h3` using `kapL_le_kap' hp hr D.dO`.

Establish `h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2` using `rfl`. Establish `h5 : D.kapD p = kap p D.r D.dO` using `rfl`. Rewrite using `[h4, h5]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[add_zero]`.

Establish `e1 : fock F (D.gaAct (D.ph p (((p : K) ^ N2) • Om Z))) = (p : K) ^ N2 * D.abelian₂ p F (Om Z)` using `D.Lam_smul p F _ _`. Establish `e2 : D.abelian₂ p F (Om Z) = D.abelian₂ p F Z + (D.abelian₂ p F (Om Z) - D.abelian₂ p F Z)` using `by ring`. Establish `h6 : vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F (Om Z))`. Rewrite using `[e2]`. Conclude with `vle_add_of_lt v hZl (hOl Z hZi hZg) (by linarith)`.

Establish `h7` using `vle_pow_p hD N2 h6`. Rewrite using `[e1]`. Establish `h8 : vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ)` using `h7`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← WithTop.coe_add]`.

Use `_ ≤ ((D.E p C0 2 + 2 * D.kapD p : ℝ) : WithTop ℝ) := by`. Rewrite using `[WithTop.coe_le_coe]`. Unfold `TwistData.E`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem plane_gram_theorem_of_combined_lemmas (h1 : 1 ≤ C0) (hBC : StepBC K v p C0) (hDEF : StepDEF K v p C0) :
    LiftBoundUniform K v p C0 := by
  intro hD D hV hH hc F hF hF0
  obtain ⟨Z, hZi, hZg, hZy, hZl⟩ := hBC hD D hV hc F hF hF0
  obtain ⟨Om, N2, hN2, hOi, hOg, hOc, hOy, hOl⟩ := hDEF hD D hV hH hc F hF hF0
  have hp : 2 ≤ p := two_le_p hD
  have hr : 1 ≤ D.r := hV.1
  have hJ : 1 ≤ D.J := hV.2.1
  have hkap := D.kapD_ge_one hp hr hJ
  have hDm := D.Dm_nonneg hp hr h1
  have hDl := D.Dl_nonneg hp hr h1
  have hcc : 4 * (D.Dm p C0 + D.Dl p C0 + 3 * D.kapD p) < D.c := hc
  have hG : D.Good p (((p : K) ^ N2) • Om Z) := TwistData.Good.smul D (hOg Z hZg) _
  have hGi : Integral v (((p : K) ^ N2) • Om Z) := hOi Z hZi hZg
  refine ⟨((p : K) ^ N2) • Om Z, 0, ⟨⟨hGi, ?_⟩, ?_, ?_⟩, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro α hα j m hm a
    exact (hG α hα).2.1 j m hm a
  · intro j i
    exact vala_smul _ (hOc Z hZg j i)
  · intro j m hm
    have := vala_smul ((p : K) ^ N2) (hOy Z hZg j m _ hm (hZy j m hm))
    exact vala_mono (by linarith) this
  · intro α hα t a
    exact (hG α hα).1 t a
  · intro α hα; simp at hα
  · intro α hα; simp at hα
  · intro α; simp [vR]
  · intro α hα
    exact ⟨(hG α hα).2.2.1, fun t => by
      have := (hG α hα).2.2.2.1 t
      simp only [ldeg] at this
      rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum]
      exact this⟩
  · intro α hα; simp at hα
  · rw [add_zero, ← bge_iff]
    have h2 := bge_of_cge hD (D.ph_mem_PolK p hG) (D.cge_ph v p ((cge_zero_iff_Integral v _).mpr hGi))
    refine bge_mono v ?_ h2
    have h3 := kapL_le_kap' hp hr D.dO
    have h4 : D.n0 v = vN v (∏ i : D.OL, (D.dO i).factorial) / 2 := rfl
    have h5 : D.kapD p = kap p D.r D.dO := rfl
    rw [h4, h5]; linarith
  · rw [add_zero]
    have e1 : fock F (D.gaAct (D.ph p (((p : K) ^ N2) • Om Z))) = (p : K) ^ N2 * D.abelian₂ p F (Om Z) :=
      D.Lam_smul p F _ _
    have e2 : D.abelian₂ p F (Om Z) = D.abelian₂ p F Z + (D.abelian₂ p F (Om Z) - D.abelian₂ p F Z) := by ring
    have h6 : vle v (D.n0 v + D.Dl p C0 + 1) (D.abelian₂ p F (Om Z)) := by
      rw [e2]
      exact vle_add_of_lt v hZl (hOl Z hZi hZg) (by linarith)
    have h7 := vle_pow_p hD N2 h6
    rw [e1]
    have h8 : vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) := h7
    calc vR v ((p : K) ^ N2 * D.abelian₂ p F (Om Z)) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ)
        ≤ ((D.n0 v + D.Dl p C0 + 1 + N2 : ℝ) : WithTop ℝ) + ((-D.n0 v + D.kapD p : ℝ) : WithTop ℝ) := by
          gcongr
      _ = ((D.n0 v + D.Dl p C0 + 1 + N2 + (-D.n0 v + D.kapD p) : ℝ) : WithTop ℝ) := by
          rw [← WithTop.coe_add]
      _ ≤ ((D.E p C0 2 + 2 * D.kapD p : ℝ) : WithTop ℝ) := by
          rw [WithTop.coe_le_coe]
          unfold TwistData.E
          linarith

end Top

end Formalism.MainNotions.PlaneGram
