import Mathlib
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.NefPsEffUpTo
import Development.AbelianVarietyTheory.Definitions.Divisors.LineBundleGlobalSectionsDimCongrPicardClass
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EventuallySubsingletonCohAmplePsEff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPowLeGlobalSectionsDimLineBundlePow
open CategoryTheory Limits AlgebraicGeometry TopologicalSpace Filter
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.QCoh GlobalTheory.CechPic GlobalTheory.Twist
open GlobalTheory.CompanionTheory.NefKleiman

set_option autoImplicit false
noncomputable section

namespace GlobalTheory.CompanionTheory.NefKleiman

/- English proof (translation)
Establish `hnd : q.natDegree = D` using `Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc.ne`. Break down `Nat.eq_zero_or_pos D with rfl | hD` into its components or cases. Use `Eventually.of_forall fun m => ?_` and prove the remaining obligations. Rewrite using `[Polynomial.eq_C_of_natDegree_eq_zero hnd, Polynomial.eval_C]`. Conclude with `hc`.

Establish `hlc : q.leadingCoeff ≤ 0`. Rewrite using `[Polynomial.leadingCoeff, hnd]`. Conclude with `hc.le`. Establish `hdg : 0 < q.degree`. Rewrite using `[Polynomial.degree_eq_natDegree (by rintro rfl; simp at hc), hnd]`.

Conclude with `hD` after adjusting the coercions. Establish `ht` using `(Polynomial.tendsto_atBot_of_leadingCoeff_nonpos q hdg hlc).comp tendsto_natCast_atTop_atTop`. Conclude with `ht.eventually (eventually_lt_atBot 0)`.
-/
theorem eventually_eval_neg_of_coeff_neg (q : Polynomial ℝ) (D : ℕ) (hdeg : q.natDegree ≤ D)
    (hc : q.coeff D < 0) : ∀ᶠ m : ℕ in atTop, q.eval (m : ℝ) < 0 := by
  have hnd : q.natDegree = D := Polynomial.natDegree_eq_of_le_of_coeff_ne_zero hdeg hc.ne
  rcases Nat.eq_zero_or_pos D with rfl | hD
  · refine Eventually.of_forall fun m => ?_
    rw [Polynomial.eq_C_of_natDegree_eq_zero hnd, Polynomial.eval_C]
    exact hc
  · have hlc : q.leadingCoeff ≤ 0 := by
      rw [Polynomial.leadingCoeff, hnd]; exact hc.le
    have hdg : 0 < q.degree := by
      rw [Polynomial.degree_eq_natDegree (by rintro rfl; simp at hc), hnd]
      exact_mod_cast hD
    have ht := (Polynomial.tendsto_atBot_of_leadingCoeff_nonpos q hdg hlc).comp
      tendsto_natCast_atTop_atTop
    exact ht.eventually (eventually_lt_atBot 0)

/- English proof (translation)
Introduce `k _ X _ _ hp n hd A hA`. Establish `hv` using `diffVanish_chiPic_of_isProjOver (d := n) (algebraMap_eq_strHom k X) (structureModule X) hp (by rw [suppDim_structureModule, hd])`. Take `⟨p, hdeg, heval, hcoeff⟩` from `hv.exists_polynomial_chi_twistZ ℝ hA.isLB`. Take `⟨D, hD, c, hc, hfreq⟩` from `(IsAmpleLB.isBig k X hp A hA).growth`. Establish `hDn : D = n`.

Rewrite `hD` using `[hd]`. Conclude with `hD.symm` after adjusting the coercions. Substitute `hDn` using the available equality. Establish `hser` using `eventually_subsingleton_coh_twistZ_of_isProjOver (algebraMap_eq_strHom k X) (structureModule X) hp hA`. Establish `hchi : ∀ᶠ m : ℕ in atTop, (lbH0 k (lbPow A m) : ℝ) = p.eval (m : ℝ)` using `by filter_upwards [tendsto_natCast_atTop_atTop.eventually hser] with m hm`.

Establish `h1` using `heval (m : ℤ)`. Establish `h2` using `chi_eq_hdim_zero k hm`. Move the coercions through the operations in `at h1`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.

Assume the negation of the conclusion as `hneg`. Use `push_neg at hneg`. Establish `hcD : p.coeff D ≤ 0`. Rewrite using `[hcoeff]`. Establish `: ((interNum k (structureModule X) fun _ : Fin D => A : ℤ) : ℝ) ≤ 0` using `by exact_mod_cast hneg`.

Conclude with `mul_nonpos_of_nonneg_of_nonpos (by positivity) this`. Establish `hq` using `eventually_eval_neg_of_coeff_neg (p - Polynomial.C c * Polynomial.X ^ D) D ((Polynomial.natDegree_sub_le _ _).trans (max_le hdeg ((Polynomial.natDegree_C_mul_X_pow_le c D)))) (by`. Rewrite using `[Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, if_pos rfl]`. Use the proof step `linarith)`. Take `⟨m, h1, h2, h3⟩` from `(hfreq.and_eventually (hchi.and hq)).exists`.

Rewrite `h3` using `[Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow, Polynomial.eval_X]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem interNum_top_pos_of_isAmpleLB : ∀ (k : Type) [Field k] (X : Scheme.{0}) [IsIntegral X]
    [Algebra k Γ(X, ⊤)] (hp : IsProjOver (strHom k X)) (n : ℕ)
    (hd : topologicalKrullDim X = (n : WithBot ℕ∞)) (A : LB X) (hA : IsAmpleLB A),
    0 < interNum k (GlobalTheory.structureModule X) (fun _ : Fin n => A) := by
  intro k _ X _ _ hp n hd A hA
  have hv := diffVanish_chiPic_of_isProjOver (d := n) (algebraMap_eq_strHom k X)
    (structureModule X) hp (by rw [suppDim_structureModule, hd])
  obtain ⟨p, hdeg, heval, hcoeff⟩ := hv.exists_polynomial_chi_twistZ ℝ hA.isLB
  obtain ⟨D, hD, c, hc, hfreq⟩ := (IsAmpleLB.isBig k X hp A hA).growth
  have hDn : D = n := by
    rw [hd] at hD
    exact_mod_cast hD.symm
  subst hDn
  have hser := eventually_subsingleton_coh_twistZ_of_isProjOver (algebraMap_eq_strHom k X)
    (structureModule X) hp hA
  have hchi : ∀ᶠ m : ℕ in atTop, (lbH0 k (lbPow A m) : ℝ) = p.eval (m : ℝ) := by
    filter_upwards [tendsto_natCast_atTop_atTop.eventually hser] with m hm
    have h1 := heval (m : ℤ)
    have h2 := chi_eq_hdim_zero k hm
    push_cast at h1
    rw [h1, h2]
    rfl
  by_contra hneg
  push_neg at hneg
  have hcD : p.coeff D ≤ 0 := by
    rw [hcoeff]
    have : ((interNum k (structureModule X) fun _ : Fin D => A : ℤ) : ℝ) ≤ 0 := by exact_mod_cast hneg
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) this
  have hq := eventually_eval_neg_of_coeff_neg (p - Polynomial.C c * Polynomial.X ^ D) D
    ((Polynomial.natDegree_sub_le _ _).trans (max_le hdeg
      ((Polynomial.natDegree_C_mul_X_pow_le c D))))
    (by
      rw [Polynomial.coeff_sub, Polynomial.coeff_C_mul_X_pow, if_pos rfl]
      linarith)
  obtain ⟨m, h1, h2, h3⟩ := (hfreq.and_eventually (hchi.and hq)).exists
  rw [Polynomial.eval_sub, Polynomial.eval_mul, Polynomial.eval_C, Polynomial.eval_pow,
    Polynomial.eval_X] at h3
  linarith

end GlobalTheory.CompanionTheory.NefKleiman
