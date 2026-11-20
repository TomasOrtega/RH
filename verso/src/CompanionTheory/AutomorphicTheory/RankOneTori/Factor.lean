import CompanionTheory.AutomorphicTheory.RankOneTori.MatGroupOf

open MeasureTheory Matrix Formalism.QuantumDeterminants Formalism.MainNotions.S Formalism.MainNotions.S.Pv.AmpDDPf Formalism.FourierDecayAlt
open scoped ENNReal InnerProductSpace

noncomputable section

namespace Formalism.MainStatements.RankOne

variable {k r : ℕ}

def lamP (L : LocBessel k r) (l : L.Hs → L.Wp) (P : L.Hs →L[ℂ] L.Wp) : ℂ :=
  ∑ i, ⟪l (ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ L.Wp i)), stdOrthonormalBasis ℂ L.Wp i⟫_ℂ

def lamQ (L : LocBessel k r) (l' : L.Hs → L.Wq) (Q : L.Wq →L[ℂ] L.Hs) : ℂ :=
  ∑ j, ⟪stdOrthonormalBasis ℂ L.Wq j, l' (Q (stdOrthonormalBasis ℂ L.Wq j))⟫_ℂ

/- English proof (translation)
Use extensionality with `η`. Simplify using `only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, Pv.AmpDD.coefF, ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left, smul_smul]`. Use `conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wp).sum_repr' (P (L.σ x (Q η)))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_smul]`.

Use `congr 1`. Use `conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wq).sum_repr' η]`. Simplify using `only [map_sum, map_smul, inner_sum, inner_smul_right]`.
-/
theorem coef_expand (L : LocBessel k r) (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs) (x : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ) :
    P.comp ((L.σ x).comp Q) = ∑ i, ∑ j, Pv.AmpDD.coefF L (ContinuousLinearMap.adjoint P (stdOrthonormalBasis ℂ L.Wp i))
      (Q (stdOrthonormalBasis ℂ L.Wq j)) (stdOrthonormalBasis ℂ L.Wp i) (stdOrthonormalBasis ℂ L.Wq j) x := by
  ext η
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.sum_apply, Pv.AmpDD.coefF,
    ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, ContinuousLinearMap.adjoint_inner_left, smul_smul]
  conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wp).sum_repr' (P (L.σ x (Q η)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [← Finset.sum_smul]
  congr 1
  conv_lhs => rw [← (stdOrthonormalBasis ℂ L.Wq).sum_repr' η]
  simp only [map_sum, map_smul, inner_sum, inner_smul_right]

/- English proof (translation)
Establish `: SigmaFinite μG` using `hμG.1`. Use `set K : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG) with hK`. Establish `hK0 : 0 ≤ K`. Establish `: 0 ≤ ∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG` using `integral_nonneg fun x => Real.rpow_nonneg (P.S3dx6.gN_nonneg _) _`. Check the signs of the components of the expression.

Establish `hsm : StronglyMeasurable fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG` using `(sm_PsiM L w0 v v' ξ ξ' γ).integral_prod_right'`. Establish `he : ∀ p, InPair L p → ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG = ∫ x, Psi L w0 v v' ξ ξ' γ p x ∂μG` using `fun p hp => integral_congr_ae ((ae_mem_sk hμG).mono fun x hx => PsiM_eq L w0 v v' ξ ξ' hγ hp hx)`. Establish `hI : Integrable (fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG) ν`. Use `(hpm.const_mul K).mono' hsm.aestronglyMeasurable (hae.mono fun p hp => ?_)` and prove the remaining obligations. Rewrite using `[he p hp]`.

Establish `h1` using `(enorm_integral_le_lintegral_enorm _).trans (lint_G_bound L hμG P.norm_inverse_bound hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp)`. Rewrite `h1` using `[← ofReal_norm_eq_enorm]`. Conclude with `(ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (pairMaj_nonneg γ b p))).1 h1`. Use `(hI.smul (d : ℂ)).congr (hae.mono fun p hp => ?_)` and prove the remaining obligations. Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`.

Simplify using `only [Pi.smul_apply]`. Rewrite using `[he p hp, (schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp).2, smul_smul, mul_inv_cancel₀ hd', one_smul]`.
-/
theorem int_coefF (L : LocBessel k r) {μG : Measure (Mt k r)} (hμG : IsHaarOn (UH (Hpk k r)) μG) {d : ℝ} (hd : 0 < d)
    (hSch : ∀ v w v' w' : L.Hs,
      Integrable (fun x : Mt k r => ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ) μG ∧
      ∫ x, ⟪w, L.σ (Matrix.of x) v⟫_ℂ * star ⟪w', L.σ (Matrix.of x) v'⟫_ℂ ∂μG = ⟪v', v⟫_ℂ * ⟪w, w'⟫_ℂ / (d : ℂ))
    {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} (hγ : γ ∈ UH (Hpk k r)) {ν : Measure (PairSp k r)}
    (hae : ∀ᵐ p ∂ν, InPair L p) {a b C1 C2 : ℝ} (hb : 0 ≤ b) (hab : b ≤ a)
    (hIG : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (b - a)) μG)
    (hpm : Integrable (Pv.AmpDD.pairMaj γ b) ν) {v v' : L.Hs}
    (hC1 : ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C1 * B.gN g ^ (-a))
    (hC2 : ∀ g ∈ UH (Hpk k r), ‖⟪v', L.σ g w0⟫_ℂ‖ ≤ C2 * B.gN g ^ (-a)) (ξ : L.Wp) (ξ' : L.Wq) :
    Integrable (besselIntg L (Pv.AmpDD.coefF L v v' ξ ξ') γ) ν := by
  have : SigmaFinite μG := hμG.1
  set K : ℝ := ‖ξ‖ * ‖ξ'‖ * (|C1| * |C2|) * (∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG) with hK
  have hK0 : 0 ≤ K := by
    have : 0 ≤ ∫ x, B.gN (Matrix.of x) ^ (b - a) ∂μG :=
      integral_nonneg fun x => Real.rpow_nonneg (P.S3dx6.gN_nonneg _) _
    positivity
  have hsm : StronglyMeasurable fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG :=
    (sm_PsiM L w0 v v' ξ ξ' γ).integral_prod_right'
  have he : ∀ p, InPair L p → ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG = ∫ x, Psi L w0 v v' ξ ξ' γ p x ∂μG := fun p hp =>
    integral_congr_ae ((ae_mem_sk hμG).mono fun x hx => PsiM_eq L w0 v v' ξ ξ' hγ hp hx)
  have hI : Integrable (fun p : PairSp k r => ∫ x, PsiM L w0 v v' ξ ξ' γ (p, x) ∂μG) ν := by
    refine (hpm.const_mul K).mono' hsm.aestronglyMeasurable (hae.mono fun p hp => ?_)
    rw [he p hp]
    have h1 := (enorm_integral_le_lintegral_enorm _).trans
      (lint_G_bound L hμG P.norm_inverse_bound hb hab hIG w0 v v' ξ ξ' hC1 hC2 hγ hp)
    rw [← ofReal_norm_eq_enorm] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hK0 (pairMaj_nonneg γ b p))).1 h1
  refine (hI.smul (d : ℂ)).congr (hae.mono fun p hp => ?_)
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  simp only [Pi.smul_apply]
  rw [he p hp, (schur_step L hμG hd hSch hw1 v v' ξ ξ' hγ hp).2, smul_smul, mul_inv_cancel₀ hd', one_smul]

/- English proof (translation)
Take `⟨hγ, hrel, hR, hq, hinv, b, hb, hab, hpm⟩` from `hc`. Take `⟨μG, hμG0⟩` from `P.unitary_group_haar_exists k r`. Establish `hμG : IsHaarOn (UH (Hpk k r)) μG` using `⟨P.B5.haar_sigmaFinite hμG0, hμG0.ne_zero, hμG0.conc, hμG0.left⟩`. Take `⟨νR, hν⟩` from `quot_exists hγ hμG hR`. Take `⟨d, hd, hSch⟩` from `P.schur_hermitian k r L.ε L.lam L.Hs L.σ μG L.hlam L.hσ hμG`.

Establish `hd' : (d : ℂ) ≠ 0` using `by exact_mod_cast hd.ne'`. Establish `hAG0 : 0 ≤ ThreeDimData.AG k r` using `by unfold ThreeDimData.AG; positivity`. Establish `hab' : b ≤ a` using `by linarith`. Establish `hIG : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (b - a)) μG`. Establish `h1` using `P.growth_group_bound k r μG (a - b) hμG (by linarith)`.

Simplify `h1` using `only [neg_sub]`. Establish `hae` using `ae_inPair_nu L hR hq`. Use `⟨(d : ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ, fun P Q hP hQ F hF => ?_⟩` and prove the remaining obligations. Use `set e := stdOrthonormalBasis ℂ L.Wp with he`. Use `set e' := stdOrthonormalBasis ℂ L.Wq with he'`.

Use `choose C1 hC1 using fun i => hdec _ (hP (e i))`. Use `choose C2 hC2 using fun j => hdec _ (hQ (e' j))`. Establish `hI` using `fun i j => int_coefF L hμG hd hSch hw1 hγ hae hb hab' hIG hpm (hC1 i) (hC2 j) (e i) (e' j)`. Establish `hA` using `fun i j => amp_core' L hμG hd hSch Formalism.FourierDecayAlt.P.norm_inverse_bound hw1 l l' hγ hrel hR hq hν hinv hb hab' hIG hpm (hl _ (hP (e i))) (hl' _ (hQ (e' j))) (hC1 i) (hC2 j) (e i) (e' j)`. Establish `h1 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (Pv.AmpDD.coefF L (ContinuousLinearMap.adjoint P (e i)) (Q (e' j)) (e i) (e' j)) γ ν`.

Unfold `OrbInt`. Simplify using `only [← integral_finsetSum _ fun j _ => hI _ j]`. Rewrite using `[← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]`. Use `integral_congr_ae (hae.mono fun p hp => ?_)` and prove the remaining obligations. Establish `hx` using `WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)) hγ) hp.2.2.2.1) hp.2.2.1.1`.

Simplify using `only [besselIntg]`. Rewrite using `[hF _ hx, coef_expand]`. Simplify using `only [ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum, Finset.smul_sum]`. Both sides reduce to the same expression. Rewrite using `[h1, lamP, lamQ, Finset.sum_mul_sum, Finset.sum_smul]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_comm, hA i j, smul_smul, mul_inv_cancel₀ hd', one_smul]`.
-/
theorem cell_factor (L : LocBessel k r) {a : ℝ} {w0 : L.Hs} (hw1 : ⟪w0, w0⟫_ℂ = 1) (l : L.Hs → L.Wp) (l' : L.Hs → L.Wq)
    (Sm : Set L.Hs) (hdec : ∀ v ∈ Sm, ∃ C : ℝ, ∀ g ∈ UH (Hpk k r), ‖⟪v, L.σ g w0⟫_ℂ‖ ≤ C * B.gN g ^ (-a))
    (hl : ∀ v ∈ Sm, ∀ t ∈ UH (Hpk k r), ThreeDimData.be L.z L.c L.π L.σ L.μW L.μN (L.σ t w0) v =
      (innerSL ℂ (l v)).smulRight (l (L.σ t w0)))
    (hl' : ∀ v ∈ Sm, ∀ t ∈ UH (Hpk k r), ThreeDimData.be L.z' L.c L.π' L.σ L.μW' L.μN (L.σ t w0) v =
      (innerSL ℂ (l' v)).smulRight (l' (L.σ t w0)))
    {γ : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ} {μR : Measure (Mt k r)} {ν : Measure (PairSp k r)} (hc : Cell L a γ μR ν) :
    ∃ Ψ : L.Wq →L[ℂ] L.Wp, ∀ (P : L.Hs →L[ℂ] L.Wp) (Q : L.Wq →L[ℂ] L.Hs),
      (∀ x, ContinuousLinearMap.adjoint P x ∈ Sm) → (∀ w, Q w ∈ Sm) → ∀ F : Matrix (Fin (2 * r + k + 1)) (Fin (2 * r + k + 1)) ℂ → (L.Wq →L[ℂ] L.Wp),
      (∀ x ∈ UH (Hpk k r), F x = P.comp ((L.σ x).comp Q)) → OrbInt L F γ ν = (lamP L l P * lamQ L l' Q) • Ψ := by
  obtain ⟨hγ, hrel, hR, hq, hinv, b, hb, hab, hpm⟩ := hc
  obtain ⟨μG, hμG0⟩ := P.unitary_group_haar_exists k r
  have hμG : IsHaarOn (UH (Hpk k r)) μG := ⟨P.B5.haar_sigmaFinite hμG0, hμG0.ne_zero, hμG0.conc, hμG0.left⟩
  obtain ⟨νR, hν⟩ := quot_exists hγ hμG hR
  obtain ⟨d, hd, hSch⟩ := P.schur_hermitian k r L.ε L.lam L.Hs L.σ μG L.hlam L.hσ hμG
  have hd' : (d : ℂ) ≠ 0 := by exact_mod_cast hd.ne'
  have hAG0 : 0 ≤ ThreeDimData.AG k r := by unfold ThreeDimData.AG; positivity
  have hab' : b ≤ a := by linarith
  have hIG : Integrable (fun x : Mt k r => B.gN (Matrix.of x) ^ (b - a)) μG := by
    have h1 := P.growth_group_bound k r μG (a - b) hμG (by linarith)
    simpa only [neg_sub] using h1
  have hae := ae_inPair_nu L hR hq
  refine ⟨(d : ℂ) • ampJ νR 1 (fun g => l (L.σ g w0)) (fun g => l' (L.σ g w0)) γ, fun P Q hP hQ F hF => ?_⟩
  set e := stdOrthonormalBasis ℂ L.Wp with he
  set e' := stdOrthonormalBasis ℂ L.Wq with he'
  choose C1 hC1 using fun i => hdec _ (hP (e i))
  choose C2 hC2 using fun j => hdec _ (hQ (e' j))
  have hI := fun i j => int_coefF L hμG hd hSch hw1 hγ hae hb hab' hIG hpm (hC1 i) (hC2 j) (e i) (e' j)
  have hA := fun i j => amp_core' L hμG hd hSch Formalism.FourierDecayAlt.P.norm_inverse_bound hw1 l l' hγ hrel hR hq hν hinv hb hab' hIG hpm
    (hl _ (hP (e i))) (hl' _ (hQ (e' j))) (hC1 i) (hC2 j) (e i) (e' j)
  have h1 : OrbInt L F γ ν = ∑ i, ∑ j, OrbInt L (Pv.AmpDD.coefF L (ContinuousLinearMap.adjoint P (e i)) (Q (e' j))
      (e i) (e' j)) γ ν := by
    unfold OrbInt
    simp only [← integral_finsetSum _ fun j _ => hI _ j]
    rw [← integral_finsetSum _ fun i _ => integrable_finsetSum _ fun j _ => hI i j]
    refine integral_congr_ae (hae.mono fun p hp => ?_)
    have hx := WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_mul (WeylGroupFacts.uh_inv hp.1.1) (WeylGroupFacts.uh_inv hp.2.1.1)) hγ)
      hp.2.2.2.1) hp.2.2.1.1
    simp only [besselIntg]
    rw [hF _ hx, coef_expand]
    simp only [ContinuousLinearMap.finset_sum_comp, ContinuousLinearMap.comp_finset_sum, Finset.smul_sum]
    rfl
  rw [h1, lamP, lamQ, Finset.sum_mul_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [smul_comm, hA i j, smul_smul, mul_inv_cancel₀ hd', one_smul]

end Formalism.MainStatements.RankOne
