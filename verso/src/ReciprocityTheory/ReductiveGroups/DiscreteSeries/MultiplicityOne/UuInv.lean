import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.PiInvApply
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.UnitaryGroupStructuralFacts
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvGroup
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JInvChar
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.StReps
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.MultiplicityOne.JTransM

open Matrix MeasureTheory
open scoped InnerProductSpace ENNReal ComplexConjugate

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymB ReciprocityTheory.ChartRestriction.DS.Mult1.SymC ReciprocityTheory.ChartRestriction.DS.Mult1.SymD

variable {k r : ℕ} {Wp : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [FiniteDimensional ℂ Wp]

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hi` using `i.isLt`. Establish `hj` using `j.isLt`. Apply the tactic sequence `let l : Fin (2 * r + k + 1) := ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩`.

Rewrite using `[Finset.sum_eq_single l]`. Apply the tactic sequence `simp only [Hpk, l, Fin.ext_iff, Fin.val_mk] split_ifs <;> first | (exfalso; omega) | norm_num`. Introduce `b _ hb`. Establish `hb' : b.val ≠ l.val` using `fun h => hb (Fin.ext h)`. Simplify using `only [l, Fin.val_mk] at hb'`.

Establish `hbl` using `b.isLt`. Apply `mul_eq_zero_of_left` to reduce the goal to its premises. Simplify using `only [Hpk, Fin.ext_iff]`. Apply the tactic sequence `split_ifs at hb' ⊢ <;> first | (exfalso; omega) | rfl`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ l) h`.
-/
private theorem hpk_sq_lemma : Hpk k r * Hpk k r = 1 := by
  ext i j
  rw [Matrix.mul_apply, Matrix.one_apply]
  have hi := i.isLt
  have hj := j.isLt
  let l : Fin (2 * r + k + 1) :=
    ⟨if r ≤ i.val ∧ i.val ≤ r + k then i.val else 2 * r + k - i.val, by split_ifs <;> omega⟩
  rw [Finset.sum_eq_single l]
  · simp only [Hpk, l, Fin.ext_iff, Fin.val_mk]
    split_ifs <;> first | (exfalso; omega) | norm_num
  · intro b _ hb
    have hb' : b.val ≠ l.val := fun h => hb (Fin.ext h)
    simp only [l, Fin.val_mk] at hb'
    have hbl := b.isLt
    apply mul_eq_zero_of_left
    simp only [Hpk, Fin.ext_iff]
    split_ifs at hb' ⊢ <;> first | (exfalso; omega) | rfl
  · intro h
    exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Simplify using `only [UUset, UWset, UH, Set.mem_setOf_eq] at hu ⊢`. Take `⟨⟨hH, hb, hz⟩, hw⟩` from `hu`. Establish `hdH : (Hpk k r).det ≠ 0`. Establish `h` using `congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))`. Rewrite `h` using `[Matrix.det_mul, Matrix.det_one]`.

Conclude with `left_ne_zero_of_mul_eq_one h`. Establish `hdu : IsUnit u.det`. Rewrite using `[isUnit_iff_ne_zero]`. Introduce `h0`. Establish `h` using `congrArg Matrix.det hH`.

Rewrite `h` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `hdH h.symm`. Establish `h1 : u⁻¹ * u = 1` using `Matrix.nonsing_inv_mul u hdu`. Establish `h3 : u * u⁻¹ = 1` using `Matrix.mul_nonsing_inv u hdu`. Establish `h2 : (u⁻¹)ᴴ * uᴴ = 1`.

Rewrite using `[← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]`. Establish `fix : ∀ v, u *ᵥ v = v → u⁻¹ *ᵥ v = v` using `fun v hv => by conv_lhs => rw [← hv]`. Rewrite using `[Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]`. Use `⟨⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩, fix _ hw⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
lemma uu_inv {z : Fin (2 * r + k + 1) → ℂ} {γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ} {u : Mat k r}
    (hu : u ∈ UUset k r z γ) : u⁻¹ ∈ UUset k r z γ := by
  simp only [UUset, UWset, UH, Set.mem_setOf_eq] at hu ⊢
  obtain ⟨⟨hH, hb, hz⟩, hw⟩ := hu
  have hdH : (Hpk k r).det ≠ 0 := by
    have h := congrArg Matrix.det (hpk_sq_lemma (k := k) (r := r))
    rw [Matrix.det_mul, Matrix.det_one] at h
    exact left_ne_zero_of_mul_eq_one h
  have hdu : IsUnit u.det := by
    rw [isUnit_iff_ne_zero]
    intro h0
    have h := congrArg Matrix.det hH
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at h
    exact hdH h.symm
  have h1 : u⁻¹ * u = 1 := Matrix.nonsing_inv_mul u hdu
  have h3 : u * u⁻¹ = 1 := Matrix.mul_nonsing_inv u hdu
  have h2 : (u⁻¹)ᴴ * uᴴ = 1 := by
    rw [← Matrix.conjTranspose_mul, h3, Matrix.conjTranspose_one]
  have fix : ∀ v, u *ᵥ v = v → u⁻¹ *ᵥ v = v := fun v hv => by
    conv_lhs => rw [← hv]
    rw [Matrix.mulVec_mulVec, h1, Matrix.one_mulVec]
  refine ⟨⟨?_, fun a => ⟨fix _ (hb a).1, fix _ (hb a).2⟩, fix _ hz⟩, fix _ hw⟩
  calc (u⁻¹)ᴴ * Hpk k r * u⁻¹ = (u⁻¹)ᴴ * (uᴴ * Hpk k r * u) * u⁻¹ := by rw [hH]
    _ = ((u⁻¹)ᴴ * uᴴ) * Hpk k r * (u * u⁻¹) := by simp only [Matrix.mul_assoc]
    _ = Hpk k r := by rw [h2, h3, Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `hz : D.z' = D.z` using `hD.z_eq`. Establish `hπ : D.π' = D.π` using `hD.π_eq`. Establish `Bc : ∀ F : Mat k r → (Wp →L[ℂ] Wp), ∀ u ∈ UUset k r D.z γ, (JF D F g0).comp (D.π u) = (D.π u).comp (JF D F g0)`. Introduce `F u hu`. Establish `hu' : u ∈ UWset k r D.z'` using `hz ▸ hu.1`.

Establish `e` using `J_equiv D hCI hu.1 hu' F g0`. Establish `eg : u⁻¹ * g0 * u = g0`. Rewrite using `[Matrix.mul_assoc, ← hcomm u hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hu.1.1), Matrix.one_mul]`. Rewrite `e` using `[eg, Lab_apply, hπ]`. Use `conv_lhs => rw [e]`.

Use extensionality with `v`. Simplify using `only [ContinuousLinearMap.comp_apply, pi_inv_apply D hu.1]`. Establish `hB : JF D (scalF Wp f) g0 = ∫ p, Phi D f g0 p ∂D.μSS` using `J_phi D hD f g0`. Establish `hB' : JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS` using `J_th D hD γ hE hgW hgN hlam hg0 f`. Establish `hC` using `aesm_C D hD γ hclW hgW`.

Establish `hPC : ∀ᵐ p ∂D.μSS, Psi D γ f g0 p = (Phi D f g0 p).comp (Cf D γ p) ∧ Phi D f g0 p = (Psi D γ f g0 p).comp (Cb D γ p) ∧ ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1` using `by filter_upwards [ae_in D] with p hp using psi_eq_C D hD γ hWbar hp f g0`. Distinguish the cases in `hm : AEStronglyMeasurable (Phi D f g0) D.μSS`. Use `swap`. Establish `hm' : ¬ AEStronglyMeasurable (Psi D γ f g0) D.μSS` using `fun h => hm ((aesm_comp h hC.2).congr (hPC.mono fun p hp => hp.2.1.symm))`. Rewrite using `[hB, hB', integral_non_aestronglyMeasurable hm, integral_non_aestronglyMeasurable hm']`.

Establish `hPhiI : Integrable (Phi D f g0) D.μSS`. Use `⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩` and prove the remaining obligations. Establish `e : ∀ p, ‖Phi D f g0 p‖ₑ = ‖rho D p (scalF Wp f) g0‖ₑ` using `fun p => by`. Establish `h1 : ‖ph D p‖ₑ = 1`. Rewrite using `[enorm_eq_nnnorm, show ‖ph D p‖₊ = 1 from NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact norm_ph D p), ENNReal.coe_one]`.

Rewrite using `[show Phi D f g0 p = ph D p • rho D p (scalF Wp f) g0 by rw [rho_scalF, hπ]; rfl, enorm_smul, h1, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `hPsiM : AEStronglyMeasurable (Psi D γ f g0) D.μSS` using `(aesm_comp hm hC.1).congr (hPC.mono fun p hp => hp.1.symm)`. Establish `hPsiI : Integrable (Psi D γ f g0) D.μSS`. Use `hPhiI.norm.mono' hPsiM (hPC.mono fun p hp => ?_)` and prove the remaining obligations.

Rewrite using `[hp.1]`. Conclude with `(ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp.2.2.1)`. Take `⟨Y, hY⟩ : ∃ Y, Y = JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0` from `⟨_, rfl⟩`. Establish `hYc : ∀ u ∈ UUset k r D.z γ, Y.comp (D.π u) = (D.π u).comp Y` using `fun u hu => by`. Rewrite using `[hY, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, Bc _ u hu, Bc _ u hu]`.

Establish `key : ∀ᵐ p ∂D.μSS, trY Y (Psi D γ f g0 p) = trY Y (Phi D f g0 p)` using `by filter_upwards [ae_in D] with p hp`. Establish `hh` using `hp.1`. Establish `hh' : Matrix.of p.2.1 ∈ UWset k r D.z` using `hz ▸ hp.2.2.1`. Establish `hy : Matrix.of p.1.1 * (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z` using `uw_mul hh (uw_inv hh')`. Take `⟨u₀, hu₀, hth⟩` from `hT6 _ hy`.

Establish `hop : (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹) = ((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1 : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp (((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)).comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1). …`. Rewrite using `[← D.π_rep.2 _ (hWbar _ hh') _ (uw_inv (hWbar _ hh)), ← th_mul_inv γ hE (isUnit_of_uh hh'.1), hth, D.π_rep.2 _ (uw_mul hu₀.1 hy) _ (uw_inv hu₀.1), D.π_rep.2 _ hu₀.1 _ hy, D.π_rep.2 _ hh _ (uw_inv hh')]`. Use extensionality with `v`. Both sides reduce to the same expression. Establish `h2 : Y.comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) = (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp Y`.

Rewrite using `[← pi_inv_eq D hu₀.1]`. Conclude with `hYc _ (uu_inv hu₀)`. Simplify using `only [Psi, Phi, hop, map_smul, trY_conj Y _ _ h2]`. Establish `hI1 : trY Y (∫ p, Psi D γ f g0 p ∂D.μSS) = trY Y (∫ p, Phi D f g0 p ∂D.μSS)`. Rewrite using `[← ContinuousLinearMap.integral_comp_comm _ hPsiI, ← ContinuousLinearMap.integral_comp_comm _ hPhiI]`.

Conclude with `integral_congr_ae key`. Establish `hYY : trY Y (JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0) = 0`. Rewrite using `[map_sub, hB, hB', hI1, sub_self]`. Rewrite `hYY` using `[← hY]`. Establish `h0` using `trY_self hYY`.

Rewrite `h0` using `[hY, sub_eq_zero]`. Then use the resulting hypothesis.
-/
theorem core (D : RealPlaceData k r Wp Wp) (hD : IsDiag D) (hCI : ConjInv D) (hclW : IsClosed (UWset k r D.z))
    (γ : Matrix (Fin (k + 1)) (Fin (k + 1)) ℂ) (hE : IsUnit (embWb k r γ).det)
    (hgW : D.μW.map (gb γ) = D.μW) (hgN : D.μN.map (gb γ) = D.μN)
    (hlam : ∀ m ∈ Nset k r, lam k r D.z (gbar k r γ m) = -lam k r D.z m)
    (hWbar : ∀ h ∈ UWset k r D.z, gbar k r γ h ∈ UWset k r D.z)
    (hT6 : ∀ y ∈ UWset k r D.z, ∃ u₀ ∈ UUset k r D.z γ, th k r γ y = u₀ * y * u₀⁻¹)
    {g0 : Mat k r} (hg0 : th k r γ g0 = g0) (hcomm : ∀ u ∈ UUset k r D.z γ, u * g0 = g0 * u)
    (f : Mat k r → ℂ) (hEf : ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS ≠ ∞) :
    JF D (scalF Wp (f ∘ th k r γ)) g0 = JF D (scalF Wp f) g0 := by
  have hz : D.z' = D.z := hD.z_eq
  have hπ : D.π' = D.π := hD.π_eq
  have Bc : ∀ F : Mat k r → (Wp →L[ℂ] Wp), ∀ u ∈ UUset k r D.z γ,
      (JF D F g0).comp (D.π u) = (D.π u).comp (JF D F g0) := by
    intro F u hu
    have hu' : u ∈ UWset k r D.z' := hz ▸ hu.1
    have e := J_equiv D hCI hu.1 hu' F g0
    have eg : u⁻¹ * g0 * u = g0 := by
      rw [Matrix.mul_assoc, ← hcomm u hu, ← Matrix.mul_assoc, Matrix.nonsing_inv_mul _ (isUnit_of_uh hu.1.1),
        Matrix.one_mul]
    rw [eg, Lab_apply, hπ] at e
    conv_lhs => rw [e]
    ext v
    simp only [ContinuousLinearMap.comp_apply, pi_inv_apply D hu.1]
  have hB : JF D (scalF Wp f) g0 = ∫ p, Phi D f g0 p ∂D.μSS := J_phi D hD f g0
  have hB' : JF D (scalF Wp (f ∘ th k r γ)) g0 = ∫ p, Psi D γ f g0 p ∂D.μSS :=
    J_th D hD γ hE hgW hgN hlam hg0 f
  have hC := aesm_C D hD γ hclW hgW
  have hPC : ∀ᵐ p ∂D.μSS, Psi D γ f g0 p = (Phi D f g0 p).comp (Cf D γ p) ∧
      Phi D f g0 p = (Psi D γ f g0 p).comp (Cb D γ p) ∧ ‖Cf D γ p‖ ≤ 1 ∧ ‖Cb D γ p‖ ≤ 1 := by
    filter_upwards [ae_in D] with p hp using psi_eq_C D hD γ hWbar hp f g0
  by_cases hm : AEStronglyMeasurable (Phi D f g0) D.μSS
  swap
  · have hm' : ¬ AEStronglyMeasurable (Psi D γ f g0) D.μSS := fun h =>
      hm ((aesm_comp h hC.2).congr (hPC.mono fun p hp => hp.2.1.symm))
    rw [hB, hB', integral_non_aestronglyMeasurable hm, integral_non_aestronglyMeasurable hm']
  have hPhiI : Integrable (Phi D f g0) D.μSS := by
    refine ⟨hm, hasFiniteIntegral_iff_enorm.2 ?_⟩
    have e : ∀ p, ‖Phi D f g0 p‖ₑ = ‖rho D p (scalF Wp f) g0‖ₑ := fun p => by
      have h1 : ‖ph D p‖ₑ = 1 := by
        rw [enorm_eq_nnnorm, show ‖ph D p‖₊ = 1 from NNReal.eq (by rw [coe_nnnorm, NNReal.coe_one]; exact norm_ph D p),
          ENNReal.coe_one]
      rw [show Phi D f g0 p = ph D p • rho D p (scalF Wp f) g0 by rw [rho_scalF, hπ]; rfl, enorm_smul, h1, one_mul]
    calc ∫⁻ p, ‖Phi D f g0 p‖ₑ ∂D.μSS = ∫⁻ p, ‖rho D p (scalF Wp f) g0‖ₑ ∂D.μSS := lintegral_congr e
      _ < ∞ := hEf.lt_top
  have hPsiM : AEStronglyMeasurable (Psi D γ f g0) D.μSS :=
    (aesm_comp hm hC.1).congr (hPC.mono fun p hp => hp.1.symm)
  have hPsiI : Integrable (Psi D γ f g0) D.μSS := by
    refine hPhiI.norm.mono' hPsiM (hPC.mono fun p hp => ?_)
    rw [hp.1]
    exact (ContinuousLinearMap.opNorm_comp_le _ _).trans (mul_le_of_le_one_right (norm_nonneg _) hp.2.2.1)
  obtain ⟨Y, hY⟩ : ∃ Y, Y = JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0 := ⟨_, rfl⟩
  have hYc : ∀ u ∈ UUset k r D.z γ, Y.comp (D.π u) = (D.π u).comp Y := fun u hu => by
    rw [hY, ContinuousLinearMap.sub_comp, ContinuousLinearMap.comp_sub, Bc _ u hu, Bc _ u hu]
  have key : ∀ᵐ p ∂D.μSS, trY Y (Psi D γ f g0 p) = trY Y (Phi D f g0 p) := by
    filter_upwards [ae_in D] with p hp
    have hh := hp.1
    have hh' : Matrix.of p.2.1 ∈ UWset k r D.z := hz ▸ hp.2.2.1
    have hy : Matrix.of p.1.1 * (Matrix.of p.2.1)⁻¹ ∈ UWset k r D.z := uw_mul hh (uw_inv hh')
    obtain ⟨u₀, hu₀, hth⟩ := hT6 _ hy
    have hop : (D.π (gbar k r γ (Matrix.of p.2.1))).comp (D.π (gbar k r γ (Matrix.of p.1.1))⁻¹) =
        ((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1 : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp
          (((D.π (Matrix.of p.1.1)).comp (D.π (Matrix.of p.2.1)⁻¹)).comp
            (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp)) := by
      rw [← D.π_rep.2 _ (hWbar _ hh') _ (uw_inv (hWbar _ hh)), ← th_mul_inv γ hE (isUnit_of_uh hh'.1), hth,
        D.π_rep.2 _ (uw_mul hu₀.1 hy) _ (uw_inv hu₀.1), D.π_rep.2 _ hu₀.1 _ hy, D.π_rep.2 _ hh _ (uw_inv hh')]
      ext v
      rfl
    have h2 : Y.comp (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp) =
        (((piLIE D.z D.π D.π_rep D.π_unitary u₀ hu₀.1).symm : Wp ≃ₗᵢ[ℂ] Wp) : Wp →L[ℂ] Wp).comp Y := by
      rw [← pi_inv_eq D hu₀.1]
      exact hYc _ (uu_inv hu₀)
    simp only [Psi, Phi, hop, map_smul, trY_conj Y _ _ h2]
  have hI1 : trY Y (∫ p, Psi D γ f g0 p ∂D.μSS) = trY Y (∫ p, Phi D f g0 p ∂D.μSS) := by
    rw [← ContinuousLinearMap.integral_comp_comm _ hPsiI, ← ContinuousLinearMap.integral_comp_comm _ hPhiI]
    exact integral_congr_ae key
  have hYY : trY Y (JF D (scalF Wp (f ∘ th k r γ)) g0 - JF D (scalF Wp f) g0) = 0 := by
    rw [map_sub, hB, hB', hI1, sub_self]
  rw [← hY] at hYY
  have h0 := trY_self hYY
  rwa [hY, sub_eq_zero] at h0

end ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

namespace ReciprocityTheory.ChartRestriction.DS.Mult1

open Formalism.QuantumDeterminants Formalism.FourierDecayAlt.B Formalism.FourierDecayAlt.B2 ReciprocityTheory.ChartRestriction.DS.Mult1.SymA ReciprocityTheory.ChartRestriction.DS.Mult1.SymB
  ReciprocityTheory.ChartRestriction.DS.Mult1.SymE

/- English proof (translation)
Introduce `k r Wp _ _ _ D X hD hX γ hγ f q _ hq hT hEf`. Take `⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIall, -, -, -, -, -, -, -, -, hClW, -⟩, -, -, hBCF, hUWb, -⟩` from `id hIn`. Establish `hCI : ConjInv D` using `hCIall k r Wp Wp D`. Take `⟨-, -, hW1, -, -, -, -, hμN, hμW⟩` from `stInvGroup hIn k r Wp D X hD hX γ hγ`. Establish `hChar` using `stInvChar k r Wp D X hD hX γ hγ`.

Establish `hL6` using `stTransM hIn k r Wp D X hD hX γ hγ`. Establish `hE : IsUnit (embWb k r γ).det` using `emb_unit (unit_of_frame hγ.1)`. Establish `hTpos : 0 < Tz k r D.z` using `D.T_pos`. Establish `hc : ∀ a, q.1 a ≠ 0`. Introduce `a ha0`.

Establish `hw : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q` using `hq`. Unfold `bcWeight at hw`. Use `split_ifs at hw with h1`. Establish `hM : 0 < 2 * (Mdim k r a - 2)`. Unfold `Mdim`.

Use `a.isLt` as an intermediate fact. Use `D.k_pos` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `h0 : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Mdim k r b - 2))) = 0` using `Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha0, norm_zero, zero_pow hM.ne'])`. Rewrite `hw` using `[h0, zero_mul]`.

Conclude with `lt_irrefl _ hw`. Conclude with `lt_irrefl _ hw`. Establish `hT0 : ((Tz k r D.z : ℝ) : ℂ) ≠ 0` using `Complex.ofReal_ne_zero.2 hTpos.ne'`. Take `⟨d, hd_def⟩ : ∃ d : ℂ, d = -(q.2 / ((Tz k r D.z : ℝ) : ℂ))` from `⟨_, rfl⟩`. Establish `hd : 1 < ‖d‖`.

Establish `h3 : Tz k r D.z < ‖q.2‖`. Rewrite `hT` using `[Complex.normSq_eq_norm_sq]`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Use polynomial arithmetic with `[norm_nonneg q.2]`.

Establish `hnT : ‖((Tz k r D.z : ℝ) : ℂ)‖ = Tz k r D.z`. Rewrite using `[Complex.norm_real, Real.norm_of_nonneg hTpos.le]`. Rewrite using `[hd_def, norm_neg, norm_div, hnT, one_lt_div hTpos]`. Conclude with `h3`. Establish `hqd : (q.1, -((Tz k r D.z : ℝ) : ℂ) * d) = q`.

Use `Prod.ext rfl ?_` and prove the remaining obligations. Use `show -((Tz k r D.z : ℝ) : ℂ) * d = q.2`. Rewrite using `[hd_def]`. Clear the denominators using the available nonvanishing facts. Take `⟨-, -, -, hg0th, h₀, hh₀, h₀', hh₀', hgq⟩` from `stReps hIn k r Wp D X hD hX γ hγ q.1 d hc hd`.

Rewrite `hgq` using `[hqd]`. Establish `hh₀'' : h₀' ∈ UWset k r D.z'` using `hD.z_eq ▸ hh₀'`. Establish `red : ∀ F : Mat k r → (Wp →L[ℂ] Wp), JF D F (gq D q) = (Lab D hh₀ hh₀'').symm (JF D F (g0 k r γ q.1 d))` using `fun F => by`. Rewrite using `[J_equiv D hCI hh₀ hh₀'' F (g0 k r γ q.1 d), ← hgq, ContinuousLinearEquiv.symm_apply_apply]`. Establish `hEf0 : ∫⁻ p, ‖rho D p (scalF Wp f) (g0 k r γ q.1 d)‖ₑ ∂D.μSS ≠ ∞`.

Rewrite using `[E_equiv D hCI hh₀ hh₀'', ← hgq]`. Conclude with `hEf`. Rewrite using `[red, red, core D hD hCI (hClW k r D.z).closed γ hE hμW hμN (fun m hm => (hChar m hm).1) hW1 hL6 hg0th (fun u hu => big_cell_commute_frame_element hBCF hUWb D.k_pos hγ hu q.1 d) f hEf0]`.
-/
theorem stSym (hIn : UnitaryGroupStructuralFacts) : StSym := by
  intro k r Wp _ _ _ D X hD hX γ hγ f q _ hq hT hEf
  obtain ⟨⟨-, -, -, -, -, -, -, -, -, -, -, -, hCIall, -, -, -, -, -, -, -, -, hClW, -⟩, -, -, hBCF, hUWb, -⟩ := id hIn
  have hCI : ConjInv D := hCIall k r Wp Wp D
  obtain ⟨-, -, hW1, -, -, -, -, hμN, hμW⟩ := stInvGroup hIn k r Wp D X hD hX γ hγ
  have hChar := stInvChar k r Wp D X hD hX γ hγ
  have hL6 := stTransM hIn k r Wp D X hD hX γ hγ
  have hE : IsUnit (embWb k r γ).det := emb_unit (unit_of_frame hγ.1)
  have hTpos : 0 < Tz k r D.z := D.T_pos
  have hc : ∀ a, q.1 a ≠ 0 := by
    intro a ha0
    have hw : 0 < bcWeight k r (Tz k r D.z) (Tz k r D.z') q := hq
    unfold bcWeight at hw
    split_ifs at hw with h1
    · have hM : 0 < 2 * (Mdim k r a - 2) := by
        unfold Mdim
        have := a.isLt
        have := D.k_pos
        omega
      have h0 : (∏ b : Fin r, ‖q.1 b‖ ^ (2 * (Mdim k r b - 2))) = 0 :=
        Finset.prod_eq_zero (Finset.mem_univ a) (by rw [ha0, norm_zero, zero_pow hM.ne'])
      rw [h0, zero_mul] at hw
      exact lt_irrefl _ hw
    · exact lt_irrefl _ hw
  have hT0 : ((Tz k r D.z : ℝ) : ℂ) ≠ 0 := Complex.ofReal_ne_zero.2 hTpos.ne'
  obtain ⟨d, hd_def⟩ : ∃ d : ℂ, d = -(q.2 / ((Tz k r D.z : ℝ) : ℂ)) := ⟨_, rfl⟩
  have hd : 1 < ‖d‖ := by
    have h3 : Tz k r D.z < ‖q.2‖ := by
      rw [Complex.normSq_eq_norm_sq] at hT
      by_contra hcon
      push Not at hcon
      nlinarith [norm_nonneg q.2]
    have hnT : ‖((Tz k r D.z : ℝ) : ℂ)‖ = Tz k r D.z := by
      rw [Complex.norm_real, Real.norm_of_nonneg hTpos.le]
    rw [hd_def, norm_neg, norm_div, hnT, one_lt_div hTpos]
    exact h3
  have hqd : (q.1, -((Tz k r D.z : ℝ) : ℂ) * d) = q := by
    refine Prod.ext rfl ?_
    show -((Tz k r D.z : ℝ) : ℂ) * d = q.2
    rw [hd_def]
    field_simp
  obtain ⟨-, -, -, hg0th, h₀, hh₀, h₀', hh₀', hgq⟩ := stReps hIn k r Wp D X hD hX γ hγ q.1 d hc hd
  rw [hqd] at hgq
  have hh₀'' : h₀' ∈ UWset k r D.z' := hD.z_eq ▸ hh₀'
  have red : ∀ F : Mat k r → (Wp →L[ℂ] Wp),
      JF D F (gq D q) = (Lab D hh₀ hh₀'').symm (JF D F (g0 k r γ q.1 d)) := fun F => by
    rw [J_equiv D hCI hh₀ hh₀'' F (g0 k r γ q.1 d), ← hgq, ContinuousLinearEquiv.symm_apply_apply]
  have hEf0 : ∫⁻ p, ‖rho D p (scalF Wp f) (g0 k r γ q.1 d)‖ₑ ∂D.μSS ≠ ∞ := by
    rw [E_equiv D hCI hh₀ hh₀'', ← hgq]
    exact hEf
  rw [red, red, core D hD hCI (hClW k r D.z).closed γ hE hμW hμN (fun m hm => (hChar m hm).1) hW1 hL6 hg0th
    (fun u hu => big_cell_commute_frame_element hBCF hUWb D.k_pos hγ hu q.1 d) f hEf0]

end ReciprocityTheory.ChartRestriction.DS.Mult1
