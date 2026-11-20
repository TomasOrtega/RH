import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.MlabNotMemYset
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.SubstitutedExponentApplyLabel

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

variable {K : Type} [Field K] [CharZero K] {v : AddValuation K (WithTop ℚ)} {p : ℕ} {C0 : ℝ}

/- English proof (translation)
Establish `key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W))` using `fun W => by`. Simplify using `only [TwistData.abelian₂, gaAct_eq_dg]`. Establish `hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i)`. Introduce `s f`. Simplify using `only [key, map_sum, fock_sum_right]`.

Establish `hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W`. Introduce `c W`. Simplify using `only [key, map_smul, fock_smul_right]`. Establish `hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K)`. Introduce `g ζ`.

Rewrite using `[dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]`. Establish `hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K)` using `by conv_lhs => rw [Z.as_sum]`. Use `Finset.sum_congr rfl fun ζ _ => ?_` and prove the remaining obligations. Rewrite using `[MvPolynomial.smul_monomial, smul_eq_mul, mul_one]`. Establish `hp2 : 2 ≤ p` using `by have := hD.five_le; omega`.

Establish `hr1 : 1 ≤ D.r` using `hV.1`. Establish `hkap : 0 ≤ D.kapD p`. Unfold `TwistData.kapD kap`. Conclude with `Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)`. Establish `hDm : 0 ≤ D.Dm p C0` using `TwistData.Dm_nonneg (D := D) hp2 hr1 h1`.

Rewrite using `[hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]`. Simplify using `only [map_smul, hLsmul]`. Apply `vge_sum'` to reduce the goal to its premises. Introduce `ζ hζ`. Rewrite using `[← mul_sub]`.

Establish `hgood : D.GoodE p ζ` using `hZg ζ hζ`. Establish `hlow : D.LabLowE p ζ` using `hgood.1`. Establish `h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) = gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K))))`. Rewrite using `[hmon, map_smul, map_smul, hLsmul]`. Establish `h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K))`.

Rewrite using `[hmon, hLsmul]`. Establish `hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) = gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) + (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))`. Rewrite using `[h1', h2']`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hexp]`.

Establish `hval` using `TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm (fun ζ h => (happ ζ h).2) hgood`. Establish `hZζ : vge v 0 (Z.coeff ζ)` using `(vge_zero_iff v _).mpr (hZi ζ)`. Establish `hgp' : vge v 0 (gp ζ)` using `(vge_zero_iff v _).mpr (hgp0 ζ)`. Establish `t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))))`. Use `vge_mul' v hgp' hval` as an intermediate fact.

Simplify using `using this`. Establish `hgaP : v (D.gaP p gam ζ) = 0` using `TwistData.v_gaP (D := D) hV hdig hlow`. Establish `hg0 : D.gaP p gam ζ ≠ 0`. Introduce `h`. Rewrite `hgaP` using `[h]`.

Simplify using `at hgaP`. Establish `hgaP' : vge v 0 (D.gaP p gam ζ)` using `(vge_zero_iff v _).mpr (le_of_eq hgaP.symm)`. Establish `hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ)`. Use `(vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)` as an intermediate fact. Simplify using `using this`.

Establish `hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹)`. Use `(vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)` as an intermediate fact. Simplify using `using this`. Establish `hgm' : vge v 0 (gm ζ)`. Establish `h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹` using `by ring`.

Rewrite using `[h3]`. Use `vge_add' v (vge_mono' v (by positivity) hc2) ?_` and prove the remaining obligations. Rewrite using `[vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]`. Establish `hsplit : gp ζ * gm ζ - 1 = (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹)`. Rewrite using `[mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]`.

Expand and normalize the polynomial expressions, which then agree. Establish `t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1)`. Rewrite using `[hsplit]`. Use `vge_add' v ?_ ?_` and prove the remaining obligations. Simplify using `using vge_mul' v hc1 hgm'`.

Simplify using `using vge_mul' v hgaP' hc2`. Establish `hΛ` using `TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood`. Establish `t3` using `vge_mul' v t2 hΛ`. Establish `t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0) ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)))` using `vge_mono' v (by linarith) t3`. Simplify using `using vge_mul' v hZζ (vge_add' v t1 t3')`.
-/
theorem omega_value (hD : DVRHyp v p) (h1 : 1 ≤ C0) (D : TwistData K) (hV : D.Valid v p) (hH : D.HypH p 13)
    (hE : StepE K v p) {F : MvPolynomial (D.OL × Fin D.r) K} (hF : D.InXX p F) (hF0 : bge v 0 F)
    {cst : D.Tau → (Fin D.r → ℕ) → ℕ → K} {gam : D.Tau → (Fin D.r → ℕ) → (Fin D.r → ℕ) → K}
    (hdig : D.DigOK v p cst gam)
    (Pj : MvPolynomial (D.ML × Fin D.r) K →ₗ[K] MvPolynomial (D.ML × Fin D.r) K)
    (hP1 : ∀ ζ ζ' : D.EM, ζ' ∈ (Pj (monomial ζ 1)).support → D.SameBlockAlt ζ ζ')
    (hP2 : ∀ ζ : D.EM, D.GoodE p ζ → bge v (vN v (fact ζ) / 2 - D.Dm p C0) (Pj (monomial ζ 1)))
    (hP4 : ∀ (A : MvPolynomial (D.ML × Fin D.r) K) (ζ : D.EM), A ∈ PolK K D.r (fun i => ldeg ζ i) →
        (∀ (j : Fin D.J) (i : Fin (D.nch j)), vala D.msg (D.chainSet j i) (D.th j i - D.sl j i) A) →
        fock A (Pj (monomial ζ 1)) = fock A (monomial ζ 1))
    (gp gm : D.EM → K) (hgp0 : ∀ ζ, 0 ≤ v (gp ζ))
    (happ : ∀ ζ, D.LabLowE p ζ → ((D.c : ℕ) : WithTop ℚ) ≤ v (gp ζ - D.gaP p gam ζ) ∧
        ((D.c : ℕ) : WithTop ℚ) ≤ v (gm ζ - (D.gaP p gam ζ)⁻¹))
    (Z : MvPolynomial (D.ML × Fin D.r) K) (hZi : Integral v Z) (hZg : D.Good p Z) :
    vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (D.abelian₂ p F (dg gm (Pj (dg gp Z))) - D.abelian₂ p F Z) := by
  have key : ∀ W, D.abelian₂ p F W = fock F (dg D.ga (D.ph p W)) := fun W => by
    simp only [TwistData.abelian₂, gaAct_eq_dg]
  have hLsum : ∀ (s : Finset D.EM) (f : D.EM → MvPolynomial (D.ML × Fin D.r) K),
      D.abelian₂ p F (∑ i ∈ s, f i) = ∑ i ∈ s, D.abelian₂ p F (f i) := by
    intro s f
    simp only [key, map_sum, fock_sum_right]
  have hLsmul : ∀ (c : K) (W : MvPolynomial (D.ML × Fin D.r) K), D.abelian₂ p F (c • W) = c * D.abelian₂ p F W := by
    intro c W
    simp only [key, map_smul, fock_smul_right]
  have hmon : ∀ (g : D.EM → K) (ζ : D.EM), dg g (monomial ζ (1 : K)) = g ζ • monomial ζ (1 : K) := by
    intro g ζ
    rw [dg_monomial, MvPolynomial.smul_monomial, smul_eq_mul]
  have hZ : Z = ∑ ζ ∈ Z.support, Z.coeff ζ • monomial ζ (1 : K) := by
    conv_lhs => rw [Z.as_sum]
    refine Finset.sum_congr rfl fun ζ _ => ?_
    rw [MvPolynomial.smul_monomial, smul_eq_mul, mul_one]
  have hp2 : 2 ≤ p := by have := hD.five_le; omega
  have hr1 : 1 ≤ D.r := hV.1
  have hkap : 0 ≤ D.kapD p := by
    unfold TwistData.kapD kap
    exact Finset.sum_nonneg fun i _ => mul_nonneg (Nat.cast_nonneg _) (lg_nonneg' hp2 hr1 _)
  have hDm : 0 ≤ D.Dm p C0 := TwistData.Dm_nonneg (D := D) hp2 hr1 h1
  rw [hZ, map_sum (dg gp), map_sum Pj, map_sum (dg gm), hLsum, hLsum, ← Finset.sum_sub_distrib]
  simp only [map_smul, hLsmul]
  apply vge_sum'
  intro ζ hζ
  rw [← mul_sub]
  have hgood : D.GoodE p ζ := hZg ζ hζ
  have hlow : D.LabLowE p ζ := hgood.1
  have h1' : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) =
      gp ζ * D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) := by
    rw [hmon, map_smul, map_smul, hLsmul]
  have h2' : D.abelian₂ p F (dg gm (monomial ζ (1 : K))) = gm ζ * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [hmon, hLsmul]
  have hexp : D.abelian₂ p F (dg gm (Pj (dg gp (monomial ζ (1 : K))))) - D.abelian₂ p F (monomial ζ (1 : K)) =
      gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K)))) +
        (gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K)) := by
    rw [h1', h2']
    ring
  rw [hexp]
  have hval := TwistData.value_monomial (D := D) hD h1 hV hH hE hF hF0 hdig Pj hP1 hP2 hP4 gm
    (fun ζ h => (happ ζ h).2) hgood
  have hZζ : vge v 0 (Z.coeff ζ) := (vge_zero_iff v _).mpr (hZi ζ)
  have hgp' : vge v 0 (gp ζ) := (vge_zero_iff v _).mpr (hgp0 ζ)
  have t1 : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      (gp ζ * (D.abelian₂ p F (dg gm (Pj (monomial ζ (1 : K)))) - D.abelian₂ p F (dg gm (monomial ζ (1 : K))))) := by
    have := vge_mul' v hgp' hval
    simpa using this
  have hgaP : v (D.gaP p gam ζ) = 0 := TwistData.v_gaP (D := D) hV hdig hlow
  have hg0 : D.gaP p gam ζ ≠ 0 := by
    intro h
    rw [h] at hgaP
    simp at hgaP
  have hgaP' : vge v 0 (D.gaP p gam ζ) := (vge_zero_iff v _).mpr (le_of_eq hgaP.symm)
  have hc1 : vge v (D.c : ℝ) (gp ζ - D.gaP p gam ζ) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gp ζ - D.gaP p gam ζ)).mpr (by exact_mod_cast (happ ζ hlow).1)
    simpa using this
  have hc2 : vge v (D.c : ℝ) (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    have := (vge_rat_iff (v := v) (D.c : ℚ) (gm ζ - (D.gaP p gam ζ)⁻¹)).mpr (by exact_mod_cast (happ ζ hlow).2)
    simpa using this
  have hgm' : vge v 0 (gm ζ) := by
    have h3 : gm ζ = (gm ζ - (D.gaP p gam ζ)⁻¹) + (D.gaP p gam ζ)⁻¹ := by ring
    rw [h3]
    refine vge_add' v (vge_mono' v (by positivity) hc2) ?_
    rw [vge_zero_iff v, AddValuation.map_inv, hgaP, neg_zero]
  have hsplit : gp ζ * gm ζ - 1 =
      (gp ζ - D.gaP p gam ζ) * gm ζ + D.gaP p gam ζ * (gm ζ - (D.gaP p gam ζ)⁻¹) := by
    rw [mul_sub (D.gaP p gam ζ), mul_inv_cancel₀ hg0]
    ring
  have t2 : vge v (D.c : ℝ) (gp ζ * gm ζ - 1) := by
    rw [hsplit]
    refine vge_add' v ?_ ?_
    · simpa using vge_mul' v hc1 hgm'
    · simpa using vge_mul' v hgaP' hc2
  have hΛ := TwistData.vge_Lam_monomial (D := D) hD hV hF0 hgood
  have t3 := vge_mul' v t2 hΛ
  have t3' : vge v (D.c + D.n0 v - 2 * D.kapD p - D.Dm p C0)
      ((gp ζ * gm ζ - 1) * D.abelian₂ p F (monomial ζ (1 : K))) := vge_mono' v (by linarith) t3
  simpa using vge_mul' v hZζ (vge_add' v t1 t3')

/- English proof (translation)
Introduce `hD D hV hH _ F hF hF0`. Establish `hF0'` using `(exists_of_vBB_zero v F hF0).2`. Take `⟨Pj, hP1, hP2, hP3, hP4, hP5⟩` from `hP hD D hV`. Take `⟨cst, gam, hdig⟩` from `D.digOK_exists hDIG hD hV.2.2.1`. Take `⟨gp, gm, hgp, hgm, happ, hcost⟩` from `hG hD D hV cst gam hdig`.

Take `⟨hN, hI, hGd, hch, hY⟩` from `omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost`. Use `⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩` and prove the remaining obligations. Introduce `Z hZi hZg`. Conclude with `omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg`.
-/
theorem stepDEF_of (h1 : 1 ≤ C0) (hDIG : DIG K v p) (hG : StepG K v p) (hP : StepP K v p C0)
    (hE : StepE K v p) : StepDEF K v p C0 := by
  intro hD D hV hH _ F hF hF0
  have hF0' := (exists_of_vBB_zero v F hF0).2
  obtain ⟨Pj, hP1, hP2, hP3, hP4, hP5⟩ := hP hD D hV
  obtain ⟨cst, gam, hdig⟩ := D.digOK_exists hDIG hD hV.2.2.1
  obtain ⟨gp, gm, hgp, hgm, happ, hcost⟩ := hG hD D hV cst gam hdig
  obtain ⟨hN, hI, hGd, hch, hY⟩ :=
    omega_clauses hD h1 D hV Pj ⟨hP1, hP2, hP3, hP4, hP5⟩ gp gm hgp hgm hcost
  refine ⟨(dg gm).comp (Pj.comp (dg gp)), ⌈D.Dm p C0 + D.kapD p / 2⌉₊, hN, hI, hGd, hch, hY, ?_⟩
  intro Z hZi hZg
  exact omega_value hD h1 D hV hH hE hF hF0' hdig Pj hP1 hP2 hP4 gp gm hgp happ Z hZi hZg

end Formalism.MainNotions.PlaneGram
