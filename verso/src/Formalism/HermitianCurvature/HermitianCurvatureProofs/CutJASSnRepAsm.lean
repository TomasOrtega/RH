import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapTP
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutJABddKapNrmW
import Formalism.HermitianCurvature.HermitianCurvatureProofs.RestrictionIrrelevantDoubleLevelOperator

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt NumberField
open scoped ComplexConjugate Matrix

namespace Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

/- English proof (translation)
Establish `hP : (∏ i, c i) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun a _ => hc a`. Rewrite using `[← map_prod, Finset.prod_inv_distrib]`. Unfold `SSn.phD`. Use `set D := ∏ i, c i with hD`. Establish `hn : ((‖D‖ : ℝ) : ℂ) ≠ 0` using `by exact_mod_cast norm_ne_zero_iff.2 hP`.

Establish `hnn : ((‖D‖ : ℝ) : ℂ) ^ 2 = D * conj D`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[map_div₀, Complex.conj_ofReal, div_pow, hnn]`.

Clear the denominators using the available nonvanishing facts.
-/
theorem conj_phD_sq {r : ℕ} {c : Fin r → ℂ} (hc : ∀ a, c a ≠ 0) :
    (conj (SSn.phD c)) ^ 2 = (∏ i, conj (c i)) * ∏ i, (c i)⁻¹ := by
  have hP : (∏ i, c i) ≠ 0 := Finset.prod_ne_zero_iff.2 fun a _ => hc a
  rw [← map_prod, Finset.prod_inv_distrib]
  unfold SSn.phD
  set D := ∏ i, c i with hD
  have hn : ((‖D‖ : ℝ) : ℂ) ≠ 0 := by exact_mod_cast norm_ne_zero_iff.2 hP
  have hnn : ((‖D‖ : ℝ) : ℂ) ^ 2 = D * conj D := by
    rw [Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; ring
  rw [map_div₀, Complex.conj_ofReal, div_pow, hnn]
  field_simp

section gen

variable {Wp Wq : Type} [NormedAddCommGroup Wp] [InnerProductSpace ℂ Wp] [NormedAddCommGroup Wq]
  [InnerProductSpace ℂ Wq] [FiniteDimensional ℂ Wq]

/- English proof (translation)
The claim follows from `((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hg.prodMk hf)`.
-/
theorem cd_comp {X : Type} [NormedAddCommGroup X] [NormedSpace ℝ X] {U V W : Type} [NormedAddCommGroup U]
    [NormedSpace ℂ U] [NormedAddCommGroup V] [NormedSpace ℂ V] [NormedAddCommGroup W] [NormedSpace ℂ W]
    {n : WithTop ℕ∞} {g : X → V →L[ℂ] W} {f : X → U →L[ℂ] V} (hg : ContDiff ℝ n g) (hf : ContDiff ℝ n f) :
    ContDiff ℝ n (fun x => (g x).comp (f x)) :=
  ((ContinuousLinearMap.compL ℂ U V W).bilinearRestrictScalars ℝ).isBoundedBilinearMap.contDiff.comp (hg.prodMk hf)

/- English proof (translation)
Unfold `B.hsVec`. Use extensionality with `i`. Simplify using the standard rewrite rules.
-/
theorem hsVec_zero' : B.hsVec (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsVec; ext i; simp

/- English proof (translation)
Unfold `B.hsInner`. Rewrite using `[hsVec_zero', inner_zero_right]`.
-/
theorem hsInner_zero_l (B' : Wq →L[ℂ] Wp) : B.hsInner (0 : Wq →L[ℂ] Wp) B' = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_right]

/- English proof (translation)
Unfold `B.hsInner`. Rewrite using `[hsVec_zero', inner_zero_left]`.
-/
theorem hsInner_zero_r (A : Wq →L[ℂ] Wp) : B.hsInner A (0 : Wq →L[ℂ] Wp) = 0 := by
  unfold B.hsInner; rw [hsVec_zero', inner_zero_left]

/- English proof (translation)
Rewrite using `[Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]`.
-/
theorem inner_hs_smul (c : ℂ) (A B' : Wq →L[ℂ] Wp) :
    inner ℂ (B.hsVec A) (B.hsVec (c • B')) = c * inner ℂ (B.hsVec A) (B.hsVec B') := by
  rw [Formalism.FourierDecayAlt.P.JCTx2.hsVec_smul', inner_smul_right]

/- English proof (translation)
Rewrite using `[kap_hsInner_sum_left, Finset.sum_eq_single π]`. Rewrite using `[kap_hsInner_sum_left, Finset.sum_eq_single ρ]`. Rewrite using `[kap_hsInner_smul_left, hQadj, hline π π, hline ρ ρ, if_pos rfl, if_pos rfl]`. Introduce `ρ' _ hne`. Rewrite using `[kap_hsInner_smul_left, hQadj, hline ρ' ρ, if_neg hne, hsInner_zero_r, mul_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ ρ) h`. Introduce `π' _ hne`. Rewrite using `[hline π' π, if_neg hne, map_zero]`. Simplify using `only [map_zero, smul_zero, Finset.sum_const_zero]`.

Conclude with `hsInner_zero_l _`. Introduce `h`. Conclude with `absurd (Finset.mem_univ π) h`.
-/
theorem mat_gen {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    B.hsInner (∑ π', ∑ ρ', c π' ρ' • Qd ρ' (T0 (Qd π' (e π)))) (e ρ) = c π ρ * B.hsInner (T0 (e π)) (e ρ) := by
  rw [kap_hsInner_sum_left, Finset.sum_eq_single π]
  · rw [kap_hsInner_sum_left, Finset.sum_eq_single ρ]
    · rw [kap_hsInner_smul_left, hQadj, hline π π, hline ρ ρ, if_pos rfl, if_pos rfl]
    · intro ρ' _ hne
      rw [kap_hsInner_smul_left, hQadj, hline ρ' ρ, if_neg hne, hsInner_zero_r, mul_zero]
    · intro h; exact absurd (Finset.mem_univ ρ) h
  · intro π' _ hne
    rw [hline π' π, if_neg hne, map_zero]
    simp only [map_zero, smul_zero, Finset.sum_const_zero]
    exact hsInner_zero_l _
  · intro h; exact absurd (Finset.mem_univ π) h

/- English proof (translation)
Establish `h` using `mat_gen Qd T0 c e hQadj hline π ρ`. Unfold `B.hsInner at h`. Rewrite using `[← h]`. Use `congr 2`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]`.
-/
theorem mat_gen' {Ty : Type} [Fintype Ty] [DecidableEq Ty] (Qd : Ty → (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp))
    (T0 : (Wq →L[ℂ] Wp) →L[ℂ] (Wq →L[ℂ] Wp)) (c : Ty → Ty → ℂ) (e : Ty → (Wq →L[ℂ] Wp))
    (hQadj : ∀ σ A B', B.hsInner (Qd σ A) B' = B.hsInner A (Qd σ B'))
    (hline : ∀ σ ρ, Qd σ (e ρ) = if σ = ρ then e ρ else 0) (π ρ : Ty) :
    inner ℂ (B.hsVec (e ρ)) (B.hsVec ((∑ π', ∑ ρ', c π' ρ' • (Qd ρ').comp (T0.comp (Qd π'))) (e π))) =
      c π ρ * inner ℂ (B.hsVec (e ρ)) (B.hsVec (T0 (e π))) := by
  have h := mat_gen Qd T0 c e hQadj hline π ρ
  unfold B.hsInner at h
  rw [← h]
  congr 2
  simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply,
    ContinuousLinearMap.comp_apply]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sandw_apply (A : Wp →L[ℂ] Wp) (B' : Wq →L[ℂ] Wq) (X : Wq →L[ℂ] Wp) : sandw A B' X = A.comp (X.comp B') := rfl

end gen

/- English proof (translation)
Take `⟨K, hK, hTP⟩` from `hTP`. Use `⟨K, hK, ?_⟩` and prove the remaining obligations. Introduce `Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl`. Establish `hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π'` using `(hB.1.2.2.2.1.2 v).2.2.2.1`. Establish `hk : 2 ≤ S.G.k`.

Use `(Finset.mem_Icc.1 hl)` as an intermediate fact. Establish `h2 : (D.parOf S v).k = S.G.k` using `rfl`. Use linear arithmetic over natural numbers and integers. Take `⟨Qp, hQs, hQadj, hQeq, hQline⟩` from `hTP Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ`. Take `⟨Bw, hBw⟩` from `Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z_mem (T v).base.T_pos`.

Take `⟨Bw', hBw'⟩` from `Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z'_mem (T v).base.T'_pos`. Take `⟨hc, hca, hadj, heqv, hph⟩` from `hTF (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl Bw Bw' hBw hBw'`. Take `⟨κ, hκ⟩` from `hTG Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk l hl Bw Bw' hBw hBw'`. Use `set th := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hth`. Use `set thA := thtA S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hthA`.

Use `⟨fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then κ π else 0) • (Qp ρ a).comp ((th a a' ι).comp (Qp π a)), fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then conj (κ π) else 0) • (Qp π a).comp ((thA a a' ι).comp (Qp ρ a)), ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_` and prove the remaining obligations. Conclude with `cd_comp ((hQs ρ).comp contDiff_fst) (cd_comp hc ((hQs π).comp contDiff_fst))`. Use `ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_` and prove the remaining obligations. Conclude with `cd_comp ((hQs π).comp contDiff_fst) (cd_comp hca ((hQs ρ).comp contDiff_fst))`.

Introduce `a a' ι A B'`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]`. Rewrite using `[kap_hsInner_sum_left, kap_hsInner_sum_right]`. Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Rewrite using `[kap_hsInner_sum_left, kap_hsInner_sum_right]`.

Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[kap_hsInner_smul_left, kap_hsInner_smul_right, hQadj, hadj, hQadj]`. Use `congr 1`. Apply the tactic sequence `split_ifs <;> simp`. Introduce `h hh h' hh' a a' ι X`.

Establish `hsum : ∀ (F : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) → ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))), ((T v).base.π h).comp (((∑ π, ∑ ρ, F π ρ) X).comp ((T v).base.π' h'⁻¹)) = ∑ π, ∑ ρ, ((T v).base.π h).comp ((F π ρ X).comp ((T v).base.π' h'⁻¹))`. Introduce `F`. Use `map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun π => (∑ ρ, F π ρ) X) Finset.univ` as an intermediate fact. Simplify using `only [sandw_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at this ⊢`. Rewrite using `[this]`.

Use `Finset.sum_congr rfl fun π _ => ?_` and prove the remaining obligations. Conclude with `map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun ρ => F π ρ X) Finset.univ`. Prove the components needed by the constructor for the conclusion. Rewrite using `[hsum]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]`.

Use `Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[hQeq π h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).1, hQeq ρ h hh h' hh' a _]`. Apply the tactic sequence `split_ifs <;> ext y <;> simp`. Rewrite using `[hsum]`. Simplify using `only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]`.

Use `Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Rewrite using `[hQeq ρ h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).2, hQeq π h hh h' hh' a _]`. Apply the tactic sequence `split_ifs <;> ext y <;> simp`. Introduce `q hq ρ π`. Establish `hq1 : ∀ a, q.1 a ≠ 0` using `hq.1`.

Establish `hζ : (D.parOf S v).TT < Complex.normSq q.2` using `hq.2`. Establish `hline` using `hQline q hq`. Use `(mat_gen' (fun σ => Qp σ (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)) (th (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2) (conj (SSn.phD q.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μse …` and prove the remaining obligations. Rewrite using `[hph (SSn.phD q.1), ContinuousLinearMap.smul_apply, inner_hs_smul]`. Unfold `SSn.ssnV`.

Use `split_ifs with hup`. Establish `h1` using `hκ q.2 hζ π ρ hup`. Rewrite using `[← conj_phD_sq hq1]`. Take the linear combination `(conj (SSn.phD q.1)) ^ 2 * h1`. Simplify using the standard rewrite rules.
-/
theorem ssnRep_of (hTP : TypeProj) (hTF : ThtFacts) (hTG : ThtGaugeConst) : SSnRep := by
  obtain ⟨K, hK, hTP⟩ := hTP
  refine ⟨K, hK, ?_⟩
  intro Cc hCc E _ _ _ Wp Wq _ _ _ _ _ _ S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ l hl
  have hPl : Q.IsPlace (D.parOf S v) (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' :=
    (hB.1.2.2.2.1.2 v).2.2.2.1
  have hk : 2 ≤ S.G.k := by
    have := (Finset.mem_Icc.1 hl)
    have h2 : (D.parOf S v).k = S.G.k := rfl
    omega
  obtain ⟨Qp, hQs, hQadj, hQeq, hQline⟩ := hTP Cc hCc E Wp Wq S T f χ ν' m₀ top A₀ hB v e hFr hGa hQQ
  obtain ⟨Bw, hBw⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z_mem (T v).base.T_pos
  obtain ⟨Bw', hBw'⟩ := Formalism.FourierDecayAlt.P.Qx8.frame_exists (T v).base.z'_mem (T v).base.T'_pos
  obtain ⟨hc, hca, hadj, heqv, hph⟩ := hTF (Wp (S.pl v)) (Wq (S.pl v)) (D.parOf S v) (T v).base hPl Bw Bw' hBw hBw'
  obtain ⟨κ, hκ⟩ := hTG Cc E Wp Wq S T f χ ν' m₀ top A₀ v e ⟨hB, hFr, hGa, hQQ⟩ hk l hl Bw Bw' hBw hBw'
  classical
  set th := tht S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hth
  set thA := thtA S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.π (T v).base.π' Bw Bw' with hthA
  refine ⟨fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then κ π else 0) •
      (Qp ρ a).comp ((th a a' ι).comp (Qp π a)),
    fun a a' ι => ∑ π, ∑ ρ, (if M.Up (D.parOf S v) l π ρ then conj (κ π) else 0) •
      (Qp π a).comp ((thA a a' ι).comp (Qp ρ a)), ?_, ?_, ?_, ?_, ?_⟩
  ·
    refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs ρ).comp contDiff_fst) (cd_comp hc ((hQs π).comp contDiff_fst))
  · refine ContDiff.sum fun π _ => ContDiff.sum fun ρ _ => ContDiff.const_smul _ ?_
    exact cd_comp ((hQs π).comp contDiff_fst) (cd_comp hca ((hQs ρ).comp contDiff_fst))
  ·
    intro a a' ι A B'
    simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun π _ => ?_
    rw [kap_hsInner_sum_left, kap_hsInner_sum_right]
    refine Finset.sum_congr rfl fun ρ _ => ?_
    rw [kap_hsInner_smul_left, kap_hsInner_smul_right, hQadj, hadj, hQadj]
    congr 1
    split_ifs <;> simp
  ·
    intro h hh h' hh' a a' ι X
    have hsum : ∀ (F : M.Ty (D.parOf S v) → M.Ty (D.parOf S v) →
        ((Wq (S.pl v) →L[ℂ] Wp (S.pl v)) →L[ℂ] (Wq (S.pl v) →L[ℂ] Wp (S.pl v)))),
        ((T v).base.π h).comp (((∑ π, ∑ ρ, F π ρ) X).comp ((T v).base.π' h'⁻¹)) =
          ∑ π, ∑ ρ, ((T v).base.π h).comp ((F π ρ X).comp ((T v).base.π' h'⁻¹)) := by
      intro F
      have := map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun π => (∑ ρ, F π ρ) X) Finset.univ
      simp only [sandw_apply, ContinuousLinearMap.coe_sum', Finset.sum_apply] at this ⊢
      rw [this]
      refine Finset.sum_congr rfl fun π _ => ?_
      exact map_sum (sandw ((T v).base.π h) ((T v).base.π' h'⁻¹)) (fun ρ => F π ρ X) Finset.univ
    constructor
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq π h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).1, hQeq ρ h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
    · rw [hsum]
      simp only [ContinuousLinearMap.coe_sum', Finset.sum_apply, ContinuousLinearMap.coe_smul', Pi.smul_apply, ContinuousLinearMap.comp_apply]
      refine Finset.sum_congr rfl fun π _ => Finset.sum_congr rfl fun ρ _ => ?_
      rw [hQeq ρ h hh h' hh' a X, (heqv h hh h' hh' a a' ι _).2, hQeq π h hh h' hh' a _]
      split_ifs <;> ext y <;> simp
  ·
    intro q hq ρ π
    have hq1 : ∀ a, q.1 a ≠ 0 := hq.1
    have hζ : (D.parOf S v).TT < Complex.normSq q.2 := hq.2
    have hline := hQline q hq
    refine (mat_gen' (fun σ => Qp σ (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (th (SSn.phD q.1 • SSn.nu0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (conj (SSn.phD q.1) • SSn.nu0' S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2)
        (SSn.io0 S.G.k S.G.r (T v).base.z (T v).base.z' (T v).base.μsec q.2))
      (fun π' ρ' => if M.Up (D.parOf S v) l π' ρ' then κ π' else 0) (fun σ => e σ q.2)
      (fun σ => hQadj σ _) hline π ρ).trans ?_
    rw [hph (SSn.phD q.1), ContinuousLinearMap.smul_apply, inner_hs_smul]
    unfold SSn.ssnV
    split_ifs with hup
    · have h1 := hκ q.2 hζ π ρ hup
      rw [← conj_phD_sq hq1]
      linear_combination (conj (SSn.phD q.1)) ^ 2 * h1
    · simp

/- English proof (translation)
Introduce `hPE hGL hTF hDU hTG` and use `ssnRep_of (typeProj_of hPE hGL hDU weighted_norm_facts_hold) hTF hTG`.
-/
theorem second_shift_representation_assembly : SSnRepOfCut := fun hPE hGL hTF hDU hTG =>
  ssnRep_of (typeProj_of hPE hGL hDU weighted_norm_facts_hold) hTF hTG

end

end Formalism.FourierDecayAlt.P.CutMP.JA.SSn.Rep
