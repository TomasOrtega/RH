import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTRRMatFrom
import Formalism.HermitianCurvature.HermitianCurvatureProofs.CutGCoreGTConnGaugeB

open Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.Gauge.GC

noncomputable section

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

namespace RRFin

/- English proof (translation)
Establish `h` using `(((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp`. Simplify using `using h`.
-/
theorem hasDerivAt_rotExp (m : ℂ) :
    HasDerivAt (fun φ : ℝ => Complex.exp (m * (φ : ℂ) * Complex.I)) (m * Complex.I) 0 := by
  have h := (((hasDerivAt_id (0 : ℝ)).ofReal_comp.const_mul m).mul_const Complex.I).cexp
  simpa using h

end RRFin

open RRMat RRFin in
/- English proof (translation)
Introduce `hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ`. Establish `hB` using `SSTr.radBase P Bs hpl`. Establish `hTT0 : 0 ≤ P.TT`. Rewrite using `[← SSTr.tz_eq P Bs hpl]`. Conclude with `mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le`.

Use `set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef`. Establish `heE : ∀ σ ζ, e σ ζ = E σ` using `fun σ ζ => hc σ ζ 0`. Establish `hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P)` using `contDiff_id.contDiffOn`. Establish `hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P)`. Establish `h : (fun w : ℂ => star w) = ⇑Complex.conjCLE` using `by funext w; simp`.

Rewrite using `[h]`. Conclude with `Complex.conjCLE.contDiff.contDiffOn`. Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `q`. Simplify using `only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply, Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]`.

Rewrite using `[dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]`. Establish `hcq : q.1.1 ∈ OmX P.r` using `q.2.1`. Establish `hζq : P.TT < Complex.normSq q.1.2` using `q.2.2`. Establish `hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT)` using `(trR P Bs e Φ ρ).2`. Establish `hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1` using `(hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)`.

Establish `hWa` using `hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff`. Establish `hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈ NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))`. Introduce `φ`. Establish `hm` using `Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2`. Establish `hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z'` using `⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩`.

Establish `h2` using `hm.2.1 _ hx`. Simplify using `only [NF.radR, Set.indicator_of_mem hx] at h2`. Conclude with `h2`. Establish `hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) = Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μs …`. Introduce `φ`.

Establish `hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))` using `by rw [normSq_rot]; exact hζq`. Establish `hexp` using `(he.2 _ hζe).2.2 _ (hfibq φ)`. Simplify using `only [heE] at hexp`. Establish `hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) = if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0` using `fun σ => hn φ ρ σ`. Rewrite using `[rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]`.

Use `conv_lhs => rw [hexp]`. Rewrite using `[rotA_sum, SSTr.hsVec_sum, inner_sum]`. Simplify using `only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree. Establish `hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z'` using `Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩`.

Establish `hG` using `hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1`. Simplify using `only [one_mul] at hG`. Establish `hE` using `hasDerivAt_rotExp (-(n ρ : ℂ))`. Establish `hprod` using `(hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)`. Establish `hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) = ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k …`.

Introduce `φ`. Establish `hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT` using `⟨hcq, by rw [normSq_rot]; exact hζq⟩`. Unfold `MA.ext`. Rewrite using `[dif_pos hmem, SSTr.trR_apply P Bs hpl hk2 e he]`. Simplify using `only [rawR]`.

Rewrite using `[wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]`. Establish `h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0` using `by ring`. Rewrite using `[h0, Complex.exp_zero, one_mul]`. Establish `hF` using `hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)`. Establish `heq` using `hWa.unique hF`.

Establish `hsum` using `hRt Φ _ hD`. Simplify using `only at hsum`. Establish `hG0` using `hGy 0`. Simplify using `only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq`. Rewrite using `[SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]`.

Simplify using `only [rawR]`. Rewrite `heq` using `[hG0]`. Rewrite using `[heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]`. Use `push_cast`. Apply `mul_left_cancel₀ Complex.I_ne_zero` to reduce the goal to its premises.

Take the linear combination `-heq`.
-/
theorem rotation_finite_from_matrix : GTRRFinFrom := by
  intro hC hS hW Wp Wq _ _ _ _ _ _ P Bs hpl hk2 hsec e he hc n hn Rt s hRt ρ Φ
  have hB := SSTr.radBase P Bs hpl
  have hTT0 : 0 ≤ P.TT := by
    rw [← SSTr.tz_eq P Bs hpl]; exact mul_nonneg hB.2.2.2.1.le hB.2.2.2.2.1.le
  set E : M.Ty P → (Wq →L[ℂ] Wp) := fun σ => e σ 0 with hEdef
  have heE : ∀ σ ζ, e σ ζ = E σ := fun σ ζ => hc σ ζ 0
  have hid : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => w) (Ann P) := contDiff_id.contDiffOn
  have hstar : ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun w : ℂ => star w) (Ann P) :=
    by
      have h : (fun w : ℂ => star w) = ⇑Complex.conjCLE := by funext w; simp
      rw [h]; exact Complex.conjCLE.contDiff.contDiffOn
  apply Subtype.ext
  funext q
  simp only [AddSubgroupClass.coe_sub, AddMemClass.coe_add, MulMemClass.coe_mul, SetLike.val_smul, Pi.add_apply,
    Pi.sub_apply, Pi.mul_apply, Pi.smul_apply, smul_eq_mul]
  rw [dzQ_apply P hTT0, dzbQ_apply P hTT0, fnZ_val P hid, fnZ_val P hstar]
  have hcq : q.1.1 ∈ OmX P.r := q.2.1
  have hζq : P.TT < Complex.normSq q.1.2 := q.2.2

  have hsm : ContDiffOn ℝ MA.sm (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) (MA.Qset P.r P.TT) :=
    (trR P Bs e Φ ρ).2
  have hdiff : DifferentiableAt ℝ (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 :=
    (hsm.differentiableOn (by simp [MA.sm])).differentiableAt ((MA.Qset_open P.r P.TT).mem_nhds q.2)
  have hWa := hW P.r (MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ)) q.1 hdiff

  have hfibq : ∀ φ : ℝ, (Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
      (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))) ∈
        NF.Fib P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by
    intro φ
    have hm := Formalism.FourierDecayAlt.P.radical_reduction_mem Wp Wq P.k P.r Bs.z Bs.z' Bs.μsec Bs.π Bs.π' hB Φ.1 Φ.2
    have hx : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : (Fin P.r → ℂ) × ℂ) ∈ NF.QR P.k P.r Bs.z Bs.z' :=
      ⟨hcq, by rw [normSq_rot]; exact ann_tz P Bs hpl hζq⟩
    have h2 := hm.2.1 _ hx
    simp only [NF.radR, Set.indicator_of_mem hx] at h2
    exact h2
  have hGy : ∀ φ : ℝ, inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
        (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ))) =
      Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) * inner ℂ (B.hsVec (E ρ)) (B.hsVec
        ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1 (NF.muZ P.k P.r Bs.μsec (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I))))) := by
    intro φ
    have hζe : P.TT < Complex.normSq (q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) := by rw [normSq_rot]; exact hζq
    have hexp := (he.2 _ hζe).2.2 _ (hfibq φ)
    simp only [heE] at hexp
    have hM : ∀ σ, inner ℂ (B.hsVec (E ρ)) (B.hsVec (rotA P Bs φ (E σ))) =
        if ρ = σ then Complex.exp ((n ρ : ℂ) * (φ : ℂ) * Complex.I) else 0 := fun σ => hn φ ρ σ
    rw [rot_eqv hS P Bs hpl hsec Φ q.1.1 hcq q.1.2 hζq φ]
    conv_lhs => rw [hexp]
    rw [rotA_sum, SSTr.hsVec_sum, inner_sum]
    simp only [VLem.hsV_smul, inner_smul_right, hM, mul_ite, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
    ring

  have hD : ((q.1.1, NF.muZ P.k P.r Bs.μsec q.1.2) : (Fin P.r → ℂ) × Q.Mx P.k P.r) ∈ Q.DomR P.k P.r Bs.z Bs.z' :=
    Formalism.FourierDecayAlt.P.NFRadRedA.mem_domR hB.2.1 hB.2.2.1 hB.2.2.2.2.2.1 (q := q.1) ⟨hcq, ann_tz P Bs hpl hζq⟩
  have hG := hasDerivAt_pair hC P Bs Φ _ hD (E ρ) 1
  simp only [one_mul] at hG
  have hE := hasDerivAt_rotExp (-(n ρ : ℂ))
  have hprod := (hE.mul hG).const_mul ((wR P.k P.TT q.1.2 : ℝ) : ℂ)
  have hpt : ∀ φ : ℝ, MA.ext (trR P Bs e Φ ρ : MA.Qp P.r P.TT → ℂ) (q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) =
      ((wR P.k P.TT q.1.2 : ℝ) : ℂ) * (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I) *
        inner ℂ (B.hsVec (E ρ)) (B.hsVec ((Φ : Q.Fn P.k P.r (Wq →L[ℂ] Wp)) q.1.1
          (NF.muZ P.k P.r Bs.μsec q.1.2 * zc P.k P.r φ)))) := by
    intro φ
    have hmem : ((q.1.1, q.1.2 * Complex.exp ((φ : ℂ) * Complex.I)) : MA.E P.r) ∈ MA.Qset P.r P.TT :=
      ⟨hcq, by rw [normSq_rot]; exact hζq⟩
    unfold MA.ext
    rw [dif_pos hmem, SSTr.trR_apply P Bs hpl hk2 e he]
    simp only [rawR]
    rw [wR_rot, heE, hGy φ, ← mul_assoc (Complex.exp (-(n ρ : ℂ) * (φ : ℂ) * Complex.I)), ← Complex.exp_add]
    have h0 : -(n ρ : ℂ) * (φ : ℂ) * Complex.I + (n ρ : ℂ) * (φ : ℂ) * Complex.I = 0 := by ring
    rw [h0, Complex.exp_zero, one_mul]
  have hF := hprod.congr_of_eventuallyEq (Filter.Eventually.of_forall hpt)
  have heq := hWa.unique hF

  have hsum := hRt Φ _ hD
  simp only at hsum
  have hG0 := hGy 0
  simp only [Complex.ofReal_zero, mul_zero, zero_mul, Complex.exp_zero, one_mul, mul_one] at hG0 heq
  rw [SSTr.trR_apply P Bs hpl hk2 e he, SSTr.trR_apply P Bs hpl hk2 e he]
  simp only [rawR]
  rw [hG0] at heq
  rw [heE, hsum, VLem.hsV_add, inner_add_right, VLem.hsV_smul, inner_smul_right]
  push_cast
  apply mul_left_cancel₀ Complex.I_ne_zero
  linear_combination -heq

end

end Formalism.FourierDecayAlt.P.CutMP.Gauge.GC
