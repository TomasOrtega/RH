import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.WeightFunctionOnFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.CuspidalExponentialDecay
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.FundamentalDomains.BoundedSectionAlgebra

open NumberField ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR ReciprocityTheory.ChartRestriction.G.AR.Inst ReciprocityTheory.ChartRestriction.G.AR.Up ReciprocityTheory.L2DbarEstimates MeasureTheory Topology
open scoped ContDiff ENNReal Matrix

namespace GlobalTheory.LeadBound

open ReciprocityTheory.ChartRestriction.G.FD.BoundedSectionAlgebra

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

section

variable {r : ℕ} (X : Data E r) (g : Frame X.Ψ r → ℝ)

def IsDom (la : Wt X.Ψ r) (n : ℕ) (P : Frame X.Ψ r → ℂ) : Prop :=
  X.IsBddSec la P ∧ ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm la P x ≤ C * g x ^ n

variable {X g}

/- English proof (translation)
Take `⟨C, hC⟩` from `h.2`. Conclude with `⟨h, C, fun x hx => by simpa using hC x hx⟩`.
-/
theorem IsDom.of_bdd {la : Wt X.Ψ r} {P : Frame X.Ψ r → ℂ} (h : X.IsBddSec la P) :
    IsDom X g la 0 P := by
  obtain ⟨C, hC⟩ := h.2
  exact ⟨h, C, fun x hx => by simpa using hC x hx⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨bdd_zero X la, 0, fun x _ => by simp [Data.pnorm]⟩`.
-/
theorem IsDom.zero (la : Wt X.Ψ r) (n : ℕ) : IsDom X g la n 0 :=
  ⟨bdd_zero X la, 0, fun x _ => by simp [Data.pnorm]⟩

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Take `⟨C', hC'⟩` from `hQ.2`. Use `⟨bdd_add X hP.1 hQ.1, C + C', fun x hx => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsDom.add {la : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la n Q) : IsDom X g la n (P + Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_add X hP.1 hQ.1, C + C', fun x hx => ?_⟩
  calc X.pnorm la (P + Q) x ≤ (‖P x‖ + ‖Q x‖) * X.nfac la x :=
        mul_le_mul_of_nonneg_right (norm_add_le _ _) (nfac_nonneg X la x)
    _ = X.pnorm la P x + X.pnorm la Q x := by rw [add_mul]; rfl
    _ ≤ C * g x ^ n + C' * g x ^ n := add_le_add (hC x hx) (hC' x hx)
    _ = (C + C') * g x ^ n := by ring

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Use `⟨bdd_smul X a hP.1, ‖a‖ * C, fun x hx => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pnorm_eq, pnorm_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]`. Use `_ ≤ ‖a‖ * (C * g x ^ n) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg a)`.

Use `_ = ‖a‖ * C * g x ^ n := by ring`.
-/
theorem IsDom.smul {la : Wt X.Ψ r} {n : ℕ} {P : Frame X.Ψ r → ℂ} (a : ℂ) (hP : IsDom X g la n P) :
    IsDom X g la n (a • P) := by
  obtain ⟨C, hC⟩ := hP.2
  refine ⟨bdd_smul X a hP.1, ‖a‖ * C, fun x hx => ?_⟩
  calc X.pnorm la (a • P) x = ‖a‖ * X.pnorm la P x := by
        rw [pnorm_eq, pnorm_eq, Pi.smul_apply, smul_eq_mul, norm_mul, mul_assoc]
    _ ≤ ‖a‖ * (C * g x ^ n) := mul_le_mul_of_nonneg_left (hC x hx) (norm_nonneg a)
    _ = ‖a‖ * C * g x ^ n := by ring

/- English proof (translation)
Take `⟨C, hC⟩` from `hP.2`. Take `⟨C', hC'⟩` from `hQ.2`. Use `⟨bdd_mul X hP.1 hQ.1, C * C', fun x hx => ?_⟩` and prove the remaining obligations. Establish `e : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x`. Rewrite using `[pnorm_eq, pnorm_eq, pnorm_eq, Pi.mul_apply, norm_mul, nfac_add X hx]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem IsDom.mul {la la' : Wt X.Ψ r} {n n' : ℕ} {P Q : Frame X.Ψ r → ℂ} (hP : IsDom X g la n P)
    (hQ : IsDom X g la' n' Q) : IsDom X g (la + la') (n + n') (P * Q) := by
  obtain ⟨C, hC⟩ := hP.2
  obtain ⟨C', hC'⟩ := hQ.2
  refine ⟨bdd_mul X hP.1 hQ.1, C * C', fun x hx => ?_⟩
  have e : X.pnorm (la + la') (P * Q) x = X.pnorm la P x * X.pnorm la' Q x := by
    rw [pnorm_eq, pnorm_eq, pnorm_eq, Pi.mul_apply, norm_mul, nfac_add X hx]
    ring
  rw [e]
  calc X.pnorm la P x * X.pnorm la' Q x ≤ (C * g x ^ n) * (C' * g x ^ n') :=
        mul_le_mul (hC x hx) (hC' x hx) (pnorm_nonneg X _ _ _)
          ((pnorm_nonneg X _ _ _).trans (hC x hx))
    _ = C * C' * g x ^ (n + n') := by ring

/- English proof (translation)
The claim follows from `Finset.sum_induction P (IsDom X g la n) (fun _ _ ha hb => ha.add hb) (IsDom.zero la n) hP`.
-/
theorem IsDom.sum {ι : Type*} (S : Finset ι) {la : Wt X.Ψ r} {n : ℕ} {P : ι → Frame X.Ψ r → ℂ}
    (hP : ∀ i ∈ S, IsDom X g la n (P i)) : IsDom X g la n (∑ i ∈ S, P i) :=
  Finset.sum_induction P (IsDom X g la n) (fun _ _ ha hb => ha.add hb) (IsDom.zero la n) hP

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => simpa using hQ`. Consider the case `succ m ih`. Establish `h` using `ih.mul hP`. Rewrite `h` using `[add_assoc, ← succ_nsmul, add_assoc, mul_assoc, ← pow_succ]`. Then use the resulting hypothesis.
-/
theorem IsDom.mul_pow {la L : Wt X.Ψ r} {n : ℕ} {P Q : Frame X.Ψ r → ℂ} (hQ : IsDom X g la n Q)
    (hP : IsDom X g L 1 P) (m : ℕ) : IsDom X g (la + m • L) (n + m) (Q * P ^ m) := by
  induction m with
  | zero => simpa using hQ
  | succ m ih =>
    have h := ih.mul hP
    rwa [add_assoc, ← succ_nsmul, add_assoc, mul_assoc, ← pow_succ] at h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using hQ`. Consider the case `insert a S ha ih`. Establish `h` using `ih.mul_pow (hP a) (α a)`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), mul_comm (P a ^ α a), add_nsmul, ← add_assoc, ← add_assoc, ← mul_assoc]`.

Conclude with `h`.
-/
theorem IsDom.mul_prod {ι : Type*} (S : Finset ι) {la L : Wt X.Ψ r} {n : ℕ} {Q : Frame X.Ψ r → ℂ}
    {P : ι → Frame X.Ψ r → ℂ} (hQ : IsDom X g la n Q) (hP : ∀ i, IsDom X g L 1 (P i)) (α : ι → ℕ) :
    IsDom X g (la + (∑ i ∈ S, α i) • L) (n + ∑ i ∈ S, α i) (Q * ∏ i ∈ S, P i ^ α i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using hQ
  | insert a S ha ih =>
    have h := ih.mul_pow (hP a) (α a)
    rw [Finset.sum_insert ha, Finset.prod_insert ha, add_comm (α a), mul_comm (P a ^ α a), add_nsmul,
      ← add_assoc, ← add_assoc, ← mul_assoc]
    exact h

/- English proof (translation)
Use `⟨hP, Real.sqrt K, fun x hx => ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, ← Real.sqrt_mul' _ (hW x)]`. Conclude with `Real.le_sqrt_of_sq_le (hK x hx)`.
-/
theorem IsDom.of_sq_le {W : Frame X.Ψ r → ℝ} {la : Wt X.Ψ r}
    {P : Frame X.Ψ r → ℂ} (hP : X.IsBddSec la P) {K : ℝ} (hW : ∀ x, 0 ≤ W x)
    (hK : ∀ x ∈ X.dom, X.pnorm la P x ^ 2 ≤ K * W x) :
    IsDom X (fun x => Real.sqrt (W x)) la 1 P := by
  refine ⟨hP, Real.sqrt K, fun x hx => ?_⟩
  rw [pow_one, ← Real.sqrt_mul' _ (hW x)]
  exact Real.le_sqrt_of_sq_le (hK x hx)

end

/- English proof (translation)
Introduce `r X Xa Fl G T a δ ha t ht cc`. Use `set W : Frame X.Ψ r → ℝ := fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWdef`. Establish `hW : ∀ x, 0 ≤ W x` using `fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _`. Take `⟨K0, hK0⟩` from `Fl.denom_le_family`. Take `⟨K1, hK1⟩` from `Fl.s_le_w`.

Establish `hw0 : IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 Fl.w0` using `IsDom.of_sq_le Fl.weightForm_vanishes.1.1 hW hK0`. Establish `hs : ∀ k, IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 (Fl.s k)` using `fun k => IsDom.of_sq_le (Fl.s_van k).1.1 hW (K := K1) fun x hx => (Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Fl.s k) x ^ 2) (fun _ _ => sq_nonneg _) (Finset.mem_univ k)).trans (hK1 x hx)`. Establish `e : leadM X Fl.s Fl.w0 t T a cc = ∑ α ∈ multiLt (nd X) a, ∑ k, cc α k • (t k * (∏ q, Fl.s q ^ α q) * Fl.w0 ^ (T - ∑ q, α q))`. Use function extensionality and compare the values at `x`. Simplify using `only [leadM, monoM, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply, Pi.pow_apply, smul_eq_mul]`.

Use `Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Establish `hD : IsDom X (fun x => Real.sqrt (W x)) (G + T • Xa.L) T (leadM X Fl.s Fl.w0 t T a cc)`. Rewrite using `[e]`. Use `IsDom.sum _ fun α hα => IsDom.sum _ fun k _ => IsDom.smul _ ?_` and prove the remaining obligations.

Establish `hlt : ∑ q, α q < a`. Simplify `hα` using `[multiLt, Finset.Nat.mem_antidiagonalTuple]`. Establish `hle : ∑ q, α q ≤ T` using `by omega`. Establish `h` using `((IsDom.of_bdd (ht k)).mul_prod Finset.univ hs α).mul_pow hw0 (T - ∑ q, α q)`. Rewrite `h` using `[add_assoc, ← add_nsmul, zero_add, Nat.add_sub_cancel' hle]`. Then use the resulting hypothesis.

Take `⟨hb, C, hC⟩` from `hD`. Use `⟨hb, C ^ 2, fun x hx => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem main : ∀ (r : ℕ) (X : Data E r) (Xa : ArchInM X) (Fl : FlatM X Xa) (G : Wt X.Ψ r) (T a δ : ℕ), a ≤ T + 1 →
    ∀ (t : Fin δ → Frame X.Ψ r → ℂ), (∀ k, X.IsBddSec G (t k)) → ∀ cc : (Fin (nd X) → ℕ) → Fin δ → ℂ,
    X.IsBddSec (G + T • Xa.L) (leadM X Fl.s Fl.w0 t T a cc) ∧
    ∃ C : ℝ, ∀ x ∈ X.dom, X.pnorm (G + T • Xa.L) (leadM X Fl.s Fl.w0 t T a cc) x ^ 2 ≤
      C * (∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2) ^ T := by
  intro r X Xa Fl G T a δ ha t ht cc
  set W : Frame X.Ψ r → ℝ := fun x => ∑ k, X.pnorm Xa.L (Xa.w k) x ^ 2 with hWdef
  have hW : ∀ x, 0 ≤ W x := fun x => Finset.sum_nonneg fun _ _ => sq_nonneg _
  obtain ⟨K0, hK0⟩ := Fl.denom_le_family
  obtain ⟨K1, hK1⟩ := Fl.s_le_w
  have hw0 : IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 Fl.w0 :=
    IsDom.of_sq_le Fl.weightForm_vanishes.1.1 hW hK0
  have hs : ∀ k, IsDom X (fun x => Real.sqrt (W x)) Xa.L 1 (Fl.s k) := fun k =>
    IsDom.of_sq_le (Fl.s_van k).1.1 hW (K := K1) fun x hx =>
      (Finset.single_le_sum (f := fun k => X.pnorm Xa.L (Fl.s k) x ^ 2)
        (fun _ _ => sq_nonneg _) (Finset.mem_univ k)).trans (hK1 x hx)
  have e : leadM X Fl.s Fl.w0 t T a cc = ∑ α ∈ multiLt (nd X) a, ∑ k,
      cc α k • (t k * (∏ q, Fl.s q ^ α q) * Fl.w0 ^ (T - ∑ q, α q)) := by
    funext x
    simp only [leadM, monoM, Finset.sum_apply, Pi.smul_apply, Pi.mul_apply, Finset.prod_apply,
      Pi.pow_apply, smul_eq_mul]
    refine Finset.sum_congr rfl fun α _ => Finset.sum_congr rfl fun k _ => ?_
    ring
  have hD : IsDom X (fun x => Real.sqrt (W x)) (G + T • Xa.L) T (leadM X Fl.s Fl.w0 t T a cc) := by
    rw [e]
    refine IsDom.sum _ fun α hα => IsDom.sum _ fun k _ => IsDom.smul _ ?_
    have hlt : ∑ q, α q < a := by
      simpa [multiLt, Finset.Nat.mem_antidiagonalTuple] using hα
    have hle : ∑ q, α q ≤ T := by omega
    have h := ((IsDom.of_bdd (ht k)).mul_prod Finset.univ hs α).mul_pow hw0 (T - ∑ q, α q)
    rwa [add_assoc, ← add_nsmul, zero_add, Nat.add_sub_cancel' hle] at h
  obtain ⟨hb, C, hC⟩ := hD
  refine ⟨hb, C ^ 2, fun x hx => ?_⟩
  calc _ ≤ (C * Real.sqrt (W x) ^ T) ^ 2 :=
        pow_le_pow_left₀ (pnorm_nonneg X _ _ _) (hC x hx) 2
    _ = C ^ 2 * (Real.sqrt (W x) ^ 2) ^ T := by ring
    _ = C ^ 2 * W x ^ T := by rw [Real.sq_sqrt (hW x)]

end GlobalTheory.LeadBound
