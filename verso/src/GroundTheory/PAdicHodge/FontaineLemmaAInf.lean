import Mathlib
import GroundTheory.PAdicHodge.AInfXi
import GroundTheory.PAdicHodge.AInfTopology
set_option maxSynthPendingDepth 1

namespace GroundTheory.PAdicHodge

namespace AInf

open _root_.WittVector

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

/- English proof (translation)
Rewrite using `[pow_succ, RingAut.mul_apply, frobeniusEquiv_xi, map_sum, map_sum]`. Simplify using `only [map_pow, WittVector.frobeniusEquiv_pow_teichmuller, fontaineTheta_teichmuller, hε, one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`.
-/
theorem fontaineTheta_frobenius_pow_succ_xi {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ (n + 1)) (xi ε)) = p := by
  rw [pow_succ, RingAut.mul_apply, frobeniusEquiv_xi, map_sum, map_sum]
  simp only [map_pow, WittVector.frobeniusEquiv_pow_teichmuller, fontaineTheta_teichmuller, hε,
    one_pow, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one, WittVector.frobeniusEquiv_pow_teichmuller, map_sub, map_one, fontaineTheta_teichmuller, map_pow, hε, one_pow, sub_self]`.
-/
theorem fontaineTheta_frobenius_pow_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (n : ℕ) :
    θ ((φ ^ n) (mu ε)) = 0 := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_pow_teichmuller, map_sub, map_one,
    fontaineTheta_teichmuller, map_pow, hε, one_pow, sub_self]

/- English proof (translation)
Rewrite using `[map_mul, map_mul, fontaineTheta_frobenius_pow_mu hε, zero_mul]`.
-/
theorem fontaineTheta_frobenius_pow_mul_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) (b : AInf K p)
    (n : ℕ) : θ ((φ ^ n) (mu ε * b)) = 0 := by
  rw [map_mul, map_mul, fontaineTheta_frobenius_pow_mu hε, zero_mul]

/- English proof (translation)
Introduce `h`. Apply `norm_natCast_ne_zero hε hζ` to reduce the goal to its premises. Establish `h2 : ((p : 𝒪) : K) = (p : K)` using `by simp`. Rewrite using `[← h2, h, ZeroMemClass.coe_zero, norm_zero]`.
-/
theorem natCast_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : (p : 𝒪) ≠ 0 := by
  intro h
  apply norm_natCast_ne_zero hε hζ
  have h2 : ((p : 𝒪) : K) = (p : K) := by simp
  rw [← h2, h, ZeroMemClass.coe_zero, norm_zero]

variable (K p) in

noncomputable def kerThetaFrob : Ideal (AInf K p) :=
  ⨅ n : ℕ, RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ ^ n : AInf K p ≃+* AInf K p) : AInf K p →+* AInf K p))

/- English proof (translation)
Simplify using `only [kerThetaFrob, Ideal.mem_iInf, RingHom.mem_ker, RingHom.coe_comp, RingHom.coe_coe, Function.comp_apply]`.
-/
theorem mem_kerThetaFrob {a : AInf K p} : a ∈ kerThetaFrob K p ↔ ∀ n : ℕ, θ ((φ ^ n) a) = 0 := by
  simp only [kerThetaFrob, Ideal.mem_iInf, RingHom.mem_ker, RingHom.coe_comp, RingHom.coe_coe,
    Function.comp_apply]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => exact fun a _ => ⟨a, by rw [pow_zero, RingAut.one_apply, mul_comm]⟩`. Consider the case `succ N ih`. Introduce `a ha`. Establish `h0 : a ∈ RingHom.ker θ`.

Rewrite using `[RingHom.mem_ker]`. Simplify using `using ha 0`. Rewrite `h0` using `[ker_fontaineTheta_eq_span_xi hε hζ, Ideal.mem_span_singleton']`. Take `⟨a₁, rfl⟩` from `h0`. Establish `hp0` using `natCast_ne_zero hε hζ`.

Establish `h1 : ∀ n : ℕ, θ ((φ ^ n) (φ a₁)) = 0`. Introduce `n`. Establish `h` using `ha (n + 1)`. Rewrite `h` using `[map_mul, map_mul, fontaineTheta_frobenius_pow_succ_xi hε n, mul_eq_zero]`. Rewrite using `[← RingAut.mul_apply, ← pow_succ]`.

Conclude with `h.resolve_right hp0`. Take `⟨c, hc⟩` from `ih _ h1`. Use `⟨(φ).symm c, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg (φ).symm hc`. Rewrite `h2` using `[map_mul, map_mul, RingEquiv.symm_apply_apply]`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ', RingAut.mul_apply]`. Expand and normalize the polynomial expressions, which then agree. Use `_ = xi ε * ((φ).symm (mu ε) * (φ).symm c) := by rw [h2]`. Use `_ = mu ε * (φ).symm c := by conv_rhs => rw [mu_eq_xi_mul ε]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_mul_frobeniusEquiv_symm_pow_mu_eq {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) (N : ℕ) :
    ∀ a : AInf K p, (∀ n : ℕ, θ ((φ ^ n) a) = 0) →
      ∃ c : AInf K p, a * ((φ).symm ^ N) (mu ε) = mu ε * c := by
  induction N with
  | zero => exact fun a _ => ⟨a, by rw [pow_zero, RingAut.one_apply, mul_comm]⟩
  | succ N ih =>
    intro a ha
    have h0 : a ∈ RingHom.ker θ := by
      rw [RingHom.mem_ker]
      simpa using ha 0
    rw [ker_fontaineTheta_eq_span_xi hε hζ, Ideal.mem_span_singleton'] at h0
    obtain ⟨a₁, rfl⟩ := h0
    have hp0 := natCast_ne_zero hε hζ
    have h1 : ∀ n : ℕ, θ ((φ ^ n) (φ a₁)) = 0 := by
      intro n
      have h := ha (n + 1)
      rw [map_mul, map_mul, fontaineTheta_frobenius_pow_succ_xi hε n, mul_eq_zero] at h
      rw [← RingAut.mul_apply, ← pow_succ]
      exact h.resolve_right hp0
    obtain ⟨c, hc⟩ := ih _ h1
    refine ⟨(φ).symm c, ?_⟩
    have h2 := congrArg (φ).symm hc
    rw [map_mul, map_mul, RingEquiv.symm_apply_apply] at h2
    calc a₁ * xi ε * ((φ).symm ^ (N + 1)) (mu ε)
        = xi ε * (a₁ * (φ).symm (((φ).symm ^ N) (mu ε))) := by
          rw [pow_succ', RingAut.mul_apply]; ring
      _ = xi ε * ((φ).symm (mu ε) * (φ).symm c) := by rw [h2]
      _ = mu ε * (φ).symm c := by
          conv_rhs => rw [mu_eq_xi_mul ε]
          ring

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one]`. Conclude with `congrArg (· - 1) (teichmuller_coeff_zero p ε)`.
-/
theorem constantCoeff_mu (ε : 𝒪♭) : WittVector.constantCoeff (mu ε : AInf K p) = ε - 1 := by
  rw [mu, map_sub, map_one]
  exact congrArg (· - 1) (teichmuller_coeff_zero p ε)

/- English proof (translation)
Rewrite using `[frobeniusEquiv_symm_pow_mu, map_sub, map_one]`. Conclude with `congrArg (· - 1) (teichmuller_coeff_zero p _)`.
-/
theorem constantCoeff_frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (N : ℕ) :
    WittVector.constantCoeff (((φ).symm ^ N) (mu ε) : AInf K p) =
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1 := by
  rw [frobeniusEquiv_symm_pow_mu, map_sub, map_one]
  exact congrArg (· - 1) (teichmuller_coeff_zero p _)

/- English proof (translation)
Rewrite using `[← norm_pow, sub_pow_char_pow, one_pow, frobeniusEquiv_symm_pow_apply_pow]`.
-/
theorem norm_frobeniusEquiv_symm_pow_sub_one_pow (ε : 𝒪♭) (N : ℕ) :
    ‖((_root_.frobeniusEquiv 𝒪♭ p).symm ^ N) ε - 1‖ ^ p ^ N = ‖ε - 1‖ := by
  rw [← norm_pow, sub_pow_char_pow, one_pow, frobeniusEquiv_symm_pow_apply_pow]

/- English proof (translation)
Rewrite using `[preTilt_dvd_iff_norm_le]`. Use `set r := ‖ε - 1‖ with hr`. Use `set x := ‖WittVector.constantCoeff a‖ with hx`. Establish `hr0 : 0 < r` using `norm_pos_iff.2 (sub_ne_zero.2 (ne_one_of_untilt_ne_one hζ))`. Establish `key : ∀ N : ℕ, x ^ p ^ N * r ≤ r ^ p ^ N`.

Introduce `N`. Take `⟨c, hc⟩` from `exists_mul_frobeniusEquiv_symm_pow_mu_eq hε hζ N a ha`. Establish `h` using `congrArg (fun y : AInf K p => ‖WittVector.constantCoeff y‖ ^ p ^ N) hc`. Simplify using `only [map_mul, norm_mul, mul_pow, constantCoeff_mu, constantCoeff_frobeniusEquiv_symm_pow_mu, norm_frobeniusEquiv_symm_pow_sub_one_pow] at h`. Rewrite using `[h]`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `pow_le_one₀ (norm_nonneg _) (preTilt_norm_le_one _)`. Use `_ = r ^ p ^ N := mul_one _`. Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`.

Use `set q := x / r with hq`. Establish `hq1 : 1 < q` using `by rw [hq, one_lt_div hr0]; exact hlt`. Establish `hbound : ∀ N : ℕ, q ^ p ^ N * r ≤ 1`. Introduce `N`. Establish `h` using `key N`.

Establish `hxq : x = q * r` using `by rw [hq, div_mul_cancel₀ _ hr0.ne']`. Rewrite `h` using `[hxq, mul_pow]`. Establish `hrN : 0 < r ^ p ^ N` using `pow_pos hr0 _`. Use the polynomial consequences of the given equalities and inequalities. Take `⟨N, hN⟩` from `exists_nat_gt (1 / (r * (q - 1)))`.

Establish `hpN : (N : ℝ) < (p ^ N : ℕ)` using `by exact_mod_cast Nat.lt_pow_self hp.out.one_lt`. Establish `hB` using `one_add_mul_le_pow (a := q - 1) (by linarith) (p ^ N)`. Rewrite `hB` using `[add_sub_cancel]`. Establish `h3` using `hbound N`. Establish `hq0 : 0 < q - 1` using `by linarith`.

Establish `h4 : (1 : ℝ) / (r * (q - 1)) < ((p ^ N : ℕ) : ℝ)` using `hN.trans hpN`. Rewrite `h4` using `[div_lt_iff₀ (mul_pos hr0 hq0)]`. Move the coercions through the operations in `at h4 hB`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem sub_one_dvd_coeff_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : ε - 1 ∣ WittVector.constantCoeff a := by
  rw [preTilt_dvd_iff_norm_le]
  set r := ‖ε - 1‖ with hr
  set x := ‖WittVector.constantCoeff a‖ with hx
  have hr0 : 0 < r := norm_pos_iff.2 (sub_ne_zero.2 (ne_one_of_untilt_ne_one hζ))
  have key : ∀ N : ℕ, x ^ p ^ N * r ≤ r ^ p ^ N := by
    intro N
    obtain ⟨c, hc⟩ := exists_mul_frobeniusEquiv_symm_pow_mu_eq hε hζ N a ha
    have h := congrArg (fun y : AInf K p => ‖WittVector.constantCoeff y‖ ^ p ^ N) hc
    simp only [map_mul, norm_mul, mul_pow, constantCoeff_mu,
      constantCoeff_frobeniusEquiv_symm_pow_mu, norm_frobeniusEquiv_symm_pow_sub_one_pow] at h
    rw [h]
    calc r ^ p ^ N * ‖WittVector.constantCoeff c‖ ^ p ^ N ≤ r ^ p ^ N * 1 := by
          gcongr
          exact pow_le_one₀ (norm_nonneg _) (preTilt_norm_le_one _)
      _ = r ^ p ^ N := mul_one _
  by_contra hlt
  push_neg at hlt
  set q := x / r with hq
  have hq1 : 1 < q := by rw [hq, one_lt_div hr0]; exact hlt
  have hbound : ∀ N : ℕ, q ^ p ^ N * r ≤ 1 := by
    intro N
    have h := key N
    have hxq : x = q * r := by rw [hq, div_mul_cancel₀ _ hr0.ne']
    rw [hxq, mul_pow] at h
    have hrN : 0 < r ^ p ^ N := pow_pos hr0 _
    nlinarith
  obtain ⟨N, hN⟩ := exists_nat_gt (1 / (r * (q - 1)))
  have hpN : (N : ℝ) < (p ^ N : ℕ) := by exact_mod_cast Nat.lt_pow_self hp.out.one_lt
  have hB := one_add_mul_le_pow (a := q - 1) (by linarith) (p ^ N)
  rw [add_sub_cancel] at hB
  have h3 := hbound N
  have hq0 : 0 < q - 1 := by linarith
  have h4 : (1 : ℝ) / (r * (q - 1)) < ((p ^ N : ℕ) : ℝ) := hN.trans hpN
  rw [div_lt_iff₀ (mul_pos hr0 hq0)] at h4
  push_cast at h4 hB
  nlinarith

/- English proof (translation)
Establish `hp0` using `natCast_ne_zero hε hζ`. Establish `hJ : kerThetaFrob K p ≤ Ideal.span {mu ε}`. Use `le_span_singleton_of_forall_mem_eq (π := (p : AInf K p)) fun x hx => ?_` and prove the remaining obligations. Rewrite `hx` using `[mem_kerThetaFrob]`. Take `⟨β, hβ⟩` from `sub_one_dvd_coeff_zero hε hζ hx`.

Take `⟨v, hv⟩` from `exists_eq_teichmuller_add_mul_p (x - mu ε * teichmuller p β)`. Establish `h0 : (x - mu ε * teichmuller p β).coeff 0 = 0`. Express the relevant statement in the definitionally equal form `_root_.WittVector.constantCoeff (x - mu ε * teichmuller p β) = 0`. Rewrite using `[map_sub, map_mul, constantCoeff_mu, hβ]`. Express the relevant statement in the definitionally equal form `_ - _ * (teichmuller p β).coeff 0 = 0`.

Rewrite using `[teichmuller_coeff_zero, sub_self]`. Rewrite `hv` using `[h0, teichmuller_zero, zero_add]`. Establish `hxv : x = teichmuller p β * mu ε + v * p` using `by linear_combination hv`. Use `⟨teichmuller p β, v, ?_, hxv⟩` and prove the remaining obligations. Rewrite using `[mem_kerThetaFrob]`.

Introduce `n`. Establish `h` using `hx n`. Rewrite `h` using `[hxv, map_add, map_add, map_mul, map_mul, map_mul, map_mul, fontaineTheta_frobenius_pow_mu hε, mul_zero, zero_add, map_natCast, map_natCast, mul_eq_zero]`. Conclude with `h.resolve_right hp0`. Conclude with `hJ (mem_kerThetaFrob.2 ha)`.
-/
theorem mem_span_mu_of_forall {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {a : AInf K p}
    (ha : ∀ n : ℕ, θ ((φ ^ n) a) = 0) : a ∈ Ideal.span {mu ε} := by
  have hp0 := natCast_ne_zero hε hζ
  have hJ : kerThetaFrob K p ≤ Ideal.span {mu ε} := by
    refine le_span_singleton_of_forall_mem_eq (π := (p : AInf K p)) fun x hx => ?_
    rw [mem_kerThetaFrob] at hx
    obtain ⟨β, hβ⟩ := sub_one_dvd_coeff_zero hε hζ hx
    obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p (x - mu ε * teichmuller p β)
    have h0 : (x - mu ε * teichmuller p β).coeff 0 = 0 := by
      change _root_.WittVector.constantCoeff (x - mu ε * teichmuller p β) = 0
      rw [map_sub, map_mul, constantCoeff_mu, hβ]
      change _ - _ * (teichmuller p β).coeff 0 = 0
      rw [teichmuller_coeff_zero, sub_self]
    rw [h0, teichmuller_zero, zero_add] at hv
    have hxv : x = teichmuller p β * mu ε + v * p := by linear_combination hv
    refine ⟨teichmuller p β, v, ?_, hxv⟩
    rw [mem_kerThetaFrob]
    intro n
    have h := hx n
    rw [hxv, map_add, map_add, map_mul, map_mul, map_mul, map_mul,
      fontaineTheta_frobenius_pow_mu hε, mul_zero, zero_add, map_natCast, map_natCast,
      mul_eq_zero] at h
    exact h.resolve_right hp0
  exact hJ (mem_kerThetaFrob.2 ha)

/- English proof (translation)
Use `le_antisymm (fun a ha => mem_span_mu_of_forall hε hζ (mem_kerThetaFrob.1 ha)) ?_` and prove the remaining obligations. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_kerThetaFrob]`. Introduce `n`. Simplify using `using fontaineTheta_frobenius_pow_mul_mu (K := K) hε 1 n`.
-/
theorem kerThetaFrob_eq_span_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    kerThetaFrob K p = Ideal.span {mu ε} := by
  refine le_antisymm (fun a ha => mem_span_mu_of_forall hε hζ (mem_kerThetaFrob.1 ha)) ?_
  rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe, mem_kerThetaFrob]
  intro n
  simpa using fontaineTheta_frobenius_pow_mul_mu (K := K) hε 1 n

end AInf

end GroundTheory.PAdicHodge
