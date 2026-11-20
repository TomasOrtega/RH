import Mathlib
import GroundTheory.PAdicHodge.KerFontaineThetaCompFrobeniusEquivSymmPow
set_option maxSynthPendingDepth 1

noncomputable section

open WittVector

namespace GroundTheory.PAdicHodge

section RootsOfUnity

variable {F : Type*} [NormedField F] [IsUltrametricDist F]

omit [IsUltrametricDist F] in

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `one_lt_pow₀ (lt_of_not_ge hlt) hn` as an intermediate fact. Rewrite `this` using `[← norm_pow, h, norm_one]`. Conclude with `lt_irrefl _ this`.
-/
theorem norm_le_one_of_pow_eq_one {ζ : F} {n : ℕ} (hn : n ≠ 0) (h : ζ ^ n = 1) : ‖ζ‖ ≤ 1 := by
  by_contra hlt
  have := one_lt_pow₀ (lt_of_not_ge hlt) hn
  rw [← norm_pow, h, norm_one] at this
  exact lt_irrefl _ this

/- English proof (translation)
Rewrite using `[← mul_neg_geom_sum, norm_mul]`. Establish `: ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ 1` using `IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by`. Rewrite using `[norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) hx`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem norm_one_sub_pow_le {x : F} (hx : ‖x‖ ≤ 1) (m : ℕ) : ‖1 - x ^ m‖ ≤ ‖1 - x‖ := by
  rw [← mul_neg_geom_sum, norm_mul]
  have : ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ 1 :=
    IsUltrametricDist.norm_sum_le_of_forall_le_of_nonneg zero_le_one fun i _ => by
      rw [norm_pow]; exact pow_le_one₀ (norm_nonneg _) hx
  calc ‖1 - x‖ * ‖∑ i ∈ Finset.range m, x ^ i‖ ≤ ‖1 - x‖ * 1 := by gcongr
    _ = ‖1 - x‖ := mul_one _

/- English proof (translation)
Establish `hk : k ≠ 0` using `NeZero.ne k`. Establish `h1 : ‖ζ‖ ≤ 1` using `norm_le_one_of_pow_eq_one hk hζ.pow_eq_one`. Establish `h2 : ‖μ‖ ≤ 1` using `norm_le_one_of_pow_eq_one hk hμ.pow_eq_one`. Take `⟨i, -, hi⟩` from `hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one`. Take `⟨j, -, hj⟩` from `hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one`.

Rewrite using `[norm_sub_rev, norm_sub_rev ζ]`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[← hi]`. Conclude with `norm_one_sub_pow_le h1 i`. Rewrite using `[← hj]`.

Conclude with `norm_one_sub_pow_le h2 j`.
-/
theorem norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist {ζ μ : F} {k : ℕ} [NeZero k]
    (hζ : IsPrimitiveRoot ζ k) (hμ : IsPrimitiveRoot μ k) : ‖μ - 1‖ = ‖ζ - 1‖ := by
  have hk : k ≠ 0 := NeZero.ne k
  have h1 : ‖ζ‖ ≤ 1 := norm_le_one_of_pow_eq_one hk hζ.pow_eq_one
  have h2 : ‖μ‖ ≤ 1 := norm_le_one_of_pow_eq_one hk hμ.pow_eq_one
  obtain ⟨i, -, hi⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
  obtain ⟨j, -, hj⟩ := hμ.eq_pow_of_pow_eq_one hζ.pow_eq_one
  rw [norm_sub_rev, norm_sub_rev ζ]
  refine le_antisymm ?_ ?_
  · rw [← hi]; exact norm_one_sub_pow_le h1 i
  · rw [← hj]; exact norm_one_sub_pow_le h2 j

/- English proof (translation)
Establish `: NeZero (p ^ (k + 1))` using `⟨pow_ne_zero _ hp.out.ne_zero⟩`. Establish `h1` using `Polynomial.eval_one_cyclotomic_prime_pow (R := F) (p := p) k`. Rewrite `h1` using `[Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]`. Simplify using `only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1`. Rewrite using `[← h1, norm_prod, Finset.prod_congr rfl fun μ hμ => (norm_sub_rev 1 μ).trans (norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist hζ ((mem_primitiveRoots (Nat.pos_of_ne_zero (NeZero.ne _))).1 hμ)), Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime_pow hp.out (Nat.s …`.
-/
theorem norm_sub_one_pow_eq_norm_p {p : ℕ} [hp : Fact p.Prime] {ζ : F} {k : ℕ}
    (hζ : IsPrimitiveRoot ζ (p ^ (k + 1))) : ‖ζ - 1‖ ^ (p ^ k * (p - 1)) = ‖(p : F)‖ := by
  have : NeZero (p ^ (k + 1)) := ⟨pow_ne_zero _ hp.out.ne_zero⟩
  have h1 := Polynomial.eval_one_cyclotomic_prime_pow (R := F) (p := p) k
  rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
  simp only [Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C] at h1
  rw [← h1, norm_prod, Finset.prod_congr rfl fun μ hμ => (norm_sub_rev 1 μ).trans
    (norm_sub_one_eq_of_isPrimitiveRoot_of_isUltrametricDist hζ
      ((mem_primitiveRoots (Nat.pos_of_ne_zero (NeZero.ne _))).1 hμ)),
    Finset.prod_const, hζ.card_primitiveRoots, Nat.totient_prime_pow hp.out (Nat.succ_pos k),
    Nat.succ_sub_one]

end RootsOfUnity

namespace AInf

variable {K : Type*} [NontriviallyNormedField K] [IsUltrametricDist K]
variable {p : ℕ} [hp : Fact p.Prime] [IsPerfectoidField K p]

local notation "𝒪" => normInteger K
local notation "𝒪♭" => PreTilt (normInteger K) p
local notation "θ" => fontaineTheta (normInteger K) p
local notation "φ" => WittVector.frobeniusEquiv p (PreTilt (normInteger K) p)

def mu (ε : 𝒪♭) : AInf K p := teichmuller p ε - 1

def xi (ε : 𝒪♭) : AInf K p := ∑ i ∈ Finset.range p, teichmuller p ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ^ i

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one, WittVector.frobeniusEquiv_symm_teichmuller]`.
-/
theorem frobeniusEquiv_symm_mu (ε : 𝒪♭) :
    (φ).symm (mu ε) = teichmuller p ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) - 1 := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_symm_teichmuller]

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one, WittVector.frobeniusEquiv_symm_pow_teichmuller]`.
-/
theorem frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (n : ℕ) :
    ((φ).symm ^ n) (mu ε) = teichmuller p (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) ε) - 1 := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_symm_pow_teichmuller]

/- English proof (translation)
Rewrite using `[frobeniusEquiv_symm_mu, xi, geom_sum_mul, ← map_pow, frobeniusEquiv_symm_pow_p, mu]`.
-/
theorem mu_eq_xi_mul (ε : 𝒪♭) : mu ε = xi ε * (φ).symm (mu ε) := by
  rw [frobeniusEquiv_symm_mu, xi, geom_sum_mul, ← map_pow, frobeniusEquiv_symm_pow_p, mu]

/- English proof (translation)
Rewrite using `[xi, map_sum]`. Simplify using `only [map_pow, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]`.
-/
theorem frobeniusEquiv_xi (ε : 𝒪♭) :
    φ (xi ε) = ∑ i ∈ Finset.range p, teichmuller p ε ^ i := by
  rw [xi, map_sum]
  simp only [map_pow, WittVector.frobeniusEquiv_teichmuller, frobeniusEquiv_symm_pow_p]

/- English proof (translation)
Rewrite using `[frobeniusEquiv_symm_pow_mu, map_sub, map_one, fontaineTheta_teichmuller]`.
-/
theorem fontaineTheta_frobeniusEquiv_symm_pow_mu (ε : 𝒪♭) (n : ℕ) :
    θ (((φ).symm ^ n) (mu ε)) = PreTilt.untilt (((_root_.frobeniusEquiv 𝒪♭ p).symm ^ n) ε) - 1 := by
  rw [frobeniusEquiv_symm_pow_mu, map_sub, map_one, fontaineTheta_teichmuller]

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one, fontaineTheta_teichmuller, hε, sub_self]`.
-/
theorem fontaineTheta_mu {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) : θ (mu ε) = 0 := by
  rw [mu, map_sub, map_one, fontaineTheta_teichmuller, hε, sub_self]

/- English proof (translation)
Rewrite using `[← map_pow, frobeniusEquiv_symm_pow_p, hε]`.
-/
theorem untilt_frobeniusEquiv_symm_pow_p {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ^ p = 1 := by
  rw [← map_pow, frobeniusEquiv_symm_pow_p, hε]

/- English proof (translation)
Rewrite using `[xi, map_sum]`. Simplify using `only [map_pow, fontaineTheta_teichmuller]`. Establish `h` using `mul_geom_sum (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε)) p`. Rewrite `h` using `[untilt_frobeniusEquiv_symm_pow_p hε, sub_self]`. Conclude with `(mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ)`.
-/
theorem fontaineTheta_xi {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : θ (xi ε) = 0 := by
  rw [xi, map_sum]
  simp only [map_pow, fontaineTheta_teichmuller]
  have h := mul_geom_sum (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε)) p
  rw [untilt_frobeniusEquiv_symm_pow_p hε, sub_self] at h
  exact (mul_eq_zero.1 h).resolve_left (sub_ne_zero.2 hζ)

/- English proof (translation)
Introduce `h`. Use `congrArg θ h` as an intermediate fact. Rewrite `this` using `[frobeniusEquiv_symm_mu, map_sub, map_one, fontaineTheta_teichmuller, map_zero, sub_eq_zero]`. Conclude with `hζ this`.
-/
theorem frobeniusEquiv_symm_mu_ne_zero {ε : 𝒪♭} (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    (φ).symm (mu ε) ≠ 0 := by
  intro h
  have := congrArg θ h
  rw [frobeniusEquiv_symm_mu, map_sub, map_one, fontaineTheta_teichmuller, map_zero,
    sub_eq_zero] at this
  exact hζ this

/- English proof (translation)
Introduce `h`. Apply `frobeniusEquiv_symm_mu_ne_zero hζ` to reduce the goal to its premises. Rewrite using `[h, map_zero]`.
-/
theorem mu_ne_zero {ε : 𝒪♭} (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : mu ε ≠ 0 := by
  intro h
  apply frobeniusEquiv_symm_mu_ne_zero hζ
  rw [h, map_zero]

/- English proof (translation)
Use `mul_right_cancel₀ (frobeniusEquiv_symm_mu_ne_zero hζ) (h.trans (mu_eq_xi_mul ε))` as an intermediate fact. Conclude with `this`.
-/
theorem eq_xi_of_mul_eq {ε : 𝒪♭} (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) {x : AInf K p}
    (h : x * (φ).symm (mu ε) = mu ε) : x = xi ε := by
  have := mul_right_cancel₀ (frobeniusEquiv_symm_mu_ne_zero hζ)
    (h.trans (mu_eq_xi_mul ε))
  exact this

/- English proof (translation)
Use `set z : 𝒪 := PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] ε) with hz`. Establish `hz2 : z ^ p ^ (1 + 1) = 1`. Rewrite using `[hz, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, hε]`. Establish `hz1 : ¬ z ^ p ^ 1 = 1`. Introduce `h`.

Apply `hζ` to reduce the goal to its premises. Rewrite using `[← h, hz, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) 1]`. Both sides reduce to the same expression. Establish `hz2K : (z : K) ^ p ^ (1 + 1) = 1`. Rewrite using `[← SubmonoidClass.coe_pow, hz2, OneMemClass.coe_one]`.

Establish `hz1K : ¬ (z : K) ^ p ^ 1 = 1`. Rewrite using `[← SubmonoidClass.coe_pow]`. Conclude with `fun h => hz1 (Subtype.ext (by rw [h, OneMemClass.coe_one]))`. Establish `hprim : IsPrimitiveRoot (z : K) (p ^ (1 + 1))`. Rewrite using `[← orderOf_eq_prime_pow hz1K hz2K]`.

Conclude with `IsPrimitiveRoot.orderOf _`. Establish `hnorm` using `norm_sub_one_pow_eq_norm_p hprim`. Use `set a := ‖(z : K) - 1‖ with ha`. Establish `ha0 : 0 < a` using `norm_pos_iff.2 (sub_ne_zero.2 fun h => hz1K (by rw [h, one_pow]))`. Establish `ha1 : a ≤ 1`.

Use `mem_normInteger.1 (z - 1).2` as an intermediate fact. Rewrite `this` using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one]`. Then use the resulting hypothesis. Establish `hp1 : ‖(p : K)‖ < 1` using `IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)`. Establish `hp2 : 1 < p ^ 1 * (p - 1)`. Use `hp.out.two_le` as an intermediate fact.

Rewrite using `[pow_one]`. Use polynomial arithmetic with `[Nat.sub_add_cancel hp.out.one_le]`. Establish `hpa : ‖(p : K)‖ < a`. Establish `ha1' : a < 1` using `lt_of_le_of_ne ha1 fun h => by`. Rewrite `hnorm` using `[h, one_pow]`.

Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[← hnorm]`. Conclude with `pow_lt_self_of_lt_one₀ ha0 ha1' hp2`. Establish `hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] (ε - 1))) = Ideal.Quotient.mk _ (z - 1)`. Rewrite using `[← coeff_eq_mk_untilt (ε - 1) 2, map_sub, map_one, coeff_eq_mk_untilt ε 2, map_sub, map_one]`.

Establish `hb` using `IsPerfectoidField.norm_eq_of_mk_eq p hmk (by`. Rewrite using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one]`. Conclude with `hpa)`. Rewrite `hb` using `[AddSubgroupClass.coe_sub, OneMemClass.coe_one]`. Establish `hε1 : ‖ε - 1‖ = a ^ p ^ 2`.

Rewrite using `[preTilt_norm_def, ← norm_untilt_iterate_pow (ε - 1) 2, hb]`. Rewrite using `[hε1, ← pow_mul, ← hnorm, ← pow_mul]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sub_one_pow {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ‖ε - 1‖ ^ (p - 1) = ‖(p : K)‖ ^ p := by
  set z : 𝒪 := PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] ε) with hz
  have hz2 : z ^ p ^ (1 + 1) = 1 := by
    rw [hz, PreTilt.untilt_iterate_frobeniusEquiv_symm_pow, hε]
  have hz1 : ¬ z ^ p ^ 1 = 1 := by
    intro h
    apply hζ
    rw [← h, hz, ← PreTilt.untilt_iterate_frobeniusEquiv_symm_pow
      ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) 1]
    rfl
  have hz2K : (z : K) ^ p ^ (1 + 1) = 1 := by
    rw [← SubmonoidClass.coe_pow, hz2, OneMemClass.coe_one]
  have hz1K : ¬ (z : K) ^ p ^ 1 = 1 := by
    rw [← SubmonoidClass.coe_pow]
    exact fun h => hz1 (Subtype.ext (by rw [h, OneMemClass.coe_one]))
  have hprim : IsPrimitiveRoot (z : K) (p ^ (1 + 1)) := by
    rw [← orderOf_eq_prime_pow hz1K hz2K]
    exact IsPrimitiveRoot.orderOf _
  have hnorm := norm_sub_one_pow_eq_norm_p hprim
  set a := ‖(z : K) - 1‖ with ha
  have ha0 : 0 < a := norm_pos_iff.2 (sub_ne_zero.2 fun h => hz1K (by rw [h, one_pow]))
  have ha1 : a ≤ 1 := by
    have := mem_normInteger.1 (z - 1).2
    rwa [AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this
  have hp1 : ‖(p : K)‖ < 1 := IsPerfectoidField.norm_natCast_lt_one (K := K) (p := p)
  have hp2 : 1 < p ^ 1 * (p - 1) := by
    have := hp.out.two_le
    rw [pow_one]
    nlinarith [Nat.sub_add_cancel hp.out.one_le]
  have hpa : ‖(p : K)‖ < a := by
    have ha1' : a < 1 := lt_of_le_of_ne ha1 fun h => by
      rw [h, one_pow] at hnorm; linarith
    rw [← hnorm]
    exact pow_lt_self_of_lt_one₀ ha0 ha1' hp2
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)})
      (PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm^[2] (ε - 1))) =
        Ideal.Quotient.mk _ (z - 1) := by
    rw [← coeff_eq_mk_untilt (ε - 1) 2, map_sub, map_one, coeff_eq_mk_untilt ε 2, map_sub, map_one]
  have hb := IsPerfectoidField.norm_eq_of_mk_eq p hmk (by
    rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one]; exact hpa)
  rw [AddSubgroupClass.coe_sub, OneMemClass.coe_one] at hb
  have hε1 : ‖ε - 1‖ = a ^ p ^ 2 := by
    rw [preTilt_norm_def, ← norm_untilt_iterate_pow (ε - 1) 2, hb]
  rw [hε1, ← pow_mul, ← hnorm, ← pow_mul]
  congr 1
  ring

/- English proof (translation)
Introduce and unpack `rfl`. Apply `hζ` to reduce the goal to its premises. Rewrite using `[map_one, map_one]`.
-/
theorem ne_one_of_untilt_ne_one {ε : 𝒪♭}
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : ε ≠ 1 := by
  rintro rfl
  apply hζ
  rw [map_one, map_one]

/- English proof (translation)
Introduce `h`. Use `norm_sub_one_pow hε hζ` as an intermediate fact. Rewrite `this` using `[h, zero_pow hp.out.ne_zero, pow_eq_zero_iff (Nat.sub_ne_zero_of_lt hp.out.one_lt), norm_eq_zero, sub_eq_zero]`. Conclude with `ne_one_of_untilt_ne_one hζ this`.
-/
theorem norm_natCast_ne_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) : ‖(p : K)‖ ≠ 0 := by
  intro h
  have := norm_sub_one_pow hε hζ
  rw [h, zero_pow hp.out.ne_zero, pow_eq_zero_iff (Nat.sub_ne_zero_of_lt hp.out.one_lt),
    norm_eq_zero, sub_eq_zero] at this
  exact ne_one_of_untilt_ne_one hζ this

/- English proof (translation)
Express the relevant statement in the definitionally equal form `WittVector.constantCoeff (xi ε) = _`. Rewrite using `[xi, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[map_pow]`. Conclude with `congrArg (· ^ i) (teichmuller_coeff_zero p _)`.
-/
theorem xi_coeff_zero (ε : 𝒪♭) :
    (xi ε).coeff 0 = ∑ i ∈ Finset.range p, (_root_.frobeniusEquiv 𝒪♭ p).symm ε ^ i := by
  change WittVector.constantCoeff (xi ε) = _
  rw [xi, map_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_pow]
  exact congrArg (· ^ i) (teichmuller_coeff_zero p _)

/- English proof (translation)
Use `set e := (_root_.frobeniusEquiv 𝒪♭ p).symm ε`. Establish `hgeom : (xi ε).coeff 0 * (e - 1) = ε - 1`. Rewrite using `[xi_coeff_zero, geom_sum_mul, frobeniusEquiv_symm_pow_p]`. Establish `hfrob : ‖e - 1‖ ^ p = ‖ε - 1‖`. Rewrite using `[← norm_pow, sub_pow_char, one_pow, frobeniusEquiv_symm_pow_p]`.

Establish `hne : ‖ε - 1‖ ≠ 0`. Rewrite using `[norm_ne_zero_iff, sub_ne_zero]`. Conclude with `ne_one_of_untilt_ne_one hζ`. Establish `h1 : ‖(xi ε).coeff 0‖ ^ p * ‖ε - 1‖ = ‖(p : K)‖ ^ p * ‖ε - 1‖`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `(pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hp.out.ne_zero).1 (mul_right_cancel₀ hne h1)`.
-/
theorem norm_xi_coeff_zero {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    ‖(xi ε).coeff 0‖ = ‖(p : K)‖ := by
  set e := (_root_.frobeniusEquiv 𝒪♭ p).symm ε
  have hgeom : (xi ε).coeff 0 * (e - 1) = ε - 1 := by
    rw [xi_coeff_zero, geom_sum_mul, frobeniusEquiv_symm_pow_p]
  have hfrob : ‖e - 1‖ ^ p = ‖ε - 1‖ := by
    rw [← norm_pow, sub_pow_char, one_pow, frobeniusEquiv_symm_pow_p]
  have hne : ‖ε - 1‖ ≠ 0 := by
    rw [norm_ne_zero_iff, sub_ne_zero]
    exact ne_one_of_untilt_ne_one hζ
  have h1 : ‖(xi ε).coeff 0‖ ^ p * ‖ε - 1‖ = ‖(p : K)‖ ^ p * ‖ε - 1‖ :=
    calc ‖(xi ε).coeff 0‖ ^ p * ‖ε - 1‖ = ‖(xi ε).coeff 0‖ ^ p * ‖e - 1‖ ^ p := by rw [hfrob]
      _ = ‖(xi ε).coeff 0 * (e - 1)‖ ^ p := by rw [norm_mul, mul_pow]
      _ = ‖ε - 1‖ ^ p := by rw [hgeom]
      _ = ‖ε - 1‖ ^ (p - 1) * ‖ε - 1‖ := by rw [← pow_succ, Nat.sub_add_cancel hp.out.one_le]
      _ = ‖(p : K)‖ ^ p * ‖ε - 1‖ := by rw [norm_sub_one_pow hε hζ]
  exact (pow_left_inj₀ (norm_nonneg _) (norm_nonneg _) hp.out.ne_zero).1
    (mul_right_cancel₀ hne h1)

/- English proof (translation)
Take `⟨v, hv⟩` from `exists_eq_teichmuller_add_mul_p (xi ε)`. Establish `hker : xi ε ∈ RingHom.ker θ` using `fontaineTheta_xi hε hζ`. Establish `h1` using `IsPerfectoidField.norm_untilt_coeff_zero hker hv`. Rewrite `h1` using `[← preTilt_norm_def, norm_xi_coeff_zero hε hζ]`. Establish `hθv : ‖((θ v : 𝒪) : K)‖ = 1` using `(mul_eq_right₀ (norm_natCast_ne_zero hε hζ)).1 h1.symm`.

Establish `hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt (v.coeff 0)) = Ideal.Quotient.mk _ (θ v)`. Rewrite using `[IsPerfectoidField.mk_untilt, WittVector.mk_fontaineTheta]`. Establish `hu` using `IsPerfectoidField.norm_eq_one_of_mk_eq p hmk hθv`. Rewrite using `[hv, coeff_one_teichmuller_add_mul_p]`. Conclude with `((IsPerfectoidField.isUnit_iff_norm_untilt p).2 hu).pow p`.
-/
theorem isUnit_xi_coeff_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    IsUnit ((xi ε).coeff 1) := by
  obtain ⟨v, hv⟩ := exists_eq_teichmuller_add_mul_p (xi ε)
  have hker : xi ε ∈ RingHom.ker θ := fontaineTheta_xi hε hζ
  have h1 := IsPerfectoidField.norm_untilt_coeff_zero hker hv
  rw [← preTilt_norm_def, norm_xi_coeff_zero hε hζ] at h1
  have hθv : ‖((θ v : 𝒪) : K)‖ = 1 :=
    (mul_eq_right₀ (norm_natCast_ne_zero hε hζ)).1 h1.symm
  have hmk : Ideal.Quotient.mk (Ideal.span {(p : 𝒪)}) (PreTilt.untilt (v.coeff 0)) =
      Ideal.Quotient.mk _ (θ v) := by
    rw [IsPerfectoidField.mk_untilt, WittVector.mk_fontaineTheta]
  have hu := IsPerfectoidField.norm_eq_one_of_mk_eq p hmk hθv
  rw [hv, coeff_one_teichmuller_add_mul_p]
  exact ((IsPerfectoidField.isUnit_iff_norm_untilt p).2 hu).pow p

/- English proof (translation)
The claim follows from `IsPerfectoidField.ker_fontaineTheta_eq_span (fontaineTheta_xi hε hζ) (isUnit_xi_coeff_one hε hζ)`.
-/
theorem ker_fontaineTheta_eq_span_xi {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    RingHom.ker θ = Ideal.span {xi ε} :=
  IsPerfectoidField.ker_fontaineTheta_eq_span (fontaineTheta_xi hε hζ) (isUnit_xi_coeff_one hε hζ)

/- English proof (translation)
Use `ker_fontaineTheta_comp_frobeniusEquiv_symm_pow (ker_fontaineTheta_eq_span_xi hε hζ) 1` as an intermediate fact. Rewrite `this` using `[pow_one, pow_one, frobeniusEquiv_xi]`. Then use the resulting hypothesis.
-/
theorem ker_fontaineTheta_comp_frobeniusEquiv_symm_eq_span {ε : 𝒪♭}
    (hε : PreTilt.untilt ε = 1)
    (hζ : PreTilt.untilt ((_root_.frobeniusEquiv 𝒪♭ p).symm ε) ≠ 1) :
    RingHom.ker ((fontaineTheta (normInteger K) p).comp ((φ).symm : AInf K p ≃+* AInf K p).toRingHom) =
      Ideal.span {∑ i ∈ Finset.range p, teichmuller p ε ^ i} := by
  have := ker_fontaineTheta_comp_frobeniusEquiv_symm_pow (ker_fontaineTheta_eq_span_xi hε hζ) 1
  rwa [pow_one, pow_one, frobeniusEquiv_xi] at this

/- English proof (translation)
Rewrite using `[mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, mul_comm, geom_sum_mul]`.
-/
theorem frobeniusEquiv_mu (ε : 𝒪♭) :
    φ (mu ε) = mu ε * ∑ i ∈ Finset.range p, teichmuller p ε ^ i := by
  rw [mu, map_sub, map_one, WittVector.frobeniusEquiv_teichmuller, map_pow, mul_comm,
    geom_sum_mul]

/- English proof (translation)
The claim follows from `IsPerfectoidField.preTilt_ext p fun n => by rw [PreTilt.coeff_frobeniusEquiv_symm, IsPerfectoidField.coeff_ofCompatible, IsPerfectoidField.coeff_ofCompatible]`.
-/
theorem frobeniusEquiv_symm_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n) :
    (_root_.frobeniusEquiv 𝒪♭ p).symm (IsPerfectoidField.ofCompatible p y hy) =
      IsPerfectoidField.ofCompatible p (fun n => y (n + 1)) (fun n => hy (n + 1)) :=
  IsPerfectoidField.preTilt_ext p fun n => by
    rw [PreTilt.coeff_frobeniusEquiv_symm, IsPerfectoidField.coeff_ofCompatible,
      IsPerfectoidField.coeff_ofCompatible]

/- English proof (translation)
Use `ker_fontaineTheta_eq_span_xi ?_ ?_` and prove the remaining obligations. Rewrite using `[IsPerfectoidField.untilt_ofCompatible, h0]`. Rewrite using `[frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]`. Conclude with `h1`.
-/
theorem ker_fontaineTheta_eq_span_xi_ofCompatible (y : ℕ → 𝒪) (hy : ∀ n, y (n + 1) ^ p = y n)
    (h0 : y 0 = 1) (h1 : y 1 ≠ 1) :
    RingHom.ker θ = Ideal.span {xi (IsPerfectoidField.ofCompatible p y hy)} := by
  refine ker_fontaineTheta_eq_span_xi ?_ ?_
  · rw [IsPerfectoidField.untilt_ofCompatible, h0]
  · rw [frobeniusEquiv_symm_ofCompatible, IsPerfectoidField.untilt_ofCompatible]
    exact h1

/- English proof (translation)
Use `IsUnit.map (teichmuller p) ((IsPerfectoidField.isUnit_iff_norm_untilt p).2 ?_)` and prove the remaining obligations. Rewrite using `[hε, OneMemClass.coe_one, norm_one]`.
-/
theorem isUnit_teichmuller_of_untilt_eq_one {ε : 𝒪♭} (hε : PreTilt.untilt ε = 1) :
    IsUnit (teichmuller p ε : AInf K p) := by
  refine IsUnit.map (teichmuller p) ((IsPerfectoidField.isUnit_iff_norm_untilt p).2 ?_)
  rw [hε, OneMemClass.coe_one, norm_one]

end AInf

end GroundTheory.PAdicHodge
