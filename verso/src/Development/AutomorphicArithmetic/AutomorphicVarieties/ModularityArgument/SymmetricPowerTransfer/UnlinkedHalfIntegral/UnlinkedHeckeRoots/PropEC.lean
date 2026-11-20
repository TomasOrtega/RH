import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.IdeleGenerators.HolomorphicIrreducibility.SumDivHecke
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.UnitFormC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.EigLiftC
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.ConstCj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.UnlinkedHalfIntegral.UnlinkedHeckeRoots.PrimCj

open Formalism.ConjugateSelfDual CongruenceSubgroup UpperHalfPlane UpperTheory.V.Af UpperTheory.V.Sd
open scoped MatrixGroups ModularForm

namespace UpperTheory.V.Z.Sym.Unl

/- English proof (translation)
Establish `hp0 : 0 < p` using `hp.pos`. Establish `hset : (p * n).divisors.filter (fun j => p ∣ j) = n.divisors.image (fun d => p * d)`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hj, _⟩, ⟨d, rfl⟩⟩`. Conclude with `⟨d, ⟨(Nat.mul_dvd_mul_iff_left hp0).mp hj, by omega⟩, rfl⟩`. Introduce and unpack `⟨d, ⟨hd, _⟩, rfl⟩`. Conclude with `⟨⟨Nat.mul_dvd_mul_left p hd, mul_ne_zero hp.ne_zero (by omega)⟩, dvd_mul_right p d⟩`. Rewrite using `[hset, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h), Finset.mul_sum]`.

Simplify using `only [hg]`.
-/
private theorem sum_div_split (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors with p ∣ j, g j = g p * ∑ j ∈ n.divisors, g j := by
  have hp0 : 0 < p := hp.pos
  have hset : (p * n).divisors.filter (fun j => p ∣ j) = n.divisors.image (fun d => p * d) := by
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors, Finset.mem_image]
    constructor
    · rintro ⟨⟨hj, _⟩, ⟨d, rfl⟩⟩
      exact ⟨d, ⟨(Nat.mul_dvd_mul_iff_left hp0).mp hj, by omega⟩, rfl⟩
    · rintro ⟨d, ⟨hd, _⟩, rfl⟩
      exact ⟨⟨Nat.mul_dvd_mul_left p hd, mul_ne_zero hp.ne_zero (by omega)⟩, dvd_mul_right p d⟩
  rw [hset, Finset.sum_image (fun a _ b _ h => Nat.eq_of_mul_eq_mul_left hp0 h), Finset.mul_sum]
  simp only [hg]

/- English proof (translation)
Rewrite using `[← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun j => p ∣ j) g, sum_div_split g hg hp n hn]`. Establish `hnd : (p * n).divisors.filter (fun j => ¬ p ∣ j) = n.divisors.filter (fun j => ¬ p ∣ j)`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨hj, _⟩, hpj⟩`. Establish `hc : Nat.Coprime j p` using `Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj)`. Conclude with `⟨⟨hc.dvd_of_dvd_mul_left hj, by omega⟩, hpj⟩`. Introduce and unpack `⟨⟨hj, _⟩, hpj⟩`. Conclude with `⟨⟨dvd_mul_of_dvd_right hj p, mul_ne_zero hp.ne_zero (by omega)⟩, hpj⟩`.

Establish `hsplit` using `Finset.sum_filter_add_sum_filter_not n.divisors (fun j => p ∣ j) g`. Establish `hdiv : (∑ j ∈ n.divisors with p ∣ j, g j) = g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0)` using `by split_ifs with hpn`. Take `⟨m, rfl⟩` from `hpn`. Establish `hm : 1 ≤ m`. Break down `Nat.eq_zero_or_pos m with h0 | h0` into its components or cases.

Substitute `h0` using the available equality. Simplify using `at hn`. Conclude with `h0`. Rewrite using `[Nat.mul_div_cancel_left m hp.pos]`. Conclude with `sum_div_split g hg hp m hm`.

Rewrite using `[mul_zero]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Nat.mem_divisors] at hj`. Conclude with `absurd (hj.2.trans hj.1.1) hpn`.

Rewrite using `[hnd, ← hdiv, ← hsplit]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem sum_div_hecke (g : ℕ → ℂ) (hg : ∀ a b, g (a * b) = g a * g b) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    ∑ j ∈ (p * n).divisors, g j + g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) =
      (1 + g p) * ∑ j ∈ n.divisors, g j := by
  rw [← Finset.sum_filter_add_sum_filter_not (p * n).divisors (fun j => p ∣ j) g,
    sum_div_split g hg hp n hn]
  have hnd : (p * n).divisors.filter (fun j => ¬ p ∣ j) = n.divisors.filter (fun j => ¬ p ∣ j) := by
    ext j
    simp only [Finset.mem_filter, Nat.mem_divisors]
    constructor
    · rintro ⟨⟨hj, _⟩, hpj⟩
      have hc : Nat.Coprime j p := Nat.coprime_comm.mp ((Nat.Prime.coprime_iff_not_dvd hp).mpr hpj)
      exact ⟨⟨hc.dvd_of_dvd_mul_left hj, by omega⟩, hpj⟩
    · rintro ⟨⟨hj, _⟩, hpj⟩
      exact ⟨⟨dvd_mul_of_dvd_right hj p, mul_ne_zero hp.ne_zero (by omega)⟩, hpj⟩
  have hsplit := Finset.sum_filter_add_sum_filter_not n.divisors (fun j => p ∣ j) g
  have hdiv : (∑ j ∈ n.divisors with p ∣ j, g j) =
      g p * (if p ∣ n then ∑ j ∈ (n / p).divisors, g j else 0) := by
    split_ifs with hpn
    · obtain ⟨m, rfl⟩ := hpn
      have hm : 1 ≤ m := by
        rcases Nat.eq_zero_or_pos m with h0 | h0
        · subst h0
          simp at hn
        · exact h0
      rw [Nat.mul_div_cancel_left m hp.pos]
      exact sum_div_split g hg hp m hm
    · rw [mul_zero]
      apply Finset.sum_eq_zero
      intro j hj
      simp only [Finset.mem_filter, Nat.mem_divisors] at hj
      exact absurd (hj.2.trans hj.1.1) hpn
  rw [hnd, ← hdiv, ← hsplit]
  ring

/- English proof (translation)
Establish `hg : ∀ a b : ℕ, (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) (a * b) = (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) a * (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) b`. Introduce `a b`. Simplify using `only [Nat.cast_mul, map_mul, mul_pow]`. Expand and normalize the polynomial expressions, which then agree. Establish `h` using `sum_div_hecke (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) hg hp n hn`.

Use `beta_reduce at h`. Simplify using `only [sigChi]`. Conclude with `h`.
-/
private theorem sig_hecke (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) {p : ℕ} (hp : p.Prime) (n : ℕ) (hn : 1 ≤ n) :
    sigChi k χ (p * n) + χ (p : ZMod N) * (p : ℂ) ^ (k - 1) * (if p ∣ n then sigChi k χ (n / p) else 0) =
      (1 + χ (p : ZMod N) * (p : ℂ) ^ (k - 1)) * sigChi k χ n := by
  have hg : ∀ a b : ℕ, (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) (a * b) =
      (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) a *
        (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) b := by
    intro a b
    simp only [Nat.cast_mul, map_mul, mul_pow]
    ring
  have h := sum_div_hecke (fun j : ℕ => χ (j : ZMod N) * (j : ℂ) ^ (k - 1)) hg hp n hn
  beta_reduce at h
  simp only [sigChi]
  exact h

section Int

variable {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ)

/- English proof (translation)
Rewrite using `[map_add]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)`.
-/
private theorem int_add {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x + y)‖ ≤ 1 := by
  rw [map_add]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx hy)

/- English proof (translation)
Rewrite using `[map_sub, sub_eq_add_neg]`. Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rwa [norm_neg]))`.
-/
private theorem int_sub {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x - y)‖ ≤ 1 := by
  rw [map_sub, sub_eq_add_neg]
  exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le hx (by rwa [norm_neg]))

/- English proof (translation)
Rewrite using `[map_mul, norm_mul]`. Conclude with `mul_le_one₀ hx (norm_nonneg _) hy`.
-/
private theorem int_mul {x y : ℂ} (hx : ‖ι.symm x‖ ≤ 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ ≤ 1 := by
  rw [map_mul, norm_mul]
  exact mul_le_one₀ hx (norm_nonneg _) hy

/- English proof (translation)
Rewrite using `[map_mul, norm_mul]`. Conclude with `lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hy) hx`.
-/
private theorem small_mul {x y : ℂ} (hx : ‖ι.symm x‖ < 1) (hy : ‖ι.symm y‖ ≤ 1) : ‖ι.symm (x * y)‖ < 1 := by
  rw [map_mul, norm_mul]
  exact lt_of_le_of_lt (mul_le_of_le_one_right (norm_nonneg _) hy) hx

/- English proof (translation)
Distinguish the cases in `ha : IsUnit a`. Take `⟨u, rfl⟩` from `ha`. Establish `hfin : 0 < orderOf u` using `orderOf_pos u`. Establish `h1 : (ι.symm (χ u)) ^ orderOf u = 1`. Rewrite using `[← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one, map_one, map_one]`.

Establish `h2 : ‖ι.symm (χ u)‖ ^ orderOf u = 1`. Rewrite using `[← norm_pow, h1, norm_one]`. Conclude with `le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hfin.ne').mp h2)`. Rewrite using `[MulChar.map_nonunit χ ha, map_zero, norm_zero]`. Conclude with `zero_le_one`.
-/
private theorem int_chi {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (a : ZMod N) : ‖ι.symm (χ a)‖ ≤ 1 := by
  by_cases ha : IsUnit a
  · obtain ⟨u, rfl⟩ := ha
    have hfin : 0 < orderOf u := orderOf_pos u
    have h1 : (ι.symm (χ u)) ^ orderOf u = 1 := by
      rw [← map_pow, ← map_pow, ← Units.val_pow_eq_pow_val, pow_orderOf_eq_one, Units.val_one,
        map_one, map_one]
    have h2 : ‖ι.symm (χ u)‖ ^ orderOf u = 1 := by
      rw [← norm_pow, h1, norm_one]
    exact le_of_eq ((pow_eq_one_iff_of_nonneg (norm_nonneg _) hfin.ne').mp h2)
  · rw [MulChar.map_nonunit χ ha, map_zero, norm_zero]
    exact zero_le_one

/- English proof (translation)
Use `int_mul ι (int_chi ι χ _) ?_` and prove the remaining obligations. Rewrite using `[map_pow, map_natCast, norm_pow]`. Conclude with `pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ j)`.
-/
private theorem int_term (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (j : ℕ) :
    ‖ι.symm (χ (j : ZMod N) * (j : ℂ) ^ (k - 1))‖ ≤ 1 := by
  refine int_mul ι (int_chi ι χ _) ?_
  rw [map_pow, map_natCast, norm_pow]
  exact pow_le_one₀ (norm_nonneg _) (IsUltrametricDist.norm_natCast_le_one _ j)

/- English proof (translation)
Unfold `sigChi`. Generalize the expression as in `n.divisors = s`. Use `Finset.induction_on s ?_ ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Introduce `a s ha ih`.

Rewrite using `[Finset.sum_insert ha]`. Conclude with `int_add ι (int_term ι k χ a) ih`.
-/
private theorem int_sig (k : ℕ) {N : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (n : ℕ) :
    ‖ι.symm (sigChi k χ n)‖ ≤ 1 := by
  unfold sigChi
  generalize n.divisors = s
  refine Finset.induction_on s ?_ ?_
  · simp
  · intro a s ha ih
    rw [Finset.sum_insert ha]
    exact int_add ι (int_term ι k χ a) ih

end Int

/- English proof (translation)
Establish `hM` using `h.one_lt`. Establish `hw` using `h.prime`. Establish `hN : 1 ≤ M * w` using `Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hw.ne_zero)`. Establish `hcast : ((M * w - 1 : ℕ) : ZMod (M * w)) = -1`. Rewrite using `[Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one, zero_sub]`.

Establish `hM' : ((M * w - 1 : ℕ) : ZMod M) = -1`. Rewrite using `[Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_sub]`. Establish `hw' : ((M * w - 1 : ℕ) : ZMod w) = -1`. Rewrite using `[Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, mul_zero, Nat.cast_one, zero_sub]`. Establish `hmul` using `h.mul (M * w - 1)`.

Rewrite `hmul` using `[hcast, hM', hw']`. Rewrite using `[hmul]`. Establish `hl0 : l ≠ 0` using `hl.ne_zero`. Establish `h2 : θ (-1) ^ l = 1`. Rewrite using `[← MulChar.pow_apply' θ hl0, h.θpow, MulChar.one_apply isUnit_one.neg]`.

Establish `hodd : Odd l` using `(hl.eq_two_or_odd').resolve_left h.odd`. Establish `h1 : θ (-1) * θ (-1) = 1`. Rewrite using `[← map_mul, neg_one_mul, neg_neg, map_one]`. Break down `mul_self_eq_one_iff.mp h1 with h3 | h3` into its components or cases. Rewrite using `[h3, mul_one]`.

It suffices to derive a contradiction. Rewrite `h2` using `[h3, hodd.neg_one_pow]`. Evaluate the numerical expressions using `at h2`.
-/
private theorem chi_neg_one {l M w : ℕ} (hl : l.Prime) {φ θ χ} (h : EDat l M w φ θ χ) : χ (-1) = φ (-1) := by
  have hM := h.one_lt
  have hw := h.prime
  have hN : 1 ≤ M * w := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero (by omega) hw.ne_zero)
  have hcast : ((M * w - 1 : ℕ) : ZMod (M * w)) = -1 := by
    rw [Nat.cast_sub hN, ZMod.natCast_self, Nat.cast_one, zero_sub]
  have hM' : ((M * w - 1 : ℕ) : ZMod M) = -1 := by
    rw [Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, zero_mul, Nat.cast_one, zero_sub]
  have hw' : ((M * w - 1 : ℕ) : ZMod w) = -1 := by
    rw [Nat.cast_sub hN, Nat.cast_mul, ZMod.natCast_self, mul_zero, Nat.cast_one, zero_sub]
  have hmul := h.mul (M * w - 1)
  rw [hcast, hM', hw'] at hmul
  rw [hmul]
  have hl0 : l ≠ 0 := hl.ne_zero
  have h2 : θ (-1) ^ l = 1 := by
    rw [← MulChar.pow_apply' θ hl0, h.θpow, MulChar.one_apply isUnit_one.neg]
  have hodd : Odd l := (hl.eq_two_or_odd').resolve_left h.odd
  have h1 : θ (-1) * θ (-1) = 1 := by
    rw [← map_mul, neg_one_mul, neg_neg, map_one]
  rcases mul_self_eq_one_iff.mp h1 with h3 | h3
  · rw [h3, mul_one]
  · exfalso
    rw [h3, hodd.neg_one_pow] at h2
    norm_num at h2

/- English proof (translation)
Establish `h1 : (1 : ℝ) ∈ ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods` using `by simp`. Unfold `coef`. Rewrite using `[ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 E (c • G), ModularForm.coe_smul, ModularForm.qExpansion_smul one_pos h1 c G]`. Simplify using the standard rewrite rules.
-/
private theorem coef_comb {N k : ℕ} [NeZero N] (E G : ModularForm (Gamma1 N) (k : ℤ)) (c : ℂ) (n : ℕ) :
    coef (E - c • G : ModularForm (Gamma1 N) (k : ℤ)) n = coef E n - c * coef G n := by
  have h1 : (1 : ℝ) ∈ ((Gamma1 N : Subgroup (GL (Fin 2) ℝ))).strictPeriods := by simp
  unfold coef
  rw [ModularForm.coe_sub, ModularForm.qExpansion_sub one_pos h1 E (c • G), ModularForm.coe_smul,
    ModularForm.qExpansion_smul one_pos h1 c G]
  simp

/- English proof (translation)
Rewrite using `[sub_eq_add_neg, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash, ModularForm.SL_smul_slash]`.
-/
private theorem slash_comb (k : ℕ) (E G : ℍ → ℂ) (c : ℂ) (γ : SL(2, ℤ)) :
    (E - c • G) ∣[(k : ℤ)] γ = E ∣[(k : ℤ)] γ - c • G ∣[(k : ℤ)] γ := by
  rw [sub_eq_add_neg, sub_eq_add_neg, SlashAction.add_slash, SlashAction.neg_slash,
    ModularForm.SL_smul_slash]

/- English proof (translation)
Simplify using `[sigChi, cj, MulChar.ringHomComp_apply, map_sum]`.
-/
private theorem sig_cj (k : ℕ) {N : ℕ} (χ : DirichletCharacter ℂ N) (σ : ℂ ≃+* ℂ) (n : ℕ) :
    σ (sigChi k χ n) = sigChi k (cj σ χ) n := by
  simp [sigChi, cj, MulChar.ringHomComp_apply, map_sum]

/- English proof (translation)
Establish `hFc : HasChar k χ ⇑(E - coef E 0 • G)`. Introduce `γ hγ`. Rewrite using `[ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, hEc γ hγ, hGc γ hγ, smul_sub, smul_comm (χ _) (coef E 0)]`. Establish `hFv : VanOff N k ⇑(E - coef E 0 • G)`. Introduce `γ hγ`.

Rewrite using `[ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, sub_eq_add_neg]`. Conclude with `Filter.ZeroAtFilter.add (hEv γ hγ) (Filter.ZeroAtFilter.neg (Filter.ZeroAtFilter.smul (coef E 0) (hGv γ hγ)))`. Establish `hF0 : coef ⇑(E - coef E 0 • G) 0 = 0`. Rewrite using `[coef_comb, hG0, mul_one, sub_self]`. Take `⟨g, hg⟩` from `cuspOf N k χ (E - coef E 0 • G) hFc hFv hF0`.

Use `⟨g, ?_, fun n => ?_⟩` and prove the remaining obligations. Rewrite using `[hg]`. Conclude with `hFc`. Rewrite using `[hg]`. Conclude with `coef_comb E G (coef E 0) n`.
-/
private theorem cusp_comb {N k : ℕ} [NeZero N] (χ : DirichletCharacter ℂ N) (E G : ModularForm (Gamma1 N) (k : ℤ))
    (hEc : HasChar k χ E) (hGc : HasChar k χ G) (hEv : VanOff N k E) (hGv : VanOff N k G) (hG0 : coef G 0 = 1) :
    ∃ f : CuspForm (Gamma1 N) (k : ℤ), HasChar k χ f ∧ ∀ n, coef f n = coef E n - coef E 0 * coef G n := by
  have hFc : HasChar k χ ⇑(E - coef E 0 • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, hEc γ hγ, hGc γ hγ, smul_sub,
      smul_comm (χ _) (coef E 0)]
  have hFv : VanOff N k ⇑(E - coef E 0 • G) := by
    intro γ hγ
    rw [ModularForm.coe_sub, ModularForm.coe_smul, slash_comb, sub_eq_add_neg]
    exact Filter.ZeroAtFilter.add (hEv γ hγ)
      (Filter.ZeroAtFilter.neg (Filter.ZeroAtFilter.smul (coef E 0) (hGv γ hγ)))
  have hF0 : coef ⇑(E - coef E 0 • G) 0 = 0 := by
    rw [coef_comb, hG0, mul_one, sub_self]
  obtain ⟨g, hg⟩ := cuspOf N k χ (E - coef E 0 • G) hFc hFv hF0
  refine ⟨g, ?_, fun n => ?_⟩
  · rw [hg]
    exact hFc
  · rw [hg]
    exact coef_comb E G (coef E 0) n

end UpperTheory.V.Z.Sym.Unl

/- English proof (translation)
Unfold `UpperTheory.V.Z.Sym.Unl.PropEC`. Introduce `l _ ι M w φ θ χ h`. Establish `hM` using `h.one_lt`. Establish `hw` using `h.prime`. Establish `hl : l.Prime` using `Fact.out`.

Use `haveI : NeZero (M * w) := ⟨mul_ne_zero (by omega) hw.ne_zero⟩`. Establish `hN3 : 3 ≤ M * w`. Use `hw.two_le` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities. Establish `hlN : ¬ l ∣ M * w`.

Introduce `hd`. Break down `(Nat.Prime.dvd_mul hl).mp hd with h1 | h1` into its components or cases. Conclude with `h.cop h1`. Establish `h2` using `h.dvd`. Establish `h3 : l ∣ 1` using `(Nat.dvd_add_right h2).mp (by rwa [Nat.sub_add_cancel hw.one_le])`.

Conclude with `hl.one_lt.ne' (Nat.dvd_one.mp h3)`. Take `⟨k₀, hk₀⟩` from `unitFormC l h.odd ι (M * w) hN3 hlN`. Use `⟨max k₀ 3, fun k hk hφk => ?_⟩` and prove the remaining obligations. Establish `hk1 : k₀ ≤ k` using `le_trans (le_max_left _ _) hk`. Establish `hk3 : 3 ≤ k` using `le_trans (le_max_right _ _) hk`.

Establish `hχk : χ (-1) = (-1) ^ k`. Rewrite using `[chi_neg_one hl h, hφk]`. Establish `hprim : χ.IsPrimitive` using `ePrim l M w φ θ χ h`. Establish `h1N : 1 < M * w` using `by omega`. Take `⟨E, hEc, hEv, hEn, hE0⟩` from `eisChi (M * w) k h1N hk3 χ hprim hχk`.

Take `⟨G, hGc, hGi, hGv, hG0, hGσ⟩` from `hk₀ k hk1 χ hχk`. Take `⟨f, hfc, hfn⟩` from `cusp_comb χ E G hEc hGc hEv hGv hG0`. Establish `hc : ‖ι.symm (coef E 0)‖ < 1` using `constSmall l ι M w φ θ χ h k (by omega) (coef E 0) hE0`. Establish `hGint : ∀ n, ‖ι.symm (coef G n)‖ ≤ 1` using `hGi`. Establish `hfcoef : ∀ n, 1 ≤ n → coef f n = sigChi k χ n - coef E 0 * coef G n`.

Introduce `n hn`. Rewrite using `[hfn, hEn n hn]`. Establish `hfint : UpperTheory.V.Sd.IntQ ι f`. Introduce `n`. Break down `Nat.eq_zero_or_pos n with rfl | hn` into its components or cases.

Rewrite using `[hfn, hG0, mul_one, sub_self, map_zero, norm_zero]`. Conclude with `zero_le_one`. Rewrite using `[hfcoef n hn]`. Conclude with `int_sub ι (int_sig ι k χ n) (int_mul ι hc.le (hGint n))`. Establish `hf1 : ‖ι.symm (coef f 1)‖ = 1`.

Establish `hs1 : sigChi k χ 1 = 1` using `by simp [sigChi]`. Establish `hsm : ‖ι.symm (coef E 0 * coef G 1)‖ < 1` using `small_mul ι hc (hGint 1)`. Rewrite using `[hfcoef 1 le_rfl, map_sub, hs1, map_one, sub_eq_add_neg, IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]`. Rewrite using `[norm_neg, norm_one]`. Conclude with `max_eq_left hsm.le`.

Rewrite using `[norm_neg, norm_one]`. Conclude with `hsm.ne'`. Establish `hCj : Cj k (M * w) χ f`. Introduce `σ`. Establish `hprim'` using `primCj (M * w) χ σ hprim`.

Establish `hχk' : (cj σ χ) (-1) = (-1) ^ k`. Rewrite using `[MulChar.ringHomComp_apply, hχk]`. Simplify using the standard rewrite rules. Take `⟨E', hE'c, hE'v, hE'n, hE'0⟩` from `eisChi (M * w) k h1N hk3 (cj σ χ) hprim' hχk'`. Take `⟨G', hG'c, hG'v, hG'n⟩` from `hGσ σ`.

Establish `hG'0 : coef G' 0 = 1`. Rewrite using `[hG'n, hG0, map_one]`. Take `⟨f', hf'c, hf'n⟩` from `cusp_comb (cj σ χ) E' G' hE'c hG'c hE'v hG'v hG'0`. Establish `hc' : coef E' 0 = σ (coef E 0)` using `constCj (M * w) k h1N χ hprim σ (coef E 0) (coef E' 0) hE0 hE'0`. Use `⟨f', hf'c, fun n hn => ?_⟩` and prove the remaining obligations.

Rewrite using `[hf'n, hE'n n hn, hc', hG'n, hfcoef n hn, map_sub, map_mul, sig_cj]`. Use `eigLiftC l ι (M * w) k (by omega) χ f hfc hCj hfint hf1 (fun p => 1 + χ p * (p : ℂ) ^ (k - 1)) ?_` and prove the remaining obligations. Introduce `p hp`. Establish `hone : ‖ι.symm (1 : ℂ)‖ ≤ 1`. Rewrite using `[map_one, norm_one]`.

Use `⟨int_add ι hone (int_term ι k χ p), fun n hn => ?_⟩` and prove the remaining obligations. Establish `hkey : (coef f (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)) - (1 + χ p * (p : ℂ) ^ (k - 1)) * coef f n = coef E 0 * -((coef G (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef G (n / p) else 0)) - (1 + χ p * (p : ℂ) ^ (k - 1)) * coef G n)`. Establish `hpn : 1 ≤ p * n` using `Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega))`. Establish `hs` using `sig_hecke k χ hp n hn`. Rewrite using `[hfcoef _ hpn, hfcoef n hn]`.

Use `split_ifs at hs ⊢ with hd`. Establish `hnp : 1 ≤ n / p` using `Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos`. Rewrite using `[hfcoef _ hnp]`. Take the linear combination `hs`. Take the linear combination `hs`.

Use `beta_reduce`. Rewrite using `[hkey]`. Use `small_mul ι hc ?_` and prove the remaining obligations. Rewrite using `[map_neg, norm_neg]`. Establish `hite : ‖ι.symm (if p ∣ n then coef G (n / p) else 0)‖ ≤ 1` using `by split_ifs`.

Conclude with `hGint _`. Rewrite using `[map_zero, norm_zero]`. Conclude with `zero_le_one`. Conclude with `int_sub ι (int_add ι (hGint _) (int_mul ι (int_term ι k χ p) hite)) (int_mul ι (int_add ι hone (int_term ι k χ p)) (hGint n))`.
-/
theorem UpperTheory.V.Z.Sym.Unl.propEC :
    UpperTheory.V.Z.Sym.Unl.PropEC := by
  unfold UpperTheory.V.Z.Sym.Unl.PropEC
  intro l _ ι M w φ θ χ h
  have hM := h.one_lt
  have hw := h.prime
  have hl : l.Prime := Fact.out
  haveI : NeZero (M * w) := ⟨mul_ne_zero (by omega) hw.ne_zero⟩
  have hN3 : 3 ≤ M * w := by
    have := hw.two_le
    nlinarith
  have hlN : ¬ l ∣ M * w := by
    intro hd
    rcases (Nat.Prime.dvd_mul hl).mp hd with h1 | h1
    · exact h.cop h1
    · have h2 := h.dvd
      have h3 : l ∣ 1 := (Nat.dvd_add_right h2).mp (by rwa [Nat.sub_add_cancel hw.one_le])
      exact hl.one_lt.ne' (Nat.dvd_one.mp h3)
  obtain ⟨k₀, hk₀⟩ := unitFormC l h.odd ι (M * w) hN3 hlN
  refine ⟨max k₀ 3, fun k hk hφk => ?_⟩
  have hk1 : k₀ ≤ k := le_trans (le_max_left _ _) hk
  have hk3 : 3 ≤ k := le_trans (le_max_right _ _) hk
  have hχk : χ (-1) = (-1) ^ k := by
    rw [chi_neg_one hl h, hφk]
  have hprim : χ.IsPrimitive := ePrim l M w φ θ χ h
  have h1N : 1 < M * w := by omega
  obtain ⟨E, hEc, hEv, hEn, hE0⟩ := eisChi (M * w) k h1N hk3 χ hprim hχk
  obtain ⟨G, hGc, hGi, hGv, hG0, hGσ⟩ := hk₀ k hk1 χ hχk
  obtain ⟨f, hfc, hfn⟩ := cusp_comb χ E G hEc hGc hEv hGv hG0
  have hc : ‖ι.symm (coef E 0)‖ < 1 := constSmall l ι M w φ θ χ h k (by omega) (coef E 0) hE0
  have hGint : ∀ n, ‖ι.symm (coef G n)‖ ≤ 1 := hGi
  have hfcoef : ∀ n, 1 ≤ n → coef f n = sigChi k χ n - coef E 0 * coef G n := by
    intro n hn
    rw [hfn, hEn n hn]
  have hfint : UpperTheory.V.Sd.IntQ ι f := by
    intro n
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · rw [hfn, hG0, mul_one, sub_self, map_zero, norm_zero]
      exact zero_le_one
    · rw [hfcoef n hn]
      exact int_sub ι (int_sig ι k χ n) (int_mul ι hc.le (hGint n))
  have hf1 : ‖ι.symm (coef f 1)‖ = 1 := by
    have hs1 : sigChi k χ 1 = 1 := by simp [sigChi]
    have hsm : ‖ι.symm (coef E 0 * coef G 1)‖ < 1 := small_mul ι hc (hGint 1)
    rw [hfcoef 1 le_rfl, map_sub, hs1, map_one, sub_eq_add_neg,
      IsUltrametricDist.norm_add_eq_max_of_norm_ne_norm]
    · rw [norm_neg, norm_one]
      exact max_eq_left hsm.le
    · rw [norm_neg, norm_one]
      exact hsm.ne'
  have hCj : Cj k (M * w) χ f := by
    intro σ
    have hprim' := primCj (M * w) χ σ hprim
    have hχk' : (cj σ χ) (-1) = (-1) ^ k := by
      rw [MulChar.ringHomComp_apply, hχk]
      simp
    obtain ⟨E', hE'c, hE'v, hE'n, hE'0⟩ := eisChi (M * w) k h1N hk3 (cj σ χ) hprim' hχk'
    obtain ⟨G', hG'c, hG'v, hG'n⟩ := hGσ σ
    have hG'0 : coef G' 0 = 1 := by
      rw [hG'n, hG0, map_one]
    obtain ⟨f', hf'c, hf'n⟩ := cusp_comb (cj σ χ) E' G' hE'c hG'c hE'v hG'v hG'0
    have hc' : coef E' 0 = σ (coef E 0) :=
      constCj (M * w) k h1N χ hprim σ (coef E 0) (coef E' 0) hE0 hE'0
    refine ⟨f', hf'c, fun n hn => ?_⟩
    rw [hf'n, hE'n n hn, hc', hG'n, hfcoef n hn, map_sub, map_mul, sig_cj]
  refine eigLiftC l ι (M * w) k (by omega) χ f hfc hCj hfint hf1
    (fun p => 1 + χ p * (p : ℂ) ^ (k - 1)) ?_
  intro p hp
  have hone : ‖ι.symm (1 : ℂ)‖ ≤ 1 := by
    rw [map_one, norm_one]
  refine ⟨int_add ι hone (int_term ι k χ p), fun n hn => ?_⟩
  have hkey : (coef f (p * n) + χ p * (p : ℂ) ^ (k - 1) * (if p ∣ n then coef f (n / p) else 0)) -
      (1 + χ p * (p : ℂ) ^ (k - 1)) * coef f n =
      coef E 0 * -((coef G (p * n) + χ p * (p : ℂ) ^ (k - 1) *
        (if p ∣ n then coef G (n / p) else 0)) - (1 + χ p * (p : ℂ) ^ (k - 1)) * coef G n) := by
    have hpn : 1 ≤ p * n := Nat.one_le_iff_ne_zero.mpr (mul_ne_zero hp.ne_zero (by omega))
    have hs := sig_hecke k χ hp n hn
    rw [hfcoef _ hpn, hfcoef n hn]
    split_ifs at hs ⊢ with hd
    · have hnp : 1 ≤ n / p := Nat.div_pos (Nat.le_of_dvd (by omega) hd) hp.pos
      rw [hfcoef _ hnp]
      linear_combination hs
    · linear_combination hs
  beta_reduce
  rw [hkey]
  refine small_mul ι hc ?_
  rw [map_neg, norm_neg]
  have hite : ‖ι.symm (if p ∣ n then coef G (n / p) else 0)‖ ≤ 1 := by
    split_ifs
    · exact hGint _
    · rw [map_zero, norm_zero]
      exact zero_le_one
  exact int_sub ι (int_add ι (hGint _) (int_mul ι (int_term ι k χ p) hite))
    (int_mul ι (int_add ι hone (int_term ι k χ p)) (hGint n))
