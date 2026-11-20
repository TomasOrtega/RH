import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModDefs
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModBasic
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.CoeffRescaleExpandOfNotDvd

noncomputable section
open scoped BigOperators Classical UpperHalfPlane MatrixGroups CongruenceSubgroup Manifold
open ModularForm EisensteinSeries ModularFormClass UpperHalfPlane Formalism.L2.Th1.CM

namespace ReciprocityTheory.ChartRestriction.L1

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use extensionality with `n`. Establish `key` using `congrArg (fun q => Polynomial.coeff q n) (PowerSeries.trunc_trunc_pow (n := n + 1) f p)`. Simplify using `only [PowerSeries.coeff_trunc, Nat.lt_add_one, ↓reduceIte] at key`. Rewrite using `[← key, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]`.

Simplify using `only [xp, PowerSeries.coeff_mk]`. Use `split_ifs with h`. Rewrite using `[PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]`. Both sides reduce to the same expression.
-/
theorem xp_zmod {p : ℕ} (hp : p.Prime) (f : PowerSeries (ZMod p)) : xp p f = f ^ p := by
  haveI := Fact.mk hp
  ext n
  have key := congrArg (fun q => Polynomial.coeff q n) (PowerSeries.trunc_trunc_pow (n := n + 1) f p)
  simp only [PowerSeries.coeff_trunc, Nat.lt_add_one, ↓reduceIte] at key
  rw [← key, ← Polynomial.coe_pow, Polynomial.coeff_coe, ← ZMod.expand_card, Polynomial.coeff_expand hp.pos]
  simp only [xp, PowerSeries.coeff_mk]
  split_ifs with h
  · rw [PowerSeries.coeff_trunc, if_pos (Nat.lt_succ_of_le (Nat.div_le_self n p))]
  · rfl

/- English proof (translation)
Establish `hd : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n h`. Introduce `n`. Establish `h1` using `congrArg (PowerSeries.coeff n) h0`. Rewrite `h1` using `[PowerSeries.coeff_map, map_zero, eq_intCast]`. Conclude with `(CharP.intCast_eq_zero_iff (ZMod p) p _).1 h1`.

Use `⟨PowerSeries.mk fun n => PowerSeries.coeff n h / p, ?_⟩` and prove the remaining obligations. Use extensionality with `n`. Rewrite using `[PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hd n)]`.
-/
theorem exists_C_mul_of_map_eq_zero {p : ℕ} (h : PowerSeries ℤ)
    (h0 : h.map (Int.castRingHom (ZMod p)) = 0) :
    ∃ g : PowerSeries ℤ, h = PowerSeries.C (p : ℤ) * g := by
  have hd : ∀ n, (p : ℤ) ∣ PowerSeries.coeff n h := by
    intro n
    have h1 := congrArg (PowerSeries.coeff n) h0
    rw [PowerSeries.coeff_map, map_zero, eq_intCast] at h1
    exact (CharP.intCast_eq_zero_iff (ZMod p) p _).1 h1
  refine ⟨PowerSeries.mk fun n => PowerSeries.coeff n h / p, ?_⟩
  ext n
  rw [PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, Int.mul_ediv_cancel' (hd n)]

/- English proof (translation)
Establish `hmap : (xp p f).map (Int.castRingHom (ZMod p)) = xp p (f.map (Int.castRingHom (ZMod p)))`. Use extensionality with `n`. Simplify using `only [xp, PowerSeries.coeff_map, PowerSeries.coeff_mk]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `h0 : (xp p f - f ^ p).map (Int.castRingHom (ZMod p)) = 0`.

Rewrite using `[map_sub, map_pow, hmap, xp_zmod hp, sub_self]`. Take `⟨g, hg⟩` from `exists_C_mul_of_map_eq_zero (p := p) _ h0`. Conclude with `⟨g, by rw [← hg]; ring⟩`.
-/
theorem xp_congr {p : ℕ} (hp : p.Prime) (f : PowerSeries ℤ) :
    ∃ g : PowerSeries ℤ, xp p f = f ^ p + PowerSeries.C (p : ℤ) * g := by
  have hmap : (xp p f).map (Int.castRingHom (ZMod p)) = xp p (f.map (Int.castRingHom (ZMod p))) := by
    ext n
    simp only [xp, PowerSeries.coeff_map, PowerSeries.coeff_mk]
    split_ifs <;> simp
  have h0 : (xp p f - f ^ p).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, hmap, xp_zmod hp, sub_self]
  obtain ⟨g, hg⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨g, by rw [← hg]; ring⟩

/- English proof (translation)
Use `haveI := Fact.mk hp`. Use `haveI : CharP (PowerSeries (ZMod p)) p := charP_of_injective_algebraMap (algebraMap (ZMod p) (PowerSeries (ZMod p))).injective p`. Establish `h0 : ((f - g) ^ p - (f ^ p - g ^ p)).map (Int.castRingHom (ZMod p)) = 0`. Rewrite using `[map_sub, map_pow, map_sub, map_sub, map_pow, map_pow, sub_pow_char, sub_self]`. Take `⟨w, hw⟩` from `exists_C_mul_of_map_eq_zero (p := p) _ h0`.

Conclude with `⟨w, by rw [← hw]; ring⟩`.
-/
theorem sub_pow_congr {p : ℕ} (hp : p.Prime) (f g : PowerSeries ℤ) :
    ∃ w : PowerSeries ℤ, (f - g) ^ p = f ^ p - g ^ p + PowerSeries.C (p : ℤ) * w := by
  haveI := Fact.mk hp
  haveI : CharP (PowerSeries (ZMod p)) p :=
    charP_of_injective_algebraMap (algebraMap (ZMod p) (PowerSeries (ZMod p))).injective p
  have h0 : ((f - g) ^ p - (f ^ p - g ^ p)).map (Int.castRingHom (ZMod p)) = 0 := by
    rw [map_sub, map_pow, map_sub, map_sub, map_pow, map_pow, sub_pow_char, sub_self]
  obtain ⟨w, hw⟩ := exists_C_mul_of_map_eq_zero (p := p) _ h0
  exact ⟨w, by rw [← hw]; ring⟩

/- English proof (translation)
Use `⟨PowerSeries.mk fun n => -(∑ i ∈ Finset.range (b * n), zetaC p ^ i) * ((PowerSeries.coeff n f : ℤ) : ℂ), ?_, ?_⟩` and prove the remaining obligations. Introduce `n`. Rewrite using `[PowerSeries.coeff_mk]`. Conclude with `mul_mem (neg_mem (sum_mem fun i _ => pow_mem (Subring.subset_closure (Set.mem_singleton _)) _)) (intCast_mem _ _)`. Use extensionality with `n`.

Simplify using `only [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_C_mul, PowerSeries.coeff_mk, eq_intCast]`. Establish `hg` using `geom_sum_mul (zetaC p) (b * n)`. Take the linear combination `(-((PowerSeries.coeff n f : ℤ) : ℂ)) * hg`.
-/
theorem rescale_congr {p : ℕ} (hp : 0 < p) (b : ℕ) (f : PowerSeries ℤ) :
    ∃ w : PowerSeries ℂ, CoeffIn (Rm p) w ∧
      PowerSeries.rescale (zetaC p ^ b) (f.map (Int.castRingHom ℂ)) =
        f.map (Int.castRingHom ℂ) + PowerSeries.C (1 - zetaC p) * w := by
  refine ⟨PowerSeries.mk fun n => -(∑ i ∈ Finset.range (b * n), zetaC p ^ i) * ((PowerSeries.coeff n f : ℤ) : ℂ), ?_, ?_⟩
  · intro n
    rw [PowerSeries.coeff_mk]
    exact mul_mem (neg_mem (sum_mem fun i _ => pow_mem (Subring.subset_closure (Set.mem_singleton _)) _))
      (intCast_mem _ _)
  · ext n
    simp only [map_add, PowerSeries.coeff_rescale, PowerSeries.coeff_map, PowerSeries.coeff_C_mul,
      PowerSeries.coeff_mk, eq_intCast]
    have hg := geom_sum_mul (zetaC p) (b * n)
    linear_combination (-((PowerSeries.coeff n f : ℤ) : ℂ)) * hg

/- English proof (translation)
The claim follows from `Complex.isPrimitiveRoot_exp p hp`.
-/
theorem zetaC_isPrimitiveRoot {p : ℕ} (hp : p ≠ 0) : IsPrimitiveRoot (zetaC p) p := Complex.isPrimitiveRoot_exp p hp

/- English proof (translation)
Use `haveI := Fact.mk hp`. Establish `hζ` using `zetaC_isPrimitiveRoot hp.ne_zero`. Establish `hmem : ∀ μ ∈ primitiveRoots p ℂ, μ ∈ Rm p`. Introduce `μ hμ`. Rewrite `hμ` using `[mem_primitiveRoots hp.pos]`.

Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one`. Conclude with `pow_mem (Subring.subset_closure (Set.mem_singleton _)) _`. Establish `hprod : (p : ℂ) = ∏ μ ∈ primitiveRoots p ℂ, (1 - μ)`. Establish `h1` using `Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := p)`. Rewrite `h1` using `[Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod]`.

Simplify using `using h1.symm`. Use `⟨∏ μ ∈ (primitiveRoots p ℂ).erase (zetaC p), (1 - μ), prod_mem fun μ hμ => sub_mem (one_mem _) (hmem μ (Finset.mem_of_mem_erase hμ)), ?_⟩` and prove the remaining obligations. Rewrite using `[hprod, Finset.mul_prod_erase _ _ ((mem_primitiveRoots hp.pos).2 hζ)]`.
-/
theorem p_mem_span {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (p : ℂ) = (1 - zetaC p) * r := by
  haveI := Fact.mk hp
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hmem : ∀ μ ∈ primitiveRoots p ℂ, μ ∈ Rm p := by
    intro μ hμ
    rw [mem_primitiveRoots hp.pos] at hμ
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hμ.pow_eq_one
    exact pow_mem (Subring.subset_closure (Set.mem_singleton _)) _
  have hprod : (p : ℂ) = ∏ μ ∈ primitiveRoots p ℂ, (1 - μ) := by
    have h1 := Polynomial.eval_one_cyclotomic_prime (R := ℂ) (p := p)
    rw [Polynomial.cyclotomic_eq_prod_X_sub_primitiveRoots hζ, Polynomial.eval_prod] at h1
    simpa using h1.symm
  refine ⟨∏ μ ∈ (primitiveRoots p ℂ).erase (zetaC p), (1 - μ),
    prod_mem fun μ hμ => sub_mem (one_mem _) (hmem μ (Finset.mem_of_mem_erase hμ)), ?_⟩
  rw [hprod, Finset.mul_prod_erase _ _ ((mem_primitiveRoots hp.pos).2 hζ)]

/- English proof (translation)
Establish `hζ` using `zetaC_isPrimitiveRoot hp.ne_zero`. Establish `hz : zetaC p ∈ Rm p` using `Subring.subset_closure (Set.mem_singleton _)`. Use `set z : Rm p := ⟨zetaC p, hz⟩ with hzdef`. Establish `hzc : (z : ℂ) = zetaC p` using `rfl`. Take `⟨r, hr⟩` from `exists_add_pow_prime_eq hp (1 : Rm p) (-z)`.

Establish `hr' : (1 - zetaC p) ^ p = 1 + (-zetaC p) ^ p + p * (-(zetaC p * (r : ℂ)))`. Establish `h1` using `congrArg (fun x : Rm p => (x : ℂ)) hr`. Move the coercions through the operations in `at h1`. Rewrite `h1` using `[hzc]`. Rewrite using `[sub_eq_add_neg, h1]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hm : -(zetaC p * (r : ℂ)) ∈ Rm p` using `neg_mem (mul_mem hz r.2)`. Break down `hp.eq_two_or_odd' with rfl | hodd` into its components or cases. Use `⟨1 + -(zetaC 2 * (r : ℂ)), add_mem (one_mem _) hm, ?_⟩` and prove the remaining obligations. Rewrite using `[hr', neg_sq, hζ.pow_eq_one]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Use `⟨-(zetaC p * (r : ℂ)), hm, ?_⟩` and prove the remaining obligations. Rewrite using `[hr', hodd.neg_pow, hζ.pow_eq_one]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem one_sub_zeta_pow {p : ℕ} (hp : p.Prime) : ∃ r ∈ Rm p, (1 - zetaC p) ^ p = (p : ℂ) * r := by
  have hζ := zetaC_isPrimitiveRoot hp.ne_zero
  have hz : zetaC p ∈ Rm p := Subring.subset_closure (Set.mem_singleton _)
  set z : Rm p := ⟨zetaC p, hz⟩ with hzdef
  have hzc : (z : ℂ) = zetaC p := rfl
  obtain ⟨r, hr⟩ := exists_add_pow_prime_eq hp (1 : Rm p) (-z)
  have hr' : (1 - zetaC p) ^ p = 1 + (-zetaC p) ^ p + p * (-(zetaC p * (r : ℂ))) := by
    have h1 := congrArg (fun x : Rm p => (x : ℂ)) hr
    push_cast at h1
    rw [hzc] at h1
    rw [sub_eq_add_neg, h1]
    ring
  have hm : -(zetaC p * (r : ℂ)) ∈ Rm p := neg_mem (mul_mem hz r.2)
  rcases hp.eq_two_or_odd' with rfl | hodd
  · refine ⟨1 + -(zetaC 2 * (r : ℂ)), add_mem (one_mem _) hm, ?_⟩
    rw [hr', neg_sq, hζ.pow_eq_one]
    push_cast
    ring
  · refine ⟨-(zetaC p * (r : ℂ)), hm, ?_⟩
    rw [hr', hodd.neg_pow, hζ.pow_eq_one]
    ring

/- English proof (translation)
Conclude with `sub_ne_zero.2 ((zetaC_isPrimitiveRoot hp.ne_zero).ne_one hp.one_lt).symm`.
-/
theorem one_sub_zeta_ne_zero {p : ℕ} (hp : p.Prime) : 1 - zetaC p ≠ 0 := by
  exact sub_ne_zero.2 ((zetaC_isPrimitiveRoot hp.ne_zero).ne_one hp.one_lt).symm

end ReciprocityTheory.ChartRestriction.L1
