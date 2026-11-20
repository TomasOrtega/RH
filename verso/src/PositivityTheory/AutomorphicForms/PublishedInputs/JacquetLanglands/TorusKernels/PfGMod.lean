import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.TorusKernels.IsHolVOf

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped NNReal

namespace UpperTheory.Esk.ModulusCharacterLemmas

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Rewrite using `[WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]`. Both sides reduce to the same expression.
-/
theorem tnn {e : ℝ≥0} (he : e ≠ 0) (m : ℤ) : WithZeroMulInt.toNNReal he (WithZero.exp m) = e ^ m := by
  rw [WithZeroMulInt.toNNReal_neg_apply he WithZero.exp_ne_zero]; rfl

/- English proof (translation)
Rewrite using `[WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul, ← ofAdd_zsmul, ← ofAdd_add]`. Simplify using the standard rewrite rules.
-/
theorem exp_mul_pow (m : ℤ) :
    WithZero.exp m * (WithZero.exp (-1 : ℤ)) ^ m = (1 : WithZero (Multiplicative ℤ)) := by
  rw [WithZero.exp_eq_coe_ofAdd, WithZero.exp_eq_coe_ofAdd, ← WithZero.coe_zpow, ← WithZero.coe_mul,
    ← ofAdd_zsmul, ← ofAdd_add]
  simp

/- English proof (translation)
Assemble the required witnesses or components as `⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩`.
-/
theorem val_exp {w : Pl F} {x : w.adicCompletion F} (hx : x ≠ 0) : ∃ m : ℤ, Valued.v x = WithZero.exp m :=
  ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 hx)).symm⟩

/- English proof (translation)
Rewrite using `[FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]`.
-/
theorem norm_eq (w : Pl F) {x : w.adicCompletion F} {m : ℤ} (hm : Valued.v x = WithZero.exp m) :
    ‖x‖ = ((Ideal.absNorm w.asIdeal : ℕ) : ℝ) ^ m := by
  rw [FinitePlace.norm_def (x := x), hm, tnn, NNReal.coe_zpow, NNReal.coe_natCast]

/- English proof (translation)
Simplify using `[normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]`.
-/
theorem normV_eq (w : Pl F) : normV w = Ideal.absNorm w.asIdeal := by
  simp [normV, Ideal.absNorm_apply, Submodule.cardQuot_apply]

/- English proof (translation)
Establish `e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l])` using `by rw [map_natCast, map_natCast]`. Apply `NNReal.coe_injective` to reduce the goal to its premises. Rewrite using `[nu_apply, coe_nnnorm, e, norm_algebraMap', Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]`.
-/
theorem nu_nat {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {n : ℕ} (h : ¬ l ∣ n) : nu ι (n : ℂ) = 1 := by
  have e : ι.symm (n : ℂ) = algebraMap ℚ_[l] (Qbar l) (n : ℚ_[l]) := by rw [map_natCast, map_natCast]
  apply NNReal.coe_injective
  rw [nu_apply, coe_nnnorm, e, norm_algebraMap',
    Padic.norm_natCast_eq_one_iff.2 ((Nat.Prime.coprime_iff_not_dvd Fact.out).2 h), NNReal.coe_one]

/- English proof (translation)
Introduce `hd`. Use `haveI := w.isPrime`. Establish `hne : normV w ≠ 0`. Rewrite using `[normV_eq]`. Use `HeightOneSpectrum.one_lt_absNorm w` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Use `haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne`. Use `haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)`. Establish `hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal)` using `by rw [Fintype.card_eq_nat_card]; exact hd`. Take `⟨a, ha⟩` from `exists_prime_addOrderOf_dvd_card l hd'`.

Establish `h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0` using `by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]`. Establish `h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `h`. Establish `h3 : a = 0` using `(mul_eq_zero.1 h1).resolve_left h2`.

Rewrite `ha` using `[h3, addOrderOf_zero]`. Conclude with `hl.out.one_lt.ne ha`.
-/
theorem not_dvd (w : Pl F) {l : ℕ} [hl : Fact l.Prime] (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal) : ¬ l ∣ normV w := by
  intro hd
  haveI := w.isPrime
  have hne : normV w ≠ 0 := by
    rw [normV_eq]; have := HeightOneSpectrum.one_lt_absNorm w; omega
  haveI : Finite (𝓞 F ⧸ w.asIdeal) := Nat.finite_of_card_ne_zero hne
  haveI := Fintype.ofFinite (𝓞 F ⧸ w.asIdeal)
  have hd' : l ∣ Fintype.card (𝓞 F ⧸ w.asIdeal) := by rw [Fintype.card_eq_nat_card]; exact hd
  obtain ⟨a, ha⟩ := exists_prime_addOrderOf_dvd_card l hd'
  have h1 : (l : 𝓞 F ⧸ w.asIdeal) * a = 0 := by rw [← nsmul_eq_mul, ← ha, addOrderOf_nsmul_eq_zero]
  have h2 : (l : 𝓞 F ⧸ w.asIdeal) ≠ 0 := by
    rw [← map_natCast (Ideal.Quotient.mk w.asIdeal), Ne, Ideal.Quotient.eq_zero_iff_mem]; exact h
  have h3 : a = 0 := (mul_eq_zero.1 h1).resolve_left h2
  rw [h3, addOrderOf_zero] at ha
  exact hl.out.one_lt.ne ha

/- English proof (translation)
Take `⟨m, hm⟩` from `val_exp hx`. Rewrite using `[norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h), one_zpow]`.
-/
theorem away {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) (w : Pl F) (h : ((l : ℕ) : 𝓞 F) ∉ w.asIdeal)
    {x : w.adicCompletion F} (hx : x ≠ 0) : nu ι (‖x‖ : ℂ) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  rw [norm_eq w hm, Complex.ofReal_zpow, Complex.ofReal_natCast, map_zpow₀, ← normV_eq, nu_nat ι (not_dvd w h),
    one_zpow]

/- English proof (translation)
Take `⟨m, hm⟩` from `val_exp hx`. Use `set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL`. Establish `hLv : Valued.v L = WithZero.exp (-1 : ℤ)` using `D.unif v`. Establish `hL0 : L ≠ 0` using `fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm`. Establish `hemL : D.em v L = (l : ℂ)` using `map_natCast _ l`.

Establish `hl0 : (l : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero`. Establish `hy : Valued.v (x * L ^ m) = 1` using `by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]`. Establish `hnu : nu ι (D.em v (x * L ^ m)) = 1` using `le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)`. Establish `hn : ‖x‖ = (l : ℝ) ^ m` using `by rw [norm_eq _ hm, ← normV_eq, D.norm v]`. Establish `e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m)`.

Rewrite using `[hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hnu]`.
-/
theorem atL {l : ℕ} [Fact l.Prime] {ι : Qbar l ≃+* ℂ} (D : LDat F ι) (v : InfinitePlace F)
    {x : (D.pl v).adicCompletion F} (hx : x ≠ 0) : nu ι ((‖x‖ : ℂ) * D.em v x) = 1 := by
  obtain ⟨m, hm⟩ := val_exp hx
  set L : (D.pl v).adicCompletion F := ((l : ℕ) : (D.pl v).adicCompletion F) with hL
  have hLv : Valued.v L = WithZero.exp (-1 : ℤ) := D.unif v
  have hL0 : L ≠ 0 := fun h => by rw [h, map_zero] at hLv; exact WithZero.exp_ne_zero hLv.symm
  have hemL : D.em v L = (l : ℂ) := map_natCast _ l
  have hl0 : (l : ℂ) ≠ 0 := Nat.cast_ne_zero.2 (Fact.out : l.Prime).ne_zero
  have hy : Valued.v (x * L ^ m) = 1 := by rw [map_mul, map_zpow₀, hLv, hm, exp_mul_pow]
  have hnu : nu ι (D.em v (x * L ^ m)) = 1 :=
    le_antisymm ((D.le v _).2 hy.le) (not_lt.1 fun h => ((D.lt v _).1 h).ne hy)
  have hn : ‖x‖ = (l : ℝ) ^ m := by rw [norm_eq _ hm, ← normV_eq, D.norm v]
  have e : (‖x‖ : ℂ) * D.em v x = D.em v (x * L ^ m) := by
    rw [hn, map_mul, map_zpow₀, hemL, Complex.ofReal_zpow, Complex.ofReal_natCast]
    ring
  rw [e, hnu]

/- English proof (translation)
The claim follows from `le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le) ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)`.
-/
theorem nrm_unit {w : Pl F} {x : w.adicCompletion F} (h : Valued.v x = 1) : ‖x‖ = 1 :=
  le_antisymm ((Valued.toNormedField.norm_le_one_iff (x := x)).2 h.le)
    ((Valued.toNormedField.one_le_norm_iff (x := x)).2 h.ge)

/- English proof (translation)
Establish `h1` using `Filter.eventually_cofinite.1 (y : Af F).2`. Establish `h2` using `Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2`. Use `(h1.union h2).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hc`. Simplify using `only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc`.

Establish `a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1` using `hc.1`. Establish `a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1` using `hc.2`. Establish `a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1`. Rewrite using `[← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]`. Use `hw (nrm_unit (le_antisymm a1 ?_))` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem fin_supp (y : (Af F)ˣ) : (Function.mulSupport fun w : Pl F => ‖pLoc F w (y : Af F)‖).Finite := by
  have h1 := Filter.eventually_cofinite.1 (y : Af F).2
  have h2 := Filter.eventually_cofinite.1 ((y⁻¹ : (Af F)ˣ) : Af F).2
  refine (h1.union h2).subset fun w hw => ?_
  by_contra hc
  simp only [Set.mem_union, Set.mem_setOf_eq, not_or, not_not] at hc
  have a1 : Valued.v (pLoc F w (y : Af F)) ≤ 1 := hc.1
  have a2 : Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) ≤ 1 := hc.2
  have a3 : Valued.v (pLoc F w (y : Af F)) * Valued.v (pLoc F w ((y⁻¹ : (Af F)ˣ) : Af F)) = 1 := by
    rw [← map_mul, ← map_mul, Units.mul_inv, map_one, map_one]
  refine hw (nrm_unit (le_antisymm a1 ?_))
  calc 1 = _ := a3.symm
    _ ≤ Valued.v (pLoc F w (y : Af F)) * 1 := mul_le_mul_right a2 _
    _ = _ := mul_one _

end UpperTheory.Esk.ModulusCharacterLemmas

open UpperTheory.Esk.ModulusCharacterLemmas in
/- English proof (translation)
Introduce `F _ _ l _ ι D z`. Establish `hz : ∀ w, pLoc F w (z : Af F) ≠ 0` using `fun w => (z.isUnit.map (pLoc F w)).ne_zero`. Establish `habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖` using `rfl`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[habs]`.

Conclude with `finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)`. Establish `hfin` using `fin_supp z`. Use `set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def`. Establish `hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖`. Rewrite using `[habs]`.

Use `finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_` and prove the remaining obligations. Rewrite using `[hs_def, Finset.coe_union]`. Conclude with `Or.inl (hfin.mem_toFinset.2 hw)`. Establish `hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F)` using `(Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm`. Rewrite using `[hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]`.

Use `Finset.prod_eq_one fun w _ => ?_` and prove the remaining obligations. Distinguish the cases in `hw : ∃ v, D.pl v = w`. Take `⟨v, rfl⟩` from `hw`. Establish `e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v}`. Use extensionality with `u`.

Simplify using `[D.inj.eq_iff]`. Rewrite using `[e, Finset.prod_singleton]`. Conclude with `atL D v (hz _)`. Establish `e : Finset.univ.filter (fun u => D.pl u = w) = ∅`. Use extensionality with `u`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]`. Conclude with `fun h => hw ⟨u, h⟩`. Rewrite using `[e, Finset.prod_empty, mul_one]`. Conclude with `away ι w (fun h => hw (D.surj w h)) (hz w)`.
-/
theorem UpperTheory.Esk.pf_GMod : UpperTheory.Esk.GMod := by
  intro F _ _ l _ ι D z
  have hz : ∀ w, pLoc F w (z : Af F) ≠ 0 := fun w => (z.isUnit.map (pLoc F w)).ne_zero
  have habs : absF z = ∏ᶠ w : Pl F, ‖pLoc F w (z : Af F)‖ := rfl
  refine ⟨?_, ?_⟩
  · rw [habs]
    exact finprod_induction (fun x : ℝ => 0 < x) one_pos (fun _ _ => mul_pos) fun w => norm_pos_iff.2 (hz w)
  classical
  have hfin := fin_supp z
  set s : Finset (Pl F) := hfin.toFinset ∪ Finset.univ.image D.pl with hs_def
  have hs : absF z = ∏ w ∈ s, ‖pLoc F w (z : Af F)‖ := by
    rw [habs]
    refine finprod_eq_prod_of_mulSupport_subset _ fun w hw => ?_
    rw [hs_def, Finset.coe_union]
    exact Or.inl (hfin.mem_toFinset.2 hw)
  have hprod : ∏ v, D.ea v (z : Af F) = ∏ w ∈ s, ∏ v ∈ Finset.univ.filter (fun v => D.pl v = w), D.ea v (z : Af F) :=
    (Finset.prod_fiberwise_of_maps_to (fun v _ => by simp [hs_def]) _).symm
  rw [hs, hprod, Complex.ofReal_prod, ← Finset.prod_mul_distrib, map_prod]
  refine Finset.prod_eq_one fun w _ => ?_
  by_cases hw : ∃ v, D.pl v = w
  · obtain ⟨v, rfl⟩ := hw
    have e : Finset.univ.filter (fun u => D.pl u = D.pl v) = {v} := by
      ext u; simp [D.inj.eq_iff]
    rw [e, Finset.prod_singleton]
    exact atL D v (hz _)
  · have e : Finset.univ.filter (fun u => D.pl u = w) = ∅ := by
      ext u; simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false]
      exact fun h => hw ⟨u, h⟩
    rw [e, Finset.prod_empty, mul_one]
    exact away ι w (fun h => hw (D.surj w h)) (hz w)
