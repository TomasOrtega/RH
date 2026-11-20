import Mathlib
import Formalism.LocalToGlobal.UnitaryNorms.CharProd
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.ExistsPowLocKMulInf

open NumberField IsDedekindDomain

section
open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Col Formalism.L2.Ker Formalism.MainNotions GlobalTheory.CharVal GlobalTheory.IndefiniteRowSideFullHecke.CharacterValuation Formalism.L2.Host

variable {L : Type} [Field L] [NumberField L]

/- English proof (translation)
Establish `hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k` using `fun k => HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k`. Use `h (atFin v y) ((hval _).trans h2) ?_` and prove the remaining obligations. Establish `: ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 = algebraMap L (v.adicCompletion L) ((y : L) - 1)`. Rewrite using `[map_sub, map_one]`. Both sides reduce to the same expression.

Rewrite using `[this, hval]`. Simplify using `using h1`.
-/
private theorem locK_eq_one_of_two (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.LevelLe v 2) (y : Lˣ)
    (h2 : v.valuation L (y : L) = 1) (h1 : v.valuation L ((y : L) - 1) ≤ WithZero.exp (-2 : ℤ)) :
    χ.locK v y = 1 := by
  have hval : ∀ k : L, Valued.v (algebraMap L (v.adicCompletion L) k) = v.valuation L k := fun k =>
    HeightOneSpectrum.valuedAdicCompletion_eq_valuation' v k
  refine h (atFin v y) ((hval _).trans h2) ?_
  have : ((atFin v y : (v.adicCompletion L)ˣ) : v.adicCompletion L) - 1 =
      algebraMap L (v.adicCompletion L) ((y : L) - 1) := by
    rw [map_sub, map_one]; rfl
  rw [this, hval]
  simpa using h1

/- English proof (translation)
Establish `hfin : Finite (𝓞 L ⧸ v.asIdeal ^ 2)` using `Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero 2 v.ne_bot)`. Establish `hmax` using `v.isMaximal`. Use `⟨Nat.card (𝓞 L ⧸ v.asIdeal ^ 2)ˣ, Nat.card_pos, fun r hr => ?_⟩` and prove the remaining obligations. Establish `h0 : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ 2) r)`. Take `⟨y, i, hi, e⟩` from `hmax.exists_inv hr`.

Use `IsUnit.of_mul_eq_one (Ideal.Quotient.mk (v.asIdeal ^ 2) (y * (1 + i))) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← map_one (Ideal.Quotient.mk (v.asIdeal ^ 2)), Ideal.Quotient.eq]`. Establish `: r * (y * (1 + i)) - 1 = -(i ^ 2)`. Take the linear combination `(1 + i) * e`. Rewrite using `[this]`.

Conclude with `neg_mem (Ideal.pow_mem_pow hi 2)`. Establish `h1` using `congrArg Units.val (pow_card_eq_one' (x := h0.unit))`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]`. Rewrite `h1` using `[Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one]`. Then use the resulting hypothesis.
-/
private theorem exists_pow_sub_one_mem_two (v : HeightOneSpectrum (𝓞 L)) :
    ∃ m : ℕ, 0 < m ∧ ∀ r : 𝓞 L, r ∉ v.asIdeal → r ^ m - 1 ∈ v.asIdeal ^ 2 := by
  have hfin : Finite (𝓞 L ⧸ v.asIdeal ^ 2) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero 2 v.ne_bot)
  have hmax := v.isMaximal
  refine ⟨Nat.card (𝓞 L ⧸ v.asIdeal ^ 2)ˣ, Nat.card_pos, fun r hr => ?_⟩
  have h0 : IsUnit (Ideal.Quotient.mk (v.asIdeal ^ 2) r) := by
    obtain ⟨y, i, hi, e⟩ := hmax.exists_inv hr
    refine IsUnit.of_mul_eq_one (Ideal.Quotient.mk (v.asIdeal ^ 2) (y * (1 + i))) ?_
    rw [← map_mul, ← map_one (Ideal.Quotient.mk (v.asIdeal ^ 2)), Ideal.Quotient.eq]
    have : r * (y * (1 + i)) - 1 = -(i ^ 2) := by
      linear_combination (1 + i) * e
    rw [this]
    exact neg_mem (Ideal.pow_mem_pow hi 2)
  have h1 := congrArg Units.val (pow_card_eq_one' (x := h0.unit))
  rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, map_pow, map_one, sub_eq_zero]
  rwa [Units.val_pow_eq_pow_val, IsUnit.unit_spec, Units.val_one] at h1

/- English proof (translation)
Take `⟨m, hm, hpow⟩` from `exists_pow_sub_one_mem_two v`. Use `⟨m, hm, fun u hu => ?_⟩` and prove the remaining obligations. Take `⟨r, s, hs, hsr⟩` from `(intAt_iff (P := v) (u : L)).2 hu.le`. Establish `hsv : v.valuation L (algebraMap (𝓞 L) L s) = 1`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hs]`.

Establish `hr : r ∉ v.asIdeal`. Rewrite using `[← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]`. Use `show v.valuation L (algebraMap (𝓞 L) L r) = 1`. Rewrite using `[← hsr, map_mul, hsv, hu, one_mul]`. Establish `hs0 : algebraMap (𝓞 L) L s ≠ 0`.

Introduce `h0`. Rewrite `hsv` using `[h0, map_zero]`. Conclude with `zero_ne_one hsv`. Establish `hle : ∀ t : 𝓞 L, t ∉ v.asIdeal → v.valuation L (algebraMap (𝓞 L) L (t ^ m - 1)) ≤ WithZero.exp (-2 : ℤ)`. Introduce `t ht`.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h2` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).2 (hpow t ht)`. Simplify using `using h2`. Rewrite using `[← map_pow]`. Apply `locK_eq_one_of_two χ h` to reduce the goal to its premises.

Rewrite using `[Units.val_pow_eq_pow_val, map_pow, hu, one_pow]`. Establish `hu' : ((u ^ m : Lˣ) : L) - 1 = (algebraMap (𝓞 L) L (r ^ m - 1) - algebraMap (𝓞 L) L (s ^ m - 1)) / (algebraMap (𝓞 L) L s) ^ m`. Simplify using `only [map_sub, map_pow, map_one, Units.val_pow_eq_pow_val]`. Rewrite using `[eq_div_iff (pow_ne_zero _ hs0), ← hsr]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hu', map_div₀, map_pow, hsv, one_pow, div_one]`. Conclude with `le_trans (Valuation.map_sub _ _ _) (max_le (hle r hr) (hle s hs))`.
-/
private theorem exists_pow_locK_two (χ : HChar L) {v : HeightOneSpectrum (𝓞 L)} (h : χ.LevelLe v 2) :
    ∃ m : ℕ, 0 < m ∧ ∀ u : Lˣ, v.valuation L (u : L) = 1 → χ.locK v u ^ m = 1 := by
  obtain ⟨m, hm, hpow⟩ := exists_pow_sub_one_mem_two v
  refine ⟨m, hm, fun u hu => ?_⟩
  obtain ⟨r, s, hs, hsr⟩ := (intAt_iff (P := v) (u : L)).2 hu.le
  have hsv : v.valuation L (algebraMap (𝓞 L) L s) = 1 := by
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_eq_one_iff.2 hs]
  have hr : r ∉ v.asIdeal := by
    rw [← HeightOneSpectrum.intValuation_eq_one_iff, ← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    show v.valuation L (algebraMap (𝓞 L) L r) = 1
    rw [← hsr, map_mul, hsv, hu, one_mul]
  have hs0 : algebraMap (𝓞 L) L s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsv
    exact zero_ne_one hsv
  have hle : ∀ t : 𝓞 L, t ∉ v.asIdeal →
      v.valuation L (algebraMap (𝓞 L) L (t ^ m - 1)) ≤ WithZero.exp (-2 : ℤ) := by
    intro t ht
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    have h2 := (HeightOneSpectrum.intValuation_le_pow_iff_mem v _ 2).2 (hpow t ht)
    simpa using h2
  rw [← map_pow]
  apply locK_eq_one_of_two χ h
  · rw [Units.val_pow_eq_pow_val, map_pow, hu, one_pow]
  · have hu' : ((u ^ m : Lˣ) : L) - 1 = (algebraMap (𝓞 L) L (r ^ m - 1) -
        algebraMap (𝓞 L) L (s ^ m - 1)) / (algebraMap (𝓞 L) L s) ^ m := by
      simp only [map_sub, map_pow, map_one, Units.val_pow_eq_pow_val]
      rw [eq_div_iff (pow_ne_zero _ hs0), ← hsr]
      ring
    rw [hu', map_div₀, map_pow, hsv, one_pow, div_one]
    exact le_trans (Valuation.map_sub _ _ _) (max_le (hle r hr) (hle s hs))

end

open Formalism.L2.Host in
/- English proof (translation)
Introduce `E _ _ χ S hS hlev P k`. Take `⟨h, a, hh, haP, haQ⟩` from `GlobalTheory.TamePow.exists_gen P`. Take `⟨c, hc⟩ : ∃ c : ℤ, P.valuation E (k : E) = WithZero.exp c` from `⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)).symm⟩`. Use `choose mf hmf hmu using fun v => exists_pow_locK_two χ (hlev v)`. Establish `hPS : P ∈ S ∪ {P}` using `by simp`.

Take `⟨N, hN⟩ : ∃ N, N = ∏ v ∈ (S ∪ {P}).erase P, mf v` from `⟨_, rfl⟩`. Establish `hNpos : 0 < N`. Rewrite using `[hN]`. Conclude with `Finset.prod_pos (fun v _ => hmf v)`. Establish `hrule` using `Formalism.L2.Host.HChar.productRule χ (S ∪ {P}) (fun v hv => hS v (fun h' => hv (Finset.mem_union_left _ h'))) a`.

Establish `hfin : ∏ᶠ (v) (_ : v ∉ S ∪ {P}), χ.val v ^ ordF v a = 1`. Apply `finprod_eq_one_of_forall_eq_one` to reduce the goal to its premises. Introduce `v`. Rewrite using `[finprod_eq_if]`. Use `split_ifs with hv`.

Both sides reduce to the same expression. Establish `hvP : v ≠ P` using `fun e => hv (by simp [e])`. Establish `h0 : ordF v a = 0`. Simplify using `[Formalism.L2.Host.ordF, haQ v hvP]`. Rewrite using `[h0, zpow_zero]`.

Rewrite `hrule` using `[hfin, mul_one, ← Finset.mul_prod_erase (S ∪ {P}) (fun v => χ.locK v a) hPS, ← mul_assoc]`. Establish `hrest : (∏ v ∈ (S ∪ {P}).erase P, χ.locK v a) ^ N = 1`. Rewrite using `[← Finset.prod_pow]`. Apply `Finset.prod_eq_one` to reduce the goal to its premises. Introduce `v hv`.

Take `⟨d, hd⟩` from `Finset.dvd_prod_of_mem mf hv`. Rewrite using `[hN, hd, pow_mul, hmu v a (haQ v (Finset.ne_of_mem_erase hv)), one_pow]`. Establish `hA : (χ.inf a * χ.locK P a) ^ N = 1`. Establish `hp` using `congrArg (fun z => z ^ N) hrule`. Rewrite `hp` using `[mul_pow, hrest, mul_one, one_pow]`.

Conclude with `hp`. Establish `hw : P.valuation E ((k ^ h * a ^ c : Eˣ) : E) = 1`. Rewrite using `[Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow, map_zpow₀, hc, haP, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add, WithZero.exp_eq_one]`. Simplify using `only [nsmul_eq_mul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hwm` using `hmu P _ hw`. Rewrite `hwm` using `[map_mul, map_pow, map_zpow]`. Establish `htpos : 0 < mf P * N` using `Nat.mul_pos (hmf P) hNpos`. Use `⟨h * (mf P * N), a ^ (-(c * ((mf P * N : ℕ) : ℤ))), Nat.mul_pos hh htpos, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, haP, hc, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul, WithZero.exp_inj]`.

Simplify using `only [nsmul_eq_mul, smul_eq_mul]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Introduce `Q hQ`. Rewrite using `[Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]`.

Rewrite using `[map_zpow]`. Establish `e1 : χ.locK P k ^ (((h * (mf P * N) : ℕ)) : ℤ) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1`. Establish `hp` using `congrArg (fun z => z ^ N) hwm`. Simplify using `only [one_pow] at hp`. Rewrite using `[← hp, ← pow_mul, ← zpow_natCast, mul_zpow, ← zpow_natCast (χ.locK P k) h, ← zpow_mul, ← zpow_mul]`.

Apply the tactic sequence `congr 2 <;> push_cast <;> ring`. Establish `e2 : χ.inf a ^ (c * ((mf P * N : ℕ) : ℤ)) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1`. Rewrite using `[← mul_zpow, show c * ((mf P * N : ℕ) : ℤ) = (N : ℤ) * (c * mf P) by push_cast; ring, zpow_mul, zpow_natCast, hA, one_zpow]`. Rewrite using `[← zpow_natCast, eq_inv_of_mul_eq_one_left e1, zpow_neg, eq_inv_of_mul_eq_one_left e2, inv_inv, inv_mul_cancel]`.
-/
theorem UpperTheory.exists_pow_locK_mul_inf_eq_one_of_levelLe_two :
    ∀ (E : Type) [Field E] [NumberField E] (χ : Formalism.L2.Host.HChar E) (S : Finset (HeightOneSpectrum (𝓞 E))), (∀ v, v ∉ S → χ.UnrAt v) → (∀ v, χ.LevelLe v 2) → ∀ (P : HeightOneSpectrum (𝓞 E)) (k : Eˣ), ∃ (M : ℕ) (z : Eˣ), 0 < M ∧ P.valuation E (z : E) = P.valuation E (k : E) ^ M ∧ (∀ Q : HeightOneSpectrum (𝓞 E), Q ≠ P → Q.valuation E (z : E) = 1) ∧ χ.locK P k ^ M * χ.inf z = 1 := by
  intro E _ _ χ S hS hlev P k
  classical
  obtain ⟨h, a, hh, haP, haQ⟩ := GlobalTheory.TamePow.exists_gen P
  obtain ⟨c, hc⟩ : ∃ c : ℤ, P.valuation E (k : E) = WithZero.exp c :=
    ⟨_, (WithZero.exp_log ((Valuation.ne_zero_iff _).2 k.ne_zero)).symm⟩
  choose mf hmf hmu using fun v => exists_pow_locK_two χ (hlev v)
  have hPS : P ∈ S ∪ {P} := by simp
  obtain ⟨N, hN⟩ : ∃ N, N = ∏ v ∈ (S ∪ {P}).erase P, mf v := ⟨_, rfl⟩
  have hNpos : 0 < N := by
    rw [hN]
    exact Finset.prod_pos (fun v _ => hmf v)
  have hrule := Formalism.L2.Host.HChar.productRule χ (S ∪ {P})
    (fun v hv => hS v (fun h' => hv (Finset.mem_union_left _ h'))) a
  have hfin : ∏ᶠ (v) (_ : v ∉ S ∪ {P}), χ.val v ^ ordF v a = 1 := by
    apply finprod_eq_one_of_forall_eq_one
    intro v
    rw [finprod_eq_if]
    split_ifs with hv
    · rfl
    · have hvP : v ≠ P := fun e => hv (by simp [e])
      have h0 : ordF v a = 0 := by
        simp [Formalism.L2.Host.ordF, haQ v hvP]
      rw [h0, zpow_zero]
  rw [hfin, mul_one, ← Finset.mul_prod_erase (S ∪ {P}) (fun v => χ.locK v a) hPS, ← mul_assoc] at hrule
  have hrest : (∏ v ∈ (S ∪ {P}).erase P, χ.locK v a) ^ N = 1 := by
    rw [← Finset.prod_pow]
    apply Finset.prod_eq_one
    intro v hv
    obtain ⟨d, hd⟩ := Finset.dvd_prod_of_mem mf hv
    rw [hN, hd, pow_mul, hmu v a (haQ v (Finset.ne_of_mem_erase hv)), one_pow]
  have hA : (χ.inf a * χ.locK P a) ^ N = 1 := by
    have hp := congrArg (fun z => z ^ N) hrule
    rw [mul_pow, hrest, mul_one, one_pow] at hp
    exact hp
  have hw : P.valuation E ((k ^ h * a ^ c : Eˣ) : E) = 1 := by
    rw [Units.val_mul, Units.val_pow_eq_pow_val, Units.val_zpow_eq_zpow_val, map_mul, map_pow,
      map_zpow₀, hc, haP, ← WithZero.exp_nsmul, ← WithZero.exp_zsmul, ← WithZero.exp_add,
      WithZero.exp_eq_one]
    simp only [nsmul_eq_mul, smul_eq_mul]
    ring
  have hwm := hmu P _ hw
  rw [map_mul, map_pow, map_zpow] at hwm
  have htpos : 0 < mf P * N := Nat.mul_pos (hmf P) hNpos
  refine ⟨h * (mf P * N), a ^ (-(c * ((mf P * N : ℕ) : ℤ))), Nat.mul_pos hh htpos, ?_, ?_, ?_⟩
  · rw [Units.val_zpow_eq_zpow_val, map_zpow₀, haP, hc, ← WithZero.exp_zsmul, ← WithZero.exp_nsmul,
      WithZero.exp_inj]
    simp only [nsmul_eq_mul, smul_eq_mul]
    push_cast
    ring
  · intro Q hQ
    rw [Units.val_zpow_eq_zpow_val, map_zpow₀, haQ Q hQ, one_zpow]
  · rw [map_zpow]
    have e1 : χ.locK P k ^ (((h * (mf P * N) : ℕ)) : ℤ) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1 := by
      have hp := congrArg (fun z => z ^ N) hwm
      simp only [one_pow] at hp
      rw [← hp, ← pow_mul, ← zpow_natCast, mul_zpow, ← zpow_natCast (χ.locK P k) h, ← zpow_mul,
        ← zpow_mul]
      congr 2 <;> push_cast <;> ring
    have e2 : χ.inf a ^ (c * ((mf P * N : ℕ) : ℤ)) * χ.locK P a ^ (c * ((mf P * N : ℕ) : ℤ)) = 1 := by
      rw [← mul_zpow, show c * ((mf P * N : ℕ) : ℤ) = (N : ℤ) * (c * mf P) by push_cast; ring,
        zpow_mul, zpow_natCast, hA, one_zpow]
    rw [← zpow_natCast, eq_inv_of_mul_eq_one_left e1, zpow_neg, eq_inv_of_mul_eq_one_left e2,
      inv_inv, inv_mul_cancel]
