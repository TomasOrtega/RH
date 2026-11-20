import Formalism.LocalToGlobal.PairingIndexBounds.LatticeNormPowers.NegOneZpowEqOfParity
import Formalism.SharpRestriction.GlobalSchurBounds.GL3Theta
import Formalism.LocalToGlobal.GlobalTheory.GL3.PIopNorm
import Formalism.LocalRingCardinality.SpanPowerMembership.ExampleLayerExistsGenerators

noncomputable section
open scoped BigOperators

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable (D : D7)

/- English proof (translation)
Rewrite using `[mem_algebraicClosure_iff]`. Conclude with `(Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom`.
-/
theorem test_vector_mem_schwartz_bruhat (x : D.host.E) : D.host.φ₀ x ∈ Qbar := by
  rw [mem_algebraicClosure_iff]
  exact (Algebra.IsAlgebraic.isAlgebraic (R := ℚ) x).algHom D.host.φ₀.toRatAlgHom

def Lp {p : ℕ} [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) : D.host.E →+* ℂ_[p] :=
  lam.comp (D.host.φ₀.codRestrict (Qbar : IntermediateField ℚ ℂ) (test_vector_mem_schwartz_bruhat D))

/- English proof (translation)
Simplify using `only [lamC, dif_pos (test_vector_mem_schwartz_bruhat D x), Lp]`. Both sides reduce to the same expression.
-/
theorem lamC_phi_zero_eq (p : ℕ) [Fact p.Prime] (lam : Qbar →+* ℂ_[p]) (x : D.host.E) :
    lamC lam (D.host.φ₀ x) = Lp D lam x := by
  simp only [lamC, dif_pos (test_vector_mem_schwartz_bruhat D x), Lp]
  rfl

variable {p : ℕ} [hp : Fact p.Prime]

/- English proof (translation)
Rewrite using `[← map_intCast (algebraMap ℚ_[p] ℂ_[p]) k]`. Conclude with `PadicComplex.norm_extends' (p := p) _`.
-/
theorem normC_int (k : ℤ) : ‖(k : ℂ_[p])‖ = ‖(k : ℚ_[p])‖ := by
  rw [← map_intCast (algebraMap ℚ_[p] ℂ_[p]) k]
  exact PadicComplex.norm_extends' (p := p) _

/- English proof (translation)
Use `normC_int (p := p) (k : ℤ)` as an intermediate fact. Simplify using `using this`.
-/
theorem normC_nat (k : ℕ) : ‖(k : ℂ_[p])‖ = ‖(k : ℚ_[p])‖ := by
  have := normC_int (p := p) (k : ℤ)
  simpa using this

/- English proof (translation)
Rewrite using `[normC_int]`. Conclude with `Padic.norm_int_le_one k`.
-/
theorem normC_int_le_one (k : ℤ) : ‖(k : ℂ_[p])‖ ≤ 1 := by
  rw [normC_int]; exact Padic.norm_int_le_one k

/- English proof (translation)
Rewrite using `[normC_nat]`. Conclude with `Padic.norm_natCast_eq_one_iff.mpr hs.symm`.
-/
theorem normC_nat_coprime {s : ℕ} (hs : Nat.Coprime s p) : ‖(s : ℂ_[p])‖ = 1 := by
  rw [normC_nat]; exact Padic.norm_natCast_eq_one_iff.mpr hs.symm

/- English proof (translation)
Rewrite using `[← Padic.norm_p_pow, norm_pow, norm_pow, normC_nat]`.
-/
theorem normC_p_pow (n : ℕ) : ‖(p : ℂ_[p]) ^ n‖ = (p : ℝ) ^ (-(n : ℤ)) := by
  rw [← Padic.norm_p_pow, norm_pow, norm_pow, normC_nat]

/- English proof (translation)
Rewrite `h` using `[normC_int]`. Conclude with `(Padic.norm_int_le_pow_iff_dvd k n).mp h`.
-/
theorem dvd_of_normC {k : ℤ} {n : ℕ} (h : ‖(k : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))) :
    (p ^ n : ℤ) ∣ k := by
  rw [normC_int] at h
  exact (Padic.norm_int_le_pow_iff_dvd k n).mp h

/- English proof (translation)
The claim follows from `IsUltrametricDist.norm_add_le_max x y`.
-/
theorem norm_max (x y : ℂ_[p]) : ‖x + y‖ ≤ max ‖x‖ ‖y‖ := IsUltrametricDist.norm_add_le_max x y

section Kstr

variable (D : D7)

abbrev bet : D.host.E := D.host.sqd

/- English proof (translation)
Rewrite using `[← sq]`. Conclude with `Formalism.BasicNotions.Examples₂.bE_sq D.host`.
-/
theorem bet_sq : bet D * bet D = -(D.host.d : D.host.E) := by
  rw [← sq]; exact Formalism.BasicNotions.Examples₂.bE_sq D.host

/- English proof (translation)
Conclude with `D.host.hyp.2.1.pos` after adjusting the coercions.
-/
theorem d_pos : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos

/- English proof (translation)
Establish `hsq` using `bet_sq D`. Proceed by induction on `hx using IntermediateField.adjoin_induction with`. Consider the case `mem x hx`. Rewrite `hx` using `[Set.mem_singleton_iff]`. Substitute `hx` using the available equality.

Conclude with `⟨0, 1, by simp⟩`. Consider the case `algebraMap x => exact ⟨x, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, e, rfl⟩` from `hy`.

Conclude with `⟨a + c, b + e, by push_cast; ring⟩`. Consider the case `mul x y _ _ hx hy`. Take `⟨a, b, rfl⟩` from `hx`. Take `⟨c, e, rfl⟩` from `hy`. Use `⟨a * c - D.host.d * b * e, a * e + b * c, ?_⟩` and prove the remaining obligations.

Use `push_cast`. Take the linear combination `((b : D.host.E) * e) * hsq`. Consider the case `inv x _ hx`. Take `⟨a, b, rfl⟩` from `hx`. Establish `hd` using `d_pos D`.

Distinguish the cases in `h0 : a ^ 2 + D.host.d * b ^ 2 = 0`. Establish `ha : a = 0` using `by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]`. Establish `hb : b = 0`. Establish `: b ^ 2 = 0` using `by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]`. Conclude with `pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this`.

Substitute `ha` using the available equality. Substitute `hb` using the available equality. Conclude with `⟨0, 0, by simp⟩`. Use `⟨a / (a ^ 2 + D.host.d * b ^ 2), -b / (a ^ 2 + D.host.d * b ^ 2), ?_⟩` and prove the remaining obligations. Establish `h0' : ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) ≠ 0` using `by exact_mod_cast h0`.

Apply `inv_eq_of_mul_eq_one_right` to reduce the goal to its premises. Rewrite using `[Rat.cast_div, Rat.cast_div, Rat.cast_neg]`. Clear the denominators using the available nonvanishing facts. Move the coercions through the operations in `at h0' ⊢`. Take the linear combination `(-(b : D.host.E) ^ 2) * hsq`.
-/
theorem K_coords {x : D.host.E} (hx : x ∈ D.host.K) :
    ∃ a b : ℚ, x = (a : D.host.E) + (b : D.host.E) * bet D := by
  have hsq := bet_sq D
  induction hx using IntermediateField.adjoin_induction with
  | mem x hx =>
    rw [Set.mem_singleton_iff] at hx; subst hx
    exact ⟨0, 1, by simp⟩
  | algebraMap x => exact ⟨x, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, e, rfl⟩ := hy
    exact ⟨a + c, b + e, by push_cast; ring⟩
  | mul x y _ _ hx hy =>
    obtain ⟨a, b, rfl⟩ := hx; obtain ⟨c, e, rfl⟩ := hy
    refine ⟨a * c - D.host.d * b * e, a * e + b * c, ?_⟩
    push_cast
    linear_combination ((b : D.host.E) * e) * hsq
  | inv x _ hx =>
    obtain ⟨a, b, rfl⟩ := hx
    have hd := d_pos D
    by_cases h0 : a ^ 2 + D.host.d * b ^ 2 = 0
    · have ha : a = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]
      have hb : b = 0 := by
        have : b ^ 2 = 0 := by nlinarith [sq_nonneg a, sq_nonneg b, mul_nonneg hd.le (sq_nonneg b)]
        exact pow_eq_zero_iff (n := 2) (by norm_num) |>.mp this
      subst ha; subst hb
      exact ⟨0, 0, by simp⟩
    · refine ⟨a / (a ^ 2 + D.host.d * b ^ 2), -b / (a ^ 2 + D.host.d * b ^ 2), ?_⟩
      have h0' : ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) ≠ 0 := by exact_mod_cast h0
      apply inv_eq_of_mul_eq_one_right
      rw [Rat.cast_div, Rat.cast_div, Rat.cast_neg]
      field_simp
      push_cast at h0' ⊢
      linear_combination (-(b : D.host.E) ^ 2) * hsq

/- English proof (translation)
Apply `D.host.φ₀.injective` to reduce the goal to its premises. Rewrite using `[Formalism.BasicNotions.Examples₂.emb_conj, Formalism.BasicNotions.Examples₂.emb_conj, Complex.conj_conj]`.
-/
theorem conj_conj (x : D.host.E) : D.host.conj (D.host.conj x) = x := by
  apply D.host.φ₀.injective
  rw [Formalism.BasicNotions.Examples₂.emb_conj, Formalism.BasicNotions.Examples₂.emb_conj, Complex.conj_conj]

/- English proof (translation)
Rewrite using `[map_add, map_mul, map_ratCast, map_ratCast, bet, Formalism.BasicNotions.Examples₂.conj_bE]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem conj_coords (a b : ℚ) :
    D.host.conj ((a : D.host.E) + (b : D.host.E) * bet D) = (a : D.host.E) - (b : D.host.E) * bet D := by
  rw [map_add, map_mul, map_ratCast, map_ratCast, bet, Formalism.BasicNotions.Examples₂.conj_bE]; ring

/- English proof (translation)
The claim follows from `IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)`.
-/
theorem bet_mem : bet D ∈ D.host.K := IntermediateField.subset_adjoin _ _ (Set.mem_singleton _)

/- English proof (translation)
Take `⟨a, b, rfl⟩` from `K_coords D hx`. Rewrite using `[conj_coords]`. Conclude with `sub_mem (SubfieldClass.ratCast_mem D.host.K a) (mul_mem (SubfieldClass.ratCast_mem D.host.K b) (bet_mem D))`.
-/
theorem conj_mem {x : D.host.E} (hx : x ∈ D.host.K) : D.host.conj x ∈ D.host.K := by
  obtain ⟨a, b, rfl⟩ := K_coords D hx
  rw [conj_coords]
  exact sub_mem (SubfieldClass.ratCast_mem D.host.K a)
    (mul_mem (SubfieldClass.ratCast_mem D.host.K b) (bet_mem D))

abbrev oE (z : 𝓞 D.host.K) : D.host.E := ((z : D.host.K) : D.host.E)

/- English proof (translation)
Establish `h` using `(RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)`. Simplify using `using h`.
-/
theorem isInt_oE (z : 𝓞 D.host.K) : IsIntegral ℤ (oE D z) := by
  have h := (RingOfIntegers.isIntegral_coe z).map (IsScalarTower.toAlgHom ℤ D.host.K D.host.E)
  simpa using h

/- English proof (translation)
Establish `h` using `(isInt_oE D z).map ((D.host.conj : D.host.E →+* D.host.E).toIntAlgHom)`. Simplify using `using h`.
-/
theorem isInt_conj_oE (z : 𝓞 D.host.K) : IsIntegral ℤ (D.host.conj (oE D z)) := by
  have h := (isInt_oE D z).map ((D.host.conj : D.host.E →+* D.host.E).toIntAlgHom)
  simpa using h

/- English proof (translation)
Establish `h' : IsIntegral ℤ q`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]`. Simplify using `using h`. Take `⟨k, hk⟩` from `IsIntegrallyClosed.isIntegral_iff.mp h'`. Conclude with `⟨k, by simpa using hk.symm⟩`.
-/
theorem int_of_rat {q : ℚ} (h : IsIntegral ℤ (q : D.host.E)) : ∃ k : ℤ, q = k := by
  have h' : IsIntegral ℤ q := by
    rw [← isIntegral_algebraMap_iff (algebraMap ℚ D.host.E).injective]
    simpa using h
  obtain ⟨k, hk⟩ := IsIntegrallyClosed.isIntegral_iff.mp h'
  exact ⟨k, by simpa using hk.symm⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `K_coords D (z : D.host.K).2`. Express the relevant statement in the definitionally equal form `oE D z = _ at hab`. Establish `hs : oE D z + D.host.conj (oE D z) = ((2 * a : ℚ) : D.host.E)`. Rewrite using `[hab, conj_coords]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hi : IsIntegral ℤ ((2 * a : ℚ) : D.host.E)` using `hs ▸ (isInt_oE D z).add (isInt_conj_oE D z)`. Take `⟨k, hk⟩` from `int_of_rat D hi`. Conclude with `⟨k, by rw [hs, hk]; push_cast; rfl⟩`.
-/
theorem tr_int (z : 𝓞 D.host.K) : ∃ t : ℤ, oE D z + D.host.conj (oE D z) = t := by
  obtain ⟨a, b, hab⟩ := K_coords D (z : D.host.K).2
  change oE D z = _ at hab
  have hs : oE D z + D.host.conj (oE D z) = ((2 * a : ℚ) : D.host.E) := by
    rw [hab, conj_coords]; push_cast; ring
  have hi : IsIntegral ℤ ((2 * a : ℚ) : D.host.E) := hs ▸ (isInt_oE D z).add (isInt_conj_oE D z)
  obtain ⟨k, hk⟩ := int_of_rat D hi
  exact ⟨k, by rw [hs, hk]; push_cast; rfl⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `K_coords D (z : D.host.K).2`. Express the relevant statement in the definitionally equal form `oE D z = _ at hab`. Establish `hs : oE D z * D.host.conj (oE D z) = ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E)`. Rewrite using `[hab, conj_coords]`. Use `push_cast`.

Take the linear combination `(-(b : D.host.E) ^ 2) * bet_sq D`. Establish `hi : IsIntegral ℤ ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E)` using `hs ▸ (isInt_oE D z).mul (isInt_conj_oE D z)`. Take `⟨k, hk⟩` from `int_of_rat D hi`. Conclude with `⟨k, by rw [hs, hk]; push_cast; rfl⟩`.
-/
theorem nm_int (z : 𝓞 D.host.K) : ∃ n : ℤ, oE D z * D.host.conj (oE D z) = n := by
  obtain ⟨a, b, hab⟩ := K_coords D (z : D.host.K).2
  change oE D z = _ at hab
  have hs : oE D z * D.host.conj (oE D z) = ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) := by
    rw [hab, conj_coords]; push_cast; linear_combination (-(b : D.host.E) ^ 2) * bet_sq D
  have hi : IsIntegral ℤ ((a ^ 2 + D.host.d * b ^ 2 : ℚ) : D.host.E) :=
    hs ▸ (isInt_oE D z).mul (isInt_conj_oE D z)
  obtain ⟨k, hk⟩ := int_of_rat D hi
  exact ⟨k, by rw [hs, hk]; push_cast; rfl⟩

/- English proof (translation)
Establish `hK` using `conj_mem D (z : D.host.K).2`. Use `set w : D.host.K := ⟨D.host.conj (oE D z), hK⟩`. Establish `hw : IsIntegral ℤ w`. Rewrite using `[← isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective]`. Conclude with `isInt_conj_oE D z`.

Conclude with `⟨⟨w, hw⟩, rfl⟩`.
-/
theorem conj_O (z : 𝓞 D.host.K) : ∃ z' : 𝓞 D.host.K, oE D z' = D.host.conj (oE D z) := by
  have hK := conj_mem D (z : D.host.K).2
  set w : D.host.K := ⟨D.host.conj (oE D z), hK⟩
  have hw : IsIntegral ℤ w := by
    rw [← isIntegral_algebraMap_iff (algebraMap D.host.K D.host.E).injective]
    exact isInt_conj_oE D z
  exact ⟨⟨w, hw⟩, rfl⟩

end Kstr

section PadicK

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

/- English proof (translation)
The claim follows from `map_intCast _ k`.
-/
theorem Lp_int (k : ℤ) : Lp D lam (k : D.host.E) = (k : ℂ_[p]) := map_intCast _ k

/- English proof (translation)
Take `⟨t, ht⟩` from `tr_int D z`. Take `⟨n, hn⟩` from `nm_int D z`. Establish `hrelE : oE D z ^ 2 = (t : D.host.E) * oE D z - n` using `by rw [← ht, ← hn]; ring`. Establish `hrel : (Lp D lam (oE D z)) ^ 2 = (t : ℂ_[p]) * Lp D lam (oE D z) - n`. Use `congrArg (Lp D lam) hrelE` as an intermediate fact.

Rewrite `this` using `[map_pow, map_sub, map_mul, Lp_int, Lp_int]`. Then use the resulting hypothesis. Use `set x := Lp D lam (oE D z)`. Assume the negation of the conclusion as `hgt`. Use `push Not at hgt`. Establish `h1 : ‖x‖ ^ 2 ≤ max (‖(t : ℂ_[p])‖ * ‖x‖) ‖(n : ℂ_[p])‖`.

Rewrite using `[← norm_pow, hrel, sub_eq_add_neg]`. Combine the equalities or inequalities in the displayed calculation. Establish `ht1` using `normC_int_le_one (p := p) t`. Establish `hn1` using `normC_int_le_one (p := p) n`. Break down `le_max_iff.mp h1 with h | h` into its components or cases.

Use polynomial arithmetic with `[norm_nonneg x, norm_nonneg (t : ℂ_[p])]`. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem norm_Lp_le_one (z : 𝓞 D.host.K) : ‖Lp D lam (oE D z)‖ ≤ 1 := by
  obtain ⟨t, ht⟩ := tr_int D z
  obtain ⟨n, hn⟩ := nm_int D z
  have hrelE : oE D z ^ 2 = (t : D.host.E) * oE D z - n := by rw [← ht, ← hn]; ring
  have hrel : (Lp D lam (oE D z)) ^ 2 = (t : ℂ_[p]) * Lp D lam (oE D z) - n := by
    have := congrArg (Lp D lam) hrelE
    rwa [map_pow, map_sub, map_mul, Lp_int, Lp_int] at this
  set x := Lp D lam (oE D z)
  by_contra hgt
  push Not at hgt
  have h1 : ‖x‖ ^ 2 ≤ max (‖(t : ℂ_[p])‖ * ‖x‖) ‖(n : ℂ_[p])‖ := by
    rw [← norm_pow, hrel, sub_eq_add_neg]
    calc _ ≤ max ‖(t : ℂ_[p]) * x‖ ‖-(n : ℂ_[p])‖ := norm_max _ _
      _ = _ := by rw [norm_mul, norm_neg]
  have ht1 := normC_int_le_one (p := p) t
  have hn1 := normC_int_le_one (p := p) n
  rcases le_max_iff.mp h1 with h | h
  · nlinarith [norm_nonneg x, norm_nonneg (t : ℂ_[p])]
  · nlinarith

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `norm_max (x - 1) 1` as an intermediate fact. Rewrite `this` using `[sub_add_cancel, norm_one]`. Conclude with `this.trans (max_le h.le le_rfl)`. Use `norm_max x (1 - x)` as an intermediate fact.

Rewrite `this` using `[add_sub_cancel, norm_one, norm_sub_rev]`. Break down `le_max_iff.mp this with h' | h'` into its components or cases. Conclude with `h'`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem norm_eq_one_of_close {x : ℂ_[p]} (h : ‖x - 1‖ < 1) : ‖x‖ = 1 := by
  apply le_antisymm
  · have := norm_max (x - 1) 1
    rw [sub_add_cancel, norm_one] at this
    exact this.trans (max_le h.le le_rfl)
  · have := norm_max x (1 - x)
    rw [add_sub_cancel, norm_one, norm_sub_rev] at this
    rcases le_max_iff.mp this with h' | h'
    · exact h'
    · linarith

/- English proof (translation)
Apply `zpow_le_zpow_right₀` to reduce the goal to its premises. Conclude with `hp.out.one_lt.le` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem pzpow_le {k m : ℕ} (hkm : k ≤ m) : (p : ℝ) ^ (-(m : ℤ)) ≤ (p : ℝ) ^ (-(k : ℤ)) := by
  apply zpow_le_zpow_right₀
  · exact_mod_cast hp.out.one_lt.le
  · omega

/- English proof (translation)
Apply `zpow_lt_one_of_neg₀` to reduce the goal to its premises. Conclude with `hp.out.one_lt` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem pzpow_lt_one {m : ℕ} (hm : 1 ≤ m) : (p : ℝ) ^ (-(m : ℤ)) < 1 := by
  apply zpow_lt_one_of_neg₀
  · exact_mod_cast hp.out.one_lt
  · omega

/- English proof (translation)
Take `⟨t, ht⟩` from `tr_int D z`. Take `⟨n, hn⟩` from `nm_int D z`. Establish `hpm` using `pzpow_le (p := p) hkm`. Establish `hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(m : ℤ))` using `by positivity`. Establish `htd : ((p ^ k : ℕ) : ℤ) ∣ t`.

Establish `: ‖(t : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ))`. Rewrite using `[← Lp_int D lam, ← ht, map_add]`. Conclude with `(norm_max _ _).trans (max_le (h1.trans hpm) (h2.trans hpm))`. Use `dvd_of_normC this` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hnd : ((p ^ (2 * k) : ℕ) : ℤ) ∣ n`. Establish `: ‖(n : ℂ_[p])‖ ≤ (p : ℝ) ^ (-((2 * k : ℕ) : ℤ))`. Rewrite using `[← Lp_int D lam, ← hn, map_mul, norm_mul]`. Establish `e : (p : ℝ) ^ (-((2 * k : ℕ) : ℤ)) = (p : ℝ) ^ (-(k : ℤ)) * (p : ℝ) ^ (-(k : ℤ))`. Rewrite using `[← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; congr 1; push_cast; ring`.

Rewrite using `[e]`. Conclude with `mul_le_mul (h1.trans hpm) (h2.trans hpm) (norm_nonneg _) (by positivity)`. Use `dvd_of_normC this` as an intermediate fact. Conclude with `this` after adjusting the coercions. Take `⟨t', rfl⟩` from `htd`.

Take `⟨n', rfl⟩` from `hnd`. Establish `hp0 : (p : D.host.K) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Use `set w : D.host.K := (z : D.host.K) / (p : D.host.K) ^ k with hw`. Establish `hrelE : oE D z ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * oE D z + (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0`. Rewrite using `[← ht, ← hn]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hrelK : w ^ 2 - (t' : D.host.K) * w + (n' : D.host.K) = 0`. Establish `hzw : (z : D.host.K) = (p : D.host.K) ^ k * w` using `by rw [hw]; field_simp`. Establish `hrelK0 : (z : D.host.K) ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * (z : D.host.K) + (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0`. Apply `(algebraMap D.host.K D.host.E).injective` to reduce the goal to its premises.

Simplify using `using hrelE`. Rewrite `hrelK0` using `[hzw]`. Establish `hpk : ((p : D.host.K) ^ k) ^ 2 ≠ 0` using `pow_ne_zero _ (pow_ne_zero _ hp0)`. Apply `(mul_right_inj' hpk).mp` to reduce the goal to its premises. Rewrite using `[mul_zero, ← hrelK0]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hwi : IsIntegral ℤ w`. Use `⟨Polynomial.X ^ 2 + (Polynomial.C (-t') * Polynomial.X + Polynomial.C n'), ?_, ?_⟩` and prove the remaining obligations. Conclude with `Polynomial.monic_X_pow_add (Polynomial.degree_linear_lt)`.

Simplify using `only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul, Polynomial.eval₂_C]`. Rewrite using `[← hrelK]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Use `⟨⟨w, hwi⟩, ?_⟩` and prove the remaining obligations.

Use `show oE D z = (p : D.host.E) ^ k * ((w : D.host.K) : D.host.E)`. Rewrite using `[hw]`. Establish `hp0E : (p : D.host.E) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem lemT (z : 𝓞 D.host.K) {k m : ℕ} (hkm : k ≤ m)
    (h1 : ‖Lp D lam (oE D z)‖ ≤ (p : ℝ) ^ (-(m : ℤ)))
    (h2 : ‖Lp D lam (D.host.conj (oE D z))‖ ≤ (p : ℝ) ^ (-(m : ℤ))) :
    ∃ u : 𝓞 D.host.K, oE D z = (p : D.host.E) ^ k * oE D u := by
  obtain ⟨t, ht⟩ := tr_int D z
  obtain ⟨n, hn⟩ := nm_int D z
  have hpm := pzpow_le (p := p) hkm
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-(m : ℤ)) := by positivity
  have htd : ((p ^ k : ℕ) : ℤ) ∣ t := by
    have : ‖(t : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(k : ℤ)) := by
      rw [← Lp_int D lam, ← ht, map_add]
      exact (norm_max _ _).trans (max_le (h1.trans hpm) (h2.trans hpm))
    have := dvd_of_normC this
    exact_mod_cast this
  have hnd : ((p ^ (2 * k) : ℕ) : ℤ) ∣ n := by
    have : ‖(n : ℂ_[p])‖ ≤ (p : ℝ) ^ (-((2 * k : ℕ) : ℤ)) := by
      rw [← Lp_int D lam, ← hn, map_mul, norm_mul]
      have e : (p : ℝ) ^ (-((2 * k : ℕ) : ℤ)) = (p : ℝ) ^ (-(k : ℤ)) * (p : ℝ) ^ (-(k : ℤ)) := by
        rw [← zpow_add₀ (by exact_mod_cast hp.out.ne_zero)]; congr 1; push_cast; ring
      rw [e]
      exact mul_le_mul (h1.trans hpm) (h2.trans hpm) (norm_nonneg _) (by positivity)
    have := dvd_of_normC this
    exact_mod_cast this
  obtain ⟨t', rfl⟩ := htd
  obtain ⟨n', rfl⟩ := hnd
  have hp0 : (p : D.host.K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set w : D.host.K := (z : D.host.K) / (p : D.host.K) ^ k with hw
  have hrelE : oE D z ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * oE D z + (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0 := by
    rw [← ht, ← hn]; ring
  have hrelK : w ^ 2 - (t' : D.host.K) * w + (n' : D.host.K) = 0 := by
    have hzw : (z : D.host.K) = (p : D.host.K) ^ k * w := by rw [hw]; field_simp
    have hrelK0 : (z : D.host.K) ^ 2 - (((p ^ k : ℕ) : ℤ) * t' : ℤ) * (z : D.host.K) +
        (((p ^ (2 * k) : ℕ) : ℤ) * n' : ℤ) = 0 := by
      apply (algebraMap D.host.K D.host.E).injective
      simpa using hrelE
    rw [hzw] at hrelK0
    have hpk : ((p : D.host.K) ^ k) ^ 2 ≠ 0 := pow_ne_zero _ (pow_ne_zero _ hp0)
    apply (mul_right_inj' hpk).mp
    rw [mul_zero, ← hrelK0]
    push_cast; ring
  have hwi : IsIntegral ℤ w := by
    refine ⟨Polynomial.X ^ 2 + (Polynomial.C (-t') * Polynomial.X + Polynomial.C n'), ?_, ?_⟩
    · exact Polynomial.monic_X_pow_add (Polynomial.degree_linear_lt)
    · simp only [Polynomial.eval₂_add, Polynomial.eval₂_pow, Polynomial.eval₂_X, Polynomial.eval₂_mul,
        Polynomial.eval₂_C]
      rw [← hrelK]; simp; ring
  refine ⟨⟨w, hwi⟩, ?_⟩
  show oE D z = (p : D.host.E) ^ k * ((w : D.host.K) : D.host.E)
  rw [hw]
  have hp0E : (p : D.host.E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  push_cast
  field_simp

end PadicK

section Alg

variable (D : D7) {p : ℕ} [hp : Fact p.Prime] (lam : Qbar →+* ℂ_[p])

/- English proof (translation)
Simplify using `[oE]`.
-/
theorem oE_mul (a b : 𝓞 D.host.K) : oE D (a * b) = oE D a * oE D b := by simp [oE]
/- English proof (translation)
Simplify using `[oE]`.
-/
theorem oE_sub (a b : 𝓞 D.host.K) : oE D (a - b) = oE D a - oE D b := by simp [oE]
/- English proof (translation)
Simplify using `[oE]`.
-/
theorem oE_one : oE D 1 = 1 := by simp [oE]

/- English proof (translation)
Use `norm_max 1 (-x)` as an intermediate fact. Rewrite `this` using `[← sub_eq_add_neg, norm_one, norm_neg]`. Conclude with `this.trans (max_le le_rfl hx)`.
-/
theorem norm_one_sub_le {x : ℂ_[p]} (hx : ‖x‖ ≤ 1) : ‖1 - x‖ ≤ 1 := by
  have := norm_max 1 (-x)
  rw [← sub_eq_add_neg, norm_one, norm_neg] at this
  exact this.trans (max_le le_rfl hx)

/- English proof (translation)
Take `⟨h1, h2⟩` from `hId`. Rewrite `h1`, `h2` using `[lamC_phi_zero_eq]`. Express the relevant statement in the definitionally equal form `‖Lp D lam (oE D ε) - 1‖ ≤ _ at h1`. Express the relevant statement in the definitionally equal form `‖Lp D lam (D.host.conj (oE D ε))‖ ≤ _ at h2`. Establish `hε1` using `norm_Lp_le_one D lam ε`.

Take `⟨ε', hε'⟩` from `conj_O D ε`. Establish `hε'1 : ‖Lp D lam (D.host.conj (oE D ε))‖ ≤ 1` using `hε' ▸ norm_Lp_le_one D lam ε'`. Establish `hkm : n ≤ 2 * n + 2` using `by omega`. Establish `hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ))` using `by positivity`. Take `⟨u1, hu1⟩` from `lemT D lam (ε * (1 - ε)) hkm (by`.

Rewrite using `[oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, norm_mul, norm_sub_rev]`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`. Rewrite using `[oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, map_mul, map_sub, map_one, norm_mul]`. Combine the equalities or inequalities in the displayed calculation.

Take `⟨u2, hu2⟩` from `lemT D lam (ε * ε') hkm (by`. Rewrite using `[oE_mul, hε', map_mul, norm_mul]`. Combine the equalities or inequalities in the displayed calculation. Use the proof step `(by`. Rewrite using `[oE_mul, hε', map_mul, conj_conj, map_mul, norm_mul]`.

Combine the equalities or inequalities in the displayed calculation. Take `⟨μ', hμ'⟩` from `conj_O D μ`. Take `⟨c0, hc0⟩` from `tr_int D (ε * μ')`. Rewrite `hc0` using `[oE_mul, hμ', map_mul, conj_conj]`. Rewrite `hu1` using `[oE_mul, oE_sub, oE_one]`.

Rewrite `hu2` using `[oE_mul, hε']`. Use `⟨c0, u1 * μ' - u2 * μ, ?_⟩` and prove the remaining obligations. Rewrite using `[oE_sub, oE_mul, oE_mul, hμ']`. Take the linear combination `(oE D ε) * hc0 + (D.host.conj (oE D μ)) * hu1 - (oE D μ) * hu2`.
-/
theorem alg_step (ε : 𝓞 D.host.K) (n : ℕ) (hId : IsIdem D lam (2 * n + 2) ε) (μ : 𝓞 D.host.K) :
    ∃ (c0 : ℤ) (w : 𝓞 D.host.K),
      oE D ε * D.host.conj (oE D μ) = (c0 : D.host.E) * oE D ε + (p : D.host.E) ^ n * oE D w := by
  obtain ⟨h1, h2⟩ := hId
  rw [lamC_phi_zero_eq] at h1 h2
  change ‖Lp D lam (oE D ε) - 1‖ ≤ _ at h1
  change ‖Lp D lam (D.host.conj (oE D ε))‖ ≤ _ at h2
  have hε1 := norm_Lp_le_one D lam ε
  obtain ⟨ε', hε'⟩ := conj_O D ε
  have hε'1 : ‖Lp D lam (D.host.conj (oE D ε))‖ ≤ 1 := hε' ▸ norm_Lp_le_one D lam ε'
  have hkm : n ≤ 2 * n + 2 := by omega
  have hpos : (0 : ℝ) ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := by positivity

  obtain ⟨u1, hu1⟩ := lemT D lam (ε * (1 - ε)) hkm (by
      rw [oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, norm_mul, norm_sub_rev]
      calc _ ≤ 1 * (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := mul_le_mul hε1 h1 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
    (by
      rw [oE_mul, oE_sub, oE_one, map_mul, map_sub, map_one, map_mul, map_sub, map_one, norm_mul]
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 :=
            mul_le_mul h2 (norm_one_sub_le hε'1) (norm_nonneg _) hpos
        _ = _ := mul_one _)

  obtain ⟨u2, hu2⟩ := lemT D lam (ε * ε') hkm (by
      rw [oE_mul, hε', map_mul, norm_mul]
      calc _ ≤ 1 * (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) := mul_le_mul hε1 h2 (norm_nonneg _) zero_le_one
        _ = _ := one_mul _)
    (by
      rw [oE_mul, hε', map_mul, conj_conj, map_mul, norm_mul]
      calc _ ≤ (p : ℝ) ^ (-((2 * n + 2 : ℕ) : ℤ)) * 1 := mul_le_mul h2 hε1 (norm_nonneg _) hpos
        _ = _ := mul_one _)
  obtain ⟨μ', hμ'⟩ := conj_O D μ
  obtain ⟨c0, hc0⟩ := tr_int D (ε * μ')
  rw [oE_mul, hμ', map_mul, conj_conj] at hc0
  rw [oE_mul, oE_sub, oE_one] at hu1
  rw [oE_mul, hε'] at hu2
  refine ⟨c0, u1 * μ' - u2 * μ, ?_⟩
  rw [oE_sub, oE_mul, oE_mul, hμ']
  linear_combination (oE D ε) * hc0 + (D.host.conj (oE D μ)) * hu1 - (oE D μ) * hu2

end Alg

section Lat

variable {D : D7} {N N' : ℕ}

/- English proof (translation)
Simplify using `only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]`.
-/
theorem Hf_smul_left (T : Tor D) (c : ℂ) (x y : VC D N N') :
    Hf D T (c • x) y = c * Hf D T x y := by
  simp only [Hf, Pi.smul_apply, smul_eq_mul, mul_assoc, ← Finset.mul_sum, mul_div_assoc]

/- English proof (translation)
Rewrite using `[Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (c • y) x, Hf_smul_left, map_mul, ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]`.
-/
theorem Hf_smul_right (T : Tor D) (c : ℂ) (x y : VC D N N') :
    Hf D T x (c • y) = starRingEnd ℂ c * Hf D T x y := by
  rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm T (c • y) x, Hf_smul_left, map_mul,
    ← Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_herm]

/- English proof (translation)
Use `Hf_smul_right T 0 x 0` as an intermediate fact. Rewrite `this` using `[zero_smul, map_zero, zero_mul]`. Conclude with `this`.
-/
theorem Hf_zero_right (T : Tor D) (x : VC D N N') : Hf D T x 0 = 0 := by
  have := Hf_smul_right T 0 x 0
  rw [zero_smul, map_zero, zero_mul] at this
  exact this

/- English proof (translation)
Use `Hf_smul_left T 0 0 y` as an intermediate fact. Rewrite `this` using `[zero_smul, zero_mul]`. Conclude with `this`.
-/
theorem Hf_zero_left (T : Tor D) (y : VC D N N') : Hf D T 0 y = 0 := by
  have := Hf_smul_left T 0 0 y
  rw [zero_smul, zero_mul] at this
  exact this

def HfR (T : Tor D) (x : VC D N N') : VC D N N' →+ ℂ where
  toFun y := Hf D T x y
  map_zero' := Hf_zero_right T x
  map_add' y y' := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right T x y y'

/- English proof (translation)
The claim follows from `map_sum (HfR T x) f s`.
-/
theorem Hf_sum_right (T : Tor D) {ι : Type*} (s : Finset ι) (x : VC D N N') (f : ι → VC D N N') :
    Hf D T x (∑ i ∈ s, f i) = ∑ i ∈ s, Hf D T x (f i) :=
  map_sum (HfR T x) f s

def imIntSub (T : Tor D) (x : VC D N N') : AddSubgroup (VC D N N') where
  carrier := {v | ∃ k : ℤ, (Hf D T x v).im = k}
  add_mem' := by
    rintro a b ⟨k, hk⟩ ⟨l, hl⟩
    exact ⟨k + l, by
      show (Hf D T x (a + b)).im = _
      rw [Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right, Complex.add_im, hk, hl]; push_cast; ring⟩
  zero_mem' := ⟨0, by simp [Hf_zero_right]⟩
  neg_mem' := by
    rintro a ⟨k, hk⟩
    refine ⟨-k, ?_⟩
    have h0 := Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.Hf_add_right T x a (-a)
    rw [add_neg_cancel, Hf_zero_right] at h0
    have h1 := congrArg Complex.im h0
    rw [Complex.add_im, Complex.zero_im] at h1
    push_cast
    linarith

/- English proof (translation)
Take `⟨a, b, -, h⟩` from `hI x hx y hy`. Conclude with `⟨b, by rw [h]; simp⟩`.
-/
theorem im_int (T : Tor D) {La' : AddSubgroup (VC D N N')} (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt T La')
    {x y : VC D N N'} (hx : x ∈ La') (hy : y ∈ La') : ∃ k : ℤ, (Hf D T x y).im = k := by
  obtain ⟨a, b, -, h⟩ := hI x hx y hy
  exact ⟨b, by rw [h]; simp⟩

end Lat

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Tor0

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0]`.
-/
theorem embV_add (A B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (A + B) = embV D (tor0 D cc δ) A + embV D (tor0 D cc δ) B := by
  funext τ i j
  simp [embV, tor0]

variable (D cc δ) in

def embVh : Matrix (Fin N') (Fin N) D.host.E →+ VC D N N' where
  toFun := embV D (tor0 D cc δ)
  map_zero' := by funext τ i j; simp [embV, tor0]
  map_add' := embV_add

/- English proof (translation)
The claim follows from `map_sum (embVh D cc δ) f s`.
-/
theorem embV_sum {ι : Type*} (s : Finset ι) (f : ι → Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (∑ i ∈ s, f i) = ∑ i ∈ s, embV D (tor0 D cc δ) (f i) :=
  map_sum (embVh D cc δ) f s

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Simplify using `[embV, tor0, Matrix.smul_apply, map_mul]`.
-/
theorem embV_smulE (x : D.host.E) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (x • B) = fun τ i j => embT D τ x * embV D (tor0 D cc δ) B τ i j := by
  funext τ i j
  simp [embV, tor0, Matrix.smul_apply, map_mul]

/- English proof (translation)
Rewrite using `[embV_smulE]`. Use function extensionality and compare the values at `τ i j`. Simplify using the standard rewrite rules.
-/
theorem embV_natsmul (m : ℕ) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) ((m : D.host.E) • B) = (m : ℂ) • embV D (tor0 D cc δ) B := by
  rw [embV_smulE]
  funext τ i j
  simp

/- English proof (translation)
Rewrite using `[embV_smulE]`. Use function extensionality and compare the values at `τ i j`. Simplify using `only [Pi.smul_apply, smul_eq_mul]`. Rewrite using `[hPsi τ k]`.
-/
theorem embV_smulK (hPsi : InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) ((k : D.host.E) • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  rw [embV_smulE]
  funext τ i j
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [hPsi τ k]

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨c, hc, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨κ * c, cc.mul_mem_left κ hc, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `D.host.φ₀ (oE D κ) * (δ * D.host.φ₀ (oE D c)) = δ * D.host.φ₀ (oE D (κ * c))`.

Rewrite using `[oE_mul, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => rw [mul_zero]`. Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [mul_add]`.

Conclude with `add_mem h1 h2`. Consider the case `neg x _ h1 => rw [mul_neg]`. Conclude with `neg_mem h1`.
-/
theorem mem_lam_mul (κ : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (oE D κ) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨c, hc, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨κ * c, cc.mul_mem_left κ hc, ?_⟩
    change D.host.φ₀ (oE D κ) * (δ * D.host.φ₀ (oE D c)) = δ * D.host.φ₀ (oE D (κ * c))
    rw [oE_mul, map_mul]
    ring
  | zero => rw [mul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [mul_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [mul_neg]; exact neg_mem h1

/- English proof (translation)
Proceed by induction on `hv using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨w, hw, A, hA, rfl⟩` from `hx`. Conclude with `AddSubgroup.subset_closure ⟨_, mem_lam_mul κ hw, A, hA, by rw [smul_smul]⟩`. Consider the case `zero => rw [smul_zero]`.

Conclude with `zero_mem _`. Consider the case `add x y _ _ h1 h2 => rw [smul_add]`. Conclude with `add_mem h1 h2`. Consider the case `neg x _ h1 => rw [smul_neg]`. Conclude with `neg_mem h1`.
-/
theorem mem_La_smul {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} (κ : 𝓞 D.host.K) {v : VC D N N'}
    (hv : v ∈ La D (tor0 D cc δ) L L') : D.host.φ₀ (oE D κ) • v ∈ La D (tor0 D cc δ) L L' := by
  induction hv using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨w, hw, A, hA, rfl⟩ := hx
    exact AddSubgroup.subset_closure ⟨_, mem_lam_mul κ hw, A, hA, by rw [smul_smul]⟩
  | zero => rw [smul_zero]; exact zero_mem _
  | add x y _ _ h1 h2 => rw [smul_add]; exact add_mem h1 h2
  | neg x _ h1 => rw [smul_neg]; exact neg_mem h1

variable (D cc δ) in

def ee {r : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (i : Fin r) : VC D N N' :=
  δ • embV D (tor0 D cc δ) (b i)

variable (D cc δ) in

def Xv {r m : ℕ} (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin m) : VC D N N' :=
  ∑ j, ((y j : ℕ) : ℂ) • ee D cc δ b j

/- English proof (translation)
Unfold `vecN Xv ee`. Rewrite using `[embV_sum, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[embV_natsmul, smul_comm]`.
-/
theorem va_eq {r : ℕ} (p n : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (a : Fin r → Fin (p ^ n)) :
    vecN D (tor0 D cc δ) δ p n b a = Xv D cc δ b a := by
  unfold vecN Xv ee
  rw [embV_sum, Finset.smul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [embV_natsmul, smul_comm]

/- English proof (translation)
Unfold `liftY`. Establish `hk : ((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n = (((ε : D.host.K) / (p : D.host.K) ^ n : D.host.K) : D.host.E)` using `by push_cast; rfl`. Rewrite using `[hk, embV_smulK hPsi, embV_sum]`. Establish `hφ : D.host.φ₀ (((ε : D.host.K) / (p : D.host.K) ^ n : D.host.K) : D.host.E) = D.host.φ₀ (oE D ε) / (p : ℂ) ^ n`. Simplify using `[oE, map_div₀]`.

Rewrite using `[hφ]`. Unfold `Xv ee`. Simplify using `only [embV_natsmul, Finset.smul_sum, smul_smul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem ly_eq (hPsi : InducedCMType D) {r : ℕ} (p n : ℕ) (ε : 𝓞 D.host.K)
    (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (y : Fin r → Fin (p ^ n)) :
    liftY D (tor0 D cc δ) δ p n ε b y =
      (D.host.φ₀ (oE D ε) / (p : ℂ) ^ n) • Xv D cc δ b y := by
  unfold liftY
  have hk : ((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n =
      (((ε : D.host.K) / (p : D.host.K) ^ n : D.host.K) : D.host.E) := by push_cast; rfl
  rw [hk, embV_smulK hPsi, embV_sum]
  have hφ : D.host.φ₀ (((ε : D.host.K) / (p : D.host.K) ^ n : D.host.K) : D.host.E) =
      D.host.φ₀ (oE D ε) / (p : ℂ) ^ n := by
    simp [oE, map_div₀]
  rw [hφ]
  unfold Xv ee
  simp only [embV_natsmul, Finset.smul_sum, smul_smul]
  refine Finset.sum_congr rfl fun j _ => ?_
  congr 1
  ring

/- English proof (translation)
Use `sum_mem fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Nat.cast_smul_eq_nsmul ℂ ((y j : ℕ)) (ee D cc δ b j)]`. Conclude with `nsmul_mem (hb j) _`.
-/
theorem Xv_mem {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r m : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (hb : ∀ i, ee D cc δ b i ∈ La D (tor0 D cc δ) L L')
    (y : Fin r → Fin m) : Xv D cc δ b y ∈ La D (tor0 D cc δ) L L' := by
  refine sum_mem fun j _ => ?_
  rw [Nat.cast_smul_eq_nsmul ℂ ((y j : ℕ)) (ee D cc δ b j)]
  exact nsmul_mem (hb j) _

end Tor0

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section Sums

/- English proof (translation)
Use `set ζ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) with hζ`. Establish `hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ))) = ζ ^ j`. Introduce `j`. Rewrite using `[hζ, ← Complex.exp_nat_mul]`. Put the polynomial expressions in normal form.

Repeatedly rewrite using `[hterm]`. Rewrite using `[Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) (p ^ n)]`. Establish `hζ1 : ζ ≠ 1`. Introduce `h`. Rewrite `h` using `[hζ, Complex.exp_eq_one_iff]`.

Take `⟨m, hm⟩` from `h`. Apply `hnot m` to reduce the goal to its premises. Establish `h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0`. Simplify using `[Real.pi_ne_zero, Complex.I_ne_zero]`. Establish `: (t : ℂ) = (m : ℂ)`.

Apply `mul_left_cancel₀ h2` to reduce the goal to its premises. Rewrite using `[hm]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions. Rewrite using `[geom_sum_eq hζ1]`.

Establish `hpow : ζ ^ (p ^ n) = 1`. Rewrite using `[hζ, ← Complex.exp_nat_mul]`. Establish `: ((p ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (t : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I)`. Establish `hk' : ((p : ℂ) ^ n * (t : ℂ)) = (k : ℂ)` using `by exact_mod_cast hk`. Rewrite using `[← hk']`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Complex.exp_int_mul_two_pi_mul_I]`. Rewrite using `[hpow, sub_self, zero_div]`.
-/
theorem geom_zero (p n : ℕ) (t : ℝ) (k : ℤ) (hk : (p : ℝ) ^ n * t = k) (hnot : ∀ m : ℤ, t ≠ m) :
    ∑ j : Fin (p ^ n), Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) * (t : ℂ))) = 0 := by
  set ζ := Complex.exp (2 * Real.pi * Complex.I * (t : ℂ)) with hζ
  have hterm : ∀ j : ℕ, Complex.exp (2 * Real.pi * Complex.I * ((j : ℂ) * (t : ℂ))) = ζ ^ j := by
    intro j
    rw [hζ, ← Complex.exp_nat_mul]
    ring_nf
  simp_rw [hterm]
  rw [Fin.sum_univ_eq_sum_range (fun j => ζ ^ j) (p ^ n)]
  have hζ1 : ζ ≠ 1 := by
    intro h
    rw [hζ, Complex.exp_eq_one_iff] at h
    obtain ⟨m, hm⟩ := h
    apply hnot m
    have h2 : (2 * (Real.pi : ℂ) * Complex.I) ≠ 0 := by
      simp [Real.pi_ne_zero, Complex.I_ne_zero]
    have : (t : ℂ) = (m : ℂ) := by
      apply mul_left_cancel₀ h2
      rw [hm]; ring
    exact_mod_cast this
  rw [geom_sum_eq hζ1]
  have hpow : ζ ^ (p ^ n) = 1 := by
    rw [hζ, ← Complex.exp_nat_mul]
    have : ((p ^ n : ℕ) : ℂ) * (2 * Real.pi * Complex.I * (t : ℂ)) = (k : ℂ) * (2 * Real.pi * Complex.I) := by
      have hk' : ((p : ℂ) ^ n * (t : ℂ)) = (k : ℂ) := by exact_mod_cast hk
      rw [← hk']; push_cast; ring
    rw [this, Complex.exp_int_mul_two_pi_mul_I]
  rw [hpow, sub_self, zero_div]

end Sums

section Main

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Establish `: (p : ℂ) ^ n = (((p : ℝ) ^ n : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.im_ofReal_mul]`.
-/
theorem im_natCast_pow_mul (p n : ℕ) (w : ℂ) : ((p : ℂ) ^ n * w).im = (p : ℝ) ^ n * w.im := by
  have : (p : ℂ) ^ n = (((p : ℝ) ^ n : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul]

/- English proof (translation)
Establish `: (s : ℂ) = ((s : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[this, Complex.im_ofReal_mul]`.
-/
theorem im_natCast_mul (s : ℕ) (w : ℂ) : ((s : ℂ) * w).im = (s : ℝ) * w.im := by
  have : (s : ℂ) = ((s : ℝ) : ℂ) := by push_cast; rfl
  rw [this, Complex.im_ofReal_mul]

/- English proof (translation)
Establish `hp0 : (p : ℂ) ^ n ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)`. Establish `hmem : ((p : ℂ) ^ n) • liftY D (tor0 D cc δ) δ p n ε b y ∈ La D (tor0 D cc δ) L L'`. Rewrite using `[ly_eq hPsi, smul_smul, mul_div_cancel₀ _ hp0]`. Conclude with `mem_La_smul ε (Xv_mem hb y)`. Take `⟨k, hk⟩` from `im_int _ hI hmem hv`.

Use `⟨k, ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, Hf_smul_left, im_natCast_pow_mul]`.
-/
theorem pn_int (hPsi : InducedCMType D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L'))
    (hb : ∀ i, ee D cc δ b i ∈ La D (tor0 D cc δ) L L') (p n : ℕ) [Fact p.Prime] (ε : 𝓞 D.host.K)
    (y : Fin r → Fin (p ^ n)) {v : VC D N N'} (hv : v ∈ La D (tor0 D cc δ) L L') :
    ∃ k : ℤ, (p : ℝ) ^ n * (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) v).im = k := by
  have hp0 : (p : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  have hmem : ((p : ℂ) ^ n) • liftY D (tor0 D cc δ) δ p n ε b y ∈ La D (tor0 D cc δ) L L' := by
    rw [ly_eq hPsi, smul_smul, mul_div_cancel₀ _ hp0]
    exact mem_La_smul ε (Xv_mem hb y)
  obtain ⟨k, hk⟩ := im_int _ hI hmem hv
  refine ⟨k, ?_⟩
  rw [← hk, Hf_smul_left, im_natCast_pow_mul]

/- English proof (translation)
Take `⟨c0, w, hw⟩` from `alg_step D lam ε n hId μ`. Take `⟨k, hk⟩` from `hgood i`. Establish `hp0 : (p : ℂ) ^ n ≠ 0` using `pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)`. Use `set q : ℂ := D.host.φ₀ (oE D ε) / (p : ℂ) ^ n with hq`. Establish `hφ` using `congrArg D.host.φ₀ hw`.

Rewrite `hφ` using `[map_mul, map_add, map_mul, map_mul, map_intCast, map_pow, map_natCast]`. Establish `hkey : D.host.φ₀ (D.host.conj (oE D μ)) * q = (c0 : ℂ) * q + D.host.φ₀ (oE D w)`. Rewrite using `[hq]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `hφ`.

Take `⟨k2, hk2⟩` from `im_int _ hI (mem_La_smul w (Xv_mem hb y)) (hb i)`. Use `⟨c0 * k + k2, ?_⟩` and prove the remaining obligations. Use `show (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) (D.host.φ₀ (oE D μ) • ee D cc δ b i)).im = _`. Establish `hly` using `ly_eq (cc := cc) (δ := δ) hPsi p n ε b y`. Rewrite `hly` using `[← hq]`.

Rewrite `hk`, the goal using `[hly]`. Rewrite `hk`, `hk2` using `[Hf_smul_left]`. Rewrite using `[Hf_smul_right, Hf_smul_left, ← Formalism.BasicNotions.Examples₂.emb_conj, ← mul_assoc, hkey, add_mul, Complex.add_im, hk2, mul_assoc]`. Establish `hc : (c0 : ℂ) = ((c0 : ℝ) : ℂ)` using `by push_cast; rfl`. Rewrite using `[hc, Complex.im_ofReal_mul, hk]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem claimC (hPsi : InducedCMType D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E}
    (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L'))
    (hb : ∀ i, ee D cc δ b i ∈ La D (tor0 D cc δ) L L') (p n : ℕ) [Fact p.Prime]
    (lam : Qbar →+* ℂ_[p]) (ε : 𝓞 D.host.K) (hId : IsIdem D lam (2 * n + 2) ε)
    (y : Fin r → Fin (p ^ n))
    (hgood : ∀ i, ∃ k : ℤ, (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) (ee D cc δ b i)).im = k)
    (μ : 𝓞 D.host.K) (i : Fin r) :
    D.host.φ₀ (oE D μ) • ee D cc δ b i ∈
      imIntSub (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) := by
  obtain ⟨c0, w, hw⟩ := alg_step D lam ε n hId μ
  obtain ⟨k, hk⟩ := hgood i
  have hp0 : (p : ℂ) ^ n ≠ 0 := pow_ne_zero _ (by exact_mod_cast (Fact.out : p.Prime).ne_zero)
  set q : ℂ := D.host.φ₀ (oE D ε) / (p : ℂ) ^ n with hq
  have hφ := congrArg D.host.φ₀ hw
  rw [map_mul, map_add, map_mul, map_mul, map_intCast, map_pow, map_natCast] at hφ
  have hkey : D.host.φ₀ (D.host.conj (oE D μ)) * q = (c0 : ℂ) * q + D.host.φ₀ (oE D w) := by
    rw [hq]
    field_simp
    linear_combination hφ
  obtain ⟨k2, hk2⟩ := im_int _ hI (mem_La_smul w (Xv_mem hb y)) (hb i)
  refine ⟨c0 * k + k2, ?_⟩
  show (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) (D.host.φ₀ (oE D μ) • ee D cc δ b i)).im = _
  have hly := ly_eq (cc := cc) (δ := δ) hPsi p n ε b y
  rw [← hq] at hly
  rw [hly] at hk ⊢
  rw [Hf_smul_left] at hk hk2
  rw [Hf_smul_right, Hf_smul_left, ← Formalism.BasicNotions.Examples₂.emb_conj, ← mul_assoc, hkey, add_mul, Complex.add_im,
    hk2, mul_assoc]
  have hc : (c0 : ℂ) = ((c0 : ℝ) : ℂ) := by push_cast; rfl
  rw [hc, Complex.im_ofReal_mul, hk]
  push_cast; ring

end Main

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

section StepA

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

variable (D cc δ) in

def smulHom (A : Matrix (Fin N') (Fin N) D.host.E) : ℂ →+ VC D N N' where
  toFun w := w • embV D (tor0 D cc δ) A
  map_zero' := zero_smul _ _
  map_add' a b := add_smul a b _

/- English proof (translation)
Use `set S := imIntSub (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) with hS`. It suffices to establish `hle : La D (tor0 D cc δ) L L' ≤ S from fun v hv => hle hv`. Unfold `La`. Apply `(AddSubgroup.closure_le _).mpr` to reduce the goal to its premises. Introduce and unpack `z ⟨w, hw, A, hA, rfl⟩`.

Establish `hle2 : lamOf D cc δ ≤ S.comap (smulHom D cc δ A)`. Unfold `lamOf`. Apply `(AddSubgroup.closure_le _).mpr` to reduce the goal to its premises. Introduce and unpack `w' ⟨c, hc, rfl⟩`. Use `show (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ S`.

Establish `hvLa : (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ La D (tor0 D cc δ) L L'` using `AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (oE D c), AddSubgroup.subset_closure ⟨c, hc, rfl⟩, A, hA, rfl⟩`. Take `⟨k1, hk1⟩` from `pn_int hPsi hI hb p n ε y hvLa`. Take `⟨s, hs, κ, hκ⟩` from `hLoc.2.2 A hA`. Establish `hsv : (s : ℂ) • ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A) = ∑ i, D.host.φ₀ (oE D (c * κ i)) • ee D cc δ b i`. Rewrite using `[smul_comm, ← embV_natsmul, hκ, embV_sum, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[embV_smulK hPsi, smul_smul, oE_mul, map_mul]`. Unfold `ee`. Rewrite using `[smul_smul]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Establish `hsS : (s : ℂ) • ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A) ∈ S`. Rewrite using `[hsv]`. Conclude with `sum_mem fun i _ => claimC hPsi hI hb p n lam ε hId y hgood (c * κ i) i`. Take `⟨k2, hk2⟩` from `hsS`.

Rewrite `hk2` using `[Hf_smul_right, Complex.conj_natCast, im_natCast_mul]`. Establish `hcop : IsCoprime (s : ℤ) ((p ^ n : ℕ) : ℤ)` using `Nat.isCoprime_iff_coprime.mpr (hs.pow_right n)`. Take `⟨u, v, huv⟩` from `hcop`. Establish `huvR : (u : ℝ) * s + (v : ℝ) * (p : ℝ) ^ n = 1` using `by exact_mod_cast huv`. Use `⟨u * k2 + v * k1, ?_⟩` and prove the remaining obligations.

Use `set x := (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A)).im`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hle2 hw`.
-/
theorem stepA (hPsi : InducedCMType D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (p n : ℕ) [Fact p.Prime]
    (hI : Formalism.L2.GlobalTheoryTheory.IntegralLatticeDensity.IO.HfInt (tor0 D cc δ) (La D (tor0 D cc δ) L L'))
    (hLoc : LocBasis D p (YYl D L L') b)
    (hb : ∀ i, ee D cc δ b i ∈ La D (tor0 D cc δ) L L')
    (lam : Qbar →+* ℂ_[p]) (ε : 𝓞 D.host.K) (hId : IsIdem D lam (2 * n + 2) ε)
    (y : Fin r → Fin (p ^ n))
    (hgood : ∀ i, ∃ k : ℤ, (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) (ee D cc δ b i)).im = k) :
    ∀ v ∈ La D (tor0 D cc δ) L L', ∃ k : ℤ,
      (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) v).im = k := by
  set S := imIntSub (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y) with hS
  suffices hle : La D (tor0 D cc δ) L L' ≤ S from fun v hv => hle hv
  unfold La
  apply (AddSubgroup.closure_le _).mpr
  rintro z ⟨w, hw, A, hA, rfl⟩
  have hle2 : lamOf D cc δ ≤ S.comap (smulHom D cc δ A) := by
    unfold lamOf
    apply (AddSubgroup.closure_le _).mpr
    rintro w' ⟨c, hc, rfl⟩
    show (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ S
    have hvLa : (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ La D (tor0 D cc δ) L L' :=
      AddSubgroup.subset_closure ⟨δ * D.host.φ₀ (oE D c),
        AddSubgroup.subset_closure ⟨c, hc, rfl⟩, A, hA, rfl⟩
    obtain ⟨k1, hk1⟩ := pn_int hPsi hI hb p n ε y hvLa
    obtain ⟨s, hs, κ, hκ⟩ := hLoc.2.2 A hA
    have hsv : (s : ℂ) • ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A) =
        ∑ i, D.host.φ₀ (oE D (c * κ i)) • ee D cc δ b i := by
      rw [smul_comm, ← embV_natsmul, hκ, embV_sum, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [embV_smulK hPsi, smul_smul, oE_mul, map_mul]
      unfold ee
      rw [smul_smul]
      congr 1
      ring
    have hsS : (s : ℂ) • ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A) ∈ S := by
      rw [hsv]
      exact sum_mem fun i _ => claimC hPsi hI hb p n lam ε hId y hgood (c * κ i) i
    obtain ⟨k2, hk2⟩ := hsS
    rw [Hf_smul_right, Complex.conj_natCast, im_natCast_mul] at hk2
    have hcop : IsCoprime (s : ℤ) ((p ^ n : ℕ) : ℤ) :=
      Nat.isCoprime_iff_coprime.mpr (hs.pow_right n)
    obtain ⟨u, v, huv⟩ := hcop
    have huvR : (u : ℝ) * s + (v : ℝ) * (p : ℝ) ^ n = 1 := by exact_mod_cast huv
    refine ⟨u * k2 + v * k1, ?_⟩
    set x := (Hf D (tor0 D cc δ) (liftY D (tor0 D cc δ) δ p n ε b y)
      ((δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A)).im
    calc x = ((u : ℝ) * s + (v : ℝ) * (p : ℝ) ^ n) * x := by rw [huvR, one_mul]
      _ = _ := by push_cast; rw [← hk1, ← hk2]; ring
  exact hle2 hw

end StepA

section StepC

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

variable (D cc δ) in

def locSub {r : ℕ} (p : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) : AddSubgroup (VC D N N') where
  carrier := {v | ∃ (B : Matrix (Fin N') (Fin N) D.host.E) (s : ℕ) (κ : Fin r → 𝓞 D.host.K),
    v = δ • embV D (tor0 D cc δ) B ∧ Nat.Coprime s p ∧ (s : D.host.E) • B = ∑ i, oE D (κ i) • b i}
  zero_mem' := ⟨0, 1, 0, by
    show (0 : VC D N N') = δ • (embVh D cc δ) 0
    rw [map_zero, smul_zero], Nat.coprime_one_left p, by simp [oE]⟩
  add_mem' := by
    rintro v1 v2 ⟨B1, s1, κ1, rfl, hs1, h1⟩ ⟨B2, s2, κ2, rfl, hs2, h2⟩
    refine ⟨B1 + B2, s1 * s2, fun i => (s2 : 𝓞 D.host.K) * κ1 i + (s1 : 𝓞 D.host.K) * κ2 i,
      by rw [embV_add, smul_add], Nat.Coprime.mul_left hs1 hs2, ?_⟩
    have e1 : ((s1 * s2 : ℕ) : D.host.E) • B1 = (s2 : D.host.E) • ((s1 : D.host.E) • B1) := by
      rw [smul_smul, Nat.cast_mul, mul_comm]
    have e2 : ((s1 * s2 : ℕ) : D.host.E) • B2 = (s1 : D.host.E) • ((s2 : D.host.E) • B2) := by
      rw [smul_smul, Nat.cast_mul]
    rw [smul_add, e1, e2, h1, h2, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [smul_smul, smul_smul, ← add_smul]
    congr 1
  neg_mem' := by
    rintro v ⟨B, s, κ, rfl, hs, h⟩
    refine ⟨-B, s, -κ, ?_, hs, ?_⟩
    · show -(δ • (embVh D cc δ) B) = δ • (embVh D cc δ) (-B)
      rw [map_neg, smul_neg]
    · rw [smul_neg, h, ← Finset.sum_neg_distrib]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp [oE, neg_smul]

/- English proof (translation)
Unfold `La`. Apply `(AddSubgroup.closure_le _).mpr` to reduce the goal to its premises. Introduce and unpack `z ⟨w, hw, A, hA, rfl⟩`. Establish `hle2 : lamOf D cc δ ≤ (locSub D cc δ p b).comap (smulHom D cc δ A)`. Unfold `lamOf`.

Apply `(AddSubgroup.closure_le _).mpr` to reduce the goal to its premises. Introduce and unpack `w' ⟨c, hc, rfl⟩`. Use `show (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ locSub D cc δ p b`. Take `⟨s, hs, κ, hκ⟩` from `hLoc.2.2 A hA`. Use `⟨oE D c • A, s, fun i => c * κ i, ?_, hs, ?_⟩` and prove the remaining obligations.

Rewrite using `[embV_smulK hPsi, mul_smul]`. Rewrite using `[smul_comm, hκ, Finset.smul_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, oE_mul]`. Conclude with `hle2 hw`.
-/
theorem La_le_loc (hPsi : InducedCMType D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} {p : ℕ} (hLoc : LocBasis D p (YYl D L L') b) :
    La D (tor0 D cc δ) L L' ≤ locSub D cc δ p b := by
  unfold La
  apply (AddSubgroup.closure_le _).mpr
  rintro z ⟨w, hw, A, hA, rfl⟩
  have hle2 : lamOf D cc δ ≤ (locSub D cc δ p b).comap (smulHom D cc δ A) := by
    unfold lamOf
    apply (AddSubgroup.closure_le _).mpr
    rintro w' ⟨c, hc, rfl⟩
    show (δ * D.host.φ₀ (oE D c)) • embV D (tor0 D cc δ) A ∈ locSub D cc δ p b
    obtain ⟨s, hs, κ, hκ⟩ := hLoc.2.2 A hA
    refine ⟨oE D c • A, s, fun i => c * κ i, ?_, hs, ?_⟩
    · rw [embV_smulK hPsi, mul_smul]
    · rw [smul_comm, hκ, Finset.smul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [smul_smul, oE_mul]
  exact hle2 hw

/- English proof (translation)
Take `⟨B, s, κ, hB, hs, hsB⟩` from `La_le_loc hPsi hLoc hmem`. Unfold `liftY at hB`. Establish `h1` using `smul_right_injective (VC D N N') hδ hB`. Set `τ0 : D.what₂.Tau` to `D.eTau.symm ⟨1, (D.R.Psi).one_mem⟩`. Establish `hB0 : ((((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n) • ∑ j, (((y j : ℕ) : D.host.E)) • b j) = B`.

Use function extensionality and compare the values at `i j`. Use `congrFun (congrFun (congrFun h1 τ0) i) j` as an intermediate fact. Conclude with `(embT D τ0).injective this`. Rewrite `hsB` using `[← hB0]`. Establish `hp0K : (p : D.host.K) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`.

Use `set g : Fin r → D.host.K := fun j => (s : D.host.K) * (ε : D.host.K) / (p : D.host.K) ^ n * ((y j : ℕ) : D.host.K) - (κ j : D.host.K) with hg`. Establish `hsum : ∑ j, g j • b j = 0`. Establish `hc : ∀ j, g j • b j = ((g j : D.host.K) : D.host.E) • b j` using `fun j => (algebraMap_smul D.host.E (g j) (b j)).symm`. Repeatedly rewrite using `[hc]`. Rewrite using `[← sub_eq_zero.mpr hsB, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, smul_smul, ← sub_smul]`. Use `congr 1`. Simplify using `only [hg, oE]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgj` using `Fintype.linearIndependent_iff.mp hLoc.1 g hsum`. Use function extensionality and compare the values at `j`. Establish `hj` using `hgj j`. Simplify using `only [hg, sub_eq_zero] at hj`.

Establish `hE : (s : D.host.E) * oE D ε * ((y j : ℕ) : D.host.E) = (p : D.host.E) ^ n * oE D (κ j)`. Use `congrArg (fun x : D.host.K => (x : D.host.E)) hj` as an intermediate fact. Establish `hp0E : (p : D.host.E) ≠ 0` using `by exact_mod_cast hp.out.ne_zero`. Unfold `oE`. Rewrite using `[← this]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Establish `hC` using `congrArg (Lp D lam) hE`. Rewrite `hC` using `[map_mul, map_mul, map_natCast, map_natCast, map_mul, map_pow, map_natCast]`. Take `⟨h1', -⟩` from `hId`.

Rewrite `h1'` using `[lamC_phi_zero_eq]`. Establish `hε1 : ‖Lp D lam (oE D ε)‖ = 1` using `norm_eq_one_of_close (lt_of_le_of_lt h1' (pzpow_lt_one (by omega)))`. Establish `hnorm : ‖((y j : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ))`. Use `congrArg norm hC` as an intermediate fact. Rewrite `this` using `[norm_mul, norm_mul, norm_mul, normC_nat_coprime hs, hε1, one_mul, one_mul, normC_p_pow]`.

Rewrite using `[this]`. Combine the equalities or inequalities in the displayed calculation. Establish `hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((y j : ℕ) : ℤ)`. Use `dvd_of_normC (p := p) (k := ((y j : ℕ) : ℤ)) (n := n) (by rw [Int.cast_natCast]; exact hnorm)` as an intermediate fact. Conclude with `this` after adjusting the coercions.

Establish `hdvd' : p ^ n ∣ (y j : ℕ)` using `Int.natCast_dvd_natCast.mp hdvd`. Use `Nat.eq_zero_of_dvd_of_lt hdvd' (y j).isLt` as an intermediate fact. Conclude with `Fin.ext (by simpa using this)`.
-/
theorem stepC (hPsi : InducedCMType D) {L : Submodule (𝓞 D.host.E) (Fin N → D.host.E)}
    {L' : Submodule (𝓞 D.host.E) (Fin N' → D.host.E)} {r : ℕ}
    {b : Fin r → Matrix (Fin N') (Fin N) D.host.E} (p n : ℕ) [hp : Fact p.Prime]
    (hLoc : LocBasis D p (YYl D L L') b) (hδ : δ ≠ 0)
    (lam : Qbar →+* ℂ_[p]) (ε : 𝓞 D.host.K) (hId : IsIdem D lam (2 * n + 2) ε)
    (y : Fin r → Fin (p ^ n))
    (hmem : liftY D (tor0 D cc δ) δ p n ε b y ∈ La D (tor0 D cc δ) L L') : y = 0 := by
  obtain ⟨B, s, κ, hB, hs, hsB⟩ := La_le_loc hPsi hLoc hmem
  unfold liftY at hB
  have h1 := smul_right_injective (VC D N N') hδ hB
  let τ0 : D.what₂.Tau := D.eTau.symm ⟨1, (D.R.Psi).one_mem⟩
  have hB0 : ((((ε : D.host.K) : D.host.E) / (p : D.host.E) ^ n) •
      ∑ j, (((y j : ℕ) : D.host.E)) • b j) = B := by
    funext i j
    have := congrFun (congrFun (congrFun h1 τ0) i) j
    exact (embT D τ0).injective this
  rw [← hB0] at hsB
  have hp0K : (p : D.host.K) ≠ 0 := by exact_mod_cast hp.out.ne_zero
  set g : Fin r → D.host.K := fun j =>
    (s : D.host.K) * (ε : D.host.K) / (p : D.host.K) ^ n * ((y j : ℕ) : D.host.K) - (κ j : D.host.K) with hg
  have hsum : ∑ j, g j • b j = 0 := by
    have hc : ∀ j, g j • b j = ((g j : D.host.K) : D.host.E) • b j := fun j =>
      (algebraMap_smul D.host.E (g j) (b j)).symm
    simp_rw [hc]
    rw [← sub_eq_zero.mpr hsB, Finset.smul_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [smul_smul, smul_smul, ← sub_smul]
    congr 1
    simp only [hg, oE]
    push_cast
    ring
  have hgj := Fintype.linearIndependent_iff.mp hLoc.1 g hsum
  funext j
  have hj := hgj j
  simp only [hg, sub_eq_zero] at hj
  have hE : (s : D.host.E) * oE D ε * ((y j : ℕ) : D.host.E) = (p : D.host.E) ^ n * oE D (κ j) := by
    have := congrArg (fun x : D.host.K => (x : D.host.E)) hj
    have hp0E : (p : D.host.E) ≠ 0 := by exact_mod_cast hp.out.ne_zero
    unfold oE
    rw [← this]
    push_cast
    field_simp
  have hC := congrArg (Lp D lam) hE
  rw [map_mul, map_mul, map_natCast, map_natCast, map_mul, map_pow, map_natCast] at hC
  obtain ⟨h1', -⟩ := hId
  rw [lamC_phi_zero_eq] at h1'
  have hε1 : ‖Lp D lam (oE D ε)‖ = 1 :=
    norm_eq_one_of_close (lt_of_le_of_lt h1' (pzpow_lt_one (by omega)))
  have hnorm : ‖((y j : ℕ) : ℂ_[p])‖ ≤ (p : ℝ) ^ (-(n : ℤ)) := by
    have := congrArg norm hC
    rw [norm_mul, norm_mul, norm_mul, normC_nat_coprime hs, hε1, one_mul, one_mul, normC_p_pow] at this
    rw [this]
    calc _ ≤ (p : ℝ) ^ (-(n : ℤ)) * 1 :=
          mul_le_mul_of_nonneg_left (norm_Lp_le_one D lam (κ j)) (by positivity)
      _ = _ := mul_one _
  have hdvd : ((p ^ n : ℕ) : ℤ) ∣ ((y j : ℕ) : ℤ) := by
    have := dvd_of_normC (p := p) (k := ((y j : ℕ) : ℤ)) (n := n) (by rw [Int.cast_natCast]; exact hnorm)
    exact_mod_cast this
  have hdvd' : p ^ n ∣ (y j : ℕ) := Int.natCast_dvd_natCast.mp hdvd
  have := Nat.eq_zero_of_dvd_of_lt hdvd' (y j).isLt
  exact Fin.ext (by simpa using this)

end StepC

end Formalism.L2.PairingIndexBounds.Xf.XiOneP

namespace Formalism.L2.PairingIndexBounds.Xf.XiOneP

open NumberField Formalism.BasicNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.GL3Theta

variable {D : D7} {N N' : ℕ} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ}

/- English proof (translation)
Establish `hterm : ∀ a : Fin r → Fin (p ^ n), (kap D (tor0 D cc δ) x (vecN D (tor0 D cc δ) δ p n b a))⁻¹ = ∏ i, Complex.exp (2 * Real.pi * Complex.I * (((a i : ℕ) : ℂ) * (((Hf D (tor0 D cc δ) x (ee D cc δ b i)).im : ℝ) : ℂ)))`. Introduce `a`. Unfold `kap`. Rewrite using `[← Complex.exp_neg, va_eq]`. Unfold `Xv`.

Rewrite using `[Hf_sum_right, Complex.im_sum, ← Complex.exp_sum]`. Use `congr 1`. Simplify using `only [Hf_smul_right, Complex.conj_natCast, im_natCast_mul]`. Use `push_cast`. Rewrite using `[neg_mul, neg_neg, Finset.mul_sum]`.

Repeatedly rewrite using `[hterm]`. Conclude with `(Fintype.prod_sum (fun i (j : Fin (p ^ n)) => Complex.exp (2 * Real.pi * Complex.I * (((j : ℕ) : ℂ) * (((Hf D (tor0 D cc δ) x (ee D cc δ b i)).im : ℝ) : ℂ))))).symm`.
-/
theorem kap_sum {r : ℕ} (p n : ℕ) (b : Fin r → Matrix (Fin N') (Fin N) D.host.E) (x : VC D N N') :
    ∑ a : Fin r → Fin (p ^ n), (kap D (tor0 D cc δ) x (vecN D (tor0 D cc δ) δ p n b a))⁻¹ =
      ∏ i, ∑ j : Fin (p ^ n), Complex.exp (2 * Real.pi * Complex.I *
        (((j : ℕ) : ℂ) * (((Hf D (tor0 D cc δ) x (ee D cc δ b i)).im : ℝ) : ℂ))) := by
  have hterm : ∀ a : Fin r → Fin (p ^ n), (kap D (tor0 D cc δ) x (vecN D (tor0 D cc δ) δ p n b a))⁻¹ =
      ∏ i, Complex.exp (2 * Real.pi * Complex.I *
        (((a i : ℕ) : ℂ) * (((Hf D (tor0 D cc δ) x (ee D cc δ b i)).im : ℝ) : ℂ))) := by
    intro a
    unfold kap
    rw [← Complex.exp_neg, va_eq]
    unfold Xv
    rw [Hf_sum_right, Complex.im_sum, ← Complex.exp_sum]
    congr 1
    simp only [Hf_smul_right, Complex.conj_natCast, im_natCast_mul]
    push_cast
    rw [neg_mul, neg_neg, Finset.mul_sum]
  simp_rw [hterm]
  exact (Fintype.prod_sum (fun i (j : Fin (p ^ n)) => Complex.exp (2 * Real.pi * Complex.I *
    (((j : ℕ) : ℂ) * (((Hf D (tor0 D cc δ) x (ee D cc δ b i)).im : ℝ) : ℂ))))).symm

end Formalism.L2.PairingIndexBounds.Xf.XiOneP
