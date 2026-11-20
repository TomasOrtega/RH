import Formalism.SharpRestriction.GrowthBounds.Lemma5aAt

noncomputable section

open Formalism.MainNotions.G MvPolynomial

namespace Formalism.MainNotions.G.Joints

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

def nv (x : O) : ℕ := (IsDiscreteValuationRing.addVal O x).toNat

/- English proof (translation)
Establish `hat : IsDiscreteValuationRing.addVal O a ≠ ⊤`. Simplify `ha` using `[IsDiscreteValuationRing.addVal_eq_top_iff]`. Establish `hbt : IsDiscreteValuationRing.addVal O b ≠ ⊤`. Simplify `hb` using `[IsDiscreteValuationRing.addVal_eq_top_iff]`. Unfold `nv`.

Rewrite using `[AddValuation.map_mul, ENat.toNat_add hat hbt]`.
-/
theorem nv_mul {a b : O} (ha : a ≠ 0) (hb : b ≠ 0) : nv (a * b) = nv a + nv b := by
  have hat : IsDiscreteValuationRing.addVal O a ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using ha
  have hbt : IsDiscreteValuationRing.addVal O b ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using hb
  unfold nv
  rw [AddValuation.map_mul, ENat.toNat_add hat hbt]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [nv]`. Consider the case `succ k ih => rw [pow_succ, nv_mul (pow_ne_zero k ha) ha, ih]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem nv_pow {a : O} (ha : a ≠ 0) (k : ℕ) : nv (a ^ k) = k * nv a := by
  induction k with
  | zero => simp [nv]
  | succ k ih => rw [pow_succ, nv_mul (pow_ne_zero k ha) ha, ih]; ring

/- English proof (translation)
Establish `hx : x ≠ 0`. Introduce and unpack `rfl`. Rewrite `h` using `[zero_mul]`. Conclude with `ha ((map_eq_zero_iff _ (IsFractionRing.injective O (KK O))).1 h.symm)`. Unfold `ordW`.

Rewrite using `[if_neg hx]`. Establish `h1` using `Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) x)`. Use `set ab := Classical.choose (IsLocalization.surj (nonZeroDivisors O) x) with hab`. Establish `hb2 : (ab.2 : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero _`. Establish `h2 : a * (ab.2 : O) = ab.1 * b`.

Apply `IsFractionRing.injective O (KK O)` to reduce the goal to its premises. Rewrite using `[map_mul, map_mul, ← h, ← h1]`. Expand and normalize the polynomial expressions, which then agree. Establish `ha1 : ab.1 ≠ 0`. Introduce `h0`.

Rewrite `h2` using `[h0, zero_mul]`. Conclude with `(mul_ne_zero ha hb2) h2`. Establish `h3 : nv a + nv (ab.2 : O) = nv ab.1 + nv b`. Rewrite using `[← nv_mul ha hb2, ← nv_mul ha1 hb, h2]`. Use `show (((nv ab.1 : ℤ) - (nv (ab.2 : O) : ℤ) : ℤ) : WithTop ℤ) = _`.

Use `congr 1`. Use linear arithmetic over natural numbers and integers.
-/
theorem ordW_eq (x : KK O) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x * algebraMap O (KK O) b = algebraMap O (KK O) a) :
    ordW x = (((nv a : ℤ) - (nv b : ℤ) : ℤ) : WithTop ℤ) := by
  classical
  have hx : x ≠ 0 := by
    rintro rfl
    rw [zero_mul] at h
    exact ha ((map_eq_zero_iff _ (IsFractionRing.injective O (KK O))).1 h.symm)
  unfold ordW
  rw [if_neg hx]
  have h1 := Classical.choose_spec (IsLocalization.surj (nonZeroDivisors O) x)
  set ab := Classical.choose (IsLocalization.surj (nonZeroDivisors O) x) with hab
  have hb2 : (ab.2 : O) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have h2 : a * (ab.2 : O) = ab.1 * b := by
    apply IsFractionRing.injective O (KK O)
    rw [map_mul, map_mul, ← h, ← h1]; ring
  have ha1 : ab.1 ≠ 0 := by
    intro h0
    rw [h0, zero_mul] at h2
    exact (mul_ne_zero ha hb2) h2
  have h3 : nv a + nv (ab.2 : O) = nv ab.1 + nv b := by
    rw [← nv_mul ha hb2, ← nv_mul ha1 hb, h2]
  show (((nv ab.1 : ℤ) - (nv (ab.2 : O) : ℤ) : ℤ) : WithTop ℤ) = _
  congr 1
  omega

/- English proof (translation)
Establish `h1 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0`. Introduce `h0`. Establish `: IsUnit (p : O)`. Break down `IsDiscreteValuationRing.exists_irreducible O with ⟨w, hw⟩` into its components or cases. Take `⟨n, u, hu⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible S.p_ne hw`.

Rewrite `h0` using `[hu, IsDiscreteValuationRing.addVal_def' u hw n]`. Establish `hn : n = 0` using `by exact_mod_cast h0`. Rewrite using `[hu, hn]`. Simplify using the standard rewrite rules. Conclude with `(IsLocalRing.mem_maximalIdeal _).1 S.p_mem this`.

Establish `h2 : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤`. Simplify `S.p_ne` using `[IsDiscreteValuationRing.addVal_eq_top_iff]`. Unfold `ramE`. Simplify using `[ENat.toNat_eq_zero, h1, h2]`.
-/
theorem ramE_ne_zero {p : ℕ} (S : UniformizedDVR p O) : ramE p O ≠ 0 := by
  have h1 : IsDiscreteValuationRing.addVal O (p : O) ≠ 0 := by
    intro h0
    have : IsUnit (p : O) := by
      rcases IsDiscreteValuationRing.exists_irreducible O with ⟨w, hw⟩
      obtain ⟨n, u, hu⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible S.p_ne hw
      rw [hu, IsDiscreteValuationRing.addVal_def' u hw n] at h0
      have hn : n = 0 := by exact_mod_cast h0
      rw [hu, hn]; simp
    exact (IsLocalRing.mem_maximalIdeal _).1 S.p_mem this
  have h2 : IsDiscreteValuationRing.addVal O (p : O) ≠ ⊤ := by
    simpa [IsDiscreteValuationRing.addVal_eq_top_iff] using S.p_ne
  unfold ramE
  simp [ENat.toNat_eq_zero, h1, h2]

/- English proof (translation)
Simplify using `[vK, ordW]`.
-/
theorem vK_zero (p : ℕ) : vK p (0 : KK O) = ⊤ := by
  simp [vK, ordW]

/- English proof (translation)
Unfold `vK`. Rewrite using `[ordW_eq x a b ha hb h]`. Both sides reduce to the same expression.
-/
theorem vK_eq (p : ℕ) (x : KK O) (a b : O) (ha : a ≠ 0) (hb : b ≠ 0)
    (h : x * algebraMap O (KK O) b = algebraMap O (KK O) a) :
    vK p x = (((((nv a : ℤ) - (nv b : ℤ) : ℤ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  unfold vK
  rw [ordW_eq x a b ha hb h]
  rfl

/- English proof (translation)
Distinguish the cases in `hx : x = 0`. Substitute `hx` using the available equality. Rewrite using `[mul_zero, vK_zero, WithTop.add_top]`. Take `⟨⟨a, b⟩, hab⟩` from `IsLocalization.surj (nonZeroDivisors O) x`. Establish `hb : (b : O) ≠ 0` using `nonZeroDivisors.coe_ne_zero _`.

Establish `hb' : algebraMap O (KK O) (b : O) ≠ 0` using `by simp`. Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Simplify using `only [map_zero] at hab`. Conclude with `(mul_ne_zero hx hb') hab`.

Establish `hp : ((p : O) ^ D) ≠ 0` using `pow_ne_zero D S.p_ne`. Establish `h2 : (p : KK O) ^ D * x * algebraMap O (KK O) (b : O) = algebraMap O (KK O) ((p : O) ^ D * a)`. Rewrite using `[map_mul, map_pow, map_natCast, ← hab]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[vK_eq p x a (b : O) ha hb hab, vK_eq p _ _ (b : O) (mul_ne_zero hp ha) hb h2, nv_mul hp ha, nv_pow S.p_ne]`.

Establish `he : (ramE p O : ℚ) ≠ 0` using `by exact_mod_cast ramE_ne_zero S`. Rewrite using `[← WithTop.coe_add]`. Use `congr 1`. Establish `: nv (p : O) = ramE p O` using `rfl`. Rewrite using `[this]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem vK_pow_mul {p : ℕ} (S : UniformizedDVR p O) (D : ℕ) (x : KK O) :
    vK p ((p : KK O) ^ D * x) = ((D : ℚ) : WithTop ℚ) + vK p x := by
  by_cases hx : x = 0
  · subst hx
    rw [mul_zero, vK_zero, WithTop.add_top]
  obtain ⟨⟨a, b⟩, hab⟩ := IsLocalization.surj (nonZeroDivisors O) x
  have hb : (b : O) ≠ 0 := nonZeroDivisors.coe_ne_zero _
  have hb' : algebraMap O (KK O) (b : O) ≠ 0 := by simp
  have ha : a ≠ 0 := by
    rintro rfl
    simp only [map_zero] at hab
    exact (mul_ne_zero hx hb') hab
  have hp : ((p : O) ^ D) ≠ 0 := pow_ne_zero D S.p_ne
  have h2 : (p : KK O) ^ D * x * algebraMap O (KK O) (b : O) = algebraMap O (KK O) ((p : O) ^ D * a) := by
    rw [map_mul, map_pow, map_natCast, ← hab]; ring
  rw [vK_eq p x a (b : O) ha hb hab, vK_eq p _ _ (b : O) (mul_ne_zero hp ha) hb h2, nv_mul hp ha, nv_pow S.p_ne]
  have he : (ramE p O : ℚ) ≠ 0 := by exact_mod_cast ramE_ne_zero S
  rw [← WithTop.coe_add]
  congr 1
  have : nv (p : O) = ramE p O := rfl
  rw [this]
  push_cast
  field_simp
  ring

/- English proof (translation)
Establish `h` using `vK_eq p (algebraMap O (KK O) o) o 1 ho one_ne_zero (by simp)`. Rewrite using `[h]`. Establish `: nv (1 : O) = 0` using `by simp [nv]`. Rewrite using `[this]`. Simplify using the standard rewrite rules.
-/
theorem vK_alg (p : ℕ) (o : O) (ho : o ≠ 0) :
    vK p (algebraMap O (KK O) o) = ((((nv o : ℕ) : ℚ) / (ramE p O : ℚ) : ℚ) : WithTop ℚ) := by
  have h := vK_eq p (algebraMap O (KK O) o) o 1 ho one_ne_zero (by simp)
  rw [h]
  have : nv (1 : O) = 0 := by simp [nv]
  rw [this]
  simp

/- English proof (translation)
Introduce `q hq`. Distinguish the cases in `ho : o = 0`. Substitute `ho` using the available equality. Rewrite `hq` using `[map_zero, mul_zero, vK_zero]`. Conclude with `absurd hq (by simp)`.

Rewrite `hq` using `[vK_pow_mul S, vK_alg p o ho, ← WithTop.coe_add, WithTop.coe_inj]`. Rewrite using `[← hq]`. Use `push_cast`. Establish `: (0 : ℝ) ≤ (nv o : ℝ) / (ramE p O : ℝ)` using `by positivity`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem geQ_vK_pow_mul {p : ℕ} (S : UniformizedDVR p O) (c : ℕ) (o : O) :
    Formalism.MainNotions.PlaneGramData.geQ (vK p ((p : KK O) ^ c * algebraMap O (KK O) o)) (c : ℝ) := by
  intro q hq
  by_cases ho : o = 0
  · subst ho
    rw [map_zero, mul_zero, vK_zero] at hq
    exact absurd hq (by simp)
  rw [vK_pow_mul S, vK_alg p o ho, ← WithTop.coe_add, WithTop.coe_inj] at hq
  rw [← hq]
  push_cast
  have : (0 : ℝ) ≤ (nv o : ℝ) / (ramE p O : ℝ) := by positivity
  linarith

/- English proof (translation)
Assume the negation of the conclusion as `hu`. Establish `hm : (n : O) ∈ IsLocalRing.maximalIdeal O` using `(IsLocalRing.mem_maximalIdeal _).2 hu`. Establish `hco : Nat.Coprime p n` using `(Nat.Prime.coprime_iff_not_dvd hp).2 hn`. Establish `hb` using `Nat.gcd_eq_gcd_ab p n`. Rewrite `hb` using `[hco]`.

Establish `h1 : (1 : O) = (p : O) * ((Nat.gcdA p n : ℤ) : O) + (n : O) * ((Nat.gcdB p n : ℤ) : O)`. Use `congrArg (fun z : ℤ => (z : O)) hb` as an intermediate fact. Simplify using `using this`. Establish `: (1 : O) ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[h1]`.

Conclude with `Ideal.add_mem _ (Ideal.mul_mem_right _ _ S.p_mem) (Ideal.mul_mem_right _ _ hm)`. Conclude with `(Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this`.
-/
theorem isUnit_natCast_of_not_dvd {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) (n : ℕ) (hn : ¬ p ∣ n) :
    IsUnit (n : O) := by
  by_contra hu
  have hm : (n : O) ∈ IsLocalRing.maximalIdeal O := (IsLocalRing.mem_maximalIdeal _).2 hu
  have hco : Nat.Coprime p n := (Nat.Prime.coprime_iff_not_dvd hp).2 hn
  have hb := Nat.gcd_eq_gcd_ab p n
  rw [hco] at hb
  have h1 : (1 : O) = (p : O) * ((Nat.gcdA p n : ℤ) : O) + (n : O) * ((Nat.gcdB p n : ℤ) : O) := by
    have := congrArg (fun z : ℤ => (z : O)) hb
    simpa using this
  have : (1 : O) ∈ IsLocalRing.maximalIdeal O := by
    rw [h1]
    exact Ideal.add_mem _ (Ideal.mul_mem_right _ _ S.p_mem) (Ideal.mul_mem_right _ _ hm)
  exact (Ideal.ne_top_iff_one _).1 (IsLocalRing.maximalIdeal.isMaximal O).ne_top this

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Establish `: CharZero (KK O)` using `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`. Break down `h with rfl | h` into its components or cases. Conclude with `⟨0, by simp⟩`. Distinguish the cases in `hx : x = 0`.

Substitute `hx; exact ⟨0, by simp⟩` using the available equality. Establish `hv : (c : ℤ) ≤ padicValRat p x` using `by exact_mod_cast h`. Establish `hnum : x.num ≠ 0` using `Rat.num_ne_zero.2 hx`. Establish `hdef : padicValRat p x = padicValInt p x.num - padicValNat p x.den` using `rfl`. Establish `hden : ¬ p ∣ x.den`.

Introduce `hd`. Establish `hn : ¬ (p : ℤ) ∣ x.num`. Introduce `hn`. Establish `h1 : p ∣ x.num.natAbs` using `Int.natCast_dvd.1 hn`. Use `Nat.dvd_gcd h1 hd` as an intermediate fact.

Rewrite `this` using `[x.reduced]`. Conclude with `hp.one_lt.ne' (Nat.dvd_one.1 this)`. Establish `h0 : padicValInt p x.num = 0` using `padicValInt.eq_zero_of_not_dvd hn`. Establish `h1 : 1 ≤ padicValNat p x.den` using `one_le_padicValNat_of_dvd x.den_nz hd`. Rewrite `hv` using `[hdef, h0]`.

Use linear arithmetic over natural numbers and integers. Establish `hd0 : padicValNat p x.den = 0` using `padicValNat.eq_zero_of_not_dvd hden`. Establish `hc : c ≤ padicValInt p x.num`. Rewrite `hv` using `[hdef, hd0]`. Simplify using `using hv`.

Establish `hdvd : (p : ℤ) ^ c ∣ x.num` using `(padicValInt_dvd_iff c x.num).2 (Or.inr hc)`. Take `⟨k, hk⟩` from `hdvd`. Take `⟨u, hu⟩` from `isUnit_natCast_of_not_dvd hp S x.den hden`. Use `⟨(k : O) * ((u⁻¹ : Oˣ) : O), ?_⟩` and prove the remaining obligations. Establish `hdK : ((x.den : ℕ) : KK O) ≠ 0` using `by exact_mod_cast x.den_nz`.

Establish `huK : algebraMap O (KK O) (u : O) = ((x.den : ℕ) : KK O)` using `by rw [hu]; simp`. Establish `hinv : algebraMap O (KK O) ((u⁻¹ : Oˣ) : O) = ((x.den : ℕ) : KK O)⁻¹`. Apply `eq_inv_of_mul_eq_one_left` to reduce the goal to its premises. Rewrite using `[← huK, ← map_mul]`. Simplify using the standard rewrite rules.

Rewrite using `[map_mul, hinv, Rat.cast_def, hk]`. Use `push_cast`. Rewrite using `[map_intCast]`. Clear the denominators using the available nonvanishing facts.
-/
theorem rat_padicGe_cast {p : ℕ} (hp : p.Prime) (S : UniformizedDVR p O) [CharZero O] (x : ℚ) (c : ℕ)
    (h : Formalism.MainNotions.CovariantDegrees.PadicGe p x c) :
    ∃ o : O, ((x : ℚ) : KK O) = (p : KK O) ^ c * algebraMap O (KK O) o := by
  have : Fact p.Prime := ⟨hp⟩
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  rcases h with rfl | h
  · exact ⟨0, by simp⟩
  by_cases hx : x = 0
  · subst hx; exact ⟨0, by simp⟩
  have hv : (c : ℤ) ≤ padicValRat p x := by exact_mod_cast h
  have hnum : x.num ≠ 0 := Rat.num_ne_zero.2 hx
  have hdef : padicValRat p x = padicValInt p x.num - padicValNat p x.den := rfl
  have hden : ¬ p ∣ x.den := by
    intro hd
    have hn : ¬ (p : ℤ) ∣ x.num := by
      intro hn
      have h1 : p ∣ x.num.natAbs := Int.natCast_dvd.1 hn
      have := Nat.dvd_gcd h1 hd
      rw [x.reduced] at this
      exact hp.one_lt.ne' (Nat.dvd_one.1 this)
    have h0 : padicValInt p x.num = 0 := padicValInt.eq_zero_of_not_dvd hn
    have h1 : 1 ≤ padicValNat p x.den := one_le_padicValNat_of_dvd x.den_nz hd
    rw [hdef, h0] at hv
    omega
  have hd0 : padicValNat p x.den = 0 := padicValNat.eq_zero_of_not_dvd hden
  have hc : c ≤ padicValInt p x.num := by
    rw [hdef, hd0] at hv
    simpa using hv
  have hdvd : (p : ℤ) ^ c ∣ x.num := (padicValInt_dvd_iff c x.num).2 (Or.inr hc)
  obtain ⟨k, hk⟩ := hdvd
  obtain ⟨u, hu⟩ := isUnit_natCast_of_not_dvd hp S x.den hden
  refine ⟨(k : O) * ((u⁻¹ : Oˣ) : O), ?_⟩
  have hdK : ((x.den : ℕ) : KK O) ≠ 0 := by exact_mod_cast x.den_nz
  have huK : algebraMap O (KK O) (u : O) = ((x.den : ℕ) : KK O) := by rw [hu]; simp
  have hinv : algebraMap O (KK O) ((u⁻¹ : Oˣ) : O) = ((x.den : ℕ) : KK O)⁻¹ := by
    apply eq_inv_of_mul_eq_one_left
    rw [← huK, ← map_mul]; simp
  rw [map_mul, hinv, Rat.cast_def, hk]
  push_cast
  rw [map_intCast]
  field_simp

/- English proof (translation)
Establish `hpK : ((p : KK O) ^ D) ≠ 0`. Apply `pow_ne_zero` to reduce the goal to its premises. Establish `: algebraMap O (KK O) (p : O) ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 S.p_ne`. Rewrite `this` using `[map_natCast]`. Then use the resulting hypothesis. Unfold `vBB`.

Establish `hs : (((p : KK O) ^ D) • G).support = G.support`. Use extensionality with `m`. Simplify using `[MvPolynomial.mem_support_iff, hpK]`. Rewrite using `[hs]`. Simplify using `only [MvPolynomial.coeff_smul, smul_eq_mul, vK_pow_mul S, add_assoc]`.

Distinguish the cases in `hne : G.support.Nonempty`. Conclude with `(Finset.apply_inf_eq_inf_comp_of_linearOrder (fun y : WithTop ℚ => ((D : ℚ) : WithTop ℚ) + y) (fun a b hab => add_le_add_right hab _) (by simp)).symm`. Rewrite `hne` using `[Finset.not_nonempty_iff_eq_empty]`. Simplify using `[hne]`.
-/
theorem vBB_pow_smul {p : ℕ} (S : UniformizedDVR p O) {σ : Type*} (D : ℕ) (G : MvPolynomial σ (KK O)) :
    vBB (O := O) p (((p : KK O) ^ D) • G) = ((D : ℚ) : WithTop ℚ) + vBB (O := O) p G := by
  have hpK : ((p : KK O) ^ D) ≠ 0 := by
    apply pow_ne_zero
    have : algebraMap O (KK O) (p : O) ≠ 0 := (map_ne_zero_iff _ (IsFractionRing.injective O (KK O))).2 S.p_ne
    rwa [map_natCast] at this
  unfold vBB
  have hs : (((p : KK O) ^ D) • G).support = G.support := by
    ext m
    simp [MvPolynomial.mem_support_iff, hpK]
  rw [hs]
  simp only [MvPolynomial.coeff_smul, smul_eq_mul, vK_pow_mul S, add_assoc]
  by_cases hne : G.support.Nonempty
  · exact (Finset.apply_inf_eq_inf_comp_of_linearOrder (fun y : WithTop ℚ => ((D : ℚ) : WithTop ℚ) + y)
      (fun a b hab => add_le_add_right hab _) (by simp)).symm
  · rw [Finset.not_nonempty_iff_eq_empty] at hne
    simp [hne]

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G MvPolynomial

namespace Formalism.MainNotions.G.Joints

variable {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Introduce `q hq`. Conclude with `absurd hq (by simp)`.
-/
theorem geQ_top (t : ℝ) : Formalism.MainNotions.PlaneGramData.geQ (⊤ : WithTop ℚ) t := by
  intro q hq
  exact absurd hq (by simp)

/- English proof (translation)
Use `⟨Finsupp.onFinset T (fun j => if j ∈ T then o j else 0) (fun j hj => by` and prove the remaining obligations. Assume the negation of the conclusion as `hT`. Simplify using `[hT] at hj), Finsupp.support_onFinset_subset, fun be => ?_⟩`. Unfold `Formalism.MainNotions.PlaneGramData.binomComb`. Rewrite using `[Finset.sum_subset (Finsupp.support_onFinset_subset)]`.

Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Simplify using `[Finsupp.onFinset_apply, hm]`. Introduce `m _ hm`. Rewrite using `[Finsupp.notMem_support_iff.1 hm]`. Simplify using the standard rewrite rules.
-/
theorem binomComb_onFinset {r : ℕ} (T : Finset (Fin r → ℕ)) (o : (Fin r → ℕ) → O) :
    ∃ lam : (Fin r → ℕ) →₀ O, lam.support ⊆ T ∧
      ∀ be : Fin r → ℕ, Formalism.MainNotions.PlaneGramData.binomComb (K := KK O) lam be =
        ∑ m ∈ T, algebraMap O (KK O) (o m) * ∏ a, (((be a).choose (m a) : ℕ) : KK O) := by
  classical
  refine ⟨Finsupp.onFinset T (fun j => if j ∈ T then o j else 0) (fun j hj => by
    by_contra hT; simp [hT] at hj), Finsupp.support_onFinset_subset, fun be => ?_⟩
  unfold Formalism.MainNotions.PlaneGramData.binomComb
  rw [Finset.sum_subset (Finsupp.support_onFinset_subset)]
  · refine Finset.sum_congr rfl fun m hm => ?_
    simp [Finsupp.onFinset_apply, hm]
  · intro m _ hm
    rw [Finsupp.notMem_support_iff.1 hm]
    simp

/- English proof (translation)
Unfold `Formalism.MainNotions.PlaneGramData.gamDig cUnit dUnit`. Use `Finset.prod_eq_one fun a _ => ?_` and prove the remaining obligations. Establish `: ((be a).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Simplify using `[this]`.
-/
theorem gamDig_one_zero {r : ℕ} (be : Fin r → ℕ) : Formalism.MainNotions.PlaneGramData.gamDig 1 (fun _ : Fin r => 0) be = 1 := by
  unfold Formalism.MainNotions.PlaneGramData.gamDig cUnit dUnit
  refine Finset.prod_eq_one fun a _ => ?_
  have : ((be a).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
  simp [this]

/- English proof (translation)
Introduce `p O _ _ _ _ hset g r rho hrho`. Take `⟨⟨S⟩, n', hG⟩` from `hset`. Establish `hp` using `hG.prime`. Establish `h5` using `hG.five_le`. Establish `hK : CharZero (KK O)` using `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`.

Take `⟨hA, hB⟩` from `h p hp h5`. Break down `g with _ | t` into its components or cases. Establish `hr : rho = fun _ => 0`. Use function extensionality and compare the values at `a`. Use `hrho a` as an intermediate fact.

Simplify using `using this`. Substitute `hr` using the available equality. Simplify using `only [pow_zero, gamDig_one_zero]`. Use `⟨fun be => by simp, fun be => by simp, fun c _ ε => ?_⟩` and prove the remaining obligations. Take `⟨lam, hsup, hlam⟩` from `binomComb_onFinset (O := O) ({0} : Finset (Fin r → ℕ)) (fun _ => 1)`.

Use `⟨lam, fun m hm => ?_, fun be => ?_⟩` and prove the remaining obligations. Use `Finset.mem_singleton.1 (hsup hm)` as an intermediate fact. Substitute `this` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[hlam be]`.

Establish `: ((if ε = true then ((1 : ℚ) : KK O) else ((1 : ℚ) : KK O)⁻¹) - ∑ m ∈ ({0} : Finset (Fin r → ℕ)), algebraMap O (KK O) 1 * ∏ a, (((be a).choose (m a) : ℕ) : KK O)) = 0`. Apply the tactic sequence `cases ε <;> simp`. Rewrite using `[this, vK_zero]`. Conclude with `geQ_top _`. Take `⟨hU, _, hQ⟩` from `hB (Fin r) (fun _ => t) rho hrho`.

Establish `hlet : ∀ (be : Fin r → ℕ) (a : Fin r), ((rho a + p ^ (t + 1) * be a).factorial : ℚ) = (((rho a).factorial : ℚ) * ((be a).factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ (be a)) * (cUnit (p ^ (t + 1)) (be a) * dUnit (p ^ (t + 1)) (be a) (rho a))`. Introduce `be a`. Rewrite using `[hA t (rho a) (be a) (hrho a)]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun be => ?_, hU, fun c _ ε => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.prod_congr rfl (fun a _ => hlet be a)]`. Simplify using `only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Formalism.MainNotions.PlaneGramData.gamDig]`. Expand and normalize the polynomial expressions, which then agree. Establish `hquot : ∀ be : Fin r → ℕ, ((∏ k, (((rho k + p ^ (t + 1) * be k).factorial : ℕ) : ℚ)) / (∏ k, ((rho k).factorial : ℚ) * ((be k).factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ (be k))) = Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be`. Introduce `be`.

Rewrite using `[Finset.prod_congr rfl (fun a _ => hlet be a), Finset.prod_mul_distrib]`. Establish `hne : (∏ k, ((rho k).factorial : ℚ) * ((be k).factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ (be k)) ≠ 0`. Use `Finset.prod_ne_zero_iff.2 fun k _ => ?_` and prove the remaining obligations. Establish `h1 : ((rho k).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Establish `h2 : ((be k).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`.

Establish `h3 : ((p ^ (t + 1)).factorial : ℚ) ≠ 0` using `by exact_mod_cast (Nat.factorial_ne_zero _)`. Conclude with `mul_ne_zero (mul_ne_zero h1 h2) (pow_ne_zero _ h3)`. Rewrite using `[mul_div_cancel_left₀ _ hne]`. Both sides reduce to the same expression. Take `⟨T, q, hT, hq⟩` from `hQ (!ε) c`.

Establish `hex : ∀ j, ∃ o : O, j ∈ T → ((q j : ℚ) : KK O) = algebraMap O (KK O) o`. Introduce `j`. Distinguish the cases in `hj : j ∈ T`. Take `⟨o, ho⟩` from `rat_padicGe_cast hp S (q j) 0 (by simpa using (hT j hj).2)`. Conclude with `⟨o, fun _ => by simpa using ho⟩`.

Conclude with `⟨0, fun h => absurd h hj⟩`. Use `choose o ho using hex`. Take `⟨lam, hsup, hlam⟩` from `binomComb_onFinset (O := O) T o`. Use `⟨lam, fun m hm => (hT m (hsup hm)).1, fun be => ?_⟩` and prove the remaining obligations. Establish `hqb` using `hq be`.

Simplify using `only [hquot] at hqb`. Take `⟨z, hz⟩` from `rat_padicGe_cast hp S _ c hqb`. Establish `hsum : Formalism.MainNotions.PlaneGramData.binomComb (K` using `KK O) lam be = ((∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ) : ℚ) : KK O) := by`. Rewrite using `[hlam be]`. Use `push_cast`.

Conclude with `Finset.sum_congr rfl fun j hj => by rw [ho j hj]`. Establish `heq : ((if ε = true then ((Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be : ℚ) : KK O) else ((Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be : ℚ) : KK O)⁻¹) - Formalism.MainNotions.PlaneGramData.binomComb (K` using `KK O) lam be) = (p : KK O) ^ c * algebraMap O (KK O) z := by`. Rewrite using `[← hz, hsum]`. Apply the tactic sequence `cases ε <;> simp`. Rewrite using `[heq]`.

Conclude with `geQ_vK_pow_mul S c z`.
-/
theorem digit_identity_of_decomposition (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.FactorialUnitDecomposition D) : Formalism.MainNotions.PlaneGramData.adm5 D := by
  intro p O _ _ _ _ hset g r rho hrho
  obtain ⟨⟨S⟩, n', hG⟩ := hset
  have hp := hG.prime
  have h5 := hG.five_le
  have hK : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨hA, hB⟩ := h p hp h5
  rcases g with _ | t
  · have hr : rho = fun _ => 0 := by
      funext a
      have := hrho a
      simpa using this
    subst hr
    simp only [pow_zero, gamDig_one_zero]
    refine ⟨fun be => by simp, fun be => by simp, fun c _ ε => ?_⟩
    obtain ⟨lam, hsup, hlam⟩ := binomComb_onFinset (O := O) ({0} : Finset (Fin r → ℕ)) (fun _ => 1)
    refine ⟨lam, fun m hm => ?_, fun be => ?_⟩
    · have := Finset.mem_singleton.1 (hsup hm)
      subst this
      simp
    · rw [hlam be]
      have : ((if ε = true then ((1 : ℚ) : KK O) else ((1 : ℚ) : KK O)⁻¹) -
          ∑ m ∈ ({0} : Finset (Fin r → ℕ)), algebraMap O (KK O) 1 * ∏ a, (((be a).choose (m a) : ℕ) : KK O)) = 0 := by
        cases ε <;> simp
      rw [this, vK_zero]
      exact geQ_top _
  · obtain ⟨hU, _, hQ⟩ := hB (Fin r) (fun _ => t) rho hrho
    have hlet : ∀ (be : Fin r → ℕ) (a : Fin r), ((rho a + p ^ (t + 1) * be a).factorial : ℚ) =
        (((rho a).factorial : ℚ) * ((be a).factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ (be a)) *
          (cUnit (p ^ (t + 1)) (be a) * dUnit (p ^ (t + 1)) (be a) (rho a)) := by
      intro be a
      rw [hA t (rho a) (be a) (hrho a)]; ring
    refine ⟨fun be => ?_, hU, fun c _ ε => ?_⟩
    · rw [Finset.prod_congr rfl (fun a _ => hlet be a)]
      simp only [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum, Formalism.MainNotions.PlaneGramData.gamDig]
      ring
    · have hquot : ∀ be : Fin r → ℕ,
          ((∏ k, (((rho k + p ^ (t + 1) * be k).factorial : ℕ) : ℚ)) /
            (∏ k, ((rho k).factorial : ℚ) * ((be k).factorial : ℚ) * ((p ^ (t + 1)).factorial : ℚ) ^ (be k))) =
          Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be := by
        intro be
        rw [Finset.prod_congr rfl (fun a _ => hlet be a), Finset.prod_mul_distrib]
        have hne : (∏ k, ((rho k).factorial : ℚ) * ((be k).factorial : ℚ) *
            ((p ^ (t + 1)).factorial : ℚ) ^ (be k)) ≠ 0 := by
          refine Finset.prod_ne_zero_iff.2 fun k _ => ?_
          have h1 : ((rho k).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
          have h2 : ((be k).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
          have h3 : ((p ^ (t + 1)).factorial : ℚ) ≠ 0 := by exact_mod_cast (Nat.factorial_ne_zero _)
          exact mul_ne_zero (mul_ne_zero h1 h2) (pow_ne_zero _ h3)
        rw [mul_div_cancel_left₀ _ hne]
        rfl
      obtain ⟨T, q, hT, hq⟩ := hQ (!ε) c
      have hex : ∀ j, ∃ o : O, j ∈ T → ((q j : ℚ) : KK O) = algebraMap O (KK O) o := by
        intro j
        by_cases hj : j ∈ T
        · obtain ⟨o, ho⟩ := rat_padicGe_cast hp S (q j) 0 (by simpa using (hT j hj).2)
          exact ⟨o, fun _ => by simpa using ho⟩
        · exact ⟨0, fun h => absurd h hj⟩
      choose o ho using hex
      obtain ⟨lam, hsup, hlam⟩ := binomComb_onFinset (O := O) T o
      refine ⟨lam, fun m hm => (hT m (hsup hm)).1, fun be => ?_⟩
      have hqb := hq be
      simp only [hquot] at hqb
      obtain ⟨z, hz⟩ := rat_padicGe_cast hp S _ c hqb
      have hsum : Formalism.MainNotions.PlaneGramData.binomComb (K := KK O) lam be =
          ((∑ j ∈ T, q j * ∏ k, ((be k).choose (j k) : ℚ) : ℚ) : KK O) := by
        rw [hlam be]
        push_cast
        exact Finset.sum_congr rfl fun j hj => by rw [ho j hj]
      have heq : ((if ε = true then ((Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be : ℚ) : KK O)
            else ((Formalism.MainNotions.PlaneGramData.gamDig (p ^ (t + 1)) rho be : ℚ) : KK O)⁻¹) -
          Formalism.MainNotions.PlaneGramData.binomComb (K := KK O) lam be) = (p : KK O) ^ c * algebraMap O (KK O) z := by
        rw [← hz, hsum]
        cases ε <;> simp
      rw [heq]
      exact geQ_vK_pow_mul S c z

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.PlaneGramData

namespace Formalism.MainNotions.G.Joints

/- English proof (translation)
Unfold `atLetter`. Rewrite using `[Finsupp.finsetSum_apply]`. Simplify using `[Finsupp.single_apply]`.
-/
theorem atLetter_apply {r : ℕ} (e : Fin r → ℕ) (a : Fin r) : atLetter () e ((), a) = e a := by
  unfold atLetter
  rw [Finsupp.finsetSum_apply]
  simp [Finsupp.single_apply]

/- English proof (translation)
Unfold `monoL atLetter`. Rewrite using `[monomial_sum_one]`. Conclude with `Finset.prod_congr rfl fun a _ => X_pow_eq_monomial`.
-/
theorem monoL_eq {K : Type*} [Field K] {r : ℕ} (e : Fin r → ℕ) :
    monoL (K := K) e = monomial (atLetter () e) 1 := by
  unfold monoL atLetter
  rw [monomial_sum_one]
  exact Finset.prod_congr rfl fun a _ => X_pow_eq_monomial

/- English proof (translation)
Unfold `monoL`. Rewrite using `[← Finset.prod_mul_distrib]`. Conclude with `Finset.prod_congr rfl fun a _ => (pow_add _ _ _).symm`.
-/
theorem monoL_mul {K : Type*} [Field K] {r : ℕ} (e e' : Fin r → ℕ) :
    monoL (K := K) e * monoL e' = monoL fun a => e a + e' a := by
  unfold monoL
  rw [← Finset.prod_mul_distrib]
  exact Finset.prod_congr rfl fun a _ => (pow_add _ _ _).symm

/- English proof (translation)
Rewrite using `[Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _), Fintype.prod_prod_type]`. Simplify using `[atLetter_apply]`.
-/
theorem atLetter_prod {r : ℕ} (M e : Fin r → ℕ) :
    ((atLetter () M).prod fun k j => (atLetter () e k).choose j) = ∏ a, (e a).choose (M a) := by
  rw [Finsupp.prod_fintype _ _ (fun _ => Nat.choose_zero_right _), Fintype.prod_prod_type]
  simp [atLetter_apply]

/- English proof (translation)
Use extensionality with `⟨⟨⟩, a⟩`. Rewrite using `[Finsupp.tsub_apply]`. Simplify using `only [atLetter_apply]`.
-/
theorem atLetter_sub {r : ℕ} (M e : Fin r → ℕ) :
    atLetter () e - atLetter () M = atLetter () fun a => e a - M a := by
  ext ⟨⟨⟩, a⟩
  rw [Finsupp.tsub_apply]
  simp only [atLetter_apply]

/- English proof (translation)
Rewrite using `[monoL_eq, monoL_eq]`. Unfold `divDer`. Rewrite using `[support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]`. Distinguish the cases in `h : atLetter () M ≤ atLetter () e`. Rewrite using `[if_pos h, atLetter_prod, atLetter_sub, C_mul_monomial, mul_one]`.

Use `push_cast`. Both sides reduce to the same expression. Rewrite using `[if_neg h]`. Rewrite `h` using `[Finsupp.le_def]`. Use `push Not at h`.

Take `⟨⟨⟨⟩, a⟩, ha⟩` from `h`. Rewrite `ha` using `[atLetter_apply, atLetter_apply]`. Establish `h0 : (∏ a, (((e a).choose (M a) : ℕ) : K)) = 0` using `Finset.prod_eq_zero (Finset.mem_univ a) (by rw [Nat.choose_eq_zero_of_lt ha]; simp)`. Rewrite using `[h0, map_zero, zero_mul]`.
-/
theorem divDer_monoL {K : Type*} [Field K] {r : ℕ} (M e : Fin r → ℕ) :
    divDer (atLetter () M) (monoL (K := K) e) =
      C (∏ a, (((e a).choose (M a) : ℕ) : K)) * monoL fun a => e a - M a := by
  classical
  rw [monoL_eq, monoL_eq]
  unfold divDer
  rw [support_monomial, if_neg one_ne_zero, Finset.sum_singleton, coeff_monomial, if_pos rfl, one_mul]
  by_cases h : atLetter () M ≤ atLetter () e
  · rw [if_pos h, atLetter_prod, atLetter_sub, C_mul_monomial, mul_one]
    push_cast
    rfl
  · rw [if_neg h]
    rw [Finsupp.le_def] at h
    push Not at h
    obtain ⟨⟨⟨⟩, a⟩, ha⟩ := h
    rw [atLetter_apply, atLetter_apply] at ha
    have h0 : (∏ a, (((e a).choose (M a) : ℕ) : K)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by rw [Nat.choose_eq_zero_of_lt ha]; simp)
    rw [h0, map_zero, zero_mul]

def derTriple {r : ℕ} (P : ℕ) (M rho l : Fin r → ℕ) : (Fin r → ℕ) × (Fin r → ℕ) × (Fin r → ℕ) :=
  (fun a => (rho a + P * l a - M a) % P, fun a => (rho a + P * l a - M a) / P, l)

/- English proof (translation)
Distinguish the cases in `h : ∀ a, l a ≤ be a`. Rewrite using `[mul_assoc, monoL_mul]`. Use `congr 2`. Use function extensionality and compare the values at `a`. Use `show (rho a + P * l a - M a) % P + P * (be a - l a + (rho a + P * l a - M a) / P) = _`.

Take `⟨k, hk⟩` from `Nat.exists_eq_add_of_le (h a)`. Establish `h1` using `Nat.mod_add_div (rho a + P * l a - M a) P`. Establish `h2` using `hl a`. Rewrite using `[hk, Nat.add_sub_cancel_left, mul_add, mul_add]`. Use linear arithmetic over natural numbers and integers.

Use `push Not at h`. Take `⟨a, ha⟩` from `h`. Establish `h0 : (∏ a, (((be a).choose (l a) : ℕ) : K)) = 0` using `Finset.prod_eq_zero (Finset.mem_univ a) (by rw [Nat.choose_eq_zero_of_lt ha]; simp)`. Rewrite using `[h0, mul_zero, map_zero, zero_mul, zero_mul, zero_mul]`.
-/
theorem der_term {K : Type*} [Field K] {r : ℕ} (P : ℕ) (M rho l be : Fin r → ℕ)
    (hl : ∀ a, M a ≤ rho a + P * l a) (x : K) :
    C (x * ∏ a, (((be a).choose (l a) : ℕ) : K)) * monoL (K := K) (derTriple P M rho l).1 *
        monoL (K := K) (fun a => P * (be a - l a + (derTriple P M rho l).2.1 a)) =
      C (x * ∏ a, (((be a).choose (l a) : ℕ) : K)) * monoL fun a => rho a + P * be a - M a := by
  by_cases h : ∀ a, l a ≤ be a
  · rw [mul_assoc, monoL_mul]
    congr 2
    funext a
    show (rho a + P * l a - M a) % P + P * (be a - l a + (rho a + P * l a - M a) / P) = _
    obtain ⟨k, hk⟩ := Nat.exists_eq_add_of_le (h a)
    have h1 := Nat.mod_add_div (rho a + P * l a - M a) P
    have h2 := hl a
    rw [hk, Nat.add_sub_cancel_left, mul_add, mul_add]
    omega
  · push Not at h
    obtain ⟨a, ha⟩ := h
    have h0 : (∏ a, (((be a).choose (l a) : ℕ) : K)) = 0 :=
      Finset.prod_eq_zero (Finset.mem_univ a) (by rw [Nat.choose_eq_zero_of_lt ha]; simp)
    rw [h0, mul_zero, map_zero, zero_mul, zero_mul, zero_mul]

/- English proof (translation)
Introduce `g r M rho hrho c _hc`. Take `⟨T, γ, hT1, hT2, hT3⟩` from `h p hp h5 g (Fin r) rho M hrho c`. Use `⟨T.image (derTriple (p ^ g) M rho), fun t => ((γ t.2.2 : ℤ) : O), ?_, ?_⟩` and prove the remaining obligations. Introduce `t ht`. Take `⟨l, hl, rfl⟩` from `Finset.mem_image.1 ht`.

Conclude with `⟨fun a => Nat.mod_lt _ (pow_pos hp.pos g), hT1 l hl⟩`. Introduce `be mo`. Establish `hinj : Set.InjOn (derTriple (p ^ g) M rho) (T : Set (Fin r → ℕ))`. Introduce `l _ l' _ hll`. Conclude with `congrArg (fun t => t.2.2) hll`.

Rewrite using `[Finset.sum_image hinj]`. Establish `e2 : (∑ l ∈ T, C (algebraMap O (KK O) ((γ (derTriple (p ^ g) M rho l).2.2 : ℤ) : O) * ∏ a, (((be a).choose ((derTriple (p ^ g) M rho l).2.2 a) : ℕ) : KK O)) * monoL (K` using `KK O) (derTriple (p ^ g) M rho l).1 * monoL (K := KK O) (fun a => p ^ g * (be a - (derTriple (p ^ g) M rho l).2.2 a + (derTriple (p ^ g) M rho l).2.1 a))) = C (∑ l ∈ T, algebraMap O (KK O) ((γ l : ℤ) : O) * ∏ a, (((be a).choose (l a) : ℕ) : KK O)) * monoL fun a => rho a + p ^ g * …`. Rewrite using `[map_sum, Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun l hl => der_term (p ^ g) M rho l be (hT2 l hl) _`. Rewrite using `[e2, divDer_monoL, ← sub_mul, ← map_sub]`.

Take `⟨z, hz⟩` from `hT3 be`. Establish `e3 : (∏ a, (((rho a + p ^ g * be a).choose (M a) : ℕ) : KK O)) - ∑ l ∈ T, algebraMap O (KK O) ((γ l : ℤ) : O) * ∏ a, (((be a).choose (l a) : ℕ) : KK O) = (p : KK O) ^ c * algebraMap O (KK O) ((z : ℤ) : O)`. Use `congrArg (fun n : ℤ => (n : KK O)) hz` as an intermediate fact. Move the coercions through the operations in `at this`. Simplify using `using this`.

Rewrite using `[e3, coeff_C_mul, monoL_eq, coeff_monomial]`. Use `split_ifs`. Rewrite using `[mul_one]`. Conclude with `hvk c _`. Use `hvk c 0` as an intermediate fact.

Simplify using `using this`.
-/
theorem derivation_valuation_at_prime (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.DerivativeDigitExpansion D) (p : ℕ) (hp : p.Prime) (h5 : 5 ≤ p)
    (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
    (hvk : ∀ (c : ℕ) (o : O), geQ (vK p ((p : KK O) ^ c * algebraMap O (KK O) o)) (c : ℝ)) :
    DerivativeCongruenceAtRing p O := by
  intro g r M rho hrho c _hc
  obtain ⟨T, γ, hT1, hT2, hT3⟩ := h p hp h5 g (Fin r) rho M hrho c
  refine ⟨T.image (derTriple (p ^ g) M rho), fun t => ((γ t.2.2 : ℤ) : O), ?_, ?_⟩
  · intro t ht
    obtain ⟨l, hl, rfl⟩ := Finset.mem_image.1 ht
    exact ⟨fun a => Nat.mod_lt _ (pow_pos hp.pos g), hT1 l hl⟩
  · intro be mo
    have hinj : Set.InjOn (derTriple (p ^ g) M rho) (T : Set (Fin r → ℕ)) := by
      intro l _ l' _ hll
      exact congrArg (fun t => t.2.2) hll
    rw [Finset.sum_image hinj]
    have e2 : (∑ l ∈ T, C (algebraMap O (KK O) ((γ (derTriple (p ^ g) M rho l).2.2 : ℤ) : O) *
          ∏ a, (((be a).choose ((derTriple (p ^ g) M rho l).2.2 a) : ℕ) : KK O)) *
            monoL (K := KK O) (derTriple (p ^ g) M rho l).1 *
            monoL (K := KK O) (fun a => p ^ g * (be a - (derTriple (p ^ g) M rho l).2.2 a +
              (derTriple (p ^ g) M rho l).2.1 a))) =
        C (∑ l ∈ T, algebraMap O (KK O) ((γ l : ℤ) : O) * ∏ a, (((be a).choose (l a) : ℕ) : KK O)) *
          monoL fun a => rho a + p ^ g * be a - M a := by
      rw [map_sum, Finset.sum_mul]
      exact Finset.sum_congr rfl fun l hl => der_term (p ^ g) M rho l be (hT2 l hl) _
    rw [e2, divDer_monoL, ← sub_mul, ← map_sub]
    obtain ⟨z, hz⟩ := hT3 be
    have e3 : (∏ a, (((rho a + p ^ g * be a).choose (M a) : ℕ) : KK O)) -
        ∑ l ∈ T, algebraMap O (KK O) ((γ l : ℤ) : O) * ∏ a, (((be a).choose (l a) : ℕ) : KK O) =
        (p : KK O) ^ c * algebraMap O (KK O) ((z : ℤ) : O) := by
      have := congrArg (fun n : ℤ => (n : KK O)) hz
      push_cast at this
      simpa using this
    rw [e3, coeff_C_mul, monoL_eq, coeff_monomial]
    split_ifs
    · rw [mul_one]; exact hvk c _
    · have := hvk c 0
      simpa using this

/- English proof (translation)
Introduce `p O _ _ _ _ hS`. Take `⟨⟨S⟩, n', hR⟩` from `hS`. Conclude with `derivation_valuation_at_prime D h p hR.prime hR.five_le O (hvk p O S)`.
-/
theorem derivation_of_valuation_bound (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.DerivativeDigitExpansion D)
    (hvk : ∀ (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O], UniformizedDVR p O →
      ∀ (c : ℕ) (o : O), geQ (vK p ((p : KK O) ^ c * algebraMap O (KK O) o)) (c : ℝ)) :
    Formalism.MainNotions.PlaneGramData.adm6 D := by
  intro p O _ _ _ _ hS
  obtain ⟨⟨S⟩, n', hR⟩ := hS
  exact derivation_valuation_at_prime D h p hR.prime hR.five_le O (hvk p O S)

/- English proof (translation)
The claim follows from `derivation_of_valuation_bound D h fun _ _ _ _ _ S c o => geQ_vK_pow_mul S c o`.
-/
theorem derivation_of_lattice_index (D : Formalism.BasicNotions.D7) (h : Formalism.MainNotions.CovariantDegrees.DerivativeDigitExpansion D) : Formalism.MainNotions.PlaneGramData.adm6 D :=
  derivation_of_valuation_bound D h fun _ _ _ _ _ S c o => geQ_vK_pow_mul S c o

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

/- English proof (translation)
Establish `h0 : a.1 < a'.1` using `h`. Establish `h1 : a.1 + 1 < n` using `by have := a'.2; omega`. Establish `h2 : (⟨a.1 + 1, h1⟩ : Fin n) ≤ a'` using `by show a.1 + 1 ≤ a'.1`. Use linear arithmetic over natural numbers and integers. Conclude with `(hd h2).trans (hs.2.1 a h1)`.
-/
theorem strip_lt {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (hs : HStrip nu mu b) (hd : Dominant mu) {a a' : Fin n}
    (h : a < a') : mu a' ≤ nu a := by
  have h0 : a.1 < a'.1 := h
  have h1 : a.1 + 1 < n := by have := a'.2; omega
  have h2 : (⟨a.1 + 1, h1⟩ : Fin n) ≤ a' := by
    show a.1 + 1 ≤ a'.1
    omega
  exact (hd h2).trans (hs.2.1 a h1)

/- English proof (translation)
Unfold `colH`. Rewrite using `[← Finset.card_union_of_disjoint]`. Use `congr 1`. Use extensionality with `a`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]`.

Use `h a` as an intermediate fact. Prove the components needed by the constructor for the conclusion. Introduce `h1`. Distinguish the cases in `h2 : c ≤ nu a`. Conclude with `Or.inl h2`.

Conclude with `Or.inr ⟨by omega, h1⟩`. Introduce and unpack `(h1 | h1)`. Use linear arithmetic over natural numbers and integers. Conclude with `h1.2`. Rewrite using `[Finset.disjoint_filter]`.

Introduce `a _ h1 h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem colH_strip {n : ℕ} {nu mu : Fin n → ℤ} (h : ∀ a, nu a ≤ mu a) (c : ℤ) :
    colH mu c = colH nu c + (univ.filter fun a => nu a < c ∧ c ≤ mu a).card := by
  unfold colH
  rw [← Finset.card_union_of_disjoint]
  · congr 1
    ext a
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union]
    have := h a
    constructor
    · intro h1
      by_cases h2 : c ≤ nu a
      · exact Or.inl h2
      · exact Or.inr ⟨by omega, h1⟩
    · rintro (h1 | h1)
      · omega
      · exact h1.2
  · rw [Finset.disjoint_filter]
    intro a _ h1 h2
    omega

/- English proof (translation)
Rewrite using `[Finset.card_le_one]`. Introduce `a ha a' ha'`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'`. Break down `lt_trichotomy a a' with h | h | h` into its components or cases. Use `strip_lt hs hd h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h`. Use `strip_lt hs hd h` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
theorem strip_le_one {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (hs : HStrip nu mu b) (hd : Dominant mu) (c : ℤ) :
    (univ.filter fun a => nu a < c ∧ c ≤ mu a).card ≤ 1 := by
  rw [Finset.card_le_one]
  intro a ha a' ha'
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha ha'
  rcases lt_trichotomy a a' with h | h | h
  · have := strip_lt hs hd h; omega
  · exact h
  · have := strip_lt hs hd h; omega

/- English proof (translation)
Rewrite using `[colH_strip h c]`. Prove the components needed by the constructor for the conclusion. Introduce `hne`. Establish `h0 : (univ.filter fun a => nu a < c ∧ c ≤ mu a).card ≠ 0` using `by omega`. Take `⟨a, ha⟩` from `Finset.card_pos.1 (Nat.pos_of_ne_zero h0)`.

Conclude with `⟨a, (Finset.mem_filter.1 ha).2⟩`. Introduce and unpack `⟨a, ha⟩`. Establish `h0 : 0 < (univ.filter fun a => nu a < c ∧ c ≤ mu a).card` using `Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩`. Use linear arithmetic over natural numbers and integers.
-/
theorem colH_ne_iff {n : ℕ} {nu mu : Fin n → ℤ} (h : ∀ a, nu a ≤ mu a) (c : ℤ) :
    colH nu c ≠ colH mu c ↔ ∃ a, nu a < c ∧ c ≤ mu a := by
  rw [colH_strip h c]
  constructor
  · intro hne
    have h0 : (univ.filter fun a => nu a < c ∧ c ≤ mu a).card ≠ 0 := by omega
    obtain ⟨a, ha⟩ := Finset.card_pos.1 (Nat.pos_of_ne_zero h0)
    exact ⟨a, (Finset.mem_filter.1 ha).2⟩
  · rintro ⟨a, ha⟩
    have h0 : 0 < (univ.filter fun a => nu a < c ∧ c ≤ mu a).card :=
      Finset.card_pos.2 ⟨a, Finset.mem_filter.2 ⟨Finset.mem_univ _, ha⟩⟩
    omega

/- English proof (translation)
Establish `hEq : Rg.filter q = univ.biUnion fun a => Finset.Ioc (nu a) (mu a)`. Use extensionality with `c`. Simplify using `only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_Ioc]`. Rewrite using `[hq c]`. Prove the components needed by the constructor for the conclusion.

Conclude with `fun h => h.2`. Introduce and unpack `⟨a, h1, h2⟩`. Conclude with `⟨hR a c h1 h2, a, h1, h2⟩`. Rewrite using `[hEq, Finset.card_biUnion]`. Simplify using `only [Int.card_Ioc]`.

Establish `h3 : ((∑ a, (mu a - nu a).toNat : ℕ) : ℤ) = b`. Rewrite using `[← hs.2.2]`. Use `push_cast`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Use `hs.1 a` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Conclude with `h3` after adjusting the coercions. Introduce `a _ a' _ hne show Disjoint (Finset.Ioc (nu a) (mu a)) (Finset.Ioc (nu a') (mu a'))`. Rewrite using `[Finset.disjoint_left]`. Introduce `c h1 h2`.

Rewrite `h1`, `h2` using `[Finset.mem_Ioc]`. Break down `lt_or_gt_of_ne hne with h | h` into its components or cases. Use `strip_lt hs hd h` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Use `strip_lt hs hd h` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem strip_count {n : ℕ} {nu mu : Fin n → ℤ} {b : ℕ} (hs : HStrip nu mu b) (hd : Dominant mu) (Rg : Finset ℤ)
    (hR : ∀ a c, nu a < c → c ≤ mu a → c ∈ Rg) (q : ℤ → Prop) [DecidablePred q]
    (hq : ∀ c, q c ↔ ∃ a, nu a < c ∧ c ≤ mu a) :
    (Rg.filter q).card = b := by
  have hEq : Rg.filter q = univ.biUnion fun a => Finset.Ioc (nu a) (mu a) := by
    ext c
    simp only [Finset.mem_filter, Finset.mem_biUnion, Finset.mem_univ, true_and, Finset.mem_Ioc]
    rw [hq c]
    constructor
    · exact fun h => h.2
    · rintro ⟨a, h1, h2⟩
      exact ⟨hR a c h1 h2, a, h1, h2⟩
  rw [hEq, Finset.card_biUnion]
  · simp only [Int.card_Ioc]
    have h3 : ((∑ a, (mu a - nu a).toNat : ℕ) : ℤ) = b := by
      rw [← hs.2.2]
      push_cast
      refine Finset.sum_congr rfl fun a _ => ?_
      have := hs.1 a
      omega
    exact_mod_cast h3
  · intro a _ a' _ hne
    show Disjoint (Finset.Ioc (nu a) (mu a)) (Finset.Ioc (nu a') (mu a'))
    rw [Finset.disjoint_left]
    intro c h1 h2
    rw [Finset.mem_Ioc] at h1 h2
    rcases lt_or_gt_of_ne hne with h | h
    · have := strip_lt hs hd h; omega
    · have := strip_lt hs hd h; omega

/- English proof (translation)
The claim follows from `|mu i m| ≤ ∑ i, ∑ m, |mu i m| := calc |mu i m| ≤ ∑ m, |mu i m| := Finset.single_le_sum (f := fun m => |mu i m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m) _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ m, |mu i m|) (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset …`.
-/
theorem abs_le_alt {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (i : Fin (N + 1)) (m : Fin n) :
    |mu i m| ≤ ∑ i, ∑ m, |mu i m| :=
  calc |mu i m| ≤ ∑ m, |mu i m| :=
        Finset.single_le_sum (f := fun m => |mu i m|) (fun _ _ => abs_nonneg _) (Finset.mem_univ m)
    _ ≤ _ := Finset.single_le_sum (f := fun i => ∑ m, |mu i m|)
        (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

/- English proof (translation)
Establish `t1` using `abs_le_alt mu i1 a`. Establish `t2` using `abs_le_alt mu i2 a'`. Establish `t3` using `neg_abs_le (mu i1 a)`. Establish `t4` using `le_abs_self (mu i2 a')`. Use `show c ∈ Finset.Icc (-(∑ i, ∑ m, |mu i m|)) (∑ i, ∑ m, |mu i m|)`.

Rewrite using `[Finset.mem_Icc]`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem mem_colRange {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) {i1 i2 : Fin (N + 1)} {a a' : Fin n} {c : ℤ}
    (h1 : mu i1 a < c) (h2 : c ≤ mu i2 a') : c ∈ colRange mu := by
  have t1 := abs_le_alt mu i1 a
  have t2 := abs_le_alt mu i2 a'
  have t3 := neg_abs_le (mu i1 a)
  have t4 := le_abs_self (mu i2 a')
  show c ∈ Finset.Icc (-(∑ i, ∑ m, |mu i m|)) (∑ i, ∑ m, |mu i m|)
  rw [Finset.mem_Icc]
  constructor <;> linarith

/- English proof (translation)
Establish `hstep` using `P.step i`. Distinguish the cases in `hv : LL.vec i = true`. Rewrite `hstep` using `[if_pos hv]`. Conclude with `⟨_, _, hstep, fun c => colH_ne_iff hstep.1 c⟩`. Rewrite `hstep` using `[if_neg hv]`.

Use `⟨_, _, hstep, fun c => ?_⟩` and prove the remaining obligations. Rewrite using `[← colH_ne_iff hstep.1 c]`. Conclude with `ne_comm`.
-/
theorem path_step {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (i : Fin N) :
    ∃ i1 i2 : Fin (N + 1), HStrip (P.mu i1) (P.mu i2) (d i) ∧
      ∀ c, IsUsed P.mu c i ↔ ∃ a, P.mu i1 a < c ∧ c ≤ P.mu i2 a := by
  have hstep := P.step i
  by_cases hv : LL.vec i = true
  · rw [if_pos hv] at hstep
    exact ⟨_, _, hstep, fun c => colH_ne_iff hstep.1 c⟩
  · rw [if_neg hv] at hstep
    refine ⟨_, _, hstep, fun c => ?_⟩
    rw [← colH_ne_iff hstep.1 c]
    exact ne_comm

def HomD {R : Type*} [CommRing R] {N n : ℕ} (de : Fin N → ℕ) (F : MvPolynomial (Fin N × Fin n) R) : Prop :=
  ∀ m ∈ F.support, ∀ i, multideg m i = de i

section Hom

variable {R : Type*} [CommRing R] {N n : ℕ} {de : Fin N → ℕ} {F G : MvPolynomial (Fin N × Fin n) R}

/- English proof (translation)
Introduce `m hm`. Simplify using `at hm`.
-/
theorem HomD.zero : HomD de (0 : MvPolynomial (Fin N × Fin n) R) := by
  intro m hm
  simp at hm

/- English proof (translation)
Introduce `m hm`. Break down `Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h` into its components or cases. Conclude with `hF m h`. Conclude with `hG m h`.
-/
theorem HomD.add (hF : HomD de F) (hG : HomD de G) : HomD de (F + G) := by
  intro m hm
  rcases Finset.mem_union.1 (MvPolynomial.support_add hm) with h | h
  · exact hF m h
  · exact hG m h

/- English proof (translation)
Introduce `m hm`. Rewrite `hm` using `[MvPolynomial.support_neg]`. Conclude with `hF m hm`.
-/
theorem HomD.neg (hF : HomD de F) : HomD de (-F) := by
  intro m hm
  rw [MvPolynomial.support_neg] at hm
  exact hF m hm

/- English proof (translation)
The claim follows from `Finset.sum_induction f (HomD de) (fun _ _ => HomD.add) HomD.zero h`.
-/
theorem HomD.sum {α : Type*} (s : Finset α) (f : α → MvPolynomial (Fin N × Fin n) R)
    (h : ∀ a ∈ s, HomD de (f a)) : HomD de (∑ a ∈ s, f a) :=
  Finset.sum_induction f (HomD de) (fun _ _ => HomD.add) HomD.zero h

/- English proof (translation)
Break down `neg_one_pow_eq_or (MvPolynomial (Fin N × Fin n) R) k with h | h` into its components or cases. Rewrite using `[h, one_mul]`. Conclude with `hF`. Rewrite using `[h, neg_one_mul]`. Conclude with `hF.neg`.
-/
theorem HomD.sign (k : ℕ) (hF : HomD de F) : HomD de ((-1) ^ k * F) := by
  rcases neg_one_pow_eq_or (MvPolynomial (Fin N × Fin n) R) k with h | h
  · rw [h, one_mul]; exact hF
  · rw [h, neg_one_mul]; exact hF.neg

/- English proof (translation)
Unfold `multideg`. Simplify using `only [Finsupp.add_apply, Finset.sum_add_distrib]`. Use `congr 1`. Distinguish the cases in `h : i = j0`. Substitute `h` using the available equality.

Simplify using `[Finsupp.single_apply]`. Simplify using `[h]`.
-/
theorem multideg_single_add (j0 : Fin N) (a : Fin n) (m' : Fin N × Fin n →₀ ℕ) (i : Fin N) :
    multideg (Finsupp.single (j0, a) 1 + m') i = (if i = j0 then 1 else 0) + multideg m' i := by
  unfold multideg
  simp only [Finsupp.add_apply, Finset.sum_add_distrib]
  congr 1
  by_cases h : i = j0
  · subst h
    simp [Finsupp.single_apply]
  · simp [h]

/- English proof (translation)
Introduce `m hm i`. Rewrite `hm` using `[MvPolynomial.support_X_mul]`. Take `⟨m', hm', rfl⟩` from `Finset.mem_map.1 hm`. Simplify using `only [addLeftEmbedding_apply]`. Rewrite using `[multideg_single_add, hF m' hm' i]`.
-/
theorem HomD.X_mul (j0 : Fin N) (a : Fin n) (hF : HomD de F) :
    HomD (fun i => (if i = j0 then 1 else 0) + de i) (X (j0, a) * F) := by
  intro m hm i
  rw [MvPolynomial.support_X_mul] at hm
  obtain ⟨m', hm', rfl⟩ := Finset.mem_map.1 hm
  simp only [addLeftEmbedding_apply]
  rw [multideg_single_add, hF m' hm' i]

/- English proof (translation)
Unfold `wedgeR`. Use `HomD.sum _ _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `HomD.sign _ (HomD.X_mul j0 m (hK _))`.
-/
theorem wedgeR_hom (j0 : Fin N) (K : Finset (Fin n) → MvPolynomial (Fin N × Fin n) R) (hK : ∀ J, HomD de (K J))
    (J : Finset (Fin n)) : HomD (fun i => (if i = j0 then 1 else 0) + de i) (wedgeR (letVec R j0) K J) := by
  unfold wedgeR
  refine HomD.sum _ _ fun m _ => ?_
  rw [mul_assoc]
  exact HomD.sign _ (HomD.X_mul j0 m (hK _))

/- English proof (translation)
Unfold `contrR`. Use `HomD.sum _ _ fun m _ => ?_` and prove the remaining obligations. Rewrite using `[mul_assoc]`. Conclude with `HomD.sign _ (HomD.X_mul j0 m (hK _))`.
-/
theorem contrR_hom (j0 : Fin N) (K : Finset (Fin n) → MvPolynomial (Fin N × Fin n) R) (hK : ∀ J, HomD de (K J))
    (J : Finset (Fin n)) : HomD (fun i => (if i = j0 then 1 else 0) + de i) (contrR (letVec R j0) K J) := by
  unfold contrR
  refine HomD.sum _ _ fun m _ => ?_
  rw [mul_assoc]
  exact HomD.sign _ (HomD.X_mul j0 m (hK _))

/- English proof (translation)
Unfold `colStep`. Use `split_ifs`. Conclude with `wedgeR_hom j0 K hK J`. Conclude with `contrR_hom j0 K hK J`. Conclude with `contrR_hom j0 K hK J`.

Conclude with `wedgeR_hom j0 K hK J`. Use linear arithmetic over natural numbers and integers.
-/
theorem colStep_hom (c : ℤ) (hP hN : ℕ) (hne : hP ≠ hN) (j0 : Fin N)
    (K : Finset (Fin n) → MvPolynomial (Fin N × Fin n) R) (hK : ∀ J, HomD de (K J)) (J : Finset (Fin n)) :
    HomD (fun i => (if i = j0 then 1 else 0) + de i) (colStep c hP hN (letVec R j0) K J) := by
  unfold colStep
  split_ifs
  · exact wedgeR_hom j0 K hK J
  · exact contrR_hom j0 K hK J
  · exact contrR_hom j0 K hK J
  · exact wedgeR_hom j0 K hK J
  · omega

/- English proof (translation)
Unfold `colStep`. Simplify using the standard rewrite rules.
-/
theorem colStep_same (c : ℤ) (h : ℕ) {P : Type*} [CommRing P] (x : Fin n → P) (K : Finset (Fin n) → P) :
    colStep c h h x K = K := by
  unfold colStep
  simp

end Hom

/- English proof (translation)
Rewrite using `[Kcol, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem Kcol_succ (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) (j : ℕ) (h : j < N) :
    Kcol R mu c (j + 1) =
      colStep c (colH (mu (⟨j, h⟩ : Fin N).castSucc) c) (colH (mu (⟨j, h⟩ : Fin N).succ) c) (letVec R ⟨j, h⟩)
        (Kcol R mu c j) := by
  rw [Kcol, dif_pos h]
  rfl

/- English proof (translation)
Introduce `j`. Proceed by induction on `j with`. Consider the case `zero`. Introduce `_ J m hm i`. Establish `hm0 : m = 0`.

Assume the negation of the conclusion as `hne`. Establish `hm' : m ∈ (extOne J : MvPolynomial (Fin N × Fin n) R).support` using `hm`. Unfold `extOne at hm'`. Use `split_ifs at hm' with h`. Apply `(MvPolynomial.mem_support_iff.1 hm')` to reduce the goal to its premises.

Rewrite using `[MvPolynomial.coeff_one, if_neg (Ne.symm hne)]`. Simplify using `at hm'`. Substitute `hm0` using the available equality. Simplify using `[multideg]`. Consider the case `succ j ih`.

Introduce `hj J`. Establish `hlt : j < N` using `hj`. Rewrite using `[Kcol_succ R mu c j hlt]`. Establish `ih'` using `ih (by omega)`. Distinguish the cases in `hu : IsUsed mu c ⟨j, hlt⟩`.

Establish `hde : (fun i : Fin N => if i.val < j + 1 ∧ IsUsed mu c i then 1 else 0) = fun i => (if i = (⟨j, hlt⟩ : Fin N) then 1 else 0) + (if i.val < j ∧ IsUsed mu c i then 1 else 0)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = ⟨j, hlt⟩`. Substitute `hi` using the available equality. Simplify using `[hu]`.

Establish `h1 : i.val ≠ j` using `fun h => hi (Fin.ext h)`. Establish `h2 : i.val < j + 1 ↔ i.val < j` using `by omega`. Simplify using `[hi, h2]`. Rewrite using `[hde]`. Conclude with `colStep_hom c _ _ hu ⟨j, hlt⟩ _ ih' J`.

Establish `hsame : colH (mu (⟨j, hlt⟩ : Fin N).castSucc) c = colH (mu (⟨j, hlt⟩ : Fin N).succ) c` using `not_not.1 hu`. Rewrite using `[hsame, colStep_same]`. Establish `hde : (fun i : Fin N => if i.val < j + 1 ∧ IsUsed mu c i then 1 else 0) = fun i => (if i.val < j ∧ IsUsed mu c i then 1 else 0)`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = ⟨j, hlt⟩`.

Substitute `hi` using the available equality. Simplify using `[hu]`. Establish `h1 : i.val ≠ j` using `fun h => hi (Fin.ext h)`. Establish `h2 : i.val < j + 1 ↔ i.val < j` using `by omega`. Simplify using `[h2]`.

Rewrite using `[hde]`. Conclude with `ih' J`.
-/
theorem Kcol_hom (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ) :
    ∀ j, j ≤ N → ∀ J, HomD (fun i : Fin N => if i.val < j ∧ IsUsed mu c i then 1 else 0) (Kcol R mu c j J) := by
  intro j
  induction j with
  | zero =>
    intro _ J m hm i
    have hm0 : m = 0 := by
      by_contra hne
      have hm' : m ∈ (extOne J : MvPolynomial (Fin N × Fin n) R).support := hm
      unfold extOne at hm'
      split_ifs at hm' with h
      · apply (MvPolynomial.mem_support_iff.1 hm')
        rw [MvPolynomial.coeff_one, if_neg (Ne.symm hne)]
      · simp at hm'
    subst hm0
    simp [multideg]
  | succ j ih =>
    intro hj J
    have hlt : j < N := hj
    rw [Kcol_succ R mu c j hlt]
    have ih' := ih (by omega)
    by_cases hu : IsUsed mu c ⟨j, hlt⟩
    · have hde : (fun i : Fin N => if i.val < j + 1 ∧ IsUsed mu c i then 1 else 0) =
          fun i => (if i = (⟨j, hlt⟩ : Fin N) then 1 else 0) + (if i.val < j ∧ IsUsed mu c i then 1 else 0) := by
        funext i
        by_cases hi : i = ⟨j, hlt⟩
        · subst hi
          simp [hu]
        · have h1 : i.val ≠ j := fun h => hi (Fin.ext h)
          have h2 : i.val < j + 1 ↔ i.val < j := by omega
          simp [hi, h2]
      rw [hde]
      exact colStep_hom c _ _ hu ⟨j, hlt⟩ _ ih' J
    · have hsame : colH (mu (⟨j, hlt⟩ : Fin N).castSucc) c = colH (mu (⟨j, hlt⟩ : Fin N).succ) c := not_not.1 hu
      rw [hsame, colStep_same]
      have hde : (fun i : Fin N => if i.val < j + 1 ∧ IsUsed mu c i then 1 else 0) =
          fun i => (if i.val < j ∧ IsUsed mu c i then 1 else 0) := by
        funext i
        by_cases hi : i = ⟨j, hlt⟩
        · subst hi
          simp [hu]
        · have h1 : i.val ≠ j := fun h => hi (Fin.ext h)
          have h2 : i.val < j + 1 ↔ i.val < j := by omega
          simp [h2]
      rw [hde]
      exact ih' J

/- English proof (translation)
Introduce `m hm`. Establish `h` using `Kcol_hom R mu c N le_rfl Jc m hm i`. Rewrite using `[h]`. Simplify using `[i.2]`.
-/
theorem col_clause1 (R : Type*) [CommRing R] {N n : ℕ} (mu : Fin (N + 1) → Fin n → ℤ) (c : ℤ)
    (Jc : Finset (Fin n)) (i : Fin N) : ∀ m ∈ (Kcol R mu c N Jc).support,
      multideg m i = if IsUsed mu c i then 1 else 0 := by
  intro m hm
  have h := Kcol_hom R mu c N le_rfl Jc m hm i
  rw [h]
  simp [i.2]

/- English proof (translation)
Take `⟨i1, i2, hs, hu⟩` from `path_step P i`. Conclude with `strip_count hs (P.dom i2) (colRange P.mu) (fun a c h1 h2 => mem_colRange P.mu h1 h2) _ hu`.
-/
theorem col_clause2 {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (i : Fin N) :
    ((colRange P.mu).filter fun c => IsUsed P.mu c i).card = d i := by
  obtain ⟨i1, i2, hs, hu⟩ := path_step P i
  exact strip_count hs (P.dom i2) (colRange P.mu) (fun a c h1 h2 => mem_colRange P.mu h1 h2) _ hu

/- English proof (translation)
Take `⟨i1, i2, _, hu⟩` from `path_step P i`. Take `⟨a, h1, h2⟩` from `(hu c).1 h`. Conclude with `mem_colRange P.mu h1 h2`.
-/
theorem col_clause3 {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (c : ℤ) (i : Fin N)
    (h : IsUsed P.mu c i) : c ∈ colRange P.mu := by
  obtain ⟨i1, i2, _, hu⟩ := path_step P i
  obtain ⟨a, h1, h2⟩ := (hu c).1 h
  exact mem_colRange P.mu h1 h2

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `hk`. Establish `h0 : (⟨0, hk⟩ : Fin (N + 1)) = 0` using `rfl`.

Rewrite using `[h0, P.zero]`. Establish `h1 : colH (0 : Fin r → ℤ) c = 0`. Unfold `colH`. Rewrite using `[Finset.card_eq_zero, Finset.filter_eq_empty_iff]`. Introduce `m _`.

Simplify using `only [Pi.zero_apply]`. Use linear arithmetic over natural numbers and integers. Use linear arithmetic over natural numbers and integers. Consider the case `succ k ih`. Introduce `hk`.

Establish `hlt : k < N` using `by omega`. Establish `ih'` using `ih (by omega)`. Establish `hsub : (univ.filter fun j : Fin N => j.val < k ∧ LL.vec j = true ∧ IsUsed P.mu c j) ⊆ (univ.filter fun j : Fin N => j.val < k + 1 ∧ LL.vec j = true ∧ IsUsed P.mu c j)`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢`.

Conclude with `⟨by omega, hj.2⟩`. Establish `hmono` using `Finset.card_le_card hsub`. Establish `hstep` using `P.step ⟨k, hlt⟩`. Establish `e1 : (⟨k, by omega⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).castSucc` using `rfl`. Establish `e2 : (⟨k + 1, hk⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).succ` using `rfl`.

Rewrite using `[e2]`. Rewrite `ih'` using `[e1]`. Distinguish the cases in `hv : LL.vec ⟨k, hlt⟩ = true`. Rewrite `hstep` using `[if_pos hv]`. Establish `h1` using `colH_strip hstep.1 c`.

Establish `h2` using `strip_le_one hstep (P.dom _) c`. Distinguish the cases in `hu : IsUsed P.mu c ⟨k, hlt⟩`. Establish `hss` using `(Finset.ssubset_iff_of_subset hsub).2 ⟨⟨k, hlt⟩, by simp [hv, hu], by simp⟩`. Use `Finset.card_lt_card hss` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `h3 : colH (P.mu (⟨k, hlt⟩ : Fin N).castSucc) c = colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c` using `not_not.1 hu`. Use linear arithmetic over natural numbers and integers. Rewrite `hstep` using `[if_neg hv]`. Establish `h1` using `colH_strip hstep.1 c`. Use linear arithmetic over natural numbers and integers.
-/
theorem column_height_le_used_count {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (c : ℤ)
    (hc : 1 ≤ c) : ∀ k (hk : k < N + 1), colH (P.mu ⟨k, hk⟩) c ≤
      (Finset.univ.filter fun j : Fin N => j.val < k ∧ LL.vec j = true ∧ IsUsed P.mu c j).card := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : (⟨0, hk⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]
    have h1 : colH (0 : Fin r → ℤ) c = 0 := by
      unfold colH
      rw [Finset.card_eq_zero, Finset.filter_eq_empty_iff]
      intro m _
      simp only [Pi.zero_apply]
      omega
    omega
  | succ k ih =>
    intro hk
    have hlt : k < N := by omega
    have ih' := ih (by omega)
    have hsub : (univ.filter fun j : Fin N => j.val < k ∧ LL.vec j = true ∧ IsUsed P.mu c j) ⊆
        (univ.filter fun j : Fin N => j.val < k + 1 ∧ LL.vec j = true ∧ IsUsed P.mu c j) := by
      intro j hj
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj ⊢
      exact ⟨by omega, hj.2⟩
    have hmono := Finset.card_le_card hsub
    have hstep := P.step ⟨k, hlt⟩
    have e1 : (⟨k, by omega⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).castSucc := rfl
    have e2 : (⟨k + 1, hk⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).succ := rfl
    rw [e2]
    rw [e1] at ih'
    by_cases hv : LL.vec ⟨k, hlt⟩ = true
    · rw [if_pos hv] at hstep
      have h1 := colH_strip hstep.1 c
      have h2 := strip_le_one hstep (P.dom _) c
      by_cases hu : IsUsed P.mu c ⟨k, hlt⟩
      · have hss := (Finset.ssubset_iff_of_subset hsub).2 ⟨⟨k, hlt⟩, by simp [hv, hu], by simp⟩
        have := Finset.card_lt_card hss
        omega
      · have h3 : colH (P.mu (⟨k, hlt⟩ : Fin N).castSucc) c = colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c := not_not.1 hu
        omega
    · rw [if_neg hv] at hstep
      have h1 := colH_strip hstep.1 c
      omega

/- English proof (translation)
The claim follows from `column_height_le_used_count P c hc i.val i.2`.
-/
theorem col_clause4 {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (c : ℤ)
    (hc : 1 ≤ c) (i : Fin (N + 1)) : P.h i c ≤
      (Finset.univ.filter fun j : Fin N => j.val < i.val ∧ LL.vec j = true ∧ IsUsed P.mu c j).card :=
  column_height_le_used_count P c hc i.val i.2

/- English proof (translation)
Introduce `k`. Proceed by induction on `k with`. Consider the case `zero`. Introduce `hk`. Establish `h0 : (⟨0, hk⟩ : Fin (N + 1)) = 0` using `rfl`.

Rewrite using `[h0, P.zero]`. Unfold `colH`. Rewrite using `[Finset.filter_true_of_mem (fun m _ => by simpa using hc)]`. Simplify using the standard rewrite rules. Consider the case `succ k ih`.

Introduce `hk`. Establish `hlt : k < N` using `by omega`. Establish `ih'` using `ih (by omega)`. Establish `e1 : (⟨k, by omega⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).castSucc` using `rfl`. Establish `e2 : (⟨k + 1, hk⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).succ` using `rfl`.

Rewrite using `[e2]`. Rewrite `ih'` using `[e1]`. Distinguish the cases in `hu : IsUsed P.mu c ⟨k, hlt⟩`. Establish `hstep` using `P.step ⟨k, hlt⟩`. Rewrite `hstep` using `[if_pos (hcov _ hu)]`.

Establish `h1` using `colH_strip hstep.1 c`. Establish `h2 : colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c ≤ r`. Unfold `colH`. Conclude with `(Finset.card_filter_le _ _).trans (by simp)`. Use linear arithmetic over natural numbers and integers.

Establish `h3 : colH (P.mu (⟨k, hlt⟩ : Fin N).castSucc) c = colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c` using `not_not.1 hu`. Use linear arithmetic over natural numbers and integers.
-/
theorem column_height_eq_rank_nonpos {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d) (c : ℤ)
    (hc : c ≤ 0) (hcov : ∀ i, IsUsed P.mu c i → LL.vec i = true) :
    ∀ k (hk : k < N + 1), colH (P.mu ⟨k, hk⟩) c = r := by
  intro k
  induction k with
  | zero =>
    intro hk
    have h0 : (⟨0, hk⟩ : Fin (N + 1)) = 0 := rfl
    rw [h0, P.zero]
    unfold colH
    rw [Finset.filter_true_of_mem (fun m _ => by simpa using hc)]
    simp
  | succ k ih =>
    intro hk
    have hlt : k < N := by omega
    have ih' := ih (by omega)
    have e1 : (⟨k, by omega⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).castSucc := rfl
    have e2 : (⟨k + 1, hk⟩ : Fin (N + 1)) = (⟨k, hlt⟩ : Fin N).succ := rfl
    rw [e2]
    rw [e1] at ih'
    by_cases hu : IsUsed P.mu c ⟨k, hlt⟩
    · have hstep := P.step ⟨k, hlt⟩
      rw [if_pos (hcov _ hu)] at hstep
      have h1 := colH_strip hstep.1 c
      have h2 : colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c ≤ r := by
        unfold colH
        exact (Finset.card_filter_le _ _).trans (by simp)
      omega
    · have h3 : colH (P.mu (⟨k, hlt⟩ : Fin N).castSucc) c = colH (P.mu (⟨k, hlt⟩ : Fin N).succ) c := not_not.1 hu
      omega

/- English proof (translation)
Establish `hA` using `column_height_eq_rank_nonpos P c hc hcov`. Establish `hB : ∀ j, j ≤ N → Kcol R P.mu c j = extOne`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => intro _`.

Both sides reduce to the same expression. Consider the case `succ j ih`. Introduce `hj`. Establish `hlt : j < N` using `hj`. Rewrite using `[Kcol_succ R P.mu c j hlt, ih (by omega)]`.

Establish `e1 : colH (P.mu (⟨j, hlt⟩ : Fin N).castSucc) c = r` using `hA j (by omega)`. Establish `e2 : colH (P.mu (⟨j, hlt⟩ : Fin N).succ) c = r` using `hA (j + 1) (by omega)`. Rewrite using `[e1, e2, colStep_same]`. Establish `hcard` using `hI.2.1 c`. Rewrite `hcard` using `[if_neg (by omega)]`.

Establish `e3 : colH (pEnd P.mu) c = r` using `hA N (by omega)`. Rewrite `hcard` using `[e3, Nat.sub_self, Finset.card_eq_zero]`. Rewrite using `[hB N le_rfl, hcard]`. Simplify using `[extOne]`.
-/
theorem col_clause5 (R : Type*) [CommRing R] {N r : ℕ} {LL : Letters (Fin N)} {d : Fin N → ℕ} (P : PPath r N LL d)
    (c : ℤ) (hc : c ≤ 0) (hcov : ∀ i, IsUsed P.mu c i → LL.vec i = true) (I : ℤ → Finset (Fin r))
    (hI : IsSt P.mu I) : Kcol R P.mu c N (I c) = 1 := by
  have hA := column_height_eq_rank_nonpos P c hc hcov
  have hB : ∀ j, j ≤ N → Kcol R P.mu c j = extOne := by
    intro j
    induction j with
    | zero => intro _; rfl
    | succ j ih =>
      intro hj
      have hlt : j < N := hj
      rw [Kcol_succ R P.mu c j hlt, ih (by omega)]
      have e1 : colH (P.mu (⟨j, hlt⟩ : Fin N).castSucc) c = r := hA j (by omega)
      have e2 : colH (P.mu (⟨j, hlt⟩ : Fin N).succ) c = r := hA (j + 1) (by omega)
      rw [e1, e2, colStep_same]
  have hcard := hI.2.1 c
  rw [if_neg (by omega)] at hcard
  have e3 : colH (pEnd P.mu) c = r := hA N (by omega)
  rw [e3, Nat.sub_self, Finset.card_eq_zero] at hcard
  rw [hB N le_rfl, hcard]
  simp [extOne]

/- English proof (translation)
Introduce `N r _ LL d P`. Conclude with `⟨fun c Jc i => col_clause1 O P.mu c Jc i, fun i => col_clause2 P i, fun c i h => col_clause3 P c i h, fun c hc i => col_clause4 P c hc i, fun c hc hcov I hI => col_clause5 O P c hc hcov I hI⟩`.
-/
theorem span_column_clauses_at (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] : Formalism.MainNotions.PlaneGramData.ColumnDegreeBoundAtRing O := by
  intro N r _ LL d P
  exact ⟨fun c Jc i => col_clause1 O P.mu c Jc i, fun i => col_clause2 P i, fun c i h => col_clause3 P c i h,
    fun c hc i => col_clause4 P c hc i, fun c hc hcov I hI => col_clause5 O P c hc hcov I hI⟩

/- English proof (translation)
Introduce `_ O _ _ _ _ _` and use `span_column_clauses_at O`.
-/
theorem span_column_clauses (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.IntegralityRemainder D :=
  fun _ O _ _ _ _ _ => span_column_clauses_at O

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

section LGe

variable {B : Type*} [CommRing B]

def LGe (k : ℤ) (f : LaurentPolynomial B) : Prop := ∀ e ∈ f.coeff.support, k ≤ e

/- English proof (translation)
Introduce `e he`. Simplify using `at he`.
-/
theorem LGe_zero (k : ℤ) : LGe k (0 : LaurentPolynomial B) := by
  intro e he; simp at he

/- English proof (translation)
Introduce `e he`. Rewrite `he` using `[AddMonoidAlgebra.coeff_add]`. Break down `Finset.mem_union.1 (Finsupp.support_add he) with h | h` into its components or cases. Conclude with `hf e h`. Conclude with `hg e h`.
-/
theorem LGe_add {k : ℤ} {f g : LaurentPolynomial B} (hf : LGe k f) (hg : LGe k g) : LGe k (f + g) := by
  intro e he
  rw [AddMonoidAlgebra.coeff_add] at he
  rcases Finset.mem_union.1 (Finsupp.support_add he) with h | h
  · exact hf e h
  · exact hg e h

/- English proof (translation)
Introduce `e he`. Use `AddMonoidAlgebra.support_coeff_mul_subset f g he` as an intermediate fact. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 this`. Conclude with `add_le_add (hf a ha) (hg b hb)`.
-/
theorem LGe_mul {j k : ℤ} {f g : LaurentPolynomial B} (hf : LGe j f) (hg : LGe k g) : LGe (j + k) (f * g) := by
  intro e he
  have := AddMonoidAlgebra.support_coeff_mul_subset f g he
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 this
  exact add_le_add (hf a ha) (hg b hb)

/- English proof (translation)
Introduce `e he`. Establish `h : (LaurentPolynomial.C a).coeff e ≠ 0` using `Finsupp.mem_support_iff.1 he`. Rewrite `h` using `[LaurentPolynomial.C_apply]`. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hc le_rfl`.
-/
theorem LGe_C (a : B) : LGe 0 (LaurentPolynomial.C a) := by
  intro e he
  have h : (LaurentPolynomial.C a).coeff e ≠ 0 := Finsupp.mem_support_iff.1 he
  rw [LaurentPolynomial.C_apply] at h
  by_contra hc
  apply h; rw [if_neg]; rintro rfl; exact hc le_rfl

/- English proof (translation)
Introduce `e he`. Establish `h : (LaurentPolynomial.T k : LaurentPolynomial B).coeff e ≠ 0` using `Finsupp.mem_support_iff.1 he`. Rewrite `h` using `[LaurentPolynomial.T_apply]`. Assume the negation of the conclusion as `hc`. Apply `h` to reduce the goal to its premises.

Rewrite using `[if_neg]`. Introduce and unpack `rfl`. Conclude with `hc le_rfl`.
-/
theorem laurent_order_ge_T (k : ℤ) : LGe k (LaurentPolynomial.T k : LaurentPolynomial B) := by
  intro e he
  have h : (LaurentPolynomial.T k : LaurentPolynomial B).coeff e ≠ 0 := Finsupp.mem_support_iff.1 he
  rw [LaurentPolynomial.T_apply] at h
  by_contra hc
  apply h; rw [if_neg]; rintro rfl; exact hc le_rfl

/- English proof (translation)
Introduce `e he` and use `h.trans (hf e he)`.
-/
theorem LGe_mono {j k : ℤ} {f : LaurentPolynomial B} (h : j ≤ k) (hf : LGe k f) : LGe j f :=
  fun e he => h.trans (hf e he)

/- English proof (translation)
The claim follows from `Finset.sum_induction f (LGe k) (fun _ _ => LGe_add) (LGe_zero k) h`.
-/
theorem LGe_sum {α : Type*} (s : Finset α) (f : α → LaurentPolynomial B) (k : ℤ) (h : ∀ i ∈ s, LGe k (f i)) :
    LGe k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (LGe k) (fun _ _ => LGe_add) (LGe_zero k) h

/- English proof (translation)
Simplify using `using LGe_C (1 : B)`.
-/
theorem LGe_one : LGe 0 (1 : LaurentPolynomial B) := by
  simpa using LGe_C (1 : B)

variable {σ : Type*}

def PGe (k : ℤ) (H : MvPolynomial σ (LaurentPolynomial B)) : Prop := ∀ m, LGe k (H.coeff m)

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_zero]`. Conclude with `LGe_zero k`.
-/
theorem PGe_zero (k : ℤ) : PGe k (0 : MvPolynomial σ (LaurentPolynomial B)) := by
  intro m; rw [MvPolynomial.coeff_zero]; exact LGe_zero k

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_add]`. Conclude with `LGe_add (hH m) (hG m)`.
-/
theorem PGe_add {k : ℤ} {H G : MvPolynomial σ (LaurentPolynomial B)} (hH : PGe k H) (hG : PGe k G) :
    PGe k (H + G) := by
  intro m; rw [MvPolynomial.coeff_add]; exact LGe_add (hH m) (hG m)

/- English proof (translation)
The claim follows from `Finset.sum_induction f (PGe k) (fun _ _ => PGe_add) (PGe_zero k) h`.
-/
theorem PGe_sum {α : Type*} (s : Finset α) (f : α → MvPolynomial σ (LaurentPolynomial B)) (k : ℤ)
    (h : ∀ i ∈ s, PGe k (f i)) : PGe k (∑ i ∈ s, f i) :=
  Finset.sum_induction f (PGe k) (fun _ _ => PGe_add) (PGe_zero k) h

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_mul]`. Conclude with `LGe_sum _ _ _ fun x _ => LGe_mul (hH _) (hG _)`.
-/
theorem PGe_mul {j k : ℤ} {H G : MvPolynomial σ (LaurentPolynomial B)} (hH : PGe j H) (hG : PGe k G) :
    PGe (j + k) (H * G) := by
  intro m
  rw [MvPolynomial.coeff_mul]
  exact LGe_sum _ _ _ fun x _ => LGe_mul (hH _) (hG _)

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_C]`. Use `split_ifs`. Conclude with `h`. Conclude with `LGe_zero k`.
-/
theorem PGe_C {k : ℤ} {a : LaurentPolynomial B} (h : LGe k a) :
    PGe k (C a : MvPolynomial σ (LaurentPolynomial B)) := by
  intro m; rw [MvPolynomial.coeff_C]; split_ifs
  · exact h
  · exact LGe_zero k

/- English proof (translation)
Introduce `m`. Rewrite using `[MvPolynomial.coeff_X]`. Use `split_ifs`. Conclude with `LGe_one`. Conclude with `LGe_zero 0`.
-/
theorem PGe_X (v : σ) : PGe 0 (X v : MvPolynomial σ (LaurentPolynomial B)) := by
  intro m; rw [MvPolynomial.coeff_X]; split_ifs
  · exact LGe_one
  · exact LGe_zero 0

/- English proof (translation)
Use `PGe_C (σ := σ) (LGe_one (B := B))` as an intermediate fact. Simplify using `using this`.
-/
theorem PGe_one : PGe 0 (1 : MvPolynomial σ (LaurentPolynomial B)) := by
  have := PGe_C (σ := σ) (LGe_one (B := B))
  simpa using this

/- English proof (translation)
Simplify using `using PGe_mul hH hG`.
-/
theorem laurent_order_nonneg_mul {H G : MvPolynomial σ (LaurentPolynomial B)} (hH : PGe 0 H) (hG : PGe 0 G) : PGe 0 (H * G) := by
  simpa using PGe_mul hH hG

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using PGe_one`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `laurent_order_nonneg_mul ih h`.
-/
theorem laurent_order_nonneg_pow {H : MvPolynomial σ (LaurentPolynomial B)} (h : PGe 0 H) (n : ℕ) : PGe 0 (H ^ n) := by
  induction n with
  | zero => simpa using PGe_one
  | succ n ih => rw [pow_succ]; exact laurent_order_nonneg_mul ih h

/- English proof (translation)
The claim follows from `Finset.prod_induction f (PGe 0) (fun _ _ => laurent_order_nonneg_mul) PGe_one h`.
-/
theorem PGe_prod0 {α : Type*} (s : Finset α) (f : α → MvPolynomial σ (LaurentPolynomial B))
    (h : ∀ i ∈ s, PGe 0 (f i)) : PGe 0 (∏ i ∈ s, f i) :=
  Finset.prod_induction f (PGe 0) (fun _ _ => laurent_order_nonneg_mul) PGe_one h

/- English proof (translation)
Rewrite using `[MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]`. Use `PGe_sum _ _ _ fun m _ => ?_` and prove the remaining obligations. Use `PGe_mul (PGe_C (σ := σ) (hH m)) (PGe_prod0 m.support (fun i => g i ^ m i) fun i _ => laurent_order_nonneg_pow (hg i) _)` as an intermediate fact. Simplify `this` using `[MvPolynomial.algebraMap_eq]`.
-/
theorem PGe_aeval {k : ℤ} (g : σ → MvPolynomial σ (LaurentPolynomial B)) (hg : ∀ v, PGe 0 (g v))
    (H : MvPolynomial σ (LaurentPolynomial B)) (hH : PGe k H) : PGe k (aeval g H) := by
  rw [MvPolynomial.aeval_def, MvPolynomial.eval₂_eq]
  refine PGe_sum _ _ _ fun m _ => ?_
  have := PGe_mul (PGe_C (σ := σ) (hH m)) (PGe_prod0 m.support (fun i => g i ^ m i) fun i _ => laurent_order_nonneg_pow (hg i) _)
  simpa [MvPolynomial.algebraMap_eq] using this

end LGe

/- English proof (translation)
Unfold `valS sDegs PGe LGe`. Rewrite using `[Finset.le_inf_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h m e he`. Establish `hm : m ∈ (twistSub LL S (lastIdx n) G).support`.

Rewrite using `[MvPolynomial.mem_support_iff]`. Introduce `h0`. Rewrite `he` using `[h0]`. Simplify using `at he`. Conclude with `WithTop.coe_le_coe.1 (h e (Finset.mem_biUnion.2 ⟨m, hm, he⟩))`.

Introduce `h e he`. Take `⟨m, _, hm⟩` from `Finset.mem_biUnion.1 he`. Conclude with `WithTop.coe_le_coe.2 (h m e hm)`.
-/
theorem le_valuation_iff_twist_order {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S : Set ι)
    (G : MvPolynomial (ι × Fin n) R) (k : ℤ) :
    ((k : ℤ) : WithTop ℤ) ≤ valS LL S G ↔ PGe k (twistSub LL S (lastIdx n) G) := by
  unfold valS sDegs PGe LGe
  rw [Finset.le_inf_iff]
  constructor
  · intro h m e he
    have hm : m ∈ (twistSub LL S (lastIdx n) G).support := by
      rw [MvPolynomial.mem_support_iff]; intro h0; rw [h0] at he; simp at he
    exact WithTop.coe_le_coe.1 (h e (Finset.mem_biUnion.2 ⟨m, hm, he⟩))
  · intro h e he
    obtain ⟨m, _, hm⟩ := Finset.mem_biUnion.1 he
    exact WithTop.coe_le_coe.2 (h m e hm)

/- English proof (translation)
Proceed by induction on `b using WithTop.recTopCoe with`. Consider the case `top => simp`. Consider the case `coe m`. Proceed by induction on `a using WithTop.recTopCoe with`. Consider the case `top`.

Establish `h1` using `WithTop.coe_le_coe.1 (h (m + D + 1) le_top)`. Use linear arithmetic over natural numbers and integers. Consider the case `coe k`. Establish `h1` using `WithTop.coe_le_coe.1 (h k le_rfl)`. Rewrite using `[← WithTop.coe_add]`.

Conclude with `WithTop.coe_le_coe.2 (by omega)`.
-/
theorem withTop_le_add_of_forall {a b : WithTop ℤ} {D : ℤ}
    (h : ∀ k : ℤ, (k : WithTop ℤ) ≤ a → ((k - D : ℤ) : WithTop ℤ) ≤ b) : a ≤ b + (D : WithTop ℤ) := by
  induction b using WithTop.recTopCoe with
  | top => simp
  | coe m =>
    induction a using WithTop.recTopCoe with
    | top =>
      have h1 := WithTop.coe_le_coe.1 (h (m + D + 1) le_top)
      omega
    | coe k =>
      have h1 := WithTop.coe_le_coe.1 (h k le_rfl)
      rw [← WithTop.coe_add]
      exact WithTop.coe_le_coe.2 (by omega)

/- English proof (translation)
Set `f : MvPolynomial (Fin n × Fin n) R →+* GLLaurent R n` to `LaurentPolynomial.C.comp (algebraMap _ (GLCoord R n))`. Establish `h1 : gL R n = (genMat R n).map f` using `rfl`. Establish `h2 : gLinv R n = (LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det : GLCoord R n)) • ((genMat R n).adjugate.map f)`. Use extensionality with `a b`. Simplify using `[gLinv, f, Matrix.map_apply]`.

Rewrite using `[h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]`. Use `Matrix.ext fun a b => ?_` and prove the remaining obligations. Rewrite using `[Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply]`. Simplify using `only [Matrix.one_apply]`. Distinguish the cases in `hab : a = b`.

Simplify using `only [hab, if_true, smul_eq_mul, mul_one] show LaurentPolynomial.C _ * LaurentPolynomial.C (algebraMap _ (GLCoord R n) (genMat R n).det) = 1`. Rewrite using `[← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]`. Simplify using `[hab]`.
-/
theorem genericMatrix_mul_inverse_eq_one (R : Type*) [CommRing R] (n : ℕ) : gL R n * gLinv R n = 1 := by
  let f : MvPolynomial (Fin n × Fin n) R →+* GLLaurent R n :=
    LaurentPolynomial.C.comp (algebraMap _ (GLCoord R n))
  have h1 : gL R n = (genMat R n).map f := rfl
  have h2 : gLinv R n = (LaurentPolynomial.C (IsLocalization.Away.invSelf (genMat R n).det : GLCoord R n)) •
      ((genMat R n).adjugate.map f) := by
    ext a b; simp [gLinv, f, Matrix.map_apply]
  rw [h1, h2, Matrix.mul_smul, ← Matrix.map_mul, Matrix.mul_adjugate]
  refine Matrix.ext fun a b => ?_
  rw [Matrix.smul_apply, Matrix.map_apply, Matrix.smul_apply]
  simp only [Matrix.one_apply]
  by_cases hab : a = b
  · simp only [hab, if_true, smul_eq_mul, mul_one]
    show LaurentPolynomial.C _ * LaurentPolynomial.C (algebraMap _ (GLCoord R n) (genMat R n).det) = 1
    rw [← map_mul, mul_comm, IsLocalization.Away.mul_invSelf, map_one]
  · simp [hab]

/- English proof (translation)
The claim follows from `mul_eq_one_comm.1 (genericMatrix_mul_inverse_eq_one R n)`.
-/
theorem gLinv_mul_gL (R : Type*) [CommRing R] (n : ℕ) : gLinv R n * gL R n = 1 :=
  mul_eq_one_comm.1 (genericMatrix_mul_inverse_eq_one R n)

/- English proof (translation)
Unfold `twistMat`. Establish `: ∀ A B C D : Matrix (Fin n) (Fin n) (GLLaurent R n), A * B * C * (A * D * C) = A * (B * ((C * A) * D)) * C`. Introduce `A B C D`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[this, gLinv_mul_gL, Matrix.one_mul, Matrix.diagonal_mul_diagonal]`.

Establish `hd : (fun a : Fin n => (if a = j then (LaurentPolynomial.T (-1) : GLLaurent R n) else 1) * (if a = j then LaurentPolynomial.T 1 else 1)) = fun _ => 1`. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : a = j`. Simplify using `only [h, if_true]`. Rewrite using `[← LaurentPolynomial.T_add]`.

Simplify using the standard rewrite rules. Simplify using `[h]`. Rewrite using `[hd, Matrix.diagonal_one, Matrix.mul_one, genericMatrix_mul_inverse_eq_one]`.
-/
theorem twistMat_neg_mul (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) :
    twistMat R n j (-1) * twistMat R n j 1 = 1 := by
  unfold twistMat
  have : ∀ A B C D : Matrix (Fin n) (Fin n) (GLLaurent R n),
      A * B * C * (A * D * C) = A * (B * ((C * A) * D)) * C := by
    intro A B C D; simp only [Matrix.mul_assoc]
  rw [this, gLinv_mul_gL, Matrix.one_mul, Matrix.diagonal_mul_diagonal]
  have hd : (fun a : Fin n => (if a = j then (LaurentPolynomial.T (-1) : GLLaurent R n) else 1) *
      (if a = j then LaurentPolynomial.T 1 else 1)) = fun _ => 1 := by
    funext a
    by_cases h : a = j
    · simp only [h, if_true]; rw [← LaurentPolynomial.T_add]; simp
    · simp [h]
  rw [hd, Matrix.diagonal_one, Matrix.mul_one, genericMatrix_mul_inverse_eq_one]

/- English proof (translation)
Unfold `twistMat`. Rewrite using `[Matrix.mul_apply]`. Use `LGe_sum _ _ _ fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_diagonal]`. Establish `h1 : LGe 0 (gL R n a x)` using `LGe_C _`.

Establish `h2 : LGe c (if x = j then (LaurentPolynomial.T k : GLLaurent R n) else 1)` using `by split_ifs`. Conclude with `LGe_mono hk (laurent_order_ge_T k)`. Conclude with `LGe_mono hc LGe_one`. Establish `h3 : LGe 0 (gLinv R n x b)` using `LGe_C _`. Simplify using `using LGe_mul (LGe_mul h1 h2) h3`.
-/
theorem LGe_twistMat (R : Type*) [CommRing R] (n : ℕ) (j : Fin n) (k c : ℤ) (hk : c ≤ k) (hc : c ≤ 0)
    (a b : Fin n) : LGe c (twistMat R n j k a b) := by
  unfold twistMat
  rw [Matrix.mul_apply]
  refine LGe_sum _ _ _ fun x _ => ?_
  rw [Matrix.mul_diagonal]
  have h1 : LGe 0 (gL R n a x) := LGe_C _
  have h2 : LGe c (if x = j then (LaurentPolynomial.T k : GLLaurent R n) else 1) := by
    split_ifs
    · exact LGe_mono hk (laurent_order_ge_T k)
    · exact LGe_mono hc LGe_one
  have h3 : LGe 0 (gLinv R n x b) := LGe_C _
  simpa using LGe_mul (LGe_mul h1 h2) h3

/- English proof (translation)
Establish `key : ∀ k : ℤ, (k : WithTop ℤ) ≤ valS LL S F → ((k - 0 : ℤ) : WithTop ℤ) ≤ valS LL (S ∪ V) F`. Introduce `k hk`. Rewrite using `[sub_zero, le_valuation_iff_twist_order]`. Rewrite `hk` using `[le_valuation_iff_twist_order]`. Set `g : ι × Fin n → MvPolynomial (ι × Fin n) (GLLaurent R n)` to `fun v => if v.1 ∈ V ∧ v.1 ∉ S then ∑ b, C (twistMat R n (lastIdx n) 1 b v.2) * X (v.1, b) else X v`.

Establish `hg : ∀ v, PGe 0 (g v)`. Introduce `v`. Distinguish the cases in `h : v.1 ∈ V ∧ v.1 ∉ S`. Simplify using `only [g, if_pos h]`. Conclude with `PGe_sum _ _ _ fun b _ => laurent_order_nonneg_mul (PGe_C (LGe_twistMat R n _ 1 0 (by norm_num) le_rfl _ _)) (PGe_X _)`.

Simplify using `only [g, if_neg h]`. Conclude with `PGe_X _`. Establish `hcomp : twistSub LL (S ∪ V) (lastIdx n) = (aeval g : MvPolynomial (ι × Fin n) (GLLaurent R n) →ₐ[GLLaurent R n] MvPolynomial (ι × Fin n) (GLLaurent R n)).toRingHom.comp (twistSub LL S (lastIdx n))`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises. Introduce `r`.

Simplify using `[twistSub]`. Introduce `v`. Distinguish the cases in `hS : v.1 ∈ S`. Distinguish the cases in `hv : LL.vec v.1 = true`. Simplify using `[twistSub, hS, hv, g]`.

Simplify using `[twistSub, hS, hv, g]`. Distinguish the cases in `hVv : v.1 ∈ V`. Simplify using `[twistSub, hS, hVv, hV _ hVv, g]`. Simplify using `[twistSub, hS, hVv, g]`. Rewrite using `[hcomp]`.

Conclude with `PGe_aeval g hg _ hk`. Simplify using `using withTop_le_add_of_forall key`.
-/
theorem valS_le_union {R : Type*} [CommRing R] {ι : Type*} {n : ℕ} [NeZero n] (LL : Letters ι) (S V : Set ι)
    (hV : ∀ i ∈ V, LL.vec i = true) (F : MvPolynomial (ι × Fin n) R) :
    valS LL S F ≤ valS LL (S ∪ V) F := by
  have key : ∀ k : ℤ, (k : WithTop ℤ) ≤ valS LL S F → ((k - 0 : ℤ) : WithTop ℤ) ≤ valS LL (S ∪ V) F := by
    intro k hk
    rw [sub_zero, le_valuation_iff_twist_order]
    rw [le_valuation_iff_twist_order] at hk
    let g : ι × Fin n → MvPolynomial (ι × Fin n) (GLLaurent R n) := fun v =>
      if v.1 ∈ V ∧ v.1 ∉ S then ∑ b, C (twistMat R n (lastIdx n) 1 b v.2) * X (v.1, b) else X v
    have hg : ∀ v, PGe 0 (g v) := by
      intro v
      by_cases h : v.1 ∈ V ∧ v.1 ∉ S
      · simp only [g, if_pos h]
        exact PGe_sum _ _ _ fun b _ => laurent_order_nonneg_mul (PGe_C (LGe_twistMat R n _ 1 0 (by norm_num) le_rfl _ _)) (PGe_X _)
      · simp only [g, if_neg h]
        exact PGe_X _
    have hcomp : twistSub LL (S ∪ V) (lastIdx n) =
        (aeval g : MvPolynomial (ι × Fin n) (GLLaurent R n) →ₐ[GLLaurent R n]
          MvPolynomial (ι × Fin n) (GLLaurent R n)).toRingHom.comp
          (twistSub LL S (lastIdx n)) := by
      apply MvPolynomial.ringHom_ext
      · intro r
        simp [twistSub]
      · intro v
        by_cases hS : v.1 ∈ S
        · by_cases hv : LL.vec v.1 = true
          · simp [twistSub, hS, hv, g]
          · simp [twistSub, hS, hv, g]
        · by_cases hVv : v.1 ∈ V
          · simp [twistSub, hS, hVv, hV _ hVv, g]
          · simp [twistSub, hS, hVv, g]
    rw [hcomp]
    exact PGe_aeval g hg _ hk
  simpa using withTop_le_add_of_forall key

/- English proof (translation)
Rewrite using `[MvPolynomial.monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]`. Simplify using `only [map_pow, hX, mul_pow, ← pow_mul]`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hom_scale {R B σ : Type*} [CommRing R] [CommRing B] (φ ψ : MvPolynomial σ R →+* B) (u : B) (e : σ → ℕ)
    (hC : ∀ r, φ (C r) = ψ (C r)) (hX : ∀ v, φ (X v) = u ^ e v * ψ (X v)) (m : σ →₀ ℕ) (c : R) :
    φ (monomial m c) = u ^ (∑ v ∈ m.support, e v * m v) * ψ (monomial m c) := by
  rw [MvPolynomial.monomial_eq, map_mul, map_mul, hC, Finsupp.prod, map_prod, map_prod]
  simp only [map_pow, hX, mul_pow, ← pow_mul]
  rw [Finset.prod_mul_distrib, Finset.prod_pow_eq_pow_sum]
  ring

/- English proof (translation)
Use `conv_lhs => rw [F.as_sum]`. Use `conv_rhs => rw [F.as_sum]`. Rewrite using `[map_sum, map_sum, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun m hm => by rw [hom_scale φ ψ u e hC hX, hD m hm]`.
-/
theorem hom_scale_sum {R B σ : Type*} [CommRing R] [CommRing B] (φ ψ : MvPolynomial σ R →+* B) (u : B) (e : σ → ℕ)
    (hC : ∀ r, φ (C r) = ψ (C r)) (hX : ∀ v, φ (X v) = u ^ e v * ψ (X v)) (F : MvPolynomial σ R) (D : ℕ)
    (hD : ∀ m ∈ F.support, ∑ v ∈ m.support, e v * m v = D) : φ F = u ^ D * ψ F := by
  conv_lhs => rw [F.as_sum]
  conv_rhs => rw [F.as_sum]
  rw [map_sum, map_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun m hm => by rw [hom_scale φ ψ u e hC hX, hD m hm]

/- English proof (translation)
Rewrite using `[Finset.sum_subset (Finset.subset_univ _) (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv]), Fintype.sum_prod_type]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem deg_sum {ι : Type*} [Fintype ι] {n : ℕ} (V : Finset ι) (m : ι × Fin n →₀ ℕ) :
    ∑ v ∈ m.support, (if v.1 ∈ V then 1 else 0) * m v = ∑ i ∈ V, multideg m i := by
  rw [Finset.sum_subset (Finset.subset_univ _)
    (fun v _ hv => by simp [Finsupp.notMem_support_iff.1 hv]), Fintype.sum_prod_type]
  calc ∑ i, ∑ c, (if (i, c).1 ∈ V then 1 else 0) * m (i, c)
      = ∑ i, (if i ∈ V then multideg m i else 0) :=
        Finset.sum_congr rfl fun i _ => by by_cases h : i ∈ V <;> simp [h, multideg]
    _ = ∑ i ∈ V, multideg m i := by simp [Finset.sum_ite_mem]

/- English proof (translation)
Apply `withTop_le_add_of_forall` to reduce the goal to its premises. Introduce `k hk`. Rewrite `hk`, the goal using `[le_valuation_iff_twist_order]`. Use `set D : ℕ := ∑ i ∈ V, d i with hDdef`. Set `g : ι × Fin n → MvPolynomial (ι × Fin n) (GLLaurent R n)` to `fun v => if v.1 ∈ V then ∑ b, C (LaurentPolynomial.T 1 * twistMat R n (lastIdx n) (-1) b v.2) * X (v.1, b) else X v`.

Establish `hg : ∀ v, PGe 0 (g v)`. Introduce `v`. Distinguish the cases in `h : v.1 ∈ V`. Simplify using `only [g, if_pos h]`. Use `PGe_sum _ _ _ fun b _ => laurent_order_nonneg_mul (PGe_C ?_) (PGe_X _)` and prove the remaining obligations.

Use `LGe_mul (laurent_order_ge_T (B := GLCoord R n) 1) (LGe_twistMat R n (lastIdx n) (-1) (-1) le_rfl (by norm_num) b v.2)` as an intermediate fact. Simplify using `using this`. Simplify using `only [g, if_neg h]`. Conclude with `PGe_X _`. Set `φ : MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) (GLLaurent R n)` to `(aeval g : MvPolynomial (ι × Fin n) (GLLaurent R n) →ₐ[GLLaurent R n] MvPolynomial (ι × Fin n) (GLLaurent R n)).toRingHom.comp (twistSub LL S (lastIdx n))`.

Establish `hφ : φ F = (C (LaurentPolynomial.T 1) : MvPolynomial (ι × Fin n) (GLLaurent R n)) ^ D * twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F`. Use `hom_scale_sum φ _ _ (fun v => if v.1 ∈ V then 1 else 0) ?_ ?_ F D ?_` and prove the remaining obligations. Introduce `r`. Simplify using `[φ, twistSub]`. Introduce `v`.

Distinguish the cases in `hVv : v.1 ∈ V`. Establish `hS : v.1 ∈ S` using `hVS hVv`. Establish `hmul : ∀ c, ∑ b, twistMat R n (lastIdx n) (-1) c b * twistMat R n (lastIdx n) 1 b v.2 = (1 : Matrix (Fin n) (Fin n) (GLLaurent R n)) c v.2` using `fun c => by`. Rewrite using `[← Matrix.mul_apply, twistMat_neg_mul]`. Establish `e1 : φ (X v) = ∑ b, C (twistMat R n (lastIdx n) 1 b v.2) * ∑ c, C (LaurentPolynomial.T 1 * twistMat R n (lastIdx n) (-1) c b) * X (v.1, c)`.

Simplify using `[φ, twistSub, hS, hVv, hV _ hVv, g]`. Establish `e2 : twistSub LL (S \ (↑V : Set ι)) (lastIdx n) (X v : MvPolynomial (ι × Fin n) R) = X v`. Simplify using `[twistSub, hVv]`. Rewrite using `[e1, e2]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring`. Use `_ = C (LaurentPolynomial.T 1) ^ (if v.1 ∈ V then 1 else 0) * X v := by`. Simplify using `only [hmul, Matrix.one_apply, if_pos hVv, pow_one]`.

Rewrite using `[Finset.sum_eq_single v.2]`. Simplify using the standard rewrite rules. Introduce `c _ hc`. Simplify using `[hc]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`. Distinguish the cases in `hS : v.1 ∈ S`. Distinguish the cases in `hv : LL.vec v.1 = true`. Simplify using `[φ, twistSub, hS, hVv, hv, g]`. Simplify using `[φ, twistSub, hS, hVv, hv, g]`.

Simplify using `[φ, twistSub, hS, hVv, g]`. Introduce `m hm`. Establish `hm' : ∀ i, multideg m i = d i` using `((MvPolynomial.mem_restrictSupport_iff R).1 hF) hm`. Rewrite using `[deg_sum V m, hDdef]`. Conclude with `Finset.sum_congr rfl fun i _ => hm' i`.

Establish `h1 : PGe k (φ F)` using `PGe_aeval g hg _ hk`. Rewrite `h1` using `[hφ]`. Establish `h2 : twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F = C (LaurentPolynomial.T (-(D : ℤ))) * ((C (LaurentPolynomial.T 1) : MvPolynomial (ι × Fin n) (GLLaurent R n)) ^ D * twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F)`. Rewrite using `[← mul_assoc, ← map_pow, LaurentPolynomial.T_pow, ← map_mul, ← LaurentPolynomial.T_add]`. Simplify using the standard rewrite rules.

Rewrite using `[h2]`. Establish `h3` using `PGe_mul (PGe_C (σ := ι × Fin n) (laurent_order_ge_T (B := GLCoord R n) (-(D : ℤ)))) h1`. Establish `h4 : k - (D : ℤ) = -(D : ℤ) + k` using `by ring`. Rewrite using `[h4]`. Conclude with `h3`.
-/
theorem valS_le_diff {R : Type*} [CommRing R] {ι : Type*} [Fintype ι] {n : ℕ} [NeZero n] (LL : Letters ι)
    (S : Set ι) (V : Finset ι) (d : ι → ℕ) (hVS : (↑V : Set ι) ⊆ S) (hV : ∀ i ∈ V, LL.vec i = true)
    (F : MvPolynomial (ι × Fin n) R) (hF : F ∈ Pol R n d) :
    valS LL S F ≤ valS LL (S \ (↑V : Set ι)) F + (((∑ i ∈ V, d i : ℕ) : ℤ) : WithTop ℤ) := by
  apply withTop_le_add_of_forall
  intro k hk
  rw [le_valuation_iff_twist_order] at hk ⊢
  set D : ℕ := ∑ i ∈ V, d i with hDdef
  let g : ι × Fin n → MvPolynomial (ι × Fin n) (GLLaurent R n) := fun v =>
    if v.1 ∈ V then ∑ b, C (LaurentPolynomial.T 1 * twistMat R n (lastIdx n) (-1) b v.2) * X (v.1, b) else X v
  have hg : ∀ v, PGe 0 (g v) := by
    intro v
    by_cases h : v.1 ∈ V
    · simp only [g, if_pos h]
      refine PGe_sum _ _ _ fun b _ => laurent_order_nonneg_mul (PGe_C ?_) (PGe_X _)
      have := LGe_mul (laurent_order_ge_T (B := GLCoord R n) 1) (LGe_twistMat R n (lastIdx n) (-1) (-1) le_rfl (by norm_num) b v.2)
      simpa using this
    · simp only [g, if_neg h]
      exact PGe_X _
  let φ : MvPolynomial (ι × Fin n) R →+* MvPolynomial (ι × Fin n) (GLLaurent R n) :=
    (aeval g : MvPolynomial (ι × Fin n) (GLLaurent R n) →ₐ[GLLaurent R n]
          MvPolynomial (ι × Fin n) (GLLaurent R n)).toRingHom.comp
      (twistSub LL S (lastIdx n))
  have hφ : φ F = (C (LaurentPolynomial.T 1) : MvPolynomial (ι × Fin n) (GLLaurent R n)) ^ D *
      twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F := by
    refine hom_scale_sum φ _ _ (fun v => if v.1 ∈ V then 1 else 0) ?_ ?_ F D ?_
    · intro r
      simp [φ, twistSub]
    · intro v
      by_cases hVv : v.1 ∈ V
      · have hS : v.1 ∈ S := hVS hVv
        have hmul : ∀ c, ∑ b, twistMat R n (lastIdx n) (-1) c b * twistMat R n (lastIdx n) 1 b v.2 =
            (1 : Matrix (Fin n) (Fin n) (GLLaurent R n)) c v.2 := fun c => by
          rw [← Matrix.mul_apply, twistMat_neg_mul]
        have e1 : φ (X v) = ∑ b, C (twistMat R n (lastIdx n) 1 b v.2) *
            ∑ c, C (LaurentPolynomial.T 1 * twistMat R n (lastIdx n) (-1) c b) * X (v.1, c) := by
          simp [φ, twistSub, hS, hVv, hV _ hVv, g]
        have e2 : twistSub LL (S \ (↑V : Set ι)) (lastIdx n) (X v : MvPolynomial (ι × Fin n) R) = X v := by
          simp [twistSub, hVv]
        rw [e1, e2]
        calc ∑ b, C (twistMat R n (lastIdx n) 1 b v.2) *
              ∑ c, C (LaurentPolynomial.T 1 * twistMat R n (lastIdx n) (-1) c b) * X (v.1, c)
            = ∑ c, C (LaurentPolynomial.T 1) *
                C (∑ b, twistMat R n (lastIdx n) (-1) c b * twistMat R n (lastIdx n) 1 b v.2) * X (v.1, c) := by
              simp only [Finset.mul_sum, map_sum, Finset.sum_mul, map_mul]
              rw [Finset.sum_comm]
              exact Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun b _ => by ring
          _ = C (LaurentPolynomial.T 1) ^ (if v.1 ∈ V then 1 else 0) * X v := by
              simp only [hmul, Matrix.one_apply, if_pos hVv, pow_one]
              rw [Finset.sum_eq_single v.2]
              · simp
              · intro c _ hc; simp [hc]
              · intro h; exact absurd (Finset.mem_univ _) h
      · by_cases hS : v.1 ∈ S
        · by_cases hv : LL.vec v.1 = true
          · simp [φ, twistSub, hS, hVv, hv, g]
          · simp [φ, twistSub, hS, hVv, hv, g]
        · simp [φ, twistSub, hS, hVv, g]
    · intro m hm
      have hm' : ∀ i, multideg m i = d i := ((MvPolynomial.mem_restrictSupport_iff R).1 hF) hm
      rw [deg_sum V m, hDdef]
      exact Finset.sum_congr rfl fun i _ => hm' i
  have h1 : PGe k (φ F) := PGe_aeval g hg _ hk
  rw [hφ] at h1
  have h2 : twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F =
      C (LaurentPolynomial.T (-(D : ℤ))) * ((C (LaurentPolynomial.T 1) : MvPolynomial (ι × Fin n) (GLLaurent R n)) ^ D *
        twistSub LL (S \ (↑V : Set ι)) (lastIdx n) F) := by
    rw [← mul_assoc, ← map_pow, LaurentPolynomial.T_pow, ← map_mul, ← LaurentPolynomial.T_add]
    simp
  rw [h2]
  have h3 := PGe_mul (PGe_C (σ := ι × Fin n) (laurent_order_ge_T (B := GLCoord R n) (-(D : ℤ)))) h1
  have h4 : k - (D : ℤ) = -(D : ℤ) + k := by ring
  rw [h4]
  exact h3

/- English proof (translation)
Introduce `r _ ι _ LL S`. Conclude with `⟨fun V hV F => valS_le_union LL S V hV F, fun V d hVS hV F hF => valS_le_diff LL S V d hVS hV F hF⟩`.
-/
theorem twisted_valuation_second_sentence_at (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] :
    Formalism.MainNotions.PlaneGramData.EnlargingLettersAtRing O := by
  intro r _ ι _ LL S
  exact ⟨fun V hV F => valS_le_union LL S V hV F, fun V d hVS hV F hF => valS_le_diff LL S V d hVS hV F hF⟩

/- English proof (translation)
Introduce `_ O _ _ _ _ _` and use `twisted_valuation_second_sentence_at O`.
-/
theorem twisted_valuation_second_sentence (D : Formalism.BasicNotions.D7) : Formalism.MainNotions.PlaneGramData.adm2b D :=
  fun _ O _ _ _ _ _ => twisted_valuation_second_sentence_at O

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

section Abstract

variable {K V I : Type*} [Field K] [AddCommGroup V] [Module K V]

structure DecSys (W : I → Submodule K V) (e : I → Module.End K V) : Prop where
  id_on : ∀ mu, ∀ x ∈ W mu, e mu x = x
  zero_on : ∀ mu nu, nu ≠ mu → ∀ x ∈ W nu, e mu x = 0
  cover : ∀ x, ∃ T : Finset I, x = ∑ mu ∈ T, e mu x
  mem : ∀ mu x, e mu x ∈ W mu

variable {W : I → Submodule K V} {e : I → Module.End K V}

/- English proof (translation)
The claim follows from `h.zero_on mu nu hne _ (h.mem nu x)`.
-/
theorem DecSys.e_e_ne (h : DecSys W e) {mu nu : I} (hne : nu ≠ mu) (x : V) : e mu (e nu x) = 0 :=
  h.zero_on mu nu hne _ (h.mem nu x)

/- English proof (translation)
Establish `h1` using `congrArg (e mu) hT`. Rewrite `h1` using `[map_sum]`. Rewrite using `[h1]`. Use `Finset.sum_eq_zero fun nu hnu => h.e_e_ne (fun hh : nu = mu => hmu (hh ▸ hnu)) x` and prove the remaining obligations.
-/
theorem DecSys.zero_of_not_mem (h : DecSys W e) {x : V} {T : Finset I} (hT : x = ∑ mu ∈ T, e mu x) {mu : I}
    (hmu : mu ∉ T) : e mu x = 0 := by
  have h1 := congrArg (e mu) hT
  rw [map_sum] at h1
  rw [h1]
  refine Finset.sum_eq_zero fun nu hnu => h.e_e_ne (fun hh : nu = mu => hmu (hh ▸ hnu)) x

/- English proof (translation)
Rewrite using `[← Finset.sum_subset hTT fun mu _ hmu => h.zero_of_not_mem hT hmu]`. Conclude with `hT`.
-/
theorem DecSys.cover_mono (h : DecSys W e) {x : V} {T T' : Finset I} (hT : x = ∑ mu ∈ T, e mu x) (hTT : T ⊆ T') :
    x = ∑ mu ∈ T', e mu x := by
  rw [← Finset.sum_subset hTT fun mu _ hmu => h.zero_of_not_mem hT hmu]
  exact hT

/- English proof (translation)
Take `⟨T1, h1⟩` from `h.cover x`. Take `⟨T2, h2⟩` from `h.cover y`. Conclude with `⟨T1 ∪ T2, h.cover_mono h1 Finset.subset_union_left, h.cover_mono h2 Finset.subset_union_right⟩`.
-/
theorem DecSys.cover2 (h : DecSys W e) (x y : V) : ∃ T : Finset I, x = ∑ mu ∈ T, e mu x ∧ y = ∑ mu ∈ T, e mu y := by
  obtain ⟨T1, h1⟩ := h.cover x
  obtain ⟨T2, h2⟩ := h.cover y
  exact ⟨T1 ∪ T2, h.cover_mono h1 Finset.subset_union_left, h.cover_mono h2 Finset.subset_union_right⟩

def DecSys.projFun (h : DecSys W e) (Q : I → Prop) (x : V) : V :=
  ∑ mu ∈ (Classical.choose (h.cover x)).filter Q, e mu x

/- English proof (translation)
Establish `hT0` using `Classical.choose_spec (h.cover x)`. Unfold `DecSys.projFun`. Use `set T0 := Classical.choose (h.cover x)`. Establish `a1 : ∑ mu ∈ T0.filter Q, e mu x = ∑ mu ∈ (T0 ∪ T).filter Q, e mu x`. Use `Finset.sum_subset (Finset.filter_subset_filter _ Finset.subset_union_left) fun mu hmu hn => ?_` and prove the remaining obligations.

Use `h.zero_of_not_mem hT0 fun hh => hn ?_` and prove the remaining obligations. Conclude with `Finset.mem_filter.2 ⟨hh, (Finset.mem_filter.1 hmu).2⟩`. Establish `a2 : ∑ mu ∈ T.filter Q, e mu x = ∑ mu ∈ (T0 ∪ T).filter Q, e mu x`. Use `Finset.sum_subset (Finset.filter_subset_filter _ Finset.subset_union_right) fun mu hmu hn => ?_` and prove the remaining obligations. Use `h.zero_of_not_mem hT fun hh => hn ?_` and prove the remaining obligations.

Conclude with `Finset.mem_filter.2 ⟨hh, (Finset.mem_filter.1 hmu).2⟩`. Rewrite using `[a1, a2]`.
-/
theorem DecSys.projFun_eq (h : DecSys W e) (Q : I → Prop) {x : V} {T : Finset I} (hT : x = ∑ mu ∈ T, e mu x) :
    h.projFun Q x = ∑ mu ∈ T.filter Q, e mu x := by
  have hT0 := Classical.choose_spec (h.cover x)
  unfold DecSys.projFun
  set T0 := Classical.choose (h.cover x)
  have a1 : ∑ mu ∈ T0.filter Q, e mu x = ∑ mu ∈ (T0 ∪ T).filter Q, e mu x := by
    refine Finset.sum_subset (Finset.filter_subset_filter _ Finset.subset_union_left) fun mu hmu hn => ?_
    refine h.zero_of_not_mem hT0 fun hh => hn ?_
    exact Finset.mem_filter.2 ⟨hh, (Finset.mem_filter.1 hmu).2⟩
  have a2 : ∑ mu ∈ T.filter Q, e mu x = ∑ mu ∈ (T0 ∪ T).filter Q, e mu x := by
    refine Finset.sum_subset (Finset.filter_subset_filter _ Finset.subset_union_right) fun mu hmu hn => ?_
    refine h.zero_of_not_mem hT fun hh => hn ?_
    exact Finset.mem_filter.2 ⟨hh, (Finset.mem_filter.1 hmu).2⟩
  rw [a1, a2]

def DecSys.projQ (h : DecSys W e) (Q : I → Prop) : Module.End K V where
  toFun := h.projFun Q
  map_add' x y := by
    obtain ⟨T, h1, h2⟩ := h.cover2 x y
    have h3 : x + y = ∑ mu ∈ T, e mu (x + y) := by
      simp only [map_add, Finset.sum_add_distrib]
      rw [← h1, ← h2]
    rw [h.projFun_eq Q h1, h.projFun_eq Q h2, h.projFun_eq Q h3]
    simp only [map_add, Finset.sum_add_distrib]
  map_smul' c x := by
    obtain ⟨T, h1⟩ := h.cover x
    have h3 : c • x = ∑ mu ∈ T, e mu (c • x) := by
      simp only [map_smul, ← Finset.smul_sum]
      rw [← h1]
    rw [h.projFun_eq Q h1, h.projFun_eq Q h3]
    simp only [map_smul, ← Finset.smul_sum, RingHom.id_apply]

/- English proof (translation)
Establish `h1 : h.projQ Q x = _` using `h.projFun_eq Q hT`. Rewrite using `[h1]`. Reduce the equality to equality of the corresponding arguments.
-/
theorem DecSys.projQ_eq (h : DecSys W e) (Q : I → Prop) [DecidablePred Q] {x : V} {T : Finset I}
    (hT : x = ∑ mu ∈ T, e mu x) : h.projQ Q x = ∑ mu ∈ T.filter Q, e mu x := by
  have h1 : h.projQ Q x = _ := h.projFun_eq Q hT
  rw [h1]
  congr

/- English proof (translation)
Take `⟨T, h1⟩` from `h.cover x`. Establish `h3 : A x = ∑ mu ∈ T, e mu (A x)`. Simplify using `only [← hA, ← map_sum]`. Rewrite using `[← h1]`. Rewrite using `[h.projQ_eq Q h1, h.projQ_eq Q h3, map_sum]`.

Conclude with `Finset.sum_congr rfl fun mu _ => hA mu x`.
-/
theorem DecSys.comm_projQ (h : DecSys W e) (Q : I → Prop) (A : Module.End K V)
    (hA : ∀ mu x, A (e mu x) = e mu (A x)) (x : V) : A (h.projQ Q x) = h.projQ Q (A x) := by
  obtain ⟨T, h1⟩ := h.cover x
  have h3 : A x = ∑ mu ∈ T, e mu (A x) := by
    simp only [← hA, ← map_sum]
    rw [← h1]
  rw [h.projQ_eq Q h1, h.projQ_eq Q h3, map_sum]
  exact Finset.sum_congr rfl fun mu _ => hA mu x

/- English proof (translation)
Take `⟨T, h1⟩` from `h.cover x`. Establish `h2 : e mu (A x) = ∑ nu ∈ T, e mu (A (e nu x))` using `by conv_lhs => rw [h1]`. Rewrite using `[map_sum, map_sum]`. Rewrite using `[h2]`. Distinguish the cases in `hmu : mu ∈ T`.

Rewrite using `[Finset.sum_eq_single_of_mem mu hmu fun nu _ hne => h.zero_on mu nu hne _ (hA nu _ (h.mem nu x))]`. Conclude with `(h.id_on mu _ (hA mu _ (h.mem mu x))).symm`. Rewrite using `[h.zero_of_not_mem h1 hmu, map_zero]`. Use `(Finset.sum_eq_zero fun nu hnu => ?_).symm` and prove the remaining obligations. Conclude with `h.zero_on mu nu (fun hh : nu = mu => hmu (hh ▸ hnu)) _ (hA nu _ (h.mem nu x))`.
-/
theorem DecSys.comm_of_preserve (h : DecSys W e) (A : Module.End K V) (hA : ∀ mu, ∀ x ∈ W mu, A x ∈ W mu)
    (mu : I) (x : V) : A (e mu x) = e mu (A x) := by
  obtain ⟨T, h1⟩ := h.cover x
  have h2 : e mu (A x) = ∑ nu ∈ T, e mu (A (e nu x)) := by
    conv_lhs => rw [h1]
    rw [map_sum, map_sum]
  rw [h2]
  by_cases hmu : mu ∈ T
  · rw [Finset.sum_eq_single_of_mem mu hmu fun nu _ hne => h.zero_on mu nu hne _ (hA nu _ (h.mem nu x))]
    exact (h.id_on mu _ (hA mu _ (h.mem mu x))).symm
  · rw [h.zero_of_not_mem h1 hmu, map_zero]
    refine (Finset.sum_eq_zero fun nu hnu => ?_).symm
    exact h.zero_on mu nu (fun hh : nu = mu => hmu (hh ▸ hnu)) _ (hA nu _ (h.mem nu x))

end Abstract

section Iso

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction generalizing x with`. Consider the case `mem y hy`. Take `⟨ab, rfl⟩` from `hy`. Conclude with `hA _ _ x`.

Consider the case `one => rfl`. Consider the case `mul y z _ _ hy hz => show A (y (z x)) = y (z (A x))`. Rewrite using `[hy, hz]`.
-/
theorem umon_comm (E : GLOps n K V) (A : Module.End K V) (hA : ∀ a b x, A (E a b x) = E a b (A x))
    (u : Module.End K V) (hu : u ∈ Umon E) (x : V) : A (u x) = u (A x) := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction generalizing x with
  | mem y hy =>
    obtain ⟨ab, rfl⟩ := hy
    exact hA _ _ x
  | one => rfl
  | mul y z _ _ hy hz =>
    show A (y (z x)) = y (z (A x))
    rw [hy, hz]

/- English proof (translation)
Introduce `x hx`. Unfold `isoSub at hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, v, hv, rfl⟩` from `hy`.

Rewrite using `[umon_comm E A hA u hu v]`. Distinguish the cases in `h0 : A v = 0`. Rewrite using `[h0, map_zero]`. Conclude with `Submodule.zero_mem _`. Use `Submodule.subset_span ⟨u, hu, A v, ⟨h0, ?_, fun a b hab => ?_⟩, rfl⟩` and prove the remaining obligations.

Establish `hw` using `hv.2.1`. Unfold `weightSp at hw ⊢`. Rewrite `hw`, the goal using `[Submodule.mem_iInf]`. Introduce `a`. Use `hw a` as an intermediate fact.

Rewrite `this`, the goal using `[LinearMap.mem_ker]`. Establish `h2 : (E a a - (mu a : K) • (1 : Module.End K V)) (A v) = A ((E a a - (mu a : K) • (1 : Module.End K V)) v)`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA]`. Rewrite using `[h2, this, map_zero]`. Rewrite using `[← hA, hv.2.2 a b hab, map_zero]`.

Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul c y _ hy => rw [map_smul]`.

Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem isoSub_map_of_comm (E : GLOps n K V) (A : Module.End K V) (hA : ∀ a b x, A (E a b x) = E a b (A x))
    (mu : Fin n → ℤ) : ∀ x ∈ isoSub E mu, A x ∈ isoSub E mu := by
  intro x hx
  unfold isoSub at hx
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    rw [umon_comm E A hA u hu v]
    by_cases h0 : A v = 0
    · rw [h0, map_zero]; exact Submodule.zero_mem _
    · refine Submodule.subset_span ⟨u, hu, A v, ⟨h0, ?_, fun a b hab => ?_⟩, rfl⟩
      · have hw := hv.2.1
        unfold weightSp at hw ⊢
        rw [Submodule.mem_iInf] at hw ⊢
        intro a
        have := hw a
        rw [LinearMap.mem_ker] at this ⊢
        have h2 : (E a a - (mu a : K) • (1 : Module.End K V)) (A v) =
            A ((E a a - (mu a : K) • (1 : Module.End K V)) v) := by
          simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, map_sub, map_smul, hA]
        rw [h2, this, map_zero]
      · rw [← hA, hv.2.2 a b hab, map_zero]
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

end Iso

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

section PolProj

variable {K : Type*} [Field K] {ι : Type*} {r : ℕ}

/- English proof (translation)
Simplify using `[multideg, Finset.sum_add_distrib]`.
-/
theorem multideg_add (x y : ι × Fin r →₀ ℕ) (i : ι) : multideg (x + y) i = multideg x i + multideg y i := by
  simp [multideg, Finset.sum_add_distrib]

/- English proof (translation)
Unfold `multideg`. Distinguish the cases in `h : l = i`. Substitute `h` using the available equality. Rewrite using `[if_pos rfl, Finset.sum_eq_single c]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `hh`. Conclude with `hb (Prod.mk.inj hh).2.symm`. Introduce `hc`.

Conclude with `absurd (Finset.mem_univ c) hc`. Rewrite using `[if_neg h]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Rewrite using `[Finsupp.single_apply, if_neg]`. Introduce `hh`.

Conclude with `h (Prod.mk.inj hh).1`.
-/
theorem multideg_single (l : ι) (c : Fin r) (i : ι) :
    multideg (Finsupp.single (l, c) 1) i = if l = i then 1 else 0 := by
  unfold multideg
  by_cases h : l = i
  · subst h
    rw [if_pos rfl, Finset.sum_eq_single c]
    · simp
    · intro b _ hb
      rw [Finsupp.single_apply, if_neg]
      intro hh; exact hb (Prod.mk.inj hh).2.symm
    · intro hc; exact absurd (Finset.mem_univ c) hc
  · rw [if_neg h]
    refine Finset.sum_eq_zero fun b _ => ?_
    rw [Finsupp.single_apply, if_neg]
    intro hh; exact h (Prod.mk.inj hh).1

def polProj (K : Type*) [Field K] {ι : Type*} {r : ℕ} (d : ι → ℕ) : Module.End K (MvPolynomial (ι × Fin r) K) :=
  (basisMonomials (ι × Fin r) K).constr K fun m => if (∀ i, multideg m i = d i) then monomial m 1 else 0

/- English proof (translation)
Establish `h1 : (monomial m c : MvPolynomial (ι × Fin r) K) = c • basisMonomials (ι × Fin r) K m`. Rewrite using `[coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]`. Rewrite using `[h1, map_smul]`. Unfold `polProj`. Rewrite using `[Module.Basis.constr_basis]`.

Use `split_ifs`. Rewrite using `[coe_basisMonomials]`. Rewrite using `[smul_zero]`.
-/
theorem polProj_monomial (d : ι → ℕ) (m : ι × Fin r →₀ ℕ) (c : K) :
    polProj K d (monomial m c) = if (∀ i, multideg m i = d i) then monomial m c else 0 := by
  have h1 : (monomial m c : MvPolynomial (ι × Fin r) K) = c • basisMonomials (ι × Fin r) K m := by
    rw [coe_basisMonomials, smul_monomial, smul_eq_mul, mul_one]
  rw [h1, map_smul]
  unfold polProj
  rw [Module.Basis.constr_basis]
  split_ifs
  · rw [coe_basisMonomials]
  · rw [smul_zero]

/- English proof (translation)
Unfold `Pol`. Rewrite using `[mem_restrictSupport_iff]`. Introduce `m' hm'`. Use `support_monomial_subset hm'` as an intermediate fact. Rewrite `this` using `[Finset.mem_singleton]`.

Substitute `this` using the available equality. Conclude with `h`.
-/
theorem monomial_mem_Pol (d : ι → ℕ) (m : ι × Fin r →₀ ℕ) (c : K) (h : ∀ i, multideg m i = d i) :
    (monomial m c : MvPolynomial (ι × Fin r) K) ∈ Pol K r d := by
  unfold Pol
  rw [mem_restrictSupport_iff]
  intro m' hm'
  have := support_monomial_subset hm'
  rw [Finset.mem_singleton] at this
  subst this
  exact h

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[polProj_monomial]`. Use `split_ifs with h`. Conclude with `monomial_mem_Pol d m c h`.

Conclude with `Submodule.zero_mem _`. Consider the case `add p q hp hq => rw [map_add]`. Conclude with `Submodule.add_mem _ hp hq`.
-/
theorem polProj_mem (d : ι → ℕ) (F : MvPolynomial (ι × Fin r) K) : polProj K d F ∈ Pol K r d := by
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [polProj_monomial]
    split_ifs with h
    · exact monomial_mem_Pol d m c h
    · exact Submodule.zero_mem _
  | add p q hp hq => rw [map_add]; exact Submodule.add_mem _ hp hq

/- English proof (translation)
Unfold `Pol at hF`. Rewrite `hF` using `[mem_restrictSupport_iff]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[support_sum_monomial_coeff]`. Use `_ = ∑ m ∈ F.support, monomial m (F.coeff m) := by`.

Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun m hm => ?_` and prove the remaining obligations. Rewrite using `[polProj_monomial, if_pos (show ∀ i, multideg m i = d i from hF hm)]`. Use `_ = F := support_sum_monomial_coeff F`.
-/
theorem polProj_of_mem (d : ι → ℕ) (F : MvPolynomial (ι × Fin r) K) (hF : F ∈ Pol K r d) : polProj K d F = F := by
  unfold Pol at hF
  rw [mem_restrictSupport_iff] at hF
  calc polProj K d F = polProj K d (∑ m ∈ F.support, monomial m (F.coeff m)) := by
        rw [support_sum_monomial_coeff]
    _ = ∑ m ∈ F.support, monomial m (F.coeff m) := by
        rw [map_sum]
        refine Finset.sum_congr rfl fun m hm => ?_
        rw [polProj_monomial, if_pos (show ∀ i, multideg m i = d i from hF hm)]
    _ = F := support_sum_monomial_coeff F

/- English proof (translation)
Rewrite using `[pderiv_monomial]`. Distinguish the cases in `h0 : m (l, b) = 0`. Simplify using `[h0]`. Establish `hle : Finsupp.single (l, b) 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Establish `hX : (X (l, a) : MvPolynomial (ι × Fin r) K) * monomial (m - Finsupp.single (l, b) 1) (c * (m (l, b) : K)) = monomial (Finsupp.single (l, a) 1 + (m - Finsupp.single (l, b) 1)) (c * (m (l, b) : K))`. Rewrite using `[X, monomial_mul, one_mul]`. Rewrite using `[hX, polProj_monomial]`. Establish `hdeg : ∀ i, multideg (Finsupp.single (l, a) 1 + (m - Finsupp.single (l, b) 1)) i = multideg m i`.

Introduce `i`. Establish `h2 : multideg m i = multideg (m - Finsupp.single (l, b) 1) i + multideg (Finsupp.single (l, b) 1) i`. Rewrite using `[← multideg_add, tsub_add_cancel_of_le hle]`. Rewrite using `[multideg_add, h2, multideg_single, multideg_single, add_comm]`. Simplify using `only [hdeg]`.
-/
theorem polProj_step (d : ι → ℕ) (l : ι) (a b : Fin r) (m : ι × Fin r →₀ ℕ) (c : K) :
    polProj K d (X (l, a) * pderiv (l, b) (monomial m c)) =
      if (∀ i, multideg m i = d i) then X (l, a) * pderiv (l, b) (monomial m c) else 0 := by
  rw [pderiv_monomial]
  by_cases h0 : m (l, b) = 0
  · simp [h0]
  · have hle : Finsupp.single (l, b) 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    have hX : (X (l, a) : MvPolynomial (ι × Fin r) K) * monomial (m - Finsupp.single (l, b) 1) (c * (m (l, b) : K)) =
        monomial (Finsupp.single (l, a) 1 + (m - Finsupp.single (l, b) 1)) (c * (m (l, b) : K)) := by
      rw [X, monomial_mul, one_mul]
    rw [hX, polProj_monomial]
    have hdeg : ∀ i, multideg (Finsupp.single (l, a) 1 + (m - Finsupp.single (l, b) 1)) i = multideg m i := by
      intro i
      have h2 : multideg m i = multideg (m - Finsupp.single (l, b) 1) i + multideg (Finsupp.single (l, b) 1) i := by
        rw [← multideg_add, tsub_add_cancel_of_le hle]
      rw [multideg_add, h2, multideg_single, multideg_single, add_comm]
    simp only [hdeg]

/- English proof (translation)
Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial m c`. Rewrite using `[polProj_monomial]`. Establish `hg : ∀ G : MvPolynomial (ι × Fin r) K, glAct K LL S a b G = ∑ l : ι, if l ∈ S then (if LL.vec l then X (l, a) * pderiv (l, b) G else -(X (l, b) * pderiv (l, a) G)) else 0`. Introduce `G`.

Unfold `glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[hg, map_sum]`.

Distinguish the cases in `h : ∀ i, multideg m i = d i`. Rewrite using `[if_pos h, hg]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`. Rewrite using `[polProj_step, if_pos h]`.

Rewrite using `[map_neg, polProj_step, if_pos h]`. Rewrite using `[map_zero]`. Rewrite using `[if_neg h, map_zero]`. Use `Finset.sum_eq_zero fun l _ => ?_` and prove the remaining obligations. Use `split_ifs`.

Rewrite using `[polProj_step, if_neg h]`. Rewrite using `[map_neg, polProj_step, if_neg h, neg_zero]`. Rewrite using `[map_zero]`. Consider the case `add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]`.
-/
theorem polProj_glAct [Fintype ι] (d : ι → ℕ) (LL : Letters ι) (S : Set ι) (a b : Fin r)
    (F : MvPolynomial (ι × Fin r) K) : polProj K d (glAct K LL S a b F) = glAct K LL S a b (polProj K d F) := by
  induction F using MvPolynomial.induction_on' with
  | monomial m c =>
    rw [polProj_monomial]
    have hg : ∀ G : MvPolynomial (ι × Fin r) K, glAct K LL S a b G =
        ∑ l : ι, if l ∈ S then (if LL.vec l then X (l, a) * pderiv (l, b) G else -(X (l, b) * pderiv (l, a) G))
          else 0 := by
      intro G
      unfold glAct
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs <;> simp
    rw [hg, map_sum]
    by_cases h : ∀ i, multideg m i = d i
    · rw [if_pos h, hg]
      refine Finset.sum_congr rfl fun l _ => ?_
      split_ifs
      · rw [polProj_step, if_pos h]
      · rw [map_neg, polProj_step, if_pos h]
      · rw [map_zero]
    · rw [if_neg h, map_zero]
      refine Finset.sum_eq_zero fun l _ => ?_
      split_ifs
      · rw [polProj_step, if_neg h]
      · rw [map_neg, polProj_step, if_neg h, neg_zero]
      · rw [map_zero]
  | add p q hp hq => rw [map_add, map_add, map_add, map_add, hp, hq]

/- English proof (translation)
Establish `h` using `polProj_glAct d LL S a b F`. Rewrite `h` using `[polProj_of_mem d F hF]`. Rewrite using `[← h]`. Conclude with `polProj_mem d _`.
-/
theorem glAct_mem_Pol [Fintype ι] (d : ι → ℕ) (LL : Letters ι) (S : Set ι) (a b : Fin r)
    (F : MvPolynomial (ι × Fin r) K) (hF : F ∈ Pol K r d) : glAct K LL S a b F ∈ Pol K r d := by
  have h := polProj_glAct d LL S a b F
  rw [polProj_of_mem d F hF] at h
  rw [← h]
  exact polProj_mem d _

end PolProj

section Fock

variable {K : Type*} [Field K] {σ : Type*}

/- English proof (translation)
Unfold `fock`. Use `Finset.sum_subset hs fun m _ hm => ?_` and prove the remaining obligations. Rewrite using `[notMem_support_iff.1 hm, zero_mul, zero_mul]`.
-/
theorem fock_eq_sum (F G : MvPolynomial σ K) (s : Finset (σ →₀ ℕ)) (hs : F.support ⊆ s) :
    fock F G = ∑ m ∈ s, F.coeff m * G.coeff m * (expFact m : K) := by
  unfold fock
  refine Finset.sum_subset hs fun m _ hm => ?_
  rw [notMem_support_iff.1 hm, zero_mul, zero_mul]

/- English proof (translation)
Rewrite using `[fock_eq_sum (F + F') G (F.support ∪ F'.support ∪ (F + F').support) Finset.subset_union_right, fock_eq_sum F G (F.support ∪ F'.support ∪ (F + F').support) (Finset.subset_union_left.trans Finset.subset_union_left), fock_eq_sum F' G (F.support ∪ F'.support ∪ (F + F').support) (Fins …`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_add_left (F F' G : MvPolynomial σ K) : fock (F + F') G = fock F G + fock F' G := by
  rw [fock_eq_sum (F + F') G (F.support ∪ F'.support ∪ (F + F').support) Finset.subset_union_right,
    fock_eq_sum F G (F.support ∪ F'.support ∪ (F + F').support)
      (Finset.subset_union_left.trans Finset.subset_union_left),
    fock_eq_sum F' G (F.support ∪ F'.support ∪ (F + F').support)
      (Finset.subset_union_right.trans Finset.subset_union_left), ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Simplify using `[fock]`.
-/
theorem fock_zero_left (G : MvPolynomial σ K) : fock (0 : MvPolynomial σ K) G = 0 := by
  simp [fock]

/- English proof (translation)
Unfold `fock`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_add]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem fock_add_right (F G G' : MvPolynomial σ K) : fock F (G + G') = fock F G + fock F G' := by
  unfold fock
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [coeff_add]; ring

/- English proof (translation)
Simplify using `[fock]`.
-/
theorem fock_zero_right (F : MvPolynomial σ K) : fock F (0 : MvPolynomial σ K) = 0 := by
  simp [fock]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [fock_zero_left]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]`.
-/
theorem fock_sum_left {J : Type*} (s : Finset J) (F : J → MvPolynomial σ K) (G : MvPolynomial σ K) :
    fock (∑ j ∈ s, F j) G = ∑ j ∈ s, fock (F j) G := by
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_left]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_left, ih]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp [fock_zero_right]`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_right, ih]`.
-/
theorem fock_sum_right {J : Type*} (s : Finset J) (F : MvPolynomial σ K) (G : J → MvPolynomial σ K) :
    fock F (∑ j ∈ s, G j) = ∑ j ∈ s, fock F (G j) := by
  induction s using Finset.induction_on with
  | empty => simp [fock_zero_right]
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, fock_add_right, ih]

/- English proof (translation)
Rewrite using `[fock_eq_sum F _ (insert m F.support) (Finset.subset_insert _ _), Finset.sum_eq_single_of_mem m (Finset.mem_insert_self _ _)]`. Rewrite using `[coeff_monomial, if_pos rfl, mul_one]`. Introduce `m' _ hne`. Rewrite using `[coeff_monomial, if_neg (Ne.symm hne), mul_zero, zero_mul]`.
-/
theorem fock_monomial_right (F : MvPolynomial σ K) (m : σ →₀ ℕ) :
    fock F (monomial m 1) = F.coeff m * (expFact m : K) := by
  rw [fock_eq_sum F _ (insert m F.support) (Finset.subset_insert _ _),
    Finset.sum_eq_single_of_mem m (Finset.mem_insert_self _ _)]
  · rw [coeff_monomial, if_pos rfl, mul_one]
  · intro m' _ hne
    rw [coeff_monomial, if_neg (Ne.symm hne), mul_zero, zero_mul]

/- English proof (translation)
Unfold `expFact`. Conclude with `Finset.prod_ne_zero_iff.2 fun k _ => Nat.factorial_ne_zero _`.
-/
theorem expFact_ne_zero (m : σ →₀ ℕ) : expFact m ≠ 0 := by
  unfold expFact
  exact Finset.prod_ne_zero_iff.2 fun k _ => Nat.factorial_ne_zero _

end Fock

/- English proof (translation)
Use extensionality with `m`. Distinguish the cases in `hm : ∀ i, multideg m i = d i`. Establish `h1` using `h _ (monomial_mem_Pol d m 1 hm)`. Rewrite `h1` using `[fock_monomial_right, fock_monomial_right]`. Conclude with `mul_right_cancel₀ (Nat.cast_ne_zero.2 (expFact_ne_zero m)) h1`.

Unfold `Pol at hu hu'`. Rewrite `hu`, `hu'` using `[mem_restrictSupport_iff]`. Establish `a1 : u.coeff m = 0`. Assume the negation of the conclusion as `hh`. Conclude with `hm (hu (mem_support_iff.2 hh))`.

Establish `a2 : u'.coeff m = 0`. Assume the negation of the conclusion as `hh`. Conclude with `hm (hu' (mem_support_iff.2 hh))`. Rewrite using `[a1, a2]`.
-/
theorem fock_nondeg {K : Type*} [Field K] [CharZero K] {ι : Type*} {r : ℕ} (d : ι → ℕ)
    (u u' : MvPolynomial (ι × Fin r) K) (hu : u ∈ Pol K r d) (hu' : u' ∈ Pol K r d)
    (h : ∀ G ∈ Pol K r d, fock u G = fock u' G) : u = u' := by
  ext m
  by_cases hm : ∀ i, multideg m i = d i
  · have h1 := h _ (monomial_mem_Pol d m 1 hm)
    rw [fock_monomial_right, fock_monomial_right] at h1
    exact mul_right_cancel₀ (Nat.cast_ne_zero.2 (expFact_ne_zero m)) h1
  · unfold Pol at hu hu'
    rw [mem_restrictSupport_iff] at hu hu'
    have a1 : u.coeff m = 0 := by
      by_contra hh; exact hm (hu (mem_support_iff.2 hh))
    have a2 : u'.coeff m = 0 := by
      by_contra hh; exact hm (hu' (mem_support_iff.2 hh))
    rw [a1, a2]

/- English proof (translation)
Introduce `F hF`. Use `fock_nondeg d _ _ (h.1 F hF).1 (h'.1 F hF).1 fun G hG => ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem fockProj_unique {K : Type*} [Field K] [CharZero K] {ι : Type*} {r : ℕ} (d : ι → ℕ)
    (U : Set (MvPolynomial (ι × Fin r) K)) (π π' : MvPolynomial (ι × Fin r) K →ₗ[K] MvPolynomial (ι × Fin r) K)
    (h : Formalism.MainNotions.PlaneGramData.IsFockProj d U π) (h' : Formalism.MainNotions.PlaneGramData.IsFockProj d U π') :
    ∀ F ∈ Pol K r d, π F = π' F := by
  intro F hF
  refine fock_nondeg d _ _ (h.1 F hF).1 (h'.1 F hF).1 fun G hG => ?_
  calc fock (π F) G = fock (π' (π F)) G := by rw [h'.2.1 _ (h.1 F hF).1 (h.1 F hF).2]
    _ = fock (π F) (π' G) := h'.2.2 _ (h.1 F hF).1 _ hG
    _ = fock F (π (π' G)) := h.2.2 _ hF _ (h'.1 G hG).1
    _ = fock F (π' G) := by rw [h.2.1 _ (h'.1 G hG).1 (h'.1 G hG).2]
    _ = fock (π' F) G := (h'.2.2 _ hF _ hG).symm

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

def PolIsoDecompB : Prop :=
  ∀ (K : Type) [Field K] [CharZero K] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) [NeZero r] (S : Set ι),
    ∃ e : (Fin r → ℤ) → Module.End K (MvPolynomial (ι × Fin r) K),
      (∀ mu, IsIsoProj (glOps K r LL S) mu (e mu)) ∧
      ∀ G : MvPolynomial (ι × Fin r) K, ∃ T : Finset (Fin r → ℤ),
        G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K r LL S) mu

section

variable {K : Type} [Field K] [CharZero K] {ι : Type} [Fintype ι] {r : ℕ} [NeZero r] (LL : Letters ι) (S : Set ι)
variable {e : (Fin r → ℤ) → Module.End K (MvPolynomial (ι × Fin r) K)}

/- English proof (translation)
The claim follows from `(he mu).1 x hx zero_on mu nu hne x hx := (he mu).2 nu hne x hx cover x := by obtain ⟨T, h, _⟩ := hs x; exact ⟨T, h⟩ mem mu x := by obtain ⟨_, _, h⟩ := hs x; exact h mu`.
-/
theorem decSys_of (he : ∀ mu, IsIsoProj (glOps K r LL S) mu (e mu))
    (hs : ∀ G : MvPolynomial (ι × Fin r) K, ∃ T : Finset (Fin r → ℤ),
      G = ∑ mu ∈ T, e mu G ∧ ∀ mu, e mu G ∈ isoSub (glOps K r LL S) mu) :
    DecSys (fun mu => isoSub (glOps K r LL S) mu) e where
  id_on mu x hx := (he mu).1 x hx
  zero_on mu nu hne x hx := (he mu).2 nu hne x hx
  cover x := by obtain ⟨T, h, _⟩ := hs x; exact ⟨T, h⟩
  mem mu x := by obtain ⟨_, _, h⟩ := hs x; exact h mu

/- English proof (translation)
Establish `h` using `sys.comm_of_preserve (polProj K d) (fun nu => isoSub_map_of_comm (glOps K r LL S) (polProj K d) (fun a b x => polProj_glAct d LL S a b x) nu) mu F`. Rewrite `h` using `[polProj_of_mem d F hF]`. Rewrite using `[← h]`. Conclude with `polProj_mem d _`.
-/
theorem e_mem_Pol (sys : DecSys (fun mu => isoSub (glOps K r LL S) mu) e) (d : ι → ℕ) (mu : Fin r → ℤ)
    (F : MvPolynomial (ι × Fin r) K) (hF : F ∈ Pol K r d) : e mu F ∈ Pol K r d := by
  have h := sys.comm_of_preserve (polProj K d)
    (fun nu => isoSub_map_of_comm (glOps K r LL S) (polProj K d) (fun a b x => polProj_glAct d LL S a b x) nu) mu F
  rw [polProj_of_mem d F hF] at h
  rw [← h]
  exact polProj_mem d _

/- English proof (translation)
Use `⟨fun F hF => ?_, fun F hF hU => ?_, fun F hF G hG => ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `sys.cover F`. Establish `hP : sys.projQ (fun mu => th ≤ mu (lastIdx r)) F ∈ Pol K r d`. Rewrite using `[sys.projQ_eq _ hT]`. Conclude with `Submodule.sum_mem _ fun mu _ => e_mem_Pol LL S sys d mu F hF`.

Use `⟨hP, hP, ?_⟩` and prove the remaining obligations. Use `show ((th : ℤ) : WithTop ℤ) ≤ valS LL S _`. Rewrite using `[hV2]`. Introduce `mu hne`. Assume the negation of the conclusion as `hQ`.

Apply `hne` to reduce the goal to its premises. Rewrite using `[sys.projQ_eq _ hT, map_sum]`. Conclude with `Finset.sum_eq_zero fun nu hnu => sys.e_e_ne (fun hh : nu = mu => hQ (hh ▸ (Finset.mem_filter.1 hnu).2)) F`. Take `⟨T, hT⟩` from `sys.cover F`. Rewrite using `[sys.projQ_eq _ hT, Finset.sum_filter_of_ne]`.

Conclude with `hT.symm`. Introduce `mu _ hne`. Conclude with `(hV2 F th).1 hU.2 mu hne`. Take `⟨T, h1, h2⟩` from `sys.cover2 F G`. Rewrite using `[sys.projQ_eq _ h1, sys.projQ_eq _ h2, fock_sum_left, fock_sum_right]`.

Conclude with `Finset.sum_congr rfl fun mu _ => hself mu F G`.
-/
theorem isFockProj_projQ (sys : DecSys (fun mu => isoSub (glOps K r LL S) mu) e)
    (hV2 : ∀ (G : MvPolynomial (ι × Fin r) K) (th : ℤ),
      (th : WithTop ℤ) ≤ valS LL S G ↔ ∀ mu, e mu G ≠ 0 → th ≤ mu (lastIdx r))
    (hself : ∀ mu (F G : MvPolynomial (ι × Fin r) K), fock (e mu F) G = fock F (e mu G)) (d : ι → ℕ) (th : ℤ) :
    Formalism.MainNotions.PlaneGramData.IsFockProj d (Formalism.MainNotions.PlaneGramData.AK (K := K) (r := r) LL S d th)
      (sys.projQ fun mu => th ≤ mu (lastIdx r)) := by
  refine ⟨fun F hF => ?_, fun F hF hU => ?_, fun F hF G hG => ?_⟩
  · obtain ⟨T, hT⟩ := sys.cover F
    have hP : sys.projQ (fun mu => th ≤ mu (lastIdx r)) F ∈ Pol K r d := by
      rw [sys.projQ_eq _ hT]
      exact Submodule.sum_mem _ fun mu _ => e_mem_Pol LL S sys d mu F hF
    refine ⟨hP, hP, ?_⟩
    show ((th : ℤ) : WithTop ℤ) ≤ valS LL S _
    rw [hV2]
    intro mu hne
    by_contra hQ
    apply hne
    rw [sys.projQ_eq _ hT, map_sum]
    exact Finset.sum_eq_zero fun nu hnu =>
      sys.e_e_ne (fun hh : nu = mu => hQ (hh ▸ (Finset.mem_filter.1 hnu).2)) F
  · obtain ⟨T, hT⟩ := sys.cover F
    rw [sys.projQ_eq _ hT, Finset.sum_filter_of_ne]
    · exact hT.symm
    · intro mu _ hne
      exact (hV2 F th).1 hU.2 mu hne
  · obtain ⟨T, h1, h2⟩ := sys.cover2 F G
    rw [sys.projQ_eq _ h1, sys.projQ_eq _ h2, fock_sum_left, fock_sum_right]
    exact Finset.sum_congr rfl fun mu _ => hself mu F G

end

/- English proof (translation)
Establish `h1 : N0 r = r.choose 2` using `by rw [Nat.choose_two_right]; rfl`. Establish `h2 : (Nat.log p (2 * dS + r - 1) : ℝ) ≤ Real.logb p (2 * (dS : ℝ) + r)`. Establish `a1 : Nat.log p (2 * dS + r - 1) ≤ Nat.log p (2 * dS + r)` using `Nat.log_mono_right (Nat.sub_le _ _)`. Establish `a2` using `Real.natLog_le_logb (2 * dS + r) p`. Establish `a3 : ((2 * dS + r : ℕ) : ℝ) = 2 * (dS : ℝ) + r` using `by push_cast; ring`.

Rewrite `a2` using `[a3]`. Conclude with `le_trans (by exact_mod_cast a1) a2`. Rewrite using `[h1, Nat.cast_mul]`. Conclude with `mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)`.
-/
theorem proj_exponent_le (p r dS : ℕ) :
    ((N0 r * Nat.log p (2 * dS + r - 1) : ℕ) : ℝ) ≤ ((r.choose 2 : ℕ) : ℝ) * Real.logb p (2 * (dS : ℝ) + r) := by
  have h1 : N0 r = r.choose 2 := by rw [Nat.choose_two_right]; rfl
  have h2 : (Nat.log p (2 * dS + r - 1) : ℝ) ≤ Real.logb p (2 * (dS : ℝ) + r) := by
    have a1 : Nat.log p (2 * dS + r - 1) ≤ Nat.log p (2 * dS + r) := Nat.log_mono_right (Nat.sub_le _ _)
    have a2 := Real.natLog_le_logb (2 * dS + r) p
    have a3 : ((2 * dS + r : ℕ) : ℝ) = 2 * (dS : ℝ) + r := by push_cast; ring
    rw [a3] at a2
    exact le_trans (by exact_mod_cast a1) a2
  rw [h1, Nat.cast_mul]
  exact mul_le_mul_of_nonneg_left h2 (Nat.cast_nonneg _)

/- English proof (translation)
Introduce `r _ ι _ LL d S th`. Take `⟨⟨St⟩, n', hR⟩` from `hS`. Establish `: CharZero (KK O)` using `charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))`. Take `⟨e, he, hs⟩` from `hdec (KK O) ι LL r S`. Establish `sys` using `decSys_of LL S he hs`.

Take `⟨-, C1⟩` from `hC p n' O St hR r ι LL 1 (fun _ => S) monotone_const`. Take `⟨-, hcD, -, hself, hint⟩` from `C1 (fun _ => e) (fun _ => he)`. Establish `hV2` using `(hV (KK O) ι LL r S e he).1`. Establish `hπ0` using `isFockProj_projQ LL S sys hV2 (fun mu F G => hself 0 mu F G) d th`. Use `⟨⟨_, hπ0⟩, fun π hπ => ?_⟩` and prove the remaining obligations.

Establish `huniq` using `fockProj_unique d _ π _ hπ hπ0`. Use `⟨fun S' hSS => ?_, fun F hF hBB => ?_⟩` and prove the remaining obligations. Take `⟨e', he', hs'⟩` from `hdec (KK O) ι LL r S'`. Establish `sys'` using `decSys_of LL S' he' hs'`. Take `⟨-, C1'⟩` from `hC p n' O St hR r ι LL 1 (fun _ => S') monotone_const`.

Take `⟨-, -, -, hself', -⟩` from `C1' (fun _ => e') (fun _ => he')`. Establish `hV2'` using `(hV (KK O) ι LL r S' e' he').1`. Establish `key : (∀ mu a b x, glAct (KK O) LL S' a b (e mu x) = e mu (glAct (KK O) LL S' a b x)) ∧ (∀ mu nu x, e' nu (e mu x) = e mu (e' nu x))`. Break down `hSS with hsub | hdis` into its components or cases. Establish `hmono : Monotone (![S, S'] : Fin 2 → Set ι)`.

Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `le_refl _`. Conclude with `hsub`. Conclude with `absurd hij (by decide)`.

Conclude with `le_refl _`. Take `⟨-, C2⟩` from `hC p n' O St hR r ι LL 2 ![S, S'] hmono`. Take `⟨h1, -, h3, -, -⟩` from `C2 ![e, e'] (by`. Introduce `i`. Use `fin_cases i`.

Conclude with `he`. Conclude with `he')`. Conclude with `⟨fun mu a b x => (LinearMap.congr_fun (h1 0 1 (by decide) mu a b) x).symm, fun mu nu x => (LinearMap.congr_fun (h3 0 1 mu nu) x).symm⟩`. Establish `hg : ∀ mu a b x, glAct (KK O) LL S' a b (e mu x) = e mu (glAct (KK O) LL S' a b x)` using `fun mu a b x => (LinearMap.congr_fun (hcD 0 mu S' hdis a b) x).symm`. Use `⟨hg, fun mu nu x => ?_⟩` and prove the remaining obligations.

Conclude with `(sys'.comm_of_preserve (e mu) (fun nu' => isoSub_map_of_comm (glOps (KK O) r LL S') (e mu) (fun a b x => (hg mu a b x).symm) nu') nu x).symm`. Use `⟨fun a b F hF => ?_, fun th' π' hπ' F hF => ?_⟩` and prove the remaining obligations. Rewrite using `[huniq _ (glAct_mem_Pol d LL S' a b F hF), huniq F hF]`. Conclude with `(sys.comm_projQ _ (glAct (KK O) LL S' a b) (fun mu x => key.1 mu a b x) F).symm`. Establish `hπ0'` using `isFockProj_projQ LL S' sys' hV2' (fun mu F G => hself' 0 mu F G) d th'`.

Establish `huniq'` using `fockProj_unique d _ π' _ hπ' hπ0'`. Rewrite using `[huniq _ (hπ'.1 F hF).1, huniq' F hF, huniq' _ (hπ.1 F hF).1, huniq F hF]`. Establish `c1 : ∀ nu x, sys.projQ (fun mu => th ≤ mu (lastIdx r)) (e' nu x) = e' nu (sys.projQ (fun mu => th ≤ mu (lastIdx r)) x)` using `fun nu x => (sys.comm_projQ _ (e' nu) (fun mu y => key.2 mu nu y) x).symm`. Conclude with `sys'.comm_projQ _ (sys.projQ fun mu => th ≤ mu (lastIdx r)) c1 F`. Rewrite using `[huniq F hF]`.

Take `⟨T, hT⟩` from `sys.cover F`. Rewrite using `[sys.projQ_eq _ hT]`. Establish `hI` using `(hint ((T.filter fun mu => th ≤ mu (lastIdx r)).image fun mu (_ : Fin 1) => mu) d F hF).2 hBB`. Establish `hsum : (∑ t ∈ (T.filter fun mu => th ≤ mu (lastIdx r)).image (fun mu (_ : Fin 1) => mu), (List.ofFn fun i : Fin 1 => e (t i)).prod) F = ∑ mu ∈ T.filter (fun mu => th ≤ mu (lastIdx r)), e mu F`. Rewrite using `[Finset.sum_image (by intro a _ b _ h; exact congrFun h 0), LinearMap.sum_apply]`.

Conclude with `Finset.sum_congr rfl fun mu _ => by simp`. Use `beta_reduce at hI`. Rewrite `hI` using `[hsum, Fin.sum_univ_one]`. Unfold `InBB at hI`. Rewrite `hI` using `[vBB_pow_smul St]`.

Introduce `q hq`. Rewrite `hI` using `[hq]`. Establish `hI' : (0 : ℚ) ≤ ((N0 r * Nat.log p (2 * degIn d S + r - 1) : ℕ) : ℚ) + q` using `by exact_mod_cast hI`. Establish `hI'' : (0 : ℝ) ≤ ((N0 r * Nat.log p (2 * degIn d S + r - 1) : ℕ) : ℝ) + (q : ℝ)` using `by exact_mod_cast hI'`. Use `proj_exponent_le p r (degIn d S)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem projection_at_of_isotypic (D : Formalism.BasicNotions.D7) (hC : Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) (hV : Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo D) (hdec : PolIsoDecompB)
    (p : ℕ) (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [CharZero O]
    (hS : Formalism.MainNotions.PlaneGramData.HidaSetting p O) : Formalism.MainNotions.PlaneGramData.FockProjectorAtRing p O := by
  intro r _ ι _ LL d S th
  obtain ⟨⟨St⟩, n', hR⟩ := hS
  have : CharZero (KK O) := charZero_of_injective_algebraMap (IsFractionRing.injective O (KK O))
  obtain ⟨e, he, hs⟩ := hdec (KK O) ι LL r S
  have sys := decSys_of LL S he hs
  obtain ⟨-, C1⟩ := hC p n' O St hR r ι LL 1 (fun _ => S) monotone_const
  obtain ⟨-, hcD, -, hself, hint⟩ := C1 (fun _ => e) (fun _ => he)
  have hV2 := (hV (KK O) ι LL r S e he).1
  have hπ0 := isFockProj_projQ LL S sys hV2 (fun mu F G => hself 0 mu F G) d th
  refine ⟨⟨_, hπ0⟩, fun π hπ => ?_⟩
  have huniq := fockProj_unique d _ π _ hπ hπ0
  refine ⟨fun S' hSS => ?_, fun F hF hBB => ?_⟩
  · obtain ⟨e', he', hs'⟩ := hdec (KK O) ι LL r S'
    have sys' := decSys_of LL S' he' hs'
    obtain ⟨-, C1'⟩ := hC p n' O St hR r ι LL 1 (fun _ => S') monotone_const
    obtain ⟨-, -, -, hself', -⟩ := C1' (fun _ => e') (fun _ => he')
    have hV2' := (hV (KK O) ι LL r S' e' he').1
    have key : (∀ mu a b x, glAct (KK O) LL S' a b (e mu x) = e mu (glAct (KK O) LL S' a b x)) ∧
        (∀ mu nu x, e' nu (e mu x) = e mu (e' nu x)) := by
      rcases hSS with hsub | hdis
      · have hmono : Monotone (![S, S'] : Fin 2 → Set ι) := by
          intro i j hij
          fin_cases i <;> fin_cases j
          · exact le_refl _
          · exact hsub
          · exact absurd hij (by decide)
          · exact le_refl _
        obtain ⟨-, C2⟩ := hC p n' O St hR r ι LL 2 ![S, S'] hmono
        obtain ⟨h1, -, h3, -, -⟩ := C2 ![e, e'] (by
          intro i
          fin_cases i
          · exact he
          · exact he')
        exact ⟨fun mu a b x => (LinearMap.congr_fun (h1 0 1 (by decide) mu a b) x).symm,
          fun mu nu x => (LinearMap.congr_fun (h3 0 1 mu nu) x).symm⟩
      · have hg : ∀ mu a b x, glAct (KK O) LL S' a b (e mu x) = e mu (glAct (KK O) LL S' a b x) :=
          fun mu a b x => (LinearMap.congr_fun (hcD 0 mu S' hdis a b) x).symm
        refine ⟨hg, fun mu nu x => ?_⟩
        exact (sys'.comm_of_preserve (e mu) (fun nu' => isoSub_map_of_comm (glOps (KK O) r LL S') (e mu)
          (fun a b x => (hg mu a b x).symm) nu') nu x).symm
    refine ⟨fun a b F hF => ?_, fun th' π' hπ' F hF => ?_⟩
    · rw [huniq _ (glAct_mem_Pol d LL S' a b F hF), huniq F hF]
      exact (sys.comm_projQ _ (glAct (KK O) LL S' a b) (fun mu x => key.1 mu a b x) F).symm
    · have hπ0' := isFockProj_projQ LL S' sys' hV2' (fun mu F G => hself' 0 mu F G) d th'
      have huniq' := fockProj_unique d _ π' _ hπ' hπ0'
      rw [huniq _ (hπ'.1 F hF).1, huniq' F hF, huniq' _ (hπ.1 F hF).1, huniq F hF]
      have c1 : ∀ nu x, sys.projQ (fun mu => th ≤ mu (lastIdx r)) (e' nu x) =
          e' nu (sys.projQ (fun mu => th ≤ mu (lastIdx r)) x) :=
        fun nu x => (sys.comm_projQ _ (e' nu) (fun mu y => key.2 mu nu y) x).symm
      exact sys'.comm_projQ _ (sys.projQ fun mu => th ≤ mu (lastIdx r)) c1 F
  · rw [huniq F hF]
    obtain ⟨T, hT⟩ := sys.cover F
    rw [sys.projQ_eq _ hT]
    have hI := (hint ((T.filter fun mu => th ≤ mu (lastIdx r)).image fun mu (_ : Fin 1) => mu) d F hF).2 hBB
    have hsum : (∑ t ∈ (T.filter fun mu => th ≤ mu (lastIdx r)).image (fun mu (_ : Fin 1) => mu),
        (List.ofFn fun i : Fin 1 => e (t i)).prod) F = ∑ mu ∈ T.filter (fun mu => th ≤ mu (lastIdx r)), e mu F := by
      rw [Finset.sum_image (by intro a _ b _ h; exact congrFun h 0), LinearMap.sum_apply]
      exact Finset.sum_congr rfl fun mu _ => by simp
    beta_reduce at hI
    rw [hsum, Fin.sum_univ_one] at hI
    unfold InBB at hI
    rw [vBB_pow_smul St] at hI
    intro q hq
    rw [hq] at hI
    have hI' : (0 : ℚ) ≤ ((N0 r * Nat.log p (2 * degIn d S + r - 1) : ℕ) : ℚ) + q := by exact_mod_cast hI
    have hI'' : (0 : ℝ) ≤ ((N0 r * Nat.log p (2 * degIn d S + r - 1) : ℕ) : ℝ) + (q : ℝ) := by exact_mod_cast hI'
    have := proj_exponent_le p r (degIn d S)
    linarith

/- English proof (translation)
Introduce `p O _ _ _ _ hS` and use `projection_at_of_isotypic D hC hV hdec p O hS`.
-/
theorem projection_of_isotypic_decomposition (D : Formalism.BasicNotions.D7) (hC : Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) (hV : Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo D) (hdec : PolIsoDecompB) :
    Formalism.MainNotions.PlaneGramData.ArchimedeanSignatureMatching D :=
  fun p O _ _ _ _ hS => projection_at_of_isotypic D hC hV hdec p O hS

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

def GLRel (E : GLOps n K V) : Prop :=
  ∀ a b c d, E a b * E c d - E c d * E a b = (if b = c then E a d else 0) - (if d = a then E c b else 0)

def Stab (E : GLOps n K V) (W : Submodule K V) : Prop := ∀ a b, ∀ x ∈ W, E a b x ∈ W

def htW (mu : Fin n → ℤ) : ℤ := ∑ a : Fin n, ((n : ℤ) - (a.val : ℤ)) * mu a

def genSub (E : GLOps n K V) (v : V) : Submodule K V := Submodule.span K {x | ∃ u ∈ Umon E, x = u v}

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

section IsoW

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Unfold `weightSp`. Rewrite using `[Submodule.mem_iInf]`. Use `forall_congr' fun a => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`.
-/
theorem isoW_mem_weightSp (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) :
    x ∈ weightSp E mu ↔ ∀ a, E a a x = (mu a : K) • x := by
  unfold weightSp
  rw [Submodule.mem_iInf]
  refine forall_congr' fun a => ?_
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]

/- English proof (translation)
Rewrite `hx`, the goal using `[isoW_mem_weightSp]`. Introduce `c`. Establish `h1` using `LinearMap.congr_fun (h c c a b) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1`. Rewrite `h1` using `[hx c, map_smul]`.

Establish `h2 : E c c (E a b x) = (mu c : K) • E a b x + ((if c = a then E c b else 0) x - (if b = c then E a c else 0) x)`. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws. Rewrite using `[h2]`. Distinguish the cases in `hca : c = a`.

Substitute `hca` using the available equality. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality. Simplify using `[rootW]`. Establish `hcb : c ≠ b` using `fun hh => hbc hh.symm`.

Simplify using `[rootW, hbc, hcb, add_smul]`. Distinguish the cases in `hbc : b = c`. Substitute `hbc` using the available equality. Simplify using `[rootW, hca, sub_eq_add_neg, add_smul]`. Establish `hcb : c ≠ b` using `fun hh => hbc hh.symm`.

Simplify using `[rootW, hca, hbc, hcb]`.
-/
theorem E_weight (E : GLOps n K V) (h : GLRel E) (a b : Fin n) (mu : Fin n → ℤ) (x : V)
    (hx : x ∈ weightSp E mu) : E a b x ∈ weightSp E (mu + rootW a b) := by
  rw [isoW_mem_weightSp] at hx ⊢
  intro c
  have h1 := LinearMap.congr_fun (h c c a b) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
  rw [hx c, map_smul] at h1
  have h2 : E c c (E a b x) = (mu c : K) • E a b x +
      ((if c = a then E c b else 0) x - (if b = c then E a c else 0) x) := by
    rw [← h1]; abel
  rw [h2]
  by_cases hca : c = a
  · subst hca
    by_cases hbc : b = c
    · subst hbc
      simp [rootW]
    · have hcb : c ≠ b := fun hh => hbc hh.symm
      simp [rootW, hbc, hcb, add_smul]
  · by_cases hbc : b = c
    · subst hbc
      simp [rootW, hca, sub_eq_add_neg, add_smul]
    · have hcb : c ≠ b := fun hh => hbc hh.symm
      simp [rootW, hca, hbc, hcb]

/- English proof (translation)
Unfold `htW rootW`. Simplify using `only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib, Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem isoW_htW_root (mu : Fin n → ℤ) (a b : Fin n) :
    htW (mu + rootW a b) = htW mu + ((b.val : ℤ) - (a.val : ℤ)) := by
  unfold htW rootW
  simp only [Pi.add_apply, Pi.sub_apply, mul_add, mul_sub, Finset.sum_add_distrib, Finset.sum_sub_distrib,
    Pi.single_apply, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Rewrite using `[isoW_htW_root]`. Establish `: (a.val : ℤ) < (b.val : ℤ)` using `by exact_mod_cast hab`. Use linear arithmetic over natural numbers and integers.
-/
theorem htW_root_lt (mu : Fin n → ℤ) (a b : Fin n) (hab : a < b) : htW mu < htW (mu + rootW a b) := by
  rw [isoW_htW_root]
  have : (a.val : ℤ) < (b.val : ℤ) := by exact_mod_cast hab
  omega

/- English proof (translation)
Rewrite using `[isoW_htW_root]`. Establish `: (b.val : ℤ) < (a.val : ℤ)` using `by exact_mod_cast hab`. Use linear arithmetic over natural numbers and integers.
-/
theorem htW_root_gt (mu : Fin n → ℤ) (a b : Fin n) (hab : b < a) : htW (mu + rootW a b) < htW mu := by
  rw [isoW_htW_root]
  have : (b.val : ℤ) < (a.val : ℤ) := by exact_mod_cast hab
  omega

end IsoW

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

section IsoW2

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
Introduce `T`. Proceed by induction on `T using Finset.strongInduction with`. Consider the case `H T ih`. Introduce `f hf hs mu hmu`. Distinguish the cases in `hT : ∃ nu ∈ T, nu ≠ mu`.

Take `⟨nu, hnu, hne⟩` from `hT`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, nu a ≠ mu a := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hne (funext h)`.

Establish `hy : ∑ k ∈ T.erase nu, ((k a : K) - (nu a : K)) • f k ∈ W`. Establish `h1 : E a a (∑ k ∈ T, f k) - (nu a : K) • ∑ k ∈ T, f k ∈ W` using `W.sub_mem (hW a _ hs) (W.smul_mem _ hs)`. Establish `h2 : E a a (∑ k ∈ T, f k) - (nu a : K) • ∑ k ∈ T, f k = ∑ k ∈ T, ((k a : K) - (nu a : K)) • f k`. Rewrite using `[map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun k hk => ?_` and prove the remaining obligations.

Rewrite using `[(isoW_mem_weightSp E k (f k)).1 (hf k hk) a, sub_smul]`. Rewrite `h1` using `[h2, ← Finset.add_sum_erase T _ hnu, sub_self, zero_smul, zero_add]`. Conclude with `h1`. Establish `h3` using `ih (T.erase nu) (Finset.erase_ssubset hnu) (fun k => ((k a : K) - (nu a : K)) • f k) (fun k hk => Submodule.smul_mem _ _ (hf k (Finset.mem_of_mem_erase hk))) hy mu (Finset.mem_erase.2 ⟨Ne.symm hne, hmu⟩)`. Establish `hc : ((mu a : K) - (nu a : K)) ≠ 0`.

Rewrite using `[sub_ne_zero]`. Conclude with `(Ne.symm ha)` after adjusting the coercions. Establish `h4` using `W.smul_mem ((mu a : K) - (nu a : K))⁻¹ h3`. Rewrite `h4` using `[smul_smul, inv_mul_cancel₀ hc, one_smul]`. Then use the resulting hypothesis. Use `push Not at hT`.

Establish `h5 : T = {mu}` using `Finset.eq_singleton_iff_unique_mem.2 ⟨hmu, hT⟩`. Rewrite `hs` using `[h5, Finset.sum_singleton]`. Conclude with `hs`.
-/
theorem wt_comp_mem (E : GLOps n K V) [CharZero K] (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) :
    ∀ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ T, f mu ∈ weightSp E mu) →
      ∑ mu ∈ T, f mu ∈ W → ∀ mu ∈ T, f mu ∈ W := by
  classical
  intro T
  induction T using Finset.strongInduction with
  | H T ih =>
    intro f hf hs mu hmu
    by_cases hT : ∃ nu ∈ T, nu ≠ mu
    · obtain ⟨nu, hnu, hne⟩ := hT
      obtain ⟨a, ha⟩ : ∃ a, nu a ≠ mu a := by
        by_contra h
        push Not at h
        exact hne (funext h)
      have hy : ∑ k ∈ T.erase nu, ((k a : K) - (nu a : K)) • f k ∈ W := by
        have h1 : E a a (∑ k ∈ T, f k) - (nu a : K) • ∑ k ∈ T, f k ∈ W :=
          W.sub_mem (hW a _ hs) (W.smul_mem _ hs)
        have h2 : E a a (∑ k ∈ T, f k) - (nu a : K) • ∑ k ∈ T, f k = ∑ k ∈ T, ((k a : K) - (nu a : K)) • f k := by
          rw [map_sum, Finset.smul_sum, ← Finset.sum_sub_distrib]
          refine Finset.sum_congr rfl fun k hk => ?_
          rw [(isoW_mem_weightSp E k (f k)).1 (hf k hk) a, sub_smul]
        rw [h2, ← Finset.add_sum_erase T _ hnu, sub_self, zero_smul, zero_add] at h1
        exact h1
      have h3 := ih (T.erase nu) (Finset.erase_ssubset hnu) (fun k => ((k a : K) - (nu a : K)) • f k)
        (fun k hk => Submodule.smul_mem _ _ (hf k (Finset.mem_of_mem_erase hk))) hy mu
        (Finset.mem_erase.2 ⟨Ne.symm hne, hmu⟩)
      have hc : ((mu a : K) - (nu a : K)) ≠ 0 := by
        rw [sub_ne_zero]
        exact_mod_cast (Ne.symm ha)
      have h4 := W.smul_mem ((mu a : K) - (nu a : K))⁻¹ h3
      rwa [smul_smul, inv_mul_cancel₀ hc, one_smul] at h4
    · push Not at hT
      have h5 : T = {mu} := Finset.eq_singleton_iff_unique_mem.2 ⟨hmu, hT⟩
      rw [h5, Finset.sum_singleton] at hs
      exact hs

/- English proof (translation)
Apply `iSupIndep_of_dfinsupp_lsum_injective` to reduce the goal to its premises. Rewrite using `[← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']`. Introduce `v hv`. Rewrite `hv` using `[DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply]`. Use extensionality with `mu`.

Distinguish the cases in `hmu : mu ∈ v.support`. Establish `h1` using `wt_comp_mem E ⊥ (fun a x hx => by`. Rewrite using `[(Submodule.mem_bot K).1 hx, map_zero]`. Conclude with `Submodule.zero_mem _) v.support (fun i => (v i : V))`. Use the proof step `(fun i _ => (v i).2) (by rw [Submodule.mem_bot]; exact hv) mu hmu`.

Simplify using `using h1`. Simplify using `using hmu`.
-/
theorem weightSp_indep (E : GLOps n K V) [CharZero K] : iSupIndep (weightSp E) := by
  classical
  apply iSupIndep_of_dfinsupp_lsum_injective
  rw [← LinearMap.ker_eq_bot, LinearMap.ker_eq_bot']
  intro v hv
  rw [DFinsupp.lsum_apply_apply, DFinsupp.sumAddHom_apply] at hv
  ext mu
  by_cases hmu : mu ∈ v.support
  · have h1 := wt_comp_mem E ⊥ (fun a x hx => by
      rw [(Submodule.mem_bot K).1 hx, map_zero]; exact Submodule.zero_mem _) v.support (fun i => (v i : V))
      (fun i _ => (v i).2) (by rw [Submodule.mem_bot]; exact hv) mu hmu
    simpa using h1
  · simpa using hmu

/- English proof (translation)
Establish `hx' : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu` using `by rw [hwt]; trivial`. Take `⟨f, hf, hsum⟩` from `(Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'`. Establish `hsum' : ∑ mu ∈ f.support, f mu = x` using `hsum`. Use `⟨f.support, f, fun mu hmu => ⟨hf mu, ?_⟩, hsum'.symm⟩` and prove the remaining obligations. Conclude with `wt_comp_mem E W hW f.support f (fun k _ => hf k) (by rw [hsum']; exact hx) mu hmu`.
-/
theorem stab_wt_decomp (E : GLOps n K V) [CharZero K] (hwt : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (W : Submodule K V) (hW : ∀ a, ∀ x ∈ W, E a a x ∈ W) (x : V) (hx : x ∈ W) :
    ∃ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V), (∀ mu ∈ T, f mu ∈ weightSp E mu ∧ f mu ∈ W) ∧
      x = ∑ mu ∈ T, f mu := by
  have hx' : x ∈ ⨆ mu : Fin n → ℤ, weightSp E mu := by rw [hwt]; trivial
  obtain ⟨f, hf, hsum⟩ := (Submodule.mem_iSup_iff_exists_finsupp _ _).1 hx'
  have hsum' : ∑ mu ∈ f.support, f mu = x := hsum
  refine ⟨f.support, f, fun mu hmu => ⟨hf mu, ?_⟩, hsum'.symm⟩
  exact wt_comp_mem E W hW f.support f (fun k _ => hf k) (by rw [hsum']; exact hx) mu hmu

/- English proof (translation)
Establish `hnon : Nonempty {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥}`. Take `⟨x, hxW, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`. Take `⟨T, f, hf, hsum⟩` from `stab_wt_decomp E hwt W (fun a y hy => hW a a y hy) x hxW`. Establish `: ∃ mu ∈ T, f mu ≠ 0`. Assume the negation of the conclusion as `hall`.

Use `push Not at hall`. Conclude with `hx0 (hsum.trans (Finset.sum_eq_zero hall))`. Take `⟨mu, hmu, hfm⟩` from `this`. Use `⟨⟨mu, fun hb => hfm ?_⟩⟩` and prove the remaining obligations. Establish `h1 : f mu ∈ W ⊓ weightSp E mu` using `⟨(hf mu hmu).2, (hf mu hmu).1⟩`.

Rewrite `h1` using `[hb]`. Conclude with `(Submodule.mem_bot K).1 h1`. Establish `hex : ∀ mu : {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥}, ∃ v ∈ W ⊓ weightSp E mu.1, v ≠ 0` using `fun mu => Submodule.exists_mem_ne_zero_of_ne_bot mu.2`. Use `choose v hv hv0 using hex`. Establish `hli : LinearIndependent K v` using `((weightSp_indep E).comp Subtype.val_injective).linearIndependent _ (fun i => (hv i).2) hv0`.

Establish `hli' : LinearIndependent K (fun i => (⟨v i, (hv i).1⟩ : W))` using `LinearIndependent.of_comp W.subtype hli`. Establish `hfin : Finite {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥}` using `hli'.finite`. Take `⟨mu0, hmax⟩` from `Finite.exists_max (fun mu : {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥} => htW mu.1)`. Use `⟨mu0.1, v mu0, (hv mu0).1, hv0 mu0, (hv mu0).2, fun a b hab => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `h0`.

Establish `hmem : (mu0.1 + rootW a b) ∈ {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥}`. Introduce `hb`. Establish `h1 : E a b (v mu0) ∈ W ⊓ weightSp E (mu0.1 + rootW a b)` using `⟨hW a b _ (hv mu0).1, E_weight E h a b mu0.1 _ (hv mu0).2⟩`. Rewrite `h1` using `[hb]`. Conclude with `h0 ((Submodule.mem_bot K).1 h1)`.

Establish `h2` using `hmax ⟨_, hmem⟩`. Establish `h3` using `htW_root_lt mu0.1 a b hab`. Simplify using `only at h2`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_hwv (E : GLOps n K V) [CharZero K] (h : GLRel E) (hwt : (⨆ mu : Fin n → ℤ, weightSp E mu) = ⊤)
    (W : Submodule K V) [FiniteDimensional K W] (hW : Stab E W) (hne : W ≠ ⊥) :
    ∃ mu, ∃ v ∈ W, IsHWV E mu v := by
  classical
  have hnon : Nonempty {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥} := by
    obtain ⟨x, hxW, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
    obtain ⟨T, f, hf, hsum⟩ := stab_wt_decomp E hwt W (fun a y hy => hW a a y hy) x hxW
    have : ∃ mu ∈ T, f mu ≠ 0 := by
      by_contra hall
      push Not at hall
      exact hx0 (hsum.trans (Finset.sum_eq_zero hall))
    obtain ⟨mu, hmu, hfm⟩ := this
    refine ⟨⟨mu, fun hb => hfm ?_⟩⟩
    have h1 : f mu ∈ W ⊓ weightSp E mu := ⟨(hf mu hmu).2, (hf mu hmu).1⟩
    rw [hb] at h1
    exact (Submodule.mem_bot K).1 h1
  have hex : ∀ mu : {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥}, ∃ v ∈ W ⊓ weightSp E mu.1, v ≠ 0 :=
    fun mu => Submodule.exists_mem_ne_zero_of_ne_bot mu.2
  choose v hv hv0 using hex
  have hli : LinearIndependent K v :=
    ((weightSp_indep E).comp Subtype.val_injective).linearIndependent _ (fun i => (hv i).2) hv0
  have hli' : LinearIndependent K (fun i => (⟨v i, (hv i).1⟩ : W)) :=
    LinearIndependent.of_comp W.subtype hli
  have hfin : Finite {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥} := hli'.finite
  obtain ⟨mu0, hmax⟩ := Finite.exists_max (fun mu : {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥} => htW mu.1)
  refine ⟨mu0.1, v mu0, (hv mu0).1, hv0 mu0, (hv mu0).2, fun a b hab => ?_⟩
  by_contra h0
  have hmem : (mu0.1 + rootW a b) ∈ {mu : Fin n → ℤ | W ⊓ weightSp E mu ≠ ⊥} := by
    intro hb
    have h1 : E a b (v mu0) ∈ W ⊓ weightSp E (mu0.1 + rootW a b) :=
      ⟨hW a b _ (hv mu0).1, E_weight E h a b mu0.1 _ (hv mu0).2⟩
    rw [hb] at h1
    exact h0 ((Submodule.mem_bot K).1 h1)
  have h2 := hmax ⟨_, hmem⟩
  have h3 := htW_root_lt mu0.1 a b hab
  simp only at h2
  omega

end IsoW2

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V]

/- English proof (translation)
The claim follows from `Submonoid.subset_closure ⟨(a, b), rfl⟩`.
-/
theorem isoH_E_mem_Umon (E : GLOps n K V) (a b : Fin n) : E a b ∈ Umon E :=
  Submonoid.subset_closure ⟨(a, b), rfl⟩

/- English proof (translation)
Introduce `a b x hx`. Unfold `genSub at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (isoH_E_mem_Umon E a b) hu, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem genSub_stab (E : GLOps n K V) (v : V) : Stab E (genSub E v) := by
  intro a b x hx
  unfold genSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (isoH_E_mem_Umon E a b) hu, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, (Umon E).one_mem, rfl⟩`.
-/
theorem mem_genSub_self (E : GLOps n K V) (v : V) : v ∈ genSub E v :=
  Submodule.subset_span ⟨1, (Umon E).one_mem, rfl⟩

/- English proof (translation)
Unfold `Umon at hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem y hy`. Take `⟨ab, rfl⟩` from `hy`. Conclude with `fun x hx => hW _ _ x hx`.

Consider the case `one => exact fun x hx => hx`. Consider the case `mul y z _ _ hy hz => exact fun x hx => hy _ (hz x hx)`.
-/
theorem isoH_umon_mem (E : GLOps n K V) (W : Submodule K V) (hW : Stab E W) (u : Module.End K V)
    (hu : u ∈ Umon E) : ∀ x ∈ W, u x ∈ W := by
  unfold Umon at hu
  induction hu using Submonoid.closure_induction with
  | mem y hy =>
    obtain ⟨ab, rfl⟩ := hy
    exact fun x hx => hW _ _ x hx
  | one => exact fun x hx => hx
  | mul y z _ _ hy hz => exact fun x hx => hy _ (hz x hx)

/- English proof (translation)
Unfold `genSub`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, rfl⟩`. Conclude with `isoH_umon_mem E W hW u hu v hv`.
-/
theorem genSub_le (E : GLOps n K V) (v : V) (W : Submodule K V) (hW : Stab E W) (hv : v ∈ W) : genSub E v ≤ W := by
  unfold genSub
  rw [Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  exact isoH_umon_mem E W hW u hu v hv

/- English proof (translation)
Introduce `a b x hx`. Unfold `isoSub at hx ⊢`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, v, hv, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (isoH_E_mem_Umon E a b) hu, v, hv, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul c y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem isoSub_stab (E : GLOps n K V) (mu : Fin n → ℤ) : Stab E (isoSub E mu) := by
  intro a b x hx
  unfold isoSub at hx ⊢
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, v, hv, rfl⟩ := hy
    exact Submodule.subset_span ⟨E a b * u, (Umon E).mul_mem (isoH_E_mem_Umon E a b) hu, v, hv, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul c y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Unfold `genSub isoSub`. Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, rfl⟩`. Conclude with `⟨u, hu, v, hv, rfl⟩`.
-/
theorem genSub_le_isoSub (E : GLOps n K V) (mu : Fin n → ℤ) (v : V) (hv : IsHWV E mu v) :
    genSub E v ≤ isoSub E mu := by
  unfold genSub isoSub
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, rfl⟩
  exact ⟨u, hu, v, hv, rfl⟩

def isoH_lowMon (E : GLOps n K V) : Submonoid (Module.End K V) :=
  Submonoid.closure {F | ∃ c d : Fin n, d ≤ c ∧ F = E c d}

def isoH_Z (E : GLOps n K V) (v : V) : Submodule K V :=
  Submodule.span K {x | ∃ u ∈ isoH_lowMon E, x = u v}

/- English proof (translation)
Introduce `z hz`. Unfold `isoH_Z at hz ⊢`. Proceed by induction on `hz using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨u, hu, rfl⟩` from `hy`.

Conclude with `Submodule.subset_span ⟨E c d * u, (isoH_lowMon E).mul_mem (Submonoid.subset_closure ⟨c, d, hcd, rfl⟩) hu, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `Submodule.add_mem _ hy hz`.

Consider the case `smul k y _ hy => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem isoH_Z_low (E : GLOps n K V) (v : V) (c d : Fin n) (hcd : d ≤ c) :
    ∀ z ∈ isoH_Z E v, E c d z ∈ isoH_Z E v := by
  intro z hz
  unfold isoH_Z at hz ⊢
  induction hz using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact Submodule.subset_span
      ⟨E c d * u, (isoH_lowMon E).mul_mem (Submonoid.subset_closure ⟨c, d, hcd, rfl⟩) hu, rfl⟩
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
  | smul k y _ hy => rw [map_smul]; exact Submodule.smul_mem _ _ hy

/- English proof (translation)
Establish `h1` using `LinearMap.congr_fun (h a b c d) x`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply] at h1`. Rewrite using `[← h1]`. Normalize the expressions using the abelian group laws.
-/
theorem isoH_comm (E : GLOps n K V) (h : GLRel E) (a b c d : Fin n) (x : V) :
    E a b (E c d x) = E c d (E a b x) +
      ((if b = c then E a d else 0 : Module.End K V) x - (if d = a then E c b else 0 : Module.End K V) x) := by
  have h1 := LinearMap.congr_fun (h a b c d) x
  simp only [LinearMap.sub_apply, Module.End.mul_apply] at h1
  rw [← h1]
  abel

/- English proof (translation)
Unfold `isoH_lowMon at hu`. Proceed by induction on `hu using Submonoid.closure_induction_left with`. Consider the case `one`. Introduce `a b`. Distinguish the cases in `hab : a < b`.

Rewrite using `[Module.End.one_apply, hv.2.2 a b hab]`. Conclude with `Submodule.zero_mem _`. Conclude with `Submodule.subset_span ⟨E a b, Submonoid.subset_closure ⟨a, b, not_lt.1 hab, rfl⟩, rfl⟩`. Consider the case `mul_left F hF u' hu' ih`. Take `⟨c, d, hcd, rfl⟩` from `hF`.

Introduce `a b`. Use `show E a b (E c d (u' v)) ∈ _`. Rewrite using `[isoH_comm E h]`. Use `Submodule.add_mem _ (isoH_Z_low E v c d hcd _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)` and prove the remaining obligations. Use `split_ifs`.

Conclude with `ih a d`. Rewrite using `[LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`. Use `split_ifs`. Conclude with `ih c b`.

Rewrite using `[LinearMap.zero_apply]`. Conclude with `Submodule.zero_mem _`.
-/
theorem isoH_Z_word (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v)
    (u : Module.End K V) (hu : u ∈ isoH_lowMon E) : ∀ a b, E a b (u v) ∈ isoH_Z E v := by
  unfold isoH_lowMon at hu
  induction hu using Submonoid.closure_induction_left with
  | one =>
    intro a b
    by_cases hab : a < b
    · rw [Module.End.one_apply, hv.2.2 a b hab]
      exact Submodule.zero_mem _
    · exact Submodule.subset_span ⟨E a b, Submonoid.subset_closure ⟨a, b, not_lt.1 hab, rfl⟩, rfl⟩
  | mul_left F hF u' hu' ih =>
    obtain ⟨c, d, hcd, rfl⟩ := hF
    intro a b
    show E a b (E c d (u' v)) ∈ _
    rw [isoH_comm E h]
    refine Submodule.add_mem _ (isoH_Z_low E v c d hcd _ (ih a b)) (Submodule.sub_mem _ ?_ ?_)
    · split_ifs
      · exact ih a d
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _
    · split_ifs
      · exact ih c b
      · rw [LinearMap.zero_apply]; exact Submodule.zero_mem _

/- English proof (translation)
Introduce `a b x hx`. Establish `hx'` using `hx`. Unfold `isoH_Z at hx'`. Proceed by induction on `hx' using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨u, hu, rfl⟩` from `hy`. Conclude with `isoH_Z_word E h lam v hv u hu a b`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z hy' hz' hy hz`.

Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (hy hy') (hz hz')`. Consider the case `smul k y hy' hy`. Rewrite using `[map_smul]`. Conclude with `Submodule.smul_mem _ _ (hy hy')`.
-/
theorem isoH_Z_stab (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) :
    Stab E (isoH_Z E v) := by
  intro a b x hx
  have hx' := hx
  unfold isoH_Z at hx'
  induction hx' using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨u, hu, rfl⟩ := hy
    exact isoH_Z_word E h lam v hv u hu a b
  | zero => rw [map_zero]; exact Submodule.zero_mem _
  | add y z hy' hz' hy hz =>
    rw [map_add]
    exact Submodule.add_mem _ (hy hy') (hz hz')
  | smul k y hy' hy =>
    rw [map_smul]
    exact Submodule.smul_mem _ _ (hy hy')

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, (isoH_lowMon E).one_mem, rfl⟩`.
-/
theorem isoH_mem_Z (E : GLOps n K V) (v : V) : v ∈ isoH_Z E v :=
  Submodule.subset_span ⟨1, (isoH_lowMon E).one_mem, rfl⟩

def isoH_Y (E : GLOps n K V) (lam : Fin n → ℤ) (v : V) : Submodule K V :=
  Submodule.span K {v} ⊔ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu

/- English proof (translation)
Unfold `weightSp at hx`. Rewrite `hx` using `[Submodule.mem_iInf]`. Establish `h1` using `hx a`. Rewrite `h1` using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Conclude with `h1`.
-/
theorem isoH_wt_apply (E : GLOps n K V) (mu : Fin n → ℤ) (x : V) (hx : x ∈ weightSp E mu) (a : Fin n) :
    E a a x = (mu a : K) • x := by
  unfold weightSp at hx
  rw [Submodule.mem_iInf] at hx
  have h1 := hx a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero] at h1
  exact h1

/- English proof (translation)
Establish `h1` using `E_weight E h c d mu x hx`. Break down `hcd.lt_or_eq with hlt | heq` into its components or cases. Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (lt_trans (htW_root_gt mu c d hlt) hmu) h1)`. Substitute `heq` using the available equality. Establish `h0 : mu + rootW d d = mu` using `by simp [rootW]`.

Rewrite `h1` using `[h0]`. Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hmu h1)`.
-/
theorem isoH_low_wt (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (c d : Fin n) (hcd : d ≤ c)
    (mu : Fin n → ℤ) (hmu : htW mu < htW lam) (x : V) (hx : x ∈ weightSp E mu) :
    E c d x ∈ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu := by
  have h1 := E_weight E h c d mu x hx
  rcases hcd.lt_or_eq with hlt | heq
  · exact Submodule.mem_iSup_of_mem _
      (Submodule.mem_iSup_of_mem (lt_trans (htW_root_gt mu c d hlt) hmu) h1)
  · subst heq
    have h0 : mu + rootW d d = mu := by simp [rootW]
    rw [h0] at h1
    exact Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem hmu h1)

/- English proof (translation)
Introduce `y hy`. Unfold `isoH_Y at hy ⊢`. Take `⟨y1, hy1, y2, hy2, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite using `[map_add]`. Use `Submodule.add_mem _ ?_ ?_` and prove the remaining obligations.

Take `⟨k, rfl⟩` from `Submodule.mem_span_singleton.1 hy1`. Rewrite using `[map_smul]`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Break down `hcd.lt_or_eq with hlt | heq` into its components or cases. Use `Submodule.mem_sup_right ?_` and prove the remaining obligations.

Conclude with `Submodule.mem_iSup_of_mem _ (Submodule.mem_iSup_of_mem (htW_root_gt lam c d hlt) (E_weight E h c d lam v hv.2.1))`. Substitute `heq` using the available equality. Use `Submodule.mem_sup_left ?_` and prove the remaining obligations. Rewrite using `[isoH_wt_apply E lam v hv.2.1 d]`. Conclude with `Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)`.

Use `Submodule.mem_sup_right ?_` and prove the remaining obligations. Establish `hle : (⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu) ≤ Submodule.comap (E c d) (⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu)` using `iSup_le fun mu => iSup_le fun hmu => fun x hx => isoH_low_wt E h lam c d hcd mu hmu x hx`. Conclude with `hle hy2`.
-/
theorem isoH_Y_low (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v)
    (c d : Fin n) (hcd : d ≤ c) : ∀ y ∈ isoH_Y E lam v, E c d y ∈ isoH_Y E lam v := by
  intro y hy
  unfold isoH_Y at hy ⊢
  obtain ⟨y1, hy1, y2, hy2, rfl⟩ := Submodule.mem_sup.1 hy
  rw [map_add]
  refine Submodule.add_mem _ ?_ ?_
  · obtain ⟨k, rfl⟩ := Submodule.mem_span_singleton.1 hy1
    rw [map_smul]
    refine Submodule.smul_mem _ _ ?_
    rcases hcd.lt_or_eq with hlt | heq
    · refine Submodule.mem_sup_right ?_
      exact Submodule.mem_iSup_of_mem _
        (Submodule.mem_iSup_of_mem (htW_root_gt lam c d hlt) (E_weight E h c d lam v hv.2.1))
    · subst heq
      refine Submodule.mem_sup_left ?_
      rw [isoH_wt_apply E lam v hv.2.1 d]
      exact Submodule.smul_mem _ _ (Submodule.mem_span_singleton_self v)
  · refine Submodule.mem_sup_right ?_
    have hle : (⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu) ≤
        Submodule.comap (E c d) (⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu) :=
      iSup_le fun mu => iSup_le fun hmu => fun x hx => isoH_low_wt E h lam c d hcd mu hmu x hx
    exact hle hy2

/- English proof (translation)
Unfold `isoH_lowMon at hu`. Proceed by induction on `hu using Submonoid.closure_induction with`. Consider the case `mem F hF`. Take `⟨c, d, hcd, rfl⟩` from `hF`. Conclude with `isoH_Y_low E h lam v hv c d hcd`.

Consider the case `one => exact fun y hy => hy`. Consider the case `mul y z _ _ hy hz => exact fun x hx => hy _ (hz x hx)`.
-/
theorem isoH_lowMon_Y (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v)
    (u : Module.End K V) (hu : u ∈ isoH_lowMon E) : ∀ y ∈ isoH_Y E lam v, u y ∈ isoH_Y E lam v := by
  unfold isoH_lowMon at hu
  induction hu using Submonoid.closure_induction with
  | mem F hF =>
    obtain ⟨c, d, hcd, rfl⟩ := hF
    exact isoH_Y_low E h lam v hv c d hcd
  | one => exact fun y hy => hy
  | mul y z _ _ hy hz => exact fun x hx => hy _ (hz x hx)

/- English proof (translation)
Use `le_trans (genSub_le E v (isoH_Z E v) (isoH_Z_stab E h lam v hv) (isoH_mem_Z E v)) ?_` and prove the remaining obligations. Unfold `isoH_Z`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨u, hu, rfl⟩`. Conclude with `isoH_lowMon_Y E h lam v hv u hu v (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))`.
-/
theorem genSub_le_top (E : GLOps n K V) (h : GLRel E) (lam : Fin n → ℤ) (v : V) (hv : IsHWV E lam v) :
    genSub E v ≤ Submodule.span K {v} ⊔ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu := by
  refine le_trans (genSub_le E v (isoH_Z E v) (isoH_Z_stab E h lam v hv) (isoH_mem_Z E v)) ?_
  unfold isoH_Z
  rw [Submodule.span_le]
  rintro x ⟨u, hu, rfl⟩
  exact isoH_lowMon_Y E h lam v hv u hu v
    (Submodule.mem_sup_left (Submodule.mem_span_singleton_self v))

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

section CR

variable {n : ℕ} {K V : Type} [Field K] [AddCommGroup V] [Module K V]

def crRes (E : GLOps n K V) (P : Submodule K V) (hP : Stab E P) : GLOps n K P :=
  fun a b => (E a b).restrict (hP a b)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem crRes_coe (E : GLOps n K V) (P : Submodule K V) (hP : Stab E P) (a b : Fin n) (x : P) :
    ((crRes E P hP a b x : P) : V) = E a b (x : V) := rfl

/- English proof (translation)
Unfold `weightSp at hy ⊢`. Rewrite `hy`, the goal using `[Submodule.mem_iInf]`. Introduce `a`. Establish `h1` using `hy a`. Rewrite `h1`, the goal using `[LinearMap.mem_ker]`.

Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub, Submodule.coe_smul, crRes_coe, Submodule.coe_zero]`. Conclude with `h1`.
-/
theorem crRes_weight (E : GLOps n K V) (P : Submodule K V) (hP : Stab E P) (mu : Fin n → ℤ) (y : P)
    (hy : (y : V) ∈ weightSp E mu) : y ∈ weightSp (crRes E P hP) mu := by
  unfold weightSp at hy ⊢
  rw [Submodule.mem_iInf] at hy ⊢
  intro a
  have h1 := hy a
  rw [LinearMap.mem_ker] at h1 ⊢
  apply Subtype.ext
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply] at h1
  simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, Submodule.coe_sub,
    Submodule.coe_smul, crRes_coe, Submodule.coe_zero]
  exact h1

/- English proof (translation)
Use `⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩` and prove the remaining obligations. Use extensionality with `x`. Establish `h1` using `LinearMap.congr_fun (h a b c d) (x : V)`. Establish `h2 : (((crRes E P hP a b * crRes E P hP c d - crRes E P hP c d * crRes E P hP a b) x : P) : V) = (E a b * E c d - E c d * E a b) (x : V)` using `rfl`. Rewrite using `[h2, h1]`.

Apply the tactic sequence `by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, crRes_coe]`. Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨T, f, hf, hx⟩` from `hPwt x.1 x.2`. Establish `hx' : x = ∑ mu ∈ T, (if hm : mu ∈ T then (⟨f mu, (hf mu hm).2⟩ : P) else 0)`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[Submodule.coe_sum, hx]`. Use `Finset.sum_congr rfl fun mu hmu => ?_` and prove the remaining obligations. Rewrite using `[dif_pos hmu]`. Rewrite using `[hx']`.

Use `Submodule.sum_mem _ fun mu hmu => ?_` and prove the remaining obligations. Rewrite using `[dif_pos hmu]`. Conclude with `Submodule.mem_iSup_of_mem mu (crRes_weight E P hP mu _ (hf mu hmu).1)`.
-/
theorem crRes_isGLRep (E : GLOps n K V) (h : GLRel E) (P : Submodule K V) [FiniteDimensional K P] (hP : Stab E P)
    (hPwt : ∀ x ∈ P, ∃ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
      (∀ mu ∈ T, f mu ∈ weightSp E mu ∧ f mu ∈ P) ∧ x = ∑ mu ∈ T, f mu) :
    IsGLRep (crRes E P hP) := by
  classical
  refine ⟨fun a b c d => ?_, fun x => ⟨⊤, inferInstance, Submodule.mem_top, fun _ _ _ _ => Submodule.mem_top⟩, ?_⟩
  · ext x
    have h1 := LinearMap.congr_fun (h a b c d) (x : V)
    have h2 : (((crRes E P hP a b * crRes E P hP c d - crRes E P hP c d * crRes E P hP a b) x : P) : V) =
        (E a b * E c d - E c d * E a b) (x : V) := rfl
    rw [h2, h1]
    by_cases hbc : b = c <;> by_cases hda : d = a <;> simp [hbc, hda, crRes_coe]
  · rw [eq_top_iff]
    intro x _
    obtain ⟨T, f, hf, hx⟩ := hPwt x.1 x.2
    have hx' : x = ∑ mu ∈ T, (if hm : mu ∈ T then (⟨f mu, (hf mu hm).2⟩ : P) else 0) := by
      apply Subtype.ext
      rw [Submodule.coe_sum, hx]
      refine Finset.sum_congr rfl fun mu hmu => ?_
      rw [dif_pos hmu]
    rw [hx']
    refine Submodule.sum_mem _ fun mu hmu => ?_
    rw [dif_pos hmu]
    exact Submodule.mem_iSup_of_mem mu (crRes_weight E P hP mu _ (hf mu hmu).1)

/- English proof (translation)
Take `⟨W0', hc, hst⟩` from `h2 K P n (crRes E P hP) (crRes_isGLRep E h P hP hPwt) (W.comap P.subtype) (fun a b x hx => hW a b _ hx)`. Use `⟨W0'.map P.subtype, Submodule.map_subtype_le _ _, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `a b x ⟨y, hy, rfl⟩`. Conclude with `⟨crRes E P hP a b y, hst a b y hy, rfl⟩`. Rewrite using `[eq_bot_iff]`.

Introduce and unpack `x ⟨hxW, y, hy, rfl⟩`. Establish `h0 : y ∈ W.comap P.subtype ⊓ W0'` using `⟨hxW, hy⟩`. Rewrite `h0` using `[hc.inf_eq_bot, Submodule.mem_bot]`. Rewrite using `[h0]`. Conclude with `Submodule.zero_mem _`.

Establish `hWm : W = (W.comap P.subtype).map P.subtype`. Rewrite using `[Submodule.map_comap_subtype, inf_eq_right.2 hWP]`. Use `conv_lhs => rw [hWm]`. Rewrite using `[← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, Submodule.range_subtype]`.
-/
theorem cr_in (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) {n : ℕ} {K V : Type} [Field K] [CharZero K]
    [AddCommGroup V] [Module K V] (E : GLOps n K V) (h : GLRel E) (P : Submodule K V) [FiniteDimensional K P]
    (hP : Stab E P)
    (hPwt : ∀ x ∈ P, ∃ (T : Finset (Fin n → ℤ)) (f : (Fin n → ℤ) → V),
      (∀ mu ∈ T, f mu ∈ weightSp E mu ∧ f mu ∈ P) ∧ x = ∑ mu ∈ T, f mu)
    (W : Submodule K V) (hWP : W ≤ P) (hW : Stab E W) :
    ∃ W' : Submodule K V, W' ≤ P ∧ Stab E W' ∧ W ⊓ W' = ⊥ ∧ W ⊔ W' = P := by
  obtain ⟨W0', hc, hst⟩ := h2 K P n (crRes E P hP) (crRes_isGLRep E h P hP hPwt) (W.comap P.subtype)
    (fun a b x hx => hW a b _ hx)
  refine ⟨W0'.map P.subtype, Submodule.map_subtype_le _ _, ?_, ?_, ?_⟩
  · rintro a b x ⟨y, hy, rfl⟩
    exact ⟨crRes E P hP a b y, hst a b y hy, rfl⟩
  · rw [eq_bot_iff]
    rintro x ⟨hxW, y, hy, rfl⟩
    have h0 : y ∈ W.comap P.subtype ⊓ W0' := ⟨hxW, hy⟩
    rw [hc.inf_eq_bot, Submodule.mem_bot] at h0
    rw [h0]
    exact Submodule.zero_mem _
  · have hWm : W = (W.comap P.subtype).map P.subtype := by
      rw [Submodule.map_comap_subtype, inf_eq_right.2 hWP]
    conv_lhs => rw [hWm]
    rw [← Submodule.map_sup, hc.sup_eq_top, Submodule.map_top, Submodule.range_subtype]

end CR

end Formalism.MainNotions.G.Joints

end

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G
open Classical

namespace Formalism.MainNotions.G.Joints

section IsoPol

variable {K : Type} [Field K] {ι : Type} [Fintype ι] {r : ℕ}

/- English proof (translation)
Unfold `glAct`. Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isoPol_glAct_eq (LL : Letters ι) (S : Set ι) (a b : Fin r) (G : MvPolynomial (ι × Fin r) K) :
    glAct K LL S a b G =
      ∑ l : ι, if l ∈ S then (if LL.vec l then X (l, a) * pderiv (l, b) G else -(X (l, b) * pderiv (l, a) G))
        else 0 := by
  unfold glAct
  rw [LinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]`.
-/
theorem isoPol_der_sum {A : Type} [CommRing A] [Algebra K A] {J : Type} (s : Finset J) (D : J → Derivation K A A)
    (F : A) : (∑ j ∈ s, D j) F = ∑ j ∈ s, D j F := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.sum_insert ha, Finset.sum_insert ha, Derivation.add_apply, ih]

def isoPolDer (K : Type) [Field K] {ι : Type} [Fintype ι] {r : ℕ} (LL : Letters ι) (S : Set ι) (a b : Fin r) :
    Derivation K (MvPolynomial (ι × Fin r) K) (MvPolynomial (ι × Fin r) K) :=
  ∑ l : ι, if l ∈ S then
      (if LL.vec l then (X (l, a) : MvPolynomial (ι × Fin r) K) • pderiv (l, b)
       else -((X (l, b) : MvPolynomial (ι × Fin r) K) • pderiv (l, a)))
    else 0

/- English proof (translation)
Rewrite using `[isoPol_glAct_eq]`. Unfold `isoPolDer`. Rewrite using `[isoPol_der_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isoPolDer_apply (LL : Letters ι) (S : Set ι) (a b : Fin r) (F : MvPolynomial (ι × Fin r) K) :
    isoPolDer K LL S a b F = glAct K LL S a b F := by
  rw [isoPol_glAct_eq]
  unfold isoPolDer
  rw [isoPol_der_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Distinguish the cases in `h : l' = l ∧ c = b`. Take `⟨rfl, rfl⟩` from `h`. Simplify using the standard rewrite rules. Rewrite using `[if_neg h]`. Apply `pderiv_X_of_ne` to reduce the goal to its premises.

Introduce `hh`. Conclude with `h ⟨(Prod.mk.inj hh).1.symm, (Prod.mk.inj hh).2⟩`.
-/
theorem isoPol_pderiv_X (l l' : ι) (b c : Fin r) :
    pderiv (l', b) (X (l, c) : MvPolynomial (ι × Fin r) K) = if l' = l ∧ c = b then 1 else 0 := by
  by_cases h : l' = l ∧ c = b
  · obtain ⟨rfl, rfl⟩ := h
    simp
  · rw [if_neg h]
    apply pderiv_X_of_ne
    intro hh
    exact h ⟨(Prod.mk.inj hh).1.symm, (Prod.mk.inj hh).2⟩

/- English proof (translation)
Rewrite using `[isoPolDer_apply, isoPol_glAct_eq, Finset.sum_eq_single l]`. Apply the tactic sequence `simp only [isoPol_pderiv_X, true_and] split_ifs <;> simp`. Introduce `l' _ hne`. Simplify using `only [isoPol_pderiv_X, hne, false_and, if_false, mul_zero, neg_zero, ite_self]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ l) h`.
-/
theorem isoPolDer_X (LL : Letters ι) (S : Set ι) (a b : Fin r) (l : ι) (c : Fin r) :
    isoPolDer K LL S a b (X (l, c)) =
      if l ∈ S then (if LL.vec l then (if c = b then X (l, a) else 0) else (if c = a then -X (l, b) else 0))
      else 0 := by
  rw [isoPolDer_apply, isoPol_glAct_eq, Finset.sum_eq_single l]
  · simp only [isoPol_pderiv_X, true_and]
    split_ifs <;> simp
  · intro l' _ hne
    simp only [isoPol_pderiv_X, hne, false_and, if_false, mul_zero, neg_zero, ite_self]
  · intro h; exact absurd (Finset.mem_univ l) h

/- English proof (translation)
Apply `MvPolynomial.derivation_ext` to reduce the goal to its premises. Introduce and unpack `⟨l, x⟩`. Rewrite using `[Derivation.commutator_apply, Derivation.sub_apply]`. Apply the tactic sequence `have e1 : (if b = c then isoPolDer K LL S a d else 0) (X (l, x)) = if b = c then isoPolDer K LL S a d (X (l, x)) else 0 := by split_ifs <;> simp`. Apply the tactic sequence `have e2 : (if d = a then isoPolDer K LL S c b else 0) (X (l, x)) = if d = a then isoPolDer K LL S c b (X (l, x)) else 0 := by split_ifs <;> simp`.

Rewrite using `[e1, e2]`. Distinguish the cases in `hl : l ∈ S`. Distinguish the cases in `hv : LL.vec l = true`. Simplify using `only [isoPolDer_X, hl, hv, if_true, eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]`. Apply the tactic sequence `by_cases h1 : x = d <;> by_cases h2 : x = b <;> by_cases h3 : c = b <;> by_cases h4 : a = d <;>`.

Simplify using `[isoPolDer_X]`. Simplify using `only [isoPolDer_X, hl, hv, if_true, if_false, Bool.false_eq_true]`. Apply the tactic sequence `by_cases h1 : x = c <;> by_cases h2 : x = a <;> by_cases h3 : b = c <;> by_cases h4 : d = a <;>`. Simplify using `[isoPolDer_X]`. Simplify using `[isoPolDer_X, hl]`.
-/
theorem isoPol_rel_der (LL : Letters ι) (S : Set ι) (a b c d : Fin r) :
    ⁅isoPolDer K LL S a b, isoPolDer K LL S c d⁆ =
      (if b = c then isoPolDer K LL S a d else 0) - (if d = a then isoPolDer K LL S c b else 0) := by
  apply MvPolynomial.derivation_ext
  rintro ⟨l, x⟩
  rw [Derivation.commutator_apply, Derivation.sub_apply]
  have e1 : (if b = c then isoPolDer K LL S a d else 0) (X (l, x)) =
      if b = c then isoPolDer K LL S a d (X (l, x)) else 0 := by split_ifs <;> simp
  have e2 : (if d = a then isoPolDer K LL S c b else 0) (X (l, x)) =
      if d = a then isoPolDer K LL S c b (X (l, x)) else 0 := by split_ifs <;> simp
  rw [e1, e2]
  by_cases hl : l ∈ S
  · by_cases hv : LL.vec l = true
    · simp only [isoPolDer_X, hl, hv, if_true, eq_comm (a := b) (b := c), eq_comm (a := d) (b := a)]
      by_cases h1 : x = d <;> by_cases h2 : x = b <;> by_cases h3 : c = b <;> by_cases h4 : a = d <;>
        simp_all [isoPolDer_X]
    · simp only [isoPolDer_X, hl, hv, if_true, if_false, Bool.false_eq_true]
      by_cases h1 : x = c <;> by_cases h2 : x = a <;> by_cases h3 : b = c <;> by_cases h4 : d = a <;>
        simp_all [isoPolDer_X]
  · simp [isoPolDer_X, hl]

/- English proof (translation)
Introduce `a b c d`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `F`. Establish `h` using `congrArg (fun D : Derivation K (MvPolynomial (ι × Fin r) K) (MvPolynomial (ι × Fin r) K) => D F) (isoPol_rel_der (K := K) LL S a b c d)`. Simplify using `only [Derivation.commutator_apply, Derivation.sub_apply, isoPolDer_apply] at h`.

Use `show glAct K LL S a b (glAct K LL S c d F) - glAct K LL S c d (glAct K LL S a b F) = _`. Rewrite using `[h]`. Rewrite using `[LinearMap.sub_apply]`. Use `congr 1`. Use `split_ifs`.

Conclude with `isoPolDer_apply LL S a d F`. Simplify using the standard rewrite rules. Use `split_ifs`. Conclude with `isoPolDer_apply LL S c b F`. Simplify using the standard rewrite rules.
-/
theorem isoPol_GLRel (LL : Letters ι) (S : Set ι) : GLRel (glOps K r LL S) := by
  intro a b c d
  apply LinearMap.ext
  intro F
  have h := congrArg (fun D : Derivation K (MvPolynomial (ι × Fin r) K) (MvPolynomial (ι × Fin r) K) => D F)
    (isoPol_rel_der (K := K) LL S a b c d)
  simp only [Derivation.commutator_apply, Derivation.sub_apply, isoPolDer_apply] at h
  show glAct K LL S a b (glAct K LL S c d F) - glAct K LL S c d (glAct K LL S a b F) = _
  rw [h]
  rw [LinearMap.sub_apply]
  congr 1
  · split_ifs
    · exact isoPolDer_apply LL S a d F
    · simp
  · split_ifs
    · exact isoPolDer_apply LL S c b F
    · simp

/- English proof (translation)
Rewrite using `[pderiv_monomial]`. Distinguish the cases in `h0 : m (l, a) = 0`. Simplify using `[h0]`. Establish `hle : Finsupp.single (l, a) 1 ≤ m`. Rewrite using `[Finsupp.single_le_iff]`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, smul_monomial, smul_eq_mul, mul_comm]`.
-/
theorem isoPol_euler (l : ι) (a : Fin r) (m : ι × Fin r →₀ ℕ) (c : K) :
    (X (l, a) : MvPolynomial (ι × Fin r) K) * pderiv (l, a) (monomial m c) = (m (l, a) : K) • monomial m c := by
  rw [pderiv_monomial]
  by_cases h0 : m (l, a) = 0
  · simp [h0]
  · have hle : Finsupp.single (l, a) 1 ≤ m := by
      rw [Finsupp.single_le_iff]; omega
    rw [X, monomial_mul, one_mul, add_tsub_cancel_of_le hle, smul_monomial, smul_eq_mul, mul_comm]

/- English proof (translation)
Unfold `weightSp`. Rewrite using `[Submodule.mem_iInf]`. Introduce `a`. Rewrite using `[LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]`. Use `show glAct K LL S a a (monomial m c) = _`.

Rewrite using `[isoPol_glAct_eq]`. Unfold `wtS`. Rewrite using `[Int.cast_sum, Finset.sum_smul]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Rewrite using `[isoPol_euler]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem isoPol_monomial_weight (LL : Letters ι) (S : Set ι) (m : ι × Fin r →₀ ℕ) (c : K) :
    (monomial m c : MvPolynomial (ι × Fin r) K) ∈ weightSp (glOps K r LL S) (wtS LL S m) := by
  unfold weightSp
  rw [Submodule.mem_iInf]
  intro a
  rw [LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply, sub_eq_zero]
  show glAct K LL S a a (monomial m c) = _
  rw [isoPol_glAct_eq]
  unfold wtS
  rw [Int.cast_sum, Finset.sum_smul]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [isoPol_euler]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `F _`. Proceed by induction on `F using MvPolynomial.induction_on' with`. Consider the case `monomial m c => exact Submodule.mem_iSup_of_mem _ (isoPol_monomial_weight LL S m c)`. Consider the case `add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)`.
-/
theorem isoPol_weights_top (LL : Letters ι) (S : Set ι) :
    (⨆ mu : Fin r → ℤ, weightSp (glOps K r LL S) mu) = ⊤ := by
  rw [eq_top_iff]
  intro F _
  induction F using MvPolynomial.induction_on' with
  | monomial m c => exact Submodule.mem_iSup_of_mem _ (isoPol_monomial_weight LL S m c)
  | add p q hp hq => exact Submodule.add_mem _ (hp trivial) (hq trivial)

/- English proof (translation)
Use `Set.Finite.subset (Set.finite_Icc (0 : ι × Fin r →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun v => d v.1)) ?_` and prove the remaining obligations. Introduce `m hm`. Use `⟨fun v => Nat.zero_le _, fun v => ?_⟩` and prove the remaining obligations. Establish `h1 : m v ≤ multideg m v.1`. Unfold `multideg`.

Conclude with `Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)`. Establish `h2 : multideg m v.1 = d v.1` using `hm v.1`. Simplify `h1` using `[h2]`.
-/
theorem isoPol_finite_set (d : ι → ℕ) : Set.Finite {m : ι × Fin r →₀ ℕ | ∀ i, multideg m i = d i} := by
  refine Set.Finite.subset (Set.finite_Icc (0 : ι × Fin r →₀ ℕ) (Finsupp.equivFunOnFinite.symm fun v => d v.1)) ?_
  intro m hm
  refine ⟨fun v => Nat.zero_le _, fun v => ?_⟩
  have h1 : m v ≤ multideg m v.1 := by
    unfold multideg
    exact Finset.single_le_sum (f := fun c => m (v.1, c)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ v.2)
  have h2 : multideg m v.1 = d v.1 := hm v.1
  simpa [h2] using h1

instance isoPol_finDim (d : ι → ℕ) : FiniteDimensional K (Pol K r d) := by
  have : Finite ↥{m : ι × Fin r →₀ ℕ | ∀ i, multideg m i = d i} := (isoPol_finite_set d).to_subtype
  exact Module.Finite.of_basis (basisRestrictSupport K {m : ι × Fin r →₀ ℕ | ∀ i, multideg m i = d i})

/- English proof (translation)
Use `⟨x.support.sup fun m => Pol K r (multideg m), Submodule.finiteDimensional_finset_sup _ _, ?_, ?_⟩` and prove the remaining obligations. Establish `h : ∑ m ∈ x.support, monomial m (x.coeff m) ∈ x.support.sup fun m => Pol K r (multideg m)`. Use `Submodule.sum_mem _ fun m hm => ?_` and prove the remaining obligations. Establish `hle : Pol K r (multideg m) ≤ x.support.sup fun m => Pol K r (multideg m)` using `Finset.le_sup (f := fun m => Pol K r (multideg m)) hm`. Conclude with `hle (monomial_mem_Pol _ m _ fun _ => rfl)`.

Rewrite `h` using `[support_sum_monomial_coeff]`. Then use the resulting hypothesis. Introduce `a b`. Establish `hle : (x.support.sup fun m => Pol K r (multideg m)) ≤ (x.support.sup fun m => Pol K r (multideg m)).comap (glAct K LL S a b)`. Use `Finset.sup_le fun m hm y hy => ?_` and prove the remaining obligations. Establish `hle : Pol K r (multideg m) ≤ x.support.sup fun m => Pol K r (multideg m)` using `Finset.le_sup (f := fun m => Pol K r (multideg m)) hm`.

Conclude with `hle (glAct_mem_Pol _ LL S a b y hy)`. Conclude with `fun y hy => hle hy`.
-/
theorem isoPol_locFin (LL : Letters ι) (S : Set ι) (x : MvPolynomial (ι × Fin r) K) :
    ∃ W : Submodule K (MvPolynomial (ι × Fin r) K), FiniteDimensional K W ∧ x ∈ W ∧
      ∀ a b, ∀ y ∈ W, glOps K r LL S a b y ∈ W := by
  refine ⟨x.support.sup fun m => Pol K r (multideg m), Submodule.finiteDimensional_finset_sup _ _, ?_, ?_⟩
  · have h : ∑ m ∈ x.support, monomial m (x.coeff m) ∈ x.support.sup fun m => Pol K r (multideg m) := by
      refine Submodule.sum_mem _ fun m hm => ?_
      have hle : Pol K r (multideg m) ≤ x.support.sup fun m => Pol K r (multideg m) :=
        Finset.le_sup (f := fun m => Pol K r (multideg m)) hm
      exact hle (monomial_mem_Pol _ m _ fun _ => rfl)
    rwa [support_sum_monomial_coeff] at h
  · intro a b
    have hle : (x.support.sup fun m => Pol K r (multideg m)) ≤
        (x.support.sup fun m => Pol K r (multideg m)).comap (glAct K LL S a b) := by
      refine Finset.sup_le fun m hm y hy => ?_
      have hle : Pol K r (multideg m) ≤ x.support.sup fun m => Pol K r (multideg m) :=
        Finset.le_sup (f := fun m => Pol K r (multideg m)) hm
      exact hle (glAct_mem_Pol _ LL S a b y hy)
    exact fun y hy => hle hy

end IsoPol

/- English proof (translation)
Assemble the required witnesses or components as `⟨isoPol_GLRel LL S, isoPol_locFin LL S, isoPol_weights_top LL S⟩`.
-/
theorem isGLRep_glOps (K : Type) [Field K] (ι : Type) [Fintype ι] (LL : Letters ι) (r : ℕ) (S : Set ι) :
    IsGLRep (glOps K r LL S) :=
  ⟨isoPol_GLRel LL S, isoPol_locFin LL S, isoPol_weights_top LL S⟩

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

/- English proof (translation)
Establish `hint : DirectSum.IsInternal A` using `DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht`. Set `φ : (DirectSum I fun i => A i) ≃ₗ[K] V` to `LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint`. Establish `hφ : ∀ y, φ y = DirectSum.coeLinearMap A y` using `fun y => rfl`. Set `e : I → Module.End K V` to `fun i => (A i).subtype ∘ₗ DirectSum.component K I (fun i => A i) i ∘ₗ φ.symm.toLinearMap`. Establish `he : ∀ i x, e i x = ((φ.symm x) i : V)` using `fun i x => rfl`.

Establish `hlof : ∀ (i : I) (x : V) (hx : x ∈ A i), φ.symm x = DirectSum.lof K I (fun i => A i) i ⟨x, hx⟩`. Introduce `i x hx`. Rewrite using `[LinearEquiv.symm_apply_eq, hφ, DirectSum.coeLinearMap_lof]`. Use `⟨e, ⟨?_, ?_, ?_, ?_⟩⟩` and prove the remaining obligations. Introduce `mu x hx`.

Rewrite using `[he, hlof mu x hx, DirectSum.lof_eq_of, DirectSum.of_eq_same]`. Introduce `mu nu hne x hx`. Rewrite using `[he, hlof nu x hx, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hne.symm]`. Both sides reduce to the same expression. Introduce `x`.

Use `⟨(φ.symm x).support, ?_⟩` and prove the remaining obligations. Establish `h1 : x = φ (φ.symm x)` using `(φ.apply_symm_apply x).symm`. Use `conv_lhs => rw [h1, hφ, DirectSum.coeLinearMap_eq_dfinsuppSum]`. Both sides reduce to the same expression. Introduce `mu x`.

Rewrite using `[he]`. Conclude with `((φ.symm x) mu).2`.
-/
theorem decomp_of_indep_top {K V I : Type*} [Field K] [AddCommGroup V] [Module K V] (A : I → Submodule K V)
    (hi : iSupIndep A) (ht : (⨆ i, A i) = ⊤) : ∃ e : I → Module.End K V, DecSys A e := by
  classical
  have hint : DirectSum.IsInternal A := DirectSum.isInternal_submodule_of_iSupIndep_of_iSup_eq_top hi ht
  let φ : (DirectSum I fun i => A i) ≃ₗ[K] V := LinearEquiv.ofBijective (DirectSum.coeLinearMap A) hint
  have hφ : ∀ y, φ y = DirectSum.coeLinearMap A y := fun y => rfl
  let e : I → Module.End K V := fun i =>
    (A i).subtype ∘ₗ DirectSum.component K I (fun i => A i) i ∘ₗ φ.symm.toLinearMap
  have he : ∀ i x, e i x = ((φ.symm x) i : V) := fun i x => rfl
  have hlof : ∀ (i : I) (x : V) (hx : x ∈ A i), φ.symm x = DirectSum.lof K I (fun i => A i) i ⟨x, hx⟩ := by
    intro i x hx
    rw [LinearEquiv.symm_apply_eq, hφ, DirectSum.coeLinearMap_lof]
  refine ⟨e, ⟨?_, ?_, ?_, ?_⟩⟩
  · intro mu x hx
    rw [he, hlof mu x hx, DirectSum.lof_eq_of, DirectSum.of_eq_same]
  · intro mu nu hne x hx
    rw [he, hlof nu x hx, DirectSum.lof_eq_of, DirectSum.of_eq_of_ne _ _ _ hne.symm]
    rfl
  · intro x
    refine ⟨(φ.symm x).support, ?_⟩
    have h1 : x = φ (φ.symm x) := (φ.apply_symm_apply x).symm
    conv_lhs => rw [h1, hφ, DirectSum.coeLinearMap_eq_dfinsuppSum]
    rfl
  · intro mu x
    rw [he]
    exact ((φ.symm x) mu).2

end Formalism.MainNotions.G.Joints

end

noncomputable section

open Formalism.MainNotions.G

namespace Formalism.MainNotions.G.Joints

section

variable {n : ℕ} {K V : Type*} [Field K] [AddCommGroup V] [Module K V] (E : GLOps n K V)

/- English proof (translation)
Introduce `a b x hx`. Establish `hle : (⨆ i, f i) ≤ (⨆ i, f i).comap (E a b)` using `iSup_le fun i y hy => Submodule.mem_iSup_of_mem i (h i a b y hy)`. Conclude with `hle hx`.
-/
theorem Stab_iSup {J : Sort*} (f : J → Submodule K V) (h : ∀ i, Stab E (f i)) : Stab E (⨆ i, f i) := by
  intro a b x hx
  have hle : (⨆ i, f i) ≤ (⨆ i, f i).comap (E a b) :=
    iSup_le fun i y hy => Submodule.mem_iSup_of_mem i (h i a b y hy)
  exact hle hx

/- English proof (translation)
Introduce `a b x hx` and use `⟨hA a b x hx.1, hB a b x hx.2⟩`.
-/
theorem Stab_inf (A B : Submodule K V) (hA : Stab E A) (hB : Stab E B) : Stab E (A ⊓ B) :=
  fun a b x hx => ⟨hA a b x hx.1, hB a b x hx.2⟩

/- English proof (translation)
Introduce `a b x hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx`. Rewrite using `[map_add]`. Conclude with `Submodule.add_mem _ (Submodule.mem_sup_left (hA a b y hy)) (Submodule.mem_sup_right (hB a b z hz))`.
-/
theorem Stab_sup (A B : Submodule K V) (hA : Stab E A) (hB : Stab E B) : Stab E (A ⊔ B) := by
  intro a b x hx
  obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx
  rw [map_add]
  exact Submodule.add_mem _ (Submodule.mem_sup_left (hA a b y hy)) (Submodule.mem_sup_right (hB a b z hz))

def isoSet (Om : Set (Fin n → ℤ)) (P : Submodule K V) : Set V :=
  {x | ∃ nu ∈ Om, ∃ v ∈ P, IsHWV E nu v ∧ ∃ u ∈ Umon E, x = u v}

/- English proof (translation)
Introduce and unpack `x ⟨nu, hnu, v, hv, hh⟩`. Conclude with `⟨nu, hnu, v, h hv, hh⟩`.
-/
theorem isoSet_mono (Om : Set (Fin n → ℤ)) {P P' : Submodule K V} (h : P ≤ P') : isoSet E Om P ⊆ isoSet E Om P' := by
  rintro x ⟨nu, hnu, v, hv, hh⟩
  exact ⟨nu, hnu, v, h hv, hh⟩

/- English proof (translation)
Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `x ⟨u, hu, v, hv, rfl⟩`. Conclude with `⟨mu, h, v, trivial, hv, u, hu, rfl⟩`.
-/
theorem isoSub_le_span (mu : Fin n → ℤ) (Om : Set (Fin n → ℤ)) (h : mu ∈ Om) :
    isoSub E mu ≤ Submodule.span K (isoSet E Om ⊤) := by
  refine Submodule.span_mono ?_
  rintro x ⟨u, hu, v, hv, rfl⟩
  exact ⟨mu, h, v, trivial, hv, u, hu, rfl⟩

/- English proof (translation)
Establish `key : ∀ T : Module.End K V, (∀ x ∈ A, T x ∈ A) → (∀ x ∈ C, T x ∈ C) → T (a + c) = 0 → T a = 0`. Introduce `T hTA hTC h0`. Rewrite `h0` using `[map_add]`. Establish `h1 : T a = -T c` using `eq_neg_of_add_eq_zero_left h0`. Establish `h2 : T a ∈ A ⊓ C` using `⟨hTA a ha, by rw [h1]; exact C.neg_mem (hTC c hc)⟩`.

Rewrite `h2` using `[hAC]`. Conclude with `(Submodule.mem_bot K).1 h2`. Prove the components needed by the constructor for the conclusion. Unfold `weightSp`. Rewrite using `[Submodule.mem_iInf]`.

Introduce `i`. Rewrite using `[LinearMap.mem_ker]`. Apply `key` to reduce the goal to its premises. Introduce `x hx`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`.

Conclude with `A.sub_mem (hA i i x hx) (A.smul_mem _ hx)`. Introduce `x hx`. Simplify using `only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]`. Conclude with `C.sub_mem (hC i i x hx) (C.smul_mem _ hx)`. Establish `h3` using `hv.2.1`.

Unfold `weightSp at h3`. Rewrite `h3` using `[Submodule.mem_iInf]`. Conclude with `LinearMap.mem_ker.1 (h3 i)`. Introduce `i j hij`. Conclude with `key (E i j) (hA i j) (hC i j) (hv.2.2 i j hij)`.
-/
theorem split_hwv (A C : Submodule K V) (hA : Stab E A) (hC : Stab E C) (hAC : A ⊓ C = ⊥) (nu : Fin n → ℤ)
    (a c : V) (ha : a ∈ A) (hc : c ∈ C) (hv : IsHWV E nu (a + c)) :
    a ∈ weightSp E nu ∧ ∀ i j, i < j → E i j a = 0 := by
  have key : ∀ T : Module.End K V, (∀ x ∈ A, T x ∈ A) → (∀ x ∈ C, T x ∈ C) → T (a + c) = 0 → T a = 0 := by
    intro T hTA hTC h0
    rw [map_add] at h0
    have h1 : T a = -T c := eq_neg_of_add_eq_zero_left h0
    have h2 : T a ∈ A ⊓ C := ⟨hTA a ha, by rw [h1]; exact C.neg_mem (hTC c hc)⟩
    rw [hAC] at h2
    exact (Submodule.mem_bot K).1 h2
  constructor
  · unfold weightSp
    rw [Submodule.mem_iInf]
    intro i
    rw [LinearMap.mem_ker]
    apply key
    · intro x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact A.sub_mem (hA i i x hx) (A.smul_mem _ hx)
    · intro x hx
      simp only [LinearMap.sub_apply, LinearMap.smul_apply, Module.End.one_apply]
      exact C.sub_mem (hC i i x hx) (C.smul_mem _ hx)
    · have h3 := hv.2.1
      unfold weightSp at h3
      rw [Submodule.mem_iInf] at h3
      exact LinearMap.mem_ker.1 (h3 i)
  · intro i j hij
    exact key (E i j) (hA i j) (hC i j) (hv.2.2 i j hij)

/- English proof (translation)
Assume the negation of the conclusion as `hge`. Establish `hle : Submodule.span K {w} ⊔ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu ≤ ⨆ (mu : Fin n → ℤ) (_ : mu ≠ nu), weightSp E mu`. Use `sup_le ?_ (iSup_le fun mu => iSup_le fun hmu => ?_)` and prove the remaining obligations. Rewrite using `[Submodule.span_singleton_le_iff_mem]`. Conclude with `Submodule.mem_iSup_of_mem lam (Submodule.mem_iSup_of_mem (Ne.symm hne) hw)`.

Conclude with `le_iSup_of_le mu (le_iSup_of_le (fun h : mu = nu => hge (h ▸ hmu)) le_rfl)`. Establish `hd` using `(weightSp_indep E) nu`. Conclude with `hx0 ((Submodule.mem_bot K).1 (hd.le_bot ⟨hx, hle hmem⟩))`.
-/
theorem wt_in_top [CharZero K] (lam nu : Fin n → ℤ) (w x : V) (hw : w ∈ weightSp E lam) (hx : x ∈ weightSp E nu)
    (hx0 : x ≠ 0) (hne : nu ≠ lam)
    (hmem : x ∈ Submodule.span K {w} ⊔ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu) :
    htW nu < htW lam := by
  by_contra hge
  have hle : Submodule.span K {w} ⊔ ⨆ (mu : Fin n → ℤ) (_ : htW mu < htW lam), weightSp E mu ≤
      ⨆ (mu : Fin n → ℤ) (_ : mu ≠ nu), weightSp E mu := by
    refine sup_le ?_ (iSup_le fun mu => iSup_le fun hmu => ?_)
    · rw [Submodule.span_singleton_le_iff_mem]
      exact Submodule.mem_iSup_of_mem lam (Submodule.mem_iSup_of_mem (Ne.symm hne) hw)
    · exact le_iSup_of_le mu (le_iSup_of_le (fun h : mu = nu => hge (h ▸ hmu)) le_rfl)
  have hd := (weightSp_indep E) nu
  exact hx0 ((Submodule.mem_bot K).1 (hd.le_bot ⟨hx, hle hmem⟩))

end

section Main

variable {n : ℕ} {K V : Type} [Field K] [CharZero K] [AddCommGroup V] [Module K V] (E : GLOps n K V)

/- English proof (translation)
The claim follows from `cr_in D h2 E hE.1 P hP (fun x hx => stab_wt_decomp E hE.2.2 P (fun a y hy => hP a a y hy) x hx) W hWP hW`.
-/
theorem cr_of (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (hE : IsGLRep E) (P : Submodule K V) [FiniteDimensional K P]
    (hP : Stab E P) (W : Submodule K V) (hWP : W ≤ P) (hW : Stab E W) :
    ∃ W' : Submodule K V, W' ≤ P ∧ Stab E W' ∧ W ⊓ W' = ⊥ ∧ W ⊔ W' = P :=
  cr_in D h2 E hE.1 P hP (fun x hx => stab_wt_decomp E hE.2.2 P (fun a y hy => hP a a y hy) x hx) W hWP hW

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `x _`. Take `⟨P, hfd, hxP, hP⟩` from `hE.2.1 x`. Use `hfd` as an intermediate fact. Establish `hWst : Stab E (P ⊓ ⨆ mu, isoSub E mu)` using `Stab_inf E _ _ hP (Stab_iSup E _ fun mu => isoSub_stab E mu)`.

Take `⟨W', hW'P, hW', hdis, hsup⟩` from `cr_of E D h2 hE P hP _ inf_le_left hWst`. Distinguish the cases in `hbot : W' = ⊥`. Rewrite `hsup` using `[hbot, sup_bot_eq]`. Rewrite `hxP` using `[← hsup]`. Conclude with `hxP.2`.

It suffices to derive a contradiction. Establish `: FiniteDimensional K W'` using `Submodule.finiteDimensional_of_le hW'P`. Take `⟨mu, v, hvW, hv⟩` from `exists_hwv E hE.1 hE.2.2 W' hW' hbot`. Establish `h1 : v ∈ (P ⊓ ⨆ mu, isoSub E mu) ⊓ W'` using `⟨⟨hW'P hvW, Submodule.mem_iSup_of_mem mu (genSub_le_isoSub E mu v hv (mem_genSub_self E v))⟩, hvW⟩`. Rewrite `h1` using `[hdis]`.

Conclude with `hv.1 ((Submodule.mem_bot K).1 h1)`.
-/
theorem isoSub_top (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (hE : IsGLRep E) : (⨆ mu, isoSub E mu) = ⊤ := by
  rw [eq_top_iff]
  intro x _
  obtain ⟨P, hfd, hxP, hP⟩ := hE.2.1 x
  have := hfd
  have hWst : Stab E (P ⊓ ⨆ mu, isoSub E mu) := Stab_inf E _ _ hP (Stab_iSup E _ fun mu => isoSub_stab E mu)
  obtain ⟨W', hW'P, hW', hdis, hsup⟩ := cr_of E D h2 hE P hP _ inf_le_left hWst
  by_cases hbot : W' = ⊥
  · rw [hbot, sup_bot_eq] at hsup
    rw [← hsup] at hxP
    exact hxP.2
  · exfalso
    have : FiniteDimensional K W' := Submodule.finiteDimensional_of_le hW'P
    obtain ⟨mu, v, hvW, hv⟩ := exists_hwv E hE.1 hE.2.2 W' hW' hbot
    have h1 : v ∈ (P ⊓ ⨆ mu, isoSub E mu) ⊓ W' :=
      ⟨⟨hW'P hvW, Submodule.mem_iSup_of_mem mu (genSub_le_isoSub E mu v hv (mem_genSub_self E v))⟩, hvW⟩
    rw [hdis] at h1
    exact hv.1 ((Submodule.mem_bot K).1 h1)

/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨nu, hnu, v, -, hv, u, hu, rfl⟩` from `hy`. Take `⟨P, hfd, hvP, hst⟩` from `hE.2.1 v`. Conclude with `⟨P, hfd, hst, Submodule.subset_span ⟨nu, hnu, v, hvP, hv, u, hu, rfl⟩⟩`.

Consider the case `zero`. Conclude with `⟨⊥, inferInstance, fun a b x hx => by`. Rewrite using `[(Submodule.mem_bot K).1 hx, map_zero]`. Conclude with `Submodule.zero_mem _, Submodule.zero_mem _⟩`. Consider the case `add y z _ _ hy hz`.

Take `⟨P1, f1, s1, m1⟩` from `hy`. Take `⟨P2, f2, s2, m2⟩` from `hz`. Use `f1` as an intermediate fact. Use `f2` as an intermediate fact. Conclude with `⟨P1 ⊔ P2, inferInstance, Stab_sup E _ _ s1 s2, Submodule.add_mem _ (Submodule.span_mono (isoSet_mono E Om le_sup_left) m1) (Submodule.span_mono (isoSet_mono E Om le_sup_right) m2)⟩`.

Consider the case `smul c y _ hy`. Take `⟨P, f, s, m⟩` from `hy`. Conclude with `⟨P, f, s, Submodule.smul_mem _ _ m⟩`.
-/
theorem isoSet_env (hE : IsGLRep E) (Om : Set (Fin n → ℤ)) (x : V) (hx : x ∈ Submodule.span K (isoSet E Om ⊤)) :
    ∃ P : Submodule K V, FiniteDimensional K P ∧ Stab E P ∧ x ∈ Submodule.span K (isoSet E Om P) := by
  induction hx using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨nu, hnu, v, -, hv, u, hu, rfl⟩ := hy
    obtain ⟨P, hfd, hvP, hst⟩ := hE.2.1 v
    exact ⟨P, hfd, hst, Submodule.subset_span ⟨nu, hnu, v, hvP, hv, u, hu, rfl⟩⟩
  | zero =>
    exact ⟨⊥, inferInstance, fun a b x hx => by
      rw [(Submodule.mem_bot K).1 hx, map_zero]; exact Submodule.zero_mem _, Submodule.zero_mem _⟩
  | add y z _ _ hy hz =>
    obtain ⟨P1, f1, s1, m1⟩ := hy
    obtain ⟨P2, f2, s2, m2⟩ := hz
    have := f1
    have := f2
    exact ⟨P1 ⊔ P2, inferInstance, Stab_sup E _ _ s1 s2,
      Submodule.add_mem _ (Submodule.span_mono (isoSet_mono E Om le_sup_left) m1)
        (Submodule.span_mono (isoSet_mono E Om le_sup_right) m2)⟩
  | smul c y _ hy =>
    obtain ⟨P, f, s, m⟩ := hy
    exact ⟨P, f, s, Submodule.smul_mem _ _ m⟩

/- English proof (translation)
Assume the negation of the conclusion as `hlam`. Take `⟨P, hfd, hP, hwN⟩` from `isoSet_env E hE Om w hmem`. Use `hfd` as an intermediate fact. Establish `hgen : ∀ C : Submodule K V, Stab E C → (∀ nu ∈ Om, ∀ v ∈ P, IsHWV E nu v → v ∈ C) → Submodule.span K (isoSet E Om P) ≤ C`. Introduce `C hC hall`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `x ⟨nu, hnu, v, hvP, hv, u, hu, rfl⟩`. Conclude with `genSub_le E v C hC (hall nu hnu v hvP hv) (Submodule.subset_span ⟨u, hu, rfl⟩)`. Establish `hwP : w ∈ P` using `hgen P hP (fun _ _ v hv _ => hv) hwN`. Establish `hUwP : genSub E w ≤ P` using `genSub_le E w P hP hwP`.

Take `⟨C, hCP, hC, hdis, hsup⟩` from `cr_of E D h2 hE P hP (genSub E w) hUwP (genSub_stab E w)`. Establish `step2 : ∃ nu ∈ Om, ∃ a ∈ genSub E w, IsHWV E nu a`. Assume the negation of the conclusion as `hno`. Use `push Not at hno`. Establish `hall : ∀ nu ∈ Om, ∀ v ∈ P, IsHWV E nu v → v ∈ C`.

Introduce `nu hnu v hvP hv`. Rewrite `hvP` using `[← hsup]`. Take `⟨a, ha, c, hc, rfl⟩` from `Submodule.mem_sup.1 hvP`. Establish `hs` using `split_hwv E _ C (genSub_stab E w) hC hdis nu a c ha hc hv`. Establish `ha0 : a = 0`.

Assume the negation of the conclusion as `h0`. Conclude with `hno nu hnu a ha ⟨h0, hs.1, hs.2⟩`. Rewrite using `[ha0, zero_add]`. Conclude with `hc`. Establish `h5 : w ∈ genSub E w ⊓ C` using `⟨mem_genSub_self E w, hgen C hC hall hwN⟩`.

Rewrite `h5` using `[hdis]`. Conclude with `hw.1 ((Submodule.mem_bot K).1 h5)`. Take `⟨nu, hnu, a, haU, ha⟩` from `step2`. Establish `hne : nu ≠ lam` using `fun h => hlam (h ▸ hnu)`. Establish `h3 : htW nu < htW lam` using `wt_in_top E lam nu w a hw.2.1 ha.2.1 ha.1 hne (genSub_le_top E hE.1 lam w hw haU)`.

Establish `hUaP : genSub E a ≤ P` using `(genSub_le E a _ (genSub_stab E w) haU).trans hUwP`. Take `⟨C', hCP', hC', hdis', hsup'⟩` from `cr_of E D h2 hE P hP (genSub E a) hUaP (genSub_stab E a)`. Establish `hwP'` using `hwP`. Rewrite `hwP'` using `[← hsup']`. Take `⟨a', ha', c', hc', hsum⟩` from `Submodule.mem_sup.1 hwP'`.

Establish `hs` using `split_hwv E _ C' (genSub_stab E a) hC' hdis' lam a' c' ha' hc' (by rw [hsum]; exact hw)`. Establish `ha0 : a' = 0`. Assume the negation of the conclusion as `h0`. Establish `h6` using `wt_in_top E nu lam a a' ha.2.1 hs.1 h0 (Ne.symm hne) (genSub_le_top E hE.1 nu a ha ha')`. Use linear arithmetic over natural numbers and integers.

Establish `hwC : w ∈ C'`. Rewrite using `[← hsum, ha0, zero_add]`. Conclude with `hc'`. Establish `h7 : a ∈ genSub E a ⊓ C'` using `⟨mem_genSub_self E a, genSub_le E w C' hC' hwC haU⟩`. Rewrite `h7` using `[hdis']`.

Conclude with `ha.1 ((Submodule.mem_bot K).1 h7)`.
-/
theorem hwv_wt_mem (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (hE : IsGLRep E) (Om : Set (Fin n → ℤ))
    (lam : Fin n → ℤ) (w : V) (hw : IsHWV E lam w) (hmem : w ∈ Submodule.span K (isoSet E Om ⊤)) : lam ∈ Om := by
  by_contra hlam
  obtain ⟨P, hfd, hP, hwN⟩ := isoSet_env E hE Om w hmem
  have := hfd
  have hgen : ∀ C : Submodule K V, Stab E C → (∀ nu ∈ Om, ∀ v ∈ P, IsHWV E nu v → v ∈ C) →
      Submodule.span K (isoSet E Om P) ≤ C := by
    intro C hC hall
    rw [Submodule.span_le]
    rintro x ⟨nu, hnu, v, hvP, hv, u, hu, rfl⟩
    exact genSub_le E v C hC (hall nu hnu v hvP hv) (Submodule.subset_span ⟨u, hu, rfl⟩)
  have hwP : w ∈ P := hgen P hP (fun _ _ v hv _ => hv) hwN
  have hUwP : genSub E w ≤ P := genSub_le E w P hP hwP
  obtain ⟨C, hCP, hC, hdis, hsup⟩ := cr_of E D h2 hE P hP (genSub E w) hUwP (genSub_stab E w)
  have step2 : ∃ nu ∈ Om, ∃ a ∈ genSub E w, IsHWV E nu a := by
    by_contra hno
    push Not at hno
    have hall : ∀ nu ∈ Om, ∀ v ∈ P, IsHWV E nu v → v ∈ C := by
      intro nu hnu v hvP hv
      rw [← hsup] at hvP
      obtain ⟨a, ha, c, hc, rfl⟩ := Submodule.mem_sup.1 hvP
      have hs := split_hwv E _ C (genSub_stab E w) hC hdis nu a c ha hc hv
      have ha0 : a = 0 := by
        by_contra h0
        exact hno nu hnu a ha ⟨h0, hs.1, hs.2⟩
      rw [ha0, zero_add]
      exact hc
    have h5 : w ∈ genSub E w ⊓ C := ⟨mem_genSub_self E w, hgen C hC hall hwN⟩
    rw [hdis] at h5
    exact hw.1 ((Submodule.mem_bot K).1 h5)
  obtain ⟨nu, hnu, a, haU, ha⟩ := step2
  have hne : nu ≠ lam := fun h => hlam (h ▸ hnu)
  have h3 : htW nu < htW lam :=
    wt_in_top E lam nu w a hw.2.1 ha.2.1 ha.1 hne (genSub_le_top E hE.1 lam w hw haU)
  have hUaP : genSub E a ≤ P := (genSub_le E a _ (genSub_stab E w) haU).trans hUwP
  obtain ⟨C', hCP', hC', hdis', hsup'⟩ := cr_of E D h2 hE P hP (genSub E a) hUaP (genSub_stab E a)
  have hwP' := hwP
  rw [← hsup'] at hwP'
  obtain ⟨a', ha', c', hc', hsum⟩ := Submodule.mem_sup.1 hwP'
  have hs := split_hwv E _ C' (genSub_stab E a) hC' hdis' lam a' c' ha' hc' (by rw [hsum]; exact hw)
  have ha0 : a' = 0 := by
    by_contra h0
    have h6 := wt_in_top E nu lam a a' ha.2.1 hs.1 h0 (Ne.symm hne) (genSub_le_top E hE.1 nu a ha ha')
    omega
  have hwC : w ∈ C' := by
    rw [← hsum, ha0, zero_add]
    exact hc'
  have h7 : a ∈ genSub E a ⊓ C' := ⟨mem_genSub_self E a, genSub_le E w C' hC' hwC haU⟩
  rw [hdis'] at h7
  exact ha.1 ((Submodule.mem_bot K).1 h7)

/- English proof (translation)
Introduce `mu`. Rewrite using `[disjoint_iff]`. Assume the negation of the conclusion as `hne`. Establish `hMst : Stab E (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu)` using `Stab_inf E _ _ (isoSub_stab E mu) (Stab_iSup E _ fun nu => Stab_iSup E _ fun _ => isoSub_stab E nu)`. Take `⟨x, hxM, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hne`.

Take `⟨P, hfd, hxP, hP⟩` from `hE.2.1 x`. Use `hfd` as an intermediate fact. Establish `: FiniteDimensional K ↥((isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P)` using `Submodule.finiteDimensional_of_le inf_le_right`. Establish `hne2 : (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P ≠ ⊥`. Introduce `h`.

Establish `h8 : x ∈ (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P` using `⟨hxM, hxP⟩`. Rewrite `h8` using `[h]`. Conclude with `hx0 ((Submodule.mem_bot K).1 h8)`. Take `⟨lam, w, hwMP, hw⟩` from `exists_hwv E hE.1 hE.2.2 _ (Stab_inf E _ _ hMst hP) hne2`. Establish `h1 : lam ∈ ({mu} : Set (Fin n → ℤ))` using `hwv_wt_mem E D h2 hE {mu} lam w hw (isoSub_le_span E mu {mu} rfl hwMP.1.1)`.

Establish `hle : (⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ≤ Submodule.span K (isoSet E {nu | nu ≠ mu} ⊤)` using `iSup_le fun nu => iSup_le fun h => isoSub_le_span E nu _ h`. Establish `h2' : lam ∈ {nu : Fin n → ℤ | nu ≠ mu}` using `hwv_wt_mem E D h2 hE _ lam w hw (hle hwMP.1.2)`. Conclude with `h2' h1`.
-/
theorem isoSub_indep (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (hE : IsGLRep E) : iSupIndep (isoSub E) := by
  intro mu
  rw [disjoint_iff]
  by_contra hne
  have hMst : Stab E (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) :=
    Stab_inf E _ _ (isoSub_stab E mu) (Stab_iSup E _ fun nu => Stab_iSup E _ fun _ => isoSub_stab E nu)
  obtain ⟨x, hxM, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hne
  obtain ⟨P, hfd, hxP, hP⟩ := hE.2.1 x
  have := hfd
  have : FiniteDimensional K ↥((isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P) :=
    Submodule.finiteDimensional_of_le inf_le_right
  have hne2 : (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P ≠ ⊥ := by
    intro h
    have h8 : x ∈ (isoSub E mu ⊓ ⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ⊓ P := ⟨hxM, hxP⟩
    rw [h] at h8
    exact hx0 ((Submodule.mem_bot K).1 h8)
  obtain ⟨lam, w, hwMP, hw⟩ := exists_hwv E hE.1 hE.2.2 _ (Stab_inf E _ _ hMst hP) hne2
  have h1 : lam ∈ ({mu} : Set (Fin n → ℤ)) :=
    hwv_wt_mem E D h2 hE {mu} lam w hw (isoSub_le_span E mu {mu} rfl hwMP.1.1)
  have hle : (⨆ (nu : Fin n → ℤ) (_ : nu ≠ mu), isoSub E nu) ≤ Submodule.span K (isoSet E {nu | nu ≠ mu} ⊤) :=
    iSup_le fun nu => iSup_le fun h => isoSub_le_span E nu _ h
  have h2' : lam ∈ {nu : Fin n → ℤ | nu ≠ mu} := hwv_wt_mem E D h2 hE _ lam w hw (hle hwMP.1.2)
  exact h2' h1

/- English proof (translation)
The claim follows from `decomp_of_indep_top (isoSub E) (isoSub_indep E D h2 hE) (isoSub_top E D h2 hE)`.
-/
theorem isoDecomp (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) (hE : IsGLRep E) :
    ∃ e : (Fin n → ℤ) → Module.End K V, DecSys (isoSub E) e :=
  decomp_of_indep_top (isoSub E) (isoSub_indep E D h2 hE) (isoSub_top E D h2 hE)

end Main

/- English proof (translation)
Introduce `K _ _ ι _ LL r _ S`. Take `⟨e, sys⟩` from `isoDecomp (glOps K r LL S) D h2 (isGLRep_glOps K ι LL r S)`. Use `⟨e, fun mu => ⟨sys.id_on mu, fun nu hne x hx => sys.zero_on mu nu hne x hx⟩, fun G => ?_⟩` and prove the remaining obligations. Take `⟨T, hT⟩` from `sys.cover G`. Conclude with `⟨T, hT, fun mu => sys.mem mu G⟩`.
-/
theorem polIsoDecompB_of (D : Formalism.BasicNotions.D7) (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) : PolIsoDecompB := by
  intro K _ _ ι _ LL r _ S
  obtain ⟨e, sys⟩ := isoDecomp (glOps K r LL S) D h2 (isGLRep_glOps K ι LL r S)
  refine ⟨e, fun mu => ⟨sys.id_on mu, fun nu hne x hx => sys.zero_on mu nu hne x hx⟩, fun G => ?_⟩
  obtain ⟨T, hT⟩ := sys.cover G
  exact ⟨T, hT, fun mu => sys.mem mu G⟩

/- English proof (translation)
The claim follows from `projection_of_isotypic_decomposition D hC hV (polIsoDecompB_of D h2)`.
-/
theorem projection_of_integral_corollary (D : Formalism.BasicNotions.D7) (hC : Formalism.MainNotions.CovariantDegrees.FilteredProjectorCorollaryField D) (hV : Formalism.MainNotions.CovariantDegrees.ShaLengthVersionTwo D)
    (h2 : Formalism.MainNotions.CovariantDegrees.adm2 D) : Formalism.MainNotions.PlaneGramData.ArchimedeanSignatureMatching D :=
  projection_of_isotypic_decomposition D hC hV (polIsoDecompB_of D h2)

end Formalism.MainNotions.G.Joints

end
