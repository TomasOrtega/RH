import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.Divisibility.Tuples
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeCharacterUnramifiedAeAndExistsLevelStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LocalIdeleSndSelf

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr Classical

noncomputable section

namespace GlobalTheory.Mem.ValAlg

variable {L : Type} [Field L] [NumberField L]

def uOf (a : 𝓞 L) (ha : a ≠ 0) : Lˣ := Units.mk0 (algebraMap (𝓞 L) L a) (by simpa using ha)

/- English proof (translation)
Establish `h1 : ordF w (uOf a ha) = FractionalIdeal.count L w ((Ideal.span {a} : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L)`. Rewrite using `[FractionalIdeal.count_coe L w (by simpa using ha)]`. Use `show -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) = _`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]`. Simplify using the standard rewrite rules.

Establish `h2 : ∀ u : HeightOneSpectrum (𝓞 L), FractionalIdeal.count L w (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = if u = w then 1 else 0`. Introduce `u`. Use `split_ifs with hu`. Rewrite using `[hu, FractionalIdeal.count_self]`. Conclude with `FractionalIdeal.count_maximal_coprime L w hu`.

Establish `h3 : ∀ u : HeightOneSpectrum (𝓞 L), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ≠ 0` using `fun u => FractionalIdeal.coeIdeal_ne_zero.2 u.ne_bot`. Rewrite using `[h1, h, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow, FractionalIdeal.count_mul L w (h3 v) (pow_ne_zero _ (h3 v')), FractionalIdeal.count_pow, h2, h2]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ordF_of_span (v v' w : HeightOneSpectrum (𝓞 L)) (j : ℕ) (a : 𝓞 L) (ha : a ≠ 0)
    (h : Ideal.span {a} = v.asIdeal * v'.asIdeal ^ j) :
    ordF w (uOf a ha) = (if v = w then 1 else 0) + (if v' = w then (j : ℤ) else 0) := by
  have h1 : ordF w (uOf a ha) = FractionalIdeal.count L w ((Ideal.span {a} : Ideal (𝓞 L)) : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) := by
    rw [FractionalIdeal.count_coe L w (by simpa using ha)]
    show -WithZero.log (w.valuation L (algebraMap (𝓞 L) L a)) = _
    rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_if_neg _ ha]
    simp
  have h2 : ∀ u : HeightOneSpectrum (𝓞 L), FractionalIdeal.count L w (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) = if u = w then 1 else 0 := by
    intro u
    split_ifs with hu
    · rw [hu, FractionalIdeal.count_self]
    · exact FractionalIdeal.count_maximal_coprime L w hu
  have h3 : ∀ u : HeightOneSpectrum (𝓞 L), (u.asIdeal : FractionalIdeal (nonZeroDivisors (𝓞 L)) L) ≠ 0 := fun u =>
    FractionalIdeal.coeIdeal_ne_zero.2 u.ne_bot
  rw [h1, h, FractionalIdeal.coeIdeal_mul, FractionalIdeal.coeIdeal_pow,
    FractionalIdeal.count_mul L w (h3 v) (pow_ne_zero _ (h3 v')), FractionalIdeal.count_pow, h2, h2]
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS (uOf a ha)]`. Use `congr 1`. Establish `e : ∀ w, (∏ᶠ (_ : w ∉ S), χ.val w ^ ordF w (uOf a ha)) = (if v = w then χ.val v else 1) * (if v' = w then χ.val v' ^ j else 1)`. Introduce `w`. Rewrite using `[ordF_of_span v v' w j a ha h]`.

Distinguish the cases in `hw : w ∈ S`. Establish `h1 : v ≠ w` using `fun e => hv (e ▸ hw)`. Establish `h2 : v' ≠ w` using `fun e => hv' (e ▸ hw)`. Simplify using `[h1, h2]`. Rewrite using `[finprod_eq_if, if_pos hw, zpow_add]`.

Use `congr 1`. Use `split_ifs with h1`. Simplify using `[h1]`. Simplify using the standard rewrite rules. Use `split_ifs with h1`.

Simplify using `[h1]`. Simplify using the standard rewrite rules. Repeatedly rewrite using `[e]`. Rewrite using `[finprod_mul_distrib, finprod_eq_single _ v, finprod_eq_single _ v']`. Simplify using the standard rewrite rules.

Introduce `x hx`. Simplify using `[Ne.symm hx]`. Introduce `x hx`. Simplify using `[Ne.symm hx]`. Use `(Set.finite_singleton v).subset fun x hx => ?_` and prove the remaining obligations.

Assume the negation of the conclusion as `h1`. Conclude with `hx (if_neg fun e => h1 e.symm)`. Use `(Set.finite_singleton v').subset fun x hx => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `h1`. Conclude with `hx (if_neg fun e => h1 e.symm)`.
-/
theorem prod_rule_two (χ : HChar L) (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : v ∉ S) (hv' : v' ∉ S) (j : ℕ) (a : 𝓞 L) (ha : a ≠ 0)
    (h : Ideal.span {a} = v.asIdeal * v'.asIdeal ^ j) :
    χ.inf (uOf a ha) * (∏ w ∈ S, χ.locK w (uOf a ha)) * (χ.val v * χ.val v' ^ j) = 1 := by
  rw [← GlobalTheory.HeckeProduct.hchar_productRule L χ S hS (uOf a ha)]
  congr 1
  have e : ∀ w, (∏ᶠ (_ : w ∉ S), χ.val w ^ ordF w (uOf a ha)) =
      (if v = w then χ.val v else 1) * (if v' = w then χ.val v' ^ j else 1) := by
    intro w
    rw [ordF_of_span v v' w j a ha h]
    by_cases hw : w ∈ S
    · have h1 : v ≠ w := fun e => hv (e ▸ hw)
      have h2 : v' ≠ w := fun e => hv' (e ▸ hw)
      simp [h1, h2]
    · rw [finprod_eq_if, if_pos hw, zpow_add]
      congr 1
      · split_ifs with h1
        · simp [h1]
        · simp
      · split_ifs with h1
        · simp [h1]
        · simp
  simp_rw [e]
  rw [finprod_mul_distrib, finprod_eq_single _ v, finprod_eq_single _ v']
  · simp
  · intro x hx; simp [Ne.symm hx]
  · intro x hx; simp [Ne.symm hx]
  · refine (Set.finite_singleton v).subset fun x hx => ?_
    by_contra h1
    exact hx (if_neg fun e => h1 e.symm)
  · refine (Set.finite_singleton v').subset fun x hx => ?_
    by_contra h1
    exact hx (if_neg fun e => h1 e.symm)

/- English proof (translation)
Take `⟨n, hn⟩` from `(GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ).2 w`. Establish `: Finite (𝓞 L ⧸ w.asIdeal ^ n)` using `Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)`. Use `⟨Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ, Nat.card_pos, fun a ha hw => ?_⟩` and prove the remaining obligations. Establish `hco : IsCoprime (Ideal.span {a}) (w.asIdeal ^ n)`. Use `IsCoprime.pow_right ?_` and prove the remaining obligations.

Rewrite using `[Ideal.isCoprime_iff_sup_eq, sup_comm]`. Use `w.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun e => hw ?_)` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)`. Take `⟨x, hx, y, hy, hxy⟩` from `Ideal.isCoprime_iff_exists.1 hco`.

Take `⟨b, rfl⟩` from `Ideal.mem_span_singleton'.1 hx`. Establish `hu : IsUnit (Ideal.Quotient.mk (w.asIdeal ^ n) a)`. Use `IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk _ b) ?_` and prove the remaining obligations. Rewrite using `[← map_mul, ← (Ideal.Quotient.mk _).map_one, ← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]`. Take `⟨u, hu⟩` from `hu`.

Establish `h1 : a ^ Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ - 1 ∈ w.asIdeal ^ n`. Rewrite using `[← Ideal.Quotient.eq, map_pow, ← hu, ← Units.val_pow_eq_pow_val, pow_card_eq_one', map_one, Units.val_one]`. Use `set N := Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ`. Rewrite using `[← map_pow]`. Establish `hval : ∀ z : 𝓞 L, Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L z)) = w.intValuation z`.

Introduce `z`. Rewrite using `[← HeightOneSpectrum.valuation_of_algebraMap (K := L)]`. Conclude with `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _`. Establish `hc : ((atFin w (uOf a ha ^ N) : (w.adicCompletion L)ˣ) : w.adicCompletion L) = algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a ^ N))`. Rewrite using `[map_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]`.

Both sides reduce to the same expression. Use `hn _ ?_ ?_` and prove the remaining obligations. Unfold `IsUnitAt`. Rewrite using `[hc, hval, map_pow, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]`. Rewrite using `[hc, ← (algebraMap L (w.adicCompletion L)).map_one, ← map_sub, ← (algebraMap (𝓞 L) L).map_one, ← map_sub, hval]`.

Conclude with `(w.intValuation_le_pow_iff_mem _ _).2 h1`.
-/
theorem locK_pow (χ : HChar L) (w : HeightOneSpectrum (𝓞 L)) :
    ∃ N : ℕ, 0 < N ∧ ∀ (a : 𝓞 L) (ha : a ≠ 0), a ∉ w.asIdeal → χ.locK w (uOf a ha) ^ N = 1 := by
  obtain ⟨n, hn⟩ := (GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ).2 w
  have : Finite (𝓞 L ⧸ w.asIdeal ^ n) := Ideal.finiteQuotientOfFreeOfNeBot _ (pow_ne_zero _ w.ne_bot)
  refine ⟨Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ, Nat.card_pos, fun a ha hw => ?_⟩
  have hco : IsCoprime (Ideal.span {a}) (w.asIdeal ^ n) := by
    refine IsCoprime.pow_right ?_
    rw [Ideal.isCoprime_iff_sup_eq, sup_comm]
    refine w.isMaximal.out.2 _ (lt_of_le_of_ne le_sup_left fun e => hw ?_)
    rw [e]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self a)
  obtain ⟨x, hx, y, hy, hxy⟩ := Ideal.isCoprime_iff_exists.1 hco
  obtain ⟨b, rfl⟩ := Ideal.mem_span_singleton'.1 hx
  have hu : IsUnit (Ideal.Quotient.mk (w.asIdeal ^ n) a) := by
    refine IsUnit.of_mul_eq_one_right (Ideal.Quotient.mk _ b) ?_
    rw [← map_mul, ← (Ideal.Quotient.mk _).map_one, ← hxy, map_add, Ideal.Quotient.eq_zero_iff_mem.2 hy, add_zero]
  obtain ⟨u, hu⟩ := hu
  have h1 : a ^ Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ - 1 ∈ w.asIdeal ^ n := by
    rw [← Ideal.Quotient.eq, map_pow, ← hu, ← Units.val_pow_eq_pow_val, pow_card_eq_one', map_one, Units.val_one]
  set N := Nat.card (𝓞 L ⧸ w.asIdeal ^ n)ˣ
  rw [← map_pow]
  have hval : ∀ z : 𝓞 L, Valued.v (algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L z)) = w.intValuation z := by
    intro z
    rw [← HeightOneSpectrum.valuation_of_algebraMap (K := L)]
    exact HeightOneSpectrum.valuedAdicCompletion_eq_valuation' w _
  have hc : ((atFin w (uOf a ha ^ N) : (w.adicCompletion L)ˣ) : w.adicCompletion L) =
      algebraMap L (w.adicCompletion L) (algebraMap (𝓞 L) L (a ^ N)) := by
    rw [map_pow, map_pow, map_pow, Units.val_pow_eq_pow_val]
    rfl
  refine hn _ ?_ ?_
  · unfold IsUnitAt
    rw [hc, hval, map_pow, HeightOneSpectrum.intValuation_eq_one_iff.2 hw, one_pow]
  · rw [hc, ← (algebraMap L (w.adicCompletion L)).map_one, ← map_sub, ← (algebraMap (𝓞 L) L).map_one, ← map_sub, hval]
    exact (w.intValuation_le_pow_iff_mem _ _).2 h1

/- English proof (translation)
Establish `h` using `InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 L) L a)`. Rewrite `h` using `[← hφ.prod_comp]`. Rewrite using `[Ideal.absNorm_span_singleton, ← Finset.prod_pow]`. Establish `h2 : ∀ i, (InfinitePlace.mk (φ i)) (algebraMap (𝓞 L) L a) ^ (InfinitePlace.mk (φ i)).mult = ‖φ i (algebraMap (𝓞 L) L a)‖ ^ 2`. Introduce `i`.

Rewrite using `[InfinitePlace.apply, IsTotallyComplex.mult_eq]`. Rewrite `h` using `[h2]`. Rewrite using `[h, ← Algebra.coe_norm_int]`. Simplify using `[Nat.cast_natAbs]`.
-/
theorem absNorm_eq (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (a : 𝓞 L) :
    ((Ideal.absNorm (Ideal.span {a}) : ℕ) : ℝ) = (∏ i, ‖φ i (algebraMap (𝓞 L) L a)‖) ^ 2 := by
  have h := InfinitePlace.prod_eq_abs_norm (algebraMap (𝓞 L) L a)
  rw [← hφ.prod_comp] at h
  rw [Ideal.absNorm_span_singleton, ← Finset.prod_pow]
  have h2 : ∀ i, (InfinitePlace.mk (φ i)) (algebraMap (𝓞 L) L a) ^ (InfinitePlace.mk (φ i)).mult =
      ‖φ i (algebraMap (𝓞 L) L a)‖ ^ 2 := by
    intro i
    rw [InfinitePlace.apply, IsTotallyComplex.mult_eq]
  simp_rw [h2] at h
  rw [h, ← Algebra.coe_norm_int]
  simp [Nat.cast_natAbs]

/- English proof (translation)
Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `mul_ne_zero v.ne_bot (pow_ne_zero j v'.ne_bot) (by rw [← h]; simp)`. Establish `hw : ∀ w ∈ S, a ∉ w.asIdeal`. Introduce `w hw hmem`.

Establish `h1 : w.asIdeal ∣ v.asIdeal * v'.asIdeal ^ j`. Rewrite using `[← h, Ideal.dvd_span_singleton]`. Conclude with `hmem`. Establish `h2 : ∀ u : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ u.asIdeal → u = w` using `fun u hu => HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd hu))`. Break down `w.prime.dvd_or_dvd h1 with h3 | h3` into its components or cases.

Conclude with `hv (h2 v h3 ▸ hw)`. Conclude with `hv' (h2 v' (w.prime.dvd_of_dvd_pow h3) ▸ hw)`. Establish `hp` using `congrArg (Units.val : ℂˣ → ℂ) (prod_rule_two χ S hS v v' hv hv' j a ha h)`. Rewrite `hp` using `[Units.val_mul, Units.val_mul, hinf, Units.val_one, Units.val_mul, Units.val_pow_eq_pow_val]`. Establish `hloc : ((∏ w ∈ S, χ.locK w (uOf a ha) : ℂˣ) : ℂ) ∈ M`.

Rewrite using `[Units.coe_prod]`. Conclude with `prod_mem fun w hwS => hM' w hwS a ha (hw w hwS)`. Use `set k : L := algebraMap (𝓞 L) L a with hk`. Establish `hk' : ((uOf a ha : Lˣ) : L) = k` using `rfl`. Rewrite `hp` using `[hk']`.

Establish `hk0 : k ≠ 0` using `by rw [← hk']; exact Units.ne_zero _`. Establish `hN` using `absNorm_eq hL φ hφ a`. Rewrite `hN` using `[h, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, ← hk]`. Establish `hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ)`. Introduce `m`.

Rewrite using `[Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]`. Establish `hreal : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2)) * (((Ideal.absNorm v'.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ j = (∏ i, ‖φ i k‖) ^ (-r)`. Establish `h0 : 0 ≤ ∏ i, ‖φ i k‖` using `Finset.prod_nonneg fun _ _ => norm_nonneg _`. Rewrite using `[Real.rpow_pow_comm (Nat.cast_nonneg _), ← Real.mul_rpow (Nat.cast_nonneg _) (by positivity), hN, ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hc : χ.valTw ((r : ℝ) / 2) v * χ.valTw ((r : ℝ) / 2) v' ^ j = ((χ.val v : ℂˣ) : ℂ) * ((χ.val v' : ℂˣ) : ℂ) ^ j * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r)`. Unfold `HChar.valTw`. Rewrite using `[hpow, hpow, mul_pow, mul_mul_mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_mul, hreal, Finset.prod_zpow, Complex.ofReal_zpow, Complex.ofReal_prod]`.

Rewrite using `[hc, eq_inv_of_mul_eq_one_right hp, mul_inv, mul_right_comm]`. Use `mul_mem ?_ (inv_mem hloc)` and prove the remaining obligations. Rewrite using `[← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `prod_mem fun i _ => ?_` and prove the remaining obligations. Take `⟨m, hm⟩` from `hev i`.

Establish `hz : φ i k ≠ 0` using `(map_ne_zero _).2 hk0`. Establish `hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0` using `by simpa using hk0`. Establish `hsq : ((‖φ i k‖ : ℝ) : ℂ) * ((‖φ i k‖ : ℝ) : ℂ) ∈ M`. Rewrite using `[← sq, ← Complex.mul_conj']`. Conclude with `mul_mem (hM _ _) (hM ((starRingEnd ℂ).comp (φ i)) k)`.

Establish `e : ((φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ n i)⁻¹ * ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) = (φ i k ^ n i)⁻¹ * (((‖φ i k‖ : ℝ) : ℂ) * ((‖φ i k‖ : ℝ) : ℂ)) ^ m`. Rewrite using `[mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `mul_mem (inv_mem (zpow_mem (hM _ _) _)) (zpow_mem hsq _)`.
-/
theorem valTw_two_mem (hL : IsTotallyComplex L) {I : Type} [Fintype I] (φ : I → L →+* ℂ)
    (hφ : Function.Bijective fun i => InfinitePlace.mk (φ i)) (χ : HChar L) (n : I → ℤ) (r : ℤ)
    (hinf : χ.HasInf φ n) (hev : ∀ i, Even (n i - r))
    (S : Finset (HeightOneSpectrum (𝓞 L))) (hS : ∀ v, v ∉ S → χ.UnrAt v)
    (M : IntermediateField ℚ ℂ) (hM : ∀ (f : L →+* ℂ) (x : L), f x ∈ M)
    (hM' : ∀ w ∈ S, ∀ (a : 𝓞 L) (ha : a ≠ 0), a ∉ w.asIdeal → ((χ.locK w (uOf a ha) : ℂˣ) : ℂ) ∈ M)
    (v v' : HeightOneSpectrum (𝓞 L)) (hv : v ∉ S) (hv' : v' ∉ S) (j : ℕ) (a : 𝓞 L)
    (h : Ideal.span {a} = v.asIdeal * v'.asIdeal ^ j) :
    χ.valTw ((r : ℝ) / 2) v * χ.valTw ((r : ℝ) / 2) v' ^ j ∈ M := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero v.ne_bot (pow_ne_zero j v'.ne_bot) (by rw [← h]; simp)
  have hw : ∀ w ∈ S, a ∉ w.asIdeal := by
    intro w hw hmem
    have h1 : w.asIdeal ∣ v.asIdeal * v'.asIdeal ^ j := by
      rw [← h, Ideal.dvd_span_singleton]; exact hmem
    have h2 : ∀ u : HeightOneSpectrum (𝓞 L), w.asIdeal ∣ u.asIdeal → u = w := fun u hu =>
      HeightOneSpectrum.ext (u.isMaximal.eq_of_le w.isPrime.ne_top (Ideal.le_of_dvd hu))
    rcases w.prime.dvd_or_dvd h1 with h3 | h3
    · exact hv (h2 v h3 ▸ hw)
    · exact hv' (h2 v' (w.prime.dvd_of_dvd_pow h3) ▸ hw)
  have hp := congrArg (Units.val : ℂˣ → ℂ) (prod_rule_two χ S hS v v' hv hv' j a ha h)
  rw [Units.val_mul, Units.val_mul, hinf, Units.val_one, Units.val_mul, Units.val_pow_eq_pow_val] at hp
  have hloc : ((∏ w ∈ S, χ.locK w (uOf a ha) : ℂˣ) : ℂ) ∈ M := by
    rw [Units.coe_prod]
    exact prod_mem fun w hwS => hM' w hwS a ha (hw w hwS)
  set k : L := algebraMap (𝓞 L) L a with hk
  have hk' : ((uOf a ha : Lˣ) : L) = k := rfl
  rw [hk'] at hp
  have hk0 : k ≠ 0 := by rw [← hk']; exact Units.ne_zero _
  have hN := absNorm_eq hL φ hφ a
  rw [h, map_mul, map_pow, Nat.cast_mul, Nat.cast_pow, ← hk] at hN
  have hpow : ∀ m : ℕ, (m : ℂ) ^ (-(((r : ℝ) / 2 : ℝ) : ℂ)) = (((m : ℝ) ^ (-((r : ℝ) / 2)) : ℝ) : ℂ) := by
    intro m
    rw [Complex.ofReal_cpow (Nat.cast_nonneg m), Complex.ofReal_natCast, Complex.ofReal_neg]
  have hreal : ((Ideal.absNorm v.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2)) *
      (((Ideal.absNorm v'.asIdeal : ℕ) : ℝ) ^ (-((r : ℝ) / 2))) ^ j = (∏ i, ‖φ i k‖) ^ (-r) := by
    have h0 : 0 ≤ ∏ i, ‖φ i k‖ := Finset.prod_nonneg fun _ _ => norm_nonneg _
    rw [Real.rpow_pow_comm (Nat.cast_nonneg _), ← Real.mul_rpow (Nat.cast_nonneg _) (by positivity), hN,
      ← Real.rpow_natCast, ← Real.rpow_mul h0, ← Real.rpow_intCast]
    congr 1
    push_cast
    ring
  have hc : χ.valTw ((r : ℝ) / 2) v * χ.valTw ((r : ℝ) / 2) v' ^ j =
      ((χ.val v : ℂˣ) : ℂ) * ((χ.val v' : ℂˣ) : ℂ) ^ j * ∏ i, ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) := by
    unfold HChar.valTw
    rw [hpow, hpow, mul_pow, mul_mul_mul_comm, ← Complex.ofReal_pow, ← Complex.ofReal_mul, hreal, Finset.prod_zpow,
      Complex.ofReal_zpow, Complex.ofReal_prod]
  rw [hc, eq_inv_of_mul_eq_one_right hp, mul_inv, mul_right_comm]
  refine mul_mem ?_ (inv_mem hloc)
  rw [← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]
  refine prod_mem fun i _ => ?_
  obtain ⟨m, hm⟩ := hev i
  have hz : φ i k ≠ 0 := (map_ne_zero _).2 hk0
  have hz' : ((‖φ i k‖ : ℝ) : ℂ) ≠ 0 := by simpa using hk0
  have hsq : ((‖φ i k‖ : ℝ) : ℂ) * ((‖φ i k‖ : ℝ) : ℂ) ∈ M := by
    rw [← sq, ← Complex.mul_conj']
    exact mul_mem (hM _ _) (hM ((starRingEnd ℂ).comp (φ i)) k)
  have e : ((φ i k / ((‖φ i k‖ : ℝ) : ℂ)) ^ n i)⁻¹ * ((‖φ i k‖ : ℝ) : ℂ) ^ (-r) =
      (φ i k ^ n i)⁻¹ * (((‖φ i k‖ : ℝ) : ℂ) * ((‖φ i k‖ : ℝ) : ℂ)) ^ m := by
    rw [mul_zpow, ← zpow_add₀ hz', ← hm, sub_eq_add_neg, zpow_add₀ hz', div_zpow, inv_div, div_eq_mul_inv]
    ring
  rw [e]
  exact mul_mem (inv_mem (zpow_mem (hM _ _) _)) (zpow_mem hsq _)

/- English proof (translation)
Establish `h1 : ∀ f : L →+* ℂ, FiniteDimensional ℚ f.toRatAlgHom.fieldRange` using `fun f => Module.Finite.of_surjective f.toRatAlgHom.rangeRestrict.toLinearMap f.toRatAlgHom.rangeRestrict_surjective`. Establish `h2 : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1})`. Introduce `t`. Establish `: Finite {z : ℂ | z ^ N t = 1}`. Use `Set.Finite.subset (Polynomial.nthRoots (N t) (1 : ℂ)).toFinset.finite_toSet fun z hz => ?_` and prove the remaining obligations.

Simplify `hz` using `[Polynomial.mem_nthRoots (hN t)]`. Use `IntermediateField.finiteDimensional_adjoin fun z hz => IsIntegral.of_pow (hN t) ?_` and prove the remaining obligations. Rewrite using `[show z ^ N t = 1 from hz]`. Conclude with `isIntegral_one`. Establish `h3 : FiniteDimensional ℚ (⨆ f : L →+* ℂ, f.toRatAlgHom.fieldRange : IntermediateField ℚ ℂ)` using `IntermediateField.finiteDimensional_iSup_of_finite`.

Establish `h4 : FiniteDimensional ℚ (⨆ t, IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1} : IntermediateField ℚ ℂ)` using `IntermediateField.finiteDimensional_iSup_of_finite`. Use `⟨(⨆ f : L →+* ℂ, f.toRatAlgHom.fieldRange) ⊔ ⨆ t, IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1}, IntermediateField.finiteDimensional_sup _ _, fun f x => ?_, fun t z hz => ?_⟩` and prove the remaining obligations. Conclude with `(le_sup_of_le_left (le_iSup (fun f : L →+* ℂ => f.toRatAlgHom.fieldRange) f) : f.toRatAlgHom.fieldRange ≤ _) ⟨x, rfl⟩`. Conclude with `(le_sup_of_le_right (le_iSup (fun t => IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1}) t) : IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1} ≤ _) (IntermediateField.subset_adjoin ℚ _ hz)`.
-/
theorem exists_base_field {T : Type} [Finite T] (N : T → ℕ) (hN : ∀ t, 0 < N t) :
    ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ (∀ (f : L →+* ℂ) (x : L), f x ∈ M) ∧
      ∀ t (z : ℂ), z ^ N t = 1 → z ∈ M := by
  have h1 : ∀ f : L →+* ℂ, FiniteDimensional ℚ f.toRatAlgHom.fieldRange := fun f =>
    Module.Finite.of_surjective f.toRatAlgHom.rangeRestrict.toLinearMap f.toRatAlgHom.rangeRestrict_surjective
  have h2 : ∀ t, FiniteDimensional ℚ (IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1}) := by
    intro t
    have : Finite {z : ℂ | z ^ N t = 1} := by
      refine Set.Finite.subset (Polynomial.nthRoots (N t) (1 : ℂ)).toFinset.finite_toSet fun z hz => ?_
      simpa [Polynomial.mem_nthRoots (hN t)] using hz
    refine IntermediateField.finiteDimensional_adjoin fun z hz => IsIntegral.of_pow (hN t) ?_
    rw [show z ^ N t = 1 from hz]
    exact isIntegral_one
  have h3 : FiniteDimensional ℚ (⨆ f : L →+* ℂ, f.toRatAlgHom.fieldRange : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  have h4 : FiniteDimensional ℚ (⨆ t, IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1} : IntermediateField ℚ ℂ) :=
    IntermediateField.finiteDimensional_iSup_of_finite
  refine ⟨(⨆ f : L →+* ℂ, f.toRatAlgHom.fieldRange) ⊔ ⨆ t, IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1},
    IntermediateField.finiteDimensional_sup _ _, fun f x => ?_, fun t z hz => ?_⟩
  · exact (le_sup_of_le_left (le_iSup (fun f : L →+* ℂ => f.toRatAlgHom.fieldRange) f) :
      f.toRatAlgHom.fieldRange ≤ _) ⟨x, rfl⟩
  · exact (le_sup_of_le_right (le_iSup (fun t => IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1}) t) :
      IntermediateField.adjoin ℚ {z : ℂ | z ^ N t = 1} ≤ _) (IntermediateField.subset_adjoin ℚ _ hz)

def clsOf (v : HeightOneSpectrum (𝓞 L)) : ClassGroup (𝓞 L) :=
  ClassGroup.mk0 ⟨v.asIdeal, mem_nonZeroDivisors_of_ne_zero v.ne_bot⟩

/- English proof (translation)
Establish `h0 : v.asIdeal * v'.asIdeal ^ (Nat.card (ClassGroup (𝓞 L)) - 1) ∈ nonZeroDivisors (Ideal (𝓞 L))` using `mem_nonZeroDivisors_of_ne_zero (mul_ne_zero v.ne_bot (pow_ne_zero _ v'.ne_bot))`. Establish `h1 : ClassGroup.mk0 ⟨_, h0⟩ = clsOf v * clsOf v' ^ (Nat.card (ClassGroup (𝓞 L)) - 1)`. Unfold `clsOf`. Rewrite using `[← map_pow, ← map_mul]`. Both sides reduce to the same expression.

Rewrite `h1` using `[h, ← pow_succ', Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one', ClassGroup.mk0_eq_one_iff]`. Take `⟨a, ha⟩` from `h1`. Conclude with `⟨a, ha.symm⟩`.
-/
theorem exists_span_eq {v v' : HeightOneSpectrum (𝓞 L)} (h : clsOf v = clsOf v') :
    ∃ a : 𝓞 L, Ideal.span {a} = v.asIdeal * v'.asIdeal ^ (Nat.card (ClassGroup (𝓞 L)) - 1) := by
  have h0 : v.asIdeal * v'.asIdeal ^ (Nat.card (ClassGroup (𝓞 L)) - 1) ∈ nonZeroDivisors (Ideal (𝓞 L)) :=
    mem_nonZeroDivisors_of_ne_zero (mul_ne_zero v.ne_bot (pow_ne_zero _ v'.ne_bot))
  have h1 : ClassGroup.mk0 ⟨_, h0⟩ = clsOf v * clsOf v' ^ (Nat.card (ClassGroup (𝓞 L)) - 1) := by
    unfold clsOf
    rw [← map_pow, ← map_mul]
    rfl
  rw [h, ← pow_succ', Nat.sub_add_cancel Nat.card_pos, pow_card_eq_one', ClassGroup.mk0_eq_one_iff] at h1
  obtain ⟨a, ha⟩ := h1
  exact ⟨a, ha.symm⟩

/- English proof (translation)
Introduce `F L _ _ _ _ _ c I _ φ hcm χ n r hinf hev`. Use `set S := (GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ).1.toFinset with hSdef`. Establish `hS : ∀ v, v ∉ S ↔ χ.UnrAt v` using `fun v => by simp [hSdef]`. Use `choose N hN hN' using locK_pow χ`. Take `⟨M, hMfin, hM, hM'⟩` from `exists_base_field (L := L) (fun w : S => N w) (fun w => hN w)`.

Establish `key` using `valTw_two_mem hcm.cplx φ hcm.bij χ n r hinf hev S (fun v hv => (hS v).1 hv) M hM (fun w hw a ha haw => hM' ⟨w, hw⟩ _ (by rw [← Units.val_pow_eq_pow_val, hN' w a ha haw, Units.val_one]))`. Use `set j := Nat.card (ClassGroup (𝓞 L)) - 1`. Establish `key2 : ∀ v v', v ∉ S → v' ∉ S → clsOf v = clsOf v' → χ.valTw ((r : ℝ) / 2) v * χ.valTw ((r : ℝ) / 2) v' ^ j ∈ M` using `fun v v' hv hv' h => by`. Take `⟨a, ha⟩` from `exists_span_eq h`. Conclude with `key v v' hv hv' j a ha`.

Establish `hrep : ∀ C : {C : ClassGroup (𝓞 L) // ∃ v, v ∉ S ∧ clsOf v = C}, ∃ v, v ∉ S ∧ clsOf v = C` using `fun C => C.2`. Use `choose rep hrepS hrepC using hrep`. Establish `hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range fun C => χ.valTw ((r : ℝ) / 2) (rep C)))`. Use `IntermediateField.finiteDimensional_adjoin ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨C, rfl⟩`.

Establish `h1` using `key2 _ _ (hrepS C) (hrepS C) rfl`. Rewrite `h1` using `[← pow_succ']`. Use `IsIntegral.of_pow j.succ_pos ?_` and prove the remaining obligations. Conclude with `(IntermediateField.isIntegral_iff (x := (⟨_, h1⟩ : M))).1 (Algebra.IsIntegral.isIntegral _)`. Use `⟨M ⊔ IntermediateField.adjoin ℚ (Set.range fun C => χ.valTw ((r : ℝ) / 2) (rep C)), IntermediateField.finiteDimensional_sup _ _, fun v hv => ?_⟩` and prove the remaining obligations.

Establish `hv'` using `(hS v).2 hv`. Set `C : {C : ClassGroup (𝓞 L) // ∃ v, v ∉ S ∧ clsOf v = C}` to `⟨clsOf v, v, hv', rfl⟩`. Establish `h1` using `key2 v (rep C) hv' (hrepS C) (hrepC C).symm`. Establish `h0 : χ.valTw ((r : ℝ) / 2) (rep C) ≠ 0`. Use `mul_ne_zero (Units.ne_zero _) ?_` and prove the remaining obligations.

Rewrite using `[Ne, Complex.cpow_eq_zero_iff]`. Introduce and unpack `⟨h, -⟩`. Conclude with `(rep C).ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h))`. Use `⟨⟨χ.valTw ((r : ℝ) / 2) v, ?_⟩, rfl⟩` and prove the remaining obligations. Rewrite using `[← mul_div_cancel_right₀ (χ.valTw ((r : ℝ) / 2) v) (pow_ne_zero j h0)]`.

Conclude with `div_mem ((le_sup_left : M ≤ _) h1) (pow_mem ((le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (f := fun C => χ.valTw ((r : ℝ) / 2) (rep C)) C))) _)`.
-/
theorem values_in_numberField : ∀ (F L : Type) [Field F] [NumberField F] [Field L] [NumberField L] [Algebra F L] (c : L ≃ₐ[F] L) (I : Type) [Fintype I] (φ : I → L →+* ℂ), CMData F c φ → ∀ (χ : HChar L) (n : I → ℤ) (r : ℤ), χ.HasInf φ n → (∀ i, Even (n i - r)) → ∃ M : IntermediateField ℚ ℂ, FiniteDimensional ℚ M ∧ χ.ValuesIn ((r : ℝ) / 2) M.val.toRingHom := by
  intro F L _ _ _ _ _ c I _ φ hcm χ n r hinf hev
  set S := (GlobalTheory.T.heckeCharacter_unramified_ae_and_exists_level L χ).1.toFinset with hSdef
  have hS : ∀ v, v ∉ S ↔ χ.UnrAt v := fun v => by simp [hSdef]
  choose N hN hN' using locK_pow χ
  obtain ⟨M, hMfin, hM, hM'⟩ := exists_base_field (L := L) (fun w : S => N w) (fun w => hN w)
  have key := valTw_two_mem hcm.cplx φ hcm.bij χ n r hinf hev S (fun v hv => (hS v).1 hv) M hM
    (fun w hw a ha haw => hM' ⟨w, hw⟩ _ (by rw [← Units.val_pow_eq_pow_val, hN' w a ha haw, Units.val_one]))
  set j := Nat.card (ClassGroup (𝓞 L)) - 1
  have key2 : ∀ v v', v ∉ S → v' ∉ S → clsOf v = clsOf v' →
      χ.valTw ((r : ℝ) / 2) v * χ.valTw ((r : ℝ) / 2) v' ^ j ∈ M := fun v v' hv hv' h => by
    obtain ⟨a, ha⟩ := exists_span_eq h
    exact key v v' hv hv' j a ha
  have hrep : ∀ C : {C : ClassGroup (𝓞 L) // ∃ v, v ∉ S ∧ clsOf v = C}, ∃ v, v ∉ S ∧ clsOf v = C := fun C => C.2
  choose rep hrepS hrepC using hrep
  have hfin : FiniteDimensional ℚ (IntermediateField.adjoin ℚ (Set.range fun C => χ.valTw ((r : ℝ) / 2) (rep C))) := by
    refine IntermediateField.finiteDimensional_adjoin ?_
    rintro _ ⟨C, rfl⟩
    have h1 := key2 _ _ (hrepS C) (hrepS C) rfl
    rw [← pow_succ'] at h1
    refine IsIntegral.of_pow j.succ_pos ?_
    exact (IntermediateField.isIntegral_iff (x := (⟨_, h1⟩ : M))).1 (Algebra.IsIntegral.isIntegral _)
  refine ⟨M ⊔ IntermediateField.adjoin ℚ (Set.range fun C => χ.valTw ((r : ℝ) / 2) (rep C)),
    IntermediateField.finiteDimensional_sup _ _, fun v hv => ?_⟩
  have hv' := (hS v).2 hv
  let C : {C : ClassGroup (𝓞 L) // ∃ v, v ∉ S ∧ clsOf v = C} := ⟨clsOf v, v, hv', rfl⟩
  have h1 := key2 v (rep C) hv' (hrepS C) (hrepC C).symm
  have h0 : χ.valTw ((r : ℝ) / 2) (rep C) ≠ 0 := by
    refine mul_ne_zero (Units.ne_zero _) ?_
    rw [Ne, Complex.cpow_eq_zero_iff]
    rintro ⟨h, -⟩
    exact (rep C).ne_bot (Ideal.absNorm_eq_zero_iff.1 (by exact_mod_cast h))
  refine ⟨⟨χ.valTw ((r : ℝ) / 2) v, ?_⟩, rfl⟩
  rw [← mul_div_cancel_right₀ (χ.valTw ((r : ℝ) / 2) v) (pow_ne_zero j h0)]
  exact div_mem ((le_sup_left : M ≤ _) h1)
    (pow_mem ((le_sup_right : IntermediateField.adjoin ℚ _ ≤ _) (IntermediateField.subset_adjoin ℚ _ (Set.mem_range_self (f := fun C => χ.valTw ((r : ℝ) / 2) (rep C)) C))) _)

end GlobalTheory.Mem.ValAlg
