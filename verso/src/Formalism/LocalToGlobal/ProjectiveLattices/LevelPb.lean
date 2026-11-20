import Formalism.LocalToGlobal.ProjectiveLattices.ExistsParameterConditions

noncomputable section

namespace Formalism.L2.Pj

open NumberField IsDedekindDomain Formalism.BasicNotions Polynomial ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped Pointwise

namespace LPb

variable (D : D7)

/- English proof (translation)
The claim follows from `IntermediateField.mem_adjoin_simple_self ℚ _`.
-/
theorem sqrtMinusD_mem_K : D.host.sqrtMinusD ∈ D.host.K :=
  IntermediateField.mem_adjoin_simple_self ℚ _

/- English proof (translation)
Establish `hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E)` using `D.host.sqrtMinusD_sq`. Establish `hd : (0 : ℚ) < D.host.d` using `by exact_mod_cast D.host.hyp.2.1.pos`. Establish `hmon : (X ^ 2 + C (D.host.d : ℚ)).Monic` using `by monicity!`. Establish `hroot : aeval D.host.sqrtMinusD (X ^ 2 + C (D.host.d : ℚ)) = 0` using `by simp [hb]`. Establish `hirr : Irreducible (X ^ 2 + C (D.host.d : ℚ))`.

Apply `Polynomial.irreducible_of_degree_le_three_of_not_isRoot` to reduce the goal to its premises. Rewrite using `[natDegree_X_pow_add_C]`. Simplify using the standard rewrite rules. Introduce `x hx`. Simplify using `only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx`.

Use polynomial arithmetic with `[sq_nonneg x]`. Establish `hint : IsIntegral ℚ D.host.sqrtMinusD` using `⟨_, hmon, by simpa [aeval_def] using hroot⟩`. Establish `hmin : minpoly ℚ D.host.sqrtMinusD = X ^ 2 + C (D.host.d : ℚ)` using `(minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm`. Establish `h` using `IntermediateField.adjoin.finrank hint`. Rewrite `h` using `[hmin, natDegree_X_pow_add_C]`.

Conclude with `h`.
-/
theorem finrank_K : Module.finrank ℚ D.host.K = 2 := by
  have hb : D.host.sqrtMinusD ^ 2 = -(D.host.d : D.host.E) := D.host.sqrtMinusD_sq
  have hd : (0 : ℚ) < D.host.d := by exact_mod_cast D.host.hyp.2.1.pos
  have hmon : (X ^ 2 + C (D.host.d : ℚ)).Monic := by monicity!
  have hroot : aeval D.host.sqrtMinusD (X ^ 2 + C (D.host.d : ℚ)) = 0 := by simp [hb]
  have hirr : Irreducible (X ^ 2 + C (D.host.d : ℚ)) := by
    apply Polynomial.irreducible_of_degree_le_three_of_not_isRoot
    · rw [natDegree_X_pow_add_C]; simp
    · intro x hx
      simp only [IsRoot, eval_add, eval_pow, eval_X, eval_C] at hx
      nlinarith [sq_nonneg x]
  have hint : IsIntegral ℚ D.host.sqrtMinusD := ⟨_, hmon, by simpa [aeval_def] using hroot⟩
  have hmin : minpoly ℚ D.host.sqrtMinusD = X ^ 2 + C (D.host.d : ℚ) :=
    (minpoly.eq_of_irreducible_of_monic hirr hroot hmon).symm
  have h := IntermediateField.adjoin.finrank hint
  rw [hmin, natDegree_X_pow_add_C] at h
  exact h

/- English proof (translation)
Establish `h2 : (2 : D.host.E) ∈ D.host.K`. Use `D.host.K.algebraMap_mem (2 : ℚ)` as an intermediate fact. Simplify using `using this`. Conclude with `div_mem (add_mem (one_mem _) (sqrtMinusD_mem_K D)) h2`.
-/
theorem half_one_add_sqrt_mem_K : ((1 + D.host.sqrtMinusD) / 2 : D.host.E) ∈ D.host.K := by
  have h2 : (2 : D.host.E) ∈ D.host.K := by
    have := D.host.K.algebraMap_mem (2 : ℚ)
    simpa using this
  exact div_mem (add_mem (one_mem _) (sqrtMinusD_mem_K D)) h2

def w0K : 𝓞 D.host.K :=
  ⟨⟨(1 + D.host.sqrtMinusD) / 2, half_one_add_sqrt_mem_K D⟩,
    (isIntegral_algHom_iff (D.host.K.val.toRingHom.toIntAlgHom) Subtype.val_injective).1 (half_one_add_sqrt_neg_isIntegral D)⟩

def phiK : 𝓞 D.host.K →+* D.host.E :=
  (D.host.K.val.toRingHom).comp (algebraMap (𝓞 D.host.K) D.host.K)

/- English proof (translation)
Introduce `a b h`. Apply `IsFractionRing.injective (𝓞 D.host.K) D.host.K` to reduce the goal to its premises. Conclude with `(RingHom.injective (D.host.K.val.toRingHom)) h`.
-/
theorem phiK_inj : Function.Injective (phiK D) := by
  intro a b h
  apply IsFractionRing.injective (𝓞 D.host.K) D.host.K
  exact (RingHom.injective (D.host.K.val.toRingHom)) h

/- English proof (translation)
Apply `phiK_inj D` to reduce the goal to its premises. Rewrite using `[map_pow, map_sub, map_natCast]`. Use `show ((1 + D.host.sqrtMinusD) / 2) ^ 2 = (1 + D.host.sqrtMinusD) / 2 - (mE D : D.host.E)`. Establish `e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (mE D : D.host.E)` using `by exact_mod_cast (mE_spec D).symm`. Take the linear combination `(1 / 4 : D.host.E) * D.host.sqrtMinusD_sq - (1 / 4 : D.host.E) * e`.
-/
theorem w0K_sq : w0K D ^ 2 = w0K D - (mE D : 𝓞 D.host.K) := by
  apply phiK_inj D
  rw [map_pow, map_sub, map_natCast]
  show ((1 + D.host.sqrtMinusD) / 2) ^ 2 = (1 + D.host.sqrtMinusD) / 2 - (mE D : D.host.E)
  have e : ((D.host.d : ℕ) : D.host.E) + 1 = 4 * (mE D : D.host.E) := by exact_mod_cast (mE_spec D).symm
  linear_combination (1 / 4 : D.host.E) * D.host.sqrtMinusD_sq - (1 / 4 : D.host.E) * e

/- English proof (translation)
Apply `RingOfIntegers.ext` to reduce the goal to its premises. Both sides reduce to the same expression.
-/
theorem algebraMap_w0K : algebraMap (𝓞 D.host.K) (𝓞 D.host.E) (w0K D) = w0E D := by
  apply RingOfIntegers.ext
  rfl

def JK (p : ℕ) (e : ℤ) : Ideal (𝓞 D.host.K) := Ideal.span {(p : 𝓞 D.host.K), w0K D - (e : 𝓞 D.host.K)}

def QE (p : ℕ) (e : ℤ) : Ideal (𝓞 D.host.E) := Ideal.span {(p : 𝓞 D.host.E), w0E D - (e : 𝓞 D.host.E)}

/- English proof (translation)
Simplify using `only [JK, QE, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_natCast, map_sub, map_intCast, algebraMap_w0K]`.
-/
theorem map_JK (p : ℕ) (e : ℤ) : (JK D p e).map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = QE D p e := by
  simp only [JK, QE, Ideal.map_span, Set.image_insert_eq, Set.image_singleton, map_natCast, map_sub,
    map_intCast, algebraMap_w0K]

/- English proof (translation)
Unfold `JK`. Rewrite using `[Ideal.span_pair_mul_span_pair]`. Take `⟨t, ht⟩` from `hp`. Take `⟨u, v, huv⟩` from `hc`. Establish `hw` using `w0K_sq D`.

Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce `z hz`. Simplify using `only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz`. Rewrite using `[SetLike.mem_coe, Ideal.mem_span_singleton]`.

Break down `hz with rfl | rfl | rfl | rfl` into its components or cases. Conclude with `dvd_mul_right _ _`. Conclude with `dvd_mul_right _ _`. Conclude with `dvd_mul_left _ _`. Use `⟨-(t : 𝓞 D.host.K), ?_⟩` and prove the remaining obligations.

Establish `ht' : ((e ^ 2 - e + mE D : ℤ) : 𝓞 D.host.K) = ((p * t : ℤ) : 𝓞 D.host.K)` using `by rw [ht]`. Move the coercions through the operations in `at ht' ⊢`. Take the linear combination `hw - ht'`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]`. Establish `huv' : ((u * (1 - 2 * e) + v * p : ℤ) : 𝓞 D.host.K) = ((1 : ℤ) : 𝓞 D.host.K)` using `by rw [huv]`.

Move the coercions through the operations in `at huv'`. Establish `e1 : (p : 𝓞 D.host.K) = (-(u : 𝓞 D.host.K)) * ((p : 𝓞 D.host.K) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K))) + (u : 𝓞 D.host.K) * ((w0K D - (e : 𝓞 D.host.K)) * (p : 𝓞 D.host.K)) + (v : 𝓞 D.host.K) * ((p : 𝓞 D.host.K) * (p : 𝓞 D.host.K))`. Use `push_cast`. Take the linear combination `(-(p : 𝓞 D.host.K)) * huv'`. Establish `hm : (-(u : 𝓞 D.host.K)) * ((p : 𝓞 D.host.K) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K))) + (u : 𝓞 D.host.K) * ((w0K D - (e : 𝓞 D.host.K)) * (p : 𝓞 D.host.K)) + (v : 𝓞 D.host.K) * ((p : 𝓞 D.host.K) * (p : 𝓞 D.host.K)) ∈ Ideal.span {(p : 𝓞 D.host.K) * (p : 𝓞 D.host.K), (p : 𝓞 D.host.K) …` using `Ideal.add_mem _ (Ideal.add_mem _ (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))) (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _)))))) (Ideal.mul_mem_left _ _ (Ideal.subse …`.

Rewrite `hm` using `[← e1]`. Then use the resulting hypothesis.
-/
theorem JK_mul (p : ℕ) (e : ℤ) (hp : (p : ℤ) ∣ e ^ 2 - e + mE D) (hc : IsCoprime (1 - 2 * e) (p : ℤ)) :
    JK D p e * JK D p (1 - e) = Ideal.span {(p : 𝓞 D.host.K)} := by
  unfold JK
  rw [Ideal.span_pair_mul_span_pair]
  obtain ⟨t, ht⟩ := hp
  obtain ⟨u, v, huv⟩ := hc
  have hw := w0K_sq D
  apply le_antisymm
  · rw [Ideal.span_le]
    intro z hz
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at hz
    rw [SetLike.mem_coe, Ideal.mem_span_singleton]
    rcases hz with rfl | rfl | rfl | rfl
    · exact dvd_mul_right _ _
    · exact dvd_mul_right _ _
    · exact dvd_mul_left _ _
    · refine ⟨-(t : 𝓞 D.host.K), ?_⟩
      have ht' : ((e ^ 2 - e + mE D : ℤ) : 𝓞 D.host.K) = ((p * t : ℤ) : 𝓞 D.host.K) := by rw [ht]
      push_cast at ht' ⊢
      linear_combination hw - ht'
  · rw [Ideal.span_le, Set.singleton_subset_iff, SetLike.mem_coe]
    have huv' : ((u * (1 - 2 * e) + v * p : ℤ) : 𝓞 D.host.K) = ((1 : ℤ) : 𝓞 D.host.K) := by rw [huv]
    push_cast at huv'
    have e1 : (p : 𝓞 D.host.K) = (-(u : 𝓞 D.host.K)) * ((p : 𝓞 D.host.K) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K))) +
        (u : 𝓞 D.host.K) * ((w0K D - (e : 𝓞 D.host.K)) * (p : 𝓞 D.host.K)) +
        (v : 𝓞 D.host.K) * ((p : 𝓞 D.host.K) * (p : 𝓞 D.host.K)) := by
      push_cast
      linear_combination (-(p : 𝓞 D.host.K)) * huv'
    have hm : (-(u : 𝓞 D.host.K)) * ((p : 𝓞 D.host.K) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K))) +
        (u : 𝓞 D.host.K) * ((w0K D - (e : 𝓞 D.host.K)) * (p : 𝓞 D.host.K)) +
        (v : 𝓞 D.host.K) * ((p : 𝓞 D.host.K) * (p : 𝓞 D.host.K)) ∈
        Ideal.span {(p : 𝓞 D.host.K) * (p : 𝓞 D.host.K), (p : 𝓞 D.host.K) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K)),
          (w0K D - (e : 𝓞 D.host.K)) * (p : 𝓞 D.host.K),
          (w0K D - (e : 𝓞 D.host.K)) * (w0K D - ((1 - e : ℤ) : 𝓞 D.host.K))} :=
      Ideal.add_mem _ (Ideal.add_mem _
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert_of_mem _ (Set.mem_insert_of_mem _ (Set.mem_insert _ _))))))
        (Ideal.mul_mem_left _ _ (Ideal.subset_span (Set.mem_insert _ _)))
    rwa [← e1] at hm

/- English proof (translation)
Rewrite using `[← map_JK, ← map_JK, ← Ideal.map_mul, JK_mul D p e hp hc, Ideal.map_span, Set.image_singleton, map_natCast]`.
-/
theorem QE_mul (p : ℕ) (e : ℤ) (hp : (p : ℤ) ∣ e ^ 2 - e + mE D) (hc : IsCoprime (1 - 2 * e) (p : ℤ)) :
    QE D p e * QE D p (1 - e) = Ideal.span {(p : 𝓞 D.host.E)} := by
  rw [← map_JK, ← map_JK, ← Ideal.map_mul, JK_mul D p e hp hc, Ideal.map_span, Set.image_singleton, map_natCast]

/- English proof (translation)
Rewrite using `[QE, QE, Ideal.map_span, Set.image_pair, map_sub, map_natCast, map_intCast]`. Establish `hb : bH D (w0E D) = 1 - w0E D` using `conj_w0E D`. Rewrite using `[hb]`. Establish `: (1 - w0E D - (e : 𝓞 D.host.E)) = -(w0E D - ((1 - e : ℤ) : 𝓞 D.host.E))` using `by push_cast; ring`. Rewrite using `[this, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_neg]`.
-/
theorem QE_map_bar (p : ℕ) (e : ℤ) : (QE D p e).map (bH D) = QE D p (1 - e) := by
  rw [QE, QE, Ideal.map_span, Set.image_pair, map_sub, map_natCast, map_intCast]
  have hb : bH D (w0E D) = 1 - w0E D := conj_w0E D
  rw [hb]
  have : (1 - w0E D - (e : 𝓞 D.host.E)) = -(w0E D - ((1 - e : ℤ) : 𝓞 D.host.E)) := by push_cast; ring
  rw [this, Ideal.span_insert, Ideal.span_insert, Ideal.span_singleton_neg]

/- English proof (translation)
Establish `hp : ((p : ℕ) : 𝓞 D.host.K) = algebraMap ℤ (𝓞 D.host.K) (p : ℤ)` using `by simp`. Rewrite using `[Ideal.absNorm_span_singleton, hp, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_K D]`. Simplify using `[Int.natAbs_pow]`.
-/
theorem absNorm_span_p (p : ℕ) : Ideal.absNorm (Ideal.span {(p : 𝓞 D.host.K)}) = p ^ 2 := by
  have hp : ((p : ℕ) : 𝓞 D.host.K) = algebraMap ℤ (𝓞 D.host.K) (p : ℤ) := by simp
  rw [Ideal.absNorm_span_singleton, hp, Algebra.norm_algebraMap, NumberField.RingOfIntegers.rank, finrank_K D]
  simp [Int.natAbs_pow]

/- English proof (translation)
Rewrite using `[Ne, Ideal.span_singleton_eq_top]`. Introduce `hu`. Establish `h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 D.host.E) (p : ℤ)))`. Simplify using `using hu.map (Algebra.norm ℤ)`. Rewrite `h2` using `[Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne']`.

Conclude with `hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.1 h2)`.
-/
theorem span_p_ne_top {p : ℕ} (hp : p.Prime) : Ideal.span {(p : 𝓞 D.host.E)} ≠ ⊤ := by
  rw [Ne, Ideal.span_singleton_eq_top]
  intro hu
  have h2 : IsUnit (Algebra.norm ℤ (algebraMap ℤ (𝓞 D.host.E) (p : ℤ))) := by
    simpa using hu.map (Algebra.norm ℤ)
  rw [Algebra.norm_algebraMap, isUnit_pow_iff Module.finrank_pos.ne'] at h2
  exact hp.ne_one (by simpa using Int.isUnit_iff_natAbs_eq.1 h2)

/- English proof (translation)
Establish `key : ∀ e : ℤ, (p : ℤ) ∣ e ^ 2 - e + mE D → IsCoprime (1 - 2 * e) (p : ℤ) → w0K D - (e : 𝓞 D.host.K) ∈ pb.asIdeal → pb.asIdeal = JK D p e`. Introduce `e he1 he2 hmem`. Establish `hJ : JK D p e ≤ pb.asIdeal`. Rewrite using `[JK, Ideal.span_le]`. Introduce `z hz`.

Break down `hz with rfl | hz` into its components or cases. Conclude with `hpb`. Rewrite using `[Set.mem_singleton_iff.1 hz]`. Conclude with `hmem`. Establish `hN` using `congrArg Ideal.absNorm (JK_mul D p e he1 he2)`.

Rewrite `hN` using `[map_mul, absNorm_span_p]`. Establish `h1 : Ideal.absNorm (JK D p e) ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Introduce `htop`. Conclude with `pb.isPrime.ne_top (top_le_iff.1 (htop ▸ hJ))`.

Establish `h2 : Ideal.absNorm (JK D p (1 - e)) ≠ 1`. Rewrite using `[Ne, Ideal.absNorm_eq_one_iff]`. Introduce `htop`. Establish `hm` using `map_JK D p (1 - e)`. Rewrite `hm` using `[htop, Ideal.map_top]`.

Establish `hb` using `QE_map_bar D p (1 - e)`. Rewrite `hb` using `[← hm, Ideal.map_top, sub_sub_cancel]`. Establish `hmulE` using `QE_mul D p e he1 he2`. Rewrite `hmulE` using `[← hb, ← hm, Ideal.top_mul]`. Conclude with `span_p_ne_top D hp.1 hmulE.symm`.

Take `⟨i, hi, hieq⟩` from `(Nat.dvd_prime_pow hp.1).1 (Dvd.intro _ hN)`. Establish `hi1 : i = 1` using `by interval_cases i`. Rewrite `hieq` using `[pow_zero]`. Conclude with `absurd hieq h1`. Both sides reduce to the same expression.

It suffices to derive a contradiction. Rewrite `hN` using `[hieq]`. Conclude with `h2 (Nat.eq_of_mul_eq_mul_left (by have := hp.1.pos; positivity) (hN.trans (mul_one _).symm))`. Rewrite `hieq` using `[hi1, pow_one]`. Establish `hprime : (JK D p e).IsPrime` using `Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.1.prime.irreducible)`.

Establish `hne : JK D p e ≠ ⊥`. Introduce `h`. Rewrite `hieq` using `[h, Ideal.absNorm_bot]`. Conclude with `hp.1.ne_zero hieq.symm`. Conclude with `((hprime.isMaximal hne).eq_of_le pb.isPrime.ne_top hJ).symm`.

Use `set c := cRoot D p`. Establish `hc1` using `cRoot_spec D hp`. Establish `hc2` using `cRoot_coprime D hp`. Establish `hd1 : (p : ℤ) ∣ (1 - c) ^ 2 - (1 - c) + mE D`. Establish `: (1 - c) ^ 2 - (1 - c) + (mE D : ℤ) = c ^ 2 - c + mE D` using `by ring`.

Rewrite using `[this]`. Conclude with `hc1`. Establish `hd2 : IsCoprime (1 - 2 * (1 - c)) (p : ℤ)`. Establish `: 1 - 2 * (1 - c) = -(1 - 2 * c)` using `by ring`. Rewrite using `[this]`.

Conclude with `hc2.neg_left`. Take `⟨t, ht⟩` from `hc1`. Establish `hprod : (w0K D - (c : 𝓞 D.host.K)) * (w0K D - ((1 - c : ℤ) : 𝓞 D.host.K)) ∈ pb.asIdeal`. Establish `e1 : (w0K D - (c : 𝓞 D.host.K)) * (w0K D - ((1 - c : ℤ) : 𝓞 D.host.K)) = (p : 𝓞 D.host.K) * (-(t : 𝓞 D.host.K))`. Establish `hw` using `w0K_sq D`.

Establish `ht' : ((c ^ 2 - c + mE D : ℤ) : 𝓞 D.host.K) = ((p * t : ℤ) : 𝓞 D.host.K)` using `by rw [ht]`. Move the coercions through the operations in `at ht' ⊢`. Take the linear combination `hw - ht'`. Rewrite using `[e1]`. Conclude with `Ideal.mul_mem_right _ _ hpb`.

Break down `pb.isPrime.mem_or_mem hprod with h | h` into its components or cases. Conclude with `⟨c, ⟨t, ht⟩, hc2, key c ⟨t, ht⟩ hc2 h⟩`. Conclude with `⟨1 - c, hd1, hd2, key (1 - c) hd1 hd2 h⟩`.
-/
theorem pb_eq_JK {p : ℕ} (hp : SplitOK D p) (pb : HeightOneSpectrum (𝓞 D.host.K))
    (hpb : (p : 𝓞 D.host.K) ∈ pb.asIdeal) :
    ∃ e : ℤ, (p : ℤ) ∣ e ^ 2 - e + mE D ∧ IsCoprime (1 - 2 * e) (p : ℤ) ∧ pb.asIdeal = JK D p e := by
  have key : ∀ e : ℤ, (p : ℤ) ∣ e ^ 2 - e + mE D → IsCoprime (1 - 2 * e) (p : ℤ) →
      w0K D - (e : 𝓞 D.host.K) ∈ pb.asIdeal → pb.asIdeal = JK D p e := by
    intro e he1 he2 hmem
    have hJ : JK D p e ≤ pb.asIdeal := by
      rw [JK, Ideal.span_le]
      intro z hz
      rcases hz with rfl | hz
      · exact hpb
      · rw [Set.mem_singleton_iff.1 hz]; exact hmem
    have hN := congrArg Ideal.absNorm (JK_mul D p e he1 he2)
    rw [map_mul, absNorm_span_p] at hN
    have h1 : Ideal.absNorm (JK D p e) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      exact pb.isPrime.ne_top (top_le_iff.1 (htop ▸ hJ))
    have h2 : Ideal.absNorm (JK D p (1 - e)) ≠ 1 := by
      rw [Ne, Ideal.absNorm_eq_one_iff]
      intro htop
      have hm := map_JK D p (1 - e)
      rw [htop, Ideal.map_top] at hm
      have hb := QE_map_bar D p (1 - e)
      rw [← hm, Ideal.map_top, sub_sub_cancel] at hb
      have hmulE := QE_mul D p e he1 he2
      rw [← hb, ← hm, Ideal.top_mul] at hmulE
      exact span_p_ne_top D hp.1 hmulE.symm
    obtain ⟨i, hi, hieq⟩ := (Nat.dvd_prime_pow hp.1).1 (Dvd.intro _ hN)
    have hi1 : i = 1 := by
      interval_cases i
      · rw [pow_zero] at hieq; exact absurd hieq h1
      · rfl
      · exfalso
        rw [hieq] at hN
        exact h2 (Nat.eq_of_mul_eq_mul_left (by have := hp.1.pos; positivity) (hN.trans (mul_one _).symm))
    rw [hi1, pow_one] at hieq
    have hprime : (JK D p e).IsPrime :=
      Ideal.isPrime_of_irreducible_absNorm (by rw [hieq]; exact hp.1.prime.irreducible)
    have hne : JK D p e ≠ ⊥ := by
      intro h
      rw [h, Ideal.absNorm_bot] at hieq
      exact hp.1.ne_zero hieq.symm
    exact ((hprime.isMaximal hne).eq_of_le pb.isPrime.ne_top hJ).symm
  set c := cRoot D p
  have hc1 := cRoot_spec D hp
  have hc2 := cRoot_coprime D hp
  have hd1 : (p : ℤ) ∣ (1 - c) ^ 2 - (1 - c) + mE D := by
    have : (1 - c) ^ 2 - (1 - c) + (mE D : ℤ) = c ^ 2 - c + mE D := by ring
    rw [this]; exact hc1
  have hd2 : IsCoprime (1 - 2 * (1 - c)) (p : ℤ) := by
    have : 1 - 2 * (1 - c) = -(1 - 2 * c) := by ring
    rw [this]; exact hc2.neg_left
  obtain ⟨t, ht⟩ := hc1
  have hprod : (w0K D - (c : 𝓞 D.host.K)) * (w0K D - ((1 - c : ℤ) : 𝓞 D.host.K)) ∈ pb.asIdeal := by
    have e1 : (w0K D - (c : 𝓞 D.host.K)) * (w0K D - ((1 - c : ℤ) : 𝓞 D.host.K)) =
        (p : 𝓞 D.host.K) * (-(t : 𝓞 D.host.K)) := by
      have hw := w0K_sq D
      have ht' : ((c ^ 2 - c + mE D : ℤ) : 𝓞 D.host.K) = ((p * t : ℤ) : 𝓞 D.host.K) := by rw [ht]
      push_cast at ht' ⊢
      linear_combination hw - ht'
    rw [e1]; exact Ideal.mul_mem_right _ _ hpb
  rcases pb.isPrime.mem_or_mem hprod with h | h
  · exact ⟨c, ⟨t, ht⟩, hc2, key c ⟨t, ht⟩ hc2 h⟩
  · exact ⟨1 - c, hd1, hd2, key (1 - c) hd1 hd2 h⟩

/- English proof (translation)
Take `⟨u, v, huv⟩` from `hc`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]`. Establish `h1 : ((1 - 2 * e : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e)`. Establish `ha : w0E D - (e : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e)` using `Ideal.mem_sup_left (Ideal.subset_span (by simp))`. Establish `hb : w0E D - ((1 - e : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e)` using `Ideal.mem_sup_right (Ideal.subset_span (by simp))`.

Establish `hab` using `Submodule.sub_mem _ ha hb`. Use `hab using 1` and compare the differences between its conclusion and the goal. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `h2 : ((p : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e)` using `Ideal.mem_sup_left (Ideal.subset_span (by simp))`.

Establish `hs` using `Submodule.add_mem _ (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) h1) (Ideal.mul_mem_left _ (v : 𝓞 D.host.E) h2)`. Establish `e1 : (u : 𝓞 D.host.E) * ((1 - 2 * e : ℤ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((p : ℤ) : 𝓞 D.host.E) = 1`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv` after adjusting the coercions. Rewrite `hs` using `[e1]`. Then use the resulting hypothesis.
-/
theorem QE_cop_self (p : ℕ) (e : ℤ) (hc : IsCoprime (1 - 2 * e) (p : ℤ)) :
    IsCoprime (QE D p e) (QE D p (1 - e)) := by
  obtain ⟨u, v, huv⟩ := hc
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have h1 : ((1 - 2 * e : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e) := by
    have ha : w0E D - (e : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e) :=
      Ideal.mem_sup_left (Ideal.subset_span (by simp))
    have hb : w0E D - ((1 - e : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e) :=
      Ideal.mem_sup_right (Ideal.subset_span (by simp))
    have hab := Submodule.sub_mem _ ha hb
    convert hab using 1
    push_cast
    ring
  have h2 : ((p : ℤ) : 𝓞 D.host.E) ∈ QE D p e ⊔ QE D p (1 - e) :=
    Ideal.mem_sup_left (Ideal.subset_span (by simp))
  have hs := Submodule.add_mem _ (Ideal.mul_mem_left _ (u : 𝓞 D.host.E) h1)
    (Ideal.mul_mem_left _ (v : 𝓞 D.host.E) h2)
  have e1 : (u : 𝓞 D.host.E) * ((1 - 2 * e : ℤ) : 𝓞 D.host.E) + (v : 𝓞 D.host.E) * ((p : ℤ) : 𝓞 D.host.E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.E) huv
  rwa [e1] at hs

/- English proof (translation)
Take `⟨a, b, hab⟩` from `Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)`. Rewrite using `[Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]`. Establish `e1 : (a : 𝓞 D.host.E) * (p : 𝓞 D.host.E) + (b : 𝓞 D.host.E) * (q : 𝓞 D.host.E) = 1`. Conclude with `congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab` after adjusting the coercions. Rewrite using `[← e1]`.

Conclude with `Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp))) (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))`.
-/
theorem QE_cop_ne {p q : ℕ} (hp : p.Prime) (hq : q.Prime) (hpq : p ≠ q) (e f : ℤ) :
    IsCoprime (QE D p e) (QE D q f) := by
  obtain ⟨a, b, hab⟩ := Nat.isCoprime_iff_coprime.2 ((Nat.coprime_primes hp hq).2 hpq)
  rw [Ideal.isCoprime_iff_sup_eq, Ideal.eq_top_iff_one]
  have e1 : (a : 𝓞 D.host.E) * (p : 𝓞 D.host.E) + (b : 𝓞 D.host.E) * (q : 𝓞 D.host.E) = 1 := by
    exact_mod_cast congrArg (Int.cast : ℤ → 𝓞 D.host.E) hab
  rw [← e1]
  exact Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))
    (Ideal.mul_mem_left _ _ (Ideal.subset_span (by simp)))

end LPb

open LPb in

/- English proof (translation)
Apply the tactic sequence `have hsp : ∀ k : Fin 2, SplitOK D (D.host.g k) := fun k => splitG D _ (by fin_cases k <;> simp)`. Use `choose e he1 he2 hpb using fun k => pb_eq_JK D (hsp k) (pb k) (hg k)`. Establish `hQ : ∀ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = QE D (D.host.g k) (e k)` using `fun k => by rw [hpb k, map_JK]`. Establish `g0` using `(D.host.g_prime 0).two_le`. Establish `g1` using `(D.host.g_prime 1).two_le`.

Establish `n0` using `g_ne_two D 0`. Establish `n1` using `g_ne_two D 1`. Use `⟨{ M := D.host.g 0 * D.host.g 1 three_le := by` and prove the remaining obligations. Establish `a : 3 ≤ D.host.g 0` using `by omega`. Establish `b : 3 ≤ D.host.g 1` using `by omega`.

Use the polynomial consequences of the given equalities and inequalities. Use `odd := ((D.host.g_prime 0).odd_of_ne_two n0).mul ((D.host.g_prime 1).odd_of_ne_two n1)`. Use `Mb := QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)`. Use `fromK := ?_`. Use `prod := ?_`.

Use `coprime := ?_`. Use `A := 1`. Use `A_pos := Nat.one_pos }, ⟨rfl, rfl⟩, ?_⟩`. Use `fromK_of_gen ⟨{((D.host.g 0 : ℕ) : 𝓞 D.host.E), w0E D - (e 0 : 𝓞 D.host.E)} * {((D.host.g 1 : ℕ) : 𝓞 D.host.E), w0E D - (e 1 : 𝓞 D.host.E)}, by rw [QE, QE, Ideal.span_mul_span'], ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Take `⟨a, ha, b, hb, rfl⟩` from `Set.mem_mul.1 hx`. Establish `hgen : ∀ (p : ℕ) (f : ℤ) (y : 𝓞 D.host.E), y ∈ ({(p : 𝓞 D.host.E), w0E D - (f : 𝓞 D.host.E)} : Set (𝓞 D.host.E)) → y ∈ Algebra.adjoin ℤ {w0E D}`. Introduce `p f y hy`. Break down `hy with rfl | hy` into its components or cases. Conclude with `Subalgebra.natCast_mem _ _`.

Rewrite using `[Set.mem_singleton_iff.1 hy]`. Conclude with `Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)`. Conclude with `Subalgebra.mul_mem _ (hgen _ _ _ ha) (hgen _ _ _ hb)`. Express the relevant statement in the definitionally equal form `QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1) * (QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)).map (bH D) = Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}`. Rewrite using `[Ideal.map_mul, QE_map_bar, QE_map_bar, mul_mul_mul_comm, QE_mul D _ _ (he1 0) (he2 0), QE_mul D _ _ (he1 1) (he2 1), Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]`.

Express the relevant statement in the definitionally equal form `QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1) ⊔ (QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)).map (bH D) = ⊤`. Rewrite using `[← Ideal.isCoprime_iff_sup_eq, Ideal.map_mul, QE_map_bar, QE_map_bar]`. Conclude with `IsCoprime.mul_left (IsCoprime.mul_right (QE_cop_self D _ _ (he2 0)) (QE_cop_ne D (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne _ _)) (IsCoprime.mul_right (QE_cop_ne D (D.host.g_prime 1) (D.host.g_prime 0) D.host.g_ne.symm _ _) (QE_cop_self D _ _ (he2 1)))`. Use `show _ = ∏ k, _`. Rewrite using `[Fin.prod_univ_two, hQ 0, hQ 1]`.
-/
theorem levelPb_exists (D : D7) (pb : Fin 2 → HeightOneSpectrum (𝓞 D.host.K))
    (hg : ∀ k, ((D.host.g k : ℕ) : 𝓞 D.host.K) ∈ (pb k).asIdeal) :
    ∃ l : Level (hostOfRecord D), (l.M = D.host.g 0 * D.host.g 1 ∧ l.A = 1) ∧
      l.Mb = ∏ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) := by
  have hsp : ∀ k : Fin 2, SplitOK D (D.host.g k) := fun k => splitG D _ (by fin_cases k <;> simp)
  choose e he1 he2 hpb using fun k => pb_eq_JK D (hsp k) (pb k) (hg k)
  have hQ : ∀ k, (pb k).asIdeal.map (algebraMap (𝓞 D.host.K) (𝓞 D.host.E)) = QE D (D.host.g k) (e k) :=
    fun k => by rw [hpb k, map_JK]
  have g0 := (D.host.g_prime 0).two_le
  have g1 := (D.host.g_prime 1).two_le
  have n0 := g_ne_two D 0
  have n1 := g_ne_two D 1
  refine ⟨{ M := D.host.g 0 * D.host.g 1
            three_le := by
              have a : 3 ≤ D.host.g 0 := by omega
              have b : 3 ≤ D.host.g 1 := by omega
              nlinarith
            odd := ((D.host.g_prime 0).odd_of_ne_two n0).mul ((D.host.g_prime 1).odd_of_ne_two n1)
            Mb := QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)
            fromK := ?_
            prod := ?_
            coprime := ?_
            A := 1
            A_pos := Nat.one_pos }, ⟨rfl, rfl⟩, ?_⟩
  · refine fromK_of_gen ⟨{((D.host.g 0 : ℕ) : 𝓞 D.host.E), w0E D - (e 0 : 𝓞 D.host.E)} *
        {((D.host.g 1 : ℕ) : 𝓞 D.host.E), w0E D - (e 1 : 𝓞 D.host.E)}, by rw [QE, QE, Ideal.span_mul_span'], ?_⟩
    intro x hx
    obtain ⟨a, ha, b, hb, rfl⟩ := Set.mem_mul.1 hx
    have hgen : ∀ (p : ℕ) (f : ℤ) (y : 𝓞 D.host.E),
        y ∈ ({(p : 𝓞 D.host.E), w0E D - (f : 𝓞 D.host.E)} : Set (𝓞 D.host.E)) → y ∈ Algebra.adjoin ℤ {w0E D} := by
      intro p f y hy
      rcases hy with rfl | hy
      · exact Subalgebra.natCast_mem _ _
      · rw [Set.mem_singleton_iff.1 hy]
        exact Subalgebra.sub_mem _ (Algebra.subset_adjoin (Set.mem_singleton _)) (Subalgebra.intCast_mem _ _)
    exact Subalgebra.mul_mem _ (hgen _ _ _ ha) (hgen _ _ _ hb)
  · change QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1) *
        (QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)).map (bH D) =
        Ideal.span {((D.host.g 0 * D.host.g 1 : ℕ) : 𝓞 D.host.E)}
    rw [Ideal.map_mul, QE_map_bar, QE_map_bar, mul_mul_mul_comm, QE_mul D _ _ (he1 0) (he2 0),
      QE_mul D _ _ (he1 1) (he2 1), Ideal.span_singleton_mul_span_singleton, Nat.cast_mul]
  · change QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1) ⊔
        (QE D (D.host.g 0) (e 0) * QE D (D.host.g 1) (e 1)).map (bH D) = ⊤
    rw [← Ideal.isCoprime_iff_sup_eq, Ideal.map_mul, QE_map_bar, QE_map_bar]
    exact IsCoprime.mul_left
      (IsCoprime.mul_right (QE_cop_self D _ _ (he2 0))
        (QE_cop_ne D (D.host.g_prime 0) (D.host.g_prime 1) D.host.g_ne _ _))
      (IsCoprime.mul_right (QE_cop_ne D (D.host.g_prime 1) (D.host.g_prime 0) D.host.g_ne.symm _ _)
        (QE_cop_self D _ _ (he2 1)))
  · show _ = ∏ k, _
    rw [Fin.prod_univ_two, hQ 0, hQ 1]

end Formalism.L2.Pj
