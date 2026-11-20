import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.NormAlmostAll
import Development.AutomorphicArithmetic.Foundations.Convolution.HermitianDescent.GalBase

namespace UpperTheory.ConvolutionTheory.D

section

variable {S T : Type} [CommRing S] [CommRing T] [Algebra S T]

/- English proof (translation)
Rewrite using `[pow_succ', AlgEquiv.mul_apply]`.
-/
private theorem pow_succ_app (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = σ ((σ ^ j) t) := by
  rw [pow_succ', AlgEquiv.mul_apply]

/- English proof (translation)
Rewrite using `[pow_succ, AlgEquiv.mul_apply]`.
-/
private theorem pow_succ_app' (σ : T ≃ₐ[S] T) (j : ℕ) (t : T) : (σ ^ (j + 1)) t = (σ ^ j) (σ t) := by
  rw [pow_succ, AlgEquiv.mul_apply]

/- English proof (translation)
Take `⟨s, x, y, hxy⟩` from `h.sep`. Set `c : ℕ → T` to `fun j => ∏ i ∈ Finset.range j, (σ ^ i) a`. Establish `hc : ∀ j, a * σ (c j) = c (j + 1)`. Introduce `j`. Simplify using `only [c]`.

Rewrite using `[Finset.prod_range_succ', map_prod, mul_comm]`. Simplify using `only [pow_succ_app, pow_zero, AlgEquiv.one_apply]`. Set `z : T → T` to `fun t => ∑ j ∈ Finset.range q, c j * (σ ^ j) t`. Establish `hz : ∀ t, a * σ (z t) = z t`. Introduce `t`.

Establish `h1 : a * σ (z t) = ∑ j ∈ Finset.range q, c (j + 1) * (σ ^ (j + 1)) t`. Simplify using `only [z, map_sum, Finset.mul_sum, map_mul, ← hc, pow_succ_app, mul_assoc]`. Establish `h2` using `Finset.sum_range_succ (fun j => c j * (σ ^ j) t) q`. Rewrite `h2` using `[Finset.sum_range_succ']`. Establish `h3 : c q = 1` using `ha`.

Establish `h4 : c 0 = 1` using `by simp [c]`. Rewrite `h2` using `[h3, h4, h.pow, pow_zero]`. Rewrite using `[h1]`. Conclude with `add_right_cancel h2`. Establish `hs : ∑ i, x i * z (y i) = 1`.

Establish `: ∑ i, x i * z (y i) = ∑ j ∈ Finset.range q, c j * ∑ i, x i * (σ ^ j) (y i)`. Simplify using `only [z, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring`. Rewrite using `[this, Finset.sum_eq_single 0]`.

Rewrite using `[hxy 0 h.pos]`. Simplify using `[c]`. Introduce `j hj hj0`. Rewrite using `[hxy j (Finset.mem_range.1 hj), if_neg hj0, mul_zero]`. Introduce `h0`.

Conclude with `absurd (Finset.mem_range.2 h.pos) h0`. Assume the negation of the conclusion as `hcon`. Use `push Not at hcon`. Apply `hP` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, ← hs]`.

Conclude with `P.sum_mem fun i _ => P.mul_mem_left _ (hcon _ (hz _))`.
-/
private theorem exists_notMem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a : T)
    (ha : ∏ i ∈ Finset.range q, (σ ^ i) a = 1) (P : Ideal T) (hP : P ≠ ⊤) :
    ∃ z, a * σ z = z ∧ z ∉ P := by
  obtain ⟨s, x, y, hxy⟩ := h.sep
  let c : ℕ → T := fun j => ∏ i ∈ Finset.range j, (σ ^ i) a
  have hc : ∀ j, a * σ (c j) = c (j + 1) := by
    intro j
    simp only [c]
    rw [Finset.prod_range_succ', map_prod, mul_comm]
    simp only [pow_succ_app, pow_zero, AlgEquiv.one_apply]
  let z : T → T := fun t => ∑ j ∈ Finset.range q, c j * (σ ^ j) t
  have hz : ∀ t, a * σ (z t) = z t := by
    intro t
    have h1 : a * σ (z t) = ∑ j ∈ Finset.range q, c (j + 1) * (σ ^ (j + 1)) t := by
      simp only [z, map_sum, Finset.mul_sum, map_mul, ← hc, pow_succ_app, mul_assoc]
    have h2 := Finset.sum_range_succ (fun j => c j * (σ ^ j) t) q
    rw [Finset.sum_range_succ'] at h2
    have h3 : c q = 1 := ha
    have h4 : c 0 = 1 := by simp [c]
    rw [h3, h4, h.pow, pow_zero] at h2
    rw [h1]
    exact add_right_cancel h2
  have hs : ∑ i, x i * z (y i) = 1 := by
    have : ∑ i, x i * z (y i) = ∑ j ∈ Finset.range q, c j * ∑ i, x i * (σ ^ j) (y i) := by
      simp only [z, Finset.mul_sum]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this, Finset.sum_eq_single 0]
    · rw [hxy 0 h.pos]; simp [c]
    · intro j hj hj0
      rw [hxy j (Finset.mem_range.1 hj), if_neg hj0, mul_zero]
    · intro h0
      exact absurd (Finset.mem_range.2 h.pos) h0
  by_contra hcon
  push Not at hcon
  apply hP
  rw [Ideal.eq_top_iff_one, ← hs]
  exact P.sum_mem fun i _ => P.mul_mem_left _ (hcon _ (hz _))

/- English proof (translation)
Establish `hd : ∀ j, (σ ^ j) z ∣ z`. Introduce `j`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih`.

Use `dvd_trans ?_ ih` and prove the remaining obligations. Rewrite using `[pow_succ_app']`. Use `conv_rhs => rw [← hz, map_mul]`. Conclude with `dvd_mul_left _ _`. Take `⟨r, rfl⟩ : ∃ r, q = r + 1` from `⟨q - 1, by have := h.pos; omega⟩`.

Establish `hN : σ (∏ j ∈ Finset.range (r + 1), (σ ^ j) z) = ∏ j ∈ Finset.range (r + 1), (σ ^ j) z`. Rewrite using `[map_prod]`. Simplify using `only [← pow_succ_app]`. Rewrite using `[Finset.prod_range_succ, h.pow, Finset.prod_range_succ' _ r, pow_zero]`. Take `⟨n, hn⟩` from `h.fix _ hN`.

Establish `h1 : algebraMap S T n ∈ P`. Rewrite using `[hn, Finset.prod_range_succ']`. Conclude with `P.mul_mem_left _ (by simpa using hzP)`. Establish `h2 : algebraMap S T n ∈ Q`. Rewrite using `[← Ideal.mem_comap, ← hPQ]`.

Conclude with `h1`. Rewrite `h2` using `[hn, Ideal.IsPrime.prod_mem_iff]`. Take `⟨j, -, hj⟩` from `h2`. Conclude with `Q.mem_of_dvd (hd j) hj`.
-/
private theorem mem_of_mem {σ : T ≃ₐ[S] T} {q : ℕ} (h : IsGal σ q) (a z : T) (hz : a * σ z = z)
    (P Q : Ideal T) [Q.IsPrime] (hPQ : P.comap (algebraMap S T) = Q.comap (algebraMap S T))
    (hzP : z ∈ P) : z ∈ Q := by
  have hd : ∀ j, (σ ^ j) z ∣ z := by
    intro j
    induction j with
    | zero => simp
    | succ j ih =>
      refine dvd_trans ?_ ih
      rw [pow_succ_app']
      conv_rhs => rw [← hz, map_mul]
      exact dvd_mul_left _ _
  obtain ⟨r, rfl⟩ : ∃ r, q = r + 1 := ⟨q - 1, by have := h.pos; omega⟩
  have hN : σ (∏ j ∈ Finset.range (r + 1), (σ ^ j) z) = ∏ j ∈ Finset.range (r + 1), (σ ^ j) z := by
    rw [map_prod]
    simp only [← pow_succ_app]
    rw [Finset.prod_range_succ, h.pow, Finset.prod_range_succ' _ r, pow_zero]
  obtain ⟨n, hn⟩ := h.fix _ hN
  have h1 : algebraMap S T n ∈ P := by
    rw [hn, Finset.prod_range_succ']
    exact P.mul_mem_left _ (by simpa using hzP)
  have h2 : algebraMap S T n ∈ Q := by
    rw [← Ideal.mem_comap, ← hPQ]; exact h1
  rw [hn, Ideal.IsPrime.prod_mem_iff] at h2
  obtain ⟨j, -, hj⟩ := h2
  exact Q.mem_of_dvd (hd j) hj

end

/- English proof (translation)
Establish `hf` using `Algebra.QuasiFinite.finite_primesOver (R := k) (S := S) (IsLocalRing.maximalIdeal k)`. Establish `: Finite ((IsLocalRing.maximalIdeal k).primesOver S)` using `hf`. Use `Finite.of_injective (β := (IsLocalRing.maximalIdeal k).primesOver S) (fun m => ⟨m.asIdeal, m.isMaximal.isPrime, ⟨?_⟩⟩) ?_` and prove the remaining obligations. Use `m.isMaximal` as an intermediate fact. Conclude with `(IsLocalRing.eq_maximalIdeal (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := k) m.asIdeal)).symm`.

Introduce `m m' hm`. Conclude with `MaximalSpectrum.ext (congrArg Subtype.val hm)`.
-/
private theorem finite_max (k S : Type) [CommRing k] [IsLocalRing k] [CommRing S] [Algebra k S]
    [Module.Finite k S] : Finite (MaximalSpectrum S) := by
  have hf := Algebra.QuasiFinite.finite_primesOver (R := k) (S := S) (IsLocalRing.maximalIdeal k)
  have : Finite ((IsLocalRing.maximalIdeal k).primesOver S) := hf
  refine Finite.of_injective (β := (IsLocalRing.maximalIdeal k).primesOver S)
    (fun m => ⟨m.asIdeal, m.isMaximal.isPrime, ⟨?_⟩⟩) ?_
  · have := m.isMaximal
    exact (IsLocalRing.eq_maximalIdeal
      (Ideal.isMaximal_comap_of_isIntegral_of_isMaximal (R := k) m.asIdeal)).symm
  · intro m m' hm
    exact MaximalSpectrum.ext (congrArg Subtype.val hm)

/- English proof (translation)
Introduce `k R _ _ _ _ S T _ _ _ _ _ σ q h a ha`. Establish `hfin : Module.Finite S T` using `(galBase S T S σ q h).1`. Use `finite_max k S` as an intermediate fact. Use `Fintype.ofFinite (MaximalSpectrum S)` as an intermediate fact. Establish `hloc : ∀ m : MaximalSpectrum S, ∃ z : T, a * σ z = z ∧ ∀ P : Ideal T, P.IsMaximal → P.comap (algebraMap S T) = m.asIdeal → z ∉ P`.

Introduce `m`. Distinguish the cases in `hm : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap S T) = m.asIdeal`. Take `⟨Q, hQ, hQm⟩` from `hm`. Take `⟨z, hz, hzQ⟩` from `exists_notMem h a ha Q hQ.ne_top`. Conclude with `⟨z, hz, fun P _ hP hzP => hzQ (mem_of_mem h a z hz P Q (hP.trans hQm.symm) hzP)⟩`.

Conclude with `⟨0, by simp, fun P hP hPm => (hm ⟨P, hP, hPm⟩).elim⟩`. Use `choose z hz hzP using hloc`. Establish `he : ∀ m : MaximalSpectrum S, ∃ e : S, e - 1 ∈ m.asIdeal ∧ ∀ m', m' ≠ m → e ∈ m'.asIdeal`. Introduce `m`. Take `⟨e, he⟩` from `Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum S => m.asIdeal) (fun m m' hne => MaximalSpectrum.isCoprime_of_ne hne) (Pi.single m 1)`.

Use `⟨e, ?_, fun m' hne => ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, he m, Pi.single_eq_same, map_one]`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, he m', Pi.single_eq_of_ne hne]`. Use `choose e he1 he0 using he`. Establish `hu : IsUnit (∑ m, algebraMap S T (e m) * z m)`.

Assume the negation of the conclusion as `hnu`. Take `⟨P, hP, hmem⟩` from `exists_max_ideal_of_mem_nonunits hnu`. Set `m : MaximalSpectrum S` to `⟨P.comap (algebraMap S T), Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P⟩`. Apply `hzP m P hP rfl` to reduce the goal to its premises. Rewrite `hmem` using `[← Finset.add_sum_erase _ _ (Finset.mem_univ m)]`.

Establish `h1 : ∑ m' ∈ Finset.univ.erase m, algebraMap S T (e m') * z m' ∈ P` using `P.sum_mem fun m' hm' => P.mul_mem_right _ (he0 m' m (Finset.ne_of_mem_erase hm').symm)`. Establish `h2 : algebraMap S T (e m - 1) * z m ∈ P` using `P.mul_mem_right _ (he1 m)`. Establish `h3` using `P.sub_mem (P.sub_mem hmem h1) h2`. Rewrite `h3` using `[map_sub, map_one]`. Use `h3 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[hu.unit_spec, map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[map_mul, σ.commutes, mul_left_comm, hz]`.
-/
theorem h90 : H90 := by
  intro k R _ _ _ _ S T _ _ _ _ _ σ q h a ha
  classical
  have hfin : Module.Finite S T := (galBase S T S σ q h).1
  have := finite_max k S
  have := Fintype.ofFinite (MaximalSpectrum S)
  have hloc : ∀ m : MaximalSpectrum S, ∃ z : T, a * σ z = z ∧
      ∀ P : Ideal T, P.IsMaximal → P.comap (algebraMap S T) = m.asIdeal → z ∉ P := by
    intro m
    by_cases hm : ∃ Q : Ideal T, Q.IsMaximal ∧ Q.comap (algebraMap S T) = m.asIdeal
    · obtain ⟨Q, hQ, hQm⟩ := hm
      obtain ⟨z, hz, hzQ⟩ := exists_notMem h a ha Q hQ.ne_top
      exact ⟨z, hz, fun P _ hP hzP => hzQ (mem_of_mem h a z hz P Q (hP.trans hQm.symm) hzP)⟩
    · exact ⟨0, by simp, fun P hP hPm => (hm ⟨P, hP, hPm⟩).elim⟩
  choose z hz hzP using hloc
  have he : ∀ m : MaximalSpectrum S, ∃ e : S, e - 1 ∈ m.asIdeal ∧ ∀ m', m' ≠ m → e ∈ m'.asIdeal := by
    intro m
    obtain ⟨e, he⟩ := Ideal.pi_quotient_surjective (I := fun m : MaximalSpectrum S => m.asIdeal)
      (fun m m' hne => MaximalSpectrum.isCoprime_of_ne hne) (Pi.single m 1)
    refine ⟨e, ?_, fun m' hne => ?_⟩
    · rw [← Ideal.Quotient.eq, he m, Pi.single_eq_same, map_one]
    · rw [← Ideal.Quotient.eq_zero_iff_mem, he m', Pi.single_eq_of_ne hne]
  choose e he1 he0 using he
  have hu : IsUnit (∑ m, algebraMap S T (e m) * z m) := by
    by_contra hnu
    obtain ⟨P, hP, hmem⟩ := exists_max_ideal_of_mem_nonunits hnu
    let m : MaximalSpectrum S := ⟨P.comap (algebraMap S T), Ideal.isMaximal_comap_of_isIntegral_of_isMaximal P⟩
    apply hzP m P hP rfl
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ m)] at hmem
    have h1 : ∑ m' ∈ Finset.univ.erase m, algebraMap S T (e m') * z m' ∈ P :=
      P.sum_mem fun m' hm' => P.mul_mem_right _ (he0 m' m (Finset.ne_of_mem_erase hm').symm)
    have h2 : algebraMap S T (e m - 1) * z m ∈ P := P.mul_mem_right _ (he1 m)
    have h3 := P.sub_mem (P.sub_mem hmem h1) h2
    rw [map_sub, map_one] at h3
    convert h3 using 1
    ring
  refine ⟨hu.unit, ?_⟩
  rw [hu.unit_spec, map_sum, Finset.mul_sum]
  refine Finset.sum_congr rfl fun m _ => ?_
  rw [map_mul, σ.commutes, mul_left_comm, hz]

end UpperTheory.ConvolutionTheory.D
