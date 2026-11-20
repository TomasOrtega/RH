import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S} {ι : Type}

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top]`.
-/
theorem smul_top_ideal (J : Ideal A) : (J • ⊤ : Submodule A A) = J := by
  rw [smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Rewrite using `[SModEq.sub_mem, smul_top_ideal]`.
-/
theorem sub_mem_iff (J : Ideal A) (n : ℕ) (x y : A) :
    x ≡ y [SMOD ((J ^ n • ⊤ : Submodule A A))] ↔ x - y ∈ J ^ n := by
  rw [SModEq.sub_mem, smul_top_ideal]

/- English proof (translation)
Establish `hH : IsHausdorff (I.map s) A` using `TB.complete.toIsHausdorff`. Use `hH.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[sub_mem_iff, ← Ideal.map_pow]`. Use `TB.approx x n ∅ (fun i _ => by rw [h i]; exact zero_mem _)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_c (TB : TopBasis s I ι) (x : A) (h : ∀ i, TB.c i x = 0) : x = 0 := by
  have hH : IsHausdorff (I.map s) A := TB.complete.toIsHausdorff
  refine hH.haus x fun n => ?_
  rw [sub_mem_iff, ← Ideal.map_pow]
  have := TB.approx x n ∅ (fun i _ => by rw [h i]; exact zero_mem _)
  simpa using this

/- English proof (translation)
Rewrite using `[mul_comm]`. Conclude with `TB.c_mul i a x`.
-/
theorem c_s (TB : TopBasis s I ι) (i : ι) (a : S) (x : A) : TB.c i (x * s a) = a * TB.c i x := by
  rw [mul_comm]; exact TB.c_mul i a x

/- English proof (translation)
Use `TB.c_mul TB.i₀ a (TB.b TB.i₀)` as an intermediate fact. Rewrite `this` using `[TB.b_i₀, mul_one, ← TB.b_i₀, TB.c_self, mul_one]`. Conclude with `this`.
-/
theorem coeff_unitIndex_baseMap (TB : TopBasis s I ι) (a : S) : TB.c TB.i₀ (s a) = a := by
  have := TB.c_mul TB.i₀ a (TB.b TB.i₀)
  rw [TB.b_i₀, mul_one, ← TB.b_i₀, TB.c_self, mul_one] at this
  exact this

/- English proof (translation)
Introduce `a b h` and use `by rw [← coeff_unitIndex_baseMap TB a, h, coeff_unitIndex_baseMap]`.
-/
theorem injective (TB : TopBasis s I ι) : Function.Injective s := fun a b h => by
  rw [← coeff_unitIndex_baseMap TB a, h, coeff_unitIndex_baseMap]

/- English proof (translation)
Set `J : Ideal A` to `{ carrier := {y | ∀ a : A, ∀ i, TB.c i (a * y) ∈ L} add_mem' := fun {y z} hy hz a i => by rw [mul_add, map_add]; exact L.add_mem (hy a i) (hz a i) zero_mem' := fun a i => by rw [mul_zero, map_zero]; exact L.zero_mem smul_mem' := fun b y hy a i => by rw [smul_eq_mul, ← mul_assoc]; …`. Establish `hle : L.map s ≤ J` using `Ideal.map_le_iff_le_comap.2 fun y hy a i => by show TB.c i (a * s y) ∈ L`. Rewrite using `[c_s]`. Conclude with `L.mul_mem_right _ hy`. Use `hle hx 1 i` as an intermediate fact.

Rewrite `this` using `[one_mul]`. Then use the resulting hypothesis.
-/
theorem c_mem_of_mem_map (TB : TopBasis s I ι) (L : Ideal S) (x : A) (hx : x ∈ L.map s) (i : ι) :
    TB.c i x ∈ L := by
  let J : Ideal A :=
    { carrier := {y | ∀ a : A, ∀ i, TB.c i (a * y) ∈ L}
      add_mem' := fun {y z} hy hz a i => by rw [mul_add, map_add]; exact L.add_mem (hy a i) (hz a i)
      zero_mem' := fun a i => by rw [mul_zero, map_zero]; exact L.zero_mem
      smul_mem' := fun b y hy a i => by rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b) i }
  have hle : L.map s ≤ J := Ideal.map_le_iff_le_comap.2 fun y hy a i => by
    show TB.c i (a * s y) ∈ L
    rw [c_s]; exact L.mul_mem_right _ hy
  have := hle hx 1 i
  rwa [one_mul] at this

/- English proof (translation)
Use `⟨fun hx i => c_mem_of_mem_map TB L x hx i, fun h => ?_⟩` and prove the remaining obligations. Establish `hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n` using `fun i hi => by`. Simplify using `using hi`. Establish `h1` using `Ideal.map_mono (f := s) hL (TB.approx x n _ hF)`. Establish `h2 : ∑ i ∈ (TB.fin x n).toFinset, s (TB.c i x) * TB.b i ∈ L.map s` using `Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (h i))`.

Simplify using `using Ideal.add_mem _ h1 h2`.
-/
theorem mem_map_iff (TB : TopBasis s I ι) (L : Ideal S) (n : ℕ) (hL : I ^ n ≤ L) (x : A) :
    x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L := by
  refine ⟨fun hx i => c_mem_of_mem_map TB L x hx i, fun h => ?_⟩
  have hF : ∀ i, i ∉ (TB.fin x n).toFinset → TB.c i x ∈ I ^ n := fun i hi => by
    simpa using hi
  have h1 := Ideal.map_mono (f := s) hL (TB.approx x n _ hF)
  have h2 : ∑ i ∈ (TB.fin x n).toFinset, s (TB.c i x) * TB.b i ∈ L.map s :=
    Ideal.sum_mem _ fun i _ => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (h i))
  simpa using Ideal.add_mem _ h1 h2

open Classical in
/- English proof (translation)
Rewrite using `[map_sum]`. Repeatedly rewrite using `[TB.c_mul]`. Use `split_ifs with hi`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [TB.c_ne i j (Ne.symm hj), mul_zero]) (fun h => (h hi).elim), TB.c_self, mul_one]`. Conclude with `Finset.sum_eq_zero fun j hj => by`.

Rewrite using `[TB.c_ne i j (fun e => hi (e ▸ hj)), mul_zero]`.
-/
theorem c_sum (TB : TopBasis s I ι) (z : ι → S) (F : Finset ι) (i : ι) :
    TB.c i (∑ j ∈ F, s (z j) * TB.b j) = if i ∈ F then z i else 0 := by
  rw [map_sum]
  simp_rw [TB.c_mul]
  split_ifs with hi
  · rw [Finset.sum_eq_single i (fun j _ hj => by rw [TB.c_ne i j (Ne.symm hj), mul_zero])
      (fun h => (h hi).elim), TB.c_self, mul_one]
  · exact Finset.sum_eq_zero fun j hj => by
      rw [TB.c_ne i j (fun e => hi (e ▸ hj)), mul_zero]

/- English proof (translation)
Set `F : ℕ → Finset ι` to `fun n => (hz n).toFinset`. Establish `hFm : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n` using `fun {m n} hmn i hi => by`. Simplify using `only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢`. Conclude with `fun h => hi (Ideal.pow_le_pow_right hmn h)`. Establish `hFc : ∀ n i, i ∉ F n → z i ∈ I ^ n` using `fun n i hi => by`.

Simplify `hi` using `[F]`. Set `f : ℕ → A` to `fun n => ∑ i ∈ F n, s (z i) * TB.b i`. Establish `hP : IsPrecomplete (I.map s) A` using `TB.complete.toIsPrecomplete`. Take `⟨x, hx⟩` from `hP.prec' f (fun {m n} hmn => by`. Rewrite using `[sub_mem_iff, ← Ideal.map_pow, ← neg_mem_iff, neg_sub]`.

Use `show (∑ i ∈ F n, s (z i) * TB.b i) - ∑ i ∈ F m, s (z i) * TB.b i ∈ _`. Rewrite using `[← Finset.sum_sdiff (hFm hmn), add_sub_cancel_right]`. Conclude with `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem s (hFc m i (Finset.mem_sdiff.1 hi).2)))`. Use `⟨x, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[← sub_eq_zero]`.

Use `hS.haus _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, smul_top_ideal]`. Establish `h1 : TB.c i (f n - x) ∈ I ^ n`. Use `(sub_mem_iff _ n _ _).1 (hx n)` as an intermediate fact. Rewrite `this` using `[← Ideal.map_pow]`.

Conclude with `c_mem_of_mem_map TB _ _ this i`. Establish `h2 : TB.c i (f n) - z i ∈ I ^ n` using `by show TB.c i (∑ j ∈ F n, s (z j) * TB.b j) - z i ∈ I ^ n`. Rewrite using `[c_sum]`. Use `split_ifs with hi`. Rewrite using `[sub_self]`.

Conclude with `zero_mem _`. Rewrite using `[zero_sub, neg_mem_iff]`. Conclude with `hFc n i hi`. Use `Ideal.sub_mem _ h2 h1` as an intermediate fact. Rewrite `this` using `[map_sub]`.

Simplify using `using this`.
-/
theorem exists_c_eq (TB : TopBasis s I ι) (hS : IsHausdorff I S) (z : ι → S)
    (hz : ∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) : ∃ x, ∀ i, TB.c i x = z i := by
  classical
  let F : ℕ → Finset ι := fun n => (hz n).toFinset
  have hFm : ∀ {m n : ℕ}, m ≤ n → F m ⊆ F n := fun {m n} hmn i hi => by
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  have hFc : ∀ n i, i ∉ F n → z i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  let f : ℕ → A := fun n => ∑ i ∈ F n, s (z i) * TB.b i
  have hP : IsPrecomplete (I.map s) A := TB.complete.toIsPrecomplete
  obtain ⟨x, hx⟩ := hP.prec' f (fun {m n} hmn => by
    rw [sub_mem_iff, ← Ideal.map_pow, ← neg_mem_iff, neg_sub]
    show (∑ i ∈ F n, s (z i) * TB.b i) - ∑ i ∈ F m, s (z i) * TB.b i ∈ _
    rw [← Finset.sum_sdiff (hFm hmn), add_sub_cancel_right]
    exact Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _
      (Ideal.mem_map_of_mem s (hFc m i (Finset.mem_sdiff.1 hi).2)))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, smul_top_ideal]
  have h1 : TB.c i (f n - x) ∈ I ^ n := by
    have := (sub_mem_iff _ n _ _).1 (hx n)
    rw [← Ideal.map_pow] at this
    exact c_mem_of_mem_map TB _ _ this i
  have h2 : TB.c i (f n) - z i ∈ I ^ n := by
    show TB.c i (∑ j ∈ F n, s (z j) * TB.b j) - z i ∈ I ^ n
    rw [c_sum]
    split_ifs with hi
    · rw [sub_self]; exact zero_mem _
    · rw [zero_sub, neg_mem_iff]; exact hFc n i hi
  have := Ideal.sub_mem _ h2 h1
  rw [map_sub] at this
  simpa using this

/- English proof (translation)
Rewrite using `[mem_nonZeroDivisors_iff]`. Use `⟨fun x hx => eq_zero_of_c TB x fun i => ?_, fun x hx => eq_zero_of_c TB x fun i => ?_⟩` and prove the remaining obligations. Use `congrArg (TB.c i) hx` as an intermediate fact. Rewrite `this` using `[TB.c_mul, map_zero]`. Use `first`.

Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).1 _ this`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).2 _ this`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)`. Use `congrArg (TB.c i) hx` as an intermediate fact.

Rewrite `this` using `[c_s, map_zero]`. Use `first`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).1 _ this`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)`. Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).2 _ this`.

Consider the case `exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)`.
-/
theorem map_nonZeroDivisors (TB : TopBasis s I ι) (a : S) (ha : a ∈ nonZeroDivisors S) :
    s a ∈ nonZeroDivisors A := by
  rw [mem_nonZeroDivisors_iff]
  refine ⟨fun x hx => eq_zero_of_c TB x fun i => ?_, fun x hx => eq_zero_of_c TB x fun i => ?_⟩
  · have := congrArg (TB.c i) hx
    rw [TB.c_mul, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)
  · have := congrArg (TB.c i) hx
    rw [c_s, map_zero] at this
    first
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).1 _ (by rw [mul_comm]; exact this)
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ this
    | exact (mem_nonZeroDivisors_iff.1 ha).2 _ (by rw [mul_comm]; exact this)

end GlobalTheory.BSP.TopBasis

/- English proof (translation)
Introduce `S A _ _ s I ι TB hS`. Conclude with `⟨TB.eq_zero_of_c, TB.injective, TB.mem_map_iff, TB.exists_c_eq hS, TB.map_nonZeroDivisors⟩`.
-/
theorem GlobalTheory.BSP.TopBasis.basic_facts : ∀ (S A : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S) (ι : Type) (TB : TopBasis s I ι), IsHausdorff I S → (∀ x, (∀ i, TB.c i x = 0) → x = 0) ∧ Function.Injective s ∧ (∀ (L : Ideal S) (n : ℕ), I ^ n ≤ L → ∀ x, x ∈ L.map s ↔ ∀ i, TB.c i x ∈ L) ∧ (∀ z : ι → S, (∀ n : ℕ, {i | z i ∉ I ^ n}.Finite) → ∃ x, ∀ i, TB.c i x = z i) ∧ ∀ a ∈ nonZeroDivisors S, s a ∈ nonZeroDivisors A := by
  intro S A _ _ s I ι TB hS
  exact ⟨TB.eq_zero_of_c, TB.injective, TB.mem_map_iff, TB.exists_c_eq hS, TB.map_nonZeroDivisors⟩
