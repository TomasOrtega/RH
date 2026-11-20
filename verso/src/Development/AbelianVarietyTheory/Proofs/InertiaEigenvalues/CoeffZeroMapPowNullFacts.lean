import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsStratHom
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.BSP.TopBasis

variable {S A ι : Type} [CommRing S] [CommRing A] {s : S →+* A} {I : Ideal S}

/- English proof (translation)
Rewrite using `[smul_eq_mul, Ideal.mul_top]`.
-/
theorem pow_smul_top_eq {R : Type} [CommRing R] (J : Ideal R) (n : ℕ) :
    (J ^ n • ⊤ : Submodule R R) = J ^ n := by
  rw [smul_eq_mul, Ideal.mul_top]

/- English proof (translation)
Establish `key : ∀ a : A, tb.c i (a * x) ∈ I ^ n`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨z, hz, rfl⟩` from `hy`. Introduce `a`.

Rewrite using `[mul_comm, tb.c_mul]`. Conclude with `Ideal.mul_mem_right _ _ hz`. Consider the case `zero => intro a`. Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz => intro a`.

Rewrite using `[mul_add, map_add]`. Conclude with `add_mem (hy a) (hz a)`. Consider the case `smul b y _ hy => intro a`. Rewrite using `[smul_eq_mul, ← mul_assoc]`. Conclude with `hy (a * b)`.

Simplify using `using key 1`.
-/
theorem c_mem_of_mem (tb : TopBasis s I ι) (n : ℕ) {x : A} (hx : x ∈ (I ^ n).map s) (i : ι) :
    tb.c i x ∈ I ^ n := by
  have key : ∀ a : A, tb.c i (a * x) ∈ I ^ n := by
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨z, hz, rfl⟩ := hy
      intro a
      rw [mul_comm, tb.c_mul]
      exact Ideal.mul_mem_right _ _ hz
    | zero => intro a; simp
    | add y z _ _ hy hz => intro a; rw [mul_add, map_add]; exact add_mem (hy a) (hz a)
    | smul b y _ hy => intro a; rw [smul_eq_mul, ← mul_assoc]; exact hy (a * b)
  simpa using key 1

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩`.
-/
theorem mem_map_pow_iff (tb : TopBasis s I ι) (n : ℕ) (x : A) :
    x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n :=
  ⟨fun h i => c_mem_of_mem tb n h i, fun h => by simpa using tb.approx x n ∅ (fun i _ => h i)⟩

/- English proof (translation)
Use `tb.complete.toIsHausdorff.haus x fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]`. Conclude with `(mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _`.
-/
theorem eq_zero_of_c_eq_zero (tb : TopBasis s I ι) (x : A) (h : ∀ i, tb.c i x = 0) : x = 0 := by
  refine tb.complete.toIsHausdorff.haus x fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq, ← Ideal.map_pow]
  exact (mem_map_pow_iff tb n x).2 fun i => by rw [h i]; exact zero_mem _

/- English proof (translation)
Set `F : ℕ → Finset ι` to `fun n => (ha n).toFinset`. Establish `hF : ∀ n i, i ∉ F n → a i ∈ I ^ n` using `fun n i hi => by`. Simplify `hi` using `[F]`. Establish `hFm : Monotone F`. Introduce `m n hmn i hi`.

Simplify using `only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢`. Conclude with `fun h => hi (Ideal.pow_le_pow_right hmn h)`. Set `y : ℕ → A` to `fun n => ∑ i ∈ F n, s (a i) * tb.b i`. Establish `hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s`. Introduce `m n hmn`.

Establish `e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i`. Simplify using `only [y]`. Rewrite using `[← Finset.sum_sdiff (hFm hmn)]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `Ideal.sum_mem _ fun i hi => Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))`. Take `⟨x, hx⟩` from `tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by`. Rewrite using `[SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]`. Conclude with `neg_mem (hy m n hmn))`. Use `⟨x, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[← sub_eq_zero]`. Use `hS.haus _ fun n => ?_` and prove the remaining obligations. Rewrite using `[SModEq.sub_mem, sub_zero, pow_smul_top_eq]`. Establish `h1 : tb.c i (x - y n) ∈ I ^ n`. Establish `h` using `hx n`.

Rewrite `h` using `[SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]`. Conclude with `c_mem_of_mem tb n (by simpa using neg_mem h) i`. Establish `h2 : tb.c i (y n) - a i ∈ I ^ n`. Establish `e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j)`. Simplify using `only [y, map_sum, tb.c_mul]`.

Rewrite using `[e]`. Distinguish the cases in `hi : i ∈ F n`. Rewrite using `[Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero]) (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]`. Conclude with `zero_mem _`. Rewrite using `[Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]`.

Conclude with `neg_mem (hF n i hi)`. Establish `e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i)` using `by rw [map_sub]; ring`. Rewrite using `[e]`. Conclude with `add_mem h1 h2`.
-/
theorem exists_coeffs_eq_of_null (tb : TopBasis s I ι) (hS : IsHausdorff I S) (a : ι → S)
    (ha : ∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) : ∃ x, ∀ i, tb.c i x = a i := by
  classical
  let F : ℕ → Finset ι := fun n => (ha n).toFinset
  have hF : ∀ n i, i ∉ F n → a i ∈ I ^ n := fun n i hi => by
    simpa [F] using hi
  have hFm : Monotone F := by
    intro m n hmn i hi
    simp only [F, Set.Finite.mem_toFinset, Set.mem_setOf_eq] at hi ⊢
    exact fun h => hi (Ideal.pow_le_pow_right hmn h)
  let y : ℕ → A := fun n => ∑ i ∈ F n, s (a i) * tb.b i
  have hy : ∀ m n, m ≤ n → y n - y m ∈ (I ^ m).map s := by
    intro m n hmn
    have e : y n - y m = ∑ i ∈ F n \ F m, s (a i) * tb.b i := by
      simp only [y]; rw [← Finset.sum_sdiff (hFm hmn)]; ring
    rw [e]
    exact Ideal.sum_mem _ fun i hi =>
      Ideal.mul_mem_right _ _ (Ideal.mem_map_of_mem _ (hF m i (Finset.mem_sdiff.1 hi).2))
  obtain ⟨x, hx⟩ := tb.complete.toIsPrecomplete.prec (f := y) (fun {m n} hmn => by
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub]
    exact neg_mem (hy m n hmn))
  refine ⟨x, fun i => ?_⟩
  rw [← sub_eq_zero]
  refine hS.haus _ fun n => ?_
  rw [SModEq.sub_mem, sub_zero, pow_smul_top_eq]
  have h1 : tb.c i (x - y n) ∈ I ^ n := by
    have h := hx n
    rw [SModEq.sub_mem, pow_smul_top_eq, ← Ideal.map_pow, ← neg_sub] at h
    exact c_mem_of_mem tb n (by simpa using neg_mem h) i
  have h2 : tb.c i (y n) - a i ∈ I ^ n := by
    have e : tb.c i (y n) = ∑ j ∈ F n, a j * tb.c i (tb.b j) := by
      simp only [y, map_sum, tb.c_mul]
    rw [e]
    by_cases hi : i ∈ F n
    · rw [Finset.sum_eq_single i (fun j _ hj => by rw [tb.c_ne i j (Ne.symm hj), mul_zero])
        (fun h => (h hi).elim), tb.c_self, mul_one, sub_self]
      exact zero_mem _
    · rw [Finset.sum_eq_zero (fun j hj => by rw [tb.c_ne i j (fun h => hi (h ▸ hj)), mul_zero]), zero_sub]
      exact neg_mem (hF n i hi)
  have e : tb.c i x - a i = tb.c i (x - y n) + (tb.c i (y n) - a i) := by rw [map_sub]; ring
  rw [e]
  exact add_mem h1 h2

end GlobalTheory.BSP.TopBasis

/- English proof (translation)
Introduce `_ _ _ _ _ _ _ tb` and use `⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb, fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩`.
-/
theorem GlobalTheory.BSP.TopBasis.coeff_facts : ∀ (S A ι : Type) [CommRing S] [CommRing A] (s : S →+* A) (I : Ideal S)
    (tb : TopBasis s I ι), (∀ x, (∀ i, tb.c i x = 0) → x = 0) ∧ (∀ (n : ℕ) x, x ∈ (I ^ n).map s ↔ ∀ i, tb.c i x ∈ I ^ n) ∧
    (IsHausdorff I S → ∀ a : ι → S, (∀ n : ℕ, {i | a i ∉ I ^ n}.Finite) → ∃ x, ∀ i, tb.c i x = a i) :=
  fun _ _ _ _ _ _ _ tb => ⟨GlobalTheory.BSP.TopBasis.eq_zero_of_c_eq_zero tb, GlobalTheory.BSP.TopBasis.mem_map_pow_iff tb,
    fun hS a ha => GlobalTheory.BSP.TopBasis.exists_coeffs_eq_of_null tb hS a ha⟩
