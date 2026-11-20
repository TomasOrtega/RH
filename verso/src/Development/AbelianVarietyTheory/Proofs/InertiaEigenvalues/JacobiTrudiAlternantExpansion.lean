import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SchurEqJtDet
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddLeOfStrictAnti

noncomputable section

open MvPolynomial Finset Equiv

namespace GlobalTheory.JSW

def antisymHExt {A : Type*} [CommRing A] (h : ℕ → A) (z : ℤ) : A :=
  if z < 0 then 0 else h z.toNat

def antisymMat {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (ν : Fin m → ℕ) :
    Matrix (Fin m) (Fin m) A :=
  Matrix.of fun i j => antisymHExt h ((ν j : ℤ) - staircase m i)

/- English proof (translation)
Rewrite using `[alternant, Matrix.det_apply']`. Simplify using `[Matrix.of_apply]`.
-/
theorem alternant_eq_sum_perm {A : Type*} [CommRing A] (m : ℕ) (μ : Fin m → ℕ) :
    alternant A m μ = ∑ σ : Perm (Fin m),
      ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) * ∏ i, X i ^ μ (σ i) := by
  rw [alternant, Matrix.det_apply']
  simp [Matrix.of_apply]

/- English proof (translation)
Use `set F : (Fin m → ℕ) → MvPolynomial (Fin m) A := fun ν => (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, X j ^ ν j with hF`. Establish `key : ∀ k : Fin m → ℕ, (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) * ∏ j, C (h (k j)) * X j ^ (k j) = F (k + μ)`. Introduce `k`. Simplify using `only [hF]`. Rewrite using `[← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]`.

Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `e : (((k + μ) j : ℕ) : ℤ) - μ j = k j` using `by simp`. Rewrite using `[e, antisymHExt, if_neg (not_lt.2 (Int.natCast_nonneg _)), Int.toNat_natCast, Pi.add_apply, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.mul_sum, Finset.sum_congr rfl fun k _ => key k]`.

Rewrite using `[← Finset.sum_image (g := fun k => k + μ) (by intro a _ b _ hab; exact add_right_cancel hab)]`. Apply `Finset.sum_subset` to reduce the goal to its premises. Introduce `ν hν`. Take `⟨k, hk, rfl⟩` from `Finset.mem_image.1 hν`. Rewrite `hk`, the goal using `[Finset.Nat.mem_antidiagonalTuple]`.

Simplify using `[Finset.sum_add_distrib, hk]`. Introduce `ν hν hnot`. Distinguish the cases in `hle : ∀ j, μ j ≤ ν j`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises.

Use `Finset.mem_image.2 ⟨ν - μ, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hν`, the goal using `[Finset.Nat.mem_antidiagonalTuple]`. Establish `: ∑ i, (ν - μ) i + ∑ i, μ i = ∑ i, ν i`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)`.

Use linear arithmetic over natural numbers and integers. Use function extensionality and compare the values at `j`. Simplify using `[Nat.sub_add_cancel (hle j)]`. Use `push_neg at hle`. Take `⟨j, hj⟩` from `hle`.

Simplify using `only [hF]`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]`. Rewrite using `[antisymHExt, if_pos (by omega), map_zero]`.
-/
theorem antisym_shift_sum {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) (μ : Fin m → ℕ) :
    (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, μ i),
        (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  classical
  set F : (Fin m → ℕ) → MvPolynomial (Fin m) A :=
    fun ν => (∏ j, C (antisymHExt h ((ν j : ℤ) - μ j))) * ∏ j, X j ^ ν j with hF
  have key : ∀ k : Fin m → ℕ, (∏ i, (X i : MvPolynomial (Fin m) A) ^ μ i) *
      ∏ j, C (h (k j)) * X j ^ (k j) = F (k + μ) := by
    intro k
    simp only [hF]
    rw [← Finset.prod_mul_distrib, ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun j _ => ?_
    have e : (((k + μ) j : ℕ) : ℤ) - μ j = k j := by simp
    rw [e, antisymHExt, if_neg (not_lt.2 (Int.natCast_nonneg _)), Int.toNat_natCast, Pi.add_apply, pow_add]
    ring
  rw [Finset.mul_sum, Finset.sum_congr rfl fun k _ => key k]
  rw [← Finset.sum_image (g := fun k => k + μ) (by intro a _ b _ hab; exact add_right_cancel hab)]
  apply Finset.sum_subset
  · intro ν hν
    obtain ⟨k, hk, rfl⟩ := Finset.mem_image.1 hν
    rw [Finset.Nat.mem_antidiagonalTuple] at hk ⊢
    simp [Finset.sum_add_distrib, hk]
  · intro ν hν hnot
    by_cases hle : ∀ j, μ j ≤ ν j
    · exfalso
      apply hnot
      refine Finset.mem_image.2 ⟨ν - μ, ?_, ?_⟩
      · rw [Finset.Nat.mem_antidiagonalTuple] at hν ⊢
        have : ∑ i, (ν - μ) i + ∑ i, μ i = ∑ i, ν i := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hle i)
        omega
      · funext j
        simp [Nat.sub_add_cancel (hle j)]
    · push_neg at hle
      obtain ⟨j, hj⟩ := hle
      simp only [hF]
      rw [Finset.prod_eq_zero (Finset.mem_univ j), zero_mul]
      rw [antisymHExt, if_pos (by omega), map_zero]

/- English proof (translation)
Rewrite using `[alternant_eq_sum_perm, Finset.sum_mul]`. Establish `hσ : ∀ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) * (∏ i, X i ^ staircase m (σ i)) * ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) = ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i), (((Perm.sign σ : ℤ) : MvPolynomial (Fin …`. Introduce `σ`. Rewrite using `[mul_assoc, antisym_shift_sum m d h (fun i => staircase m (σ i)), Equiv.sum_comp σ (staircase m), Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun ν _ => by ring`.

Rewrite using `[Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun ν _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_mul, Matrix.det_apply', map_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_intCast, map_prod]`. Both sides reduce to the same expression.
-/
theorem antisym_lhs_eq {A : Type*} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
  rw [alternant_eq_sum_perm, Finset.sum_mul]
  have hσ : ∀ σ : Perm (Fin m), ((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
      (∏ i, X i ^ staircase m (σ i)) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, C (h (k j)) * X j ^ (k j) =
      ∑ ν ∈ Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i),
        (((Perm.sign σ : ℤ) : MvPolynomial (Fin m) A) *
          ∏ j, C (antisymHExt h ((ν j : ℤ) - staircase m (σ j)))) * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j := by
    intro σ
    rw [mul_assoc, antisym_shift_sum m d h (fun i => staircase m (σ i)),
      Equiv.sum_comp σ (staircase m), Finset.mul_sum]
    exact Finset.sum_congr rfl fun ν _ => by ring
  rw [Finset.sum_congr rfl fun σ _ => hσ σ, Finset.sum_comm]
  refine Finset.sum_congr rfl fun ν _ => ?_
  rw [← Finset.sum_mul, Matrix.det_apply', map_sum]
  congr 1
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [map_mul, map_intCast, map_prod]
  rfl

/- English proof (translation)
Rewrite using `[← Matrix.det_permute']`. Both sides reduce to the same expression.
-/
theorem antisymMat_comp_perm {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (μ : Fin m → ℕ)
    (τ : Perm (Fin m)) :
    (antisymMat m h (fun i => μ (τ i))).det = (Perm.sign τ : ℤ) * (antisymMat m h μ).det := by
  rw [← Matrix.det_permute']
  rfl

/- English proof (translation)
Rewrite using `[jtDet, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `i j`. Establish `hi` using `i.2`. Establish `hj` using `j.2`.

Establish `e : (((l i + staircase m i : ℕ)) : ℤ) - (staircase m j : ℕ) = (l i : ℤ) - i + j`. Simplify using `only [staircase]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [antisymMat, Matrix.of_apply, Matrix.transpose_apply, antisymHExt]`. Rewrite using `[e]`.
-/
theorem antisymMat_staircase {A : Type*} [CommRing A] (m : ℕ) (h : ℕ → A) (l : Fin m → ℕ) :
    (antisymMat m h (fun i => l i + staircase m i)).det = jtDet m h l := by
  rw [jtDet, ← Matrix.det_transpose]
  congr 1
  ext i j
  have hi := i.2
  have hj := j.2
  have e : (((l i + staircase m i : ℕ)) : ℤ) - (staircase m j : ℕ) = (l i : ℤ) - i + j := by
    simp only [staircase]
    omega
  simp only [antisymMat, Matrix.of_apply, Matrix.transpose_apply, antisymHExt]
  rw [e]

/- English proof (translation)
Introduce `i j hij`. Establish `h1` using `hl hij.le`. Establish `h2 : (i : ℕ) < j` using `hij`. Use `j.2` as an intermediate fact. Simplify using `only [staircase]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem antisym_strictAnti {m : ℕ} {l : Fin m → ℕ} (hl : Antitone l) :
    StrictAnti (fun i => l i + staircase m i) := by
  intro i j hij
  have h1 := hl hij.le
  have h2 : (i : ℕ) < j := hij
  have := j.2
  simp only [staircase]
  omega

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti`. Consider the case `exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti`. Consider the case `(apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti ..)`.
-/
theorem antisym_gap {m : ℕ} {s : Fin m → ℕ} (hs : StrictAnti s) :
    ∀ (k : ℕ) (i j : Fin m), (j : ℕ) = i + k → s j + k ≤ s i := by
  first
  | exact @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti
  | (apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> assumption)
  | (intros; apply @_root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.StrictAntiAddLe.add_le_of_strictAnti ..)

open Classical in

/- English proof (translation)
Rewrite using `[← Finset.sum_product']`. Use `Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i) + staircase m (p.2 i)) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `p hp`. Take `⟨hl, -⟩` from `Finset.mem_product.1 hp`. Rewrite `hl` using `[mem_antiParts]`.

Rewrite using `[Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Equiv.sum_comp p.2 (fun i => p.1 i + staircase m i), Finset.sum_add_distrib, hl.1]`. Conclude with `(antisym_strictAnti hl.2).injective.comp p.2.injective`. Introduce `p hp q hq hpq`.

Take `⟨hl, -⟩` from `Finset.mem_product.1 hp`. Take `⟨hl', -⟩` from `Finset.mem_product.1 hq`. Rewrite `hl`, `hl'` using `[mem_antiParts]`. Use `set ν : Fin m → ℕ := fun i => p.1 (p.2 i) + staircase m (p.2 i) with hν`. Establish `hν' : ν = fun i => q.1 (q.2 i) + staircase m (q.2 i)` using `hpq`.

Establish `a1 : Antitone (ν ∘ p.2.symm)`. Establish `: ν ∘ p.2.symm = fun i => p.1 i + staircase m i` using `by funext i; simp [hν]`. Rewrite using `[this]`. Conclude with `(antisym_strictAnti hl.2).antitone`. Establish `a2 : Antitone (ν ∘ q.2.symm)`.

Establish `: ν ∘ q.2.symm = fun i => q.1 i + staircase m i` using `by funext i; simp [hν']`. Rewrite using `[this]`. Conclude with `(antisym_strictAnti hl'.2).antitone`. Establish `u` using `Tuple.unique_antitone a1 a2`. Establish `hinj : Function.Injective ν` using `(antisym_strictAnti hl.2).injective.comp p.2.injective`.

Establish `hperm : p.2.symm = q.2.symm` using `Equiv.ext fun i => hinj (congrFun u i)`. Establish `h2 : p.2 = q.2` using `by simpa using congrArg Equiv.symm hperm`. Establish `h1 : p.1 = q.1`. Use function extensionality and compare the values at `i`. Use `congrFun hν' (p.2.symm i)` as an intermediate fact.

Simplify using `only [hν, h2, Equiv.apply_symm_apply] at this`. Use linear arithmetic over natural numbers and integers. Conclude with `Prod.ext h1 h2`. Introduce `ν hν`. Rewrite `hν` using `[Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]`.

Take `⟨hsum, hinj⟩` from `hν`. Use `set σ := Tuple.sort (fun i => OrderDual.toDual (ν i)) with hσ`. Establish `hanti : Antitone (ν ∘ σ)`. Use `Tuple.monotone_sort (fun i => OrderDual.toDual (ν i))` as an intermediate fact. Conclude with `monotone_toDual_comp_iff.1 this`.

Establish `hs : StrictAnti (ν ∘ σ)` using `hanti.strictAnti_of_injective (hinj.comp σ.injective)`. Establish `hδ : ∀ i, staircase m i ≤ ν (σ i)`. Introduce `i`. Establish `hm : m - 1 < m` using `by have := i.2; omega`. Use `antisym_gap hs (m - 1 - i) i ⟨m - 1, hm⟩ (by simp; have := i.2; omega)` as an intermediate fact.

Simplify using `only [staircase, Function.comp] at this ⊢`. Use linear arithmetic over natural numbers and integers. Use `⟨(fun i => ν (σ i) - staircase m i, σ.symm), ?_, ?_⟩` and prove the remaining obligations. Use `Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩` and prove the remaining obligations. Rewrite using `[mem_antiParts]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Use `show ∑ i, (ν (σ i) - staircase m i) = d`. Establish `e : ∑ i, (ν (σ i) - staircase m i) + ∑ i, staircase m i = ∑ i, ν (σ i)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hδ i)`.

Rewrite `e` using `[Equiv.sum_comp σ ν]`. Use linear arithmetic over natural numbers and integers. Introduce `i j hij`. Establish `g` using `antisym_gap hs (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)`. Establish `h1` using `hδ i`.

Establish `h2` using `hδ j`. Simplify using `only [staircase, Function.comp] at g h1 h2 ⊢`. Use `j.2` as an intermediate fact. Establish `: (i : ℕ) ≤ j` using `hij`. Use linear arithmetic over natural numbers and integers.

Use function extensionality and compare the values at `i`. Use `hδ (σ.symm i)` as an intermediate fact. Simplify using `only [Equiv.apply_symm_apply] at this ⊢`. Use linear arithmetic over natural numbers and integers. Introduce `p _`.

Both sides reduce to the same expression.
-/
theorem antisym_sum_sort {M : Type*} [AddCommMonoid M] (m d : ℕ) (g : (Fin m → ℕ) → M) :
    ∑ l ∈ antiParts m d, ∑ τ : Perm (Fin m), g (fun i => l (τ i) + staircase m (τ i)) =
      ∑ ν ∈ (Finset.Nat.antidiagonalTuple m (d + ∑ i, staircase m i)).filter Function.Injective, g ν := by
  rw [← Finset.sum_product']
  refine Finset.sum_bij (fun p _ => fun i => p.1 (p.2 i) + staircase m (p.2 i)) ?_ ?_ ?_ ?_
  · intro p hp
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    rw [mem_antiParts] at hl
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple]
    refine ⟨?_, ?_⟩
    · rw [Equiv.sum_comp p.2 (fun i => p.1 i + staircase m i), Finset.sum_add_distrib, hl.1]
    · exact (antisym_strictAnti hl.2).injective.comp p.2.injective
  · intro p hp q hq hpq
    obtain ⟨hl, -⟩ := Finset.mem_product.1 hp
    obtain ⟨hl', -⟩ := Finset.mem_product.1 hq
    rw [mem_antiParts] at hl hl'
    set ν : Fin m → ℕ := fun i => p.1 (p.2 i) + staircase m (p.2 i) with hν
    have hν' : ν = fun i => q.1 (q.2 i) + staircase m (q.2 i) := hpq
    have a1 : Antitone (ν ∘ p.2.symm) := by
      have : ν ∘ p.2.symm = fun i => p.1 i + staircase m i := by funext i; simp [hν]
      rw [this]; exact (antisym_strictAnti hl.2).antitone
    have a2 : Antitone (ν ∘ q.2.symm) := by
      have : ν ∘ q.2.symm = fun i => q.1 i + staircase m i := by funext i; simp [hν']
      rw [this]; exact (antisym_strictAnti hl'.2).antitone
    have u := Tuple.unique_antitone a1 a2
    have hinj : Function.Injective ν := (antisym_strictAnti hl.2).injective.comp p.2.injective
    have hperm : p.2.symm = q.2.symm := Equiv.ext fun i => hinj (congrFun u i)
    have h2 : p.2 = q.2 := by simpa using congrArg Equiv.symm hperm
    have h1 : p.1 = q.1 := by
      funext i
      have := congrFun hν' (p.2.symm i)
      simp only [hν, h2, Equiv.apply_symm_apply] at this
      omega
    exact Prod.ext h1 h2
  · intro ν hν
    rw [Finset.mem_filter, Finset.Nat.mem_antidiagonalTuple] at hν
    obtain ⟨hsum, hinj⟩ := hν
    set σ := Tuple.sort (fun i => OrderDual.toDual (ν i)) with hσ
    have hanti : Antitone (ν ∘ σ) := by
      have := Tuple.monotone_sort (fun i => OrderDual.toDual (ν i))
      exact monotone_toDual_comp_iff.1 this
    have hs : StrictAnti (ν ∘ σ) := hanti.strictAnti_of_injective (hinj.comp σ.injective)
    have hδ : ∀ i, staircase m i ≤ ν (σ i) := by
      intro i
      have hm : m - 1 < m := by have := i.2; omega
      have := antisym_gap hs (m - 1 - i) i ⟨m - 1, hm⟩ (by simp; have := i.2; omega)
      simp only [staircase, Function.comp] at this ⊢
      omega
    refine ⟨(fun i => ν (σ i) - staircase m i, σ.symm), ?_, ?_⟩
    · refine Finset.mem_product.2 ⟨?_, Finset.mem_univ _⟩
      rw [mem_antiParts]
      refine ⟨?_, ?_⟩
      · show ∑ i, (ν (σ i) - staircase m i) = d
        have e : ∑ i, (ν (σ i) - staircase m i) + ∑ i, staircase m i = ∑ i, ν (σ i) := by
          rw [← Finset.sum_add_distrib]
          exact Finset.sum_congr rfl fun i _ => Nat.sub_add_cancel (hδ i)
        rw [Equiv.sum_comp σ ν] at e
        omega
      · intro i j hij
        have g := antisym_gap hs (j - i) i j (by have : (i : ℕ) ≤ j := hij; omega)
        have h1 := hδ i
        have h2 := hδ j
        simp only [staircase, Function.comp] at g h1 h2 ⊢
        have := j.2
        have : (i : ℕ) ≤ j := hij
        omega
    · funext i
      have := hδ (σ.symm i)
      simp only [Equiv.apply_symm_apply] at this ⊢
      omega
  · intro p _
    rfl

/- English proof (translation)
Rewrite using `[antisym_lhs_eq]`. Establish `hr : ∀ l : Fin m → ℕ, C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) = ∑ τ : Perm (Fin m), (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j) (fun i => l (τ i) + staircase m (τ i))`. Introduce `l`. Rewrite using `[alternant_eq_sum_perm, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun τ _ => ?_` and prove the remaining obligations.

Establish `e` using `antisymMat_comp_perm m h (fun i => l i + staircase m i) τ`. Simplify using `only at e ⊢`. Rewrite using `[e, antisymMat_staircase, map_mul, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[Finset.sum_congr rfl fun l _ => hr l, antisym_sum_sort m d (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)]`.

Use `symm`. Apply `Finset.sum_filter_of_ne` to reduce the goal to its premises. Introduce `ν _ hne`. Assume the negation of the conclusion as `hni`. Apply `hne` to reduce the goal to its premises.

Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab, hne'⟩ : ∃ a b, ν a = ν b ∧ a ≠ b := by`. Simplify using `only [Function.Injective, not_forall] at hni`. Take `⟨a, b, hab, hne⟩` from `hni`. Conclude with `⟨a, b, hab, hne⟩`. Rewrite using `[Matrix.det_zero_of_column_eq hne' (fun k => by simp [antisymMat, hab]), map_zero, zero_mul]`.
-/
theorem alternant_staircase_mul_antidiagonal {A : Type} [CommRing A] (m d : ℕ) (h : ℕ → A) :
    alternant A m (staircase m) *
        ∑ k ∈ Finset.Nat.antidiagonalTuple m d, ∏ j, MvPolynomial.C (h (k j)) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts m d,
        MvPolynomial.C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) := by
  classical
  rw [antisym_lhs_eq]
  have hr : ∀ l : Fin m → ℕ, C (jtDet m h l) * alternant A m (fun i => l i + staircase m i) =
      ∑ τ : Perm (Fin m), (fun ν : Fin m → ℕ =>
        C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)
        (fun i => l (τ i) + staircase m (τ i)) := by
    intro l
    rw [alternant_eq_sum_perm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun τ _ => ?_
    have e := antisymMat_comp_perm m h (fun i => l i + staircase m i) τ
    simp only at e ⊢
    rw [e, antisymMat_staircase, map_mul, map_intCast]
    ring
  rw [Finset.sum_congr rfl fun l _ => hr l, antisym_sum_sort m d
    (fun ν : Fin m → ℕ => C (antisymMat m h ν).det * ∏ j, (X j : MvPolynomial (Fin m) A) ^ ν j)]
  symm
  apply Finset.sum_filter_of_ne
  intro ν _ hne
  by_contra hni
  apply hne
  obtain ⟨a, b, hab, hne'⟩ : ∃ a b, ν a = ν b ∧ a ≠ b := by
    simp only [Function.Injective, not_forall] at hni
    obtain ⟨a, b, hab, hne⟩ := hni
    exact ⟨a, b, hab, hne⟩
  rw [Matrix.det_zero_of_column_eq hne' (fun k => by simp [antisymMat, hab]), map_zero, zero_mul]

/- English proof (translation)
The claim follows from `alternant_staircase_mul_antidiagonal 2 1 (fun k => (k : ℤ) + 1)`.
-/
example : alternant ℤ 2 (staircase 2) *
    ∑ k ∈ Finset.Nat.antidiagonalTuple 2 1, ∏ j, MvPolynomial.C ((k j : ℤ) + 1) * MvPolynomial.X j ^ (k j) =
      ∑ l ∈ antiParts 2 1, MvPolynomial.C (jtDet 2 (fun k => (k : ℤ) + 1) l) *
        alternant ℤ 2 (fun i => l i + staircase 2 i) :=
  alternant_staircase_mul_antidiagonal 2 1 (fun k => (k : ℤ) + 1)

end GlobalTheory.JSW
