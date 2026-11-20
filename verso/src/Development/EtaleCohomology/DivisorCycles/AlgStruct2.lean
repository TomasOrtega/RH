import Development.EtaleCohomology.DivisorCycles.CycleCount

open Matrix
namespace LateralTheory.DivDb
namespace AlgStruct₂

variable {C : Type} [Field C] {N n : ℕ} {p : Fin n → Mat C N}

/- English proof (translation)
The claim follows from `(hp.1.idem i).eq`.
-/
theorem pp (hp : Sys p) (i : Fin n) : p i * p i = p i := (hp.1.idem i).eq
/- English proof (translation)
Rewrite using `[← mul_assoc, pp hp]`.
-/
theorem pp' (hp : Sys p) (i : Fin n) (X : Mat C N) : p i * (p i * X) = p i * X := by
  rw [← mul_assoc, pp hp]
/- English proof (translation)
The claim follows from `hp.1.ortho h`.
-/
theorem pq (hp : Sys p) {i j : Fin n} (h : i ≠ j) : p i * p j = 0 := hp.1.ortho h
/- English proof (translation)
Rewrite using `[← mul_assoc, pq hp h, zero_mul]`.
-/
theorem pq' (hp : Sys p) {i j : Fin n} (h : i ≠ j) (X : Mat C N) : p i * (p j * X) = 0 := by
  rw [← mul_assoc, pq hp h, zero_mul]

/- English proof (translation)
Distinguish the cases in `h : m = i`. Rewrite using `[h]`. Simplify using `only [mul_assoc, pp hp, pp' hp]`. Simplify using `only [mul_assoc, pq hp (Ne.symm h), pq' hp h, mul_zero]`.
-/
theorem corner_comm (hp : Sys p) (X : Mat C N) (i m : Fin n) :
    p i * X * p i * p m = p m * (p i * X * p i) := by
  by_cases h : m = i
  · rw [h]; simp only [mul_assoc, pp hp, pp' hp]
  · simp only [mul_assoc, pq hp (Ne.symm h), pq' hp h, mul_zero]

/- English proof (translation)
Establish `h1 : a * b = a * (∑ j, p j) * b` using `by rw [hp.1.complete, mul_one]`. Rewrite using `[h1]`. Simplify using `only [Finset.mul_sum, Finset.sum_mul]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [mul_assoc, pp' hp]`.
-/
theorem decomp (hp : Sys p) (a b : Mat C N) (i k : Fin n) :
    p i * (a * b) * p k = ∑ j, p i * a * p j * (p j * b * p k) := by
  have h1 : a * b = a * (∑ j, p j) * b := by rw [hp.1.complete, mul_one]
  rw [h1]; simp only [Finset.mul_sum, Finset.sum_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [mul_assoc, pp' hp]

/- English proof (translation)
Establish `h : Y = (∑ i, p i) * Y * (∑ j, p j)` using `by rw [hp.1.complete, one_mul, mul_one]`. Use `conv_lhs => rw [h]`. Rewrite using `[Finset.sum_mul, Finset.sum_mul]`. Simplify using `only [Finset.mul_sum]`.
-/
theorem expand (hp : Sys p) (Y : Mat C N) : Y = ∑ i, ∑ j, p i * Y * p j := by
  have h : Y = (∑ i, p i) * Y * (∑ j, p j) := by rw [hp.1.complete, one_mul, mul_one]
  conv_lhs => rw [h]
  rw [Finset.sum_mul, Finset.sum_mul]
  simp only [Finset.mul_sum]

def S (p : Fin n → Mat C N) (g : Submodule C (Mat C N)) : Set (Mat C N) :=
  {a | (∀ i j, i ≠ j → p i * a * p j ∈ g) ∧ ∀ i, ∃ c : C, p i * a * p i = c • p i}

variable {g : Submodule C (Mat C N)}

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[mul_add, add_mul]`. Conclude with `g.add_mem (ha.1 i j h) (hb.1 i j h)`. Take `⟨c, hc⟩` from `ha.2 i`. Take `⟨c', hc'⟩` from `hb.2 i`.

Conclude with `⟨c + c', by rw [mul_add, add_mul, hc, hc', add_smul]⟩`.
-/
theorem S_add {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a + b ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ?_⟩
  · rw [mul_add, add_mul]; exact g.add_mem (ha.1 i j h) (hb.1 i j h)
  · obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
    exact ⟨c + c', by rw [mul_add, add_mul, hc, hc', add_smul]⟩

/- English proof (translation)
Use `⟨fun i j h => ?_, fun i => ⟨r, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pq hp h, smul_zero]`. Conclude with `g.zero_mem`. Rewrite using `[Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pp hp]`.
-/
theorem S_alg (hp : Sys p) (r : C) : algebraMap C (Mat C N) r ∈ S p g := by
  refine ⟨fun i j h => ?_, fun i => ⟨r, ?_⟩⟩
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pq hp h, smul_zero]
    exact g.zero_mem
  · rw [Algebra.algebraMap_eq_smul_one, mul_smul_comm, mul_one, smul_mul_assoc, pp hp]

/- English proof (translation)
Use `⟨fun i k hik => ?_, fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[decomp hp]`. Use `g.sum_mem fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hji : j = i`. Rewrite using `[hji]`.

Take `⟨c, hc⟩` from `ha.2 i`. Establish `e : p i * (p i * b * p k) = p i * b * p k` using `by simp only [mul_assoc, pp' hp]`. Rewrite using `[hc, smul_mul_assoc, e]`. Conclude with `g.smul_mem _ (hb.1 _ _ hik)`. Distinguish the cases in `hjk : j = k`.

Rewrite using `[hjk]`. Take `⟨c, hc⟩` from `hb.2 k`. Establish `e : p i * a * p k * p k = p i * a * p k` using `by simp only [mul_assoc, pp hp]`. Rewrite using `[hc, mul_smul_comm, e]`. Conclude with `g.smul_mem _ (ha.1 _ _ hik)`.

Establish `h` using `hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j k hjk)`. Establish `z : p j * b * p k * (p i * a * p j) = 0`. Simplify using `only [mul_assoc, pq' hp (Ne.symm hik), mul_zero]`. Rewrite `h` using `[z, sub_zero]`. Then use the resulting hypothesis. Establish `key : ∀ j, ∃ c : C, p i * a * p j * (p j * b * p i) = c • p i`.

Introduce `j`. Distinguish the cases in `hji : j = i`. Rewrite using `[hji]`. Take `⟨c, hc⟩` from `ha.2 i`. Take `⟨c', hc'⟩` from `hb.2 i`.

Conclude with `⟨c * c', by rw [hc, hc', smul_mul_assoc, mul_smul_comm, pp hp, smul_smul]⟩`. Establish `hZ` using `hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j i hji)`. Establish `e1 : p i * a * p j * (p j * b * p i) = p i * (a * p j * (p j * b)) * p i`. Simplify using `only [mul_assoc]`. Establish `e2 : p j * b * p i * (p i * a * p j) = p j * (b * p i * (p i * a)) * p j`.

Simplify using `only [mul_assoc]`. Rewrite `hZ` using `[e1, e2]`. Establish `hc : ∀ m, (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) * p m = p m * (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j)`. Introduce `m`. Rewrite using `[sub_mul, mul_sub, corner_comm hp, corner_comm hp]`.

Take `⟨c, hcZ⟩` from `hdiag _ hZ hc i`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[e1, ← hcZ, sub_mul]`. Establish `f1 : p i * (a * p j * (p j * b)) * p i * p i = p i * (a * p j * (p j * b)) * p i`. Simplify using `only [mul_assoc, pp hp]`.

Establish `f2 : p j * (b * p i * (p i * a)) * p j * p i = 0`. Simplify using `only [mul_assoc, pq hp hji, mul_zero]`. Rewrite using `[f1, f2, sub_zero]`. Use `choose f hf using key`. Conclude with `⟨∑ j, f j, by rw [decomp hp, Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => hf j⟩`.
-/
theorem S_mul (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {a b : Mat C N} (ha : a ∈ S p g) (hb : b ∈ S p g) : a * b ∈ S p g := by
  refine ⟨fun i k hik => ?_, fun i => ?_⟩
  · rw [decomp hp]
    refine g.sum_mem fun j _ => ?_
    by_cases hji : j = i
    · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i
      have e : p i * (p i * b * p k) = p i * b * p k := by simp only [mul_assoc, pp' hp]
      rw [hc, smul_mul_assoc, e]; exact g.smul_mem _ (hb.1 _ _ hik)
    by_cases hjk : j = k
    · rw [hjk]; obtain ⟨c, hc⟩ := hb.2 k
      have e : p i * a * p k * p k = p i * a * p k := by simp only [mul_assoc, pp hp]
      rw [hc, mul_smul_comm, e]; exact g.smul_mem _ (ha.1 _ _ hik)
    have h := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j k hjk)
    have z : p j * b * p k * (p i * a * p j) = 0 := by
      simp only [mul_assoc, pq' hp (Ne.symm hik), mul_zero]
    rwa [z, sub_zero] at h
  · have key : ∀ j, ∃ c : C, p i * a * p j * (p j * b * p i) = c • p i := by
      intro j
      by_cases hji : j = i
      · rw [hji]; obtain ⟨c, hc⟩ := ha.2 i; obtain ⟨c', hc'⟩ := hb.2 i
        exact ⟨c * c', by rw [hc, hc', smul_mul_assoc, mul_smul_comm, pp hp, smul_smul]⟩
      have hZ := hbr _ (ha.1 i j (Ne.symm hji)) _ (hb.1 j i hji)
      have e1 : p i * a * p j * (p j * b * p i) = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc]
      have e2 : p j * b * p i * (p i * a * p j) = p j * (b * p i * (p i * a)) * p j := by
        simp only [mul_assoc]
      rw [e1, e2] at hZ
      have hc : ∀ m, (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) * p m =
          p m * (p i * (a * p j * (p j * b)) * p i - p j * (b * p i * (p i * a)) * p j) := by
        intro m; rw [sub_mul, mul_sub, corner_comm hp, corner_comm hp]
      obtain ⟨c, hcZ⟩ := hdiag _ hZ hc i
      refine ⟨c, ?_⟩
      rw [e1, ← hcZ, sub_mul]
      have f1 : p i * (a * p j * (p j * b)) * p i * p i = p i * (a * p j * (p j * b)) * p i := by
        simp only [mul_assoc, pp hp]
      have f2 : p j * (b * p i * (p i * a)) * p j * p i = 0 := by
        simp only [mul_assoc, pq hp hji, mul_zero]
      rw [f1, f2, sub_zero]
    choose f hf using key
    exact ⟨∑ j, f j, by rw [decomp hp, Finset.sum_smul]; exact Finset.sum_congr rfl fun j _ => hf j⟩

/- English proof (translation)
Use `⟨hoff Y hY, fun i => ?_⟩` and prove the remaining obligations. Use `set D := ∑ k, p k * Y * p k with hDdef`. Establish `hsplit : Y = D + ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j` using `by conv_lhs => rw [expand hp Y]`. Rewrite using `[hDdef, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm`.

Establish `hD : D ∈ g`. Establish `: D = Y - ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j`. Rewrite using `[eq_sub_iff_add_eq, ← hsplit]`. Rewrite using `[this]`. Use `g.sub_mem hY (g.sum_mem fun k _ => g.sum_mem fun j hj => hoff Y hY k j ?_)` and prove the remaining obligations.

Conclude with `Ne.symm (Finset.ne_of_mem_erase hj)`. Establish `hcomm : ∀ m, D * p m = p m * D`. Introduce `m`. Rewrite using `[hDdef, Finset.sum_mul, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun k _ => corner_comm hp Y k m`.

Take `⟨c, hc⟩` from `hdiag D hD hcomm i`. Use `⟨c, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, hDdef, Finset.sum_mul, Finset.sum_eq_single i]`. Simplify using `only [mul_assoc, pp hp]`. Introduce `k _ hki`.

Simplify using `only [mul_assoc, pq hp hki, mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem S_of_mem (hp : Sys p) (hoff : ∀ Y ∈ g, ∀ i j, i ≠ j → p i * Y * p j ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i)
    {Y : Mat C N} (hY : Y ∈ g) : Y ∈ S p g := by
  refine ⟨hoff Y hY, fun i => ?_⟩
  set D := ∑ k, p k * Y * p k with hDdef
  have hsplit : Y = D + ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
    conv_lhs => rw [expand hp Y]
    rw [hDdef, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => (Finset.add_sum_erase _ _ (Finset.mem_univ k)).symm
  have hD : D ∈ g := by
    have : D = Y - ∑ k, ∑ j ∈ Finset.univ.erase k, p k * Y * p j := by
      rw [eq_sub_iff_add_eq, ← hsplit]
    rw [this]
    refine g.sub_mem hY (g.sum_mem fun k _ => g.sum_mem fun j hj => hoff Y hY k j ?_)
    exact Ne.symm (Finset.ne_of_mem_erase hj)
  have hcomm : ∀ m, D * p m = p m * D := by
    intro m; rw [hDdef, Finset.sum_mul, Finset.mul_sum]
    exact Finset.sum_congr rfl fun k _ => corner_comm hp Y k m
  obtain ⟨c, hc⟩ := hdiag D hD hcomm i
  refine ⟨c, ?_⟩
  rw [← hc, hDdef, Finset.sum_mul, Finset.sum_eq_single i]
  · simp only [mul_assoc, pp hp]
  · intro k _ hki; simp only [mul_assoc, pq hp hki, mul_zero]
  · intro h; exact absurd (Finset.mem_univ i) h

def Sa (hp : Sys p) (hbr : ∀ Y ∈ g, ∀ Z ∈ g, Y * Z - Z * Y ∈ g)
    (hdiag : ∀ Y ∈ g, (∀ i, Y * p i = p i * Y) → ∀ i, ∃ c : C, Y * p i = c • p i) :
    Subalgebra C (Mat C N) where
  carrier := S p g
  mul_mem' := S_mul hp hbr hdiag
  add_mem' := S_add
  algebraMap_mem' := S_alg hp

/- English proof (translation)
Introduce `C _ N n p g hp hbr hoff hdiag a ha`. Establish `hle : Algebra.adjoin C (g : Set (Mat C N)) ≤ Sa hp hbr hdiag` using `Algebra.adjoin_le fun Y hY => S_of_mem hp hoff hdiag hY`. Conclude with `hle ha`.
-/
theorem AlgStruct_of : AlgStruct := by
  intro C _ N n p g hp hbr hoff hdiag a ha
  have hle : Algebra.adjoin C (g : Set (Mat C N)) ≤ Sa hp hbr hdiag :=
    Algebra.adjoin_le fun Y hY => S_of_mem hp hoff hdiag hY
  exact hle ha

end AlgStruct₂
end LateralTheory.DivDb
