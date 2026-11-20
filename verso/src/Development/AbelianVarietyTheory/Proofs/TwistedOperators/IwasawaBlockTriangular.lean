import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.SimpleSum
import Formalism.LocalToGlobal.ProjectiveLattices.ExistsOfValILeOne

open MeasureTheory ValuativeRel Matrix GlobalTheory.SplitWeil GlobalTheory.RootEx

namespace GlobalTheory.SplitWeil

/- English proof (translation)
Take `⟨x, rfl⟩` from `hg`. Use `⟨(x.val i j).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `((x⁻¹).val i j).2`.
-/
private theorem entries_mem_integer_of_mem_KO {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] {g : GL ι k} (hg : g ∈ KO k ι) (i j : ι) :
    g.val i j ∈ 𝒪[k] ∧ (g⁻¹).val i j ∈ 𝒪[k] := by
  obtain ⟨x, rfl⟩ := hg
  refine ⟨(x.val i j).2, ?_⟩
  rw [← map_inv]
  exact ((x⁻¹).val i j).2

/- English proof (translation)
Set `M' : Matrix ι ι 𝒪[k]` to `Matrix.of fun i j => ⟨M i j, hM i j⟩`. Set `N' : Matrix ι ι 𝒪[k]` to `Matrix.of fun i j => ⟨N i j, hN i j⟩`. Establish `e1 : (algebraMap 𝒪[k] k).mapMatrix M' = M` using `by ext i j; rfl`. Establish `e2 : (algebraMap 𝒪[k] k).mapMatrix N' = N` using `by ext i j; rfl`. Establish `inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix ι ι 𝒪[k] →+* Matrix ι ι k)` using `Matrix.map_injective Subtype.val_injective`.

Establish `h1 : M' * N' = 1` using `inj (by rw [map_mul, map_one, e1, e2, hMN])`. Establish `h2 : N' * M' = 1` using `inj (by rw [map_mul, map_one, e1, e2, hNM])`. Set `x : GL ι 𝒪[k]` to `⟨M', N', h1, h2⟩`. Use `⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x, ⟨x, rfl⟩, e1, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_inv]`.

Conclude with `e2`.
-/
private theorem exists_mem_KO_of_integral_inverse_pair {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (M N : Matrix ι ι k) (hM : ∀ i j, M i j ∈ 𝒪[k])
    (hN : ∀ i j, N i j ∈ 𝒪[k]) (hMN : M * N = 1) (hNM : N * M = 1) :
    ∃ g : GL ι k, g ∈ KO k ι ∧ g.val = M ∧ (g⁻¹).val = N := by
  let M' : Matrix ι ι 𝒪[k] := Matrix.of fun i j => ⟨M i j, hM i j⟩
  let N' : Matrix ι ι 𝒪[k] := Matrix.of fun i j => ⟨N i j, hN i j⟩
  have e1 : (algebraMap 𝒪[k] k).mapMatrix M' = M := by ext i j; rfl
  have e2 : (algebraMap 𝒪[k] k).mapMatrix N' = N := by ext i j; rfl
  have inj : Function.Injective ((algebraMap 𝒪[k] k).mapMatrix : Matrix ι ι 𝒪[k] →+* Matrix ι ι k) :=
    Matrix.map_injective Subtype.val_injective
  have h1 : M' * N' = 1 := inj (by rw [map_mul, map_one, e1, e2, hMN])
  have h2 : N' * M' = 1 := inj (by rw [map_mul, map_one, e1, e2, hNM])
  let x : GL ι 𝒪[k] := ⟨M', N', h1, h2⟩
  refine ⟨Matrix.GeneralLinearGroup.map (algebraMap 𝒪[k] k) x, ⟨x, rfl⟩, e1, ?_⟩
  rw [← map_inv]
  exact e2

/- English proof (translation)
Establish `hone : ∀ i j, (1 : Matrix ι ι k) i j ∈ 𝒪[k]`. Introduce `i j`. Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _]`.

Establish `e1 : (1 + N) * (1 - N) = 1 - N * N` using `by noncomm_ring`. Establish `e2 : (1 - N) * (1 + N) = 1 - N * N` using `by noncomm_ring`. Take `⟨g, hg, hv, -⟩` from `exists_mem_KO_of_integral_inverse_pair (1 + N) (1 - N) (fun i j => add_mem (hone i j) (hN i j)) (fun i j => sub_mem (hone i j) (hN i j)) (by rw [e1, hNN, sub_zero]) (by rw [e2, hNN, sub_zero])`. Conclude with `⟨g, hg, hv⟩`.
-/
private theorem exists_mem_KO_eq_one_add_of_sq_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι k) (hN : ∀ i j, N i j ∈ 𝒪[k]) (hNN : N * N = 0) :
    ∃ g ∈ KO k ι, g.val = 1 + N := by
  have hone : ∀ i j, (1 : Matrix ι ι k) i j ∈ 𝒪[k] := by
    intro i j
    rw [Matrix.one_apply]
    split_ifs
    exacts [one_mem _, zero_mem _]
  have e1 : (1 + N) * (1 - N) = 1 - N * N := by noncomm_ring
  have e2 : (1 - N) * (1 + N) = 1 - N * N := by noncomm_ring
  obtain ⟨g, hg, hv, -⟩ := exists_mem_KO_of_integral_inverse_pair (1 + N) (1 - N) (fun i j => add_mem (hone i j) (hN i j))
    (fun i j => sub_mem (hone i j) (hN i j)) (by rw [e1, hNN, sub_zero]) (by rw [e2, hNN, sub_zero])
  exact ⟨g, hg, hv⟩

/- English proof (translation)
Establish `hrow : ∃ j, g.val i0 j ≠ 0`. Assume the negation of the conclusion as `hcon`. Simplify using `only [not_exists, not_not] at hcon`. Establish `h1` using `congrFun (congrFun (Units.mul_inv g) i0) i0`. Simplify using `[Matrix.mul_apply, hcon] at h1`.

Establish `: Nonempty ι` using `⟨i0⟩`. Take `⟨j0, hj0⟩` from `Finite.exists_max (fun j => valuation k (g.val i0 j))`. Establish `hj0ne : g.val i0 j0 ≠ 0`. Take `⟨j, hj⟩` from `hrow`. Introduce `hz`.

Establish `h` using `hj0 j`. Simplify using `only [hz, map_zero] at h`. Conclude with `hj ((Valuation.zero_iff _).mp (le_antisymm h zero_le))`. Distinguish the cases in `hcase : valuation k (g.val i0 j0) ≤ valuation k (g.val i0 i0)`. Use `⟨1, one_mem _, ?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [mul_one]`. Introduce `hz`. Rewrite `hcase` using `[hz, map_zero]`. Conclude with `hj0ne ((Valuation.zero_iff _).mp (le_antisymm hcase zero_le))`. Introduce `j`.

Simplify using `only [mul_one]`. Conclude with `(hj0 j).trans hcase`. Use `replace hcase := not_le.mp hcase`. Establish `hne : j0 ≠ i0`. Introduce and unpack `rfl`.

Conclude with `lt_irrefl _ hcase`. Take `⟨u, hu, hval⟩` from `exists_mem_KO_eq_one_add_of_sq_eq_zero (Matrix.of fun l j => if l = j0 ∧ j = i0 then (1 : k) else 0) (by`. Introduce `l j`. Simplify using `only [Matrix.of_apply]`. Use `split_ifs`.

Use `exacts [one_mem _, zero_mem _])`. Use the proof step `(by`. Use extensionality with `l j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `m _`. Distinguish the cases in `hm : m = i0`. Establish `: ¬ (m = j0 ∧ j = i0)` using `fun h => hne (h.1.symm.trans hm)`. Simplify using `[this]`. Simplify using `[hm])`.

Use `⟨u, hu, ?_⟩` and prove the remaining obligations. Establish `key : ∀ j, (g * u).val i0 j = g.val i0 j + if j = i0 then g.val i0 j0 else 0`. Introduce `j`. Rewrite using `[Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply]`. Use `congr 1`.

Distinguish the cases in `hj : j = i0`. Simplify using `[Matrix.mul_apply, hj]`. Simplify using `[Matrix.mul_apply, hj]`. Establish `hsum : valuation k ((g * u).val i0 i0) = valuation k (g.val i0 j0)`. Rewrite using `[key, if_pos rfl]`.

Conclude with `(valuation k).map_add_eq_of_lt_right hcase`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `hz`. Rewrite `hsum` using `[hz, map_zero]`. Conclude with `hj0ne ((Valuation.zero_iff _).mp hsum.symm)`.

Introduce `j`. Rewrite using `[hsum]`. Distinguish the cases in `hj : j = i0`. Rewrite using `[hj, hsum]`. Rewrite using `[key, if_neg hj, add_zero]`.

Conclude with `hj0 j`.
-/
private theorem exists_mem_KO_pivot_ne_zero_valuation_max {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (i0 : ι) :
    ∃ u ∈ KO k ι, (g * u).val i0 i0 ≠ 0 ∧
      ∀ j, valuation k ((g * u).val i0 j) ≤ valuation k ((g * u).val i0 i0) := by
  have hrow : ∃ j, g.val i0 j ≠ 0 := by
    by_contra hcon
    simp only [not_exists, not_not] at hcon
    have h1 := congrFun (congrFun (Units.mul_inv g) i0) i0
    simp [Matrix.mul_apply, hcon] at h1
  have : Nonempty ι := ⟨i0⟩
  obtain ⟨j0, hj0⟩ := Finite.exists_max (fun j => valuation k (g.val i0 j))
  have hj0ne : g.val i0 j0 ≠ 0 := by
    obtain ⟨j, hj⟩ := hrow
    intro hz
    have h := hj0 j
    simp only [hz, map_zero] at h
    exact hj ((Valuation.zero_iff _).mp (le_antisymm h zero_le))
  by_cases hcase : valuation k (g.val i0 j0) ≤ valuation k (g.val i0 i0)
  · refine ⟨1, one_mem _, ?_, ?_⟩
    · simp only [mul_one]
      intro hz
      rw [hz, map_zero] at hcase
      exact hj0ne ((Valuation.zero_iff _).mp (le_antisymm hcase zero_le))
    · intro j
      simp only [mul_one]
      exact (hj0 j).trans hcase
  · replace hcase := not_le.mp hcase
    have hne : j0 ≠ i0 := by
      rintro rfl
      exact lt_irrefl _ hcase
    obtain ⟨u, hu, hval⟩ := exists_mem_KO_eq_one_add_of_sq_eq_zero (Matrix.of fun l j => if l = j0 ∧ j = i0 then (1 : k) else 0)
      (by
        intro l j
        simp only [Matrix.of_apply]
        split_ifs
        exacts [one_mem _, zero_mem _])
      (by
        ext l j
        simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
        apply Finset.sum_eq_zero
        intro m _
        by_cases hm : m = i0
        · have : ¬ (m = j0 ∧ j = i0) := fun h => hne (h.1.symm.trans hm)
          simp [this]
        · simp [hm])
    refine ⟨u, hu, ?_⟩
    have key : ∀ j, (g * u).val i0 j = g.val i0 j + if j = i0 then g.val i0 j0 else 0 := by
      intro j
      rw [Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply]
      congr 1
      by_cases hj : j = i0
      · simp [Matrix.mul_apply, hj]
      · simp [Matrix.mul_apply, hj]
    have hsum : valuation k ((g * u).val i0 i0) = valuation k (g.val i0 j0) := by
      rw [key, if_pos rfl]
      exact (valuation k).map_add_eq_of_lt_right hcase
    refine ⟨?_, ?_⟩
    · intro hz
      rw [hz, map_zero] at hsum
      exact hj0ne ((Valuation.zero_iff _).mp hsum.symm)
    · intro j
      rw [hsum]
      by_cases hj : j = i0
      · rw [hj, hsum]
      · rw [key, if_neg hj, add_zero]
        exact hj0 j

/- English proof (translation)
Take `⟨u, hu, hval⟩` from `exists_mem_KO_eq_one_add_of_sq_eq_zero (Matrix.of fun l j => if l = i0 ∧ j ≠ i0 then -(g.val i0 j / g.val i0 i0) else 0) (by`. Introduce `l j`. Simplify using `only [Matrix.of_apply]`. Use `split_ifs`. Rewrite using `[Valuation.mem_integer_iff, Valuation.map_neg, Valuation.map_div]`.

Establish `hpos : 0 < valuation k (g.val i0 i0)`. Rewrite using `[zero_lt_iff]`. Conclude with `(Valuation.ne_zero_iff _).mpr hc`. Conclude with `div_le_one_of_le₀ (hle j) zero_le`. Conclude with `zero_mem _)`.

Use the proof step `(by`. Use extensionality with `l j`. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `m _`.

Distinguish the cases in `hm : m = i0`. Simplify using `[hm]`. Simplify using `[hm])`. Use `⟨u, hu, fun j hj => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]`.

Establish `hx : ∀ x, (x = i0 ∧ j ≠ i0) ↔ x = i0` using `fun x => ⟨And.left, fun h => ⟨h, hj⟩⟩`. Simplify using `only [Matrix.of_apply, hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem exists_mem_KO_row_eq_zero_of_pivot_max {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (g : GL ι k) (i0 : ι) (hc : g.val i0 i0 ≠ 0)
    (hle : ∀ j, valuation k (g.val i0 j) ≤ valuation k (g.val i0 i0)) :
    ∃ u ∈ KO k ι, ∀ j, j ≠ i0 → (g * u).val i0 j = 0 := by
  obtain ⟨u, hu, hval⟩ := exists_mem_KO_eq_one_add_of_sq_eq_zero
    (Matrix.of fun l j => if l = i0 ∧ j ≠ i0 then -(g.val i0 j / g.val i0 i0) else 0)
    (by
      intro l j
      simp only [Matrix.of_apply]
      split_ifs
      · rw [Valuation.mem_integer_iff, Valuation.map_neg, Valuation.map_div]
        have hpos : 0 < valuation k (g.val i0 i0) := by
          rw [zero_lt_iff]
          exact (Valuation.ne_zero_iff _).mpr hc
        exact div_le_one_of_le₀ (hle j) zero_le
      · exact zero_mem _)
    (by
      ext l j
      simp only [Matrix.mul_apply, Matrix.of_apply, Matrix.zero_apply]
      apply Finset.sum_eq_zero
      intro m _
      by_cases hm : m = i0
      · simp [hm]
      · simp [hm])
  refine ⟨u, hu, fun j hj => ?_⟩
  rw [Units.val_mul, hval, mul_add, mul_one, Matrix.add_apply, Matrix.mul_apply]
  have hx : ∀ x, (x = i0 ∧ j ≠ i0) ↔ x = i0 := fun x => ⟨And.left, fun h => ⟨h, hj⟩⟩
  simp only [Matrix.of_apply, hx, mul_ite, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  field_simp
  ring

/- English proof (translation)
Establish `key : ∀ j, m.val i0 i0 * (m⁻¹).val i0 j = (1 : Matrix ι ι k) i0 j`. Introduce `j`. Establish `h` using `congrFun (congrFun (Units.mul_inv m) i0) j`. Rewrite `h` using `[Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, Finset.sum_eq_zero (fun l _ => by rw [hrow _ l.2, zero_mul]), add_zero]`. Conclude with `h`.

Establish `hc : m.val i0 i0 ≠ 0`. Introduce `hz`. Establish `h` using `key i0`. Rewrite `h` using `[hz, zero_mul, Matrix.one_apply_eq]`. Conclude with `zero_ne_one h`.

Establish `hinv : ∀ j, j ≠ i0 → (m⁻¹).val i0 j = 0`. Introduce `j hj`. Establish `h` using `key j`. Rewrite `h` using `[Matrix.one_apply_ne (Ne.symm hj)]`. Conclude with `(mul_eq_zero.mp h).resolve_left hc`.

Use `⟨⟨Matrix.of fun i j => m.val i j, Matrix.of fun i j => (m⁻¹).val i j, ?_, ?_⟩, fun i j => rfl⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `h` using `congrFun (congrFun (Units.mul_inv m) i) j`. Rewrite `h` using `[Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hinv _ j.2, mul_zero, zero_add]`. Rewrite using `[Matrix.mul_apply]`.

Simplify using `only [Matrix.of_apply]`. Rewrite using `[h]`. Distinguish the cases in `hij : i = j`. Rewrite using `[hij, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]`.

Use extensionality with `i j`. Establish `h` using `congrFun (congrFun (Units.inv_mul m) i) j`. Rewrite `h` using `[Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hrow _ j.2, mul_zero, zero_add]`. Rewrite using `[Matrix.mul_apply]`. Simplify using `only [Matrix.of_apply]`.

Rewrite using `[h]`. Distinguish the cases in `hij : i = j`. Rewrite using `[hij, Matrix.one_apply_eq, Matrix.one_apply_eq]`. Rewrite using `[Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]`.
-/
private theorem exists_GL_compl_eq_of_row_eq_zero {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (m : GL ι k) (i0 : ι) (hrow : ∀ j, j ≠ i0 → m.val i0 j = 0) :
    ∃ A : GL {i // i ≠ i0} k, ∀ i j : {i // i ≠ i0}, A.val i j = m.val i j := by
  have key : ∀ j, m.val i0 i0 * (m⁻¹).val i0 j = (1 : Matrix ι ι k) i0 j := by
    intro j
    have h := congrFun (congrFun (Units.mul_inv m) i0) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0,
      Finset.sum_eq_zero (fun l _ => by rw [hrow _ l.2, zero_mul]), add_zero] at h
    exact h
  have hc : m.val i0 i0 ≠ 0 := by
    intro hz
    have h := key i0
    rw [hz, zero_mul, Matrix.one_apply_eq] at h
    exact zero_ne_one h
  have hinv : ∀ j, j ≠ i0 → (m⁻¹).val i0 j = 0 := by
    intro j hj
    have h := key j
    rw [Matrix.one_apply_ne (Ne.symm hj)] at h
    exact (mul_eq_zero.mp h).resolve_left hc
  refine ⟨⟨Matrix.of fun i j => m.val i j, Matrix.of fun i j => (m⁻¹).val i j, ?_, ?_⟩, fun i j => rfl⟩
  · ext i j
    have h := congrFun (congrFun (Units.mul_inv m) i) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hinv _ j.2, mul_zero, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]
  · ext i j
    have h := congrFun (congrFun (Units.inv_mul m) i) j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hrow _ j.2, mul_zero, zero_add] at h
    rw [Matrix.mul_apply]
    simp only [Matrix.of_apply]
    rw [h]
    by_cases hij : i = j
    · rw [hij, Matrix.one_apply_eq, Matrix.one_apply_eq]
    · rw [Matrix.one_apply_ne hij, Matrix.one_apply_ne (fun h => hij (Subtype.ext h))]

/- English proof (translation)
Set `E : Matrix {i // i ≠ i0} {i // i ≠ i0} k → Matrix ι ι k` to `fun X => Matrix.of fun i j => if hi : i = i0 then (if j = i0 then 1 else 0) else if hj : j = i0 then 0 else X ⟨i, hi⟩ ⟨j, hj⟩`. Establish `hl : ∀ l : {i // i ≠ i0}, ((l : ι) = i0) ↔ False` using `fun l => iff_false_intro l.2`. Establish `hE : ∀ X Y, E X * E Y = E (X * Y)`. Introduce `X Y`. Use extensionality with `i j`.

Rewrite using `[Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0]`. Apply the tactic sequence `by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [E, hi, hj, hl, Matrix.mul_apply]`. Establish `hE1 : E 1 = 1`. Use extensionality with `i j`. Distinguish the cases in `hi : i = i0`.

Rewrite using `[hi]`. Distinguish the cases in `hj : j = i0`. Rewrite using `[hj]`. Simplify using `[E]`. Simplify using `[E, hj, Matrix.one_apply_ne (Ne.symm hj)]`.

Distinguish the cases in `hj : j = i0`. Simplify using `[E, hi, hj]`. Simplify using `[E, hi, hj, Matrix.one_apply]`. Establish `hint : ∀ X : Matrix {i // i ≠ i0} {i // i ≠ i0} k, (∀ i j, X i j ∈ 𝒪[k]) → ∀ i j, E X i j ∈ 𝒪[k]`. Introduce `X hX i j`.

Simplify using `only [E, Matrix.of_apply]`. Use `split_ifs`. Use `exacts [one_mem _, zero_mem _, zero_mem _, hX _ _]`. Take `⟨V, hV, hv, -⟩` from `exists_mem_KO_of_integral_inverse_pair (E g.val) (E (g⁻¹).val) (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).1) (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).2) (by rw [hE, Units.mul_inv, hE1]) (by rw [hE, Units.inv_mul, hE1])`. Use `⟨V, hV, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `j`. Rewrite using `[hv]`. Simplify using `[E]`. Introduce `i hi`. Rewrite using `[hv]`.

Simplify using `[E, hi]`. Introduce `i j`. Rewrite using `[hv]`. Simplify using `[E, i.2, j.2]`.
-/
private theorem exists_mem_KO_extend_of_mem_KO_compl {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {ι : Type} [Fintype ι] [DecidableEq ι] (i0 : ι) (g : GL {i // i ≠ i0} k) (hg : g ∈ KO k {i // i ≠ i0}) :
    ∃ V ∈ KO k ι, (∀ j, V.val i0 j = if j = i0 then 1 else 0) ∧ (∀ i, i ≠ i0 → V.val i i0 = 0) ∧
      ∀ i j : {i // i ≠ i0}, V.val i j = g.val i j := by
  let E : Matrix {i // i ≠ i0} {i // i ≠ i0} k → Matrix ι ι k := fun X => Matrix.of fun i j =>
    if hi : i = i0 then (if j = i0 then 1 else 0) else if hj : j = i0 then 0 else X ⟨i, hi⟩ ⟨j, hj⟩
  have hl : ∀ l : {i // i ≠ i0}, ((l : ι) = i0) ↔ False := fun l => iff_false_intro l.2
  have hE : ∀ X Y, E X * E Y = E (X * Y) := by
    intro X Y
    ext i j
    rw [Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0]
    by_cases hi : i = i0 <;> by_cases hj : j = i0 <;> simp [E, hi, hj, hl, Matrix.mul_apply]
  have hE1 : E 1 = 1 := by
    ext i j
    by_cases hi : i = i0
    · rw [hi]
      by_cases hj : j = i0
      · rw [hj]
        simp [E]
      · simp [E, hj, Matrix.one_apply_ne (Ne.symm hj)]
    · by_cases hj : j = i0
      · simp [E, hi, hj]
      · simp [E, hi, hj, Matrix.one_apply]
  have hint : ∀ X : Matrix {i // i ≠ i0} {i // i ≠ i0} k, (∀ i j, X i j ∈ 𝒪[k]) → ∀ i j, E X i j ∈ 𝒪[k] := by
    intro X hX i j
    simp only [E, Matrix.of_apply]
    split_ifs
    exacts [one_mem _, zero_mem _, zero_mem _, hX _ _]
  obtain ⟨V, hV, hv, -⟩ := exists_mem_KO_of_integral_inverse_pair (E g.val) (E (g⁻¹).val)
    (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).1) (hint _ fun i j => (entries_mem_integer_of_mem_KO hg i j).2)
    (by rw [hE, Units.mul_inv, hE1]) (by rw [hE, Units.inv_mul, hE1])
  refine ⟨V, hV, ?_, ?_, ?_⟩
  · intro j
    rw [hv]
    simp [E]
  · intro i hi
    rw [hv]
    simp [E, hi]
  · intro i j
    rw [hv]
    simp [E, i.2, j.2]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `ι _ _ hn lv h`. Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Use `⟨h, ?_, 1, one_mem _, (mul_one h).symm⟩` and prove the remaining obligations.

Introduce `i`. Conclude with `isEmptyElim i`. Take `⟨i0, hi0⟩` from `Finite.exists_max lv`. Take `⟨u1, hu1, hc, hle⟩` from `exists_mem_KO_pivot_ne_zero_valuation_max h i0`. Take `⟨u2, hu2, hrow⟩` from `exists_mem_KO_row_eq_zero_of_pivot_max (h * u1) i0 hc hle`.

Take `⟨A, hA⟩` from `exists_GL_compl_eq_of_row_eq_zero (h * u1 * u2) i0 hrow`. Establish `hcard : Fintype.card {i // i ≠ i0} < n`. Rewrite using `[← hn]`. Conclude with `Fintype.card_subtype_lt (p := fun i => i ≠ i0) (x := i0) (fun h => h rfl)`. Take `⟨b', hb', w', hw', hAw⟩` from `ih _ hcard {i // i ≠ i0} rfl (fun i => lv i) A`.

Take `⟨V, hV, hV1, -, hV3⟩` from `exists_mem_KO_extend_of_mem_KO_compl i0 w'⁻¹ (inv_mem hw')`. Use `⟨h * u1 * u2 * V, ?_, V⁻¹ * (u1 * u2)⁻¹, mul_mem (inv_mem hV) (inv_mem (mul_mem hu1 hu2)), by group⟩` and prove the remaining obligations. Introduce `i j hij`. Establish `hj : j ≠ i0`. Introduce and unpack `rfl`.

Conclude with `absurd (hi0 i) (not_le.mpr hij)`. Rewrite using `[Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hV1 j, if_neg hj, mul_zero, zero_add]`. Distinguish the cases in `hi : i = i0`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `l _`.

Rewrite using `[hi, hrow _ l.2, zero_mul]`. Establish `hb : b'.val ⟨i, hi⟩ ⟨j, hj⟩ = 0` using `hb' hij`. Establish `hbA : b' = A * w'⁻¹` using `by rw [hAw, mul_inv_cancel_right]`. Establish `e : ∑ l : {i // i ≠ i0}, (h * u1 * u2).val i l * V.val l j = (A * w'⁻¹).val ⟨i, hi⟩ ⟨j, hj⟩`. Rewrite using `[show (A * w'⁻¹).val = A.val * (w'⁻¹).val from Units.val_mul _ _, Matrix.mul_apply]`.

Use `Finset.sum_congr rfl (fun l _ => ?_)` and prove the remaining obligations. Rewrite using `[hA, ← hV3]`. Rewrite using `[e, ← hbA]`. Conclude with `hb`.
-/
private theorem exists_blockTriangular_mul_mem_KO_eq {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (n : ℕ) :
    ∀ (ι : Type) [Fintype ι] [DecidableEq ι], Fintype.card ι = n → ∀ (lv : ι → ℕ) (h : GL ι k),
      ∃ (b : GL ι k), b.val.BlockTriangular lv ∧ ∃ w ∈ KO k ι, h = b * w := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro ι _ _ hn lv h
  rcases isEmpty_or_nonempty ι with hι | hι
  · refine ⟨h, ?_, 1, one_mem _, (mul_one h).symm⟩
    intro i
    exact isEmptyElim i
  · obtain ⟨i0, hi0⟩ := Finite.exists_max lv
    obtain ⟨u1, hu1, hc, hle⟩ := exists_mem_KO_pivot_ne_zero_valuation_max h i0
    obtain ⟨u2, hu2, hrow⟩ := exists_mem_KO_row_eq_zero_of_pivot_max (h * u1) i0 hc hle
    obtain ⟨A, hA⟩ := exists_GL_compl_eq_of_row_eq_zero (h * u1 * u2) i0 hrow
    have hcard : Fintype.card {i // i ≠ i0} < n := by
      rw [← hn]
      exact Fintype.card_subtype_lt (p := fun i => i ≠ i0) (x := i0) (fun h => h rfl)
    obtain ⟨b', hb', w', hw', hAw⟩ := ih _ hcard {i // i ≠ i0} rfl (fun i => lv i) A
    obtain ⟨V, hV, hV1, -, hV3⟩ := exists_mem_KO_extend_of_mem_KO_compl i0 w'⁻¹ (inv_mem hw')
    refine ⟨h * u1 * u2 * V, ?_, V⁻¹ * (u1 * u2)⁻¹, mul_mem (inv_mem hV) (inv_mem (mul_mem hu1 hu2)), by group⟩
    intro i j hij
    have hj : j ≠ i0 := by
      rintro rfl
      exact absurd (hi0 i) (not_le.mpr hij)
    rw [Units.val_mul, Matrix.mul_apply, Fintype.sum_eq_add_sum_subtype_ne _ i0, hV1 j, if_neg hj,
      mul_zero, zero_add]
    by_cases hi : i = i0
    · apply Finset.sum_eq_zero
      intro l _
      rw [hi, hrow _ l.2, zero_mul]
    · have hb : b'.val ⟨i, hi⟩ ⟨j, hj⟩ = 0 := hb' hij
      have hbA : b' = A * w'⁻¹ := by rw [hAw, mul_inv_cancel_right]
      have e : ∑ l : {i // i ≠ i0}, (h * u1 * u2).val i l * V.val l j = (A * w'⁻¹).val ⟨i, hi⟩ ⟨j, hj⟩ := by
        rw [show (A * w'⁻¹).val = A.val * (w'⁻¹).val from Units.val_mul _ _, Matrix.mul_apply]
        refine Finset.sum_congr rfl (fun l _ => ?_)
        rw [hA, ← hV3]
      rw [e, ← hbA]
      exact hb

/- English proof (translation)
Introduce `k _ _ _ _ ι _ _ lv h`. Conclude with `exists_blockTriangular_mul_mem_KO_eq _ ι rfl lv h`.
-/
theorem iwasawa_blockTriangular : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k]
    [IsNonarchimedeanLocalField k] (ι : Type) [Fintype ι] [DecidableEq ι] (lv : ι → ℕ) (h : GL ι k),
    ∃ (b : GL ι k), b.val.BlockTriangular lv ∧ ∃ w ∈ KO k ι, h = b * w := by
  intro k _ _ _ _ ι _ _ lv h
  exact exists_blockTriangular_mul_mem_KO_eq _ ι rfl lv h

end GlobalTheory.SplitWeil
