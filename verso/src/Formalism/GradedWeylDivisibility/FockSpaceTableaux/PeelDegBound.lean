import Formalism.GradedWeylDivisibility.StatementC
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LCdegLemmas

open MvPolynomial

noncomputable section

namespace Formalism.GradedWeylDivisibility

/- English proof (translation)
Establish `key` using `hom_congr_vars (f₁ := (aeval g : MvPolynomial τ B →ₐ[B] MvPolynomial τ B).toRingHom) (f₂ := RingHom.id _) (p₁ := p) (p₂ := p) (RingHom.ext fun b => by simp [algebraMap_eq]) (fun i hi _ => by simpa using h i hi) rfl`. Simplify using `using key`.
-/
private theorem aeval_eq_self_of_eq_X_on_vars {τ B : Type*} [CommRing B] (g : τ → MvPolynomial τ B)
    (p : MvPolynomial τ B) (h : ∀ i ∈ p.vars, g i = X i) : aeval g p = p := by
  have key := hom_congr_vars (f₁ := (aeval g : MvPolynomial τ B →ₐ[B] MvPolynomial τ B).toRingHom)
    (f₂ := RingHom.id _) (p₁ := p) (p₂ := p) (RingHom.ext fun b => by simp [algebraMap_eq])
    (fun i hi _ => by simpa using h i hi) rfl
  simpa using key

/- English proof (translation)
Use `Nat.le_zero.1 (degreeOf_le_iff.2 fun m hm => ?_)` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Conclude with `h ((mem_vars i).2 ⟨m, hm, Finsupp.mem_support_iff.2 (by omega)⟩)`.
-/
private theorem degreeOf_eq_zero_of_not_mem_vars {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : i ∉ p.vars) : degreeOf i p = 0 := by
  refine Nat.le_zero.1 (degreeOf_le_iff.2 fun m hm => ?_)
  by_contra hne
  exact h ((mem_vars i).2 ⟨m, hm, Finsupp.mem_support_iff.2 (by omega)⟩)

/- English proof (translation)
Introduce `hi`. Take `⟨m, hm, hmi⟩` from `(mem_vars i).1 hi`. Establish `h1` using `degreeOf_le_iff.1 h.le m hm`. Conclude with `Finsupp.mem_support_iff.1 hmi (by omega)`.
-/
private theorem not_mem_vars_of_degreeOf_eq_zero {τ B : Type*} [CommRing B] (i : τ)
    (p : MvPolynomial τ B) (h : degreeOf i p = 0) : i ∉ p.vars := by
  intro hi
  obtain ⟨m, hm, hmi⟩ := (mem_vars i).1 hi
  have h1 := degreeOf_le_iff.1 h.le m hm
  exact Finsupp.mem_support_iff.1 hmi (by omega)

/- English proof (translation)
Take `⟨Y, hY⟩ : ∃ Y : MvPolynomial τ B, Y = X y + X c * X x` from `⟨_, rfl⟩`. Rewrite `hs` using `[← hY]`. Take `⟨Q, hQ⟩ : ∃ Q : MvPolynomial τ B, Q = ∑ k ∈ Finset.range (K + 1), X x ^ k * Y ^ (K - k) * W k` from `⟨_, rfl⟩`. Rewrite `hs` using `[← hQ]`. Establish `hX : ∀ v : τ, (X v : MvPolynomial τ B) ≠ 0`.

Introduce `v hv`. Establish `h1 : degreeOf v (0 : MvPolynomial τ B) ≤ 0` using `degreeOf_le_iff.2 fun m hm => by simp at hm`. Rewrite `h1` using `[← hv, degreeOf_X]`. Simplify using `at h1`. Establish `hYσ : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v) Y = 0`.

Rewrite using `[hY]`. Simplify using `[hxy.symm, hxc.symm, hyc.symm]`. Establish `hWσ : ∀ k, aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v) (W k) = W k`. Introduce `k`. Use `aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_` and prove the remaining obligations.

Simplify using `[(hW k i hi).1, (hW k i hi).2]`. Establish `hsum : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v) Q = W K`. Rewrite using `[hQ, map_sum, Finset.sum_eq_single K]`. Rewrite using `[Nat.sub_self, pow_zero, mul_one, map_mul, map_pow, hWσ, aeval_X]`. Simplify using the standard rewrite rules.

Introduce `k hk hkK`. Establish `hk' : K - k ≠ 0`. Rewrite `hk` using `[Finset.mem_range]`. Use linear arithmetic over natural numbers and integers. Simplify using `only [map_mul, map_pow, hYσ, zero_pow hk', mul_zero, zero_mul]`.

Introduce `h`. Conclude with `absurd (Finset.self_mem_range_succ K) h`. Establish `hQ0 : Q ≠ 0`. Introduce `h`. Rewrite `hsum` using `[h, map_zero]`.

Conclude with `hWK hsum.symm`. Establish `hcY : 1 ≤ degreeOf c Y`. Assume the negation of the conclusion as `hlt`. Establish `h0 : degreeOf c Y = 0` using `by omega`. Establish `hfix : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v) Y = Y`.

Use `aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_` and prove the remaining obligations. Establish `hic : i ≠ c` using `fun h => not_mem_vars_of_degreeOf_eq_zero c Y h0 (by rwa [h] at hi)`. Simplify using `[hic]`. Establish `h2 : (X c : MvPolynomial τ B) * X x = 0`. Establish `h3 : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v) (X y + X c * X x : MvPolynomial τ B) = X y`.

Simplify using `[hyc, hxc]`. Rewrite `h3` using `[← hY, hfix, hY]`. Take the linear combination `h3`. Conclude with `mul_ne_zero (hX c) (hX x) h2`. Establish `hY0 : Y ≠ 0`.

Introduce and unpack `rfl`. Establish `h1 : degreeOf c (0 : MvPolynomial τ B) ≤ 0` using `degreeOf_le_iff.2 fun m hm => by simp at hm`. Use linear arithmetic over natural numbers and integers. Establish `hyQ : degreeOf y Q ≤ K`. Rewrite using `[hQ]`.

Use `Finset.sum_induction _ (fun q => degreeOf y q ≤ K) (fun a b ha hb => (degreeOf_add_le y a b).trans (max_le ha hb)) (degreeOf_le_iff.2 fun m hm => by simp at hm) ?_` and prove the remaining obligations. Introduce `k _`. Use `show degreeOf y (X x ^ k * Y ^ (K - k) * W k) ≤ K`. Establish `h1` using `degreeOf_mul_le y (X x ^ k * Y ^ (K - k)) (W k)`. Establish `h2` using `degreeOf_mul_le y (X x ^ k) (Y ^ (K - k))`.

Establish `h3` using `degreeOf_pow_le y (X x : MvPolynomial τ B) k`. Establish `h4` using `degreeOf_pow_le y Y (K - k)`. Establish `h5 : degreeOf y (X x : MvPolynomial τ B) = 0`. Rewrite using `[degreeOf_X]`. Simplify using `[hxy.symm]`.

Establish `h6 : degreeOf y Y ≤ 1`. Rewrite using `[hY]`. Use `(degreeOf_add_le _ _ _).trans (max_le ?_ ?_)` and prove the remaining obligations. Apply the tactic sequence `rw [degreeOf_X]; split_ifs <;> omega`. Use `(degreeOf_mul_le _ _ _).trans ?_` and prove the remaining obligations.

Rewrite using `[degreeOf_X, degreeOf_X]`. Simplify using `[hyc, hxy.symm]`. Establish `h7 : degreeOf y (W k) = 0` using `degreeOf_eq_zero_of_not_mem_vars y (W k) fun hi => (hW k y hi).2 rfl`. Rewrite `h3` using `[h5, mul_zero]`. Establish `h8 : (K - k) * degreeOf y Y ≤ K - k`.

Simplify using `using Nat.mul_le_mul_left (K - k) h6`. Generalize the expression as in `(K - k) * degreeOf y Y = t at h4 h8`. Use linear arithmetic over natural numbers and integers. Establish `key : degreeOf c (W K) ≤ degreeOf c Q + degreeOf y Q`. Use `hE B τ x y c hxy hxc hyc Q using 2` and compare the differences between its conclusion and the goal.

Conclude with `hsum.symm`. Rewrite `hs` using `[degreeOf_mul_eq (pow_ne_zero _ hY0) hQ0, degreeOf_pow_eq c Y e hY0]`. Establish `he : e ≤ e * degreeOf c Y` using `by simpa using Nat.mul_le_mul_left e hcY`. Generalize the expression as in `e * degreeOf c Y = t at hs he`. Apply the tactic sequence `constructor <;> omega`.
-/
private theorem le_and_degreeOf_top_le_of_degreeOf_sum_le {B τ : Type} [CommRing B] [IsDomain B] [DecidableEq τ]
    (hE : EvalDeg) (x y c : τ) (hxy : x ≠ y) (hxc : x ≠ c) (hyc : y ≠ c) (K e s : ℕ)
    (W : ℕ → MvPolynomial τ B) (hW : ∀ k, ∀ i ∈ (W k).vars, i ≠ x ∧ i ≠ y) (hWK : W K ≠ 0)
    (hs : degreeOf c ((X y + X c * X x) ^ e *
      ∑ k ∈ Finset.range (K + 1), X x ^ k * (X y + X c * X x) ^ (K - k) * W k) ≤ s) :
    e ≤ s ∧ degreeOf c (W K) ≤ s - e + K := by
  obtain ⟨Y, hY⟩ : ∃ Y : MvPolynomial τ B, Y = X y + X c * X x := ⟨_, rfl⟩
  rw [← hY] at hs
  obtain ⟨Q, hQ⟩ : ∃ Q : MvPolynomial τ B,
      Q = ∑ k ∈ Finset.range (K + 1), X x ^ k * Y ^ (K - k) * W k := ⟨_, rfl⟩
  rw [← hQ] at hs
  have hX : ∀ v : τ, (X v : MvPolynomial τ B) ≠ 0 := by
    intro v hv
    have h1 : degreeOf v (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    rw [← hv, degreeOf_X] at h1
    simp at h1
  have hYσ : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c else X v)
      Y = 0 := by
    rw [hY]; simp [hxy.symm, hxc.symm, hyc.symm]
  have hWσ : ∀ k, aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) (W k) = W k := by
    intro k
    refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
    simp [(hW k i hi).1, (hW k i hi).2]
  have hsum : aeval (fun v : τ => if v = x then (1 : MvPolynomial τ B) else if v = y then -X c
      else X v) Q = W K := by
    rw [hQ, map_sum, Finset.sum_eq_single K]
    · rw [Nat.sub_self, pow_zero, mul_one, map_mul, map_pow, hWσ, aeval_X]
      simp
    · intro k hk hkK
      have hk' : K - k ≠ 0 := by
        rw [Finset.mem_range] at hk; omega
      simp only [map_mul, map_pow, hYσ, zero_pow hk', mul_zero, zero_mul]
    · intro h; exact absurd (Finset.self_mem_range_succ K) h
  have hQ0 : Q ≠ 0 := by
    intro h; rw [h, map_zero] at hsum; exact hWK hsum.symm
  have hcY : 1 ≤ degreeOf c Y := by
    by_contra hlt
    have h0 : degreeOf c Y = 0 := by omega
    have hfix : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v) Y = Y := by
      refine aeval_eq_self_of_eq_X_on_vars _ _ fun i hi => ?_
      have hic : i ≠ c := fun h => not_mem_vars_of_degreeOf_eq_zero c Y h0 (by rwa [h] at hi)
      simp [hic]
    have h2 : (X c : MvPolynomial τ B) * X x = 0 := by
      have h3 : aeval (fun v : τ => if v = c then (0 : MvPolynomial τ B) else X v)
          (X y + X c * X x : MvPolynomial τ B) = X y := by
        simp [hyc, hxc]
      rw [← hY, hfix, hY] at h3
      linear_combination h3
    exact mul_ne_zero (hX c) (hX x) h2
  have hY0 : Y ≠ 0 := by
    rintro rfl
    have h1 : degreeOf c (0 : MvPolynomial τ B) ≤ 0 := degreeOf_le_iff.2 fun m hm => by simp at hm
    omega
  have hyQ : degreeOf y Q ≤ K := by
    rw [hQ]
    refine Finset.sum_induction _ (fun q => degreeOf y q ≤ K)
      (fun a b ha hb => (degreeOf_add_le y a b).trans (max_le ha hb))
      (degreeOf_le_iff.2 fun m hm => by simp at hm) ?_
    intro k _
    show degreeOf y (X x ^ k * Y ^ (K - k) * W k) ≤ K
    have h1 := degreeOf_mul_le y (X x ^ k * Y ^ (K - k)) (W k)
    have h2 := degreeOf_mul_le y (X x ^ k) (Y ^ (K - k))
    have h3 := degreeOf_pow_le y (X x : MvPolynomial τ B) k
    have h4 := degreeOf_pow_le y Y (K - k)
    have h5 : degreeOf y (X x : MvPolynomial τ B) = 0 := by
      rw [degreeOf_X]; simp [hxy.symm]
    have h6 : degreeOf y Y ≤ 1 := by
      rw [hY]
      refine (degreeOf_add_le _ _ _).trans (max_le ?_ ?_)
      · rw [degreeOf_X]; split_ifs <;> omega
      · refine (degreeOf_mul_le _ _ _).trans ?_
        rw [degreeOf_X, degreeOf_X]
        simp [hyc, hxy.symm]
    have h7 : degreeOf y (W k) = 0 :=
      degreeOf_eq_zero_of_not_mem_vars y (W k) fun hi => (hW k y hi).2 rfl
    rw [h5, mul_zero] at h3
    have h8 : (K - k) * degreeOf y Y ≤ K - k := by
      simpa using Nat.mul_le_mul_left (K - k) h6
    generalize (K - k) * degreeOf y Y = t at h4 h8
    omega
  have key : degreeOf c (W K) ≤ degreeOf c Q + degreeOf y Q := by
    convert hE B τ x y c hxy hxc hyc Q using 2
    exact hsum.symm
  rw [degreeOf_mul_eq (pow_ne_zero _ hY0) hQ0, degreeOf_pow_eq c Y e hY0] at hs
  have he : e ≤ e * degreeOf c Y := by simpa using Nat.mul_le_mul_left e hcY
  generalize e * degreeOf c Y = t at hs he
  constructor <;> omega

/- English proof (translation)
Introduce `B _ _ r n l j hlj a0 K e s w hw hK hs`. Establish `hφX : ∀ v : Fin r × Fin n, colAddGen B l j (X v : MvPolynomial (Fin r × Fin n) B) = if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v)`. Introduce `v`. Simplify using `only [colAddGen, aeval_X]`. Establish `hinj : ∀ f : MvPolynomial (Fin r × Fin n) B, colAddGen B l j f = 0 → f = 0`.

Introduce `f hf`. Establish `hl : (aeval (fun v : Option (Fin r × Fin n) => v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)).comp (colAddGen B l j) = AlgHom.id B _`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Simplify using `only [AlgHom.comp_apply, AlgHom.id_apply, hφX]`.

Apply the tactic sequence `split_ifs <;> simp`. Establish `h1` using `congrArg (aeval (fun v : Option (Fin r × Fin n) => v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)) hf`. Rewrite `h1` using `[map_zero, ← AlgHom.comp_apply, hl, AlgHom.id_apply]`. Conclude with `h1`. Establish `hvars : ∀ k, ∀ i ∈ (colAddGen B l j (w k)).vars, i ≠ some (a0, l) ∧ i ≠ some (a0, j)`.

Introduce `k i hi`. Establish `hi2 : i ∈ ((bind₁ fun v : Fin r × Fin n => if v.2 = j then (X (some v) + X none * X (some (v.1, l)) : MvPolynomial (Option (Fin r × Fin n)) B) else X (some v)) (w k)).vars`. Rewrite using `[← aeval_eq_bind₁]`. Conclude with `hi`. Establish `hi3` using `vars_bind₁ _ _ hi2`.

Rewrite `hi3` using `[Finset.mem_biUnion]`. Take `⟨v, hv, hiv⟩` from `hi3`. Take `⟨m, hm, hmv⟩` from `(mem_vars v).1 hv`. Establish `hvl : v ≠ (a0, l)`. Introduce and unpack `rfl`.

Conclude with `(Finsupp.mem_support_iff.1 hmv) (hw k m hm).1`. Establish `hvj : v ≠ (a0, j)`. Introduce and unpack `rfl`. Conclude with `(Finsupp.mem_support_iff.1 hmv) (hw k m hm).2`. Use `split_ifs at hiv with hv2`.

Break down `Finset.mem_union.1 (vars_add_subset _ _ hiv) with h1 | h1` into its components or cases. Rewrite `h1` using `[vars_X, Finset.mem_singleton]`. Substitute `h1` using the available equality. Simplify using `[hvl, hvj]`. Break down `Finset.mem_union.1 (vars_mul _ _ h1) with h2 | h2` into its components or cases.

Rewrite `h2` using `[vars_X, Finset.mem_singleton]`. Substitute `h2` using the available equality. Simplify using the standard rewrite rules. Rewrite `h2` using `[vars_X, Finset.mem_singleton]`. Substitute `h2` using the available equality.

Use `⟨fun h => ?_, by simp [hlj]⟩` and prove the remaining obligations. Simplify using `only [Option.some.injEq, Prod.mk.injEq, and_true] at h`. Conclude with `hvj (Prod.ext h hv2)`. Rewrite `hiv` using `[vars_X, Finset.mem_singleton]`. Substitute `hiv` using the available equality.

Simplify using `[hvl, hvj]`. Establish `e1 : colAddGen B l j (X (a0, l) : MvPolynomial (Fin r × Fin n) B) = X (some (a0, l))`. Rewrite using `[hφX]`. Simplify using `[hlj]`. Establish `e2 : colAddGen B l j (X (a0, j) : MvPolynomial (Fin r × Fin n) B) = X (some (a0, j)) + X none * X (some (a0, l))`.

Rewrite using `[hφX]`. Simplify using the standard rewrite rules. Establish `hQ : colAddGen B l j (∑ k ∈ Finset.range (K + 1), X (a0, l) ^ k * X (a0, j) ^ (e + (K - k)) * w k) = (X (some (a0, j)) + X none * X (some (a0, l))) ^ e * ∑ k ∈ Finset.range (K + 1), X (some (a0, l)) ^ k * (X (some (a0, j)) + X none * X (some (a0, l))) ^ (K - k) * colAddGen B l j …`. Rewrite using `[map_sum, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations.

Rewrite using `[map_mul, map_mul, map_pow, map_pow, e1, e2, pow_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hs` using `[hQ]`. Conclude with `le_and_degreeOf_top_le_of_degreeOf_sum_le hE (some (a0, l)) (some (a0, j)) none (by simp [hlj]) (by simp) (by simp) K e s (fun k => colAddGen B l j (w k)) hvars (fun h => hK (hinj _ h)) hs`.
-/
theorem peelDegBound_of (hE : EvalDeg) : PeelDegBound := by
  intro B _ _ r n l j hlj a0 K e s w hw hK hs
  have hφX : ∀ v : Fin r × Fin n, colAddGen B l j (X v : MvPolynomial (Fin r × Fin n) B) =
      if v.2 = j then X (some v) + X none * X (some (v.1, l)) else X (some v) := by
    intro v; simp only [colAddGen, aeval_X]
  have hinj : ∀ f : MvPolynomial (Fin r × Fin n) B, colAddGen B l j f = 0 → f = 0 := by
    intro f hf
    have hl : (aeval (fun v : Option (Fin r × Fin n) => v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)).comp
        (colAddGen B l j) = AlgHom.id B _ := by
      apply MvPolynomial.algHom_ext
      intro v
      simp only [AlgHom.comp_apply, AlgHom.id_apply, hφX]
      split_ifs <;> simp
    have h1 := congrArg (aeval (fun v : Option (Fin r × Fin n) =>
      v.elim (0 : MvPolynomial (Fin r × Fin n) B) X)) hf
    rw [map_zero, ← AlgHom.comp_apply, hl, AlgHom.id_apply] at h1
    exact h1
  have hvars : ∀ k, ∀ i ∈ (colAddGen B l j (w k)).vars,
      i ≠ some (a0, l) ∧ i ≠ some (a0, j) := by
    intro k i hi
    have hi2 : i ∈ ((bind₁ fun v : Fin r × Fin n => if v.2 = j then
        (X (some v) + X none * X (some (v.1, l)) : MvPolynomial (Option (Fin r × Fin n)) B)
        else X (some v)) (w k)).vars := by
      rw [← aeval_eq_bind₁]; exact hi
    have hi3 := vars_bind₁ _ _ hi2
    rw [Finset.mem_biUnion] at hi3
    obtain ⟨v, hv, hiv⟩ := hi3
    obtain ⟨m, hm, hmv⟩ := (mem_vars v).1 hv
    have hvl : v ≠ (a0, l) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).1
    have hvj : v ≠ (a0, j) := by
      rintro rfl; exact (Finsupp.mem_support_iff.1 hmv) (hw k m hm).2
    split_ifs at hiv with hv2
    · rcases Finset.mem_union.1 (vars_add_subset _ _ hiv) with h1 | h1
      · rw [vars_X, Finset.mem_singleton] at h1
        subst h1; simp [hvl, hvj]
      · rcases Finset.mem_union.1 (vars_mul _ _ h1) with h2 | h2
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2; simp
        · rw [vars_X, Finset.mem_singleton] at h2
          subst h2
          refine ⟨fun h => ?_, by simp [hlj]⟩
          simp only [Option.some.injEq, Prod.mk.injEq, and_true] at h
          exact hvj (Prod.ext h hv2)
    · rw [vars_X, Finset.mem_singleton] at hiv
      subst hiv; simp [hvl, hvj]
  have e1 : colAddGen B l j (X (a0, l) : MvPolynomial (Fin r × Fin n) B) = X (some (a0, l)) := by
    rw [hφX]; simp [hlj]
  have e2 : colAddGen B l j (X (a0, j) : MvPolynomial (Fin r × Fin n) B) =
      X (some (a0, j)) + X none * X (some (a0, l)) := by
    rw [hφX]; simp
  have hQ : colAddGen B l j
      (∑ k ∈ Finset.range (K + 1), X (a0, l) ^ k * X (a0, j) ^ (e + (K - k)) * w k) =
      (X (some (a0, j)) + X none * X (some (a0, l))) ^ e * ∑ k ∈ Finset.range (K + 1),
        X (some (a0, l)) ^ k * (X (some (a0, j)) + X none * X (some (a0, l))) ^ (K - k) *
          colAddGen B l j (w k) := by
    rw [map_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [map_mul, map_mul, map_pow, map_pow, e1, e2, pow_add]
    ring
  rw [hQ] at hs
  exact le_and_degreeOf_top_le_of_degreeOf_sum_le hE (some (a0, l)) (some (a0, j)) none (by simp [hlj]) (by simp) (by simp)
    K e s (fun k => colAddGen B l j (w k)) hvars (fun h => hK (hinj _ h)) hs

end Formalism.GradedWeylDivisibility
