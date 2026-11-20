import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Integral
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.Imports
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.EntryMod
import Development.AutomorphicArithmetic.AutomorphicVarieties.FrobeniusSmoothVectors.AlgClosed
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.CoQuot

open IsLocalRing Matrix UpperTheory.V.Alg UpperTheory.V.U3 UpperTheory.V.Fr UpperTheory.V.Fr.PF

section Sub

variable {O R : Type} [CommRing O] [IsLocalRing O] [CommRing R] [Algebra O R] [IsCO O R] (A : Subalgebra O R)
  [IsCO O A]

/- English proof (translation)
Rewrite using `[← res_eq_zero_iff O, ← res_eq_zero_iff O, ← res_map A.val]`. Both sides reduce to the same expression.
-/
private theorem mem_max (a : A) : (a : R) ∈ maximalIdeal R ↔ a ∈ maximalIdeal A := by
  rw [← res_eq_zero_iff O, ← res_eq_zero_iff O, ← res_map A.val]
  rfl

/- English proof (translation)
Use `choose c hc hx using hx`. Establish `hsep : ⨅ N : ℕ, maximalIdeal R ^ N = ⊥` using `Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top`. Take `⟨y, hy⟩` from `alg_closed A (maximalIdeal R) ⟨inferInstance, Subtype.val_injective, hsep, Ideal.ext (mem_max A), fun d => by`. Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) d`. Conclude with `⟨algebraMap O A a, ha⟩⟩ (fun N => ⟨c (N + 1), hc _⟩) (fun N => by`.

Establish `h` using `sub_mem (hx (N + 1)) (Ideal.pow_le_pow_right (Nat.le_succ _) (hx (N + 1 + 1)))`. Rewrite `h` using `[sub_sub_sub_cancel_left]`. Conclude with `h)`. Establish `h : x - y ∈ ⨅ N : ℕ, maximalIdeal R ^ N` using `Ideal.mem_iInf.2 fun N => by`. Establish `h` using `sub_mem (hx (N + 1)) (show (y : R) - c (N + 1) ∈ _ from hy N)`.

Rewrite `h` using `[sub_sub_sub_cancel_right]`. Conclude with `Ideal.pow_le_pow_right (Nat.le_succ _) h`. Rewrite `h` using `[hsep, Ideal.mem_bot, sub_eq_zero]`. Conclude with `h ▸ y.2`.
-/
private theorem closed {x : R} (hx : ∀ N : ℕ, ∃ y ∈ A, x - y ∈ maximalIdeal R ^ N) : x ∈ A := by
  choose c hc hx using hx
  have hsep : ⨅ N : ℕ, maximalIdeal R ^ N = ⊥ :=
    Ideal.iInf_pow_eq_bot_of_isLocalRing _ (maximalIdeal.isMaximal R).ne_top
  obtain ⟨y, hy⟩ := alg_closed A (maximalIdeal R)
    ⟨inferInstance, Subtype.val_injective, hsep, Ideal.ext (mem_max A), fun d => by
      obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) d
      exact ⟨algebraMap O A a, ha⟩⟩ (fun N => ⟨c (N + 1), hc _⟩) (fun N => by
      have h := sub_mem (hx (N + 1)) (Ideal.pow_le_pow_right (Nat.le_succ _) (hx (N + 1 + 1)))
      rw [sub_sub_sub_cancel_left] at h
      exact h)
  have h : x - y ∈ ⨅ N : ℕ, maximalIdeal R ^ N := Ideal.mem_iInf.2 fun N => by
    have h := sub_mem (hx (N + 1)) (show (y : R) - c (N + 1) ∈ _ from hy N)
    rw [sub_sub_sub_cancel_right] at h
    exact Ideal.pow_le_pow_right (Nat.le_succ _) h
  rw [hsep, Ideal.mem_bot, sub_eq_zero] at h
  exact h ▸ y.2

/- English proof (translation)
Take `⟨u, hu⟩` from `h2.exists_left_inv`. Establish `hu' : (u : R) * 2 = 1` using `congrArg A.val hu`. Establish `h1 : ζ ^ 2 ∈ A`. Use `mul_mem u.2 h` as an intermediate fact. Rewrite `this` using `[← mul_assoc, hu', one_mul]`. Then use the resulting hypothesis.

Take `⟨a, ha⟩` from `IsCO.res_surj (O := O) ζ`. Establish `ha' : IsUnit (algebraMap O A a)`. Assume the negation of the conclusion as `hn`. Use `add_mem ha ((mem_max A _).2 hn)` as an intermediate fact. Conclude with `this (by simpa using hζ)`.

Take `⟨d, hd, hd'⟩` from `HenselianRing.is_henselian (I := maximalIdeal A) (Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)) (Polynomial.monic_X_pow_sub_C _ two_ne_zero) (algebraMap O A a) (by`. Rewrite using `[← mem_max]`. Establish `: (((Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)).eval (algebraMap O A a) : A) : R) = -(ζ + algebraMap O R a) * (ζ - algebraMap O R a)` using `by simp; ring`. Rewrite using `[this]`. Conclude with `Ideal.mul_mem_left _ _ ha) (by`.

Use `IsUnit.map _ ?_` and prove the remaining obligations. Simplify `h2.mul ha')` using `[one_add_one_eq_two]`. Establish `e1 : ((d : R) + ζ) * (d - ζ) = 0`. Use `congrArg A.val hd` as an intermediate fact. Simplify using `at this`.

Take the linear combination `this`. Establish `e2 : IsUnit ((d : R) + ζ)`. Assume the negation of the conclusion as `hn`. Establish `h3 : (d : R) - algebraMap O R a ∈ maximalIdeal R` using `(mem_max A _).2 hd'`. Establish `h4` using `add_mem (sub_mem (show (d : R) + ζ ∈ maximalIdeal R from hn) h3) ha`.

Establish `h5 : (d : R) + ζ - (d - algebraMap O R a) + (ζ - algebraMap O R a) = 2 * ζ` using `by ring`. Rewrite `h4` using `[h5]`. Conclude with `h4 ((IsUnit.of_mul_eq_one_right _ hu').mul hζ)`. Conclude with `sub_eq_zero.1 (e2.mul_right_eq_zero.1 e1) ▸ d.2`.
-/
private theorem sqrt_mem (h2 : IsUnit (2 : A)) {ζ : R} (hζ : IsUnit ζ) (h : 2 * ζ ^ 2 ∈ A) : ζ ∈ A := by
  obtain ⟨u, hu⟩ := h2.exists_left_inv
  have hu' : (u : R) * 2 = 1 := congrArg A.val hu
  have h1 : ζ ^ 2 ∈ A := by
    have := mul_mem u.2 h
    rwa [← mul_assoc, hu', one_mul] at this
  obtain ⟨a, ha⟩ := IsCO.res_surj (O := O) ζ
  have ha' : IsUnit (algebraMap O A a) := by
    by_contra hn
    have := add_mem ha ((mem_max A _).2 hn)
    exact this (by simpa using hζ)
  obtain ⟨d, hd, hd'⟩ := HenselianRing.is_henselian (I := maximalIdeal A)
    (Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
    (algebraMap O A a) (by
      rw [← mem_max]
      have : (((Polynomial.X ^ 2 - Polynomial.C (⟨ζ ^ 2, h1⟩ : A)).eval (algebraMap O A a) : A) : R) =
          -(ζ + algebraMap O R a) * (ζ - algebraMap O R a) := by
        simp; ring
      rw [this]
      exact Ideal.mul_mem_left _ _ ha) (by
      refine IsUnit.map _ ?_
      simpa [one_add_one_eq_two] using h2.mul ha')
  have e1 : ((d : R) + ζ) * (d - ζ) = 0 := by
    have := congrArg A.val hd
    simp at this
    linear_combination this
  have e2 : IsUnit ((d : R) + ζ) := by
    by_contra hn
    have h3 : (d : R) - algebraMap O R a ∈ maximalIdeal R := (mem_max A _).2 hd'
    have h4 := add_mem (sub_mem (show (d : R) + ζ ∈ maximalIdeal R from hn) h3) ha
    have h5 : (d : R) + ζ - (d - algebraMap O R a) + (ζ - algebraMap O R a) = 2 * ζ := by ring
    rw [h5] at h4
    exact h4 ((IsUnit.of_mul_eq_one_right _ hu').mul hζ)
  exact sub_eq_zero.1 (e2.mul_right_eq_zero.1 e1) ▸ d.2

end Sub

/- English proof (translation)
Apply the tactic sequence `rcases hn with rfl | rfl <;> decide`.
-/
private theorem w_facts {n : ℕ} (hn : n = 2 ∨ n = 3) :
    (∀ i, w n i = 1 ∨ w n i = 0 ∨ w n i = -1) ∧ (∀ i j, w n i = w n j → i = j) ∧ (∀ i, w n i.rev = - w n i) ∧
    (∀ i j k m, 0 < w n i - w n j → w n k - w n m < 0 → j = k ∨ m = i ∨ i.rev = k ∨ m = j.rev) ∧
    (∑ i, w n i ^ 2 = 2) ∧ (∃ i, w n i = 1) := by
  rcases hn with rfl | rfl <;> decide

/- English proof (translation)
Take `⟨w1, w2, -⟩` from `w_facts hn`. Take `⟨u, hu⟩` from `h2.exists_left_inv`. Establish `hu' : algebraMap C K u * 2 = 1`. Use `congrArg (algebraMap C K) hu` as an intermediate fact. Rewrite `this` using `[map_mul, map_ofNat, map_one]`. Then use the resulting hypothesis.

Establish `hyy` using `span_mul r hy hy`. Establish `h1 : (1 : Matrix (Fin n) (Fin n) K) ∈ Submodule.span C (Set.range r)` using `Submodule.subset_span ⟨1, map_one r⟩`. Establish `key : ∀ f : Fin n → K, f i = 1 → (∀ j, w n j ≠ w n i → f j = 0) → diagonal f = Matrix.single i i (1 : K)`. Introduce `f e1 e2`. Rewrite using `[← Matrix.diagonal_single]`.

Use `congr 1`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Rewrite using `[h, e1, Pi.single_eq_same]`. Rewrite using `[e2 j fun e => h (w2 _ _ e), Pi.single_eq_of_ne h]`.

Rewrite `hyy` using `[diagonal_mul_diagonal]`. Break down `w1 i with h | h | h` into its components or cases. Use `Submodule.smul_mem _ u (add_mem hyy hy)` as an intermediate fact. Rewrite `this` using `[diagonal_add, ← diagonal_smul]`. Use `key _ ?_ (fun j hj => ?_) ▸ this` and prove the remaining obligations.

Simplify using `[h, Algebra.smul_def, one_add_one_eq_two, hu']`. Rewrite `hj` using `[h]`. Apply the tactic sequence `rcases w1 j with e | e | e <;> simp [e] at hj ⊢`. Use `sub_mem h1 hyy` as an intermediate fact. Rewrite `this` using `[← diagonal_one, diagonal_sub]`.

Use `key _ ?_ (fun j hj => ?_) ▸ this` and prove the remaining obligations. Simplify using `[h]`. Rewrite `hj` using `[h]`. Apply the tactic sequence `rcases w1 j with e | e | e <;> simp [e] at hj ⊢`. Use `Submodule.smul_mem _ u (sub_mem hyy hy)` as an intermediate fact.

Rewrite `this` using `[diagonal_sub, ← diagonal_smul]`. Use `key _ ?_ (fun j hj => ?_) ▸ this` and prove the remaining obligations. Simplify using `[h, Algebra.smul_def, one_add_one_eq_two, hu']`. Rewrite `hj` using `[h]`. Apply the tactic sequence `rcases w1 j with e | e | e <;> simp [e] at hj ⊢`.
-/
private theorem units_mem {G C K : Type} [Monoid G] [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (hn : n = 2 ∨ n = 3) (r : G →* Matrix (Fin n) (Fin n) K) (h2 : IsUnit (2 : C))
    (hy : (diagonal fun i => (w n i : K)) ∈ Submodule.span C (Set.range r)) (i : Fin n) :
    Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range r) := by
  obtain ⟨w1, w2, -⟩ := w_facts hn
  obtain ⟨u, hu⟩ := h2.exists_left_inv
  have hu' : algebraMap C K u * 2 = 1 := by
    have := congrArg (algebraMap C K) hu
    rwa [map_mul, map_ofNat, map_one] at this
  have hyy := span_mul r hy hy
  have h1 : (1 : Matrix (Fin n) (Fin n) K) ∈ Submodule.span C (Set.range r) := Submodule.subset_span ⟨1, map_one r⟩
  have key : ∀ f : Fin n → K, f i = 1 → (∀ j, w n j ≠ w n i → f j = 0) → diagonal f = Matrix.single i i (1 : K) := by
    intro f e1 e2
    rw [← Matrix.diagonal_single]
    congr 1
    funext j
    by_cases h : j = i
    · rw [h, e1, Pi.single_eq_same]
    · rw [e2 j fun e => h (w2 _ _ e), Pi.single_eq_of_ne h]
  rw [diagonal_mul_diagonal] at hyy
  rcases w1 i with h | h | h
  · have := Submodule.smul_mem _ u (add_mem hyy hy)
    rw [diagonal_add, ← diagonal_smul] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h, Algebra.smul_def, one_add_one_eq_two, hu']
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢
  · have := sub_mem h1 hyy
    rw [← diagonal_one, diagonal_sub] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h]
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢
  · have := Submodule.smul_mem _ u (sub_mem hyy hy)
    rw [diagonal_sub, ← diagonal_smul] at this
    refine key _ ?_ (fun j hj => ?_) ▸ this
    · simp [h, Algebra.smul_def, one_add_one_eq_two, hu']
    · rw [h] at hj
      rcases w1 j with e | e | e <;> simp [e] at hj ⊢

/- English proof (translation)
Proceed by induction on `hm using Submodule.span_induction with`. Consider the case `mem x hx => obtain ⟨g, rfl⟩ := hx`. Conclude with `ht g`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add x y _ _ hx hy`.

Take `⟨c, h1⟩` from `hx`. Take `⟨d, h2⟩` from `hy`. Conclude with `⟨c + d, by rw [map_add, h1, h2, trace_add]⟩`. Consider the case `smul a x _ hx`. Take `⟨c, h1⟩` from `hx`.

Conclude with `⟨a * c, by rw [map_mul, h1, trace_smul, Algebra.smul_def]⟩`.
-/
private theorem trace_mem {G C K : Type} [Monoid G] [CommRing C] [CommRing K] [Algebra C K] {n : ℕ}
    (r : G →* Matrix (Fin n) (Fin n) K) (ht : ∀ g, ∃ c, algebraMap C K c = (r g).trace)
    {m : Matrix (Fin n) (Fin n) K} (hm : m ∈ Submodule.span C (Set.range r)) : ∃ c, algebraMap C K c = m.trace := by
  induction hm using Submodule.span_induction with
  | mem x hx => obtain ⟨g, rfl⟩ := hx; exact ht g
  | zero => exact ⟨0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨c, h1⟩ := hx
    obtain ⟨d, h2⟩ := hy
    exact ⟨c + d, by rw [map_add, h1, h2, trace_add]⟩
  | smul a x _ hx =>
    obtain ⟨c, h1⟩ := hx
    exact ⟨a * c, by rw [map_mul, h1, trace_smul, Algebra.smul_def]⟩

section Mon

variable {l : ℕ} [Fact l.Prime] {k : Type} [Field k] [CharP k l] {F : Frame l k} {C₀ : ℕ} {n : ℕ}

/- English proof (translation)
Take `⟨-, -, -, -, hs⟩` from `UpperTheory.V.Fr.star hF`. Take `⟨-, w2, w3, w4, -⟩` from `w_facts hn`. Take `⟨L, hL, rfl⟩` from `hx`. Set `E : Fin n → Fin n → Submodule C K` to `fun i j => Submodule.span C (Set.range fun g => ρ.r g i j)`. Establish `hmem : ∀ g i j, ρ.r g i j ∈ E i j` using `fun g i j => Submodule.subset_span ⟨g, rfl⟩`.

Establish `hrev : ∀ i j, ∀ x ∈ E i j, x ∈ E j.rev i.rev` using `fun i j => by`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Establish `h` using `hmem (F.star g) j.rev i.rev`. Rewrite `h` using `[hs, Fin.rev_rev, Fin.rev_rev]`. Then use the resulting hypothesis.

Establish `hdiag : ∀ i, ∀ x ∈ E i i, ∃ c, algebraMap C K c = x` using `fun i x hx => by`. Simplify using `using trace_mem ρ.r ht (single_mem hE hx)`. Set `N : ℤ → Set K` to `fun a => {x | ∃ i j, w n i - w n j = a ∧ x ∈ E i j}`. Establish `step : ∀ i j k, ∀ x ∈ E i j, ∀ y ∈ E j k, ∀ s, s = w n i - w n k → x * y ∈ N s ∧ (s = 0 → ∃ c ∈ (⊤ : Ideal C), algebraMap C K c = x * y)`. Introduce `i j k x hx y hy s hs'`.

Use `⟨⟨i, k, hs'.symm, ent_mul hE hx hy⟩, fun h => ?_⟩` and prove the remaining obligations. Take `rfl : i = k` from `w2 i k (by omega)`. Take `⟨c, hc⟩` from `hdiag i _ (ent_mul hE hx hy)`. Conclude with `⟨c, trivial, hc⟩`. Take `⟨c, h1, -⟩` from `cycles (⊤ : Ideal C) N (by`.

Introduce and unpack `x ⟨i, j, h, hx⟩`. Take `rfl : i = j` from `w2 i j (by omega)`. Conclude with `hdiag i x hx)`. Use the proof step `(by`. Introduce and unpack `_ _ ha hb x ⟨i, j, rfl, hx⟩ y ⟨k, m, rfl, hy⟩`.

Establish `e1` using `w3 i`. Establish `e2` using `w3 j`. Break down `w4 i j k m ha hb with rfl | rfl | rfl | rfl` into its components or cases. Conclude with `step _ _ _ x hx y hy _ (by omega)`. Rewrite using `[mul_comm]`.

Conclude with `step _ _ _ y hy x hx _ (by omega)`. Conclude with `step _ _ _ x (hrev _ _ x hx) y hy _ (by omega)`. Rewrite using `[mul_comm]`. Conclude with `step _ _ _ y hy x (hrev _ _ x hx) _ (by omega))`. Use the proof step `((L : Multiset (F.G0 × Fin n × Fin n)).map fun s => (w n s.2.1 - w n s.2.2, ρ.r s.1 s.2.1 s.2.2))`.

Use the proof step `(fun p hp => by`. Take `⟨s, -, rfl⟩` from `Multiset.mem_map.1 hp`. Conclude with `⟨_, _, rfl, hmem _ _ _⟩)`. Use the proof step `(by rw [Multiset.map_map, Multiset.map_coe, Multiset.sum_coe]; exact hL)`. Use `⟨c, ?_⟩` and prove the remaining obligations.

Rewrite using `[h1, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]`. Both sides reduce to the same expression.
-/
private theorem mon_mem (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {C K : Type} [CommRing C] [CommRing K] [Algebra C K]
    (ρ : NRep F n K) (ht : ∀ g, ∃ c, algebraMap C K c = (ρ.r g).trace)
    (hE : ∀ i, Matrix.single i i (1 : K) ∈ Submodule.span C (Set.range ρ.r)) {x : K} (hx : x ∈ ρ.mon 0) :
    ∃ c, algebraMap C K c = x := by
  obtain ⟨-, -, -, -, hs⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨-, w2, w3, w4, -⟩ := w_facts hn
  obtain ⟨L, hL, rfl⟩ := hx
  let E : Fin n → Fin n → Submodule C K := fun i j => Submodule.span C (Set.range fun g => ρ.r g i j)
  have hmem : ∀ g i j, ρ.r g i j ∈ E i j := fun g i j => Submodule.subset_span ⟨g, rfl⟩
  have hrev : ∀ i j, ∀ x ∈ E i j, x ∈ E j.rev i.rev := fun i j => by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨g, rfl⟩
    have h := hmem (F.star g) j.rev i.rev
    rwa [hs, Fin.rev_rev, Fin.rev_rev] at h
  have hdiag : ∀ i, ∀ x ∈ E i i, ∃ c, algebraMap C K c = x := fun i x hx => by
    simpa using trace_mem ρ.r ht (single_mem hE hx)
  let N : ℤ → Set K := fun a => {x | ∃ i j, w n i - w n j = a ∧ x ∈ E i j}
  have step : ∀ i j k, ∀ x ∈ E i j, ∀ y ∈ E j k, ∀ s, s = w n i - w n k →
      x * y ∈ N s ∧ (s = 0 → ∃ c ∈ (⊤ : Ideal C), algebraMap C K c = x * y) := by
    intro i j k x hx y hy s hs'
    refine ⟨⟨i, k, hs'.symm, ent_mul hE hx hy⟩, fun h => ?_⟩
    obtain rfl : i = k := w2 i k (by omega)
    obtain ⟨c, hc⟩ := hdiag i _ (ent_mul hE hx hy)
    exact ⟨c, trivial, hc⟩
  obtain ⟨c, h1, -⟩ := cycles (⊤ : Ideal C) N
    (by
      rintro x ⟨i, j, h, hx⟩
      obtain rfl : i = j := w2 i j (by omega)
      exact hdiag i x hx)
    (by
      rintro _ _ ha hb x ⟨i, j, rfl, hx⟩ y ⟨k, m, rfl, hy⟩
      have e1 := w3 i
      have e2 := w3 j
      rcases w4 i j k m ha hb with rfl | rfl | rfl | rfl
      · exact step _ _ _ x hx y hy _ (by omega)
      · rw [mul_comm]
        exact step _ _ _ y hy x hx _ (by omega)
      · exact step _ _ _ x (hrev _ _ x hx) y hy _ (by omega)
      · rw [mul_comm]
        exact step _ _ _ y hy x (hrev _ _ x hx) _ (by omega))
    ((L : Multiset (F.G0 × Fin n × Fin n)).map fun s => (w n s.2.1 - w n s.2.2, ρ.r s.1 s.2.1 s.2.2))
    (fun p hp => by
      obtain ⟨s, -, rfl⟩ := Multiset.mem_map.1 hp
      exact ⟨_, _, rfl, hmem _ _ _⟩)
    (by rw [Multiset.map_map, Multiset.map_coe, Multiset.sum_coe]; exact hL)
  refine ⟨c, ?_⟩
  rw [h1, Multiset.map_map, Multiset.map_coe, Multiset.prod_coe]
  rfl

/- English proof (translation)
Take `⟨-, -, -, -, hs⟩` from `UpperTheory.V.Fr.star hF`. Take `⟨w1, w2, w3, -⟩` from `w_facts hn`. Use extensionality with `i j`. Rewrite using `[Matrix.smul_apply]`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Rewrite using `[diagonal_apply_eq, Matrix.sub_apply, Matrix.sub_apply, hs, hs]`. Establish `e` using `w3 i`. Break down `w1 i with h | h | h` into its components or cases. Rewrite using `[w2 i i₀ (by omega), h0]; simp`.

Rewrite using `[w2 i.rev i (by omega), h]; simp`. Rewrite using `[← w2 i.rev i₀ (by omega), h]; simp`. Rewrite using `[ρ.diag i j h, diagonal_apply_ne _ h, smul_zero]`.
-/
private theorem z_diag (hF : F.Ok C₀) (hn : n = 2 ∨ n = 3) {K : Type} [CommRing K] (ρ : NRep F n K) {i₀ : Fin n}
    (h0 : w n i₀ = 1) : ρ.r F.g0 - ρ.r (F.star F.g0) =
      (ρ.r F.g0 - ρ.r (F.star F.g0)) i₀ i₀ • diagonal fun i => (w n i : K) := by
  obtain ⟨-, -, -, -, hs⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨w1, w2, w3, -⟩ := w_facts hn
  ext i j
  rw [Matrix.smul_apply]
  by_cases h : i = j
  · subst h
    rw [diagonal_apply_eq, Matrix.sub_apply, Matrix.sub_apply, hs, hs]
    have e := w3 i
    rcases w1 i with h | h | h
    · rw [w2 i i₀ (by omega), h0]; simp
    · rw [w2 i.rev i (by omega), h]; simp
    · rw [← w2 i.rev i₀ (by omega), h]; simp
  · rw [ρ.diag i j h, diagonal_apply_ne _ h, smul_zero]

end Mon

/- English proof (translation)
Introduce `l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ φ ht hψ`. Use `haveI : IsCO O φ.range := co_quot O C φ.range φ.rangeRestrict φ.rangeRestrict_surjective`. Generalize the expression as in `φ.range = A at *`. Take `⟨-, -, hΨ, -, -⟩` from `UpperTheory.V.Fr.star hF`. Take `⟨-, -, -, -, w5, i₀, h0⟩` from `w_facts hn`.

Establish `ht' : ∀ g, ∃ c, algebraMap A S.R c = (S.ρ.r g).trace` using `fun g => ⟨⟨_, ht g⟩, rfl⟩`. Establish `h2 : IsUnit (2 : A)`. Assume the negation of the conclusion as `h`. Establish `h3` using `(res_eq_zero_iff O A _).2 h`. Rewrite `h3` using `[map_ofNat]`.

Conclude with `hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1 ((CharP.cast_eq_zero_iff (ResidueField O) l 2).1 h3))`. Establish `hz` using `z_diag hF hn S.ρ h0`. Establish `hzm : S.ρ.r F.g0 - S.ρ.r (F.star F.g0) ∈ Submodule.span A (Set.range S.ρ.r)` using `sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)`. Establish `hζ : IsUnit ((S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀)`. Assume the negation of the conclusion as `h`.

Establish `h3` using `(res_eq_zero_iff O S.R _).2 h`. Establish `h4 : ∀ g, res O S.R (S.ρ.r g i₀ i₀) = (F.Ψ g : ResidueField O)` using `fun g => by`. Simplify `S.lift.2.1.1 g i₀` using `[h0]`. Rewrite `h3` using `[Matrix.sub_apply, map_sub, h4, h4, hΨ, sub_eq_zero]`. Use `hF.baseSubgroup_spec ?_` and prove the remaining obligations.

Rewrite using `[sq, mul_eq_one_iff_eq_inv]`. Conclude with `Units.ext h3`. Generalize the expression as in `(S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀ = ζ at hz hζ`. Rewrite `hzm` using `[hz]`. Establish `hζA : ζ ∈ A`.

Use `sqrt_mem A h2 hζ ?_` and prove the remaining obligations. Take `⟨c, hc⟩` from `trace_mem _ ht' (span_mul _ hzm hzm)`. Establish `h3 : ∑ i, (w n i : S.R) * w n i = 2`. Use `congrArg (Int.cast : ℤ → S.R) w5` as an intermediate fact. Simplify `this` using `[sq]`.

Rewrite `hc` using `[smul_mul_smul_comm, diagonal_mul_diagonal, trace_smul, trace_diagonal, h3, smul_eq_mul, mul_comm, ← sq]`. Conclude with `hc ▸ c.2`. Establish `hu : IsUnit (⟨ζ, hζA⟩ : A)`. Assume the negation of the conclusion as `h`. Conclude with `(mem_max A _).2 h hζ`.

Take `⟨u, hu⟩` from `hu.exists_left_inv`. Establish `hE` using `units_mem hn S.ρ.r h2 (by`. Use `Submodule.smul_mem _ u hzm` as an intermediate fact. Rewrite using `[Subalgebra.smul_def, smul_smul, show (u : S.R) * ζ = 1 from congrArg A.val hu, one_smul] at this)` and apply the resulting hypothesis. Establish `hadj : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ A`.

Use `Algebra.adjoin_le ?_` and prove the remaining obligations. Introduce and unpack `x (hx | ⟨v, i, g, rfl⟩)`. Take `⟨c, rfl⟩` from `mon_mem hF hn S.ρ ht' hE hx`. Conclude with `c.2`. Conclude with `hψ v i g`.

Introduce `x hx`. Use `closed A fun N => ?_` and prove the remaining obligations. Take `⟨y, hy, h⟩` from `hx N`. Conclude with `⟨y, hadj hy, h⟩`.
-/
theorem UpperTheory.V.Fr.B_gen :
    ∀ {l : ℕ} [Fact l.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsCoef l O] {F : Frame l (ResidueField O)} {C₀ : ℕ} {n : ℕ}, F.Ok C₀ → (n = 2 ∨ n = 3) → ∀ S : Space O F n, ∀ (C : Type) [CommRing C] [Algebra O C] [IsCO O C] (φ : C →ₐ[O] S.R), (∀ g, (S.ρ.r g).trace ∈ φ.range) → (∀ v i g, (S.ρ.ψ v i g : S.R) ∈ φ.range) → S.B ≤ φ.range := by
  intro l _ O _ _ _ _ F C₀ n hF hn S C _ _ _ φ ht hψ
  haveI : IsCO O φ.range := co_quot O C φ.range φ.rangeRestrict φ.rangeRestrict_surjective
  generalize φ.range = A at *
  obtain ⟨-, -, hΨ, -, -⟩ := UpperTheory.V.Fr.star hF
  obtain ⟨-, -, -, -, w5, i₀, h0⟩ := w_facts hn
  have ht' : ∀ g, ∃ c, algebraMap A S.R c = (S.ρ.r g).trace := fun g => ⟨⟨_, ht g⟩, rfl⟩
  have h2 : IsUnit (2 : A) := by
    by_contra h
    have h3 := (res_eq_zero_iff O A _).2 h
    rw [map_ofNat] at h3
    exact hF.l_odd ((Nat.prime_dvd_prime_iff_eq Fact.out Nat.prime_two).1
      ((CharP.cast_eq_zero_iff (ResidueField O) l 2).1 h3))
  have hz := z_diag hF hn S.ρ h0
  have hzm : S.ρ.r F.g0 - S.ρ.r (F.star F.g0) ∈ Submodule.span A (Set.range S.ρ.r) :=
    sub_mem (Submodule.subset_span ⟨_, rfl⟩) (Submodule.subset_span ⟨_, rfl⟩)
  have hζ : IsUnit ((S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀) := by
    by_contra h
    have h3 := (res_eq_zero_iff O S.R _).2 h
    have h4 : ∀ g, res O S.R (S.ρ.r g i₀ i₀) = (F.Ψ g : ResidueField O) := fun g => by
      simpa [h0] using S.lift.2.1.1 g i₀
    rw [Matrix.sub_apply, map_sub, h4, h4, hΨ, sub_eq_zero] at h3
    refine hF.baseSubgroup_spec ?_
    rw [sq, mul_eq_one_iff_eq_inv]
    exact Units.ext h3
  generalize (S.ρ.r F.g0 - S.ρ.r (F.star F.g0)) i₀ i₀ = ζ at hz hζ
  rw [hz] at hzm
  have hζA : ζ ∈ A := by
    refine sqrt_mem A h2 hζ ?_
    obtain ⟨c, hc⟩ := trace_mem _ ht' (span_mul _ hzm hzm)
    have h3 : ∑ i, (w n i : S.R) * w n i = 2 := by
      have := congrArg (Int.cast : ℤ → S.R) w5
      simpa [sq] using this
    rw [smul_mul_smul_comm, diagonal_mul_diagonal, trace_smul, trace_diagonal, h3, smul_eq_mul, mul_comm, ← sq] at hc
    exact hc ▸ c.2
  have hu : IsUnit (⟨ζ, hζA⟩ : A) := by
    by_contra h
    exact (mem_max A _).2 h hζ
  obtain ⟨u, hu⟩ := hu.exists_left_inv
  have hE := units_mem hn S.ρ.r h2 (by
    have := Submodule.smul_mem _ u hzm
    rwa [Subalgebra.smul_def, smul_smul, show (u : S.R) * ζ = 1 from congrArg A.val hu, one_smul] at this)
  have hadj : Algebra.adjoin O (S.ρ.mon 0 ∪ {x | ∃ v i g, x = (S.ρ.ψ v i g : S.R)}) ≤ A := by
    refine Algebra.adjoin_le ?_
    rintro x (hx | ⟨v, i, g, rfl⟩)
    · obtain ⟨c, rfl⟩ := mon_mem hF hn S.ρ ht' hE hx
      exact c.2
    · exact hψ v i g
  intro x hx
  refine closed A fun N => ?_
  obtain ⟨y, hy, h⟩ := hx N
  exact ⟨y, hadj hy, h⟩
