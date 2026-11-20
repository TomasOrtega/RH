import Development.EtaleCohomology.EtaleSheaves.LZIdemSumApprox

noncomputable section
open LateralTheory.E.StandardEtaleChartsIdempotentGluing Polynomial

namespace LateralTheory.E.LZIdemSumApproxYDDUPf

/- English proof (translation)
Use `Submodule.smul_induction_on (p := fun x => ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I ∧ p.2 ∈ N) ∧ x = (l.map (fun p => p.1 • p.2)).sum) hx ?_ ?_` and prove the remaining obligations. Introduce `a ha n hn`. Conclude with `⟨[(a, n)], by simp [ha, hn], by simp⟩`. Introduce and unpack `x y ⟨l1, h1, rfl⟩ ⟨l2, h2, rfl⟩`. Use `⟨l1 ++ l2, fun p hp => ?_, by simp⟩` and prove the remaining obligations.

Break down `List.mem_append.mp hp with h | h` into its components or cases. Conclude with `h1 p h`. Conclude with `h2 p h`.
-/
theorem smul_wit {R M : Type*} [CommRing R] [AddCommGroup M] [Module R M] (I : Ideal R) (N : Submodule R M)
    {x : M} (hx : x ∈ I • N) :
    ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I ∧ p.2 ∈ N) ∧ x = (l.map (fun p => p.1 • p.2)).sum := by
  refine Submodule.smul_induction_on (p := fun x => ∃ l : List (R × M), (∀ p ∈ l, p.1 ∈ I ∧ p.2 ∈ N) ∧
    x = (l.map (fun p => p.1 • p.2)).sum) hx ?_ ?_
  · intro a ha n hn
    exact ⟨[(a, n)], by simp [ha, hn], by simp⟩
  · rintro x y ⟨l1, h1, rfl⟩ ⟨l2, h2, rfl⟩
    refine ⟨l1 ++ l2, fun p hp => ?_, by simp⟩
    rcases List.mem_append.mp hp with h | h
    · exact h1 p h
    · exact h2 p h

/- English proof (translation)
Set `A₀` to `Subring.closure S`. Establish `: IsNoetherianRing A₀` using `is_noetherian_subring_closure S hS`. Set `g : A₀ →+* A` to `A₀.subtype`. Set `P₀ : Ideal A₀` to `(IsLocalRing.maximalIdeal A).comap g`. Establish `: P₀.IsPrime` using `Ideal.comap_isPrime _ _`.

Set `A'` to `Localization.AtPrime P₀`. Establish `: IsNoetherianRing A'` using `IsLocalization.isNoetherianRing P₀.primeCompl A' inferInstance`. Establish `hu : ∀ y : P₀.primeCompl, IsUnit (g y)`. Introduce `y`. Assume the negation of the conclusion as `h`.

Conclude with `y.2 (show (y : A₀) ∈ P₀ from h)`. Set `φ : A' →+* A` to `IsLocalization.lift (M := P₀.primeCompl) hu`. Use `⟨A', inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩` and prove the remaining obligations. Introduce `a ha`. Use `⟨algebraMap A₀ A' ⟨a, Subring.subset_closure ha⟩, IsLocalization.lift_eq _ _, fun hm => ?_⟩` and prove the remaining obligations.

Rewrite using `[IsLocalization.AtPrime.to_map_mem_maximal_iff A' P₀]`. Conclude with `hm`. Introduce `a' ha'`. Take `⟨x, s, rfl⟩` from `IsLocalization.mk'_surjective P₀.primeCompl a'`. Rewrite `ha'` using `[IsLocalization.AtPrime.mk'_mem_maximal_iff A' P₀]`.

Simplify using `only [φ, IsLocalization.lift_mk']`. Conclude with `Ideal.mul_mem_right _ _ ha'`.
-/
theorem approx_base {A : Type} [CommRing A] [IsLocalRing A] (S : Set A) (hS : S.Finite) :
    ∃ (A' : Type) (_ : CommRing A') (_ : IsLocalRing A') (_ : IsNoetherianRing A') (φ : A' →+* A),
    (∀ a ∈ S, ∃ a', φ a' = a ∧ (a ∈ IsLocalRing.maximalIdeal A → a' ∈ IsLocalRing.maximalIdeal A')) ∧
    (∀ a' ∈ IsLocalRing.maximalIdeal A', φ a' ∈ IsLocalRing.maximalIdeal A) := by
  let A₀ := Subring.closure S
  have : IsNoetherianRing A₀ := is_noetherian_subring_closure S hS
  let g : A₀ →+* A := A₀.subtype
  let P₀ : Ideal A₀ := (IsLocalRing.maximalIdeal A).comap g
  have : P₀.IsPrime := Ideal.comap_isPrime _ _
  let A' := Localization.AtPrime P₀
  have : IsNoetherianRing A' := IsLocalization.isNoetherianRing P₀.primeCompl A' inferInstance
  have hu : ∀ y : P₀.primeCompl, IsUnit (g y) := by
    intro y
    by_contra h
    exact y.2 (show (y : A₀) ∈ P₀ from h)
  let φ : A' →+* A := IsLocalization.lift (M := P₀.primeCompl) hu
  refine ⟨A', inferInstance, inferInstance, inferInstance, φ, ?_, ?_⟩
  · intro a ha
    refine ⟨algebraMap A₀ A' ⟨a, Subring.subset_closure ha⟩, IsLocalization.lift_eq _ _, fun hm => ?_⟩
    rw [IsLocalization.AtPrime.to_map_mem_maximal_iff A' P₀]
    exact hm
  · intro a' ha'
    obtain ⟨x, s, rfl⟩ := IsLocalization.mk'_surjective P₀.primeCompl a'
    rw [IsLocalization.AtPrime.mk'_mem_maximal_iff A' P₀] at ha'
    simp only [φ, IsLocalization.lift_mk']
    exact Ideal.mul_mem_right _ _ ha'

section Tools
variable {A K : Type} [CommRing A] [Field K] [Algebra A K]

/- English proof (translation)
Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Break down `hx with hx | hx` into its components or cases. Conclude with `⟨x, hx, 0, by simp⟩`. Rewrite using `[Set.mem_singleton_iff.mp hx]; exact ⟨1, S.one_mem, 1, by simp⟩`.

Consider the case `algebraMap r => exact ⟨algebraMap A K r, S.algebraMap_mem r, 0, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨b1, hb1, n1, rfl⟩` from `hx`. Take `⟨b2, hb2, n2, rfl⟩` from `hy`. Use `⟨b1 * u⁻¹ ^ n2 + b2 * u⁻¹ ^ n1, S.add_mem (S.mul_mem hb1 (S.pow_mem hinv _)) (S.mul_mem hb2 (S.pow_mem hinv _)), n1 + n2, ?_⟩` and prove the remaining obligations.

Rewrite using `[inv_pow, inv_pow, pow_add]`. Clear the denominators using the available nonvanishing facts. Consider the case `mul x y _ _ hx hy`. Take `⟨b1, hb1, n1, rfl⟩` from `hx`. Take `⟨b2, hb2, n2, rfl⟩` from `hy`.

Conclude with `⟨b1 * b2, S.mul_mem hb1 hb2, n1 + n2, by rw [pow_add]; ring⟩`.
-/
theorem adj_nf (S : Subalgebra A K) (u : K) (hu : u ≠ 0) (hinv : u⁻¹ ∈ S) {x : K}
    (hx : x ∈ Algebra.adjoin A ((S : Set K) ∪ {u})) : ∃ s ∈ S, ∃ n : ℕ, x = s * u ^ n := by
  induction hx using Algebra.adjoin_induction with
  | mem x hx =>
    rcases hx with hx | hx
    · exact ⟨x, hx, 0, by simp⟩
    · rw [Set.mem_singleton_iff.mp hx]; exact ⟨1, S.one_mem, 1, by simp⟩
  | algebraMap r => exact ⟨algebraMap A K r, S.algebraMap_mem r, 0, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨b1, hb1, n1, rfl⟩ := hx
    obtain ⟨b2, hb2, n2, rfl⟩ := hy
    refine ⟨b1 * u⁻¹ ^ n2 + b2 * u⁻¹ ^ n1,
      S.add_mem (S.mul_mem hb1 (S.pow_mem hinv _)) (S.mul_mem hb2 (S.pow_mem hinv _)), n1 + n2, ?_⟩
    rw [inv_pow, inv_pow, pow_add]; field_simp
  | mul x y _ _ hx hy =>
    obtain ⟨b1, hb1, n1, rfl⟩ := hx
    obtain ⟨b2, hb2, n2, rfl⟩ := hy
    exact ⟨b1 * b2, S.mul_mem hb1 hb2, n1 + n2, by rw [pow_add]; ring⟩

/- English proof (translation)
Rewrite using `[aeval_eq_sum_range]`. Use `Subalgebra.sum_mem _ fun n _ => ?_` and prove the remaining obligations. Take `⟨a', ha'⟩` from `hq n`. Establish `e : algebraMap A K (q.coeff n) = algebraMap A' K a'` using `by rw [h, RingHom.comp_apply, ha']`. Rewrite using `[Algebra.smul_def, e]`.

Conclude with `Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _) (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton t)) _)`.
-/
theorem aeval_mem {A' : Type} [CommRing A'] [Algebra A' K] (φ : A' →+* A)
    (h : algebraMap A' K = (algebraMap A K).comp φ) (t : K) (q : A[X])
    (hq : ∀ n, q.coeff n ∈ Set.range φ) : aeval t q ∈ Algebra.adjoin A' {t} := by
  rw [aeval_eq_sum_range]
  refine Subalgebra.sum_mem _ fun n _ => ?_
  obtain ⟨a', ha'⟩ := hq n
  have e : algebraMap A K (q.coeff n) = algebraMap A' K a' := by rw [h, RingHom.comp_apply, ha']
  rw [Algebra.smul_def, e]
  exact Subalgebra.mul_mem _ (Subalgebra.algebraMap_mem _ _)
    (Subalgebra.pow_mem _ (Algebra.subset_adjoin (Set.mem_singleton t)) _)

/- English proof (translation)
Take `⟨p, hm, hp⟩` from `hx`. Establish `hq : ∀ n, ∃ q : A[X], aeval t q = (p.coeff n : K)`. Introduce `n`. Establish `: (p.coeff n : K) ∈ (aeval t : A[X] →ₐ[A] K).range`. Rewrite using `[← Algebra.adjoin_singleton_eq_range_aeval]`.

Conclude with `(p.coeff n).2`. Take `⟨q, hq⟩` from `this`. Conclude with `⟨q, hq⟩`. Use `choose q hq using hq`. Use `⟨⋃ n ∈ Finset.range (p.natDegree + 1), ((q n).coeffs : Set A), Set.Finite.biUnion (Finset.finite_toSet _) (fun _ _ => Finset.finite_toSet _), ?_⟩` and prove the remaining obligations.

Introduce `A' _ _ φ h hT`. Set `P : K[X]` to `p.map (algebraMap (Algebra.adjoin A {t}) K)`. Establish `hPl : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin A' {t}) K)`. Rewrite using `[Polynomial.lifts_iff_coeff_lifts]`. Introduce `n`.

Rewrite using `[Polynomial.coeff_map]`. Use `show (p.coeff n : K) ∈ Set.range (algebraMap (Algebra.adjoin A' {t}) K)`. Establish `hmem : (p.coeff n : K) ∈ Algebra.adjoin A' {t}`. Distinguish the cases in `hn : n ≤ p.natDegree`. Rewrite using `[← hq n]`.

Use `aeval_mem φ h t (q n) fun k => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (q n).coeff k = 0`. Conclude with `⟨0, by rw [hk, map_zero]⟩`. Conclude with `hT (Set.mem_biUnion (x := n) (by simp; omega) (Polynomial.coeff_mem_coeffs hk))`. Rewrite using `[Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]`.

Simplify using the standard rewrite rules. Conclude with `⟨⟨_, hmem⟩, rfl⟩`. Take `⟨q', hq'map, -, hq'm⟩` from `Polynomial.lifts_and_natDegree_eq_and_monic hPl (hm.map _)`. Use `⟨q', hq'm, ?_⟩` and prove the remaining obligations. Rewrite using `[← Polynomial.eval_map, hq'map, Polynomial.eval_map]`.

Conclude with `hp`.
-/
theorem int_wit (t x : K) (hx : IsIntegral (Algebra.adjoin A {t}) x) :
    ∃ T : Set A, T.Finite ∧ ∀ (A' : Type) [CommRing A'] [Algebra A' K] (φ : A' →+* A),
      algebraMap A' K = (algebraMap A K).comp φ → T ⊆ Set.range φ →
      IsIntegral (Algebra.adjoin A' {t}) x := by
  obtain ⟨p, hm, hp⟩ := hx
  have hq : ∀ n, ∃ q : A[X], aeval t q = (p.coeff n : K) := by
    intro n
    have : (p.coeff n : K) ∈ (aeval t : A[X] →ₐ[A] K).range := by
      rw [← Algebra.adjoin_singleton_eq_range_aeval]; exact (p.coeff n).2
    obtain ⟨q, hq⟩ := this
    exact ⟨q, hq⟩
  choose q hq using hq
  refine ⟨⋃ n ∈ Finset.range (p.natDegree + 1), ((q n).coeffs : Set A),
    Set.Finite.biUnion (Finset.finite_toSet _) (fun _ _ => Finset.finite_toSet _), ?_⟩
  intro A' _ _ φ h hT
  let P : K[X] := p.map (algebraMap (Algebra.adjoin A {t}) K)
  have hPl : P ∈ Polynomial.lifts (algebraMap (Algebra.adjoin A' {t}) K) := by
    rw [Polynomial.lifts_iff_coeff_lifts]
    intro n
    rw [Polynomial.coeff_map]
    show (p.coeff n : K) ∈ Set.range (algebraMap (Algebra.adjoin A' {t}) K)
    have hmem : (p.coeff n : K) ∈ Algebra.adjoin A' {t} := by
      by_cases hn : n ≤ p.natDegree
      · rw [← hq n]
        refine aeval_mem φ h t (q n) fun k => ?_
        by_cases hk : (q n).coeff k = 0
        · exact ⟨0, by rw [hk, map_zero]⟩
        · exact hT (Set.mem_biUnion (x := n) (by simp; omega) (Polynomial.coeff_mem_coeffs hk))
      · rw [Polynomial.coeff_eq_zero_of_natDegree_lt (by omega)]
        simp
    exact ⟨⟨_, hmem⟩, rfl⟩
  obtain ⟨q', hq'map, -, hq'm⟩ := Polynomial.lifts_and_natDegree_eq_and_monic hPl (hm.map _)
  refine ⟨q', hq'm, ?_⟩
  rw [← Polynomial.eval_map, hq'map, Polynomial.eval_map]
  exact hp

end Tools

section Transfer
variable {A K : Type} [CommRing A] [IsLocalRing A] [Field K] [Algebra A K]
variable {A' : Type} [CommRing A'] [Algebra A' K] (φ : A' →+* A) (h : algebraMap A' K = (algebraMap A K).comp φ)
include h

/- English proof (translation)
Introduce `x hx`. Proceed by induction on `hx using Algebra.adjoin_induction with`. Consider the case `mem x hx => exact hs hx`. Consider the case `algebraMap r => rw [h, RingHom.comp_apply]`. Conclude with `S.algebraMap_mem _`.

Consider the case `add x y _ _ h1 h2 => exact S.add_mem h1 h2`. Consider the case `mul x y _ _ h1 h2 => exact S.mul_mem h1 h2`.
-/
theorem adj_sub (S : Subalgebra A K) (s : Set K) (hs : s ⊆ S) : ∀ x ∈ Algebra.adjoin A' s, x ∈ S := by
  intro x hx
  induction hx using Algebra.adjoin_induction with
  | mem x hx => exact hs hx
  | algebraMap r => rw [h, RingHom.comp_apply]; exact S.algebraMap_mem _
  | add x y _ _ h1 h2 => exact S.add_mem h1 h2
  | mul x y _ _ h1 h2 => exact S.mul_mem h1 h2

/- English proof (translation)
Introduce `x hx`. Establish `hx' : x ∈ IsLocalRing.maximalIdeal A' • Subalgebra.toSubmodule B'` using `hx`. Use `show x ∈ IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule B`. Use `Submodule.smul_induction_on hx' ?_ ?_` and prove the remaining obligations. Introduce `a ha n hn`.

Establish `e : (a • n : K) = (φ a) • n` using `by simp only [Algebra.smul_def, h, RingHom.comp_apply]`. Rewrite using `[e]`. Conclude with `Submodule.smul_mem_smul (hmax a ha) (hsub n hn)`. Introduce `x y hx hy`. Conclude with `add_mem hx hy`.
-/
theorem mS_sub [IsLocalRing A']
    (hmax : ∀ a' ∈ IsLocalRing.maximalIdeal A', φ a' ∈ IsLocalRing.maximalIdeal A)
    (B' : Subalgebra A' K) (B : Subalgebra A K) (hsub : ∀ x ∈ B', x ∈ B) : ∀ x ∈ mS B', x ∈ mS B := by
  intro x hx
  have hx' : x ∈ IsLocalRing.maximalIdeal A' • Subalgebra.toSubmodule B' := hx
  show x ∈ IsLocalRing.maximalIdeal A • Subalgebra.toSubmodule B
  refine Submodule.smul_induction_on hx' ?_ ?_
  · intro a ha n hn
    have e : (a • n : K) = (φ a) • n := by simp only [Algebra.smul_def, h, RingHom.comp_apply]
    rw [e]
    exact Submodule.smul_mem_smul (hmax a ha) (hsub n hn)
  · intro x y hx hy
    exact add_mem hx hy

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons p l ih`. Simplify using `only [List.map_cons, List.sum_cons]`. Use `add_mem ?_ (ih (fun q hq => h1 q (by simp [hq])) (fun q hq => h2 q (by simp [hq])))` and prove the remaining obligations.

Take `⟨a', ha', hp⟩` from `h1 p (by simp)`. Establish `e : (φ a' • p.2 : K) = a' • p.2` using `by simp only [Algebra.smul_def, h, RingHom.comp_apply]`. Rewrite using `[← hp, e]`. Conclude with `Submodule.smul_mem_smul ha' (h2 p (by simp))`.
-/
theorem list_mem [IsLocalRing A'] (l : List (A × K)) (N : Submodule A' K)
    (h1 : ∀ p ∈ l, ∃ a' ∈ IsLocalRing.maximalIdeal A', φ a' = p.1) (h2 : ∀ p ∈ l, p.2 ∈ N) :
    (l.map fun p => p.1 • p.2).sum ∈ IsLocalRing.maximalIdeal A' • N := by
  induction l with
  | nil => simp
  | cons p l ih =>
    simp only [List.map_cons, List.sum_cons]
    refine add_mem ?_ (ih (fun q hq => h1 q (by simp [hq])) (fun q hq => h2 q (by simp [hq])))
    obtain ⟨a', ha', hp⟩ := h1 p (by simp)
    have e : (φ a' • p.2 : K) = a' • p.2 := by simp only [Algebra.smul_def, h, RingHom.comp_apply]
    rw [← hp, e]
    exact Submodule.smul_mem_smul ha' (h2 p (by simp))

end Transfer

/- English proof (translation)
Introduce `x hx`. Establish `: Algebra.adjoin A' s ≤ (integralClosure R K).restrictScalars A'` using `Algebra.adjoin_le (fun y hy => (mem_integralClosure_iff _ _).mpr (hs y hy))`. Conclude with `(mem_integralClosure_iff _ _).mp (this hx)`.
-/
theorem int_adj {A' K : Type} [CommRing A'] [Field K] [Algebra A' K] (R : Subalgebra A' K) (s : Set K)
    (hs : ∀ x ∈ s, IsIntegral R x) : ∀ x ∈ Algebra.adjoin A' s, IsIntegral R x := by
  intro x hx
  have : Algebra.adjoin A' s ≤ (integralClosure R K).restrictScalars A' :=
    Algebra.adjoin_le (fun y hy => (mem_integralClosure_iff _ _).mpr (hs y hy))
  exact (mem_integralClosure_iff _ _).mp (this hx)

open Classical in
/- English proof (translation)
Introduce `hN A _ _ K _ _ B C t hc e f hp`. Take `⟨heB, hfC, hee, hff, hef⟩` from `hp`. Establish `ht0 : t ≠ 0` using `hc.ne`. Take `⟨l1, hl1, hs1⟩` from `smul_wit _ _ hee`. Take `⟨l2, hl2, hs2⟩` from `smul_wit _ _ hff`.

Take `⟨l3, hl3, hs3⟩` from `smul_wit _ _ hef`. Establish `hDB : ∀ d : K, ∃ b : K, ∃ n : ℕ, d ∈ AdjoinInv B t → b ∈ B ∧ d = b * t⁻¹ ^ n`. Introduce `d`. Distinguish the cases in `hd : d ∈ AdjoinInv B t`. Take `⟨b, hb, n, hbn⟩` from `adj_nf B t⁻¹ (inv_ne_zero ht0) (by rw [inv_inv]; exact hc.tB) hd`.

Conclude with `⟨b, n, fun _ => ⟨hb, hbn⟩⟩`. Conclude with `⟨0, 0, fun h' => absurd h' hd⟩`. Use `choose nb nn hnb using hDB`. Establish `hDC : ∀ d : K, ∃ c : K, ∃ n : ℕ, d ∈ AdjoinInv B t → c ∈ C ∧ d = c * t ^ n`. Introduce `d`.

Distinguish the cases in `hd : d ∈ AdjoinInv B t`. Rewrite `hd` using `[hc.glue]`. Take `⟨c, hc', n, hcn⟩` from `adj_nf C t ht0 hc.tC hd`. Conclude with `⟨c, n, fun _ => ⟨hc', hcn⟩⟩`. Conclude with `⟨0, 0, fun h' => absurd h' hd⟩`.

Use `choose nc mc hnc using hDC`. Establish `hBD : ∀ b ∈ B, b ∈ AdjoinInv B t` using `fun b hb => Algebra.subset_adjoin (Or.inl hb)`. Establish `hCD : ∀ c ∈ C, c ∈ AdjoinInv B t` using `fun c hc' => by`. Rewrite using `[hc.glue]`. Conclude with `Algebra.subset_adjoin (Or.inl hc')`.

Set `Bc : List K` to `e :: (l1.map Prod.snd ++ l3.map (fun p => nb p.2))`. Set `Cc : List K` to `f :: l2.map Prod.snd`. Set `LB : List K` to `t :: (Bc ++ Cc.map nb)`. Set `LC : List K` to `t⁻¹ :: (Cc ++ Bc.map nc)`. Establish `hBc : ∀ x ∈ Bc, x ∈ B`.

Introduce `x hx`. Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases. Conclude with `heB`. Break down `List.mem_append.mp hx with hx | hx` into its components or cases. Take `⟨p, hp, rfl⟩` from `List.mem_map.mp hx`.

Conclude with `(hl1 p hp).2`. Take `⟨p, hp, rfl⟩` from `List.mem_map.mp hx`. Conclude with `(hnb p.2 (hl3 p hp).2).1`. Establish `hCc : ∀ x ∈ Cc, x ∈ C`. Introduce `x hx`.

Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases. Conclude with `hfC`. Take `⟨p, hp, rfl⟩` from `List.mem_map.mp hx`. Conclude with `(hl2 p hp).2`. Establish `hLB : ∀ x ∈ LB, x ∈ B`.

Introduce `x hx`. Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases. Conclude with `hc.tB`. Break down `List.mem_append.mp hx with hx | hx` into its components or cases. Conclude with `hBc x hx`.

Take `⟨c, hcm, rfl⟩` from `List.mem_map.mp hx`. Conclude with `(hnb c (hCD c (hCc c hcm))).1`. Establish `hLC : ∀ x ∈ LC, x ∈ C`. Introduce `x hx`. Break down `List.mem_cons.mp hx with rfl | hx` into its components or cases.

Conclude with `hc.tC`. Break down `List.mem_append.mp hx with hx | hx` into its components or cases. Conclude with `hCc x hx`. Take `⟨b, hbm, rfl⟩` from `List.mem_map.mp hx`. Conclude with `(hnc b (hBD b (hBc b hbm))).1`.

Establish `hIB : ∀ s : K, ∃ T : Set A, T.Finite ∧ (s ∈ B → ∀ (A' : Type) [CommRing A'] [Algebra A' K] (φ : A' →+* A), algebraMap A' K = (algebraMap A K).comp φ → T ⊆ Set.range φ → IsIntegral (Algebra.adjoin A' {t}) s)`. Introduce `s`. Distinguish the cases in `hs : s ∈ B`. Take `⟨T, hT, hT'⟩` from `int_wit t s (hc.intB s hs)`. Conclude with `⟨T, hT, fun _ => hT'⟩`.

Conclude with `⟨∅, Set.finite_empty, fun h' => absurd h' hs⟩`. Use `choose TB hTBf hTB using hIB`. Establish `hIC : ∀ s : K, ∃ T : Set A, T.Finite ∧ (s ∈ C → ∀ (A' : Type) [CommRing A'] [Algebra A' K] (φ : A' →+* A), algebraMap A' K = (algebraMap A K).comp φ → T ⊆ Set.range φ → IsIntegral (Algebra.adjoin A' {t⁻¹}) s)`. Introduce `s`. Distinguish the cases in `hs : s ∈ C`.

Take `⟨T, hT, hT'⟩` from `int_wit t⁻¹ s (hc.intC s hs)`. Conclude with `⟨T, hT, fun _ => hT'⟩`. Conclude with `⟨∅, Set.finite_empty, fun h' => absurd h' hs⟩`. Use `choose TC hTCf hTC using hIC`. Set `TA : Set A` to `((⋃ s ∈ {x | x ∈ LB}, TB s) ∪ (⋃ s ∈ {x | x ∈ LC}, TC s)) ∪ {a | a ∈ (l1 ++ l2 ++ l3).map Prod.fst}`.

Establish `hTA : TA.Finite`. Use `Set.Finite.union (Set.Finite.union ?_ ?_) (List.finite_toSet _)` and prove the remaining obligations. Conclude with `Set.Finite.biUnion (List.finite_toSet _) (fun s _ => hTBf s)`. Conclude with `Set.Finite.biUnion (List.finite_toSet _) (fun s _ => hTCf s)`. Take `⟨A', _, _, _, φ, hlift, hmax⟩` from `approx_base TA hTA`.

Use `letI : Algebra A' K := ((algebraMap A K).comp φ).toAlgebra`. Establish `hφ : algebraMap A' K = (algebraMap A K).comp φ` using `rfl`. Establish `sa : ∀ {s : Set K} {x : K}, x ∈ s → x ∈ Algebra.adjoin A' s` using `fun h => Algebra.subset_adjoin h`. Establish `hrange : TA ⊆ Set.range φ` using `fun a ha => by`. Take `⟨a', h1, _⟩` from `hlift a ha`.

Conclude with `⟨a', h1⟩`. Establish `hcoef : ∀ p ∈ l1 ++ l2 ++ l3, p.1 ∈ IsLocalRing.maximalIdeal A → ∃ a' ∈ IsLocalRing.maximalIdeal A', φ a' = p.1`. Introduce `p hp hm`. Take `⟨a', h1, h2⟩` from `hlift p.1 (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))`. Conclude with `⟨a', h2 hm, h1⟩`.

Set `B' : Subalgebra A' K` to `Algebra.adjoin A' (LB.toFinset : Set K)`. Set `C' : Subalgebra A' K` to `Algebra.adjoin A' (LC.toFinset : Set K)`. Establish `memB' : ∀ x ∈ LB, x ∈ B'` using `fun x hx => Algebra.subset_adjoin (by simpa using hx)`. Establish `memC' : ∀ x ∈ LC, x ∈ C'` using `fun x hx => Algebra.subset_adjoin (by simpa using hx)`. Establish `hB'B : ∀ x ∈ B', x ∈ B` using `adj_sub φ hφ B _ (fun x hx => hLB x (by simpa using hx))`.

Establish `hC'C : ∀ x ∈ C', x ∈ C` using `adj_sub φ hφ C _ (fun x hx => hLC x (by simpa using hx))`. Establish `hchart : Charts B' C' t`. Use `⟨ht0, memB' t (List.mem_cons.mpr (Or.inl rfl)), memC' t⁻¹ (List.mem_cons.mpr (Or.inl rfl)), ?_, ?_, ?_⟩` and prove the remaining obligations. Use `int_adj _ _ (fun s hs => ?_)` and prove the remaining obligations. Establish `hs' : s ∈ LB` using `by simpa using hs`.

Conclude with `hTB s (hLB s hs') A' φ hφ (fun a ha => hrange (Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨s, hs', ha⟩))))`. Use `int_adj _ _ (fun s hs => ?_)` and prove the remaining obligations. Establish `hs' : s ∈ LC` using `by simpa using hs`. Conclude with `hTC s (hLC s hs') A' φ hφ (fun a ha => hrange (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨s, hs', ha⟩))))`. Use `show Algebra.adjoin A' ((B' : Set K) ∪ {t⁻¹}) = Algebra.adjoin A' ((C' : Set K) ∪ {t})`.

Apply `le_antisymm` to reduce the goal to its premises. Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `x (hx | hx)`. Use `(Algebra.adjoin_le ?_ : B' ≤ _) hx` and prove the remaining obligations. Introduce `y hy`.

Establish `hy' : y ∈ LB` using `by simpa using hy`. Break down `List.mem_cons.mp hy' with rfl | hy'` into its components or cases. Conclude with `sa (Or.inr rfl)`. Break down `List.mem_append.mp hy' with hy' | hy'` into its components or cases. Take `⟨_, h2⟩` from `hnc y (hBD y (hBc y hy'))`.

Rewrite using `[h2]`. Conclude with `mul_mem (sa (Or.inl (memC' _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨y, hy', rfl⟩)))))))) (pow_mem (sa (Or.inr rfl)) _)`. Take `⟨c, hcm, rfl⟩` from `List.mem_map.mp hy'`. Take `⟨_, h2⟩` from `hnb c (hCD c (hCc c hcm))`. Establish `key : c * t ^ nn c = nb c`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← key]`. Conclude with `mul_mem (sa (Or.inl (memC' _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hcm))))))) (pow_mem (sa (Or.inr rfl)) _)`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `sa (Or.inl (memC' _ (List.mem_cons.mpr (Or.inl rfl))))`.

Apply `Algebra.adjoin_le` to reduce the goal to its premises. Introduce and unpack `x (hx | hx)`. Use `(Algebra.adjoin_le ?_ : C' ≤ _) hx` and prove the remaining obligations. Introduce `y hy`. Establish `hy' : y ∈ LC` using `by simpa using hy`.

Break down `List.mem_cons.mp hy' with rfl | hy'` into its components or cases. Conclude with `sa (Or.inr rfl)`. Break down `List.mem_append.mp hy' with hy' | hy'` into its components or cases. Take `⟨_, h2⟩` from `hnb y (hCD y (hCc y hy'))`. Rewrite using `[h2]`.

Conclude with `mul_mem (sa (Or.inl (memB' _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨y, hy', rfl⟩)))))))) (pow_mem (sa (Or.inr rfl)) _)`. Take `⟨b, hbm, rfl⟩` from `List.mem_map.mp hy'`. Take `⟨_, h2⟩` from `hnc b (hBD b (hBc b hbm))`. Establish `key : b * t⁻¹ ^ mc b = nc b`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← key]`. Conclude with `mul_mem (sa (Or.inl (memB' _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hbm))))))) (pow_mem (sa (Or.inr rfl)) _)`. Rewrite using `[Set.mem_singleton_iff.mp hx]`. Conclude with `sa (Or.inl (memB' _ (List.mem_cons.mpr (Or.inl rfl))))`. Establish `inBc : ∀ x ∈ Bc, x ∈ LB` using `fun x hx => List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hx)))`.

Establish `inCc : ∀ x ∈ Cc, x ∈ LC` using `fun x hx => List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hx)))`. Establish `hpair : IdemPair B' C' t e f`. Use `⟨memB' e (inBc e (List.mem_cons.mpr (Or.inl rfl))), memC' f (inCc f (List.mem_cons.mpr (Or.inl rfl))), ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hs1]`. Conclude with `list_mem φ hφ l1 (Subalgebra.toSubmodule B') (fun p hp => hcoef p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp)))) (hl1 p hp).1) (fun p hp => memB' _ (inBc _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩)))))))`.

Rewrite using `[hs2]`. Conclude with `list_mem φ hφ l2 (Subalgebra.toSubmodule C') (fun p hp => hcoef p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp)))) (hl2 p hp).1) (fun p hp => memC' _ (inCc _ (List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))))`. Rewrite using `[hs3]`. Use `list_mem φ hφ l3 (Subalgebra.toSubmodule (AdjoinInv B' t)) (fun p hp => hcoef p (List.mem_append.mpr (Or.inr hp)) (hl3 p hp).1) (fun p hp => ?_)` and prove the remaining obligations. Use `show p.2 ∈ AdjoinInv B' t`.

Rewrite using `[(hnb p.2 (hl3 p hp).2).2]`. Conclude with `mul_mem (sa (Or.inl (memB' _ (inBc _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))))))))) (pow_mem (sa (Or.inr rfl)) _)`. Establish `hres` using `hN A' K B' C' t hchart (Subalgebra.fg_adjoin_finset _) (Subalgebra.fg_adjoin_finset _) e f hpair`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.mp hres`. Rewrite using `[← hyz]`.

Conclude with `Submodule.add_mem_sup (mS_sub φ hφ hmax B' B hB'B y hy) (mS_sub φ hφ hmax C' C hC'C z hz)`.
-/
theorem LZIdemSumApprox_of : LateralTheory.E.IdempotentLiftingAlt.LZIdemSumApprox := by
  intro hN A _ _ K _ _ B C t hc e f hp
  obtain ⟨heB, hfC, hee, hff, hef⟩ := hp
  have ht0 : t ≠ 0 := hc.ne
  obtain ⟨l1, hl1, hs1⟩ := smul_wit _ _ hee
  obtain ⟨l2, hl2, hs2⟩ := smul_wit _ _ hff
  obtain ⟨l3, hl3, hs3⟩ := smul_wit _ _ hef
  have hDB : ∀ d : K, ∃ b : K, ∃ n : ℕ, d ∈ AdjoinInv B t → b ∈ B ∧ d = b * t⁻¹ ^ n := by
    intro d
    by_cases hd : d ∈ AdjoinInv B t
    · obtain ⟨b, hb, n, hbn⟩ := adj_nf B t⁻¹ (inv_ne_zero ht0) (by rw [inv_inv]; exact hc.tB) hd
      exact ⟨b, n, fun _ => ⟨hb, hbn⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' hd⟩
  choose nb nn hnb using hDB
  have hDC : ∀ d : K, ∃ c : K, ∃ n : ℕ, d ∈ AdjoinInv B t → c ∈ C ∧ d = c * t ^ n := by
    intro d
    by_cases hd : d ∈ AdjoinInv B t
    · rw [hc.glue] at hd
      obtain ⟨c, hc', n, hcn⟩ := adj_nf C t ht0 hc.tC hd
      exact ⟨c, n, fun _ => ⟨hc', hcn⟩⟩
    · exact ⟨0, 0, fun h' => absurd h' hd⟩
  choose nc mc hnc using hDC
  have hBD : ∀ b ∈ B, b ∈ AdjoinInv B t := fun b hb => Algebra.subset_adjoin (Or.inl hb)
  have hCD : ∀ c ∈ C, c ∈ AdjoinInv B t := fun c hc' => by
    rw [hc.glue]; exact Algebra.subset_adjoin (Or.inl hc')
  let Bc : List K := e :: (l1.map Prod.snd ++ l3.map (fun p => nb p.2))
  let Cc : List K := f :: l2.map Prod.snd
  let LB : List K := t :: (Bc ++ Cc.map nb)
  let LC : List K := t⁻¹ :: (Cc ++ Bc.map nc)
  have hBc : ∀ x ∈ Bc, x ∈ B := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact heB
    rcases List.mem_append.mp hx with hx | hx
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact (hl1 p hp).2
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact (hnb p.2 (hl3 p hp).2).1
  have hCc : ∀ x ∈ Cc, x ∈ C := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hfC
    · obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hx
      exact (hl2 p hp).2
  have hLB : ∀ x ∈ LB, x ∈ B := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc.tB
    rcases List.mem_append.mp hx with hx | hx
    · exact hBc x hx
    · obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hx
      exact (hnb c (hCD c (hCc c hcm))).1
  have hLC : ∀ x ∈ LC, x ∈ C := by
    intro x hx
    rcases List.mem_cons.mp hx with rfl | hx
    · exact hc.tC
    rcases List.mem_append.mp hx with hx | hx
    · exact hCc x hx
    · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hx
      exact (hnc b (hBD b (hBc b hbm))).1
  have hIB : ∀ s : K, ∃ T : Set A, T.Finite ∧ (s ∈ B → ∀ (A' : Type) [CommRing A'] [Algebra A' K]
      (φ : A' →+* A), algebraMap A' K = (algebraMap A K).comp φ → T ⊆ Set.range φ →
      IsIntegral (Algebra.adjoin A' {t}) s) := by
    intro s
    by_cases hs : s ∈ B
    · obtain ⟨T, hT, hT'⟩ := int_wit t s (hc.intB s hs)
      exact ⟨T, hT, fun _ => hT'⟩
    · exact ⟨∅, Set.finite_empty, fun h' => absurd h' hs⟩
  choose TB hTBf hTB using hIB
  have hIC : ∀ s : K, ∃ T : Set A, T.Finite ∧ (s ∈ C → ∀ (A' : Type) [CommRing A'] [Algebra A' K]
      (φ : A' →+* A), algebraMap A' K = (algebraMap A K).comp φ → T ⊆ Set.range φ →
      IsIntegral (Algebra.adjoin A' {t⁻¹}) s) := by
    intro s
    by_cases hs : s ∈ C
    · obtain ⟨T, hT, hT'⟩ := int_wit t⁻¹ s (hc.intC s hs)
      exact ⟨T, hT, fun _ => hT'⟩
    · exact ⟨∅, Set.finite_empty, fun h' => absurd h' hs⟩
  choose TC hTCf hTC using hIC
  let TA : Set A := ((⋃ s ∈ {x | x ∈ LB}, TB s) ∪ (⋃ s ∈ {x | x ∈ LC}, TC s)) ∪
    {a | a ∈ (l1 ++ l2 ++ l3).map Prod.fst}
  have hTA : TA.Finite := by
    refine Set.Finite.union (Set.Finite.union ?_ ?_) (List.finite_toSet _)
    · exact Set.Finite.biUnion (List.finite_toSet _) (fun s _ => hTBf s)
    · exact Set.Finite.biUnion (List.finite_toSet _) (fun s _ => hTCf s)
  obtain ⟨A', _, _, _, φ, hlift, hmax⟩ := approx_base TA hTA
  letI : Algebra A' K := ((algebraMap A K).comp φ).toAlgebra
  have hφ : algebraMap A' K = (algebraMap A K).comp φ := rfl
  have sa : ∀ {s : Set K} {x : K}, x ∈ s → x ∈ Algebra.adjoin A' s := fun h => Algebra.subset_adjoin h
  have hrange : TA ⊆ Set.range φ := fun a ha => by
    obtain ⟨a', h1, _⟩ := hlift a ha
    exact ⟨a', h1⟩
  have hcoef : ∀ p ∈ l1 ++ l2 ++ l3, p.1 ∈ IsLocalRing.maximalIdeal A →
      ∃ a' ∈ IsLocalRing.maximalIdeal A', φ a' = p.1 := by
    intro p hp hm
    obtain ⟨a', h1, h2⟩ := hlift p.1 (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩))
    exact ⟨a', h2 hm, h1⟩
  let B' : Subalgebra A' K := Algebra.adjoin A' (LB.toFinset : Set K)
  let C' : Subalgebra A' K := Algebra.adjoin A' (LC.toFinset : Set K)
  have memB' : ∀ x ∈ LB, x ∈ B' := fun x hx => Algebra.subset_adjoin (by simpa using hx)
  have memC' : ∀ x ∈ LC, x ∈ C' := fun x hx => Algebra.subset_adjoin (by simpa using hx)
  have hB'B : ∀ x ∈ B', x ∈ B := adj_sub φ hφ B _ (fun x hx => hLB x (by simpa using hx))
  have hC'C : ∀ x ∈ C', x ∈ C := adj_sub φ hφ C _ (fun x hx => hLC x (by simpa using hx))
  have hchart : Charts B' C' t := by
    refine ⟨ht0, memB' t (List.mem_cons.mpr (Or.inl rfl)), memC' t⁻¹ (List.mem_cons.mpr (Or.inl rfl)),
      ?_, ?_, ?_⟩
    · refine int_adj _ _ (fun s hs => ?_)
      have hs' : s ∈ LB := by simpa using hs
      exact hTB s (hLB s hs') A' φ hφ
        (fun a ha => hrange (Or.inl (Or.inl (Set.mem_iUnion₂.mpr ⟨s, hs', ha⟩))))
    · refine int_adj _ _ (fun s hs => ?_)
      have hs' : s ∈ LC := by simpa using hs
      exact hTC s (hLC s hs') A' φ hφ
        (fun a ha => hrange (Or.inl (Or.inr (Set.mem_iUnion₂.mpr ⟨s, hs', ha⟩))))
    · show Algebra.adjoin A' ((B' : Set K) ∪ {t⁻¹}) = Algebra.adjoin A' ((C' : Set K) ∪ {t})
      apply le_antisymm
      · apply Algebra.adjoin_le
        rintro x (hx | hx)
        · refine (Algebra.adjoin_le ?_ : B' ≤ _) hx
          intro y hy
          have hy' : y ∈ LB := by simpa using hy
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact sa (Or.inr rfl)
          rcases List.mem_append.mp hy' with hy' | hy'
          · obtain ⟨_, h2⟩ := hnc y (hBD y (hBc y hy'))
            rw [h2]
            exact mul_mem (sa (Or.inl (memC' _
              (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨y, hy', rfl⟩))))))))
              (pow_mem (sa (Or.inr rfl)) _)
          · obtain ⟨c, hcm, rfl⟩ := List.mem_map.mp hy'
            obtain ⟨_, h2⟩ := hnb c (hCD c (hCc c hcm))
            have key : c * t ^ nn c = nb c := by
              calc c * t ^ nn c = (nb c * t⁻¹ ^ nn c) * t ^ nn c := by rw [← h2]
                _ = nb c := by rw [inv_pow, mul_assoc, inv_mul_cancel₀ (pow_ne_zero _ ht0), mul_one]
            rw [← key]
            exact mul_mem (sa (Or.inl (memC' _
              (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hcm)))))))
              (pow_mem (sa (Or.inr rfl)) _)
        · rw [Set.mem_singleton_iff.mp hx]
          exact sa (Or.inl (memC' _ (List.mem_cons.mpr (Or.inl rfl))))
      · apply Algebra.adjoin_le
        rintro x (hx | hx)
        · refine (Algebra.adjoin_le ?_ : C' ≤ _) hx
          intro y hy
          have hy' : y ∈ LC := by simpa using hy
          rcases List.mem_cons.mp hy' with rfl | hy'
          · exact sa (Or.inr rfl)
          rcases List.mem_append.mp hy' with hy' | hy'
          · obtain ⟨_, h2⟩ := hnb y (hCD y (hCc y hy'))
            rw [h2]
            exact mul_mem (sa (Or.inl (memB' _
              (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨y, hy', rfl⟩))))))))
              (pow_mem (sa (Or.inr rfl)) _)
          · obtain ⟨b, hbm, rfl⟩ := List.mem_map.mp hy'
            obtain ⟨_, h2⟩ := hnc b (hBD b (hBc b hbm))
            have key : b * t⁻¹ ^ mc b = nc b := by
              calc b * t⁻¹ ^ mc b = (nc b * t ^ mc b) * t⁻¹ ^ mc b := by rw [← h2]
                _ = nc b := by rw [inv_pow, mul_assoc, mul_inv_cancel₀ (pow_ne_zero _ ht0), mul_one]
            rw [← key]
            exact mul_mem (sa (Or.inl (memB' _
              (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hbm)))))))
              (pow_mem (sa (Or.inr rfl)) _)
        · rw [Set.mem_singleton_iff.mp hx]
          exact sa (Or.inl (memB' _ (List.mem_cons.mpr (Or.inl rfl))))
  have inBc : ∀ x ∈ Bc, x ∈ LB := fun x hx => List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hx)))
  have inCc : ∀ x ∈ Cc, x ∈ LC := fun x hx => List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inl hx)))
  have hpair : IdemPair B' C' t e f := by
    refine ⟨memB' e (inBc e (List.mem_cons.mpr (Or.inl rfl))),
      memC' f (inCc f (List.mem_cons.mpr (Or.inl rfl))), ?_, ?_, ?_⟩
    · rw [hs1]
      exact list_mem φ hφ l1 (Subalgebra.toSubmodule B')
        (fun p hp => hcoef p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inl hp)))) (hl1 p hp).1)
        (fun p hp => memB' _ (inBc _ (List.mem_cons.mpr (Or.inr (List.mem_append.mpr
          (Or.inl (List.mem_map.mpr ⟨p, hp, rfl⟩)))))))
    · rw [hs2]
      exact list_mem φ hφ l2 (Subalgebra.toSubmodule C')
        (fun p hp => hcoef p (List.mem_append.mpr (Or.inl (List.mem_append.mpr (Or.inr hp)))) (hl2 p hp).1)
        (fun p hp => memC' _ (inCc _ (List.mem_cons.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))))
    · rw [hs3]
      refine list_mem φ hφ l3 (Subalgebra.toSubmodule (AdjoinInv B' t))
        (fun p hp => hcoef p (List.mem_append.mpr (Or.inr hp)) (hl3 p hp).1) (fun p hp => ?_)
      show p.2 ∈ AdjoinInv B' t
      rw [(hnb p.2 (hl3 p hp).2).2]
      exact mul_mem (sa (Or.inl (memB' _ (inBc _
        (List.mem_cons.mpr (Or.inr (List.mem_append.mpr (Or.inr (List.mem_map.mpr ⟨p, hp, rfl⟩)))))))))
        (pow_mem (sa (Or.inr rfl)) _)
  have hres := hN A' K B' C' t hchart (Subalgebra.fg_adjoin_finset _) (Subalgebra.fg_adjoin_finset _) e f hpair
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.mp hres
  rw [← hyz]
  exact Submodule.add_mem_sup (mS_sub φ hφ hmax B' B hB'B y hy) (mS_sub φ hφ hmax C' C hC'C z hz)

end LateralTheory.E.LZIdemSumApproxYDDUPf
