import Mathlib
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj TopologicalSpace TensorProduct
open scoped CategoryTheory.Obj

namespace GlobalTheory
namespace NoCommonZeroSpread

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp⟩`. Consider the case `insert x S hx ih`. Take `⟨b, hb, hbS⟩` from `ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))`. Establish `hxK` using `hS x (Finset.mem_insert_self x S)`.

Rewrite `hxK` using `[Subfield.mem_closure_iff, Subring.closure_eq]`. Take `⟨y, hy, z, hz, hyz⟩` from `hxK`. Take `⟨a, rfl⟩` from `RingHom.mem_range.1 hy`. Take `⟨c, rfl⟩` from `RingHom.mem_range.1 hz`. Distinguish the cases in `hc : φ c = 0`.

Establish `hx0 : x = 0` using `by rw [← hyz, hc, div_zero]`. Use `⟨b, hb, fun w hw => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hw with h | h` into its components or cases. Conclude with `⟨0, by rw [h, hx0, mul_zero, map_zero]⟩`. Conclude with `hbS w h`.

Use `⟨b * c, by simp [hb, hc], fun w hw => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hw with h | h` into its components or cases. Use `⟨b * a, ?_⟩` and prove the remaining obligations. Rewrite using `[h, ← hyz, map_mul, map_mul]`. Clear the denominators using the available nonvanishing facts.

Take `⟨d, hd⟩` from `hbS w h`. Use `⟨d * c, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hd, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma exists_common_denominator {A Ω : Type} [CommRing A] [Field Ω] (φ : A →+* Ω)
    (S : Finset Ω) (hS : ∀ x ∈ S, x ∈ Subfield.closure (φ.range : Set Ω)) :
    ∃ b : A, φ b ≠ 0 ∧ ∀ x ∈ S, φ b * x ∈ Set.range φ := by
  classical
  induction S using Finset.induction_on with
  | empty => exact ⟨1, by simp, by simp⟩
  | insert x S hx ih =>
    obtain ⟨b, hb, hbS⟩ := ih (fun y hy => hS y (Finset.mem_insert_of_mem hy))
    have hxK := hS x (Finset.mem_insert_self x S)
    rw [Subfield.mem_closure_iff, Subring.closure_eq] at hxK
    obtain ⟨y, hy, z, hz, hyz⟩ := hxK
    obtain ⟨a, rfl⟩ := RingHom.mem_range.1 hy
    obtain ⟨c, rfl⟩ := RingHom.mem_range.1 hz
    by_cases hc : φ c = 0
    · have hx0 : x = 0 := by rw [← hyz, hc, div_zero]
      refine ⟨b, hb, fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · exact ⟨0, by rw [h, hx0, mul_zero, map_zero]⟩
      · exact hbS w h
    · refine ⟨b * c, by simp [hb, hc], fun w hw => ?_⟩
      rcases Finset.mem_insert.1 hw with h | h
      · refine ⟨b * a, ?_⟩
        rw [h, ← hyz, map_mul, map_mul]
        field_simp
      · obtain ⟨d, hd⟩ := hbS w h
        refine ⟨d * c, ?_⟩
        rw [map_mul, hd, map_mul]
        ring

/- English proof (translation)
Introduce `A _ τ J _ F Ω _ _ φ hno`. Set `G : J → MvPolynomial τ Ω` to `fun j => MvPolynomial.map φ (F j)`. Establish `h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G)`. Establish `hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅`. Use extensionality with `x`.

Simplify using `only [Set.mem_empty_iff_false, iff_false]`. Introduce `hx`. Apply `hno` to reduce the goal to its premises. Use `⟨x, fun j => ?_⟩` and prove the remaining obligations. Use `hx (G j) (Ideal.subset_span ⟨j, rfl⟩)` as an intermediate fact.

Simplify `this` using `[G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map]`. Use `MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))` as an intermediate fact. Rewrite `this` using `[hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top]`. Rewrite using `[this]`. Conclude with `Submodule.mem_top`.

Take `⟨c, hc⟩` from `(Finsupp.mem_span_range_iff_exists_finsupp).1 h1`. Set `K : Subfield Ω` to `Subfield.closure (φ.range : Set Ω)`. Take `⟨g, hg⟩` from `LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω) (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)`. Establish `hg1 : ∀ y : K, g (y : Ω) = y` using `fun y => by`. Conclude with `LinearMap.congr_fun hg y`.

Establish `hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y`. Introduce `x y`. Establish `: x * (y : Ω) = y • x` using `by rw [mul_comm]; rfl`. Rewrite using `[this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]`. Establish `hφK : ∀ a : A, φ a ∈ K` using `fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)`.

Set `P : MvPolynomial τ Ω → MvPolynomial τ Ω` to `fun h => ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)`. Establish `hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω)`. Introduce `h n`. Simplify using `only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]`. Rewrite using `[Finset.sum_ite_eq']`.

Use `split_ifs with hn`. Both sides reduce to the same expression. Rewrite using `[MvPolynomial.notMem_support_iff.1 hn]`. Simplify using the standard rewrite rules. Establish `hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂`.

Introduce `h₁ h₂`. Use extensionality with `n`. Simplify using `[hPc, MvPolynomial.coeff_add]`. Establish `hP1 : P 1 = 1`. Use extensionality with `n`.

Rewrite using `[hPc, MvPolynomial.coeff_one]`. Use `split_ifs`. Use `hg1 1` as an intermediate fact. Simplify using `using this`. Simplify using the standard rewrite rules.

Establish `hPmul : ∀ h j, P (h * G j) = P h * G j`. Introduce `h j`. Use extensionality with `n`. Rewrite using `[hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]`. Use `(map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)` and prove the remaining obligations.

Use `show ((g _ : K) : Ω) = _`. Establish `e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω)`. Simplify using `[G, MvPolynomial.coeff_map]`. Rewrite using `[e, hgK, hPc]`. Set `PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω` to `AddMonoidHom.mk' P hPadd`.

Establish `hsum : ∑ j ∈ c.support, P (c j) * G j = 1`. Simplify using `only [Finsupp.sum, smul_eq_mul] at hc`. Use `congrArg PA hc` as an intermediate fact. Rewrite `this` using `[map_sum]`. Simplify using `only [PA, AddMonoidHom.mk'_apply] at this`.

Rewrite using `[← hP1]`. Use `this using 1` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Conclude with `(hPmul _ _).symm`. Set `S : Finset Ω` to `c.support.biUnion (fun j => (P (c j)).coeffs)`.

Take `⟨b, hb, hbS⟩` from `exists_common_denominator φ S (by`. Introduce `x hx`. Take `⟨j, -, hj⟩` from `Finset.mem_biUnion.1 hx`. Take `⟨n, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 hj`. Rewrite using `[hPc]`.

Conclude with `(g _).2)`. Establish `hQ : ∀ j, ∃ q : MvPolynomial τ A, MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j)`. Introduce `j`. Establish `: MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ` using `τ) φ) := by`. Rewrite using `[MvPolynomial.mem_range_map_iff_coeffs_subset]`.

Introduce `y hy`. Take `⟨n, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)`. Rewrite using `[MvPolynomial.coeff_C_mul]`. Distinguish the cases in `hn : (P (c j)).coeff n = 0`. Rewrite using `[hn, mul_zero]`.

Conclude with `⟨0, map_zero φ⟩`. Establish `hj : j ∈ c.support`. Rewrite using `[Finsupp.mem_support_iff]`. Introduce `h0`. Apply `hn` to reduce the goal to its premises.

Rewrite using `[hPc, h0]`. Simplify using the standard rewrite rules. Conclude with `hbS _ (Finset.mem_biUnion.2 ⟨j, hj, MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)`. Conclude with `this`. Use `choose q hq using hQ`.

Set `E : MvPolynomial τ A` to `MvPolynomial.C b - ∑ j ∈ c.support, q j * F j`. Establish `hE : MvPolynomial.map φ E = 0`. Establish `hG : ∀ j, MvPolynomial.map φ (F j) = G j` using `fun j => rfl`. Simplify using `only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]`. Rewrite using `[← Finset.mul_sum, hsum, _root_.mul_one, sub_self]`.

Use `⟨b, E.coeffs, hb, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨n, -, rfl⟩` from `MvPolynomial.mem_coeffs_iff.1 hy`. Use `congrArg (MvPolynomial.coeff n) hE` as an intermediate fact. Rewrite `this` using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero]`. Then use the resulting hypothesis.

Introduce `k _ ψ hψb hψI ⟨z, hz⟩`. Establish `h0 : MvPolynomial.map ψ E = 0`. Use extensionality with `n`. Rewrite using `[MvPolynomial.coeff_map, MvPolynomial.coeff_zero]`. Distinguish the cases in `hn : n ∈ E.support`.

Conclude with `hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)`. Rewrite using `[MvPolynomial.notMem_support_iff.1 hn, map_zero]`. Establish `h2 : MvPolynomial.eval₂ ψ z E = 0`. Rewrite using `[MvPolynomial.eval₂_eq_eval_map, h0, map_zero]`. Establish `h3 : MvPolynomial.eval₂ ψ z E = ψ b`.

Simplify using `[E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum, MvPolynomial.eval₂_mul, hz]`. Conclude with `hψb (h3 ▸ h2)`.
-/
theorem no_common_zero_spreads : ∀ (A : Type) [CommRing A] (τ J : Type) [Finite τ] (F : J → MvPolynomial τ A) (Ω : Type) [Field Ω] [IsAlgClosed Ω] (φ : A →+* Ω), (¬ ∃ z : τ → Ω, ∀ j, MvPolynomial.eval₂ φ z (F j) = 0) → ∃ (a : A) (I : Finset A), φ a ≠ 0 ∧ (∀ c ∈ I, φ c = 0) ∧ ∀ (k : Type) [Field k] (ψ : A →+* k), ψ a ≠ 0 → (∀ c ∈ I, ψ c = 0) → ¬ ∃ z : τ → k, ∀ j, MvPolynomial.eval₂ ψ z (F j) = 0 := by
  intro A _ τ J _ F Ω _ _ φ hno
  classical
  let G : J → MvPolynomial τ Ω := fun j => MvPolynomial.map φ (F j)

  have h1 : (1 : MvPolynomial τ Ω) ∈ Ideal.span (Set.range G) := by
    have hz : MvPolynomial.zeroLocus Ω (Ideal.span (Set.range G)) = ∅ := by
      ext x
      simp only [Set.mem_empty_iff_false, iff_false]
      intro hx
      apply hno
      refine ⟨x, fun j => ?_⟩
      have := hx (G j) (Ideal.subset_span ⟨j, rfl⟩)
      simpa [G, MvPolynomial.coe_aeval_eq_eval, MvPolynomial.eval_map] using this
    have := MvPolynomial.vanishingIdeal_zeroLocus_eq_radical (K := Ω) (Ideal.span (Set.range G))
    rw [hz, MvPolynomial.vanishingIdeal_empty, eq_comm, Ideal.radical_eq_top] at this
    rw [this]; exact Submodule.mem_top
  obtain ⟨c, hc⟩ := (Finsupp.mem_span_range_iff_exists_finsupp).1 h1

  let K : Subfield Ω := Subfield.closure (φ.range : Set Ω)
  obtain ⟨g, hg⟩ := LinearMap.exists_leftInverse_of_injective (Algebra.linearMap K Ω)
    (LinearMap.ker_eq_bot.2 (algebraMap K Ω).injective)
  have hg1 : ∀ y : K, g (y : Ω) = y := fun y => by
    exact LinearMap.congr_fun hg y
  have hgK : ∀ (x : Ω) (y : K), ((g (x * y) : K) : Ω) = (g x : Ω) * y := by
    intro x y
    have : x * (y : Ω) = y • x := by rw [mul_comm]; rfl
    rw [this, map_smul, smul_eq_mul, Subfield.coe_mul, mul_comm]
  have hφK : ∀ a : A, φ a ∈ K := fun a => Subfield.subset_closure (RingHom.mem_range_self φ a)
  let P : MvPolynomial τ Ω → MvPolynomial τ Ω := fun h =>
    ∑ m ∈ h.support, MvPolynomial.monomial m ((g (h.coeff m) : K) : Ω)
  have hPc : ∀ h n, (P h).coeff n = ((g (h.coeff n) : K) : Ω) := by
    intro h n
    simp only [P, MvPolynomial.coeff_sum, MvPolynomial.coeff_monomial]
    rw [Finset.sum_ite_eq']
    split_ifs with hn
    · rfl
    · rw [MvPolynomial.notMem_support_iff.1 hn]; simp
  have hPadd : ∀ h₁ h₂, P (h₁ + h₂) = P h₁ + P h₂ := by
    intro h₁ h₂; ext n; simp [hPc, MvPolynomial.coeff_add]
  have hP1 : P 1 = 1 := by
    ext n
    rw [hPc, MvPolynomial.coeff_one]
    split_ifs
    · have := hg1 1; simpa using this
    · simp
  have hPmul : ∀ h j, P (h * G j) = P h * G j := by
    intro h j; ext n
    rw [hPc, MvPolynomial.coeff_mul, MvPolynomial.coeff_mul, map_sum]
    refine (map_sum K.subtype _ _).trans (Finset.sum_congr rfl fun x _ => ?_)
    show ((g _ : K) : Ω) = _
    have e : (G j).coeff x.2 = ((⟨φ ((F j).coeff x.2), hφK _⟩ : K) : Ω) := by
      simp [G, MvPolynomial.coeff_map]
    rw [e, hgK, hPc]
  let PA : MvPolynomial τ Ω →+ MvPolynomial τ Ω := AddMonoidHom.mk' P hPadd
  have hsum : ∑ j ∈ c.support, P (c j) * G j = 1 := by
    simp only [Finsupp.sum, smul_eq_mul] at hc
    have := congrArg PA hc
    rw [map_sum] at this
    simp only [PA, AddMonoidHom.mk'_apply] at this
    rw [← hP1]
    convert this using 1
    refine Finset.sum_congr rfl fun j _ => ?_
    exact (hPmul _ _).symm

  let S : Finset Ω := c.support.biUnion (fun j => (P (c j)).coeffs)
  obtain ⟨b, hb, hbS⟩ := exists_common_denominator φ S (by
    intro x hx
    obtain ⟨j, -, hj⟩ := Finset.mem_biUnion.1 hx
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hj
    rw [hPc]; exact (g _).2)
  have hQ : ∀ j, ∃ q : MvPolynomial τ A,
      MvPolynomial.map φ q = MvPolynomial.C (φ b) * P (c j) := by
    intro j
    have : MvPolynomial.C (φ b) * P (c j) ∈ Set.range (MvPolynomial.map (σ := τ) φ) := by
      rw [MvPolynomial.mem_range_map_iff_coeffs_subset]
      intro y hy
      obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 (Finset.mem_coe.1 hy)
      rw [MvPolynomial.coeff_C_mul]
      by_cases hn : (P (c j)).coeff n = 0
      · rw [hn, mul_zero]; exact ⟨0, map_zero φ⟩
      · have hj : j ∈ c.support := by
          rw [Finsupp.mem_support_iff]
          intro h0; apply hn; rw [hPc, h0]; simp
        exact hbS _ (Finset.mem_biUnion.2 ⟨j, hj,
          MvPolynomial.mem_coeffs_iff.2 ⟨n, MvPolynomial.mem_support_iff.2 hn, rfl⟩⟩)
    exact this
  choose q hq using hQ
  let E : MvPolynomial τ A := MvPolynomial.C b - ∑ j ∈ c.support, q j * F j
  have hE : MvPolynomial.map φ E = 0 := by
    have hG : ∀ j, MvPolynomial.map φ (F j) = G j := fun j => rfl
    simp only [E, map_sub, map_sum, map_mul, MvPolynomial.map_C, hq, hG, _root_.mul_assoc]
    rw [← Finset.mul_sum, hsum, _root_.mul_one, sub_self]
  refine ⟨b, E.coeffs, hb, ?_, ?_⟩
  · intro y hy
    obtain ⟨n, -, rfl⟩ := MvPolynomial.mem_coeffs_iff.1 hy
    have := congrArg (MvPolynomial.coeff n) hE
    rwa [MvPolynomial.coeff_map, MvPolynomial.coeff_zero] at this
  · intro k _ ψ hψb hψI ⟨z, hz⟩
    have h0 : MvPolynomial.map ψ E = 0 := by
      ext n
      rw [MvPolynomial.coeff_map, MvPolynomial.coeff_zero]
      by_cases hn : n ∈ E.support
      · exact hψI _ (MvPolynomial.mem_coeffs_iff.2 ⟨n, hn, rfl⟩)
      · rw [MvPolynomial.notMem_support_iff.1 hn, map_zero]
    have h2 : MvPolynomial.eval₂ ψ z E = 0 := by
      rw [MvPolynomial.eval₂_eq_eval_map, h0, map_zero]
    have h3 : MvPolynomial.eval₂ ψ z E = ψ b := by
      simp [E, MvPolynomial.eval₂_sub, MvPolynomial.eval₂_C, MvPolynomial.eval₂_sum,
        MvPolynomial.eval₂_mul, hz]
    exact hψb (h3 ▸ h2)

end NoCommonZeroSpread
end GlobalTheory
