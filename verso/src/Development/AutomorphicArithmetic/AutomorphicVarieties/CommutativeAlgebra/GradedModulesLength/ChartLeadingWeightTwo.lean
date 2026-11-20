import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.ToDegInjective
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.GradedModulesLength.NegWeightLe

open IsLocalRing Filter Formalism.MainNotions.V.Pf.V2.Calc UpperTheory.V.Alg UpperTheory.V.Alg.M

namespace UpperTheory.V.Alg.M

section Comb

variable {τ : Type}

/- English proof (translation)
Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum]`. Take `⟨i, hi, hne⟩` from `Finset.exists_ne_zero_of_sum_ne_zero h`. Rewrite `hne` using `[smul_eq_mul]`. Use `⟨i, ν - Finsupp.single i 1, right_ne_zero_of_mul hne, ?_⟩` and prove the remaining obligations. Rewrite using `[add_tsub_cancel_of_le]`.

Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul hne)`.
-/
private theorem sp_peel (w : τ → ℕ) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν ≠ 0) :
    ∃ i ν', w i ≠ 0 ∧ ν = Finsupp.single i 1 + ν' := by
  rw [Finsupp.weight_apply, Finsupp.sum] at h
  obtain ⟨i, hi, hne⟩ := Finset.exists_ne_zero_of_sum_ne_zero h
  rw [smul_eq_mul] at hne
  refine ⟨i, ν - Finsupp.single i 1, right_ne_zero_of_mul hne, ?_⟩
  rw [add_tsub_cancel_of_le]
  rw [Finsupp.single_le_iff]
  exact Nat.one_le_iff_ne_zero.mpr (left_ne_zero_of_mul hne)

/- English proof (translation)
Simplify using `[Finsupp.weight_apply, Finsupp.sum_single_index]`.
-/
private theorem sp_ws (w : τ → ℕ) (i : τ) : Finsupp.weight w (Finsupp.single i 1) = w i := by
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

/- English proof (translation)
Rewrite using `[← Finsupp.support_eq_empty]`. Assume the negation of the conclusion as `hne`. Take `⟨i, hi⟩` from `Finset.nonempty_iff_ne_empty.mpr hne`. Rewrite `h` using `[Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff]`. Establish `h1` using `h i hi`.

Rewrite `h1` using `[smul_eq_mul, mul_eq_zero]`. Break down `h1 with h1 | h1` into its components or cases. Conclude with `(Finsupp.mem_support_iff.mp hi) h1`. Conclude with `hw i h1`.
-/
private theorem sp_zero (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 0) : ν = 0 := by
  rw [← Finsupp.support_eq_empty]
  by_contra hne
  obtain ⟨i, hi⟩ := Finset.nonempty_iff_ne_empty.mpr hne
  rw [Finsupp.weight_apply, Finsupp.sum, Finset.sum_eq_zero_iff] at h
  have h1 := h i hi
  rw [smul_eq_mul, mul_eq_zero] at h1
  rcases h1 with h1 | h1
  · exact (Finsupp.mem_support_iff.mp hi) h1
  · exact hw i h1

/- English proof (translation)
Take `⟨i, ν', hi, rfl⟩` from `sp_peel w ν (by rw [h]; exact one_ne_zero)`. Rewrite `h` using `[map_add, sp_ws]`. Establish `h0 : Finsupp.weight w ν' = 0` using `by omega`. Conclude with `⟨i, by rw [sp_zero w hw ν' h0, add_zero]⟩`.
-/
private theorem sp_one (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 1) :
    ∃ i, ν = Finsupp.single i 1 := by
  obtain ⟨i, ν', hi, rfl⟩ := sp_peel w ν (by rw [h]; exact one_ne_zero)
  rw [map_add, sp_ws] at h
  have h0 : Finsupp.weight w ν' = 0 := by omega
  exact ⟨i, by rw [sp_zero w hw ν' h0, add_zero]⟩

/- English proof (translation)
Take `⟨i, ν', hi, rfl⟩` from `sp_peel w ν (by rw [h]; exact two_ne_zero)`. Rewrite `h` using `[map_add, sp_ws]`. Break down `(by omega : w i = 2 ∨ w i = 1) with h2 | h1` into its components or cases. Use `left`. Conclude with `⟨i, by rw [sp_zero w hw ν' (by omega), add_zero]⟩`.

Use `right`. Take `⟨k, rfl⟩` from `sp_one w hw ν' (by omega)`. Rewrite `h` using `[sp_ws]`. Conclude with `⟨i, k, h1, by omega, rfl⟩`.
-/
private theorem sp_two (w : τ → ℕ) (hw : ∀ i, w i ≠ 0) (ν : τ →₀ ℕ) (h : Finsupp.weight w ν = 2) :
    (∃ i, ν = Finsupp.single i 1) ∨
      ∃ i k, w i = 1 ∧ w k = 1 ∧ ν = Finsupp.single i 1 + Finsupp.single k 1 := by
  obtain ⟨i, ν', hi, rfl⟩ := sp_peel w ν (by rw [h]; exact two_ne_zero)
  rw [map_add, sp_ws] at h
  rcases (by omega : w i = 2 ∨ w i = 1) with h2 | h1
  · left
    exact ⟨i, by rw [sp_zero w hw ν' (by omega), add_zero]⟩
  · right
    obtain ⟨k, rfl⟩ := sp_one w hw ν' (by omega)
    rw [sp_ws] at h
    exact ⟨i, k, h1, by omega, rfl⟩

/- English proof (translation)
Take `⟨i, ν1, hi, rfl⟩` from `sp_peel w ν (by rw [h]; omega)`. Rewrite `h` using `[map_add, sp_ws]`. Establish `hi2` using `hw i`. Break down `(by omega : w i = 2 ∨ w i = 1) with h2 | h1` into its components or cases. Conclude with `⟨Finsupp.single i 1, ν1, rfl, by rw [sp_ws]; exact h2, by rw [sp_ws]; exact hw' i hi⟩`.

Take `⟨k, ν2, hk, rfl⟩` from `sp_peel w ν1 (by omega)`. Rewrite `h` using `[map_add, sp_ws]`. Establish `hk2` using `hw k`. Break down `(by omega : w k = 2 ∨ w k = 1) with h2 | h1'` into its components or cases. Conclude with `⟨Finsupp.single k 1, Finsupp.single i 1 + ν2, add_left_comm _ _ _, by rw [sp_ws]; exact h2, by rw [sp_ws]; exact hw' k hk⟩`.

Use `⟨Finsupp.single i 1 + Finsupp.single k 1, ν2, by rw [add_assoc], ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, sp_ws, sp_ws]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[map_add, sp_ws, sp_ws, hw' i hi, hw' k hk]`.
-/
private theorem sp_split (w w' : τ → ℕ) (hw : ∀ i, w i ≤ 2) (hw' : ∀ i, w i ≠ 0 → w' i = 0) (a : ℕ) (ν : τ →₀ ℕ)
    (h : Finsupp.weight w ν = 2 * (a + 1)) :
    ∃ μ ν', ν = μ + ν' ∧ Finsupp.weight w μ = 2 ∧ Finsupp.weight w' μ = 0 := by
  obtain ⟨i, ν1, hi, rfl⟩ := sp_peel w ν (by rw [h]; omega)
  rw [map_add, sp_ws] at h
  have hi2 := hw i
  rcases (by omega : w i = 2 ∨ w i = 1) with h2 | h1
  · exact ⟨Finsupp.single i 1, ν1, rfl, by rw [sp_ws]; exact h2, by rw [sp_ws]; exact hw' i hi⟩
  · obtain ⟨k, ν2, hk, rfl⟩ := sp_peel w ν1 (by omega)
    rw [map_add, sp_ws] at h
    have hk2 := hw k
    rcases (by omega : w k = 2 ∨ w k = 1) with h2 | h1'
    · exact ⟨Finsupp.single k 1, Finsupp.single i 1 + ν2, add_left_comm _ _ _, by rw [sp_ws]; exact h2,
        by rw [sp_ws]; exact hw' k hk⟩
    · refine ⟨Finsupp.single i 1 + Finsupp.single k 1, ν2, by rw [add_assoc], ?_, ?_⟩
      · rw [map_add, sp_ws, sp_ws]
        omega
      · rw [map_add, sp_ws, sp_ws, hw' i hi, hw' k hk]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul, nsmul_eq_mul]`. Use `push_cast`. Rewrite using `[← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← mul_sub, Int.toNat_sub_toNat_neg]`. Simplify using `only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul]`. Rewrite using `[← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[← mul_add, Int.toNat_add_toNat_neg_eq_natAbs]`.
-/
private theorem sp_wt (wt : τ → ℤ) (ν : τ →₀ ℕ) :
    Finsupp.weight wt ν = (Finsupp.weight (posW wt) ν : ℕ) - (Finsupp.weight (negW wt) ν : ℕ) ∧
    Finsupp.weight (fun i => (wt i).natAbs) ν = Finsupp.weight (posW wt) ν + Finsupp.weight (negW wt) ν := by
  constructor
  · simp only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul, nsmul_eq_mul]
    push_cast
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_sub, Int.toNat_sub_toNat_neg]
  · simp only [Finsupp.weight_apply, Finsupp.sum, posW, negW, smul_eq_mul]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← mul_add, Int.toNat_add_toNat_neg_eq_natAbs]

private def Lead {E : Type} [CommRing E] (wt : τ → ℤ) (g : MvPowerSeries τ E) (ν : τ →₀ ℕ) : Prop :=
  g ∈ fil E wt (Finsupp.weight (negW wt) ν) ∧ MvPowerSeries.coeff ν g ≠ 0 ∧
    ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν → MvPowerSeries.coeff ν' g = 0

/- English proof (translation)
Take `⟨hg1, -, hg3⟩` from `hg`. Take `⟨hh1, -, hh3⟩` from `hh`. Establish `key : ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ → ∀ p ∈ Finset.HasAntidiagonal.antidiagonal ν', p ≠ (ν, μ) → MvPowerSeries.coeff p.1 g * MvPowerSeries.coeff p.2 h = 0`. Introduce `ν' hν' p hp hne`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`.

Establish `hs : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ`. Rewrite using `[← map_add, hp, hν']`. Distinguish the cases in `h1 : Finsupp.weight (negW wt) p.1 < Finsupp.weight (negW wt) ν`. Rewrite using `[hg1 p.1 h1, zero_mul]`. Distinguish the cases in `h2 : Finsupp.weight (negW wt) p.2 < Finsupp.weight (negW wt) μ`.

Rewrite using `[hh1 p.2 h2, mul_zero]`. Establish `e1 : Finsupp.weight (negW wt) p.1 = Finsupp.weight (negW wt) ν` using `by omega`. Establish `e2 : Finsupp.weight (negW wt) p.2 = Finsupp.weight (negW wt) μ` using `by omega`. Distinguish the cases in `q1 : p.1 = ν`. Establish `q2 : p.2 ≠ μ` using `fun q2 => hne (Prod.ext q1 q2)`.

Rewrite using `[hh3 p.2 e2 q2, mul_zero]`. Rewrite using `[hg3 p.1 e1 q1, zero_mul]`. Prove the components needed by the constructor for the conclusion. Rewrite using `[MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (ν, μ) (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl) (key (ν + μ) (map_add _ _ _))]`. Introduce `ν' hν' hne`.

Rewrite using `[MvPowerSeries.coeff_mul]`. Use `Finset.sum_eq_zero fun p hp => key ν' hν' p hp ?_` and prove the remaining obligations. Introduce and unpack `rfl`. Rewrite `hp` using `[Finset.HasAntidiagonal.mem_antidiagonal]`. Conclude with `hne hp.symm`.
-/
private theorem Lead.coeff_mul_of_lead_add_and_vanishing {E : Type} [Field E] {wt : τ → ℤ} {g h : MvPowerSeries τ E} {ν μ : τ →₀ ℕ}
    (hg : Lead wt g ν) (hh : Lead wt h μ) :
    MvPowerSeries.coeff (ν + μ) (g * h) = MvPowerSeries.coeff ν g * MvPowerSeries.coeff μ h ∧
      ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ →
        ν' ≠ ν + μ → MvPowerSeries.coeff ν' (g * h) = 0 := by
  classical
  obtain ⟨hg1, -, hg3⟩ := hg
  obtain ⟨hh1, -, hh3⟩ := hh
  have key : ∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ →
      ∀ p ∈ Finset.HasAntidiagonal.antidiagonal ν', p ≠ (ν, μ) →
        MvPowerSeries.coeff p.1 g * MvPowerSeries.coeff p.2 h = 0 := by
    intro ν' hν' p hp hne
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    have hs : Finsupp.weight (negW wt) p.1 + Finsupp.weight (negW wt) p.2 =
        Finsupp.weight (negW wt) ν + Finsupp.weight (negW wt) μ := by
      rw [← map_add, hp, hν']
    by_cases h1 : Finsupp.weight (negW wt) p.1 < Finsupp.weight (negW wt) ν
    · rw [hg1 p.1 h1, zero_mul]
    by_cases h2 : Finsupp.weight (negW wt) p.2 < Finsupp.weight (negW wt) μ
    · rw [hh1 p.2 h2, mul_zero]
    have e1 : Finsupp.weight (negW wt) p.1 = Finsupp.weight (negW wt) ν := by omega
    have e2 : Finsupp.weight (negW wt) p.2 = Finsupp.weight (negW wt) μ := by omega
    by_cases q1 : p.1 = ν
    · have q2 : p.2 ≠ μ := fun q2 => hne (Prod.ext q1 q2)
      rw [hh3 p.2 e2 q2, mul_zero]
    · rw [hg3 p.1 e1 q1, zero_mul]
  constructor
  · rw [MvPowerSeries.coeff_mul, Finset.sum_eq_single_of_mem (ν, μ)
      (Finset.HasAntidiagonal.mem_antidiagonal.mpr rfl) (key (ν + μ) (map_add _ _ _))]
  · intro ν' hν' hne
    rw [MvPowerSeries.coeff_mul]
    refine Finset.sum_eq_zero fun p hp => key ν' hν' p hp ?_
    rintro rfl
    rw [Finset.HasAntidiagonal.mem_antidiagonal] at hp
    exact hne hp.symm

/- English proof (translation)
Establish `hc` using `Lead.coeff_mul_of_lead_add_and_vanishing hg hh`. Take `⟨hg1, hg2, -⟩` from `hg`. Take `⟨hh1, hh2, -⟩` from `hh`. Unfold `Lead`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_add]`. Conclude with `(fil_holds E τ wt _ _ g h hg1 hh1).1`. Rewrite using `[hc.1]`. Conclude with `mul_ne_zero hg2 hh2`. Introduce `ν' hν' hne`.

Conclude with `hc.2 ν' (by rw [hν', map_add]) hne`.
-/
private theorem Lead.mul {E : Type} [Field E] {wt : τ → ℤ} {g h : MvPowerSeries τ E} {ν μ : τ →₀ ℕ}
    (hg : Lead wt g ν) (hh : Lead wt h μ) : Lead wt (g * h) (ν + μ) := by
  have hc := Lead.coeff_mul_of_lead_add_and_vanishing hg hh
  obtain ⟨hg1, hg2, -⟩ := hg
  obtain ⟨hh1, hh2, -⟩ := hh
  unfold Lead
  refine ⟨?_, ?_, ?_⟩
  · rw [map_add]
    exact (fil_holds E τ wt _ _ g h hg1 hh1).1
  · rw [hc.1]
    exact mul_ne_zero hg2 hh2
  · intro ν' hν' hne
    exact hc.2 ν' (by rw [hν', map_add]) hne

/- English proof (translation)
Use `⟨fun ν hν => by simp at hν, by simp, fun ν' _ h => ?_⟩` and prove the remaining obligations. Rewrite using `[MvPowerSeries.coeff_one, if_neg h]`.
-/
private theorem Lead.one {E : Type} [Field E] (wt : τ → ℤ) : Lead wt (1 : MvPowerSeries τ E) 0 := by
  classical
  refine ⟨fun ν hν => by simp at hν, by simp, fun ν' _ h => ?_⟩
  rw [MvPowerSeries.coeff_one, if_neg h]

end Comb

section Chart

variable {O A τ : Type} [CommRing O] [IsDomain O] [CommRing A] [Algebra O A] {𝒜 : ℤ → Submodule O A}
  [GradedAlgebra 𝒜] {x : A →ₐ[O] O} {wt : τ → ℤ} {φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)}

/- English proof (translation)
Simplify using `[Finsupp.weight_apply, Finsupp.sum_single_index]`.
-/
private theorem finsupp_weight_single_one (w : τ → ℤ) (i : τ) : Finsupp.weight w (Finsupp.single i 1) = w i := by
  simp [Finsupp.weight_apply, Finsupp.sum_single_index]

/- English proof (translation)
Use `conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]`. Rewrite using `[map_sum, map_sum, Finset.sum_eq_single (Finsupp.weight wt ν)]`. Introduce `j _ hj`. Conclude with `H.graded j _ (SetLike.coe_mem _) ν (Ne.symm hj)`. Introduce `hnot`.

Simplify using `only [DFinsupp.mem_support_iff, not_not] at hnot`. Rewrite using `[hnot]`. Simplify using the standard rewrite rules.
-/
private theorem sp_comp (H : IsChart0 𝒜 x wt φ) (ν : τ →₀ ℕ) (f : A) :
    MvPowerSeries.coeff ν (φ (DirectSum.decompose 𝒜 f (Finsupp.weight wt ν))) = MvPowerSeries.coeff ν (φ f) := by
  classical
  conv_rhs => rw [← DirectSum.sum_support_decompose 𝒜 f]
  rw [map_sum, map_sum, Finset.sum_eq_single (Finsupp.weight wt ν)]
  · intro j _ hj
    exact H.graded j _ (SetLike.coe_mem _) ν (Ne.symm hj)
  · intro hnot
    simp only [DFinsupp.mem_support_iff, not_not] at hnot
    rw [hnot]
    simp

/- English proof (translation)
Take `⟨f, hf1, hf2⟩` from `H.onto i`. Use `⟨(DirectSum.decompose 𝒜 f (wt i) : A), SetLike.coe_mem _, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `sp_comp H (Finsupp.single i 1) f`. Rewrite `h1` using `[finsupp_weight_single_one]`. Rewrite using `[h1]`.

Conclude with `hf1`. Introduce `i' hi'`. Distinguish the cases in `hw : wt i' = wt i`. Establish `h1` using `sp_comp H (Finsupp.single i' 1) f`. Rewrite `h1` using `[finsupp_weight_single_one, hw]`.

Rewrite using `[h1]`. Conclude with `hf2 i' hi'`. Conclude with `H.graded (wt i) _ (SetLike.coe_mem _) (Finsupp.single i' 1) (by rw [finsupp_weight_single_one]; exact hw)`.
-/
private theorem sp_lin (H : IsChart0 𝒜 x wt φ) (i : τ) :
    ∃ f ∈ 𝒜 (wt i), MvPowerSeries.coeff (Finsupp.single i 1) (φ f) ≠ 0 ∧
      ∀ i', i' ≠ i → MvPowerSeries.coeff (Finsupp.single i' 1) (φ f) = 0 := by
  obtain ⟨f, hf1, hf2⟩ := H.onto i
  refine ⟨(DirectSum.decompose 𝒜 f (wt i) : A), SetLike.coe_mem _, ?_, ?_⟩
  · have h1 := sp_comp H (Finsupp.single i 1) f
    rw [finsupp_weight_single_one] at h1
    rw [h1]
    exact hf1
  · intro i' hi'
    by_cases hw : wt i' = wt i
    · have h1 := sp_comp H (Finsupp.single i' 1) f
      rw [finsupp_weight_single_one, hw] at h1
      rw [h1]
      exact hf2 i' hi'
    · exact H.graded (wt i) _ (SetLike.coe_mem _) (Finsupp.single i' 1) (by rw [finsupp_weight_single_one]; exact hw)

omit [GradedAlgebra 𝒜] in
/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty`. Introduce `f hf h1 h2`. Conclude with `⟨f, hf, h1, fun ν' e hne => h2 ν' e hne (by simp)⟩`. Consider the case `@insert μ S hμ ih`.

Introduce `f hf h1 h2`. Establish `hνS : ν ∉ S` using `fun h => hν (Finset.mem_insert_of_mem h)`. Establish `hνμ : ν ≠ μ` using `fun h => hν (h ▸ Finset.mem_insert_self μ S)`. Establish `hS' : ∀ μ' ∈ S, Finsupp.weight (negW wt) μ' = Finsupp.weight (negW wt) ν → ∃ g ∈ M, Lead wt (φ g) μ'` using `fun μ' hm => hS μ' (Finset.mem_insert_of_mem hm)`. Distinguish the cases in `hl : Finsupp.weight (negW wt) μ = Finsupp.weight (negW wt) ν`.

Take `⟨g, hg, -, hg2, hg3⟩` from `hS μ (Finset.mem_insert_self μ S) hl`. Take `⟨⟨p, d⟩, hpd⟩` from `IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ g))`. Take `⟨⟨q, e⟩, hqe⟩` from `IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ f))`. Simplify using `only at hpd hqe`. Establish `hc : ∀ n, MvPowerSeries.coeff n (φ ((p * e) • f - (q * d) • g)) = algebraMap O (FractionRing O) (p * e) * MvPowerSeries.coeff n (φ f) - algebraMap O (FractionRing O) (q * d) * MvPowerSeries.coeff n (φ g)`.

Introduce `n`. Rewrite using `[map_sub, map_smul, map_smul, map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower, Algebra.smul_def, Algebra.smul_def]`. Establish `hd : algebraMap O (FractionRing O) d ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2`. Establish `he : algebraMap O (FractionRing O) e ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors e.2`. Establish `hp : algebraMap O (FractionRing O) p ≠ 0`.

Rewrite using `[← hpd]`. Conclude with `mul_ne_zero hg2 hd`. Apply `ih hνS hS' _ (M.sub_mem (M.smul_mem _ hf) (M.smul_mem _ hg))` to reduce the goal to its premises. Rewrite using `[hc, hg3 ν hl.symm hνμ, mul_zero, sub_zero, map_mul]`. Conclude with `mul_ne_zero (mul_ne_zero hp he) h1`.

Introduce `ν' e' hne hnS`. Distinguish the cases in `hm : ν' = μ`. Substitute `hm` using the available equality. Rewrite using `[hc, map_mul, map_mul, ← hpd, ← hqe]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[hc, h2 ν' e' hne (by simp [hm, hnS]), hg3 ν' (e'.trans hl.symm) hm]`. Expand and normalize the polynomial expressions, which then agree. Apply `ih hνS hS' f hf h1` to reduce the goal to its premises. Introduce `ν' e' hne hnS`. Apply `h2 ν' e' hne` to reduce the goal to its premises.

Introduce `hmem`. Break down `Finset.mem_insert.mp hmem with rfl | h` into its components or cases. Conclude with `hl e'`. Conclude with `hnS h`.
-/
private theorem sp_elim (M : Submodule O A) (ν : τ →₀ ℕ) (S : Finset (τ →₀ ℕ)) (hν : ν ∉ S)
    (hS : ∀ μ ∈ S, Finsupp.weight (negW wt) μ = Finsupp.weight (negW wt) ν → ∃ g ∈ M, Lead wt (φ g) μ) :
    ∀ f ∈ M, MvPowerSeries.coeff ν (φ f) ≠ 0 →
      (∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν → ν' ∉ S →
        MvPowerSeries.coeff ν' (φ f) = 0) →
      ∃ f ∈ M, MvPowerSeries.coeff ν (φ f) ≠ 0 ∧
      (∀ ν', Finsupp.weight (negW wt) ν' = Finsupp.weight (negW wt) ν → ν' ≠ ν →
        MvPowerSeries.coeff ν' (φ f) = 0) := by
  classical
  induction S using Finset.induction_on with
  | empty =>
    intro f hf h1 h2
    exact ⟨f, hf, h1, fun ν' e hne => h2 ν' e hne (by simp)⟩
  | @insert μ S hμ ih =>
    intro f hf h1 h2
    have hνS : ν ∉ S := fun h => hν (Finset.mem_insert_of_mem h)
    have hνμ : ν ≠ μ := fun h => hν (h ▸ Finset.mem_insert_self μ S)
    have hS' : ∀ μ' ∈ S, Finsupp.weight (negW wt) μ' = Finsupp.weight (negW wt) ν → ∃ g ∈ M, Lead wt (φ g) μ' :=
      fun μ' hm => hS μ' (Finset.mem_insert_of_mem hm)
    by_cases hl : Finsupp.weight (negW wt) μ = Finsupp.weight (negW wt) ν
    · obtain ⟨g, hg, -, hg2, hg3⟩ := hS μ (Finset.mem_insert_self μ S) hl
      obtain ⟨⟨p, d⟩, hpd⟩ := IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ g))
      obtain ⟨⟨q, e⟩, hqe⟩ := IsLocalization.surj (nonZeroDivisors O) (MvPowerSeries.coeff μ (φ f))
      dsimp only at hpd hqe
      have hc : ∀ n, MvPowerSeries.coeff n (φ ((p * e) • f - (q * d) • g)) =
          algebraMap O (FractionRing O) (p * e) * MvPowerSeries.coeff n (φ f) -
            algebraMap O (FractionRing O) (q * d) * MvPowerSeries.coeff n (φ g) := by
        intro n
        rw [map_sub, map_smul, map_smul, map_sub, LinearMap.map_smul_of_tower, LinearMap.map_smul_of_tower,
          Algebra.smul_def, Algebra.smul_def]
      have hd : algebraMap O (FractionRing O) d ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors d.2
      have he : algebraMap O (FractionRing O) e ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors e.2
      have hp : algebraMap O (FractionRing O) p ≠ 0 := by
        rw [← hpd]
        exact mul_ne_zero hg2 hd
      apply ih hνS hS' _ (M.sub_mem (M.smul_mem _ hf) (M.smul_mem _ hg))
      · rw [hc, hg3 ν hl.symm hνμ, mul_zero, sub_zero, map_mul]
        exact mul_ne_zero (mul_ne_zero hp he) h1
      · intro ν' e' hne hnS
        by_cases hm : ν' = μ
        · subst hm
          rw [hc, map_mul, map_mul, ← hpd, ← hqe]
          ring
        · rw [hc, h2 ν' e' hne (by simp [hm, hnS]), hg3 ν' (e'.trans hl.symm) hm]
          ring
    · apply ih hνS hS' f hf h1
      intro ν' e' hne hnS
      apply h2 ν' e' hne
      intro hmem
      rcases Finset.mem_insert.mp hmem with rfl | h
      · exact hl e'
      · exact hnS h

omit [GradedAlgebra 𝒜] in
/- English proof (translation)
Establish `h0 : φ f ∈ fil (FractionRing O) wt 0` using `fun ν hν => absurd hν (Nat.not_lt_zero _)`. Establish `h1` using `(fil_holds (FractionRing O) τ wt 0 0 (φ f) 0 h0 (Submodule.zero_mem _)).2 (wt i) (H.graded (wt i) f hf)`. Rewrite using `[sp_ws]`. Conclude with `h1`.
-/
private theorem sp_fil (H : IsChart0 𝒜 x wt φ) (i : τ) (f : A) (hf : f ∈ 𝒜 (wt i)) :
    φ f ∈ fil (FractionRing O) wt (Finsupp.weight (negW wt) (Finsupp.single i 1)) := by
  have h0 : φ f ∈ fil (FractionRing O) wt 0 := fun ν hν => absurd hν (Nat.not_lt_zero _)
  have h1 := (fil_holds (FractionRing O) τ wt 0 0 (φ f) 0 h0 (Submodule.zero_mem _)).2 (wt i) (H.graded (wt i) f hf)
  rw [sp_ws]
  exact h1

omit [GradedAlgebra 𝒜] in
/- English proof (translation)
Apply the tactic sequence `rcases H.wts i with h | h | h | h <;> rw [h] <;> decide`.
-/
private theorem sp_abs (H : IsChart0 𝒜 x wt φ) (i : τ) : (wt i).natAbs ≠ 0 := by
  rcases H.wts i with h | h | h | h <;> rw [h] <;> decide

/- English proof (translation)
Take `⟨f, hf, h1, h2⟩` from `sp_lin H i`. Use `⟨f, hf, sp_fil H i f hf, h1, fun ν' a b => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hw : Finsupp.weight wt ν' = wt i`. Use `sp_wt wt ν'` as an intermediate fact. Rewrite `a` using `[sp_ws, negW]`.

Take `⟨k, rfl⟩` from `sp_one _ (sp_abs H) ν' (by omega)`. Conclude with `h2 k fun h => b (by rw [h])`. Conclude with `H.graded _ _ hf _ hw`.
-/
private theorem chart_leading_weight_one (H : IsChart0 𝒜 x wt φ) (i : τ) (hi : (wt i).natAbs = 1) :
    ∃ f ∈ 𝒜 (wt i), Lead wt (φ f) (Finsupp.single i 1) := by
  obtain ⟨f, hf, h1, h2⟩ := sp_lin H i
  refine ⟨f, hf, sp_fil H i f hf, h1, fun ν' a b => ?_⟩
  by_cases hw : Finsupp.weight wt ν' = wt i
  · have := sp_wt wt ν'
    rw [sp_ws, negW] at a
    obtain ⟨k, rfl⟩ := sp_one _ (sp_abs H) ν' (by omega)
    exact h2 k fun h => b (by rw [h])
  · exact H.graded _ _ hf _ hw

/- English proof (translation)
Take `⟨f, hf, hfl⟩` from `chart_leading_weight_one H i hi`. Take `⟨g, hg, hgl⟩` from `chart_leading_weight_one H k hk`. Use `⟨f * g, SetLike.mul_mem_graded hf hg, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `Lead.mul hfl hgl`.
-/
private theorem chart_leading_weight_sum (H : IsChart0 𝒜 x wt φ) (i k : τ) (hi : (wt i).natAbs = 1) (hk : (wt k).natAbs = 1) :
    ∃ f ∈ 𝒜 (wt i + wt k), Lead wt (φ f) (Finsupp.single i 1 + Finsupp.single k 1) := by
  obtain ⟨f, hf, hfl⟩ := chart_leading_weight_one H i hi
  obtain ⟨g, hg, hgl⟩ := chart_leading_weight_one H k hk
  refine ⟨f * g, SetLike.mul_mem_graded hf hg, ?_⟩
  rw [map_mul]
  exact Lead.mul hfl hgl

/- English proof (translation)
Take `⟨f, hf, hf1, hf2⟩` from `sp_lin H i`. Set `S : Finset (τ →₀ ℕ)` to `((Finset.univ ×ˢ Finset.univ).filter (fun kl : τ × τ => (wt kl.1).natAbs = 1 ∧ (wt kl.2).natAbs = 1 ∧ wt kl.1 + wt kl.2 = wt i)).image (fun kl => Finsupp.single kl.1 1 + Finsupp.single kl.2 1)`. Establish `hnS : Finsupp.single i 1 ∉ S`. Introduce `hmem`. Take `⟨⟨k, l⟩, -, heq⟩` from `Finset.mem_image.mp hmem`.

Establish `h3` using `congrArg (Finsupp.weight (fun _ : τ => (1 : ℕ))) heq`. Simplify using `[sp_ws] at h3`. Take `⟨f', hf', hf'1, hf'2⟩` from `sp_elim (wt := wt) (φ := φ) (𝒜 (wt i)) (Finsupp.single i 1) S hnS (by`. Introduce `μ hμ _`. Take `⟨⟨k, l⟩, hkl, rfl⟩` from `Finset.mem_image.mp hμ`.

Take `⟨-, hk, hl, hsum⟩` from `Finset.mem_filter.mp hkl`. Take `⟨g, hg, hgl⟩` from `chart_leading_weight_sum H k l hk hl`. Conclude with `⟨g, hsum ▸ hg, hgl⟩) f hf hf1 (by`. Introduce `ν' e hne hnot`. Distinguish the cases in `hw : Finsupp.weight wt ν' = wt i`.

Establish `hwt` using `sp_wt wt ν'`. Rewrite `e` using `[sp_ws]`. Establish `hn : Finsupp.weight (negW wt) ν' = (-wt i).toNat` using `e`. Establish `hsgn : wt i = 2 ∨ wt i = -2`. Apply the tactic sequence `rcases Int.natAbs_eq (wt i) with h | h <;> rw [hi] at h <;> simp [h]`.

Establish `hw'` using `hw`. Rewrite `hw'` using `[hwt.1]`. Break down `sp_two (fun k => (wt k).natAbs) (sp_abs H) ν' (by` into its components or cases. Rewrite using `[hwt.2]`. Apply the tactic sequence `rcases hsgn with h | h <;> rw [h] at hn hw' <;>`.

Apply the tactic sequence `simp only [show (-(2:ℤ)).toNat = 0 from rfl, show (-(-2:ℤ)).toNat = 2 from rfl] at hn <;> omega)`. Use `with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩`. Conclude with `hf2 k (fun h => hne (by rw [h]))`. It suffices to derive a contradiction. Apply `hnot` to reduce the goal to its premises.

Rewrite `hw` using `[map_add, finsupp_weight_single_one, finsupp_weight_single_one]`. Conclude with `Finset.mem_image.mpr ⟨(k, l), Finset.mem_filter.mpr ⟨by simp, hk, hl, hw⟩, rfl⟩`. Conclude with `H.graded (wt i) f hf ν' hw)`. Use `⟨f', hf', ?_⟩` and prove the remaining obligations. Unfold `Lead`.

Conclude with `⟨sp_fil H i f' hf', hf'1, hf'2⟩`.
-/
private theorem chart_leading_weight_two [Fintype τ] (H : IsChart0 𝒜 x wt φ) (i : τ) (hi : (wt i).natAbs = 2) :
    ∃ f ∈ 𝒜 (wt i), Lead wt (φ f) (Finsupp.single i 1) := by
  classical
  obtain ⟨f, hf, hf1, hf2⟩ := sp_lin H i
  let S : Finset (τ →₀ ℕ) := ((Finset.univ ×ˢ Finset.univ).filter (fun kl : τ × τ =>
      (wt kl.1).natAbs = 1 ∧ (wt kl.2).natAbs = 1 ∧ wt kl.1 + wt kl.2 = wt i)).image
      (fun kl => Finsupp.single kl.1 1 + Finsupp.single kl.2 1)
  have hnS : Finsupp.single i 1 ∉ S := by
    intro hmem
    obtain ⟨⟨k, l⟩, -, heq⟩ := Finset.mem_image.mp hmem
    have h3 := congrArg (Finsupp.weight (fun _ : τ => (1 : ℕ))) heq
    simp [sp_ws] at h3
  obtain ⟨f', hf', hf'1, hf'2⟩ := sp_elim (wt := wt) (φ := φ) (𝒜 (wt i)) (Finsupp.single i 1) S hnS (by
      intro μ hμ _
      obtain ⟨⟨k, l⟩, hkl, rfl⟩ := Finset.mem_image.mp hμ
      obtain ⟨-, hk, hl, hsum⟩ := Finset.mem_filter.mp hkl
      obtain ⟨g, hg, hgl⟩ := chart_leading_weight_sum H k l hk hl
      exact ⟨g, hsum ▸ hg, hgl⟩) f hf hf1 (by
      intro ν' e hne hnot
      by_cases hw : Finsupp.weight wt ν' = wt i
      · have hwt := sp_wt wt ν'
        rw [sp_ws] at e
        have hn : Finsupp.weight (negW wt) ν' = (-wt i).toNat := e
        have hsgn : wt i = 2 ∨ wt i = -2 := by
          rcases Int.natAbs_eq (wt i) with h | h <;> rw [hi] at h <;> simp [h]
        have hw' := hw
        rw [hwt.1] at hw'
        rcases sp_two (fun k => (wt k).natAbs) (sp_abs H) ν' (by
          rw [hwt.2]
          rcases hsgn with h | h <;> rw [h] at hn hw' <;>
            simp only [show (-(2:ℤ)).toNat = 0 from rfl, show (-(-2:ℤ)).toNat = 2 from rfl] at hn <;> omega)
          with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
        · exact hf2 k (fun h => hne (by rw [h]))
        · exfalso
          apply hnot
          rw [map_add, finsupp_weight_single_one, finsupp_weight_single_one] at hw
          exact Finset.mem_image.mpr ⟨(k, l), Finset.mem_filter.mpr ⟨by simp, hk, hl, hw⟩, rfl⟩
      · exact H.graded (wt i) f hf ν' hw)
  refine ⟨f', hf', ?_⟩
  unfold Lead
  exact ⟨sp_fil H i f' hf', hf'1, hf'2⟩

/- English proof (translation)
Establish `hwt` using `sp_wt wt μ`. Establish `hj' : j = 2 ∨ j = -2`. Apply the tactic sequence `rcases Int.natAbs_eq j with h | h <;> rw [hj] at h <;> simp [h]`. Establish `habs : Finsupp.weight (fun k => (wt k).natAbs) μ = 2`. Rewrite using `[hwt.2, h1, h2]`.

Apply the tactic sequence `rcases hj' with h | h <;> subst h <;> decide`. Establish `hwj : Finsupp.weight wt μ = j`. Rewrite using `[hwt.1, h1, h2]`. Apply the tactic sequence `rcases hj' with h | h <;> subst h <;> decide`. Break down `sp_two (fun k => (wt k).natAbs) (sp_abs H) μ habs with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩` into its components or cases.

Rewrite `hwj` using `[finsupp_weight_single_one]`. Take `⟨f, hf, hfl⟩` from `chart_leading_weight_two H k (by rw [hwj]; exact hj)`. Conclude with `⟨f, hwj ▸ hf, hfl⟩`. Rewrite `hwj` using `[map_add, finsupp_weight_single_one, finsupp_weight_single_one]`. Take `⟨f, hf, hfl⟩` from `chart_leading_weight_sum H k l hk hl`.

Conclude with `⟨f, hwj ▸ hf, hfl⟩`.
-/
private theorem sp_l [Fintype τ] (H : IsChart0 𝒜 x wt φ) (μ : τ →₀ ℕ) (j : ℤ) (hj : j.natAbs = 2)
    (h1 : Finsupp.weight (negW wt) μ = (-j).toNat) (h2 : Finsupp.weight (posW wt) μ = j.toNat) :
    ∃ f ∈ 𝒜 j, Lead wt (φ f) μ := by
  have hwt := sp_wt wt μ
  have hj' : j = 2 ∨ j = -2 := by
    rcases Int.natAbs_eq j with h | h <;> rw [hj] at h <;> simp [h]
  have habs : Finsupp.weight (fun k => (wt k).natAbs) μ = 2 := by
    rw [hwt.2, h1, h2]
    rcases hj' with h | h <;> subst h <;> decide
  have hwj : Finsupp.weight wt μ = j := by
    rw [hwt.1, h1, h2]
    rcases hj' with h | h <;> subst h <;> decide
  rcases sp_two (fun k => (wt k).natAbs) (sp_abs H) μ habs with ⟨k, rfl⟩ | ⟨k, l, hk, hl, rfl⟩
  · rw [finsupp_weight_single_one] at hwj
    obtain ⟨f, hf, hfl⟩ := chart_leading_weight_two H k (by rw [hwj]; exact hj)
    exact ⟨f, hwj ▸ hf, hfl⟩
  · rw [map_add, finsupp_weight_single_one, finsupp_weight_single_one] at hwj
    obtain ⟨f, hf, hfl⟩ := chart_leading_weight_sum H k l hk hl
    exact ⟨f, hwj ▸ hf, hfl⟩

/- English proof (translation)
Unfold `posW negW`. Apply the tactic sequence `rcases H.wts k with h | h | h | h <;> rw [h] <;> decide`.
-/
private theorem posW_negW_le_two_and_disjoint_of_isChart0 (H : IsChart0 𝒜 x wt φ) (k : τ) :
    posW wt k ≤ 2 ∧ negW wt k ≤ 2 ∧ (negW wt k ≠ 0 → posW wt k = 0) ∧ (posW wt k ≠ 0 → negW wt k = 0) := by
  unfold posW negW
  rcases H.wts k with h | h | h | h <;> rw [h] <;> decide

/- English proof (translation)
Introduce `ν hn hp`. Proceed by induction on `a generalizing ν with`. Consider the case `zero`. Proceed by induction on `b generalizing ν with`. Consider the case `zero`.

Establish `h0 : ν = 0` using `sp_zero (fun k => (wt k).natAbs) (sp_abs H) ν (by rw [(sp_wt wt ν).2, hn, hp])`. Substitute `h0` using the available equality. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [pow_zero, mul_one]`. Conclude with `Submodule.mem_one.mpr ⟨1, map_one _⟩`.

Rewrite using `[map_one]`. Conclude with `Lead.one wt`. Consider the case `succ b ih`. Take `⟨μ, ν', rfl, hμ1, hμ2⟩` from `sp_split (posW wt) (negW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).1) (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.2 hk) b ν hp`. Rewrite `hn`, `hp` using `[map_add]`.

Take `⟨g, hg, hgl⟩` from `ih ν' (by omega) (by omega)`. Take `⟨f1, hf1, hf1l⟩` from `sp_l H μ 2 rfl (by rw [hμ2]; rfl) (by rw [hμ1]; rfl)`. Use `⟨f1 * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', mul_left_comm]`. Conclude with `Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 2 from hf1) hg`.

Rewrite using `[map_mul]`. Conclude with `Lead.mul hf1l hgl`. Consider the case `succ a ih`. Take `⟨μ, ν', rfl, hμ1, hμ2⟩` from `sp_split (negW wt) (posW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.1) (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.1 hk) a ν hn`. Rewrite `hn`, `hp` using `[map_add]`.

Take `⟨g, hg, hgl⟩` from `ih ν' (by omega) (by omega)`. Take `⟨f1, hf1, hf1l⟩` from `sp_l H μ (-2) rfl (by rw [hμ1]; rfl) (by rw [hμ2]; rfl)`. Use `⟨f1 * g, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_succ', mul_assoc]`. Conclude with `Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 (-2) from hf1) hg`.

Rewrite using `[map_mul]`. Conclude with `Lead.mul hf1l hgl`.
-/
private theorem sp_main [Fintype τ] (H : IsChart0 𝒜 x wt φ) (a b : ℕ) :
    ∀ ν : τ →₀ ℕ, Finsupp.weight (negW wt) ν = 2 * a → Finsupp.weight (posW wt) ν = 2 * b →
      ∃ f ∈ oz 𝒜 (-2) ^ a * oz 𝒜 2 ^ b, Lead wt (φ f) ν := by
  intro ν hn hp
  induction a generalizing ν with
  | zero =>
    induction b generalizing ν with
    | zero =>
      have h0 : ν = 0 := sp_zero (fun k => (wt k).natAbs) (sp_abs H) ν (by rw [(sp_wt wt ν).2, hn, hp])
      subst h0
      refine ⟨1, ?_, ?_⟩
      · simp only [pow_zero, mul_one]
        exact Submodule.mem_one.mpr ⟨1, map_one _⟩
      · rw [map_one]
        exact Lead.one wt
    | succ b ih =>
      obtain ⟨μ, ν', rfl, hμ1, hμ2⟩ := sp_split (posW wt) (negW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).1)
        (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.2 hk) b ν hp
      rw [map_add] at hn hp
      obtain ⟨g, hg, hgl⟩ := ih ν' (by omega) (by omega)
      obtain ⟨f1, hf1, hf1l⟩ := sp_l H μ 2 rfl (by rw [hμ2]; rfl) (by rw [hμ1]; rfl)
      refine ⟨f1 * g, ?_, ?_⟩
      · rw [pow_succ', mul_left_comm]
        exact Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 2 from hf1) hg
      · rw [map_mul]
        exact Lead.mul hf1l hgl
  | succ a ih =>
    obtain ⟨μ, ν', rfl, hμ1, hμ2⟩ := sp_split (negW wt) (posW wt) (fun k => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.1)
      (fun k hk => (posW_negW_le_two_and_disjoint_of_isChart0 H k).2.2.1 hk) a ν hn
    rw [map_add] at hn hp
    obtain ⟨g, hg, hgl⟩ := ih ν' (by omega) (by omega)
    obtain ⟨f1, hf1, hf1l⟩ := sp_l H μ (-2) rfl (by rw [hμ1]; rfl) (by rw [hμ2]; rfl)
    refine ⟨f1 * g, ?_, ?_⟩
    · rw [pow_succ', mul_assoc]
      exact Submodule.mul_mem_mul (show f1 ∈ oz 𝒜 (-2) from hf1) hg
    · rw [map_mul]
      exact Lead.mul hf1l hgl

end Chart

end UpperTheory.V.Alg.M

/- English proof (translation)
Introduce `O _ _ _ _ _ A _ _ 𝒜 _ _ x _ τ _ wt φ H a b ν h1 h2`. Take `⟨f, hf, hfl⟩` from `UpperTheory.V.Alg.M.sp_main H a b ν h1 h2`. Take `⟨-, hc, hz⟩` from `hfl`. Conclude with `⟨f, hf, hc, fun ν' e hne => hz ν' (e.trans h1.symm) hne⟩`.
-/
theorem UpperTheory.V.Alg.M.exists_mem_oz_pow_coeff_ne_zero_unique :
    ∀ (O : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [IsAdicComplete (maximalIdeal O) O] [CharZero O]
      (A : Type) [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜] [IsCO O (𝒜 0)] (x : A →ₐ[O] O), IsWRing 𝒜 x →
    ∀ (τ : Type) [Fintype τ] (wt : τ → ℤ) (φ : A →ₐ[O] MvPowerSeries τ (FractionRing O)), IsChart0 𝒜 x wt φ →
    ∀ (a b : ℕ) (ν : τ →₀ ℕ), Finsupp.weight (negW wt) ν = 2 * a → Finsupp.weight (posW wt) ν = 2 * b →
      ∃ f ∈ oz 𝒜 (-2) ^ a * oz 𝒜 2 ^ b, MvPowerSeries.coeff ν (φ f) ≠ 0 ∧
        ∀ ν', Finsupp.weight (negW wt) ν' = 2 * a → ν' ≠ ν → MvPowerSeries.coeff ν' (φ f) = 0 := by
  intro O _ _ _ _ _ A _ _ 𝒜 _ _ x _ τ _ wt φ H a b ν h1 h2
  obtain ⟨f, hf, hfl⟩ := UpperTheory.V.Alg.M.sp_main H a b ν h1 h2
  obtain ⟨-, hc, hz⟩ := hfl
  exact ⟨f, hf, hc, fun ν' e hne => hz ν' (e.trans h1.symm) hne⟩
