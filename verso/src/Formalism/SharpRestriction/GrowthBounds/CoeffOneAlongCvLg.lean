import Formalism.SharpRestriction.GrowthBounds.MixedCoefficientClosed

noncomputable section

open scoped BigOperators
open Classical

namespace Formalism.L2.FormalSeriesBounds

open Formalism.IncomingBounds

namespace SelfConjCharts

variable {C : Type} [Field C]

/- English proof (translation)
Rewrite using `[← tyS_Vpow hl]`. Apply `tyS_eq hl` to reduce the goal to its premises. Introduce `s`. Rewrite using `[map_sum]`. Simplify using `only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]`.

Rewrite using `[← Finset.sum_mul]`. Consider the cases of `s with`. Consider the case `zero`. Simplify using `only [pow_zero, pow_one]`. Rewrite using `[hζ.geom_sum_eq_zero (by omega), zero_mul]`.

Simplify using the standard rewrite rules. Consider the case `succ s`. Establish `h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1`. Introduce `k`. Rewrite using `[← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]`.

Simplify using `only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]`. Simplify using the standard rewrite rules. Introduce `m hm`. Rewrite using `[map_sum]`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `k _`. Rewrite using `[PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]`.
-/
theorem subst_tyS_Fs {l : ℕ} (hl : 2 ≤ l) {ζ : C} (hζ : IsPrimitiveRoot ζ l) (a : ℕ → C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ l) (tyS l fun s => (l : C) * a (s + 1)) =
      ∑ k ∈ Finset.range l, PowerSeries.rescale (ζ ^ k) (tyS l a) := by
  rw [← tyS_Vpow hl]
  apply tyS_eq hl
  · intro s
    rw [map_sum]
    simp only [PowerSeries.coeff_rescale, coeff_tyS_pow hl]
    rw [← Finset.sum_mul]
    cases s with
    | zero =>
      simp only [pow_zero, pow_one]
      rw [hζ.geom_sum_eq_zero (by omega), zero_mul]
      simp
    | succ s =>
      have h1 : ∀ k, (ζ ^ k) ^ (l ^ (s + 1)) = 1 := by
        intro k
        rw [← pow_mul, mul_comm, pow_mul, pow_succ', pow_mul, hζ.pow_eq_one, one_pow, one_pow]
      simp only [h1, Finset.sum_const, Finset.card_range, nsmul_eq_mul, mul_one]
      simp
  · intro m hm
    rw [map_sum]
    apply Finset.sum_eq_zero
    intro k _
    rw [PowerSeries.coeff_rescale, coeff_tyS_of_ne _ m hm, mul_zero]

/- English proof (translation)
Rewrite using `[map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Use extensionality with `n`. Simplify using `only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem rescale_sum_smul {ι : Type} [Fintype ι] (a : C) (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.rescale a (∑ c, u c • f c) = ∑ c, u c • PowerSeries.rescale a (f c) := by
  rw [map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  ext n
  simp only [PowerSeries.coeff_rescale, PowerSeries.coeff_smul, smul_eq_mul]
  ring

/- English proof (translation)
Establish `hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n)` using `PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])`. Rewrite using `[← PowerSeries.coe_substAlgHom hS, map_sum]`. Simplify using `only [map_smul]`.
-/
theorem subst_pow_sum_smul {n : ℕ} (hn : 0 < n) {ι : Type} [Fintype ι] (u : ι → C) (f : ι → PowerSeries C) :
    PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (∑ c, u c • f c) =
      ∑ c, u c • PowerSeries.subst ((PowerSeries.X : PowerSeries C) ^ n) (f c) := by
  have hS : PowerSeries.HasSubst ((PowerSeries.X : PowerSeries C) ^ n) :=
    PowerSeries.HasSubst.of_constantCoeff_zero' (by simp [hn.ne'])
  rw [← PowerSeries.coe_substAlgHom hS, map_sum]
  simp only [map_smul]

variable {d : ℕ} {I : Fin 2 → Type} [∀ g, Fintype (I g)] {κ : Type} [Fintype κ]

/- English proof (translation)
Rewrite using `[coeff_alongCv_low le_rfl (fun j m hm => by`. Establish `: m = 0` using `by omega`. Substitute `this` using the available equality. Rewrite using `[PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]`. Rewrite using `[Finset.sum_eq_single i]`.

Rewrite using `[hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]`. Introduce `j _ hj`. Rewrite using `[hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]`. Introduce `h`. Conclude with `hj (Finsupp.single_left_injective one_ne_zero h)`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`.
-/
theorem coeff_one_alongCv_lg (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) (i : κ) :
    PowerSeries.coeff 1 (alongCv γ (X.lg i)) = PowerSeries.coeff 1 (γ i) := by
  rw [coeff_alongCv_low le_rfl (fun j m hm => by
      have : m = 0 := by omega
      subst this
      rw [PowerSeries.coeff_zero_eq_constantCoeff_apply, hγ j]) (hB.lg0 i)]
  rw [Finset.sum_eq_single i]
  · rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_pos rfl, one_mul]
  · intro j _ hj
    rw [hB.lin i _ (by simp), MvPowerSeries.coeff_X, if_neg, zero_mul]
    intro h
    exact hj (Finsupp.single_left_injective one_ne_zero h)
  · intro h
    exact absurd (Finset.mem_univ i) h

/- English proof (translation)
Establish `h` using `coeff_tyS_pow hl a 0`. Rewrite `h` using `[pow_zero]`. Then use the resulting hypothesis.
-/
theorem coeff_one_tyS {l : ℕ} (hl : 2 ≤ l) (a : ℕ → C) : PowerSeries.coeff 1 (tyS l a) = a 0 := by
  have h := coeff_tyS_pow hl a 0
  rwa [pow_zero] at h

/- English proof (translation)
Rewrite using `[← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]`. Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]`.
-/
theorem coeff_one_of_mem (X : RawChart C d I κ) {V : VF C} (hB : Basic X V) {g : Fin 2} {γ : κ → PowerSeries C}
    (hγ : ∀ i, PowerSeries.constantCoeff (γ i) = 0) {x : ℕ → I g ⊕ JJ I g → C}
    (h1 : ∀ i : κ, alongCv γ (X.lg i) = ∑ c : I g, X.u g c i • tyS V.l (fun s => x s (Sum.inl c))) (i : κ) :
    PowerSeries.coeff 1 (γ i) = ∑ c : I g, X.u g c i * x 0 (Sum.inl c) := by
  rw [← coeff_one_alongCv_lg X hB hγ i, h1 i, map_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [PowerSeries.coeff_smul, coeff_one_tyS V.l_prime.two_le, smul_eq_mul]

end SelfConjCharts

open SelfConjCharts in
/- English proof (translation)
Introduce `C _ _ V d I _ κ _ X hB H ζ hζ g q`. Establish `hl2` using `V.l_prime.two_le`. Use `set g' : Fin 2 := 1 - g with hg'`. Apply the tactic sequence `obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0) (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one]) (fun c hc => by`. Rewrite using `[if_neg]`.

Introduce and unpack `rfl`. Conclude with `hc rfl)`. Establish `hF` using `(H g').Fm x hx`. Take `⟨z, -, hz, -, hz1, -⟩` from `id hx`. Take `⟨ε, -, hε, -, hε1, -⟩` from `hF`.

Use `⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `i`. Rewrite using `[hε1 i, hz1 i, subst_pow_sum_smul (by omega)]`. Simplify using `only [rescale_sum_smul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.smul_sum]`. Use `congr 1`. Conclude with `subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))`. Introduce `i`.

Rewrite using `[coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]`. Simplify using `only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Introduce `i`. Rewrite using `[coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree. Introduce `q'`. Conclude with `(H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _`.
-/
theorem r1sRestB_holds : OtherGroupCurvesClosed := by
  intro C _ _ V d I _ κ _ X hB H ζ hζ g q
  have hl2 := V.l_prime.two_le
  set g' : Fin 2 := 1 - g with hg'
  obtain ⟨x, hx, hx0, -⟩ := (H g').t4 (X.ty g' q) (fun c => if c = q then 1 else 0)
    (fun c => by split_ifs <;> simp [VF.Ge.zero, VF.Ge.one])
    (fun c hc => by
      rw [if_neg]
      rintro rfl
      exact hc rfl)
  have hF := (H g').Fm x hx
  obtain ⟨z, -, hz, -, hz1, -⟩ := id hx
  obtain ⟨ε, -, hε, -, hε1, -⟩ := hF
  refine ⟨z, ε, fun q' => Fs V.l x 0 (Sum.inl q'), hz, hε, ?_, ?_, ?_, ?_⟩
  · intro i
    rw [hε1 i, hz1 i, subst_pow_sum_smul (by omega)]
    simp only [rescale_sum_smul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [← Finset.smul_sum]
    congr 1
    exact subst_tyS_Fs hl2 hζ (fun s => x s (Sum.inl c))
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hz i).1) hz1 i, hx0]
    simp only [Sum.elim_inl, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
    rfl
  · intro i
    rw [coeff_one_of_mem X hB (fun i => (hε i).1) hε1 i]
    refine Finset.sum_congr rfl fun c _ => ?_
    ring
  · intro q'
    exact (H g').t2 _ ((H g').Fm x hx) 0 (fun i hi => absurd hi (Nat.not_lt_zero _)) _

end Formalism.L2.FormalSeriesBounds
