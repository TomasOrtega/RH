import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ZetaActRefl
import Development.AbelianVarietyTheory.Definitions.Foundations.MemRingOfInR
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModQPrin
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.ModJTau
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.QExpansionCoeffsInSubringRingClosed
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PermutedModularFamilySumEsymmSlashInvariant

open scoped UpperHalfPlane MatrixGroups ModularForm Manifold BigOperators
open GlobalTheory.QFam GlobalTheory.WpFam GlobalTheory.KZ GlobalTheory.FN
open ReciprocityTheory.ChartRestriction.L1 (DD jT IsMF)
open ModularForm (E₄ E₆)

noncomputable section

namespace GlobalTheory.QFam.LagrangeFam

def esymmOff {ι : Type} [Fintype ι] [DecidableEq ι] (t : ι → ℍ → ℂ) (j : ℕ) (i : ι) (τ : ℍ) : ℂ :=
  ∑ s ∈ Finset.powersetCard j (Finset.univ.erase i), ∏ l ∈ s, t l τ

def lagCoeff {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (j : ℕ) (τ : ℍ) : ℂ :=
  (-1) ^ j * ∑ i, F i τ * esymmOff t j i τ

/- English proof (translation)
Establish `h` using `congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm (s.val.map y))`. Simplify using `only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.eval_sub, Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, Polynomial.eval_mul, Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Multiset.card_map, Finset.esymm_map …`. Rewrite using `[Finset.prod_eq_multiset_prod]`. Rewrite using `[h]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [Finset.card_val]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prod_sub_eq_sum {κ : Type} (s : Finset κ) (y : κ → ℂ) (x : ℂ) :
    ∏ l ∈ s, (x - y l) = ∑ j ∈ Finset.range (s.card + 1),
      (-1) ^ j * (∑ u ∈ Finset.powersetCard j s, ∏ l ∈ u, y l) * x ^ (s.card - j) := by
  have h := congrArg (Polynomial.eval x) (Multiset.prod_X_sub_X_eq_sum_esymm (s.val.map y))
  simp only [Polynomial.eval_multiset_prod, Multiset.map_map, Function.comp_def, Polynomial.eval_sub,
    Polynomial.eval_X, Polynomial.eval_C, Polynomial.eval_finset_sum, Polynomial.eval_mul,
    Polynomial.eval_pow, Polynomial.eval_neg, Polynomial.eval_one, Multiset.card_map,
    Finset.esymm_map_val] at h
  rw [Finset.prod_eq_multiset_prod]
  rw [h]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Finset.card_val]
  ring

/- English proof (translation)
Establish `hc : ∀ i' : ι, (Finset.univ.erase i').card + 1 = Fintype.card ι` using `fun i' => by`. Rewrite using `[Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]`. Establish `: 0 < Fintype.card ι` using `Fintype.card_pos_iff.mpr ⟨i'⟩`. Use linear arithmetic over natural numbers and integers. Establish `hc' : ∀ i' : ι, (Finset.univ.erase i').card = Fintype.card ι - 1` using `fun i' => by`.

Use `hc i'` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `key : ∀ i' : ι, F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), (-1) ^ j * (F i' τ * esymmOff t j i' τ) * t i τ ^ (Fintype.card ι - 1 - j)`. Introduce `i'`. Rewrite using `[prod_sub_eq_sum, hc i', hc' i', Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Simplify using `only [esymmOff]`. Expand and normalize the polynomial expressions, which then agree. Establish `hz : ∀ i' ∈ (Finset.univ : Finset ι), i' ≠ i → F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) = 0`. Introduce `i' _ hne`.

Rewrite using `[Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩) (sub_self _), mul_zero]`. Rewrite using `[← Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hz]`. Simplify using `only [key]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Simplify using `only [lagCoeff, Finset.mul_sum, Finset.sum_mul]`.
-/
theorem lag_eval {ι : Type} [Fintype ι] [DecidableEq ι] (t F : ι → ℍ → ℂ) (i : ι) (τ : ℍ) :
    F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι), lagCoeff t F j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  have hc : ∀ i' : ι, (Finset.univ.erase i').card + 1 = Fintype.card ι := fun i' => by
    rw [Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ]
    have : 0 < Fintype.card ι := Fintype.card_pos_iff.mpr ⟨i'⟩
    omega
  have hc' : ∀ i' : ι, (Finset.univ.erase i').card = Fintype.card ι - 1 := fun i' => by
    have := hc i'; omega
  have key : ∀ i' : ι, F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) =
      ∑ j ∈ Finset.range (Fintype.card ι),
        (-1) ^ j * (F i' τ * esymmOff t j i' τ) * t i τ ^ (Fintype.card ι - 1 - j) := by
    intro i'
    rw [prod_sub_eq_sum, hc i', hc' i', Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [esymmOff]
    ring
  have hz : ∀ i' ∈ (Finset.univ : Finset ι), i' ≠ i →
      F i' τ * ∏ l ∈ Finset.univ.erase i', (t i τ - t l τ) = 0 := by
    intro i' _ hne
    rw [Finset.prod_eq_zero (i := i) (Finset.mem_erase.mpr ⟨fun h => hne h.symm, Finset.mem_univ _⟩)
      (sub_self _), mul_zero]
  rw [← Finset.sum_eq_single_of_mem i (Finset.mem_univ i) hz]
  simp only [key]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [lagCoeff, Finset.mul_sum, Finset.sum_mul]

/- English proof (translation)
Unfold `esymmOff`. Rewrite using `[Finset.sum_mul]`. Set `e : ι ≃ ι` to `Equiv.ofBijective _ (hb γ)`. Establish `he : ∀ l, e l = act l γ` using `fun l => rfl`. Use `Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s hs => ?_)` and prove the remaining obligations.

Simplify using `only [Finset.mem_powersetCard, Equiv.finsetCongr_apply, Finset.card_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun x hx => ?_, h2⟩` and prove the remaining obligations. Take `⟨y, hy, rfl⟩` from `Finset.mem_map.mp hx`.

Use `h1 hy` as an intermediate fact. Rewrite `this`, the goal using `[Finset.mem_erase]`. Use `⟨fun h => this.1 ?_, Finset.mem_univ _⟩` and prove the remaining obligations. Rewrite `h` using `[← he]`. Conclude with `e.injective h`.

Introduce and unpack `⟨h1, h2⟩`. Use `⟨fun x hx => ?_, h2⟩` and prove the remaining obligations. Use `h1 (Finset.mem_map_of_mem e.toEmbedding hx)` as an intermediate fact. Rewrite `this`, the goal using `[Finset.mem_erase]`. Conclude with `⟨fun h => this.1 (by rw [Equiv.coe_toEmbedding, h]; rfl), Finset.mem_univ _⟩`.

Establish `hc : s.card = j` using `(Finset.mem_powersetCard.mp hs).2`. Establish `h1 : UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) = ∏ _l ∈ s, UpperHalfPlane.denom γ τ ^ (-(m : ℤ))`. Rewrite using `[Finset.prod_const, hc, ← zpow_natCast, ← zpow_mul]`. Use `congr 1`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[h1, ← Finset.prod_mul_distrib, Equiv.finsetCongr_apply, Finset.prod_map]`. Conclude with `Finset.prod_congr rfl fun l _ => ht.value_mul_denom l γ τ`.
-/
theorem esymmOff_value {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m : ℕ}
    {t : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (γ : SL(2, ℤ)) (j : ℕ) (i : ι)
    (τ : ℍ) :
    esymmOff t j i (γ • τ) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
      esymmOff t j (act i γ) τ := by
  unfold esymmOff
  rw [Finset.sum_mul]
  let e : ι ≃ ι := Equiv.ofBijective _ (hb γ)
  have he : ∀ l, e l = act l γ := fun l => rfl
  refine Finset.sum_equiv e.finsetCongr (fun s => ?_) (fun s hs => ?_)
  · simp only [Finset.mem_powersetCard, Equiv.finsetCongr_apply, Finset.card_map]
    constructor
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.mp hx
      have := h1 hy
      rw [Finset.mem_erase] at this ⊢
      refine ⟨fun h => this.1 ?_, Finset.mem_univ _⟩
      rw [← he] at h
      exact e.injective h
    · rintro ⟨h1, h2⟩
      refine ⟨fun x hx => ?_, h2⟩
      have := h1 (Finset.mem_map_of_mem e.toEmbedding hx)
      rw [Finset.mem_erase] at this ⊢
      exact ⟨fun h => this.1 (by rw [Equiv.coe_toEmbedding, h]; rfl), Finset.mem_univ _⟩
  · have hc : s.card = j := (Finset.mem_powersetCard.mp hs).2
    have h1 : UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) =
        ∏ _l ∈ s, UpperHalfPlane.denom γ τ ^ (-(m : ℤ)) := by
      rw [Finset.prod_const, hc, ← zpow_natCast, ← zpow_mul]
      congr 1
      push_cast
      ring
    rw [h1, ← Finset.prod_mul_distrib, Equiv.finsetCongr_apply, Finset.prod_map]
    exact Finset.prod_congr rfl fun l _ => ht.value_mul_denom l γ τ

/- English proof (translation)
Use function extensionality and compare the values at `τ`. Rewrite using `[ModularForm.SL_slash_apply]`. Unfold `lagCoeff`. Establish `hD : UpperHalfPlane.denom γ τ ^ (-(((k + m * j : ℕ) : ℤ))) = UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ))`. Rewrite using `[← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ τ)]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[hD, mul_assoc, Finset.sum_mul]`. Use `congr 1`.

Establish `: ∀ i, F i (γ • τ) * esymmOff t j i (γ • τ) * (UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ))) = F (act i γ) τ * esymmOff t j (act i γ) τ` using `fun i => by`. Rewrite using `[← hF.value_mul_denom i γ τ, ← esymmOff_value hb ht γ j i τ]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [this]`. Conclude with `(hb γ).sum_comp (fun i => F i τ * esymmOff t j i τ)`.
-/
theorem lagCoeff_slash {ι : Type} [Fintype ι] [DecidableEq ι] {act : ι → SL(2, ℤ) → ι} {m k : ℕ}
    {t F : ι → ℍ → ℂ} (hb : ActBij act) (ht : IsFam act m t) (hF : IsFam act k F) (j : ℕ)
    (γ : SL(2, ℤ)) :
    lagCoeff t F j ∣[((k + m * j : ℕ) : ℤ)] γ = lagCoeff t F j := by
  funext τ
  rw [ModularForm.SL_slash_apply]
  unfold lagCoeff
  have hD : UpperHalfPlane.denom γ τ ^ (-(((k + m * j : ℕ) : ℤ))) =
      UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ)) := by
    rw [← zpow_add₀ (UpperHalfPlane.denom_ne_zero _ τ)]
    congr 1
    push_cast
    ring
  rw [hD, mul_assoc, Finset.sum_mul]
  congr 1
  have : ∀ i, F i (γ • τ) * esymmOff t j i (γ • τ) *
      (UpperHalfPlane.denom γ τ ^ (-(k : ℤ)) * UpperHalfPlane.denom γ τ ^ (-((m * j : ℕ) : ℤ))) =
      F (act i γ) τ * esymmOff t j (act i γ) τ := fun i => by
    rw [← hF.value_mul_denom i γ τ, ← esymmOff_value hb ht γ j i τ]
    ring
  simp only [this]
  exact (hb γ).sum_comp (fun i => F i τ * esymmOff t j i τ)

/- English proof (translation)
Introduce `ι _ _ act m k N t F _ hb ht hF hqt hqF`. Use `⟨lagCoeff t F, fun j => ⟨fun γ => lagCoeff_slash hb ht hF j γ, ?_⟩, fun i τ => lag_eval t F i τ⟩` and prove the remaining obligations. Establish `qt : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (t i)` using `fun i =>`. Set `⟨a, ha⟩` to `hqt i`. Use the proof step `⟨a, ha, fun _ => Subring.mem_top _⟩`.

Establish `qF : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (F i)` using `fun i =>`. Set `⟨a, ha⟩` to `hqF i`. Use the proof step `⟨a, ha, fun _ => Subring.mem_top _⟩`. Establish `hq : QAll (· ∈ (⊤ : Subring ℂ)) N (lagCoeff t F j)` using `QAllSubring.mul (QAllSubring.const (Subring.mem_top ((-1 : ℂ) ^ j))) (QAllSubring.sum _ fun i _ => QAllSubring.mul (qF i) (QAllSubring.sum _ fun s _ => QAllSubring.prod s fun l _ => qt l))`. Take `⟨a, ha, _⟩` from `hq`.

Conclude with `⟨a, ha⟩`.
-/
theorem lagrange_fam : ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (act : ι → SL(2, ℤ) → ι) (m k N : ℕ) (t F : ι → ℍ → ℂ), 0 < N → ActBij act → IsFam act m t → IsFam act k F → (∀ i, ∃ a, HasQ N (t i) a) → (∀ i, ∃ a, HasQ N (F i) a) → ∃ c : ℕ → ℍ → ℂ, (∀ j, (∀ γ : SL(2, ℤ), c j ∣[((k + m * j : ℕ) : ℤ)] γ = c j) ∧ ∃ a, HasQ N (c j) a) ∧ ∀ i τ, F i τ * ∏ l ∈ Finset.univ.erase i, (t i τ - t l τ) = ∑ j ∈ Finset.range (Fintype.card ι), c j τ * t i τ ^ (Fintype.card ι - 1 - j) := by
  intro ι _ _ act m k N t F _ hb ht hF hqt hqF
  refine ⟨lagCoeff t F, fun j => ⟨fun γ => lagCoeff_slash hb ht hF j γ, ?_⟩,
    fun i τ => lag_eval t F i τ⟩
  have qt : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (t i) := fun i =>
    let ⟨a, ha⟩ := hqt i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have qF : ∀ i, QAll (· ∈ (⊤ : Subring ℂ)) N (F i) := fun i =>
    let ⟨a, ha⟩ := hqF i; ⟨a, ha, fun _ => Subring.mem_top _⟩
  have hq : QAll (· ∈ (⊤ : Subring ℂ)) N (lagCoeff t F j) :=
    QAllSubring.mul (QAllSubring.const (Subring.mem_top ((-1 : ℂ) ^ j)))
      (QAllSubring.sum _ fun i _ => QAllSubring.mul (qF i)
        (QAllSubring.sum _ fun s _ => QAllSubring.prod s fun l _ => qt l))
  obtain ⟨a, ha, _⟩ := hq
  exact ⟨a, ha⟩

end GlobalTheory.QFam.LagrangeFam
