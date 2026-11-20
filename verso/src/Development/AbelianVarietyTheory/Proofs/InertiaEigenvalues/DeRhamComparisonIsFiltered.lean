import Mathlib
import Formalism.LocalRingCardinality.AdicCompletionLocal.LocTied
import Formalism.SharpRestriction.LevelLetterCocycles.LocalSituation
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.CLTateInvariantsFiniteExtensionMem
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfTateTwistInvariantFiniteExtension
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonemptyThetaDeRhamFilZeroConcretePeriod
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFinExt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.DeRhamDieudonneSpansTensorDeRhamPeriodsStatement

open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N TensorProduct
open scoped Formalism.Per

namespace GlobalTheory.DRFil

section Abstract

variable {G B M : Type} [CommRing B] [AddCommGroup M] [Module B M]
  (σ : G → B →+* B) (ρ : G → M →+ M) (F : ℤ → AddSubgroup B) (FM : ℤ → AddSubgroup M)

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert i₀ s hi₀ ih`. Establish `ih'` using `ih (by`. Introduce and unpack `⟨i, hi, κ, hκ, hmem⟩`.

Establish `hne : i₀ ≠ i` using `fun h => hi₀ (h ▸ hi)`. Use `hs ⟨i, Finset.mem_insert_of_mem hi, Function.update κ i₀ 0, fun j => ?_, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hj : j = i₀`. Substitute `hj` using the available equality. Simplify using `[(F 0).zero_mem]`.

Rewrite using `[Function.update_of_ne hj]`. Conclude with `hκ j`. Rewrite using `[Finset.erase_insert_of_ne hne, Finset.sum_insert (fun h => hi₀ (Finset.mem_of_mem_erase h)), Function.update_self, zero_smul, zero_add]`. Use `hmem using 2` and compare the differences between its conclusion and the goal. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Rewrite using `[Function.update_of_ne (fun h : j = i₀ => hi₀ (h ▸ Finset.mem_of_mem_erase hj))])`. Introduce `c b hb hsum`. Rewrite `hsum` using `[Finset.sum_insert hi₀]`. Establish `h0 : b i₀ ∈ F (c - k i₀ + 1)`. Assume the negation of the conclusion as `hn`.

Take `⟨β, hβ, hβ1⟩` from `hinv _ _ (hb i₀ (Finset.mem_insert_self _ _)) hn`. Establish `he : ∀ i ∈ s, β * b i ∈ F (k i₀ - k i)` using `fun i hi => by`. Use `hmul _ _ _ _ hβ (hb i (Finset.mem_insert_of_mem hi))` as an intermediate fact. Rewrite `this` using `[show -(c - k i₀) + (c - k i) = k i₀ - k i by ring]`. Then use the resulting hypothesis. Establish `hz : d i₀ + ∑ i ∈ s, (β * b i) • d i ∈ FM (k i₀ + 1)`.

Establish `h1` using `hsmul _ _ _ _ hβ hsum`. Rewrite `h1` using `[show -(c - k i₀) + (c + 1) = k i₀ + 1 by ring]`. Establish `h2` using `hsmul _ _ _ _ hβ1 (hdk i₀)`. Rewrite `h2` using `[add_comm]`. Use `(FM _).sub_mem h1 h2 using 1` and compare the differences between its conclusion and the goal.

Simplify using `only [smul_add, Finset.smul_sum, mul_smul, sub_smul, one_smul]`. Normalize the expressions using the abelian group laws. Establish `hg : ∀ g, ∀ i ∈ s, σ g (β * b i) - β * b i ∈ F (k i₀ - k i + 1)` using `fun g => ih' (k i₀) (fun i => σ g (β * b i) - β * b i) (fun i hi => (F _).sub_mem (hFG _ _ _ (he i hi)) (he i hi)) (by`. Use `(FM _).sub_mem (hMG g _ _ hz) hz using 1` and compare the differences between its conclusion and the goal. Simplify using `only [map_add, map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib]`.

Use the proof step `abel)`. Establish `hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (k i₀ ≠ k i → κ = 0) ∧ (i ∈ s → β * b i - κ ∈ F (k i₀ - k i + 1))` using `fun i => by`. Distinguish the cases in `hi : i ∈ s`. Take `⟨κ, h1, h2, h3, h4⟩` from `hT _ _ (he i hi) (fun g => hg g i hi)`. Conclude with `⟨κ, h1, h2, fun h => h3 (sub_ne_zero.2 h), fun _ => h4⟩`.

Conclude with `⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩`. Use `choose κ h1 h2 h3 h4 using hκ`. Use `hs ⟨i₀, Finset.mem_insert_self _ _, κ, fun j => ⟨h1 j, h2 j, h3 j⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.erase_insert hi₀]`. Establish `h5 : ∑ i ∈ s, (β * b i - κ i) • d i ∈ FM (k i₀ + 1)` using `(FM _).sum_mem fun i hi => by`.

Use `hsmul _ _ _ _ (h4 i hi) (hdk i)` as an intermediate fact. Rewrite `this` using `[show k i₀ - k i + 1 + k i = k i₀ + 1 by ring]`. Then use the resulting hypothesis. Use `(FM _).sub_mem hz h5 using 1` and compare the differences between its conclusion and the goal. Simplify using `only [sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.

Establish `h1 : ∑ i ∈ s, b i • d i ∈ FM (c + 1)`. Use `hsmul _ _ _ _ h0 (hdk i₀)` as an intermediate fact. Rewrite `this` using `[show c - k i₀ + 1 + k i₀ = c + 1 by ring]`. Simplify using `using (FM _).sub_mem hsum this`. Introduce `i hi`.

Break down `Finset.mem_insert.1 hi with rfl | hi` into its components or cases. Conclude with `h0`. Conclude with `ih' c b (fun j hj => hb j (Finset.mem_insert_of_mem hj)) h1 i hi`.
-/
theorem graded_indep
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (s : Finset ι)
    (hs : ¬ ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)) :
    ∀ (c : ℤ) (b : ι → B), (∀ i ∈ s, b i ∈ F (c - k i)) → ∑ i ∈ s, b i • d i ∈ FM (c + 1) →
      ∀ i ∈ s, b i ∈ F (c - k i + 1) := by
  induction s using Finset.induction_on with
  | empty => simp
  | insert i₀ s hi₀ ih =>
    have ih' := ih (by
      rintro ⟨i, hi, κ, hκ, hmem⟩
      have hne : i₀ ≠ i := fun h => hi₀ (h ▸ hi)
      refine hs ⟨i, Finset.mem_insert_of_mem hi, Function.update κ i₀ 0, fun j => ?_, ?_⟩
      · by_cases hj : j = i₀
        · subst hj
          simp [(F 0).zero_mem]
        · rw [Function.update_of_ne hj]
          exact hκ j
      · rw [Finset.erase_insert_of_ne hne,
          Finset.sum_insert (fun h => hi₀ (Finset.mem_of_mem_erase h)), Function.update_self, zero_smul,
          zero_add]
        convert hmem using 2
        refine Finset.sum_congr rfl fun j hj => ?_
        rw [Function.update_of_ne (fun h : j = i₀ => hi₀ (h ▸ Finset.mem_of_mem_erase hj))])
    intro c b hb hsum
    rw [Finset.sum_insert hi₀] at hsum
    have h0 : b i₀ ∈ F (c - k i₀ + 1) := by
      by_contra hn
      obtain ⟨β, hβ, hβ1⟩ := hinv _ _ (hb i₀ (Finset.mem_insert_self _ _)) hn
      have he : ∀ i ∈ s, β * b i ∈ F (k i₀ - k i) := fun i hi => by
        have := hmul _ _ _ _ hβ (hb i (Finset.mem_insert_of_mem hi))
        rwa [show -(c - k i₀) + (c - k i) = k i₀ - k i by ring] at this
      have hz : d i₀ + ∑ i ∈ s, (β * b i) • d i ∈ FM (k i₀ + 1) := by
        have h1 := hsmul _ _ _ _ hβ hsum
        rw [show -(c - k i₀) + (c + 1) = k i₀ + 1 by ring] at h1
        have h2 := hsmul _ _ _ _ hβ1 (hdk i₀)
        rw [add_comm] at h2
        convert (FM _).sub_mem h1 h2 using 1
        simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, one_smul]
        abel
      have hg : ∀ g, ∀ i ∈ s, σ g (β * b i) - β * b i ∈ F (k i₀ - k i + 1) := fun g =>
        ih' (k i₀) (fun i => σ g (β * b i) - β * b i)
          (fun i hi => (F _).sub_mem (hFG _ _ _ (he i hi)) (he i hi)) (by
            convert (FM _).sub_mem (hMG g _ _ hz) hz using 1
            simp only [map_add, map_sum, hρ, hd, sub_smul, Finset.sum_sub_distrib]
            abel)
      have hκ : ∀ i, ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (k i₀ ≠ k i → κ = 0) ∧
          (i ∈ s → β * b i - κ ∈ F (k i₀ - k i + 1)) := fun i => by
        by_cases hi : i ∈ s
        · obtain ⟨κ, h1, h2, h3, h4⟩ := hT _ _ (he i hi) (fun g => hg g i hi)
          exact ⟨κ, h1, h2, fun h => h3 (sub_ne_zero.2 h), fun _ => h4⟩
        · exact ⟨0, (F 0).zero_mem, fun g => map_zero _, fun _ => rfl, fun h => (hi h).elim⟩
      choose κ h1 h2 h3 h4 using hκ
      refine hs ⟨i₀, Finset.mem_insert_self _ _, κ, fun j => ⟨h1 j, h2 j, h3 j⟩, ?_⟩
      rw [Finset.erase_insert hi₀]
      have h5 : ∑ i ∈ s, (β * b i - κ i) • d i ∈ FM (k i₀ + 1) :=
        (FM _).sum_mem fun i hi => by
          have := hsmul _ _ _ _ (h4 i hi) (hdk i)
          rwa [show k i₀ - k i + 1 + k i = k i₀ + 1 by ring] at this
      convert (FM _).sub_mem hz h5 using 1
      simp only [sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 : ∑ i ∈ s, b i • d i ∈ FM (c + 1) := by
      have := hsmul _ _ _ _ h0 (hdk i₀)
      rw [show c - k i₀ + 1 + k i₀ = c + 1 by ring] at this
      simpa using (FM _).sub_mem hsum this
    intro i hi
    rcases Finset.mem_insert.1 hi with rfl | hi
    · exact h0
    · exact ih' c b (fun j hj => hb j (Finset.mem_insert_of_mem hj)) h1 i hi

def gens (a : ℤ) : Set M :=
  {x | ∃ (k : ℤ) (b : B) (d : M), (∀ g, ρ g d = d) ∧ d ∈ FM k ∧ b ∈ F (a - k) ∧ x = b • d}

/- English proof (translation)
Take `⟨m, f, x, rfl⟩` from `Submodule.mem_span_set'.1 hy`. Use `choose k b d h1 h2 h3 h4 using fun i => (x i).2`. Use `⟨m, k, fun i => f i • b i, d, fun i => ⟨h1 i, h2 i, (F _).zsmul_mem (h3 i) _⟩, ?_⟩` and prove the remaining obligations. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h4, smul_assoc]`.
-/
theorem exists_rep_of_mem_span {a : ℤ} {y : M} (hy : y ∈ Submodule.span ℤ (gens ρ F FM a)) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → B) (d : Fin m → M),
      (∀ i, (∀ g, ρ g (d i) = d i) ∧ d i ∈ FM (k i) ∧ b i ∈ F (a - k i)) ∧ y = ∑ i, b i • d i := by
  obtain ⟨m, f, x, rfl⟩ := Submodule.mem_span_set'.1 hy
  choose k b d h1 h2 h3 h4 using fun i => (x i).2
  refine ⟨m, k, fun i => f i • b i, d, fun i => ⟨h1 i, h2 i, (F _).zsmul_mem (h3 i) _⟩, ?_⟩
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [h4, smul_assoc]

/- English proof (translation)
Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `s hn b hb hsum`. Distinguish the cases in `hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧ d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)`. Take `⟨i, hi, κ, hκ, hmem⟩` from `hs`.

Establish `heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) + ∑ j ∈ s.erase i, (b j - b i * κ j) • d j`. Rewrite using `[← Finset.add_sum_erase s _ hi]`. Simplify using `only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws. Establish `h1` using `hsmul _ _ _ _ (hb i hi) hmem`.

Rewrite `h1` using `[show c - k i + (k i + 1) = c + 1 by ring]`. Rewrite `hsum`, the goal using `[heq]`. Use `Submodule.add_mem _ (Submodule.subset_span ⟨k i + 1, b i, _, fun g => ?_, hmem, ?_, rfl⟩) (ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) _ rfl _ (fun j hj => ?_) ?_)` and prove the remaining obligations. Simplify using `only [map_add, map_sum, hρ, hd, (hκ _).2.1]`. Rewrite using `[show c + 1 - (k i + 1) = c - k i by ring]`.

Conclude with `hb i hi`. Use `(F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_` and prove the remaining obligations. Distinguish the cases in `hk : k i = k j`. Use `hmul _ _ _ _ (hb i hi) (hκ j).1` as an intermediate fact. Rewrite `this` using `[add_zero, hk]`. Then use the resulting hypothesis.

Rewrite using `[(hκ j).2.2 hk, mul_zero]`. Conclude with `(F _).zero_mem`. Simplify using `using (FM _).sub_mem hsum h1`. Use `graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c b hb hsum` as an intermediate fact. Use `Submodule.sum_mem _ fun i hi => Submodule.subset_span ⟨k i, b i, d i, hd i, hdk i, ?_, rfl⟩` and prove the remaining obligations.

Rewrite using `[show c + 1 - k i = c - k i + 1 by ring]`. Conclude with `this i hi`.
-/
theorem step
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    {ι : Type} [DecidableEq ι] (k : ι → ℤ) (d : ι → M) (hd : ∀ i g, ρ g (d i) = d i)
    (hdk : ∀ i, d i ∈ FM (k i)) (c : ℤ) (n : ℕ) :
    ∀ (s : Finset ι), s.card = n → ∀ b : ι → B, (∀ i ∈ s, b i ∈ F (c - k i)) →
      ∑ i ∈ s, b i • d i ∈ FM (c + 1) →
      ∑ i ∈ s, b i • d i ∈ Submodule.span ℤ (gens ρ F FM (c + 1)) := by
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro s hn b hb hsum
  by_cases hs : ∃ i ∈ s, ∃ κ : ι → B, (∀ j, κ j ∈ F 0 ∧ (∀ g, σ g (κ j) = κ j) ∧ (k i ≠ k j → κ j = 0)) ∧
      d i + ∑ j ∈ s.erase i, κ j • d j ∈ FM (k i + 1)
  · obtain ⟨i, hi, κ, hκ, hmem⟩ := hs
    have heq : ∑ j ∈ s, b j • d j = b i • (d i + ∑ j ∈ s.erase i, κ j • d j) +
        ∑ j ∈ s.erase i, (b j - b i * κ j) • d j := by
      rw [← Finset.add_sum_erase s _ hi]
      simp only [smul_add, Finset.smul_sum, mul_smul, sub_smul, Finset.sum_sub_distrib]
      abel
    have h1 := hsmul _ _ _ _ (hb i hi) hmem
    rw [show c - k i + (k i + 1) = c + 1 by ring] at h1
    rw [heq] at hsum ⊢
    refine Submodule.add_mem _ (Submodule.subset_span ⟨k i + 1, b i, _, fun g => ?_, hmem, ?_, rfl⟩)
      (ih _ (hn ▸ Finset.card_erase_lt_of_mem hi) _ rfl _ (fun j hj => ?_) ?_)
    · simp only [map_add, map_sum, hρ, hd, (hκ _).2.1]
    · rw [show c + 1 - (k i + 1) = c - k i by ring]
      exact hb i hi
    · refine (F _).sub_mem (hb j (Finset.mem_of_mem_erase hj)) ?_
      by_cases hk : k i = k j
      · have := hmul _ _ _ _ (hb i hi) (hκ j).1
        rwa [add_zero, hk] at this
      · rw [(hκ j).2.2 hk, mul_zero]
        exact (F _).zero_mem
    · simpa using (FM _).sub_mem hsum h1
  · have := graded_indep σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k d hd hdk s hs c b hb hsum
    refine Submodule.sum_mem _ fun i hi => Submodule.subset_span ⟨k i, b i, d i, hd i, hdk i, ?_, rfl⟩
    rw [show c + 1 - k i = c - k i + 1 by ring]
    exact this i hi

/- English proof (translation)
Apply `exists_rep_of_mem_span` to reduce the goal to its premises. Use `choose k hk using fun i => hMe (d i)`. Use `choose r hr using fun i => hFe (b i)`. Take `⟨c₀, hc₀⟩` from `(Set.finite_range fun i => r i + k i).bddBelow`. Establish `hle : min c₀ a ≤ a` using `min_le_right _ _`.

Establish `key : ∀ c, min c₀ a ≤ c → c ≤ a → y ∈ Submodule.span ℤ (gens ρ F FM c)`. Introduce `c hc`. Proceed by induction on `c, hc using Int.le_induction with`. Consider the case `base`. Introduce `_`.

Rewrite using `[hsum]`. Use `Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨k i, b i, d i, hd i, hk i, ?_, rfl⟩` and prove the remaining obligations. Use `hFa ?_ (hr i)` and prove the remaining obligations. Establish `h1 : c₀ ≤ r i + k i` using `hc₀ ⟨i, rfl⟩`. Establish `h2` using `min_le_left c₀ a`.

Use linear arithmetic over natural numbers and integers. Consider the case `succ c hc ih`. Introduce `hca`. Take `⟨m', k', b', d', h, e⟩` from `exists_rep_of_mem_span ρ F FM (ih (by omega))`. Rewrite using `[e]`.

Conclude with `step σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d' (fun i => (h i).1) (fun i => (h i).2.1) c _ Finset.univ rfl b' (fun i _ => (h i).2.2) (e ▸ hMa hca hy)`. Conclude with `key a hle le_rfl`.
-/
theorem filtered
    (hρ : ∀ g (b : B) (m : M), ρ g (b • m) = σ g b • ρ g m)
    (hmul : ∀ a b x y, x ∈ F a → y ∈ F b → x * y ∈ F (a + b))
    (hsmul : ∀ a b x y, x ∈ F a → y ∈ FM b → x • y ∈ FM (a + b))
    (hFG : ∀ g a x, x ∈ F a → σ g x ∈ F a)
    (hMG : ∀ g a x, x ∈ FM a → ρ g x ∈ FM a)
    (hinv : ∀ a b, b ∈ F a → b ∉ F (a + 1) → ∃ β ∈ F (-a), β * b - 1 ∈ F 1)
    (hT : ∀ n e, e ∈ F n → (∀ g, σ g e - e ∈ F (n + 1)) →
      ∃ κ ∈ F 0, (∀ g, σ g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧ e - κ ∈ F (n + 1))
    (hFa : Antitone F) (hMa : Antitone FM) (hFe : ∀ x, ∃ a, x ∈ F a) (hMe : ∀ x, ∃ a, x ∈ FM a)
    (a : ℤ) (y : M) (hy : y ∈ FM a) (m : ℕ) (b : Fin m → B) (d : Fin m → M)
    (hd : ∀ i g, ρ g (d i) = d i) (hsum : y = ∑ i, b i • d i) :
    ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → B) (d : Fin m → M),
      (∀ i, (∀ g, ρ g (d i) = d i) ∧ d i ∈ FM (k i) ∧ b i ∈ F (a - k i)) ∧ y = ∑ i, b i • d i := by
  apply exists_rep_of_mem_span
  choose k hk using fun i => hMe (d i)
  choose r hr using fun i => hFe (b i)
  obtain ⟨c₀, hc₀⟩ := (Set.finite_range fun i => r i + k i).bddBelow
  have hle : min c₀ a ≤ a := min_le_right _ _
  have key : ∀ c, min c₀ a ≤ c → c ≤ a → y ∈ Submodule.span ℤ (gens ρ F FM c) := by
    intro c hc
    induction c, hc using Int.le_induction with
    | base =>
      intro _
      rw [hsum]
      refine Submodule.sum_mem _ fun i _ => Submodule.subset_span ⟨k i, b i, d i, hd i, hk i, ?_, rfl⟩
      refine hFa ?_ (hr i)
      have h1 : c₀ ≤ r i + k i := hc₀ ⟨i, rfl⟩
      have h2 := min_le_left c₀ a
      omega
    | succ c hc ih =>
      intro hca
      obtain ⟨m', k', b', d', h, e⟩ := exists_rep_of_mem_span ρ F FM (ih (by omega))
      rw [e]
      exact step σ ρ F FM hρ hmul hsmul hFG hMG hinv hT k' d' (fun i => (h i).1) (fun i => (h i).2.1) c _
        Finset.univ rfl b' (fun i _ => (h i).2.2) (e ▸ hMa hca hy)
  exact key a hle le_rfl

end Abstract

section Periods

variable {l : ℕ} [Fact l.Prime] {P : LocPrime l} {AI : LocAinf l P}

/- English proof (translation)
Rewrite using `[← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]`.
-/
theorem fil_iff (K K' : FinExt l) (a : ℤ) (x : P.R.BdR) :
    x ∈ (P.PD K).Fil a ↔ x ∈ (P.PD K').Fil a := by
  rw [← SetLike.mem_coe, P.PD_Fil K K' a, SetLike.mem_coe]

/- English proof (translation)
Rewrite using `[Algebra.algebraMap_eq_smul_one]`. Conclude with `Submodule.smul_mem _ _ (P.PD K).one_mem`.
-/
theorem alg_mem_fil_zero (K : FinExt l) (c : ↥K.1) : algebraMap ↥K.1 P.R.BdR c ∈ (P.PD K).Fil 0 := by
  rw [Algebra.algebraMap_eq_smul_one]
  exact Submodule.smul_mem _ _ (P.PD K).one_mem

/- English proof (translation)
Use `(P.PD K).t_unit` as an intermediate fact. Rewrite `this` using `[P.period_datum_t_eq]`. Conclude with `this.map _`.
-/
theorem isUnit_cyclotomicPeriod_deRham (K : FinExt l) : IsUnit (P.ιB P.tB) := by
  have := (P.PD K).t_unit
  rw [P.period_datum_t_eq] at this
  exact this.map _

/- English proof (translation)
Establish `h1 : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔ (T : P.R.BdR) * x ∈ (P.PD K).Fil (a + 1)`. Introduce `a x`. Rewrite using `[fil_iff K (MainNotions.LocalSituation.botExt l) (a + 1), Θ.fil_succ_iff_mul_t, ← hT, fil_iff K (MainNotions.LocalSituation.botExt l)]`. Use `⟨fun h => ⟨x, h, rfl⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy, e⟩`.

Rewrite using `[T.isUnit.mul_left_cancel e]` and apply the resulting hypothesis. Proceed by induction on `n using Int.induction_on with`. Consider the case `zero => simp`. Consider the case `succ n ih`. Introduce `a x`.

Rewrite using `[ih, h1, ← mul_assoc, ← Units.val_mul, ← zpow_one_add, add_assoc, add_comm 1]`. Consider the case `pred n ih`. Introduce `a x`. Rewrite using `[ih, h1 (a + (-(n : ℤ) - 1)), ← mul_assoc, ← Units.val_mul, ← zpow_one_add]`. Simplify using `[add_assoc]`.
-/
theorem fil_shift (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) (T : P.R.BdRˣ) (hT : (T : P.R.BdR) = P.ιB P.tB)
    (n : ℤ) : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔
      ((T ^ n : P.R.BdRˣ) : P.R.BdR) * x ∈ (P.PD K).Fil (a + n) := by
  have h1 : ∀ (a : ℤ) (x : P.R.BdR), x ∈ (P.PD K).Fil a ↔ (T : P.R.BdR) * x ∈ (P.PD K).Fil (a + 1) := by
    intro a x
    rw [fil_iff K (MainNotions.LocalSituation.botExt l) (a + 1), Θ.fil_succ_iff_mul_t, ← hT, fil_iff K (MainNotions.LocalSituation.botExt l)]
    refine ⟨fun h => ⟨x, h, rfl⟩, ?_⟩
    rintro ⟨y, hy, e⟩
    rwa [T.isUnit.mul_left_cancel e]
  induction n using Int.induction_on with
  | zero => simp
  | succ n ih =>
    intro a x
    rw [ih, h1, ← mul_assoc, ← Units.val_mul, ← zpow_one_add, add_assoc, add_comm 1]
  | pred n ih =>
    intro a x
    rw [ih, h1 (a + (-(n : ℤ) - 1)), ← mul_assoc, ← Units.val_mul, ← zpow_one_add]
    simp [add_assoc]

/- English proof (translation)
Rewrite `hx`, `hy`, the goal using `[fil_iff K (MainNotions.LocalSituation.botExt l)]`. Establish `hxy` using `Submodule.sub_mem _ hx hy`. Establish `h` using `Θ.θ_add _ hxy _ hy`. Rewrite `h` using `[sub_add_cancel]`. Rewrite using `[← Θ.θ_ker _ hxy, h]`.

Simplify using the standard rewrite rules.
-/
theorem theta_sub_iff (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) {x y : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil 0) (hy : y ∈ (P.PD K).Fil 0) :
    x - y ∈ (P.PD K).Fil 1 ↔ Θ.θ x = Θ.θ y := by
  rw [fil_iff K (MainNotions.LocalSituation.botExt l)] at hx hy ⊢
  have hxy := Submodule.sub_mem _ hx hy
  have h := Θ.θ_add _ hxy _ hy
  rw [sub_add_cancel] at h
  rw [← Θ.θ_ker _ hxy, h]
  simp

/- English proof (translation)
The claim follows from `Θ.θ_mul _ ((fil_iff _ _ _ _).1 hx) _ ((fil_iff _ _ _ _).1 hy)`.
-/
theorem theta_mul (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) {x y : P.R.BdR}
    (hx : x ∈ (P.PD K).Fil 0) (hy : y ∈ (P.PD K).Fil 0) : Θ.θ (x * y) = Θ.θ x * Θ.θ y :=
  Θ.θ_mul _ ((fil_iff _ _ _ _).1 hx) _ ((fil_iff _ _ _ _).1 hy)

/- English proof (translation)
The claim follows from `(Θ.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)`.
-/
theorem theta_zero (Θ : MainNotions.LocalSituation.ThetaL P AI) : Θ.θ 0 = 0 :=
  (Θ.θ_ker 0 (Submodule.zero_mem _)).2 (Submodule.zero_mem _)

/- English proof (translation)
Take `⟨T, hT⟩` from `isUnit_cyclotomicPeriod_deRham (P := P) K`. Rewrite `hb`, `hn` using `[fil_shift Θ K T hT (-a)]`. Rewrite `hb` using `[add_neg_cancel]`. Rewrite `hn` using `[show a + 1 + -a = 1 by ring, ← sub_zero (_ * b), theta_sub_iff Θ K hb (Submodule.zero_mem _), theta_zero]`. Take `⟨u, hu, e⟩` from `Θ.θ_onto (Θ.θ (((T ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b))⁻¹`.

Rewrite `hu` using `[fil_iff _ K]`. Use `⟨((T ^ (-a) : P.R.BdRˣ) : P.R.BdR) * u, ?_, ?_⟩` and prove the remaining obligations. Use `(fil_shift Θ K T hT (-a) 0 u).1 hu` as an intermediate fact. Rewrite `this` using `[zero_add]`. Then use the resulting hypothesis. Establish `h0` using `(P.PD K).Fil_mul _ _ _ _ hu hb`.

Rewrite `h0` using `[add_zero]`. Rewrite using `[mul_comm _ u, mul_assoc, theta_sub_iff Θ K h0 (P.PD K).one_mem, theta_mul Θ K hu hb, e, Θ.θ_one, inv_mul_cancel₀ hn]`.
-/
theorem graded_inv (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) (a : ℤ) (b : P.R.BdR)
    (hb : b ∈ (P.PD K).Fil a) (hn : b ∉ (P.PD K).Fil (a + 1)) :
    ∃ β ∈ (P.PD K).Fil (-a), β * b - 1 ∈ (P.PD K).Fil 1 := by
  obtain ⟨T, hT⟩ := isUnit_cyclotomicPeriod_deRham (P := P) K
  rw [fil_shift Θ K T hT (-a)] at hb hn
  rw [add_neg_cancel] at hb
  rw [show a + 1 + -a = 1 by ring, ← sub_zero (_ * b), theta_sub_iff Θ K hb (Submodule.zero_mem _),
    theta_zero] at hn
  obtain ⟨u, hu, e⟩ := Θ.θ_onto (Θ.θ (((T ^ (-a) : P.R.BdRˣ) : P.R.BdR) * b))⁻¹
  rw [fil_iff _ K] at hu
  refine ⟨((T ^ (-a) : P.R.BdRˣ) : P.R.BdR) * u, ?_, ?_⟩
  · have := (fil_shift Θ K T hT (-a) 0 u).1 hu
    rwa [zero_add] at this
  · have h0 := (P.PD K).Fil_mul _ _ _ _ hu hb
    rw [add_zero] at h0
    rw [mul_comm _ u, mul_assoc, theta_sub_iff Θ K h0 (P.PD K).one_mem, theta_mul Θ K hu hb, e,
      Θ.θ_one, inv_mul_cancel₀ hn]

/- English proof (translation)
Establish `hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 → Θ.θ ((P.PD K).actdR g x) = Per.σC (g : GQ l) (Θ.θ x)` using `fun g x hx => by`. Rewrite using `[P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 hx), GlobalTheory.MemLoc.locAinf_actC]`. Distinguish the cases in `hn : n = 0`. Substitute `hn` using the available equality. Rewrite `hg`, the goal using `[zero_add]`.

Take `⟨y, hy, ey⟩` from `GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by`. Rewrite using `[← hact ⟨g, hg'⟩ e he]`. Conclude with `(theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg _))`. Use `⟨algebraMap ↥K.1 P.R.BdR ⟨y, hy⟩, alg_mem_fil_zero K _, fun g => AlgEquiv.commutes _ _, fun h => (h rfl).elim, ?_⟩` and prove the remaining obligations. Rewrite using `[theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]`.

Conclude with `(Θ.θ_Om y).symm`. Use `⟨0, Submodule.zero_mem _, fun g => map_zero _, fun _ => rfl, ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `GlobalTheory.MemLoc.FitsEx.exists_fits l P AI TT`. Take `⟨T, hT⟩` from `isUnit_cyclotomicPeriod_deRham (P := P) K`. Take `⟨u, rfl⟩ : ∃ u, e = ((T ^ n : P.R.BdRˣ) : P.R.BdR) * u` from `⟨((T ^ n)⁻¹ : P.R.BdRˣ) * e, by rw [Units.mul_inv_cancel_left]⟩`.

Establish `hu : u ∈ (P.PD K).Fil 0`. Rewrite using `[fil_shift Θ K T hT n, zero_add]`. Conclude with `he`. Rewrite using `[sub_zero, add_comm, ← fil_shift Θ K T hT n, ← sub_zero u, theta_sub_iff Θ K hu (Submodule.zero_mem _), theta_zero]`. Use `GlobalTheory.MemLoc.tate_twist_invariants l C K n _ hn fun g hg' => ?_` and prove the remaining obligations.

Set `g' : ↥(GK K)` to `⟨g, hg'⟩`. Set `χ : ℚ_[l]ˣ` to `(P.PD K).χ g'`. Establish `h1 : Units.map ((P.PD K).actdR g' : P.R.BdR →* P.R.BdR) T = Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) χ * T`. Use `ext`. Establish `h2` using `(P.PD K).ι_comm g' (P.PD K).t`.

Rewrite `h2` using `[(P.PD K).t_act, P.PD_ι, P.PD_ι, P.period_datum_t_eq, map_smul, ← hT, Algebra.smul_def]`. Conclude with `h2.symm`. Establish `h2 : (P.PD K).actdR g' ((T ^ n : P.R.BdRˣ) : P.R.BdR) = ((T ^ n : P.R.BdRˣ) : P.R.BdR) * algebraMap ℚ_[l] P.R.BdR ((χ : ℚ_[l]) ^ n)`. Establish `h3` using `congrArg (fun x : P.R.BdRˣ => ((x ^ n : P.R.BdRˣ) : P.R.BdR)) h1`. Simplify using `only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3`.

Rewrite using `[mul_comm, ← Units.val_zpow_eq_zpow_val]`. Conclude with `h3`. Establish `h3` using `hg g'`. Establish `h4 : algebraMap ℚ_[l] P.R.BdR ((χ : ℚ_[l]) ^ n) ∈ (P.PD K).Fil 0`. Rewrite using `[IsScalarTower.algebraMap_apply ℚ_[l] ↥K.1 P.R.BdR]`.

Conclude with `alg_mem_fil_zero K _`. Establish `h5` using `(P.PD K).Fil_G g' _ _ hu`. Establish `h6` using `(P.PD K).Fil_mul _ _ _ _ h4 h5`. Rewrite `h6` using `[add_zero]`. Rewrite `h3` using `[map_mul, h2, mul_assoc, ← mul_sub, add_comm, ← fil_shift Θ K T hT n, theta_sub_iff Θ K h6 hu, theta_mul Θ K h4 h5, hact _ _ hu, IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, Θ.θ_Om]`.

Rewrite using `[← hC.χ, ← map_zpow₀, mul_comm]`. Use `Eq.trans ?_ h3` and prove the remaining obligations. Use `congr 1`. Rewrite using `[show ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = χ from (P.PD_χ K g').symm]`. Conclude with `IsScalarTower.algebraMap_apply ℚ_[l] (Om l) ℂ_[l] _`.
-/
theorem graded_invariants (TT : LocTied l P AI) (Θ : MainNotions.LocalSituation.ThetaL P AI) (K : FinExt l) (n : ℤ)
    (e : P.R.BdR) (he : e ∈ (P.PD K).Fil n)
    (hg : ∀ g, (P.PD K).actdR g e - e ∈ (P.PD K).Fil (n + 1)) :
    ∃ κ ∈ (P.PD K).Fil 0, (∀ g, (P.PD K).actdR g κ = κ) ∧ (n ≠ 0 → κ = 0) ∧
      e - κ ∈ (P.PD K).Fil (n + 1) := by
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), x ∈ (P.PD K).Fil 0 →
      Θ.θ ((P.PD K).actdR g x) = Per.σC (g : GQ l) (Θ.θ x) := fun g x hx => by
    rw [P.PD_actdR, Θ.θ_act _ _ ((fil_iff _ _ _ _).1 hx), GlobalTheory.MemLoc.locAinf_actC]
  by_cases hn : n = 0
  · subst hn
    rw [zero_add] at hg ⊢
    obtain ⟨y, hy, ey⟩ := GlobalTheory.MemLoc.invariants_finExt l K (Θ.θ e) (fun g hg' => by
      rw [← hact ⟨g, hg'⟩ e he]
      exact (theta_sub_iff Θ K ((P.PD K).Fil_G _ _ _ he) he).1 (hg _))
    refine ⟨algebraMap ↥K.1 P.R.BdR ⟨y, hy⟩, alg_mem_fil_zero K _, fun g => AlgEquiv.commutes _ _,
      fun h => (h rfl).elim, ?_⟩
    rw [theta_sub_iff Θ K he (alg_mem_fil_zero K _), ← ey]
    exact (Θ.θ_Om y).symm
  · refine ⟨0, Submodule.zero_mem _, fun g => map_zero _, fun _ => rfl, ?_⟩
    obtain ⟨C, hC⟩ := GlobalTheory.MemLoc.FitsEx.exists_fits l P AI TT
    obtain ⟨T, hT⟩ := isUnit_cyclotomicPeriod_deRham (P := P) K
    obtain ⟨u, rfl⟩ : ∃ u, e = ((T ^ n : P.R.BdRˣ) : P.R.BdR) * u :=
      ⟨((T ^ n)⁻¹ : P.R.BdRˣ) * e, by rw [Units.mul_inv_cancel_left]⟩
    have hu : u ∈ (P.PD K).Fil 0 := by
      rw [fil_shift Θ K T hT n, zero_add]
      exact he
    rw [sub_zero, add_comm, ← fil_shift Θ K T hT n, ← sub_zero u,
      theta_sub_iff Θ K hu (Submodule.zero_mem _), theta_zero]
    refine GlobalTheory.MemLoc.tate_twist_invariants l C K n _ hn fun g hg' => ?_
    let g' : ↥(GK K) := ⟨g, hg'⟩
    let χ : ℚ_[l]ˣ := (P.PD K).χ g'
    have h1 : Units.map ((P.PD K).actdR g' : P.R.BdR →* P.R.BdR) T =
        Units.map (algebraMap ℚ_[l] P.R.BdR : ℚ_[l] →* P.R.BdR) χ * T := by
      ext
      have h2 := (P.PD K).ι_comm g' (P.PD K).t
      rw [(P.PD K).t_act, P.PD_ι, P.PD_ι, P.period_datum_t_eq, map_smul, ← hT, Algebra.smul_def] at h2
      exact h2.symm
    have h2 : (P.PD K).actdR g' ((T ^ n : P.R.BdRˣ) : P.R.BdR) =
        ((T ^ n : P.R.BdRˣ) : P.R.BdR) * algebraMap ℚ_[l] P.R.BdR ((χ : ℚ_[l]) ^ n) := by
      have h3 := congrArg (fun x : P.R.BdRˣ => ((x ^ n : P.R.BdRˣ) : P.R.BdR)) h1
      simp only [mul_zpow, ← map_zpow, Units.val_mul, Units.coe_map] at h3
      rw [mul_comm, ← Units.val_zpow_eq_zpow_val]
      exact h3
    have h3 := hg g'
    have h4 : algebraMap ℚ_[l] P.R.BdR ((χ : ℚ_[l]) ^ n) ∈ (P.PD K).Fil 0 := by
      rw [IsScalarTower.algebraMap_apply ℚ_[l] ↥K.1 P.R.BdR]
      exact alg_mem_fil_zero K _
    have h5 := (P.PD K).Fil_G g' _ _ hu
    have h6 := (P.PD K).Fil_mul _ _ _ _ h4 h5
    rw [add_zero] at h6
    rw [map_mul, h2, mul_assoc, ← mul_sub, add_comm, ← fil_shift Θ K T hT n,
      theta_sub_iff Θ K h6 hu, theta_mul Θ K h4 h5, hact _ _ hu,
      IsScalarTower.algebraMap_apply ℚ_[l] (Om l) P.R.BdR, Θ.θ_Om] at h3
    rw [← hC.χ, ← map_zpow₀, mul_comm]
    refine Eq.trans ?_ h3
    congr 1
    rw [show ((P.χQ g : ℚ_[l]ˣ) : ℚ_[l]) = χ from (P.PD_χ K g').symm]
    exact IsScalarTower.algebraMap_apply ℚ_[l] (Om l) ℂ_[l] _

end Periods

/- English proof (translation)
Introduce `l _ P AI TT K LL V _ _ _ _ _ ρ hdR a y hy`. Take `⟨Θ⟩` from `GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT`. Take `⟨m, b, d, hd, hsum⟩` from `GlobalTheory.T.deRhamDieudonne_spans_tensor_deRham_periods l P AI TT K LL V ρ hdR y`. Set `φ : P.R.BdR →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR)` to `{ toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] b) map_one' := by ext; simp map_mul' := fun x y => by ext; simp [mul_assoc] map_zero' := by ext; simp map_add' := fun x y => by ext; simp [add_mul, tmul_add] }`. Use `letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ`.

Establish `hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x = AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] b) x` using `fun _ _ => rfl`. Establish `hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x` using `fun x => by`. Simplify using `[DdR, Submodule.mem_iInf, sub_eq_zero]`. Establish `htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL` using `↥LL.1) (V := V) a := fun a v x hx => ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩`. Establish `hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)), (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) → ∀ z ∈ FilV (P.PD K) (LL` using `↥LL.1) (V := V) a, z ∈ S := by`.

Introduce and unpack `a S hS _ ⟨z, rfl⟩`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [map_zero]`. Conclude with `S.zero_mem`. Consider the case `tmul v x => exact hS v x x.2`.

Consider the case `add x y hx hy => rw [map_add]`. Conclude with `S.add_mem hx hy`. Establish `hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup` using `antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a`. Establish `hMa : Antitone fun a => (FilV (P.PD K) (LL` using `↥LL.1) (V := V) a).toAddSubgroup := fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz`. Take `⟨m', k, b', d', h, e⟩` from `filtered (G := ↥(GK K)) (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR)) (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom) (fun a => ((P.PD K).Fil a).toAddSubgroup) (fun a => (FilV (P.PD K) (LL := ↥LL.1) (V := V) a).toAddSubgroup) (fun g b x => by`.

Rewrite using `[hsm, hsm]`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul v x => simp [actVdR]`. Consider the case `add x y hx hy => simp only [map_add, hx, hy])`.

Use the proof step `(P.PD K).Fil_mul`. Use the proof step `(fun a c x z hx hz => hind c ((FilV (P.PD K) (LL := ↥LL.1) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom) (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)`. Use the proof step `(P.PD K).Fil_G`. Use the proof step `(fun g a z hz => hind a ((FilV (P.PD K) (LL := ↥LL.1) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom) (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)`. Use the proof step `(graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh`.

Use the proof step `(fun x => by`. Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, AddSubgroup.zero_mem _⟩`. Consider the case `tmul v x`. Take `⟨c, hc⟩` from `(P.PD K).Fil_exh x`.

Conclude with `⟨c, htm c v x hc⟩`. Consider the case `add x y hx hy`. Take `⟨c, hc⟩` from `hx`. Take `⟨c', hc'⟩` from `hy`. Conclude with `⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)`.

Use `a y hy m b d (fun i g => (hD _).1 (hd i) g) hsum`. Conclude with `⟨m', k, b', d', fun i => ⟨(hD _).2 (h i).1, (h i).2.1, (h i).2.2⟩, e⟩`.
-/
theorem deRham_filtered : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (AI : LocAinf l P), LocTied l P AI → ∀ (K LL : FinExt l) (V : Type) [AddCommGroup V] [Module ↥LL.1 V] [Module ℚ_[l] V] [IsScalarTower ℚ_[l] ↥LL.1 V] [FiniteDimensional ↥LL.1 V] (ρ : Representation ↥LL.1 ↥(GK K) V), IsDR (P.PD K) ρ → ∀ (a : ℤ), ∀ y ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, ∃ (m : ℕ) (k : Fin m → ℤ) (b : Fin m → P.R.BdR) (d : Fin m → V ⊗[ℚ_[l]] P.R.BdR), (∀ i, d i ∈ DdR (P.PD K) ρ ∧ d i ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) (k i) ∧ b i ∈ (P.PD K).Fil (a - k i)) ∧ y = ∑ i, AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] (b i)) (d i) := by
  intro l _ P AI TT K LL V _ _ _ _ _ ρ hdR a y hy
  obtain ⟨Θ⟩ := GlobalTheory.MemLoc.TiedTheta.nonempty_thetaL l P AI TT
  obtain ⟨m, b, d, hd, hsum⟩ := GlobalTheory.T.deRhamDieudonne_spans_tensor_deRham_periods l P AI TT K LL V ρ hdR y
  let φ : P.R.BdR →+* Module.End ↥LL.1 (V ⊗[ℚ_[l]] P.R.BdR) :=
    { toFun := fun b => AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] b)
      map_one' := by ext; simp
      map_mul' := fun x y => by ext; simp [mul_assoc]
      map_zero' := by ext; simp
      map_add' := fun x y => by ext; simp [add_mul, tmul_add] }
  letI : Module P.R.BdR (V ⊗[ℚ_[l]] P.R.BdR) := Module.compHom _ φ
  have hsm : ∀ (b : P.R.BdR) (x : V ⊗[ℚ_[l]] P.R.BdR), b • x =
      AlgebraTensorModule.map (LinearMap.id : V →ₗ[↥LL.1] V) (LinearMap.mulLeft ℚ_[l] b) x := fun _ _ => rfl
  have hD : ∀ x, x ∈ DdR (P.PD K) ρ ↔ ∀ g, actVdR (P.PD K) ρ g x = x := fun x => by
    simp [DdR, Submodule.mem_iInf, sub_eq_zero]
  have htm : ∀ (a : ℤ) (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a →
      v ⊗ₜ[ℚ_[l]] x ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) a := fun a v x hx =>
    ⟨v ⊗ₜ ⟨x, hx⟩, rfl⟩
  have hind : ∀ (a : ℤ) (S : AddSubgroup (V ⊗[ℚ_[l]] P.R.BdR)),
      (∀ (v : V) (x : P.R.BdR), x ∈ (P.PD K).Fil a → v ⊗ₜ[ℚ_[l]] x ∈ S) →
      ∀ z ∈ FilV (P.PD K) (LL := ↥LL.1) (V := V) a, z ∈ S := by
    rintro a S hS _ ⟨z, rfl⟩
    induction z using TensorProduct.induction_on with
    | zero => rw [map_zero]; exact S.zero_mem
    | tmul v x => exact hS v x x.2
    | add x y hx hy => rw [map_add]; exact S.add_mem hx hy
  have hFa : Antitone fun a => ((P.PD K).Fil a).toAddSubgroup :=
    antitone_int_of_succ_le fun a => (P.PD K).Fil_anti a
  have hMa : Antitone fun a => (FilV (P.PD K) (LL := ↥LL.1) (V := V) a).toAddSubgroup :=
    fun a a' h z hz => hind a' _ (fun v x hx => htm a v x (hFa h hx)) z hz
  obtain ⟨m', k, b', d', h, e⟩ := filtered (G := ↥(GK K))
    (fun g => ((P.PD K).actdR g : P.R.BdR →+* P.R.BdR))
    (fun g => (actVdR (P.PD K) ρ g).toAddMonoidHom)
    (fun a => ((P.PD K).Fil a).toAddSubgroup)
    (fun a => (FilV (P.PD K) (LL := ↥LL.1) (V := V) a).toAddSubgroup)
    (fun g b x => by
      rw [hsm, hsm]
      induction x using TensorProduct.induction_on with
      | zero => simp
      | tmul v x => simp [actVdR]
      | add x y hx hy => simp only [map_add, hx, hy])
    (P.PD K).Fil_mul
    (fun a c x z hx hz => hind c
      ((FilV (P.PD K) (LL := ↥LL.1) (V := V) (a + c)).toAddSubgroup.comap (φ x).toAddMonoidHom)
      (fun v w hw => htm _ v (x * w) ((P.PD K).Fil_mul _ _ _ _ hx hw)) z hz)
    (P.PD K).Fil_G
    (fun g a z hz => hind a
      ((FilV (P.PD K) (LL := ↥LL.1) (V := V) a).toAddSubgroup.comap (actVdR (P.PD K) ρ g).toAddMonoidHom)
      (fun v w hw => htm _ (ρ g v) ((P.PD K).actdR g w) ((P.PD K).Fil_G _ _ _ hw)) z hz)
    (graded_inv Θ K) (graded_invariants TT Θ K) hFa hMa (P.PD K).Fil_exh
    (fun x => by
      induction x using TensorProduct.induction_on with
      | zero => exact ⟨0, AddSubgroup.zero_mem _⟩
      | tmul v x =>
        obtain ⟨c, hc⟩ := (P.PD K).Fil_exh x
        exact ⟨c, htm c v x hc⟩
      | add x y hx hy =>
        obtain ⟨c, hc⟩ := hx
        obtain ⟨c', hc'⟩ := hy
        exact ⟨min c c', AddSubgroup.add_mem _ (hMa (min_le_left _ _) hc) (hMa (min_le_right _ _) hc')⟩)
    a y hy m b d (fun i g => (hD _).1 (hd i) g) hsum
  exact ⟨m', k, b', d', fun i => ⟨(hD _).2 (h i).1, (h i).2.1, (h i).2.2⟩, e⟩

end GlobalTheory.DRFil
