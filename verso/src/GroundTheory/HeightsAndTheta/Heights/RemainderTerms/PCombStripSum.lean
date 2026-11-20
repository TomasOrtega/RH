import Mathlib
import GroundTheory.HeightsAndTheta.Heights.RemainderTerms.StatementsComb
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.RestTerms

open MvPolynomial Finset Equiv Comb

noncomputable section

/- English proof (translation)
Introduce `m n q lam hlam hq`. Use `set l : Fin m → ℕ := fun j => lam j + stair m j with hl`. Establish `hAlt : IsAlt (alternantPsum m (List.replicate n 1))` using `isAlt_vandermonde_mul_prod _`. Establish `hl_inj : Function.Injective l`. Introduce `a b hab`.

Simplify using `only [hl, stair] at hab`. Establish `ha` using `a.isLt`. Establish `hb` using `b.isLt`. Break down `lt_trichotomy a b with h | h | h` into its components or cases. Establish `h'` using `hlam h.le`.

Establish `: (a : ℕ) < b` using `h`. Use linear arithmetic over natural numbers and integers. Conclude with `h`. Establish `h'` using `hlam h.le`. Establish `: (b : ℕ) < a` using `h`.

Use linear arithmetic over natural numbers and integers. Establish `key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) → ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m, (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧ |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| = …`. Introduce `i hqi hinj`. Take `⟨σ, μ, hμ, hμle, hσ0⟩` from `h2 m lam hlam q i hqi hinj`. Establish `hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k` using `hσ0`.

Establish `hsum : ∑ k, lam k = ∑ k, μ k + q`. Establish `e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k`. Rewrite using `[← Equiv.sum_comp σ (Function.update l i (l i - q))]`. Conclude with `Finset.sum_congr rfl fun k _ => (hσ k).symm`. Establish `e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k` using `Finset.sum_add_distrib`.

Establish `e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0`. Introduce `k`. Distinguish the cases in `hk : k = i`. Substitute `hk` using the available equality. Simplify using `only [Function.update_self, if_true]`.

Use linear arithmetic over natural numbers and integers. Simplify using `[hk]`. Establish `e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q`. Rewrite using `[Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']`. Simplify using the standard rewrite rules.

Rewrite `e1` using `[Finset.sum_add_distrib]`. Use linear arithmetic over natural numbers and integers. Take `⟨s, hs⟩` from `h4 m n q μ lam hμ hlam hμle hsum`. Use `⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩` and prove the remaining obligations. Establish `hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm`.

Use function extensionality and compare the values at `k`. Rewrite using `[Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]`. Rewrite using `[hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]`. Apply the tactic sequence `rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]`. Establish `key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m, (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) → (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧ |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1)) …`.

Introduce `i`. Distinguish the cases in `h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))`. Take `⟨μ, s, hs⟩` from `key i h.1 h.2`. Conclude with `⟨μ, s, fun _ => hs⟩`. Conclude with `⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩`.

Use `choose μ s hμs using key'`. Use `set S := univ.filter (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS`. Express the relevant statement in the definitionally equal form `∑ i : Fin m, (if q ≤ l i then |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _`. Establish `hsum_eq : ∑ i : Fin m, (if q ≤ l i then |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) = ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ)`. Rewrite using `[hS, Finset.sum_filter]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hqi : q ≤ l i`. Distinguish the cases in `hinj : Function.Injective (Function.update l i (l i - q))`. Rewrite using `[if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]`. Rewrite using `[if_pos hqi, if_neg (fun h => hinj h.2)]`.

Simplify using `only [Function.Injective, not_forall] at hinj`. Take `⟨a, b, hab, hne⟩` from `hinj`. Rewrite using `[cf_eq_zero_of_eq hAlt hne hab, abs_zero]`. Rewrite using `[if_neg hqi, if_neg (fun h => hqi h.1)]`. Rewrite using `[hsum_eq]`.

Establish `hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card`. Rewrite using `[← Finset.card_sigma]`. Use `Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_` and prove the remaining obligations. Introduce `x hx`. Rewrite `hx` using `[Finset.mem_coe, Finset.mem_sigma]`.

Conclude with `(hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2`. Introduce and unpack `⟨i, w⟩ hx ⟨j, w'⟩ hy hxy`. Rewrite `hx`, `hy` using `[Finset.mem_coe, Finset.mem_sigma]`. Simplify using `only at hxy hx hy`. Establish `hw : w = w'`.

Use function extensionality and compare the values at `k`. Use `congrFun hxy (Fin.castAdd q k)` as an intermediate fact. Simplify `this` using `only [Fin.append_left]`. Substitute `hw` using the available equality. Establish `hμij : μ i = μ j`.

Use function extensionality and compare the values at `k`. Establish `a1` using `(Finset.mem_filter.mp hx.2).2.2 k`. Establish `a2` using `(Finset.mem_filter.mp hy.2).2.2 k`. Rewrite using `[← a1, ← a2]`. Establish `hSi` using `(Finset.mem_filter.mp hx.1).2`.

Establish `hSj` using `(Finset.mem_filter.mp hy.1).2`. Establish `hij : i = j`. Assume the negation of the conclusion as `hij`. Take `⟨σ, hσ⟩` from `(hμs i hSi).1`. Take `⟨τ, hτ⟩` from `(hμs j hSj).1`.

Use `h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_` and prove the remaining obligations. Use function extensionality and compare the values at `k`. Rewrite using `[Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]`. Substitute `hij` using the available equality. Both sides reduce to the same expression.

Conclude with `hcard` after adjusting the coercions.
-/
theorem CombStripSum.proof (h1 : CombCfAtStair.Statement) (h2 : CombSortShift.Statement)
    (h3 : CombSortShiftDistinct.Statement) (h4 : CombExtendWord.Statement) :
    CombStripSum.Statement := by
  classical
  intro m n q lam hlam hq
  set l : Fin m → ℕ := fun j => lam j + stair m j with hl
  have hAlt : IsAlt (alternantPsum m (List.replicate n 1)) := isAlt_vandermonde_mul_prod _
  have hl_inj : Function.Injective l := by
    intro a b hab
    simp only [hl, stair] at hab
    have ha := a.isLt
    have hb := b.isLt
    rcases lt_trichotomy a b with h | h | h
    · have h' := hlam h.le
      have : (a : ℕ) < b := h
      omega
    · exact h
    · have h' := hlam h.le
      have : (b : ℕ) < a := h
      omega

  have key : ∀ i : Fin m, q ≤ l i → Function.Injective (Function.update l i (l i - q)) →
      ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i hqi hinj
    obtain ⟨σ, μ, hμ, hμle, hσ0⟩ := h2 m lam hlam q i hqi hinj
    have hσ : ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k := hσ0
    have hsum : ∑ k, lam k = ∑ k, μ k + q := by
      have e1 : ∑ k, (μ k + stair m k) = ∑ k, Function.update l i (l i - q) k := by
        rw [← Equiv.sum_comp σ (Function.update l i (l i - q))]
        exact Finset.sum_congr rfl fun k _ => (hσ k).symm
      have e4 : ∑ k, l k = ∑ k, lam k + ∑ k, stair m k := Finset.sum_add_distrib
      have e3 : ∀ k, l k = Function.update l i (l i - q) k + if k = i then q else 0 := by
        intro k
        by_cases hk : k = i
        · subst hk; simp only [Function.update_self, if_true]; omega
        · simp [hk]
      have e2 : ∑ k, l k = ∑ k, Function.update l i (l i - q) k + q := by
        rw [Finset.sum_congr rfl (fun k _ => e3 k), Finset.sum_add_distrib, Finset.sum_ite_eq']
        simp
      rw [Finset.sum_add_distrib] at e1
      omega
    obtain ⟨s, hs⟩ := h4 m n q μ lam hμ hlam hμle hsum
    refine ⟨μ, s, ⟨σ, hσ⟩, ?_, hs⟩
    have hu : Function.update l i (l i - q) = (fun k => μ k + stair m k) ∘ σ.symm := by
      funext k
      rw [Function.comp_apply, ← hσ (σ.symm k), Equiv.apply_symm_apply]
    rw [hu, cf_perm hAlt, abs_mul, h1 m n μ hμ]
    rcases Int.units_eq_one_or (Perm.sign σ) with h | h <;> simp [h]
  have key' : ∀ i : Fin m, ∃ μ : Fin m → ℕ, ∃ s : Fin q → Fin m,
      (q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) →
        (∃ σ : Perm (Fin m), ∀ k, Function.update l i (l i - q) (σ k) = μ k + stair m k) ∧
        |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| =
          ((latticeWords n μ).card : ℚ) ∧
        ∀ w ∈ latticeWords n μ, Fin.append w s ∈ latticeWords (n + q) lam := by
    intro i
    by_cases h : q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))
    · obtain ⟨μ, s, hs⟩ := key i h.1 h.2
      exact ⟨μ, s, fun _ => hs⟩
    · exact ⟨fun _ => 0, fun _ => i, fun h' => absurd h' h⟩
  choose μ s hμs using key'
  set S := univ.filter
    (fun i : Fin m => q ≤ l i ∧ Function.Injective (Function.update l i (l i - q))) with hS
  change ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) ≤ _
  have hsum_eq : ∑ i : Fin m, (if q ≤ l i then
      |cf (Function.update l i (l i - q)) (alternantPsum m (List.replicate n 1))| else 0) =
      ∑ i ∈ S, ((latticeWords n (μ i)).card : ℚ) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun i _ => ?_
    by_cases hqi : q ≤ l i
    · by_cases hinj : Function.Injective (Function.update l i (l i - q))
      · rw [if_pos hqi, if_pos ⟨hqi, hinj⟩, (hμs i ⟨hqi, hinj⟩).2.1]
      · rw [if_pos hqi, if_neg (fun h => hinj h.2)]
        simp only [Function.Injective, not_forall] at hinj
        obtain ⟨a, b, hab, hne⟩ := hinj
        rw [cf_eq_zero_of_eq hAlt hne hab, abs_zero]
    · rw [if_neg hqi, if_neg (fun h => hqi h.1)]
  rw [hsum_eq]
  have hcard : ∑ i ∈ S, (latticeWords n (μ i)).card ≤ (latticeWords (n + q) lam).card := by
    rw [← Finset.card_sigma]
    refine Finset.card_le_card_of_injOn (fun x => Fin.append x.2 (s x.1)) ?_ ?_
    · intro x hx
      rw [Finset.mem_coe, Finset.mem_sigma] at hx
      exact (hμs x.1 (Finset.mem_filter.mp hx.1).2).2.2 x.2 hx.2
    · rintro ⟨i, w⟩ hx ⟨j, w'⟩ hy hxy
      rw [Finset.mem_coe, Finset.mem_sigma] at hx hy
      simp only at hxy hx hy
      have hw : w = w' := by
        funext k
        have := congrFun hxy (Fin.castAdd q k)
        simpa only [Fin.append_left] using this
      subst hw
      have hμij : μ i = μ j := by
        funext k
        have a1 := (Finset.mem_filter.mp hx.2).2.2 k
        have a2 := (Finset.mem_filter.mp hy.2).2.2 k
        rw [← a1, ← a2]
      have hSi := (Finset.mem_filter.mp hx.1).2
      have hSj := (Finset.mem_filter.mp hy.1).2
      have hij : i = j := by
        by_contra hij
        obtain ⟨σ, hσ⟩ := (hμs i hSi).1
        obtain ⟨τ, hτ⟩ := (hμs j hSj).1
        refine h3 m l hl_inj q hq i j hij hSi.1 hSj.1 σ τ ?_
        funext k
        rw [Function.comp_apply, Function.comp_apply, hσ k, hτ k, hμij]
      subst hij
      rfl
  exact_mod_cast hcard

end

end GroundTheory.Heights₂.Heights.RestTerms
