import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GlobSpecOfExists
import Formalism.GradedWeylDivisibility.FinalD
import Formalism.LocalToGlobal.Divisibility.CoefModLemmas
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.PosOkId
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.GenMDetNeZeroOfNontrivial

open MvPolynomial NumberField IsDedekindDomain Formalism.GradedWeylDivisibility Formalism.MainNotions.G Formalism.L2.Col Formalism.HermitianLatticesTheory Formalism.BasicNotions Formalism.L2.DIV GlobalTheory.GO GlobalTheory.ValCmp

namespace GlobalTheory.ValCmp

/- English proof (translation)
Establish `h` using `bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)`. Establish `e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs`. Simplify using `[bideterminant]`. Establish `e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0`. Use function extensionality and compare the values at `t`.

Apply the tactic sequence `by_cases ht : t.val < s <;> simp [shapeDeg, ht]`. Rewrite `h` using `[e1, e2]`. Then use the resulting hypothesis.
-/
theorem initMinor_mem_dualWeyl_ind (R : Type) [CommRing R] {r n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin r) :
    initMinor R I hs ∈ dualWeyl R r n (fun t => if t.val < s then 1 else 0) := by
  have h := bidetMem R r n 1 (fun _ => s) (fun _ => hs) (fun _ => I)
  have e1 : bideterminant R (fun _ : Fin 1 => s) (fun _ => hs) (fun _ => I) = initMinor R I hs := by
    simp [bideterminant]
  have e2 : (shapeDeg (fun _ : Fin 1 => s) : Fin n → ℕ) = fun t => if t.val < s then 1 else 0 := by
    funext t
    by_cases ht : t.val < s <;> simp [shapeDeg, ht]
  rwa [e1, e2] at h

/- English proof (translation)
Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]`. Conclude with `⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩`.
-/
private lemma one_mem_dualWeyl_zero (R : Type) [CommRing R] (r n : ℕ) :
    (1 : MvPolynomial (Fin r × Fin n) R) ∈ dualWeyl R r n 0 := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule]
  exact ⟨isWeightedHomogeneous_one R _, fun l j _ => by rw [map_one, map_one]⟩

/- English proof (translation)
Simplify using `only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢`. Use `⟨hf.1.mul hg.1, fun l j hlj => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]`.
-/
private lemma mul_mem_dualWeyl_add (R : Type) [CommRing R] {r n : ℕ} {ν₁ ν₂ : Fin n → ℕ}
    {f g : MvPolynomial (Fin r × Fin n) R} (hf : f ∈ dualWeyl R r n ν₁) (hg : g ∈ dualWeyl R r n ν₂) :
    f * g ∈ dualWeyl R r n (ν₁ + ν₂) := by
  simp only [dualWeyl, Submodule.mem_inf, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
    AlgHom.toLinearMap_apply, sub_eq_zero, mem_weightedHomogeneousSubmodule] at hf hg ⊢
  refine ⟨hf.1.mul hg.1, fun l j hlj => ?_⟩
  rw [map_mul, map_mul, hf.2 l j hlj, hg.2 l j hlj]

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using one_mem_dualWeyl_zero R r n`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.prod_insert ha, Finset.sum_insert ha]`. Conclude with `mul_mem_dualWeyl_add R (hg a) ih`.
-/
theorem prod_mem_dualWeyl_sum (R : Type) [CommRing R] {r n : ℕ} {ι : Type} (S : Finset ι) (w : ι → Fin n → ℕ)
    (g : ι → MvPolynomial (Fin r × Fin n) R) (hg : ∀ k, g k ∈ dualWeyl R r n (w k)) :
    ∏ k ∈ S, g k ∈ dualWeyl R r n (∑ k ∈ S, w k) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using one_mem_dualWeyl_zero R r n
  | insert a S ha ih =>
    rw [Finset.prod_insert ha, Finset.sum_insert ha]
    exact mul_mem_dualWeyl_add R (hg a) ih

/- English proof (translation)
Break down `Nat.eq_zero_or_pos s with rfl | h1` into its components or cases. Use `⟨1, ?_, ?_⟩` and prove the remaining obligations. Use `one_mem_dualWeyl_zero R n n using 2` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `t`. Simplify using the standard rewrite rules.

Simplify using `[initMinor]`. Distinguish the cases in `hI : Function.Injective I`. Choose the witnesses or unpack the hypotheses as in `⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by`. Set `e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I}` to `(Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)`. Use `⟨e.extendSubtype, fun a => ?_⟩` and prove the remaining obligations.

Rewrite using `[Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]`. Simplify using `only [e, Equiv.trans_apply]`. Rewrite using `[Equiv.ofInjective_symm_apply]`. Both sides reduce to the same expression. Take `⟨ε, hε⟩` from `cofAct_initMinor R n s hs h1 σ`.

Establish `hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I` using `funext hσ`. Rewrite `hε` using `[hIσ]`. Use `⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a))) (Nat.sub_le n s), ?_, ?_⟩` and prove the remaining obligations. Establish `hm` using `initMinor_mem_dualWeyl_ind R (Nat.sub_le n s) (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))`. Establish `hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) = fun t : Fin n => if t.val < n - s then 1 else 0`.

Use function extensionality and compare the values at `t`. Simplify using `[h1]`. Rewrite using `[hw]`. Conclude with `zsmul_mem hm _`. Rewrite using `[hε, mul_smul_comm]`.

Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Simplify using `only [Function.Injective, not_forall, exists_prop] at hI`. Take `⟨a, b, hab, hne⟩` from `hI`. Establish `h0 : initMinor R I hs = 0`. Unfold `initMinor`.

Conclude with `Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])`. Rewrite using `[h0, map_zero, mul_zero]`.
-/
theorem exists_cofAct_initMinor (R : Type) [CommRing R] [IsDomain R] {n s : ℕ} (hs : s ≤ n) (I : Fin s → Fin n) :
    ∃ g ∈ dualWeyl R n n (fun t => if 0 < s ∧ t.val < n - s then 1 else 0),
      (genM R n).det ^ (s - 1) * g = cofAct R n (initMinor R I hs) := by
  classical
  rcases Nat.eq_zero_or_pos s with rfl | h1
  · refine ⟨1, ?_, ?_⟩
    · convert one_mem_dualWeyl_zero R n n using 2
      funext t
      simp
    · simp [initMinor]
  by_cases hI : Function.Injective I
  · obtain ⟨σ, hσ⟩ : ∃ σ : Equiv.Perm (Fin n), ∀ a, σ (Fin.castLE hs a) = I a := by
      let e : {x // x ∈ Set.range (Fin.castLE hs)} ≃ {x // x ∈ Set.range I} :=
        (Equiv.ofInjective _ (Fin.castLE_injective hs)).symm.trans (Equiv.ofInjective I hI)
      refine ⟨e.extendSubtype, fun a => ?_⟩
      rw [Equiv.extendSubtype_apply_of_mem e _ ⟨a, rfl⟩]
      simp only [e, Equiv.trans_apply]
      rw [Equiv.ofInjective_symm_apply]
      rfl
    obtain ⟨ε, hε⟩ := cofAct_initMinor R n s hs h1 σ
    have hIσ : (fun a : Fin s => σ (Fin.castLE hs a)) = I := funext hσ
    rw [hIσ] at hε
    refine ⟨(ε : ℤ) • initMinor R (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      (Nat.sub_le n s), ?_, ?_⟩
    · have hm := initMinor_mem_dualWeyl_ind R (Nat.sub_le n s)
        (fun a : Fin (n - s) => σ (Fin.rev (Fin.castLE (Nat.sub_le n s) a)))
      have hw : (fun t : Fin n => if 0 < s ∧ t.val < n - s then 1 else 0) =
          fun t : Fin n => if t.val < n - s then 1 else 0 := by
        funext t
        simp [h1]
      rw [hw]
      exact zsmul_mem hm _
    · rw [hε, mul_smul_comm]
  · refine ⟨0, zero_mem _, ?_⟩
    simp only [Function.Injective, not_forall, exists_prop] at hI
    obtain ⟨a, b, hab, hne⟩ := hI
    have h0 : initMinor R I hs = 0 := by
      unfold initMinor
      exact Matrix.det_zero_of_row_eq hne (by funext q; simp [hab])
    rw [h0, map_zero, mul_zero]

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `key : ∀ k, ((if t.rev.val < sz k then 1 else 0) + (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) = if (0 : Fin (m + 1)).val < sz k then 1 else 0`. Introduce `k`. Use `t.isLt` as an intermediate fact. Rewrite using `[Fin.val_rev]`.

Apply the tactic sequence `split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega`. Establish `hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) + ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun k _ => key k`. Simplify using `only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem nuDual_shapeDeg {m K : ℕ} (sz : Fin K → ℕ) :
    nuDual (shapeDeg sz : Fin (m + 1) → ℕ) =
      ∑ k, fun t : Fin (m + 1) => if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0 := by
  funext t
  have key : ∀ k, ((if t.rev.val < sz k then 1 else 0) +
      (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) : ℕ) =
        if (0 : Fin (m + 1)).val < sz k then 1 else 0 := by
    intro k
    have := t.isLt
    rw [Fin.val_rev]
    split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  have hsum : ∑ k, (if t.rev.val < sz k then 1 else 0) +
      ∑ k, (if 0 < sz k ∧ t.val < m + 1 - sz k then 1 else 0) =
        ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => key k
  simp only [nuDual, shapeDeg, Finset.sum_apply, Finset.card_filter]
  omega

/- English proof (translation)
Establish `e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h)`. Use extensionality with `i`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]`. Prove the components needed by the constructor for the conclusion. Introduce `hi`.

Conclude with `⟨⟨i.val, hi⟩, rfl⟩`. Introduce and unpack `⟨j, rfl⟩`. Conclude with `j.isLt`. Rewrite using `[e, Finset.card_map, Finset.card_univ, Fintype.card_fin]`.
-/
private lemma card_filter_fin_val_lt_eq_of_le {N a : ℕ} (h : a ≤ N) :
    (Finset.univ.filter fun i : Fin N => i.val < a).card = a := by
  have e : (Finset.univ.filter fun i : Fin N => i.val < a) = Finset.univ.map (Fin.castLEEmb h) := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_map, Fin.castLEEmb_apply]
    constructor
    · intro hi
      exact ⟨⟨i.val, hi⟩, rfl⟩
    · rintro ⟨j, rfl⟩
      exact j.isLt
  rw [e, Finset.card_map, Finset.card_univ, Fintype.card_fin]

/- English proof (translation)
Establish `h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k`. Simplify using `only [shapeDeg, Finset.card_filter]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.card_filter]`.

Conclude with `card_filter_fin_val_lt_eq_of_le (hsz k)`. Establish `h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0)`. Simplify using `only [shapeDeg, Finset.card_filter]`. Establish `h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k`. Rewrite using `[← Finset.sum_add_distrib]`.

Apply the tactic sequence `exact Finset.sum_congr rfl fun k _ => by split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega`. Rewrite using `[h1, h0]`. Use linear arithmetic over natural numbers and integers.
-/
theorem sum_shapeDeg_sub {m K : ℕ} (sz : Fin K → ℕ) (hsz : ∀ k, sz k ≤ m + 1) :
    ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i - (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (sz k - 1) := by
  have h1 : ∑ i, (shapeDeg sz : Fin (m + 1) → ℕ) i = ∑ k, sz k := by
    simp only [shapeDeg, Finset.card_filter]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← Finset.card_filter]
    exact card_filter_fin_val_lt_eq_of_le (hsz k)
  have h0 : (shapeDeg sz : Fin (m + 1) → ℕ) 0 = ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) := by
    simp only [shapeDeg, Finset.card_filter]
  have h2 : ∑ k, (sz k - 1) + ∑ k, (if (0 : Fin (m + 1)).val < sz k then 1 else 0) = ∑ k, sz k := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun k _ => by
      split_ifs <;> (try simp only [Fin.val_zero] at *) <;> omega
  rw [h1, h0]
  omega

/- English proof (translation)
Introduce `R _ _ m ν _ _ f hf`. Take `⟨b, ⟨_, hspan, _⟩, hb⟩` from `sSBasis R (m + 1) (m + 1) ν`. Rewrite `hf` using `[← hspan]`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨i, rfl⟩` from `hx`. Take `⟨K, sz, hsz, I, hsh, -, hbi⟩` from `(hb i).2.2`. Rewrite using `[hbi]`. Use `choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)`. Use `⟨∏ k, g k, ?_, ?_⟩` and prove the remaining obligations.

Establish `hm` using `prod_mem_dualWeyl_sum R Finset.univ _ g hg`. Rewrite `hm` using `[← nuDual_shapeDeg sz, hsh]`. Then use the resulting hypothesis. Use `show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)`. Rewrite using `[← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant, map_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => hgeq k`.

Consider the case `zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨g₁, h₁, e₁⟩` from `hx`. Take `⟨g₂, h₂, e₂⟩` from `hy`. Use `⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩` and prove the remaining obligations.

Unfold `CofRel at e₁ e₂ ⊢`. Rewrite using `[mul_add, e₁, e₂, map_add]`. Consider the case `smul a x _ hx`. Take `⟨g, h, e⟩` from `hx`. Use `⟨a • g, Submodule.smul_mem _ a h, ?_⟩` and prove the remaining obligations.

Unfold `CofRel at e ⊢`. Rewrite using `[mul_smul_comm, e, map_smul]`.
-/
theorem exists_cofRel_dualWeyl : ∀ (R : Type) [CommRing R] [IsDomain R] (m : ℕ) (ν : Fin (m + 1) → ℕ), Antitone ν → ν (Fin.last m) = 0 → ∀ f ∈ dualWeyl R (m + 1) (m + 1) ν, ∃ g ∈ dualWeyl R (m + 1) (m + 1) (nuDual ν), CofRel R m ν f g := by
  intro R _ _ m ν _ _ f hf
  obtain ⟨b, ⟨_, hspan, _⟩, hb⟩ := sSBasis R (m + 1) (m + 1) ν
  rw [← hspan] at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨i, rfl⟩ := hx
    obtain ⟨K, sz, hsz, I, hsh, -, hbi⟩ := (hb i).2.2
    rw [hbi]
    choose g hg hgeq using fun k => exists_cofAct_initMinor R (hsz k) (I k)
    refine ⟨∏ k, g k, ?_, ?_⟩
    · have hm := prod_mem_dualWeyl_sum R Finset.univ _ g hg
      rwa [← nuDual_shapeDeg sz, hsh] at hm
    · show (genM R (m + 1)).det ^ (∑ i, ν i - ν 0) * ∏ k, g k = cofAct R (m + 1) (bideterminant R sz hsz I)
      rw [← hsh, sum_shapeDeg_sub sz hsz, ← Finset.prod_pow_eq_pow_sum, ← Finset.prod_mul_distrib, bideterminant,
        map_prod]
      exact Finset.prod_congr rfl fun k _ => hgeq k
  | zero => exact ⟨0, zero_mem _, by simp [CofRel]⟩
  | add x y _ _ hx hy =>
    obtain ⟨g₁, h₁, e₁⟩ := hx
    obtain ⟨g₂, h₂, e₂⟩ := hy
    refine ⟨g₁ + g₂, add_mem h₁ h₂, ?_⟩
    unfold CofRel at e₁ e₂ ⊢
    rw [mul_add, e₁, e₂, map_add]
  | smul a x _ hx =>
    obtain ⟨g, h, e⟩ := hx
    refine ⟨a • g, Submodule.smul_mem _ a h, ?_⟩
    unfold CofRel at e ⊢
    rw [mul_smul_comm, e, map_smul]

end GlobalTheory.ValCmp
