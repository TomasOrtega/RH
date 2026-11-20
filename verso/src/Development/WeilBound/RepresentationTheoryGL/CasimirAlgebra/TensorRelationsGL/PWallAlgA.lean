import Development.WeilBound.RepresentationTheoryGL.CasimirAlgebra.TensorRelationsGL.LiftCommEAt

noncomputable section

open Formalism.REAL Matrix

namespace PositivityTheory.Rg.Cz

namespace WallAlgP

variable {n : ℕ} {M : Type} [AddCommGroup M] [Module ℂ M]

/- English proof (translation)
Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_lowS {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun j : Fin m => (j : ℕ) < k).card = k := by
  rw [Fin.card_filter_val_lt]; omega

/- English proof (translation)
Establish `h` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m))) (fun j : Fin m => (j : ℕ) < k)`. Rewrite `h` using `[card_lowS hk, Finset.card_univ, Fintype.card_fin]`. Simplify using `only [not_lt] at h`. Use linear arithmetic over natural numbers and integers.
-/
theorem card_highS {m k : ℕ} (hk : k ≤ m) :
    (Finset.univ.filter fun j : Fin m => k ≤ (j : ℕ)).card = m - k := by
  have h := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin m)))
    (fun j : Fin m => (j : ℕ) < k)
  rw [card_lowS hk, Finset.card_univ, Fintype.card_fin] at h
  simp only [not_lt] at h
  omega

/- English proof (translation)
Simplify using `[firstG]`.
-/
theorem mem_firstG {m k : ℕ} (σ : Equiv.Perm (Fin m)) :
    σ ∈ firstG m k ↔ ∀ j : Fin m, k ≤ (j : ℕ) → σ j = j := by
  simp [firstG]

/- English proof (translation)
Rewrite using `[← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]`. Simplify using the standard rewrite rules.
-/
theorem sgn_sq {m : ℕ} (τ : Equiv.Perm (Fin m)) :
    ((Equiv.Perm.sign τ : ℤ) : ℂ) * ((Equiv.Perm.sign τ : ℤ) : ℂ) = 1 := by
  rw [← Int.cast_mul, ← Units.val_mul, Int.units_mul_self]; simp

/- English proof (translation)
Rewrite `hτ` using `[mem_firstG]`. Simplify using `only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]`. Use `Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_` and prove the remaining obligations. Introduce `σ`. Simplify using `only [mem_firstG, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply]`.

Prove the components needed by the constructor for the conclusion. Introduce `h j hj`. Rewrite using `[h j hj, hτ j hj]`. Introduce `h j hj`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[h j hj, hτ j hj]`. Introduce `σ _`. Simplify using `only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]`. Rewrite using `[show pm τ (pm σ ξ) = pm (τ * σ) ξ from rfl, Units.val_mul, Int.cast_mul, ← mul_assoc, sgn_sq, one_mul]`.
-/
theorem pm_alt_first {m k : ℕ} (τ : Equiv.Perm (Fin m)) (hτ : τ ∈ firstG m k) (ξ : TV n M (Fin m)) :
    pm τ (alt (firstG m k) ξ) = ((Equiv.Perm.sign τ : ℤ) : ℂ) • alt (firstG m k) ξ := by
  rw [mem_firstG] at hτ
  simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul, Finset.smul_sum]
  refine Finset.sum_equiv (Equiv.mulLeft τ) ?_ ?_
  · intro σ
    simp only [mem_firstG, Equiv.coe_mulLeft, Equiv.Perm.coe_mul, Function.comp_apply]
    constructor
    · intro h j hj; rw [h j hj, hτ j hj]
    · intro h j hj
      apply τ.injective; rw [h j hj, hτ j hj]
  · intro σ _
    simp only [Equiv.coe_mulLeft, Equiv.Perm.sign_mul, smul_smul]
    rw [show pm τ (pm σ ξ) = pm (τ * σ) ξ from rfl, Units.val_mul, Int.cast_mul, ← mul_assoc, sgn_sq, one_mul]

/- English proof (translation)
Establish `: firstG m 0 = {1}`. Use extensionality with `σ`. Simplify using `only [mem_firstG, Finset.mem_singleton, zero_le, forall_const]`. Conclude with `⟨fun h => Equiv.ext h, fun h j => by simp [h]⟩`. Rewrite using `[this]`.

Simplify using `[alt]`.
-/
theorem alt_zero {m : ℕ} (ξ : TV n M (Fin m)) : alt (firstG m 0) ξ = ξ := by
  have : firstG m 0 = {1} := by
    ext σ
    simp only [mem_firstG, Finset.mem_singleton, zero_le, forall_const]
    exact ⟨fun h => Equiv.ext h, fun h j => by simp [h]⟩
  rw [this]; simp [alt]

/- English proof (translation)
Rewrite using `[alt, LinearMap.sum_apply]`. Simplify using `only [LinearMap.smul_apply]`. Conclude with `X.sum_mem fun σ _ => X.smul_mem _ (hP σ ξ hξ)`.
-/
theorem alt_mem {m k : ℕ} (X : Submodule ℂ (TV n M (Fin m))) (hP : ∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X) (ξ) (hξ : ξ ∈ X) :
    alt (firstG m k) ξ ∈ X := by
  rw [alt, LinearMap.sum_apply]
  simp only [LinearMap.smul_apply]
  exact X.sum_mem fun σ _ => X.smul_mem _ (hP σ ξ hξ)

/- English proof (translation)
Use function extensionality and compare the values at `I`. Establish `key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a (I j) ξ (Function.update I j a) = ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a)` using `Finset.sum_congr rfl fun a _ => congrFun (hX a (I j)) _`. Establish `hR : ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a) = c • ξ I`. Simplify using `only [ite_apply, Pi.smul_apply, Pi.zero_apply]`. Rewrite using `[Finset.sum_ite_eq']`.

Simplify using the standard rewrite rules. Simplify using `only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply] at key`. Rewrite `key` using `[Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)]`. Establish `h1 : ∑ a, (if Function.update I j a j = a then ξ (Function.update (Function.update I j a) j (I j)) else 0) = (n : ℂ) • ξ I`. Simplify using `[Function.update_idem]`.

Conclude with `(Nat.cast_smul_eq_nsmul ℂ n _).symm`. Establish `h2 : ∀ p ∈ Finset.univ.erase j, ∑ a, (if Function.update I j a p = a then ξ (Function.update (Function.update I j a) p (I j)) else 0) = ξ (I ∘ Equiv.swap j p)`. Introduce `p hp`. Establish `hpj : p ≠ j` using `Finset.ne_of_mem_erase hp`. Simplify using `only [Function.update_of_ne hpj]`.

Rewrite using `[Finset.sum_ite_eq]`. Simplify using `only [Finset.mem_univ, if_true]`. Use `congr 1`. Use function extensionality and compare the values at `x`. Simplify using `only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]`.

Apply the tactic sequence `split_ifs <;> subst_vars <;> simp_all`. Rewrite `key` using `[h1, Finset.sum_congr rfl h2, hR]`. Simplify using `only [Pi.add_apply, Pi.smul_apply, Om_apply, Finset.sum_apply, pm_apply, Finset.filter_ne']`. Rewrite using `[← key]`. Normalize the expressions using the abelian group laws.
-/
theorem contr (E₁ E₂ : Fin n → Fin n → Module.End ℂ M) {m : ℕ} (c : ℂ) (ξ : TV n M (Fin m))
    (hX : ∀ a b, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) (j : Fin m) :
    Om E₁ j ξ + Om E₂ j ξ + ∑ p ∈ Finset.univ.filter (· ≠ j), pm (Equiv.swap j p) ξ + (n : ℂ) • ξ = c • ξ := by
  funext I
  have key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a (I j) ξ (Function.update I j a) =
      ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a) :=
    Finset.sum_congr rfl fun a _ => congrFun (hX a (I j)) _
  have hR : ∑ a, (if a = I j then c • ξ else 0) (Function.update I j a) = c • ξ I := by
    simp only [ite_apply, Pi.smul_apply, Pi.zero_apply]
    rw [Finset.sum_ite_eq']
    simp
  simp only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply] at key
  rw [Finset.sum_comm, ← Finset.add_sum_erase _ _ (Finset.mem_univ j)] at key
  have h1 : ∑ a, (if Function.update I j a j = a then
      ξ (Function.update (Function.update I j a) j (I j)) else 0) = (n : ℂ) • ξ I := by
    simp [Function.update_idem]
    exact (Nat.cast_smul_eq_nsmul ℂ n _).symm
  have h2 : ∀ p ∈ Finset.univ.erase j, ∑ a, (if Function.update I j a p = a then
      ξ (Function.update (Function.update I j a) p (I j)) else 0) = ξ (I ∘ Equiv.swap j p) := by
    intro p hp
    have hpj : p ≠ j := Finset.ne_of_mem_erase hp
    simp only [Function.update_of_ne hpj]
    rw [Finset.sum_ite_eq]
    simp only [Finset.mem_univ, if_true]
    congr 1
    funext x
    simp only [Function.comp_apply, Function.update_apply, Equiv.swap_apply_def]
    split_ifs <;> subst_vars <;> simp_all
  rw [h1, Finset.sum_congr rfl h2, hR] at key
  simp only [Pi.add_apply, Pi.smul_apply, Om_apply, Finset.sum_apply, pm_apply, Finset.filter_ne']
  rw [← key]
  abel

/- English proof (translation)
Use function extensionality and compare the values at `I`. Establish `key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a a ξ I = ∑ a, (if a = a then c • ξ else 0) I` using `Finset.sum_congr rfl fun a _ => congrFun (hX a a) _`. Simplify using `only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply, if_true] at key`. Rewrite `key` using `[Finset.sum_comm]`. Establish `h3 : ∀ p : Fin m, ∑ a, (if I p = a then ξ (Function.update I p a) else 0) = ξ I`.

Introduce `p`. Rewrite using `[Finset.sum_ite_eq]`. Simplify using the standard rewrite rules. Establish `e₁ : ∑ a, E₁ a a (ξ I) = t₁ • ξ I`. Rewrite using `[← LinearMap.sum_apply, h₁]`.

Both sides reduce to the same expression. Establish `e₂ : ∑ a, E₂ a a (ξ I) = t₂ • ξ I`. Rewrite using `[← LinearMap.sum_apply, h₂]`. Both sides reduce to the same expression. Rewrite `key` using `[Finset.sum_congr rfl fun p _ => h3 p, e₁, e₂]`.

Simplify using `only [Pi.smul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at key ⊢`. Rewrite using `[add_smul, add_smul, mul_smul, Nat.cast_smul_eq_nsmul ℂ m, Nat.cast_smul_eq_nsmul ℂ n]`. Conclude with `key`.
-/
theorem trace_rel (E₁ E₂ : Fin n → Fin n → Module.End ℂ M) {m : ℕ} (c t₁ t₂ : ℂ) (ξ : TV n M (Fin m))
    (h₁ : ∑ a, E₁ a a = algebraMap ℂ _ t₁) (h₂ : ∑ a, E₂ a a = algebraMap ℂ _ t₂)
    (hX : ∀ a b, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a b ξ = if a = b then c • ξ else 0) :
    (t₁ + t₂ + m) • ξ = ((n : ℂ) * c) • ξ := by
  funext I
  have key : ∑ a, tE Finset.univ (fun a b => E₁ a b + E₂ a b) a a ξ I = ∑ a, (if a = a then c • ξ else 0) I :=
    Finset.sum_congr rfl fun a _ => congrFun (hX a a) _
  simp only [tE_apply, Finset.sum_add_distrib, LinearMap.add_apply, if_true] at key
  rw [Finset.sum_comm] at key
  have h3 : ∀ p : Fin m, ∑ a, (if I p = a then ξ (Function.update I p a) else 0) = ξ I := by
    intro p
    rw [Finset.sum_ite_eq]; simp
  have e₁ : ∑ a, E₁ a a (ξ I) = t₁ • ξ I := by
    rw [← LinearMap.sum_apply, h₁]; rfl
  have e₂ : ∑ a, E₂ a a (ξ I) = t₂ • ξ I := by
    rw [← LinearMap.sum_apply, h₂]; rfl
  rw [Finset.sum_congr rfl fun p _ => h3 p, e₁, e₂] at key
  simp only [Pi.smul_apply, Finset.sum_const, Finset.card_univ, Fintype.card_fin] at key ⊢
  rw [add_smul, add_smul, mul_smul, Nat.cast_smul_eq_nsmul ℂ m, Nat.cast_smul_eq_nsmul ℂ n]
  exact key

/- English proof (translation)
Use `set k' : Fin m := ⟨k, hk⟩ with hk'`. Establish `hins : (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) = insert k' (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)`. Use extensionality with `j`. Simplify using `[Fin.ext_iff, k']`. Use linear arithmetic over natural numbers and integers.

Establish `hnot : k' ∉ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k)` using `by simp [k']`. Establish `h1 : ∑ τ ∈ firstG m (k + 1), f τ = ∑ p ∈ (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) ×ˢ firstG m k, f (Equiv.swap p.1 k' * p.2)`. Use `Finset.sum_nbij' (fun τ => (τ k', Equiv.swap (τ k') k' * τ)) (fun p => Equiv.swap p.1 k' * p.2) ?_ ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`. Rewrite `hτ` using `[mem_firstG]`.

Establish `hle : (τ k' : ℕ) ≤ k`. Assume the negation of the conclusion as `h`. Establish `h2` using `hτ (τ k') (by omega)`. Establish `h3` using `τ.injective h2`. Rewrite `h` using `[h3]`.

Simplify using `[k'] at h`. Use `Finset.mem_product.2 ⟨by simpa using hle, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_firstG]`. Introduce `j hj`. Rewrite using `[Equiv.Perm.mul_apply]`.

Distinguish the cases in `hjk : j = k'`. Rewrite using `[hjk, Equiv.swap_apply_left]`. Establish `hj1 : k + 1 ≤ (j : ℕ)`. Establish `: (j : ℕ) ≠ k` using `fun h => hjk (Fin.ext h)`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hτ j hj1]`. Use `Equiv.swap_apply_of_ne_of_ne ?_ hjk` and prove the remaining obligations. Introduce `h`. Rewrite `hj1` using `[h]`. Use linear arithmetic over natural numbers and integers.

Introduce `p hp`. Rewrite `hp` using `[Finset.mem_product]`. Take `⟨hp1, hp2⟩` from `hp`. Rewrite `hp2`, the goal using `[mem_firstG]`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1`.

Introduce `j hj`. Rewrite using `[Equiv.Perm.mul_apply, hp2 j (by omega)]`. Use `Equiv.swap_apply_of_ne_of_ne ?_ ?_` and prove the remaining obligations. Introduce `h`. Rewrite `hj` using `[h]`.

Use linear arithmetic over natural numbers and integers. Introduce `h`. Rewrite `hj` using `[h]`. Simplify using `[k'] at hj`. Introduce `τ _`.

Simplify using `only [Equiv.swap_mul_self_mul]`. Introduce `p hp`. Rewrite `hp` using `[Finset.mem_product, mem_firstG]`. Establish `hk2` using `hp.2 k' (le_refl _)`. Simplify using `only [Equiv.Perm.mul_apply, hk2, Equiv.swap_apply_right, Equiv.swap_mul_self_mul]`.

Introduce `τ _`. Simplify using `only [Equiv.swap_mul_self_mul]`. Rewrite using `[h1, Finset.sum_product, hins, Finset.sum_insert hnot]`. Simplify using `only [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]`.
-/
theorem coset {m k : ℕ} (hk : k < m) {V : Type} [AddCommMonoid V] (f : Equiv.Perm (Fin m) → V) :
    ∑ τ ∈ firstG m (k + 1), f τ = ∑ σ ∈ firstG m k, f σ +
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ σ ∈ firstG m k, f (Equiv.swap j ⟨k, hk⟩ * σ) := by
  set k' : Fin m := ⟨k, hk⟩ with hk'
  have hins : (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) =
      insert k' (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by
    ext j; simp [Fin.ext_iff, k']; omega
  have hnot : k' ∉ (Finset.univ.filter fun j : Fin m => (j : ℕ) < k) := by simp [k']
  have h1 : ∑ τ ∈ firstG m (k + 1), f τ = ∑ p ∈ (Finset.univ.filter fun j : Fin m => (j : ℕ) ≤ k) ×ˢ firstG m k,
      f (Equiv.swap p.1 k' * p.2) := by
    refine Finset.sum_nbij' (fun τ => (τ k', Equiv.swap (τ k') k' * τ)) (fun p => Equiv.swap p.1 k' * p.2)
      ?_ ?_ ?_ ?_ ?_
    · intro τ hτ
      rw [mem_firstG] at hτ
      have hle : (τ k' : ℕ) ≤ k := by
        by_contra h
        have h2 := hτ (τ k') (by omega)
        have h3 := τ.injective h2
        rw [h3] at h
        simp [k'] at h
      refine Finset.mem_product.2 ⟨by simpa using hle, ?_⟩
      rw [mem_firstG]
      intro j hj
      rw [Equiv.Perm.mul_apply]
      by_cases hjk : j = k'
      · rw [hjk, Equiv.swap_apply_left]
      · have hj1 : k + 1 ≤ (j : ℕ) := by
          have : (j : ℕ) ≠ k := fun h => hjk (Fin.ext h)
          omega
        rw [hτ j hj1]
        refine Equiv.swap_apply_of_ne_of_ne ?_ hjk
        intro h; rw [h] at hj1; omega
    · intro p hp
      rw [Finset.mem_product] at hp
      obtain ⟨hp1, hp2⟩ := hp
      rw [mem_firstG] at hp2 ⊢
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp1
      intro j hj
      rw [Equiv.Perm.mul_apply, hp2 j (by omega)]
      refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
      · intro h; rw [h] at hj; omega
      · intro h; rw [h] at hj; simp [k'] at hj
    · intro τ _
      simp only [Equiv.swap_mul_self_mul]
    · intro p hp
      rw [Finset.mem_product, mem_firstG] at hp
      have hk2 := hp.2 k' (le_refl _)
      simp only [Equiv.Perm.mul_apply, hk2, Equiv.swap_apply_right, Equiv.swap_mul_self_mul]
    · intro τ _
      simp only [Equiv.swap_mul_self_mul]
  rw [h1, Finset.sum_product, hins, Finset.sum_insert hnot]
  simp only [Equiv.swap_self, ← Equiv.Perm.one_def, one_mul]

/- English proof (translation)
Use `set k' : Fin m := ⟨k, hk⟩ with hk'`. Use `set π := Equiv.swap k' i with hπ`. Establish `hπ2 : π * π = 1` using `Equiv.swap_mul_self k' i`. Establish `hcomm : ∀ η : TV n M (Fin m), alt (firstG m k) (pm π η) = pm π (alt (firstG m k) η)`. Introduce `η`.

Simplify using `only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Use `Finset.sum_congr rfl fun σ hσ => ?_` and prove the remaining obligations. Rewrite `hσ` using `[mem_firstG]`. Use `congr 1`. Rewrite using `[← Module.End.mul_apply, ← Module.End.mul_apply, ← pm_mul, ← pm_mul]`.

Use `congr 1`. Rewrite using `[hπ, Equiv.mul_swap_eq_swap_mul, hσ k' (le_refl _), hσ i hi]`. Establish `hdec : ∀ η : TV n M (Fin m), alt (firstG m (k + 1)) η = alt (firstG m k) η - ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), pm (Equiv.swap j k') (alt (firstG m k) η)`. Introduce `η`. Establish `hc` using `coset hk (fun τ => ((Equiv.Perm.sign τ : ℤ) : ℂ) • pm τ η)`.

Simplify using `only at hc`. Simplify using `only [alt, LinearMap.sum_apply, LinearMap.smul_apply]`. Rewrite using `[hc, sub_eq_add_neg, ← Finset.sum_neg_distrib]`. Use `congr 1`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Establish `hne : j ≠ k'`. Introduce `h`. Rewrite `hj` using `[h]`. Simplify using `[k'] at hj`. Rewrite using `[map_sum, ← Finset.sum_neg_distrib]`.

Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, pm_mul, map_smul, Module.End.mul_apply]`. Simplify using the standard rewrite rules. Both sides reduce to the same expression. Establish `hA` using `h0 (pm π ξ) (hP π ξ hξ)`.

Rewrite `hA` using `[hdec, hcomm, sub_eq_zero]`. Establish `h2` using `congrArg (pm π) hA`. Rewrite `h2` using `[← Module.End.mul_apply, ← pm_mul, hπ2, pm_one, Module.End.one_apply, map_sum]`. Use `conv_rhs => rw [h2]`. Use `Finset.sum_congr rfl fun j hj => ?_` and prove the remaining obligations.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Establish `hj1 : π j = j`. Use `Equiv.swap_apply_of_ne_of_ne ?_ ?_` and prove the remaining obligations. Introduce `h`. Rewrite `hj` using `[h]`.

Simplify using `[k'] at hj`. Introduce `h`. Rewrite `hj` using `[h]`. Use linear arithmetic over natural numbers and integers. Establish `e : Equiv.swap j i = π * Equiv.swap j k' * π`.

Rewrite using `[Equiv.mul_swap_eq_swap_mul π j k', hj1, hπ, Equiv.swap_apply_left, mul_assoc, ← hπ, hπ2, mul_one]`. Rewrite using `[e]`. Simplify using `only [pm_mul, Module.End.mul_apply]`.
-/
theorem outer {m k : ℕ} (hk : k < m) (X : Submodule ℂ (TV n M (Fin m))) (hP : ∀ σ, ∀ ξ ∈ X, pm σ ξ ∈ X)
    (h0 : ∀ ξ ∈ X, alt (firstG m (k + 1)) ξ = 0) (ξ) (hξ : ξ ∈ X) (i : Fin m) (hi : k ≤ (i : ℕ)) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), pm (Equiv.swap j i) (alt (firstG m k) ξ) =
      alt (firstG m k) ξ := by
  set k' : Fin m := ⟨k, hk⟩ with hk'
  set π := Equiv.swap k' i with hπ
  have hπ2 : π * π = 1 := Equiv.swap_mul_self k' i
  have hcomm : ∀ η : TV n M (Fin m), alt (firstG m k) (pm π η) = pm π (alt (firstG m k) η) := by
    intro η
    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
    refine Finset.sum_congr rfl fun σ hσ => ?_
    rw [mem_firstG] at hσ
    congr 1
    rw [← Module.End.mul_apply, ← Module.End.mul_apply, ← pm_mul, ← pm_mul]
    congr 1
    rw [hπ, Equiv.mul_swap_eq_swap_mul, hσ k' (le_refl _), hσ i hi]
  have hdec : ∀ η : TV n M (Fin m), alt (firstG m (k + 1)) η = alt (firstG m k) η -
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), pm (Equiv.swap j k') (alt (firstG m k) η) := by
    intro η
    have hc := coset hk (fun τ => ((Equiv.Perm.sign τ : ℤ) : ℂ) • pm τ η)
    simp only at hc
    simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply]
    rw [hc, sub_eq_add_neg, ← Finset.sum_neg_distrib]
    congr 1
    refine Finset.sum_congr rfl fun j hj => ?_
    have hne : j ≠ k' := by
      intro h; rw [h] at hj; simp [k'] at hj
    rw [map_sum, ← Finset.sum_neg_distrib]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [Equiv.Perm.sign_mul, Equiv.Perm.sign_swap hne, pm_mul, map_smul, Module.End.mul_apply]
    simp
    rfl
  have hA := h0 (pm π ξ) (hP π ξ hξ)
  rw [hdec, hcomm, sub_eq_zero] at hA
  have h2 := congrArg (pm π) hA
  rw [← Module.End.mul_apply, ← pm_mul, hπ2, pm_one, Module.End.one_apply, map_sum] at h2
  conv_rhs => rw [h2]
  refine Finset.sum_congr rfl fun j hj => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
  have hj1 : π j = j := by
    refine Equiv.swap_apply_of_ne_of_ne ?_ ?_
    · intro h; rw [h] at hj; simp [k'] at hj
    · intro h; rw [h] at hj; omega
  have e : Equiv.swap j i = π * Equiv.swap j k' * π := by
    rw [Equiv.mul_swap_eq_swap_mul π j k', hj1, hπ, Equiv.swap_apply_left, mul_assoc, ← hπ, hπ2, mul_one]
  rw [e]
  simp only [pm_mul, Module.End.mul_apply]

/- English proof (translation)
Establish `hsplit : ∀ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p = ∑ i ∈ Finset.univ.filter (· < j), g i j + ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p), g j p`. Introduce `j hj`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hj`. Establish `hu : Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j) = Finset.univ.filter (· < j) ∪ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p)`. Use extensionality with `p`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.lt_def, ne_eq, Fin.ext_iff]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[hu, Finset.sum_union]`. Use `congr 1`. Conclude with `Finset.sum_congr rfl fun i _ => hg j i`.

Rewrite using `[Finset.disjoint_filter]`. Introduce `p _ h1 h2`. Rewrite `h1`, `h2` using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, two_nsmul]`.

Use `congr 1`. Use `Finset.sum_comm' fun j p => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]`. Use linear arithmetic over natural numbers and integers.
-/
theorem symm_sum {m k : ℕ} {V : Type} [AddCommMonoid V] (g : Fin m → Fin m → V) (hg : ∀ i j, g i j = g j i) :
    ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k),
      ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p =
    2 • ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), ∑ i ∈ Finset.univ.filter (· < j), g i j := by
  have hsplit : ∀ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k),
      ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j), g j p =
      ∑ i ∈ Finset.univ.filter (· < j), g i j +
        ∑ p ∈ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p), g j p := by
    intro j hj
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hj
    have hu : Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ p ≠ j) =
        Finset.univ.filter (· < j) ∪ Finset.univ.filter (fun p : Fin m => (p : ℕ) < k ∧ j < p) := by
      ext p
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_union, Fin.lt_def, ne_eq, Fin.ext_iff]
      omega
    rw [hu, Finset.sum_union]
    · congr 1
      exact Finset.sum_congr rfl fun i _ => hg j i
    · rw [Finset.disjoint_filter]
      intro p _ h1 h2
      rw [Fin.lt_def] at h1 h2
      omega
  rw [Finset.sum_congr rfl hsplit, Finset.sum_add_distrib, two_nsmul]
  congr 1
  refine Finset.sum_comm' fun j p => ?_
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Fin.lt_def]
  omega

/- English proof (translation)
Simplify using `only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]`. Use `conv_lhs => rw [Finset.sum_comm]`. Use `conv_rhs => rw [Finset.sum_comm]`. Apply `Finset.sum_congr rfl` to reduce the goal to its premises. Introduce `σ hσ`.

Rewrite `hσ` using `[mem_firstG]`. Establish `h1 : ∀ j, pm σ (Om E j ξ) = Om E (σ j) (pm σ ξ)` using `fun j => LinearMap.congr_fun (hT σ j) ξ`. Repeatedly rewrite using `[h1]`. Use `Finset.sum_equiv σ ?_ (fun _ _ => rfl)` and prove the remaining obligations. Introduce `j`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion. Introduce `hj`. Assume the negation of the conclusion as `hc`. Rewrite `hc` using `[not_lt]`.

Establish `h3` using `σ.injective (hσ (σ j) hc)`. Rewrite `hc` using `[h3]`. Use linear arithmetic over natural numbers and integers. Introduce `hj`. Assume the negation of the conclusion as `hc`.

Rewrite `hc` using `[not_lt]`. Rewrite `hj` using `[hσ j hc]`. Use linear arithmetic over natural numbers and integers.
-/
theorem om_alt {m : ℕ} (E : Fin n → Fin n → Module.End ℂ M) (hT : ∀ (σ : Equiv.Perm (Fin m)) (p : Fin m),
      pm σ * Om E p = (Om E (σ p) * pm σ : Module.End ℂ (TV n M (Fin m)))) (k : ℕ) (ξ : TV n M (Fin m)) :
    alt (firstG m k) (∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j ξ) =
      ∑ j ∈ Finset.univ.filter (fun j : Fin m => (j : ℕ) < k), Om E j (alt (firstG m k) ξ) := by
  simp only [alt, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_smul]
  conv_lhs => rw [Finset.sum_comm]
  conv_rhs => rw [Finset.sum_comm]
  apply Finset.sum_congr rfl
  intro σ hσ
  rw [mem_firstG] at hσ
  have h1 : ∀ j, pm σ (Om E j ξ) = Om E (σ j) (pm σ ξ) := fun j => LinearMap.congr_fun (hT σ j) ξ
  simp_rw [h1]
  refine Finset.sum_equiv σ ?_ (fun _ _ => rfl)
  intro j
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · intro hj
    by_contra hc
    rw [not_lt] at hc
    have h3 := σ.injective (hσ (σ j) hc)
    rw [h3] at hc
    omega
  · intro hj
    by_contra hc
    rw [not_lt] at hc
    rw [hσ j hc] at hj
    omega

/- English proof (translation)
Establish `pres : ∀ (L : List ℕ), ∀ y ∈ Y, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y ∈ Y`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro y hy`. Simplify using `using hy`.

Consider the case `cons r L ih`. Introduce `y hy`. Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]`. Conclude with `Y.sub_mem (hT _ (ih y hy)) (Y.smul_mem _ (ih y hy))`. Establish `main : ∀ (L : List ℕ), (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0 → ∃ z ∈ Y, z ≠ 0 ∧ ∃ r : ℕ, T z = μ r • z`.

Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => intro h`. Simplify using `at h`. Conclude with `absurd h hy0`.

Consider the case `cons r L ih`. Introduce `h`. Distinguish the cases in `hz : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0`. Conclude with `ih hz`. Use `⟨_, pres L y hy, hz, r, ?_⟩` and prove the remaining obligations.

Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply, Module.algebraMap_end_apply] at h`. Conclude with `sub_eq_zero.mp h`. Conclude with `main L (by rw [hL]; rfl)`.
-/
theorem eigen {V : Type} [AddCommGroup V] [Module ℂ V] (Y : Submodule ℂ V) (T : Module.End ℂ V)
    (hT : ∀ y ∈ Y, T y ∈ Y) (μ : ℕ → ℂ) (L : List ℕ) (hL : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod = 0)
    (y : V) (hy : y ∈ Y) (hy0 : y ≠ 0) : ∃ z ∈ Y, z ≠ 0 ∧ ∃ r : ℕ, T z = μ r • z := by
  have pres : ∀ (L : List ℕ), ∀ y ∈ Y, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y ∈ Y := by
    intro L
    induction L with
    | nil => intro y hy; simpa using hy
    | cons r L ih =>
      intro y hy
      simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
        Module.algebraMap_end_apply]
      exact Y.sub_mem (hT _ (ih y hy)) (Y.smul_mem _ (ih y hy))
  have main : ∀ (L : List ℕ), (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0 →
      ∃ z ∈ Y, z ≠ 0 ∧ ∃ r : ℕ, T z = μ r • z := by
    intro L
    induction L with
    | nil => intro h; simp at h; exact absurd h hy0
    | cons r L ih =>
      intro h
      by_cases hz : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod y = 0
      · exact ih hz
      · refine ⟨_, pres L y hy, hz, r, ?_⟩
        simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, LinearMap.sub_apply,
          Module.algebraMap_end_apply] at h
        exact sub_eq_zero.mp h
  exact main L (by rw [hL]; rfl)

/- English proof (translation)
Establish `h2 : ∀ L : List ℕ, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod z = (L.map fun r => lam - μ r).prod • z`. Introduce `L`. Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons r L ih`.

Rewrite using `[List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h, Module.algebraMap_end_apply, ← sub_smul, smul_smul, List.map_cons, List.prod_cons, mul_comm]`. Establish `h3` using `h2 L`. Rewrite `h3` using `[hL, LinearMap.zero_apply]`. Establish `h4` using `(smul_eq_zero.mp h3.symm).resolve_right hz`. Take `⟨r, -, hr⟩` from `List.mem_map.mp (List.prod_eq_zero_iff.mp h4)`.

Conclude with `⟨r, sub_eq_zero.mp hr⟩`.
-/
theorem eigen_val {V : Type} [AddCommGroup V] [Module ℂ V] (T : Module.End ℂ V) (μ : ℕ → ℂ) (L : List ℕ)
    (hL : (L.map fun r => T - algebraMap ℂ _ (μ r)).prod = 0) (z : V) (hz : z ≠ 0) (lam : ℂ) (h : T z = lam • z) :
    ∃ r : ℕ, lam = μ r := by
  have h2 : ∀ L : List ℕ, (L.map fun r => T - algebraMap ℂ _ (μ r)).prod z = (L.map fun r => lam - μ r).prod • z := by
    intro L
    induction L with
    | nil => simp
    | cons r L ih =>
      rw [List.map_cons, List.prod_cons, Module.End.mul_apply, ih, map_smul, LinearMap.sub_apply, h,
        Module.algebraMap_end_apply, ← sub_smul, smul_smul, List.map_cons, List.prod_cons, mul_comm]
  have h3 := h2 L
  rw [hL, LinearMap.zero_apply] at h3
  have h4 := (smul_eq_zero.mp h3.symm).resolve_right hz
  obtain ⟨r, -, hr⟩ := List.mem_map.mp (List.prod_eq_zero_iff.mp h4)
  exact ⟨r, sub_eq_zero.mp hr⟩

end WallAlgP

end PositivityTheory.Rg.Cz

end
