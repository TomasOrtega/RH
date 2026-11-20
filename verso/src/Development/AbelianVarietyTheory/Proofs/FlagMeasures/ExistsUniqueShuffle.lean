import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.IsMirClass
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsColReduced

open Polynomial Formalism.MainNotions.ArithmeticCylinders GlobalTheory.GLq GlobalTheory.GLm Formalism.L2.DIV GlobalTheory.FinGL.Bruhat
open scoped Classical

namespace GlobalTheory.GLm.Shuffle

variable {g : ℕ} [Fact g.Prime] {n : ℕ}

/- English proof (translation)
Establish `hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ))`. Use extensionality with `r j`. Simplify using `[mono]`. Establish `hu : IsUnit (mono (F` using `ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by`. Use `IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_` and prove the remaining obligations.

Use extensionality with `r j`. Rewrite using `[mul_mono]`. Simplify using `[mono, Matrix.one_apply]`. Unfold `pm toG`. Rewrite using `[hm, dif_pos hu]`.

Both sides reduce to the same expression.
-/
theorem pm_eq_mono (σ : Equiv.Perm (Fin n)) : (pm g σ : Mt g n) = mono (σ, fun _ => 1) := by
  have hm : (fun r j : Fin n => if r = σ j then (1 : ZMod g) else 0) = mono (σ, fun _ => (1 : (ZMod g)ˣ)) := by
    ext r j; simp [mono]
  have hu : IsUnit (mono (F := ZMod g) (σ, fun _ => (1 : (ZMod g)ˣ))) := by
    refine IsUnit.of_mul_eq_one (mono (σ.symm, fun _ => (1 : (ZMod g)ˣ))) ?_
    ext r j
    rw [mul_mono]
    simp [mono, Matrix.one_apply]
  unfold pm toG
  rw [hm, dif_pos hu]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩, fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩`.
-/
theorem isUniUp_iff (u : Gn g n) : IsUniUp (u : Mt g n) ↔ u ∈ unip (ZMod g) n :=
  ⟨fun h => ⟨fun i j hij => (h i j).1 hij, fun i => (h i i).2 rfl⟩,
    fun h a b => ⟨fun hab => unip_lower h hab, fun e => e ▸ unip_diag h a⟩⟩

/- English proof (translation)
Rewrite using `[mem_blockTri]`. Prove the components needed by the constructor for the conclusion. Introduce `h i j hij`. Apply the tactic sequence `by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij`. Conclude with `h i j hj (not_lt.1 hi)`.

Introduce `h i j hj hi`. Conclude with `h i j (by simp [hj, not_lt.2 hi])`.
-/
theorem inPar_iff (a : ℕ) (p : Gn g n) :
    InPar a (p : Mt g n) ↔ p ∈ blockTri (κ := ZMod g) (fun i : Fin n => if (i : ℕ) < a then 0 else 1 : Fin n → ℕ) := by
  rw [mem_blockTri]
  constructor
  · intro h i j hij
    by_cases hi : (i : ℕ) < a <;> by_cases hj : (j : ℕ) < a <;> simp [hi, hj] at hij
    exact h i j hj (not_lt.1 hi)
  · intro h i j hj hi
    exact h i j (by simp [hj, not_lt.2 hi])

/- English proof (translation)
Establish `hv : u'⁻¹ * u ∈ unip (ZMod g) n` using `Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)`. Establish `hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n)` using `(inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))`. Establish `h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Establish `h2` using `congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)`.

Rewrite `h2` using `[Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul]`. Simplify using `only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2`. Rewrite `h2` using `[unip_diag hv]`. Assume the negation of the conclusion as `hc`. Rewrite `h2` using `[hq _ _ hr (not_lt.1 hc)]`.

Conclude with `one_ne_zero h2`.
-/
theorem block_of_eq {a : ℕ} {σ σ' : Equiv.Perm (Fin n)} {u u' p p' : Gn g n} (hu : IsUniUp (u : Mt g n))
    (hu' : IsUniUp (u' : Mt g n)) (hp : InPar a (p : Mt g n)) (hp' : InPar a (p' : Mt g n))
    (h : u * pm g σ * p = u' * pm g σ' * p') (r : Fin n) (hr : (σ.symm r : ℕ) < a) : (σ'.symm r : ℕ) < a := by
  have hv : u'⁻¹ * u ∈ unip (ZMod g) n :=
    Subgroup.mul_mem _ (Subgroup.inv_mem _ ((isUniUp_iff _).1 hu')) ((isUniUp_iff _).1 hu)
  have hq : InPar a ((p' * p⁻¹ : Gn g n) : Mt g n) :=
    (inPar_iff _ _).2 (Subgroup.mul_mem _ ((inPar_iff _ _).1 hp') (Subgroup.inv_mem _ ((inPar_iff _ _).1 hp)))
  have h1 : (u'⁻¹ * u) * pm g σ = pm g σ' * (p' * p⁻¹) := by
    calc (u'⁻¹ * u) * pm g σ = u'⁻¹ * (u * pm g σ * p) * p⁻¹ := by group
      _ = _ := by rw [h]; group
  have h2 := congrFun (congrFun (congrArg (fun z : Gn g n => (z : Mt g n)) h1) r) (σ.symm r)
  rw [Units.val_mul _ (pm g σ), Units.val_mul (pm g σ'), pm_eq_mono, pm_eq_mono, mul_mono, mono_mul] at h2
  simp only [Equiv.apply_symm_apply, Units.val_one, mul_one, one_mul] at h2
  rw [unip_diag hv] at h2
  by_contra hc
  rw [hq _ _ hr (not_lt.1 hc)] at h2
  exact one_ne_zero h2

noncomputable def key (S : Fin n → Prop) (r : Fin n) : ℕ := if S r then (r : ℕ) else n + r

/- English proof (translation)
Introduce `r s h`. Use `r.2` as an intermediate fact. Use `s.2` as an intermediate fact. Unfold `key at h`. Apply `Fin.ext` to reduce the goal to its premises.

Apply the tactic sequence `split_ifs at h <;> omega`.
-/
theorem key_injective (S : Fin n → Prop) : Function.Injective (key S) := by
  intro r s h
  have := r.2; have := s.2
  unfold key at h
  apply Fin.ext
  split_ifs at h <;> omega

/- English proof (translation)
Use `StrictMono.monotone fun i j hij => ?_` and prove the remaining obligations. Establish `h1` using `hσ i j hij`. Establish `h2 : (i : ℕ) < j` using `hij`. Use `(σ i).2` as an intermediate fact. Simplify using `only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢`.

Apply the tactic sequence `split_ifs <;> omega`.
-/
theorem key_mono {a : ℕ} {σ : Equiv.Perm (Fin n)} {S : Fin n → Prop} (hS : ∀ r, S r ↔ (σ.symm r : ℕ) < a)
    (hσ : ∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) : Monotone (key S ∘ σ) := by
  refine StrictMono.monotone fun i j hij => ?_
  have h1 := hσ i j hij
  have h2 : (i : ℕ) < j := hij
  have := (σ i).2
  simp only [Function.comp, key, hS, Equiv.symm_apply_apply, Fin.lt_def] at h1 ⊢
  split_ifs <;> omega

/- English proof (translation)
Use `set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS`. Use `set σ := Tuple.sort (key S) with hσ`. Establish `hm : Monotone (key S ∘ σ)` using `Tuple.monotone_sort _`. Establish `hlt : ∀ r, key S r < n ↔ S r`. Introduce `r`.

Use `r.2` as an intermediate fact. Unfold `key`. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Establish `hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a`. Establish `: (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a`.

Rewrite using `[Fin.card_filter_val_lt]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← this]`. Use `Finset.card_equiv (σ.trans s.symm) fun i => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]`.

Conclude with `hlt _`. Establish `hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a`. Introduce `j`. Rewrite using `[← hlt, ← hcard]`. Conclude with `(Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm`.

Use `⟨σ, fun i j hij hb => ?_, hiff⟩` and prove the remaining obligations. Establish `h1 : (key S ∘ σ) i < (key S ∘ σ) j` using `(hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij`. Establish `h2 : (i : ℕ) < j` using `hij`. Simplify using `only [Function.comp, key, hiff] at h1`. Rewrite using `[Fin.lt_def]`.

Apply the tactic sequence `split_ifs at h1 <;> omega`.
-/
theorem exists_shuffle {a : ℕ} (ha : a ≤ n) (s : Equiv.Perm (Fin n)) : ∃ σ : Equiv.Perm (Fin n),
    (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧
      ∀ j : Fin n, (s.symm (σ j) : ℕ) < a ↔ (j : ℕ) < a := by
  set S : Fin n → Prop := fun r => (s.symm r : ℕ) < a with hS
  set σ := Tuple.sort (key S) with hσ
  have hm : Monotone (key S ∘ σ) := Tuple.monotone_sort _
  have hlt : ∀ r, key S r < n ↔ S r := by
    intro r
    have := r.2
    unfold key
    split_ifs with h <;> simp [h]
  have hcard : (Finset.univ.filter fun i => (key S ∘ σ) i < n).card = a := by
    have : (Finset.univ.filter fun i : Fin n => (i : ℕ) < a).card = a := by
      rw [Fin.card_filter_val_lt]; omega
    rw [← this]
    refine Finset.card_equiv (σ.trans s.symm) fun i => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp]
    exact hlt _
  have hiff : ∀ j : Fin n, S (σ j) ↔ (j : ℕ) < a := by
    intro j
    rw [← hlt, ← hcard]
    exact (Tuple.lt_card_lt_iff_apply_lt_of_monotone hm).symm
  refine ⟨σ, fun i j hij hb => ?_, hiff⟩
  have h1 : (key S ∘ σ) i < (key S ∘ σ) j :=
    (hm.strictMono_of_injective ((key_injective S).comp σ.injective)) hij
  have h2 : (i : ℕ) < j := hij
  simp only [Function.comp, key, hiff] at h1
  rw [Fin.lt_def]
  split_ifs at h1 <;> omega

/- English proof (translation)
Introduce `g _ a n ha x`. Take `⟨m, u, hu, u', hu', hx⟩` from `exists_decomp x`. Take `⟨σ, hσ, hb⟩` from `exists_shuffle ha m.1`. Establish `hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n)`. Introduce `i j hj hi`.

Establish `h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n)`. Rewrite using `[← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc, Units.inv_mul_cancel_left]`. Establish `h2` using `congrFun (congrFun h1 (σ i)) j`. Rewrite `h2` using `[pm_eq_mono, mono_mul, mono_mul]`. Simplify using `only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2`.

Establish `h3 : j < m.1.symm (σ i)`. Use `(hb i).not.2 (not_lt.2 hi)` as an intermediate fact. Rewrite using `[Fin.lt_def]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h2, unip_lower hu' h3, mul_zero]`.

Establish `hu1` using `(isUniUp_iff u).2 hu`. Establish `hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x)` using `by group`. Use `⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `τ ⟨hτ, v, q, hv, hq, hx2⟩`. Establish `h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ)` using `key_mono (fun _ => Iff.rfl) hσ`.

Establish `h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ)` using `key_mono (fun r => ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ`. Conclude with `Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)`.
-/
theorem existsUnique_shuffle : ∀ (g : ℕ) [Fact g.Prime] (a n : ℕ), a ≤ n → ∀ x : Gn g n, ∃! σ : Equiv.Perm (Fin n), (∀ i j : Fin n, i < j → ((j : ℕ) < a ∨ a ≤ (i : ℕ)) → σ i < σ j) ∧ ∃ u p : Gn g n, IsUniUp (u : Mt g n) ∧ InPar a (p : Mt g n) ∧ x = u * pm g σ * p := by
  intro g _ a n ha x
  obtain ⟨m, u, hu, u', hu', hx⟩ := exists_decomp x
  obtain ⟨σ, hσ, hb⟩ := exists_shuffle ha m.1
  have hp : InPar a (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) := by
    intro i j hj hi
    have h1 : (pm g σ : Mt g n) * (((pm g σ)⁻¹ * u⁻¹ * x : Gn g n) : Mt g n) = mono m * (u' : Mt g n) := by
      rw [← Units.val_mul, ← mul_assoc, mul_inv_cancel_left, Units.val_mul, hx, Matrix.mul_assoc,
        Units.inv_mul_cancel_left]
    have h2 := congrFun (congrFun h1 (σ i)) j
    rw [pm_eq_mono, mono_mul, mono_mul] at h2
    simp only [Equiv.symm_apply_apply, Units.val_one, one_mul] at h2
    have h3 : j < m.1.symm (σ i) := by
      have := (hb i).not.2 (not_lt.2 hi)
      rw [Fin.lt_def]; omega
    rw [h2, unip_lower hu' h3, mul_zero]
  have hu1 := (isUniUp_iff u).2 hu
  have hx1 : x = u * pm g σ * ((pm g σ)⁻¹ * u⁻¹ * x) := by group
  refine ⟨σ, ⟨hσ, u, _, hu1, hp, hx1⟩, ?_⟩
  rintro τ ⟨hτ, v, q, hv, hq, hx2⟩
  have h1 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ σ) := key_mono (fun _ => Iff.rfl) hσ
  have h2 : Monotone (key (fun r => (σ.symm r : ℕ) < a) ∘ τ) := key_mono (fun r =>
    ⟨block_of_eq hu1 hv hp hq (hx1.symm.trans hx2) r, block_of_eq hv hu1 hq hp (hx2.symm.trans hx1) r⟩) hτ
  exact Equiv.ext fun i => key_injective _ (congrFun (Tuple.unique_monotone h2 h1) i)

end GlobalTheory.GLm.Shuffle
