import Mathlib
import Development.AbelianVarietyTheory.Definitions.CommutativeAlgebra.InvariantSubspaceMobiusInverseRecEqOfFinrankLt
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.InvariantSubspaceMobiusInverseCharpolyLinearEquiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyEqFinsumPsiStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.CharpolyBlockAndInvariantUnderStabilizerNilradicStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.SumPrimitiveEndClassFunctionRestrictMixedSubspacStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyTransversalSubspacesStatement
import Development.AbelianVarietyTheory.Proofs.CharacterTheory.FinsumMobiusInverseCharpolyInvariantLeStatement

open Polynomial GlobalTheory.CuspGL

noncomputable section

namespace GlobalTheory.CuspGL.PsiPrimitive

open Classical in

/- English proof (translation)
Rewrite using `[finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]`. Establish `h1 : ∀ i : {a // p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = f i` using `fun i => by`. Rewrite using `[dif_pos i.2]`. Establish `h2 : ∀ i : {a // ¬ p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0` using `fun i => by`. Rewrite using `[dif_neg i.2]`.

Simplify using `only [h1, h2, Finset.sum_const_zero, add_zero]`.
-/
theorem finsum_sub {α : Type} [Fintype α] (p : α → Prop) (f : {a // p a} → ℂ) :
    ∑ᶠ x, f x = ∑ a, if h : p a then f ⟨a, h⟩ else 0 := by
  rw [finsum_eq_sum_of_fintype, ← Fintype.sum_subtype_add_sum_subtype p]
  have h1 : ∀ i : {a // p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = f i := fun i => by
    rw [dif_pos i.2]
  have h2 : ∀ i : {a // ¬ p a}, (if h : p i.1 then f ⟨i.1, h⟩ else 0) = 0 := fun i => by
    rw [dif_neg i.2]
  simp only [h1, h2, Finset.sum_const_zero, add_zero]

open Classical in

def res {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (W : Submodule F V) (k : Module.End F V) : ℂ :=
  if hk : ∀ x ∈ W, k x ∈ W then psi s W (k.restrict hk) else 0

/- English proof (translation)
Rewrite using `[psi_eq s V g]`. Establish `hpoly : LinearMap.charpoly g = 1`. Establish `hdeg : (LinearMap.charpoly g).natDegree = 0`. Rewrite using `[LinearMap.charpoly_natDegree]`. Conclude with `Module.finrank_zero_of_subsingleton`.

Conclude with `Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g) hdeg`. Establish `hs1 : s 1 = 0`. Establish `h11` using `hs 1 1 monic_one monic_one`. Rewrite `h11` using `[one_mul]`. Take the linear combination `-h11`.

Establish `hempty : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W}`. Use `⟨fun W => W.2.1 ?_⟩` and prove the remaining obligations. Use `eq_top_iff.2 fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Subsingleton.elim x 0]`. Conclude with `W.1.zero_mem`.

Rewrite using `[hpoly, hs1, finsum_of_isEmpty, sub_zero]`.
-/
theorem psi_trivial {F : Type} [Field F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V] [Subsingleton V] (g : Module.End F V) :
    psi s V g = 0 := by
  rw [psi_eq s V g]
  have hpoly : LinearMap.charpoly g = 1 := by
    have hdeg : (LinearMap.charpoly g).natDegree = 0 := by
      rw [LinearMap.charpoly_natDegree]
      exact Module.finrank_zero_of_subsingleton
    exact Polynomial.eq_one_of_monic_natDegree_zero (LinearMap.charpoly_monic g) hdeg
  have hs1 : s 1 = 0 := by
    have h11 := hs 1 1 monic_one monic_one
    rw [one_mul] at h11
    linear_combination -h11
  have hempty : IsEmpty {W : Submodule F V // W ≠ ⊤ ∧ ∀ x ∈ W, g x ∈ W} := by
    refine ⟨fun W => W.2.1 ?_⟩
    refine eq_top_iff.2 fun x _ => ?_
    rw [Subsingleton.elim x 0]
    exact W.1.zero_mem
  rw [hpoly, hs1, finsum_of_isEmpty, sub_zero]

/- English proof (translation)
Establish `htop : ∀ x ∈ (⊤ : Submodule F V), k x ∈ (⊤ : Submodule F V)` using `fun _ _ => Submodule.mem_top`. Unfold `res`. Rewrite using `[dif_pos htop]`. Establish `hconj` using `GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s (⊤ : Submodule F V) V Submodule.topEquiv (k.restrict htop)`. Rewrite using `[← hconj]`.

Use `congr 1`.
-/
theorem res_top {F : Type} [Field F] (s : F[X] → ℂ) {V : Type} [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (k : Module.End F V) : res s ⊤ k = psi s V k := by
  have htop : ∀ x ∈ (⊤ : Submodule F V), k x ∈ (⊤ : Submodule F V) := fun _ _ => Submodule.mem_top
  unfold res
  rw [dif_pos htop]
  have hconj := GlobalTheory.T.invariantSubspaceMobiusInverseCharpoly_linearEquiv_conj F s (⊤ : Submodule F V) V Submodule.topEquiv (k.restrict htop)
  rw [← hconj]
  congr 1

/- English proof (translation)
Establish `: Finite V` using `Module.finite_of_finite F`. Establish `: Finite (Module.End F V)` using `Finite.of_injective (fun f : Module.End F V => (f : V → V)) fun a b h => LinearMap.ext (congrFun h)`. Establish `: Finite (Submodule F V)` using `Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective`. Set `_ : Fintype (Module.End F V)` to `Fintype.ofFinite _`. Set `_ : Fintype (Submodule F V)` to `Fintype.ofFinite _`.

Introduce `A hA0 hAT g hg`. Use `set H : Finset (Module.End F V) := Finset.univ.filter fun h => h ∈ nilRad A with hH`. Establish `memH : ∀ h, h ∈ H ↔ h ∈ nilRad A` using `fun h => by simp [hH]`. Establish `sum_H : ∀ f : Module.End F V → ℂ, ∑ h ∈ H, f h = ∑ h, if h ∈ nilRad A then f h else 0` using `fun f => by`. Rewrite using `[hH, Finset.sum_filter]`.

Establish `card_H : ((Nat.card (nilRad A) : ℕ) : ℂ) = (H.card : ℂ)`. Rewrite using `[Nat.card_eq_fintype_card, Fintype.card_subtype]`. Establish `res_bot : ∀ k : Module.End F V, res s (⊥ : Submodule F V) k = 0`. Introduce `k`. Unfold `res`.

Use `split_ifs`. Conclude with `psi_trivial s hs _ _`. Both sides reduce to the same expression. Establish `s_cp : ∀ k : Module.End F V, s (LinearMap.charpoly k) = ∑ W : Submodule F V, res s W k`. Introduce `k`.

Conclude with `(GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F V s k).trans (finsum_sub (fun W : Submodule F V => ∀ x ∈ W, k x ∈ W) fun W => psi s W.1 (k.restrict W.2))`. Establish `res_le : ∀ h ∈ nilRad A, ∀ W : Submodule F V, W ≤ A → res s W (g + h) = res s W g`. Introduce `h hh W hWA`. Establish `hh' : (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0` using `hh`. Establish `h0 : ∀ x ∈ W, h x = 0` using `fun x hx => hh'.2 x (hWA hx)`.

Unfold `res`. Distinguish the cases in `hk : ∀ x ∈ W, g x ∈ W`. Establish `hk' : ∀ x ∈ W, (g + h) x ∈ W` using `fun x hx => by`. Simplify `hk x hx` using `[h0 x hx]`. Rewrite using `[dif_pos hk', dif_pos hk]`.

Use `congr 1`. Use extensionality with `x`. Simplify using `[h0 x.1 x.2]`. Establish `hk' : ¬ ∀ x ∈ W, (g + h) x ∈ W` using `fun hk' => hk fun x hx => by`. Simplify `hk' x hx` using `[h0 x hx]`.

Rewrite using `[dif_neg hk', dif_neg hk]`. Establish `res_mixed : ∀ W : Submodule F V, W ≠ ⊤ → W ⊓ A ≠ ⊥ → ¬ W ≤ A → ∑ h ∈ H, res s W (g + h) = 0`. Introduce `W hWT hWA hWle`. Establish `key` using `(finsum_sub (fun h : Module.End F V => h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W) fun h => psi s W ((g + h.1).restrict h.2.2)).symm.trans (GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace F V A W g hg hWA hWle (psi s W) (ih W hWT))`. Rewrite using `[← key, sum_H]`.

Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hh : h ∈ nilRad A <;> simp [hh, res]`. Establish `sum_le : ∑ W : Submodule F V, (if W ≤ A then res s W g else 0) = s (LinearMap.charpoly (g.restrict hg))`. Establish `key` using `(finsum_sub (fun W : Submodule F V => W ≤ A ∧ ∀ x ∈ W, g x ∈ W) fun W => psi s W.1 (g.restrict W.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le F V s A g hg)`. Rewrite using `[← key]`.

Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hW : W ≤ A <;> by_cases hk : ∀ x ∈ W, g x ∈ W <;> simp [hW, hk, res]`. Establish `sum_disj : ∑ W : Submodule F V, (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) = (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)))`. Establish `key` using `(finsum_sub (fun x : Module.End F V × Submodule F V => x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2) fun x => psi s x.1.2 ((g + x.1.1).restrict x.2.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces F V s A g hg)`. Rewrite using `[← card_H, ← key, Fintype.sum_prod_type, Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Distinguish the cases in `hW : W ⊓ A = ⊥`. Rewrite using `[if_pos hW, sum_H]`. Use `Finset.sum_congr rfl fun h _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hh : h ∈ nilRad A <;> simp [hh, hW, res]`.

Rewrite using `[if_neg hW]`. Use `symm`. Use `Finset.sum_eq_zero fun h _ => ?_` and prove the remaining obligations. Simplify using `[hW]`. Establish `split : ∀ W : Submodule F V, W ≠ ⊤ → ∑ h ∈ H, res s W (g + h) = (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) + (if W ≤ A then (H.card : ℂ) * res s W g else 0)`.

Introduce `W hWT`. Distinguish the cases in `hb : W = ⊥`. Substitute `hb` using the available equality. Simplify using `[res_bot]`. Distinguish the cases in `hle : W ≤ A`.

Establish `hmeet : W ⊓ A ≠ ⊥` using `by rw [inf_eq_left.2 hle]; exact hb`. Rewrite using `[if_neg hmeet, if_pos hle, zero_add, Finset.sum_congr rfl fun h hh => res_le h ((memH h).1 hh) W hle, Finset.sum_const, nsmul_eq_mul]`. Distinguish the cases in `hd : W ⊓ A = ⊥`. Rewrite using `[if_pos hd, if_neg hle, add_zero]`. Rewrite using `[if_neg hd, if_neg hle, add_zero]`.

Conclude with `res_mixed W hWT hd hle`. Establish `s_split : s (LinearMap.charpoly g) = s (LinearMap.charpoly (g.restrict hg)) + s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx)))`. Rewrite using `[(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).1]`. Conclude with `hs _ _ (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)`. Establish `s_const : ∑ h ∈ H, s (LinearMap.charpoly (g + h)) = (H.card : ℂ) * s (LinearMap.charpoly g)`.

Rewrite using `[Finset.sum_congr rfl fun h hh => by rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).2 h ((memH h).1 hh)], Finset.sum_const, nsmul_eq_mul]`. Establish `psi_expand : ∀ k : Module.End F V, psi s V k = s (LinearMap.charpoly k) - ∑ W ∈ Finset.univ.erase ⊤, res s W k`. Introduce `k`. Rewrite using `[s_cp, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⊤), res_top]`. Expand and normalize the polynomial expressions, which then agree.

Establish `proper : ∑ W ∈ Finset.univ.erase ⊤, ∑ h ∈ H, res s W (g + h) = (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) + (H.card : ℂ) * s (LinearMap.charpoly (g.restrict hg))`. Rewrite using `[Finset.sum_congr rfl fun W hW => split W (Finset.ne_of_mem_erase hW), Finset.sum_add_distrib]`. Establish `htop1 : ¬ (⊤ : Submodule F V) ⊓ A = ⊥` using `by rw [top_inf_eq]; exact hA0`. Establish `htop2 : ¬ (⊤ : Submodule F V) ≤ A` using `fun h => hAT (top_le_iff.1 h)`. Rewrite using `[Finset.sum_erase _ (by rw [if_neg htop1]), Finset.sum_erase _ (by rw [if_neg htop2]), sum_disj, ← sum_le, Finset.mul_sum]`.

Use `congr 1`. Use `Finset.sum_congr rfl fun W _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`. Rewrite using `[finsum_mem_def, finsum_eq_sum_of_fintype]`. Simplify using `only [Set.indicator_apply]`.

Rewrite using `[← sum_H, Finset.sum_congr rfl fun h _ => psi_expand (g + h), Finset.sum_sub_distrib, Finset.sum_comm, proper, s_const, s_split]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem step {F : Type} [Field F] [Finite F] (s : F[X] → ℂ) (hs : IsAdditive s) (V : Type)
    [AddCommGroup V] [Module F V] [FiniteDimensional F V]
    (ih : ∀ W : Submodule F V, W ≠ ⊤ → IsPrimitive (psi s W)) : IsPrimitive (psi s V) := by
  classical
  have : Finite V := Module.finite_of_finite F
  have : Finite (Module.End F V) :=
    Finite.of_injective (fun f : Module.End F V => (f : V → V)) fun a b h => LinearMap.ext (congrFun h)
  have : Finite (Submodule F V) :=
    Finite.of_injective (fun W : Submodule F V => (W : Set V)) SetLike.coe_injective
  let _ : Fintype (Module.End F V) := Fintype.ofFinite _
  let _ : Fintype (Submodule F V) := Fintype.ofFinite _
  intro A hA0 hAT g hg
  set H : Finset (Module.End F V) := Finset.univ.filter fun h => h ∈ nilRad A with hH
  have memH : ∀ h, h ∈ H ↔ h ∈ nilRad A := fun h => by simp [hH]
  have sum_H : ∀ f : Module.End F V → ℂ,
      ∑ h ∈ H, f h = ∑ h, if h ∈ nilRad A then f h else 0 := fun f => by
    rw [hH, Finset.sum_filter]
  have card_H : ((Nat.card (nilRad A) : ℕ) : ℂ) = (H.card : ℂ) := by
    rw [Nat.card_eq_fintype_card, Fintype.card_subtype]
  have res_bot : ∀ k : Module.End F V, res s (⊥ : Submodule F V) k = 0 := by
    intro k
    unfold res
    split_ifs
    · exact psi_trivial s hs _ _
    · rfl
  have s_cp : ∀ k : Module.End F V, s (LinearMap.charpoly k) = ∑ W : Submodule F V, res s W k := by
    intro k
    exact (GlobalTheory.T.apply_charpoly_eq_finsum_psi_invariant_submodules F V s k).trans
      (finsum_sub (fun W : Submodule F V => ∀ x ∈ W, k x ∈ W) fun W => psi s W.1 (k.restrict W.2))
  have res_le : ∀ h ∈ nilRad A, ∀ W : Submodule F V, W ≤ A → res s W (g + h) = res s W g := by
    intro h hh W hWA
    have hh' : (∀ x, h x ∈ A) ∧ ∀ x ∈ A, h x = 0 := hh
    have h0 : ∀ x ∈ W, h x = 0 := fun x hx => hh'.2 x (hWA hx)
    unfold res
    by_cases hk : ∀ x ∈ W, g x ∈ W
    · have hk' : ∀ x ∈ W, (g + h) x ∈ W := fun x hx => by
        simpa [h0 x hx] using hk x hx
      rw [dif_pos hk', dif_pos hk]
      congr 1
      ext x
      simp [h0 x.1 x.2]
    · have hk' : ¬ ∀ x ∈ W, (g + h) x ∈ W := fun hk' => hk fun x hx => by
        simpa [h0 x hx] using hk' x hx
      rw [dif_neg hk', dif_neg hk]
  have res_mixed : ∀ W : Submodule F V, W ≠ ⊤ → W ⊓ A ≠ ⊥ → ¬ W ≤ A →
      ∑ h ∈ H, res s W (g + h) = 0 := by
    intro W hWT hWA hWle
    have key := (finsum_sub (fun h : Module.End F V => h ∈ nilRad A ∧ ∀ x ∈ W, (g + h) x ∈ W)
      fun h => psi s W ((g + h.1).restrict h.2.2)).symm.trans
        (GlobalTheory.T.sum_primitiveEndClassFunction_restrict_mixed_subspace F V A W g hg hWA hWle (psi s W) (ih W hWT))
    rw [← key, sum_H]
    refine Finset.sum_congr rfl fun h _ => ?_
    by_cases hh : h ∈ nilRad A <;> simp [hh, res]
  have sum_le : ∑ W : Submodule F V, (if W ≤ A then res s W g else 0) =
      s (LinearMap.charpoly (g.restrict hg)) := by
    have key := (finsum_sub (fun W : Submodule F V => W ≤ A ∧ ∀ x ∈ W, g x ∈ W)
      fun W => psi s W.1 (g.restrict W.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_invariant_le F V s A g hg)
    rw [← key]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ≤ A <;> by_cases hk : ∀ x ∈ W, g x ∈ W <;> simp [hW, hk, res]
  have sum_disj : ∑ W : Submodule F V,
      (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    have key := (finsum_sub
      (fun x : Module.End F V × Submodule F V =>
        x.1 ∈ nilRad A ∧ x.2 ⊓ A = ⊥ ∧ ∀ v ∈ x.2, (g + x.1) v ∈ x.2)
      fun x => psi s x.1.2 ((g + x.1.1).restrict x.2.2.2)).symm.trans (GlobalTheory.T.finsum_mobiusInverseCharpoly_transversal_subspaces F V s A g hg)
    rw [← card_H, ← key, Fintype.sum_prod_type, Finset.sum_comm]
    refine Finset.sum_congr rfl fun W _ => ?_
    by_cases hW : W ⊓ A = ⊥
    · rw [if_pos hW, sum_H]
      refine Finset.sum_congr rfl fun h _ => ?_
      by_cases hh : h ∈ nilRad A <;> simp [hh, hW, res]
    · rw [if_neg hW]
      symm
      refine Finset.sum_eq_zero fun h _ => ?_
      simp [hW]
  have split : ∀ W : Submodule F V, W ≠ ⊤ →
      ∑ h ∈ H, res s W (g + h) =
        (if W ⊓ A = ⊥ then ∑ h ∈ H, res s W (g + h) else 0) +
          (if W ≤ A then (H.card : ℂ) * res s W g else 0) := by
    intro W hWT
    by_cases hb : W = ⊥
    · subst hb
      simp [res_bot]
    by_cases hle : W ≤ A
    · have hmeet : W ⊓ A ≠ ⊥ := by rw [inf_eq_left.2 hle]; exact hb
      rw [if_neg hmeet, if_pos hle, zero_add,
        Finset.sum_congr rfl fun h hh => res_le h ((memH h).1 hh) W hle, Finset.sum_const, nsmul_eq_mul]
    by_cases hd : W ⊓ A = ⊥
    · rw [if_pos hd, if_neg hle, add_zero]
    · rw [if_neg hd, if_neg hle, add_zero]
      exact res_mixed W hWT hd hle
  have s_split : s (LinearMap.charpoly g) = s (LinearMap.charpoly (g.restrict hg)) +
      s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) := by
    rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).1]
    exact hs _ _ (LinearMap.charpoly_monic _) (LinearMap.charpoly_monic _)
  have s_const : ∑ h ∈ H, s (LinearMap.charpoly (g + h)) = (H.card : ℂ) * s (LinearMap.charpoly g) := by
    rw [Finset.sum_congr rfl fun h hh => by rw [(GlobalTheory.T.charpoly_block_and_invariant_under_stabilizerNilradical F V A g hg).2 h ((memH h).1 hh)],
      Finset.sum_const, nsmul_eq_mul]
  have psi_expand : ∀ k : Module.End F V, psi s V k =
      s (LinearMap.charpoly k) - ∑ W ∈ Finset.univ.erase ⊤, res s W k := by
    intro k
    rw [s_cp, ← Finset.add_sum_erase _ _ (Finset.mem_univ ⊤), res_top]
    ring
  have proper : ∑ W ∈ Finset.univ.erase ⊤, ∑ h ∈ H, res s W (g + h) =
      (H.card : ℂ) * s (LinearMap.charpoly (A.mapQ A g (fun x hx => hg x hx))) +
        (H.card : ℂ) * s (LinearMap.charpoly (g.restrict hg)) := by
    rw [Finset.sum_congr rfl fun W hW => split W (Finset.ne_of_mem_erase hW), Finset.sum_add_distrib]
    have htop1 : ¬ (⊤ : Submodule F V) ⊓ A = ⊥ := by rw [top_inf_eq]; exact hA0
    have htop2 : ¬ (⊤ : Submodule F V) ≤ A := fun h => hAT (top_le_iff.1 h)
    rw [Finset.sum_erase _ (by rw [if_neg htop1]), Finset.sum_erase _ (by rw [if_neg htop2]),
      sum_disj, ← sum_le, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun W _ => ?_
    split_ifs <;> simp
  rw [finsum_mem_def, finsum_eq_sum_of_fintype]
  simp only [Set.indicator_apply]
  rw [← sum_H, Finset.sum_congr rfl fun h _ => psi_expand (g + h), Finset.sum_sub_distrib,
    Finset.sum_comm, proper, s_const, s_split]
  ring

end GlobalTheory.CuspGL.PsiPrimitive

namespace GlobalTheory.CuspGL

/- English proof (translation)
Introduce `F _ _ V _ _ _ s hs`. It suffices to establish `key : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V], Module.finrank F V < n → IsPrimitive (psi s V) from key _ V (Nat.lt_succ_self _)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => intro V _ _ _ h`.

Conclude with `absurd h (Nat.not_lt_zero _)`. Consider the case `succ n ih`. Introduce `V _ _ _ h`. Conclude with `PsiPrimitive.step s hs V fun W hW => ih W (lt_of_lt_of_le (Submodule.finrank_lt hW) (Nat.lt_succ_iff.1 h))`.
-/
theorem isPrimitive_psi : ∀ (F : Type) [Field F] [Finite F] (V : Type) [AddCommGroup V] [Module F V]
    [FiniteDimensional F V] (s : F[X] → ℂ), IsAdditive s → IsPrimitive (psi s V) := by
  intro F _ _ V _ _ _ s hs
  suffices key : ∀ n : ℕ, ∀ (V : Type) [AddCommGroup V] [Module F V] [FiniteDimensional F V],
      Module.finrank F V < n → IsPrimitive (psi s V) from key _ V (Nat.lt_succ_self _)
  intro n
  induction n with
  | zero => intro V _ _ _ h; exact absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    intro V _ _ _ h
    exact PsiPrimitive.step s hs V fun W hW =>
      ih W (lt_of_lt_of_le (Submodule.finrank_lt hW) (Nat.lt_succ_iff.1 h))

end GlobalTheory.CuspGL
