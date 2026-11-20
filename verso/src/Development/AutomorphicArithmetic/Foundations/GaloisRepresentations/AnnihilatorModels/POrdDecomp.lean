import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.AnnihilatorModels.SameNormBasic

open CategoryTheory AlgebraicGeometry TensorProduct
open UpperTheory.Gal.crystallineComparison

namespace UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Rewrite using `[Finset.sum_eq_multiset_sum]`. Establish `h` using `Multiset.sum_map_singleton (s.val.map f)`. Rewrite `h` using `[Multiset.map_map]`. Conclude with `h.symm`.
-/
private theorem val_map_sum {α P : Type} (s : Finset α) (f : α → P) :
    s.val.map f = ∑ x ∈ s, ({f x} : Multiset P) := by
  rw [Finset.sum_eq_multiset_sum]
  have h := Multiset.sum_map_singleton (s.val.map f)
  rw [Multiset.map_map] at h
  exact h.symm

open Classical in
/- English proof (translation)
Take `⟨hbij, hrk, -⟩` from `hIn k H C hC`. Use `Finset.sum_bij (fun D _ => D.map C.mkQ) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `D hD`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢`. Use `hrk D hD.2` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Introduce `D₁ h₁ D₂ h₂ he`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂`. Conclude with `Subtype.ext_iff.mp (@hbij.1 ⟨D₁, h₁.2⟩ ⟨D₂, h₂.2⟩ he)`. Introduce `E hE`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hE`. Take `⟨⟨D, hD⟩, hDE⟩` from `hbij.2 E`. Use `⟨D, ?_, hDE⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Use `⟨?_, hD⟩` and prove the remaining obligations.

Use `hrk D hD` as an intermediate fact. Simplify using `only at hDE`. Rewrite `this` using `[hDE]`. Use linear arithmetic over natural numbers and integers. Introduce `D hD`.

Both sides reduce to the same expression.
-/
private theorem partIn (hIn : CountIn) {k H P : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j + 1).filter
        (fun D => C ≤ D), g (D.map C.mkQ)
      = ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨hbij, hrk, -⟩ := hIn k H C hC
  refine Finset.sum_bij (fun D _ => D.map C.mkQ) ?_ ?_ ?_ ?_
  · intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    have := hrk D hD.2
    omega
  · intro D₁ h₁ D₂ h₂ he
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at h₁ h₂
    exact Subtype.ext_iff.mp (@hbij.1 ⟨D₁, h₁.2⟩ ⟨D₂, h₂.2⟩ he)
  · intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    obtain ⟨⟨D, hD⟩, hDE⟩ := hbij.2 E
    refine ⟨D, ?_, hDE⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨?_, hD⟩
    have := hrk D hD
    simp only at hDE
    rw [hDE] at this
    omega
  · intro D hD
    rfl

open Classical in
/- English proof (translation)
Use extensionality with `D`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]`. Introduce `hD hCD`. Use `Submodule.finrank_mono hCD` as an intermediate fact. Use linear arithmetic over natural numbers and integers.
-/
private theorem partZero (hIn : CountIn) {k H : Type} [Field k] [AddCommGroup H] [Module k H]
    [Module.Finite k H] (C : Submodule k H) (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] :
    (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = 0).filter
        (fun D => C ≤ D) = ∅ := by
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.notMem_empty, iff_false, not_and]
  intro hD hCD
  have := Submodule.finrank_mono hCD
  omega

open Classical in
/- English proof (translation)
Take `⟨-, -, hrk⟩` from `hIn k H C hC`. Establish `hmaps : ∀ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter (fun D => ¬ C ≤ D), D.map C.mkQ ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j)`. Introduce `D hD`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢`. Rewrite using `[← hrk D hD.2]`.

Conclude with `hD.1`. Rewrite using `[Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations. Introduce `E hE`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hE`.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => g E) (fun D hD => by rw [(Finset.mem_filter.mp hD).2])]`. Rewrite using `[Finset.sum_const]`. Use `congr 1`. Establish `hc : Nat.card k ^ j = Nat.card { D // ¬C ≤ D ∧ Submodule.map C.mkQ D = E }`. Rewrite using `[hOut k H C hC E, hE]`.

Rewrite using `[hc, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 1`. Use extensionality with `D`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨-, h2⟩, h3⟩`. Conclude with `⟨h2, h3⟩`. Introduce and unpack `⟨h2, h3⟩`. Use `⟨⟨?_, h2⟩, h3⟩` and prove the remaining obligations. Rewrite using `[hrk D h2, h3, hE]`.
-/
private theorem partOut (hIn : CountIn) (hOut : CountOut) {k H P : Type} [Field k] [Finite k]
    [AddCommGroup H] [Module k H] [Module.Finite k H] (C : Submodule k H)
    (hC : Module.finrank k C = 1)
    [Fintype (Submodule k H)] [Fintype (Submodule k (H ⧸ C))]
    (g : Submodule k (H ⧸ C) → Multiset P) (j : ℕ) :
    ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
        (fun D => ¬ C ≤ D), g (D.map C.mkQ)
      = Nat.card k ^ j •
        ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), g E := by
  obtain ⟨-, -, hrk⟩ := hIn k H C hC
  have hmaps : ∀ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = j).filter
      (fun D => ¬ C ≤ D), D.map C.mkQ ∈
        Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j) := by
    intro D hD
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hD ⊢
    rw [← hrk D hD.2]
    exact hD.1
  rw [Finset.smul_sum, ← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_congr rfl ?_
  intro E hE
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
  rw [Finset.sum_congr rfl (g := fun _ => g E) (fun D hD => by rw [(Finset.mem_filter.mp hD).2])]
  rw [Finset.sum_const]
  congr 1
  have hc : Nat.card k ^ j = Nat.card { D // ¬C ≤ D ∧ Submodule.map C.mkQ D = E } := by
    rw [hOut k H C hC E, hE]
  rw [hc, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 1
  ext D
  simp only [Finset.mem_filter, Finset.mem_univ, true_and]
  constructor
  · rintro ⟨⟨-, h2⟩, h3⟩
    exact ⟨h2, h3⟩
  · rintro ⟨h2, h3⟩
    refine ⟨⟨?_, h2⟩, h3⟩
    rw [hrk D h2, h3, hE]

end UpperTheory.Gal.crystallineComparison

/- English proof (translation)
Introduce `hIn hOut q n P F I _ v hv`. Take `⟨k, H, _, _, _, _, _, C, A', e, hq, hn, hC, hve⟩` from `hv`. Use `haveI : Finite H := Module.finite_of_finite k`. Use `haveI : Finite (Submodule k H) := Finite.of_injective (fun S : Submodule k H => (S : Set H)) SetLike.coe_injective`. Use `haveI : Finite (H ⧸ C) := Module.finite_of_finite k`.

Use `haveI : Finite (Submodule k (H ⧸ C)) := Finite.of_injective (fun S : Submodule k (H ⧸ C) => (S : Set (H ⧸ C))) SetLike.coe_injective`. Use `letI : Fintype (Submodule k H) := Fintype.ofFinite _`. Use `letI : Fintype (Submodule k (H ⧸ C)) := Fintype.ofFinite _`. Use `letI hG : ∀ m : ℕ, Fintype (Gr k H m) := fun m => (inferInstance : Fintype {D : Submodule k H // Module.finrank k D = m})`. Establish `key : ∀ j : Fin (n + 1), Multiset.map (v j) Finset.univ.val = ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter (fun D => C ≤ D), ({F (A' (D.map C.mkQ))} : Multiset P) + ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = …`.

Introduce `j`. Rewrite using `[← Finset.sum_ite]`. Rewrite using `[val_map_sum, ← Equiv.sum_comp (e j).symm]`. Rewrite using `[Finset.sum_subtype (F := hG j) (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (p := fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (by simp)]`. Use `Finset.sum_congr rfl ?_` and prove the remaining obligations.

Introduce `D _`. Establish `h` using `hve j ((e j).symm D)`. Rewrite `h` using `[Equiv.apply_symm_apply]`. Distinguish the cases in `hCD : C ≤ D.1`. Rewrite using `[h.1 hCD]`.

Simplify using `[hCD]`. Rewrite using `[h.2 hCD]`. Simplify using `[hCD]`. Use `⟨fun j => ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), ({A' E} : Multiset P), ?_, ?_, ?_⟩` and prove the remaining obligations. Apply `Finset.sum_eq_zero` to reduce the goal to its premises.

Introduce `E hE`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hE`. It suffices to derive a contradiction. Establish `h1` using `Submodule.finrank_le E`. Establish `h2` using `Submodule.finrank_quotient_add_finrank C`.

Use linear arithmetic over natural numbers and integers. Rewrite using `[key 0]`. Simplify using `only [Fin.val_zero]`. Establish `h0` using `partZero hIn C hC`. Establish `h1` using `partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) 0`.

Simplify using `only [pow_zero, one_smul] at h1`. Use `congrArg₂ (· + ·) (congrArg (fun s => ∑ D ∈ s, ({F (A' (D.map C.mkQ))} : Multiset P)) h0) h1` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp`.

Consider the case `(ext x; simp)`. Introduce `j`. Rewrite using `[key j.succ]`. Simplify using `only [Fin.val_succ]`. Establish `h2` using `partIn hIn C hC (fun E => ({F (A' E)} : Multiset P)) j`.

Establish `h3` using `partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) (j + 1)`. Rewrite `h3` using `[hq]`. Establish `h4 : ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), ({F (A' E)} : Multiset P) = Multiset.map F (∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j), ({A' E} : Multiset P))`. Rewrite using `[← val_map_sum, ← val_map_sum, Multiset.map_map]`. Both sides reduce to the same expression.

Rewrite using `[← h4]`. Use `congrArg₂ (· + ·) h2 h3` and compare the differences between its conclusion and the goal. Apply the tactic sequence `all_goals first`. Consider the case `rfl`. Consider the case `simp`.

Consider the case `(ext x; simp)`.
-/
theorem UpperTheory.Gal.crystallineComparison.ordDecomp_of :
    CountIn → CountOut → OrdDecomp := by
  intro hIn hOut q n P F I _ v hv
  obtain ⟨k, H, _, _, _, _, _, C, A', e, hq, hn, hC, hve⟩ := hv
  classical
  haveI : Finite H := Module.finite_of_finite k
  haveI : Finite (Submodule k H) :=
    Finite.of_injective (fun S : Submodule k H => (S : Set H)) SetLike.coe_injective
  haveI : Finite (H ⧸ C) := Module.finite_of_finite k
  haveI : Finite (Submodule k (H ⧸ C)) :=
    Finite.of_injective (fun S : Submodule k (H ⧸ C) => (S : Set (H ⧸ C))) SetLike.coe_injective
  letI : Fintype (Submodule k H) := Fintype.ofFinite _
  letI : Fintype (Submodule k (H ⧸ C)) := Fintype.ofFinite _
  letI hG : ∀ m : ℕ, Fintype (Gr k H m) := fun m =>
    (inferInstance : Fintype {D : Submodule k H // Module.finrank k D = m})
  have key : ∀ j : Fin (n + 1), Multiset.map (v j) Finset.univ.val =
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => C ≤ D), ({F (A' (D.map C.mkQ))} : Multiset P) +
      ∑ D ∈ (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ)).filter
        (fun D => ¬ C ≤ D), ({A' (D.map C.mkQ)} : Multiset P) := by
    intro j
    rw [← Finset.sum_ite]
    rw [val_map_sum, ← Equiv.sum_comp (e j).symm]
    rw [Finset.sum_subtype (F := hG j)
      (Finset.univ.filter fun D : Submodule k H => Module.finrank k D = (j : ℕ))
      (p := fun D : Submodule k H => Module.finrank k D = (j : ℕ)) (by simp)]
    refine Finset.sum_congr rfl ?_
    intro D _
    have h := hve j ((e j).symm D)
    rw [Equiv.apply_symm_apply] at h
    by_cases hCD : C ≤ D.1
    · rw [h.1 hCD]
      simp [hCD]
    · rw [h.2 hCD]
      simp [hCD]
  refine ⟨fun j => ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
    ({A' E} : Multiset P), ?_, ?_, ?_⟩
  · apply Finset.sum_eq_zero
    intro E hE
    simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hE
    exfalso
    have h1 := Submodule.finrank_le E
    have h2 := Submodule.finrank_quotient_add_finrank C
    omega
  · rw [key 0]
    simp only [Fin.val_zero]
    have h0 := partZero hIn C hC
    have h1 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) 0
    simp only [pow_zero, one_smul] at h1
    convert congrArg₂ (· + ·) (congrArg (fun s => ∑ D ∈ s, ({F (A' (D.map C.mkQ))} : Multiset P)) h0) h1
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
  · intro j
    rw [key j.succ]
    simp only [Fin.val_succ]
    have h2 := partIn hIn C hC (fun E => ({F (A' E)} : Multiset P)) j
    have h3 := partOut hIn hOut C hC (fun E => ({A' E} : Multiset P)) (j + 1)
    rw [hq] at h3
    have h4 : ∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
        ({F (A' E)} : Multiset P) = Multiset.map F
          (∑ E ∈ Finset.univ.filter (fun E : Submodule k (H ⧸ C) => Module.finrank k E = j),
            ({A' E} : Multiset P)) := by
      rw [← val_map_sum, ← val_map_sum, Multiset.map_map]
      rfl
    rw [← h4]
    convert congrArg₂ (· + ·) h2 h3
    all_goals first
      | rfl
      | simp
      | (ext x; simp)
