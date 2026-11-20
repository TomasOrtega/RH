import Development.WeilBound.RepresentationTheoryGL.UnitaryDualProof.TwistedPieces.IntegralParts.LocallyConstantCosets.PsiBiUnion

noncomputable section

open Matrix GroundTheory.Automorphic.Whittaker GlobalTheory.SplitWeil
open scoped Pointwise

namespace PositivityTheory.RgUd.TP.Nil.Fib2

open PositivityTheory.RgUd.T PositivityTheory.RgUd.T.Nil PositivityTheory.RgUd.TP PositivityTheory.RgUd.TP.Nil PositivityTheory.RgUd.TP.Nil.Fib1

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] {n : ℕ}
  {Z : Subalgebra k (Matrix (Fin n) (Fin n) k)}

/- English proof (translation)
Establish `hfi : (M.addSubgroupOf L).FiniteIndex` using `⟨lat_index_pos hL hM hML⟩`. Use `haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _`. Set `f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k` to `fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)`. Establish `hf : Function.Injective f` using `fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)`. Establish `hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M`.

Introduce `z q`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨m, hm, rfl⟩`. Simplify using `using hm`. Introduce `hz`.

Conclude with `⟨z - f q, hz, by simp⟩`. Establish `key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z = ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z`. Introduce `z`. Rewrite using `[Finset.sum_image (fun a _ b _ hab => hf hab)]`. Distinguish the cases in `hz : z ∈ L`.

Rewrite using `[Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]`. Establish `hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z = if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0`. Introduce `q`. Establish `e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = QuotientAddGroup.mk (Quotient.out q)`. Rewrite using `[QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]`.

Use `show z - f q ∈ M ↔ -z + f q ∈ M`. Rewrite using `[show -z + f q = -(z - f q) by abel, neg_mem_iff]`. Rewrite `e` using `[QuotientAddGroup.out_eq']`. Distinguish the cases in `h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q`. Rewrite using `[if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]`.

Both sides reduce to the same expression. Rewrite using `[if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]`. Simplify using `only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Both sides reduce to the same expression. Rewrite using `[Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]`.

Use `symm`. Apply `Finset.sum_eq_zero` to reduce the goal to its premises. Introduce `q _`. Apply `Set.indicator_of_notMem` to reduce the goal to its premises. Introduce `h'`.

Apply `hz` to reduce the goal to its premises. Establish `h2 : z = (z - f q) + f q` using `by abel`. Rewrite using `[h2]`. Conclude with `L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2`. Use `⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Introduce `d hd`. Take `⟨q, _, rfl⟩` from `Finset.mem_image.1 hd`. Conclude with `(Quotient.out q).2`.

Rewrite using `[Finset.sum_apply]`. Distinguish the cases in `hp : p.1 ∈ CC Z`. Simplify using `only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]`. Rewrite using `[key, Finset.sum_mul]`. Simplify using `only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]`.
-/
theorem psi_cosets {L M : AddSubgroup (Matrix (Fin n) (Fin n) k)} (hL : IsLat Z L) (hM : IsLat Z M) (hML : M ≤ L) :
    ∃ D : Finset (Matrix (Fin n) (Fin n) k), D.card = M.relIndex L ∧ (∀ d ∈ D, d ∈ L) ∧
      ∀ h : Sp k n → ℂ, psi Z (L : Set (Matrix (Fin n) (Fin n) k)) h =
        ∑ d ∈ D, psi Z ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))) h := by
  classical
  have hfi : (M.addSubgroupOf L).FiniteIndex := ⟨lat_index_pos hL hM hML⟩
  haveI : Fintype (L ⧸ M.addSubgroupOf L) := Fintype.ofFinite _
  let f : (L ⧸ M.addSubgroupOf L) → Matrix (Fin n) (Fin n) k := fun q => ((Quotient.out q : L) : Matrix (Fin n) (Fin n) k)
  have hf : Function.Injective f := fun a b hab => Quotient.out_inj.1 (Subtype.ext hab)
  have hmem : ∀ z q, z ∈ (fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k)) ↔ z - f q ∈ M := by
    intro z q
    constructor
    · rintro ⟨m, hm, rfl⟩
      simpa using hm
    · intro hz
      exact ⟨z - f q, hz, by simp⟩
  have key : ∀ z, (L : Set (Matrix (Fin n) (Fin n) k)).indicator (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
      ∑ d ∈ Finset.univ.image f, ((fun a => a + d) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator 1 z := by
    intro z
    rw [Finset.sum_image (fun a _ b _ hab => hf hab)]
    by_cases hz : z ∈ L
    · rw [Set.indicator_of_mem (show z ∈ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      have hq : ∀ q, ((fun a => a + f q) '' (M : Set (Matrix (Fin n) (Fin n) k))).indicator
          (1 : Matrix (Fin n) (Fin n) k → ℂ) z =
          if (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q then 1 else 0 := by
        intro q
        have e : z - f q ∈ M ↔ (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) =
            QuotientAddGroup.mk (Quotient.out q) := by
          rw [QuotientAddGroup.eq, AddSubgroup.mem_addSubgroupOf]
          show z - f q ∈ M ↔ -z + f q ∈ M
          rw [show -z + f q = -(z - f q) by abel, neg_mem_iff]
        rw [QuotientAddGroup.out_eq'] at e
        by_cases h : (QuotientAddGroup.mk ⟨z, hz⟩ : L ⧸ M.addSubgroupOf L) = q
        · rw [if_pos h, Set.indicator_of_mem ((hmem z q).2 (e.2 h))]
          rfl
        · rw [if_neg h, Set.indicator_of_notMem (fun h' => h (e.1 ((hmem z q).1 h')))]
      simp only [hq, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rfl
    · rw [Set.indicator_of_notMem (show z ∉ (L : Set (Matrix (Fin n) (Fin n) k)) from hz)]
      symm
      apply Finset.sum_eq_zero
      intro q _
      apply Set.indicator_of_notMem
      intro h'
      apply hz
      have h2 : z = (z - f q) + f q := by abel
      rw [h2]
      exact L.add_mem (hML ((hmem z q).1 h')) (Quotient.out q).2
  refine ⟨Finset.univ.image f, ?_, ?_, fun h => funext fun p => ?_⟩
  · rw [Finset.card_image_of_injective _ hf, Finset.card_univ, ← Nat.card_eq_fintype_card]
    rfl
  · intro d hd
    obtain ⟨q, _, rfl⟩ := Finset.mem_image.1 hd
    exact (Quotient.out q).2
  · rw [Finset.sum_apply]
    by_cases hp : p.1 ∈ CC Z
    · simp only [psi, Set.indicator_of_mem (show p ∈ {q : Sp k n | q.1 ∈ CC Z} from hp)]
      rw [key, Finset.sum_mul]
    · simp only [psi, Set.indicator_of_notMem (show p ∉ {q : Sp k n | q.1 ∈ CC Z} from hp), Finset.sum_const_zero]

end PositivityTheory.RgUd.TP.Nil.Fib2

end
