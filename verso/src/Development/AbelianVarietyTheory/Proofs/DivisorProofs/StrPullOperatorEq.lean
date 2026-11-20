import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false
namespace GlobalTheory.TorsionForm.OneVec.StrPull

/- English proof (translation)
Simplify using `only [join, Finset.mem_union, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, ha, h⟩ | ⟨a, ha, h⟩)`. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`.

Rewrite using `[← Fin.ext h']` and apply the resulting hypothesis. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Use linear arithmetic over natural numbers and integers. Introduce `h`.

Conclude with `Or.inl ⟨i, h, rfl⟩`.
-/
theorem mem_join_castAdd {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) (i : Fin m) :
    Fin.castAdd g i ∈ join S I ↔ i ∈ S := by
  simp only [join, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · have h' := congrArg Fin.val h
      simp at h'
      rwa [← Fin.ext h']
    · have h' := congrArg Fin.val h
      simp at h'
      omega
  · intro h; exact Or.inl ⟨i, h, rfl⟩

/- English proof (translation)
Simplify using `only [join, Finset.mem_union, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨a, ha, h⟩ | ⟨a, ha, h⟩)`. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`.

Use linear arithmetic over natural numbers and integers. Establish `h'` using `congrArg Fin.val h`. Simplify using `at h'`. Rewrite using `[← Fin.ext h']` and apply the resulting hypothesis. Introduce `h`.

Conclude with `Or.inr ⟨c, h, rfl⟩`.
-/
theorem mem_join_natAdd {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) (c : Fin g) :
    Fin.natAdd m c ∈ join S I ↔ c ∈ I := by
  simp only [join, Finset.mem_union, Finset.mem_map]
  constructor
  · rintro (⟨a, ha, h⟩ | ⟨a, ha, h⟩)
    · have h' := congrArg Fin.val h
      simp at h'
      omega
    · have h' := congrArg Fin.val h
      simp at h'
      rwa [← Fin.ext h']
  · intro h; exact Or.inr ⟨c, h, rfl⟩

/- English proof (translation)
Use extensionality with `i`. Simplify using `[basePart, mem_join_castAdd]`.
-/
theorem basePart_join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) :
    basePart (join S I) = S := by
  ext i; simp [basePart, mem_join_castAdd]

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fibrePart, mem_join_natAdd]`.
-/
theorem fibrePart_join {m g : ℕ} (S : Finset (Fin m)) (I : Finset (Fin g)) :
    fibrePart (join S I) = I := by
  ext i; simp [fibrePart, mem_join_natAdd]

/- English proof (translation)
Use extensionality with `x`. Use `Fin.addCases (fun i => ?_) (fun c => ?_) x` and prove the remaining obligations. Simplify using `[basePart, mem_join_castAdd]`. Simplify using `[fibrePart, mem_join_natAdd]`.
-/
theorem join_parts {m g : ℕ} (U : Finset (Fin (m + g))) :
    join (basePart U) (fibrePart U) = U := by
  ext x
  refine Fin.addCases (fun i => ?_) (fun c => ?_) x
  · simp [basePart, mem_join_castAdd]
  · simp [fibrePart, mem_join_natAdd]

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← basePart_join S I, h, basePart_join]`. Rewrite using `[← fibrePart_join S I, h, fibrePart_join]`.
-/
theorem join_inj {m g : ℕ} {S S' : Finset (Fin m)} {I I' : Finset (Fin g)}
    (h : join S I = join S' I') : S = S' ∧ I = I' := by
  refine ⟨?_, ?_⟩
  · rw [← basePart_join S I, h, basePart_join]
  · rw [← fibrePart_join S I, h, fibrePart_join]

/- English proof (translation)
Use function extensionality and compare the values at `U`. Express the relevant statement in the definitionally equal form `(if basePart U = ∅ then (Pi.single (join ∅ I) 1 : Ext (1 + 1 + g)) (join S' (fibrePart U)) else 0) = _`. Distinguish the cases in `hS : S' = ∅`. Substitute `hS` using the available equality. Simplify using `only [if_true, Pi.single_apply]`.

Distinguish the cases in `hU : U = join ∅ I`. Substitute `hU` using the available equality. Simplify using `[basePart_join, fibrePart_join]`. Rewrite using `[if_neg hU] split_ifs with hb hj`. Establish `hf` using `(join_inj hj).2`.

Conclude with `absurd ((join_parts U).symm.trans (by rw [hb, hf])) hU`. Both sides reduce to the same expression. Both sides reduce to the same expression. Rewrite using `[if_neg hS]`. Simplify using `only [Pi.single_apply]`.

Use `split_ifs with hb hj`. Conclude with `absurd (join_inj hj).1 hS`. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
theorem rhoL_single {n g : ℕ} (S' : Finset (Fin (1 + 1))) (I : Finset (Fin g)) :
    rhoL (n := n) S' (Pi.single (join ∅ I) 1) =
      if S' = ∅ then Pi.single (join ∅ I) 1 else 0 := by
  funext U
  change (if basePart U = ∅ then (Pi.single (join ∅ I) 1 : Ext (1 + 1 + g)) (join S' (fibrePart U))
    else 0) = _
  by_cases hS : S' = ∅
  · subst hS
    simp only [if_true, Pi.single_apply]
    by_cases hU : U = join ∅ I
    · subst hU; simp [basePart_join, fibrePart_join]
    · rw [if_neg hU]
      split_ifs with hb hj
      · have hf := (join_inj hj).2
        exact absurd ((join_parts U).symm.trans (by rw [hb, hf])) hU
      · rfl
      · rfl
  · rw [if_neg hS]
    simp only [Pi.single_apply]
    split_ifs with hb hj
    · exact absurd (join_inj hj).1 hS
    · rfl
    · rfl

/- English proof (translation)
Rewrite using `[pullOp, ContinuousLinearMap.sum_apply, Finset.sum_eq_single (∅ : Finset (Fin (1 + 1)))]`. Simplify using `only [ContinuousLinearMap.comp_apply, rhoL_single, if_true]`. Simplify using `[lamL]`. Both sides reduce to the same expression. Introduce `S _ hS`.

Simplify using `[ContinuousLinearMap.comp_apply, rhoL_single, hS]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem pullOp_single {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g))
    (I : Finset (Fin g)) :
    pullOp a K (Pi.single (join ∅ I) 1) = pullFull a (K (Pi.single (join ∅ I) 1)) := by
  rw [pullOp, ContinuousLinearMap.sum_apply, Finset.sum_eq_single (∅ : Finset (Fin (1 + 1)))]
  · simp only [ContinuousLinearMap.comp_apply, rhoL_single, if_true]
    simp [lamL]
    rfl
  · intro S _ hS
    simp [ContinuousLinearMap.comp_apply, rhoL_single, hS]
  · intro h; exact absurd (Finset.mem_univ _) h

/- English proof (translation)
Simplify using `[pullFull, basePart_join, fibrePart_join]`.
-/
theorem pullFull_join {n g : ℕ} (a : Fin n → ℂ) (y : Ext (n + n + g)) (S : Finset (Fin (1 + 1)))
    (I : Finset (Fin g)) :
    pullFull a y (join S I) = pullBase a (fun S' => y (join S' I)) S := by
  simp [pullFull, basePart_join, fibrePart_join]

end GlobalTheory.TorsionForm.OneVec.StrPull

namespace GlobalTheory.TorsionForm.OneVec

open GlobalTheory.TorsionForm.OneVec.StrPull in

/- English proof (translation)
Establish `h : strN K = ∑ I : Finset (Fin g), ((-1) ^ I.card * (I.card : ℂ)) • (fun S' : Finset (Fin (n + n)) => K (Pi.single (join ∅ I) 1) (join S' I))`. Use function extensionality and compare the values at `S'`. Simplify using `[strN, Finset.sum_apply, smul_eq_mul]`. Rewrite using `[h, map_sum]`. Use function extensionality and compare the values at `S`.

Rewrite using `[Finset.sum_apply]`. Simplify using `only [strN, pullOp_single, pullFull_join, map_smul, Pi.smul_apply, smul_eq_mul]`. Both sides reduce to the same expression.
-/
theorem strN_pullOp {n g : ℕ} (a : Fin n → ℂ) (K : Ext (n + n + g) →L[ℂ] Ext (n + n + g)) :
    strN (pullOp a K) = pullBaseL a (strN K) := by
  have h : strN K = ∑ I : Finset (Fin g), ((-1) ^ I.card * (I.card : ℂ)) •
      (fun S' : Finset (Fin (n + n)) => K (Pi.single (join ∅ I) 1) (join S' I)) := by
    funext S'
    simp [strN, Finset.sum_apply, smul_eq_mul]
  rw [h, map_sum]
  funext S
  rw [Finset.sum_apply]
  simp only [strN, pullOp_single, pullFull_join, map_smul, Pi.smul_apply, smul_eq_mul]
  rfl

end GlobalTheory.TorsionForm.OneVec
