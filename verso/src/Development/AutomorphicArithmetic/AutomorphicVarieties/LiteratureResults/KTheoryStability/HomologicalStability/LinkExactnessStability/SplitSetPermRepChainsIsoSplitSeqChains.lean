import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.MemSplitSeqIff
import Development.AutomorphicArithmetic.AutomorphicVarieties.PublishedTheorems.KAcyclicHomology

open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL

namespace GlobalTheory.HomStab

/- English proof (translation)
Apply `Finsupp.lhom_ext` to reduce the goal to its premises. Introduce `l a`. Establish `hlen : l.1.length = p + 1` using `l.2.2`. Simplify using `only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul, Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]`. Unfold `bd`.

Rewrite using `[Finsupp.linearCombination_single, hlen, Finset.smul_sum]`. Rewrite using `[← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a = a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))`. Simplify using `[Finsupp.smul_single, mul_comm]`.
-/
private theorem split_set_boundary_comp_face_sum (R : Type) [CommRing R] (n p : ℕ) :
    (Finsupp.lmapDomain ℤ ℤ (fun x : SplitSet R n p => (x.1 : List ((Fin n → R) × (Fin n → R))))) ∘ₗ
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.lmapDomain ℤ ℤ (face R n p i)) =
    bd _ ∘ₗ Finsupp.lmapDomain ℤ ℤ
      (fun x : SplitSet R n (p + 1) => (x.1 : List ((Fin n → R) × (Fin n → R)))) := by
  apply Finsupp.lhom_ext
  intro l a
  have hlen : l.1.length = p + 1 := l.2.2
  simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, map_sum, map_zsmul,
    Finsupp.lmapDomain_apply, Finsupp.mapDomain_single]
  unfold bd
  rw [Finsupp.linearCombination_single, hlen, Finset.smul_sum]
  rw [← Fin.sum_univ_eq_sum_range (fun i => a • ((-1 : ℤ) ^ i • Finsupp.single (l.1.eraseIdx i) (1 : ℤ)))]
  refine Finset.sum_congr rfl fun i _ => ?_
  show (-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) a =
    a • ((-1 : ℤ) ^ (i : ℕ) • Finsupp.single (l.1.eraseIdx i) (1 : ℤ))
  simp [Finsupp.smul_single, mul_comm]

/- English proof (translation)
Introduce `R _ n p`. Establish `hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c = (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ)`. Introduce `c`. Simplify using `[splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom, Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations.

Conclude with `Finsupp.mapDomain_injective Subtype.val_injective`. Rewrite using `[LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]`. Unfold `chains`. Use `congr 1`. Use extensionality with `l`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨x, rfl⟩`. Conclude with `x.2`. Introduce `hl`. Conclude with `⟨⟨l, hl⟩, rfl⟩`.

Introduce `c`. Rewrite using `[hD]`. Establish `key` using `LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c`. Simplify using `only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply, Finsupp.lmapDomain_apply] at key`. Conclude with `key`.
-/
theorem splitSet_chains_incl : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  intro R _ n p
  have hD : ∀ c : SplitSet R n (p + 1) →₀ ℤ, (splitD R n p).hom c =
      (∑ i : Fin (p + 1), (-1 : ℤ) ^ (i : ℕ) • Finsupp.mapDomain (face R n p i) c : SplitSet R n p →₀ ℤ) := by
    intro c
    simp [splitD, permMap, Rep.sum_hom, Rep.hom_ofHom, Rep.zsmul_hom, Rep.smul_hom,
      Representation.IntertwiningMap.sum_apply, Representation.IntertwiningMap.smul_apply]
  refine ⟨?_, ?_, ?_⟩
  · exact Finsupp.mapDomain_injective Subtype.val_injective
  · rw [LinearMap.range_eq_map, ← Finsupp.supported_univ, Finsupp.lmapDomain_supported, Set.image_univ]
    unfold chains
    congr 1
    ext l
    constructor
    · rintro ⟨x, rfl⟩
      exact x.2
    · intro hl
      exact ⟨⟨l, hl⟩, rfl⟩
  · intro c
    rw [hD]
    have key := LinearMap.congr_fun (split_set_boundary_comp_face_sum R n p) c
    simp only [LinearMap.comp_apply, LinearMap.sum_apply, LinearMap.smul_apply,
      Finsupp.lmapDomain_apply] at key
    exact key

end GlobalTheory.HomStab

section
open CategoryTheory CategoryTheory.Limits GlobalTheory.HomStab GlobalTheory.SeqCx UpperTheory.V.KL
/- English proof (translation)
Use `first`. Consider the case `exact @GlobalTheory.HomStab.splitSet_chains_incl`.
-/
theorem _root_.GlobalTheory.T.splitSet_permRep_chains_iso_splitSeq_chains : ∀ (R : Type) [CommRing R] (n p : ℕ), Function.Injective (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) ∧ LinearMap.range (Finsupp.lmapDomain ℤ ℤ (Subtype.val : SplitSet R n p → _)) = chains (splitSeq R n) p ∧ ∀ c : SplitSet R n (p + 1) →₀ ℤ, Finsupp.mapDomain (Subtype.val : SplitSet R n p → _) ((splitD R n p).hom c) = bd _ (Finsupp.mapDomain (Subtype.val : SplitSet R n (p + 1) → _) c) := by
  first
  | exact @GlobalTheory.HomStab.splitSet_chains_incl
end
