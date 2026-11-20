import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.GrothendieckRingPolynomial.ProdList
import Development.WeilBound.CoreStatements.TemperedRepresentationTheory.BernsteinZelevinskyGL.TopAdm
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.LanglandsRepOrderedWordOccursStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SegmentProductWordInShuffleStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WordOccursOfSubquotientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedWordLettersCuspidalStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.OrderedFormsMutualShuffleEqStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShuffleWeightSquareLengthLtStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ShufflePermFlattenStatement

noncomputable section

open GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.JHMult Zc Zc.M

set_option synthInstance.maxHeartbeats 400000

namespace PositivityTheory.Groth

section TriLemmas

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Unfold `decW Segment.ms`. Rewrite using `[← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]`.
-/
theorem tri_coe_decW (Δ : Segment k) : ((decW Δ : List (IrrGL k)) : Multiset (IrrGL k)) = Δ.ms := by
  unfold decW Segment.ms
  rw [← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]

/- English proof (translation)
Proceed by induction on `L with`. Consider the case `nil => simp`. Consider the case `cons a L ih`. Rewrite using `[List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe, Multiset.cons_bind]`.
-/
theorem tri_coe_flatten_decW (L : List (Segment k)) :
    (((L.map decW).flatten : List (IrrGL k)) : Multiset (IrrGL k)) = (L : Multiset (Segment k)).bind Segment.ms := by
  induction L with
  | nil => simp
  | cons a L ih =>
    rw [List.map_cons, List.flatten_cons, ← Multiset.coe_add, ih, tri_coe_decW, ← Multiset.cons_coe,
      Multiset.cons_bind]

/- English proof (translation)
Take `⟨L, rfl, hs⟩` from `H`. Unfold `msupp`. Rewrite using `[← tri_coe_flatten_decW]`. Conclude with `Multiset.coe_eq_coe.mpr (GlobalTheory.T.perm_flatten_of_shuffle _ _ hs).symm`.
-/
theorem tri_msupp_of_inShW {𝔪 : Multiset (Segment k)} {w : List (IrrGL k)} (H : InShW 𝔪 w) :
    msupp 𝔪 = (w : Multiset (IrrGL k)) := by
  obtain ⟨L, rfl, hs⟩ := H
  unfold msupp
  rw [← tri_coe_flatten_decW]
  exact Multiset.coe_eq_coe.mpr (GlobalTheory.T.perm_flatten_of_shuffle _ _ hs).symm

/- English proof (translation)
Take `⟨h1, _⟩` from `H`. Unfold `wtW msupp`. Rewrite using `[← h1]`. Establish `e1 : (List.ofFn fun i => decW (Γ i.rev)) = (List.ofFn fun i => Γ i.rev).map decW`. Rewrite using `[List.map_ofFn]`.

Both sides reduce to the same expression. Rewrite using `[e1, tri_coe_flatten_decW, ← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]`.
-/
theorem tri_msupp_wtW {h : ℕ} {Γ : Fin h → Segment k} {𝔫 : Multiset (Segment k)} (H : IsOrderedForm Γ 𝔫) :
    msupp 𝔫 = (wtW Γ : Multiset (IrrGL k)) := by
  obtain ⟨h1, _⟩ := H
  unfold wtW msupp
  rw [← h1]
  have e1 : (List.ofFn fun i => decW (Γ i.rev)) = (List.ofFn fun i => Γ i.rev).map decW := by
    rw [List.map_ofFn]
    rfl
  rw [e1, tri_coe_flatten_decW, ← GlobalTheory.CompanionTheory.ZcWords.reverse_ofFn, Multiset.coe_reverse, Fin.univ_val_map]

/- English proof (translation)
Rewrite using `[Comb.sqLen, Multiset.map_map]`. Both sides reduce to the same expression.
-/
theorem tri_sqLen_map_toA (𝔪 : Multiset (Segment k)) : Comb.sqLen (𝔪.map toA) = sq 𝔪 := by
  rw [Comb.sqLen, Multiset.map_map]
  rfl

end TriLemmas

/- English proof (translation)
Introduce `𝔪 𝔫 h x y hd hL hy hj`. Take `⟨Δ, hΔ, hx⟩` from `hL`. Take `⟨h', x', hd', ⟨Γ, hΓ, _⟩, _⟩` from `id hy`. Establish `hadm` using `PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top`. Establish `hw : Wd y.rep (wtW Γ)` using `GlobalTheory.T.langlands_rep_ordered_word_occurs hadm c.soc c.jac 𝔫 y.rep hy h' Γ hΓ`.

Establish `hsub : IsSubquotient y.rep (prodIrr x hd)` using `jhMult_ne_zero_iff.mp hj`. Establish `hw2 : Wd (prodIrr x hd) (wtW Γ)` using `GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hsub _ hw`. Establish `hsh : InShW (Multiset.map Δ Finset.univ.val) (wtW Γ)` using `GlobalTheory.T.segment_product_word_in_shuffle hadm c.jac x hd Δ hx _ (GlobalTheory.T.ordered_word_letters_cuspidal Γ) hw2`. Rewrite `hsh` using `[hΔ.1]`. Use `⟨(tri_msupp_of_inShW hsh).trans (tri_msupp_wtW hΓ).symm, ?_⟩` and prove the remaining obligations.

Distinguish the cases in `heq : 𝔪 = 𝔫`. Conclude with `Or.inl heq`. Use `right`. Establish `hne : Multiset.map toA 𝔪 ≠ ↑(List.map toA (List.ofFn Γ))`. Rewrite using `[GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ]`.

Conclude with `fun e => heq (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)`. Establish `hlt` using `GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic (List.map toA (List.ofFn Γ)) (Multiset.map toA 𝔪) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ) (GlobalTh …`. Rewrite `hlt` using `[GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ, tri_sqLen_map_toA, tri_sqLen_map_toA]`. Conclude with `hlt`.
-/
theorem tri (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (c : Cls k) :
    Tri k := by
  intro 𝔪 𝔫 h x y hd hL hy hj
  obtain ⟨Δ, hΔ, hx⟩ := hL
  obtain ⟨h', x', hd', ⟨Γ, hΓ, _⟩, _⟩ := id hy
  have hadm := PositivityTheory.Tls2.BZGL.irreducibleAdmissibleGL_top
  have hw : Wd y.rep (wtW Γ) := GlobalTheory.T.langlands_rep_ordered_word_occurs hadm c.soc c.jac 𝔫 y.rep hy h' Γ hΓ
  have hsub : IsSubquotient y.rep (prodIrr x hd) := jhMult_ne_zero_iff.mp hj
  have hw2 : Wd (prodIrr x hd) (wtW Γ) := GlobalTheory.T.word_occurs_of_subquotient _ _ (isSmooth_prodIrr x hd) hsub _ hw
  have hsh : InShW (Multiset.map Δ Finset.univ.val) (wtW Γ) :=
    GlobalTheory.T.segment_product_word_in_shuffle hadm c.jac x hd Δ hx _ (GlobalTheory.T.ordered_word_letters_cuspidal Γ) hw2
  rw [hΔ.1] at hsh
  refine ⟨(tri_msupp_of_inShW hsh).trans (tri_msupp_wtW hΓ).symm, ?_⟩
  by_cases heq : 𝔪 = 𝔫
  · exact Or.inl heq
  · right
    have hne : Multiset.map toA 𝔪 ≠ ↑(List.map toA (List.ofFn Γ)) := by
      rw [GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ]
      exact fun e => heq (Multiset.map_injective GlobalTheory.CompanionTheory.ZcWords.toA_injective e)
    have hlt := GlobalTheory.T.shuffle_weight_square_length_lt sNu GlobalTheory.CompanionTheory.ZcWords.sNu_injective GlobalTheory.CompanionTheory.ZcWords.sNu_aperiodic
      (List.map toA (List.ofFn Γ)) (Multiset.map toA 𝔪) (GlobalTheory.CompanionTheory.ZcWords.aOrdered_of_isOrderedForm hΓ)
      (GlobalTheory.CompanionTheory.ZcWords.inSh_of_inShW hsh) hne
    rw [GlobalTheory.CompanionTheory.ZcWords.coe_map_ofFn hΓ, tri_sqLen_map_toA, tri_sqLen_map_toA] at hlt
    exact hlt

end PositivityTheory.Groth

end
