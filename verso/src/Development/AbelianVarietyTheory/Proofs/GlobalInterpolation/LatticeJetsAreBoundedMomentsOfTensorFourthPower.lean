import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.LatIntZero
import Formalism.LocalToGlobal.TorsionIntegrality.QuadraticSemicharacters.IsSemiChar
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerCoefficientNormLeOneIffJetsBoundedMeasureMStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientOfFamilyZeroOffEmbeddingStatement
import Development.AbelianVarietyTheory.Proofs.GlobalInterpolation.MahlerJetCoefficientMulOfDisjointSupportStatement

open GlobalTheory.MomN Formalism.L2.Th1.H

noncomputable section

namespace GlobalTheory.MomRoot

/- English proof (translation)
Unfold `GlobalTheory.MomN.mahler`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Use `congr 1`. Unfold `GlobalTheory.MomN.monoJet`. Establish `h` using `L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top`.

Express the relevant statement in the definitionally equal form `iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _`. Rewrite using `[h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]`.
-/
theorem mahler_comp_clm (E V : Type) [NormedAddCommGroup E] [NormedSpace ℂ E] [NormedAddCommGroup V] [NormedSpace ℂ V]
    (κ : Type) [Fintype κ] (L : E →L[ℂ] V) (u : κ → E) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G) (k : κ → ℕ) :
    mahler u (fun z => G (L z)) k = mahler (fun i => L (u i)) G k := by
  unfold GlobalTheory.MomN.mahler
  refine Finset.sum_congr rfl fun m _ => ?_
  congr 1
  unfold GlobalTheory.MomN.monoJet
  have h := L.iteratedFDeriv_comp_right hG (0 : E) (i := m.toMultiset.toList.length) le_top
  change iteratedFDeriv ℂ _ (G ∘ L) 0 _ = _
  rw [h, ContinuousMultilinearMap.compContinuousLinearMap_apply, map_zero]

/- English proof (translation)
The claim follows from `GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding V κ ι' e w u G hG hu hz`.
-/
theorem mahler_embed (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (κ ι' : Type) [Fintype κ] [Fintype ι']
    (e : κ ↪ ι') (w : κ → V) (u : ι' → V) (G : V → ℂ) (hG : ContDiff ℂ ⊤ G)
    (hu : ∀ i, u (e i) = w i) (hz : ∀ p, p ∉ Set.range e → u p = 0) :
    (∀ k : ι' → ℕ, (∃ p, p ∉ Set.range e ∧ k p ≠ 0) → mahler u G k = 0) ∧
    (∀ k : ι' → ℕ, (∀ p, p ∉ Set.range e → k p = 0) → mahler u G k = mahler w G (fun i => k (e i))) :=
  GlobalTheory.T.mahlerJetCoefficient_of_family_zero_off_embedding V κ ι' e w u G hG hu hz

/- English proof (translation)
The claim follows from `GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT`.
-/
theorem mahler_mul_disj (V : Type) [NormedAddCommGroup V] [NormedSpace ℂ V] (ι' : Type) [Fintype ι'] [DecidableEq ι']
    (u : ι' → V) (F H : V → ℂ) (hF : ContDiff ℂ ⊤ F) (hH : ContDiff ℂ ⊤ H) (S T : Finset ι') (hST : Disjoint S T)
    (hFS : ∀ k : ι' → ℕ, (∃ p, p ∉ S ∧ k p ≠ 0) → mahler u F k = 0)
    (hHT : ∀ k : ι' → ℕ, (∃ p, p ∉ T ∧ k p ≠ 0) → mahler u H k = 0) :
    (∀ N : ι' → ℕ, (∃ p, p ∉ S ∪ T ∧ N p ≠ 0) → mahler u (fun z => F z * H z) N = 0) ∧
    (∀ N : ι' → ℕ, (∀ p, p ∉ S ∪ T → N p = 0) → mahler u (fun z => F z * H z) N =
      mahler u F (fun p => if p ∈ S then N p else 0) * mahler u H (fun p => if p ∈ T then N p else 0)) :=
  GlobalTheory.T.mahlerJetCoefficient_mul_of_disjoint_support V ι' u F H hF hH S T hST hFS hHT

variable {n : Type} [Fintype n]

def sliceL (a : Fin 4) : (Fin 4 × n → ℂ) →L[ℂ] (n → ℂ) :=
  ContinuousLinearMap.pi fun i => ContinuousLinearMap.proj (a, i)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem sliceL_apply (a : Fin 4) (z : Fin 4 × n → ℂ) : sliceL a z = slice a z := rfl

def fourBlockInclusionVector (b : Fin 4) (x : n → ℂ) : Fin 4 × n → ℂ := fun z => if z.1 = b then x z.2 else 0

/- English proof (translation)
Apply the tactic sequence `funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]`.
-/
theorem slice_fourBlockInclusionVector (a b : Fin 4) (x : n → ℂ) : slice a (fourBlockInclusionVector b x) = if a = b then x else 0 := by
  funext i; by_cases h : a = b <;> simp [slice, fourBlockInclusionVector, h]

end GlobalTheory.MomRoot

namespace GlobalTheory.MomRoot

/- English proof (translation)
Introduce `q _ ι n _ ω Λ G hG hL κ _ v hv`. Use `set c := ι.symm ω`. Rewrite using `[GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι (n → ℂ) κ _ G hG]`. Introduce `m`. Set `U : Fin 4 × κ → (Fin 4 × n → ℂ)` to `fun p => c • fourBlockInclusionVector p.1 (v p.2)`.

Establish `hU : MomInt ι U (tens4 G)` using `hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ`. Rewrite using `[slice_fourBlockInclusionVector]`. Use `split_ifs`. Conclude with `hv _`. Conclude with `Λ.zero_mem)`.

Establish `hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z))` using `fun a => by`. Establish `h : ContDiff ℂ ⊤ (sliceL (n` using `n) a) := ContinuousLinearMap.contDiff _`. Conclude with `hG.comp h`. Establish `ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z)`. Use function extensionality and compare the values at `z`.

Simplify using `[tens4, Fin.prod_univ_four]`. Establish `hcd : ContDiff ℂ ⊤ (tens4 G)`. Rewrite using `[ht]`. Conclude with `(((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)`. Establish `hb` using `((GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)`.

Set `S : Fin 4 → Finset (Fin 4 × κ)` to `fun a => Finset.univ.filter (fun p => p.1 = a)`. Set `e : Fin 4 → κ ↪ Fin 4 × κ` to `fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩`. Establish `hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧ (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) → mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i)))`. Introduce `a`. Establish `he : ∀ i, e a i = (a, i)` using `fun _ => rfl`.

Establish `hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k` using `fun k => by`. Establish `h` using `mahler_comp_clm _ _ _ (sliceL a) U G hG k`. Simplify using `only [sliceL_apply] at h`. Conclude with `h`. Establish `hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a`.

Introduce and unpack `⟨b, i⟩`. Simplify using `[Set.mem_range, he, S, eq_comm]`. Take `⟨h1, h2⟩` from `mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector]) (fun p hp => by`. Establish `: p.1 ≠ a` using `fun h => hp ((hrange p).2 (by simp [S, h]))`. Simplify using `[U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])`.

Use `⟨fun k hk => ?_, fun k hk => ?_⟩` and prove the remaining obligations. Rewrite using `[hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩`. Rewrite using `[hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))`. Establish `dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b)`. Introduce `A b hb`.

Rewrite using `[Finset.disjoint_left]`. Introduce `p hp hq`. Simplify using `only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq`. Take `⟨a, ha, rfl⟩` from `hp`. Conclude with `hb (hq ▸ ha)`.

Establish `u1 : ({0} : Finset (Fin 4)).biUnion S = S 0` using `by simp`. Establish `u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1` using `by simp [Finset.biUnion_insert]`. Establish `u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2`. Simplify using `[Finset.biUnion_insert, Finset.union_assoc]`. Establish `d1` using `dj {0} 1 (by decide)`.

Establish `d2` using `dj {0, 1} 2 (by decide)`. Establish `d3` using `dj {0, 1, 2} 3 (by decide)`. Rewrite `d1` using `[u1]`. Rewrite `d2` using `[u2]`. Rewrite `d3` using `[u3]`.

Take `⟨A1v, A1⟩` from `mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1`. Take `⟨A2v, A2⟩` from `mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1`. Take `⟨-, A3⟩` from `mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3) (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1`. Establish `key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4`. Rewrite using `[ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]`.

Simplify using `only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]`. Evaluate the numerical expressions. Expand and normalize the polynomial expressions, which then agree. Use `all_goals`. Introduce `p hp`.

Break down `p with ⟨b, i⟩` into its components or cases. Simplify using `only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢`. Apply the tactic sequence `fin_cases b <;> simp at hp ⊢`. Rewrite `hb` using `[key, map_pow, norm_pow]`. Conclude with `(pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb`.
-/
theorem jets_root : ∀ (q : ℕ) [Fact q.Prime] (ι : ℂ ≃+* ℂ_[q]) (n : Type) [Fintype n] (ω : ℂ_[q]) (Λ : AddSubgroup (n → ℂ))
    (G : (n → ℂ) → ℂ), ContDiff ℂ ⊤ G → LatInt ι ω (pow4 Λ) (tens4 G) → LatInt ι ω Λ G := by
  intro q _ ι n _ ω Λ G hG hL κ _ v hv
  classical
  set c := ι.symm ω
  rw [GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι (n → ℂ) κ _ G hG]
  intro m
  let U : Fin 4 × κ → (Fin 4 × n → ℂ) := fun p => c • fourBlockInclusionVector p.1 (v p.2)
  have hU : MomInt ι U (tens4 G) := hL (Fin 4 × κ) (fun p => fourBlockInclusionVector p.1 (v p.2)) (fun p a => by
    show slice a (fourBlockInclusionVector p.1 (v p.2)) ∈ Λ
    rw [slice_fourBlockInclusionVector]; split_ifs
    · exact hv _
    · exact Λ.zero_mem)
  have hGa : ∀ a, ContDiff ℂ ⊤ (fun z => G (slice a z)) := fun a => by
    have h : ContDiff ℂ ⊤ (sliceL (n := n) a) := ContinuousLinearMap.contDiff _
    exact hG.comp h
  have ht : tens4 G = fun z => G (slice 0 z) * G (slice 1 z) * G (slice 2 z) * G (slice 3 z) := by
    funext z; simp [tens4, Fin.prod_univ_four]
  have hcd : ContDiff ℂ ⊤ (tens4 G) := by
    rw [ht]; exact (((hGa 0).mul (hGa 1)).mul (hGa 2)).mul (hGa 3)
  have hb := ((GlobalTheory.T.mahlerCoefficient_norm_le_one_iff_jets_boundedMeasureMoments q ι _ _ U (tens4 G) hcd).1 hU) (fun p => m p.2)
  let S : Fin 4 → Finset (Fin 4 × κ) := fun a => Finset.univ.filter (fun p => p.1 = a)
  let e : Fin 4 → κ ↪ Fin 4 × κ := fun a => ⟨fun i => (a, i), fun i j h => (Prod.mk.inj h).2⟩
  have hposition : ∀ a, (∀ k : Fin 4 × κ → ℕ, (∃ p, p ∉ S a ∧ k p ≠ 0) → mahler U (fun z => G (slice a z)) k = 0) ∧
      (∀ k : Fin 4 × κ → ℕ, (∀ p, p ∉ S a → k p = 0) →
        mahler U (fun z => G (slice a z)) k = mahler (fun i => c • v i) G (fun i => k (a, i))) := by
    intro a
    have he : ∀ i, e a i = (a, i) := fun _ => rfl
    have hcomp : ∀ k, mahler U (fun z => G (slice a z)) k = mahler (fun p => sliceL a (U p)) G k :=
      fun k => by
        have h := mahler_comp_clm _ _ _ (sliceL a) U G hG k
        simp only [sliceL_apply] at h
        exact h
    have hrange : ∀ p : Fin 4 × κ, p ∈ Set.range (e a) ↔ p ∈ S a := by
      rintro ⟨b, i⟩; simp [Set.mem_range, he, S, eq_comm]
    obtain ⟨h1, h2⟩ := mahler_embed (n → ℂ) κ (Fin 4 × κ) (e a) (fun i => c • v i) (fun p => sliceL a (U p)) G hG
      (fun i => by simp [U, he, sliceL_apply, slice_fourBlockInclusionVector])
      (fun p hp => by
        have : p.1 ≠ a := fun h => hp ((hrange p).2 (by simp [S, h]))
        simp [U, sliceL_apply, slice_fourBlockInclusionVector, Ne.symm this])
    refine ⟨fun k hk => ?_, fun k hk => ?_⟩
    · rw [hcomp]; obtain ⟨p, hp, hk⟩ := hk; exact h1 k ⟨p, by rwa [hrange], hk⟩
    · rw [hcomp]; exact h2 k (fun p hp => hk p (by rwa [← hrange]))
  have dj : ∀ (A : Finset (Fin 4)) (b : Fin 4), b ∉ A → Disjoint (A.biUnion S) (S b) := by
    intro A b hb
    rw [Finset.disjoint_left]; intro p hp hq
    simp only [Finset.mem_biUnion, S, Finset.mem_filter, Finset.mem_univ, true_and] at hp hq
    obtain ⟨a, ha, rfl⟩ := hp; exact hb (hq ▸ ha)
  have u1 : ({0} : Finset (Fin 4)).biUnion S = S 0 := by simp
  have u2 : ({0, 1} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 := by simp [Finset.biUnion_insert]
  have u3 : ({0, 1, 2} : Finset (Fin 4)).biUnion S = S 0 ∪ S 1 ∪ S 2 := by
    simp [Finset.biUnion_insert, Finset.union_assoc]
  have d1 := dj {0} 1 (by decide)
  have d2 := dj {0, 1} 2 (by decide)
  have d3 := dj {0, 1, 2} 3 (by decide)
  rw [u1] at d1; rw [u2] at d2; rw [u3] at d3
  obtain ⟨A1v, A1⟩ := mahler_mul_disj _ _ U _ _ (hGa 0) (hGa 1) (S 0) (S 1) d1 (hposition 0).1 (hposition 1).1
  obtain ⟨A2v, A2⟩ := mahler_mul_disj _ _ U _ _ ((hGa 0).mul (hGa 1)) (hGa 2) (S 0 ∪ S 1) (S 2) d2 A1v (hposition 2).1
  obtain ⟨-, A3⟩ := mahler_mul_disj _ _ U _ _ (((hGa 0).mul (hGa 1)).mul (hGa 2)) (hGa 3)
    (S 0 ∪ S 1 ∪ S 2) (S 3) d3 A2v (hposition 3).1
  have key : mahler U (tens4 G) (fun p => m p.2) = (mahler (fun i => c • v i) G m) ^ 4 := by
    rw [ht, A3 _ ?_, A2 _ ?_, A1 _ ?_, (hposition 0).2 _ ?_, (hposition 1).2 _ ?_, (hposition 2).2 _ ?_, (hposition 3).2 _ ?_]
    · simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and]
      norm_num
      ring
    all_goals
      intro p hp
      rcases p with ⟨b, i⟩
      simp only [S, Finset.mem_union, Finset.mem_filter, Finset.mem_univ, true_and] at hp ⊢
      fin_cases b <;> simp at hp ⊢
  rw [key, map_pow, norm_pow] at hb
  exact (pow_le_one_iff_of_nonneg (norm_nonneg _) (by norm_num)).1 hb
end GlobalTheory.MomRoot
