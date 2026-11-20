import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrSpanG
import Formalism.SharpRestriction.GrowthBounds.MonomialOrderSegments.BrBase

noncomputable section

open MvPolynomial Finset

namespace Formalism.MainNotions.PlaneGram

open Formalism.MainNotions.G.Joints.PlaneGramSpan

variable {p : ℕ} {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]

/- English proof (translation)
Use extensionality with `j`. Simplify using `[initSet]`.
-/
theorem coe_initSet_zero (N : ℕ) : ((initSet N 0 : Finset (Fin N)) : Set (Fin N)) = ∅ := by
  ext j; simp [initSet]

/- English proof (translation)
Use extensionality with `j`. Simplify using `only [initSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.val_succ]`. Rewrite using `[Fin.le_iff_val_le_val]`. Use linear arithmetic over natural numbers and integers.
-/
theorem coe_initSet_succ (N : ℕ) (i : Fin N) :
    ((initSet N (i.succ : Fin (N + 1)).val : Finset (Fin N)) : Set (Fin N)) = {j | j ≤ i} := by
  ext j
  simp only [initSet, Finset.coe_filter, Finset.mem_univ, true_and, Set.mem_setOf_eq, Fin.val_succ]
  rw [Fin.le_iff_val_le_val]
  omega

/- English proof (translation)
Introduce `_ N r _ sg d`. Take `⟨h3a, h3b, h3c⟩` from `h3`. Set `LL : G.Letters (Fin N)` to `⟨sg⟩`. Use `haveI : Finite (Idx N r LL d) := idx_finite h3a N r LL d`. Use `letI : Fintype (Idx N r LL d) := Fintype.ofFinite _`.

Establish `hint : ∀ F : MvPolynomial (Fin N × Fin r) (G.KK O), Integral (vQ p S) F → ∀ m, ∃ o : O, coeff m F = algebraMap O (G.KK O) o` using `fun F hF m => (vQ_nonneg_iff S _).1 (hF m)`. Set `cI : (b : Idx N r LL d) → Fin #(G.colRange b.1.1.mu) → ℤ` to `fun b k => ((G.colRange b.1.1.mu).equivFin.symm k : ℤ)`. Use `⟨Idx N r LL d, inferInstance, fun b => G.Psi (G.KK O) b.1.1.mu b.1.2, fun b => b.1.1.mu, fun b => #(G.colRange b.1.1.mu), fun b k => G.Kcol (G.KK O) b.1.1.mu (cI b k) N (b.1.2 (cI b k)), cI, fun b k i => b.1.1.h i (cI b k), fun b k => Finset.univ.filter (fun i => G.IsUsed b.1.1.m …` and prove the remaining obligations. Introduce `b`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[PolK_eq]`. Conclude with `(psiK_mem h3a b).1`. Introduce `m`. Take `⟨o, ho⟩` from `(psiK_mem h3a b).2 m`. Rewrite using `[ho]`.

Conclude with `(vQ_nonneg_iff S _).2 ⟨o, rfl⟩`. Introduce `F hF`. Take `⟨hFK, hFI⟩` from `hF`. Rewrite `hFK` using `[PolK_eq]`. Take `⟨l, hl⟩` from `span_all (LL := LL) h3a F hFK (hint F hFI)`.

Conclude with `⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, hl⟩`. Introduce and unpack `th F ⟨⟨hFK, hFI⟩, hA⟩`. Rewrite `hFK` using `[PolK_eq]`. Establish `hth : ∀ i : Fin N, ((th i.succ : ℤ) : WithTop ℤ) ≤ G.valS LL {j | j ≤ i} F`. Introduce `i`.

Establish `h1` using `hA i.succ`. Express the relevant statement in the definitionally equal form `((th i.succ : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (i.succ : Fin (N + 1)).val) F at h1`. Rewrite `h1` using `[valS_eq, coe_initSet_succ]`. Conclude with `h1`. Take `⟨l, hl1, hl2⟩` from `span_mem h3b F hFK (hint F hFI) (fun i => th i.succ) hth`.

Use `⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, ?_, hl2⟩` and prove the remaining obligations. Introduce `b hb i`. Establish `hlb : l b ≠ 0`. Introduce `h0`. Apply `hb` to reduce the goal to its premises.

Simplify using `[h0]`. Simplify using `only`. Rewrite using `[lastIdx_eq]`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`.

Rewrite using `[b.1.1.zero]`. Establish `hF0 : F ≠ 0`. Introduce `hF0`. Rewrite `hl2` using `[hF0]`. Establish `hz` using `Fintype.linearIndependent_iff.1 (li_K h3a N r LL d) _ hl2.symm b`.

Conclude with `hlb (IsFractionRing.injective O (G.KK O) (by rw [hz, map_zero]))`. Establish `h0` using `hA 0`. Express the relevant statement in the definitionally equal form `((th 0 : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (0 : Fin (N + 1)).val) F at h0`. Rewrite `h0` using `[valS_eq, Fin.val_zero, coe_initSet_zero]`. Conclude with `valS_empty_le LL F hF0 _ h0`.

Consider the case `succ j => exact hl1 b hlb j`. Introduce `b`. Conclude with `(prod_fin_equiv (G.colRange b.1.1.mu) (fun c => G.Kcol (G.KK O) b.1.1.mu c N (b.1.2 c))).symm`. Introduce `b k dsimp only`. Rewrite using `[PolK, mem_restrictSupport_iff]`.

Introduce `m hm`. Rewrite `hm` using `[← Formalism.MainNotions.G.Joints.StandardMonomialSpace.lift_Kcol_map (algebraMap O (G.KK O))]`. Establish `hm'` using `MvPolynomial.support_map_subset _ _ hm`. Introduce `i`. Establish `h1` using `(h3c N r LL d b.1.1).1 (cI b k) (b.1.2 (cI b k)) i m hm'`.

Simplify `h1` using `[G.multideg]`. Introduce `b i`. Rewrite using `[← (h3c N r LL d b.1.1).2.1 i]`. Use `Finset.card_bij (fun k _ => (((G.colRange b.1.1.mu).equivFin.symm k : ℤ))) ?_ ?_ ?_` and prove the remaining obligations. Introduce `k hk`.

Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢`. Conclude with `⟨Subtype.prop _, hk⟩`. Introduce `k1 _ k2 _ h`. Conclude with `(G.colRange b.1.1.mu).equivFin.symm.injective (Subtype.ext h)`. Introduce `c hc`.

Simplify using `only [Finset.mem_filter] at hc`. Use `⟨(G.colRange b.1.1.mu).equivFin ⟨c, hc.1⟩, ?_, ?_⟩` and prove the remaining obligations. Simplify using `[cI, hc.2]`. Simplify using the standard rewrite rules. Introduce `b k i hc`.

Use `((h3c N r LL d b.1.1).2.2.2.1 (cI b k) hc i).trans (le_of_eq ?_)` and prove the remaining obligations. Use `congr 1`. Use extensionality with `j`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, LL]`. The claim follows by propositional logic.

Introduce `b k i dsimp only`. Rewrite using `[valS_eq]`. Consider the cases of `i using Fin.cases with`. Consider the case `zero`. Rewrite using `[Fin.val_zero, coe_initSet_zero]`.

Establish `hv0 : colVal (cI b k) (b.1.1.h 0 (cI b k)) r = 0` using `by show colVal (cI b k) (G.colH (b.1.1.mu 0) (cI b k)) r = 0`. Rewrite using `[b.1.1.zero, colH_zero]`. Establish `hr` using `NeZero.ne r`. Simplify using `only [colVal]`. Apply the tactic sequence `split_ifs <;> omega`.

Rewrite using `[hv0]`. Conclude with `valS_empty_nonneg LL _`. Consider the case `succ j`. Rewrite using `[coe_initSet_succ]`. Conclude with `col_est h3b b.1.1 (cI b k) (b.1.2 (cI b k)) (b.2.2.1 (cI b k)) j`.

Introduce `b i dsimp only`. Rewrite using `[lastIdx_eq, stage_identity b.1.1 i]`. Conclude with `(sum_fin_equiv _ (fun c => colVal c (b.1.1.h i c) r)).symm`.
-/
theorem brSPAN [CharZero (G.KK O)] (S : G.UniformizedDVR p O) (h3 : Formalism.MainNotions.PlaneGramData.PolynomialSpanAtRing O) :
    SPAN (G.KK O) (vQ p S) p := by
  classical
  intro _ N r _ sg d
  obtain ⟨h3a, h3b, h3c⟩ := h3
  let LL : G.Letters (Fin N) := ⟨sg⟩
  haveI : Finite (Idx N r LL d) := idx_finite h3a N r LL d
  letI : Fintype (Idx N r LL d) := Fintype.ofFinite _
  have hint : ∀ F : MvPolynomial (Fin N × Fin r) (G.KK O), Integral (vQ p S) F →
      ∀ m, ∃ o : O, coeff m F = algebraMap O (G.KK O) o :=
    fun F hF m => (vQ_nonneg_iff S _).1 (hF m)
  let cI : (b : Idx N r LL d) → Fin #(G.colRange b.1.1.mu) → ℤ :=
    fun b k => ((G.colRange b.1.1.mu).equivFin.symm k : ℤ)
  refine ⟨Idx N r LL d, inferInstance, fun b => G.Psi (G.KK O) b.1.1.mu b.1.2, fun b => b.1.1.mu,
    fun b => #(G.colRange b.1.1.mu), fun b k => G.Kcol (G.KK O) b.1.1.mu (cI b k) N (b.1.2 (cI b k)),
    cI, fun b k i => b.1.1.h i (cI b k),
    fun b k => Finset.univ.filter (fun i => G.IsUsed b.1.1.mu (cI b k) i),
    ?_, li_K h3a N r LL d, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro b
    refine ⟨?_, ?_⟩
    · rw [PolK_eq]
      exact (psiK_mem h3a b).1
    · intro m
      obtain ⟨o, ho⟩ := (psiK_mem h3a b).2 m
      rw [ho]
      exact (vQ_nonneg_iff S _).2 ⟨o, rfl⟩
  · intro F hF
    obtain ⟨hFK, hFI⟩ := hF
    rw [PolK_eq] at hFK
    obtain ⟨l, hl⟩ := span_all (LL := LL) h3a F hFK (hint F hFI)
    exact ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, hl⟩
  · rintro th F ⟨⟨hFK, hFI⟩, hA⟩
    rw [PolK_eq] at hFK
    have hth : ∀ i : Fin N, ((th i.succ : ℤ) : WithTop ℤ) ≤ G.valS LL {j | j ≤ i} F := by
      intro i
      have h1 := hA i.succ
      change ((th i.succ : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (i.succ : Fin (N + 1)).val) F at h1
      rw [valS_eq, coe_initSet_succ] at h1
      exact h1
    obtain ⟨l, hl1, hl2⟩ := span_mem h3b F hFK (hint F hFI) (fun i => th i.succ) hth
    refine ⟨fun b => algebraMap O _ (l b), fun b => (vQ_nonneg_iff S _).2 ⟨_, rfl⟩, ?_, hl2⟩
    intro b hb i
    have hlb : l b ≠ 0 := by
      intro h0
      apply hb
      simp [h0]
    dsimp only
    rw [lastIdx_eq]
    cases i using Fin.cases with
    | zero =>
      rw [b.1.1.zero]
      have hF0 : F ≠ 0 := by
        intro hF0
        rw [hF0] at hl2
        have hz := Fintype.linearIndependent_iff.1 (li_K h3a N r LL d) _ hl2.symm b
        exact hlb (IsFractionRing.injective O (G.KK O) (by rw [hz, map_zero]))
      have h0 := hA 0
      change ((th 0 : ℤ) : WithTop ℤ) ≤ valS sg (initSet N (0 : Fin (N + 1)).val) F at h0
      rw [valS_eq, Fin.val_zero, coe_initSet_zero] at h0
      exact valS_empty_le LL F hF0 _ h0
    | succ j => exact hl1 b hlb j
  · intro b
    exact (prod_fin_equiv (G.colRange b.1.1.mu) (fun c => G.Kcol (G.KK O) b.1.1.mu c N (b.1.2 c))).symm
  · intro b k
    dsimp only
    rw [PolK, mem_restrictSupport_iff]
    intro m hm
    rw [← Formalism.MainNotions.G.Joints.StandardMonomialSpace.lift_Kcol_map (algebraMap O (G.KK O))] at hm
    have hm' := MvPolynomial.support_map_subset _ _ hm
    intro i
    have h1 := (h3c N r LL d b.1.1).1 (cI b k) (b.1.2 (cI b k)) i m hm'
    simpa [G.multideg] using h1
  · intro b i
    rw [← (h3c N r LL d b.1.1).2.1 i]
    refine Finset.card_bij (fun k _ => (((G.colRange b.1.1.mu).equivFin.symm k : ℤ))) ?_ ?_ ?_
    · intro k hk
      simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hk ⊢
      exact ⟨Subtype.prop _, hk⟩
    · intro k1 _ k2 _ h
      exact (G.colRange b.1.1.mu).equivFin.symm.injective (Subtype.ext h)
    · intro c hc
      simp only [Finset.mem_filter] at hc
      refine ⟨(G.colRange b.1.1.mu).equivFin ⟨c, hc.1⟩, ?_, ?_⟩
      · simp [cI, hc.2]
      · simp
  · intro b k i hc
    refine ((h3c N r LL d b.1.1).2.2.2.1 (cI b k) hc i).trans (le_of_eq ?_)
    congr 1
    ext j
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, LL]
    tauto
  · intro b k i
    dsimp only
    rw [valS_eq]
    cases i using Fin.cases with
    | zero =>
      rw [Fin.val_zero, coe_initSet_zero]
      have hv0 : colVal (cI b k) (b.1.1.h 0 (cI b k)) r = 0 := by
        show colVal (cI b k) (G.colH (b.1.1.mu 0) (cI b k)) r = 0
        rw [b.1.1.zero, colH_zero]
        have hr := NeZero.ne r
        simp only [colVal]
        split_ifs <;> omega
      rw [hv0]
      exact valS_empty_nonneg LL _
    | succ j =>
      rw [coe_initSet_succ]
      exact col_est h3b b.1.1 (cI b k) (b.1.2 (cI b k)) (b.2.2.1 (cI b k)) j
  · intro b i
    dsimp only
    rw [lastIdx_eq, stage_identity b.1.1 i]
    exact (sum_fin_equiv _ (fun c => colVal c (b.1.1.h i c) r)).symm

end Formalism.MainNotions.PlaneGram
