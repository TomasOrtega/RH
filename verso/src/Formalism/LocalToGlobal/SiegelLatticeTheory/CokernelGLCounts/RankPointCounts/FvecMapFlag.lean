import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.SymmMemOfMem

noncomputable section

open scoped Classical
open Module Matrix
open Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.L2.SG.TermOp

namespace Formalism.L2.SG.NGCut.NormalVectorPairings

variable {E : Type} [Field E] [NumberField E] [StarRing E] {S : HSpace E} {r : ℕ} {T T' : E}

/- English proof (translation)
Establish `hF : F.fvec = G.fvec` using `funext h`. Establish `hF' : F'.fvec = G'.fvec` using `funext h'`. Establish `hZ : Zhat F F' = Zhat G G'`. Unfold `Zhat`. Use `first`.

Consider the case `rw [hF, hF']`. Consider the case `(simp only [hF, hF']; rfl)`. Use `⟨?_, hZ⟩` and prove the remaining obligations. Unfold `omp`. Rewrite using `[hZ, hF']`.
-/
theorem omp_congr {F G : FlagG S r T} {F' G' : FlagG S r T'} (h : ∀ a, F.fvec a = G.fvec a)
    (h' : ∀ a, F'.fvec a = G'.fvec a) : omp F F' = omp G G' ∧ Zhat F F' = Zhat G G' := by
  have hF : F.fvec = G.fvec := funext h
  have hF' : F'.fvec = G'.fvec := funext h'
  have hZ : Zhat F F' = Zhat G G' := by
    unfold Zhat
    first
      | rw [hF, hF']
      | (simp only [hF, hF']; rfl)
  refine ⟨?_, hZ⟩
  unfold omp
  rw [hZ, hF']

/- English proof (translation)
Unfold `FlagG.fvec`. Proceed by induction on `b using Fin.lastCases with`. Consider the case `last => simp [mapFlag]`. Consider the case `cast i => simp [mapFlag]`.
-/
theorem fvec_mapFlag (g : S.V ≃ₗ[E] S.V) (hg : g ∈ Formalism.HermitianLatticesTheory.isom S.hT) (F : FlagG S r T) (b : Fin (r + 1)) :
    (mapFlag g hg F).fvec b = g (F.fvec b) := by
  unfold FlagG.fvec
  induction b using Fin.lastCases with
  | last => simp [mapFlag]
  | cast i => simp [mapFlag]

/- English proof (translation)
Establish `hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧ s (F.e b') = F.e b' + ∑ i, l i • F.e i`. Introduce `b'`. Establish `hmem : F.e b' ∈ F.Xa (b'.1 + 1)` using `Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩`. Establish `h1` using `hs b'.1 (F.e b') hmem`. Take `⟨l, hl, hl2⟩` from `(Finsupp.mem_span_image_iff_linearCombination E).1 h1`.

Use `⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩` and prove the remaining obligations. Rewrite `hl2` using `[Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Rewrite using `[hl2]`. Normalize the expressions using the abelian group laws. Use `choose l hl0 hl using hcolE`.

Take `⟨cz, hcz⟩` from `(Submodule.mem_span_range_iff_exists_fun E).1 hz`. Set `M : Matrix (Fin (r + 1)) (Fin (r + 1)) E` to `Matrix.of fun c b => Fin.lastCases (motive := fun _ => E) (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c) (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b`. Establish `hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c`. Introduce `b`. Proceed by induction on `b using Fin.lastCases with`.

Consider the case `last`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, one_smul]`. Establish `h2 : s F.z = F.z + ∑ i, cz i • F.e i`. Rewrite using `[hcz]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h2, add_comm]`. Consider the case `cast b'`. Rewrite using `[Fin.sum_univ_castSucc]`. Simplify using `only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec, Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul, one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`.

Conclude with `hl b'`. Establish `hdiag : ∀ i, M i i = 1`. Introduce `i`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [M]`.

Consider the case `cast i => simp [M, hl0 i i (lt_irrefl _)]`. Establish `htri : M.BlockTriangular id`. Introduce `i j hij`. Proceed by induction on `j using Fin.lastCases with`. Consider the case `last => exact absurd hij (not_lt.2 (Fin.le_last i))`.

Consider the case `cast j`. Proceed by induction on `i using Fin.lastCases with`. Consider the case `last => simp [M]`. Consider the case `cast i`. Establish `hji : j < i` using `by simpa using hij`.

Establish `hne : i ≠ j` using `(ne_of_lt hji).symm`. Simplify using `[M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]`. Use `⟨M, hMcol, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_of_upperTriangular htri]`. Conclude with `Finset.prod_eq_one fun i _ => hdiag i`.

Introduce `c`. Proceed by induction on `c using Fin.lastCases with`. Consider the case `last => simp [M]`. Consider the case `cast c => simp [M, Fin.castSucc_ne_last]`.
-/
theorem coef_mat (F : FlagG S r T) (s : S.V →ₗ[E] S.V) (hs : ∀ j, ∀ x ∈ F.Xa (j + 1), s x - x ∈ F.Xa j)
    (hz : s F.z - F.z ∈ F.X) :
    ∃ M : Matrix (Fin (r + 1)) (Fin (r + 1)) E, (∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c) ∧ M.det = 1 ∧
      ∀ c, M (Fin.last r) c = if c = Fin.last r then 1 else 0 := by
  have hcolE : ∀ b' : Fin r, ∃ l : Fin r →₀ E, (∀ i : Fin r, ¬ i.1 < b'.1 → l i = 0) ∧
      s (F.e b') = F.e b' + ∑ i, l i • F.e i := by
    intro b'
    have hmem : F.e b' ∈ F.Xa (b'.1 + 1) := Submodule.subset_span ⟨b', Nat.lt_succ_self _, rfl⟩
    have h1 := hs b'.1 (F.e b') hmem
    obtain ⟨l, hl, hl2⟩ := (Finsupp.mem_span_image_iff_linearCombination E).1 h1
    refine ⟨l, fun i hi => (Finsupp.mem_supported' E l).1 hl i hi, ?_⟩
    rw [Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)] at hl2
    rw [hl2]
    abel
  choose l hl0 hl using hcolE
  obtain ⟨cz, hcz⟩ := (Submodule.mem_span_range_iff_exists_fun E).1 hz
  let M : Matrix (Fin (r + 1)) (Fin (r + 1)) E := Matrix.of fun c b =>
    Fin.lastCases (motive := fun _ => E)
      (Fin.lastCases (motive := fun _ => E) 1 (fun i => cz i) c)
      (fun b' => Fin.lastCases (motive := fun _ => E) 0 (fun i => (if i = b' then 1 else 0) + l b' i) c) b
  have hMcol : ∀ b, s (F.fvec b) = ∑ c, M c b • F.fvec c := by
    intro b
    induction b using Fin.lastCases with
    | last =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, one_smul]
      have h2 : s F.z = F.z + ∑ i, cz i • F.e i := by
        rw [hcz]
        abel
      rw [h2, add_comm]
    | cast b' =>
      rw [Fin.sum_univ_castSucc]
      simp only [M, Matrix.of_apply, Fin.lastCases_last, Fin.lastCases_castSucc, Formalism.MainNotions.S.FlagG.fvec,
        Fin.snoc_last, Fin.snoc_castSucc, zero_smul, add_zero, add_smul, Finset.sum_add_distrib, ite_smul,
        one_smul, Finset.sum_ite_eq', Finset.mem_univ, if_true]
      exact hl b'
  have hdiag : ∀ i, M i i = 1 := by
    intro i
    induction i using Fin.lastCases with
    | last => simp [M]
    | cast i => simp [M, hl0 i i (lt_irrefl _)]
  have htri : M.BlockTriangular id := by
    intro i j hij
    induction j using Fin.lastCases with
    | last => exact absurd hij (not_lt.2 (Fin.le_last i))
    | cast j =>
      induction i using Fin.lastCases with
      | last => simp [M]
      | cast i =>
        have hji : j < i := by simpa using hij
        have hne : i ≠ j := (ne_of_lt hji).symm
        simp [M, hne, hl0 j i (not_lt.2 (le_of_lt hji))]
  refine ⟨M, hMcol, ?_, ?_⟩
  · rw [Matrix.det_of_upperTriangular htri]
    exact Finset.prod_eq_one fun i _ => hdiag i
  · intro c
    induction c using Fin.lastCases with
    | last => simp [M]
    | cast c => simp [M, Fin.castSucc_ne_last]

end Formalism.L2.SG.NGCut.NormalVectorPairings
