import Formalism.LocalToGlobal.Columns.RecLevelSym
import Formalism.LocalToGlobal.Columns.Record

noncomputable section

open NumberField IsDedekindDomain Matrix

namespace Formalism.L2.Col

open Formalism.BasicNotions (Ranks)

section SymExt

variable {κ : Type} [CommRing κ]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[diagEmb_val]`. Use `show padM κ n h.1 i j = diagMat n (n + 1) h.1 i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j`.

Rewrite using `[diagMat_of_not_left _ _ (by simp)]`. Simplify using `[padM]`. Rewrite using `[diagMat_of_not_left _ _ (by simp)]`. Simplify using `[padM, (Fin.castSucc_ne_last _).symm]`. Rewrite using `[diagMat_of_not_right _ _ (by simp)]`.

Simplify using `[padM, Fin.castSucc_ne_last]`. Rewrite using `[diagMat_of_lt _ (show (Fin.castSucc i').val < n from i'.2) (show (Fin.castSucc j').val < n from j'.2)]`. Simplify using `[padM]`.
-/
theorem symX_padM_eq {n : ℕ} (h : GL (Fin n) κ) : Units.map (padM κ n) h = diagEmb κ (Nat.le_succ n) h := by
  apply Units.ext
  ext i j
  rw [diagEmb_val]
  show padM κ n h.1 i j = diagMat n (n + 1) h.1 i j
  refine Fin.lastCases ?_ (fun i' => ?_) i <;> refine Fin.lastCases ?_ (fun j' => ?_) j
  · rw [diagMat_of_not_left _ _ (by simp)]
    simp [padM]
  · rw [diagMat_of_not_left _ _ (by simp)]
    simp [padM, (Fin.castSucc_ne_last _).symm]
  · rw [diagMat_of_not_right _ _ (by simp)]
    simp [padM, Fin.castSucc_ne_last]
  · rw [diagMat_of_lt _ (show (Fin.castSucc i').val < n from i'.2) (show (Fin.castSucc j').val < n from j'.2)]
    simp [padM]

/- English proof (translation)
Take `⟨hB, h0⟩` from `mem_HPar.mp hg`. Establish `hB' : diagEmb κ (Nat.le_succ n') g ∈ blockUT (n' + 1) κ r (List.replicate m t)`. Use `mem_btG.mpr fun i j hij => ?_` and prove the remaining obligations. Rewrite using `[diagEmb_val]`. Distinguish the cases in `hi : i.val < n'`.

Distinguish the cases in `hj : j.val < n'`. Rewrite using `[diagMat_of_lt _ hi hj]`. Conclude with `(mem_btG.mp hB) ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij`. It suffices to derive a contradiction. Use `blkIdx_mono (r :: List.replicate m t) (show i.val ≤ j.val by omega)` as an intermediate fact.

Unfold `coarse at hij`. Use linear arithmetic over natural numbers and integers. Rewrite using `[diagMat_of_not_left _ _ hi]`. Conclude with `Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)`. Use `⟨mem_HPar.mpr ⟨hB', ?_⟩, ?_⟩` and prove the remaining obligations.

Establish `e : blk0 (n' + 1) κ hrN (List.replicate m t) ⟨diagEmb κ (Nat.le_succ n') g, hB'⟩ = blk0 n' κ hr (List.replicate m t) ⟨g, hB⟩`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[blockZero_val, blockZero_val]`. Use `show (diagEmb κ (Nat.le_succ n') g : Matrix (Fin (n' + 1)) (Fin (n' + 1)) κ) (Fin.castLE hrN a) (Fin.castLE hrN b) = (g : Matrix (Fin n') (Fin n') κ) (Fin.castLE hr a) (Fin.castLE hr b)`.

Rewrite using `[diagEmb_val, diagMat_of_lt _ (show (Fin.castLE hrN a).val < n' by simp; omega) (show (Fin.castLE hrN b).val < n' by simp; omega)]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `h0`. Introduce `i j hj`.

Rewrite using `[diagEmb_val, diagMat_of_not_right _ _ (by omega)]`.
-/
theorem diagEmb_mem_HXmsym {n' k r t m rS : ℕ} (hn : n' = r + m * t) (hr : r ≤ n') (hrN : r ≤ n' + 1) (g : GL (Fin n') κ)
    (hg : g ∈ HJsym κ n' k r t m rS hr) : diagEmb κ (Nat.le_succ n') g ∈ HXmsym κ (n' + 1) k r t m rS hrN := by
  obtain ⟨hB, h0⟩ := mem_HPar.mp hg
  have hB' : diagEmb κ (Nat.le_succ n') g ∈ blockUT (n' + 1) κ r (List.replicate m t) := by
    refine mem_btG.mpr fun i j hij => ?_
    rw [diagEmb_val]
    by_cases hi : i.val < n'
    · by_cases hj : j.val < n'
      · rw [diagMat_of_lt _ hi hj]
        exact (mem_btG.mp hB) ⟨i.val, hi⟩ ⟨j.val, hj⟩ hij
      · exfalso
        have := blkIdx_mono (r :: List.replicate m t) (show i.val ≤ j.val by omega)
        unfold coarse at hij
        omega
    · rw [diagMat_of_not_left _ _ hi]
      exact Matrix.one_apply_ne (fun e => by rw [e] at hij; omega)
  refine ⟨mem_HPar.mpr ⟨hB', ?_⟩, ?_⟩
  · have e : blk0 (n' + 1) κ hrN (List.replicate m t) ⟨diagEmb κ (Nat.le_succ n') g, hB'⟩ =
        blk0 n' κ hr (List.replicate m t) ⟨g, hB⟩ := by
      apply Units.ext
      ext a b
      rw [blockZero_val, blockZero_val]
      show (diagEmb κ (Nat.le_succ n') g : Matrix (Fin (n' + 1)) (Fin (n' + 1)) κ) (Fin.castLE hrN a) (Fin.castLE hrN b) =
        (g : Matrix (Fin n') (Fin n') κ) (Fin.castLE hr a) (Fin.castLE hr b)
      rw [diagEmb_val, diagMat_of_lt _ (show (Fin.castLE hrN a).val < n' by simp; omega)
        (show (Fin.castLE hrN b).val < n' by simp; omega)]
      rfl
    rw [e]
    exact h0
  · intro i j hj
    rw [diagEmb_val, diagMat_of_not_right _ _ (by omega)]

/- English proof (translation)
Substitute `hN` using the available equality. Use `diagEmb_mem_HXmsym hn hr hrN (g w) hg` as an intermediate fact. Rewrite `this` using `[← symX_padM_eq]`. Conclude with `this`.
-/
theorem symX_ext_mem {E : Type} [Field E] [NumberField E] [StarRing E] {SG : Finset (HeightOneSpectrum (𝓞 E))} {N n : ℕ}
    (hN : N = n + 1) (k r t m rS : ℕ) (hn : n = r + m * t) (hr : r ≤ n) (hrN : r ≤ N) (g : GLG E n SG) (w : SG)
    (hg : g w ∈ HJsym (𝓞 E ⧸ w.1.asIdeal) n k r t m rS hr) :
    extGH hN g w ∈ HXmsym (𝓞 E ⧸ w.1.asIdeal) N k r t m rS hrN := by
  subst hN
  have := diagEmb_mem_HXmsym hn hr hrN (g w) hg
  rw [← symX_padM_eq] at this
  exact this

end SymExt

end Formalism.L2.Col
