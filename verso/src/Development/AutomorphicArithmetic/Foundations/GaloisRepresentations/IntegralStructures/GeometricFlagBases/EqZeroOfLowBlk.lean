import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.FlagBasis

open CategoryTheory Limits AlgebraicGeometry NumberField GlobalTheory.EtC GlobalTheory.Et TensorProduct Polynomial
open GlobalTheory.GalV (HTower Htot hop galV galTot)
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.MainNotions.N
open UpperTheory.Gal UpperTheory.Gal.Int.Geo

namespace UpperTheory.Gal.Int.Geo

private def blk (k : Type) [Field k] {d : ℕ} (c : Fin d → ℕ) (i : ℕ) : Submodule k (Fin d → k) where
  carrier := {v | ∀ j, c j ≠ i → v j = 0}
  zero_mem' _ _ := rfl
  add_mem' ha hb j h := by simp [ha j h, hb j h]
  smul_mem' r v hv j h := by simp [hv j h]

/- English proof (translation)
Introduce `_ hSS Γ k _ _ d ρ₀ ρ c hJH hρ`. Take `⟨hinv, hmax⟩` from `hJH`. Establish `key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a, (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a = if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0`. Introduce `g i u hu a`. Simplify using `only [Matrix.mulVec, dotProduct, hρ]`.

Use `split_ifs with h`. Use `Finset.sum_congr rfl fun b _ => ?_ split_ifs with h'` and prove the remaining obligations. Both sides reduce to the same expression. Simplify using `[hu b (by omega)]`. Use `Finset.sum_eq_zero fun b _ => ?_ split_ifs with h'` and prove the remaining obligations.

Simplify using `[hu b (by omega)]`. Simplify using the standard rewrite rules. Establish `hblk : ∀ i, IsInv ρ (blk k c i)`. Introduce `i g u hu j hj`. Rewrite using `[key g i u hu j, if_neg hj]`.

Establish `hsup : ⨆ i, blk k c i = ⊤`. Rewrite using `[eq_top_iff]`. Introduce `v _`. Rewrite using `[← Finset.univ_sum_single v]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations.

Use `Submodule.mem_iSup_of_mem (c j) ?_` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[Pi.single_eq_of_ne]`. Introduce and unpack `rfl`. Conclude with `ha rfl`.

Use `hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup` and prove the remaining obligations. Introduce `i U hU hUle`. Establish `hlow : low k c i ≤ low k c (i + 1)` using `fun v hv j hj => hv j (by omega)`. Establish `hblkle : blk k c i ≤ low k c (i + 1)` using `fun v hv j hj => hv j (by omega)`. Establish `hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0`.

Introduce `v h1 h2`. Use function extensionality and compare the values at `j`. Distinguish the cases in `h : c j = i`. Conclude with `h2 j h.ge`. Conclude with `h1 j h`.

Establish `hU'inv : IsInv ρ₀ (low k c i ⊔ U)`. Introduce `g v hv`. Take `⟨w, hw, u, hu, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[Matrix.mulVec_add]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_` and prove the remaining obligations.

Establish `huB` using `hUle hu`. Rewrite using `[← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u) ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]`. Use `Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))` and prove the remaining obligations. Introduce `a ha`. Rewrite using `[Pi.sub_apply, key g i u huB a]`.

Use `split_ifs with h`. Conclude with `sub_self _`. Rewrite using `[hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]`. Break down `hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h` into its components or cases. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `v hv`. Rewrite using `[Submodule.mem_bot]`. Establish `hv' : v ∈ low k c i`. Rewrite using `[← h]`.

Conclude with `Submodule.mem_sup_right hv`. Conclude with `hdisj v (hUle hv) hv'`. Use `right`. Apply `le_antisymm hUle` to reduce the goal to its premises. Introduce `v hv`.

Establish `hv' : v ∈ low k c i ⊔ U`. Rewrite using `[h]`. Conclude with `hblkle hv`. Take `⟨w, hw, u, hu, rfl⟩` from `Submodule.mem_sup.mp hv'`. Establish `hwB : w ∈ blk k c i`.

Use `Submodule.sub_mem _ hv (hUle hu)` as an intermediate fact. Simplify using `using this`. Rewrite using `[hdisj w hwB hw, zero_add]`. Conclude with `hu`.
-/
theorem grSS_of :
    GrHom → SSOfSum → GrSS := by
  intro _ hSS Γ k _ _ d ρ₀ ρ c hJH hρ
  obtain ⟨hinv, hmax⟩ := hJH
  have key : ∀ (g : Γ) (i : ℕ) (u : Fin d → k), u ∈ blk k c i → ∀ a,
      (↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u a =
        if c a = i then (↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u a else 0 := by
    intro g i u hu a
    simp only [Matrix.mulVec, dotProduct, hρ]
    split_ifs with h
    · refine Finset.sum_congr rfl fun b _ => ?_
      split_ifs with h'
      · rfl
      · simp [hu b (by omega)]
    · refine Finset.sum_eq_zero fun b _ => ?_
      split_ifs with h'
      · simp [hu b (by omega)]
      · simp
  have hblk : ∀ i, IsInv ρ (blk k c i) := by
    intro i g u hu j hj
    rw [key g i u hu j, if_neg hj]
  have hsup : ⨆ i, blk k c i = ⊤ := by
    rw [eq_top_iff]
    intro v _
    rw [← Finset.univ_sum_single v]
    refine Submodule.sum_mem _ fun j _ => ?_
    refine Submodule.mem_iSup_of_mem (c j) ?_
    intro a ha
    rw [Pi.single_eq_of_ne]
    rintro rfl
    exact ha rfl
  refine hSS Γ k d ρ (fun i => blk k c i) hblk ?_ hsup
  intro i U hU hUle
  have hlow : low k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hblkle : blk k c i ≤ low k c (i + 1) := fun v hv j hj => hv j (by omega)
  have hdisj : ∀ v, v ∈ blk k c i → v ∈ low k c i → v = 0 := by
    intro v h1 h2
    funext j
    by_cases h : c j = i
    · exact h2 j h.ge
    · exact h1 j h
  have hU'inv : IsInv ρ₀ (low k c i ⊔ U) := by
    intro g v hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv
    rw [Matrix.mulVec_add]
    refine Submodule.add_mem _ (Submodule.mem_sup_left (hinv i g w hw)) ?_
    have huB := hUle hu
    rw [← sub_add_cancel ((↑(ρ₀ g) : Matrix (Fin d) (Fin d) k).mulVec u)
      ((↑(ρ g) : Matrix (Fin d) (Fin d) k).mulVec u)]
    refine Submodule.add_mem _ (Submodule.mem_sup_left ?_) (Submodule.mem_sup_right (hU g u hu))
    intro a ha
    rw [Pi.sub_apply, key g i u huB a]
    split_ifs with h
    · exact sub_self _
    · rw [hinv (i + 1) g u (hblkle huB) a (by omega), sub_zero]
  rcases hmax i _ hU'inv le_sup_left (sup_le hlow (hUle.trans hblkle)) with h | h
  · left
    rw [eq_bot_iff]
    intro v hv
    rw [Submodule.mem_bot]
    have hv' : v ∈ low k c i := by
      rw [← h]
      exact Submodule.mem_sup_right hv
    exact hdisj v (hUle hv) hv'
  · right
    apply le_antisymm hUle
    intro v hv
    have hv' : v ∈ low k c i ⊔ U := by
      rw [h]
      exact hblkle hv
    obtain ⟨w, hw, u, hu, rfl⟩ := Submodule.mem_sup.mp hv'
    have hwB : w ∈ blk k c i := by
      have := Submodule.sub_mem _ hv (hUle hu)
      simpa using this
    rw [hdisj w hwB hw, zero_add]
    exact hu

end UpperTheory.Gal.Int.Geo
