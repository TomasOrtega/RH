import Formalism.LocalToGlobal.Columns.LastRowColLevSym
import Formalism.LocalToGlobal.Columns.OcbLevIsSym

open NumberField IsDedekindDomain Module Matrix

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV Formalism.L2.Ker

section FE

variable {X : Fields} {Pr : Primes X} {R : Ranks}

/- English proof (translation)
Rewrite `hM` using `[mem_HPar_iff hr ht hn]`. Take `⟨hB, hS⟩` from `hM`. Rewrite `hS` using `[mem_HPsymF_iff hkrS]`. Take `⟨s1, s2, s3⟩` from `hS`. Establish `hv` using `upper_block_val_submatrix hr (blockTri_blkOf_le r t hB)`.

Rewrite `hB` using `[mem_blockTri]`. Establish `hkn : k < n` using `by omega`. Establish `he : Loc.eN κ n k = Pi.single (⟨k, hkn⟩ : Fin n) 1`. Use function extensionality and compare the values at `l`. Simplify using `only [Loc.eN, Pi.single_apply, Fin.ext_iff]`.

Rewrite using `[he, Matrix.mulVec_single_one]`. Use function extensionality and compare the values at `i`. Simplify using `only [Matrix.col_apply, Pi.single_apply]`. Distinguish the cases in `hir : (i : ℕ) < r`. Establish `key : ∀ a b : Fin r, ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b = (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr a) (Fin.castLE hr b)`.

Introduce `a b`. Rewrite using `[hv]`. Both sides reduce to the same expression. Establish `hk' : (⟨k, hkn⟩ : Fin n) = Fin.castLE hr ⟨k, hkr⟩` using `Fin.ext rfl`. Rewrite using `[hk']`.

Distinguish the cases in `hik : (i : ℕ) = k`. Establish `hi2 : i = Fin.castLE hr ⟨k, hkr⟩` using `Fin.ext hik`. Rewrite using `[if_pos hi2, hi2, ← key]`. Conclude with `s2 _`. Establish `hi' : i = Fin.castLE hr ⟨i, hir⟩` using `Fin.ext rfl`.

Rewrite using `[if_neg (fun h => hik (by rw [h]; rfl)), hi', ← key]`. Distinguish the cases in `hrS : rS = 0`. Break down `Nat.lt_or_gt_of_ne hik with h | h` into its components or cases. Conclude with `s3 _ _ h (by simp [hrS])`. Apply the tactic sequence `exact s1 _ _ (by simp only [symIdx, Fin.val_mk, hrS]; split_ifs <;> omega)`.

Apply the tactic sequence `exact s1 _ _ (by simp only [symIdx, Fin.val_mk]; split_ifs <;> omega)`. Rewrite using `[if_neg (fun h => hir (by rw [h]; exact hkr))]`. Conclude with `hB _ _ (by`. Simplify using `only [blkOf, Fin.val_mk, if_pos hkr, if_neg hir]`. Conclude with `Nat.succ_pos _)`.
-/
private theorem mulVec_eN_eq_of_mem_HPar {κ : Type} [CommRing κ] {n r k rS t s : ℕ} (hr : r ≤ n) (ht : 0 < t)
    (hn : n = r + s * t) (hkr : k < r) (hkrS : k + rS ≤ r) (M : GL (Fin n) κ)
    (hM : M ∈ HPar n κ hr (List.replicate s t) (HPsymF κ r k rS)) :
    (M : Matrix (Fin n) (Fin n) κ) *ᵥ Loc.eN κ n k = Loc.eN κ n k := by
  rw [mem_HPar_iff hr ht hn] at hM
  obtain ⟨hB, hS⟩ := hM
  rw [mem_HPsymF_iff hkrS] at hS
  obtain ⟨s1, s2, s3⟩ := hS
  have hv := upper_block_val_submatrix hr (blockTri_blkOf_le r t hB)
  rw [mem_blockTri] at hB
  have hkn : k < n := by omega
  have he : Loc.eN κ n k = Pi.single (⟨k, hkn⟩ : Fin n) 1 := by
    funext l
    simp only [Loc.eN, Pi.single_apply, Fin.ext_iff]
  rw [he, Matrix.mulVec_single_one]
  funext i
  simp only [Matrix.col_apply, Pi.single_apply]
  by_cases hir : (i : ℕ) < r
  · have key : ∀ a b : Fin r, ((upperLeftBlock hr M : GL (Fin r) κ) : Matrix (Fin r) (Fin r) κ) a b =
        (M : Matrix (Fin n) (Fin n) κ) (Fin.castLE hr a) (Fin.castLE hr b) := by
      intro a b
      rw [hv]
      rfl
    have hk' : (⟨k, hkn⟩ : Fin n) = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext rfl
    rw [hk']
    by_cases hik : (i : ℕ) = k
    · have hi2 : i = Fin.castLE hr ⟨k, hkr⟩ := Fin.ext hik
      rw [if_pos hi2, hi2, ← key]
      exact s2 _
    · have hi' : i = Fin.castLE hr ⟨i, hir⟩ := Fin.ext rfl
      rw [if_neg (fun h => hik (by rw [h]; rfl)), hi', ← key]
      by_cases hrS : rS = 0
      · rcases Nat.lt_or_gt_of_ne hik with h | h
        · exact s3 _ _ h (by simp [hrS])
        · exact s1 _ _ (by simp only [symIdx, Fin.val_mk, hrS]; split_ifs <;> omega)
      · exact s1 _ _ (by simp only [symIdx, Fin.val_mk]; split_ifs <;> omega)
  · rw [if_neg (fun h => hir (by rw [h]; exact hkr))]
    exact hB _ _ (by
      simp only [blkOf, Fin.val_mk, if_pos hkr, if_neg hir]
      exact Nat.succ_pos _)

/- English proof (translation)
Introduce `h hh w`. Establish `hw : h w ∈ (colLevSym Ch (m2 + 1) w).H` using `(Subgroup.mem_pi _).mp hh w (Set.mem_univ _)`. Establish `e0 : ¬ (m2 + 1 = 0)` using `by omega`. Establish `e1 : ¬ (m2 + 1 + 1 < R.m)` using `by omega`. Establish `e2 : m2 + 1 + 1 = R.m` using `by omega`.

Unfold `colLevSym at hw`. Rewrite `hw` using `[if_neg e0, dif_neg e1, dif_pos e2]`. Conclude with `mulVec_eN_eq_of_mem_HPar _ (by have := R.rank_add_five_le; omega) (by show R.k + (m2 + 1) * (R.t + 1) = R.k + R.m - 1 + (m2 + 1) * R.t`. Rewrite using `[hm, Nat.mul_succ]`. Use the proof step `omega)`.

Use the proof step `(by show R.k < R.k + R.m - 1`. Use `R.two_le_m` as an intermediate fact. Use the proof step `omega)`. Use the proof step `(by show R.k + (R.m / 2 - 1) ≤ R.k + R.m - 1 omega) _ hw`.
-/
theorem fixE_colLevSym (Ch : Chars X Pr R.m) {m2 : ℕ} (hm : R.m = m2 + 2) : FixE (R := R) (colLevSym Ch) m2 := by
  intro h hh w
  have hw : h w ∈ (colLevSym Ch (m2 + 1) w).H := (Subgroup.mem_pi _).mp hh w (Set.mem_univ _)
  have e0 : ¬ (m2 + 1 = 0) := by omega
  have e1 : ¬ (m2 + 1 + 1 < R.m) := by omega
  have e2 : m2 + 1 + 1 = R.m := by omega
  unfold colLevSym at hw
  rw [if_neg e0, dif_neg e1, dif_pos e2] at hw
  exact mulVec_eN_eq_of_mem_HPar _ (by have := R.rank_add_five_le; omega)
    (by
      show R.k + (m2 + 1) * (R.t + 1) = R.k + R.m - 1 + (m2 + 1) * R.t
      rw [hm, Nat.mul_succ]
      omega)
    (by
      show R.k < R.k + R.m - 1
      have := R.two_le_m
      omega)
    (by
      show R.k + (R.m / 2 - 1) ≤ R.k + R.m - 1
      omega) _ hw

end FE

end Formalism.L2.Col
