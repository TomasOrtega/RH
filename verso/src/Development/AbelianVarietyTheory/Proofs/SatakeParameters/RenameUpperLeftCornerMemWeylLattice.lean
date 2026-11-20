import Mathlib
import Formalism.GradedWeylDivisibility.DualWeylDominanceOf
import Formalism.SatakeDualWeyl.KpqSubgroupCompact
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas

open MvPolynomial Formalism.GradedWeylDivisibility

namespace GlobalTheory

namespace WeylRankEmbed

variable (R : Type) [CommRing R] {a b : ℕ} (hab : a ≤ b)

abbrev corner : Fin a × Fin a → Fin b × Fin b :=
  fun v => (Fin.castLE hab v.1, Fin.castLE hab v.2)

/- English proof (translation)
Unfold `lpMinor`. Rewrite using `[AlgHom.map_det]`. Use `congr 1`. Use extensionality with `p q : 2`. Simplify using `[corner]`.
-/
theorem rename_lpMinor (s : ℕ) (h1 : s ≤ a) (h2 : s ≤ b) :
    rename (corner hab) (lpMinor R s h1 h1) = lpMinor R s h2 h2 := by
  unfold lpMinor
  rw [AlgHom.map_det]
  congr 1
  ext p q : 2
  simp [corner]

/- English proof (translation)
Unfold `hw`. Rewrite using `[map_prod]`. Use `symm`. Use `(Finset.prod_of_injOn (Fin.castLE hab) ((Fin.castLE_injective hab).injOn) (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_).symm` and prove the remaining obligations. Introduce `j _ hj`.

Establish `hja : ¬ (j : ℕ) < a`. Introduce `hlt`. Conclude with `hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩`. Rewrite using `[h j, dif_neg hja]`. Simplify using the standard rewrite rules.

Introduce `i _`. Rewrite using `[map_pow, rename_lpMinor R hab _ _ (by have := i.2; omega)]`. Establish `e1 : ν' (Fin.castLE hab i) = ν i`. Rewrite using `[h, dif_pos (by simp)]`. Both sides reduce to the same expression.

Establish `e2 : nuNext ν' (Fin.castLE hab i) = nuNext ν i`. Unfold `nuNext`. Distinguish the cases in `h1 : (i : ℕ) + 1 < a`. Rewrite using `[dif_pos h1, dif_pos (by simp; omega), h, dif_pos (by simpa using h1)]`. Both sides reduce to the same expression.

Rewrite using `[dif_neg h1] split_ifs with h2`. Rewrite using `[h, dif_neg (by simpa using h1)]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Both sides reduce to the same expression.
-/
theorem rename_hw (ν : Fin a → ℕ) (ν' : Fin b → ℕ)
    (h : ∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) :
    rename (corner hab) (hw R le_rfl ν) = hw R le_rfl ν' := by
  unfold hw
  rw [map_prod]
  symm
  refine (Finset.prod_of_injOn (Fin.castLE hab) ((Fin.castLE_injective hab).injOn)
    (fun _ _ => Finset.mem_coe.2 (Finset.mem_univ _)) ?_ ?_).symm
  · intro j _ hj
    have hja : ¬ (j : ℕ) < a := by
      intro hlt
      exact hj ⟨⟨j, hlt⟩, by simp, by ext; simp⟩
    rw [h j, dif_neg hja]
    simp
  · intro i _
    rw [map_pow, rename_lpMinor R hab _ _ (by have := i.2; omega)]
    have e1 : ν' (Fin.castLE hab i) = ν i := by
      rw [h, dif_pos (by simp)]
      rfl
    have e2 : nuNext ν' (Fin.castLE hab i) = nuNext ν i := by
      unfold nuNext
      by_cases h1 : (i : ℕ) + 1 < a
      · rw [dif_pos h1, dif_pos (by simp; omega), h, dif_pos (by simpa using h1)]
        rfl
      · rw [dif_neg h1]
        split_ifs with h2
        · rw [h, dif_neg (by simpa using h1)]
        · rfl
    rw [e1, e2]
    rfl

/- English proof (translation)
Establish `key : (Polynomial.mapAlgHom (rename (R` using `R) (corner hab))).comp (rowGen R x y) = (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `v`. Distinguish the cases in `hv : v.1 = y`. Simplify using `[rowGen, hv, corner]`.

Establish `hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y` using `fun e => hv (Fin.castLE_injective hab e)`. Simplify using `[rowGen, hv, corner]`. Establish `h2` using `congrArg (fun φ => (φ f).coeff k) key`. Simplify `h2` using `[rowDiv, Polynomial.coeff_map]`.
-/
theorem rename_rowDiv (x y : Fin a) (k : ℕ) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (rowDiv R x y k f) =
      rowDiv R (Fin.castLE hab x) (Fin.castLE hab y) k (rename (corner hab) f) := by
  have key : (Polynomial.mapAlgHom (rename (R := R) (corner hab))).comp (rowGen R x y) =
      (rowGen R (Fin.castLE hab x) (Fin.castLE hab y)).comp (rename (corner hab)) := by
    apply MvPolynomial.algHom_ext
    intro v
    by_cases hv : v.1 = y
    · simp [rowGen, hv, corner]
    · have hv' : Fin.castLE hab v.1 ≠ Fin.castLE hab y := fun e => hv (Fin.castLE_injective hab e)
      simp [rowGen, hv, corner]
  have h2 := congrArg (fun φ => (φ f).coeff k) key
  simpa [rowDiv, Polynomial.coeff_map] using h2

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => rfl`. Consider the case `cons x w ih`. Simplify using `only [applyWord, List.foldr_cons, List.map_cons] at ih ⊢`. Rewrite using `[rename_rowDiv, ih]`.
-/
theorem rename_applyWord (w : List (Fin a × Fin a × ℕ)) (f : MvPolynomial (Fin a × Fin a) R) :
    rename (corner hab) (applyWord R w f) =
      applyWord R (w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2))
        (rename (corner hab) f) := by
  induction w with
  | nil => rfl
  | cons x w ih =>
    simp only [applyWord, List.foldr_cons, List.map_cons] at ih ⊢
    rw [rename_rowDiv, ih]

end WeylRankEmbed

/- English proof (translation)
Introduce `R _ a b hab ν ν' h f hf`. Express the relevant statement in the definitionally equal form `rename (WeylRankEmbed.corner hab) f ∈ _`. Unfold `weyl at hf`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨w, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2), ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[WeylRankEmbed.rename_applyWord, WeylRankEmbed.rename_hw R hab ν ν' h]`. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [map_add]`. Conclude with `add_mem hx hy`. Consider the case `smul c x _ hx => rw [map_smul]`. Conclude with `Submodule.smul_mem _ _ hx`.
-/
theorem weyl_rename_castLE_mem :
    ∀ (R : Type) [CommRing R] (a b : ℕ) (hab : a ≤ b) (ν : Fin a → ℕ) (ν' : Fin b → ℕ), (∀ j : Fin b, ν' j = if h : (j : ℕ) < a then ν ⟨j, h⟩ else 0) → ∀ f ∈ Formalism.GradedWeylDivisibility.weyl R a a le_rfl ν, MvPolynomial.rename (fun v : Fin a × Fin a => ((Fin.castLE hab v.1, Fin.castLE hab v.2) : Fin b × Fin b)) f ∈ Formalism.GradedWeylDivisibility.weyl R b b le_rfl ν' := by
  intro R _ a b hab ν ν' h f hf
  change rename (WeylRankEmbed.corner hab) f ∈ _
  unfold weyl at hf
  induction hf using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨w, rfl⟩ := hx
    refine Submodule.subset_span ⟨w.map fun x => (Fin.castLE hab x.1, Fin.castLE hab x.2.1, x.2.2), ?_⟩
    simp only
    rw [WeylRankEmbed.rename_applyWord, WeylRankEmbed.rename_hw R hab ν ν' h]
  | zero => simp
  | add x y _ _ hx hy => rw [map_add]; exact add_mem hx hy
  | smul c x _ hx => rw [map_smul]; exact Submodule.smul_mem _ _ hx

end GlobalTheory
