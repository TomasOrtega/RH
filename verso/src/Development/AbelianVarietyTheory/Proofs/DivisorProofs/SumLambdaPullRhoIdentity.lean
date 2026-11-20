import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.TranslationInv
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PullFullL
open Matrix MeasureTheory Set Filter Topology
open GlobalTheory.IndefiniteRowSideFullHecke.SiegelReframe GlobalTheory.TorsionForm GlobalTheory.TorsionForm.OneVec
open scoped Real ContDiff

set_option autoImplicit false

namespace GlobalTheory.TorsionForm.OneVec.Reassemble

/- English proof (translation)
Use extensionality with `i`. Simplify using `[basePart, join, Fin.castAdd_inj]`. Introduce `x hx h`. Conclude with `absurd h (by simp [Fin.ext_iff]; omega)`.
-/
theorem basePart_join {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) :
    basePart (join S Z) = S := by
  ext i; simp [basePart, join, Fin.castAdd_inj]
  intro x hx h
  exact absurd h (by simp [Fin.ext_iff]; omega)

/- English proof (translation)
Use extensionality with `i`. Simplify using `[fibrePart, join]`. Introduce `x hx h`. Conclude with `absurd h (by simp [Fin.ext_iff]; omega)`.
-/
theorem fibrePart_join {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) :
    fibrePart (join S Z) = Z := by
  ext i; simp [fibrePart, join]
  intro x hx h
  exact absurd h (by simp [Fin.ext_iff]; omega)

/- English proof (translation)
Use extensionality with `x`. Simplify using `only [join, basePart, fibrePart, Finset.mem_union, Finset.mem_map, Finset.mem_filter, Finset.mem_univ, true_and, Fin.castAddEmb_apply, Fin.natAddEmb_apply]`. Use `Fin.addCases (fun i => ?_) (fun c => ?_) x` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `(⟨j, hj, he⟩ | ⟨j, hj, he⟩)`.

Rewrite using `[← he]` and apply the resulting hypothesis. Conclude with `absurd he (by simp [Fin.ext_iff]; omega)`. Introduce `h`. Conclude with `Or.inl ⟨i, h, rfl⟩`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `(⟨j, hj, he⟩ | ⟨j, hj, he⟩)`. Conclude with `absurd he (by simp [Fin.ext_iff]; omega)`. Rewrite using `[← he]` and apply the resulting hypothesis. Introduce `h`. Conclude with `Or.inr ⟨c, h, rfl⟩`.
-/
theorem join_parts {m g : ℕ} (U : Finset (Fin (m + g))) :
    join (basePart U) (fibrePart U) = U := by
  ext x; simp only [join, basePart, fibrePart, Finset.mem_union, Finset.mem_map, Finset.mem_filter,
    Finset.mem_univ, true_and, Fin.castAddEmb_apply, Fin.natAddEmb_apply]
  refine Fin.addCases (fun i => ?_) (fun c => ?_) x
  · constructor
    · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
      · rwa [← he]
      · exact absurd he (by simp [Fin.ext_iff]; omega)
    · intro h; exact Or.inl ⟨i, h, rfl⟩
  · constructor
    · rintro (⟨j, hj, he⟩ | ⟨j, hj, he⟩)
      · exact absurd he (by simp [Fin.ext_iff]; omega)
      · rwa [← he]
    · intro h; exact Or.inr ⟨c, h, rfl⟩

/- English proof (translation)
Simplify using `[join, Fin.castAdd_inj]`. Introduce `x hx h`. Conclude with `absurd h (by simp [Fin.ext_iff]; omega)`.
-/
theorem mem_join_castAdd {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) (i : Fin m) :
    Fin.castAdd g i ∈ join S Z ↔ i ∈ S := by
  simp [join, Fin.castAdd_inj]
  intro x hx h
  exact absurd h (by simp [Fin.ext_iff]; omega)

/- English proof (translation)
Simplify using `[join, Fin.natAdd_inj]`. Introduce `x hx h`. Conclude with `absurd h (by simp [Fin.ext_iff]; omega)`.
-/
theorem mem_join_natAdd {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) (c : Fin g) :
    Fin.natAdd m c ∈ join S Z ↔ c ∈ Z := by
  simp [join, Fin.natAdd_inj]
  intro x hx h
  exact absurd h (by simp [Fin.ext_iff]; omega)

/- English proof (translation)
Use extensionality with `x`. Use `Fin.addCases (fun j => ?_) (fun c => ?_) x` and prove the remaining obligations. Rewrite using `[Finset.mem_erase, mem_join_castAdd, mem_join_castAdd, Finset.mem_erase, Ne, Fin.castAdd_inj]`. Rewrite using `[Finset.mem_erase, mem_join_natAdd, mem_join_natAdd]`. Simplify using `[Fin.ext_iff]`.

Introduce `_`. Use linear arithmetic over natural numbers and integers.
-/
theorem erase_join_castAdd {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) (i : Fin m) :
    (join S Z).erase (Fin.castAdd g i) = join (S.erase i) Z := by
  ext x
  refine Fin.addCases (fun j => ?_) (fun c => ?_) x
  · rw [Finset.mem_erase, mem_join_castAdd, mem_join_castAdd, Finset.mem_erase, Ne, Fin.castAdd_inj]
  · rw [Finset.mem_erase, mem_join_natAdd, mem_join_natAdd]
    simp [Fin.ext_iff]; intro _; omega

/- English proof (translation)
Unfold `sgn`. Establish `h : (join S Z).filter (· < Fin.castAdd g i) = (S.filter (· < i)).map (Fin.castAddEmb g)`. Use extensionality with `x`. Use `Fin.addCases (fun j => ?_) (fun c => ?_) x` and prove the remaining obligations. Rewrite using `[Finset.mem_filter, mem_join_castAdd, Finset.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h2⟩`. Conclude with `⟨j, Finset.mem_filter.2 ⟨h1, Fin.lt_def.2 (by have := Fin.lt_def.1 h2; simpa only [Fin.coe_castAdd] using this)⟩, rfl⟩`. Introduce and unpack `⟨k, hk, he⟩`. Simplify using `only [Fin.castAddEmb_apply, Fin.castAdd_inj] at he`.

Substitute `he` using the available equality. Conclude with `⟨(Finset.mem_filter.1 hk).1, Fin.lt_def.2 (by have := Fin.lt_def.1 (Finset.mem_filter.1 hk).2; simpa only [Fin.coe_castAdd] using this)⟩`. Rewrite using `[Finset.mem_filter, mem_join_natAdd, Finset.mem_map]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨_, h2⟩`.

It suffices to derive a contradiction. Simplify using `[Fin.lt_def] at h2`. Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨k, _, he⟩`. It suffices to derive a contradiction.

Simplify using `[Fin.ext_iff] at he`. Use linear arithmetic over natural numbers and integers. Rewrite using `[h, Finset.card_map]`.
-/
theorem sgn_join_castAdd {m g : ℕ} (S : Finset (Fin m)) (Z : Finset (Fin g)) (i : Fin m) :
    sgn (Fin.castAdd g i) (join S Z) = sgn i S := by
  unfold sgn
  have h : (join S Z).filter (· < Fin.castAdd g i) = (S.filter (· < i)).map (Fin.castAddEmb g) := by
    ext x
    refine Fin.addCases (fun j => ?_) (fun c => ?_) x
    · rw [Finset.mem_filter, mem_join_castAdd, Finset.mem_map]
      constructor
      · rintro ⟨h1, h2⟩
        exact ⟨j, Finset.mem_filter.2 ⟨h1, Fin.lt_def.2 (by have := Fin.lt_def.1 h2; simpa only [Fin.coe_castAdd] using this)⟩, rfl⟩
      · rintro ⟨k, hk, he⟩
        simp only [Fin.castAddEmb_apply, Fin.castAdd_inj] at he
        subst he
        exact ⟨(Finset.mem_filter.1 hk).1, Fin.lt_def.2 (by have := Fin.lt_def.1 (Finset.mem_filter.1 hk).2; simpa only [Fin.coe_castAdd] using this)⟩
    · rw [Finset.mem_filter, mem_join_natAdd, Finset.mem_map]
      constructor
      · rintro ⟨_, h2⟩; exfalso; simp [Fin.lt_def] at h2; omega
      · rintro ⟨k, _, he⟩; exfalso; simp [Fin.ext_iff] at he; omega
  rw [h, Finset.card_map]

/- English proof (translation)
Simplify using `only [wedge, mem_join_castAdd, sgn_join_castAdd, erase_join_castAdd]`.
-/
theorem wedge_castAdd_join {m g : ℕ} (i : Fin m) (x : Ext (m + g)) (S : Finset (Fin m))
    (Z : Finset (Fin g)) :
    wedge (Fin.castAdd g i) x (join S Z) = if i ∈ S then sgn i S * x (join (S.erase i) Z) else 0 := by
  simp only [wedge, mem_join_castAdd, sgn_join_castAdd, erase_join_castAdd]

/- English proof (translation)
Use function extensionality and compare the values at `U`. Use `show pullFull a (rhoL (n := n) S w) U = _`. Establish `hy : (fun S' : Finset (Fin (n + n)) => rhoL (n` using `n) S w (join S' (fibrePart U))) = fun S' => if S' = ∅ then w (join S (fibrePart U)) else 0 := by`. Use function extensionality and compare the values at `S'`. Use `show (if basePart (join S' (fibrePart U)) = ∅ then w (join S (fibrePart (join S' (fibrePart U)))) else 0) = _`.

Rewrite using `[basePart_join, fibrePart_join]`. Unfold `pullFull`. Rewrite using `[hy]`. Unfold `pullBase`. Apply the tactic sequence `split_ifs <;> simp_all`.
-/
theorem pull_rho {n g : ℕ} (a : Fin n → ℂ) (w : Ext (1 + 1 + g)) (S : Finset (Fin (1 + 1))) :
    pullFullL a (rhoL (n := n) S w) = fun U => if basePart U = ∅ then w (join S (fibrePart U)) else 0 := by
  funext U
  show pullFull a (rhoL (n := n) S w) U = _
  have hy : (fun S' : Finset (Fin (n + n)) => rhoL (n := n) S w (join S' (fibrePart U))) =
      fun S' => if S' = ∅ then w (join S (fibrePart U)) else 0 := by
    funext S'
    show (if basePart (join S' (fibrePart U)) = ∅ then w (join S (fibrePart (join S' (fibrePart U)))) else 0) = _
    rw [basePart_join, fibrePart_join]
  unfold pullFull
  rw [hy]
  unfold pullBase
  split_ifs <;> simp_all

/- English proof (translation)
Apply the tactic sequence `unfold lamL; split_ifs <;> rfl`.
-/
theorem lamL_apply {g : ℕ} (S : Finset (Fin (1 + 1))) (x : Ext (1 + 1 + g)) (U : Finset (Fin (1 + 1 + g))) :
    lamL S x U = (if Fin.castAdd 1 (0 : Fin 1) ∈ S then wedge (Fin.castAdd g (Fin.castAdd 1 (0 : Fin 1))) else id)
      ((if Fin.natAdd 1 (0 : Fin 1) ∈ S then wedge (Fin.castAdd g (Fin.natAdd 1 (0 : Fin 1))) else id) x) U := by
  unfold lamL; split_ifs <;> rfl

/- English proof (translation)
Introduce `n g a w`. Simplify using `only [pull_rho]`. Use function extensionality and compare the values at `U`. Rewrite using `[Finset.sum_apply]`. Establish `huniv : (Finset.univ : Finset (Finset (Fin (1 + 1)))) = {∅, {0}, {1}, {0, 1}}` using `by decide`.

Rewrite using `[huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_singleton]`. Simplify using `only [lamL_apply]`. Rewrite using `[← join_parts U]`. Generalize the expression as in `basePart U = B`. Generalize the expression as in `fibrePart U = Z`.

Establish `hB : B = ∅ ∨ B = {0} ∨ B = {1} ∨ B = {0, 1}` using `by revert B; decide`. Apply the tactic sequence `rcases hB with rfl | rfl | rfl | rfl <;>`. Simplify using `(config := {decide := true}) [wedge_castAdd_join, basePart_join, fibrePart_join, sgn]`.
-/
theorem sum_lam_pull_rho : ∀ {n g : ℕ} (a : Fin n → ℂ) (w : Ext (1 + 1 + g)),
    ∑ S : Finset (Fin (1 + 1)), lamL S (pullFullL a (rhoL (n := n) S w)) = w := by
  intro n g a w
  simp only [pull_rho]
  funext U
  rw [Finset.sum_apply]
  have huniv : (Finset.univ : Finset (Finset (Fin (1 + 1)))) = {∅, {0}, {1}, {0, 1}} := by decide
  rw [huniv, Finset.sum_insert (by decide), Finset.sum_insert (by decide), Finset.sum_insert (by decide),
    Finset.sum_singleton]
  simp only [lamL_apply]
  rw [← join_parts U]
  generalize basePart U = B
  generalize fibrePart U = Z
  have hB : B = ∅ ∨ B = {0} ∨ B = {1} ∨ B = {0, 1} := by revert B; decide
  rcases hB with rfl | rfl | rfl | rfl <;>
    simp (config := {decide := true}) [wedge_castAdd_join, basePart_join, fibrePart_join, sgn]

end GlobalTheory.TorsionForm.OneVec.Reassemble
