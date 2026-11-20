import Mathlib
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.SingularValueFrame
import Development.AbelianVarietyTheory.BlockTheory.TorsionBlocks.CartanCoshPower
import Formalism.LocalRingCardinality.SpanPowerMembership.SignSplitEquivInl

namespace GlobalTheory.CartanDiagSigns

/- English proof (translation)
Use `set φ := Matrix.reindexAlgEquiv ℂ ℂ e with hφ`. Establish `h1 : ∀ M : Matrix m m ℂ, Matrix.reindex e e M = φ M` using `fun M => rfl`. Establish `hc : Continuous φ`. Express the relevant statement in the definitionally equal form `Continuous (fun M : Matrix m m ℂ => Matrix.reindex e e M)`. Conclude with `(continuous_id.matrix_reindex e e)`.

Establish `hc' : Continuous φ.symm`. Express the relevant statement in the definitionally equal form `Continuous (fun M : Matrix n n ℂ => Matrix.reindex e.symm e.symm M)`. Conclude with `(continuous_id.matrix_reindex e.symm e.symm)`. Rewrite using `[h1, h1, NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]`. Simplify using `only`.

Rewrite using `[Function.LeftInverse.map_tsum (g := φ) _ hc hc' (fun x => φ.symm_apply_apply x)]`. Use `congr 1`. Use function extensionality and compare the values at `k`. Rewrite using `[map_smul, map_pow]`.
-/
theorem exp_reindex {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) (A : Matrix m m ℂ) :
    NormedSpace.exp (Matrix.reindex e e A) = Matrix.reindex e e (NormedSpace.exp A) := by
  set φ := Matrix.reindexAlgEquiv ℂ ℂ e with hφ
  have h1 : ∀ M : Matrix m m ℂ, Matrix.reindex e e M = φ M := fun M => rfl
  have hc : Continuous φ := by
    change Continuous (fun M : Matrix m m ℂ => Matrix.reindex e e M)
    exact (continuous_id.matrix_reindex e e)
  have hc' : Continuous φ.symm := by
    change Continuous (fun M : Matrix n n ℂ => Matrix.reindex e.symm e.symm M)
    exact (continuous_id.matrix_reindex e.symm e.symm)
  rw [h1, h1, NormedSpace.exp_eq_tsum ℂ, NormedSpace.exp_eq_tsum ℂ]
  simp only
  rw [Function.LeftInverse.map_tsum (g := φ) _ hc hc' (fun x => φ.symm_apply_apply x)]
  congr 1
  funext k
  rw [map_smul, map_pow]

end GlobalTheory.CartanDiagSigns

namespace GlobalTheory.CartanDiagSigns
open Formalism.BasicNotions.Examples₂.CD

/- English proof (translation)
Use `(Equiv.symm_apply_eq (e0 ε)).mpr ?_` and prove the remaining obligations. Use `show a.1 = (Equiv.sumCompl fun i => ε i = true) (Sum.inl ((Fintype.equivFin {i // ε i = true}).symm (Fintype.equivFin {i // ε i = true} a)))`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem sign_split_symm_true {n : ℕ} (ε : Fin n → Bool) (a : {i // ε i = true}) :
    (e0 ε).symm a.1 = Sum.inl (Fintype.equivFin {i // ε i = true} a) := by
  refine (Equiv.symm_apply_eq (e0 ε)).mpr ?_
  show a.1 = (Equiv.sumCompl fun i => ε i = true)
    (Sum.inl ((Fintype.equivFin {i // ε i = true}).symm (Fintype.equivFin {i // ε i = true} a)))
  rw [Equiv.symm_apply_apply]
  rfl

/- English proof (translation)
Use `(Equiv.symm_apply_eq (e0 ε)).mpr ?_` and prove the remaining obligations. Use `show b.1 = (Equiv.sumCompl fun i => ε i = true) (Sum.inr ((Fintype.equivFin {i // ¬ ε i = true}).symm (Fintype.equivFin {i // ¬ ε i = true} ⟨b.1, by simp [b.2]⟩)))`. Rewrite using `[Equiv.symm_apply_apply]`. Both sides reduce to the same expression.
-/
theorem sign_split_symm_false {n : ℕ} (ε : Fin n → Bool) (b : {i // ε i = false}) :
    (e0 ε).symm b.1 = Sum.inr (Fintype.equivFin {i // ¬ ε i = true} ⟨b.1, by simp [b.2]⟩) := by
  refine (Equiv.symm_apply_eq (e0 ε)).mpr ?_
  show b.1 = (Equiv.sumCompl fun i => ε i = true)
    (Sum.inr ((Fintype.equivFin {i // ¬ ε i = true}).symm
      (Fintype.equivFin {i // ¬ ε i = true} ⟨b.1, by simp [b.2]⟩)))
  rw [Equiv.symm_apply_apply]
  rfl

/- English proof (translation)
Consider the cases of `x with`. Consider the case `inl a => simpa using sign_split_equiv_inl ε a`. Consider the case `inr b => simpa using sign_split_equiv_inr ε b`.
-/
theorem sign_split_eval {n : ℕ} (ε : Fin n → Bool) (x : Fin (nT ε) ⊕ Fin (nF ε)) :
    ε (e0 ε x) = x.elim (fun _ => true) (fun _ => false) := by
  cases x with
  | inl a => simpa using sign_split_equiv_inl ε a
  | inr b => simpa using sign_split_equiv_inr ε b

/- English proof (translation)
Establish `h : Matrix.reindex e e A = Matrix.reindexAlgEquiv ℂ ℂ e A` using `rfl`. Rewrite `hA`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Establish `hs : star (Matrix.reindex e e A) = Matrix.reindex e e (star A)`. Simplify using `[Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]`. Rewrite using `[hs]`.

Establish `h2 : Matrix.reindex e e (star A) = Matrix.reindexAlgEquiv ℂ ℂ e (star A)` using `rfl`. Rewrite using `[h, h2, ← map_mul, hA, map_one]`.
-/
theorem reindex_unitary {m n : Type} [Fintype m] [DecidableEq m] [Fintype n] [DecidableEq n]
    (e : m ≃ n) {A : Matrix m m ℂ} (hA : A ∈ Matrix.unitaryGroup m ℂ) :
    Matrix.reindex e e A ∈ Matrix.unitaryGroup n ℂ := by
  have h : Matrix.reindex e e A = Matrix.reindexAlgEquiv ℂ ℂ e A := rfl
  rw [Matrix.mem_unitaryGroup_iff] at hA ⊢
  have hs : star (Matrix.reindex e e A) = Matrix.reindex e e (star A) := by
    simp [Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix]
  rw [hs]
  have h2 : Matrix.reindex e e (star A) = Matrix.reindexAlgEquiv ℂ ℂ e (star A) := rfl
  rw [h, h2, ← map_mul, hA, map_one]

end GlobalTheory.CartanDiagSigns

namespace GlobalTheory.CartanDiagSigns
open Formalism.BasicNotions.Examples₂.CD

/- English proof (translation)
Introduce `n ε u`. Take `⟨k₁, hk₁, k₂, hk₂, hu⟩` from `GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.isCartan_cartanB u`. Use `set B := GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.cartanB u with hB`. Use `set P : Matrix (Fin (nT ε) ⊕ Fin (nF ε)) (Fin (nT ε) ⊕ Fin (nF ε)) ℂ := Formalism.MainNotions.SchurIrreducible.pOf B with hP`. Establish `hPapp : ∀ x y, P x y = Matrix.fromBlocks 0 B B.conjTranspose 0 x y` using `fun _ _ => rfl`.

Use `⟨Matrix.reindex (e0 ε) (e0 ε) P, ⟨⟨?herm, ?zeroP⟩, ?K⟩, ?off⟩` and prove the remaining obligations. Establish `hPh : P.conjTranspose = P`. Rewrite using `[Matrix.ext_iff.symm]`. Introduce `x y`. Rewrite using `[hPapp, Matrix.conjTranspose_apply, hPapp]`.

Apply the tactic sequence `cases x <;> cases y <;> simp`. Use `show (Matrix.reindex (e0 ε) (e0 ε) P).conjTranspose = Matrix.reindex (e0 ε) (e0 ε) P`. Rewrite using `[Matrix.reindex_apply, Matrix.conjTranspose_submatrix, hPh]`. Introduce `i j hij`. Rewrite using `[Matrix.reindex_apply, Matrix.submatrix_apply, hPapp]`.

Establish `hi` using `sign_split_eval ε ((e0 ε).symm i)`. Establish `hj` using `sign_split_eval ε ((e0 ε).symm j)`. Rewrite `hi`, `hj` using `[Equiv.apply_symm_apply]`. Apply the tactic sequence `rcases hx : (e0 ε).symm i with a | a <;> rcases hy : (e0 ε).symm j with b | b <;>`. Simplify the hypotheses and the goal together.

Use `⟨Matrix.reindex (e0 ε) (e0 ε) (Matrix.fromBlocks k₁ 0 0 k₂), 1, ⟨?_, ?_⟩, ⟨one_mem _, ?_⟩, ?_⟩` and prove the remaining obligations. Apply `reindex_unitary` to reduce the goal to its premises. Rewrite `hk₁`, `hk₂`, the goal using `[Matrix.mem_unitaryGroup_iff]`. Rewrite using `[Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]`. Simplify using `only [← Matrix.star_eq_conjTranspose, hk₁, hk₂, star_zero, mul_zero, zero_mul, add_zero, zero_add, Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.fromBlocks_one]`.

Introduce `i j hij`. Rewrite using `[Matrix.reindex_apply, Matrix.submatrix_apply]`. Establish `hi` using `sign_split_eval ε ((e0 ε).symm i)`. Establish `hj` using `sign_split_eval ε ((e0 ε).symm j)`. Rewrite `hi`, `hj` using `[Equiv.apply_symm_apply]`.

Apply the tactic sequence `rcases hx : (e0 ε).symm i with a | a <;> rcases hy : (e0 ε).symm j with b | b <;>`. Simplify the hypotheses and the goal together. Introduce `i j hij`. Establish `: i ≠ j` using `fun h => hij (h ▸ rfl)`. Simplify using `[Matrix.one_apply, this]`.

Rewrite using `[mul_one, exp_reindex, hu]`. Express the relevant statement in the definitionally equal form `Matrix.reindexAlgEquiv ℂ ℂ (e0 ε) (Matrix.fromBlocks k₁ 0 0 k₂ * NormedSpace.exp P) = _`. Rewrite using `[map_mul]`. Both sides reduce to the same expression. Use extensionality with `a b`.

Simplify using `only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.offBlock, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]`. Rewrite using `[sign_split_symm_true ε a, sign_split_symm_false ε b]`. Both sides reduce to the same expression.
-/
theorem cartan_reindex_diag : ∀ (n : ℕ) (ε : Fin n → Bool) (u : Formalism.BasicNotions.UpqT (Formalism.BasicNotions.Examples₂.CD.nT ε) (Formalism.BasicNotions.Examples₂.CD.nF ε)), ∃ X : Matrix (Fin n) (Fin n) ℂ, GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.IsCartan ε (Matrix.reindex (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.Examples₂.CD.e0 ε) (Formalism.BasicNotions.UpqT.mat u)) X ∧ GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.offBlock ε X = (GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.cartanB u).submatrix (Fintype.equivFin {i // ε i = true}) ((Equiv.subtypeEquivRight (fun i => by simp)).trans (Fintype.equivFin {i // ¬ ε i = true})) := by
  intro n ε u
  obtain ⟨k₁, hk₁, k₂, hk₂, hu⟩ := GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.isCartan_cartanB u
  set B := GlobalTheory.IndefiniteRowSideFullHecke.CartanCoshPower.cartanB u with hB
  set P : Matrix (Fin (nT ε) ⊕ Fin (nF ε)) (Fin (nT ε) ⊕ Fin (nF ε)) ℂ := Formalism.MainNotions.SchurIrreducible.pOf B with hP
  have hPapp : ∀ x y, P x y = Matrix.fromBlocks 0 B B.conjTranspose 0 x y := fun _ _ => rfl
  refine ⟨Matrix.reindex (e0 ε) (e0 ε) P, ⟨⟨?herm, ?zeroP⟩, ?K⟩, ?off⟩
  · have hPh : P.conjTranspose = P := by
      rw [Matrix.ext_iff.symm]
      intro x y
      rw [hPapp, Matrix.conjTranspose_apply, hPapp]
      cases x <;> cases y <;> simp
    show (Matrix.reindex (e0 ε) (e0 ε) P).conjTranspose = Matrix.reindex (e0 ε) (e0 ε) P
    rw [Matrix.reindex_apply, Matrix.conjTranspose_submatrix, hPh]
  · intro i j hij
    rw [Matrix.reindex_apply, Matrix.submatrix_apply, hPapp]
    have hi := sign_split_eval ε ((e0 ε).symm i)
    have hj := sign_split_eval ε ((e0 ε).symm j)
    rw [Equiv.apply_symm_apply] at hi hj
    rcases hx : (e0 ε).symm i with a | a <;> rcases hy : (e0 ε).symm j with b | b <;>
      simp_all
  · refine ⟨Matrix.reindex (e0 ε) (e0 ε) (Matrix.fromBlocks k₁ 0 0 k₂), 1, ⟨?_, ?_⟩, ⟨one_mem _, ?_⟩, ?_⟩
    · apply reindex_unitary
      rw [Matrix.mem_unitaryGroup_iff] at hk₁ hk₂ ⊢
      rw [Matrix.star_eq_conjTranspose, Matrix.fromBlocks_conjTranspose, Matrix.fromBlocks_multiply]
      simp only [← Matrix.star_eq_conjTranspose, hk₁, hk₂, star_zero, mul_zero, zero_mul, add_zero, zero_add,
        Matrix.conjTranspose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.fromBlocks_one]
    · intro i j hij
      rw [Matrix.reindex_apply, Matrix.submatrix_apply]
      have hi := sign_split_eval ε ((e0 ε).symm i)
      have hj := sign_split_eval ε ((e0 ε).symm j)
      rw [Equiv.apply_symm_apply] at hi hj
      rcases hx : (e0 ε).symm i with a | a <;> rcases hy : (e0 ε).symm j with b | b <;>
        simp_all
    · intro i j hij
      have : i ≠ j := fun h => hij (h ▸ rfl)
      simp [Matrix.one_apply, this]
    · rw [mul_one, exp_reindex, hu]
      change Matrix.reindexAlgEquiv ℂ ℂ (e0 ε) (Matrix.fromBlocks k₁ 0 0 k₂ * NormedSpace.exp P) = _
      rw [map_mul]
      rfl
  · ext a b
    simp only [GlobalTheory.IndefiniteRowSideFullHecke.RealRankSubgroupMembership.offBlock, Matrix.of_apply, Matrix.reindex_apply, Matrix.submatrix_apply]
    rw [sign_split_symm_true ε a, sign_split_symm_false ε b]
    rfl

end GlobalTheory.CartanDiagSigns
