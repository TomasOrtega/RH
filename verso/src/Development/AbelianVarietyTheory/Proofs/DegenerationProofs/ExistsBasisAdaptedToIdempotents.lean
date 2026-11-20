import Mathlib

open Module

namespace GlobalTheory.ZH

open Module in
/- English proof (translation)
Use extensionality with `i`. Establish `h` using `congrFun (congrFun (he d c) i) s`. Rewrite `h` using `[Matrix.mul_apply]`. Simplify using `only [Matrix.mulVec, dotProduct]`. Rewrite using `[h]`.

Use `split_ifs with hdc`. Substitute `hdc` using the available equality. Both sides reduce to the same expression. Both sides reduce to the same expression.
-/
private lemma mulVec_column_of_orthogonal_idempotents {R J C : Type} [CommRing R] [Fintype J]
    [DecidableEq C] (e : C → Matrix J J R)
    (he : ∀ c c', e c * e c' = if c = c' then e c else 0) (d c : C) (s : J) :
    (e d).mulVec (fun j => e c j s) = if d = c then (fun j => e c j s) else 0 := by
  ext i
  have h := congrFun (congrFun (he d c) i) s
  rw [Matrix.mul_apply] at h
  simp only [Matrix.mulVec, dotProduct]
  rw [h]
  split_ifs with hdc
  · subst hdc; rfl
  · rfl

open Module in

/- English proof (translation)
Introduce `O _ _ J C _ _ _ _ e he hsum`. Set `f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O)` to `(IsLocalRing.residue O).mapMatrix`. Set `E : C → Matrix J J (IsLocalRing.ResidueField O)` to `fun c => f (e c)`. Establish `hE : ∀ c c', E c * E c' = if c = c' then E c else 0`. Introduce `c c'`.

Simplify using `only [E, ← map_mul, he]`. Apply the tactic sequence `split_ifs <;> simp`. Establish `hEsum : ∑ c, E c = 1` using `by simp only [E, ← map_sum, hsum, map_one]`. Set `w : C → J → (J → IsLocalRing.ResidueField O)` to `fun c s j => E c j s`. Use `choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)`.

Use `haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)`. Set `W : (Σ c, T c) → (J → IsLocalRing.ResidueField O)` to `fun p => w p.1 (a p.1 p.2)`. Establish `hWli : LinearIndependent (IsLocalRing.ResidueField O) W`. Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg p`.

Take `⟨d, t⟩` from `p`. Establish `h1` using `congrArg (Matrix.mulVecLin (E d)) hg`. Simplify using `only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w, mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1`. Rewrite `h1` using `[Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)]`. Simplify using `only [if_pos rfl] at h1`.

Conclude with `Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t`. Establish `hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W)`. Rewrite using `[← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Establish `hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s`.

Use extensionality with `j`. Use `congrFun (congrFun hEsum j) s` as an intermediate fact. Simplify using `only [Matrix.sum_apply, Matrix.one_apply] at this`. Simplify using `[w, Finset.sum_apply, this, Pi.single_apply]`. Rewrite using `[hs]`.

Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Establish `h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c))`. Rewrite using `[hsp c]`. Conclude with `Submodule.subset_span ⟨s, rfl⟩`. Use `Submodule.span_mono ?_ h2` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, rfl⟩`. Conclude with `⟨⟨c, t⟩, rfl⟩`. Set `b` to `Basis.mk hWli hWsp`. Establish `hcard : Fintype.card J = Fintype.card (Σ c, T c)`. Rewrite using `[← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O), Module.finrank_eq_card_basis b]`.

Set `σ : J ≃ (Σ c, T c)` to `Fintype.equivOfCardEq hcard`. Set `M : Matrix J J O` to `Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)`. Establish `hdet : IsUnit M.det`. Rewrite using `[← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det, ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]`. Conclude with `hWli.comp σ σ.injective`.

Use `⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩` and prove the remaining obligations. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨s, rfl⟩`. Use `show (fun j => e c j s) ∈ Submodule.span O _`. Establish `hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s`.

Simplify using `using mulVec_column_of_orthogonal_idempotents e he c c s`. Establish `h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M`. Rewrite using `[Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]`. Establish `h4 : (fun j => e c j s) = ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Matrix.vecMul_eq_sum]`. Simplify using `only [← Matrix.mulVecLin_apply, map_sum, map_smul]`. Rewrite using `[h4]`. Use `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0` using `mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _`.

Rewrite using `[h5]`. Use `split_ifs with h`. Conclude with `Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩`. Conclude with `zero_mem _`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨i, -, rfl⟩`. Conclude with `Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩`.
-/
theorem _root_.GlobalTheory.ZH.exists_basis_adapted_to_idempotents :
    ∀ (O : Type) [CommRing O] [IsLocalRing O] (J C : Type) [Fintype J] [DecidableEq J] [Fintype C]
      [DecidableEq C] (e : C → Matrix J J O),
      (∀ c c', e c * e c' = if c = c' then e c else 0) → ∑ c, e c = 1 →
      ∃ (κ : J → C) (col : J → J),
        IsUnit (Matrix.det (Matrix.of fun i j => e (κ i) j (col i))) ∧
        ∀ c, Submodule.span O (Set.range fun i => fun j => e c j i) =
          Submodule.span O {v | ∃ i, κ i = c ∧ v = fun j => e c j (col i)} := by
  intro O _ _ J C _ _ _ _ e he hsum
  classical
  let f : Matrix J J O →+* Matrix J J (IsLocalRing.ResidueField O) :=
    (IsLocalRing.residue O).mapMatrix
  let E : C → Matrix J J (IsLocalRing.ResidueField O) := fun c => f (e c)
  have hE : ∀ c c', E c * E c' = if c = c' then E c else 0 := by
    intro c c'
    simp only [E, ← map_mul, he]
    split_ifs <;> simp
  have hEsum : ∑ c, E c = 1 := by simp only [E, ← map_sum, hsum, map_one]
  let w : C → J → (J → IsLocalRing.ResidueField O) := fun c s j => E c j s
  choose T a ha hsp hli using fun c => exists_linearIndependent' (IsLocalRing.ResidueField O) (w c)
  haveI : ∀ c, Fintype (T c) := fun c => Fintype.ofInjective (a c) (ha c)
  let W : (Σ c, T c) → (J → IsLocalRing.ResidueField O) := fun p => w p.1 (a p.1 p.2)
  have hWli : LinearIndependent (IsLocalRing.ResidueField O) W := by
    rw [Fintype.linearIndependent_iff]
    intro g hg p
    obtain ⟨d, t⟩ := p
    have h1 := congrArg (Matrix.mulVecLin (E d)) hg
    simp only [map_sum, map_smul, map_zero, Matrix.mulVecLin_apply, W, w,
      mulVec_column_of_orthogonal_idempotents E hE, Fintype.sum_sigma, smul_ite, smul_zero] at h1
    rw [Finset.sum_eq_single d (fun c _ hc => by simp [Ne.symm hc]) (by simp)] at h1
    simp only [if_pos rfl] at h1
    exact Fintype.linearIndependent_iff.mp (hli d) (fun t => g ⟨d, t⟩) h1 t
  have hWsp : ⊤ ≤ Submodule.span (IsLocalRing.ResidueField O) (Set.range W) := by
    rw [← (Pi.basisFun (IsLocalRing.ResidueField O) J).span_eq, Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    have hs : Pi.basisFun (IsLocalRing.ResidueField O) J s = ∑ c, w c s := by
      ext j
      have := congrFun (congrFun hEsum j) s
      simp only [Matrix.sum_apply, Matrix.one_apply] at this
      simp [w, Finset.sum_apply, this, Pi.single_apply]
    rw [hs]
    refine Submodule.sum_mem _ fun c _ => ?_
    have h2 : w c s ∈ Submodule.span (IsLocalRing.ResidueField O) (Set.range (w c ∘ a c)) := by
      rw [hsp c]; exact Submodule.subset_span ⟨s, rfl⟩
    refine Submodule.span_mono ?_ h2
    rintro _ ⟨t, rfl⟩
    exact ⟨⟨c, t⟩, rfl⟩
  let b := Basis.mk hWli hWsp
  have hcard : Fintype.card J = Fintype.card (Σ c, T c) := by
    rw [← Module.finrank_fintype_fun_eq_card (IsLocalRing.ResidueField O),
      Module.finrank_eq_card_basis b]
  let σ : J ≃ (Σ c, T c) := Fintype.equivOfCardEq hcard
  let M : Matrix J J O := Matrix.of fun i j => e (σ i).1 j (a (σ i).1 (σ i).2)
  have hdet : IsUnit M.det := by
    rw [← isUnit_map_iff (IsLocalRing.residue O), RingHom.map_det,
      ← Matrix.isUnit_iff_isUnit_det, ← Matrix.linearIndependent_rows_iff_isUnit]
    exact hWli.comp σ σ.injective
  refine ⟨fun i => (σ i).1, fun i => a (σ i).1 (σ i).2, hdet, fun c => le_antisymm ?_ ?_⟩
  · rw [Submodule.span_le]
    rintro _ ⟨s, rfl⟩
    show (fun j => e c j s) ∈ Submodule.span O _
    have hfix : (e c).mulVec (fun j => e c j s) = fun j => e c j s := by
      simpa using mulVec_column_of_orthogonal_idempotents e he c c s
    have h3 : (fun j => e c j s) = Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M := by
      rw [Matrix.vecMul_vecMul, Matrix.nonsing_inv_mul _ hdet, Matrix.vecMul_one]
    have h4 : (fun j => e c j s) =
        ∑ i, (Matrix.vecMul (fun j => e c j s) M⁻¹) i • (e c).mulVec (M i) := by
      calc (fun j => e c j s) = (e c).mulVec (fun j => e c j s) := hfix.symm
        _ = (e c).mulVec (Matrix.vecMul (Matrix.vecMul (fun j => e c j s) M⁻¹) M) := by rw [← h3]
        _ = _ := by
          rw [Matrix.vecMul_eq_sum]
          simp only [← Matrix.mulVecLin_apply, map_sum, map_smul]
    rw [h4]
    refine Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ ?_
    have h5 : (e c).mulVec (M i) = if c = (σ i).1 then M i else 0 :=
      mulVec_column_of_orthogonal_idempotents e he c (σ i).1 _
    rw [h5]
    split_ifs with h
    · exact Submodule.subset_span ⟨i, h.symm, by subst h; rfl⟩
    · exact zero_mem _
  · rw [Submodule.span_le]
    rintro _ ⟨i, -, rfl⟩
    exact Submodule.subset_span ⟨a (σ i).1 (σ i).2, rfl⟩

end GlobalTheory.ZH
