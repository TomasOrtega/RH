import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.JpUnif

noncomputable section

open Matrix
open scoped NNReal

namespace GlobalTheory.CompanionTheory.Jp.Hgt

variable {n : ℕ}

/- English proof (translation)
Use `first`. Consider the case `exact Fintype.sum_sum_type f`. Consider the case `exact (Fintype.sum_equiv (Equiv.refl _ : GlobalTheory.CompanionTheory.Jp.Ix n ≃ (Fin n ⊕ Fin n)) f f (fun _ => rfl)).trans (Fintype.sum_sum_type f)`.
-/
private theorem sum_Ix_eq_sum_inl_add_sum_inr {M : Type} [AddCommMonoid M] (f : GlobalTheory.CompanionTheory.Jp.Ix n → M) :
    ∑ x, f x = ∑ i, f (Sum.inl i) + ∑ i, f (Sum.inr i) := by
  first
  | exact Fintype.sum_sum_type f
  | exact (Fintype.sum_equiv (Equiv.refl _ : GlobalTheory.CompanionTheory.Jp.Ix n ≃ (Fin n ⊕ Fin n)) f f
      (fun _ => rfl)).trans (Fintype.sum_sum_type f)

/- English proof (translation)
Combine the equalities or inequalities in the displayed calculation.
-/
private theorem eq_zero_of_vecMul_GL_eq_zero {ι R : Type} [Fintype ι] [DecidableEq ι]
    [CommRing R] (A : GL ι R) {x : ι → R} (h : x ᵥ* A.1 = 0) : x = 0 := by
  calc x = x ᵥ* (A.1 * (A⁻¹).1) := by rw [Units.mul_inv A, Matrix.vecMul_one]
    _ = 0 := by rw [← Matrix.vecMul_vecMul, h, Matrix.zero_vecMul]

/- English proof (translation)
Establish `hy : (Sum.elim 0 x : GlobalTheory.CompanionTheory.Jp.Ix n → R) ᵥ* K.1 = 0`. Use function extensionality and compare the values at `c`. Break down `c with c | c` into its components or cases. Establish `h` using `congrFun h₁ c`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h ⊢`.

Rewrite using `[sum_Ix_eq_sum_inl_add_sum_inr]`. Simplify `h` using `[GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, Matrix.toBlocks₂₁]`. Establish `h` using `congrFun h₂ c`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h ⊢`. Rewrite using `[sum_Ix_eq_sum_inl_add_sum_inr]`.

Simplify `h` using `[GlobalTheory.CompanionTheory.Jp.dBlk, Matrix.toBlocks₂₂]`. Establish `h0` using `eq_zero_of_vecMul_GL_eq_zero K hy`. Use function extensionality and compare the values at `j`. Conclude with `congrFun h0 (Sum.inr j)`.
-/
private theorem eq_zero_of_vecMul_lowerLeftBlock_dBlk_eq_zero {R : Type} [CommRing R]
    (K : GL (GlobalTheory.CompanionTheory.Jp.Ix n) R) (x : Fin n → R) (h₁ : x ᵥ* GlobalTheory.CompanionTheory.Jp.lowerLeftBlock K = 0)
    (h₂ : x ᵥ* GlobalTheory.CompanionTheory.Jp.dBlk K = 0) : x = 0 := by
  have hy : (Sum.elim 0 x : GlobalTheory.CompanionTheory.Jp.Ix n → R) ᵥ* K.1 = 0 := by
    funext c
    rcases c with c | c
    · have h := congrFun h₁ c
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h ⊢
      rw [sum_Ix_eq_sum_inl_add_sum_inr]
      simpa [GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, Matrix.toBlocks₂₁] using h
    · have h := congrFun h₂ c
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply] at h ⊢
      rw [sum_Ix_eq_sum_inl_add_sum_inr]
      simpa [GlobalTheory.CompanionTheory.Jp.dBlk, Matrix.toBlocks₂₂] using h
  have h0 := eq_zero_of_vecMul_GL_eq_zero K hy
  funext j
  exact congrFun h0 (Sum.inr j)

/- English proof (translation)
Take `⟨L, L', e, h⟩` from `Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal D`. Establish `hdet : ∀ l : List (TransvectionStruct (Fin n) k), ((l.map TransvectionStruct.toMatrix).prod).det = 1`. Introduce `l`. Proceed by induction on `l with`. Consider the case `nil => simp`.

Consider the case `cons t l ih => simp [Matrix.det_mul, ih, TransvectionStruct.det]`. Take `⟨uA, huA⟩ : ∃ u : GL (Fin n) k, u.1 = (L.map TransvectionStruct.toMatrix).prod` from `⟨Matrix.nonsingInvUnit (L.map TransvectionStruct.toMatrix).prod (by rw [hdet]; exact isUnit_one), rfl⟩`. Take `⟨uB, huB⟩ : ∃ u : GL (Fin n) k, u.1 = (L'.map TransvectionStruct.toMatrix).prod` from `⟨Matrix.nonsingInvUnit (L'.map TransvectionStruct.toMatrix).prod (by rw [hdet]; exact isUnit_one), rfl⟩`. Establish `hP : uA.1 * D = diagonal e * (uB⁻¹).1`. Combine the equalities or inequalities in the displayed calculation.

Use `⟨uA, uB⁻¹, e, hP, ?_⟩` and prove the remaining obligations. Establish `h1 : (uA.1 * D).rank = D.rank` using `Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [huA, hdet]; exact isUnit_one)`. Establish `h2 : (diagonal e * (uB⁻¹).1).rank = (diagonal e).rank` using `Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _)`. Rewrite using `[← h1, hP, h2, Matrix.rank_diagonal]`. Conclude with `Nat.card_eq_fintype_card`.
-/
theorem exists_row_reduction {k : Type} [Field k] (D : Matrix (Fin n) (Fin n) k) :
    ∃ (P R : GL (Fin n) k) (e : Fin n → k), P.1 * D = diagonal e * R.1 ∧
      Nat.card {j // e j ≠ 0} = D.rank := by
  classical
  obtain ⟨L, L', e, h⟩ := Matrix.Pivot.exists_list_transvec_mul_mul_list_transvec_eq_diagonal D
  have hdet : ∀ l : List (TransvectionStruct (Fin n) k),
      ((l.map TransvectionStruct.toMatrix).prod).det = 1 := by
    intro l
    induction l with
    | nil => simp
    | cons t l ih => simp [Matrix.det_mul, ih, TransvectionStruct.det]
  obtain ⟨uA, huA⟩ : ∃ u : GL (Fin n) k, u.1 = (L.map TransvectionStruct.toMatrix).prod :=
    ⟨Matrix.nonsingInvUnit (L.map TransvectionStruct.toMatrix).prod
      (by rw [hdet]; exact isUnit_one), rfl⟩
  obtain ⟨uB, huB⟩ : ∃ u : GL (Fin n) k, u.1 = (L'.map TransvectionStruct.toMatrix).prod :=
    ⟨Matrix.nonsingInvUnit (L'.map TransvectionStruct.toMatrix).prod
      (by rw [hdet]; exact isUnit_one), rfl⟩
  have hP : uA.1 * D = diagonal e * (uB⁻¹).1 := by
    calc uA.1 * D = uA.1 * D * (uB.1 * (uB⁻¹).1) := by rw [Units.mul_inv uB, Matrix.mul_one]
      _ = diagonal e * (uB⁻¹).1 := by rw [← mul_assoc, huA, huB, h]
  refine ⟨uA, uB⁻¹, e, hP, ?_⟩
  have h1 : (uA.1 * D).rank = D.rank :=
    Matrix.rank_mul_eq_right_of_isUnit_det _ _ (by rw [huA, hdet]; exact isUnit_one)
  have h2 : (diagonal e * (uB⁻¹).1).rank = (diagonal e).rank :=
    Matrix.rank_mul_eq_left_of_isUnit_det _ _ (Matrix.isUnits_det_units _)
  rw [← h1, hP, h2, Matrix.rank_diagonal]
  exact Nat.card_eq_fintype_card

/- English proof (translation)
Take `⟨W, hW⟩` from `Submodule.exists_isCompl (Submodule.span k (Set.range v))`. Establish `hcard : Fintype.card (GlobalTheory.CompanionTheory.Jp.Ix n) = n + n` using `(Fintype.card_congr (Equiv.refl _ : GlobalTheory.CompanionTheory.Jp.Ix n ≃ (Fin n ⊕ Fin n))).trans (by simp)`. Establish `hfin : Module.finrank k W = n`. Establish `h1` using `Submodule.finrank_add_eq_of_isCompl hW`. Rewrite `h1` using `[finrank_span_eq_card hv, Fintype.card_fin, Module.finrank_fintype_fun_eq_card, hcard]`.

Use linear arithmetic over natural numbers and integers. Set `b` to `Module.finBasisOfFinrankEq k W hfin`. Set `u : Fin n → GlobalTheory.CompanionTheory.Jp.Ix n → k` to `fun j => (b j : GlobalTheory.CompanionTheory.Jp.Ix n → k)`. Establish `hu : LinearIndependent k u` using `b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)`. Establish `hle : Submodule.span k (Set.range u) ≤ W`.

Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `(b j).2`. Establish `hsum : LinearIndependent k (Sum.elim u v)` using `LinearIndependent.sum_type hu hv (Disjoint.mono_left hle hW.disjoint.symm)`. Establish `hM : IsUnit (Matrix.of (Sum.elim u v) : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) k)` using `(Matrix.linearIndependent_rows_iff_isUnit (A := (Matrix.of (Sum.elim u v) : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) k))).mp hsum`.

Use `⟨hM.unit, fun j c => ?_⟩` and prove the remaining obligations. Use `first`. Consider the case `rfl`. Consider the case `(rw [IsUnit.unit_spec]; rfl)`. Consider the case `simp`.
-/
theorem exists_completion {k : Type} [Field k] (v : Fin n → Ix n → k) (hv : LinearIndependent k v) :
    ∃ G : GL (Ix n) k, ∀ j c, G.1 (Sum.inr j) c = v j c := by
  classical
  obtain ⟨W, hW⟩ := Submodule.exists_isCompl (Submodule.span k (Set.range v))
  have hcard : Fintype.card (GlobalTheory.CompanionTheory.Jp.Ix n) = n + n :=
    (Fintype.card_congr (Equiv.refl _ : GlobalTheory.CompanionTheory.Jp.Ix n ≃ (Fin n ⊕ Fin n))).trans (by simp)
  have hfin : Module.finrank k W = n := by
    have h1 := Submodule.finrank_add_eq_of_isCompl hW
    rw [finrank_span_eq_card hv, Fintype.card_fin, Module.finrank_fintype_fun_eq_card,
      hcard] at h1
    omega
  let b := Module.finBasisOfFinrankEq k W hfin
  let u : Fin n → GlobalTheory.CompanionTheory.Jp.Ix n → k := fun j => (b j : GlobalTheory.CompanionTheory.Jp.Ix n → k)
  have hu : LinearIndependent k u := b.linearIndependent.map' W.subtype (Submodule.ker_subtype W)
  have hle : Submodule.span k (Set.range u) ≤ W := by
    rw [Submodule.span_le]
    rintro _ ⟨j, rfl⟩
    exact (b j).2
  have hsum : LinearIndependent k (Sum.elim u v) :=
    LinearIndependent.sum_type hu hv (Disjoint.mono_left hle hW.disjoint.symm)
  have hM : IsUnit (Matrix.of (Sum.elim u v) : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) k) :=
    (Matrix.linearIndependent_rows_iff_isUnit
      (A := (Matrix.of (Sum.elim u v) : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) k))).mp hsum
  refine ⟨hM.unit, fun j c => ?_⟩
  first
  | rfl
  | (rw [IsUnit.unit_spec]; rfl)
  | simp

section Lift

variable {O : Type} [CommRing O] [IsLocalRing O]

/- English proof (translation)
Apply `isUnit_of_map_unit (IsLocalRing.residue O)` to reduce the goal to its premises. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply, h]`. Conclude with `Matrix.isUnits_det_units G`.
-/
theorem isUnit_det_of_res {ι : Type} [Fintype ι] [DecidableEq ι] (X : Matrix ι ι O)
    (G : GL ι (IsLocalRing.ResidueField O)) (h : X.map (IsLocalRing.residue O) = G.1) : IsUnit X.det := by
  apply isUnit_of_map_unit (IsLocalRing.residue O)
  rw [RingHom.map_det, RingHom.mapMatrix_apply, h]
  exact Matrix.isUnits_det_units G

/- English proof (translation)
Use `choose X hX using fun i j => IsLocalRing.residue_surjective (G.1 i j)`. Establish `hXm : Matrix.map (X : Matrix ι ι O) (IsLocalRing.residue O) = G.1` using `Matrix.ext fun i j => hX i j`. Conclude with `⟨Matrix.nonsingInvUnit _ (GlobalTheory.CompanionTheory.Jp.Hgt.isUnit_det_of_res _ G hXm), hXm⟩`.
-/
theorem exists_lift {ι : Type} [Fintype ι] [DecidableEq ι] (G : GL ι (IsLocalRing.ResidueField O)) :
    ∃ P : GL ι O, P.1.map (IsLocalRing.residue O) = G.1 := by
  choose X hX using fun i j => IsLocalRing.residue_surjective (G.1 i j)
  have hXm : Matrix.map (X : Matrix ι ι O) (IsLocalRing.residue O) = G.1 :=
    Matrix.ext fun i j => hX i j
  exact ⟨Matrix.nonsingInvUnit _ (GlobalTheory.CompanionTheory.Jp.Hgt.isUnit_det_of_res _ G hXm), hXm⟩

/- English proof (translation)
Take `⟨G, hG⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_completion _ hM`. Take `⟨P, hP⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_lift G`. Set `X : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) O` to `Matrix.of (Sum.elim (fun i => P.1 (Sum.inl i)) M)`. Establish `hX : X.map (IsLocalRing.residue O) = G.1`. Use extensionality with `i c`.

Break down `i with i | j` into its components or cases. Use `show IsLocalRing.residue O (P.1 (Sum.inl i) c) = G.1 (Sum.inl i) c`. Conclude with `congrFun (congrFun hP (Sum.inl i)) c`. Use `show IsLocalRing.residue O (M j c) = G.1 (Sum.inr j) c`. Conclude with `(hG j c).symm`.

Conclude with `⟨Matrix.nonsingInvUnit X (GlobalTheory.CompanionTheory.Jp.Hgt.isUnit_det_of_res X G hX), fun j c => rfl⟩`.
-/
theorem exists_lower (M : Matrix (Fin n) (Ix n) O)
    (hM : LinearIndependent (IsLocalRing.ResidueField O) (fun j c => IsLocalRing.residue O (M j c))) :
    ∃ κ : GL (Ix n) O, ∀ j c, κ.1 (Sum.inr j) c = M j c := by
  obtain ⟨G, hG⟩ := GlobalTheory.CompanionTheory.Jp.Hgt.exists_completion _ hM
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.Jp.Hgt.exists_lift G
  let X : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) O :=
    Matrix.of (Sum.elim (fun i => P.1 (Sum.inl i)) M)
  have hX : X.map (IsLocalRing.residue O) = G.1 := by
    ext i c
    rcases i with i | j
    · show IsLocalRing.residue O (P.1 (Sum.inl i) c) = G.1 (Sum.inl i) c
      exact congrFun (congrFun hP (Sum.inl i)) c
    · show IsLocalRing.residue O (M j c) = G.1 (Sum.inr j) c
      exact (hG j c).symm
  exact ⟨Matrix.nonsingInvUnit X (GlobalTheory.CompanionTheory.Jp.Hgt.isUnit_det_of_res X G hX), fun j c => rfl⟩

end Lift

/- English proof (translation)
Rewrite using `[Fintype.linearIndependent_iff]`. Introduce `g hg`. Establish `h1 : ∀ j, e j = 0 → g j = 0`. Take `⟨y, hy⟩ : ∃ y : Fin n → k, ∀ j, y j = if e j = 0 then g j else 0` from `⟨fun j => if e j = 0 then g j else 0, fun _ => rfl⟩`. Establish `hyC : (y ᵥ* P.1) ᵥ* GlobalTheory.CompanionTheory.Jp.lowerLeftBlock K = 0`.

Rewrite using `[Matrix.vecMul_vecMul]`. Use function extensionality and compare the values at `c`. Establish `hc` using `congrFun hg (Sum.inl c)`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc`. Rewrite using `[Pi.zero_apply, ← hc]`.

Simplify using `only [Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : e j = 0`. Rewrite using `[hy j, if_pos hj, hl j c hj]`. Rewrite using `[hy j, if_neg hj, hl' j c hj, zero_mul, mul_zero]`.

Establish `hyD : (y ᵥ* P.1) ᵥ* GlobalTheory.CompanionTheory.Jp.dBlk K = 0`. Rewrite using `[Matrix.vecMul_vecMul, h]`. Use function extensionality and compare the values at `c`. Simplify using `only [Matrix.vecMul, dotProduct, Pi.zero_apply]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[Matrix.diagonal_mul]`. Distinguish the cases in `hj : e j = 0`. Rewrite using `[hj, zero_mul, mul_zero]`. Rewrite using `[hy j, if_neg hj, zero_mul]`. Establish `hyP` using `eq_zero_of_vecMul_lowerLeftBlock_dBlk_eq_zero K _ hyC hyD`.

Establish `hy0` using `eq_zero_of_vecMul_GL_eq_zero P hyP`. Introduce `j hj`. Establish `hyj` using `congrFun hy0 j`. Rewrite `hyj` using `[Pi.zero_apply, hy j, if_pos hj]`. Then use the resulting hypothesis. Introduce `j`.

Distinguish the cases in `hj : e j = 0`. Conclude with `h1 j hj`. Establish `hz : (fun i => g i * e i) ᵥ* R.1 = 0`. Use function extensionality and compare the values at `c`. Establish `hc` using `congrFun hg (Sum.inr c)`.

Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc`. Rewrite using `[Pi.zero_apply, ← hc]`. Simplify using `only [Matrix.vecMul, dotProduct]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : e i = 0`.

Rewrite using `[h1 i hi, zero_mul, zero_mul, zero_mul]`. Rewrite using `[hr i c hi, h, Matrix.diagonal_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hzj : g j * e j = 0` using `congrFun (eq_zero_of_vecMul_GL_eq_zero R hz) j`. Conclude with `(mul_eq_zero.mp hzj).resolve_right hj`.
-/
theorem indep_core {k : Type} [Field k] (K : GL (Ix n) k) (P R : GL (Fin n) k) (e : Fin n → k)
    (h : P.1 * dBlk K = diagonal e * R.1) (v : Fin n → Ix n → k)
    (hl : ∀ j c, e j = 0 → v j (Sum.inl c) = (P.1 * lowerLeftBlock K) j c)
    (hl' : ∀ j c, e j ≠ 0 → v j (Sum.inl c) = 0)
    (hr : ∀ j c, e j ≠ 0 → v j (Sum.inr c) = (P.1 * dBlk K) j c) : LinearIndependent k v := by
  classical
  rw [Fintype.linearIndependent_iff]
  intro g hg
  have h1 : ∀ j, e j = 0 → g j = 0 := by
    obtain ⟨y, hy⟩ : ∃ y : Fin n → k, ∀ j, y j = if e j = 0 then g j else 0 :=
      ⟨fun j => if e j = 0 then g j else 0, fun _ => rfl⟩
    have hyC : (y ᵥ* P.1) ᵥ* GlobalTheory.CompanionTheory.Jp.lowerLeftBlock K = 0 := by
      rw [Matrix.vecMul_vecMul]
      funext c
      have hc := congrFun hg (Sum.inl c)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      rw [Pi.zero_apply, ← hc]
      simp only [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun j _ => ?_
      by_cases hj : e j = 0
      · rw [hy j, if_pos hj, hl j c hj]
      · rw [hy j, if_neg hj, hl' j c hj, zero_mul, mul_zero]
    have hyD : (y ᵥ* P.1) ᵥ* GlobalTheory.CompanionTheory.Jp.dBlk K = 0 := by
      rw [Matrix.vecMul_vecMul, h]
      funext c
      simp only [Matrix.vecMul, dotProduct, Pi.zero_apply]
      refine Finset.sum_eq_zero fun j _ => ?_
      rw [Matrix.diagonal_mul]
      by_cases hj : e j = 0
      · rw [hj, zero_mul, mul_zero]
      · rw [hy j, if_neg hj, zero_mul]
    have hyP := eq_zero_of_vecMul_lowerLeftBlock_dBlk_eq_zero K _ hyC hyD
    have hy0 := eq_zero_of_vecMul_GL_eq_zero P hyP
    intro j hj
    have hyj := congrFun hy0 j
    rwa [Pi.zero_apply, hy j, if_pos hj] at hyj
  intro j
  by_cases hj : e j = 0
  · exact h1 j hj
  · have hz : (fun i => g i * e i) ᵥ* R.1 = 0 := by
      funext c
      have hc := congrFun hg (Sum.inr c)
      simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply] at hc
      rw [Pi.zero_apply, ← hc]
      simp only [Matrix.vecMul, dotProduct]
      refine Finset.sum_congr rfl fun i _ => ?_
      by_cases hi : e i = 0
      · rw [h1 i hi, zero_mul, zero_mul, zero_mul]
      · rw [hr i c hi, h, Matrix.diagonal_mul]
        ring
    have hzj : g j * e j = 0 := congrFun (eq_zero_of_vecMul_GL_eq_zero R hz) j
    exact (mul_eq_zero.mp hzj).resolve_right hj

section Field

variable {L : Type} [Field L]

/- English proof (translation)
Use `ext`. Rewrite using `[Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `Matrix.det_fromBlocks_zero₂₁ _ _ _`.
-/
theorem det_pM (a d : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) :
    Matrix.GeneralLinearGroup.det (pM a d b) =
      Matrix.GeneralLinearGroup.det a * Matrix.GeneralLinearGroup.det d := by
  ext
  rw [Units.val_mul, Matrix.GeneralLinearGroup.val_det_apply,
    Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply]
  exact Matrix.det_fromBlocks_zero₂₁ _ _ _

/- English proof (translation)
Unfold `GlobalTheory.CompanionTheory.Jp.tauM`. Rewrite using `[GlobalTheory.CompanionTheory.Jp.Hgt.det_pM, map_one, one_mul]`. Use `ext`. Simplify using `[GlobalTheory.CompanionTheory.Jp.scM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.scalar_apply, Matrix.det_diagonal]`.
-/
theorem det_tauM (w : Lˣ) : Matrix.GeneralLinearGroup.det (tauM (n := n) w) = w ^ n := by
  unfold GlobalTheory.CompanionTheory.Jp.tauM
  rw [GlobalTheory.CompanionTheory.Jp.Hgt.det_pM, map_one, one_mul]
  ext
  simp [GlobalTheory.CompanionTheory.Jp.scM, Matrix.GeneralLinearGroup.val_det_apply, Matrix.scalar_apply,
    Matrix.det_diagonal]

/- English proof (translation)
Establish `key : ∀ M N : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L, (M * N).submatrix Sum.inr id = M.submatrix Sum.inr id * N`. Introduce `M N`. Use extensionality with `i j`. Use `first`. Consider the case `rfl`.

Consider the case `simp [Matrix.mul_apply]`. Take `⟨X, hX⟩ : ∃ X : GL (GlobalTheory.CompanionTheory.Jp.Ix n) L, X = g * κ₂⁻¹` from `⟨_, rfl⟩`. Establish `hbot : X.1.submatrix Sum.inr id = (dd⁻¹).1 * (1 : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L).submatrix Sum.inr id`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hX, Units.val_mul, key]`.

Use `_ = (dd⁻¹).1 * (dd.1 * g.1.submatrix Sum.inr id) * (κ₂⁻¹).1 := by`. Rewrite using `[← Matrix.mul_assoc (dd⁻¹).1, Units.inv_mul, Matrix.one_mul]`. Use `_ = (dd⁻¹).1 * (κ₂.1 * (κ₂⁻¹).1).submatrix Sum.inr id := by`. Rewrite using `[h, key, Matrix.mul_assoc]`. Use `_ = (dd⁻¹).1 * (1 : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L).submatrix Sum.inr id := by`.

Rewrite using `[Units.mul_inv]`. Establish `h21 : toBlocks₂₁ X.1 = 0`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hbot i) (Sum.inl j)`. Use `show X.1 (Sum.inr i) (Sum.inl j) = 0`.

Rewrite using `[show X.1 (Sum.inr i) (Sum.inl j) = X.1.submatrix Sum.inr id i (Sum.inl j) from rfl, hij]`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `h22 : toBlocks₂₂ X.1 = (dd⁻¹).1`. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hbot i) (Sum.inr j)`.

Use `show X.1 (Sum.inr i) (Sum.inr j) = (dd⁻¹).1 i j`. Rewrite using `[show X.1 (Sum.inr i) (Sum.inr j) = X.1.submatrix Sum.inr id i (Sum.inr j) from rfl, hij]`. Simplify using `[Matrix.mul_apply, Matrix.one_apply]`. Establish `hXeq : X.1 = fromBlocks (toBlocks₁₁ X.1) (toBlocks₁₂ X.1) 0 (dd⁻¹).1`. Rewrite using `[← h21, ← h22]`.

Conclude with `(Matrix.fromBlocks_toBlocks X.1).symm`. Establish `hdetX : X.1.det ≠ 0` using `(Matrix.isUnits_det_units X).ne_zero`. Establish `hdetA : (toBlocks₁₁ X.1).det ≠ 0`. Introduce `h0`. Apply `hdetX` to reduce the goal to its premises.

Rewrite using `[hXeq, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]`. Establish `hpar : GlobalTheory.CompanionTheory.Jp.pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetA) dd⁻¹ (toBlocks₁₂ X.1) = X` using `Units.ext hXeq.symm`. Use `⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetA, toBlocks₁₂ X.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hpar, hX, inv_mul_cancel_right]`.
-/
theorem block_form (g κ₂ : GL (Ix n) L) (dd : GL (Fin n) L)
    (h : dd.1 * g.1.submatrix Sum.inr id = κ₂.1.submatrix Sum.inr id) :
    ∃ a b, g = pM a dd⁻¹ b * κ₂ := by
  have key : ∀ M N : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L,
      (M * N).submatrix Sum.inr id = M.submatrix Sum.inr id * N := by
    intro M N
    ext i j
    first
    | rfl
    | simp [Matrix.mul_apply]
  obtain ⟨X, hX⟩ : ∃ X : GL (GlobalTheory.CompanionTheory.Jp.Ix n) L, X = g * κ₂⁻¹ := ⟨_, rfl⟩
  have hbot : X.1.submatrix Sum.inr id =
      (dd⁻¹).1 * (1 : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L).submatrix Sum.inr id := by
    calc X.1.submatrix Sum.inr id = g.1.submatrix Sum.inr id * (κ₂⁻¹).1 := by
          rw [hX, Units.val_mul, key]
      _ = (dd⁻¹).1 * (dd.1 * g.1.submatrix Sum.inr id) * (κ₂⁻¹).1 := by
          rw [← Matrix.mul_assoc (dd⁻¹).1, Units.inv_mul, Matrix.one_mul]
      _ = (dd⁻¹).1 * (κ₂.1 * (κ₂⁻¹).1).submatrix Sum.inr id := by
          rw [h, key, Matrix.mul_assoc]
      _ = (dd⁻¹).1 * (1 : Matrix (GlobalTheory.CompanionTheory.Jp.Ix n) (GlobalTheory.CompanionTheory.Jp.Ix n) L).submatrix Sum.inr id := by
          rw [Units.mul_inv]
  have h21 : toBlocks₂₁ X.1 = 0 := by
    ext i j
    have hij := congrFun (congrFun hbot i) (Sum.inl j)
    show X.1 (Sum.inr i) (Sum.inl j) = 0
    rw [show X.1 (Sum.inr i) (Sum.inl j) = X.1.submatrix Sum.inr id i (Sum.inl j) from rfl, hij]
    simp [Matrix.mul_apply, Matrix.one_apply]
  have h22 : toBlocks₂₂ X.1 = (dd⁻¹).1 := by
    ext i j
    have hij := congrFun (congrFun hbot i) (Sum.inr j)
    show X.1 (Sum.inr i) (Sum.inr j) = (dd⁻¹).1 i j
    rw [show X.1 (Sum.inr i) (Sum.inr j) = X.1.submatrix Sum.inr id i (Sum.inr j) from rfl, hij]
    simp [Matrix.mul_apply, Matrix.one_apply]
  have hXeq : X.1 = fromBlocks (toBlocks₁₁ X.1) (toBlocks₁₂ X.1) 0 (dd⁻¹).1 := by
    rw [← h21, ← h22]
    exact (Matrix.fromBlocks_toBlocks X.1).symm
  have hdetX : X.1.det ≠ 0 := (Matrix.isUnits_det_units X).ne_zero
  have hdetA : (toBlocks₁₁ X.1).det ≠ 0 := by
    intro h0
    apply hdetX
    rw [hXeq, Matrix.det_fromBlocks_zero₂₁, h0, zero_mul]
  have hpar : GlobalTheory.CompanionTheory.Jp.pM (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetA) dd⁻¹
      (toBlocks₁₂ X.1) = X := Units.ext hXeq.symm
  refine ⟨Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdetA, toBlocks₁₂ X.1, ?_⟩
  rw [hpar, hX, inv_mul_cancel_right]

end Field

section Main

variable {O L : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field L] [Algebra O L]
  [IsFractionRing O L]

def diagU (δ : Fin n → Lˣ) : GL (Fin n) L where
  val := diagonal fun j => (δ j : L)
  inv := diagonal fun j => ((δ j)⁻¹ : Lˣ).1
  val_inv := by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  inv_val := by simp [Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]

/- English proof (translation)
Use `ext`. Use `first`. Consider the case `(rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod]`. Conclude with `Matrix.det_diagonal)`. Consider the case `simp [GlobalTheory.CompanionTheory.Jp.Hgt.diagU, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]`.
-/
theorem det_diagU (δ : Fin n → Lˣ) : Matrix.GeneralLinearGroup.det (diagU δ) = ∏ j, δ j := by
  ext
  first
  | (rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_prod]
     exact Matrix.det_diagonal)
  | simp [GlobalTheory.CompanionTheory.Jp.Hgt.diagU, Matrix.GeneralLinearGroup.val_det_apply, Matrix.det_diagonal]

/- English proof (translation)
Use `first`. Consider the case `(show fromBlocks ((1 : GL (Fin n) L)⁻¹).1 (-(((1 : GL (Fin n) L)⁻¹).1 * 0 * ((GlobalTheory.CompanionTheory.Jp.scM w)⁻¹).1)) 0 ((GlobalTheory.CompanionTheory.Jp.scM w)⁻¹).1 = _`. Simplify using `only [inv_one, Units.val_one, mul_zero, zero_mul, neg_zero]`. Use `congr 1`. Simplify using `[GlobalTheory.CompanionTheory.Jp.scM, Matrix.scalar_apply])`.

Consider the case `simp [GlobalTheory.CompanionTheory.Jp.tauM, GlobalTheory.CompanionTheory.Jp.pM, GlobalTheory.CompanionTheory.Jp.scM, Matrix.scalar_apply]`.
-/
theorem tauM_inv_val (w : Lˣ) :
    ((tauM (n := n) w)⁻¹).1 = fromBlocks 1 0 0 (diagonal fun _ => ((w⁻¹ : Lˣ) : L)) := by
  first
  | (show fromBlocks ((1 : GL (Fin n) L)⁻¹).1
        (-(((1 : GL (Fin n) L)⁻¹).1 * 0 * ((GlobalTheory.CompanionTheory.Jp.scM w)⁻¹).1)) 0
        ((GlobalTheory.CompanionTheory.Jp.scM w)⁻¹).1 = _
     simp only [inv_one, Units.val_one, mul_zero, zero_mul, neg_zero]
     congr 1
     simp [GlobalTheory.CompanionTheory.Jp.scM, Matrix.scalar_apply])
  | simp [GlobalTheory.CompanionTheory.Jp.tauM, GlobalTheory.CompanionTheory.Jp.pM, GlobalTheory.CompanionTheory.Jp.scM,
      Matrix.scalar_apply]

/- English proof (translation)
Rewrite using `[Units.val_mul, GlobalTheory.CompanionTheory.Jp.Hgt.tauM_inv_val, Matrix.mul_apply, sum_Ix_eq_sum_inl_add_sum_inr]`. Simplify using `[Matrix.one_apply, GlobalTheory.CompanionTheory.Jp.inL, GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, Matrix.toBlocks₂₁, Matrix.GeneralLinearGroup.map_apply]`.
-/
theorem lower_left (κ : GL (Ix n) O) (w : Lˣ) (j c : Fin n) :
    (inL κ * (tauM w)⁻¹).1 (Sum.inr j) (Sum.inl c) = algebraMap O L (lowerLeftBlock κ j c) := by
  rw [Units.val_mul, GlobalTheory.CompanionTheory.Jp.Hgt.tauM_inv_val, Matrix.mul_apply, sum_Ix_eq_sum_inl_add_sum_inr]
  simp [Matrix.one_apply, GlobalTheory.CompanionTheory.Jp.inL, GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, Matrix.toBlocks₂₁,
    Matrix.GeneralLinearGroup.map_apply]

/- English proof (translation)
Rewrite using `[Units.val_mul, GlobalTheory.CompanionTheory.Jp.Hgt.tauM_inv_val, Matrix.mul_apply, sum_Ix_eq_sum_inl_add_sum_inr]`. Simplify using `[Matrix.diagonal_apply, GlobalTheory.CompanionTheory.Jp.inL, GlobalTheory.CompanionTheory.Jp.dBlk, Matrix.toBlocks₂₂, Matrix.GeneralLinearGroup.map_apply]`.
-/
theorem lower_right (κ : GL (Ix n) O) (w : Lˣ) (j c : Fin n) :
    (inL κ * (tauM w)⁻¹).1 (Sum.inr j) (Sum.inr c) = algebraMap O L (dBlk κ j c) * ((w⁻¹ : Lˣ) : L) := by
  rw [Units.val_mul, GlobalTheory.CompanionTheory.Jp.Hgt.tauM_inv_val, Matrix.mul_apply, sum_Ix_eq_sum_inl_add_sum_inr]
  simp [Matrix.diagonal_apply, GlobalTheory.CompanionTheory.Jp.inL, GlobalTheory.CompanionTheory.Jp.dBlk, Matrix.toBlocks₂₂,
    Matrix.GeneralLinearGroup.map_apply]

/- English proof (translation)
Establish `hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ}` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ`. Establish `hϖ0 : IsLocalRing.residue O ϖ = 0`. Rewrite using `[IsLocalRing.residue_eq_zero_iff, hmax]`. Conclude with `Ideal.mem_span_singleton_self ϖ`. Take `⟨Pb, Rb, e, hPR, hcard⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_row_reduction (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ))`.

Take `⟨P, hP⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_lift Pb`. Establish `hPm : ∀ (N : Matrix (Fin n) (Fin n) O) (j c : Fin n), IsLocalRing.residue O ((P.1 * N) j c) = (Pb.1 * N.map (IsLocalRing.residue O)) j c`. Introduce `N j c`. Apply the tactic sequence `rw [← hP, ← Matrix.map_mul] <;> rfl`. Establish `hmapC : (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ).map (IsLocalRing.residue O) = GlobalTheory.CompanionTheory.Jp.lowerLeftBlock (GlobalTheory.CompanionTheory.Jp.resK κ)`.

Use extensionality with `a c`. Use `first`. Consider the case `rfl`. Consider the case `simp [GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, GlobalTheory.CompanionTheory.Jp.resK, Matrix.GeneralLinearGroup.map_apply, Matrix.toBlocks₂₁]`. Establish `hmapD : (GlobalTheory.CompanionTheory.Jp.dBlk κ).map (IsLocalRing.residue O) = GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)`.

Use extensionality with `a c`. Use `first`. Consider the case `rfl`. Consider the case `simp [GlobalTheory.CompanionTheory.Jp.dBlk, GlobalTheory.CompanionTheory.Jp.resK, Matrix.GeneralLinearGroup.map_apply, Matrix.toBlocks₂₂]`. Establish `hdiv : ∀ j c, ∃ t : O, e j = 0 → (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c = ϖ * t`.

Introduce `j c`. Distinguish the cases in `hj : e j = 0`. Establish `hmem : (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c ∈ IsLocalRing.maximalIdeal O`. Rewrite using `[← IsLocalRing.residue_eq_zero_iff, hPm, hmapD, hPR, Matrix.diagonal_mul, hj, zero_mul]`. Rewrite `hmem` using `[hmax, Ideal.mem_span_singleton]`.

Take `⟨t, ht⟩` from `hmem`. Conclude with `⟨t, fun _ => ht⟩`. Conclude with `⟨0, fun h0 => absurd h0 hj⟩`. Use `choose t ht using hdiv`. Take `⟨M, hMl, hMr⟩ : ∃ M : Matrix (Fin n) (GlobalTheory.CompanionTheory.Jp.Ix n) O, (∀ j c, M j (Sum.inl c) = if e j = 0 then (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c else ϖ * (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c) ∧ (∀ j c, M j (Sum.inr c) = …` from `⟨fun j => Sum.elim (fun c => if e j = 0 then (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c else ϖ * (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c) (fun c => if e j = 0 then t j c else (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c), fun _ _ => rf …`.

Establish `hli : LinearIndependent (IsLocalRing.ResidueField O) (fun j c => IsLocalRing.residue O (M j c))`. Use `GlobalTheory.CompanionTheory.Jp.Hgt.indep_core (GlobalTheory.CompanionTheory.Jp.resK κ) Pb Rb e hPR _ ?_ ?_ ?_` and prove the remaining obligations. Introduce `j c hj show IsLocalRing.residue O (M j (Sum.inl c)) = _`. Rewrite using `[hMl, if_pos hj, hPm, hmapC]`. Introduce `j c hj show IsLocalRing.residue O (M j (Sum.inl c)) = 0`.

Rewrite using `[hMl, if_neg hj, map_mul, hϖ0, zero_mul]`. Introduce `j c hj show IsLocalRing.residue O (M j (Sum.inr c)) = _`. Rewrite using `[hMr, if_neg hj, hPm, hmapD]`. Take `⟨κ₂, hκ₂⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_lower M hli`. Take `⟨δ, hδ⟩ : ∃ δ : Fin n → Lˣ, ∀ j, δ j = if e j = 0 then 1 else w` from `⟨fun j => if e j = 0 then 1 else w, fun _ => rfl⟩`.

Take `⟨dd, hdddef⟩ : ∃ dd : GL (Fin n) L, dd = GlobalTheory.CompanionTheory.Jp.Hgt.diagU δ * Matrix.GeneralLinearGroup.map (algebraMap O L) P` from `⟨_, rfl⟩`. Take `⟨X, hXdef⟩ : ∃ X : GL (GlobalTheory.CompanionTheory.Jp.Ix n) L, X = GlobalTheory.CompanionTheory.Jp.inL κ * (GlobalTheory.CompanionTheory.Jp.tauM w)⁻¹` from `⟨_, rfl⟩`. Establish `hX : ∀ m c, X.1 (Sum.inr m) (Sum.inl c) = algebraMap O L (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ m c)`. Introduce `m c`. Rewrite using `[hXdef]`.

Conclude with `GlobalTheory.CompanionTheory.Jp.Hgt.lower_left κ w m c`. Establish `hX' : ∀ m c, X.1 (Sum.inr m) (Sum.inr c) = algebraMap O L (GlobalTheory.CompanionTheory.Jp.dBlk κ m c) * ((w⁻¹ : Lˣ) : L)`. Introduce `m c`. Rewrite using `[hXdef]`. Conclude with `GlobalTheory.CompanionTheory.Jp.Hgt.lower_right κ w m c`.

Establish `hdd : ∀ j m, dd.1 j m = (δ j : L) * algebraMap O L (P.1 j m)`. Introduce `j m`. Rewrite using `[hdddef, Units.val_mul]`. Use `show (Matrix.diagonal (fun i => (δ i : L)) * (Matrix.GeneralLinearGroup.map (algebraMap O L) P).1) j m = _`. Rewrite using `[Matrix.diagonal_mul, Matrix.GeneralLinearGroup.map_apply]`.

Apply the tactic sequence `have hentry : ∀ j col, (dd.1 * X.1.submatrix Sum.inr id) j col = (δ j : L) * ∑ m, algebraMap O L (P.1 j m) * X.1 (Sum.inr m) col := by`. Introduce `j col`. Rewrite using `[Matrix.mul_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun m _ => ?_` and prove the remaining obligations. Rewrite using `[hdd, Matrix.submatrix_apply, id_eq, mul_assoc]`.

Establish `hκ₂L : ∀ j col, (GlobalTheory.CompanionTheory.Jp.inL κ₂).1 (Sum.inr j) col = algebraMap O L (M j col)`. Introduce `j col`. Rewrite using `[← hκ₂ j col]`. Use `first`. Consider the case `rfl`.

Consider the case `simp [GlobalTheory.CompanionTheory.Jp.inL, Matrix.GeneralLinearGroup.map_apply]`. Establish `hPC : ∀ j c, ∑ m, algebraMap O L (P.1 j m) * algebraMap O L (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ m c) = algebraMap O L ((P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c)`. Introduce `j c`. Rewrite using `[Matrix.mul_apply, map_sum]`. Simplify using `only [map_mul]`.

Establish `hPD : ∀ j c, ∑ m, algebraMap O L (P.1 j m) * (algebraMap O L (GlobalTheory.CompanionTheory.Jp.dBlk κ m c) * ((w⁻¹ : Lˣ) : L)) = algebraMap O L ((P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c) * ((w⁻¹ : Lˣ) : L)`. Introduce `j c`. Rewrite using `[Matrix.mul_apply, map_sum, Finset.sum_mul]`. Simplify using `only [map_mul, mul_assoc]`. Establish `hbot : dd.1 * X.1.submatrix Sum.inr id = (GlobalTheory.CompanionTheory.Jp.inL κ₂).1.submatrix Sum.inr id`.

Use extensionality with `j col`. Rewrite using `[hentry, Matrix.submatrix_apply, id_eq, hκ₂L]`. Break down `col with c | c` into its components or cases. Simplify using `only [hX]`. Rewrite using `[hPC, hMl]`.

Distinguish the cases in `hj : e j = 0`. Simplify using `only [hδ j, if_pos hj, Units.val_one, one_mul]`. Simplify using `only [hδ j, if_neg hj, map_mul, ← hw]`. Simplify using `only [hX']`. Rewrite using `[hPD, hMr]`.

Distinguish the cases in `hj : e j = 0`. Simplify using `only [hδ j, if_pos hj, Units.val_one, one_mul]`. Rewrite using `[ht j c hj, map_mul, ← hw, mul_comm (w : L), mul_assoc, Units.mul_inv, mul_one]`. Simplify using `only [hδ j, if_neg hj]`. Rewrite using `[mul_comm (w : L), mul_assoc, Units.inv_mul, mul_one]`.

Take `⟨a, b, hab⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.block_form X (GlobalTheory.CompanionTheory.Jp.inL κ₂) dd hbot`. Establish `hprod : ∏ j, δ j = w ^ (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank`. Rewrite using `[← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.prod_const, Finset.prod_filter]`. Use `Finset.prod_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[hδ j]`.

Apply the tactic sequence `by_cases hj : e j = 0 <;> simp [hj]`. Establish `hdet : Matrix.GeneralLinearGroup.det dd = Units.map (algebraMap O L).toMonoidHom (Matrix.GeneralLinearGroup.det P) * w ^ (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank`. Rewrite using `[hdddef, map_mul, GlobalTheory.CompanionTheory.Jp.Hgt.det_diagU, hprod, Matrix.GeneralLinearGroup.map_det]`. Conclude with `mul_comm _ _`. Use `⟨a, b, κ₂, dd, Matrix.GeneralLinearGroup.det P, hdet, ?_⟩` and prove the remaining obligations.

Rewrite using `[← hXdef]`. Conclude with `hab`.
-/
theorem exists_decomp (ϖ : O) (hϖ : Irreducible ϖ) (w : Lˣ) (hw : (w : L) = algebraMap O L ϖ)
    (κ : GL (Ix n) O) :
    ∃ (a : GL (Fin n) L) (b : Matrix (Fin n) (Fin n) L) (κ₂ : GL (Ix n) O) (dd : GL (Fin n) L) (u : Oˣ),
      Matrix.GeneralLinearGroup.det dd =
        Units.map (algebraMap O L).toMonoidHom u * w ^ (dBlk (resK κ)).rank ∧
      inL κ * (tauM w)⁻¹ = pM a dd⁻¹ b * inL κ₂ := by
  classical
  have hmax : IsLocalRing.maximalIdeal O = Ideal.span {ϖ} :=
    (IsDiscreteValuationRing.irreducible_iff_uniformizer ϖ).mp hϖ
  have hϖ0 : IsLocalRing.residue O ϖ = 0 := by
    rw [IsLocalRing.residue_eq_zero_iff, hmax]
    exact Ideal.mem_span_singleton_self ϖ
  obtain ⟨Pb, Rb, e, hPR, hcard⟩ :=
    GlobalTheory.CompanionTheory.Jp.Hgt.exists_row_reduction
      (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ))
  obtain ⟨P, hP⟩ := GlobalTheory.CompanionTheory.Jp.Hgt.exists_lift Pb
  have hPm : ∀ (N : Matrix (Fin n) (Fin n) O) (j c : Fin n),
      IsLocalRing.residue O ((P.1 * N) j c) = (Pb.1 * N.map (IsLocalRing.residue O)) j c := by
    intro N j c
    rw [← hP, ← Matrix.map_mul] <;> rfl
  have hmapC : (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ).map (IsLocalRing.residue O) =
      GlobalTheory.CompanionTheory.Jp.lowerLeftBlock (GlobalTheory.CompanionTheory.Jp.resK κ) := by
    ext a c
    first
    | rfl
    | simp [GlobalTheory.CompanionTheory.Jp.lowerLeftBlock, GlobalTheory.CompanionTheory.Jp.resK, Matrix.GeneralLinearGroup.map_apply,
        Matrix.toBlocks₂₁]
  have hmapD : (GlobalTheory.CompanionTheory.Jp.dBlk κ).map (IsLocalRing.residue O) =
      GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ) := by
    ext a c
    first
    | rfl
    | simp [GlobalTheory.CompanionTheory.Jp.dBlk, GlobalTheory.CompanionTheory.Jp.resK, Matrix.GeneralLinearGroup.map_apply,
        Matrix.toBlocks₂₂]
  have hdiv : ∀ j c, ∃ t : O, e j = 0 → (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c = ϖ * t := by
    intro j c
    by_cases hj : e j = 0
    · have hmem : (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c ∈ IsLocalRing.maximalIdeal O := by
        rw [← IsLocalRing.residue_eq_zero_iff, hPm, hmapD, hPR, Matrix.diagonal_mul, hj, zero_mul]
      rw [hmax, Ideal.mem_span_singleton] at hmem
      obtain ⟨t, ht⟩ := hmem
      exact ⟨t, fun _ => ht⟩
    · exact ⟨0, fun h0 => absurd h0 hj⟩
  choose t ht using hdiv
  obtain ⟨M, hMl, hMr⟩ : ∃ M : Matrix (Fin n) (GlobalTheory.CompanionTheory.Jp.Ix n) O,
      (∀ j c, M j (Sum.inl c) = if e j = 0 then (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c
        else ϖ * (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c) ∧
      (∀ j c, M j (Sum.inr c) = if e j = 0 then t j c else (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c) :=
    ⟨fun j => Sum.elim (fun c => if e j = 0 then (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c
        else ϖ * (P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c)
      (fun c => if e j = 0 then t j c else (P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c),
      fun _ _ => rfl, fun _ _ => rfl⟩
  have hli : LinearIndependent (IsLocalRing.ResidueField O)
      (fun j c => IsLocalRing.residue O (M j c)) := by
    refine GlobalTheory.CompanionTheory.Jp.Hgt.indep_core
      (GlobalTheory.CompanionTheory.Jp.resK κ) Pb Rb e hPR _ ?_ ?_ ?_
    · intro j c hj
      show IsLocalRing.residue O (M j (Sum.inl c)) = _
      rw [hMl, if_pos hj, hPm, hmapC]
    · intro j c hj
      show IsLocalRing.residue O (M j (Sum.inl c)) = 0
      rw [hMl, if_neg hj, map_mul, hϖ0, zero_mul]
    · intro j c hj
      show IsLocalRing.residue O (M j (Sum.inr c)) = _
      rw [hMr, if_neg hj, hPm, hmapD]
  obtain ⟨κ₂, hκ₂⟩ := GlobalTheory.CompanionTheory.Jp.Hgt.exists_lower M hli
  obtain ⟨δ, hδ⟩ : ∃ δ : Fin n → Lˣ, ∀ j, δ j = if e j = 0 then 1 else w :=
    ⟨fun j => if e j = 0 then 1 else w, fun _ => rfl⟩
  obtain ⟨dd, hdddef⟩ : ∃ dd : GL (Fin n) L,
      dd = GlobalTheory.CompanionTheory.Jp.Hgt.diagU δ * Matrix.GeneralLinearGroup.map (algebraMap O L) P := ⟨_, rfl⟩
  obtain ⟨X, hXdef⟩ : ∃ X : GL (GlobalTheory.CompanionTheory.Jp.Ix n) L,
      X = GlobalTheory.CompanionTheory.Jp.inL κ * (GlobalTheory.CompanionTheory.Jp.tauM w)⁻¹ := ⟨_, rfl⟩
  have hX : ∀ m c, X.1 (Sum.inr m) (Sum.inl c) = algebraMap O L (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ m c) := by
    intro m c
    rw [hXdef]
    exact GlobalTheory.CompanionTheory.Jp.Hgt.lower_left κ w m c
  have hX' : ∀ m c, X.1 (Sum.inr m) (Sum.inr c) =
      algebraMap O L (GlobalTheory.CompanionTheory.Jp.dBlk κ m c) * ((w⁻¹ : Lˣ) : L) := by
    intro m c
    rw [hXdef]
    exact GlobalTheory.CompanionTheory.Jp.Hgt.lower_right κ w m c
  have hdd : ∀ j m, dd.1 j m = (δ j : L) * algebraMap O L (P.1 j m) := by
    intro j m
    rw [hdddef, Units.val_mul]
    show (Matrix.diagonal (fun i => (δ i : L)) *
      (Matrix.GeneralLinearGroup.map (algebraMap O L) P).1) j m = _
    rw [Matrix.diagonal_mul, Matrix.GeneralLinearGroup.map_apply]
  have hentry : ∀ j col, (dd.1 * X.1.submatrix Sum.inr id) j col =
      (δ j : L) * ∑ m, algebraMap O L (P.1 j m) * X.1 (Sum.inr m) col := by
    intro j col
    rw [Matrix.mul_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [hdd, Matrix.submatrix_apply, id_eq, mul_assoc]
  have hκ₂L : ∀ j col, (GlobalTheory.CompanionTheory.Jp.inL κ₂).1 (Sum.inr j) col =
      algebraMap O L (M j col) := by
    intro j col
    rw [← hκ₂ j col]
    first
    | rfl
    | simp [GlobalTheory.CompanionTheory.Jp.inL, Matrix.GeneralLinearGroup.map_apply]
  have hPC : ∀ j c, ∑ m, algebraMap O L (P.1 j m) * algebraMap O L (GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ m c) =
      algebraMap O L ((P.1 * GlobalTheory.CompanionTheory.Jp.lowerLeftBlock κ) j c) := by
    intro j c
    rw [Matrix.mul_apply, map_sum]
    simp only [map_mul]
  have hPD : ∀ j c, ∑ m, algebraMap O L (P.1 j m) *
      (algebraMap O L (GlobalTheory.CompanionTheory.Jp.dBlk κ m c) * ((w⁻¹ : Lˣ) : L)) =
      algebraMap O L ((P.1 * GlobalTheory.CompanionTheory.Jp.dBlk κ) j c) * ((w⁻¹ : Lˣ) : L) := by
    intro j c
    rw [Matrix.mul_apply, map_sum, Finset.sum_mul]
    simp only [map_mul, mul_assoc]
  have hbot : dd.1 * X.1.submatrix Sum.inr id =
      (GlobalTheory.CompanionTheory.Jp.inL κ₂).1.submatrix Sum.inr id := by
    ext j col
    rw [hentry, Matrix.submatrix_apply, id_eq, hκ₂L]
    rcases col with c | c
    · simp only [hX]
      rw [hPC, hMl]
      by_cases hj : e j = 0
      · simp only [hδ j, if_pos hj, Units.val_one, one_mul]
      · simp only [hδ j, if_neg hj, map_mul, ← hw]
    · simp only [hX']
      rw [hPD, hMr]
      by_cases hj : e j = 0
      · simp only [hδ j, if_pos hj, Units.val_one, one_mul]
        rw [ht j c hj, map_mul, ← hw, mul_comm (w : L), mul_assoc, Units.mul_inv, mul_one]
      · simp only [hδ j, if_neg hj]
        rw [mul_comm (w : L), mul_assoc, Units.inv_mul, mul_one]
  obtain ⟨a, b, hab⟩ := GlobalTheory.CompanionTheory.Jp.Hgt.block_form X
    (GlobalTheory.CompanionTheory.Jp.inL κ₂) dd hbot
  have hprod : ∏ j, δ j = w ^ (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank := by
    rw [← hcard, Nat.card_eq_fintype_card, Fintype.card_subtype, ← Finset.prod_const,
      Finset.prod_filter]
    refine Finset.prod_congr rfl fun j _ => ?_
    rw [hδ j]
    by_cases hj : e j = 0 <;> simp [hj]
  have hdet : Matrix.GeneralLinearGroup.det dd = Units.map (algebraMap O L).toMonoidHom
      (Matrix.GeneralLinearGroup.det P) * w ^ (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank := by
    rw [hdddef, map_mul, GlobalTheory.CompanionTheory.Jp.Hgt.det_diagU, hprod, Matrix.GeneralLinearGroup.map_det]
    exact mul_comm _ _
  refine ⟨a, b, κ₂, dd, Matrix.GeneralLinearGroup.det P, hdet, ?_⟩
  rw [← hXdef]
  exact hab

/- English proof (translation)
Introduce `O L _ _ _ _ _ _ _ n ϖ hϖ w hw nv hnv h hh κ`. Take `⟨hunit, hnw⟩` from `hnv`. Take `⟨a, b, κ₂, dd, u, hdet, heq⟩` from `GlobalTheory.CompanionTheory.Jp.Hgt.exists_decomp ϖ hϖ w hw κ`. Take `⟨t, ht⟩` from `Nat.exists_eq_add_of_le (Matrix.rank_le_width (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)))`. Establish `hcorank : GlobalTheory.CompanionTheory.Jp.iD (GlobalTheory.CompanionTheory.Jp.resK κ) = t`.

Unfold `GlobalTheory.CompanionTheory.Jp.iD`. Use linear arithmetic over natural numbers and integers. Establish `hu : nv (Units.map (algebraMap O L).toMonoidHom u) = 1` using `hunit u`. Use `set q : ℝ≥0 := (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) with hq_def`. Use `set r := (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank with hr_def`.

Establish `hq : q ≠ 0`. Rewrite using `[hq_def]`. Conclude with `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Establish `hDd : nv (Matrix.GeneralLinearGroup.det dd) = q⁻¹ ^ r`. Rewrite using `[hdet, map_mul, hu, one_mul, map_pow, hnw]`.

Establish `hdetEq` using `congrArg Matrix.GeneralLinearGroup.det heq`. Simplify using `only [map_mul, map_inv, GlobalTheory.CompanionTheory.Jp.Hgt.det_tauM, GlobalTheory.CompanionTheory.Jp.Hgt.det_pM, GlobalTheory.CompanionTheory.Jp.inL, Matrix.GeneralLinearGroup.map_det] at hdetEq`. Establish `hnvEq` using `congrArg nv hdetEq`. Simplify using `only [map_mul, map_inv, map_pow, hnw] at hnvEq`. Use `erw [hunit, hunit] at hnvEq`.

Rewrite `hnvEq` using `[one_mul, mul_one]`. Rewrite `hnvEq` using `[hDd, inv_pow, inv_inv, inv_pow, inv_inv]`. Establish `hA : nv (Matrix.GeneralLinearGroup.det a) = q ^ t`. Apply `mul_right_cancel₀ (pow_ne_zero r hq)` to reduce the goal to its premises. Rewrite using `[← hnvEq, ht, pow_add, mul_comm]`.

Rewrite using `[heq, hh a dd⁻¹ b κ₂, map_inv, map_inv, hDd, hcorank, inv_pow, inv_inv, hA, div_eq_div_iff (pow_ne_zero _ hq) (pow_ne_zero _ hq), ht]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem jpHgt : JpHgt := by
  intro O L _ _ _ _ _ _ _ n ϖ hϖ w hw nv hnv h hh κ
  obtain ⟨hunit, hnw⟩ := hnv
  obtain ⟨a, b, κ₂, dd, u, hdet, heq⟩ :=
    GlobalTheory.CompanionTheory.Jp.Hgt.exists_decomp ϖ hϖ w hw κ
  obtain ⟨t, ht⟩ := Nat.exists_eq_add_of_le
    (Matrix.rank_le_width (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)))
  have hcorank : GlobalTheory.CompanionTheory.Jp.iD (GlobalTheory.CompanionTheory.Jp.resK κ) = t := by
    unfold GlobalTheory.CompanionTheory.Jp.iD
    omega
  have hu : nv (Units.map (algebraMap O L).toMonoidHom u) = 1 := hunit u
  set q : ℝ≥0 := (Fintype.card (IsLocalRing.ResidueField O) : ℝ≥0) with hq_def
  set r := (GlobalTheory.CompanionTheory.Jp.dBlk (GlobalTheory.CompanionTheory.Jp.resK κ)).rank with hr_def
  have hq : q ≠ 0 := by
    rw [hq_def]
    exact Nat.cast_ne_zero.mpr Fintype.card_ne_zero
  have hDd : nv (Matrix.GeneralLinearGroup.det dd) = q⁻¹ ^ r := by
    rw [hdet, map_mul, hu, one_mul, map_pow, hnw]
  have hdetEq := congrArg Matrix.GeneralLinearGroup.det heq
  simp only [map_mul, map_inv, GlobalTheory.CompanionTheory.Jp.Hgt.det_tauM, GlobalTheory.CompanionTheory.Jp.Hgt.det_pM,
    GlobalTheory.CompanionTheory.Jp.inL, Matrix.GeneralLinearGroup.map_det] at hdetEq
  have hnvEq := congrArg nv hdetEq
  simp only [map_mul, map_inv, map_pow, hnw] at hnvEq
  erw [hunit, hunit] at hnvEq
  rw [one_mul, mul_one] at hnvEq
  rw [hDd, inv_pow, inv_inv, inv_pow, inv_inv] at hnvEq
  have hA : nv (Matrix.GeneralLinearGroup.det a) = q ^ t := by
    apply mul_right_cancel₀ (pow_ne_zero r hq)
    rw [← hnvEq, ht, pow_add, mul_comm]
  rw [heq, hh a dd⁻¹ b κ₂, map_inv, map_inv, hDd, hcorank, inv_pow, inv_inv, hA,
    div_eq_div_iff (pow_ne_zero _ hq) (pow_ne_zero _ hq), ht]
  ring

end Main

end GlobalTheory.CompanionTheory.Jp.Hgt

end
