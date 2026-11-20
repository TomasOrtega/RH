import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.IsTermOver
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.DetUpdateRowLastSingle

open ValuativeRel Formalism.MainNotions.S Formalism.MainNotions.S.Loc

namespace GlobalTheory

section

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V)

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma hsub_left (x x' y : V) : H.h (x - x') y = H.h x y - H.h x' y := by
  rw [eq_sub_iff_add_eq, ← H.h_add_left, sub_add_cancel]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma hsub_right (x y y' : V) : H.h x (y - y') = H.h x y - H.h x y' := by
  rw [H.h_herm (y - y') x, hsub_left, map_sub, ← H.h_herm, ← H.h_herm]

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
private lemma hsmul_right (c : F) (x y : V) :
    H.h x (algebraMap F E c • y) = algebraMap F E c * H.h x y := by
  rw [H.h_herm (algebraMap F E c • y) x, H.h_smul_left, map_mul, AlgEquiv.commutes, ← H.h_herm]

/- English proof (translation)
Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. A detailed English derivation is pending.
-/
private lemma det_transpose_map_cj {ι : Type} [Fintype ι] [DecidableEq ι] (N : Matrix ι ι E) :
    (N.transpose.map M.L.cj).det = M.L.cj N.det := by
  have h1 := RingHom.map_det (M.L.cj : E →+* E) N.transpose
  rw [Matrix.det_transpose] at h1
  exact h1.symm

/- English proof (translation)
Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression.
-/
private lemma castLE_succ_eq_castSucc (r : ℕ) (h : r ≤ r + 1) :
    (Fin.castLE h : Fin r → Fin (r + 1)) = Fin.castSucc := by
  funext i
  rfl

/- English proof (translation)
Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Substitute using the available equality.

Consider separately whether the proposition holds or fails. Substitute using the available equality. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Assume the negation of the conclusion and derive a contradiction. Simplify using the standard rewrite rules. Establish an intermediate fact. By extensionality, compare the relevant components. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
-/
theorem det_gram_sumElim_frames {r : ℕ} (P : LocNG.FPair H r) :
    (H.gram (Sum.elim P.A.f P.B.f)).det = (-1) ^ (r + 1) * P.Gv := by
  have diag : ∀ (Fr : LocNG.FrameD H r) (a b : Fin (r + 1)),
      H.h (Fr.f b) (Fr.f a) = Matrix.diagonal
        (fun i => if i = Fin.last r then -algebraMap F E Fr.T else 0) a b := by
    intro Fr a b
    rw [Matrix.diagonal_apply]
    by_cases hab : a = b
    · subst hab
      by_cases ha : a = Fin.last r
      · subst ha
        simp [Fr.h_zz]
      · simp [ha, Fr.h_iso a a (Or.inl ha)]
    · rw [if_neg hab, Fr.h_iso b a ?_]
      by_contra hc
      simp only [not_or, not_not] at hc
      exact hab (hc.2.trans hc.1.symm)
  have hblk : H.gram (Sum.elim P.A.f P.B.f) = Matrix.fromBlocks
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.A.T else 0)
      (H.Zhat P.A.f P.B.f)
      ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj)
      (Matrix.diagonal fun i => if i = Fin.last r then -algebraMap F E P.B.T else 0) := by
    ext (a | a) (b | b)
    · exact diag P.A a b
    · rfl
    · exact H.h_herm _ _
    · exact diag P.B a b
  rw [hblk, GlobalTheory.det_gram_two_frames, det_transpose_map_cj]
  have hsub : ((H.Zhat P.A.f P.B.f).transpose.map M.L.cj).submatrix Fin.castSucc Fin.castSucc
      = ((H.Zhat P.A.f P.B.f).submatrix Fin.castSucc Fin.castSucc).transpose.map M.L.cj := rfl
  rw [hsub, det_transpose_map_cj]
  congr 1
  simp only [LocNG.FPair.Gv, HermSp.Gdet, HermSp.normE, HermSp.Dl, dif_pos le_rfl,
    dif_pos (Nat.le_succ r), Fin.castLE_rfl, Matrix.submatrix_id_id, castLE_succ_eq_castSucc, map_mul]

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. A detailed English derivation is pending.
-/
theorem det_gram_sumElim_smul_sub {n : ℕ} (f f' : Fin n → V) (c : F) :
    (H.gram (Sum.elim f fun a => algebraMap F E c • (f' a - f a))).det
      = algebraMap F E c ^ (2 * n) * (H.gram (Sum.elim f f')).det := by
  set c' := algebraMap F E c with hc'
  have hcs : ∀ x : E, c • x = algebraMap F E c * x := fun x => Algebra.smul_def c x
  have key : H.gram (Sum.elim f fun a => c' • (f' a - f a)) =
      Matrix.fromBlocks 1 0 (-c' • (1 : Matrix (Fin n) (Fin n) E)) (c' • 1) * H.gram (Sum.elim f f') *
        Matrix.fromBlocks 1 (-c' • (1 : Matrix (Fin n) (Fin n) E)) 0 (c' • 1) := by
    ext (a | a) (b | b) <;>
      simp [HermSp.gram, Matrix.mul_apply, Fintype.sum_sum_type, Matrix.one_apply, H.h_smul_left,
        hsub_left, hsub_right, hc', hsmul_right, hcs] <;> ring
  rw [key, Matrix.det_mul, Matrix.det_mul, Matrix.det_fromBlocks_zero₁₂, Matrix.det_fromBlocks_zero₂₁]
  simp only [Matrix.det_one, Matrix.det_smul, Fintype.card_fin, one_mul, two_mul, pow_add]
  ring

end

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Replace the relevant objects with their definitions. Split into cases according to the possible forms of the given data. Treat this case separately. Simplify using the standard rewrite rules.

Treat this case separately. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses.

Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem det_gram_frame_generators :
    ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] {E : Type} [CommRing E]
      [Algebra F E] [TopologicalSpace E] [MeasurableSpace E] (M : Model F E), M.OK →
      ∀ {V : Type} [AddCommGroup V] [Module E V] (H : HermSp M V) (r _k : ℕ) (P : LocNG.FPair H r),
        (H.gram P.MMgen).det * algebraMap F E (LocNG.theta M) ^ (2 * (r + 1))
          = (-1) ^ (r + 1) * P.Gv := by
  intro F _ _ _ E _ _ _ _ M _ V _ _ H r _ P
  unfold LocNG.FPair.MMgen HermSp.MMfam LocNG.theta
  cases hs : M.split with
  | none =>
    simp only [map_one, one_pow, mul_one]
    exact det_gram_sumElim_frames H P
  | some g =>
    simp only
    rw [det_gram_sumElim_smul_sub H, det_gram_sumElim_frames H P, mul_comm _ (algebraMap F E _ ^ _),
      ← mul_assoc, ← mul_pow, ← map_mul]
    have hq : ((g.q : 𝒪[F]) : F) ≠ 0 := by
      intro h0
      exact g.q_irr.ne_zero (Subtype.ext h0)
    rw [mul_inv_cancel₀ hq, map_one, one_pow, one_mul]

end GlobalTheory
