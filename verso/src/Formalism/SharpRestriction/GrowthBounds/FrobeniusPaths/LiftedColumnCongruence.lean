import Formalism.SharpRestriction.GrowthBounds.FrobeniusPaths.ColStepFactor

noncomputable section

open MvPolynomial Finset Formalism.MainNotions.G Formalism.MainNotions.CovariantDegrees

namespace Formalism.MainNotions.LemmaBAlt

section LinkG

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

/- English proof (translation)
Establish `hinv : sigMat p f O g⁻¹ (LL.pos i) * sigMat p f O g (LL.pos i) = 1`. Rewrite using `[← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one]`. Establish `hC : ∀ x : KK O, liftSubst p f O w r LL g (C x) = C x` using `fun x => (liftSubst p f O w r LL g).commutes x`. Simplify using `only [yO, map_mul, map_C, map_X]`. Distinguish the cases in `hv : LL.vec i = true`.

Simplify using `only [letG, hv, if_true, map_sum, map_mul, hC, liftSubst_X_vec p f O w LL r g hg i _ hv]`. Repeatedly rewrite using `[Finset.sum_mul, mul_assoc, ← map_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply, apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Establish `hv' : LL.vec i = false` using `by simpa using hv`.

Simplify using `only [letG, hv', Bool.false_eq_true, if_false, map_sum, map_mul, hC, liftSubst_X_cov p f O w LL r g i _ hv', sigMat_inv p f O g hg]`. Repeatedly rewrite using `[Finset.sum_mul, mul_assoc, ← map_mul]`. Rewrite using `[Finset.sum_comm]`. Repeatedly rewrite using `[← Finset.mul_sum, ← map_sum, mul_comm (sigMat p f O g (LL.pos i) _ _), ← Matrix.mul_apply, hinv, Matrix.one_apply, apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`.
-/
lemma lift_letG (w : O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (hg : IsGLW g)
    (i : Fin N) (b : Fin (r + K)) :
    liftSubst p f O w r LL g (letG p f (O := O) LL g i b) =
      MvPolynomial.map (algebraMap O (KK O)) (yO w LL i b) := by
  have hinv : sigMat p f O g⁻¹ (LL.pos i) * sigMat p f O g (LL.pos i) = 1 := by
    rw [← sigMat_mul, Matrix.nonsing_inv_mul g hg, sigMat_one]
  have hC : ∀ x : KK O, liftSubst p f O w r LL g (C x) = C x := fun x => (liftSubst p f O w r LL g).commutes x
  simp only [yO, map_mul, map_C, map_X]
  by_cases hv : LL.vec i = true
  · simp only [letG, hv, if_true, map_sum, map_mul, hC, liftSubst_X_vec p f O w LL r g hg i _ hv]
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, ← Matrix.mul_apply, hinv, Matrix.one_apply, apply_ite C, map_one, map_zero,
      mul_ite, mul_one, mul_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  · have hv' : LL.vec i = false := by simpa using hv
    simp only [letG, hv', Bool.false_eq_true, if_false, map_sum, map_mul, hC,
      liftSubst_X_cov p f O w LL r g i _ hv', sigMat_inv p f O g hg]
    simp_rw [Finset.sum_mul, mul_assoc, ← map_mul]
    rw [Finset.sum_comm]
    simp_rw [← Finset.mul_sum, ← map_sum, mul_comm (sigMat p f O g (LL.pos i) _ _), ← Matrix.mul_apply, hinv,
      Matrix.one_apply, apply_ite C, map_one, map_zero, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq,
      Finset.mem_univ, if_true]

/- English proof (translation)
Rewrite using `[KKc_eq (O := O) p f LL g z mu c]`. Establish `h1` using `ZZ_map (liftSubst p f O w r LL g).toRingHom p (letG p f (O := O) LL g) LL.pos mu c N le_rfl z J`. Establish `h2` using `ZZ_map (MvPolynomial.map (algebraMap O (KK O))) p (yO w LL) LL.pos mu c N le_rfl z J`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1`. Rewrite using `[h1, h2]`.

Use `congr 1`. Use function extensionality and compare the values at `i b`. Conclude with `lift_letG p f w LL g hg i b`.
-/
lemma lift_KKc (w : O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f)) (hg : IsGLW g)
    (z : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (J : Finset (Fin (r + K))) :
    liftSubst p f O w r LL g (KKc p f (O := O) LL g z mu c J) =
      MvPolynomial.map (algebraMap O (KK O)) (ZZ p (yO w LL) LL.pos mu c N z J) := by
  rw [KKc_eq (O := O) p f LL g z mu c]
  have h1 := ZZ_map (liftSubst p f O w r LL g).toRingHom p (letG p f (O := O) LL g) LL.pos mu c N le_rfl z J
  have h2 := ZZ_map (MvPolynomial.map (algebraMap O (KK O))) p (yO w LL) LL.pos mu c N le_rfl z J
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe] at h1
  rw [h1, h2]
  congr 1
  funext i b
  exact lift_letG p f w LL g hg i b

end LinkG

section MapSg

variable {N r K : ℕ}

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => intro J`. Simplify using `only [SgW]`. Conclude with `extOne_map _ J`. Consider the case `succ j ih`.

Introduce `J`. Simplify using `only [SgW]`. Use `split_ifs with h`. Rewrite using `[colStep_map]`. Use `congr 1`.

Use function extensionality and compare the values at `b`. Simplify using `only [nomL]`. Apply the tactic sequence `split_ifs <;> simp`. Use function extensionality and compare the values at `J'`. Conclude with `ih J'`.

Conclude with `ih J`.
-/
lemma SgW_map {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') (LL : LiftLetters (Fin N))
    (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (j : ℕ) :
    ∀ J, MvPolynomial.map φ (SgW R LL mu c j J) = SgW R' LL mu c j J := by
  induction j with
  | zero => intro J; simp only [SgW]; exact extOne_map _ J
  | succ j ih =>
    intro J
    simp only [SgW]
    split_ifs with h
    · rw [colStep_map]
      congr 1
      · funext b
        simp only [nomL]
        split_ifs <;> simp
      · funext J'
        exact ih J'
    · exact ih J

end MapSg

section Clause4

variable (p f : ℕ) [Fact p.Prime] {O : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O]
  [Algebra (WF p f) O] {N r K : ℕ}

/- English proof (translation)
Establish `: CharP (FF O) p` using `(CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by`. Rewrite using `[← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]`. Conclude with `S.p_mem)`. Take `⟨Y, hY, hYres⟩` from `Inv_main p S LL mu c hmono hposc HV N le_rfl z (fun i _ _ => hz i) J`. Rewrite `hY` using `[oS_top]`.

Use `set o := oc (fun i => p ^ (z - LL.pos i).toNat) mu c with ho`. Set `P : Fin N × Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O` to `fun v => X v ^ p ^ (z - LL.pos v.1).toNat`. Establish `hps : ∀ F : MvPolynomial (Fin N × Fin (r + K)) O, powSubst p LL z F = MvPolynomial.map (algebraMap O (KK O)) (aeval P F)`. Introduce `F`. Proceed by induction on `F using MvPolynomial.induction_on with`.

Consider the case `C a => simp [powSubst, MvPolynomial.algebraMap_eq]`. Consider the case `add F G hF hG => simp only [map_add, hF, hG]`. Consider the case `mul_X F v hF => simp [powSubst, hF, P] at hF ⊢`. Establish `hres : ∀ F : MvPolynomial (Fin N × Fin (r + K)) ℤ, MvPolynomial.map (IsLocalRing.residue O) (aeval P (MvPolynomial.map (Int.castRingHom O) F)) = piS p O LL.pos z F`. Introduce `F`.

Proceed by induction on `F using MvPolynomial.induction_on with`. Consider the case `C a => simp [piS]`. Consider the case `add F G hF hG => simp only [map_add, hF, hG]`. Consider the case `mul_X F v hF => simp [piS, hF, P] at hF ⊢`. Use `set Q := aeval P (SgW O LL mu c N J) with hQ`.

Establish `hQres : MvPolynomial.map (IsLocalRing.residue O) Q = piS p O LL.pos z (SgW ℤ LL mu c N J)`. Rewrite using `[hQ, ← SgW_map (Int.castRingHom O) LL mu c N J, hres]`. Take `⟨T, hT⟩` from `piR_ker p S (Y - Q) (by rw [map_sub, hYres, hQres, sub_self])`. Establish `key : liftSubst p f O S.w r LL g (KKc p f (O` using `O) LL g z mu c J) - C (algebraMap O (KK O) S.w ^ o) * powSubst p LL z (plTanCol O mu c J) = MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ (o + 1)) * T) := by`. Rewrite using `[lift_KKc p f S.w LL g hg z mu c J, hY, hS2 J, hps, ← hQ, ← map_pow]`.

Establish `e : (C ((algebraMap O (KK O)) S.w ^ o) : MvPolynomial (Fin N × Fin (r + K)) (KK O)) = MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ o))`. Rewrite using `[map_C, map_pow (algebraMap O (KK O))]`. Rewrite using `[e, ← map_mul, ← map_sub, ← mul_sub, hT, ← mul_assoc, ← C_mul, ← pow_succ]`. Introduce `m`. Use `⟨T.coeff m, ?_⟩` and prove the remaining obligations.

Rewrite using `[key, coeff_map, coeff_C_mul]`.
-/
theorem lifted_column_congruence (S : UniformizedDVR p O) (LL : LiftLetters (Fin N)) (g : Matrix (Fin (r + K)) (Fin (r + K)) (WF p f))
    (hg : IsGLW g) (z : ℤ) (mu : Fin (N + 1) → Fin (r + K) → ℤ) (c : ℤ) (hmono : Monotone LL.pos)
    (hz : ∀ i, LL.pos i ≤ z)
    (hposc : ∀ i j : Fin N, i < j → IsUsed mu c i → IsCostly mu c j → LL.pos i < LL.pos j)
    (HV : SgVanish LL mu c) (hS2 : ∀ J, plTanCol O mu c J = SgW O LL mu c N J) (J : Finset (Fin (r + K))) :
    InWj S.w (liftSubst p f O S.w r LL g (KKc p f (O := O) LL g z mu c J) -
        C (algebraMap O (KK O) S.w ^ oc (fun i => p ^ (z - LL.pos i).toNat) mu c) *
          powSubst p LL z (plTanCol O mu c J))
      (oc (fun i => p ^ (z - LL.pos i).toNat) mu c + 1) := by
  have : CharP (FF O) p := (CharP.charP_iff_prime_eq_zero (Fact.out : p.Prime)).2 (by
    rw [← map_natCast (IsLocalRing.residue O), IsLocalRing.residue_eq_zero_iff]; exact S.p_mem)
  obtain ⟨Y, hY, hYres⟩ := Inv_main p S LL mu c hmono hposc HV N le_rfl z (fun i _ _ => hz i) J
  rw [oS_top] at hY
  set o := oc (fun i => p ^ (z - LL.pos i).toNat) mu c with ho
  let P : Fin N × Fin (r + K) → MvPolynomial (Fin N × Fin (r + K)) O := fun v => X v ^ p ^ (z - LL.pos v.1).toNat
  have hps : ∀ F : MvPolynomial (Fin N × Fin (r + K)) O,
      powSubst p LL z F = MvPolynomial.map (algebraMap O (KK O)) (aeval P F) := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [powSubst, MvPolynomial.algebraMap_eq]
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F v hF => simp [powSubst, hF, P] at hF ⊢
  have hres : ∀ F : MvPolynomial (Fin N × Fin (r + K)) ℤ,
      MvPolynomial.map (IsLocalRing.residue O) (aeval P (MvPolynomial.map (Int.castRingHom O) F)) =
        piS p O LL.pos z F := by
    intro F
    induction F using MvPolynomial.induction_on with
    | C a => simp [piS]
    | add F G hF hG => simp only [map_add, hF, hG]
    | mul_X F v hF => simp [piS, hF, P] at hF ⊢
  set Q := aeval P (SgW O LL mu c N J) with hQ
  have hQres : MvPolynomial.map (IsLocalRing.residue O) Q = piS p O LL.pos z (SgW ℤ LL mu c N J) := by
    rw [hQ, ← SgW_map (Int.castRingHom O) LL mu c N J, hres]
  obtain ⟨T, hT⟩ := piR_ker p S (Y - Q) (by rw [map_sub, hYres, hQres, sub_self])
  have key : liftSubst p f O S.w r LL g (KKc p f (O := O) LL g z mu c J) -
      C (algebraMap O (KK O) S.w ^ o) * powSubst p LL z (plTanCol O mu c J) =
      MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ (o + 1)) * T) := by
    rw [lift_KKc p f S.w LL g hg z mu c J, hY, hS2 J, hps, ← hQ, ← map_pow]
    have e : (C ((algebraMap O (KK O)) S.w ^ o) : MvPolynomial (Fin N × Fin (r + K)) (KK O)) =
        MvPolynomial.map (algebraMap O (KK O)) (C (S.w ^ o)) := by
      rw [map_C, map_pow (algebraMap O (KK O))]
    rw [e, ← map_mul, ← map_sub, ← mul_sub, hT, ← mul_assoc, ← C_mul, ← pow_succ]
  intro m
  refine ⟨T.coeff m, ?_⟩
  rw [key, coeff_map, coeff_C_mul]

end Clause4

end Formalism.MainNotions.LemmaBAlt
