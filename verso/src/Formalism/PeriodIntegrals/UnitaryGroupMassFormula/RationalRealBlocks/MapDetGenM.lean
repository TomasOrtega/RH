import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.EvenStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.RationalRealBlocks.Bridge
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.OddDualWeylJacobian.OddDualWeylFactorization

open MvPolynomial Matrix

noncomputable section

namespace PI.BlockRatReal.UnitaryGroupMassFormula.Odd

open PI.OddDualWeyl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[genM]`.
-/
theorem map_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    (MvPolynomial.map φ).mapMatrix (genM R k) = genM S k := by
  ext i j; simp [genM]

/- English proof (translation)
Establish `h` using `congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map φ) (genM R k)) (Fin.rev j)) i`. Rewrite `h` using `[map_genM]`. Simplify `h` using `[dualM, RingHom.mapMatrix_apply, Matrix.map_apply]`.
-/
theorem map_dualM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) (i j : Fin k) :
    MvPolynomial.map φ (dualM R k i j) = dualM S k i j := by
  have h := congrFun (congrFun (RingHom.map_adjugate (MvPolynomial.map φ) (genM R k)) (Fin.rev j)) i
  rw [map_genM] at h
  simpa [dualM, RingHom.mapMatrix_apply, Matrix.map_apply] using h

/- English proof (translation)
Rewrite using `[RingHom.map_det, map_genM]`.
-/
theorem map_det_genM {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ) :
    MvPolynomial.map φ (genM R k).det = (genM S k).det := by
  rw [RingHom.map_det, map_genM]

/- English proof (translation)
Proceed by induction on `p using MvPolynomial.induction_on with`. Consider the case `C a => simp [dualSub]`. Consider the case `add p q hp hq => simp only [map_add, hp, hq]`. Consider the case `mul_X p v hp`. Simplify using `only [map_mul, hp, map_X]`.

Use `congr 1`. Simplify using `only [dualSub, aeval_X]`. Conclude with `map_dualM φ k v.1 v.2`.
-/
theorem map_dualSub {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k : ℕ)
    (p : MvPolynomial (Fin k × Fin k) R) :
    MvPolynomial.map φ (dualSub R k p) = dualSub S k (MvPolynomial.map φ p) := by
  induction p using MvPolynomial.induction_on with
  | C a => simp [dualSub]
  | add p q hp hq => simp only [map_add, hp, hq]
  | mul_X p v hp =>
    simp only [map_mul, hp, map_X]
    congr 1
    simp only [dualSub, aeval_X]
    exact map_dualM φ k v.1 v.2

/- English proof (translation)
Unfold `PI.OddDualWeyl.Rel at *`. Rewrite using `[← map_dualSub, h, map_mul, map_pow, map_det_genM]`.
-/
theorem rel_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) (k M : ℕ)
    (f f' : MvPolynomial (Fin k × Fin k) R) (h : PI.OddDualWeyl.Rel R k M f f') :
    PI.OddDualWeyl.Rel S k M (MvPolynomial.map φ f) (MvPolynomial.map φ f') := by
  unfold PI.OddDualWeyl.Rel at *
  rw [← map_dualSub, h, map_mul, map_pow, map_det_genM]

/- English proof (translation)
Simplify using `only [sgnK]`. Rewrite using `[RingHom.map_det]`. Use `congr 1`. Use extensionality with `i j`. Simplify using `only [RingHom.mapMatrix_apply, Matrix.map_apply, revCol, Matrix.submatrix_apply, id, Matrix.one_apply]`.

Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem sgnK_map {LL : Type} [Field LL] (φ : LL →+* ℂ) (m : ℕ) : φ (sgnK LL m) = sgnK ℂ m := by
  simp only [sgnK]
  rw [RingHom.map_det]
  congr 1
  ext i j
  simp only [RingHom.mapMatrix_apply, Matrix.map_apply, revCol, Matrix.submatrix_apply, id,
    Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Establish `hgen : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ), PI.OddDualWeyl.MH R (PI.OddDualWeyl.applyWord R w (PI.OddDualWeyl.hw R le_rfl (PI.OddDualWeyl.nuOf lam))) ∧ ∃ f' ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf (lamStar lam)), PI.OddDualWeyl.Rel R (m + 1) (ex …`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil`. Rewrite using `[PI.OddDualWeyl.applyWord_nil]`.

Use `⟨PI.OddDualWeyl.highest_weight_multiplicity R (m + 1) _, ?_⟩` and prove the remaining obligations. Take `⟨u, -, hu⟩` from `PI.OddDualWeyl.highestWeightDual_of PI.OddDualWeyl.jacobiMinorReverse R m lam hlam`. Use `⟨C u * PI.OddDualWeyl.low R (PI.OddDualWeyl.nuOf (lamStar lam)), ?_, hu⟩` and prove the remaining obligations. Rewrite using `[MvPolynomial.C_mul']`. Conclude with `Submodule.smul_mem _ u (PI.OddDualWeyl.lowestWeightMem R (m + 1) _)`.

Consider the case `cons x w ih`. Take `⟨hMH, f', hf', hrel⟩` from `ih`. Rewrite using `[PI.OddDualWeyl.applyWord_cons]`. Use `⟨PI.OddDualWeyl.highest_weight_divisibility R (m + 1) _ _ _ _ hMH, ?_⟩` and prove the remaining obligations. Distinguish the cases in `hab : x.1 = x.2.1`.

Take `⟨d, hd⟩` from `hMH x.1`. Establish `hdiag` using `PI.OddDualWeyl.hermitianDiagonalization R (m + 1) x.1 x.2.2 d _ hd`. Rewrite using `[← hab, hdiag]`. Use `⟨(d.choose x.2.2 : MvPolynomial _ R) * f', ?_, PI.OddDualWeyl.rel_natMul _ hrel⟩` and prove the remaining obligations. Rewrite using `[← nsmul_eq_mul]`.

Conclude with `Submodule.smul_of_tower_mem _ _ hf'`. Use `⟨(-1) ^ x.2.2 * PI.OddDualWeyl.rowDiv R x.2.1 x.1 x.2.2 f', ?_, PI.OddDualWeyl.rowOpIntertwining R (m + 1) _ x.1 x.2.1 x.2.2 _ _ hab hrel⟩` and prove the remaining obligations. Establish `hm` using `PI.OddDualWeyl.weyl_rowDiv x.2.1 x.1 x.2.2 hf'`. Break down `neg_one_pow_eq_or (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) x.2.2 with h | h` into its components or cases. Rewrite using `[h, one_mul]`.

Conclude with `hm`. Rewrite using `[h, neg_one_mul]`. Conclude with `Submodule.neg_mem _ hm`. Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem g hg`.

Take `⟨w, rfl⟩` from `hg`. Conclude with `(hgen w).2`. Consider the case `zero => exact ⟨0, Submodule.zero_mem _, PI.OddDualWeyl.rel_zero⟩`. Consider the case `add g h _ _ hg hh`. Take `⟨g', hg', hrg⟩` from `hg`.

Take `⟨h', hh', hrh⟩` from `hh`. Conclude with `⟨g' + h', Submodule.add_mem _ hg' hh', PI.OddDualWeyl.rel_add hrg hrh⟩`. Consider the case `smul c g _ hg`. Take `⟨g', hg', hrg⟩` from `hg`. Conclude with `⟨c • g', Submodule.smul_mem _ c hg', PI.OddDualWeyl.rel_smul c hrg⟩`.
-/
private theorem exists_weyl_lamStar_rel_of_mem_weyl (R : Type) [CommRing R] (m : ℕ) (lam : Fin (m + 1) → ℤ)
    (hlam : Antitone lam) (f : MvPolynomial (Fin (m + 1) × Fin (m + 1)) R)
    (hf : f ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf lam)) :
    ∃ f' ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf (lamStar lam)),
      PI.OddDualWeyl.Rel R (m + 1) (expM lam) f f' := by
  have hgen : ∀ w : List (Fin (m + 1) × Fin (m + 1) × ℕ),
      PI.OddDualWeyl.MH R (PI.OddDualWeyl.applyWord R w
        (PI.OddDualWeyl.hw R le_rfl (PI.OddDualWeyl.nuOf lam))) ∧
      ∃ f' ∈ PI.OddDualWeyl.weyl R (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf (lamStar lam)),
        PI.OddDualWeyl.Rel R (m + 1) (expM lam)
          (PI.OddDualWeyl.applyWord R w (PI.OddDualWeyl.hw R le_rfl (PI.OddDualWeyl.nuOf lam))) f' := by
    intro w
    induction w with
    | nil =>
      rw [PI.OddDualWeyl.applyWord_nil]
      refine ⟨PI.OddDualWeyl.highest_weight_multiplicity R (m + 1) _, ?_⟩
      obtain ⟨u, -, hu⟩ := PI.OddDualWeyl.highestWeightDual_of PI.OddDualWeyl.jacobiMinorReverse R m lam hlam
      refine ⟨C u * PI.OddDualWeyl.low R (PI.OddDualWeyl.nuOf (lamStar lam)), ?_, hu⟩
      rw [MvPolynomial.C_mul']
      exact Submodule.smul_mem _ u (PI.OddDualWeyl.lowestWeightMem R (m + 1) _)
    | cons x w ih =>
      obtain ⟨hMH, f', hf', hrel⟩ := ih
      rw [PI.OddDualWeyl.applyWord_cons]
      refine ⟨PI.OddDualWeyl.highest_weight_divisibility R (m + 1) _ _ _ _ hMH, ?_⟩
      by_cases hab : x.1 = x.2.1
      · obtain ⟨d, hd⟩ := hMH x.1
        have hdiag := PI.OddDualWeyl.hermitianDiagonalization R (m + 1) x.1 x.2.2 d _ hd
        rw [← hab, hdiag]
        refine ⟨(d.choose x.2.2 : MvPolynomial _ R) * f', ?_, PI.OddDualWeyl.rel_natMul _ hrel⟩
        rw [← nsmul_eq_mul]
        exact Submodule.smul_of_tower_mem _ _ hf'
      · refine ⟨(-1) ^ x.2.2 * PI.OddDualWeyl.rowDiv R x.2.1 x.1 x.2.2 f', ?_,
          PI.OddDualWeyl.rowOpIntertwining R (m + 1) _ x.1 x.2.1 x.2.2 _ _ hab hrel⟩
        have hm := PI.OddDualWeyl.weyl_rowDiv x.2.1 x.1 x.2.2 hf'
        rcases neg_one_pow_eq_or (MvPolynomial (Fin (m + 1) × Fin (m + 1)) R) x.2.2 with h | h
        · rw [h, one_mul]
          exact hm
        · rw [h, neg_one_mul]
          exact Submodule.neg_mem _ hm
  induction hf using Submodule.span_induction with
  | mem g hg =>
    obtain ⟨w, rfl⟩ := hg
    exact (hgen w).2
  | zero => exact ⟨0, Submodule.zero_mem _, PI.OddDualWeyl.rel_zero⟩
  | add g h _ _ hg hh =>
    obtain ⟨g', hg', hrg⟩ := hg
    obtain ⟨h', hh', hrh⟩ := hh
    exact ⟨g' + h', Submodule.add_mem _ hg' hh', PI.OddDualWeyl.rel_add hrg hrh⟩
  | smul c g _ hg =>
    obtain ⟨g', hg', hrg⟩ := hg
    exact ⟨c • g', Submodule.smul_mem _ c hg', PI.OddDualWeyl.rel_smul c hrg⟩

/- English proof (translation)
Introduce `m LL _ embLL lam hlam M0 f hf`. Establish `hf0 : f ∈ PI.OddDualWeyl.weyl ℤ (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf lam)` using `hf`. Take `⟨f', hf', hrel⟩` from `exists_weyl_lamStar_rel_of_mem_weyl ℤ m lam hlam f hf0`. Establish `hstar : Antitone (lamStar lam)` using `PI.OddDualWeyl.antitone_lamStar hlam`. Establish `hν : Antitone (PI.BlockRatReal.nuOf (fun i : Fin (m + 1) => -lam i.rev))`.

Introduce `i j hij`. Conclude with `Int.toNat_le_toNat (sub_le_sub_right (hstar hij) _)`. Use `set e' : ℤ := -lam (Fin.last m).rev with he'`. Use `set c : LL := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' * sgnK LL m ^ e' with hc`. Use `⟨C c * Formalism.GradedWeylDivisibility.rowAct LL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ (MvPolynomial.map (Int.castRingHom LL) f'), ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[MvPolynomial.C_mul']`. Use `Submodule.smul_mem _ c ?_` and prove the remaining obligations. Conclude with `PI.BlockRatReal.UnitaryGroupMassFormula.s2 _ _ _ _ (PI.BlockRatReal.UnitaryGroupMassFormula.s1 (Int.castRingHom LL) (m + 1) _ hν f' hf')`. Introduce `y hy`. Establish `hdet0 : IsUnit (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det` using `(Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit`.

Use `set Mc := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL with hMc`. Establish `hdetMc : Mc.det = embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det`. Rewrite using `[RingHom.map_det, RingHom.mapMatrix_apply]`. Establish `ha : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ≠ 0` using `(map_ne_zero embLL).mpr hdet0.ne_zero`. Establish `hU : IsUnit Mc.det`.

Rewrite using `[hdetMc]`. Conclude with `isUnit_iff_ne_zero.mpr ha`. Establish `hz : revCol ((Mc * y)⁻¹ᵀ) = Mc⁻¹ᵀ * revCol y⁻¹ᵀ`. Rewrite using `[Matrix.mul_inv_rev, Matrix.transpose_mul, revCol_eq (Mc⁻¹ᵀ * y⁻¹ᵀ), revCol_eq y⁻¹ᵀ, Matrix.mul_assoc]`. Establish `hz' : ((Mc * y)⁻¹ᵀ).submatrix id Fin.rev = Mc⁻¹ᵀ * revCol y⁻¹ᵀ` using `hz`.

Establish `hg : ((M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ).map embLL * Mc⁻¹ᵀ = 1`. Rewrite using `[Matrix.transpose_map, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU, Matrix.transpose_one]`. Establish `hev` using `PI.OddDualWeyl.evalDuality ℂ m (lam (Fin.last m)) e' (PI.OddDualWeyl.degW (PI.OddDualWeyl.nuOf (lamStar lam))) (expM lam) (MvPolynomial.map (Int.castRingHom ℂ) f) (MvPolynomial.map (Int.castRingHom ℂ) f') (PI.OddDualWeyl.degreeBalance m lam hlam) (rel_map (Int.castRingHom ℂ) (m + …`. Rewrite using `[hev]`. Rewrite using `[map_mul, map_C, map_mul, eval_C, PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct, hz', ← Matrix.mul_assoc, hg, Matrix.one_mul, PI.BlockRatReal.UnitaryGroupMassFormula.map_map_int]`.

Rewrite using `[Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, hdetMc, Ring.inverse_eq_inv']`. Rewrite using `[hc]`. Simplify using `only [map_mul, eval_C, map_zpow₀, sgnK_map]`. Rewrite using `[mul_zpow, _root_.inv_zpow]`. Establish `hA : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' ≠ 0` using `zpow_ne_zero _ ha`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem oddStep : PI.BlockRatReal.OddStep := by
  intro m LL _ embLL lam hlam M0 f hf
  have hf0 : f ∈ PI.OddDualWeyl.weyl ℤ (m + 1) (m + 1) le_rfl (PI.OddDualWeyl.nuOf lam) := hf
  obtain ⟨f', hf', hrel⟩ := exists_weyl_lamStar_rel_of_mem_weyl ℤ m lam hlam f hf0
  have hstar : Antitone (lamStar lam) := PI.OddDualWeyl.antitone_lamStar hlam
  have hν : Antitone (PI.BlockRatReal.nuOf (fun i : Fin (m + 1) => -lam i.rev)) := by
    intro i j hij
    exact Int.toNat_le_toNat (sub_le_sub_right (hstar hij) _)
  set e' : ℤ := -lam (Fin.last m).rev with he'
  set c : LL := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' * sgnK LL m ^ e' with hc
  refine ⟨C c * Formalism.GradedWeylDivisibility.rowAct LL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ
    (MvPolynomial.map (Int.castRingHom LL) f'), ?_, ?_⟩
  · rw [MvPolynomial.C_mul']
    refine Submodule.smul_mem _ c ?_
    exact PI.BlockRatReal.UnitaryGroupMassFormula.s2 _ _ _ _
      (PI.BlockRatReal.UnitaryGroupMassFormula.s1 (Int.castRingHom LL) (m + 1) _ hν f' hf')
  · intro y hy
    have hdet0 : IsUnit (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det :=
      (Matrix.isUnit_iff_isUnit_det _).mp M0.isUnit
    set Mc := (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).map embLL with hMc
    have hdetMc : Mc.det = embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det := by
      rw [RingHom.map_det, RingHom.mapMatrix_apply]
    have ha : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ≠ 0 :=
      (map_ne_zero embLL).mpr hdet0.ne_zero
    have hU : IsUnit Mc.det := by
      rw [hdetMc]
      exact isUnit_iff_ne_zero.mpr ha
    have hz : revCol ((Mc * y)⁻¹ᵀ) = Mc⁻¹ᵀ * revCol y⁻¹ᵀ := by
      rw [Matrix.mul_inv_rev, Matrix.transpose_mul, revCol_eq (Mc⁻¹ᵀ * y⁻¹ᵀ), revCol_eq y⁻¹ᵀ,
        Matrix.mul_assoc]
    have hz' : ((Mc * y)⁻¹ᵀ).submatrix id Fin.rev = Mc⁻¹ᵀ * revCol y⁻¹ᵀ := hz
    have hg : ((M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL)ᵀ).map embLL * Mc⁻¹ᵀ = 1 := by
      rw [Matrix.transpose_map, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hU,
        Matrix.transpose_one]
    have hev := PI.OddDualWeyl.evalDuality ℂ m (lam (Fin.last m)) e'
      (PI.OddDualWeyl.degW (PI.OddDualWeyl.nuOf (lamStar lam))) (expM lam)
      (MvPolynomial.map (Int.castRingHom ℂ) f) (MvPolynomial.map (Int.castRingHom ℂ) f')
      (PI.OddDualWeyl.degreeBalance m lam hlam)
      (rel_map (Int.castRingHom ℂ) (m + 1) _ f f' hrel)
      ((PI.OddDualWeyl.weight_homomorphism ℤ (m + 1) _ f' hf').map (Int.castRingHom ℂ)) y hy
    rw [hev]
    rw [map_mul, map_C, map_mul, eval_C, PI.BlockRatReal.UnitaryGroupMassFormula.eval_map_rowAct, hz',
      ← Matrix.mul_assoc, hg, Matrix.one_mul, PI.BlockRatReal.UnitaryGroupMassFormula.map_map_int]
    rw [Matrix.det_mul, Matrix.det_transpose, Matrix.det_nonsing_inv, hdetMc, Ring.inverse_eq_inv']
    rw [hc]
    simp only [map_mul, eval_C, map_zpow₀, sgnK_map]
    rw [mul_zpow, _root_.inv_zpow]
    have hA : embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e' ≠ 0 := zpow_ne_zero _ ha
    calc _ = ((embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e')⁻¹ *
          embLL (M0 : Matrix (Fin (m + 1)) (Fin (m + 1)) LL).det ^ e') *
          ((revCol y⁻¹ᵀ).det ^ e' * (sgnK ℂ m ^ e' *
            (eval fun x => revCol y⁻¹ᵀ x.1 x.2) ((MvPolynomial.map (Int.castRingHom ℂ)) f'))) := by ring
      _ = _ := by rw [inv_mul_cancel₀ hA, one_mul]

end PI.BlockRatReal.UnitaryGroupMassFormula.Odd
