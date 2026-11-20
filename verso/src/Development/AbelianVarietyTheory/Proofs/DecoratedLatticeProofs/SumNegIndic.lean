import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsCoType
import Formalism.LocalToGlobal.Columns.HeckeSp
open MeasureTheory ValuativeRel Matrix GlobalTheory.PRep GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.Doubling GlobalTheory.GLDoubling GlobalTheory.IndefiniteRowSideFullHecke.VolumeFlatSection GlobalTheory.ZonalCellDecomposition GlobalTheory.SatakeBound GlobalTheory.ParHecke

noncomputable section
namespace GlobalTheory.TorusRightScalar

/- English proof (translation)
Use `ext`. Rewrite using `[GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val, Fintype.prod_sum_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]`. Proceed by induction on `(Finset.univ : Finset D) using Finset.induction_on with`. Consider the case `empty => simp`.

Consider the case `insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]`.
-/
theorem det_mtor' {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]
    {A D : Type} [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] (ϖ : kˣ) (e : D → ℤ) :
    GeneralLinearGroup.det (mtor ϖ e : GL (A ⊕ D) k) = ϖ ^ ∑ i, e i := by
  ext
  rw [GeneralLinearGroup.val_det_apply, mtor, val_torusElt, det_diagonal, Units.val_zpow_eq_zpow_val,
    Fintype.prod_sum_type]
  simp only [Sum.elim_inl, Sum.elim_inr, Pi.zero_apply, zpow_zero, Finset.prod_const_one, one_mul]
  induction (Finset.univ : Finset D) using Finset.induction_on with
  | empty => simp
  | insert i t hi ih => rw [Finset.prod_insert hi, Finset.sum_insert hi, zpow_add₀ (Units.ne_zero ϖ), ih]

/- English proof (translation)
Simplify using `[indic, Finset.sum_neg_distrib, Finset.sum_ite_mem]`.
-/
theorem sum_neg_indic {D : Type} [Fintype D] [DecidableEq D] (s : Finset D) :
    ∑ i, (-indic s) i = -(s.card : ℤ) := by
  simp [indic, Finset.sum_neg_distrib, Finset.sum_ite_mem]

/- English proof (translation)
Introduce `k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hun s j hj u y`. Establish `hjK : j ∈ KO k (A ⊕ D)` using `(mem_parahoric.1 hj).1`. Establish `hn1 : nabs k (GeneralLinearGroup.det j) = 1` using `nabs_det_of_mem_KO hjK`. Establish `hv1 : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1` using `(nabs_eq_one_iff _).1 hn1`. Establish `hxi : μT (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j)`.

Use `hun _ hv1` as an intermediate fact. Rewrite `this` using `[MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one]`. Conclude with `this`. Establish `hdet : GeneralLinearGroup.det (j * mtor ϖ (-indic s)) = GeneralLinearGroup.det j * ϖ ^ (-(s.card : ℤ))`. Rewrite using `[map_mul, det_mtor', sum_neg_indic]`.

Establish `hq0 : (0 : ℝ) < resCard k`. Establish `q1 : 1 < Nat.card 𝓀[k]` using `Finite.one_lt_card`. Unfold `resCard`. Conclude with `(lt_trans one_pos q1)` after adjusting the coercions. Establish `hnabs : nabs k (GeneralLinearGroup.det (j * mtor ϖ (-indic s))) = (resCard k : ℝ) ^ s.card`.

Rewrite using `[map_mul, show nabs k (GeneralLinearGroup.det j * GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) = nabs k (GeneralLinearGroup.det j) * nabs k (GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) by`. Simplify using `[nabs, map_mul], hn1, one_mul, mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]`. Simplify using `[indic, Finset.sum_ite_mem]`. Establish `hpow : ((resCard k : ℝ) ^ s.card) ^ ((Fintype.card (A ⊕ D') : ℝ) / 2) = (Real.sqrt (resCard k)) ^ (s.card * (Fintype.card A + Fintype.card D'))`. Rewrite using `[Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le, ← Real.rpow_mul hq0.le, Fintype.card_sum]`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [omTwo, om, map_one, inv_one, Units.val_one, one_smul, Matrix.one_mul, hnabs, hpow]`. Establish `h1 : nabs k 1 = 1` using `by simp [nabs]`.

Rewrite using `[h1, Real.one_rpow, hdet, map_mul, map_zpow, MonoidHom.inv_apply, MonoidHom.inv_apply, hxi]`. Use `push_cast`. Simplify using `only [_root_.zpow_neg, zpow_natCast]`. Rewrite using `[inv_pow, inv_inv]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem torusRight : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (A D D' : Type) [Fintype A] [DecidableEq A] [Fintype D] [DecidableEq D] [Fintype D'] [DecidableEq D'] (ϖ : kˣ), valuation k (ϖ : k) = uniformizer k → ∀ (ξ μS μT : kˣ →* ℂˣ), IsUnram (μT * ξ⁻¹) → ∀ (s : Finset D) (j : GL (A ⊕ D) k), j ∈ parahoric k A D → ∀ (u : Matrix (A ⊕ D') (A ⊕ D) k → ℂ) (y : Matrix (A ⊕ D') (A ⊕ D) k), omTwo μS μT (j * mtor ϖ (-indic s)) (1 : GL (A ⊕ D') k) u y = (((ξ (GeneralLinearGroup.det j))⁻¹ : ℂˣ) : ℂ) * (μT ϖ : ℂ) ^ s.card * ((Real.sqrt (resCard k) : ℝ) : ℂ) ^ (s.card * (Fintype.card A + Fintype.card D')) * u (y * (j * mtor ϖ (-indic s)).1) := by
  intro k _ _ _ _ A D D' _ _ _ _ _ _ ϖ hϖ ξ μS μT hun s j hj u y
  have hjK : j ∈ KO k (A ⊕ D) := (mem_parahoric.1 hj).1
  have hn1 : nabs k (GeneralLinearGroup.det j) = 1 := nabs_det_of_mem_KO hjK
  have hv1 : valuation k ((GeneralLinearGroup.det j : kˣ) : k) = 1 := (nabs_eq_one_iff _).1 hn1
  have hxi : μT (GeneralLinearGroup.det j) = ξ (GeneralLinearGroup.det j) := by
    have := hun _ hv1
    rw [MonoidHom.mul_apply, MonoidHom.inv_apply, mul_inv_eq_one] at this
    exact this
  have hdet : GeneralLinearGroup.det (j * mtor ϖ (-indic s)) =
      GeneralLinearGroup.det j * ϖ ^ (-(s.card : ℤ)) := by
    rw [map_mul, det_mtor', sum_neg_indic]
  have hq0 : (0 : ℝ) < resCard k := by
    have q1 : 1 < Nat.card 𝓀[k] := Finite.one_lt_card
    unfold resCard; exact_mod_cast (lt_trans one_pos q1)
  have hnabs : nabs k (GeneralLinearGroup.det (j * mtor ϖ (-indic s))) = (resCard k : ℝ) ^ s.card := by
    rw [map_mul, show nabs k (GeneralLinearGroup.det j * GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) =
      nabs k (GeneralLinearGroup.det j) * nabs k (GeneralLinearGroup.det (mtor ϖ (-indic s) : GL (A ⊕ D) k)) by
        simp [nabs, map_mul], hn1, one_mul, mtor, nabs_det_torusElt hϖ, Fintype.sum_sum_type]
    simp [indic, Finset.sum_ite_mem]
  have hpow : ((resCard k : ℝ) ^ s.card) ^ ((Fintype.card (A ⊕ D') : ℝ) / 2) =
      (Real.sqrt (resCard k)) ^ (s.card * (Fintype.card A + Fintype.card D')) := by
    rw [Real.sqrt_eq_rpow, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hq0.le,
      ← Real.rpow_mul hq0.le, Fintype.card_sum]
    congr 1
    push_cast
    ring
  simp only [omTwo, om, map_one, inv_one, Units.val_one, one_smul, Matrix.one_mul, hnabs, hpow]
  have h1 : nabs k 1 = 1 := by simp [nabs]
  rw [h1, Real.one_rpow, hdet, map_mul, map_zpow, MonoidHom.inv_apply, MonoidHom.inv_apply, hxi]
  push_cast
  simp only [_root_.zpow_neg, zpow_natCast]
  rw [inv_pow, inv_inv]
  ring

end GlobalTheory.TorusRightScalar
