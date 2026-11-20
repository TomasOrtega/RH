import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsTestRep

open GlobalTheory.JR Matrix MeasureTheory Filter Topology

noncomputable section

namespace GlobalTheory.JR.LinDesc

variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

def bas (hG : A.IsGen τ p) : Module.Basis (Fin r) F A.K :=
  basisOfLinearIndependentOfCardEqFinrank' _ hG.1 (by rw [hG.2.1]; simp)

def pt (hG : A.IsGen τ p) (lam : F) (b c : A.K) : Gl r F :=
  (companion p, (bas A hG).equivFun b, fun i => Algebra.trace F A.K (τ ^ (i : ℕ) * c), lam)

def tm (hG : A.IsGen τ p) : A.Kˣ →* GL (Fin r) F :=
  Units.map (Algebra.leftMulMatrix (bas A hG)).toRingHom.toMonoidHom

def unitsMeas (μK : Measure A.K) : Measure A.Kˣ :=
  (μK.withDensity fun t => ENNReal.ofReal (A.absK t)⁻¹).comap Units.val

def desc (M : Meas r F E)
    (hG : A.IsGen τ p) (lam : F) (α : GL (Fin r) F → ℝ) (f' : Gl r F → ℂ) (x : A.K × A.K) : ℂ :=
  letI := M.mG
  ∫ g, f' (act g (pt A hG lam x.1 x.2)) * eta ((g : Matrix (Fin r) (Fin r) F).det) * (α g : ℂ) ∂M.μG

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

/- English proof (translation)
Simplify using `[LinDesc.bas]`.
-/
theorem bas_apply (hG : A.IsGen τ p) (i : Fin r) : LinDesc.bas A hG i = τ ^ (i : ℕ) := by
  simp [LinDesc.bas]

/- English proof (translation)
Establish `: (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c`. Rewrite using `[Module.Basis.equivFun_symm_apply]`. Simplify using `[bas_apply]`. Rewrite using `[this]`. Use extensionality with `i`.

Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Simplify using the standard rewrite rules.
-/
theorem repr_sum (hG : A.IsGen τ p) (c : Fin r → F) :
    (LinDesc.bas A hG).repr (∑ i, c i • τ ^ (i : ℕ)) = Finsupp.equivFunOnFinite.symm c := by
  have : (∑ i, c i • τ ^ (i : ℕ)) = (LinDesc.bas A hG).equivFun.symm c := by
    rw [Module.Basis.equivFun_symm_apply]; simp [bas_apply]
  rw [this]
  ext i
  rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]; simp

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']`. Simplify using `only [companion, Matrix.of_apply]`. Distinguish the cases in `hj : (j : ℕ) + 1 = r`. Rewrite using `[if_pos hj, hj]`.

Establish `h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ)`. Use `hG.2.2` as an intermediate fact. Simplify using `only [neg_smul, Finset.sum_neg_distrib]`. Conclude with `eq_neg_of_add_eq_zero_left this`. Rewrite using `[h3, repr_sum]`.

Simplify using the standard rewrite rules. Rewrite using `[if_neg hj]`. Establish `hlt : (j : ℕ) + 1 < r` using `lt_of_le_of_ne j.2 hj`. Establish `h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩` using `by rw [bas_apply]`. Rewrite using `[h3, Module.Basis.repr_self, Finsupp.single_apply]`.

Distinguish the cases in `hi : (i : ℕ) = (j : ℕ) + 1`. Rewrite using `[if_pos hi, if_pos (Fin.ext hi.symm)]`. Rewrite using `[if_neg hi, if_neg]`. Introduce `h; exact hi (by rw [← h])`.
-/
theorem leftMul_tau (hG : A.IsGen τ p) : Algebra.leftMulMatrix (LinDesc.bas A hG) τ = companion p := by
  ext i j
  rw [Algebra.leftMulMatrix_eq_repr_mul, bas_apply, ← pow_succ']
  simp only [companion, Matrix.of_apply]
  by_cases hj : (j : ℕ) + 1 = r
  · rw [if_pos hj, hj]
    have h3 : τ ^ r = ∑ k, (-p k) • τ ^ (k : ℕ) := by
      have := hG.2.2
      simp only [neg_smul, Finset.sum_neg_distrib]
      exact eq_neg_of_add_eq_zero_left this
    rw [h3, repr_sum]; simp
  · rw [if_neg hj]
    have hlt : (j : ℕ) + 1 < r := lt_of_le_of_ne j.2 hj
    have h3 : τ ^ ((j : ℕ) + 1) = LinDesc.bas A hG ⟨(j : ℕ) + 1, hlt⟩ := by rw [bas_apply]
    rw [h3, Module.Basis.repr_self, Finsupp.single_apply]
    by_cases hi : (i : ℕ) = (j : ℕ) + 1
    · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
    · rw [if_neg hi, if_neg]
      intro h; exact hi (by rw [← h])

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
variable {F E : Type} [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E]
  (A : Et F E) {r : ℕ} {τ : A.K} {p : Fin r → F}

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem tm_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) = Algebra.leftMulMatrix (bas A hG) (t : A.K) := rfl

/- English proof (translation)
Rewrite using `[← map_inv]`. Both sides reduce to the same expression.
-/
theorem tm_inv_coe (hG : A.IsGen τ p) (t : A.Kˣ) :
    (((tm A hG t)⁻¹ : GL (Fin r) F) : Matrix (Fin r) (Fin r) F) =
      Algebra.leftMulMatrix (bas A hG) ((t⁻¹ : A.Kˣ) : A.K) := by
  rw [← map_inv]; rfl

/- English proof (translation)
Use function extensionality and compare the values at `j`. Simplify using `only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]`. Establish `hx` using `(bas A hG).sum_repr (s * bas A hG j)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]`. Use `_ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by`. Rewrite using `[← Finset.sum_mul, hx, bas_apply]`. Put the polynomial expressions in normal form.
-/
theorem row_mul (hG : A.IsGen τ p) (s c : A.K) :
    (fun i : Fin r => Algebra.trace F A.K (τ ^ (i : ℕ) * c)) ᵥ* Algebra.leftMulMatrix (bas A hG) s =
      fun j : Fin r => Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
  funext j
  simp only [Matrix.vecMul, dotProduct, Algebra.leftMulMatrix_eq_repr_mul]
  have hx := (bas A hG).sum_repr (s * bas A hG j)
  calc ∑ i : Fin r, Algebra.trace F A.K (τ ^ (i : ℕ) * c) * (bas A hG).repr (s * bas A hG j) i
      = Algebra.trace F A.K (∑ i : Fin r, ((bas A hG).repr (s * bas A hG j) i • bas A hG i) * c) := by
        rw [map_sum]; refine Finset.sum_congr rfl fun i _ => ?_
        rw [smul_mul_assoc, map_smul, smul_eq_mul, mul_comm, bas_apply A hG i]
    _ = Algebra.trace F A.K (τ ^ (j : ℕ) * (s * c)) := by
        rw [← Finset.sum_mul, hx, bas_apply]; ring_nf

/- English proof (translation)
Unfold `act pt`. Rewrite using `[tm_inv_coe, tm_coe]`. Use `Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))` and prove the remaining obligations. Simplify using `only`. Rewrite using `[← leftMul_tau A hG, ← map_mul, ← map_mul]`.

Use `congr 1`. Rewrite using `[mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]`. Simplify using `only`. Rewrite using `[Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]`. Conclude with `Algebra.leftMulMatrix_mulVec_repr _ _ _`.

Conclude with `row_mul A hG _ c`.
-/
theorem act_tm (hG : A.IsGen τ p) (lam : F) (t : A.Kˣ) (b c : A.K) :
    act (tm A hG t) (pt A hG lam b c) = pt A hG lam ((t : A.K) * b) (((t⁻¹ : A.Kˣ) : A.K) * c) := by
  unfold act pt
  rw [tm_inv_coe, tm_coe]
  refine Prod.ext ?_ (Prod.ext ?_ (Prod.ext ?_ rfl))
  · simp only
    rw [← leftMul_tau A hG, ← map_mul, ← map_mul]; congr 1
    rw [mul_comm (t : A.K) τ, mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, mul_one]
  · simp only
    rw [Module.Basis.equivFun_apply, Module.Basis.equivFun_apply]
    exact Algebra.leftMulMatrix_mulVec_repr _ _ _
  · exact row_mul A hG _ c

/- English proof (translation)
Rewrite using `[tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]`.
-/
theorem det_tm (hG : A.IsGen τ p) (t : A.Kˣ) :
    ((tm A hG t : GL (Fin r) F) : Matrix (Fin r) (Fin r) F).det = Algebra.norm F (t : A.K) := by
  rw [tm_coe, Algebra.norm_eq_matrix_det (bas A hG)]

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc

/- English proof (translation)
Unfold `act`. Simplify using `only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]`.
-/
theorem act_mul {r : ℕ} {k : Type} [CommRing k] (g h : GL (Fin r) k) (Y : Gl r k) :
    act (g * h) Y = act g (act h Y) := by
  unfold act
  simp only [_root_.mul_inv_rev, Units.val_mul, Matrix.mulVec_mulVec, Matrix.vecMul_vecMul, Matrix.mul_assoc]

/- English proof (translation)
Unfold `act`. Simplify using the standard rewrite rules.
-/
theorem act_one {r : ℕ} {k : Type} [CommRing k] (Y : Gl r k) : act 1 Y = Y := by
  unfold act; simp

end GlobalTheory.JR.LinDesc

namespace GlobalTheory.JR.LinDesc
/- English proof (translation)
Introduce `F E _ _ _ _ _ A r τ p hG lam a`. Unfold `LinDesc.pt sec Et.invK`. Use `congr 1`. Use `Prod.ext ?_ rfl` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩`. Simplify using `[LinDesc.bas]`. Simplify using `only`. Rewrite using `[h1, Module.Basis.equivFun_self]`. Distinguish the cases in `hi : (i : ℕ) = 0`.

Rewrite using `[if_pos hi, if_pos (Fin.ext hi.symm)]`. Rewrite using `[if_neg hi, if_neg]`. Introduce `h; exact hi (by rw [← h])`.
-/
theorem pt_one : ∀ (F E : Type) [NontriviallyNormedField F] [NontriviallyNormedField E] [NormedAlgebra F E] [StarRing E] [Unram F E] (A : Et F E) (r : ℕ) (τ : A.K) (p : Fin r → F) (hG : A.IsGen τ p) (lam : F), ∀ a : A.K, LinDesc.pt A hG lam 1 a = sec (A.invK τ p lam a) := by
  intro F E _ _ _ _ _ A r τ p hG lam a
  unfold LinDesc.pt sec Et.invK
  congr 1
  refine Prod.ext ?_ rfl
  funext i
  have h1 : (1 : A.K) = LinDesc.bas A hG ⟨0, Fin.pos i⟩ := by
    simp [LinDesc.bas]
  simp only
  rw [h1, Module.Basis.equivFun_self]
  by_cases hi : (i : ℕ) = 0
  · rw [if_pos hi, if_pos (Fin.ext hi.symm)]
  · rw [if_neg hi, if_neg]
    intro h; exact hi (by rw [← h])
end GlobalTheory.JR.LinDesc
