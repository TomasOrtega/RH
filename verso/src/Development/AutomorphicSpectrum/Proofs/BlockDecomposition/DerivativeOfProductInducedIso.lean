import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsUMOfMem
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantPairingMirabolicVanishing
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ParabolicProductTwoRepsEquivTwoBlockInduction
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsEquivProdIrrTw

noncomputable section

open Matrix GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.BZMir GlobalTheory.BZMir.Leib GlobalTheory.RgGu.Leib GlobalTheory.CompanionTheory.Rodier GlobalTheory.CompanionTheory.BZPsiPG
open scoped TensorProduct

namespace GlobalTheory.CompanionTheory.BZPsiPG.Norm

section Generic

variable {G V W : Type} [Group G] [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W]

def twistEquivOf {ρ : Representation ℂ G V} {σ : Representation ℂ G W} (φ : ρ.Equiv σ) (χ : G →* ℂˣ) :
    (twist ρ χ).Equiv (twist σ χ) :=
  .mk φ.toLinearEquiv fun g => LinearMap.ext fun v => by
    show φ.toLinearEquiv ((χ g : ℂ) • ρ g v) = (χ g : ℂ) • σ g (φ.toLinearEquiv v)
    rw [map_smul]
    exact congrArg _ (LinearMap.congr_fun (φ.isIntertwining' g) v)

def pairT (a : V) (y : W) : ∀ x : Bool, TwoT V W x
  | false => a
  | true => y

/- English proof (translation)
The claim follows from `Exponents.boolTensorEquiv_tprod _`.
-/
theorem bool_tprod_pairT (a : V) (y : W) :
    Exponents.boolTensorEquiv (X := TwoT V W) (PiTensorProduct.tprod ℂ (pairT a y)) = (a ⊗ₜ[ℂ] y : V ⊗[ℂ] W) :=
  Exponents.boolTensorEquiv_tprod _

/- English proof (translation)
Apply `(Exponents.boolTensorEquiv (X := TwoT V W)).injective` to reduce the goal to its premises. Rewrite using `[map_smul, bool_tprod_pairT, bool_tprod_pairT]`. Conclude with `TensorProduct.smul_tmul_smul c d a y`.
-/
theorem tprod_pairT_smul (a : V) (c d : ℂ) (y : W) :
    PiTensorProduct.tprod ℂ (pairT (c • a) (d • y)) = (c * d) • PiTensorProduct.tprod ℂ (pairT a y) := by
  apply (Exponents.boolTensorEquiv (X := TwoT V W)).injective
  rw [map_smul, bool_tprod_pairT, bool_tprod_pairT]
  exact TensorProduct.smul_tmul_smul c d a y

end Generic

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

section Chars

/- English proof (translation)
Use `ext`. Conclude with `GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _`.
-/
theorem det_levi' (n : ℕ) (g : GL (Fin n) k) :
    GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k) = GeneralLinearGroup.det g := by
  ext
  exact GlobalTheory.CompanionTheory.MirPsiPair.det_glEmbMat n _

/- English proof (translation)
Use `ext`. Use `show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1`. Rewrite using `[Matrix.det_of_upperTriangular]`. Use `Finset.prod_eq_one fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = Fin.last n`.

Substitute `hi` using the available equality. Simplify using `[colMat]`. Simplify using `[colMat, hi]`. Introduce `a b hab`. Establish `hb : b ≠ Fin.last n` using `fun h => by`.

Substitute `h` using the available equality. Conclude with `absurd (Fin.le_last a) (not_le.2 hab)`. Establish `hne : a ≠ b` using `fun h => by`. Substitute `h` using the available equality. Conclude with `lt_irrefl _ hab`.

Simplify using `[colMat, hb, Matrix.one_apply, hne]`.
-/
theorem det_unip' (n : ℕ) (v : Multiplicative (Fin n → k)) : GeneralLinearGroup.det (unip k n v) = 1 := by
  ext
  show (1 + colMat k n v.toAdd : Matrix (Fin (n + 1)) (Fin (n + 1)) k).det = 1
  rw [Matrix.det_of_upperTriangular]
  · refine Finset.prod_eq_one fun i _ => ?_
    by_cases hi : i = Fin.last n
    · subst hi
      simp [colMat]
    · simp [colMat, hi]
  · intro a b hab
    have hb : b ≠ Fin.last n := fun h => by
      subst h
      exact absurd (Fin.le_last a) (not_le.2 hab)
    have hne : a ≠ b := fun h => by
      subst h
      exact lt_irrefl _ hab
    simp [colMat, hb, Matrix.one_apply, hne]

/- English proof (translation)
Use `show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _`. Rewrite using `[det_levi']`.
-/
theorem dpowM_levi' (n : ℕ) (s : ℝ) (g : GL (Fin n) k) : dpowM n s (levi k n g) = dpow n s g := by
  show absPow k (s : ℂ) (GeneralLinearGroup.det ((levi k n g : Mir k n) : GL (Fin (n + 1)) k)) = absPow k (s : ℂ) _
  rw [det_levi']

/- English proof (translation)
Take `⟨v, hv⟩` from `(hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)`. Use `show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1`. Establish `hv' : (u : GL (Fin (n + 1)) k) = unip k n v` using `hv.symm`. Rewrite using `[hv', det_unip', map_one]`.
-/
theorem dpowM_of_mem' (n : ℕ) (s : ℝ) (u : Mir k n) (hu : u ∈ MirUin k n) : dpowM n s u = 1 := by
  obtain ⟨v, hv⟩ := (hu : (u : GL (Fin (n + 1)) k) ∈ MirU k n)
  show absPow k (s : ℂ) (GeneralLinearGroup.det (u : GL (Fin (n + 1)) k)) = 1
  have hv' : (u : GL (Fin (n + 1)) k) = unip k n v := hv.symm
  rw [hv', det_unip', map_one]

/- English proof (translation)
Establish `e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2)`. Rewrite using `[← absPow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Establish `e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹`.

Rewrite using `[← absPow_neg, ← absPow_add]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹`.

Rewrite using `[← absPow_neg]`. Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2)`.

Use `congr 1`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e0, e1, e2, e3]`. Simplify using `only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]`.

Generalize the expression as in `absPow k (1 / 2) a = A`. Generalize the expression as in `absPow k (1 / 2) b = B`. Generalize the expression as in `absPow k ((t : ℂ) / 2) a = T`. Generalize the expression as in `absPow k (-(i : ℂ) / 2) b = R`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem scalar_sum (i t : ℕ) (a b : kˣ) :
    absPow k ((-1 / 2 : ℝ) : ℂ) (a * b) * (absPow k 1 b * (absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) a *
        absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) b)) =
      absPow k ((t : ℂ) / 2) a * absPow k (-(i : ℂ) / 2) b * absPow k ((-1 / 2 : ℝ) : ℂ) a := by
  have e0 : absPow k 1 = absPow k (1 / 2) * absPow k (1 / 2) := by
    rw [← absPow_add]
    congr 1
    ring
  have e1 : absPow k ((-((i + 1 : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k (-(i : ℂ) / 2) * (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg, ← absPow_add]
    congr 1
    push_cast
    ring
  have e2 : absPow k ((-1 / 2 : ℝ) : ℂ) = (absPow k (1 / 2))⁻¹ := by
    rw [← absPow_neg]
    congr 1
    push_cast
    ring
  have e3 : absPow k ((((t : ℕ) : ℝ) / 2 : ℝ) : ℂ) = absPow k ((t : ℂ) / 2) := by
    congr 1
    push_cast
    ring
  rw [e0, e1, e2, e3]
  simp only [MonoidHom.mul_apply, MonoidHom.inv_apply, map_mul, mul_inv]
  generalize absPow k (1 / 2) a = A
  generalize absPow k (1 / 2) b = B
  generalize absPow k ((t : ℂ) / 2) a = T
  generalize absPow k (-(i : ℂ) / 2) b = R
  calc A⁻¹ * B⁻¹ * (B * B * (T * (R * B⁻¹))) = (B⁻¹ * B) * (B * B⁻¹) * (T * R * A⁻¹) := by ac_rfl
    _ = T * R * A⁻¹ := by rw [inv_mul_cancel, mul_inv_cancel, one_mul, one_mul]

/- English proof (translation)
The claim follows from `(isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar`.
-/
theorem isSmoothChar_dpow (n : ℕ) (s : ℝ) : IsSmoothChar (dpow (k := k) n s) :=
  (isSmoothChar_of_isUnram (isUnram_absPow k _)).detChar

/- English proof (translation)
Unfold `twKer`. Use `congr 1`. Use extensionality with `w`. Use `exists_congr fun u => exists_congr fun v => ?_` and prove the remaining obligations. Establish `hu : dpowM n s (u : Mir k n) = 1` using `dpowM_of_mem' n s u.1 u.2`.

Rewrite using `[twist_apply, hu, Units.val_one, one_smul]`.
-/
theorem twKer_twist_dpowM {V : Type} [AddCommGroup V] [Module ℂ V] (n : ℕ) (τ : Representation ℂ (Mir k n) V) (s : ℝ) :
    twKer (twist τ (dpowM n s)) (MirUin k n) 1 = twKer τ (MirUin k n) 1 := by
  unfold twKer
  congr 1
  ext w
  refine exists_congr fun u => exists_congr fun v => ?_
  have hu : dpowM n s (u : Mir k n) = 1 := dpowM_of_mem' n s u.1 u.2
  rw [twist_apply, hu, Units.val_one, one_smul]

end Chars

section Main

variable {i t : ℕ} (τ : MRep k i) (σ : GRep k t)

abbrev eIT (i t : ℕ) : (Σ x, Two (Fin i) (Fin t) x) ≃ Fin (i + t) := two (stdSum (rfl : i + t = i + t))

abbrev sigT : Representation ℂ (Qp k i t) (PiTensorProduct ℂ (TwoT (psiN τ).V σ.V)) :=
  (twist (piTensor (twoRep (psiN τ).ρ σ.ρ)) (deltaHalf k (Two (Fin i) (Fin t)))).comp (leviProj k (eIT i t))

abbrev mkT (s : ℝ) : τ.V →ₗ[ℂ] Jacquet (mtw τ s).ρ (MirUin k i) := (twKer (mtw τ s).ρ (MirUin k i) 1).mkQ

abbrev mkY : τ.V →ₗ[ℂ] (psiN τ).V := (twKer τ.ρ (MirUin k i) 1).mkQ

def Lq (s : ℝ) : (Jacquet (mtw τ s).ρ (MirUin k i) ⊗[ℂ] σ.V) ≃ₗ[ℂ] PiTensorProduct ℂ (TwoT (psiN τ).V σ.V) :=
  (TensorProduct.congr (Submodule.quotEquivOfEq _ _ (twKer_twist_dpowM i τ.ρ s)) (LinearEquiv.refl ℂ σ.V)).trans
    (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).symm

/- English proof (translation)
Apply `(Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective` to reduce the goal to its premises. Rewrite using `[bool_tprod_pairT]`. Use `(LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_` and prove the remaining obligations. Both sides reduce to the same expression.
-/
theorem Lq_tmul (s : ℝ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s y ⊗ₜ[ℂ] w) = PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)).injective
  rw [bool_tprod_pairT]
  refine (LinearEquiv.apply_symm_apply (Exponents.boolTensorEquiv (X := TwoT (psiN τ).V σ.V)) _).trans ?_
  rfl

/- English proof (translation)
Establish `h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) = mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)`. Use `(extTensor_tmul _ _ _ _ _).trans ?_` and prove the remaining obligations. Use `show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _`. Rewrite using `[dpowM_levi']`. Both sides reduce to the same expression.

Conclude with `congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h`.
-/
theorem qRep_tmul (s₁ s₂ : ℝ) (q : Qp k i t) (y : τ.V) (w : σ.V) :
    qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) •
        (mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V)) := by
  have h : extTensor (psiMinus k (mtw τ s₁).ρ) (σ.tw s₂).ρ (qBlocks k i t q) (mkT τ s₁ y ⊗ₜ[ℂ] w) =
      mkT τ s₁ (((dpow i s₁ (qBlocks k i t q).1 : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ]
          (((dpow t s₂ (qBlocks k i t q).2 : ℂˣ) : ℂ) • σ.ρ (qBlocks k i t q).2 w : σ.V) := by
    refine (extTensor_tmul _ _ _ _ _).trans ?_
    show mkT τ s₁ (((dpowM i s₁ (levi k i (qBlocks k i t q).1) : ℂˣ) : ℂ) • τ.ρ (levi k i (qBlocks k i t q).1) y) ⊗ₜ[ℂ] _ = _
    rw [dpowM_levi']
    rfl
  exact congrArg (fun z => ((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) • z) h

/- English proof (translation)
Rewrite using `[Lq_tmul, map_smul, tprod_pairT_smul]`.
-/
theorem Lq_tmul_smul (s : ℝ) (c d : ℂ) (y : τ.V) (w : σ.V) :
    Lq τ σ s (mkT τ s (c • y) ⊗ₜ[ℂ] (d • w : σ.V)) = (c * d) • PiTensorProduct.tprod ℂ (pairT (mkY τ y) w) := by
  rw [Lq_tmul, map_smul, tprod_pairT_smul]

/- English proof (translation)
Establish `hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q)`. Use function extensionality and compare the values at `x`. Consider the cases of `x`. Both sides reduce to the same expression. Both sides reduce to the same expression.

Establish `hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) = GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2`. Rewrite using `[det_parab, Fintype.prod_bool, mul_comm]`. Both sides reduce to the same expression. Rewrite using `[hlev, deltaHalf_two]`. Simplify using `only [← Units.val_mul]`.

Use `congr 1`. Use `scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1) (GeneralLinearGroup.det (qBlocks k i t q).2)` as an intermediate fact. Simplify using `only [dpow, detChar_apply, hdet, Fintype.card_fin]`. Conclude with `this`.
-/
theorem scalar_q (i t : ℕ) (q : Qp k i t) :
    ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) *
        (((absPow k 1 (GeneralLinearGroup.det (qBlocks k i t q).2) : ℂˣ) : ℂ) *
          (((dpow i (((t : ℕ) : ℝ) / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) *
            ((dpow t (-((i + 1 : ℕ) : ℝ) / 2) (qBlocks k i t q).2 : ℂˣ) : ℂ))) =
      ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) *
        ((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) := by
  have hlev : leviProj k (eIT i t) q = leviTwo k (Fin i) (Fin t) (qBlocks k i t q) := by
    funext x
    cases x
    · rfl
    · rfl
  have hdet : GeneralLinearGroup.det (q : GL (Fin (i + t)) k) =
      GeneralLinearGroup.det (qBlocks k i t q).1 * GeneralLinearGroup.det (qBlocks k i t q).2 := by
    rw [det_parab, Fintype.prod_bool, mul_comm]
    rfl
  rw [hlev, deltaHalf_two]
  simp only [← Units.val_mul]
  congr 1
  have := scalar_sum (k := k) i t (GeneralLinearGroup.det (qBlocks k i t q).1)
    (GeneralLinearGroup.det (qBlocks k i t q).2)
  simp only [dpow, detChar_apply, hdet, Fintype.card_fin]
  exact this

def qEnd (s₁ s₂ : ℝ) (q : Qp k i t) :
    (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) →ₗ[ℂ] (Jacquet (mtw τ s₁).ρ (MirUin k i) ⊗[ℂ] σ.V) :=
  qRep (mtw τ s₁).ρ (σ.tw s₂).ρ q

/- English proof (translation)
Proceed by induction on `v using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `add x y hx hy => simp only [map_add, smul_add, hx, hy]`. Consider the case `tmul x w`. Take `⟨y, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`.

Establish `h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) = pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w)`. Use function extensionality and compare the values at `x`. Consider the cases of `x`. Both sides reduce to the same expression. Conclude with `(one_smul ℂ _).symm`.

Establish `hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) • (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) • PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (q …` using `by show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) • piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _`. Rewrite using `[piTensor_tprod]`. Conclude with `congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))`. Establish `hR` using `qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w`. Use `(congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)` and prove the remaining obligations.

Use `Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)` and prove the remaining obligations. Use `show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)`. Rewrite using `[map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]`. Use `congr 1`. Rewrite using `[← scalar_q i t q]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem sigT_Lq (q : Qp k i t) (v : Jacquet (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (MirUin k i) ⊗[ℂ] σ.V) :
    sigT τ σ q (Lq τ σ (((t : ℕ) : ℝ) / 2) v) =
      ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) •
        Lq τ σ (((t : ℕ) : ℝ) / 2) (qEnd τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q v) := by
  induction v using TensorProduct.induction_on with
  | zero => simp
  | add x y hx hy => simp only [map_add, smul_add, hx, hy]
  | tmul x w =>
    obtain ⟨y, rfl⟩ := Submodule.Quotient.mk_surjective _ x
    have h2 : (fun x => twoRep (psiN τ).ρ σ.ρ x (leviProj k (eIT i t) q x) (pairT (mkY τ y) w x)) =
        pairT (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) • mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y))
          ((1 : ℂ) • σ.ρ (qBlocks k i t q).2 w) := by
      funext x
      cases x
      · rfl
      · exact (one_smul ℂ _).symm
    have hL : sigT τ σ q (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) =
        ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
          (((dpow i (-1 / 2) (qBlocks k i t q).1 : ℂˣ) : ℂ) * 1) •
            PiTensorProduct.tprod ℂ (pairT (mkY τ (τ.ρ (levi k i (qBlocks k i t q).1) y)) (σ.ρ (qBlocks k i t q).2 w)) := by
      show ((deltaHalf k (Two (Fin i) (Fin t)) (leviProj k (eIT i t) q) : ℂˣ) : ℂ) •
        piTensor (twoRep (psiN τ).ρ σ.ρ) (leviProj k (eIT i t) q) (PiTensorProduct.tprod ℂ (pairT (mkY τ y) w)) = _
      rw [piTensor_tprod]
      exact congrArg _ ((congrArg (PiTensorProduct.tprod ℂ) h2).trans (tprod_pairT_smul _ _ _ _))
    have hR := qRep_tmul τ σ (((t : ℕ) : ℝ) / 2) (-((i + 1 : ℕ) : ℝ) / 2) q y w
    refine (congrArg (sigT τ σ q) (Lq_tmul τ σ _ y w)).trans (hL.trans ?_)
    refine Eq.trans ?_ (congrArg (fun z => ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) z) hR.symm)
    show _ = ((dpow (i + t) (-1 / 2) (q : GL (Fin (i + t)) k) : ℂˣ) : ℂ) • Lq τ σ (((t : ℕ) : ℝ) / 2) (_ • _)
    rw [map_smul, Lq_tmul_smul, smul_smul, smul_smul, smul_smul, mul_one]
    congr 1
    rw [← scalar_q i t q]
    ring

end Main

/- English proof (translation)
Introduce `k _ _ _ _ i t τ σ _ _ hE`. Take `⟨E⟩` from `hE`. Conclude with `⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩`.
-/
theorem psiN_prodPGn_of_equiv : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (i t : ℕ) (τ : MRep k i) (σ : GRep k t), IsSmooth τ.ρ → IsSmooth σ.ρ → Nonempty ((psiMinus k (prodPGn τ σ).ρ).Equiv (smInd (Qp k i t) (qRep (mtw τ (((t : ℕ) : ℝ) / 2)).ρ (σ.tw (-((i + 1 : ℕ) : ℝ) / 2)).ρ))) → GIso (psiN (prodPGn τ σ)) ((psiN τ).prod σ) := by
  intro k _ _ _ _ i t τ σ _ _ hE
  obtain ⟨E⟩ := hE
  exact ⟨(twistEquivOf E (dpow (i + t) (-1 / 2))).trans
    (GlobalTheory.LocGL.smIndTwistEquiv le_rfl le_rfl (isSmoothChar_dpow _ _) (Lq τ σ _) fun q v => sigT_Lq τ σ q v)⟩

end GlobalTheory.CompanionTheory.BZPsiPG.Norm

end
