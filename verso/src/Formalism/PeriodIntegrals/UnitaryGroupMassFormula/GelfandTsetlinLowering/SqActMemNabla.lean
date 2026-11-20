import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GelfandTsetlinLowering.AdjBase

noncomputable section

namespace PI.WGL.Adj

open Formalism.BasicNotions MvPolynomial

def gStar {N : ℕ} (g : GL (Fin N) ℂ) : GL (Fin N) ℂ where
  val := Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ)
  inv := Matrix.conjTranspose ((g⁻¹ : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)
  val_inv := by rw [← Matrix.conjTranspose_mul]; simp
  inv_val := by rw [← Matrix.conjTranspose_mul]; simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem gStar_val {N : ℕ} (g : GL (Fin N) ℂ) :
    ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) = Matrix.conjTranspose (g : Matrix (Fin N) (Fin N) ℂ) := rfl

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[gStar_val]`.
-/
theorem gStar_gStar {N : ℕ} (g : GL (Fin N) ℂ) : gStar (gStar g) = g := by
  ext i j; simp [gStar_val]

def cU (a : ℂˣ) : ℂˣ := Units.map (starRingEnd ℂ : ℂ →* ℂ) a

/- English proof (translation)
Unfold `cU`. Rewrite using `[← map_zpow, Units.coe_map]`. Both sides reduce to the same expression.
-/
theorem cU_zpow_val (a : ℂˣ) (e : ℤ) : ((cU a ^ e : ℂˣ) : ℂ) = star ((a ^ e : ℂˣ) : ℂ) := by
  unfold cU
  rw [← map_zpow, Units.coe_map]
  rfl

/- English proof (translation)
Establish `key : ∀ p q : Fin n ⊕ Fin 1, Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q = (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p)`. Introduce and unpack `(p | p) (q | q)`. Simplify using `[Matrix.conjTranspose_apply]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.

Establish `hp : p = q` using `Subsingleton.elim _ _`. Substitute `hp` using the available equality. Simplify using the standard rewrite rules. Use extensionality with `i j`. Simplify using `only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]`.

Simplify using the standard rewrite rules. Conclude with `key _ _`.
-/
theorem embGL_gStar {n N : ℕ} (h : n + 1 = N) (g : GL (Fin n) ℂ) :
    embGL ℂ n N h (gStar g) = gStar (embGL ℂ n N h g) := by
  have key : ∀ p q : Fin n ⊕ Fin 1,
      Matrix.fromBlocks (Matrix.conjTranspose (g : Matrix (Fin n) (Fin n) ℂ)) 0 0 1 p q =
        (starRingEnd ℂ) (Matrix.fromBlocks (g : Matrix (Fin n) (Fin n) ℂ) 0 0 1 q p) := by
    rintro (p | p) (q | q)
    · simp [Matrix.conjTranspose_apply]
    · simp
    · simp
    · have hp : p = q := Subsingleton.elim _ _
      subst hp; simp
  ext i j
  simp only [embGL, blkHom, gStar_val, Matrix.conjTranspose_apply]
  simp
  exact key _ _

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]`. Distinguish the cases in `hij : i = j`. Apply the tactic sequence `subst hij; split_ifs <;> simp [cU]`. Establish `hji : j ≠ i` using `fun e => hij e.symm`.

Simplify using `[hij, hji]`.
-/
theorem lastGL_cU (N : ℕ) (a : ℂˣ) : lastGL ℂ N (cU a) = gStar (lastGL ℂ N a) := by
  ext i j
  simp only [lastGL, diagGL, gStar_val, Matrix.conjTranspose_apply, Matrix.diagonal_apply]
  by_cases hij : i = j
  · subst hij; split_ifs <;> simp [cU]
  · have hji : j ≠ i := fun e => hij e.symm
    simp [hij, hji]

/- English proof (translation)
Unfold `detPow`. Rewrite using `[Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]`. Use `congr 1`. Simplify using `[gStar_val, Matrix.det_conjTranspose]`.
-/
theorem detPow_gStar {N : ℕ} (g : GL (Fin N) ℂ) (k : ℤ) :
    detPow ℂ N (gStar g) k = star (detPow ℂ N g k) := by
  unfold detPow
  rw [Units.val_zpow_eq_zpow_val, Units.val_zpow_eq_zpow_val, star_zpow₀]
  congr 1
  simp [gStar_val, Matrix.det_conjTranspose]

/- English proof (translation)
Unfold `sqAct`. Conclude with `Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)`.
-/
theorem sqAct_mem_nabla {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ)
    (hf : f ∈ nablaSq ℂ N lam) : sqAct ℂ N lam g f ∈ nablaSq ℂ N lam := by
  unfold sqAct
  exact Submodule.smul_mem _ _ (Formalism.GradedWeylDivisibility.dualWeylRowStable ℂ N N lam.natW _ f hf)

/- English proof (translation)
Unfold `sqAct`. Rewrite using `[map_smul, smul_comm]`.
-/
theorem sqAct_smul {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (c : ℂ) (f : MvPolynomial (Fin N × Fin N) ℂ) :
    sqAct ℂ N lam g (c • f) = c • sqAct ℂ N lam g f := by
  unfold sqAct
  rw [map_smul, smul_comm]

/- English proof (translation)
Establish `hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) = Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)`. Use extensionality with `i j`. Simplify using `[gStar_val, Matrix.conjTranspose_apply]`. Establish `hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n` using `N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y = Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by`. Rewrite using `[Formalism.GradedWeylDivisibility.fockRowAdj, hm]`.

Unfold `sqAct`. Rewrite using `[nf_smul_left, nf_smul_right, detPow_gStar, star_star]`. Unfold `normFock`. Rewrite using `[hf]`.
-/
theorem nf_sqAct_adj {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam (sqAct ℂ N lam g x) y = normFock lam x (sqAct ℂ N lam (gStar g) y) := by
  have hm : Matrix.conjTranspose (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) =
      Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ) := by
    ext i j; simp [gStar_val, Matrix.conjTranspose_apply]
  have hf : Formalism.REAL.fockF (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N) (Matrix.transpose (g : Matrix (Fin N) (Fin N) ℂ)) x) y =
      Formalism.REAL.fockF x (Formalism.GradedWeylDivisibility.rowAct ℂ (n := N)
        (Matrix.transpose ((gStar g : GL (Fin N) ℂ) : Matrix (Fin N) (Fin N) ℂ)) y) := by
    rw [Formalism.GradedWeylDivisibility.fockRowAdj, hm]
  unfold sqAct
  rw [nf_smul_left, nf_smul_right, detPow_gStar, star_star]
  unfold normFock
  rw [hf]

/- English proof (translation)
Rewrite using `[nf_sqAct_adj, gStar_gStar]`.
-/
theorem nf_sqAct_adj' {N : ℕ} (lam : DomWeight N) (g : GL (Fin N) ℂ) (x y : MvPolynomial (Fin N × Fin N) ℂ) :
    normFock lam x (sqAct ℂ N lam g y) = normFock lam (sqAct ℂ N lam (gStar g) x) y := by
  rw [nf_sqAct_adj, gStar_gStar]

/- English proof (translation)
Introduce `i j hij`. Unfold `DomWeight.natW`. Conclude with `Int.toNat_le_toNat (by have := lam.anti hij; linarith)`.
-/
theorem natW_anti {N : ℕ} (lam : DomWeight N) : Antitone lam.natW := by
  intro i j hij
  unfold DomWeight.natW
  exact Int.toNat_le_toNat (by have := lam.anti hij; linarith)

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)`.
-/
theorem extremal_mem {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ∈ nablaSq ℂ N lam :=
  Formalism.GradedWeylDivisibility.hwMem ℂ N N le_rfl lam.natW (natW_anti lam)

/- English proof (translation)
The claim follows from `Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW`.
-/
theorem extremal_ne {N : ℕ} (lam : DomWeight N) : extremal ℂ N lam ≠ 0 :=
  Formalism.GradedWeylDivisibility.hwNe ℂ N N le_rfl lam.natW

end PI.WGL.Adj
