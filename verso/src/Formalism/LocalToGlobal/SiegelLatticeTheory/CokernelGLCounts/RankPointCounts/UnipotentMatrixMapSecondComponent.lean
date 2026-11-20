import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.CornerRight
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.ThetaModuleTransport.HeadColumnCoordinates.DeterminantUnitTheta.CompOfMemR

noncomputable section

open Matrix

namespace Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents

section Sandwich

variable {K : Type*} [CommRing K] {r : ℕ}

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Apply the first step, then apply the next step to every resulting obligation.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem corner_sandwich (A B : Matrix (Fin (r + 1)) (Fin (r + 1)) K)
    (hA : ∀ i, A i (Fin.last r) = if i = Fin.last r then 1 else 0)
    (hB : ∀ j, B (Fin.last r) j = if j = Fin.last r then 1 else 0) (c : K) :
    A * cornerM (r := r) c * B = cornerM c := by
  ext i j
  simp only [Matrix.mul_apply, cornerM, Matrix.of_apply]
  rw [Finset.sum_eq_single (Fin.last r)]
  · rw [Finset.sum_eq_single (Fin.last r)]
    · rw [hA, hB]
      split_ifs <;> simp_all
    · intro k _ hk
      simp [hk]
    · simp
  · intro l _ hl
    have h0 : ∀ k, (A i k * if k = Fin.last r ∧ l = Fin.last r then c else 0) = 0 := by
      intro k
      simp [hl]
    simp [h0]
  · simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem Ec_eq_cornerM : (Ec (K := K) r) = cornerM 1 := rfl

end Sandwich

section Comp

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  (M : Formalism.MainNotions.S.Loc.Model F E) (g : Formalism.MainNotions.S.Loc.SplitG M.L)

def π1 : E →+* F := (RingHom.fst F F).comp g.e.toRingEquiv.toRingHom

def π2 : E →+* F := (RingHom.snd F F).comp g.e.toRingEquiv.toRingHom

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem π1_apply (x : E) : π1 M g x = (g.e x).1 := rfl
/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem π2_apply (x : E) : π2 M g x = (g.e x).2 := rfl

/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem π1_cj (x : E) : π1 M g (M.L.cj x) = π2 M g x := by
  rw [π1_apply, g.e_cj, π2_apply, Prod.fst_swap]
/- English proof (translation)
Rewrite the conclusion using the stated equalities.
-/
theorem π2_cj (x : E) : π2 M g (M.L.cj x) = π1 M g x := by
  rw [π2_apply, g.e_cj, π1_apply, Prod.snd_swap]

variable {r : ℕ}

def mmG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).2, (g.e (L j i)).1)

def uuG (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : Matrix (Fin (r + 1)) (Fin (r + 1)) E :=
  Matrix.of fun i j => g.e.symm ((g.e (P i j)).1, (g.e (L j i)).2)

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem middleMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π1 M g) = P.map (π2 M g) := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem middleMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (mmG M g L P).map (π2 M g) = (L.map (π1 M g))ᵀ := by
  ext i j
  simp [mmG, π1_apply, π2_apply]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem unipotentMatrix_map_firstComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π1 M g) = P.map (π1 M g) := by
  ext i j
  simp [uuG, π1_apply, π2_apply]
/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem unipotentMatrix_map_secondComponent (L P : Matrix (Fin (r + 1)) (Fin (r + 1)) E) : (uuG M g L P).map (π2 M g) = (L.map (π2 M g))ᵀ := by
  ext i j
  simp [uuG, π1_apply, π2_apply]

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zzPlus_map_firstComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π1 M g) =
      ((g.q : F))⁻¹ • Zh.map (π1 M g) + (T / (g.q : F)) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π1_apply]
    ring
  · simp [h, cornerM, π1_apply]
    ring

/- English proof (translation)
By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities. Consider separately whether the proposition holds or fails. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem zzPlus_map_secondComponent (hs : M.split = some g) (Zh : Matrix (Fin (r + 1)) (Fin (r + 1)) E) (T T' : F) :
    (Formalism.MainNotions.S.Loc.HermSp.ZZplusOf M Zh T T').map (π2 M g) =
      (-((g.q : F))⁻¹) • (Zh.map (π2 M g))ᵀ + (-(T' / (g.q : F))) • Ec r := by
  ext a b
  simp only [Formalism.MainNotions.S.Loc.HermSp.ZZplusOf, hs]
  rw [Ec_eq_cornerM]
  by_cases h : a = Fin.last r ∧ b = Fin.last r
  · simp [h, cornerM, π2_apply]
    ring
  · simp [h, cornerM, π2_apply]
    ring

end Comp

end Formalism.L2.SG.Pf.Coef.SplitCoefficientComponents
