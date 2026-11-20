import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.StatementsFlZIdealEqCoord
set_option maxSynthPendingDepth 1

noncomputable section

namespace GroundTheory.Heights₂.Heights.LowerBoundFree

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter

namespace FlZIdealEqCoord

variable (Ψ : Type) [Fintype Ψ] [DecidableEq Ψ] (N : ℕ)

abbrev ConeRing : Type := MvPolynomial (Ψ × Fin (N - 1)) (ΩFl Ψ N)

abbrev ConeFrac : Type := FractionRing (ConeRing Ψ N)

def tVar (τ : Ψ) (k : ℕ) : ConeFrac Ψ N :=
  if h : k < N - 1 then algebraMap (ConeRing Ψ N) (ConeFrac Ψ N) (X (τ, ⟨k, h⟩)) else 1

def rowFac (τ : Ψ) (a : ℕ) : ConeFrac Ψ N :=
  tVar Ψ N τ a / (if a = 0 then 1 else tVar Ψ N τ (a - 1))

omit [Fintype Ψ] [DecidableEq Ψ] in
/- English proof (translation)
Unfold `tVar`. Use `split_ifs with h`. Conclude with `(map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero _)`. Conclude with `one_ne_zero`.
-/
theorem tVar_ne_zero (τ : Ψ) (k : ℕ) : tVar Ψ N τ k ≠ 0 := by
  unfold tVar
  split_ifs with h
  · exact (map_ne_zero_iff _ (IsFractionRing.injective _ _)).mpr (X_ne_zero _)
  · exact one_ne_zero

omit [Fintype Ψ] [DecidableEq Ψ] in

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simp [rowFac]`. Consider the case `succ k ih`. Rewrite using `[Fin.prod_univ_castSucc]`. Simplify using `only [Fin.val_castSucc, Fin.val_last]`.

Rewrite using `[ih, rowFac, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]`. Clear denominators, using `[tVar_ne_zero Ψ N τ k]` for the nonvanishing conditions.
-/
theorem prod_rowFac (τ : Ψ) (k : ℕ) : ∏ a : Fin (k + 1), rowFac Ψ N τ a = tVar Ψ N τ k := by
  induction k with
  | zero => simp [rowFac]
  | succ k ih =>
    rw [Fin.prod_univ_castSucc]
    simp only [Fin.val_castSucc, Fin.val_last]
    rw [ih, rowFac, if_neg (Nat.succ_ne_zero k), Nat.add_sub_cancel]
    field_simp [tVar_ne_zero Ψ N τ k]

def gEnt : MvPolynomial (Ψ × Fin N × Fin N) ℚ →+* ConeFrac Ψ N :=
  (algebraMap (ConeRing Ψ N) (ConeFrac Ψ N)).comp
    ((C : ΩFl Ψ N →+* ConeRing Ψ N).comp (algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)))

def scaleMap : MvPolynomial (Ψ × Fin N × Fin N) ℤ →+* ConeFrac Ψ N :=
  eval₂Hom (Int.castRingHom _) fun v => rowFac Ψ N v.1 v.2.1 * gEnt Ψ N (X v)

omit [Fintype Ψ] [DecidableEq Ψ] in

/- English proof (translation)
Use `set M : Matrix (Fin ((i : ℕ) + 1)) (Fin ((i : ℕ) + 1)) (MvPolynomial (Ψ × Fin N × Fin N) ℚ) := Matrix.of fun a b => X (τ, Fin.castLE (step_le i) a, S.1.orderEmbOfFin S.2 b) with hMdef`. Establish `hM : (((IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT Ψ N τ).submatrix (Fin.castLE (step_le i)) (S.1.orderEmbOfFin S.2)).map (scaleMap Ψ N)) = Matrix.of fun (a b : Fin ((i : ℕ) + 1)) => rowFac Ψ N τ (a : ℕ) * (M.map (gEnt Ψ N)) a b`. Use extensionality with `a b`. Simplify using `[scaleMap, IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT, hMdef]`. Establish `hy : yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ = algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) M.det` using `rfl`.

Rewrite using `[flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]`. Rewrite using `[show Fin.castLE _ = Fin.castLE (step_le i) from rfl, hM, Matrix.det_mul_column, ← RingHom.mapMatrix_apply, ← RingHom.map_det, prod_rowFac, hy, tVar, dif_pos i.2, map_mul, mul_comm]`. Both sides reduce to the same expression.
-/
theorem scaleMap_flagMinor (τ : Ψ) (i : Fin (N - 1)) (S : PluckerBlocks N N i) :
    scaleMap Ψ N (flagMinor (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT Ψ N τ) i S) =
      algebraMap (ConeRing Ψ N) (ConeFrac Ψ N)
        (C (yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩) * X (τ, i)) := by
  set M : Matrix (Fin ((i : ℕ) + 1)) (Fin ((i : ℕ) + 1)) (MvPolynomial (Ψ × Fin N × Fin N) ℚ) :=
    Matrix.of fun a b => X (τ, Fin.castLE (step_le i) a, S.1.orderEmbOfFin S.2 b) with hMdef
  have hM : (((IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT Ψ N τ).submatrix (Fin.castLE (step_le i))
      (S.1.orderEmbOfFin S.2)).map (scaleMap Ψ N)) =
      Matrix.of fun (a b : Fin ((i : ℕ) + 1)) => rowFac Ψ N τ (a : ℕ) * (M.map (gEnt Ψ N)) a b := by
    ext a b
    simp [scaleMap, IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT, hMdef]
  have hy : yFl Ψ N ⟨(τ, i), ⟨S.1.orderEmbOfFin S.2, (S.1.orderEmbOfFin S.2).strictMono⟩⟩ =
      algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) M.det := rfl
  rw [flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]
  rw [show Fin.castLE _ = Fin.castLE (step_le i) from rfl, hM, Matrix.det_mul_column, ← RingHom.mapMatrix_apply, ← RingHom.map_det,
    prod_rowFac, hy, tVar, dif_pos i.2, map_mul, mul_comm]
  rfl

end FlZIdealEqCoord

open FlZIdealEqCoord in
/- English proof (translation)
Introduce `Ψ _ _ N`. Use `set y := fun p => yFl Ψ N (flZIncr Ψ N p) with hydef`. Establish `hA : ∀ f, scaleMap Ψ N (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap Ψ N f) = algebraMap (ConeRing Ψ N) (ConeFrac Ψ N) (mConeMap y f)`. Introduce `f`. Proceed by induction on `f using MvPolynomial.induction_on with`.

Consider the case `C a => simp [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, mConeMap]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`. Consider the case `mul_X f p hf`. Simplify using `only [map_mul, hf]`. Use `congr 1`.

Simplify using `only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, coe_eval₂Hom, eval₂_X, mConeMap, aeval_X]`. Rewrite using `[scaleMap_flagMinor]`. Both sides reduce to the same expression. Establish `hB : ∀ f, algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N) (MvPolynomial.map (Int.castRingHom ℚ) (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap Ψ N f)) = aeval (fun _ => (1 : ΩFl Ψ N)) (mConeMap y f)`. Introduce `f`.

Proceed by induction on `f using MvPolynomial.induction_on with`. Consider the case `C a => simp [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, mConeMap]`. Consider the case `add f g hf hg => simp only [map_add, hf, hg]`. Consider the case `mul_X f p hf`. Simplify using `only [map_mul, hf]`.

Use `congr 1`. Simplify using `only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, coe_eval₂Hom, eval₂_X, mConeMap, aeval_X, map_mul, aeval_C, Algebra.algebraMap_self, RingHom.id_apply, mul_one]`. Rewrite using `[hydef]`. Simplify using `only [yFl, flZIncr]`. Use `congr 1`.

Rewrite using `[flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]`. Use `congr 1`. Use extensionality with `a b`. Simplify using `[IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT]`. Use extensionality with `f`.

Simplify using `only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal, mCoordIdeal, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `hf`. Establish `h` using `hA f`. Rewrite `h` using `[hf, map_zero]`.

Conclude with `(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h.symm`. Introduce `hf`. Establish `h` using `hB f`. Rewrite `h` using `[hf, map_zero]`. Establish `h2` using `(map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h`.

Conclude with `(map_eq_zero_iff _ (map_injective _ (Int.castRingHom ℚ).injective_int)).mp h2`.
-/
theorem FlZIdealEqCoord.proof : FlZIdealEqCoord.Statement := by
  intro Ψ _ _ N
  set y := fun p => yFl Ψ N (flZIncr Ψ N p) with hydef

  have hA : ∀ f, scaleMap Ψ N (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap Ψ N f) =
      algebraMap (ConeRing Ψ N) (ConeFrac Ψ N) (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf =>
      simp only [map_mul, hf]
      congr 1
      simp only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, coe_eval₂Hom, eval₂_X, mConeMap, aeval_X]
      rw [scaleMap_flagMinor]
      rfl

  have hB : ∀ f, algebraMap (MvPolynomial (Ψ × Fin N × Fin N) ℚ) (ΩFl Ψ N)
      (MvPolynomial.map (Int.castRingHom ℚ) (IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap Ψ N f)) =
      aeval (fun _ => (1 : ΩFl Ψ N)) (mConeMap y f) := by
    intro f
    induction f using MvPolynomial.induction_on with
    | C a => simp [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, mConeMap]
    | add f g hf hg => simp only [map_add, hf, hg]
    | mul_X f p hf =>
      simp only [map_mul, hf]
      congr 1
      simp only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.flZMap, coe_eval₂Hom, eval₂_X, mConeMap, aeval_X, map_mul, aeval_C,
        Algebra.algebraMap_self, RingHom.id_apply, mul_one]
      rw [hydef]
      dsimp only [yFl, flZIncr]
      congr 1
      rw [flagMinor, RingHom.map_det, RingHom.mapMatrix_apply]
      congr 1
      ext a b
      simp [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.genT]
  ext f
  simp only [IndefiniteRowSideFullHecke.LowerBoundFree.Nine.FlZIdeal, mCoordIdeal, RingHom.mem_ker]
  constructor
  · intro hf
    have h := hA f
    rw [hf, map_zero] at h
    exact (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h.symm
  · intro hf
    have h := hB f
    rw [hf, map_zero] at h
    have h2 := (map_eq_zero_iff _ (IsFractionRing.injective _ _)).mp h
    exact (map_eq_zero_iff _ (map_injective _ (Int.castRingHom ℚ).injective_int)).mp h2

end GroundTheory.Heights₂.Heights.LowerBoundFree
