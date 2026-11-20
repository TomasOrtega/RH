import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CstD

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Matrix Filter Topology
open GroundTheory.Global GroundTheory.LocalField GroundTheory.Automorphic GroundTheory.Automorphic.AutomorphicForm
open GroundTheory.Automorphic.Reduction (finAt infAt maxCompact)
open Ad3 Ad3.K Ad3.K.QuadraticBaseChangeGL3
open Ad3.R (G2 Jd md Dt KA Set0 Coord LInv pt dia2 pri)
open GlobalTheory.CompanionTheory.UnfoldingAlt
open scoped NumberField.AdeleRing ENNReal

namespace GlobalTheory.CompanionTheory.TiArch

open scoped ContDiff

variable {K : Type*} [Field K] [NumberField K] {n : ℕ}

def tr (A : ArchMatrix K n) : ArchMatrix K n :=
  Matrix.transpose (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from A)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_mul (A B : ArchMatrix K n) : tr (A * B) = tr B * tr A :=
  Matrix.transpose_mul (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from A)
    (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from B)

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_one : tr (1 : ArchMatrix K n) = 1 :=
  Matrix.transpose_one

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_neg (A : ArchMatrix K n) : tr (-A) = -tr A :=
  Matrix.transpose_neg _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_add (A B : ArchMatrix K n) : tr (A + B) = tr A + tr B :=
  Matrix.transpose_add _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_smul (r : ℝ) (A : ArchMatrix K n) : tr (r • A) = r • tr A :=
  Matrix.transpose_smul _ _

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem tr_exp (Y : ArchMatrix K n) : NormedSpace.exp (tr Y) = tr (NormedSpace.exp Y) :=
  Matrix.exp_transpose _

def tiA (x : archGroup K n) : archGroup K n :=
  ⟨⟨tr (((x : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n),
    tr ((x : (ArchMatrix K n)ˣ) : ArchMatrix K n),
    by rw [← tr_mul, Units.mul_inv, tr_one],
    by rw [← tr_mul, Units.inv_mul, tr_one]⟩, trivial⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem coe_tiA (x : archGroup K n) :
    (((tiA x : archGroup K n) : (ArchMatrix K n)ˣ) : ArchMatrix K n) =
      tr (((x : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) : ArchMatrix K n) := rfl

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules.
-/
theorem tiA_mul (x y : archGroup K n) : tiA (x * y) = tiA x * tiA y := by
  apply Subtype.ext
  apply Units.ext
  simp only [Subgroup.coe_mul, Units.val_mul, coe_tiA, _root_.mul_inv_rev, tr_mul]

def dtiA : archLie K n →ₗ[ℝ] archLie K n where
  toFun Y := ⟨-tr (Y : ArchMatrix K n), trivial⟩
  map_add' X Y := by
    apply Subtype.ext
    show -tr ((X : ArchMatrix K n) + (Y : ArchMatrix K n)) = -tr (X : ArchMatrix K n) + -tr (Y : ArchMatrix K n)
    rw [tr_add, neg_add]
  map_smul' r Y := by
    apply Subtype.ext
    show -tr (r • (Y : ArchMatrix K n)) = r • -tr (Y : ArchMatrix K n)
    rw [tr_smul, smul_neg]

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Reduce the claim to the hypotheses of an applicable result. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem tiA_expG (Y : archLie K n) :
    tiA ((isExpLieAlgebra K n).expG Y) = (isExpLieAlgebra K n).expG (dtiA Y) := by
  apply Subtype.ext
  apply Units.ext
  have h : ((((isExpLieAlgebra K n).expG Y : archGroup K n) : (ArchMatrix K n)ˣ)⁻¹ : (ArchMatrix K n)ˣ) =
      (((isExpLieAlgebra K n).expG (-Y) : archGroup K n) : (ArchMatrix K n)ˣ) := by
    rw [IsExpLieAlgebra.expG_neg]; rfl
  rw [coe_tiA, h]
  show tr (NormedSpace.exp (-(Y : ArchMatrix K n))) = NormedSpace.exp (-tr (Y : ArchMatrix K n))
  rw [← tr_exp, tr_neg]

/- English proof (translation)
Rewrite the hypotheses and the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem isSmoothFun_comp_tiA {f : archGroup K n → ℂ} (hf : (isExpLieAlgebra K n).IsSmoothFun f) :
    (isExpLieAlgebra K n).IsSmoothFun (fun x => f (tiA x)) := by
  rw [IsExpLieAlgebra.isSmoothFun_iff] at hf ⊢
  intro g
  haveI : FiniteDimensional ℝ (archLie K n) := FiniteDimensional.finiteDimensional_submodule _
  have hL : ContDiff ℝ (∞) (dtiA (K := K) (n := n)) :=
    (LinearMap.toContinuousLinearMap (dtiA (K := K) (n := n))).contDiff
  have e : (fun Y : archLie K n => f (tiA (g * (isExpLieAlgebra K n).expG Y))) =
      (fun Y : archLie K n => f (tiA g * (isExpLieAlgebra K n).expG Y)) ∘ dtiA := by
    funext Y
    rw [Function.comp_apply, tiA_mul, tiA_expG]
  rw [e]
  exact (hf (tiA g)).comp hL

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Both sides reduce to the same expression. A detailed English derivation is pending.
-/
theorem infEmb_fst (y : archGroup K n) (a b : Fin n) :
    InfiniteAdeleRing.ringEquiv_mixedSpace K ((infEmb K n y) a b).1 =
      (show Matrix (Fin n) (Fin n) (mixedEmbedding.mixedSpace K) from ((y : (ArchMatrix K n)ˣ) : ArchMatrix K n)) a b := by
  have h1 : ((infEmb K n y) a b).1 = ((archEquiv K n).symm y) a b := by
    have := congrArg (fun p => (p.1 : Matrix (Fin n) (Fin n) (InfiniteAdeleRing K)) a b) (prodEquiv_infEmb y)
    exact this
  rw [h1]
  obtain ⟨z, rfl⟩ := (archEquiv K n).surjective y
  rw [ContinuousMulEquiv.symm_apply_apply]
  rfl

/- English proof (translation)
A detailed English derivation is pending.
-/
theorem infEmb_snd (y : archGroup K n) (a b : Fin n) :
    ((infEmb K n y) a b).2 = (1 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) a b :=
  congrArg (fun p => (p.2 : Matrix (Fin n) (Fin n) (FiniteAdeleRing (𝓞 K) K)) a b) (prodEquiv_infEmb y)

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations.

Reduce the claim to the hypotheses of an applicable result. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
theorem ti_infEmb (x : archGroup K n) : ti (infEmb K n x) = infEmb K n (tiA x) := by
  apply Units.ext
  ext a b
  change (infEmb K n x)⁻¹.val b a = (infEmb K n (tiA x)) a b
  rw [← map_inv]
  refine Prod.ext ?_ ?_
  · apply (InfiniteAdeleRing.ringEquiv_mixedSpace K).injective
    rw [infEmb_fst, infEmb_fst]
    rfl
  · rw [infEmb_snd, infEmb_snd]
    exact congrFun (congrFun (Matrix.transpose_one (n := Fin n) (α := FiniteAdeleRing (𝓞 K) K)) a) b

/- English proof (translation)
Reduce the claim to the hypotheses of an applicable result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.
-/
theorem ti_mul' {R : Type*} [CommRing R] {m : Type*} [Fintype m] [DecidableEq m] (a b : GL m R) :
    ti (a * b) = ti a * ti b := by
  apply Units.ext
  change (b.inv * a.inv).transpose = a.inv.transpose * b.inv.transpose
  rw [Matrix.transpose_mul]

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

A detailed English derivation is pending.
-/
theorem isArchSmooth_comp_ti :
    ∀ (F : G3 → ℂ), IsArchSmooth F → ∀ c : G3, IsArchSmooth (fun g : G3 => F (c * ti g)) := by
  intro F hF c g
  have e : archSlice (fun g : G3 => F (c * ti g)) g = fun x => archSlice F (c * ti g) (tiA x) := by
    funext x
    simp only [archSlice_apply, ti_mul', ti_infEmb, mul_assoc]
  rw [e]
  exact isSmoothFun_comp_tiA (hF _)

end GlobalTheory.CompanionTheory.TiArch
