import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.Placed
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.ExistsNormLeHeightPow
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.DiscreteSeriesClassificationIff
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.ThmSOwn
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.FinitePartMemFrameStabilizerIffLocalStabilizer
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsSuppVecLocEq
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.SelfDualLatticeFrameChainStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.DatumLevelHyperspecialOffFinitePlaces
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ExistsCompactOpenLatticeStabilizerAtPlaces
open scoped InnerProductSpace TensorProduct
open Formalism.BasicNotions Formalism.MainNotions Formalism.DivisionValues Formalism.L2 Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Mult Formalism.IndefR.Datum MeasureTheory NumberField IsDedekindDomain
open Formalism.L2.SG.RowsJoinPinned Formalism.L2.SG.RowDict Formalism.L2.SG.PoincareInHH.PoincareSetting
open GlobalTheory.MixModel GlobalTheory.MixPer GlobalTheory.Unf GlobalTheory.MiS GlobalTheory.Core.Mi
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.MiTop GlobalTheory.SeeSaw GlobalTheory.Fam ValuativeRel IsLocalRing GlobalTheory.FinPl

noncomputable section
namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Rewrite using `[Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]`. Use `congr 1`. Use extensionality with `a b : 2`. Apply the tactic sequence `by_cases h : a = b <;> simp [h, mul_comm z]`.
-/
theorem eval_charpolyRev_eq (M : Matrix n n E) (z : E) :
    M.charpolyRev.eval z = (1 - z • M).det := by
  rw [Matrix.charpolyRev, ← coe_evalRingHom, RingHom.map_det]
  congr 1
  ext a b : 2
  by_cases h : a = b <;> simp [h, mul_comm z]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_smul (σ : E →+* E) (c : E) (M : Matrix n n E) :
    Formalism.UG.cT σ (c • M) = σ c • Formalism.UG.cT σ M := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_add (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M + N) = Formalism.UG.cT σ M + Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT]`.
-/
theorem cT_sub (σ : E →+* E) (M N : Matrix n n E) :
    Formalism.UG.cT σ (M - N) = Formalism.UG.cT σ M - Formalism.UG.cT σ N := by
  ext i j; simp [Formalism.UG.cT]

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[Formalism.UG.cT, hσ]`.
-/
theorem cT_cT (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (M : Matrix n n E) :
    Formalism.UG.cT σ (Formalism.UG.cT σ M) = M := by
  ext i j; simp [Formalism.UG.cT, hσ]

/- English proof (translation)
Use `set A : Matrix n n E := 1 - t • X with hAdef`. Use `set P : Matrix n n E := A⁻¹`. Establish `hu : IsUnit A.det` using `isUnit_iff_ne_zero.2 hA`. Establish `hAP : A * P = 1` using `Matrix.mul_nonsing_inv A hu`. Establish `hPA : P * A = 1` using `Matrix.nonsing_inv_mul A hu`.

Use `set g : Matrix n n E := (2 : E) • P - 1`. Establish `hgA : g * A = 1 + t • X`. Rewrite using `[Matrix.sub_mul, Matrix.smul_mul, hPA, Matrix.one_mul, hAdef, two_smul]`. Normalize the expressions using the abelian group laws. Establish `hcA : Formalism.UG.cT σ A = 1 - t • Formalism.UG.cT σ X`.

Rewrite using `[hAdef, cT_sub, cT_smul, Formalism.UG.cT_one, ht]`. Establish `hcPA : Formalism.UG.cT σ P * Formalism.UG.cT σ A = 1`. Rewrite using `[← Formalism.UG.cT_mul, hAP, Formalism.UG.cT_one]`. Establish `hY : Formalism.UG.cT σ X * J = -(J * X)` using `eq_neg_of_add_eq_zero_left hX`. Establish `key : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ A * J * A`.

Establish `e1 : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ (g * A) * J * (g * A)`. Rewrite using `[Formalism.UG.cT_mul]`. Simplify using `only [Matrix.mul_assoc]`. Rewrite using `[e1, hgA, hcA, cT_add, cT_smul, Formalism.UG.cT_one, ht]`. Simplify using `only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one, Matrix.smul_mul, Matrix.mul_smul, hY]`.

Rewrite using `[hAdef]`. Simplify using `only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul]`. Use `module`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcPA, hAP, Matrix.one_mul, Matrix.mul_one]`.

Use `_ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A) * P := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A) * P := by rw [key]`. Use `_ = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * J * (A * P) := by simp only [Matrix.mul_assoc]`. Use `_ = J := by rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]`.
-/
theorem cayley_unitary (σ : E →+* E) (J X : Matrix n n E) (t : E) (ht : σ t = t)
    (hX : Formalism.UG.cT σ X * J + J * X = 0) (hA : (1 - t • X).det ≠ 0) :
    Formalism.UG.cT σ ((2 : E) • (1 - t • X)⁻¹ - 1) * J * ((2 : E) • (1 - t • X)⁻¹ - 1) = J := by
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hA
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  set g : Matrix n n E := (2 : E) • P - 1
  have hgA : g * A = 1 + t • X := by
    rw [Matrix.sub_mul, Matrix.smul_mul, hPA, Matrix.one_mul, hAdef, two_smul]
    abel
  have hcA : Formalism.UG.cT σ A = 1 - t • Formalism.UG.cT σ X := by
    rw [hAdef, cT_sub, cT_smul, Formalism.UG.cT_one, ht]
  have hcPA : Formalism.UG.cT σ P * Formalism.UG.cT σ A = 1 := by
    rw [← Formalism.UG.cT_mul, hAP, Formalism.UG.cT_one]
  have hY : Formalism.UG.cT σ X * J = -(J * X) := eq_neg_of_add_eq_zero_left hX
  have key : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ A * J * A := by
    have e1 : Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A = Formalism.UG.cT σ (g * A) * J * (g * A) := by
      rw [Formalism.UG.cT_mul]; simp only [Matrix.mul_assoc]
    rw [e1, hgA, hcA, cT_add, cT_smul, Formalism.UG.cT_one, ht]
    simp only [Matrix.add_mul, Matrix.sub_mul, Matrix.mul_add, Matrix.mul_sub, Matrix.one_mul, Matrix.mul_one,
      Matrix.smul_mul, Matrix.mul_smul, hY]
    rw [hAdef]
    simp only [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul, Matrix.neg_mul]
    module
  calc Formalism.UG.cT σ g * J * g
      = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * (Formalism.UG.cT σ g * J * g) * (A * P) := by
        rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * (Formalism.UG.cT σ g * J * g) * A) * P := by
        simp only [Matrix.mul_assoc]
    _ = Formalism.UG.cT σ P * (Formalism.UG.cT σ A * J * A) * P := by rw [key]
    _ = (Formalism.UG.cT σ P * Formalism.UG.cT σ A) * J * (A * P) := by simp only [Matrix.mul_assoc]
    _ = J := by rw [hcPA, hAP, Matrix.one_mul, Matrix.mul_one]

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Polynomial

variable {E : Type} [Field E] {n : Type} [Fintype n] [DecidableEq n]
variable {R : Type} [CommRing R] (ι : E →+* R)

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smulE (c : E) (M : Matrix n n E) : (c • M).map ι = ι c • M.map ι := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_subE (M N : Matrix n n E) : (M - N).map ι = M.map ι - N.map ι := by
  ext i j; simp

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_addE (M N : Matrix n n E) : (M + N).map ι = M.map ι + N.map ι := by
  ext i j; simp

/- English proof (translation)
The claim follows from `Matrix.map_one _ (map_zero ι) (map_one ι)`.
-/
theorem map_oneE : (1 : Matrix n n E).map ι = 1 := Matrix.map_one _ (map_zero ι) (map_one ι)

/- English proof (translation)
The claim follows from `Matrix.map_mul`.
-/
theorem map_mulE (M N : Matrix n n E) : (M * N).map ι = M.map ι * N.map ι := Matrix.map_mul

/- English proof (translation)
Establish `hp : X.charpolyRev ≠ 0`. Introduce `h`. Use `Matrix.eval_charpolyRev (M := X)` as an intermediate fact. Rewrite `this` using `[h, Polynomial.eval_zero]`. Conclude with `zero_ne_one this`.

Take `⟨t, ht, hts⟩` from `hF.exists_notMem_finset (insert 0 X.charpolyRev.roots.toFinset)`. Establish `ht0 : t ≠ 0` using `fun e => hts (by simp [e])`. Establish `hdet : (1 - t • X).det ≠ 0`. Introduce `e`. Apply `hts` to reduce the goal to its premises.

Rewrite using `[Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_charpolyRev_eq]`. Conclude with `Or.inr e`. Establish `hg` using `hZ _ (cayley_unitary σ J X t ht hX hdet)`. Use `set A : Matrix n n E := 1 - t • X with hAdef`. Use `set P : Matrix n n E := A⁻¹`.

Establish `hu : IsUnit A.det` using `isUnit_iff_ne_zero.2 hdet`. Establish `hAP : A * P = 1` using `Matrix.mul_nonsing_inv A hu`. Establish `hPA : P * A = 1` using `Matrix.nonsing_inv_mul A hu`. Establish `hP : Commute Z (P.map ι)`. Establish `h1 : Commute Z (((2 : E) • P - 1).map ι + 1)` using `hg.add_right (Commute.one_right Z)`.

Rewrite `h1` using `[map_subE, map_smulE, map_oneE, sub_add_cancel]`. Establish `h3` using `h1.smul_right (ι (2 : E)⁻¹)`. Rewrite `h3` using `[smul_smul, ← map_mul, inv_mul_cancel₀ h2, map_one, one_smul]`. Then use the resulting hypothesis. Establish `hA : Commute Z (A.map ι)`. Set `u : (Matrix n n R)ˣ` to `⟨P.map ι, A.map ι, by rw [← map_mulE, hPA, map_oneE], by rw [← map_mulE, hAP, map_oneE]⟩`.

Conclude with `Commute.units_inv_right (u := u) hP`. Establish `h4 : Commute Z (ι t • X.map ι)`. Use `(Commute.one_right Z).sub_right hA` as an intermediate fact. Rewrite `this` using `[hAdef, map_subE, map_oneE, map_smulE, sub_sub_cancel]`. Then use the resulting hypothesis. Establish `h5` using `h4.smul_right (ι t⁻¹)`.

Rewrite `h5` using `[smul_smul, ← map_mul, inv_mul_cancel₀ ht0, map_one, one_smul]`. Then use the resulting hypothesis.
-/
theorem commute_skew (σ : E →+* E) (J : Matrix n n E) (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (X : Matrix n n E) (hX : Formalism.UG.cT σ X * J + J * X = 0) : Commute Z (X.map ι) := by
  classical
  have hp : X.charpolyRev ≠ 0 := by
    intro h
    have := Matrix.eval_charpolyRev (M := X)
    rw [h, Polynomial.eval_zero] at this
    exact zero_ne_one this
  obtain ⟨t, ht, hts⟩ := hF.exists_notMem_finset (insert 0 X.charpolyRev.roots.toFinset)
  have ht0 : t ≠ 0 := fun e => hts (by simp [e])
  have hdet : (1 - t • X).det ≠ 0 := by
    intro e
    apply hts
    rw [Finset.mem_insert, Multiset.mem_toFinset, Polynomial.mem_roots hp, Polynomial.IsRoot, eval_charpolyRev_eq]
    exact Or.inr e
  have hg := hZ _ (cayley_unitary σ J X t ht hX hdet)
  set A : Matrix n n E := 1 - t • X with hAdef
  set P : Matrix n n E := A⁻¹
  have hu : IsUnit A.det := isUnit_iff_ne_zero.2 hdet
  have hAP : A * P = 1 := Matrix.mul_nonsing_inv A hu
  have hPA : P * A = 1 := Matrix.nonsing_inv_mul A hu
  have hP : Commute Z (P.map ι) := by
    have h1 : Commute Z (((2 : E) • P - 1).map ι + 1) := hg.add_right (Commute.one_right Z)
    rw [map_subE, map_smulE, map_oneE, sub_add_cancel] at h1
    have h3 := h1.smul_right (ι (2 : E)⁻¹)
    rwa [smul_smul, ← map_mul, inv_mul_cancel₀ h2, map_one, one_smul] at h3
  have hA : Commute Z (A.map ι) := by
    let u : (Matrix n n R)ˣ := ⟨P.map ι, A.map ι, by rw [← map_mulE, hPA, map_oneE], by rw [← map_mulE, hAP, map_oneE]⟩
    exact Commute.units_inv_right (u := u) hP
  have h4 : Commute Z (ι t • X.map ι) := by
    have := (Commute.one_right Z).sub_right hA
    rwa [hAdef, map_subE, map_oneE, map_smulE, sub_sub_cancel] at this
  have h5 := h4.smul_right (ι t⁻¹)
  rwa [smul_smul, ← map_mul, inv_mul_cancel₀ ht0, map_one, one_smul] at h5

/- English proof (translation)
Establish `hu : IsUnit J.det` using `isUnit_iff_ne_zero.2 hJ`. Establish `hJJi : J * J⁻¹ = 1` using `Matrix.mul_nonsing_inv J hu`. Establish `hJiJ : J⁻¹ * J = 1` using `Matrix.nonsing_inv_mul J hu`. Establish `hcJi : Formalism.UG.cT σ J⁻¹ * J = 1`. Combine the equalities or inequalities in the displayed calculation.

Establish `skew : ∀ K : Matrix n n E, Formalism.UG.cT σ K = -K → Commute Z ((J⁻¹ * K).map ι)`. Introduce `K hK`. Use `commute_skew ι σ J hF h2 Z hZ _ ?_` and prove the remaining obligations. Rewrite using `[Formalism.UG.cT_mul, hK, Matrix.mul_assoc, hcJi, ← Matrix.mul_assoc, hJJi]`. Simplify using the standard rewrite rules.

Use `set K := J * M`. Establish `hK1 : Formalism.UG.cT σ (K - Formalism.UG.cT σ K) = -(K - Formalism.UG.cT σ K)`. Rewrite using `[cT_sub, cT_cT σ hσ]`. Normalize the expressions using the abelian group laws. Establish `hK2 : Formalism.UG.cT σ (ξ • (K + Formalism.UG.cT σ K)) = -(ξ • (K + Formalism.UG.cT σ K))`.

Rewrite using `[cT_smul, cT_add, cT_cT σ hσ, hξ, neg_smul, add_comm (Formalism.UG.cT σ K)]`. Establish `c1` using `skew _ hK1`. Establish `c2` using `(skew _ hK2).smul_right (ι ξ⁻¹)`. Establish `c3` using `(c1.add_right c2).smul_right (ι (2 : E)⁻¹)`. Establish `e : M = (2 : E)⁻¹ • (J⁻¹ * (K - Formalism.UG.cT σ K) + ξ⁻¹ • (J⁻¹ * (ξ • (K + Formalism.UG.cT σ K))))`.

Rewrite using `[Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ0, one_smul, ← Matrix.mul_add, sub_add_add_cancel, ← two_smul E K, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hJiJ, Matrix.one_mul]`. Rewrite using `[e, map_smulE, map_addE, map_smulE]`. Conclude with `c3`.
-/
theorem commute_all (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι))
    (M : Matrix n n E) : Commute Z (M.map ι) := by
  have hu : IsUnit J.det := isUnit_iff_ne_zero.2 hJ
  have hJJi : J * J⁻¹ = 1 := Matrix.mul_nonsing_inv J hu
  have hJiJ : J⁻¹ * J = 1 := Matrix.nonsing_inv_mul J hu
  have hcJi : Formalism.UG.cT σ J⁻¹ * J = 1 := by
    calc Formalism.UG.cT σ J⁻¹ * J = Formalism.UG.cT σ J⁻¹ * Formalism.UG.cT σ J := by rw [hJh]
      _ = 1 := by rw [← Formalism.UG.cT_mul, hJJi, Formalism.UG.cT_one]
  have skew : ∀ K : Matrix n n E, Formalism.UG.cT σ K = -K → Commute Z ((J⁻¹ * K).map ι) := by
    intro K hK
    refine commute_skew ι σ J hF h2 Z hZ _ ?_
    rw [Formalism.UG.cT_mul, hK, Matrix.mul_assoc, hcJi, ← Matrix.mul_assoc, hJJi]
    simp
  set K := J * M
  have hK1 : Formalism.UG.cT σ (K - Formalism.UG.cT σ K) = -(K - Formalism.UG.cT σ K) := by
    rw [cT_sub, cT_cT σ hσ]; abel
  have hK2 : Formalism.UG.cT σ (ξ • (K + Formalism.UG.cT σ K)) = -(ξ • (K + Formalism.UG.cT σ K)) := by
    rw [cT_smul, cT_add, cT_cT σ hσ, hξ, neg_smul, add_comm (Formalism.UG.cT σ K)]
  have c1 := skew _ hK1
  have c2 := (skew _ hK2).smul_right (ι ξ⁻¹)
  have c3 := (c1.add_right c2).smul_right (ι (2 : E)⁻¹)
  have e : M = (2 : E)⁻¹ • (J⁻¹ * (K - Formalism.UG.cT σ K) + ξ⁻¹ • (J⁻¹ * (ξ • (K + Formalism.UG.cT σ K)))) := by
    rw [Matrix.mul_smul, smul_smul, inv_mul_cancel₀ hξ0, one_smul, ← Matrix.mul_add, sub_add_add_cancel,
      ← two_smul E K, Matrix.mul_smul, smul_smul, inv_mul_cancel₀ h2, one_smul, ← Matrix.mul_assoc, hJiJ,
      Matrix.one_mul]
  rw [e, map_smulE, map_addE, map_smulE]
  exact c3

/- English proof (translation)
Establish `hs : Z ∈ Set.range (Matrix.scalar n)`. Use `Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_` and prove the remaining obligations. Use `(commute_all ι σ hσ J hJh hJ ξ hξ hξ0 hF h2 Z hZ (Matrix.single i j 1)).symm` as an intermediate fact. Establish `e : (Matrix.single i j (1 : E)).map ι = Matrix.single i j 1`. Use extensionality with `a b`.

Simplify using `[Matrix.single_apply]`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Take `⟨c, hc⟩` from `hs`. Conclude with `⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩`.
-/
theorem eq_smul_one (σ : E →+* E) (hσ : ∀ x, σ (σ x) = x) (J : Matrix n n E) (hJh : Formalism.UG.cT σ J = J)
    (hJ : J.det ≠ 0) (ξ : E) (hξ : σ ξ = -ξ) (hξ0 : ξ ≠ 0)
    (hF : {t : E | σ t = t}.Infinite) (h2 : (2 : E) ≠ 0)
    (Z : Matrix n n R) (hZ : ∀ g : Matrix n n E, Formalism.UG.cT σ g * J * g = J → Commute Z (g.map ι)) :
    ∃ c : R, Z = c • (1 : Matrix n n R) := by
  have hs : Z ∈ Set.range (Matrix.scalar n) := by
    refine Matrix.mem_range_scalar_of_commute_single fun i j _ => ?_
    have := (commute_all ι σ hσ J hJh hJ ξ hξ hξ0 hF h2 Z hZ (Matrix.single i j 1)).symm
    have e : (Matrix.single i j (1 : E)).map ι = Matrix.single i j 1 := by
      ext a b; simp [Matrix.single_apply]
    rwa [e] at this
  obtain ⟨c, hc⟩ := hs
  exact ⟨c, by rw [← hc, Matrix.scalar_apply, Matrix.smul_one_eq_diagonal]⟩

end GlobalTheory.CenterScalar

namespace GlobalTheory.CenterScalar
open Matrix Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨e, he⟩ : ∃ e : D.host.E, e ∉ (algebraMap D.host.F D.host.E).range := by`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Establish `htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤`. Use extensionality with `x`.

Simplify using `only [Algebra.mem_bot, Algebra.mem_top, iff_true]`. Conclude with `h x`. Establish `h1` using `Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop`. Rewrite `h1` using `[D.sp.cm.deg2]`. Evaluate the numerical expressions using `at h1`.

Use `⟨e - star e, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `star (e - star e) = -(e - star e)`. Rewrite using `[star_sub, star_star, neg_sub]`. Introduce `h0`. Apply `he` to reduce the goal to its premises.

Conclude with `(D.sp.cm.fixed e).1 (sub_eq_zero.1 h0).symm`.
-/
theorem exists_skew (D : D7) : ∃ ξ : D.host.E,
    (D.sp.cm.sig : D.host.E →+* D.host.E) ξ = -ξ ∧ ξ ≠ 0 := by
  obtain ⟨e, he⟩ : ∃ e : D.host.E, e ∉ (algebraMap D.host.F D.host.E).range := by
    by_contra h
    push_neg at h
    have htop : (⊥ : Subalgebra D.host.F D.host.E) = ⊤ := by
      ext x
      simp only [Algebra.mem_bot, Algebra.mem_top, iff_true]
      exact h x
    have h1 := Subalgebra.bot_eq_top_iff_finrank_eq_one.mp htop
    rw [D.sp.cm.deg2] at h1
    norm_num at h1
  refine ⟨e - star e, ?_, ?_⟩
  · change star (e - star e) = -(e - star e)
    rw [star_sub, star_star, neg_sub]
  · intro h0
    apply he
    exact (D.sp.cm.fixed e).1 (sub_eq_zero.1 h0).symm

/- English proof (translation)
Use `Set.Infinite.mono ?_ (Set.infinite_range_of_injective (algebraMap D.host.F D.host.E).injective)` and prove the remaining obligations. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `D.sp.cm.sig.commutes a`.
-/
theorem fixed_infinite (D : D7) :
    {t : D.host.E | (D.sp.cm.sig : D.host.E →+* D.host.E) t = t}.Infinite := by
  refine Set.Infinite.mono ?_ (Set.infinite_range_of_injective (algebraMap D.host.F D.host.E).injective)
  rintro _ ⟨a, rfl⟩
  exact D.sp.cm.sig.commutes a

/- English proof (translation)
Introduce `D V z hz`. Take `⟨ξ, hξ, hξ0⟩` from `exists_skew D`. Use `set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)`. Establish `hσ : ∀ x, σ (σ x) = x` using `fun x => star_star x`. Establish `hJh : Formalism.UG.cT σ V.gram = V.gram` using `Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)`.

Use `eq_smul_one (incA D) σ hσ V.gram hJh (Formalism.L2.Theta.gram_det_ne V) ξ hξ hξ0 (fixed_infinite D) two_ne_zero _ ?_` and prove the remaining obligations. Introduce `g hg`. Establish `hdet : IsUnit g.det`. Use `isUnit_iff_ne_zero.2 fun h0 => Formalism.L2.Theta.gram_det_ne V ?_` and prove the remaining obligations. Use `congrArg Matrix.det hg` as an intermediate fact.

Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, h0, mul_zero]`. Conclude with `this.symm`. Set `gG : GL (Fin V.rank) D.host.E` to `Matrix.nonsingInvUnit g hdet`. Establish `hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) = (Formalism.UG.cT σ g).map (incA D)`. Use extensionality with `i j`.

Simplify using `[Formalism.UG.cT, sigR, inclR, σ]`. Establish `hmem : Formalism.UG.bc (incA D) gG ∈ HR (AF D.host.F) D.sp.cm.sig V.gram`. Express the relevant statement in the definitionally equal form `Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) * (V.gram.map (incA D)) * g.map (incA D) = V.gram.map (incA D)`. Rewrite using `[hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]`. Set `w : GA D V` to `⟨Formalism.UG.bc (incA D) gG, hmem⟩`.

Establish `hw : Formalism.L2.Theta.mt V w = g.map (incA D)` using `rfl`. Establish `hzw : w * z = z * w` using `Subgroup.mem_center_iff.1 hz w`. Establish `e1 : Formalism.L2.Theta.mt V (w * z) = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z`. Simplify using `[Formalism.L2.Theta.mt, map_mul]`. Establish `e2 : Formalism.L2.Theta.mt V (z * w) = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w`.

Simplify using `[Formalism.L2.Theta.mt, map_mul]`. Rewrite using `[← hw]`. Express the relevant statement in the definitionally equal form `Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z`. Rewrite using `[← e1, ← e2, hzw]`.
-/
theorem center_mt_eq_smul_one : ∀ (D : D7) (V : Formalism.BasicNotions.TH.HSp D) (z : GA D V), z ∈ Subgroup.center (GA D V) →
    ∃ c : AE D, Formalism.L2.Theta.mt V z = c • (1 : Matrix (Fin V.rank) (Fin V.rank) (AE D)) := by
  intro D V z hz
  obtain ⟨ξ, hξ, hξ0⟩ := exists_skew D
  set σ : D.host.E →+* D.host.E := (D.sp.cm.sig : D.host.E →+* D.host.E)
  have hσ : ∀ x, σ (σ x) = x := fun x => star_star x
  have hJh : Formalism.UG.cT σ V.gram = V.gram := Matrix.ext fun i j => V.herm.eq (V.frame j) (V.frame i)
  refine eq_smul_one (incA D) σ hσ V.gram hJh (Formalism.L2.Theta.gram_det_ne V) ξ hξ hξ0 (fixed_infinite D)
    two_ne_zero _ ?_
  intro g hg
  have hdet : IsUnit g.det := by
    refine isUnit_iff_ne_zero.2 fun h0 => Formalism.L2.Theta.gram_det_ne V ?_
    have := congrArg Matrix.det hg
    rw [Matrix.det_mul, Matrix.det_mul, h0, mul_zero] at this
    exact this.symm
  let gG : GL (Fin V.rank) D.host.E := Matrix.nonsingInvUnit g hdet
  have hc : Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) = (Formalism.UG.cT σ g).map (incA D) := by
    ext i j
    simp [Formalism.UG.cT, sigR, inclR, σ]
  have hmem : Formalism.UG.bc (incA D) gG ∈ HR (AF D.host.F) D.sp.cm.sig V.gram := by
    change Formalism.UG.cT (sigR (AF D.host.F) D.sp.cm.sig) (g.map (incA D)) * (V.gram.map (incA D)) * g.map (incA D) =
      V.gram.map (incA D)
    rw [hc, ← Matrix.map_mul, ← Matrix.map_mul, hg]
  let w : GA D V := ⟨Formalism.UG.bc (incA D) gG, hmem⟩
  have hw : Formalism.L2.Theta.mt V w = g.map (incA D) := rfl
  have hzw : w * z = z * w := Subgroup.mem_center_iff.1 hz w
  have e1 : Formalism.L2.Theta.mt V (w * z) = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z := by
    simp [Formalism.L2.Theta.mt, map_mul]
  have e2 : Formalism.L2.Theta.mt V (z * w) = Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w := by
    simp [Formalism.L2.Theta.mt, map_mul]
  rw [← hw]
  change Formalism.L2.Theta.mt V z * Formalism.L2.Theta.mt V w = Formalism.L2.Theta.mt V w * Formalism.L2.Theta.mt V z
  rw [← e1, ← e2, hzw]

end GlobalTheory.CenterScalar
