import Mathlib
import Formalism.LocalToGlobal.GaloisLevelStructure.DefsAut
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCompAtEqZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsRealAdd

open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2

noncomputable section

namespace GlobalTheory.SplitLocComm

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

local notation3 "L⁺" => maximalRealSubfield L

/- English proof (translation)
Establish `hx' : s.loc n x⁻¹ = 1` using `by rw [map_inv, hx, inv_one]`. Use extensionality with `i j`. Establish `hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i`. Establish `hm` using `x.2`. Simplify using `only [GA, UGroup, Subgroup.mem_mk] at hm`.

Establish `h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1` using `Units.inv_eq_of_mul_eq_one_right hm`. Simplify using `only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]`. Establish `hz : compAt L s.v ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0`. Apply `GlobalTheory.SplitComp.compAt_eq_zero L s` to reduce the goal to its premises. Establish `e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j` using `rfl`.

Rewrite using `[map_sub, e1, hx]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) = ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i` using `rfl`. Rewrite using `[map_sub, map_sub, hconj, e1, hx']`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]`.

Rewrite `hz` using `[map_sub, sub_eq_zero]`. Rewrite using `[Matrix.map_apply, hz]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.
-/
theorem map_compAt_eq_one {n : ℕ} (s : SplitPlace L) (x : GA L n) (hx : s.loc n x = 1) :
    (x.1 : Matrix (Fin n) (Fin n) (AL L)).map (compAt L s.v) = 1 := by
  have hx' : s.loc n x⁻¹ = 1 := by rw [map_inv, hx, inv_one]
  ext i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    have hm := x.2
    simp only [GA, UGroup, Subgroup.mem_mk] at hm
    have h1 : ((x.1⁻¹ : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = conjT (conjAL L) x.1 :=
      Units.inv_eq_of_mul_eq_one_right hm
    simp only [InvMemClass.coe_inv, h1, conjT, Matrix.transpose_apply, Matrix.map_apply]
  have hz : compAt L s.v ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j) = 0 := by
    apply GlobalTheory.SplitComp.compAt_eq_zero L s
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1, hx]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GA L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1, hx']
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij, eq_comm]
  rw [map_sub, sub_eq_zero] at hz
  rw [Matrix.map_apply, hz]
  by_cases hij : i = j <;> simp [Matrix.one_apply, hij]

/- English proof (translation)
Introduce `L _ _ _ n s x y hx hy`. Use `Subtype.ext (Units.ext ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) = (y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))`. Use extensionality with `i j`. Rewrite using `[← sub_eq_zero]`.

Use `GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero L _ fun w => ?_` and prove the remaining obligations. Establish `h : ((x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) = ((y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w)`. Rewrite using `[Matrix.map_mul, Matrix.map_mul]`. Distinguish the cases in `hw : w = s.v`. Substitute `hw` using the available equality.

Rewrite using `[map_compAt_eq_one s x hx, one_mul, mul_one]`. Rewrite using `[hy w (by simpa using hw), one_mul, mul_one]`. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `congrFun (congrFun h i) j`.
-/
theorem commute_of_loc_eq_one : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (s : SplitPlace L)
    (x y : GAf L n), s.loc n x = 1 → TrivOutside {s.v} y → Commute x y := by
  intro L _ _ _ n s x y hx hy
  refine Subtype.ext (Units.ext ?_)
  change (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) =
    (y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))
  ext i j
  rw [← sub_eq_zero]
  refine GlobalTheory.AdelicComp.eq_zero_of_compAt_eq_zero L _ fun w => ?_
  have h : ((x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) =
      ((y.1 : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L))).map (compAt L w) := by
    rw [Matrix.map_mul, Matrix.map_mul]
    by_cases hw : w = s.v
    · subst hw
      rw [map_compAt_eq_one s x hx, one_mul, mul_one]
    · rw [hy w (by simpa using hw), one_mul, mul_one]
  rw [map_sub, sub_eq_zero]
  exact congrFun (congrFun h i) j

end GlobalTheory.SplitLocComm
