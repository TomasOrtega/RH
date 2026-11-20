import Mathlib
import Formalism.LocalRingCardinality.RhoDetPrimeEqMuTildeMulChiPow
import Formalism.LocalToGlobal.UnitaryNorms.CharTied
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.IsRationalUnitaryDeterminantMapRationalUnitaryTo
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsUniqueIdeleOfLinearEquivQuotientLocal

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.FrobeniusOrbits Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR Formalism.L2.Host GlobalTheory.Mem.Chr
open scoped nonZeroDivisors

namespace GlobalTheory.Mem.UnitIndex

variable (L : Type) [Field L] [NumberField L]

def finIdele : Ideles L →* (FiniteAdeleRing (𝓞 L) L)ˣ :=
  Units.map (MonoidHom.snd (InfiniteAdeleRing L) (FiniteAdeleRing (𝓞 L) L))

def idealHom : (FiniteAdeleRing (𝓞 L) L)ˣ →* FractionalIdeal (𝓞 L)⁰ L where
  toFun := GlobalTheory.Idele.idealOf
  map_one' := GlobalTheory.Idele.idealOf_one
  map_mul' := GlobalTheory.Idele.idealOf_mul

def classHom : Ideles L →* ClassGroup (𝓞 L) :=
  (ClassGroup.mk L).comp ((idealHom L).comp (finIdele L)).toHomUnits

/- English proof (translation)
Introduce `a ha`. Establish `h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1` using `ha`. Rewrite `h1` using `[ClassGroup.mk_eq_one_iff]`. Take `⟨x, hx⟩` from `(FractionalIdeal.isPrincipal_iff _).1 h1`. Establish `hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x` using `hx`.

Establish `hx0 : x ≠ 0`. Introduce and unpack `rfl`. Conclude with `GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))`. Establish `hd : finIdele L (diagUnits L (Units.mk0 x hx0)) = FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0)` using `Units.ext rfl`. Establish `hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L`.

Use `(GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹)) (I := 1) one_ne_zero).1 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd, GlobalTheory.Idele.idealOf_unitEmbedding, hx']`. Conclude with `mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)`. Establish `: a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0)` using `by simp`. Rewrite using `[this]`.

Conclude with `Subgroup.mul_mem_sup hu ⟨_, rfl⟩`.
-/
theorem ker_classHom_le : (classHom L).ker ≤ unitIdl L ⊔ (diagUnits L).range := by
  intro a ha
  have h1 : ClassGroup.mk L (((idealHom L).comp (finIdele L)).toHomUnits a) = 1 := ha
  rw [ClassGroup.mk_eq_one_iff] at h1
  obtain ⟨x, hx⟩ := (FractionalIdeal.isPrincipal_iff _).1 h1
  have hx' : GlobalTheory.Idele.idealOf (finIdele L a) = FractionalIdeal.spanSingleton (𝓞 L)⁰ x := hx
  have hx0 : x ≠ 0 := by
    rintro rfl
    exact GlobalTheory.Idele.idealOf_ne_zero _ (hx'.trans (FractionalIdeal.spanSingleton_zero))
  have hd : finIdele L (diagUnits L (Units.mk0 x hx0)) =
      FiniteAdeleRing.unitEmbedding (𝓞 L) L (Units.mk0 x hx0) := Units.ext rfl
  have hu : a * (diagUnits L (Units.mk0 x hx0))⁻¹ ∈ unitIdl L := by
    refine (GlobalTheory.Idele.smul_eq_self_iff (finIdele L (a * (diagUnits L (Units.mk0 x hx0))⁻¹))
      (I := 1) one_ne_zero).1 ?_
    rw [GlobalTheory.Idele.smul_one_eq, map_mul, map_inv, GlobalTheory.Idele.idealOf_mul, GlobalTheory.Idele.idealOf_inv, hd,
      GlobalTheory.Idele.idealOf_unitEmbedding, hx']
    exact mul_inv_cancel₀ (FractionalIdeal.spanSingleton_ne_zero_iff.2 hx0)
  have : a = a * (diagUnits L (Units.mk0 x hx0))⁻¹ * diagUnits L (Units.mk0 x hx0) := by simp
  rw [this]
  exact Subgroup.mul_mem_sup hu ⟨_, rfl⟩

open Classical in

/- English proof (translation)
Introduce `L _ _`. Establish `: (classHom L).ker.FiniteIndex` using `Subgroup.finiteIndex_ker _`. Conclude with `Subgroup.finiteIndex_of_le (ker_classHom_le L)`.
-/
theorem finiteIndex_unitIdl_sup : ∀ (L : Type) [Field L] [NumberField L],
    (unitIdl L ⊔ (diagUnits L).range).FiniteIndex := by
  intro L _ _
  have : (classHom L).ker.FiniteIndex := Subgroup.finiteIndex_ker _
  exact Subgroup.finiteIndex_of_le (ker_classHom_le L)

end GlobalTheory.Mem.UnitIndex
