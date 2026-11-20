import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

noncomputable section

namespace GlobalTheory.EtC.GalSec

variable (K Ω : Type) [Field K] [Field Ω] [Algebra K Ω]

abbrev LCRing (k : ℕ) : Type := LocallyConstant (Fin k → (Ω ≃ₐ[K] Ω)) Ω

/- English proof (translation)
Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem isLocallyConstant_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) :
    IsLocallyConstant (fun g : Fin k → (Ω ≃ₐ[K] Ω) => g i a) := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g₀
  have hfd : FiniteDimensional K (IntermediateField.adjoin K {a}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral a)
  have hopen : IsOpen {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    (IntermediateField.fixingSubgroup_isOpen _).preimage (continuous_const.mul continuous_id)
  have hmem : ∀ᶠ g in nhds g₀, g i ∈ {σ : Ω ≃ₐ[K] Ω | (g₀ i)⁻¹ * σ ∈ (IntermediateField.adjoin K {a}).fixingSubgroup} :=
    ((continuous_apply i).tendsto g₀).eventually (hopen.mem_nhds (by simp [one_mem]))
  filter_upwards [hmem] with g hg
  have h1 := (IntermediateField.mem_fixingSubgroup_iff _ _).1 hg a (IntermediateField.mem_adjoin_simple_self K a)
  have h2 := congrArg (g₀ i) h1
  simpa [AlgEquiv.mul_apply] using h2

def coord [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) : Ω →+* LCRing K Ω k where
  toFun a := ⟨fun g => g i a, isLocallyConstant_apply K Ω k i a⟩
  map_one' := LocallyConstant.ext fun g => by simp
  map_mul' a b := LocallyConstant.ext fun g => by simp
  map_zero' := LocallyConstant.ext fun g => by simp
  map_add' a b := LocallyConstant.ext fun g => by simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem coord_apply [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin k) (a : Ω) (g : Fin k → (Ω ≃ₐ[K] Ω)) :
    coord K Ω k i a g = g i a := rfl

def legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) : Fin (k + 1) → (Ω →+* LCRing K Ω k) :=
  Fin.cases LocallyConstant.constRingHom (coord K Ω k)

def baseHom (k : ℕ) : K →+* LCRing K Ω k := LocallyConstant.constRingHom.comp (algebraMap K Ω)

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Both sides reduce to the same expression. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem legHom_comp [Algebra.IsAlgebraic K Ω] (k : ℕ) (i : Fin (k + 1)) :
    (legHom K Ω k i).comp (algebraMap K Ω) = baseHom K Ω k := by
  refine Fin.cases ?_ (fun j => ?_) i
  · rfl
  · ext c g
    simp [legHom, baseHom]

def cone [Algebra.IsAlgebraic K Ω] (k : ℕ) :
    WidePullbackCone (fun _ : Fin (k + 1) => Spec.map (CommRingCat.ofHom (algebraMap K Ω))) :=
  WidePullbackCone.mk (Spec.map (CommRingCat.ofHom (baseHom K Ω k)))
    (fun i => Spec.map (CommRingCat.ofHom (legHom K Ω k i)))
    (fun i => by rw [← Spec.map_comp, ← CommRingCat.ofHom_comp, legHom_comp])

def tailG (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : Fin k → (Ω ≃ₐ[K] Ω) := fun i => (σ 0)⁻¹ * σ i.succ

def ptHom (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) : LCRing K Ω k →+* Ω :=
  ((σ 0 : Ω ≃ₐ[K] Ω) : Ω →+* Ω).comp (LocallyConstant.evalRingHom (tailG K Ω k σ))

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. By extensionality, compare the relevant components. Simplify using the standard rewrite rules.
-/
theorem ptHom_legHom [Algebra.IsAlgebraic K Ω] (k : ℕ) (σ : Fin (k + 1) → (Ω ≃ₐ[K] Ω)) (i : Fin (k + 1)) :
    (ptHom K Ω k σ).comp (legHom K Ω k i) = ((σ i : Ω ≃ₐ[K] Ω) : Ω →+* Ω) := by
  refine Fin.cases ?_ (fun j => ?_) i
  · ext a; simp [ptHom, legHom]
  · ext a; simp [ptHom, legHom, tailG, AlgEquiv.mul_apply]

end GlobalTheory.EtC.GalSec

end
