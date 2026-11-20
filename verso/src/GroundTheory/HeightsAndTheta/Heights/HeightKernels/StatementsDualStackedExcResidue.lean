import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HeightKernels.StatementsDualStackedExcLinear
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open ReciprocityTheory.ChartRestriction.G.Geo MvPolynomial NumberField

noncomputable section

def IsExcResidueData {K : Type} [Field K] [NumberField K] {i : ℕ} {F F' : HermLattice K i} {T : Type}
    (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F')) {k : Type} [Field k]
    (α : T → k) (M : T → Fin i → k) : Prop :=
  ∃ (ρ : 𝓞 K →+* k) (ρ' : dualLattice F' →+ k) (σ : dualLattice F →+ (Fin i → k)),
    Function.Surjective ρ ∧ Function.Surjective ρ' ∧ Function.Surjective σ ∧
    (∀ φ : dualLattice F', ρ' φ = 0 ↔ (φ : Fin i → K) ∈ dualLattice F) ∧
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F'),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → ρ' ψ = ρ μ * ρ' φ) ∧
    (∀ (μ : 𝓞 K) (φ ψ : dualLattice F),
      (ψ : Fin i → K) = algebraMap (𝓞 K) K μ • (φ : Fin i → K) → σ ψ = ρ μ • σ φ) ∧
    (∀ t, α t = ρ' (b' t)) ∧ ∀ t, M t = σ (b t)

def DualStackedExcResidueExists.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∃ (k : Type) (_ : Field k) (_ : Fintype k) (α : T → k) (M : T → Fin i → k),
      IsExcResidueData b b' α M ∧ Fintype.card k = F'.lattice.toAddSubgroup.relIndex F.lattice.toAddSubgroup

def DualStackedExcBaseLe.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      stackedBase b' a ≤ linPrime α M

def DualStackedExcLinPrimeLe.Statement : Prop :=
  ∀ (K : Type) [Field K] [NumberField K] (i : ℕ) (F F' : HermLattice K i) (T : Type) [Fintype T]
    [DecidableEq T] (b : Module.Basis T ℤ (dualLattice F)) (b' : Module.Basis T ℤ (dualLattice F'))
    (a : T → ℤ),
    1 ≤ i → F'.lattice < F.lattice →
    (∀ N : Submodule (𝓞 K) (Fin i → K), F'.lattice ≤ N → N ≤ F.lattice → N = F'.lattice ∨ N = F.lattice) →
    (∀ t, (b t : Fin i → K) = a t • (b' t : Fin i → K)) →
    ∀ (k : Type) [Field k] (α : T → k) (M : T → Fin i → k), IsExcResidueData b b' α M →
      ∀ P : Ideal (MRing (stackedBlocks T)), P.IsPrime → stackedBase b' a ≤ P → IsRelevant P →
        linPrime α M ≤ P

namespace DualStackedExcResidueExample

open DualTopSimpleSubExample DualStackedExcExample

/- English proof (translation)
Introduce `x hx`. Take `⟨m, hm⟩` from `coord_of_mem_two hx`. Use `⟨(m : 𝓞 ℚ), ?_⟩` and prove the remaining obligations. Simplify using `[dotProduct, hm]`.
-/
theorem half_mem : (fun _ : Fin 1 => (1 / 2 : ℚ)) ∈ dualLattice HermLattice.twiceStandardExample := by
  intro x hx
  obtain ⟨m, hm⟩ := coord_of_mem_two hx
  refine ⟨(m : 𝓞 ℚ), ?_⟩
  simp [dotProduct, hm]

def halfDual : dualLattice HermLattice.twiceStandardExample := ⟨fun _ => 1 / 2, half_mem⟩

/- English proof (translation)
Use `linearIndependent_unique_iff.mpr fun h => ?_` and prove the remaining obligations. Establish `h1 : ((halfDual : dualLattice HermLattice.twiceStandardExample) : Fin 1 → ℚ) 0 = 0`. Rewrite using `[h]`. Both sides reduce to the same expression. Evaluate the numerical expressions using `[halfDual] at h1`.
-/
theorem halfDual_linearIndependent : LinearIndependent ℤ (fun _ : Unit => halfDual) := by
  refine linearIndependent_unique_iff.mpr fun h => ?_
  have h1 : ((halfDual : dualLattice HermLattice.twiceStandardExample) : Fin 1 → ℚ) 0 = 0 := by
    rw [h]; rfl
  norm_num [halfDual] at h1

/- English proof (translation)
Introduce and unpack `⟨φ, hφ⟩ -`. Take `⟨c, hc⟩` from `hφ twoVecExample (Submodule.subset_span rfl)`. Establish `h0 : φ 0 = (Rat.ringOfIntegersEquiv c : ℚ) / 2`. Rewrite using `[Rat.ringOfIntegersEquiv_apply_coe]`. Establish `: φ ⬝ᵥ twoVecExample = 2 * φ 0` using `by simp [dotProduct, twoVecExample, mul_comm]`.

Rewrite `hc` using `[this]`. Express the relevant statement in the definitionally equal form `(c : ℚ) = 2 * φ 0 at hc`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[Set.range_const]`. Use `Submodule.mem_span_singleton.mpr ⟨Rat.ringOfIntegersEquiv c, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Use `show ((Rat.ringOfIntegersEquiv c : ℤ) : ℚ) * (1 / 2) = φ 0`. Rewrite using `[h0]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem halfDual_span : ⊤ ≤ Submodule.span ℤ (Set.range fun _ : Unit => halfDual) := by
  rintro ⟨φ, hφ⟩ -
  obtain ⟨c, hc⟩ := hφ twoVecExample (Submodule.subset_span rfl)
  have h0 : φ 0 = (Rat.ringOfIntegersEquiv c : ℚ) / 2 := by
    rw [Rat.ringOfIntegersEquiv_apply_coe]
    have : φ ⬝ᵥ twoVecExample = 2 * φ 0 := by simp [dotProduct, twoVecExample, mul_comm]
    rw [this] at hc
    change (c : ℚ) = 2 * φ 0 at hc
    linarith
  rw [Set.range_const]
  refine Submodule.mem_span_singleton.mpr ⟨Rat.ringOfIntegersEquiv c, ?_⟩
  apply Subtype.ext
  funext j
  fin_cases j
  show ((Rat.ringOfIntegersEquiv c : ℤ) : ℚ) * (1 / 2) = φ 0
  rw [h0]
  ring

def halfBasis : Module.Basis Unit ℤ (dualLattice HermLattice.twiceStandardExample) :=
  Module.Basis.mk halfDual_linearIndependent halfDual_span

/- English proof (translation)
Simplify using `[halfBasis]`.
-/
theorem halfBasis_apply (t : Unit) : halfBasis t = halfDual := by
  simp [halfBasis]

def redTwo : 𝓞 ℚ →+* ZMod 2 := (Int.castRingHom (ZMod 2)).comp Rat.ringOfIntegersEquiv.toRingHom

def rhoHalf : dualLattice HermLattice.twiceStandardExample →+ ZMod 2 :=
  (Int.castAddHom (ZMod 2)).comp (halfBasis.coord ()).toAddMonoidHom

def sigmaOne : dualLattice (HermLattice.standard ℚ 1) →+ (Fin 1 → ZMod 2) :=
  AddMonoidHom.pi fun _ => (Int.castAddHom (ZMod 2)).comp (dualBasisStandard.coord ()).toAddMonoidHom

end DualStackedExcResidueExample

end

end GroundTheory.Heights₂.Heights
