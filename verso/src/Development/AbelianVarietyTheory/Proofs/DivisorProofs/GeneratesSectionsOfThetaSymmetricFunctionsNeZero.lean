import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreExistsGeneratorStable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSymmetricFunctionsDegreeFactorialBasicPrope
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaConstantListAlgClosedStatement
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsSinglePolarisationGeneratorAllTraits
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsGlueRigidifiedLineBundlesCover
import Development.AbelianVarietyTheory.Statements.PrincipalLattices.LogHermFormOfUnitDiscriminant
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsWithoutCohomology
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipallyPolarisedFibreIffOfGrpPullback
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin.GenSym

/- English proof (translation)
Take `⟨P, α, hg, hα, hPL⟩` from `h`. Take `⟨P', ψ, hg', hψ, hPL'⟩` from `exists_isPolFibre polBaseChange_holds i P`. Use `⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩` and prove the remaining obligations. Conclude with `LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL _) hPL'.symm (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL α) ψ) (pull_isLB hL _) (RigidBundleGlue.LBIso.pull hPL ψ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp hL α ψ).symm)`.
-/
theorem polFib_base {S : Scheme.{0}} {G : Over S} [GrpObj G] {L : LB G.left} (hL : L.IsLB) {g : ℕ} {R R' : Type}
    [CommRing R] [CommRing R'] {x : Sp R ⟶ S} (i : R →+* R') (h : PolFib G L g x) : PolFib G L g (spMap i ≫ x) := by
  obtain ⟨P, α, hg, hα, hPL⟩ := h
  obtain ⟨P', ψ, hg', hψ, hPL'⟩ := exists_isPolFibre polBaseChange_holds i P
  refine ⟨P', ψ ≫ α, hg'.trans hg, hψ.comp hα, ?_⟩
  exact LBIso.trans P'.isLB (pull_isLB P.isLB ψ) (pull_isLB hL _) hPL'.symm
    (LBIso.trans (pull_isLB P.isLB ψ) (pull_isLB (pull_isLB hL α) ψ) (pull_isLB hL _)
      (RigidBundleGlue.LBIso.pull hPL ψ) (GlobalTheory.UMin.FibMove.lbIso_pull_comp hL α ψ).symm)

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m N Ω _ _ x θ e hm hN hpol hsym hne`. Take `⟨⟨θ₁, h₁⟩, -⟩` from `GlobalTheory.UMin.gen_of_polFib S G L hL g Ω x hpol`. Take `⟨r, hr⟩` from `(isGenSec_iff θ₁).1 h₁ (SecM.ofSec G θ)`. Take `⟨a, rfl⟩` from `(fnR x).surjective r`. Distinguish the cases in `ha : a = 0`.

It suffices to derive a contradiction. Substitute `ha` using the available equality. Set `K` to `AlgebraicClosure Ω`. Set `i : Ω →+* K` to `algebraMap Ω K`. Establish `hpol' : PolFib G L g (spMap i ≫ x)` using `polFib_base hL i hpol`.

Establish `hmK : (m : K) ≠ 0`. Establish `: m ≠ 0` using `by rintro rfl; exact (Nat.not_odd_zero hm)`. Conclude with `this` after adjusting the coercions. Take `⟨pt, c, hl⟩` from `GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m N K (spMap i ≫ x) (SecAt.pull G L θ₁ i) hm hmK hN hpol'`. Establish `h0 : SecM.ofSec G (SecAt.pull G L θ i) = (0 : Γ((Over.mk (spMap i ≫ x)).left, ⊤)) • SecM.ofSec G (SecAt.pull G L θ₁ i)`.

Establish `q` using `congrArg (pl i rfl) hr`. Rewrite `q` using `[pl_smul, map_zero, map_zero, pl_ofSec, pl_ofSec]`. Conclude with `q`. Establish `hl' : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => 0 * c b)`. Use `⟨hl.1, fun b => ?_, hl.2.2⟩` and prove the remaining obligations.

Establish `q` using `ThG.smul hL h0 (hl.2.1 b)`. Simplify using `using q`. Take `⟨j, hj⟩` from `hne`. Establish `q` using `hsym K i pt _ hl' j`. Rewrite `q` using `[(GlobalTheory.UMin.symTup_basic).1 K N c 0 j, zero_pow (Nat.factorial_ne_zero N), zero_mul]`.

Conclude with `hj (i.injective (q.trans (map_zero i).symm))`. Use `(isGenSec_iff θ).2 fun s => ?_` and prove the remaining obligations. Take `⟨r', hr'⟩` from `(isGenSec_iff θ₁).1 h₁ s`. Use `⟨r' * fnR x a⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hr', hr, smul_smul, _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, _root_.mul_one]`.
-/
theorem isGenSec_of_symAt : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left)
    (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m N : ℕ) (Ω : Type) [Field Ω] [CharZero Ω]
    (x : Sp Ω ⟶ S) (θ : SecAt G L x) (e : Fin N → Ω), Odd m → N = m ^ (4 * g) → PolFib G L g x →
    SymAt G L ρ m x θ e → (∃ j, e j ≠ 0) → IsGenSec G L ((1 : ℕ) : ℤ) θ := by
  intro S G _ _ L ρ hL hρ g m N Ω _ _ x θ e hm hN hpol hsym hne
  obtain ⟨⟨θ₁, h₁⟩, -⟩ := GlobalTheory.UMin.gen_of_polFib S G L hL g Ω x hpol
  obtain ⟨r, hr⟩ := (isGenSec_iff θ₁).1 h₁ (SecM.ofSec G θ)
  obtain ⟨a, rfl⟩ := (fnR x).surjective r
  by_cases ha : a = 0
  · exfalso
    subst ha
    let K := AlgebraicClosure Ω
    let i : Ω →+* K := algebraMap Ω K
    have hpol' : PolFib G L g (spMap i ≫ x) := polFib_base hL i hpol
    have hmK : (m : K) ≠ 0 := by
      have : m ≠ 0 := by rintro rfl; exact (Nat.not_odd_zero hm)
      exact_mod_cast this
    obtain ⟨pt, c, hl⟩ := GlobalTheory.T.exists_thetaConstantList_algClosed S G L ρ hL hρ g m N K (spMap i ≫ x) (SecAt.pull G L θ₁ i) hm hmK hN hpol'
    have h0 : SecM.ofSec G (SecAt.pull G L θ i) = (0 : Γ((Over.mk (spMap i ≫ x)).left, ⊤)) •
        SecM.ofSec G (SecAt.pull G L θ₁ i) := by
      have q := congrArg (pl i rfl) hr
      rw [pl_smul, map_zero, map_zero, pl_ofSec, pl_ofSec] at q
      exact q
    have hl' : ThList G L ρ m (spMap i ≫ x) (SecAt.pull G L θ i) pt (fun b => 0 * c b) := by
      refine ⟨hl.1, fun b => ?_, hl.2.2⟩
      have q := ThG.smul hL h0 (hl.2.1 b)
      simpa using q
    obtain ⟨j, hj⟩ := hne
    have q := hsym K i pt _ hl' j
    rw [(GlobalTheory.UMin.symTup_basic).1 K N c 0 j, zero_pow (Nat.factorial_ne_zero N), zero_mul] at q
    exact hj (i.injective (q.trans (map_zero i).symm))
  · refine (isGenSec_iff θ).2 fun s => ?_
    obtain ⟨r', hr'⟩ := (isGenSec_iff θ₁).1 h₁ s
    refine ⟨r' * fnR x a⁻¹, ?_⟩
    rw [hr', hr, smul_smul, _root_.mul_assoc, ← map_mul, inv_mul_cancel₀ ha, map_one, _root_.mul_one]

end GlobalTheory.UMin.GenSym
end
