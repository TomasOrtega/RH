import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.FactTypePrime
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsArchimedeanLiftUnitaryGroupProduct
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContDiffDerivSnoc
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteSmoothIrreducible

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S IsDedekindDomain NumberField
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.DivisionValues
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Cx Formalism.IndefR.Links
open Formalism.IndefR.Datum (InfFam)
open GlobalTheory.DefFree GlobalTheory.DefLift Polynomial
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.RealAct

variable {D : D7} {θ : InfFam D} {V : HSp D} {S : D.what₂.Tau → SPar}

def ActsLin (θ : InfFam D) (M : DSModel V S) (k : GA D V) : Prop :=
  ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ),
    ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T)

/- English proof (translation)
Use `⟨LinearMap.id, ?_⟩` and prove the remaining obligations. Introduce `J χ T _ g`. Rewrite using `[mul_one]`. Both sides reduce to the same expression.
-/
theorem actsLin_one (M : DSModel V S) : ActsLin θ M 1 := by
  refine ⟨LinearMap.id, ?_⟩
  intro J χ T _ g
  rw [mul_one]
  rfl

/- English proof (translation)
Take `⟨φa, hφa⟩` from `ha`. Take `⟨φb, hφb⟩` from `hb`. Use `⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem actsLin_mul {M : DSModel V S} {a b : GA D V} (ha : ActsLin θ M a) (hb : ActsLin θ M b) :
    ActsLin θ M (a * b) := by
  obtain ⟨φa, hφa⟩ := ha
  obtain ⟨φb, hφb⟩ := hb
  refine ⟨φb ∘ₗ φa, fun J χ T hT g => ?_⟩
  calc evAt M (g * (a * b)) T = evAt M ((g * a) * b) T := by rw [mul_assoc]
    _ = φb (evAt M (g * a) T) := hφb J χ T hT (g * a)
    _ = φb (φa (evAt M g T)) := by rw [hφa J χ T hT g]

/- English proof (translation)
Establish `htop : M.sm τ = ⊤` using `(AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1`. Set `A : M.sm τ →ₗ[ℂ] M.sm τ` to `(M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)`. Set `F : ∀ i, M.sm i →ₗ[ℂ] M.sm i` to `Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A`. Use `⟨MultilinearMap.compLinearMapₗ F, ?_⟩` and prove the remaining obligations. Introduce `J χ T hT g`.

Establish `hmap` using `(GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT`. Use extensionality with `v`. Establish `hv : (fun i => F i (v i)) = Function.update v τ (A (v τ))`. Use function extensionality and compare the values at `i`. Distinguish the cases in `h : i = τ`.

Substitute `h` using the available equality. Simplify using `[F]`. Simplify using `[F, h]`. Establish `hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ)` using `rfl`. Establish `key` using `congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g`.

Rewrite using `[evAt_apply]`. Simplify using `only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]`. Rewrite using `[evAt_apply, hv, key]`. Both sides reduce to the same expression.
-/
theorem actsLin_atTau {M : DSModel V S} (hM : AllPlus M) (τ : D.what₂.Tau)
    {u : Matrix (Fin V.rank) (Fin V.rank) ℂ} (hu : u ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)) :
    ActsLin θ M (atTau θ V τ u) := by
  classical
  have htop : M.sm τ = ⊤ := (AllPlus.finite_smooth_irreducible _ V S M hM τ).2.1
  let A : M.sm τ →ₗ[ℂ] M.sm τ :=
    (M.rep τ u).toLinearMap.restrict (fun x _ => by rw [htop]; exact Submodule.mem_top)
  let F : ∀ i, M.sm i →ₗ[ℂ] M.sm i := Function.update (fun i => (LinearMap.id : M.sm i →ₗ[ℂ] M.sm i)) τ A
  refine ⟨MultilinearMap.compLinearMapₗ F, ?_⟩
  intro J χ T hT g
  have hmap := (GlobalTheory.MultMem.mem_mult_iff _ θ V S M J χ T).1 hT
  ext v
  have hv : (fun i => F i (v i)) = Function.update v τ (A (v τ)) := by
    funext i
    by_cases h : i = τ
    · subst h
      simp [F]
    · simp [F, h]
  have hw : ((A (v τ) : M.sm τ) : M.H τ) = M.rep τ u (v τ) := rfl
  have key := congrFun (hmap.equiv τ u hu v (A (v τ)) hw) g
  rw [evAt_apply]
  simp only [MultilinearMap.compLinearMapₗ_apply, MultilinearMap.compLinearMap_apply]
  rw [evAt_apply, hv, key]
  rfl

/- English proof (translation)
Introduce `D θ V S M hθ hM k hk`. Take `⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩` from `GlobalTheory.RealLift.exists_real_lift D θ V hθ`. Take `⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k` from `⟨_, hLarch k, hLinv k hk⟩`. Establish `haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)` using `hUa`. Establish `h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ)`.

Introduce `τ`. Simplify using `[Formalism.QuantumDeterminants.UH]`. Establish `hL1 : L 1 = 1`. Establish `h` using `hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)`. Rewrite `h` using `[mul_one]`.

Combine the equalities or inequalities in the displayed calculation. Establish `hpart : ∀ s : Finset D.what₂.Tau, ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1)`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`.

Establish `he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Rewrite using `[he, hL1]`. Conclude with `actsLin_one M`.

Consider the case `insert x s hx ih`. Establish `hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V)`. Introduce `τ`. Distinguish the cases in `h : τ ∈ s`. Simplify `haU τ` using `[h]`.

Simplify `h1U τ` using `[h]`. Establish `hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V)`. Introduce `τ`. Distinguish the cases in `h : τ = x`. Substitute `h` using the available equality.

Simplify using `using haU τ`. Simplify `h1U τ` using `[Pi.mulSingle_apply, h]`. Establish `hsplit : (fun τ => if τ ∈ insert x s then a τ else 1) = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = x`.

Substitute `h` using the available equality. Simplify using `[hx]`. Simplify using `[h, Pi.mulSingle_apply]`. Rewrite using `[hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]`. Conclude with `actsLin_mul (actsLin_atTau hM x (haU x)) ih`.

Establish `hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a`. Use function extensionality and compare the values at `τ`. Simplify using the standard rewrite rules. Use `hpart Finset.univ` as an intermediate fact. Rewrite `this` using `[hall, hkL]`.

Conclude with `this`.
-/
theorem real_acts : ∀ (D : D7) (θ : InfFam D) (V : HSp D) (S : D.what₂.Tau → SPar) (M : DSModel V S), IsInfFam θ → AllPlus M → ∀ k ∈ GinfC V, ∃ φ : Module.End ℂ (MultilinearMap ℂ (fun τ : D.what₂.Tau => M.sm τ) ℂ), ∀ (J : Set (GA D V)) (χ : GA D V → ℂ), ∀ T ∈ Mult θ M J χ, ∀ g : GA D V, evAt M (g * k) T = φ (evAt M g T) := by
  intro D θ V S M hθ hM k hk
  classical
  obtain ⟨L, -, hLmul, -, hLarch, hLinv, hLat, -⟩ := GlobalTheory.RealLift.exists_real_lift D θ V hθ
  obtain ⟨a, hUa, hkL⟩ : ∃ a, a ∈ GlobalTheory.HolDict.UG (gramAt D V) ∧ L a = k := ⟨_, hLarch k, hLinv k hk⟩
  have haU : ∀ τ, a τ ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := hUa
  have h1U : ∀ τ, (1 : Matrix (Fin V.rank) (Fin V.rank) ℂ) ∈ Formalism.QuantumDeterminants.UH (gramAt D V τ) := by
    intro τ
    simp [Formalism.QuantumDeterminants.UH]
  have hL1 : L 1 = 1 := by
    have h := hLmul 1 (fun τ => h1U τ) 1 (fun τ => h1U τ)
    rw [mul_one] at h
    calc L 1 = (L 1)⁻¹ * (L 1 * L 1) := by group
      _ = (L 1)⁻¹ * L 1 := by rw [← h]
      _ = 1 := inv_mul_cancel _
  have hpart : ∀ s : Finset D.what₂.Tau,
      ActsLin θ M (L fun τ => if τ ∈ s then a τ else 1) := by
    intro s
    induction s using Finset.induction_on with
    | empty =>
      have he : (fun τ : D.what₂.Tau => if τ ∈ (∅ : Finset D.what₂.Tau) then a τ else 1) = 1 := by
        funext τ
        simp
      rw [he, hL1]
      exact actsLin_one M
    | insert x s hx ih =>
      have hs : (fun τ => if τ ∈ s then a τ else 1) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ ∈ s
        · simpa [h] using haU τ
        · simpa [h] using h1U τ
      have hsing : Pi.mulSingle x (a x) ∈ GlobalTheory.HolDict.UG (gramAt D V) := by
        intro τ
        by_cases h : τ = x
        · subst h
          simpa using haU τ
        · simpa [Pi.mulSingle_apply, h] using h1U τ
      have hsplit : (fun τ => if τ ∈ insert x s then a τ else 1)
          = Pi.mulSingle x (a x) * fun τ => if τ ∈ s then a τ else 1 := by
        funext τ
        by_cases h : τ = x
        · subst h
          simp [hx]
        · simp [h, Pi.mulSingle_apply]
      rw [hsplit, hLmul _ hsing _ hs, ← hLat x (a x) (haU x)]
      exact actsLin_mul (actsLin_atTau hM x (haU x)) ih
  have hall : (fun τ => if τ ∈ (Finset.univ : Finset D.what₂.Tau) then a τ else 1) = a := by
    funext τ
    simp
  have := hpart Finset.univ
  rw [hall, hkL] at this
  exact this

end GlobalTheory.RealAct

end
