import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.LocCoh
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.TwistStep
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FinrankInvariantsEqOfInvertiblePeriodMatrixStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TensorProductBasisCoordinatesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.Pst GlobalTheory.PMon TensorProduct Module
open scoped Formalism.Per

namespace GlobalTheory.PMon

/- English proof (translation)
Introduce `l _ P n _ _ K V _ _ b ρ Q hQ`. Use `haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK`. Use `haveI : Nontrivial P.R.BdR := by`. Use `⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩` and prove the remaining obligations. Rewrite using `[h]`.

Conclude with `Submodule.zero_mem _`. Take `⟨e, -, -, he⟩` from `GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] P.R.BdR V n b`. Establish `hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x` using `fun g x => P.PD_actdR K g x`. Establish `key` using `GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K) (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR)) (fun x => ⟨fun h => (P.PD K).invdR x h, by`. Introduce and unpack `⟨c, rfl⟩ g`.

Conclude with `((P.PD K).actdR g).commutes c⟩) Q`. Use the proof step `(fun g => by`. Establish `h` using `hQ g`. Establish `: (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l)`. Use function extensionality and compare the values at `(hact g)`.

Rewrite using `[this]`. Conclude with `h)`. Use the proof step `((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))`. Use the proof step `(fun x => by`. Take `⟨y, rfl⟩` from `e.surjective x`.

Establish `h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔ y ∈ DdR (P.PD K) ρ`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, hzy⟩`. Establish `: z = y` using `e.injective hzy`. Conclude with `this ▸ hz`.

Conclude with `fun h => ⟨y, h, rfl⟩`. Rewrite using `[h1]`. Simplify using `only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply, LinearMap.id_apply, sub_eq_zero]`. Use `forall_congr' fun g => ?_` and prove the remaining obligations. Establish `h2` using `he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y`.

Establish `h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y` using `rfl`. Rewrite using `[h3, ← e.injective.eq_iff, h2]`. Use the proof step `rfl)`. Rewrite `key` using `[LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b]`. Conclude with `key`.
-/
theorem isDR_of_periodMatrix : ∀ (l : ℕ) [Fact l.Prime] (P : LocPrime l) (n : Type) [Fintype n] [DecidableEq n] (K : FinExt l) (V : Type) [AddCommGroup V] [Module ℚ_[l] V] (b : Basis n ℚ_[l] V) (ρ : Representation ℚ_[l] ↥(GK K) V) (Q : GL n P.R.BdR), (∀ g : ↥(GK K), (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR) * (Q : Matrix n n P.R.BdR).map (P.actQdR (g : GQ l)) = Q) → IsDR (P.PD K) ρ := by
  intro l _ P n _ _ K V _ _ b ρ Q hQ
  haveI : FiniteDimensional ℚ_[l] ↥K.1 := (P.PD K).finK
  haveI : Nontrivial P.R.BdR := by
    refine ⟨⟨(P.PD K).ι (P.PD K).t, 0, fun h => (P.PD K).not_mem_filtration_two ?_⟩⟩
    rw [h]
    exact Submodule.zero_mem _
  obtain ⟨e, -, -, he⟩ := GlobalTheory.T.tensorProduct_basis_coordinates ℚ_[l] P.R.BdR V n b
  have hact : ∀ (g : ↥(GK K)) (x : P.R.BdR), (P.PD K).actdR g x = P.actQdR (g : GQ l) x :=
    fun g x => P.PD_actdR K g x
  have key := GlobalTheory.T.finrank_invariants_eq_of_invertible_periodMatrix ℚ_[l] ↥K.1 P.R.BdR ↥(GK K)
    (fun g => ((P.PD K).actdR g).toRingEquiv.toRingHom) n
    (fun g => (LinearMap.toMatrix b b (ρ g)).map (algebraMap ℚ_[l] P.R.BdR))
    (fun x => ⟨fun h => (P.PD K).invdR x h, by
      rintro ⟨c, rfl⟩ g
      exact ((P.PD K).actdR g).commutes c⟩) Q
    (fun g => by
      have h := hQ g
      have : (⇑((P.PD K).actdR g).toRingEquiv.toRingHom : P.R.BdR → P.R.BdR) = P.actQdR (g : GQ l) :=
        funext (hact g)
      rw [this]
      exact h)
    ((DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)))
    (fun x => by
      obtain ⟨y, rfl⟩ := e.surjective x
      have h1 : e y ∈ (DdR (P.PD K) ρ).map (e : V ⊗[ℚ_[l]] P.R.BdR →ₗ[ℚ_[l]] (n → P.R.BdR)) ↔
          y ∈ DdR (P.PD K) ρ := by
        constructor
        · rintro ⟨z, hz, hzy⟩
          have : z = y := e.injective hzy
          exact this ▸ hz
        · exact fun h => ⟨y, h, rfl⟩
      rw [h1]
      simp only [DdR, Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.sub_apply,
        LinearMap.id_apply, sub_eq_zero]
      refine forall_congr' fun g => ?_
      have h2 := he (ρ g) ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y
      have h3 : actVdR (P.PD K) ρ g y = TensorProduct.map (ρ g)
          ((((P.PD K).actdR g).toAlgHom.toLinearMap).restrictScalars ℚ_[l]) y := rfl
      rw [h3, ← e.injective.eq_iff, h2]
      rfl)
  rw [LinearEquiv.finrank_map_eq, ← finrank_eq_card_basis b] at key
  exact key

end GlobalTheory.PMon
