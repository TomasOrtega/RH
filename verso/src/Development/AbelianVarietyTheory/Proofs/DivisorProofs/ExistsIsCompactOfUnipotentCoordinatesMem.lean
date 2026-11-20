import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsLv
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ModerateGrowthOfHasCompactSupport
import Development.AbelianVarietyTheory.Definitions.Divisors.LocallyCompactUnipFlag
open scoped TensorProduct NNReal ENNReal Matrix
open NumberField MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.EisLine GlobalTheory.SphEis
open GlobalTheory.ResLine (IsHt SemiLat)
open GlobalTheory.Doubling (absE npow)
open Formalism.UG (cT bc)

namespace GlobalTheory.SphEis

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ`. Establish `: IsModuleTopology (AF F) (AF F ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (AF F ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (AF F) _`. Establish `: T2Space (AF F)` using `GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F`. Take `⟨e⟩` from `GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)`.

Establish `: T2Space (AF F ⊗[F] E)` using `e.isEmbedding.t2Space`. Set `Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E)` to `fun p => adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)`. Establish `key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c)`. Introduce `u b c h`. Establish `hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) + adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1`.

Use `congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum` as an intermediate fact. Simplify `this` using `only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z), ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]`. Establish `hsig` using `GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ`.

Establish `hΦ : Continuous Φ`. Establish `h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1` using `continuous_fst`. Establish `h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2` using `continuous_snd`. Establish `hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1` using `continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose`. Conclude with `((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))`.

Establish `hadj : Continuous (adjA σ J)`. Establish `: Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X` using `(continuous_id.matrix_map hsig).matrix_transpose`. Conclude with `(continuous_const.matrix_mul this).matrix_mul continuous_const`. Set `S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E))` to `(Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)`. Establish `hS : IsCompact S` using `(isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)`.

Set `ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ` to `fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))`. Establish `hψ : Continuous ψ` using `hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))`. Establish `hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)` using `(Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)`. Use `⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩` and prove the remaining obligations. Introduce `u b c h hb hc`.

Use `⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩` and prove the remaining obligations. Establish `e1` using `key u b c h`. Establish `e2` using `adjA_mat hFr.herm u`. Simplify using `only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]`.
-/
theorem exists_isCompact_of_crd_mem : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (n : ℕ) (J : Matrix (Fin n) (Fin n) E) (j m : ℕ) (C D : Matrix (Fin n) (Fin j) E) (Z : Matrix (Fin n) (Fin m) E) (J₀ : Matrix (Fin m) (Fin m) E), Fr σ J C D Z J₀ → ∀ Ω : Set (AF F ⊗[F] E), IsCompact Ω → ∃ V : Set (GAd σ J), IsCompact V ∧ ∀ (u : GAd σ J) (b : Matrix (Fin j) (Fin m) (AF F ⊗[F] E)) (c : Matrix (Fin j) (Fin j) (AF F ⊗[F] E)), Crd σ J C D Z J₀ u b c → (∀ i k, b i k ∈ Ω) → (∀ i k, c i k ∈ Ω) → u ∈ V := by
  intro F E _ _ _ _ _ σ n J j m C D Z J₀ hFr Ω hΩ
  have : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (AF F ⊗[F] E) := IsModuleTopology.isTopologicalRing (AF F) _
  have : T2Space (AF F) := GlobalTheory.AdelicUnitaryTop.t2Space_adeleRing_numberField F
  obtain ⟨e⟩ := GlobalTheory.AdelicUnitaryTop.nonempty_homeomorph (F := F) (E := E) (AF F)
  have : T2Space (AF F ⊗[F] E) := e.isEmbedding.t2Space
  let Φ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) := fun p =>
    adMat F C * adMat F (cT (σ : E →+* E) D * J) + (adMat F Z + adMat F C * p.1) * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
      (adMat F D - adMat F Z * plus σ J₀ p.1 + adMat F C * p.2) * adMat F (cT (σ : E →+* E) C * J)
  have key : ∀ u b c, Crd σ J C D Z J₀ u b c → (matHom _ σ J u).1 = Φ (b, c) := by
    intro u b c h
    have hs : adMat F C * adMat F (cT (σ : E →+* E) D * J) + adMat F Z * adMat F (J₀⁻¹ * (cT (σ : E →+* E) Z * J)) +
        adMat F D * adMat F (cT (σ : E →+* E) C * J) = 1 := by
      have := congrArg (Matrix.map · (inclR (F := F) (E := E) (AF F))) hFr.sum
      simpa only [Matrix.map_add _ (map_add _), Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)] using this
    calc (matHom _ σ J u).1 = (matHom _ σ J u).1 * 1 := (Matrix.mul_one _).symm
      _ = Φ (b, c) := by
        rw [← hs, Matrix.mul_add, Matrix.mul_add, ← Matrix.mul_assoc _ (adMat F C), ← Matrix.mul_assoc _ (adMat F Z),
          ← Matrix.mul_assoc _ (adMat F D), h.onC, h.onZ, h.onD]
  have hsig := GlobalTheory.AdelicUnitaryTop.continuous_sigR (AF F) σ
  have hΦ : Continuous Φ := by
    have h1 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.1 := continuous_fst
    have h2 : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => p.2 := continuous_snd
    have hp : Continuous fun p : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) => plus σ J₀ p.1 :=
      continuous_const.matrix_mul (h1.matrix_map hsig).matrix_transpose
    exact ((continuous_const.add ((continuous_const.add (continuous_const.matrix_mul h1)).matrix_mul continuous_const)).add
      (((continuous_const.sub (continuous_const.matrix_mul hp)).add (continuous_const.matrix_mul h2)).matrix_mul continuous_const))
  have hadj : Continuous (adjA σ J) := by
    have : Continuous fun X : Matrix (Fin n) (Fin n) (AF F ⊗[F] E) => cT (sigR (AF F) σ) X :=
      (continuous_id.matrix_map hsig).matrix_transpose
    exact (continuous_const.matrix_mul this).matrix_mul continuous_const
  let S : Set (Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E)) :=
    (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω) ×ˢ (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => Ω)
  have hS : IsCompact S := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ).prod
    (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hΩ)
  let ψ : Matrix (Fin j) (Fin m) (AF F ⊗[F] E) × Matrix (Fin j) (Fin j) (AF F ⊗[F] E) → Matrix (Fin n) (Fin n) (AF F ⊗[F] E) × (Matrix (Fin n) (Fin n) (AF F ⊗[F] E))ᵐᵒᵖ :=
    fun p => (Φ p, MulOpposite.op (adjA σ J (Φ p)))
  have hψ : Continuous ψ := hΦ.prodMk (MulOpposite.continuous_op.comp (hadj.comp hΦ))
  have hce : IsClosedEmbedding fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g) :=
    (Units.isClosedEmbedding_embedProduct (α := Matrix (Fin n) (Fin n) (AF F ⊗[F] E))).comp (isClosedEmbedding_matHom_GAd σ J)
  refine ⟨(fun g : GAd σ J => Units.embedProduct _ (matHom _ σ J g)) ⁻¹' (ψ '' S), hce.isCompact_preimage (hS.image hψ), ?_⟩
  intro u b c h hb hc
  refine ⟨(b, c), ⟨fun i _ k _ => hb i k, fun i _ k _ => hc i k⟩, ?_⟩
  have e1 := key u b c h
  have e2 := adjA_mat hFr.herm u
  simp only [ψ, Units.embedProduct_apply, ← e1, e2, ← map_inv]

end GlobalTheory.SphEis
