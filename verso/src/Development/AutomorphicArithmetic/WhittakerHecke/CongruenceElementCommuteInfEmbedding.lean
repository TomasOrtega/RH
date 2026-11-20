import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.XgDefs

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.Xg
open scoped Classical
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)
open UpperTheory.V.Af.Smo (EigAt)
open scoped ComplexOrder

/- English proof (translation)
Introduce `E _ _ _ M κ h X`. Establish `h0 : ∀ c : A E, c.1 = 0 → pInf E c = 0` using `fun c hc => by`. Express the relevant statement in the definitionally equal form `(infEq E).symm c.1 = 0`. Rewrite using `[hc]`. Conclude with `map_zero _`.

Establish `hk : GeneralLinearGroup.map (pInf E) κ = 1`. Use `Units.ext (Matrix.ext fun i j => ?_)` and prove the remaining obligations. Take `⟨⟨c, hc, e⟩, _⟩` from `h i j`. Establish `h1` using `congrArg (pInf E) e`. Rewrite `h1` using `[map_sub, map_mul, h0 c hc.1, mul_zero]`.

Establish `h2 : pInf E (κ.val i j) = pInf E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j)` using `sub_eq_zero.1 h1`. Express the relevant statement in the definitionally equal form `pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j`. Rewrite using `[h2]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using the standard rewrite rules. Simplify using `[Matrix.one_apply_ne hij]`. Establish `e` using `infGL_mul_finGL κ`. Rewrite `e` using `[hk, map_one, one_mul]`. Rewrite using `[← e]`.

Conclude with `(infGL_comm X _).symm`.
-/
theorem UpperTheory.congruence_element_commute_inf_embedding :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (M : ℕ) (κ : GL (Fin 2) (A E)), CongE M κ → ∀ X : GL (Fin 2) (Cinf E), κ * infGL E 2 X = infGL E 2 X * κ := by
  intro E _ _ _ M κ h X
  have h0 : ∀ c : A E, c.1 = 0 → pInf E c = 0 := fun c hc => by
    change (infEq E).symm c.1 = 0
    rw [hc]
    exact map_zero _
  have hk : GeneralLinearGroup.map (pInf E) κ = 1 := by
    refine Units.ext (Matrix.ext fun i j => ?_)
    obtain ⟨⟨c, hc, e⟩, _⟩ := h i j
    have h1 := congrArg (pInf E) e
    rw [map_sub, map_mul, h0 c hc.1, mul_zero] at h1
    have h2 : pInf E (κ.val i j) = pInf E ((1 : Matrix (Fin 2) (Fin 2) (A E)) i j) := sub_eq_zero.1 h1
    change pInf E (κ.val i j) = (1 : Matrix (Fin 2) (Fin 2) (Cinf E)) i j
    rw [h2]
    by_cases hij : i = j
    · subst hij
      simp
    · simp [Matrix.one_apply_ne hij]
  have e := infGL_mul_finGL κ
  rw [hk, map_one, one_mul] at e
  rw [← e]
  exact (infGL_comm X _).symm
