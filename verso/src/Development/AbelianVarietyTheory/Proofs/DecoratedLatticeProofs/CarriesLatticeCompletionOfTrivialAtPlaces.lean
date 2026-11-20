import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemHomLatticeCompletionIffSupportedMapsStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Introduce `D S L P g hg y hy`. Take `⟨⟨ε, -, -, -, hAt, hOff⟩, -⟩` from `GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P`. Establish `hmul : ∀ a ∈ idOff D P, ∀ b ∈ idAt D P, a * b = 0`. Introduce `a ha b hb`. Rewrite using `[← (hAt b).1 hb, ← mul_assoc, mul_comm a ε, (hOff a).1 ha, zero_mul]`.

Establish `hker` using `MonoidHom.mem_ker.1 hg`. Establish `hent : ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P`. Introduce `i j`. Rewrite using `[← Ideal.Quotient.eq]`. Establish `h2` using `congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idOff D P) => u.1 i j) hker`.

Simplify using `only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2`. Establish `h3 : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using `only [Matrix.one_apply_eq, map_one]`.

Simplify using `only [Matrix.one_apply_ne hij, map_zero]`. Rewrite using `[h3, ← h2]`. Both sides reduce to the same expression. Establish `hfix : mt S g *ᵥ y = y`. Use function extensionality and compare the values at `i`.

Establish `e : (mt S g *ᵥ y) i = y i + ∑ j, (mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j`. Simplify using `[Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]`. Rewrite using `[e, Finset.sum_eq_zero (fun j _ => hmul _ (hent i j) _ (hy j)), add_zero]`. Rewrite using `[hfix]`.
-/
theorem GlobalTheory.fixes_latV_of_mem_grpOff : ∀ (D : D7) (S : HSp D) (L : Lat S) (P : Pl D → Prop), ∀ g ∈ grpOff S P, Moves S g L L P := by
  intro D S L P g hg y hy
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, -⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D P
  have hmul : ∀ a ∈ idOff D P, ∀ b ∈ idAt D P, a * b = 0 := by
    intro a ha b hb
    rw [← (hAt b).1 hb, ← mul_assoc, mul_comm a ε, (hOff a).1 ha, zero_mul]
  have hker := MonoidHom.mem_ker.1 hg
  have hent : ∀ i j, mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ idOff D P := by
    intro i j
    rw [← Ideal.Quotient.eq]
    have h2 := congrArg (fun u : GL (Fin S.rank) (AE D ⧸ idOff D P) => u.1 i j) hker
    simp only [MonoidHom.comp_apply, Matrix.GeneralLinearGroup.map_apply, Units.val_one] at h2
    have h3 : Ideal.Quotient.mk (idOff D P) ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) =
        (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ idOff D P)) i j := by
      by_cases hij : i = j
      · subst hij; simp only [Matrix.one_apply_eq, map_one]
      · simp only [Matrix.one_apply_ne hij, map_zero]
    rw [h3, ← h2]
    rfl
  have hfix : mt S g *ᵥ y = y := by
    funext i
    have e : (mt S g *ᵥ y) i = y i + ∑ j, (mt S g i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j := by
      simp [Matrix.mulVec, dotProduct, sub_mul, Finset.sum_sub_distrib, Matrix.one_apply]
    rw [e, Finset.sum_eq_zero (fun j _ => hmul _ (hent i j) _ (hy j)), add_zero]
  rw [hfix]
