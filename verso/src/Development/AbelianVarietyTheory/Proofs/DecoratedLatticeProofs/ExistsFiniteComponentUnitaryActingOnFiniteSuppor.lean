import Mathlib
import Development.AbelianVarietyTheory.Definitions.LatticeFrames.IsSumFrame
import Formalism.LocalToGlobal.IndefiniteReal.SubgroupCharExtensionOneApply
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.AdelicPointComponentsAtPlacesLatticesVacuaStatement
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.FinPl GlobalTheory.MixPer GlobalTheory.MixModel
open IsDedekindDomain NumberField Matrix
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option synthInstance.maxHeartbeats 400000

/- English proof (translation)
Establish `h1` using `congrArg (fun A : GL (Fin S.rank) (AE D ⧸ I) => A.1 i j) (MonoidHom.mem_ker.mp hh)`. Rewrite using `[← Ideal.Quotient.eq]`. Establish `h2 : Ideal.Quotient.mk I ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ I)) i j`. Apply the tactic sequence `rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *]`. Rewrite using `[h2]`.

Simplify `h1` using `[Formalism.L2.Theta.mt, Matrix.GeneralLinearGroup.map]`.
-/
theorem GlobalTheory.GlobFin.cong_entry {D : D7} {S : HSp D} {I : Ideal (AE D)} {h : GA D S} (hh : h ∈ congGrp S I) (i j : Fin S.rank) :
    mt S h i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ I := by
  have h1 := congrArg (fun A : GL (Fin S.rank) (AE D ⧸ I) => A.1 i j) (MonoidHom.mem_ker.mp hh)
  rw [← Ideal.Quotient.eq]
  have h2 : Ideal.Quotient.mk I ((1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) = (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D ⧸ I)) i j := by
    rcases eq_or_ne i j with rfl | hij <;> simp [Matrix.one_apply, *]
  rw [h2]
  simpa [Formalism.L2.Theta.mt, Matrix.GeneralLinearGroup.map] using h1

/- English proof (translation)
Use `show infHom S x = 1`. Use extensionality with `i j`. Apply the tactic sequence `have h := GlobalTheory.GlobFin.cong_entry hx i j`. Establish `hk : mt S x i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ RingHom.ker (infPart D)` using `(inf_le_left : idAt D (fun _ => True) ≤ _) h`. Rewrite `hk` using `[RingHom.mem_ker, map_sub, sub_eq_zero]`.

Establish `: ((infHom S x : GL _ _) : Matrix _ _ _) i j = infPart D (mt S x i j)` using `rfl`. Rewrite using `[this, hk]`. Simplify using `[Matrix.one_apply, apply_ite]`.
-/
theorem GlobalTheory.GlobFin.mem_GfC {D : D7} {S : HSp D} {x : GA D S} (hx : x ∈ congGrp S (idAt D (fun _ => True))) : x ∈ GfC S := by
  show infHom S x = 1
  ext i j
  have h := GlobalTheory.GlobFin.cong_entry hx i j
  have hk : mt S x i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j ∈ RingHom.ker (infPart D) :=
    (inf_le_left : idAt D (fun _ => True) ≤ _) h
  rw [RingHom.mem_ker, map_sub, sub_eq_zero] at hk
  have : ((infHom S x : GL _ _) : Matrix _ _ _) i j = infPart D (mt S x i j) := rfl
  rw [this, hk]
  simp [Matrix.one_apply, apply_ite]

/- English proof (translation)
Introduce `D S g`. Take `⟨⟨ε, -, -, -, hAt, hOff⟩, hS⟩` from `GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)`. Take `⟨x, hx, u, hu, rfl⟩` from `(hS S).1 g`. Use `⟨x, GlobalTheory.GlobFin.mem_GfC hx, fun P y hy => ?_⟩` and prove the remaining obligations. Establish `hy0 : ∀ j, y j ∈ idAt D (fun _ => True)`.

Introduce `j`. Use `Ideal.mem_inf.mpr ⟨(Ideal.mem_inf.mp (hy j)).1, ?_⟩` and prove the remaining obligations. Simplify using `only [Submodule.mem_iInf]`. Introduce `w`. Conclude with `absurd trivial w.2`.

Establish `hu1 : Formalism.L2.Theta.mt S u *ᵥ y = y`. Use function extensionality and compare the values at `i`. Establish `hz : ∀ j, (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j = 0`. Introduce `j`. Apply the tactic sequence `have ha := (hOff _).mp (GlobalTheory.GlobFin.cong_entry hu i j)`.

Establish `hb` using `(hAt _).mp (hy0 j)`. Combine the equalities or inequalities in the displayed calculation. Establish `hsum : ((Formalism.L2.Theta.mt S u - 1) *ᵥ y) i = 0`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.sub_apply]`. Conclude with `Finset.sum_eq_zero fun j _ => hz j`.

Rewrite `hsum` using `[Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero]`. Conclude with `hsum`. Rewrite using `[mt_mul, ← Matrix.mulVec_mulVec, hu1]`.
-/
theorem GlobalTheory.GlobFin.fin_rep : ∀ (D : D7) (S : HSp D) (g : GA D S), ∃ x ∈ GfC S, ∀ (P : Pl D → Prop) (y : Fin S.rank → AE D), (∀ i, y i ∈ idAt D P) → mt S g *ᵥ y = mt S x *ᵥ y := by
  intro D S g
  obtain ⟨⟨ε, -, -, -, hAt, hOff⟩, hS⟩ := GlobalTheory.T.adelicPoint_components_atPlaces_lattices_vacua D (fun _ => True)
  obtain ⟨x, hx, u, hu, rfl⟩ := (hS S).1 g
  refine ⟨x, GlobalTheory.GlobFin.mem_GfC hx, fun P y hy => ?_⟩
  have hy0 : ∀ j, y j ∈ idAt D (fun _ => True) := by
    intro j
    refine Ideal.mem_inf.mpr ⟨(Ideal.mem_inf.mp (hy j)).1, ?_⟩
    simp only [Submodule.mem_iInf]
    intro w
    exact absurd trivial w.2
  have hu1 : Formalism.L2.Theta.mt S u *ᵥ y = y := by
    funext i
    have hz : ∀ j, (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j = 0 := by
      intro j
      have ha := (hOff _).mp (GlobalTheory.GlobFin.cong_entry hu i j)
      have hb := (hAt _).mp (hy0 j)
      calc (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * y j
          = (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j) * (ε * y j) := by rw [hb]
        _ = (ε * (Formalism.L2.Theta.mt S u i j - (1 : Matrix (Fin S.rank) (Fin S.rank) (AE D)) i j)) * y j := by ring
        _ = 0 := by rw [ha, zero_mul]
    have hsum : ((Formalism.L2.Theta.mt S u - 1) *ᵥ y) i = 0 := by
      simp only [Matrix.mulVec, dotProduct, Matrix.sub_apply]
      exact Finset.sum_eq_zero fun j _ => hz j
    rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, sub_eq_zero] at hsum
    exact hsum
  rw [mt_mul, ← Matrix.mulVec_mulVec, hu1]
