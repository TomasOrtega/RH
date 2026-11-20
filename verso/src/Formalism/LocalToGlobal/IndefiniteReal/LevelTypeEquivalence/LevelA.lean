import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.MeasBrg
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedVolumeStatements.LevelSubgroupProperties

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open scoped TensorProduct Matrix

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def kf (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) : Set (UI.instV fr).Gf :=
  {y | (y.1 : GL (Fin V.rank) (Lev.EAf D)) ∈ K}

/- English proof (translation)
Use `show UI.brg fr x ∈ GfC V ⊓ K.comap (Lev.finE V) ↔ _`. Rewrite using `[Subgroup.mem_inf, Subgroup.mem_comap, brg_mem_GfC, finE_brg]`. Both sides reduce to the same expression.
-/
theorem brg_mem_levA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (x : (UI.instV fr).GA) :
    UI.brg fr x ∈ Lev.levA V K ↔ x.1 = 1 ∧ x.2 ∈ kf fr K := by
  show UI.brg fr x ∈ GfC V ⊓ K.comap (Lev.finE V) ↔ _
  rw [Subgroup.mem_inf, Subgroup.mem_comap, brg_mem_GfC, finE_brg]
  rfl

/- English proof (translation)
Establish `hpre : kf fr K = jf fr ⁻¹' (Lev.levA V K : Set (GA D V))`. Use extensionality with `y`. Use `show y ∈ kf fr K ↔ UI.brg fr (1, y) ∈ Lev.levA V K`. Rewrite using `[brg_mem_levA]`. Conclude with `⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hpre]`. Conclude with `(jf_isClosedEmbedding fr).isCompact_preimage hK.1`. Establish `hmem : ∀ y, jf fr y ∈ GfC V` using `fun y => (brg_mem_GfC fr (1, y)).mpr rfl`. Set `jc : (UI.instV fr).Gf → GfC V` to `fun y => ⟨jf fr y, hmem y⟩`.

Establish `hjc : Continuous jc` using `(jf_isClosedEmbedding fr).continuous.subtype_mk _`. Establish `e : kf fr K = jc ⁻¹' (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V))`. Rewrite using `[hpre]`. Use extensionality with `y`. Simplify using `only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, jc]`.

Rewrite using `[e]`. Conclude with `hK.2.preimage hjc`.
-/
theorem kf_isCompact_isOpen_of_levelA (K : Subgroup (GL (Fin V.rank) (Lev.EAf D))) (hK : IsLevelA V K) :
    IsCompact (kf fr K) ∧ IsOpen (kf fr K) := by
  have hpre : kf fr K = jf fr ⁻¹' (Lev.levA V K : Set (GA D V)) := by
    ext y
    show y ∈ kf fr K ↔ UI.brg fr (1, y) ∈ Lev.levA V K
    rw [brg_mem_levA]
    exact ⟨fun h => ⟨rfl, h⟩, fun h => h.2⟩
  refine ⟨?_, ?_⟩
  · rw [hpre]
    exact (jf_isClosedEmbedding fr).isCompact_preimage hK.1
  · have hmem : ∀ y, jf fr y ∈ GfC V := fun y => (brg_mem_GfC fr (1, y)).mpr rfl
    let jc : (UI.instV fr).Gf → GfC V := fun y => ⟨jf fr y, hmem y⟩
    have hjc : Continuous jc := (jf_isClosedEmbedding fr).continuous.subtype_mk _
    have e : kf fr K = jc ⁻¹' (((Lev.levA V K).subgroupOf (GfC V)) : Set (GfC V)) := by
      rw [hpre]
      ext y
      simp only [Set.mem_preimage, SetLike.mem_coe, Subgroup.mem_subgroupOf, jc]
    rw [e]
    exact hK.2.preimage hjc

def KstI : Subgroup (GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) :=
  Formalism.UG.stabGL (UI.instV fr).Lf

variable (V) in

def Kst : Subgroup (GL (Fin V.rank) (Lev.EAf D)) := KstI (UI.framesV D V)

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce `hx`. Use `⟨hx, fun y hy => ⟨_, Submodule.sub_mem _ ((hx y).mp hy) hy, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]`.

Introduce `hx`. Conclude with `hx.1`.
-/
theorem stabilizer_eq_level_subgroup : (UI.instV fr).Kset = {x : (UI.instV fr).Gf |
    (x : GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) ∈
      Formalism.UG.stabGL (lamAf (F := (UI.instV fr).F) (UI.instV fr).L) ∧
    ∀ y ∈ lamAf (F := (UI.instV fr).F) (UI.instV fr).L, ∃ z ∈ lamAf (F := (UI.instV fr).F) (UI.instV fr).L,
      ((x : GL (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) - 1 :
        Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ((UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F)) *ᵥ y =
        ((1 : ℕ) : (UI.instV fr).E ⊗[(UI.instV fr).F] Formalism.MainNotions.S.Af (UI.instV fr).F) • z} := by
  ext x
  constructor
  · intro hx
    refine ⟨hx, fun y hy => ⟨_, Submodule.sub_mem _ ((hx y).mp hy) hy, ?_⟩⟩
    rw [Nat.cast_one, one_smul, Matrix.sub_mulVec, Matrix.one_mulVec]
  · intro hx
    exact hx.1

end Formalism.IndefR.Eqv

end
