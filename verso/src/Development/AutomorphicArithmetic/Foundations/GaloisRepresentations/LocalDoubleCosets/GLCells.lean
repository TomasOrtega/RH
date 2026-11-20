import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalDoubleCosets.TracePow
import GroundTheory.AutomorphicForms.GeometricLemmaFiltration
import GroundTheory.AutomorphicForms.WhittakerCells

noncomputable section

open UpperTheory.ConvolutionTheory.Loc Matrix
open GroundTheory.Automorphic (permGL permGL_apply)
open DoubleCoset (doubleCoset mem_doubleCoset)

namespace UpperTheory.Gal.LocD

section SlopeTestRemainingChoices

variable {E : Type} [Field E] {n : ℕ}

/- English proof (translation)
Rewrite using `[GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_borel]`. Conclude with `⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩`.
-/
private theorem mem_blockUpper_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_blockUpper, GlobalTheory.SmGL.mem_borel]
  exact ⟨fun h i j hij => h hij, fun h i j hij => h i j hij⟩

/- English proof (translation)
Rewrite using `[GroundTheory.Automorphic.mem_borel_iff, GlobalTheory.SmGL.mem_borel E]`.
-/
private theorem mem_autBorel_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.borel n E ↔ g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GroundTheory.Automorphic.mem_borel_iff, GlobalTheory.SmGL.mem_borel E]

/- English proof (translation)
Rewrite using `[GroundTheory.Automorphic.Iwasawa.mem_unipotent, GlobalTheory.SmGL.mem_unipB E]`. Conclude with `Iff.rfl`.
-/
private theorem mem_unipotent_iff {g : GL (Fin n) E} :
    g ∈ GroundTheory.Automorphic.Iwasawa.unipotent E n ↔ g ∈ GlobalTheory.SmGL.unipB E (Fin n) := by
  rw [GroundTheory.Automorphic.Iwasawa.mem_unipotent, GlobalTheory.SmGL.mem_unipB E]
  exact Iff.rfl

/- English proof (translation)
Rewrite `hg` using `[GlobalTheory.SmGL.mem_unipB]`. Rewrite using `[GlobalTheory.SmGL.mem_borel]`. Conclude with `hg.1`.
-/
private theorem unipB_le_borel {g : GL (Fin n) E} (hg : g ∈ GlobalTheory.SmGL.unipB E (Fin n)) :
    g ∈ GlobalTheory.SmGL.borel E (Fin n) := by
  rw [GlobalTheory.SmGL.mem_unipB] at hg
  rw [GlobalTheory.SmGL.mem_borel]
  exact hg.1

/- English proof (translation)
Establish `hset : ((GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) : Set (GL (Fin n) E)) = ((GroundTheory.Automorphic.borel n E) : Set (GL (Fin n) E))`. Use extensionality with `g`. Simplify using `only [SetLike.mem_coe]`. Rewrite using `[mem_blockUpper_iff, mem_autBorel_iff]`. Use extensionality with `g`.

Prove the components needed by the constructor for the conclusion. Introduce `hg`. Rewrite `hg` using `[hset, GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm]`. Take `⟨u, hu, t, v, hv, rfl⟩` from `hg`. Use `⟨u * GroundTheory.Automorphic.Iwasawa.diagGL E n t, ?_, v, ?_, rfl⟩` and prove the remaining obligations.

Use `Subgroup.mul_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `unipB_le_borel (mem_unipotent_iff.mp hu)`. Conclude with `mem_autBorel_iff.mp (GroundTheory.Automorphic.Whittaker.diagGL_mem_borel t)`. Conclude with `mem_unipotent_iff.mp hv`. Introduce and unpack `⟨b, hb, u, hu, rfl⟩`.

Rewrite using `[mem_doubleCoset]`. Conclude with `⟨b, mem_blockUpper_iff.mpr hb, u, mem_blockUpper_iff.mpr (unipB_le_borel hu), rfl⟩`.
-/
private theorem doubleCoset_eq_cell (w : Equiv.Perm (Fin n)) :
    doubleCoset (permGL E w) (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ) : Set (GL (Fin n) E))
        (GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) =
      cell (GlobalTheory.SmGL.borel E (Fin n)) (GlobalTheory.SmGL.unipB E (Fin n)) (permGL E w) := by
  have hset : ((GroundTheory.Automorphic.Iwasawa.blockUpper E n (Fin.val : Fin n → ℕ)) : Set (GL (Fin n) E)) =
      ((GroundTheory.Automorphic.borel n E) : Set (GL (Fin n) E)) := by
    ext g
    simp only [SetLike.mem_coe]
    rw [mem_blockUpper_iff, mem_autBorel_iff]
  ext g
  constructor
  · intro hg
    rw [hset, GroundTheory.Automorphic.Whittaker.mem_doubleCoset_iff_normalForm] at hg
    obtain ⟨u, hu, t, v, hv, rfl⟩ := hg
    refine ⟨u * GroundTheory.Automorphic.Iwasawa.diagGL E n t, ?_, v, ?_, rfl⟩
    · refine Subgroup.mul_mem _ ?_ ?_
      · exact unipB_le_borel (mem_unipotent_iff.mp hu)
      · exact mem_autBorel_iff.mp (GroundTheory.Automorphic.Whittaker.diagGL_mem_borel t)
    · exact mem_unipotent_iff.mp hv
  · rintro ⟨b, hb, u, hu, rfl⟩
    rw [mem_doubleCoset]
    exact ⟨b, mem_blockUpper_iff.mpr hb, u, mem_blockUpper_iff.mpr (unipB_le_borel hu), rfl⟩

/- English proof (translation)
Use extensionality with `i j`. Rewrite using `[sg_val, permGL_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private theorem sg_permGL (σ : E ≃+* E) (w : Equiv.Perm (Fin n)) : sg σ (permGL E w) = permGL E w := by
  ext i j
  rw [sg_val, permGL_apply]
  split_ifs <;> simp

end SlopeTestRemainingChoices

/- English proof (translation)
Introduce `E _ _ _ _ n σ`. Use `haveI : T2Space E := GroundTheory.Automorphic.GLnLocal.t2Space E`. Take `⟨k, w, hcov, hanti⟩` from `GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := E) (Fin.val : Fin n → ℕ) Fin.val`. Establish `hcl` using `GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone hcov hanti`. Use `⟨k, fun j => permGL E (w j), fun j => sg_permGL σ _, fun g => ?_, fun j => ?_⟩` and prove the remaining obligations.

Simplify `hcov g` using `only [doubleCoset_eq_cell]`. Simplify `hcl j` using `only [doubleCoset_eq_cell]`.
-/
theorem gLCells : GLCells := by
  intro E _ _ _ _ n σ
  haveI : T2Space E := GroundTheory.Automorphic.GLnLocal.t2Space E
  obtain ⟨k, w, hcov, hanti⟩ :=
    GroundTheory.Automorphic.Parabolic.exists_cellEnumeration (F := E) (Fin.val : Fin n → ℕ) Fin.val
  have hcl := GroundTheory.Automorphic.Parabolic.closure_doubleCoset_subset_of_antitone hcov hanti
  refine ⟨k, fun j => permGL E (w j), fun j => sg_permGL σ _, fun g => ?_, fun j => ?_⟩
  · simpa only [doubleCoset_eq_cell] using hcov g
  · simpa only [doubleCoset_eq_cell] using hcl j

end UpperTheory.Gal.LocD

end
