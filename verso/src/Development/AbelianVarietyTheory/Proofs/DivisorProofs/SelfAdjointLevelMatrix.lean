import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsHaarProd
import Development.AbelianVarietyTheory.Counterexamples.AdelicSplittingExamples.TwoPrimesOfSplitPl
open Formalism.BasicNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix Filter Topology
open scoped TensorProduct ENNReal
open GlobalTheory.TamSU GlobalTheory.SUVol GlobalTheory.UCls GlobalTheory.AdLat GlobalTheory.Published GlobalTheory.TamUnf

noncomputable section
namespace GlobalTheory.TamUnf

/- English proof (translation)
Introduce `E _ _ _ r G`. Use `set F := maximalRealSubfield E`. Use `set c := IsCMField.complexConj E`. Establish `key : ∀ m : Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E), Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom) m * JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) G …`. Introduce `m`.

Rewrite using `[GlobalTheory.UnRepCheck.isUnA_iff]`. Establish `hJ : JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) Gᵀ = (GlobalTheory.UnRep.fm F G)ᵀ` using `rfl`. Establish `hs : Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom) m = (m.map (sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ` using `rfl`. Rewrite using `[hJ, hs]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Use `congrArg Matrix.transpose h` as an intermediate fact. Simplify `this` using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Introduce `h`. Use `congrArg Matrix.transpose h` as an intermediate fact.

Simplify `this` using `[Matrix.transpose_mul, Matrix.mul_assoc]`. Use `⟨fun k => ?_, fun g hg => ?_⟩` and prove the remaining obligations. Establish `hmem : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ k.1) ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ` using `k.1.2`. Establish `hdet` using `mem_finSU.1 k.2`. Use `⟨⟨?_, (key _).1 hmem⟩, hdet⟩` and prove the remaining obligations.

Conclude with `(HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ k.1).isUnit.map Matrix.detMonoidHom`. Take `⟨⟨hu, hinv⟩, hdet⟩` from `hg`. Set `u : GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E)` to `((Matrix.isUnit_iff_isUnit_det g).2 hu).unit`. Establish `hum : (u : Matrix (Fin r) (Fin r) _) = g` using `rfl`. Establish `hmem : u ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ`.

Establish `h2` using `(key g).2 hinv`. Rewrite `h2` using `[← hum]`. Conclude with `h2`. Set `h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ` to `(⟨u, hmem⟩ : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ)`. Establish `hh : ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ h : GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = g` using `rfl`.

Use `⟨⟨h, mem_finSU.2 (by rw [hh]; exact hdet)⟩, hh⟩` and prove the remaining obligations.
-/
theorem finSU_mat_iff_isSA : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (r : ℕ) (G : Matrix (Fin r) (Fin r) E),
    (∀ k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ,
      IsSA G ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
        GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
        Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E))) ∧
    ∀ g : Matrix (Fin r) (Fin r) (RA (maximalRealSubfield E) E), IsSA G g →
      ∃ k : finSU (IsCMField.complexConj E).toAlgHom Gᵀ,
        ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E)) (IsCMField.complexConj E).toAlgHom Gᵀ k.1 :
          GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) :
          Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af (maximalRealSubfield E) ⊗[maximalRealSubfield E] E)) = g := by
  intro E _ _ _ r G
  set F := maximalRealSubfield E
  set c := IsCMField.complexConj E
  have key : ∀ m : Matrix (Fin r) (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E),
      Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom) m * JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) Gᵀ * m =
        JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) Gᵀ ↔ GlobalTheory.UnRep.IsUnA c G m := by
    intro m
    rw [GlobalTheory.UnRepCheck.isUnA_iff]
    have hJ : JR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) Gᵀ = (GlobalTheory.UnRep.fm F G)ᵀ := rfl
    have hs : Formalism.UG.cT (sigR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom) m =
        (m.map (sg (FiniteAdeleRing (𝓞 F) F) c))ᵀ := rfl
    rw [hJ, hs]
    constructor
    · intro h
      have := congrArg Matrix.transpose h
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
    · intro h
      have := congrArg Matrix.transpose h
      simpa [Matrix.transpose_mul, Matrix.mul_assoc] using this
  refine ⟨fun k => ?_, fun g hg => ?_⟩
  · have hmem : (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ k.1) ∈
        HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ := k.1.2
    have hdet := mem_finSU.1 k.2
    refine ⟨⟨?_, (key _).1 hmem⟩, hdet⟩
    exact (HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ k.1).isUnit.map Matrix.detMonoidHom
  · obtain ⟨⟨hu, hinv⟩, hdet⟩ := hg
    let u : GL (Fin r) (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F ⊗[F] E) := ((Matrix.isUnit_iff_isUnit_det g).2 hu).unit
    have hum : (u : Matrix (Fin r) (Fin r) _) = g := rfl
    have hmem : u ∈ HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ := by
      have h2 := (key g).2 hinv
      rw [← hum] at h2
      exact h2
    let h : HA (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ := (⟨u, hmem⟩ : HR (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ)
    have hh : ((HA.mat (Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes.Af F) c.toAlgHom Gᵀ h : GL (Fin r) _) : Matrix (Fin r) (Fin r) _) = g := rfl
    refine ⟨⟨h, mem_finSU.2 (by rw [hh]; exact hdet)⟩, hh⟩

end GlobalTheory.TamUnf
