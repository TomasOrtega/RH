import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.UnimodInst
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.PeterssonNormOfUpLift
import Formalism.LocalToGlobal.IndefiniteReal.LevelTypeEquivalence.GinfCSecondCountable
import Formalism.LocalToGlobal.IndefiniteReal.HaarTransfer.UnimodP
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJUnimod
import Formalism.PeriodIntegrals.ExplicitFormulaCounts.AdUnimod

noncomputable section

open MeasureTheory NumberField Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.S Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

namespace Formalism.IndefR.Eqv

attribute [local instance] Formalism.BasicNotions.Host.cmStar

section Fin

variable {D : D7} {V : HSp D} (fr : UI.Frames D V)

def jf (x : (UI.instV fr).Gf) : GA D V := UI.brg fr (1, x)

/- English proof (translation)
Use `haveI : T2Space (Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ℂ)ˣ := Units.isEmbedding_embedProduct.t2Space`. Use `haveI : T2Space (UI.instV fr).Ginf := inferInstance`. Establish `hemb : Topology.IsEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x))` using `Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd (continuous_const.prodMk continuous_id)`. Establish `hcl : IsClosed (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x))`. Establish `hr : (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) = ({1} : Set (UI.instV fr).Ginf) ×ˢ Set.univ`.

Use extensionality with `⟨a, b⟩`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy⟩`. Simplify using `only [Prod.mk.injEq] at hy`. Conclude with `⟨hy.1.symm, Set.mem_univ _⟩`.

Introduce and unpack `⟨ha, -⟩`. Establish `ha' : a = 1` using `ha`. Conclude with `⟨b, by rw [ha']⟩`. Rewrite using `[hr]`. Conclude with `isClosed_singleton.prod isClosed_univ`.

Establish `h1 : Topology.IsClosedEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x))` using `⟨hemb, hcl⟩`. Conclude with `(UI.brg fr).toHomeomorph.isClosedEmbedding.comp h1`.
-/
theorem jf_isClosedEmbedding : Topology.IsClosedEmbedding (jf fr) := by
  haveI : T2Space (Matrix (Fin (UI.instV fr).n) (Fin (UI.instV fr).n) ℂ)ˣ :=
    Units.isEmbedding_embedProduct.t2Space
  haveI : T2Space (UI.instV fr).Ginf := inferInstance
  have hemb : Topology.IsEmbedding (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) :=
    Function.LeftInverse.isEmbedding (f := Prod.snd) (fun _ => rfl) continuous_snd
      (continuous_const.prodMk continuous_id)
  have hcl : IsClosed (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := by
    have hr : (Set.range fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) =
        ({1} : Set (UI.instV fr).Ginf) ×ˢ Set.univ := by
      ext ⟨a, b⟩
      constructor
      · rintro ⟨y, hy⟩
        simp only [Prod.mk.injEq] at hy
        exact ⟨hy.1.symm, Set.mem_univ _⟩
      · rintro ⟨ha, -⟩
        have ha' : a = 1 := ha
        exact ⟨b, by rw [ha']⟩
    rw [hr]
    exact isClosed_singleton.prod isClosed_univ
  have h1 : Topology.IsClosedEmbedding
      (fun x : (UI.instV fr).Gf => ((1 : (UI.instV fr).Ginf), x)) := ⟨hemb, hcl⟩
  exact (UI.brg fr).toHomeomorph.isClosedEmbedding.comp h1

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `ga_facts D V`. Establish `he` using `jf_isClosedEmbedding fr`. Conclude with `⟨he.isEmbedding.t2Space, he.locallyCompactSpace, he.isInducing.secondCountableTopology⟩`.
-/
theorem gf_facts : T2Space (UI.instV fr).Gf ∧ LocallyCompactSpace (UI.instV fr).Gf ∧
    SecondCountableTopology (UI.instV fr).Gf := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ga_facts D V
  have he := jf_isClosedEmbedding fr
  exact ⟨he.isEmbedding.t2Space, he.locallyCompactSpace, he.isInducing.secondCountableTopology⟩

end Fin

/- English proof (translation)
Establish `hR : (Formalism.REAL.muG ε).IsMulRightInvariant` using `unitary_unimodular_right_inv n ε`. Rewrite using `[Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]`. Conclude with `⟨fun g => by rw [Measure.map_smul, hR.map_mul_right_eq_self]⟩`.
-/
theorem uJ_rightInv {n : ℕ} (ε : Fin n → Bool) (μ : Measure (Formalism.REAL.UJ ε)) (hμ : μ.IsHaarMeasure) :
    μ.IsMulRightInvariant := by
  have hR : (Formalism.REAL.muG ε).IsMulRightInvariant := unitary_unimodular_right_inv n ε
  rw [Measure.isMulLeftInvariant_eq_smul μ (Formalism.REAL.muG ε)]
  exact ⟨fun g => by rw [Measure.map_smul, hR.map_mul_right_eq_self]⟩

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `ga_facts D V`. Take `⟨g1, g2, g3⟩` from `gf_facts fr`. Establish `hinf : ∀ μ : Measure (UI.instV fr).Ginf, μ.IsHaarMeasure → μ.IsMulRightInvariant` using `Leaf.Proofs.piStatement_holds (InfinitePlace D.host.F) (fun v => Formalism.REAL.UJ (fr.ε v)) (fun v μ hμ => uJ_rightInv (fr.ε v) μ hμ)`. Establish `hf : ∀ μ : Measure (UI.instV fr).Gf, μ.IsHaarMeasure → μ.IsMulRightInvariant` using `fun μ hμ => adUnimod_closed (UI.instV fr) μ hμ`. Establish `hprod` using `Leaf.Proofs.prodStatement_holds (UI.instV fr).Ginf (UI.instV fr).Gf hinf hf`.

Conclude with `Leaf.Proofs.transferStatement_holds (UI.instV fr).GA (GA D V) (UI.brg fr) hprod`.
-/
theorem unimodGA_of_frames {D : D7} {V : HSp D} (fr : UI.Frames D V) : UnimodGA V := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := ga_facts D V
  obtain ⟨g1, g2, g3⟩ := gf_facts fr
  have hinf : ∀ μ : Measure (UI.instV fr).Ginf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    Leaf.Proofs.piStatement_holds (InfinitePlace D.host.F) (fun v => Formalism.REAL.UJ (fr.ε v))
      (fun v μ hμ => uJ_rightInv (fr.ε v) μ hμ)
  have hf : ∀ μ : Measure (UI.instV fr).Gf, μ.IsHaarMeasure → μ.IsMulRightInvariant :=
    fun μ hμ => adUnimod_closed (UI.instV fr) μ hμ
  have hprod := Leaf.Proofs.prodStatement_holds (UI.instV fr).Ginf (UI.instV fr).Gf hinf hf
  exact Leaf.Proofs.transferStatement_holds (UI.instV fr).GA (GA D V) (UI.brg fr) hprod

/- English proof (translation)
The claim follows from `unimodGA_of_frames (UI.frames_nonempty D V).some`.
-/
theorem unimodGA_holds {D : D7} (V : HSp D) : UnimodGA V :=
  unimodGA_of_frames (UI.frames_nonempty D V).some

end Formalism.IndefR.Eqv

end
