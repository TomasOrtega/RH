import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace GlobalTheory.EtC.RedChern

/- English proof (translation)
Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_mono {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → P' V g) : Loc U P' := by
  obtain ⟨S, hS, hP0⟩ := h
  exact ⟨S, hS, fun V g hg => hP V g (hP0 V g hg)⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Supply the required witnesses or components.
-/
theorem loc_and {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P) (h' : Loc U P') :
    Loc U fun V g => P V g ∧ P' V g := by
  obtain ⟨S, hS, hP⟩ := h
  obtain ⟨S', hS', hP'⟩ := h'
  exact ⟨S ⊓ S', Scheme.etaleTopology.intersection_covering hS hS', fun V g hg => ⟨hP V g hg.1, hP' V g hg.2⟩⟩

/- English proof (translation)
Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. A detailed English derivation is pending.
-/
theorem loc_bind {U : Scheme.{0}} {P P' : ∀ V : Scheme.{0}, (V ⟶ U) → Prop} (h : Loc U P)
    (hP : ∀ V g, P V g → Loc V fun W k => P' W (k ≫ g)) : Loc U P' := by
  classical
  obtain ⟨S, hS, hP0⟩ := h
  choose T hT hT' using fun (V : Scheme.{0}) (g : V ⟶ U) (hg : S.arrows g) => hP V g (hP0 V g hg)
  refine ⟨Sieve.bind S.arrows fun V g hg => T V g hg, Scheme.etaleTopology.bind_covering hS fun V g hg => hT V g hg, ?_⟩
  rintro W f ⟨V, k, g, hg, hk, rfl⟩
  exact hT' V g hg W k hk

end GlobalTheory.EtC.RedChern
