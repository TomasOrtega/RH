import PositivityTheory.AutomorphicForms.PublishedInputs.JacquetLanglands.RealArchimedeanBounds.ATrans

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Base UpperTheory.V.Sd UpperTheory.V.Sd.Wc
open scoped Matrix NNReal

namespace UpperTheory.Esk

/- English proof (translation)
Introduce `hB hO F _ _ c hc`. Take `⟨S, hS⟩` from `hB F`. Take `⟨T, hT⟩` from `hO F c hc 1`. Use `⟨Finset.image₂ (· * ·) S T, fun x => ?_⟩` and prove the remaining obligations. Take `⟨b, hb, x', hx', k, hk, hx⟩` from `hS x`.

Take `⟨y, hy, h, hh, hkh⟩` from `hT k hk`. Use `⟨b, hb, x' * y, Finset.mem_image₂_of_mem hx' hy, h, hh, ?_⟩` and prove the remaining obligations. Rewrite using `[hx, mul_assoc, ← hkh, mul_one]`.
-/
theorem aBnfH : UpperTheory.Esk.ABnf → UpperTheory.Esk.AOrb → UpperTheory.Esk.ABnfH := by
  classical
  intro hB hO F _ _ c hc
  obtain ⟨S, hS⟩ := hB F
  obtain ⟨T, hT⟩ := hO F c hc 1
  refine ⟨Finset.image₂ (· * ·) S T, fun x => ?_⟩
  obtain ⟨b, hb, x', hx', k, hk, hx⟩ := hS x
  obtain ⟨y, hy, h, hh, hkh⟩ := hT k hk
  refine ⟨b, hb, x' * y, Finset.mem_image₂_of_mem hx' hy, h, hh, ?_⟩
  rw [hx, mul_assoc, ← hkh, mul_one]

end UpperTheory.Esk
