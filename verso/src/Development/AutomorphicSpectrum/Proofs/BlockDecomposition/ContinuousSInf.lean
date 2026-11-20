import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.SmoothVectorEstimates.WhittakerVanishingImpliesZero

noncomputable section

open NumberField IsDedekindDomain Matrix Topology Filter
open GlobalTheory.CuspGeneric GlobalTheory.CuspRep PositivityTheory.jumpWindows

namespace GlobalTheory.CompanionTheory.JSInfStep

variable {E : Type} [Field E] [NumberField E] {a : ℕ}

/- English proof (translation)
Take `⟨M, hM⟩` from `Ideal.exists_maximal (𝓞 E)`. Conclude with `⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩`.
-/
theorem nonempty_pl : Nonempty (Pl E) := by
  obtain ⟨M, hM⟩ := Ideal.exists_maximal (𝓞 E)
  exact ⟨⟨M, hM.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hM (RingOfIntegers.not_isField E)⟩⟩

variable [IsTotallyComplex E]

def chiInf (ψ : AddChar (Ad E) ℂ) : AddChar (Cinf E) ℂ :=
  ψ.compAddMonoidHom (AddMonoidHomClass.toAddMonoidHom (sInf E))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem chiInf_apply (ψ : AddChar (Ad E) ℂ) (z : Cinf E) : chiInf ψ z = ψ (sInf E z) := rfl

/- English proof (translation)
The claim follows from `((continuous_infEq E).prodMk continuous_const : Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))`.
-/
theorem continuous_sInf : Continuous (sInf E) :=
  ((continuous_infEq E).prodMk continuous_const :
    Continuous fun x : Cinf E => ((infEq E x, 0) : InfiniteAdeleRing E × Af E))

/- English proof (translation)
The claim follows from `(infEq E).symm_apply_apply x`.
-/
theorem pInf_sInf (x : Cinf E) : pInf E (sInf E x) = x := (infEq E).symm_apply_apply x

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem pFin_sInf (x : Cinf E) : pFin E (sInf E x) = 0 := rfl

/- English proof (translation)
Take `⟨d, hd⟩` from `hψ.ann (sInf E z) fun c => by`. Establish `e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c))`. Use `ad_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, pInf_sInf, pInf_sInf]`. Rewrite using `[map_mul, pFin_sInf, pFin_sInf, zero_mul]`.

Rewrite using `[e]`. Conclude with `h _`. Take `⟨w⟩` from `nonempty_pl (E := E)`. Use `haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial`. Establish `h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0`.

Express the relevant statement in the definitionally equal form `pFin E (algebraMap E (Ad E) d) = 0`. Rewrite using `[← hd, pFin_sInf]`. Establish `hd0 : d = 0` using `(injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0`. Rewrite using `[← pInf_sInf z, hd, hd0, map_zero, map_zero]`.
-/
theorem chiInf_nondeg {ψ : AddChar (Ad E) ℂ} (hψ : StdPsi ψ) (z : Cinf E)
    (h : ∀ w, chiInf ψ (z * w) = 1) : z = 0 := by
  obtain ⟨d, hd⟩ := hψ.ann (sInf E z) fun c => by
    have e : sInf E z * algebraMap E (Ad E) c = sInf E (z * pInf E (algebraMap E (Ad E) c)) := by
      refine ad_ext ?_ ?_
      · rw [map_mul, pInf_sInf, pInf_sInf]
      · rw [map_mul, pFin_sInf, pFin_sInf, zero_mul]
    rw [e]
    exact h _
  obtain ⟨w⟩ := nonempty_pl (E := E)
  haveI : Nontrivial (Af E) := (pLoc E w).domain_nontrivial
  have h0 : ((pFin E).comp (algebraMap E (Ad E))) d = 0 := by
    change pFin E (algebraMap E (Ad E) d) = 0
    rw [← hd, pFin_sInf]
  have hd0 : d = 0 := (injective_iff_map_eq_zero _).1 ((pFin E).comp (algebraMap E (Ad E))).injective d h0
  rw [← pInf_sInf z, hd, hd0, map_zero, map_zero]

end GlobalTheory.CompanionTheory.JSInfStep

end
