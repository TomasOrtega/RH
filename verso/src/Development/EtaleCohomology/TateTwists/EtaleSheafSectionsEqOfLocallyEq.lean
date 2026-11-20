import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Definitions.Divisors.SecClass
import Development.EtaleCohomology.TateTwists.EtaleSheafificationSectionsLocallyFromPresheaf

open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.ShfLocPf

/- English proof (translation)
Introduce `R _ P`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `U y`. Use `⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩` and prove the remaining obligations. Introduce `V g hg`.

Take `⟨t, ht⟩` from `hg`. Conclude with `⟨t, ht⟩`. Introduce `U x hx`. Establish `h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x = ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0` using `by rw [hx, map_zero]`. Use `⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩` and prove the remaining obligations.

Introduce `V g hg`. Establish `hg' : (P.map g.op).hom x = (P.map g.op).hom 0` using `hg`. Rewrite using `[hg', map_zero]`. Introduce `F φ`. Use `⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `toSheafify_sheafifyLift Scheme.etaleTopology φ F.property`. Introduce `ψ hψ ext1`. Conclude with `sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ`.
-/
theorem etale_sheaf_sections_eq_of_locally_eq : LateralTheory.EtaleFoundations.EtaleSheafificationSectionsLocallyFromPresheaf := by
  intro R _ P
  refine ⟨?_, ?_, ?_⟩
  · intro U y
    refine ⟨_, Presheaf.imageSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) y, ?_⟩
    intro V g hg
    obtain ⟨t, ht⟩ := hg
    exact ⟨t, ht⟩
  · intro U x hx
    have h : ((toSheafify Scheme.etaleTopology P).app (op U)).hom x =
        ((toSheafify Scheme.etaleTopology P).app (op U)).hom 0 := by rw [hx, map_zero]
    refine ⟨_, Presheaf.equalizerSieve_mem Scheme.etaleTopology (toSheafify Scheme.etaleTopology P) x 0 h, ?_⟩
    intro V g hg
    have hg' : (P.map g.op).hom x = (P.map g.op).hom 0 := hg
    rw [hg', map_zero]
  · intro F φ
    refine ⟨ObjectProperty.homMk (sheafifyLift Scheme.etaleTopology φ F.property), ?_, ?_⟩
    · exact toSheafify_sheafifyLift Scheme.etaleTopology φ F.property
    · intro ψ hψ
      ext1
      exact sheafifyLift_unique Scheme.etaleTopology φ F.property ψ.hom hψ

end LateralTheory.EtaleFoundations.ShfLocPf
