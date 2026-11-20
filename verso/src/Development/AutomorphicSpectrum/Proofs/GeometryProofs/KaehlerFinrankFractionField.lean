import Mathlib

open TensorProduct

namespace GlobalTheory.CompanionTheory.Ggeo

/- English proof (translation)
Use `haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors T)`. Use `haveI : Algebra.FormallyUnramified S K := Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)`. Use `haveI : Subsingleton (KaehlerDifferential S K) := Algebra.FormallyUnramified.subsingleton_kaehlerDifferential`. Establish `hinj : Function.Injective (KaehlerDifferential.map S K L L)`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `x hx`. Take `⟨y, rfl⟩` from `(KaehlerDifferential.exact_mapBaseChange_map S K L x).1 hx`. Establish `hy : y = 0` using `Subsingleton.elim _ _`. Simplify using `[hy]`. Set `e : KaehlerDifferential S L ≃ₗ[L] KaehlerDifferential K L` to `LinearEquiv.ofBijective (KaehlerDifferential.map S K L L) ⟨hinj, KaehlerDifferential.map_surjective S K L⟩`.

Set `b : Module.Basis (Fin m) T (KaehlerDifferential S T)` to `Module.Basis.mk hli hspan.ge`. Set `b' : Module.Basis (Fin m) L (KaehlerDifferential K L)` to `((Algebra.TensorProduct.basis L b).map (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S T L)).map e`. Simplify using `using Module.finrank_eq_card_basis b'`.
-/
theorem finrank_kaehler_fractionRing_eq_of_basis
    (S T K L : Type) [CommRing S] [CommRing T] [Field K] [Field L] [Algebra S T] [Algebra S K]
    [Algebra S L] [Algebra T L] [Algebra K L] [IsScalarTower S T L] [IsScalarTower S K L]
    [IsFractionRing S K] [IsFractionRing T L] (m : ℕ) (w : Fin m → T)
    (hli : LinearIndependent T (fun i => KaehlerDifferential.D S T (w i)))
    (hspan : Submodule.span T (Set.range fun i => KaehlerDifferential.D S T (w i)) = ⊤) :
    Module.finrank L (KaehlerDifferential K L) = m := by
  haveI : Algebra.FormallyEtale T L := Algebra.FormallyEtale.of_isLocalization (nonZeroDivisors T)
  haveI : Algebra.FormallyUnramified S K :=
    Algebra.FormallyUnramified.of_isLocalization (nonZeroDivisors S)
  haveI : Subsingleton (KaehlerDifferential S K) :=
    Algebra.FormallyUnramified.subsingleton_kaehlerDifferential
  have hinj : Function.Injective (KaehlerDifferential.map S K L L) := by
    rw [injective_iff_map_eq_zero]
    intro x hx
    obtain ⟨y, rfl⟩ := (KaehlerDifferential.exact_mapBaseChange_map S K L x).1 hx
    have hy : y = 0 := Subsingleton.elim _ _
    simp [hy]
  let e : KaehlerDifferential S L ≃ₗ[L] KaehlerDifferential K L :=
    LinearEquiv.ofBijective (KaehlerDifferential.map S K L L)
      ⟨hinj, KaehlerDifferential.map_surjective S K L⟩
  let b : Module.Basis (Fin m) T (KaehlerDifferential S T) := Module.Basis.mk hli hspan.ge
  let b' : Module.Basis (Fin m) L (KaehlerDifferential K L) :=
    ((Algebra.TensorProduct.basis L b).map
      (KaehlerDifferential.tensorKaehlerEquivOfFormallyEtale S T L)).map e
  simpa using Module.finrank_eq_card_basis b'

end GlobalTheory.CompanionTheory.Ggeo
