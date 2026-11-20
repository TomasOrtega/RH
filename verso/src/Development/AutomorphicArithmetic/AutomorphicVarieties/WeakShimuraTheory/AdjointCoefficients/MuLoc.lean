import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.GenOfMax
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointCoefficients.MuBock
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.LocEuler
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.PlaceDict
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.AdjointMemSp4
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.NearSplit
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisCochains.GLinkQuot

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Introduce `P F Ω _ _ _ _ _ l _ A hA`. Establish `hl : l.Prime` using `Fact.out`. Use `haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Use `haveI : IsGalois F Ω := {}`. Take `⟨-, h1, h2, -⟩` from `Kum.placeDict F Ω`.

Take `⟨v, hv⟩` from `h1 A (h2 A l hl.ne_zero hA)`. Establish `hc : ReciprocityTheory.Gal.ContAction (charRep (1 : Dec (F` using `F) A →* (ZMod l)ˣ)) := by`. Establish `e : (fun p : Dec (F` using `F) A × ZMod l => charRep (1 : Dec (F := F) A →* (ZMod l)ˣ) p.1 p.2) = Prod.snd := by`. Use function extensionality and compare the values at `p`. Conclude with `one_mul p.2`.

Unfold `ReciprocityTheory.Gal.ContAction`. Rewrite using `[e]`. Conclude with `continuous_snd`. Take `⟨-, f2, -, -, e2⟩` from `GC.locEuler P.loc.lf P.loc.lt P.loc.le F Ω l v A hv (ZMod l) (ZMod l) _ hc`. Use `X1.muCyc l _ (isClosed_Dec A) (X1.muBock l _ (isClosed_Dec A) (Module.finite_of_finite (ZMod l)) ?_)` and prove the remaining obligations.

Rewrite using `[Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod, e2]`. Use `(Nat.pow_le_pow_right hl.pos ((Submodule.finrank_le _).trans ?_)).trans_eq (pow_one l)` and prove the remaining obligations. Rewrite using `[Subspace.dual_finrank_eq, Module.finrank_self]`.
-/
theorem UpperTheory.V.Ws.X1.muLoc :
    CohomologyHyp → ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (l : ℕ) [Fact l.Prime] (A : ValuationSubring Ω), A.valuation (l : Ω) < 1 → ∃ ζ, MuGen (Dec (F := F) A) (muOf l (Dec (F := F) A)) ζ := by
  intro P F Ω _ _ _ _ _ l _ A hA
  have hl : l.Prime := Fact.out
  haveI : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  haveI : IsGalois F Ω := {}
  obtain ⟨-, h1, h2, -⟩ := Kum.placeDict F Ω
  obtain ⟨v, hv⟩ := h1 A (h2 A l hl.ne_zero hA)
  have hc : ReciprocityTheory.Gal.ContAction (charRep (1 : Dec (F := F) A →* (ZMod l)ˣ)) := by
    have e : (fun p : Dec (F := F) A × ZMod l => charRep (1 : Dec (F := F) A →* (ZMod l)ˣ) p.1 p.2) = Prod.snd := by
      funext p
      exact one_mul p.2
    unfold ReciprocityTheory.Gal.ContAction
    rw [e]
    exact continuous_snd
  obtain ⟨-, f2, -, -, e2⟩ := GC.locEuler P.loc.lf P.loc.lt P.loc.le F Ω l v A hv (ZMod l) (ZMod l) _ hc
  refine X1.muCyc l _ (isClosed_Dec A) (X1.muBock l _ (isClosed_Dec A) (Module.finite_of_finite (ZMod l)) ?_)
  rw [Module.natCard_eq_pow_finrank (K := ZMod l), Nat.card_zmod, e2]
  refine (Nat.pow_le_pow_right hl.pos ((Submodule.finrank_le _).trans ?_)).trans_eq (pow_one l)
  rw [Subspace.dual_finrank_eq, Module.finrank_self]
