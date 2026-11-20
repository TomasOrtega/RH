import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.ZetaCharacterDivisibility.PhiOfDivOf

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.WeilDeligne GlobalTheory.Pst GlobalTheory.HeckeGal GlobalTheory.UnitaryBC GlobalTheory.Cong GlobalTheory.CongL GlobalTheory.RoadWGeo
open Formalism.MainNotions.SumRepresentations.At (sumRep)
open GlobalTheory.TripleGal (rk1)
open UpperTheory.V.Af (FrobEig algSat RepIso)
open UpperTheory.Gal.TP.Sub (Cl Above unrPol)
open UpperTheory.Gal.crystallineComparison (GenericMul rootPol)
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
open GlobalTheory.BlockSum (blockRep)
open PositivityTheory.AutomorphicGaloisHodgeTate.Div (DivWCoreLac SenWLac HTLac IsSSMat)
open UpperTheory.Gal.Int.Div

/- English proof (translation)
Introduce `E Ω _ _ _ _ _ l _ a dd ρ h`. Take `⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩` from `h`. Establish `hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i)` using `(J₀.orderEmbOfFin hc).injective`. Use `⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩` and prove the remaining obligations. Introduce `S T hS hT' hd heq`.

Set `f : Fin a ↪ ℤ` to `⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩`. Establish `hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀`. Introduce `C x hx`. Take `⟨i, -, rfl⟩` from `Finset.mem_map.1 hx`. Conclude with `Finset.orderEmbOfFin_mem J₀ hc i`.

Use `hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd) (hS.map) (hT'.map) ?_` and prove the remaining obligations. Rewrite using `[Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]`. Establish `: ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i`. Simplify `heq` using `[f]`. Simplify using `using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)`.
-/
theorem UpperTheory.Gal.Int.Div.lacBridge_of :
    LacBridge := by
  intro E Ω _ _ _ _ _ l _ a dd ρ h
  obtain ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ, J₀, hc, hm, hL⟩ := h
  have hinj : Function.Injective (fun i => J₀.orderEmbOfFin hc i) := (J₀.orderEmbOfFin hc).injective
  refine ⟨P, AI, hT, w, A, hl, hA, O, i1, i2, i3, Bw, hI, τ, J, hJ,
    fun i => J₀.orderEmbOfFin hc i, hinj, fun i => hm _ (Finset.orderEmbOfFin_mem J₀ hc i), ?_⟩
  intro S T hS hT' hd heq
  let f : Fin a ↪ ℤ := ⟨fun i => J₀.orderEmbOfFin hc i, hinj⟩
  have hsub : ∀ C : Finset (Fin a), C.map f ⊆ J₀ := by
    intro C x hx
    obtain ⟨i, -, rfl⟩ := Finset.mem_map.1 hx
    exact Finset.orderEmbOfFin_mem J₀ hc i
  refine hL (S.map f) (T.map f) (hsub S) (hsub T) ((Finset.disjoint_map f).2 hd)
    (hS.map) (hT'.map) ?_
  rw [Finset.card_map, Finset.card_map, Finset.sum_map, Finset.sum_map]
  have : ((T.card : ℤ) * ∑ i ∈ S, f i : ℚ) = (S.card : ℤ) * ∑ i ∈ T, f i := by
    simpa [f] using heq
  simpa using (by exact_mod_cast this : (T.card : ℤ) * ∑ i ∈ S, f i = (S.card : ℤ) * ∑ i ∈ T, f i)
