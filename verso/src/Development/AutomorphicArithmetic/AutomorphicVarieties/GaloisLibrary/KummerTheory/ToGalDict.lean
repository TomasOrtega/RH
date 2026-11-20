import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.KummerTheory.Mk0IdMapCongr
import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.SelmerTransport.GalEmbTop

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.LDataCardLeFinrank UpperTheory.V.Base UpperTheory.V.Kum
open scoped Pointwise

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU`. Take `⟨hE, hO, -⟩` from `galEmbTop F K Ω`. Establish `hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F` using `K) A ↔ u.1 ∈ Dec (F := F) A := by`. Introduce `A u`. Rewrite using `[mem_Dec, mem_Dec]`.

Establish `e : toGal K hU u • A = u.1 • A`. Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]`. Conclude with `Iff.rfl`. Rewrite using `[e]`.

Establish `hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val` using `funext fun u => AlgEquiv.ext fun x => rfl`. Establish `hc : Continuous (toGal K hU)`. Rewrite using `[hE.isInducing.continuous_iff, hcomp]`. Conclude with `continuous_subtype_val`. Use `⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩` and prove the remaining obligations.

Conclude with `⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩`. Rewrite using `[isHomeomorph_iff_exists_inverse]`. Use `⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl), fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩` and prove the remaining obligations. Rewrite using `[le_antisymm hU h]`. Conclude with `hO`.
-/
theorem UpperTheory.V.Kum.toGalDict :
    ∀ (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] (K : Type) [Field K] [NumberField K] [Algebra F K] [Algebra K Ω] [IsScalarTower F K Ω] [IsAlgClosure K Ω] (U : Subgroup (G F Ω)) (hU : U ≤ galOf F K Ω),
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A) ∧
    (∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Ine (F := K) A ↔ u.1 ∈ Ine (F := F) A) ∧
    Continuous (toGal K hU) ∧ (galOf F K Ω ≤ U → IsHomeomorph (toGal K hU) ∧ IsOpen (U : Set (G F Ω))) := by
  intro F Ω _ _ _ _ _ K _ _ _ _ _ _ U hU
  obtain ⟨hE, hO, -⟩ := galEmbTop F K Ω
  have hD : ∀ (A : ValuationSubring Ω) (u : U), toGal K hU u ∈ Dec (F := K) A ↔ u.1 ∈ Dec (F := F) A := by
    intro A u
    rw [mem_Dec, mem_Dec]
    have e : toGal K hU u • A = u.1 • A := by
      ext x
      rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem]
      exact Iff.rfl
    rw [e]
  have hcomp : galEmb F K Ω ∘ toGal K hU = Subtype.val := funext fun u => AlgEquiv.ext fun x => rfl
  have hc : Continuous (toGal K hU) := by
    rw [hE.isInducing.continuous_iff, hcomp]
    exact continuous_subtype_val
  refine ⟨hD, fun A u => ?_, hc, fun h => ⟨?_, ?_⟩⟩
  · exact ⟨fun h => ⟨(hD A u).1 h.1, h.2⟩, fun h => ⟨(hD A u).2 h.1, h.2⟩⟩
  · rw [isHomeomorph_iff_exists_inverse]
    refine ⟨hc, fun σ => ⟨galEmb F K Ω σ, h (galEmb_mem F K Ω σ)⟩, fun u => Subtype.ext (AlgEquiv.ext fun x => rfl),
      fun σ => AlgEquiv.ext fun x => rfl, hE.continuous.subtype_mk _⟩
  · rw [le_antisymm hU h]
    exact hO
