import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.CuspRapidDecaySiegelGL
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EqZeroOfMemWeakIn
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.SetIntegralNormRmulLe
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ContinuousIntegralInvMulOfLocallyIntegrable
open NumberField GlobalTheory.CuspRep GlobalTheory.CuspRep.CuspidalL2GL GlobalTheory.CuspQuot GlobalTheory.AutomorphicL2Unitary GlobalTheory.OpTrace MeasureTheory

open scoped RestrictedProduct

noncomputable section

namespace GlobalTheory.GLFinAdeleNhds

/- English proof (translation)
Use `⟨fun s _ hs => ?_⟩` and prove the remaining obligations. Establish `h` using `(hs.image f hf.continuousOn).subsingleton`. Conclude with `fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))`.
-/
theorem totallyDisconnectedSpace_of_injective {X Y : Type} [TopologicalSpace X] [TopologicalSpace Y]
    [TotallyDisconnectedSpace Y] (f : X → Y) (hf : Continuous f) (hi : Function.Injective f) :
    TotallyDisconnectedSpace X := by
  refine ⟨fun s _ hs => ?_⟩
  have h := (hs.image f hf.continuousOn).subsingleton
  exact fun x hx y hy => hi (h (Set.mem_image_of_mem f hx) (Set.mem_image_of_mem f hy))

/- English proof (translation)
Rewrite using `[totallyDisconnectedSpace_iff_connectedComponent_zero]`. Use `Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0` using `(Valuation.zero_iff _).not.mpr hne`. Establish `hc` using `Valued.isClopen_ball (R := v.adicCompletion F) ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)`.

Establish `h0 : (0 : v.adicCompletion F) ∈ {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y < (Valued.v : Valuation (v.adicCompletion F) _).restrict x}`. Simplify using `only [Set.mem_ofPred_eq, map_zero]`. Conclude with `pos_iff_ne_zero.mpr hr`. Establish `h1` using `hc.connectedComponent_subset h0 hx`. Conclude with `(lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1`.
-/
theorem totallyDisconnectedSpace_adicCompletion {F : Type} [Field F] [NumberField F]
    (v : IsDedekindDomain.HeightOneSpectrum (𝓞 F)) : TotallyDisconnectedSpace (v.adicCompletion F) := by
  rw [totallyDisconnectedSpace_iff_connectedComponent_zero]
  refine Set.eq_singleton_iff_unique_mem.mpr ⟨mem_connectedComponent, fun x hx => ?_⟩
  by_contra hne
  have hr : (Valued.v : Valuation (v.adicCompletion F) _).restrict x ≠ 0 :=
    (Valuation.zero_iff _).not.mpr hne
  have hc := Valued.isClopen_ball (R := v.adicCompletion F)
    ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)
  have h0 : (0 : v.adicCompletion F) ∈
      {y | (Valued.v : Valuation (v.adicCompletion F) _).restrict y <
        (Valued.v : Valuation (v.adicCompletion F) _).restrict x} := by
    simp only [Set.mem_ofPred_eq, map_zero]
    exact pos_iff_ne_zero.mpr hr
  have h1 := hc.connectedComponent_subset h0 hx
  exact (lt_irrefl ((Valued.v : Valuation (v.adicCompletion F) _).restrict x)) h1

/- English proof (translation)
Use `haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), TotallyDisconnectedSpace (v.adicCompletion E) := fun v => totallyDisconnectedSpace_adicCompletion v`. Use `haveI : TotallyDisconnectedSpace (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]) := totallyDisconnectedSpace_of_injective (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v) fun x y h => Subtype.ext (fu …`. Conclude with `inferInstanceAs (TotallyDisconnectedSpace (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))`.
-/
theorem totallyDisconnectedSpace_Af (E : Type) [Field E] [NumberField E] : TotallyDisconnectedSpace (Af E) := by
  haveI : ∀ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), TotallyDisconnectedSpace (v.adicCompletion E) :=
    fun v => totallyDisconnectedSpace_adicCompletion v
  haveI : TotallyDisconnectedSpace
      (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]) :=
    totallyDisconnectedSpace_of_injective (fun x v => x v) (continuous_pi fun v => RestrictedProduct.continuous_eval v)
      fun x y h => Subtype.ext (funext fun v => congrFun h v)
  exact inferInstanceAs (TotallyDisconnectedSpace
    (Πʳ v : IsDedekindDomain.HeightOneSpectrum (𝓞 E), [v.adicCompletion E, v.adicCompletionIntegers E]))

/- English proof (translation)
Use `haveI := totallyDisconnectedSpace_Af E`. Use `haveI : TotallyDisconnectedSpace (Matrix (Fin a) (Fin a) (Af E)) := inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin a → Af E))`. Use `haveI : TotallyDisconnectedSpace (GL (Fin a) (Af E)) := totallyDisconnectedSpace_of_injective _ Units.continuous_val Units.val_injective`. Use `haveI : LocallyCompactSpace (GL (Fin a) (Af E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace`. Take `⟨K, hK, hKB, hc⟩` from `local_compact_nhds hB`.

Take `⟨U, hU, h1, hUK⟩` from `loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK`. Conclude with `⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, hU.1, h1, hUK.trans hKB⟩`.
-/
theorem exists_isCompact_isClopen (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E)))
    (hB : B ∈ nhds (1 : GL (Fin a) (Af E))) :
    ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := by
  haveI := totallyDisconnectedSpace_Af E
  haveI : TotallyDisconnectedSpace (Matrix (Fin a) (Fin a) (Af E)) :=
    inferInstanceAs (TotallyDisconnectedSpace (Fin a → Fin a → Af E))
  haveI : TotallyDisconnectedSpace (GL (Fin a) (Af E)) :=
    totallyDisconnectedSpace_of_injective _ Units.continuous_val Units.val_injective
  haveI : LocallyCompactSpace (GL (Fin a) (Af E)) := Units.isClosedEmbedding_embedProduct.locallyCompactSpace
  obtain ⟨K, hK, hKB, hc⟩ := local_compact_nhds hB
  obtain ⟨U, hU, h1, hUK⟩ := loc_compact_Haus_tot_disc_of_zero_dim.mem_nhds_iff.1 hK
  exact ⟨U, hU.2, hc.of_isClosed_subset hU.1 hUK, hU.1, h1, hUK.trans hKB⟩

/- English proof (translation)
The claim follows from `exists_isCompact_isClopen`.
-/
example : ∀ (E : Type) [Field E] [NumberField E] (a : ℕ) (B : Set (GL (Fin a) (Af E))), B ∈ nhds (1 : GL (Fin a) (Af E)) → ∃ U : Set (GL (Fin a) (Af E)), IsOpen U ∧ IsCompact U ∧ IsClosed U ∧ 1 ∈ U ∧ U ⊆ B := exists_isCompact_isClopen

end GlobalTheory.GLFinAdeleNhds
