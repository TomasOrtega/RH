import ReciprocityTheory.Hypotheses.GalCoh
import ReciprocityTheory.NeutralLocalFields.LocalFieldComparison.Transport
import Development.WeilBound.CoreStatements.EulerCharacteristicCounts.GcohCmp
import GroundTheory.ProfiniteCohomology.RestrictedRamification.IsUnramifiedOutsideIffLeMaxUnramifiedOutside
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.NormalSubgroupLeUnramifiedFixingStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.GaloisUnramifiedOutsideCohomologyStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH1UnramifiedOutsideStatement
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.FiniteH2UnramifiedOutside
import Development.AutomorphicSpectrum.Proofs.GlobalProofs.CohomologicalDimensionTwoUnramified

noncomputable section

open NumberField IsDedekindDomain CategoryTheory GroundTheory.ProfCoh ReciprocityTheory.Gal Formalism.ConjugateSelfDual

namespace GlobalTheory.CompanionTheory.Hypotheses₂

/- English proof (translation)
The claim follows from `le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)`.
-/
theorem NS_eq_fixingSubgroup (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) :
    NS Ω S = (maxUnramifiedOutside F Ω S).fixingSubgroup :=
  le_antisymm (GlobalTheory.T.normal_subgroup_le_unramified_fixing F Ω S) (GlobalTheory.T.galois_unramified_outside_cohomology F Ω S)

/- English proof (translation)
Establish `: IsGalois F Ω` using `IsAlgClosure.isGalois F Ω`. Set `E` to `maxUnramifiedOutside F Ω S`. Set `φ : G F Ω →* Gal(E/F)` to `AlgEquiv.restrictNormalHom E`. Establish `hφs : Function.Surjective φ` using `AlgEquiv.restrictNormalHom_surjective Ω`. Establish `hker : φ.ker = NS Ω S`.

Rewrite using `[NS_eq_fixingSubgroup F Ω S]`. Use extensionality with `σ`. Rewrite using `[MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`.

Establish `h1` using `AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)`. Establish `h2 : σ.restrictNormal E = 1` using `h`. Rewrite `h1` using `[h2]`. Conclude with `h1.symm`. Introduce `h`.

Apply `AlgEquiv.ext` to reduce the goal to its premises. Introduce `x`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `(AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)`. Establish `hφc : Continuous φ` using `InfiniteGalois.restrictNormalHom_continuous E`.

Set `q : GS Ω S ≃* Gal(E/F)` to `(QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)`. Establish `hq : Continuous q` using `continuous_coinduced_dom.2 hφc`. Establish `: CompactSpace (G F Ω)` using `inferInstance`. Establish `: CompactSpace (GS Ω S)` using `Quotient.compactSpace`. Conclude with `⟨{ q with continuous_toFun := hq continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }⟩`.
-/
theorem exists_gsEquiv (F Ω : Type) [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
    (S : Set (HeightOneSpectrum (𝓞 F))) : Nonempty (GS Ω S ≃ₜ* galUnramifiedOutside F Ω S) := by
  have : IsGalois F Ω := IsAlgClosure.isGalois F Ω
  let E := maxUnramifiedOutside F Ω S
  let φ : G F Ω →* Gal(E/F) := AlgEquiv.restrictNormalHom E
  have hφs : Function.Surjective φ := AlgEquiv.restrictNormalHom_surjective Ω
  have hker : φ.ker = NS Ω S := by
    rw [NS_eq_fixingSubgroup F Ω S]
    ext σ
    rw [MonoidHom.mem_ker, IntermediateField.mem_fixingSubgroup_iff]
    constructor
    · intro h x hx
      have h1 := AlgEquiv.restrictNormal_commutes σ E (⟨x, hx⟩ : E)
      have h2 : σ.restrictNormal E = 1 := h
      rw [h2] at h1
      exact h1.symm
    · intro h
      apply AlgEquiv.ext
      intro x
      apply Subtype.ext
      exact (AlgEquiv.restrictNormal_commutes σ E x).trans (h x.1 x.2)
  have hφc : Continuous φ := InfiniteGalois.restrictNormalHom_continuous E
  let q : GS Ω S ≃* Gal(E/F) :=
    (QuotientGroup.quotientMulEquivOfEq hker.symm).trans (QuotientGroup.quotientKerEquivOfSurjective φ hφs)
  have hq : Continuous q := continuous_coinduced_dom.2 hφc
  have : CompactSpace (G F Ω) := inferInstance
  have : CompactSpace (GS Ω S) := Quotient.compactSpace
  exact ⟨{ q with
    continuous_toFun := hq
    continuous_invFun := Continuous.continuous_symm_of_equiv_compact_to_t2 (f := q.toEquiv) hq }⟩

/- English proof (translation)
Introduce `F Ω _ _ _ _ _ l hl r M _ _ _ _ _ S rhoS hr hS hc`. Take `⟨e0⟩` from `exists_gsEquiv F Ω (S : Set (HeightOneSpectrum (𝓞 F)))`. Set `e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* GS Ω (S : Set (HeightOneSpectrum (𝓞 F)))` to `e0.symm`. Establish `hc'` using `ReciprocityTheory.Neutral.Bridge.contAction_comp e hc`. Set `rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M` to `rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))`.

Take `⟨A, _, eA, he⟩` from `PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'`. Establish `hAf : Finite A.V` using `Finite.of_equiv _ eA.toEquiv`. Establish `hn : ∀ a : A.V, (l ^ r) • a = 0`. Introduce `a`. Take `⟨m, rfl⟩` from `eA.surjective a`.

Rewrite using `[← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]`. Take `⟨e1, -⟩` from `PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he`. Take `⟨e2, -⟩` from `PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he`. Establish `f1` using `GlobalTheory.T.finite_H1_unramified_outside F Ω l r S hS A hAf hn`. Establish `f2` using `GlobalTheory.T.finite_H2_unramified_outside F Ω l r S hS A hAf hn`.

Establish `t1` using `ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)`. Establish `t2` using `ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)`. Use `⟨?_, ?_, ?_, fun hl2 n hn3 => ?_⟩` and prove the remaining obligations. Conclude with `Finite.of_injective (fun x : H0 rhoS => (x : M)) Subtype.val_injective`. Establish `: Finite (H1 rho')` using `Finite.of_equiv _ e1.symm.toEquiv`.

Conclude with `Finite.of_equiv _ t1.toEquiv.symm`. Establish `: Finite (H2 rho')` using `Finite.of_equiv _ e2.symm.toEquiv`. Conclude with `Finite.of_equiv _ t2.toEquiv.symm`. Take `⟨en⟩` from `PositivityTheory.LocalTateOrthogonality.Gcoh.gcn _ (ZMod (l ^ r)) M rho' A eA he n`. Use `GlobalTheory.T.cohomological_dimension_two_unramified F Ω l r S hS hl2 A hAf hn n hn3` as an intermediate fact.

Establish `: Subsingleton (Hn rho' n)` using `en.toEquiv.subsingleton`. Conclude with `(ReciprocityTheory.Neutral.Bridge.isoHn e rhoS rho' (fun _ _ => rfl) n).toEquiv.subsingleton`.
-/
theorem globalFiniteness : ReciprocityTheory.Gal.GlobalFiniteness := by
  intro F Ω _ _ _ _ _ l hl r M _ _ _ _ _ S rhoS hr hS hc
  obtain ⟨e0⟩ := exists_gsEquiv F Ω (S : Set (HeightOneSpectrum (𝓞 F)))
  let e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) ≃ₜ* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))) :=
    e0.symm
  have hc' := ReciprocityTheory.Neutral.Bridge.contAction_comp e hc
  let rho' : Representation (ZMod (l ^ r)) (galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F)))) M :=
    rhoS.comp (e : galUnramifiedOutside F Ω (S : Set (HeightOneSpectrum (𝓞 F))) →* GS Ω (S : Set (HeightOneSpectrum (𝓞 F))))
  obtain ⟨A, _, eA, he⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcRep _ (ZMod (l ^ r)) M rho' hc'
  have hAf : Finite A.V := Finite.of_equiv _ eA.toEquiv
  have hn : ∀ a : A.V, (l ^ r) • a = 0 := by
    intro a
    obtain ⟨m, rfl⟩ := eA.surjective a
    rw [← map_nsmul, ← Nat.cast_smul_eq_nsmul (ZMod (l ^ r)), ZMod.natCast_self, zero_smul, map_zero]
  obtain ⟨e1, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc1 _ (ZMod (l ^ r)) M rho' A eA he
  obtain ⟨e2, -⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gc2 _ (ZMod (l ^ r)) M rho' A eA he
  have f1 := GlobalTheory.T.finite_H1_unramified_outside F Ω l r S hS A hAf hn
  have f2 := GlobalTheory.T.finite_H2_unramified_outside F Ω l r S hS A hAf hn
  have t1 := ReciprocityTheory.Neutral.Bridge.equivH1OfIso e rhoS rho' (fun _ _ => rfl)
  have t2 := ReciprocityTheory.Neutral.Bridge.equivH2OfIso e rhoS rho' (fun _ _ => rfl)
  refine ⟨?_, ?_, ?_, fun hl2 n hn3 => ?_⟩
  · exact Finite.of_injective (fun x : H0 rhoS => (x : M)) Subtype.val_injective
  · have : Finite (H1 rho') := Finite.of_equiv _ e1.symm.toEquiv
    exact Finite.of_equiv _ t1.toEquiv.symm
  · have : Finite (H2 rho') := Finite.of_equiv _ e2.symm.toEquiv
    exact Finite.of_equiv _ t2.toEquiv.symm
  · obtain ⟨en⟩ := PositivityTheory.LocalTateOrthogonality.Gcoh.gcn _ (ZMod (l ^ r)) M rho' A eA he n
    have := GlobalTheory.T.cohomological_dimension_two_unramified F Ω l r S hS hl2 A hAf hn n hn3
    have : Subsingleton (Hn rho' n) := en.toEquiv.subsingleton
    exact (ReciprocityTheory.Neutral.Bridge.isoHn e rhoS rho' (fun _ _ => rfl) n).toEquiv.subsingleton

end GlobalTheory.CompanionTheory.Hypotheses₂
