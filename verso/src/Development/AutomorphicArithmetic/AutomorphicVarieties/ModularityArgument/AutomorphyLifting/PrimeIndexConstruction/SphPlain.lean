import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.AutomorphyLifting.PrimeIndexConstruction.GenericR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsSubquotientProdIrrUc
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CohomologicalLocalComponentExponents
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FieldPointLiftsGenericFibre
import Development.WeilBound.RepresentationTheoryGL.GenericUnitaryGL.GenericUnitaryDualGLOfTwo

noncomputable section

open NumberField IsDedekindDomain GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.LocGL GlobalTheory.CuspRep GlobalTheory.RoadU GlobalTheory.LocLanglands UpperTheory.V UpperTheory.V.Af UpperTheory.V.Z.Win

attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

open private UpperTheory.V.Af.RealLocalComponent.isotypic from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.TemperedLocalComponents.LocCompR
open private satLocFree from Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.HeckeAdjoints.SatLocFree

namespace UpperTheory.V.Z.Win.Birth

section Local

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Introduce `e`. Rewrite `e` using `[IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj]`. Establish `h1 : absPow k 1 = 1` using `mul_left_cancel (a := θ) (by rw [mul_one]; exact e.symm)`. Establish `h2 : absPow k ((1 : ℝ) : ℂ) = 1` using `by simpa using h1`. Conclude with `one_ne_zero (absPow_ofReal_eq_one.1 h2)`.
-/
private theorem ofChar_ne_nu (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ) : IrrGL.ofChar θ hθ ≠ (IrrGL.ofChar θ hθ).nu 1 := by
  intro e
  rw [IrrGL.nu, IrrGL.tw_ofChar, IrrGL.ofChar_inj] at e
  have h1 : absPow k 1 = 1 := mul_left_cancel (a := θ) (by rw [mul_one]; exact e.symm)
  have h2 : absPow k ((1 : ℝ) : ℂ) = 1 := by simpa using h1
  exact one_ne_zero (absPow_ofReal_eq_one.1 h2)

/- English proof (translation)
Use extensionality with `x`. Rewrite using `[Segment.mem_carrier, Set.mem_singleton_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, rfl⟩`. Take `rfl : n = 0` from `by omega`.

Simplify using the standard rewrite rules. Introduce and unpack `rfl`. Conclude with `⟨0, by omega, by simp⟩`.
-/
private theorem carrier_of_len {D : Segment k} (h : D.len = 1) : D.carrier = {D.first} := by
  ext x
  rw [Segment.mem_carrier, Set.mem_singleton_iff]
  constructor
  · rintro ⟨n, hn, rfl⟩
    obtain rfl : n = 0 := by omega
    simp
  · rintro rfl
    exact ⟨0, by omega, by simp⟩

/- English proof (translation)
Establish `hne : D.first ≠ D'.first`. Rewrite using `[e, e']`. Conclude with `fun h => ofChar_ne_nu θ hθ h.symm`. Rewrite using `[Segment.Linked, carrier_of_len h, carrier_of_len h']`. Use `⟨⟨Segment.ofChar θ hθ 2 (by norm_num), ?_⟩, ?_, ?_⟩` and prove the remaining obligations.

Establish `hf : (Segment.ofChar θ hθ 2 (by norm_num)).first = D'.first` using `e'.symm`. Establish `hl : (Segment.ofChar θ hθ 2 (by norm_num)).len = 2` using `rfl`. Use extensionality with `x`. Simplify using `only [Segment.mem_carrier, Set.mem_union, Set.mem_singleton_iff]`. Rewrite using `[hl, hf]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨n, hn, rfl⟩`. Take `rfl | rfl : n = 0 ∨ n = 1` from `by omega`. Use `right`. Simplify using the standard rewrite rules.

Use `left`. Simplify using `using e.symm`. Introduce and unpack `(rfl | rfl)`. Conclude with `⟨1, by omega, by simpa using e.symm⟩`. Conclude with `⟨0, by omega, by simp⟩`.

Simplify using `using hne`. Simplify using `using hne.symm`.
-/
private theorem linked_of_len {D D' : Segment k} (h : D.len = 1) (h' : D'.len = 1) (θ : kˣ →* ℂˣ) (hθ : IsSmoothChar θ)
    (e' : D'.first = IrrGL.ofChar θ hθ) (e : D.first = D'.first.nu 1) : D.Linked D' := by
  have hne : D.first ≠ D'.first := by
    rw [e, e']
    exact fun h => ofChar_ne_nu θ hθ h.symm
  rw [Segment.Linked, carrier_of_len h, carrier_of_len h']
  refine ⟨⟨Segment.ofChar θ hθ 2 (by norm_num), ?_⟩, ?_, ?_⟩
  · have hf : (Segment.ofChar θ hθ 2 (by norm_num)).first = D'.first := e'.symm
    have hl : (Segment.ofChar θ hθ 2 (by norm_num)).len = 2 := rfl
    ext x
    simp only [Segment.mem_carrier, Set.mem_union, Set.mem_singleton_iff]
    rw [hl, hf]
    constructor
    · rintro ⟨n, hn, rfl⟩
      obtain rfl | rfl : n = 0 ∨ n = 1 := by omega
      · right
        simp
      · left
        simpa using e.symm
    · rintro (rfl | rfl)
      · exact ⟨1, by omega, by simpa using e.symm⟩
      · exact ⟨0, by omega, by simp⟩
  · simpa using hne
  · simpa using hne.symm

end Local

/- English proof (translation)
Use `haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective`. Take `⟨ξ, hξ, ϖ, hs, -, -, -⟩` from `GlobalTheory.SatSupp.hasSupport_of_hasSatGL E N hN w σ B hB`. Take `⟨α, -, hα⟩` from `(GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1 (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)`. Take `⟨h, Δ, y, hd, hun, hL, ⟨φ⟩⟩` from `GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds _ N σ.V σ.ρ σ.smooth σ.irred hg`. Establish `hsub : IsSubquotient σ.ρ (prodIrr y hd)` using `IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective`.

Establish `hsp` using `GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ h N y hd σ.V σ.ρ hsub hα.2.1`. Establish `h1 : ∀ i, (y i).1 = 1` using `fun i => GlobalTheory.TempSat.deg_eq_one_of_isLSeg (hL i) (hsp i)`. Establish `hlen : ∀ i, (Δ i).len = 1` using `fun i => by`. Establish `h2` using `(hL i).deg_eq`. Rewrite `h2` using `[h1 i, Segment.deg]`.

Conclude with `Nat.eq_one_of_mul_eq_one_right h2`. Establish `hG : GlobalTheory.Published.GeometricLemma` using `GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds`. Establish `hs2 : HasSupport σ.ρ (∑ i, (Δ i).ms)` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL i).hasSupport) σ.irred hsub`. Establish `he : ∑ i, (Δ i).ms = chars ξ hξ` using `GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2 (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)`. Use `⟨chars ξ hξ, hs, fun z hz => ?_, fun a ha b hb e => ?_⟩` and prove the remaining obligations.

Take `⟨j, -, rfl⟩` from `Multiset.mem_map.1 hz`. Both sides reduce to the same expression. Take `⟨j, -, hj⟩` from `Multiset.mem_map.1 hb`. Rewrite `ha`, `hb` using `[← he]`. Take `⟨i, -, hi⟩` from `Multiset.mem_sum.1 ha`.

Take `⟨i', -, hi'⟩` from `Multiset.mem_sum.1 hb`. Establish `ea : a = (Δ i).first`. Use `Segment.mem_ms.1 hi` as an intermediate fact. Rewrite `this` using `[carrier_of_len (hlen i)]`. Then use the resulting hypothesis. Establish `eb : b = (Δ i').first`.

Use `Segment.mem_ms.1 hi'` as an intermediate fact. Rewrite `this` using `[carrier_of_len (hlen i')]`. Then use the resulting hypothesis. Substitute `ea` using the available equality. Distinguish the cases in `hii : i = i'`. Substitute `hii` using the available equality.

Rewrite `e` using `[← eb]`. Substitute `hj` using the available equality. Conclude with `ofChar_ne_nu _ _ e`. Conclude with `hun i i' hii (linked_of_len (hlen i) (hlen i') (ξ j) (hξ j) (eb ▸ hj.symm) (eb ▸ e))`.
-/
theorem plainTor_of_sph {E : Type} [Field E] [NumberField E] {N : ℕ} (hN : 1 ≤ N) (w : HeightOneSpectrum (𝓞 E))
    (σ : SmIrr (GL (Fin N) (w.adicCompletion E))) (B : Multiset ℂˣ) (hB : GlobalTheory.LFun.HasSatGL w σ.ρ B)
    (hg : IsGeneric σ.ρ) : PlainTor (IrrGL.of σ.ρ σ.smooth σ.irred) := by
  haveI : CharZero (w.adicCompletion E) := charZero_of_injective_algebraMap (algebraMap E _).injective
  obtain ⟨ξ, hξ, ϖ, hs, -, -, -⟩ := GlobalTheory.SatSupp.hasSupport_of_hasSatGL E N hN w σ B hB
  obtain ⟨α, -, hα⟩ := (GlobalTheory.LGrp.SatakeCompare.hasSatakeGL_iff _ _ _ σ.ρ B).1
    (GlobalTheory.LFun.SatCompare.hasSatakeGL_iff.2 ⟨⟨σ.smooth, σ.irred⟩, hB⟩)
  obtain ⟨h, Δ, y, hd, hun, hL, ⟨φ⟩⟩ := GlobalTheory.RgGu.Holds.genericUnlinkedGL_holds _ N σ.V σ.ρ σ.smooth σ.irred hg
  have hsub : IsSubquotient σ.ρ (prodIrr y hd) :=
    IsSubquotient.of_injective φ.toIntertwiningMap φ.toLinearEquiv.injective
  have hsp := GlobalTheory.LocLanglands.SphFac.isSpherical_factor _ h N y hd σ.V σ.ρ hsub hα.2.1
  have h1 : ∀ i, (y i).1 = 1 := fun i => GlobalTheory.TempSat.deg_eq_one_of_isLSeg (hL i) (hsp i)
  have hlen : ∀ i, (Δ i).len = 1 := fun i => by
    have h2 := (hL i).deg_eq
    rw [h1 i, Segment.deg] at h2
    exact Nat.eq_one_of_mul_eq_one_right h2
  have hG : GlobalTheory.Published.GeometricLemma :=
    GlobalTheory.geometricLemma_of_filtration GlobalTheory.Laid.bzfin_holds GlobalTheory.geometricLemmaFiltration_holds
  have hs2 : HasSupport σ.ρ (∑ i, (Δ i).ms) :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_of_isSubquotient_prodIrr (fun i => (hL i).hasSupport) σ.irred hsub
  have he : ∑ i, (Δ i).ms = chars ξ hξ :=
    GlobalTheory.CompanionTheory.Hypotheses₂.TD.hasSupport_unique hG GlobalTheory.Laid.bzfin_holds hs2
      (hs.of_equiv (IrrGL.equivOf σ.ρ σ.smooth σ.irred).symm)
  refine ⟨chars ξ hξ, hs, fun z hz => ?_, fun a ha b hb e => ?_⟩
  · obtain ⟨j, -, rfl⟩ := Multiset.mem_map.1 hz
    rfl
  · obtain ⟨j, -, hj⟩ := Multiset.mem_map.1 hb
    rw [← he] at ha hb
    obtain ⟨i, -, hi⟩ := Multiset.mem_sum.1 ha
    obtain ⟨i', -, hi'⟩ := Multiset.mem_sum.1 hb
    have ea : a = (Δ i).first := by
      have := Segment.mem_ms.1 hi
      rwa [carrier_of_len (hlen i)] at this
    have eb : b = (Δ i').first := by
      have := Segment.mem_ms.1 hi'
      rwa [carrier_of_len (hlen i')] at this
    subst ea
    by_cases hii : i = i'
    · subst hii
      rw [← eb] at e
      subst hj
      exact ofChar_ne_nu _ _ e
    · exact hun i i' hii (linked_of_len (hlen i) (hlen i') (ξ j) (hξ j) (eb ▸ hj.symm) (eb ▸ e))

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

/- English proof (translation)
Introduce `σ hσ` and use `plainTor_of_sph hn v σ B (((satLocFree F n v σ).2 _ π.finPart (UpperTheory.V.Af.RealLocalComponent.isotypic π v σ hσ) B).1 hB) (isGeneric_of_isLocCompR n π v σ hσ)`.
-/
theorem plainAtR_of_hasSat {n : ℕ} (hn : 1 ≤ n) (π : TR.CuspSub F n) (v : HeightOneSpectrum (𝓞 F)) (B : Multiset ℂˣ)
    (hB : π.HasSat v B) : PlainAtR π v := fun σ hσ =>
  plainTor_of_sph hn v σ B (((satLocFree F n v σ).2 _ π.finPart (UpperTheory.V.Af.RealLocalComponent.isotypic π v σ hσ) B).1 hB)
    (isGeneric_of_isLocCompR n π v σ hσ)

end UpperTheory.V.Z.Win.Birth
