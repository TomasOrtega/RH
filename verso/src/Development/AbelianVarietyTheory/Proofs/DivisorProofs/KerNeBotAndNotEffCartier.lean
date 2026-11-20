import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits
open ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R

noncomputable section
namespace GlobalTheory.NotCartier

/- English proof (translation)
Use `haveI := IsLocallyNoetherian.component_noetherian V`. Establish `hV : IsAffineOpen V.1` using `V.2`. Set `p` to `hV.primeIdealOf ⟨x, hxV⟩`. Set `_ : Algebra Γ(X, V.1) (X.presheaf.stalk x)` to `TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩`. Establish `hloc` using `hV.isLocalization_stalk ⟨x, hxV⟩`.

Establish `hp : hV.fromSpec p = x` using `hV.fromSpec_primeIdealOf ⟨x, hxV⟩`. Establish `hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal`. Introduce `q`. Establish `hqV : hV.fromSpec q ∈ V.1` using `(Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩`. Rewrite using `[Scheme.IdealSheafData.mem_support_iff_of_mem hqV]`.

Express the relevant statement in the definitionally equal form `q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _`. Rewrite using `[hV.fromSpec_preimage_zeroLocus]`. Conclude with `Iff.rfl`. Establish `hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes`. Use `⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩` and prove the remaining obligations.

Set `y : PrimeSpectrum Γ(X, V.1)` to `⟨q, hq.1⟩`. Establish `hsp : hV.fromSpec y ⤳ x`. Use `((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous` as an intermediate fact. Rewrite `this` using `[hp]`. Then use the resulting hypothesis. Establish `hyx : hV.fromSpec y = hV.fromSpec p` using `(hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm`.

Use `congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)` as an intermediate fact. Conclude with `le_of_eq this.symm`. Rewrite using `[IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]`. Conclude with `Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem` after adjusting the coercions.
-/
theorem ringKrullDim_stalk_le_one {X : Scheme.{0}} [IsLocallyNoetherian X] (J : X.IdealSheafData) (x : X)
    (hx : x ∈ J.support) (hmin : ∀ z ∈ J.support, z ⤳ x → z = x) (V : X.affineOpens) (hxV : x ∈ V.1)
    (hP : (J.ideal V).IsPrincipal) : ringKrullDim (X.presheaf.stalk x) ≤ 1 := by
  haveI := IsLocallyNoetherian.component_noetherian V
  have hV : IsAffineOpen V.1 := V.2
  let p := hV.primeIdealOf ⟨x, hxV⟩
  let _ : Algebra Γ(X, V.1) (X.presheaf.stalk x) := TopCat.Presheaf.algebra_section_stalk X.presheaf ⟨x, hxV⟩
  have hloc := hV.isLocalization_stalk ⟨x, hxV⟩
  have hp : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hsupp : ∀ q : Spec Γ(X, V.1), hV.fromSpec q ∈ J.support ↔ J.ideal V ≤ q.asIdeal := by
    intro q
    have hqV : hV.fromSpec q ∈ V.1 := (Set.ext_iff.1 hV.range_fromSpec _).1 ⟨q, rfl⟩
    rw [Scheme.IdealSheafData.mem_support_iff_of_mem hqV]
    change q ∈ hV.fromSpec ⁻¹' X.zeroLocus (J.ideal V : Set Γ(X, V.1)) ↔ _
    rw [hV.fromSpec_preimage_zeroLocus]
    exact Iff.rfl
  have hmem : p.asIdeal ∈ (J.ideal V).minimalPrimes := by
    refine ⟨⟨p.isPrime, (hsupp p).1 (hp ▸ hx)⟩, fun q hq hqp => ?_⟩
    let y : PrimeSpectrum Γ(X, V.1) := ⟨q, hq.1⟩
    have hsp : hV.fromSpec y ⤳ x := by
      have := ((PrimeSpectrum.le_iff_specializes y p).1 hqp).map hV.fromSpec.continuous
      rwa [hp] at this
    have hyx : hV.fromSpec y = hV.fromSpec p := (hmin _ ((hsupp y).2 hq.2) hsp).trans hp.symm
    have := congrArg PrimeSpectrum.asIdeal (hV.fromSpec.isOpenEmbedding.injective hyx)
    exact le_of_eq this.symm
  rw [IsLocalization.AtPrime.ringKrullDim_eq_height p.asIdeal (X.presheaf.stalk x)]
  exact_mod_cast Ideal.height_le_one_of_isPrincipal_of_mem_minimalPrimes _ _ hmem

end GlobalTheory.NotCartier

namespace GlobalTheory.NotCartier

/- English proof (translation)
Introduce `W Y _ _ i _ hdim`. Use `set y := i (genericPoint W) with hy`. Establish `hsub : (i.ker.support : Set Y) ⊆ closure {y}`. Rewrite using `[Scheme.Hom.support_ker]`. Use `closure_minimal ?_ isClosed_closure` and prove the remaining obligations.

Introduce and unpack `_ ⟨w, rfl⟩`. Establish `hw : w ∈ closure {genericPoint W}`. Rewrite using `[(genericPoint_spec W).def]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)`.

Establish `hyS : y ∈ i.ker.support`. Rewrite using `[← SetLike.mem_coe, Scheme.Hom.support_ker]`. Conclude with `subset_closure ⟨_, rfl⟩`. Establish `hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y` using `fun z hz hzy => (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq`. Establish `hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1` using `fun h => by`.

Use `hdim.trans h` as an intermediate fact. Conclude with `absurd this (by decide)`. Use `⟨fun hbot => ?_, fun U hyU hC => ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨V, hV, rfl⟩, hyV, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ`. Use `hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)` and prove the remaining obligations.

Rewrite using `[hbot, Scheme.IdealSheafData.ideal_bot]`. Conclude with `bot_isPrincipal`. Set `x : U.toScheme` to `⟨y, hyU⟩`. Take `⟨V, f, hxV, -, hf⟩` from `hC x`. Establish `hxS : x ∈ (i.ker.comap U.ι).support`.

Rewrite using `[Scheme.IdealSheafData.support_comap]`. Conclude with `hyS`. Establish `hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x`. Introduce `z hz hzx`. Rewrite `hz` using `[Scheme.IdealSheafData.support_comap]`.

Conclude with `Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))`. Establish `h1` using `ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩`. Rewrite `h1` using `[← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv]`. Conclude with `hlt h1`.
-/
theorem ker_ne_bot_and_not_effCartier : ∀ {W Y : Scheme.{0}} [IsIntegral W] [IsLocallyNoetherian Y] (i : W ⟶ Y)
    [IsClosedImmersion i], 2 ≤ ringKrullDim (Y.presheaf.stalk (i (genericPoint W))) →
    i.ker ≠ ⊥ ∧ ∀ U : Y.Opens, i (genericPoint W) ∈ U → ¬ FinalTheorems.EffCartier (i.ker.comap U.ι) := by
  intro W Y _ _ i _ hdim
  set y := i (genericPoint W) with hy
  have hsub : (i.ker.support : Set Y) ⊆ closure {y} := by
    rw [Scheme.Hom.support_ker]
    refine closure_minimal ?_ isClosed_closure
    rintro _ ⟨w, rfl⟩
    have hw : w ∈ closure {genericPoint W} := by
      rw [(genericPoint_spec W).def]; trivial
    exact specializes_iff_mem_closure.1 ((specializes_iff_mem_closure.2 hw).map i.continuous)
  have hyS : y ∈ i.ker.support := by
    rw [← SetLike.mem_coe, Scheme.Hom.support_ker]; exact subset_closure ⟨_, rfl⟩
  have hmin : ∀ z ∈ i.ker.support, z ⤳ y → z = y := fun z hz hzy =>
    (hzy.antisymm (specializes_iff_mem_closure.2 (hsub hz))).eq
  have hlt : ¬ ringKrullDim (Y.presheaf.stalk y) ≤ 1 := fun h => by
    have := hdim.trans h
    exact absurd this (by decide)
  refine ⟨fun hbot => ?_, fun U hyU hC => ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hyV, -⟩ :=
      Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ y) isOpen_univ
    refine hlt (ringKrullDim_stalk_le_one i.ker y hyS hmin ⟨V, hV⟩ hyV ?_)
    rw [hbot, Scheme.IdealSheafData.ideal_bot]
    exact bot_isPrincipal
  · let x : U.toScheme := ⟨y, hyU⟩
    obtain ⟨V, f, hxV, -, hf⟩ := hC x
    have hxS : x ∈ (i.ker.comap U.ι).support := by
      rw [Scheme.IdealSheafData.support_comap]; exact hyS
    have hminU : ∀ z ∈ (i.ker.comap U.ι).support, z ⤳ x → z = x := by
      intro z hz hzx
      rw [Scheme.IdealSheafData.support_comap] at hz
      exact Subtype.ext (hmin _ hz (hzx.map U.ι.continuous))
    have h1 := ringKrullDim_stalk_le_one _ x hxS hminU V hxV ⟨⟨f, hf⟩⟩
    rw [← ringKrullDim_eq_of_ringEquiv (asIso (U.ι.stalkMap x)).commRingCatIsoToRingEquiv] at h1
    exact hlt h1

end GlobalTheory.NotCartier
