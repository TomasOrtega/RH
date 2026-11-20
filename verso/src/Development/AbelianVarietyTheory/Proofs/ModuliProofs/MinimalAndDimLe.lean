import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.AbProj
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

namespace GlobalTheory.ZM.FullLevel

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Take `⟨N, i, hi, hq, rfl⟩` from `h`. Use `_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N` as an intermediate fact. Use `infer_instance`.
-/
theorem _root_.GlobalTheory.ZM.FullLevel.lft_of_qproj {R : Type} [CommRing R] {X : Scheme.{0}}
    {f : X ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R} (h : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsQProjOver f) :
    LocallyOfFiniteType f := by
  obtain ⟨N, i, hi, hq, rfl⟩ := h
  have := _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.isProper_str R N
  infer_instance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
/- English proof (translation)
Establish `hle : ∀ a b, f a ≤ f b ↔ a ≤ b` using `fun a b => by`. Rewrite using `[PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes, hf.isInducing.specializes_iff]`. Use `Order.krullDim_le_of_strictMono (fun a => ⟨f a.1, ?_⟩) ?_` and prove the remaining obligations. Establish `ha : p ≤ a.1`. Use `a.2` as an intermediate fact.

Rewrite `this` using `[PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]`. Conclude with `this`. Rewrite using `[PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]`. Conclude with `(hle p a.1).2 ha`. Use `Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)` and prove the remaining obligations.

Conclude with `(hle a.1 b.1).2 hab`. Conclude with `Subtype.ext (hf.injective (congrArg Subtype.val hab))`.
-/
private theorem krullDim_zeroLocus_le_of_isEmbedding {S T : Type} [CommRing S] [CommRing T]
    (f : PrimeSpectrum S → PrimeSpectrum T) (hf : Topology.IsEmbedding f) (p : PrimeSpectrum S) :
    Order.krullDim (PrimeSpectrum.zeroLocus (p.asIdeal : Set S)) ≤
      Order.krullDim (PrimeSpectrum.zeroLocus ((f p).asIdeal : Set T)) := by
  have hle : ∀ a b, f a ≤ f b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hf.isInducing.specializes_iff]
  refine Order.krullDim_le_of_strictMono (fun a => ⟨f a.1, ?_⟩) ?_
  · have ha : p ≤ a.1 := by
      have := a.2
      rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe] at this
      exact this
    rw [PrimeSpectrum.mem_zeroLocus, SetLike.coe_subset_coe]
    exact (hle p a.1).2 ha
  · refine Monotone.strictMono_of_injective (fun a b hab => ?_) (fun a b hab => ?_)
    · exact (hle a.1 b.1).2 hab
    · exact Subtype.ext (hf.injective (congrArg Subtype.val hab))

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Establish `hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors o)`. Set `pr` to `pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))`. Establish `hpr : Topology.IsEmbedding pr` using `IsPreimmersion.isEmbedding pr`. Set `y₀ : PrimeSpectrum R` to `⟨q, hq.1.1⟩`. Take `⟨O, hO, hOx⟩` from `hpr.isInducing.isOpen_iff.1 x.isOpenEmbedding.isOpen_range`.

Establish `hyO : pr (x y₀) ∈ O`. Establish `: x y₀ ∈ pr ⁻¹' O` using `hOx ▸ ⟨y₀, rfl⟩`. Conclude with `this`. Take `⟨V, hV, hyV, hVO⟩` from `TopologicalSpace.Opens.isBasis_iff_nbhd.1 U.isBasis_affineOpens (show pr (x y₀) ∈ (⟨O, hO⟩ : TopologicalSpace.Opens U) from hyO)`. Establish `hVa : IsAffineOpen V` using `hV`.

Set `A : Type` to `Γ(U, V)`. Set `j : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ U` to `hVa.fromSpec`. Use `haveI : IsOpenImmersion j := hVa.isOpenImmersion_fromSpec`. Use `letI : Algebra o A := (Spec.preimage (j ≫ s)).hom.toAlgebra`. Establish `hjs : j ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o A)`.

Rewrite using `[RingHom.algebraMap_toAlgebra]`. Simplify using `[_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]`. Establish `hbound` using `h A j inferInstance hjs`. Set `e : A ⊗[o] K ≃ₐ[o] FractionRing o ⊗[o] A` to `(Algebra.TensorProduct.comm o A K).trans (Algebra.TensorProduct.congr (IsLocalization.algEquiv (nonZeroDivisors o) K (FractionRing o)) AlgEquiv.refl)`. Set `I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing o ⊗[o] A) ≅ pullback j pr` to `asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom) ≪≫ (pullbackSpecIso o A K).symm ≪≫ (pullback.congrHom hjs rfl).symm ≪≫ (pullbackRightPullbackFstIso s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) j).symm`.

Set `F` to `I.hom ≫ pullback.snd j pr`. Establish `hF : ∀ w, F w = pullback.snd j pr (I.hom w)` using `fun w => rfl`. Establish `hrange : Set.range F ⊆ Set.range x`. Introduce and unpack `_ ⟨w, rfl⟩`. Rewrite using `[← hOx]`.

Establish `hmem : pullback.snd j pr (I.hom w) ∈ Set.range (pullback.snd j pr)` using `⟨_, rfl⟩`. Rewrite `hmem` using `[IsOpenImmersion.range_pullbackSnd]`. Establish `hmem' : pr (pullback.snd j pr (I.hom w)) ∈ j.opensRange` using `hmem`. Rewrite `hmem'` using `[hVa.opensRange_fromSpec]`. Use `show pr (F w) ∈ O`.

Rewrite using `[hF]`. Conclude with `hVO hmem'`. Establish `hy : x y₀ ∈ Set.range F`. Establish `: x y₀ ∈ Set.range (pullback.snd j pr)`. Rewrite using `[IsOpenImmersion.range_pullbackSnd]`.

Use `show pr (x y₀) ∈ j.opensRange`. Rewrite using `[hVa.opensRange_fromSpec]`. Conclude with `hyV`. Take `⟨p, hp⟩` from `this`. Use `⟨I.inv p, ?_⟩` and prove the remaining obligations.

Use `show (I.inv ≫ I.hom ≫ pullback.snd j pr) p = _`. Rewrite using `[Iso.inv_hom_id_assoc, hp]`. Take `⟨z, hz⟩` from `hy`. Set `g` to `IsOpenImmersion.lift x F hrange`. Establish `hg : g ≫ x = F` using `IsOpenImmersion.lift_fac x F hrange`.

Use `haveI : IsOpenImmersion g := by haveI : IsOpenImmersion (g ≫ x) := hg ▸ inferInstance`. Conclude with `IsOpenImmersion.of_comp g x`. Set `gf : PrimeSpectrum (FractionRing o ⊗[o] A) → PrimeSpectrum R` to `fun a => g a`. Establish `hgemb : Topology.IsEmbedding gf` using `g.isOpenEmbedding.isEmbedding`. Establish `hgz : gf z = y₀` using `x.isOpenEmbedding.injective (by show x (g z) = x y₀`.

Rewrite using `[← Scheme.Hom.comp_apply, hg, hz])`. Establish `hle : ∀ a b, gf a ≤ gf b ↔ a ≤ b` using `fun a b => by`. Rewrite using `[PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes, hgemb.isInducing.specializes_iff]`. Establish `hzmin : z.asIdeal ∈ minimalPrimes (FractionRing o ⊗[o] A)`. Use `⟨⟨z.isPrime, bot_le⟩, fun p' hp' hp'le => ?_⟩` and prove the remaining obligations.

Set `w : PrimeSpectrum (FractionRing o ⊗[o] A)` to `⟨p', hp'.1⟩`. Establish `hwz : w ≤ z` using `hp'le`. Establish `h1 : gf w ≤ y₀` using `hgz ▸ (hle w z).2 hwz`. Establish `h2 : y₀ ≤ gf w` using `hq.2 ⟨(gf w).isPrime, bot_le⟩ h1`. Conclude with `(hle z w).1 (hgz ▸ h2)`.

Establish `hq' : (gf z).asIdeal = q` using `congrArg PrimeSpectrum.asIdeal hgz`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem _root_.GlobalTheory.ZM.FullLevel.dim_generic_chart {o K : Type} [CommRing o] [IsDomain o] [Field K]
    [Algebra o K] [IsFractionRing o K]
    {U : Scheme.{0}} (s : U ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp o) (d : WithBot ℕ∞)
    (h : ∀ (R : Type) [CommRing R] [Algebra o R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ U), IsOpenImmersion x →
      x ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o R) →
      ∀ q ∈ minimalPrimes (FractionRing o ⊗[o] R), d ≤ ringKrullDim ((FractionRing o ⊗[o] R) ⧸ q))
    (R : Type) [CommRing R] (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp R ⟶ pullback s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)))
    [IsOpenImmersion x]
    (q : Ideal R) (hq : q ∈ minimalPrimes R) : d ≤ ringKrullDim (R ⧸ q) := by
  classical
  have hpre : IsPreimmersion (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) :=
    IsPreimmersion.of_isLocalization (nonZeroDivisors o)
  let pr := pullback.fst s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K))
  have hpr : Topology.IsEmbedding pr := IsPreimmersion.isEmbedding pr
  let y₀ : PrimeSpectrum R := ⟨q, hq.1.1⟩
  obtain ⟨O, hO, hOx⟩ := hpr.isInducing.isOpen_iff.1 x.isOpenEmbedding.isOpen_range
  have hyO : pr (x y₀) ∈ O := by
    have : x y₀ ∈ pr ⁻¹' O := hOx ▸ ⟨y₀, rfl⟩
    exact this
  obtain ⟨V, hV, hyV, hVO⟩ := TopologicalSpace.Opens.isBasis_iff_nbhd.1 U.isBasis_affineOpens
    (show pr (x y₀) ∈ (⟨O, hO⟩ : TopologicalSpace.Opens U) from hyO)
  have hVa : IsAffineOpen V := hV
  let A : Type := Γ(U, V)
  let j : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp A ⟶ U := hVa.fromSpec
  haveI : IsOpenImmersion j := hVa.isOpenImmersion_fromSpec
  letI : Algebra o A := (Spec.preimage (j ≫ s)).hom.toAlgebra
  have hjs : j ≫ s = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o A) := by
    rw [RingHom.algebraMap_toAlgebra]
    simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]
  have hbound := h A j inferInstance hjs
  let e : A ⊗[o] K ≃ₐ[o] FractionRing o ⊗[o] A :=
    (Algebra.TensorProduct.comm o A K).trans
      (Algebra.TensorProduct.congr (IsLocalization.algEquiv (nonZeroDivisors o) K (FractionRing o))
        AlgEquiv.refl)
  let I : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (FractionRing o ⊗[o] A) ≅ pullback j pr :=
    asIso (Spec.map e.toRingEquiv.toCommRingCatIso.hom) ≪≫ (pullbackSpecIso o A K).symm ≪≫
      (pullback.congrHom hjs rfl).symm ≪≫ (pullbackRightPullbackFstIso s (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (algebraMap o K)) j).symm
  let F := I.hom ≫ pullback.snd j pr
  have hF : ∀ w, F w = pullback.snd j pr (I.hom w) := fun w => rfl
  have hrange : Set.range F ⊆ Set.range x := by
    rintro _ ⟨w, rfl⟩
    rw [← hOx]
    have hmem : pullback.snd j pr (I.hom w) ∈ Set.range (pullback.snd j pr) := ⟨_, rfl⟩
    rw [IsOpenImmersion.range_pullbackSnd] at hmem
    have hmem' : pr (pullback.snd j pr (I.hom w)) ∈ j.opensRange := hmem
    rw [hVa.opensRange_fromSpec] at hmem'
    show pr (F w) ∈ O
    rw [hF]
    exact hVO hmem'
  have hy : x y₀ ∈ Set.range F := by
    have : x y₀ ∈ Set.range (pullback.snd j pr) := by
      rw [IsOpenImmersion.range_pullbackSnd]
      show pr (x y₀) ∈ j.opensRange
      rw [hVa.opensRange_fromSpec]
      exact hyV
    obtain ⟨p, hp⟩ := this
    refine ⟨I.inv p, ?_⟩
    show (I.inv ≫ I.hom ≫ pullback.snd j pr) p = _
    rw [Iso.inv_hom_id_assoc, hp]
  obtain ⟨z, hz⟩ := hy
  let g := IsOpenImmersion.lift x F hrange
  have hg : g ≫ x = F := IsOpenImmersion.lift_fac x F hrange
  haveI : IsOpenImmersion g := by
    haveI : IsOpenImmersion (g ≫ x) := hg ▸ inferInstance
    exact IsOpenImmersion.of_comp g x
  let gf : PrimeSpectrum (FractionRing o ⊗[o] A) → PrimeSpectrum R := fun a => g a
  have hgemb : Topology.IsEmbedding gf := g.isOpenEmbedding.isEmbedding
  have hgz : gf z = y₀ := x.isOpenEmbedding.injective (by
    show x (g z) = x y₀
    rw [← Scheme.Hom.comp_apply, hg, hz])
  have hle : ∀ a b, gf a ≤ gf b ↔ a ≤ b := fun a b => by
    rw [PrimeSpectrum.le_iff_specializes, PrimeSpectrum.le_iff_specializes,
      hgemb.isInducing.specializes_iff]
  have hzmin : z.asIdeal ∈ minimalPrimes (FractionRing o ⊗[o] A) := by
    refine ⟨⟨z.isPrime, bot_le⟩, fun p' hp' hp'le => ?_⟩
    let w : PrimeSpectrum (FractionRing o ⊗[o] A) := ⟨p', hp'.1⟩
    have hwz : w ≤ z := hp'le
    have h1 : gf w ≤ y₀ := hgz ▸ (hle w z).2 hwz
    have h2 : y₀ ≤ gf w := hq.2 ⟨(gf w).isPrime, bot_le⟩ h1
    exact (hle z w).1 (hgz ▸ h2)
  have hq' : (gf z).asIdeal = q := congrArg PrimeSpectrum.asIdeal hgz
  calc d ≤ ringKrullDim ((FractionRing o ⊗[o] A) ⧸ z.asIdeal) := hbound _ hzmin
    _ = Order.krullDim (PrimeSpectrum.zeroLocus (z.asIdeal : Set (FractionRing o ⊗[o] A))) :=
      ringKrullDim_quotient _
    _ ≤ Order.krullDim (PrimeSpectrum.zeroLocus ((gf z).asIdeal : Set R)) :=
      krullDim_zeroLocus_le_of_isEmbedding gf hgemb z
    _ = ringKrullDim (R ⧸ q) := by rw [hq', ringKrullDim_quotient]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
The claim follows from `(RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance`.
-/
theorem _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom {k K : Type} [Field k] [CharZero k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp K ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : CharZero K :=
  (RingHom.charZero_iff (Spec.preimage x).hom.injective).1 inferInstance

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in
/- English proof (translation)
Use `⟨2, le_bot_iff.1 ?_⟩` and prove the remaining obligations. Rewrite using `[pow_two, Ideal.mul_le]`. Introduce `r hr s hs`. Rewrite `hr`, `hs` using `[RingHom.mem_ker]`. Simplify using `only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hr hs`.

Rewrite using `[Ideal.mem_bot]`. Apply the tactic sequence `ext <;> simp [hr, hs]`.
-/
private theorem isNilpotent_ker_fstHom_dualNumber {K : Type} [Field K] :
    IsNilpotent (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) := by
  refine ⟨2, le_bot_iff.1 ?_⟩
  rw [pow_two, Ideal.mul_le]
  intro r hr s hs
  rw [RingHom.mem_ker] at hr hs
  simp only [AlgHom.toRingHom_eq_coe, RingHom.coe_coe, TrivSqZeroExt.fstHom_apply] at hr hs
  rw [Ideal.mem_bot]
  ext <;> simp [hr, hs]

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField in
open scoped CategoryTheory.Obj TensorProduct in

/- English proof (translation)
Establish `hK : CharZero K` using `_root_.GlobalTheory.ZM.FullLevel.charZero_of_hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ x)`. Use `haveI : Algebra.IsSeparable ℚ k := Algebra.IsAlgebraic.isSeparable_of_perfectField`. Use `haveI : Algebra.FormallyUnramified ℚ k := Algebra.FormallyUnramified.of_isSeparable ℚ k`. Take `⟨φ, rfl⟩ : ∃ φ : k →+* DualNumber K, x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ` from `⟨(Spec.preimage x).hom, by simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]⟩`. Set `ψ : k →+* DualNumber K` to `(algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)`.

Establish `hψ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ`. Simplify using `only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ψ, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[hψ]`. Use `congr 1`.

Establish `key` using `Algebra.FormallyUnramified.ext (R := ℚ) (A := k) (B := DualNumber K) (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) isNilpotent_ker_fstHom_dualNumber (g₁ := φ.toRatAlgHom) (g₂ := ψ.toRatAlgHom) ?_`. Conclude with `congrArg AlgHom.toRingHom key`. Introduce `a`. Rewrite using `[Ideal.Quotient.eq, RingHom.mem_ker]`. Simplify using `[ψ, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
theorem _root_.GlobalTheory.ZM.FullLevel.eq_constPt {k K : Type} [Field k] [CharZero k]
    [Algebra.IsAlgebraic ℚ k] [Field K]
    (x : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp (DualNumber K) ⟶ _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp k) : x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt x := by
  have hK : CharZero K :=
    _root_.GlobalTheory.ZM.FullLevel.charZero_of_hom (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap (TrivSqZeroExt.fstHom K K K).toRingHom ≫ x)
  haveI : Algebra.IsSeparable ℚ k := Algebra.IsAlgebraic.isSeparable_of_perfectField
  haveI : Algebra.FormallyUnramified ℚ k := Algebra.FormallyUnramified.of_isSeparable ℚ k
  obtain ⟨φ, rfl⟩ : ∃ φ : k →+* DualNumber K, x = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ :=
    ⟨(Spec.preimage x).hom, by simp [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap]⟩
  let ψ : k →+* DualNumber K :=
    (algebraMap K (DualNumber K)).comp ((TrivSqZeroExt.fstHom K K K).toRingHom.comp φ)
  have hψ : _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt (_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap φ) = _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap ψ := by
    simp only [_root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.constPt, _root_.ReciprocityTheory.ChartRestriction.G.Geo.Tor.spMap, ψ, ← Spec.map_comp]; rfl
  rw [hψ]
  congr 1
  have key := Algebra.FormallyUnramified.ext (R := ℚ) (A := k) (B := DualNumber K)
    (RingHom.ker (TrivSqZeroExt.fstHom K K K).toRingHom) isNilpotent_ker_fstHom_dualNumber
    (g₁ := φ.toRatAlgHom) (g₂ := ψ.toRatAlgHom) ?_
  · exact congrArg AlgHom.toRingHom key
  · intro a
    rw [Ideal.Quotient.eq, RingHom.mem_ker]
    simp [ψ, TrivSqZeroExt.algebraMap_eq_inl]

end GlobalTheory.ZM.FullLevel
