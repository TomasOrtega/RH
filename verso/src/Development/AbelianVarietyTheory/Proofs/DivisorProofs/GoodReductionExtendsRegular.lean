import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SemiposAtOfPositive
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NormsAtOfNorms
import Development.AbelianVarietyTheory.Proofs.CoherentCohomologyProofs.ExistsLinearMapMultilinearMapBaseChange
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularOfIntegralValuationBound
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsometricOfSameNorms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinsumLifts
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsIsRatSecOfPull

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj GlobalTheory GlobalTheory.Cartier GlobalTheory.CechPic GlobalTheory.ArInt GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.Mean4O GlobalTheory.CoverNorm GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.VertForm GlobalTheory.TrivFlag GlobalTheory.CovTop GlobalTheory.CovHt GlobalTheory.TrueCx
open scoped Classical

namespace GlobalTheory.Mean4O.Cover.RegOverP

/- English proof (translation)
Establish `hc : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk v.asIdeal)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 h`. Use `haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top`. Break down `hp.eq_one_or_self_of_dvd _ (ringChar.dvd hc) with h1 | h1` into its components or cases.

Conclude with `absurd h1 CharP.ringChar_ne_one`. Conclude with `h1`.
-/
theorem residueCharacteristic_eq_of_mem {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)} {p : ℕ} (hp : p.Prime)
    (h : (p : 𝓞 F) ∈ v.asIdeal) : resP v = p := by
  have hc : ((p : ℕ) : 𝓞 F ⧸ v.asIdeal) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk v.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 h
  haveI : Nontrivial (𝓞 F ⧸ v.asIdeal) := Ideal.Quotient.nontrivial_iff.2 v.isPrime.ne_top
  rcases hp.eq_one_or_self_of_dvd _ (ringChar.dvd hc) with h1 | h1
  · exact absurd h1 CharP.ringChar_ne_one
  · exact h1

/- English proof (translation)
Establish `h1` using `Scheme.mem_basicOpen V.X (U := ⊤) (n : Γ(V.X, ⊤)) x trivial`. Rewrite `h1` using `[map_natCast]`. Rewrite using `[← h1]`. Establish `h2` using `Scheme.preimage_basicOpen V.p (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv (n : 𝓞 F))`. Rewrite `h2` using `[basicOpen_eq_of_affine, map_natCast, map_natCast]`.

Conclude with `(SetLike.ext_iff.1 h2 x).symm.trans Iff.rfl`.
-/
theorem isUnit_natCast_stalk_iff {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (x : V.X) (n : ℕ) :
    IsUnit (n : V.X.presheaf.stalk x) ↔ (n : 𝓞 F) ∉ (V.p x).asIdeal := by
  have h1 := Scheme.mem_basicOpen V.X (U := ⊤) (n : Γ(V.X, ⊤)) x trivial
  rw [map_natCast] at h1
  rw [← h1]
  have h2 := Scheme.preimage_basicOpen V.p (U := ⊤) ((Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv (n : 𝓞 F))
  rw [basicOpen_eq_of_affine, map_natCast, map_natCast] at h2
  exact (SetLike.ext_iff.1 h2 x).symm.trans Iff.rfl

open GlobalTheory.TrueGeo.HorizPt in

/- English proof (translation)
Use `V.ar.flat` as an intermediate fact. Establish `: IsProper V.p`. Take `⟨m, c, hc, hm⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) m` as an intermediate fact. Rewrite using `[← hm]`.

Use `infer_instance`. Establish `: Nonempty U` using `⟨⟨z, hzU⟩⟩`. Establish `: CharZero Γ(V.X, U)` using `charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU`. Set `_ : Algebra (𝓞 F) Γ(V.X, U)` to `(GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra`. Establish `: Algebra.FiniteType (𝓞 F) Γ(V.X, U)` using `RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top) (RingHom.FiniteType.of_surjective _ (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)`.

Establish `hb : ∀ (x : PrimeSpectrum Γ(V.X, U)) (a : Γ(V.X, U)), hU.fromSpec x ∈ V.X.basicOpen a ↔ a ∉ x.asIdeal`. Introduce `x a`. Express the relevant statement in the definitionally equal form `x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen a ↔ _`. Rewrite using `[hU.fromSpec_preimage_basicOpen]`. Both sides reduce to the same expression.

Establish `hz' : hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) = z` using `hU.fromSpec_primeIdealOf ⟨z, hzU⟩`. Establish `hp : g ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal`. Assume the negation of the conclusion as `hc`. Establish `h1` using `(hb _ _).2 hc`. Rewrite `h1` using `[hz']`.

Conclude with `hzg h1`. Establish `hnp : (n : Γ(V.X, U)) ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal`. Assume the negation of the conclusion as `hc`. Establish `h1` using `(hb _ _).2 hc`. Rewrite `h1` using `[hz', Scheme.mem_basicOpen V.X _ z hzU, map_natCast]`.

Conclude with `hn h1`. Take `⟨𝔪, h𝔪, hle'⟩` from `Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top`. Take `⟨v, e, φ, h₁, h₂, h₃⟩` from `GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 (g * h) hgh`. Set `yt : Sp e.O ⟶ V.X` to `Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec`. Establish `hw : (spMap e.O.subtype ≫ yt) ≫ V.p = spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F)`.

Simplify using `only [yt, Category.assoc]`. Rewrite using `[fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]`. Use `congr 1`. Use extensionality with `a`. Conclude with `h₁ a`.

Establish `hy` using `V.pb.lift_fst _ _ hw`. Use `⟨v, e, V.pb.lift _ _ hw, yt, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `x _`. Conclude with `(Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩`. Introduce `hc`.

Use `(hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O)) g).1 hc ?_` and prove the remaining obligations. Use `hle' hp` as an intermediate fact. Rewrite `this` using `[← h₂]`. Conclude with `this`. Express the relevant statement in the definitionally equal form `(V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _`.

Rewrite using `[hy]`. Use `(hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype (IsLocalRing.closedPoint (AlgebraicClosure F)))) _).2 fun hc => h₃ ?_` and prove the remaining obligations. Establish `h' : ((φ (g * h) : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F)` using `hc`. Rewrite `h'` using `[IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot]`. Conclude with `Subtype.ext h'`.

Establish `h4 : φ (n : Γ(V.X, U)) ∈ IsLocalRing.maximalIdeal e.O`. Use `hle' hnp` as an intermediate fact. Rewrite `this` using `[← h₂]`. Conclude with `this`. Rewrite `h4` using `[map_natCast, ValuationSubring.valuation_lt_one_iff]`.

Establish `h5 : e.w (n : AlgebraicClosure F) < 1`. Rewrite using `[← GlobalTheory.TrueGeo.SmallSec.valuation_lt_one_iff]`. Simplify using `using h4`. Establish `h6 : e.w (algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F (n : 𝓞 F))) < 1`. Simplify using `using h5`.

Rewrite `h6` using `[e.w_alg]`. Conclude with `(v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).1 h6`.
-/
theorem exists_horizPt_over {F : Type} [Field F] [NumberField F] {Y : Var F} (V : Cover Y) (U : V.X.Opens)
    (hU : IsAffineOpen U) (z : V.X) (hzU : z ∈ U) (g h : Γ(V.X, U)) (hgh : g * h ≠ 0) (hzg : z ∉ V.X.basicOpen g)
    (n : ℕ) (hn : ¬ IsUnit (n : V.X.presheaf.stalk z)) :
    ∃ (v : HeightOneSpectrum (𝓞 F)) (e : Ext v) (y : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X),
      y ≫ V.π ≫ Y.str = spMap (algebraMap F (AlgebraicClosure F)) ∧ spMap e.O.subtype ≫ yt = y ≫ V.j ∧
      ⊤ ≤ yt ⁻¹ᵁ U ∧ yt (IsLocalRing.closedPoint e.O) ∉ V.X.basicOpen g ∧
      below (y ≫ V.j) ∈ V.X.basicOpen (g * h) ∧ (n : 𝓞 F) ∈ v.asIdeal := by
  have := V.ar.flat
  have : IsProper V.p := by
    obtain ⟨m, c, hc, hm⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) m
    rw [← hm]
    infer_instance
  have : Nonempty U := ⟨⟨z, hzU⟩⟩
  have : CharZero Γ(V.X, U) := charZero (V.p ≫ spMap (Int.castRingHom (𝓞 F))) hU
  let _ : Algebra (𝓞 F) Γ(V.X, U) := (GlobalTheory.TrueGeo.HorizPt.strHom V.p U).hom.toAlgebra
  have : Algebra.FiniteType (𝓞 F) Γ(V.X, U) :=
    RingHom.FiniteType.comp (V.p.finiteType_appLE (isAffineOpen_top _) hU le_top)
      (RingHom.FiniteType.of_surjective _
        (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of (𝓞 F))).inv).2)
  have hb : ∀ (x : PrimeSpectrum Γ(V.X, U)) (a : Γ(V.X, U)), hU.fromSpec x ∈ V.X.basicOpen a ↔ a ∉ x.asIdeal := by
    intro x a
    change x ∈ hU.fromSpec ⁻¹ᵁ V.X.basicOpen a ↔ _
    rw [hU.fromSpec_preimage_basicOpen]
    rfl
  have hz' : hU.fromSpec (hU.primeIdealOf ⟨z, hzU⟩) = z := hU.fromSpec_primeIdealOf ⟨z, hzU⟩
  have hp : g ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra hc
    have h1 := (hb _ _).2 hc
    rw [hz'] at h1
    exact hzg h1
  have hnp : (n : Γ(V.X, U)) ∈ (hU.primeIdealOf ⟨z, hzU⟩).asIdeal := by
    by_contra hc
    have h1 := (hb _ _).2 hc
    rw [hz', Scheme.mem_basicOpen V.X _ z hzU, map_natCast] at h1
    exact hn h1
  obtain ⟨𝔪, h𝔪, hle'⟩ := Ideal.exists_le_maximal _ (hU.primeIdealOf ⟨z, hzU⟩).isPrime.ne_top
  obtain ⟨v, e, φ, h₁, h₂, h₃⟩ := GlobalTheory.T.exists_ext_place_of_ne_zero_maximal F Γ(V.X, U) 𝔪 h𝔪 (g * h) hgh
  let yt : Sp e.O ⟶ V.X := Spec.map (CommRingCat.ofHom φ) ≫ hU.fromSpec
  have hw : (spMap e.O.subtype ≫ yt) ≫ V.p =
      spMap (algebraMap F (AlgebraicClosure F)) ≫ spMap (algebraMap (𝓞 F) F) := by
    simp only [yt, Category.assoc]
    rw [fromSpec_str, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp]
    congr 1
    ext a
    exact h₁ a
  have hy := V.pb.lift_fst _ _ hw
  refine ⟨v, e, V.pb.lift _ _ hw, yt, V.pb.lift_snd _ _ hw, hy.symm, ?_, ?_, ?_, ?_⟩
  · intro x _
    exact (Set.ext_iff.1 hU.range_fromSpec _).1 ⟨_, rfl⟩
  · intro hc
    refine (hb (PrimeSpectrum.comap φ (IsLocalRing.closedPoint e.O)) g).1 hc ?_
    have := hle' hp
    rw [← h₂] at this
    exact this
  · change (V.pb.lift _ _ hw ≫ V.j) (IsLocalRing.closedPoint (AlgebraicClosure F)) ∈ _
    rw [hy]
    refine (hb (PrimeSpectrum.comap φ (PrimeSpectrum.comap e.O.subtype
      (IsLocalRing.closedPoint (AlgebraicClosure F)))) _).2 fun hc => h₃ ?_
    have h' : ((φ (g * h) : e.O) : AlgebraicClosure F) ∈ IsLocalRing.maximalIdeal (AlgebraicClosure F) := hc
    rw [IsLocalRing.maximalIdeal_eq_bot, Ideal.mem_bot] at h'
    exact Subtype.ext h'
  · have h4 : φ (n : Γ(V.X, U)) ∈ IsLocalRing.maximalIdeal e.O := by
      have := hle' hnp
      rw [← h₂] at this
      exact this
    rw [map_natCast, ValuationSubring.valuation_lt_one_iff] at h4
    have h5 : e.w (n : AlgebraicClosure F) < 1 := by
      rw [← GlobalTheory.TrueGeo.SmallSec.valuation_lt_one_iff]
      simpa using h4
    have h6 : e.w (algebraMap F (AlgebraicClosure F) (algebraMap (𝓞 F) F (n : 𝓞 F))) < 1 := by
      simpa using h5
    rw [e.w_alg] at h6
    exact (v.adicAbv_coe_lt_one_iff (NumberField.HeightOneSpectrum.one_lt_absNorm_nnreal v) _).1 h6

open GlobalTheory.TrueGeo.RegCrit in

/- English proof (translation)
Introduce `F _ _ Y V p hp W hW U f hgen hval x hxU hx`. Establish `: IsProper V.p`. Take `⟨m, c, hc, hm⟩` from `V.ar.isProjOver`. Use `isProper_str (𝓞 F) m` as an intermediate fact. Rewrite using `[← hm]`.

Use `infer_instance`. Establish `: IsLocallyNoetherian V.X` using `LocallyOfFiniteType.isLocallyNoetherian V.p`. Assume the negation of the conclusion as `hreg`. Take `⟨z, hz, hzero⟩` from `GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg`. Establish `hf0 : f ≠ 0` using `fun h => hreg (h ▸ regAt_zero x)`.

Establish `hzU : z ∈ U` using `hz.mem_open U.isOpen hxU`. Establish `hzq : (V.p z).asIdeal ≠ ⊥`. Introduce `h`. Take `⟨z', rfl⟩` from `GlobalTheory.CoverNorm.Isom.mem_range_j V h`. Establish `h1` using `hzero.mul (hgen z' hzU)`.

Rewrite `h1` using `[inv_mul_cancel₀ hf0]`. Conclude with `(zeroAt_iff.1 h1).2 (unitAt_one _)`. Establish `hpx : (p : 𝓞 F) ∈ (V.p x).asIdeal`. Assume the negation of the conclusion as `hc`. Conclude with `hx ((isUnit_natCast_stalk_iff V x p).2 hc)`.

Establish `hle : (V.p z).asIdeal ≤ (V.p x).asIdeal` using `(PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous)`. Establish `hmax` using `Ideal.IsPrime.isMaximal (V.p z).isPrime hzq`. Establish `hpz : (p : 𝓞 F) ∈ (V.p z).asIdeal`. Rewrite using `[hmax.eq_of_le (V.p x).isPrime.ne_top hle]`. Conclude with `hpx`.

Establish `hnz : ¬ IsUnit (p : V.X.presheaf.stalk z)` using `fun h => (isUnit_natCast_stalk_iff V z p).1 h hpz`. Take `⟨W₀, hzW, g₀, hg₀⟩` from `hzero.regAt.exists_fnOf`. Establish `hzW' : z ∈ W₀ ⊓ U` using `⟨hzW, hzU⟩`. Take `⟨U₁, hU₁, hzU₁, hU₁W⟩` from `exists_isAffineOpen_mem_and_subset hzW'`. Establish `hU₁le : U₁ ≤ W₀` using `fun q hq => (hU₁W hq).1`.

Establish `: Nonempty U₁` using `⟨⟨z, hzU₁⟩⟩`. Take `⟨g, hg⟩ : ∃ g : Γ(V.X, U₁), ∀ h, fnOf _ h g = f⁻¹` from `⟨resG V.X hU₁le g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩`. Establish `hg0 : g ≠ 0` using `fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzU₁), h, map_zero])`. Establish `hzg : z ∉ V.X.basicOpen g` using `fun h => (zeroAt_iff.1 hzero).2 (hg (gen_mem hzU₁) ▸ (unitAt_fnOf_iff hzU₁ _ g).2 h)`. Use `haveI := CoverHt.isPreimmersion_j V`.

Use `set T : Set V.X := closure (V.j '' (V.π ⁻¹' (W : Set Y.X)ᶜ)) with hTdef`. Establish `hT : ∀ w : V.G, V.j w ∈ T ↔ V.π w ∉ W`. Establish `e1` using `(Scheme.Hom.isEmbedding V.j).closure_eq_preimage_closure_image (V.π ⁻¹' (W : Set Y.X)ᶜ)`. Rewrite `e1` using `[(W.isOpen.isClosed_compl.preimage V.π.continuous).closure_eq]`. Introduce `w`.

Conclude with `(Set.ext_iff.1 e1 w).symm`. Take `⟨w0, hw0⟩` from `V.π.surjective (genericPoint Y.X)`. Establish `hw0T : V.j w0 ∉ T` using `fun h => (hT w0).1 h (hw0 ▸ hW)`. Take `⟨u, huU, huT⟩` from `nonempty_preirreducible_inter U₁.isOpen isClosed_closure.isOpen_compl ⟨z, hzU₁⟩ ⟨_, hw0T⟩`. Take `⟨h, hhle, huh⟩` from `hU₁.exists_basicOpen_le (V := ⟨Tᶜ, isClosed_closure.isOpen_compl⟩) ⟨u, huT⟩ huU`.

Establish `hh0 : h ≠ 0`. Introduce and unpack `rfl`. Rewrite `huh` using `[Scheme.basicOpen_zero]`. Conclude with `huh`. Establish `hgh : g * h ≠ 0` using `mul_ne_zero hg0 hh0`.

Take `⟨v, e, y, yt, hy, hc, hWt, hn, hu, hpv⟩` from `exists_horizPt_over V U₁ hU₁ z hzU₁ g h hgh hzg p hnz`. Establish `hbelow : below (y ≫ V.π) ∈ W`. Establish `h1 : V.j (below y) ∉ T` using `hhle ((V.X.basicOpen_mul g h ▸ hu).2)`. Conclude with `not_not.1 fun h2 => h1 ((hT _).2 h2)`. Establish `hlev` using `hval v (residueCharacteristic_eq_of_mem hp hpv) e ⟨y ≫ V.π, by rw [Category.assoc]; exact hy⟩ hbelow y yt rfl hc (fun q hq => (hU₁W (hWt hq)).2)`.

Establish `hu' : below (y ≫ V.j) ∈ V.X.basicOpen g` using `(V.X.basicOpen_mul g h ▸ hu).1`. Establish `hb : below (y ≫ V.j) ∈ U₁` using `V.X.basicOpen_le g hu'`. Establish `ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ U₁` using `fun q _ => by`. Express the relevant statement in the definitionally equal form `(y ≫ V.j) q ∈ U₁`. Rewrite using `[← hc]`.

Conclude with `hWt (x := spMap e.O.subtype q) trivial`. Establish `hunit : UnitAt (below (y ≫ V.j)) f⁻¹` using `hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'`. Establish `hfu : UnitAt (below (y ≫ V.j)) f` using `inv_inv f ▸ hunit.inv`. Establish `hmul` using `OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt`. Establish `hone : valAt (y ≫ V.j) (1 : V.X.functionField) = 1`.

Use `OfModel.valAt_algebraMap (y ≫ V.j) 1` as an intermediate fact. Rewrite `this` using `[map_one, map_one]`. Then use the resulting hypothesis. Establish `hev` using `OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm) (U := U₁) (W := U₁) le_rfl ht hWt g`. Establish `hid : ((𝟙 V.X : V.X ⟶ V.X).appLE U₁ U₁ le_rfl).hom g = g`. Establish `: (𝟙 V.X : V.X ⟶ V.X).appLE U₁ U₁ le_rfl = 𝟙 _` using `(Category.id_comp _).trans (V.X.presheaf.map_id _)`.

Rewrite using `[this]`. Both sides reduce to the same expression. Rewrite `hev` using `[hid]`. Rewrite `hmul` using `[mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev]`. Use `hn ((isUnit_eval_iff yt hWt g).1 (isUnit_of_one_le e _ ?_))` and prove the remaining obligations.

Establish `h₁` using `congrArg e.w hmul`. Rewrite `h₁` using `[map_one, map_mul]`. Conclude with `h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hlev)`.
-/
theorem regAt_of_values_over : ∀ (F : Type) [Field F] [NumberField F] (Y : Var F) (V : Cover Y) (p : ℕ), p.Prime → ∀ (W : Y.X.Opens), genericPoint Y.X ∈ W → ∀ (U : V.X.Opens) (f : V.X.functionField), (∀ z : V.G, V.j z ∈ U → RegAt (V.j z) f) → (∀ v : HeightOneSpectrum (𝓞 F), resP v = p → ∀ (e : TrueGeo.Ext v) (y : AlgPt Y), below y.1 ∈ W → ∀ (z : Sp (AlgebraicClosure F) ⟶ V.G) (yt : Sp e.O ⟶ V.X), z ≫ V.π = y.1 → spMap e.O.subtype ≫ yt = z ≫ V.j → ⊤ ≤ yt ⁻¹ᵁ U → e.w (valAt (z ≫ V.j) f) ≤ 1) → ∀ x ∈ U, ¬ IsUnit (p : V.X.presheaf.stalk x) → RegAt x f := by
  intro F _ _ Y V p hp W hW U f hgen hval x hxU hx
  have : IsProper V.p := by
    obtain ⟨m, c, hc, hm⟩ := V.ar.isProjOver
    have := isProper_str (𝓞 F) m
    rw [← hm]
    infer_instance
  have : IsLocallyNoetherian V.X := LocallyOfFiniteType.isLocallyNoetherian V.p
  by_contra hreg
  obtain ⟨z, hz, hzero⟩ := GlobalTheory.T.exists_zero_of_inv_of_not_regular_normal V.X V.normal x f hreg
  have hf0 : f ≠ 0 := fun h => hreg (h ▸ regAt_zero x)
  have hzU : z ∈ U := hz.mem_open U.isOpen hxU

  have hzq : (V.p z).asIdeal ≠ ⊥ := by
    intro h
    obtain ⟨z', rfl⟩ := GlobalTheory.CoverNorm.Isom.mem_range_j V h
    have h1 := hzero.mul (hgen z' hzU)
    rw [inv_mul_cancel₀ hf0] at h1
    exact (zeroAt_iff.1 h1).2 (unitAt_one _)

  have hpx : (p : 𝓞 F) ∈ (V.p x).asIdeal := by
    by_contra hc
    exact hx ((isUnit_natCast_stalk_iff V x p).2 hc)
  have hle : (V.p z).asIdeal ≤ (V.p x).asIdeal :=
    (PrimeSpectrum.le_iff_specializes _ _).2 (hz.map V.p.continuous)
  have hmax := Ideal.IsPrime.isMaximal (V.p z).isPrime hzq
  have hpz : (p : 𝓞 F) ∈ (V.p z).asIdeal := by
    rw [hmax.eq_of_le (V.p x).isPrime.ne_top hle]
    exact hpx
  have hnz : ¬ IsUnit (p : V.X.presheaf.stalk z) := fun h => (isUnit_natCast_stalk_iff V z p).1 h hpz

  obtain ⟨W₀, hzW, g₀, hg₀⟩ := hzero.regAt.exists_fnOf
  have hzW' : z ∈ W₀ ⊓ U := ⟨hzW, hzU⟩
  obtain ⟨U₁, hU₁, hzU₁, hU₁W⟩ := exists_isAffineOpen_mem_and_subset hzW'
  have hU₁le : U₁ ≤ W₀ := fun q hq => (hU₁W hq).1
  have : Nonempty U₁ := ⟨⟨z, hzU₁⟩⟩
  obtain ⟨g, hg⟩ : ∃ g : Γ(V.X, U₁), ∀ h, fnOf _ h g = f⁻¹ :=
    ⟨resG V.X hU₁le g₀, fun h => (fnOf_resG _ h _).trans hg₀⟩
  have hg0 : g ≠ 0 := fun h => inv_ne_zero hf0 (by rw [← hg (gen_mem hzU₁), h, map_zero])
  have hzg : z ∉ V.X.basicOpen g := fun h =>
    (zeroAt_iff.1 hzero).2 (hg (gen_mem hzU₁) ▸ (unitAt_fnOf_iff hzU₁ _ g).2 h)

  haveI := CoverHt.isPreimmersion_j V
  set T : Set V.X := closure (V.j '' (V.π ⁻¹' (W : Set Y.X)ᶜ)) with hTdef
  have hT : ∀ w : V.G, V.j w ∈ T ↔ V.π w ∉ W := by
    have e1 := (Scheme.Hom.isEmbedding V.j).closure_eq_preimage_closure_image (V.π ⁻¹' (W : Set Y.X)ᶜ)
    rw [(W.isOpen.isClosed_compl.preimage V.π.continuous).closure_eq] at e1
    intro w
    exact (Set.ext_iff.1 e1 w).symm
  obtain ⟨w0, hw0⟩ := V.π.surjective (genericPoint Y.X)
  have hw0T : V.j w0 ∉ T := fun h => (hT w0).1 h (hw0 ▸ hW)
  obtain ⟨u, huU, huT⟩ := nonempty_preirreducible_inter U₁.isOpen isClosed_closure.isOpen_compl
    ⟨z, hzU₁⟩ ⟨_, hw0T⟩
  obtain ⟨h, hhle, huh⟩ := hU₁.exists_basicOpen_le (V := ⟨Tᶜ, isClosed_closure.isOpen_compl⟩) ⟨u, huT⟩ huU
  have hh0 : h ≠ 0 := by
    rintro rfl
    rw [Scheme.basicOpen_zero] at huh
    exact huh
  have hgh : g * h ≠ 0 := mul_ne_zero hg0 hh0
  obtain ⟨v, e, y, yt, hy, hc, hWt, hn, hu, hpv⟩ := exists_horizPt_over V U₁ hU₁ z hzU₁ g h hgh hzg p hnz
  have hbelow : below (y ≫ V.π) ∈ W := by
    have h1 : V.j (below y) ∉ T := hhle ((V.X.basicOpen_mul g h ▸ hu).2)
    exact not_not.1 fun h2 => h1 ((hT _).2 h2)
  have hlev := hval v (residueCharacteristic_eq_of_mem hp hpv) e ⟨y ≫ V.π, by rw [Category.assoc]; exact hy⟩ hbelow y yt rfl hc
    (fun q hq => (hU₁W (hWt hq)).2)
  have hu' : below (y ≫ V.j) ∈ V.X.basicOpen g := (V.X.basicOpen_mul g h ▸ hu).1
  have hb : below (y ≫ V.j) ∈ U₁ := V.X.basicOpen_le g hu'
  have ht : ⊤ ≤ (y ≫ V.j) ⁻¹ᵁ U₁ := fun q _ => by
    change (y ≫ V.j) q ∈ U₁
    rw [← hc]
    exact hWt (x := spMap e.O.subtype q) trivial
  have hunit : UnitAt (below (y ≫ V.j)) f⁻¹ := hg (gen_mem hb) ▸ (unitAt_fnOf_iff hb _ g).2 hu'
  have hfu : UnitAt (below (y ≫ V.j)) f := inv_inv f ▸ hunit.inv
  have hmul := OfModel.valAt_mul (y ≫ V.j) hfu.regAt hunit.regAt
  have hone : valAt (y ≫ V.j) (1 : V.X.functionField) = 1 := by
    have := OfModel.valAt_algebraMap (y ≫ V.j) 1
    rwa [map_one, map_one] at this
  have hev := OfModel.eval_pull e.O.subtype (𝟙 V.X) (y ≫ V.j) yt (hc.trans (Category.comp_id _).symm)
    (U := U₁) (W := U₁) le_rfl ht hWt g
  have hid : ((𝟙 V.X : V.X ⟶ V.X).appLE U₁ U₁ le_rfl).hom g = g := by
    have : (𝟙 V.X : V.X ⟶ V.X).appLE U₁ U₁ le_rfl = 𝟙 _ :=
      (Category.id_comp _).trans (V.X.presheaf.map_id _)
    rw [this]
    rfl
  rw [hid] at hev
  rw [mul_inv_cancel₀ hf0, hone, ← hg (gen_mem hb), OfModel.valAt_fnOf _ hb ht, hev] at hmul
  refine hn ((isUnit_eval_iff yt hWt g).1 (isUnit_of_one_le e _ ?_))
  have h₁ := congrArg e.w hmul
  rw [map_one, map_mul] at h₁
  exact h₁.le.trans (mul_le_of_le_one_left (e.w.nonneg _) hlev)

end GlobalTheory.Mean4O.Cover.RegOverP
