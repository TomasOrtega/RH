import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.LinksDefs
import Formalism.LocalRingCardinality.DataExtra
import Formalism.LocalRingCardinality.DataTies
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SupportedSubgroupSplitCommutePrimeIdempotents
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.UnitaryHeckeCharacterIdele
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UnitOpenAndCongrOpen
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsFinitePlaceIdempotentBaseChangeAdeles

open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsDedekindDomain NumberField Formalism.L2.Theta Formalism.IndefR.Links
  Formalism.L2.JoinChr Formalism.L2.Host Neutral.B1 ReciprocityTheory.Neutral.Bridge.HCFR
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.CharTransport

section General

variable (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Use `sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val P _ fun n => ?_)` and prove the remaining obligations. Establish `hc` using `GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap F E P`. Establish `h1` using `(GlobalTheory.Mem.UnitOpen.isOpen_val_le (P.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)`. Establish `h2` using `(GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-(n : ℤ))).preimage ((continuous_sub_left (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a)).comp hc)`. Take `⟨k, hk1, hk2⟩` from `(HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F) (P.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩`.

Establish `e : GlobalTheory.AdeleBaseChange.locMap F P a - GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a = GlobalTheory.AdeleBaseChange.locMap F P (a - algebraMap F _ k) - (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.fi …`. Rewrite using `[map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk1) hk2`.
-/
theorem locMap_eq (P : HeightOneSpectrum (𝓞 E)) (a : (P.under (𝓞 F)).adicCompletion F) :
    GlobalTheory.AdeleBaseChange.locMap F P a = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a := by
  refine sub_eq_zero.1 (GlobalTheory.PlaceIdem.eq_zero_of_val P _ fun n => ?_)
  have hc := GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_finiteCompletionMap F E P
  have h1 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le (P.under (𝓞 F)) (-(n : ℤ))).preimage (continuous_sub_left a)
  have h2 := (GlobalTheory.Mem.UnitOpen.isOpen_val_le P (-(n : ℤ))).preimage
    ((continuous_sub_left (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a)).comp hc)
  obtain ⟨k, hk1, hk2⟩ := (HeightOneSpectrum.denseRange_algebraMap (R := 𝓞 F) (K := F)
    (P.under (𝓞 F))).exists_mem_open (h1.inter h2) ⟨a, by simp, by simp⟩
  have e : GlobalTheory.AdeleBaseChange.locMap F P a - GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a =
      GlobalTheory.AdeleBaseChange.locMap F P (a - algebraMap F _ k) -
        (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P a -
          GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap F E P (algebraMap F _ k)) := by
    rw [map_sub, GlobalTheory.AdeleBaseChange.locMap_algebraMap, GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.finiteCompletionMap_coe]
    ring
  rw [e]
  exact Valuation.map_sub_le _ (GlobalTheory.AdeleBaseChange.locMap_valued P n _ hk1) hk2

/- English proof (translation)
Use `letI : Algebra F (AdeleRing (𝓞 E) E) := ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra`. Set `f : E →ₐ[F] AdeleRing (𝓞 E) E` to `⟨algebraMap E _, fun _ => rfl⟩`. Set `g : AF F →ₐ[F] AdeleRing (𝓞 E) E` to `⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E, fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x⟩`. Set `Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E` to `(Algebra.TensorProduct.productMap g f).toRingHom`. Establish `hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x` using `fun a x => rfl`.

Use `⟨Θ, ?_, hΘ⟩` and prove the remaining obligations. Use `haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩`. Set `φ : AF F ⊗[F] E →ₛₗ[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E] AdeleRing (𝓞 E) E` to `{ toFun := Θ map_add' := map_add Θ map_smul' := fun r z => by`. Rewrite using `[Algebra.smul_def, map_mul, smul_eq_mul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `Θ (r ⊗ₜ[F] 1) = _`. Rewrite using `[hΘ, map_one, mul_one] }`. Conclude with `IsModuleTopology.continuous_of_linearMapₛₗ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap F E) φ`.
-/
theorem exists_toAdele : ∃ Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E, Continuous Θ ∧
    ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := by
  letI : Algebra F (AdeleRing (𝓞 E) E) :=
    ((algebraMap E (AdeleRing (𝓞 E) E)).comp (algebraMap F E)).toAlgebra
  let f : E →ₐ[F] AdeleRing (𝓞 E) E := ⟨algebraMap E _, fun _ => rfl⟩
  let g : AF F →ₐ[F] AdeleRing (𝓞 E) E :=
    ⟨GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E, fun x => GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap_algebraMap F E x⟩
  let Θ : AF F ⊗[F] E →+* AdeleRing (𝓞 E) E := (Algebra.TensorProduct.productMap g f).toRingHom
  have hΘ : ∀ a x, Θ (a ⊗ₜ[F] x) = GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E a * algebraMap E _ x := fun a x => rfl
  refine ⟨Θ, ?_, hΘ⟩
  haveI : IsModuleTopology (AF F) (AF F ⊗[F] E) := ⟨rfl⟩
  let φ : AF F ⊗[F] E →ₛₗ[GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.adeleMap F E] AdeleRing (𝓞 E) E :=
    { toFun := Θ
      map_add' := map_add Θ
      map_smul' := fun r z => by
        rw [Algebra.smul_def, map_mul, smul_eq_mul]
        congr 1
        change Θ (r ⊗ₜ[F] 1) = _
        rw [hΘ, map_one, mul_one] }
  exact IsModuleTopology.continuous_of_linearMapₛₗ (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.continuous_adeleMap F E) φ

end General

/- English proof (translation)
Take `⟨h1, ⟨v, ε, hε, h2⟩, ht⟩` from `h`. Use `(GlobalTheory.IdemSupport.tie_iff hΦ h1 ?_ P).1 ht` and prove the remaining obligations. Break down `h2 with ⟨h2, h3⟩ | h2` into its components or cases. Establish `: e = (e + cA D e) * e` using `by linear_combination -h1 - h2`. Rewrite using `[this, h3, RingHom.map_mul, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, zero_mul]`.

Rewrite using `[h2, (GlobalTheory.IdemSupport.place_comp hΦ hε).1]`.
-/
theorem isDelta_of_isPlIdem {D : D7} {Φ : AE D →+* FiniteAdeleRing (𝓞 D.host.E) D.host.E}
    (hΦ : GlobalTheory.IdemSupport.Comp D Φ) {e : AE D} {P : HeightOneSpectrum (𝓞 D.host.E)} (h : IsPlIdem D e P) :
    GlobalTheory.IdemSupport.IsDelta Φ P e := by
  obtain ⟨h1, ⟨v, ε, hε, h2⟩, ht⟩ := h
  refine (GlobalTheory.IdemSupport.tie_iff hΦ h1 ?_ P).1 ht
  rcases h2 with ⟨h2, h3⟩ | h2
  · have : e = (e + cA D e) * e := by linear_combination -h1 - h2
    rw [this, h3, RingHom.map_mul, (GlobalTheory.IdemSupport.place_comp hΦ hε).1, zero_mul]
  · rw [h2, (GlobalTheory.IdemSupport.place_comp hΦ hε).1]

/- English proof (translation)
Rewrite using `[map_add, map_mul, map_sub, map_one]`.
-/
theorem map_loc {A B : Type} [Ring A] [Ring B] (f : A →+* B) (e k : A) :
    f (1 + e * (k - 1)) = 1 + f e * (f k - 1) := by
  rw [map_add, map_mul, map_sub, map_one]

set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨Θ, hc, hΘ⟩` from `exists_toAdele D.host.F D.host.E`. Take `⟨Φ, hΦ⟩` from `GlobalTheory.IdemSupport.exists_comp D`. Establish `hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x` using `fun x => by`. Express the relevant statement in the definitionally equal form `Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _`. Rewrite using `[hΘ, map_one, one_mul]`.

Establish `hfin : ∀ z, (Θ z).2 = Φ z` using `fun z => by`. Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => rw [RingHom.map_zero, RingHom.map_zero]`. Both sides reduce to the same expression. Consider the case `add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]`.

Both sides reduce to the same expression. Consider the case `tmul a x`. Establish `e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x`. Express the relevant statement in the definitionally equal form `_ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Rewrite using `[hΘ, e, RingHom.map_mul, hΦ.inc]`. Use `FiniteAdeleRing.ext _ fun Q => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ = Φ _ Q * _`. Rewrite using `[hΦ.base, locMap_eq]`. Both sides reduce to the same expression.

Establish `hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0` using `fun z hz => by`. Set `u : AE D` to `algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)`. Establish `h1 : u * z = 0`. Use `GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_` and prove the remaining obligations. Rewrite using `[RingHom.map_mul, hz, mul_zero, RingHom.map_zero]`.

Establish `: finPart D u = 0` using `TensorProduct.zero_tmul _ _`. Rewrite using `[RingHom.map_mul, this, zero_mul, RingHom.map_zero]`. Establish `h2 : (Θ u).1 = 1`. Express the relevant statement in the definitionally equal form `(Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1`. Rewrite using `[hΘ, map_one, mul_one]`.

Conclude with `map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)`. Establish `h3 : (Θ u).1 * (Θ z).1 = 0`. Express the relevant statement in the definitionally equal form `(Θ u * Θ z).1 = 0`. Rewrite using `[← RingHom.map_mul, h1, RingHom.map_zero]`. Both sides reduce to the same expression.

Rewrite `h3` using `[h2, one_mul]`. Then use the resulting hypothesis. Use `⟨Θ, hc, hinc, fun P e he k => ?_⟩` and prove the remaining obligations. Take `⟨d0, d1, d2⟩` from `isDelta_of_isPlIdem hΦ he`. Establish `hl : Θ (locE D e (k : D.host.E)) = 1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1)` using `(map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])`. Rewrite using `[hl]`.

Use `Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `1 + (Θ e).1 * _ = 1`. Rewrite using `[hinf e d0, zero_mul, add_zero]`. Express the relevant statement in the definitionally equal form `1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) = Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q`. Rewrite using `[hfin]`.

Distinguish the cases in `hQ : Q = P`. Substitute `hQ` using the available equality. Rewrite using `[d1, Function.update_self]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[d2 Q hQ, Function.update_of_ne hQ]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_hom (D : D7) : ∃ Θ : AE D →+* AdeleRing (𝓞 D.host.E) D.host.E, Continuous Θ ∧
    (∀ x, Θ (incA D x) = algebraMap D.host.E _ x) ∧
    ∀ (P : HeightOneSpectrum (𝓞 D.host.E)) (e : AE D), IsPlIdem D e P → ∀ k : D.host.Eˣ,
      Θ (locE D e (k : D.host.E)) =
        ((localIdele D.host.E P (atFin P k) : Ideles D.host.E) : AdeleRing (𝓞 D.host.E) D.host.E) := by
  obtain ⟨Θ, hc, hΘ⟩ := exists_toAdele D.host.F D.host.E
  obtain ⟨Φ, hΦ⟩ := GlobalTheory.IdemSupport.exists_comp D
  have hinc : ∀ x, Θ (incA D x) = algebraMap D.host.E _ x := fun x => by
    change Θ ((1 : AF D.host.F) ⊗ₜ[D.host.F] x) = _
    rw [hΘ, map_one, one_mul]
  have hfin : ∀ z, (Θ z).2 = Φ z := fun z => by
    induction z using TensorProduct.induction_on with
    | zero => rw [RingHom.map_zero, RingHom.map_zero]; rfl
    | add x y hx hy => rw [RingHom.map_add, RingHom.map_add, ← hx, ← hy]; rfl
    | tmul a x =>
      have e : (a ⊗ₜ[D.host.F] x : AE D) = algebraMap (AF D.host.F) (AE D) a * incA D x := by
        change _ = (a ⊗ₜ[D.host.F] (1 : D.host.E)) * ((1 : AF D.host.F) ⊗ₜ[D.host.F] x)
        rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
      rw [hΘ, e, RingHom.map_mul, hΦ.inc]
      refine FiniteAdeleRing.ext _ fun Q => ?_
      change _ = Φ _ Q * _
      rw [hΦ.base, locMap_eq]
      rfl
  have hinf : ∀ z, infPart D z = 0 → (Θ z).1 = 0 := fun z hz => by
    let u : AE D := algebraMap (AF D.host.F) (AE D) (pairA D.host.F 1 0)
    have h1 : u * z = 0 := by
      refine GlobalTheory.PlaceIdem.parts_inj D _ _ ?_ ?_
      · rw [RingHom.map_mul, hz, mul_zero, RingHom.map_zero]
      · have : finPart D u = 0 := TensorProduct.zero_tmul _ _
        rw [RingHom.map_mul, this, zero_mul, RingHom.map_zero]
    have h2 : (Θ u).1 = 1 := by
      change (Θ (pairA D.host.F 1 0 ⊗ₜ[D.host.F] (1 : D.host.E))).1 = 1
      rw [hΘ, map_one, mul_one]
      exact map_one (GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele.infiniteAdeleMap D.host.F D.host.E)
    have h3 : (Θ u).1 * (Θ z).1 = 0 := by
      change (Θ u * Θ z).1 = 0
      rw [← RingHom.map_mul, h1, RingHom.map_zero]
      rfl
    rwa [h2, one_mul] at h3
  refine ⟨Θ, hc, hinc, fun P e he k => ?_⟩
  obtain ⟨d0, d1, d2⟩ := isDelta_of_isPlIdem hΦ he
  have hl : Θ (locE D e (k : D.host.E)) =
      1 + Θ e * (algebraMap D.host.E (AdeleRing (𝓞 D.host.E) D.host.E) (k : D.host.E) - 1) :=
    (map_loc Θ e (incA D (k : D.host.E))).trans (by rw [hinc])
  rw [hl]
  refine Prod.ext ?_ (FiniteAdeleRing.ext _ fun Q => ?_)
  · change 1 + (Θ e).1 * _ = 1
    rw [hinf e d0, zero_mul, add_zero]
  · classical
    change 1 + (Θ e).2 Q * (algebraMap D.host.E (Q.adicCompletion D.host.E) (k : D.host.E) - 1) =
      Function.update (fun w : HeightOneSpectrum (𝓞 D.host.E) => (1 : w.adicCompletion D.host.E)) P
        (algebraMap D.host.E (P.adicCompletion D.host.E) (k : D.host.E)) Q
    rw [hfin]
    by_cases hQ : Q = P
    · subst hQ
      rw [d1, Function.update_self]
      ring
    · rw [d2 Q hQ, Function.update_of_ne hQ]
      ring

/- English proof (translation)
Introduce `D χ hχ`. Take `⟨Θ, hc, hinc, hloc⟩` from `exists_hom D`. Set `u : (AE D)ˣ →* Ideles D.host.E` to `Units.map Θ.toMonoidHom`. Establish `hu : Continuous u` using `Continuous.units_map _ hc`. Set `c : (AE D)ˣ →* Circle` to `{ toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩ map_one' := Circle.ext (by simp) map_mul' := fun x y => Circle.ext (by`.

Express the relevant statement in the definitionally equal form `((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)`. Rewrite using `[map_mul, map_mul, Units.val_mul]) }`. Establish `hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ)` using `fun x => rfl`. Use `⟨c, ⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩` and prove the remaining obligations. Conclude with `Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _`.

Establish `: u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x` using `Units.ext (hinc x)`. Rewrite using `[hcoe, this, χ.2.2]`. Both sides reduce to the same expression. Establish `: u x = localIdele D.host.E P (atFin P k)`. Use `Units.ext ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Θ (x : AE D) = _`. Rewrite using `[hx, hloc P e he]`. Rewrite using `[hcoe, this]`. Both sides reduce to the same expression.
-/
theorem exists_chrEq : ∀ (D : D7) (χ : Formalism.L2.Host.HChar D.host.E), χ.IsUnitary → ∃ c, ChrEq c χ := by
  intro D χ hχ
  obtain ⟨Θ, hc, hinc, hloc⟩ := exists_hom D
  let u : (AE D)ˣ →* Ideles D.host.E := Units.map Θ.toMonoidHom
  have hu : Continuous u := Continuous.units_map _ hc
  let c : (AE D)ˣ →* Circle :=
    { toFun := fun x => ⟨((χ.1 (u x) : ℂˣ) : ℂ), mem_sphere_zero_iff_norm.2 (hχ _)⟩
      map_one' := Circle.ext (by simp)
      map_mul' := fun x y => Circle.ext (by
        change ((χ.1 (u (x * y)) : ℂˣ) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) * ((χ.1 (u y) : ℂˣ) : ℂ)
        rw [map_mul, map_mul, Units.val_mul]) }
  have hcoe : ∀ x, ((c x : Circle) : ℂ) = ((χ.1 (u x) : ℂˣ) : ℂ) := fun x => rfl
  refine ⟨c, ⟨?_, fun x => Circle.ext ?_⟩, fun P e he k x hx => ?_⟩
  · exact Continuous.subtype_mk (Units.continuous_val.comp (χ.2.1.comp hu)) _
  · have : u (Units.map (incA D).toMonoidHom x) = diagUnits D.host.E x := Units.ext (hinc x)
    rw [hcoe, this, χ.2.2]
    rfl
  · have : u x = localIdele D.host.E P (atFin P k) := by
      refine Units.ext ?_
      change Θ (x : AE D) = _
      rw [hx, hloc P e he]
    rw [hcoe, this]
    rfl

end GlobalTheory.CharTransport
