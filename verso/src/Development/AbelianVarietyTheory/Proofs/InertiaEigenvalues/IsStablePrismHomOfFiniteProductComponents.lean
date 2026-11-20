import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.AdIPowLe
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.PrismHomMapIdealEqStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsFiniteProductOrientedBoundedPrismsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RingHomIsPushoutOfPiComponentsStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BKReal GlobalTheory.Per GlobalTheory.BSP
open scoped Formalism.Per NNReal

namespace GlobalTheory.ProdStable

/- English proof (translation)
Establish `hsurj : ∀ i, Function.Surjective (g i)` using `fun i y => by`. Take `⟨a, ha⟩` from `hg.2 (Pi.single (M := Ps) i y)`. Conclude with `⟨a, by simpa using congrFun ha i⟩`. Use `choose e he0 using fun i => hg.2 (Pi.single (M := Ps) i 1)`. Establish `he : ∀ i j, g j (e i) = Pi.single (M` using `Ps) i 1 j := fun i j => congrFun (he0 i) j`.

Set `F : (P ⧸ J) →+* ∀ i, Ps i ⧸ Ji i` to `Pi.ringHom fun i => Ideal.quotientMap (Ji i) (g i) (hle i)`. Express the relevant statement in the definitionally equal form `Function.Bijective F`. Use `⟨(injective_iff_map_eq_zero F).2 fun x hx => ?_, fun y => ?_⟩` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem]`.

Establish `hb : ∀ i, ∃ b ∈ J, g i b = g i a` using `fun i => by`. Use `congrFun hx i` as an intermediate fact. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ji i) (g i a) = 0 at this`. Rewrite `this` using `[Ideal.Quotient.eq_zero_iff_mem, ← hJ i]`. Conclude with `(Ideal.mem_map_iff_of_surjective _ (hsurj i)).1 this`.

Use `choose b hbJ hbg using hb`. Establish `ha : a = ∑ i, e i * b i` using `hg.1 <| funext fun j => by`. Express the relevant statement in the definitionally equal form `g j a = g j (∑ i, e i * b i)`. Rewrite using `[map_sum, Finset.sum_eq_single j]`. Rewrite using `[map_mul, he j j, Pi.single_eq_same, one_mul, hbg]`.

Introduce `i _ hij`. Rewrite using `[map_mul, he i j, Pi.single_eq_of_ne (Ne.symm hij), zero_mul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite using `[ha]`.

Conclude with `J.sum_mem fun i _ => J.mul_mem_left _ (hbJ i)`. Use `choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)`. Take `⟨a, ha⟩` from `hg.2 z`. Use `⟨Ideal.Quotient.mk J a, funext fun i => ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `Ideal.Quotient.mk (Ji i) (g i a) = y i`.

Rewrite using `[show g i a = z i from congrFun ha i, hz]`.
-/
theorem quot_pi_bij {P : Type} [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (J : Ideal P) (Ji : ∀ i, Ideal (Ps i)) (hle : ∀ i, J ≤ (Ji i).comap (g i))
    (hJ : ∀ i, J.map (g i) = Ji i) :
    Function.Bijective fun (x : P ⧸ J) (i : Fin n) => Ideal.quotientMap (Ji i) (g i) (hle i) x := by
  classical
  have hsurj : ∀ i, Function.Surjective (g i) := fun i y => by
    obtain ⟨a, ha⟩ := hg.2 (Pi.single (M := Ps) i y)
    exact ⟨a, by simpa using congrFun ha i⟩
  choose e he0 using fun i => hg.2 (Pi.single (M := Ps) i 1)
  have he : ∀ i j, g j (e i) = Pi.single (M := Ps) i 1 j := fun i j => congrFun (he0 i) j
  let F : (P ⧸ J) →+* ∀ i, Ps i ⧸ Ji i := Pi.ringHom fun i => Ideal.quotientMap (Ji i) (g i) (hle i)
  change Function.Bijective F
  refine ⟨(injective_iff_map_eq_zero F).2 fun x hx => ?_, fun y => ?_⟩
  · obtain ⟨a, rfl⟩ := Ideal.Quotient.mk_surjective x
    rw [Ideal.Quotient.eq_zero_iff_mem]
    have hb : ∀ i, ∃ b ∈ J, g i b = g i a := fun i => by
      have := congrFun hx i
      change Ideal.Quotient.mk (Ji i) (g i a) = 0 at this
      rw [Ideal.Quotient.eq_zero_iff_mem, ← hJ i] at this
      exact (Ideal.mem_map_iff_of_surjective _ (hsurj i)).1 this
    choose b hbJ hbg using hb
    have ha : a = ∑ i, e i * b i := hg.1 <| funext fun j => by
      change g j a = g j (∑ i, e i * b i)
      rw [map_sum, Finset.sum_eq_single j]
      · rw [map_mul, he j j, Pi.single_eq_same, one_mul, hbg]
      · intro i _ hij
        rw [map_mul, he i j, Pi.single_eq_of_ne (Ne.symm hij), zero_mul]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [ha]
    exact J.sum_mem fun i _ => J.mul_mem_left _ (hbJ i)
  · choose z hz using fun i => Ideal.Quotient.mk_surjective (y i)
    obtain ⟨a, ha⟩ := hg.2 z
    refine ⟨Ideal.Quotient.mk J a, funext fun i => ?_⟩
    change Ideal.Quotient.mk (Ji i) (g i a) = y i
    rw [show g i a = z i from congrFun ha i, hz]

/- English proof (translation)
Set `e : P ≃+* ∀ i, Ps i` to `RingEquiv.ofBijective (Pi.ringHom g) hg`. Establish `hpi : (Pi.ringHom fun i => (g i).comp f).Flat`. Use `letI : ∀ i, Algebra A (Ps i) := fun i => ((g i).comp f).toAlgebra`. Use `haveI : ∀ i, Module.Flat A (Ps i) := fun i => RingHom.flat_algebraMap_iff.1 (hf i)`. Use `haveI : Module.Flat A (Π₀ i, Ps i) := inferInstance`.

Use `haveI : Module.Flat A (∀ i, Ps i) := Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := Ps)).symm`. Conclude with `RingHom.flat_algebraMap_iff.2 this`. Establish `: f = (e.symm : (∀ i, Ps i) →+* P).comp (Pi.ringHom fun i => (g i).comp f)`. Use extensionality with `a`. Apply `e.injective` to reduce the goal to its premises.

Simplify using `[e]`. Both sides reduce to the same expression. Rewrite using `[this]`. Conclude with `hpi.comp (RingHom.Flat.of_bijective e.symm.bijective)`.
-/
theorem flat_of_pi {A P : Type} [CommRing A] [CommRing P] {n : ℕ} {Ps : Fin n → Type} [∀ i, CommRing (Ps i)]
    (f : A →+* P) (g : ∀ i, P →+* Ps i) (hg : Function.Bijective fun (x : P) (i : Fin n) => g i x)
    (hf : ∀ i, ((g i).comp f).Flat) : f.Flat := by
  classical
  let e : P ≃+* ∀ i, Ps i := RingEquiv.ofBijective (Pi.ringHom g) hg
  have hpi : (Pi.ringHom fun i => (g i).comp f).Flat := by
    letI : ∀ i, Algebra A (Ps i) := fun i => ((g i).comp f).toAlgebra
    haveI : ∀ i, Module.Flat A (Ps i) := fun i => RingHom.flat_algebraMap_iff.1 (hf i)
    haveI : Module.Flat A (Π₀ i, Ps i) := inferInstance
    haveI : Module.Flat A (∀ i, Ps i) :=
      Module.Flat.of_linearEquiv (DFinsupp.linearEquivFunOnFintype (R := A) (M := Ps)).symm
    exact RingHom.flat_algebraMap_iff.2 this
  have : f = (e.symm : (∀ i, Ps i) →+* P).comp (Pi.ringHom fun i => (g i).comp f) := by
    ext a
    apply e.injective
    simp [e]
    rfl
  rw [this]
  exact hpi.comp (RingHom.Flat.of_bijective e.symm.bijective)

/- English proof (translation)
The claim follows from `Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)`.
-/
theorem qmap_comp {l : ℕ} {R : Type} [CommRing R] {X Y Z : Obj l R} (g : Hom Y Z) (f : Hom X Y) (m : ℕ) :
    qmap (g.comp f) m = (qmap g m).comp (qmap f m) :=
  Ideal.Quotient.ringHom_ext (RingHom.ext fun _ => rfl)

/- English proof (translation)
Rewrite using `[Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]`.
-/
theorem adI_pow_map {l : ℕ} {R : Type} [CommRing R] {X Y : Obj l R} (f : Hom X Y)
    (hI : X.I.map f.f = Y.I) (m : ℕ) : (adI X ^ m).map f.f = adI Y ^ m := by
  rw [Ideal.map_pow, Ideal.map_sup, Ideal.map_span, Set.image_singleton, map_natCast, hI]

/- English proof (translation)
The claim follows from `quot_pi_bij (fun i => (π i).f) hbij _ _ (fun i => adI_pow_le (π i) m) fun i => adI_pow_map (π i) (hI i) m`.
-/
theorem qmap_pi_bij {l : ℕ} {R : Type} [CommRing R] {n : ℕ} {C : Fin n → Obj l R} {Q : Obj l R}
    (π : ∀ i, Hom Q (C i)) (hbij : Function.Bijective fun (x : Q.A) (i : Fin n) => (π i).f x)
    (hI : ∀ i, Q.I.map (π i).f = (C i).I) (m : ℕ) :
    Function.Bijective fun (x : Q.A ⧸ adI Q ^ m) (i : Fin n) => qmap (π i) m x :=
  quot_pi_bij (fun i => (π i).f) hbij _ _ (fun i => adI_pow_le (π i) m) fun i => adI_pow_map (π i) (hI i) m

/- English proof (translation)
Introduce `l _ R _ n C hC Q π hbij B h hs`. Establish `hQI : ∀ i, Q.I.map (π i).f = (C i).I` using `fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q (C i) (π i)`. Use `⟨fun m => ?_, fun B' k => ?_⟩` and prove the remaining obligations. Conclude with `flat_of_pi (qmap h m) (fun i => qmap (π i) m) (qmap_pi_bij π hbij hQI m) fun i => by rw [← qmap_comp]; exact (hs i).flat m`. Use `choose C' k' h' hpo using fun i => (hs i).po B' k`.

Establish `hC' : ∀ i, ∃ t, (C' i).I = Ideal.span {t}` using `fun i => by`. Take `⟨t, ht⟩` from `hC i`. Conclude with `⟨(k' i).f t, by rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R _ _ (k' i), ht, Ideal.map_span, Set.image_singleton]⟩`. Take `⟨Q', π', hbij', -, huniv⟩` from `GlobalTheory.T.exists_finite_product_oriented_boundedPrisms l R n C' hC'`. Establish `hQ'I : ∀ i, Q'.I.map (π' i).f = (C' i).I` using `fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q' (C' i) (π' i)`.

Take `⟨K, hK⟩` from `huniv Q fun i => (k' i).comp (π i)`. Take `⟨H, hH⟩` from `huniv B' h'`. Establish `hinj : ∀ {X : Obj l R} (a b : Hom X Q'), (∀ i, (π' i).comp a = (π' i).comp b) → a = b` using `fun a b hab => Hom.ext' (RingHom.ext fun x => hbij'.1 (funext fun i => congrArg (fun c => c.f x) (hab i)))`. Use `⟨Q', K, H, ⟨hinj _ _ fun i => ?_, fun m => ?_⟩⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Use `GlobalTheory.T.ringHom_isPushout_of_pi_components (qmap h m) (qmap k m) (qmap K m) (qmap H m) (fun i => qmap (π i) m) (fun i => qmap (π' i) m) (fun i => qmap (k' i) m) (fun i => qmap (h' i) m) (qmap_pi_bij π hbij hQI m) (qmap_pi_bij π' hbij' hQ'I m) (fun i => ?_) (fun i => ?_) (f …` and prove the remaining obligations. Rewrite using `[← qmap_comp, ← qmap_comp, hK i]`. Rewrite using `[← qmap_comp, hH i]`. Rewrite using `[← qmap_comp]`. Conclude with `(hpo i).po m`.
-/
theorem prodStable : ∀ (l : ℕ) [Fact l.Prime] (R : Type) [CommRing R] (n : ℕ) (C : Fin n → Obj l R),
    (∀ i, ∃ t, (C i).I = Ideal.span {t}) → ∀ (Q : Obj l R) (π : ∀ i, Hom Q (C i)),
    Function.Bijective (fun (x : Q.A) (i : Fin n) => (π i).f x) → ∀ (B : Obj l R) (h : Hom B Q),
    (∀ i, Stable ((π i).comp h)) → Stable h := by
  intro l _ R _ n C hC Q π hbij B h hs
  have hQI : ∀ i, Q.I.map (π i).f = (C i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q (C i) (π i)
  refine ⟨fun m => ?_, fun B' k => ?_⟩
  · exact flat_of_pi (qmap h m) (fun i => qmap (π i) m) (qmap_pi_bij π hbij hQI m)
      fun i => by rw [← qmap_comp]; exact (hs i).flat m
  · choose C' k' h' hpo using fun i => (hs i).po B' k
    have hC' : ∀ i, ∃ t, (C' i).I = Ideal.span {t} := fun i => by
      obtain ⟨t, ht⟩ := hC i
      exact ⟨(k' i).f t, by rw [← GlobalTheory.T.prism_hom_map_ideal_eq l R _ _ (k' i), ht, Ideal.map_span, Set.image_singleton]⟩
    obtain ⟨Q', π', hbij', -, huniv⟩ := GlobalTheory.T.exists_finite_product_oriented_boundedPrisms l R n C' hC'
    have hQ'I : ∀ i, Q'.I.map (π' i).f = (C' i).I := fun i => GlobalTheory.T.prism_hom_map_ideal_eq l R Q' (C' i) (π' i)
    obtain ⟨K, hK⟩ := huniv Q fun i => (k' i).comp (π i)
    obtain ⟨H, hH⟩ := huniv B' h'
    have hinj : ∀ {X : Obj l R} (a b : Hom X Q'), (∀ i, (π' i).comp a = (π' i).comp b) → a = b :=
      fun a b hab => Hom.ext' (RingHom.ext fun x => hbij'.1 (funext fun i => congrArg (fun c => c.f x) (hab i)))
    refine ⟨Q', K, H, ⟨hinj _ _ fun i => ?_, fun m => ?_⟩⟩
    · calc (π' i).comp (K.comp h) = ((π' i).comp K).comp h := Hom.ext' rfl
        _ = (k' i).comp ((π i).comp h) := by rw [hK i]; exact Hom.ext' rfl
        _ = (h' i).comp k := (hpo i).comm
        _ = ((π' i).comp H).comp k := by rw [hH i]
        _ = (π' i).comp (H.comp k) := Hom.ext' rfl
    · refine GlobalTheory.T.ringHom_isPushout_of_pi_components (qmap h m) (qmap k m) (qmap K m) (qmap H m) (fun i => qmap (π i) m)
        (fun i => qmap (π' i) m) (fun i => qmap (k' i) m) (fun i => qmap (h' i) m)
        (qmap_pi_bij π hbij hQI m) (qmap_pi_bij π' hbij' hQ'I m) (fun i => ?_) (fun i => ?_) (fun i => ?_)
      · rw [← qmap_comp, ← qmap_comp, hK i]
      · rw [← qmap_comp, hH i]
      · rw [← qmap_comp]; exact (hpo i).po m

end GlobalTheory.ProdStable
