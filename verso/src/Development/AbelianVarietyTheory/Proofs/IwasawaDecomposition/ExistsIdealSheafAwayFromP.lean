import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HasPRatio
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.MultiplicationLatticeSecond
import Development.AbelianVarietyTheory.Definitions.ThetaMetrics.IsRegularFnIffOfIsAffineOpen
open AlgebraicGeometry CategoryTheory Limits NumberField MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj GlobalTheory.LocM GlobalTheory.ShFam.Pad GlobalTheory.HTLine
open Formalism.MainNotions.DIV.Cons (intO SCF)
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section

namespace GlobalTheory.Principalise

/- English proof (translation)
Establish `hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom` using `fun B => by`. Rewrite using `[← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]`. Rewrite using `[hk, RingHom.mem_ker]`. Use `GlobalTheory.Cartier.ext_germ fun z hz => ?_` and prove the remaining obligations. Take `⟨B, e, hzB, this⟩` from `h _ hz`.

Rewrite `this` using `[hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG]`. Rewrite using `[← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]`.
-/
theorem memIdealOfLocally {W : Scheme.{0}} (I : W.IdealSheafData) (A : W.affineOpens) (b : Γ(W, A.1))
    (h : ∀ y ∈ A.1, ∃ (B : W.affineOpens) (e : B.1 ≤ A.1), y ∈ B.1 ∧ resG W e b ∈ I.ideal B) :
    b ∈ I.ideal A := by
  have hk : ∀ B : W.affineOpens, I.ideal B = RingHom.ker (I.subschemeι.app B.1).hom := fun B => by
    rw [← Scheme.Hom.ker_apply, Scheme.IdealSheafData.ker_subschemeι]
  rw [hk, RingHom.mem_ker]
  refine GlobalTheory.Cartier.ext_germ fun z hz => ?_
  obtain ⟨B, e, hzB, this⟩ := h _ hz
  rw [hk, RingHom.mem_ker, GlobalTheory.Cartier.app_resG] at this
  rw [← GlobalTheory.Cartier.germ_resG (I.subschemeι.preimage_mono e) z hzB, this, map_zero, map_zero]

/- English proof (translation)
Establish `key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U))`. Use `(GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_` and prove the remaining obligations. Take `⟨t, htle, hyt⟩` from `U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)`. Take `⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩` from `W.isBasis_affineOpens.exists_subset_of_mem_open (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen`. Use `⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩` and prove the remaining obligations.

Establish `hDU' : X.basicOpen t ≤ U'.1` using `htle.trans inf_le_left`. Establish `h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t)` using `J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha`. Rewrite `h1` using `[← J.map_ideal_basicOpen U t]`. Establish `hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t` using `fun x hx => (hB'le hx).2`. Establish `e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) = (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a)` using `by show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))`.

Rewrite using `[GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]`. Rewrite using `[e, Scheme.IdealSheafData.ofIdealTop_ideal]`. Establish `h2` using `Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1`. Rewrite `h2` using `[Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE]`. Rewrite using `[Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]`.

Conclude with `h2`. Use `key ⟨⊤, isAffineOpen_top W⟩` as an intermediate fact. Rewrite `this` using `[Scheme.IdealSheafData.ofIdealTop_ideal]`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Use `Ideal.map_id _` and compare the differences between its conclusion and the goal.

Rewrite using `[show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]`. Both sides reduce to the same expression.
-/
theorem comapIdealTopLe {X W : Scheme.{0}} [IsAffine W] (J : X.IdealSheafData) (g : W ⟶ X)
    (U : X.affineOpens) (h : ⊤ ≤ g ⁻¹ᵁ U.1) :
    (J.comap g).ideal ⟨⊤, isAffineOpen_top W⟩ ≤ Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U) := by
  have key : J.comap g ≤ Scheme.IdealSheafData.ofIdealTop (Ideal.map (g.appLE U.1 ⊤ h).hom (J.ideal U)) := by
    refine (GlobalTheory.Cartier.comap_le_iff _ _ _).2 fun U' a ha B hB => memIdealOfLocally _ _ _ fun y hy => ?_
    obtain ⟨t, htle, hyt⟩ := U.2.exists_basicOpen_le (V := U'.1 ⊓ U.1) ⟨g y, hB hy, h trivial⟩ (h trivial)
    obtain ⟨_, ⟨B', hB'a, rfl⟩, hyB', hB'le⟩ := W.isBasis_affineOpens.exists_subset_of_mem_open
      (show y ∈ B.1 ⊓ g ⁻¹ᵁ X.basicOpen t from ⟨hy, hyt⟩) (B.1 ⊓ g ⁻¹ᵁ X.basicOpen t).isOpen
    refine ⟨⟨B', hB'a⟩, fun x hx => (hB'le hx).1, hyB', ?_⟩
    have hDU' : X.basicOpen t ≤ U'.1 := htle.trans inf_le_left
    have h1 : resG X hDU' a ∈ J.ideal (X.affineBasicOpen t) :=
      J.ideal_le_comap_ideal (U := X.affineBasicOpen t) (V := U') hDU' ha
    rw [← J.map_ideal_basicOpen U t] at h1
    have hB'D : B' ≤ g ⁻¹ᵁ X.basicOpen t := fun x hx => (hB'le hx).2
    have e : resG W (fun x hx => (hB'le hx).1 : B' ≤ B.1) (resG W hB ((g.app U'.1).hom a)) =
        (g.appLE (X.basicOpen t) B' hB'D).hom (resG X hDU' a) := by
      show _ = resG W hB'D ((g.app (X.basicOpen t)).hom (resG X hDU' a))
      rw [GlobalTheory.Cartier.app_resG, GlobalTheory.Cartier.resG_resG, GlobalTheory.Cartier.resG_resG]
    rw [e, Scheme.IdealSheafData.ofIdealTop_ideal]
    have h2 := Ideal.mem_map_of_mem (g.appLE (X.basicOpen t) B' hB'D).hom h1
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.map_appLE] at h2
    rw [Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_map]
    exact h2
  have := key ⟨⊤, isAffineOpen_top W⟩
  rw [Scheme.IdealSheafData.ofIdealTop_ideal] at this
  refine this.trans (le_of_eq ?_)
  convert Ideal.map_id _
  rw [show homOfLE (le_top : (⊤ : W.Opens) ≤ ⊤) = 𝟙 _ from rfl, op_id, CategoryTheory.Functor.map_id]
  rfl

/- English proof (translation)
Introduce `X W J g U A h`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Establish `: IsAffine A.1.toScheme` using `A.2`. Establish `hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1` using `A.1.ι_preimage_self.ge`.

Establish `h1` using `(GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA`. Rewrite `h1` using `[← Scheme.IdealSheafData.comap_comp]`. Establish `h2` using `comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1`. Establish `hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom` using `ConcreteCategory.bijective_of_isIso _`. Rewrite using `[← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)), Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]`.

Conclude with `h2`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Conclude with `(GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h`.
-/
theorem comapIdealAffine : ∀ {X W : Scheme.{0}} (J : X.IdealSheafData) (g : W ⟶ X) (U : X.affineOpens) (A : W.affineOpens) (h : A.1 ≤ g ⁻¹ᵁ U.1), (J.comap g).ideal A = Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U) := by
  intro X W J g U A h
  apply le_antisymm
  · intro x hx
    have : IsAffine A.1.toScheme := A.2
    have hA : ⊤ ≤ A.1.ι ⁻¹ᵁ A.1 := A.1.ι_preimage_self.ge
    have h1 := (GlobalTheory.Cartier.comap_le_iff (J.comap g) A.1.ι _).1 le_rfl A x hx ⟨⊤, isAffineOpen_top _⟩ hA
    rw [← Scheme.IdealSheafData.comap_comp] at h1
    have h2 := comapIdealTopLe J (A.1.ι ≫ g) U (hA.trans (A.1.ι.preimage_mono h)) h1
    have hb : Function.Bijective (A.1.ι.appLE A.1 ⊤ hA).hom := ConcreteCategory.bijective_of_isIso _
    rw [← Ideal.comap_map_of_bijective _ hb (I := Ideal.map (g.appLE U.1 A.1 h).hom (J.ideal U)),
      Ideal.mem_comap, Ideal.map_map, ← CommRingCat.hom_comp, Scheme.Hom.appLE_comp_appLE]
    exact h2
  · rw [Ideal.map_le_iff_le_comap]
    intro a ha
    exact (GlobalTheory.Cartier.comap_le_iff J g _).1 le_rfl U a ha A h

/- English proof (translation)
Introduce `X _ U hU I`. Establish `hR : IsNoetherianRing Γ(X, U)` using `IsLocallyNoetherian.component_noetherian ⟨U, hU⟩`. Set `q : Γ(X, U) →+* Γ(X, U) ⧸ I` to `Ideal.Quotient.mk I`. Set `f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X` to `Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec`. Use `haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f`.

Establish `hz : ⊤ ≤ f ⁻¹ᵁ U` using `fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩`. Establish `hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U` using `by rw [hU.fromSpec_preimage_self]`. Establish `hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop`. Rewrite using `[Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.

Establish `m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop`. Rewrite using `[hzapp]`. Use `congr 1`. Rewrite using `[Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]`. Use `Category.comp_id _` and compare the differences between its conclusion and the goal.

Conclude with `(Spec Γ(X, U)).presheaf.map_id _`. Establish `m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop = CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv` using `(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm`. Establish `k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b)`. Introduce `b`. Rewrite using `[m2, m3]`.

Both sides reduce to the same expression. Use `⟨f.ker, ?_, ?_⟩` and prove the remaining obligations. Use extensionality with `a`. Rewrite using `[Scheme.Hom.ker_apply, RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion.

Introduce `ha`. Establish `h1 : (f.appLE U ⊤ hz).hom a = 0` using `by show resG _ hz ((f.app U).hom a) = 0`. Rewrite using `[ha, map_zero]`. Rewrite `h1` using `[k1]`. Establish `h2` using `congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1`.

Rewrite `h2` using `[Iso.inv_hom_id_apply, map_zero]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h2`. Introduce `ha`. Establish `h1 : (f.appLE U ⊤ hz).hom a = 0`. Rewrite using `[k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]`.

Use `GlobalTheory.Cartier.ext_germ fun x hx => ?_` and prove the remaining obligations. Rewrite using `[map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]`. Conclude with `(congrArg _ h1).trans (map_zero _)`. Introduce `N hN V`. Rewrite using `[Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]`.

Establish `h0 : (N : Γ(X, U) ⧸ I) = 0`. Rewrite using `[← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]`. Conclude with `hN`. Establish `h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0`. Rewrite using `[← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]`.

Rewrite using `[← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]`.
-/
theorem kerIdealAffine : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (U : X.Opens) (hU : IsAffineOpen U) (I : Ideal Γ(X, U)), ∃ J : X.IdealSheafData, J.ideal ⟨U, hU⟩ = I ∧ ∀ N : ℕ, (N : Γ(X, U)) ∈ I → ∀ V : X.affineOpens, (N : Γ(X, V.1)) ∈ J.ideal V := by
  intro X _ U hU I
  have hR : IsNoetherianRing Γ(X, U) := IsLocallyNoetherian.component_noetherian ⟨U, hU⟩
  let q : Γ(X, U) →+* Γ(X, U) ⧸ I := Ideal.Quotient.mk I
  let f : Spec (CommRingCat.of (Γ(X, U) ⧸ I)) ⟶ X := Spec.map (CommRingCat.ofHom q) ≫ hU.fromSpec
  haveI : QuasiCompact f := quasiCompact_of_noetherianSpace_source f
  have hz : ⊤ ≤ f ⁻¹ᵁ U := fun _ _ => hU.range_fromSpec.subset ⟨_, rfl⟩
  have hfs : ⊤ ≤ hU.fromSpec ⁻¹ᵁ U := by rw [hU.fromSpec_preimage_self]
  have hzapp : f.appLE U ⊤ hz = hU.fromSpec.appLE U ⊤ hfs ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [Scheme.Hom.comp_appLE]
    rfl
  have m2 : f.appLE U ⊤ hz = (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop := by
    rw [hzapp]
    congr 1
    rw [Scheme.Hom.appLE, IsAffineOpen.fromSpec_app_self, Category.assoc, ← Functor.map_comp]
    convert Category.comp_id _
    exact (Spec Γ(X, U)).presheaf.map_id _
  have m3 : (Scheme.ΓSpecIso Γ(X, U)).inv ≫ (Spec.map (CommRingCat.ofHom q)).appTop =
      CommRingCat.ofHom q ≫ (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv :=
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom q)).symm
  have k1 : ∀ b, (f.appLE U ⊤ hz).hom b = (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom (q b) := by
    intro b
    rw [m2, m3]
    rfl
  refine ⟨f.ker, ?_, ?_⟩
  · ext a
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker]
    constructor
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        show resG _ hz ((f.app U).hom a) = 0
        rw [ha, map_zero]
      rw [k1] at h1
      have h2 := congrArg (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).hom.hom h1
      rw [Iso.inv_hom_id_apply, map_zero] at h2
      exact Ideal.Quotient.eq_zero_iff_mem.1 h2
    · intro ha
      have h1 : (f.appLE U ⊤ hz).hom a = 0 := by
        rw [k1, show q a = 0 from Ideal.Quotient.eq_zero_iff_mem.2 ha, map_zero]
      refine GlobalTheory.Cartier.ext_germ fun x hx => ?_
      rw [map_zero, ← GlobalTheory.Cartier.germ_resG hz x trivial]
      exact (congrArg _ h1).trans (map_zero _)
  · intro N hN V
    rw [Scheme.Hom.ker_apply, RingHom.mem_ker, map_natCast]
    have h0 : (N : Γ(X, U) ⧸ I) = 0 := by
      rw [← map_natCast q, Ideal.Quotient.eq_zero_iff_mem]; exact hN
    have h1 : (N : Γ(Spec (CommRingCat.of (Γ(X, U) ⧸ I)), ⊤)) = 0 := by
      rw [← map_natCast (Scheme.ΓSpecIso (CommRingCat.of (Γ(X, U) ⧸ I))).inv.hom, h0, map_zero]
    rw [← map_natCast (resG _ (le_top : f ⁻¹ᵁ V.1 ≤ ⊤)), h1, map_zero]

/- English proof (translation)
Establish `hfm : f ∈ Ideal.span (Set.range A) * I'` using `h ▸ Ideal.mem_span_singleton_self f`. Establish `key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k`. Introduce `x hx`. Use `Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)` and prove the remaining obligations. Take `⟨d, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 ha`.

Use `⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩` and prove the remaining obligations. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring`. Use `⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩` and prove the remaining obligations. Simplify using `only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]`.

Take `⟨c, hc, hfc⟩` from `key f hfm`. Establish `hAc : ∀ k k', ∃ t, A k' * c k = f * t` using `fun k k' => by`. Establish `: A k' * c k ∈ Ideal.span {f}` using `h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)`. Take `⟨t, ht⟩` from `Ideal.mem_span_singleton'.1 this`. Conclude with `⟨t, by rw [← ht, mul_comm]⟩`.

Use `choose t ht using hAc`. Establish `hsum : ∑ k, t k k = 1`. Use `(mul_cancel_left_mem_nonZeroDivisors hf).1 ?_` and prove the remaining obligations. Rewrite using `[Finset.mul_sum, _root_.mul_one]`. Use `conv_rhs => rw [hfc]`.

Conclude with `Finset.sum_congr rfl fun k _ => (ht k k).symm`. Choose the witnesses or unpack the hypotheses as in `⟨k, hk⟩ : ∃ k, t k k ∉ P := by`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Conclude with `(Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2 (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))`.

Use `⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩` and prove the remaining obligations. Use `(mul_cancel_left_mem_nonZeroDivisors hf).1 ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem exists_dvd_of_span_mul_eq {R : Type*} [CommRing R] (P : Ideal R) [P.IsPrime] {m : ℕ}
    (A : Fin m → R) (I' : Ideal R) {f : R} (h : Ideal.span (Set.range A) * I' = Ideal.span {f})
    (hf : f ∈ nonZeroDivisors R) : ∃ k, ∃ s ∉ P, ∀ k', A k ∣ s * A k' := by
  have hfm : f ∈ Ideal.span (Set.range A) * I' := h ▸ Ideal.mem_span_singleton_self f
  have key : ∀ x ∈ Ideal.span (Set.range A) * I', ∃ c : Fin m → R, (∀ k, c k ∈ I') ∧ x = ∑ k, A k * c k := by
    intro x hx
    refine Submodule.mul_induction_on hx (fun a ha b hb => ?_) (fun x y ⟨c, hc, hx⟩ ⟨d, hd, hy⟩ => ?_)
    · obtain ⟨d, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 ha
      refine ⟨fun k => d k * b, fun k => I'.mul_mem_left _ hb, ?_⟩
      rw [Finset.sum_mul]
      exact Finset.sum_congr rfl fun k _ => by simp only [smul_eq_mul]; ring
    · refine ⟨c + d, fun k => I'.add_mem (hc k) (hd k), ?_⟩
      simp only [hx, hy, Pi.add_apply, mul_add, Finset.sum_add_distrib]
  obtain ⟨c, hc, hfc⟩ := key f hfm
  have hAc : ∀ k k', ∃ t, A k' * c k = f * t := fun k k' => by
    have : A k' * c k ∈ Ideal.span {f} :=
      h ▸ Ideal.mul_mem_mul (Ideal.subset_span ⟨k', rfl⟩) (hc k)
    obtain ⟨t, ht⟩ := Ideal.mem_span_singleton'.1 this
    exact ⟨t, by rw [← ht, mul_comm]⟩
  choose t ht using hAc
  have hsum : ∑ k, t k k = 1 := by
    refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
    rw [Finset.mul_sum, _root_.mul_one]
    conv_rhs => rw [hfc]
    exact Finset.sum_congr rfl fun k _ => (ht k k).symm
  obtain ⟨k, hk⟩ : ∃ k, t k k ∉ P := by
    by_contra hcon
    push_neg at hcon
    exact (Ideal.IsPrime.ne_top inferInstance) ((Ideal.eq_top_iff_one _).2
      (hsum ▸ Ideal.sum_mem _ fun k _ => hcon k))
  refine ⟨k, t k k, hk, fun k' => ⟨t k k', ?_⟩⟩
  refine (mul_cancel_left_mem_nonZeroDivisors hf).1 ?_
  calc f * (t k k * A k') = (f * t k k) * A k' := by ring
    _ = A k * c k * A k' := by rw [ht]
    _ = A k * (A k' * c k) := by ring
    _ = f * (A k * t k k') := by rw [ht]; ring

/- English proof (translation)
Introduce `X _ p n U m A hU hp`. Use `choose J hJU hJp using fun j => kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))`. Use `choose N hN using fun j => hp j`. Establish `hmem : ∀ (V : X.affineOpens) (s : Finset (Fin n)), ((p ^ (∑ j ∈ s, N j) : ℕ) : Γ(X, V.1)) ∈ (∏ j ∈ s, J j).ideal V`. Introduce `V s`.

Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert j s hj ih`. Rewrite using `[Finset.prod_insert hj, Finset.sum_insert hj, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, pow_add, Nat.cast_mul]`. Use `Ideal.mul_mem_mul (hJp j _ ?_ V) ih` and prove the remaining obligations.

Rewrite using `[Nat.cast_pow]`. Conclude with `hN j`. Use `⟨∏ j, J j, fun x hx hxp => ?_, ?_⟩` and prove the remaining obligations. Take `⟨_, ⟨V, hV, rfl⟩, hxV, -⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ`. Establish `h1` using `(Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx`.

Rewrite `h1` using `[Scheme.mem_zeroLocus_iff]`. Use `h1 _ (hmem ⟨V, hV⟩ Finset.univ) ?_` and prove the remaining obligations. Establish `e : ((p ^ (∑ j, N j) : ℕ) : Γ(X, V)) = (X.presheaf.map (homOfLE le_top).op).hom ((p : Γ(X, ⊤)) ^ (∑ j, N j))`. Simplify using the standard rewrite rules. Rewrite using `[e, Scheme.basicOpen_res]`.

Use `⟨hxV, ?_⟩` and prove the remaining obligations. Establish `htop : x ∈ (⊤ : X.Opens)` using `trivial`. Use `show x ∈ X.basicOpen _`. Rewrite using `[Scheme.mem_basicOpen _ _ _ htop, map_pow]`. Conclude with `((Scheme.mem_basicOpen _ _ _ htop).1 hxp).pow _`.

Introduce `W W' b ν hE w j hw`. Establish `hw0 : b (ν w) ∈ U j` using `hw`. Take `⟨V₁, f, hw₁, hf, hV₁⟩` from `hE (ν w)`. Take `⟨g, hgle, hwg⟩` from `V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨ν w, hw₁, hw0⟩ hw₁`. Establish `hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j` using `hgle.trans inf_le_right`.

Establish `hDV : (W.affineBasicOpen g).1 ≤ V₁.1` using `W.basicOpen_le g`. Establish `hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1)` using `(GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1 (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)`. Establish `hI1` using `((∏ i, J i).comap b).map_ideal_basicOpen V₁ g`. Rewrite `hI1` using `[hV₁, Ideal.map_span, Set.image_singleton]`. Establish `hI2` using `comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU`.

Rewrite `hI2` using `[← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul, Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp]`. Rewrite `hI1` using `[← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)]`. Establish `hwD : ν w ∈ (W.affineBasicOpen g).1` using `hwg`. Take `⟨k, s, hsP, hdiv⟩` from `exists_dvd_of_span_mul_eq (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 (ν w) hwD).hom (IsLocalRing.maximalIdeal _)) _ _ (hI2.symm.trans hI1.symm) hfD`. Establish `hsu : ν w ∈ W.basicOpen s`.

Rewrite using `[Scheme.mem_basicOpen _ _ _ hwD]`. Assume the negation of the conclusion as `hc`. Conclude with `hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)`. Establish `hED : W.basicOpen s ≤ (W.affineBasicOpen g).1` using `W.basicOpen_le s`. Take `⟨_, ⟨V, hVa, rfl⟩, hwV, hVE⟩` from `W'.isBasis_affineOpens.exists_subset_of_mem_open (show w ∈ ν ⁻¹ᵁ W.basicOpen s from hsu) (ν ⁻¹ᵁ W.basicOpen s).isOpen`.

Establish `hVE' : V ≤ ν ⁻¹ᵁ W.basicOpen s` using `hVE`. Establish `hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j` using `fun x hx => hDU (hED (hVE' hx))`. Use `⟨V, hV, hwV, hVa, k, fun k' => ?_⟩` and prove the remaining obligations. Establish `key : (b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op) ≫ ν.appLE _ V hVE' = (ν ≫ b).appLE (U j) V hV`. Rewrite using `[Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]`.

Establish `hu` using `W.toRingedSpace.isUnit_res_basicOpen s`. Establish `h1` using `map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')`. Rewrite `h1` using `[map_mul]`. Establish `h2` using `hu.dvd_mul_left.1 h1`. Establish `h3` using `map_dvd (ν.appLE _ V hVE').hom h2`.

Rewrite using `[← key]`. Simplify using `using h3`.
-/
theorem exists_idealSheaf_principalises : ∀ (X : Scheme.{0}) [IsLocallyNoetherian X] (p n : ℕ) (U : Fin n → X.Opens) (m : Fin n → ℕ) (A : ∀ j, Fin (m j) → Γ(X, U j)), (∀ j, IsAffineOpen (U j)) → (∀ j, (p : Γ(X, U j)) ∈ (Ideal.span (Set.range (A j))).radical) → ∃ J : X.IdealSheafData, (∀ x ∈ J.support, x ∉ X.basicOpen (p : Γ(X, ⊤))) ∧ ∀ (W W' : Scheme.{0}) (b : W ⟶ X) (ν : W' ⟶ W), ReciprocityTheory.AnForm.R.FinalTheorems.EffCartier (J.comap b) → ∀ (w : W') (j : Fin n), (ν ≫ b) w ∈ U j → ∃ (V : W'.Opens) (hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j), w ∈ V ∧ IsAffineOpen V ∧ ∃ k, ∀ k', ((ν ≫ b).appLE (U j) V hV).hom (A j k) ∣ ((ν ≫ b).appLE (U j) V hV).hom (A j k') := by
  intro X _ p n U m A hU hp
  choose J hJU hJp using fun j => kerIdealAffine X (U j) (hU j) (Ideal.span (Set.range (A j)))
  choose N hN using fun j => hp j
  have hmem : ∀ (V : X.affineOpens) (s : Finset (Fin n)),
      ((p ^ (∑ j ∈ s, N j) : ℕ) : Γ(X, V.1)) ∈ (∏ j ∈ s, J j).ideal V := by
    intro V s
    induction s using Finset.induction_on with
    | empty => simp
    | insert j s hj ih =>
      rw [Finset.prod_insert hj, Finset.sum_insert hj, Scheme.IdealSheafData.ideal_mul, Pi.mul_apply,
        pow_add, Nat.cast_mul]
      refine Ideal.mul_mem_mul (hJp j _ ?_ V) ih
      rw [Nat.cast_pow]
      exact hN j
  refine ⟨∏ j, J j, fun x hx hxp => ?_, ?_⟩
  · obtain ⟨_, ⟨V, hV, rfl⟩, hxV, -⟩ :=
      X.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ x) isOpen_univ
    have h1 := (Scheme.IdealSheafData.mem_support_iff_of_mem (U := ⟨V, hV⟩) hxV).1 hx
    rw [Scheme.mem_zeroLocus_iff] at h1
    refine h1 _ (hmem ⟨V, hV⟩ Finset.univ) ?_
    have e : ((p ^ (∑ j, N j) : ℕ) : Γ(X, V)) =
        (X.presheaf.map (homOfLE le_top).op).hom ((p : Γ(X, ⊤)) ^ (∑ j, N j)) := by
      simp
    rw [e, Scheme.basicOpen_res]
    refine ⟨hxV, ?_⟩
    have htop : x ∈ (⊤ : X.Opens) := trivial
    show x ∈ X.basicOpen _
    rw [Scheme.mem_basicOpen _ _ _ htop, map_pow]
    exact ((Scheme.mem_basicOpen _ _ _ htop).1 hxp).pow _
  · intro W W' b ν hE w j hw
    have hw0 : b (ν w) ∈ U j := hw
    obtain ⟨V₁, f, hw₁, hf, hV₁⟩ := hE (ν w)
    obtain ⟨g, hgle, hwg⟩ := V₁.2.exists_basicOpen_le (V := V₁.1 ⊓ b ⁻¹ᵁ U j) ⟨ν w, hw₁, hw0⟩ hw₁
    have hDU : (W.affineBasicOpen g).1 ≤ b ⁻¹ᵁ U j := hgle.trans inf_le_right
    have hDV : (W.affineBasicOpen g).1 ≤ V₁.1 := W.basicOpen_le g
    have hfD : (W.presheaf.map (homOfLE hDV).op).hom f ∈ nonZeroDivisors Γ(W, (W.affineBasicOpen g).1) :=
      (GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen (W.affineBasicOpen g).2).1
        (((GlobalTheory.Cartier.isRegularFn_iff_of_isAffineOpen V₁.2).2 hf).resG hDV)
    have hI1 := ((∏ i, J i).comap b).map_ideal_basicOpen V₁ g
    rw [hV₁, Ideal.map_span, Set.image_singleton] at hI1
    have hI2 := comapIdealAffine (∏ i, J i) b ⟨U j, hU j⟩ (W.affineBasicOpen g) hDU
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j), Scheme.IdealSheafData.ideal_mul,
      Pi.mul_apply, Ideal.map_mul, hJU, Ideal.map_span, ← Set.range_comp] at hI2
    rw [← Finset.mul_prod_erase Finset.univ J (Finset.mem_univ j)] at hI1
    have hwD : ν w ∈ (W.affineBasicOpen g).1 := hwg
    obtain ⟨k, s, hsP, hdiv⟩ := exists_dvd_of_span_mul_eq
      (Ideal.comap (W.presheaf.germ (W.affineBasicOpen g).1 (ν w) hwD).hom (IsLocalRing.maximalIdeal _)) _ _
      (hI2.symm.trans hI1.symm) hfD
    have hsu : ν w ∈ W.basicOpen s := by
      rw [Scheme.mem_basicOpen _ _ _ hwD]
      by_contra hc
      exact hsP ((IsLocalRing.mem_maximalIdeal _).2 hc)
    have hED : W.basicOpen s ≤ (W.affineBasicOpen g).1 := W.basicOpen_le s
    obtain ⟨_, ⟨V, hVa, rfl⟩, hwV, hVE⟩ := W'.isBasis_affineOpens.exists_subset_of_mem_open
      (show w ∈ ν ⁻¹ᵁ W.basicOpen s from hsu) (ν ⁻¹ᵁ W.basicOpen s).isOpen
    have hVE' : V ≤ ν ⁻¹ᵁ W.basicOpen s := hVE
    have hV : V ≤ (ν ≫ b) ⁻¹ᵁ U j := fun x hx => hDU (hED (hVE' hx))
    refine ⟨V, hV, hwV, hVa, k, fun k' => ?_⟩
    have key : (b.appLE (U j) _ hDU ≫ W.presheaf.map (homOfLE hED).op) ≫ ν.appLE _ V hVE' =
        (ν ≫ b).appLE (U j) V hV := by
      rw [Scheme.Hom.appLE_map, Scheme.Hom.appLE_comp_appLE]
    have hu := W.toRingedSpace.isUnit_res_basicOpen s
    have h1 := map_dvd (W.presheaf.map (homOfLE hED).op).hom (hdiv k')
    rw [map_mul] at h1
    have h2 := hu.dvd_mul_left.1 h1
    have h3 := map_dvd (ν.appLE _ V hVE').hom h2
    rw [← key]
    simpa using h3

end GlobalTheory.Principalise
