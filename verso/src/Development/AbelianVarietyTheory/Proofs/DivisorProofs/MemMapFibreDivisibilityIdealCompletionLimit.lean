import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NonUnitAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.NonUnitAtOfNotIsUnit
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsCorrectionApproximateIdealSections
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SpecializesLiftClosedFibreStalkBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R GlobalTheory GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.ZH GlobalTheory.Poinc
open GlobalTheory.SiegelTor

noncomputable section

namespace GlobalTheory.FormalCorr

/- English proof (translation)
Assume the negation of the conclusion as `hv`. Use `set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ`. Establish `hZc : IsClosed Z`. Rewrite using `[← isOpen_compl_iff, isOpen_iff_forall_mem_open]`. Introduce `y hy`.

Establish `hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y`. Simplify `hy` using `[hZ]`. Take `⟨O, hyO, hO⟩` from `GlobalTheory.SpreadIdeal.exists_open_nhds_mem_stalkId P I s y hy'`. Conclude with `⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩`. Take `⟨w, hwZ, hw⟩` from `hZc.exists_closed_singleton ⟨v, hv⟩`.

Conclude with `hwZ (h w hw)`.
-/
theorem mem_stalkId_of_closedPoints (P : Scheme.{0}) [CompactSpace P] (I : P.IdealSheafData) (s : Γ(P, ⊤))
    (h : ∀ v : P, IsClosed ({v} : Set P) → (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v) (v : P) :
    (P.presheaf.germ ⊤ v trivial).hom s ∈ FinalTheorems.stalkId I v := by
  by_contra hv
  set Z : Set P := {y | (P.presheaf.germ ⊤ y trivial).hom s ∉ FinalTheorems.stalkId I y} with hZ
  have hZc : IsClosed Z := by
    rw [← isOpen_compl_iff, isOpen_iff_forall_mem_open]
    intro y hy
    have hy' : (P.presheaf.germ ⊤ y trivial).hom s ∈ FinalTheorems.stalkId I y := by
      simpa [hZ] using hy
    obtain ⟨O, hyO, hO⟩ := GlobalTheory.SpreadIdeal.exists_open_nhds_mem_stalkId P I s y hy'
    exact ⟨O, fun z hz => by simpa [hZ] using hO z hz, O.2, hyO⟩
  obtain ⟨w, hwZ, hw⟩ := hZc.exists_closed_singleton ⟨v, hv⟩
  exact hwZ (h w hw)

/- English proof (translation)
Establish `hξc : (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) (closedPoint R) = z`. Establish `: Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Y.presheaf.stalk z)` using `IsLocalRing.comap_closedPoint i`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Y.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)`. Establish `h1 : pullback.fst _ π v = closedPoint R`. Establish `hc : IsClosed ((pullback.fst _ π).base '' {v})` using `(pullback.fst _ π).isClosedMap _ hv`.

Rewrite `hc` using `[Set.image_singleton]`. Conclude with `((IsLocalRing.specializes_closedPoint _).mem_closed hc rfl).symm`. Use `⟨h1, ?_⟩` and prove the remaining obligations. Establish `hx : π (pullback.snd _ π v) = z`. Rewrite using `[← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, h1, hξc]`.

Use `closure_subset_iff_isClosed.1 fun y hy => ?_` and prove the remaining obligations. Establish `hvy : pullback.snd _ π v ⤳ y` using `specializes_iff_mem_closure.2 hy`. Establish `hy' : π y = z`. Establish `: z ⤳ π y` using `hx ▸ hvy.map π.continuous`. Conclude with `(hz.closure_eq ▸ specializes_iff_mem_closure.1 this : π y ∈ ({z} : Set Y))`.

Take `⟨w, hvw, hw⟩` from `GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk π z R i hi v y h1 hvy hy'`. Establish `: w = v` using `(hv.closure_eq ▸ specializes_iff_mem_closure.1 hvw : w ∈ ({v} : Set _))`. Rewrite using `[← hw, this]`. Both sides reduce to the same expression.
-/
theorem closed_of_closed {X Y : Scheme.{0}} (π : X ⟶ Y) [UniversallyClosed π] (z : Y) (hz : IsClosed ({z} : Set Y))
    (R : Type) [CommRing R] [IsLocalRing R] (i : Y.presheaf.stalk z →+* R) [IsLocalHom i]
    (hi : Function.Surjective (ResidueField.map i))
    (v : ↥(pullback (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π)) (hv : IsClosed ({v} : Set _)) :
    pullback.fst (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v = closedPoint R ∧
      IsClosed ({pullback.snd (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) π v} : Set X) := by
  have hξc : (Spec.map (CommRingCat.ofHom i) ≫ Y.fromSpecStalk z) (closedPoint R) = z := by
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Y.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Y.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  have h1 : pullback.fst _ π v = closedPoint R := by
    have hc : IsClosed ((pullback.fst _ π).base '' {v}) := (pullback.fst _ π).isClosedMap _ hv
    rw [Set.image_singleton] at hc
    exact ((IsLocalRing.specializes_closedPoint _).mem_closed hc rfl).symm
  refine ⟨h1, ?_⟩
  have hx : π (pullback.snd _ π v) = z := by
    rw [← Scheme.Hom.comp_apply, ← pullback.condition, Scheme.Hom.comp_apply, h1, hξc]
  refine closure_subset_iff_isClosed.1 fun y hy => ?_
  have hvy : pullback.snd _ π v ⤳ y := specializes_iff_mem_closure.2 hy
  have hy' : π y = z := by
    have : z ⤳ π y := hx ▸ hvy.map π.continuous
    exact (hz.closure_eq ▸ specializes_iff_mem_closure.1 this : π y ∈ ({z} : Set Y))
  obtain ⟨w, hvw, hw⟩ := GlobalTheory.T.exists_specializes_lift_pullback_snd_fromSpecStalk π z R i hi v y h1 hvy hy'
  have : w = v := (hv.closure_eq ▸ specializes_iff_mem_closure.1 hvw : w ∈ ({v} : Set _))
  rw [← hw, this]
  rfl

/- English proof (translation)
Rewrite using `[← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]`. Establish `hcl` using `fun v hv => closed_of_closed π z hz R i hres v hv`. Generalize the expression as in `hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ at hcl`. Establish `hfl : Flat ξ`. Rewrite using `[← hξ]`.

Use `haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z`. Use `haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi`. Use `infer_instance`. Establish `hξc : ξ (closedPoint R) = z`. Rewrite using `[← hξ]`.

Establish `: Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z)` using `IsLocalRing.comap_closedPoint i`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)`. Use `GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_` and prove the remaining obligations. Rewrite using `[Scheme.stalkClosedPointTo, CommRingCat.hom_comp]`. Conclude with `RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))`.

Use `haveI : CompactSpace ↥(Limits.pullback ξ π : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst ξ π)`. Use `mem_stalkId_of_closedPoints _ _ _ fun v hvc => ?_` and prove the remaining obligations. Take `⟨hv, hqc⟩` from `hcl v hvc`. Use `haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)`. Use `set p := Limits.pullback.fst ξ π with hp`.

Use `set q := Limits.pullback.snd ξ π with hq`. Establish `hpq : p ≫ ξ = q ≫ π` using `Limits.pullback.condition`. Establish `hx : π (q v) = z`. Rewrite using `[← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]`. Take `⟨ψ, hψ, hψc⟩` from `ApproxCorr.exists_stalk_map π (q v) z hx`.

Set `α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v` to `((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v`. Establish `hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p`. Rewrite using `[Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]`. Use `haveI : IsLocalHom α.hom := by`. Use `(IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `Spec.map α (closedPoint _) = _`. Rewrite using `[hα]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)`. Use `haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v`. Establish `hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v`.

Use `Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)` and prove the remaining obligations. Rewrite using `[Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]`. Use `erw [hψc]`. Rewrite using `[Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]`. Establish `hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t)` using `fun t => congrArg (fun f => f.hom t) hc`.

Establish `e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F` using `(Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm`. Rewrite using `[e]`. Use `ApproxCorr.mem_of_forall_mem_sup _ _ fun k => ?_` and prove the remaining obligations. Take `⟨N, hN⟩` from `H (q v) ψ hψ hψc hx hqc k`. Take `⟨b, hb, c, hc2, hbc⟩` from `Submodule.mem_sup.1 (hN (max N k) (le_max_left _ _))`.

Establish `e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a (max N k))))`. Rewrite using `[← add_assoc, ← map_add, hbc, ← hc', map_sub]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e2]`. Conclude with `Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb)) (add_mem (ApproxCorr.map_mem_pow _ hc2) (Ideal.pow_le_pow_right (le_max_right N k) (ApproxCorr.map_mem_pow _ (ha _))))`.
-/
theorem mem_map_of_approx_closed {Z S : Scheme.{0}} (π : S ⟶ Z) [IsProper π] (I : S.IdealSheafData) (z : Z)
    (hz : IsClosed ({z} : Set Z))
    {R : Type} [CommRing R] [IsLocalRing R] [IsNoetherianRing R] (i : Z.presheaf.stalk z →+* R) [IsLocalHom i]
    (hi : i.Flat) (hres : Function.Surjective (ResidueField.map i))
    (F : R) (a : ℕ → Z.presheaf.stalk z) (ha : ∀ n, F - i (a n) ∈ maximalIdeal R ^ n)
    (H : ∀ (x : S) (ψ : Z.presheaf.stalk z →+* S.presheaf.stalk x), IsLocalHom ψ →
      spMap ψ ≫ Z.fromSpecStalk z = S.fromSpecStalk x ≫ π → π x = z → IsClosed ({x} : Set S) →
      ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ψ (a n) ∈ FinalTheorems.stalkId I x ⊔ maximalIdeal _ ^ e) :
    F ∈ (FinalTheorems.stalkId (I.map π) z).map i := by
  rw [← GlobalTheory.PolDiv.idlAlong_fromSpecStalk]
  have hcl := fun v hv => closed_of_closed π z hz R i hres v hv
  generalize hξ : Spec.map (CommRingCat.ofHom i) ≫ Z.fromSpecStalk z = ξ at hcl
  have hfl : Flat ξ := by
    rw [← hξ]
    haveI := GlobalTheory.LocalRingGeneralisation.flat_fromSpecStalk Z z
    haveI : Flat (Spec.map (CommRingCat.ofHom i)) := (HasRingHomProperty.Spec_iff (P := @Flat)).2 hi
    infer_instance
  have hξc : ξ (closedPoint R) = z := by
    rw [← hξ]
    have : Spec.map (CommRingCat.ofHom i) (closedPoint R) = closedPoint (Z.presheaf.stalk z) :=
      IsLocalRing.comap_closedPoint i
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg (Z.fromSpecStalk z) this).trans Scheme.fromSpecStalk_closedPoint)
  refine GlobalTheory.FlatPush.mem_idlAlong_map_of_flat π I ξ ?_ F ?_
  · rw [Scheme.stalkClosedPointTo, CommRingCat.hom_comp]
    exact RingHom.Flat.comp (Flat.stalkMap ξ _) (RingHom.Flat.of_bijective (ConcreteCategory.bijective_of_isIso _))
  haveI : CompactSpace ↥(Limits.pullback ξ π : Scheme.{0}) := QuasiCompact.compactSpace_of_compactSpace (Limits.pullback.fst ξ π)
  refine mem_stalkId_of_closedPoints _ _ _ fun v hvc => ?_
  obtain ⟨hv, hqc⟩ := hcl v hvc
  haveI : IsLocallyNoetherian (Limits.pullback ξ π) := LocallyOfFiniteType.isLocallyNoetherian (Limits.pullback.fst ξ π)
  set p := Limits.pullback.fst ξ π with hp
  set q := Limits.pullback.snd ξ π with hq
  have hpq : p ≫ ξ = q ≫ π := Limits.pullback.condition
  have hx : π (q v) = z := by
    rw [← Scheme.Hom.comp_apply, ← hpq, Scheme.Hom.comp_apply, hv, hξc]
  obtain ⟨ψ, hψ, hψc⟩ := ApproxCorr.exists_stalk_map π (q v) z hx
  let α : CommRingCat.of R ⟶ (Limits.pullback ξ π).presheaf.stalk v :=
    ((Scheme.ΓSpecIso (CommRingCat.of R)).inv ≫ (Sp R).presheaf.germ ⊤ (p v) trivial) ≫ p.stalkMap v
  have hα : Spec.map α = (Limits.pullback ξ π).fromSpecStalk v ≫ p := by
    rw [Spec.map_comp, ← Spec.fromSpecStalk_eq, Scheme.SpecMap_stalkMap_fromSpecStalk]
  haveI : IsLocalHom α.hom := by
    refine (IsLocalRing.isLocalHom_iff_comap_closedPoint _).2 ?_
    change Spec.map α (closedPoint _) = _
    rw [hα]
    exact (Scheme.Hom.comp_apply _ _ _).trans ((congrArg p Scheme.fromSpecStalk_closedPoint).trans hv)
  haveI : IsLocalHom (q.stalkMap v).hom := q.toLRSHom.prop v
  have hc : CommRingCat.ofHom i ≫ α = CommRingCat.ofHom ψ ≫ q.stalkMap v := by
    refine Spec.map_injective ((cancel_mono (Z.fromSpecStalk z)).1 ?_)
    rw [Spec.map_comp _ α, Spec.map_comp _ (q.stalkMap v), Category.assoc, Category.assoc, hξ, hα, Category.assoc, hpq]
    erw [hψc]
    rw [Scheme.SpecMap_stalkMap_fromSpecStalk_assoc]
  have hc' : ∀ t, α.hom (i t) = (q.stalkMap v).hom (ψ t) := fun t => congrArg (fun f => f.hom t) hc
  have e : ((Limits.pullback ξ π).presheaf.germ ⊤ v trivial).hom (p.appTop.hom
      ((Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom F)) = α.hom F :=
    (Scheme.Hom.germ_stalkMap_apply p ⊤ v trivial _).symm
  rw [e]
  refine ApproxCorr.mem_of_forall_mem_sup _ _ fun k => ?_
  obtain ⟨N, hN⟩ := H (q v) ψ hψ hψc hx hqc k
  obtain ⟨b, hb, c, hc2, hbc⟩ := Submodule.mem_sup.1 (hN (max N k) (le_max_left _ _))
  have e2 : α.hom F = (q.stalkMap v).hom b + ((q.stalkMap v).hom c + α.hom (F - i (a (max N k)))) := by
    rw [← add_assoc, ← map_add, hbc, ← hc', map_sub]; ring
  rw [e2]
  exact Submodule.add_mem_sup (GlobalTheory.VanStalk.map_le_stalkId_comap q I v (Ideal.mem_map_of_mem _ hb))
    (add_mem (ApproxCorr.map_mem_pow _ hc2)
      (Ideal.pow_le_pow_right (le_max_right N k) (ApproxCorr.map_mem_pow _ (ha _))))

end GlobalTheory.FormalCorr

namespace GlobalTheory.FormalCorr

variable {o Ω : Type} [CommRing o] [Field Ω] [Algebra o Ω]

/- English proof (translation)
Take `⟨U, hU, f, rfl⟩` from `M₁.Z.presheaf.germ_exist t`. Rewrite using `[Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ]`. Conclude with `(RatModel.stalkHom_germ (M := M) (show x ∈ π ⁻¹ᵁ U from hU) _).trans (by rw [hπ.valF_app ⟨_, hU⟩]; rfl)`.
-/
theorem stalkHom_stalkMap {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z} (hπ : M₁.IsHom M (AlgHom.id o Ω) π) (x : M.Z)
    (t : M₁.Z.presheaf.stalk (π x)) : M.stalkHom x ((π.stalkMap x).hom t) = M₁.stalkHom (π x) t := by
  obtain ⟨U, hU, f, rfl⟩ := M₁.Z.presheaf.germ_exist t
  rw [Scheme.Hom.germ_stalkMap_apply, RatModel.stalkHom_germ]
  exact (RatModel.stalkHom_germ (M := M) (show x ∈ π ⁻¹ᵁ U from hU) _).trans (by rw [hπ.valF_app ⟨_, hU⟩]; rfl)

/- English proof (translation)
Use `GlobalTheory.FibreCorr.mem_fibreIdeal.2 ?_` and prove the remaining obligations. Introduce and unpack `x' hx' f' ⟨j, hj, hf'⟩`. Substitute `hx'` using the available equality. Establish `h1 : FinalTheorems.stalkId ((D.idealSheaf.map π).comap π) x' ≤ FinalTheorems.stalkId D.idealSheaf x'` using `iSup₂_mono fun U hx => Ideal.map_mono (Scheme.IdealSheafData.comap_map_le D.idealSheaf π U)`. Establish `h2 : (π.stalkMap x').hom t ∈ FinalTheorems.stalkId D.idealSheaf x'`.

Use `h1 ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.VanStalk.stalkId_comap]`. Conclude with `Ideal.mem_map_of_mem _ ht`. Rewrite `h2` using `[D.stalkId_idealSheaf j x' hj, Ideal.mem_span_singleton']`. Take `⟨r, hr⟩` from `h2`.

Establish `h3 : (M₁.stalkEquiv (π x') t : Ω) = M.stalkHom x' r * f'`. Rewrite using `[RatModel.coe_stalkEquiv, ← stalkHom_stalkMap hπ, ← hr, map_mul, RatModel.stalkHom_germ, hf']`. Rewrite using `[h3]`. Distinguish the cases in `h0 : f' = 0`. Rewrite using `[h0, div_zero]`.

Conclude with `zero_mem _`. Rewrite using `[mul_div_cancel_right₀ _ h0]`. Conclude with `(M.stalkEquiv x' r).2`.
-/
theorem stalkEquiv_mem_fibreIdeal {M₁ M : RatModel o Ω} {π : M.Z ⟶ M₁.Z} (hπ : M₁.IsHom M (AlgHom.id o Ω) π)
    (D : EffCartierData M.Z) (z : M₁.Z) (t : M₁.Z.presheaf.stalk z) (ht : t ∈ FinalTheorems.stalkId (D.idealSheaf.map π) z) :
    M₁.stalkEquiv z t ∈ GlobalTheory.FibreCorr.fibreIdeal hπ D z := by
  refine GlobalTheory.FibreCorr.mem_fibreIdeal.2 ?_
  rintro x' hx' f' ⟨j, hj, hf'⟩
  subst hx'
  have h1 : FinalTheorems.stalkId ((D.idealSheaf.map π).comap π) x' ≤ FinalTheorems.stalkId D.idealSheaf x' :=
    iSup₂_mono fun U hx => Ideal.map_mono (Scheme.IdealSheafData.comap_map_le D.idealSheaf π U)
  have h2 : (π.stalkMap x').hom t ∈ FinalTheorems.stalkId D.idealSheaf x' := by
    refine h1 ?_
    rw [GlobalTheory.VanStalk.stalkId_comap]
    exact Ideal.mem_map_of_mem _ ht
  rw [D.stalkId_idealSheaf j x' hj, Ideal.mem_span_singleton'] at h2
  obtain ⟨r, hr⟩ := h2
  have h3 : (M₁.stalkEquiv (π x') t : Ω) = M.stalkHom x' r * f' := by
    rw [RatModel.coe_stalkEquiv, ← stalkHom_stalkMap hπ, ← hr, map_mul, RatModel.stalkHom_germ, hf']
  rw [h3]
  by_cases h0 : f' = 0
  · rw [h0, div_zero]; exact zero_mem _
  · rw [mul_div_cancel_right₀ _ h0]; exact (M.stalkEquiv x' r).2

end GlobalTheory.FormalCorr

/- English proof (translation)
Introduce `o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn D z hz F a ha H`. Use `haveI := hprop`. Use `haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z`. Use `haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (M₁.O z))`. Set `e` to `M₁.stalkEquiv z`.

Set `i : M₁.Z.presheaf.stalk z →+* AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)` to `(algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom`. Use `haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm⟩`. Use `haveI : IsLocalHom i := inferInstance`. Establish `hfl : i.Flat` using `RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective) (RingHom.flat_algebraMap_iff.2 inferInstance)`. Establish `hres : Function.Surjective (ResidueField.map i)`.

Introduce `y`. Take `⟨r, rfl⟩` from `(AdicCompletion.residueField_map_bijective (M₁.O z)).2 y`. Take `⟨s, rfl⟩` from `IsLocalRing.residue_surjective r`. Use `⟨IsLocalRing.residue _ (e.symm s), ?_⟩` and prove the remaining obligations. Simplify using `[i, ResidueField.map_residue]`.

Establish `key` using `GlobalTheory.FormalCorr.mem_map_of_approx_closed π D.idealSheaf z hz i hfl hres F (fun n => e.symm (a n)) (fun n => by`. Establish `h` using `ha n`. Rewrite `h` using `[← AdicCompletion.maximalIdeal_eq_map]`. Simplify `h) ?_` using `[i]`. Rewrite `key` using `[show i = (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom from rfl, ← Ideal.map_map]`.

Conclude with `Ideal.map_mono (Ideal.map_le_iff_le_comap.2 fun t ht => Ideal.mem_comap.2 (GlobalTheory.FormalCorr.stalkEquiv_mem_fibreIdeal hπ D z t ht)) key`. Introduce `x ψ hψ hc hx hcl k`. Substitute `hx` using the available equality. Establish `hψe : ψ = (π.stalkMap x).hom`. Establish `h` using `Spec.map_injective ((cancel_mono (M₁.Z.fromSpecStalk (π x))).1 (hc.trans (Scheme.SpecMap_stalkMap_fromSpecStalk π).symm))`.

Conclude with `congrArg CommRingCat.Hom.hom h`. Substitute `hψe` using the available equality. Take `⟨j, hj⟩ : ∃ j, x ∈ D.U j` from `TopologicalSpace.Opens.mem_iSup.1 (D.cover ▸ trivial)`. Take `⟨N, hN⟩` from `H x rfl hcl _ ⟨j, hj, rfl⟩ k`. Use `⟨N, fun n hn => ?_⟩` and prove the remaining obligations.

Take `⟨c, d, hcd, hd⟩` from `hN n hn`. Set `E` to `M.stalkEquiv x`. Use `haveI : IsLocalHom E.symm.toRingHom := ⟨fun a ha => by simpa using ha.map E⟩`. Establish `hw : (π.stalkMap x).hom (e.symm (a n)) = E.symm c * (M.Z.presheaf.germ _ x hj).hom (D.f j) + E.symm d`. Apply `E.injective` to reduce the goal to its premises.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[map_add, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RatModel.stalkEquiv_germ]`. Simplify using `only [Subalgebra.coe_add, Subalgebra.coe_mul]`. Rewrite using `[RatModel.coe_stalkEquiv, GlobalTheory.FormalCorr.stalkHom_stalkMap hπ, ← RatModel.coe_stalkEquiv, RingEquiv.apply_symm_apply, hcd]`. Rewrite using `[hw, D.stalkId_idealSheaf j x hj]`.

Use `Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)) ?_` and prove the remaining obligations. Conclude with `ApproxCorr.map_mem_pow E.symm.toRingHom hd`.
-/
theorem GlobalTheory.FormalCorr.mem_map_fibreIdeal : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (M₁ M : RatModel o Ω) (π : M.Z ⟶ M₁.Z) (hπ : M₁.IsHom M (AlgHom.id o Ω) π), IsProper π → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M₁.Z → ReciprocityTheory.ChartRestriction.G.Geo.Tor.IsNormalScheme M.Z → ∀ (D : EffCartierData M.Z) (z : M₁.Z), IsClosed ({z} : Set M₁.Z) → ∀ (F : AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a : ℕ → M₁.O z), (∀ n, F - algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z)) (a n) ∈ (maximalIdeal (M₁.O z)).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) ^ n) → (∀ x' : M.Z, π x' = z → IsClosed ({x'} : Set M.Z) → ∀ f', EqAt M D x' f' → ∀ e : ℕ, ∃ N : ℕ, ∀ n, N ≤ n → ∃ c d : M.O x', (a n : Ω) = c * f' + d ∧ d ∈ maximalIdeal (M.O x') ^ e) → F ∈ (GlobalTheory.FibreCorr.fibreIdeal hπ D z).map (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))) := by
  intro o Ω _ _ _ _ M₁ M π hπ hprop hn₁ hn D z hz F a ha H
  haveI := hprop
  haveI := GlobalTheory.FibreCorr.isNoetherianRing_O M₁ z
  haveI := GlobalTheory.AdicNoeth.isNoetherianRing_adicCompletion _ (maximalIdeal (M₁.O z))
  let e := M₁.stalkEquiv z
  let i : M₁.Z.presheaf.stalk z →+* AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z) :=
    (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom
  haveI : IsLocalHom e.toRingHom := ⟨fun a ha => by simpa using ha.map e.symm⟩
  haveI : IsLocalHom i := inferInstance
  have hfl : i.Flat := RingHom.Flat.comp (RingHom.Flat.of_bijective e.bijective)
    (RingHom.flat_algebraMap_iff.2 inferInstance)
  have hres : Function.Surjective (ResidueField.map i) := by
    intro y
    obtain ⟨r, rfl⟩ := (AdicCompletion.residueField_map_bijective (M₁.O z)).2 y
    obtain ⟨s, rfl⟩ := IsLocalRing.residue_surjective r
    refine ⟨IsLocalRing.residue _ (e.symm s), ?_⟩
    simp [i, ResidueField.map_residue]
  have key := GlobalTheory.FormalCorr.mem_map_of_approx_closed π D.idealSheaf z hz i hfl hres F (fun n => e.symm (a n))
    (fun n => by
      have h := ha n
      rw [← AdicCompletion.maximalIdeal_eq_map] at h
      simpa [i] using h) ?_
  · rw [show i = (algebraMap (M₁.O z) (AdicCompletion (maximalIdeal (M₁.O z)) (M₁.O z))).comp e.toRingHom from rfl,
      ← Ideal.map_map] at key
    exact Ideal.map_mono (Ideal.map_le_iff_le_comap.2 fun t ht =>
      Ideal.mem_comap.2 (GlobalTheory.FormalCorr.stalkEquiv_mem_fibreIdeal hπ D z t ht)) key
  · intro x ψ hψ hc hx hcl k
    subst hx
    have hψe : ψ = (π.stalkMap x).hom := by
      have h := Spec.map_injective ((cancel_mono (M₁.Z.fromSpecStalk (π x))).1
        (hc.trans (Scheme.SpecMap_stalkMap_fromSpecStalk π).symm))
      exact congrArg CommRingCat.Hom.hom h
    subst hψe
    obtain ⟨j, hj⟩ : ∃ j, x ∈ D.U j := TopologicalSpace.Opens.mem_iSup.1 (D.cover ▸ trivial)
    obtain ⟨N, hN⟩ := H x rfl hcl _ ⟨j, hj, rfl⟩ k
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨c, d, hcd, hd⟩ := hN n hn
    let E := M.stalkEquiv x
    haveI : IsLocalHom E.symm.toRingHom := ⟨fun a ha => by simpa using ha.map E⟩
    have hw : (π.stalkMap x).hom (e.symm (a n)) =
        E.symm c * (M.Z.presheaf.germ _ x hj).hom (D.f j) + E.symm d := by
      apply E.injective
      apply Subtype.ext
      rw [map_add, map_mul, RingEquiv.apply_symm_apply, RingEquiv.apply_symm_apply, RatModel.stalkEquiv_germ]
      simp only [Subalgebra.coe_add, Subalgebra.coe_mul]
      rw [RatModel.coe_stalkEquiv, GlobalTheory.FormalCorr.stalkHom_stalkMap hπ, ← RatModel.coe_stalkEquiv,
        RingEquiv.apply_symm_apply, hcd]
    rw [hw, D.stalkId_idealSheaf j x hj]
    refine Submodule.add_mem_sup (Ideal.mul_mem_left _ _ (Ideal.subset_span rfl)) ?_
    exact ApproxCorr.map_mem_pow E.symm.toRingHom hd
