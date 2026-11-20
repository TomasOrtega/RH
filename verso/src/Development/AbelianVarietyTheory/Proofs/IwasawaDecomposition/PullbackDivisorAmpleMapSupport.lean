import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.BlowPolSt
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NormalizedBlowupSeparated
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetOmIsLBOfAmple
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ClsLinCombSingle
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteFiberAmpleTorsionStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.DetBundleTrivialOnFibersStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.BlowupDivisorTrivialOnFibersStatement

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField IsLocalRing TopologicalSpace
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R Formalism.L2.Pj
open GlobalTheory.Toroidal GlobalTheory.Models GlobalTheory.LN GlobalTheory.ShFam GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.TorRef

namespace GlobalTheory.BlowQF

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Y ρ hjQ`. Establish `hiso : IsIso (genι Y)` using `by show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))`. Establish `: IsIso (spMap (RingHom.id c.F))` using `by show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))`. Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Use `infer_instance`.

Use `infer_instance`. Establish `: IsReduced Y.X` using `by haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by haveI := (Y.normal x).1 infer_instance`. Conclude with `isReduced_of_isReduced_stalk _`. Establish `: IsReduced (gen Y)` using `isReduced_of_isOpenImmersion (genι Y)`. Establish `: IsDominant Y.jQ` using `⟨Y.jQ_dense⟩`.

Use `ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) Y.jQ ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, hjQ]`. Conclude with `X.jQ_over.trans Y.jQ_over.symm`.
-/
theorem rho_over : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (ρ : gen Y ⟶ gen X),
    Y.jQ ≫ ρ = X.jQ → ρ ≫ genStr X = genStr Y := by
  intro E _ _ _ H D l Xo c X Y ρ hjQ
  have hiso : IsIso (genι Y) := by
    show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [CommRingCat.ofHom_id, Spec.map_id]
      infer_instance
    infer_instance
  have : IsReduced Y.X := by
    haveI : ∀ x : Y.X, _root_.IsReduced (Y.X.presheaf.stalk x) := fun x => by
      haveI := (Y.normal x).1
      infer_instance
    exact isReduced_of_isReduced_stalk _
  have : IsReduced (gen Y) := isReduced_of_isOpenImmersion (genι Y)
  have : IsDominant Y.jQ := ⟨Y.jQ_dense⟩
  refine ext_of_isDominant_of_isSeparated (terminal.from (Sp c.F)) (terminal.hom_ext _ _) Y.jQ ?_
  rw [← Category.assoc, hjQ]
  exact X.jQ_over.trans Y.jQ_over.symm

/- English proof (translation)
Introduce `E _ _ _ H D l Xo c X Y BY k n ρ X' b q hjQ hA hn hJ hB hq x`. Establish `hρ : ρ ≫ genStr X = genStr Y` using `rho_over E H D l Xo c X Y ρ hjQ`. Establish `hPY` using `isProper_genStr Y`. Establish `hPX` using `isProper_genStr X`. Establish `hρP : IsProper ρ`.

Establish `: IsProper (ρ ≫ genStr X)` using `hρ ▸ hPY`. Conclude with `IsProper.of_comp ρ (genStr X)`. Establish `hbs : IsSeparated (b ≫ X.s)`. Use `(blowup_finite_noeth_sep c.F X.X X' X' X.s _ b (𝟙 X') X.proj hB inferInstance).2` as an intermediate fact. Simplify using `using this`.

Set `T` to `pullback (b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F))`. Set `u : T ⟶ X'` to `pullback.fst _ _`. Establish `hw : q ≫ b ≫ X.s = genStr Y ≫ spMap (algebraMap (𝓞 c.F) c.F)`. Rewrite using `[← Category.assoc, hq, Category.assoc, pullback.condition, ← Category.assoc, hρ]`. Set `qF : gen Y ⟶ T` to `pullback.lift q (genStr Y) hw`.

Set `bF : T ⟶ gen X` to `pullback.lift (u ≫ b) (pullback.snd _ _) (by simp [u, pullback.condition])`. Establish `hqF : qF ≫ bF = ρ`. Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hq]`. Rewrite using `[Category.assoc, pullback.lift_snd, pullback.lift_snd, hρ]`.

Establish `hqu : qF ≫ u = q` using `pullback.lift_fst _ _ _`. Establish `hbF : IsSeparated bF`. Establish `: IsSeparated (bF ≫ genStr X)` using `by show IsSeparated (bF ≫ pullback.snd _ _)`. Rewrite using `[pullback.lift_snd]`. Use `infer_instance`.

Conclude with `IsSeparated.of_comp bF (genStr X)`. Establish `hqFP : IsProper qF`. Establish `: IsProper (qF ≫ bF)` using `hqF ▸ hρP`. Conclude with `IsProper.of_comp qF bF`. Establish `hu : Function.Injective u.base`.

Establish `: IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F))` using `IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))`. Establish `: IsPreimmersion u` using `inferInstance`. Conclude with `u.isEmbedding.injective`. Establish `hiso : IsIso (genι Y)` using `by show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))`. Establish `: IsIso (spMap (RingHom.id c.F))` using `by show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))`.

Rewrite using `[CommRingCat.ofHom_id, Spec.map_id]`. Use `infer_instance`. Use `infer_instance`. Establish `hD : (GlobalTheory.FlagMod.detOm Y).IsLB` using `GlobalTheory.PolDet.isLB_detOm_of_ample E H D l Xo c c.F (RingHom.id c.F) Y k BY hA`. Establish `hcls : GlobalTheory.CechPic.cls (polOf Y k BY) hA.isLB = k • GlobalTheory.CechPic.cls _ hD + -GlobalTheory.CechPic.cls _ BY.isLB_lb`.

Establish `h1` using `GlobalTheory.CechPic.cls_tens (isLB_lbPow hD k) (GlobalTheory.CechPic.isLB_dual BY.isLB_lb) hA.isLB`. Rewrite `h1` using `[GlobalTheory.CechPic.cls_lbPow hD, GlobalTheory.CechPic.cls_dual BY.isLB_lb]`. Conclude with `h1`. Establish `hfin : ∀ t : T, (qF ⁻¹' {t}).Finite`. Introduce `t`.

Use `GlobalTheory.T.finite_fiber_ample_torsion qF (genι Y) (polOf Y k BY) hqFP inferInstance hA t ⟨n, hn, ?_⟩` and prove the remaining obligations. Establish `hc : qF.fiberι t ≫ qF = qF.fiberToSpecResidueField t ≫ T.fromSpecResidueField t` using `pullback.condition`. Establish `h3` using `GlobalTheory.T.det_bundle_trivial_on_fibers E H D l Xo c X Y ρ hD hjQ (qF.fiber t) (T.residueField t) (qF.fiberι t) (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ bF) (by rw [← hqF, ← Category.assoc, hc, Category.assoc])`. Establish `hI : ((((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap b).comap q = (BY.idealSheaf ^ n).comap (genι Y)`. Rewrite using `[← Scheme.IdealSheafData.comap_comp, hq, hJ]`.

Establish `h4` using `GlobalTheory.T.blowup_divisor_trivial_on_fibers BY n (genι Y) q _ hiso hB.1 hI (qF.fiber t) (T.residueField t) (qF.fiberι t) (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ u) (by rw [← hqu, ← Category.assoc, hc, Category.assoc])`. Rewrite using `[hcls, map_nsmul, map_add, map_nsmul, map_neg, h3, smul_zero, zero_add, smul_neg, ← map_nsmul, h4, neg_zero]`. Distinguish the cases in `hx : ∃ t : T, u t = x`. Take `⟨t, rfl⟩` from `hx`. Use `(hfin t).subset fun p hp => ?_` and prove the remaining obligations.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff] at hp ⊢`. Rewrite `hp` using `[← hqu, Scheme.Hom.comp_apply]`. Conclude with `hu hp`. Use `Set.finite_empty` and compare the differences between its conclusion and the goal. Use extensionality with `p`.

Simplify using `only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]`. Introduce `hp`. Conclude with `hx ⟨qF p, by rw [← Scheme.Hom.comp_apply, hqu, hp]⟩`.
-/
theorem finite_preimage_of_blowup : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l : Level H) (Xo : Moduli D l)
    (c : Coeff l) (X : GMod Xo c) (Y : Model Xo c (RingHom.id c.F)) (BY : GlobalTheory.EffCartierData Y.X) (k n : ℕ)
    (ρ : gen Y ⟶ gen X) (X' : Scheme.{0}) (b : X' ⟶ X.X) (q : gen Y ⟶ X'),
    Y.jQ ≫ ρ = X.jQ → GlobalTheory.IsAmpleLB (polOf Y k BY) → 0 < n →
    (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap (ρ ≫ genι X) = (BY.idealSheaf ^ n).comap (genι Y) →
    FinalTheorems.Blowup b (((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)) → q ≫ b = ρ ≫ genι X →
    ∀ x : X', (q ⁻¹' {x}).Finite := by
  intro E _ _ _ H D l Xo c X Y BY k n ρ X' b q hjQ hA hn hJ hB hq x
  have hρ : ρ ≫ genStr X = genStr Y := rho_over E H D l Xo c X Y ρ hjQ
  have hPY := isProper_genStr Y
  have hPX := isProper_genStr X
  have hρP : IsProper ρ := by
    have : IsProper (ρ ≫ genStr X) := hρ ▸ hPY
    exact IsProper.of_comp ρ (genStr X)
  have hbs : IsSeparated (b ≫ X.s) := by
    have := (blowup_finite_noeth_sep c.F X.X X' X' X.s _ b (𝟙 X') X.proj hB inferInstance).2
    simpa using this
  let T := pullback (b ≫ X.s) (spMap (algebraMap (𝓞 c.F) c.F))
  let u : T ⟶ X' := pullback.fst _ _
  have hw : q ≫ b ≫ X.s = genStr Y ≫ spMap (algebraMap (𝓞 c.F) c.F) := by
    rw [← Category.assoc, hq, Category.assoc, pullback.condition, ← Category.assoc, hρ]
  let qF : gen Y ⟶ T := pullback.lift q (genStr Y) hw
  let bF : T ⟶ gen X := pullback.lift (u ≫ b) (pullback.snd _ _) (by simp [u, pullback.condition])
  have hqF : qF ≫ bF = ρ := by
    apply pullback.hom_ext
    · rw [Category.assoc, pullback.lift_fst, ← Category.assoc, pullback.lift_fst, hq]
    · rw [Category.assoc, pullback.lift_snd, pullback.lift_snd, hρ]
  have hqu : qF ≫ u = q := pullback.lift_fst _ _ _
  have hbF : IsSeparated bF := by
    have : IsSeparated (bF ≫ genStr X) := by
      show IsSeparated (bF ≫ pullback.snd _ _)
      rw [pullback.lift_snd]; infer_instance
    exact IsSeparated.of_comp bF (genStr X)
  have hqFP : IsProper qF := by
    have : IsProper (qF ≫ bF) := hqF ▸ hρP
    exact IsProper.of_comp qF bF
  have hu : Function.Injective u.base := by
    have : IsPreimmersion (spMap (algebraMap (𝓞 c.F) c.F)) :=
      IsPreimmersion.of_isLocalization (nonZeroDivisors (𝓞 c.F))
    have : IsPreimmersion u := inferInstance
    exact u.isEmbedding.injective
  have hiso : IsIso (genι Y) := by
    show IsIso (pullback.fst Y.s (spMap (RingHom.id c.F)))
    have : IsIso (spMap (RingHom.id c.F)) := by
      show IsIso (Spec.map (CommRingCat.ofHom (RingHom.id c.F)))
      rw [CommRingCat.ofHom_id, Spec.map_id]
      infer_instance
    infer_instance
  have hD : (GlobalTheory.FlagMod.detOm Y).IsLB := GlobalTheory.PolDet.isLB_detOm_of_ample E H D l Xo c c.F (RingHom.id c.F) Y k BY hA
  have hcls : GlobalTheory.CechPic.cls (polOf Y k BY) hA.isLB =
      k • GlobalTheory.CechPic.cls _ hD + -GlobalTheory.CechPic.cls _ BY.isLB_lb := by
    have h1 := GlobalTheory.CechPic.cls_tens (isLB_lbPow hD k) (GlobalTheory.CechPic.isLB_dual BY.isLB_lb) hA.isLB
    rw [GlobalTheory.CechPic.cls_lbPow hD, GlobalTheory.CechPic.cls_dual BY.isLB_lb] at h1
    exact h1
  have hfin : ∀ t : T, (qF ⁻¹' {t}).Finite := by
    intro t
    refine GlobalTheory.T.finite_fiber_ample_torsion qF (genι Y) (polOf Y k BY) hqFP inferInstance hA t ⟨n, hn, ?_⟩
    have hc : qF.fiberι t ≫ qF = qF.fiberToSpecResidueField t ≫ T.fromSpecResidueField t := pullback.condition
    have h3 := GlobalTheory.T.det_bundle_trivial_on_fibers E H D l Xo c X Y ρ hD hjQ (qF.fiber t) (T.residueField t) (qF.fiberι t)
      (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ bF)
      (by rw [← hqF, ← Category.assoc, hc, Category.assoc])
    have hI : ((((BY.idealSheaf ^ n).comap (genι Y)).map (ρ ≫ genι X)).comap b).comap q =
        (BY.idealSheaf ^ n).comap (genι Y) := by
      rw [← Scheme.IdealSheafData.comap_comp, hq, hJ]
    have h4 := GlobalTheory.T.blowup_divisor_trivial_on_fibers BY n (genι Y) q _ hiso hB.1 hI (qF.fiber t) (T.residueField t) (qF.fiberι t)
      (qF.fiberToSpecResidueField t) (T.fromSpecResidueField t ≫ u)
      (by rw [← hqu, ← Category.assoc, hc, Category.assoc])
    rw [hcls, map_nsmul, map_add, map_nsmul, map_neg, h3, smul_zero, zero_add, smul_neg, ← map_nsmul, h4, neg_zero]
  by_cases hx : ∃ t : T, u t = x
  · obtain ⟨t, rfl⟩ := hx
    refine (hfin t).subset fun p hp => ?_
    simp only [Set.mem_preimage, Set.mem_singleton_iff] at hp ⊢
    rw [← hqu, Scheme.Hom.comp_apply] at hp
    exact hu hp
  · convert Set.finite_empty
    ext p
    simp only [Set.mem_preimage, Set.mem_singleton_iff, Set.mem_empty_iff_false, iff_false]
    intro hp
    exact hx ⟨qF p, by rw [← Scheme.Hom.comp_apply, hqu, hp]⟩

end GlobalTheory.BlowQF
