import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.PublishedTheorems.SemiabelianTori.GeometricallyConnectedSplitTorusAff
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.LocallyOfFinitePresentationDiagMap
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.HomBaseChangeBijectiveOfLeNilradical
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.SplitTorusHomProperTrivialLocal
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.BijectiveRestrictPointsOfEtaleOfHenselian
import Development.AbelianVarietyTheory.Definitions.ShimuraVarieties.PowObjGeometricallyConnected
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj CategoryTheory.MonObj
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Pdiv ReciprocityTheory.ChartRestriction.G.Pdiv.AvDefs
open GlobalTheory.IndefiniteRowSideFullHecke.LieAlgebraMaps (torus lieMap lieAdd LieCongr IsLieLinear lieCoord)

namespace GlobalTheory.TorusFieldCrit

/- English proof (translation)
Take `⟨y, hy⟩` from `not_forall.1 hM`. Establish `hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range)` using `⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩`. Use `haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance`. Take `⟨n, κ, _, p, hp, e, ⟨f⟩⟩` from `AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)`. It suffices to establish `h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by`.

Take `⟨q, hq, ψ, hψ⟩` from `h`. Use `haveI := Fact.mk hq`. Use `⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `hψ 1`. Take `⟨z, rfl⟩` from `QuotientAddGroup.mk'_surjective M.range x`.

Use `DFunLike.congr_fun h z` as an intermediate fact. Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this`. Rewrite `hx` using `[this]`. Conclude with `zero_ne_one hx`. Use extensionality with `x`.

Simplify using `[(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]`. Distinguish the cases in `hn : 0 < n`. Use `⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩` and prove the remaining obligations. Introduce `z`. Take `⟨k, rfl⟩` from `ZMod.intCast_surjective z`.

Use `⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩` and prove the remaining obligations. Simplify using the standard rewrite rules. Establish `hn0 : n = 0` using `by omega`. Substitute `hn0` using the available equality. Choose the witnesses or unpack the hypotheses as in `⟨i, hi⟩ : ∃ i, e i ≠ 0 := by`.

Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply `not_subsingleton ((Fin r → ℤ) ⧸ M.range)` to reduce the goal to its premises. Use `⟨fun a b => f.injective ?_⟩` and prove the remaining obligations. Establish `key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0` using `fun x => by`.

Use `Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)` and prove the remaining obligations. Use `haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance`. Conclude with `Subsingleton.elim _ _`. Rewrite using `[key (f a), key (f b)]`. Use `haveI := Fact.mk (hp i)`.

Use `⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩` and prove the remaining obligations. Introduce `z`. Take `⟨k, rfl⟩` from `ZMod.intCast_surjective z`. Use `⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩` and prove the remaining obligations. Simplify using `only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom, AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe, DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]`.

Conclude with `ZMod.cast_intCast (dvd_pow_self (p i) hi) k`.
-/
theorem exists_prime_hom_of_not_surjective {X : Type} [AddCommGroup X] {r : ℕ}
    (M : X →+ (Fin r → ℤ)) (hM : ¬ Function.Surjective M) :
    ∃ p : ℕ, p.Prime ∧ ∃ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 ∧ φ.comp M = 0 := by
  obtain ⟨y, hy⟩ := not_forall.1 hM
  have hQ : Nontrivial ((Fin r → ℤ) ⧸ M.range) :=
    ⟨⟨(y : (Fin r → ℤ) ⧸ M.range), 0, fun h => hy ((QuotientAddGroup.eq_zero_iff y).1 h)⟩⟩
  haveI : AddGroup.FG ((Fin r → ℤ) ⧸ M.range) := inferInstance
  obtain ⟨n, κ, _, p, hp, e, ⟨f⟩⟩ := AddCommGroup.equiv_free_prod_directSum_zmod ((Fin r → ℤ) ⧸ M.range)
  suffices h : ∃ q, q.Prime ∧ ∃ ψ : ((Fin r → ℤ) ⧸ M.range) →+ ZMod q, Function.Surjective ψ by
    obtain ⟨q, hq, ψ, hψ⟩ := h
    haveI := Fact.mk hq
    refine ⟨q, hq, ψ.comp (QuotientAddGroup.mk' M.range), fun h => ?_, ?_⟩
    · obtain ⟨x, hx⟩ := hψ 1
      obtain ⟨z, rfl⟩ := QuotientAddGroup.mk'_surjective M.range x
      have := DFunLike.congr_fun h z
      simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddMonoidHom.zero_apply] at this
      rw [this] at hx
      exact zero_ne_one hx
    · ext x
      simp [(QuotientAddGroup.eq_zero_iff _).2 (AddMonoidHom.mem_range.2 ⟨x, rfl⟩)]
  by_cases hn : 0 < n
  · refine ⟨2, Nat.prime_two, ((Int.castAddHom (ZMod 2)).comp
        ((Finsupp.applyAddHom (⟨0, hn⟩ : Fin n)).comp (AddMonoidHom.fst _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (Finsupp.single ⟨0, hn⟩ k, 0), ?_⟩
    simp
  · have hn0 : n = 0 := by omega
    subst hn0
    obtain ⟨i, hi⟩ : ∃ i, e i ≠ 0 := by
      by_contra h
      push_neg at h
      apply not_subsingleton ((Fin r → ℤ) ⧸ M.range)
      refine ⟨fun a b => f.injective ?_⟩
      have key : ∀ x : (Fin 0 →₀ ℤ) × DirectSum κ (fun j ↦ ZMod (p j ^ e j)), x = 0 := fun x => by
        refine Prod.ext (Finsupp.ext fun j => j.elim0) (DFinsupp.ext fun j => ?_)
        haveI : Subsingleton (ZMod (p j ^ e j)) := by rw [h j, pow_zero]; infer_instance
        exact Subsingleton.elim _ _
      rw [key (f a), key (f b)]
    classical
    haveI := Fact.mk (hp i)
    refine ⟨p i, hp i, ((ZMod.castHom (dvd_pow_self (p i) hi) (ZMod (p i))).toAddMonoidHom.comp
      ((DirectSum.component ℤ κ (fun j => ZMod (p j ^ e j)) i).toAddMonoidHom.comp
        (AddMonoidHom.snd _ _))).comp f.toAddMonoidHom, ?_⟩
    intro z
    obtain ⟨k, rfl⟩ := ZMod.intCast_surjective z
    refine ⟨f.symm (0, DirectSum.lof ℤ κ (fun j => ZMod (p j ^ e j)) i (k : ZMod (p i ^ e i))), ?_⟩
    simp only [AddMonoidHom.coe_comp, Function.comp_apply, AddEquiv.coe_toAddMonoidHom,
      AddEquiv.apply_symm_apply, AddMonoidHom.coe_snd, LinearMap.toAddMonoidHom_coe,
      DirectSum.component.lof_self, RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, ZMod.castHom_apply]
    exact ZMod.cast_intCast (dvd_pow_self (p i) hi) k

/- English proof (translation)
Use `letI := E.addCommGroup`. Use `letI := E.grpB`. Use `haveI := E.free`. Use `haveI := E.finite`. Use `haveI := E.i_hom`.

Use `haveI := E.q_hom`. Use `haveI := E.isAbelian.proper`. Use `haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω`. Establish `h1 : v ≫ E.q = toUnit _ ≫ η[E.B]` using `GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance`. Set `w` to `E.isKernel.lift v (toUnit _) h1`.

Establish `hw : w ≫ E.i = v` using `E.isKernel.lift_fst _ _ _`. Establish `hmono : Mono E.i` using `⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩`. Use `haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by`. Rewrite using `[← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw, MonObj.mul_comp]`. Take `⟨M, hM⟩` from `GlobalTheory.SplitTorus.exists_eq_torusMap w`.

Distinguish the cases in `hs : Function.Surjective M`. Establish `hdiag : w = GlobalTheory.Diag.diagMap _ M`. Rewrite using `[hM]`. Use `symm`. Conclude with `(GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b`.

Establish `hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left` using `GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])`. Establish `hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left` using `E.isKernel.map (Over.forget _)`. Establish `hi : IsClosedImmersion E.i.left` using `MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη`. Establish `hw' : IsClosedImmersion w.left` using `hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs`. Rewrite using `[← hw, Over.comp_left]`.

Use `infer_instance`. It suffices to derive a contradiction. Take `⟨p, hp, φ, hφ, hφM⟩` from `exists_prime_hom_of_not_surjective M hs`. Apply `hker p hp φ hφ` to reduce the goal to its premises. Rewrite using `[← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero, MonObj.one_comp]`.
-/
theorem isClosedImmersion_of_torusExtension (Ω : Type) [Field Ω] (H : Over (Spec (CommRingCat.of Ω)))
    [GrpObj H] (E : TorusExtension H) (r : ℕ) (v : splitTorus (Spec (CommRingCat.of Ω)) (Fin r → ℤ) ⟶ H)
    (hv : IsMonHom v)
    (hker : ∀ (p : ℕ), p.Prime → ∀ φ : (Fin r → ℤ) →+ ZMod p, φ ≠ 0 →
      GlobalTheory.SplitTorus.torusMap (Spec (CommRingCat.of Ω)) φ ≫ v ≠ 1) :
    IsClosedImmersion v.left := by
  letI := E.addCommGroup; letI := E.grpB
  haveI := E.free; haveI := E.finite
  haveI := E.i_hom; haveI := E.q_hom; haveI := E.isAbelian.proper
  haveI : ConnectedSpace (Spec (CommRingCat.of Ω)) := GlobalTheory.SplitTorus.connectedSpace_of_isLocalRing Ω
  have h1 : v ≫ E.q = toUnit _ ≫ η[E.B] :=
    GlobalTheory.splitTorus_hom_proper_trivial_local Ω (Fin r → ℤ) E.B (v ≫ E.q) inferInstance
  let w := E.isKernel.lift v (toUnit _) h1
  have hw : w ≫ E.i = v := E.isKernel.lift_fst _ _ _
  have hmono : Mono E.i := ⟨fun a b e => E.isKernel.hom_ext e (toUnit_unique _ _)⟩
  haveI : IsMonHom w := GlobalTheory.Serre.isMonHom_of_mul_comp w fun T x y => by
    rw [← cancel_mono E.i, MonObj.mul_comp (x ≫ w), Category.assoc, Category.assoc, Category.assoc, hw,
      MonObj.mul_comp]
  obtain ⟨M, hM⟩ := GlobalTheory.SplitTorus.exists_eq_torusMap w
  by_cases hs : Function.Surjective M
  · have hdiag : w = GlobalTheory.Diag.diagMap _ M := by
      rw [hM]; symm
      exact (GlobalTheory.SplitTorus.eq_torusMap_iff _ M).2 fun b => GlobalTheory.Diag.diagMap_chi _ M b
    have hη : IsClosedImmersion (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      GlobalTheory.isClosedImmersion_of_section_of_isSeparated E.B.hom _ (by simpa using Over.w η[E.B])
    have hpb : IsPullback E.i.left (toUnit _ : splitTorus _ E.X ⟶ 𝟙_ _).left E.q.left (η[E.B] : 𝟙_ _ ⟶ E.B).left :=
      E.isKernel.map (Over.forget _)
    have hi : IsClosedImmersion E.i.left :=
      MorphismProperty.of_isPullback (P := @IsClosedImmersion) hpb.flip hη
    have hw' : IsClosedImmersion w.left := hdiag ▸ GlobalTheory.Diag.isClosedImmersion_diagMap _ hs
    rw [← hw, Over.comp_left]
    infer_instance
  · exfalso
    obtain ⟨p, hp, φ, hφ, hφM⟩ := exists_prime_hom_of_not_surjective M hs
    apply hker p hp φ hφ
    rw [← hw, hM, ← Category.assoc, ← GlobalTheory.SplitTorus.torusMap_comp, hφM, GlobalTheory.SplitTorus.torusMap_zero,
      MonObj.one_comp]

end GlobalTheory.TorusFieldCrit
