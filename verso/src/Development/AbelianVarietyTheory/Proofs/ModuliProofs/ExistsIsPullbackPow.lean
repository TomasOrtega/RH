import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.AllTorsMap
import Development.AbelianVarietyTheory.Definitions.Uniformization.TXFrame
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.TorusExtensionOverCompleteLocalDvr
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IsFiniteFlatTorsionOfIsGt
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.AbelianSchemeLawsUnconditional
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.GeometricallyConnectedOfIsPullbackOfSurjective

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
open GlobalTheory.FlatTors GlobalTheory.IndefiniteRowSideFullHecke.FlatIsoUnitGenerator
open scoped TensorProduct

namespace GlobalTheory.ExtensionMul

section General

variable {S : Scheme.{0}} {T G B : Over S} [GrpObj T] [GrpObj G] [GrpObj B]

/- English proof (translation)
Establish `inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y` using `fun h => hk.hom_ext h (toUnit_unique _ _)`. Establish `ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x` using `fun x h => ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩`. Establish `hiq : i ≫ q = 1` using `by rw [hk.w, Hom.one_def]`. Take `⟨c, hc⟩` from `ex ((p ≫ a) / y ^ N) (by`. Rewrite using `[GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow, Category.comp_id, div_self'])`.

Establish `hsr : s ≫ y ≫ q = r ≫ q`. Rewrite using `[hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]`. Establish `hsa : s ≫ p ≫ a = r ^ N`. Rewrite using `[← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]`. Take `⟨t, ht⟩` from `ex (r / (s ≫ y)) (by`.

Rewrite using `[GrpObj.div_comp, Category.assoc, hsr, div_self'])`. Use `⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩` and prove the remaining obligations. Apply `inj` to reduce the goal to its premises. Rewrite using `[MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa, MonObj.comp_pow]`. Establish `hW : W.fst ≫ c = W.snd ^ N` using `by rw [W.condition, MonObj.comp_pow, Category.comp_id]`.

Establish `hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ`. Use `hP.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow, ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]`. Rewrite using `[Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq, MonObj.comp_one, _root_.one_mul, hP'.w]`. Use `⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩` and prove the remaining obligations.

Apply `inj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(_ ≫ t) ≫ i = _`. Rewrite using `[Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]`. Introduce `(m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)`. Express the relevant statement in the definitionally equal form `m = _`.

Use `hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_` and prove the remaining obligations. Rewrite using `[hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]`.
-/
theorem exists_isPullback_pow [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P P' Q : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q)
    {p : P' ⟶ P} {y : P' ⟶ G} (hP' : IsPullback y p q b)
    {s : Q ⟶ P'} {r : Q ⟶ G} (hQ : IsPullback s r p φ) :
    ∃ (c : P' ⟶ T) (t : Q ⟶ T), IsPullback s t c ((𝟙 T) ^ N) := by
  have inj : ∀ {W : Over S} {x y : W ⟶ T}, x ≫ i = y ≫ i → x = y := fun h =>
    hk.hom_ext h (toUnit_unique _ _)
  have ex : ∀ {W : Over S} (x : W ⟶ G), x ≫ q = 1 → ∃ y : W ⟶ T, y ≫ i = x := fun x h =>
    ⟨hk.lift x (toUnit _) (by rw [h, Hom.one_def]), hk.lift_fst _ _ _⟩
  have hiq : i ≫ q = 1 := by rw [hk.w, Hom.one_def]
  obtain ⟨c, hc⟩ := ex ((p ≫ a) / y ^ N) (by
    rw [GrpObj.div_comp, Category.assoc, hP.w, MonObj.pow_comp, hP'.w, ← Category.assoc, MonObj.comp_pow,
      Category.comp_id, div_self'])
  have hsr : s ≫ y ≫ q = r ≫ q := by
    rw [hP'.w, ← Category.assoc, hQ.w, Category.assoc, hφb]
  have hsa : s ≫ p ≫ a = r ^ N := by
    rw [← Category.assoc, hQ.w, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id]
  obtain ⟨t, ht⟩ := ex (r / (s ≫ y)) (by
    rw [GrpObj.div_comp, Category.assoc, hsr, div_self'])
  refine ⟨c, t, ⟨?_⟩, ⟨PullbackCone.isLimitAux' _ fun W => ?_⟩⟩
  · apply inj
    rw [MonObj.comp_pow, Category.comp_id, MonObj.pow_comp, ht, div_pow, Category.assoc, hc, GrpObj.comp_div, hsa,
      MonObj.comp_pow]
  · have hW : W.fst ≫ c = W.snd ^ N := by rw [W.condition, MonObj.comp_pow, Category.comp_id]
    have hl : W.fst ≫ p = ((W.snd ≫ i) * (W.fst ≫ y)) ≫ φ := by
      refine hP.hom_ext ?_ ?_
      · rw [Category.assoc, Category.assoc, hφa, MonObj.comp_pow, Category.comp_id, mul_pow,
          ← MonObj.pow_comp _ _ i, ← hW, Category.assoc, hc, GrpObj.comp_div, MonObj.comp_pow, div_mul_cancel]
      · rw [Category.assoc, Category.assoc, hφb, MonObj.mul_comp, Category.assoc, Category.assoc, hiq,
          MonObj.comp_one, _root_.one_mul, hP'.w]
    refine ⟨hQ.lift W.fst _ hl, hQ.lift_fst _ _ _, ?_, ?_⟩
    · apply inj
      change (_ ≫ t) ≫ i = _
      rw [Category.assoc, ht, GrpObj.comp_div, ← Category.assoc, hQ.lift_fst, hQ.lift_snd, mul_div_cancel_right]
    · intro (m : W.pt ⟶ Q) (h1 : m ≫ s = W.fst) (h2 : m ≫ t = W.snd)
      change m = _
      refine hQ.hom_ext (by rw [hQ.lift_fst, h1]) ?_
      rw [hQ.lift_snd, ← h1, ← h2, Category.assoc, Category.assoc, ht, GrpObj.comp_div, div_mul_cancel]

/- English proof (translation)
Establish `hP'` using `IsPullback.of_hasPullback q b`. Establish `hQ` using `IsPullback.of_hasPullback (pullback.snd q b) φ`. Take `⟨c, t, H⟩` from `exists_isPullback_pow i q hk N hP hφa hφb hP' hQ`. Establish `hP''` using `hP'.map (Over.forget S)`. Use `MorphismProperty.of_isPullback_of_descendsAlong (P := Pr) (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_` and prove the remaining obligations.

Conclude with `MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›`. Conclude with `MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›`. Conclude with `MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›`. Conclude with `MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h`.
-/
theorem of_pow_kernel (Pr : MorphismProperty Scheme.{0}) [Pr.IsStableUnderBaseChange]
    [Pr.DescendsAlong (@Surjective ⊓ @Flat ⊓ @QuasiCompact)]
    [IsCommMonObj G] (i : T ⟶ G) (q : G ⟶ B) [IsMonHom i] [IsMonHom q]
    [Surjective q.left] [Flat q.left] [QuasiCompact q.left]
    (hk : IsPullback i (toUnit _) q (η : 𝟙_ _ ⟶ B)) (N : ℕ)
    {P : Over S} {a : P ⟶ G} {b : P ⟶ B} (hP : IsPullback a b q ((𝟙 B) ^ N))
    {φ : G ⟶ P} (hφa : φ ≫ a = (𝟙 G) ^ N) (hφb : φ ≫ b = q) (h : Pr ((𝟙 T) ^ N : T ⟶ T).left) :
    Pr φ.left := by
  have hP' := IsPullback.of_hasPullback q b
  have hQ := IsPullback.of_hasPullback (pullback.snd q b) φ
  obtain ⟨c, t, H⟩ := exists_isPullback_pow i q hk N hP hφa hφb hP' hQ
  have hP'' := hP'.map (Over.forget S)
  refine MorphismProperty.of_isPullback_of_descendsAlong (P := Pr)
    (Q := @Surjective ⊓ @Flat ⊓ @QuasiCompact) (hQ.map (Over.forget S)) ⟨⟨?_, ?_⟩, ?_⟩ ?_
  · exact MorphismProperty.of_isPullback (P := @Surjective) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @Flat) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := @QuasiCompact) hP'' ‹_›
  · exact MorphismProperty.of_isPullback (P := Pr) (H.map (Over.forget S)).flip h

end General

/- English proof (translation)
Take `⟨D⟩` from `hG`. Use `D.q_hom` as an intermediate fact. Use `D.i_hom` as an intermediate fact. Use `D.q_flat` as an intermediate fact. Use `D.q_surjective` as an intermediate fact.

Use `D.q_affine` as an intermediate fact. Use `E.free` as an intermediate fact. Use `E.finite` as an intermediate fact. Establish `hN' : N ≠ 0` using `by omega`. Establish `hf : IsFinite (mulN (splitTorus S E.X) N).left` using `Diag.isFinite_mulN S E.X hN'`.

Establish `hl : Flat (mulN (splitTorus S E.X) N).left` using `Diag.flat_mulN S E.X hN'`. Establish `hs : Surjective (mulN (splitTorus S E.X) N).left` using `Diag.surjective_mulN S E.X hN'`. Rewrite `hf`, `hl`, `hs` using `[MulEtaleDvr.mulN_eq_pow]`. Use `flat_descendsAlong_fpqc` as an intermediate fact. Use `isAffineHom_descendsAlong_fpqc.{0}` as an intermediate fact.

Establish `hP` using `IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)`. Establish `w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N)`. Rewrite using `[MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]`. Establish `ha` using `hP.lift_fst _ _ w`. Establish `hb` using `hP.lift_snd _ _ w`.

Establish `a0 : Surjective (hP.lift _ _ w).left` using `of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs`. Establish `a1 : Flat (hP.lift _ _ w).left` using `of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl`. Establish `a2 : IsAffineHom (hP.lift _ _ w).left` using `of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance`. Establish `a3 : UniversallyClosed (hP.lift _ _ w).left` using `of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance`. Establish `a4 : LocallyOfFiniteType (hP.lift _ _ w).left` using `of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance`.

Establish `a5 : IsFinite (hP.lift _ _ w).left` using `(IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩`. Establish `hP'` using `(hP.map (Over.forget S)).flip`. Establish `b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left` using `MorphismProperty.of_isPullback (P := @IsFinite) hP' h1`. Establish `b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left` using `MorphismProperty.of_isPullback (P := @Flat) hP' h2`. Establish `b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left` using `MorphismProperty.of_isPullback (P := @Surjective) hP' h3`.

Rewrite using `[← ha, Over.comp_left]`. Conclude with `⟨inferInstance, inferInstance, inferInstance⟩`.
-/
theorem pow_of_isGt {S : Scheme.{0}} (E : SplitExt S) (G : Over S) [GrpObj G] [IsCommMonObj G] (hG : E.IsGt G)
    (N : ℕ) (hN : 1 ≤ N) (h1 : IsFinite ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) (h2 : Flat ((𝟙 E.B) ^ N : E.B ⟶ E.B).left)
    (h3 : Surjective ((𝟙 E.B) ^ N : E.B ⟶ E.B).left) :
    IsFinite ((𝟙 G) ^ N : G ⟶ G).left ∧ Flat ((𝟙 G) ^ N : G ⟶ G).left ∧ Surjective ((𝟙 G) ^ N : G ⟶ G).left := by
  obtain ⟨D⟩ := hG
  have := D.q_hom
  have := D.i_hom
  have := D.q_flat
  have := D.q_surjective
  have := D.q_affine
  have := E.free
  have := E.finite
  have hN' : N ≠ 0 := by omega
  have hf : IsFinite (mulN (splitTorus S E.X) N).left := Diag.isFinite_mulN S E.X hN'
  have hl : Flat (mulN (splitTorus S E.X) N).left := Diag.flat_mulN S E.X hN'
  have hs : Surjective (mulN (splitTorus S E.X) N).left := Diag.surjective_mulN S E.X hN'
  rw [MulEtaleDvr.mulN_eq_pow] at hf hl hs
  have := flat_descendsAlong_fpqc
  have := isAffineHom_descendsAlong_fpqc.{0}
  have hP := IsPullback.of_hasPullback D.q ((𝟙 E.B) ^ N)
  have w : ((𝟙 G) ^ N) ≫ D.q = D.q ≫ ((𝟙 E.B) ^ N) := by
    rw [MonObj.pow_comp, MonObj.comp_pow, Category.id_comp, Category.comp_id]
  have ha := hP.lift_fst _ _ w
  have hb := hP.lift_snd _ _ w
  have a0 : Surjective (hP.lift _ _ w).left := of_pow_kernel @Surjective D.i D.q D.isKernel N hP ha hb hs
  have a1 : Flat (hP.lift _ _ w).left := of_pow_kernel @Flat D.i D.q D.isKernel N hP ha hb hl
  have a2 : IsAffineHom (hP.lift _ _ w).left :=
    of_pow_kernel @IsAffineHom D.i D.q D.isKernel N hP ha hb inferInstance
  have a3 : UniversallyClosed (hP.lift _ _ w).left :=
    of_pow_kernel @UniversallyClosed D.i D.q D.isKernel N hP ha hb inferInstance
  have a4 : LocallyOfFiniteType (hP.lift _ _ w).left :=
    of_pow_kernel @LocallyOfFiniteType D.i D.q D.isKernel N hP ha hb inferInstance
  have a5 : IsFinite (hP.lift _ _ w).left :=
    (IsFinite.iff_isIntegralHom_and_locallyOfFiniteType _).mpr
      ⟨IsIntegralHom.iff_universallyClosed_and_isAffineHom.mpr ⟨a3, a2⟩, a4⟩
  have hP' := (hP.map (Over.forget S)).flip
  have b1 : IsFinite (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @IsFinite) hP' h1
  have b2 : Flat (pullback.fst D.q ((𝟙 E.B) ^ N)).left := MorphismProperty.of_isPullback (P := @Flat) hP' h2
  have b3 : Surjective (pullback.fst D.q ((𝟙 E.B) ^ N)).left :=
    MorphismProperty.of_isPullback (P := @Surjective) hP' h3
  rw [← ha, Over.comp_left]
  exact ⟨inferInstance, inferInstance, inferInstance⟩

/- English proof (translation)
Introduce `R _ _ _ D`. Establish `hL` using `abelianSchemeLaws_all.1`. Take `⟨H, _, _, hH⟩` from `TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)`. Take `⟨Φ, hΦ⟩` from `TorusModel.exists_points hL.globalFns hH`. Use `⟨H, inferInstance, inferInstance, Φ, hΦ, (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩` and prove the remaining obligations.

Take `⟨d⟩` from `hH`. Use `d.q_affine` as an intermediate fact. Use `(TorusModel.splitExt D).isAbelian.proper` as an intermediate fact. Rewrite using `[← Over.w d.q]`. Use `infer_instance`.

Take `⟨h₁, h₂, h₃, -⟩` from `hL.mulN _ D.P k hk`. Conclude with `pow_of_isGt _ H hH k hk h₁ h₂ h₃`.
-/
theorem exists_represents_pow : ∀ (R : Type) [CommRing R] [IsDomain R] [IsNoetherianRing R] (D : DegPre R), ∃ (Gt : Over (Sp R)) (_ : GrpObj Gt) (_ : IsCommMonObj Gt) (Φ : ∀ T, (T ⟶ Gt) ≃ GtPt D T), GlobalTheory.TorusModel.Represents Φ ∧ Smooth Gt.hom ∧ IsSeparated Gt.hom ∧ ∀ k : ℕ, 1 ≤ k → IsFinite ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Flat ((𝟙 Gt) ^ k : Gt ⟶ Gt).left ∧ Surjective ((𝟙 Gt) ^ k : Gt ⟶ Gt).left := by
  intro R _ _ _ D
  have hL := abelianSchemeLaws_all.1
  obtain ⟨H, _, _, hH⟩ := TorusModel.exists_isGt hL.globalFns (TorusModel.splitExt D)
  obtain ⟨Φ, hΦ⟩ := TorusModel.exists_points hL.globalFns hH
  refine ⟨H, inferInstance, inferInstance, Φ, hΦ,
    (UnitRigidity.smooth_geometricallyConnected_of_isGt _ H hH).1, ?_, fun k hk => ?_⟩
  · obtain ⟨d⟩ := hH
    have := d.q_affine
    have := (TorusModel.splitExt D).isAbelian.proper
    rw [← Over.w d.q]
    infer_instance
  · obtain ⟨h₁, h₂, h₃, -⟩ := hL.mulN _ D.P k hk
    exact pow_of_isGt _ H hH k hk h₁ h₂ h₃

end GlobalTheory.ExtensionMul
