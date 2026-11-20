import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrPull
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UniformisedMemberDividingThetaConstantNeZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPointsFramesThetaSectionGenericFibreMember
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SecScalOneVal
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkDescendsAlongBaseChange
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.QkToAkUInvariantUnderFieldEmbedding
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.SumFCalculus
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ThetaOperatorsProjectiveRepresentation
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsUniqueThickTorusLevelWeightExpansion
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.LinCombValueAct
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR GlobalTheory.ZH GlobalTheory.FieldBaseChange GlobalTheory.TorsionExt GlobalTheory.UT.CoefBasic

noncomputable section

namespace GlobalTheory.TermsMove

section Sums

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {I : Ideal R} {I' : Ideal R'}
  {F F' : Type} [Field F] [Algebra (FractionRing R) F] [Field F'] [Algebra (FractionRing R') F'] {Ix : Type}

/- English proof (translation)
Use `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))`. Use `letI : Module R' F' := Module.compHom F' (algebraMap R' (FractionRing R'))`. Set `l : F →ₛₗ[φ] F'` to `{ toFun := σ map_add' := map_add σ map_smul' := fun r y => by show σ (algebraMap R (FractionRing R) r • y) = algebraMap R' (FractionRing R') (φ r) • σ y`. Rewrite using `[Algebra.smul_def, Algebra.smul_def, map_mul, hσ] }`. Take `⟨N, ⟨T, hT⟩, hs, hx, hS⟩` from `h`.

Establish `hN : ∀ y ∈ N, l y ∈ Submodule.span R' (l '' (T : Set F))` using `fun y hy => by`. Rewrite `hy` using `[← hT]`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩`. Consider the case `zero => rw [map_zero]`.

Conclude with `zero_mem _`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ ha`.

Use `⟨Submodule.span R' (l '' (T : Set F)), Submodule.fg_span (T.finite_toSet.image _), hN _ hs, fun i => hN _ (hx i), fun n => ?_⟩` and prove the remaining obligations. Take `⟨S, hS⟩` from `hS n`. Use `⟨S, fun U hU => ?_⟩` and prove the remaining obligations. Establish `e : σ s - ∑ i ∈ U, σ (x i) = l (s - ∑ i ∈ U, x i)` using `by rw [map_sub, map_sum]; rfl`. Rewrite using `[e]`.

Use `Submodule.smul_induction_on (hS U hU) (fun r hr y hy => ?_) (fun a b ha hb => ?_)` and prove the remaining obligations. Rewrite using `[map_smulₛₗ]`. Use `Submodule.smul_mem_smul ?_ (hN y hy)` and prove the remaining obligations. Use `Ideal.mem_map_of_mem φ hr` as an intermediate fact. Rewrite `this` using `[Ideal.map_pow]`.

Conclude with `Ideal.pow_right_mono hI n this`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
theorem sumF_map (φ : R →+* R') (hI : I.map φ ≤ I') (σ : F →+* F')
    (hσ : ∀ r, σ (algebraMap (FractionRing R) F (algebraMap R (FractionRing R) r)) =
      algebraMap (FractionRing R') F' (algebraMap R' (FractionRing R') (φ r)))
    {x : Ix → F} {s : F} (h : SumF I F x s) : SumF I' F' (fun i => σ (x i)) (σ s) := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  letI : Module R' F' := Module.compHom F' (algebraMap R' (FractionRing R'))
  let l : F →ₛₗ[φ] F' :=
    { toFun := σ
      map_add' := map_add σ
      map_smul' := fun r y => by
        show σ (algebraMap R (FractionRing R) r • y) = algebraMap R' (FractionRing R') (φ r) • σ y
        rw [Algebra.smul_def, Algebra.smul_def, map_mul, hσ] }
  obtain ⟨N, ⟨T, hT⟩, hs, hx, hS⟩ := h
  have hN : ∀ y ∈ N, l y ∈ Submodule.span R' (l '' (T : Set F)) := fun y hy => by
    rw [← hT] at hy
    induction hy using Submodule.span_induction with
    | mem y hy => exact Submodule.subset_span ⟨y, hy, rfl⟩
    | zero => rw [map_zero]; exact zero_mem _
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smulₛₗ]; exact Submodule.smul_mem _ _ ha
  refine ⟨Submodule.span R' (l '' (T : Set F)), Submodule.fg_span (T.finite_toSet.image _), hN _ hs,
    fun i => hN _ (hx i), fun n => ?_⟩
  obtain ⟨S, hS⟩ := hS n
  refine ⟨S, fun U hU => ?_⟩
  have e : σ s - ∑ i ∈ U, σ (x i) = l (s - ∑ i ∈ U, x i) := by rw [map_sub, map_sum]; rfl
  rw [e]
  refine Submodule.smul_induction_on (hS U hU) (fun r hr y hy => ?_) (fun a b ha hb => ?_)
  · rw [map_smulₛₗ]
    refine Submodule.smul_mem_smul ?_ (hN y hy)
    have := Ideal.mem_map_of_mem φ hr
    rw [Ideal.map_pow] at this
    exact Ideal.pow_right_mono hI n this
  · rw [map_add]; exact add_mem ha hb

/- English proof (translation)
Use `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))`. Set `f : F →ₗ[R] F` to `{ toFun := fun y => c * y map_add' := mul_add c map_smul' := fun r y => mul_smul_comm (algebraMap R (FractionRing R) r) c y }`. Conclude with `AdicSum.sumI_add (AdicSum.sumI_map f h) h'`.
-/
theorem sumF_lin {x x' : Ix → F} {s s' : F} (h : SumF I F x s) (h' : SumF I F x' s') (c : F) :
    SumF I F (fun i => c * x i + x' i) (c * s + s') := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  let f : F →ₗ[R] F :=
    { toFun := fun y => c * y
      map_add' := mul_add c
      map_smul' := fun r y => mul_smul_comm (algebraMap R (FractionRing R) r) c y }
  exact AdicSum.sumI_add (AdicSum.sumI_map f h) h'

/- English proof (translation)
The claim follows from `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R)) ⟨_, Submodule.fg_bot, zero_mem _, fun _ => zero_mem _, fun _ => ⟨∅, fun _ _ => by simp⟩⟩`.
-/
theorem sumF_zero : SumF I F (fun _ : Ix => (0 : F)) 0 :=
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  ⟨_, Submodule.fg_bot, zero_mem _, fun _ => zero_mem _, fun _ => ⟨∅, fun _ _ => by simp⟩⟩

/- English proof (translation)
Use `letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))`. Conclude with `(AdicSum.sumI_comp_iff e.injective (fun i hi => absurd (e.surjective i) hi)).2 h`.
-/
theorem sumF_equiv {Jx : Type} (e : Jx ≃ Ix) {x : Ix → F} {s : F} (h : SumF I F x s) : SumF I F (fun j => x (e j)) s := by
  letI : Module R F := Module.compHom F (algebraMap R (FractionRing R))
  exact (AdicSum.sumI_comp_iff e.injective (fun i hi => absurd (e.surjective i) hi)).2 h

end Sums

section Values

variable {R : Type} [CommRing R] [IsDomain R] {A : PolAV (Spec (CommRingCat.of (FractionRing R)))}
  {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h Z r z J hJ`. Establish `a` using `congrArg (r.stalkMap z).hom (h (r z) _ (LevelExpansion.good_comp r hJ))`. Use `(LevelExpansion.sval_comp t r _ hJ).trans (a.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))` and prove the remaining obligations. Conclude with `(LiftTest.gs_comp r (𝟙 _) z ⊤ trivial _).symm.trans (by rw [Category.comp_id]; rfl)`.

Use `(LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans ?_` and prove the remaining obligations. Rewrite using `[Category.comp_id, FrameMove.val_powFrame, zpow_natCast]`. Introduce `h z J hJ`. Establish `a` using `h _ (𝟙 _) z J hJ`. Rewrite `a` using `[Category.id_comp]`.

Rewrite using `[FrameMove.val_powFrame, zpow_natCast]`. Conclude with `a`.
-/
theorem valAt_iff (t : SecA A F k) (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) (c : F) : ValAt t x e c ↔
    ∀ (Z : Scheme.{0}) (r : Z ⟶ Sp F) (z : Z) J, Good A.L z J →
      sA t (r ≫ (ptSecT A.A x).left) z J = constVal r z c * (val e r z J ^ k).val := by
  constructor
  · intro h Z r z J hJ
    have a := congrArg (r.stalkMap z).hom (h (r z) _ (LevelExpansion.good_comp r hJ))
    refine (LevelExpansion.sval_comp t r _ hJ).trans (a.trans ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ?_)))
    · exact (LiftTest.gs_comp r (𝟙 _) z ⊤ trivial _).symm.trans (by rw [Category.comp_id]; rfl)
    · refine (LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans ?_
      rw [Category.comp_id, FrameMove.val_powFrame, zpow_natCast]
  · intro h z J hJ
    have a := h _ (𝟙 _) z J hJ
    rw [Category.id_comp] at a
    rw [FrameMove.val_powFrame, zpow_natCast]
    exact a

/- English proof (translation)
The claim follows from `SecValue.ValM.add (σ := SecValue.kon R F c • SecM.ofSec A.A t) (σ' := SecM.ofSec A.A t') (SecValue.ValM.smul (σ := SecM.ofSec A.A t) h c) h'`.
-/
theorem valAt_lin {t t' : AbSec A F k} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x} {a a' : F} (h : ValAt t x e a)
    (h' : ValAt t' x e a') (c : F) : ValAt (c • t + t' : AbSec A F k) x e (c * a + a') :=
  SecValue.ValM.add (σ := SecValue.kon R F c • SecM.ofSec A.A t) (σ' := SecM.ofSec A.A t')
    (SecValue.ValM.smul (σ := SecM.ofSec A.A t) h c) h'

/- English proof (translation)
The claim follows from `SecComb.valM_zero x e`.
-/
theorem valAt_zero (x : TFK (R := R) F ⟶ A.A) (e : FrAt x) : ValAt (0 : AbSec A F k) x e 0 :=
  SecComb.valM_zero x e

/- English proof (translation)
The claim follows from `SecValue.ValM.unique (σ := SecM.ofSec A.A t) h h'`.
-/
theorem valAt_unique {t : SecA A F k} {x : TFK (R := R) F ⟶ A.A} {e : FrAt x} {a a' : F} (h : ValAt t x e a)
    (h' : ValAt t x e a') : a = a' :=
  SecValue.ValM.unique (σ := SecM.ofSec A.A t) h h'

/- English proof (translation)
Establish `h` using `ThetaRep.finrank_secM GlobalTheory.abelianSchemeLaws_all.1.secBaseChange A (n := 1) le_rfl (jFK (R := R) F)`. Rewrite `h` using `[one_pow]`. Establish `hf : IsField Γ((TFK (R` using `R) F).left, ⊤) := MulEquiv.isField (Field.toIsField F) (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv`. Take `⟨u, -, hu⟩` from `ThetaPtExist.exists_generator_of_isField hf h`. Establish `key : ∀ s : AbSec A F 1, ∃ c : F, s = (c • (show AbSec A F 1 from SecM.toSec A.A u))` using `fun s => by`.

Take `⟨r, hr⟩` from `hu (SecM.ofSec A.A s)`. Take `⟨c, rfl⟩` from `SecValue.kon_surj (R := R) r`. Conclude with `⟨c, congrArg (SecM.toSec A.A) hr.symm⟩`. Take `⟨a, ha⟩` from `key t`. Take `⟨b, hb⟩` from `key s`.

Establish `a0 : a ≠ 0` using `by rintro rfl; exact ht (ha.trans (zero_smul _ _))`. Conclude with `⟨b / a, by rw [hb, ha, smul_smul, div_mul_cancel₀ _ a0]⟩`.
-/
theorem exists_eq_smul {t : AbSec A F 1} (ht : t ≠ 0) (s : AbSec A F 1) : ∃ c : F, s = c • t := by
  have h := ThetaRep.finrank_secM GlobalTheory.abelianSchemeLaws_all.1.secBaseChange A (n := 1) le_rfl (jFK (R := R) F)
  rw [one_pow] at h
  have hf : IsField Γ((TFK (R := R) F).left, ⊤) :=
    MulEquiv.isField (Field.toIsField F) (Scheme.ΓSpecIso (CommRingCat.of F)).commRingCatIsoToRingEquiv.toMulEquiv
  obtain ⟨u, -, hu⟩ := ThetaPtExist.exists_generator_of_isField hf h
  have key : ∀ s : AbSec A F 1, ∃ c : F, s = (c • (show AbSec A F 1 from SecM.toSec A.A u)) := fun s => by
    obtain ⟨r, hr⟩ := hu (SecM.ofSec A.A s)
    obtain ⟨c, rfl⟩ := SecValue.kon_surj (R := R) r
    exact ⟨c, congrArg (SecM.toSec A.A) hr.symm⟩
  obtain ⟨a, ha⟩ := key t
  obtain ⟨b, hb⟩ := key s
  have a0 : a ≠ 0 := by rintro rfl; exact ht (ha.trans (zero_smul _ _))
  exact ⟨b / a, by rw [hb, ha, smul_smul, div_mul_cancel₀ _ a0]⟩

end Values

/- English proof (translation)
Substitute `hq` using the available equality. Establish `le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull (c ≫ P)).U p.1 ⊓ (L.pull c).U p.2 ≤ c ⁻¹ᵁ ((M.pull P).U (fun _ => p.1 PUnit.unit) ⊓ L.U (p.2 PUnit.unit))` using `fun p x hx => ⟨mem_pull.2 ((mem_pull (F := c ≫ P)).1 hx.1), mem_pull.1 hx.2⟩`. Set `w : LB.Iso (L.pull c) (M.pull (c ≫ P))` to `⟨fun p => res (le p) (pullU c _ (u.s (fun _ => p.1 PUnit.unit, p.2 PUnit.unit)))⟩`. Establish `hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : M.ι) (i : L.ι), (c ≫ P) (f z) ∈ M.U j → c (f z) ∈ L.U i → isoVal w f z j i = gw u (f ≫ c) z j i` using `fun Z f z j i hj hi => by`. Establish `hm : f z ∈ (M.pull (c ≫ P)).U (fun _ => j) ⊓ (L.pull c).U (fun _ => i)` using `⟨mem_pull.2 hj, mem_pull.2 hi⟩`.

Conclude with `(gm_res f z (le (fun _ => j, fun _ => i)) hm _).trans (gm_pull f c z _ (le (fun _ => j, fun _ => i) hm) _)`. Use `⟨w, (isGen_iff w).2 fun Z f z j j' i i' hj hj' hi hi' => ?_, hw⟩` and prove the remaining obligations. Use `(hw Z f z j (i PUnit.unit) hj (mem_pull.1 hi)).trans ((hu Z (f ≫ c) z j j' _ (i' PUnit.unit) hj hj' ((mem_pull (F := c)).1 hi) ((mem_pull (F := c)).1 hi')).trans ?_)` and prove the remaining obligations. Rewrite using `[gm_pull_g L c f z i i' hi hi', Category.assoc]`. Conclude with `congrArg _ (hw Z f z j' (i' PUnit.unit) hj' (mem_pull.1 hi')).symm`.
-/
theorem exists_pull_iso {X N Y : Scheme.{0}} {L : LB X} {M : LB N} {P : X ⟶ N} {u : LB.Iso L (M.pull P)} (hu : PGen u)
    (c : Y ⟶ X) {q : Y ⟶ N} (hq : c ≫ P = q) : ∃ w : LB.Iso (L.pull c) (M.pull q), w.IsGen ∧
      ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : M.ι) (i : L.ι), q (f z) ∈ M.U j → c (f z) ∈ L.U i →
        isoVal w f z j i = gw u (f ≫ c) z j i := by
  subst hq
  have le : ∀ p : (PUnit → M.ι) × (PUnit → L.ι), (M.pull (c ≫ P)).U p.1 ⊓ (L.pull c).U p.2 ≤
      c ⁻¹ᵁ ((M.pull P).U (fun _ => p.1 PUnit.unit) ⊓ L.U (p.2 PUnit.unit)) := fun p x hx =>
    ⟨mem_pull.2 ((mem_pull (F := c ≫ P)).1 hx.1), mem_pull.1 hx.2⟩
  let w : LB.Iso (L.pull c) (M.pull (c ≫ P)) :=
    ⟨fun p => res (le p) (pullU c _ (u.s (fun _ => p.1 PUnit.unit, p.2 PUnit.unit)))⟩
  have hw : ∀ (Z : Scheme.{0}) (f : Z ⟶ Y) (z : Z) (j : M.ι) (i : L.ι), (c ≫ P) (f z) ∈ M.U j → c (f z) ∈ L.U i →
      isoVal w f z j i = gw u (f ≫ c) z j i := fun Z f z j i hj hi => by
    have hm : f z ∈ (M.pull (c ≫ P)).U (fun _ => j) ⊓ (L.pull c).U (fun _ => i) := ⟨mem_pull.2 hj, mem_pull.2 hi⟩
    exact (gm_res f z (le (fun _ => j, fun _ => i)) hm _).trans (gm_pull f c z _ (le (fun _ => j, fun _ => i) hm) _)
  refine ⟨w, (isGen_iff w).2 fun Z f z j j' i i' hj hj' hi hi' => ?_, hw⟩
  refine (hw Z f z j (i PUnit.unit) hj (mem_pull.1 hi)).trans
    ((hu Z (f ≫ c) z j j' _ (i' PUnit.unit) hj hj' ((mem_pull (F := c)).1 hi) ((mem_pull (F := c)).1 hi')).trans ?_)
  rw [gm_pull_g L c f z i i' hi hi', Category.assoc]
  exact congrArg _ (hw Z f z j' (i' PUnit.unit) hj' (mem_pull.1 hi')).symm

section Coef

variable {R : Type} [CommRing R] [IsDomain R] {D : DegPre R} {F : Type} [Field F] [Algebra (FractionRing R) F] {k : ℕ}

/- English proof (translation)
Establish `a` using `congrArg (r.stalkMap z).hom (h (r z) _ (LevelExpansion.good_comp r hJ))`. Use `Eq.trans ?_ (a.trans ?_)` and prove the remaining obligations. Use `Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ((map_pow _ _ _).trans (congrArg (· ^ k) ?_))))` and prove the remaining obligations. Conclude with `(LiftTest.gs_comp r (𝟙 _) z ⊤ trivial _).symm.trans (by rw [Category.comp_id]; rfl)`. Conclude with `(LevelExpansion.val_comp (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r _ hJ).symm`.

Use `(map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·) (LevelExpansion.sval_comp s r _ hJ).symm ?_)) ?_)` and prove the remaining obligations. Conclude with `(LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans (by rw [Category.comp_id])`. Conclude with `(LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans (by rw [Category.comp_id])`.
-/
theorem isCoef_val {g : GtPtF D F} {w : Frm D F k g.b} {χ : D.X} {s} {x : F} (h : IsCoef k g w χ s x)
    {Z : Scheme.{0}} (r : Z ⟶ Sp F) {z : Z} {J} (hJ : Good D.P.L z J) :
    constVal r z x * (rigV D (r ≫ (TF (R := R) F).hom) z J).val ^ k =
      sval s (r ≫ (lift (𝟙 (TF (R := R) F)) g.b).left) z J * (val (g.s χ) r z J).val * (val w r z J).val := by
  have a := congrArg (r.stalkMap z).hom (h (r z) _ (LevelExpansion.good_comp r hJ))
  refine Eq.trans ?_ (a.trans ?_)
  · refine Eq.symm ((map_mul _ _ _).trans (congrArg₂ (· * ·) ?_ ((map_pow _ _ _).trans (congrArg (· ^ k) ?_))))
    · exact (LiftTest.gs_comp r (𝟙 _) z ⊤ trivial _).symm.trans (by rw [Category.comp_id]; rfl)
    · exact (LevelExpansion.val_comp (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig r _ hJ).symm
  · refine (map_mul _ _ _).trans (congrArg₂ (· * ·) ((map_mul _ _ _).trans (congrArg₂ (· * ·)
      (LevelExpansion.sval_comp s r _ hJ).symm ?_)) ?_)
    · exact (LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans (by rw [Category.comp_id])
    · exact (LevelExpansion.val_comp _ r (𝟙 _) hJ).symm.trans (by rw [Category.comp_id])

/- English proof (translation)
The claim follows from `((coef_basic R D F k g).2.2 w hw).2.1 s s' c χ`.
-/
theorem coef_lin {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (s s' : Fam D F k) (c : F) (χ : D.X) :
    coef (c • s + s') g w χ = c * coef s g w χ + coef s' g w χ :=
  ((coef_basic R D F k g).2.2 w hw).2.1 s s' c χ

/- English proof (translation)
Use `coef_lin hw (0 : Fam D F k) 0 (-1) χ` as an intermediate fact. Rewrite `this` using `[smul_zero, add_zero]`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem coef_zero {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (χ : D.X) : coef (0 : Fam D F k) g w χ = 0 := by
  have := coef_lin hw (0 : Fam D F k) 0 (-1) χ
  rw [smul_zero, add_zero] at this
  rw [this]; ring

/- English proof (translation)
Use `coef_lin hw s 0 c χ` as an intermediate fact. Rewrite `this` using `[add_zero, coef_zero hw, add_zero]`. Then use the resulting hypothesis.
-/
theorem coef_smul {g : GtPtF D F} {w : Frm D F k g.b} (hw : w.IsGen) (s : Fam D F k) (c : F) (χ : D.X) :
    coef (c • s) g w χ = c * coef s g w χ := by
  have := coef_lin hw s 0 c χ
  rwa [add_zero, coef_zero hw, add_zero] at this

/- English proof (translation)
Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `a` using `isCoef_coef g hw χ s z J hJ`. Rewrite using `[hv z J hJ]`. Simplify using `only [cst_eq, map_mul] at a ⊢`. Take the linear combination `cstH z c * a`.
-/
theorem coef_scale {g : GtPtF D F} {w w' : Frm D F k g.b} (hw : w.IsGen) {c : F}
    (hv : ∀ z J, Good D.P.L z J → (val w' (𝟙 _) z J).val = cst F z c * (val w (𝟙 _) z J).val) (s : Fam D F k) (χ : D.X) :
    coef s g w' χ = c * coef s g w χ := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_coef g hw χ s z J hJ
  rw [hv z J hJ]
  simp only [cst_eq, map_mul] at a ⊢
  linear_combination cstH z c * a

variable {E : Type} [Field E] [Algebra (FractionRing R) E] [Algebra E F] [IsScalarTower (FractionRing R) E F]

/- English proof (translation)
Use `coef_eq fun z J hJ => ?_` and prove the remaining obligations. Establish `a` using `isCoef_val (isCoef_coef g hw χ s) (spMap (algebraMap E F)) hJ`. Establish `e₁ : spMap (algebraMap E F) ≫ (TF (R` using `R) E).hom = (TF (R := R) F).hom := Over.w (baseMap (R := R) E F)`. Establish `e₂ : lift (𝟙 (TF (R` using `R) F)) g₁.b ≫ famMap D E F = baseMap (R := R) E F ≫ lift (𝟙 (TF (R := R) E)) g.b := by`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [famMap, hb]`.

Establish `e₃ : (lift (𝟙 (TF (R` using `R) F)) g₁.b).left ≫ (famMap D E F).left = spMap (algebraMap E F) ≫ (lift (𝟙 (TF (R := R) E)) g.b).left := congrArg (fun q => q.left) e₂`. Rewrite `a` using `[e₁, ← e₃, ← hs χ z J hJ, ← hv z J hJ]`. Establish `c : cst (R` using `R) F z (algebraMap E F (coef s g w χ)) = constVal (spMap (algebraMap E F)) z (coef s g w χ) := (FrameMove.gs_spMap _ z _).symm`. Rewrite using `[c]`. Conclude with `a.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (sval_pullOver _ _ _ _ hJ).symm rfl) rfl)`.
-/
theorem coef_ext (hG : GlobalFnsSt) {g : GtPtF D E} {w : Frm D E k g.b} (hw : w.IsGen) {g₁ : GtPtF D F}
    (hb : g₁.b = baseMap (R := R) E F ≫ g.b)
    (hs : ∀ χ (z : Sp F) J, Good D.P.L z J → val (g₁.s χ) (𝟙 (Sp F)) z J = val (g.s χ) (spMap (algebraMap E F)) z J)
    {w₁ : Frm D F k g₁.b}
    (hv : ∀ (z : Sp F) J, Good D.P.L z J → val w₁ (𝟙 (Sp F)) z J = val w (spMap (algebraMap E F)) z J)
    (s : Fam D E k) (χ : D.X) : coef (famPull D E F hG k s) g₁ w₁ χ = algebraMap E F (coef s g w χ) := by
  refine coef_eq fun z J hJ => ?_
  have a := isCoef_val (isCoef_coef g hw χ s) (spMap (algebraMap E F)) hJ
  have e₁ : spMap (algebraMap E F) ≫ (TF (R := R) E).hom = (TF (R := R) F).hom := Over.w (baseMap (R := R) E F)
  have e₂ : lift (𝟙 (TF (R := R) F)) g₁.b ≫ famMap D E F = baseMap (R := R) E F ≫ lift (𝟙 (TF (R := R) E)) g.b := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [famMap, hb]
  have e₃ : (lift (𝟙 (TF (R := R) F)) g₁.b).left ≫ (famMap D E F).left =
      spMap (algebraMap E F) ≫ (lift (𝟙 (TF (R := R) E)) g.b).left := congrArg (fun q => q.left) e₂
  rw [e₁, ← e₃, ← hs χ z J hJ, ← hv z J hJ] at a
  have c : cst (R := R) F z (algebraMap E F (coef s g w χ)) = constVal (spMap (algebraMap E F)) z (coef s g w χ) :=
    (FrameMove.gs_spMap _ z _).symm
  rw [c]
  exact a.trans (congrArg₂ (· * ·) (congrArg₂ (· * ·) (sval_pullOver _ _ _ _ hJ).symm rfl) rfl)

/- English proof (translation)
Establish `h0 : (baseMap (R` using `R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left := congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))`. Take `⟨w', hw', hv⟩` from `exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₁) (ε' := DegPre.lineε k) (fun U _ h => Finset.prod_congr rfl fun i _ => by fin_cases i`. Conclude with `congrArg (fun q => h q ^ _) h0`. Conclude with `congrArg (fun q : TF (R := R) F ⟶ D.P.A => h q.left ^ _) hb.symm)`. Use the proof step `(LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)`.

Conclude with `⟨w', hw', fun z J hJ => (hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans (congrArg (fun q => val w q z J) (Category.id_comp _)))⟩`.
-/
theorem exists_frm_ext {b : TF (R := R) E ⟶ D.P.A} {w : Frm D E k b} (hw : w.IsGen) {b₁ : TF (R := R) F ⟶ D.P.A}
    (hb : b₁ = baseMap (R := R) E F ≫ b) : ∃ w₁ : Frm D F k b₁, w₁.IsGen ∧
      ∀ (z : Sp F) J, Good D.P.L z J → val w₁ (𝟙 (Sp F)) z J = val w (spMap (algebraMap E F)) z J := by
  have h0 : (baseMap (R := R) E F).left ≫ (DegPre.zeroF D E).left = (DegPre.zeroF D F).left :=
    congrArg (fun q : TF (R := R) F ⟶ D.P.A => q.left) (MonObj.comp_one (M := D.P.A) (baseMap (R := R) E F))
  obtain ⟨w', hw', hv⟩ := exists_gen D.P.isLB (φ' := DegPre.lineφ D F b₁) (ε' := DegPre.lineε k)
    (fun U _ h => Finset.prod_congr rfl fun i _ => by
      fin_cases i
      · exact congrArg (fun q => h q ^ _) h0
      · exact congrArg (fun q : TF (R := R) F ⟶ D.P.A => h q.left ^ _) hb.symm)
    (LB.pullGen D.P.L _ _ w (baseMap (R := R) E F).left) (pullGen_isGen _ _ _ _ hw _)
  exact ⟨w', hw', fun z J hJ => (hv _ _ z J hJ).trans ((val_pull hJ _ _ _).trans
    (congrArg (fun q => val w q z J) (Category.id_comp _)))⟩

end Coef

section Lies

variable {R : Type} [CommRing R] [IsDomain R] {I : Ideal R} {D : DegData R I}
  {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]

def LiesOver (U : UnifPre I D A G) (F : Type) [Field F] [Algebra (FractionRing R) F] (w₀ : W0 U) (g : GtPtF D.toPre F)
    (w : Frm D.toPre F 1 g.b) (x : TFK (R := R) F ⟶ A.A) (fr : FrAt x) : Prop :=
  ∀ k : ℕ, 1 ≤ k → ∀ wk : Frm D.toPre F k g.b,
    (∀ z J, Good D.toPre.P.L z J → val wk (𝟙 _) z J = val w (𝟙 _) z J ^ k) → wk.IsGen →
    ∀ (s : SecA A F k) (s' : Fam D.toPre F k) (v : F), U.ExpandsF F k w₀ s s' → ValAt s x fr v → SumF I F (coef s' g wk) v

variable {E F : Type} [Field F] [Algebra (FractionRing R) F] [Field E] [Algebra (FractionRing R) E] [Algebra E F]
  [IsScalarTower (FractionRing R) E F]

def frExt (F : Type) [Field F] [Algebra (FractionRing R) F] [Algebra E F] [IsScalarTower (FractionRing R) E F]
    {x : TFK (R := R) E ⟶ A.A} (e : FrAt x) : FrAt (fieldMap (R := R) E F ≫ x) :=
  LB.pullGen A.L _ _ e (fieldMap (R := R) E F).left

/- English proof (translation)
The claim follows from `val_pull hJ e (fieldMap (R := R) E F).left r`.
-/
theorem val_frExt {x : TFK (R := R) E ⟶ A.A} (e : FrAt x) {Z : Scheme.{0}} (r : Z ⟶ Sp F) {z : Z} {J}
    (hJ : Good A.L z J) : val (frExt F e) r z J = val e (r ≫ spMap (algebraMap E F)) z J :=
  val_pull hJ e (fieldMap (R := R) E F).left r

/- English proof (translation)
Use `(valAt_iff _ _ _ _).2 fun Z r z J hJ => ?_` and prove the remaining obligations. Establish `a` using `(valAt_iff _ _ _ _).1 h Z (r ≫ spMap (algebraMap E F)) z J hJ`. Establish `e₂ : ptSecT A.A (fieldMap (R` using `R) E F ≫ x) ≫ fieldMap (R := R) E F ▷ A.A = fieldMap (R := R) E F ≫ ptSecT A.A x := by`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]`. Establish `e₃ : (ptSecT A.A (fieldMap (R` using `R) E F ≫ x)).left ≫ (fieldMap (R := R) E F ▷ A.A).left = spMap (algebraMap E F) ≫ (ptSecT A.A x).left := congrArg (fun q => q.left) e₂`.

Rewrite `a` using `[constVal_specMap, ← val_frExt e r hJ, Category.assoc, ← e₃, ← Category.assoc]`. Conclude with `(sval_pullOver _ _ _ _ hJ).trans a`.
-/
theorem valAt_ext {k : ℕ} {t : AbSec A E k} {x : TFK (R := R) E ⟶ A.A} {e : FrAt x} {v : E} (h : ValAt t x e v) :
    ValAt (abPull E F A k t) (fieldMap (R := R) E F ≫ x) (frExt F e) (algebraMap E F v) := by
  refine (valAt_iff _ _ _ _).2 fun Z r z J hJ => ?_
  have a := (valAt_iff _ _ _ _).1 h Z (r ≫ spMap (algebraMap E F)) z J hJ
  have e₂ : ptSecT A.A (fieldMap (R := R) E F ≫ x) ≫ fieldMap (R := R) E F ▷ A.A = fieldMap (R := R) E F ≫ ptSecT A.A x := by
    apply CartesianMonoidalCategory.hom_ext <;> simp [ptSecT]
  have e₃ : (ptSecT A.A (fieldMap (R := R) E F ≫ x)).left ≫ (fieldMap (R := R) E F ▷ A.A).left =
    spMap (algebraMap E F) ≫ (ptSecT A.A x).left := congrArg (fun q => q.left) e₂
  rw [constVal_specMap, ← val_frExt e r hJ, Category.assoc, ← e₃, ← Category.assoc] at a
  exact (sval_pullOver _ _ _ _ hJ).trans a

/- English proof (translation)
Use `letI := @TorusExt.gtGroup`. Establish `hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F` using `(IsScalarTower.algebraMap_eq _ _ _).symm`. Establish `hb : (TorusExt.gtExt D.toPre _ hf g).b = baseMap (R` using `R) E F ≫ g.b := TorusExt.gtExt_b _ hf g`. Establish `hs` using `fun χ (z : Sp F) J (hJ : Good D.toPre.P.L z J) => TorusExt.gtExt_val _ hf g χ hJ`. Take `⟨w₁, hw₁, hv₁⟩` from `exists_frm_ext hw hb`.

Use `⟨_, w₁, hw₁, ?_, coef_ext hG hw hb hs hv₁, fun x fr hfr H k hk wk' hwk' gen' t s v hE hV => ?_⟩` and prove the remaining obligations. Introduce and unpack `n ⟨o, h₁, h₂⟩`. Rewrite `h₁` using `[TorusExt.isNsmul_iff_eq]`. Rewrite `h₂` using `[TorusExt.isZero_iff_eq]`. Use `⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩` and prove the remaining obligations.

Rewrite using `[← map_nsmul, ← h₁, h₂, map_zero]`. Take `⟨wk, gen, hwk⟩` from `SecValue.exists_pow k (SecValue.line_exp k) w hw`. Establish `hv : ∀ (z : Sp F) J, Good D.toPre.P.L z J → val wk' (𝟙 (Sp F)) z J = val wk (spMap (algebraMap E F)) z J` using `fun z J hJ => (hwk' z J hJ).trans ((congrArg (· ^ k) (hv₁ z J hJ)).trans (hwk _ _ z J).symm)`. Take `⟨e, he⟩` from `exists_linearEquiv_expandsF hG U E hk w₀ hw₀`. Take `⟨e', he'⟩` from `exists_linearEquiv_expandsF hG U F hk w₀ hw₀`.

Set `P : Fam D.toPre F k → Prop` to `fun s => ∃ v, ValAt (e'.symm s) (fieldMap (R := R) E F ≫ x) (frExt F fr) v ∧ SumF I F (coef s _ wk') v`. Establish `P0 : P 0` using `⟨0, by rw [map_zero]; exact valAt_zero _ _, by`. Rewrite using `[show coef (0 : Fam D.toPre F k) _ wk' = fun _ => 0 from funext (coef_zero gen')]`. Conclude with `sumF_zero⟩`. Establish `Pl : ∀ (c : F) s s', P s → P s' → P (c • s + s')`.

Introduce and unpack `c s s' ⟨a, h₁, h₂⟩ ⟨a', h₁', h₂'⟩`. Use `⟨c * a + a', by rw [map_add, map_smul]; exact valAt_lin h₁ h₁' c, ?_⟩` and prove the remaining obligations. Rewrite using `[show coef (c • s + s') _ wk' = _ from funext (coef_lin gen' s s' c)]`. Conclude with `sumF_lin h₂ h₂' c`. Establish `all : P s`.

Establish `hx : s ∈ Submodule.span F (Set.range (famPull D.toPre E F hG k))` using `(isExtension_famPull D.toPre E F hG hk).span ▸ Submodule.mem_top`. Use `clear hE`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨s₀, rfl⟩` from `hy`.

Establish `h₀` using `(he _ _).2 (e.apply_symm_apply s₀)`. Take `⟨v₀, hv₀⟩` from `SecComb.exists_valAt (e.symm s₀) hfr`. Use `⟨algebraMap E F v₀, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← (he' _ _).1 (expandsF_pull (F := F) U.toUnifPre hG h₀), e'.symm_apply_apply]`. Conclude with `valAt_ext hv₀`.

Rewrite using `[show coef (famPull D.toPre E F hG k s₀) _ wk' = _ from funext (coef_ext hG gen hb hs hv s₀)]`. Conclude with `sumF_map (RingHom.id R) (Ideal.map_id I).le (algebraMap E F) (fun r => (IsScalarTower.algebraMap_apply _ _ _ _).symm) (H k hk wk (fun z J _ => hwk _ _ z J) gen _ _ _ h₀ hv₀)`. Consider the case `zero => exact P0`. Consider the case `add a b _ _ ha hb => simpa only [one_smul] using Pl 1 a b ha hb`. Consider the case `smul c a _ ha => simpa only [add_zero] using Pl c a 0 ha P0`.

Take `⟨v', h₁, h₂⟩` from `all`. Rewrite `h₁` using `[show e'.symm s = t from e'.symm_apply_eq.2 ((he' _ _).1 hE).symm]`. Rewrite using `[valAt_unique hV h₁]` and apply the resulting hypothesis.
-/
theorem exists_ext (hG : GlobalFnsSt) (U : Unif I D A G) {w₀ : W0 U.toUnifPre} (hw₀ : w₀.IsGen) (g : GtPtF D.toPre E)
    {w : Frm D.toPre E 1 g.b} (hw : w.IsGen) : ∃ (g₁ : GtPtF D.toPre F) (w₁ : Frm D.toPre F 1 g₁.b), w₁.IsGen ∧
      (∀ n, (∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) → ∃ o, GtPtF.IsNsmul n g₁ o ∧ o.IsZero) ∧
      (∀ s χ, coef (famPull D.toPre E F hG 1 s) g₁ w₁ χ = algebraMap E F (coef s g w χ)) ∧
      ∀ (x : TFK (R := R) E ⟶ A.A) (fr : FrAt x), fr.IsGen → LiesOver U.toUnifPre E w₀ g w x fr →
        LiesOver U.toUnifPre F w₀ g₁ w₁ (fieldMap (R := R) E F ≫ x) (frExt F fr) := by
  letI := @TorusExt.gtGroup
  have hf : (algebraMap E F).comp (algebraMap (FractionRing R) E) = algebraMap (FractionRing R) F :=
    (IsScalarTower.algebraMap_eq _ _ _).symm
  have hb : (TorusExt.gtExt D.toPre _ hf g).b = baseMap (R := R) E F ≫ g.b := TorusExt.gtExt_b _ hf g
  have hs := fun χ (z : Sp F) J (hJ : Good D.toPre.P.L z J) => TorusExt.gtExt_val _ hf g χ hJ
  obtain ⟨w₁, hw₁, hv₁⟩ := exists_frm_ext hw hb
  refine ⟨_, w₁, hw₁, ?_, coef_ext hG hw hb hs hv₁, fun x fr hfr H k hk wk' hwk' gen' t s v hE hV => ?_⟩
  · rintro n ⟨o, h₁, h₂⟩
    rw [TorusExt.isNsmul_iff_eq] at h₁
    rw [TorusExt.isZero_iff_eq] at h₂
    refine ⟨0, (TorusExt.isNsmul_iff_eq _ _ _).2 ?_, (TorusExt.isZero_iff_eq _).2 rfl⟩
    rw [← map_nsmul, ← h₁, h₂, map_zero]
  obtain ⟨wk, gen, hwk⟩ := SecValue.exists_pow k (SecValue.line_exp k) w hw
  have hv : ∀ (z : Sp F) J, Good D.toPre.P.L z J → val wk' (𝟙 (Sp F)) z J = val wk (spMap (algebraMap E F)) z J :=
    fun z J hJ => (hwk' z J hJ).trans ((congrArg (· ^ k) (hv₁ z J hJ)).trans (hwk _ _ z J).symm)
  obtain ⟨e, he⟩ := exists_linearEquiv_expandsF hG U E hk w₀ hw₀
  obtain ⟨e', he'⟩ := exists_linearEquiv_expandsF hG U F hk w₀ hw₀
  let P : Fam D.toPre F k → Prop := fun s => ∃ v, ValAt (e'.symm s) (fieldMap (R := R) E F ≫ x) (frExt F fr) v ∧
    SumF I F (coef s _ wk') v
  have P0 : P 0 := ⟨0, by rw [map_zero]; exact valAt_zero _ _, by
    rw [show coef (0 : Fam D.toPre F k) _ wk' = fun _ => 0 from funext (coef_zero gen')]; exact sumF_zero⟩
  have Pl : ∀ (c : F) s s', P s → P s' → P (c • s + s') := by
    rintro c s s' ⟨a, h₁, h₂⟩ ⟨a', h₁', h₂'⟩
    refine ⟨c * a + a', by rw [map_add, map_smul]; exact valAt_lin h₁ h₁' c, ?_⟩
    rw [show coef (c • s + s') _ wk' = _ from funext (coef_lin gen' s s' c)]
    exact sumF_lin h₂ h₂' c
  have all : P s := by
    have hx : s ∈ Submodule.span F (Set.range (famPull D.toPre E F hG k)) :=
      (isExtension_famPull D.toPre E F hG hk).span ▸ Submodule.mem_top
    clear hE
    induction hx using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨s₀, rfl⟩ := hy
      have h₀ := (he _ _).2 (e.apply_symm_apply s₀)
      obtain ⟨v₀, hv₀⟩ := SecComb.exists_valAt (e.symm s₀) hfr
      refine ⟨algebraMap E F v₀, ?_, ?_⟩
      · rw [← (he' _ _).1 (expandsF_pull (F := F) U.toUnifPre hG h₀), e'.symm_apply_apply]
        exact valAt_ext hv₀
      · rw [show coef (famPull D.toPre E F hG k s₀) _ wk' = _ from funext (coef_ext hG gen hb hs hv s₀)]
        exact sumF_map (RingHom.id R) (Ideal.map_id I).le (algebraMap E F)
          (fun r => (IsScalarTower.algebraMap_apply _ _ _ _).symm)
          (H k hk wk (fun z J _ => hwk _ _ z J) gen _ _ _ h₀ hv₀)
    | zero => exact P0
    | add a b _ _ ha hb => simpa only [one_smul] using Pl 1 a b ha hb
    | smul c a _ ha => simpa only [add_zero] using Pl c a 0 ha P0
  obtain ⟨v', h₁, h₂⟩ := all
  rw [show e'.symm s = t from e'.symm_apply_eq.2 ((he' _ _).1 hE).symm] at h₁
  rwa [valAt_unique hV h₁]

end Lies

section Pull

open GlobalTheory.ArcPull GlobalTheory.ThetaBaseChange GlobalTheory.ThetaDescent GlobalTheory.TorusExt
open GlobalTheory.PsiEvenPull (proj)

/- English proof (translation)
Establish `e₁ : b ^ ((k : ℤ) - 1) * d * e⁻¹ * o * g * w = o ^ k * (g' * w')`. Rewrite using `[h₂, h₃]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]`. Use `module`.

Establish `e₂` using `congrArg Units.val e₁`. Rewrite `h` using `[h₁, h₄]`. Simplify using `only [Units.val_mul, Units.val_pow_eq_pow_val] at e₂ h`. Use `(Units.mul_right_inj (o ^ k)).1 ?_` and prove the remaining obligations. Rewrite using `[Units.val_pow_eq_pow_val]`.

Take the linear combination `h + σ' * e₂`.
-/
theorem coef_alg {S : Type} [CommRing S] (k : ℕ) {c σ σ' : S} {ρ ρ' g g' w w' b d e o : Sˣ}
    (h : c * ρ.val ^ k = σ * g.val * w.val) (h₁ : σ = (b ^ ((k : ℤ) - 1) * d * e⁻¹ * o).val * σ')
    (h₂ : g = d⁻¹ * e * b * o⁻¹ * g') (h₃ : w = o ^ k * (b ^ k)⁻¹ * w') (h₄ : ρ = o * ρ') :
    c * ρ'.val ^ k = σ' * g'.val * w'.val := by
  have e₁ : b ^ ((k : ℤ) - 1) * d * e⁻¹ * o * g * w = o ^ k * (g' * w') := by
    rw [h₂, h₃]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv, ofMul_zpow, ofMul_pow]
    module
  have e₂ := congrArg Units.val e₁
  rw [h₁, h₄] at h
  simp only [Units.val_mul, Units.val_pow_eq_pow_val] at e₂ h
  refine (Units.mul_right_inj (o ^ k)).1 ?_
  rw [Units.val_pow_eq_pow_val]
  linear_combination h + σ' * e₂

variable {R R' : Type} [CommRing R] [IsDomain R] [CommRing R'] [IsDomain R'] {φ : R →+* R'}
  {F : Type} [Field F] [Algebra (FractionRing R) F] [Algebra (FractionRing R') F]

def FamUp {D : DegPre R} {D' : DegPre R'} (hD : IsPullDeg φ D D') (κ : (DegPre.BF D' F).left ⟶ (DegPre.BF D F).left) {k : ℕ}
    (s' : Fam D' F k) (s : Fam D F k) : Prop := ∀ α β, hD.xe α = β → SecUp hD κ (s'.s α) (s.s β)

/- English proof (translation)
Use `coef_eq fun z J' hJ' => ?_` and prove the remaining obligations. Take `⟨J, hJ⟩` from `exists_good' D.P.isLB (Z := Sp F) z`. Establish `a` using `isCoef_coef g hw (hD.xe α) s z J hJ`. Establish `z₁ : (lift (𝟙 (TF (R` using `R) F)) g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)`. Establish `z₂ : (lift (𝟙 (TF (R` using `R) F)) g.b).left ≫ (DegPre.prB D F).left = g.b.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)`.

Establish `z₃ : (lift (𝟙 (TF (R` using `R') F)) g'.b).left ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R') F)) g'.b)`. Establish `z₄ : (lift (𝟙 (TF (R` using `R') F)) g'.b).left ≫ (DegPre.prB D' F).left = g'.b.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R') F)) g'.b)`. Establish `e : (lift (𝟙 (TF (R` using `R') F)) g'.b).left ≫ κ = (lift (𝟙 (TF (R := R) F)) g.b).left := by`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.fst).trans (z₃.trans z₁.symm))`.

Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.snd.symm).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) z₄).trans (hg.1.trans z₂.symm))))`. Establish `a₁` using `hs α _ rfl _ (lift (𝟙 (TF (R := R') F)) g'.b).left z J J' hJ hJ'`. Rewrite `a₁` using `[prod_fam D' F (lift (𝟙 (TF (R := R') F)) g'.b) α k (om hD.w z J J'), lift_snd, e]`. Establish `a₂` using `pullGt_val hD hg α (𝟙 _) hJ hJ'`. Simplify using `only [Category.id_comp] at a₂`.

Establish `pm` using `(maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _ (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig`. Establish `a₄` using `pmaps_om (fun _ => hD.he) pm (TF (R := R') F).hom z hJ hJ'`. Rewrite `a₄` using `[Fintype.prod_unique, zpow_one, hF.base]`. Conclude with `coef_alg (S := (Sp F).presheaf.stalk z) k a a₁ a₂ (vw z J J' hJ hJ') a₄`.
-/
theorem coef_pull {D : DegPre R} {D' : DegPre R'} {hD : IsPullDeg φ D D'} (hF : Compat φ F) {κ κ'}
    (hκ : IsFibreIso hD (F := F) κ κ') {k : ℕ} {g : GtPtF D F} {g' : GtPtF D' F} (hg : IsPullGtF φ hD F g g')
    {w : Frm D F k g.b} {w' : Frm D' F k g'.b} (hw : w.IsGen)
    (vw : ∀ (y : Sp F) J J', Good D.P.L y J → Good D'.P.L y J' → vS w y J =
        om hD.w y J J' (1 : TF (R := R') F ⟶ D'.P.A).left ^ k * (om hD.w y J J' g'.b.left ^ k)⁻¹ * vS w' y J')
    {s : Fam D F k} {s' : Fam D' F k} (hs : FamUp hD κ s' s) (α : D'.X) : coef s' g' w' α = coef s g w (hD.xe α) := by
  refine coef_eq fun z J' hJ' => ?_
  obtain ⟨J, hJ⟩ := exists_good' D.P.isLB (Z := Sp F) z
  have a := isCoef_coef g hw (hD.xe α) s z J hJ
  have z₁ : (lift (𝟙 (TF (R := R) F)) g.b).left ≫ (fst (TF (R := R) F) D.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R) F)) g.b)
  have z₂ : (lift (𝟙 (TF (R := R) F)) g.b).left ≫ (DegPre.prB D F).left = g.b.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R) F)) g.b)
  have z₃ : (lift (𝟙 (TF (R := R') F)) g'.b).left ≫ (fst (TF (R := R') F) D'.P.A).left = 𝟙 _ :=
    congrArg (fun q => q.left) (lift_fst (𝟙 (TF (R := R') F)) g'.b)
  have z₄ : (lift (𝟙 (TF (R := R') F)) g'.b).left ≫ (DegPre.prB D' F).left = g'.b.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TF (R := R') F)) g'.b)
  have e : (lift (𝟙 (TF (R := R') F)) g'.b).left ≫ κ = (lift (𝟙 (TF (R := R) F)) g.b).left := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.fst).trans (z₃.trans z₁.symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) hκ.snd.symm).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) z₄).trans (hg.1.trans z₂.symm))))
  have a₁ := hs α _ rfl _ (lift (𝟙 (TF (R := R') F)) g'.b).left z J J' hJ hJ'
  rw [prod_fam D' F (lift (𝟙 (TF (R := R') F)) g'.b) α k (om hD.w z J J'), lift_snd, e] at a₁
  have a₂ := pullGt_val hD hg α (𝟙 _) hJ hJ'
  simp only [Category.id_comp] at a₂
  have pm := (maps_iff hD.w _ (fun _ => eSec D.P.A) _ D'.rig D.rig (specOf φ) _
    (rigPull_le (proj hD) (specOf φ) hD.he D.P.L) (fun _ => rfl)).1 hD.w_rig
  have a₄ := pmaps_om (fun _ => hD.he) pm (TF (R := R') F).hom z hJ hJ'
  rw [Fintype.prod_unique, zpow_one, hF.base] at a₄
  exact coef_alg (S := (Sp F).presheaf.stalk z) k a a₁ a₂ (vw z J J' hJ hJ') a₄

variable {A : PolAV (Spec (CommRingCat.of (FractionRing R)))} {A' : PolAV (Spec (CommRingCat.of (FractionRing R')))}
  {Φ : A'.A.left ⟶ A.A.left} {v : LB.Iso A'.L (A.L.pull Φ)}
  {Ω : (TFK (R := R') F ⊗ A'.A).left ⟶ (TFK (R := R) F ⊗ A.A).left}

variable (v Ω) in

def AbUp {k : ℕ} (t' : SecA A' F k) (t : SecA A F k) : Prop :=
  ∀ (Z : Scheme.{0}) (r : Z ⟶ (TFK (R := R') F ⊗ A'.A).left) (z : Z) J J', Good A.L z J → Good A'.L z J' →
    sA t (r ≫ Ω) z J = (om v z J J' (r ≫ (snd (TFK (R := R') F) A'.A).left) ^ (k : ℤ)).val * sA t' r z J'

variable (v) in

def FrUp {x' : TFK (R := R') F ⟶ A'.A} (e' : FrAt x') {x : TFK (R := R) F ⟶ A.A} (e : FrAt x) (ρ : F) : Prop :=
  ∀ (z : Sp F) J J', Good A.L z J → Good A'.L z J' →
    (om (Z := Sp F) v z J J' x'.left).val * (vS e' z J').val = constVal (𝟙 (Sp F)) z ρ * (vS e z J).val

/- English proof (translation)
Use `(Units.mul_right_inj (o ^ (k : ℤ))).1 (h₁.symm.trans (h.trans ?_))` and prove the remaining obligations. Establish `e₁ : κ (ρ⁻¹).val * κ ρ = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`. Establish `e₂ : e.val = κ (ρ⁻¹).val * (o.val * e'.val)` using `by rw [h₂, ← _root_.mul_assoc, e₁, _root_.one_mul]`. Simplify using `only [zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]`. Rewrite using `[e₂]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem val_alg {S F : Type} [CommRing S] [Field F] (κ : F →+* S) (k : ℕ) {σ σ' : S} {o e e' : Sˣ} {c : F} {ρ : Fˣ}
    (h : σ = κ c * (e ^ k).val) (h₁ : σ = (o ^ (k : ℤ)).val * σ') (h₂ : o.val * e'.val = κ ρ * e.val) :
    σ' = κ (c * (ρ⁻¹ ^ k).val) * (e' ^ k).val := by
  refine (Units.mul_right_inj (o ^ (k : ℤ))).1 (h₁.symm.trans (h.trans ?_))
  have e₁ : κ (ρ⁻¹).val * κ ρ = 1 := by rw [← map_mul, Units.inv_mul, map_one]
  have e₂ : e.val = κ (ρ⁻¹).val * (o.val * e'.val) := by rw [h₂, ← _root_.mul_assoc, e₁, _root_.one_mul]
  simp only [zpow_natCast, Units.val_pow_eq_pow_val, map_mul, map_pow]
  rw [e₂]
  ring

/- English proof (translation)
Introduce `z J' hJ'`. Take `⟨J, hJ⟩` from `exists_good' A.isLB (Z := Sp F) z`. Establish `z₁ : (ptSecT A.A x).left ≫ (fst (TFK (R` using `R) F) A.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TFK (R := R) F)) x)`. Establish `z₂ : (ptSecT A.A x).left ≫ (snd (TFK (R` using `R) F) A.A).left = x.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) x)`. Establish `z₃ : (ptSecT A'.A x').left ≫ (fst (TFK (R` using `R') F) A'.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TFK (R := R') F)) x')`.

Establish `z₄ : (ptSecT A'.A x').left ≫ (snd (TFK (R` using `R') F) A'.A).left = x'.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R') F)) x')`. Establish `e₀ : (ptSecT A'.A x').left ≫ Ω = (ptSecT A.A x).left`. Use `pullback.hom_ext ?_ ?_` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans (z₃.trans z₁.symm))`. Conclude with `(Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) z₄).trans (hx.trans z₂.symm))))`.

Establish `a₁` using `ht _ (ptSecT A'.A x').left z J J' hJ hJ'`. Rewrite `a₁` using `[e₀, z₄]`. Establish `a` using `h z J hJ`. Establish `a₂` using `he z J J' hJ hJ'`. Rewrite `a`, the goal using `[FrameMove.val_powFrame, zpow_natCast, cst_eq]`.

Rewrite `a₂` using `[show constVal (𝟙 (Sp F)) z ρ.val = cstH (R := R) z ρ.val from cst_eq (R := R) z _]`. Conclude with `val_alg (S := (Sp F).presheaf.stalk z) (cstH (R := R) z) k a a₁ a₂`.
-/
theorem valAt_pull (h₁ : Ω ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R') F) A'.A).left)
    (h₂ : Ω ≫ (snd (TFK (R := R) F) A.A).left = (snd (TFK (R := R') F) A'.A).left ≫ Φ) {k : ℕ} {t' : SecA A' F k}
    {t : SecA A F k} (ht : AbUp v Ω t' t) {x' : TFK (R := R') F ⟶ A'.A} {e' : FrAt x'} {x : TFK (R := R) F ⟶ A.A}
    {e : FrAt x} (hx : x'.left ≫ Φ = x.left) {ρ : Fˣ} (he : FrUp v e' e ρ) {c : F} (h : ValAt t x e c) :
    ValAt t' x' e' (c * (ρ⁻¹ ^ k).val) := by
  intro z J' hJ'
  obtain ⟨J, hJ⟩ := exists_good' A.isLB (Z := Sp F) z
  have z₁ : (ptSecT A.A x).left ≫ (fst (TFK (R := R) F) A.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TFK (R := R) F)) x)
  have z₂ : (ptSecT A.A x).left ≫ (snd (TFK (R := R) F) A.A).left = x.left := congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R) F)) x)
  have z₃ : (ptSecT A'.A x').left ≫ (fst (TFK (R := R') F) A'.A).left = 𝟙 _ := congrArg (fun q => q.left) (lift_fst (𝟙 (TFK (R := R') F)) x')
  have z₄ : (ptSecT A'.A x').left ≫ (snd (TFK (R := R') F) A'.A).left = x'.left :=
    congrArg (fun q => q.left) (lift_snd (𝟙 (TFK (R := R') F)) x')
  have e₀ : (ptSecT A'.A x').left ≫ Ω = (ptSecT A.A x).left := by
    refine pullback.hom_ext ?_ ?_
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₁).trans (z₃.trans z₁.symm))
    · exact (Category.assoc _ _ _).trans ((congrArg (_ ≫ ·) h₂).trans ((Category.assoc _ _ _).symm.trans
        ((congrArg (· ≫ _) z₄).trans (hx.trans z₂.symm))))
  have a₁ := ht _ (ptSecT A'.A x').left z J J' hJ hJ'
  rw [e₀, z₄] at a₁
  have a := h z J hJ
  have a₂ := he z J J' hJ hJ'
  rw [FrameMove.val_powFrame, zpow_natCast, cst_eq] at a ⊢
  rw [show constVal (𝟙 (Sp F)) z ρ.val = cstH (R := R) z ρ.val from cst_eq (R := R) z _] at a₂
  exact val_alg (S := (Sp F).presheaf.stalk z) (cstH (R := R) z) k a a₁ a₂

variable {I : Ideal R} {I' : Ideal R'} {D : DegData R I} {D' : DegData R' I'} {hD : IsPullDeg φ D.toPre D'.toPre}
  {G : Over (Spec (CommRingCat.of R))} [GrpObj G] [IsCommMonObj G]
  {G' : Over (Spec (CommRingCat.of R'))} [GrpObj G'] [IsCommMonObj G']

/- English proof (translation)
Use `letI := @TorusExt.gtGroup`. Establish `hg` using `isPullGtF_pullGt hD hG hF g`. Take `⟨w₁, hw₁, vw₁⟩` from `FamPull.exists_lineDown hD hF hg.1 w hw`. Take `⟨w', hw', vw'⟩` from `PhiProj.exists_scaled hw₁ (ρ⁻¹).val (Units.ne_zero _)`. Use `⟨_, w', hw', ?_, fun s s' hs α => ?_, fun x' e' x e gen hx he H k hk wk' hwk' gen' t' s' c' E' hV => ?_⟩` and prove the remaining obligations.

Introduce and unpack `n ⟨o, o₁, o₂⟩`. Rewrite `o₁` using `[isNsmul_iff_eq]`. Rewrite `o₂` using `[isZero_iff_eq]`. Use `⟨0, (isNsmul_iff_eq _ _ _).2 ?_, (isZero_iff_eq _).2 rfl⟩` and prove the remaining obligations. Rewrite using `[← map_nsmul, ← o₁, o₂, map_zero]`.

Rewrite using `[coef_scale hw₁ vw', coef_pull hF hκ hg hw vw₁ hs, mul_right_comm, Units.inv_mul, _root_.one_mul]`. Take `⟨wk, genk, hwk⟩` from `SecValue.exists_pow k (SecValue.line_exp k) w hw`. Take `⟨wk₁, gen₁, vk₁⟩` from `FamPull.exists_lineDown hD hF hg.1 wk genk`. Establish `p₁ : ∀ (z : Sp F) J', Good D'.toPre.P.L z J' → vS wk₁ z J' = vS w₁ z J' ^ k` using `fun z J' hJ' => by`. Take `⟨J, hJ⟩` from `exists_good' D.toPre.P.isLB (Z := Sp F) z`.

Establish `a` using `vk₁ z J J' hJ hJ'`. Establish `b : vS wk z J = vS w z J ^ k` using `hwk _ _ z J`. Rewrite `a` using `[b, vw₁ z J J' hJ hJ', pow_one, pow_one, mul_pow, mul_pow, inv_pow]`. Conclude with `(mul_left_cancel a).symm`. Establish `p₂ : ∀ z J', Good D'.toPre.P.L z J' → (val wk' (𝟙 _) z J').val = cst F z (ρ⁻¹ ^ k).val * (val wk₁ (𝟙 _) z J').val` using `fun z J' hJ' => by`.

Establish `b : val wk₁ (𝟙 _) z J' = val w₁ (𝟙 _) z J' ^ k` using `p₁ z J' hJ'`. Rewrite using `[hwk' z J' hJ', b, Units.val_pow_eq_pow_val, vw' z J' hJ', mul_pow, cst_eq, cst_eq, Units.val_pow_eq_pow_val, Units.val_pow_eq_pow_val, map_pow]`. Take `⟨t, s, E, ht, hs⟩` from `hE k hk t' s' E'`. Take `⟨c, hc⟩` from `SecComb.exists_valAt t gen`. Establish `S` using `sumF_lin (sumF_equiv hD.xe.toEquiv (sumF_map φ hI (RingHom.id F) hF (H k hk wk (fun z J _ => hwk _ _ z J) genk t s c E hc))) sumF_zero (ρ⁻¹ ^ k).val`.

Rewrite using `[valAt_unique hV (valAt_pull h₁ h₂ ht hx he hc), show coef s' _ wk' = _ from funext fun α => (coef_scale gen₁ p₂ s' α).trans (congrArg _ (coef_pull hF hκ hg genk vk₁ hs α)), mul_comm c]`. Simplify using `only [add_zero] at S`. Conclude with `S`.
-/
theorem exists_point (hG : GlobalFnsSt) (hI : I.map φ ≤ I') (hF : Compat φ F) {κ κ'} (hκ : IsFibreIso hD (F := F) κ κ')
    (h₁ : Ω ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R') F) A'.A).left)
    (h₂ : Ω ≫ (snd (TFK (R := R) F) A.A).left = (snd (TFK (R := R') F) A'.A).left ≫ Φ)
    {U : UnifPre I D A G} {U' : UnifPre I' D' A' G'} {w₀ : W0 U} {w₀' : W0 U'}
    (hE : ∀ k, 1 ≤ k → ∀ t' s', U'.ExpandsF F k w₀' t' s' → ∃ t s, U.ExpandsF F k w₀ t s ∧ AbUp v Ω t' t ∧ FamUp hD κ s' s)
    (g : GtPtF D.toPre F) {w : Frm D.toPre F 1 g.b} (hw : w.IsGen) (ρ : Fˣ) :
    ∃ (g' : GtPtF D'.toPre F) (w' : Frm D'.toPre F 1 g'.b), w'.IsGen ∧
      (∀ n, (∃ o, GtPtF.IsNsmul n g o ∧ o.IsZero) → ∃ o, GtPtF.IsNsmul n g' o ∧ o.IsZero) ∧
      (∀ s s', FamUp hD κ s' s → ∀ α, coef s' g' w' α * ρ = coef s g w (hD.xe α)) ∧
      ∀ (x' : TFK (R := R') F ⟶ A'.A) (e' : FrAt x') (x : TFK (R := R) F ⟶ A.A) (e : FrAt x), e.IsGen →
        x'.left ≫ Φ = x.left → FrUp v e' e ρ → LiesOver U F w₀ g w x e → LiesOver U' F w₀' g' w' x' e' := by
  letI := @TorusExt.gtGroup
  have hg := isPullGtF_pullGt hD hG hF g
  obtain ⟨w₁, hw₁, vw₁⟩ := FamPull.exists_lineDown hD hF hg.1 w hw
  obtain ⟨w', hw', vw'⟩ := PhiProj.exists_scaled hw₁ (ρ⁻¹).val (Units.ne_zero _)
  refine ⟨_, w', hw', ?_, fun s s' hs α => ?_, fun x' e' x e gen hx he H k hk wk' hwk' gen' t' s' c' E' hV => ?_⟩
  · rintro n ⟨o, o₁, o₂⟩
    rw [isNsmul_iff_eq] at o₁
    rw [isZero_iff_eq] at o₂
    refine ⟨0, (isNsmul_iff_eq _ _ _).2 ?_, (isZero_iff_eq _).2 rfl⟩
    rw [← map_nsmul, ← o₁, o₂, map_zero]
  · rw [coef_scale hw₁ vw', coef_pull hF hκ hg hw vw₁ hs, mul_right_comm, Units.inv_mul, _root_.one_mul]
  obtain ⟨wk, genk, hwk⟩ := SecValue.exists_pow k (SecValue.line_exp k) w hw
  obtain ⟨wk₁, gen₁, vk₁⟩ := FamPull.exists_lineDown hD hF hg.1 wk genk
  have p₁ : ∀ (z : Sp F) J', Good D'.toPre.P.L z J' → vS wk₁ z J' = vS w₁ z J' ^ k := fun z J' hJ' => by
    obtain ⟨J, hJ⟩ := exists_good' D.toPre.P.isLB (Z := Sp F) z
    have a := vk₁ z J J' hJ hJ'
    have b : vS wk z J = vS w z J ^ k := hwk _ _ z J
    rw [b, vw₁ z J J' hJ hJ', pow_one, pow_one, mul_pow, mul_pow, inv_pow] at a
    exact (mul_left_cancel a).symm
  have p₂ : ∀ z J', Good D'.toPre.P.L z J' →
      (val wk' (𝟙 _) z J').val = cst F z (ρ⁻¹ ^ k).val * (val wk₁ (𝟙 _) z J').val := fun z J' hJ' => by
    have b : val wk₁ (𝟙 _) z J' = val w₁ (𝟙 _) z J' ^ k := p₁ z J' hJ'
    rw [hwk' z J' hJ', b, Units.val_pow_eq_pow_val, vw' z J' hJ', mul_pow, cst_eq, cst_eq, Units.val_pow_eq_pow_val,
      Units.val_pow_eq_pow_val, map_pow]
  obtain ⟨t, s, E, ht, hs⟩ := hE k hk t' s' E'
  obtain ⟨c, hc⟩ := SecComb.exists_valAt t gen
  have S := sumF_lin (sumF_equiv hD.xe.toEquiv (sumF_map φ hI (RingHom.id F) hF
    (H k hk wk (fun z J _ => hwk _ _ z J) genk t s c E hc))) sumF_zero (ρ⁻¹ ^ k).val
  rw [valAt_unique hV (valAt_pull h₁ h₂ ht hx he hc),
    show coef s' _ wk' = _ from funext fun α => (coef_scale gen₁ p₂ s' α).trans
      (congrArg _ (coef_pull hF hκ hg genk vk₁ hs α)), mul_comm c]
  simp only [add_zero] at S
  exact S

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨wL, hwL, -, -, hlev⟩` from `(isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU`. Establish `n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _` using `by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]`. Establish `n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _` using `by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]`. Establish `n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _` using `by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]`. Establish `hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ)` using `(Category.assoc _ _ _).trans hΦ`.

Establish `pv` using `(isGen_iff v).1 hv`. Establish `pL` using `(isGen_iff wL).1 hwL`. Take `⟨u, hu, huv⟩` from `exists_unpull hw U.gen.inv.left n₁ rfl`. Take `⟨uv, T⟩` from `exists_comp A.isLB u v hu pv U.LG.isLB A'.isLB`. Take `⟨w'', g'', hw''⟩` from `exists_pull_iso (T.pgen_comp A.isLB hu pv) U'.gen.hom.left hΦ`.

Establish `p''` using `(isGen_iff w'').1 g''`. Take `⟨w', T'⟩` from `exists_cancel U.LG.isLB wL w'' pL p'' U'.LG.isLB (pull_isLB A'.isLB _)`. Establish `hw' : w'.IsGen` using `(isGen_iff w').2 (T'.pgen_cancel U.LG.isLB pL p'')`. Take `⟨v₂, hv₂, hv₂v⟩` from `exists_pull_iso pv U'.gen.hom.left rfl`. Establish `hvv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.A.left) (z : Z) (j : A.L.ι) (i : A'.L.ι), Φ (f z) ∈ A.L.U j → f z ∈ A'.L.U i → gw v f z j i = isoVal v₂ (f ≫ U'.gen.inv.left) z j i` using `fun Z f z j i hj hi => by`.

Establish `e : (f ≫ U'.gen.inv.left) ≫ U'.gen.hom.left = f` using `by rw [Category.assoc, n₂, Category.comp_id]`. Establish `pt : U'.gen.hom.left ((f ≫ U'.gen.inv.left) z) = f z` using `congrArg (fun q : Z ⟶ A'.A.left => q z) e`. Rewrite using `[hv₂v Z _ z j i (show Φ (U'.gen.hom.left ((f ≫ U'.gen.inv.left) z)) ∈ _ from pt.symm ▸ hj) (pt.symm ▸ hi), e]`. Establish `hsq : ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R')).obj G').left) (z : Z) (j : U.LG.L.ι) (j' : U'.LG.L.ι) (i : A.L.ι) (i' : A'.L.ι), (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (pullback.fst G'.hom (jK R') (f z)) ∈ U.LG.L.U j → pullback.fst G'.hom (jK R') (f z) ∈ U'.LG.L …` using `fun Z f z j j' i i' a b c d => by`. Establish `a' : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (Φ (U'.gen.hom.left (f z))) ∈ U.LG.L.U j` using `(congrArg (fun q : _ ⟶ G.left => q (f z) ∈ U.LG.L.U j) hΦ).mpr a`.

Use `Eq.trans ?_ ((hw'' Z f z j i' a d).symm.trans (T' Z f z j j' (fun _ => i') a b (mem_pull.2 d)))` and prove the remaining obligations. Rewrite using `[T Z (f ≫ U'.gen.hom.left) z j i i' a' c d, huv Z ((f ≫ U'.gen.hom.left) ≫ Φ) z j i a' c, hv₂v Z f z i i' c d]`. Simplify using `only [Category.assoc]`. Take `⟨Ω, hΩ₁, hΩ₂⟩` from `exists_cmp hg₂ gΦ.w`. Take `⟨ω, hω₁, hω₂⟩` from `exists_cmp_inv hg₂ gΦ`.

Establish `hΩω : Ω ≫ ω = 𝟙 _` using `cmp_ext gΦ (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp]) (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])`. Set `n : TFK (R` to `R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)`. Establish `hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _` using `congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by`. Apply the tactic sequence `apply CartesianMonoidalCategory.hom_ext <;> simp [n])`. Establish `hn₁ : n.left ≫ (fst (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left := congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)`.

Establish `hn₂ : n.left ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left := congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)`. Establish `hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R` using `R') F) A'.A).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)`. Establish `hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R` using `R') F) A'.A).left = (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left := congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)`. Take `⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G` from `G') F).left ⟶ (UnifPre.GF (G := G) F).left, Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩`. Establish `x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left`.

Rewrite using `[hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω, Category.comp_id]`. Establish `x₂ : Ξ ≫ (snd (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by`. Rewrite using `[hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]`. Use `(congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, hh₂]`.

Simplify using `only [Category.assoc]`. Establish `hΞ₁ : Ξ ≫ (fst (TFK (R` using `R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by`. Rewrite using `[hΞ, Category.assoc, Category.assoc, hn₁]`. Conclude with `(congrArg (_ ≫ ·) hΩ₁).trans hh₁`. Establish `hΞ₂ : Ξ ≫ UnifPre.gFK (G` using `G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by`.

Use `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)` and prove the remaining obligations. Use `Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)` and prove the remaining obligations. Simplify using `only [Category.assoc]`. Use `⟨w', hw', Ω, hΩ₁, hΩ₂, fun k hk => ?_⟩` and prove the remaining obligations. Establish `bij` using `expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw`.

Establish `bij'` using `expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw'`. Use `choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF κ hκ.fst hκ.snd.symm k`. Establish `up : ∀ b, FamUp hD κ (pl b) b` using `fun b α β e Z r z J J' hJ hJ' => by`. Substitute `e` using the available equality. Conclude with `FamFieldPull.IsSecPull.val (hpl b α) (hκ.fam α) r z hJ hJ'`.

Establish `key : ∀ t' s', U'.ExpandsF F k w' t' s' → ∃ t s, U.ExpandsF F k w t s ∧ AbUp v Ω t' t ∧ FamUp hD κ s' s` using `fun a' b' E => by`. Take `⟨a, ha⟩` from `exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'`. Take `⟨b, σ, h₁, h₂⟩` from `(bij.1 a).exists`. Establish `e : pl b = b'`. Use `(bij'.1 a').unique ?_ E` and prove the remaining obligations.

Take `⟨σ', h₁', -⟩` from `E`. Conclude with `⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF κ hκ.fst hκ.snd.symm Ξ hΞ₁ hΞ₂ k σ σ' b (pl b) (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩`. Conclude with `⟨a, b, ⟨σ, h₁, h₂⟩, fun Z r z J J' hJ hJ' => moved_val hΩω hΩ₂ ha r z hJ hJ', e ▸ up b⟩`. Use `⟨fun t s E => ?_, key⟩` and prove the remaining obligations. Take `⟨t', E'⟩` from `(bij'.2 (pl s)).exists`.

Take `⟨a, b, E₁, h₁, h₂⟩` from `key t' _ E'`. Take `rfl : b = s` from `FamPull.fam_up_unique hκ h₂ (up s)`. Take `rfl : a = t` from `(bij.2 b).unique E₁ E`. Conclude with `⟨t', _, E', h₁, h₂⟩`.
-/
theorem exists_expand (hG : GlobalFnsSt) {U : Unif I D A G} {U' : Unif I' D' A' G'}
    {bc : G' ≅ (Over.pullback (specOf φ)).obj G} (hbc : IsMonHom bc.hom) (hU : IsPullUnif φ hD bc U U') (hF : Compat φ F)
    {g : Spec (CommRingCat.of (FractionRing R')) ⟶ Spec (CommRingCat.of (FractionRing R))}
    (hg₂ : jFK (R := R') F ≫ g = jFK (R := R) F) (gΦ : IsPullback Φ A'.A.hom A.A.hom g) (hv : v.IsGen)
    (hΦ : U'.gen.hom.left ≫ Φ ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ))
    {w : W0 U.toUnifPre} (hw : w.IsGen) {κ κ'} (hκ : IsFibreIso hD (F := F) κ κ') :
    ∃ w' : W0 U'.toUnifPre, w'.IsGen ∧ ∃ Ω : (TFK (R := R') F ⊗ A'.A).left ⟶ (TFK (R := R) F ⊗ A.A).left,
      Ω ≫ (fst (TFK (R := R) F) A.A).left = (fst (TFK (R := R') F) A'.A).left ∧
      Ω ≫ (snd (TFK (R := R) F) A.A).left = (snd (TFK (R := R') F) A'.A).left ≫ Φ ∧ ∀ k, 1 ≤ k →
      (∀ t s, U.ExpandsF F k w t s → ∃ t' s', U'.ExpandsF F k w' t' s' ∧ AbUp v Ω t' t ∧ FamUp hD κ s' s) ∧
      ∀ t' s', U'.ExpandsF F k w' t' s' → ∃ t s, U.ExpandsF F k w t s ∧ AbUp v Ω t' t ∧ FamUp hD κ s' s := by
  obtain ⟨wL, hwL, -, -, hlev⟩ := (isPullUnif_iff_stalks R R' I I' φ D D' hD A A' G G' bc U U').1 hU
  have n₁ : U.gen.inv.left ≫ U.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U.gen.inv_hom_id, Over.id_left]
  have n₂ : U'.gen.inv.left ≫ U'.gen.hom.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.inv_hom_id, Over.id_left]
  have n₃ : U'.gen.hom.left ≫ U'.gen.inv.left = 𝟙 _ := by rw [← Over.comp_left, U'.gen.hom_inv_id, Over.id_left]
  have hΦ₃ : (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R') ≫ bc.hom.left ≫ pullback.fst G.hom (specOf φ) := (Category.assoc _ _ _).trans hΦ
  have pv := (isGen_iff v).1 hv
  have pL := (isGen_iff wL).1 hwL
  obtain ⟨u, hu, huv⟩ := exists_unpull hw U.gen.inv.left n₁ rfl
  obtain ⟨uv, T⟩ := exists_comp A.isLB u v hu pv U.LG.isLB A'.isLB
  obtain ⟨w'', g'', hw''⟩ := exists_pull_iso (T.pgen_comp A.isLB hu pv) U'.gen.hom.left hΦ
  have p'' := (isGen_iff w'').1 g''
  obtain ⟨w', T'⟩ := exists_cancel U.LG.isLB wL w'' pL p'' U'.LG.isLB (pull_isLB A'.isLB _)
  have hw' : w'.IsGen := (isGen_iff w').2 (T'.pgen_cancel U.LG.isLB pL p'')
  obtain ⟨v₂, hv₂, hv₂v⟩ := exists_pull_iso pv U'.gen.hom.left rfl
  have hvv : ∀ (Z : Scheme.{0}) (f : Z ⟶ A'.A.left) (z : Z) (j : A.L.ι) (i : A'.L.ι),
      Φ (f z) ∈ A.L.U j → f z ∈ A'.L.U i → gw v f z j i = isoVal v₂ (f ≫ U'.gen.inv.left) z j i := fun Z f z j i hj hi => by
    have e : (f ≫ U'.gen.inv.left) ≫ U'.gen.hom.left = f := by rw [Category.assoc, n₂, Category.comp_id]
    have pt : U'.gen.hom.left ((f ≫ U'.gen.inv.left) z) = f z := congrArg (fun q : Z ⟶ A'.A.left => q z) e
    rw [hv₂v Z _ z j i (show Φ (U'.gen.hom.left ((f ≫ U'.gen.inv.left) z)) ∈ _ from pt.symm ▸ hj) (pt.symm ▸ hi), e]
  have hsq : ∀ (Z : Scheme.{0}) (f : Z ⟶ ((Over.pullback (jK R')).obj G').left) (z : Z) (j : U.LG.L.ι) (j' : U'.LG.L.ι)
      (i : A.L.ι) (i' : A'.L.ι),
      (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) (pullback.fst G'.hom (jK R') (f z)) ∈ U.LG.L.U j →
      pullback.fst G'.hom (jK R') (f z) ∈ U'.LG.L.U j' → (U'.gen.hom.left ≫ Φ) (f z) ∈ A.L.U i →
      U'.gen.hom.left (f z) ∈ A'.L.U i' →
      isoVal w (f ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left) z j i * isoVal v₂ f z i i' =
        gw wL (f ≫ pullback.fst G'.hom (jK R')) z j j' * isoVal w' f z j' i' := fun Z f z j j' i i' a b c d => by
    have a' : (U.gen.inv.left ≫ pullback.fst G.hom (jK R)) (Φ (U'.gen.hom.left (f z))) ∈ U.LG.L.U j :=
      (congrArg (fun q : _ ⟶ G.left => q (f z) ∈ U.LG.L.U j) hΦ).mpr a
    refine Eq.trans ?_ ((hw'' Z f z j i' a d).symm.trans (T' Z f z j j' (fun _ => i') a b (mem_pull.2 d)))
    rw [T Z (f ≫ U'.gen.hom.left) z j i i' a' c d, huv Z ((f ≫ U'.gen.hom.left) ≫ Φ) z j i a' c, hv₂v Z f z i i' c d]
    simp only [Category.assoc]
  obtain ⟨Ω, hΩ₁, hΩ₂⟩ := exists_cmp hg₂ gΦ.w
  obtain ⟨ω, hω₁, hω₂⟩ := exists_cmp_inv hg₂ gΦ
  have hΩω : Ω ≫ ω = 𝟙 _ := cmp_ext gΦ (by rw [Category.assoc, hω₁, hΩ₁, Category.id_comp])
    (by rw [Category.assoc, hω₂, hΩ₂, Category.id_comp])
  let n : TFK (R := R) F ⊗ A.A ⟶ UnifPre.GF (G := G) F := lift (fst _ _) (snd _ _ ≫ U.gen.inv)
  have hn : n.left ≫ (U.toUnifPre.genF F).left = 𝟙 _ := congrArg (fun q => q.left) (show n ≫ U.toUnifPre.genF F = 𝟙 _ by
    apply CartesianMonoidalCategory.hom_ext <;> simp [n])
  have hn₁ : n.left ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left = (fst (TFK (R := R) F) A.A).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : n ≫ fst _ _ = _)
  have hn₂ : n.left ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R) F) A.A).left ≫ U.gen.inv.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : n ≫ snd _ _ = _)
  have hh₁ : (U'.toUnifPre.genF F).left ≫ (fst (TFK (R := R') F) A'.A).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left :=
    congrArg (fun q => q.left) (lift_fst _ _ : U'.toUnifPre.genF F ≫ fst _ _ = _)
  have hh₂ : (U'.toUnifPre.genF F).left ≫ (snd (TFK (R := R') F) A'.A).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ U'.gen.hom.left :=
    congrArg (fun q => q.left) (lift_snd _ _ : U'.toUnifPre.genF F ≫ snd _ _ = _)
  obtain ⟨Ξ, hΞ⟩ : ∃ Ξ : (UnifPre.GF (G := G') F).left ⟶ (UnifPre.GF (G := G) F).left,
      Ξ = (U'.toUnifPre.genF F).left ≫ Ω ≫ n.left := ⟨_, rfl⟩
  have x₁ : (Ξ ≫ (U.toUnifPre.genF F).left) ≫ ω = (U'.toUnifPre.genF F).left := by
    rw [hΞ, Category.assoc _ (Ω ≫ n.left), Category.assoc Ω, hn, Category.comp_id, Category.assoc, hΩω,
      Category.comp_id]
  have x₂ : Ξ ≫ (snd (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (snd (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left ≫ (U'.gen.hom.left ≫ Φ) ≫ U.gen.inv.left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₂, ← Category.assoc Ω]
    refine (congrArg (fun a => _ ≫ a ≫ _) hΩ₂).trans ?_
    rw [← Category.assoc, ← Category.assoc, hh₂]
    simp only [Category.assoc]
  have hΞ₁ : Ξ ≫ (fst (TFK (R := R) F) ((Over.pullback (jK R)).obj G)).left =
      (fst (TFK (R := R') F) ((Over.pullback (jK R')).obj G')).left := by
    rw [hΞ, Category.assoc, Category.assoc, hn₁]
    exact (congrArg (_ ≫ ·) hΩ₁).trans hh₁
  have hΞ₂ : Ξ ≫ UnifPre.gFK (G := G) F = UnifPre.gFK (G := G') F ≫ (bc.hom.left ≫ pullback.fst G.hom (specOf φ)) := by
    refine (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ _) x₂).trans ?_)
    refine Eq.trans ?_ ((congrArg (_ ≫ ·) hΦ₃).trans (Category.assoc _ _ _).symm)
    simp only [Category.assoc]
  refine ⟨w', hw', Ω, hΩ₁, hΩ₂, fun k hk => ?_⟩
  have bij := expandsF_bijective U.toUnifPre F hG hk (U.expand k hk) hw
  have bij' := expandsF_bijective U'.toUnifPre F hG hk (U'.expand k hk) hw'
  choose pl hpl using exists_fam_field_pull hG R R' φ D.toPre D'.toPre hD F hF κ hκ.fst hκ.snd.symm k
  have up : ∀ b, FamUp hD κ (pl b) b := fun b α β e Z r z J J' hJ hJ' => by
    subst e
    exact FamFieldPull.IsSecPull.val (hpl b α) (hκ.fam α) r z hJ hJ'
  have key : ∀ t' s', U'.ExpandsF F k w' t' s' → ∃ t s, U.ExpandsF F k w t s ∧ AbUp v Ω t' t ∧ FamUp hD κ s' s :=
      fun a' b' E => by
    obtain ⟨a, ha⟩ := exists_moved A.isLB A'.isLB hω₂ n₂ hv₂ hvv a'
    obtain ⟨b, σ, h₁, h₂⟩ := (bij.1 a).exists
    have e : pl b = b' := by
      refine (bij'.1 a').unique ?_ E
      obtain ⟨σ', h₁', -⟩ := E
      exact ⟨σ', h₁', expandsG_transport R R' I I' φ D D' hD A A' G G' bc hbc U.toUnifPre U'.toUnifPre wL hwL hlev F hF
        κ hκ.fst hκ.snd.symm Ξ hΞ₁ hΞ₂ k σ σ' b (pl b)
        (moved_sec A.isLB A'.isLB n₃ n₁ hΦ₃ hsq hvv x₁ x₂ ha h₁ h₁') (hpl b) h₂⟩
    exact ⟨a, b, ⟨σ, h₁, h₂⟩, fun Z r z J J' hJ hJ' => moved_val hΩω hΩ₂ ha r z hJ hJ', e ▸ up b⟩
  refine ⟨fun t s E => ?_, key⟩
  obtain ⟨t', E'⟩ := (bij'.2 (pl s)).exists
  obtain ⟨a, b, E₁, h₁, h₂⟩ := key t' _ E'
  obtain rfl : b = s := FamPull.fam_up_unique hκ h₂ (up s)
  obtain rfl : a = t := (bij.2 b).unique E₁ E
  exact ⟨t', _, E', h₁, h₂⟩

end Pull

end GlobalTheory.TermsMove
