import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.AtBase
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.NGData
import Formalism.LocalToGlobal.SiegelLatticeTheory.ClosedLocalOrbits.GaugeLatticeShifts.TermDefPf
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LocalTermsSameDoubleCosetSameDatumStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.RationalIsometryExtendsLocalIsometryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnsignedLocalTermRowLatticeIsTerm
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IdentificationCompatPassesToLocalCongruenceStatement

noncomputable section

open NumberField Formalism.BasicNotions Formalism.MainNotions.S Formalism.MainNotions.S.Lat Formalism.MainNotions.S.LocalSplitGroups Formalism.L2.SG.TermLoc Formalism.L2.SG.TermDef GlobalTheory.LocOver
open scoped Classical

attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.LocSame

section Gen

variable {K W : Type} [CommRing K] [AddCommGroup W] [Module K W] {n : ℕ}

/- English proof (translation)
Assemble the required witnesses or components as `⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩, fun b => by simp [Matrix.one_apply]⟩`.
-/
theorem tri_refl (f : Fin n → W) : Tri K f f :=
  ⟨1, ⟨fun a b h => Matrix.one_apply_ne (ne_of_lt h).symm, fun a => Matrix.one_apply_eq a⟩,
    fun b => by simp [Matrix.one_apply]⟩

/- English proof (translation)
Take `⟨A, hA, hc⟩` from `h`. Establish `hbt : A.BlockTriangular id` using `fun i j hij => hA.1 i j hij`. Establish `hu : IsUnit A.det`. Rewrite using `[Matrix.det_of_upperTriangular hbt]`. Simplify using `[hA.2]`.

Take `⟨i1, i2⟩` from `inv_unitri A hA.1 hA.2`. Use `⟨A⁻¹, ⟨i1, i2⟩, fun b => ?_⟩` and prove the remaining obligations. Establish `hm` using `Matrix.mul_nonsing_inv A hu`. Establish `key : ∀ c, (∑ a, A⁻¹ a b * A c a) = (1 : Matrix (Fin n) (Fin n) K) c b`. Introduce `c`.

Rewrite using `[← hm, Matrix.mul_apply]`. Conclude with `Finset.sum_congr rfl fun a _ => mul_comm _ _`. Combine the equalities or inequalities in the displayed calculation. Establish `e : ∀ a, A⁻¹ a b • g a = ∑ c, (A⁻¹ a b * A c a) • f c` using `fun a => by`. Rewrite using `[hc a, Finset.smul_sum]`.

Simplify using `only [smul_smul]`. Rewrite using `[Finset.sum_congr rfl fun a _ => e a, Finset.sum_comm]`. Simplify using `only [Finset.sum_smul]`.
-/
theorem tri_symm {f g : Fin n → W} (h : Tri K f g) : Tri K g f := by
  obtain ⟨A, hA, hc⟩ := h
  have hbt : A.BlockTriangular id := fun i j hij => hA.1 i j hij
  have hu : IsUnit A.det := by
    rw [Matrix.det_of_upperTriangular hbt]; simp [hA.2]
  obtain ⟨i1, i2⟩ := inv_unitri A hA.1 hA.2
  refine ⟨A⁻¹, ⟨i1, i2⟩, fun b => ?_⟩
  have hm := Matrix.mul_nonsing_inv A hu
  have key : ∀ c, (∑ a, A⁻¹ a b * A c a) = (1 : Matrix (Fin n) (Fin n) K) c b := by
    intro c; rw [← hm, Matrix.mul_apply]; exact Finset.sum_congr rfl fun a _ => mul_comm _ _
  calc f b = ∑ c, (1 : Matrix (Fin n) (Fin n) K) c b • f c := by simp [Matrix.one_apply]
    _ = ∑ c, (∑ a, A⁻¹ a b * A c a) • f c := by simp_rw [key]
    _ = ∑ a, A⁻¹ a b • g a := by
        have e : ∀ a, A⁻¹ a b • g a = ∑ c, (A⁻¹ a b * A c a) • f c := fun a => by
          rw [hc a, Finset.smul_sum]; simp only [smul_smul]
        rw [Finset.sum_congr rfl fun a _ => e a, Finset.sum_comm]
        simp only [Finset.sum_smul]

/- English proof (translation)
Take `⟨A, hA, hc⟩` from `h1`. Take `⟨B, hB, hd⟩` from `h2`. Use `⟨A * B, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations.

Break down `lt_or_ge c a with hca | hca` into its components or cases. Rewrite using `[hA.1 a c hca, zero_mul]`. Rewrite using `[hB.1 c b (lt_of_lt_of_le hab hca), mul_zero]`. Rewrite using `[Matrix.mul_apply, Finset.sum_eq_single a]`. Rewrite using `[hA.2, hB.2, one_mul]`.

Introduce `c _ hc`. Break down `lt_or_gt_of_ne hc with hc | hc` into its components or cases. Rewrite using `[hA.1 a c hc, zero_mul]`. Rewrite using `[hB.1 c a hc, mul_zero]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ a) h`. Rewrite using `[hd b]`. Establish `e1 : ∀ c, B c b • g c = ∑ a, (A a c * B c b) • f a`. Introduce `c`. Rewrite using `[hc c, Finset.smul_sum]`.

Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[smul_smul, mul_comm]`. Rewrite using `[Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_smul]`.
-/
theorem tri_trans {f g h : Fin n → W} (h1 : Tri K f g) (h2 : Tri K g h) : Tri K f h := by
  obtain ⟨A, hA, hc⟩ := h1
  obtain ⟨B, hB, hd⟩ := h2
  refine ⟨A * B, ⟨fun a b hab => ?_, fun a => ?_⟩, fun b => ?_⟩
  · rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun c _ => ?_
    rcases lt_or_ge c a with hca | hca
    · rw [hA.1 a c hca, zero_mul]
    · rw [hB.1 c b (lt_of_lt_of_le hab hca), mul_zero]
  · rw [Matrix.mul_apply, Finset.sum_eq_single a]
    · rw [hA.2, hB.2, one_mul]
    · intro c _ hc
      rcases lt_or_gt_of_ne hc with hc | hc
      · rw [hA.1 a c hc, zero_mul]
      · rw [hB.1 c a hc, mul_zero]
    · intro h; exact absurd (Finset.mem_univ a) h
  · rw [hd b]
    have e1 : ∀ c, B c b • g c = ∑ a, (A a c * B c b) • f a := by
      intro c; rw [hc c, Finset.smul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [smul_smul, mul_comm]
    rw [Finset.sum_congr rfl fun c _ => e1 c, Finset.sum_comm]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Matrix.mul_apply, Finset.sum_smul]

/- English proof (translation)
Take `⟨A, hA, hc⟩` from `h`. Conclude with `⟨A, hA, fun b => by simp only [hc b, map_sum, map_smul]⟩`.
-/
theorem tri_map {f g : Fin n → W} (h : Tri K f g) (φ : W ≃ₗ[K] W) :
    Tri K (fun a => φ (f a)) (fun a => φ (g a)) := by
  obtain ⟨A, hA, hc⟩ := h
  exact ⟨A, hA, fun b => by simp only [hc b, map_sum, map_smul]⟩

/- English proof (translation)
Take `⟨A, hA, hc⟩` from `h`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨b, hb, rfl⟩`. Rewrite using `[hc b]`. Use `Submodule.sum_mem _ fun a _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hab : b < a`. Rewrite using `[hA.1 a b hab, zero_smul]`. Conclude with `Submodule.zero_mem _`. Establish `hab' : a.val ≤ b.val` using `Fin.le_iff_val_le_val.1 (not_lt.1 hab)`. Establish `hb' : b.val < j` using `hb`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, lt_of_le_of_lt hab' hb', rfl⟩)`.
-/
theorem span_le_of_tri {f g : Fin n → W} (h : Tri K f g) (j : ℕ) :
    Submodule.span K (g '' {c | c.val < j}) ≤ Submodule.span K (f '' {c | c.val < j}) := by
  obtain ⟨A, hA, hc⟩ := h
  rw [Submodule.span_le]
  rintro _ ⟨b, hb, rfl⟩
  rw [hc b]
  refine Submodule.sum_mem _ fun a _ => ?_
  by_cases hab : b < a
  · rw [hA.1 a b hab, zero_smul]; exact Submodule.zero_mem _
  · have hab' : a.val ≤ b.val := Fin.le_iff_val_le_val.1 (not_lt.1 hab)
    have hb' : b.val < j := hb
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, lt_of_le_of_lt hab' hb', rfl⟩)

/- English proof (translation)
The claim follows from `le_antisymm (span_le_of_tri (tri_symm h) j) (span_le_of_tri h j)`.
-/
theorem span_eq_of_tri {f g : Fin n → W} (h : Tri K f g) (j : ℕ) :
    Submodule.span K (f '' {c | c.val < j}) = Submodule.span K (g '' {c | c.val < j}) :=
  le_antisymm (span_le_of_tri (tri_symm h) j) (span_le_of_tri h j)

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨b, hb, rfl⟩`. Conclude with `⟨b.castSucc, by simpa using hb, rfl⟩`. Introduce and unpack `⟨c, hc, rfl⟩`.

Establish `hc' : c.val < j` using `hc`. Conclude with `⟨⟨c.val, by omega⟩, hc', congrArg f (Fin.ext rfl)⟩`.
-/
theorem img_cs {r : ℕ} (f : Fin (r + 1) → W) (j : ℕ) (hj : j ≤ r) :
    (fun b : Fin r => f b.castSucc) '' {b | b.val < j} = f '' {c | c.val < j} := by
  ext x
  constructor
  · rintro ⟨b, hb, rfl⟩
    exact ⟨b.castSucc, by simpa using hb, rfl⟩
  · rintro ⟨c, hc, rfl⟩
    have hc' : c.val < j := hc
    exact ⟨⟨c.val, by omega⟩, hc', congrArg f (Fin.ext rfl)⟩

end Gen

section Loc

open Formalism.MainNotions.S.Loc Formalism.MainNotions.S.LocNG

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
  {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] [MeasurableSpace E]
  {M : Model F E} {V : Type} [AddCommGroup V] [Module E V] {r : ℕ}

/- English proof (translation)
Unfold `HermSp.X`. Rewrite using `[← img_cs f r le_rfl]`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem X_eq_span (H : HermSp M V) (f : Fin (r + 1) → V) :
    H.X f = Submodule.span E (f '' {c | c.val < r}) := by
  unfold HermSp.X
  rw [← img_cs f r le_rfl]
  congr 1
  ext x
  simp

/- English proof (translation)
Rewrite using `[X_eq_span, X_eq_span, span_eq_of_tri h]`.
-/
theorem X_eq_of_tri (H : HermSp M V) {f g : Fin (r + 1) → V} (h : Tri E f g) : H.X f = H.X g := by
  rw [X_eq_span, X_eq_span, span_eq_of_tri h]

/- English proof (translation)
Take `⟨hU, h1, h2⟩` from `hu`. Establish `hX` using `X_eq_of_tri H h`. Use `⟨hU, fun a => ?_, fun v hv => ?_⟩` and prove the remaining obligations. Establish `hsp : Submodule.span E ((fun b : Fin r => g b.castSucc) '' {b | b < a}) = Submodule.span E (f '' {c | c.val < a.val})`. Rewrite using `[show {b : Fin r | b < a} = {b | b.val < a.val} from rfl, img_cs g a.val a.isLt.le, span_eq_of_tri h]`.

Rewrite using `[hsp]`. Take `⟨A, hA, hc⟩` from `h`. Rewrite using `[hc a.castSucc, map_sum]`. Establish `e : ∑ c, u (A c a.castSucc • f c) - ∑ c, A c a.castSucc • f c = ∑ c, A c a.castSucc • (u (f c) - f c)`. Rewrite using `[← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Rewrite using `[map_smul, smul_sub]`. Rewrite using `[e]`. Use `Submodule.sum_mem _ fun c _ => ?_` and prove the remaining obligations. Distinguish the cases in `hca : a.castSucc < c`.

Rewrite using `[hA.1 c a.castSucc hca, zero_smul]`. Conclude with `Submodule.zero_mem _`. Use `Submodule.smul_mem _ _ ?_` and prove the remaining obligations. Establish `hcv : c.val ≤ a.val`. Establish `h'` using `Fin.le_iff_val_le_val.1 (not_lt.1 hca)`.

Rewrite `h'` using `[Fin.coe_castSucc]`. Then use the resulting hypothesis. Establish `hcr : c.val < r` using `lt_of_le_of_lt hcv a.isLt`. Establish `hfc` using `h1 ⟨c.val, hcr⟩`. Establish `ecs : (⟨c.val, hcr⟩ : Fin r).castSucc = c` using `Fin.ext rfl`. Rewrite `hfc` using `[ecs, show {b : Fin r | b < ⟨c.val, hcr⟩} = {b | b.val < c.val} from rfl, img_cs f c.val hcr.le]`.

Use `Submodule.span_mono (Set.image_mono fun x hx => ?_) hfc` and prove the remaining obligations. Establish `hx' : x.val < c.val` using `hx`. Use `show x.val < a.val`. Use linear arithmetic over natural numbers and integers. Rewrite `hv`, the goal using `[← hX]`.

Conclude with `h2 v hv`.
-/
theorem NU_of_tri (H : HermSp M V) {f g : Fin (r + 1) → V} (h : Tri E f g) {u : V ≃ₗ[E] V}
    (hu : u ∈ NU H f) : u ∈ NU H g := by
  obtain ⟨hU, h1, h2⟩ := hu
  have hX := X_eq_of_tri H h
  refine ⟨hU, fun a => ?_, fun v hv => ?_⟩
  · have hsp : Submodule.span E ((fun b : Fin r => g b.castSucc) '' {b | b < a}) =
        Submodule.span E (f '' {c | c.val < a.val}) := by
      rw [show {b : Fin r | b < a} = {b | b.val < a.val} from rfl, img_cs g a.val a.isLt.le,
        span_eq_of_tri h]
    rw [hsp]
    obtain ⟨A, hA, hc⟩ := h
    rw [hc a.castSucc, map_sum]
    have e : ∑ c, u (A c a.castSucc • f c) - ∑ c, A c a.castSucc • f c =
        ∑ c, A c a.castSucc • (u (f c) - f c) := by
      rw [← Finset.sum_sub_distrib]
      refine Finset.sum_congr rfl fun c _ => ?_
      rw [map_smul, smul_sub]
    rw [e]
    refine Submodule.sum_mem _ fun c _ => ?_
    by_cases hca : a.castSucc < c
    · rw [hA.1 c a.castSucc hca, zero_smul]; exact Submodule.zero_mem _
    · refine Submodule.smul_mem _ _ ?_
      have hcv : c.val ≤ a.val := by
        have h' := Fin.le_iff_val_le_val.1 (not_lt.1 hca)
        rwa [Fin.coe_castSucc] at h'
      have hcr : c.val < r := lt_of_le_of_lt hcv a.isLt
      have hfc := h1 ⟨c.val, hcr⟩
      have ecs : (⟨c.val, hcr⟩ : Fin r).castSucc = c := Fin.ext rfl
      rw [ecs, show {b : Fin r | b < ⟨c.val, hcr⟩} = {b | b.val < c.val} from rfl,
        img_cs f c.val hcr.le] at hfc
      refine Submodule.span_mono (Set.image_mono fun x hx => ?_) hfc
      have hx' : x.val < c.val := hx
      show x.val < a.val
      omega
  · rw [← hX] at hv ⊢
    exact h2 v hv

/- English proof (translation)
Unfold `Cong`. Rewrite using `[hX]`.
-/
theorem cong_congr (H : HermSp M V) (Λ : Submodule M.L.O V) (f : Fin (r + 1) → V)
    {f₁ f₂ : Fin (r + 1) → V} (hX : H.X f₁ = H.X f₂) (x : V) :
    Cong H Λ f f₁ x ↔ Cong H Λ f f₂ x := by
  unfold Cong
  rw [hX]

end Loc

/- English proof (translation)
Introduce `D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ hG n hn m hm hgm hfr hio p P hP d hd`. Establish `hOK : (Z.M p).OK` using `(Z.agree p).1`. Establish `hfr' : ∀ a, frame F₂ a = n (m (frame F₁ a))` using `fun a => by`. Establish `h` using `hfr a`. Simplify using `only [LinearEquiv.mul_apply] at h`.

Conclude with `h`. Establish `hG₂ : Gval (lf D F0) F₂ ≠ 0`. Establish `hrel : DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D F0) F₁ (⟨F₂.fl, n (m F₁.zt)⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E))` using `⟨n, ⟨⟨hn.1, (Formalism.L2.SG.Pf.gmap_eq_iff n).2 fun x => by simp⟩, hn.2⟩, m, ⟨⟨hm.1, (Formalism.L2.SG.Pf.gmap_eq_iff m).2 fun x => by simp⟩, hm.2⟩, hfr', rfl⟩`. Establish `e` using `Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel`. Conclude with `fun h0 => hG (e.symm.trans h0)`.

Take `⟨hT₁, htri₁⟩` from `GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₁ hP₁ hG p`. Take `⟨hT₂, htri₂⟩` from `GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₂ hP₂ hG₂ p`. Establish `hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `hn.1`. Establish `hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `hm.1`. Establish `hnmI : n * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT` using `mul_mem hnI hmI`.

Apply the tactic sequence `obtain ⟨gn, hgnE, -, -, -, hgnN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p n hnI`. Apply the tactic sequence `obtain ⟨gm, hgmE, -, -, -, hgmN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p m hmI`. Apply the tactic sequence `obtain ⟨g, -, -, hguniq, hgimg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p (n * m) hnmI`. Establish `hext : Ext p (n * m) (gn * gm)` using `fun x => by show (gn * gm) (baseChange₂ D p x) = baseChange₂ D p ((n * m) x)`. Rewrite using `[LinearEquiv.mul_apply, hgmE x, hgnE (m x), LinearEquiv.mul_apply]`.

Establish `hgeq : gn * gm = g` using `hguniq _ hext`. Establish `hn' : gn ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f` using `hgnN (lf D F0) hn`. Establish `hm' : gm ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f'` using `NU_of_tri (locH Z p) htri₁ (hgmN F₁ hm)`. Establish `himg : Formalism.MainNotions.S.LocNG.img (gn * gm) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂ = (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂` using `by show Formalism.MainNotions.S.LocNG.img (gn * gm) (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ`. Rewrite using `[hgeq, hgimg Λ, hgm]`.

Establish `hsc : scaled Z p (frame F₂) = fun a => (gn * gm) (scaled Z p (frame F₁) a)`. Use function extensionality and compare the values at `a`. Use `show frFac Z.δ p a • baseChange₂ D p (frame F₂ a) = (gn * gm) (frFac Z.δ p a • baseChange₂ D p (frame F₁ a))`. Rewrite using `[LinearEquiv.map_smul, hext, hfr a]`. Establish `htri : Tri (D.s.atP p).Ep (fun b => (gn * gm) ((locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f' b)) (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')).f'`.

Establish `h2` using `tri_symm (tri_map htri₁ (gn * gm))`. Rewrite `h2` using `[← hsc]`. Conclude with `tri_trans h2 htri₂`. Establish `hX₁` using `X_eq_of_tri (locH Z p) htri₁`. Establish `hX₂` using `X_eq_of_tri (locH Z p) htri₂`.

Establish `hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1`. Rewrite using `[finrank_Vp]`. Take `⟨j, hj⟩` from `D.R.m_even`. Use `D.R.two_le_m` as an intermediate fact. Unfold `Ranks.r Ranks.rS`.

Use linear arithmetic over natural numbers and integers. Use `GlobalTheory.T.localTerms_same_doubleCoset_same_datum (Z.M p) hOK (locH Z p) D.R.rS D.R.k P hfin hP (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) hT₁ hT₂` and prove the remaining obligations. Use `rfl rfl rfl gn hn' gm hm' himg (tri_refl _) htri ?_ d hd`. Introduce `hs x' hx' x hx hx'p hxp`. Establish `key` using `GlobalTheory.T.identificationCompat_passes_to_local_congruence D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ (n * m) hnmI hgm hfr hio p (gn * gm) hext hs x' hx' x hx (by rw [hX₁]; exact hx'p) hxp`.

Rewrite using `[cong_congr (locH Z p) _ _ hX₁.symm, cong_congr (locH Z p) _ _ hX₂.symm]`. Conclude with `key`.
-/
theorem over_same : ∀ (D : D7) (Z : LocDat D), ∀ (u u' : D.what₂.Word) (F0 : FlagG (VS D) D.R.rS ((Tu D u : ℕ) : D.host.E)) (Λ : Submodule (𝓞 D.host.E) (VS D).V), IsRowLat D F0 Λ → ∀ F₁ F₂ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E), PD D Λ (lf D F0) u' F₁ → PD D Λ (lf D F0) u' F₂ → Gval (lf D F0) F₁ ≠ 0 → ∀ n ∈ Formalism.L2.SG.NGData.NRat (lf D F0), ∀ m ∈ Formalism.L2.SG.NGData.NRat F₁, Formalism.HermitianLatticesTheory.gmap (n * m) Λ = Λ → (∀ a, frame F₂ a = (n * m) (frame F₁ a)) → IotaCompat Λ (lf D F0) F₁ F₂ (n * m) (gS D) → ∀ (p : PlF D) (P : LocNG.FPair (locH Z p) D.R.rS), P.RelG (LocNG.theta (Z.M p)) → ∀ d, Over P d (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) → Over P d (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) := by
  intro D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ hG n hn m hm hgm hfr hio p P hP d hd
  have hOK : (Z.M p).OK := (Z.agree p).1
  have hfr' : ∀ a, frame F₂ a = n (m (frame F₁ a)) := fun a => by
    have h := hfr a
    simp only [LinearEquiv.mul_apply] at h
    exact h
  have hG₂ : Gval (lf D F0) F₂ ≠ 0 := by
    have hrel : DCRel (⊤ : Submodule (𝓞 D.host.E) (VS D).V) (lf D F0) F₁
        (⟨F₂.fl, n (m F₁.zt)⟩ : LFlag (VS D) D.R.rS ((Tu D u' : ℕ) : D.host.E)) :=
      ⟨n, ⟨⟨hn.1, (Formalism.L2.SG.Pf.gmap_eq_iff n).2 fun x => by simp⟩, hn.2⟩,
        m, ⟨⟨hm.1, (Formalism.L2.SG.Pf.gmap_eq_iff m).2 fun x => by simp⟩, hm.2⟩, hfr', rfl⟩
    have e := Formalism.L2.SG.Pf.gval_rel (lf D F0) hrel
    exact fun h0 => hG (e.symm.trans h0)
  obtain ⟨hT₁, htri₁⟩ := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₁ hP₁ hG p
  obtain ⟨hT₂, htri₂⟩ := GlobalTheory.LocOver.locU_isTerm D Z u u' F0 Λ hΛ F₂ hP₂ hG₂ p
  have hnI : n ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hn.1
  have hmI : m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := hm.1
  have hnmI : n * m ∈ Formalism.HermitianLatticesTheory.isom (VS D).hT := mul_mem hnI hmI
  obtain ⟨gn, hgnE, -, -, -, hgnN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p n hnI
  obtain ⟨gm, hgmE, -, -, -, hgmN⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p m hmI
  obtain ⟨g, -, -, hguniq, hgimg, -⟩ := GlobalTheory.T.rational_isometry_extends_local_isometry D Z p (n * m) hnmI
  have hext : Ext p (n * m) (gn * gm) := fun x => by
    show (gn * gm) (baseChange₂ D p x) = baseChange₂ D p ((n * m) x)
    rw [LinearEquiv.mul_apply, hgmE x, hgnE (m x), LinearEquiv.mul_apply]
  have hgeq : gn * gm = g := hguniq _ hext
  have hn' : gn ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f := hgnN (lf D F0) hn
  have hm' : gm ∈ NU (locH Z p) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f' :=
    NU_of_tri (locH Z p) htri₁ (hgmN F₁ hm)
  have himg : Formalism.MainNotions.S.LocNG.img (gn * gm) (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂ =
      (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).abelian₂ := by
    show Formalism.MainNotions.S.LocNG.img (gn * gm) (lattice₂ D Z.M p Λ) = lattice₂ D Z.M p Λ
    rw [hgeq, hgimg Λ, hgm]
  have hsc : scaled Z p (frame F₂) = fun a => (gn * gm) (scaled Z p (frame F₁) a) := by
    funext a
    show frFac Z.δ p a • baseChange₂ D p (frame F₂ a) = (gn * gm) (frFac Z.δ p a • baseChange₂ D p (frame F₁ a))
    rw [LinearEquiv.map_smul, hext, hfr a]
  have htri : Tri (D.s.atP p).Ep (fun b => (gn * gm) ((locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')).f' b))
      (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')).f' := by
    have h2 := tri_symm (tri_map htri₁ (gn * gm))
    rw [← hsc] at h2
    exact tri_trans h2 htri₂
  have hX₁ := X_eq_of_tri (locH Z p) htri₁
  have hX₂ := X_eq_of_tri (locH Z p) htri₂
  have hfin : Module.finrank (D.s.atP p).Ep (Vp D p) = D.R.k + 2 * D.R.rS + 1 := by
    rw [finrank_Vp]
    obtain ⟨j, hj⟩ := D.R.m_even
    have := D.R.two_le_m
    unfold Ranks.r Ranks.rS
    omega
  refine GlobalTheory.T.localTerms_same_doubleCoset_same_datum (Z.M p) hOK (locH Z p) D.R.rS D.R.k P hfin hP
    (locU Z p Λ (lf D F0) F₁ (Tu D u) (Tu D u')) (locU Z p Λ (lf D F0) F₂ (Tu D u) (Tu D u')) hT₁ hT₂
    rfl rfl rfl gn hn' gm hm' himg (tri_refl _) htri ?_ d hd
  intro hs x' hx' x hx hx'p hxp
  have key := GlobalTheory.T.identificationCompat_passes_to_local_congruence D Z u u' F0 Λ hΛ F₁ F₂ hP₁ hP₂ (n * m) hnmI hgm hfr hio p (gn * gm) hext hs
    x' hx' x hx (by rw [hX₁]; exact hx'p) hxp
  rw [cong_congr (locH Z p) _ _ hX₁.symm, cong_congr (locH Z p) _ _ hX₂.symm]
  exact key

end GlobalTheory.LocSame
