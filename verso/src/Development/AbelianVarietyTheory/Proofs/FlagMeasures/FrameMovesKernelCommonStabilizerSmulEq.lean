import Mathlib
import Formalism.SharpRestriction.CuspSpanNormBounds.FractionFieldToGenericStalkAlgebraMapEq
import Development.AbelianVarietyTheory.Definitions.Foundations.IsHermND
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ComplementReferenceCompactSubgroup
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.Cint
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NoLeak
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IndexMeasureIntegralTransportAndChangeStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermitianFramesStabilizerActsOnTermsStatement

noncomputable section
open ValuativeRel Formalism.MainNotions.S.Loc GlobalTheory.HL GlobalTheory.IdxInt MeasureTheory
open scoped Pointwise ENNReal Classical

namespace GlobalTheory.HL.KernInv

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F]
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E]
variable {L : LocE F E} {r k : ℕ} (S : Frames L r k)

def mvEquiv (h : S.GLV) : S.MW ≃+ S.MW :=
  (h.toAddEquiv.prodCongr h.toAddEquiv).prodCongr (h.toAddEquiv.prodCongr (AddEquiv.refl E))

end GlobalTheory.HL.KernInv

namespace GlobalTheory.HL

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.HL.Frames.St at hh`. Establish `hN` using `(Subgroup.mem_inf.mp hh).1`. Unfold `_root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN`. Establish `hI` using `(Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1`. Unfold `_root_.GlobalTheory.HL.isomG at hI`.

Unfold `_root_.GlobalTheory.HL.Frames.h`. Conclude with `hI x y`.
-/
private lemma form_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (x y : S.V) :
    S.h (h x) (h y) = S.h x y := by
  unfold _root_.GlobalTheory.HL.Frames.St at hh
  have hN := (Subgroup.mem_inf.mp hh).1
  unfold _root_.GlobalTheory.HL.Frames.N _root_.GlobalTheory.HL.Frames.Nof at hN
  have hI := (Subgroup.mem_inf.mp (Subgroup.mem_inf.mp hN).1).1
  unfold _root_.GlobalTheory.HL.isomG at hI
  unfold _root_.GlobalTheory.HL.Frames.h
  exact hI x y

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Use extensionality with `w`. Prove the components needed by the constructor for the conclusion. Introduce `hw`. Conclude with `⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩`. Introduce and unpack `⟨w, hw, rfl⟩`.

Conclude with `(hAB w).mpr hw`.
-/
private lemma addSubgroup_eq_map_of_apply_mem_iff {M : Type} [AddCommGroup M] (e : M ≃+ M)
    (A B : AddSubgroup M) (hAB : ∀ w, e w ∈ B ↔ w ∈ A) : B = A.map e.toAddMonoidHom := by
  ext w
  constructor
  · intro hw
    exact ⟨e.symm w, (hAB _).mp (by simpa using hw), by simp⟩
  · rintro ⟨w, hw, rfl⟩
    exact (hAB w).mpr hw

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.HL.Frames.refB`. Simplify using `only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map, Submodule.mem_toAddSubgroup, and_assoc]`. Conclude with `Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))`.
-/
private lemma mem_refB_iff (J : ℕ) (Λ : Submodule L.O S.V) (a b : S.V) :
    (a, b) ∈ S.refB J Λ ↔ a ∈ S.spanTo S.f J ∧ b ∈ S.spanTo S.f' J ∧
      ∃ y ∈ Λ, a + b = (algebraMap F E) S.th • y := by
  unfold _root_.GlobalTheory.HL.Frames.refB
  simp only [AddSubgroup.mem_inf, AddSubgroup.mem_prod, AddSubgroup.mem_comap, AddSubgroup.mem_map,
    Submodule.mem_toAddSubgroup, and_assoc]
  exact Iff.rfl.and (Iff.rfl.and (exists_congr fun _ => Iff.rfl.and eq_comm))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Simplify using `only [Submodule.mem_sup]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, z, hz, hyz⟩`. Use `⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩` and prove the remaining obligations. Rewrite using `[← map_add, hyz, LinearEquiv.symm_apply_apply]`.

Introduce and unpack `⟨y, hy, z, hz, rfl⟩`. Conclude with `⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩`.
-/
private lemma apply_mem_sup_iff_of_apply_mem_iff (h : S.GLV) (A B : Submodule E S.V)
    (hA : ∀ v, h v ∈ A ↔ v ∈ A) (hB : ∀ v, h v ∈ B ↔ v ∈ B) (v : S.V) :
    h v ∈ A ⊔ B ↔ v ∈ A ⊔ B := by
  simp only [Submodule.mem_sup]
  constructor
  · rintro ⟨y, hy, z, hz, hyz⟩
    refine ⟨h.symm y, (hA _).mp (by simpa using hy), h.symm z, (hB _).mp (by simpa using hz), ?_⟩
    rw [← map_add, hyz, LinearEquiv.symm_apply_apply]
  · rintro ⟨y, hy, z, hz, rfl⟩
    exact ⟨h y, (hA y).mpr hy, h z, (hB z).mpr hz, (map_add h y z).symm⟩

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Establish `hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) = _root_.GlobalTheory.HL.hf L S.Hm x y` using `form_apply_apply_of_mem_St S hh`. Establish `hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J`. Unfold `_root_.GlobalTheory.HL.Frames.Ysp`. Conclude with `apply_mem_sup_iff_of_apply_mem_iff S h _ _ (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J) (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)`. Unfold `_root_.GlobalTheory.HL.perp`.

Use `show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)`. Prove the components needed by the constructor for the conclusion. Introduce `H y hy`. Rewrite using `[← hform]`. Conclude with `H _ ((hY y).mpr hy)`.

Introduce `H y hy`. Establish `hyy : h (h.symm y) = y` using `h.apply_symm_apply y`. Rewrite using `[← hyy, hform]`. Conclude with `H _ ((hY _).mp (hyy.symm ▸ hy))`.
-/
private lemma apply_mem_perp_Ysp_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (J : ℕ) (u : S.V) :
    h u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) ↔
      u ∈ _root_.GlobalTheory.HL.perp L S.Hm (S.Ysp J) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  have hY : ∀ v, h v ∈ S.Ysp J ↔ v ∈ S.Ysp J := by
    unfold _root_.GlobalTheory.HL.Frames.Ysp
    exact apply_mem_sup_iff_of_apply_mem_iff S h _ _
      (_root_.GlobalTheory.FrameAct.spanTo_iff S h hh J)
      (_root_.GlobalTheory.FrameAct.spanTo_iff' S h hh J)
  unfold _root_.GlobalTheory.HL.perp
  show (∀ y ∈ S.Ysp J, _ = 0) ↔ (∀ y ∈ S.Ysp J, _ = 0)
  constructor
  · intro H y hy
    rw [← hform]
    exact H _ ((hY y).mpr hy)
  · intro H y hy
    have hyy : h (h.symm y) = y := h.apply_symm_apply y
    rw [← hyy, hform]
    exact H _ ((hY _).mp (hyy.symm ▸ hy))

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Simplify using `only [Set.ext_iff, SetLike.mem_coe]`. Rewrite using `[h.surjective.forall]`. Simplify using `only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]`.
-/
private lemma coe_smul_submodule_eq_iff_of_apply_mem_iff (h : S.GLV) (Λ₁ : Submodule L.O S.V) (P Q : Set S.V)
    (hPQ : ∀ v, h v ∈ Q ↔ v ∈ P) :
    ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = Q ↔ (Λ₁ : Set S.V) = P := by
  simp only [Set.ext_iff, SetLike.mem_coe]
  rw [h.surjective.forall]
  simp only [_root_.GlobalTheory.FrameAct.mem_smul_iff, hPQ]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Establish `hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) = _root_.GlobalTheory.HL.hf L S.Hm x y` using `form_apply_apply_of_mem_St S hh`. Unfold `_root_.GlobalTheory.HL.eich`. Rewrite using `[hform, hform]`. Simplify using `only [map_add, map_sub, map_smul]`.
-/
private lemma eich_apply_apply_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (a b v : S.V) (c : E) :
    _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) = h (_root_.GlobalTheory.HL.eich L S.Hm a b c v) := by
  have hform : ∀ x y, _root_.GlobalTheory.HL.hf L S.Hm (h x) (h y) =
      _root_.GlobalTheory.HL.hf L S.Hm x y := form_apply_apply_of_mem_St S hh
  unfold _root_.GlobalTheory.HL.eich
  rw [hform, hform]
  simp only [map_add, map_sub, map_smul]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in
/- English proof (translation)
Unfold `_root_.GlobalTheory.HL.Frames.moved`. Use `show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔ _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ`. Rewrite using `[eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]`.
-/
private lemma apply_mem_moved_smul_iff_of_mem_St {h : S.GLV}
    (hh : h ∈ S.St) (Λ : Submodule L.O S.V) (a b v : S.V) (c : E) :
    h v ∈ S.moved (h • Λ) (h a) (h b) c ↔ v ∈ S.moved Λ a b c := by
  unfold _root_.GlobalTheory.HL.Frames.moved
  show _root_.GlobalTheory.HL.eich L S.Hm (h a) (h b) c (h v) ∈ h • Λ ↔
    _root_.GlobalTheory.HL.eich L S.Hm a b c v ∈ Λ
  rw [eich_apply_apply_of_mem_St S hh, _root_.GlobalTheory.FrameAct.mem_smul_iff]

open ValuativeRel MeasureTheory in
open scoped Pointwise ENNReal Classical in
variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] in
variable {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] in
variable {L : _root_.Formalism.MainNotions.S.Loc.LocE F E} {r k : ℕ} (S : _root_.GlobalTheory.HL.Frames L r k) in

/- English proof (translation)
Introduce `F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh`. Establish `hform` using `form_apply_apply_of_mem_St S hh`. Establish `hmove` using `(_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2`. Establish `hA : S.refA J (h • Λ) = (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom`. Use `addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_` and prove the remaining obligations.

Introduce and unpack `⟨⟨a, b⟩, u, t⟩`. Unfold `_root_.GlobalTheory.HL.Frames.refA`. Simplify using `only [AddSubgroup.mem_prod]`. Express the relevant statement in the definitionally equal form `(h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔ (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT`. Rewrite using `[mem_refB_iff, mem_refB_iff, ← map_add, _root_.GlobalTheory.FrameAct.spanTo_iff S h hh, _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]`.

Establish `hth` using `_root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)`. Unfold `_root_.GlobalTheory.HL.Frames.InTh at hth`. Rewrite using `[hth]`. Unfold `_root_.GlobalTheory.HL.Frames.refU`. Simplify using `only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]`.

Establish `hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁)) (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w`. Introduce and unpack `⟨⟨a, b⟩, u, t⟩`. Establish `hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t))`. Unfold `_root_.GlobalTheory.HL.Frames.sOf`. Simplify using `only [hform]`.

Establish `hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔ S.MvTo J d Λ Λ₁ ((a, b), (u, t))`. Unfold `_root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv`. Express the relevant statement in the definitionally equal form `S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧ ((h • Λ₁ : Submodule L.O S.V) : Set S.V) = S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔ S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧ (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))`. Rewrite using `[hs]`. Conclude with `and_congr (hmove J a b u _).symm (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)`.

Unfold `_root_.GlobalTheory.IdxInt.ind`. Conclude with `if_congr hiff rfl rfl`. Unfold `_root_.GlobalTheory.HL.Frames.kern`. Rewrite using `[hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]`. Simplify using `only [hP]`.
-/
theorem _root_.GlobalTheory.HL.kern_smul_eq : ∀ {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F] [CharZero F] {E : Type} [CommRing E] [Algebra F E] [TopologicalSpace E] (L : _root_.Formalism.MainNotions.S.Loc.LocE F E), ∀ (r k : ℕ) (S : _root_.GlobalTheory.HL.Frames L r k), ∀ (d : S.Datum) (Λ : Submodule L.O S.V), S.IsTerm d Λ → ∀ (β J βJ : ℕ) (Λ₁ : Submodule L.O S.V), ∀ h ∈ S.St, S.kern β J βJ d (h • Λ) (h • Λ₁) = S.kern β J βJ d Λ Λ₁ := by
  intro F _ _ _ _ _ E _ _ _ L r k S d Λ hT β J βJ Λ₁ h hh
  have hform := form_apply_apply_of_mem_St S hh
  have hmove := (_root_.GlobalTheory.FrameAct.stabiliser_acts_on_terms L r k S d Λ hT h hh).2.2.2.2.2.2.2.2.2.2
  have hA : S.refA J (h • Λ) =
      (S.refA J Λ).map (_root_.GlobalTheory.HL.KernInv.mvEquiv S h).toAddMonoidHom := by
    refine addSubgroup_eq_map_of_apply_mem_iff _ _ _ ?_
    rintro ⟨⟨a, b⟩, u, t⟩
    unfold _root_.GlobalTheory.HL.Frames.refA
    simp only [AddSubgroup.mem_prod]
    change (h a, h b) ∈ S.refB J (h • Λ) ∧ h u ∈ S.refU J (h • Λ) ∧ t ∈ S.refT ↔
      (a, b) ∈ S.refB J Λ ∧ u ∈ S.refU J Λ ∧ t ∈ S.refT
    rw [mem_refB_iff, mem_refB_iff, ← map_add,
      _root_.GlobalTheory.FrameAct.spanTo_iff S h hh,
      _root_.GlobalTheory.FrameAct.spanTo_iff' S h hh]
    have hth := _root_.GlobalTheory.FrameAct.inTh_iff S h Λ (a + b)
    unfold _root_.GlobalTheory.HL.Frames.InTh at hth
    rw [hth]
    unfold _root_.GlobalTheory.HL.Frames.refU
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup,
      _root_.GlobalTheory.FrameAct.mem_smul_iff, apply_mem_perp_Ysp_iff_of_mem_St S hh]
  have hP : ∀ w, _root_.GlobalTheory.IdxInt.ind (S.MvTo J d (h • Λ) (h • Λ₁))
      (_root_.GlobalTheory.HL.KernInv.mvEquiv S h w) = _root_.GlobalTheory.IdxInt.ind (S.MvTo J d Λ Λ₁) w := by
    rintro ⟨⟨a, b⟩, u, t⟩
    have hs : S.sOf ((h a, h b), (h u, t)) = S.sOf ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.sOf
      simp only [hform]
    have hiff : S.MvTo J d (h • Λ) (h • Λ₁) ((h a, h b), (h u, t)) ↔
        S.MvTo J d Λ Λ₁ ((a, b), (u, t)) := by
      unfold _root_.GlobalTheory.HL.Frames.MvTo _root_.GlobalTheory.HL.Frames.Mv
      change S.IsMove J d (h • Λ) (h a) (h b) (h u) (S.sOf ((h a, h b), (h u, t))) ∧
          ((h • Λ₁ : Submodule L.O S.V) : Set S.V) =
            S.moved (h • Λ) (h a) (h u) (S.sOf ((h a, h b), (h u, t))) ↔
        S.IsMove J d Λ a b u (S.sOf ((a, b), (u, t))) ∧
          (Λ₁ : Set S.V) = S.moved Λ a u (S.sOf ((a, b), (u, t)))
      rw [hs]
      exact and_congr (hmove J a b u _).symm
        (coe_smul_submodule_eq_iff_of_apply_mem_iff S h Λ₁ _ _ fun v => apply_mem_moved_smul_iff_of_mem_St S hh Λ a u v _)
    unfold _root_.GlobalTheory.IdxInt.ind
    exact if_congr hiff rfl rfl
  unfold _root_.GlobalTheory.HL.Frames.kern
  rw [hA, (_root_.GlobalTheory.IdxInt.Transport.cint_map_and_change.1 _ _ _).2]
  simp only [hP]

end GlobalTheory.HL
