import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.ImportsBis
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DoubledUnitaryPartnerDiagStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsContOnOfLocal

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta
open IsDedekindDomain NumberField
open scoped TensorProduct GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels Matrix
open GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels (Base Spc Model Chr incM)

attribute [local instance] Formalism.BasicNotions.Host.cmStar
open scoped Classical

/- English proof (translation)
Introduce `F _ _ κ _ L hLo hLc K hK`. Establish `hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k` using `fun k => continuous_id.sub continuous_const`. Establish `hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F, (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L`. Introduce `a b`. Rewrite using `[QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]`.

Establish `hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite`. Take `⟨t, -, hcov⟩` from `hK.elim_nhds_subcover (fun k => {w | w - k ∈ L}) (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))`. Use `(t.finite_toSet.image QuotientAddGroup.mk).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨w, hw, rfl⟩`. Take `⟨k, hk, hwk⟩` from `Set.mem_iUnion₂.mp (hcov hw)`.

Conclude with `⟨k, hk, ((hmk w k).2 hwk).symm⟩`. Choose the witnesses or unpack the hypotheses as in `⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧ ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by`. Use `⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1, Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩` and prove the remaining obligations. Conclude with `⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩`. Introduce and unpack `⟨i, rfl⟩`.

Conclude with `hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2`. Use `choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)`. Use `⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y, fun i => ?_, fun i j => ?_, ?_⟩` and prove the remaining obligations. Use `⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp, fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L}) ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc) ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont …` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[(hmk x' x).2 hx']`. Simplify using `only`. Rewrite using `[if_neg]`. Introduce `h`. Conclude with `hw ((hmk w (y i)).1 (h.trans (hy i).symm))`.

Simplify using `only`. Rewrite using `[hy j]`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg (fun h' => h (he h').symm), if_neg h]`. Introduce `Ψ hΨ hper hsupp choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)`. Use `⟨f, funext fun z => ?_⟩` and prove the remaining obligations. Take `⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w` from `⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,`. Use function extensionality and compare the values at `fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩`.

Simplify using `only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]`. Distinguish the cases in `hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K`. Take `⟨i0, hi0⟩` from `(hS _).1 hw`. Rewrite using `[Finset.sum_eq_single i0]`. Rewrite using `[if_pos hi0.symm, mul_one, hf]`.

Establish `hL : w - y i0 ∈ L` using `(hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)`. Rewrite using `[← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [GlobalTheory.WeilCont.adeleJoin, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, map_zero]`.

Conclude with `Prod.ext (add_zero _).symm (add_sub_cancel _ _).symm`. Introduce `j _ hj`. Rewrite using `[if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ _) h`.

Establish `h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0`. Assume the negation of the conclusion as `h`. Conclude with `hw ⟨w, hsupp _ h, rfl⟩`. Rewrite using `[h0]`. Use `(Finset.sum_eq_zero fun i _ => ?_).symm` and prove the remaining obligations.

Rewrite using `[if_neg, mul_zero]`. Introduce `h`. Conclude with `hw (h ▸ (hS _).2 ⟨i, rfl⟩)`.
-/
theorem GlobalTheory.WeilCont.schA_periodic_finite_cosets : ∀ (F : Type) [Field F] [NumberField F] (κ : Type) [Fintype κ]
    (L : AddSubgroup (κ → FiniteAdeleRing (𝓞 F) F)), IsOpen (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    IsCompact (L : Set (κ → FiniteAdeleRing (𝓞 F) F)) →
    ∀ K : Set (κ → FiniteAdeleRing (𝓞 F) F), IsCompact K →
    ∃ (m : ℕ) (g : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) → ℂ) (y : Fin m → κ → FiniteAdeleRing (𝓞 F) F),
      (∀ i, g i ∈ GlobalTheory.WeilM.SB (κ → FiniteAdeleRing (𝓞 F) F)) ∧ (∀ i j, g i (y j) = if i = j then 1 else 0) ∧
      ∀ Ψ ∈ GlobalTheory.WeilM.schA F κ, (∀ x ∈ L, ∀ z, Ψ (z + GlobalTheory.WeilCont.adeleJoin F 0 x) = Ψ z) →
        (∀ z, Ψ z ≠ 0 → (fun i => (z i).2) ∈ K) →
        ∃ f : Fin m → SchwartzMap (κ → mixedEmbedding.mixedSpace F) ℂ, Ψ = ∑ i, GlobalTheory.WeilM.pureA F (f i) (g i) := by
  intro F _ _ κ _ L hLo hLc K hK
  have hcont : ∀ k : κ → FiniteAdeleRing (𝓞 F) F, Continuous fun w : κ → FiniteAdeleRing (𝓞 F) F => w - k :=
    fun k => continuous_id.sub continuous_const
  have hmk : ∀ a b : κ → FiniteAdeleRing (𝓞 F) F,
      (QuotientAddGroup.mk a : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = QuotientAddGroup.mk b ↔ a - b ∈ L := by
    intro a b
    rw [QuotientAddGroup.eq, ← neg_mem_iff, neg_add, neg_neg, ← sub_eq_add_neg]
  have hfin : (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)).Finite := by
    obtain ⟨t, -, hcov⟩ := hK.elim_nhds_subcover (fun k => {w | w - k ∈ L})
      (fun k _ => (hLo.preimage (hcont k)).mem_nhds (by simp))
    refine (t.finite_toSet.image QuotientAddGroup.mk).subset ?_
    rintro _ ⟨w, hw, rfl⟩
    obtain ⟨k, hk, hwk⟩ := Set.mem_iUnion₂.mp (hcov hw)
    exact ⟨k, hk, ((hmk w k).2 hwk).symm⟩
  obtain ⟨m, e, he, hS⟩ : ∃ (m : ℕ) (e : Fin m → (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L), Function.Injective e ∧
      ∀ q, q ∈ (QuotientAddGroup.mk '' K : Set ((κ → FiniteAdeleRing (𝓞 F) F) ⧸ L)) ↔ ∃ i, e i = q := by
    refine ⟨hfin.toFinset.card, fun i => (hfin.toFinset.equivFin.symm i).1,
      Subtype.val_injective.comp hfin.toFinset.equivFin.symm.injective, fun q => ⟨fun hq => ?_, ?_⟩⟩
    · exact ⟨hfin.toFinset.equivFin ⟨q, hfin.mem_toFinset.2 hq⟩, by simp⟩
    · rintro ⟨i, rfl⟩
      exact hfin.mem_toFinset.1 (hfin.toFinset.equivFin.symm i).2
  choose y hy using fun i => QuotientAddGroup.mk_surjective (e i)
  refine ⟨m, fun i w => if (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) = e i then 1 else 0, y,
    fun i => ?_, fun i j => ?_, ?_⟩
  · refine ⟨(IsLocallyConstant.iff_exists_open _).2 fun x => ⟨{w | w - x ∈ L}, hLo.preimage (hcont x), by simp,
      fun x' hx' => ?_⟩, HasCompactSupport.intro' (K := {w | w - y i ∈ L})
      ((Homeomorph.subRight (y i)).isCompact_preimage.2 hLc)
      ((AddSubgroup.isClosed_of_isOpen L hLo).preimage (hcont (y i))) fun w hw => ?_⟩
    · dsimp only
      rw [(hmk x' x).2 hx']
    · dsimp only
      rw [if_neg]
      intro h
      exact hw ((hmk w (y i)).1 (h.trans (hy i).symm))
  · dsimp only
    rw [hy j]
    by_cases h : i = j
    · subst h; simp
    · rw [if_neg (fun h' => h (he h').symm), if_neg h]
  · intro Ψ hΨ hper hsupp
    choose f hf using fun i => GlobalTheory.WeilCont.exists_slice F hΨ (y i)
    refine ⟨f, funext fun z => ?_⟩
    obtain ⟨x, w, rfl⟩ : ∃ x w, z = GlobalTheory.WeilCont.adeleJoin F x w :=
      ⟨fun i => InfiniteAdeleRing.ringEquiv_mixedSpace F (z i).1, fun i => (z i).2,
        funext fun i => Prod.ext (by simp only [GlobalTheory.WeilCont.adeleJoin, RingEquiv.symm_apply_apply]) rfl⟩
    simp only [Finset.sum_apply, GlobalTheory.WeilCont.pureA_adeleJoin, ← hf]
    by_cases hw : (QuotientAddGroup.mk w : (κ → FiniteAdeleRing (𝓞 F) F) ⧸ L) ∈ QuotientAddGroup.mk '' K
    · obtain ⟨i0, hi0⟩ := (hS _).1 hw
      rw [Finset.sum_eq_single i0]
      · rw [if_pos hi0.symm, mul_one, hf]
        have hL : w - y i0 ∈ L := (hmk w (y i0)).1 (hi0.symm.trans (hy i0).symm)
        rw [← hper _ hL (GlobalTheory.WeilCont.adeleJoin F x (y i0))]
        congr 1
        funext i
        simp only [GlobalTheory.WeilCont.adeleJoin, Pi.add_apply, Pi.sub_apply, Pi.zero_apply, map_zero]
        exact Prod.ext (add_zero _).symm (add_sub_cancel _ _).symm
      · intro j _ hj
        rw [if_neg (fun h => hj (he (h.symm.trans hi0.symm))), mul_zero]
      · intro h
        exact absurd (Finset.mem_univ _) h
    · have h0 : Ψ (GlobalTheory.WeilCont.adeleJoin F x w) = 0 := by
        by_contra h
        exact hw ⟨w, hsupp _ h, rfl⟩
      rw [h0]
      refine (Finset.sum_eq_zero fun i _ => ?_).symm
      rw [if_neg, mul_zero]
      intro h
      exact hw (h ▸ (hS _).2 ⟨i, rfl⟩)
