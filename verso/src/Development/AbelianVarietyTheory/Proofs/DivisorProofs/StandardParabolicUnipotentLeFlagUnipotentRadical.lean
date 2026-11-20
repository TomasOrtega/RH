import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToGAdMat
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.LanglandsSquareIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.IsSquareIntegrableIffMemL2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPurelyImaginaryElement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsHermNDSmulSkewForm
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.SiegelSet GlobalTheory.UAut GlobalTheory.ThK.SquareIntegrability
open Matrix

namespace GlobalTheory.StdPar

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg`. Establish `e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m}` using `Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩`. Apply `Subgroup.subset_closure` to reduce the goal to its premises. Use `⟨fun i => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Establish `key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2}, ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤ (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a`.

Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩` from `hy`. Establish `hl : l.val < m.val + 1` using `Nat.lt_succ_of_le (hlk.trans (hS k hk))`.

Use `⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Use `Pi.single_eq_of_ne ?_ _` and prove the remaining obligations. Introduce and unpack `rfl`. Use `absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))` and prove the remaining obligations. Rewrite `ht`, the goal using `[Finset.mem_filter]`.

Conclude with `⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩`. Use `(Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2` as an intermediate fact. Conclude with `absurd this (not_lt.2 hlk)`. Rewrite using `[mulVec_single_one]`. Both sides reduce to the same expression.

Consider the case `zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨a, ha, rfl⟩` from `hy`. Take `⟨b, hb, rfl⟩` from `hz`. Conclude with `⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩`.

Consider the case `smul c y _ hy`. Take `⟨a, ha, rfl⟩` from `hy`. Conclude with `⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩`. Use `(Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)` as an intermediate fact. Take `⟨a, ha, e⟩` from `key _ this`.

Use `⟨a, ha, ?_⟩` and prove the remaining obligations. Rewrite using `[sub_mulVec, one_mulVec]`. Conclude with `e`. Use `hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by` as an intermediate fact. Rewrite using `[e1, mem_colPerp_iff]`.

Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))`. Rewrite `this` using `[e1, mem_colSpan_iff]`. Conclude with `this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]`.
-/
theorem unip_le_unipFlag_initCols : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ →
    ∀ (n : ℕ) (J : Matrix (Fin n) (Fin n) E), IsHermND σ J → ∀ (r : ℕ) (X Y : Matrix (Fin n) (Fin r) E), IsWittFrame σ J X Y →
      ∀ (S : Finset (Fin r)) (m : Fin r), m ∈ S → (∀ k ∈ S, k ≤ m) →
        GlobalTheory.StdPar.unip σ J X S ≤ GlobalTheory.UAut.unipFlag σ J (GlobalTheory.StdPar.initCols X m) (fun i => (S.filter fun k => k.val < i.val).card) := by
  intro F E _ _ _ _ _ σ _ n J _ r X Y _ S m hm hS g hg
  have e1 : {i | ∃ k ∈ S, i ≤ k} = {i | i ≤ m} :=
    Set.ext fun i => ⟨fun ⟨k, hk, h⟩ => h.trans (hS k hk), fun h => ⟨m, hm, h⟩⟩
  apply Subgroup.subset_closure
  refine ⟨fun i => ?_, fun x hx => ?_⟩
  · have key : ∀ y ∈ colSpan F X {l | ∃ k ∈ S, l ≤ k ∧ k < i.castLE m.2},
        ∃ a : Fin (m.val + 1) → AF F ⊗[F] E, (∀ j : Fin (m.val + 1), (S.filter fun k => k.val < i.val).card ≤
          (S.filter fun k => k.val < j.val).card → a j = 0) ∧ y = adMat F (initCols X m) *ᵥ a := by
      intro y hy
      induction hy using Submodule.span_induction with
      | mem y hy =>
        obtain ⟨l, ⟨k, hk, hlk, hki⟩, rfl⟩ := hy
        have hl : l.val < m.val + 1 := Nat.lt_succ_of_le (hlk.trans (hS k hk))
        refine ⟨Pi.single ⟨l.val, hl⟩ 1, fun j hj => ?_, ?_⟩
        · refine Pi.single_eq_of_ne ?_ _
          rintro rfl
          refine absurd hj (not_le.2 (Finset.card_lt_card ⟨fun t ht => ?_, fun h => ?_⟩))
          · rw [Finset.mem_filter] at ht ⊢
            exact ⟨ht.1, lt_trans (lt_of_lt_of_le ht.2 hlk) hki⟩
          · have := (Finset.mem_filter.1 (h (Finset.mem_filter.2 ⟨hk, hki⟩))).2
            exact absurd this (not_lt.2 hlk)
        · rw [mulVec_single_one]
          rfl
      | zero => exact ⟨0, fun _ _ => rfl, (mulVec_zero _).symm⟩
      | add y z _ _ hy hz =>
        obtain ⟨a, ha, rfl⟩ := hy
        obtain ⟨b, hb, rfl⟩ := hz
        exact ⟨a + b, fun j hj => by rw [Pi.add_apply, ha j hj, hb j hj, add_zero], (mulVec_add _ _ _).symm⟩
      | smul c y _ hy =>
        obtain ⟨a, ha, rfl⟩ := hy
        exact ⟨c • a, fun j hj => by rw [Pi.smul_apply, ha j hj, smul_zero], (mulVec_smul _ _ _).symm⟩
    have := (Subgroup.mem_iInf.1 hg.1 (i.castLE m.2)).2 _ (Submodule.subset_span ⟨_, rfl, rfl⟩)
    obtain ⟨a, ha, e⟩ := key _ this
    refine ⟨a, ha, ?_⟩
    rw [sub_mulVec, one_mulVec]
    exact e
  · have := hg.2.2 (fun i => inclR (F := F) (AF F) (x i)) (by
      rw [e1, mem_colPerp_iff]
      funext i
      exact (RingHom.map_mulVec (inclR (F := F) (AF F)) _ x i).symm.trans (by rw [hx]; exact map_zero _))
    rw [e1, mem_colSpan_iff] at this
    exact this.imp fun a ha => by rw [sub_mulVec, one_mulVec, ha]

end GlobalTheory.StdPar
