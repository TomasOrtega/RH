import Mathlib
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.FlagPairDefinitePartLattice
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.ChartGen
import Development.AbelianVarietyTheory.PublishedTheorems.DiscreteSeriesUnitary₂.MaxMass
import Development.AbelianVarietyTheory.Definitions.SemilocalFrames.NormalFormDualOrthogonalLast
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.InvVolEqInfMulSupAndMono
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairCommonUnipotentStabiliserSummary
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.HermFramePairNormalFormGeometrySummaryStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.NormalFormTerminalDeterminantStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FlagPairDefiniteThetaLatticeLeFixedIndexBoundStatement
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegerAddStarEqOneOfIsCMUnramStatement
import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.ExistsHasLeadingCoeffOfMemSpanBelow

open NumberField Formalism.HermitianLatticeCounting.S6 GlobalTheory.HermLat GlobalTheory.DegCnt
open scoped Pointwise ENNReal Classical nonZeroDivisors

namespace GlobalTheory.DegCnt.MidLayer

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on_max with`. Consider the case `empty`. Introduce `R A B hA hB _ hker _ _ _`. Establish `e1 : A = R` using `le_antisymm hA fun s hs => (hker s hs (by simp)).1`. Establish `e2 : B = R` using `le_antisymm hB fun s hs => (hker s hs (by simp)).2`.

Rewrite using `[e1, e2]`. Simplify using `[GlobalTheory.HL.invVol]`. Consider the case `insert m S hlt ih`. Introduce `R A B hA hB hhom hker hAP hQB hfin`. Establish `hm : m ∉ S` using `fun h => lt_irrefl m (hlt m h)`.

Establish `hmS : m ∈ insert m S` using `Finset.mem_insert_self m S`. Establish `hnn : ∀ X Y : Subgroup G, (0 : ℝ) ≤ GlobalTheory.HL.invVol X Y` using `fun X Y => by`. Unfold `GlobalTheory.HL.invVol`. Check the signs of the components of the expression. Distinguish the cases in `hAB : A.relIndex B = 0`.

Establish `h0 : GlobalTheory.HL.invVol A B = 0` using `by simp [GlobalTheory.HL.invVol, hAB]`. Rewrite using `[h0]`. Conclude with `Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _`. Distinguish the cases in `hBA : B.relIndex A = 0`. Establish `h0 : GlobalTheory.HL.invVol A B = 0` using `by simp [GlobalTheory.HL.invVol, hBA]`.

Rewrite using `[h0]`. Conclude with `Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _`. Establish `hf1 : f m 1 = 0`. Establish `h` using `hhom m hmS 1 R.one_mem 1 R.one_mem`. Rewrite `h` using `[mul_one]`.

Conclude with `add_left_cancel (h.symm.trans (add_zero _).symm)`. Establish `hinv : ∀ s ∈ R, f m s⁻¹ = -f m s` using `fun s hs => by`. Establish `h` using `hhom m hmS s hs s⁻¹ (R.inv_mem hs)`. Rewrite `h` using `[mul_inv_cancel, hf1]`. Rewrite using `[eq_neg_iff_add_eq_zero, add_comm, ← h]`.

Set `pre : AddSubgroup W → Subgroup G` to `fun X => { carrier := {s | s ∈ R ∧ f m s ∈ X} one_mem' := ⟨R.one_mem, by rw [hf1]; exact X.zero_mem⟩ mul_mem' := fun {s t} hs ht => ⟨R.mul_mem hs.1 ht.1, by`. Rewrite using `[hhom m hmS s hs.1 t ht.1]`. Conclude with `X.add_mem hs.2 ht.2⟩`. Use the proof step `inv_mem' := fun {s} hs => ⟨R.inv_mem hs.1, by rw [hinv s hs.1]; exact X.neg_mem hs.2⟩ }`. Establish `hpre : ∀ X s, s ∈ pre X ↔ s ∈ R ∧ f m s ∈ X` using `fun _ _ => Iff.rfl`.

Establish `hM : ∀ s, s ∈ pre ⊥ ↔ s ∈ R ∧ f m s = 0` using `fun s => by`. Rewrite using `[hpre, AddSubgroup.mem_bot]`. Establish `hMR : pre ⊥ ≤ R` using `fun s hs => ((hM s).1 hs).1`. Establish `hnorm : ∀ s ∈ R, ∀ t ∈ pre ⊥, s * t * s⁻¹ ∈ pre ⊥`. Introduce `s hs t ht`.

Rewrite `ht`, the goal using `[hM]`. Use `⟨R.mul_mem (R.mul_mem hs ht.1) (R.inv_mem hs), ?_⟩` and prove the remaining obligations. Rewrite using `[hhom m hmS _ (R.mul_mem hs ht.1) _ (R.inv_mem hs), hhom m hmS _ hs _ ht.1, ht.2, hinv s hs]`. Normalize the expressions using the abelian group laws. Take `⟨hsplit, -⟩` from `GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) A B hMR hA hB hnorm hAB hBA`.

Establish `hI` using `ih (pre ⊥) (A ⊓ pre ⊥) (B ⊓ pre ⊥) inf_le_right inf_le_right (fun a ha s hs t ht => hhom a (Finset.mem_insert_of_mem ha) s (hMR hs) t (hMR ht)) (fun s hs h0 => by`. Establish `hsR` using `(hM s).1 hs`. Establish `hAB'` using `hker s hsR.1 fun a ha => by`. Break down `Finset.mem_insert.1 ha with rfl | ha'` into its components or cases. Conclude with `hsR.2`.

Conclude with `h0 a ha'`. Conclude with `⟨⟨hAB'.1, hs⟩, ⟨hAB'.2, hs⟩⟩)`. Use the proof step `(fun a ha s hs => hAP a (Finset.mem_insert_of_mem ha) s hs.1)`. Use the proof step `(fun a ha y hy => by`. Take `⟨s, hs, hfs, hb⟩` from `hQB a (Finset.mem_insert_of_mem ha) y hy`.

Conclude with `⟨s, ⟨hs, (hM s).2 ⟨hB hs, hb m hmS (hlt a ha)⟩⟩, hfs, fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩)`. Use the proof step `(fun a ha => hfin a (Finset.mem_insert_of_mem ha))`. Establish `hpos : GlobalTheory.HL.invVol A B ≠ 0`. Unfold `GlobalTheory.HL.invVol`. Conclude with `div_ne_zero (Nat.cast_ne_zero.2 hBA) (Nat.cast_ne_zero.2 hAB)`.

Establish `hY0 : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≠ 0` using `fun h0 => hpos (by rw [hsplit, h0, mul_zero])`. Establish `hA1B1 : (A ⊔ pre ⊥).relIndex (B ⊔ pre ⊥) ≠ 0` using `fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])`. Establish `hB1A1 : (B ⊔ pre ⊥).relIndex (A ⊔ pre ⊥) ≠ 0` using `fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])`. Establish `hA1R : A ⊔ pre ⊥ ≤ R` using `sup_le hA hMR`. Establish `hB1R : B ⊔ pre ⊥ ≤ R` using `sup_le hB hMR`.

Take `⟨-, hmono⟩` from `GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) (A ⊔ pre ⊥) (B ⊔ pre ⊥) hMR hA1R hB1R hnorm hA1B1 hB1A1`. Establish `hB2 : pre (Q m) ≤ B ⊔ pre ⊥`. Introduce `s hs`. Rewrite `hs` using `[hpre]`. Take `⟨b, hb, hfb, -⟩` from `hQB m hmS (f m s) hs.2`.

Establish `hbs : b⁻¹ * s ∈ pre ⊥`. Rewrite using `[hM]`. Use `⟨R.mul_mem (R.inv_mem (hB hb)) hs.1, ?_⟩` and prove the remaining obligations. Rewrite using `[hhom m hmS _ (R.inv_mem (hB hb)) _ hs.1, hinv b (hB hb), hfb]`. Normalize the expressions using the abelian group laws.

Establish `hs' : b * (b⁻¹ * s) = s` using `mul_inv_cancel_left b s`. Rewrite using `[← hs']`. Conclude with `(B ⊔ pre ⊥).mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hbs)`. Establish `hA1P : A ⊔ pre ⊥ ≤ pre (P m)` using `sup_le (fun s hs => (hpre _ _).2 ⟨hA hs, hAP m hmS s hs⟩) (fun s hs => (hpre _ _).2 ⟨hMR hs, by rw [((hM s).1 hs).2]; exact (P m).zero_mem⟩)`. Set `ψ : R →* Multiplicative W` to `{ toFun := fun s => Multiplicative.ofAdd (f m s) map_one' := by show Multiplicative.ofAdd (f m 1) = 1`.

Rewrite using `[hf1, ofAdd_zero]`. Use the proof step `map_mul' := fun s t => by show Multiplicative.ofAdd (f m ((s : G) * t)) = Multiplicative.ofAdd (f m s) * Multiplicative.ofAdd (f m t)`. Rewrite using `[hhom m hmS s s.2 t t.2, ofAdd_add] }`. Establish `hcomap : (pre (Q m)).subgroupOf R = (AddSubgroup.toSubgroup (Q m)).comap ψ`. Use extensionality with `s`.

Conclude with `⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩`. Establish `hmap : ((A ⊔ pre ⊥).subgroupOf R).map ψ ≤ AddSubgroup.toSubgroup (P m)`. Introduce and unpack `_ ⟨s, hs, rfl⟩`. Conclude with `((hpre _ _).1 (hA1P (Subgroup.mem_subgroupOf.1 hs))).2`. Establish `hQP : (AddSubgroup.toSubgroup (Q m)).relIndex (AddSubgroup.toSubgroup (P m)) ≠ 0`.

Rewrite using `[AddSubgroup.relIndex_toSubgroup]`. Conclude with `hfin m hmS`. Establish `hkey : (pre (Q m)).relIndex (A ⊔ pre ⊥) = (AddSubgroup.toSubgroup (Q m)).relIndex (((A ⊔ pre ⊥).subgroupOf R).map ψ)`. Rewrite using `[← Subgroup.relIndex_subgroupOf (H := pre (Q m)) hA1R, hcomap, Subgroup.relIndex_comap]`. Establish `hB2A1 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≠ 0`.

Rewrite using `[hkey]`. Conclude with `fun h0 => hQP (Subgroup.relIndex_eq_zero_of_le_right hmap h0)`. Establish `hA1B2 : (A ⊔ pre ⊥).relIndex (pre (Q m)) ≠ 0` using `fun h0 => hA1B1 (Subgroup.relIndex_eq_zero_of_le_right hB2 h0)`. Establish `h5 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≤ (Q m).relIndex (P m)`. Rewrite using `[hkey, ← AddSubgroup.relIndex_toSubgroup]`.

Conclude with `Subgroup.relIndex_le_of_le_right hmap hQP`. Establish `hY : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≤ ((Q m).relIndex (P m) : ℝ)` using `((hmono (pre (Q m)) hB2 hB2A1 hA1B2).2).trans (by exact_mod_cast h5)`. Rewrite using `[hsplit, Finset.prod_insert hm, mul_comm ((Q m).relIndex (P m) : ℝ)]`. Conclude with `mul_le_mul hI hY (hnn _ _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)`.
-/
theorem invVol_le_prod {G W ι : Type} [Group G] [AddCommGroup W] [LinearOrder ι] (f : ι → G → W)
    (P Q : ι → AddSubgroup W) (S : Finset ι) :
    ∀ R A B : Subgroup G, A ≤ R → B ≤ R →
      (∀ a ∈ S, ∀ s ∈ R, ∀ t ∈ R, f a (s * t) = f a s + f a t) →
      (∀ s ∈ R, (∀ a ∈ S, f a s = 0) → s ∈ A ∧ s ∈ B) →
      (∀ a ∈ S, ∀ s ∈ A, f a s ∈ P a) →
      (∀ a ∈ S, ∀ y ∈ Q a, ∃ s ∈ B, f a s = y ∧ ∀ b ∈ S, a < b → f b s = 0) →
      (∀ a ∈ S, (Q a).relIndex (P a) ≠ 0) →
      GlobalTheory.HL.invVol A B ≤ ∏ a ∈ S, ((Q a).relIndex (P a) : ℝ) := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro R A B hA hB _ hker _ _ _
    have e1 : A = R := le_antisymm hA fun s hs => (hker s hs (by simp)).1
    have e2 : B = R := le_antisymm hB fun s hs => (hker s hs (by simp)).2
    rw [e1, e2]
    simp [GlobalTheory.HL.invVol]
  | insert m S hlt ih =>
    intro R A B hA hB hhom hker hAP hQB hfin
    have hm : m ∉ S := fun h => lt_irrefl m (hlt m h)
    have hmS : m ∈ insert m S := Finset.mem_insert_self m S
    have hnn : ∀ X Y : Subgroup G, (0 : ℝ) ≤ GlobalTheory.HL.invVol X Y := fun X Y => by
      unfold GlobalTheory.HL.invVol
      positivity
    by_cases hAB : A.relIndex B = 0
    · have h0 : GlobalTheory.HL.invVol A B = 0 := by simp [GlobalTheory.HL.invVol, hAB]
      rw [h0]
      exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    by_cases hBA : B.relIndex A = 0
    · have h0 : GlobalTheory.HL.invVol A B = 0 := by simp [GlobalTheory.HL.invVol, hBA]
      rw [h0]
      exact Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _
    have hf1 : f m 1 = 0 := by
      have h := hhom m hmS 1 R.one_mem 1 R.one_mem
      rw [mul_one] at h
      exact add_left_cancel (h.symm.trans (add_zero _).symm)
    have hinv : ∀ s ∈ R, f m s⁻¹ = -f m s := fun s hs => by
      have h := hhom m hmS s hs s⁻¹ (R.inv_mem hs)
      rw [mul_inv_cancel, hf1] at h
      rw [eq_neg_iff_add_eq_zero, add_comm, ← h]
    let pre : AddSubgroup W → Subgroup G := fun X =>
      { carrier := {s | s ∈ R ∧ f m s ∈ X}
        one_mem' := ⟨R.one_mem, by rw [hf1]; exact X.zero_mem⟩
        mul_mem' := fun {s t} hs ht => ⟨R.mul_mem hs.1 ht.1, by
          rw [hhom m hmS s hs.1 t ht.1]; exact X.add_mem hs.2 ht.2⟩
        inv_mem' := fun {s} hs => ⟨R.inv_mem hs.1, by rw [hinv s hs.1]; exact X.neg_mem hs.2⟩ }
    have hpre : ∀ X s, s ∈ pre X ↔ s ∈ R ∧ f m s ∈ X := fun _ _ => Iff.rfl
    have hM : ∀ s, s ∈ pre ⊥ ↔ s ∈ R ∧ f m s = 0 := fun s => by
      rw [hpre, AddSubgroup.mem_bot]
    have hMR : pre ⊥ ≤ R := fun s hs => ((hM s).1 hs).1
    have hnorm : ∀ s ∈ R, ∀ t ∈ pre ⊥, s * t * s⁻¹ ∈ pre ⊥ := by
      intro s hs t ht
      rw [hM] at ht ⊢
      refine ⟨R.mul_mem (R.mul_mem hs ht.1) (R.inv_mem hs), ?_⟩
      rw [hhom m hmS _ (R.mul_mem hs ht.1) _ (R.inv_mem hs), hhom m hmS _ hs _ ht.1, ht.2, hinv s hs]
      abel
    obtain ⟨hsplit, -⟩ :=
      GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) A B hMR hA hB hnorm hAB hBA
    have hI := ih (pre ⊥) (A ⊓ pre ⊥) (B ⊓ pre ⊥) inf_le_right inf_le_right
      (fun a ha s hs t ht => hhom a (Finset.mem_insert_of_mem ha) s (hMR hs) t (hMR ht))
      (fun s hs h0 => by
        have hsR := (hM s).1 hs
        have hAB' := hker s hsR.1 fun a ha => by
          rcases Finset.mem_insert.1 ha with rfl | ha'
          · exact hsR.2
          · exact h0 a ha'
        exact ⟨⟨hAB'.1, hs⟩, ⟨hAB'.2, hs⟩⟩)
      (fun a ha s hs => hAP a (Finset.mem_insert_of_mem ha) s hs.1)
      (fun a ha y hy => by
        obtain ⟨s, hs, hfs, hb⟩ := hQB a (Finset.mem_insert_of_mem ha) y hy
        exact ⟨s, ⟨hs, (hM s).2 ⟨hB hs, hb m hmS (hlt a ha)⟩⟩, hfs,
          fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩)
      (fun a ha => hfin a (Finset.mem_insert_of_mem ha))
    have hpos : GlobalTheory.HL.invVol A B ≠ 0 := by
      unfold GlobalTheory.HL.invVol
      exact div_ne_zero (Nat.cast_ne_zero.2 hBA) (Nat.cast_ne_zero.2 hAB)
    have hY0 : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≠ 0 := fun h0 => hpos (by rw [hsplit, h0, mul_zero])
    have hA1B1 : (A ⊔ pre ⊥).relIndex (B ⊔ pre ⊥) ≠ 0 := fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])
    have hB1A1 : (B ⊔ pre ⊥).relIndex (A ⊔ pre ⊥) ≠ 0 := fun h0 => hY0 (by simp [GlobalTheory.HL.invVol, h0])
    have hA1R : A ⊔ pre ⊥ ≤ R := sup_le hA hMR
    have hB1R : B ⊔ pre ⊥ ≤ R := sup_le hB hMR
    obtain ⟨-, hmono⟩ := GlobalTheory.IndexProd.invVol_eq_inf_mul_sup_and_mono G R (pre ⊥) (A ⊔ pre ⊥)
      (B ⊔ pre ⊥) hMR hA1R hB1R hnorm hA1B1 hB1A1
    have hB2 : pre (Q m) ≤ B ⊔ pre ⊥ := by
      intro s hs
      rw [hpre] at hs
      obtain ⟨b, hb, hfb, -⟩ := hQB m hmS (f m s) hs.2
      have hbs : b⁻¹ * s ∈ pre ⊥ := by
        rw [hM]
        refine ⟨R.mul_mem (R.inv_mem (hB hb)) hs.1, ?_⟩
        rw [hhom m hmS _ (R.inv_mem (hB hb)) _ hs.1, hinv b (hB hb), hfb]
        abel
      have hs' : b * (b⁻¹ * s) = s := mul_inv_cancel_left b s
      rw [← hs']
      exact (B ⊔ pre ⊥).mul_mem (Subgroup.mem_sup_left hb) (Subgroup.mem_sup_right hbs)
    have hA1P : A ⊔ pre ⊥ ≤ pre (P m) := sup_le (fun s hs => (hpre _ _).2 ⟨hA hs, hAP m hmS s hs⟩)
      (fun s hs => (hpre _ _).2 ⟨hMR hs, by rw [((hM s).1 hs).2]; exact (P m).zero_mem⟩)
    let ψ : R →* Multiplicative W :=
      { toFun := fun s => Multiplicative.ofAdd (f m s)
        map_one' := by
          show Multiplicative.ofAdd (f m 1) = 1
          rw [hf1, ofAdd_zero]
        map_mul' := fun s t => by
          show Multiplicative.ofAdd (f m ((s : G) * t)) =
            Multiplicative.ofAdd (f m s) * Multiplicative.ofAdd (f m t)
          rw [hhom m hmS s s.2 t t.2, ofAdd_add] }
    have hcomap : (pre (Q m)).subgroupOf R = (AddSubgroup.toSubgroup (Q m)).comap ψ := by
      ext s
      exact ⟨fun h => h.2, fun h => ⟨s.2, h⟩⟩
    have hmap : ((A ⊔ pre ⊥).subgroupOf R).map ψ ≤ AddSubgroup.toSubgroup (P m) := by
      rintro _ ⟨s, hs, rfl⟩
      exact ((hpre _ _).1 (hA1P (Subgroup.mem_subgroupOf.1 hs))).2
    have hQP : (AddSubgroup.toSubgroup (Q m)).relIndex (AddSubgroup.toSubgroup (P m)) ≠ 0 := by
      rw [AddSubgroup.relIndex_toSubgroup]
      exact hfin m hmS
    have hkey : (pre (Q m)).relIndex (A ⊔ pre ⊥) =
        (AddSubgroup.toSubgroup (Q m)).relIndex (((A ⊔ pre ⊥).subgroupOf R).map ψ) := by
      rw [← Subgroup.relIndex_subgroupOf (H := pre (Q m)) hA1R, hcomap, Subgroup.relIndex_comap]
    have hB2A1 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≠ 0 := by
      rw [hkey]
      exact fun h0 => hQP (Subgroup.relIndex_eq_zero_of_le_right hmap h0)
    have hA1B2 : (A ⊔ pre ⊥).relIndex (pre (Q m)) ≠ 0 := fun h0 =>
      hA1B1 (Subgroup.relIndex_eq_zero_of_le_right hB2 h0)
    have h5 : (pre (Q m)).relIndex (A ⊔ pre ⊥) ≤ (Q m).relIndex (P m) := by
      rw [hkey, ← AddSubgroup.relIndex_toSubgroup]
      exact Subgroup.relIndex_le_of_le_right hmap hQP
    have hY : GlobalTheory.HL.invVol (A ⊔ pre ⊥) (B ⊔ pre ⊥) ≤ ((Q m).relIndex (P m) : ℝ) :=
      ((hmono (pre (Q m)) hB2 hB2A1 hA1B2).2).trans (by exact_mod_cast h5)
    rw [hsplit, Finset.prod_insert hm, mul_comm ((Q m).relIndex (P m) : ℝ)]
    exact mul_le_mul hI hY (hnn _ _) (Finset.prod_nonneg fun _ _ => Nat.cast_nonneg _)

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on_max with`. Consider the case `empty`. Introduce `A B hBA _ _`. Conclude with `⟨by simp, by simpa using Nat.one_le_iff_ne_zero.2 hBA⟩`. Consider the case `insert m S hlt ih`.

Introduce `A B hBA h1 h2`. Establish `hm : m ∉ S` using `fun h => lt_irrefl m (hlt m h)`. Establish `hDA : B ⊓ A ≤ A` using `inf_le_right`. Establish `hsplit : B.relIndex A = B.relIndex (A ⊓ (f m).ker) * ((B ⊓ A).map (f m)).relIndex (A.map (f m))`. Establish `hDE : B ⊓ A ≤ (B ⊓ A) ⊔ (A ⊓ (f m).ker)` using `le_sup_left`.

Establish `hEA : (B ⊓ A) ⊔ (A ⊓ (f m).ker) ≤ A` using `sup_le inf_le_right inf_le_left`. Rewrite using `[← AddSubgroup.inf_relIndex_right B A, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hDE hEA]`. Use `congr 1`. Rewrite using `[AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right (B ⊓ A) (A ⊓ (f m).ker), ← AddSubgroup.inf_relIndex_right B (A ⊓ (f m).ker)]`. Use `congr 1`.

Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic. Rewrite using `[← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq, ← AddSubgroup.inf_relIndex_right (B ⊓ A ⊔ (f m).ker) A, sup_inf_assoc_of_le _ hDA, inf_comm (f m).ker A]`. Establish `hBk : (B ⊓ (f m).ker).relIndex (A ⊓ (f m).ker) = B.relIndex (A ⊓ (f m).ker)`.

Rewrite using `[← AddSubgroup.inf_relIndex_right (B ⊓ (f m).ker), ← AddSubgroup.inf_relIndex_right B]`. Use `congr 1`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf]`. The claim follows by propositional logic.

Establish `hX : B.relIndex (A ⊓ (f m).ker) ≠ 0` using `fun h0 => hBA (by rw [hsplit, h0, zero_mul])`. Establish `hY : ((B ⊓ A).map (f m)).relIndex (A.map (f m)) ≠ 0` using `fun h0 => hBA (by rw [hsplit, h0, mul_zero])`. Establish `h1' : ∀ a ∈ S, ∀ y ∈ P a, ∃ x ∈ A ⊓ (f m).ker, f a x = y ∧ ∀ b ∈ S, a < b → f b x = 0`. Introduce `a ha y hy`. Take `⟨x, hx, hfx, hb⟩` from `h1 a (Finset.mem_insert_of_mem ha) y hy`.

Conclude with `⟨x, AddSubgroup.mem_inf.2 ⟨hx, (f m).mem_ker.2 (hb m (Finset.mem_insert_self m S) (hlt a ha))⟩, hfx, fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩`. Establish `h2' : ∀ a ∈ S, ∀ x ∈ B ⊓ (f m).ker, (∀ b ∈ S, a < b → f b x = 0) → f a x ∈ Q a`. Introduce `a ha x hx hb`. Establish `hx'` using `AddSubgroup.mem_inf.1 hx`. Use `h2 a (Finset.mem_insert_of_mem ha) x hx'.1 fun b hb' hab => ?_` and prove the remaining obligations.

Break down `Finset.mem_insert.1 hb' with rfl | hb''` into its components or cases. Conclude with `(f b).mem_ker.1 hx'.2`. Conclude with `hb b hb'' hab`. Take `⟨hne', hprod'⟩` from `ih (A ⊓ (f m).ker) (B ⊓ (f m).ker) (by rw [hBk]; exact hX) h1' h2'`. Establish `hPm : P m ≤ A.map (f m)`.

Introduce `y hy`. Take `⟨x, hx, hfx, _⟩` from `h1 m (Finset.mem_insert_self m S) y hy`. Conclude with `⟨x, hx, hfx⟩`. Establish `hQm : (B ⊓ A).map (f m) ≤ Q m`. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `h2 m (Finset.mem_insert_self m S) x (AddSubgroup.mem_inf.1 hx).1 fun b hb hmb => ?_` and prove the remaining obligations. Break down `Finset.mem_insert.1 hb with rfl | hb''` into its components or cases. Conclude with `absurd hmb (lt_irrefl _)`. Conclude with `absurd (hlt b hb'') (lt_asymm hmb)`. Establish `hQA : (Q m).relIndex (A.map (f m)) ≠ 0` using `fun h0 => hY (AddSubgroup.relIndex_eq_zero_of_le_left hQm h0)`.

Establish `hlev : (Q m).relIndex (P m) ≤ ((B ⊓ A).map (f m)).relIndex (A.map (f m))` using `(AddSubgroup.relIndex_le_of_le_right hPm hQA).trans (AddSubgroup.relIndex_le_of_le_left hQm hY)`. Establish `hneM : (Q m).relIndex (P m) ≠ 0` using `fun h0 => hQA (AddSubgroup.relIndex_eq_zero_of_le_right hPm h0)`. Use `⟨fun a ha => ?_, ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 ha with rfl | ha'` into its components or cases. Conclude with `hneM`.

Conclude with `hne' a ha'`. Rewrite using `[Finset.prod_insert hm, hsplit, ← hBk, mul_comm]`. Conclude with `Nat.mul_le_mul hprod' hlev`.
-/
theorem prod_le_relIndex {V W ι : Type} [AddCommGroup V] [AddCommGroup W] [LinearOrder ι]
    (f : ι → V →+ W) (P Q : ι → AddSubgroup W) (S : Finset ι) :
    ∀ A B : AddSubgroup V, B.relIndex A ≠ 0 →
      (∀ a ∈ S, ∀ y ∈ P a, ∃ x ∈ A, f a x = y ∧ ∀ b ∈ S, a < b → f b x = 0) →
      (∀ a ∈ S, ∀ x ∈ B, (∀ b ∈ S, a < b → f b x = 0) → f a x ∈ Q a) →
      (∀ a ∈ S, (Q a).relIndex (P a) ≠ 0) ∧ ∏ a ∈ S, (Q a).relIndex (P a) ≤ B.relIndex A := by
  classical
  induction S using Finset.induction_on_max with
  | empty =>
    intro A B hBA _ _
    exact ⟨by simp, by simpa using Nat.one_le_iff_ne_zero.2 hBA⟩
  | insert m S hlt ih =>
    intro A B hBA h1 h2
    have hm : m ∉ S := fun h => lt_irrefl m (hlt m h)
    have hDA : B ⊓ A ≤ A := inf_le_right
    have hsplit : B.relIndex A = B.relIndex (A ⊓ (f m).ker) *
        ((B ⊓ A).map (f m)).relIndex (A.map (f m)) := by
      have hDE : B ⊓ A ≤ (B ⊓ A) ⊔ (A ⊓ (f m).ker) := le_sup_left
      have hEA : (B ⊓ A) ⊔ (A ⊓ (f m).ker) ≤ A := sup_le inf_le_right inf_le_left
      rw [← AddSubgroup.inf_relIndex_right B A, ← AddSubgroup.relIndex_mul_relIndex _ _ _ hDE hEA]
      congr 1
      · rw [AddSubgroup.relIndex_sup_left, ← AddSubgroup.inf_relIndex_right (B ⊓ A) (A ⊓ (f m).ker),
          ← AddSubgroup.inf_relIndex_right B (A ⊓ (f m).ker)]
        congr 1
        ext x
        simp only [AddSubgroup.mem_inf]
        tauto
      · rw [← AddSubgroup.relIndex_comap, AddSubgroup.comap_map_eq,
          ← AddSubgroup.inf_relIndex_right (B ⊓ A ⊔ (f m).ker) A, sup_inf_assoc_of_le _ hDA,
          inf_comm (f m).ker A]
    have hBk : (B ⊓ (f m).ker).relIndex (A ⊓ (f m).ker) = B.relIndex (A ⊓ (f m).ker) := by
      rw [← AddSubgroup.inf_relIndex_right (B ⊓ (f m).ker), ← AddSubgroup.inf_relIndex_right B]
      congr 1
      ext x
      simp only [AddSubgroup.mem_inf]
      tauto
    have hX : B.relIndex (A ⊓ (f m).ker) ≠ 0 := fun h0 => hBA (by rw [hsplit, h0, zero_mul])
    have hY : ((B ⊓ A).map (f m)).relIndex (A.map (f m)) ≠ 0 := fun h0 => hBA (by rw [hsplit, h0, mul_zero])
    have h1' : ∀ a ∈ S, ∀ y ∈ P a, ∃ x ∈ A ⊓ (f m).ker, f a x = y ∧ ∀ b ∈ S, a < b → f b x = 0 := by
      intro a ha y hy
      obtain ⟨x, hx, hfx, hb⟩ := h1 a (Finset.mem_insert_of_mem ha) y hy
      exact ⟨x, AddSubgroup.mem_inf.2 ⟨hx, (f m).mem_ker.2 (hb m (Finset.mem_insert_self m S) (hlt a ha))⟩,
        hfx, fun b hb' hab => hb b (Finset.mem_insert_of_mem hb') hab⟩
    have h2' : ∀ a ∈ S, ∀ x ∈ B ⊓ (f m).ker, (∀ b ∈ S, a < b → f b x = 0) → f a x ∈ Q a := by
      intro a ha x hx hb
      have hx' := AddSubgroup.mem_inf.1 hx
      refine h2 a (Finset.mem_insert_of_mem ha) x hx'.1 fun b hb' hab => ?_
      rcases Finset.mem_insert.1 hb' with rfl | hb''
      · exact (f b).mem_ker.1 hx'.2
      · exact hb b hb'' hab
    obtain ⟨hne', hprod'⟩ := ih (A ⊓ (f m).ker) (B ⊓ (f m).ker) (by rw [hBk]; exact hX) h1' h2'
    have hPm : P m ≤ A.map (f m) := by
      intro y hy
      obtain ⟨x, hx, hfx, _⟩ := h1 m (Finset.mem_insert_self m S) y hy
      exact ⟨x, hx, hfx⟩
    have hQm : (B ⊓ A).map (f m) ≤ Q m := by
      rintro _ ⟨x, hx, rfl⟩
      refine h2 m (Finset.mem_insert_self m S) x (AddSubgroup.mem_inf.1 hx).1 fun b hb hmb => ?_
      rcases Finset.mem_insert.1 hb with rfl | hb''
      · exact absurd hmb (lt_irrefl _)
      · exact absurd (hlt b hb'') (lt_asymm hmb)
    have hQA : (Q m).relIndex (A.map (f m)) ≠ 0 := fun h0 =>
      hY (AddSubgroup.relIndex_eq_zero_of_le_left hQm h0)
    have hlev : (Q m).relIndex (P m) ≤ ((B ⊓ A).map (f m)).relIndex (A.map (f m)) :=
      (AddSubgroup.relIndex_le_of_le_right hPm hQA).trans (AddSubgroup.relIndex_le_of_le_left hQm hY)
    have hneM : (Q m).relIndex (P m) ≠ 0 := fun h0 =>
      hQA (AddSubgroup.relIndex_eq_zero_of_le_right hPm h0)
    refine ⟨fun a ha => ?_, ?_⟩
    · rcases Finset.mem_insert.1 ha with rfl | ha'
      · exact hneM
      · exact hne' a ha'
    · rw [Finset.prod_insert hm, hsplit, ← hBk, mul_comm]
      exact Nat.mul_le_mul hprod' hlev

/- English proof (translation)
Establish `h1 : (Q.comap φ).relIndex P₁ ≠ 0` using `fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_left hQ h0)`. Establish `h2 : (Q.comap φ).relIndex P₁ ≤ Q₁.relIndex P₁` using `AddSubgroup.relIndex_le_of_le_left hQ h`. Rewrite `h1`, `h2` using `[AddSubgroup.relIndex_comap]`. Establish `h3 : Q.relIndex (P₁.map φ ⊔ Q) ≠ 0` using `by rwa [AddSubgroup.relIndex_sup_right]`. Establish `hle : P ⊔ Q ≤ P₁.map φ ⊔ Q` using `sup_le (hP.trans (sup_le le_sup_right le_sup_left)) le_sup_right`.

Establish `h4 : Q.relIndex (P ⊔ Q) ≤ Q.relIndex (P₁.map φ ⊔ Q)` using `AddSubgroup.relIndex_le_of_le_right hle h3`. Rewrite `h4` using `[AddSubgroup.relIndex_sup_right, AddSubgroup.relIndex_sup_right]`. Use `⟨?_, h4.trans h2⟩` and prove the remaining obligations. Rewrite using `[← AddSubgroup.relIndex_sup_right]`. Conclude with `fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0)`.
-/
theorem relIndex_le_of_map {G₁ G : Type} [AddCommGroup G₁] [AddCommGroup G] (φ : G₁ →+ G)
    {P₁ Q₁ : AddSubgroup G₁} {P Q : AddSubgroup G} (hP : P ≤ Q ⊔ P₁.map φ) (hQ : Q₁ ≤ Q.comap φ)
    (h : Q₁.relIndex P₁ ≠ 0) : Q.relIndex P ≠ 0 ∧ Q.relIndex P ≤ Q₁.relIndex P₁ := by
  have h1 : (Q.comap φ).relIndex P₁ ≠ 0 := fun h0 => h (AddSubgroup.relIndex_eq_zero_of_le_left hQ h0)
  have h2 : (Q.comap φ).relIndex P₁ ≤ Q₁.relIndex P₁ := AddSubgroup.relIndex_le_of_le_left hQ h
  rw [AddSubgroup.relIndex_comap] at h1 h2
  have h3 : Q.relIndex (P₁.map φ ⊔ Q) ≠ 0 := by rwa [AddSubgroup.relIndex_sup_right]
  have hle : P ⊔ Q ≤ P₁.map φ ⊔ Q := sup_le (hP.trans (sup_le le_sup_right le_sup_left)) le_sup_right
  have h4 : Q.relIndex (P ⊔ Q) ≤ Q.relIndex (P₁.map φ ⊔ Q) := AddSubgroup.relIndex_le_of_le_right hle h3
  rw [AddSubgroup.relIndex_sup_right, AddSubgroup.relIndex_sup_right] at h4
  refine ⟨?_, h4.trans h2⟩
  rw [← AddSubgroup.relIndex_sup_right]
  exact fun h0 => h3 (AddSubgroup.relIndex_eq_zero_of_le_right hle h0)

section Lattice

variable {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V]
  [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]

/- English proof (translation)
Take `⟨d, hd, hdA⟩` from `FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hA`. Establish `hd0 : algebraMap (𝓞 K) K d ≠ 0` using `(map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hd)`. Set `f : 𝓞 K →ₗ[𝓞 K] K` to `(LinearMap.mulRight (𝓞 K) (algebraMap (𝓞 K) K d)⁻¹) ∘ₗ Algebra.linearMap (𝓞 K) K`. Establish `hf : ∀ b, f b = algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K d)⁻¹` using `fun b => rfl`. Set `I : Ideal (𝓞 K)` to `A.comap f`.

Establish `hsurj : ∀ t ∈ A, ∃ b ∈ I, f b = t`. Introduce `t ht`. Take `⟨b, hb⟩` from `RingHom.mem_rangeS.1 (hdA t ht)`. Establish `hfb : f b = t`. Rewrite using `[hf, hb, Algebra.smul_def, mul_comm (algebraMap (𝓞 K) K d) t, mul_assoc, mul_inv_cancel₀ hd0, mul_one]`.

Use `⟨b, ?_, hfb⟩` and prove the remaining obligations. Use `show f b ∈ A`. Rewrite using `[hfb]`. Conclude with `ht`. Distinguish the cases in `hA0 : ∀ t ∈ A, t = 0`.

Use `⟨0, A.zero_mem, fun t ht => ⟨0, 0, A.zero_mem, ?_⟩⟩` and prove the remaining obligations. Simplify using `[hA0 t ht]`. Use `push Not at hA0`. Take `⟨t0, ht0, ht00⟩` from `hA0`. Take `⟨b0, hb0, hfb0⟩` from `hsurj t0 ht0`.

Establish `hI : I ≠ ⊥`. Introduce `h`. Establish `hb : b0 ∈ (⊥ : Ideal (𝓞 K))` using `h ▸ hb0`. Rewrite `hb` using `[Ideal.mem_bot]`. Apply `ht00` to reduce the goal to its premises.

Rewrite using `[← hfb0, hb, map_zero]`. Establish `hn' : ((n : 𝓞 K)) ≠ 0` using `Nat.cast_ne_zero.2 hn`. Establish `hJ : Ideal.span {(n : 𝓞 K)} * I ≠ ⊥`. Rewrite using `[Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]`. Conclude with `⟨hn', hI⟩`.

Take `⟨y, hy⟩` from `IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(n : 𝓞 K)} * I) (J := I) (Ideal.mul_le.2 fun a _ b hb => I.mul_mem_left a hb) (by rwa [Ideal.zero_eq_bot])`. Establish `hyI : y ∈ I`. Rewrite using `[← hy]`. Conclude with `Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)`. Use `⟨f y, hyI, fun t ht => ?_⟩` and prove the remaining obligations.

Take `⟨b, hb, rfl⟩` from `hsurj t ht`. Rewrite `hb` using `[← hy]`. Take `⟨u, hu, w, hw, rfl⟩` from `Submodule.mem_sup.1 hb`. Take `⟨z, hz, rfl⟩` from `(Ideal.mem_span_singleton_mul).1 hu`. Take `⟨a, rfl⟩` from `(Ideal.mem_span_singleton').1 hw`.

Use `⟨a, f z, hz, ?_⟩` and prove the remaining obligations. Establish `e1 : f ((n : 𝓞 K) * z) = n • f z`. Rewrite using `[← smul_eq_mul, map_smul, Nat.cast_smul_eq_nsmul]`. Establish `e2 : f (a * y) = a • f y` using `by rw [← smul_eq_mul, map_smul]`. Rewrite using `[map_add, e1, e2, add_comm]`.
-/
theorem exists_gen_one (n : ℕ) (hn : n ≠ 0) (A : Submodule (𝓞 K) K) (hA : A.FG) :
    ∃ x ∈ A, ∀ t ∈ A, ∃ a : 𝓞 K, ∃ t' ∈ A, t = a • x + n • t' := by
  classical
  obtain ⟨d, hd, hdA⟩ := FractionalIdeal.isFractional_of_fg (S := (𝓞 K)⁰) hA
  have hd0 : algebraMap (𝓞 K) K d ≠ 0 :=
    (map_ne_zero_iff _ (IsFractionRing.injective (𝓞 K) K)).2 (nonZeroDivisors.ne_zero hd)
  let f : 𝓞 K →ₗ[𝓞 K] K :=
    (LinearMap.mulRight (𝓞 K) (algebraMap (𝓞 K) K d)⁻¹) ∘ₗ Algebra.linearMap (𝓞 K) K
  have hf : ∀ b, f b = algebraMap (𝓞 K) K b * (algebraMap (𝓞 K) K d)⁻¹ := fun b => rfl
  let I : Ideal (𝓞 K) := A.comap f
  have hsurj : ∀ t ∈ A, ∃ b ∈ I, f b = t := by
    intro t ht
    obtain ⟨b, hb⟩ := RingHom.mem_rangeS.1 (hdA t ht)
    have hfb : f b = t := by
      rw [hf, hb, Algebra.smul_def, mul_comm (algebraMap (𝓞 K) K d) t, mul_assoc,
        mul_inv_cancel₀ hd0, mul_one]
    refine ⟨b, ?_, hfb⟩
    show f b ∈ A
    rw [hfb]
    exact ht
  by_cases hA0 : ∀ t ∈ A, t = 0
  · refine ⟨0, A.zero_mem, fun t ht => ⟨0, 0, A.zero_mem, ?_⟩⟩
    simp [hA0 t ht]
  push Not at hA0
  obtain ⟨t0, ht0, ht00⟩ := hA0
  obtain ⟨b0, hb0, hfb0⟩ := hsurj t0 ht0
  have hI : I ≠ ⊥ := by
    intro h
    have hb : b0 ∈ (⊥ : Ideal (𝓞 K)) := h ▸ hb0
    rw [Ideal.mem_bot] at hb
    apply ht00
    rw [← hfb0, hb, map_zero]
  have hn' : ((n : 𝓞 K)) ≠ 0 := Nat.cast_ne_zero.2 hn
  have hJ : Ideal.span {(n : 𝓞 K)} * I ≠ ⊥ := by
    rw [Ne, Ideal.mul_eq_bot, not_or, Ideal.span_singleton_eq_bot]
    exact ⟨hn', hI⟩
  obtain ⟨y, hy⟩ := IsDedekindDomain.exists_sup_span_eq (I := Ideal.span {(n : 𝓞 K)} * I) (J := I) (Ideal.mul_le.2 fun a _ b hb => I.mul_mem_left a hb) (by rwa [Ideal.zero_eq_bot])
  have hyI : y ∈ I := by
    rw [← hy]
    exact Ideal.mem_sup_right (Ideal.mem_span_singleton_self y)
  refine ⟨f y, hyI, fun t ht => ?_⟩
  obtain ⟨b, hb, rfl⟩ := hsurj t ht
  rw [← hy] at hb
  obtain ⟨u, hu, w, hw, rfl⟩ := Submodule.mem_sup.1 hb
  obtain ⟨z, hz, rfl⟩ := (Ideal.mem_span_singleton_mul).1 hu
  obtain ⟨a, rfl⟩ := (Ideal.mem_span_singleton').1 hw
  refine ⟨a, f z, hz, ?_⟩
  have e1 : f ((n : 𝓞 K) * z) = n • f z := by
    rw [← smul_eq_mul, map_smul, Nat.cast_smul_eq_nsmul]
  have e2 : f (a * y) = a • f y := by rw [← smul_eq_mul, map_smul]
  rw [map_add, e1, e2, add_comm]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Introduce `W hW M _ hMW`. Use `⟨Fin.elim0, fun i => i.elim0, fun m hm => ⟨Fin.elim0, 0, M.zero_mem, ?_⟩⟩` and prove the remaining obligations. Establish `hW0 : W = ⊥` using `Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hW)`.

Establish `hm0 : m = 0`. Establish `h` using `hMW m hm`. Rewrite `h` using `[hW0]`. Conclude with `(Submodule.mem_bot K).1 h`. Simplify using `[hm0]`.

Consider the case `succ k ih`. Introduce `W hW M hM hMW`. Distinguish the cases in `hM0 : ∀ m ∈ M, m = 0`. Use `⟨0, fun i => by simp [M.zero_mem], fun m hm => ⟨0, 0, M.zero_mem, by simp [hM0 m hm]⟩⟩` and prove the remaining obligations. Use `push Not at hM0`.

Take `⟨w, hwM, hw0⟩` from `hM0`. Choose the witnesses or unpack the hypotheses as in `⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`. Conclude with `hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 h)`.

Set `φ' : V →ₗ[𝓞 K] K` to `φ.restrictScalars (𝓞 K)`. Take `⟨x0, hx0, hgen⟩` from `exists_gen_one n hn (M.map φ') (hM.map φ')`. Take `⟨m0, hm0, rfl⟩` from `Submodule.mem_map.1 hx0`. Establish `hW' : Module.finrank K ↥(W ⊓ LinearMap.ker φ) ≤ k`. Establish `hlt : W ⊓ LinearMap.ker φ < W`.

Use `lt_of_le_of_ne inf_le_left (fun h => hφ ?_)` and prove the remaining obligations. Establish `hw : w ∈ W ⊓ LinearMap.ker φ`. Rewrite using `[h]`. Conclude with `hMW w hwM`. Conclude with `LinearMap.mem_ker.1 hw.2`.

Use `Submodule.finrank_lt_finrank_of_lt hlt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hM' : (M ⊓ LinearMap.ker φ').FG`. Use `isNoetherian_of_fg_of_noetherian M hM` as an intermediate fact. Conclude with `Submodule.FG.of_le_of_isNoetherian inf_le_left`.

Take `⟨v', hv'M, hv'⟩` from `ih (W ⊓ LinearMap.ker φ) hW' (M ⊓ LinearMap.ker φ') hM' (fun x hx => ⟨hMW x hx.1, hx.2⟩)`. Use `⟨Fin.cons m0 v', fun i => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Simplify using `using hm0`. Simplify using `using (hv'M j).1`.

Take `⟨a0, t', ht', he⟩` from `hgen (φ' m) (Submodule.mem_map_of_mem hm)`. Take `⟨m1, hm1, rfl⟩` from `Submodule.mem_map.1 ht'`. Establish `hr : m - a0 • m0 - n • m1 ∈ M ⊓ LinearMap.ker φ'`. Use `⟨M.sub_mem (M.sub_mem hm (M.smul_mem a0 hm0)) (nsmul_mem hm1 n), ?_⟩` and prove the remaining obligations. Rewrite using `[SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, he]`.

Normalize the expressions using the abelian group laws. Take `⟨a', m'', hm'', he'⟩` from `hv' _ hr`. Use `⟨Fin.cons a0 a', m1 + m'', M.add_mem hm1 hm''.1, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succ]`. Simplify using `only [Fin.cons_zero, Fin.cons_succ]`.

Rewrite `he'` using `[sub_sub, sub_eq_iff_eq_add]`. Rewrite using `[he', smul_add]`. Normalize the expressions using the abelian group laws.
-/
theorem exists_gen [FiniteDimensional K V] (n : ℕ) (hn : n ≠ 0) (k : ℕ) :
    ∀ W : Submodule K V, Module.finrank K W ≤ k → ∀ M : Submodule (𝓞 K) V, M.FG → (∀ x ∈ M, x ∈ W) →
      ∃ v : Fin k → V, (∀ i, v i ∈ M) ∧
        ∀ m ∈ M, ∃ a : Fin k → 𝓞 K, ∃ m' ∈ M, m = ∑ i, a i • v i + n • m' := by
  induction k with
  | zero =>
    intro W hW M _ hMW
    refine ⟨Fin.elim0, fun i => i.elim0, fun m hm => ⟨Fin.elim0, 0, M.zero_mem, ?_⟩⟩
    have hW0 : W = ⊥ := Submodule.finrank_eq_zero.1 (Nat.le_zero.1 hW)
    have hm0 : m = 0 := by
      have h := hMW m hm
      rw [hW0] at h
      exact (Submodule.mem_bot K).1 h
    simp [hm0]
  | succ k ih =>
    intro W hW M hM hMW
    by_cases hM0 : ∀ m ∈ M, m = 0
    · refine ⟨0, fun i => by simp [M.zero_mem], fun m hm => ⟨0, 0, M.zero_mem, by simp [hM0 m hm]⟩⟩
    push Not at hM0
    obtain ⟨w, hwM, hw0⟩ := hM0
    obtain ⟨φ, hφ⟩ : ∃ φ : Module.Dual K V, φ w ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 ((Module.forall_dual_apply_eq_zero_iff K w).1 h)
    let φ' : V →ₗ[𝓞 K] K := φ.restrictScalars (𝓞 K)
    obtain ⟨x0, hx0, hgen⟩ := exists_gen_one n hn (M.map φ') (hM.map φ')
    obtain ⟨m0, hm0, rfl⟩ := Submodule.mem_map.1 hx0
    have hW' : Module.finrank K ↥(W ⊓ LinearMap.ker φ) ≤ k := by
      have hlt : W ⊓ LinearMap.ker φ < W := by
        refine lt_of_le_of_ne inf_le_left (fun h => hφ ?_)
        have hw : w ∈ W ⊓ LinearMap.ker φ := by
          rw [h]
          exact hMW w hwM
        exact LinearMap.mem_ker.1 hw.2
      have := Submodule.finrank_lt_finrank_of_lt hlt
      omega
    have hM' : (M ⊓ LinearMap.ker φ').FG := by
      have := isNoetherian_of_fg_of_noetherian M hM
      exact Submodule.FG.of_le_of_isNoetherian inf_le_left
    obtain ⟨v', hv'M, hv'⟩ := ih (W ⊓ LinearMap.ker φ) hW' (M ⊓ LinearMap.ker φ') hM'
      (fun x hx => ⟨hMW x hx.1, hx.2⟩)
    refine ⟨Fin.cons m0 v', fun i => ?_, fun m hm => ?_⟩
    · refine Fin.cases ?_ (fun j => ?_) i
      · simpa using hm0
      · simpa using (hv'M j).1
    · obtain ⟨a0, t', ht', he⟩ := hgen (φ' m) (Submodule.mem_map_of_mem hm)
      obtain ⟨m1, hm1, rfl⟩ := Submodule.mem_map.1 ht'
      have hr : m - a0 • m0 - n • m1 ∈ M ⊓ LinearMap.ker φ' := by
        refine ⟨M.sub_mem (M.sub_mem hm (M.smul_mem a0 hm0)) (nsmul_mem hm1 n), ?_⟩
        rw [SetLike.mem_coe, LinearMap.mem_ker, map_sub, map_sub, map_smul, map_nsmul, he]
        abel
      obtain ⟨a', m'', hm'', he'⟩ := hv' _ hr
      refine ⟨Fin.cons a0 a', m1 + m'', M.add_mem hm1 hm''.1, ?_⟩
      rw [Fin.sum_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [sub_sub, sub_eq_iff_eq_add] at he'
      rw [he', smul_add]
      abel

def prodGrp (C : AddSubgroup K) (M : AddSubgroup V) : AddSubgroup V :=
  AddSubgroup.closure {y | ∃ t ∈ C, ∃ v ∈ M, t • v = y}

omit [NumberField K] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨t, ht, v, hv, rfl⟩`.
-/
theorem smul_mem_prodGrp {C : AddSubgroup K} {M : AddSubgroup V} {t : K} {v : V} (ht : t ∈ C)
    (hv : v ∈ M) : t • v ∈ prodGrp C M := AddSubgroup.subset_closure ⟨t, ht, v, hv, rfl⟩

/- English proof (translation)
Set `f : (ι → L) →+ (AddSubgroup.pi (Set.univ : Set ι) fun _ => L)` to `{ toFun := fun g => ⟨fun i => (g i : G), fun i _ => (g i).2⟩ map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `hf : Function.Surjective f` using `fun x => ⟨fun i => ⟨(x : ι → G) i, x.2 i (Set.mem_univ i)⟩, rfl⟩`. Establish `hc : ((AddSubgroup.pi Set.univ fun _ => L').addSubgroupOf (AddSubgroup.pi Set.univ fun _ => L)).comap f = AddSubgroup.pi Set.univ fun _ => L'.addSubgroupOf L`. Use extensionality with `g`. Simplify using `[f, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]`.

Simplify using `only [AddSubgroup.relIndex]`. Rewrite using `[← AddSubgroup.index_comap_of_surjective _ hf, hc, AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ]`.
-/
theorem relIndex_pi_const {ι G : Type} [Fintype ι] [AddCommGroup G] (L L' : AddSubgroup G) :
    (AddSubgroup.pi (Set.univ : Set ι) fun _ => L').relIndex (AddSubgroup.pi Set.univ fun _ => L) =
      L'.relIndex L ^ Fintype.card ι := by
  classical
  let f : (ι → L) →+ (AddSubgroup.pi (Set.univ : Set ι) fun _ => L) :=
    { toFun := fun g => ⟨fun i => (g i : G), fun i _ => (g i).2⟩
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have hf : Function.Surjective f := fun x => ⟨fun i => ⟨(x : ι → G) i, x.2 i (Set.mem_univ i)⟩, rfl⟩
  have hc : ((AddSubgroup.pi Set.univ fun _ => L').addSubgroupOf (AddSubgroup.pi Set.univ fun _ => L)).comap f =
      AddSubgroup.pi Set.univ fun _ => L'.addSubgroupOf L := by
    ext g
    simp [f, AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_pi]
  simp only [AddSubgroup.relIndex]
  rw [← AddSubgroup.index_comap_of_surjective _ hf, hc, AddSubgroup.index_pi, Finset.prod_const,
    Finset.card_univ]

/- English proof (translation)
Establish `hCmem : ∀ t ∈ A, C.relIndex A.toAddSubgroup • t ∈ C` using `fun t ht => AddSubgroup.nsmul_relIndex_mem C (show t ∈ A.toAddSubgroup from ht)`. Establish `hMmem : ∀ l ∈ L, M.toAddSubgroup.relIndex L.toAddSubgroup • l ∈ M` using `fun l hl => AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (show l ∈ L.toAddSubgroup from hl)`. Take `⟨v, hvM, hv⟩` from `exists_gen (C.relIndex A.toAddSubgroup) hCA k W hW M hM hMW`. Set `φ : (Fin k → K) →+ V` to `AddMonoidHom.mk' (fun t : Fin k → K => ∑ i, t i • v i) (by intro a b; simp [add_smul, Finset.sum_add_distrib])`. Establish `hφ : ∀ t, φ t = ∑ i, t i • v i` using `fun t => rfl`.

Establish `h2` using `relIndex_le_of_map φ (P₁ := AddSubgroup.pi Set.univ fun _ => A.toAddSubgroup) (Q₁ := AddSubgroup.pi Set.univ fun _ => C) (P := prodGrp A.toAddSubgroup M.toAddSubgroup) (Q := prodGrp C M.toAddSubgroup) ?_ ?_ ?_`. Use `rotate_left`. Use `show AddSubgroup.closure _ ≤ _`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨t, ht, m, hm, rfl⟩`.

Take `⟨a, m', hm', he⟩` from `hv m hm`. Establish `e : t • m = φ (fun i => a i • t) + (C.relIndex A.toAddSubgroup • t) • m'`. Rewrite using `[he, hφ, smul_add, Finset.smul_sum]`. Use `congr 1`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[← algebraMap_smul K (a i) (v i), smul_smul, Algebra.smul_def, mul_comm]`. Rewrite using `[smul_comm t (C.relIndex A.toAddSubgroup) m', smul_assoc]`. Rewrite using `[SetLike.mem_coe, e]`. Use `AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨_, ?_, rfl⟩)) (AddSubgroup.mem_sup_left (smul_mem_prodGrp (hCmem t ht) hm'))` and prove the remaining obligations. Conclude with `(AddSubgroup.mem_pi _).2 fun i _ => A.smul_mem (a i) ht`.

Introduce `c hc`. Rewrite using `[AddSubgroup.mem_comap, hφ]`. Conclude with `AddSubgroup.sum_mem _ fun i _ => smul_mem_prodGrp ((AddSubgroup.mem_pi _).1 hc i (Set.mem_univ _)) (hvM i)`. Rewrite using `[relIndex_pi_const]`. Conclude with `pow_ne_zero _ hCA`.

Take `⟨x, hxA, hx⟩` from `exists_gen_one (M.toAddSubgroup.relIndex L.toAddSubgroup) hi A hA`. Establish `h1` using `relIndex_le_of_map (DistribSMul.toAddMonoidHom V x) (P₁ := L.toAddSubgroup) (Q₁ := M.toAddSubgroup) (P := prodGrp A.toAddSubgroup L.toAddSubgroup) (Q := prodGrp A.toAddSubgroup M.toAddSubgroup) ?_ ?_ hi`. Use `rotate_left`. Use `show AddSubgroup.closure _ ≤ _`. Rewrite using `[AddSubgroup.closure_le]`.

Introduce and unpack `_ ⟨t, ht, l, hl, rfl⟩`. Take `⟨a, t', ht', he⟩` from `hx t ht`. Establish `e : t • l = x • (a • l) + t' • (M.toAddSubgroup.relIndex L.toAddSubgroup • l)`. Rewrite using `[he, add_smul, smul_assoc, smul_comm a x l, smul_assoc, smul_comm _ t' l]`. Rewrite using `[SetLike.mem_coe, e]`.

Conclude with `AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨a • l, L.smul_mem a hl, rfl⟩)) (AddSubgroup.mem_sup_left (smul_mem_prodGrp ht' (hMmem l hl)))`. Introduce `m hm`. Conclude with `smul_mem_prodGrp hxA hm`. Establish `hCM : prodGrp C M.toAddSubgroup ≤ prodGrp A.toAddSubgroup M.toAddSubgroup`. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨t, ht, m, hm, rfl⟩`. Conclude with `⟨t, hC ht, m, hm, rfl⟩`. Establish `hAM : prodGrp A.toAddSubgroup M.toAddSubgroup ≤ prodGrp A.toAddSubgroup L.toAddSubgroup`. Use `AddSubgroup.closure_mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, m, hm, rfl⟩`.

Conclude with `⟨t, ht, m, hML hm, rfl⟩`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ hCM hAM]`. Use `⟨mul_ne_zero h2.1 h1.1, Nat.mul_le_mul (h2.2.trans_eq ?_) h1.2⟩` and prove the remaining obligations. Rewrite using `[relIndex_pi_const, Fintype.card_fin]`.
-/
theorem relIndex_prodGrp_le [FiniteDimensional K V] {k : ℕ} {W : Submodule K V}
    (hW : Module.finrank K W ≤ k) {A : Submodule (𝓞 K) K} (hA : A.FG) {C : AddSubgroup K}
    (hC : C ≤ A.toAddSubgroup) (hCA : C.relIndex A.toAddSubgroup ≠ 0) {L M : Submodule (𝓞 K) V}
    (hM : M.FG) (hMW : ∀ x ∈ M, x ∈ W) (hML : M ≤ L)
    (hi : M.toAddSubgroup.relIndex L.toAddSubgroup ≠ 0) :
    (prodGrp C M.toAddSubgroup).relIndex (prodGrp A.toAddSubgroup L.toAddSubgroup) ≠ 0 ∧
    (prodGrp C M.toAddSubgroup).relIndex (prodGrp A.toAddSubgroup L.toAddSubgroup) ≤
      C.relIndex A.toAddSubgroup ^ k * M.toAddSubgroup.relIndex L.toAddSubgroup := by
  classical
  have hCmem : ∀ t ∈ A, C.relIndex A.toAddSubgroup • t ∈ C := fun t ht =>
    AddSubgroup.nsmul_relIndex_mem C (show t ∈ A.toAddSubgroup from ht)
  have hMmem : ∀ l ∈ L, M.toAddSubgroup.relIndex L.toAddSubgroup • l ∈ M := fun l hl =>
    AddSubgroup.nsmul_relIndex_mem M.toAddSubgroup (show l ∈ L.toAddSubgroup from hl)
  obtain ⟨v, hvM, hv⟩ := exists_gen (C.relIndex A.toAddSubgroup) hCA k W hW M hM hMW
  let φ : (Fin k → K) →+ V := AddMonoidHom.mk' (fun t : Fin k → K => ∑ i, t i • v i)
    (by intro a b; simp [add_smul, Finset.sum_add_distrib])
  have hφ : ∀ t, φ t = ∑ i, t i • v i := fun t => rfl
  have h2 := relIndex_le_of_map φ (P₁ := AddSubgroup.pi Set.univ fun _ => A.toAddSubgroup)
    (Q₁ := AddSubgroup.pi Set.univ fun _ => C) (P := prodGrp A.toAddSubgroup M.toAddSubgroup)
    (Q := prodGrp C M.toAddSubgroup) ?_ ?_ ?_
  rotate_left
  · show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨t, ht, m, hm, rfl⟩
    obtain ⟨a, m', hm', he⟩ := hv m hm
    have e : t • m = φ (fun i => a i • t) + (C.relIndex A.toAddSubgroup • t) • m' := by
      rw [he, hφ, smul_add, Finset.smul_sum]
      congr 1
      · refine Finset.sum_congr rfl fun i _ => ?_
        rw [← algebraMap_smul K (a i) (v i), smul_smul, Algebra.smul_def, mul_comm]
      · rw [smul_comm t (C.relIndex A.toAddSubgroup) m', smul_assoc]
    rw [SetLike.mem_coe, e]
    refine AddSubgroup.add_mem _ (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨_, ?_, rfl⟩))
      (AddSubgroup.mem_sup_left (smul_mem_prodGrp (hCmem t ht) hm'))
    exact (AddSubgroup.mem_pi _).2 fun i _ => A.smul_mem (a i) ht
  · intro c hc
    rw [AddSubgroup.mem_comap, hφ]
    exact AddSubgroup.sum_mem _ fun i _ =>
      smul_mem_prodGrp ((AddSubgroup.mem_pi _).1 hc i (Set.mem_univ _)) (hvM i)
  · rw [relIndex_pi_const]
    exact pow_ne_zero _ hCA
  obtain ⟨x, hxA, hx⟩ := exists_gen_one (M.toAddSubgroup.relIndex L.toAddSubgroup) hi A hA
  have h1 := relIndex_le_of_map (DistribSMul.toAddMonoidHom V x) (P₁ := L.toAddSubgroup)
    (Q₁ := M.toAddSubgroup) (P := prodGrp A.toAddSubgroup L.toAddSubgroup)
    (Q := prodGrp A.toAddSubgroup M.toAddSubgroup) ?_ ?_ hi
  rotate_left
  · show AddSubgroup.closure _ ≤ _
    rw [AddSubgroup.closure_le]
    rintro _ ⟨t, ht, l, hl, rfl⟩
    obtain ⟨a, t', ht', he⟩ := hx t ht
    have e : t • l = x • (a • l) + t' • (M.toAddSubgroup.relIndex L.toAddSubgroup • l) := by
      rw [he, add_smul, smul_assoc, smul_comm a x l, smul_assoc, smul_comm _ t' l]
    rw [SetLike.mem_coe, e]
    exact AddSubgroup.add_mem _
      (AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨a • l, L.smul_mem a hl, rfl⟩))
      (AddSubgroup.mem_sup_left (smul_mem_prodGrp ht' (hMmem l hl)))
  · intro m hm
    exact smul_mem_prodGrp hxA hm
  have hCM : prodGrp C M.toAddSubgroup ≤ prodGrp A.toAddSubgroup M.toAddSubgroup := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨t, ht, m, hm, rfl⟩
    exact ⟨t, hC ht, m, hm, rfl⟩
  have hAM : prodGrp A.toAddSubgroup M.toAddSubgroup ≤ prodGrp A.toAddSubgroup L.toAddSubgroup := by
    refine AddSubgroup.closure_mono ?_
    rintro _ ⟨t, ht, m, hm, rfl⟩
    exact ⟨t, ht, m, hML hm, rfl⟩
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hCM hAM]
  refine ⟨mul_ne_zero h2.1 h1.1, Nat.mul_le_mul (h2.2.trans_eq ?_) h1.2⟩
  rw [relIndex_pi_const, Fintype.card_fin]

end Lattice

section Ideals

variable {K : Type} [Field K] [NumberField K]

/- English proof (translation)
The claim follows from `FractionalIdeal.fg_of_isNoetherianRing le_rfl _`.
-/
theorem ipow_fg (𝔡 : Ideal (𝓞 K)) (n : ℤ) : (ipow 𝔡 n).FG := FractionalIdeal.fg_of_isNoetherianRing le_rfl _

/- English proof (translation)
Establish `h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h`. Establish `e : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (-n) * (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n = 1`. Rewrite using `[← zpow_add₀ h0, neg_add_cancel, zpow_zero]`. Unfold `ipow`. Rewrite using `[← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]`.

Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`.
-/
theorem one_mem_ipow_mul {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (n : ℤ) : (1 : K) ∈ ipow 𝔡 (-n) * ipow 𝔡 n := by
  have h0 : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  have e : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ^ (-n) * (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ n = 1 := by
    rw [← zpow_add₀ h0, neg_add_cancel, zpow_zero]
  unfold ipow
  rw [← FractionalIdeal.coe_mul, e, FractionalIdeal.coe_one]
  exact Submodule.mem_one.2 ⟨1, map_one _⟩

variable [StarRing K]

omit [NumberField K] in

/- English proof (translation)
Take `⟨a, rfl⟩` from `Submodule.mem_one.1 ht`. Use `Submodule.mem_one.2 ⟨⟨star (a : K), ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `(NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom`.
-/
theorem star_mem_one {t : K} (ht : t ∈ (1 : Submodule (𝓞 K) K)) : star t ∈ (1 : Submodule (𝓞 K) K) := by
  obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ht
  refine Submodule.mem_one.2 ⟨⟨star (a : K), ?_⟩, rfl⟩
  exact (NumberField.RingOfIntegers.isIntegral_coe a).map (starRingEnd K).toIntAlgHom
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Introduce `x _`. Establish `h1 : star (x : K) ∈ (1 : Submodule (𝓞 K) K)` using `star_mem_one (Submodule.mem_one.2 ⟨x, rfl⟩)`. Take `⟨y, hy⟩` from `Submodule.mem_one.1 h1`.

Conclude with `⟨y, by simp, hy⟩`. Consider the case `succ m ih`. Introduce `x hx`. Rewrite `hx`, the goal using `[pow_succ]`. Use `Submodule.smul_induction_on hx ?_ ?_` and prove the remaining obligations.

Introduce `a ha b hb`. Take `⟨a', ha', e1⟩` from `ih a ha`. Take `⟨b', hb', e2⟩` from `hs b hb`. Use `⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩` and prove the remaining obligations. Establish `c1 : ((a' * b' : 𝓞 K) : K) = (a' : K) * b'` using `map_mul (algebraMap (𝓞 K) K) a' b'`.

Establish `c2 : ((a * b : 𝓞 K) : K) = (a : K) * b` using `map_mul (algebraMap (𝓞 K) K) a b`. Rewrite using `[smul_eq_mul, c1, c2, e1, e2, star_mul']`. Introduce and unpack `x y ⟨x', hx', e1⟩ ⟨y', hy', e2⟩`. Use `⟨x' + y', add_mem hx' hy', ?_⟩` and prove the remaining obligations. Establish `c1 : ((x' + y' : 𝓞 K) : K) = (x' : K) + y'` using `map_add (algebraMap (𝓞 K) K) x' y'`.

Establish `c2 : ((x + y : 𝓞 K) : K) = (x : K) + y` using `map_add (algebraMap (𝓞 K) K) x y`. Rewrite using `[c1, c2, e1, e2, star_add]`.
-/
private theorem geo_lemma_2 {K : Type} [Field K] [StarRing K] {𝔡 : Ideal (𝓞 K)}
    (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K)) (m : ℕ) :
    ∀ x ∈ 𝔡 ^ m, ∃ y ∈ 𝔡 ^ m, (y : K) = star (x : K) := by
  induction m with
  | zero =>
    intro x _
    have h1 : star (x : K) ∈ (1 : Submodule (𝓞 K) K) := star_mem_one (Submodule.mem_one.2 ⟨x, rfl⟩)
    obtain ⟨y, hy⟩ := Submodule.mem_one.1 h1
    exact ⟨y, by simp, hy⟩
  | succ m ih =>
    intro x hx
    rw [pow_succ] at hx ⊢
    refine Submodule.smul_induction_on hx ?_ ?_
    · intro a ha b hb
      obtain ⟨a', ha', e1⟩ := ih a ha
      obtain ⟨b', hb', e2⟩ := hs b hb
      refine ⟨a' * b', Ideal.mul_mem_mul ha' hb', ?_⟩
      have c1 : ((a' * b' : 𝓞 K) : K) = (a' : K) * b' := map_mul (algebraMap (𝓞 K) K) a' b'
      have c2 : ((a * b : 𝓞 K) : K) = (a : K) * b := map_mul (algebraMap (𝓞 K) K) a b
      rw [smul_eq_mul, c1, c2, e1, e2, star_mul']
    · rintro x y ⟨x', hx', e1⟩ ⟨y', hy', e2⟩
      refine ⟨x' + y', add_mem hx' hy', ?_⟩
      have c1 : ((x' + y' : 𝓞 K) : K) = (x' : K) + y' := map_add (algebraMap (𝓞 K) K) x' y'
      have c2 : ((x + y : 𝓞 K) : K) = (x : K) + y := map_add (algebraMap (𝓞 K) K) x y
      rw [c1, c2, e1, e2, star_add]

/- English proof (translation)
Unfold `ipow at ht ⊢`. Rewrite `ht`, the goal using `[FractionalIdeal.mem_coe]`. Establish `hI : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0` using `FractionalIdeal.coeIdeal_ne_zero.2 h`. Establish `hA : ∀ m : ℕ, ∀ t : K, t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m → star t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m`. Introduce `m t ht`.

Rewrite `ht`, the goal using `[← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal]`. Take `⟨x, hx, rfl⟩` from `ht`. Take `⟨y, hy, e⟩` from `geo_lemma_2 hs m x hx`. Conclude with `⟨y, hy, e⟩`. Establish `hone : ∀ t : K, t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) → star t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K)`.

Introduce `t ht`. Rewrite `ht`, the goal using `[FractionalIdeal.mem_one_iff]`. Take `⟨x, rfl⟩` from `ht`. Use `star_mem_one (K := K) (Submodule.mem_one.2 ⟨x, rfl⟩)` as an intermediate fact. Conclude with `Submodule.mem_one.1 this`.

Take `⟨m, rfl | rfl⟩` from `Int.eq_nat_or_neg n`. Rewrite `ht`, the goal using `[zpow_natCast]`. Conclude with `hA m t ht`. Rewrite `ht`, the goal using `[zpow_neg, zpow_natCast]`. Rewrite `ht`, the goal using `[FractionalIdeal.mem_inv_iff (pow_ne_zero m hI)]`.

Introduce `y hy`. Establish `h1` using `hone _ (ht (star y) (hA m y hy))`. Rewrite `h1` using `[star_mul, star_star, mul_comm]`. Then use the resulting hypothesis.
-/
theorem star_mem_ipow {𝔡 : Ideal (𝓞 K)} (h : 𝔡 ≠ ⊥) (hs : ∀ x ∈ 𝔡, ∃ y ∈ 𝔡, (y : K) = star (x : K))
    (n : ℤ) {t : K} (ht : t ∈ ipow 𝔡 n) : star t ∈ ipow 𝔡 n := by
  unfold ipow at ht ⊢
  rw [FractionalIdeal.mem_coe] at ht ⊢
  have hI : ((𝔡 : FractionalIdeal (𝓞 K)⁰ K)) ≠ 0 := FractionalIdeal.coeIdeal_ne_zero.2 h
  have hA : ∀ m : ℕ, ∀ t : K, t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m →
      star t ∈ (𝔡 : FractionalIdeal (𝓞 K)⁰ K) ^ m := by
    intro m t ht
    rw [← FractionalIdeal.coeIdeal_pow, FractionalIdeal.mem_coeIdeal] at ht ⊢
    obtain ⟨x, hx, rfl⟩ := ht
    obtain ⟨y, hy, e⟩ := geo_lemma_2 hs m x hx
    exact ⟨y, hy, e⟩
  have hone : ∀ t : K, t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) → star t ∈ (1 : FractionalIdeal (𝓞 K)⁰ K) := by
    intro t ht
    rw [FractionalIdeal.mem_one_iff] at ht ⊢
    obtain ⟨x, rfl⟩ := ht
    have := star_mem_one (K := K) (Submodule.mem_one.2 ⟨x, rfl⟩)
    exact Submodule.mem_one.1 this
  obtain ⟨m, rfl | rfl⟩ := Int.eq_nat_or_neg n
  · rw [zpow_natCast] at ht ⊢
    exact hA m t ht
  · rw [zpow_neg, zpow_natCast] at ht ⊢
    rw [FractionalIdeal.mem_inv_iff (pow_ne_zero m hI)] at ht ⊢
    intro y hy
    have h1 := hone _ (ht (star y) (hA m y hy))
    rwa [star_mul, star_star, mul_comm] at h1

end Ideals

section Geometry

variable {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
  [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V]
  {H : HermSpace K V} {r : ℕ} (N : NF H r)

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

/- English proof (translation)
Use `show F.X ⊓ F'.X ≤ F.X ⊔ F'.X ⊔ _`. Conclude with `inf_le_left.trans (le_sup_left.trans le_sup_left)`.
-/
theorem isotropicMeet_le_jointSpan (F F' : FlagD H r) : II F F' ≤ V0 F F' := by
  show F.X ⊓ F'.X ≤ F.X ⊔ F'.X ⊔ _
  exact inf_le_left.trans (le_sup_left.trans le_sup_left)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in

/- English proof (translation)
Take `⟨hR, hfix⟩` from `Subgroup.mem_inf.1 hs`. Establish `hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y`. Establish `h1` using `((GlobalTheory.UnipStab.mem_R N s).1 hR).1`. Unfold `FlagD.InN at h1`. Simplify using `using h1.1`.

Use `show s y - y ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F')`. Rewrite using `[GlobalTheory.HermLat.mem_perp_iff]`. Introduce `x hx`. Establish `hsx : s x = x` using `(GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix x hx`. Rewrite using `[map_sub, LinearMap.sub_apply, ← hiso y x, hsx, sub_self]`.
-/
theorem sub_mem_wSp {s : V ≃ₗ[K] V} (hs : s ∈ N.R1) (y : V) : s y - y ∈ wSp N.F N.F' := by
  obtain ⟨hR, hfix⟩ := Subgroup.mem_inf.1 hs
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  show s y - y ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F')
  rw [GlobalTheory.HermLat.mem_perp_iff]
  intro x hx
  have hsx : s x = x := (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix x hx
  rw [map_sub, LinearMap.sub_apply, ← hiso y x, hsx, sub_self]

omit [NumberField K] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Introduce `y hy`. Rewrite `hy` using `[wSp, GlobalTheory.HermLat.mem_perp_iff]`. Rewrite using `[uPerp, GlobalTheory.HermLat.mem_perp_iff]`. Introduce `x hx`. Conclude with `hy x (show x ∈ F.X ⊔ F'.X ⊔ _ from le_sup_left (a := F.X ⊔ F'.X) hx)`.
-/
theorem wSp_le_uPerp (F F' : FlagD H r) : wSp F F' ≤ uPerp F F' := by
  intro y hy
  rw [wSp, GlobalTheory.HermLat.mem_perp_iff] at hy
  rw [uPerp, GlobalTheory.HermLat.mem_perp_iff]
  intro x hx
  exact hy x (show x ∈ F.X ⊔ F'.X ⊔ _ from le_sup_left (a := F.X ⊔ F'.X) hx)

noncomputable def row (a : Fin r) (s : V ≃ₗ[K] V) : V ⧸ II N.F N.F' :=
  (II N.F N.F').mkQ (s (N.ist a) - N.ist a)

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `hs1 : s ∈ N.R` using `(Subgroup.mem_inf.1 hs).1`. Establish `hw : t (N.ist a) - N.ist a ∈ uPerp N.F N.F'` using `wSp_le_uPerp N.F N.F' (sub_mem_wSp N ht (N.ist a))`. Establish `h2` using `GlobalTheory.UnipStab.sub_mem_II N hs1 hw`. Unfold `row`. Simplify using `only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]`.

Establish `e : (s * t) (N.ist a) = s (t (N.ist a))` using `rfl`. Rewrite using `[e]`. Use `h2 using 1` and compare the differences between its conclusion and the goal. Rewrite using `[map_sub]`. Normalize the expressions using the abelian group laws.
-/
theorem row_mul (a : Fin r) {s t : V ≃ₗ[K] V} (hs : s ∈ N.R1) (ht : t ∈ N.R1) :
    row N a (s * t) = row N a s + row N a t := by
  have hs1 : s ∈ N.R := (Subgroup.mem_inf.1 hs).1
  have hw : t (N.ist a) - N.ist a ∈ uPerp N.F N.F' := wSp_le_uPerp N.F N.F' (sub_mem_wSp N ht (N.ist a))
  have h2 := GlobalTheory.UnipStab.sub_mem_II N hs1 hw
  unfold row
  simp only [Submodule.mkQ_apply, ← Submodule.Quotient.mk_add, Submodule.Quotient.eq]
  have e : (s * t) (N.ist a) = s (t (N.ist a)) := rfl
  rw [e]
  convert h2 using 1
  rw [map_sub]
  abel

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Take `⟨hR, hfix⟩` from `Subgroup.mem_inf.1 hs`. Establish `hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y`. Establish `h1` using `((GlobalTheory.UnipStab.mem_R N s).1 hR).1`. Unfold `FlagD.InN at h1`. Simplify using `using h1.1`.

Take `⟨hF, hF'⟩` from `(GlobalTheory.UnipStab.mem_R N s).1 hR`. Use `Subgroup.mem_inf.2 ⟨hs, (GlobalTheory.UnipStab.mem_fixing N _ s).2 fun u hu => ?_⟩` and prove the remaining obligations. Establish `hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)` using `hu`. Establish `hu3` using `(GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2`. Establish `hX : s u - u ∈ N.F.X` using `GlobalTheory.UnipStab.sub_mem_X hF (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F')) hu2`.

Establish `hX' : s u - u ∈ N.F'.X` using `GlobalTheory.UnipStab.sub_mem_X hF' (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F')) hu2`. Establish `hI : s u - u ∈ II N.F N.F'` using `Submodule.mem_inf.2 ⟨hX, hX'⟩`. Establish `hW0 : s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F')` using `sub_mem_wSp N hs u`. Establish `hdW : s u - u ∈ N.Wt` using `by show s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)`. Rewrite using `[GlobalTheory.HermLat.mem_perp_iff]`.

Establish `hle : V0 N.F N.F' ⊔ N.Ist ≤ LinearMap.ker (H.B (s u - u))`. Use `sup_le (fun x hx => ?_) ?_` and prove the remaining obligations. Rewrite using `[LinearMap.mem_ker]`. Conclude with `(GlobalTheory.HermLat.mem_perp_iff H _ _).1 hW0 x hx`. Rewrite using `[NF.Ist, Submodule.span_le]`.

Introduce and unpack `_ ⟨b, hb, rfl⟩`. Establish `hi : s (N.ist b) - N.ist b ∈ II N.F N.F'`. Use `h b hb` as an intermediate fact. Unfold `row at this`. Rewrite `this` using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Then use the resulting hypothesis.

Establish `hsi : s (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b` using `(GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix _ (isotropicMeet_le_jointSpan N.F N.F' hi)`. Establish `hui : H.B u (s (N.ist b) - N.ist b) = 0` using `hu3 _ (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))`. Establish `e2 : H.B (s u) (N.ist b) = H.B u (N.ist b)`. Establish `e1 : N.ist b = s (N.ist b) - (s (N.ist b) - N.ist b)` using `by abel`. Establish `e3 : H.B (s u) (s (N.ist b) - N.ist b) = 0`.

Rewrite using `[← hsi, hiso, hui]`. Combine the equalities or inequalities in the displayed calculation. Use `show H.B (s u - u) (N.ist b) = 0`. Rewrite using `[map_sub, LinearMap.sub_apply, e2, sub_self]`. Conclude with `fun x hx => hle hx`.

Establish `hl'` using `hl`. Unfold `IsLift at hl'`. Establish `hmem : s u - u ∈ N.Wt ⊓ II N.F N.F'` using `Submodule.mem_inf.2 ⟨hdW, hI⟩`. Rewrite `hmem` using `[hl'.2.1]`. Conclude with `sub_eq_zero.1 ((Submodule.mem_bot K).1 hmem)`.
-/
theorem mem_ZI_of_row (hl : IsLift N.F N.F' N.Wt) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.R1) (h : ∀ a : Fin r, N.j ≤ a.val → row N a s = 0) : s ∈ N.ZI := by
  obtain ⟨hR, hfix⟩ := Subgroup.mem_inf.1 hs
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  obtain ⟨hF, hF'⟩ := (GlobalTheory.UnipStab.mem_R N s).1 hR
  refine Subgroup.mem_inf.2 ⟨hs, (GlobalTheory.UnipStab.mem_fixing N _ s).2 fun u hu => ?_⟩
  have hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hu
  have hu3 := (GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2
  have hX : s u - u ∈ N.F.X :=
    GlobalTheory.UnipStab.sub_mem_X hF (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F')) hu2
  have hX' : s u - u ∈ N.F'.X :=
    GlobalTheory.UnipStab.sub_mem_X hF' (le_sup_of_le_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F')) hu2
  have hI : s u - u ∈ II N.F N.F' := Submodule.mem_inf.2 ⟨hX, hX'⟩
  have hW0 : s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F') := sub_mem_wSp N hs u
  have hdW : s u - u ∈ N.Wt := by
    show s u - u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)
    rw [GlobalTheory.HermLat.mem_perp_iff]
    have hle : V0 N.F N.F' ⊔ N.Ist ≤ LinearMap.ker (H.B (s u - u)) := by
      refine sup_le (fun x hx => ?_) ?_
      · rw [LinearMap.mem_ker]
        exact (GlobalTheory.HermLat.mem_perp_iff H _ _).1 hW0 x hx
      · rw [NF.Ist, Submodule.span_le]
        rintro _ ⟨b, hb, rfl⟩
        have hi : s (N.ist b) - N.ist b ∈ II N.F N.F' := by
          have := h b hb
          unfold row at this
          rwa [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero] at this
        have hsi : s (s (N.ist b) - N.ist b) = s (N.ist b) - N.ist b :=
          (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfix _ (isotropicMeet_le_jointSpan N.F N.F' hi)
        have hui : H.B u (s (N.ist b) - N.ist b) = 0 :=
          hu3 _ (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))
        have e2 : H.B (s u) (N.ist b) = H.B u (N.ist b) := by
          have e1 : N.ist b = s (N.ist b) - (s (N.ist b) - N.ist b) := by abel
          have e3 : H.B (s u) (s (N.ist b) - N.ist b) = 0 := by
            rw [← hsi, hiso, hui]
          calc H.B (s u) (N.ist b) = H.B (s u) (s (N.ist b) - (s (N.ist b) - N.ist b)) := by rw [← e1]
            _ = H.B u (N.ist b) := by rw [map_sub, e3, sub_zero, hiso]
        show H.B (s u - u) (N.ist b) = 0
        rw [map_sub, LinearMap.sub_apply, e2, sub_self]
    exact fun x hx => hle hx
  have hl' := hl
  unfold IsLift at hl'
  have hmem : s u - u ∈ N.Wt ⊓ II N.F N.F' := Submodule.mem_inf.2 ⟨hdW, hI⟩
  rw [hl'.2.1] at hmem
  exact sub_eq_zero.1 ((Submodule.mem_bot K).1 hmem)
/- English proof (translation)
Take `⟨hR1, hfW⟩` from `Subgroup.mem_inf.1 hs`. Take `⟨hR, -⟩` from `Subgroup.mem_inf.1 hR1`. Establish `hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y`. Establish `h1` using `((GlobalTheory.UnipStab.mem_R N s).1 hR).1`. Unfold `FlagD.InN at h1`.

Simplify using `using h1.1`. Establish `hd` using `sub_mem_wSp N hR1 y`. Rewrite `hd` using `[hw, Submodule.mem_sup]`. Take `⟨w, hwW, i, hiI, hwi⟩` from `hd`. Establish `hIV : ∀ i ∈ II N.F N.F', ∀ u ∈ N.Wt, H.B i u = 0`.

Introduce `i hi u hu`. Establish `hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)` using `hu`. Establish `hu'` using `(GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2 i (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))`. Rewrite using `[← H.herm, hu', star_zero]`. Establish `hwP : w ∈ N.Pi` using `by show w ∈ GlobalTheory.HermLat.perp H N.Wt`.

Rewrite using `[GlobalTheory.HermLat.mem_perp_iff]`. Introduce `u hu`. Establish `hsu : s u = u` using `(GlobalTheory.UnipStab.mem_fixing N _ s).1 hfW u hu`. Establish `e1 : H.B (s y - y) u = 0`. Rewrite using `[map_sub, LinearMap.sub_apply, ← hiso y u, hsu, sub_self]`.

Establish `e2 : w = (s y - y) - i` using `by rw [← hwi]; abel`. Rewrite using `[e2, map_sub, LinearMap.sub_apply, e1, hIV i hiI u hu, sub_self]`. Establish `hw0 : w = 0` using `Submodule.disjoint_def.1 hc.disjoint w hwW hwP`. Rewrite using `[← hwi, hw0, zero_add]`. Conclude with `hiI`.
-/
private theorem geo_lemma {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [FiniteDimensional K V] {H : HermSpace K V} {r : ℕ} (N : NF H r) (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.ZI) (y : V) : s y - y ∈ II N.F N.F' := by
  obtain ⟨hR1, hfW⟩ := Subgroup.mem_inf.1 hs
  obtain ⟨hR, -⟩ := Subgroup.mem_inf.1 hR1
  have hiso : ∀ x y : V, H.B (s x) (s y) = H.B x y := by
    have h1 := ((GlobalTheory.UnipStab.mem_R N s).1 hR).1
    unfold FlagD.InN at h1
    simpa using h1.1
  have hd := sub_mem_wSp N hR1 y
  rw [hw, Submodule.mem_sup] at hd
  obtain ⟨w, hwW, i, hiI, hwi⟩ := hd
  have hIV : ∀ i ∈ II N.F N.F', ∀ u ∈ N.Wt, H.B i u = 0 := by
    intro i hi u hu
    have hu2 : u ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hu
    have hu' := (GlobalTheory.HermLat.mem_perp_iff H _ u).1 hu2 i (Submodule.mem_sup_left (isotropicMeet_le_jointSpan N.F N.F' hi))
    rw [← H.herm, hu', star_zero]
  have hwP : w ∈ N.Pi := by
    show w ∈ GlobalTheory.HermLat.perp H N.Wt
    rw [GlobalTheory.HermLat.mem_perp_iff]
    intro u hu
    have hsu : s u = u := (GlobalTheory.UnipStab.mem_fixing N _ s).1 hfW u hu
    have e1 : H.B (s y - y) u = 0 := by
      rw [map_sub, LinearMap.sub_apply, ← hiso y u, hsu, sub_self]
    have e2 : w = (s y - y) - i := by rw [← hwi]; abel
    rw [e2, map_sub, LinearMap.sub_apply, e1, hIV i hiI u hu, sub_self]
  have hw0 : w = 0 := Submodule.disjoint_def.1 hc.disjoint w hwW hwP
  rw [← hwi, hw0, zero_add]
  exact hiI

omit [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Unfold `row`. Rewrite using `[Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]`. Conclude with `geo_lemma N hc hw hs (N.ist a)`.
-/
theorem row_eq_zero (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    {s : V ≃ₗ[K] V} (hs : s ∈ N.ZI) (a : Fin r) : row N a s = 0 := by
  unfold row
  rw [Submodule.mkQ_apply, Submodule.Quotient.mk_eq_zero]
  exact geo_lemma N hc hw hs (N.ist a)
/- English proof (translation)
Unfold `NF.P0 line`. Use `sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_) (iSup₂_le fun a ha => ?_)` and prove the remaining obligations. Conclude with `Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h1 a t ht`. Conclude with `Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h2 a ha t ht`. Conclude with `Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h3 t ht`.

Conclude with `Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h4 a ha t ht`.
-/
private theorem geo_lemma_3 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V]
    [Module K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ} (N : NF H r)
    (M : Submodule (𝓞 K) V)
    (h1 : ∀ a : Fin r, ∀ t ∈ N.aa a, t • N.F.e a.castSucc ∈ M)
    (h2 : ∀ a : Fin r, a.val < N.j → ∀ t ∈ N.aa a, t • N.F'.e a.castSucc ∈ M)
    (h3 : ∀ t ∈ (1 : Submodule (𝓞 K) K), t • N.F.z ∈ M)
    (h4 : ∀ a : Fin r, N.j ≤ a.val → ∀ t ∈ ipow N.𝔡 ((r : ℤ) - a.val), t • N.ist a ∈ M) :
    N.P0 ≤ M := by
  unfold NF.P0 line
  refine sup_le (sup_le (sup_le (iSup_le fun a => ?_) (iSup₂_le fun a ha => ?_)) ?_)
    (iSup₂_le fun a ha => ?_)
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h1 a t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h2 a ha t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h3 t ht
  · exact Submodule.map_le_iff_le_comap.2 fun t ht => by simpa using h4 a ha t ht

/- English proof (translation)
Establish `huW : u ∈ wSp N.F N.F'` using `hu'`. Use `show u ∈ (rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X)) ⊓ rs (𝓞 K) (wSp N.F N.F')`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨wSp_le_uPerp N.F N.F' huW, ?_⟩, hu'⟩` and prove the remaining obligations. Unfold `NF.Ref at hu`. Take `⟨p, hp, l, hl, rfl⟩` from `Submodule.mem_sup.1 hu`.

Take `⟨hlL, hlWn⟩` from `Submodule.mem_inf.1 hl`. Establish `hlL2 : l ∈ rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X)` using `hlL`. Establish `hlL' : l ∈ Λ ⊔ rs (𝓞 K) N.F.X` using `(Submodule.mem_inf.1 hlL2).2`. Establish `hlWn' : l ∈ N.Wn` using `hlWn`. Rewrite `hlWn'` using `[hn, Submodule.mem_sup]`.

Take `⟨w2, hw2, y2, hy2, hl2⟩` from `hlWn'`. Take `⟨c, rfl⟩` from `Submodule.mem_span_singleton.1 hy2`. Establish `huW'` using `huW`. Rewrite `huW'` using `[hw, Submodule.mem_sup]`. Take `⟨w1, hw1, i, hi, hu1⟩` from `huW'`.

Establish `hz0 : N.F.z ∈ V0 N.F N.F'` using `Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left N.F N.F'`. Establish `hPi : N.P0 ≤ rs (𝓞 K) N.Pi`. Apply `geo_lemma_3 N` to reduce the goal to its premises. Introduce `a t _ show t • _ ∈ N.Pi`. Rewrite using `[hP]`.

Conclude with `Submodule.smul_mem _ t (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)))`. Introduce `a _ t _ show t • _ ∈ N.Pi`. Rewrite using `[hP]`. Conclude with `Submodule.smul_mem _ t (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)))`. Introduce `t _ show t • _ ∈ N.Pi`.

Rewrite using `[hP]`. Conclude with `Submodule.smul_mem _ t (Submodule.mem_sup_left hz0)`. Introduce `a ha t _ show t • _ ∈ N.Pi`. Rewrite using `[hP]`. Conclude with `Submodule.smul_mem _ t (Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩))`.

Establish `hpPi : p ∈ N.Pi` using `hPi hp`. Establish `hpe : p = (w1 - w2) + (i - c • N.F.z)`. Establish `: p = (w1 + i) - (w2 + c • N.F.z)` using `by rw [hu1, hl2]; abel`. Rewrite using `[this]`. Normalize the expressions using the abelian group laws.

Establish `hiV0 : i - c • N.F.z ∈ V0 N.F N.F'` using `sub_mem (isotropicMeet_le_jointSpan N.F N.F' hi) (Submodule.smul_mem _ c hz0)`. Establish `hiPi : i - c • N.F.z ∈ N.Pi` using `by rw [hP]; exact Submodule.mem_sup_left hiV0`. Establish `hwPi : w1 - w2 ∈ N.Pi`. Establish `: w1 - w2 = p - (i - c • N.F.z)` using `by rw [hpe]; abel`. Rewrite using `[this]`.

Conclude with `sub_mem hpPi hiPi`. Establish `hw0 : w1 - w2 = 0` using `Submodule.disjoint_def.1 hc.disjoint _ (sub_mem hw1 hw2) hwPi`. Establish `hp2 : p = i - c • N.F.z` using `by rw [hpe, hw0, zero_add]`. Establish `hzz : N.F'.z = N.c • N.F.z` using `N.same (Fin.last r) (by simp [N.j_le])`. Establish `hc0 : star N.c ≠ 0`.

Introduce `h0`. Use `N.c_norm` as an intermediate fact. Rewrite `this` using `[h0, mul_zero]`. Conclude with `zero_ne_one this`. Establish `hB' : ∀ a : Fin r, H.B (N.F'.e a.castSucc) N.F.z = 0`.

Introduce `a`. Establish `h0` using `Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)`. Rewrite `h0` using `[hzz, map_smulₛₗ, starRingEnd_apply, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h0).resolve_left hc0`. Set `φ : V →ₗ[𝓞 K] K` to `(H.B.flip N.F.z).restrictScalars (𝓞 K)`.

Establish `hφ : ∀ v, φ v = H.B v N.F.z` using `fun v => rfl`. Establish `hP0 : N.P0 ≤ Submodule.comap φ (Submodule.span (𝓞 K) {-N.F.T})`. Apply `geo_lemma_3 N` to reduce the goal to its premises. Introduce `a t _`. Rewrite using `[Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a), mul_zero]`.

Conclude with `Submodule.zero_mem _`. Introduce `a _ t _`. Rewrite using `[Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, hB' a, mul_zero]`. Conclude with `Submodule.zero_mem _`. Introduce `t ht`.

Take `⟨γ, rfl⟩` from `Submodule.mem_one.1 ht`. Rewrite using `[Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]`. Conclude with `Submodule.mem_span_singleton.2 ⟨γ, by rw [Algebra.smul_def]⟩`. Introduce `a ha t _`. Rewrite using `[Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, ← H.herm, N.normalForm_dual_orthogonal_last a ha, star_zero, mul_zero]`.

Conclude with `Submodule.zero_mem _`. Establish `hT : N.F.T ≠ 0` using `N.F.hT`. Take `⟨γ, hγ⟩` from `Submodule.mem_span_singleton.1 (hP0 hp)`. Establish `hiX : i ∈ N.F.X` using `(Submodule.mem_inf.1 hi).1`. Establish `e1 : H.B p N.F.z = c * N.F.T`.

Rewrite using `[hp2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul, Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F hiX, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hγ` using `[hφ, e1, Algebra.smul_def]`. Establish `hcγ : c = algebraMap (𝓞 K) K (-γ)`. Rewrite using `[map_neg]`.

Apply `mul_right_cancel₀ hT` to reduce the goal to its premises. Rewrite using `[← hγ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hcz : c • N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X`. Rewrite using `[hcγ, algebraMap_smul]`.

Conclude with `Submodule.smul_mem _ _ hz`. Rewrite using `[hp2]`. Conclude with `add_mem (sub_mem (Submodule.mem_sup_right hiX) hcz) hlL'`.
-/
theorem mem_innerLattice_of_referenceLattice_trace (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hP : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    {Λ : Submodule (𝓞 K) V} (hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X) {u : V}
    (hu : u ∈ N.Ref (latL N.F N.F' Λ)) (hu' : u ∈ wSp N.F N.F') : u ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
  have huW : u ∈ wSp N.F N.F' := hu'
  show u ∈ (rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X)) ⊓ rs (𝓞 K) (wSp N.F N.F')
  refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨wSp_le_uPerp N.F N.F' huW, ?_⟩, hu'⟩
  unfold NF.Ref at hu
  obtain ⟨p, hp, l, hl, rfl⟩ := Submodule.mem_sup.1 hu
  obtain ⟨hlL, hlWn⟩ := Submodule.mem_inf.1 hl
  have hlL2 : l ∈ rs (𝓞 K) (uPerp N.F N.F') ⊓ (Λ ⊔ rs (𝓞 K) N.F.X) := hlL
  have hlL' : l ∈ Λ ⊔ rs (𝓞 K) N.F.X := (Submodule.mem_inf.1 hlL2).2
  have hlWn' : l ∈ N.Wn := hlWn
  rw [hn, Submodule.mem_sup] at hlWn'
  obtain ⟨w2, hw2, y2, hy2, hl2⟩ := hlWn'
  obtain ⟨c, rfl⟩ := Submodule.mem_span_singleton.1 hy2
  have huW' := huW
  rw [hw, Submodule.mem_sup] at huW'
  obtain ⟨w1, hw1, i, hi, hu1⟩ := huW'
  have hz0 : N.F.z ∈ V0 N.F N.F' := Formalism.HermitianLatticeCounting.P.lastVector_mem_jointSpan_left N.F N.F'
  have hPi : N.P0 ≤ rs (𝓞 K) N.Pi := by
    apply geo_lemma_3 N
    · intro a t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t
        (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)))
    · intro a _ t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t
        (Submodule.mem_sup_left (Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_right N.F N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)))
    · intro t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t (Submodule.mem_sup_left hz0)
    · intro a ha t _
      show t • _ ∈ N.Pi
      rw [hP]
      exact Submodule.smul_mem _ t (Submodule.mem_sup_right (Submodule.subset_span ⟨a, ha, rfl⟩))
  have hpPi : p ∈ N.Pi := hPi hp
  have hpe : p = (w1 - w2) + (i - c • N.F.z) := by
    have : p = (w1 + i) - (w2 + c • N.F.z) := by rw [hu1, hl2]; abel
    rw [this]; abel
  have hiV0 : i - c • N.F.z ∈ V0 N.F N.F' :=
    sub_mem (isotropicMeet_le_jointSpan N.F N.F' hi) (Submodule.smul_mem _ c hz0)
  have hiPi : i - c • N.F.z ∈ N.Pi := by rw [hP]; exact Submodule.mem_sup_left hiV0
  have hwPi : w1 - w2 ∈ N.Pi := by
    have : w1 - w2 = p - (i - c • N.F.z) := by rw [hpe]; abel
    rw [this]; exact sub_mem hpPi hiPi
  have hw0 : w1 - w2 = 0 := Submodule.disjoint_def.1 hc.disjoint _ (sub_mem hw1 hw2) hwPi
  have hp2 : p = i - c • N.F.z := by rw [hpe, hw0, zero_add]
  have hzz : N.F'.z = N.c • N.F.z := N.same (Fin.last r) (by simp [N.j_le])
  have hc0 : star N.c ≠ 0 := by
    intro h0
    have := N.c_norm
    rw [h0, mul_zero] at this
    exact zero_ne_one this
  have hB' : ∀ a : Fin r, H.B (N.F'.e a.castSucc) N.F.z = 0 := by
    intro a
    have h0 := Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F' (Formalism.HermitianLatticeCounting.P.e_mem_X N.F' a)
    rw [hzz, map_smulₛₗ, starRingEnd_apply, smul_eq_mul] at h0
    exact (mul_eq_zero.1 h0).resolve_left hc0
  let φ : V →ₗ[𝓞 K] K := (H.B.flip N.F.z).restrictScalars (𝓞 K)
  have hφ : ∀ v, φ v = H.B v N.F.z := fun v => rfl
  have hP0 : N.P0 ≤ Submodule.comap φ (Submodule.span (𝓞 K) {-N.F.T}) := by
    apply geo_lemma_3 N
    · intro a t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul,
        Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a), mul_zero]
      exact Submodule.zero_mem _
    · intro a _ t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, hB' a, mul_zero]
      exact Submodule.zero_mem _
    · intro t ht
      obtain ⟨γ, rfl⟩ := Submodule.mem_one.1 ht
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
      exact Submodule.mem_span_singleton.2 ⟨γ, by rw [Algebra.smul_def]⟩
    · intro a ha t _
      rw [Submodule.mem_comap, hφ, map_smul, LinearMap.smul_apply, smul_eq_mul, ← H.herm,
        N.normalForm_dual_orthogonal_last a ha, star_zero, mul_zero]
      exact Submodule.zero_mem _
  have hT : N.F.T ≠ 0 := N.F.hT
  obtain ⟨γ, hγ⟩ := Submodule.mem_span_singleton.1 (hP0 hp)
  have hiX : i ∈ N.F.X := (Submodule.mem_inf.1 hi).1
  have e1 : H.B p N.F.z = c * N.F.T := by
    rw [hp2, map_sub, LinearMap.sub_apply, map_smul, LinearMap.smul_apply, smul_eq_mul,
      Formalism.HermitianLatticeCounting.P.pairing_isotropicSpan_lastVector N.F hiX, Formalism.HermitianLatticeCounting.P.pairing_lastVector_lastVector]
    ring
  rw [hφ, e1, Algebra.smul_def] at hγ
  have hcγ : c = algebraMap (𝓞 K) K (-γ) := by
    rw [map_neg]
    apply mul_right_cancel₀ hT
    rw [← hγ]
    ring
  have hcz : c • N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X := by
    rw [hcγ, algebraMap_smul]
    exact Submodule.smul_mem _ _ hz
  rw [hp2]
  exact add_mem (sub_mem (Submodule.mem_sup_right hiX) hcz) hlL'

/- English proof (translation)
Take `⟨u, hu_eq⟩ : ∃ u : V, u = -v` from `⟨_, rfl⟩`. Establish `hu : u ∈ Λ` using `by rw [hu_eq]; exact Λ.neg_mem hv`. Establish `hII : x ∈ N.F.X ⊓ N.F'.X` using `hxI`. Establish `hX : x ∈ N.F.X` using `(Submodule.mem_inf.1 hII).1`. Establish `hxx : H.B x x = 0` using `Formalism.HermitianLatticeCounting.P.X_iso N.F hX hX`.

Establish `hV0x : x ∈ V0 N.F N.F'` using `Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' hX`. Establish `hvW' : v ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist)` using `hvW`. Establish `hvy : ∀ y ∈ V0 N.F N.F', H.B v y = 0` using `fun y hy => (GlobalTheory.HermLat.mem_perp_iff H _ v).1 hvW' y (Submodule.mem_sup_left hy)`. Establish `hyv : ∀ y ∈ V0 N.F N.F', H.B y v = 0` using `fun y hy => by`. Rewrite using `[← H.herm v y, hvy y hy, star_zero]`.

Establish `hyu : ∀ y ∈ V0 N.F N.F', H.B y u = 0` using `fun y hy => by`. Rewrite using `[hu_eq, map_neg, hyv y hy, neg_zero]`. Establish `hxu : H.B x u = 0` using `hyu x hV0x`. Establish `hsa : star (H.B u u) = H.B u u` using `H.herm u u`. Take `⟨b, hb⟩` from `Submodule.mem_one.1 (hΛ u hu u hu)`.

Take `⟨c, hc_eq⟩ : ∃ c : K, c = -((w₀ : K) * H.B u u)` from `⟨_, rfl⟩`. Establish `hc : c + star c = -H.B u u`. Rewrite using `[hc_eq]`. Simplify using `only [star_neg, star_mul', hsa]`. Take the linear combination `(-H.B u u) * hw₀`.

Establish `hcint : c ∈ (1 : Submodule (𝓞 K) K)`. Rewrite using `[hc_eq]`. Conclude with `Submodule.mem_one.2 ⟨-(w₀ * b), by rw [map_neg, map_mul, hb]⟩`. Establish `hscint : star c ∈ (1 : Submodule (𝓞 K) K)`. Establish `e : star c = -c - H.B u u` using `by linear_combination hc`.

Rewrite using `[e]`. Conclude with `Submodule.sub_mem _ (Submodule.neg_mem _ hcint) (hΛ u hu u hu)`. Establish `hsm : ∀ t ∈ (1 : Submodule (𝓞 K) K), ∀ z ∈ Λ, t • z ∈ Λ`. Introduce `t ht z hz`. Take `⟨a, rfl⟩` from `Submodule.mem_one.1 ht`.

Rewrite using `[algebraMap_smul]`. Conclude with `Λ.smul_mem a hz`. Establish `hint : ∀ (U : V) (C : K), U ∈ Λ → C ∈ (1 : Submodule (𝓞 K) K) → ∀ z ∈ Λ, Formalism.HermitianLatticeCounting.S6.eich H x U C z ∈ Λ`. Introduce `U C hU hC z hz`. Rewrite using `[Formalism.HermitianLatticeCounting.P.eich_apply]`.

Conclude with `Λ.add_mem (Λ.add_mem hz (Λ.sub_mem (hsm _ (hΛ z hz U hU) x hx) (hsm _ (hΛ z hz x hx) U hU))) (hsm C hC _ (hsm _ (hΛ z hz x hx) x hx))`. Apply the tactic sequence `obtain ⟨-, hleft, hright⟩ := Formalism.HermitianLatticeCounting.P.eichlerMapIsometry K V H x u c hxx hxu hc`. Set `s : V ≃ₗ[K] V` to `LinearEquiv.ofLinear (Formalism.HermitianLatticeCounting.S6.eich H x u c) (Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c)) (LinearMap.ext fun y => hright y) (LinearMap.ext fun y => hleft y)`. Apply the tactic sequence `have hgood := Formalism.HermitianLatticeCounting.P.eich_good Formalism.HermitianLatticeCounting.P.eichlerMapIsometry N.F N.F' hxI hyu hc`. Establish `hinN` using `Formalism.HermitianLatticeCounting.P.GoodMap.inN N.F N.F' hgood`.

Establish `hsR : s ∈ N.R` using `(GlobalTheory.UnipStab.mem_R N s).2 ⟨hinN.1, hinN.2⟩`. Establish `hsfix : s ∈ N.fixing (V0 N.F N.F')` using `(GlobalTheory.UnipStab.mem_fixing N _ s).2 fun y hy => hgood.2.2.1 y hy`. Establish `hstab : s • Λ = Λ`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `y hy`.

Take `⟨z, hz, rfl⟩` from `(Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy`. Conclude with `hint u c hu hcint z hz`. Introduce `y hy`. Conclude with `(Submodule.mem_smul_pointwise_iff_exists _ _ _).2 ⟨Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c) y, hint (-u) (star c) (Λ.neg_mem hu) hscint y hy, hright y⟩`. Establish `hGam : s ∈ N.Gam Λ` using `by show s ∈ N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ`.

Conclude with `Subgroup.mem_inf.2 ⟨hsR, MulAction.mem_stabilizer_iff.2 hstab⟩`. Establish `hR1 : s ∈ N.R1` using `by show s ∈ N.R ⊓ N.fixing (V0 N.F N.F')`. Conclude with `Subgroup.mem_inf.2 ⟨hsR, hsfix⟩`. Use `⟨s, Subgroup.mem_inf.2 ⟨hGam, hR1⟩, fun a => ?_⟩` and prove the remaining obligations. Establish `h0' : (Submodule.Quotient.mk x : V ⧸ II N.F N.F') = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hxI`.

Establish `e : s (N.ist a) - N.ist a = (H.B (N.ist a) u • x - H.B (N.ist a) x • u) + c • H.B (N.ist a) x • x` using `by show Formalism.HermitianLatticeCounting.S6.eich H x u c (N.ist a) - N.ist a = _`. Rewrite using `[Formalism.HermitianLatticeCounting.P.eich_apply]`. Normalize the expressions using the abelian group laws. Use `show (II N.F N.F').mkQ (s (N.ist a) - N.ist a) = _`. Rewrite using `[e, hu_eq]`.

Simplify using `[h0']`.
-/
theorem exists_eichler {w₀ : 𝓞 K} (hw₀ : (w₀ : K) + star (w₀ : K) = 1) {Λ : Submodule (𝓞 K) V}
    (hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)) {x v : V} (hx : x ∈ Λ)
    (hxI : x ∈ II N.F N.F') (hv : v ∈ Λ) (hvW : v ∈ N.Wt) :
    ∃ s ∈ N.Gam Λ ⊓ N.R1, ∀ a, row N a s = H.B (N.ist a) x • (II N.F N.F').mkQ v := by
  obtain ⟨u, hu_eq⟩ : ∃ u : V, u = -v := ⟨_, rfl⟩
  have hu : u ∈ Λ := by rw [hu_eq]; exact Λ.neg_mem hv
  have hII : x ∈ N.F.X ⊓ N.F'.X := hxI
  have hX : x ∈ N.F.X := (Submodule.mem_inf.1 hII).1
  have hxx : H.B x x = 0 := Formalism.HermitianLatticeCounting.P.X_iso N.F hX hX
  have hV0x : x ∈ V0 N.F N.F' := Formalism.HermitianLatticeCounting.P.isotropicSpan_le_jointSpan_left N.F N.F' hX
  have hvW' : v ∈ GlobalTheory.HermLat.perp H (V0 N.F N.F' ⊔ N.Ist) := hvW
  have hvy : ∀ y ∈ V0 N.F N.F', H.B v y = 0 := fun y hy =>
    (GlobalTheory.HermLat.mem_perp_iff H _ v).1 hvW' y (Submodule.mem_sup_left hy)
  have hyv : ∀ y ∈ V0 N.F N.F', H.B y v = 0 := fun y hy => by
    rw [← H.herm v y, hvy y hy, star_zero]
  have hyu : ∀ y ∈ V0 N.F N.F', H.B y u = 0 := fun y hy => by
    rw [hu_eq, map_neg, hyv y hy, neg_zero]
  have hxu : H.B x u = 0 := hyu x hV0x
  have hsa : star (H.B u u) = H.B u u := H.herm u u
  obtain ⟨b, hb⟩ := Submodule.mem_one.1 (hΛ u hu u hu)
  obtain ⟨c, hc_eq⟩ : ∃ c : K, c = -((w₀ : K) * H.B u u) := ⟨_, rfl⟩
  have hc : c + star c = -H.B u u := by
    rw [hc_eq]
    simp only [star_neg, star_mul', hsa]
    linear_combination (-H.B u u) * hw₀
  have hcint : c ∈ (1 : Submodule (𝓞 K) K) := by
    rw [hc_eq]
    exact Submodule.mem_one.2 ⟨-(w₀ * b), by rw [map_neg, map_mul, hb]⟩
  have hscint : star c ∈ (1 : Submodule (𝓞 K) K) := by
    have e : star c = -c - H.B u u := by linear_combination hc
    rw [e]
    exact Submodule.sub_mem _ (Submodule.neg_mem _ hcint) (hΛ u hu u hu)
  have hsm : ∀ t ∈ (1 : Submodule (𝓞 K) K), ∀ z ∈ Λ, t • z ∈ Λ := by
    intro t ht z hz
    obtain ⟨a, rfl⟩ := Submodule.mem_one.1 ht
    rw [algebraMap_smul]
    exact Λ.smul_mem a hz
  have hint : ∀ (U : V) (C : K), U ∈ Λ → C ∈ (1 : Submodule (𝓞 K) K) → ∀ z ∈ Λ,
      Formalism.HermitianLatticeCounting.S6.eich H x U C z ∈ Λ := by
    intro U C hU hC z hz
    rw [Formalism.HermitianLatticeCounting.P.eich_apply]
    exact Λ.add_mem (Λ.add_mem hz (Λ.sub_mem (hsm _ (hΛ z hz U hU) x hx) (hsm _ (hΛ z hz x hx) U hU)))
      (hsm C hC _ (hsm _ (hΛ z hz x hx) x hx))
  obtain ⟨-, hleft, hright⟩ := Formalism.HermitianLatticeCounting.P.eichlerMapIsometry K V H x u c hxx hxu hc
  let s : V ≃ₗ[K] V := LinearEquiv.ofLinear (Formalism.HermitianLatticeCounting.S6.eich H x u c)
    (Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c)) (LinearMap.ext fun y => hright y) (LinearMap.ext fun y => hleft y)
  have hgood := Formalism.HermitianLatticeCounting.P.eich_good Formalism.HermitianLatticeCounting.P.eichlerMapIsometry N.F N.F' hxI hyu hc
  have hinN := Formalism.HermitianLatticeCounting.P.GoodMap.inN N.F N.F' hgood
  have hsR : s ∈ N.R := (GlobalTheory.UnipStab.mem_R N s).2 ⟨hinN.1, hinN.2⟩
  have hsfix : s ∈ N.fixing (V0 N.F N.F') := (GlobalTheory.UnipStab.mem_fixing N _ s).2 fun y hy => hgood.2.2.1 y hy
  have hstab : s • Λ = Λ := by
    apply le_antisymm
    · intro y hy
      obtain ⟨z, hz, rfl⟩ := (Submodule.mem_smul_pointwise_iff_exists _ _ _).1 hy
      exact hint u c hu hcint z hz
    · intro y hy
      exact (Submodule.mem_smul_pointwise_iff_exists _ _ _).2
        ⟨Formalism.HermitianLatticeCounting.S6.eich H x (-u) (star c) y, hint (-u) (star c) (Λ.neg_mem hu) hscint y hy, hright y⟩
  have hGam : s ∈ N.Gam Λ := by
    show s ∈ N.R ⊓ MulAction.stabilizer (V ≃ₗ[K] V) Λ
    exact Subgroup.mem_inf.2 ⟨hsR, MulAction.mem_stabilizer_iff.2 hstab⟩
  have hR1 : s ∈ N.R1 := by
    show s ∈ N.R ⊓ N.fixing (V0 N.F N.F')
    exact Subgroup.mem_inf.2 ⟨hsR, hsfix⟩
  refine ⟨s, Subgroup.mem_inf.2 ⟨hGam, hR1⟩, fun a => ?_⟩
  have h0' : (Submodule.Quotient.mk x : V ⧸ II N.F N.F') = 0 := (Submodule.Quotient.mk_eq_zero _).2 hxI
  have e : s (N.ist a) - N.ist a =
      (H.B (N.ist a) u • x - H.B (N.ist a) x • u) + c • H.B (N.ist a) x • x := by
    show Formalism.HermitianLatticeCounting.S6.eich H x u c (N.ist a) - N.ist a = _
    rw [Formalism.HermitianLatticeCounting.P.eich_apply]
    abel
  show (II N.F N.F').mkQ (s (N.ist a) - N.ist a) = _
  rw [e, hu_eq]
  simp [h0']

omit [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] in
/- English proof (translation)
Establish `h : ∀ u ∈ N.F.Xa n, H.B u (N.ist b) = 0` using `Formalism.HermitianLatticeCounting.P.perp_Xa N.F (fun c hc => by`. Rewrite using `[N.ist_e c b hb, if_neg]`. Introduce and unpack `rfl`. Use the proof step `omega)`. Rewrite using `[← H.herm, h x hx, star_zero]`.
-/
theorem ist_orth_Xa {n : ℕ} {b : Fin r} (hb : N.j ≤ b.val) (hn : n ≤ b.val) {x : V} (hx : x ∈ N.F.Xa n) :
    H.B (N.ist b) x = 0 := by
  have h : ∀ u ∈ N.F.Xa n, H.B u (N.ist b) = 0 := Formalism.HermitianLatticeCounting.P.perp_Xa N.F (fun c hc => by
    rw [N.ist_e c b hb, if_neg]
    rintro rfl
    omega)
  rw [← H.herm, h x hx, star_zero]

omit [FiniteDimensional K V] in
/- English proof (translation)
Establish `hst : star t ∈ N.aa a` using `star_mem_ipow N.𝔡_ne N.𝔡_star _ ht`. Take `⟨hF1, -⟩` from `hF`. Rewrite `hst` using `[← hF1 a]`. Unfold `GlobalTheory.HermLat.lead at hst`. Rewrite `hst` using `[Submodule.mem_comap]`.

Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hst`. Establish `hzX : z ∈ N.F.Xa a.val` using `by simpa using hz`. Establish `e0 : (LinearMap.toSpanSingleton K V (N.F.e a.castSucc)).restrictScalars (𝓞 K) (star t) = star t • N.F.e a.castSucc` using `by simp [LinearMap.toSpanSingleton_apply]`. Rewrite `hyz` using `[e0]`. Establish `hy' : y = star t • N.F.e a.castSucc - z` using `by rw [← hyz]; abel`.

Establish `hab' : ∀ b : Fin r, a < b → a.val ≤ b.val` using `fun b hab => le_of_lt hab`. Use `⟨y, Submodule.mem_inf.2 ⟨hy, ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Use `show y ∈ N.F.X`. Rewrite using `[hy']`. Conclude with `sub_mem (Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)) (Formalism.HermitianLatticeCounting.P.Xa_le_X N.F _ hzX)`.

Rewrite using `[hy', map_sub, map_smulₛₗ, ist_orth_Xa N ha le_rfl hzX, ← H.herm (N.F.e a.castSucc), N.ist_e a a ha, if_pos rfl]`. Simplify using `only [star_one, smul_eq_mul, mul_one, sub_zero]`. Rewrite using `[starRingEnd_apply, star_star]`. Introduce `b hab`. Establish `hb` using `ha.trans (hab' b hab)`.

Rewrite using `[hy', map_sub, map_smulₛₗ, ist_orth_Xa N hb (hab' b hab) hzX, ← H.herm (N.F.e a.castSucc), N.ist_e a b hb, if_neg (ne_of_lt hab)]`. Simplify using the standard rewrite rules.
-/
theorem exists_lead {Λ : Submodule (𝓞 K) V} (hF : IsFrame N.F Λ N.aa) {a : Fin r} (ha : N.j ≤ a.val)
    {t : K} (ht : t ∈ N.aa a) : ∃ x ∈ Λ ⊓ rs (𝓞 K) N.F.X, H.B (N.ist a) x = t ∧
      ∀ b : Fin r, a < b → H.B (N.ist b) x = 0 := by
  have hst : star t ∈ N.aa a := star_mem_ipow N.𝔡_ne N.𝔡_star _ ht
  obtain ⟨hF1, -⟩ := hF
  rw [← hF1 a] at hst
  unfold GlobalTheory.HermLat.lead at hst
  rw [Submodule.mem_comap] at hst
  obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hst
  have hzX : z ∈ N.F.Xa a.val := by simpa using hz
  have e0 : (LinearMap.toSpanSingleton K V (N.F.e a.castSucc)).restrictScalars (𝓞 K) (star t) =
      star t • N.F.e a.castSucc := by simp [LinearMap.toSpanSingleton_apply]
  rw [e0] at hyz
  have hy' : y = star t • N.F.e a.castSucc - z := by rw [← hyz]; abel
  have hab' : ∀ b : Fin r, a < b → a.val ≤ b.val := fun b hab => le_of_lt hab
  refine ⟨y, Submodule.mem_inf.2 ⟨hy, ?_⟩, ?_, ?_⟩
  · show y ∈ N.F.X
    rw [hy']
    exact sub_mem (Submodule.smul_mem _ _ (Formalism.HermitianLatticeCounting.P.e_mem_X N.F a)) (Formalism.HermitianLatticeCounting.P.Xa_le_X N.F _ hzX)
  · rw [hy', map_sub, map_smulₛₗ, ist_orth_Xa N ha le_rfl hzX, ← H.herm (N.F.e a.castSucc),
      N.ist_e a a ha, if_pos rfl]
    simp only [star_one, smul_eq_mul, mul_one, sub_zero]
    rw [starRingEnd_apply, star_star]
  · intro b hab
    have hb := ha.trans (hab' b hab)
    rw [hy', map_sub, map_smulₛₗ, ist_orth_Xa N hb (hab' b hab) hzX, ← H.herm (N.F.e a.castSucc),
      N.ist_e a b hb, if_neg (ne_of_lt hab)]
    simp
/- English proof (translation)
Establish `hsR1 : s ∈ N.R1` using `(Subgroup.mem_inf.1 hs).2`. Establish `hst : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ)`. Establish `h` using `(Subgroup.mem_inf.1 hs).1`. Simplify using `only [NF.Gam, Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at h`. Conclude with `h.2`.

Establish `hII : ∀ x ∈ II N.F N.F', x ∈ flagPairDefinitePartLattice N.F N.F' Λ`. Introduce `x hx`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show x ∈ uPerp N.F N.F'`. Rewrite using `[huP]`.

Conclude with `Submodule.mem_sup_right hx`. Establish `hx1 : x ∈ N.F.X` using `by unfold II at hx; exact (Submodule.mem_inf.1 hx).1`. Conclude with `Submodule.mem_sup_right hx1`. Use `show x ∈ wSp N.F N.F'`. Rewrite using `[hw]`.

Conclude with `Submodule.mem_sup_right hx`. Establish `key : ∀ q ∈ ipow N.𝔡 ((r : ℤ) - a.val), q • (s (N.ist a) - N.ist a) ∈ flagPairDefinitePartLattice N.F N.F' Λ`. Introduce `q hq`. Establish `h1 : q • N.ist a ∈ N.Ref (latL N.F N.F' Λ)`. Unfold `NF.Ref NF.P0`.

Use `Submodule.mem_sup_left (Submodule.mem_sup_right ?_)` and prove the remaining obligations. Use `Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)` and prove the remaining obligations. Conclude with `Submodule.mem_map.2 ⟨q, hq, rfl⟩`. Establish `h2 : s (q • N.ist a) ∈ N.Ref (latL N.F N.F' Λ)`. Establish `h3` using `Submodule.smul_mem_pointwise_smul (q • N.ist a) s _ h1`.

Rewrite `h3` using `[hst]`. Conclude with `h3`. Establish `h4 : q • (s (N.ist a) - N.ist a) = s (q • N.ist a) - q • N.ist a`. Rewrite using `[map_smul, smul_sub]`. Rewrite using `[h4]`.

Conclude with `mem_innerLattice_of_referenceLattice_trace N hc hw hn hP hz (sub_mem h2 h1) (sub_mem_wSp N hsR1 _)`. Establish `main : ∀ u ∈ ipow N.𝔡 (-((r : ℤ) - a.val)) * ipow N.𝔡 ((r : ℤ) - a.val), ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup, u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F'`. Introduce `u hu`. Use `Submodule.mul_induction_on (C := fun u => ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup, u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F') hu ?_ ?_` and prove the remaining obligations. Introduce `p hp q hq`.

Establish `hq'` using `key q hq`. Establish `hwsp : q • (s (N.ist a) - N.ist a) ∈ N.Wt ⊔ II N.F N.F'`. Rewrite using `[← hw]`. Conclude with `(Submodule.mem_inf.1 (show _ ∈ latL N.F N.F' Λ ⊓ rs (𝓞 K) (wSp N.F N.F') from hq')).2`. Take `⟨w1, hw1, i1, hi1, hsum⟩` from `Submodule.mem_sup.1 hwsp`.

Use `⟨p • w1, smul_mem_prodGrp hp ?_, ?_⟩` and prove the remaining obligations. Use `show w1 ∈ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt`. Use `Submodule.mem_inf.2 ⟨?_, hw1⟩` and prove the remaining obligations. Establish `h5 : w1 = q • (s (N.ist a) - N.ist a) - i1` using `by rw [← hsum, add_sub_cancel_right]`. Rewrite using `[h5]`.

Conclude with `sub_mem hq' (hII i1 hi1)`. Establish `h6 : (p * q) • (s (N.ist a) - N.ist a) - p • w1 = p • i1`. Rewrite using `[mul_smul, ← smul_sub, ← hsum, add_sub_cancel_left]`. Rewrite using `[h6]`. Conclude with `(II N.F N.F').smul_mem p hi1`.

Introduce and unpack `x y ⟨y1, hy1, h1⟩ ⟨y2, hy2, h2⟩`. Use `⟨y1 + y2, add_mem hy1 hy2, ?_⟩` and prove the remaining obligations. Establish `h7 : (x + y) • (s (N.ist a) - N.ist a) - (y1 + y2) = (x • (s (N.ist a) - N.ist a) - y1) + (y • (s (N.ist a) - N.ist a) - y2)`. Rewrite using `[add_smul]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h7]`. Conclude with `add_mem h1 h2`. Take `⟨y, hy, hy'⟩` from `main 1 (one_mem_ipow_mul N.𝔡_ne _)`. Rewrite `hy'` using `[one_smul]`. Conclude with `⟨y, hy, hy'⟩`.
-/
private theorem exists_ne_zero_smul_mem_of_mem_span' {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (hc : IsCompl N.Wt N.Pi) (hw : wSp N.F N.F' = N.Wt ⊔ II N.F N.F')
    (hn : N.Wn = N.Wt ⊔ Submodule.span K {N.F.z}) (hP : N.Pi = V0 N.F N.F' ⊔ N.Ist)
    (huP : uPerp N.F N.F' = N.Wn ⊔ II N.F N.F')
    {Λ : Submodule (𝓞 K) V} (hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X)
    {s : V ≃ₗ[K] V} (hs : s ∈ N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) (a : Fin r) (ha : N.j ≤ a.val) :
    ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup,
      s (N.ist a) - N.ist a - y ∈ II N.F N.F' := by
  have hsR1 : s ∈ N.R1 := (Subgroup.mem_inf.1 hs).2
  have hst : s • N.Ref (latL N.F N.F' Λ) = N.Ref (latL N.F N.F' Λ) := by
    have h := (Subgroup.mem_inf.1 hs).1
    simp only [NF.Gam, Subgroup.mem_inf, MulAction.mem_stabilizer_iff] at h
    exact h.2
  have hII : ∀ x ∈ II N.F N.F', x ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
    intro x hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, ?_⟩, ?_⟩
    · show x ∈ uPerp N.F N.F'
      rw [huP]; exact Submodule.mem_sup_right hx
    · have hx1 : x ∈ N.F.X := by unfold II at hx; exact (Submodule.mem_inf.1 hx).1
      exact Submodule.mem_sup_right hx1
    · show x ∈ wSp N.F N.F'
      rw [hw]; exact Submodule.mem_sup_right hx
  have key : ∀ q ∈ ipow N.𝔡 ((r : ℤ) - a.val), q • (s (N.ist a) - N.ist a) ∈ flagPairDefinitePartLattice N.F N.F' Λ := by
    intro q hq
    have h1 : q • N.ist a ∈ N.Ref (latL N.F N.F' Λ) := by
      unfold NF.Ref NF.P0
      refine Submodule.mem_sup_left (Submodule.mem_sup_right ?_)
      refine Submodule.mem_iSup_of_mem a (Submodule.mem_iSup_of_mem ha ?_)
      exact Submodule.mem_map.2 ⟨q, hq, rfl⟩
    have h2 : s (q • N.ist a) ∈ N.Ref (latL N.F N.F' Λ) := by
      have h3 := Submodule.smul_mem_pointwise_smul (q • N.ist a) s _ h1
      rw [hst] at h3
      exact h3
    have h4 : q • (s (N.ist a) - N.ist a) = s (q • N.ist a) - q • N.ist a := by
      rw [map_smul, smul_sub]
    rw [h4]
    exact mem_innerLattice_of_referenceLattice_trace N hc hw hn hP hz (sub_mem h2 h1) (sub_mem_wSp N hsR1 _)
  have main : ∀ u ∈ ipow N.𝔡 (-((r : ℤ) - a.val)) * ipow N.𝔡 ((r : ℤ) - a.val),
      ∃ y ∈ prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup,
        u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F' := by
    intro u hu
    refine Submodule.mul_induction_on (C := fun u => ∃ y ∈ prodGrp (N.aa a).toAddSubgroup
      (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup, u • (s (N.ist a) - N.ist a) - y ∈ II N.F N.F') hu ?_ ?_
    · intro p hp q hq
      have hq' := key q hq
      have hwsp : q • (s (N.ist a) - N.ist a) ∈ N.Wt ⊔ II N.F N.F' := by
        rw [← hw]
        exact (Submodule.mem_inf.1 (show _ ∈ latL N.F N.F' Λ ⊓ rs (𝓞 K) (wSp N.F N.F') from hq')).2
      obtain ⟨w1, hw1, i1, hi1, hsum⟩ := Submodule.mem_sup.1 hwsp
      refine ⟨p • w1, smul_mem_prodGrp hp ?_, ?_⟩
      · show w1 ∈ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt
        refine Submodule.mem_inf.2 ⟨?_, hw1⟩
        have h5 : w1 = q • (s (N.ist a) - N.ist a) - i1 := by rw [← hsum, add_sub_cancel_right]
        rw [h5]; exact sub_mem hq' (hII i1 hi1)
      · have h6 : (p * q) • (s (N.ist a) - N.ist a) - p • w1 = p • i1 := by
          rw [mul_smul, ← smul_sub, ← hsum, add_sub_cancel_left]
        rw [h6]; exact (II N.F N.F').smul_mem p hi1
    · rintro x y ⟨y1, hy1, h1⟩ ⟨y2, hy2, h2⟩
      refine ⟨y1 + y2, add_mem hy1 hy2, ?_⟩
      have h7 : (x + y) • (s (N.ist a) - N.ist a) - (y1 + y2) =
          (x • (s (N.ist a) - N.ist a) - y1) + (y • (s (N.ist a) - N.ist a) - y2) := by
        rw [add_smul]; abel
      rw [h7]; exact add_mem h1 h2
  obtain ⟨y, hy, hy'⟩ := main 1 (one_mem_ipow_mul N.𝔡_ne _)
  rw [one_smul] at hy'
  exact ⟨y, hy, hy'⟩

/- English proof (translation)
Establish `hS' : latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F')` using `hS`. Establish `hLa : (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup`. Introduce `x hx`. Establish `hx' : (x, x) ∈ iotaGraph N.F N.F' Λ (g : 𝓞 K)` using `hx`. Unfold `iotaGraph at hx'`.

Conclude with `(Submodule.mem_prod.1 (Submodule.mem_inf.1 hx').1).2`. Establish `hT' : (latTh N.F N.F' Λ).toAddSubgroup ≤ (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup` using `hT`. Establish `hprod : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup = N.gI g Λ * N.iI g Λ`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ hT' hLa, mul_comm]`. Both sides reduce to the same expression.

Establish `hM : (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup = (latTh N.F N.F' Λ).toAddSubgroup ⊓ (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup`. Use extensionality with `x`. Simplify using `only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_inf]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hxΛ, hxW⟩`.

Establish `hxT : x ∈ latTh N.F N.F' Λ`. Rewrite using `[hS']`. Conclude with `Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hxΛ, hxW⟩)`. Conclude with `⟨hxT, hLa (hT' hxT), hxW⟩`. Introduce and unpack `⟨hxT, -, hxW⟩`.

Rewrite `hxT` using `[hS']`. Take `⟨y, hy, z, hz, hyz⟩` from `Submodule.mem_sup.1 hxT`. Establish `hzW : z ∈ N.Wt`. Establish `h8 : z = x - y` using `by rw [← hyz, add_sub_cancel_left]`. Rewrite using `[h8]`.

Conclude with `sub_mem hxW (Submodule.mem_inf.1 hy).2`. Establish `hz0 : z = 0`. Establish `h9 : z ∈ N.Wt ⊓ II N.F N.F'` using `Submodule.mem_inf.2 ⟨hzW, hz⟩`. Rewrite `h9` using `[hlift.2.1]`. Conclude with `(Submodule.mem_bot K).1 h9`.

Rewrite using `[← hyz, hz0, add_zero]`. Conclude with `Submodule.mem_inf.1 hy`. Establish `hne : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup ≠ 0`. Rewrite using `[hprod]`. Conclude with `Nat.pos_iff_ne_zero.1 (Nat.mul_pos hg0 hi0)`.

Establish `hle : (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup` using `fun x hx => (Submodule.mem_inf.1 hx).1`. Rewrite using `[hM, AddSubgroup.inf_relIndex_right]`. Use `⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_right hle h0), ?_⟩` and prove the remaining obligations. Rewrite using `[← hprod]`. Conclude with `AddSubgroup.relIndex_le_of_le_right hle hne`.
-/
private theorem main_lemma_2 {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] {H : HermSpace K V} {r : ℕ}
    (N : NF H r) (g : ℕ) (Λ : Submodule (𝓞 K) V) (hlift : IsLift N.F N.F' N.Wt) (hS : N.Split Λ)
    (hT : latTh N.F N.F' Λ ≤ latLa N.F N.F' Λ (g : 𝓞 K)) (hg0 : 0 < N.gI g Λ) (hi0 : 0 < N.iI g Λ) :
    (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≠ 0 ∧
    (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤
      N.gI g Λ * N.iI g Λ := by
  have hS' : latTh N.F N.F' Λ = (Λ ⊓ rs (𝓞 K) N.Wt) ⊔ rs (𝓞 K) (II N.F N.F') := hS
  have hLa : (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup := by
    intro x hx
    have hx' : (x, x) ∈ iotaGraph N.F N.F' Λ (g : 𝓞 K) := hx
    unfold iotaGraph at hx'
    exact (Submodule.mem_prod.1 (Submodule.mem_inf.1 hx').1).2
  have hT' : (latTh N.F N.F' Λ).toAddSubgroup ≤ (latLa N.F N.F' Λ (g : 𝓞 K)).toAddSubgroup := hT
  have hprod : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup =
      N.gI g Λ * N.iI g Λ := by
    rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ hT' hLa, mul_comm]; rfl
  have hM : (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup =
      (latTh N.F N.F' Λ).toAddSubgroup ⊓ (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup := by
    ext x
    simp only [AddSubgroup.mem_inf, Submodule.mem_toAddSubgroup, Submodule.mem_inf]
    constructor
    · rintro ⟨hxΛ, hxW⟩
      have hxT : x ∈ latTh N.F N.F' Λ := by
        rw [hS']; exact Submodule.mem_sup_left (Submodule.mem_inf.2 ⟨hxΛ, hxW⟩)
      exact ⟨hxT, hLa (hT' hxT), hxW⟩
    · rintro ⟨hxT, -, hxW⟩
      rw [hS'] at hxT
      obtain ⟨y, hy, z, hz, hyz⟩ := Submodule.mem_sup.1 hxT
      have hzW : z ∈ N.Wt := by
        have h8 : z = x - y := by rw [← hyz, add_sub_cancel_left]
        rw [h8]; exact sub_mem hxW (Submodule.mem_inf.1 hy).2
      have hz0 : z = 0 := by
        have h9 : z ∈ N.Wt ⊓ II N.F N.F' := Submodule.mem_inf.2 ⟨hzW, hz⟩
        rw [hlift.2.1] at h9; exact (Submodule.mem_bot K).1 h9
      rw [← hyz, hz0, add_zero]; exact Submodule.mem_inf.1 hy
  have hne : (latTh N.F N.F' Λ).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup ≠ 0 := by
    rw [hprod]; exact Nat.pos_iff_ne_zero.1 (Nat.mul_pos hg0 hi0)
  have hle : (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (flagPairDefinitePartLattice N.F N.F' Λ).toAddSubgroup :=
    fun x hx => (Submodule.mem_inf.1 hx).1
  rw [hM, AddSubgroup.inf_relIndex_right]
  refine ⟨fun h0 => hne (AddSubgroup.relIndex_eq_zero_of_le_right hle h0), ?_⟩
  rw [← hprod]
  exact AddSubgroup.relIndex_le_of_le_right hle hne

end Geometry

/- English proof (translation)
Introduce `K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hterm hS`. Take `⟨-, hlift, hc, -, hn, huP, hw, -, -, -, -, hP⟩` from `GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N`. Take `⟨hb0, -, -, -⟩` from `GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hterm`. Take `⟨hT, hg0, hi0, -, -, -, -, -⟩` from `GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hterm`. Take `⟨w₀, hw₀⟩` from `GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' K hK`.

Take `⟨hU, hF, -⟩` from `hterm.1`. Establish `hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K)`. Introduce `x hx y hy`. Establish `hx' : x ∈ dual H Λ` using `by rw [hU.2]; exact hx`. Conclude with `((mem_dual_iff H Λ x).1 hx').2 y hy`.

Establish `hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X`. Establish `h1 : (1 : K) ∈ lead N.F Λ (Fin.last r)`. Rewrite using `[hF.2]`. Conclude with `Submodule.mem_one.2 ⟨1, map_one _⟩`. Establish `h3 : (1 : K) • N.F.e (Fin.last r) ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa r)` using `Submodule.mem_comap.1 h1`.

Rewrite `h3` using `[one_smul]`. Conclude with `h3`. Use `set S : Finset (Fin r) := Finset.univ.filter (fun a : Fin r => N.j ≤ a.val) with hSdef`. Establish `hmemS : ∀ a, a ∈ S ↔ N.j ≤ a.val` using `by intro a; simp [hSdef]`. Establish `hZR : N.ZI ≤ N.R1` using `by unfold NF.ZI; exact inf_le_left`.

Set `Ag : Subgroup (V ≃ₗ[K] V)` to `(N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI`. Set `Bg : Subgroup (V ≃ₗ[K] V)` to `(N.Gam Λ ⊓ N.R1) ⊔ N.ZI`. Establish `hAR : Ag ≤ N.R1` using `sup_le inf_le_right hZR`. Establish `hBR : Bg ≤ N.R1` using `sup_le inf_le_right hZR`. Establish `hrow1 : ∀ a, row N a 1 = 0` using `by intro a; simp [row]`.

Establish `hrowinv : ∀ a, ∀ s ∈ N.R1, row N a s⁻¹ = -row N a s`. Introduce `a s hs`. Establish `h` using `row_mul N a hs (inv_mem hs)`. Rewrite `h` using `[mul_inv_cancel, hrow1]`. Conclude with `(neg_eq_of_add_eq_zero_right h.symm).symm`.

Set `Q : Fin r → AddSubgroup (V ⧸ II N.F N.F')` to `fun a => { carrier := {y | ∃ s ∈ Bg, row N a s = y ∧ ∀ b ∈ S, a < b → row N b s = 0} add_mem' := by`. Introduce and unpack `x y ⟨s, hs, rfl, hs0⟩ ⟨t, ht, rfl, ht0⟩`. Use `⟨s * t, mul_mem hs ht, row_mul N a (hBR hs) (hBR ht), fun b hb hab => ?_⟩` and prove the remaining obligations. Rewrite using `[row_mul N b (hBR hs) (hBR ht), hs0 b hb hab, ht0 b hb hab, add_zero]`. Use the proof step `zero_mem' := ⟨1, one_mem _, hrow1 a, fun b _ _ => hrow1 b⟩`.

Use the proof step `neg_mem' := by`. Introduce and unpack `x ⟨s, hs, rfl, hs0⟩`. Use `⟨s⁻¹, inv_mem hs, hrowinv a s (hBR hs), fun b hb hab => ?_⟩` and prove the remaining obligations. Rewrite using `[hrowinv b s (hBR hs), hs0 b hb hab, neg_zero] }`. Set `C' : Fin r → AddSubgroup K` to `fun a => { carrier := {t | ∃ i ∈ Λ ⊓ rs (𝓞 K) (II N.F N.F'), H.B (N.ist a) i = t ∧ ∀ b ∈ S, a < b → H.B (N.ist b) i = 0} add_mem' := by`.

Introduce and unpack `x y ⟨i, hi, rfl, hi0⟩ ⟨i', hi', rfl, hi0'⟩`. Use `⟨i + i', add_mem hi hi', map_add _ _ _, fun b hb hab => ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, hi0 b hb hab, hi0' b hb hab, add_zero]`. Use the proof step `zero_mem' := ⟨0, zero_mem _, map_zero _, fun b _ _ => map_zero _⟩`. Use the proof step `neg_mem' := by`.

Introduce and unpack `x ⟨i, hi, rfl, hi0⟩`. Use `⟨-i, neg_mem hi, map_neg _ _, fun b hb hab => ?_⟩` and prove the remaining obligations. Rewrite using `[map_neg, hi0 b hb hab, neg_zero] }`. Set `φ : V →+ V ⧸ II N.F N.F'` to `(II N.F N.F').mkQ.toAddMonoidHom`. Set `P : Fin r → AddSubgroup (V ⧸ II N.F N.F')` to `fun a => Q a ⊔ (prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup).map φ`.

Establish `hM_FG : (Λ ⊓ rs (𝓞 K) N.Wt).FG`. Establish `hlat : Submodule.IsLattice K Λ` using `((isUnimod_iff H Λ).1 hU).1`. Use `isNoetherian_of_fg_of_noetherian Λ hlat.fg` as an intermediate fact. Conclude with `(isNoetherian_submodule.1 this) _ inf_le_left`. Establish `hm` using `main_lemma_2 N g Λ hlift hS hT hg0 hi0`.

Use `set m : ℕ := (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup with hm_def`. Establish `hML : Λ ⊓ rs (𝓞 K) N.Wt ≤ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt`. Introduce `x hx`. Take `⟨hxΛ, hxW⟩` from `Submodule.mem_inf.1 hx`. Use `Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, Submodule.mem_sup_left hxΛ⟩, ?_⟩, hxW⟩` and prove the remaining obligations.

Use `show x ∈ uPerp N.F N.F'`. Rewrite using `[huP, hn]`. Conclude with `Submodule.mem_sup_left (Submodule.mem_sup_left hxW)`. Use `show x ∈ wSp N.F N.F'`. Rewrite using `[hw]`.

Conclude with `Submodule.mem_sup_left hxW`. Establish `hfr` using `prod_le_relIndex (fun a => (H.B (N.ist a)).toAddMonoidHom) (fun a => (N.aa a).toAddSubgroup) C' S (Λ ⊓ rs (𝓞 K) N.F.X).toAddSubgroup (latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F'))).toAddSubgroup hb0 (by`. Introduce `a ha y hy`. Take `⟨x, hx, hxa, hxb⟩` from `exists_lead N hF ((hmemS a).1 ha) hy`. Conclude with `⟨x, hx, hxa, fun b _ hab => hxb b hab⟩)`.

Use the proof step `(by`. Introduce `a ha x hx hxb`. Establish `hx' : x ∈ latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F'))` using `hx`. Take `⟨y, hy, z, hz, rfl⟩` from `Submodule.mem_sup.1 hx'`. Establish `hy' : y ∈ Λ ⊓ rs (𝓞 K) (N.F.Xa N.j)` using `hy`.

Establish `hy0 : ∀ c ∈ S, H.B (N.ist c) y = 0` using `fun c hc => ist_orth_Xa N ((hmemS c).1 hc) ((hmemS c).1 hc) (Submodule.mem_inf.1 hy').2`. Use `⟨z, hz, ?_, fun b hb hab => ?_⟩` and prove the remaining obligations. Use `show H.B (N.ist a) z = H.B (N.ist a) (y + z)`. Rewrite using `[map_add, hy0 a ha, zero_add]`. Establish `h10` using `hxb b hb hab`.

Express the relevant statement in the definitionally equal form `H.B (N.ist b) (y + z) = 0 at h10`. Rewrite using `[map_add, hy0 b hb, zero_add] at h10)` and apply the resulting hypothesis. Establish `hper : ∀ a ∈ S, (Q a).relIndex (P a) ≠ 0 ∧ (Q a).relIndex (P a) ≤ (C' a).relIndex (N.aa a).toAddSubgroup ^ Module.finrank K N.Wt * m`. Introduce `a ha`. Establish `hCA : (C' a ⊓ (N.aa a).toAddSubgroup).relIndex (N.aa a).toAddSubgroup ≠ 0`.

Rewrite using `[AddSubgroup.inf_relIndex_right]`. Conclude with `hfr.1 a ha`. Establish `hpg` using `relIndex_prodGrp_le (W := N.Wt) (k := Module.finrank K N.Wt) (A := N.aa a) (C := C' a ⊓ (N.aa a).toAddSubgroup) (L := flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt) (M := Λ ⊓ rs (𝓞 K) N.Wt) le_rfl (ipow_fg N.𝔡 _) inf_le_right hCA hM_FG (fun x hx => (Submodule.mem_inf.1 h …`. Rewrite `hpg` using `[AddSubgroup.inf_relIndex_right]`. Establish `hQ1 : prodGrp (C' a ⊓ (N.aa a).toAddSubgroup) (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (Q a).comap φ`.

Unfold `prodGrp`. Rewrite using `[AddSubgroup.closure_le]`. Introduce and unpack `_ ⟨t, ht, v, hv, rfl⟩`. Take `⟨i, hi, hit, hib⟩` from `(AddSubgroup.mem_inf.1 ht).1`. Take `⟨hiΛ, hiI⟩` from `Submodule.mem_inf.1 hi`.

Take `⟨hvΛ, hvW⟩` from `Submodule.mem_inf.1 hv`. Take `⟨s, hs, hsrow⟩` from `exists_eichler N hw₀ hΛ hiΛ hiI hvΛ hvW`. Use `AddSubgroup.mem_comap.2 ?_` and prove the remaining obligations. Use `show ∃ s ∈ Bg, row N a s = φ (t • v) ∧ ∀ b ∈ S, a < b → row N b s = 0`. Use `⟨s, Subgroup.mem_sup_left hs, ?_, fun b hb hab => ?_⟩` and prove the remaining obligations.

Rewrite using `[hsrow a, hit]`. Conclude with `(LinearMap.map_smul (II N.F N.F').mkQ t v).symm`. Rewrite using `[hsrow b, hib b hb hab, zero_smul]`. Establish `hmap` using `relIndex_le_of_map φ (P₁ := prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup) (P := P a) (Q := Q a) le_rfl hQ1 hpg.1`. Conclude with `⟨hmap.1, hmap.2.trans hpg.2⟩`.

Establish `hPmem : ∀ a ∈ S, ∀ s ∈ Ag, row N a s ∈ P a`. Introduce `a ha`. Set `T : Subgroup (V ≃ₗ[K] V)` to `{ carrier := {s | s ∈ N.R1 ∧ row N a s ∈ P a} mul_mem' := by`. Introduce and unpack `s t ⟨hs, hs'⟩ ⟨ht, ht'⟩`. Conclude with `⟨mul_mem hs ht, by rw [row_mul N a hs ht]; exact add_mem hs' ht'⟩`.

Use the proof step `one_mem' := ⟨one_mem _, by rw [hrow1]; exact zero_mem _⟩`. Use the proof step `inv_mem' := by`. Introduce and unpack `s ⟨hs, hs'⟩`. Conclude with `⟨inv_mem hs, by rw [hrowinv a s hs]; exact neg_mem hs'⟩ }`. Establish `hAT : Ag ≤ T`.

Use `sup_le ?_ ?_` and prove the remaining obligations. Introduce `s hs`. Use `⟨(Subgroup.mem_inf.1 hs).2, ?_⟩` and prove the remaining obligations. Take `⟨y, hy, hy'⟩` from `exists_ne_zero_smul_mem_of_mem_span' N hc hw hn hP huP hz hs a ((hmemS a).1 ha)`. Use `AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩)` and prove the remaining obligations.

Use `show (II N.F N.F').mkQ y = (II N.F N.F').mkQ (s (N.ist a) - N.ist a)`. Rewrite using `[Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← neg_sub]`. Conclude with `neg_mem hy'`. Introduce `s hs`. Conclude with `⟨hZR hs, by rw [row_eq_zero N hc hw hs a]; exact zero_mem _⟩`.

Introduce `s hs`. Conclude with `(hAT hs).2`. Establish `hker : ∀ s ∈ N.R1, (∀ a ∈ S, row N a s = 0) → s ∈ Ag ∧ s ∈ Bg`. Introduce `s hs h0`. Establish `hZ` using `mem_ZI_of_row N hlift hw hs (fun a ha => h0 a ((hmemS a).2 ha))`.

Conclude with `⟨Subgroup.mem_sup_right hZ, Subgroup.mem_sup_right hZ⟩`. Establish `hinv` using `invVol_le_prod (fun a s => row N a s) P Q S N.R1 Ag Bg hAR hBR (fun a _ s hs t ht => row_mul N a hs ht) hker hPmem (fun a _ y hy => hy) (fun a ha => (hper a ha).1)`. Use `hinv.trans ?_` and prove the remaining obligations. Establish `hcard : S.card = r - N.j`. Establish `h1` using `Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r))) (p := fun a : Fin r => N.j ≤ a.val)`.

Establish `h2 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)).card = N.j`. Establish `h11 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)) = Finset.univ.filter (fun a : Fin r => a.val < N.j)`. Use extensionality with `a`. Simplify using the standard rewrite rules. Rewrite using `[h11, Fin.card_filter_val_lt]`.

Conclude with `min_eq_right N.j_le`. Rewrite `h1` using `[Finset.card_univ, Fintype.card_fin, h2, ← hSdef]`. Use linear arithmetic over natural numbers and integers. Establish `hnat : ∏ a ∈ S, (Q a).relIndex (P a) ≤ N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j)`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]`. Use `_ ≤ N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) := by`. Rewrite using `[hcard]`. Conclude with `Nat.mul_le_mul (Nat.pow_le_pow_left hfr.2 _) (Nat.pow_le_pow_left hm.2 _)`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hnat` after adjusting the coercions. Use `_ = (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by`. Rewrite using `[Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul]`.
-/
theorem invVol_mid_layer_le : ∀ (K V : Type) [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V] [FiniteDimensional K V] [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (H : HermSpace K V), Formalism.HermitianLatticesTheory.IsCMUnram K → ∀ (r : ℕ) (N : NF H r), ∀ (g : ℕ) (Λ : Submodule (𝓞 K) V), 1 ≤ g → N.IsTerm g Λ → N.Split Λ → GlobalTheory.HL.invVol ((N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI) ((N.Gam Λ ⊓ N.R1) ⊔ N.ZI) ≤ (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
  intro K V _ _ _ _ _ _ _ _ H hK r N g Λ hg hterm hS
  classical
  obtain ⟨-, hlift, hc, -, hn, huP, hw, -, -, -, -, hP⟩ := GlobalTheory.T.hermFramePairNormalForm_geometry_summary K V H hK r N
  obtain ⟨hb0, -, -, -⟩ := GlobalTheory.T.normal_form_terminal_determinant K V H hK r N g Λ hg hterm
  obtain ⟨hT, hg0, hi0, -, -, -, -, -⟩ := GlobalTheory.T.flagPairDefiniteThetaLattice_le_fixed_index_bound K V H hK r N g Λ hg hterm
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.T.exists_integer_add_star_eq_one_of_isCMUnram' K hK
  obtain ⟨hU, hF, -⟩ := hterm.1
  have hΛ : ∀ x ∈ Λ, ∀ y ∈ Λ, H.B x y ∈ (1 : Submodule (𝓞 K) K) := by
    intro x hx y hy
    have hx' : x ∈ dual H Λ := by rw [hU.2]; exact hx
    exact ((mem_dual_iff H Λ x).1 hx').2 y hy
  have hz : N.F.z ∈ Λ ⊔ rs (𝓞 K) N.F.X := by
    have h1 : (1 : K) ∈ lead N.F Λ (Fin.last r) := by
      rw [hF.2]; exact Submodule.mem_one.2 ⟨1, map_one _⟩
    have h3 : (1 : K) • N.F.e (Fin.last r) ∈ Λ ⊔ rs (𝓞 K) (N.F.Xa r) := Submodule.mem_comap.1 h1
    rw [one_smul] at h3
    exact h3
  set S : Finset (Fin r) := Finset.univ.filter (fun a : Fin r => N.j ≤ a.val) with hSdef
  have hmemS : ∀ a, a ∈ S ↔ N.j ≤ a.val := by intro a; simp [hSdef]
  have hZR : N.ZI ≤ N.R1 := by unfold NF.ZI; exact inf_le_left
  let Ag : Subgroup (V ≃ₗ[K] V) := (N.Gam (N.Ref (latL N.F N.F' Λ)) ⊓ N.R1) ⊔ N.ZI
  let Bg : Subgroup (V ≃ₗ[K] V) := (N.Gam Λ ⊓ N.R1) ⊔ N.ZI
  have hAR : Ag ≤ N.R1 := sup_le inf_le_right hZR
  have hBR : Bg ≤ N.R1 := sup_le inf_le_right hZR
  have hrow1 : ∀ a, row N a 1 = 0 := by intro a; simp [row]
  have hrowinv : ∀ a, ∀ s ∈ N.R1, row N a s⁻¹ = -row N a s := by
    intro a s hs
    have h := row_mul N a hs (inv_mem hs)
    rw [mul_inv_cancel, hrow1] at h
    exact (neg_eq_of_add_eq_zero_right h.symm).symm
  let Q : Fin r → AddSubgroup (V ⧸ II N.F N.F') := fun a =>
    { carrier := {y | ∃ s ∈ Bg, row N a s = y ∧ ∀ b ∈ S, a < b → row N b s = 0}
      add_mem' := by
        rintro x y ⟨s, hs, rfl, hs0⟩ ⟨t, ht, rfl, ht0⟩
        refine ⟨s * t, mul_mem hs ht, row_mul N a (hBR hs) (hBR ht), fun b hb hab => ?_⟩
        rw [row_mul N b (hBR hs) (hBR ht), hs0 b hb hab, ht0 b hb hab, add_zero]
      zero_mem' := ⟨1, one_mem _, hrow1 a, fun b _ _ => hrow1 b⟩
      neg_mem' := by
        rintro x ⟨s, hs, rfl, hs0⟩
        refine ⟨s⁻¹, inv_mem hs, hrowinv a s (hBR hs), fun b hb hab => ?_⟩
        rw [hrowinv b s (hBR hs), hs0 b hb hab, neg_zero] }
  let C' : Fin r → AddSubgroup K := fun a =>
    { carrier := {t | ∃ i ∈ Λ ⊓ rs (𝓞 K) (II N.F N.F'), H.B (N.ist a) i = t ∧
        ∀ b ∈ S, a < b → H.B (N.ist b) i = 0}
      add_mem' := by
        rintro x y ⟨i, hi, rfl, hi0⟩ ⟨i', hi', rfl, hi0'⟩
        refine ⟨i + i', add_mem hi hi', map_add _ _ _, fun b hb hab => ?_⟩
        rw [map_add, hi0 b hb hab, hi0' b hb hab, add_zero]
      zero_mem' := ⟨0, zero_mem _, map_zero _, fun b _ _ => map_zero _⟩
      neg_mem' := by
        rintro x ⟨i, hi, rfl, hi0⟩
        refine ⟨-i, neg_mem hi, map_neg _ _, fun b hb hab => ?_⟩
        rw [map_neg, hi0 b hb hab, neg_zero] }
  let φ : V →+ V ⧸ II N.F N.F' := (II N.F N.F').mkQ.toAddMonoidHom
  let P : Fin r → AddSubgroup (V ⧸ II N.F N.F') := fun a =>
    Q a ⊔ (prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup).map φ
  have hM_FG : (Λ ⊓ rs (𝓞 K) N.Wt).FG := by
    have hlat : Submodule.IsLattice K Λ := ((isUnimod_iff H Λ).1 hU).1
    have := isNoetherian_of_fg_of_noetherian Λ hlat.fg
    exact (isNoetherian_submodule.1 this) _ inf_le_left
  have hm := main_lemma_2 N g Λ hlift hS hT hg0 hi0
  set m : ℕ := (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup.relIndex
    (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup with hm_def
  have hML : Λ ⊓ rs (𝓞 K) N.Wt ≤ flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt := by
    intro x hx
    obtain ⟨hxΛ, hxW⟩ := Submodule.mem_inf.1 hx
    refine Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨Submodule.mem_inf.2 ⟨?_, Submodule.mem_sup_left hxΛ⟩, ?_⟩, hxW⟩
    · show x ∈ uPerp N.F N.F'
      rw [huP, hn]; exact Submodule.mem_sup_left (Submodule.mem_sup_left hxW)
    · show x ∈ wSp N.F N.F'
      rw [hw]; exact Submodule.mem_sup_left hxW
  have hfr := prod_le_relIndex (fun a => (H.B (N.ist a)).toAddMonoidHom) (fun a => (N.aa a).toAddSubgroup) C' S
    (Λ ⊓ rs (𝓞 K) N.F.X).toAddSubgroup (latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F'))).toAddSubgroup hb0
    (by
      intro a ha y hy
      obtain ⟨x, hx, hxa, hxb⟩ := exists_lead N hF ((hmemS a).1 ha) hy
      exact ⟨x, hx, hxa, fun b _ hab => hxb b hab⟩)
    (by
      intro a ha x hx hxb
      have hx' : x ∈ latF N.F Λ N.j ⊔ (Λ ⊓ rs (𝓞 K) (II N.F N.F')) := hx
      obtain ⟨y, hy, z, hz, rfl⟩ := Submodule.mem_sup.1 hx'
      have hy' : y ∈ Λ ⊓ rs (𝓞 K) (N.F.Xa N.j) := hy
      have hy0 : ∀ c ∈ S, H.B (N.ist c) y = 0 := fun c hc =>
        ist_orth_Xa N ((hmemS c).1 hc) ((hmemS c).1 hc) (Submodule.mem_inf.1 hy').2
      refine ⟨z, hz, ?_, fun b hb hab => ?_⟩
      · show H.B (N.ist a) z = H.B (N.ist a) (y + z)
        rw [map_add, hy0 a ha, zero_add]
      · have h10 := hxb b hb hab
        change H.B (N.ist b) (y + z) = 0 at h10
        rwa [map_add, hy0 b hb, zero_add] at h10)
  have hper : ∀ a ∈ S, (Q a).relIndex (P a) ≠ 0 ∧
      (Q a).relIndex (P a) ≤ (C' a).relIndex (N.aa a).toAddSubgroup ^ Module.finrank K N.Wt * m := by
    intro a ha
    have hCA : (C' a ⊓ (N.aa a).toAddSubgroup).relIndex (N.aa a).toAddSubgroup ≠ 0 := by
      rw [AddSubgroup.inf_relIndex_right]; exact hfr.1 a ha
    have hpg := relIndex_prodGrp_le (W := N.Wt) (k := Module.finrank K N.Wt) (A := N.aa a)
      (C := C' a ⊓ (N.aa a).toAddSubgroup) (L := flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt)
      (M := Λ ⊓ rs (𝓞 K) N.Wt) le_rfl (ipow_fg N.𝔡 _) inf_le_right hCA hM_FG
      (fun x hx => (Submodule.mem_inf.1 hx).2) hML hm.1
    rw [AddSubgroup.inf_relIndex_right] at hpg
    have hQ1 : prodGrp (C' a ⊓ (N.aa a).toAddSubgroup) (Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup ≤ (Q a).comap φ := by
      unfold prodGrp
      rw [AddSubgroup.closure_le]
      rintro _ ⟨t, ht, v, hv, rfl⟩
      obtain ⟨i, hi, hit, hib⟩ := (AddSubgroup.mem_inf.1 ht).1
      obtain ⟨hiΛ, hiI⟩ := Submodule.mem_inf.1 hi
      obtain ⟨hvΛ, hvW⟩ := Submodule.mem_inf.1 hv
      obtain ⟨s, hs, hsrow⟩ := exists_eichler N hw₀ hΛ hiΛ hiI hvΛ hvW
      refine AddSubgroup.mem_comap.2 ?_
      show ∃ s ∈ Bg, row N a s = φ (t • v) ∧ ∀ b ∈ S, a < b → row N b s = 0
      refine ⟨s, Subgroup.mem_sup_left hs, ?_, fun b hb hab => ?_⟩
      · rw [hsrow a, hit]
        exact (LinearMap.map_smul (II N.F N.F').mkQ t v).symm
      · rw [hsrow b, hib b hb hab, zero_smul]
    have hmap := relIndex_le_of_map φ
      (P₁ := prodGrp (N.aa a).toAddSubgroup (flagPairDefinitePartLattice N.F N.F' Λ ⊓ rs (𝓞 K) N.Wt).toAddSubgroup)
      (P := P a) (Q := Q a) le_rfl hQ1 hpg.1
    exact ⟨hmap.1, hmap.2.trans hpg.2⟩
  have hPmem : ∀ a ∈ S, ∀ s ∈ Ag, row N a s ∈ P a := by
    intro a ha
    let T : Subgroup (V ≃ₗ[K] V) :=
      { carrier := {s | s ∈ N.R1 ∧ row N a s ∈ P a}
        mul_mem' := by
          rintro s t ⟨hs, hs'⟩ ⟨ht, ht'⟩
          exact ⟨mul_mem hs ht, by rw [row_mul N a hs ht]; exact add_mem hs' ht'⟩
        one_mem' := ⟨one_mem _, by rw [hrow1]; exact zero_mem _⟩
        inv_mem' := by
          rintro s ⟨hs, hs'⟩
          exact ⟨inv_mem hs, by rw [hrowinv a s hs]; exact neg_mem hs'⟩ }
    have hAT : Ag ≤ T := by
      refine sup_le ?_ ?_
      · intro s hs
        refine ⟨(Subgroup.mem_inf.1 hs).2, ?_⟩
        obtain ⟨y, hy, hy'⟩ := exists_ne_zero_smul_mem_of_mem_span' N hc hw hn hP huP hz hs a ((hmemS a).1 ha)
        refine AddSubgroup.mem_sup_right (AddSubgroup.mem_map.2 ⟨y, hy, ?_⟩)
        show (II N.F N.F').mkQ y = (II N.F N.F').mkQ (s (N.ist a) - N.ist a)
        rw [Submodule.mkQ_apply, Submodule.mkQ_apply, Submodule.Quotient.eq, ← neg_sub]
        exact neg_mem hy'
      · intro s hs
        exact ⟨hZR hs, by rw [row_eq_zero N hc hw hs a]; exact zero_mem _⟩
    intro s hs
    exact (hAT hs).2
  have hker : ∀ s ∈ N.R1, (∀ a ∈ S, row N a s = 0) → s ∈ Ag ∧ s ∈ Bg := by
    intro s hs h0
    have hZ := mem_ZI_of_row N hlift hw hs (fun a ha => h0 a ((hmemS a).2 ha))
    exact ⟨Subgroup.mem_sup_right hZ, Subgroup.mem_sup_right hZ⟩
  have hinv := invVol_le_prod (fun a s => row N a s) P Q S N.R1 Ag Bg hAR hBR
    (fun a _ s hs t ht => row_mul N a hs ht) hker hPmem (fun a _ y hy => hy) (fun a ha => (hper a ha).1)
  refine hinv.trans ?_
  have hcard : S.card = r - N.j := by
    have h1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin r)))
      (p := fun a : Fin r => N.j ≤ a.val)
    have h2 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)).card = N.j := by
      have h11 : (Finset.univ.filter (fun a : Fin r => ¬ N.j ≤ a.val)) =
          Finset.univ.filter (fun a : Fin r => a.val < N.j) := by
        ext a; simp
      rw [h11, Fin.card_filter_val_lt]; exact min_eq_right N.j_le
    rw [Finset.card_univ, Fintype.card_fin, h2, ← hSdef] at h1
    omega
  have hnat : ∏ a ∈ S, (Q a).relIndex (P a) ≤
      N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) := by
    calc ∏ a ∈ S, (Q a).relIndex (P a)
        ≤ ∏ a ∈ S, ((C' a).relIndex (N.aa a).toAddSubgroup ^ Module.finrank K N.Wt * m) :=
          Finset.prod_le_prod (fun _ _ => Nat.zero_le _) (fun a ha => (hper a ha).2)
      _ = (∏ a ∈ S, (C' a).relIndex (N.aa a).toAddSubgroup) ^ Module.finrank K N.Wt * m ^ S.card := by
          rw [Finset.prod_mul_distrib, Finset.prod_pow, Finset.prod_const]
      _ ≤ N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) := by
          rw [hcard]
          exact Nat.mul_le_mul (Nat.pow_le_pow_left hfr.2 _) (Nat.pow_le_pow_left hm.2 _)
  calc (∏ a ∈ S, ((Q a).relIndex (P a) : ℝ)) = ((∏ a ∈ S, (Q a).relIndex (P a) : ℕ) : ℝ) :=
        (Nat.cast_prod _ _).symm
    _ ≤ ((N.bI Λ ^ Module.finrank K N.Wt * (N.gI g Λ * N.iI g Λ) ^ (r - N.j) : ℕ) : ℝ) := by
        exact_mod_cast hnat
    _ = (N.bI Λ : ℝ) ^ Module.finrank K N.Wt * ((N.gI g Λ : ℝ) * N.iI g Λ) ^ (r - N.j) := by
        rw [Nat.cast_mul, Nat.cast_pow, Nat.cast_pow, Nat.cast_mul]

end GlobalTheory.DegCnt.MidLayer
