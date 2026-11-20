import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.LocalMaximality.LiftFactorization
open KaehlerDifferential GlobalTheory.CechDR GlobalTheory.PD GlobalTheory.WH GlobalTheory.W1 UpperTheory.Gal.productCup_of_system
open scoped TensorProduct

/- English proof (translation)
Set `L : (Fin d → M) →ₗ[ℂ] E` to `∑ j, ((act (f j) : E →ₗ[ℂ] E) ∘ₗ M.subtype ∘ₗ (LinearMap.proj j : (Fin d → M) →ₗ[ℂ] M))`. Establish `hL : ∀ v, L v = ∑ j, act (f j) (v j : E)`. Introduce `v`. Simplify using `[L, LinearMap.sum_apply]`. Establish `hle : sm act M (Set.range f) ≤ LinearMap.range L`.

Use `iSup₂_le ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩ _ ⟨m, hm, rfl⟩`. Use `⟨Pi.single j ⟨m, hm⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hL, Finset.sum_eq_single j]`. Simplify using the standard rewrite rules.

Introduce `b _ hb`. Simplify using `[Pi.single_eq_of_ne hb]`. Simplify using the standard rewrite rules. Take `⟨v, rfl⟩` from `hle hx`. Conclude with `⟨fun j => (v j : E), fun j => (v j).2, hL v⟩`.
-/
private lemma exists_of_mem_sm_range {S E : Type} [CommRing S] [Algebra ℂ S] [AddCommGroup E] [Module ℂ E]
    (act : S →ₐ[ℂ] Module.End ℂ E) (M : Submodule ℂ E) {d : ℕ} (f : Fin d → S) (x : E)
    (hx : x ∈ sm act M (Set.range f)) :
    ∃ m : Fin d → E, (∀ j, m j ∈ M) ∧ x = ∑ j, act (f j) (m j) := by
  classical
  let L : (Fin d → M) →ₗ[ℂ] E :=
    ∑ j, ((act (f j) : E →ₗ[ℂ] E) ∘ₗ M.subtype ∘ₗ (LinearMap.proj j : (Fin d → M) →ₗ[ℂ] M))
  have hL : ∀ v, L v = ∑ j, act (f j) (v j : E) := by
    intro v
    simp [L, LinearMap.sum_apply]
  have hle : sm act M (Set.range f) ≤ LinearMap.range L := by
    refine iSup₂_le ?_
    rintro _ ⟨j, rfl⟩ _ ⟨m, hm, rfl⟩
    refine ⟨Pi.single j ⟨m, hm⟩, ?_⟩
    rw [hL, Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      simp [Pi.single_eq_of_ne hb]
    · simp
  obtain ⟨v, rfl⟩ := hle hx
  exact ⟨fun j => (v j : E), fun j => (v j).2, hL v⟩

/- English proof (translation)
Introduce `gl1 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hKE c hc hsm`. Take `⟨m, hm, hcm⟩` from `exists_of_mem_sm_range act M (fun j => r (e j)) _ hsm`. Establish `hW : WOk (fun _ : Finset κ => M) (fun l => act (r l))`. Use `⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩` and prove the remaining obligations. Use `show act (r i) * act (r j) = act (r j) * act (r i)`.

Rewrite using `[← map_mul, ← map_mul, mul_comm]`. Establish `hQ` using `subq S E act κ M r d e hKE`. Establish `hQc : (img e).card = d` using `by simp [img]`. Establish `hmem : ∀ j, e j ∈ img e` using `fun j => by simp [img]`. Establish `hcz : ∀ s : Finset κ, (s.card : ℤ) ≠ d → c s = 0`.

Introduce `s hs`. Establish `h` using `hc.1 s (Set.mem_univ s)`. Simplify `h` using `[hs]`. Establish `hcard : ∀ j, (((img e).erase (e j)).card : ℤ) = (d : ℤ) - 1`. Introduce `j`.

Use `j.pos` as an intermediate fact. Rewrite using `[Finset.card_erase_of_mem (hmem j), hQc]`. Use linear arithmetic over natural numbers and integers. Establish `hinj : ∀ i j, (img e).erase (e i) = (img e).erase (e j) → i = j`. Introduce `i j h`.

Assume the negation of the conclusion as `hij`. Establish `hne : e i ≠ e j` using `fun h' => hij (e.injective h')`. Establish `h1 : e i ∈ (img e).erase (e j)` using `Finset.mem_erase.mpr ⟨hne, hmem i⟩`. Rewrite `h1` using `[← h]`. Conclude with `(Finset.notMem_erase _ _) h1`.

Set `y : Finset κ → E` to `fun s => ∑ j, if s = (img e).erase (e j) then GlobalTheory.cubeSign (img e) (e j) • m j else 0`. Establish `hyv : ∀ j, y ((img e).erase (e j)) = GlobalTheory.cubeSign (img e) (e j) • m j`. Introduce `j`. Use `show (∑ i, if (img e).erase (e j) = (img e).erase (e i) then _ else _) = _`. Rewrite using `[Finset.sum_eq_single j]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Rewrite using `[if_neg fun h => hb (hinj _ _ h).symm]`. Simplify using the standard rewrite rules. Establish `hy0 : ∀ s, (∀ j, s ≠ (img e).erase (e j)) → y s = 0`.

Introduce `s hs`. Conclude with `Finset.sum_eq_zero fun j _ => if_neg (hs j)`. Establish `hycard : ∀ s : Finset κ, (s.card : ℤ) ≠ (d : ℤ) - 1 → y s = 0`. Introduce `s hs`. Use `hy0 s fun j h => hs ?_` and prove the remaining obligations.

Rewrite using `[h, hcard]`. Use `gl1 κ E (fun _ => M) (fun l => act (r l)) (img e) d d hW hQ c hc ?_ ?_` and prove the remaining obligations. Introduce `s hs`. It suffices to derive a contradiction. Apply `hs` to reduce the goal to its premises.

Use `Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := img e))` as an intermediate fact. Rewrite `this` using `[hQc]`. Conclude with `this` after adjusting the coercions. Use `⟨y, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `s _ show y s ∈ if (s.card : ℤ) = (d : ℤ) - 1 then M else ⊥ split_ifs with h`.

Use `Submodule.sum_mem _ fun j _ => ?_ split_ifs` and prove the remaining obligations. Conclude with `zsmul_mem (hm j) _`. Conclude with `M.zero_mem`. Rewrite using `[hycard s h]`. Conclude with `Submodule.zero_mem _`.

Introduce `s hs`. Use `hy0 s fun j h => hs ?_` and prove the remaining obligations. Substitute `h` using the available equality. Rewrite using `[Finset.inter_eq_left.mpr (Finset.erase_subset _ _), hcard]`. Introduce `s hs`.

Establish `hsub : img e ⊆ s`. Establish `h1 : (s ∩ img e) = img e`. Apply `Finset.eq_of_subset_of_card_le Finset.inter_subset_right` to reduce the goal to its premises. Rewrite using `[hQc]`. Conclude with `hs.ge` after adjusting the coercions.

Rewrite using `[← h1]`. Conclude with `Finset.inter_subset_left`. Establish `hwd : ∀ t : Finset κ, wd (wOn (img e) fun l => act (r l)) y t = ∑ i ∈ t, GlobalTheory.cubeSign t i • (wOn (img e) (fun l => act (r l)) i) (y (t.erase i))`. Introduce `t`. Simplify using `[wd, LinearMap.sum_apply]`.

Rewrite using `[hwd]`. Distinguish the cases in `hsQ : s = img e`. Substitute `hsQ` using the available equality. Rewrite using `[hcm]`. Establish `hsum : ∀ F : κ → E, ∑ i ∈ img e, F i = ∑ j, F (e j)` using `fun F => Finset.sum_map _ _ _`.

Rewrite using `[hsum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Establish `hw : wOn (img e) (fun l => act (r l)) (e j) = act (r (e j))` using `if_pos (hmem j)`. Establish `hsq : GlobalTheory.cubeSign (img e) (e j) * GlobalTheory.cubeSign (img e) (e j) = 1`. Rewrite using `[GlobalTheory.cubeSign, ← mul_pow]`.

Simplify using the standard rewrite rules. Rewrite using `[hw, hyv j, map_zsmul, smul_smul, hsq, one_smul]`. Establish `hlt : img e ⊂ s` using `Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hsQ h.symm⟩`. Establish `hgt : d < s.card`. Use `Finset.card_lt_card hlt` as an intermediate fact.

Rewrite `this` using `[hQc]`. Then use the resulting hypothesis. Rewrite using `[hcz s (by omega)]`. Use `Finset.sum_eq_zero fun i hi => ?_` and prove the remaining obligations. Rewrite using `[hycard (s.erase i) ?_]`. Simplify using the standard rewrite rules.

Rewrite using `[Finset.card_erase_of_mem hi]`. Use linear arithmetic over natural numbers and integers.
-/
theorem UpperTheory.Gal.productCup_of_system.koszulTwoInjective_of_gl1 :
    FiltrationBoundaryCriterion → SubQEx → KoszulBoundaryOfComponentMemIdeal := by
  intro gl1 subq S E _ _ _ _ act κ _ _ R M r d e hst hr hKE c hc hsm
  classical
  obtain ⟨m, hm, hcm⟩ := exists_of_mem_sm_range act M (fun j => r (e j)) _ hsm
  have hW : WOk (fun _ : Finset κ => M) (fun l => act (r l)) := by
    refine ⟨fun i j => ?_, fun s i _ x hx => hst _ (hr i) x hx⟩
    show act (r i) * act (r j) = act (r j) * act (r i)
    rw [← map_mul, ← map_mul, mul_comm]
  have hQ := subq S E act κ M r d e hKE
  have hQc : (img e).card = d := by simp [img]
  have hmem : ∀ j, e j ∈ img e := fun j => by simp [img]
  have hcz : ∀ s : Finset κ, (s.card : ℤ) ≠ d → c s = 0 := by
    intro s hs
    have h := hc.1 s (Set.mem_univ s)
    simpa [hs] using h
  have hcard : ∀ j, (((img e).erase (e j)).card : ℤ) = (d : ℤ) - 1 := by
    intro j
    have := j.pos
    rw [Finset.card_erase_of_mem (hmem j), hQc]
    omega
  have hinj : ∀ i j, (img e).erase (e i) = (img e).erase (e j) → i = j := by
    intro i j h
    by_contra hij
    have hne : e i ≠ e j := fun h' => hij (e.injective h')
    have h1 : e i ∈ (img e).erase (e j) := Finset.mem_erase.mpr ⟨hne, hmem i⟩
    rw [← h] at h1
    exact (Finset.notMem_erase _ _) h1
  let y : Finset κ → E := fun s =>
    ∑ j, if s = (img e).erase (e j) then GlobalTheory.cubeSign (img e) (e j) • m j else 0
  have hyv : ∀ j, y ((img e).erase (e j)) = GlobalTheory.cubeSign (img e) (e j) • m j := by
    intro j
    show (∑ i, if (img e).erase (e j) = (img e).erase (e i) then _ else _) = _
    rw [Finset.sum_eq_single j]
    · simp
    · intro b _ hb
      rw [if_neg fun h => hb (hinj _ _ h).symm]
    · simp
  have hy0 : ∀ s, (∀ j, s ≠ (img e).erase (e j)) → y s = 0 := by
    intro s hs
    exact Finset.sum_eq_zero fun j _ => if_neg (hs j)
  have hycard : ∀ s : Finset κ, (s.card : ℤ) ≠ (d : ℤ) - 1 → y s = 0 := by
    intro s hs
    refine hy0 s fun j h => hs ?_
    rw [h, hcard]
  refine gl1 κ E (fun _ => M) (fun l => act (r l)) (img e) d d hW hQ c hc ?_ ?_
  · intro s hs
    exfalso
    apply hs
    have := Finset.card_le_card (Finset.inter_subset_right (s₁ := s) (s₂ := img e))
    rw [hQc] at this
    exact_mod_cast this
  · refine ⟨y, ?_, ?_, ?_⟩
    · intro s _
      show y s ∈ if (s.card : ℤ) = (d : ℤ) - 1 then M else ⊥
      split_ifs with h
      · refine Submodule.sum_mem _ fun j _ => ?_
        split_ifs
        · exact zsmul_mem (hm j) _
        · exact M.zero_mem
      · rw [hycard s h]
        exact Submodule.zero_mem _
    · intro s hs
      refine hy0 s fun j h => hs ?_
      subst h
      rw [Finset.inter_eq_left.mpr (Finset.erase_subset _ _), hcard]
    · intro s hs
      have hsub : img e ⊆ s := by
        have h1 : (s ∩ img e) = img e := by
          apply Finset.eq_of_subset_of_card_le Finset.inter_subset_right
          rw [hQc]
          exact_mod_cast hs.ge
        rw [← h1]
        exact Finset.inter_subset_left
      have hwd : ∀ t : Finset κ, wd (wOn (img e) fun l => act (r l)) y t =
          ∑ i ∈ t, GlobalTheory.cubeSign t i • (wOn (img e) (fun l => act (r l)) i) (y (t.erase i)) := by
        intro t
        simp [wd, LinearMap.sum_apply]
      rw [hwd]
      by_cases hsQ : s = img e
      · subst hsQ
        rw [hcm]
        have hsum : ∀ F : κ → E, ∑ i ∈ img e, F i = ∑ j, F (e j) := fun F =>
          Finset.sum_map _ _ _
        rw [hsum]
        refine Finset.sum_congr rfl fun j _ => ?_
        have hw : wOn (img e) (fun l => act (r l)) (e j) = act (r (e j)) := if_pos (hmem j)
        have hsq : GlobalTheory.cubeSign (img e) (e j) * GlobalTheory.cubeSign (img e) (e j) = 1 := by
          rw [GlobalTheory.cubeSign, ← mul_pow]
          simp
        rw [hw, hyv j, map_zsmul, smul_smul, hsq, one_smul]
      · have hlt : img e ⊂ s := Finset.ssubset_iff_subset_ne.mpr ⟨hsub, fun h => hsQ h.symm⟩
        have hgt : d < s.card := by
          have := Finset.card_lt_card hlt
          rwa [hQc] at this
        rw [hcz s (by omega)]
        refine Finset.sum_eq_zero fun i hi => ?_
        rw [hycard (s.erase i) ?_]
        · simp
        · rw [Finset.card_erase_of_mem hi]
          omega
