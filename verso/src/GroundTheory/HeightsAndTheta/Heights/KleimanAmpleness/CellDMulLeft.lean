import Mathlib
import GroundTheory.HeightsAndTheta.Heights.KleimanAmpleness.CellLocSys
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization

/- English proof (translation)
Use function extensionality and compare the values at `J`. Simplify using `only [cellD, LinearMap.pi_apply]`. Use `split_ifs with hJ`. Simplify using `only [LinearMap.sum_apply, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Use `split_ifs with h`. Rewrite using `[LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm]`. Both sides reduce to the same expression. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules.
-/
theorem cellD_mul_left (S : Type) [CommRing S] {K : Type} [Fintype K] [LinearOrder K] {ι : K → Type} [∀ k, Fintype (ι k)]
    [∀ k, LinearOrder (ι k)] {Ω : Type} [Field Ω] [Algebra S Ω] (y : (Σ k, ι k) → Ω) (n : ℕ) (r : Ω)
    (t : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω) :
    cellD S y n (fun I => r * t I) = fun J => r * cellD S y n t J := by
  classical
  funext J
  simp only [cellD, LinearMap.pi_apply]
  split_ifs with hJ
  · simp only [LinearMap.sum_apply, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun i _ => ?_
    split_ifs with h
    · rw [LinearMap.smul_apply, LinearMap.smul_apply, mul_smul_comm]
      rfl
    · simp
  · simp

/- English proof (translation)
Introduce `S _ K _ _ ι _ _ Ω _ _ y G R m f u hf hu hsum hR hloc q s hs hds`. Establish `memC : ∀ (H : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) (x : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω), x ∈ cellCOf S H n ↔ ∀ I, x I ∈ H I.1` using `fun H n x => by`. Simplify using `[cellCOf, Submodule.mem_pi]`. Set `J : Ideal R` to `{ carrier := {r | ∃ t ∈ cellCOf S G q, cellD S y q t = fun I => (r : Ω) * s I} add_mem' := by`. Introduce and unpack `a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩`.

Use `⟨ta + tb, Submodule.add_mem _ hta htb, ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, ha, hb]`. Use function extensionality and compare the values at `I`. Simplify using `[add_mul]`. Use the proof step `zero_mem' := ⟨0, Submodule.zero_mem _, by funext I; simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `c a ⟨t, ht, hdt⟩`. Use `⟨fun I => (c : Ω) * t I, (memC _ _ _).2 fun I => hR _ _ c.2 _ ((memC _ _ _).1 ht I), ?_⟩` and prove the remaining obligations. Rewrite using `[cellD_mul_left, hdt]`. Use function extensionality and compare the values at `I`.

Simplify using `[mul_assoc] }`. Establish `hmono : ∀ l (I : ∀ k, Finset (ι k)), Monotone fun n : ℕ => (G I).comap (LinearMap.mulLeft S (f l ^ n))`. Introduce `l I n n' hnn' a ha`. Simplify using `only [Submodule.mem_comap, LinearMap.mulLeft_apply] at ha ⊢`. Establish `: f l ^ n' * a = f l ^ (n' - n) * (f l ^ n * a)`.

Rewrite using `[← mul_assoc, ← pow_add, Nat.sub_add_cancel hnn']`. Rewrite using `[this]`. Conclude with `hR _ _ (pow_mem (hf l) _) _ ha`. Establish `key : ∀ l, ∃ N : ℕ, (⟨f l, hf l⟩ : R) ^ N ∈ J`. Introduce `l`.

Establish `hsl : s ∈ cellCOf S (cellLocSys G (f l)) (q + 1)`. Rewrite `hs`, the goal using `[memC]`. Introduce `I`. Conclude with `(le_iSup (fun n : ℕ => (G I.1).comap (LinearMap.mulLeft S (f l ^ n))) 0) (by simpa [Submodule.mem_comap] using hs I)`. Take `⟨t, ht, hdt⟩` from `hloc l q s hsl hds`.

Establish `hn : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ n : ℕ, f l ^ n * t I ∈ G I.1`. Introduce `I`. Establish `h` using `(memC _ _ _).1 ht I`. Rewrite `h` using `[cellLocSys, Submodule.mem_iSup_of_directed _ (hmono l I.1).directed_le]`. Take `⟨n, hn⟩` from `h`.

Conclude with `⟨n, by simpa [Submodule.mem_comap] using hn⟩`. Use `choose n hn using hn`. Establish `: Finite (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q)` using `by unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell; infer_instance`. Establish `: Fintype (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q)` using `Fintype.ofFinite _`. Use `⟨Finset.univ.sup n, fun I => f l ^ Finset.univ.sup n * t I, (memC _ _ _).2 fun I => ?_, ?_⟩` and prove the remaining obligations.

Use `hmono l I.1 (Finset.le_sup (Finset.mem_univ I) : n I ≤ Finset.univ.sup n)` as an intermediate fact. Conclude with `this (by simpa [Submodule.mem_comap] using hn I)`. Rewrite using `[cellD_mul_left, hdt]`. Use function extensionality and compare the values at `I`. Simplify using the standard rewrite rules.

Establish `hone : (1 : R) ∈ J`. Establish `hrad : J.radical = ⊤`. Rewrite using `[eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]`. Establish `h1 : (1 : R) = ∑ l, (⟨u l, hu l⟩ : R) * ⟨f l, hf l⟩` using `Subtype.ext (by simpa using hsum.symm)`. Rewrite using `[h1]`.

Conclude with `Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (key l)`. Rewrite `hrad` using `[Ideal.radical_eq_top]`. Rewrite using `[hrad]`. Conclude with `Submodule.mem_top`. Take `⟨t, ht, hdt⟩` from `hone`.

Conclude with `⟨t, ht, by rw [hdt]; funext I; simp⟩`.
-/
theorem CellLocGlue.proof : CellLocGlue.Statement := by
  intro S _ K _ _ ι _ _ Ω _ _ y G R m f u hf hu hsum hR hloc q s hs hds
  classical
  have memC : ∀ (H : (∀ k, Finset (ι k)) → Submodule S Ω) (n : ℕ) (x : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι n → Ω),
      x ∈ cellCOf S H n ↔ ∀ I, x I ∈ H I.1 := fun H n x => by
    simp [cellCOf, Submodule.mem_pi]

  let J : Ideal R :=
    { carrier := {r | ∃ t ∈ cellCOf S G q, cellD S y q t = fun I => (r : Ω) * s I}
      add_mem' := by
        rintro a b ⟨ta, hta, ha⟩ ⟨tb, htb, hb⟩
        refine ⟨ta + tb, Submodule.add_mem _ hta htb, ?_⟩
        rw [map_add, ha, hb]
        funext I
        simp [add_mul]
      zero_mem' := ⟨0, Submodule.zero_mem _, by funext I; simp⟩
      smul_mem' := by
        rintro c a ⟨t, ht, hdt⟩
        refine ⟨fun I => (c : Ω) * t I, (memC _ _ _).2 fun I => hR _ _ c.2 _ ((memC _ _ _).1 ht I), ?_⟩
        rw [cellD_mul_left, hdt]
        funext I
        simp [mul_assoc] }

  have hmono : ∀ l (I : ∀ k, Finset (ι k)),
      Monotone fun n : ℕ => (G I).comap (LinearMap.mulLeft S (f l ^ n)) := by
    intro l I n n' hnn' a ha
    simp only [Submodule.mem_comap, LinearMap.mulLeft_apply] at ha ⊢
    have : f l ^ n' * a = f l ^ (n' - n) * (f l ^ n * a) := by
      rw [← mul_assoc, ← pow_add, Nat.sub_add_cancel hnn']
    rw [this]
    exact hR _ _ (pow_mem (hf l) _) _ ha
  have key : ∀ l, ∃ N : ℕ, (⟨f l, hf l⟩ : R) ^ N ∈ J := by
    intro l
    have hsl : s ∈ cellCOf S (cellLocSys G (f l)) (q + 1) := by
      rw [memC] at hs ⊢
      intro I
      exact (le_iSup (fun n : ℕ => (G I.1).comap (LinearMap.mulLeft S (f l ^ n))) 0)
        (by simpa [Submodule.mem_comap] using hs I)
    obtain ⟨t, ht, hdt⟩ := hloc l q s hsl hds
    have hn : ∀ I : ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q, ∃ n : ℕ, f l ^ n * t I ∈ G I.1 := by
      intro I
      have h := (memC _ _ _).1 ht I
      rw [cellLocSys, Submodule.mem_iSup_of_directed _ (hmono l I.1).directed_le] at h
      obtain ⟨n, hn⟩ := h
      exact ⟨n, by simpa [Submodule.mem_comap] using hn⟩
    choose n hn using hn
    have : Finite (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := by unfold ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell; infer_instance
    have : Fintype (ReciprocityTheory.ChartRestriction.G.ArakelovGeometry.KH.Cell K ι q) := Fintype.ofFinite _
    refine ⟨Finset.univ.sup n, fun I => f l ^ Finset.univ.sup n * t I, (memC _ _ _).2 fun I => ?_, ?_⟩
    · have := hmono l I.1 (Finset.le_sup (Finset.mem_univ I) : n I ≤ Finset.univ.sup n)
      exact this (by simpa [Submodule.mem_comap] using hn I)
    · rw [cellD_mul_left, hdt]
      funext I
      simp
  have hone : (1 : R) ∈ J := by
    have hrad : J.radical = ⊤ := by
      rw [eq_top_iff, ← Ideal.span_singleton_one, Ideal.span_le, Set.singleton_subset_iff]
      have h1 : (1 : R) = ∑ l, (⟨u l, hu l⟩ : R) * ⟨f l, hf l⟩ :=
        Subtype.ext (by simpa using hsum.symm)
      rw [h1]
      exact Ideal.sum_mem _ fun l _ => Ideal.mul_mem_left _ _ (key l)
    rw [Ideal.radical_eq_top] at hrad
    rw [hrad]
    exact Submodule.mem_top
  obtain ⟨t, ht, hdt⟩ := hone
  exact ⟨t, ht, by rw [hdt]; funext I; simp⟩

end GroundTheory.Heights₂.Heights.Kleiman.SectionsOverLocalization
