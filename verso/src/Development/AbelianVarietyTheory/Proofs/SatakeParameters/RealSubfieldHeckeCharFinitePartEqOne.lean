import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.EqOneOfMemLev

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host
open GlobalTheory.HeckeUnrExt
open GlobalTheory.IndefiniteRowSideFullHecke.UnitaryHeckeCharacterIdele (ideleMap ideleConj finiteCompletionMap)

namespace GlobalTheory.HeckeFinTriv

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [Nat.cast_zero, map_zero]`. Conclude with `zero_le`. Consider the case `succ n ih`. Rewrite using `[Nat.cast_succ]`.

Conclude with `Valuation.map_add_le _ ih (by rw [map_one])`.
-/
theorem valued_natCast_le_one {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) (n : ℕ) :
    Valued.v (n : v.adicCompletion K) ≤ 1 := by
  induction n with
  | zero => rw [Nat.cast_zero, map_zero]; exact zero_le
  | succ n ih =>
    rw [Nat.cast_succ]
    exact Valuation.map_add_le _ ih (by rw [map_one])

/- English proof (translation)
Take `⟨k, rfl⟩` from `h`. Rewrite using `[Nat.cast_mul, map_mul]`. Conclude with `mul_le_of_le_one_right' (valued_natCast_le_one v k)`.
-/
theorem valued_natCast_le_of_dvd {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {M N : ℕ}
    (h : M ∣ N) : Valued.v (N : v.adicCompletion K) ≤ Valued.v (M : v.adicCompletion K) := by
  obtain ⟨k, rfl⟩ := h
  rw [Nat.cast_mul, map_mul]
  exact mul_le_of_le_one_right' (valued_natCast_le_one v k)

/- English proof (translation)
Introduce `E _ _ _ ψ M hlev hns w₀ N hMN b hb`. Establish `he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0` using `fun w => Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot`. Establish `hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w = finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E))))` using `fun w => rfl`. Establish `hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v` using `fun v => by haveI := v.isPrime`. Take `⟨⟨P, hP, hP'⟩⟩` from `(inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))`.

Conclude with `⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩`. Establish `hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1` using `fun v => by`. Take `⟨w, rfl⟩` from `hs v`. Establish `h` using `hb.1 w`. Express the relevant statement in the definitionally equal form `Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h`.

Rewrite `h` using `[hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)]`. Conclude with `h`. Establish `hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ → Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))` using `fun w h1 h2 => by`. Establish `h` using `hb.2 w ⟨h1, h2⟩`. Express the relevant statement in the definitionally equal form `Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h`.

Rewrite `h` using `[hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w), GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_le_pow_iff_left₀ zero_le zero_ …`. Then use the resulting hypothesis. Use `GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_` and prove the remaining obligations. Introduce `v x hx`. Rewrite `hx` using `[GlobalTheory.Mem.Chr.finPartI_snd]`. Establish `hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1` using `by rw [hx]; exact hunit v`.

Distinguish the cases in `hu : ψ.UnrAt v`. Conclude with `hu x hxu`. Take `⟨w, hw⟩` from `hs v`. Establish `hsp : GlobalTheory.UnitaryBC.IsSplitAt w`. Assume the negation of the conclusion as `hn`.

Conclude with `hu (hw ▸ hns w hn)`. Take `⟨u, hu1, hu2⟩` from `hsp`. Establish `hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v`. Distinguish the cases in `h0 : w = w₀`. Use `⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩` and prove the remaining obligations.

Conclude with `⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩`. Take `⟨w', hw'1, hw'2, rfl⟩` from `hsp'`. Establish `hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤ Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))`. Rewrite using `[hx]`. Use `(hcong w' hw'1 hw'2).trans ?_` and prove the remaining obligations.

Establish `e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))`. Rewrite using `[← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `valued_natCast_le_of_dvd _ hMN`.

Apply `hlev` to reduce the goal to its premises. Introduce `P`. Distinguish the cases in `hP : P = w'.under (𝓞 (maximalRealSubfield E))`. Substitute `hP` using the available equality. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_self]`.

Conclude with `hxu`. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]`. Conclude with `map_one _`. Introduce `w`. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_fst]`.

Both sides reduce to the same expression. Introduce `P`. Distinguish the cases in `hP : P = w'.under (𝓞 (maximalRealSubfield E))`. Substitute `hP` using the available equality. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_self]`.

Conclude with `hxc`. Rewrite using `[GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]`. Conclude with `zero_le`.
-/
theorem finPart_eq_one : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (ψ : HChar (maximalRealSubfield E)) (M : ℕ), (∀ a : Ideles (maximalRealSubfield E), a ∈ GlobalTheory.Mem.Chr.unitIdl (maximalRealSubfield E) → (∀ w, (a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).1 w = 1) → (∀ P : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v ((a : AdeleRing (𝓞 (maximalRealSubfield E)) (maximalRealSubfield E)).2 P - 1) ≤ Valued.v ((M : maximalRealSubfield E) : P.adicCompletion (maximalRealSubfield E))) → ψ.1 a = 1) → (∀ w : HeightOneSpectrum (𝓞 E), ¬ GlobalTheory.UnitaryBC.IsSplitAt w → ψ.UnrAt (w.under (𝓞 (maximalRealSubfield E)))) → ∀ (w₀ : HeightOneSpectrum (𝓞 E)) (N : ℕ), M ∣ N → ∀ b : Ideles (maximalRealSubfield E), ideleMap (maximalRealSubfield E) E b ∈ levT E {w | GlobalTheory.UnitaryBC.IsSplitAt w ∧ w ≠ w₀} N → ψ.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b) = 1 := by
  intro E _ _ _ ψ M hlev hns w₀ N hMN b hb
  have he : ∀ w : HeightOneSpectrum (𝓞 E), (w.under (𝓞 (maximalRealSubfield E))).asIdeal.ramificationIdx' w.asIdeal ≠ 0 := fun w =>
    Ideal.IsDedekindDomain.ramificationIdx'_ne_zero_of_liesOver w.asIdeal (w.under (𝓞 (maximalRealSubfield E))).ne_bot
  have hc : ∀ w : HeightOneSpectrum (𝓞 E), (ideleMap (maximalRealSubfield E) E b).val.2 w =
      finiteCompletionMap (maximalRealSubfield E) E w (b.val.2 (w.under (𝓞 (maximalRealSubfield E)))) := fun w => rfl
  have hs : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), ∃ w : HeightOneSpectrum (𝓞 E), w.under (𝓞 (maximalRealSubfield E)) = v := fun v => by
    haveI := v.isPrime
    obtain ⟨⟨P, hP, hP'⟩⟩ := (inferInstance : Nonempty (v.asIdeal.primesOver (𝓞 E)))
    exact ⟨⟨P, hP, Ideal.ne_bot_of_liesOver_of_ne_bot v.ne_bot P⟩, HeightOneSpectrum.ext hP'.over.symm⟩

  have hunit : ∀ v : HeightOneSpectrum (𝓞 (maximalRealSubfield E)), Valued.v (b.val.2 v) = 1 := fun v => by
    obtain ⟨w, rfl⟩ := hs v
    have h := hb.1 w
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w) = 1 at h
    rw [hc, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, pow_eq_one_iff_of_nonneg zero_le (he w)] at h
    exact h

  have hcong : ∀ w : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w → w ≠ w₀ →
      Valued.v (b.val.2 (w.under (𝓞 (maximalRealSubfield E))) - 1) ≤ Valued.v (N : (w.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := fun w h1 h2 => by
    have h := hb.2 w ⟨h1, h2⟩
    change Valued.v ((ideleMap (maximalRealSubfield E) E b).val.2 w - 1) ≤ _ at h
    rwa [hc, ← map_one (finiteCompletionMap (maximalRealSubfield E) E w), ← map_sub, ← map_natCast (finiteCompletionMap (maximalRealSubfield E) E w),
      GlobalTheory.UpIdeleMod.valued_finiteCompletionMap, GlobalTheory.UpIdeleMod.valued_finiteCompletionMap,
      pow_le_pow_iff_left₀ zero_le zero_le (he w)] at h
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local (maximalRealSubfield E) ψ.1 ψ.2.1 (GlobalTheory.Mem.Chr.finPartI (maximalRealSubfield E) b)
    (GlobalTheory.Mem.Chr.finPartI_mem_unitIdl.2 hunit) (fun w => by rw [GlobalTheory.Mem.Chr.finPartI_fst]; rfl) ?_
  intro v x hx
  rw [GlobalTheory.Mem.Chr.finPartI_snd] at hx
  have hxu : Valued.v (x : v.adicCompletion (maximalRealSubfield E)) = 1 := by rw [hx]; exact hunit v
  by_cases hu : ψ.UnrAt v
  · exact hu x hxu
  obtain ⟨w, hw⟩ := hs v
  have hsp : GlobalTheory.UnitaryBC.IsSplitAt w := by
    by_contra hn
    exact hu (hw ▸ hns w hn)
  obtain ⟨u, hu1, hu2⟩ := hsp
  have hsp' : ∃ w' : HeightOneSpectrum (𝓞 E), GlobalTheory.UnitaryBC.IsSplitAt w' ∧ w' ≠ w₀ ∧ w'.under (𝓞 (maximalRealSubfield E)) = v := by
    by_cases h0 : w = w₀
    · refine ⟨u, ⟨w, fun e => hu1 e.symm, hu2.symm⟩, h0 ▸ hu1, hu2.trans hw⟩
    · exact ⟨w, ⟨u, hu1, hu2⟩, h0, hw⟩
  obtain ⟨w', hw'1, hw'2, rfl⟩ := hsp'
  have hxc : Valued.v ((x : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) - 1) ≤
      Valued.v ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
    rw [hx]
    refine (hcong w' hw'1 hw'2).trans ?_
    have e : ((M : (maximalRealSubfield E)) : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) = (M : (w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E)) := by
      rw [← map_natCast (algebraMap (maximalRealSubfield E) ((w'.under (𝓞 (maximalRealSubfield E))).adicCompletion (maximalRealSubfield E))) M]; rfl
    rw [e]
    exact valued_natCast_le_of_dvd _ hMN
  apply hlev
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxu
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP]
      exact map_one _
  · intro w
    rw [GlobalTheory.HeckeProduct.localIdele_fst]
    rfl
  · intro P
    by_cases hP : P = w'.under (𝓞 (maximalRealSubfield E))
    · subst hP
      rw [GlobalTheory.HeckeProduct.localIdele_snd_self]
      exact hxc
    · rw [GlobalTheory.HeckeProduct.localIdele_snd_ne (maximalRealSubfield E) _ _ hP, sub_self, map_zero]
      exact zero_le

end GlobalTheory.HeckeFinTriv
