import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.IsGenericFlag

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

namespace GlobalTheory.CompanionTheory.Ar

namespace FlagGr

variable {Ω : Type} [Field Ω] {E : Type} [AddCommGroup E] [Module Ω E] {r : ℕ}

/- English proof (translation)
Take `⟨l, hl, hl'⟩` from `(Finsupp.mem_span_image_iff_linearCombination Ω).1 h`. Establish `h1 : ∑ k, (l k) • b k = ∑ k, c k • b k`. Rewrite using `[← hl', Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]`. Establish `h2` using `(Fintype.linearIndependent_iff.1 hb) (fun k => l k - c k) (by simp [sub_smul, Finset.sum_sub_distrib, h1]) k`. Establish `h3 : l k = 0` using `(Finsupp.mem_supported' Ω l).1 hl k hk`.

Simplify `h2` using `[h3]`.
-/
theorem coeff_eq_zero {b : Fin r → E} (hb : LinearIndependent Ω b) {s : ℕ} (c : Fin r → Ω)
    (h : ∑ k, c k • b k ∈ flagStep Ω b s) (k : Fin r) (hk : ¬ (k : ℕ) < s) : c k = 0 := by
  obtain ⟨l, hl, hl'⟩ := (Finsupp.mem_span_image_iff_linearCombination Ω).1 h
  have h1 : ∑ k, (l k) • b k = ∑ k, c k • b k := by
    rw [← hl', Finsupp.linearCombination_apply, Finsupp.sum_fintype _ _ (by simp)]
  have h2 := (Fintype.linearIndependent_iff.1 hb) (fun k => l k - c k)
    (by simp [sub_smul, Finset.sum_sub_distrib, h1]) k
  have h3 : l k = 0 := (Finsupp.mem_supported' Ω l).1 hl k hk
  simpa [h3] using h2

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨k, hk, rfl⟩`.
-/
theorem mem_step (b : Fin r → E) {s : ℕ} {k : Fin r} (hk : (k : ℕ) < s) : b k ∈ flagStep Ω b s :=
  Submodule.subset_span ⟨k, hk, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)`.
-/
theorem step_mono (b : Fin r → E) {s s' : ℕ} (h : s ≤ s') : flagStep Ω b s ≤ flagStep Ω b s' :=
  Submodule.span_mono (Set.image_mono fun _ hk => lt_of_lt_of_le hk h)

/- English proof (translation)
Use `coeff_eq_zero hb (s := i) (Pi.single i t) (by simpa [Pi.single_apply] using h) i (lt_irrefl _)` as an intermediate fact. Simplify using `using this`.
-/
theorem eq_zero_of_smul_mem {b : Fin r → E} (hb : LinearIndependent Ω b) (i : Fin r) {t : Ω}
    (h : t • b i ∈ flagStep Ω b i) : t = 0 := by
  have := coeff_eq_zero hb (s := i) (Pi.single i t) (by simpa [Pi.single_apply] using h) i (lt_irrefl _)
  simpa using this

/- English proof (translation)
Unfold `flagStep`. Use `congr 1`. Use extensionality with `x`. Simplify using the standard rewrite rules.
-/
theorem step_top (b : Fin r → E) : flagStep Ω b r = Submodule.span Ω (Set.range b) := by
  unfold flagStep
  congr 1
  ext x
  simp

/- English proof (translation)
Use extensionality with `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, rfl⟩`. Conclude with `⟨Fin.castLE hs k, k.2, rfl⟩`. Introduce and unpack `⟨k, hk, rfl⟩`.

Conclude with `⟨⟨k, hk⟩, rfl⟩`.
-/
theorem range_castLE (b : Fin r → E) {s : ℕ} (hs : s ≤ r) :
    Set.range (b ∘ Fin.castLE hs) = b '' {k | (k : ℕ) < s} := by
  ext x
  constructor
  · rintro ⟨k, rfl⟩
    exact ⟨Fin.castLE hs k, k.2, rfl⟩
  · rintro ⟨k, hk, rfl⟩
    exact ⟨⟨k, hk⟩, rfl⟩

/- English proof (translation)
Establish `hs : b '' {k : Fin r | (k : ℕ) < i + 1} = insert (b i) (b '' {k : Fin r | (k : ℕ) < i})`. Rewrite using `[← Set.image_insert_eq]`. Use `congr 1`. Use extensionality with `k`. Simplify using `only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]`.

Use linear arithmetic over natural numbers and integers. Unfold `flagStep at he`. Rewrite `he` using `[hs, Submodule.mem_span_insert]`. Take `⟨t, z, hz, rfl⟩` from `he`. Conclude with `⟨t, by simpa [flagStep] using hz⟩`.
-/
theorem exists_diag (b : Fin r → E) (i : Fin r) {e : E} (he : e ∈ flagStep Ω b (i + 1)) :
    ∃ t : Ω, e - t • b i ∈ flagStep Ω b i := by
  have hs : b '' {k : Fin r | (k : ℕ) < i + 1} = insert (b i) (b '' {k : Fin r | (k : ℕ) < i}) := by
    rw [← Set.image_insert_eq]
    congr 1
    ext k
    simp only [Set.mem_setOf_eq, Set.mem_insert_iff, Fin.ext_iff]
    omega
  unfold flagStep at he
  rw [hs, Submodule.mem_span_insert] at he
  obtain ⟨t, z, hz, rfl⟩ := he
  exact ⟨t, by simpa [flagStep] using hz⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `e ⟨he, he'⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 he`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `hk : (k : ℕ) < s`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)`. Establish `h0 : (c k : Ω) = 0` using `coeff_eq_zero hb (fun k => (c k : Ω)) he' k hk`. Establish `: c k = 0` using `Subtype.ext h0`. Simplify using `[this]`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨k, hk, rfl⟩`. Conclude with `⟨Submodule.subset_span ⟨k, rfl⟩, mem_step b hk⟩`.
-/
theorem span_inf_step (R : Subring Ω) {b : Fin r → E} (hb : LinearIndependent Ω b) (s : ℕ) :
    Submodule.span R (Set.range b) ⊓ (flagStep Ω b s).restrictScalars R =
      Submodule.span R (b '' {k | (k : ℕ) < s}) := by
  apply le_antisymm
  · rintro e ⟨he, he'⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    refine Submodule.sum_mem _ fun k _ => ?_
    by_cases hk : (k : ℕ) < s
    · exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, hk, rfl⟩)
    · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) he' k hk
      have : c k = 0 := Subtype.ext h0
      simp [this]
  · refine Submodule.span_le.2 ?_
    rintro _ ⟨k, hk, rfl⟩
    exact ⟨Submodule.subset_span ⟨k, rfl⟩, mem_step b hk⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `u ⟨e, he, hu⟩`. Take `⟨c, rfl⟩` from `(Submodule.mem_span_range_iff_exists_fun R).1 he`. Establish `h1 : ∑ k, c k • b k ∈ flagStep Ω b (i + 1)`.

Rewrite using `[hF]`. Use `Submodule.add_mem _ (step_mono b₀ (Nat.le_succ _) hu) (Submodule.smul_mem _ u (mem_step b₀ (Nat.lt_succ_self (i : ℕ))))` as an intermediate fact. Simplify using `using this`. Establish `h2 : ∑ k, c k • b k - (c i : Ω) • b i ∈ flagStep Ω b₀ i`. Rewrite using `[← hF, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]`.

Establish `: ∑ k ∈ Finset.univ.erase i, c k • b k ∈ flagStep Ω b i`. Use `Submodule.sum_mem _ fun k hk => ?_` and prove the remaining obligations. Establish `hki : k ≠ i` using `Finset.ne_of_mem_erase hk`. Express the relevant statement in the definitionally equal form `(c k : Ω) • b k ∈ _`. Distinguish the cases in `hk' : (k : ℕ) < i`.

Conclude with `Submodule.smul_mem _ _ (mem_step b hk')`. Establish `h0 : (c k : Ω) = 0` using `coeff_eq_zero hb (fun k => (c k : Ω)) h1 k (by`. Establish `: (k : ℕ) ≠ i` using `fun h => hki (Fin.ext h)`. Use the proof step `omega)`. Simplify using `[h0]`.

Establish `e2 : c i • b i = (c i : Ω) • b i` using `rfl`. Rewrite using `[e2, add_sub_cancel_right]`. Conclude with `this`. Establish `h3 : ((c i : Ω) * t - u) • b₀ i ∈ flagStep Ω b₀ i`. Use `Submodule.sub_mem _ (Submodule.sub_mem _ hu h2) (Submodule.smul_mem _ (c i : Ω) ht)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Rewrite using `[sub_smul, smul_sub, mul_smul]`. Normalize the expressions using the abelian group laws. Establish `h4` using `eq_zero_of_smul_mem hb₀ i h3`. Conclude with `Submodule.mem_span_singleton.2 ⟨c i, sub_eq_zero.1 h4⟩`.

Use `Submodule.span_mono ?_` and prove the remaining obligations. Introduce and unpack `_ rfl`. Conclude with `⟨b i, Submodule.subset_span ⟨i, rfl⟩, ht⟩`.
-/
theorem gr_eq (R : Subring Ω) {b b₀ : Fin r → E} (hb : LinearIndependent Ω b) (hb₀ : LinearIndependent Ω b₀)
    (hF : ∀ i, flagStep Ω b i = flagStep Ω b₀ i) (i : Fin r) {t : Ω} (ht : b i - t • b₀ i ∈ flagStep Ω b₀ i) :
    Submodule.span R {u : Ω | ∃ e ∈ Submodule.span R (Set.range b), e - u • b₀ i ∈ flagStep Ω b₀ i} =
      Submodule.span R {t} := by
  apply le_antisymm
  · refine Submodule.span_le.2 ?_
    rintro u ⟨e, he, hu⟩
    obtain ⟨c, rfl⟩ := (Submodule.mem_span_range_iff_exists_fun R).1 he
    have h1 : ∑ k, c k • b k ∈ flagStep Ω b (i + 1) := by
      rw [hF]
      have := Submodule.add_mem _ (step_mono b₀ (Nat.le_succ _) hu)
        (Submodule.smul_mem _ u (mem_step b₀ (Nat.lt_succ_self (i : ℕ))))
      simpa using this
    have h2 : ∑ k, c k • b k - (c i : Ω) • b i ∈ flagStep Ω b₀ i := by
      rw [← hF, ← Finset.sum_erase_add _ _ (Finset.mem_univ i)]
      have : ∑ k ∈ Finset.univ.erase i, c k • b k ∈ flagStep Ω b i := by
        refine Submodule.sum_mem _ fun k hk => ?_
        have hki : k ≠ i := Finset.ne_of_mem_erase hk
        change (c k : Ω) • b k ∈ _
        by_cases hk' : (k : ℕ) < i
        · exact Submodule.smul_mem _ _ (mem_step b hk')
        · have h0 : (c k : Ω) = 0 := coeff_eq_zero hb (fun k => (c k : Ω)) h1 k (by
            have : (k : ℕ) ≠ i := fun h => hki (Fin.ext h)
            omega)
          simp [h0]
      have e2 : c i • b i = (c i : Ω) • b i := rfl
      rw [e2, add_sub_cancel_right]
      exact this
    have h3 : ((c i : Ω) * t - u) • b₀ i ∈ flagStep Ω b₀ i := by
      have := Submodule.sub_mem _ (Submodule.sub_mem _ hu h2) (Submodule.smul_mem _ (c i : Ω) ht)
      convert this using 1
      rw [sub_smul, smul_sub, mul_smul]
      abel
    have h4 := eq_zero_of_smul_mem hb₀ i h3
    exact Submodule.mem_span_singleton.2 ⟨c i, sub_eq_zero.1 h4⟩
  · refine Submodule.span_mono ?_
    rintro _ rfl
    exact ⟨b i, Submodule.subset_span ⟨i, rfl⟩, ht⟩

end FlagGr

open FlagGr in

/- English proof (translation)
Introduce `X Ω _ ξ E _ _ L T r b₀ hb₀ hL`. Use `⟨fun p hp => ?_, fun i p hp => ?_, fun s hs p hp => ?_⟩` and prove the remaining obligations. Take `⟨U, hU, b, hF, hb⟩` from `hL p hp`. Conclude with `⟨U, hU, b, by rw [← step_top, hF, step_top], hb⟩`. Take `⟨U, hU, b, hF, hb⟩` from `hL p hp`.

Establish `hli` using `(hb p hp hU).1`. Take `⟨t, ht⟩` from `exists_diag b₀ i (e := b i) (hF _ ▸ mem_step b (Nat.lt_succ_self (i : ℕ)))`. Establish `ht0 : t ≠ 0`. Introduce and unpack `rfl`. Establish `: (1 : Ω) • b i ∈ flagStep Ω b i` using `by simpa [hF] using ht`.

Conclude with `one_ne_zero (eq_zero_of_smul_mem hli i this)`. Establish `hr : Set.range (fun _ : Fin 1 => t) = {t}` using `Set.range_const`. Use `⟨U, hU, fun _ => t, ?_, fun q hq hqU => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[hr, eq_top_iff]`. Introduce `x _`.

Conclude with `Submodule.mem_span_singleton.2 ⟨x / t, by simp [ht0]⟩`. Conclude with `linearIndependent_unique_iff.2 ht0`. Rewrite using `[hr]`. Unfold `Lat.gr`. Rewrite using `[(hb q hq hqU).2]`.

Conclude with `gr_eq _ hli hb₀ hF i ht`. Take `⟨U, hU, b, hF, hb⟩` from `hL p hp`. Establish `hli` using `(hb p hp hU).1`. Use `⟨U, hU, b ∘ Fin.castLE hs, ?_, fun q hq hqU => ⟨hli.comp _ (Fin.castLE_injective hs), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[range_castLE, ← hF]`.

Both sides reduce to the same expression. Unfold `Lat.inter`. Rewrite using `[(hb q hq hqU).2, range_castLE, ← hF]`. Conclude with `span_inf_step _ hli s`.
-/
theorem Lat.IsFlagVBOn.isVBOn_gr_inter : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (E : Type) [AddCommGroup E] [Module Ω E] (L : Lat ξ E) (T : Set (Cpt ξ)) (r : ℕ) (b₀ : Fin r → E), LinearIndependent Ω b₀ → L.IsFlagVBOn T b₀ → L.IsVBOn T r (Submodule.span Ω (Set.range b₀)) ∧ (∀ i, (L.gr b₀ i).IsVBOn T 1 ⊤) ∧ ∀ s : ℕ, s ≤ r → (L.inter (flagStep Ω b₀ s)).IsVBOn T s (flagStep Ω b₀ s) := by
  intro X Ω _ ξ E _ _ L T r b₀ hb₀ hL
  refine ⟨fun p hp => ?_, fun i p hp => ?_, fun s hs p hp => ?_⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    exact ⟨U, hU, b, by rw [← step_top, hF, step_top], hb⟩
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    obtain ⟨t, ht⟩ := exists_diag b₀ i (e := b i) (hF _ ▸ mem_step b (Nat.lt_succ_self (i : ℕ)))
    have ht0 : t ≠ 0 := by
      rintro rfl
      have : (1 : Ω) • b i ∈ flagStep Ω b i := by simpa [hF] using ht
      exact one_ne_zero (eq_zero_of_smul_mem hli i this)
    have hr : Set.range (fun _ : Fin 1 => t) = {t} := Set.range_const
    refine ⟨U, hU, fun _ => t, ?_, fun q hq hqU => ⟨?_, ?_⟩⟩
    · rw [hr, eq_top_iff]
      intro x _
      exact Submodule.mem_span_singleton.2 ⟨x / t, by simp [ht0]⟩
    · exact linearIndependent_unique_iff.2 ht0
    · rw [hr]
      unfold Lat.gr
      rw [(hb q hq hqU).2]
      exact gr_eq _ hli hb₀ hF i ht
  · obtain ⟨U, hU, b, hF, hb⟩ := hL p hp
    have hli := (hb p hp hU).1
    refine ⟨U, hU, b ∘ Fin.castLE hs, ?_, fun q hq hqU => ⟨hli.comp _ (Fin.castLE_injective hs), ?_⟩⟩
    · rw [range_castLE, ← hF]
      rfl
    · unfold Lat.inter
      rw [(hb q hq hqU).2, range_castLE, ← hF]
      exact span_inf_step _ hli s

end GlobalTheory.CompanionTheory.Ar
