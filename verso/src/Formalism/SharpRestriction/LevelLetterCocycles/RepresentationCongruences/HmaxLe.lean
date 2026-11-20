import Formalism.SharpRestriction.LevelLetterCocycles.AdmBoundsBOfAdm
import Formalism.SharpRestriction.LevelLetterCocycles.RepresentationCongruences.TsumThree

noncomputable section

namespace Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo

open Formalism.WeaklyAdmissibleFiltrations Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.MainNotions.ArcLiftingSetup Formalism.MainNotions.N.Ln17

variable {G : Type} [Group G] [TopologicalSpace G] {Qp K₀ K : Type} [Field Qp] [Field K₀] [Field K]
    [Algebra Qp K₀] [Algebra Qp K] [Algebra K₀ K] [IsScalarTower Qp K₀ K]
    {B BdR : Type} [CommRing B] [CommRing BdR] [Algebra Qp B] [Algebra K₀ B] [IsScalarTower Qp K₀ B]
    [Algebra Qp BdR] [Algebra K₀ BdR] [Algebra K BdR] [IsScalarTower Qp K BdR]
    [IsScalarTower K₀ K BdR] [IsScalarTower Qp K₀ BdR]
    {LL O : Type} [Field LL] [Algebra Qp LL] [TopologicalSpace LL] [CommRing O] [Algebra O LL]
    {v : AddValuation LL (WithTop ℚ)} {n : ℕ}
    {PD : PeriodData G Qp K₀ K B BdR}

/- English proof (translation)
Unfold `Formalism.MainNotions.LiftingTheory.Hmax`. Establish `h` using `Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))`. Simplify using `only [ZMod.natCast_zmod_val] at h`. Conclude with `h`.
-/
theorem hmax_le' [NeZero n] (Mi hi : ZMod n → ℕ) (j : ZMod n) :
    Mi j + hi j ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi hi := by
  unfold Formalism.MainNotions.LiftingTheory.Hmax
  have h := Finset.le_sup (f := fun k : ℕ => Mi k + hi k) (Finset.mem_range.2 (ZMod.val_lt j))
  simp only [ZMod.natCast_zmod_val] at h
  exact h

/- English proof (translation)
Take `⟨hp11, hSet, hwb, hηb, hSb, -⟩` from `hB`. Take `⟨hcase, hSur, hηs, hJA, -, hnt, -⟩` from `hSet`. Set `Mi' : ZMod n → ℕ` to `fun i => if up i then η else size i + S`. Set `hi' : ZMod n → ℕ` to `fun i => if up i then size i + S else η`. Establish `hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi'`.

Introduce `i τ hτ a ha`. Establish `h1` using `hJA i τ hτ a ha`. Establish `h2` using `hηs i`. Consider the cases of `hu : up i`. Simplify using `only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢`.

Use `push_cast`. Use linear arithmetic over natural numbers and integers. Simplify using `only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Establish `hwid : ∀ i, Mi' i + hi' i = size i + S + η`. Introduce `i`. Apply the tactic sequence `cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega`. Establish `hsz : ∀ i, size i ≤ b + η`. Introduce `i`.

Distinguish the cases in `ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i`. Conclude with `ht.2`. Use `hnt i ht` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ (b + η + S) + η` using `Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega`.

Take `⟨hs, -⟩` from `hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)`. Establish `hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) = (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ)` using `rfl`. Establish `e0 : c - 1 + ((0 + 1 : ℕ) : ZMod n) = c` using `by push_cast; ring`. Establish `e1 : c - 1 + ((1 + 1 : ℕ) : ZMod n) = c + 1` using `by push_cast; ring`. Establish `hc1w : size (c + 1) ≤ w` using `hnt (c + 1) hc1`.

Establish `ht` using `tsum_three PD.p hp11 (fun a => ((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) + Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3) ((((size c + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNo …`. Rewrite using `[e0, hwid, hcW])`. Use the proof step `(by show _ + _ + _ ≤ _`. Rewrite using `[e1, hwid, hcW]`. Establish `: ((size (c + 1) + S + η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ)`.

Conclude with `(by omega : size (c + 1) + S + η ≤ w + S + η)` after adjusting the coercions. Use the proof step `linarith)`. Use the proof step `(fun a _ => by`. Use `hmax_le' Mi' hi' (c - 1 + ((a + 1 : ℕ) : ZMod n))` as an intermediate fact. Establish `h' : (((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤ Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi'` using `by exact_mod_cast this`.

Use `show _ + _ + _ ≤ _`. Rewrite using `[hcW]`. Use the proof step `linarith)`. Establish `hst` using `hs.trans ht`. Establish `hx : (11 : ℝ) ≤ PD.p` using `by exact_mod_cast hp11`.

Establish `hA : (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) + 1`. Unfold `Formalism.MainNotions.LiftingTheory.AI`. Establish `h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1)` using `div_nonneg (Nat.cast_nonneg _) (by linarith)`. Conclude with `(Nat.ceil_lt_add_one h0).le`. Establish `hη1 : η + 1 ≤ b + η + S` using `by have := hηs c; have := hct.2; omega`.

Establish `key` using `Aa_cut_le PD.p hp11 (b + η + S) w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') (size c + S + η) (w + S + η) hη1 hHle (by have := hct.2; omega) le_rfl _ _ hst hA`. Establish `ec : (((size c + S + η : ℕ) : ℝ)) = (size c : ℝ) + S + η` using `by push_cast; ring`. Rewrite `key` using `[ec]`. Conclude with `key`.
-/
theorem aI_le [NeZero n] [Fintype (K →ₐ[Qp] LL)] (W : LocWach PD LL O v n)
    {T₁ T₂ : LocLat G Qp LL O} (F : LatHom T₁.L T₂.L) {b w S η m : ℕ} {up : ZMod n → Bool}
    {size Mi hi : ZMod n → ℕ} (hB : HypB PD W T₁ T₂ F b w S η m up size Mi hi)
    (CR : ℝ) (hWR : Formalism.MainNotions.LiftingTheory.coreWR W CR) (c : ZMod n)
    (hct : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size c) (hc1 : ¬ Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size (c + 1)) :
    (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤
      ((size c : ℝ) + S + η) / PD.p + 2 * Formalism.MainNotions.N.FrobeniusPowerSeries.Sg PD.p (b + η + S) w S η := by
  obtain ⟨hp11, hSet, hwb, hηb, hSb, -⟩ := hB
  obtain ⟨hcase, hSur, hηs, hJA, -, hnt, -⟩ := hSet
  let Mi' : ZMod n → ℕ := fun i => if up i then η else size i + S
  let hi' : ZMod n → ℕ := fun i => if up i then size i + S else η
  have hJ : Formalism.MainNotions.LiftingTheory.JumpsLet W T₁ Mi' hi' := by
    intro i τ hτ a ha
    have h1 := hJA i τ hτ a ha
    have h2 := hηs i
    cases hu : up i
    · simp only [hu, Mi', hi', Bool.false_eq_true, if_false, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
    · simp only [hu, Mi', hi', if_true, Set.mem_union, Set.mem_Icc] at h1 ⊢
      push_cast
      omega
  have hwid : ∀ i, Mi' i + hi' i = size i + S + η := by
    intro i
    cases hu : up i <;> simp only [hu, Mi', hi', Bool.false_eq_true, if_false, if_true] <;> omega
  have hsz : ∀ i, size i ≤ b + η := by
    intro i
    by_cases ht : Formalism.MainNotions.TruncatedSeriesCountingBounds.Thick b η size i
    · exact ht.2
    · have := hnt i ht; omega
  have hHle : Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' ≤ (b + η + S) + η :=
    Finset.sup_le fun k _ => by rw [hwid]; have := hsz (k : ZMod n); omega
  obtain ⟨hs, -⟩ := hWR hcase T₁ T₂ F Mi' hi' hSur hJ (c - 1)
  have hcW : (Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) =
      (cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') : ℝ) := rfl
  have e0 : c - 1 + ((0 + 1 : ℕ) : ZMod n) = c := by push_cast; ring
  have e1 : c - 1 + ((1 + 1 : ℕ) : ZMod n) = c + 1 := by push_cast; ring
  have hc1w : size (c + 1) ≤ w := hnt (c + 1) hc1
  have ht := tsum_three PD.p hp11
    (fun a => ((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ) +
      Formalism.MainNotions.LiftingTheory.cH PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((size c + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((((w + S + η : ℕ) : ℝ)) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    ((Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' : ℝ) + cW PD.p (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') + 3)
    (fun a => by positivity)
    (by
      show _ + _ + _ ≤ _
      rw [e0, hwid, hcW])
    (by
      show _ + _ + _ ≤ _
      rw [e1, hwid, hcW]
      have : ((size (c + 1) + S + η : ℕ) : ℝ) ≤ ((w + S + η : ℕ) : ℝ) := by
        exact_mod_cast (by omega : size (c + 1) + S + η ≤ w + S + η)
      linarith)
    (fun a _ => by
      have := hmax_le' Mi' hi' (c - 1 + ((a + 1 : ℕ) : ZMod n))
      have h' : (((Mi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) + hi' (c - 1 + ((a + 1 : ℕ) : ZMod n)) : ℕ) : ℝ)) ≤
          Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi' := by exact_mod_cast this
      show _ + _ + _ ≤ _
      rw [hcW]; linarith)
  have hst := hs.trans ht
  have hx : (11 : ℝ) ≤ PD.p := by exact_mod_cast hp11
  have hA : (Formalism.MainNotions.LiftingTheory.AI W F (c - 1) : ℝ) ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) + 1 := by
    unfold Formalism.MainNotions.LiftingTheory.AI
    have h0 : 0 ≤ (Formalism.MainNotions.LiftingTheory.sI W F (c - 1) : ℝ) / ((PD.p : ℝ) - 1) :=
      div_nonneg (Nat.cast_nonneg _) (by linarith)
    exact (Nat.ceil_lt_add_one h0).le
  have hη1 : η + 1 ≤ b + η + S := by have := hηs c; have := hct.2; omega
  have key := Aa_cut_le PD.p hp11 (b + η + S) w S η (Formalism.MainNotions.LiftingTheory.Hmax n Mi' hi') (size c + S + η)
    (w + S + η) hη1 hHle (by have := hct.2; omega) le_rfl _ _ hst hA
  have ec : (((size c + S + η : ℕ) : ℝ)) = (size c : ℝ) + S + η := by push_cast; ring
  rw [ec] at key
  exact key

end Formalism.MainNotions.N.FrobeniusPowerSeries.ArcLengthTwo
