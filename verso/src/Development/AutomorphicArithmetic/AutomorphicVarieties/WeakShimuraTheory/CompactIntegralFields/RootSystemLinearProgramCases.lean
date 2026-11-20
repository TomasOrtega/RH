import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.RedIdeal

open IsLocalRing Polynomial UpperTheory.V.Alg UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws

/- English proof (translation)
Apply the tactic sequence `by_cases al <;> by_cases mal <;> by_cases be <;> by_cases mbe <;> by_cases th <;> by_cases mth <;>`. Apply the tactic sequence `by_cases ps <;> by_cases mps <;> simp_all <;> omega`.
-/
private theorem sign_pattern_case_split (A B : ℤ) (al mal be mbe th mth ps mps : Prop)
    (h1 : al → A < 0) (h2 : mal → 0 < A) (h3 : be → B < A) (h4 : mbe → A < B) (h5 : th → A + B < 0)
    (h6 : mth → 0 < A + B) (h7 : ps → B < 0) (h8 : mps → 0 ≤ B)
    (m1 : mal ∨ be ∨ mth) (m2 : mps ∨ mbe ∨ mth) (m3 : mps ∨ al ∨ mbe) (m4 : mps ∨ mal ∨ mth) :
    (be ∧ mps ∧ ¬ al ∧ ¬ mbe ∧ ¬ th ∧ ¬ ps) ∨ (mal ∧ mps ∧ ¬ al ∧ ¬ be ∧ ¬ mbe ∧ ¬ th ∧ ¬ ps) ∨
      (mth ∧ mps ∧ ¬ al ∧ ¬ mal ∧ ¬ be ∧ ¬ mbe ∧ ¬ th ∧ ¬ ps) ∨ (mal ∧ mbe ∧ ¬ al ∧ ¬ be ∧ ¬ th ∧ ¬ ps) ∨
      (mth ∧ mbe ∧ ¬ al ∧ ¬ mal ∧ ¬ be ∧ ¬ th ∧ ¬ ps) ∨ (mth ∧ al ∧ ¬ mal ∧ ¬ be ∧ ¬ th ∧ ¬ ps) := by
  by_cases al <;> by_cases mal <;> by_cases be <;> by_cases mbe <;> by_cases th <;> by_cases mth <;>
    by_cases ps <;> by_cases mps <;> simp_all <;> omega

/- English proof (translation)
Establish `: roots = {(1, 0), (-1, 0), (-1, 1), (1, -1), (1, 1), (-1, -1), (0, 1), (0, -1)}` using `by decide`. Simplify using `[this]`.
-/
private theorem mem_rank_two_roots_iff (w : ℤ × ℤ) : w ∈ roots ↔ w = (1, 0) ∨ w = (-1, 0) ∨ w = (-1, 1) ∨ w = (1, -1) ∨ w = (1, 1) ∨
    w = (-1, -1) ∨ w = (0, 1) ∨ w = (0, -1) := by
  have : roots = {(1, 0), (-1, 0), (-1, 1), (1, -1), (1, 1), (-1, -1), (0, 1), (0, -1)} := by decide
  simp [this]

/- English proof (translation)
Substitute `hS` using the available equality. Establish `key` using `sign_pattern_case_split A B (T (1, 0)) (T (-1, 0)) (T (-1, 1)) (T (1, -1)) (T (1, 1)) (T (-1, -1)) (T (0, 1)) (T (0, -1)) (fun h => by have := sg _ (by decide) h; dsimp only at this; omega) (fun h => by have := sg _ (by decide) h; dsimp only at this; omega) (fun h => by have := s …`. Apply the tactic sequence `refine key.imp ?_ (Or.imp ?_ (Or.imp ?_ (Or.imp ?_ (Or.imp ?_ ?_)))) <;> rintro ⟨a, b, c⟩ <;>`. Apply the tactic sequence `refine ⟨⟨by decide, a⟩, ⟨by decide, b⟩, ?_⟩ <;> casesm* _ ∧ _ <;> rintro w ⟨hw, ht⟩ <;>`. Apply the tactic sequence `rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>`.

Apply the tactic sequence `first | exact absurd ht ‹_› | (simp [nP, qQ, nM, wAl, wBe, wTh, wPs]; done)`.
-/
private theorem finite_sign_pattern_cases (A B : ℤ) (T : ℤ × ℤ → Prop) (Si : Set (ℤ × ℤ)) (hS : Si = {w | w ∈ roots ∧ T w})
    (sg : ∀ w, w ≠ -wPs → T w → w.1 * A + w.2 * B < 0) (s0 : T (0, -1) → 0 ≤ B)
    (m1 : T (-1, 0) ∨ T (-1, 1) ∨ T (-1, -1)) (m2 : T (0, -1) ∨ T (1, -1) ∨ T (-1, -1))
    (m3 : T (0, -1) ∨ T (1, 0) ∨ T (1, -1)) (m4 : T (0, -1) ∨ T (-1, 0) ∨ T (-1, -1)) :
      ((wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP) ∨ (-wAl ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ qQ) ∨ (-wTh ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ {-wTh, -wPs}) ∨
          (-wAl ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ nM) ∨ (-wTh ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe}) ∨ (-wTh ∈ Si ∧ wAl ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe, wAl})) := by
  subst hS
  have key := sign_pattern_case_split A B (T (1, 0)) (T (-1, 0)) (T (-1, 1)) (T (1, -1)) (T (1, 1)) (T (-1, -1)) (T (0, 1)) (T (0, -1))
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    (fun h => by have := sg _ (by decide) h; dsimp only at this; omega)
    s0 m1 m2 m3 m4
  refine key.imp ?_ (Or.imp ?_ (Or.imp ?_ (Or.imp ?_ (Or.imp ?_ ?_)))) <;> rintro ⟨a, b, c⟩ <;>
    refine ⟨⟨by decide, a⟩, ⟨by decide, b⟩, ?_⟩ <;> casesm* _ ∧ _ <;> rintro w ⟨hw, ht⟩ <;>
    rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;>
    first | exact absurd ht ‹_› | (simp [nP, qQ, nM, wAl, wBe, wTh, wPs]; done)

/- English proof (translation)
Set `F : ℤ → ℤ → Prop` to `fun A B => ∀ w ∈ roots, ∀ k, C w k → 0 ≤ w.1 * A + w.2 * B + 2 * k`. Choose the witnesses or unpack the hypotheses as in `⟨B, ⟨A0, hA0⟩, hB⟩ : ∃ B, (∃ A, F A B) ∧ ∀ B', (∃ A, F A B') → B' ≤ B := by`. Use `Int.exists_greatest_of_bdd ?_ ⟨0, 0, fun w _ k _ => by simp⟩` and prove the remaining obligations. Take `⟨k, hk⟩` from `h1`. Use `⟨2 * k, fun z ⟨A, hz⟩ => ?_⟩` and prove the remaining obligations.

Use `hz _ (by decide) k hk` as an intermediate fact. Simplify using `[wPs] at this`. Use linear arithmetic over natural numbers and integers. Choose the witnesses or unpack the hypotheses as in `⟨A, hA, hAm⟩ : ∃ A, F A B ∧ ∀ A', F A' B → A' ≤ A := by`. Use `Int.exists_greatest_of_bdd ?_ ⟨A0, hA0⟩` and prove the remaining obligations.

Take `⟨w, hw, k, hk⟩` from `h2`. Establish `hr : w ∈ roots` using `(by decide : vV ⊆ roots) hw`. Use `⟨|B| + 2 * k, fun z hz => ?_⟩` and prove the remaining obligations. Use `hz w hr k hk` as an intermediate fact. Establish `b1` using `le_abs_self B`.

Establish `b2` using `neg_abs_le B`. Simplify using `only [vV, Finset.mem_insert, Finset.mem_singleton] at hw`. Apply the tactic sequence `rcases hw with rfl | rfl | rfl <;> simp [wBe, wAl, wTh] at this <;> omega`. Set `T : ℤ × ℤ → Prop` to `fun w => ∃ k, C w k ∧ w.1 * A + w.2 * B + 2 * k = 0`. Establish `mv : ∀ a b : ℤ, ¬ F (A + a) (B + b) → ∃ w ∈ roots, ∃ k, C w k ∧ 0 ≤ w.1 * A + w.2 * B + 2 * k ∧ w.1 * A + w.2 * B + 2 * k + (w.1 * a + w.2 * b) < 0`.

Introduce `a b h`. Simplify using `only [F, not_forall, not_le] at h`. Take `⟨w, hw, k, hk, h⟩` from `h`. Conclude with `⟨w, hw, k, hk, hA w hw k hk, by linarith⟩`. Establish `up : ∀ a : ℤ, ¬ F (A + a) (B + 1)` using `fun a h => by have := hB _ ⟨_, h⟩; omega`.

Establish `m1 : T (-1, 0) ∨ T (-1, 1) ∨ T (-1, -1)`. Take `⟨w, hw, k, hk, e1, e2⟩` from `mv 1 0 (fun h => by have := hAm _ (by simpa using h); omega)`. Apply the tactic sequence `rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;> first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)`. Establish `m2 : T (0, -1) ∨ T (1, -1) ∨ T (-1, -1)`. Take `⟨w, hw, k, hk, e1, e2⟩` from `mv 0 1 (up 0)`.

Apply the tactic sequence `rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;> first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)`. Establish `par : (A + B) % 2 = 0`. Apply the tactic sequence `rcases m1 with ⟨k, -, e⟩ | ⟨k, -, e⟩ | ⟨k, -, e⟩ <;> rcases m2 with ⟨j, -, e'⟩ | ⟨j, -, e'⟩ | ⟨j, -, e'⟩ <;> dsimp only at e e' <;> omega`. Establish `m3 : T (0, -1) ∨ T (1, 0) ∨ T (1, -1)`. Take `⟨w, hw, k, hk, e1, e2⟩` from `mv (-1) 1 (up _)`.

Apply the tactic sequence `rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;> first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)`. Establish `m4 : T (0, -1) ∨ T (-1, 0) ∨ T (-1, -1)`. Take `⟨w, hw, k, hk, e1, e2⟩` from `mv 1 1 (up _)`. Apply the tactic sequence `rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;> first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)`. Establish `sg : ∀ w, w ≠ -wPs → T w → w.1 * A + w.2 * B < 0`.

Introduce and unpack `w hw ⟨k, hk, e⟩`. Establish `: k ≠ 0` using `fun h => h0 w hw (h ▸ hk)`. Use linear arithmetic over natural numbers and integers. Conclude with `⟨A, B, {w | w ∈ roots ∧ T w}, hA, fun _ => Iff.rfl, finite_sign_pattern_cases A B T _ rfl sg (fun ⟨k, _, e⟩ => by dsimp only at e; omega) m1 m2 m3 m4⟩`.
-/
private theorem root_system_linear_program_cases (C : ℤ × ℤ → ℕ → Prop) (h0 : ∀ w, w ≠ -wPs → ¬ C w 0) (h1 : ∃ k, C (-wPs) k)
    (h2 : ∃ w ∈ vV, ∃ k, C w k) :
    ∃ (A B : ℤ) (Si : Set (ℤ × ℤ)), (∀ w ∈ roots, ∀ k, C w k → 0 ≤ w.1 * A + w.2 * B + 2 * k) ∧
      (∀ w, w ∈ Si ↔ w ∈ roots ∧ ∃ k, C w k ∧ w.1 * A + w.2 * B + 2 * k = 0) ∧
      ((wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP) ∨ (-wAl ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ qQ) ∨ (-wTh ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ {-wTh, -wPs}) ∨
          (-wAl ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ nM) ∨ (-wTh ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe}) ∨ (-wTh ∈ Si ∧ wAl ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe, wAl})) := by
  let F : ℤ → ℤ → Prop := fun A B => ∀ w ∈ roots, ∀ k, C w k → 0 ≤ w.1 * A + w.2 * B + 2 * k
  obtain ⟨B, ⟨A0, hA0⟩, hB⟩ : ∃ B, (∃ A, F A B) ∧ ∀ B', (∃ A, F A B') → B' ≤ B := by
    refine Int.exists_greatest_of_bdd ?_ ⟨0, 0, fun w _ k _ => by simp⟩
    obtain ⟨k, hk⟩ := h1
    refine ⟨2 * k, fun z ⟨A, hz⟩ => ?_⟩
    have := hz _ (by decide) k hk
    simp [wPs] at this
    omega
  obtain ⟨A, hA, hAm⟩ : ∃ A, F A B ∧ ∀ A', F A' B → A' ≤ A := by
    refine Int.exists_greatest_of_bdd ?_ ⟨A0, hA0⟩
    obtain ⟨w, hw, k, hk⟩ := h2
    have hr : w ∈ roots := (by decide : vV ⊆ roots) hw
    refine ⟨|B| + 2 * k, fun z hz => ?_⟩
    have := hz w hr k hk
    have b1 := le_abs_self B
    have b2 := neg_abs_le B
    simp only [vV, Finset.mem_insert, Finset.mem_singleton] at hw
    rcases hw with rfl | rfl | rfl <;> simp [wBe, wAl, wTh] at this <;> omega
  let T : ℤ × ℤ → Prop := fun w => ∃ k, C w k ∧ w.1 * A + w.2 * B + 2 * k = 0
  have mv : ∀ a b : ℤ, ¬ F (A + a) (B + b) → ∃ w ∈ roots, ∃ k, C w k ∧ 0 ≤ w.1 * A + w.2 * B + 2 * k ∧
      w.1 * A + w.2 * B + 2 * k + (w.1 * a + w.2 * b) < 0 := by
    intro a b h
    simp only [F, not_forall, not_le] at h
    obtain ⟨w, hw, k, hk, h⟩ := h
    exact ⟨w, hw, k, hk, hA w hw k hk, by linarith⟩
  have up : ∀ a : ℤ, ¬ F (A + a) (B + 1) := fun a h => by have := hB _ ⟨_, h⟩; omega
  have m1 : T (-1, 0) ∨ T (-1, 1) ∨ T (-1, -1) := by
    obtain ⟨w, hw, k, hk, e1, e2⟩ := mv 1 0 (fun h => by have := hAm _ (by simpa using h); omega)
    rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;>
      first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)
  have m2 : T (0, -1) ∨ T (1, -1) ∨ T (-1, -1) := by
    obtain ⟨w, hw, k, hk, e1, e2⟩ := mv 0 1 (up 0)
    rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;>
      first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)
  have par : (A + B) % 2 = 0 := by
    rcases m1 with ⟨k, -, e⟩ | ⟨k, -, e⟩ | ⟨k, -, e⟩ <;> rcases m2 with ⟨j, -, e'⟩ | ⟨j, -, e'⟩ | ⟨j, -, e'⟩ <;>
      dsimp only at e e' <;> omega
  have m3 : T (0, -1) ∨ T (1, 0) ∨ T (1, -1) := by
    obtain ⟨w, hw, k, hk, e1, e2⟩ := mv (-1) 1 (up _)
    rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;>
      first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)
  have m4 : T (0, -1) ∨ T (-1, 0) ∨ T (-1, -1) := by
    obtain ⟨w, hw, k, hk, e1, e2⟩ := mv 1 1 (up _)
    rcases (mem_rank_two_roots_iff w).1 hw with rfl | rfl | rfl | rfl | rfl | rfl | rfl | rfl <;> dsimp only at e1 e2 <;>
      first | omega | exact .inl ⟨k, hk, by dsimp only; omega⟩ | exact .inr (.inl ⟨k, hk, by dsimp only; omega⟩) | exact .inr (.inr ⟨k, hk, by dsimp only; omega⟩)
  have sg : ∀ w, w ≠ -wPs → T w → w.1 * A + w.2 * B < 0 := by
    rintro w hw ⟨k, hk, e⟩
    have : k ≠ 0 := fun h => h0 w hw (h ▸ hk)
    omega
  exact ⟨A, B, {w | w ∈ roots ∧ T w}, hA, fun _ => Iff.rfl,
    finite_sign_pattern_cases A B T _ rfl sg (fun ⟨k, _, e⟩ => by dsimp only at e; omega) m1 m2 m3 m4⟩

/- English proof (translation)
Introduce `K _ _ V A _ _ _ f hinj hloc E n hE hn _ hm hv`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible A`. Take `⟨p, hp⟩` from `IsAlgClosed.exists_pow_nat_eq ((f ϖ : V) : K) (n := 2) (by norm_num)`. Establish `hf0 : ((f ϖ : V) : K) ≠ 0`. Introduce `h`.

Conclude with `hϖ.ne_zero (hinj (by rw [map_zero]; exact Subtype.ext h))`. Establish `hp0 : p ≠ 0` using `fun h => hf0 (by rw [← hp, h]; simp)`. Establish `hlt : V.valuation ((f ϖ : V) : K) < 1`. Rewrite using `[← ValuationSubring.valuation_lt_one_iff]`. Conclude with `fun h => hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)`.

Use `set γ := V.valuation p with hγ`. Establish `hγ0 : 0 < γ` using `zero_lt_iff.2 (by simpa [hγ] using hp0)`. Establish `hγ1 : γ < 1`. Rewrite `hlt` using `[← hp, map_pow]`. Assume the negation of the conclusion as `h`.

Conclude with `absurd hlt (not_lt.2 (one_le_pow₀ (not_lt.1 h)))`. Set `D : A → ℕ → Prop` to `fun x k => ∃ u : Aˣ, x = u * ϖ ^ k`. Establish `hD : ∀ x : A, x ≠ 0 → ∃ k, D x k` using `fun x hx => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ`. Establish `hD0 : ∀ x ∈ maximalIdeal A, ¬ D x 0`. Introduce and unpack `x hx ⟨u, rfl⟩`.

Conclude with `hx (by simp)`. Set `C : ℤ × ℤ → ℕ → Prop` to `fun w k => (∃ x ∈ E w, D x k) ∨ (w ∈ nM ∧ D (n w) k)`. Take `⟨a, b, Si, hF, hS, hc⟩` from `root_system_linear_program_cases C (by`. Introduce and unpack `w hw (⟨x, hx, h⟩ | ⟨-, h⟩)`. Conclude with `hD0 _ (hE w x hx) h`.

Conclude with `hD0 _ (hn w hw) h)`. Use the proof step `(by`. Take `⟨x, hx, h⟩` from `hm`. Take `⟨k, hk⟩` from `hD x h`. Conclude with `⟨k, .inl ⟨x, hx, hk⟩⟩)`.

Use the proof step `(by`. Take `⟨w, hw, x, hx, h⟩` from `hv`. Take `⟨k, hk⟩` from `hD x h`. Conclude with `⟨w, hw, k, .inl ⟨x, hx, hk⟩⟩)`. Set `t : Kˣ × Kˣ` to `(Units.mk0 p hp0 ^ a, Units.mk0 p hp0 ^ b)`.

Establish `val : ∀ w x k, D x k → V.valuation ((wv t w : K) * (f x : K)) = γ ^ (w.1 * a + w.2 * b + 2 * k)`. Introduce and unpack `w x k ⟨u, rfl⟩`. Establish `hu : V.valuation ((f u : V) : K) = 1` using `(V.valuation_eq_one_iff _).1 (u.isUnit.map f)`. Establish `e : ((wv t w : Kˣ) : K) * ((f ϖ : V) : K) ^ k = p ^ (w.1 * a + w.2 * b + 2 * k)`. Rewrite using `[← hp, zpow_add₀ hp0, zpow_add₀ hp0, mul_comm w.1, mul_comm w.2, zpow_mul, zpow_mul, zpow_mul]`.

Simplify using `[wv, t]`. Rewrite using `[hγ, ← map_zpow₀, ← e]`. Simplify using `only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hu, one_mul]`. Establish `le : ∀ w ∈ roots, ∀ x, (∀ k, D x k → C w k) → V.valuation ((wv t w : K) * (f x : K)) ≤ 1`. Introduce `w hw x h`.

Distinguish the cases in `hx : x = 0`. Simplify using `[hx]`. Take `⟨k, hk⟩` from `hD x hx`. Rewrite using `[val w x k hk]`. Conclude with `zpow_le_one₀ hγ0 hγ1.le (hF w hw k (h k hk))`.

Establish `eq : ∀ w x, V.valuation ((wv t w : K) * (f x : K)) = 1 ↔ ∃ k, D x k ∧ w.1 * a + w.2 * b + 2 * k = 0`. Introduce `w x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hx : x ≠ 0` using `by rintro rfl; simp at h`.

Take `⟨k, hk⟩` from `hD x hx`. Rewrite `h` using `[val w x k hk]`. Conclude with `⟨k, hk, (zpow_eq_one_iff_right₀ hγ0.le hγ1.ne).1 h⟩`. Introduce and unpack `⟨k, hk, e⟩`. Rewrite using `[val w x k hk, e, zpow_zero]`.

Establish `hsub : nM ⊆ roots` using `by decide`. Use `⟨t, Si, fun w hw x hx => le w hw x fun k hk => .inl ⟨x, hx, hk⟩, fun w hw => le w (hsub hw) _ fun k hk => .inr ⟨hw, hk⟩, fun w => ?_, hc⟩` and prove the remaining obligations. Simplify using `only [hS, eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hw, k, ⟨x, hx, hk⟩ | ⟨h, hk⟩, e⟩`.

Conclude with `.inl ⟨hw, x, hx, k, hk, e⟩`. Conclude with `.inr ⟨h, k, hk, e⟩`. Introduce and unpack `(⟨hw, x, hx, k, hk, e⟩ | ⟨h, k, hk, e⟩)`. Conclude with `⟨hw, k, .inl ⟨x, hx, hk⟩, e⟩`. Conclude with `⟨hsub h, k, .inr ⟨h, hk⟩, e⟩`.
-/
theorem UpperTheory.V.Ws.h7 :
    ∀ (K : Type) [Field K] [IsAlgClosed K] (V : ValuationSubring K) (A : Type) [CommRing A] [IsDomain A] [IsDiscreteValuationRing A] (f : A →+* V),
      Function.Injective f → IsLocalHom f → ∀ (E : ℤ × ℤ → Set A) (n : ℤ × ℤ → A),
      (∀ w, ∀ x ∈ E w, x ∈ maximalIdeal A) → (∀ w, w ≠ -wPs → n w ∈ maximalIdeal A) →
      (∃ x ∈ E wPs, x ≠ 0) → (∃ x ∈ E (-wPs), x ≠ 0) → (∃ w ∈ vV, ∃ x ∈ E w, x ≠ 0) →
      ∃ (t : Kˣ × Kˣ) (Si : Set (ℤ × ℤ)),
        (∀ w ∈ roots, ∀ x ∈ E w, V.valuation ((wv t w : K) * (f x : K)) ≤ 1) ∧ (∀ w ∈ nM, V.valuation ((wv t w : K) * (f (n w) : K)) ≤ 1) ∧
        (∀ w, w ∈ Si ↔ (w ∈ roots ∧ ∃ x ∈ E w, V.valuation ((wv t w : K) * (f x : K)) = 1) ∨ (w ∈ nM ∧ V.valuation ((wv t w : K) * (f (n w) : K)) = 1)) ∧
        ((wBe ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ nP) ∨ (-wAl ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ qQ) ∨ (-wTh ∈ Si ∧ -wPs ∈ Si ∧ Si ⊆ {-wTh, -wPs}) ∨
          (-wAl ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ nM) ∨ (-wTh ∈ Si ∧ -wBe ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe}) ∨ (-wTh ∈ Si ∧ wAl ∈ Si ∧ Si ⊆ {-wTh, -wPs, -wBe, wAl})) := by
  intro K _ _ V A _ _ _ f hinj hloc E n hE hn _ hm hv
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible A
  obtain ⟨p, hp⟩ := IsAlgClosed.exists_pow_nat_eq ((f ϖ : V) : K) (n := 2) (by norm_num)
  have hf0 : ((f ϖ : V) : K) ≠ 0 := by
    intro h
    exact hϖ.ne_zero (hinj (by rw [map_zero]; exact Subtype.ext h))
  have hp0 : p ≠ 0 := fun h => hf0 (by rw [← hp, h]; simp)
  have hlt : V.valuation ((f ϖ : V) : K) < 1 := by
    rw [← ValuationSubring.valuation_lt_one_iff]
    exact fun h => hϖ.not_isUnit (IsLocalHom.map_nonunit _ h)
  set γ := V.valuation p with hγ
  have hγ0 : 0 < γ := zero_lt_iff.2 (by simpa [hγ] using hp0)
  have hγ1 : γ < 1 := by
    rw [← hp, map_pow] at hlt
    by_contra h
    exact absurd hlt (not_lt.2 (one_le_pow₀ (not_lt.1 h)))
  let D : A → ℕ → Prop := fun x k => ∃ u : Aˣ, x = u * ϖ ^ k
  have hD : ∀ x : A, x ≠ 0 → ∃ k, D x k := fun x hx => IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hx hϖ
  have hD0 : ∀ x ∈ maximalIdeal A, ¬ D x 0 := by
    rintro x hx ⟨u, rfl⟩
    exact hx (by simp)
  let C : ℤ × ℤ → ℕ → Prop := fun w k => (∃ x ∈ E w, D x k) ∨ (w ∈ nM ∧ D (n w) k)
  obtain ⟨a, b, Si, hF, hS, hc⟩ := root_system_linear_program_cases C
    (by
      rintro w hw (⟨x, hx, h⟩ | ⟨-, h⟩)
      · exact hD0 _ (hE w x hx) h
      · exact hD0 _ (hn w hw) h)
    (by
      obtain ⟨x, hx, h⟩ := hm
      obtain ⟨k, hk⟩ := hD x h
      exact ⟨k, .inl ⟨x, hx, hk⟩⟩)
    (by
      obtain ⟨w, hw, x, hx, h⟩ := hv
      obtain ⟨k, hk⟩ := hD x h
      exact ⟨w, hw, k, .inl ⟨x, hx, hk⟩⟩)
  let t : Kˣ × Kˣ := (Units.mk0 p hp0 ^ a, Units.mk0 p hp0 ^ b)
  have val : ∀ w x k, D x k → V.valuation ((wv t w : K) * (f x : K)) = γ ^ (w.1 * a + w.2 * b + 2 * k) := by
    rintro w x k ⟨u, rfl⟩
    have hu : V.valuation ((f u : V) : K) = 1 := (V.valuation_eq_one_iff _).1 (u.isUnit.map f)
    have e : ((wv t w : Kˣ) : K) * ((f ϖ : V) : K) ^ k = p ^ (w.1 * a + w.2 * b + 2 * k) := by
      rw [← hp, zpow_add₀ hp0, zpow_add₀ hp0, mul_comm w.1, mul_comm w.2, zpow_mul, zpow_mul, zpow_mul]
      simp [wv, t]
    rw [hγ, ← map_zpow₀, ← e]
    simp only [map_mul, map_pow, MulMemClass.coe_mul, SubmonoidClass.coe_pow, hu, one_mul]
  have le : ∀ w ∈ roots, ∀ x, (∀ k, D x k → C w k) → V.valuation ((wv t w : K) * (f x : K)) ≤ 1 := by
    intro w hw x h
    by_cases hx : x = 0
    · simp [hx]
    obtain ⟨k, hk⟩ := hD x hx
    rw [val w x k hk]
    exact zpow_le_one₀ hγ0 hγ1.le (hF w hw k (h k hk))
  have eq : ∀ w x, V.valuation ((wv t w : K) * (f x : K)) = 1 ↔ ∃ k, D x k ∧ w.1 * a + w.2 * b + 2 * k = 0 := by
    intro w x
    constructor
    · intro h
      have hx : x ≠ 0 := by rintro rfl; simp at h
      obtain ⟨k, hk⟩ := hD x hx
      rw [val w x k hk] at h
      exact ⟨k, hk, (zpow_eq_one_iff_right₀ hγ0.le hγ1.ne).1 h⟩
    · rintro ⟨k, hk, e⟩
      rw [val w x k hk, e, zpow_zero]
  have hsub : nM ⊆ roots := by decide
  refine ⟨t, Si, fun w hw x hx => le w hw x fun k hk => .inl ⟨x, hx, hk⟩,
    fun w hw => le w (hsub hw) _ fun k hk => .inr ⟨hw, hk⟩, fun w => ?_, hc⟩
  simp only [hS, eq]
  constructor
  · rintro ⟨hw, k, ⟨x, hx, hk⟩ | ⟨h, hk⟩, e⟩
    · exact .inl ⟨hw, x, hx, k, hk, e⟩
    · exact .inr ⟨h, k, hk, e⟩
  · rintro (⟨hw, x, hx, k, hk, e⟩ | ⟨h, k, hk, e⟩)
    · exact ⟨hw, k, .inl ⟨x, hx, hk⟩, e⟩
    · exact ⟨hsub h, k, .inr ⟨h, hk⟩, e⟩
