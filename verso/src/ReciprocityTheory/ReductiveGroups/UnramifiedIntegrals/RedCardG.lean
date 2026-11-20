import Mathlib
import ReciprocityTheory.ReductiveGroups.UnramifiedIntegrals.RedHalf
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.AnalyticIdentityTheorems.MulStableIntegral

noncomputable section
open scoped BigOperators Classical
open Formalism.L2.Th1.CM Formalism.L2.Th1.F

namespace ReciprocityTheory.ChartRestriction.L1

namespace CardG

/- English proof (translation)
Break down `h with h | h` into its components or cases. Establish `: Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0) = Finset.univ.image (fun t : F => (-(v * t) / u, t))`. Use extensionality with `⟨x, y⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion.

Introduce `e`. Use `⟨y, ?_, rfl⟩` and prove the remaining obligations. Clear the denominators using the available nonvanishing facts. Take the linear combination `-e`. Introduce and unpack `⟨t, e, rfl⟩`.

Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).2), Finset.card_univ]`. Establish `: Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0) = Finset.univ.image (fun t : F => (t, -(u * t) / v))`.

Use extensionality with `⟨x, y⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]`. Prove the components needed by the constructor for the conclusion. Introduce `e`. Use `⟨x, rfl, ?_⟩` and prove the remaining obligations.

Clear the denominators using the available nonvanishing facts. Take the linear combination `-e`. Introduce and unpack `⟨t, rfl, e⟩`. Rewrite using `[← e]`. Clear the denominators using the available nonvanishing facts.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).1), Finset.card_univ]`.
-/
theorem card_line {F : Type} [Field F] [Fintype F] (u v : F) (h : u ≠ 0 ∨ v ≠ 0) :
    (Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)).card = Fintype.card F := by
  rcases h with h | h
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (-(v * t) / u, t)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨y, ?_, rfl⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, e, rfl⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).2), Finset.card_univ]
  · have : Finset.univ.filter (fun w : F × F => u * w.1 + v * w.2 = 0)
        = Finset.univ.image (fun t : F => (t, -(u * t) / v)) := by
      ext ⟨x, y⟩
      simp only [Finset.mem_filter, Finset.mem_univ, true_and, Finset.mem_image, Prod.mk.injEq]
      constructor
      · intro e
        refine ⟨x, rfl, ?_⟩
        field_simp
        linear_combination -e
      · rintro ⟨t, rfl, e⟩
        rw [← e]; field_simp; ring
    rw [this, Finset.card_image_of_injective _ (fun s t e => (Prod.mk.inj e).1), Finset.card_univ]

/- English proof (translation)
Distinguish the cases in `hab : a ≠ 0 ∨ b ≠ 0`. Rewrite using `[← card_line a b hab]`. Use `congr 1`. Use extensionality with `⟨x, y⟩`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and]`.

Use `⟨fun e => e.1, fun e => ⟨e, ?_⟩⟩` and prove the remaining obligations. Break down `hab with h | h` into its components or cases. Apply `mul_left_cancel₀ h` to reduce the goal to its premises. Take the linear combination `c * e + y * hdet`. Apply `mul_left_cancel₀ h` to reduce the goal to its premises.

Take the linear combination `d * e - x * hdet`. Use `push Not at hab`. Take `⟨ha, hb⟩` from `hab`. Establish `hcd : c ≠ 0 ∨ d ≠ 0`. Assume the negation of the conclusion as `hcd`.

Use `push Not at hcd`. Conclude with `hne ⟨ha, hb, hcd.1, hcd.2⟩`. Rewrite using `[← card_line c d hcd]`. Use `congr 1`. Use extensionality with `⟨x, y⟩`.

Simplify using `[ha, hb]`.
-/
theorem card_ker {F : Type} [Field F] [Fintype F] (a b c d : F) (hdet : a * d - b * c = 0)
    (hne : ¬ (a = 0 ∧ b = 0 ∧ c = 0 ∧ d = 0)) :
    (Finset.univ.filter (fun w : F × F => a * w.1 + b * w.2 = 0 ∧ c * w.1 + d * w.2 = 0)).card
      = Fintype.card F := by
  by_cases hab : a ≠ 0 ∨ b ≠ 0
  · rw [← card_line a b hab]
    congr 1
    ext ⟨x, y⟩
    simp only [Finset.mem_filter, Finset.mem_univ, true_and]
    refine ⟨fun e => e.1, fun e => ⟨e, ?_⟩⟩
    rcases hab with h | h
    · apply mul_left_cancel₀ h
      linear_combination c * e + y * hdet
    · apply mul_left_cancel₀ h
      linear_combination d * e - x * hdet
  · push Not at hab
    obtain ⟨ha, hb⟩ := hab
    have hcd : c ≠ 0 ∨ d ≠ 0 := by
      by_contra hcd
      push Not at hcd
      exact hne ⟨ha, hb, hcd.1, hcd.2⟩
    rw [← card_line c d hcd]
    congr 1
    ext ⟨x, y⟩
    simp [ha, hb]

/- English proof (translation)
Establish `hi` using `LinearIndependent.pair_iff.mp L.indep ((m - m' : ℤ) : ℝ) ((n - n' : ℤ) : ℝ) (by`. Simplify using `only [Complex.real_smul]`. Use `push_cast`. Take the linear combination `h)`. Prove the components needed by the constructor for the conclusion.

Use `hi.1` as an intermediate fact. Establish `h2 : m - m' = 0` using `by exact_mod_cast this`. Use linear arithmetic over natural numbers and integers. Use `hi.2` as an intermediate fact. Establish `h2 : n - n' = 0` using `by exact_mod_cast this`.

Use linear arithmetic over natural numbers and integers.
-/
theorem coord_unique (L : PeriodPair) {m n m' n' : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = m' * L.ω₁ + n' * L.ω₂) : m = m' ∧ n = n' := by
  have hi := LinearIndependent.pair_iff.mp L.indep ((m - m' : ℤ) : ℝ) ((n - n' : ℤ) : ℝ) (by
    simp only [Complex.real_smul]; push_cast; linear_combination h)
  constructor
  · have := hi.1
    have h2 : m - m' = 0 := by exact_mod_cast this
    omega
  · have := hi.2
    have h2 : n - n' = 0 := by exact_mod_cast this
    omega

/- English proof (translation)
Establish `hpc : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hp`. Rewrite using `[ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]`. Prove the components needed by the constructor for the conclusion. Introduce `hz`. Take `⟨m', n', e⟩` from `PeriodPair.mem_lattice.mp hz`.

Use `coord_unique L (m := m) (n := n) (m' := p * m') (n' := p * n') (by` as an intermediate fact. Rewrite using `[h, ← e]`. Use `push_cast`. Use the proof step `ring)`. Conclude with `⟨⟨m', this.1⟩, ⟨n', this.2⟩⟩`.

Introduce and unpack `⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩`. Use `PeriodPair.mem_lattice.mpr ⟨m', n', ?_⟩` and prove the remaining obligations. Apply `mul_left_cancel₀ hpc` to reduce the goal to its premises. Rewrite using `[← h]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem mem_iff (L : PeriodPair) (p : ℕ) (hp : p ≠ 0) {z : ℂ} {m n : ℤ}
    (h : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z) :
    z ∈ L.lattice ↔ (m : ZMod p) = 0 ∧ (n : ZMod p) = 0 := by
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp
  rw [ZMod.intCast_zmod_eq_zero_iff_dvd, ZMod.intCast_zmod_eq_zero_iff_dvd]
  constructor
  · intro hz
    obtain ⟨m', n', e⟩ := PeriodPair.mem_lattice.mp hz
    have := coord_unique L (m := m) (n := n) (m' := p * m') (n' := p * n') (by
      rw [h, ← e]; push_cast; ring)
    exact ⟨⟨m', this.1⟩, ⟨n', this.2⟩⟩
  · rintro ⟨⟨m', rfl⟩, ⟨n', rfl⟩⟩
    refine PeriodPair.mem_lattice.mpr ⟨m', n', ?_⟩
    apply mul_left_cancel₀ hpc
    rw [← h]; push_cast; ring

def co (L : PeriodPair) (z : ℂ) : ℤ × ℤ :=
  if h : z ∈ L.lattice then
    ((PeriodPair.mem_lattice.mp h).choose, (PeriodPair.mem_lattice.mp h).choose_spec.choose)
  else 0

/- English proof (translation)
Rewrite using `[co, dif_pos h]`. Conclude with `(PeriodPair.mem_lattice.mp h).choose_spec.choose_spec`.
-/
theorem co_spec (L : PeriodPair) {z : ℂ} (h : z ∈ L.lattice) :
    ((co L z).1 : ℂ) * L.ω₁ + ((co L z).2 : ℂ) * L.ω₂ = z := by
  rw [co, dif_pos h]
  exact (PeriodPair.mem_lattice.mp h).choose_spec.choose_spec

end CardG

open CardG

/- English proof (translation)
Establish `: Fact p.Prime` using `⟨hp⟩`. Take `⟨⟨hS1, hS2, hS3⟩, hdisj⟩` from `hT.kerReps`. Take `⟨a, b, c, d, h1, h2, -, hn⟩` from `Ker.matrix_data L β hβ`. Establish `hpc : (p : ℂ) ≠ 0` using `Nat.cast_ne_zero.mpr hp.ne_zero`. Establish `hdetZ : a * d - b * c = (p : ℤ) * M`.

Establish `: ((a * d - b * c : ℤ) : ℝ) = (((p : ℤ) * M : ℤ) : ℝ)`. Rewrite using `[← hn, hN]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Conclude with `this` after adjusting the coercions.

Establish `hdet : (a : ZMod p) * d - b * c = 0`. Use `congrArg (fun k : ℤ => (k : ZMod p)) hdetZ` as an intermediate fact. Simplify using `using this`. Establish `hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0)`. Simplify using `only [ZMod.intCast_zmod_eq_zero_iff_dvd]`.

Introduce and unpack `⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩`. Apply `hM` to reduce the goal to its premises. Establish `hp0 : (p : ℤ) ≠ 0` using `by exact_mod_cast hp.ne_zero`. Establish `: (M : ℤ) = p * (a' * d' - b' * c')`. Apply `mul_left_cancel₀ hp0` to reduce the goal to its premises.

Rewrite using `[← hdetZ]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `Int.natCast_dvd_natCast.mp ⟨_, this⟩`. Establish `hmul : ∀ {z : ℂ} {m n : ℤ}, (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z → (β * z ∈ L.lattice ↔ (a : ZMod p) * m + b * n = 0 ∧ (c : ZMod p) * m + d * n = 0)`. Introduce `z m n e`.

Use `mem_iff L p hp.ne_zero (z := β * z) (m := a * m + b * n) (n := c * m + d * n) (by` as an intermediate fact. Use `push_cast`. Take the linear combination `β * e - (m : ℂ) * h1 - (n : ℂ) * h2)`. Rewrite using `[this]`. Use `push_cast`.

Both sides reduce to the same expression. Use `set S := T ∪ T.image (fun P => -P) with hSdef`. Use `set K := Finset.univ.filter (fun w : ZMod p × ZMod p => (a : ZMod p) * w.1 + b * w.2 = 0 ∧ (c : ZMod p) * w.1 + d * w.2 = 0) with hK`. Establish `hKcard : K.card = p`. Use `card_ker (a : ZMod p) b c d hdet hne` as an intermediate fact.

Rewrite `this` using `[ZMod.card]`. Rewrite using `[hK]`. Use `this` and compare the differences between its conclusion and the goal. Establish `h0K : (0 : ZMod p × ZMod p) ∈ K` using `by simp [hK]`. Establish `hcardS : (S.filter (fun P => β * P ∈ L.lattice)).card = 2 * (T.filter (fun P => β * P ∈ L.lattice)).card`.

Establish `himg : (T.image (fun P => -P)).filter (fun P => β * P ∈ L.lattice) = (T.filter (fun P => β * P ∈ L.lattice)).image (fun P => -P)`. Use extensionality with `Q`. Simplify using `only [Finset.mem_filter, Finset.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨P, hP, rfl⟩, hQ⟩`.

Use `⟨P, ⟨hP, ?_⟩, rfl⟩` and prove the remaining obligations. Use `neg_mem hQ` as an intermediate fact. Simplify using `using this`. Introduce and unpack `⟨P, ⟨hP, hQ⟩, rfl⟩`. Use `⟨⟨P, hP, rfl⟩, ?_⟩` and prove the remaining obligations.

Use `neg_mem hQ` as an intermediate fact. Simplify using `using this`. Rewrite using `[hSdef, Finset.filter_union, Finset.card_union_of_disjoint (Finset.disjoint_filter_filter hdisj), himg, Finset.card_image_of_injective _ neg_injective]`. Expand and normalize the polynomial expressions, which then agree. Establish `hbij : (S.filter (fun P => β * P ∈ L.lattice)).card = (K.erase 0).card`.

Apply `Finset.card_nbij (fun z => (((co L (p * z)).1 : ZMod p), ((co L (p * z)).2 : ZMod p)))` to reduce the goal to its premises. Introduce `P hP`. Take `⟨hPS, hPβ⟩` from `Finset.mem_filter.mp hP`. Establish `e` using `co_spec L (hS1 P hPS).1`. Rewrite using `[Finset.mem_coe, Finset.mem_erase]`.

Prove the components needed by the constructor for the conclusion. Introduce `h0`. Apply `(hS1 P hPS).2` to reduce the goal to its premises. Rewrite using `[mem_iff L p hp.ne_zero e]`. Conclude with `Prod.mk.inj h0`.

Rewrite using `[hK, Finset.mem_filter]`. Conclude with `⟨Finset.mem_univ _, (hmul e).mp hPβ⟩`. Introduce `P hP Q hQ hPQ`. Establish `hPS` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hP)).1`. Establish `hQS` using `(Finset.mem_filter.mp (Finset.mem_coe.mp hQ)).1`.

Establish `eP` using `co_spec L (hS1 P hPS).1`. Establish `eQ` using `co_spec L (hS1 Q hQS).1`. Apply `hS2 P hPS Q hQS` to reduce the goal to its premises. Rewrite using `[mem_iff L p hp.ne_zero (m := (co L (p * P)).1 - (co L (p * Q)).1) (n := (co L (p * P)).2 - (co L (p * Q)).2) (by push_cast; linear_combination eP - eQ)]`. Take `⟨e1, e2⟩` from `Prod.mk.inj hPQ`.

Use `push_cast`. Conclude with `⟨sub_eq_zero.mpr e1, sub_eq_zero.mpr e2⟩`. Introduce and unpack `⟨x, y⟩ hxy`. Take `⟨hxy0, hxyK⟩` from `Finset.mem_erase.mp (Finset.mem_coe.mp hxy)`. Take `⟨m, rfl⟩` from `ZMod.intCast_surjective x`.

Take `⟨n, rfl⟩` from `ZMod.intCast_surjective y`. Use `set z : ℂ := ((m : ℂ) * L.ω₁ + n * L.ω₂) / p with hz`. Establish `ez : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z` using `by rw [hz]; field_simp`. Establish `hzp : (p : ℂ) * z ∈ L.lattice` using `PeriodPair.mem_lattice.mpr ⟨m, n, ez⟩`. Establish `hzL : z ∉ L.lattice`.

Rewrite using `[mem_iff L p hp.ne_zero ez]`. Introduce and unpack `⟨e1, e2⟩`. Conclude with `hxy0 (by rw [e1, e2]; rfl)`. Establish `hzβ : β * z ∈ L.lattice` using `(hmul ez).mpr (Finset.mem_filter.mp hxyK).2`. Take `⟨P, hPS, hzP⟩` from `hS3 z hzp hzL`.

Establish `eP` using `co_spec L (hS1 P hPS).1`. Use `⟨P, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hPS, ?_⟩), ?_⟩` and prove the remaining obligations. Establish `: β * P = β * z - β * (z - P)` using `by ring`. Rewrite using `[this]`. Conclude with `sub_mem hzβ (hβ _ hzP)`.

Use `(mem_iff L p hp.ne_zero (m := m - (co L (p * P)).1) (n := n - (co L (p * P)).2) (by push_cast; linear_combination ez - eP)).mp hzP` as an intermediate fact. Move the coercions through the operations in `at this`. Conclude with `Prod.ext (sub_eq_zero.mp this.1).symm (sub_eq_zero.mp this.2).symm`. Rewrite using `[← hcardS, hbij, Finset.card_erase_of_mem h0K, hKcard]`. Use `hp.pos` as an intermediate fact.

Use linear arithmetic over natural numbers and integers.
-/
theorem card_G (L : PeriodPair) (β : ℂ) (hβ : MulStable L β) (p M : ℕ) (hp : p.Prime) (hp2 : p ≠ 2)
    (hN : Complex.normSq β = ((p * M : ℕ) : ℝ)) (hM : ¬ p ∣ M) (T : Finset ℂ)
    (hT : IsHalfReps L (p : ℂ) T) :
    2 * (T.filter (fun P => β * P ∈ L.lattice)).card + 1 = p := by
  have : Fact p.Prime := ⟨hp⟩
  obtain ⟨⟨hS1, hS2, hS3⟩, hdisj⟩ := hT.kerReps
  obtain ⟨a, b, c, d, h1, h2, -, hn⟩ := Ker.matrix_data L β hβ
  have hpc : (p : ℂ) ≠ 0 := Nat.cast_ne_zero.mpr hp.ne_zero
  have hdetZ : a * d - b * c = (p : ℤ) * M := by
    have : ((a * d - b * c : ℤ) : ℝ) = (((p : ℤ) * M : ℤ) : ℝ) := by
      rw [← hn, hN]; push_cast; ring
    exact_mod_cast this
  have hdet : (a : ZMod p) * d - b * c = 0 := by
    have := congrArg (fun k : ℤ => (k : ZMod p)) hdetZ
    simpa using this
  have hne : ¬ ((a : ZMod p) = 0 ∧ (b : ZMod p) = 0 ∧ (c : ZMod p) = 0 ∧ (d : ZMod p) = 0) := by
    simp only [ZMod.intCast_zmod_eq_zero_iff_dvd]
    rintro ⟨⟨a', rfl⟩, ⟨b', rfl⟩, ⟨c', rfl⟩, ⟨d', rfl⟩⟩
    apply hM
    have hp0 : (p : ℤ) ≠ 0 := by exact_mod_cast hp.ne_zero
    have : (M : ℤ) = p * (a' * d' - b' * c') := by
      apply mul_left_cancel₀ hp0
      rw [← hdetZ]; ring
    exact Int.natCast_dvd_natCast.mp ⟨_, this⟩

  have hmul : ∀ {z : ℂ} {m n : ℤ}, (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z →
      (β * z ∈ L.lattice ↔ (a : ZMod p) * m + b * n = 0 ∧ (c : ZMod p) * m + d * n = 0) := by
    intro z m n e
    have := mem_iff L p hp.ne_zero (z := β * z) (m := a * m + b * n) (n := c * m + d * n) (by
      push_cast
      linear_combination β * e - (m : ℂ) * h1 - (n : ℂ) * h2)
    rw [this]; push_cast; rfl
  set S := T ∪ T.image (fun P => -P) with hSdef
  set K := Finset.univ.filter (fun w : ZMod p × ZMod p =>
    (a : ZMod p) * w.1 + b * w.2 = 0 ∧ (c : ZMod p) * w.1 + d * w.2 = 0) with hK
  have hKcard : K.card = p := by
    have := card_ker (a : ZMod p) b c d hdet hne
    rw [ZMod.card] at this
    rw [hK]
    convert this
  have h0K : (0 : ZMod p × ZMod p) ∈ K := by simp [hK]
  have hcardS : (S.filter (fun P => β * P ∈ L.lattice)).card
      = 2 * (T.filter (fun P => β * P ∈ L.lattice)).card := by
    have himg : (T.image (fun P => -P)).filter (fun P => β * P ∈ L.lattice)
        = (T.filter (fun P => β * P ∈ L.lattice)).image (fun P => -P) := by
      ext Q
      simp only [Finset.mem_filter, Finset.mem_image]
      constructor
      · rintro ⟨⟨P, hP, rfl⟩, hQ⟩
        refine ⟨P, ⟨hP, ?_⟩, rfl⟩
        have := neg_mem hQ
        simpa using this
      · rintro ⟨P, ⟨hP, hQ⟩, rfl⟩
        refine ⟨⟨P, hP, rfl⟩, ?_⟩
        have := neg_mem hQ
        simpa using this
    rw [hSdef, Finset.filter_union, Finset.card_union_of_disjoint
      (Finset.disjoint_filter_filter hdisj), himg,
      Finset.card_image_of_injective _ neg_injective]
    ring
  have hbij : (S.filter (fun P => β * P ∈ L.lattice)).card = (K.erase 0).card := by
    apply Finset.card_nbij
      (fun z => (((co L (p * z)).1 : ZMod p), ((co L (p * z)).2 : ZMod p)))
    · intro P hP
      obtain ⟨hPS, hPβ⟩ := Finset.mem_filter.mp hP
      have e := co_spec L (hS1 P hPS).1
      rw [Finset.mem_coe, Finset.mem_erase]
      constructor
      · intro h0
        apply (hS1 P hPS).2
        rw [mem_iff L p hp.ne_zero e]
        exact Prod.mk.inj h0
      · rw [hK, Finset.mem_filter]
        exact ⟨Finset.mem_univ _, (hmul e).mp hPβ⟩
    · intro P hP Q hQ hPQ
      have hPS := (Finset.mem_filter.mp (Finset.mem_coe.mp hP)).1
      have hQS := (Finset.mem_filter.mp (Finset.mem_coe.mp hQ)).1
      have eP := co_spec L (hS1 P hPS).1
      have eQ := co_spec L (hS1 Q hQS).1
      apply hS2 P hPS Q hQS
      rw [mem_iff L p hp.ne_zero (m := (co L (p * P)).1 - (co L (p * Q)).1)
        (n := (co L (p * P)).2 - (co L (p * Q)).2) (by push_cast; linear_combination eP - eQ)]
      obtain ⟨e1, e2⟩ := Prod.mk.inj hPQ
      push_cast
      exact ⟨sub_eq_zero.mpr e1, sub_eq_zero.mpr e2⟩
    · rintro ⟨x, y⟩ hxy
      obtain ⟨hxy0, hxyK⟩ := Finset.mem_erase.mp (Finset.mem_coe.mp hxy)
      obtain ⟨m, rfl⟩ := ZMod.intCast_surjective x
      obtain ⟨n, rfl⟩ := ZMod.intCast_surjective y
      set z : ℂ := ((m : ℂ) * L.ω₁ + n * L.ω₂) / p with hz
      have ez : (m : ℂ) * L.ω₁ + n * L.ω₂ = p * z := by rw [hz]; field_simp
      have hzp : (p : ℂ) * z ∈ L.lattice := PeriodPair.mem_lattice.mpr ⟨m, n, ez⟩
      have hzL : z ∉ L.lattice := by
        rw [mem_iff L p hp.ne_zero ez]
        rintro ⟨e1, e2⟩
        exact hxy0 (by rw [e1, e2]; rfl)
      have hzβ : β * z ∈ L.lattice := (hmul ez).mpr (Finset.mem_filter.mp hxyK).2
      obtain ⟨P, hPS, hzP⟩ := hS3 z hzp hzL
      have eP := co_spec L (hS1 P hPS).1
      refine ⟨P, Finset.mem_coe.mpr (Finset.mem_filter.mpr ⟨hPS, ?_⟩), ?_⟩
      · have : β * P = β * z - β * (z - P) := by ring
        rw [this]
        exact sub_mem hzβ (hβ _ hzP)
      · have := (mem_iff L p hp.ne_zero (m := m - (co L (p * P)).1)
          (n := n - (co L (p * P)).2) (by push_cast; linear_combination ez - eP)).mp hzP
        push_cast at this
        exact Prod.ext (sub_eq_zero.mp this.1).symm (sub_eq_zero.mp this.2).symm
  rw [← hcardS, hbij, Finset.card_erase_of_mem h0K, hKcard]
  have := hp.pos
  omega

end ReciprocityTheory.ChartRestriction.L1
