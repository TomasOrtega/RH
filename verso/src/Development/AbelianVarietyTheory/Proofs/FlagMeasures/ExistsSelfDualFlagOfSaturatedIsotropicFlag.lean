import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.OrthogonalCanonicalFiltrationStepsAutPoint

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadCov.FullFlag

/- English proof (translation)
The claim follows from `Submodule.finrank_mono (Submodule.span_mono h)`.
-/
theorem rkK_mono {K V : Type} [Field K] [NumberField K] [AddCommGroup V] [Module K V] [Module (𝓞 K) V]
    [FiniteDimensional K V] {M N : Submodule (𝓞 K) V} (h : M ≤ N) : Formalism.HN.rkK M ≤ Formalism.HN.rkK N :=
  Submodule.finrank_mono (Submodule.span_mono h)

/- English proof (translation)
Introduce `I xf a j S hS`. Take `⟨h0, hmono, hrk, hsat, hiso⟩` from `hS`. Use `set x : I.GA := (1, xf) with hx`. Take `⟨-, hA, -, -, -⟩` from `GlobalTheory.PointLattice.lamX_selfDual I x`. Take `⟨-, -, -, -, hw⟩` from `GlobalTheory.Count.FrameMajorant.frames_give_majorants I x`.

Establish `hX : ∀ v, IsUnit (frm I x v).det` using `fun v => (hw v).1`. Take `⟨-, -, -, hmain⟩` from `PerpStep.main I x`. Establish `hform : ∀ s y : Fin I.n → I.E, star s ⬝ᵥ (I.J *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J s y`. Introduce `s y`. Simplify using `[Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply, -star_trivial]`.

Establish `hmem : ∀ N y, y ∈ perpIn I x N ↔ y ∈ lamX I x ∧ ∀ s ∈ N, star s ⬝ᵥ (I.J *ᵥ y) = 0`. Introduce `N y`. Rewrite using `[PerpStep.perpIn_eq, PerpStep.mem_perp]`. Simplify using `only [hform]`. Establish `hsatS : ∀ i, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i)`.

Introduce `i`. Establish `e : S i = lamX I x ⊓ (Submodule.span I.E (S i : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E)`. Use extensionality with `y`. Conclude with `hsat i y`. Rewrite using `[e]`.

Conclude with `PerpStep.sat_inf (bas I) (frm I x) hX _ hA _`. Take `⟨G, hG⟩ : ∃ G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), ∀ b, G b = S ⟨min b a, Nat.lt_succ_of_le (min_le_right _ _)⟩` from `⟨_, fun _ => rfl⟩`. Establish `hGS : ∀ i : Fin (a + 1), G i = S i`. Introduce `i`. Rewrite using `[hG]`.

Use `congr 1`. Use `ext`. Use `i.2` as an intermediate fact. Simplify using `only`. Use linear arithmetic over natural numbers and integers.

Establish `hG0 : G 0 = ⊥` using `(hGS 0).trans h0`. Establish `hGm : Monotone G`. Introduce `b c h`. Rewrite using `[hG, hG]`. Conclude with `hmono (Fin.mk_le_mk.2 (min_le_min_right _ h))`.

Establish `hGsat : ∀ b, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G b)`. Introduce `b`. Rewrite using `[hG]`. Conclude with `hsatS _`. Establish `hGr : ∀ i : Fin a, Formalism.HN.rkK (G (i + 1)) = Formalism.HN.rkK (G i) + j i`.

Introduce `i`. Establish `h1` using `hGS i.succ`. Establish `h2` using `hGS i.castSucc`. Rewrite `h1` using `[Fin.val_succ]`. Rewrite `h2` using `[Fin.val_castSucc]`.

Rewrite using `[h1, h2, hrk]`. Establish `hGsum : ∀ b (hb : b ≤ a), Formalism.HN.rkK (G b) = ∑ i : Fin b, j (Fin.castLE hb i)`. Introduce `b`. Proceed by induction on `b with`. Consider the case `zero => intro _`.

Simplify using `[hG0, Formalism.HN.rkK]`. Consider the case `succ b ih`. Introduce `hb`. Rewrite using `[Fin.sum_univ_castSucc]`. Use `hGr ⟨b, hb⟩` as an intermediate fact.

Simplify using `only at this`. Rewrite using `[this, ih (by omega)]`. Both sides reduce to the same expression. Establish `hGa : Formalism.HN.rkK (G a) = ∑ i, j i`. Rewrite using `[hGsum a le_rfl]`.

Both sides reduce to the same expression. Establish `hPr : ∀ b, Formalism.HN.rkK (perpIn I x (G b)) + Formalism.HN.rkK (G b) = I.n` using `fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.1`. Establish `hPP : ∀ b, perpIn I x (perpIn I x (G b)) = G b` using `fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.2.1`. Establish `hPa : ∀ b c, b ≤ c → perpIn I x (G c) ≤ perpIn I x (G b)` using `fun b c h => (hmain _ _ (hGsat b) (hGsat c) (hGm h)).2.2.2.1`. Establish `hP0 : perpIn I x (G 0) = lamX I x`.

Use extensionality with `y`. Rewrite using `[hmem, hG0]`. Use `⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩` and prove the remaining obligations. Rewrite using `[(Submodule.mem_bot _).1 hs]`. Simplify using the standard rewrite rules.

Establish `hmid : G a ≤ perpIn I x (G a)`. Introduce `y hy`. Establish `e : G a = S (Fin.last a)` using `hGS (Fin.last a)`. Rewrite using `[hmem]`. Use `⟨(hGsat a).1 hy, fun s hs => ?_⟩` and prove the remaining obligations.

Rewrite using `[hform]`. Rewrite `hs`, `hy` using `[e]`. Conclude with `hiso s hs y hy`. Take `⟨F, hF1, hF2⟩ : ∃ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E), (∀ b, b ≤ a → F b = G b) ∧ ∀ b c, a < b → c = 2 * a + 1 - b → F b = perpIn I x (G c)` from `⟨fun b => if b ≤ a then G b else perpIn I x (G (2 * a + 1 - b)), fun b hb => if_pos hb, fun b c hb hc => hc ▸ if_neg (by omega)⟩`. Establish `hFm : Monotone F`.

Use `monotone_nat_of_le_succ fun b => ?_` and prove the remaining obligations. Break down `lt_trichotomy b a with h | rfl | h` into its components or cases. Rewrite using `[hF1 b h.le, hF1 (b + 1) h]`. Conclude with `hGm (by omega)`. Rewrite using `[hF1 b le_rfl, hF2 (b + 1) b (by omega) (by omega)]`.

Conclude with `hmid`. Rewrite using `[hF2 b _ h rfl, hF2 (b + 1) _ (by omega) rfl]`. Conclude with `hPa _ _ (by omega)`. Establish `hFtop : ∀ b, 2 * a + 1 ≤ b → F b = lamX I x` using `fun b hb => by`. Rewrite using `[hF2 b 0 (by omega) (by omega), hP0]`.

Use `⟨F, fun b => Formalism.HN.rkK (F (b + 1)) - Formalism.HN.rkK (F b), ⟨hFm, ?_, ?_, ?_⟩, hFtop _ le_rfl, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hF1 0 (by omega), hG0]`. Introduce `b hb`. Rewrite using `[hFtop b hb, hFtop _ le_rfl]`. Introduce `b hb y`.

Rewrite using `[hFtop _ le_rfl, ← hmem]`. Distinguish the cases in `h : b ≤ a`. Rewrite using `[hF1 b h, hF2 _ b (by omega) (by omega)]`. Rewrite using `[hF2 b _ (by omega) rfl, hPP, hF1 _ (by omega)]`. Introduce `i`.

Rewrite using `[hF1 i (by have := i.2; omega), hGS]`. Introduce `b`. Use `rkK_mono (hFm (Nat.le_succ b))` as an intermediate fact. Simplify using `only [Nat.succ_eq_add_one] at this ⊢`. Use linear arithmetic over natural numbers and integers.

Introduce `i`. Establish `hi` using `i.2`. Establish `h1` using `hGr i`. Establish `h2` using `hPr i`. Establish `h3` using `hPr (i + 1)`.

Simplify using `only`. Rewrite using `[hF1 i (by omega), hF1 (i + 1) (by omega), hF2 (2 * a - i + 1) i (by omega) (by omega), hF2 (2 * a - i) (i + 1) (by omega) (by omega)]`. Use linear arithmetic over natural numbers and integers. Establish `h2` using `hPr a`. Simplify using `only`.

Rewrite using `[hF1 a le_rfl, hF2 (a + 1) a (by omega) (by omega)]`. Use linear arithmetic over natural numbers and integers. Introduce `b hb`. Simplify using `only`. Rewrite using `[hFtop b hb, hFtop _ (by omega), Nat.sub_self]`.
-/
theorem main : ∀ (I : AutInst) (xf : I.Gf) (a : ℕ) (j : Fin a → ℕ) (S : Fin (a + 1) → Submodule (𝓞 I.E) (Fin I.n → I.E)), IsSatFlag I (lamX I (1, xf)) j S → ∃ (F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E)) (r : ℕ → ℕ), IsDualFlag I.J F (2 * a + 1) ∧ F (2 * a + 1) = lamX I (1, xf) ∧ (∀ i : Fin (a + 1), F i = S i) ∧ (∀ b, Formalism.HN.rkK (F (b + 1)) = Formalism.HN.rkK (F b) + r b) ∧ (∀ i : Fin a, r i = j i ∧ r (2 * a - i) = j i) ∧ r a = I.n - 2 * ∑ i, j i ∧ ∀ b, 2 * a + 1 ≤ b → r b = 0 := by
  intro I xf a j S hS
  obtain ⟨h0, hmono, hrk, hsat, hiso⟩ := hS
  set x : I.GA := (1, xf) with hx
  obtain ⟨-, hA, -, -, -⟩ := GlobalTheory.PointLattice.lamX_selfDual I x
  obtain ⟨-, -, -, -, hw⟩ := GlobalTheory.Count.FrameMajorant.frames_give_majorants I x
  have hX : ∀ v, IsUnit (frm I x v).det := fun v => (hw v).1
  obtain ⟨-, -, -, hmain⟩ := PerpStep.main I x
  have hform : ∀ s y : Fin I.n → I.E,
      star s ⬝ᵥ (I.J *ᵥ y) = Formalism.UG.hform (starRingEnd I.E) I.J s y := by
    intro s y
    simp [Formalism.UG.hform, dotProduct, Matrix.mulVec, Finset.mul_sum, mul_assoc, starRingEnd_apply,
      -star_trivial]
  have hmem : ∀ N y, y ∈ perpIn I x N ↔ y ∈ lamX I x ∧ ∀ s ∈ N, star s ⬝ᵥ (I.J *ᵥ y) = 0 := by
    intro N y
    rw [PerpStep.perpIn_eq, PerpStep.mem_perp]
    simp only [hform]
  have hsatS : ∀ i, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (S i) := by
    intro i
    have e : S i = lamX I x ⊓ (Submodule.span I.E (S i : Set (Fin I.n → I.E))).restrictScalars (𝓞 I.E) := by
      ext y
      exact hsat i y
    rw [e]
    exact PerpStep.sat_inf (bas I) (frm I x) hX _ hA _
  obtain ⟨G, hG⟩ : ∃ G : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      ∀ b, G b = S ⟨min b a, Nat.lt_succ_of_le (min_le_right _ _)⟩ := ⟨_, fun _ => rfl⟩
  have hGS : ∀ i : Fin (a + 1), G i = S i := by
    intro i
    rw [hG]
    congr 1
    ext
    have := i.2
    simp only
    omega
  have hG0 : G 0 = ⊥ := (hGS 0).trans h0
  have hGm : Monotone G := by
    intro b c h
    rw [hG, hG]
    exact hmono (Fin.mk_le_mk.2 (min_le_min_right _ h))
  have hGsat : ∀ b, Formalism.HN.IsSat (Formalism.HermitianLatticesTheory.realize (bas I) (frm I x)) (lamX I x) (G b) := by
    intro b
    rw [hG]
    exact hsatS _
  have hGr : ∀ i : Fin a, Formalism.HN.rkK (G (i + 1)) = Formalism.HN.rkK (G i) + j i := by
    intro i
    have h1 := hGS i.succ
    have h2 := hGS i.castSucc
    rw [Fin.val_succ] at h1
    rw [Fin.val_castSucc] at h2
    rw [h1, h2, hrk]
  have hGsum : ∀ b (hb : b ≤ a), Formalism.HN.rkK (G b) = ∑ i : Fin b, j (Fin.castLE hb i) := by
    intro b
    induction b with
    | zero => intro _; simp [hG0, Formalism.HN.rkK]
    | succ b ih =>
      intro hb
      rw [Fin.sum_univ_castSucc]
      have := hGr ⟨b, hb⟩
      simp only at this
      rw [this, ih (by omega)]
      rfl
  have hGa : Formalism.HN.rkK (G a) = ∑ i, j i := by
    rw [hGsum a le_rfl]; rfl
  have hPr : ∀ b, Formalism.HN.rkK (perpIn I x (G b)) + Formalism.HN.rkK (G b) = I.n :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.1
  have hPP : ∀ b, perpIn I x (perpIn I x (G b)) = G b :=
    fun b => (hmain _ _ (hGsat b) (hGsat b) le_rfl).2.2.1
  have hPa : ∀ b c, b ≤ c → perpIn I x (G c) ≤ perpIn I x (G b) :=
    fun b c h => (hmain _ _ (hGsat b) (hGsat c) (hGm h)).2.2.2.1
  have hP0 : perpIn I x (G 0) = lamX I x := by
    ext y
    rw [hmem, hG0]
    refine ⟨fun h => h.1, fun h => ⟨h, fun s hs => ?_⟩⟩
    rw [(Submodule.mem_bot _).1 hs]
    simp
  have hmid : G a ≤ perpIn I x (G a) := by
    intro y hy
    have e : G a = S (Fin.last a) := hGS (Fin.last a)
    rw [hmem]
    refine ⟨(hGsat a).1 hy, fun s hs => ?_⟩
    rw [hform]
    rw [e] at hs hy
    exact hiso s hs y hy
  obtain ⟨F, hF1, hF2⟩ : ∃ F : ℕ → Submodule (𝓞 I.E) (Fin I.n → I.E),
      (∀ b, b ≤ a → F b = G b) ∧ ∀ b c, a < b → c = 2 * a + 1 - b → F b = perpIn I x (G c) :=
    ⟨fun b => if b ≤ a then G b else perpIn I x (G (2 * a + 1 - b)), fun b hb => if_pos hb,
      fun b c hb hc => hc ▸ if_neg (by omega)⟩
  have hFm : Monotone F := by
    refine monotone_nat_of_le_succ fun b => ?_
    rcases lt_trichotomy b a with h | rfl | h
    · rw [hF1 b h.le, hF1 (b + 1) h]
      exact hGm (by omega)
    · rw [hF1 b le_rfl, hF2 (b + 1) b (by omega) (by omega)]
      exact hmid
    · rw [hF2 b _ h rfl, hF2 (b + 1) _ (by omega) rfl]
      exact hPa _ _ (by omega)
  have hFtop : ∀ b, 2 * a + 1 ≤ b → F b = lamX I x := fun b hb => by
    rw [hF2 b 0 (by omega) (by omega), hP0]
  refine ⟨F, fun b => Formalism.HN.rkK (F (b + 1)) - Formalism.HN.rkK (F b), ⟨hFm, ?_, ?_, ?_⟩, hFtop _ le_rfl,
    ?_, ?_, ?_, ?_, ?_⟩
  · rw [hF1 0 (by omega), hG0]
  · intro b hb
    rw [hFtop b hb, hFtop _ le_rfl]
  · intro b hb y
    rw [hFtop _ le_rfl, ← hmem]
    by_cases h : b ≤ a
    · rw [hF1 b h, hF2 _ b (by omega) (by omega)]
    · rw [hF2 b _ (by omega) rfl, hPP, hF1 _ (by omega)]
  · intro i
    rw [hF1 i (by have := i.2; omega), hGS]
  · intro b
    have := rkK_mono (hFm (Nat.le_succ b))
    simp only [Nat.succ_eq_add_one] at this ⊢
    omega
  · intro i
    have hi := i.2
    have h1 := hGr i
    have h2 := hPr i
    have h3 := hPr (i + 1)
    simp only
    rw [hF1 i (by omega), hF1 (i + 1) (by omega), hF2 (2 * a - i + 1) i (by omega) (by omega),
      hF2 (2 * a - i) (i + 1) (by omega) (by omega)]
    omega
  · have h2 := hPr a
    simp only
    rw [hF1 a le_rfl, hF2 (a + 1) a (by omega) (by omega)]
    omega
  · intro b hb
    simp only
    rw [hFtop b hb, hFtop _ (by omega), Nat.sub_self]

end GlobalTheory.RadCov.FullFlag
