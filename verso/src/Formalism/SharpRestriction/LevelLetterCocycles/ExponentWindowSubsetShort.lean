import Formalism.SharpRestriction.LevelLetterCocycles.WachCoordinates
import Formalism.DistinguishedUnitIdeals.FinalArcProps

noncomputable section

namespace Formalism.MainNotions.WachCoordinates

open Formalism.ExponentWindows (Kind)

def kdOf {n : ℕ} (ty : ZMod n → LT) (i : ZMod n) : Kind :=
  match ty i with
  | LT.thin => Kind.thin
  | LT.up _ => Kind.up
  | LT.down _ => Kind.down

def bbOf {n : ℕ} (ty : ZMod n → LT) (i : ZMod n) : ℕ := (ty i).size

/- English proof (translation)
Unfold `kdOf`. Apply the tactic sequence `cases h : ty i <;> simp`.
-/
theorem kdOf_thin {n : ℕ} {ty : ZMod n → LT} {i : ZMod n} : kdOf ty i = Kind.thin ↔ ty i = LT.thin := by
  unfold kdOf
  cases h : ty i <;> simp

/- English proof (translation)
Unfold `kdOf at h`. Unfold `bbOf`. Apply the tactic sequence `cases h' : ty i <;> simp [h', LT.size] at h ⊢`.
-/
theorem kdOf_up {n : ℕ} {ty : ZMod n → LT} {i : ZMod n} (h : kdOf ty i = Kind.up) :
    ty i = LT.up (bbOf ty i) := by
  unfold kdOf at h
  unfold bbOf
  cases h' : ty i <;> simp [h', LT.size] at h ⊢

/- English proof (translation)
Unfold `kdOf at h`. Unfold `bbOf`. Apply the tactic sequence `cases h' : ty i <;> simp [h', LT.size] at h ⊢`.
-/
theorem kdOf_down {n : ℕ} {ty : ZMod n → LT} {i : ZMod n} (h : kdOf ty i = Kind.down) :
    ty i = LT.down (bbOf ty i) := by
  unfold kdOf at h
  unfold bbOf
  cases h' : ty i <;> simp [h', LT.size] at h ⊢

/- English proof (translation)
Unfold `kdOf`. Apply the tactic sequence `cases h : ty i <;> simp [LT.thick]`.
-/
theorem kdOf_thick {n : ℕ} {ty : ZMod n → LT} {i : ZMod n} :
    (ty i).thick = true ↔ kdOf ty i ≠ Kind.thin := by
  unfold kdOf
  cases h : ty i <;> simp [LT.thick]

def cutsOf {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)} {arcLen : ZMod n → ℕ}
    (h : CutsOK n j ty cuts arcLen) : Formalism.ExponentWindows.E.Cuts n where
  cuts := cuts
  ell := arcLen
  nonempty := h.1
  ell_pos := fun c hc => (h.2.2.1 c hc).1
  ell_le := fun c hc => (h.2.2.1 c hc).2.1
  prev_mem := fun c hc => (h.2.2.1 c hc).2.2.1
  no_inner := fun c hc => (h.2.2.1 c hc).2.2.2

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cutsOf_cuts {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)}
    {arcLen : ZMod n → ℕ} (h : CutsOK n j ty cuts arcLen) : (cutsOf h).cuts = cuts := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem cutsOf_ell {n j : ℕ} {ty : ZMod n → LT} {cuts : Finset (ZMod n)}
    {arcLen : ZMod n → ℕ} (h : CutsOK n j ty cuts arcLen) : (cutsOf h).ell = arcLen := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem parM_eq_Mpar (l g h : ℕ) : Formalism.ExponentWindows.E.parM l h g = Mpar l g h := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem parA_eq_initialExponentBound (l n : ℕ) [NeZero n] (j g h : ℕ) (H₁ H₂ : ZMod n → ℕ)
    (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    Formalism.ExponentWindows.E.parA (sigPar l g h j) (rrPar l n H₁ H₂ cuts) g (ellMax cuts arcLen) =
      initialExponentBound l n j g h H₁ H₂ cuts arcLen := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem parE_eq_ePar (l n : ℕ) [NeZero n] (j g h : ℕ) (H₁ H₂ : ZMod n → ℕ)
    (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) :
    Formalism.ExponentWindows.E.parE (sigPar l g h j) (rrPar l n H₁ H₂ cuts) g (ellMax cuts arcLen)
              (kapPar l g h (ellMax cuts arcLen)) =
      ePar l n j g h H₁ H₂ cuts arcLen := rfl

/- English proof (translation)
Unfold `gPar`. Use linear arithmetic over natural numbers and integers.
-/
theorem G_le_gPar (G S η : ℕ) : G ≤ gPar G S η := by unfold gPar; omega
/- English proof (translation)
Unfold `gPar`. Use linear arithmetic over natural numbers and integers.
-/
theorem S_le_gPar (G S η : ℕ) : S ≤ gPar G S η := by unfold gPar; omega
/- English proof (translation)
Unfold `gPar`. Use linear arithmetic over natural numbers and integers.
-/
theorem η_le_gPar (G S η : ℕ) : η ≤ gPar G S η := by unfold gPar; omega

/- English proof (translation)
Rewrite using `[parM_eq_Mpar]`. Unfold `Formalism.ExponentWindows.E.SigOK`. Use `set M := Mpar l g h with hM`. Establish `hl1 : (0 : ℝ) < (l : ℝ) - 1`. Establish `: (3 : ℝ) ≤ l` using `by exact_mod_cast hl`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hlp : (0 : ℝ) < (l : ℝ) ^ (j - 1)`. Establish `: (0 : ℝ) < l` using `by linarith`. Check the signs of the components of the expression. Establish `hsig : (((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 + 1 ≤ (sigPar l g h j : ℝ)` using `Nat.le_ceil _`.

Establish `hcast : (((l - 1 : ℕ) : ℕ) : ℝ) = (l : ℝ) - 1`. Rewrite using `[Nat.cast_sub (by omega)]; simp`. Establish `key : (((3 * g * l ^ (j - 1) + M) * l : ℕ) : ℝ) ≤ ((sigPar l g h j * (l ^ (j - 1) * (l - 1) ^ 2) : ℕ) : ℝ)`. Use `push_cast`. Rewrite using `[hcast]`.

Establish `h2 : (0 : ℝ) < ((l : ℝ) - 1) ^ 2` using `by positivity`. Establish `h3 : (((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 ≤ (sigPar l g h j : ℝ)` using `by linarith`. Rewrite `h3` using `[div_le_iff₀ h2]`. Establish `h4 : (3 * (g : ℝ) * (l : ℝ) ^ (j - 1) + (M : ℝ)) * l = ((((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l) * (l : ℝ) ^ (j - 1)`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[h4]`. Combine the equalities or inequalities in the displayed calculation. Conclude with `key` after adjusting the coercions.
-/
theorem sigOK_of (l g h j : ℕ) (hl : 3 ≤ l) :
    Formalism.ExponentWindows.E.SigOK l j (Formalism.ExponentWindows.E.parM l h g) g (sigPar l g h j) := by
  rw [parM_eq_Mpar]
  unfold Formalism.ExponentWindows.E.SigOK
  set M := Mpar l g h with hM
  have hl1 : (0 : ℝ) < (l : ℝ) - 1 := by
    have : (3 : ℝ) ≤ l := by exact_mod_cast hl
    linarith
  have hlp : (0 : ℝ) < (l : ℝ) ^ (j - 1) := by
    have : (0 : ℝ) < l := by linarith
    positivity
  have hsig : (((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 + 1 ≤
      (sigPar l g h j : ℝ) := Nat.le_ceil _
  have hcast : (((l - 1 : ℕ) : ℕ) : ℝ) = (l : ℝ) - 1 := by
    rw [Nat.cast_sub (by omega)]; simp
  have key : (((3 * g * l ^ (j - 1) + M) * l : ℕ) : ℝ) ≤
      ((sigPar l g h j * (l ^ (j - 1) * (l - 1) ^ 2) : ℕ) : ℝ) := by
    push_cast
    rw [hcast]
    have h2 : (0 : ℝ) < ((l : ℝ) - 1) ^ 2 := by positivity
    have h3 : (((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l / ((l : ℝ) - 1) ^ 2 ≤
        (sigPar l g h j : ℝ) := by linarith
    rw [div_le_iff₀ h2] at h3
    have h4 : (3 * (g : ℝ) * (l : ℝ) ^ (j - 1) + (M : ℝ)) * l =
        ((((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l) * (l : ℝ) ^ (j - 1) := by
      push_cast
      field_simp
    rw [h4]
    calc ((((3 * g : ℕ) : ℝ) + (M : ℝ) / (l : ℝ) ^ (j - 1)) * l) * (l : ℝ) ^ (j - 1)
        ≤ ((sigPar l g h j : ℝ) * ((l : ℝ) - 1) ^ 2) * (l : ℝ) ^ (j - 1) :=
          mul_le_mul_of_nonneg_right h3 hlp.le
      _ = (sigPar l g h j : ℝ) * ((l : ℝ) ^ (j - 1) * ((l : ℝ) - 1) ^ 2) := by ring
  exact_mod_cast key

/- English proof (translation)
Unfold `wins`. Use `Finset.mem_image.2 ⟨(a, len), ?_, rfl⟩` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]`. Conclude with `⟨⟨⟨h1, h2⟩, by omega⟩, h4⟩`.
-/
theorem Ico_mem_windows {g h : ℕ} (a : ℤ) (len : ℕ) (h1 : -(2 * h : ℤ) ≤ a) (h2 : a ≤ 2 * h)
    (h3 : len ≤ 3 * g) (h4 : a + (len : ℤ) ≤ 2 * h + 1) : Finset.Ico a (a + (len : ℤ)) ∈ wins g h := by
  unfold wins
  refine Finset.mem_image.2 ⟨(a, len), ?_, rfl⟩
  simp only [Finset.mem_filter, Finset.mem_product, Finset.mem_Icc, Finset.mem_range]
  exact ⟨⟨⟨h1, h2⟩, by omega⟩, h4⟩

/- English proof (translation)
Unfold `Formalism.ExponentWindows.E.kapExp vPP1`. Establish `h1 : ∑ i ∈ JS.erase 0, (1 + E + padicValInt l i) ≤ ∑ i ∈ JS'.erase 0, (1 + E + padicValInt l i)` using `Finset.sum_le_sum_of_subset (Finset.erase_subset_erase 0 hsub)`. Establish `h2 : ∑ i ∈ JS'.erase 0, (1 + E + padicValInt l i) ≤ ∑ i ∈ JS'.erase 0, (L + 1 + padicValInt l i)` using `Finset.sum_le_sum fun i _ => by omega`. Use linear arithmetic over natural numbers and integers.
-/
theorem kappa_exponent_le_valuation (l E L : ℕ) {JS JS' : Finset ℤ} (hsub : JS ⊆ JS') (hE : E ≤ L) :
    Formalism.ExponentWindows.E.kapExp l E JS ≤ vPP1 l L JS' := by
  unfold Formalism.ExponentWindows.E.kapExp vPP1
  have h1 : ∑ i ∈ JS.erase 0, (1 + E + padicValInt l i) ≤
      ∑ i ∈ JS'.erase 0, (1 + E + padicValInt l i) :=
    Finset.sum_le_sum_of_subset (Finset.erase_subset_erase 0 hsub)
  have h2 : ∑ i ∈ JS'.erase 0, (1 + E + padicValInt l i) ≤
      ∑ i ∈ JS'.erase 0, (L + 1 + padicValInt l i) :=
    Finset.sum_le_sum fun i _ => by omega
  omega

/- English proof (translation)
Unfold `kapPar`. Conclude with `Finset.le_sup (f := fun w : Finset ℤ × Finset ℤ × Finset ℤ => vPP1 l ell (w.1 ∪ w.2.1 ∪ w.2.2)) (b := (w₁, w₂, w₃)) (Finset.mem_product.2 ⟨h₁, Finset.mem_product.2 ⟨h₂, h₃⟩⟩)`.
-/
theorem vPP1_le_kapPar (l g h ell : ℕ) {w₁ w₂ w₃ : Finset ℤ} (h₁ : w₁ ∈ wins g h)
    (h₂ : w₂ ∈ wins g h) (h₃ : w₃ ∈ wins g h) :
    vPP1 l ell (w₁ ∪ w₂ ∪ w₃) ≤ kapPar l g h ell := by
  unfold kapPar
  exact Finset.le_sup (f := fun w : Finset ℤ × Finset ℤ × Finset ℤ => vPP1 l ell (w.1 ∪ w.2.1 ∪ w.2.2))
    (b := (w₁, w₂, w₃)) (Finset.mem_product.2 ⟨h₁, Finset.mem_product.2 ⟨h₂, h₃⟩⟩)

/- English proof (translation)
Consider the cases of `kind with`. Consider the case `thin`. Use `⟨_, Ico_mem_windows (g := g) (h := h) 0 0 (by omega) (by omega) (by omega) (by omega), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win2, Finset.mem_Icc] at hx`.

Simplify using `only [Finset.mem_union, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Consider the case `up`. Establish `hb'` using `hb (by simp)`. Use `⟨_, Ico_mem_windows (g := g) (h := h) (-(b : ℤ) - g) g (by omega) (by omega) (by omega) (by omega), ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win2, Finset.mem_union, Finset.mem_Icc] at hx`. Simplify using `only [Finset.mem_union, Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Consider the case `down`.

Establish `hb'` using `hb (by simp)`. Use `⟨_, Ico_mem_windows (g := g) (h := h) ((b : ℤ) - g) g (by omega) (by omega) (by omega) (by omega), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win2, Finset.mem_union, Finset.mem_Icc] at hx`. Simplify using `only [Finset.mem_union, Finset.mem_Ico]`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exponent_window_subset_short (g h S : ℕ) (hgh : g ≤ h) (kind : Kind) (b : ℕ) (hb : kind ≠ Kind.thin → b + S ≤ h) :
    ∃ w ∈ wins g h, Formalism.ExponentWindows.E.win2 kind g b ⊆ Finset.Ico (-(g : ℤ)) (-(g : ℤ) + (g : ℕ)) ∪ w := by
  cases kind with
  | thin =>
    refine ⟨_, Ico_mem_windows (g := g) (h := h) 0 0 (by omega) (by omega) (by omega) (by omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win2, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  | up =>
    have hb' := hb (by simp)
    refine ⟨_, Ico_mem_windows (g := g) (h := h) (-(b : ℤ) - g) g (by omega) (by omega) (by omega)
      (by omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win2, Finset.mem_union, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega
  | down =>
    have hb' := hb (by simp)
    refine ⟨_, Ico_mem_windows (g := g) (h := h) ((b : ℤ) - g) g (by omega) (by omega) (by omega)
      (by omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win2, Finset.mem_union, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    omega

/- English proof (translation)
Establish `hm1 : G ≤ max G η` using `le_max_left _ _`. Establish `hm2 : η ≤ max G η` using `le_max_right _ _`. Consider the cases of `kind with`. Consider the case `thin`. Use `⟨_, Ico_mem_windows (g := g) (h := h) 0 0 (by omega) (by omega) (by omega) (by omega), ?_⟩` and prove the remaining obligations.

Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win4, Finset.mem_Icc] at hx`. Simplify using `only [Finset.mem_union, Finset.mem_Ico]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.

Consider the case `up`. Establish `hb'` using `hb (by simp)`. Use `⟨_, Ico_mem_windows (g := g) (h := h) (-(b : ℤ) - S - g) (S + g) (by omega) (by omega) (by omega) (by push_cast; omega), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win4, Finset.mem_union, Finset.mem_Icc] at hx`.

Simplify using `only [Finset.mem_union, Finset.mem_Ico]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers. Consider the case `down`. Establish `hb'` using `hb (by simp)`.

Use `⟨_, Ico_mem_windows (g := g) (h := h) ((b : ℤ) - g) (S + g) (by omega) (by omega) (by omega) (by push_cast; omega), ?_⟩` and prove the remaining obligations. Introduce `x hx`. Simplify using `only [Formalism.ExponentWindows.E.win4, Finset.mem_union, Finset.mem_Icc] at hx`. Simplify using `only [Finset.mem_union, Finset.mem_Ico]`. Use `push_cast`.

Use linear arithmetic over natural numbers and integers.
-/
theorem exponent_window_subset_long (g G S η h : ℕ) (hG : G ≤ g) (hS : S ≤ g) (hη : η ≤ g) (hgh : g ≤ h) (kind : Kind)
    (b : ℕ) (hb : kind ≠ Kind.thin → b + S ≤ h) :
    ∃ w ∈ wins g h, Formalism.ExponentWindows.E.win4 kind g G S η b ⊆
      Finset.Ico (-(max G η : ℕ) - (g : ℤ)) (-(max G η : ℕ) - (g : ℤ) + (2 * max G η + g : ℕ)) ∪ w := by
  have hm1 : G ≤ max G η := le_max_left _ _
  have hm2 : η ≤ max G η := le_max_right _ _
  cases kind with
  | thin =>
    refine ⟨_, Ico_mem_windows (g := g) (h := h) 0 0 (by omega) (by omega) (by omega) (by omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win4, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    push_cast
    omega
  | up =>
    have hb' := hb (by simp)
    refine ⟨_, Ico_mem_windows (g := g) (h := h) (-(b : ℤ) - S - g) (S + g) (by omega) (by omega)
      (by omega) (by push_cast; omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win4, Finset.mem_union, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    push_cast
    omega
  | down =>
    have hb' := hb (by simp)
    refine ⟨_, Ico_mem_windows (g := g) (h := h) ((b : ℤ) - g) (S + g) (by omega) (by omega)
      (by omega) (by push_cast; omega), ?_⟩
    intro x hx
    simp only [Formalism.ExponentWindows.E.win4, Finset.mem_union, Finset.mem_Icc] at hx
    simp only [Finset.mem_union, Finset.mem_Ico]
    push_cast
    omega

/- English proof (translation)
The claim follows from `Ico_mem_windows _ _ (by omega) (by omega) (by omega) (by omega)`.
-/
theorem central_window_mem_short (g h : ℕ) (hgh : g ≤ h) :
    Finset.Ico (-(g : ℤ)) (-(g : ℤ) + (g : ℕ)) ∈ wins g h :=
  Ico_mem_windows _ _ (by omega) (by omega) (by omega) (by omega)

/- English proof (translation)
Establish `hm : max G η ≤ g` using `max_le hG hη`. Conclude with `Ico_mem_windows _ _ (by omega) (by omega) (by omega) (by push_cast; omega)`.
-/
theorem central_window_mem_long (g G η h : ℕ) (hG : G ≤ g) (hη : η ≤ g) (hgh : g ≤ h) :
    Finset.Ico (-(max G η : ℕ) - (g : ℤ)) (-(max G η : ℕ) - (g : ℤ) + (2 * max G η + g : ℕ)) ∈
      wins g h := by
  have hm : max G η ≤ g := max_le hG hη
  exact Ico_mem_windows _ _ (by omega) (by omega) (by omega) (by push_cast; omega)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Take `⟨w₀, hw₀, hs₀⟩` from `exponent_window_subset_short g h S hgh (kind t₀) (b t₀) (hb t₀)`. Take `⟨w₁, hw₁, hs₁⟩` from `exponent_window_subset_short g h S hgh (kind t₁) (b t₁) (hb t₁)`. Use `le_trans (kappa_exponent_le_valuation l (ell - 1) L ?_ (by omega)) (vPP1_le_kapPar l g h L (central_window_mem_short g h hgh) hw₀ hw₁)` and prove the remaining obligations. Introduce `x hx`.

Take `⟨s, hs, hxs⟩` from `Finset.mem_biUnion.1 hx`. Establish `hs' : s < ell` using `Finset.mem_range.1 hs`. Distinguish the cases in `h0 : s = t₀`. Substitute `h0` using the available equality. Break down `Finset.mem_union.1 (hs₀ hxs) with h | h` into its components or cases.

Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ h)`. Conclude with `Finset.mem_union_left _ (Finset.mem_union_right _ h)`. Distinguish the cases in `h1 : s = t₁`. Substitute `h1` using the available equality. Break down `Finset.mem_union.1 (hs₁ hxs) with h | h` into its components or cases.

Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ h)`. Conclude with `Finset.mem_union_right _ h`. Rewrite `hxs` using `[ht s hs' h0 h1]`. Use `Finset.mem_union_left _ (Finset.mem_union_left _ ?_)` and prove the remaining obligations. Simplify using `only [Formalism.ExponentWindows.E.win2, Finset.mem_Icc] at hxs`.

Simplify using `only [Finset.mem_Ico]`. Use linear arithmetic over natural numbers and integers. Take `⟨w₀, hw₀, hs₀⟩` from `exponent_window_subset_long g G S η h hG hS hη hgh (kind t₀) (b t₀) (hb t₀)`. Take `⟨w₁, hw₁, hs₁⟩` from `exponent_window_subset_long g G S η h hG hS hη hgh (kind t₁) (b t₁) (hb t₁)`. Use `le_trans (kappa_exponent_le_valuation l (ell - 1) L ?_ (by omega)) (vPP1_le_kapPar l g h L (central_window_mem_long g G η h hG hη hgh) hw₀ hw₁)` and prove the remaining obligations.

Introduce `x hx`. Take `⟨s, hs, hxs⟩` from `Finset.mem_biUnion.1 hx`. Establish `hs' : s < ell` using `Finset.mem_range.1 hs`. Distinguish the cases in `h0 : s = t₀`. Substitute `h0` using the available equality.

Break down `Finset.mem_union.1 (hs₀ hxs) with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ h)`. Conclude with `Finset.mem_union_left _ (Finset.mem_union_right _ h)`. Distinguish the cases in `h1 : s = t₁`. Substitute `h1` using the available equality.

Break down `Finset.mem_union.1 (hs₁ hxs) with h | h` into its components or cases. Conclude with `Finset.mem_union_left _ (Finset.mem_union_left _ h)`. Conclude with `Finset.mem_union_right _ h`. Rewrite `hxs` using `[ht s hs' h0 h1]`. Use `Finset.mem_union_left _ (Finset.mem_union_left _ ?_)` and prove the remaining obligations.

Establish `hm1 : G ≤ max G η` using `le_max_left _ _`. Simplify using `only [Formalism.ExponentWindows.E.win4, Finset.mem_Icc] at hxs`. Simplify using `only [Finset.mem_Ico]`. Use `push_cast`. Use linear arithmetic over natural numbers and integers.
-/
theorem kapOK_arc (l g G S η h ell L : ℕ) (hG : G ≤ g) (hS : S ≤ g) (hη : η ≤ g) (hgh : g ≤ h)
    (kind : ℕ → Kind) (b : ℕ → ℕ) (hb : ∀ s, kind s ≠ Kind.thin → b s + S ≤ h) (hL : ell ≤ L)
    (t₀ t₁ : ℕ) (ht : ∀ s < ell, s ≠ t₀ → s ≠ t₁ → kind s = Kind.thin) :
    Formalism.ExponentWindows.E.kapExp l (ell - 1) (Formalism.ExponentWindows.E.jumpWindows ell g kind b) ≤ kapPar l g h L ∧
    Formalism.ExponentWindows.E.kapExp l (ell - 1) (Formalism.ExponentWindows.E.wideWindows ell g G S η kind b) ≤ kapPar l g h L := by
  constructor
  · obtain ⟨w₀, hw₀, hs₀⟩ := exponent_window_subset_short g h S hgh (kind t₀) (b t₀) (hb t₀)
    obtain ⟨w₁, hw₁, hs₁⟩ := exponent_window_subset_short g h S hgh (kind t₁) (b t₁) (hb t₁)
    refine le_trans (kappa_exponent_le_valuation l (ell - 1) L ?_ (by omega))
      (vPP1_le_kapPar l g h L (central_window_mem_short g h hgh) hw₀ hw₁)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hx
    have hs' : s < ell := Finset.mem_range.1 hs
    by_cases h0 : s = t₀
    · subst h0
      rcases Finset.mem_union.1 (hs₀ hxs) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    by_cases h1 : s = t₁
    · subst h1
      rcases Finset.mem_union.1 (hs₁ hxs) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h
    · rw [ht s hs' h0 h1] at hxs
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      simp only [Formalism.ExponentWindows.E.win2, Finset.mem_Icc] at hxs
      simp only [Finset.mem_Ico]
      omega
  · obtain ⟨w₀, hw₀, hs₀⟩ := exponent_window_subset_long g G S η h hG hS hη hgh (kind t₀) (b t₀) (hb t₀)
    obtain ⟨w₁, hw₁, hs₁⟩ := exponent_window_subset_long g G S η h hG hS hη hgh (kind t₁) (b t₁) (hb t₁)
    refine le_trans (kappa_exponent_le_valuation l (ell - 1) L ?_ (by omega))
      (vPP1_le_kapPar l g h L (central_window_mem_long g G η h hG hη hgh) hw₀ hw₁)
    intro x hx
    obtain ⟨s, hs, hxs⟩ := Finset.mem_biUnion.1 hx
    have hs' : s < ell := Finset.mem_range.1 hs
    by_cases h0 : s = t₀
    · subst h0
      rcases Finset.mem_union.1 (hs₀ hxs) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_left _ (Finset.mem_union_right _ h)
    by_cases h1 : s = t₁
    · subst h1
      rcases Finset.mem_union.1 (hs₁ hxs) with h | h
      · exact Finset.mem_union_left _ (Finset.mem_union_left _ h)
      · exact Finset.mem_union_right _ h
    · rw [ht s hs' h0 h1] at hxs
      refine Finset.mem_union_left _ (Finset.mem_union_left _ ?_)
      have hm1 : G ≤ max G η := le_max_left _ _
      simp only [Formalism.ExponentWindows.E.win4, Finset.mem_Icc] at hxs
      simp only [Finset.mem_Ico]
      push_cast
      omega

/- English proof (translation)
Establish `h3 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2` using `by omega`. Break down `h3 with h0 | h1 | h2` into its components or cases. Rewrite `h0` using `[Finset.card_eq_zero]`. Conclude with `⟨0, 0, by simp [h0]⟩`. Take `⟨a, rfl⟩` from `Finset.card_eq_one.1 h1`.

Conclude with `⟨a, a, by simp⟩`. Take `⟨a, b, _, rfl⟩` from `Finset.card_eq_two.1 h2`. Conclude with `⟨a, b, subset_rfl⟩`.
-/
theorem exists_two_of_card_le {s : Finset ℕ} (h : s.card ≤ 2) : ∃ a b : ℕ, s ⊆ {a, b} := by
  have h3 : s.card = 0 ∨ s.card = 1 ∨ s.card = 2 := by omega
  rcases h3 with h0 | h1 | h2
  · rw [Finset.card_eq_zero] at h0
    exact ⟨0, 0, by simp [h0]⟩
  · obtain ⟨a, rfl⟩ := Finset.card_eq_one.1 h1
    exact ⟨a, a, by simp⟩
  · obtain ⟨a, b, _, rfl⟩ := Finset.card_eq_two.1 h2
    exact ⟨a, b, subset_rfl⟩

/- English proof (translation)
Take `⟨a, b, hab⟩` from `exists_two_of_card_le h`. Use `⟨a, b, fun s hs ha hb => ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hmem : s ∈ thickLv ty arcLen c`. Unfold `thickLv`.

Conclude with `Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, kdOf_thick.2 hne⟩`. Use `hab hmem` as an intermediate fact. Simplify using `only [Finset.mem_insert, Finset.mem_singleton] at this`. Use linear arithmetic over natural numbers and integers.
-/
theorem two_thick {n : ℕ} {ty : ZMod n → LT} {arcLen : ZMod n → ℕ} {c : ZMod n}
    (h : ro ty arcLen c ≤ 2) :
    ∃ t₀ t₁ : ℕ, ∀ s < arcLen c, s ≠ t₀ → s ≠ t₁ →
      Formalism.ExponentWindows.E.kindAt (kdOf ty) c s = Kind.thin := by
  obtain ⟨a, b, hab⟩ := exists_two_of_card_le h
  refine ⟨a, b, fun s hs ha hb => ?_⟩
  by_contra hne
  have hmem : s ∈ thickLv ty arcLen c := by
    unfold thickLv
    exact Finset.mem_filter.2 ⟨Finset.mem_range.2 hs, kdOf_thick.2 hne⟩
  have := hab hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at this
  omega

/- English proof (translation)
Use `⟨two_thick (hT c hc), fun s₀ s₁ h01 h1 => ⟨fun hd hu => ?_, fun hu hd => ?_⟩⟩` and prove the remaining obligations. Conclude with `(hW c hc s₀ s₁ h01 h1 _ _).1 (kdOf_down hd) (kdOf_up hu)`. Conclude with `(hW c hc s₀ s₁ h01 h1 _ _).2 (kdOf_up hu) (kdOf_down hd)`.
-/
theorem textWord_of {n : ℕ} (l a₀ : ℕ) {ty : ZMod n → LT} {cuts : Finset (ZMod n)}
    {arcLen : ZMod n → ℕ} (hT : ThickLe2 ty cuts arcLen) (hW : WordOK l a₀ ty cuts arcLen)
    (c : ZMod n) (hc : c ∈ cuts) :
    Formalism.ExponentWindows.E.TextWord l (arcLen c) a₀ (Formalism.ExponentWindows.E.sizeAt (bbOf ty) c)
      (Formalism.ExponentWindows.E.kindAt (kdOf ty) c) := by
  refine ⟨two_thick (hT c hc), fun s₀ s₁ h01 h1 => ⟨fun hd hu => ?_, fun hu hd => ?_⟩⟩
  · exact (hW c hc s₀ s₁ h01 h1 _ _).1 (kdOf_down hd) (kdOf_up hu)
  · exact (hW c hc s₀ s₁ h01 h1 _ _).2 (kdOf_up hu) (kdOf_down hd)

/- English proof (translation)
Break down `hS i with ⟨h1, h2⟩ | h3` into its components or cases. Use `⟨?_, h2⟩` and prove the remaining obligations. Unfold `bbOf`. Unfold `kdOf at hi`. Apply the tactic sequence `cases h' : ty i <;> simp [h', LT.ok, LT.size] at hi h1 ⊢`.

Conclude with `h1`. Conclude with `h1`. Conclude with `absurd (kdOf_thin.2 h3) hi`.
-/
theorem size_of_sizesOK {n : ℕ} {g S h : ℕ} {ty : ZMod n → LT} (hS : SizesOK g S h ty) (i : ZMod n)
    (hi : kdOf ty i ≠ Kind.thin) : g < bbOf ty i ∧ bbOf ty i + S ≤ h := by
  rcases hS i with ⟨h1, h2⟩ | h3
  · refine ⟨?_, h2⟩
    unfold bbOf
    unfold kdOf at hi
    cases h' : ty i <;> simp [h', LT.ok, LT.size] at hi h1 ⊢
    · exact h1
    · exact h1
  · exact absurd (kdOf_thin.2 h3) hi

/- English proof (translation)
The claim follows from `G_le_gPar _ _ _ S_le_g := S_le_gPar _ _ _ η_le_g := η_le_gPar _ _ _ g_le_h := hgh g_lt_b := fun i hi => (size_of_sizesOK hS i hi).1 b_le_h := fun i hi => (size_of_sizesOK hS i hi).2 one_le_j := hC.2.1 thin_after := fun c hc k h1 h2 => kdOf_thin.2 (hC.2.2.2.2 c hc k h1 h2) j_le_el …`.
-/
theorem finalNum_of (l : ℕ) (hl : 3 ≤ l) (n : ℕ) [NeZero n] (j Gp S η h : ℕ) (ty : ZMod n → LT)
    (cuts : Finset (ZMod n)) (arcLen : ZMod n → ℕ) (H₁ H₂ : ZMod n → ℕ)
    (hC : CutsOK n j ty cuts arcLen) (hgh : gPar Gp S η ≤ h) (hS : SizesOK (gPar Gp S η) S h ty)
    (hT : ThickLe2 ty cuts arcLen)
    (hW : WordOK l (initialExponentBound l n j (gPar Gp S η) h H₁ H₂ cuts arcLen) ty cuts arcLen) :
    Formalism.ExponentWindows.E.FinalNum l (cutsOf hC) (kdOf ty) (bbOf ty) j (gPar Gp S η) Gp S η h
      (sigPar l (gPar Gp S η) h j) (rrPar l n H₁ H₂ cuts)
      (kapPar l (gPar Gp S η) h (ellMax cuts arcLen)) (ellMax cuts arcLen) where
  G_le_g := G_le_gPar _ _ _
  S_le_g := S_le_gPar _ _ _
  η_le_g := η_le_gPar _ _ _
  g_le_h := hgh
  g_lt_b := fun i hi => (size_of_sizesOK hS i hi).1
  b_le_h := fun i hi => (size_of_sizesOK hS i hi).2
  one_le_j := hC.2.1
  thin_after := fun c hc k h1 h2 => kdOf_thin.2 (hC.2.2.2.2 c hc k h1 h2)
  j_le_ell := fun c hc => hC.2.2.2.1 c hc
  ell_le := fun c hc => Finset.le_sup (f := arcLen) hc
  word := fun c hc => textWord_of l _ hT hW c hc
  sigOK := sigOK_of l _ h j hl
  kapOK := fun c hc => by
    obtain ⟨t₀, t₁, ht⟩ := two_thick (hT c hc)
    exact kapOK_arc l (gPar Gp S η) Gp S η h (arcLen c) (ellMax cuts arcLen) (G_le_gPar _ _ _)
      (S_le_gPar _ _ _) (η_le_gPar _ _ _) hgh _ _
      (fun s hs => (size_of_sizesOK hS _ hs).2) (Finset.le_sup (f := arcLen) hc) t₀ t₁ ht

end Formalism.MainNotions.WachCoordinates
