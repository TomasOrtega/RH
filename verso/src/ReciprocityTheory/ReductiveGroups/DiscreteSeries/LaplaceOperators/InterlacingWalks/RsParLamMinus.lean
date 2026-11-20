import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.LowerStepStatement
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.AdjGap
import ReciprocityTheory.ReductiveGroups.DiscreteSeries.LaplaceOperators.InterlacingWalks.Imports

noncomputable section

namespace ReciprocityTheory.ChartRestriction.DS.Lap

open ReciprocityTheory.ChartRestriction.DS

def rsExt {N : ℕ} (f : Fin N → ℝ) (x : ℕ) : ℝ := if h : x < N then f ⟨x, h⟩ else 0

/- English proof (translation)
Rewrite using `[rsExt, dif_pos h]`.
-/
theorem rsExt_mk {N : ℕ} (f : Fin N → ℝ) (x : ℕ) (h : x < N) : f ⟨x, h⟩ = rsExt f x := by
  rw [rsExt, dif_pos h]

def rsG (B : ℕ → ℝ) (t j m q : ℕ) : ℝ :=
  if q < j then -B q else if q = j then -B q - (j : ℝ) * t + m else -B q - (q : ℝ) * t

def rsF (k : ℕ) (U B : ℕ → ℝ) (t j m x : ℕ) : ℝ :=
  if x < k then U x - 1 / 2 else rsG B t j m (x - (k - 1))

def rsPt (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ) :
    Fin (2 * r + k + 1) → ℝ :=
  fun a => rsF k (rsExt u) (rsExt b) t j m a.val

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `ha` using `a.isLt`. Simplify using `only [rsPt, rsF, rsG, raisePar, rsExt]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)`.
-/
theorem rsPt_zero (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j 0 = raisePar k r u b t j := by
  funext a
  have ha := a.isLt
  simp only [rsPt, rsF, rsG, raisePar, rsExt]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `ha` using `a.isLt`. Simplify using `only [rsPt, rsF, rsG, raisePar, rsExt]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)`.
-/
theorem rsPt_top (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j : ℕ) :
    rsPt k r u b t j (j * t) = raisePar k r u b t (j + 1) := by
  funext a
  have ha := a.isLt
  simp only [rsPt, rsF, rsG, raisePar, rsExt]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `ha` using `a.isLt`. Simplify using `only [Pi.add_apply, Pi.single_apply, rsPt, rsF, rsG, rsExt, Fin.ext_iff, Fin.val_mk]`. Apply the tactic sequence `split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)`.
-/
theorem rsPt_succ (k r : ℕ) (u : Fin k → ℝ) (b : Fin (2 * r + 2) → ℝ) (t j m : ℕ)
    (hk : 1 ≤ k) (hj : 1 ≤ j) (hj2 : j ≤ 2 * r + 1) :
    rsPt k r u b t j (m + 1) =
      rsPt k r u b t j m + Pi.single (⟨j + k - 1, by omega⟩ : Fin (2 * r + k + 1)) 1 := by
  funext a
  have ha := a.isLt
  simp only [Pi.add_apply, Pi.single_apply, rsPt, rsF, rsG, rsExt, Fin.ext_iff, Fin.val_mk]
  split_ifs <;> first | (exfalso; omega) | ring1 | (push_cast; ring1) | (subst_vars; push_cast; ring1) | (subst_vars; ring1)

/- English proof (translation)
Establish `hBq` using `hBlt q hq`. Establish `hgq` using `hBgap q hq`. Establish `hmR : (m : ℝ) ≤ (j : ℝ) * t` using `by exact_mod_cast hm`. Establish `ht : (0 : ℝ) ≤ t` using `Nat.cast_nonneg t`. Establish `hm0 : (0 : ℝ) ≤ m` using `Nat.cast_nonneg m`.

Establish `e1 : ((q : ℝ) + 1) * t = (q : ℝ) * t + t` using `by ring`. Unfold `rsG`. Break down `lt_trichotomy (q + 1) j with h1 | h1 | h1` into its components or cases. Rewrite using `[if_pos h1, if_pos (show q < j by omega)]`. Apply the tactic sequence `constructor <;> linarith`.

Rewrite using `[if_neg (show ¬ q + 1 < j by omega), if_pos h1, if_pos (show q < j by omega)]`. Apply the tactic sequence `constructor <;> linarith`. Break down `Nat.lt_or_ge j q with h2 | h2` into its components or cases. Rewrite using `[if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega), if_neg (show ¬ q < j by omega), if_neg (show q ≠ j by omega)]`. Use `push_cast`.

Establish `hqt : (0 : ℝ) ≤ (q : ℝ) * t` using `by positivity`. Apply the tactic sequence `constructor <;> linarith`. Establish `hqj : q = j` using `by omega`. Establish `hqt : (q : ℝ) * t = (j : ℝ) * t` using `by rw [hqj]`. Rewrite using `[if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega), if_neg (show ¬ q < j by omega), if_pos hqj]`.

Use `push_cast`. Apply the tactic sequence `constructor <;> linarith`.
-/
theorem rsG_step (B : ℕ → ℝ) (h : ℝ) (t j m q N : ℕ) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < N → B q < B (q + 1)) (hBgap : ∀ q, q + 1 < N → h ≤ B (q + 1) - B q)
    (hq : q + 1 < N) :
    rsG B t j m (q + 1) < rsG B t j m q ∧ h ≤ rsG B t j m q - rsG B t j m (q + 1) := by
  have hBq := hBlt q hq
  have hgq := hBgap q hq
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have ht : (0 : ℝ) ≤ t := Nat.cast_nonneg t
  have hm0 : (0 : ℝ) ≤ m := Nat.cast_nonneg m
  have e1 : ((q : ℝ) + 1) * t = (q : ℝ) * t + t := by ring
  unfold rsG
  rcases lt_trichotomy (q + 1) j with h1 | h1 | h1
  · rw [if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rw [if_neg (show ¬ q + 1 < j by omega), if_pos h1, if_pos (show q < j by omega)]
    constructor <;> linarith
  · rcases Nat.lt_or_ge j q with h2 | h2
    · rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_neg (show q ≠ j by omega)]
      push_cast
      have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
      constructor <;> linarith
    · have hqj : q = j := by omega
      have hqt : (q : ℝ) * t = (j : ℝ) * t := by rw [hqj]
      rw [if_neg (show ¬ q + 1 < j by omega), if_neg (show q + 1 ≠ j by omega),
        if_neg (show ¬ q < j by omega), if_pos hqj]
      push_cast
      constructor <;> linarith

/- English proof (translation)
Establish `hmR : (m : ℝ) ≤ (j : ℝ) * t` using `by exact_mod_cast hm`. Establish `hqt : (0 : ℝ) ≤ (q : ℝ) * t` using `by positivity`. Unfold `rsG`. Apply the tactic sequence `split_ifs <;> linarith`.
-/
theorem rsG_le (B : ℕ → ℝ) (t j m q : ℕ) (hm : m ≤ j * t) : rsG B t j m q ≤ -B q := by
  have hmR : (m : ℝ) ≤ (j : ℝ) * t := by exact_mod_cast hm
  have hqt : (0 : ℝ) ≤ (q : ℝ) * t := by positivity
  unfold rsG
  split_ifs <;> linarith

/- English proof (translation)
Unfold `rsG`. Use `split_ifs`. Conclude with `⟨0, by simp⟩`. Conclude with `⟨(m : ℤ) - (j : ℤ) * (t : ℤ), by push_cast; ring⟩`. Conclude with `⟨-((q : ℤ) * (t : ℤ)), by push_cast; ring⟩`.
-/
theorem rsG_int (B : ℕ → ℝ) (t j m q : ℕ) : ∃ z : ℤ, rsG B t j m q = -B q + z := by
  unfold rsG
  split_ifs
  · exact ⟨0, by simp⟩
  · exact ⟨(m : ℤ) - (j : ℤ) * (t : ℤ), by push_cast; ring⟩
  · exact ⟨-((q : ℤ) * (t : ℤ)), by push_cast; ring⟩

/- English proof (translation)
Distinguish the cases in `hx1 : x + 1 < k`. Establish `hx0 : x < k` using `by omega`. Rewrite using `[rsF, rsF, if_pos hx1, if_pos hx0]`. Conclude with `⟨by linarith [hUlt x hx1], fun h' => absurd h' (by omega)⟩`. Distinguish the cases in `hx0 : x < k`.

Establish `hxk : x = k - 1` using `by omega`. Establish `e : x + 1 - (k - 1) = 1` using `by omega`. Rewrite using `[rsF, rsF, if_neg hx1, if_pos hx0, e]`. Establish `hle` using `rsG_le B t j m 1 hm`. Establish `hb01 : B 0 < B 1` using `hBlt 0 (by omega)`.

Establish `hg01 : h ≤ B 1 - B 0` using `hBgap 0 (by omega)`. Establish `hU : U x = U (k - 1)` using `by rw [hxk]`. Prove the components needed by the constructor for the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Introduce `_`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hq : x - (k - 1) + 1 < 2 * r + 2` using `by omega`. Establish `e : x + 1 - (k - 1) = x - (k - 1) + 1` using `by omega`. Rewrite using `[rsF, rsF, if_neg hx1, if_neg hx0, e]`. Take `⟨h1, h2⟩` from `rsG_step B h t j m (x - (k - 1)) (2 * r + 2) hm hBlt hBgap hq`.

Conclude with `⟨h1, fun _ => h2⟩`.
-/
theorem rsF_step (k r : ℕ) (U B : ℕ → ℝ) (h : ℝ) (t j m x : ℕ) (hk : 1 ≤ k) (hm : m ≤ j * t)
    (hBlt : ∀ q, q + 1 < 2 * r + 2 → B q < B (q + 1))
    (hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ B (q + 1) - B q)
    (hUlt : ∀ x, x + 1 < k → U (x + 1) < U x) (hUhalf : -B 0 ≤ U (k - 1) - 1 / 2)
    (hx : x + 1 < 2 * r + k + 1) :
    rsF k U B t j m (x + 1) < rsF k U B t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k U B t j m x - rsF k U B t j m (x + 1)) := by
  by_cases hx1 : x + 1 < k
  · have hx0 : x < k := by omega
    rw [rsF, rsF, if_pos hx1, if_pos hx0]
    exact ⟨by linarith [hUlt x hx1], fun h' => absurd h' (by omega)⟩
  · by_cases hx0 : x < k
    · have hxk : x = k - 1 := by omega
      have e : x + 1 - (k - 1) = 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_pos hx0, e]
      have hle := rsG_le B t j m 1 hm
      have hb01 : B 0 < B 1 := hBlt 0 (by omega)
      have hg01 : h ≤ B 1 - B 0 := hBgap 0 (by omega)
      have hU : U x = U (k - 1) := by rw [hxk]
      constructor
      · linarith
      · intro _
        linarith
    · have hq : x - (k - 1) + 1 < 2 * r + 2 := by omega
      have e : x + 1 - (k - 1) = x - (k - 1) + 1 := by omega
      rw [rsF, rsF, if_neg hx1, if_neg hx0, e]
      obtain ⟨h1, h2⟩ := rsG_step B h t j m (x - (k - 1)) (2 * r + 2) hm hBlt hBgap hq
      exact ⟨h1, fun _ => h2⟩

/- English proof (translation)
Establish `h1 : ¬ a.val < k - 1` using `by omega`. Establish `h2 : a.val - (k - 1) < 2 * r + 2` using `by have := a.isLt; omega`. Simplify using `only [parLam, rsExt, dif_neg h1, dif_pos h2]`.
-/
theorem rsParLam_minus (k r : ℕ) (v : Fin (k - 1) → ℝ) (b : Fin (2 * r + 2) → ℝ)
    (a : Fin (2 * r + k + 1)) (ha : k - 1 ≤ a.val) :
    parLam k r v b a = -rsExt b (a.val - (k - 1)) := by
  have h1 : ¬ a.val < k - 1 := by omega
  have h2 : a.val - (k - 1) < 2 * r + 2 := by have := a.isLt; omega
  simp only [parLam, rsExt, dif_neg h1, dif_pos h2]

/- English proof (translation)
Assume the negation of the conclusion as `hcon`. Apply `hne` to reduce the goal to its premises. Establish `e1 : parEps k r a = true` using `by show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true`. Rewrite using `[if_pos (show a.val < k - 1 by omega)]`. Establish `e2 : parEps k r ⟨a.val + 1, ha⟩ = true` using `by show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true split_ifs with h1`.

Both sides reduce to the same expression. Establish `: a.val + 1 - (k - 1) = 0` using `by omega`. Simplify using `[this]`. Rewrite using `[e1, e2]`.
-/
theorem rsParEps_same (k r : ℕ) (a : Fin (2 * r + k + 1)) (ha : a.val + 1 < 2 * r + k + 1)
    (hne : parEps k r a ≠ parEps k r ⟨a.val + 1, ha⟩) : k - 1 ≤ a.val := by
  by_contra hcon
  apply hne
  have e1 : parEps k r a = true := by
    show (if a.val < k - 1 then true else decide ((a.val - (k - 1)) % 2 = 0)) = true
    rw [if_pos (show a.val < k - 1 by omega)]
  have e2 : parEps k r ⟨a.val + 1, ha⟩ = true := by
    show (if a.val + 1 < k - 1 then true else decide ((a.val + 1 - (k - 1)) % 2 = 0)) = true
    split_ifs with h1
    · rfl
    · have : a.val + 1 - (k - 1) = 0 := by omega
      simp [this]
  rw [e1, e2]

/- English proof (translation)
Introduce `x y hxy hy`. Proceed by induction on `y with`. Consider the case `zero => omega`. Consider the case `succ y ih`. Break down `Nat.lt_or_ge x y with h1 | h1` into its components or cases.

Conclude with `lt_trans (hg y hy) (ih h1 (by omega))`. Establish `: x = y` using `by omega`. Substitute `this` using the available equality. Conclude with `hg x hy`.
-/
private lemma strictAnti_lt_of_succ_lt (g : ℕ → ℝ) (n : ℕ) (hg : ∀ x, x + 1 < n → g (x + 1) < g x) :
    ∀ x y, x < y → y < n → g y < g x := by
  intro x y hxy hy
  induction y with
  | zero => omega
  | succ y ih =>
    rcases Nat.lt_or_ge x y with h1 | h1
    · exact lt_trans (hg y hy) (ih h1 (by omega))
    · have : x = y := by omega
      subst this
      exact hg x hy

/- English proof (translation)
Establish `h1` using `hgap (y - 1) (by omega) (by omega)`. Establish `e : y - 1 + 1 = y` using `by omega`. Rewrite `h1` using `[e]`. Break down `Nat.lt_or_ge x (y - 1) with h2 | h2` into its components or cases. Use `hanti x (y - 1) h2 (by omega)` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `: x = y - 1` using `by omega`. Rewrite using `[this]`. Conclude with `h1`.
-/
private lemma gap_lemma_2 (g : ℕ → ℝ) (n c : ℕ) (h : ℝ)
    (hanti : ∀ x y, x < y → y < n → g y < g x)
    (hgap : ∀ x, x + 1 < n → c ≤ x → h ≤ g x - g (x + 1))
    (x y : ℕ) (hxy : x < y) (hy : y < n) (hc : c < y) : h ≤ g x - g y := by
  have h1 := hgap (y - 1) (by omega) (by omega)
  have e : y - 1 + 1 = y := by omega
  rw [e] at h1
  rcases Nat.lt_or_ge x (y - 1) with h2 | h2
  · have := hanti x (y - 1) h2 (by omega)
    linarith
  · have : x = y - 1 := by omega
    rw [this]
    exact h1

/- English proof (translation)
Introduce `k r u v b h t P hk hpar hint hhalf hlow hSC j hj hj2 hP`. Establish `hBlt : ∀ q, q + 1 < 2 * r + 2 → rsExt b q < rsExt b (q + 1)`. Introduce `q hq`. Establish `hq0 : q + (k - 1) < 2 * r + k + 1` using `by omega`. Establish `hq1 : q + (k - 1) + 1 < 2 * r + k + 1` using `by omega`.

Establish `h1` using `hpar.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _) : (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)) < ⟨q + (k - 1) + 1, hq1⟩)`. Rewrite `h1` using `[rsParLam_minus k r v b ⟨q + (k - 1) + 1, hq1⟩ (show k - 1 ≤ q + (k - 1) + 1 by omega), rsParLam_minus k r v b ⟨q + (k - 1), hq0⟩ (show k - 1 ≤ q + (k - 1) by omega)]`. Establish `e1 : (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q` using `by show q + (k - 1) - (k - 1) = q`. Use linear arithmetic over natural numbers and integers. Establish `e2 : (⟨q + (k - 1) + 1, hq1⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q + 1` using `by show q + (k - 1) + 1 - (k - 1) = q + 1`.

Use linear arithmetic over natural numbers and integers. Rewrite `h1` using `[e1, e2]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ rsExt b (q + 1) - rsExt b q`. Introduce `q hq`.

Rewrite using `[← rsExt_mk b (q + 1) hq, ← rsExt_mk b q (by omega)]`. Conclude with `hlow ⟨q, by omega⟩ hq`. Establish `hUlt : ∀ x, x + 1 < k → rsExt u (x + 1) < rsExt u x`. Introduce `x hx`. Rewrite using `[← rsExt_mk u (x + 1) hx, ← rsExt_mk u x (by omega)]`.

Establish `h1` using `hint.1 ⟨x, by omega⟩`. Conclude with `lt_trans h1.2 h1.1`. Establish `hUhalf : -rsExt b 0 ≤ rsExt u (k - 1) - 1 / 2`. Establish `hk0 : k - 1 < k` using `by omega`. Establish `h1` using `hint.2 (by omega)`.

Take `⟨z, hz⟩` from `hhalf ⟨k - 1, hk0⟩ ⟨k - 1, by omega⟩`. Rewrite `hz` using `[rsParLam_minus k r v b ⟨k - 1, by omega⟩ (le_refl _)]`. Establish `e0 : rsExt b ((⟨k - 1, by omega⟩ : Fin (2 * r + k + 1)).val - (k - 1)) = b ⟨0, by omega⟩` using `by show rsExt b (k - 1 - (k - 1)) = _`. Rewrite using `[Nat.sub_self, ← rsExt_mk b 0 (by omega)]`. Rewrite `hz` using `[e0]`.

Rewrite using `[← rsExt_mk u (k - 1) hk0, ← rsExt_mk b 0 (by omega)]`. Establish `hz0 : (-1 : ℤ) < z`. Establish `: ((-1 : ℤ) : ℝ) < (z : ℝ)` using `by push_cast; linarith`. Conclude with `this` after adjusting the coercions. Establish `hz1 : (0 : ℝ) ≤ (z : ℝ)` using `by exact_mod_cast (show (0 : ℤ) ≤ z by omega)`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hstep : ∀ m, m ≤ j * t → ∀ x, x + 1 < 2 * r + k + 1 → rsF k (rsExt u) (rsExt b) t j m (x + 1) < rsF k (rsExt u) (rsExt b) t j m x ∧ (k - 1 ≤ x → h ≤ rsF k (rsExt u) (rsExt b) t j m x - rsF k (rsExt u) (rsExt b) t j m (x + 1))` using `fun m hm x hx => rsF_step k r (rsExt u) (rsExt b) h t j m x hk hm hBlt hBgap hUlt hUhalf hx`. Establish `hanti : ∀ m, m ≤ j * t → ∀ x y, x < y → y < 2 * r + k + 1 → rsF k (rsExt u) (rsExt b) t j m y < rsF k (rsExt u) (rsExt b) t j m x` using `fun m hm => strictAnti_lt_of_succ_lt (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1) (fun x hx => (hstep m hm x hx).1)`. Establish `hepsc : ∀ x y : Fin (2 * r + k + 1), x.val < y.val → parEps k r x ≠ parEps k r y → k - 1 < y.val`. Introduce `x y hxy hne`.

Assume the negation of the conclusion as `hcon`. Apply `hne` to reduce the goal to its premises. Establish `e1 : parEps k r x = true` using `by show (if x.val < k - 1 then true else decide ((x.val - (k - 1)) % 2 = 0)) = true`. Rewrite using `[if_pos (show x.val < k - 1 by omega)]`. Establish `e2 : parEps k r y = true` using `by show (if y.val < k - 1 then true else decide ((y.val - (k - 1)) % 2 = 0)) = true split_ifs with h1`.

Both sides reduce to the same expression. Establish `: y.val - (k - 1) = 0` using `by omega`. Simplify using `[this]`. Rewrite using `[e1, e2]`. Establish `hGap : ∀ m, m ≤ j * t → GapAtLeast (parEps k r) (rsPt k r u b t j m) h`.

Introduce `m hm x y hne`. Establish `hg` using `gap_lemma_2 (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1) (k - 1) h (hanti m hm) (fun z hz hc => (hstep m hm z hz).2 hc)`. Break down `lt_trichotomy x.val y.val with h1 | h1 | h1` into its components or cases. Conclude with `le_trans (hg x.val y.val h1 y.isLt (hepsc x y h1 hne)) (le_abs_self _)`. Conclude with `absurd (congrArg (parEps k r) (Fin.ext h1)) hne`.

Rewrite using `[abs_sub_comm]`. Conclude with `le_trans (hg y.val x.val h1 x.isLt (hepsc y x h1 (Ne.symm hne))) (le_abs_self _)`. Establish `hHC : ∀ m, m ≤ j * t → IsHCPar (rsPt k r u b t j m)`. Introduce `m hm`. Use `⟨fun x y hxy => hanti m hm x.val y.val hxy y.isLt, fun x => ?_⟩` and prove the remaining obligations.

Take `⟨z2, hz2⟩` from `hpar.2 x`. Distinguish the cases in `hx : x.val < k`. Take `⟨z1, hz1⟩` from `hhalf ⟨x.val, hx⟩ x`. Use `⟨z1 + z2, ?_⟩` and prove the remaining obligations. Use `show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _`.

Rewrite using `[rsF, if_pos hx, ← rsExt_mk u x.val hx, Int.cast_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨z3, hz3⟩` from `rsG_int (rsExt b) t j m (x.val - (k - 1))`. Establish `hl` using `rsParLam_minus k r v b x (by omega)`. Use `⟨z3 + z2, ?_⟩` and prove the remaining obligations.

Use `show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _`. Rewrite using `[rsF, if_neg hx, hz3, Int.cast_add]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `key : ∀ m, m ≤ j * t → P (rsPt k r u b t j m)`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero`. Introduce `_`. Rewrite using `[rsPt_zero]`. Conclude with `hP`.

Consider the case `succ m ih`. Introduce `hm`. Establish `hm' : m ≤ j * t` using `by omega`. Rewrite using `[rsPt_succ k r u b t j m hk hj hj2]`. Use `hSC.2 _ _ (hHC m hm') (hGap m hm') ?_ ?_ ?_ (ih hm')` and prove the remaining obligations.

Rewrite using `[← rsPt_succ k r u b t j m hk hj hj2]`. Conclude with `hHC (m + 1) hm`. Rewrite using `[← rsPt_succ k r u b t j m hk hj hj2]`. Conclude with `hGap (m + 1) hm`. Introduce `i heq`.

Establish `hi : i.val < j + k - 1` using `by have := i.isLt; omega`. Establish `hlt` using `(hHC m hm').1 (Fin.mk_lt_mk.mpr hi : (⟨i.val, by omega⟩ : Fin (2 * r + k + 1)) < ⟨j + k - 1, by omega⟩)`. Establish `hv : rsPt k r u b t j m ⟨i.val, by omega⟩ = u i - 1 / 2` using `by show rsF k (rsExt u) (rsExt b) t j m i.val = u i - 1 / 2`. Rewrite using `[rsF, if_pos i.isLt, ← rsExt_mk u i.val i.isLt]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `key (j * t) le_rfl` as an intermediate fact. Rewrite `this` using `[rsPt_top]`. Then use the resulting hypothesis.
-/
theorem raiseStep : RaiseStepStatement := by
  intro k r u v b h t P hk hpar hint hhalf hlow hSC j hj hj2 hP
  have hBlt : ∀ q, q + 1 < 2 * r + 2 → rsExt b q < rsExt b (q + 1) := by
    intro q hq
    have hq0 : q + (k - 1) < 2 * r + k + 1 := by omega
    have hq1 : q + (k - 1) + 1 < 2 * r + k + 1 := by omega
    have h1 := hpar.1 (Fin.mk_lt_mk.mpr (Nat.lt_succ_self _) :
      (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)) < ⟨q + (k - 1) + 1, hq1⟩)
    rw [rsParLam_minus k r v b ⟨q + (k - 1) + 1, hq1⟩ (show k - 1 ≤ q + (k - 1) + 1 by omega),
      rsParLam_minus k r v b ⟨q + (k - 1), hq0⟩ (show k - 1 ≤ q + (k - 1) by omega)] at h1
    have e1 : (⟨q + (k - 1), hq0⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q := by
      show q + (k - 1) - (k - 1) = q
      omega
    have e2 : (⟨q + (k - 1) + 1, hq1⟩ : Fin (2 * r + k + 1)).val - (k - 1) = q + 1 := by
      show q + (k - 1) + 1 - (k - 1) = q + 1
      omega
    rw [e1, e2] at h1
    linarith
  have hBgap : ∀ q, q + 1 < 2 * r + 2 → h ≤ rsExt b (q + 1) - rsExt b q := by
    intro q hq
    rw [← rsExt_mk b (q + 1) hq, ← rsExt_mk b q (by omega)]
    exact hlow ⟨q, by omega⟩ hq
  have hUlt : ∀ x, x + 1 < k → rsExt u (x + 1) < rsExt u x := by
    intro x hx
    rw [← rsExt_mk u (x + 1) hx, ← rsExt_mk u x (by omega)]
    have h1 := hint.1 ⟨x, by omega⟩
    exact lt_trans h1.2 h1.1
  have hUhalf : -rsExt b 0 ≤ rsExt u (k - 1) - 1 / 2 := by
    have hk0 : k - 1 < k := by omega
    have h1 := hint.2 (by omega)
    obtain ⟨z, hz⟩ := hhalf ⟨k - 1, hk0⟩ ⟨k - 1, by omega⟩
    rw [rsParLam_minus k r v b ⟨k - 1, by omega⟩ (le_refl _)] at hz
    have e0 : rsExt b ((⟨k - 1, by omega⟩ : Fin (2 * r + k + 1)).val - (k - 1)) =
        b ⟨0, by omega⟩ := by
      show rsExt b (k - 1 - (k - 1)) = _
      rw [Nat.sub_self, ← rsExt_mk b 0 (by omega)]
    rw [e0] at hz
    rw [← rsExt_mk u (k - 1) hk0, ← rsExt_mk b 0 (by omega)]
    have hz0 : (-1 : ℤ) < z := by
      have : ((-1 : ℤ) : ℝ) < (z : ℝ) := by push_cast; linarith
      exact_mod_cast this
    have hz1 : (0 : ℝ) ≤ (z : ℝ) := by exact_mod_cast (show (0 : ℤ) ≤ z by omega)
    linarith
  have hstep : ∀ m, m ≤ j * t → ∀ x, x + 1 < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m (x + 1) < rsF k (rsExt u) (rsExt b) t j m x ∧
      (k - 1 ≤ x → h ≤ rsF k (rsExt u) (rsExt b) t j m x - rsF k (rsExt u) (rsExt b) t j m (x + 1)) :=
    fun m hm x hx => rsF_step k r (rsExt u) (rsExt b) h t j m x hk hm hBlt hBgap hUlt hUhalf hx
  have hanti : ∀ m, m ≤ j * t → ∀ x y, x < y → y < 2 * r + k + 1 →
      rsF k (rsExt u) (rsExt b) t j m y < rsF k (rsExt u) (rsExt b) t j m x :=
    fun m hm => strictAnti_lt_of_succ_lt (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1)
      (fun x hx => (hstep m hm x hx).1)
  have hepsc : ∀ x y : Fin (2 * r + k + 1), x.val < y.val → parEps k r x ≠ parEps k r y →
      k - 1 < y.val := by
    intro x y hxy hne
    by_contra hcon
    apply hne
    have e1 : parEps k r x = true := by
      show (if x.val < k - 1 then true else decide ((x.val - (k - 1)) % 2 = 0)) = true
      rw [if_pos (show x.val < k - 1 by omega)]
    have e2 : parEps k r y = true := by
      show (if y.val < k - 1 then true else decide ((y.val - (k - 1)) % 2 = 0)) = true
      split_ifs with h1
      · rfl
      · have : y.val - (k - 1) = 0 := by omega
        simp [this]
    rw [e1, e2]
  have hGap : ∀ m, m ≤ j * t → GapAtLeast (parEps k r) (rsPt k r u b t j m) h := by
    intro m hm x y hne
    have hg := gap_lemma_2 (fun z => rsF k (rsExt u) (rsExt b) t j m z) (2 * r + k + 1) (k - 1) h
      (hanti m hm) (fun z hz hc => (hstep m hm z hz).2 hc)
    rcases lt_trichotomy x.val y.val with h1 | h1 | h1
    · exact le_trans (hg x.val y.val h1 y.isLt (hepsc x y h1 hne)) (le_abs_self _)
    · exact absurd (congrArg (parEps k r) (Fin.ext h1)) hne
    · rw [abs_sub_comm]
      exact le_trans (hg y.val x.val h1 x.isLt (hepsc y x h1 (Ne.symm hne))) (le_abs_self _)
  have hHC : ∀ m, m ≤ j * t → IsHCPar (rsPt k r u b t j m) := by
    intro m hm
    refine ⟨fun x y hxy => hanti m hm x.val y.val hxy y.isLt, fun x => ?_⟩
    obtain ⟨z2, hz2⟩ := hpar.2 x
    by_cases hx : x.val < k
    · obtain ⟨z1, hz1⟩ := hhalf ⟨x.val, hx⟩ x
      refine ⟨z1 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_pos hx, ← rsExt_mk u x.val hx, Int.cast_add]
      linarith
    · obtain ⟨z3, hz3⟩ := rsG_int (rsExt b) t j m (x.val - (k - 1))
      have hl := rsParLam_minus k r v b x (by omega)
      refine ⟨z3 + z2, ?_⟩
      show rsF k (rsExt u) (rsExt b) t j m x.val - _ = _
      rw [rsF, if_neg hx, hz3, Int.cast_add]
      linarith
  have key : ∀ m, m ≤ j * t → P (rsPt k r u b t j m) := by
    intro m
    induction m with
    | zero =>
      intro _
      rw [rsPt_zero]
      exact hP
    | succ m ih =>
      intro hm
      have hm' : m ≤ j * t := by omega
      rw [rsPt_succ k r u b t j m hk hj hj2]
      refine hSC.2 _ _ (hHC m hm') (hGap m hm') ?_ ?_ ?_ (ih hm')
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hHC (m + 1) hm
      · rw [← rsPt_succ k r u b t j m hk hj hj2]
        exact hGap (m + 1) hm
      · intro i heq
        have hi : i.val < j + k - 1 := by have := i.isLt; omega
        have hlt := (hHC m hm').1 (Fin.mk_lt_mk.mpr hi :
          (⟨i.val, by omega⟩ : Fin (2 * r + k + 1)) < ⟨j + k - 1, by omega⟩)
        have hv : rsPt k r u b t j m ⟨i.val, by omega⟩ = u i - 1 / 2 := by
          show rsF k (rsExt u) (rsExt b) t j m i.val = u i - 1 / 2
          rw [rsF, if_pos i.isLt, ← rsExt_mk u i.val i.isLt]
        linarith
  have := key (j * t) le_rfl
  rwa [rsPt_top] at this

end ReciprocityTheory.ChartRestriction.DS.Lap
