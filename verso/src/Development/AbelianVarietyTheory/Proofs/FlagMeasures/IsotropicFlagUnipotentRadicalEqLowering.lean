import Mathlib
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.LowersMulZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.IsotropicFlagUnipotentRadicalClosedSubgroupKeeps

open MeasureTheory NumberField Matrix Finset Formalism.MainNotions.S GlobalTheory.Count GlobalTheory.FlagMeas GlobalTheory.FlagBase GlobalTheory.RadCov

namespace GlobalTheory.RadFullFlag

/- English proof (translation)
Establish `h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε` using `g.2`. Rewrite using `[star_mulVec, ← dotProduct_mulVec]`. Simplify using `only [mulVec_mulVec, ← Matrix.mul_assoc, h]`.
-/
theorem form_uMat {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star (uMat g *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ (uMat g *ᵥ y)) = star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) := by
  have h : (uMat g)ᴴ * Formalism.REAL.Jm ε * uMat g = Formalism.REAL.Jm ε := g.2
  rw [star_mulVec, ← dotProduct_mulVec]
  simp only [mulVec_mulVec, ← Matrix.mul_assoc, h]

/- English proof (translation)
Establish `h` using `form_uMat g x y`. Simplify using `only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢`. Take the linear combination `h`.
-/
private theorem dotProduct_Jm_uMat_sub_one {n : ℕ} {ε : Fin n → Bool} (g : Formalism.REAL.UJ ε) (x y : Fin n → ℂ) :
    star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) =
      -(star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y)) -
        star ((uMat g - 1) *ᵥ x) ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ ((uMat g - 1) *ᵥ y)) := by
  have h := form_uMat g x y
  simp only [sub_mulVec, one_mulVec, star_sub, mulVec_sub, dotProduct_sub, sub_dotProduct] at h ⊢
  linear_combination h

/- English proof (translation)
Introduce `n a ε W W' hF htop hW'`. Take `⟨hmono, -, hstab, hdual⟩` from `hF`. Establish `hmem : ∀ y, y ∈ W (2 * a + 1)` using `fun y => by rw [htop]; exact Submodule.mem_top`. Establish `horth : ∀ b, b ≤ 2 * a + 1 → ∀ y, y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0` using `fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩`. Use extensionality with `g`.

Establish `hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y` using `fun y => by`. Rewrite using `[sub_mulVec, one_mulVec]`. Unfold `GlobalTheory.FlagMeas.flagN`. Simplify using `only [Set.mem_setOf_eq, mem_lowers, add_zero]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Establish `hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b`. Introduce `b hb y hy`. Use `h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)` as an intermediate fact. Rewrite `this` using `[hW']`.

Rewrite using `[hsub]`. Conclude with `this`. Establish `hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a`. Introduce `y hy`. Establish `hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0`.

Rewrite using `[hW']`. Establish `e : 2 * a + 1 - a = a + 1` using `by omega`. Conclude with `(horth a (by omega) y).1 (by rw [e]; exact hy)`. Use `h2 y hy'` as an intermediate fact. Rewrite `this` using `[hW']`.

Rewrite using `[hsub]`. Conclude with `this`. Establish `hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1), (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k)`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `_ y _`. Simplify using `using hmem ((uMat g - 1) *ᵥ y)`. Consider the case `succ k ih`. Introduce `hk y hy`.

Rewrite using `[horth (k + 1) (by omega)]`. Introduce `x hx`. Establish `hx' : (uMat g - 1) *ᵥ x ∈ W k` using `hlow k (by omega) x hx`. Establish `hyk : y ∈ W (2 * a + 1 - k)`. Establish `e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k` using `by omega`.

Rewrite `hy` using `[e]`. Conclude with `hy`. Establish `hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k)` using `ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)`. Rewrite using `[dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx', (horth k (by omega) _).1 hgy _ hx']`. Simplify using the standard rewrite rules.

Introduce `b y hy`. Break down `lt_trichotomy b a with hb | hb | hb` into its components or cases. Conclude with `hlow b hb y hy`. Substitute `hb` using the available equality. Conclude with `hmid y hy`.

Distinguish the cases in `hbm : 2 * a + 1 ≤ b`. Rewrite using `[hstab b hbm]`. Conclude with `hmem _`. Establish `hk : b = 2 * a + 1 - (2 * a + 1 - b)` using `by omega`. Use `hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)` as an intermediate fact.

Rewrite `this` using `[← hk]`. Conclude with `this`. Introduce `h`. Use `⟨fun i y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite `hy`, the goal using `[hW']`.

Rewrite using `[← hsub]`. Conclude with `h i y hy`. Rewrite `hy`, the goal using `[hW']`. Establish `hy' : y ∈ W (a + 1)`. Establish `e : 2 * a + 1 - a = a + 1` using `by omega`.

Rewrite using `[← e]; exact (horth a (by omega) y).2 hy`. Rewrite using `[← hsub]`. Conclude with `h a y hy'`.
-/
theorem flagN_eq_lowers : ∀ (n a : ℕ) (ε : Fin n → Bool) (W : ℕ → Submodule ℂ (Fin n → ℂ)) (W' : Fin (a + 1) → Submodule ℂ (Fin n → ℂ)), IsDualFlag (Formalism.REAL.Jm ε) W (2 * a + 1) → W (2 * a + 1) = ⊤ → (∀ i : Fin (a + 1), W' i = W i) → flagN ε W' = {g | uMat g - 1 ∈ lowers W 0} := by
  intro n a ε W W' hF htop hW'
  obtain ⟨hmono, -, hstab, hdual⟩ := hF
  have hmem : ∀ y, y ∈ W (2 * a + 1) := fun y => by rw [htop]; exact Submodule.mem_top

  have horth : ∀ b, b ≤ 2 * a + 1 → ∀ y,
      y ∈ W (2 * a + 1 - b) ↔ ∀ x ∈ W b, star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 :=
    fun b hb y => (hdual b hb y).trans ⟨fun h => h.2, fun h => ⟨hmem y, h⟩⟩
  ext g
  have hsub : ∀ y, (uMat g - 1) *ᵥ y = uMat g *ᵥ y - y := fun y => by
    rw [sub_mulVec, one_mulVec]
  unfold GlobalTheory.FlagMeas.flagN
  simp only [Set.mem_setOf_eq, mem_lowers, add_zero]
  constructor
  · rintro ⟨h1, h2⟩

    have hlow : ∀ b, b < a → ∀ y ∈ W (b + 1), (uMat g - 1) *ᵥ y ∈ W b := by
      intro b hb y hy
      have := h1 ⟨b, hb⟩ y (by rw [hW']; exact hy)
      rw [hW'] at this
      rw [hsub]; exact this
    have hmid : ∀ y ∈ W (a + 1), (uMat g - 1) *ᵥ y ∈ W a := by
      intro y hy
      have hy' : ∀ x ∈ W' (Fin.last a), star x ⬝ᵥ (Formalism.REAL.Jm ε *ᵥ y) = 0 := by
        rw [hW']
        have e : 2 * a + 1 - a = a + 1 := by omega
        exact (horth a (by omega) y).1 (by rw [e]; exact hy)
      have := h2 y hy'
      rw [hW'] at this
      rw [hsub]; exact this

    have hup : ∀ k, k ≤ a → ∀ y ∈ W (2 * a + 1 - k + 1),
        (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) := by
      intro k
      induction k with
      | zero =>
        intro _ y _
        simpa using hmem ((uMat g - 1) *ᵥ y)
      | succ k ih =>
        intro hk y hy
        rw [horth (k + 1) (by omega)]
        intro x hx
        have hx' : (uMat g - 1) *ᵥ x ∈ W k := hlow k (by omega) x hx
        have hyk : y ∈ W (2 * a + 1 - k) := by
          have e : 2 * a + 1 - (k + 1) + 1 = 2 * a + 1 - k := by omega
          rw [e] at hy; exact hy
        have hgy : (uMat g - 1) *ᵥ y ∈ W (2 * a + 1 - k) :=
          ih (by omega) y (hmono (by omega : 2 * a + 1 - k ≤ 2 * a + 1 - k + 1) hyk)
        rw [dotProduct_Jm_uMat_sub_one, (horth k (by omega) y).1 hyk _ hx',
          (horth k (by omega) _).1 hgy _ hx']
        simp
    intro b y hy
    rcases lt_trichotomy b a with hb | hb | hb
    · exact hlow b hb y hy
    · subst hb; exact hmid y hy
    · by_cases hbm : 2 * a + 1 ≤ b
      · rw [hstab b hbm]; exact hmem _
      · have hk : b = 2 * a + 1 - (2 * a + 1 - b) := by omega
        have := hup (2 * a + 1 - b) (by omega) y (by rw [← hk]; exact hy)
        rw [← hk] at this; exact this
  · intro h
    refine ⟨fun i y hy => ?_, fun y hy => ?_⟩
    · rw [hW'] at hy ⊢
      rw [← hsub]; exact h i y hy
    · rw [hW'] at hy ⊢
      have hy' : y ∈ W (a + 1) := by
        have e : 2 * a + 1 - a = a + 1 := by omega
        rw [← e]; exact (horth a (by omega) y).2 hy
      rw [← hsub]; exact h a y hy'

end GlobalTheory.RadFullFlag
