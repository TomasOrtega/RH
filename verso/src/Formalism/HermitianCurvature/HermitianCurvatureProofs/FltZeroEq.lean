import Formalism.HermitianCurvature.HermitianCurvatureProofs.HermSumRight

open Matrix Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt

namespace Formalism.FourierDecayAlt.P.CutMP.JfS.Sym

noncomputable section

variable {k r : ℕ}

/- English proof (translation)
Establish `orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) → herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0`. Introduce `v hv`. Use `herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))` and prove the remaining obligations. Introduce `b hb`. Simplify using `[hv b hb]`.

Introduce `i hi`. Distinguish the cases in `h1 : i.val < r`. Establish `e` using `herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩`. Rewrite `e` using `[show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl]`. Rewrite using `[← e]`.

Use `orth _ (fun b hb => ?_)` and prove the remaining obligations. Establish `: esI k r b ≠ esI k r ⟨i.val, h1⟩`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[esI] at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, this]`. Distinguish the cases in `h2 : i.val ≤ r + k`. Establish `hw` using `herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2`. Establish `h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0`.

Use `orth _ (fun b hb => ?_)` and prove the remaining obligations. Establish `: esI k r b ≠ i`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[esI] at this`.

Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, this]`. Rewrite `h0` using `[hw]`. Use `split_ifs at h0 with h3`. Conclude with `neg_eq_zero.1 h0`.

Conclude with `h0`. Establish `e : i = esI k r ⟨2 * r + k - i.val, by omega⟩`. Apply `Fin.ext` to reduce the goal to its premises. Simplify using `[esI]`. Use linear arithmetic over natural numbers and integers.

Establish `e2` using `herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩`. Rewrite `e2` using `[← e]`. Rewrite using `[← e2]`. Use `orth _ (fun b hb => ?_)` and prove the remaining obligations. Establish `: esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩`.

Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `[esI, eI] at this`. Use linear arithmetic over natural numbers and integers. Simplify using `[bvec, this]`.
-/
theorem colN {ζ : B.Mat k r} (hζ : B.inLie k r ζ) (z : Fin (2 * r + k + 1) → ℂ)
    (hN : ∀ X ∈ lieOf (Sset k r z), (Matrix.trace (ζ * X)).re = 0) (a : Fin r) :
    ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0 := by
  have orth : ∀ v : Fin (2 * r + k + 1) → ℂ, (∀ b : Fin r, b.val ≤ a.val → v (esI k r b) = 0) →
      herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) v = 0 := by
    intro v hv
    refine herm_zero_of_trace hζ _ v (hN _ (xuv_lieN z a v hv)) (hN _ (xuv_lieN z a _ ?_))
    intro b hb; simp [hv b hb]
  intro i hi
  by_cases h1 : i.val < r
  · have e := herm_es (ζ *ᵥ bvec (eI k r a)) ⟨i.val, h1⟩
    rw [show eI k r ⟨i.val, h1⟩ = i from Fin.ext rfl] at e
    rw [← e]
    refine orth _ (fun b hb => ?_)
    have : esI k r b ≠ esI k r ⟨i.val, h1⟩ := by
      intro h; have := congrArg Fin.val h; simp [esI] at this; omega
    simp [bvec, this]
  · by_cases h2 : i.val ≤ r + k
    · have hw := herm_w (ζ *ᵥ bvec (eI k r a)) i (by omega) h2
      have h0 : herm (Hpk k r) (ζ *ᵥ bvec (eI k r a)) (bvec i) = 0 := by
        refine orth _ (fun b hb => ?_)
        have : esI k r b ≠ i := by
          intro h; have := congrArg Fin.val h; simp [esI] at this; omega
        simp [bvec, this]
      rw [hw] at h0
      split_ifs at h0 with h3
      · exact neg_eq_zero.1 h0
      · exact h0
    · have e : i = esI k r ⟨2 * r + k - i.val, by omega⟩ := by
        apply Fin.ext; simp [esI]; omega
      have e2 := herm_e (ζ *ᵥ bvec (eI k r a)) ⟨2 * r + k - i.val, by omega⟩
      rw [← e] at e2
      rw [← e2]
      refine orth _ (fun b hb => ?_)
      have : esI k r b ≠ eI k r ⟨2 * r + k - i.val, by omega⟩ := by
        intro h; have := congrArg Fin.val h; simp [esI, eI] at this; omega
      simp [bvec, this]

/- English proof (translation)
Introduce `i hi`. Establish `: i ≠ eI k r c` using `by intro h; rw [h] at hi; simp [eI] at hi; omega`. Simplify using `[bvec, this]`.
-/
theorem flt_bvec (a : ℕ) (c : Fin r) (hc : c.val < a) : Flt (k := k) a (bvec (eI k r c)) := by
  intro i hi
  have : i ≠ eI k r c := by intro h; rw [h] at hi; simp [eI] at hi; omega
  simp [bvec, this]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Conclude with `hy i (Nat.zero_le _)`.
-/
theorem flt_zero_eq (y : Fin (2 * r + k + 1) → ℂ) (hy : Flt 0 y) : y = 0 := by
  funext i; exact hy i (Nat.zero_le _)

/- English proof (translation)
Use `set ea := bvec (eI k r a) with hea`. Use `set x := ζ *ᵥ ea with hx`. Use `set xa := x (eI k r a)`. Establish `hea1 : ea (eI k r a) = 1` using `by simp [hea, bvec]`. Establish `hy : Flt a.val (x - xa • ea)`.

Introduce `i hi`. Distinguish the cases in `he : i = eI k r a`. Rewrite using `[he]`. Simplify using `only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]`. Conclude with `sub_self _`.

Establish `hi' : a.val < i.val`. Establish `: i.val ≠ a.val` using `fun h => he (Fin.ext h)`. Use linear arithmetic over natural numbers and integers. Simplify using `[hcol i hi', hea, bvec, he]`. Establish `hζx : ζ *ᵥ x = xa • x`.

Establish `e : x = xa • ea + (x - xa • ea)` using `by abel`. Use `conv_lhs => rw [e]`. Rewrite using `[mulVec_add, mulVec_smul, hkill _ hy, add_zero]`. Establish `hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x`. Introduce `m`.

Proceed by induction on `m with`. Consider the case `zero => simp [hx]`. Consider the case `succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]`. Establish `hxa : xa = 0`. Consider the cases of `N with`.

Consider the case `zero`. It suffices to derive a contradiction. Use `congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)` as an intermediate fact. Simplify using `[hea1] at this`. Consider the case `succ m`.

Use `congrFun (hp m) (eI k r a)` as an intermediate fact. Rewrite `this` using `[hζN, zero_mulVec]`. Simplify using `only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this`. Establish `h2 : xa ^ (m + 1) = 0` using `by rw [pow_succ]; exact this.symm`. Conclude with `(pow_eq_zero_iff'.1 h2).1`.

Establish `: x = x - xa • ea` using `by rw [hxa, zero_smul, sub_zero]`. Rewrite using `[this]`. Conclude with `hy`.
-/
theorem stepNil (ζ : B.Mat k r) (N : ℕ) (hζN : ζ ^ N = 0) (a : Fin r)
    (hcol : ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ζ *ᵥ bvec (eI k r a)) i = 0)
    (hkill : ∀ y, Flt a.val y → ζ *ᵥ y = 0) : Flt a.val (ζ *ᵥ bvec (eI k r a)) := by
  set ea := bvec (eI k r a) with hea
  set x := ζ *ᵥ ea with hx
  set xa := x (eI k r a)
  have hea1 : ea (eI k r a) = 1 := by simp [hea, bvec]
  have hy : Flt a.val (x - xa • ea) := by
    intro i hi
    by_cases he : i = eI k r a
    · rw [he]; simp only [Pi.sub_apply, Pi.smul_apply, hea1, smul_eq_mul, mul_one]; exact sub_self _
    · have hi' : a.val < i.val := by
        have : i.val ≠ a.val := fun h => he (Fin.ext h)
        omega
      simp [hcol i hi', hea, bvec, he]
  have hζx : ζ *ᵥ x = xa • x := by
    have e : x = xa • ea + (x - xa • ea) := by abel
    conv_lhs => rw [e]
    rw [mulVec_add, mulVec_smul, hkill _ hy, add_zero]
  have hp : ∀ m, (ζ ^ (m + 1)) *ᵥ ea = xa ^ m • x := by
    intro m
    induction m with
    | zero => simp [hx]
    | succ m ih => rw [pow_succ', ← mulVec_mulVec, ih, mulVec_smul, hζx, smul_smul, pow_succ]
  have hxa : xa = 0 := by
    cases N with
    | zero =>
      exfalso
      have := congrFun (congrArg (fun M => M *ᵥ ea) hζN) (eI k r a)
      simp [hea1] at this
    | succ m =>
      have := congrFun (hp m) (eI k r a)
      rw [hζN, zero_mulVec] at this
      simp only [Pi.zero_apply, Pi.smul_apply, smul_eq_mul] at this
      have h2 : xa ^ (m + 1) = 0 := by rw [pow_succ]; exact this.symm
      exact (pow_eq_zero_iff'.1 h2).1
  have : x = x - xa • ea := by rw [hxa, zero_smul, sub_zero]
  rw [this]; exact hy

/- English proof (translation)
Establish `hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y)`. Introduce `y`. Rewrite using `[mulVec_mulVec, mulVec_mulVec, hgη]`. Introduce `a`. Proceed by induction on `a with`.

Consider the case `zero`. Introduce `_ y hy`. Rewrite using `[flt_zero_eq y hy, mulVec_zero, mulVec_zero]`. Conclude with `⟨rfl, rfl⟩`. Consider the case `succ a ih`.

Introduce `ha y hy`. Establish `IH` using `ih (by omega)`. Use `set a' : Fin r := ⟨a, by omega⟩`. Establish `hxξ : Flt a (ξ *ᵥ bvec (eI k r a'))` using `stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)`. Establish `hxη : Flt a (η *ᵥ bvec (eI k r a'))` using `stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)`.

Establish `hξa : ξ *ᵥ bvec (eI k r a') = 0`. Use `dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)` and prove the remaining obligations. Rewrite using `[herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]`. Establish `hηa : η *ᵥ bvec (eI k r a') = 0`. Use `dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)` and prove the remaining obligations.

Rewrite using `[← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]`. Use `set ya := y (eI k r a')`. Establish `hrest : Flt a (y - ya • bvec (eI k r a'))`. Introduce `i hi`. Distinguish the cases in `he : i = eI k r a'`.

Rewrite using `[he]`. Simplify using `[bvec, ya]`. Establish `hi' : a + 1 ≤ i.val`. Establish `: i.val ≠ a` using `fun h => he (Fin.ext h)`. Use linear arithmetic over natural numbers and integers.

Simplify using `[hy i hi', bvec, he]`. Establish `e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a'))` using `by abel`. Rewrite using `[e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]`. Simplify using the standard rewrite rules.
-/
theorem killX (z z' : Fin (2 * r + k + 1) → ℂ) (g : B.Mat k r)
    (hD : ∀ a (ha : a ≤ r), Dmin k r z z' g ⟨a, by omega⟩ ≠ 0)
    (ξ η : B.Mat k r) (hξ : B.inLie k r ξ) (N : ℕ) (hξN : ξ ^ N = 0) (hηN : η ^ N = 0)
    (hgη : g * η = ξ * g)
    (colξ : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (ξ *ᵥ bvec (eI k r a)) i = 0)
    (colη : ∀ a : Fin r, ∀ i : Fin (2 * r + k + 1), a.val < i.val → (η *ᵥ bvec (eI k r a)) i = 0) :
    ∀ a, a ≤ r → ∀ y, Flt a y → ξ *ᵥ y = 0 ∧ η *ᵥ y = 0 := by
  have hξg : ∀ y, ξ *ᵥ (g *ᵥ y) = g *ᵥ (η *ᵥ y) := by
    intro y; rw [mulVec_mulVec, mulVec_mulVec, hgη]
  intro a
  induction a with
  | zero =>
    intro _ y hy
    rw [flt_zero_eq y hy, mulVec_zero, mulVec_zero]
    exact ⟨rfl, rfl⟩
  | succ a ih =>
    intro ha y hy
    have IH := ih (by omega)
    set a' : Fin r := ⟨a, by omega⟩
    have hxξ : Flt a (ξ *ᵥ bvec (eI k r a')) := stepNil ξ N hξN a' (colξ a') (fun y hy => (IH y hy).1)
    have hxη : Flt a (η *ᵥ bvec (eI k r a')) := stepNil η N hηN a' (colη a') (fun y hy => (IH y hy).2)
    have hξa : ξ *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_ii z z' g a (by omega) (hD a (by omega)) _ hxξ (fun c hc => ?_)
      rw [herm_skew hξ, hξg, (IH _ (flt_bvec a c hc)).2, mulVec_zero, herm_zero_right, neg_zero]
    have hηa : η *ᵥ bvec (eI k r a') = 0 := by
      refine dlem_i z z' g a (by omega) (hD a (by omega)) _ hxη (fun c hc => ?_)
      rw [← hξg, herm_skew hξ, (IH _ (flt_bvec a c hc)).1, herm_zero_right, neg_zero]
    set ya := y (eI k r a')
    have hrest : Flt a (y - ya • bvec (eI k r a')) := by
      intro i hi
      by_cases he : i = eI k r a'
      · rw [he]; simp [bvec, ya]
      · have hi' : a + 1 ≤ i.val := by
          have : i.val ≠ a := fun h => he (Fin.ext h)
          omega
        simp [hy i hi', bvec, he]
    have e : y = ya • bvec (eI k r a') + (y - ya • bvec (eI k r a')) := by abel
    rw [e, mulVec_add, mulVec_smul, mulVec_add, mulVec_smul, hξa, hηa, (IH _ hrest).1, (IH _ hrest).2]
    simp

end

end Formalism.FourierDecayAlt.P.CutMP.JfS.Sym
