import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NotIsPrimZero
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.NonnegSumSmulIntBilinFormToRealMemPsdCone
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SumMulEqOfSumToRealEq
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsStrictFaceOfSmoothConePolyhedralFanStatement

noncomputable section

open NumberField ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.TorRef GlobalTheory.PolFan

namespace GlobalTheory.PolFan.SmoothEnd

section Gen

variable {O : Type} [CommRing O] {bar : O → O} {φ : InvFun O} {X : Type} [AddCommGroup X] [Module O X]
  [Module.Finite O X] {m : ℕ}

omit [Module.Finite O X] in

/- English proof (translation)
Use extensionality with `x y`. Establish `h1` using `LinearMap.congr_fun₂ h x y`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h1`. Conclude with `mul_left_cancel₀ hk h1`.
-/
theorem smul_cancel {β β' : LinearMap.BilinForm ℤ X} {k : ℤ} (hk : k ≠ 0) (h : k • β = k • β') : β = β' := by
  ext x y
  have h1 := LinearMap.congr_fun₂ h x y
  simp only [LinearMap.smul_apply, smul_eq_mul] at h1
  exact mul_left_cancel₀ hk h1

omit [Module.Finite O X] in

/- English proof (translation)
Introduce `k β' hk`. Establish `h1 : (k : ℤ) • β' = v i` using `by rw [natCast_zsmul]; exact hk.symm`. Break down `Int.isUnit_iff.mp (h.isUnit_of_smul h1) with h2 | h2` into its components or cases. Conclude with `h2` after adjusting the coercions. Use linear arithmetic over natural numbers and integers.
-/
theorem isPrim_of_isPartOfBasis {v : Fin m → balForms bar X} (h : IsPartOfBasis v) (i : Fin m) : IsPrim bar (v i) := by
  intro k β' hk
  have h1 : (k : ℤ) • β' = v i := by rw [natCast_zsmul]; exact hk.symm
  rcases Int.isUnit_iff.mp (h.isUnit_of_smul h1) with h2 | h2
  · exact_mod_cast h2
  · omega

omit [Module.Finite O X] in

/- English proof (translation)
Establish `hg : 0 < Nat.gcd k n` using `Nat.gcd_pos_of_pos_left _ hk`. Establish `hc : Nat.Coprime (k / Nat.gcd k n) (n / Nat.gcd k n)` using `Nat.coprime_div_gcd_div_gcd hg`. Use `set k' := k / Nat.gcd k n with hk'`. Use `set n' := n / Nat.gcd k n with hn'`. Establish `hk1 : k = k' * Nat.gcd k n` using `(Nat.div_mul_cancel (Nat.gcd_dvd_left k n)).symm`.

Establish `hn1 : n = n' * Nat.gcd k n` using `(Nat.div_mul_cancel (Nat.gcd_dvd_right k n)).symm`. Establish `hkn : (k' : ℤ) • x = (n' : ℤ) • y`. Establish `e : ((Nat.gcd k n : ℕ) : ℤ) • ((k' : ℤ) • x) = ((Nat.gcd k n : ℕ) : ℤ) • ((n' : ℤ) • y)`. Rewrite using `[smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm (Nat.gcd k n) k', mul_comm (Nat.gcd k n) n', ← hk1, ← hn1]`. Conclude with `h`.

Conclude with `smul_cancel (by exact_mod_cast hg.ne') e`. Take `⟨s, t, hst⟩` from `Nat.isCoprime_iff_coprime.mpr hc`. Establish `hz : s • y + t • x ∈ balForms bar X` using `Submodule.add_mem _ (Submodule.smul_mem _ s hy) (Submodule.smul_mem _ t hx)`. Establish `hyz : (k' : ℤ) • (s • y + t • x) = y`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[smul_add, smul_smul, smul_smul, smul_smul, mul_comm t]`. Use `_ = ((k' : ℤ) * s) • y + t • ((n' : ℤ) • y) := by rw [hkn]`. Use `_ = (s * k' + t * n' : ℤ) • y := by rw [smul_smul, ← add_smul, mul_comm (k' : ℤ) s]`. Use `_ = y := by rw [hst, one_smul]`. Establish `hxz : (n' : ℤ) • (s • y + t • x) = x`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_add, smul_smul, smul_smul, smul_smul, mul_comm s]`. Use `_ = s • ((k' : ℤ) • x) + ((n' : ℤ) * t) • x := by rw [← hkn]`. Use `_ = (s * k' + t * n' : ℤ) • x := by rw [smul_smul, ← add_smul, mul_comm (n' : ℤ) t]`. Use `_ = x := by rw [hst, one_smul]`.

Establish `ek : k' = 1`. Use `py k' ⟨_, hz⟩ (Subtype.ext ?_)` and prove the remaining obligations. Rewrite `hyz` using `[natCast_zsmul]`. Simplify using `using hyz.symm`. Establish `en : n' = 1`.

Use `px n' ⟨_, hz⟩ (Subtype.ext ?_)` and prove the remaining obligations. Rewrite `hxz` using `[natCast_zsmul]`. Simplify using `using hxz.symm`. Rewrite `hyz` using `[ek, Nat.cast_one, one_smul]`. Rewrite `hxz` using `[en, Nat.cast_one, one_smul]`.

Rewrite using `[← hxz, hyz]`.
-/
theorem eq_of_isPrim {x y : LinearMap.BilinForm ℤ X} (hx : x ∈ balForms bar X) (hy : y ∈ balForms bar X)
    (px : IsPrim bar ⟨x, hx⟩) (py : IsPrim bar ⟨y, hy⟩) {k n : ℕ} (hk : 0 < k) (hn : 0 < n)
    (h : (k : ℤ) • x = (n : ℤ) • y) : x = y := by
  have hg : 0 < Nat.gcd k n := Nat.gcd_pos_of_pos_left _ hk
  have hc : Nat.Coprime (k / Nat.gcd k n) (n / Nat.gcd k n) := Nat.coprime_div_gcd_div_gcd hg
  set k' := k / Nat.gcd k n with hk'
  set n' := n / Nat.gcd k n with hn'
  have hk1 : k = k' * Nat.gcd k n := (Nat.div_mul_cancel (Nat.gcd_dvd_left k n)).symm
  have hn1 : n = n' * Nat.gcd k n := (Nat.div_mul_cancel (Nat.gcd_dvd_right k n)).symm
  have hkn : (k' : ℤ) • x = (n' : ℤ) • y := by
    have e : ((Nat.gcd k n : ℕ) : ℤ) • ((k' : ℤ) • x) = ((Nat.gcd k n : ℕ) : ℤ) • ((n' : ℤ) • y) := by
      rw [smul_smul, smul_smul, ← Nat.cast_mul, ← Nat.cast_mul, mul_comm (Nat.gcd k n) k',
        mul_comm (Nat.gcd k n) n', ← hk1, ← hn1]
      exact h
    exact smul_cancel (by exact_mod_cast hg.ne') e
  obtain ⟨s, t, hst⟩ := Nat.isCoprime_iff_coprime.mpr hc
  have hz : s • y + t • x ∈ balForms bar X :=
    Submodule.add_mem _ (Submodule.smul_mem _ s hy) (Submodule.smul_mem _ t hx)
  have hyz : (k' : ℤ) • (s • y + t • x) = y := by
    calc (k' : ℤ) • (s • y + t • x) = ((k' : ℤ) * s) • y + t • ((k' : ℤ) • x) := by
          rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm t]
      _ = ((k' : ℤ) * s) • y + t • ((n' : ℤ) • y) := by rw [hkn]
      _ = (s * k' + t * n' : ℤ) • y := by rw [smul_smul, ← add_smul, mul_comm (k' : ℤ) s]
      _ = y := by rw [hst, one_smul]
  have hxz : (n' : ℤ) • (s • y + t • x) = x := by
    calc (n' : ℤ) • (s • y + t • x) = s • ((n' : ℤ) • y) + ((n' : ℤ) * t) • x := by
          rw [smul_add, smul_smul, smul_smul, smul_smul, mul_comm s]
      _ = s • ((k' : ℤ) • x) + ((n' : ℤ) * t) • x := by rw [← hkn]
      _ = (s * k' + t * n' : ℤ) • x := by rw [smul_smul, ← add_smul, mul_comm (n' : ℤ) t]
      _ = x := by rw [hst, one_smul]
  have ek : k' = 1 := by
    refine py k' ⟨_, hz⟩ (Subtype.ext ?_)
    rw [natCast_zsmul] at hyz
    simpa using hyz.symm
  have en : n' = 1 := by
    refine px n' ⟨_, hz⟩ (Subtype.ext ?_)
    rw [natCast_zsmul] at hxz
    simpa using hxz.symm
  rw [ek, Nat.cast_one, one_smul] at hyz
  rw [en, Nat.cast_one, one_smul] at hxz
  rw [← hxz, hyz]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, b, hab⟩ : ∃ a b, β a b ≠ 0 := by`. Assume the negation of the conclusion as `hc`. Use `push_neg at hc`. Conclude with `h0 (by ext a b; simpa using hc a b)`. Establish `bound : ∀ (n : ℕ) (u : LinearMap.BilinForm ℤ X), β = (n : ℤ) • u → n ≤ (β a b).natAbs`.

Introduce `n u hn`. Establish `e : β a b = n * u a b` using `by rw [hn]; simp`. Establish `hu0 : u a b ≠ 0` using `by intro h'; apply hab; rw [e, h', mul_zero]`. Rewrite using `[e, Int.natAbs_mul, Int.natAbs_natCast]`. Conclude with `Nat.le_mul_of_pos_right n (Int.natAbs_pos.mpr hu0)`.

Establish `P1 : (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u) 1` using `⟨one_pos, β, hβ, by simp⟩`. Establish `hM : 1 ≤ (β a b).natAbs` using `Int.natAbs_pos.mpr hab`. Take `⟨hNpos, u, hu, hβu⟩` from `Nat.findGreatest_spec (P := (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u)) hM P1`. Use `⟨_, u, hu, hNpos, hβu, ?_⟩` and prove the remaining obligations. Introduce `k β' hk`.

Establish `hk' : u = (k : ℤ) • (β' : LinearMap.BilinForm ℤ X)`. Use `congrArg Subtype.val hk` as an intermediate fact. Simplify using `using this`. Break down `Nat.eq_zero_or_pos k with h0k | h0k` into its components or cases. It suffices to derive a contradiction.

Apply `h0` to reduce the goal to its premises. Rewrite using `[hβu, hk', h0k]`. Simplify using the standard rewrite rules. Establish `hP : (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u) (Nat.findGreatest (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u) (β a b).natAbs * k)` using `⟨Nat.mul_pos hNpos h0k, β', β'.2, hβu.trans (by rw [hk', smul_smul, Nat.cast_mul])⟩`. Establish `hle` using `Nat.le_findGreatest (P := (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u)) (bound _ _ hP.2.choose_spec.2) hP`.

Establish `: k ≤ 1` using `Nat.le_of_mul_le_mul_left (by simpa using hle) hNpos`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_prim [Module.Finite ℤ O] {β : LinearMap.BilinForm ℤ X} (hβ : β ∈ balForms bar X) (h0 : β ≠ 0) :
    ∃ (n : ℕ) (u : LinearMap.BilinForm ℤ X) (hu : u ∈ balForms bar X), 0 < n ∧ β = (n : ℤ) • u ∧ IsPrim bar ⟨u, hu⟩ := by
  classical
  obtain ⟨a, b, hab⟩ : ∃ a b, β a b ≠ 0 := by
    by_contra hc
    push_neg at hc
    exact h0 (by ext a b; simpa using hc a b)
  have bound : ∀ (n : ℕ) (u : LinearMap.BilinForm ℤ X), β = (n : ℤ) • u → n ≤ (β a b).natAbs := by
    intro n u hn
    have e : β a b = n * u a b := by rw [hn]; simp
    have hu0 : u a b ≠ 0 := by intro h'; apply hab; rw [e, h', mul_zero]
    rw [e, Int.natAbs_mul, Int.natAbs_natCast]
    exact Nat.le_mul_of_pos_right n (Int.natAbs_pos.mpr hu0)
  have P1 : (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u) 1 := ⟨one_pos, β, hβ, by simp⟩
  have hM : 1 ≤ (β a b).natAbs := Int.natAbs_pos.mpr hab
  obtain ⟨hNpos, u, hu, hβu⟩ := Nat.findGreatest_spec (P := (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u)) hM P1
  refine ⟨_, u, hu, hNpos, hβu, ?_⟩
  intro k β' hk
  have hk' : u = (k : ℤ) • (β' : LinearMap.BilinForm ℤ X) := by
    have := congrArg Subtype.val hk
    simpa using this
  rcases Nat.eq_zero_or_pos k with h0k | h0k
  · exfalso; apply h0; rw [hβu, hk', h0k]; simp
  · have hP : (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u)
        (Nat.findGreatest (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u) (β a b).natAbs * k) :=
      ⟨Nat.mul_pos hNpos h0k, β', β'.2, hβu.trans (by rw [hk', smul_smul, Nat.cast_mul])⟩
    have hle := Nat.le_findGreatest (P := (fun n : ℕ => 0 < n ∧ ∃ u, u ∈ balForms bar X ∧ β = (n : ℤ) • u)) (bound _ _ hP.2.choose_spec.2) hP
    have : k ≤ 1 := Nat.le_of_mul_le_mul_left (by simpa using hle) hNpos
    omega

/- English proof (translation)
Establish `hnj : (n j : ℝ) ≠ 0` using `by exact_mod_cast (hn j).ne'`. Apply the tactic sequence `have key : φ.eval X (fun a b => ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * (δ l a b : ℝ)) = ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * φ.evalZ (δ l) := h (Pi.single j (1 / (n j : ℝ))) (fun l => by rw [Pi.single_apply]; split_ifs <;> positivity)`. Establish `hf : (fun a b => ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * (δ l a b : ℝ)) = fun a b => (u j a b : ℝ)`. Use function extensionality and compare the values at `a b`. Rewrite using `[Finset.sum_eq_single j]`.

Rewrite using `[Pi.single_eq_same, hu j]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]`. Clear the denominators using the available nonvanishing facts. Introduce `l _ hl`. Rewrite using `[Pi.single_eq_of_ne hl, zero_mul]`.

Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`. Establish `hr : ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * φ.evalZ (δ l) = 1 / n j * φ.evalZ (δ j)`. Rewrite using `[Finset.sum_eq_single j]`. Rewrite using `[Pi.single_eq_same]`.

Introduce `l _ hl`. Rewrite using `[Pi.single_eq_of_ne hl, zero_mul]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`. Rewrite `key` using `[hf, hr]`.

Establish `e : φ.evalZ (u j) = 1 / n j * φ.evalZ (δ j)` using `key`. Rewrite using `[e]`. Clear the denominators using the available nonvanishing facts.
-/
private lemma evalZ_eq_mul_evalZ_of_eq_nsmul {δ u : Fin m → LinearMap.BilinForm ℤ X} (h : φ.LinearOn δ) (n : Fin m → ℕ)
    (hn : ∀ i, 0 < n i) (hu : ∀ i, δ i = (n i : ℤ) • u i) (j : Fin m) : φ.evalZ (δ j) = n j * φ.evalZ (u j) := by
  have hnj : (n j : ℝ) ≠ 0 := by exact_mod_cast (hn j).ne'
  have key : φ.eval X (fun a b => ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * (δ l a b : ℝ)) =
      ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * φ.evalZ (δ l) :=
    h (Pi.single j (1 / (n j : ℝ))) (fun l => by rw [Pi.single_apply]; split_ifs <;> positivity)
  have hf : (fun a b => ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * (δ l a b : ℝ)) = fun a b => (u j a b : ℝ) := by
    funext a b
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same, hu j]
      simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      field_simp
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hr : ∑ l, (Pi.single j (1 / (n j : ℝ)) : Fin m → ℝ) l * φ.evalZ (δ l) = 1 / n j * φ.evalZ (δ j) := by
    rw [Finset.sum_eq_single j]
    · rw [Pi.single_eq_same]
    · intro l _ hl
      rw [Pi.single_eq_of_ne hl, zero_mul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  rw [hf, hr] at key
  have e : φ.evalZ (u j) = 1 / n j * φ.evalZ (δ j) := key
  rw [e]
  field_simp

/- English proof (translation)
Use `⟨hmem, fun i y => ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `h1` using `h.nonneg i y`. Rewrite `h1` using `[hu i]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul] at h1`. Establish `hn' : (0 : ℤ) < n i` using `by exact_mod_cast hn i`.

Use the polynomial consequences of the given equalities and inequalities. Introduce `c hc`. Establish `key : φ.eval X (fun a b => ∑ i, c i / n i * (δ i a b : ℝ)) = ∑ i, c i / n i * φ.evalZ (δ i)` using `h.linear _ (fun i => div_nonneg (hc i) (Nat.cast_nonneg _))`. Establish `hf : (fun a b => ∑ i, c i / n i * (δ i a b : ℝ)) = fun a b => ∑ i, c i * (u i a b : ℝ)`. Use function extensionality and compare the values at `a b`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hni : (n i : ℝ) ≠ 0` using `by exact_mod_cast (hn i).ne'`. Rewrite using `[hu i]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]`. Clear the denominators using the available nonvanishing facts.

Rewrite `key` using `[hf]`. Rewrite using `[key]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `hni : (n i : ℝ) ≠ 0` using `by exact_mod_cast (hn i).ne'`. Rewrite using `[evalZ_eq_mul_evalZ_of_eq_nsmul h.linear n hn hu i]`.

Clear the denominators using the available nonvanishing facts. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `h.strict`. Use `⟨N, ℓ, hN, fun i => ?_, h2, ?_⟩` and prove the remaining obligations. Establish `hni : (n i : ℝ) ≠ 0` using `by exact_mod_cast (hn i).ne'`. Establish `e1` using `h1 i`.

Rewrite `e1` using `[evalZ_eq_mul_evalZ_of_eq_nsmul h.linear n hn hu i, hu i, map_smul, smul_eq_mul]`. Move the coercions through the operations in `at e1`. Apply `mul_left_cancel₀ hni` to reduce the goal to its premises. Rewrite using `[e1]`. Expand and normalize the polynomial expressions, which then agree.

Introduce `β hβ hp he`. Take `⟨k, c, hk, hkc⟩` from `h3 β hβ hp he`. Use `⟨k, fun i => c i * n i, hk, ?_⟩` and prove the remaining obligations. Rewrite using `[hkc]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Rewrite using `[hu i, natCast_zsmul, mul_smul]`.
-/
theorem cell_rescale {δ u : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ δ) (n : Fin m → ℕ) (hn : ∀ i, 0 < n i)
    (hu : ∀ i, δ i = (n i : ℤ) • u i) (hmem : ∀ i, u i ∈ balForms bar X) : IsCell bar φ u := by
  refine ⟨hmem, fun i y => ?_, ?_, ?_⟩
  · have h1 := h.nonneg i y
    rw [hu i] at h1
    simp only [LinearMap.smul_apply, smul_eq_mul] at h1
    have hn' : (0 : ℤ) < n i := by exact_mod_cast hn i
    nlinarith
  · intro c hc
    have key : φ.eval X (fun a b => ∑ i, c i / n i * (δ i a b : ℝ)) = ∑ i, c i / n i * φ.evalZ (δ i) :=
      h.linear _ (fun i => div_nonneg (hc i) (Nat.cast_nonneg _))
    have hf : (fun a b => ∑ i, c i / n i * (δ i a b : ℝ)) = fun a b => ∑ i, c i * (u i a b : ℝ) := by
      funext a b
      refine Finset.sum_congr rfl fun i _ => ?_
      have hni : (n i : ℝ) ≠ 0 := by exact_mod_cast (hn i).ne'
      rw [hu i]
      simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      field_simp
    rw [hf] at key
    rw [key]
    refine Finset.sum_congr rfl fun i _ => ?_
    have hni : (n i : ℝ) ≠ 0 := by exact_mod_cast (hn i).ne'
    rw [evalZ_eq_mul_evalZ_of_eq_nsmul h.linear n hn hu i]
    field_simp
  · obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := h.strict
    refine ⟨N, ℓ, hN, fun i => ?_, h2, ?_⟩
    · have hni : (n i : ℝ) ≠ 0 := by exact_mod_cast (hn i).ne'
      have e1 := h1 i
      rw [evalZ_eq_mul_evalZ_of_eq_nsmul h.linear n hn hu i, hu i, map_smul, smul_eq_mul] at e1
      push_cast at e1
      apply mul_left_cancel₀ hni
      rw [e1]
      ring
    · intro β hβ hp he
      obtain ⟨k, c, hk, hkc⟩ := h3 β hβ hp he
      refine ⟨k, fun i => c i * n i, hk, ?_⟩
      rw [hkc]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [hu i, natCast_zsmul, mul_smul]

/- English proof (translation)
Rewrite `h`, the goal using `[Fintype.linearIndependent_iff]`. Introduce `g hg i`. Establish `hprod : ∀ j, (g j * ∏ l ∈ Finset.univ.erase j, (n l : ℤ)) • δ j = (∏ l, (n l : ℤ)) • (g j • u j)`. Introduce `j`. Rewrite using `[hu j, smul_smul, smul_smul, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_comm (g j)]`.

Establish `key` using `h (fun j => g j * ∏ l ∈ Finset.univ.erase j, (n l : ℤ)) (by`. Simplify using `only [hprod, ← Finset.smul_sum, hg, smul_zero]) i`. Establish `hp : ∏ l ∈ Finset.univ.erase i, (n l : ℤ) ≠ 0` using `Finset.prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (hn l).ne'`. Conclude with `(mul_eq_zero.mp key).resolve_right hp`.
-/
theorem linearIndependent_of_smul {δ u : Fin m → LinearMap.BilinForm ℤ X} (h : LinearIndependent ℤ δ) (n : Fin m → ℕ)
    (hn : ∀ i, 0 < n i) (hu : ∀ i, δ i = (n i : ℤ) • u i) : LinearIndependent ℤ u := by
  rw [Fintype.linearIndependent_iff] at h ⊢
  intro g hg i
  have hprod : ∀ j, (g j * ∏ l ∈ Finset.univ.erase j, (n l : ℤ)) • δ j = (∏ l, (n l : ℤ)) • (g j • u j) := by
    intro j
    rw [hu j, smul_smul, smul_smul, mul_assoc, Finset.prod_erase_mul _ _ (Finset.mem_univ j), mul_comm (g j)]
  have key := h (fun j => g j * ∏ l ∈ Finset.univ.erase j, (n l : ℤ)) (by
    simp only [hprod, ← Finset.smul_sum, hg, smul_zero]) i
  have hp : ∏ l ∈ Finset.univ.erase i, (n l : ℤ) ≠ 0 :=
    Finset.prod_ne_zero_iff.mpr fun l _ => by exact_mod_cast (hn l).ne'
  exact (mul_eq_zero.mp key).resolve_right hp

end Gen

end GlobalTheory.PolFan.SmoothEnd

namespace GlobalTheory.PolFan.SmoothEnd

/- English proof (translation)
Introduce `O _ bar φ X _ _ _ m m' γ γ' hγ hγ' c hc hsum j`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hγ'.strict`. Establish `lin1 : φ.eval X (fun a b => ∑ j, (1 : ℝ) * (γ j a b : ℝ)) = ∑ j, (1 : ℝ) * φ.evalZ (γ j)` using `hγ.linear _ (fun _ => zero_le_one)`. Establish `lin2 : φ.eval X (fun a b => ∑ i, c i * (γ' i a b : ℝ)) = ∑ i, c i * φ.evalZ (γ' i)` using `hγ'.linear c hc`. Establish `hfun : (fun a b => ∑ j, (1 : ℝ) * (γ j a b : ℝ)) = fun a b => ∑ i, c i * (γ' i a b : ℝ)`.

Use function extensionality and compare the values at `a b`. Use `LinearMap.congr_fun₂ hsum a b` as an intermediate fact. Simplify using `only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this`. Simplify using `using this`. Establish `eqφ : ∑ j, φ.evalZ (γ j) = ∑ i, c i * φ.evalZ (γ' i)`.

Use `lin1.symm.trans ((congrArg (φ.eval X) hfun).trans lin2)` as an intermediate fact. Simplify using `using this`. Establish `hℓ` using `sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) (fun _ _ h => h) ℓ (u := γ) (w := γ') (a := fun _ => (1 : ℝ)) (b := c) (by simpa using hsum)`. Simplify using `only [one_mul] at hℓ`. Establish `hsum0 : ∑ j, ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0`.

Rewrite using `[Finset.sum_sub_distrib, ← Finset.mul_sum, eqφ, hℓ, Finset.mul_sum, ← Finset.sum_sub_distrib]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Rewrite using `[h1 i]`. Expand and normalize the polynomial expressions, which then agree. Establish `hnn : ∀ j ∈ Finset.univ, 0 ≤ ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j))` using `fun j _ => sub_nonneg.mpr (h2 _ (hγ.mem j) (hγ.nonneg j))`.

Establish `hj0` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j (Finset.mem_univ j)`. Take `⟨k, c', hk, hkc⟩` from `h3 (γ j) (hγ.mem j) (hγ.nonneg j) (by linarith)`. Use `⟨fun i => (c' i : ℝ) / k, fun i => by positivity, ?_⟩` and prove the remaining obligations. Establish `hk' : (k : ℝ) ≠ 0` using `by exact_mod_cast hk.ne'`. Use extensionality with `a b`.

Establish `h4` using `congrArg (fun f : LinearMap.BilinForm ℤ X => ((f a b : ℤ) : ℝ)) hkc`. Simplify using `only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, nsmul_eq_mul, smul_eq_mul, Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h4`. Simplify using `only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]`. Establish `h5 : ∑ x, (c' x : ℝ) / k * (γ' x a b : ℝ) = 1 / k * ∑ x, (c' x : ℝ) * (γ' x a b : ℝ)`. Rewrite using `[Finset.mul_sum]`.

Conclude with `Finset.sum_congr rfl fun x _ => by ring`. Rewrite using `[h5, ← h4]`. Clear the denominators using the available nonvanishing facts.
-/
theorem mem_cone_of_sum : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X), IsCell bar φ γ → IsCell bar φ γ' → ∀ (c : Fin m' → ℝ), (∀ i, 0 ≤ c i) → ∑ j, toReal (γ j) = ∑ i, c i • toReal (γ' i) → ∀ j, ∃ a : Fin m' → ℝ, (∀ i, 0 ≤ a i) ∧ toReal (γ j) = ∑ i, a i • toReal (γ' i) := by
  intro O _ bar φ X _ _ _ m m' γ γ' hγ hγ' c hc hsum j
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ'.strict
  have lin1 : φ.eval X (fun a b => ∑ j, (1 : ℝ) * (γ j a b : ℝ)) = ∑ j, (1 : ℝ) * φ.evalZ (γ j) :=
    hγ.linear _ (fun _ => zero_le_one)
  have lin2 : φ.eval X (fun a b => ∑ i, c i * (γ' i a b : ℝ)) = ∑ i, c i * φ.evalZ (γ' i) := hγ'.linear c hc
  have hfun : (fun a b => ∑ j, (1 : ℝ) * (γ j a b : ℝ)) = fun a b => ∑ i, c i * (γ' i a b : ℝ) := by
    funext a b
    have := LinearMap.congr_fun₂ hsum a b
    simp only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    simpa using this
  have eqφ : ∑ j, φ.evalZ (γ j) = ∑ i, c i * φ.evalZ (γ' i) := by
    have := lin1.symm.trans ((congrArg (φ.eval X) hfun).trans lin2)
    simpa using this
  have hℓ := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) (fun _ _ h => h) ℓ (u := γ) (w := γ')
    (a := fun _ => (1 : ℝ)) (b := c) (by simpa using hsum)
  simp only [one_mul] at hℓ
  have hsum0 : ∑ j, ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) = 0 := by
    rw [Finset.sum_sub_distrib, ← Finset.mul_sum, eqφ, hℓ, Finset.mul_sum, ← Finset.sum_sub_distrib]
    refine Finset.sum_eq_zero fun i _ => ?_
    rw [h1 i]
    ring
  have hnn : ∀ j ∈ Finset.univ, 0 ≤ ((ℓ (γ j) : ℝ) - N * φ.evalZ (γ j)) :=
    fun j _ => sub_nonneg.mpr (h2 _ (hγ.mem j) (hγ.nonneg j))
  have hj0 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp hsum0 j (Finset.mem_univ j)
  obtain ⟨k, c', hk, hkc⟩ := h3 (γ j) (hγ.mem j) (hγ.nonneg j) (by linarith)
  refine ⟨fun i => (c' i : ℝ) / k, fun i => by positivity, ?_⟩
  have hk' : (k : ℝ) ≠ 0 := by exact_mod_cast hk.ne'
  ext a b
  have h4 := congrArg (fun f : LinearMap.BilinForm ℤ X => ((f a b : ℤ) : ℝ)) hkc
  simp only [LinearMap.smul_apply, LinearMap.sum_apply, Finset.sum_apply, nsmul_eq_mul, smul_eq_mul,
    Int.cast_sum, Int.cast_mul, Int.cast_natCast] at h4
  simp only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul]
  have h5 : ∑ x, (c' x : ℝ) / k * (γ' x a b : ℝ) = 1 / k * ∑ x, (c' x : ℝ) * (γ' x a b : ℝ) := by
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun x _ => by ring
  rw [h5, ← h4]
  field_simp

end GlobalTheory.PolFan.SmoothEnd

namespace GlobalTheory.PolFan.SmoothEnd

/- English proof (translation)
Introduce `L _ _ _ m v hv hT`. Use `haveI : _root_.Finite (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range v))) := Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion`. Use `haveI : Subsingleton (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range v))) := Finite.card_le_one_iff_subsingleton.mp hT`. Use `haveI : Module.IsTorsionFree ℤ (L ⧸ Submodule.span ℤ (Set.range v)) := Submodule.isTorsionFree_iff_torsion_eq_bot.mpr Submodule.eq_bot_of_subsingleton`. Use `set bQ := Module.finBasis ℤ (L ⧸ Submodule.span ℤ (Set.range v)) with hbQ`.

Take `⟨s, hs⟩ : ∃ s : Fin (Module.finrank ℤ (L ⧸ Submodule.span ℤ (Set.range v))) → L, ∀ k, Submodule.Quotient.mk (s k) = bQ k` from `⟨fun k => (Submodule.Quotient.mk_surjective _ (bQ k)).choose, fun k => (Submodule.Quotient.mk_surjective _ (bQ k)).choose_spec⟩`. Establish `hf : LinearIndependent ℤ (fun i => (⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)))` using `LinearIndependent.of_comp (Submodule.span ℤ (Set.range v)).subtype hv`. Establish `hg : LinearIndependent ℤ (Submodule.Quotient.mk (p` using `Submodule.span ℤ (Set.range v)) ∘ s) := by`. Establish `e : (Submodule.Quotient.mk (p` using `Submodule.span ℤ (Set.range v)) ∘ s) = ⇑bQ := funext hs`. Rewrite using `[e]`.

Conclude with `bQ.linearIndependent`. Establish `hli` using `LinearIndependent.sumElim_of_quotient hf s hg`. Establish `hsp : ⊤ ≤ Submodule.span ℤ (Set.range (Sum.elim (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s))`. Introduce `x _`. Establish `hx` using `bQ.sum_repr (Submodule.Quotient.mk x)`.

Establish `hmem : x - ∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k ∈ Submodule.span ℤ (Set.range v)`. Rewrite using `[← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]`. Establish `e : (Submodule.Quotient.mk (∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k) : L ⧸ Submodule.span ℤ (Set.range v)) = ∑ k, bQ.repr (Submodule.Quotient.mk x) k • bQ k`. Express the relevant statement in the definitionally equal form `(Submodule.span ℤ (Set.range v)).mkQ (∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k) = _`. Rewrite using `[map_sum]`.

Simplify using `only [map_smul, Submodule.mkQ_apply, hs]`. Rewrite using `[e, hx, sub_self]`. Establish `h1 : Submodule.span ℤ (Set.range v) ≤ Submodule.span ℤ (Set.range (Sum.elim (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s))` using `Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)`. Establish `h2 : ∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k ∈ Submodule.span ℤ (Set.range (Sum.elim (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s))` using `Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)`. Establish `h3` using `Submodule.add_mem _ (h1 hmem) h2`.

Rewrite `h3` using `[sub_add_cancel]`. Then use the resulting hypothesis. Conclude with `⟨_, Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]; rfl⟩`.
-/
theorem isPartOfBasis_of_card_torsion_le_one : ∀ (L : Type) [AddCommGroup L] [Module.Free ℤ L] [Module.Finite ℤ L] (m : ℕ) (v : Fin m → L), LinearIndependent ℤ v → Nat.card (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range v))) ≤ 1 → IsPartOfBasis v := by
  intro L _ _ _ m v hv hT
  haveI : _root_.Finite (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range v))) :=
    Module.finite_of_fg_torsion _ Submodule.torsion_isTorsion
  haveI : Subsingleton (Submodule.torsion ℤ (L ⧸ Submodule.span ℤ (Set.range v))) :=
    Finite.card_le_one_iff_subsingleton.mp hT
  haveI : Module.IsTorsionFree ℤ (L ⧸ Submodule.span ℤ (Set.range v)) :=
    Submodule.isTorsionFree_iff_torsion_eq_bot.mpr Submodule.eq_bot_of_subsingleton
  set bQ := Module.finBasis ℤ (L ⧸ Submodule.span ℤ (Set.range v)) with hbQ
  obtain ⟨s, hs⟩ : ∃ s : Fin (Module.finrank ℤ (L ⧸ Submodule.span ℤ (Set.range v))) → L,
      ∀ k, Submodule.Quotient.mk (s k) = bQ k :=
    ⟨fun k => (Submodule.Quotient.mk_surjective _ (bQ k)).choose,
      fun k => (Submodule.Quotient.mk_surjective _ (bQ k)).choose_spec⟩
  have hf : LinearIndependent ℤ
      (fun i => (⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v))) :=
    LinearIndependent.of_comp (Submodule.span ℤ (Set.range v)).subtype hv
  have hg : LinearIndependent ℤ (Submodule.Quotient.mk (p := Submodule.span ℤ (Set.range v)) ∘ s) := by
    have e : (Submodule.Quotient.mk (p := Submodule.span ℤ (Set.range v)) ∘ s) = ⇑bQ := funext hs
    rw [e]
    exact bQ.linearIndependent
  have hli := LinearIndependent.sumElim_of_quotient hf s hg
  have hsp : ⊤ ≤ Submodule.span ℤ (Set.range (Sum.elim
      (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s)) := by
    intro x _
    have hx := bQ.sum_repr (Submodule.Quotient.mk x)
    have hmem : x - ∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k ∈ Submodule.span ℤ (Set.range v) := by
      rw [← Submodule.Quotient.mk_eq_zero, Submodule.Quotient.mk_sub]
      have e : (Submodule.Quotient.mk (∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k) :
          L ⧸ Submodule.span ℤ (Set.range v)) = ∑ k, bQ.repr (Submodule.Quotient.mk x) k • bQ k := by
        change (Submodule.span ℤ (Set.range v)).mkQ (∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k) = _
        rw [map_sum]
        simp only [map_smul, Submodule.mkQ_apply, hs]
      rw [e, hx, sub_self]
    have h1 : Submodule.span ℤ (Set.range v) ≤ Submodule.span ℤ (Set.range (Sum.elim
        (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s)) :=
      Submodule.span_mono (by rintro _ ⟨i, rfl⟩; exact ⟨Sum.inl i, rfl⟩)
    have h2 : ∑ k, bQ.repr (Submodule.Quotient.mk x) k • s k ∈ Submodule.span ℤ (Set.range (Sum.elim
        (fun i => ((⟨v i, Submodule.subset_span ⟨i, rfl⟩⟩ : Submodule.span ℤ (Set.range v)) : L)) s)) :=
      Submodule.sum_mem _ fun k _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨Sum.inr k, rfl⟩)
    have h3 := Submodule.add_mem _ (h1 hmem) h2
    rwa [sub_add_cancel] at h3
  exact ⟨_, Module.Basis.mk hli hsp, fun i => by rw [Module.Basis.mk_apply]; rfl⟩

end GlobalTheory.PolFan.SmoothEnd

namespace GlobalTheory.PolFan.SmoothEnd

/- English proof (translation)
Introduce `O _ bar φ X _ _ _ m m' γ γ' hγ hγ' a ha hsum j`. Take `⟨N, ℓ, hN, h1, h2, h3⟩` from `hγ.strict`. Establish `hfun : (fun x y => ∑ i, a j i * (γ' i x y : ℝ)) = fun x y => (γ j x y : ℝ)`. Use function extensionality and compare the values at `x y`. Use `LinearMap.congr_fun₂ (hsum j) x y` as an intermediate fact.

Simplify using `only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this`. Conclude with `this.symm`. Establish `hev : φ.evalZ (γ j) = ∑ i, a j i * φ.evalZ (γ' i)`. Use `hγ'.linear (a j) (ha j)` as an intermediate fact. Rewrite `this` using `[hfun]`.

Conclude with `this`. Establish `hℓ : (ℓ (γ j) : ℝ) = ∑ i, a j i * (ℓ (γ' i) : ℝ)`. Use `sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) (fun _ _ h => h) ℓ (u := fun _ : Unit => γ j) (w := γ') (a := fun _ => (1 : ℝ)) (b := a j) (by simpa using hsum j)` as an intermediate fact. Simplify using `using this`. Establish `hterm : ∀ i ∈ Finset.univ, 0 ≤ a j i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i))` using `fun i _ => mul_nonneg (ha j i) (sub_nonneg.mpr (h2 _ (hγ'.mem i) (hγ'.nonneg i)))`.

Establish `hzero : ∑ i, a j i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0`. Simplify using `only [mul_sub, Finset.sum_sub_distrib]`. Rewrite using `[← hℓ, h1 j, hev, Finset.mul_sum]`. Conclude with `sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => by ring)`. Establish `hface : ∀ i, a j i ≠ 0 → ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • γ' i = ∑ l, c l • γ l`.

Introduce `i hai`. Establish `e0` using `(Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)`. Establish `e1 : (ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i) = 0` using `(mul_eq_zero.mp e0).resolve_left hai`. Conclude with `h3 _ (hγ'.mem i) (hγ'.nonneg i) (by linarith)`. Establish `hγj : γ j ≠ 0` using `hγ.linearIndependent.ne_zero j`.

Choose the witnesses or unpack the hypotheses as in `⟨i, hai, hγi⟩ : ∃ i, a j i ≠ 0 ∧ γ' i ≠ 0 := by`. Assume the negation of the conclusion as `hne`. Use `push_neg at hne`. Apply `hγj` to reduce the goal to its premises. Apply `toReal_injective` to reduce the goal to its premises.

Rewrite using `[hsum j]`. Use extensionality with `x y`. Simplify using `only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, LinearMap.zero_apply, Int.cast_zero]`. Use `Finset.sum_eq_zero fun i _ => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : a j i = 0`.

Simplify using `[h0]`. Simplify using `[hne i h0]`. Take `⟨ψ, hψ⟩` from `hγ.basis.exists_dual`. Establish `hψ' : ∀ l l', ψ l ⟨γ l', hγ.mem l'⟩ = if l = l' then 1 else 0` using `fun l l' => hψ l l'`. Establish `hcoef : ∀ i', ∀ (k : ℕ) (c : Fin m → ℕ), k • γ' i' = ∑ l, c l • γ l → ∀ l, (k : ℤ) * ψ l ⟨γ' i', hγ'.mem i'⟩ = c l`.

Introduce `i' k c hkc l`. Establish `hsub : k • (⟨γ' i', hγ'.mem i'⟩ : balForms bar X) = ∑ l', c l' • (⟨γ l', hγ.mem l'⟩ : balForms bar X)`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `using hkc`. Use `congrArg (ψ l) hsub` as an intermediate fact.

Rewrite `this` using `[map_nsmul, map_sum]`. Simplify using `only [map_nsmul, hψ', nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true] at this`. Conclude with `this`. Establish `hψface : ∀ l i', a j i' ≠ 0 → 0 ≤ ψ l ⟨γ' i', hγ'.mem i'⟩`. Introduce `l i' hai'`.

Take `⟨k, c, hk, hkc⟩` from `hface i' hai'`. Establish `e` using `hcoef i' k c hkc l`. Establish `hk' : (0 : ℤ) < k` using `by exact_mod_cast hk`. Establish `hc' : (0 : ℤ) ≤ c l` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities.

Establish `hψzero : ∀ l, l ≠ j → ψ l ⟨γ' i, hγ'.mem i⟩ = 0`. Introduce `l hl`. Establish `e` using `sum_mul_eq_of_sum_toReal_eq (j := (balForms bar X).subtype) (balForms bar X).injective_subtype (ψ l) (u := fun _ : Unit => (⟨γ j, hγ.mem j⟩ : balForms bar X)) (w := fun i' => (⟨γ' i', hγ'.mem i'⟩ : balForms bar X)) (a := fun _ => (1 : ℝ)) (b := a j) (by simpa using hsum j)`. Establish `e' : ∑ i', a j i' * (ψ l ⟨γ' i', hγ'.mem i'⟩ : ℝ) = 0`. Simplify `e.symm` using `[hψ', hl]`.

Establish `hnn : ∀ i' ∈ Finset.univ, 0 ≤ a j i' * (ψ l ⟨γ' i', hγ'.mem i'⟩ : ℝ)`. Introduce `i' _`. Distinguish the cases in `h0 : a j i' = 0`. Simplify using `[h0]`. Conclude with `mul_nonneg (ha j i') (by exact_mod_cast hψface l i' h0)`.

Establish `e2` using `(Finset.sum_eq_zero_iff_of_nonneg hnn).mp e' i (Finset.mem_univ i)`. Establish `e3` using `(mul_eq_zero.mp e2).resolve_left hai`. Conclude with `e3` after adjusting the coercions. Take `⟨k, c, hk, hkc⟩` from `hface i hai`. Establish `hcl : ∀ l, l ≠ j → c l = 0`.

Introduce `l hl`. Establish `e` using `hcoef i k c hkc l`. Rewrite `e` using `[hψzero l hl, mul_zero]`. Conclude with `e.symm` after adjusting the coercions. Establish `hkc' : (k : ℤ) • γ' i = (c j : ℤ) • γ j`.

Rewrite using `[natCast_zsmul, natCast_zsmul, hkc, Finset.sum_eq_single j]`. Introduce `l _ hl`. Rewrite using `[hcl l hl, zero_smul]`. Introduce `hj`. Conclude with `absurd (Finset.mem_univ j) hj`.

Establish `hcj : 0 < c j`. Break down `Nat.eq_zero_or_pos (c j) with h0 | h0` into its components or cases. It suffices to derive a contradiction. Apply `hγi` to reduce the goal to its premises. Rewrite `hkc'` using `[h0, Nat.cast_zero, zero_smul]`.

Conclude with `smul_cancel (k := (k : ℤ)) (by exact_mod_cast hk.ne') (by rw [hkc', smul_zero])`. Conclude with `h0`. Conclude with `⟨i, k, c j, hk, hcj, hkc'⟩`.
-/
theorem ray_of_mem_cone : ∀ (O : Type) [CommRing O] (bar : O → O) (φ : InvFun O) (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] (m m' : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X) (γ' : Fin m' → LinearMap.BilinForm ℤ X), IsCone bar φ γ → IsCell bar φ γ' → ∀ (a : Fin m → Fin m' → ℝ), (∀ j i, 0 ≤ a j i) → (∀ j, toReal (γ j) = ∑ i, a j i • toReal (γ' i)) → ∀ j, ∃ (i : Fin m') (k n : ℕ), 0 < k ∧ 0 < n ∧ (k : ℤ) • γ' i = (n : ℤ) • γ j := by
  intro O _ bar φ X _ _ _ m m' γ γ' hγ hγ' a ha hsum j
  obtain ⟨N, ℓ, hN, h1, h2, h3⟩ := hγ.strict
  have hfun : (fun x y => ∑ i, a j i * (γ' i x y : ℝ)) = fun x y => (γ j x y : ℝ) := by
    funext x y
    have := LinearMap.congr_fun₂ (hsum j) x y
    simp only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at this
    exact this.symm
  have hev : φ.evalZ (γ j) = ∑ i, a j i * φ.evalZ (γ' i) := by
    have := hγ'.linear (a j) (ha j)
    rw [hfun] at this
    exact this
  have hℓ : (ℓ (γ j) : ℝ) = ∑ i, a j i * (ℓ (γ' i) : ℝ) := by
    have := sum_mul_eq_of_sum_toReal_eq (j := LinearMap.id) (fun _ _ h => h) ℓ (u := fun _ : Unit => γ j)
      (w := γ') (a := fun _ => (1 : ℝ)) (b := a j) (by simpa using hsum j)
    simpa using this
  have hterm : ∀ i ∈ Finset.univ, 0 ≤ a j i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) :=
    fun i _ => mul_nonneg (ha j i) (sub_nonneg.mpr (h2 _ (hγ'.mem i) (hγ'.nonneg i)))
  have hzero : ∑ i, a j i * ((ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i)) = 0 := by
    simp only [mul_sub, Finset.sum_sub_distrib]
    rw [← hℓ, h1 j, hev, Finset.mul_sum]
    exact sub_eq_zero.mpr (Finset.sum_congr rfl fun i _ => by ring)
  have hface : ∀ i, a j i ≠ 0 → ∃ (k : ℕ) (c : Fin m → ℕ), 0 < k ∧ k • γ' i = ∑ l, c l • γ l := by
    intro i hai
    have e0 := (Finset.sum_eq_zero_iff_of_nonneg hterm).mp hzero i (Finset.mem_univ i)
    have e1 : (ℓ (γ' i) : ℝ) - N * φ.evalZ (γ' i) = 0 := (mul_eq_zero.mp e0).resolve_left hai
    exact h3 _ (hγ'.mem i) (hγ'.nonneg i) (by linarith)
  have hγj : γ j ≠ 0 := hγ.linearIndependent.ne_zero j
  obtain ⟨i, hai, hγi⟩ : ∃ i, a j i ≠ 0 ∧ γ' i ≠ 0 := by
    by_contra hne
    push_neg at hne
    apply hγj
    apply toReal_injective
    rw [hsum j]
    ext x y
    simp only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul,
      LinearMap.zero_apply, Int.cast_zero]
    refine Finset.sum_eq_zero fun i _ => ?_
    by_cases h0 : a j i = 0
    · simp [h0]
    · simp [hne i h0]
  obtain ⟨ψ, hψ⟩ := hγ.basis.exists_dual
  have hψ' : ∀ l l', ψ l ⟨γ l', hγ.mem l'⟩ = if l = l' then 1 else 0 := fun l l' => hψ l l'
  have hcoef : ∀ i', ∀ (k : ℕ) (c : Fin m → ℕ), k • γ' i' = ∑ l, c l • γ l →
      ∀ l, (k : ℤ) * ψ l ⟨γ' i', hγ'.mem i'⟩ = c l := by
    intro i' k c hkc l
    have hsub : k • (⟨γ' i', hγ'.mem i'⟩ : balForms bar X) =
        ∑ l', c l' • (⟨γ l', hγ.mem l'⟩ : balForms bar X) := by
      apply Subtype.ext
      simpa using hkc
    have := congrArg (ψ l) hsub
    rw [map_nsmul, map_sum] at this
    simp only [map_nsmul, hψ', nsmul_eq_mul, mul_ite, mul_one, mul_zero, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at this
    exact this
  have hψface : ∀ l i', a j i' ≠ 0 → 0 ≤ ψ l ⟨γ' i', hγ'.mem i'⟩ := by
    intro l i' hai'
    obtain ⟨k, c, hk, hkc⟩ := hface i' hai'
    have e := hcoef i' k c hkc l
    have hk' : (0 : ℤ) < k := by exact_mod_cast hk
    have hc' : (0 : ℤ) ≤ c l := by positivity
    nlinarith
  have hψzero : ∀ l, l ≠ j → ψ l ⟨γ' i, hγ'.mem i⟩ = 0 := by
    intro l hl
    have e := sum_mul_eq_of_sum_toReal_eq (j := (balForms bar X).subtype) (balForms bar X).injective_subtype
      (ψ l) (u := fun _ : Unit => (⟨γ j, hγ.mem j⟩ : balForms bar X))
      (w := fun i' => (⟨γ' i', hγ'.mem i'⟩ : balForms bar X)) (a := fun _ => (1 : ℝ)) (b := a j)
      (by simpa using hsum j)
    have e' : ∑ i', a j i' * (ψ l ⟨γ' i', hγ'.mem i'⟩ : ℝ) = 0 := by
      simpa [hψ', hl] using e.symm
    have hnn : ∀ i' ∈ Finset.univ, 0 ≤ a j i' * (ψ l ⟨γ' i', hγ'.mem i'⟩ : ℝ) := by
      intro i' _
      by_cases h0 : a j i' = 0
      · simp [h0]
      · exact mul_nonneg (ha j i') (by exact_mod_cast hψface l i' h0)
    have e2 := (Finset.sum_eq_zero_iff_of_nonneg hnn).mp e' i (Finset.mem_univ i)
    have e3 := (mul_eq_zero.mp e2).resolve_left hai
    exact_mod_cast e3
  obtain ⟨k, c, hk, hkc⟩ := hface i hai
  have hcl : ∀ l, l ≠ j → c l = 0 := by
    intro l hl
    have e := hcoef i k c hkc l
    rw [hψzero l hl, mul_zero] at e
    exact_mod_cast e.symm
  have hkc' : (k : ℤ) • γ' i = (c j : ℤ) • γ j := by
    rw [natCast_zsmul, natCast_zsmul, hkc, Finset.sum_eq_single j]
    · intro l _ hl
      rw [hcl l hl, zero_smul]
    · intro hj
      exact absurd (Finset.mem_univ j) hj
  have hcj : 0 < c j := by
    rcases Nat.eq_zero_or_pos (c j) with h0 | h0
    · exfalso
      apply hγi
      rw [h0, Nat.cast_zero, zero_smul] at hkc'
      exact smul_cancel (k := (k : ℤ)) (by exact_mod_cast hk.ne') (by rw [hkc', smul_zero])
    · exact h0
  exact ⟨i, k, c j, hk, hcj, hkc'⟩

end GlobalTheory.PolFan.SmoothEnd

namespace GlobalTheory.PolFan.SmoothEnd

variable {O : Type} [CommRing O] [IsDedekindDomain O] [CharZero O] [Module.Finite ℤ O] {bar : O → O} {φ lab : InvFun O}
  {q : ℕ}

/- English proof (translation)
Use `le_iSup_of_le X ?_` and prove the remaining obligations. Use `le_iSup_of_le (inferInstance : AddCommGroup X) ?_` and prove the remaining obligations. Use `le_iSup_of_le (inferInstance : Module O X) ?_` and prove the remaining obligations. Use `le_iSup_of_le (inferInstance : Module.Finite O X) ?_` and prove the remaining obligations. Use `le_iSup_of_le (inferInstance : Module.Projective O X) ?_` and prove the remaining obligations.

Use `le_iSup_of_le hX ?_` and prove the remaining obligations. Use `le_iSup_of_le m ?_` and prove the remaining obligations. Use `le_iSup_of_le δ ?_` and prove the remaining obligations. Use `le_iSup_of_le h ?_` and prove the remaining obligations. Use `le_iSup_of_le hli ?_` and prove the remaining obligations.

Conclude with `le_iSup_of_le hp le_rfl`.
-/
theorem cellMult_le_maxMult {X : Type} [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) {m : ℕ} {δ : Fin m → LinearMap.BilinForm ℤ X} (h : IsCell bar φ δ)
    (hli : LinearIndependent ℤ δ) (hp : ∀ i, IsPrim bar (⟨δ i, h.mem i⟩ : balForms bar X)) :
    ((cellMult bar fun i => (⟨δ i, h.mem i⟩ : balForms bar X)) : ℕ∞) ≤ maxMult bar q φ := by
  refine le_iSup_of_le X ?_
  refine le_iSup_of_le (inferInstance : AddCommGroup X) ?_
  refine le_iSup_of_le (inferInstance : Module O X) ?_
  refine le_iSup_of_le (inferInstance : Module.Finite O X) ?_
  refine le_iSup_of_le (inferInstance : Module.Projective O X) ?_
  refine le_iSup_of_le hX ?_
  refine le_iSup_of_le m ?_
  refine le_iSup_of_le δ ?_
  refine le_iSup_of_le h ?_
  refine le_iSup_of_le hli ?_
  exact le_iSup_of_le hp le_rfl

/- English proof (translation)
Use `haveI : Module.Finite ℤ X := Module.Finite.trans O X`. Take `⟨n, p, hp⟩` from `Module.Finite.exists_fin' ℤ X`. Set `F : balForms bar X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ)` to `{ toFun := fun β => (β : LinearMap.BilinForm ℤ X).compl₁₂ p p map_add' := fun β β' => by ext; simp map_smul' := fun c β => by ext; simp }`. Establish `hF : Function.Injective F`. Introduce `β β' h`.

Apply `Subtype.ext` to reduce the goal to its premises. Use extensionality with `x y`. Take `⟨x', rfl⟩` from `hp x`. Take `⟨y', rfl⟩` from `hp y`. Use `LinearMap.congr_fun₂ h x' y'` as an intermediate fact.

Simplify `this` using `[F]`. Use `haveI : Module.Finite ℤ (balForms bar X) := Module.Finite.of_injective F hF`. Use `haveI : Module.IsTorsionFree ℤ (balForms bar X) := Function.Injective.moduleIsTorsionFree F hF (fun c β => map_smul F c β)`. Conclude with `⟨inferInstance, inferInstance⟩`.
-/
private lemma balForms_free_and_finite (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] :
    Module.Free ℤ (balForms bar X) ∧ Module.Finite ℤ (balForms bar X) := by
  haveI : Module.Finite ℤ X := Module.Finite.trans O X
  obtain ⟨n, p, hp⟩ := Module.Finite.exists_fin' ℤ X
  let F : balForms bar X →ₗ[ℤ] LinearMap.BilinForm ℤ (Fin n → ℤ) :=
    { toFun := fun β => (β : LinearMap.BilinForm ℤ X).compl₁₂ p p
      map_add' := fun β β' => by ext; simp
      map_smul' := fun c β => by ext; simp }
  have hF : Function.Injective F := by
    intro β β' h
    apply Subtype.ext
    ext x y
    obtain ⟨x', rfl⟩ := hp x
    obtain ⟨y', rfl⟩ := hp y
    have := LinearMap.congr_fun₂ h x' y'
    simpa [F] using this
  haveI : Module.Finite ℤ (balForms bar X) := Module.Finite.of_injective F hF
  haveI : Module.IsTorsionFree ℤ (balForms bar X) :=
    Function.Injective.moduleIsTorsionFree F hF (fun c β => map_smul F c β)
  exact ⟨inferInstance, inferInstance⟩

/- English proof (translation)
Establish `hP : IsPolyFanOn bar φ X` using `hPF X hX`. Establish `hDX : Dominates bar X` using `hD X`. Take `⟨hfree, hfin⟩` from `balForms_free_and_finite (bar := bar) X`. Use `⟨⟨hP.homog, hP.superadd, hP.integral, hP.pos, fun m m' γ s hγ => hγ.comp s (GlobalTheory.T.isStrict_face_of_smoothCone_polyhedralFan O bar φ X hP hDX m m' γ s hγ), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `B hB`.

Take `⟨S0, -, hS0⟩` from `hP.finite`. Take `⟨e, m, δ, c, hδ, -, hc, hBe⟩` from `hS0 B hB`. Take `⟨m', δ', hδ', hli, -, hcone⟩` from `hSL.2 X hX m δ hδ`. Use `choose a ha hδa using hcone`. Establish `h0 : ∀ i, δ' i ≠ 0` using `fun i => hli.ne_zero i`.

Use `choose n u hu hn hnu hprim using fun i => exists_prim (hδ'.mem i) (h0 i)`. Establish `hcell : IsCell bar φ u` using `cell_rescale hδ' n hn hnu hu`. Establish `hliu : LinearIndependent ℤ u` using `linearIndependent_of_smul hli n hn hnu`. Establish `hmult` using `cellMult_le_maxMult hX hcell hliu hprim`. Establish `hmult1 : cellMult bar (fun i => (⟨u i, hcell.mem i⟩ : balForms bar X)) ≤ 1`.

Use `hmult.trans hM` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hbasis : IsPartOfBasis (fun i => (⟨u i, hcell.mem i⟩ : balForms bar X))` using `isPartOfBasis_of_card_torsion_le_one _ m' _ (LinearIndependent.of_comp (balForms bar X).subtype hliu) hmult1`. Establish `hcone : IsCone bar φ u` using `⟨hcell.mem, hcell.nonneg, hbasis, hcell.linear, hcell.strict⟩`. Use `⟨m', fun i => pull e.symm.toLinearMap (u i), fun i => (∑ j, c j * a j i) * n i, hcone.pull_equiv e.symm, fun i => ?_, ?_⟩` and prove the remaining obligations.

Conclude with `mul_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j i)) (Nat.cast_nonneg _)`. Use extensionality with `x y`. Establish `h1` using `LinearMap.congr_fun₂ hBe (e.symm x) (e.symm y)`. Simplify using `only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply] at h1`. Rewrite using `[h1]`.

Simplify using `only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply, pull_apply, LinearEquiv.coe_coe]`. Establish `h2 : ∀ j, (δ j (e.symm x) (e.symm y) : ℝ) = ∑ i, a j i * ((n i : ℝ) * (u i (e.symm x) (e.symm y) : ℝ))`. Introduce `j`. Establish `h3` using `LinearMap.congr_fun₂ (hδa j) (e.symm x) (e.symm y)`. Simplify using `only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h3`.

Rewrite using `[h3]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hnu i]`. Simplify using `only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]`. Simplify using `only [h2, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring`. Take `⟨S0, hS0f, hS0⟩` from `hP.finite`. Use `⟨{β | ∃ h : β ∈ balForms bar X, IsPrim bar ⟨β, h⟩ ∧ ∃ β₀ ∈ S0, ∃ k n : ℕ, 0 < k ∧ 0 < n ∧ (k : ℤ) • β₀ = (n : ℤ) • β}, ?_, ?_⟩` and prove the remaining obligations. Use `Set.Finite.subset (hS0f.biUnion (t := fun β₀ => {β | ∃ h : β ∈ balForms bar X, IsPrim bar ⟨β, h⟩ ∧ ∃ k n : ℕ, 0 < k ∧ 0 < n ∧ (k : ℤ) • β₀ = (n : ℤ) • β}) fun β₀ _ => Set.Subsingleton.finite ?_) ?_` and prove the remaining obligations.

Introduce and unpack `x ⟨hx, px, k, n, hk, hn, hkn⟩ y ⟨hy, py, k', n', hk', hn', hkn'⟩`. Use `eq_of_isPrim hx hy px py (k := k' * n) (n := k * n') (Nat.mul_pos hk' hn) (Nat.mul_pos hk hn') ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `β ⟨hβ, pβ, β₀, hβ₀, k, n, hk, hn, h⟩`. Conclude with `Set.mem_biUnion hβ₀ ⟨hβ, pβ, k, n, hk, hn, h⟩`.

Introduce `m γ hγ`. Establish `hB : ∑ j, toReal (γ j) ∈ psdCone bar X`. Use `ConeSub.sum_smul_toReal_mem_psdCone O bar X m γ (fun _ => 1) hγ.mem hγ.nonneg (fun _ => zero_le_one)` as an intermediate fact. Simplify using `using this`. Take `⟨e, m', δ, c, hδ, hδS, hc, hBe⟩` from `hS0 _ hB`.

Establish `hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j)` using `hγ.pull_equiv e`. Establish `hsum : ∑ j, toReal (pull e.toLinearMap (γ j)) = ∑ i, c i • toReal (δ i)`. Rewrite using `[← hBe]`. Use extensionality with `x y`. Simplify using the standard rewrite rules.

Establish `hin` using `mem_cone_of_sum O bar φ X m m' _ δ hγe.isCell hδ c hc hsum`. Use `choose a ha hja using hin`. Establish `hray` using `ray_of_mem_cone O bar φ X m m' _ δ hγe hδ a ha hja`. Use `⟨e, fun j => ?_⟩` and prove the remaining obligations. Take `⟨i, k, n, hk, hn, hkn⟩` from `hray j`.

Conclude with `⟨pull_mem _ (hγ.mem j), isPrim_of_isPartOfBasis hγe.basis j, δ i, hδS i, k, n, hk, hn, hkn⟩`. Introduce `m γ hγ e i j hij`. Take `⟨hlab, hcell⟩` from `hSL`. Take `⟨m', δ, hδ, -, hinj, hcone⟩` from `hcell X hX m γ hγ.isCell`. Use `choose a ha hja using hcone`.

Establish `hray` using `ray_of_mem_cone O bar φ X m m' γ δ hγ hδ a ha hja`. Take `⟨li, ki, ni, hki, hni, hi⟩` from `hray i`. Take `⟨lj, kj, nj, hkj, hnj, hj⟩` from `hray j`. Establish `lab_ray : ∀ l t (kk nn : ℕ), 0 < kk → 0 < nn → (kk : ℤ) • δ l = (nn : ℤ) • γ t → lab.evalZ (δ l) = lab.evalZ (γ t)`. Introduce `l t kk nn hkk hnn h`.

Rewrite using `[← hlab X hX (δ l) (hδ.mem l) (hδ.nonneg l) kk hkk, h, hlab X hX (γ t) (hγ.mem t) (hγ.nonneg t) nn hnn]`. Establish `hli` using `lab_ray _ _ _ _ hki hni hi`. Establish `hlj` using `lab_ray _ _ _ _ hkj hnj hj`. Establish `hinv : lab.evalZ (γ i) = lab.evalZ (γ j)`. Rewrite using `[← hij, evalZ_pull lab e.surjective]`.

Establish `hl : li = lj` using `hinj (show lab.evalZ (δ li) = lab.evalZ (δ lj) by rw [hli, hlj, hinv])`. Rewrite `hj` using `[← hl]`. Establish `hxy : γ i = γ j`. Use `eq_of_isPrim (hγ.mem i) (hγ.mem j) (isPrim_of_isPartOfBasis hγ.basis i) (isPrim_of_isPartOfBasis hγ.basis j) (k := kj * ni) (n := ki * nj) (Nat.mul_pos hkj hni) (Nat.mul_pos hki hnj) ?_` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Conclude with `hγ.injective hxy`.
-/
theorem onModule (hD : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X],
      Dominates bar X) (hPF : IsPolyFan bar q φ) (hSL : SimpLab bar q φ lab) (hM : maxMult bar q φ ≤ 1)
    (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X] [Module.Projective O X]
    (hX : Module.finrank O X ≤ q) : IsPolFanOn bar φ X ∧ ∀ (m : ℕ) (γ : Fin m → LinearMap.BilinForm ℤ X),
      IsCone bar φ γ → NoEquivRays O γ := by
  have hP : IsPolyFanOn bar φ X := hPF X hX
  have hDX : Dominates bar X := hD X
  obtain ⟨hfree, hfin⟩ := balForms_free_and_finite (bar := bar) X
  refine ⟨⟨hP.homog, hP.superadd, hP.integral, hP.pos,
    fun m m' γ s hγ => hγ.comp s (GlobalTheory.T.isStrict_face_of_smoothCone_polyhedralFan O bar φ X hP hDX m m' γ s hγ), ?_, ?_⟩, ?_⟩
  · intro B hB
    obtain ⟨S0, -, hS0⟩ := hP.finite
    obtain ⟨e, m, δ, c, hδ, -, hc, hBe⟩ := hS0 B hB
    obtain ⟨m', δ', hδ', hli, -, hcone⟩ := hSL.2 X hX m δ hδ
    choose a ha hδa using hcone
    have h0 : ∀ i, δ' i ≠ 0 := fun i => hli.ne_zero i
    choose n u hu hn hnu hprim using fun i => exists_prim (hδ'.mem i) (h0 i)
    have hcell : IsCell bar φ u := cell_rescale hδ' n hn hnu hu
    have hliu : LinearIndependent ℤ u := linearIndependent_of_smul hli n hn hnu
    have hmult := cellMult_le_maxMult hX hcell hliu hprim
    have hmult1 : cellMult bar (fun i => (⟨u i, hcell.mem i⟩ : balForms bar X)) ≤ 1 := by
      have := hmult.trans hM
      exact_mod_cast this
    have hbasis : IsPartOfBasis (fun i => (⟨u i, hcell.mem i⟩ : balForms bar X)) :=
      isPartOfBasis_of_card_torsion_le_one _ m' _ (LinearIndependent.of_comp (balForms bar X).subtype hliu) hmult1
    have hcone : IsCone bar φ u := ⟨hcell.mem, hcell.nonneg, hbasis, hcell.linear, hcell.strict⟩
    refine ⟨m', fun i => pull e.symm.toLinearMap (u i), fun i => (∑ j, c j * a j i) * n i,
      hcone.pull_equiv e.symm, fun i => ?_, ?_⟩
    · exact mul_nonneg (Finset.sum_nonneg fun j _ => mul_nonneg (hc j) (ha j i)) (Nat.cast_nonneg _)
    · ext x y
      have h1 := LinearMap.congr_fun₂ hBe (e.symm x) (e.symm y)
      simp only [pullR_apply, LinearEquiv.coe_coe, LinearEquiv.apply_symm_apply, LinearMap.sum_apply,
        Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply] at h1
      rw [h1]
      simp only [LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul, toReal_apply,
        pull_apply, LinearEquiv.coe_coe]
      have h2 : ∀ j, (δ j (e.symm x) (e.symm y) : ℝ) =
          ∑ i, a j i * ((n i : ℝ) * (u i (e.symm x) (e.symm y) : ℝ)) := by
        intro j
        have h3 := LinearMap.congr_fun₂ (hδa j) (e.symm x) (e.symm y)
        simp only [toReal_apply, LinearMap.sum_apply, Finset.sum_apply, LinearMap.smul_apply, smul_eq_mul] at h3
        rw [h3]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [hnu i]
        simp only [LinearMap.smul_apply, smul_eq_mul, Int.cast_mul, Int.cast_natCast]
      simp only [h2, Finset.mul_sum, Finset.sum_mul]
      rw [Finset.sum_comm]
      exact Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  · obtain ⟨S0, hS0f, hS0⟩ := hP.finite
    refine ⟨{β | ∃ h : β ∈ balForms bar X, IsPrim bar ⟨β, h⟩ ∧ ∃ β₀ ∈ S0, ∃ k n : ℕ, 0 < k ∧ 0 < n ∧
      (k : ℤ) • β₀ = (n : ℤ) • β}, ?_, ?_⟩
    · refine Set.Finite.subset (hS0f.biUnion (t := fun β₀ => {β | ∃ h : β ∈ balForms bar X, IsPrim bar ⟨β, h⟩ ∧
        ∃ k n : ℕ, 0 < k ∧ 0 < n ∧ (k : ℤ) • β₀ = (n : ℤ) • β}) fun β₀ _ => Set.Subsingleton.finite ?_) ?_
      · rintro x ⟨hx, px, k, n, hk, hn, hkn⟩ y ⟨hy, py, k', n', hk', hn', hkn'⟩
        refine eq_of_isPrim hx hy px py (k := k' * n) (n := k * n') (Nat.mul_pos hk' hn) (Nat.mul_pos hk hn') ?_
        calc ((k' * n : ℕ) : ℤ) • x = (k' : ℤ) • ((n : ℤ) • x) := by rw [smul_smul, Nat.cast_mul]
          _ = (k' : ℤ) • ((k : ℤ) • β₀) := by rw [hkn]
          _ = (k : ℤ) • ((k' : ℤ) • β₀) := by rw [smul_smul, smul_smul, mul_comm]
          _ = (k : ℤ) • ((n' : ℤ) • y) := by rw [hkn']
          _ = ((k * n' : ℕ) : ℤ) • y := by rw [smul_smul, Nat.cast_mul]
      · rintro β ⟨hβ, pβ, β₀, hβ₀, k, n, hk, hn, h⟩
        exact Set.mem_biUnion hβ₀ ⟨hβ, pβ, k, n, hk, hn, h⟩
    · intro m γ hγ
      have hB : ∑ j, toReal (γ j) ∈ psdCone bar X := by
        have := ConeSub.sum_smul_toReal_mem_psdCone O bar X m γ (fun _ => 1) hγ.mem hγ.nonneg (fun _ => zero_le_one)
        simpa using this
      obtain ⟨e, m', δ, c, hδ, hδS, hc, hBe⟩ := hS0 _ hB
      have hγe : IsCone bar φ fun j => pull e.toLinearMap (γ j) := hγ.pull_equiv e
      have hsum : ∑ j, toReal (pull e.toLinearMap (γ j)) = ∑ i, c i • toReal (δ i) := by
        rw [← hBe]
        ext x y
        simp
      have hin := mem_cone_of_sum O bar φ X m m' _ δ hγe.isCell hδ c hc hsum
      choose a ha hja using hin
      have hray := ray_of_mem_cone O bar φ X m m' _ δ hγe hδ a ha hja
      refine ⟨e, fun j => ?_⟩
      obtain ⟨i, k, n, hk, hn, hkn⟩ := hray j
      exact ⟨pull_mem _ (hγ.mem j), isPrim_of_isPartOfBasis hγe.basis j, δ i, hδS i, k, n, hk, hn, hkn⟩
  · intro m γ hγ e i j hij
    obtain ⟨hlab, hcell⟩ := hSL
    obtain ⟨m', δ, hδ, -, hinj, hcone⟩ := hcell X hX m γ hγ.isCell
    choose a ha hja using hcone
    have hray := ray_of_mem_cone O bar φ X m m' γ δ hγ hδ a ha hja
    obtain ⟨li, ki, ni, hki, hni, hi⟩ := hray i
    obtain ⟨lj, kj, nj, hkj, hnj, hj⟩ := hray j
    have lab_ray : ∀ l t (kk nn : ℕ), 0 < kk → 0 < nn → (kk : ℤ) • δ l = (nn : ℤ) • γ t →
        lab.evalZ (δ l) = lab.evalZ (γ t) := by
      intro l t kk nn hkk hnn h
      rw [← hlab X hX (δ l) (hδ.mem l) (hδ.nonneg l) kk hkk, h,
        hlab X hX (γ t) (hγ.mem t) (hγ.nonneg t) nn hnn]
    have hli := lab_ray _ _ _ _ hki hni hi
    have hlj := lab_ray _ _ _ _ hkj hnj hj
    have hinv : lab.evalZ (γ i) = lab.evalZ (γ j) := by
      rw [← hij, evalZ_pull lab e.surjective]
    have hl : li = lj := hinj (show lab.evalZ (δ li) = lab.evalZ (δ lj) by rw [hli, hlj, hinv])
    rw [← hl] at hj
    have hxy : γ i = γ j := by
      refine eq_of_isPrim (hγ.mem i) (hγ.mem j) (isPrim_of_isPartOfBasis hγ.basis i)
        (isPrim_of_isPartOfBasis hγ.basis j) (k := kj * ni) (n := ki * nj) (Nat.mul_pos hkj hni)
        (Nat.mul_pos hki hnj) ?_
      calc ((kj * ni : ℕ) : ℤ) • γ i = (kj : ℤ) • ((ni : ℤ) • γ i) := by rw [smul_smul, Nat.cast_mul]
        _ = (kj : ℤ) • ((ki : ℤ) • δ li) := by rw [hi]
        _ = (ki : ℤ) • ((kj : ℤ) • δ li) := by rw [smul_smul, smul_smul, mul_comm]
        _ = (ki : ℤ) • ((nj : ℤ) • γ j) := by rw [hj]
        _ = ((ki * nj : ℕ) : ℤ) • γ j := by rw [smul_smul, Nat.cast_mul]
    exact hγ.injective hxy

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Introduce `X _ _ _ _ hX`. Conclude with `(onModule hD hPF hSL hM X hX).1`. Introduce `X _ _ _ _ hX`. Conclude with `(onModule hD hPF hSL hM X hX).2`.
-/
theorem isPolFan_of_maxMult_le_one (hD : ∀ (X : Type) [AddCommGroup X] [Module O X] [Module.Finite O X]
      [Module.Projective O X], Dominates bar X) (hPF : IsPolyFan bar q φ) (hSL : SimpLab bar q φ lab)
    (hM : maxMult bar q φ ≤ 1) : IsPolFan bar q φ ∧ NoSelfInt bar q φ := by
  refine ⟨?_, ?_⟩
  · intro X _ _ _ _ hX
    exact (onModule hD hPF hSL hM X hX).1
  · intro X _ _ _ _ hX
    exact (onModule hD hPF hSL hM X hX).2

end GlobalTheory.PolFan.SmoothEnd

open GlobalTheory.PolFan.SmoothEnd in

/- English proof (translation)
Introduce `E _ _ _ H q φ lab hD hPF hSL hM`. Conclude with `isPolFan_of_maxMult_le_one hD hPF hSL hM`.
-/
theorem GlobalTheory.PolFan.smoothEnd : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (q : ℕ) (φ lab : InvFun (𝓞 E)), (∀ (X : Type) [AddCommGroup X] [Module (𝓞 E) X] [Module.Finite (𝓞 E) X] [Module.Projective (𝓞 E) X], Dominates H.bar X) → IsPolyFan H.bar q φ → SimpLab H.bar q φ lab → maxMult H.bar q φ ≤ 1 → IsPolFan H.bar q φ ∧ NoSelfInt H.bar q φ := by
  intro E _ _ _ H q φ lab hD hPF hSL hM
  exact isPolFan_of_maxMult_le_one hD hPF hSL hM
