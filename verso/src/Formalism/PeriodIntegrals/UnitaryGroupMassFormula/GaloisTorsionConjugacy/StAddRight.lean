import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpBridge
import Formalism.LocalToGlobal.TorsionIntegrality.EisensteinTranslationProducts.MulStableIntegral

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def St (L L' : PeriodPair) (M : IntermediateField ℚ ℂ) (ρ : M →ₐ[ℚ] ℂ) (t t' : ℂ) : Prop :=
  (t ∈ L.lattice ∧ t' ∈ L'.lattice) ∨
  (t ∉ L.lattice ∧ t' ∉ L'.lattice ∧ ∃ (hx : L.weierstrassP t ∈ M) (hy : L.derivWeierstrassP t ∈ M),
    L'.weierstrassP t' = ρ ⟨_, hx⟩ ∧ L'.derivWeierstrassP t' = ρ ⟨_, hy⟩)

section maps

variable {K K' : Type*} [Field K] [Field K']

/- English proof (translation)
Simplify using `only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]`.
-/
theorem addX_map (φ : K →+* K') (x y x₂ y₂ : K) :
    φ (addX x y x₂ y₂) = addX (φ x) (φ y) (φ x₂) (φ y₂) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]

/- English proof (translation)
Simplify using `only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]`.
-/
theorem addY_map (φ : K →+* K') (x y x₂ y₂ : K) :
    φ (addY x y x₂ y₂) = addY (φ x) (φ y) (φ x₂) (φ y₂) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]

/- English proof (translation)
Simplify using `only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]`.
-/
theorem dblX_map (φ : K →+* K') (x y g : K) :
    φ (dblX x y g) = dblX (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]

/- English proof (translation)
Simplify using `only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]`.
-/
theorem dblY_map (φ : K →+* K') (x y g : K) :
    φ (dblY x y g) = dblY (φ x) (φ y) (φ g) := by
  simp only [addX, addY, dblX, dblY, map_div₀, map_sub, map_pow, map_mul, map_add, map_neg, map_ofNat]

end maps

/- English proof (translation)
The claim follows from `PeriodPair.weierstrassP_add_coe L z ⟨ω, h⟩`.
-/
theorem wp_add_mem (L : PeriodPair) (z : ℂ) {ω : ℂ} (h : ω ∈ L.lattice) :
    L.weierstrassP (z + ω) = L.weierstrassP z := PeriodPair.weierstrassP_add_coe L z ⟨ω, h⟩

/- English proof (translation)
The claim follows from `PeriodPair.derivWeierstrassP_add_coe L z ⟨ω, h⟩`.
-/
theorem dwp_add_mem (L : PeriodPair) (z : ℂ) {ω : ℂ} (h : ω ∈ L.lattice) :
    L.derivWeierstrassP (z + ω) = L.derivWeierstrassP z := PeriodPair.derivWeierstrassP_add_coe L z ⟨ω, h⟩

/- English proof (translation)
Establish `hr : r = -s + (s + r)` using `by ring`. Rewrite using `[hr, wp_add_mem L _ h, dwp_add_mem L _ h, PeriodPair.weierstrassP_neg, PeriodPair.derivWeierstrassP_neg]`. Conclude with `⟨rfl, rfl⟩`.
-/
theorem neg_pair (L : PeriodPair) {s r : ℂ} (h : s + r ∈ L.lattice) :
    L.weierstrassP r = L.weierstrassP s ∧ L.derivWeierstrassP r = -L.derivWeierstrassP s := by
  have hr : r = -s + (s + r) := by ring
  rw [hr, wp_add_mem L _ h, dwp_add_mem L _ h, PeriodPair.weierstrassP_neg,
    PeriodPair.derivWeierstrassP_neg]
  exact ⟨rfl, rfl⟩

/- English proof (translation)
Break down `(pInjective L z w hz hw).1 hx with h | h` into its components or cases. Conclude with `h`. Establish `h1` using `(neg_pair L h).2`. Establish `h0 : L.derivWeierstrassP z = 0` using `by linear_combination (hy + h1) / 2`. Establish `h2 : 2 * z ∈ L.lattice` using `(pDerivZero L z hz).1 h0`.

Establish `e : z - w = 2 * z - (z + w)` using `by ring`. Rewrite using `[e]`. Conclude with `L.lattice.sub_mem h2 h`.
-/
theorem pInj (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = L.derivWeierstrassP w) :
    z - w ∈ L.lattice := by
  rcases (pInjective L z w hz hw).1 hx with h | h
  · exact h
  · have h1 := (neg_pair L h).2
    have h0 : L.derivWeierstrassP z = 0 := by linear_combination (hy + h1) / 2
    have h2 : 2 * z ∈ L.lattice := (pDerivZero L z hz).1 h0
    have e : z - w = 2 * z - (z + w) := by ring
    rw [e]
    exact L.lattice.sub_mem h2 h

/- English proof (translation)
Establish `hw' : -w ∉ L.lattice` using `fun h => hw (by simpa using L.lattice.neg_mem h)`. Establish `h` using `pInj L hz hw' (by rw [PeriodPair.weierstrassP_neg, hx]) (by rw [PeriodPair.derivWeierstrassP_neg, hy])`. Simplify using `using h`.
-/
theorem pNeg (L : PeriodPair) {z w : ℂ} (hz : z ∉ L.lattice) (hw : w ∉ L.lattice)
    (hx : L.weierstrassP z = L.weierstrassP w) (hy : L.derivWeierstrassP z = -L.derivWeierstrassP w) :
    z + w ∈ L.lattice := by
  have hw' : -w ∉ L.lattice := fun h => hw (by simpa using L.lattice.neg_mem h)
  have h := pInj L hz hw' (by rw [PeriodPair.weierstrassP_neg, hx])
    (by rw [PeriodPair.derivWeierstrassP_neg, hy])
  simpa using h

section rel

variable {L L' : PeriodPair} {M : IntermediateField ℚ ℂ} {ρ : M →ₐ[ℚ] ℂ}

/- English proof (translation)
The claim follows from `ρ.toRingHom.injective h`.
-/
theorem rho_inj {a b : M} (h : ρ a = ρ b) : a = b := ρ.toRingHom.injective h

/- English proof (translation)
The claim follows from `Or.inl ⟨L.lattice.zero_mem, L'.lattice.zero_mem⟩`.
-/
theorem st_zero : St L L' M ρ 0 0 := Or.inl ⟨L.lattice.zero_mem, L'.lattice.zero_mem⟩

/- English proof (translation)
Break down `h with ⟨h1, h2⟩ | ⟨h1, h2, _⟩` into its components or cases. Conclude with `⟨fun _ => h2, fun _ => h1⟩`. Conclude with `⟨fun h => absurd h h1, fun h => absurd h h2⟩`.
-/
theorem st_mem_iff {t t' : ℂ} (h : St L L' M ρ t t') : t ∈ L.lattice ↔ t' ∈ L'.lattice := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, _⟩
  · exact ⟨fun _ => h2, fun _ => h1⟩
  · exact ⟨fun h => absurd h h1, fun h => absurd h h2⟩

/- English proof (translation)
Break down `h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩` into its components or cases. Conclude with `Or.inl ⟨h1, L'.lattice.add_mem h2 hω⟩`. Use `Or.inr ⟨h1, fun hh => h2 (by simpa using L'.lattice.sub_mem hh hω), hx, hy, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[wp_add_mem L' t' hω, e1]`. Rewrite using `[dwp_add_mem L' t' hω, e2]`.
-/
theorem st_add_right {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L'.lattice) :
    St L L' M ρ t (t' + ω) := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨h1, L'.lattice.add_mem h2 hω⟩
  · refine Or.inr ⟨h1, fun hh => h2 (by simpa using L'.lattice.sub_mem hh hω), hx, hy, ?_, ?_⟩
    · rw [wp_add_mem L' t' hω, e1]
    · rw [dwp_add_mem L' t' hω, e2]

/- English proof (translation)
Break down `h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩` into its components or cases. Conclude with `Or.inl ⟨L.lattice.add_mem h1 hω, h2⟩`. Establish `ex : L.weierstrassP (t + ω) = L.weierstrassP t` using `wp_add_mem L t hω`. Establish `ey : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t` using `dwp_add_mem L t hω`. Establish `hx' : L.weierstrassP (t + ω) ∈ M` using `by rw [ex]; exact hx`.

Establish `hy' : L.derivWeierstrassP (t + ω) ∈ M` using `by rw [ey]; exact hy`. Use `Or.inr ⟨fun hh => h1 (by simpa using L.lattice.sub_mem hh hω), h2, hx', hy', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[e1]`. Use `congr 1`. Conclude with `Subtype.ext ex.symm`.

Rewrite using `[e2]`. Use `congr 1`. Conclude with `Subtype.ext ey.symm`.
-/
theorem st_add_left {t t' ω : ℂ} (h : St L L' M ρ t t') (hω : ω ∈ L.lattice) :
    St L L' M ρ (t + ω) t' := by
  rcases h with ⟨h1, h2⟩ | ⟨h1, h2, hx, hy, e1, e2⟩
  · exact Or.inl ⟨L.lattice.add_mem h1 hω, h2⟩
  · have ex : L.weierstrassP (t + ω) = L.weierstrassP t := wp_add_mem L t hω
    have ey : L.derivWeierstrassP (t + ω) = L.derivWeierstrassP t := dwp_add_mem L t hω
    have hx' : L.weierstrassP (t + ω) ∈ M := by rw [ex]; exact hx
    have hy' : L.derivWeierstrassP (t + ω) ∈ M := by rw [ey]; exact hy
    refine Or.inr ⟨fun hh => h1 (by simpa using L.lattice.sub_mem hh hω), h2, hx', hy', ?_, ?_⟩
    · rw [e1]
      congr 1
      exact Subtype.ext ex.symm
    · rw [e2]
      congr 1
      exact Subtype.ext ey.symm

/- English proof (translation)
Break down `h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩` into its components or cases. Break down `h2 with ⟨a2, b2⟩ | ⟨a2, _, _, _, _, _⟩` into its components or cases. Conclude with `L'.lattice.sub_mem b1 b2`. Conclude with `absurd a1 a2`. Break down `h2 with ⟨a2, _⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩` into its components or cases.

Conclude with `absurd a2 a1`. Conclude with `pInj L' b1 b2 (by rw [e1, e2]) (by rw [f1, f2])`.
-/
theorem st_unique {t t₁ t₂ : ℂ} (h1 : St L L' M ρ t t₁) (h2 : St L L' M ρ t t₂) :
    t₁ - t₂ ∈ L'.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, _, _, _, _, _⟩
    · exact L'.lattice.sub_mem b1 b2
    · exact absurd a1 a2
  · rcases h2 with ⟨a2, _⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd a2 a1
    · exact pInj L' b1 b2 (by rw [e1, e2]) (by rw [f1, f2])

/- English proof (translation)
Break down `h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩` into its components or cases. Break down `h2 with ⟨a2, b2⟩ | ⟨a2, b2, _, _, _, _⟩` into its components or cases. Conclude with `L.lattice.sub_mem a1 a2`. Conclude with `absurd b1 b2`. Break down `h2 with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩` into its components or cases.

Conclude with `absurd b2 b1`. Establish `gx` using `rho_inj (e1.symm.trans e2)`. Establish `gy` using `rho_inj (f1.symm.trans f2)`. Conclude with `pInj L a1 a2 (congrArg Subtype.val gx) (congrArg Subtype.val gy)`.
-/
theorem st_inj {t u s : ℂ} (h1 : St L L' M ρ t s) (h2 : St L L' M ρ u s) :
    t - u ∈ L.lattice := by
  rcases h1 with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, _, _, _, _⟩
    · exact L.lattice.sub_mem a1 a2
    · exact absurd b1 b2
  · rcases h2 with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
    · exact absurd b2 b1
    · have gx := rho_inj (e1.symm.trans e2)
      have gy := rho_inj (f1.symm.trans f2)
      exact pInj L a1 a2 (congrArg Subtype.val gx) (congrArg Subtype.val gy)

/- English proof (translation)
Break down `ht with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩` into its components or cases. Use `st_add_right (st_add_left hu a1) b1` as an intermediate fact. Rewrite `this` using `[add_comm u t, add_comm u' t']`. Then use the resulting hypothesis. Establish `ht : St L L' M ρ t t'` using `Or.inr ⟨a1, b1, hx1, hy1, e1, f1⟩`. Break down `hu with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩` into its components or cases.

Conclude with `st_add_right (st_add_left ht a2) b2`. Establish `hu : St L L' M ρ u u'` using `Or.inr ⟨a2, b2, hx2, hy2, e2, f2⟩`. Use `set X1 : M := ⟨_, hx1⟩`. Use `set Y1 : M := ⟨_, hy1⟩`. Use `set X2 : M := ⟨_, hx2⟩`.

Use `set Y2 : M := ⟨_, hy2⟩`. Distinguish the cases in `hs : t + u ∈ L.lattice`. Use `left`. Use `⟨hs, ?_⟩` and prove the remaining obligations. Take `⟨p1, p2⟩` from `neg_pair L hs`.

Establish `q1 : X2 = X1` using `Subtype.ext p1`. Establish `q2 : Y2 = -Y1` using `Subtype.ext (by simp [Y1, Y2, p2])`. Apply `pNeg L' b1 b2` to reduce the goal to its premises. Rewrite using `[e1, e2, q1]`. Rewrite using `[f1, f2, q2, map_neg, neg_neg]`.

Establish `hs' : t' + u' ∉ L'.lattice`. Introduce `h`. Take `⟨p1, p2⟩` from `neg_pair L' h`. Rewrite `p1` using `[e1, e2]`. Rewrite `p2` using `[f1, f2, ← map_neg]`.

Establish `k1` using `congrArg Subtype.val (rho_inj p1)`. Establish `k2` using `congrArg Subtype.val (rho_inj p2)`. Establish `k : L.derivWeierstrassP u = -L.derivWeierstrassP t` using `k2`. Conclude with `hs (pNeg L a1 a2 k1.symm (by linear_combination k))`. Use `right`.

Use `⟨hs, hs', ?_⟩` and prove the remaining obligations. Distinguish the cases in `hd : t - u ∈ L.lattice`. Establish `htu : St L L' M ρ t u'`. Use `st_add_left hu hd` as an intermediate fact. Rewrite `this` using `[show u + (t - u) = t by ring]`. Then use the resulting hypothesis.

Establish `hd' : t' - u' ∈ L'.lattice` using `st_unique ht htu`. Establish `h2 : 2 * t ∉ L.lattice`. Introduce `h`. Apply `hs` to reduce the goal to its premises. Use `L.lattice.sub_mem h hd` as an intermediate fact.

Rewrite `this` using `[show 2 * t - (t - u) = t + u by ring]`. Then use the resulting hypothesis. Establish `h2' : 2 * t' ∉ L'.lattice`. Introduce `h`. Apply `hs'` to reduce the goal to its premises. Use `L'.lattice.sub_mem h hd'` as an intermediate fact.

Rewrite `this` using `[show 2 * t' - (t' - u') = t' + u' by ring]`. Then use the resulting hypothesis. Establish `et : t + u = 2 * t + -(t - u)` using `by ring`. Establish `et' : t' + u' = 2 * t' + -(t' - u')` using `by ring`. Establish `n1` using `L.lattice.neg_mem hd`. Establish `n1'` using `L'.lattice.neg_mem hd'`.

Take `⟨d1, d2⟩` from `hD L t a1 h2`. Take `⟨d1', d2'⟩` from `hD L' t' b1 h2'`. Use `set G : M := ⟨_, hg2⟩`. Establish `v1 : L.weierstrassP (t + u) = ((dblX X1 Y1 G : M) : ℂ)`. Rewrite using `[et, wp_add_mem L _ n1, d1]`.

Conclude with `(dblX_map (algebraMap M ℂ) X1 Y1 G).symm`. Establish `v2 : L.derivWeierstrassP (t + u) = ((dblY X1 Y1 G : M) : ℂ)`. Rewrite using `[et, dwp_add_mem L _ n1, d2]`. Conclude with `(dblY_map (algebraMap M ℂ) X1 Y1 G).symm`. Use `⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[et', wp_add_mem L' _ n1', d1', e1, f1, hg2']`. Establish `: (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M) = dblX X1 Y1 G` using `Subtype.ext v1`. Rewrite using `[this]`. Conclude with `(dblX_map (ρ : M →+* ℂ) X1 Y1 G).symm`. Rewrite using `[et', dwp_add_mem L' _ n1', d2', e1, f1, hg2']`.

Establish `: (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M) = dblY X1 Y1 G` using `Subtype.ext v2`. Rewrite using `[this]`. Conclude with `(dblY_map (ρ : M →+* ℂ) X1 Y1 G).symm`. Establish `hd' : t' - u' ∉ L'.lattice`. Introduce `h`.

Establish `hut : St L L' M ρ u t'`. Use `st_add_right hu h` as an intermediate fact. Rewrite `this` using `[show u' + (t' - u') = t' by ring]`. Then use the resulting hypothesis. Conclude with `hd (st_inj ht hut)`. Take `⟨d1, d2⟩` from `hA L t u a1 a2 hd hs`.

Take `⟨d1', d2'⟩` from `hA L' t' u' b1 b2 hd' hs'`. Establish `v1 : L.weierstrassP (t + u) = ((addX X1 Y1 X2 Y2 : M) : ℂ)`. Rewrite using `[d1]`. Conclude with `(addX_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm`. Establish `v2 : L.derivWeierstrassP (t + u) = ((addY X1 Y1 X2 Y2 : M) : ℂ)`.

Rewrite using `[d2]`. Conclude with `(addY_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm`. Use `⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[d1', e1, f1, e2, f2]`. Establish `: (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M) = addX X1 Y1 X2 Y2` using `Subtype.ext v1`.

Rewrite using `[this]`. Conclude with `(addX_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm`. Rewrite using `[d2', e1, f1, e2, f2]`. Establish `: (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M) = addY X1 Y1 X2 Y2` using `Subtype.ext v2`. Rewrite using `[this]`.

Conclude with `(addY_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm`.
-/
theorem st_add (hA : AddLaw) (hD : DblLaw) (hg2 : L.g₂ ∈ M) (hg2' : L'.g₂ = ρ ⟨_, hg2⟩)
    {t t' u u' : ℂ} (ht : St L L' M ρ t t') (hu : St L L' M ρ u u') :
    St L L' M ρ (t + u) (t' + u') := by
  rcases ht with ⟨a1, b1⟩ | ⟨a1, b1, hx1, hy1, e1, f1⟩
  · have := st_add_right (st_add_left hu a1) b1
    rwa [add_comm u t, add_comm u' t'] at this
  have ht : St L L' M ρ t t' := Or.inr ⟨a1, b1, hx1, hy1, e1, f1⟩
  rcases hu with ⟨a2, b2⟩ | ⟨a2, b2, hx2, hy2, e2, f2⟩
  · exact st_add_right (st_add_left ht a2) b2
  have hu : St L L' M ρ u u' := Or.inr ⟨a2, b2, hx2, hy2, e2, f2⟩
  set X1 : M := ⟨_, hx1⟩
  set Y1 : M := ⟨_, hy1⟩
  set X2 : M := ⟨_, hx2⟩
  set Y2 : M := ⟨_, hy2⟩
  by_cases hs : t + u ∈ L.lattice
  · left
    refine ⟨hs, ?_⟩
    obtain ⟨p1, p2⟩ := neg_pair L hs
    have q1 : X2 = X1 := Subtype.ext p1
    have q2 : Y2 = -Y1 := Subtype.ext (by simp [Y1, Y2, p2])
    apply pNeg L' b1 b2
    · rw [e1, e2, q1]
    · rw [f1, f2, q2, map_neg, neg_neg]
  have hs' : t' + u' ∉ L'.lattice := by
    intro h
    obtain ⟨p1, p2⟩ := neg_pair L' h
    rw [e1, e2] at p1
    rw [f1, f2, ← map_neg] at p2
    have k1 := congrArg Subtype.val (rho_inj p1)
    have k2 := congrArg Subtype.val (rho_inj p2)
    have k : L.derivWeierstrassP u = -L.derivWeierstrassP t := k2
    exact hs (pNeg L a1 a2 k1.symm (by linear_combination k))
  right
  refine ⟨hs, hs', ?_⟩
  by_cases hd : t - u ∈ L.lattice
  ·
    have htu : St L L' M ρ t u' := by
      have := st_add_left hu hd
      rwa [show u + (t - u) = t by ring] at this
    have hd' : t' - u' ∈ L'.lattice := st_unique ht htu
    have h2 : 2 * t ∉ L.lattice := by
      intro h
      apply hs
      have := L.lattice.sub_mem h hd
      rwa [show 2 * t - (t - u) = t + u by ring] at this
    have h2' : 2 * t' ∉ L'.lattice := by
      intro h
      apply hs'
      have := L'.lattice.sub_mem h hd'
      rwa [show 2 * t' - (t' - u') = t' + u' by ring] at this
    have et : t + u = 2 * t + -(t - u) := by ring
    have et' : t' + u' = 2 * t' + -(t' - u') := by ring
    have n1 := L.lattice.neg_mem hd
    have n1' := L'.lattice.neg_mem hd'
    obtain ⟨d1, d2⟩ := hD L t a1 h2
    obtain ⟨d1', d2'⟩ := hD L' t' b1 h2'
    set G : M := ⟨_, hg2⟩
    have v1 : L.weierstrassP (t + u) = ((dblX X1 Y1 G : M) : ℂ) := by
      rw [et, wp_add_mem L _ n1, d1]
      exact (dblX_map (algebraMap M ℂ) X1 Y1 G).symm
    have v2 : L.derivWeierstrassP (t + u) = ((dblY X1 Y1 G : M) : ℂ) := by
      rw [et, dwp_add_mem L _ n1, d2]
      exact (dblY_map (algebraMap M ℂ) X1 Y1 G).symm
    refine ⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩
    · rw [et', wp_add_mem L' _ n1', d1', e1, f1, hg2']
      have : (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M)
          = dblX X1 Y1 G := Subtype.ext v1
      rw [this]
      exact (dblX_map (ρ : M →+* ℂ) X1 Y1 G).symm
    · rw [et', dwp_add_mem L' _ n1', d2', e1, f1, hg2']
      have : (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M)
          = dblY X1 Y1 G := Subtype.ext v2
      rw [this]
      exact (dblY_map (ρ : M →+* ℂ) X1 Y1 G).symm
  ·
    have hd' : t' - u' ∉ L'.lattice := by
      intro h
      have hut : St L L' M ρ u t' := by
        have := st_add_right hu h
        rwa [show u' + (t' - u') = t' by ring] at this
      exact hd (st_inj ht hut)
    obtain ⟨d1, d2⟩ := hA L t u a1 a2 hd hs
    obtain ⟨d1', d2'⟩ := hA L' t' u' b1 b2 hd' hs'
    have v1 : L.weierstrassP (t + u) = ((addX X1 Y1 X2 Y2 : M) : ℂ) := by
      rw [d1]
      exact (addX_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm
    have v2 : L.derivWeierstrassP (t + u) = ((addY X1 Y1 X2 Y2 : M) : ℂ) := by
      rw [d2]
      exact (addY_map (algebraMap M ℂ) X1 Y1 X2 Y2).symm
    refine ⟨by rw [v1]; exact SetLike.coe_mem _, by rw [v2]; exact SetLike.coe_mem _, ?_, ?_⟩
    · rw [d1', e1, f1, e2, f2]
      have : (⟨_, (by rw [v1]; exact SetLike.coe_mem _ : L.weierstrassP (t + u) ∈ M)⟩ : M)
          = addX X1 Y1 X2 Y2 := Subtype.ext v1
      rw [this]
      exact (addX_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm
    · rw [d2', e1, f1, e2, f2]
      have : (⟨_, (by rw [v2]; exact SetLike.coe_mem _ : L.derivWeierstrassP (t + u) ∈ M)⟩ : M)
          = addY X1 Y1 X2 Y2 := Subtype.ext v2
      rw [this]
      exact (addY_map (ρ : M →+* ℂ) X1 Y1 X2 Y2).symm

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using (st_zero : St L L' M ρ 0 0)`. Consider the case `succ n ih`. Establish `h2` using `st_add hA hD hg2 hg2' ih h`. Establish `e1 : ((n + 1 : ℕ) : ℂ) * t = (n : ℂ) * t + t` using `by push_cast; ring`.

Establish `e2 : ((n + 1 : ℕ) : ℂ) * t' = (n : ℂ) * t' + t'` using `by push_cast; ring`. Rewrite using `[e1, e2]`. Conclude with `h2`.
-/
theorem st_nsmul (hA : AddLaw) (hD : DblLaw) (hg2 : L.g₂ ∈ M) (hg2' : L'.g₂ = ρ ⟨_, hg2⟩)
    {t t' : ℂ} (h : St L L' M ρ t t') (n : ℕ) :
    St L L' M ρ ((n : ℂ) * t) ((n : ℂ) * t') := by
  induction n with
  | zero => simpa using (st_zero : St L L' M ρ 0 0)
  | succ n ih =>
    have h2 := st_add hA hD hg2 hg2' ih h
    have e1 : ((n + 1 : ℕ) : ℂ) * t = (n : ℂ) * t + t := by push_cast; ring
    have e2 : ((n + 1 : ℕ) : ℂ) * t' = (n : ℂ) * t' + t' := by push_cast; ring
    rw [e1, e2]
    exact h2

/- English proof (translation)
Distinguish the cases in `h : t ∈ L.lattice`. Conclude with `⟨0, Or.inl ⟨h, L'.lattice.zero_mem⟩⟩`. Take `⟨hx, hy⟩` from `ht.resolve_left h`. Use `set X : M := ⟨_, hx⟩`. Use `set Y : M := ⟨_, hy⟩`.

Establish `curve : Y ^ 2 = 4 * X ^ 3 - ⟨_, hg2⟩ * X - ⟨_, hg3⟩` using `Subtype.ext (by`. Establish `e` using `L.derivWeierstrassP_sq t h`. Establish `h4 : ((4 : M) : ℂ) = 4` using `map_ofNat (algebraMap M ℂ) 4`. Move the coercions through the operations in `[X, Y, h4]`. Take the linear combination `e)`.

Establish `curve' : (ρ Y) ^ 2 = 4 * (ρ X) ^ 3 - L'.g₂ * ρ X - L'.g₃`. Rewrite using `[hg2', hg3']`. Use `congrArg ρ curve` as an intermediate fact. Simplify `this` using `[map_sub, map_mul, map_pow, map_ofNat]`. Take `⟨z, hz, e1, e2⟩` from `hO L' (ρ X) (ρ Y) curve'`.

Conclude with `⟨z, Or.inr ⟨h, hz, hx, hy, e1, e2⟩⟩`.
-/
theorem st_exists (hO : POnto) (hg2 : L.g₂ ∈ M) (hg3 : L.g₃ ∈ M)
    (hg2' : L'.g₂ = ρ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ ⟨_, hg3⟩) (t : ℂ)
    (ht : t ∈ L.lattice ∨ (L.weierstrassP t ∈ M ∧ L.derivWeierstrassP t ∈ M)) :
    ∃ t', St L L' M ρ t t' := by
  by_cases h : t ∈ L.lattice
  · exact ⟨0, Or.inl ⟨h, L'.lattice.zero_mem⟩⟩
  obtain ⟨hx, hy⟩ := ht.resolve_left h
  set X : M := ⟨_, hx⟩
  set Y : M := ⟨_, hy⟩
  have curve : Y ^ 2 = 4 * X ^ 3 - ⟨_, hg2⟩ * X - ⟨_, hg3⟩ :=
    Subtype.ext (by
      have e := L.derivWeierstrassP_sq t h
      have h4 : ((4 : M) : ℂ) = 4 := map_ofNat (algebraMap M ℂ) 4
      push_cast [X, Y, h4]
      linear_combination e)
  have curve' : (ρ Y) ^ 2 = 4 * (ρ X) ^ 3 - L'.g₂ * ρ X - L'.g₃ := by
    rw [hg2', hg3']
    have := congrArg ρ curve
    simpa [map_sub, map_mul, map_pow, map_ofNat] using this
  obtain ⟨z, hz, e1, e2⟩ := hO L' (ρ X) (ρ Y) curve'
  exact ⟨z, Or.inr ⟨h, hz, hx, hy, e1, e2⟩⟩

/- English proof (translation)
Distinguish the cases in `h0 : t' ∈ L'.lattice`. Conclude with `⟨0, by simpa using L.lattice.zero_mem, Or.inl ⟨L.lattice.zero_mem, h0⟩⟩`. Establish `hα : (n : ℂ) ≠ 0` using `by exact_mod_cast hn.ne'`. Establish `hst : ∀ K : PeriodPair, MulStable K (n : ℂ)`. Introduce `K ω hω`.

Establish `: (n : ℂ) * ω = (n : ℤ) • ω` using `by simp`. Rewrite using `[this]`. Conclude with `K.lattice.smul_mem _ hω`. Take `⟨S, hS⟩` from `kerRepsExist L (n : ℂ) hα (hst L)`. Take `⟨S', hS'⟩` from `kerRepsExist L' (n : ℂ) hα (hst L')`.

Establish `c1` using `kerRepsCard L (n : ℂ) S hα (hst L) hS`. Establish `c2` using `kerRepsCard L' (n : ℂ) S' hα (hst L') hS'`. Establish `hcard : S'.card = S.card`. Establish `: (S'.card : ℝ) = S.card` using `by linarith`. Conclude with `this` after adjusting the coercions.

Establish `key : ∀ P ∈ S, ∃ Q ∈ S', ∃ P', St L L' M ρ P P' ∧ P' - Q ∈ L'.lattice`. Introduce `P hP`. Take `⟨hnP, hPn⟩` from `hS.1 P hP`. Take `⟨P', hP'⟩` from `st_exists hO hg2 hg3 hg2' hg3' P (Or.inr (hM P hnP hPn))`. Establish `m1 : (n : ℂ) * P' ∈ L'.lattice` using `(st_mem_iff (st_nsmul hA hD hg2 hg2' hP' n)).1 hnP`.

Establish `m2 : P' ∉ L'.lattice` using `fun h => hPn ((st_mem_iff hP').2 h)`. Take `⟨Q, hQ, hQ'⟩` from `hS'.2.2 P' m1 m2`. Conclude with `⟨Q, hQ, P', hP', hQ'⟩`. Use `choose! g hgS f hf hfg using key`. Establish `hinj : Set.InjOn g S`.

Introduce `P hP P₁ hP₁ he`. Establish `d : f P - f P₁ ∈ L'.lattice`. Use `L'.lattice.sub_mem (hfg P hP) (hfg P₁ hP₁)` as an intermediate fact. Rewrite `this` using `[he, sub_sub_sub_cancel_right]`. Then use the resulting hypothesis. Establish `h1 : St L L' M ρ P₁ (f P)`.

Use `st_add_right (hf P₁ hP₁) d` as an intermediate fact. Rewrite `this` using `[show f P₁ + (f P - f P₁) = f P by ring]`. Then use the resulting hypothesis. Conclude with `hS.2.1 P hP P₁ hP₁ (st_inj (hf P hP) h1)`. Establish `hsub : S.image g ⊆ S'`. Introduce `Q hQ`.

Take `⟨P, hP, rfl⟩` from `Finset.mem_image.1 hQ`. Conclude with `hgS P hP`. Establish `heq : S.image g = S'` using `Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj, hcard])`. Take `⟨Q, hQ, hQ'⟩` from `hS'.2.2 t' ht' h0`. Rewrite `hQ` using `[← heq]`.

Take `⟨P, hP, rfl⟩` from `Finset.mem_image.1 hQ`. Use `⟨P, (hS.1 P hP).1, ?_⟩` and prove the remaining obligations. Establish `d : t' - f P ∈ L'.lattice`. Use `L'.lattice.sub_mem hQ' (hfg P hP)` as an intermediate fact. Rewrite `this` using `[sub_sub_sub_cancel_right]`. Then use the resulting hypothesis.

Use `st_add_right (hf P hP) d` as an intermediate fact. Rewrite `this` using `[show f P + (t' - f P) = t' by ring]`. Then use the resulting hypothesis.
-/
theorem st_onto (hA : AddLaw) (hD : DblLaw) (hO : POnto) (hg2 : L.g₂ ∈ M) (hg3 : L.g₃ ∈ M)
    (hg2' : L'.g₂ = ρ ⟨_, hg2⟩) (hg3' : L'.g₃ = ρ ⟨_, hg3⟩) (n : ℕ) (hn : 0 < n)
    (hM : ∀ t, (n : ℂ) * t ∈ L.lattice → t ∉ L.lattice →
      L.weierstrassP t ∈ M ∧ L.derivWeierstrassP t ∈ M)
    (t' : ℂ) (ht' : (n : ℂ) * t' ∈ L'.lattice) :
    ∃ t, (n : ℂ) * t ∈ L.lattice ∧ St L L' M ρ t t' := by
  by_cases h0 : t' ∈ L'.lattice
  · exact ⟨0, by simpa using L.lattice.zero_mem, Or.inl ⟨L.lattice.zero_mem, h0⟩⟩
  have hα : (n : ℂ) ≠ 0 := by exact_mod_cast hn.ne'
  have hst : ∀ K : PeriodPair, MulStable K (n : ℂ) := by
    intro K ω hω
    have : (n : ℂ) * ω = (n : ℤ) • ω := by simp
    rw [this]
    exact K.lattice.smul_mem _ hω
  obtain ⟨S, hS⟩ := kerRepsExist L (n : ℂ) hα (hst L)
  obtain ⟨S', hS'⟩ := kerRepsExist L' (n : ℂ) hα (hst L')
  have c1 := kerRepsCard L (n : ℂ) S hα (hst L) hS
  have c2 := kerRepsCard L' (n : ℂ) S' hα (hst L') hS'
  have hcard : S'.card = S.card := by
    have : (S'.card : ℝ) = S.card := by linarith
    exact_mod_cast this
  have key : ∀ P ∈ S, ∃ Q ∈ S', ∃ P', St L L' M ρ P P' ∧ P' - Q ∈ L'.lattice := by
    intro P hP
    obtain ⟨hnP, hPn⟩ := hS.1 P hP
    obtain ⟨P', hP'⟩ := st_exists hO hg2 hg3 hg2' hg3' P (Or.inr (hM P hnP hPn))
    have m1 : (n : ℂ) * P' ∈ L'.lattice :=
      (st_mem_iff (st_nsmul hA hD hg2 hg2' hP' n)).1 hnP
    have m2 : P' ∉ L'.lattice := fun h => hPn ((st_mem_iff hP').2 h)
    obtain ⟨Q, hQ, hQ'⟩ := hS'.2.2 P' m1 m2
    exact ⟨Q, hQ, P', hP', hQ'⟩
  choose! g hgS f hf hfg using key
  have hinj : Set.InjOn g S := by
    intro P hP P₁ hP₁ he
    have d : f P - f P₁ ∈ L'.lattice := by
      have := L'.lattice.sub_mem (hfg P hP) (hfg P₁ hP₁)
      rwa [he, sub_sub_sub_cancel_right] at this
    have h1 : St L L' M ρ P₁ (f P) := by
      have := st_add_right (hf P₁ hP₁) d
      rwa [show f P₁ + (f P - f P₁) = f P by ring] at this
    exact hS.2.1 P hP P₁ hP₁ (st_inj (hf P hP) h1)
  have hsub : S.image g ⊆ S' := by
    intro Q hQ
    obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQ
    exact hgS P hP
  have heq : S.image g = S' :=
    Finset.eq_of_subset_of_card_le hsub (by rw [Finset.card_image_of_injOn hinj, hcard])
  obtain ⟨Q, hQ, hQ'⟩ := hS'.2.2 t' ht' h0
  rw [← heq] at hQ
  obtain ⟨P, hP, rfl⟩ := Finset.mem_image.1 hQ
  refine ⟨P, (hS.1 P hP).1, ?_⟩
  have d : t' - f P ∈ L'.lattice := by
    have := L'.lattice.sub_mem hQ' (hfg P hP)
    rwa [sub_sub_sub_cancel_right] at this
  have := st_add_right (hf P hP) d
  rwa [show f P + (t' - f P) = t' by ring] at this

end rel

end PI.GalTorsConj.W

end
