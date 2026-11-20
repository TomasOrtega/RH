import Development.AutomorphicArithmetic.AutomorphicVarieties.GaloisLibrary.CrystallineBaseChange.RnStmt

namespace UpperTheory.V.Br

section

variable {V : Type} [AddCommGroup V] [Module ℂ V] {W R L : Module.End ℂ V} {H : V →ₗ⋆[ℂ] V →ₗ[ℂ] ℂ} {k : ℕ}

/- English proof (translation)
Establish `h` using `congrArg (fun f : Module.End ℂ V => f x) hL`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h`. Rewrite `h` using `[sub_eq_iff_eq_add]`. Rewrite using `[h]`. Use `push_cast`.

Use `module`.
-/
private theorem wt_low (hL : W * L - L * W = (-2 : ℂ) • L) {x : V} {n : ℤ} (hx : W x = (n : ℂ) • x) :
    W (L x) = ((n - 2 : ℤ) : ℂ) • L x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hL
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul] at h
  rw [sub_eq_iff_eq_add] at h
  rw [h]
  push_cast
  module

/- English proof (translation)
Establish `h` using `congrArg (fun f : Module.End ℂ V => f x) hC`. Simplify using `only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul, Module.End.one_apply] at h`. Establish `e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x)`. Rewrite using `[smul_smul]`. Evaluate the numerical expressions.

Rewrite using `[e, h]`. Use `push_cast`. Use `module`.
-/
private theorem cas (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W)) {x : V} {n : ℤ}
    (hx : W x = (n : ℂ) • x) :
    R (L x) = ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) • x := by
  have h := congrArg (fun f : Module.End ℂ V => f x) hC
  simp only [LinearMap.sub_apply, Module.End.mul_apply, LinearMap.smul_apply, hx, map_smul,
    Module.End.one_apply] at h
  have e : R (L x) = (1 / 4 : ℂ) • (4 : ℂ) • R (L x) := by
    rw [smul_smul]; norm_num
  rw [e, h]
  push_cast
  module

/- English proof (translation)
Assume the negation of the conclusion as `hlt`. Use `push_neg at hlt`. Establish `hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2)` using `by exact_mod_cast hlt`. Use `set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc`. Establish `hcpos : 0 < c` using `div_pos (by linarith) (by norm_num)`.

Establish `hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ)`. Rewrite using `[hc]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hwl` using `wt_low hL hx`.

Establish `h1 : H x (L x) = 0`. Establish `e` using `hW x (L x)`. Rewrite `e` using `[hx, hwl]`. Simplify using `[map_smulₛₗ] at e`. Break down `e with e | e` into its components or cases.

Establish `h2 : (2 : ℂ) = 0` using `by linear_combination e`. Evaluate the numerical expressions using `at h2`. Conclude with `e`. Establish `h2 : H (L x) x = 0`. Establish `e` using `hW (L x) x`.

Rewrite `e` using `[hwl, hx]`. Simplify using `[map_smulₛₗ] at e`. Conclude with `e`. Establish `h3 : H (L x) (L x) = -(c : ℂ) * H x x`. Establish `e` using `hH x (L x)`.

Rewrite `e` using `[cas hC hx, hcC]`. Simplify using `only [map_smul, smul_eq_mul] at e`. Rewrite using `[e]`. Expand and normalize the polynomial expressions, which then agree. Use `set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef`.

Establish `hs : (starRingEnd ℂ) s = s` using `Complex.conj_ofReal _`. Establish `hss : s * s = (c : ℂ)`. Rewrite using `[hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]`. Establish `hy : H (s • x + L x) (s • x + L x) = 0`. Simplify using `only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs, h1, h2, h3, RingHom.id_apply]`.

Put the polynomial expressions in normal form. Take the linear combination `(H x x) * hss`. Establish `hy0` using `h0 _ hy`. Establish `hLx : L x = -(s • x)` using `eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)`. Establish `e1 : W (L x) = -(s • ((n : ℂ) • x))` using `by rw [hLx, map_neg, map_smul, hx]`.

Rewrite `e1` using `[hwl, hLx]`. Establish `key : ((2 : ℂ) * s) • x = 0`. Establish `e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x)))` using `by push_cast; module`. Rewrite using `[e2, e1, sub_self]`. Break down `smul_eq_zero.mp key with h | h` into its components or cases.

Establish `hs0 : s = 0`. Break down `mul_eq_zero.mp h with h' | h'` into its components or cases. Evaluate the numerical expressions using `at h'`. Conclude with `h'`. Establish `hc0 : (c : ℂ) = 0` using `by rw [← hss, hs0, mul_zero]`.

Establish `: c = 0` using `by exact_mod_cast hc0`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `hx0 h`.
-/
private theorem bound (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    {x : V} (hx0 : x ≠ 0) {n : ℤ} (hx : W x = (n : ℂ) • x) : (k : ℤ) * (k - 2) ≤ n * (n - 2) := by
  by_contra hlt
  push_neg at hlt
  have hltR : (n : ℝ) * (n - 2) < (k : ℝ) * (k - 2) := by exact_mod_cast hlt
  set c : ℝ := ((k : ℝ) * (k - 2) - n * (n - 2)) / 4 with hc
  have hcpos : 0 < c := div_pos (by linarith) (by norm_num)
  have hcC : ((((k : ℤ) * (k - 2) - n * (n - 2) : ℤ) : ℂ) / 4) = (c : ℂ) := by
    rw [hc]; push_cast; ring
  have hwl := wt_low hL hx
  have h1 : H x (L x) = 0 := by
    have e := hW x (L x)
    rw [hx, hwl] at e
    simp [map_smulₛₗ] at e
    rcases e with e | e
    · have h2 : (2 : ℂ) = 0 := by linear_combination e
      norm_num at h2
    · exact e
  have h2 : H (L x) x = 0 := by
    have e := hW (L x) x
    rw [hwl, hx] at e
    simp [map_smulₛₗ] at e
    exact e
  have h3 : H (L x) (L x) = -(c : ℂ) * H x x := by
    have e := hH x (L x)
    rw [cas hC hx, hcC] at e
    simp only [map_smul, smul_eq_mul] at e
    rw [e]; ring
  set s : ℂ := ((Real.sqrt c : ℝ) : ℂ) with hsdef
  have hs : (starRingEnd ℂ) s = s := Complex.conj_ofReal _
  have hss : s * s = (c : ℂ) := by
    rw [hsdef, ← Complex.ofReal_mul, Real.mul_self_sqrt hcpos.le]
  have hy : H (s • x + L x) (s • x + L x) = 0 := by
    simp only [map_add, LinearMap.add_apply, map_smulₛₗ, LinearMap.smul_apply, map_smul, smul_eq_mul, hs,
      h1, h2, h3, RingHom.id_apply]
    ring_nf
    linear_combination (H x x) * hss
  have hy0 := h0 _ hy
  have hLx : L x = -(s • x) := eq_neg_iff_add_eq_zero.mpr (by rw [add_comm]; exact hy0)
  have e1 : W (L x) = -(s • ((n : ℂ) • x)) := by rw [hLx, map_neg, map_smul, hx]
  rw [hwl, hLx] at e1
  have key : ((2 : ℂ) * s) • x = 0 := by
    have e2 : ((2 : ℂ) * s) • x = (((n - 2 : ℤ) : ℂ) • -(s • x)) - (-(s • ((n : ℂ) • x))) := by
      push_cast; module
    rw [e2, e1, sub_self]
  rcases smul_eq_zero.mp key with h | h
  · have hs0 : s = 0 := by
      rcases mul_eq_zero.mp h with h' | h'
      · norm_num at h'
      · exact h'
    have hc0 : (c : ℂ) = 0 := by rw [← hss, hs0, mul_zero]
    have : c = 0 := by exact_mod_cast hc0
    linarith
  · exact hx0 h

/- English proof (translation)
Proceed by induction on `j using Nat.strong_induction_on with`. Consider the case `_ j ih`. Introduce `x hx0 hx`. Establish `hb` using `bound hL hC h0 hW hH hx0 hx`. Establish `hk' : (3 : ℤ) ≤ k` using `by exact_mod_cast hk`.

Establish `hj2 : 2 ≤ j`. Assume the negation of the conclusion as `h`. Use `push_neg at h`. Apply the tactic sequence `interval_cases j <;> (push_cast at hb; nlinarith)`. Distinguish the cases in `hL0 : L x = 0`.

Use `⟨x, hx0, ?_, hL0⟩` and prove the remaining obligations. Establish `hc` using `cas hC hx`. Rewrite `hc` using `[hL0, map_zero]`. Establish `hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0`. Break down `smul_eq_zero.mp hc.symm with h | h` into its components or cases.

Conclude with `h`. Conclude with `absurd h hx0`. Establish `hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0`. Establish `h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0`. Take the linear combination `4 * hq`.

Conclude with `h4` after adjusting the coercions. Establish `hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0` using `by linear_combination hq'`. Establish `hjk : j = k`. Break down `mul_eq_zero.mp hf with h | h` into its components or cases. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Rewrite using `[hx, hjk]`. Simplify using the standard rewrite rules. Establish `hwl` using `wt_low hL hx`. Use `ih (j - 2) (by omega) (L x) hL0 ?_` and prove the remaining obligations.

Rewrite using `[hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]`.
-/
private theorem descend (hk : 3 ≤ k) (hL : W * L - L * W = (-2 : ℂ) • L)
    (hC : (4 : ℂ) • (R * L) = ((k : ℂ) * (k - 2)) • 1 - (W * W - (2 : ℂ) • W))
    (h0 : ∀ x, H x x = 0 → x = 0) (hW : ∀ x y, H (W x) y = H x (W y)) (hH : ∀ x y, H (L x) y = -H x (R y))
    (j : ℕ) : ∀ x : V, x ≠ 0 → W x = ((j : ℤ) : ℂ) • x → ∃ x, x ≠ 0 ∧ W x = (k : ℂ) • x ∧ L x = 0 := by
  induction j using Nat.strong_induction_on with
  | _ j ih =>
  intro x hx0 hx
  have hb := bound hL hC h0 hW hH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hj2 : 2 ≤ j := by
    by_contra h
    push_neg at h
    interval_cases j <;> (push_cast at hb; nlinarith)
  by_cases hL0 : L x = 0
  · refine ⟨x, hx0, ?_, hL0⟩
    have hc := cas hC hx
    rw [hL0, map_zero] at hc
    have hq : ((((k : ℤ) * (k - 2) - ((j : ℤ) : ℤ) * ((j : ℤ) - 2) : ℤ)) : ℂ) / 4 = 0 := by
      rcases smul_eq_zero.mp hc.symm with h | h
      · exact h
      · exact absurd h hx0
    have hq' : (k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) = 0 := by
      have h4 : (((k : ℤ) * (k - 2) - (j : ℤ) * ((j : ℤ) - 2) : ℤ) : ℂ) = 0 := by
        linear_combination 4 * hq
      exact_mod_cast h4
    have hf : ((k : ℤ) - j) * ((k : ℤ) + j - 2) = 0 := by linear_combination hq'
    have hjk : j = k := by
      rcases mul_eq_zero.mp hf with h | h
      · omega
      · omega
    rw [hx, hjk]
    simp
  · have hwl := wt_low hL hx
    refine ih (j - 2) (by omega) (L x) hL0 ?_
    rw [hwl, show ((j - 2 : ℕ) : ℤ) = (j : ℤ) - 2 by omega]

end

/- English proof (translation)
Introduce `V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex`. Take `⟨x, hx0, n, hx⟩` from `hex`. Establish `hb` using `bound hL hC h0 hW hLH hx0 hx`. Establish `hk' : (3 : ℤ) ≤ k` using `by exact_mod_cast hk`. Establish `hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2)` using `by ring`.

Break down `le_or_gt (k : ℤ) n with hn | hn` into its components or cases. Take `⟨j, rfl⟩ : ∃ j : ℕ, n = j` from `⟨n.toNat, by omega⟩`. Take `⟨y, hy0, hy1, hy2⟩` from `descend hk hL hC h0 hW hLH j x hx0 hx`. Conclude with `⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩`. Establish `hn2 : n + k - 2 ≤ 0` using `by nlinarith`.

Take `⟨j, hj⟩ : ∃ j : ℕ, -n = j` from `⟨(-n).toNat, by omega⟩`. Establish `hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R`. Rewrite using `[show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]`. Use `module`. Establish `hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W))`.

Rewrite using `[hC']`. Use `congr 1`. Rewrite using `[neg_mul_neg, smul_neg, sub_neg_eq_add]`. Establish `hW' : ∀ a b, H ((-W) a) b = H a ((-W) b)`. Introduce `a b`.

Simplify using `only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]`. Establish `hx' : (-W) x = ((j : ℤ) : ℂ) • x`. Rewrite using `[LinearMap.neg_apply, hx, ← neg_smul, ← hj]`. Use `push_cast`. Both sides reduce to the same expression.

Take `⟨y, hy0, hy1, hy2⟩` from `descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'`. Use `⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩` and prove the remaining obligations. Rewrite using `[neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]`.
-/
theorem sl2Low : UpperTheory.V.Br.Sl2Low := by
  intro V _ _ W R L H k hk hR hL hC hC' h0 hW hRH hLH hex
  obtain ⟨x, hx0, n, hx⟩ := hex
  have hb := bound hL hC h0 hW hLH hx0 hx
  have hk' : (3 : ℤ) ≤ k := by exact_mod_cast hk
  have hf : (n - k) * (n + k - 2) = n * (n - 2) - k * (k - 2) := by ring
  rcases le_or_gt (k : ℤ) n with hn | hn
  · obtain ⟨j, rfl⟩ : ∃ j : ℕ, n = j := ⟨n.toNat, by omega⟩
    obtain ⟨y, hy0, hy1, hy2⟩ := descend hk hL hC h0 hW hLH j x hx0 hx
    exact ⟨y, hy0, Or.inl ⟨hy1, hy2⟩⟩
  · have hn2 : n + k - 2 ≤ 0 := by nlinarith
    obtain ⟨j, hj⟩ : ∃ j : ℕ, -n = j := ⟨(-n).toNat, by omega⟩
    have hL' : (-W) * R - R * (-W) = (-2 : ℂ) • R := by
      rw [show (-W) * R - R * (-W) = -(W * R - R * W) by noncomm_ring, hR]
      module
    have hC2 : (4 : ℂ) • (L * R) = ((k : ℂ) * (k - 2)) • 1 - ((-W) * (-W) - (2 : ℂ) • (-W)) := by
      rw [hC']
      congr 1
      rw [neg_mul_neg, smul_neg, sub_neg_eq_add]
    have hW' : ∀ a b, H ((-W) a) b = H a ((-W) b) := by
      intro a b
      simp only [LinearMap.neg_apply, map_neg, LinearMap.neg_apply, hW]
    have hx' : (-W) x = ((j : ℤ) : ℂ) • x := by
      rw [LinearMap.neg_apply, hx, ← neg_smul, ← hj]
      push_cast
      rfl
    obtain ⟨y, hy0, hy1, hy2⟩ :=
      descend (W := -W) (R := L) (L := R) (H := H) hk hL' hC2 h0 hW' hRH j x hx0 hx'
    refine ⟨y, hy0, Or.inr ⟨?_, hy2⟩⟩
    rw [neg_smul, ← hy1, LinearMap.neg_apply, neg_neg]

end UpperTheory.V.Br
