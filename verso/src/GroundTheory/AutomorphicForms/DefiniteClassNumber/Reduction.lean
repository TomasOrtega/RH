import Mathlib

noncomputable section

namespace GroundTheory.Automorphic

open Module Submodule
open scoped RealInnerProductSpace

universe u

section Dual

variable {X : Type*} [NormedAddCommGroup X] [InnerProductSpace ℝ X]

def latticeDual (L : AddSubgroup X) : AddSubgroup X where
  carrier := {y | ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n}
  zero_mem' := fun _ _ => ⟨0, by simp⟩
  add_mem' := fun {a b} ha hb x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    obtain ⟨n, hn⟩ := hb x hx
    exact ⟨m + n, by rw [inner_add_left, hm, hn]; push_cast; ring⟩
  neg_mem' := fun {a} ha x hx => by
    obtain ⟨m, hm⟩ := ha x hx
    exact ⟨-m, by rw [inner_neg_left, hm]; push_cast; ring⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_latticeDual {L : AddSubgroup X} {y : X} :
    y ∈ latticeDual L ↔ ∀ x ∈ L, ∃ n : ℤ, ⟪y, x⟫ = n := Iff.rfl

/- English proof (translation)
Establish `hle : span ℝ s ≤ LinearMap.ker (innerSL ℝ y).toLinearMap` using `span_le.2 fun x hx => by simpa using hy x hx`. Establish `hy' : y ∈ LinearMap.ker (innerSL ℝ y).toLinearMap` using `hle (hs ▸ mem_top)`. Simplify using `using hy'`.
-/
theorem eq_zero_of_forall_inner_eq_zero {s : Set X} (hs : span ℝ s = ⊤) {y : X}
    (hy : ∀ x ∈ s, ⟪y, x⟫ = 0) : y = 0 := by
  have hle : span ℝ s ≤ LinearMap.ker (innerSL ℝ y).toLinearMap :=
    span_le.2 fun x hx => by simpa using hy x hx
  have hy' : y ∈ LinearMap.ker (innerSL ℝ y).toLinearMap := hle (hs ▸ mem_top)
  simpa using hy'

/- English proof (translation)
Take `⟨s, hsL, hspan, hli⟩` from `exists_linearIndependent ℝ (L : Set X)`. Rewrite `hspan` using `[hL]`. Establish `hsfin : s.Finite` using `hli.setFinite`. Establish `: Finite s` using `hsfin.to_subtype`. Set `Φ : X → s → ℝ` to `fun y x => ⟪y, (x : X)⟫`.

Establish `hinj : Set.InjOn Φ {y | y ∈ latticeDual L ∧ ‖y‖ ≤ C}`. Introduce `y _ y' _ h`. Establish `: y - y' = 0` using `eq_zero_of_forall_inner_eq_zero hspan fun x hx => by`. Use `congrFun h ⟨x, hx⟩` as an intermediate fact. Simplify using `only [Φ] at this`.

Rewrite using `[inner_sub_left, this, sub_self]`. Conclude with `sub_eq_zero.1 this`. Use `Set.Finite.of_finite_image (Set.Finite.subset (Set.Finite.pi (t := fun x : s => (Int.cast '' Set.Icc (-⌈C * ‖(x : X)‖⌉) ⌈C * ‖(x : X)‖⌉ : Set ℝ)) fun x => (Set.finite_Icc _ _).image _) ?_) hinj` and prove the remaining obligations. Introduce and unpack `_ ⟨y, ⟨hyD, hyC⟩, rfl⟩`. Simplify using `only [Set.mem_pi, Set.mem_univ, true_implies]`.

Introduce `x`. Take `⟨n, hn⟩` from `hyD x (hsL x.2)`. Use `⟨n, ⟨?_, ?_⟩, hn.symm⟩` and prove the remaining obligations. Use `all_goals`. Establish `h1 : |(n : ℝ)| ≤ C * ‖(x : X)‖`.

Rewrite using `[← hn]`. Conclude with `(abs_real_inner_le_norm y x).trans (mul_le_mul_of_nonneg_right hyC (norm_nonneg _))`. Establish `h2 : C * ‖(x : X)‖ ≤ ⌈C * ‖(x : X)‖⌉` using `Int.le_ceil _`. Establish `: -((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) ≤ n` using `by linarith [neg_abs_le (n : ℝ)]`. Conclude with `this` after adjusting the coercions.

Establish `: (n : ℝ) ≤ ((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ)` using `by linarith [le_abs_self (n : ℝ)]`. Conclude with `this` after adjusting the coercions.
-/
theorem finite_latticeDual_norm_le [FiniteDimensional ℝ X] {L : AddSubgroup X}
    (hL : span ℝ (L : Set X) = ⊤) (C : ℝ) :
    ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} : Set X).Finite := by
  obtain ⟨s, hsL, hspan, hli⟩ := exists_linearIndependent ℝ (L : Set X)
  rw [hL] at hspan
  have hsfin : s.Finite := hli.setFinite
  have : Finite s := hsfin.to_subtype
  let Φ : X → s → ℝ := fun y x => ⟪y, (x : X)⟫
  have hinj : Set.InjOn Φ {y | y ∈ latticeDual L ∧ ‖y‖ ≤ C} := by
    intro y _ y' _ h
    have : y - y' = 0 := eq_zero_of_forall_inner_eq_zero hspan fun x hx => by
      have := congrFun h ⟨x, hx⟩
      simp only [Φ] at this
      rw [inner_sub_left, this, sub_self]
    exact sub_eq_zero.1 this
  refine Set.Finite.of_finite_image (Set.Finite.subset (Set.Finite.pi (t := fun x : s =>
    (Int.cast '' Set.Icc (-⌈C * ‖(x : X)‖⌉) ⌈C * ‖(x : X)‖⌉ : Set ℝ))
    fun x => (Set.finite_Icc _ _).image _) ?_) hinj
  rintro _ ⟨y, ⟨hyD, hyC⟩, rfl⟩
  simp only [Set.mem_pi, Set.mem_univ, true_implies]
  intro x
  obtain ⟨n, hn⟩ := hyD x (hsL x.2)
  refine ⟨n, ⟨?_, ?_⟩, hn.symm⟩
  all_goals
    have h1 : |(n : ℝ)| ≤ C * ‖(x : X)‖ := by
      rw [← hn]
      exact (abs_real_inner_le_norm y x).trans
        (mul_le_mul_of_nonneg_right hyC (norm_nonneg _))
    have h2 : C * ‖(x : X)‖ ≤ ⌈C * ‖(x : X)‖⌉ := Int.le_ceil _
  · have : -((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) ≤ n := by linarith [neg_abs_le (n : ℝ)]
    exact_mod_cast this
  · have : (n : ℝ) ≤ ((⌈C * ‖(x : X)‖⌉ : ℤ) : ℝ) := by linarith [le_abs_self (n : ℝ)]
    exact_mod_cast this

end Dual

def shortBasisBound : ℕ → ℝ → ℝ
  | 0, _ => 0
  | N + 1, μ => N * shortBasisBound N (Real.sqrt 3 / 2 * μ) + μ⁻¹

/- English proof (translation)
The claim follows from `| 0, _, _ => le_rfl | N + 1, μ, hμ => by have h3 : 0 < Real.sqrt 3 / 2 * μ := by positivity have := shortBasisBound_nonneg N h3 simp only [shortBasisBound] positivity`.
-/
theorem shortBasisBound_nonneg : ∀ (N : ℕ) {μ : ℝ}, 0 < μ → 0 ≤ shortBasisBound N μ
  | 0, _, _ => le_rfl
  | N + 1, μ, hμ => by
    have h3 : 0 < Real.sqrt 3 / 2 * μ := by positivity
    have := shortBasisBound_nonneg N h3
    simp only [shortBasisBound]
    positivity

section Reduction

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero`. Introduce `X _ _ _ _ L μ _ _ _ _`. Conclude with `⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩`. Consider the case `succ N ih`.

Introduce `X _ _ _ hdim L μ hμ hLspan hDspan hmin`. Establish `: Nontrivial X` using `nontrivial_of_finrank_eq_succ hdim`. Choose the witnesses or unpack the hypotheses as in `⟨y0, hy0, hy0ne⟩ : ∃ y ∈ latticeDual L, y ≠ 0 := by`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Establish `hsub : (latticeDual L : Set X) ⊆ {0}` using `fun y hy => h y hy`. Establish `hle` using `span_mono (R := ℝ) hsub`. Rewrite `hle` using `[hDspan, span_singleton_eq_bot.2 rfl]`. Conclude with `top_ne_bot (eq_bot_iff.2 hle)`. Take `⟨w, ⟨⟨hwD, -⟩, hw0⟩, hwmin⟩` from `Set.exists_min_image ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ ‖y0‖} ∩ {y | y ≠ 0}) (fun y => ‖y‖) ((finite_latticeDual_norm_le hLspan ‖y0‖).subset Set.inter_subset_left) ⟨y0, ⟨hy0, le_rfl⟩, hy0ne⟩`.

Establish `hwmin' : ∀ y ∈ latticeDual L, y ≠ 0 → ‖w‖ ≤ ‖y‖`. Introduce `y hy hyne`. Distinguish the cases in `h : ‖y‖ ≤ ‖y0‖`. Conclude with `hwmin y ⟨⟨hy, h⟩, hyne⟩`. Conclude with `(hwmin y0 ⟨⟨hy0, le_rfl⟩, hy0ne⟩).trans (le_of_not_ge h)`.

Establish `hwμ : μ ≤ ‖w‖` using `hmin w hwD hw0`. Establish `hwpos : 0 < ‖w‖` using `norm_pos_iff.2 hw0`. Establish `hx1 : ∃ x ∈ L, ⟪w, x⟫ ≠ 0`. Assume the negation of the conclusion as `h`. Use `push Not at h`.

Conclude with `hw0 (eq_zero_of_forall_inner_eq_zero hLspan h)`. Establish `hex : ∃ n : ℕ, 0 < n ∧ ∃ x ∈ L, ⟪w, x⟫ = n`. Take `⟨x1, hx1L, hx1⟩` from `hx1`. Take `⟨m, hm⟩` from `hwD x1 hx1L`. Establish `hm0 : m ≠ 0` using `by rintro rfl; exact hx1 (by simpa using hm)`.

Break down `lt_or_gt_of_ne hm0 with hneg | hpos` into its components or cases. Use `⟨m.natAbs, Int.natAbs_pos.2 hm0, -x1, neg_mem hx1L, ?_⟩` and prove the remaining obligations. Rewrite using `[inner_neg_right, hm, Nat.cast_natAbs, Int.cast_abs, abs_of_neg (by exact_mod_cast hneg)]`. Use `⟨m.natAbs, Int.natAbs_pos.2 hm0, x1, hx1L, ?_⟩` and prove the remaining obligations. Rewrite using `[hm, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]`.

Take `⟨hn0pos, x0, hx0L, hx0⟩` from `Nat.find_spec hex`. Establish `hdiv : ∀ x ∈ L, ∃ q : ℤ, ⟪w, x⟫ = q * (Nat.find hex : ℝ)`. Introduce `x hx`. Take `⟨m, hm⟩` from `hwD x hx`. Use `set n0 := Nat.find hex`.

Establish `hn0z : (0 : ℤ) < n0` using `by exact_mod_cast hn0pos`. Use `set r := m % (n0 : ℤ)`. Establish `hr0 : 0 ≤ r` using `Int.emod_nonneg _ hn0z.ne'`. Establish `hrlt : r < n0` using `Int.emod_lt_of_pos _ hn0z`. Establish `hmr : m = r + n0 * (m / n0)` using `(Int.emod_add_mul_ediv m n0).symm`.

Establish `hxr : x - (m / (n0 : ℤ)) • x0 ∈ L` using `sub_mem hx (zsmul_mem hx0L _)`. Establish `hval : ⟪w, x - (m / (n0 : ℤ)) • x0⟫ = r`. Rewrite using `[inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hm, hx0]`. Establish `: (m : ℝ) = r + n0 * (m / (n0 : ℤ) : ℤ)` using `by exact_mod_cast hmr`. Rewrite using `[this]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hr : r = 0`. Assume the negation of the conclusion as `hrne`. Establish `hrpos : 0 < r` using `lt_of_le_of_ne hr0 (Ne.symm hrne)`. Use `Nat.find_min hex (m := r.toNat) (by omega)` as an intermediate fact.

Apply `this` to reduce the goal to its premises. Use `⟨by omega, _, hxr, ?_⟩` and prove the remaining obligations. Rewrite using `[hval]`. Establish `: ((r.toNat : ℤ) : ℝ) = r` using `by rw [Int.toNat_of_nonneg hr0]`. Rewrite using `[← this]`.

Use `norm_cast`. Use `⟨m / n0, ?_⟩` and prove the remaining obligations. Establish `hm' : m = (m / n0) * n0` using `by rw [hr] at hmr; linarith`. Rewrite using `[hm]`. Conclude with `hm'` after adjusting the coercions.

Establish `hn0 : Nat.find hex = 1`. Assume the negation of the conclusion as `hne`. Establish `hge : (2 : ℝ) ≤ Nat.find hex`. Establish `: 2 ≤ Nat.find hex` using `by omega`. Conclude with `this` after adjusting the coercions.

Use `set n0 := Nat.find hex`. Establish `hw'D : (n0 : ℝ)⁻¹ • w ∈ latticeDual L`. Introduce `x hx`. Take `⟨q, hq⟩` from `hdiv x hx`. Use `⟨q, ?_⟩` and prove the remaining obligations.

Rewrite using `[real_inner_smul_left, hq]`. Clear the denominators using the available nonvanishing facts. Establish `hw'0 : (n0 : ℝ)⁻¹ • w ≠ 0` using `smul_ne_zero (inv_ne_zero (by linarith)) hw0`. Establish `h1` using `hwmin' _ hw'D hw'0`. Rewrite `h1` using `[norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)]`.

Establish `: (n0 : ℝ)⁻¹ * ‖w‖ < ‖w‖`. Establish `: (n0 : ℝ)⁻¹ ≤ 1 / 2` using `by rw [inv_eq_one_div]; gcongr`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite `hx0` using `[hn0, Nat.cast_one]`.

Establish `: Fact (finrank ℝ X = N + 1)` using `⟨hdim⟩`. Use `set W : Submodule ℝ X := (ℝ ∙ w)ᗮ with hWdef`. Establish `hWdim : finrank ℝ W = N` using `finrank_orthogonal_span_singleton hw0`. Establish `memW : ∀ z : X, z ∈ W ↔ ⟪w, z⟫ = 0` using `fun z => mem_orthogonal_singleton_iff_inner_right`. Set `M : AddSubgroup W` to `L.comap W.subtype.toAddMonoidHom`.

Establish `memM : ∀ m : W, m ∈ M ↔ (m : X) ∈ L` using `fun m => Iff.rfl`. Set `P : X →ₗ[ℝ] W` to `{ toFun := fun x => ⟨x - ⟪w, x⟫ • x0, by`. Rewrite using `[memW, inner_sub_right, real_inner_smul_right, hx0]`. Use the proof step `ring⟩`. Use the proof step `map_add' := fun x y => by ext; simp only [inner_add_right, add_smul, coe_add]; abel`.

Use the proof step `map_smul' := fun c x => by ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_smul] }`. Establish `hP : ∀ x, (P x : X) = x - ⟪w, x⟫ • x0` using `fun _ => rfl`. Establish `hPL : ∀ x ∈ L, P x ∈ M`. Introduce `x hx`. Take `⟨n, hn⟩` from `hwD x hx`.

Rewrite using `[memM, hP, hn, Int.cast_smul_eq_zsmul]`. Conclude with `sub_mem hx (zsmul_mem hx0L _)`. Establish `hPW : ∀ z : W, P z = z`. Introduce `z`. Use `ext`.

Rewrite using `[hP, (memW z).1 z.2, zero_smul, sub_zero]`. Establish `hPsurj : LinearMap.range P = ⊤` using `LinearMap.range_eq_top.2 fun z => ⟨z, hPW z⟩`. Establish `hMspan : span ℝ (M : Set W) = ⊤`. Apply `eq_top_iff.2` to reduce the goal to its premises. Rewrite using `[← hPsurj, LinearMap.range_eq_map, ← hLspan, ← span_image]`.

Conclude with `span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hPL x hx)`. Set `π : X →ₗ[ℝ] W` to `{ toFun := fun z => ⟨z - (⟪w, z⟫ / ‖w‖ ^ 2) • w, by`. Rewrite using `[memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring⟩`.

Use the proof step `map_add' := fun x y => by ext; simp only [inner_add_right, add_div, add_smul, coe_add]; abel`. Use the proof step `map_smul' := fun c x => by ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_div_assoc, mul_smul] }`. Establish `hπ : ∀ z, (π z : X) = z - (⟪w, z⟫ / ‖w‖ ^ 2) • w` using `fun _ => rfl`. Establish `hπW : ∀ z : W, π z = z`. Introduce `z`.

Use `ext`. Rewrite using `[hπ, (memW z).1 z.2, zero_div, zero_smul, sub_zero]`. Establish `hπD : ∀ z ∈ latticeDual L, π z ∈ latticeDual M`. Introduce `z hz m hm`. Take `⟨n, hn⟩` from `hz m hm`.

Use `⟨n, ?_⟩` and prove the remaining obligations. Rewrite using `[coe_inner, hπ, inner_sub_left, real_inner_smul_left, (memW m).1 m.2, mul_zero, sub_zero, hn]`. Establish `hMDspan : span ℝ (latticeDual M : Set W) = ⊤`. Apply `eq_top_iff.2` to reduce the goal to its premises. Establish `hπsurj : LinearMap.range π = ⊤` using `LinearMap.range_eq_top.2 fun z => ⟨z, hπW z⟩`.

Rewrite using `[← hπsurj, LinearMap.range_eq_map, ← hDspan, ← span_image]`. Conclude with `span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hπD x hx)`. Establish `hMmin : ∀ y ∈ latticeDual M, y ≠ 0 → Real.sqrt 3 / 2 * μ ≤ ‖y‖`. Introduce `y hy hyne`. Establish `hyw : ⟪(y : X), w⟫ = 0` using `by rw [real_inner_comm]; exact (memW y).1 y.2`.

Use `set c := ⟪(y : X), x0⟫`. Use `set s : ℝ := (round c : ℝ) - c`. Establish `hs : |s| ≤ 1 / 2` using `by rw [abs_sub_comm]; exact abs_sub_round c`. Use `set z := (y : X) + s • w`. Establish `hzD : z ∈ latticeDual L`.

Introduce `x hx`. Take `⟨n, hn⟩` from `hwD x hx`. Take `⟨k, hk⟩` from `hy (P x) (hPL x hx)`. Use `⟨k + round c * n, ?_⟩` and prove the remaining obligations. Rewrite `hk` using `[coe_inner, hP, inner_sub_right, real_inner_smul_right, hn]`.

Rewrite using `[inner_add_left, real_inner_smul_left, hn]`. Use `push_cast`. Simplify using `only [s]`. Take the linear combination `hk`. Establish `hz0 : z ≠ 0`.

Introduce `h`. Establish `: ⟪(y : X), z⟫ = ‖(y : X)‖ ^ 2`. Rewrite using `[inner_add_right, real_inner_smul_right, hyw, mul_zero, add_zero, real_inner_self_eq_norm_sq]`. Rewrite `this` using `[h, inner_zero_right]`. Establish `hy0 : (y : X) = 0`.

Establish `: ‖(y : X)‖ = 0` using `by nlinarith [norm_nonneg (y : X)]`. Conclude with `norm_eq_zero.1 this`. Conclude with `hyne (Subtype.ext hy0)`. Establish `hz` using `hwmin' z hzD hz0`. Establish `hzn : ‖z‖ ^ 2 = ‖(y : X)‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2`.

Rewrite using `[norm_add_sq_real, real_inner_smul_right, hyw, norm_smul, Real.norm_eq_abs, mul_pow, sq_abs]`. Expand and normalize the polynomial expressions, which then agree. Establish `hs2 : s ^ 2 ≤ 1 / 4`. Use `abs_le.1 hs` as an intermediate fact. Use the polynomial consequences of the given equalities and inequalities.

Establish `hsq : (Real.sqrt 3 / 2 * μ) ^ 2 ≤ ‖y‖ ^ 2`. Establish `h3 : Real.sqrt 3 ^ 2 = 3` using `Real.sq_sqrt (by norm_num)`. Establish `hw2 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2` using `pow_le_pow_left₀ (norm_nonneg _) hz 2`. Establish `hμ2 : μ ^ 2 ≤ ‖w‖ ^ 2` using `pow_le_pow_left₀ hμ.le hwμ 2`. Establish `: ‖y‖ = ‖(y : X)‖` using `rfl`.

Rewrite using `[mul_pow, div_pow, h3, this]`. Use the polynomial consequences of the given equalities and inequalities. Conclude with `le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _) |>.trans_eq' rfl`. Take `⟨e', hli', he'⟩` from `ih (X := W) hWdim M (Real.sqrt 3 / 2 * μ) (by positivity) hMspan hMDspan hMmin`. Use `set R' := shortBasisBound N (Real.sqrt 3 / 2 * μ)`.

Establish `hR' : 0 ≤ R'` using `shortBasisBound_nonneg N (by positivity)`. Establish `hspan' : ⊤ ≤ span ℝ (Set.range e')`. Break down `Nat.eq_zero_or_pos N with hN | hN` into its components or cases. Substitute `hN` using the available equality. Establish `: Subsingleton W` using `finrank_zero_iff.1 hWdim`.

Introduce `z _`. Rewrite using `[Subsingleton.elim z 0]`. Conclude with `zero_mem _`. Establish `: Nonempty (Fin N)` using `⟨⟨0, hN⟩⟩`. Conclude with `(hli'.span_eq_top_of_card_eq_finrank (by simp [hWdim])).ge`.

Set `B` to `Basis.mk hli' hspan'`. Use `set q : W := ⟨x0 - (‖w‖ ^ 2)⁻¹ • w, by`. Rewrite using `[memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx0]`. Clear the denominators using the available nonvanishing facts. Use the proof step `ring⟩`.

Use `set c := B.repr q`. Use `set x0' := x0 - ∑ i, ⌊c i⌋ • (e' i : X)`. Establish `hx0'L : x0' ∈ L` using `sub_mem hx0L (sum_mem fun i _ => zsmul_mem (he' i).1 _)`. Establish `hq : (q : X) = ∑ i, c i • (e' i : X)` using `by conv_lhs => rw [← B.sum_repr q]`. Rewrite using `[coe_sum]`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coe_smul, Basis.mk_apply]`. Establish `hx0'eq : x0' = ∑ i, Int.fract (c i) • (e' i : X) + (‖w‖ ^ 2)⁻¹ • w`. Establish `hx0q : x0 = (q : X) + (‖w‖ ^ 2)⁻¹ • w` using `by simp [q]`. Simplify using `only [x0']`.

Rewrite using `[hx0q, hq]`. Establish `: ∀ i, Int.fract (c i) • (e' i : X) = c i • (e' i : X) - ⌊c i⌋ • (e' i : X)`. Introduce `i`. Rewrite using `[Int.fract, sub_smul, Int.cast_smul_eq_zsmul]`. Simplify using `only [this, Finset.sum_sub_distrib]`.

Normalize the expressions using the abelian group laws. Establish `hx0'norm : ‖x0'‖ ≤ N * R' + μ⁻¹`. Rewrite using `[hx0'eq]`. Use `(norm_add_le _ _).trans (add_le_add ?_ ?_)` and prove the remaining obligations. Use `(norm_sum_le _ _).trans ?_` and prove the remaining obligations.

Establish `: ∀ i, ‖Int.fract (c i) • (e' i : X)‖ ≤ R'`. Introduce `i`. Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]`. Establish `h1` using `(he' i).2`. Establish `h2` using `(Int.fract_lt_one (c i)).le`.

Establish `: ‖(e' i : X)‖ = ‖e' i‖` using `rfl`. Rewrite using `[this]`. Use polynomial arithmetic with `[norm_nonneg (e' i), Int.fract_nonneg (c i)]`. Use `(Finset.sum_le_sum fun i _ => this i).trans ?_` and prove the remaining obligations. Simplify using the standard rewrite rules.

Rewrite using `[norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), sq, mul_inv, mul_assoc, inv_mul_cancel₀ hwpos.ne', mul_one]`. Conclude with `inv_anti₀ hμ hwμ`. Establish `hx0'w : ⟪w, x0'⟫ = 1`. Simplify using `only [x0', inner_sub_right, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]`. Rewrite using `[hx0]`.

Establish `: ∀ i, ⟪w, (e' i : X)⟫ = 0` using `fun i => (memW _).1 (e' i).2`. Simplify using `[this]`. Use `⟨Fin.cons x0' fun i => (e' i : X), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[linearIndependent_finCons]`. Use `⟨hli'.map' W.subtype (ker_subtype W), ?_⟩` and prove the remaining obligations.

Introduce `hmem`. Establish `hle : span ℝ (Set.range fun i => (e' i : X)) ≤ W` using `span_le.2 (by rintro _ ⟨i, rfl⟩; exact (e' i).2)`. Use `(memW _).1 (hle hmem)` as an intermediate fact. Rewrite `this` using `[hx0'w]`. Conclude with `one_ne_zero this`.

Introduce `i`. Use `Fin.cases ?_ (fun j => ?_) i` and prove the remaining obligations. Conclude with `⟨hx0'L, by simpa [shortBasisBound] using hx0'norm⟩`. Use `⟨(he' j).1, ?_⟩` and prove the remaining obligations. Simplify using `only [Fin.cons_succ, shortBasisBound]`.

Establish `h1 : ‖(e' j : X)‖ ≤ R'` using `(he' j).2`. Establish `hN1 : (1 : ℝ) ≤ N`. Establish `: 0 < N` using `Fin.pos j`. Conclude with `this` after adjusting the coercions. Establish `: R' ≤ N * R'` using `le_mul_of_one_le_left hR' hN1`.

Establish `: 0 ≤ μ⁻¹` using `inv_nonneg.2 hμ.le`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem exists_short_basis (N : ℕ) : ∀ {X : Type u} [NormedAddCommGroup X] [InnerProductSpace ℝ X]
    [FiniteDimensional ℝ X], finrank ℝ X = N → ∀ (L : AddSubgroup X) (μ : ℝ), 0 < μ →
    span ℝ (L : Set X) = ⊤ → span ℝ (latticeDual L : Set X) = ⊤ →
    (∀ y ∈ latticeDual L, y ≠ 0 → μ ≤ ‖y‖) →
    ∃ e : Fin N → X, LinearIndependent ℝ e ∧ ∀ i, e i ∈ L ∧ ‖e i‖ ≤ shortBasisBound N μ := by
  induction N with
  | zero =>
    intro X _ _ _ _ L μ _ _ _ _
    exact ⟨Fin.elim0, linearIndependent_empty_type, fun i => Fin.elim0 i⟩
  | succ N ih =>
    intro X _ _ _ hdim L μ hμ hLspan hDspan hmin
    classical
    have : Nontrivial X := nontrivial_of_finrank_eq_succ hdim

    obtain ⟨y0, hy0, hy0ne⟩ : ∃ y ∈ latticeDual L, y ≠ 0 := by
      by_contra h
      push Not at h
      have hsub : (latticeDual L : Set X) ⊆ {0} := fun y hy => h y hy
      have hle := span_mono (R := ℝ) hsub
      rw [hDspan, span_singleton_eq_bot.2 rfl] at hle
      exact top_ne_bot (eq_bot_iff.2 hle)

    obtain ⟨w, ⟨⟨hwD, -⟩, hw0⟩, hwmin⟩ := Set.exists_min_image
      ({y | y ∈ latticeDual L ∧ ‖y‖ ≤ ‖y0‖} ∩ {y | y ≠ 0}) (fun y => ‖y‖)
      ((finite_latticeDual_norm_le hLspan ‖y0‖).subset Set.inter_subset_left)
      ⟨y0, ⟨hy0, le_rfl⟩, hy0ne⟩
    have hwmin' : ∀ y ∈ latticeDual L, y ≠ 0 → ‖w‖ ≤ ‖y‖ := by
      intro y hy hyne
      by_cases h : ‖y‖ ≤ ‖y0‖
      · exact hwmin y ⟨⟨hy, h⟩, hyne⟩
      · exact (hwmin y0 ⟨⟨hy0, le_rfl⟩, hy0ne⟩).trans (le_of_not_ge h)
    have hwμ : μ ≤ ‖w‖ := hmin w hwD hw0
    have hwpos : 0 < ‖w‖ := norm_pos_iff.2 hw0

    have hx1 : ∃ x ∈ L, ⟪w, x⟫ ≠ 0 := by
      by_contra h
      push Not at h
      exact hw0 (eq_zero_of_forall_inner_eq_zero hLspan h)
    have hex : ∃ n : ℕ, 0 < n ∧ ∃ x ∈ L, ⟪w, x⟫ = n := by
      obtain ⟨x1, hx1L, hx1⟩ := hx1
      obtain ⟨m, hm⟩ := hwD x1 hx1L
      have hm0 : m ≠ 0 := by rintro rfl; exact hx1 (by simpa using hm)
      rcases lt_or_gt_of_ne hm0 with hneg | hpos
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, -x1, neg_mem hx1L, ?_⟩
        rw [inner_neg_right, hm, Nat.cast_natAbs, Int.cast_abs,
          abs_of_neg (by exact_mod_cast hneg)]
      · refine ⟨m.natAbs, Int.natAbs_pos.2 hm0, x1, hx1L, ?_⟩
        rw [hm, Nat.cast_natAbs, Int.cast_abs, abs_of_pos (by exact_mod_cast hpos)]
    obtain ⟨hn0pos, x0, hx0L, hx0⟩ := Nat.find_spec hex
    have hdiv : ∀ x ∈ L, ∃ q : ℤ, ⟪w, x⟫ = q * (Nat.find hex : ℝ) := by
      intro x hx
      obtain ⟨m, hm⟩ := hwD x hx
      set n0 := Nat.find hex
      have hn0z : (0 : ℤ) < n0 := by exact_mod_cast hn0pos
      set r := m % (n0 : ℤ)
      have hr0 : 0 ≤ r := Int.emod_nonneg _ hn0z.ne'
      have hrlt : r < n0 := Int.emod_lt_of_pos _ hn0z
      have hmr : m = r + n0 * (m / n0) := (Int.emod_add_mul_ediv m n0).symm
      have hxr : x - (m / (n0 : ℤ)) • x0 ∈ L := sub_mem hx (zsmul_mem hx0L _)
      have hval : ⟪w, x - (m / (n0 : ℤ)) • x0⟫ = r := by
        rw [inner_sub_right, ← Int.cast_smul_eq_zsmul ℝ, inner_smul_right, hm, hx0]
        have : (m : ℝ) = r + n0 * (m / (n0 : ℤ) : ℤ) := by exact_mod_cast hmr
        rw [this]; ring
      have hr : r = 0 := by
        by_contra hrne
        have hrpos : 0 < r := lt_of_le_of_ne hr0 (Ne.symm hrne)
        have := Nat.find_min hex (m := r.toNat) (by omega)
        apply this
        refine ⟨by omega, _, hxr, ?_⟩
        rw [hval]
        have : ((r.toNat : ℤ) : ℝ) = r := by rw [Int.toNat_of_nonneg hr0]
        rw [← this]; norm_cast
      refine ⟨m / n0, ?_⟩
      have hm' : m = (m / n0) * n0 := by rw [hr] at hmr; linarith
      rw [hm]
      exact_mod_cast hm'
    have hn0 : Nat.find hex = 1 := by
      by_contra hne
      have hge : (2 : ℝ) ≤ Nat.find hex := by
        have : 2 ≤ Nat.find hex := by omega
        exact_mod_cast this
      set n0 := Nat.find hex
      have hw'D : (n0 : ℝ)⁻¹ • w ∈ latticeDual L := by
        intro x hx
        obtain ⟨q, hq⟩ := hdiv x hx
        refine ⟨q, ?_⟩
        rw [real_inner_smul_left, hq]
        field_simp
      have hw'0 : (n0 : ℝ)⁻¹ • w ≠ 0 := smul_ne_zero (inv_ne_zero (by linarith)) hw0
      have h1 := hwmin' _ hw'D hw'0
      rw [norm_smul, Real.norm_eq_abs, abs_inv, abs_of_pos (by linarith)] at h1
      have : (n0 : ℝ)⁻¹ * ‖w‖ < ‖w‖ := by
        have : (n0 : ℝ)⁻¹ ≤ 1 / 2 := by rw [inv_eq_one_div]; gcongr
        nlinarith
      linarith
    rw [hn0, Nat.cast_one] at hx0

    have : Fact (finrank ℝ X = N + 1) := ⟨hdim⟩
    set W : Submodule ℝ X := (ℝ ∙ w)ᗮ with hWdef
    have hWdim : finrank ℝ W = N := finrank_orthogonal_span_singleton hw0
    have memW : ∀ z : X, z ∈ W ↔ ⟪w, z⟫ = 0 := fun z => mem_orthogonal_singleton_iff_inner_right
    let M : AddSubgroup W := L.comap W.subtype.toAddMonoidHom
    have memM : ∀ m : W, m ∈ M ↔ (m : X) ∈ L := fun m => Iff.rfl

    let P : X →ₗ[ℝ] W :=
      { toFun := fun x => ⟨x - ⟪w, x⟫ • x0, by
          rw [memW, inner_sub_right, real_inner_smul_right, hx0]; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_smul] }
    have hP : ∀ x, (P x : X) = x - ⟪w, x⟫ • x0 := fun _ => rfl
    have hPL : ∀ x ∈ L, P x ∈ M := by
      intro x hx
      obtain ⟨n, hn⟩ := hwD x hx
      rw [memM, hP, hn, Int.cast_smul_eq_zsmul]
      exact sub_mem hx (zsmul_mem hx0L _)
    have hPW : ∀ z : W, P z = z := by
      intro z
      ext
      rw [hP, (memW z).1 z.2, zero_smul, sub_zero]
    have hPsurj : LinearMap.range P = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hPW z⟩
    have hMspan : span ℝ (M : Set W) = ⊤ := by
      apply eq_top_iff.2
      rw [← hPsurj, LinearMap.range_eq_map, ← hLspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hPL x hx)

    let π : X →ₗ[ℝ] W :=
      { toFun := fun z => ⟨z - (⟪w, z⟫ / ‖w‖ ^ 2) • w, by
          rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq]
          field_simp; ring⟩
        map_add' := fun x y => by
          ext; simp only [inner_add_right, add_div, add_smul, coe_add]; abel
        map_smul' := fun c x => by
          ext; simp only [real_inner_smul_right, coe_smul, RingHom.id_apply, smul_sub, mul_div_assoc,
            mul_smul] }
    have hπ : ∀ z, (π z : X) = z - (⟪w, z⟫ / ‖w‖ ^ 2) • w := fun _ => rfl
    have hπW : ∀ z : W, π z = z := by
      intro z
      ext
      rw [hπ, (memW z).1 z.2, zero_div, zero_smul, sub_zero]
    have hπD : ∀ z ∈ latticeDual L, π z ∈ latticeDual M := by
      intro z hz m hm
      obtain ⟨n, hn⟩ := hz m hm
      refine ⟨n, ?_⟩
      rw [coe_inner, hπ, inner_sub_left, real_inner_smul_left, (memW m).1 m.2, mul_zero, sub_zero, hn]
    have hMDspan : span ℝ (latticeDual M : Set W) = ⊤ := by
      apply eq_top_iff.2
      have hπsurj : LinearMap.range π = ⊤ := LinearMap.range_eq_top.2 fun z => ⟨z, hπW z⟩
      rw [← hπsurj, LinearMap.range_eq_map, ← hDspan, ← span_image]
      exact span_mono (by rintro _ ⟨x, hx, rfl⟩; exact hπD x hx)

    have hMmin : ∀ y ∈ latticeDual M, y ≠ 0 → Real.sqrt 3 / 2 * μ ≤ ‖y‖ := by
      intro y hy hyne
      have hyw : ⟪(y : X), w⟫ = 0 := by rw [real_inner_comm]; exact (memW y).1 y.2
      set c := ⟪(y : X), x0⟫
      set s : ℝ := (round c : ℝ) - c
      have hs : |s| ≤ 1 / 2 := by rw [abs_sub_comm]; exact abs_sub_round c
      set z := (y : X) + s • w
      have hzD : z ∈ latticeDual L := by
        intro x hx
        obtain ⟨n, hn⟩ := hwD x hx
        obtain ⟨k, hk⟩ := hy (P x) (hPL x hx)
        refine ⟨k + round c * n, ?_⟩
        rw [coe_inner, hP, inner_sub_right, real_inner_smul_right, hn] at hk
        rw [inner_add_left, real_inner_smul_left, hn]
        push_cast
        simp only [s]
        linear_combination hk
      have hz0 : z ≠ 0 := by
        intro h
        have : ⟪(y : X), z⟫ = ‖(y : X)‖ ^ 2 := by
          rw [inner_add_right, real_inner_smul_right, hyw, mul_zero, add_zero,
            real_inner_self_eq_norm_sq]
        rw [h, inner_zero_right] at this
        have hy0 : (y : X) = 0 := by
          have : ‖(y : X)‖ = 0 := by nlinarith [norm_nonneg (y : X)]
          exact norm_eq_zero.1 this
        exact hyne (Subtype.ext hy0)
      have hz := hwmin' z hzD hz0
      have hzn : ‖z‖ ^ 2 = ‖(y : X)‖ ^ 2 + s ^ 2 * ‖w‖ ^ 2 := by
        rw [norm_add_sq_real, real_inner_smul_right, hyw, norm_smul, Real.norm_eq_abs, mul_pow,
          sq_abs]
        ring
      have hs2 : s ^ 2 ≤ 1 / 4 := by
        have := abs_le.1 hs
        nlinarith
      have hsq : (Real.sqrt 3 / 2 * μ) ^ 2 ≤ ‖y‖ ^ 2 := by
        have h3 : Real.sqrt 3 ^ 2 = 3 := Real.sq_sqrt (by norm_num)
        have hw2 : ‖w‖ ^ 2 ≤ ‖z‖ ^ 2 := pow_le_pow_left₀ (norm_nonneg _) hz 2
        have hμ2 : μ ^ 2 ≤ ‖w‖ ^ 2 := pow_le_pow_left₀ hμ.le hwμ 2
        have : ‖y‖ = ‖(y : X)‖ := rfl
        rw [mul_pow, div_pow, h3, this]
        nlinarith
      exact le_of_sq_le_sq (by simpa using hsq) (norm_nonneg _) |>.trans_eq' rfl

    obtain ⟨e', hli', he'⟩ := ih (X := W) hWdim M (Real.sqrt 3 / 2 * μ) (by positivity) hMspan
      hMDspan hMmin
    set R' := shortBasisBound N (Real.sqrt 3 / 2 * μ)
    have hR' : 0 ≤ R' := shortBasisBound_nonneg N (by positivity)
    have hspan' : ⊤ ≤ span ℝ (Set.range e') := by
      rcases Nat.eq_zero_or_pos N with hN | hN
      · subst hN
        have : Subsingleton W := finrank_zero_iff.1 hWdim
        intro z _
        rw [Subsingleton.elim z 0]; exact zero_mem _
      · have : Nonempty (Fin N) := ⟨⟨0, hN⟩⟩
        exact (hli'.span_eq_top_of_card_eq_finrank (by simp [hWdim])).ge
    let B := Basis.mk hli' hspan'

    set q : W := ⟨x0 - (‖w‖ ^ 2)⁻¹ • w, by
      rw [memW, inner_sub_right, real_inner_smul_right, real_inner_self_eq_norm_sq, hx0]
      field_simp; ring⟩
    set c := B.repr q
    set x0' := x0 - ∑ i, ⌊c i⌋ • (e' i : X)
    have hx0'L : x0' ∈ L := sub_mem hx0L (sum_mem fun i _ => zsmul_mem (he' i).1 _)
    have hq : (q : X) = ∑ i, c i • (e' i : X) := by
      conv_lhs => rw [← B.sum_repr q]
      rw [coe_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [coe_smul, Basis.mk_apply]
    have hx0'eq : x0' = ∑ i, Int.fract (c i) • (e' i : X) + (‖w‖ ^ 2)⁻¹ • w := by
      have hx0q : x0 = (q : X) + (‖w‖ ^ 2)⁻¹ • w := by simp [q]
      simp only [x0']
      rw [hx0q, hq]
      have : ∀ i, Int.fract (c i) • (e' i : X) = c i • (e' i : X) - ⌊c i⌋ • (e' i : X) := by
        intro i
        rw [Int.fract, sub_smul, Int.cast_smul_eq_zsmul]
      simp only [this, Finset.sum_sub_distrib]
      abel
    have hx0'norm : ‖x0'‖ ≤ N * R' + μ⁻¹ := by
      rw [hx0'eq]
      refine (norm_add_le _ _).trans (add_le_add ?_ ?_)
      · refine (norm_sum_le _ _).trans ?_
        have : ∀ i, ‖Int.fract (c i) • (e' i : X)‖ ≤ R' := by
          intro i
          rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg (Int.fract_nonneg _)]
          have h1 := (he' i).2
          have h2 := (Int.fract_lt_one (c i)).le
          have : ‖(e' i : X)‖ = ‖e' i‖ := rfl
          rw [this]
          nlinarith [norm_nonneg (e' i), Int.fract_nonneg (c i)]
        refine (Finset.sum_le_sum fun i _ => this i).trans ?_
        simp
      · rw [norm_smul, Real.norm_eq_abs, abs_of_pos (by positivity), sq, mul_inv, mul_assoc,
          inv_mul_cancel₀ hwpos.ne', mul_one]
        exact inv_anti₀ hμ hwμ
    have hx0'w : ⟪w, x0'⟫ = 1 := by
      simp only [x0', inner_sub_right, inner_sum, ← Int.cast_smul_eq_zsmul ℝ, real_inner_smul_right]
      rw [hx0]
      have : ∀ i, ⟪w, (e' i : X)⟫ = 0 := fun i => (memW _).1 (e' i).2
      simp [this]
    refine ⟨Fin.cons x0' fun i => (e' i : X), ?_, ?_⟩
    · rw [linearIndependent_finCons]
      refine ⟨hli'.map' W.subtype (ker_subtype W), ?_⟩
      intro hmem
      have hle : span ℝ (Set.range fun i => (e' i : X)) ≤ W :=
        span_le.2 (by rintro _ ⟨i, rfl⟩; exact (e' i).2)
      have := (memW _).1 (hle hmem)
      rw [hx0'w] at this
      exact one_ne_zero this
    · intro i
      refine Fin.cases ?_ (fun j => ?_) i
      · exact ⟨hx0'L, by simpa [shortBasisBound] using hx0'norm⟩
      · refine ⟨(he' j).1, ?_⟩
        simp only [Fin.cons_succ, shortBasisBound]
        have h1 : ‖(e' j : X)‖ ≤ R' := (he' j).2
        have hN1 : (1 : ℝ) ≤ N := by
          have : 0 < N := Fin.pos j
          exact_mod_cast this
        have : R' ≤ N * R' := le_mul_of_one_le_left hR' hN1
        have : 0 ≤ μ⁻¹ := inv_nonneg.2 hμ.le
        linarith

end Reduction

end GroundTheory.Automorphic
