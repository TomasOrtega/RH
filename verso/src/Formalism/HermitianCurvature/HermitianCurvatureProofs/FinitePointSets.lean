import Formalism.HermitianCurvature.StatementTB

namespace Formalism.FourierDecayAlt.P.FinitePointSets

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

/- English proof (translation)
Use `set F : Finset (ℕ × E) := (range (i + 1)) ×ˢ S with hFdef`. Use `((List.finite_length_le F i).image (List.map Subtype.val)).subset ?_` and prove the remaining obligations. Introduce and unpack `p ⟨hl, hp⟩`. Establish `hmem : ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ∈ S`. Introduce `x hx`.

Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.1 hx`. Conclude with `hp k hk`. Unfold `level at hl`. Establish `hF : ∀ x ∈ p, x ∈ F`. Introduce `x hx`.

Simplify using `only [hFdef, mem_product, mem_range]`. Use `⟨?_, (hmem x hx).2⟩` and prove the remaining obligations. Establish `: x.1 ≤ (p.map Prod.fst).sum` using `List.le_sum_of_mem (List.mem_map_of_mem hx)`. Use linear arithmetic over natural numbers and integers. Use `⟨p.pmap Subtype.mk hF, ?_, ?_⟩` and prove the remaining obligations.

Establish `h1 : (p.map Prod.fst).length ≤ (p.map Prod.fst).sum`. Use `List.length_le_sum_of_one_le _ fun n hn => ?_` and prove the remaining obligations. Take `⟨x, hx, rfl⟩` from `List.mem_map.1 hn`. Conclude with `(hmem x hx).1`. Express the relevant statement in the definitionally equal form `(p.pmap Subtype.mk hF).length ≤ i`.

Simplify `h1` using `[hl]`. Simplify using `[List.map_pmap]`.
-/
theorem finite_pts {E : Type} [Field E] (S : Finset E) (i : ℕ) :
    {p : Pt E | level p = i ∧
      ∀ k (hk : k < p.length), 1 ≤ (p[k]'hk).1 ∧ (p[k]'hk).2 ∈ S}.Finite := by
  classical
  set F : Finset (ℕ × E) := (range (i + 1)) ×ˢ S with hFdef
  refine ((List.finite_length_le F i).image (List.map Subtype.val)).subset ?_
  rintro p ⟨hl, hp⟩
  have hmem : ∀ x ∈ p, 1 ≤ x.1 ∧ x.2 ∈ S := by
    intro x hx
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hx
    exact hp k hk
  unfold level at hl
  have hF : ∀ x ∈ p, x ∈ F := by
    intro x hx
    simp only [hFdef, mem_product, mem_range]
    refine ⟨?_, (hmem x hx).2⟩
    have : x.1 ≤ (p.map Prod.fst).sum := List.le_sum_of_mem (List.mem_map_of_mem hx)
    omega
  refine ⟨p.pmap Subtype.mk hF, ?_, ?_⟩
  · have h1 : (p.map Prod.fst).length ≤ (p.map Prod.fst).sum := by
      refine List.length_le_sum_of_one_le _ fun n hn => ?_
      obtain ⟨x, hx, rfl⟩ := List.mem_map.1 hn
      exact (hmem x hx).1
    change (p.pmap Subtype.mk hF).length ≤ i
    simpa [hl] using h1
  · simp [List.map_pmap]

noncomputable def tw {E : Type} [Field E] (S : Finset E) (h0 : (0 : E) ∉ S) : Tower E where
  Sg := fun _ _ => S
  X := fun i => (finite_pts S i).toFinset
  isTower := by
    intro i p
    simp
  zero_not_mem := fun _ _ => h0

/- English proof (translation)
Take `⟨B, hB⟩ : ∃ B : Matrix Y Y ℂ, Matrix.gram ℂ (fun p : Y => V p.1) = star B * B` from `by open scoped MatrixOrder Matrix.Norms.L2Operator in`. Conclude with `CStarAlgebra.nonneg_iff_eq_star_mul_self.mp (Matrix.posSemidef_gram ℂ (fun p : Y => V p.1)).nonneg`. Establish `hG : ∀ p q : Y, ⟪V p.1, V q.1⟫ = ∑ j, conj (B j p) * B j q`. Introduce `p q`. Use `congrFun (congrFun hB p) q` as an intermediate fact.

Simplify `this` using `[Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_apply]`. Establish `e1 : ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫ = ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫`. Rewrite using `[← Finset.sum_coe_sort Y]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_coe_sort Y]`.

Establish `e2 : ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫ = ∑ j : Y, star (fun p : Y => conj (B j p)) ⬝ᵥ (Matrix.of fun x y : Y => k x y).mulVec (fun p : Y => conj (B j p))`. Simplify using `only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def, Complex.conj_conj, Finset.mul_sum]`. Use `symm`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[hG q p, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e1, e2, Complex.re_sum]`. Conclude with `Finset.sum_nonneg fun j _ => Matrix.PosSemidef.re_dotProduct_nonneg hk _`.
-/
theorem form_nonneg {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (hk : PSDOn Y k) (V : α → H) :
    0 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  classical
  obtain ⟨B, hB⟩ : ∃ B : Matrix Y Y ℂ, Matrix.gram ℂ (fun p : Y => V p.1) = star B * B := by
    open scoped MatrixOrder Matrix.Norms.L2Operator in
    exact CStarAlgebra.nonneg_iff_eq_star_mul_self.mp
      (Matrix.posSemidef_gram ℂ (fun p : Y => V p.1)).nonneg
  have hG : ∀ p q : Y, ⟪V p.1, V q.1⟫ = ∑ j, conj (B j p) * B j q := by
    intro p q
    have := congrFun (congrFun hB p) q
    simpa [Matrix.gram, Matrix.mul_apply, Matrix.star_eq_conjTranspose,
      Matrix.conjTranspose_apply] using this
  have e1 : ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
      = ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫ := by
    rw [← Finset.sum_coe_sort Y]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [← Finset.sum_coe_sort Y]
  have e2 : ∑ p : Y, ∑ q : Y, k p.1 q.1 * ⟪V q.1, V p.1⟫
      = ∑ j : Y, star (fun p : Y => conj (B j p)) ⬝ᵥ
          (Matrix.of fun x y : Y => k x y).mulVec (fun p : Y => conj (B j p)) := by
    simp only [dotProduct, Matrix.mulVec, Matrix.of_apply, Pi.star_apply, RCLike.star_def,
      Complex.conj_conj, Finset.mul_sum]
    symm
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [hG q p, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    ring
  rw [e1, e2, Complex.re_sum]
  exact Finset.sum_nonneg fun j _ => Matrix.PosSemidef.re_dotProduct_nonneg hk _

/- English proof (translation)
Use `inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ Y, c p • V p)` as an intermediate fact. Rewrite using `[Complex.ofReal_pow]`. Use `this.symm.trans ?_` and prove the remaining obligations. Rewrite using `[inner_sum]`. Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations.

Rewrite using `[sum_inner]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[inner_smul_left, inner_smul_right]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem norm_sq_comb {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (c : α → ℂ) (V : α → H) :
    ((‖∑ p ∈ Y, c p • V p‖ ^ 2 : ℝ) : ℂ)
      = ∑ p ∈ Y, ∑ q ∈ Y, (c p * conj (c q)) * ⟪V q, V p⟫ := by
  have := inner_self_eq_norm_sq_to_K (𝕜 := ℂ) (∑ p ∈ Y, c p • V p)
  rw [Complex.ofReal_pow]
  refine this.symm.trans ?_
  rw [inner_sum]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [sum_inner]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [inner_smul_left, inner_smul_right]
  ring

/- English proof (translation)
Establish `h0` using `form_nonneg Y _ h V`. Establish `e : ∑ p ∈ Y, ∑ q ∈ Y, (k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q)) * ⟪V q, V p⟫ = ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫ - ((∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 : ℝ) : ℂ)`. Rewrite using `[Complex.ofReal_sum]`. Repeatedly rewrite using `[norm_sq_comb]`. Rewrite using `[Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]`.

Use `Finset.sum_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[sub_mul, Finset.sum_mul]`. Rewrite `h0` using `[e, Complex.sub_re, Complex.ofReal_re]`.

Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem rows_le_form {α H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (Y : Finset α) (k : α → α → ℂ) (V : α → H) (c : ℕ → α → ℂ) (R : Finset ℕ)
    (h : PSDOn Y (fun p q => k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q))) :
    ∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 ≤ (∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫).re := by
  have h0 := form_nonneg Y _ h V
  have e : ∑ p ∈ Y, ∑ q ∈ Y, (k p q - ∑ ρ ∈ R, c ρ p * starRingEnd ℂ (c ρ q)) * ⟪V q, V p⟫
      = ∑ p ∈ Y, ∑ q ∈ Y, k p q * ⟪V q, V p⟫
        - ((∑ ρ ∈ R, ‖∑ p ∈ Y, c ρ p • V p‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.ofReal_sum]
    simp_rw [norm_sq_comb]
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    rw [Finset.sum_comm (s := R), ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [sub_mul, Finset.sum_mul]
  rw [e, Complex.sub_re, Complex.ofReal_re] at h0
  linarith

end Formalism.FourierDecayAlt.P.FinitePointSets

namespace Formalism.FourierDecayAlt.P

open Formalism.FourierDecayAlt.TB Finset Filter Topology
open scoped ComplexInnerProductSpace ComplexConjugate

/- English proof (translation)
Introduce `E W _ D jn H _ _ _ Vt c _ _ hE hC hA B hB R`. Take `⟨hA1, hA2, hA3⟩` from `hA`. Establish `hsum : ∀ ρ, Summable (fun p : Pt E => c ρ p • Vt p)`. Introduce `ρ`. Use `Summable.of_norm ?_` and prove the remaining obligations.

Simplify `hA3 ρ` using `[norm_smul]`. Establish `hlim : Tendsto (fun F : Finset (Pt E) => ∑ ρ ∈ R, ‖∑ p ∈ F, c ρ p • Vt p‖ ^ 2) atTop (𝓝 (∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2))`. Use `tendsto_finsetSum _ fun ρ _ => ?_` and prove the remaining obligations. Conclude with `((hsum ρ).hasSum.norm).pow 2`. Use `le_of_tendsto_of_frequently hlim ?_` and prove the remaining obligations.

Rewrite using `[Filter.frequently_atTop]`. Introduce `F`. Use `set F0 : Finset (Pt E) := F.filter (fun p => IsPt p (D.r + 1)) with hF0`. Use `set S : Finset E := F0.biUnion fun p => (p.map Prod.snd).toFinset with hS`. Establish `hS0 : (0 : E) ∉ S`.

Introduce `h`. Simplify using `only [hS, mem_biUnion, List.mem_toFinset, List.mem_map] at h`. Take `⟨p, hp, b, hb, hb0⟩` from `h`. Take `⟨k, hk, rfl⟩` from `List.mem_iff_getElem.1 hb`. Conclude with `((Finset.mem_filter.1 hp).2.2 k hk).2 hb0`.

Use `set T : Tower E := FinitePointSets.tw S hS0 with hT`. Use `set Y : Finset (Pt E) := T.X (D.r + 1) with hY`. Establish `hYpt : ∀ p ∈ Y, IsPt p (D.r + 1)`. Introduce `p hp`. Take `⟨h1, h2⟩` from `(T.isTower (D.r + 1) p).1 hp`.

Use `⟨h1, fun k hk => ⟨(h2 k hk).1, fun h => ?_⟩⟩` and prove the remaining obligations. Use `(h2 k hk).2` as an intermediate fact. Rewrite `this` using `[h]`. Conclude with `T.zero_not_mem _ _ this`. Establish `hF0Y : ∀ p ∈ F0, p ∈ Y`.

Introduce `p hp`. Establish `hp'` using `(Finset.mem_filter.1 hp).2`. Use `(T.isTower (D.r + 1) p).2 ⟨hp'.1, fun k hk => ⟨(hp'.2 k hk).1, ?_⟩⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(p[k]'hk).2 ∈ S`. Simplify using `only [hS, mem_biUnion, List.mem_toFinset, List.mem_map]`.

Conclude with `⟨p, hp, p[k]'hk, List.getElem_mem hk, rfl⟩`. Use `⟨F ∪ Y, Finset.subset_union_left, ?_⟩` and prove the remaining obligations. Establish `e : ∀ ρ, ∑ p ∈ F ∪ Y, c ρ p • Vt p = ∑ p ∈ Y, c ρ p • Vt p`. Introduce `ρ`. Use `symm`.

Use `Finset.sum_subset Finset.subset_union_right fun p hp hnp => ?_` and prove the remaining obligations. Establish `hc : c ρ p = 0`. Assume the negation of the conclusion as `h`. Establish `hpF : p ∈ F`. Break down `Finset.mem_union.1 hp with h' | h'` into its components or cases.

Conclude with `h'`. Conclude with `absurd h' hnp`. Conclude with `hnp (hF0Y p (Finset.mem_filter.2 ⟨hpF, hA1 ρ p h⟩))`. Rewrite using `[hc, zero_smul]`. Repeatedly rewrite using `[e]`.

Use `(FinitePointSets.rows_le_form Y (D.Kr (D.r + 1)) Vt c R (hA2 Y hYpt R)).trans ?_` and prove the remaining obligations. Establish `key : ∀ δ : ℝ, 0 < δ → (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re ≤ B * (jn + δ)`. Introduce `δ hδ`. Establish `h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ D.Wb D.Ntop, (D.gram ε 0 w [] []).re / D.wt w ≤ jn + δ` using `(Filter.eventually_all_finset _).2 fun w hw => (hE w hw).eventually_le_const (by linarith)`. Take `⟨ε, h1ε, h2ε, hε⟩` from `(h1.and ((hC Y hYpt).and self_mem_nhdsWithin)).exists`.

Establish `h3` using `hB T ε hε (jn + δ) h1ε`. Establish `e2 : D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1)) = (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re`. Unfold `Data.Sf`. Use `congr 1`. Use `Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_` and prove the remaining obligations.

Distinguish the cases in `hK : D.Kr (D.r + 1) p q = 0`. Rewrite using `[hK, zero_mul, zero_mul]`. Rewrite using `[h2ε p hp q hq hK]`. Rewrite `h3` using `[e2]`. Then use the resulting hypothesis. Establish `ht : Tendsto (fun δ : ℝ => B * (jn + δ)) (𝓝[>] 0) (𝓝 (B * (jn + 0)))` using `(Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds`.

Rewrite `ht` using `[add_zero]`. Conclude with `ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with δ hδ using key δ hδ)`.
-/
theorem limitStep : Formalism.FourierDecayAlt.TB.LimitStep := by
  intro E W _ D jn H _ _ _ Vt c _ _ hE hC hA B hB R
  classical
  obtain ⟨hA1, hA2, hA3⟩ := hA
  have hsum : ∀ ρ, Summable (fun p : Pt E => c ρ p • Vt p) := by
    intro ρ
    refine Summable.of_norm ?_
    simpa [norm_smul] using hA3 ρ
  have hlim : Tendsto (fun F : Finset (Pt E) => ∑ ρ ∈ R, ‖∑ p ∈ F, c ρ p • Vt p‖ ^ 2) atTop
      (𝓝 (∑ ρ ∈ R, ‖∑' p, c ρ p • Vt p‖ ^ 2)) := by
    refine tendsto_finsetSum _ fun ρ _ => ?_
    exact ((hsum ρ).hasSum.norm).pow 2
  refine le_of_tendsto_of_frequently hlim ?_
  rw [Filter.frequently_atTop]
  intro F

  set F0 : Finset (Pt E) := F.filter (fun p => IsPt p (D.r + 1)) with hF0
  set S : Finset E := F0.biUnion fun p => (p.map Prod.snd).toFinset with hS
  have hS0 : (0 : E) ∉ S := by
    intro h
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map] at h
    obtain ⟨p, hp, b, hb, hb0⟩ := h
    obtain ⟨k, hk, rfl⟩ := List.mem_iff_getElem.1 hb
    exact ((Finset.mem_filter.1 hp).2.2 k hk).2 hb0
  set T : Tower E := FinitePointSets.tw S hS0 with hT
  set Y : Finset (Pt E) := T.X (D.r + 1) with hY
  have hYpt : ∀ p ∈ Y, IsPt p (D.r + 1) := by
    intro p hp
    obtain ⟨h1, h2⟩ := (T.isTower (D.r + 1) p).1 hp
    refine ⟨h1, fun k hk => ⟨(h2 k hk).1, fun h => ?_⟩⟩
    have := (h2 k hk).2
    rw [h] at this
    exact T.zero_not_mem _ _ this
  have hF0Y : ∀ p ∈ F0, p ∈ Y := by
    intro p hp
    have hp' := (Finset.mem_filter.1 hp).2
    refine (T.isTower (D.r + 1) p).2 ⟨hp'.1, fun k hk => ⟨(hp'.2 k hk).1, ?_⟩⟩
    change (p[k]'hk).2 ∈ S
    simp only [hS, mem_biUnion, List.mem_toFinset, List.mem_map]
    exact ⟨p, hp, p[k]'hk, List.getElem_mem hk, rfl⟩
  refine ⟨F ∪ Y, Finset.subset_union_left, ?_⟩
  have e : ∀ ρ, ∑ p ∈ F ∪ Y, c ρ p • Vt p = ∑ p ∈ Y, c ρ p • Vt p := by
    intro ρ
    symm
    refine Finset.sum_subset Finset.subset_union_right fun p hp hnp => ?_
    have hc : c ρ p = 0 := by
      by_contra h
      have hpF : p ∈ F := by
        rcases Finset.mem_union.1 hp with h' | h'
        · exact h'
        · exact absurd h' hnp
      exact hnp (hF0Y p (Finset.mem_filter.2 ⟨hpF, hA1 ρ p h⟩))
    rw [hc, zero_smul]
  simp_rw [e]
  refine (FinitePointSets.rows_le_form Y (D.Kr (D.r + 1)) Vt c R (hA2 Y hYpt R)).trans ?_

  have key : ∀ δ : ℝ, 0 < δ →
      (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re ≤ B * (jn + δ) := by
    intro δ hδ
    have h1 : ∀ᶠ ε in 𝓝[>] (0 : ℝ), ∀ w ∈ D.Wb D.Ntop,
        (D.gram ε 0 w [] []).re / D.wt w ≤ jn + δ :=
      (Filter.eventually_all_finset _).2 fun w hw =>
        (hE w hw).eventually_le_const (by linarith)
    obtain ⟨ε, h1ε, h2ε, hε⟩ := (h1.and ((hC Y hYpt).and self_mem_nhdsWithin)).exists
    have h3 := hB T ε hε (jn + δ) h1ε
    have e2 : D.Sf ε (D.r + 1) D.emp (T.X (D.r + 1))
        = (∑ p ∈ Y, ∑ q ∈ Y, D.Kr (D.r + 1) p q * ⟪Vt q, Vt p⟫).re := by
      unfold Data.Sf
      congr 1
      refine Finset.sum_congr rfl fun p hp => Finset.sum_congr rfl fun q hq => ?_
      by_cases hK : D.Kr (D.r + 1) p q = 0
      · rw [hK, zero_mul, zero_mul]
      · rw [h2ε p hp q hq hK]
    rwa [e2] at h3
  have ht : Tendsto (fun δ : ℝ => B * (jn + δ)) (𝓝[>] 0) (𝓝 (B * (jn + 0))) :=
    (Continuous.tendsto (by fun_prop) 0).mono_left nhdsWithin_le_nhds
  rw [add_zero] at ht
  exact ge_of_tendsto ht (by filter_upwards [self_mem_nhdsWithin] with δ hδ using key δ hδ)

end Formalism.FourierDecayAlt.P
