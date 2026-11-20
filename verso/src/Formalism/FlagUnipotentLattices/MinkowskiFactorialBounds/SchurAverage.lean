import Formalism.FlagUnipotentLattices.MinkowskiFactorialBounds.LatticeSumBounds

open Module Matrix Formalism.HermitianLatticeCounting.LatticeSumBounds
open scoped BigOperators ComplexConjugate

namespace Formalism.HermitianLatticeCounting.P

open MeasureTheory Metric in
/- English proof (translation)
Use `borelize F`. Set `μ : Measure F` to `Measure.addHaar`. Set `ν : Measure (ι → F)` to `Measure.pi fun _ => μ`. Use `set n := finrank ℝ F with hn`. Set `P : (ι → F) → Set (ι → F)` to `fun c => Set.pi Set.univ fun v => ball (c v) (r v)`.

Establish `hPm : ∀ c, MeasurableSet (P c)` using `fun c => MeasurableSet.univ_pi fun v => measurableSet_ball`. Establish `D : Set.Pairwise (S : Set (ι → F)) (Function.onFun Disjoint P)`. Introduce and unpack `c hc d hd hcd`. Take `⟨v, hv⟩` from `hsep c hc d hd hcd`. Rewrite using `[Function.onFun, Set.disjoint_left]`.

Introduce `x hx hx'`. Establish `h1` using `hx v (Set.mem_univ v)`. Establish `h2` using `hx' v (Set.mem_univ v)`. Rewrite `h1`, `h2` using `[mem_ball, dist_eq_norm]`. Establish `: ‖c v - d v‖ ≤ ‖x v - d v‖ + ‖x v - c v‖`.

Establish `e : c v - d v = (x v - d v) - (x v - c v)` using `by abel`. Rewrite using `[e]`. Conclude with `norm_sub_le _ _`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsub : (⋃ c ∈ S, P c) ⊆ Set.pi Set.univ fun v => ball (0:F) (B v + r v)`.

Use `Set.iUnion₂_subset fun c hc => ?_` and prove the remaining obligations. Introduce `x hx v _`. Establish `h1` using `hx v (Set.mem_univ v)`. Rewrite `h1` using `[mem_ball, dist_eq_norm]`. Rewrite using `[mem_ball, dist_zero_right]`.

Establish `: ‖x v‖ ≤ ‖x v - c v‖ + ‖c v‖` using `by simpa using norm_add_le (x v - c v) (c v)`. Combine the linear relations using `[hS c hc v]`. Use `set m := μ (ball 0 1) with hm`. Establish `hvol : ∀ (c : ι → F) (ρ : ι → ℝ), (∀ v, 0 < ρ v) → ν (Set.pi Set.univ fun v => ball (c v) (ρ v)) = ENNReal.ofReal (∏ v, ρ v ^ n) * m ^ Fintype.card ι`. Introduce `c ρ hρ`.

Simplify using `only [ν, Measure.pi_pi]`. Establish `: ∀ v, μ (ball (c v) (ρ v)) = ENNReal.ofReal (ρ v ^ n) * m` using `fun v => μ.addHaar_ball_of_pos _ (hρ v)`. Simplify using `only [this]`. Rewrite using `[Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg (fun v _ => (pow_pos (hρ v) n).le), Finset.prod_const, Finset.card_univ]`. Establish `I : (S.card : ENNReal) * ENNReal.ofReal (∏ v, r v ^ n) * m ^ Fintype.card ι ≤ ENNReal.ofReal (∏ v, (B v + r v) ^ n) * m ^ Fintype.card ι`.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[measure_biUnion_finset D fun c _ => hPm c]`. Simplify using `only [P, hvol _ r hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]`. Use `_ ≤ ν (Set.pi Set.univ fun v => ball (0:F) (B v + r v)) := measure_mono hsub`. Use `_ = _ := hvol (fun _ => 0) (fun v => B v + r v) (fun v => by linarith [hB v, hr v])`.

Establish `hm0 : m ^ Fintype.card ι ≠ 0` using `pow_ne_zero _ (measure_ball_pos _ _ zero_lt_one).ne'`. Establish `hmt : m ^ Fintype.card ι ≠ ⊤` using `ENNReal.pow_ne_top measure_ball_lt_top.ne`. Establish `J` using `(ENNReal.mul_le_mul_iff_left hm0 hmt).1 I`. Establish `hA : 0 < ∏ v, r v ^ n` using `Finset.prod_pos fun v _ => pow_pos (hr v) n`. Establish `K` using `ENNReal.toReal_le_of_le_ofReal (Finset.prod_nonneg fun v _ => pow_nonneg (by linarith [hB v, hr v]) n) J`.

Rewrite `K` using `[ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hA.le]`. Simplify using `only [div_pow]`. Rewrite using `[Finset.prod_div_distrib, le_div_iff₀ hA]`. Conclude with `K`.
-/
lemma card_separated_set_le_prod {ι : Type*} [Fintype ι] {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [FiniteDimensional ℝ F] (S : Finset (ι → F)) (r B : ι → ℝ) (hr : ∀ v, 0 < r v)
    (hB : ∀ v, 0 ≤ B v) (hS : ∀ c ∈ S, ∀ v, ‖c v‖ ≤ B v)
    (hsep : ∀ c ∈ S, ∀ d ∈ S, c ≠ d → ∃ v, 2 * r v ≤ ‖c v - d v‖) :
    (S.card : ℝ) ≤ ∏ v, ((B v + r v) / r v) ^ finrank ℝ F := by
  borelize F
  let μ : Measure F := Measure.addHaar
  let ν : Measure (ι → F) := Measure.pi fun _ => μ
  set n := finrank ℝ F with hn
  let P : (ι → F) → Set (ι → F) := fun c => Set.pi Set.univ fun v => ball (c v) (r v)
  have hPm : ∀ c, MeasurableSet (P c) := fun c => MeasurableSet.univ_pi fun v => measurableSet_ball
  have D : Set.Pairwise (S : Set (ι → F)) (Function.onFun Disjoint P) := by
    rintro c hc d hd hcd
    obtain ⟨v, hv⟩ := hsep c hc d hd hcd
    rw [Function.onFun, Set.disjoint_left]
    intro x hx hx'
    have h1 := hx v (Set.mem_univ v)
    have h2 := hx' v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1 h2
    have : ‖c v - d v‖ ≤ ‖x v - d v‖ + ‖x v - c v‖ := by
      have e : c v - d v = (x v - d v) - (x v - c v) := by abel
      rw [e]; exact norm_sub_le _ _
    linarith
  have hsub : (⋃ c ∈ S, P c) ⊆ Set.pi Set.univ fun v => ball (0:F) (B v + r v) := by
    refine Set.iUnion₂_subset fun c hc => ?_
    intro x hx v _
    have h1 := hx v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1
    rw [mem_ball, dist_zero_right]
    have : ‖x v‖ ≤ ‖x v - c v‖ + ‖c v‖ := by simpa using norm_add_le (x v - c v) (c v)
    linarith [hS c hc v]
  set m := μ (ball 0 1) with hm
  have hvol : ∀ (c : ι → F) (ρ : ι → ℝ), (∀ v, 0 < ρ v) →
      ν (Set.pi Set.univ fun v => ball (c v) (ρ v)) =
        ENNReal.ofReal (∏ v, ρ v ^ n) * m ^ Fintype.card ι := by
    intro c ρ hρ
    simp only [ν, Measure.pi_pi]
    have : ∀ v, μ (ball (c v) (ρ v)) = ENNReal.ofReal (ρ v ^ n) * m := fun v =>
      μ.addHaar_ball_of_pos _ (hρ v)
    simp only [this]
    rw [Finset.prod_mul_distrib, ENNReal.ofReal_prod_of_nonneg (fun v _ => (pow_pos (hρ v) n).le),
      Finset.prod_const, Finset.card_univ]
  have I : (S.card : ENNReal) * ENNReal.ofReal (∏ v, r v ^ n) * m ^ Fintype.card ι ≤
      ENNReal.ofReal (∏ v, (B v + r v) ^ n) * m ^ Fintype.card ι :=
    calc (S.card : ENNReal) * ENNReal.ofReal (∏ v, r v ^ n) * m ^ Fintype.card ι
        = ν (⋃ c ∈ S, P c) := by
          rw [measure_biUnion_finset D fun c _ => hPm c]
          simp only [P, hvol _ r hr, Finset.sum_const, nsmul_eq_mul, mul_assoc]
      _ ≤ ν (Set.pi Set.univ fun v => ball (0:F) (B v + r v)) := measure_mono hsub
      _ = _ := hvol (fun _ => 0) (fun v => B v + r v) (fun v => by linarith [hB v, hr v])
  have hm0 : m ^ Fintype.card ι ≠ 0 := pow_ne_zero _ (measure_ball_pos _ _ zero_lt_one).ne'
  have hmt : m ^ Fintype.card ι ≠ ⊤ := ENNReal.pow_ne_top measure_ball_lt_top.ne
  have J := (ENNReal.mul_le_mul_iff_left hm0 hmt).1 I
  have hA : 0 < ∏ v, r v ^ n := Finset.prod_pos fun v _ => pow_pos (hr v) n
  have K := ENNReal.toReal_le_of_le_ofReal
    (Finset.prod_nonneg fun v _ => pow_nonneg (by linarith [hB v, hr v]) n) J
  rw [ENNReal.toReal_mul, ENNReal.toReal_natCast, ENNReal.toReal_ofReal hA.le] at K
  simp only [div_pow]
  rw [Finset.prod_div_distrib, le_div_iff₀ hA]
  exact K

/- English proof (translation)
Establish `hfin : T.Finite`. Assume the negation of the conclusion as `hinf`. Take `⟨S, hS, hc⟩` from `Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)`. Use `h S hS` as an intermediate fact. Rewrite `this` using `[hc]`.

Establish `h2` using `Nat.le_ceil C`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Use `⟨hfin, ?_⟩` and prove the remaining obligations. Use `h hfin.toFinset (by simp)` as an intermediate fact.

Rewrite `this` using `[← Set.ncard_eq_toFinset_card _ hfin]`. Then use the resulting hypothesis.
-/
lemma finite_of_finset_card_bound {α : Type*} (T : Set α) (C : ℝ)
    (h : ∀ S : Finset α, (↑S ⊆ T) → (S.card : ℝ) ≤ C) : T.Finite ∧ (T.ncard : ℝ) ≤ C := by
  have hfin : T.Finite := by
    by_contra hinf
    obtain ⟨S, hS, hc⟩ := Set.Infinite.exists_subset_card_eq hinf (⌈C⌉₊ + 1)
    have := h S hS
    rw [hc] at this
    have h2 := Nat.le_ceil C
    push_cast at this
    linarith
  refine ⟨hfin, ?_⟩
  have := h hfin.toFinset (by simp)
  rwa [← Set.ncard_eq_toFinset_card _ hfin] at this

/- English proof (translation)
Introduce `E _ _ _ Λ l₀ R hl hR hΛ`. Apply `finite_of_finset_card_bound` to reduce the goal to its premises. Introduce `S hS`. Set `emb : E ↪ (Unit → E)` to `⟨fun x _ => x, fun x y h => congrFun h ()⟩`. Use `card_separated_set_le_prod (S.map emb) (fun _ => l₀ / 2) (fun _ => R) (fun _ => by positivity) (fun _ => hR) (by` as an intermediate fact.

Introduce `c hc v`. Take `⟨x, hx, rfl⟩` from `Finset.mem_map.1 hc`. Conclude with `(hS hx).2) (by`. Introduce `c hc d hd hcd`. Take `⟨x, hx, rfl⟩` from `Finset.mem_map.1 hc`.

Take `⟨y, hy, rfl⟩` from `Finset.mem_map.1 hd`. Use `⟨(), ?_⟩` and prove the remaining obligations. Establish `hxy : x - y ≠ 0` using `fun h => hcd (by rw [sub_eq_zero.mp h])`. Use `hΛ (x - y) (Λ.sub_mem (hS hx).1 (hS hy).1) hxy` as an intermediate fact. Use `show 2 * (l₀ / 2) ≤ ‖x - y‖`.

Use the proof step `linarith)`. Rewrite `this` using `[Finset.card_map]`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `only [Finset.univ_unique, Finset.prod_singleton]`. Use `congr 1`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem packing_bound : Packing := by
  intro E _ _ _ Λ l₀ R hl hR hΛ
  apply finite_of_finset_card_bound
  intro S hS
  classical
  let emb : E ↪ (Unit → E) := ⟨fun x _ => x, fun x y h => congrFun h ()⟩
  have := card_separated_set_le_prod (S.map emb) (fun _ => l₀ / 2) (fun _ => R) (fun _ => by positivity)
    (fun _ => hR) (by
      intro c hc v
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hc
      exact (hS hx).2) (by
      intro c hc d hd hcd
      obtain ⟨x, hx, rfl⟩ := Finset.mem_map.1 hc
      obtain ⟨y, hy, rfl⟩ := Finset.mem_map.1 hd
      refine ⟨(), ?_⟩
      have hxy : x - y ≠ 0 := fun h => hcd (by rw [sub_eq_zero.mp h])
      have := hΛ (x - y) (Λ.sub_mem (hS hx).1 (hS hy).1) hxy
      show 2 * (l₀ / 2) ≤ ‖x - y‖
      linarith)
  rw [Finset.card_map] at this
  refine this.trans (le_of_eq ?_)
  simp only [Finset.univ_unique, Finset.prod_singleton]
  congr 1; field_simp; ring

/- English proof (translation)
Rewrite using `[← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v₀)]`. Establish `: ∏ v ∈ Finset.univ.erase v₀, a v ≤ 1` using `Finset.prod_le_one (fun v _ => h0 v) (fun v _ => (h1 v).le)`. Combine the equalities or inequalities in the displayed calculation.
-/
lemma prod_lt_one_of_lt_one {ι : Type*} [Fintype ι] (a : ι → ℝ) (h0 : ∀ v, 0 ≤ a v) (h1 : ∀ v, a v < 1)
    (v₀ : ι) : ∏ v, a v < 1 := by
  classical
  rw [← Finset.mul_prod_erase Finset.univ a (Finset.mem_univ v₀)]
  have : ∏ v ∈ Finset.univ.erase v₀, a v ≤ 1 :=
    Finset.prod_le_one (fun v _ => h0 v) (fun v _ => (h1 v).le)
  calc a v₀ * ∏ v ∈ Finset.univ.erase v₀, a v ≤ a v₀ * 1 := mul_le_mul_of_nonneg_left this (h0 v₀)
    _ < 1 := by rw [mul_one]; exact h1 v₀

/- English proof (translation)
Introduce `ι _ Λ B hB hΛ`. Establish `h12 : {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧ ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤ ∏ v, (1 + 2 * B v) ^ 2`. Apply `finite_of_finset_card_bound` to reduce the goal to its premises. Introduce `S hS`. Use `card_separated_set_le_prod S (fun _ => 1 / 2) B (fun _ => by norm_num) (fun v => (hB v).le) (fun c hc => (hS hc).2) (by` as an intermediate fact.

Introduce `c hc d hd hcd`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hne : c - d ≠ 0` using `sub_ne_zero.mpr hcd`. Take `⟨v₀, -⟩ : ∃ v, c v ≠ d v` from `Function.ne_iff.mp hcd`.

Establish `h1` using `hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne`. Establish `h2` using `prod_lt_one_of_lt_one (fun v => ‖(c - d) v‖) (fun v => norm_nonneg _) (fun v => by have := hcon v; simp only [Pi.sub_apply]; linarith) v₀`. Use the proof step `linarith)`. Use `this.trans (le_of_eq ?_)` and prove the remaining obligations. Rewrite using `[Complex.finrank_real_complex]`.

Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations. Use `congr 1`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨h12.1, h12.2, ?_⟩` and prove the remaining obligations.

Rewrite using `[Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_` and prove the remaining obligations. Establish `a1 : (1:ℝ) ≤ max 1 (B v)` using `le_max_left _ _`. Establish `a2 : B v ≤ max 1 (B v)` using `le_max_right _ _`. Use `hB v` as an intermediate fact.

Use the polynomial consequences of the given equalities and inequalities.
-/
theorem box_count_big_O : BoxCountO := by
  intro ι _ Λ B hB hΛ
  have h12 : {x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.Finite ∧
      ({x | x ∈ Λ ∧ ∀ v, ‖x v‖ ≤ B v}.ncard : ℝ) ≤ ∏ v, (1 + 2 * B v) ^ 2 := by
    apply finite_of_finset_card_bound
    intro S hS
    have := card_separated_set_le_prod S (fun _ => 1 / 2) B (fun _ => by norm_num) (fun v => (hB v).le)
      (fun c hc => (hS hc).2) (by
        intro c hc d hd hcd
        by_contra hcon
        push_neg at hcon
        have hne : c - d ≠ 0 := sub_ne_zero.mpr hcd
        obtain ⟨v₀, -⟩ : ∃ v, c v ≠ d v := Function.ne_iff.mp hcd
        have h1 := hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne
        have h2 := prod_lt_one_of_lt_one (fun v => ‖(c - d) v‖) (fun v => norm_nonneg _)
          (fun v => by have := hcon v; simp only [Pi.sub_apply]; linarith) v₀
        linarith)
    refine this.trans (le_of_eq ?_)
    rw [Complex.finrank_real_complex]
    refine Finset.prod_congr rfl fun v _ => ?_
    congr 1; field_simp; ring
  refine ⟨h12.1, h12.2, ?_⟩
  rw [Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
  refine Finset.prod_le_prod (fun v _ => by positivity) fun v _ => ?_
  have a1 : (1:ℝ) ≤ max 1 (B v) := le_max_left _ _
  have a2 : B v ≤ max 1 (B v) := le_max_right _ _
  have := hB v
  nlinarith

/- English proof (translation)
Introduce `ι _ s Λ ν B hν hB hΛ`. Apply `finite_of_finset_card_bound` to reduce the goal to its premises. Introduce `S hS`. Use `set Q := (∏ v, B v ^ 2) / ν with hQ`. Use `set M := max 1 Q with hM`.

Establish `hM1 : 1 ≤ M` using `le_max_left _ _`. Establish `hM0 : 0 < M` using `by linarith`. Establish `hPB : 0 < ∏ v, B v ^ 2` using `Finset.prod_pos fun v _ => pow_pos (hB v) 2`. Break down `isEmpty_or_nonempty ι with hι | hι` into its components or cases. Establish `h1 : S.card ≤ 1` using `Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b`.

Establish `h2 : (1:ℝ) ≤ 9 ^ (s * Fintype.card ι) * M ^ s` using `one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hM1)`. Establish `h3 : (S.card : ℝ) ≤ 1` using `by exact_mod_cast h1`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set f := Fintype.card ι with hf`. Establish `hf0 : 0 < f` using `Fintype.card_pos`.

Establish `hfR : (0:ℝ) < f` using `by exact_mod_cast hf0`. Use `set τ := M ^ (1 / (2 * (f:ℝ))) with hτ`. Establish `hτ1 : 1 ≤ τ` using `Real.one_le_rpow hM1 (by positivity)`. Establish `hτ0 : 0 < τ` using `by linarith`. Establish `hτpow : τ ^ (2 * f) = M`.

Rewrite using `[hτ, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]`. Establish `: 1 / (2 * (f:ℝ)) * ((2 * f : ℕ) : ℝ) = 1` using `by push_cast; field_simp`. Rewrite using `[this, Real.rpow_one]`. Establish `hprod : ∏ v, (2 * (B v / (2 * τ))) ^ 2 ≤ ν`. Establish `e : ∀ v, (2 * (B v / (2 * τ))) ^ 2 = B v ^ 2 / τ ^ 2` using `fun v => by field_simp`.

Simplify using `only [e]`. Rewrite using `[Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, ← hf, hτpow, div_le_iff₀ hM0]`. Establish `: Q ≤ M` using `le_max_right _ _`. Rewrite `this` using `[hQ, div_le_iff₀ hν]`. Combine the linear equalities and inequalities to obtain the conclusion.

Use `card_separated_set_le_prod S (fun v => B v / (2 * τ)) B (fun v => by have := hB v; positivity) (fun v => (hB v).le) (fun c hc => (hS hc).2) (by` as an intermediate fact. Introduce `c hc d hd hcd`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Establish `hne : c - d ≠ 0` using `sub_ne_zero.mpr hcd`.

Establish `h1` using `hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne`. Establish `hpos : ∀ v ∈ Finset.univ, 0 < ‖(c - d) v‖ ^ 2`. Introduce `v _`. Assume the negation of the conclusion as `h0`. Establish `hz : ‖(c - d) v‖ ^ 2 = 0` using `le_antisymm (not_lt.mp h0) (by positivity)`.

Establish `: ∏ v, ‖(c - d) v‖ ^ 2 = 0` using `Finset.prod_eq_zero (Finset.mem_univ v) hz`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h2 : ∏ v, ‖(c - d) v‖ ^ 2 < ∏ v, (2 * (B v / (2 * τ))) ^ 2` using `Finset.prod_lt_prod_of_nonempty hpos (fun v _ => pow_lt_pow_left₀ (hcon v) (norm_nonneg _) (by norm_num)) Finset.univ_nonempty`. Use the proof step `linarith)`. Use `this.trans ?_` and prove the remaining obligations.

Establish `hdim : finrank ℝ (EuclideanSpace ℂ (Fin s)) = 2 * s`. Rewrite using `[← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin s)), Complex.finrank_real_complex, finrank_euclideanSpace, Fintype.card_fin]`. Rewrite using `[hdim]`. Combine the equalities or inequalities in the displayed calculation. Use `Finset.prod_le_prod (fun v _ => by have := hB v; positivity) fun v _ => ?_` and prove the remaining obligations.

Establish `hb` using `hB v`. Establish `e : (B v + B v / (2 * τ)) / (B v / (2 * τ)) = 2 * τ + 1` using `by field_simp`. Rewrite using `[e]`. Conclude with `pow_le_pow_left₀ (by positivity) (by linarith) _`. Use `_ = 9 ^ (s * f) * (τ ^ (2 * f)) ^ s := by`.

Rewrite using `[Finset.prod_const, Finset.card_univ, ← hf, ← pow_mul, mul_pow, ← pow_mul, show (9:ℝ) = 3 ^ 2 by norm_num, ← pow_mul]`. Apply the tactic sequence `congr 2 <;> ring`. Use `_ = _ := by rw [hτpow]`.
-/
theorem box_count_alt : BoxCount := by
  intro ι _ s Λ ν B hν hB hΛ
  apply finite_of_finset_card_bound
  intro S hS
  set Q := (∏ v, B v ^ 2) / ν with hQ
  set M := max 1 Q with hM
  have hM1 : 1 ≤ M := le_max_left _ _
  have hM0 : 0 < M := by linarith
  have hPB : 0 < ∏ v, B v ^ 2 := Finset.prod_pos fun v _ => pow_pos (hB v) 2
  rcases isEmpty_or_nonempty ι with hι | hι
  · have h1 : S.card ≤ 1 := Finset.card_le_one.mpr fun a _ b _ => Subsingleton.elim a b
    have h2 : (1:ℝ) ≤ 9 ^ (s * Fintype.card ι) * M ^ s :=
      one_le_mul_of_one_le_of_one_le (one_le_pow₀ (by norm_num)) (one_le_pow₀ hM1)
    have h3 : (S.card : ℝ) ≤ 1 := by exact_mod_cast h1
    linarith
  · set f := Fintype.card ι with hf
    have hf0 : 0 < f := Fintype.card_pos
    have hfR : (0:ℝ) < f := by exact_mod_cast hf0
    set τ := M ^ (1 / (2 * (f:ℝ))) with hτ
    have hτ1 : 1 ≤ τ := Real.one_le_rpow hM1 (by positivity)
    have hτ0 : 0 < τ := by linarith
    have hτpow : τ ^ (2 * f) = M := by
      rw [hτ, ← Real.rpow_natCast, ← Real.rpow_mul hM0.le]
      have : 1 / (2 * (f:ℝ)) * ((2 * f : ℕ) : ℝ) = 1 := by push_cast; field_simp
      rw [this, Real.rpow_one]
    have hprod : ∏ v, (2 * (B v / (2 * τ))) ^ 2 ≤ ν := by
      have e : ∀ v, (2 * (B v / (2 * τ))) ^ 2 = B v ^ 2 / τ ^ 2 := fun v => by field_simp
      simp only [e]
      rw [Finset.prod_div_distrib, Finset.prod_const, Finset.card_univ, ← pow_mul, ← hf, hτpow,
        div_le_iff₀ hM0]
      have : Q ≤ M := le_max_right _ _
      rw [hQ, div_le_iff₀ hν] at this
      linarith
    have := card_separated_set_le_prod S (fun v => B v / (2 * τ)) B (fun v => by have := hB v; positivity)
      (fun v => (hB v).le) (fun c hc => (hS hc).2) (by
        intro c hc d hd hcd
        by_contra hcon
        push_neg at hcon
        have hne : c - d ≠ 0 := sub_ne_zero.mpr hcd
        have h1 := hΛ (c - d) (Λ.sub_mem (hS hc).1 (hS hd).1) hne
        have hpos : ∀ v ∈ Finset.univ, 0 < ‖(c - d) v‖ ^ 2 := by
          intro v _
          by_contra h0
          have hz : ‖(c - d) v‖ ^ 2 = 0 := le_antisymm (not_lt.mp h0) (by positivity)
          have : ∏ v, ‖(c - d) v‖ ^ 2 = 0 := Finset.prod_eq_zero (Finset.mem_univ v) hz
          linarith
        have h2 : ∏ v, ‖(c - d) v‖ ^ 2 < ∏ v, (2 * (B v / (2 * τ))) ^ 2 :=
          Finset.prod_lt_prod_of_nonempty hpos (fun v _ =>
            pow_lt_pow_left₀ (hcon v) (norm_nonneg _) (by norm_num)) Finset.univ_nonempty
        linarith)
    refine this.trans ?_
    have hdim : finrank ℝ (EuclideanSpace ℂ (Fin s)) = 2 * s := by
      rw [← Module.finrank_mul_finrank ℝ ℂ (EuclideanSpace ℂ (Fin s)), Complex.finrank_real_complex,
        finrank_euclideanSpace, Fintype.card_fin]
    rw [hdim]
    calc ∏ v, ((B v + B v / (2 * τ)) / (B v / (2 * τ))) ^ (2 * s) ≤ ∏ _v : ι, (3 * τ) ^ (2 * s) := by
          refine Finset.prod_le_prod (fun v _ => by have := hB v; positivity) fun v _ => ?_
          have hb := hB v
          have e : (B v + B v / (2 * τ)) / (B v / (2 * τ)) = 2 * τ + 1 := by field_simp
          rw [e]
          exact pow_le_pow_left₀ (by positivity) (by linarith) _
      _ = 9 ^ (s * f) * (τ ^ (2 * f)) ^ s := by
          rw [Finset.prod_const, Finset.card_univ, ← hf, ← pow_mul, mul_pow, ← pow_mul,
            show (9:ℝ) = 3 ^ 2 by norm_num, ← pow_mul]
          congr 2 <;> ring
      _ = _ := by rw [hτpow]

open InnerProductSpace

section Hadamard

variable {U : Type*} [NormedAddCommGroup U] [InnerProductSpace ℂ U]

noncomputable def s5bL {r : ℕ} (a : Fin r → U) : Matrix (Fin r) (Fin r) ℂ :=
  Matrix.of fun n i =>
    if i < n then inner ℂ (gramSchmidt ℂ a i) (a n) / ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)
    else if i = n then 1 else 0

/- English proof (translation)
Rewrite using `[Matrix.det_of_lowerTriangular]`. Simplify using `[s5bL]`. Introduce `i j hij`. Establish `h : i < j` using `by simpa using hij`. Simplify using `[s5bL, not_lt.2 h.le, h.ne']`.
-/
lemma det_gramSchmidt_coeff_eq_one {r : ℕ} (a : Fin r → U) : (s5bL a).det = 1 := by
  rw [Matrix.det_of_lowerTriangular]
  · simp [s5bL]
  · intro i j hij
    have h : i < j := by simpa using hij
    simp [s5bL, not_lt.2 h.le, h.ne']

/- English proof (translation)
Establish `h0` using `gramSchmidt_def'' ℂ a n`. Establish `: ∀ i, s5bL a n i • gramSchmidt ℂ a i = (if i = n then gramSchmidt ℂ a i else 0) + (if i < n then (inner ℂ (gramSchmidt ℂ a i) (a n) / ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)) • gramSchmidt ℂ a i else 0)`. Introduce `i`. Simplify using `only [s5bL, Matrix.of_apply]`. Break down `lt_trichotomy i n with h | h | h` into its components or cases.

Simplify using `[h, h.ne]`. Simplify using `[h]`. Simplify using `[not_lt.2 h.le, h.ne']`. Simplify using `only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Rewrite using `[← Finset.sum_filter]`.

Establish `hf : Finset.univ.filter (fun i => i < n) = Finset.Iio n` using `by ext i; simp`. Rewrite using `[hf]`. Conclude with `h0`.
-/
lemma eq_sum_gramSchmidt_coeff {r : ℕ} (a : Fin r → U) (n : Fin r) :
    a n = ∑ i, s5bL a n i • gramSchmidt ℂ a i := by
  have h0 := gramSchmidt_def'' ℂ a n
  have : ∀ i, s5bL a n i • gramSchmidt ℂ a i = (if i = n then gramSchmidt ℂ a i else 0) +
      (if i < n then (inner ℂ (gramSchmidt ℂ a i) (a n) / ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)) •
        gramSchmidt ℂ a i else 0) := by
    intro i; simp only [s5bL, Matrix.of_apply]
    rcases lt_trichotomy i n with h | h | h
    · simp [h, h.ne]
    · simp [h]
    · simp [not_lt.2 h.le, h.ne']
  simp only [this, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.mem_univ, if_true]
  rw [← Finset.sum_filter]
  have hf : Finset.univ.filter (fun i => i < n) = Finset.Iio n := by ext i; simp
  rw [hf]; exact h0

/- English proof (translation)
Establish `h1 : inner ℂ (gramSchmidt ℂ a n) (a n) = ((‖gramSchmidt ℂ a n‖ ^ 2 : ℝ) : ℂ)`. Establish `h0` using `gramSchmidt_def'' ℂ a n`. Establish `h2 : inner ℂ (gramSchmidt ℂ a n) (a n) = inner ℂ (gramSchmidt ℂ a n) _` using `congrArg (inner ℂ (gramSchmidt ℂ a n)) h0`. Rewrite using `[h2, inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]`. Use `push_cast`.

Both sides reduce to the same expression. Introduce `i hi`. Rewrite using `[inner_smul_right, gramSchmidt_orthogonal ℂ a (Finset.mem_Iio.1 hi).ne', mul_zero]`. Establish `h2 : ‖gramSchmidt ℂ a n‖ ^ 2 ≤ ‖gramSchmidt ℂ a n‖ * ‖a n‖`. Use `norm_inner_le_norm (𝕜 := ℂ) (gramSchmidt ℂ a n) (a n)` as an intermediate fact.

Rewrite `this` using `[h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)]`. Conclude with `this`. Distinguish the cases in `h0 : ‖gramSchmidt ℂ a n‖ = 0`. Rewrite using `[h0]`. Check the signs of the components of the expression.

Establish `: 0 < ‖gramSchmidt ℂ a n‖` using `lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)`. Use the polynomial consequences of the given equalities and inequalities.
-/
lemma norm_gramSchmidt_le {r : ℕ} (a : Fin r → U) (n : Fin r) : ‖gramSchmidt ℂ a n‖ ≤ ‖a n‖ := by
  have h1 : inner ℂ (gramSchmidt ℂ a n) (a n) = ((‖gramSchmidt ℂ a n‖ ^ 2 : ℝ) : ℂ) := by
    have h0 := gramSchmidt_def'' ℂ a n
    have h2 : inner ℂ (gramSchmidt ℂ a n) (a n) = inner ℂ (gramSchmidt ℂ a n) _ :=
      congrArg (inner ℂ (gramSchmidt ℂ a n)) h0
    rw [h2, inner_add_right, inner_sum, Finset.sum_eq_zero, add_zero, inner_self_eq_norm_sq_to_K]
    · push_cast; rfl
    · intro i hi
      rw [inner_smul_right, gramSchmidt_orthogonal ℂ a (Finset.mem_Iio.1 hi).ne', mul_zero]
  have h2 : ‖gramSchmidt ℂ a n‖ ^ 2 ≤ ‖gramSchmidt ℂ a n‖ * ‖a n‖ := by
    have := norm_inner_le_norm (𝕜 := ℂ) (gramSchmidt ℂ a n) (a n)
    rw [h1, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by positivity)] at this
    exact this
  by_cases h0 : ‖gramSchmidt ℂ a n‖ = 0
  · rw [h0]; positivity
  · have : 0 < ‖gramSchmidt ℂ a n‖ := lt_of_le_of_ne (norm_nonneg _) (Ne.symm h0)
    nlinarith

/- English proof (translation)
Establish `: (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)) = L * (Matrix.of fun i k => B (g i) (g' k)) * L'ᴴ`. Use extensionality with `a b`. Simplify using `only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum, LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul, Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations. Rewrite using `[this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]`.
-/
lemma det_sesquilinear_change_basis {V₁ V₂ : Type*} [AddCommGroup V₁] [Module ℂ V₁] [AddCommGroup V₂] [Module ℂ V₂]
    (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) {j : ℕ} (L L' : Matrix (Fin j) (Fin j) ℂ) (g : Fin j → V₁)
    (g' : Fin j → V₂) :
    (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)).det =
      L.det * (Matrix.of fun i k => B (g i) (g' k)).det * star L'.det := by
  have : (Matrix.of fun a b => B (∑ i, L a i • g i) (∑ k, L' b k • g' k)) =
      L * (Matrix.of fun i k => B (g i) (g' k)) * L'ᴴ := by
    ext a b
    simp only [Matrix.of_apply, Matrix.mul_apply, Matrix.conjTranspose_apply, map_sum,
      LinearMap.sum_apply, map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul,
      Finset.sum_mul, Finset.mul_sum, starRingEnd_apply]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [this, Matrix.det_mul, Matrix.det_mul, Matrix.det_conjTranspose]

/- English proof (translation)
Establish `e : Matrix.gram ℂ a = (Matrix.of fun p q => (innerₛₗ ℂ).flip (∑ i, s5bL a p i • gramSchmidt ℂ a i) (∑ k, s5bL a q k • gramSchmidt ℂ a k))ᵀ`. Use extensionality with `p q`. Simplify using `only [Matrix.transpose_apply, Matrix.of_apply, ← eq_sum_gramSchmidt_coeff, Matrix.gram_apply]`. Both sides reduce to the same expression. Rewrite using `[e, Matrix.det_transpose, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one]`.

Establish `: (Matrix.of fun i k => (innerₛₗ ℂ).flip (gramSchmidt ℂ a i) (gramSchmidt ℂ a k)) = Matrix.diagonal fun i => ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2)`. Use extensionality with `i k`. Distinguish the cases in `h : i = k`. Substitute `h` using the available equality. Simplify using `[inner_self_eq_norm_sq_to_K]`.

Simplify using `[Matrix.diagonal_apply_ne _ h, gramSchmidt_orthogonal ℂ a (Ne.symm h)]`. Rewrite using `[this, Matrix.det_diagonal]`. Simplify using the standard rewrite rules.
-/
lemma det_gram_eq_prod_gramSchmidt_norm_sq {r : ℕ} (a : Fin r → U) :
    (Matrix.gram ℂ a).det = ∏ i, ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2) := by
  have e : Matrix.gram ℂ a = (Matrix.of fun p q => (innerₛₗ ℂ).flip
      (∑ i, s5bL a p i • gramSchmidt ℂ a i) (∑ k, s5bL a q k • gramSchmidt ℂ a k))ᵀ := by
    ext p q
    simp only [Matrix.transpose_apply, Matrix.of_apply, ← eq_sum_gramSchmidt_coeff, Matrix.gram_apply]; rfl
  rw [e, Matrix.det_transpose, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one]
  have : (Matrix.of fun i k => (innerₛₗ ℂ).flip (gramSchmidt ℂ a i) (gramSchmidt ℂ a k)) =
      Matrix.diagonal fun i => ((‖gramSchmidt ℂ a i‖ : ℂ) ^ 2) := by
    ext i k
    by_cases h : i = k
    · subst h; simp [inner_self_eq_norm_sq_to_K]
    · simp [Matrix.diagonal_apply_ne _ h, gramSchmidt_orthogonal ℂ a (Ne.symm h)]
  rw [this, Matrix.det_diagonal]; simp

/- English proof (translation)
Rewrite using `[det_gram_eq_prod_gramSchmidt_norm_sq, norm_prod]`. Simplify using `only [norm_pow, Complex.norm_real, norm_norm]`. Rewrite using `[Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]`.
-/
lemma sqrt_det_gram_eq_prod_norm {r : ℕ} (a : Fin r → U) :
    Real.sqrt ‖(Matrix.gram ℂ a).det‖ = ∏ i, ‖gramSchmidt ℂ a i‖ := by
  rw [det_gram_eq_prod_gramSchmidt_norm_sq, norm_prod]
  simp only [norm_pow, Complex.norm_real, norm_norm]
  rw [Finset.prod_pow, Real.sqrt_sq (Finset.prod_nonneg fun _ _ => norm_nonneg _)]

/- English proof (translation)
Introduce `U _ _ r a`. Establish `h1 : Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ ∏ b, ‖a b‖`. Rewrite using `[sqrt_det_gram_eq_prod_norm]`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le a i`. Use `⟨h1, fun R hR => h1.trans ?_⟩` and prove the remaining obligations.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem gram_hadamard_inequality : GramHadamard := by
  intro U _ _ r a
  have h1 : Real.sqrt ‖(Matrix.gram ℂ a).det‖ ≤ ∏ b, ‖a b‖ := by
    rw [sqrt_det_gram_eq_prod_norm]
    exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le a i
  refine ⟨h1, fun R hR => h1.trans ?_⟩
  calc ∏ b, ‖a b‖ ≤ ∏ _b : Fin r, R := Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun b _ => hR b
    _ = R ^ r := by simp

/- English proof (translation)
Set `a : Fin j → EuclideanSpace ℂ (Fin j)` to `fun i => WithLp.toLp 2 (N i)`. Establish `hg : Matrix.gram ℂ a = ((starRingEnd ℂ).mapMatrix N) * Nᵀ`. Use extensionality with `p q`. Simplify using `[Matrix.gram_apply, a, Matrix.mul_apply, PiLp.inner_apply, mul_comm]`. Establish `hdet : ‖(Matrix.gram ℂ a).det‖ = ‖N.det‖ ^ 2`.

Rewrite using `[hg, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, RCLike.norm_conj]`. Expand and normalize the polynomial expressions, which then agree. Establish `h1` using `sqrt_det_gram_eq_prod_norm a`. Rewrite `h1` using `[hdet, Real.sqrt_sq (norm_nonneg _)]`. Rewrite using `[h1]`.

Use `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_` and prove the remaining obligations. Use `(norm_gramSchmidt_le a i).trans (le_of_eq ?_)` and prove the remaining obligations. Simplify using `[a, EuclideanSpace.norm_eq]`.
-/
lemma norm_det_le_prod_row_norms {j : ℕ} (N : Matrix (Fin j) (Fin j) ℂ) :
    ‖N.det‖ ≤ ∏ i, Real.sqrt (∑ k, ‖N i k‖ ^ 2) := by
  let a : Fin j → EuclideanSpace ℂ (Fin j) := fun i => WithLp.toLp 2 (N i)
  have hg : Matrix.gram ℂ a = ((starRingEnd ℂ).mapMatrix N) * Nᵀ := by
    ext p q
    simp [Matrix.gram_apply, a, Matrix.mul_apply, PiLp.inner_apply, mul_comm]
  have hdet : ‖(Matrix.gram ℂ a).det‖ = ‖N.det‖ ^ 2 := by
    rw [hg, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, RCLike.norm_conj]
    ring
  have h1 := sqrt_det_gram_eq_prod_norm a
  rw [hdet, Real.sqrt_sq (norm_nonneg _)] at h1
  rw [h1]
  refine Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => ?_
  refine (norm_gramSchmidt_le a i).trans (le_of_eq ?_)
  simp [a, EuclideanSpace.norm_eq]

/- English proof (translation)
Establish `e : inner ℂ (∑ k, c k • h k) (∑ k, c k • h k) = ((∑ k, ‖c k • h k‖ ^ 2 : ℝ) : ℂ)`. Simplify using `only [sum_inner, inner_sum]`. Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_eq_single k]`.

Rewrite using `[inner_self_eq_norm_sq_to_K]`. Both sides reduce to the same expression. Introduce `l _ hl`. Rewrite using `[inner_smul_left, inner_smul_right, horth l k hl]`. Simplify using the standard rewrite rules.

Simplify using the standard rewrite rules. Establish `e2 : ‖∑ k, c k • h k‖ ^ 2 = ∑ k, ‖c k • h k‖ ^ 2`. Use `inner_self_eq_norm_sq (𝕜 := ℂ) (∑ k, c k • h k)` as an intermediate fact. Rewrite `this` using `[e]`. Rewrite using `[← this]`.

Conclude with `(Complex.ofReal_re _).symm`. Rewrite using `[e2]`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Rewrite using `[norm_smul, mul_pow]`. Establish `: ‖h k‖ ^ 2 ≤ 1` using `pow_le_one₀ (norm_nonneg _) (h1 k)`.

Use polynomial arithmetic with `[sq_nonneg ‖c k‖]`.
-/
lemma norm_sq_orthogonal_sum_le {j : ℕ} (h : Fin j → U) (horth : ∀ k l, k ≠ l → inner ℂ (h k) (h l) = 0)
    (h1 : ∀ k, ‖h k‖ ≤ 1) (c : Fin j → ℂ) : ‖∑ k, c k • h k‖ ^ 2 ≤ ∑ k, ‖c k‖ ^ 2 := by
  have e : inner ℂ (∑ k, c k • h k) (∑ k, c k • h k) = ((∑ k, ‖c k • h k‖ ^ 2 : ℝ) : ℂ) := by
    simp only [sum_inner, inner_sum]
    push_cast
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [Finset.sum_eq_single k]
    · rw [inner_self_eq_norm_sq_to_K]; rfl
    · intro l _ hl
      rw [inner_smul_left, inner_smul_right, horth l k hl]; simp
    · simp
  have e2 : ‖∑ k, c k • h k‖ ^ 2 = ∑ k, ‖c k • h k‖ ^ 2 := by
    have := inner_self_eq_norm_sq (𝕜 := ℂ) (∑ k, c k • h k)
    rw [e] at this
    rw [← this]; exact (Complex.ofReal_re _).symm
  rw [e2]
  refine Finset.sum_le_sum fun k _ => ?_
  rw [norm_smul, mul_pow]
  have : ‖h k‖ ^ 2 ≤ 1 := pow_le_one₀ (norm_nonneg _) (h1 k)
  nlinarith [sq_nonneg ‖c k‖]

end Hadamard

/- English proof (translation)
Use `set g := gramSchmidt ℂ y with hg`. Use `set g' := gramSchmidt ℂ y' with hg'`. Establish `e1 : (Matrix.of fun a b => B (y a) (y' b)).det = (Matrix.of fun i k => B (g i) (g' k)).det`. Establish `: (Matrix.of fun a b => B (y a) (y' b)) = Matrix.of fun a b => B (∑ i, s5bL y a i • g i) (∑ k, s5bL y' b k • g' k)`. Use extensionality with `a b`.

Simplify using `only [Matrix.of_apply, hg, hg', ← eq_sum_gramSchmidt_coeff]`. Rewrite using `[this, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one, det_gramSchmidt_coeff_eq_one]`. Simplify using the standard rewrite rules. Use `set gh : Fin j → V₂ := fun k => ((‖g' k‖⁻¹ : ℝ) : ℂ) • g' k with hgh`. Establish `e2 : ∀ i k, B (g i) (g' k) = (‖g' k‖ : ℂ) * B (g i) (gh k)`.

Introduce `i k`. Simplify using `only [hgh, LinearMap.map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul]`. Distinguish the cases in `h0 : ‖g' k‖ = 0`. Establish `: g' k = 0` using `norm_eq_zero.mp h0`. Simplify using `[this]`.

Rewrite using `[← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h0]`. Simplify using the standard rewrite rules. Use `set Nt : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun i k => B (g i) (gh k) with hNt`. Establish `e3 : (Matrix.of fun i k => B (g i) (g' k)).det = (∏ k, (‖g' k‖ : ℂ)) * Nt.det`. Rewrite using `[← Matrix.det_mul_row]`.

Use `congr 1`. Use extensionality with `i k`. Simplify using `only [Matrix.of_apply, hNt]`. Conclude with `e2 i k`. Establish `hgh_orth : ∀ k l, k ≠ l → inner ℂ (gh k) (gh l) = 0`.

Introduce `k l hkl`. Simplify using `only [hgh, inner_smul_left, inner_smul_right, hg', gramSchmidt_orthogonal ℂ y' hkl, mul_zero]`. Establish `hgh1 : ∀ k, ‖gh k‖ ≤ 1`. Introduce `k`. Simplify using `only [hgh, norm_smul, Complex.norm_real, norm_inv, norm_norm]`.

Distinguish the cases in `h0 : ‖g' k‖ = 0`. Simplify using `[h0]`. Rewrite using `[inv_mul_cancel₀ h0]`. Establish `hrow : ∀ i, Real.sqrt (∑ k, ‖Nt i k‖ ^ 2) ≤ c * ‖g i‖`. Introduce `i`.

Use `set T := ∑ k, ‖Nt i k‖ ^ 2 with hT`. Establish `hT0 : 0 ≤ T` using `Finset.sum_nonneg fun k _ => by positivity`. Use `set w := ∑ k, Nt i k • gh k with hw`. Establish `hBw : B (g i) w = (T : ℂ)`. Simplify using `only [hw, map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, hT]`.

Use `push_cast`. Use `Finset.sum_congr rfl fun k _ => ?_` and prove the remaining obligations. Establish `: B (g i) (gh k) = Nt i k` using `rfl`. Rewrite using `[this, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]`. Use `push_cast`.

Both sides reduce to the same expression. Establish `hwn : ‖w‖ ≤ Real.sqrt T` using `Real.le_sqrt_of_sq_le (norm_sq_orthogonal_sum_le gh hgh_orth hgh1 (fun k => Nt i k))`. Establish `h1` using `hB (g i) w`. Rewrite `h1` using `[hBw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0]`. Establish `h2 : T ≤ c * ‖g i‖ * Real.sqrt T` using `h1.trans (mul_le_mul_of_nonneg_left hwn (by positivity))`.

Break down `hT0.lt_or_eq with hp | hz` into its components or cases. Establish `hs : 0 < Real.sqrt T` using `Real.sqrt_pos.mpr hp`. Establish `hss : Real.sqrt T * Real.sqrt T = T` using `Real.mul_self_sqrt hT0`. Use the polynomial consequences of the given equalities and inequalities. Rewrite using `[← hz, Real.sqrt_zero]`.

Check the signs of the components of the expression. Rewrite using `[e1, e3, norm_mul, norm_prod]`. Simplify using `only [Complex.norm_real, norm_norm]`. Combine the equalities or inequalities in the displayed calculation. Apply `mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)` to reduce the goal to its premises.

Conclude with `(norm_det_le_prod_row_norms Nt).trans (Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun i _ => hrow i)`. Use `_ = _ := by`. Rewrite using `[Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_det_sesquilinear_le_gramSchmidt {V₁ V₂ : Type*} [NormedAddCommGroup V₁] [InnerProductSpace ℂ V₁]
    [NormedAddCommGroup V₂] [InnerProductSpace ℂ V₂] (B : V₁ →ₗ[ℂ] V₂ →ₗ⋆[ℂ] ℂ) (c : ℝ) (hc : 0 ≤ c)
    (hB : ∀ x y, ‖B x y‖ ≤ c * ‖x‖ * ‖y‖) {j : ℕ} (y : Fin j → V₁) (y' : Fin j → V₂) :
    ‖(Matrix.of fun a b => B (y a) (y' b)).det‖ ≤
      c ^ j * (∏ i, ‖gramSchmidt ℂ y i‖) * ∏ k, ‖gramSchmidt ℂ y' k‖ := by
  set g := gramSchmidt ℂ y with hg
  set g' := gramSchmidt ℂ y' with hg'
  have e1 : (Matrix.of fun a b => B (y a) (y' b)).det = (Matrix.of fun i k => B (g i) (g' k)).det := by
    have : (Matrix.of fun a b => B (y a) (y' b)) =
        Matrix.of fun a b => B (∑ i, s5bL y a i • g i) (∑ k, s5bL y' b k • g' k) := by
      ext a b; simp only [Matrix.of_apply, hg, hg', ← eq_sum_gramSchmidt_coeff]
    rw [this, det_sesquilinear_change_basis, det_gramSchmidt_coeff_eq_one, det_gramSchmidt_coeff_eq_one]; simp
  set gh : Fin j → V₂ := fun k => ((‖g' k‖⁻¹ : ℝ) : ℂ) • g' k with hgh
  have e2 : ∀ i k, B (g i) (g' k) = (‖g' k‖ : ℂ) * B (g i) (gh k) := by
    intro i k
    simp only [hgh, LinearMap.map_smulₛₗ, Complex.conj_ofReal, smul_eq_mul]
    by_cases h0 : ‖g' k‖ = 0
    · have : g' k = 0 := norm_eq_zero.mp h0
      simp [this]
    · rw [← mul_assoc, ← Complex.ofReal_mul, mul_inv_cancel₀ h0]; simp
  set Nt : Matrix (Fin j) (Fin j) ℂ := Matrix.of fun i k => B (g i) (gh k) with hNt
  have e3 : (Matrix.of fun i k => B (g i) (g' k)).det = (∏ k, (‖g' k‖ : ℂ)) * Nt.det := by
    rw [← Matrix.det_mul_row]; congr 1; ext i k; simp only [Matrix.of_apply, hNt]; exact e2 i k
  have hgh_orth : ∀ k l, k ≠ l → inner ℂ (gh k) (gh l) = 0 := by
    intro k l hkl
    simp only [hgh, inner_smul_left, inner_smul_right, hg', gramSchmidt_orthogonal ℂ y' hkl, mul_zero]
  have hgh1 : ∀ k, ‖gh k‖ ≤ 1 := by
    intro k
    simp only [hgh, norm_smul, Complex.norm_real, norm_inv, norm_norm]
    by_cases h0 : ‖g' k‖ = 0
    · simp [h0]
    · rw [inv_mul_cancel₀ h0]
  have hrow : ∀ i, Real.sqrt (∑ k, ‖Nt i k‖ ^ 2) ≤ c * ‖g i‖ := by
    intro i
    set T := ∑ k, ‖Nt i k‖ ^ 2 with hT
    have hT0 : 0 ≤ T := Finset.sum_nonneg fun k _ => by positivity
    set w := ∑ k, Nt i k • gh k with hw
    have hBw : B (g i) w = (T : ℂ) := by
      simp only [hw, map_sum, LinearMap.map_smulₛₗ, smul_eq_mul, hT]
      push_cast
      refine Finset.sum_congr rfl fun k _ => ?_
      have : B (g i) (gh k) = Nt i k := rfl
      rw [this, mul_comm, Complex.mul_conj, Complex.normSq_eq_norm_sq]; push_cast; rfl
    have hwn : ‖w‖ ≤ Real.sqrt T :=
      Real.le_sqrt_of_sq_le (norm_sq_orthogonal_sum_le gh hgh_orth hgh1 (fun k => Nt i k))
    have h1 := hB (g i) w
    rw [hBw, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg hT0] at h1
    have h2 : T ≤ c * ‖g i‖ * Real.sqrt T :=
      h1.trans (mul_le_mul_of_nonneg_left hwn (by positivity))
    rcases hT0.lt_or_eq with hp | hz
    · have hs : 0 < Real.sqrt T := Real.sqrt_pos.mpr hp
      have hss : Real.sqrt T * Real.sqrt T = T := Real.mul_self_sqrt hT0
      nlinarith
    · rw [← hz, Real.sqrt_zero]; positivity
  rw [e1, e3, norm_mul, norm_prod]
  simp only [Complex.norm_real, norm_norm]
  calc (∏ k, ‖g' k‖) * ‖Nt.det‖ ≤ (∏ k, ‖g' k‖) * ∏ i, (c * ‖g i‖) := by
        apply mul_le_mul_of_nonneg_left _ (Finset.prod_nonneg fun _ _ => norm_nonneg _)
        exact (norm_det_le_prod_row_norms Nt).trans
          (Finset.prod_le_prod (fun _ _ => Real.sqrt_nonneg _) fun i _ => hrow i)
    _ = _ := by
        rw [Finset.prod_mul_distrib, Finset.prod_const, Finset.card_univ, Fintype.card_fin]; ring

/- English proof (translation)
Introduce `V₁ V₂ _ _ _ _ B hB j y y'`. Use `norm_det_sesquilinear_le_gramSchmidt B 1 zero_le_one (fun x y => by rw [one_mul]; exact hB x y) y y'` as an intermediate fact. Rewrite `this` using `[one_pow, one_mul]`. Use `this.trans ?_` and prove the remaining obligations. Apply `mul_le_mul` to reduce the goal to its premises.

Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y i`. Conclude with `Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y' i`. Conclude with `Finset.prod_nonneg fun _ _ => norm_nonneg _`. Conclude with `Finset.prod_nonneg fun _ _ => norm_nonneg _`.
-/
theorem wedge_hadamard_inequality : WedgeHadamard := by
  intro V₁ V₂ _ _ _ _ B hB j y y'
  have := norm_det_sesquilinear_le_gramSchmidt B 1 zero_le_one (fun x y => by rw [one_mul]; exact hB x y) y y'
  rw [one_pow, one_mul] at this
  refine this.trans ?_
  apply mul_le_mul
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y i
  · exact Finset.prod_le_prod (fun _ _ => norm_nonneg _) fun i _ => norm_gramSchmidt_le y' i
  · exact Finset.prod_nonneg fun _ _ => norm_nonneg _
  · exact Finset.prod_nonneg fun _ _ => norm_nonneg _

/- English proof (translation)
Introduce `U₁ U₂ _ _ _ _ r u u' Z hZ`. Set `B : U₁ →ₗ[ℂ] U₂ →ₗ⋆[ℂ] ℂ` to `LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun w₁ w₂ => ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b) (by intro x x' y; simp only [inner_add_right, add_mul, Finset.sum_add_distrib]) (by intro c x y; simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul …`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)` and prove the remaining obligations. Use the proof step `(by intro x y y'; simp only [inner_add_right, map_add, mul_add, add_mul, Finset.sum_add_distrib])`. Use the proof step `(by intro c x y; simp only [inner_smul_right, map_mul, smul_eq_mul, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)` and prove the remaining obligations. Establish `hBapp : ∀ w₁ w₂, B w₁ w₂ = ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b` using `fun _ _ => rfl`. Establish `hW` using `norm_det_sesquilinear_le_gramSchmidt B 2 (by norm_num) (fun x y => by rw [hBapp]; exact hZ x y) u u'`. Rewrite `hW` using `[← sqrt_det_gram_eq_prod_norm, ← sqrt_det_gram_eq_prod_norm]`. Establish `hM : (Matrix.of fun c d => B (u c) (u' d)) = (Matrix.gram ℂ u)ᵀ * Z * ((starRingEnd ℂ).mapMatrix (Matrix.gram ℂ u'))`.

Use extensionality with `c d`. Simplify using `only [Matrix.of_apply, hBapp, Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring` and prove the remaining obligations. Rewrite `hW` using `[hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, norm_mul, RCLike.norm_conj]`.

Use `set X := Real.sqrt ‖(Matrix.gram ℂ u).det‖ with hX`. Use `set X' := Real.sqrt ‖(Matrix.gram ℂ u').det‖ with hX'`. Establish `hX2 : ‖(Matrix.gram ℂ u).det‖ = X * X` using `(Real.mul_self_sqrt (norm_nonneg _)).symm`. Establish `hX2' : ‖(Matrix.gram ℂ u').det‖ = X' * X'` using `(Real.mul_self_sqrt (norm_nonneg _)).symm`. Rewrite `hW` using `[hX2, hX2']`.

Establish `hX0 : 0 ≤ X` using `Real.sqrt_nonneg _`. Establish `hX0' : 0 ≤ X'` using `Real.sqrt_nonneg _`. Break down `(mul_nonneg hX0 hX0').lt_or_eq with hp | hz` into its components or cases. Establish `: (X * X') * (X * X' * ‖Z.det‖) ≤ (X * X') * 2 ^ r` using `by nlinarith`. Conclude with `le_of_mul_le_mul_left this hp`.

Rewrite using `[← hz, zero_mul]`. Check the signs of the components of the expression.
-/
theorem absolute_value_bound : AbsA := by
  intro U₁ U₂ _ _ _ _ r u u' Z hZ
  let B : U₁ →ₗ[ℂ] U₂ →ₗ⋆[ℂ] ℂ := LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ)
    (fun w₁ w₂ => ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b)
    (by intro x x' y; simp only [inner_add_right, add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp only [inner_smul_right, RingHom.id_apply, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
    (by intro x y y'; simp only [inner_add_right, map_add, mul_add, add_mul, Finset.sum_add_distrib])
    (by intro c x y; simp only [inner_smul_right, map_mul, smul_eq_mul, Finset.mul_sum]
        refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring)
  have hBapp : ∀ w₁ w₂, B w₁ w₂ =
      ∑ a, ∑ b, inner ℂ (u a) w₁ * conj (inner ℂ (u' b) w₂) * Z a b := fun _ _ => rfl
  have hW := norm_det_sesquilinear_le_gramSchmidt B 2 (by norm_num) (fun x y => by rw [hBapp]; exact hZ x y) u u'
  rw [← sqrt_det_gram_eq_prod_norm, ← sqrt_det_gram_eq_prod_norm] at hW
  have hM : (Matrix.of fun c d => B (u c) (u' d)) =
      (Matrix.gram ℂ u)ᵀ * Z * ((starRingEnd ℂ).mapMatrix (Matrix.gram ℂ u')) := by
    ext c d
    simp only [Matrix.of_apply, hBapp, Matrix.mul_apply, Matrix.transpose_apply, Matrix.gram_apply,
      RingHom.mapMatrix_apply, Matrix.map_apply, Finset.sum_mul]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun _ _ => Finset.sum_congr rfl fun _ _ => by ring
  rw [hM, Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, ← RingHom.map_det, norm_mul, norm_mul,
    RCLike.norm_conj] at hW
  set X := Real.sqrt ‖(Matrix.gram ℂ u).det‖ with hX
  set X' := Real.sqrt ‖(Matrix.gram ℂ u').det‖ with hX'
  have hX2 : ‖(Matrix.gram ℂ u).det‖ = X * X := (Real.mul_self_sqrt (norm_nonneg _)).symm
  have hX2' : ‖(Matrix.gram ℂ u').det‖ = X' * X' := (Real.mul_self_sqrt (norm_nonneg _)).symm
  rw [hX2, hX2'] at hW
  have hX0 : 0 ≤ X := Real.sqrt_nonneg _
  have hX0' : 0 ≤ X' := Real.sqrt_nonneg _
  rcases (mul_nonneg hX0 hX0').lt_or_eq with hp | hz
  · have : (X * X') * (X * X' * ‖Z.det‖) ≤ (X * X') * 2 ^ r := by nlinarith
    exact le_of_mul_le_mul_left this hp
  · rw [← hz, zero_mul]; positivity

open MeasureTheory Set in
/- English proof (translation)
Establish `hsplit : Ioi (0:ℝ) = Ioc 0 H ∪ Ioi H` using `(Ioc_union_Ioi_eq_Ioi hH.le).symm`. Establish `e1 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => y) (Ioc 0 H)`. Introduce `y hy`. Establish `: y / H ≤ 1` using `by rw [div_le_one hH]; exact hy.2`. Simplify using `only [max_eq_left this]`.

Evaluate the numerical expressions. Establish `e2 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => H ^ 3 * y ^ (-2 : ℝ)) (Ioi H)`. Introduce `y hy`. Establish `hy' : H < y` using `hy`. Establish `hy0 : 0 < y` using `by linarith`.

Establish `: 1 ≤ y / H` using `by rw [le_div_iff₀ hH]; linarith`. Simplify using `only [max_eq_right this]`. Rewrite using `[Real.rpow_neg hy0.le, Real.rpow_two]`. Clear the denominators using the available nonvanishing facts. Establish `i1 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioc 0 H)`.

Rewrite using `[integrableOn_congr_fun e1 measurableSet_Ioc]`. Conclude with `(continuous_id.integrableOn_Icc (a := 0) (b := H)).mono_set Ioc_subset_Icc_self`. Establish `i2 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi H)`. Rewrite using `[integrableOn_congr_fun e2 measurableSet_Ioi]`. Conclude with `(integrableOn_Ioi_rpow_of_lt (by norm_num) hH).const_mul _`.

Use `⟨by rw [hsplit]; exact i1.union i2, ?_⟩` and prove the remaining obligations. Rewrite using `[hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2, setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2, integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hH, ← intervalIntegral.integral_of_le hH.le, integral_id …`. Establish `: H ^ ((-2:ℝ) + 1) = H⁻¹`. Rewrite using `[show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]`. Rewrite using `[this]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_radial_inverse_cube (H : ℝ) (hH : 0 < H) :
    IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi 0) ∧
      ∫ y in Ioi (0:ℝ), y * ((max 1 (y / H)) ^ 3)⁻¹ = 3 * H ^ 2 / 2 := by
  have hsplit : Ioi (0:ℝ) = Ioc 0 H ∪ Ioi H := (Ioc_union_Ioi_eq_Ioi hH.le).symm
  have e1 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => y) (Ioc 0 H) := by
    intro y hy
    have : y / H ≤ 1 := by rw [div_le_one hH]; exact hy.2
    simp only [max_eq_left this]; norm_num
  have e2 : EqOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (fun y => H ^ 3 * y ^ (-2 : ℝ)) (Ioi H) := by
    intro y hy
    have hy' : H < y := hy
    have hy0 : 0 < y := by linarith
    have : 1 ≤ y / H := by rw [le_div_iff₀ hH]; linarith
    simp only [max_eq_right this]
    rw [Real.rpow_neg hy0.le, Real.rpow_two]
    field_simp
  have i1 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioc 0 H) := by
    rw [integrableOn_congr_fun e1 measurableSet_Ioc]
    exact (continuous_id.integrableOn_Icc (a := 0) (b := H)).mono_set Ioc_subset_Icc_self
  have i2 : IntegrableOn (fun y : ℝ => y * ((max 1 (y / H)) ^ 3)⁻¹) (Ioi H) := by
    rw [integrableOn_congr_fun e2 measurableSet_Ioi]
    exact (integrableOn_Ioi_rpow_of_lt (by norm_num) hH).const_mul _
  refine ⟨by rw [hsplit]; exact i1.union i2, ?_⟩
  rw [hsplit, setIntegral_union (Ioc_disjoint_Ioi le_rfl) measurableSet_Ioi i1 i2,
    setIntegral_congr_fun measurableSet_Ioc e1, setIntegral_congr_fun measurableSet_Ioi e2,
    integral_const_mul, integral_Ioi_rpow_of_lt (by norm_num) hH,
    ← intervalIntegral.integral_of_le hH.le, integral_id]
  have : H ^ ((-2:ℝ) + 1) = H⁻¹ := by
    rw [show (-2:ℝ) + 1 = -1 by norm_num, Real.rpow_neg_one]
  rw [this]; field_simp; ring

open MeasureTheory in
/- English proof (translation)
Take `⟨hi, hv⟩` from `integral_radial_inverse_cube H hH`. Establish `hdim : finrank ℝ ℂ = 2` using `Complex.finrank_real_complex`. Prove the components needed by the constructor for the conclusion. Use `(integrable_fun_norm_addHaar (volume : Measure ℂ) (f := fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)).2 (by` as an intermediate fact. Simplify `hi)` using `only [hdim, Nat.add_one_sub_one, pow_one, smul_eq_mul]`.

Conclude with `this`. Use `integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)` as an intermediate fact. Rewrite using `[this, hdim]`. Simplify using `only [Nat.add_one_sub_one, pow_one, smul_eq_mul]`. Rewrite using `[hv]`.

Establish `hb : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi`. Rewrite using `[measureReal_def, Complex.volume_ball]`. Simplify using the standard rewrite rules. Rewrite using `[hb]`. Simplify using the standard rewrite rules.

Expand and normalize the polynomial expressions, which then agree.
-/
lemma integral_inverse_cube_plateau (H : ℝ) (hH : 0 < H) :
    Integrable (fun z : ℂ => ((max 1 (‖z‖ / H)) ^ 3)⁻¹) ∧
      ∫ z : ℂ, ((max 1 (‖z‖ / H)) ^ 3)⁻¹ = 3 * Real.pi * H ^ 2 := by
  obtain ⟨hi, hv⟩ := integral_radial_inverse_cube H hH
  have hdim : finrank ℝ ℂ = 2 := Complex.finrank_real_complex
  constructor
  · have := (integrable_fun_norm_addHaar (volume : Measure ℂ)
      (f := fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)).2 (by
        simpa only [hdim, Nat.add_one_sub_one, pow_one, smul_eq_mul] using hi)
    exact this
  · have := integral_fun_norm_addHaar (volume : Measure ℂ) (fun y : ℝ => ((max 1 (y / H)) ^ 3)⁻¹)
    rw [this, hdim]
    simp only [Nat.add_one_sub_one, pow_one, smul_eq_mul]
    rw [hv]
    have hb : (volume : Measure ℂ).real (Metric.ball 0 1) = Real.pi := by
      rw [measureReal_def, Complex.volume_ball]; simp
    rw [hb]; simp; ring

open MeasureTheory Metric in
/- English proof (translation)
Introduce `ι _ Λ H hH hΛ`. Establish `hH0 : 0 < H` using `by linarith`. Establish `hpi` using `Real.pi_pos`. Use `set f := Fintype.card ι with hf`. Set `w₁ : ℂ → ℝ` to `fun z => ((max 1 (‖z‖ / H)) ^ 3)⁻¹`.

Set `W : (ι → ℂ) → ℝ` to `fun x => ∏ v, w₁ (x v)`. Take `⟨hw1i, hw1v⟩` from `integral_inverse_cube_plateau H hH0`. Establish `hWi : Integrable W` using `Integrable.fintype_prod (f := fun _ => w₁) (μ := fun _ => volume) (fun _ => hw1i)`. Establish `hWv : ∫ x, W x = (3 * Real.pi * H ^ 2) ^ f`. Use `integral_fintype_prod_volume_eq_pow (ι := ι) w₁` as an intermediate fact.

Rewrite `this` using `[hw1v]`. Conclude with `this`. Establish `hw10 : ∀ z, 0 < w₁ z` using `fun z => by simp only [w₁]; positivity`. Establish `hW0 : ∀ x, 0 ≤ W x` using `fun x => Finset.prod_nonneg fun v _ => (hw10 _).le`. Set `P : (ι → ℂ) → Set (ι → ℂ)` to `fun c => Set.pi Set.univ fun v => ball (c v) (1 / 2)`.

Establish `hPm : ∀ c, MeasurableSet (P c)` using `fun c => MeasurableSet.univ_pi fun v => measurableSet_ball`. Establish `hPvol' : ∀ c, (volume : Measure (ι → ℂ)) (P c) = ENNReal.ofReal ((Real.pi / 4) ^ f)`. Introduce `c`. Simplify using `only [P]`. Rewrite using `[volume_pi_pi]`.

Simplify using `only [Complex.volume_ball]`. Rewrite using `[Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]`. Use `congr 1`. Rewrite using `[← ENNReal.ofReal_pow (by norm_num), ← NNReal.coe_real_pi, ← ENNReal.ofReal_coe_nnreal, ← ENNReal.ofReal_mul (by positivity)]`. Use `congr 1`.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish `hPvol : ∀ c, (volume : Measure (ι → ℂ)).real (P c) = (Real.pi / 4) ^ f`. Introduce `c; rw [measureReal_def, hPvol', ENNReal.toReal_ofReal (by positivity)]`. Establish `hcomp : ∀ c y, y ∈ P c → W c ≤ (27 / 8) ^ f * W y`.

Introduce `c y hy`. Simplify using `only [W]`. Rewrite using `[hf, Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]`. Use `Finset.prod_le_prod (fun v _ => (hw10 _).le) fun v _ => ?_` and prove the remaining obligations. Establish `h1` using `hy v (Set.mem_univ v)`.

Rewrite `h1` using `[mem_ball, dist_eq_norm]`. Establish `h2 : ‖y v‖ ≤ ‖c v‖ + 1 / 2`. Establish `: ‖y v‖ ≤ ‖y v - c v‖ + ‖c v‖` using `by simpa using norm_add_le (y v - c v) (c v)`. Combine the linear equalities and inequalities to obtain the conclusion. Use `set a := max 1 (‖c v‖ / H) with ha`.

Use `set b := max 1 (‖y v‖ / H) with hb`. Establish `ha1 : 1 ≤ a` using `le_max_left _ _`. Establish `hb1 : 1 ≤ b` using `le_max_left _ _`. Establish `hba : b ≤ 3 / 2 * a`. Apply `max_le (by linarith)` to reduce the goal to its premises.

Establish `h3 : ‖c v‖ / H ≤ a` using `le_max_right _ _`. Establish `h4 : ‖y v‖ / H ≤ ‖c v‖ / H + 1 / 2`. Rewrite using `[div_le_iff₀ hH0]`. Establish `: (‖c v‖ / H + 1 / 2) * H = ‖c v‖ + H / 2` using `by field_simp`. Rewrite using `[this]`.

Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion. Use `show (a ^ 3)⁻¹ ≤ 27 / 8 * (b ^ 3)⁻¹`. Establish `h5 : b ^ 3 ≤ 27 / 8 * a ^ 3`. Combine the equalities or inequalities in the displayed calculation.

Rewrite using `[← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]`. Conclude with `h5`. Establish `key : ∀ S : Finset Λ, ∑ D ∈ S, W D ≤ (41 * H ^ 2) ^ f`. Introduce `S`. Establish `D : Set.Pairwise (S : Set Λ) (Function.onFun Disjoint fun D : Λ => P D)`.

Introduce and unpack `c hc d hd hcd`. Rewrite using `[Function.onFun, Set.disjoint_left]`. Introduce `x hx hx'`. Establish `hne : (c : ι → ℂ) - d ≠ 0` using `sub_ne_zero.mpr fun h => hcd (Subtype.ext h)`. Take `⟨v₀, -⟩ : ∃ v, (c : ι → ℂ) v ≠ (d : ι → ℂ) v` from `Function.ne_iff.mp fun h => hcd (Subtype.ext h)`.

Establish `h1` using `hΛ _ (Λ.sub_mem c.2 d.2) hne`. Establish `h2` using `prod_lt_one_of_lt_one (fun v => ‖((c : ι → ℂ) - d) v‖) (fun v => norm_nonneg _) (fun v => by`. Establish `a1` using `hx v (Set.mem_univ v)`. Establish `a2` using `hx' v (Set.mem_univ v)`. Rewrite `a1`, `a2` using `[mem_ball, dist_eq_norm]`.

Establish `: ‖(c : ι → ℂ) v - (d : ι → ℂ) v‖ ≤ ‖x v - (d : ι → ℂ) v‖ + ‖x v - (c : ι → ℂ) v‖`. Establish `e : (c : ι → ℂ) v - (d : ι → ℂ) v = (x v - (d : ι → ℂ) v) - (x v - (c : ι → ℂ) v)`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `norm_sub_le _ _`.

Simplify using `only [Pi.sub_apply]`. Use the proof step `linarith) v₀`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hgi : Integrable fun y => (27 / 8 : ℝ) ^ f * W y` using `hWi.const_mul _`. Establish `h1 : ∀ D ∈ S, W D * (Real.pi / 4) ^ f ≤ ∫ y in P D, (27 / 8 : ℝ) ^ f * W y`.

Introduce `D _`. Rewrite using `[← hPvol D, mul_comm, ← smul_eq_mul]`. Conclude with `setIntegral_ge_of_const_le (hPm D) (by rw [hPvol']; exact ENNReal.ofReal_ne_top) (fun y hy => hcomp D y hy) hgi.integrableOn`. Establish `h2 : ∑ D ∈ S, ∫ y in P D, (27 / 8 : ℝ) ^ f * W y = ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y` using `(integral_biUnion_finset S (fun D _ => hPm D) D (fun D _ => hgi.integrableOn)).symm`. Establish `h3 : ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y ≤ ∫ y, (27 / 8 : ℝ) ^ f * W y` using `setIntegral_le_integral hgi (Filter.Eventually.of_forall fun y => by`.

Use `hW0 y` as an intermediate fact. Use the proof step `positivity)`. Establish `h4 : ∫ y, (27 / 8 : ℝ) ^ f * W y = (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f`. Rewrite using `[integral_const_mul, hWv]`. Establish `h5 : (∑ D ∈ S, W D) * (Real.pi / 4) ^ f ≤ (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f`.

Rewrite using `[Finset.sum_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `h6 : (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f ≤ (41 * H ^ 2) ^ f * (Real.pi / 4) ^ f`. Rewrite using `[← mul_pow, ← mul_pow]`. Apply `pow_le_pow_left₀ (by positivity)` to reduce the goal to its premises.

Use polynomial arithmetic with `[mul_pos hpi (pow_pos hH0 2)]`. Conclude with `le_of_mul_le_mul_right (h5.trans h6) (by positivity)`. Establish `hsum : Summable (fun D : Λ => W D)` using `summable_of_sum_le (fun D => hW0 D) key`. Conclude with `⟨hsum, hsum.tsum_le_of_sum_le key⟩`.
-/
theorem lattice_sum_alt : LatticeSum := by
  intro ι _ Λ H hH hΛ
  have hH0 : 0 < H := by linarith
  have hpi := Real.pi_pos
  set f := Fintype.card ι with hf
  let w₁ : ℂ → ℝ := fun z => ((max 1 (‖z‖ / H)) ^ 3)⁻¹
  let W : (ι → ℂ) → ℝ := fun x => ∏ v, w₁ (x v)
  obtain ⟨hw1i, hw1v⟩ := integral_inverse_cube_plateau H hH0
  have hWi : Integrable W :=
    Integrable.fintype_prod (f := fun _ => w₁) (μ := fun _ => volume) (fun _ => hw1i)
  have hWv : ∫ x, W x = (3 * Real.pi * H ^ 2) ^ f := by
    have := integral_fintype_prod_volume_eq_pow (ι := ι) w₁
    rw [hw1v] at this; exact this
  have hw10 : ∀ z, 0 < w₁ z := fun z => by simp only [w₁]; positivity
  have hW0 : ∀ x, 0 ≤ W x := fun x => Finset.prod_nonneg fun v _ => (hw10 _).le
  let P : (ι → ℂ) → Set (ι → ℂ) := fun c => Set.pi Set.univ fun v => ball (c v) (1 / 2)
  have hPm : ∀ c, MeasurableSet (P c) := fun c => MeasurableSet.univ_pi fun v => measurableSet_ball
  have hPvol' : ∀ c, (volume : Measure (ι → ℂ)) (P c) = ENNReal.ofReal ((Real.pi / 4) ^ f) := by
    intro c
    simp only [P]
    rw [volume_pi_pi]
    simp only [Complex.volume_ball]
    rw [Finset.prod_const, Finset.card_univ, ENNReal.ofReal_pow (by positivity)]
    congr 1
    rw [← ENNReal.ofReal_pow (by norm_num), ← NNReal.coe_real_pi, ← ENNReal.ofReal_coe_nnreal,
      ← ENNReal.ofReal_mul (by positivity)]
    congr 1; simp; ring
  have hPvol : ∀ c, (volume : Measure (ι → ℂ)).real (P c) = (Real.pi / 4) ^ f := by
    intro c; rw [measureReal_def, hPvol', ENNReal.toReal_ofReal (by positivity)]
  have hcomp : ∀ c y, y ∈ P c → W c ≤ (27 / 8) ^ f * W y := by
    intro c y hy
    simp only [W]
    rw [hf, Fintype.card, ← Finset.prod_const, ← Finset.prod_mul_distrib]
    refine Finset.prod_le_prod (fun v _ => (hw10 _).le) fun v _ => ?_
    have h1 := hy v (Set.mem_univ v)
    rw [mem_ball, dist_eq_norm] at h1
    have h2 : ‖y v‖ ≤ ‖c v‖ + 1 / 2 := by
      have : ‖y v‖ ≤ ‖y v - c v‖ + ‖c v‖ := by simpa using norm_add_le (y v - c v) (c v)
      linarith
    set a := max 1 (‖c v‖ / H) with ha
    set b := max 1 (‖y v‖ / H) with hb
    have ha1 : 1 ≤ a := le_max_left _ _
    have hb1 : 1 ≤ b := le_max_left _ _
    have hba : b ≤ 3 / 2 * a := by
      apply max_le (by linarith)
      have h3 : ‖c v‖ / H ≤ a := le_max_right _ _
      have h4 : ‖y v‖ / H ≤ ‖c v‖ / H + 1 / 2 := by
        rw [div_le_iff₀ hH0]
        have : (‖c v‖ / H + 1 / 2) * H = ‖c v‖ + H / 2 := by field_simp
        rw [this]; linarith
      linarith
    show (a ^ 3)⁻¹ ≤ 27 / 8 * (b ^ 3)⁻¹
    have h5 : b ^ 3 ≤ 27 / 8 * a ^ 3 := by
      calc b ^ 3 ≤ (3 / 2 * a) ^ 3 := pow_le_pow_left₀ (by linarith) hba 3
        _ = _ := by ring
    rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), inv_mul_eq_div, div_le_iff₀ (by positivity)]
    exact h5
  have key : ∀ S : Finset Λ, ∑ D ∈ S, W D ≤ (41 * H ^ 2) ^ f := by
    intro S
    have D : Set.Pairwise (S : Set Λ) (Function.onFun Disjoint fun D : Λ => P D) := by
      rintro c hc d hd hcd
      rw [Function.onFun, Set.disjoint_left]
      intro x hx hx'
      have hne : (c : ι → ℂ) - d ≠ 0 := sub_ne_zero.mpr fun h => hcd (Subtype.ext h)
      obtain ⟨v₀, -⟩ : ∃ v, (c : ι → ℂ) v ≠ (d : ι → ℂ) v :=
        Function.ne_iff.mp fun h => hcd (Subtype.ext h)
      have h1 := hΛ _ (Λ.sub_mem c.2 d.2) hne
      have h2 := prod_lt_one_of_lt_one (fun v => ‖((c : ι → ℂ) - d) v‖) (fun v => norm_nonneg _)
        (fun v => by
          have a1 := hx v (Set.mem_univ v)
          have a2 := hx' v (Set.mem_univ v)
          rw [mem_ball, dist_eq_norm] at a1 a2
          have : ‖(c : ι → ℂ) v - (d : ι → ℂ) v‖ ≤ ‖x v - (d : ι → ℂ) v‖ + ‖x v - (c : ι → ℂ) v‖ := by
            have e : (c : ι → ℂ) v - (d : ι → ℂ) v = (x v - (d : ι → ℂ) v) - (x v - (c : ι → ℂ) v) := by
              abel
            rw [e]; exact norm_sub_le _ _
          simp only [Pi.sub_apply]; linarith) v₀
      linarith
    have hgi : Integrable fun y => (27 / 8 : ℝ) ^ f * W y := hWi.const_mul _
    have h1 : ∀ D ∈ S, W D * (Real.pi / 4) ^ f ≤ ∫ y in P D, (27 / 8 : ℝ) ^ f * W y := by
      intro D _
      rw [← hPvol D, mul_comm, ← smul_eq_mul]
      exact setIntegral_ge_of_const_le (hPm D) (by rw [hPvol']; exact ENNReal.ofReal_ne_top)
        (fun y hy => hcomp D y hy) hgi.integrableOn
    have h2 : ∑ D ∈ S, ∫ y in P D, (27 / 8 : ℝ) ^ f * W y =
        ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y :=
      (integral_biUnion_finset S (fun D _ => hPm D) D (fun D _ => hgi.integrableOn)).symm
    have h3 : ∫ y in ⋃ D ∈ S, P D, (27 / 8 : ℝ) ^ f * W y ≤ ∫ y, (27 / 8 : ℝ) ^ f * W y :=
      setIntegral_le_integral hgi (Filter.Eventually.of_forall fun y => by
        have := hW0 y; positivity)
    have h4 : ∫ y, (27 / 8 : ℝ) ^ f * W y = (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f := by
      rw [integral_const_mul, hWv]
    have h5 : (∑ D ∈ S, W D) * (Real.pi / 4) ^ f ≤ (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f := by
      rw [Finset.sum_mul]
      calc _ ≤ ∑ D ∈ S, ∫ y in P D, (27 / 8 : ℝ) ^ f * W y := Finset.sum_le_sum h1
        _ = _ := h2
        _ ≤ _ := h3
        _ = _ := h4
    have h6 : (27 / 8 : ℝ) ^ f * (3 * Real.pi * H ^ 2) ^ f ≤ (41 * H ^ 2) ^ f * (Real.pi / 4) ^ f := by
      rw [← mul_pow, ← mul_pow]
      apply pow_le_pow_left₀ (by positivity)
      nlinarith [mul_pos hpi (pow_pos hH0 2)]
    exact le_of_mul_le_mul_right (h5.trans h6) (by positivity)
  have hsum : Summable (fun D : Λ => W D) := summable_of_sum_le (fun D => hW0 D) key
  exact ⟨hsum, hsum.tsum_le_of_sum_le key⟩

end Formalism.HermitianLatticeCounting.P
