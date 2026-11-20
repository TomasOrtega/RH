import Development.AutomorphicArithmetic.Foundations.Convolution.TwistedLocalOrbits.HoweSpace

open GlobalTheory.PRep GlobalTheory.SmGL GlobalTheory.SplitWeil ValuativeRel Matrix GlobalTheory.IndefiniteRowSideFullHecke.IwahoriDoubleCosets UpperTheory.ConvolutionTheory.Loc

/- English proof (translation)
Substitute `hq` using the available equality. Use `haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k)) DFunLike.coe_injective`. Establish `hfin : IsOfFinOrder τ` using `isOfFinOrder_of_finite τ`. Set `G` to `Subgroup.zpowers τ`. Set `F` to `FixedPoints.subfield G k`.

Set `e : Fin (orderOf τ) ≃ (k ≃ₐ[F] k)` to `(finEquivZPowers hfin).trans (FixedPoints.toAlgAutMulEquiv G k).toEquiv`. Establish `he : ∀ (i : Fin (orderOf τ)) (x : k), e i x = (τ ^ (i : ℕ)) x` using `fun i x => rfl`. Prove the components needed by the constructor for the conclusion. Introduce `u hu`. Establish `hu' : u ∈ F`.

Introduce and unpack `⟨g, hg⟩`. Establish `: Subgroup.zpowers τ ≤ MulAction.stabilizer (k ≃+* k) u`. Rewrite using `[Subgroup.zpowers_le]`. Conclude with `hu`. Conclude with `this hg`.

Take `⟨w, hw⟩` from `FiniteField.norm_surjective F k ⟨u, hu'⟩`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `h` using `Algebra.norm_eq_prod_automorphisms F w`. Rewrite `h` using `[hw, ← e.prod_comp]`. Rewrite using `[Finset.prod_range]`.

Conclude with `h.symm`. Take `⟨w, hw⟩` from `Algebra.trace_surjective F k 1`. Use `⟨w, ?_⟩` and prove the remaining obligations. Establish `h` using `trace_eq_sum_automorphisms (K := F) w`. Rewrite `h` using `[hw, ← e.sum_comp, map_one]`.

Rewrite using `[Finset.sum_range]`. Conclude with `h.symm`.
-/
private theorem finiteField_norm_trace_surjective {k : Type} [Field k] [Finite k] (τ : k ≃+* k) (q : ℕ) (hq : orderOf τ = q) :
    (∀ u : k, τ u = u → ∃ w : k, ∏ i ∈ Finset.range q, (τ ^ i) w = u) ∧
      ∃ a : k, ∑ i ∈ Finset.range q, (τ ^ i) a = 1 := by
  classical
  subst hq
  haveI : Finite (k ≃+* k) := Finite.of_injective (fun f : k ≃+* k => (f : k → k)) DFunLike.coe_injective
  have hfin : IsOfFinOrder τ := isOfFinOrder_of_finite τ
  let G := Subgroup.zpowers τ
  let F := FixedPoints.subfield G k
  let e : Fin (orderOf τ) ≃ (k ≃ₐ[F] k) :=
    (finEquivZPowers hfin).trans (FixedPoints.toAlgAutMulEquiv G k).toEquiv
  have he : ∀ (i : Fin (orderOf τ)) (x : k), e i x = (τ ^ (i : ℕ)) x := fun i x => rfl
  constructor
  · intro u hu
    have hu' : u ∈ F := by
      rintro ⟨g, hg⟩
      have : Subgroup.zpowers τ ≤ MulAction.stabilizer (k ≃+* k) u := by
        rw [Subgroup.zpowers_le]; exact hu
      exact this hg
    obtain ⟨w, hw⟩ := FiniteField.norm_surjective F k ⟨u, hu'⟩
    refine ⟨w, ?_⟩
    have h := Algebra.norm_eq_prod_automorphisms F w
    rw [hw, ← e.prod_comp] at h
    rw [Finset.prod_range]
    exact h.symm
  · obtain ⟨w, hw⟩ := Algebra.trace_surjective F k 1
    refine ⟨w, ?_⟩
    have h := trace_eq_sum_automorphisms (K := F) w
    rw [hw, ← e.sum_comp, map_one] at h
    rw [Finset.sum_range]
    exact h.symm

/- English proof (translation)
Set `s : 𝒪[E] ≃+* 𝒪[E]` to `σ.restrict 𝒪[E] 𝒪[E] fun x => by`. Simplify using `only [Valuation.mem_integer_iff, h.isom x]`. Establish `hs : ∀ x : 𝒪[E], ((s x : 𝒪[E]) : E) = σ x` using `fun x => rfl`. Establish `hsi : ∀ (i : ℕ) (x : 𝒪[E]), ((s^[i] x : 𝒪[E]) : E) = σ^[i] x`. Introduce `i x`.

Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]`. Set `τ : 𝓀[E] ≃+* 𝓀[E]` to `IsLocalRing.ResidueField.mapEquiv s`. Establish `hτ : ∀ x : 𝒪[E], τ (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s x)` using `fun x => rfl`.

Establish `hτi : ∀ (i : ℕ) (x : 𝒪[E]), (τ ^ i) (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s^[i] x)`. Introduce `i x`. Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih, hτ]`.

Establish `key : ∀ x y : 𝒪[E], IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔ valuation E ((x : E) - y) < 1`. Introduce `x y`. Rewrite using `[← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff, Valuation.Integer.not_isUnit_iff_valuation_lt_one]`. Both sides reduce to the same expression. Establish `hord : orderOf τ = q`.

Rewrite using `[orderOf_eq_iff h.pos]`. Prove the components needed by the constructor for the conclusion. Use extensionality with `z`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`. Rewrite using `[hτi]`.

Conclude with `congrArg (IsLocalRing.residue 𝒪[E]) (Subtype.ext ((hsi q x).trans (h.ord x)))`. Introduce `m hm hm0 he`. Take `⟨x, hx, hx'⟩` from `h.res m hm0 hm`. Use `hτi m ⟨x, hx⟩` as an intermediate fact. Rewrite `this` using `[he, RingAut.one_apply, eq_comm, key, hsi]`.

Conclude with `this.ne hx'`. Take `⟨h1, z, hz⟩` from `finiteField_norm_trace_surjective τ q hord`. Prove the components needed by the constructor for the conclusion. Introduce `u hu hσ`. Take `⟨z, hz⟩` from `h1 (IsLocalRing.residue _ (⟨u, hu.le⟩ : 𝒪[E])) (by`.

Rewrite using `[hτ]`. Use `congr 1`. Conclude with `Subtype.ext hσ)`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`. Use `⟨x, x.2, ?_⟩` and prove the remaining obligations.

Simplify using `only [hτi] at hz`. Rewrite `hz` using `[← map_prod, key]`. Simplify `hz` using `only [SubmonoidClass.coe_finsetProd, hsi]`. Take `⟨x, rfl⟩` from `IsLocalRing.residue_surjective z`. Use `⟨x, x.2, ?_⟩` and prove the remaining obligations.

Simplify using `only [hτi] at hz`. Rewrite `hz` using `[← map_sum, ← map_one (IsLocalRing.residue 𝒪[E]), key]`. Simplify `hz` using `only [AddSubmonoidClass.coe_finsetSum, hsi, OneMemClass.coe_one]`.
-/
private theorem unramified_norm_trace_surjective {E : Type} [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E]
    (σ : E ≃+* E) (q : ℕ) (h : Unram σ q) :
    (∀ u : E, valuation E u = 1 → σ u = u →
      ∃ w : E, valuation E w ≤ 1 ∧ valuation E (∏ i ∈ Finset.range q, σ^[i] w - u) < 1) ∧
      ∃ a : E, valuation E a ≤ 1 ∧ valuation E (∑ i ∈ Finset.range q, σ^[i] a - 1) < 1 := by
  let s : 𝒪[E] ≃+* 𝒪[E] := σ.restrict 𝒪[E] 𝒪[E] fun x => by
    simp only [Valuation.mem_integer_iff, h.isom x]
  have hs : ∀ x : 𝒪[E], ((s x : 𝒪[E]) : E) = σ x := fun x => rfl
  have hsi : ∀ (i : ℕ) (x : 𝒪[E]), ((s^[i] x : 𝒪[E]) : E) = σ^[i] x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', Function.iterate_succ_apply', hs, ih]
  let τ : 𝓀[E] ≃+* 𝓀[E] := IsLocalRing.ResidueField.mapEquiv s
  have hτ : ∀ x : 𝒪[E], τ (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s x) := fun x => rfl
  have hτi : ∀ (i : ℕ) (x : 𝒪[E]), (τ ^ i) (IsLocalRing.residue _ x) = IsLocalRing.residue _ (s^[i] x) := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih, hτ]
  have key : ∀ x y : 𝒪[E], IsLocalRing.residue _ x = IsLocalRing.residue _ y ↔ valuation E ((x : E) - y) < 1 := by
    intro x y
    rw [← sub_eq_zero, ← map_sub, IsLocalRing.residue_eq_zero_iff, IsLocalRing.mem_maximalIdeal, mem_nonunits_iff,
      Valuation.Integer.not_isUnit_iff_valuation_lt_one]
    rfl
  have hord : orderOf τ = q := by
    rw [orderOf_eq_iff h.pos]
    constructor
    · ext z
      obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
      rw [hτi]
      exact congrArg (IsLocalRing.residue 𝒪[E]) (Subtype.ext ((hsi q x).trans (h.ord x)))
    · intro m hm hm0 he
      obtain ⟨x, hx, hx'⟩ := h.res m hm0 hm
      have := hτi m ⟨x, hx⟩
      rw [he, RingAut.one_apply, eq_comm, key, hsi] at this
      exact this.ne hx'
  obtain ⟨h1, z, hz⟩ := finiteField_norm_trace_surjective τ q hord
  constructor
  · intro u hu hσ
    obtain ⟨z, hz⟩ := h1 (IsLocalRing.residue _ (⟨u, hu.le⟩ : 𝒪[E])) (by
      rw [hτ]; congr 1; exact Subtype.ext hσ)
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨x, x.2, ?_⟩
    simp only [hτi] at hz
    rw [← map_prod, key] at hz
    simpa only [SubmonoidClass.coe_finsetProd, hsi] using hz
  · obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective z
    refine ⟨x, x.2, ?_⟩
    simp only [hτi] at hz
    rw [← map_sum, ← map_one (IsLocalRing.residue 𝒪[E]), key] at hz
    simpa only [AddSubmonoidClass.coe_finsetSum, hsi, OneMemClass.coe_one] using hz

/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero => exact ⟨0, by simp, by simp⟩`. Consider the case `succ m ih`. Take `⟨c, hc, he⟩` from `ih`. Use `⟨c + (∑ i ∈ Finset.range m, x i) * x m + d * c * x m, ?_, ?_⟩` and prove the remaining obligations.

Establish `hS : valuation E (∑ i ∈ Finset.range m, x i) ≤ 1` using `Valuation.map_sum_le _ fun i _ => hx i`. Use `Valuation.map_add_le _ (Valuation.map_add_le _ hc ?_) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hS (hx m)`. Rewrite using `[map_mul, map_mul]`.

Conclude with `mul_le_one' (mul_le_one' hd hc) (hx m)`. Rewrite using `[Finset.prod_range_succ, Finset.sum_range_succ, he]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem prod_expand {E : Type} [Field E] [ValuativeRel E] (d : E) (hd : valuation E d ≤ 1) (x : ℕ → E)
    (hx : ∀ i, valuation E (x i) ≤ 1) (m : ℕ) :
    ∃ c : E, valuation E c ≤ 1 ∧
      ∏ i ∈ Finset.range m, (1 + d * x i) = 1 + d * ∑ i ∈ Finset.range m, x i + d ^ 2 * c := by
  induction m with
  | zero => exact ⟨0, by simp, by simp⟩
  | succ m ih =>
    obtain ⟨c, hc, he⟩ := ih
    refine ⟨c + (∑ i ∈ Finset.range m, x i) * x m + d * c * x m, ?_, ?_⟩
    · have hS : valuation E (∑ i ∈ Finset.range m, x i) ≤ 1 := Valuation.map_sum_le _ fun i _ => hx i
      refine Valuation.map_add_le _ (Valuation.map_add_le _ hc ?_) ?_
      · rw [map_mul]; exact mul_le_one' hS (hx m)
      · rw [map_mul, map_mul]; exact mul_le_one' (mul_le_one' hd hc) (hx m)
    · rw [Finset.prod_range_succ, Finset.sum_range_succ, he]; ring

open scoped WithZeroTopology in
/- English proof (translation)
Introduce `E _ _ _ _ σ q h u hu hσu`. Take `⟨hres, a, ha, hTa⟩` from `unramified_norm_trace_surjective σ q h`. Take `⟨w₀, hw₀, hNw₀⟩` from `hres u hu hσu`. Establish `hit : ∀ (i : ℕ) (x : E), σ^[i] x = (σ ^ i) x`. Introduce `i x`.

Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih]`. Establish `hiso : ∀ (i : ℕ) (x : E), valuation E (σ^[i] x) = valuation E x`. Introduce `i x`.

Proceed by induction on `i with`. Consider the case `zero => rfl`. Consider the case `succ i ih => rw [Function.iterate_succ_apply', h.isom, ih]`. Establish `hfix : ∀ (i : ℕ) (x : E), σ x = x → σ^[i] x = x` using `fun i x hx => Function.iterate_fixed hx i`. Establish `hNfix : ∀ x : E, x ≠ 0 → σ (∏ i ∈ Finset.range q, σ^[i] x) = ∏ i ∈ Finset.range q, σ^[i] x`.

Introduce `x hx`. Establish `e1` using `Finset.prod_range_succ (fun i => σ^[i] x) q`. Rewrite `e1` using `[Finset.prod_range_succ', h.ord]`. Simplify using `only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1`. Rewrite using `[map_prod]`.

Conclude with `mul_right_cancel₀ hx e1`. Establish `hTfix : ∀ x : E, σ (∑ i ∈ Finset.range q, σ^[i] x) = ∑ i ∈ Finset.range q, σ^[i] x`. Introduce `x`. Establish `e1` using `Finset.sum_range_succ (fun i => σ^[i] x) q`. Rewrite `e1` using `[Finset.sum_range_succ', h.ord]`.

Simplify using `only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1`. Rewrite using `[map_sum]`. Conclude with `add_right_cancel e1`. Establish `near : ∀ x y : E, valuation E y = 1 → valuation E (x - y) < 1 → valuation E x = 1`. Introduce `x y hy hxy`.

Rewrite `hxy`, the goal using `[← hy]`. Conclude with `Valuation.map_eq_of_sub_lt _ hxy`. Establish `hNv : ∀ x : E, valuation E (∏ i ∈ Finset.range q, σ^[i] x) = valuation E x ^ q`. Introduce `x`. Rewrite using `[map_prod]`.

Simplify using `only [hiso, Finset.prod_const, Finset.card_range]`. Choose the witnesses or unpack the hypotheses as in `⟨b, hb, hTb⟩ : ∃ b : E, valuation E b ≤ 1 ∧ ∑ i ∈ Finset.range q, σ^[i] b = 1 := by`. Establish `hT1` using `near _ _ (map_one _) hTa`. Use `set T := ∑ i ∈ Finset.range q, σ^[i] a with hT`. Establish `hT0 : T ≠ 0`.

Introduce `h0`. Rewrite `hT1` using `[h0, map_zero]`. Conclude with `zero_ne_one hT1`. Use `⟨a / T, by rw [map_div₀, hT1, div_one]; exact ha, ?_⟩` and prove the remaining obligations. Establish `: ∀ i : ℕ, σ^[i] (a / T) = σ^[i] a / T`.

Introduce `i`. Rewrite using `[hit, map_div₀, ← hit, ← hit, hfix i T (hTfix a)]`. Simplify using `only [this]`. Rewrite using `[← Finset.sum_div, ← hT, div_self hT0]`. Establish `hcσ : Continuous σ`.

Use `continuous_of_continuousAt_zero σ.toAddMonoidHom ?_` and prove the remaining obligations. Rewrite using `[ContinuousAt, map_zero]`. Use `((IsValuativeTopology.hasBasis_nhds_zero E).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero E)).2 ?_` and prove the remaining obligations. Introduce `γ _`. Conclude with `⟨γ, trivial, fun x hx => (h.isom x).trans_lt hx⟩`.

Establish `hcont : Continuous fun x : E => valuation E (∏ i ∈ Finset.range q, σ^[i] x - u)` using `IsValuativeTopology.continuous_valuation.comp ((continuous_finsetProd _ fun i _ => hcσ.iterate i).sub continuous_const)`. Take `⟨w, hw, hmin⟩` from `(IsNonarchimedeanLocalField.isCompact_closedBall E 1).exists_isMinOn ⟨w₀, hw₀⟩ hcont.continuousOn`. Establish `hlt : valuation E (∏ i ∈ Finset.range q, σ^[i] w - u) < 1` using `lt_of_le_of_lt (hmin hw₀) hNw₀`. Establish `hN1` using `near _ _ hu hlt`. Establish `hw1 : valuation E w = 1`.

Rewrite `hN1` using `[hNv]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le h.pos.ne').1 hN1`. Use `⟨w, hw1, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Establish `hw0 : w ≠ 0`.

Introduce `h0`. Rewrite `hw1` using `[h0, map_zero]`. Conclude with `zero_ne_one hw1`. Establish `hNσ` using `hNfix w hw0`. Use `set N := ∏ i ∈ Finset.range q, σ^[i] w with hN`.

Establish `hN0 : N ≠ 0`. Introduce `h0`. Rewrite `hN1` using `[h0, map_zero]`. Conclude with `zero_ne_one hN1`. Use `set d := (u - N) / N with hd`.

Establish `hdσ : σ d = d` using `by rw [hd, map_div₀, map_sub, hσu, hNσ]`. Establish `hdv : valuation E d = valuation E (N - u)`. Rewrite using `[hd, map_div₀, hN1, div_one, Valuation.map_sub_swap]`. Establish `hd1 : valuation E d < 1` using `hdv ▸ hlt`. Establish `hd0 : 0 < valuation E d`.

Rewrite using `[hdv, zero_lt_iff, Valuation.ne_zero_iff]`. Conclude with `sub_ne_zero.2 hne`. Take `⟨c, hc, he⟩` from `prod_expand d hd1.le (fun i => σ^[i] b) (fun i => (hiso i b).trans_le hb) q`. Establish `hw' : valuation E (w * (1 + d * b)) ≤ 1`. Rewrite using `[map_mul, hw1, one_mul]`.

Use `Valuation.map_add_le _ (map_one _).le ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_le_one' hd1.le hb`. Establish `hle : valuation E (N - u) ≤ valuation E (∏ i ∈ Finset.range q, σ^[i] (w * (1 + d * b)) - u)` using `hmin hw'`. Establish `e1 : ∀ i : ℕ, σ^[i] (w * (1 + d * b)) = σ^[i] w * (1 + d * σ^[i] b)`.

Introduce `i`. Rewrite using `[hit, map_mul, map_add, map_one, map_mul, ← hit, ← hit, ← hit, hfix i d hdσ]`. Simplify using `only [e1] at hle`. Rewrite `hle` using `[Finset.prod_mul_distrib, he, hTb, ← hN, ← hdv]`. Establish `e2 : N * (1 + d * 1 + d ^ 2 * c) - u = N * (d * (d * c))`.

Establish `: u = N * (1 + d)` using `by rw [hd]; field_simp; ring`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `hle` using `[e2, map_mul, hN1, one_mul, map_mul, map_mul]`. Establish `: valuation E d * (valuation E d * valuation E c) < valuation E d` using `mul_lt_of_lt_one_right hd0 (lt_of_le_of_lt (mul_le_of_le_one_right' hc) hd1)`.

Conclude with `absurd hle this.not_ge`.
-/
theorem UpperTheory.ConvolutionTheory.Loc.unitNorm :
    ∀ (E : Type) [Field E] [ValuativeRel E] [TopologicalSpace E] [IsNonarchimedeanLocalField E] (σ : E ≃+* E) (q : ℕ), Unram σ q →
      ∀ u : E, valuation E u = 1 → σ u = u → ∃ w : E, valuation E w = 1 ∧ ∏ i ∈ Finset.range q, σ^[i] w = u := by
  intro E _ _ _ _ σ q h u hu hσu
  obtain ⟨hres, a, ha, hTa⟩ := unramified_norm_trace_surjective σ q h
  obtain ⟨w₀, hw₀, hNw₀⟩ := hres u hu hσu
  have hit : ∀ (i : ℕ) (x : E), σ^[i] x = (σ ^ i) x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', pow_succ', RingAut.mul_apply, ih]
  have hiso : ∀ (i : ℕ) (x : E), valuation E (σ^[i] x) = valuation E x := by
    intro i x
    induction i with
    | zero => rfl
    | succ i ih => rw [Function.iterate_succ_apply', h.isom, ih]
  have hfix : ∀ (i : ℕ) (x : E), σ x = x → σ^[i] x = x := fun i x hx => Function.iterate_fixed hx i

  have hNfix : ∀ x : E, x ≠ 0 → σ (∏ i ∈ Finset.range q, σ^[i] x) = ∏ i ∈ Finset.range q, σ^[i] x := by
    intro x hx
    have e1 := Finset.prod_range_succ (fun i => σ^[i] x) q
    rw [Finset.prod_range_succ', h.ord] at e1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1
    rw [map_prod]
    exact mul_right_cancel₀ hx e1
  have hTfix : ∀ x : E, σ (∑ i ∈ Finset.range q, σ^[i] x) = ∑ i ∈ Finset.range q, σ^[i] x := by
    intro x
    have e1 := Finset.sum_range_succ (fun i => σ^[i] x) q
    rw [Finset.sum_range_succ', h.ord] at e1
    simp only [Function.iterate_succ_apply', Function.iterate_zero_apply] at e1
    rw [map_sum]
    exact add_right_cancel e1
  have near : ∀ x y : E, valuation E y = 1 → valuation E (x - y) < 1 → valuation E x = 1 := by
    intro x y hy hxy
    rw [← hy] at hxy ⊢
    exact Valuation.map_eq_of_sub_lt _ hxy
  have hNv : ∀ x : E, valuation E (∏ i ∈ Finset.range q, σ^[i] x) = valuation E x ^ q := by
    intro x
    rw [map_prod]
    simp only [hiso, Finset.prod_const, Finset.card_range]

  obtain ⟨b, hb, hTb⟩ : ∃ b : E, valuation E b ≤ 1 ∧ ∑ i ∈ Finset.range q, σ^[i] b = 1 := by
    have hT1 := near _ _ (map_one _) hTa
    set T := ∑ i ∈ Finset.range q, σ^[i] a with hT
    have hT0 : T ≠ 0 := by
      intro h0
      rw [h0, map_zero] at hT1
      exact zero_ne_one hT1
    refine ⟨a / T, by rw [map_div₀, hT1, div_one]; exact ha, ?_⟩
    have : ∀ i : ℕ, σ^[i] (a / T) = σ^[i] a / T := by
      intro i
      rw [hit, map_div₀, ← hit, ← hit, hfix i T (hTfix a)]
    simp only [this]
    rw [← Finset.sum_div, ← hT, div_self hT0]

  have hcσ : Continuous σ := by
    refine continuous_of_continuousAt_zero σ.toAddMonoidHom ?_
    rw [ContinuousAt, map_zero]
    refine ((IsValuativeTopology.hasBasis_nhds_zero E).tendsto_iff (IsValuativeTopology.hasBasis_nhds_zero E)).2 ?_
    intro γ _
    exact ⟨γ, trivial, fun x hx => (h.isom x).trans_lt hx⟩
  have hcont : Continuous fun x : E => valuation E (∏ i ∈ Finset.range q, σ^[i] x - u) :=
    IsValuativeTopology.continuous_valuation.comp
      ((continuous_finsetProd _ fun i _ => hcσ.iterate i).sub continuous_const)
  obtain ⟨w, hw, hmin⟩ := (IsNonarchimedeanLocalField.isCompact_closedBall E 1).exists_isMinOn ⟨w₀, hw₀⟩ hcont.continuousOn
  have hlt : valuation E (∏ i ∈ Finset.range q, σ^[i] w - u) < 1 := lt_of_le_of_lt (hmin hw₀) hNw₀
  have hN1 := near _ _ hu hlt
  have hw1 : valuation E w = 1 := by
    rw [hNv] at hN1
    exact (pow_eq_one_iff_of_nonneg zero_le h.pos.ne').1 hN1
  refine ⟨w, hw1, ?_⟩
  by_contra hne
  have hw0 : w ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hw1
    exact zero_ne_one hw1
  have hNσ := hNfix w hw0
  set N := ∏ i ∈ Finset.range q, σ^[i] w with hN
  have hN0 : N ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hN1
    exact zero_ne_one hN1
  set d := (u - N) / N with hd
  have hdσ : σ d = d := by rw [hd, map_div₀, map_sub, hσu, hNσ]
  have hdv : valuation E d = valuation E (N - u) := by
    rw [hd, map_div₀, hN1, div_one, Valuation.map_sub_swap]
  have hd1 : valuation E d < 1 := hdv ▸ hlt
  have hd0 : 0 < valuation E d := by
    rw [hdv, zero_lt_iff, Valuation.ne_zero_iff]
    exact sub_ne_zero.2 hne
  obtain ⟨c, hc, he⟩ := prod_expand d hd1.le (fun i => σ^[i] b) (fun i => (hiso i b).trans_le hb) q
  have hw' : valuation E (w * (1 + d * b)) ≤ 1 := by
    rw [map_mul, hw1, one_mul]
    refine Valuation.map_add_le _ (map_one _).le ?_
    rw [map_mul]; exact mul_le_one' hd1.le hb
  have hle : valuation E (N - u) ≤ valuation E (∏ i ∈ Finset.range q, σ^[i] (w * (1 + d * b)) - u) := hmin hw'
  have e1 : ∀ i : ℕ, σ^[i] (w * (1 + d * b)) = σ^[i] w * (1 + d * σ^[i] b) := by
    intro i
    rw [hit, map_mul, map_add, map_one, map_mul, ← hit, ← hit, ← hit, hfix i d hdσ]
  simp only [e1] at hle
  rw [Finset.prod_mul_distrib, he, hTb, ← hN, ← hdv] at hle
  have e2 : N * (1 + d * 1 + d ^ 2 * c) - u = N * (d * (d * c)) := by
    have : u = N * (1 + d) := by rw [hd]; field_simp; ring
    rw [this]; ring
  rw [e2, map_mul, hN1, one_mul, map_mul, map_mul] at hle
  have : valuation E d * (valuation E d * valuation E c) < valuation E d :=
    mul_lt_of_lt_one_right hd0 (lt_of_le_of_lt (mul_le_of_le_one_right' hc) hd1)
  exact absurd hle this.not_ge
