import Mathlib
import CompanionTheory.RealGroups.UnitaryAdmissibility.ArchimedeanUnitaryDual.StSandwich

open CompanionTheory.Rg.FlB

noncomputable section

namespace GlobalTheory.CompanionTheory.HermAniso

section Core

variable {L : Type} [NontriviallyNormedField L] {V : Type} [AddCommGroup V] [Module L V]
  {s : L →+* L} {h : V → V → L}

/- English proof (translation)
Establish `h1` using `hh.2.2.1`. Rewrite using `[h1 z (x + y), hh.1, map_add, h1 z x, h1 z y]`.
-/
lemma add_left (hh : IsHerm s h) (x y z : V) : h (x + y) z = h x z + h y z := by
  have h1 := hh.2.2.1
  rw [h1 z (x + y), hh.1, map_add, h1 z x, h1 z y]

/- English proof (translation)
Establish `h1` using `hh.2.2.1`. Rewrite using `[h1 y (a • x), hh.2.1, map_mul, h1 y x]`.
-/
lemma smul_left (hh : IsHerm s h) (a : L) (x y : V) : h (a • x) y = s a * h x y := by
  have h1 := hh.2.2.1
  rw [h1 y (a • x), hh.2.1, map_mul, h1 y x]

/- English proof (translation)
Rewrite using `[add_left hh, hh.1, hh.1]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma q_add (hh : IsHerm s h) (x y : V) :
    h (x + y) (x + y) = h x x + h y y + (h x y + h y x) := by
  rw [add_left hh, hh.1, hh.1]; ring

/- English proof (translation)
Rewrite using `[smul_left hh, hh.2.1, norm_mul, norm_mul, hs.2.1]`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma norm_q_smul (hs : IsInv s) (hh : IsHerm s h) (a : L) (x : V) :
    ‖h (a • x) (a • x)‖ = ‖a‖ * ‖a‖ * ‖h x x‖ := by
  rw [smul_left hh, hh.2.1, norm_mul, norm_mul, hs.2.1]; ring

/- English proof (translation)
Establish `h1` using `hh.2.2.1`. Assume the negation of the conclusion as `hb`. Use `push_neg at hb`. Take `⟨b, hbd⟩ : ∃ b, b = h x y + h y x` from `⟨_, rfl⟩`. Rewrite `hb` using `[← hbd]`.

Establish `hbpos : 0 < ‖b‖` using `by linarith`. Establish `hb0 : b ≠ 0` using `norm_pos_iff.mp hbpos`. Establish `hsb : s b = b`. Rewrite using `[hbd, map_add, ← h1 x y, ← h1 y x, add_comm]`. Establish `hsx : s (h x x) = h x x` using `(h1 x x).symm`.

Establish `hsy : s (h y y) = h y y` using `(h1 y y).symm`. Establish `hc1 : s (h y y / b ^ 2) = h y y / b ^ 2`. Rewrite using `[map_div₀, map_pow, hsb, hsy]`. Establish `hc2 : ‖h y y / b ^ 2‖ < 1`. Rewrite using `[norm_div, norm_pow, div_lt_one (by positivity)]`.

Use the polynomial consequences of the given equalities and inequalities. Take `⟨u, hsu, hu, he⟩` from `hH L s hs (h y y / b ^ 2) (h x x) hc1 hsx hc2 hx`. Take `⟨t, htd⟩ : ∃ t, t = u / b` from `⟨_, rfl⟩`. Establish `hst : s t = t` using `by rw [htd, map_div₀, hsu, hsb]`. Establish `hq : h (x + t • y) (x + t • y) = 0`.

Rewrite using `[q_add hh, smul_left hh, hh.2.1, hh.2.1, smul_left hh, hst]`. Establish `e1 : t * (t * h y y) + t * h x y + t * h y x = t * b + t ^ 2 * h y y`. Rewrite using `[hbd]`. Expand and normalize the polynomial expressions, which then agree. Establish `e2 : t * b = u` using `by rw [htd]; field_simp`.

Establish `e3 : t ^ 2 * h y y = h y y / b ^ 2 * u ^ 2` using `by rw [htd]; field_simp`. Take the linear combination `he + e1 + e2 + e3`. Establish `hz` using `hani _ hq`. Establish `hxe : x = (-t) • y`. Rewrite using `[neg_smul]`.

Conclude with `eq_neg_of_add_eq_zero_left hz`. Establish `hxy : h x y = -t * h y y`. Establish `: h x y = h ((-t) • y) y` using `congrArg (fun z => h z y) hxe`. Rewrite using `[this, smul_left hh, map_neg, hst]`. Establish `hyx : h y x = -t * h y y`.

Establish `: h y x = h y ((-t) • y)` using `congrArg (fun z => h y z) hxe`. Rewrite using `[this, hh.2.1]`. Establish `ht : ‖t‖ < 1`. Rewrite using `[htd, norm_div, div_lt_one hbpos]`. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `hle : ‖-t * h y y‖ < 1`. Rewrite using `[norm_mul, norm_neg]`. Use polynomial arithmetic with `[norm_nonneg t, norm_nonneg (h y y)]`. Establish `: ‖b‖ < 1`. Rewrite using `[hbd, hxy, hyx]`.

Conclude with `lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by simp)) hle`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
lemma pair_le [IsUltrametricDist L] [CompleteSpace L] (hH : StHensel) (hs : IsInv s) (hh : IsHerm s h)
    (hani : ∀ x, h x x = 0 → x = 0) {x y : V} (hx : ‖h x x‖ ≤ 1) (hy : ‖h y y‖ ≤ 1) :
    ‖h x y + h y x‖ ≤ 1 := by
  have h1 := hh.2.2.1
  by_contra hb
  push_neg at hb
  obtain ⟨b, hbd⟩ : ∃ b, b = h x y + h y x := ⟨_, rfl⟩
  rw [← hbd] at hb
  have hbpos : 0 < ‖b‖ := by linarith
  have hb0 : b ≠ 0 := norm_pos_iff.mp hbpos
  have hsb : s b = b := by
    rw [hbd, map_add, ← h1 x y, ← h1 y x, add_comm]
  have hsx : s (h x x) = h x x := (h1 x x).symm
  have hsy : s (h y y) = h y y := (h1 y y).symm
  have hc1 : s (h y y / b ^ 2) = h y y / b ^ 2 := by
    rw [map_div₀, map_pow, hsb, hsy]
  have hc2 : ‖h y y / b ^ 2‖ < 1 := by
    rw [norm_div, norm_pow, div_lt_one (by positivity)]
    nlinarith
  obtain ⟨u, hsu, hu, he⟩ := hH L s hs (h y y / b ^ 2) (h x x) hc1 hsx hc2 hx
  obtain ⟨t, htd⟩ : ∃ t, t = u / b := ⟨_, rfl⟩
  have hst : s t = t := by rw [htd, map_div₀, hsu, hsb]
  have hq : h (x + t • y) (x + t • y) = 0 := by
    rw [q_add hh, smul_left hh, hh.2.1, hh.2.1, smul_left hh, hst]
    have e1 : t * (t * h y y) + t * h x y + t * h y x = t * b + t ^ 2 * h y y := by
      rw [hbd]; ring
    have e2 : t * b = u := by rw [htd]; field_simp
    have e3 : t ^ 2 * h y y = h y y / b ^ 2 * u ^ 2 := by rw [htd]; field_simp
    linear_combination he + e1 + e2 + e3
  have hz := hani _ hq
  have hxe : x = (-t) • y := by
    rw [neg_smul]; exact eq_neg_of_add_eq_zero_left hz
  have hxy : h x y = -t * h y y := by
    have : h x y = h ((-t) • y) y := congrArg (fun z => h z y) hxe
    rw [this, smul_left hh, map_neg, hst]
  have hyx : h y x = -t * h y y := by
    have : h y x = h y ((-t) • y) := congrArg (fun z => h y z) hxe
    rw [this, hh.2.1]
  have ht : ‖t‖ < 1 := by
    rw [htd, norm_div, div_lt_one hbpos]; linarith
  have hle : ‖-t * h y y‖ < 1 := by
    rw [norm_mul, norm_neg]
    nlinarith [norm_nonneg t, norm_nonneg (h y y)]
  have : ‖b‖ < 1 := by
    rw [hbd, hxy, hyx]
    exact lt_of_le_of_lt ((IsUltrametricDist.norm_add_le_max _ _).trans (by simp)) hle
  linarith

/- English proof (translation)
Use `⟨{ carrier := {x | ‖h x x‖ ≤ 1}, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun x => Iff.rfl⟩` and prove the remaining obligations. Introduce `a b ha hb`. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[q_add hh]`. Use `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp a b ha hb))` and prove the remaining obligations.

Conclude with `(IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)`. Use `hh.2.1 (0 : L) (0 : V) (0 : V)` as an intermediate fact. Simplify using `only [zero_smul, zero_mul] at this`. Simplify using `[this]`. Introduce `a ha`.

Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Use `norm_q_smul hs hh (-1 : L) a` as an intermediate fact. Simplify using `only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at this`. Rewrite using `[this]` and apply the resulting hypothesis.
-/
lemma exists_ball [IsUltrametricDist L] (hs : IsInv s) (hh : IsHerm s h)
    (hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1) :
    ∃ V₀ : AddSubgroup V, ∀ x, x ∈ V₀ ↔ ‖h x x‖ ≤ 1 := by
  refine ⟨{ carrier := {x | ‖h x x‖ ≤ 1}, add_mem' := ?_, zero_mem' := ?_, neg_mem' := ?_ }, fun x => Iff.rfl⟩
  · intro a b ha hb
    simp only [Set.mem_setOf_eq] at ha hb ⊢
    rw [q_add hh]
    refine (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ?_ (hp a b ha hb))
    exact (IsUltrametricDist.norm_add_le_max _ _).trans (max_le ha hb)
  · have := hh.2.1 (0 : L) (0 : V) (0 : V)
    simp only [zero_smul, zero_mul] at this
    simp [this]
  · intro a ha
    simp only [Set.mem_setOf_eq] at ha ⊢
    have := norm_q_smul hs hh (-1 : L) a
    simp only [neg_smul, one_smul, norm_neg, norm_one, one_mul] at this
    rwa [this]

/- English proof (translation)
Establish `h1` using `hh.2.2.1`. Set `φ : V →ₗ[L] (Fin m → L)` to `{ toFun := fun x j => h (b j) x map_add' := fun x y => by ext j; simp [hh.1] map_smul' := fun a x => by ext j; simp [hh.2.1] }`. Establish `hker : LinearMap.ker φ = ⊥`. Rewrite using `[LinearMap.ker_eq_bot']`. Introduce `x hx`.

Set `ℓ : V →ₗ[L] L` to `{ toFun := fun y => h x y map_add' := fun y z => hh.1 x y z map_smul' := fun a y => by simp [hh.2.1] }`. Establish `hl : ℓ = 0`. Use `b.ext fun j => ?_` and prove the remaining obligations. Establish `: h (b j) x = 0` using `congrFun hx j`. Express the relevant statement in the definitionally equal form `h x (b j) = 0`.

Rewrite using `[h1 (b j) x, this, map_zero]`. Conclude with `hh.2.2.2 x fun y => LinearMap.congr_fun hl y`. Take `⟨ψ, hψ⟩` from `φ.exists_leftInverse_of_injective hker`. Use `⟨fun i j => ((b.coord i) ∘ₗ ψ) (fun k => if j = k then 1 else 0), fun x i => ?_⟩` and prove the remaining obligations. Establish `e : ψ (φ x) = x` using `LinearMap.congr_fun hψ x`.

Use `LinearMap.pi_apply_eq_sum_univ ((b.coord i) ∘ₗ ψ) (φ x)` as an intermediate fact. Simplify using `only [LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul, e] at this`. Rewrite using `[this]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[mul_comm]`.

Both sides reduce to the same expression.
-/
lemma coord_comb [FiniteDimensional L V] (hh : IsHerm s h) {m : ℕ} (b : Module.Basis (Fin m) L V) :
    ∃ M : Fin m → Fin m → L, ∀ x i, b.repr x i = ∑ j, M i j * h (b j) x := by
  have h1 := hh.2.2.1
  let φ : V →ₗ[L] (Fin m → L) :=
    { toFun := fun x j => h (b j) x
      map_add' := fun x y => by ext j; simp [hh.1]
      map_smul' := fun a x => by ext j; simp [hh.2.1] }
  have hker : LinearMap.ker φ = ⊥ := by
    rw [LinearMap.ker_eq_bot']
    intro x hx
    let ℓ : V →ₗ[L] L :=
      { toFun := fun y => h x y
        map_add' := fun y z => hh.1 x y z
        map_smul' := fun a y => by simp [hh.2.1] }
    have hl : ℓ = 0 := by
      refine b.ext fun j => ?_
      have : h (b j) x = 0 := congrFun hx j
      change h x (b j) = 0
      rw [h1 (b j) x, this, map_zero]
    exact hh.2.2.2 x fun y => LinearMap.congr_fun hl y
  obtain ⟨ψ, hψ⟩ := φ.exists_leftInverse_of_injective hker
  refine ⟨fun i j => ((b.coord i) ∘ₗ ψ) (fun k => if j = k then 1 else 0), fun x i => ?_⟩
  have e : ψ (φ x) = x := LinearMap.congr_fun hψ x
  have := LinearMap.pi_apply_eq_sum_univ ((b.coord i) ∘ₗ ψ) (φ x)
  simp only [LinearMap.comp_apply, Module.Basis.coord_apply, smul_eq_mul, e] at this
  rw [this]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [mul_comm]
  rfl

end Core

/- English proof (translation)
Introduce `hH hS`. Unfold `StAniso ForAll`. Introduce `L _ _ _ _ s hs δ hδ V _ _ _ h hh hani Λ hΛ x`. Establish `h1` using `hh.2.2.1`. Establish `hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1` using `fun x y hx hy => pair_le hH hs hh hani hx hy`.

Take `⟨V₀, hV₀⟩` from `exists_ball hs hh hp`. Establish `hsmul : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ V₀, a • x ∈ V₀`. Introduce `a ha x hx`. Rewrite `hx`, the goal using `[hV₀]`. Rewrite using `[norm_q_smul hs hh]`.

Use `norm_nonneg a` as an intermediate fact. Establish `h2` using `norm_nonneg (h x x)`. Combine the equalities or inequalities in the displayed calculation. Establish `hδle : ∀ x ∈ V₀, ∀ y ∈ V₀, ‖h x y‖ ≤ ‖δ‖`. Introduce `x hx y hy`.

Use `(hδ.2.1 (h x y)).mp fun a ha => ?_` and prove the remaining obligations. Establish `hay` using `hsmul a ha y hy`. Use `hp x (a • y) ((hV₀ x).mp hx) ((hV₀ _).mp hay)` as an intermediate fact. Rewrite `this` using `[h1 x (a • y), hh.2.1]`. Rewrite using `[mul_comm]` and apply the resulting hypothesis.

Establish `hle : Λ ≤ V₀` using `fun y hy => (hV₀ y).mpr (hΛ.2.1 y hy)`. Take `⟨m, b, hb⟩` from `hΛ.1`. Establish `hbΛ : ∀ j, b j ∈ Λ`. Introduce `j`. Rewrite using `[hb]`.

Introduce `i`. Rewrite using `[Module.Basis.repr_self, Finsupp.single_apply]`. Apply the tactic sequence `split_ifs <;> simp`. Take `⟨M, hM⟩` from `coord_comb hh b`. Choose the witnesses or unpack the hypotheses as in `⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V₀, ∀ i, ‖b.repr x i‖ ≤ C := by`.

Use `⟨∑ i, ∑ j, ‖M i j‖ * ‖δ‖ + 1, ?_, fun x hx i => ?_⟩` and prove the remaining obligations. Establish `: 0 ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖` using `Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `e1 : ‖b.repr x i‖ ≤ ∑ j, ‖M i j‖ * ‖δ‖`. Rewrite using `[hM]`.

Use `(norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)` and prove the remaining obligations. Rewrite using `[norm_mul]`. Conclude with `mul_le_mul_of_nonneg_left (hδle _ (hle (hbΛ j)) x hx) (norm_nonneg _)`. Establish `e2 : ∑ j, ‖M i j‖ * ‖δ‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖` using `Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ * ‖δ‖) (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)`. Combine the linear equalities and inequalities to obtain the conclusion.

Take `⟨c, hc0, hc1⟩` from `NormedField.exists_norm_lt L (inv_pos.mpr hC0)`. Establish `hcne : c ≠ 0` using `norm_pos_iff.mp hc0`. Establish `hbound : ∀ x ∈ V₀, c • x ∈ Λ`. Introduce `x hx`. Rewrite using `[hb]`.

Introduce `i`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]`. Establish `e` using `hC x hx i`. Establish `e2 : ‖c‖ * C ≤ 1`. Use `mul_le_mul_of_nonneg_right hc1.le hC0.le` as an intermediate fact.

Rewrite `this` using `[inv_mul_cancel₀ hC0.ne']`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Establish `hab : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ V₀`. Introduce `x`. Establish `hpos : (0 : ℝ) < (1 + ‖h x x‖)⁻¹` using `by positivity`.

Take `⟨a, ha0, ha1⟩` from `NormedField.exists_norm_lt L hpos`. Use `⟨a, norm_pos_iff.mp ha0, ?_⟩` and prove the remaining obligations. Rewrite using `[hV₀, norm_q_smul hs hh]`. Establish `hq` using `norm_nonneg (h x x)`. Establish `e1 : ‖a‖ * (1 + ‖h x x‖) ≤ 1`.

Use `mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ 1 + ‖h x x‖)` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel₀ (by positivity)]`. Then use the resulting hypothesis. Establish `e2 : ‖a‖ ≤ 1` using `by nlinarith`. Establish `e3 : ‖a‖ * ‖h x x‖ ≤ 1` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation.

Establish `hlat : IsLat L V₀` using `hS L V Λ V₀ c ⟨m, b, hb⟩ hcne hbound hab hsmul`. Establish `heq : V₀ = Λ` using `hΛ.2.2 V₀ hlat (fun x hx => (hV₀ x).mp hx) hle`. Rewrite using `[← heq]`. Conclude with `hV₀ x`.
-/
theorem aniso : StHensel → StSandwich → StAniso := by
  intro hH hS
  unfold StAniso ForAll
  intro L _ _ _ _ s hs δ hδ V _ _ _ h hh hani Λ hΛ x
  have h1 := hh.2.2.1
  have hp : ∀ x y : V, ‖h x x‖ ≤ 1 → ‖h y y‖ ≤ 1 → ‖h x y + h y x‖ ≤ 1 :=
    fun x y hx hy => pair_le hH hs hh hani hx hy
  obtain ⟨V₀, hV₀⟩ := exists_ball hs hh hp
  have hsmul : ∀ a : L, ‖a‖ ≤ 1 → ∀ x ∈ V₀, a • x ∈ V₀ := by
    intro a ha x hx
    rw [hV₀] at hx ⊢
    rw [norm_q_smul hs hh]
    have := norm_nonneg a
    have h2 := norm_nonneg (h x x)
    calc ‖a‖ * ‖a‖ * ‖h x x‖ ≤ 1 * 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hδle : ∀ x ∈ V₀, ∀ y ∈ V₀, ‖h x y‖ ≤ ‖δ‖ := by
    intro x hx y hy
    refine (hδ.2.1 (h x y)).mp fun a ha => ?_
    have hay := hsmul a ha y hy
    have := hp x (a • y) ((hV₀ x).mp hx) ((hV₀ _).mp hay)
    rw [h1 x (a • y), hh.2.1] at this
    rwa [mul_comm]
  have hle : Λ ≤ V₀ := fun y hy => (hV₀ y).mpr (hΛ.2.1 y hy)
  obtain ⟨m, b, hb⟩ := hΛ.1
  have hbΛ : ∀ j, b j ∈ Λ := by
    intro j
    rw [hb]
    intro i
    rw [Module.Basis.repr_self, Finsupp.single_apply]
    split_ifs <;> simp
  obtain ⟨M, hM⟩ := coord_comb hh b
  obtain ⟨C, hC0, hC⟩ : ∃ C : ℝ, 0 < C ∧ ∀ x ∈ V₀, ∀ i, ‖b.repr x i‖ ≤ C := by
    refine ⟨∑ i, ∑ j, ‖M i j‖ * ‖δ‖ + 1, ?_, fun x hx i => ?_⟩
    · have : 0 ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => by positivity
      linarith
    · have e1 : ‖b.repr x i‖ ≤ ∑ j, ‖M i j‖ * ‖δ‖ := by
        rw [hM]
        refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun j _ => ?_)
        rw [norm_mul]
        exact mul_le_mul_of_nonneg_left (hδle _ (hle (hbΛ j)) x hx) (norm_nonneg _)
      have e2 : ∑ j, ‖M i j‖ * ‖δ‖ ≤ ∑ i, ∑ j, ‖M i j‖ * ‖δ‖ :=
        Finset.single_le_sum (f := fun i => ∑ j, ‖M i j‖ * ‖δ‖)
          (fun i _ => Finset.sum_nonneg fun j _ => by positivity) (Finset.mem_univ i)
      linarith
  obtain ⟨c, hc0, hc1⟩ := NormedField.exists_norm_lt L (inv_pos.mpr hC0)
  have hcne : c ≠ 0 := norm_pos_iff.mp hc0
  have hbound : ∀ x ∈ V₀, c • x ∈ Λ := by
    intro x hx
    rw [hb]
    intro i
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, norm_mul]
    have e := hC x hx i
    have e2 : ‖c‖ * C ≤ 1 := by
      have := mul_le_mul_of_nonneg_right hc1.le hC0.le
      rwa [inv_mul_cancel₀ hC0.ne'] at this
    calc ‖c‖ * ‖b.repr x i‖ ≤ ‖c‖ * C := mul_le_mul_of_nonneg_left e hc0.le
      _ ≤ 1 := e2
  have hab : ∀ x : V, ∃ a : L, a ≠ 0 ∧ a • x ∈ V₀ := by
    intro x
    have hpos : (0 : ℝ) < (1 + ‖h x x‖)⁻¹ := by positivity
    obtain ⟨a, ha0, ha1⟩ := NormedField.exists_norm_lt L hpos
    refine ⟨a, norm_pos_iff.mp ha0, ?_⟩
    rw [hV₀, norm_q_smul hs hh]
    have hq := norm_nonneg (h x x)
    have e1 : ‖a‖ * (1 + ‖h x x‖) ≤ 1 := by
      have := mul_le_mul_of_nonneg_right ha1.le (by positivity : (0 : ℝ) ≤ 1 + ‖h x x‖)
      rwa [inv_mul_cancel₀ (by positivity)] at this
    have e2 : ‖a‖ ≤ 1 := by nlinarith
    have e3 : ‖a‖ * ‖h x x‖ ≤ 1 := by nlinarith
    calc ‖a‖ * ‖a‖ * ‖h x x‖ = ‖a‖ * (‖a‖ * ‖h x x‖) := by ring
      _ ≤ 1 * 1 := by gcongr
      _ = 1 := by norm_num
  have hlat : IsLat L V₀ :=
    hS L V Λ V₀ c ⟨m, b, hb⟩ hcne hbound hab hsmul
  have heq : V₀ = Λ := hΛ.2.2 V₀ hlat (fun x hx => (hV₀ x).mp hx) hle
  rw [← heq]
  exact hV₀ x

end GlobalTheory.CompanionTheory.HermAniso

end
