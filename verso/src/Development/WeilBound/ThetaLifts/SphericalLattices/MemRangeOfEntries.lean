import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt

noncomputable section

namespace PositivityTheory.Sph.M2

open Matrix Formalism.UG GlobalTheory.CompanionTheory.VacLoc.BigCellLocal

namespace Comm

section Abs

variable {L : Type} [Field L] (O : Subring L) {n : Type} [Fintype n] [DecidableEq n]

/- English proof (translation)
Set `A : Matrix n n O` to `fun i j => ⟨_, h1 i j⟩`. Set `B : Matrix n n O` to `fun i j => ⟨_, h2 i j⟩`. Establish `hA : O.subtype.mapMatrix A = (g : Matrix n n L)` using `by ext i j; rfl`. Establish `hB : O.subtype.mapMatrix B = ((g⁻¹ : GL n L) : Matrix n n L)` using `by ext i j; rfl`. Establish `hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n L)`.

Introduce `X Y h`. Use extensionality with `i j`. Conclude with `congrFun (congrFun h i) j`. Use `⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, hA, hB, map_one]`.

Conclude with `Units.mul_inv g`. Rewrite using `[map_mul, hA, hB, map_one]`. Conclude with `Units.inv_mul g`. Use `ext1`. Conclude with `hA`.
-/
theorem mem_range_of_entries (g : GL n L) (h1 : ∀ i j, (g : Matrix n n L) i j ∈ O)
    (h2 : ∀ i j, ((g⁻¹ : GL n L) : Matrix n n L) i j ∈ O) :
    g ∈ (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range := by
  let A : Matrix n n O := fun i j => ⟨_, h1 i j⟩
  let B : Matrix n n O := fun i j => ⟨_, h2 i j⟩
  have hA : O.subtype.mapMatrix A = (g : Matrix n n L) := by ext i j; rfl
  have hB : O.subtype.mapMatrix B = ((g⁻¹ : GL n L) : Matrix n n L) := by ext i j; rfl
  have hinj : Function.Injective (O.subtype.mapMatrix : Matrix n n O →+* Matrix n n L) := by
    intro X Y h
    ext i j
    exact congrFun (congrFun h i) j
  refine ⟨⟨A, B, hinj ?_, hinj ?_⟩, ?_⟩
  · rw [map_mul, hA, hB, map_one]; exact Units.mul_inv g
  · rw [map_mul, hA, hB, map_one]; exact Units.inv_mul g
  · ext1; exact hA

/- English proof (translation)
Establish `e : A * X * B = 1 + A * (X - 1) * B`. Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]`. Normalize the expressions using the abelian group laws. Rewrite using `[e, Matrix.add_apply]`. Use `O.add_mem ?_ ?_` and prove the remaining obligations.

Rewrite using `[Matrix.one_apply]`. Use `split_ifs`. Conclude with `O.one_mem`. Conclude with `O.zero_mem`. Rewrite using `[Matrix.mul_apply]`.

Use `O.sum_mem fun l _ => ?_` and prove the remaining obligations. Rewrite using `[Matrix.mul_apply, Finset.sum_mul]`. Use `O.sum_mem fun k _ => ?_` and prove the remaining obligations. Take `⟨y, hy, e⟩` from `hX k l`. Rewrite using `[e]`.

Establish `: A i k * (a * y) * B l j = a * (A i k * B l j) * y` using `by ring`. Rewrite using `[this]`. Conclude with `O.mul_mem (h _ _ _ _) hy`.
-/
theorem entries_conj (a : L) (A B X : Matrix n n L) (hAB : A * B = 1)
    (h : ∀ i j k l, a * (A i j * B k l) ∈ O) (hX : ∀ i j, ∃ y ∈ O, (X - 1) i j = a * y) (i j : n) :
    (A * X * B) i j ∈ O := by
  have e : A * X * B = 1 + A * (X - 1) * B := by
    rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hAB]; abel
  rw [e, Matrix.add_apply]
  refine O.add_mem ?_ ?_
  · rw [Matrix.one_apply]; split_ifs
    · exact O.one_mem
    · exact O.zero_mem
  · rw [Matrix.mul_apply]
    refine O.sum_mem fun l _ => ?_
    rw [Matrix.mul_apply, Finset.sum_mul]
    refine O.sum_mem fun k _ => ?_
    obtain ⟨y, hy, e⟩ := hX k l
    rw [e]
    have : A i k * (a * y) * B l j = a * (A i k * B l j) * y := by ring
    rw [this]
    exact O.mul_mem (h _ _ _ _) hy

/- English proof (translation)
Establish `h1 : Ideal.Quotient.mk (Ideal.span {a}) ((k : Matrix n n O) i j) = Ideal.Quotient.mk (Ideal.span {a}) ((1 : Matrix n n O) i j)`. Use `congrArg (fun g : GL n (O ⧸ Ideal.span {a}) => (g : Matrix n n (O ⧸ Ideal.span {a})) i j) (MonoidHom.mem_ker.1 hk)` as an intermediate fact. Use `Eq.trans this ?_` and prove the remaining obligations. Simplify using `only [Units.val_one, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.

Rewrite `h1` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton]`. Take `⟨y, hy⟩` from `h1`. Use `⟨y, y.2, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg O.subtype hy`. Rewrite `h2` using `[map_sub, map_mul]`.

Use `Eq.trans ?_ h2` and prove the remaining obligations. Rewrite using `[Matrix.sub_apply]`. Use `congr 1`. Simplify using `only [Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem ker_entries (a : O) (k : GL n O)
    (hk : k ∈ (Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker) (i j : n) :
    ∃ y ∈ O, (((Matrix.GeneralLinearGroup.map (n := n) O.subtype k : GL n L) : Matrix n n L) - 1) i j = (a : L) * y := by
  have h1 : Ideal.Quotient.mk (Ideal.span {a}) ((k : Matrix n n O) i j) =
      Ideal.Quotient.mk (Ideal.span {a}) ((1 : Matrix n n O) i j) := by
    have := congrArg (fun g : GL n (O ⧸ Ideal.span {a}) => (g : Matrix n n (O ⧸ Ideal.span {a})) i j)
      (MonoidHom.mem_ker.1 hk)
    refine Eq.trans this ?_
    simp only [Units.val_one, Matrix.one_apply]
    split_ifs <;> simp
  rw [Ideal.Quotient.eq, Ideal.mem_span_singleton] at h1
  obtain ⟨y, hy⟩ := h1
  refine ⟨y, y.2, ?_⟩
  have h2 := congrArg O.subtype hy
  rw [map_sub, map_mul] at h2
  refine Eq.trans ?_ h2
  rw [Matrix.sub_apply]
  congr 1
  simp only [Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce and unpack `_ ⟨k, hk, rfl⟩`. Use `⟨p⁻¹ * Matrix.GeneralLinearGroup.map (n := n) O.subtype k * p, ?_, ?_⟩` and prove the remaining obligations. Use `mem_range_of_entries O _ ?_ ?_` and prove the remaining obligations. Introduce `i j`. Rewrite using `[Units.val_mul, Units.val_mul]`.

Conclude with `entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k hk) i j`. Introduce `i j`. Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, ← map_inv, Units.val_mul, Units.val_mul]`. Conclude with `entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k⁻¹ (Subgroup.inv_mem _ hk)) i j`. Simplify using `[mul_assoc]`.
-/
theorem ker_le_conj (a : O) (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    ((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype) ≤
      ((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom := by
  rintro _ ⟨k, hk, rfl⟩
  refine ⟨p⁻¹ * Matrix.GeneralLinearGroup.map (n := n) O.subtype k * p, ?_, ?_⟩
  · refine mem_range_of_entries O _ ?_ ?_
    · intro i j
      rw [Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k hk) i j
    · intro i j
      rw [_root_.mul_inv_rev, _root_.mul_inv_rev, inv_inv, ← mul_assoc, ← map_inv, Units.val_mul, Units.val_mul]
      exact entries_conj O a _ _ _ (Units.inv_mul p) h (ker_entries O a k⁻¹ (Subgroup.inv_mem _ hk)) i j
  · simp [mul_assoc]

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n` using `n) O.subtype) := by`. Introduce `X Y h`. Use extensionality with `i j`. Conclude with `congrArg (fun g : GL n L => (g : Matrix n n L) i j) h`. Establish `h1 : (((Matrix.GeneralLinearGroup.map (n` using `n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map (Matrix.GeneralLinearGroup.map (n := n) O.subtype)).relIndex (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by`.

Rewrite using `[MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]`. Conclude with `Subgroup.FiniteIndex.index_ne_zero`. Introduce `h0`. Conclude with `h1 (Subgroup.relIndex_eq_zero_of_le_left (ker_le_conj O a p h) h0)`.
-/
theorem relIndex_conj_range (a : O) [Finite (O ⧸ Ideal.span {a})] (p : GL n L)
    (h : ∀ i j k l, (a : L) * (((p⁻¹ : GL n L) : Matrix n n L) i j * (p : Matrix n n L) k l) ∈ O) :
    (((Matrix.GeneralLinearGroup.map (n := n) O.subtype).range).map (MulAut.conj p).toMonoidHom).relIndex
      (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
  have hinj : Function.Injective (Matrix.GeneralLinearGroup.map (n := n) O.subtype) := by
    intro X Y h
    ext i j
    exact congrArg (fun g : GL n L => (g : Matrix n n L) i j) h
  have h1 : (((Matrix.GeneralLinearGroup.map (n := n) (Ideal.Quotient.mk (Ideal.span {a}))).ker).map
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype)).relIndex
        (Matrix.GeneralLinearGroup.map (n := n) O.subtype).range ≠ 0 := by
    rw [MonoidHom.range_eq_map, Subgroup.relIndex_map_map_of_injective _ _ hinj, Subgroup.relIndex_top_right]
    exact Subgroup.FiniteIndex.index_ne_zero
  intro h0
  exact h1 (Subgroup.relIndex_eq_zero_of_le_left (ker_le_conj O a p h) h0)

end Abs

section Grp

variable {G : Type} [Group G]

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, ⟨h1, h2⟩, rfl⟩`. Conclude with `⟨P.mul_mem (P.mul_mem hp h1) (P.inv_mem hp), ⟨x, h2, rfl⟩⟩`. Introduce and unpack `_ ⟨h1, x, h2, rfl⟩`. Use `⟨x, ⟨?_, h2⟩, rfl⟩` and prove the remaining obligations.

Establish `h3 : p⁻¹ * (p * x * p⁻¹) * p ∈ P` using `P.mul_mem (P.mul_mem (P.inv_mem hp) h1) hp`. Simplify `h3` using `[mul_assoc]`.
-/
theorem conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P) :
    (P ⊓ K).map (MulAut.conj p).toMonoidHom = P ⊓ K.map (MulAut.conj p).toMonoidHom := by
  apply le_antisymm
  · rintro _ ⟨x, ⟨h1, h2⟩, rfl⟩
    exact ⟨P.mul_mem (P.mul_mem hp h1) (P.inv_mem hp), ⟨x, h2, rfl⟩⟩
  · rintro _ ⟨h1, x, h2, rfl⟩
    refine ⟨x, ⟨?_, h2⟩, rfl⟩
    have h3 : p⁻¹ * (p * x * p⁻¹) * p ∈ P := P.mul_mem (P.mul_mem (P.inv_mem hp) h1) hp
    simpa [mul_assoc] using h3

/- English proof (translation)
Rewrite using `[conj_inf P K p hp, inf_comm P, inf_comm P]`. Conclude with `Subgroup.relIndex_inter_ne_zero h P`.
-/
theorem relIndex_conj_inf (P K : Subgroup G) (p : G) (hp : p ∈ P)
    (h : (K.map (MulAut.conj p).toMonoidHom).relIndex K ≠ 0) :
    ((P ⊓ K).map (MulAut.conj p).toMonoidHom).relIndex (P ⊓ K) ≠ 0 := by
  rw [conj_inf P K p hp, inf_comm P, inf_comm P]
  exact Subgroup.relIndex_inter_ne_zero h P

/- English proof (translation)
Rewrite `h` using `[← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p).toMonoidHom) _ _ (MulAut.conj p).injective, Subgroup.map_map]`. Establish `e : (MulAut.conj p).toMonoidHom.comp (MulAut.conj p⁻¹).toMonoidHom = MonoidHom.id G`. Use extensionality with `x`. Simplify using `[mul_assoc]`. Rewrite `h` using `[e, Subgroup.map_id]`. Then use the resulting hypothesis.
-/
theorem relIndex_conj_swap (K : Subgroup G) (p : G)
    (h : (K.map (MulAut.conj p⁻¹).toMonoidHom).relIndex K ≠ 0) :
    K.relIndex (K.map (MulAut.conj p).toMonoidHom) ≠ 0 := by
  rw [← Subgroup.relIndex_map_map_of_injective (f := (MulAut.conj p).toMonoidHom) _ _ (MulAut.conj p).injective,
    Subgroup.map_map] at h
  have e : (MulAut.conj p).toMonoidHom.comp (MulAut.conj p⁻¹).toMonoidHom = MonoidHom.id G := by
    ext x; simp [mul_assoc]
  rwa [e, Subgroup.map_id] at h

end Grp

section Val

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_intL (x : L) : x ∈ intL L ↔ Valued.v x ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

/- English proof (translation)
Distinguish the cases in `hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))`. Use `Filter.Eventually.of_forall fun N => ?_` and prove the remaining obligations. Rewrite using `[mem_intL, map_mul, hx, mul_zero]`. Conclude with `zero_le_one`. Take `⟨u, hu⟩` from `WithZero.ne_zero_iff_exists.1 hx`.

Use `Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd u).toNat, fun N hN => ?_⟩` and prove the remaining obligations. Rewrite using `[mem_intL, map_mul, map_pow, hv, ← hu, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]`. Simplify using `only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one, smul_neg, nsmul_eq_mul, mul_one]`. Use linear arithmetic over natural numbers and integers.
-/
theorem eventually_int (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L) :
    ∀ᶠ N : ℕ in Filter.atTop, ϖ ^ N * x ∈ intL L := by
  by_cases hx : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · refine Filter.Eventually.of_forall fun N => ?_
    rw [mem_intL, map_mul, hx, mul_zero]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 hx
    refine Filter.eventually_atTop.2 ⟨(Multiplicative.toAdd u).toNat, fun N hN => ?_⟩
    rw [mem_intL, map_mul, map_pow, hv, ← hu, ← WithZero.coe_pow, ← WithZero.coe_mul, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_mul, toAdd_pow, toAdd_ofAdd, toAdd_one, smul_neg, nsmul_eq_mul, mul_one]
    omega

/- English proof (translation)
Distinguish the cases in `h0 : Valued.v x = (0 : WithZero (Multiplicative ℤ))`. Rewrite using `[mem_intL, map_div₀, h0, zero_div]`. Conclude with `zero_le_one`. Take `⟨u, hu⟩` from `WithZero.ne_zero_iff_exists.1 h0`. Rewrite `hx` using `[← hu, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt]`.

Rewrite using `[mem_intL, map_div₀, hv, ← hu, ← WithZero.coe_div, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]`. Simplify using `only [toAdd_div, toAdd_ofAdd, toAdd_one] at hx ⊢`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_of_lt_one (ϖ : L)
    (hv : Valued.v ϖ = ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))) (x : L)
    (hx : Valued.v x < (1 : WithZero (Multiplicative ℤ))) : x / ϖ ∈ intL L := by
  by_cases h0 : Valued.v x = (0 : WithZero (Multiplicative ℤ))
  · rw [mem_intL, map_div₀, h0, zero_div]; exact zero_le_one
  · obtain ⟨u, hu⟩ := WithZero.ne_zero_iff_exists.1 h0
    rw [← hu, ← WithZero.coe_one, WithZero.coe_lt_coe, ← Multiplicative.toAdd_lt] at hx
    rw [mem_intL, map_div₀, hv, ← hu, ← WithZero.coe_div, ← WithZero.coe_one,
      WithZero.coe_le_coe, ← Multiplicative.toAdd_le]
    simp only [toAdd_div, toAdd_ofAdd, toAdd_one] at hx ⊢
    omega

/- English proof (translation)
Take `⟨-, -, -, hv, -, hq, hc⟩` from `h`. Establish `hϖ : ϖ ∈ intL L`. Rewrite using `[mem_intL, hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]`. Simplify using the standard rewrite rules. Establish `hϖ0 : ϖ ≠ 0`.

Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `WithZero.zero_ne_coe hv`. Use `⟨⟨ϖ, hϖ⟩, rfl, fun N => ?_⟩` and prove the remaining obligations. Set `M : Ideal (intL L)` to `IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring`.

Establish `hM : Finite (intL L ⧸ M)`. Establish `: Nat.card (intL L ⧸ M) = q ^ 2` using `hc`. Conclude with `Nat.finite_of_card_ne_zero (by rw [this]; positivity)`. Establish `hle : M ≤ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)}`. Introduce `x hx`.

Establish `hx' : Valued.v (x : L) < (1 : WithZero (Multiplicative ℤ))` using `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := x)).1 hx`. Rewrite using `[Ideal.mem_span_singleton]`. Use `⟨⟨_, le_of_lt_one ϖ hv x hx'⟩, Subtype.ext ?_⟩` and prove the remaining obligations. Use `show (x : L) = ϖ * ((x : L) / ϖ)`. Clear the denominators using the available nonvanishing facts.

Establish `hF : Finite (intL L ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)})` using `Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)`. Rewrite using `[← Ideal.span_singleton_pow]`. Conclude with `Ideal.finite_quotient_pow ⟨{⟨ϖ, hϖ⟩}, by simp⟩ N`.
-/
theorem finite_quot (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) :
    ∃ a : intL L, (a : L) = ϖ ∧ ∀ N : ℕ, Finite (intL L ⧸ Ideal.span {a ^ N}) := by
  obtain ⟨-, -, -, hv, -, hq, hc⟩ := h
  have hϖ : ϖ ∈ intL L := by
    rw [mem_intL, hv, ← WithZero.coe_one, WithZero.coe_le_coe, ← Multiplicative.toAdd_le]; simp
  have hϖ0 : ϖ ≠ 0 := by
    intro h0; rw [h0, map_zero] at hv; exact WithZero.zero_ne_coe hv
  refine ⟨⟨ϖ, hϖ⟩, rfl, fun N => ?_⟩
  let M : Ideal (intL L) :=
    IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring
  have hM : Finite (intL L ⧸ M) := by
    have : Nat.card (intL L ⧸ M) = q ^ 2 := hc
    exact Nat.finite_of_card_ne_zero (by rw [this]; positivity)
  have hle : M ≤ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)} := by
    intro x hx
    have hx' : Valued.v (x : L) < (1 : WithZero (Multiplicative ℤ)) :=
      (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := x)).1 hx
    rw [Ideal.mem_span_singleton]
    refine ⟨⟨_, le_of_lt_one ϖ hv x hx'⟩, Subtype.ext ?_⟩
    show (x : L) = ϖ * ((x : L) / ϖ)
    field_simp
  have hF : Finite (intL L ⧸ Ideal.span {(⟨ϖ, hϖ⟩ : intL L)}) :=
    Finite.of_surjective _ (Ideal.Quotient.factor_surjective hle)
  rw [← Ideal.span_singleton_pow]
  exact Ideal.finite_quotient_pow ⟨{⟨ϖ, hϖ⟩}, by simp⟩ N

/- English proof (translation)
Take `⟨a, ha, hF⟩` from `finite_quot ϖ c q h`. Establish `hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ i j k l, ϖ ^ N * (((p⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j * (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) k l) ∈ intL L`. Simplify using `only [Filter.eventually_all]`. Introduce `i j k l`. Conclude with `eventually_int ϖ h.2.2.2.1 _`.

Take `⟨N, hN⟩` from `hev.exists`. Use `haveI := hF N`. Use `relIndex_conj_range (intL L) (a ^ N) p ?_` and prove the remaining obligations. Rewrite using `[SubmonoidClass.coe_pow, ha]`. Conclude with `hN`.
-/
theorem relIndex_intGL (ϖ : L) (c : L →+* L) (q : ℕ) (h : IsUnramInv ϖ c q) (m : ℕ) (p : GL (Fin m ⊕ Fin m) L) :
    ((IntGL L m).map (MulAut.conj p).toMonoidHom).relIndex (IntGL L m) ≠ 0 := by
  obtain ⟨a, ha, hF⟩ := finite_quot ϖ c q h
  have hev : ∀ᶠ N : ℕ in Filter.atTop, ∀ i j k l,
      ϖ ^ N * (((p⁻¹ : GL (Fin m ⊕ Fin m) L) : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) i j *
        (p : Matrix (Fin m ⊕ Fin m) (Fin m ⊕ Fin m) L) k l) ∈ intL L := by
    simp only [Filter.eventually_all]
    intro i j k l
    exact eventually_int ϖ h.2.2.2.1 _
  obtain ⟨N, hN⟩ := hev.exists
  haveI := hF N
  refine relIndex_conj_range (intL L) (a ^ N) p ?_
  rw [SubmonoidClass.coe_pow, ha]
  exact hN

/- English proof (translation)
Use `show PW L c m ⊓ (GW L c m ⊓ IntGL L m) = _`. Establish `hle : PW L c m ≤ GW L c m` using `inf_le_left`. Rewrite using `[← inf_assoc, inf_eq_left.2 hle]`.
-/
theorem KPW_eq (c : L →+* L) (m : ℕ) : KPW L c m = PW L c m ⊓ IntGL L m := by
  show PW L c m ⊓ (GW L c m ⊓ IntGL L m) = _
  have hle : PW L c m ≤ GW L c m := inf_le_left
  rw [← inf_assoc, inf_eq_left.2 hle]

end Val

end Comm

/- English proof (translation)
Introduce `L _ _ ϖ c q h m p hp`. Rewrite using `[Comm.KPW_eq]`. Conclude with `⟨Comm.relIndex_conj_inf _ _ p hp (Comm.relIndex_intGL ϖ c q h m p), Comm.relIndex_conj_swap _ p (Comm.relIndex_conj_inf _ _ p⁻¹ (Subgroup.inv_mem _ hp) (Comm.relIndex_intGL ϖ c q h m p⁻¹))⟩`.
-/
theorem locComm : LocCommSt := by
  intro L _ _ ϖ c q h m p hp
  rw [Comm.KPW_eq]
  exact ⟨Comm.relIndex_conj_inf _ _ p hp (Comm.relIndex_intGL ϖ c q h m p),
    Comm.relIndex_conj_swap _ p
      (Comm.relIndex_conj_inf _ _ p⁻¹ (Subgroup.inv_mem _ hp) (Comm.relIndex_intGL ϖ c q h m p⁻¹))⟩

end PositivityTheory.Sph.M2

end
