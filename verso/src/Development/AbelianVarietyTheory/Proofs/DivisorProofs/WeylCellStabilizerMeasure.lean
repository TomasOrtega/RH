import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ConvUAbsU
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemWeylCellUnitaryGroupLongSimpleReflectionIff
open MeasureTheory GlobalTheory.SplitWeil GlobalTheory.SmGL GlobalTheory.SatakeBound GlobalTheory.WeylCell Formalism.UG

noncomputable section

namespace GlobalTheory.ShellU

section Balls

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

def ball (L : Type) [Field L] [Valued L (WithZero (Multiplicative ℤ))] (j : ℤ) : AddSubgroup L where
  carrier := {b | Valued.v b ≤ WithZero.exp j}
  zero_mem' := by simp
  add_mem' := fun {a b} ha hb => by
    show Valued.v (a + b) ≤ _
    exact (Valuation.map_add _ a b).trans (max_le ha hb)
  neg_mem' := fun {a} ha => by
    show Valued.v (-a) ≤ _
    rwa [Valuation.map_neg]

def antiBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {b | σ b = -b ∧ Valued.v b ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add, ha, hb, neg_add], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

def fixBall (σ : L →+* L) (j : ℤ) : AddSubgroup L where
  carrier := {f | σ f = f ∧ Valued.v f ≤ WithZero.exp j}
  zero_mem' := ⟨by simp, by simp⟩
  add_mem' := by
    rintro a b ⟨ha, ha'⟩ ⟨hb, hb'⟩
    refine ⟨by rw [map_add, ha, hb], (Valuation.map_add _ a b).trans (max_le ha' hb')⟩
  neg_mem' := by
    rintro a ⟨ha, ha'⟩
    exact ⟨by rw [map_neg, ha], by rwa [Valuation.map_neg]⟩

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_ball {j : ℤ} {b : L} : b ∈ ball L j ↔ Valued.v b ≤ WithZero.exp j := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_antiBall {σ : L →+* L} {j : ℤ} {b : L} :
    b ∈ antiBall σ j ↔ σ b = -b ∧ Valued.v b ≤ WithZero.exp j := Iff.rfl

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_fixBall {σ : L →+* L} {j : ℤ} {f : L} :
    f ∈ fixBall σ j ↔ σ f = f ∧ Valued.v f ≤ WithZero.exp j := Iff.rfl

omit [Valued L (WithZero (Multiplicative ℤ))] in

/- English proof (translation)
Establish `e1 : A = A'.comap (AddMonoidHom.mulLeft c)` using `AddSubgroup.ext hA`. Establish `e2 : B = B'.comap (AddMonoidHom.mulLeft c)` using `AddSubgroup.ext hB`. Rewrite using `[e1, AddSubgroup.relIndex_comap, e2, AddSubgroup.map_comap_eq_self_of_surjective]`. Introduce `y`. Conclude with `⟨c⁻¹ * y, mul_inv_cancel_left₀ hc y⟩`.
-/
theorem relIndex_eq_of_mul {c : L} (hc : c ≠ 0) {A B A' B' : AddSubgroup L}
    (hA : ∀ x, x ∈ A ↔ c * x ∈ A') (hB : ∀ x, x ∈ B ↔ c * x ∈ B') : A.relIndex B = A'.relIndex B' := by
  have e1 : A = A'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hA
  have e2 : B = B'.comap (AddMonoidHom.mulLeft c) := AddSubgroup.ext hB
  rw [e1, AddSubgroup.relIndex_comap, e2, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨c⁻¹ * y, mul_inv_cancel_left₀ hc y⟩

/- English proof (translation)
Proceed by induction on `y using WithZero.recZeroCoe with`. Consider the case `zero => exact zero_le'`. Consider the case `coe a`. Rewrite `h` using `[← WithZero.coe_one, WithZero.coe_lt_coe]`. Use `show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))`.

Rewrite using `[WithZero.coe_le_coe]`. Establish `h' : Multiplicative.toAdd a < 0` using `h`. Use `show Multiplicative.toAdd a ≤ -1`. Use linear arithmetic over natural numbers and integers.
-/
theorem le_exp_neg_one_of_lt_one {y : WithZero (Multiplicative ℤ)} (h : y < 1) : y ≤ WithZero.exp (-1 : ℤ) := by
  induction y using WithZero.recZeroCoe with
  | zero => exact zero_le'
  | coe a =>
    rw [← WithZero.coe_one, WithZero.coe_lt_coe] at h
    show (a : WithZero (Multiplicative ℤ)) ≤ ((Multiplicative.ofAdd (-1 : ℤ) : Multiplicative ℤ) : WithZero (Multiplicative ℤ))
    rw [WithZero.coe_le_coe]
    have h' : Multiplicative.toAdd a < 0 := h
    show Multiplicative.toAdd a ≤ -1
    omega

/- English proof (translation)
Take `⟨-, -, -, -, -, -, hcard⟩` from `hU`. Use `set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hv`. Set `f : v.valuationSubring →+ L` to `v.valuationSubring.subtype.toAddMonoidHom`. Establish `e1 : (IsLocalRing.maximalIdeal v.valuationSubring).toAddSubgroup = (ball L (-1)).comap f`. Use extensionality with `x`.

Use `show x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v (x : L) ≤ WithZero.exp (-1 : ℤ)`. Rewrite using `[Valuation.mem_maximalIdeal_iff]`. Use `⟨le_exp_neg_one_of_lt_one, fun h => h.trans_lt ?_⟩` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Evaluate the numerical expressions.

Establish `e2 : (⊤ : AddSubgroup v.valuationSubring).map f = ball L 0`. Use extensionality with `x`. Rewrite using `[mem_ball, WithZero.exp_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, -, rfl⟩`.

Conclude with `(Valuation.mem_valuationSubring_iff _ _).1 y.2`. Introduce `h`. Conclude with `⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).2 h⟩, trivial, rfl⟩`. Rewrite using `[← e2, ← AddSubgroup.relIndex_comap, ← e1, AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]`. Conclude with `hcard`.
-/
theorem relIndex_ball {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) :
    (ball L (-1)).relIndex (ball L 0) = q ^ 2 := by
  obtain ⟨-, -, -, -, -, -, hcard⟩ := hU
  set v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ))) with hv
  let f : v.valuationSubring →+ L := v.valuationSubring.subtype.toAddMonoidHom
  have e1 : (IsLocalRing.maximalIdeal v.valuationSubring).toAddSubgroup = (ball L (-1)).comap f := by
    ext x
    show x ∈ IsLocalRing.maximalIdeal v.valuationSubring ↔ v (x : L) ≤ WithZero.exp (-1 : ℤ)
    rw [Valuation.mem_maximalIdeal_iff]
    refine ⟨le_exp_neg_one_of_lt_one, fun h => h.trans_lt ?_⟩
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    norm_num
  have e2 : (⊤ : AddSubgroup v.valuationSubring).map f = ball L 0 := by
    ext x
    rw [mem_ball, WithZero.exp_zero]
    constructor
    · rintro ⟨y, -, rfl⟩
      exact (Valuation.mem_valuationSubring_iff _ _).1 y.2
    · intro h
      exact ⟨⟨x, (Valuation.mem_valuationSubring_iff _ _).2 h⟩, trivial, rfl⟩
  rw [← e2, ← AddSubgroup.relIndex_comap, ← e1, AddSubgroup.relIndex_top_right, AddSubgroup.index_eq_card]
  exact hcard

/- English proof (translation)
Take `⟨hσ, -, hϖ, hv, ⟨x, -, hx⟩, -, -⟩` from `hU`. Establish `hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ)` using `hv`. Use `set δ := σ x - x with hδ`. Establish `hσδ : σ δ = -δ` using `by rw [hδ, map_sub, hσ]; ring`. Establish `hδ0 : δ ≠ 0` using `fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx`.

Establish `hϖ0 : ϖ ≠ 0` using `fun h => by rw [h, map_zero] at hv'; exact WithZero.exp_ne_zero hv'.symm`. Establish `hc : δ * ϖ ^ (j + 1) ≠ 0` using `mul_ne_zero hδ0 (zpow_ne_zero _ hϖ0)`. Establish `key : ∀ (i : ℤ) (z : L), z ∈ antiBall σ (i + (j + 1)) ↔ δ * ϖ ^ (j + 1) * z ∈ fixBall σ i`. Introduce `i z`. Rewrite using `[mem_antiBall, mem_fixBall]`.

Use `and_congr ?_ ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_zpow₀, hϖ, hσδ]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h]`.

Expand and normalize the polynomial expressions, which then agree. Introduce `h`. Apply `mul_left_cancel₀ hc` to reduce the goal to its premises. Take the linear combination `-h`. Rewrite using `[map_mul, map_mul, map_zpow₀, hx, hv', one_mul, ← WithZero.exp_zsmul, WithZero.exp_add, smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_comm]`.

Use `relIndex_eq_of_mul hc (fun z => ?_) (fun z => ?_)` and prove the remaining obligations. Rewrite using `[← key]`. Use `congr! 2`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← key]`.

Use `congr! 2`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relIndex_anti_eq_fix {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
  obtain ⟨hσ, -, hϖ, hv, ⟨x, -, hx⟩, -, -⟩ := hU
  have hv' : Valued.v ϖ = WithZero.exp (-1 : ℤ) := hv
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  have hϖ0 : ϖ ≠ 0 := fun h => by rw [h, map_zero] at hv'; exact WithZero.exp_ne_zero hv'.symm
  have hc : δ * ϖ ^ (j + 1) ≠ 0 := mul_ne_zero hδ0 (zpow_ne_zero _ hϖ0)
  have key : ∀ (i : ℤ) (z : L), z ∈ antiBall σ (i + (j + 1)) ↔ δ * ϖ ^ (j + 1) * z ∈ fixBall σ i := by
    intro i z
    rw [mem_antiBall, mem_fixBall]
    refine and_congr ?_ ?_
    · rw [map_mul, map_mul, map_zpow₀, hϖ, hσδ]
      constructor
      · intro h; rw [h]; ring
      · intro h
        apply mul_left_cancel₀ hc
        linear_combination -h
    · rw [map_mul, map_mul, map_zpow₀, hx, hv', one_mul, ← WithZero.exp_zsmul, WithZero.exp_add,
        smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_comm]
  refine relIndex_eq_of_mul hc (fun z => ?_) (fun z => ?_)
  · rw [← key]; congr! 2; ring
  · rw [← key]; congr! 2; ring

/- English proof (translation)
Establish `h0` using `relIndex_ball hU`. Establish `h1` using `relIndex_anti_eq_fix hU (-1)`. Rewrite using `[relIndex_anti_eq_fix hU j]`. Take `⟨hσ, hvσ, -, -, ⟨x, hxO, hx⟩, -, -⟩` from `hU`. Use `set δ := σ x - x with hδ`.

Establish `hσδ : σ δ = -δ` using `by rw [hδ, map_sub, hσ]; ring`. Establish `hδ0 : δ ≠ 0` using `fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx`. Use `set e := -x / δ with he`. Establish `he1 : e + σ e = 1`. Rewrite using `[he, map_div₀, map_neg, hσδ]`.

Clear the denominators using the available nonvanishing facts. Rewrite using `[hδ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hve : Valued.v e ≤ 1`. Rewrite using `[he, map_div₀, hx, div_one, Valuation.map_neg]`.

Conclude with `(Valuation.mem_integer_iff _ _).1 hxO`. Set `t : L →+ L` to `AddMonoidHom.id L - σ.toAddMonoidHom`. Establish `ht : ∀ z, t z = z - σ z` using `fun z => rfl`. Establish `hte : ∀ b, σ b = -b → t (e * b) = b` using `fun b hb => by`. Rewrite using `[ht, map_mul, hb]`.

Take the linear combination `b * he1`. Establish `hσt : ∀ z, σ (t z) = -t z` using `fun z => by rw [ht, map_sub, hσ]; ring`. Establish `hvt : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (t z) ≤ WithZero.exp (i : ℤ)` using `fun z i h => (Valuation.map_sub _ _ _).trans (max_le h ((hvσ z).le.trans h))`. Establish `hve' : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (e * z) ≤ WithZero.exp (i : ℤ)` using `fun z i h => by`. Rewrite using `[map_mul]`.

Conclude with `(mul_le_mul' hve h).trans (one_mul _).le`. Establish `hle : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ)` using `WithZero.exp_le_exp.2 (by norm_num)`. Establish `a1 : (ball L 0).map t = antiBall σ 0`. Use extensionality with `b`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `⟨hσt z, hvt z 0 hz⟩`. Introduce and unpack `⟨hb, hb'⟩`. Conclude with `⟨e * b, hve' b 0 hb', hte b hb⟩`. Establish `a2 : (antiBall σ (-1)).comap t ⊓ ball L 0 = fixBall σ 0 ⊔ ball L (-1)`.

Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `z ⟨⟨-, hz⟩, hz'⟩`. Use `AddSubgroup.mem_sup.2 ⟨z - e * t z, ⟨?_, ?_⟩, e * t z, hve' _ _ hz, by ring⟩` and prove the remaining obligations. Establish `: t (z - e * t z) = 0` using `by rw [map_sub, hte _ (hσt z), sub_self]`. Rewrite `this` using `[ht]`.

Conclude with `(sub_eq_zero.1 this).symm`. Conclude with `(Valuation.map_sub _ _ _).trans (max_le hz' ((hve' _ _ hz).trans hle))`. Use `sup_le (fun z hz => ⟨⟨hσt z, ?_⟩, hz.2⟩) (fun z hz => ⟨⟨hσt z, hvt z _ hz⟩, le_trans hz hle⟩)` and prove the remaining obligations. Rewrite using `[ht, hz.1, sub_self, map_zero]`. Conclude with `zero_le'`.

Establish `a3 : ball L (-1) ⊓ fixBall σ 0 = fixBall σ (-1)` using `le_antisymm (fun z hz => ⟨hz.2.1, hz.1⟩) (fun z hz => ⟨hz.2, hz.1, hz.2.trans hle⟩)`. Establish `b1 : (fixBall σ 0 ⊔ ball L (-1)).relIndex (ball L 0) = (fixBall σ (-1)).relIndex (fixBall σ 0)`. Rewrite using `[← a2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, a1, ← h1]`. Evaluate the numerical expressions. Establish `b2 : (ball L (-1)).relIndex (fixBall σ 0 ⊔ ball L (-1)) = (fixBall σ (-1)).relIndex (fixBall σ 0)`.

Rewrite using `[AddSubgroup.relIndex_sup_right, ← a3, AddSubgroup.inf_relIndex_right]`. Establish `b3` using `AddSubgroup.relIndex_mul_relIndex (ball L (-1)) (fixBall σ 0 ⊔ ball L (-1)) (ball L 0) le_sup_right (by rw [← a2]; exact inf_le_right)`. Rewrite `b3` using `[b1, b2, h0, ← sq]`. Conclude with `Nat.pow_left_injective two_ne_zero b3`.
-/
theorem relIndex_antiBall {ϖ : L} {σ : L →+* L} {q : ℕ} (hU : IsUnramInv ϖ σ q) (j : ℤ) :
    (antiBall σ j).relIndex (antiBall σ (j + 1)) = q := by
  have h0 := relIndex_ball hU
  have h1 := relIndex_anti_eq_fix hU (-1)
  rw [relIndex_anti_eq_fix hU j]
  obtain ⟨hσ, hvσ, -, -, ⟨x, hxO, hx⟩, -, -⟩ := hU
  set δ := σ x - x with hδ
  have hσδ : σ δ = -δ := by rw [hδ, map_sub, hσ]; ring
  have hδ0 : δ ≠ 0 := fun h => by rw [h, map_zero] at hx; exact zero_ne_one hx
  set e := -x / δ with he
  have he1 : e + σ e = 1 := by
    rw [he, map_div₀, map_neg, hσδ]; field_simp; rw [hδ]; ring
  have hve : Valued.v e ≤ 1 := by
    rw [he, map_div₀, hx, div_one, Valuation.map_neg]
    exact (Valuation.mem_integer_iff _ _).1 hxO
  let t : L →+ L := AddMonoidHom.id L - σ.toAddMonoidHom
  have ht : ∀ z, t z = z - σ z := fun z => rfl
  have hte : ∀ b, σ b = -b → t (e * b) = b := fun b hb => by
    rw [ht, map_mul, hb]; linear_combination b * he1
  have hσt : ∀ z, σ (t z) = -t z := fun z => by rw [ht, map_sub, hσ]; ring
  have hvt : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (t z) ≤ WithZero.exp (i : ℤ) := fun z i h =>
    (Valuation.map_sub _ _ _).trans (max_le h ((hvσ z).le.trans h))
  have hve' : ∀ z i, Valued.v z ≤ WithZero.exp i → Valued.v (e * z) ≤ WithZero.exp (i : ℤ) := fun z i h => by
    rw [map_mul]; exact (mul_le_mul' hve h).trans (one_mul _).le
  have hle : WithZero.exp (-1 : ℤ) ≤ WithZero.exp (0 : ℤ) := WithZero.exp_le_exp.2 (by norm_num)
  have a1 : (ball L 0).map t = antiBall σ 0 := by
    ext b
    constructor
    · rintro ⟨z, hz, rfl⟩
      exact ⟨hσt z, hvt z 0 hz⟩
    · rintro ⟨hb, hb'⟩
      exact ⟨e * b, hve' b 0 hb', hte b hb⟩
  have a2 : (antiBall σ (-1)).comap t ⊓ ball L 0 = fixBall σ 0 ⊔ ball L (-1) := by
    apply le_antisymm
    · rintro z ⟨⟨-, hz⟩, hz'⟩
      refine AddSubgroup.mem_sup.2 ⟨z - e * t z, ⟨?_, ?_⟩, e * t z, hve' _ _ hz, by ring⟩
      · have : t (z - e * t z) = 0 := by rw [map_sub, hte _ (hσt z), sub_self]
        rw [ht] at this
        exact (sub_eq_zero.1 this).symm
      · exact (Valuation.map_sub _ _ _).trans (max_le hz' ((hve' _ _ hz).trans hle))
    · refine sup_le (fun z hz => ⟨⟨hσt z, ?_⟩, hz.2⟩) (fun z hz => ⟨⟨hσt z, hvt z _ hz⟩, le_trans hz hle⟩)
      rw [ht, hz.1, sub_self, map_zero]; exact zero_le'
  have a3 : ball L (-1) ⊓ fixBall σ 0 = fixBall σ (-1) :=
    le_antisymm (fun z hz => ⟨hz.2.1, hz.1⟩) (fun z hz => ⟨hz.2, hz.1, hz.2.trans hle⟩)
  have b1 : (fixBall σ 0 ⊔ ball L (-1)).relIndex (ball L 0) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [← a2, AddSubgroup.inf_relIndex_right, AddSubgroup.relIndex_comap, a1, ← h1]; norm_num
  have b2 : (ball L (-1)).relIndex (fixBall σ 0 ⊔ ball L (-1)) = (fixBall σ (-1)).relIndex (fixBall σ 0) := by
    rw [AddSubgroup.relIndex_sup_right, ← a3, AddSubgroup.inf_relIndex_right]
  have b3 := AddSubgroup.relIndex_mul_relIndex (ball L (-1)) (fixBall σ 0 ⊔ ball L (-1)) (ball L 0) le_sup_right
    (by rw [← a2]; exact inf_le_right)
  rw [b1, b2, h0, ← sq] at b3
  exact Nat.pow_left_injective two_ne_zero b3

end Balls

/- English proof (translation)
Establish `hemb : MeasurableEmbedding (K.subtype : K → G)` using `MeasurableEmbedding.subtype_coe hK`. Use `haveI : (μ.comap (K.subtype : K → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb`. Use `haveI : (H.subgroupOf K).FiniteIndex := ⟨hi⟩`. Establish `key` using `(H.subgroupOf K).index_mul_measure (hemb.measurable hH) (μ.comap (K.subtype : K → G))`. Rewrite `key` using `[hemb.comap_apply, hemb.comap_apply]`.

Establish `e1 : (K.subtype : K → G) '' Set.univ = (K : Set G)`. Use extensionality with `x`. Simplify using the standard rewrite rules. Establish `e2 : (K.subtype : K → G) '' ((H.subgroupOf K : Subgroup K) : Set K) = (H : Set G)`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `hy`. Introduce `hx`. Conclude with `⟨⟨x, hle hx⟩, hx, rfl⟩`.

Rewrite `key` using `[e1, e2]`. Conclude with `key.symm`.
-/
theorem measure_eq_relIndex_mul {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [MeasurableSpace G] [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant]
    (H K : Subgroup G) (hH : MeasurableSet (H : Set G)) (hK : MeasurableSet (K : Set G)) (hle : H ≤ K)
    (hi : H.relIndex K ≠ 0) : μ K = (H.relIndex K : ENNReal) * μ H := by
  have hemb : MeasurableEmbedding (K.subtype : K → G) := MeasurableEmbedding.subtype_coe hK
  haveI : (μ.comap (K.subtype : K → G)).IsMulLeftInvariant := Measure.IsMulLeftInvariant.comap μ hemb
  haveI : (H.subgroupOf K).FiniteIndex := ⟨hi⟩
  have key := (H.subgroupOf K).index_mul_measure (hemb.measurable hH) (μ.comap (K.subtype : K → G))
  rw [hemb.comap_apply, hemb.comap_apply] at key
  have e1 : (K.subtype : K → G) '' Set.univ = (K : Set G) := by
    ext x; simp
  have e2 : (K.subtype : K → G) '' ((H.subgroupOf K : Subgroup K) : Set K) = (H : Set G) := by
    ext x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact hy
    · intro hx
      exact ⟨⟨x, hle hx⟩, hx, rfl⟩
  rw [e1, e2] at key
  exact key.symm

/- English proof (translation)
Establish `hq0 : (q : ENNReal) ≠ 0` using `Nat.cast_ne_zero.2 hq`. Establish `hqt : (q : ENNReal) ≠ ⊤` using `ENNReal.natCast_ne_top q`. Establish `step : ∀ j, μ (H (j + 1)) = q * μ (H j)` using `fun j => by`. Rewrite using `[measure_eq_relIndex_mul μ (H j) (H (j + 1)) (hm _) (hm _) (hle j) (by rw [hi]; exact hq), hi]`. Proceed by induction on `j using Int.induction_on with`.

Consider the case `zero => rw [h0, zpow_zero]`. Consider the case `succ i ih => rw [step, ih, ENNReal.zpow_add hq0 hqt, zpow_one, mul_comm]`. Consider the case `pred i ih`. Establish `h` using `step (-(i : ℤ) - 1)`. Rewrite `h` using `[sub_add_cancel, ih]`.

Apply `(ENNReal.mul_right_inj hq0 hqt).1` to reduce the goal to its premises. Rewrite using `[← h]`. Use `conv_lhs => rw [show -(i : ℤ) = 1 + (-(i : ℤ) - 1) by ring, ENNReal.zpow_add hq0 hqt, zpow_one]`.
-/
theorem measure_chain {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [MeasurableSpace G]
    [BorelSpace G] (μ : Measure G) [μ.IsMulLeftInvariant] (H : ℤ → Subgroup G) {q : ℕ} (hq : q ≠ 0)
    (hm : ∀ j, MeasurableSet (H j : Set G)) (hle : ∀ j, H j ≤ H (j + 1))
    (hi : ∀ j, (H j).relIndex (H (j + 1)) = q) (h0 : μ (H 0) = 1) (j : ℤ) : μ (H j) = (q : ENNReal) ^ j := by
  have hq0 : (q : ENNReal) ≠ 0 := Nat.cast_ne_zero.2 hq
  have hqt : (q : ENNReal) ≠ ⊤ := ENNReal.natCast_ne_top q
  have step : ∀ j, μ (H (j + 1)) = q * μ (H j) := fun j => by
    rw [measure_eq_relIndex_mul μ (H j) (H (j + 1)) (hm _) (hm _) (hle j) (by rw [hi]; exact hq), hi]
  induction j using Int.induction_on with
  | zero => rw [h0, zpow_zero]
  | succ i ih => rw [step, ih, ENNReal.zpow_add hq0 hqt, zpow_one, mul_comm]
  | pred i ih =>
    have h := step (-(i : ℤ) - 1)
    rw [sub_add_cancel, ih] at h
    apply (ENNReal.mul_right_inj hq0 hqt).1
    rw [← h]
    conv_lhs => rw [show -(i : ℤ) = 1 + (-(i : ℤ) - 1) by ring, ENNReal.zpow_add hq0 hqt, zpow_one]

/- English proof (translation)
Establish `e : {x : L | Valued.v x ≤ WithZero.exp j} = (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L)`. Use extensionality with `x`. Use `show _ ↔ Valued.v (ϖ ^ j * x) ≤ 1`. Rewrite using `[map_mul, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg, inv_mul_le_iff₀ WithZero.exp_pos, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[e]`. Conclude with `(Valued.isOpen_integer L).preimage (continuous_const.mul continuous_id)`.
-/
theorem isOpen_ball {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))] {ϖ : L}
    (hv : Valued.v ϖ = WithZero.exp (-1 : ℤ)) (j : ℤ) : IsOpen {x : L | Valued.v x ≤ WithZero.exp j} := by
  have e : {x : L | Valued.v x ≤ WithZero.exp j} = (fun x => ϖ ^ j * x) ⁻¹' (intL L : Set L) := by
    ext x
    show _ ↔ Valued.v (ϖ ^ j * x) ≤ 1
    rw [map_mul, map_zpow₀, hv, ← WithZero.exp_zsmul, smul_eq_mul, mul_neg, mul_one, WithZero.exp_neg,
      inv_mul_le_iff₀ WithZero.exp_pos, mul_one]
    rfl
  rw [e]
  exact (Valued.isOpen_integer L).preimage (continuous_const.mul continuous_id)

/- English proof (translation)
Introduce `L _ _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ j`. Establish `hidx` using `relIndex_antiBall hU`. Take `⟨-, -, -, hv, -, hq2, -⟩` from `hU`. Establish `haa : lo k ≠ (lo k).rev`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Fin.val_rev, Fin.coe_castLE] at this`. Use `k.2` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `hshape` using `cellU_rankOne_shape L σ n k hk hn y hy`.

Use `set a := lo k with ha`. Set `M : cellU y → Matrix (Fin n) (Fin n) L` to `fun u => (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)`. Set `c : cellU y → L` to `fun u => M u a a.rev`. Establish `hstr : ∀ u : cellU y, M u = 1 + Matrix.single a a.rev (c u)`. Introduce `u`.

Use extensionality with `i l`. Rewrite using `[Matrix.add_apply, Matrix.single_apply]`. Use `split_ifs with h`. Take `⟨rfl, rfl⟩` from `h`. Rewrite using `[Matrix.one_apply_ne haa, zero_add]`.

Rewrite using `[add_zero]`. Conclude with `(hshape u).1 u.2 i l (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)`. Establish `hprod : ∀ b d : L, (1 + Matrix.single a a.rev b) * (1 + Matrix.single a a.rev d) = 1 + Matrix.single a a.rev (b + d)`. Introduce `b d`. Rewrite using `[Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ haa.symm, Matrix.single_add]`.

Simplify using `only [Matrix.one_mul, Matrix.mul_one, add_zero]`. Normalize the expressions using the abelian group laws. Establish `hent : ∀ b : L, (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) a a.rev = b`. Introduce `b`. Rewrite using `[Matrix.add_apply, Matrix.one_apply_ne haa, Matrix.single_apply_same, zero_add]`.

Establish `hM : ∀ u w : cellU y, M (u * w) = M u * M w` using `fun u w => rfl`. Establish `hmul : ∀ u w : cellU y, c (u * w) = c u + c w`. Introduce `u w`. Use `show M (u * w) a a.rev = c u + c w`. Rewrite using `[hM, hstr u, hstr w, hprod, hent]`.

Establish `hone : c 1 = 0` using `Matrix.one_apply_ne haa`. Establish `hinv : ∀ u, c u⁻¹ = -c u` using `fun u => by`. Use `hmul u⁻¹ u` as an intermediate fact. Rewrite `this` using `[inv_mul_cancel, hone]`. Take the linear combination `-this`.

Establish `hanti : ∀ u, σ (c u) = -c u` using `fun u => by`. Use `(LGrp.mem_GU_iff σ n _).1 (u : GU σ n).2 a a.rev` as an intermediate fact. Rewrite `this` using `[Fin.rev_rev]`. Rewrite using `[← hinv]`. Conclude with `this.symm`.

Establish `hsurj : ∀ b : L, σ b = -b → ∃ u : cellU y, c u = b`. Introduce `b hb`. Set `g : GL (Fin n) L` to `⟨1 + Matrix.single a a.rev b, 1 + Matrix.single a a.rev (-b), by rw [hprod]; simp, by rw [hprod]; simp⟩`. Establish `hg : g ∈ GU σ n`. Rewrite using `[LGrp.mem_GU_iff]`.

Introduce `i l`. Use `show (1 + Matrix.single a a.rev (-b) : Matrix (Fin n) (Fin n) L) i l = σ ((1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) l.rev i.rev)`. Rewrite using `[Matrix.add_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply, Matrix.single_apply, apply_ite σ, apply_ite σ, map_one, map_zero, hb]`. Use `congr 1`. Conclude with `if_congr (by rw [Fin.rev_inj, eq_comm]) rfl rfl`.

Use `if_congr ?_ rfl rfl` and prove the remaining obligations. Rewrite using `[Fin.rev_inj, and_comm, Fin.rev_eq_iff]`. Use `⟨⟨⟨g, hg⟩, (hshape _).2 fun i l h => ?_⟩, hent b⟩` and prove the remaining obligations. Use `show (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) i l = _`. Rewrite using `[Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]`.

Set `φ : cellU y →* Multiplicative L` to `{ toFun := fun u => Multiplicative.ofAdd (c u) map_one' := by simp only [hone]; rfl map_mul' := fun u w => by simp only [hmul]; rfl }`. Set `H : ℤ → Subgroup (cellU y)` to `fun j => (AddSubgroup.toSubgroup (antiBall σ j)).comap φ`. Establish `memH : ∀ j (u : cellU y), u ∈ H j ↔ Valued.v (c u) ≤ WithZero.exp j`. Introduce `j u`. Use `show (c u) ∈ antiBall σ j ↔ _`.

Rewrite using `[mem_antiBall]`. Conclude with `⟨fun h => h.2, fun h => ⟨hanti u, h⟩⟩`. Establish `hset : ∀ j, (H j : Set (cellU y)) = c ⁻¹' {x : L | Valued.v x ≤ WithZero.exp j}` using `fun j => Set.ext (memH j)`. Establish `hc : Continuous c` using `(Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a a.rev`. Establish `hm : ∀ j, MeasurableSet (H j : Set (cellU y))` using `fun j => by`.

Rewrite using `[hset]`. Conclude with `((isOpen_ball hv j).preimage hc).measurableSet`. Establish `hle : ∀ j, H j ≤ H (j + 1)` using `fun j u hu => (memH _ _).2 (((memH _ _).1 hu).trans (WithZero.exp_le_exp.2 (by omega)))`. Establish `hi : ∀ j, (H j).relIndex (H (j + 1)) = q` using `fun j => by show ((AddSubgroup.toSubgroup (antiBall σ j)).comap φ).relIndex ((AddSubgroup.toSubgroup (antiBall σ (j + 1))).comap φ) = q`. Rewrite using `[Subgroup.relIndex_comap, Subgroup.map_comap_eq_self, AddSubgroup.relIndex_toSubgroup, hidx]`.

Introduce `b hb`. Take `⟨u, hu⟩` from `hsurj (Multiplicative.toAdd b) hb.1`. Conclude with `⟨u, congrArg Multiplicative.ofAdd hu⟩`. Establish `hint : ∀ u : cellU y, Valued.v (c u) ≤ 1 → ∀ i l, M u i l ∈ intL L`. Introduce `u hu i l`.

Rewrite using `[hstr u, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]`. Apply the tactic sequence `refine add_mem ?_ ?_ <;> split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Conclude with `hu`.

Conclude with `zero_mem _`. Establish `hH0 : H 0 = (KU σ n).subgroupOf (cellU y)`. Use extensionality with `u`. Rewrite using `[memH, WithZero.exp_zero, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, LFun.IntPtsUnitary.coe_KU, LFun.IntPtsUnitary.coe_GLint]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Conclude with `⟨hint u h, hint u⁻¹ (by rwa [hinv, Valuation.map_neg])⟩`. Introduce `h`. Conclude with `h.1 a a.rev`. Establish `hfin` using `measure_chain μ H (q := q) (by omega) hm hle hi (by rw [hH0]; exact hμ) j`.

Establish `hmj` using `hm j`. Rewrite `hfin`, `hmj` using `[hset]`. Conclude with `⟨hmj, hfin⟩`.
-/
theorem shell_measure : ∀ (L : Type) [Field L] [CharZero L] [Valued L (WithZero (Multiplicative ℤ))] [CompleteSpace L]
    (ϖ : L) (σ : L →+* L) (q : ℕ), IsUnramInv ϖ σ q → ∀ (n : ℕ) (k : Fin (n / 2)), ¬ k.val + 1 < n / 2 →
    Even n → ∀ (y : GU σ n), y ∈ KU σ n → IsWeylRep (simpleU k) (y : GL (Fin n) L) →
    ∀ [MeasurableSpace (cellU y)] [BorelSpace (cellU y)] (μ : Measure (cellU y)) [μ.IsHaarMeasure],
    μ ((KU σ n).subgroupOf (cellU y)) = 1 → ∀ (j : ℤ),
    MeasurableSet {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} ∧
    μ {u : cellU y | Valued.v ((((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) (lo k) (lo k).rev) ≤
        ((Multiplicative.ofAdd j : Multiplicative ℤ) : WithZero (Multiplicative ℤ))} = (q : ENNReal) ^ j := by
  intro L _ _ _ _ ϖ σ q hU n k hk hn y hyK hy _ _ μ _ hμ j
  have hidx := relIndex_antiBall hU
  obtain ⟨-, -, -, hv, -, hq2, -⟩ := hU
  have haa : lo k ≠ (lo k).rev := by
    intro h
    have := congrArg Fin.val h
    simp only [Fin.val_rev, Fin.coe_castLE] at this
    have := k.2
    omega
  have hshape := cellU_rankOne_shape L σ n k hk hn y hy
  set a := lo k with ha
  let M : cellU y → Matrix (Fin n) (Fin n) L := fun u => (((u : GU σ n) : GL (Fin n) L) : Matrix (Fin n) (Fin n) L)
  let c : cellU y → L := fun u => M u a a.rev
  have hstr : ∀ u : cellU y, M u = 1 + Matrix.single a a.rev (c u) := by
    intro u
    ext i l
    rw [Matrix.add_apply, Matrix.single_apply]
    split_ifs with h
    · obtain ⟨rfl, rfl⟩ := h
      rw [Matrix.one_apply_ne haa, zero_add]
    · rw [add_zero]
      exact (hshape u).1 u.2 i l (fun h' => h ⟨h'.1.symm, h'.2.symm⟩)
  have hprod : ∀ b d : L, (1 + Matrix.single a a.rev b) * (1 + Matrix.single a a.rev d) =
      1 + Matrix.single a a.rev (b + d) := by
    intro b d
    rw [Matrix.add_mul, Matrix.mul_add, Matrix.mul_add, Matrix.single_mul_single_of_ne _ _ _ _ haa.symm,
      Matrix.single_add]
    simp only [Matrix.one_mul, Matrix.mul_one, add_zero]
    abel
  have hent : ∀ b : L, (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) a a.rev = b := by
    intro b
    rw [Matrix.add_apply, Matrix.one_apply_ne haa, Matrix.single_apply_same, zero_add]
  have hM : ∀ u w : cellU y, M (u * w) = M u * M w := fun u w => rfl
  have hmul : ∀ u w : cellU y, c (u * w) = c u + c w := by
    intro u w
    show M (u * w) a a.rev = c u + c w
    rw [hM, hstr u, hstr w, hprod, hent]
  have hone : c 1 = 0 := Matrix.one_apply_ne haa
  have hinv : ∀ u, c u⁻¹ = -c u := fun u => by
    have := hmul u⁻¹ u
    rw [inv_mul_cancel, hone] at this
    linear_combination -this
  have hanti : ∀ u, σ (c u) = -c u := fun u => by
    have := (LGrp.mem_GU_iff σ n _).1 (u : GU σ n).2 a a.rev
    rw [Fin.rev_rev] at this
    rw [← hinv]
    exact this.symm
  have hsurj : ∀ b : L, σ b = -b → ∃ u : cellU y, c u = b := by
    intro b hb
    let g : GL (Fin n) L := ⟨1 + Matrix.single a a.rev b, 1 + Matrix.single a a.rev (-b),
      by rw [hprod]; simp, by rw [hprod]; simp⟩
    have hg : g ∈ GU σ n := by
      rw [LGrp.mem_GU_iff]
      intro i l
      show (1 + Matrix.single a a.rev (-b) : Matrix (Fin n) (Fin n) L) i l =
        σ ((1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) l.rev i.rev)
      rw [Matrix.add_apply, Matrix.add_apply, map_add, Matrix.one_apply, Matrix.one_apply, Matrix.single_apply,
        Matrix.single_apply, apply_ite σ, apply_ite σ, map_one, map_zero, hb]
      congr 1
      · exact if_congr (by rw [Fin.rev_inj, eq_comm]) rfl rfl
      · refine if_congr ?_ rfl rfl
        rw [Fin.rev_inj, and_comm, Fin.rev_eq_iff]
    refine ⟨⟨⟨g, hg⟩, (hshape _).2 fun i l h => ?_⟩, hent b⟩
    show (1 + Matrix.single a a.rev b : Matrix (Fin n) (Fin n) L) i l = _
    rw [Matrix.add_apply, Matrix.single_apply, if_neg (fun h' => h ⟨h'.1.symm, h'.2.symm⟩), add_zero]
  let φ : cellU y →* Multiplicative L :=
    { toFun := fun u => Multiplicative.ofAdd (c u)
      map_one' := by simp only [hone]; rfl
      map_mul' := fun u w => by simp only [hmul]; rfl }
  let H : ℤ → Subgroup (cellU y) := fun j => (AddSubgroup.toSubgroup (antiBall σ j)).comap φ
  have memH : ∀ j (u : cellU y), u ∈ H j ↔ Valued.v (c u) ≤ WithZero.exp j := by
    intro j u
    show (c u) ∈ antiBall σ j ↔ _
    rw [mem_antiBall]
    exact ⟨fun h => h.2, fun h => ⟨hanti u, h⟩⟩
  have hset : ∀ j, (H j : Set (cellU y)) = c ⁻¹' {x : L | Valued.v x ≤ WithZero.exp j} :=
    fun j => Set.ext (memH j)
  have hc : Continuous c :=
    (Units.continuous_val.comp (continuous_subtype_val.comp continuous_subtype_val)).matrix_elem a a.rev
  have hm : ∀ j, MeasurableSet (H j : Set (cellU y)) := fun j => by
    rw [hset]
    exact ((isOpen_ball hv j).preimage hc).measurableSet
  have hle : ∀ j, H j ≤ H (j + 1) := fun j u hu =>
    (memH _ _).2 (((memH _ _).1 hu).trans (WithZero.exp_le_exp.2 (by omega)))
  have hi : ∀ j, (H j).relIndex (H (j + 1)) = q := fun j => by
    show ((AddSubgroup.toSubgroup (antiBall σ j)).comap φ).relIndex
      ((AddSubgroup.toSubgroup (antiBall σ (j + 1))).comap φ) = q
    rw [Subgroup.relIndex_comap, Subgroup.map_comap_eq_self, AddSubgroup.relIndex_toSubgroup, hidx]
    intro b hb
    obtain ⟨u, hu⟩ := hsurj (Multiplicative.toAdd b) hb.1
    exact ⟨u, congrArg Multiplicative.ofAdd hu⟩
  have hint : ∀ u : cellU y, Valued.v (c u) ≤ 1 → ∀ i l, M u i l ∈ intL L := by
    intro u hu i l
    rw [hstr u, Matrix.add_apply, Matrix.one_apply, Matrix.single_apply]
    refine add_mem ?_ ?_ <;> split_ifs
    · exact one_mem _
    · exact zero_mem _
    · exact hu
    · exact zero_mem _
  have hH0 : H 0 = (KU σ n).subgroupOf (cellU y) := by
    ext u
    rw [memH, WithZero.exp_zero, Subgroup.mem_subgroupOf, ← SetLike.mem_coe, LFun.IntPtsUnitary.coe_KU,
      LFun.IntPtsUnitary.coe_GLint]
    constructor
    · intro h
      exact ⟨hint u h, hint u⁻¹ (by rwa [hinv, Valuation.map_neg])⟩
    · intro h
      exact h.1 a a.rev
  have hfin := measure_chain μ H (q := q) (by omega) hm hle hi (by rw [hH0]; exact hμ) j
  have hmj := hm j
  rw [hset] at hfin hmj
  exact ⟨hmj, hfin⟩

end GlobalTheory.ShellU

end
