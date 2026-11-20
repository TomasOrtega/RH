import Development.WeilBound.ThetaLifts.SphericalLattices.LocCommSt

noncomputable section

namespace PositivityTheory.Sph.M2.ZC

open Matrix Formalism.UG

/- English proof (translation)
Use `Nat.card_congr (Equiv.ofBijective (Quotient.map' f (fun a b hab => ?_) : A ⧸ H.comap f → G ⧸ H) ⟨?_, ?_⟩)` and prove the remaining obligations. Rewrite `hab`, the goal using `[QuotientGroup.leftRel_apply]`. Simplify using `using hab`. Introduce `a b`. Proceed by induction on `a using QuotientGroup.induction_on with | H a => ?_`.

Proceed by induction on `b using QuotientGroup.induction_on with | H b => ?_`. Introduce `hab`. Establish `h1 : ((f a : G) : G ⧸ H) = (f b : G)` using `hab`. Rewrite `h1`, the goal using `[QuotientGroup.eq]`. Simplify using `using h1`.

Introduce `g`. Proceed by induction on `g using QuotientGroup.induction_on with | H g => ?_`. Take `⟨a, ha⟩` from `h g`. Conclude with `⟨(a : A ⧸ H.comap f), (QuotientGroup.eq.mpr ha : ((f a : G) : G ⧸ H) = g)⟩`.
-/
theorem index_comap_of_cover {A G : Type*} [Group A] [Group G] (f : A →* G) (H : Subgroup G)
    (h : ∀ g, ∃ a, (f a)⁻¹ * g ∈ H) : (H.comap f).index = H.index := by
  refine Nat.card_congr (Equiv.ofBijective
    (Quotient.map' f (fun a b hab => ?_) : A ⧸ H.comap f → G ⧸ H) ⟨?_, ?_⟩)
  · rw [QuotientGroup.leftRel_apply] at hab ⊢
    simpa using hab
  · intro a b
    induction a using QuotientGroup.induction_on with | H a => ?_
    induction b using QuotientGroup.induction_on with | H b => ?_
    intro hab
    have h1 : ((f a : G) : G ⧸ H) = (f b : G) := hab
    rw [QuotientGroup.eq] at h1 ⊢
    simpa using h1
  · intro g
    induction g using QuotientGroup.induction_on with | H g => ?_
    obtain ⟨a, ha⟩ := h g
    exact ⟨(a : A ⧸ H.comap f), (QuotientGroup.eq.mpr ha : ((f a : G) : G ⧸ H) = g)⟩

variable {L : Type} [Field L] [Valued L (WithZero (Multiplicative ℤ))]

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_int {y : L} : y ∈ intL L ↔ Valued.v y ≤ (1 : WithZero (Multiplicative ℤ)) := Iff.rfl

def A (r : L) : AddSubgroup L := (intL L).toAddSubgroup.comap (AddMonoidHom.mulLeft r)

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_A {r y : L} : y ∈ A r ↔ r * y ∈ intL L := Iff.rfl

/- English proof (translation)
Use extensionality with `y`. Simplify using `[mem_A, mul_assoc]`.
-/
theorem A_mul (r s : L) : A (r * s) = (A r).comap (AddMonoidHom.mulLeft s) := by
  ext y
  simp [mem_A, mul_assoc]

/- English proof (translation)
Rewrite using `[A_mul, A_mul, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]`. Introduce `y`. Conclude with `⟨s⁻¹ * y, by simp [hs]⟩`.
-/
theorem relIndex_A_mul (r r' s : L) (hs : s ≠ 0) : (A (r * s)).relIndex (A (r' * s)) = (A r).relIndex (A r') := by
  rw [A_mul, A_mul, AddSubgroup.relIndex_comap, AddSubgroup.map_comap_eq_self_of_surjective]
  intro y
  exact ⟨s⁻¹ * y, by simp [hs]⟩

variable {ϖ : L} {c : L →+* L} {q : ℕ}

/- English proof (translation)
Introduce `h0`. Use `h.2.2.2.1` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `WithZero.coe_ne_zero this.symm`.
-/
theorem pi_ne (h : IsUnramInv ϖ c q) : ϖ ≠ 0 := by
  intro h0
  have := h.2.2.2.1
  rw [h0, map_zero] at this
  exact WithZero.coe_ne_zero this.symm

/- English proof (translation)
Rewrite using `[mem_int, h.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe]`. Evaluate the decidable proposition.
-/
theorem pi_int (h : IsUnramInv ϖ c q) : ϖ ∈ intL L := by
  rw [mem_int, h.2.2.2.1, ← WithZero.coe_one, WithZero.coe_le_coe]
  decide

/- English proof (translation)
Rewrite using `[mem_A, mem_int, map_mul, map_inv₀, h.2.2.2.1]`. Distinguish the cases in `hy : Valued.v y = (0 : WithZero (Multiplicative ℤ))`. Simplify using `[hy]`. Take `⟨n, hn⟩` from `WithZero.ne_zero_iff_exists.mp hy`. Rewrite using `[← hn, ← WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_lt_coe]`.

Use `show (-(-1 : ℤ) + Multiplicative.toAdd n ≤ 0) ↔ Multiplicative.toAdd n < 0`. Use linear arithmetic over natural numbers and integers.
-/
theorem mem_A_inv (h : IsUnramInv ϖ c q) {y : L} :
    y ∈ A ϖ⁻¹ ↔ Valued.v y < (1 : WithZero (Multiplicative ℤ)) := by
  rw [mem_A, mem_int, map_mul, map_inv₀, h.2.2.2.1]
  by_cases hy : Valued.v y = (0 : WithZero (Multiplicative ℤ))
  · simp [hy]
  · obtain ⟨n, hn⟩ := WithZero.ne_zero_iff_exists.mp hy
    rw [← hn, ← WithZero.coe_inv, ← WithZero.coe_mul, ← WithZero.coe_one, WithZero.coe_le_coe, WithZero.coe_lt_coe]
    show (-(-1 : ℤ) + Multiplicative.toAdd n ≤ 0) ↔ Multiplicative.toAdd n < 0
    omega

/- English proof (translation)
Establish `e : A (1 : L) = (intL L).subtype.toAddMonoidHom.range`. Use extensionality with `y`. Simplify using `[mem_A]`. Rewrite using `[e, ← AddSubgroup.index_comap, ← h.2.2.2.2.2.2]`. Establish `e2 : (A ϖ⁻¹).comap (intL L).subtype.toAddMonoidHom = (IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).toAddSubgroup`.

Use extensionality with `y`. Rewrite using `[AddSubgroup.mem_comap, mem_A_inv h]`. Conclude with `(Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := y)).symm`. Rewrite using `[e2]`. Both sides reduce to the same expression.
-/
theorem relIndex_one (h : IsUnramInv ϖ c q) : (A ϖ⁻¹).relIndex (A (1 : L)) = q ^ 2 := by
  have e : A (1 : L) = (intL L).subtype.toAddMonoidHom.range := by
    ext y
    simp [mem_A]
  rw [e, ← AddSubgroup.index_comap, ← h.2.2.2.2.2.2]
  have e2 : (A ϖ⁻¹).comap (intL L).subtype.toAddMonoidHom =
      (IsLocalRing.maximalIdeal (Valued.v : Valuation L (WithZero (Multiplicative ℤ))).valuationSubring).toAddSubgroup := by
    ext y
    rw [AddSubgroup.mem_comap, mem_A_inv h]
    exact (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation L (WithZero (Multiplicative ℤ)))) (a := y)).symm
  rw [e2]
  rfl

/- English proof (translation)
Introduce `y hy`. Rewrite `hy`, the goal using `[mem_A]`. Use `(intL L).mul_mem (pi_int h) hy` as an intermediate fact. Rewrite `this` using `[mul_assoc, mul_inv_cancel_left₀ (pi_ne h)]`. Then use the resulting hypothesis.
-/
theorem A_le (h : IsUnramInv ϖ c q) (r : L) : A (ϖ⁻¹ * r) ≤ A r := by
  intro y hy
  rw [mem_A] at hy ⊢
  have := (intL L).mul_mem (pi_int h) hy
  rwa [mul_assoc, mul_inv_cancel_left₀ (pi_ne h)] at this

/- English proof (translation)
Establish `h1 : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A ϖ⁻¹) = q ^ 2`. Rewrite using `[← relIndex_one h, ← relIndex_A_mul ϖ⁻¹ 1 ϖ⁻¹ (inv_ne_zero (pi_ne h)), one_mul]`. Establish `h2 : A ϖ⁻¹ ≤ A (1 : L)` using `by simpa using A_le h 1`. Rewrite using `[← AddSubgroup.relIndex_mul_relIndex _ _ _ (A_le h _) h2, h1, relIndex_one h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relIndex_two (h : IsUnramInv ϖ c q) : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A (1 : L)) = q ^ 4 := by
  have h1 : (A (ϖ⁻¹ * ϖ⁻¹)).relIndex (A ϖ⁻¹) = q ^ 2 := by
    rw [← relIndex_one h, ← relIndex_A_mul ϖ⁻¹ 1 ϖ⁻¹ (inv_ne_zero (pi_ne h)), one_mul]
  have h2 : A ϖ⁻¹ ≤ A (1 : L) := by simpa using A_le h 1
  rw [← AddSubgroup.relIndex_mul_relIndex _ _ _ (A_le h _) h2, h1, relIndex_one h]
  ring

def MA (m : ℕ) (r : L) : AddSubgroup (Matrix (Fin m) (Fin m) L) :=
  AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => A r

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩`.
-/
theorem mem_MA {m : ℕ} {r : L} {X : Matrix (Fin m) (Fin m) L} : X ∈ MA m r ↔ ∀ i j, r * X i j ∈ intL L :=
  ⟨fun h i j => h i trivial j trivial, fun h i _ j _ => h i j⟩

/- English proof (translation)
Set `g : (Fin m → Fin m → A (1 : L)) →+ Matrix (Fin m) (Fin m) L` to `{ toFun := fun Y => Matrix.of fun i j => (Y i j : L) map_zero' := rfl map_add' := fun _ _ => rfl }`. Establish `e : MA m (1 : L) = g.range`. Use extensionality with `X`. Prove the components needed by the constructor for the conclusion. Introduce `hX`.

Conclude with `⟨fun i j => ⟨X i j, mem_MA.mp hX i j⟩, rfl⟩`. Introduce and unpack `⟨Y, rfl⟩`. Conclude with `mem_MA.mpr fun i j => (Y i j).2`. Establish `e2 : (MA m r).comap g = AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ => (A r).addSubgroupOf (A (1 : L))`. Use extensionality with `Y`.

Conclude with `⟨fun h i _ j _ => h i trivial j trivial, fun h i _ j _ => h i trivial j trivial⟩`. Rewrite using `[e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_pi]`. Simplify using `only [AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]`. Both sides reduce to the same expression.
-/
theorem relIndex_MA (m : ℕ) (r : L) : (MA m r).relIndex (MA m (1 : L)) = ((A r).relIndex (A (1 : L))) ^ (m * m) := by
  let g : (Fin m → Fin m → A (1 : L)) →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun Y => Matrix.of fun i j => (Y i j : L)
      map_zero' := rfl
      map_add' := fun _ _ => rfl }
  have e : MA m (1 : L) = g.range := by
    ext X
    constructor
    · intro hX
      exact ⟨fun i j => ⟨X i j, mem_MA.mp hX i j⟩, rfl⟩
    · rintro ⟨Y, rfl⟩
      exact mem_MA.mpr fun i j => (Y i j).2
  have e2 : (MA m r).comap g = AddSubgroup.pi Set.univ fun _ => AddSubgroup.pi Set.univ fun _ =>
      (A r).addSubgroupOf (A (1 : L)) := by
    ext Y
    exact ⟨fun h i _ j _ => h i trivial j trivial, fun h i _ j _ => h i trivial j trivial⟩
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_pi]
  simp only [AddSubgroup.index_pi, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← pow_mul]
  rfl

def NA (c : L →+* L) (m : ℕ) : AddSubgroup (Matrix (Fin m) (Fin m) L) where
  carrier := {X | (∀ i j, X i j ∈ intL L) ∧ ∀ i j, c (X i j) = -X j i}
  zero_mem' := ⟨fun _ _ => (intL L).zero_mem, fun _ _ => by simp⟩
  add_mem' := fun {X Y} hX hY => ⟨fun i j => (intL L).add_mem (hX.1 i j) (hY.1 i j), fun i j => by
    simp only [Matrix.add_apply, map_add, hX.2, hY.2, neg_add]⟩
  neg_mem' := fun {X} hX => ⟨fun i j => (intL L).neg_mem (hX.1 i j), fun i j => by
    simp only [Matrix.neg_apply, map_neg, hX.2]⟩

/- English proof (translation)
Rewrite using `[mem_int, h.2.1]`. Conclude with `hy`.
-/
theorem c_int (h : IsUnramInv ϖ c q) {y : L} (hy : y ∈ intL L) : c y ∈ intL L := by
  rw [mem_int, h.2.1]; exact hy

/- English proof (translation)
Take `⟨x, hx, hd⟩` from `h.2.2.2.2.1`. Establish `hd0 : c x - x ≠ 0`. Introduce `h0`. Rewrite `hd` using `[h0, map_zero]`. Conclude with `zero_ne_one hd`.

Establish `hd1 : x - c x ≠ 0` using `fun h0 => hd0 (by linear_combination -h0)`. Establish `hdi : (c x - x)⁻¹ ∈ intL L` using `by rw [mem_int, map_inv₀, hd, inv_one]`. Set `f : NA c m × NA c m →+ Matrix (Fin m) (Fin m) L` to `{ toFun := fun p => (p.1 : Matrix (Fin m) (Fin m) L) + x • (p.2 : Matrix (Fin m) (Fin m) L) map_zero' := by simp map_add' := fun p p' => by`. Simplify using `only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]`. Use `abel }`.

Establish `fa : ∀ p i j, f p i j = (p.1 : Matrix (Fin m) (Fin m) L) i j + x * (p.2 : Matrix (Fin m) (Fin m) L) i j` using `fun _ _ _ => rfl`. Establish `e : MA m (1 : L) = f.range`. Use extensionality with `X`. Rewrite using `[mem_MA]`. Simplify using `only [one_mul]`.

Prove the components needed by the constructor for the conclusion. Introduce `hX`. Establish `hb : ∀ i j, -((c x - x)⁻¹ * (X i j + c (X j i))) ∈ intL L` using `fun i j => (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hX i j) (c_int h (hX j i))))`. Use `⟨(⟨Matrix.of fun i j => X i j - x * -((c x - x)⁻¹ * (X i j + c (X j i))), fun i j => (intL L).sub_mem (hX i j) ((intL L).mul_mem hx (hb i j)), fun i j => ?_⟩, ⟨Matrix.of fun i j => -((c x - x)⁻¹ * (X i j + c (X j i))), hb, fun i j => ?_⟩), ?_⟩` and prove the remaining obligations. Simplify using `only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]`.

Rewrite using `[← neg_sub (c x) x, inv_neg]`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]`. Rewrite using `[← neg_sub (c x) x, inv_neg]`.

Expand and normalize the polynomial expressions, which then agree. Use extensionality with `i j`. Rewrite using `[fa]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨p, rfl⟩ i j`.

Rewrite using `[fa]`. Conclude with `(intL L).add_mem (p.1.2.1 i j) ((intL L).mul_mem hx (p.2.2.1 i j))`. Establish `e2 : (MA m r).comap f = ((MA m r).addSubgroupOf (NA c m)).prod ((MA m r).addSubgroupOf (NA c m))`. Use extensionality with `p`. Simplify using `only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, mem_MA, fa]`.

Prove the components needed by the constructor for the conclusion. Introduce `hp`. Establish `hb : ∀ i j, r * (p.2 : Matrix (Fin m) (Fin m) L) i j ∈ intL L` using `fun i j => by`. Establish `h1` using `(intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hp i j) (c_int h (hp j i))))`. Simplify using `only [map_mul, map_add, hr, p.1.2.2, p.2.2.2] at h1`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Use `⟨fun i j => ?_, hb⟩` and prove the remaining obligations. Establish `h1` using `(intL L).sub_mem (hp i j) ((intL L).mul_mem hx (hb i j))`.

Use `h1 using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce `hp i j`. Establish `h1` using `(intL L).add_mem (hp.1 i j) ((intL L).mul_mem hx (hp.2 i j))`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_prod]`. Both sides reduce to the same expression.
-/
theorem relIndex_NA_sq (h : IsUnramInv ϖ c q) (m : ℕ) (r : L) (hr : c r = r) :
    (MA m r).relIndex (NA c m) * (MA m r).relIndex (NA c m) = (MA m r).relIndex (MA m (1 : L)) := by
  obtain ⟨x, hx, hd⟩ := h.2.2.2.2.1
  have hd0 : c x - x ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hd
    exact zero_ne_one hd
  have hd1 : x - c x ≠ 0 := fun h0 => hd0 (by linear_combination -h0)
  have hdi : (c x - x)⁻¹ ∈ intL L := by rw [mem_int, map_inv₀, hd, inv_one]
  let f : NA c m × NA c m →+ Matrix (Fin m) (Fin m) L :=
    { toFun := fun p => (p.1 : Matrix (Fin m) (Fin m) L) + x • (p.2 : Matrix (Fin m) (Fin m) L)
      map_zero' := by simp
      map_add' := fun p p' => by
        simp only [Prod.fst_add, Prod.snd_add, AddSubgroup.coe_add, smul_add]
        abel }
  have fa : ∀ p i j, f p i j = (p.1 : Matrix (Fin m) (Fin m) L) i j + x * (p.2 : Matrix (Fin m) (Fin m) L) i j :=
    fun _ _ _ => rfl
  have e : MA m (1 : L) = f.range := by
    ext X
    rw [mem_MA]
    simp only [one_mul]
    constructor
    · intro hX
      have hb : ∀ i j, -((c x - x)⁻¹ * (X i j + c (X j i))) ∈ intL L := fun i j =>
        (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hX i j) (c_int h (hX j i))))
      refine ⟨(⟨Matrix.of fun i j => X i j - x * -((c x - x)⁻¹ * (X i j + c (X j i))), fun i j =>
          (intL L).sub_mem (hX i j) ((intL L).mul_mem hx (hb i j)), fun i j => ?_⟩,
        ⟨Matrix.of fun i j => -((c x - x)⁻¹ * (X i j + c (X j i))), hb, fun i j => ?_⟩), ?_⟩
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        field_simp
        ring
      · simp only [Matrix.of_apply, map_sub, map_mul, map_neg, map_inv₀, map_add, h.1]
        rw [← neg_sub (c x) x, inv_neg]
        ring
      · ext i j
        rw [fa]
        simp
    · rintro ⟨p, rfl⟩ i j
      rw [fa]
      exact (intL L).add_mem (p.1.2.1 i j) ((intL L).mul_mem hx (p.2.2.1 i j))
  have e2 : (MA m r).comap f = ((MA m r).addSubgroupOf (NA c m)).prod ((MA m r).addSubgroupOf (NA c m)) := by
    ext p
    simp only [AddSubgroup.mem_comap, AddSubgroup.mem_prod, AddSubgroup.mem_addSubgroupOf, mem_MA, fa]
    constructor
    · intro hp
      have hb : ∀ i j, r * (p.2 : Matrix (Fin m) (Fin m) L) i j ∈ intL L := fun i j => by
        have h1 := (intL L).neg_mem ((intL L).mul_mem hdi ((intL L).add_mem (hp i j) (c_int h (hp j i))))
        simp only [map_mul, map_add, hr, p.1.2.2, p.2.2.2] at h1
        convert h1 using 1
        field_simp
        ring
      refine ⟨fun i j => ?_, hb⟩
      have h1 := (intL L).sub_mem (hp i j) ((intL L).mul_mem hx (hb i j))
      convert h1 using 1
      ring
    · intro hp i j
      have h1 := (intL L).add_mem (hp.1 i j) ((intL L).mul_mem hx (hp.2 i j))
      convert h1 using 1
      ring
  rw [e, ← AddSubgroup.index_comap, e2, AddSubgroup.index_prod]
  rfl

/- English proof (translation)
Establish `h1` using `relIndex_NA_sq h m (ϖ⁻¹ * ϖ⁻¹) (by rw [map_mul, map_inv₀, h.2.2.1])`. Rewrite `h1` using `[relIndex_MA, relIndex_two h]`. Apply `Nat.mul_self_inj.mp` to reduce the goal to its premises. Rewrite using `[h1]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem relIndex_NA (h : IsUnramInv ϖ c q) (m : ℕ) :
    (MA m (ϖ⁻¹ * ϖ⁻¹)).relIndex (NA c m) = q ^ (2 * m * m) := by
  have h1 := relIndex_NA_sq h m (ϖ⁻¹ * ϖ⁻¹) (by rw [map_mul, map_inv₀, h.2.2.1])
  rw [relIndex_MA, relIndex_two h] at h1
  apply Nat.mul_self_inj.mp
  rw [h1]
  ring

end PositivityTheory.Sph.M2.ZC

end
