import Formalism.LocalToGlobal.UnitaryNorms.RealCyclotomicTwoPower

noncomputable section

open IntermediateField NumberField

namespace Formalism.L2.Host

open Formalism.FrobeniusOrbits Formalism.TwoAdicCyclotomicDecomposition

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `show adjoin ℚ (sqrts m) ≤ _`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `z hz`. Establish `hz' : z ^ 2 = w ^ 2`.

Rewrite using `[hw]`. Conclude with `hz`. Break down `sq_eq_sq_iff_eq_or_eq_neg.mp hz' with rfl | rfl` into its components or cases. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ z`. Conclude with `neg_mem (IntermediateField.mem_adjoin_simple_self ℚ w)`.

Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `IntermediateField.subset_adjoin ℚ (sqrts m) hw`.
-/
theorem sqQ_eq {m : ℤ} {w : Qb} (hw : w ^ 2 = (m : Qb)) : sqQ m = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (sqrts m) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    have hz' : z ^ 2 = w ^ 2 := by
      rw [hw]
      exact hz
    rcases sq_eq_sq_iff_eq_or_eq_neg.mp hz' with rfl | rfl
    · exact IntermediateField.mem_adjoin_simple_self ℚ z
    · exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ w)
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (sqrts m) hw

/- English proof (translation)
Establish `key : ∀ n : ℕ, w ^ n + w⁻¹ ^ n ∈ ℚ⟮w + w⁻¹⟯ ∧ w ^ (n + 1) + w⁻¹ ^ (n + 1) ∈ ℚ⟮w + w⁻¹⟯`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Use `⟨?_, ?_⟩` and prove the remaining obligations.

Simplify using `only [pow_zero]`. Conclude with `add_mem (one_mem _) (one_mem _)`. Simplify using `only [zero_add, pow_one]`. Conclude with `IntermediateField.mem_adjoin_simple_self ℚ _`. Consider the case `succ n ih`.

Use `⟨ih.2, ?_⟩` and prove the remaining obligations. Establish `h1 : w * w⁻¹ = 1` using `mul_inv_cancel₀ hw`. Establish `e : w ^ (n + 1 + 1) + w⁻¹ ^ (n + 1 + 1) = (w + w⁻¹) * (w ^ (n + 1) + w⁻¹ ^ (n + 1)) - (w ^ n + w⁻¹ ^ n)`. Take the linear combination `(-(w ^ n + w⁻¹ ^ n)) * h1`. Rewrite using `[e]`.

Conclude with `sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih.2) ih.1`. Conclude with `(key k).1`.
-/
theorem pow_add_inv_pow_mem {w : Qb} (hw : w ≠ 0) (k : ℕ) : w ^ k + w⁻¹ ^ k ∈ ℚ⟮w + w⁻¹⟯ := by
  have key : ∀ n : ℕ, w ^ n + w⁻¹ ^ n ∈ ℚ⟮w + w⁻¹⟯ ∧ w ^ (n + 1) + w⁻¹ ^ (n + 1) ∈ ℚ⟮w + w⁻¹⟯ := by
    intro n
    induction n with
    | zero =>
      refine ⟨?_, ?_⟩
      · simp only [pow_zero]
        exact add_mem (one_mem _) (one_mem _)
      · simp only [zero_add, pow_one]
        exact IntermediateField.mem_adjoin_simple_self ℚ _
    | succ n ih =>
      refine ⟨ih.2, ?_⟩
      have h1 : w * w⁻¹ = 1 := mul_inv_cancel₀ hw
      have e : w ^ (n + 1 + 1) + w⁻¹ ^ (n + 1 + 1) =
          (w + w⁻¹) * (w ^ (n + 1) + w⁻¹ ^ (n + 1)) - (w ^ n + w⁻¹ ^ n) := by
        linear_combination (-(w ^ n + w⁻¹ ^ n)) * h1
      rw [e]
      exact sub_mem (mul_mem (IntermediateField.mem_adjoin_simple_self ℚ _) ih.2) ih.1
  exact (key k).1

/- English proof (translation)
Establish `hw0 : w ≠ 0` using `hw.ne_zero (NeZero.ne N)`. Apply `le_antisymm` to reduce the goal to its premises. Use `show adjoin ℚ ((fun z => z + z⁻¹) '' mus N) ≤ _`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Take `⟨i, -, rfl⟩` from `hw.eq_pow_of_pow_eq_one hz`. Use `show w ^ i + (w ^ i)⁻¹ ∈ ℚ⟮w + w⁻¹⟯`. Rewrite using `[← inv_pow]`. Conclude with `pow_add_inv_pow_mem hw0 i`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`.

Conclude with `IntermediateField.subset_adjoin ℚ ((fun z : Qb => z + z⁻¹) '' mus N) ⟨w, hw.pow_eq_one, rfl⟩`.
-/
theorem cycQplus_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) :
    cycQplus N = ℚ⟮w + w⁻¹⟯ := by
  have hw0 : w ≠ 0 := hw.ne_zero (NeZero.ne N)
  apply le_antisymm
  · show adjoin ℚ ((fun z => z + z⁻¹) '' mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    rintro _ ⟨z, hz, rfl⟩
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    show w ^ i + (w ^ i)⁻¹ ∈ ℚ⟮w + w⁻¹⟯
    rw [← inv_pow]
    exact pow_add_inv_pow_mem hw0 i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ ((fun z : Qb => z + z⁻¹) '' mus N) ⟨w, hw.pow_eq_one, rfl⟩

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `show adjoin ℚ (mus N) ≤ _`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `z hz`. Take `⟨i, -, rfl⟩` from `hw.eq_pow_of_pow_eq_one hz`.

Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ w) i`. Rewrite using `[IntermediateField.adjoin_simple_le_iff]`. Conclude with `IntermediateField.subset_adjoin ℚ (mus N) hw.pow_eq_one`.
-/
theorem cycQ_eq {N : ℕ} [NeZero N] {w : Qb} (hw : IsPrimitiveRoot w N) : cycQ N = ℚ⟮w⟯ := by
  apply le_antisymm
  · show adjoin ℚ (mus N) ≤ _
    rw [IntermediateField.adjoin_le_iff]
    intro z hz
    obtain ⟨i, -, rfl⟩ := hw.eq_pow_of_pow_eq_one hz
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ w) i
  · rw [IntermediateField.adjoin_simple_le_iff]
    exact IntermediateField.subset_adjoin ℚ (mus N) hw.pow_eq_one

/- English proof (translation)
Rewrite using `[Set.insert_eq]`. Conclude with `IntermediateField.gc.l_sup`.
-/
theorem adjoin_pair_eq_sup (x y : Qb) : adjoin ℚ {x, y} = ℚ⟮x⟯ ⊔ ℚ⟮y⟯ := by
  rw [Set.insert_eq]
  exact IntermediateField.gc.l_sup

/- English proof (translation)
Use `show sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2)) = _`. Rewrite using `[sqQ, sqQ, cycQplus, ← IntermediateField.gc.l_sup, ← IntermediateField.gc.l_sup]`. Both sides reduce to the same expression.
-/
theorem EQ_eq_adjoin (e q d : ℕ) : EQ e q d =
    adjoin ℚ ((sqrts (-(q : ℤ)) ∪ sqrts (-(d : ℤ))) ∪ (fun z => z + z⁻¹) '' mus (2 ^ (e + 2))) := by
  show sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2)) = _
  rw [sqQ, sqQ, cycQplus, ← IntermediateField.gc.l_sup, ← IntermediateField.gc.l_sup]
  rfl

/- English proof (translation)
Establish `hdvd : N ∣ (-u).val + u.val`. Rewrite using `[← CharP.cast_eq_zero_iff (ZMod N) N]`. Simplify using the standard rewrite rules. Take `⟨c, hc⟩` from `hdvd`. Establish `h1 : z ^ (-u).val * z ^ u.val = 1` using `by rw [← pow_add, hc, pow_mul, hz, one_pow]`.

Rewrite using `[inv_pow]`. Conclude with `eq_inv_of_mul_eq_one_left h1`.
-/
theorem pow_neg_val {N : ℕ} [NeZero N] {z : Qb} (hz : z ^ N = 1) (u : ZMod N) :
    z ^ (-u).val = z⁻¹ ^ u.val := by
  have hdvd : N ∣ (-u).val + u.val := by
    rw [← CharP.cast_eq_zero_iff (ZMod N) N]
    simp
  obtain ⟨c, hc⟩ := hdvd
  have h1 : z ^ (-u).val * z ^ u.val = 1 := by rw [← pow_add, hc, pow_mul, hz, one_pow]
  rw [inv_pow]
  exact eq_inv_of_mul_eq_one_left h1

/- English proof (translation)
Take `⟨h1, h2, u, hu, hs⟩` from `h`. Take `⟨h1', h2', u', hu', hs'⟩` from `h'`. Use `IntermediateField.algHom_ext_of_eq_adjoin ℚ (EQ_eq_adjoin e q d) ?_` and prove the remaining obligations. Introduce `x hx`. Break down `hx with (hx | hx) | ⟨z, hz, hzx⟩` into its components or cases.

Conclude with `(h1 _ hx).trans (h1' _ hx).symm`. Conclude with `(h2 _ hx).trans (h2' _ hx).symm`. Establish `hz1 : z ^ (2 ^ (e + 2)) = 1` using `hz`. Establish `hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1` using `by rw [inv_pow, hz1, inv_one]`. Establish `hval : z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val = z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val`.

Establish `hq : (hcl e u : HGrp e) = hcl e u'` using `hu.trans hu'.symm`. Rewrite `hq` using `[hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff]`. Take `⟨k, hk⟩` from `hq`. Break down `Int.even_or_odd k with he | ho` into its components or cases. Rewrite `hk` using `[he.neg_one_zpow, eq_comm, inv_mul_eq_one]`.

Rewrite using `[hk]`. Rewrite `hk` using `[ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one]`. Rewrite using `[hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]`. Conclude with `((hs _ z hz hzx.symm).trans hval).trans (hs' _ z hz hzx.symm).symm`.
-/
theorem ActsAs.unique {e q d : ℕ} {s s' : EQ e q d →ₐ[ℚ] Qb} {g : GG e}
    (h : ActsAs e q d s g) (h' : ActsAs e q d s' g) : s = s' := by
  obtain ⟨h1, h2, u, hu, hs⟩ := h
  obtain ⟨h1', h2', u', hu', hs'⟩ := h'
  refine IntermediateField.algHom_ext_of_eq_adjoin ℚ (EQ_eq_adjoin e q d) ?_
  intro x hx
  rcases hx with (hx | hx) | ⟨z, hz, hzx⟩
  · exact (h1 _ hx).trans (h1' _ hx).symm
  · exact (h2 _ hx).trans (h2' _ hx).symm
  · have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
    have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
    have hval : z ^ (u : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u : ZMod (2 ^ (e + 2))).val =
        z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
      have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
      rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
      obtain ⟨k, hk⟩ := hq
      rcases Int.even_or_odd k with he | ho
      · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
        rw [hk]
      · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
        rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]
    exact ((hs _ z hz hzx.symm).trans hval).trans (hs' _ z hz hzx.symm).symm

/- English proof (translation)
Take `⟨-, -, u, hu, hs⟩` from `h`. Rewrite using `[hs x z hz hx]`. Establish `hq : (hcl e u : HGrp e) = hcl e u'` using `hu.trans hu'.symm`. Rewrite `hq` using `[hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff]`. Take `⟨k, hk⟩` from `hq`.

Establish `hz1 : z ^ (2 ^ (e + 2)) = 1` using `hz`. Establish `hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1` using `by rw [inv_pow, hz1, inv_one]`. Break down `Int.even_or_odd k with he | ho` into its components or cases. Rewrite `hk` using `[he.neg_one_zpow, eq_comm, inv_mul_eq_one]`. Rewrite using `[hk]`.

Rewrite `hk` using `[ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one]`. Rewrite using `[hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]`.
-/
theorem ActsAs.snd {e q d : ℕ} {s : EQ e q d →ₐ[ℚ] Qb} {g : GG e} (h : ActsAs e q d s g)
    (u' : (ZMod (2 ^ (e + 2)))ˣ) (hu' : hcl e u' = g.2) (x : EQ e q d) (z : Qb) (hz : z ∈ mus (2 ^ (e + 2)))
    (hx : (x : Qb) = z + z⁻¹) :
    s x = z ^ (u' : ZMod (2 ^ (e + 2))).val + z⁻¹ ^ (u' : ZMod (2 ^ (e + 2))).val := by
  obtain ⟨-, -, u, hu, hs⟩ := h
  rw [hs x z hz hx]
  have hq : (hcl e u : HGrp e) = hcl e u' := hu.trans hu'.symm
  rw [hcl, hcl, QuotientGroup.eq, Subgroup.mem_zpowers_iff] at hq
  obtain ⟨k, hk⟩ := hq
  have hz1 : z ^ (2 ^ (e + 2)) = 1 := hz
  have hz' : z⁻¹ ^ (2 ^ (e + 2)) = 1 := by rw [inv_pow, hz1, inv_one]
  rcases Int.even_or_odd k with he | ho
  · rw [he.neg_one_zpow, eq_comm, inv_mul_eq_one] at hk
    rw [hk]
  · rw [ho.neg_one_zpow, eq_comm, inv_mul_eq_iff_eq_mul, mul_neg_one] at hk
    rw [hk, Units.val_neg, pow_neg_val hz1, pow_neg_val hz', inv_inv, add_comm]

section Layer

variable {e q d : ℕ} {L : Type} [Field L] [NumberField L] {ζ a b : L}

/- English proof (translation)
Rewrite using `[← map_pow, h.2.1]`. Simplify using the standard rewrite rules.
-/
theorem map_a_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ a ^ 2 = ((-(q : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.1]
  simp

/- English proof (translation)
Rewrite using `[← map_pow, h.2.2.1]`. Simplify using the standard rewrite rules.
-/
theorem map_b_sq (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    φ b ^ 2 = ((-(d : ℤ) : ℤ) : Qb) := by
  rw [← map_pow, h.2.2.1]
  simp

/- English proof (translation)
The claim follows from `h.1.map_of_injective (f := φ) (RingHom.injective φ.toRingHom)`.
-/
theorem map_zeta (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    IsPrimitiveRoot (φ ζ) (2 ^ (e + 2)) := h.1.map_of_injective (f := φ) (RingHom.injective φ.toRingHom)

/- English proof (translation)
The claim follows from `IntermediateField.gc.l_sup`.
-/
private theorem adjoin_union_eq_sup {E : Type*} [Field E] [Algebra ℚ E] (S T : Set E) :
    adjoin ℚ (S ∪ T) = adjoin ℚ S ⊔ adjoin ℚ T :=
  IntermediateField.gc.l_sup

/- English proof (translation)
Rewrite using `[show hostE ζ a b = adjoin ℚ ({a, b} ∪ {ζ + ζ⁻¹}) from (adjoin_union_eq_sup _ _).symm, IntermediateField.adjoin_map, Set.image_union, Set.image_insert_eq, Set.image_singleton, Set.image_singleton, map_add, map_inv₀, adjoin_union_eq_sup, adjoin_pair_eq_sup]`. Use `show _ = sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2))`. Rewrite using `[sqQ_eq (map_a_sq h φ), sqQ_eq (map_b_sq h φ), cycQplus_eq (map_zeta h φ)]`.
-/
theorem map_hostE (h : IsLayer (e + 2) q d ζ a b) (φ : L →ₐ[ℚ] Qb) :
    (hostE ζ a b).map φ = EQ e q d := by
  rw [show hostE ζ a b = adjoin ℚ ({a, b} ∪ {ζ + ζ⁻¹}) from (adjoin_union_eq_sup _ _).symm,
    IntermediateField.adjoin_map, Set.image_union, Set.image_insert_eq, Set.image_singleton, Set.image_singleton,
    map_add, map_inv₀, adjoin_union_eq_sup, adjoin_pair_eq_sup]
  show _ = sqQ (-(q : ℤ)) ⊔ sqQ (-(d : ℤ)) ⊔ cycQplus (2 ^ (e + 2))
  rw [sqQ_eq (map_a_sq h φ), sqQ_eq (map_b_sq h φ), cycQplus_eq (map_zeta h φ)]

/- English proof (translation)
Use `letI : Algebra (hostE ζ a b) Qb := f.toRingHom.toAlgebra`. Use `haveI : FiniteDimensional (hostE ζ a b) L := FiniteDimensional.right ℚ (hostE ζ a b) L`. Use `haveI : Algebra.IsAlgebraic (hostE ζ a b) L := Algebra.IsAlgebraic.of_finite (hostE ζ a b) L`. Set `ψ : L →ₐ[hostE ζ a b] Qb` to `IsAlgClosed.lift`. Conclude with `⟨ψ.toRingHom.toRatAlgHom, fun x => ψ.commutes x⟩`.
-/
theorem exists_layer_emb (f : hostE ζ a b →ₐ[ℚ] Qb) :
    ∃ φ : L →ₐ[ℚ] Qb, ∀ x : hostE ζ a b, φ (x : L) = f x := by
  letI : Algebra (hostE ζ a b) Qb := f.toRingHom.toAlgebra
  haveI : FiniteDimensional (hostE ζ a b) L := FiniteDimensional.right ℚ (hostE ζ a b) L
  haveI : Algebra.IsAlgebraic (hostE ζ a b) L := Algebra.IsAlgebraic.of_finite (hostE ζ a b) L
  let ψ : L →ₐ[hostE ζ a b] Qb := IsAlgClosed.lift
  exact ⟨ψ.toRingHom.toRatAlgHom, fun x => ψ.commutes x⟩

/- English proof (translation)
Take `⟨φ, hφ⟩` from `exists_layer_emb f`. Rewrite using `[← map_hostE h φ]`. Use extensionality with `y`. Simplify using `only [AlgHom.mem_fieldRange, IntermediateField.mem_map]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨x, rfl⟩`. Conclude with `⟨x, x.2, hφ x⟩`. Introduce and unpack `⟨x, hx, rfl⟩`. Conclude with `⟨⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩`.
-/
theorem range_hostE (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) :
    f.fieldRange = EQ e q d := by
  obtain ⟨φ, hφ⟩ := exists_layer_emb f
  rw [← map_hostE h φ]
  ext y
  simp only [AlgHom.mem_fieldRange, IntermediateField.mem_map]
  constructor
  · rintro ⟨x, rfl⟩
    exact ⟨x, x.2, hφ x⟩
  · rintro ⟨x, hx, rfl⟩
    exact ⟨⟨x, hx⟩, (hφ ⟨x, hx⟩).symm⟩

/- English proof (translation)
Rewrite using `[← range_hostE h f]`. Conclude with `AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩`.
-/
theorem mem_EQ (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    f x ∈ EQ e q d := by
  rw [← range_hostE h f]
  exact AlgHom.mem_fieldRange.mpr ⟨x, rfl⟩

def jOf (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) : hostE ζ a b ≃ₐ[ℚ] EQ e q d :=
  AlgEquiv.ofBijective (f.codRestrict (EQ e q d).toSubalgebra (mem_EQ h f))
    ⟨fun x y hxy => f.toRingHom.injective (congrArg Subtype.val hxy), fun y => by
      have hy : (y : Qb) ∈ f.fieldRange := by rw [range_hostE h f]; exact y.2
      obtain ⟨x, hx⟩ := hy
      exact ⟨x, Subtype.ext hx⟩⟩

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] theorem jOf_coe (h : IsLayer (e + 2) q d ζ a b) (f : hostE ζ a b →ₐ[ℚ] Qb) (x : hostE ζ a b) :
    ((jOf h f x : EQ e q d) : Qb) = f x := rfl

end Layer

end Formalism.L2.Host
