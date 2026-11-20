import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.ClassMassEqSumOfBijective

noncomputable section

open Formalism.UG

namespace GlobalTheory.Mass.Model

section Abstract

variable {G : Type} [Group G] {Γ K K' : Subgroup G}

/- English proof (translation)
Set `H : Subgroup K` to `(Γ.comap (MulAut.conj g).toMonoidHom).subgroupOf K`. Establish `hH : ∀ x : K, x ∈ H ↔ g * x * g⁻¹ ∈ Γ` using `fun x => Iff.rfl`. Set `b : K ⧸ K'.subgroupOf K` to `QuotientGroup.mk k`. Establish `e0` using `Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H b)`. Rewrite `e0` using `[Nat.card_prod]`.

Establish `e1 : Nat.card H = Nat.card (stabAt Γ K g)` using `Nat.card_congr { toFun := fun x => ⟨⟨_, (hH x).1 x.2⟩, by`. Express the relevant statement in the definitionally equal form `g⁻¹ * (g * (x.1 : G) * g⁻¹) * g ∈ K`. Simplify `x.1.2⟩` using `[mul_assoc]`. Use `invFun := fun y => ⟨⟨_, y.2⟩, (hH _).2 (by simpa [mul_assoc] using y.1.2)⟩`. Use `left_inv := fun x => by ext; simp [mul_assoc]`.

Use `right_inv := fun y => by ext; simp [mul_assoc] }`. Establish `hs : ∀ x : H, x ∈ MulAction.stabilizer H b ↔ (k : G)⁻¹ * x.1 * k ∈ K'` using `fun x => by`. Rewrite using `[MulAction.mem_stabilizer_iff, eq_comm]`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk k : K ⧸ K'.subgroupOf K) = QuotientGroup.mk (x.1 * k) ↔ _`. Rewrite using `[QuotientGroup.eq, Subgroup.mem_subgroupOf]`.

Simplify using `[mul_assoc]`. Establish `e2 : Nat.card (MulAction.stabilizer H b) = Nat.card (stabAt Γ K' (g * k))` using `Nat.card_congr { toFun := fun x => ⟨⟨_, (hH x.1).1 x.1.2⟩, by`. Express the relevant statement in the definitionally equal form `(g * k)⁻¹ * (g * (x.1.1 : G) * g⁻¹) * (g * k) ∈ K'`. Simplify `(hs _).1 x.2⟩` using `[mul_assoc]`. Use `invFun := fun y => ⟨⟨⟨g⁻¹ * y.1 * g, by`.

Establish `h1 : (g * k)⁻¹ * (y.1 : G) * (g * k) ∈ K` using `hle y.2`. Simplify `K.mul_mem (K.mul_mem k.2 h1) (K.inv_mem k.2)⟩,` using `[mul_assoc]`. Use the proof step `(hH _).2 (by simpa [mul_assoc] using y.1.2)⟩, (hs _).2 (by`. Establish `h1 : (g * k)⁻¹ * (y.1 : G) * (g * k) ∈ K'` using `y.2`. Simplify `h1)⟩` using `[mul_assoc]`.

Use `left_inv := fun x => by ext; simp [mul_assoc]`. Use `right_inv := fun y => by ext; simp [mul_assoc] }`. Establish `e3 : ∀ t : K ⧸ K'.subgroupOf K, (DoubleCoset.mk Γ K' (g * (t.out : K)) : ClassSet Γ K') = DoubleCoset.mk Γ K' (g * k) ↔ t ∈ MulAction.orbit H b` using `fun t => by`. Rewrite using `[eq_comm, DoubleCoset.eq]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨γ, hγ, κ, hκ, e⟩`. Establish `e' : g⁻¹ * γ * g = (t.out : K) * κ⁻¹ * (k : G)⁻¹`. Rewrite using `[← inv_mul_cancel_left g (t.out : K), e]`. Use `group`. Establish `hm : g⁻¹ * γ * g ∈ K` using `e' ▸ K.mul_mem (K.mul_mem t.out.2 (K.inv_mem (hle hκ))) (K.inv_mem k.2)`.

Use `⟨⟨⟨_, hm⟩, (hH _).2 (by simpa [mul_assoc] using hγ)⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (⟨_, hm⟩ * k) : K ⧸ K'.subgroupOf K) = t`. Rewrite using `[← QuotientGroup.out_eq' t, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, e']`. Simplify `hκ` using `[mul_assoc]`.

Introduce and unpack `⟨x, hx⟩`. Express the relevant statement in the definitionally equal form `(QuotientGroup.mk (x.1 * k) : K ⧸ K'.subgroupOf K) = t at hx`. Rewrite `hx` using `[← QuotientGroup.out_eq' t, QuotientGroup.eq, Subgroup.mem_subgroupOf]`. Use `⟨_, (hH _).1 x.2, _, hx, ?_⟩` and prove the remaining obligations. Simplify using `[mul_assoc]`.

Rewrite using `[← e1, ← e0, e2]`. Use `congr 1`. Conclude with `Nat.card_congr (Equiv.subtypeEquivRight e3)`.
-/
theorem card_fibre_mul (hle : K' ≤ K) (g : G) (k : K) :
    Nat.card {t : K ⧸ K'.subgroupOf K //
        (DoubleCoset.mk Γ K' (g * (t.out : K)) : ClassSet Γ K') = DoubleCoset.mk Γ K' (g * k)} *
      Nat.card (stabAt Γ K' (g * k)) = Nat.card (stabAt Γ K g) := by
  let H : Subgroup K := (Γ.comap (MulAut.conj g).toMonoidHom).subgroupOf K
  have hH : ∀ x : K, x ∈ H ↔ g * x * g⁻¹ ∈ Γ := fun x => Iff.rfl
  let b : K ⧸ K'.subgroupOf K := QuotientGroup.mk k
  have e0 := Nat.card_congr (MulAction.orbitProdStabilizerEquivGroup H b)
  rw [Nat.card_prod] at e0
  have e1 : Nat.card H = Nat.card (stabAt Γ K g) := Nat.card_congr
    { toFun := fun x => ⟨⟨_, (hH x).1 x.2⟩, by
        change g⁻¹ * (g * (x.1 : G) * g⁻¹) * g ∈ K
        simpa [mul_assoc] using x.1.2⟩
      invFun := fun y => ⟨⟨_, y.2⟩, (hH _).2 (by simpa [mul_assoc] using y.1.2)⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun y => by ext; simp [mul_assoc] }
  have hs : ∀ x : H, x ∈ MulAction.stabilizer H b ↔ (k : G)⁻¹ * x.1 * k ∈ K' := fun x => by
    rw [MulAction.mem_stabilizer_iff, eq_comm]
    change (QuotientGroup.mk k : K ⧸ K'.subgroupOf K) = QuotientGroup.mk (x.1 * k) ↔ _
    rw [QuotientGroup.eq, Subgroup.mem_subgroupOf]
    simp [mul_assoc]
  have e2 : Nat.card (MulAction.stabilizer H b) = Nat.card (stabAt Γ K' (g * k)) := Nat.card_congr
    { toFun := fun x => ⟨⟨_, (hH x.1).1 x.1.2⟩, by
        change (g * k)⁻¹ * (g * (x.1.1 : G) * g⁻¹) * (g * k) ∈ K'
        simpa [mul_assoc] using (hs _).1 x.2⟩
      invFun := fun y => ⟨⟨⟨g⁻¹ * y.1 * g, by
          have h1 : (g * k)⁻¹ * (y.1 : G) * (g * k) ∈ K := hle y.2
          simpa [mul_assoc] using K.mul_mem (K.mul_mem k.2 h1) (K.inv_mem k.2)⟩,
          (hH _).2 (by simpa [mul_assoc] using y.1.2)⟩, (hs _).2 (by
          have h1 : (g * k)⁻¹ * (y.1 : G) * (g * k) ∈ K' := y.2
          simpa [mul_assoc] using h1)⟩
      left_inv := fun x => by ext; simp [mul_assoc]
      right_inv := fun y => by ext; simp [mul_assoc] }
  have e3 : ∀ t : K ⧸ K'.subgroupOf K,
      (DoubleCoset.mk Γ K' (g * (t.out : K)) : ClassSet Γ K') = DoubleCoset.mk Γ K' (g * k) ↔
        t ∈ MulAction.orbit H b := fun t => by
    rw [eq_comm, DoubleCoset.eq]
    constructor
    · rintro ⟨γ, hγ, κ, hκ, e⟩
      have e' : g⁻¹ * γ * g = (t.out : K) * κ⁻¹ * (k : G)⁻¹ := by
        rw [← inv_mul_cancel_left g (t.out : K), e]; group
      have hm : g⁻¹ * γ * g ∈ K := e' ▸ K.mul_mem (K.mul_mem t.out.2 (K.inv_mem (hle hκ))) (K.inv_mem k.2)
      refine ⟨⟨⟨_, hm⟩, (hH _).2 (by simpa [mul_assoc] using hγ)⟩, ?_⟩
      change (QuotientGroup.mk (⟨_, hm⟩ * k) : K ⧸ K'.subgroupOf K) = t
      rw [← QuotientGroup.out_eq' t, QuotientGroup.eq, Subgroup.mem_subgroupOf]
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, e']
      simpa [mul_assoc] using hκ
    · rintro ⟨x, hx⟩
      change (QuotientGroup.mk (x.1 * k) : K ⧸ K'.subgroupOf K) = t at hx
      rw [← QuotientGroup.out_eq' t, QuotientGroup.eq, Subgroup.mem_subgroupOf] at hx
      refine ⟨_, (hH _).1 x.2, _, hx, ?_⟩
      simp [mul_assoc]
  rw [← e1, ← e0, e2]
  congr 1
  exact Nat.card_congr (Equiv.subtypeEquivRight e3)

/- English proof (translation)
Establish `h'` using `h.of_le hle hi`. Use `haveI := h.1`. Use `haveI := h'.1`. Use `haveI : Finite (K ⧸ K'.subgroupOf K) := Nat.finite_of_card_ne_zero hi`. Use `haveI := Fintype.ofFinite (ClassSet Γ K)`.

Use `haveI := Fintype.ofFinite (ClassSet Γ K')`. Use `haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)`. Set `φ : ClassSet Γ K × (K ⧸ K'.subgroupOf K) → ClassSet Γ K'` to `fun p => DoubleCoset.mk Γ K' (p.1.out * (p.2.out : K))`. Establish `h1 : (K'.relIndex K : ℝ) * classMass Γ K = ∑ p : ClassSet Γ K × (K ⧸ K'.subgroupOf K), ((stabOrder Γ K p.1 : ℝ))⁻¹`. Rewrite using `[Fintype.sum_prod_type, classMass_eq_sum, Finset.mul_sum]`.

Use `Finset.sum_congr rfl fun c _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]`. Rewrite using `[← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Rewrite using `[h1, ← Finset.sum_fiberwise (s := Finset.univ) (g := φ), classMass_eq_sum]`.

Use `Finset.sum_congr rfl fun d _ => ?_` and prove the remaining obligations. Proceed by induction on `d using Quotient.inductionOn' with`. Consider the case `h g`. Take `⟨γ, k, hγ, hk, e⟩` from `DoubleCoset.mk_out_eq_mul Γ K g`. Use `set c : ClassSet Γ K := DoubleCoset.mk Γ K g with hc`.

Establish `hd : (Quotient.mk'' g : ClassSet Γ K') = DoubleCoset.mk Γ K' (c.out * ((⟨k, hk⟩ : K)⁻¹ : K))` using `(DoubleCoset.eq Γ K' _ _).2 ⟨γ, hγ, 1, one_mem _, by rw [e]; simp⟩`. Rewrite using `[hd]`. Establish `key` using `card_fibre_mul (Γ := Γ) hle c.out (⟨k, hk⟩ : K)⁻¹`. Generalize the expression as in `((⟨k, hk⟩ : K)⁻¹ : K) = κ at key ⊢`. Establish `hf : ∀ p, φ p = DoubleCoset.mk Γ K' (c.out * κ) → p.1 = c` using `fun p hp => by`.

Take `⟨a, ha, b, hb, e⟩` from `(DoubleCoset.eq Γ K' _ _).1 hp`. Rewrite using `[← DoubleCoset.out_eq' _ _ p.1, ← DoubleCoset.out_eq' _ _ c]`. Use `(DoubleCoset.eq Γ K _ _).2 ⟨a, ha, (p.2.out : K) * b * (κ : G)⁻¹, K.mul_mem (K.mul_mem p.2.out.2 (hle hb)) (K.inv_mem κ.2), ?_⟩` and prove the remaining obligations. Rewrite using `[eq_mul_inv_of_mul_eq e]`. Use `group`.

Rewrite using `[Finset.sum_congr rfl (g := fun _ => ((stabOrder Γ K c : ℝ))⁻¹) fun p hp => by rw [hf p (Finset.mem_filter.1 hp).2], Finset.sum_const, nsmul_eq_mul]`. Establish `hcard : (Finset.univ.filter fun p => φ p = DoubleCoset.mk Γ K' (c.out * κ)).card = Nat.card {t : K ⧸ K'.subgroupOf K // (DoubleCoset.mk Γ K' (c.out * (t.out : K)) : ClassSet Γ K') = DoubleCoset.mk Γ K' (c.out * κ)}`. Rewrite using `[← Fintype.card_subtype, ← Nat.card_eq_fintype_card]`. Conclude with `Nat.card_congr { toFun := fun p => ⟨p.1.2, by`. Establish `h2 : DoubleCoset.mk Γ K' (p.1.1.out * (p.1.2.out : K)) = _` using `p.2`.

Rewrite using `[hf _ p.2] at h2⟩` and apply the resulting hypothesis. Use `invFun := fun t => ⟨(c, t.1), t.2⟩`. Use `left_inv := fun p => Subtype.ext (Prod.ext (hf _ p.2).symm rfl)`. Use `right_inv := fun t => rfl }`. Establish `p1` using `h'.stabOrder_pos (DoubleCoset.mk Γ K' (c.out * κ))`.

Establish `p2` using `h.stabOrder_pos c`. Establish `e2 : stabOrder Γ K c = Nat.card (stabAt Γ K c.out)` using `by rw [← stabOrder_mk, DoubleCoset.out_eq']`. Rewrite using `[hcard, e2, ← key, stabOrder_mk]`. Rewrite `p2` using `[e2, ← key]`. Rewrite `p1` using `[stabOrder_mk]`.

Establish `p3` using `Nat.pos_of_mul_pos_right p2`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.
-/
theorem classMass_of_le (h : FiniteClasses Γ K) (hle : K' ≤ K) (hi : K'.relIndex K ≠ 0) :
    classMass Γ K' = K'.relIndex K * classMass Γ K := by
  classical
  have h' := h.of_le hle hi
  haveI := h.1
  haveI := h'.1
  haveI : Finite (K ⧸ K'.subgroupOf K) := Nat.finite_of_card_ne_zero hi
  haveI := Fintype.ofFinite (ClassSet Γ K)
  haveI := Fintype.ofFinite (ClassSet Γ K')
  haveI := Fintype.ofFinite (K ⧸ K'.subgroupOf K)
  let φ : ClassSet Γ K × (K ⧸ K'.subgroupOf K) → ClassSet Γ K' :=
    fun p => DoubleCoset.mk Γ K' (p.1.out * (p.2.out : K))
  have h1 : (K'.relIndex K : ℝ) * classMass Γ K =
      ∑ p : ClassSet Γ K × (K ⧸ K'.subgroupOf K), ((stabOrder Γ K p.1 : ℝ))⁻¹ := by
    rw [Fintype.sum_prod_type, classMass_eq_sum, Finset.mul_sum]
    refine Finset.sum_congr rfl fun c _ => ?_
    simp only [Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
    rw [← Nat.card_eq_fintype_card]
    rfl
  rw [h1, ← Finset.sum_fiberwise (s := Finset.univ) (g := φ), classMass_eq_sum]
  refine Finset.sum_congr rfl fun d _ => ?_
  induction d using Quotient.inductionOn' with
  | h g =>
    obtain ⟨γ, k, hγ, hk, e⟩ := DoubleCoset.mk_out_eq_mul Γ K g
    set c : ClassSet Γ K := DoubleCoset.mk Γ K g with hc
    have hd : (Quotient.mk'' g : ClassSet Γ K') = DoubleCoset.mk Γ K' (c.out * ((⟨k, hk⟩ : K)⁻¹ : K)) :=
      (DoubleCoset.eq Γ K' _ _).2 ⟨γ, hγ, 1, one_mem _, by rw [e]; simp⟩
    rw [hd]
    have key := card_fibre_mul (Γ := Γ) hle c.out (⟨k, hk⟩ : K)⁻¹
    generalize ((⟨k, hk⟩ : K)⁻¹ : K) = κ at key ⊢
    have hf : ∀ p, φ p = DoubleCoset.mk Γ K' (c.out * κ) → p.1 = c := fun p hp => by
      obtain ⟨a, ha, b, hb, e⟩ := (DoubleCoset.eq Γ K' _ _).1 hp
      rw [← DoubleCoset.out_eq' _ _ p.1, ← DoubleCoset.out_eq' _ _ c]
      refine (DoubleCoset.eq Γ K _ _).2 ⟨a, ha, (p.2.out : K) * b * (κ : G)⁻¹,
        K.mul_mem (K.mul_mem p.2.out.2 (hle hb)) (K.inv_mem κ.2), ?_⟩
      rw [eq_mul_inv_of_mul_eq e]; group
    rw [Finset.sum_congr rfl (g := fun _ => ((stabOrder Γ K c : ℝ))⁻¹)
      fun p hp => by rw [hf p (Finset.mem_filter.1 hp).2], Finset.sum_const, nsmul_eq_mul]
    have hcard : (Finset.univ.filter fun p => φ p = DoubleCoset.mk Γ K' (c.out * κ)).card =
        Nat.card {t : K ⧸ K'.subgroupOf K //
          (DoubleCoset.mk Γ K' (c.out * (t.out : K)) : ClassSet Γ K') = DoubleCoset.mk Γ K' (c.out * κ)} := by
      rw [← Fintype.card_subtype, ← Nat.card_eq_fintype_card]
      exact Nat.card_congr
        { toFun := fun p => ⟨p.1.2, by
            have h2 : DoubleCoset.mk Γ K' (p.1.1.out * (p.1.2.out : K)) = _ := p.2
            rwa [hf _ p.2] at h2⟩
          invFun := fun t => ⟨(c, t.1), t.2⟩
          left_inv := fun p => Subtype.ext (Prod.ext (hf _ p.2).symm rfl)
          right_inv := fun t => rfl }
    have p1 := h'.stabOrder_pos (DoubleCoset.mk Γ K' (c.out * κ))
    have p2 := h.stabOrder_pos c
    have e2 : stabOrder Γ K c = Nat.card (stabAt Γ K c.out) := by rw [← stabOrder_mk, DoubleCoset.out_eq']
    rw [hcard, e2, ← key, stabOrder_mk]
    rw [e2, ← key] at p2
    rw [stabOrder_mk] at p1
    have p3 := Nat.pos_of_mul_pos_right p2
    push_cast
    field_simp

/- English proof (translation)
Establish `h1` using `classMass_of_le (finiteClasses_of_finite Γ K) (K' := ⊥) bot_le (by rw [Subgroup.relIndex_bot_left]; exact Nat.card_pos.ne')`. Use `haveI : Finite (ClassSet Γ ⊥) := (finiteClasses_of_finite Γ ⊥).1`. Rewrite using `[classMass_of_isNeat fun g => Set.eq_singleton_iff_unique_mem.2 ⟨one_mem_stabAt _ _ _, fun x hx => by`. Establish `: g⁻¹ * (x : G) * g = 1` using `hx`. Use `ext`.

Simplify `congrArg (fun y => g * y * g⁻¹) this⟩, Subgroup.relIndex_bot_left] at h1` using `[mul_assoc]`. Establish `e : ClassSet Γ ⊥ = Quotient (QuotientGroup.rightRel Γ)` using `DoubleCoset.right_bot_eq_right_quot Γ`. Establish `h2 : Nat.card (ClassSet Γ ⊥) = Γ.index`. Rewrite using `[e]`. Conclude with `Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)`.

Establish `h3 : (Γ.index : ℝ) * Nat.card Γ = Nat.card G` using `by exact_mod_cast Γ.index_mul_card`. Establish `p1 : (0 : ℝ) < Nat.card Γ` using `by exact_mod_cast Nat.card_pos`. Establish `p2 : (0 : ℝ) < Nat.card K` using `by exact_mod_cast Nat.card_pos`. Rewrite using `[← h3, ← h2, h1]`. Clear the denominators using the available nonvanishing facts.
-/
theorem classMass_finite [Finite G] (Γ K : Subgroup G) :
    classMass Γ K = (Nat.card G : ℝ) / (Nat.card Γ * Nat.card K) := by
  have h1 := classMass_of_le (finiteClasses_of_finite Γ K) (K' := ⊥) bot_le
    (by rw [Subgroup.relIndex_bot_left]; exact Nat.card_pos.ne')
  haveI : Finite (ClassSet Γ ⊥) := (finiteClasses_of_finite Γ ⊥).1
  rw [classMass_of_isNeat fun g => Set.eq_singleton_iff_unique_mem.2 ⟨one_mem_stabAt _ _ _, fun x hx => by
    have : g⁻¹ * (x : G) * g = 1 := hx
    ext; simpa [mul_assoc] using congrArg (fun y => g * y * g⁻¹) this⟩, Subgroup.relIndex_bot_left] at h1
  have e : ClassSet Γ ⊥ = Quotient (QuotientGroup.rightRel Γ) := DoubleCoset.right_bot_eq_right_quot Γ
  have h2 : Nat.card (ClassSet Γ ⊥) = Γ.index := by
    rw [e]; exact Nat.card_congr (QuotientGroup.quotientRightRelEquivQuotientLeftRel Γ)
  have h3 : (Γ.index : ℝ) * Nat.card Γ = Nat.card G := by exact_mod_cast Γ.index_mul_card
  have p1 : (0 : ℝ) < Nat.card Γ := by exact_mod_cast Nat.card_pos
  have p2 : (0 : ℝ) < Nat.card K := by exact_mod_cast Nat.card_pos
  rw [← h3, ← h2, h1]
  field_simp

/- English proof (translation)
Establish `: orderOf (Equiv.swap (0 : Fin 3) 1) = 2` using `orderOf_eq_prime (by decide) (by decide)`. Rewrite using `[classMass_finite, Nat.card_zpowers, this, Nat.card_eq_fintype_card, Fintype.card_perm]`. Evaluate the numerical expressions using `[Nat.factorial]`.
-/
theorem classMass_swap : classMass (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1))
    (Subgroup.zpowers (Equiv.swap (0 : Fin 3) 1)) = 3 / 2 := by
  have : orderOf (Equiv.swap (0 : Fin 3) 1) = 2 := orderOf_eq_prime (by decide) (by decide)
  rw [classMass_finite, Nat.card_zpowers, this, Nat.card_eq_fintype_card, Fintype.card_perm]
  norm_num [Nat.factorial]

/- English proof (translation)
Establish `hn : ∀ c, stabOrder (⊥ : Subgroup G) ⊥ c = 1` using `fun c => by`. Proceed by induction on `c using Quotient.inductionOn' with`. Consider the case `h g => haveI : Nonempty (stabAt (⊥ : Subgroup G) ⊥ g) := ⟨⟨1, one_mem_stabAt _ _ _⟩⟩`. Conclude with `Nat.card_unique (α := stabAt (⊥ : Subgroup G) ⊥ g)`. Use `haveI : Infinite (ClassSet (⊥ : Subgroup G) ⊥) := Infinite.of_injective (fun g => DoubleCoset.mk ⊥ ⊥ g) fun a b e => by`.

Take `⟨x, hx, y, hy, e⟩` from `(DoubleCoset.eq _ _ _ _).1 e`. Rewrite using `[e, Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]`. Simplify using the standard rewrite rules. Use `finsum_of_infinite_support ?_` and prove the remaining obligations. Establish `: (Function.support fun c : ClassSet (⊥ : Subgroup G) ⊥ => ((stabOrder ⊥ ⊥ c : ℝ))⁻¹) = Set.univ` using `Set.eq_univ_of_forall fun c => by simp [hn]`.

Rewrite using `[this]`. Conclude with `Set.infinite_univ`.
-/
theorem classMass_bot_bot_of_infinite [Infinite G] : classMass (⊥ : Subgroup G) ⊥ = 0 := by
  have hn : ∀ c, stabOrder (⊥ : Subgroup G) ⊥ c = 1 := fun c => by
    induction c using Quotient.inductionOn' with
    | h g =>
      haveI : Nonempty (stabAt (⊥ : Subgroup G) ⊥ g) := ⟨⟨1, one_mem_stabAt _ _ _⟩⟩
      exact Nat.card_unique (α := stabAt (⊥ : Subgroup G) ⊥ g)
  haveI : Infinite (ClassSet (⊥ : Subgroup G) ⊥) :=
    Infinite.of_injective (fun g => DoubleCoset.mk ⊥ ⊥ g) fun a b e => by
      obtain ⟨x, hx, y, hy, e⟩ := (DoubleCoset.eq _ _ _ _).1 e
      rw [e, Subgroup.mem_bot.1 hx, Subgroup.mem_bot.1 hy]; simp
  refine finsum_of_infinite_support ?_
  have : (Function.support fun c : ClassSet (⊥ : Subgroup G) ⊥ => ((stabOrder ⊥ ⊥ c : ℝ))⁻¹) = Set.univ :=
    Set.eq_univ_of_forall fun c => by simp [hn]
  rw [this]
  exact Set.infinite_univ

end Abstract

section Unitary

open Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes NumberField IsDedekindDomain
open scoped TensorProduct Matrix

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {M : ℕ} {J : Matrix (Fin M) (Fin M) E}

/- English proof (translation)
Use `haveI := topGroup_fin σ J`. Establish `hi` using `relIndex_ne_zero_of_isOpen hc ho'`. Conclude with `⟨hi, classMass_of_le (finiteClasses_unitary hσ hJ hd hc (Subgroup.isOpen_mono hle ho')) hle hi⟩`.
-/
theorem unitaryMass_of_le (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hd : IsTotDef σ J)
    {K K' : Subgroup (HA (Af F) σ J)} (hc : IsCompact (K : Set (HA (Af F) σ J)))
    (ho' : IsOpen (K' : Set (HA (Af F) σ J))) (hle : K' ≤ K) :
    K'.relIndex K ≠ 0 ∧ unitaryMass σ J K' = K'.relIndex K * unitaryMass σ J K := by
  haveI := topGroup_fin σ J
  have hi := relIndex_ne_zero_of_isOpen hc ho'
  exact ⟨hi, classMass_of_le (finiteClasses_unitary hσ hJ hd hc (Subgroup.isOpen_mono hle ho')) hle hi⟩

/- English proof (translation)
Take `⟨e, he, -, hc⟩` from `GlobalTheory.AdSplit.exists_adele_equiv F E`. Use `choose s h1 h2 using fun b : HA (Af F) σ J => (parts_spec σ J).2 1 (HA.mat (Af F) σ J b)`. Establish `hm : Continuous (HA.mat (Af F) σ J)` using `continuous_subtype_val`. Use `⟨fun b => ⟨s b, ((parts_spec σ J).1 _).2 ⟨h1 b ▸ one_mem _, h2 b ▸ b.2⟩⟩, ?_, fun b => Subtype.ext ((h _).trans (h2 b))⟩` and prove the remaining obligations. Use `continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)` and prove the remaining obligations.

Use `continuous_matrix fun i j => (hc.comp ((continuous_const (y := (1 : Matrix (Fin M) (Fin M) _) i j)).prodMk ((Units.continuous_val.comp hm).matrix_elem i j))).congr fun b => e.symm_apply_eq.2 (Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun z : GL (Fin M) _ => z.1 i j) (h1 b)).symm.trans (he _).1.symm`. Conclude with `(congrArg (fun z : GL (Fin M) _ => z.1 i j) (h2 b)).symm.trans (he _).2.symm`. Use `continuous_matrix fun i j => (hc.comp ((continuous_const (y := (1 : Matrix (Fin M) (Fin M) _) i j)).prodMk ((Units.continuous_coe_inv.comp hm).matrix_elem i j))).congr fun b => e.symm_apply_eq.2 (Prod.ext ?_ ?_)` and prove the remaining obligations. Conclude with `(congrArg (fun z : GL (Fin M) _ => (z⁻¹).1 i j) (h1 b)).symm.trans (he _).1.symm`.

Conclude with `(congrArg (fun z : GL (Fin M) _ => (z⁻¹).1 i j) (h2 b)).symm.trans (he _).2.symm`.
-/
theorem exists_section {π : HA (AF F) σ J →* HA (Af F) σ J} (h : IsFinProj σ J π) :
    ∃ s : HA (Af F) σ J → HA (AF F) σ J, Continuous s ∧ ∀ b, π (s b) = b := by
  obtain ⟨e, he, -, hc⟩ := GlobalTheory.AdSplit.exists_adele_equiv F E
  choose s h1 h2 using fun b : HA (Af F) σ J => (parts_spec σ J).2 1 (HA.mat (Af F) σ J b)
  have hm : Continuous (HA.mat (Af F) σ J) := continuous_subtype_val
  refine ⟨fun b => ⟨s b, ((parts_spec σ J).1 _).2 ⟨h1 b ▸ one_mem _, h2 b ▸ b.2⟩⟩, ?_,
    fun b => Subtype.ext ((h _).trans (h2 b))⟩
  refine continuous_induced_rng.2 (Units.continuous_iff.2 ⟨?_, ?_⟩)
  · refine continuous_matrix fun i j => (hc.comp ((continuous_const (y := (1 : Matrix (Fin M) (Fin M) _) i j)).prodMk
      ((Units.continuous_val.comp hm).matrix_elem i j))).congr fun b => e.symm_apply_eq.2 (Prod.ext ?_ ?_)
    · exact (congrArg (fun z : GL (Fin M) _ => z.1 i j) (h1 b)).symm.trans (he _).1.symm
    · exact (congrArg (fun z : GL (Fin M) _ => z.1 i j) (h2 b)).symm.trans (he _).2.symm
  · refine continuous_matrix fun i j => (hc.comp ((continuous_const (y := (1 : Matrix (Fin M) (Fin M) _) i j)).prodMk
      ((Units.continuous_coe_inv.comp hm).matrix_elem i j))).congr fun b => e.symm_apply_eq.2 (Prod.ext ?_ ?_)
    · exact (congrArg (fun z : GL (Fin M) _ => (z⁻¹).1 i j) (h1 b)).symm.trans (he _).1.symm
    · exact (congrArg (fun z : GL (Fin M) _ => (z⁻¹).1 i j) (h2 b)).symm.trans (he _).2.symm

/- English proof (translation)
Take `⟨s, hs, e⟩` from `exists_section h`. Use `ho.preimage hs using 1` and compare the differences between its conclusion and the goal. Use extensionality with `b`. Simplify using `[e]`.
-/
theorem isOpen_of_comap {π : HA (AF F) σ J →* HA (Af F) σ J} (h : IsFinProj σ J π)
    {L : Subgroup (HA (Af F) σ J)} (ho : IsOpen (L.comap π : Set (HA (AF F) σ J))) :
    IsOpen (L : Set (HA (Af F) σ J)) := by
  obtain ⟨s, hs, e⟩ := exists_section h
  convert ho.preimage hs using 1
  ext b
  simp [e]

/- English proof (translation)
Proceed by induction on `c using Quotient.inductionOn' with`. Consider the case `h g`. Establish `hf` using `finiteClasses_unitary hσ hJ hd (isCompact_stdLevel σ J hJ.2) (isOpen_stdLevel σ J)`. Use `haveI := hf.2 g`. Use `haveI : Nontrivial (Af F) := by`.

Take `⟨P, hP⟩` from `Ideal.exists_maximal (𝓞 F)`. Conclude with `(Formalism.UG.evalV F ⟨P, hP.isPrime, Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩).toRingHom.domain_nontrivial`. Use `haveI : Nontrivial (Af F ⊗[F] E) := (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Af F) (B := E) (algebraMap F E).injective).nontrivial`. Establish `hm : (-1 : GL (Fin M) (Af F ⊗[F] E)) ∈ HR (Af F) σ J`. Express the relevant statement in the definitionally equal form `cT _ _ * _ * _ = _`.

Simplify using `[cT, Matrix.map_neg]`. Set `m : HA (Af F) σ J` to `⟨-1, hm⟩`. Establish `hr : m ∈ ratIn (Af F) σ J`. Use `⟨-1, ?_, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cT _ _ * _ * _ = _`.

Simplify using `[cT, Matrix.map_neg]`. Use `Units.ext ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((-1 : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) = -1`. Simplify using `[Matrix.map_neg]`. Establish `hc : g⁻¹ * m * g = m` using `Subtype.ext (by`.

Express the relevant statement in the definitionally equal form `(HA.mat _ σ J g)⁻¹ * (-1) * HA.mat _ σ J g = -1`. Use the proof step `simp)`. Establish `hs : m ∈ stdLevel σ J` using `(mem_stdLevel σ J m).2 fun i j => by`. Express the relevant statement in the definitionally equal form `((-1 : GL (Fin M) (Af F ⊗[F] E)).1 i j ∈ _) ∧ ((-1 : GL (Fin M) (Af F ⊗[F] E))⁻¹.1 i j ∈ _)`. Establish `: (-1 : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) i j ∈ intTens F E`.

Rewrite using `[Matrix.neg_apply, Matrix.one_apply]`. Use `split_ifs`. Use `exacts [neg_mem (one_mem _), neg_mem (zero_mem _)]`. Simplify using `using this`. Use `haveI : Nontrivial (stabAt (ratIn (Af F) σ J) (stdLevel σ J) g) := ⟨⟨⟨⟨m, hr⟩, by change g⁻¹ * m * g ∈ stdLevel σ J; rwa [hc]⟩, ⟨1, one_mem_stabAt _ _ _⟩, fun e => by`.

Establish `e1 : (-1 : GL (Fin M) (Af F ⊗[F] E)) = 1` using `congrArg (fun z => HA.mat _ σ J z.1.1) e`. Establish `e2` using `congrArg (fun z : GL (Fin M) (Af F ⊗[F] E) => z.1 ⟨0, hM⟩ ⟨0, hM⟩) e1`. Establish `e3 : inclR (F` using `F) (E := E) (Af F) (-1) = inclR (F := F) (E := E) (Af F) 1 := by simpa using e2`. Use `(inclR (F := F) (E := E) (Af F)).injective e3` as an intermediate fact. Evaluate the numerical expressions using `at this⟩⟩`.

Conclude with `Finite.one_lt_card (α := stabAt (ratIn (Af F) σ J) (stdLevel σ J) g)`.
-/
theorem two_le_stabOrder_std (hσ : IsCMExt F E σ) (hJ : IsHermND σ J) (hd : IsTotDef σ J) (hM : 0 < M)
    (c : ClassSet (ratIn (Af F) σ J) (stdLevel σ J)) : 2 ≤ stabOrder _ _ c := by
  induction c using Quotient.inductionOn' with
  | h g =>
    have hf := finiteClasses_unitary hσ hJ hd (isCompact_stdLevel σ J hJ.2) (isOpen_stdLevel σ J)
    haveI := hf.2 g
    haveI : Nontrivial (Af F) := by
      obtain ⟨P, hP⟩ := Ideal.exists_maximal (𝓞 F)
      exact (Formalism.UG.evalV F ⟨P, hP.isPrime,
        Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField F)⟩).toRingHom.domain_nontrivial
    haveI : Nontrivial (Af F ⊗[F] E) :=
      (Algebra.TensorProduct.includeLeft_injective (R := F) (S := F) (A := Af F) (B := E)
        (algebraMap F E).injective).nontrivial
    have hm : (-1 : GL (Fin M) (Af F ⊗[F] E)) ∈ HR (Af F) σ J := by
      change cT _ _ * _ * _ = _
      simp [cT, Matrix.map_neg]
    let m : HA (Af F) σ J := ⟨-1, hm⟩
    have hr : m ∈ ratIn (Af F) σ J := by
      refine ⟨-1, ?_, ?_⟩
      · change cT _ _ * _ * _ = _
        simp [cT, Matrix.map_neg]
      · refine Units.ext ?_
        change ((-1 : GL (Fin M) E) : Matrix (Fin M) (Fin M) E).map (inclR (F := F) (Af F)) = -1
        simp [Matrix.map_neg]
    have hc : g⁻¹ * m * g = m := Subtype.ext (by
      change (HA.mat _ σ J g)⁻¹ * (-1) * HA.mat _ σ J g = -1
      simp)
    have hs : m ∈ stdLevel σ J := (mem_stdLevel σ J m).2 fun i j => by
      change ((-1 : GL (Fin M) (Af F ⊗[F] E)).1 i j ∈ _) ∧ ((-1 : GL (Fin M) (Af F ⊗[F] E))⁻¹.1 i j ∈ _)
      have : (-1 : Matrix (Fin M) (Fin M) (Af F ⊗[F] E)) i j ∈ intTens F E := by
        rw [Matrix.neg_apply, Matrix.one_apply]
        split_ifs
        exacts [neg_mem (one_mem _), neg_mem (zero_mem _)]
      simpa using this
    haveI : Nontrivial (stabAt (ratIn (Af F) σ J) (stdLevel σ J) g) :=
      ⟨⟨⟨⟨m, hr⟩, by change g⁻¹ * m * g ∈ stdLevel σ J; rwa [hc]⟩, ⟨1, one_mem_stabAt _ _ _⟩, fun e => by
        have e1 : (-1 : GL (Fin M) (Af F ⊗[F] E)) = 1 := congrArg (fun z => HA.mat _ σ J z.1.1) e
        have e2 := congrArg (fun z : GL (Fin M) (Af F ⊗[F] E) => z.1 ⟨0, hM⟩ ⟨0, hM⟩) e1
        have e3 : inclR (F := F) (E := E) (Af F) (-1) = inclR (F := F) (E := E) (Af F) 1 := by simpa using e2
        have := (inclR (F := F) (E := E) (Af F)).injective e3
        norm_num at this⟩⟩
    exact Finite.one_lt_card (α := stabAt (ratIn (Af F) σ J) (stdLevel σ J) g)

end Unitary

section Record

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.Theta

attribute [local instance] Formalism.BasicNotions.Host.cmStar

/- English proof (translation)
Establish `hk : π.ker = GinfC V`. Use extensionality with `g`. Establish `hg : HA.mat _ _ _ (π g) = finHom V g` using `h g`. Rewrite using `[MonoidHom.mem_ker, GinfC, MonoidHom.mem_ker, ← hg]`. Conclude with `⟨fun e => by rw [e]; rfl, fun e => Subtype.ext e⟩`.

Rewrite using `[h.unitaryMass_eq, Subgroup.comap_map_eq, hk]`. Both sides reduce to the same expression.
-/
theorem unitaryMass_map_eq {D : D7} (V : HSp D)
    {π : GA D V →* HA (Af D.host.F) D.sp.cm.sig V.gram} (h : IsFinProj D.sp.cm.sig V.gram π)
    (K : Subgroup (GA D V)) :
    unitaryMass D.sp.cm.sig V.gram (K.map π) = classMass (GQ V) (K ⊔ GinfC V) := by
  have hk : π.ker = GinfC V := by
    ext g
    have hg : HA.mat _ _ _ (π g) = finHom V g := h g
    rw [MonoidHom.mem_ker, GinfC, MonoidHom.mem_ker, ← hg]
    exact ⟨fun e => by rw [e]; rfl, fun e => Subtype.ext e⟩
  rw [h.unitaryMass_eq, Subgroup.comap_map_eq, hk]
  rfl

/- English proof (translation)
Take `⟨π, h, -⟩` from `existsUnique_isFinProj D.sp.cm.sig V.gram`. Establish `hk : π.ker = GinfC V`. Use extensionality with `g`. Establish `hg : HA.mat _ _ _ (π g) = finHom V g` using `h g`. Rewrite using `[MonoidHom.mem_ker, GinfC, MonoidHom.mem_ker, ← hg]`.

Conclude with `⟨fun e => by rw [e]; rfl, fun e => Subtype.ext e⟩`. Rewrite `ho`, the goal using `[← hk, ← Subgroup.comap_map_eq]`. Use `(finiteClasses_comap π (ratIn _ _ _) _ h.surjective h.injOn).2 ?_` and prove the remaining obligations. Rewrite using `[h.map_ratIn]`. Conclude with `finiteClasses_unitary hσ hJ hd (hc.image h.continuous) (isOpen_of_comap h ho)`.
-/
theorem finiteClasses_record {D : D7} (V : HSp D) (hσ : IsCMExt D.host.F D.host.E D.sp.cm.sig)
    (hJ : IsHermND D.sp.cm.sig V.gram) (hd : IsTotDef D.sp.cm.sig V.gram) {K : Subgroup (GA D V)}
    (hc : IsCompact (K : Set (GA D V))) (ho : IsOpen ((K ⊔ GinfC V : Subgroup (GA D V)) : Set (GA D V))) :
    FiniteClasses (GQ V) (K ⊔ GinfC V) := by
  obtain ⟨π, h, -⟩ := existsUnique_isFinProj D.sp.cm.sig V.gram
  have hk : π.ker = GinfC V := by
    ext g
    have hg : HA.mat _ _ _ (π g) = finHom V g := h g
    rw [MonoidHom.mem_ker, GinfC, MonoidHom.mem_ker, ← hg]
    exact ⟨fun e => by rw [e]; rfl, fun e => Subtype.ext e⟩
  rw [← hk, ← Subgroup.comap_map_eq] at ho ⊢
  refine (finiteClasses_comap π (ratIn _ _ _) _ h.surjective h.injOn).2 ?_
  rw [h.map_ratIn]
  exact finiteClasses_unitary hσ hJ hd (hc.image h.continuous) (isOpen_of_comap h ho)

end Record

end GlobalTheory.Mass.Model
