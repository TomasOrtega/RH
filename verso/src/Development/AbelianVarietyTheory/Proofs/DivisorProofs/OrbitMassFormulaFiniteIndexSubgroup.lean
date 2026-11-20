import Mathlib

open MulAction

namespace GlobalTheory.OrbitMass

variable {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D]

def toG (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) :
    orbitRel.Quotient H D → orbitRel.Quotient G D :=
  Quotient.map' id (fun a b hab => by
    change a ∈ orbit H b at hab
    change a ∈ orbit G b
    obtain ⟨h, rfl⟩ := hab
    exact ⟨ι h, hc h b⟩)

def toCoset (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) :
    G ⧸ ι.range → orbitRel.Quotient H D :=
  fun ω => Quotient.liftOn' ω (fun g => (Quotient.mk'' (g⁻¹ • x) : orbitRel.Quotient H D)) (by
    intro g₁ g₂ hg
    rw [QuotientGroup.leftRel_apply, MonoidHom.mem_range] at hg
    obtain ⟨h, hh⟩ := hg
    apply Quotient.sound'
    change g₁⁻¹ • x ∈ orbit H (g₂⁻¹ • x)
    refine ⟨h, ?_⟩
    change h • g₂⁻¹ • x = g₁⁻¹ • x
    rw [← hc, smul_smul, hh, mul_inv_cancel_right])

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toCoset_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (g⁻¹ • x) := rfl

/- English proof (translation)
Rewrite using `[toCoset_mk, Quotient.eq'']`. Express the relevant statement in the definitionally equal form `g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _`. Rewrite using `[mem_orbit_iff, mem_orbit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h, hh⟩`.

Use `⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]`. Express the relevant statement in the definitionally equal form `((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g`. Rewrite using `[MulAction.Quotient.smul_mk, QuotientGroup.eq]`. Conclude with `⟨h⁻¹, by simp [mul_assoc]⟩`.

Introduce and unpack `⟨⟨s, hs⟩, hsa⟩`. Express the relevant statement in the definitionally equal form `((s : G) • (a : G ⧸ ι.range)) = g at hsa`. Rewrite `hsa` using `[MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range]`. Take `⟨k, hk⟩` from `hsa`. Establish `hg : g = s * a * ι k` using `by rw [hk, smul_eq_mul, mul_inv_cancel_left]`.

Substitute `hg` using the available equality. Establish `hs' : s⁻¹ • x = x` using `by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm`. Use `⟨k⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']`.
-/
theorem toCoset_eq_iff (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a g : G) :
    toCoset ι hc x (g : G ⧸ ι.range) = Quotient.mk'' (a⁻¹ • x) ↔
      (g : G ⧸ ι.range) ∈ orbit (stabilizer G x) (a : G ⧸ ι.range) := by
  rw [toCoset_mk, Quotient.eq'']
  change g⁻¹ • x ∈ orbit H (a⁻¹ • x) ↔ _
  rw [mem_orbit_iff, mem_orbit_iff]
  constructor
  · rintro ⟨h, hh⟩
    refine ⟨⟨g * ι h * a⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, hh, smul_inv_smul]
    · change ((g * ι h * a⁻¹ : G) • (a : G ⧸ ι.range)) = g
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      exact ⟨h⁻¹, by simp [mul_assoc]⟩
  · rintro ⟨⟨s, hs⟩, hsa⟩
    change ((s : G) • (a : G ⧸ ι.range)) = g at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have hg : g = s * a * ι k := by rw [hk, smul_eq_mul, mul_inv_cancel_left]
    subst hg
    have hs' : s⁻¹ • x = x := by rw [inv_smul_eq_iff]; exact (mem_stabilizer_iff.mp hs).symm
    refine ⟨k⁻¹, ?_⟩
    rw [← hc, map_inv, mul_inv_rev, mul_inv_rev, mul_smul, mul_smul, hs']

/- English proof (translation)
Use `symm`. Use `Nat.card_eq_of_bijective (fun h => ⟨⟨a * ι h.1 * a⁻¹, by` and prove the remaining obligations. Rewrite using `[mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,`. Use `by`. Rewrite using `[mem_stabilizer_iff]`.

Express the relevant statement in the definitionally equal form `((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a`. Rewrite using `[MulAction.Quotient.smul_mk, QuotientGroup.eq]`. Conclude with `⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩`. Introduce `h₁ h₂ he`. Establish `e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹` using `congrArg (fun s => ((s.1 : stabilizer G x) : G)) he`.

Conclude with `Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))`. Introduce and unpack `⟨⟨s, hs⟩, hsa⟩`. Rewrite `hsa` using `[mem_stabilizer_iff]`. Express the relevant statement in the definitionally equal form `((s : G) • (a : G ⧸ ι.range)) = a at hsa`. Rewrite `hsa` using `[MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range]`.

Take `⟨k, hk⟩` from `hsa`. Establish `e : ι k⁻¹ = a⁻¹ * s * a`. Rewrite using `[map_inv, hk, smul_eq_mul]`. Use `group`. Use `⟨⟨k⁻¹, ?_⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `a * ι k⁻¹ * a⁻¹ = s`. Rewrite using `[e]`.

Use `group`.
-/
theorem card_stab (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) (x : D) (a : G) :
    Nat.card (stabilizer (stabilizer G x) (a : G ⧸ ι.range)) =
      Nat.card (stabilizer H (a⁻¹ • x)) := by
  symm
  refine Nat.card_eq_of_bijective
    (fun h => ⟨⟨a * ι h.1 * a⁻¹, by
      rw [mem_stabilizer_iff, mul_smul, mul_smul, hc, mem_stabilizer_iff.mp h.2, smul_inv_smul]⟩,
      by
        rw [mem_stabilizer_iff]
        change ((a * ι h.1 * a⁻¹ : G) • (a : G ⧸ ι.range)) = a
        rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
        exact ⟨h.1⁻¹, by simp [mul_assoc]⟩⟩) ⟨?_, ?_⟩
  · intro h₁ h₂ he
    have e : a * ι h₁.1 * a⁻¹ = a * ι h₂.1 * a⁻¹ := congrArg (fun s => ((s.1 : stabilizer G x) : G)) he
    exact Subtype.ext (hinj (mul_left_cancel (mul_right_cancel e)))
  · rintro ⟨⟨s, hs⟩, hsa⟩
    rw [mem_stabilizer_iff] at hsa
    change ((s : G) • (a : G ⧸ ι.range)) = a at hsa
    rw [MulAction.Quotient.smul_mk, QuotientGroup.eq, MonoidHom.mem_range] at hsa
    obtain ⟨k, hk⟩ := hsa
    have e : ι k⁻¹ = a⁻¹ * s * a := by
      rw [map_inv, hk, smul_eq_mul]; group
    refine ⟨⟨k⁻¹, ?_⟩, ?_⟩
    · rw [mem_stabilizer_iff, ← hc, e, mul_smul, mul_smul, smul_inv_smul, mem_stabilizer_iff.mp hs]
    · apply Subtype.ext; apply Subtype.ext
      change a * ι k⁻¹ * a⁻¹ = s
      rw [e]; group

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toG_mk (ι : H →* G) (hc : ∀ (h : H) (d : D), ι h • d = h • d) (y : D) :
    toG ι hc (Quotient.mk'' y) = Quotient.mk'' y := rfl

/- English proof (translation)
Use `set x := Quotient.out c' with hx`. Use `haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _`. Establish `hS0 : 0 < Nat.card (stabilizer G x)` using `Nat.card_pos`. Establish `hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) = ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹`. Rewrite using `[Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card, Nat.card_eq_fintype_card, div_eq_mul_inv]`.

Rewrite using `[hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]`. Use `Finset.sum_congr rfl (fun c _ => ?_)` and prove the remaining obligations. Rewrite using `[Finset.sum_const, nsmul_eq_mul]`. Use `split_ifs with hcx`. Establish `hmem : Quotient.out c ∈ orbit G x`.

Establish `h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x`. Rewrite using `[← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']`. Conclude with `Quotient.exact' h1`. Take `⟨b, hb⟩` from `hmem`. Establish `hy : (b⁻¹)⁻¹ • x = Quotient.out c` using `by rw [inv_inv]; exact hb`.

Establish `hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) = (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset`. Use extensionality with `ω`. Proceed by induction on `ω using QuotientGroup.induction_on with`. Consider the case `H g`. Rewrite using `[Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy, Quotient.out_eq']`.

Simplify using the standard rewrite rules. Establish `hcard` using `Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))`. Rewrite `hcard` using `[index_stabilizer, card_stab ι hinj hc x b⁻¹, hy]`. Rewrite using `[hfib, ← Set.ncard_eq_toFinset_card']`. Establish `hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0`.

Introduce `h0`. Rewrite `hcard` using `[h0, zero_mul]`. Use linear arithmetic over natural numbers and integers. Establish `hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0`. Introduce `h0`.

Rewrite `hcard` using `[h0, mul_zero]`. Use linear arithmetic over natural numbers and integers. Rewrite using `[← hcard]`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Rewrite using `[Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]`. Rewrite using `[Finset.filter_eq_empty_iff]`. Introduce `ω _ hω`. Apply `hcx` to reduce the goal to its premises. Rewrite using `[← hω]`.

Proceed by induction on `ω using QuotientGroup.induction_on with`. Consider the case `H g`. Rewrite using `[toCoset_mk, toG_mk, hx]`. Use `conv_rhs => rw [← Quotient.out_eq' c']`. Conclude with `Quotient.sound' ⟨g⁻¹, rfl⟩`.
-/
theorem sum_fiber (ι : H →* G) (hinj : Function.Injective ι)
    (hc : ∀ (h : H) (d : D), ι h • d = h • d) [ι.range.FiniteIndex]
    (c' : orbitRel.Quotient G D) [Finite (stabilizer G (Quotient.out c'))]
    [Fintype (orbitRel.Quotient H D)] [DecidableEq (orbitRel.Quotient G D)] :
    ∑ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
        ((Nat.card (stabilizer H (Quotient.out c)) : ℂ))⁻¹
      = (ι.range.index : ℂ) / Nat.card (stabilizer G (Quotient.out c')) := by
  classical
  set x := Quotient.out c' with hx
  haveI : Fintype (G ⧸ ι.range) := Fintype.ofFinite _
  have hS0 : 0 < Nat.card (stabilizer G x) := Nat.card_pos
  have hidx : (ι.range.index : ℂ) / Nat.card (stabilizer G x) =
      ∑ _ω : G ⧸ ι.range, ((Nat.card (stabilizer G x) : ℂ))⁻¹ := by
    rw [Finset.sum_const, Finset.card_univ, nsmul_eq_mul, Subgroup.index_eq_card,
      Nat.card_eq_fintype_card, div_eq_mul_inv]
  rw [hidx, ← Finset.sum_fiberwise Finset.univ (toCoset ι hc x), Finset.sum_filter]
  refine Finset.sum_congr rfl (fun c _ => ?_)
  rw [Finset.sum_const, nsmul_eq_mul]
  split_ifs with hcx
  · have hmem : Quotient.out c ∈ orbit G x := by
      have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' x := by
        rw [← toG_mk ι hc, Quotient.out_eq', hcx, hx, Quotient.out_eq']
      exact Quotient.exact' h1
    obtain ⟨b, hb⟩ := hmem
    have hy : (b⁻¹)⁻¹ • x = Quotient.out c := by rw [inv_inv]; exact hb
    have hfib : (Finset.univ.filter (fun ω => toCoset ι hc x ω = c)) =
        (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).toFinset := by
      ext ω
      induction ω using QuotientGroup.induction_on with
      | H g =>
        rw [Finset.mem_filter, Set.mem_toFinset, ← toCoset_eq_iff ι hc x b⁻¹ g, hy,
          Quotient.out_eq']
        simp
    have hcard := Subgroup.card_mul_index (stabilizer (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range))
    rw [index_stabilizer, card_stab ι hinj hc x b⁻¹, hy] at hcard
    rw [hfib, ← Set.ncard_eq_toFinset_card']
    have hm0 : Nat.card (stabilizer H (Quotient.out c)) ≠ 0 := by
      intro h0; rw [h0, zero_mul] at hcard; omega
    have hn0 : (orbit (stabilizer G x) ((b⁻¹ : G) : G ⧸ ι.range)).ncard ≠ 0 := by
      intro h0; rw [h0, mul_zero] at hcard; omega
    rw [← hcard]
    push_cast
    field_simp
  · rw [Finset.card_eq_zero.mpr, Nat.cast_zero, zero_mul]
    rw [Finset.filter_eq_empty_iff]
    intro ω _ hω
    apply hcx
    rw [← hω]
    induction ω using QuotientGroup.induction_on with
    | H g =>
      rw [toCoset_mk, toG_mk, hx]
      conv_rhs => rw [← Quotient.out_eq' c']
      exact Quotient.sound' ⟨g⁻¹, rfl⟩

/- English proof (translation)
Introduce `G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf`. Rewrite using `[← Finset.sum_fiberwise Finset.univ (toG ι hc) (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)), Finset.mul_sum]`. Use `Finset.sum_congr rfl (fun c' _ => ?_)` and prove the remaining obligations. Establish `hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'), ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c')`. Introduce `c hc'`.

Rewrite `hc'` using `[Finset.mem_filter]`. Establish `h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c')`. Rewrite using `[← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']`. Take `⟨g, hg⟩` from `(Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))`. Rewrite using `[← hg]`.

Express the relevant statement in the definitionally equal form `_ * f (g • Quotient.out c') = _`. Rewrite using `[hf]`. Use `haveI := hfin (Quotient.out c')`. Rewrite using `[Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]`.
-/
theorem mass_formula : ∀ {G H D : Type} [Group G] [Group H] [MulAction G D] [MulAction H D] (ι : H →* G), Function.Injective ι → (∀ (h : H) (d : D), ι h • d = h • d) → ι.range.FiniteIndex → (∀ d : D, Finite (MulAction.stabilizer G d)) → ∀ [Fintype (MulAction.orbitRel.Quotient G D)] [Fintype (MulAction.orbitRel.Quotient H D)] (f : D → ℂ), (∀ (g : G) (d : D), f (g • d) = f d) → ∑ c : MulAction.orbitRel.Quotient H D, ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) = (ι.range.index : ℂ) * ∑ c : MulAction.orbitRel.Quotient G D, ((Nat.card (MulAction.stabilizer G (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) := by
  intro G H D _ _ _ _ ι hinj hc hfi hfin _ _ f hf
  classical
  rw [← Finset.sum_fiberwise Finset.univ (toG ι hc)
    (fun c => ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c)),
    Finset.mul_sum]
  refine Finset.sum_congr rfl (fun c' _ => ?_)
  have hconst : ∀ c ∈ Finset.univ.filter (fun c => toG ι hc c = c'),
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c) =
      ((Nat.card (MulAction.stabilizer H (Quotient.out c)) : ℂ))⁻¹ * f (Quotient.out c') := by
    intro c hc'
    rw [Finset.mem_filter] at hc'
    have h1 : (Quotient.mk'' (Quotient.out c) : orbitRel.Quotient G D) = Quotient.mk'' (Quotient.out c') := by
      rw [← toG_mk ι hc, Quotient.out_eq', hc'.2, Quotient.out_eq']
    obtain ⟨g, hg⟩ := (Quotient.exact' h1 : Quotient.out c ∈ orbit G (Quotient.out c'))
    rw [← hg]
    change _ * f (g • Quotient.out c') = _
    rw [hf]
  haveI := hfin (Quotient.out c')
  rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, sum_fiber ι hinj hc c', div_eq_mul_inv, mul_assoc]

end GlobalTheory.OrbitMass
