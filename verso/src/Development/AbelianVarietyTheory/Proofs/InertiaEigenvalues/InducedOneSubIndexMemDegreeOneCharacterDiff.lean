import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IndApplyOne
open GlobalTheory.BI GlobalTheory.BrauerZero

namespace GlobalTheory.BrauerZero

/- English proof (translation)
Use `haveI := Fintype.ofFinite G`. Use `haveI hN : K.Normal := ⟨fun n hn g => by`. Establish `h1` using `hK g n`. Establish `: g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n` using `by group`. Rewrite using `[this]`.

Conclude with `K.mul_mem h1 hn⟩`. Use `letI : CommGroup (G ⧸ K) := { (inferInstance : Group (G ⧸ K)) with mul_comm := by`. Introduce `x y`. Proceed by induction on `x using QuotientGroup.induction_on with`. Consider the case `H a`.

Proceed by induction on `y using QuotientGroup.induction_on with`. Consider the case `H b`. Rewrite using `[← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]`. Use `hK b⁻¹ a⁻¹` as an intermediate fact. Establish `e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹` using `by group`.

Rewrite using `[e]`. Conclude with `this }`. Use `haveI : Fintype (G ⧸ K) := Fintype.ofFinite _`. Set `Q` to `Additive (G ⧸ K)`. Set `F : AddChar Q ℂ → G → ℂ` to `fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))`.

Establish `hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b`. Introduce `ψ a b`. Simplify using `only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]`. Establish `hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1`. Introduce `ψ`.

Simplify using `only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]`. Establish `hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G`. Introduce `ψ`. Set `f : G →* ℂ` to `{ toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }`. Set `χ : (⊤ : Subgroup G) →* ℂˣ` to `(MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype`.

Establish `hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g`. Introduce `g x`. Rewrite using `[hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]`. Establish `h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ`. Conclude with `(ind_top (F ψ) hcl : _)`.

Establish `h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ)` using `ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)`. Apply `AddSubgroup.subset_closure` to reduce the goal to its premises. Conclude with `⟨⊤, χ, by rw [h1, h2]⟩`. Establish `hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0`. Introduce `g`.

Establish `hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K)`. Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `hN.conj_mem _ h x` as an intermediate fact.

Establish `e : x * (x⁻¹ * g * x) * x⁻¹ = g` using `by group`. Rewrite `this` using `[e]`. Then use the resulting hypothesis. Introduce `h`. Use `hN.conj_mem _ h x⁻¹` as an intermediate fact. Establish `e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x` using `by group`.

Rewrite `this` using `[e]`. Then use the resulting hypothesis. Simplify using `only [ind, finsum_eq_sum_of_fintype, ext0]`. Establish `hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0`. Introduce `x`. Distinguish the cases in `hg : g ∈ K`.

Rewrite using `[dif_pos ((hconj x).2 hg), if_pos hg]`. Rewrite using `[dif_neg (fun h => hg ((hconj x).1 h)), if_neg hg]`. Rewrite using `[Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← Nat.card_eq_fintype_card, ← K.card_mul_index]`. Establish `: (Nat.card K : ℂ) ≠ 0` using `by exact_mod_cast (Nat.card_pos (α := K)).ne'`. Use `split_ifs`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Simplify using the standard rewrite rules. Establish `hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0`. Introduce `g`.

Use `AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))` as an intermediate fact. Simplify using `only [F]`. Rewrite using `[this]`. Establish `hc : (Fintype.card Q : ℂ) = (K.index : ℂ)`. Rewrite using `[Subgroup.index, ← Nat.card_eq_fintype_card]`.

Both sides reduce to the same expression. Establish `he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K`. Rewrite using `[ofMul_eq_zero, QuotientGroup.eq_one_iff]`. Distinguish the cases in `hg : g ∈ K`. Rewrite using `[if_pos (he.2 hg), if_pos hg, hc]`.

Rewrite using `[if_neg (fun h => hg (he.1 h)), if_neg hg]`. Establish `hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ)`. Rewrite using `[AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]`. Both sides reduce to the same expression. Establish `heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ))`.

Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply]`. Simplify using `only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, mul_one]`. Rewrite using `[hind g, hsum g, hcard]`. Rewrite using `[heq]`.

Conclude with `AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)`.
-/
theorem ind_one_sub_index_mem_D0 {G : Type} [Group G] [Finite G] (K : Subgroup G)
    (hK : ∀ a b : G, a * b * a⁻¹ * b⁻¹ ∈ K) :
    ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ)) ∈ D0 G := by
  classical
  haveI := Fintype.ofFinite G
  haveI hN : K.Normal := ⟨fun n hn g => by
    have h1 := hK g n
    have : g * n * g⁻¹ = (g * n * g⁻¹ * n⁻¹) * n := by group
    rw [this]; exact K.mul_mem h1 hn⟩
  letI : CommGroup (G ⧸ K) :=
    { (inferInstance : Group (G ⧸ K)) with
      mul_comm := by
        intro x y
        induction x using QuotientGroup.induction_on with
        | H a =>
        induction y using QuotientGroup.induction_on with
        | H b =>
          rw [← QuotientGroup.mk_mul, ← QuotientGroup.mk_mul, QuotientGroup.eq]
          have := hK b⁻¹ a⁻¹
          have e : (a * b)⁻¹ * (b * a) = b⁻¹ * a⁻¹ * b⁻¹⁻¹ * a⁻¹⁻¹ := by group
          rw [e]; exact this }
  haveI : Fintype (G ⧸ K) := Fintype.ofFinite _
  let Q := Additive (G ⧸ K)

  let F : AddChar Q ℂ → G → ℂ := fun ψ g => ψ (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
  have hFmul : ∀ ψ : AddChar Q ℂ, ∀ a b : G, F ψ (a * b) = F ψ a * F ψ b := by
    intro ψ a b
    simp only [F, QuotientGroup.mk_mul, ofMul_mul, AddChar.map_add_eq_mul]
  have hFone : ∀ ψ : AddChar Q ℂ, F ψ 1 = 1 := by
    intro ψ
    simp only [F, QuotientGroup.mk_one, ofMul_one, AddChar.map_zero_eq_one]

  have hgen : ∀ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) ∈ D0 G := by
    intro ψ
    let f : G →* ℂ := { toFun := F ψ, map_one' := hFone ψ, map_mul' := hFmul ψ }
    let χ : (⊤ : Subgroup G) →* ℂˣ := (MonoidHom.toHomUnits f).comp (⊤ : Subgroup G).subtype
    have hcl : ∀ g x : G, F ψ (x⁻¹ * g * x) = F ψ g := by
      intro g x
      rw [hFmul, hFmul, mul_comm (F ψ x⁻¹), mul_assoc, ← hFmul, inv_mul_cancel, hFone, mul_one]
    have h1 : ind (⊤ : Subgroup G) (fun h => (χ h : ℂ)) = F ψ := by
      exact (ind_top (F ψ) hcl : _)
    have h2 : ind (⊤ : Subgroup G) (fun _ => (1 : ℂ)) = fun _ => (1 : ℂ) :=
      ind_top (fun _ => (1 : ℂ)) (fun _ _ => rfl)
    apply AddSubgroup.subset_closure
    exact ⟨⊤, χ, by rw [h1, h2]⟩

  have hind : ∀ g : G, ind K (fun _ => (1 : ℂ)) g = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have hconj : ∀ x : G, (x⁻¹ * g * x ∈ K ↔ g ∈ K) := by
      intro x
      constructor
      · intro h
        have := hN.conj_mem _ h x
        have e : x * (x⁻¹ * g * x) * x⁻¹ = g := by group
        rwa [e] at this
      · intro h
        have := hN.conj_mem _ h x⁻¹
        have e : x⁻¹ * g * x⁻¹⁻¹ = x⁻¹ * g * x := by group
        rwa [e] at this
    simp only [ind, finsum_eq_sum_of_fintype, ext0]
    have hs : ∀ x : G, (if h : x⁻¹ * g * x ∈ K then (1 : ℂ) else 0) = if g ∈ K then 1 else 0 := by
      intro x
      by_cases hg : g ∈ K
      · rw [dif_pos ((hconj x).2 hg), if_pos hg]
      · rw [dif_neg (fun h => hg ((hconj x).1 h)), if_neg hg]
    rw [Finset.sum_congr rfl (fun x _ => hs x), Finset.sum_const, Finset.card_univ, nsmul_eq_mul,
      ← Nat.card_eq_fintype_card, ← K.card_mul_index]
    have : (Nat.card K : ℂ) ≠ 0 := by exact_mod_cast (Nat.card_pos (α := K)).ne'
    split_ifs
    · push_cast; field_simp
    · simp

  have hsum : ∀ g : G, (∑ ψ : AddChar Q ℂ, F ψ g) = if g ∈ K then (K.index : ℂ) else 0 := by
    intro g
    have := AddChar.sum_apply_eq_ite (α := Q) (Additive.ofMul (QuotientGroup.mk g : G ⧸ K))
    simp only [F]
    rw [this]
    have hc : (Fintype.card Q : ℂ) = (K.index : ℂ) := by
      rw [Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
    have he : (Additive.ofMul (QuotientGroup.mk g : G ⧸ K) = 0) ↔ g ∈ K := by
      rw [ofMul_eq_zero, QuotientGroup.eq_one_iff]
    by_cases hg : g ∈ K
    · rw [if_pos (he.2 hg), if_pos hg, hc]
    · rw [if_neg (fun h => hg (he.1 h)), if_neg hg]
  have hcard : (Fintype.card (AddChar Q ℂ) : ℂ) = (K.index : ℂ) := by
    rw [AddChar.card_eq, Subgroup.index, ← Nat.card_eq_fintype_card]; rfl
  have heq : ind K (fun _ => (1 : ℂ)) - (fun _ => (K.index : ℂ))
      = ∑ ψ : AddChar Q ℂ, (F ψ - fun _ => (1 : ℂ)) := by
    funext g
    rw [Finset.sum_apply]
    simp only [Pi.sub_apply, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
      nsmul_eq_mul, mul_one]
    rw [hind g, hsum g, hcard]
  rw [heq]
  exact AddSubgroup.sum_mem _ (fun ψ _ => hgen ψ)

end GlobalTheory.BrauerZero
