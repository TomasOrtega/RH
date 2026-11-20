import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.PointSide
open GlobalTheory.LKCount

namespace GlobalTheory

/- English proof (translation)
Establish `memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L`. Introduce `L a x`. Rewrite using `[Subgroup.mem_map_equiv]`. Simplify using `[MulAut.conj_symm_apply]`. Establish `memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L`.

Introduce `L a x`. Rewrite using `[Subgroup.mem_map_equiv]`. Simplify using `[MulAut.conj_symm_apply]`. Use `set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC`. Use `set A : Subgroup T := Γ'.subgroupOf T`.

Use `set B : Subgroup T := C.subgroupOf T`. Set `φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G)` to `fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)`. Establish `hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}`. Introduce `q`. Use `show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0`.

Take `⟨h, k, hh, hk, he⟩` from `DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)`. Rewrite using `[he, hF h (hΓT hh) _ k hk]`. Use `hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem` as an intermediate fact. Rewrite `this` using `[mul_one]`. Rewrite using `[this]`.

Conclude with `hy`. Establish `hφinj : Function.Injective φ`. Introduce `q1 q2 h12`. Rewrite using `[← DoubleCoset.out_eq' A B q1, ← DoubleCoset.out_eq' A B q2]`. Take `⟨g, hg, k, hk, he⟩` from `(DoubleCoset.eq Γ' K _ _).1 h12`.

Use `set t1 : T := Quotient.out q1`. Use `set t2 : T := Quotient.out q2`. Establish `hgT : g ∈ T` using `hΓT hg`. Establish `hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G)`. Establish `ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹` using `by rw [← he]; group`.

Rewrite using `[ht2]`. Use `group`. Establish `hsT : y * k * y⁻¹ ∈ T`. Rewrite using `[hs]`. Conclude with `T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2`.

Establish `hsC : y * k * y⁻¹ ∈ C`. Use `⟨hsT, (memconj K y _).2 ?_⟩` and prove the remaining obligations. Simplify `hk` using `[mul_assoc]`. Rewrite using `[DoubleCoset.eq]`. Use `⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩` and prove the remaining obligations.

Simplify `hg` using `[A, Subgroup.mem_subgroupOf]`. Simplify `hsC` using `[B, Subgroup.mem_subgroupOf]`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `only [Subgroup.coe_mul]`. Rewrite using `[hs]`.

Use `group`. Use `haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype`. Use `haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) := Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0})) (fun a b h => hφinj (congrArg Subtype.val h))`. Establish `hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T), 0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹`. Introduce `q`.

Use `set t : T := Quotient.out q`. Use `haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype`. Establish `hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom), ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom`. Introduce `x`. Establish `hx` using `x.2`.

Rewrite `hx` using `[Subgroup.mem_inf]`. Take `⟨hxA, hxB⟩` from `hx`. Rewrite `hxB` using `[memconjT]`. Establish `hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C` using `hxB`. Use `⟨hxA, (memconj K _ _).2 ?_⟩` and prove the remaining obligations.

Use `(memconj K y _).1 hxC.2` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Use `haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) := Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom))) (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')`. Conclude with `inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)`. Use `haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))`.

Unfold `massC`. Rewrite using `[finsum_eq_sum_of_fintype]`. Conclude with `ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)`.
-/
theorem massC_ne_zero_of_support {G : Type} [Group G] (Γ' T K : Subgroup G) (F : G → ℂ) (hΓT : Γ' ≤ T)
    (hF : ∀ t ∈ T, ∀ x, ∀ k ∈ K, F (t * x * k) = F x)
    (hfin : ∀ x : G, ((Γ' ⊓ K.map (MulAut.conj x).toMonoidHom : Subgroup G) : Set G).Finite)
    (hsupp : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}.Finite)
    (y : G) (hy : F y ≠ 0) :
    massC Γ' T (T ⊓ K.map (MulAut.conj y).toMonoidHom) ≠ 0 := by
  have memconj : ∀ (L : Subgroup G) (a x : G), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  have memconjT : ∀ (L : Subgroup T) (a x : T), x ∈ L.map (MulAut.conj a).toMonoidHom ↔ a⁻¹ * x * a ∈ L := by
    intro L a x
    rw [Subgroup.mem_map_equiv]
    simp [MulAut.conj_symm_apply]
  set C := T ⊓ K.map (MulAut.conj y).toMonoidHom with hC
  set A : Subgroup T := Γ'.subgroupOf T
  set B : Subgroup T := C.subgroupOf T

  let φ : DoubleCoset.Quotient (A : Set T) (B : Set T) → DoubleCoset.Quotient (Γ' : Set G) (K : Set G) :=
    fun q => DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y)
  have hφS : ∀ q, φ q ∈ {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := by
    intro q
    show F (Quotient.out (DoubleCoset.mk Γ' K (((Quotient.out q : T) : G) * y))) ≠ 0
    obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul Γ' K (((Quotient.out q : T) : G) * y)
    rw [he, hF h (hΓT hh) _ k hk]
    have := hF ((Quotient.out q : T) : G) (Quotient.out q).2 y 1 K.one_mem
    rw [mul_one] at this
    rw [this]; exact hy
  have hφinj : Function.Injective φ := by
    intro q1 q2 h12
    rw [← DoubleCoset.out_eq' A B q1, ← DoubleCoset.out_eq' A B q2]
    obtain ⟨g, hg, k, hk, he⟩ := (DoubleCoset.eq Γ' K _ _).1 h12
    set t1 : T := Quotient.out q1
    set t2 : T := Quotient.out q2
    have hgT : g ∈ T := hΓT hg
    have hs : y * k * y⁻¹ = ((t1 : G))⁻¹ * g⁻¹ * (t2 : G) := by
      have ht2 : (t2 : G) = g * ((t1 : G) * y) * k * y⁻¹ := by rw [← he]; group
      rw [ht2]; group
    have hsT : y * k * y⁻¹ ∈ T := by
      rw [hs]; exact T.mul_mem (T.mul_mem (T.inv_mem t1.2) (T.inv_mem hgT)) t2.2
    have hsC : y * k * y⁻¹ ∈ C := by
      refine ⟨hsT, (memconj K y _).2 ?_⟩
      simpa [mul_assoc] using hk
    rw [DoubleCoset.eq]
    refine ⟨⟨g, hgT⟩, ?_, ⟨y * k * y⁻¹, hsT⟩, ?_, ?_⟩
    · simpa [A, Subgroup.mem_subgroupOf] using hg
    · simpa [B, Subgroup.mem_subgroupOf] using hsC
    · apply Subtype.ext
      simp only [Subgroup.coe_mul]
      rw [hs]; group
  haveI : Finite {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0} := hsupp.to_subtype
  haveI hQ : Finite (DoubleCoset.Quotient (A : Set T) (B : Set T)) :=
    Finite.of_injective (fun q => (⟨φ q, hφS q⟩ : {q : DoubleCoset.Quotient (Γ' : Set G) (K : Set G) | F (Quotient.out q) ≠ 0}))
      (fun a b h => hφinj (congrArg Subtype.val h))

  have hpos : ∀ q : DoubleCoset.Quotient (A : Set T) (B : Set T),
      0 < ((Nat.card (A ⊓ B.map (MulAut.conj (Quotient.out q)).toMonoidHom : Subgroup T) : ℕ) : ℚ)⁻¹ := by
    intro q
    set t : T := Quotient.out q
    haveI : Finite ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom) := (hfin ((t : G) * y)).to_subtype
    have hmem : ∀ x : ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom),
        ((x : T) : G) ∈ Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom := by
      intro x
      have hx := x.2
      rw [Subgroup.mem_inf] at hx
      obtain ⟨hxA, hxB⟩ := hx
      rw [memconjT] at hxB
      have hxC : ((t⁻¹ * (x : T) * t : T) : G) ∈ C := hxB
      refine ⟨hxA, (memconj K _ _).2 ?_⟩
      have := (memconj K y _).1 hxC.2
      simpa [mul_assoc] using this
    haveI : Finite ↥(A ⊓ B.map (MulAut.conj t).toMonoidHom) :=
      Finite.of_injective (fun x => (⟨((x : T) : G), hmem x⟩ : ↥(Γ' ⊓ K.map (MulAut.conj ((t : G) * y)).toMonoidHom)))
        (by intro a b h; apply Subtype.ext; apply Subtype.ext; have h' := congrArg Subtype.val h; exact h')
    exact inv_pos.mpr (Nat.cast_pos.mpr Nat.card_pos)
  haveI := Fintype.ofFinite (DoubleCoset.Quotient (A : Set T) (B : Set T))
  unfold massC
  rw [finsum_eq_sum_of_fintype]
  exact ne_of_gt (Finset.sum_pos (fun q _ => hpos q) Finset.univ_nonempty)

end GlobalTheory
