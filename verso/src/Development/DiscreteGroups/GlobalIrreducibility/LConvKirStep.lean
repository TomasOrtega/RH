import Mathlib
import Development.DiscreteGroups.GlobalIrreducibility.LConvKirC

noncomputable section
set_option linter.unusedSimpArgs false
set_option linter.unusedSectionVars false
set_option linter.style.longLine false
open Matrix GlobalTheory.SmGL GlobalTheory.Whittaker GlobalTheory.LocLanglands GlobalTheory.PRep ValuativeRel

namespace DiscreteGroups.sglob.LConvKir

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by`. Assume the negation of the conclusion as `h`. Conclude with `hψ (AddChar.ext _ _ fun x => by rw [not_exists_not.1 h x, AddChar.one_apply])`. Use `set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc`. Use `set jj : Fin (m + 1) := ⟨j, by omega⟩ with hjj`.

Establish `hjc : jj < c` using `Fin.mk_lt_mk.2 (Nat.lt_succ_self j)`. Take `⟨γ₁, hγ₁⟩` from `kappa_nbhd {g | ρ g v = v} (hsm v) (by simp) jj`. Take `⟨γ₀, hγ₀⟩` from `psi_ball ψ hψc`. Set `r₁ : ValueGroupWithZero k` to `valuation k y * ↑γ₁⁻¹`. Set `L : AddSubgroup (Fin (m + 1) → k)` to `AddSubgroup.pi Set.univ fun _ => ballLe r₁`.

Set `Sx : AddSubgroup (Fin (m + 1) → k)` to `{ carrier := {x | ρ (U c x) v = v} add_mem' := by`. Introduce `a b (ha : ρ (U c a) v = v) (hb : ρ (U c b) v = v)`. Use `show ρ (U c (a + b)) v = v`. Rewrite using `[U_add, map_mul, Module.End.mul_apply, hb, ha]`. Use the proof step `zero_mem' := by show ρ (U c 0) v = v`.

Rewrite using `[U_zero, map_one, Module.End.one_apply]`. Use the proof step `neg_mem' := by`. Introduce `a (ha : ρ (U c a) v = v)`. Use `show ρ (U c (-a)) v = v`. Use `conv_lhs => rw [← ha]`.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← U_add, neg_add_cancel, U_zero, map_one, Module.End.one_apply] }`. Set `L'' : AddSubgroup (Fin (m + 1) → k)` to `Sx ⊓ AddSubgroup.pi Set.univ fun _ => ballLt γ₀`. Establish `hLc : IsCompact (L : Set (Fin (m + 1) → k))` using `isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k r₁`. Establish `: CompactSpace L` using `isCompact_iff_compactSpace.1 hLc`. Establish `hL''o : IsOpen (L'' : Set (Fin (m + 1) → k))` using `((hsm v).preimage (continuous_U c)).inter (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ballLt γ₀)`.

Establish `hQf : Finite (L ⧸ L''.addSubgroupOf L)` using `AddSubgroup.quotient_finite_of_isOpen _ (hL''o.preimage continuous_subtype_val)`. Set `_ : Fintype (L ⧸ L''.addSubgroupOf L)` to `Fintype.ofFinite _`. Set `xs : (L ⧸ L''.addSubgroupOf L) → Fin (m + 1) → k` to `fun q => ((Quotient.out q : L) : Fin (m + 1) → k)`. Establish `hN : (Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 Fintype.card_ne_zero`. Use `⟨(Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ)⁻¹ • ∑ q : L ⧸ L''.addSubgroupOf L, ((ψ (-(xs q jj)) : Circle) : ℂ) • ρ (U c (xs q)) v, fun l hl => ⟨?_, fun hv g hg => ?_⟩⟩` and prove the remaining obligations.

Simplify using `only [map_smul, map_sum, smul_eq_mul]`. Establish `hq : ∀ q, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ (U c (xs q)) v) = l v` using `fun q => by`. Rewrite using `[hl _ (U_mem _ _), superDiag_U, ← mul_assoc, psi_neg_mul, one_mul]`. Rewrite using `[Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc, inv_mul_cancel₀ hN, one_mul]`. Simplify using `only [map_smul, map_sum, smul_eq_mul]`.

Set `w : Fin (m + 1) → k` to `fun r => if r < c then (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r else 0`. Set `χ : (Fin (m + 1) → k) → ℂ` to `fun x => ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)`. Establish `hterm : ∀ x, ((ψ (-(x jj)) : Circle) : ℂ) * l (ρ g (ρ (U c x) v)) = χ x * l (ρ g v)` using `fun x => by`. Rewrite using `[l_gU ψ ρ l hl j hj g hg x v]`. Conclude with `(mul_assoc _ _ _).symm`.

Rewrite using `[mul_eq_zero]`. Use `right`. Establish `hS : (∑ q : L ⧸ L''.addSubgroupOf L, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ g (ρ (U c (xs q)) v))) = (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) * l (ρ g v)`. Rewrite using `[Finset.sum_mul]`. Conclude with `Finset.sum_congr rfl fun q _ => hterm (xs q)`.

Use `hS.trans ?_` and prove the remaining obligations. Distinguish the cases in `h0 : l (ρ g v) = 0`. Rewrite using `[h0, mul_zero]`. Establish `hχadd : ∀ x x', χ (x + x') = χ x * χ x'` using `fun x x' => by show ((ψ (-((x + x') jj)) : Circle) : ℂ) * (ψ (∑ r, w r * (x + x') r) : ℂ) = (((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)) * (((ψ (-(x' jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x' r) : ℂ))`. Establish `hs : ∑ r, w r * (x + x') r = ∑ r, w r * x r + ∑ r, w r * x' r`.

Rewrite using `[← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, mul_add]`. Rewrite using `[Pi.add_apply, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hs, AddChar.map_add_eq_mul, Circle.coe_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `hχ'' : ∀ x ∈ L'', χ x = 1`. Introduce `x hx`.

Establish `hx1 : ρ (U c x) v = v` using `(AddSubgroup.mem_inf.1 hx).1`. Establish `hx2 : valuation k (x jj) < γ₀` using `(AddSubgroup.mem_pi _).1 (AddSubgroup.mem_inf.1 hx).2 jj (Set.mem_univ _)`. Establish `e1 : ψ (-(x jj)) = 1` using `hγ₀ _ (by rwa [Valuation.map_neg])`. Establish `e2 : (ψ (∑ r, w r * x r) : ℂ) = 1`. Use `l_gU ψ ρ l hl j hj g hg x v` as an intermediate fact.

Rewrite `this` using `[hx1]`. Conclude with `(mul_eq_right₀ h0).1 this.symm`. Use `show ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ) = 1`. Rewrite using `[e1, Circle.coe_one, one_mul, e2]`. Distinguish the cases in `hall : ∀ x ∈ L, χ x = 1`.

It suffices to derive a contradiction. Apply `h0` to reduce the goal to its premises. Establish `hsmall : ∀ i, valuation k (w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ₁`. Introduce `i`. Use `small_of_triv ψ y hy γ₁ _ fun t ht => ?_` and prove the remaining obligations.

Establish `hxL : (Pi.single i t : Fin (m + 1) → k) ∈ L`. Use `(AddSubgroup.mem_pi _).2 fun r _ => ?_` and prove the remaining obligations. Distinguish the cases in `hr : r = i`. Rewrite using `[hr] show valuation k ((Pi.single i t : Fin (m + 1) → k) i) ≤ r₁`. Rewrite using `[Pi.single_eq_same]`.

Conclude with `ht`. Use `show valuation k ((Pi.single i t : Fin (m + 1) → k) r) ≤ r₁`. Rewrite using `[Pi.single_eq_of_ne hr, map_zero]`. Conclude with `zero_le`. Establish `h3 : ((ψ (-((Pi.single i t : Fin (m + 1) → k) jj)) : Circle) : ℂ) * (ψ (∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r) : ℂ) = 1` using `hall _ hxL`.

Establish `hs : ∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r = w i * t`. Rewrite using `[Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, mul_zero]) (by simp), Pi.single_eq_same]`. Establish `hsj : (Pi.single i t : Fin (m + 1) → k) jj = (Pi.single jj (1 : k) : Fin (m + 1) → k) i * t`. Distinguish the cases in `h : i = jj`. Rewrite using `[h, Pi.single_eq_same, Pi.single_eq_same, one_mul]`.

Rewrite using `[Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne h, zero_mul]`. Establish `h4 : ((ψ ((w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) * t) : Circle) : ℂ) = 1`. Rewrite using `[sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← hs, ← hsj]`. Conclude with `h3`. Conclude with `Circle.coe_eq_one.1 h4`.

Take `⟨κ, hκS, hκ, hκi⟩` from `hγ₁ w hsmall`. Establish `hgrow : ∀ r, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r = w r` using `fun r => by`. Distinguish the cases in `hr : r < c`. Simplify using `only [w, if_pos hr]`. Simplify using `only [w, if_neg hr]`.

Rewrite using `[hg jj r (fun h => hr (by rw [Fin.lt_def]; exact h.2)), Matrix.one_apply_ne (fun h => hr (by rw [← h]; exact hjc))]`. Establish `hMrow : ∀ q, ((g * κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q`. Introduce `q`. Establish `hk1 : Kmat jj w * Kinv jj w = 1`. Rewrite using `[← hκ, ← hκi, ← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Rewrite using `[Units.val_mul, hκi, Matrix.mul_apply, ← hk1, Matrix.mul_apply]`. Use `Finset.sum_congr rfl fun r _ => ?_` and prove the remaining obligations. Rewrite using `[hgrow r]`. Simplify using `only [Kmat, Matrix.of_apply, ↓reduceIte]`. Establish `hMH : InH (j + 1) (g * κ⁻¹)`.

Introduce `p q hpq`. Rewrite using `[Units.val_mul, hκi, Matrix.mul_apply]`. Distinguish the cases in `hp : p < c`. Establish `hq : ¬ q < c` using `fun hq => hpq ⟨hp, hq⟩`. Establish `hK : ∀ r, Kinv jj w r q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q` using `fun r => by`.

Distinguish the cases in `hr : r = jj`. Rewrite using `[hr]`. Simplify using `only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]`. Rewrite using `[if_neg (fun h => hq (by rw [h]; exact hjc)), show w q = 0 from if_neg hq, neg_zero, zero_mul, Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hjc))]`. Simplify using `only [Kinv, Kinv2, Matrix.of_apply, if_neg hr]`.

Rewrite using `[Finset.sum_congr rfl fun r _ => by rw [hK r], ← Matrix.mul_apply, Matrix.mul_one]`. Conclude with `hg p q hpq`. Rewrite using `[Finset.sum_eq_single p (fun r _ hr => by`. Rewrite using `[hg p r (fun h => hp h.1), Matrix.one_apply_ne (Ne.symm hr), zero_mul]) (by simp),`. Use `hg p p (fun h => hp h.1), Matrix.one_apply_eq, one_mul]`.

Simplify using `only [Kinv, Kinv2, Matrix.of_apply, if_neg (fun h : p = jj => hp (by rw [h]; exact hjc))]`. Take `⟨yv, h, hh, hM⟩` from `decomp j (by omega) (g * κ⁻¹) hMH hMrow`. Establish `hki : ρ κ⁻¹ v = v` using `by conv_lhs => rw [← (hκS : ρ κ v = v)]`. Rewrite using `[← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]`. Establish `e1 : ρ g v = ρ (g * κ⁻¹) v` using `by rw [map_mul, Module.End.mul_apply, hki]`.

Rewrite using `[e1, hM, map_mul, Module.End.mul_apply, hl _ (U_mem _ _), hv h hh, mul_zero]`. Use `push Not at hall`. Take `⟨x₀, hx₀L, hx₀⟩` from `hall`. Establish `hsum` using `sum_char_eq_zero L L'' χ hχadd hχ'' ⟨x₀, hx₀L⟩ hx₀`. Rewrite using `[show (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) = 0 from hsum, zero_mul]`.
-/
theorem step (ψ : AddChar k Circle) (hψc : Continuous ψ) (hψ : ψ ≠ 1) {m : ℕ} {V : Type} [AddCommGroup V]
    [Module ℂ V] (ρ : Representation ℂ (GL (Fin (m + 1)) k) V) (hsm : IsSmooth ρ) (j : ℕ) (hj : j + 1 < m + 1)
    (v : V) : ∃ v' : V, ∀ l : Module.Dual ℂ V, IsFunctional ψ ρ l → l v' = l v ∧
      ((∀ h, InH j h → l (ρ h v) = 0) → ∀ g, InH (j + 1) g → l (ρ g v') = 0) := by
  classical
  obtain ⟨y, hy⟩ : ∃ y, ψ y ≠ 1 := by
    by_contra h
    exact hψ (AddChar.ext _ _ fun x => by rw [not_exists_not.1 h x, AddChar.one_apply])
  set c : Fin (m + 1) := ⟨j + 1, hj⟩ with hc
  set jj : Fin (m + 1) := ⟨j, by omega⟩ with hjj
  have hjc : jj < c := Fin.mk_lt_mk.2 (Nat.lt_succ_self j)
  obtain ⟨γ₁, hγ₁⟩ := kappa_nbhd {g | ρ g v = v} (hsm v) (by simp) jj
  obtain ⟨γ₀, hγ₀⟩ := psi_ball ψ hψc
  let r₁ : ValueGroupWithZero k := valuation k y * ↑γ₁⁻¹
  let L : AddSubgroup (Fin (m + 1) → k) := AddSubgroup.pi Set.univ fun _ => ballLe r₁
  let Sx : AddSubgroup (Fin (m + 1) → k) :=
    { carrier := {x | ρ (U c x) v = v}
      add_mem' := by
        intro a b (ha : ρ (U c a) v = v) (hb : ρ (U c b) v = v)
        show ρ (U c (a + b)) v = v
        rw [U_add, map_mul, Module.End.mul_apply, hb, ha]
      zero_mem' := by
        show ρ (U c 0) v = v
        rw [U_zero, map_one, Module.End.one_apply]
      neg_mem' := by
        intro a (ha : ρ (U c a) v = v)
        show ρ (U c (-a)) v = v
        conv_lhs => rw [← ha]
        rw [← Module.End.mul_apply, ← map_mul, ← U_add, neg_add_cancel, U_zero, map_one, Module.End.one_apply] }
  let L'' : AddSubgroup (Fin (m + 1) → k) := Sx ⊓ AddSubgroup.pi Set.univ fun _ => ballLt γ₀
  have hLc : IsCompact (L : Set (Fin (m + 1) → k)) :=
    isCompact_univ_pi fun _ => IsNonarchimedeanLocalField.isCompact_closedBall k r₁
  have : CompactSpace L := isCompact_iff_compactSpace.1 hLc
  have hL''o : IsOpen (L'' : Set (Fin (m + 1) → k)) :=
    ((hsm v).preimage (continuous_U c)).inter (isOpen_set_pi Set.finite_univ fun _ _ => isOpen_ballLt γ₀)
  have hQf : Finite (L ⧸ L''.addSubgroupOf L) :=
    AddSubgroup.quotient_finite_of_isOpen _ (hL''o.preimage continuous_subtype_val)
  let _ : Fintype (L ⧸ L''.addSubgroupOf L) := Fintype.ofFinite _
  let xs : (L ⧸ L''.addSubgroupOf L) → Fin (m + 1) → k := fun q => ((Quotient.out q : L) : Fin (m + 1) → k)
  have hN : (Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ) ≠ 0 := Nat.cast_ne_zero.2 Fintype.card_ne_zero
  refine ⟨(Fintype.card (L ⧸ L''.addSubgroupOf L) : ℂ)⁻¹ • ∑ q : L ⧸ L''.addSubgroupOf L,
    ((ψ (-(xs q jj)) : Circle) : ℂ) • ρ (U c (xs q)) v, fun l hl => ⟨?_, fun hv g hg => ?_⟩⟩
  · simp only [map_smul, map_sum, smul_eq_mul]
    have hq : ∀ q, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ (U c (xs q)) v) = l v := fun q => by
      rw [hl _ (U_mem _ _), superDiag_U, ← mul_assoc, psi_neg_mul, one_mul]
    rw [Finset.sum_congr rfl fun q _ => hq q, Finset.sum_const, Finset.card_univ, nsmul_eq_mul, ← mul_assoc,
      inv_mul_cancel₀ hN, one_mul]
  · simp only [map_smul, map_sum, smul_eq_mul]
    let w : Fin (m + 1) → k := fun r => if r < c then (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r else 0
    let χ : (Fin (m + 1) → k) → ℂ := fun x => ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)
    have hterm : ∀ x, ((ψ (-(x jj)) : Circle) : ℂ) * l (ρ g (ρ (U c x) v)) = χ x * l (ρ g v) := fun x => by
      rw [l_gU ψ ρ l hl j hj g hg x v]; exact (mul_assoc _ _ _).symm
    rw [mul_eq_zero]; right
    have hS : (∑ q : L ⧸ L''.addSubgroupOf L, ((ψ (-(xs q jj)) : Circle) : ℂ) * l (ρ g (ρ (U c (xs q)) v))) =
        (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) * l (ρ g v) := by
      rw [Finset.sum_mul]; exact Finset.sum_congr rfl fun q _ => hterm (xs q)
    refine hS.trans ?_
    by_cases h0 : l (ρ g v) = 0
    · rw [h0, mul_zero]
    have hχadd : ∀ x x', χ (x + x') = χ x * χ x' := fun x x' => by
      show ((ψ (-((x + x') jj)) : Circle) : ℂ) * (ψ (∑ r, w r * (x + x') r) : ℂ) =
        (((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ)) *
          (((ψ (-(x' jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x' r) : ℂ))
      have hs : ∑ r, w r * (x + x') r = ∑ r, w r * x r + ∑ r, w r * x' r := by
        rw [← Finset.sum_add_distrib]; exact Finset.sum_congr rfl fun r _ => by rw [Pi.add_apply, mul_add]
      rw [Pi.add_apply, neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, hs, AddChar.map_add_eq_mul, Circle.coe_mul]
      ring
    have hχ'' : ∀ x ∈ L'', χ x = 1 := by
      intro x hx
      have hx1 : ρ (U c x) v = v := (AddSubgroup.mem_inf.1 hx).1
      have hx2 : valuation k (x jj) < γ₀ := (AddSubgroup.mem_pi _).1 (AddSubgroup.mem_inf.1 hx).2 jj (Set.mem_univ _)
      have e1 : ψ (-(x jj)) = 1 := hγ₀ _ (by rwa [Valuation.map_neg])
      have e2 : (ψ (∑ r, w r * x r) : ℂ) = 1 := by
        have := l_gU ψ ρ l hl j hj g hg x v
        rw [hx1] at this
        exact (mul_eq_right₀ h0).1 this.symm
      show ((ψ (-(x jj)) : Circle) : ℂ) * (ψ (∑ r, w r * x r) : ℂ) = 1
      rw [e1, Circle.coe_one, one_mul, e2]
    by_cases hall : ∀ x ∈ L, χ x = 1
    · exfalso
      apply h0
      have hsmall : ∀ i, valuation k (w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) < γ₁ := by
        intro i
        refine small_of_triv ψ y hy γ₁ _ fun t ht => ?_
        have hxL : (Pi.single i t : Fin (m + 1) → k) ∈ L := by
          refine (AddSubgroup.mem_pi _).2 fun r _ => ?_
          by_cases hr : r = i
          · rw [hr]
            show valuation k ((Pi.single i t : Fin (m + 1) → k) i) ≤ r₁
            rw [Pi.single_eq_same]; exact ht
          · show valuation k ((Pi.single i t : Fin (m + 1) → k) r) ≤ r₁
            rw [Pi.single_eq_of_ne hr, map_zero]; exact zero_le
        have h3 : ((ψ (-((Pi.single i t : Fin (m + 1) → k) jj)) : Circle) : ℂ) *
            (ψ (∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r) : ℂ) = 1 := hall _ hxL
        have hs : ∑ r, w r * (Pi.single i t : Fin (m + 1) → k) r = w i * t := by
          rw [Finset.sum_eq_single i (fun r _ hr => by rw [Pi.single_eq_of_ne hr, mul_zero]) (by simp),
            Pi.single_eq_same]
        have hsj : (Pi.single i t : Fin (m + 1) → k) jj = (Pi.single jj (1 : k) : Fin (m + 1) → k) i * t := by
          by_cases h : i = jj
          · rw [h, Pi.single_eq_same, Pi.single_eq_same, one_mul]
          · rw [Pi.single_eq_of_ne (Ne.symm h), Pi.single_eq_of_ne h, zero_mul]
        have h4 : ((ψ ((w i - (Pi.single jj (1 : k) : Fin (m + 1) → k) i) * t) : Circle) : ℂ) = 1 := by
          rw [sub_mul, sub_eq_neg_add, AddChar.map_add_eq_mul, Circle.coe_mul, ← hs, ← hsj]
          exact h3
        exact Circle.coe_eq_one.1 h4
      obtain ⟨κ, hκS, hκ, hκi⟩ := hγ₁ w hsmall
      have hgrow : ∀ r, (g : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj r = w r := fun r => by
        by_cases hr : r < c
        · simp only [w, if_pos hr]
        · simp only [w, if_neg hr]
          rw [hg jj r (fun h => hr (by rw [Fin.lt_def]; exact h.2)),
            Matrix.one_apply_ne (fun h => hr (by rw [← h]; exact hjc))]
      have hMrow : ∀ q, ((g * κ⁻¹ : GL (Fin (m + 1)) k) : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q =
          (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) jj q := by
        intro q
        have hk1 : Kmat jj w * Kinv jj w = 1 := by
          rw [← hκ, ← hκi, ← Units.val_mul, mul_inv_cancel, Units.val_one]
        rw [Units.val_mul, hκi, Matrix.mul_apply, ← hk1, Matrix.mul_apply]
        refine Finset.sum_congr rfl fun r _ => ?_
        rw [hgrow r]
        simp only [Kmat, Matrix.of_apply, ↓reduceIte]
      have hMH : InH (j + 1) (g * κ⁻¹) := by
        intro p q hpq
        rw [Units.val_mul, hκi, Matrix.mul_apply]
        by_cases hp : p < c
        · have hq : ¬ q < c := fun hq => hpq ⟨hp, hq⟩
          have hK : ∀ r, Kinv jj w r q = (1 : Matrix (Fin (m + 1)) (Fin (m + 1)) k) r q := fun r => by
            by_cases hr : r = jj
            · rw [hr]
              simp only [Kinv, Kinv2, Matrix.of_apply, ↓reduceIte]
              rw [if_neg (fun h => hq (by rw [h]; exact hjc)), show w q = 0 from if_neg hq, neg_zero, zero_mul,
                Matrix.one_apply_ne (fun h => hq (by rw [← h]; exact hjc))]
            · simp only [Kinv, Kinv2, Matrix.of_apply, if_neg hr]
          rw [Finset.sum_congr rfl fun r _ => by rw [hK r], ← Matrix.mul_apply, Matrix.mul_one]
          exact hg p q hpq
        · rw [Finset.sum_eq_single p (fun r _ hr => by
              rw [hg p r (fun h => hp h.1), Matrix.one_apply_ne (Ne.symm hr), zero_mul]) (by simp),
            hg p p (fun h => hp h.1), Matrix.one_apply_eq, one_mul]
          simp only [Kinv, Kinv2, Matrix.of_apply, if_neg (fun h : p = jj => hp (by rw [h]; exact hjc))]
      obtain ⟨yv, h, hh, hM⟩ := decomp j (by omega) (g * κ⁻¹) hMH hMrow
      have hki : ρ κ⁻¹ v = v := by
        conv_lhs => rw [← (hκS : ρ κ v = v)]
        rw [← Module.End.mul_apply, ← map_mul, inv_mul_cancel, map_one, Module.End.one_apply]
      have e1 : ρ g v = ρ (g * κ⁻¹) v := by rw [map_mul, Module.End.mul_apply, hki]
      rw [e1, hM, map_mul, Module.End.mul_apply, hl _ (U_mem _ _), hv h hh, mul_zero]
    · push Not at hall
      obtain ⟨x₀, hx₀L, hx₀⟩ := hall
      have hsum := sum_char_eq_zero L L'' χ hχadd hχ'' ⟨x₀, hx₀L⟩ hx₀
      rw [show (∑ q : L ⧸ L''.addSubgroupOf L, χ (xs q)) = 0 from hsum, zero_mul]

end DiscreteGroups.sglob.LConvKir
