import Mathlib
import Formalism.GL3MeanSquares.GenusMeanAsymptotics.UnimodularClassRepresentatives.CardFiberMulCardRange

namespace Formalism.HermitianLattices.Ext.L3.SecondPropositionFree

open NormLifting

variable {A B : Type*} [CommRing A] [CommRing B] {σ : A →+* A} {τ : B →+* B} {π : A →+* B}

/- English proof (translation)
Establish `hIσ : ∀ a ∈ RingHom.ker π, σ a ∈ RingHom.ker π`. Introduce `a ha`. Rewrite `ha`, the goal using `[RingHom.mem_ker]`. Rewrite using `[hστ, ha, map_zero]`. Use `haveI : Finite B := Finite.of_surjective π hπ`.

Establish `hker : Nat.card (RingHom.ker π) = q ^ 2`. Establish `h1 : Nat.card A = Nat.card (RingHom.ker π) * Nat.card B`. Use `card_eq_mul_of_fibers π _ (fun b => ?_)` and prove the remaining obligations. Take `⟨a0, ha0⟩` from `hπ b`. Conclude with `Nat.card_congr { toFun := fun a => ⟨a.1 - a0, by rw [RingHom.mem_ker, map_sub, a.2, ha0, sub_self]⟩ invFun := fun k => ⟨k.1 + a0, by rw [map_add, RingHom.mem_ker.mp k.2, ha0, zero_add]⟩ left_inv := fun a => Subtype.ext (sub_add_cancel a.1 a0) right_inv := fun k => Subtype.ext (ad …`.

Establish `hB : 0 < Nat.card B` using `Nat.card_pos`. Rewrite `h1` using `[hq]`. Conclude with `(Nat.eq_of_mul_eq_mul_right hB h1).symm`. Establish `hq0 : 0 < q`. Establish `hk : 0 < Nat.card (RingHom.ker π)` using `Nat.card_pos`.

Rewrite `hk` using `[hker]`. Conclude with `Nat.pos_of_ne_zero (fun h => by simp [h] at hk)`. Establish `hfix : Nat.card (fixSub σ (RingHom.ker π)) = q`. Establish `h` using `card_fixSub_sq hσ hIσ he`. Rewrite `h` using `[hker]`.

Conclude with `Nat.pow_left_injective two_ne_zero h`. Establish `hrange : ∀ x0 : Fin M → A, p (fun i => π (x0 i)) → Nat.card (linPart σ (RingHom.ker π) x0).range = q`. Introduce `x0 hp`. Establish `hR : (linPart σ (RingHom.ker π) x0).range = fixSub σ (RingHom.ker π)`. Use extensionality with `w`.

Rewrite using `[AddMonoidHom.mem_range]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ, rfl⟩ show linPart σ (RingHom.ker π) x0 δ ∈ RingHom.ker π ∧ σ (linPart σ (RingHom.ker π) x0 δ) = linPart σ (RingHom.ker π) x0 δ`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[linPart_apply]`.

Use `Ideal.sum_mem _ fun i _ => Ideal.add_mem _ ?_ ?_` and prove the remaining obligations. Conclude with `Ideal.mul_mem_left _ _ (δ i).2`. Conclude with `Ideal.mul_mem_right _ _ (hIσ _ (δ i).2)`. Rewrite using `[linPart_apply, map_sum]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations.

Simplify using `only [map_add, map_mul, hσ]`. Expand and normalize the polynomial expressions, which then agree. Introduce `hw`. Conclude with `AddMonoidHom.mem_range.mp (hsurj x0 hp w hw)`. Rewrite using `[hR, hfix]`.

Establish `hnorm : ∀ x : Fin M → A, ∑ i, σ (x i) * x i = n → ∑ i, τ (π (x i)) * π (x i) = π n`. Introduce `x hx`. Rewrite using `[← hx, map_sum]`. Simplify using `only [map_mul, hστ]`. Use `card_eq_mul_of_fibers (fun x : {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} => (⟨fun i => π (x.1 i), x.2.1, hnorm x.1 x.2.2⟩ : {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n})) _ ?_` and prove the remaining obligations.

Introduce `y`. Use `choose x0 hx0 using fun i => hπ (y.1 i)`. Establish `hpx0 : p (fun i => π (x0 i))`. Establish `h : (fun i => π (x0 i)) = y.1` using `funext hx0`. Rewrite using `[h]`.

Conclude with `y.2.1`. Establish `hNx0 : π (∑ i, σ (x0 i) * x0 i) = π n`. Rewrite using `[map_sum]`. Simplify using `only [map_mul, hστ, hx0]`. Conclude with `y.2.2`.

Establish `ht : n - ∑ i, σ (x0 i) * x0 i ∈ fixSub σ (RingHom.ker π)` using `by show n - ∑ i, σ (x0 i) * x0 i ∈ RingHom.ker π ∧ σ (n - ∑ i, σ (x0 i) * x0 i) = n - ∑ i, σ (x0 i) * x0 i`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[RingHom.mem_ker, map_sub, hNx0, sub_self]`. Rewrite using `[map_sub, hn, map_sum]`. Use `congr 1`.

Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Simplify using `only [map_mul, hσ]`. Expand and normalize the polynomial expressions, which then agree. Establish `key : Nat.card {δ : Fin M → RingHom.ker π // linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i} = q ^ (2 * M - 1)`. Establish `hfib` using `card_fiber_mul_card_range (linPart σ (RingHom.ker π) x0) _ (hsurj x0 hpx0 _ ht)`.

Rewrite `hfib` using `[hrange x0 hpx0, Nat.card_fun, hker, Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin, ← pow_mul]`. Establish `hpow : q ^ (2 * M) = q ^ (2 * M - 1) * q`. Rewrite using `[← pow_succ]`. Use `congr 1`. Use linear arithmetic over natural numbers and integers.

Rewrite `hfib` using `[hpow]`. Conclude with `Nat.eq_of_mul_eq_mul_right hq0 hfib`. Establish `hfwd : ∀ x : Fin M → A, (∀ i, π (x i) = y.1 i) → ∀ i, x i - x0 i ∈ RingHom.ker π`. Introduce `x hx i`. Rewrite using `[RingHom.mem_ker, map_sub, hx, hx0, sub_self]`.

Establish `hexp : ∀ (x : Fin M → A) (hd : ∀ i, x i - x0 i ∈ RingHom.ker π), ∑ i, σ (x i) * x i = ∑ i, σ (x0 i) * x0 i + linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hd i⟩)`. Introduce `x hd`. Rewrite using `[linPart_apply, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Establish `h0 : σ (x i - x0 i) * (x i - x0 i) = 0` using `hsq _ _ (RingHom.mem_ker.mp (hIσ _ (hd i))) (RingHom.mem_ker.mp (hd i))`.

Simplify using `only`. Rewrite `h0`, the goal using `[map_sub]`. Take the linear combination `h0`. Establish `hLfwd : ∀ (x : Fin M → A) (hx : ∀ i, π (x i) = y.1 i), ∑ i, σ (x i) * x i = n → linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hfwd x hx i⟩) = n - ∑ i, σ (x0 i) * x0 i`. Introduce `x hx hN`.

Establish `h` using `hexp x (hfwd x hx)`. Rewrite `h` using `[hN]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree. Establish `hdmem : ∀ (δ : Fin M → RingHom.ker π) i, (x0 i + δ i) - x0 i ∈ RingHom.ker π`.

Introduce `δ i`. Rewrite using `[add_sub_cancel_left]`. Conclude with `(δ i).2`. Establish `hbinv : ∀ (δ : Fin M → RingHom.ker π) i, π (x0 i + δ i) = y.1 i`. Introduce `δ i`.

Rewrite using `[map_add, RingHom.mem_ker.mp (δ i).2, add_zero, hx0]`. Establish `hpinv : ∀ δ : Fin M → RingHom.ker π, p (fun i => π (x0 i + δ i))`. Introduce `δ`. Establish `h : (fun i => π (x0 i + δ i)) = y.1` using `funext (hbinv δ)`. Rewrite using `[h]`.

Conclude with `y.2.1`. Establish `hNinv : ∀ δ : Fin M → RingHom.ker π, linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i → ∑ i, σ (x0 i + δ i) * (x0 i + δ i) = n`. Introduce `δ hδ`. Establish `h` using `hexp (fun i => x0 i + δ i) (hdmem δ)`. Establish `hδ' : (fun i => (⟨(x0 i + δ i) - x0 i, hdmem δ i⟩ : RingHom.ker π)) = δ`.

Use function extensionality and compare the values at `i`. Conclude with `Subtype.ext (add_sub_cancel_left (x0 i) (δ i : A))`. Rewrite `h` using `[hδ', hδ]`. Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← key]`. Conclude with `Nat.card_congr { toFun := fun x => ⟨fun i => ⟨x.1.1 i - x0 i, hfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) i⟩, hLfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) x.1.2.2⟩ invFun := fun δ => ⟨⟨fun i => x0 i + δ.1 i, hpinv δ.1, hNinv δ.1 δ.2⟩, Subtype.ext ( …`.
-/
theorem card_lift_pred [Finite A] (hπ : Function.Surjective π) (hστ : ∀ a, π (σ a) = τ (π a))
    (hσ : ∀ a, σ (σ a) = a) (hsq : ∀ a b, π a = 0 → π b = 0 → a * b = 0) {θ e : A}
    (he : (θ - σ θ) * e = 1) {n : A} (hn : σ n = n) (q : ℕ)
    (hq : Nat.card A = q ^ 2 * Nat.card B) (M : ℕ) (hM : 1 ≤ M) (p : (Fin M → B) → Prop)
    (hsurj : ∀ y : Fin M → A, p (fun i => π (y i)) → ∀ w ∈ fixSub σ (RingHom.ker π),
      w ∈ (linPart σ (RingHom.ker π) y).range) :
    Nat.card {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =
      q ^ (2 * M - 1) * Nat.card {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n} := by
  classical
  have hIσ : ∀ a ∈ RingHom.ker π, σ a ∈ RingHom.ker π := by
    intro a ha
    rw [RingHom.mem_ker] at ha ⊢
    rw [hστ, ha, map_zero]
  haveI : Finite B := Finite.of_surjective π hπ

  have hker : Nat.card (RingHom.ker π) = q ^ 2 := by
    have h1 : Nat.card A = Nat.card (RingHom.ker π) * Nat.card B := by
      refine card_eq_mul_of_fibers π _ (fun b => ?_)
      obtain ⟨a0, ha0⟩ := hπ b
      exact Nat.card_congr
        { toFun := fun a => ⟨a.1 - a0, by rw [RingHom.mem_ker, map_sub, a.2, ha0, sub_self]⟩
          invFun := fun k => ⟨k.1 + a0, by rw [map_add, RingHom.mem_ker.mp k.2, ha0, zero_add]⟩
          left_inv := fun a => Subtype.ext (sub_add_cancel a.1 a0)
          right_inv := fun k => Subtype.ext (add_sub_cancel_right k.1 a0) }
    have hB : 0 < Nat.card B := Nat.card_pos
    rw [hq] at h1
    exact (Nat.eq_of_mul_eq_mul_right hB h1).symm
  have hq0 : 0 < q := by
    have hk : 0 < Nat.card (RingHom.ker π) := Nat.card_pos
    rw [hker] at hk
    exact Nat.pos_of_ne_zero (fun h => by simp [h] at hk)

  have hfix : Nat.card (fixSub σ (RingHom.ker π)) = q := by
    have h := card_fixSub_sq hσ hIσ he
    rw [hker] at h
    exact Nat.pow_left_injective two_ne_zero h

  have hrange : ∀ x0 : Fin M → A, p (fun i => π (x0 i)) →
      Nat.card (linPart σ (RingHom.ker π) x0).range = q := by
    intro x0 hp
    have hR : (linPart σ (RingHom.ker π) x0).range = fixSub σ (RingHom.ker π) := by
      ext w
      rw [AddMonoidHom.mem_range]
      constructor
      · rintro ⟨δ, rfl⟩
        show linPart σ (RingHom.ker π) x0 δ ∈ RingHom.ker π ∧
          σ (linPart σ (RingHom.ker π) x0 δ) = linPart σ (RingHom.ker π) x0 δ
        refine ⟨?_, ?_⟩
        · rw [linPart_apply]
          refine Ideal.sum_mem _ fun i _ => Ideal.add_mem _ ?_ ?_
          · exact Ideal.mul_mem_left _ _ (δ i).2
          · exact Ideal.mul_mem_right _ _ (hIσ _ (δ i).2)
        · rw [linPart_apply, map_sum]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [map_add, map_mul, hσ]
          ring
      · intro hw
        exact AddMonoidHom.mem_range.mp (hsurj x0 hp w hw)
    rw [hR, hfix]

  have hnorm : ∀ x : Fin M → A, ∑ i, σ (x i) * x i = n → ∑ i, τ (π (x i)) * π (x i) = π n := by
    intro x hx
    rw [← hx, map_sum]
    simp only [map_mul, hστ]
  refine card_eq_mul_of_fibers
    (fun x : {x : Fin M → A // p (fun i => π (x i)) ∧ ∑ i, σ (x i) * x i = n} =>
      (⟨fun i => π (x.1 i), x.2.1, hnorm x.1 x.2.2⟩ :
        {x : Fin M → B // p x ∧ ∑ i, τ (x i) * x i = π n})) _ ?_
  intro y
  choose x0 hx0 using fun i => hπ (y.1 i)
  have hpx0 : p (fun i => π (x0 i)) := by
    have h : (fun i => π (x0 i)) = y.1 := funext hx0
    rw [h]
    exact y.2.1
  have hNx0 : π (∑ i, σ (x0 i) * x0 i) = π n := by
    rw [map_sum]
    simp only [map_mul, hστ, hx0]
    exact y.2.2
  have ht : n - ∑ i, σ (x0 i) * x0 i ∈ fixSub σ (RingHom.ker π) := by
    show n - ∑ i, σ (x0 i) * x0 i ∈ RingHom.ker π ∧
      σ (n - ∑ i, σ (x0 i) * x0 i) = n - ∑ i, σ (x0 i) * x0 i
    refine ⟨?_, ?_⟩
    · rw [RingHom.mem_ker, map_sub, hNx0, sub_self]
    · rw [map_sub, hn, map_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [map_mul, hσ]
      ring

  have key : Nat.card {δ : Fin M → RingHom.ker π //
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i} = q ^ (2 * M - 1) := by
    have hfib := card_fiber_mul_card_range (linPart σ (RingHom.ker π) x0) _ (hsurj x0 hpx0 _ ht)
    rw [hrange x0 hpx0, Nat.card_fun, hker, Nat.card_eq_fintype_card (α := Fin M), Fintype.card_fin,
      ← pow_mul] at hfib
    have hpow : q ^ (2 * M) = q ^ (2 * M - 1) * q := by
      rw [← pow_succ]
      congr 1
      omega
    rw [hpow] at hfib
    exact Nat.eq_of_mul_eq_mul_right hq0 hfib

  have hfwd : ∀ x : Fin M → A, (∀ i, π (x i) = y.1 i) → ∀ i, x i - x0 i ∈ RingHom.ker π := by
    intro x hx i
    rw [RingHom.mem_ker, map_sub, hx, hx0, sub_self]
  have hexp : ∀ (x : Fin M → A) (hd : ∀ i, x i - x0 i ∈ RingHom.ker π),
      ∑ i, σ (x i) * x i = ∑ i, σ (x0 i) * x0 i +
        linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hd i⟩) := by
    intro x hd
    rw [linPart_apply, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h0 : σ (x i - x0 i) * (x i - x0 i) = 0 :=
      hsq _ _ (RingHom.mem_ker.mp (hIσ _ (hd i))) (RingHom.mem_ker.mp (hd i))
    dsimp only
    rw [map_sub] at h0 ⊢
    linear_combination h0
  have hLfwd : ∀ (x : Fin M → A) (hx : ∀ i, π (x i) = y.1 i), ∑ i, σ (x i) * x i = n →
      linPart σ (RingHom.ker π) x0 (fun i => ⟨x i - x0 i, hfwd x hx i⟩) =
        n - ∑ i, σ (x0 i) * x0 i := by
    intro x hx hN
    have h := hexp x (hfwd x hx)
    rw [hN] at h
    rw [h]
    ring
  have hdmem : ∀ (δ : Fin M → RingHom.ker π) i, (x0 i + δ i) - x0 i ∈ RingHom.ker π := by
    intro δ i
    rw [add_sub_cancel_left]
    exact (δ i).2
  have hbinv : ∀ (δ : Fin M → RingHom.ker π) i, π (x0 i + δ i) = y.1 i := by
    intro δ i
    rw [map_add, RingHom.mem_ker.mp (δ i).2, add_zero, hx0]
  have hpinv : ∀ δ : Fin M → RingHom.ker π, p (fun i => π (x0 i + δ i)) := by
    intro δ
    have h : (fun i => π (x0 i + δ i)) = y.1 := funext (hbinv δ)
    rw [h]
    exact y.2.1
  have hNinv : ∀ δ : Fin M → RingHom.ker π,
      linPart σ (RingHom.ker π) x0 δ = n - ∑ i, σ (x0 i) * x0 i →
        ∑ i, σ (x0 i + δ i) * (x0 i + δ i) = n := by
    intro δ hδ
    have h := hexp (fun i => x0 i + δ i) (hdmem δ)
    have hδ' : (fun i => (⟨(x0 i + δ i) - x0 i, hdmem δ i⟩ : RingHom.ker π)) = δ := by
      funext i
      exact Subtype.ext (add_sub_cancel_left (x0 i) (δ i : A))
    rw [hδ', hδ] at h
    rw [h]
    ring
  rw [← key]
  exact Nat.card_congr
    { toFun := fun x => ⟨fun i => ⟨x.1.1 i - x0 i,
          hfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) i⟩,
        hLfwd x.1.1 (fun j => congrFun (congrArg Subtype.val x.2) j) x.1.2.2⟩
      invFun := fun δ => ⟨⟨fun i => x0 i + δ.1 i, hpinv δ.1, hNinv δ.1 δ.2⟩,
        Subtype.ext (funext fun i => hbinv δ.1 i)⟩
      left_inv := fun x => Subtype.ext (Subtype.ext (funext fun i =>
        show x0 i + (x.1.1 i - x0 i) = x.1.1 i by ring))
      right_inv := fun δ => Subtype.ext (funext fun i => Subtype.ext
        (show x0 i + (δ.1 i : A) - x0 i = (δ.1 i : A) by ring)) }

/- English proof (translation)
Establish `hw' : w ∈ I ∧ σ w = w` using `hw`. Take `⟨hwI, hσw⟩` from `hw'`. Use `⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩` and prove the remaining obligations. Rewrite using `[linPart_apply, Finset.sum_eq_single i₀]`. Rewrite using `[if_pos rfl] show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w`.

Rewrite using `[map_mul, hσw]`. Take the linear combination `w * hb`. Introduce `j _ hj`. Simplify using `[hj]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ i₀) h`.
-/
theorem mem_range_linPart (I : Ideal A) {M : ℕ} (y : Fin M → A) (i₀ : Fin M)
    {b : A} (hb : σ (y i₀) * b + σ b * y i₀ = 1) {w : A} (hw : w ∈ fixSub σ I) :
    w ∈ (linPart σ I y).range := by
  have hw' : w ∈ I ∧ σ w = w := hw
  obtain ⟨hwI, hσw⟩ := hw'
  classical
  refine ⟨fun i => if i = i₀ then ⟨b * w, I.mul_mem_left b hwI⟩ else 0, ?_⟩
  rw [linPart_apply, Finset.sum_eq_single i₀]
  · rw [if_pos rfl]
    show σ (y i₀) * (b * w) + σ (b * w) * y i₀ = w
    rw [map_mul, hσw]
    linear_combination w * hb
  · intro j _ hj
    simp [hj]
  · intro h
    exact absurd (Finset.mem_univ i₀) h

end Formalism.HermitianLattices.Ext.L3.SecondPropositionFree
