import Mathlib
import Formalism.LocalToGlobal.Columns.AtTLemmas

open NumberField IsDedekindDomain Module

noncomputable section

namespace Formalism.L2.Col

open Formalism.BasicNotions Formalism.HermitianLatticesTheory Formalism.L2.DIV

section Gen

/- English proof (translation)
Establish `hfin : Finite (A ⧸ P)` using `Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)`. Set `_ : Fintype (A ⧸ P)` to `Fintype.ofFinite _`. Establish `hc' : Fintype.card (A ⧸ P) = p` using `by rw [← Nat.card_eq_fintype_card, hc]`. Set `e` to `ZMod.ringEquivOfPrime (A ⧸ P) hp hc'`. Establish `: NeZero p` using `⟨hp.ne_zero⟩`.

Establish `h1 : e (e.symm (Ideal.Quotient.mk P x)) = Ideal.Quotient.mk P x` using `e.apply_symm_apply _`. Rewrite `h1` using `[← ZMod.natCast_zmod_val (e.symm (Ideal.Quotient.mk P x)), map_natCast]`. Take `⟨k, hk⟩ : ∃ k : ℕ, (k : A ⧸ P) = Ideal.Quotient.mk P x` from `⟨_, h1⟩`. Use `⟨(k : ℤ), ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq, ← hk, Int.cast_natCast, map_natCast]`.
-/
theorem owedS_exists_int {A : Type} [CommRing A] (P : Ideal A) {p : ℕ} (hp : p.Prime) (hc : Nat.card (A ⧸ P) = p) (x : A) :
    ∃ a : ℤ, x - (a : A) ∈ P := by
  have hfin : Finite (A ⧸ P) := Nat.finite_of_card_ne_zero (by rw [hc]; exact hp.ne_zero)
  let _ : Fintype (A ⧸ P) := Fintype.ofFinite _
  have hc' : Fintype.card (A ⧸ P) = p := by rw [← Nat.card_eq_fintype_card, hc]
  let e := ZMod.ringEquivOfPrime (A ⧸ P) hp hc'
  have : NeZero p := ⟨hp.ne_zero⟩
  have h1 : e (e.symm (Ideal.Quotient.mk P x)) = Ideal.Quotient.mk P x := e.apply_symm_apply _
  rw [← ZMod.natCast_zmod_val (e.symm (Ideal.Quotient.mk P x)), map_natCast] at h1
  obtain ⟨k, hk⟩ : ∃ k : ℕ, (k : A ⧸ P) = Ideal.Quotient.mk P x := ⟨_, h1⟩
  refine ⟨(k : ℤ), ?_⟩
  rw [← Ideal.Quotient.eq, ← hk, Int.cast_natCast, map_natCast]

/- English proof (translation)
Establish `hsup : Ideal.span {(p : A)} ⊔ P ^ 2 = P`. Establish `h1 : P ^ (1 + 1) < Ideal.span {(p : A)} ⊔ P ^ 2`. Use `lt_of_le_of_ne le_sup_right ?_` and prove the remaining obligations. Introduce `h`. Apply `hp2` to reduce the goal to its premises.

Establish `: (p : A) ∈ Ideal.span {(p : A)} ⊔ P ^ 2` using `Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)`. Rewrite `this` using `[← h]`. Conclude with `this`. Establish `h2 : Ideal.span {(p : A)} ⊔ P ^ 2 ≤ P ^ 1`. Rewrite using `[pow_one]`.

Conclude with `sup_le ((Ideal.span_singleton_le_iff_mem _).2 hp) (Ideal.pow_le_self (by norm_num))`. Use `Ideal.eq_prime_pow_of_succ_lt_of_le hP0 h1 h2` as an intermediate fact. Rewrite `this` using `[pow_one]`. Then use the resulting hypothesis. Establish `key : ∀ (n : ℕ) (x : A), φ x - φ' x ∈ w ^ n`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero`. Introduce `x`. Rewrite using `[pow_zero, Ideal.one_eq_top]`. Conclude with `Submodule.mem_top`.

Consider the case `succ n ih`. Establish `hprod : ∀ r ∈ P, ∀ s ∈ P, φ (r * s) - φ' (r * s) ∈ w ^ (n + 1)`. Introduce `r hr s hs`. Establish `e : φ (r * s) - φ' (r * s) = (φ s - φ' s) * φ r + (φ r - φ' r) * φ' s`. Rewrite using `[map_mul, map_mul]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, pow_succ]`. Conclude with `Ideal.add_mem _ (Ideal.mul_mem_mul (ih s) (hφ r hr)) (Ideal.mul_mem_mul (ih r) (hφ' s hs))`. Establish `hsq : ∀ z ∈ P ^ 2, φ z - φ' z ∈ w ^ (n + 1)`. Introduce `z hz`.

Rewrite `hz` using `[sq]`. Use `Submodule.mul_induction_on hz (fun r hr s hs => hprod r hr s hs) (fun a b ha hb => ?_)` and prove the remaining obligations. Establish `e : φ (a + b) - φ' (a + b) = (φ a - φ' a) + (φ b - φ' b)`. Rewrite using `[map_add, map_add]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Conclude with `Ideal.add_mem _ ha hb`. Establish `hP : ∀ y ∈ P, φ y - φ' y ∈ w ^ (n + 1)`. Introduce `y hy`. Rewrite `hy` using `[← hsup]`.

Take `⟨y1, hy1, z, hz, rfl⟩` from `Submodule.mem_sup.1 hy`. Take `⟨c, rfl⟩` from `Ideal.mem_span_singleton'.1 hy1`. Establish `e : φ (c * (p : A) + z) - φ' (c * (p : A) + z) = (φ c - φ' c) * φ (p : A) + (φ z - φ' z)`. Rewrite using `[map_add, map_add, map_mul, map_mul, map_natCast, map_natCast]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[e]`. Use `Ideal.add_mem _ ?_ (hsq z hz)` and prove the remaining obligations. Rewrite using `[pow_succ]`. Conclude with `Ideal.mul_mem_mul (ih c) (hφ _ hp)`. Introduce `x`.

Take `⟨a, ha⟩` from `hZ x`. Establish `e : φ x - φ' x = φ (x - (a : A)) - φ' (x - (a : A))`. Rewrite using `[map_sub, map_sub, map_intCast, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Conclude with `hP _ ha`. Use extensionality with `x`. Establish `h0 : φ x - φ' x ∈ (⨅ i, w ^ i : Ideal B)`. Rewrite using `[Ideal.mem_iInf]`. Conclude with `fun n => key n x`.

Rewrite `h0` using `[Ideal.iInf_pow_eq_bot_of_isDomain w hw, Ideal.mem_bot]`. Conclude with `sub_eq_zero.1 h0`.
-/
theorem owedS_ringHom_eq {A B : Type} [CommRing A] [IsDedekindDomain A] [CommRing B] [IsDomain B] [IsNoetherianRing B]
    (φ φ' : A →+* B) (w : Ideal B) (hw : w ≠ ⊤) (P : Ideal A) [hPp : P.IsPrime] (hP0 : P ≠ ⊥)
    (hφ : ∀ x ∈ P, φ x ∈ w) (hφ' : ∀ x ∈ P, φ' x ∈ w) (p : ℕ) (hp : (p : A) ∈ P) (hp2 : (p : A) ∉ P ^ 2)
    (hZ : ∀ x : A, ∃ a : ℤ, x - (a : A) ∈ P) : φ = φ' := by
  have hsup : Ideal.span {(p : A)} ⊔ P ^ 2 = P := by
    have h1 : P ^ (1 + 1) < Ideal.span {(p : A)} ⊔ P ^ 2 := by
      refine lt_of_le_of_ne le_sup_right ?_
      intro h
      apply hp2
      have : (p : A) ∈ Ideal.span {(p : A)} ⊔ P ^ 2 := Ideal.mem_sup_left (Ideal.mem_span_singleton_self _)
      rw [← h] at this
      exact this
    have h2 : Ideal.span {(p : A)} ⊔ P ^ 2 ≤ P ^ 1 := by
      rw [pow_one]
      exact sup_le ((Ideal.span_singleton_le_iff_mem _).2 hp) (Ideal.pow_le_self (by norm_num))
    have := Ideal.eq_prime_pow_of_succ_lt_of_le hP0 h1 h2
    rwa [pow_one] at this
  have key : ∀ (n : ℕ) (x : A), φ x - φ' x ∈ w ^ n := by
    intro n
    induction n with
    | zero =>
      intro x
      rw [pow_zero, Ideal.one_eq_top]
      exact Submodule.mem_top
    | succ n ih =>
      have hprod : ∀ r ∈ P, ∀ s ∈ P, φ (r * s) - φ' (r * s) ∈ w ^ (n + 1) := by
        intro r hr s hs
        have e : φ (r * s) - φ' (r * s) = (φ s - φ' s) * φ r + (φ r - φ' r) * φ' s := by
          rw [map_mul, map_mul]; ring
        rw [e, pow_succ]
        exact Ideal.add_mem _ (Ideal.mul_mem_mul (ih s) (hφ r hr)) (Ideal.mul_mem_mul (ih r) (hφ' s hs))
      have hsq : ∀ z ∈ P ^ 2, φ z - φ' z ∈ w ^ (n + 1) := by
        intro z hz
        rw [sq] at hz
        refine Submodule.mul_induction_on hz (fun r hr s hs => hprod r hr s hs) (fun a b ha hb => ?_)
        have e : φ (a + b) - φ' (a + b) = (φ a - φ' a) + (φ b - φ' b) := by
          rw [map_add, map_add]; ring
        rw [e]
        exact Ideal.add_mem _ ha hb
      have hP : ∀ y ∈ P, φ y - φ' y ∈ w ^ (n + 1) := by
        intro y hy
        rw [← hsup] at hy
        obtain ⟨y1, hy1, z, hz, rfl⟩ := Submodule.mem_sup.1 hy
        obtain ⟨c, rfl⟩ := Ideal.mem_span_singleton'.1 hy1
        have e : φ (c * (p : A) + z) - φ' (c * (p : A) + z) = (φ c - φ' c) * φ (p : A) + (φ z - φ' z) := by
          rw [map_add, map_add, map_mul, map_mul, map_natCast, map_natCast]; ring
        rw [e]
        refine Ideal.add_mem _ ?_ (hsq z hz)
        rw [pow_succ]
        exact Ideal.mul_mem_mul (ih c) (hφ _ hp)
      intro x
      obtain ⟨a, ha⟩ := hZ x
      have e : φ x - φ' x = φ (x - (a : A)) - φ' (x - (a : A)) := by
        rw [map_sub, map_sub, map_intCast, map_intCast]; ring
      rw [e]
      exact hP _ ha
  ext x
  have h0 : φ x - φ' x ∈ (⨅ i, w ^ i : Ideal B) := by
    rw [Ideal.mem_iInf]
    exact fun n => key n x
  rw [Ideal.iInf_pow_eq_bot_of_isDomain w hw, Ideal.mem_bot] at h0
  exact sub_eq_zero.1 h0

end Gen

section Seen

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
The claim follows from `Fintype.card_pos_iff.1 hX.f_pos`.
-/
theorem Fields.Ok.nonempty_Tau (hX : X.Ok) : Nonempty X.Tau := Fintype.card_pos_iff.1 hX.f_pos

/- English proof (translation)
Apply `hX.emb_inj` to reduce the goal to its premises. Apply `IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 X.E))` to reduce the goal to its premises. Use extensionality with `x`. Use `congrArg (fun z : 𝓞 X.K => (z : X.K)) (DFunLike.congr_fun h x)` as an intermediate fact. Conclude with `this`.
-/
theorem owedS_emb_of_embO (hX : X.Ok) {τ τ' : X.Tau} (h : X.embO τ = X.embO τ') : τ = τ' := by
  apply hX.emb_inj
  apply IsLocalization.ringHom_ext (nonZeroDivisors (𝓞 X.E))
  ext x
  have := congrArg (fun z : 𝓞 X.K => (z : X.K)) (DFunLike.congr_fun h x)
  exact this

/- English proof (translation)
The claim follows from `mem_divs (hPr.piT_ne_zero u) _`.
-/
theorem conjP_pullW_mem_vT_iff (hPr : Pr.Ok) (u : Pr.Word) (τ : X.Tau) (w : HeightOneSpectrum (𝓞 X.K)) :
    conjPrime₂ (pullW τ w) ∈ Pr.vT u ↔ X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal :=
  mem_divs (hPr.piT_ne_zero u) _

/- English proof (translation)
Establish `e : (Pr.T u : 𝓞 X.K) = X.embO τ (Pr.piT u) * X.embO τ (X.conjO (Pr.piT u))`. Rewrite using `[← map_mul, hPr.piT_norm u, map_natCast]`. Rewrite using `[e]`. Break down `h with h | h` into its components or cases. Conclude with `Ideal.mul_mem_right _ _ h`.

Conclude with `Ideal.mul_mem_left _ _ h`.
-/
theorem owedS_T_mem {u : Pr.Word} (hPr : Pr.Ok) {w : HeightOneSpectrum (𝓞 X.K)} {τ : X.Tau}
    (h : X.embO τ (Pr.piT u) ∈ w.asIdeal ∨ X.embO τ (X.conjO (Pr.piT u)) ∈ w.asIdeal) : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal := by
  have e : (Pr.T u : 𝓞 X.K) = X.embO τ (Pr.piT u) * X.embO τ (X.conjO (Pr.piT u)) := by
    rw [← map_mul, hPr.piT_norm u, map_natCast]
  rw [e]
  rcases h with h | h
  · exact Ideal.mul_mem_right _ _ h
  · exact Ideal.mul_mem_left _ _ h

/- English proof (translation)
Apply `owedS_emb_of_embO hX` to reduce the goal to its premises. Take `⟨h1, h2⟩` from `T_unif hX hPr u ⟨pullW τ w, hP⟩`. Establish `hc : Nat.card (𝓞 X.E ⧸ (pullW τ w).asIdeal) = Pr.T u`. Rewrite using `[← hPr.vT_norm u _ hP, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `(pullW τ w).isPrime` as an intermediate fact.

Conclude with `owedS_ringHom_eq (X.embO τ) (X.embO τ') w.asIdeal w.isPrime.ne_top (pullW τ w).asIdeal (pullW τ w).ne_bot (fun x hx => hx) (fun x hx => by rw [h] at hx; exact hx) (Pr.T u) h1 h2 (owedS_exists_int _ (hPr.T_prime u) hc)`.
-/
theorem eq_of_pullW_eq (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) {τ τ' : X.Tau}
    (h : pullW τ w = pullW τ' w) (hP : pullW τ w ∈ Pr.vT u) : τ = τ' := by
  apply owedS_emb_of_embO hX
  obtain ⟨h1, h2⟩ := T_unif hX hPr u ⟨pullW τ w, hP⟩
  have hc : Nat.card (𝓞 X.E ⧸ (pullW τ w).asIdeal) = Pr.T u := by
    rw [← hPr.vT_norm u _ hP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have := (pullW τ w).isPrime
  exact owedS_ringHom_eq (X.embO τ) (X.embO τ') w.asIdeal w.isPrime.ne_top (pullW τ w).asIdeal (pullW τ w).ne_bot
    (fun x hx => hx) (fun x hx => by rw [h] at hx; exact hx) (Pr.T u) h1 h2
    (owedS_exists_int _ (hPr.T_prime u) hc)

/- English proof (translation)
Apply `owedS_emb_of_embO hX` to reduce the goal to its premises. Take `⟨h1, h2⟩` from `T_unif hX hPr u ⟨conjPrime₂ (pullW τ w), hP⟩`. Establish `hc : Nat.card (𝓞 X.E ⧸ (conjPrime₂ (pullW τ w)).asIdeal) = Pr.T u`. Rewrite using `[← hPr.vT_norm u _ hP, Ideal.absNorm_apply, Submodule.cardQuot_apply]`. Use `(conjPrime₂ (pullW τ w)).isPrime` as an intermediate fact.

Establish `key` using `owedS_ringHom_eq ((X.embO τ).comp (cO X.E)) ((X.embO τ').comp (cO X.E)) w.asIdeal w.isPrime.ne_top (conjPrime₂ (pullW τ w)).asIdeal (conjPrime₂ (pullW τ w)).ne_bot (fun x hx => hx) (fun x hx => by rw [h] at hx; exact hx) (Pr.T u) h1 h2 (owedS_exists_int _ (hPr.T_prime u) hc)`. Use `ext1 x`. Use `DFunLike.congr_fun key (cO X.E x)` as an intermediate fact. Simplify `this` using `only [RingHom.comp_apply, cO_cO]`.
-/
theorem owedS_inj_Pbar (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) {τ τ' : X.Tau}
    (h : pullW τ w = pullW τ' w) (hP : conjPrime₂ (pullW τ w) ∈ Pr.vT u) : τ = τ' := by
  apply owedS_emb_of_embO hX
  obtain ⟨h1, h2⟩ := T_unif hX hPr u ⟨conjPrime₂ (pullW τ w), hP⟩
  have hc : Nat.card (𝓞 X.E ⧸ (conjPrime₂ (pullW τ w)).asIdeal) = Pr.T u := by
    rw [← hPr.vT_norm u _ hP, Ideal.absNorm_apply, Submodule.cardQuot_apply]
  have := (conjPrime₂ (pullW τ w)).isPrime
  have key := owedS_ringHom_eq ((X.embO τ).comp (cO X.E)) ((X.embO τ').comp (cO X.E)) w.asIdeal w.isPrime.ne_top
    (conjPrime₂ (pullW τ w)).asIdeal (conjPrime₂ (pullW τ w)).ne_bot
    (fun x hx => hx) (fun x hx => by rw [h] at hx; exact hx) (Pr.T u) h1 h2
    (owedS_exists_int _ (hPr.T_prime u) hc)
  ext1 x
  have := DFunLike.congr_fun key (cO X.E x)
  simpa only [RingHom.comp_apply, cO_cO] using this

/- English proof (translation)
Introduce `τ τ' h`. Break down `seenC_or_seenBarC hX hPr u w hw with hs | hs` into its components or cases. Conclude with `eq_of_pullW_eq hX hPr u w h ((pullW_mem_vT hPr u τ w).2 (hs τ))`. Conclude with `owedS_inj_Pbar hX hPr u w h ((conjP_pullW_mem_vT_iff hPr u τ w).2 (hs τ))`.
-/
theorem pullW_injective (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : Function.Injective fun τ : X.Tau => pullW τ w := by
  intro τ τ' h
  rcases seenC_or_seenBarC hX hPr u w hw with hs | hs
  · exact eq_of_pullW_eq hX hPr u w h ((pullW_mem_vT hPr u τ w).2 (hs τ))
  · exact owedS_inj_Pbar hX hPr u w h ((conjP_pullW_mem_vT_iff hPr u τ w).2 (hs τ))

/- English proof (translation)
Take `⟨τ⟩` from `hX.nonempty_Tau`. Conclude with `owedS_T_mem hPr (Or.inl (h τ))`.
-/
theorem seenC.T_mem (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (h : seenC Pr u w) :
    (Pr.T u : 𝓞 X.K) ∈ w.asIdeal := by
  obtain ⟨τ⟩ := hX.nonempty_Tau
  exact owedS_T_mem hPr (Or.inl (h τ))

/- English proof (translation)
Take `⟨τ⟩` from `hX.nonempty_Tau`. Conclude with `owedS_T_mem hPr (Or.inr (h τ))`.
-/
theorem seenBarC.T_mem (hX : X.Ok) (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (h : seenBarC Pr u w) :
    (Pr.T u : 𝓞 X.K) ∈ w.asIdeal := by
  obtain ⟨τ⟩ := hX.nonempty_Tau
  exact owedS_T_mem hPr (Or.inr (h τ))

/- English proof (translation)
Introduce `τ'`. Rewrite using `[embO_of_Kq (hPr.piT_Kq u) τ' τ]`. Conclude with `(pullW_mem_vT hPr u τ w).1 h`.
-/
theorem seenC_of_one (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} {τ : X.Tau}
    (h : pullW τ w ∈ Pr.vT u) : seenC Pr u w := by
  intro τ'
  rw [embO_of_Kq (hPr.piT_Kq u) τ' τ]
  exact (pullW_mem_vT hPr u τ w).1 h

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨fun τ τ' e => pullW_injective hX hPr u w (h.T_mem hX hPr) (congrArg Subtype.val e), ?_⟩` and prove the remaining obligations. Rewrite using `[Fintype.card_coe, hPr.vT_card u]`. Both sides reduce to the same expression.
-/
theorem pullW_bijective (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenC Pr u w) :
    Function.Bijective fun τ : X.Tau => (⟨pullW τ w, (seenC_iff hPr u w).1 h τ⟩ : {P // P ∈ Pr.vT u}) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun τ τ' e => pullW_injective hX hPr u w (h.T_mem hX hPr) (congrArg Subtype.val e), ?_⟩
  rw [Fintype.card_coe, hPr.vT_card u]
  rfl

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨fun τ τ' e => ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : conjPrime₂ (pullW τ w) = conjPrime₂ (pullW τ' w)` using `congrArg Subtype.val e`. Use `pullW_injective hX hPr u w (h.T_mem hX hPr) ?_` and prove the remaining obligations. Use `show pullW τ w = pullW τ' w`.

Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Use `congrArg (fun Q : HeightOneSpectrum (𝓞 X.E) => cO X.E x ∈ Q.asIdeal) e1` as an intermediate fact. Simplify `this` using `only [mem_conjP, cO_cO, eq_iff_iff]`. Rewrite using `[Fintype.card_coe, hPr.vT_card u]`.

Both sides reduce to the same expression.
-/
theorem pullW_bar_bijective (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenBarC Pr u w) :
    Function.Bijective fun τ : X.Tau =>
      (⟨conjPrime₂ (pullW τ w), (conjP_pullW_mem_vT_iff hPr u τ w).2 (h τ)⟩ : {P // P ∈ Pr.vT u}) := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun τ τ' e => ?_, ?_⟩
  · have e1 : conjPrime₂ (pullW τ w) = conjPrime₂ (pullW τ' w) := congrArg Subtype.val e
    refine pullW_injective hX hPr u w (h.T_mem hX hPr) ?_
    show pullW τ w = pullW τ' w
    apply HeightOneSpectrum.ext
    ext x
    have := congrArg (fun Q : HeightOneSpectrum (𝓞 X.E) => cO X.E x ∈ Q.asIdeal) e1
    simpa only [mem_conjP, cO_cO, eq_iff_iff] using this
  · rw [Fintype.card_coe, hPr.vT_card u]
    rfl

/- English proof (translation)
Apply `HeightOneSpectrum.ext` to reduce the goal to its premises. Use extensionality with `x`. Rewrite using `[mem_conjP, mem_conjP, cO_cO]`.
-/
theorem conjP_conjP'₂ (P : HeightOneSpectrum (𝓞 X.E)) : conjPrime₂ (conjPrime₂ P) = P := by
  apply HeightOneSpectrum.ext
  ext x
  rw [mem_conjP, mem_conjP, cO_cO]

/- English proof (translation)
Introduce `hb`. Use `not_seen_both hPr u w τ (h τ) ((conjP_pullW_mem_vT_iff hPr u τ w).1 ?_)` and prove the remaining obligations. Rewrite using `[show pullW τ w = conjPrime₂ P.1 from hb, conjP_conjP'₂]`. Conclude with `P.2`.
-/
theorem seenC.not_bar (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (h : seenC Pr u w) (τ : X.Tau)
    (P : {P // P ∈ Pr.vT u}) : ¬ SeesPbar w τ P.1 := by
  intro hb
  refine not_seen_both hPr u w τ (h τ) ((conjP_pullW_mem_vT_iff hPr u τ w).1 ?_)
  rw [show pullW τ w = conjPrime₂ P.1 from hb, conjP_conjP'₂]
  exact P.2

/- English proof (translation)
Introduce `hb`. Use `not_seen_both hPr u w τ ((pullW_mem_vT hPr u τ w).1 ?_) (h τ)` and prove the remaining obligations. Rewrite using `[show pullW τ w = P.1 from hb]`. Conclude with `P.2`.
-/
theorem seenBarC.not_P (hPr : Pr.Ok) {u : Pr.Word} {w : HeightOneSpectrum (𝓞 X.K)} (h : seenBarC Pr u w) (τ : X.Tau)
    (P : {P // P ∈ Pr.vT u}) : ¬ SeesP w τ P.1 := by
  intro hb
  refine not_seen_both hPr u w τ ((pullW_mem_vT hPr u τ w).1 ?_) (h τ)
  rw [show pullW τ w = P.1 from hb]
  exact P.2

/- English proof (translation)
Break down `seenC_or_seenBarC hX hPr u w hw with hs | hs` into its components or cases. Take `⟨τ, hτ⟩` from `(pullW_bijective hX hPr u w hs).2 P`. Establish `hτ' : pullW τ w = P.1` using `congrArg Subtype.val hτ`. Use `⟨τ, Or.inl hτ', ?_⟩` and prove the remaining obligations. Introduce and unpack `τ' (h' | h')`.

Conclude with `pullW_injective hX hPr u w hw ((show pullW τ' w = P.1 from h').trans hτ'.symm)`. Conclude with `absurd h' (hs.not_bar hPr τ' P)`. Take `⟨τ, hτ⟩` from `(pullW_bar_bijective hX hPr u w hs).2 P`. Establish `hτ' : conjPrime₂ (pullW τ w) = P.1` using `congrArg Subtype.val hτ`. Establish `hτ'' : pullW τ w = conjPrime₂ P.1` using `by rw [← hτ', conjP_conjP'₂]`.

Use `⟨τ, Or.inr hτ'', ?_⟩` and prove the remaining obligations. Introduce and unpack `τ' (h' | h')`. Conclude with `absurd h' (hs.not_P hPr τ' P)`. Conclude with `pullW_injective hX hPr u w hw ((show pullW τ' w = conjPrime₂ P.1 from h').trans hτ''.symm)`.
-/
theorem existsUnique_sees (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) : ∃! τ : X.Tau, SeesP w τ P.1 ∨ SeesPbar w τ P.1 := by
  rcases seenC_or_seenBarC hX hPr u w hw with hs | hs
  · obtain ⟨τ, hτ⟩ := (pullW_bijective hX hPr u w hs).2 P
    have hτ' : pullW τ w = P.1 := congrArg Subtype.val hτ
    refine ⟨τ, Or.inl hτ', ?_⟩
    rintro τ' (h' | h')
    · exact pullW_injective hX hPr u w hw ((show pullW τ' w = P.1 from h').trans hτ'.symm)
    · exact absurd h' (hs.not_bar hPr τ' P)
  · obtain ⟨τ, hτ⟩ := (pullW_bar_bijective hX hPr u w hs).2 P
    have hτ' : conjPrime₂ (pullW τ w) = P.1 := congrArg Subtype.val hτ
    have hτ'' : pullW τ w = conjPrime₂ P.1 := by rw [← hτ', conjP_conjP'₂]
    refine ⟨τ, Or.inr hτ'', ?_⟩
    rintro τ' (h' | h')
    · exact absurd h' (hs.not_P hPr τ' P)
    · exact pullW_injective hX hPr u w hw ((show pullW τ' w = conjPrime₂ P.1 from h').trans hτ''.symm)

variable [Nonempty X.Tau]

/- English proof (translation)
The claim follows from `Classical.epsilon_spec (p := fun τ => SeesP w τ P.1 ∨ SeesPbar w τ P.1) (existsUnique_sees hX hPr u w hw P).exists`.
-/
theorem tauOfC_spec (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) :
    SeesP w (tauOfC w P.1) P.1 ∨ SeesPbar w (tauOfC w P.1) P.1 :=
  Classical.epsilon_spec (p := fun τ => SeesP w τ P.1 ∨ SeesPbar w τ P.1) (existsUnique_sees hX hPr u w hw P).exists

/- English proof (translation)
The claim follows from `(existsUnique_sees hX hPr u w hw P).unique (tauOfC_spec hX hPr u w hw P) h`.
-/
theorem tauOfC_unique (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) (P : {P // P ∈ Pr.vT u}) {τ : X.Tau} (h : SeesP w τ P.1 ∨ SeesPbar w τ P.1) :
    tauOfC w P.1 = τ :=
  (existsUnique_sees hX hPr u w hw P).unique (tauOfC_spec hX hPr u w hw P) h

/- English proof (translation)
The claim follows from `tauOfC_unique hX hPr u w ((seenC_of_one hPr h).T_mem hX hPr) ⟨pullW τ w, h⟩ (Or.inl rfl)`.
-/
theorem tauOfC_pullW (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (τ : X.Tau)
    (h : pullW τ w ∈ Pr.vT u) : tauOfC w (pullW τ w) = τ :=
  tauOfC_unique hX hPr u w ((seenC_of_one hPr h).T_mem hX hPr) ⟨pullW τ w, h⟩ (Or.inl rfl)

/- English proof (translation)
The claim follows from `(tauOfC_spec hX hPr u w (h.T_mem hX hPr) P).resolve_right (h.not_bar hPr _ P)`.
-/
theorem pullW_tauOfC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) (h : seenC Pr u w)
    (P : {P // P ∈ Pr.vT u}) : pullW (tauOfC w P.1) w = P.1 :=
  (tauOfC_spec hX hPr u w (h.T_mem hX hPr) P).resolve_right (h.not_bar hPr _ P)

/- English proof (translation)
Rewrite using `[Fintype.bijective_iff_injective_and_card]`. Use `⟨fun P P' e => ?_, ?_⟩` and prove the remaining obligations. Establish `e' : tauOfC w P.1 = tauOfC w P'.1` using `e`. Establish `h1` using `tauOfC_spec hX hPr u w hw P`. Establish `h2` using `tauOfC_spec hX hPr u w hw P'`.

Rewrite `h2` using `[← e']`. Apply `Subtype.ext` to reduce the goal to its premises. Break down `seenC_or_seenBarC hX hPr u w hw with hs | hs` into its components or cases. Conclude with `(h1.resolve_right (hs.not_bar hPr _ P)).symm.trans (h2.resolve_right (hs.not_bar hPr _ P'))`. Establish `a1 : pullW (tauOfC w P.1) w = conjPrime₂ P.1` using `h1.resolve_left (hs.not_P hPr _ P)`.

Establish `a2 : pullW (tauOfC w P.1) w = conjPrime₂ P'.1` using `h2.resolve_left (hs.not_P hPr _ P')`. Rewrite using `[← conjP_conjP'₂ P.1, ← a1, a2, conjP_conjP'₂]`. Rewrite using `[Fintype.card_coe, hPr.vT_card u]`. Both sides reduce to the same expression.
-/
theorem tauOfC_bijective (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K))
    (hw : (Pr.T u : 𝓞 X.K) ∈ w.asIdeal) : Function.Bijective fun P : {P // P ∈ Pr.vT u} => tauOfC w P.1 := by
  rw [Fintype.bijective_iff_injective_and_card]
  refine ⟨fun P P' e => ?_, ?_⟩
  · have e' : tauOfC w P.1 = tauOfC w P'.1 := e
    have h1 := tauOfC_spec hX hPr u w hw P
    have h2 := tauOfC_spec hX hPr u w hw P'
    rw [← e'] at h2
    apply Subtype.ext
    rcases seenC_or_seenBarC hX hPr u w hw with hs | hs
    · exact (h1.resolve_right (hs.not_bar hPr _ P)).symm.trans (h2.resolve_right (hs.not_bar hPr _ P'))
    · have a1 : pullW (tauOfC w P.1) w = conjPrime₂ P.1 := h1.resolve_left (hs.not_P hPr _ P)
      have a2 : pullW (tauOfC w P.1) w = conjPrime₂ P'.1 := h2.resolve_left (hs.not_P hPr _ P')
      rw [← conjP_conjP'₂ P.1, ← a1, a2, conjP_conjP'₂]
  · rw [Fintype.card_coe, hPr.vT_card u]
    rfl

variable {R : Ranks} (W : Wts X Pr.Word R)

open Classical in

/- English proof (translation)
Use `split_ifs with h`. Use extensionality with `P`. Rewrite using `[mem_VVTc, topsP_of_seenC W hPr u w h, Finset.mem_filter]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨τ, hτ, e⟩`.

Use `⟨Finset.mem_univ _, ?_⟩` and prove the remaining obligations. Rewrite using `[tauOfC_unique hX hPr u w (h.T_mem hX hPr) P (Or.inl e)]`. Conclude with `hτ`. Introduce and unpack `⟨-, hτ⟩`. Conclude with `⟨_, hτ, pullW_tauOfC hX hPr u w h P⟩`.

Use extensionality with `P`. Rewrite using `[mem_VVTc]`. Simplify using `only [Finset.notMem_empty, iff_false]`. Introduce and unpack `⟨τ, -, e⟩`. Conclude with `h (seenC_of_one hPr (τ := τ) (by rw [e]; exact P.2))`.
-/
theorem VVTc_eq (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    VVTc W u w =
      if seenC Pr u w then Finset.univ.filter fun P : {P // P ∈ Pr.vT u} => tauOfC w P.1 ∈ W.tops else ∅ := by
  split_ifs with h
  · ext P
    rw [mem_VVTc, topsP_of_seenC W hPr u w h, Finset.mem_filter]
    constructor
    · rintro ⟨τ, hτ, e⟩
      refine ⟨Finset.mem_univ _, ?_⟩
      rw [tauOfC_unique hX hPr u w (h.T_mem hX hPr) P (Or.inl e)]
      exact hτ
    · rintro ⟨-, hτ⟩
      exact ⟨_, hτ, pullW_tauOfC hX hPr u w h P⟩
  · ext P
    rw [mem_VVTc]
    simp only [Finset.notMem_empty, iff_false]
    rintro ⟨τ, -, e⟩
    exact h (seenC_of_one hPr (τ := τ) (by rw [e]; exact P.2))

/- English proof (translation)
Unfold `expTc`. Use `congr 1`. Establish `hmem : ∀ τ ∈ topsP W u w, pullW τ w ∈ Pr.vT u` using `fun τ hτ => (Finset.mem_filter.1 hτ).2`. Use `Finset.sum_bij (fun τ hτ => (⟨pullW τ w, hmem τ hτ⟩ : {P // P ∈ Pr.vT u})) ?_ ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`.

Conclude with `(mem_VVTc W u w _).2 ⟨τ, hτ, rfl⟩`. Introduce `τ hτ τ' _ e`. Conclude with `pullW_injective hX hPr u w ((seenC_of_one hPr (hmem τ hτ)).T_mem hX hPr) (congrArg Subtype.val e)`. Introduce `P hP`. Take `⟨τ, hτ, e⟩` from `(mem_VVTc W u w P).1 hP`.

Conclude with `⟨τ, hτ, Subtype.ext e⟩`. Introduce `τ hτ`. Rewrite using `[tauOfC_pullW hX hPr u w τ (hmem τ hτ)]`.
-/
theorem expTc_eq (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    expTc W u w = (R.m : ℤ) * ∑ P ∈ VVTc W u w, W.bTop u (tauOfC w P.1) := by
  classical
  unfold expTc
  congr 1
  have hmem : ∀ τ ∈ topsP W u w, pullW τ w ∈ Pr.vT u := fun τ hτ => (Finset.mem_filter.1 hτ).2
  refine Finset.sum_bij (fun τ hτ => (⟨pullW τ w, hmem τ hτ⟩ : {P // P ∈ Pr.vT u})) ?_ ?_ ?_ ?_
  · intro τ hτ
    exact (mem_VVTc W u w _).2 ⟨τ, hτ, rfl⟩
  · intro τ hτ τ' _ e
    exact pullW_injective hX hPr u w ((seenC_of_one hPr (hmem τ hτ)).T_mem hX hPr) (congrArg Subtype.val e)
  · intro P hP
    obtain ⟨τ, hτ, e⟩ := (mem_VVTc W u w P).1 hP
    exact ⟨τ, hτ, Subtype.ext e⟩
  · intro τ hτ
    rw [tauOfC_pullW hX hPr u w τ (hmem τ hτ)]

/- English proof (translation)
Establish `hmem : ∀ τ ∈ topsP W u w, pullW τ w ∈ Pr.vT u` using `fun τ hτ => (Finset.mem_filter.1 hτ).2`. Use `symm`. Use `Finset.card_bij (fun τ hτ => (⟨pullW τ w, hmem τ hτ⟩ : {P // P ∈ Pr.vT u})) ?_ ?_ ?_` and prove the remaining obligations. Introduce `τ hτ`. Conclude with `(mem_VVTc W u w _).2 ⟨τ, hτ, rfl⟩`.

Introduce `τ hτ τ' _ e`. Conclude with `pullW_injective hX hPr u w ((seenC_of_one hPr (hmem τ hτ)).T_mem hX hPr) (congrArg Subtype.val e)`. Introduce `P hP`. Take `⟨τ, hτ, e⟩` from `(mem_VVTc W u w P).1 hP`. Conclude with `⟨τ, hτ, Subtype.ext e⟩`.
-/
theorem card_VVTc (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) (w : HeightOneSpectrum (𝓞 X.K)) :
    (VVTc W u w).card = (topsP W u w).card := by
  classical
  have hmem : ∀ τ ∈ topsP W u w, pullW τ w ∈ Pr.vT u := fun τ hτ => (Finset.mem_filter.1 hτ).2
  symm
  refine Finset.card_bij (fun τ hτ => (⟨pullW τ w, hmem τ hτ⟩ : {P // P ∈ Pr.vT u})) ?_ ?_ ?_
  · intro τ hτ
    exact (mem_VVTc W u w _).2 ⟨τ, hτ, rfl⟩
  · intro τ hτ τ' _ e
    exact pullW_injective hX hPr u w ((seenC_of_one hPr (hmem τ hτ)).T_mem hX hPr) (congrArg Subtype.val e)
  · intro P hP
    obtain ⟨τ, hτ, e⟩ := (mem_VVTc W u w P).1 hP
    exact ⟨τ, hτ, Subtype.ext e⟩

end Seen

section Exist

variable {X : Fields} {Pr : Primes X}

/- English proof (translation)
Establish `hx0' : (x : X.E) ≠ 0`. Introduce `h`. Conclude with `hx0 (RingOfIntegers.ext h)`. Establish `hnu : ¬ IsUnit (X.embO τ x)`. Introduce `hu`.

Take `⟨y, hy⟩` from `hu.exists_right_inv`. Establish `hy' : X.emb τ (x : X.E) * (y : X.K) = 1` using `congrArg (fun z : 𝓞 X.K => (z : X.K)) hy`. Establish `e : X.emb τ ((x : X.E)⁻¹) = (y : X.K)`. Rewrite using `[map_inv₀]`. Conclude with `inv_eq_of_mul_eq_one_right hy'`.

Establish `hint : IsIntegral ℤ ((x : X.E)⁻¹)`. Establish `h1 : IsIntegral ℤ ((X.emb τ).toIntAlgHom ((x : X.E)⁻¹))` using `by show IsIntegral ℤ (X.emb τ ((x : X.E)⁻¹))`. Rewrite using `[e]`. Conclude with `y.isIntegral_coe`. Conclude with `(isIntegral_algHom_iff (X.emb τ).toIntAlgHom (X.emb τ).injective).1 h1`.

Apply `hx` to reduce the goal to its premises. Use `IsUnit.of_mul_eq_one (IsIntegralClosure.mk' (𝓞 X.E) _ hint) ?_` and prove the remaining obligations. Apply `RingOfIntegers.ext` to reduce the goal to its premises. Use `show (x : X.E) * algebraMap (𝓞 X.E) X.E (IsIntegralClosure.mk' (𝓞 X.E) _ hint) = 1`. Rewrite using `[IsIntegralClosure.algebraMap_mk', mul_inv_cancel₀ hx0']`.

Take `⟨M, hM, hle⟩` from `Ideal.exists_le_maximal (Ideal.span {X.embO τ x}) (fun h => hnu (Ideal.span_singleton_eq_top.1 h))`. Establish `hmem : X.embO τ x ∈ M` using `hle (Ideal.mem_span_singleton_self _)`. Use `⟨⟨M, hM.isPrime, ?_⟩, hmem⟩` and prove the remaining obligations. Introduce `hb`. Rewrite `hmem` using `[hb, Ideal.mem_bot]`.

Apply `hx0'` to reduce the goal to its premises. Establish `: X.emb τ (x : X.E) = 0` using `congrArg (fun z : 𝓞 X.K => (z : X.K)) hmem`. Conclude with `(map_eq_zero (X.emb τ)).1 this`.
-/
theorem owedS_exists_prime (τ : X.Tau) {x : 𝓞 X.E} (hx0 : x ≠ 0) (hx : ¬ IsUnit x) :
    ∃ w : HeightOneSpectrum (𝓞 X.K), X.embO τ x ∈ w.asIdeal := by
  have hx0' : (x : X.E) ≠ 0 := by
    intro h
    exact hx0 (RingOfIntegers.ext h)
  have hnu : ¬ IsUnit (X.embO τ x) := by
    intro hu
    obtain ⟨y, hy⟩ := hu.exists_right_inv
    have hy' : X.emb τ (x : X.E) * (y : X.K) = 1 := congrArg (fun z : 𝓞 X.K => (z : X.K)) hy
    have e : X.emb τ ((x : X.E)⁻¹) = (y : X.K) := by
      rw [map_inv₀]
      exact inv_eq_of_mul_eq_one_right hy'
    have hint : IsIntegral ℤ ((x : X.E)⁻¹) := by
      have h1 : IsIntegral ℤ ((X.emb τ).toIntAlgHom ((x : X.E)⁻¹)) := by
        show IsIntegral ℤ (X.emb τ ((x : X.E)⁻¹))
        rw [e]
        exact y.isIntegral_coe
      exact (isIntegral_algHom_iff (X.emb τ).toIntAlgHom (X.emb τ).injective).1 h1
    apply hx
    refine IsUnit.of_mul_eq_one (IsIntegralClosure.mk' (𝓞 X.E) _ hint) ?_
    apply RingOfIntegers.ext
    show (x : X.E) * algebraMap (𝓞 X.E) X.E (IsIntegralClosure.mk' (𝓞 X.E) _ hint) = 1
    rw [IsIntegralClosure.algebraMap_mk', mul_inv_cancel₀ hx0']
  obtain ⟨M, hM, hle⟩ := Ideal.exists_le_maximal (Ideal.span {X.embO τ x})
    (fun h => hnu (Ideal.span_singleton_eq_top.1 h))
  have hmem : X.embO τ x ∈ M := hle (Ideal.mem_span_singleton_self _)
  refine ⟨⟨M, hM.isPrime, ?_⟩, hmem⟩
  intro hb
  rw [hb, Ideal.mem_bot] at hmem
  apply hx0'
  have : X.emb τ (x : X.E) = 0 := congrArg (fun z : 𝓞 X.K => (z : X.K)) hmem
  exact (map_eq_zero (X.emb τ)).1 this

/- English proof (translation)
Take `⟨τ⟩` from `hX.nonempty_Tau`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP⟩ : (Pr.vT u).Nonempty := by`. Rewrite using `[← Finset.card_pos, hPr.vT_card u]`. Conclude with `hX.f_pos`. Establish `hmem : Pr.piT u ∈ P.asIdeal` using `(mem_divs (hPr.piT_ne_zero u) P).1 hP`.

Take `⟨w, hw⟩` from `owedS_exists_prime τ (hPr.piT_ne_zero u) (fun hu => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu))`. Conclude with `⟨w, seenC_of_one hPr ((pullW_mem_vT hPr u τ w).2 hw)⟩`.
-/
theorem exists_seenC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) : ∃ w : HeightOneSpectrum (𝓞 X.K), seenC Pr u w := by
  obtain ⟨τ⟩ := hX.nonempty_Tau
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := by
    rw [← Finset.card_pos, hPr.vT_card u]
    exact hX.f_pos
  have hmem : Pr.piT u ∈ P.asIdeal := (mem_divs (hPr.piT_ne_zero u) P).1 hP
  obtain ⟨w, hw⟩ := owedS_exists_prime τ (hPr.piT_ne_zero u)
    (fun hu => P.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem hu))
  exact ⟨w, seenC_of_one hPr ((pullW_mem_vT hPr u τ w).2 hw)⟩

/- English proof (translation)
Take `⟨τ⟩` from `hX.nonempty_Tau`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP⟩ : (Pr.vT u).Nonempty := by`. Rewrite using `[← Finset.card_pos, hPr.vT_card u]`. Conclude with `hX.f_pos`. Establish `hmem : Pr.piT u ∈ P.asIdeal` using `(mem_divs (hPr.piT_ne_zero u) P).1 hP`.

Establish `hmem' : X.conjO (Pr.piT u) ∈ (conjPrime₂ P).asIdeal`. Rewrite using `[mem_conjP]`. Use `show cO X.E (cO X.E (Pr.piT u)) ∈ P.asIdeal`. Rewrite using `[cO_cO]`. Conclude with `hmem`.

Establish `h0 : X.conjO (Pr.piT u) ≠ 0`. Introduce `h`. Apply `hPr.piT_ne_zero u` to reduce the goal to its premises. Rewrite using `[← cO_cO (Pr.piT u)]`. Use `show cO X.E (X.conjO (Pr.piT u)) = 0`.

Rewrite using `[h, map_zero]`. Take `⟨w, hw⟩` from `owedS_exists_prime τ h0 (fun hu => (conjPrime₂ P).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem' hu))`. Use `⟨w, fun τ' => ?_⟩` and prove the remaining obligations. Rewrite using `[embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ' τ]`. Conclude with `hw`.
-/
theorem exists_seenBarC (hX : X.Ok) (hPr : Pr.Ok) (u : Pr.Word) : ∃ w : HeightOneSpectrum (𝓞 X.K), seenBarC Pr u w := by
  obtain ⟨τ⟩ := hX.nonempty_Tau
  obtain ⟨P, hP⟩ : (Pr.vT u).Nonempty := by
    rw [← Finset.card_pos, hPr.vT_card u]
    exact hX.f_pos
  have hmem : Pr.piT u ∈ P.asIdeal := (mem_divs (hPr.piT_ne_zero u) P).1 hP
  have hmem' : X.conjO (Pr.piT u) ∈ (conjPrime₂ P).asIdeal := by
    rw [mem_conjP]
    show cO X.E (cO X.E (Pr.piT u)) ∈ P.asIdeal
    rw [cO_cO]
    exact hmem
  have h0 : X.conjO (Pr.piT u) ≠ 0 := by
    intro h
    apply hPr.piT_ne_zero u
    rw [← cO_cO (Pr.piT u)]
    show cO X.E (X.conjO (Pr.piT u)) = 0
    rw [h, map_zero]
  obtain ⟨w, hw⟩ := owedS_exists_prime τ h0
    (fun hu => (conjPrime₂ P).isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hmem' hu))
  refine ⟨w, fun τ' => ?_⟩
  rw [embO_of_Kq (conjO_mem_Kq hX (hPr.piT_Kq u)) τ' τ]
  exact hw

end Exist

end Formalism.L2.Col
