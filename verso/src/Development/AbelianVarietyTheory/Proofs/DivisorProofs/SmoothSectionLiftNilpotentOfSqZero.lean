import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LiftAt

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.SecLift

/- English proof (translation)
Introduce `H`. It suffices to establish `key : ∀ n : ℕ, ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ n = ⊥ → ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom → ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ …`. Introduce `R R₀ _ _ π hπ hnil`. Take `⟨n, hn⟩` from `hnil`. Conclude with `key n R R₀ π hπ hn`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `R R₀ _ _ π hπ hn`. Use `H R R₀ π hπ ?_` and prove the remaining obligations.

Conclude with `le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.zero_le 2)).trans hn.le)`. Consider the case `succ n ih`. Introduce `R R₀ _ _ π hπ hn X X₀ i hi hX e₀ he₀`. Distinguish the cases in `hn2 : n + 1 ≤ 2`. Conclude with `H R R₀ π hπ (le_bot_iff.mp ((Ideal.pow_le_pow_right hn2).trans hn.le)) X X₀ i hi hX e₀ he₀`.

Establish `hn1 : 1 ≤ n` using `by omega`. Use `set I := RingHom.ker π with hIdef`. Use `set J : Ideal R := I ^ n with hJdef`. Establish `hJI : J ≤ RingHom.ker π` using `Ideal.pow_le_self (by omega)`. Set `q : R →+* R ⧸ J` to `Ideal.Quotient.mk J`.

Set `π'' : R ⧸ J →+* R₀` to `Ideal.Quotient.lift J π (fun a ha => (RingHom.mem_ker).mp (hJI ha))`. Establish `hcomp : π''.comp q = π`. Use extensionality with `a`. Both sides reduce to the same expression. Establish `hsp : spMap π = spMap π'' ≫ spMap q`.

Rewrite using `[← hcomp]`. Simplify using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Establish `hπ'' : Function.Surjective π''` using `Ideal.Quotient.lift_surjective_of_surjective J _ hπ`. Establish `hkerq : RingHom.ker q = J` using `Ideal.mk_ker`. Establish `hkerπ'' : RingHom.ker π'' = I.map q`.

Use `RingHom.comap_ker π'' q` as an intermediate fact. Rewrite `this` using `[hcomp]`. Rewrite using `[← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective (RingHom.ker π''), this]`. Establish `hn'' : RingHom.ker π'' ^ n = ⊥`. Rewrite using `[hkerπ'', ← Ideal.map_pow]`.

Conclude with `Ideal.map_quotient_self J`. Establish `hJ2 : RingHom.ker q ^ 2 = ⊥`. Rewrite using `[hkerq, hJdef, ← pow_mul]`. Conclude with `le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)`. Set `X' : Over (Sp (R ⧸ J))` to `Over.mk (pullback.snd X.hom (spMap q))`.

Establish `hX' : Smooth X'.hom` using `show Smooth (pullback.snd X.hom (spMap q)) from inferInstance`. Establish `hw : i ≫ X.hom = (X₀.hom ≫ spMap π'') ≫ spMap q`. Rewrite using `[hi.w, hsp, Category.assoc]`. Set `i' : X₀.left ⟶ X'.left` to `pullback.lift i (X₀.hom ≫ spMap π'') hw`. Establish `hi'1 : i' ≫ pullback.fst X.hom (spMap q) = i` using `pullback.lift_fst _ _ _`.

Establish `hi'2 : i' ≫ X'.hom = X₀.hom ≫ spMap π''` using `pullback.lift_snd _ _ _`. Establish `hi' : IsPullback i' X₀.hom X'.hom (spMap π'')`. Use `IsPullback.of_right (h₁₂ := pullback.fst X.hom (spMap q)) (h₂₂ := spMap q) (v₁₃ := X.hom) ?_ hi'2 (IsPullback.of_hasPullback X.hom (spMap q))` and prove the remaining obligations. Rewrite using `[hi'1, ← hsp]`. Conclude with `hi`.

Take `⟨e', he'1, he'2⟩` from `ih (R ⧸ J) R₀ π'' hπ'' hn'' X' X₀ i' hi' hX' e₀ he₀`. Take `⟨e, he1, he2⟩` from `H R (R ⧸ J) q Ideal.Quotient.mk_surjective hJ2 X X' (pullback.fst X.hom (spMap q)) (IsPullback.of_hasPullback X.hom (spMap q)) hX e' he'1`. Use `⟨e, he1, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.
-/
theorem lift_of_nilpotent_of_sqZero :
    (∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → RingHom.ker π ^ 2 = ⊥ →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e) →
  ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π → IsNilpotent (RingHom.ker π) →
    ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) → Smooth X.hom →
    ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e := by
  intro H
  suffices key : ∀ n : ℕ, ∀ (R R₀ : Type) [CommRing R] [CommRing R₀] (π : R →+* R₀), Function.Surjective π →
      RingHom.ker π ^ n = ⊥ →
      ∀ (X : Over (Sp R)) (X₀ : Over (Sp R₀)) (i : X₀.left ⟶ X.left), IsPullback i X₀.hom X.hom (spMap π) →
      Smooth X.hom →
      ∀ e₀ : Sp R₀ ⟶ X₀.left, e₀ ≫ X₀.hom = 𝟙 _ → ∃ e : Sp R ⟶ X.left, e ≫ X.hom = 𝟙 _ ∧ e₀ ≫ i = spMap π ≫ e by
    intro R R₀ _ _ π hπ hnil
    obtain ⟨n, hn⟩ := hnil
    exact key n R R₀ π hπ hn
  intro n
  induction n with
  | zero =>
    intro R R₀ _ _ π hπ hn
    refine H R R₀ π hπ ?_
    exact le_bot_iff.mp ((Ideal.pow_le_pow_right (Nat.zero_le 2)).trans hn.le)
  | succ n ih =>
    intro R R₀ _ _ π hπ hn X X₀ i hi hX e₀ he₀
    by_cases hn2 : n + 1 ≤ 2
    · exact H R R₀ π hπ (le_bot_iff.mp ((Ideal.pow_le_pow_right hn2).trans hn.le)) X X₀ i hi hX e₀ he₀
    have hn1 : 1 ≤ n := by omega
    set I := RingHom.ker π with hIdef
    set J : Ideal R := I ^ n with hJdef
    have hJI : J ≤ RingHom.ker π := Ideal.pow_le_self (by omega)
    let q : R →+* R ⧸ J := Ideal.Quotient.mk J
    let π'' : R ⧸ J →+* R₀ := Ideal.Quotient.lift J π (fun a ha => (RingHom.mem_ker).mp (hJI ha))
    have hcomp : π''.comp q = π := by
      ext a; rfl
    have hsp : spMap π = spMap π'' ≫ spMap q := by
      rw [← hcomp]
      simp [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
    have hπ'' : Function.Surjective π'' := Ideal.Quotient.lift_surjective_of_surjective J _ hπ
    have hkerq : RingHom.ker q = J := Ideal.mk_ker
    have hkerπ'' : RingHom.ker π'' = I.map q := by
      have := RingHom.comap_ker π'' q
      rw [hcomp] at this
      rw [← Ideal.map_comap_of_surjective q Ideal.Quotient.mk_surjective (RingHom.ker π''), this]
    have hn'' : RingHom.ker π'' ^ n = ⊥ := by
      rw [hkerπ'', ← Ideal.map_pow]
      exact Ideal.map_quotient_self J
    have hJ2 : RingHom.ker q ^ 2 = ⊥ := by
      rw [hkerq, hJdef, ← pow_mul]
      exact le_bot_iff.mp ((Ideal.pow_le_pow_right (by omega)).trans hn.le)
    let X' : Over (Sp (R ⧸ J)) := Over.mk (pullback.snd X.hom (spMap q))
    have hX' : Smooth X'.hom := show Smooth (pullback.snd X.hom (spMap q)) from inferInstance
    have hw : i ≫ X.hom = (X₀.hom ≫ spMap π'') ≫ spMap q := by
      rw [hi.w, hsp, Category.assoc]
    let i' : X₀.left ⟶ X'.left := pullback.lift i (X₀.hom ≫ spMap π'') hw
    have hi'1 : i' ≫ pullback.fst X.hom (spMap q) = i := pullback.lift_fst _ _ _
    have hi'2 : i' ≫ X'.hom = X₀.hom ≫ spMap π'' := pullback.lift_snd _ _ _
    have hi' : IsPullback i' X₀.hom X'.hom (spMap π'') := by
      refine IsPullback.of_right (h₁₂ := pullback.fst X.hom (spMap q)) (h₂₂ := spMap q) (v₁₃ := X.hom) ?_ hi'2
        (IsPullback.of_hasPullback X.hom (spMap q))
      rw [hi'1, ← hsp]
      exact hi
    obtain ⟨e', he'1, he'2⟩ := ih (R ⧸ J) R₀ π'' hπ'' hn'' X' X₀ i' hi' hX' e₀ he₀
    obtain ⟨e, he1, he2⟩ := H R (R ⧸ J) q Ideal.Quotient.mk_surjective hJ2 X X'
      (pullback.fst X.hom (spMap q)) (IsPullback.of_hasPullback X.hom (spMap q)) hX e' he'1
    refine ⟨e, he1, ?_⟩
    calc e₀ ≫ i = e₀ ≫ i' ≫ pullback.fst X.hom (spMap q) := by rw [hi'1]
      _ = (spMap π'' ≫ e') ≫ pullback.fst X.hom (spMap q) := by rw [← Category.assoc, he'2]
      _ = spMap π'' ≫ spMap q ≫ e := by rw [Category.assoc, he2]
      _ = spMap π ≫ e := by rw [hsp, Category.assoc]

end GlobalTheory.SecLift
