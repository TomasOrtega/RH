import Mathlib
import Formalism.SharpRestriction.LevelLetterCocycles.IntegralHeckeForms
import Formalism.LocalToGlobal.IndefiniteReal.Bridge

noncomputable section

open Formalism.IndefR.Bridge

namespace GlobalTheory.ClassTrace

variable {O Γ Hf P : Type} [CommRing O] [Group Γ] [Group Hf] [AddCommGroup P] [Module O P]
  (ι : Γ →* Hf) (J : Subgroup Hf) (lam : J →* Oˣ) (ρ : Representation O Γ P)

def intForms (LL : Hf → Submodule O P) : Submodule O (Hf → P) where
  carrier := {f | (∀ (γ : Γ) (h : Hf) (k : J), f (ι γ * h * k) = (lam k : O) • ρ γ (f h)) ∧ ∀ h, f h ∈ LL h}
  add_mem' := fun {f g} hf hg =>
    ⟨fun γ h k => by simp only [Pi.add_apply, hf.1 γ h k, hg.1 γ h k, map_add, smul_add],
      fun h => Submodule.add_mem _ (hf.2 h) (hg.2 h)⟩
  zero_mem' := ⟨fun γ h k => by simp, fun h => Submodule.zero_mem _⟩
  smul_mem' := fun a f hf =>
    ⟨fun γ h k => by simp only [Pi.smul_apply, hf.1 γ h k, map_smul]; rw [smul_comm],
      fun h => Submodule.smul_mem _ _ (hf.2 h)⟩

def LatticeLaw (LL : Hf → Submodule O P) : Prop :=
  (∀ γ h, (LL h).map (ρ γ) = LL (ι γ * h)) ∧ ∀ h (k : J), LL (h * k) = LL h

def tr (h : Hf) (p : P) : P := ∑ᶠ γ : stab ι J h, (lam (stabK ι γ) : O) • ρ (γ : Γ) p

open Classical in

def lamExt (x : Hf) : O := if hx : x ∈ J then (lam ⟨x, hx⟩ : O) else 0

/- English proof (translation)
Simplify using `[lamExt]`.
-/
theorem lamExt_coe (k : J) : lamExt J lam (k : Hf) = (lam k : O) := by
  simp [lamExt]

/- English proof (translation)
Simplify using `[lamExt, hx]`.
-/
theorem lamExt_of_not_mem {x : Hf} (hx : x ∉ J) : lamExt J lam x = 0 := by
  simp [lamExt, hx]

/- English proof (translation)
Distinguish the cases in `hx : x ∈ J`. Establish `hxk : x * (k : Hf) ∈ J` using `J.mul_mem hx k.2`. Unfold `lamExt`. Rewrite using `[dif_pos hxk, dif_pos hx, ← Units.val_mul, ← map_mul]`. Both sides reduce to the same expression.

Establish `hxk : x * (k : Hf) ∉ J` using `fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))`. Rewrite using `[lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]`.
-/
theorem lamExt_mul (x : Hf) (k : J) : lamExt J lam (x * k) = lamExt J lam x * (lam k : O) := by
  by_cases hx : x ∈ J
  · have hxk : x * (k : Hf) ∈ J := J.mul_mem hx k.2
    unfold lamExt
    rw [dif_pos hxk, dif_pos hx, ← Units.val_mul, ← map_mul]
    rfl
  · have hxk : x * (k : Hf) ∉ J := fun hm => hx (by simpa using J.mul_mem hm (J.inv_mem k.2))
    rw [lamExt_of_not_mem J lam hx, lamExt_of_not_mem J lam hxk, zero_mul]

def traceForm (h : Hf) (p : P) (x : Hf) : P := ∑ᶠ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p

def link (h x : Hf) : Set Γ := {γ | h⁻¹ * (ι γ)⁻¹ * x ∈ J}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hγ`. Use `⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩` and prove the remaining obligations. Use `show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)`. Use `group`.

Introduce and unpack `⟨k, rfl⟩ show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J`. Rewrite using `[show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]`. Conclude with `k.2`.
-/
theorem mem_link_iff {h x : Hf} {γ : Γ} : γ ∈ link ι J h x ↔ ∃ k : J, x = ι γ * h * k := by
  constructor
  · intro hγ
    refine ⟨⟨h⁻¹ * (ι γ)⁻¹ * x, hγ⟩, ?_⟩
    show x = ι γ * h * (h⁻¹ * (ι γ)⁻¹ * x)
    group
  · rintro ⟨k, rfl⟩
    show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) ∈ J
    rw [show h⁻¹ * (ι γ)⁻¹ * (ι γ * h * k) = (k : Hf) by group]
    exact k.2

def linkEquiv {h x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) : stab ι J x ≃ link ι J h x where
  toFun δ := ⟨δ * γ₀, by
    have h1 := J.mul_mem h0 (J.inv_mem ((mem_stab ι).1 δ.2))
    simpa [link, mul_assoc] using h1⟩
  invFun γ := ⟨γ * γ₀⁻¹, by
    have h1 := J.mul_mem (J.inv_mem γ.2) h0
    rw [mem_stab]
    simpa [link, mul_assoc] using h1⟩
  left_inv δ := by simp
  right_inv γ := by simp

/- English proof (translation)
Break down `(link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩` into its components or cases. Rewrite using `[he]`. Conclude with `Set.finite_empty`. Use `hfin x` as an intermediate fact. Conclude with `Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))`.
-/
theorem link_finite (hfin : ∀ x, Finite (stab ι J x)) (h x : Hf) : (link ι J h x).Finite := by
  rcases (link ι J h x).eq_empty_or_nonempty with he | ⟨γ₀, h0⟩
  · rw [he]
    exact Set.finite_empty
  · have := hfin x
    exact Set.finite_coe_iff.mp (Finite.of_equiv _ (linkEquiv ι J h0))

/- English proof (translation)
Introduce `γ hγ`. Rewrite `hγ` using `[Function.mem_support]`. Assume the negation of the conclusion as `hn`. Establish `hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J` using `hn`. Conclude with `hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])`.
-/
theorem support_subset (h : Hf) (p : P) (x : Hf) :
    (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) ⊆ link ι J h x := by
  intro γ hγ
  rw [Function.mem_support] at hγ
  by_contra hn
  have hn' : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hn
  exact hγ (by rw [lamExt_of_not_mem J lam hn', zero_smul])

/- English proof (translation)
Unfold `traceForm`. Establish `hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0`. Introduce `γ`. Establish `hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J` using `fun hm => hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩`. Rewrite using `[lamExt_of_not_mem J lam hn, zero_smul]`.

Simplify using `only [hz, finsum_zero]`.
-/
theorem traceForm_eq_zero (h : Hf) (p : P) {x : Hf} (hx : ¬ ∃ (γ : Γ) (k : J), x = ι γ * h * k) :
    traceForm ι J lam ρ h p x = 0 := by
  unfold traceForm
  have hz : ∀ γ : Γ, lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p = 0 := by
    intro γ
    have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := fun hm =>
      hx ⟨γ, (mem_link_iff ι J (h := h) (x := x) (γ := γ)).1 hm⟩
    rw [lamExt_of_not_mem J lam hn, zero_smul]
  simp only [hz, finsum_zero]

/- English proof (translation)
Establish `hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite` using `(link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)`. Unfold `traceForm`. Use `conv_rhs => rw [← LinearMap.smul_apply]`. Rewrite using `[map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]`. Use `finsum_congr fun γ => ?_` and prove the remaining obligations.

Simplify using `only [Equiv.coe_mulLeft]`. Establish `e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k`. Rewrite using `[map_mul]`. Use `group`. Rewrite using `[e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]`.

Conclude with `smul_comm _ _ _`.
-/
theorem traceForm_law (hfin : ∀ x, Finite (stab ι J x)) (h : Hf) (p : P) (γ₀ : Γ) (x : Hf) (k : J) :
    traceForm ι J lam ρ h p (ι γ₀ * x * k) = (lam k : O) • ρ γ₀ (traceForm ι J lam ρ h p x) := by
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    (link_finite ι J hfin h x).subset (support_subset ι J lam ρ h p x)
  unfold traceForm
  conv_rhs => rw [← LinearMap.smul_apply]
  rw [map_finsum _ hf, ← finsum_comp_equiv (Equiv.mulLeft γ₀)]
  refine finsum_congr fun γ => ?_
  simp only [Equiv.coe_mulLeft]
  have e : h⁻¹ * (ι (γ₀ * γ))⁻¹ * (ι γ₀ * x * k) = h⁻¹ * (ι γ)⁻¹ * x * k := by
    rw [map_mul]
    group
  rw [e, lamExt_mul, map_mul, Module.End.mul_apply, LinearMap.smul_apply, map_smul, mul_smul]
  exact smul_comm _ _ _

variable {C W : Type} [Field C] [AddCommGroup W] [Module C W] {e : O →+* C}

def classSum (θ : Hf → P →ₛₗ[e] W) {I : Type} [Fintype I] (y : I → Hf) (f : Hf → P) : W :=
  ∑ i, (Nat.card (stab ι J (y i)) : C)⁻¹ • θ (y i) (f (y i))

def DualLaw (θ : Hf → P →ₛₗ[e] W) : Prop :=
  ∀ (γ : Γ) (h : Hf) (k : J) (p : P), e (lam k) • θ (ι γ * h * k) (ρ γ p) = θ h p

/- English proof (translation)
Establish `hL` using `link_finite ι J hfin h x`. Establish `hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite` using `hL.subset (support_subset ι J lam ρ h p x)`. Establish `hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) = if γ ∈ link ι J h x then θ h p else 0`. Introduce `γ`. Use `split_ifs with hγ`.

Take `⟨k, hk⟩` from `(mem_link_iff ι J).1 hγ`. Establish `hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf)`. Rewrite using `[hk]`. Use `group`. Rewrite using `[hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]`.

Establish `hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J` using `hγ`. Rewrite using `[lamExt_of_not_mem J lam hn, zero_smul, map_zero]`. Establish `hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆ (hL.toFinset : Set Γ)`. Introduce `γ hγ`. Rewrite using `[Set.Finite.coe_toFinset]`.

Assume the negation of the conclusion as `hn`. Conclude with `hγ (if_neg hn)`. Establish `hc : hL.toFinset.card = Nat.card (stab ι J x)`. Rewrite using `[Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]`. Unfold `traceForm`.

Rewrite using `[map_finsum (θ x) hf]`. Simplify using `only [hterm]`. Rewrite using `[finsum_eq_sum_of_support_subset _ hsub, Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)), Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]`.
-/
theorem kernel_traceForm (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W} (hθ : DualLaw ι J lam ρ θ)
    (h : Hf) (p : P) {x : Hf} {γ₀ : Γ} (h0 : γ₀ ∈ link ι J h x) :
    θ x (traceForm ι J lam ρ h p x) = (Nat.card (stab ι J x) : C) • θ h p := by
  classical
  have hL := link_finite ι J hfin h x
  have hf : (Function.support fun γ : Γ => lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p).Finite :=
    hL.subset (support_subset ι J lam ρ h p x)
  have hterm : ∀ γ : Γ, θ x (lamExt J lam (h⁻¹ * (ι γ)⁻¹ * x) • ρ γ p) =
      if γ ∈ link ι J h x then θ h p else 0 := by
    intro γ
    split_ifs with hγ
    · obtain ⟨k, hk⟩ := (mem_link_iff ι J).1 hγ
      have hk' : h⁻¹ * (ι γ)⁻¹ * x = (k : Hf) := by
        rw [hk]
        group
      rw [hk', lamExt_coe, map_smulₛₗ, ← hθ γ h k p, ← hk]
    · have hn : h⁻¹ * (ι γ)⁻¹ * x ∉ J := hγ
      rw [lamExt_of_not_mem J lam hn, zero_smul, map_zero]
  have hsub : Function.support (fun γ : Γ => if γ ∈ link ι J h x then θ h p else 0) ⊆
      (hL.toFinset : Set Γ) := by
    intro γ hγ
    rw [Set.Finite.coe_toFinset]
    by_contra hn
    exact hγ (if_neg hn)
  have hc : hL.toFinset.card = Nat.card (stab ι J x) := by
    rw [Nat.card_congr (linkEquiv ι J h0), Nat.card_coe_set_eq, Set.ncard_eq_toFinset_card _ hL]
  unfold traceForm
  rw [map_finsum (θ x) hf]
  simp only [hterm]
  rw [finsum_eq_sum_of_support_subset _ hsub,
    Finset.sum_congr rfl (fun γ hγ => if_pos ((Set.Finite.mem_toFinset hL).1 hγ)),
    Finset.sum_const, hc, Nat.cast_smul_eq_nsmul]

/- English proof (translation)
Take `⟨i₀, ⟨γ, k, hh⟩, huniq⟩` from `hy h`. Unfold `classSum`. Rewrite using `[Finset.sum_eq_single i₀]`. Establish `h0 : γ⁻¹ ∈ link ι J h (y i₀)`. Rewrite using `[mem_link_iff]`.

Use `⟨k⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hh]`. Simplify using `only [map_inv, Subgroup.coe_inv]`. Use `group`. Rewrite using `[kernel_traceForm ι J lam ρ hfin hθ h p h0]`.

Use `hfin (y i₀)` as an intermediate fact. Establish `hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Conclude with `inv_smul_smul₀ hne _`. Introduce `i _ hi`. Establish `hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k'`.

Introduce and unpack `⟨γ', k', hy'⟩`. Apply `hi` to reduce the goal to its premises. Apply `huniq` to reduce the goal to its premises. Use `⟨γ'⁻¹, k'⁻¹, ?_⟩` and prove the remaining obligations. Rewrite using `[hy']`.

Simplify using `only [map_inv, Subgroup.coe_inv]`. Use `group`. Rewrite using `[traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]`. Introduce `hi`. Conclude with `absurd (Finset.mem_univ i₀) hi`.
-/
theorem classSum_traceForm [CharZero C] (hfin : ∀ x, Finite (stab ι J x)) {θ : Hf → P →ₛₗ[e] W}
    (hθ : DualLaw ι J lam ρ θ) {I : Type} [Fintype I] {y : I → Hf} (hy : IsReps ι J y) (h : Hf) (p : P) :
    classSum ι J θ y (traceForm ι J lam ρ h p) = θ h p := by
  obtain ⟨i₀, ⟨γ, k, hh⟩, huniq⟩ := hy h
  unfold classSum
  rw [Finset.sum_eq_single i₀]
  · have h0 : γ⁻¹ ∈ link ι J h (y i₀) := by
      rw [mem_link_iff]
      refine ⟨k⁻¹, ?_⟩
      rw [hh]
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [kernel_traceForm ι J lam ρ hfin hθ h p h0]
    have := hfin (y i₀)
    have hne : (Nat.card (stab ι J (y i₀)) : C) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
    exact inv_smul_smul₀ hne _
  · intro i _ hi
    have hx : ¬ ∃ (γ' : Γ) (k' : J), y i = ι γ' * h * k' := by
      rintro ⟨γ', k', hy'⟩
      apply hi
      apply huniq
      refine ⟨γ'⁻¹, k'⁻¹, ?_⟩
      rw [hy']
      simp only [map_inv, Subgroup.coe_inv]
      group
    rw [traceForm_eq_zero ι J lam ρ h p hx, map_zero, smul_zero]
  · intro hi
    exact absurd (Finset.mem_univ i₀) hi

/- English proof (translation)
Take `⟨i, ⟨γ, k, hx⟩, -⟩` from `hy x`. Substitute `hx` using the available equality. Use `hfin i` as an intermediate fact. Use `Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_` and prove the remaining obligations. Rewrite using `[mem_stab]`.

Establish `hδ` using `(mem_stab ι).1 δ.2`. Establish `e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i = (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹`. Simplify using `only [map_mul, map_inv]`. Use `group`. Rewrite using `[e]`.

Conclude with `J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)`. Introduce `a b hab`. Apply `Subtype.ext` to reduce the goal to its premises. Use `congrArg Subtype.val hab` as an intermediate fact. Simplify using `using this`.
-/
theorem finite_stab_of_reps {I : Type} {y : I → Hf} (hy : IsReps ι J y) (hfin : ∀ i, Finite (stab ι J (y i)))
    (x : Hf) : Finite (stab ι J x) := by
  obtain ⟨i, ⟨γ, k, hx⟩, -⟩ := hy x
  subst hx
  have := hfin i
  refine Finite.of_injective (β := stab ι J (y i)) (fun δ => ⟨γ⁻¹ * δ * γ, ?_⟩) ?_
  · rw [mem_stab]
    have hδ := (mem_stab ι).1 δ.2
    have e : (y i)⁻¹ * ι (γ⁻¹ * δ * γ) * y i =
        (k : Hf) * ((ι γ * y i * k)⁻¹ * ι δ * (ι γ * y i * k)) * (k : Hf)⁻¹ := by
      simp only [map_mul, map_inv]
      group
    rw [e]
    exact J.mul_mem (J.mul_mem k.2 hδ) (J.inv_mem k.2)
  · intro a b hab
    apply Subtype.ext
    have := congrArg Subtype.val hab
    simpa using this

end GlobalTheory.ClassTrace

end
