import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RevPosRevPos
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OscillatorModelValuesFourth
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.WeilActionLiftPairStepVectorInvLevelChar

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.TraceLift

/- English proof (translation)
Set `T : H → Γ → W` to `fun z γ => if h : z₀⁻¹ * ι γ * z ∈ J then (χ ⟨_, h⟩ : ℂ) • ρ γ⁻¹ w else 0`. Establish `hS : ∀ z, Function.support (T z) ⊆ {γ | z₀⁻¹ * ι γ * z ∈ J}` using `fun z γ hγ => by`. Assume the negation of the conclusion as `h`. Conclude with `hγ (dif_neg h)`. Establish `hS0 : {γ | z₀⁻¹ * ι γ * z₀ ∈ J} = (Bridge.stab ι J z₀ : Set Γ)`.

Use extensionality with `γ`. Conclude with `(Bridge.mem_stab _).symm`. Establish `hfin' : (Bridge.stab ι J z₀ : Set Γ).Finite` using `hfin`. Establish `hF : ∀ z, {γ | z₀⁻¹ * ι γ * z ∈ J}.Finite` using `fun z => by`. Break down `Set.eq_empty_or_nonempty {γ | z₀⁻¹ * ι γ * z ∈ J} with h | ⟨δ, hδ⟩` into its components or cases.

Rewrite using `[h]`. Conclude with `Set.finite_empty`. Use `(hfin'.image (· * δ)).subset fun γ hγ => ⟨γ * δ⁻¹, ?_, by simp⟩` and prove the remaining obligations. Rewrite using `[← hS0]`. Use `J.mul_mem hγ (J.inv_mem hδ)` as an intermediate fact.

Simplify `this` using `[mul_assoc]`. Establish `hT : ∀ z, (Function.support (T z)).Finite` using `fun z => (hF z).subset (hS z)`. Use `⟨fun z => ∑ᶠ γ, T z γ, fun δ z k => ?_, fun z hz => ?_, fun L hL => ?_⟩` and prove the remaining obligations. Establish `h1 : ∀ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (T z (γ * δ))` using `fun γ => by`. Establish `e : z₀⁻¹ * ι γ * (ι δ * z * k) = z₀⁻¹ * ι (γ * δ) * z * k` using `by rw [map_mul]; group`.

Distinguish the cases in `h : z₀⁻¹ * ι (γ * δ) * z ∈ J`. Establish `h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∈ J` using `by rw [e]; exact J.mul_mem h k.2`. Establish `e2 : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k` using `Subtype.ext e`. Establish `e3 : ρ δ (ρ (γ * δ)⁻¹ w) = ρ γ⁻¹ w`. Rewrite using `[← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]`.

Simplify using `only [T]`. Rewrite using `[dif_pos h, dif_pos h', e2, map_mul, LinearMap.smul_apply, map_smul, e3, smul_smul, Units.val_mul, mul_comm]`. Establish `h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∉ J` using `by rw [e, J.mul_mem_cancel_right k.2]; exact h`. Simplify using `only [T]`. Rewrite using `[dif_neg h, dif_neg h', map_zero]`.

Use `show ∑ᶠ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (∑ᶠ γ, T z γ)`. Rewrite using `[map_finsum _ (hT z), finsum_congr h1]`. Conclude with `finsum_comp_equiv (Equiv.mulRight δ) (f := fun γ => ((χ k : ℂ) • ρ δ) (T z γ))`. Use `finsum_eq_zero_of_forall_eq_zero fun γ => dif_neg fun h => hz ⟨γ⁻¹, ⟨_, h⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[map_inv]`.

Use `group`. Use `show L (∑ᶠ γ, T z₀ γ) = _`. Rewrite using `[finsum_eq_sum_of_support_subset (s := hfin'.toFinset) _ (by rw [Set.Finite.coe_toFinset, ← hS0]; exact hS z₀), map_sum, Finset.sum_congr rfl (g := fun _ => L w) fun γ hγ => ?_]`. Rewrite using `[Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin']`. Both sides reduce to the same expression.

Establish `h : z₀⁻¹ * ι γ * z₀ ∈ J` using `(Bridge.mem_stab _).1 (hfin'.mem_toFinset.1 hγ)`. Simplify using `only [T]`. Rewrite using `[dif_pos h, hL]`.
-/
theorem exists_traceForm {H Γ W : Type} [Group H] [Group Γ] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (ι : Γ →* H)
    (ρ : Γ →* Module.End ℂ W) (J : Subgroup H) (χ : J →* ℂˣ) (z₀ : H) (hfin : Finite (Bridge.stab ι J z₀)) (w : W) :
    ∃ f ∈ Bridge.AdForms ι ρ J χ, (∀ z, (¬ ∃ (γ : Γ) (k : J), z = ι γ * z₀ * k) → f z = 0) ∧
      ∀ L : W →ₗ[ℂ] ℂ, (∀ (γ : Γ) (hγ : z₀⁻¹ * ι γ * z₀ ∈ J), L ((χ ⟨_, hγ⟩ : ℂ) • ρ γ⁻¹ w) = L w) →
        L (f z₀) = (Nat.card (Bridge.stab ι J z₀) : ℂ) * L w := by
  let T : H → Γ → W := fun z γ => if h : z₀⁻¹ * ι γ * z ∈ J then (χ ⟨_, h⟩ : ℂ) • ρ γ⁻¹ w else 0
  have hS : ∀ z, Function.support (T z) ⊆ {γ | z₀⁻¹ * ι γ * z ∈ J} := fun z γ hγ => by
    by_contra h
    exact hγ (dif_neg h)
  have hS0 : {γ | z₀⁻¹ * ι γ * z₀ ∈ J} = (Bridge.stab ι J z₀ : Set Γ) := by
    ext γ
    exact (Bridge.mem_stab _).symm
  have hfin' : (Bridge.stab ι J z₀ : Set Γ).Finite := hfin
  have hF : ∀ z, {γ | z₀⁻¹ * ι γ * z ∈ J}.Finite := fun z => by
    rcases Set.eq_empty_or_nonempty {γ | z₀⁻¹ * ι γ * z ∈ J} with h | ⟨δ, hδ⟩
    · rw [h]; exact Set.finite_empty
    · refine (hfin'.image (· * δ)).subset fun γ hγ => ⟨γ * δ⁻¹, ?_, by simp⟩
      rw [← hS0]
      have := J.mul_mem hγ (J.inv_mem hδ)
      simpa [mul_assoc] using this
  have hT : ∀ z, (Function.support (T z)).Finite := fun z => (hF z).subset (hS z)
  refine ⟨fun z => ∑ᶠ γ, T z γ, fun δ z k => ?_, fun z hz => ?_, fun L hL => ?_⟩
  · have h1 : ∀ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (T z (γ * δ)) := fun γ => by
      have e : z₀⁻¹ * ι γ * (ι δ * z * k) = z₀⁻¹ * ι (γ * δ) * z * k := by rw [map_mul]; group
      by_cases h : z₀⁻¹ * ι (γ * δ) * z ∈ J
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∈ J := by rw [e]; exact J.mul_mem h k.2
        have e2 : (⟨_, h'⟩ : J) = ⟨_, h⟩ * k := Subtype.ext e
        have e3 : ρ δ (ρ (γ * δ)⁻¹ w) = ρ γ⁻¹ w := by
          rw [← Module.End.mul_apply, ← map_mul, _root_.mul_inv_rev, mul_inv_cancel_left]
        simp only [T]
        rw [dif_pos h, dif_pos h', e2, map_mul, LinearMap.smul_apply, map_smul, e3, smul_smul, Units.val_mul, mul_comm]
      · have h' : z₀⁻¹ * ι γ * (ι δ * z * k) ∉ J := by rw [e, J.mul_mem_cancel_right k.2]; exact h
        simp only [T]
        rw [dif_neg h, dif_neg h', map_zero]
    show ∑ᶠ γ, T (ι δ * z * k) γ = ((χ k : ℂ) • ρ δ) (∑ᶠ γ, T z γ)
    rw [map_finsum _ (hT z), finsum_congr h1]
    exact finsum_comp_equiv (Equiv.mulRight δ) (f := fun γ => ((χ k : ℂ) • ρ δ) (T z γ))
  · refine finsum_eq_zero_of_forall_eq_zero fun γ => dif_neg fun h => hz ⟨γ⁻¹, ⟨_, h⟩, ?_⟩
    rw [map_inv]; group
  · show L (∑ᶠ γ, T z₀ γ) = _
    rw [finsum_eq_sum_of_support_subset (s := hfin'.toFinset) _ (by rw [Set.Finite.coe_toFinset, ← hS0]; exact hS z₀),
      map_sum, Finset.sum_congr rfl (g := fun _ => L w) fun γ hγ => ?_]
    · rw [Finset.sum_const, nsmul_eq_mul, ← Set.ncard_eq_toFinset_card _ hfin']
      rfl
    · have h : z₀⁻¹ * ι γ * z₀ ∈ J := (Bridge.mem_stab _).1 (hfin'.mem_toFinset.1 hγ)
      simp only [T]
      rw [dif_pos h, hL]

/- English proof (translation)
Take `⟨c, ⟨γ, m, e⟩, -⟩` from `hy z`. Establish `key : ∀ δ : Bridge.stab ι J z, γ⁻¹ * δ.1 * γ ∈ Bridge.stab ι J (y c)` using `fun δ => by`. Establish `h1 : z⁻¹ * ι δ.1 * z ∈ J` using `(Bridge.mem_stab _).1 δ.2`. Rewrite using `[Bridge.mem_stab]`. Establish `h2` using `J.mul_mem (J.mul_mem m.2 h1) (J.inv_mem m.2)`.

Generalize the expression as in `δ.1 = d at h2`. Rewrite `h2` using `[e]`. Simplify `h2` using `[mul_assoc]`. Use `haveI := hf c`. Use `Finite.of_injective (fun δ => (⟨_, key δ⟩ : Bridge.stab ι J (y c))) fun a b hab => ?_` and prove the remaining obligations.

Conclude with `Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab)))`.
-/
theorem finite_stab {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H} (hy : Bridge.IsReps ι J y)
    (hf : ∀ c, Finite (Bridge.stab ι J (y c))) (z : H) : Finite (Bridge.stab ι J z) := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  have key : ∀ δ : Bridge.stab ι J z, γ⁻¹ * δ.1 * γ ∈ Bridge.stab ι J (y c) := fun δ => by
    have h1 : z⁻¹ * ι δ.1 * z ∈ J := (Bridge.mem_stab _).1 δ.2
    rw [Bridge.mem_stab]
    have h2 := J.mul_mem (J.mul_mem m.2 h1) (J.inv_mem m.2)
    generalize δ.1 = d at h2
    rw [e] at h2
    simpa [mul_assoc] using h2
  haveI := hf c
  refine Finite.of_injective (fun δ => (⟨_, key δ⟩ : Bridge.stab ι J (y c))) fun a b hab => ?_
  exact Subtype.ext (mul_left_cancel (mul_right_cancel (congrArg Subtype.val hab)))

/- English proof (translation)
Take `⟨c, ⟨γ, m, e⟩, -⟩` from `hy z`. Use `⟨Function.update y c z, c, fun g => ?_, Function.update_self _ _ _⟩` and prove the remaining obligations. Establish `hiff : ∀ j, (∃ (δ : Γ) (k : J), g = ι δ * Function.update y c z j * k) ↔ ∃ (δ : Γ) (k : J), g = ι δ * y j * k`. Introduce `j`. Distinguish the cases in `hj : j = c`.

Substitute `hj` using the available equality. Rewrite using `[Function.update_self, e]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨δ, k, h⟩`. Conclude with `⟨δ * γ, m * k, by rw [h, map_mul, Subgroup.coe_mul]; group⟩`.

Introduce and unpack `⟨δ, k, h⟩`. Conclude with `⟨δ * γ⁻¹, m⁻¹ * k, by rw [h, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group⟩`. Rewrite using `[Function.update_of_ne hj]`. Simplify using `only [hiff]`. Conclude with `hy g`.
-/
theorem exists_isReps_through {H Γ I : Type} [Group H] [Group Γ] (ι : Γ →* H) (J : Subgroup H) {y : I → H}
    (hy : Bridge.IsReps ι J y) (z : H) : ∃ (y' : I → H) (c : I), Bridge.IsReps ι J y' ∧ y' c = z := by
  obtain ⟨c, ⟨γ, m, e⟩, -⟩ := hy z
  refine ⟨Function.update y c z, c, fun g => ?_, Function.update_self _ _ _⟩
  have hiff : ∀ j, (∃ (δ : Γ) (k : J), g = ι δ * Function.update y c z j * k) ↔ ∃ (δ : Γ) (k : J), g = ι δ * y j * k := by
    intro j
    by_cases hj : j = c
    · subst hj
      rw [Function.update_self, e]
      constructor
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ, m * k, by rw [h, map_mul, Subgroup.coe_mul]; group⟩
      · rintro ⟨δ, k, h⟩
        exact ⟨δ * γ⁻¹, m⁻¹ * k, by rw [h, map_mul, map_inv, Subgroup.coe_mul, Subgroup.coe_inv]; group⟩
    · rw [Function.update_of_ne hj]
  simp only [hiff]
  exact hy g

/- English proof (translation)
Take `⟨h₀, hh₀, a, ha, rfl, -⟩` from `hdec h`. Take `⟨y', c₀, hy', e₀⟩` from `exists_isReps_through _ _ hy (p h₀)`. Establish `hlift : ∀ z : Hf, ∃ k ∈ F, p k = z` using `fun z => by`. Take `⟨u, hu⟩` from `hp z`. Take `⟨k, hk, -, -, -, e⟩` from `hdec u`.

Conclude with `⟨k, hk, e.trans hu⟩`. Use `choose σ hσ hσ' using hlift`. Set `r : Cl → H` to `Function.update (fun k => σ (y' k)) c₀ h₀`. Establish `hr : ∀ k, r k ∈ F ∧ p (r k) = y' k` using `fun k => by`. Distinguish the cases in `hk : k = c₀`.

Substitute `hk` using the available equality. Simplify using `only [r, Function.update_self]`. Conclude with `⟨hh₀, e₀.symm⟩`. Simplify using `only [r, Function.update_of_ne hk]`. Conclude with `⟨hσ _, hσ' _⟩`.

Establish `hr0 : r c₀ = h₀` using `Function.update_self _ _ _`. Establish `hyr : (fun k => p (r k)) = y'` using `funext fun k => (hr k).2`. Establish `hf0` using `finite_stab _ _ hy hfin (p h₀)`. Take `⟨f, hf, hz, hv⟩` from `exists_traceForm (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) hf0 (ρ a w)`. Use `⟨f, hf, r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩` and prove the remaining obligations.

Rewrite using `[Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]`. Set `L₀ : W →ₗ[ℂ] ℂ` to `(LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ`. Establish `hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀` using `fun v => rfl`. Establish `key` using `hv L₀ fun γ hγ => ?_`. Establish `hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0` using `Nat.cast_ne_zero.2 (Nat.card_pos).ne'`.

Establish `e1 : (h₀ * a, g) = ((h₀, g) : H × G') * (a, 1)` using `by rw [Prod.mk_mul_mk, mul_one]`. Rewrite using `[hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀, e1, map_mul, Module.End.mul_apply, hΛa a ha]`. Generalize the expression as in `ρ a w = v`. Take `⟨k, hk, b, hb, e, e'⟩` from `hdec ((γ : H)⁻¹ * h₀)`. Establish `hκ : h₀⁻¹ * k ∈ F` using `mul_mem (inv_mem hh₀) hk`.

Establish `eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹` using `by show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹`. Rewrite using `[map_mul, e', map_mul, map_inv, map_inv]`. Use `group`. Establish `hκ' : p (h₀⁻¹ * k) ∈ J` using `by rw [eκ]; exact inv_mem hγ`. Establish `eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩`.

Rewrite using `[show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]`. Establish `eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v`. Establish `h1` using `congrArg ρ e`. Rewrite `h1` using `[map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul]`. Rewrite using `[← h1]`.

Both sides reduce to the same expression. Establish `e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g)`. Rewrite using `[Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]`. Rewrite using `[hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply, ← map_mul, ← map_mul, e3, map_mul]`. Conclude with `hom _ (inv_mem γ.2) _ _`.

Introduce `k _ hk`. Rewrite using `[hz _ ?_, map_zero, map_zero]`. Simplify using the standard rewrite rules. Introduce `hex`. Take `⟨j, -, hu⟩` from `hy' (y' k)`.

Use `hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)` and prove the remaining obligations. Use `show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m`. Rewrite using `[e₀, ← (hr k).2]`. Conclude with `hex`.
-/
theorem exists_form_sum {H Hf W : Type} [Group H] [Group Hf] [NormedAddCommGroup W] [InnerProductSpace ℂ W] (p : H →* Hf)
    (hp : Function.Surjective p) (Γ F R : Subgroup H) (ρ : H →* Module.End ℂ W) (J : Subgroup Hf) (χ : J →* ℂˣ)
    (hdec : ∀ u : H, ∃ k ∈ F, ∃ a ∈ R, u = k * a ∧ p k = p u) (hρ : ∀ k ∈ F, ρ k = 1)
    (Cl : Type) [Fintype Cl] (y : Cl → Hf) (hy : Bridge.IsReps (p.comp Γ.subtype) J y)
    (hfin : ∀ k, Finite (Bridge.stab (p.comp Γ.subtype) J (y k))) (h : H) (w : W) :
    ∃ f ∈ Bridge.AdForms (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ, ∃ r : Cl → H, (∀ k, r k ∈ F) ∧
      Bridge.IsReps (p.comp Γ.subtype) J (fun k => p (r k)) ∧
      ∀ {G' X : Type} [Group G'] (x₀ : X) (om : H × G' →* Module.End ℂ (X → ℂ)) (Λ : W →ₗ[ℂ] (X → ℂ)),
        (∀ γ ∈ Γ, ∀ z v, om (γ, 1) (om z (Λ v)) x₀ = om z (Λ v) x₀) → (∀ a ∈ R, ∀ v, om (a, 1) (Λ v) = Λ (ρ a v)) →
        (∀ k ∈ F, ∀ hk : p k ∈ J, ∀ v, om (k, 1) (Λ v) = ((χ ⟨p k, hk⟩ : ℂˣ) : ℂ)⁻¹ • Λ v) →
        ∀ g : G', ∑ k, ((J.relIndex J : ℕ) : ℂ)⁻¹ * ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p (r k))) : ℕ) : ℂ)⁻¹ *
          om (r k, g) (Λ (f (p (r k)))) x₀ = om (h, g) (Λ w) x₀ := by
  obtain ⟨h₀, hh₀, a, ha, rfl, -⟩ := hdec h
  obtain ⟨y', c₀, hy', e₀⟩ := exists_isReps_through _ _ hy (p h₀)
  have hlift : ∀ z : Hf, ∃ k ∈ F, p k = z := fun z => by
    obtain ⟨u, hu⟩ := hp z
    obtain ⟨k, hk, -, -, -, e⟩ := hdec u
    exact ⟨k, hk, e.trans hu⟩
  choose σ hσ hσ' using hlift
  let r : Cl → H := Function.update (fun k => σ (y' k)) c₀ h₀
  have hr : ∀ k, r k ∈ F ∧ p (r k) = y' k := fun k => by
    by_cases hk : k = c₀
    · subst hk
      simp only [r, Function.update_self]
      exact ⟨hh₀, e₀.symm⟩
    · simp only [r, Function.update_of_ne hk]
      exact ⟨hσ _, hσ' _⟩
  have hr0 : r c₀ = h₀ := Function.update_self _ _ _
  have hyr : (fun k => p (r k)) = y' := funext fun k => (hr k).2
  have hf0 := finite_stab _ _ hy hfin (p h₀)
  obtain ⟨f, hf, hz, hv⟩ := exists_traceForm (p.comp Γ.subtype) (ρ.comp Γ.subtype) J χ (p h₀) hf0 (ρ a w)
  refine ⟨f, hf, r, fun k => (hr k).1, by rw [hyr]; exact hy', fun {G' X} _ x₀ om Λ hom hΛa hΛk g => ?_⟩
  rw [Finset.sum_eq_single c₀ ?_ (fun h => absurd (Finset.mem_univ _) h)]
  · let L₀ : W →ₗ[ℂ] ℂ := (LinearMap.proj x₀ : (X → ℂ) →ₗ[ℂ] ℂ) ∘ₗ (om (h₀, g)) ∘ₗ Λ
    have hL₀ : ∀ v, L₀ v = om (h₀, g) (Λ v) x₀ := fun v => rfl
    have key := hv L₀ fun γ hγ => ?_
    · have hN : ((Nat.card (Bridge.stab (p.comp Γ.subtype) J (p h₀)) : ℕ) : ℂ) ≠ 0 :=
        Nat.cast_ne_zero.2 (Nat.card_pos).ne'
      have e1 : (h₀ * a, g) = ((h₀, g) : H × G') * (a, 1) := by rw [Prod.mk_mul_mk, mul_one]
      rw [hr0, Subgroup.relIndex_self, Nat.cast_one, inv_one, one_mul, ← hL₀, key, inv_mul_cancel_left₀ hN, hL₀, e1,
        map_mul, Module.End.mul_apply, hΛa a ha]
    · generalize ρ a w = v
      obtain ⟨k, hk, b, hb, e, e'⟩ := hdec ((γ : H)⁻¹ * h₀)
      have hκ : h₀⁻¹ * k ∈ F := mul_mem (inv_mem hh₀) hk
      have eκ : p (h₀⁻¹ * k) = ((p h₀)⁻¹ * (p.comp Γ.subtype) γ * p h₀)⁻¹ := by
        show p (h₀⁻¹ * k) = ((p h₀)⁻¹ * p γ * p h₀)⁻¹
        rw [map_mul, e', map_mul, map_inv, map_inv]
        group
      have hκ' : p (h₀⁻¹ * k) ∈ J := by rw [eκ]; exact inv_mem hγ
      have eχ : ((χ ⟨_, hκ'⟩ : ℂˣ) : ℂ)⁻¹ = χ ⟨_, hγ⟩ := by
        rw [show (⟨_, hκ'⟩ : J) = ⟨_, hγ⟩⁻¹ from Subtype.ext eκ, map_inv, Units.val_inv_eq_inv_val, inv_inv]
      have eρ : (ρ.comp Γ.subtype) γ⁻¹ v = ρ b v := by
        have h1 := congrArg ρ e
        rw [map_mul, map_mul, hρ _ hh₀, hρ _ hk, mul_one, one_mul] at h1
        rw [← h1]
        rfl
      have e3 : ((h₀, g) : H × G') * (h₀⁻¹ * k, 1) * (b, 1) = (((γ : H)⁻¹, 1) : H × G') * (h₀, g) := by
        rw [Prod.mk_mul_mk, Prod.mk_mul_mk, Prod.mk_mul_mk, mul_inv_cancel_left, e, mul_one, mul_one, one_mul]
      rw [hL₀, hL₀, map_smul, eρ, ← eχ, ← hΛk _ hκ hκ', ← hΛa b hb, ← Module.End.mul_apply, ← Module.End.mul_apply,
        ← map_mul, ← map_mul, e3, map_mul]
      exact hom _ (inv_mem γ.2) _ _
  · intro k _ hk
    rw [hz _ ?_, map_zero, map_zero]
    · simp
    · intro hex
      obtain ⟨j, -, hu⟩ := hy' (y' k)
      refine hk ((hu k ⟨1, 1, by simp⟩).trans (hu c₀ ?_).symm)
      show ∃ (γ : Γ) (m : J), y' k = (p.comp Γ.subtype) γ * y' c₀ * m
      rw [e₀, ← (hr k).2]
      exact hex

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 T0 A Ks _ _ _ R hlev hmod hth i t h w`. Use `(hth.thF i t).elim fun thP hPF => ?_` and prove the remaining obligations. Use `(exists_form_sum (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i)) (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hmo …` and prove the remaining obligations. Establish `hf : f ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ` using `hf0.1`. Use `(LinearMap.mem_range.1 ((hmod.HV i t).2.1.ge hf)).elim fun x hx => ⟨x, fun u g => ?_⟩` and prove the remaining obligations.

Establish `hlaw : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J, R.ωP i t (k, 1) (R.vP i t) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t`. Introduce `k hkf hk`. Establish `hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i) (Formalism.IndefR.Lev.flag1L (R.datVt i t))` using `hk`. Establish `hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k` using `⟨hkf, hl.1, Subgroup.mem_bot.1 hl.2⟩`. Establish `hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1` using `⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩`.

Use `(GlobalTheory.VecInv.omega_lifts_vP R hlev hmod.inf hth.ωP hth.vP i t 1 k 1 hκ hκ').trans ?_` and prove the remaining obligations. Conclude with `congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t) (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm`. Establish `hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J, ∀ P, R.ωP i t (k, 1) (R.ptP i t P) = (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P` using `fun k hk hk' => GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hmod.inf (hth.ωP i t) _ _ _ _ _ (hth.pt_theta i t) k hk 1 (one_mem _) _ (hlaw k hk hk')`. Establish `key` using `GlobalTheory.LiftUnfold.integral_theta (hth.ωP i t) (D.sp.V_sig _) (hmod.vpos i) (R.cV i) (hmod.cV i) (R.βV i) (R.datVt i t) (fun _ => Iff.rfl) hf (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) ∘ₗ R.ioP i …`. Establish `key2` using `hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t) (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A))) (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun γ hγ z v => (hth.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hth.ωP i t). …`.

Establish `h1` using `congrFun (hPF.2 x u) g`. Establish `h2` using `hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g`. Use `h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))` and prove the remaining obligations. Rewrite using `[← hx]`. Both sides reduce to the same expression.
-/
theorem exists_thF_eq_thetaKO : ∀ (D : D7) (G : Type) [Group G] [Fintype G] (Pl0 T0 : Type) (A : Formalism.L2.DIV.FamIn D.what₂.LL G Pl0 T0 D.R.m) (Ks : Type) [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks), R.toLevCh.Is A.μ0 → R.IsModels → R.IsThP → ∀ (i : Fin D.R.m) (t : T0) (h : GA D (Vc D i)) (w : (R.cV i).W), ∃ x : (R.HV i t).H, ∀ (u : ∀ ρ, lowT (R.MW i (sg0 D A)) ρ) (g : GA D (Wc D i)), R.thF i t x (fun ρ => u ρ) g = thetaKO (R.ωP i t) h g (R.ptP i t (R.ioP i (PiTensorProduct.tprod ℂ u) w)) := by
  intro D G _ _ Pl0 T0 A Ks _ _ _ R hlev hmod hth i t h w
  refine (hth.thF i t).elim fun thP hPF => ?_
  refine (exists_form_sum (finHom (Vc D i)).rangeRestrict (finHom (Vc D i)).rangeRestrict_surjective (GQ (Vc D i))
    (GfC (Vc D i)) (GinfC (Vc D i)) (R.cV i).ρ (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ
    (GlobalTheory.LiftUnfold.exists_fin_mul_real (Vc D i)) (hmod.cV i).1 _ (R.B.L i t).pres.y (R.B.L i t).pres.reps
    (fun c => Finite.of_equiv _ ((R.B.L i t).pres.stabI c).toEquiv) h w).elim fun f hf0 => hf0.2.elim fun r hr => ?_
  have hf : f ∈ Bridge.AdForms (Bridge.ratF (Vc D i)) (R.cV i).coef.ρ
      (levEnv _ (R.βV i) (R.datVt i t)).J (levEnv _ (R.βV i) (R.datVt i t)).χ := hf0.1
  refine (LinearMap.mem_range.1 ((hmod.HV i t).2.1.ge hf)).elim fun x hx => ⟨x, fun u g => ?_⟩
  have hlaw : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J,
      R.ωP i t (k, 1) (R.vP i t) =
        (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.vP i t := by
    intro k hkf hk
    have hl : Formalism.IndefR.Lev.finE (Vc D i) k ∈ Formalism.L2.DIV.lev D.sp.cm (Vc D i).gram (R.βV i)
        (Formalism.IndefR.Lev.flag1L (R.datVt i t)) := hk
    have hκ : Formalism.IndefR.Lev.IsLevelLift (Vc D i) (R.βV i) (R.datVt i t) 1 k := ⟨hkf, hl.1, Subgroup.mem_bot.1 hl.2⟩
    have hκ' : Formalism.IndefR.Lev.IsLevelLift (Wc D i) (R.βW i) (R.datWp i R.triv) 1 1 :=
      ⟨Subgroup.one_mem _, by rw [map_one]; exact Subgroup.one_mem _, by rw [map_one]; exact Formalism.L2.DIV.rTup_one⟩
    refine (GlobalTheory.VecInv.omega_lifts_vP R hlev hmod.inf hth.ωP hth.vP i t 1 k 1 hκ hκ').trans ?_
    exact congrArg (fun z : ℂˣ => (z : ℂ)⁻¹ • R.vP i t)
      (Formalism.IndefR.Lev.levFn_flag1 (V := Vc D i) (β := R.βV i) (L := R.datVt i t) (Formalism.IndefR.Lev.finE (Vc D i) k)).symm
  have hfin : ∀ k ∈ GfC (Vc D i), ∀ hk : fin (Vc D i) k ∈ (levEnv _ (R.βV i) (R.datVt i t)).J, ∀ P,
      R.ωP i t (k, 1) (R.ptP i t P) =
      (((levEnv (Vc D i) (R.βV i) (R.datVt i t)).χ ⟨fin (Vc D i) k, hk⟩ : ℂˣ) : ℂ)⁻¹ • R.ptP i t P := fun k hk hk' =>
    GlobalTheory.FiniteFock.om_pureTensorO_of_finite R.ψ R.θ (Vc D i) (Wc D i) _ _ (R.ωP i t) hmod.inf
      (hth.ωP i t) _ _ _ _ _ (hth.pt_theta i t) k hk 1 (one_mem _) _ (hlaw k hk hk')
  have key := GlobalTheory.LiftUnfold.integral_theta (hth.ωP i t) (D.sp.V_sig _) (hmod.vpos i) (R.cV i) (hmod.cV i) (R.βV i)
    (R.datVt i t) (fun _ => Iff.rfl) hf
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u)) (fun w => hth.pt_theta i t _)
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _)
    (hmod.νV i t) _ _ r le_rfl (by rw [Subgroup.relIndex_self]; exact one_ne_zero) hr.2.1 hr.1 g
  have key2 := hr.2.2 (0 : WO (Vc D i) (Wc D i)) (R.ωP i t)
    (pureTensorO R.ψ R.θ (Vc D i) (Wc D i) (fun _ => 1) (cart (R.MW i (sg0 D A))) (R.BV i) (onb (R.MW i (sg0 D A)))
      (R.vP i t) ∘ₗ R.ioP i (PiTensorProduct.tprod ℂ u))
    (fun γ hγ z v => (hth.ωP i t).om_aut γ hγ 1 (one_mem _) _ ((hth.ωP i t).om_pres _ _ (hth.pt_theta i t _)))
    (fun a ha w => (hth.ioP i t).1 a ha _ w) (fun k hk hk' w => hfin k hk hk' _) g
  have h1 := congrFun (hPF.2 x u) g
  have h2 := hPF.1.eq ((R.extV i t).rangeRestrict x) (PiTensorProduct.tprod ℂ u) g
  refine h1.trans (h2.trans (Eq.trans ?_ (key.trans key2)))
  rw [← hx]
  rfl

end GlobalTheory.TraceLift
