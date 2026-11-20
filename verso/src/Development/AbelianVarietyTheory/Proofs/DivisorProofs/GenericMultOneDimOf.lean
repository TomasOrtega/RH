import Mathlib
import Formalism.LocalToGlobal.Divisibility.DefGroup
import Formalism.LocalToGlobal.Divisibility.GoodPartHermitianSpec
import Development.AbelianVarietyTheory.Definitions.Divisors.SplitDoublingNBlock
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.GenericMultiplicityOne

noncomputable section

namespace GlobalTheory.GenericProduct

open Formalism.L2.DIV GlobalTheory.FinGL GlobalTheory.IndefiniteRowSideFullHecke.GenericMultiplicityOne NumberField Module

def OneGenericVector : Prop :=
  ∀ (F : Type) [Field F] [Fintype F] (ψ : AddChar F ℂ), ψ ≠ 1 →
    ∀ (r : ℕ) (V : Type) [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V] (b : Fin r → ℕ)
      (σ : Representation ℂ (blockTri (κ := F) b) V), IsCuspDatum b σ → whDim ψ (parInd b σ) = 1

section Twist

variable {K P V : Type} [Field K] [Group P] [AddCommGroup V] [Module K V]

def twistInv (τ : Representation K P V) (c : P →* Kˣ) : Representation K P V where
  toFun h := (((c h)⁻¹ : Kˣ) : K) • τ h
  map_one' := by simp
  map_mul' x y := by
    rw [map_mul, map_mul, mul_inv, Units.val_mul, smul_mul_smul_comm]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem twistInv_apply (τ : Representation K P V) (c : P →* Kˣ) (h : P) :
    twistInv τ c h = (((c h)⁻¹ : Kˣ) : K) • τ h := rfl

/- English proof (translation)
Establish `hc : (Nat.card P : K) ≠ 0` using `Nat.cast_ne_zero.2 Nat.card_pos.ne'`. Use `letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc`. Use `letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)`. Establish `h` using `Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)`. Rewrite using `[← h, mul_inv_cancel_left₀ hc]`.

Use `Finset.sum_congr rfl fun x _ => ?_` and prove the remaining obligations. Rewrite using `[Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]`.
-/
theorem sum_trace_mul_inv [Fintype P] [CharZero K] [FiniteDimensional K V] (τ : Representation K P V) (c : P →* Kˣ) :
    ∑ h : P, LinearMap.trace K V (τ h) * (((c h)⁻¹ : Kˣ) : K) =
      (Nat.card P : K) * (finrank K (twistInv τ c).invariants : K) := by
  have hc : (Nat.card P : K) ≠ 0 := Nat.cast_ne_zero.2 Nat.card_pos.ne'
  letI : Invertible (Nat.card P : K) := invertibleOfNonzero hc
  letI : Invertible (Fintype.card P : K) := invertibleOfNonzero (by rw [← Nat.card_eq_fintype_card]; exact hc)
  have h := Representation.card_inv_mul_sum_char_eq_finrank (twistInv τ c)
  rw [← h, mul_inv_cancel_left₀ hc]
  refine Finset.sum_congr rfl fun x _ => ?_
  rw [Representation.character, twistInv_apply, map_smul, smul_eq_mul, mul_comm]

end Twist

/- English proof (translation)
Establish `h` using `sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))`. Establish `e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants = eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g)`. Use extensionality with `v`. Simplify using `only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]`. Establish `key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔ τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v)`.

Introduce `g`. Establish `hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ)` using `rfl`. Rewrite using `[hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]`. Both sides reduce to the same expression. Conclude with `⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩`.

Rewrite `h` using `[e]`. Conclude with `h`.
-/
theorem sum_unip_eq {F : Type} [Field F] {r : ℕ} [Fintype (unip F r)] {V : Type} [AddCommGroup V] [Module ℂ V]
    [FiniteDimensional ℂ V] (ψ : AddChar F ℂ) (τ : Representation ℂ (GL (Fin r) F) V) :
    ∑ h : unip F r, LinearMap.trace ℂ V (τ h) * (((addCharHom ψ (supHom F r) h)⁻¹ : ℂˣ) : ℂ) =
      (Nat.card (unip F r) : ℂ) * (whDim ψ τ : ℂ) := by
  have h := sum_trace_mul_inv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))
  have e : (twistInv (τ.comp (unip F r).subtype) (addCharHom ψ (supHom F r))).invariants =
      eig τ (unip F r : Set (GL (Fin r) F)) fun g => ψ (edgeSum supEdge g) := by
    ext v
    simp only [Representation.mem_invariants, eig, Submodule.mem_iInf, LinearMap.mem_ker, twistInv_apply,
      LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, sub_eq_zero]
    have key : ∀ g : unip F r, ((((addCharHom ψ (supHom F r) g)⁻¹ : ℂˣ) : ℂ) • (τ.comp (unip F r).subtype g) v = v ↔
        τ g v = ψ (edgeSum supEdge (g : GL (Fin r) F)) • v) := by
      intro g
      have hv : ψ (edgeSum supEdge (g : GL (Fin r) F)) = ((addCharHom ψ (supHom F r) g : ℂˣ) : ℂ) := rfl
      rw [hv, Units.val_inv_eq_inv_val, inv_smul_eq_iff₀ (Units.ne_zero _)]
      rfl
    exact ⟨fun H g hg => (key ⟨g, hg⟩).1 (H ⟨g, hg⟩), fun H g => (key g).2 (H g.1 g.2)⟩
  rw [e] at h
  exact h

def piEquiv {ι : Type} {G : ι → Type} [∀ i, Group (G i)] (H : ∀ i, Subgroup (G i)) :
    (Subgroup.pi Set.univ H) ≃ ∀ i, H i where
  toFun x i := ⟨x.1 i, x.2 i (Set.mem_univ _)⟩
  invFun y := ⟨fun i => (y i).1, fun i _ => (y i).2⟩
  left_inv _ := rfl
  right_inv _ := rfl

attribute [local instance] resField finite_res

/- English proof (translation)
Introduce `E _ _ Pg r K _ _ s ψ hψ χ hχ`. Take `⟨b, V, i1, i2, i3, σ, hσ, hs⟩` from `hχ`. Use `letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _`. Use `letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _`. Apply `s.injective` to reduce the goal to its premises.

Set `ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ` to `fun PP => s.toMonoidHom.compAddChar (ψ PP.1)`. Establish `hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1`. Introduce `PP h`. Use `hψ PP.1 PP.2 ?_` and prove the remaining obligations. Use extensionality with `x`.

Apply `s.injective` to reduce the goal to its premises. Use `DFunLike.congr_fun h x` as an intermediate fact. Simplify `this` using `[ψ']`. Set `e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r` to `piEquiv fun PP : ↥Pg => unip (kP PP.1) r`. Set `f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ` to `fun PP h => LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) * (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)`.

Establish `hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ)`. Introduce `PP`. Use `letI : Fintype (kP PP.1) := Fintype.ofFinite _`. Use `haveI := finite_parInd (b PP) (σ PP)`. Establish `h1` using `sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))`.

Rewrite `h1` using `[hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one]`. Conclude with `h1`. Establish `hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP)`. Introduce `h`. Establish `hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP)`.

Conclude with `MonoidHom.finset_prod_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h`. Rewrite using `[map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib, ← Finset.prod_mul_distrib]`. Use `Finset.prod_congr rfl fun PP _ => ?_` and prove the remaining obligations. Simplify using `only [f, Units.val_inv_eq_inv_val]`. Both sides reduce to the same expression.

Rewrite using `[map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod, ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]`. Conclude with `Fintype.sum_equiv e _ _ fun _ => rfl`.
-/
theorem genericMultOne (hL : OneGenericVector) : GenericMultOne := by
  classical
  intro E _ _ Pg r K _ _ s ψ hψ χ hχ
  obtain ⟨b, V, i1, i2, i3, σ, hσ, hs⟩ := hχ
  letI : Fintype (P0 Pg r ψ).H := Fintype.ofFinite _
  letI : ∀ PP : ↥Pg, Fintype (unip (kP PP.1) r) := fun PP => Fintype.ofFinite _
  apply s.injective
  let ψ' : ∀ PP : ↥Pg, AddChar (kP PP.1) ℂ := fun PP => s.toMonoidHom.compAddChar (ψ PP.1)
  have hψ' : ∀ PP : ↥Pg, ψ' PP ≠ 1 := by
    intro PP h
    refine hψ PP.1 PP.2 ?_
    ext x
    apply s.injective
    have := DFunLike.congr_fun h x
    simpa [ψ'] using this
  let e : (P0 Pg r ψ).H ≃ ∀ PP : ↥Pg, unip (kP PP.1) r := piEquiv fun PP : ↥Pg => unip (kP PP.1) r
  let f : ∀ PP : ↥Pg, unip (kP PP.1) r → ℂ := fun PP h =>
    LinearMap.trace ℂ _ (parInd (F := kP PP.1) (b PP) (σ PP) h) *
      (((addCharHom (ψ' PP) (supHom (kP PP.1) r) h)⁻¹ : ℂˣ) : ℂ)
  have hf : ∀ PP : ↥Pg, ∑ h, f PP h = (Nat.card (unip (kP PP.1) r) : ℂ) := by
    intro PP
    letI : Fintype (kP PP.1) := Fintype.ofFinite _
    haveI := finite_parInd (b PP) (σ PP)
    have h1 := sum_unip_eq (ψ' PP) (parInd (F := kP PP.1) (b PP) (σ PP))
    rw [hL (kP PP.1) (ψ' PP) (hψ' PP) r (V PP) (b PP) (σ PP) (hσ PP), Nat.cast_one, mul_one] at h1
    exact h1
  have hterm : ∀ h : (P0 Pg r ψ).H, s (χ (h : G0 Pg r) * ((((P0 Pg r ψ).chi h)⁻¹ : Kˣ) : K)) = ∏ PP, f PP (e h PP) := by
    intro h
    have hchi : (P0 Pg r ψ).chi h = ∏ PP : ↥Pg, addCharHom (ψ PP.1) (supHom (kP PP.1) r) (e h PP) := by
      exact MonoidHom.finset_prod_apply (fun PP : ↥Pg => (addCharHom (ψ PP.1) (supHom (kP PP.1) r)).comp
        (LevelP.prj (fun PP : ↥Pg => unip (kP PP.1) r) PP)) Finset.univ h
    rw [map_mul, hs, hchi, Units.val_inv_eq_inv_val, map_inv₀, Units.coe_prod, map_prod, ← Finset.prod_inv_distrib,
      ← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun PP _ => ?_
    simp only [f, Units.val_inv_eq_inv_val]
    rfl
  rw [map_sum, Finset.sum_congr rfl fun h _ => hterm h, map_natCast, Nat.card_congr e, Nat.card_pi, Nat.cast_prod,
    ← Finset.prod_congr rfl fun PP _ => hf PP, Fintype.prod_sum]
  exact Fintype.sum_equiv e _ _ fun _ => rfl

end GlobalTheory.GenericProduct
