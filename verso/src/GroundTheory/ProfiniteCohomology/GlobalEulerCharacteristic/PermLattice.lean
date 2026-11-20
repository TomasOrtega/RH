import Mathlib
import GroundTheory.ProfiniteCohomology.LocalEulerCharacteristic.Additive
import GroundTheory.GlobalFields.HerbrandQuotients.Lattice
import GroundTheory.GlobalFields.HerbrandQuotients.SUnitsPerm
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLatticeDefs
import GroundTheory.ProfiniteCohomology.GlobalEulerCharacteristic.PermLatticeCharacter
set_option maxSynthPendingDepth 1

namespace GroundTheory.ProfCoh

open Module Representation GroundTheory.Global
open scoped TensorProduct

universe u v

section Character

variable {k : Type*} {Γ : Type*} [Field k] [Group Γ]

/- English proof (translation)
Use `Fintype.ofFinite X` as an intermediate fact. Rewrite using `[Representation.character, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k X), Matrix.trace]`. Simplify using `only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr, funPermRep_apply, Pi.single_apply]`. Rewrite using `[Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]`. Use `congr 2`.

Use extensionality with `x`. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedBy]`. Rewrite using `[inv_smul_eq_iff, eq_comm]`.
-/
theorem character_funPermRep (X : Type*) [MulAction Γ X] [Finite X] (γ : Γ) :
    (funPermRep k Γ X).character γ = Nat.card (MulAction.fixedBy X γ) := by
  classical
  have := Fintype.ofFinite X
  rw [Representation.character, LinearMap.trace_eq_matrix_trace k (Pi.basisFun k X), Matrix.trace]
  simp only [Matrix.diag, LinearMap.toMatrix_apply, Pi.basisFun_apply, Pi.basisFun_repr,
    funPermRep_apply, Pi.single_apply]
  rw [Finset.sum_boole, Nat.card_eq_fintype_card, Fintype.card_subtype]
  congr 2
  ext x
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, MulAction.mem_fixedBy]
  rw [inv_smul_eq_iff, eq_comm]

/- English proof (translation)
Use `Fintype.ofFinite X` as an intermediate fact. Use `Fintype.ofFinite X'` as an intermediate fact. Conclude with `nonempty_equiv_of_character_eq _ _ (funext fun γ => by`. Rewrite using `[character_funPermRep, character_funPermRep, h])`.
-/
theorem nonempty_equiv_funPermRep_of_card_fixedBy_eq [CharZero k] [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    Nonempty ((funPermRep k Γ X).Equiv (funPermRep k Γ X')) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  exact nonempty_equiv_of_character_eq _ _ (funext fun γ => by
    rw [character_funPermRep, character_funPermRep, h])

end Character

section Lattice

variable {Γ : Type*} [Group Γ]

/- English proof (translation)
Proceed by induction on `x using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul r f`. Use function extensionality and compare the values at `y`. Simplify using `[LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul]`.

Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]`.
-/
theorem piScalarRight_baseChange_funPermRep (X : Type*) [MulAction Γ X] [Fintype X]
    [DecidableEq X] (γ : Γ) (x : ℝ ⊗[ℤ] (X → ℤ)) :
    TensorProduct.piScalarRight ℤ ℝ ℝ X ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      funPermRep ℝ Γ X γ (TensorProduct.piScalarRight ℤ ℝ ℝ X x) := by
  induction x using TensorProduct.induction_on with
  | zero => simp
  | tmul r f =>
    funext y
    simp [LinearMap.baseChange_tmul, TensorProduct.piScalarRightHom_tmul]
  | add a b ha hb => rw [map_add, map_add, ha, hb, map_add, map_add]

/- English proof (translation)
Use `Fintype.ofFinite X` as an intermediate fact. Use `Fintype.ofFinite X'` as an intermediate fact. Take `⟨E⟩` from `nonempty_equiv_funPermRep_of_card_fixedBy_eq (k := ℝ) h`. Set `P` to `TensorProduct.piScalarRight ℤ ℝ ℝ X`. Set `P'` to `TensorProduct.piScalarRight ℤ ℝ ℝ X'`.

Set `e : ℝ ⊗[ℤ] (X → ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (X' → ℤ)` to `P.trans (E.toLinearEquiv.trans P'.symm)`. Establish `he : ∀ γ x, e ((funPermRep ℤ Γ X γ).baseChange ℝ x) = (funPermRep ℤ Γ X' γ).baseChange ℝ (e x)`. Introduce `γ x`. Apply `P'.injective` to reduce the goal to its premises. Simplify using `only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]`.

Rewrite using `[piScalarRight_baseChange_funPermRep, piScalarRight_baseChange_funPermRep, LinearEquiv.apply_symm_apply]`. Conclude with `LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' γ) (P x)`. Conclude with `exists_injective_intertwiner_of_real_equiv _ _ e he`.
-/
theorem exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq [Finite Γ] {X X' : Type*}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    ∃ φ : (X → ℤ) →ₗ[ℤ] (X' → ℤ), Function.Injective φ ∧
      (∃ n : ℤ, n ≠ 0 ∧ ∀ y, ∃ x, φ x = n • y) ∧
      ∀ γ x, φ (funPermRep ℤ Γ X γ x) = funPermRep ℤ Γ X' γ (φ x) := by
  classical
  have := Fintype.ofFinite X
  have := Fintype.ofFinite X'
  obtain ⟨E⟩ := nonempty_equiv_funPermRep_of_card_fixedBy_eq (k := ℝ) h
  let P := TensorProduct.piScalarRight ℤ ℝ ℝ X
  let P' := TensorProduct.piScalarRight ℤ ℝ ℝ X'
  let e : ℝ ⊗[ℤ] (X → ℤ) ≃ₗ[ℝ] ℝ ⊗[ℤ] (X' → ℤ) := P.trans (E.toLinearEquiv.trans P'.symm)
  have he : ∀ γ x, e ((funPermRep ℤ Γ X γ).baseChange ℝ x) =
      (funPermRep ℤ Γ X' γ).baseChange ℝ (e x) := by
    intro γ x
    apply P'.injective
    simp only [e, LinearEquiv.trans_apply, LinearEquiv.apply_symm_apply]
    rw [piScalarRight_baseChange_funPermRep, piScalarRight_baseChange_funPermRep,
      LinearEquiv.apply_symm_apply]
    exact LinearMap.congr_fun (E.toIntertwiningMap.isIntertwining' γ) (P x)
  exact exists_injective_intertwiner_of_real_equiv _ _ e he

end Lattice

namespace AdditiveFunction

variable {l : ℕ} {Γ : Type v} [Group Γ] (d : AdditiveFunction.{u} l Γ)

/- English proof (translation)
Set `_` to `funPermAction Γ X ℤ`. Establish `hl : (l : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne l`. Establish `htors : ∀ f : X → ℤ, l • f = 0 → f = 0` using `fun f hf => funext fun x => by`. Establish `h1` using `congrFun hf x`. Simplify using `only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1`.

Conclude with `(mul_eq_zero.1 h1).resolve_left hl`. Set `c : (X → ℤ) →ₗ[ℤ] (X → ZMod l)` to `LinearMap.pi fun x => (Int.castAddHom (ZMod l)).toIntLinearMap ∘ₗ LinearMap.proj x`. Establish `hc : ∀ f x, c f x = (f x : ZMod l)` using `fun _ _ => rfl`. Establish `hker : LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ)) ≤ LinearMap.ker c`. Introduce and unpack `_ ⟨f, rfl⟩`.

Rewrite using `[LinearMap.mem_ker]`. Use function extensionality and compare the values at `x`. Simplify using `[hc]`. Set `ψ` to `(LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))).liftQ c hker`. Establish `hψ : Function.Bijective (ψ.toAddMonoidHom.toZModLinearMap l)`.

Use `⟨?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `x hx`. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Establish `h1 : ∀ y, (l : ℤ) ∣ f y` using `fun y => by`.

Rewrite using `[← ZMod.intCast_zmod_eq_zero_iff_dvd]`. Conclude with `congrFun hx y`. Use `choose a ha using h1`. Rewrite using `[Submodule.Quotient.mk_eq_zero]`. Conclude with `⟨a, funext fun y => by simp [ha y]⟩`.

Use `⟨Submodule.Quotient.mk (fun x => ((y x).val : ℤ)), funext fun x => ?_⟩ show c _ x = y x` and prove the remaining obligations. Rewrite using `[hc, Int.cast_natCast, ZMod.natCast_zmod_val]`. Set `E : ModN (X → ℤ) l ≃ₗ[ZMod l] (X → ZMod l)` to `LinearEquiv.ofBijective _ hψ`. Establish `: Finite (ModN (X → ℤ) l)` using `Finite.of_equiv _ E.symm.toEquiv`. Rewrite using `[d.g_eq_of_torsion_trivial _ htors]`.

Use `d.toFun_congr _ _ E fun γ x => ?_` and prove the remaining obligations. Take `⟨f, rfl⟩` from `Submodule.Quotient.mk_surjective _ x`. Rewrite using `[modNRep_mk]`. Both sides reduce to the same expression.
-/
theorem g_funPermAction [NeZero l] (X : Type u) [MulAction Γ X] [Finite X] :
    letI := funPermAction Γ X ℤ
    d.g (X → ℤ) = d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) := by
  let _ := funPermAction Γ X ℤ
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have htors : ∀ f : X → ℤ, l • f = 0 → f = 0 := fun f hf => funext fun x => by
    have h1 := congrFun hf x
    simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left hl
  let c : (X → ℤ) →ₗ[ℤ] (X → ZMod l) :=
    LinearMap.pi fun x => (Int.castAddHom (ZMod l)).toIntLinearMap ∘ₗ LinearMap.proj x
  have hc : ∀ f x, c f x = (f x : ZMod l) := fun _ _ => rfl
  have hker : LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ)) ≤ LinearMap.ker c := by
    rintro _ ⟨f, rfl⟩
    rw [LinearMap.mem_ker]
    funext x
    simp [hc]
  let ψ := (LinearMap.range (LinearMap.lsmul ℤ (X → ℤ) (l : ℤ))).liftQ c hker
  have hψ : Function.Bijective (ψ.toAddMonoidHom.toZModLinearMap l) := by
    refine ⟨?_, fun y => ?_⟩
    · rw [injective_iff_map_eq_zero]
      intro x hx
      obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
      have h1 : ∀ y, (l : ℤ) ∣ f y := fun y => by
        rw [← ZMod.intCast_zmod_eq_zero_iff_dvd]
        exact congrFun hx y
      choose a ha using h1
      rw [Submodule.Quotient.mk_eq_zero]
      exact ⟨a, funext fun y => by simp [ha y]⟩
    · refine ⟨Submodule.Quotient.mk (fun x => ((y x).val : ℤ)), funext fun x => ?_⟩
      show c _ x = y x
      rw [hc, Int.cast_natCast, ZMod.natCast_zmod_val]
  let E : ModN (X → ℤ) l ≃ₗ[ZMod l] (X → ZMod l) := LinearEquiv.ofBijective _ hψ
  have : Finite (ModN (X → ℤ) l) := Finite.of_equiv _ E.symm.toEquiv
  rw [d.g_eq_of_torsion_trivial _ htors]
  refine d.toFun_congr _ _ E fun γ x => ?_
  obtain ⟨f, rfl⟩ := Submodule.Quotient.mk_surjective _ x
  rw [modNRep_mk]
  rfl

/- English proof (translation)
Take `⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩` from `exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq h`. Set `_` to `funPermAction Γ X ℤ`. Set `_` to `funPermAction Γ X' ℤ`. Establish `: Finite ((X' → ℤ) ⧸ φ.toAddMonoidHom.range)` using `finite_quotient_of_smul_mem _ hn fun y => by`. Take `⟨x, hx⟩` from `hrange y`.

Conclude with `⟨x, hx⟩`. Establish `hl : (l : ℤ) ≠ 0` using `by exact_mod_cast NeZero.ne l`. Establish `: Subsingleton (TorsN (X → ℤ) l)` using `⟨fun a b => Subtype.ext (by`. Establish `key : ∀ t : TorsN (X → ℤ) l, (t : X → ℤ) = 0` using `fun t => funext fun x => by`. Establish `h1` using `congrFun ((mem_ker_lsmul_iff l (t : X → ℤ)).1 t.2) x`.

Simplify using `only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1`. Conclude with `(mul_eq_zero.1 h1).resolve_left hl`. Rewrite using `[key a, key b])⟩`. Establish `: Finite (TorsN (X → ℤ) l)` using `Finite.of_subsingleton`. Establish `hg` using `d.g_eq_of_finite_cokernel φ.toAddMonoidHom (fun γ b => hcomm γ b) hφ`.

Rewrite using `[← d.g_funPermAction X, ← d.g_funPermAction X', hg]`.
-/
theorem toFun_funPermRep_eq_of_card_fixedBy_eq [NeZero l] [Finite Γ] {X X' : Type u}
    [MulAction Γ X] [MulAction Γ X'] [Finite X] [Finite X']
    (h : ∀ γ : Γ, Nat.card (MulAction.fixedBy X γ) = Nat.card (MulAction.fixedBy X' γ)) :
    d.toFun (X → ZMod l) (funPermRep (ZMod l) Γ X) =
      d.toFun (X' → ZMod l) (funPermRep (ZMod l) Γ X') := by
  obtain ⟨φ, hφ, ⟨n, hn, hrange⟩, hcomm⟩ :=
    exists_injective_intertwiner_funPermRep_of_card_fixedBy_eq h
  let _ := funPermAction Γ X ℤ
  let _ := funPermAction Γ X' ℤ
  have : Finite ((X' → ℤ) ⧸ φ.toAddMonoidHom.range) :=
    finite_quotient_of_smul_mem _ hn fun y => by
      obtain ⟨x, hx⟩ := hrange y
      exact ⟨x, hx⟩
  have hl : (l : ℤ) ≠ 0 := by exact_mod_cast NeZero.ne l
  have : Subsingleton (TorsN (X → ℤ) l) := ⟨fun a b => Subtype.ext (by
    have key : ∀ t : TorsN (X → ℤ) l, (t : X → ℤ) = 0 := fun t => funext fun x => by
      have h1 := congrFun ((mem_ker_lsmul_iff l (t : X → ℤ)).1 t.2) x
      simp only [Pi.smul_apply, Pi.zero_apply, nsmul_eq_mul] at h1
      exact (mul_eq_zero.1 h1).resolve_left hl
    rw [key a, key b])⟩
  have : Finite (TorsN (X → ℤ) l) := Finite.of_subsingleton
  have hg := d.g_eq_of_finite_cokernel φ.toAddMonoidHom (fun γ b => hcomm γ b) hφ
  rw [← d.g_funPermAction X, ← d.g_funPermAction X', hg]

end AdditiveFunction

end GroundTheory.ProfCoh
