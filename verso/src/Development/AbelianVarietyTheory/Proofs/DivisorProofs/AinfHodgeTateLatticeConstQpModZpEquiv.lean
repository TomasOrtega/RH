import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.GhostFrobenius
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ToSpanSingletonConstGenSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HodgeTateSandwichOfPrismaticDieudonne
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PadicRingHomEqCanonical

set_option autoImplicit false

noncomputable section

open CategoryTheory Opposite Matrix GlobalTheory GlobalTheory.PDivGroup GlobalTheory.Sandwich GlobalTheory.IndefiniteRowSideFullHecke.EpsilonPairingZeta GlobalTheory.PDivLat

namespace GlobalTheory.PDivLat

/- English proof (translation)
Set `g : ℤ_[p] →+* O` to `{ toFun := fun s => ghost p O n (ofPadic p O s) map_one' := by simp only [map_one, ghost, iterate_map_one] map_mul' := fun a b => by simp only [map_mul, ghost_mul] map_zero' := by simp only [map_zero, ghost_zero] map_add' := fun a b => by simp only [map_add, ghost_add] }`. Conclude with `congrArg (fun f : ℤ_[p] →+* O => f s) (padicToO_unique p O g)`.
-/
theorem ghost_ofPadic (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] (n : ℕ) (s : ℤ_[p]) :
    ghost p O n (ofPadic p O s) = padicToO p O s := by
  let g : ℤ_[p] →+* O :=
    { toFun := fun s => ghost p O n (ofPadic p O s)
      map_one' := by simp only [map_one, ghost, iterate_map_one]
      map_mul' := fun a b => by simp only [map_mul, ghost_mul]
      map_zero' := by simp only [map_zero, ghost_zero]
      map_add' := fun a b => by simp only [map_add, ghost_add] }
  exact congrArg (fun f : ℤ_[p] →+* O => f s) (padicToO_unique p O g)

/- English proof (translation)
Rewrite using `[hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by`. Rewrite using `[← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,`. Use the proof step `LinearMap.id_apply]`.
-/
theorem hodgeTate_constGen (p : ℕ) [Fact p.Prime] (O : Type) [CommRing O] :
    hodgeTate (const p O) (constGen p O) = constDlogT p O := by
  rw [hodgeTate_eq_omegaDualMap, show constHom _ (constGen p O) = 𝟙 _ by
    rw [← LinearEquiv.eq_symm_apply, constHom_symm_apply, tateMap_id], omegaDualMap_id,
    LinearMap.id_apply]

/- English proof (translation)
Introduce `p _ C _ _ _ v O _ _ _ _ _ _ ε hε`. Establish `hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1` using `fun e he => IsIdempotentElem.iff_eq_zero_or_one.1 he`. Set `φ : ℤ_[p] ≃ₗ[ℤ_[p]] (const p O).Tate` to `LinearEquiv.ofBijective _ (toSpanSingleton_constGen_bijective p O hO)`. Establish `hφ : ∀ s, φ s = s • constGen p O` using `fun s => rfl`. Take `⟨eω, heω⟩` from `DieudonneSandwich.exists_equiv_constDlogT (p := p) (O := O)`.

Set `f : latt (const p O) →ₗ[Ainf p O] Ainf p O` to `{ toFun := fun y => y.1 (constGen p O) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Use `⟨LinearEquiv.ofBijective f ⟨fun y z h => ?_, fun a => ?_⟩, fun _ => rfl⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `t`.

Take `⟨s, rfl⟩` from `φ.surjective t`. Rewrite using `[hφ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]`. Conclude with `congrArg _ h`. Set `y : TDual (const p O)` to `{ toFun := fun t => ofPadic p O (φ.symm t) * a map_add' := fun t t' => by rw [map_add, map_add, add_mul] map_smul' := fun c t => by`. Rewrite using `[map_smul, smul_eq_mul, map_mul, smul_eq_mul, mul_assoc] }`.

Establish `hy : y ∈ latt (const p O)` using `fun n => by`. Use `⟨ghost p O n a • eω.symm.toLinearMap, fun t => ?_⟩` and prove the remaining obligations. Take `⟨s, rfl⟩` from `φ.surjective t`. Express the relevant statement in the definitionally equal form `ghost p O n (ofPadic p O (φ.symm (φ s)) * a) = _`. Rewrite using `[LinearEquiv.symm_apply_apply, ghost_mul, ghost_ofPadic, hφ, hodgeTate_smul (padicToO p O), hodgeTate_constGen, LinearMap.smul_apply, LinearEquiv.coe_toLinearMap, map_smul, ← heω, LinearEquiv.symm_apply_apply, smul_eq_mul, smul_eq_mul, mul_one, mul_comm]`.

Use `⟨⟨y, hy⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ofPadic p O (φ.symm (constGen p O)) * a = a`. Establish `: φ.symm (constGen p O) = 1` using `φ.symm_apply_eq.2 (by rw [hφ, one_smul])`. Rewrite using `[this, map_one, one_mul]`.
-/
theorem latt_const_equiv : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C]
    (v : Valuation C NNReal) (O : Type) [CommRing O] [Algebra O C] [Fact ¬IsUnit (p : O)]
    [IsAdicComplete (Ideal.span {(p : O)}) O] [IsDomain O], v.Integers O →
    ∀ (ε : PreTilt O p) (hε : IsPrimitiveSystem ε),
    ∃ e : latt (const p O) ≃ₗ[Ainf p O] Ainf p O, ∀ y, e y = y.1 (constGen p O) := by
  intro p _ C _ _ _ v O _ _ _ _ _ _ ε hε
  have hO : ∀ e : O, IsIdempotentElem e → e = 0 ∨ e = 1 := fun e he =>
    IsIdempotentElem.iff_eq_zero_or_one.1 he

  let φ : ℤ_[p] ≃ₗ[ℤ_[p]] (const p O).Tate :=
    LinearEquiv.ofBijective _ (toSpanSingleton_constGen_bijective p O hO)
  have hφ : ∀ s, φ s = s • constGen p O := fun s => rfl
  obtain ⟨eω, heω⟩ := DieudonneSandwich.exists_equiv_constDlogT (p := p) (O := O)
  let f : latt (const p O) →ₗ[Ainf p O] Ainf p O :=
    { toFun := fun y => y.1 (constGen p O)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  refine ⟨LinearEquiv.ofBijective f ⟨fun y z h => ?_, fun a => ?_⟩, fun _ => rfl⟩
  · apply Subtype.ext
    apply LinearMap.ext
    intro t
    obtain ⟨s, rfl⟩ := φ.surjective t
    rw [hφ, LinearMap.map_smulₛₗ, LinearMap.map_smulₛₗ]
    exact congrArg _ h
  · let y : TDual (const p O) :=
      { toFun := fun t => ofPadic p O (φ.symm t) * a
        map_add' := fun t t' => by rw [map_add, map_add, add_mul]
        map_smul' := fun c t => by
          rw [map_smul, smul_eq_mul, map_mul, smul_eq_mul, mul_assoc] }
    have hy : y ∈ latt (const p O) := fun n => by
      refine ⟨ghost p O n a • eω.symm.toLinearMap, fun t => ?_⟩
      obtain ⟨s, rfl⟩ := φ.surjective t
      change ghost p O n (ofPadic p O (φ.symm (φ s)) * a) = _
      rw [LinearEquiv.symm_apply_apply, ghost_mul, ghost_ofPadic, hφ,
        hodgeTate_smul (padicToO p O), hodgeTate_constGen, LinearMap.smul_apply,
        LinearEquiv.coe_toLinearMap, map_smul, ← heω, LinearEquiv.symm_apply_apply, smul_eq_mul,
        smul_eq_mul, mul_one, mul_comm]
    refine ⟨⟨y, hy⟩, ?_⟩
    change ofPadic p O (φ.symm (constGen p O)) * a = a
    have : φ.symm (constGen p O) = 1 := φ.symm_apply_eq.2 (by rw [hφ, one_smul])
    rw [this, map_one, one_mul]

end GlobalTheory.PDivLat
