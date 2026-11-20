import Mathlib
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HeisenbergWeightSpaceIrreducible
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsProjectiveRep
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.CubeVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.IsNsmul
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.QkToAkU
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.FamMod
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PhiGenPf
import Development.AbelianVarietyTheory.Definitions.Uniformization.PsiScal
open CategoryTheory CategoryTheory.Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UU

namespace GlobalTheory.ThetaIrred

/- English proof (translation)
Use `letI := (MulEquiv.isField (Field.toIsField F) σ.symm.toMulEquiv).toField`. Use `haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R σ`. Establish `h0 : Nat.card A ≠ 0` using `fun h => hcard (by rw [h, Nat.cast_zero])`. Use `haveI : Finite A := Nat.finite_of_card_ne_zero h0`. Use `haveI : Module.Finite R V := Module.finite_of_finrank_pos (Nat.pos_of_ne_zero fun h => h0 (by rw [← hdim, h]; rfl))`.

Establish `hc : (Nat.card A : R) ≠ 0` using `fun h => hcard (σ.injective (by rw [map_natCast, h, map_zero]))`. Set `W : Submodule R V` to `{ carrier := {v | j v ∈ U} add_mem' := fun {a b} ha hb => by show j (a + b) ∈ U`. Rewrite using `[map_add]`. Conclude with `U.add_mem ha hb`. Use the proof step `zero_mem' := by show j 0 ∈ U`.

Rewrite using `[map_zero]`. Conclude with `U.zero_mem`. Use the proof step `smul_mem' := fun c v hv => by show j (c • v) ∈ U`. Rewrite using `[← σ.apply_symm_apply c, hj]`. Conclude with `U.smul_mem _ hv }`.

Establish `hone : ∃ c : Rˣ, ∀ v, (1 : V ≃ₗ[R] V) v = (c : R) • Φ 1 v`. Take `⟨c, hc⟩` from `hmul 1 1`. Use `⟨c, fun v => (Φ 1).injective ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, ← hc, _root_.mul_one]`. Both sides reduce to the same expression.

Establish `key` using `GlobalTheory.heisenberg_weightSpace_irreducible R A V e Φ hc hdim hmul hcomm hnd ⊥ 1 (fun t => by`. Take `rfl : t = 1` from `Subsingleton.elim _ _`. Conclude with `hone)`. Use the proof step `(fun _ => ⊤)`. Use the proof step `(fun χ v => ⟨fun _ t => by`.

Take `rfl : t = 1` from `Subsingleton.elim _ _`. Rewrite using `[map_one, map_one, Units.val_one, one_smul]`. Use the proof step `rfl, fun _ => trivial⟩)`. Use `1 W le_top (fun h _ v hv => hU h v hv)`. Use `key.imp (fun h => ?_) (fun h => ?_)` and prove the remaining obligations.

Use `(Submodule.eq_bot_iff _).2 fun x hx => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `j.surjective x`. Establish `hv : v ∈ W` using `hx`. Rewrite `hv` using `[h, Submodule.mem_bot]`. Rewrite using `[hv, map_zero]`.

Use `Submodule.eq_top_iff'.2 fun x => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `j.surjective x`. Conclude with `(h ▸ Submodule.mem_top : v ∈ W)`.
-/
theorem irreducible_of_ringEquiv (F : Type) [Field F] [IsAlgClosed F] (R : Type) [CommRing R] (σ : F ≃+* R)
    (A : Type) [CommGroup A] (V : Type) [AddCommGroup V] [Module R V] (E : Type) [AddCommGroup E] [Module F E]
    (j : V ≃+ E) (hj : ∀ (c : F) v, j (σ c • v) = c • j v) (e : A → A → Rˣ) (Φ : A → (V ≃ₗ[R] V))
    (hcard : (Nat.card A : F) ≠ 0) (hdim : Module.finrank R V ^ 2 = Nat.card A)
    (hmul : ∀ a b, ∃ c : Rˣ, ∀ v, Φ (a * b) v = (c : R) • Φ a (Φ b v))
    (hcomm : ∀ a b v, Φ a (Φ b v) = (e a b : R) • Φ b (Φ a v)) (hnd : ∀ a, (∀ b, e a b = 1) → a = 1)
    (U : Submodule F E) (hU : ∀ a v, j v ∈ U → j (Φ a v) ∈ U) : U = ⊥ ∨ U = ⊤ := by
  letI := (MulEquiv.isField (Field.toIsField F) σ.symm.toMulEquiv).toField
  haveI : IsAlgClosed R := IsAlgClosed.of_ringEquiv F R σ
  have h0 : Nat.card A ≠ 0 := fun h => hcard (by rw [h, Nat.cast_zero])
  haveI : Finite A := Nat.finite_of_card_ne_zero h0
  haveI : Module.Finite R V := Module.finite_of_finrank_pos
    (Nat.pos_of_ne_zero fun h => h0 (by rw [← hdim, h]; rfl))
  have hc : (Nat.card A : R) ≠ 0 := fun h => hcard (σ.injective (by rw [map_natCast, h, map_zero]))
  let W : Submodule R V :=
    { carrier := {v | j v ∈ U}
      add_mem' := fun {a b} ha hb => by
        show j (a + b) ∈ U
        rw [map_add]; exact U.add_mem ha hb
      zero_mem' := by
        show j 0 ∈ U
        rw [map_zero]; exact U.zero_mem
      smul_mem' := fun c v hv => by
        show j (c • v) ∈ U
        rw [← σ.apply_symm_apply c, hj]; exact U.smul_mem _ hv }
  have hone : ∃ c : Rˣ, ∀ v, (1 : V ≃ₗ[R] V) v = (c : R) • Φ 1 v := by
    obtain ⟨c, hc⟩ := hmul 1 1
    refine ⟨c, fun v => (Φ 1).injective ?_⟩
    rw [map_smul, ← hc, _root_.mul_one]; rfl
  have key := GlobalTheory.heisenberg_weightSpace_irreducible R A V e Φ hc hdim hmul hcomm hnd ⊥ 1
    (fun t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      exact hone)
    (fun _ => ⊤)
    (fun χ v => ⟨fun _ t => by
      obtain rfl : t = 1 := Subsingleton.elim _ _
      rw [map_one, map_one, Units.val_one, one_smul]; rfl, fun _ => trivial⟩)
    1 W le_top (fun h _ v hv => hU h v hv)
  refine key.imp (fun h => ?_) (fun h => ?_)
  · refine (Submodule.eq_bot_iff _).2 fun x hx => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    have hv : v ∈ W := hx
    rw [h, Submodule.mem_bot] at hv
    rw [hv, map_zero]
  · refine Submodule.eq_top_iff'.2 fun x => ?_
    obtain ⟨v, rfl⟩ := j.surjective x
    exact (h ▸ Submodule.mem_top : v ∈ W)

/- English proof (translation)
Introduce `hL hL2 S _ P F _ _ p N hN`. Establish `hN1 : 1 ≤ N` using `Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])`. Take `⟨Φ, e, hdim, hact, hmul, hcomm, hnd⟩` from `GlobalTheory.ThetaRep.exists_projective_rep hL hL2 S P F p N hN`. Use `⟨fun x hx => (hact ⟨x, hx⟩).imp fun θ h => h.1, fun U hU => ?_⟩` and prove the remaining obligations. Set `G : Subgroup (Over.mk p ⟶ P.A)` to `(powMonoidHom N).ker`.

Establish `hcard : Nat.card G = N ^ (2 * P.g)` using `(hL.mulN _ P N hN1).2.2.2.2 F p hN`. Set `j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N` to `{ toFun := fun v => SecMod.mk _ (SecM.toSec P.A v) invFun := fun v => SecM.ofSec P.A v.sec left_inv := fun _ => rfl right_inv := fun _ => rfl map_add' := fun _ _ => rfl }`. Use `irreducible_of_ringEquiv F Γ((Over.mk p).left, ⊤) (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv G _ _ j (fun c v => rfl) (fun a b => e ⟨a.1, a.2⟩ ⟨b.1, b.2⟩) (fun a => Φ ⟨a.1, a.2⟩) ?_ ?_ (fun a b => hmul _ _ _ rfl) (fun a b => (hcomm _ _).2) (fun a h => Sub …` and prove the remaining obligations. Rewrite using `[hcard, Nat.cast_pow]`. Conclude with `pow_ne_zero _ hN`.

Rewrite using `[hdim, hcard, ← pow_mul, mul_comm]`. Take `⟨θ, h₁, h₂⟩` from `hact ⟨a.1, a.2⟩`. Conclude with `hU θ (by rw [h₁]; exact a.2) (j v) _ (h₂ v) hv`.
-/
theorem main : Laws → Laws2 → ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P : PolAV S) (F : Type) [Field F] [IsAlgClosed F] (p : Spec (CommRingCat.of F) ⟶ S) (N : ℕ), (N : F) ≠ 0 → (∀ x : Over.mk p ⟶ P.A, x ^ N = 1 → ∃ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt = x) ∧ ∀ U : Submodule F (EA P p N), (∀ θ : ThetaGrp P.A P.L (N : ℤ) (Over.mk p), θ.pt ^ N = 1 → ∀ v v' : EA P p N, IsActOf P.A P.L (N : ℤ) θ v.sec v'.sec → v ∈ U → v' ∈ U) → U = ⊥ ∨ U = ⊤ := by
  intro hL hL2 S _ P F _ _ p N hN
  have hN1 : 1 ≤ N := Nat.one_le_iff_ne_zero.2 fun e => hN (by rw [e, Nat.cast_zero])
  obtain ⟨Φ, e, hdim, hact, hmul, hcomm, hnd⟩ := GlobalTheory.ThetaRep.exists_projective_rep hL hL2 S P F p N hN
  refine ⟨fun x hx => (hact ⟨x, hx⟩).imp fun θ h => h.1, fun U hU => ?_⟩
  let G : Subgroup (Over.mk p ⟶ P.A) := (powMonoidHom N).ker
  have hcard : Nat.card G = N ^ (2 * P.g) := (hL.mulN _ P N hN1).2.2.2.2 F p hN
  let j : SecM P.A P.L N (Over.mk p) ≃+ EA P p N :=
    { toFun := fun v => SecMod.mk _ (SecM.toSec P.A v)
      invFun := fun v => SecM.ofSec P.A v.sec
      left_inv := fun _ => rfl
      right_inv := fun _ => rfl
      map_add' := fun _ _ => rfl }
  refine irreducible_of_ringEquiv F Γ((Over.mk p).left, ⊤)
    (Scheme.ΓSpecIso (CommRingCat.of F)).symm.commRingCatIsoToRingEquiv G _ _ j (fun c v => rfl)
    (fun a b => e ⟨a.1, a.2⟩ ⟨b.1, b.2⟩) (fun a => Φ ⟨a.1, a.2⟩) ?_ ?_ (fun a b => hmul _ _ _ rfl)
    (fun a b => (hcomm _ _).2) (fun a h => Subtype.ext (hnd ⟨a.1, a.2⟩ fun b => h ⟨b.1, b.2⟩)) U fun a v hv => ?_
  · rw [hcard, Nat.cast_pow]; exact pow_ne_zero _ hN
  · rw [hdim, hcard, ← pow_mul, mul_comm]
  · obtain ⟨θ, h₁, h₂⟩ := hact ⟨a.1, a.2⟩
    exact hU θ (by rw [h₁]; exact a.2) (j v) _ (h₂ v) hv

end GlobalTheory.ThetaIrred
