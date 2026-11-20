import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.LocGenOfTrivial
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsPrimitiveNormalisation
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.RigidifiedOfChart
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.IsReducedAlgebraOfSmoothOfIsNoetherianRing

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory
open scoped CategoryTheory.Obj
open GlobalTheory GlobalTheory.CM

noncomputable section

namespace GlobalTheory.CM.PairingIso

open GlobalTheory.KerPow

/- English proof (translation)
Take `⟨w, hw⟩` from `h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)`. Take `⟨t, ht⟩` from `H`. Take `⟨a, ha⟩` from `gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht`. Take `⟨c, hc, -⟩` from `exists_up ((isGen_iff w).1 hw) hQ hP a ha`. Conclude with `gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc`.
-/
theorem exists_gen_of_lbIso {X : Scheme.{0}} {P Q : LB X} (hP : P.IsLB) (hQ : Q.IsLB) (h : LBIso P Q)
    (H : ∃ t : LB.Gen P, t.IsGen) : ∃ t : LB.Gen Q, t.IsGen := by
  obtain ⟨w, hw⟩ := h.chartPull (chartPullId P) (chartPullPull Q (𝟙 X) (𝟙 X) rfl)
  obtain ⟨t, ht⟩ := H
  obtain ⟨a, ha⟩ := gen_chartPull (chartPullPull P (𝟙 X) (𝟙 X) rfl) t ht
  obtain ⟨c, hc, -⟩ := exists_up ((isGen_iff w).1 hw) hQ hP a ha
  exact gen_chartPull (chartPullUnpull Q _ (Category.id_comp _)) c hc

/- English proof (translation)
Substitute `e` using the available equality. Introduce `p`. Take `⟨i, hi⟩` from `exists_chart hL (a p)`. Conclude with `⟨a ⁻¹ᵁ L.U i, hi, ChartRig.exists_gen_pull L _ i hL fun y _ => y.2⟩`.
-/
theorem locGen_base {X Y B : Scheme.{0}} {L : LB X} (hL : L.IsLB) (π : Y ⟶ B) (a : B ⟶ X) {b : Y ⟶ X}
    (e : b = π ≫ a) : LocGen L π (fun _ : PUnit => b) (fun _ => 1) := by
  subst e
  intro p
  obtain ⟨i, hi⟩ := exists_chart hL (a p)
  exact ⟨a ⁻¹ᵁ L.U i, hi, ChartRig.exists_gen_pull L _ i hL fun y _ => y.2⟩

/- English proof (translation)
Establish `h' : LBIso (cubeLB B ![1, snd T A ≫ Φ] M) (cubeLB A ![fst T A ≫ x, snd T A] L)` using `LBIso.chartPull (PrimNorm.chartSquare M (lift (fst T A ≫ x) (snd T A)) (by rw [lift_fst_assoc, Category.assoc, hx, MonObj.comp_one]) (by rw [lift_snd_assoc])) (PrimNorm.chartSquare L (lift (fst T A ≫ x) (snd T A)) (by simp) (by simp)) h`. Establish `g₁ : ∃ t : LB.Gen (cubeLB B ![1, snd T A ≫ Φ] M), t.IsGen` using `hasGen_of_trivial hM fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])`. Establish `g₂ : HasGen L _ _` using `exists_gen_of_lbIso (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) h' g₁`. Establish `g₃ : LocGen L (fst T A).left (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left) (fun I => (-1) ^ (2 - I.down.card))` using `fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩`. Establish `b₁` using `locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl`.

Establish `b₀` using `locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left) (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)`. Establish `b` using `b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1]) fun U _ k => by simp [Fin.prod_univ_two]`. Use `eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)` and prove the remaining obligations. Rewrite using `[PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]`. Use `show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left * (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ = k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)`.

Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_zpow]`. Use `module`.
-/
theorem eq_one_of_comp_eq_one {S : Scheme.{0}} {A B : Over S} [GrpObj A] [GrpObj B] [IsCommMonObj A] [IsCommMonObj B]
    {L : LB A.left} {M : LB B.left} {Φ : A ⟶ B} (hL : L.IsLB) (hM : M.IsLB) (hK : Out.KTriv A L)
    (h : LamEq M Φ Φ L (𝟙 A) (𝟙 A)) {T : Over S} (x : T ⟶ A) (hx : x ≫ Φ = 1) : x = 1 := by
  have h' : LBIso (cubeLB B ![1, snd T A ≫ Φ] M) (cubeLB A ![fst T A ≫ x, snd T A] L) :=
    LBIso.chartPull
      (PrimNorm.chartSquare M (lift (fst T A ≫ x) (snd T A))
        (by rw [lift_fst_assoc, Category.assoc, hx, MonObj.comp_one]) (by rw [lift_snd_assoc]))
      (PrimNorm.chartSquare L (lift (fst T A ≫ x) (snd T A)) (by simp) (by simp)) h
  have g₁ : ∃ t : LB.Gen (cubeLB B ![1, snd T A ≫ Φ] M), t.IsGen :=
    hasGen_of_trivial hM fun U _ k => (PrimNorm.prod_square_id _ _ k).trans (by simp [PrimNorm.diff₂])
  have g₂ : HasGen L _ _ :=
    exists_gen_of_lbIso (DVR.linComb_isLB _ hM _ _) (DVR.linComb_isLB _ hL _ _) h' g₁
  have g₃ : LocGen L (fst T A).left
      (fun I : ULift.{0} (Finset (Fin 2)) => (psum A ![fst T A ≫ x, snd T A] I.down).left)
      (fun I => (-1) ^ (2 - I.down.card)) := fun _ => ⟨⊤, trivial, g₂.pull _ fun _ => rfl⟩
  have b₁ := locGen_base hL (fst T A).left x.left (b := (fst T A ≫ x).left) rfl
  have b₀ := locGen_base hL (fst T A).left (1 : T ⟶ A).left (b := (1 : T ⊗ A ⟶ A).left)
    (congrArg (fun q : T ⊗ A ⟶ A => q.left) (MonObj.comp_one (fst T A) : fst T A ≫ (1 : T ⟶ A) = 1).symm)
  have b := b₀.comb hL b₁ (φ'' := ![(1 : T ⊗ A ⟶ A).left, (fst T A ≫ x).left]) (ε'' := ![1, -1])
    fun U _ k => by simp [Fin.prod_univ_two]
  refine eq_one_of_locGen hK x (g₃.comb hL b fun U _ k => ?_)
  rw [PrimNorm.prod_square_id, Fin.prod_univ_two, Fin.prod_univ_two]
  show k ((fst T A ≫ x) * snd T A).left * (k (fst T A ≫ x).left)⁻¹ * (k (snd T A).left)⁻¹ * k (1 : T ⊗ A ⟶ A).left *
    (k (1 : T ⊗ A ⟶ A).left ^ (1 : ℤ) * k (fst T A ≫ x).left ^ (-1 : ℤ))⁻¹ =
    k ((fst T A ≫ x) * snd T A).left ^ (1 : ℤ) * k (snd T A).left ^ (-1 : ℤ)
  apply Additive.ofMul.injective
  simp only [ofMul_mul, ofMul_inv, ofMul_zpow]
  module

/- English proof (translation)
Introduce `S _ A B _ _ L M Φ hA hB hL hM hΦ hK h hs`. Use `hA.comm` as an intermediate fact. Use `hB.comm` as an intermediate fact. Use `hA.proper` as an intermediate fact. Use `hB.proper` as an intermediate fact.

Use `hB.smooth` as an intermediate fact. Establish `: Mono Φ` using `⟨fun {T} x y e => mul_inv_eq_one.1 (eq_one_of_comp_eq_one hL hM hK h (x * y⁻¹) (by`. Rewrite using `[MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]))⟩`. Establish `: Mono Φ.left` using `inferInstanceAs (Mono ((Over.forget S).map Φ))`. Establish `: IsReduced B.left` using `GlobalTheory.isReduced_of_smooth_of_isReduced B.hom`.

Establish `: IsProper (Φ.left ≫ B.hom)` using `by rw [Over.w]; infer_instance`. Establish `: IsProper Φ.left` using `IsProper.of_comp Φ.left B.hom`. Establish `: IsClosedImmersion Φ.left` using `(IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩`. Establish `: IsIso Φ.left` using `isIso_of_isClosedImmersion_of_surjective _`. Establish `: IsIso ((Over.forget _).map Φ)` using `‹_›`.

Conclude with `isIso_of_reflects_iso Φ (Over.forget _)`.
-/
theorem isIso_of_lamEq : ∀ (S : Scheme.{0}) [IsReduced S] (A B : Over S) [GrpObj A] [GrpObj B] (L : LB A.left) (M : LB B.left) (Φ : A ⟶ B), IsAbelianScheme A → IsAbelianScheme B → L.IsLB → M.IsLB → IsMonHom Φ → Out.KTriv A L → LamEq M Φ Φ L (𝟙 A) (𝟙 A) → Surjective Φ.left → IsIso Φ := by
  intro S _ A B _ _ L M Φ hA hB hL hM hΦ hK h hs
  have := hA.comm
  have := hB.comm
  have := hA.proper
  have := hB.proper
  have := hB.smooth
  have : Mono Φ := ⟨fun {T} x y e => mul_inv_eq_one.1 (eq_one_of_comp_eq_one hL hM hK h (x * y⁻¹) (by
    rw [MonObj.mul_comp, GrpObj.inv_comp, e, mul_inv_cancel]))⟩
  have : Mono Φ.left := inferInstanceAs (Mono ((Over.forget S).map Φ))
  have : IsReduced B.left := GlobalTheory.isReduced_of_smooth_of_isReduced B.hom
  have : IsProper (Φ.left ≫ B.hom) := by rw [Over.w]; infer_instance
  have : IsProper Φ.left := IsProper.of_comp Φ.left B.hom
  have : IsClosedImmersion Φ.left := (IsClosedImmersion.iff_isProper_and_mono _).2 ⟨‹_›, ‹_›⟩
  have : IsIso Φ.left := isIso_of_isClosedImmersion_of_surjective _
  have : IsIso ((Over.forget _).map Φ) := ‹_›
  exact isIso_of_reflects_iso Φ (Over.forget _)

end GlobalTheory.CM.PairingIso
end
