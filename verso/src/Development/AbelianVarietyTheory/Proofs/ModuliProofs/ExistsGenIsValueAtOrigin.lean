import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.TopLePreimageOfValAtNeZero

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct

namespace GlobalTheory.OriginValue

/- English proof (translation)
Distinguish the cases in `hW : ⊤ ≤ x ⁻¹ᵁ W`. Establish `h1` using `h hW`. Rewrite `h1` using `[valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt]`. Establish `h2` using `(ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1`. Establish `e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W` using `le_antisymm hW le_top`.

Establish `: IsIso (homOfLE hW)` using `⟨⟨homOfLE le_top, rfl, rfl⟩⟩`. Establish `: IsIso (x.appLE W ⊤ hW)`. Unfold `Scheme.Hom.appLE`. Use `infer_instance`. Conclude with `(ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2`.

Establish `hb : W = ⊥`. Rewrite `hW` using `[top_le_preimage_iff_mem]`. Use `le_bot_iff.1 fun y hy => ?_` and prove the remaining obligations. Take `⟨q, rfl⟩` from `x.surjective y`. Establish `: q = (default : PrimeSpectrum ℂ)` using `Subsingleton.elim (α := PrimeSpectrum ℂ) _ _`.

Substitute `this` using the available equality. Conclude with `(hW hy).elim`. Substitute `hb` using the available equality. Conclude with `Subsingleton.elim _ _`.
-/
theorem eq_of_valAt'_eq_of_isIso {X : Scheme.{0}} (x : Sp ℂ ⟶ X) [IsIso x] (W : X.Opens) (f g : Γ(X, W))
    (h : ⊤ ≤ x ⁻¹ᵁ W → valAt' x W f = valAt' x W g) : f = g := by
  by_cases hW : ⊤ ≤ x ⁻¹ᵁ W
  · have h1 := h hW
    rw [valAt'_eq_valAt x hW, valAt'_eq_valAt x hW, valAt, valAt] at h1
    have h2 := (ConcreteCategory.bijective_of_isIso (Scheme.ΓSpecIso (CommRingCat.of ℂ)).hom).1 h1
    have e : (⊤ : (Sp ℂ).Opens) = x ⁻¹ᵁ W := le_antisymm hW le_top
    have : IsIso (homOfLE hW) := ⟨⟨homOfLE le_top, rfl, rfl⟩⟩
    have : IsIso (x.appLE W ⊤ hW) := by
      unfold Scheme.Hom.appLE
      infer_instance
    exact (ConcreteCategory.bijective_of_isIso (x.appLE W ⊤ hW)).1 h2
  · have hb : W = ⊥ := by
      rw [top_le_preimage_iff_mem] at hW
      refine le_bot_iff.1 fun y hy => ?_
      obtain ⟨q, rfl⟩ := x.surjective y
      have : q = (default : PrimeSpectrum ℂ) := Subsingleton.elim (α := PrimeSpectrum ℂ) _ _
      subst this
      exact (hW hy).elim
    subst hb
    exact Subsingleton.elim _ _

def constFnHom {X : Scheme.{0}} (f : X ⟶ Sp ℂ) (U : X.Opens) : ℂ →+* Γ(X, U) :=
  ((Scheme.ΓSpecIso (CommRingCat.of ℂ)).inv ≫ f.appLE ⊤ U (fun _ _ => trivial)).hom

/- English proof (translation)
The claim follows from `(top_le_preimage_comp x φ _).2 (top_le_preimage_mono x (LB.wchart_le L (fun _ : Fin 1 => φ) j 0) h)`.
-/
theorem top_le_preimage_wchart_one {X Y : Scheme.{0}} (L : LB X) (φ : Y ⟶ X) (x : Sp ℂ ⟶ Y) (j : Fin 1 → L.ι)
    (h : ⊤ ≤ x ⁻¹ᵁ LB.wchart L (fun _ : Fin 1 => φ) j) : ⊤ ≤ (x ≫ φ) ⁻¹ᵁ L.U (j 0) :=
  (top_le_preimage_comp x φ _).2 (top_le_preimage_mono x (LB.wchart_le L (fun _ : Fin 1 => φ) j 0) h)

/- English proof (translation)
The claim follows from `(u.ker 0).2 u.Λ.zero_mem`.
-/
theorem ex_zero {A : Over (Sp ℂ)} [GrpObj A] {L : LB A.left} {g : ℕ} (u : HolUnif A L g) : u.ex 0 = 1 :=
  (u.ker 0).2 u.Λ.zero_mem

open Classical in

def unitOrOne (c : ℂ) : ℂˣ := if h : c ≠ 0 then Units.mk0 c h else 1

/- English proof (translation)
Rewrite using `[unitOrOne, dif_pos h]`. Both sides reduce to the same expression.
-/
theorem unitOrOne_val {c : ℂ} (h : c ≠ 0) : (unitOrOne c : ℂ) = c := by
  rw [unitOrOne, dif_pos h]; rfl

/- English proof (translation)
Introduce `P u a T _ p`. Set `x : Sp ℂ ⟶ T.left` to `p.left`. Establish `hx : x ≫ T.hom = 𝟙 _` using `Over.w p`. Establish `: IsIso x`. Establish `: x = inv T.hom` using `IsIso.eq_inv_of_inv_hom_id hx`.

Rewrite using `[this]`. Use `infer_instance`. Establish `h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0`. Rewrite using `[ex_zero, MonObj.comp_one]`. Establish `h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left` using `congrArg CommaMorphism.left h1`.

Establish `hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j → ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0)` using `fun j h => by`. Use `top_le_preimage_wchart_one P.L _ x j h` as an intermediate fact. Rewrite `this` using `[h1']`. Then use the resulting hypothesis. Set `τ : LB.Gen (LB.LinComb P.L (Y` to `T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) := ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩`. Establish `hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j → valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a` using `fun j h => by`.

Use `(valAt'_constFn x T.hom hx _ _ h).trans ?_` and prove the remaining obligations. Rewrite using `[Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]`. Use `⟨τ, fun i j => ?_, fun s f hs j => ?_⟩` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises. Use `eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_` and prove the remaining obligations.

Take `⟨hi, hj⟩` from `(top_le_preimage_inf x _ _).1 h`. Rewrite using `[Units.val_mul, valAt'_mul]`. Use `((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_` and prove the remaining obligations. Establish `e2` using `(valAt'_res x inf_le_right _ h).trans (hτ j hj)`. Use `Eq.trans ?_ (congrArg _ e2.symm)` and prove the remaining obligations.

Establish `hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0))` using `(top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩`. Rewrite using `[u.fr_compat _ _ _ hij, mul_zpow]`. Use `congr 1`. Simplify using `only [LB.LinComb, Fin.prod_univ_one]`. Use `Eq.trans ?_ (valAt'_zpow x h _ a).symm` and prove the remaining obligations.

Use `congr 1`. Use `Eq.trans ?_ (valAt'_res x _ _ h).symm` and prove the remaining obligations. Use `Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm` and prove the remaining obligations. Rewrite using `[h1']`. Use `eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_` and prove the remaining obligations.

Rewrite using `[valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]`. Use `(valAt'_comp x _ _ _).trans ?_` and prove the remaining obligations. Establish `h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0)`. Rewrite using `[Out.ptSecT, comp_lift, Category.comp_id, h1]`. Establish `h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left` using `congrArg CommaMorphism.left h2`.

Rewrite using `[h2']`. Conclude with `hs j 0 (hch j h)`.
-/
theorem exists_gen_isValueAt_origin : ∀ (P : Out.PolAV (Sp ℂ)) (u : HolUnif P.A P.L P.g) (a : ℤ) (T : Over (Sp ℂ)) [IsIso T.hom] (p : 𝟙_ (Over (Sp ℂ)) ⟶ T), ∃ τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)), τ.IsGen ∧ ∀ (s : LB.Sec (Out.LPow P.A P.L a T)) (f : (Fin P.g → ℂ) → ℂ), (∀ (j : Fin 1 → P.L.ι) z, ⊤ ≤ (u.ex z).left ⁻¹ᵁ P.L.U (j 0) → valAt' (lift p (u.ex z)).left ((Out.LPow P.A P.L a T).U j) (s.f j) = f z * u.fr (j 0) z ^ (a : ℤ)) → Out.IsValueAt P.A P.L a s 1 τ (constFn T.hom ⊤ (f 0)) := by
  intro P u a T _ p
  let x : Sp ℂ ⟶ T.left := p.left
  have hx : x ≫ T.hom = 𝟙 _ := Over.w p
  have : IsIso x := by
    have : x = inv T.hom := IsIso.eq_inv_of_inv_hom_id hx
    rw [this]; infer_instance
  have h1 : p ≫ (1 : T ⟶ P.A) = u.ex 0 := by
    rw [ex_zero, MonObj.comp_one]
  have h1' : x ≫ (1 : T ⟶ P.A).left = (u.ex 0).left := congrArg CommaMorphism.left h1
  have hch : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      ⊤ ≤ (u.ex 0).left ⁻¹ᵁ P.L.U (j 0) := fun j h => by
    have := top_le_preimage_wchart_one P.L _ x j h
    rwa [h1'] at this
  let τ : LB.Gen (LB.LinComb P.L (Y := T.left) (K := Fin 1) (fun _ => (1 : T ⟶ P.A).left) (fun _ => a)) :=
    ⟨fun j => Units.map (constFnHom T.hom _).toMonoidHom (unitOrOne (u.fr (j 0) 0) ^ a)⟩
  have hτ : ∀ j : Fin 1 → P.L.ι, ⊤ ≤ x ⁻¹ᵁ LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j →
      valAt' x (LB.wchart P.L (fun _ : Fin 1 => (1 : T ⟶ P.A).left) j) (τ.s j).val = u.fr (j 0) 0 ^ a := fun j h => by
    refine (valAt'_constFn x T.hom hx _ _ h).trans ?_
    rw [Units.val_zpow_eq_zpow_val, unitOrOne_val (u.fr_ne _ _ (hch j h))]
  refine ⟨τ, fun i j => ?_, fun s f hs j => ?_⟩
  · apply Units.ext
    refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    obtain ⟨hi, hj⟩ := (top_le_preimage_inf x _ _).1 h
    rw [Units.val_mul, valAt'_mul]
    refine ((valAt'_res x inf_le_left _ h).trans (hτ i hi)).trans ?_
    have e2 := (valAt'_res x inf_le_right _ h).trans (hτ j hj)
    refine Eq.trans ?_ (congrArg _ e2.symm)
    have hij : ⊤ ≤ (u.ex 0).left ⁻¹ᵁ (P.L.U (i 0) ⊓ P.L.U (j 0)) :=
      (top_le_preimage_inf (u.ex 0).left _ _).2 ⟨hch i hi, hch j hj⟩
    rw [u.fr_compat _ _ _ hij, mul_zpow]
    congr 1
    simp only [LB.LinComb, Fin.prod_univ_one]
    refine Eq.trans ?_ (valAt'_zpow x h _ a).symm
    congr 1
    refine Eq.trans ?_ (valAt'_res x _ _ h).symm
    refine Eq.trans ?_ (valAt'_comp x (1 : T ⟶ P.A).left (P.L.U (i 0) ⊓ P.L.U (j 0)) (P.L.g (i 0) (j 0)).val).symm
    rw [h1']
  · refine eq_of_valAt'_eq_of_isIso x _ _ _ fun h => ?_
    rw [valAt'_mul, hτ j h, valAt'_map x _ _ h, valAt'_map x _ _ h, valAt'_constFn x T.hom hx _ _ le_top]
    refine (valAt'_comp x _ _ _).trans ?_
    have h2 : p ≫ Out.ptSecT P.A (1 : T ⟶ P.A) = lift p (u.ex 0) := by
      rw [Out.ptSecT, comp_lift, Category.comp_id, h1]
    have h2' : x ≫ (Out.ptSecT P.A (1 : T ⟶ P.A)).left = (lift p (u.ex 0)).left := congrArg CommaMorphism.left h2
    rw [h2']
    exact hs j 0 (hch j h)

end GlobalTheory.OriginValue
