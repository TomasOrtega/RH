import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.NefFibOfIsNef

set_option autoImplicit false

noncomputable section

open CategoryTheory AlgebraicGeometry TopologicalSpace ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
  ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory GlobalTheory.CechPic

namespace GlobalTheory.ArInt

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Rewrite using `[interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0 ((cls_lbPow hN 0 _).trans (zero_nsmul _))]`. Simplify using the standard rewrite rules. Consider the case `succ n ih`.

Rewrite using `[interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN (by rw [cls_lbPow hN, cls_lbPow hN, succ_nsmul]), ih]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem interNum_one_lbPow_of_curve {κ : Type} [Field κ] {C : Scheme.{0}} [Algebra κ Γ(C, ⊤)]
    [IsProper (strHom κ C)] {H N : LB C} (hH : IsAmpleLB H) (hd : topologicalKrullDim C = 1)
    (hN : N.IsLB) (n : ℕ) :
    interNum κ (structureModule C) ![lbPow N n] = n * interNum κ (structureModule C) ![N] := by
  induction n with
  | zero =>
    rw [interNum_eq_zero_of_cls_eq_zero κ _ (isLB_vecOne (isLB_lbPow hN 0)) 0
      ((cls_lbPow hN 0 _).trans (zero_nsmul _))]
    simp
  | succ n ih =>
    rw [interNum_one_of_cls_eq_add hH hd (isLB_lbPow hN (n + 1)) (isLB_lbPow hN n) hN
      (by rw [cls_lbPow hN, cls_lbPow hN, succ_nsmul]), ih]
    push_cast
    ring

/- English proof (translation)
Introduce `k _ _ X p hp L m hm`. Take `⟨hpr, A, hA⟩` from `(isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp`. Establish `key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type) [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 → topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1`. Introduce `Z i _ _ κ _ _ _ hd`. Establish `: IsFinite (spMap (Int.castRingHom k))`.

Rewrite using `[spMap, IsFinite.SpecMap_iff]`. Conclude with `(RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance`. Establish `e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k)` using `specZIsTerminal.hom_ext _ _`. Establish `: IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ))` using `by rw [e]; infer_instance`. Establish `: IsProper (strHom κ Z)` using `IsProper.of_comp _ (spMap (Int.castRingHom κ))`.

Establish `hAZ` using `hA.pull_of_isClosedImmersion i`. Establish `hN : (L.B.pull i).IsLB` using `LB.isLB_pull L.isLB i`. Establish `e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 = interNum κ (structureModule Z) ![lbPow (L.B.pull i) m]` using `interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i) (isLB_vecOne (isLB_lbPow hN m)) fun j => by fin_cases j`. Conclude with `(cls_pull (L.pow m).isLB i _).trans ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))`. Establish `e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i]`.

Rewrite using `[topSelf_def]`. Use `congr 1`. Use function extensionality and compare the values at `j`. Use `fin_cases j`. Both sides reduce to the same expression.

Rewrite using `[e1, e2]`. Conclude with `interNum_one_lbPow_of_curve hAZ hd hN m`. Establish `hm' : (0 : ℤ) < m` using `by exact_mod_cast hm`. Prove the components needed by the constructor for the conclusion. Introduce `h Z i _ _ κ _ _ _ hd`.

Establish `h'` using `h Z i κ hd`. Rewrite `h'` using `[key Z i κ hd]`. Conclude with `(mul_nonneg_iff_of_pos_left hm').1 h'`. Introduce `h Z i _ _ κ _ _ _ hd`. Rewrite using `[key Z i κ hd]`.

Conclude with `mul_nonneg hm'.le (h Z i κ hd)`.
-/
theorem nefFib_pow_iff : ∀ (k : Type) [CommRing k] [Module.Finite ℤ k] (X : Scheme.{0})
    (p : X ⟶ Sp k), IsProjOver p → ∀ (L : HermLB p) (m : ℕ), 0 < m →
      (ArInt.NefFib (L.pow m) ↔ ArInt.NefFib L) := by
  intro k _ _ X p hp L m hm
  obtain ⟨hpr, A, hA⟩ := (isProjOver_iff_isProper_and_exists_isAmpleLB p).1 hp
  have key : ∀ (Z : Scheme.{0}) (i : Z ⟶ X) [IsClosedImmersion i] [IsIntegral Z] (κ : Type)
      [Field κ] [Finite κ] [Algebra κ Γ(Z, ⊤)], topologicalKrullDim Z = 1 →
      topSelfIntersection κ ((L.pow m).B.pull i) 1 = m * topSelfIntersection κ (L.B.pull i) 1 := by
    intro Z i _ _ κ _ _ _ hd
    have : IsFinite (spMap (Int.castRingHom k)) := by
      rw [spMap, IsFinite.SpecMap_iff]
      exact (RingHom.finite_algebraMap (A := ℤ) (B := k)).2 inferInstance
    have e : strHom κ Z ≫ spMap (Int.castRingHom κ) = i ≫ p ≫ spMap (Int.castRingHom k) :=
      specZIsTerminal.hom_ext _ _
    have : IsProper (strHom κ Z ≫ spMap (Int.castRingHom κ)) := by rw [e]; infer_instance
    have : IsProper (strHom κ Z) := IsProper.of_comp _ (spMap (Int.castRingHom κ))
    have hAZ := hA.pull_of_isClosedImmersion i
    have hN : (L.B.pull i).IsLB := LB.isLB_pull L.isLB i
    have e1 : topSelfIntersection κ ((L.pow m).B.pull i) 1 =
        interNum κ (structureModule Z) ![lbPow (L.B.pull i) m] :=
      interNum_congr_cls κ _ (fun _ => LB.isLB_pull (L.pow m).isLB i)
        (isLB_vecOne (isLB_lbPow hN m)) fun j => by
          fin_cases j
          exact (cls_pull (L.pow m).isLB i _).trans
            ((congrArg (pull i) (cls_lbPow L.isLB m (L.pow m).isLB)).trans
              ((map_nsmul (pull i) m _).trans (cls_lbPow hN m _).symm))
    have e2 : topSelfIntersection κ (L.B.pull i) 1 = interNum κ (structureModule Z) ![L.B.pull i] := by
      rw [topSelf_def]
      congr 1
      funext j
      fin_cases j
      rfl
    rw [e1, e2]
    exact interNum_one_lbPow_of_curve hAZ hd hN m
  have hm' : (0 : ℤ) < m := by exact_mod_cast hm
  constructor
  · intro h Z i _ _ κ _ _ _ hd
    have h' := h Z i κ hd
    rw [key Z i κ hd] at h'
    exact (mul_nonneg_iff_of_pos_left hm').1 h'
  · intro h Z i _ _ κ _ _ _ hd
    rw [key Z i κ hd]
    exact mul_nonneg hm'.le (h Z i κ hd)

end GlobalTheory.ArInt
