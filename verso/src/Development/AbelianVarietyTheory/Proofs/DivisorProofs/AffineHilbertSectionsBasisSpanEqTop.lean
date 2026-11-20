import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BasicIff
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine

open AlgebraicGeometry CategoryTheory CategoryTheory.Limits Opposite

noncomputable section

namespace GlobalTheory.HilbAff

/- English proof (translation)
Establish `sq : IsPullback (pullback.fst (str A B) y.1) (pullback.snd (str A B) y.1) (str A B) y.1` using `IsPullback.of_hasPullback _ _`. Use `haveI : IsAffineHom (pullback.snd (str A B) y.1) := isAffineHom_isStableUnderBaseChange.of_isPullback sq inferInstance`. Establish `hpo` using `ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) W.2 (by simp) (by simp)`. Establish `hQ : IsAffineOpen (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))` using `W.2.preimage _`. Establish `hsurj` using `y.2.1.subschemeι_app_surjective ⟨_, hQ⟩`.

Set `R` to `Γ(Spec (CommRingCat.of A), ⊤)`. Set `S` to `Γ(Spec (CommRingCat.of B), ⊤)`. Set `T` to `Γ(Z, (W : Z.Opens))`. Set `Q` to `Γ(pullback (str A B) y.1, pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))`. Use `letI : Algebra R S := (show R ⟶ S from (str A B).app ⊤).hom.toAlgebra`.

Use `letI : Algebra R T := (y.1.appLE ⊤ W (by simp)).hom.toAlgebra`. Use `letI : Algebra T Q := ((pullback.snd (str A B) y.1).app W).hom.toAlgebra`. Use `letI : Algebra S Q := (show S ⟶ Q from (pullback.fst (str A B) y.1).appLE (str A B ⁻¹ᵁ ⊤) _ (by simp)).hom.toAlgebra`. Use `letI : Algebra R Q := ((y.1.appLE ⊤ W (by simp)) ≫ (pullback.snd (str A B) y.1).app W).hom.toAlgebra`. Use `haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)`.

Use `haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq (fun x => by`. Establish `h` using `congr($(hpo.w).hom x)`. Conclude with `h.symm)`. Use `haveI : Algebra.IsPushout R T S Q := (CommRingCat.isPushout_iff_isPushout).mp hpo.flip`. Establish `hbc` using `Algebra.IsPushout.out (R := R) (S := T) (R' := S) (S' := Q)`.

Establish `key : ∀ s : S, (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom (algebraMap S Q s) = ((y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)).hom s`. Introduce `s`. Establish `h : (Scheme.Hom.appLE (pullback.fst (str A B) y.fst) (str A B ⁻¹ᵁ ⊤) (pullback.snd (str A B) y.fst ⁻¹ᵁ ↑W) (by simp)) ≫ y.2.1.subschemeι.app _ = (y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤ (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)`. Rewrite using `[Scheme.Hom.app_eq_appLE]`. Conclude with `Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _`.

Conclude with `congrArg (fun f => (CommRingCat.Hom.hom f) s) h`. Establish `hι : ∀ (t : T) (n : Q), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom (t • n) = t • (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom n)`. Introduce `t n`. Rewrite using `[Algebra.smul_def, map_mul, Algebra.smul_def]`. Use `congr 1`.

Establish `term : ∀ (c : A) (j : Fin N), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c * e j))) = (algebraMap R T ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)) • gen A B y W (e j)`. Introduce `c j`. Establish `h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c) = algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)` using `congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).hom c)`. Rewrite using `[map_mul, h1, map_mul, ← IsScalarTower.algebraMap_apply R S Q, IsScalarTower.algebraMap_apply R T Q, ← Algebra.smul_def, hι, key]`. Both sides reduce to the same expression.

Establish `hB : ∀ b : B, (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j))`. Introduce `b`. Rewrite using `[← e.sum_repr b, map_sum, map_sum, map_sum]`. Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.smul_def, term]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)`. Use `eq_top_iff.mpr fun x _ => ?_` and prove the remaining obligations. Take `⟨q, rfl⟩` from `hsurj x`. Use `hbc.inductionOn q (fun q => (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom q) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j))) ?_ ?_ ?_ ?_` and prove the remaining obligations. Use `zero_mem (Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))` and compare the differences between its conclusion and the goal.

Conclude with `map_zero _`. Introduce `s`. Take `⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b = s` from `⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s, by simp⟩`. Conclude with `hB b`. Introduce `t n hn`.

Rewrite using `[hι]`. Conclude with `Submodule.smul_mem _ _ hn`. Introduce `a b ha hb`. Rewrite using `[map_add]`. Conclude with `add_mem ha hb`.
-/
theorem span_gen_eq_top (A B : Type) [CommRing A] [CommRing B] [Algebra A B] (N r : ℕ)
    (e : Module.Basis (Fin N) A B) (Z : Scheme.{0}) (y : (functor A B r).obj (op Z))
    (W : Z.affineOpens) :
    Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) = ⊤ := by
  have sq : IsPullback (pullback.fst (str A B) y.1) (pullback.snd (str A B) y.1) (str A B) y.1 :=
    IsPullback.of_hasPullback _ _
  haveI : IsAffineHom (pullback.snd (str A B) y.1) :=
    isAffineHom_isStableUnderBaseChange.of_isPullback sq inferInstance
  have hpo := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) W.2
    (by simp) (by simp)
  have hQ : IsAffineOpen (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens)) := W.2.preimage _
  have hsurj := y.2.1.subschemeι_app_surjective ⟨_, hQ⟩
  let R := Γ(Spec (CommRingCat.of A), ⊤)
  let S := Γ(Spec (CommRingCat.of B), ⊤)
  let T := Γ(Z, (W : Z.Opens))
  let Q := Γ(pullback (str A B) y.1, pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))
  letI : Algebra R S := (show R ⟶ S from (str A B).app ⊤).hom.toAlgebra
  letI : Algebra R T := (y.1.appLE ⊤ W (by simp)).hom.toAlgebra
  letI : Algebra T Q := ((pullback.snd (str A B) y.1).app W).hom.toAlgebra
  letI : Algebra S Q :=
    (show S ⟶ Q from (pullback.fst (str A B) y.1).appLE (str A B ⁻¹ᵁ ⊤) _ (by simp)).hom.toAlgebra
  letI : Algebra R Q :=
    ((y.1.appLE ⊤ W (by simp)) ≫ (pullback.snd (str A B) y.1).app W).hom.toAlgebra
  haveI : IsScalarTower R T Q := IsScalarTower.of_algebraMap_eq (fun _ => rfl)
  haveI : IsScalarTower R S Q := IsScalarTower.of_algebraMap_eq (fun x => by
    have h := congr($(hpo.w).hom x)
    exact h.symm)
  haveI : Algebra.IsPushout R T S Q := (CommRingCat.isPushout_iff_isPushout).mp hpo.flip
  have hbc := Algebra.IsPushout.out (R := R) (S := T) (R' := S) (S' := Q)

  have key : ∀ s : S, (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom
      (algebraMap S Q s) = ((y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp)).hom s := by
    intro s
    have h : (Scheme.Hom.appLE (pullback.fst (str A B) y.fst) (str A B ⁻¹ᵁ ⊤)
      (pullback.snd (str A B) y.fst ⁻¹ᵁ ↑W) (by simp)) ≫ y.2.1.subschemeι.app _ =
        (y.2.1.subschemeι ≫ pullback.fst (str A B) y.1).appLE ⊤
        (subStr A B y ⁻¹ᵁ (W : Z.Opens)) (by simp) := by
      rw [Scheme.Hom.app_eq_appLE]
      exact Scheme.Hom.appLE_comp_appLE _ _ _ _ _ _ _
    exact congrArg (fun f => (CommRingCat.Hom.hom f) s) h
  have hι : ∀ (t : T) (n : Q), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (t • n) =
      t • (show Sec A B y W from
        (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ (W : Z.Opens))).hom n) := by
    intro t n
    rw [Algebra.smul_def, map_mul, Algebra.smul_def]
    congr 1
  have term : ∀ (c : A) (j : Fin N), (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q
        ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c * e j))) =
      (algebraMap R T ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c)) • gen A B y W (e j) := by
    intro c j
    have h1 : (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom (algebraMap A B c) =
        algebraMap R S ((Scheme.ΓSpecIso (CommRingCat.of A)).inv.hom c) :=
      congr($(Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap A B))).hom c)
    rw [map_mul, h1, map_mul, ← IsScalarTower.algebraMap_apply R S Q,
      IsScalarTower.algebraMap_apply R T Q, ← Algebra.smul_def, hι, key]
    rfl
  have hB : ∀ b : B, (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom (algebraMap S Q ((Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b))) ∈
      Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)) := by
    intro b
    rw [← e.sum_repr b, map_sum, map_sum, map_sum]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [Algebra.smul_def, term]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨j, rfl⟩)
  refine eq_top_iff.mpr fun x _ => ?_
  obtain ⟨q, rfl⟩ := hsurj x
  refine hbc.inductionOn q (fun q => (show Sec A B y W from (y.2.1.subschemeι.app (pullback.snd (str A B) y.1 ⁻¹ᵁ
      (W : Z.Opens))).hom q) ∈ Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    ?_ ?_ ?_ ?_
  · convert zero_mem (Submodule.span Γ(Z, W) (Set.range fun j => gen A B y W (e j)))
    exact map_zero _
  · intro s
    obtain ⟨b, rfl⟩ : ∃ b, (Scheme.ΓSpecIso (CommRingCat.of B)).inv.hom b = s :=
      ⟨(Scheme.ΓSpecIso (CommRingCat.of B)).hom.hom s, by simp⟩
    exact hB b
  · intro t n hn
    rw [hι]
    exact Submodule.smul_mem _ _ hn
  · intro a b ha hb
    rw [map_add]
    exact add_mem ha hb

end GlobalTheory.HilbAff
