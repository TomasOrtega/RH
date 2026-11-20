import Development.EtaleCohomology.KummerTheory.FinalTheorems

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.KummerTheory.LHCut

def shvHomOf {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F G : SlShv Λ S)
    (f : ∀ U : Over S, F.obj.obj (op U) →ₗ[ULift.{1} Λ] G.obj.obj (op U))
    (hf : ∀ (V U : Over S) (g : V ⟶ U) x, f V ((F.obj.map g.op).hom x) = (G.obj.map g.op).hom (f U x)) : F ⟶ G :=
  ⟨{ app := fun U => ModuleCat.ofHom (f U.unop)
     naturality := by intro U V g; ext x; exact hf V.unop U.unop g.unop x }⟩

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `a b`. Establish `h` using `hF.eq_of_src (𝟙 F) 0`. Establish `ha : a = Sec.map (𝟙 F) a` using `rfl`. Establish `hb : b = Sec.map (𝟙 F) b` using `rfl`.

Rewrite using `[ha, hb, h]`. Both sides reduce to the same expression.
-/
lemma sec_sub {Λ : Type} [CommRing Λ] {F : Shv Λ} (hF : IsZero F) (U : Scheme.{0}) : Subsingleton (Sec F U) := by
  constructor
  intro a b
  have h := hF.eq_of_src (𝟙 F) 0
  have ha : a = Sec.map (𝟙 F) a := rfl
  have hb : b = Sec.map (𝟙 F) b := rfl
  rw [ha, hb, h]
  rfl

/- English proof (translation)
Rewrite using `[IsZero.iff_id_eq_zero]`. Use extensionality with `U x`. Conclude with `Subsingleton.elim _ _`.
-/
lemma isZero_of_sub {Λ : Type} [CommRing Λ] {S : Scheme.{0}} (F : SlShv Λ S)
    (h : ∀ U : Over S, Subsingleton (F.obj.obj (op U))) : IsZero F := by
  rw [IsZero.iff_id_eq_zero]
  ext U x
  exact Subsingleton.elim _ _

/- English proof (translation)
Introduce `Λ _ I J K μ hJ hK X S p r M γ hγ`. Use `choose T hT e he using fun j : ℤ => h1 Λ J K hJ.1 hK.1 p r M j`. Establish `hA` using `fun j : ℤ => h2 Λ μ p r M γ hγ j (j + 1) rfl`. Set `D : ∀ (j : ℤ) (U : Over S), (T j).obj.obj (op U) →ₗ[ULift.{1} Λ] (T (j + 1)).obj.obj (op U)` to `fun j U => (e (j + 1) U).symm.toLinearMap ∘ₗ IsLinearMap.mk' _ (hA j U).1 ∘ₗ (e j U).toLinearMap`. Establish `hD : ∀ (j : ℤ) (U : Over S) x, e (j + 1) U (D j U x) = cD μ p γ j (j + 1) rfl U (e j U x)`.

Introduce `j U x`. Simplify using `[D]`. Set `d : ∀ j : ℤ, T j ⟶ T (j + 1)` to `fun j => shvHomOf (T j) (T (j + 1)) (D j) (by`. Introduce `V U g x`. Use `(e (j + 1) V).injective ?_` and prove the remaining obligations.

Rewrite using `[hD, he, he, hD, ((hA j U).2.2 V g).2.1])`. Establish `sq : ∀ j : ℤ, d j ≫ d (j + 1) = 0`. Introduce `j`. Use extensionality with `U x`. Express the relevant statement in the definitionally equal form `D (j + 1) U.unop (D j U.unop x) = 0`.

Use `(e (j + 1 + 1) U.unop).injective ?_` and prove the remaining obligations. Rewrite using `[hD, hD, (hA j U.unop).2.1, map_zero]`. Use `⟨CochainComplex.of T d sq, fun j => hT j, ?_, fun j U => (e j U).toAddEquiv, fun j V U g x => he j V U g x, ?_⟩` and prove the remaining obligations. Introduce `j hj`. Apply `isZero_of_sub` to reduce the goal to its premises.

Introduce `U`. Establish `: Subsingleton (Cone J K p r M j U)`. Establish `h3 : ∀ (a : Fin (M + 1)) (s : Fin (r a)), Subsingleton (Sec (J.X (j + 1 - ((a : ℕ) : ℤ))) U.left)` using `fun a s => sec_sub (hJ.2 _ (by omega)) _`. Establish `h4 : Subsingleton (Sec (K.X j) (pullback p U.hom))` using `sec_sub (hK.2 _ (by omega)) _`. Prove the components needed by the constructor for the conclusion.

Introduce `x y`. Use `Prod.ext ?_ (Subsingleton.elim _ _)` and prove the remaining obligations. Use function extensionality and compare the values at `a s`. Conclude with `(h3 a s).elim _ _`. Conclude with `(e j U).injective.subsingleton`.

Introduce `j j' h U x`. Substitute `h` using the available equality. Establish `hd : (CochainComplex.of T d sq).d j (j + 1) = d j` using `CochainComplex.of_d _ _ _`. Rewrite using `[hd]`. Conclude with `hD j U x`.
-/
theorem coneCx_of (h1 : ConeObj) (h2 : ConeAlg) : ConeCx := by
  intro Λ _ I J K μ hJ hK X S p r M γ hγ
  choose T hT e he using fun j : ℤ => h1 Λ J K hJ.1 hK.1 p r M j
  have hA := fun j : ℤ => h2 Λ μ p r M γ hγ j (j + 1) rfl
  let D : ∀ (j : ℤ) (U : Over S), (T j).obj.obj (op U) →ₗ[ULift.{1} Λ] (T (j + 1)).obj.obj (op U) :=
    fun j U => (e (j + 1) U).symm.toLinearMap ∘ₗ IsLinearMap.mk' _ (hA j U).1 ∘ₗ (e j U).toLinearMap
  have hD : ∀ (j : ℤ) (U : Over S) x, e (j + 1) U (D j U x) = cD μ p γ j (j + 1) rfl U (e j U x) := by
    intro j U x
    simp [D]
  let d : ∀ j : ℤ, T j ⟶ T (j + 1) := fun j => shvHomOf (T j) (T (j + 1)) (D j) (by
    intro V U g x
    refine (e (j + 1) V).injective ?_
    rw [hD, he, he, hD, ((hA j U).2.2 V g).2.1])
  have sq : ∀ j : ℤ, d j ≫ d (j + 1) = 0 := by
    intro j
    ext U x
    change D (j + 1) U.unop (D j U.unop x) = 0
    refine (e (j + 1 + 1) U.unop).injective ?_
    rw [hD, hD, (hA j U.unop).2.1, map_zero]
  refine ⟨CochainComplex.of T d sq, fun j => hT j, ?_, fun j U => (e j U).toAddEquiv, fun j V U g x => he j V U g x, ?_⟩
  · intro j hj
    apply isZero_of_sub
    intro U
    have : Subsingleton (Cone J K p r M j U) := by
      have h3 : ∀ (a : Fin (M + 1)) (s : Fin (r a)), Subsingleton (Sec (J.X (j + 1 - ((a : ℕ) : ℤ))) U.left) :=
        fun a s => sec_sub (hJ.2 _ (by omega)) _
      have h4 : Subsingleton (Sec (K.X j) (pullback p U.hom)) := sec_sub (hK.2 _ (by omega)) _
      constructor
      intro x y
      refine Prod.ext ?_ (Subsingleton.elim _ _)
      funext a s
      exact (h3 a s).elim _ _
    exact (e j U).injective.subsingleton
  · intro j j' h U x
    subst h
    have hd : (CochainComplex.of T d sq).d j (j + 1) = d j := CochainComplex.of_d _ _ _
    rw [hd]
    exact hD j U x

end LateralTheory.KummerTheory.LHCut
