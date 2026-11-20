import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.ComparisonMemCechHodgeFiltration
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.VanishingH1InvertingMorphisms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLocalizationOfData
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUnitMpOmjExtIff
open CategoryTheory AlgebraicGeometry KaehlerDifferential GlobalTheory.CatCoh GlobalTheory.CechDR

set_option autoImplicit false

namespace GlobalTheory.CatCoh

/- English proof (translation)
Introduce `R _ C _ C' _ F G hsep hglue hvan`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `c hc`. Take `⟨z, rfl⟩` from `H2.mk_surjective F c`. Rewrite `hc` using `[CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero]`.

Take `⟨y0, hy0⟩` from `hc`. Take `⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t') (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b = z.1 _ _ _ (G.map a) (G.map b)` from `⟨y0, fun t t' t'' a b ↦ congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩`. Establish `hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u) = z.1 _ _ _ u (G.map a) - y t t' a` using `fun T ↦ hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by`. Establish `k1` using `z.2 u (G.map a) (G.map b)`. Establish `k2` using `hy' t t' t'' a b`.

Rewrite using `[Functor.map_comp]`. Simplify using `only [map_sub]`. Take the linear combination `k2 - k1`. Use `choose g hg using hg`. Establish `hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t), mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u`.

Introduce `T T' φ`. Use `hglue T' _ fun t t' u a ↦ ?_` and prove the remaining obligations. Establish `k1` using `z.2 φ u (G.map a)`. Establish `k2` using `hg T t t' (φ ≫ u) a`. Establish `k3` using `hg T' t t' u a`.

Rewrite `k2` using `[Category.assoc]`. Simplify using `only [map_sub, map_add]`. Take the linear combination `-k1 - k2 + k3`. Use `choose x hx using hx`. Use `H2.mk_eq_zero.2 ⟨x, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `T T' T'' φ ψ`. Use `sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)` and prove the remaining obligations. Establish `k1` using `z.2 φ ψ u`. Establish `k2` using `hx T T' φ t (ψ ≫ u)`. Establish `k3` using `hx T T'' (φ ≫ ψ) t u`.

Establish `k4` using `hx T' T'' ψ t u`. Rewrite `k2` using `[mp_comp]`. Rewrite using `[d1_apply]`. Simplify using `only [map_sub, map_add, Category.assoc] at k2 k3 ⊢`. Take the linear combination `k2 - k3 + k4 - k1`.
-/
theorem pull2_restrict_injective_of_comma : ∀ {R : Type} [CommRing R] {C : Type} [Category.{0} C] {C' : Type} [Category.{0} C'] (F : C ⥤ CommAlgCat.{0} R) (G : C' ⥤ C), (∀ (T : C) (x : (F).obj T), (∀ t (u : T ⟶ G.obj t), mp (F) u x = 0) → x = 0) → (∀ (T : C) (s : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t)), (∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), s t' (u ≫ G.map a) = mp (F) (G.map a) (s t u)) → ∃ x : (F).obj T, ∀ t u, mp (F) u x = s t u) → (∀ (T : C) (y : ∀ t t', (T ⟶ G.obj t) → (t ⟶ t') → (F).obj (G.obj t')), (∀ t t' t'' (u : T ⟶ G.obj t) (a : t ⟶ t') (b : t' ⟶ t''), y t t'' u (a ≫ b) = mp (F) (G.map b) (y t t' u a) + y t' t'' (u ≫ G.map a) b) → ∃ g : ∀ t, (T ⟶ G.obj t) → (F).obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t) (a : t ⟶ t'), g t' (u ≫ G.map a) - mp (F) (G.map a) (g t u) = y t t' u a) → Function.Injective (CoefMap.restrict F G).pull2 := by
  intro R _ C _ C' _ F G hsep hglue hvan
  rw [injective_iff_map_eq_zero]
  intro c hc
  obtain ⟨z, rfl⟩ := H2.mk_surjective F c
  rw [CoefMap.pullCohomologyTwo_class, H2.mk_eq_zero] at hc
  obtain ⟨y0, hy0⟩ := hc
  obtain ⟨y, hy'⟩ : ∃ y : ∀ t t' (_ : t ⟶ t'), F.obj (G.obj t'), ∀ t t' t'' (a : t ⟶ t')
      (b : t' ⟶ t''), mp F (G.map b) (y t t' a) - y t t'' (a ≫ b) + y t' t'' b
        = z.1 _ _ _ (G.map a) (G.map b) := ⟨y0, fun t t' t'' a b ↦
    congrFun (congrFun (congrFun (congrFun (congrFun hy0 t) t') t'') a) b⟩
  have hg : ∀ T : C, ∃ g : ∀ t, (T ⟶ G.obj t) → F.obj (G.obj t), ∀ t t' (u : T ⟶ G.obj t)
      (a : t ⟶ t'), g t' (u ≫ G.map a) - mp F (G.map a) (g t u)
        = z.1 _ _ _ u (G.map a) - y t t' a := fun T ↦
    hvan T (fun t t' u a ↦ z.1 _ _ _ u (G.map a) - y t t' a) fun t t' t'' u a b ↦ by
      have k1 := z.2 u (G.map a) (G.map b)
      have k2 := hy' t t' t'' a b
      rw [Functor.map_comp]
      simp only [map_sub]
      linear_combination k2 - k1
  choose g hg using hg
  have hx : ∀ T T' (φ : T ⟶ T'), ∃ x : F.obj T', ∀ t (u : T' ⟶ G.obj t),
      mp F u x = z.1 _ _ _ φ u - g T t (φ ≫ u) + g T' t u := by
    intro T T' φ
    refine hglue T' _ fun t t' u a ↦ ?_
    have k1 := z.2 φ u (G.map a)
    have k2 := hg T t t' (φ ≫ u) a
    have k3 := hg T' t t' u a
    rw [Category.assoc] at k2
    simp only [map_sub, map_add]
    linear_combination -k1 - k2 + k3
  choose x hx using hx
  refine H2.mk_eq_zero.2 ⟨x, ?_⟩
  funext T T' T'' φ ψ
  refine sub_eq_zero.1 (hsep T'' _ fun t u ↦ ?_)
  have k1 := z.2 φ ψ u
  have k2 := hx T T' φ t (ψ ≫ u)
  have k3 := hx T T'' (φ ≫ ψ) t u
  have k4 := hx T' T'' ψ t u
  rw [mp_comp] at k2
  rw [d1_apply]
  simp only [map_sub, map_add, Category.assoc] at k2 k3 ⊢
  linear_combination k2 - k3 + k4 - k1

end GlobalTheory.CatCoh
