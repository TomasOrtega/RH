import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ExistsCrystalPairing
set_option autoImplicit false
noncomputable section
open CategoryTheory AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.AbLaw GlobalTheory.CechPic GlobalTheory.AbDual
attribute [local instance] Over.cartesianMonoidalCategory

namespace GlobalTheory.AbDual

/- English proof (translation)
Establish `hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB` using `pull_isLB h.isLB _`. Establish `ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁))`. Use `(isAdditive_iff hM).2 fun Y a a' t ↦ ?_` and prove the remaining obligations. Rewrite using `[evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]`. Simplify using `only [lift_fst, lift_snd_assoc]`.

Conclude with `(isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)`. Conclude with `(h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl) ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)`.
-/
theorem IsDual.eq_of_evc {S : Scheme.{0}} {A B' T : Over S} [GrpObj A] [GrpObj B'] {P' : LB (A ⊗ B').left}
    (h : IsDual A B' P') {y₁ y₂ : T ⟶ B'}
    (e : evc h.isLB (fst A T) (snd A T ≫ y₁) = evc h.isLB (fst A T) (snd A T ≫ y₂)) : y₁ = y₂ := by
  have hM : (ev P' (fst A T) (snd A T ≫ y₁)).IsLB := pull_isLB h.isLB _
  have ha : IsAdditive (ev P' (fst A T) (snd A T ≫ y₁)) := by
    refine (isAdditive_iff hM).2 fun Y a a' t ↦ ?_
    rw [evc_ev h.isLB, evc_ev h.isLB, evc_ev h.isLB]
    simp only [lift_fst, lift_snd_assoc]
    exact (isAdditive_iff h.isLB).1 h.additive Y a a' (t ≫ y₁)
  exact (h.univ T _ hM ha).unique ((cls_eq_iff hM hM).1 rfl)
    ((cls_eq_iff hM (pull_isLB h.isLB _)).1 e)

/- English proof (translation)
Use `show _ = lift _ _ ≫ μ`. Rewrite using `[lift_comp_fst_snd]`.
-/
theorem comp_mul_eq {S : Scheme.{0}} {G Y : Over S} [MonObj G] (f : Y ⟶ G ⊗ G) :
    f ≫ μ = (f ≫ fst G G) * (f ≫ snd G G) := by
  show _ = lift _ _ ≫ μ
  rw [lift_comp_fst_snd]

/- English proof (translation)
Introduce `S A B B' _ _ _ P P' h' ha' hP ha x e`. Establish `hP'` using `h'.isLB`. Establish `hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB` using `pull_isLB hP' _`. Establish `c : cls P hP = cls _ hE` using `(cls_eq_iff hP hE).2 e`. Establish `K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x)`.

Introduce `Y a b`. Establish `k` using `evc_ev hP' (fst A B) (snd A B ≫ x) hE a b`. Rewrite `k` using `[lift_fst, lift_snd_assoc]`. Rewrite using `[← k, evc, evc, c]`. Establish `hs : (swap P).IsLB` using `pull_isLB hP _`.

Establish `hs' : (swap P').IsLB` using `pull_isLB hP' _`. Establish `addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b'`. Introduce `Y a b b'`. Establish `k` using `(isAdditive_iff hs).1 ha Y b b' a`. Rewrite `k` using `[evc_swap hP hs, evc_swap hP hs, evc_swap hP hs]`. Then use the resulting hypothesis.

Establish `addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'), evc hP' a (b * b') = evc hP' a b + evc hP' a b'`. Introduce `Y a b b'`. Establish `k` using `(isAdditive_iff hs').1 ha' Y b b' a`. Rewrite `k` using `[evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs']`. Then use the resulting hypothesis. Establish `oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0` using `fun Y a ↦ by`.

Rewrite using `[← evc_swap hP hs]`. Conclude with `ha.evc_one hs a`. Establish `oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0` using `fun Y a ↦ by`. Rewrite using `[← evc_swap hP' hs']`. Conclude with `ha'.evc_one hs' a`.

Establish `u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1` using `fun G _ ↦ by show _ = toUnit _ ≫ η`. Rewrite using `[toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Apply `h'.eq_of_evc` to reduce the goal to its premises. Rewrite using `[← Category.assoc, ← K, u, u, oneR, oneR']`.

Apply `h'.eq_of_evc` to reduce the goal to its premises. Rewrite using `[← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']`. Simplify using `only [Category.assoc, tensorHom_fst, tensorHom_snd]`.
-/
theorem isMonHom_of_classifying : ∀ (S : Scheme.{0}) (A B B' : Over S) [GrpObj A] [GrpObj B] [GrpObj B']
    (P : LB (A ⊗ B).left) (P' : LB (A ⊗ B').left), IsDual A B' P' → IsAdditive (swap P') → P.IsLB →
    IsAdditive (swap P) → ∀ x : B ⟶ B', LBIso P (ev P' (fst A B) (snd A B ≫ x)) → IsMonHom x := by
  intro S A B B' _ _ _ P P' h' ha' hP ha x e
  have hP' := h'.isLB
  have hE : (ev P' (fst A B) (snd A B ≫ x)).IsLB := pull_isLB hP' _
  have c : cls P hP = cls _ hE := (cls_eq_iff hP hE).2 e
  have K : ∀ (Y : Over S) (a : Y ⟶ A) (b : Y ⟶ B), evc hP a b = evc hP' a (b ≫ x) := by
    intro Y a b
    have k := evc_ev hP' (fst A B) (snd A B ≫ x) hE a b
    rw [lift_fst, lift_snd_assoc] at k
    rw [← k, evc, evc, c]
  have hs : (swap P).IsLB := pull_isLB hP _
  have hs' : (swap P').IsLB := pull_isLB hP' _
  have addR : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B), evc hP a (b * b') = evc hP a b + evc hP a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs).1 ha Y b b' a
    rwa [evc_swap hP hs, evc_swap hP hs, evc_swap hP hs] at k
  have addR' : ∀ (Y : Over S) (a : Y ⟶ A) (b b' : Y ⟶ B'),
      evc hP' a (b * b') = evc hP' a b + evc hP' a b' := by
    intro Y a b b'
    have k := (isAdditive_iff hs').1 ha' Y b b' a
    rwa [evc_swap hP' hs', evc_swap hP' hs', evc_swap hP' hs'] at k
  have oneR : ∀ (Y : Over S) (a : Y ⟶ A), evc hP a (1 : Y ⟶ B) = 0 := fun Y a ↦ by
    rw [← evc_swap hP hs]; exact ha.evc_one hs a
  have oneR' : ∀ (Y : Over S) (a : Y ⟶ A), evc hP' a (1 : Y ⟶ B') = 0 := fun Y a ↦ by
    rw [← evc_swap hP' hs']; exact ha'.evc_one hs' a
  have u : ∀ (G : Over S) [MonObj G], snd A (𝟙_ (Over S)) ≫ (η : 𝟙_ (Over S) ⟶ G) = 1 := fun G _ ↦ by
    show _ = toUnit _ ≫ η
    rw [toUnit_unique (snd A (𝟙_ (Over S))) (toUnit _)]
  refine ⟨?_, ?_⟩
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← K, u, u, oneR, oneR']
  · apply h'.eq_of_evc
    rw [← Category.assoc, ← Category.assoc, comp_mul_eq, comp_mul_eq, ← K, addR, K, K, ← addR']
    simp only [Category.assoc, tensorHom_fst, tensorHom_snd]

end GlobalTheory.AbDual
