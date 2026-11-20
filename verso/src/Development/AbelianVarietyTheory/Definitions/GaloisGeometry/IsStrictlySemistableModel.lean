import Mathlib
import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.IsStrictlySemistableAlt
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.SubsingletonObjOfIsEmpty

noncomputable section

open CategoryTheory Limits AlgebraicGeometry Opposite

namespace GlobalTheory.Et

section Transfer

variable (R : Type) [CommRing R] [TopologicalSpace R] [IsTopologicalRing R]

/- English proof (translation)
Break down `Nat.lt_trichotomy m 1 with hm | hm | hm` into its components or cases. Establish `hm0 : m = 0` using `by omega`. Substitute `hm0` using the available equality. Establish `f : S ⟶ (∅ : Scheme.{0})` using `inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)`. Conclude with `(IsEmpty.false (f pt)).elim`.

Conclude with `hm`. It suffices to derive a contradiction. Set `i : Fin m` to `⟨0, by omega⟩`. Set `j : Fin m` to `⟨1, hm⟩`. Establish `hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j` using `(cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)`.

Establish `hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt` using `by rw [hij]`. Use `congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)` as an intermediate fact. Simplify using `[i, j] at this`.
-/
theorem eq_one_of_isIso_codiag {S : Scheme.{0}} (pt : S) {m : ℕ}
    (h : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)) : m = 1 := by
  rcases Nat.lt_trichotomy m 1 with hm | hm | hm
  · have hm0 : m = 0 := by omega
    subst hm0
    have f : S ⟶ (∅ : Scheme.{0}) :=
      inv (Sigma.desc (fun _ : Fin 0 => 𝟙 S)) ≫ Sigma.desc (fun j : Fin 0 => j.elim0)
    exact (IsEmpty.false (f pt)).elim
  · exact hm
  · exfalso
    let i : Fin m := ⟨0, by omega⟩
    let j : Fin m := ⟨1, hm⟩
    have hij : Sigma.ι (fun _ : Fin m => S) i = Sigma.ι (fun _ : Fin m => S) j :=
      (cancel_mono (Sigma.desc (fun _ : Fin m => 𝟙 S))).1 (by simp)
    have hp : Sigma.ι (fun _ : Fin m => S) i pt = Sigma.ι (fun _ : Fin m => S) j pt := by rw [hij]
    have := congrArg Sigma.fst ((sigmaι_eq_iff (fun _ : Fin m => S) i j pt pt).mp hp)
    simp [i, j] at this

/- English proof (translation)
Introduce `S x m s hs hiso`. Establish `hsx : ∀ j, s j = x` using `fun j => by simpa using hs j`. Simplify using `only [Category.comp_id, hsx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]`. Break down `isEmpty_or_nonempty S with hS | hS` into its components or cases. Conclude with `(isZero_freeOn_of_isEmpty R S).eq_of_src _ _`.

Take `⟨pt⟩` from `hS`. Establish `hc : (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) : ∐ (fun _ : Fin m => S) ⟶ pullback (𝟙 X) x) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin m => 𝟙 S)`. Apply `Sigma.hom_ext` to reduce the goal to its premises. Introduce `j`. Rewrite using `[Sigma.ι_desc_assoc, Sigma.ι_desc]`.

Conclude with `pullback.lift_snd _ _ _`. Establish `: IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S)`. Rewrite using `[← hc]`. Use `infer_instance`. Rewrite using `[eq_one_of_isIso_codiag pt this, one_smul]`.
-/
theorem isTransfer_id (X : Scheme.{0}) : IsTransfer R (𝟙 X) (𝟙 _) := by
  intro S x m s hs hiso
  have hsx : ∀ j, s j = x := fun j => by simpa using hs j
  simp only [Category.comp_id, hsx, Finset.sum_const, Finset.card_univ, Fintype.card_fin]
  rcases isEmpty_or_nonempty S with hS | hS
  · exact (isZero_freeOn_of_isEmpty R S).eq_of_src _ _
  · obtain ⟨pt⟩ := hS
    have hc : (Sigma.desc (fun j => pullback.lift (s j) (𝟙 S) (by rw [hs j, Category.id_comp])) :
        ∐ (fun _ : Fin m => S) ⟶ pullback (𝟙 X) x) ≫ pullback.snd _ _ = Sigma.desc (fun _ : Fin m => 𝟙 S) := by
      apply Sigma.hom_ext; intro j; rw [Sigma.ι_desc_assoc, Sigma.ι_desc]; exact pullback.lift_snd _ _ _
    have : IsIso (Sigma.desc (fun _ : Fin m => 𝟙 S) : ∐ (fun _ : Fin m => S) ⟶ S) := by
      rw [← hc]; infer_instance
    rw [eq_one_of_isIso_codiag pt this, one_smul]

end Transfer

section Semistable

variable (O : Type) [CommRing O] (ϖ : O) (m r : ℕ)

abbrev ssModel : Type :=
  MvPolynomial (Fin m) O ⧸ Ideal.span {(∏ i ∈ Finset.univ.filter (fun i : Fin m => (i : ℕ) < r), MvPolynomial.X i) -
      MvPolynomial.C ϖ}

/- English proof (translation)
Introduce `x`. Use `⟨⊤, isAffineOpen_top _, trivial, m, r, h1, h2, (Scheme.ΓSpecIso (CommRingCat.of (ssModel O ϖ m r))).inv.hom, RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_⟩` and prove the remaining obligations. Establish `h : (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appTop = (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appLE ⊤ ⊤ le_top` using `Scheme.Hom.app_eq_appLE _`. Rewrite using `[← h, ← Scheme.ΓSpecIso_inv_naturality]`. Both sides reduce to the same expression.
-/
theorem isStrictlySemistable_model (h1 : 1 ≤ r) (h2 : r ≤ m) :
    IsStrictlySemistable ϖ (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))) := by
  intro x
  refine ⟨⊤, isAffineOpen_top _, trivial, m, r, h1, h2, (Scheme.ΓSpecIso (CommRingCat.of (ssModel O ϖ m r))).inv.hom,
    RingHom.Etale.of_bijective (ConcreteCategory.bijective_of_isIso _), ?_⟩
  have h : (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appTop =
      (Spec.map (CommRingCat.ofHom (algebraMap O (ssModel O ϖ m r)))).appLE ⊤ ⊤ le_top := Scheme.Hom.app_eq_appLE _
  rw [← h, ← Scheme.ΓSpecIso_inv_naturality]
  rfl

/- English proof (translation)
The claim follows from `isStrictlySemistable_model ℤ 2 2 2 (by norm_num) le_rfl`.
-/
example : IsStrictlySemistable (2 : ℤ) (Spec.map (CommRingCat.ofHom (algebraMap ℤ (ssModel ℤ 2 2 2)))) :=
  isStrictlySemistable_model ℤ 2 2 2 (by norm_num) le_rfl

end Semistable

section MuTest

/- English proof (translation)
Rewrite using `[mem_rootsOfUnity]`. Evaluate the decidable proposition.
-/
example : (-1 : ℤˣ) ∈ rootsOfUnity 2 ℤ := by
  rw [mem_rootsOfUnity]; decide

end MuTest

end GlobalTheory.Et

end
