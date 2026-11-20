import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.GeneralLinearActions.GenusMassVolumes
import Formalism.SharpRestriction.GlobalSchurBounds.StandardLattice

noncomputable section

namespace GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers

open scoped TensorProduct Pointwise
open NumberField Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice

section Lat

variable {F E : Type} [Field F] [Field E] [Algebra F E]

def IsSelfDualLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) : Prop :=
  L.FG ∧ Submodule.span E (L : Set (Fin M → E)) = ⊤ ∧
    ∀ y : Fin M → E, y ∈ L ↔ ∀ x ∈ L, IsIntegral ℤ (hE σ J x y)

def perpIn (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) : Set (Fin M → E) :=
  {y | y ∈ L ∧ hE σ J x y = 0}

variable (R : Type) [CommRing R] [Algebra F R]

def actV (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : Fin M → R ⊗[F] E :=
  (h • (fun _ => y : Fin 1 → Fin M → R ⊗[F] E)) 0

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem actV_eq (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (h : HA R σ J)
    (y : Fin M → R ⊗[F] E) :
    actV R σ J h y = ((HA.mat R σ J h : GL (Fin M) (R ⊗[F] E)) :
      Matrix (Fin M) (Fin M) (R ⊗[F] E)).mulVec y := rfl

/- English proof (translation)
Unfold `actV`. Rewrite using `[one_smul]`.
-/
theorem actV_one (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (y : Fin M → R ⊗[F] E) : actV R σ J 1 y = y := by
  unfold actV
  rw [one_smul]

/- English proof (translation)
Unfold `actV`. Rewrite using `[mul_smul]`. Both sides reduce to the same expression.
-/
theorem actV_mul (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E) (g h : HA R σ J)
    (y : Fin M → R ⊗[F] E) : actV R σ J (g * h) y = actV R σ J g (actV R σ J h y) := by
  unfold actV
  rw [mul_smul]
  rfl

def stabLat (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (Λ : AddSubgroup (Fin M → R ⊗[F] E)) : Subgroup (HA R σ J) where
  carrier := {h | ∀ y, y ∈ Λ ↔ actV R σ J h y ∈ Λ}
  one_mem' := by intro y; rw [actV_one]
  mul_mem' := by
    intro a b ha hb y
    rw [actV_mul]
    exact (hb y).trans (ha _)
  inv_mem' := by
    intro g hg y
    have := hg (actV R σ J g⁻¹ y)
    rw [← actV_mul, mul_inv_cancel, actV_one] at this
    exact this.symm

end Lat

def UnramifiedAtFinite (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E]
    [Algebra F E] : Prop :=
  ∀ (P : Ideal (𝓞 E)) [P.IsPrime], P ≠ ⊥ → Algebra.IsUnramifiedAt (𝓞 F) P

def OrbitConcl (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E]
    (σ : E →ₐ[F] E) {M : ℕ} (J : Matrix (Fin M) (Fin M) E)
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (β : F) : Prop :=
  (∀ y ∈ latHat F E (L : Set (Fin M → E)), qR (Af F) σ J y = algebraMap F (Af F) β →
      ∃ k ∈ stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))),
        actV (Af F) σ J k (fun i => inclR (F := F) (Af F) (x i)) = y) ∧
  ({h : HA (Af F) σ J | actV (Af F) σ J h⁻¹ (fun i => inclR (F := F) (Af F) (x i)) ∈
        latHat F E (L : Set (Fin M → E))} =
      (Hstab (Af F) σ J (fun _ => x) : Set (HA (Af F) σ J)) *
        (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) : Set (HA (Af F) σ J))) ∧
  (stabLat (Af F) σ J (latHat F E (L : Set (Fin M → E))) ⊓ Hstab (Af F) σ J (fun _ => x) =
      stabLat (Af F) σ J (latHat F E (perpIn σ J L x)) ⊓ Hstab (Af F) σ J (fun _ => x))

def StabTransitive : Prop :=
  ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (σ : E →ₐ[F] E), IsCMExt F E σ → UnramifiedAtFinite F E →
    ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J →
    ∀ L : Submodule (𝓞 E) (Fin M → E), IsSelfDualLat σ J L →
    ∀ β : F, (β = 1 ∨ β = -1) →
    ∀ x ∈ L, hE σ J x x = algebraMap F E β → OrbitConcl F E σ J L x β

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩`.
-/
example (F E : Type) [Field F] [NumberField F] [Field E] [Algebra F E] {M : ℕ}
    (L : Submodule (𝓞 E) (Fin M → E)) (x : Fin M → E) (hx : x ∈ L) :
    (fun i => inclR (F := F) (Af F) (x i)) ∈ latHat F E (L : Set (Fin M → E)) :=
  AddSubgroup.subset_closure ⟨1, fun v => by rw [map_one]; exact one_mem _, x, hx, rfl⟩

def stdLat (E : Type) [Field E] (M : ℕ) : Submodule (𝓞 E) (Fin M → E) :=
  Submodule.span (𝓞 E) (Set.range fun i : Fin M => (Pi.single i 1 : Fin M → E))

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hy`. Proceed by induction on `hy using Submodule.span_induction with`. Consider the case `mem z hz`. Take `⟨j, rfl⟩` from `hz`.

Introduce `i`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `using isIntegral_one`. Simplify `isIntegral_zero` using `[Pi.single_eq_of_ne h]`.

Consider the case `zero => intro i`. Conclude with `isIntegral_zero`. Consider the case `add a b _ _ ha hb => intro i`. Conclude with `(ha i).add (hb i)`. Consider the case `smul c a _ ha => intro i`.

Conclude with `(c.2 : IsIntegral ℤ (c : E)).mul (ha i)`. Introduce `hy`. Rewrite using `[← Finset.univ_sum_single y]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i (y i) : Fin M → E) = (⟨y i, hy i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E)`.

Use function extensionality and compare the values at `j`. Distinguish the cases in `h : j = i`. Substitute `h` using the available equality. Rewrite using `[Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one]`. Both sides reduce to the same expression.

Rewrite using `[Pi.smul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero]`. Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)`.
-/
theorem mem_stdLat (E : Type) [Field E] (M : ℕ) (y : Fin M → E) :
    y ∈ stdLat E M ↔ ∀ i, IsIntegral ℤ (y i) := by
  constructor
  · intro hy
    induction hy using Submodule.span_induction with
    | mem z hz =>
      obtain ⟨j, rfl⟩ := hz
      intro i
      by_cases h : i = j
      · subst h; simpa using isIntegral_one
      · simpa [Pi.single_eq_of_ne h] using isIntegral_zero
    | zero => intro i; exact isIntegral_zero
    | add a b _ _ ha hb => intro i; exact (ha i).add (hb i)
    | smul c a _ ha => intro i; exact (c.2 : IsIntegral ℤ (c : E)).mul (ha i)
  · intro hy
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (y i) : Fin M → E) =
        (⟨y i, hy i⟩ : 𝓞 E) • (Pi.single i 1 : Fin M → E) := by
      funext j
      by_cases h : j = i
      · subst h
        rw [Pi.smul_apply, Pi.single_eq_same, Pi.single_eq_same, Algebra.smul_def, mul_one]; rfl
      · rw [Pi.smul_apply, Pi.single_eq_of_ne h, Pi.single_eq_of_ne h, smul_zero]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

/- English proof (translation)
Establish `hh : ∀ x y : Fin M → E, hE σ 1 x y = ∑ i, σ (x i) * y i`. Introduce `x y`. Simplify using `[hE, Formalism.UG.hform, Matrix.one_apply]`. Use `⟨Submodule.fg_span (Set.finite_range _), ?_, fun y => ?_⟩` and prove the remaining obligations. Rewrite using `[eq_top_iff]`.

Introduce `y _`. Rewrite using `[← Finset.univ_sum_single y]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations. Establish `: (Pi.single i (y i) : Fin M → E) = y i • (Pi.single i 1 : Fin M → E)`. Rewrite using `[← Pi.single_smul, smul_eq_mul, mul_one]`.

Rewrite using `[this]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))`. Prove the components needed by the constructor for the conclusion. Introduce `hy x hx`. Rewrite using `[hh]`.

Rewrite `hx`, `hy` using `[mem_stdLat]`. Conclude with `IsIntegral.sum _ fun i _ => ((hx i).map (σ : E →+* E).toIntAlgHom).mul (hy i)`. Introduce `H`. Rewrite using `[mem_stdLat]`. Introduce `i`.

Use `H (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩)` as an intermediate fact. Rewrite `this` using `[hh, Finset.sum_eq_single i]`. Simplify using `using this`. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`.

Simplify using the standard rewrite rules.
-/
theorem isSelfDualLat_std {F E : Type} [Field F] [Field E] [Algebra F E] (σ : E →ₐ[F] E) (M : ℕ) :
    IsSelfDualLat σ (1 : Matrix (Fin M) (Fin M) E) (stdLat E M) := by
  have hh : ∀ x y : Fin M → E, hE σ 1 x y = ∑ i, σ (x i) * y i := by
    intro x y
    simp [hE, Formalism.UG.hform, Matrix.one_apply]
  refine ⟨Submodule.fg_span (Set.finite_range _), ?_, fun y => ?_⟩
  · rw [eq_top_iff]
    intro y _
    rw [← Finset.univ_sum_single y]
    refine Submodule.sum_mem _ fun i _ => ?_
    have : (Pi.single i (y i) : Fin M → E) = y i • (Pi.single i 1 : Fin M → E) := by
      rw [← Pi.single_smul, smul_eq_mul, mul_one]
    rw [this]
    exact Submodule.smul_mem _ _ (Submodule.subset_span (Submodule.subset_span ⟨i, rfl⟩))
  · constructor
    · intro hy x hx
      rw [hh]
      rw [mem_stdLat] at hx hy
      exact IsIntegral.sum _ fun i _ =>
        ((hx i).map (σ : E →+* E).toIntAlgHom).mul (hy i)
    · intro H
      rw [mem_stdLat]
      intro i
      have := H (Pi.single i 1) (Submodule.subset_span ⟨i, rfl⟩)
      rw [hh, Finset.sum_eq_single i] at this
      · simpa using this
      · intro j _ hj; simp [Pi.single_eq_of_ne hj]
      · simp

end GlobalTheory.IndefiniteRowSideFullHecke.SelfDualLatticeStabilizers
