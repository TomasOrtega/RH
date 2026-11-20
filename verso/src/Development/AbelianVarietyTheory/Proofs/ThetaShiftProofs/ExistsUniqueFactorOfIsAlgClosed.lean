import Mathlib
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsRingEquivOfIsTranscendenceBasis

open CategoryTheory AlgebraicGeometry

namespace GlobalTheory.FixedPoint

universe u v w

section Algebra

variable {K₀ : Type u} {K₁ : Type v} {L : Type w} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

/- English proof (translation)
Take `⟨k, hk⟩` from `GaloisDescent.mem_range_algebraMap_of_forall_algEquiv _ ha`. Use `⟨k, (algebraMap K₁ L).injective ?_⟩` and prove the remaining obligations. Rewrite using `[← IsScalarTower.algebraMap_apply, hk]`.
-/
theorem mem_range_of_algebraMap_fixed [PerfectField K₀] [IsAlgClosed L] (a : K₁)
    (ha : ∀ s : L ≃ₐ[K₀] L, s (algebraMap K₁ L a) = algebraMap K₁ L a) :
    a ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨k, hk⟩ := GaloisDescent.mem_range_algebraMap_of_forall_algEquiv _ ha
  refine ⟨k, (algebraMap K₁ L).injective ?_⟩
  rw [← IsScalarTower.algebraMap_apply, hk]

/- English proof (translation)
Use `choose f hf using h`. Establish `hi` using `(algebraMap K₀ K₁).injective`. Apply the tactic sequence `refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext hf⟩ <;>`. Simplify using `[hf]`.
-/
theorem exists_ringHom_of_forall_mem_range {A : Type*} [CommRing A] (φ : A →+* K₁)
    (h : ∀ a, φ a ∈ Set.range (algebraMap K₀ K₁)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ := by
  choose f hf using h
  have hi := (algebraMap K₀ K₁).injective
  refine ⟨⟨⟨⟨f, hi ?_⟩, fun a b => hi ?_⟩, hi ?_, fun a b => hi ?_⟩, RingHom.ext hf⟩ <;>
    simp [hf]

/- English proof (translation)
The claim follows from `exists_ringHom_of_forall_mem_range φ fun a => mem_range_of_algebraMap_fixed _ fun s => h s a`.
-/
theorem exists_ringHom_of_fixed [PerfectField K₀] [IsAlgClosed L] {A : Type*} [CommRing A]
    (φ : A →+* K₁)
    (h : ∀ (s : L ≃ₐ[K₀] L) (a : A), s (algebraMap K₁ L (φ a)) = algebraMap K₁ L (φ a)) :
    ∃ ψ : A →+* K₀, (algebraMap K₀ K₁).comp ψ = φ :=
  exists_ringHom_of_forall_mem_range φ fun a => mem_range_of_algebraMap_fixed _ fun s => h s a

end Algebra

section Scheme

local notation "specAlg(" K ", " L ")" => Spec.map (CommRingCat.ofHom (algebraMap K L))

variable {K₀ K₁ L : Type u} [Field K₀] [Field K₁] [Field L]
  [Algebra K₀ K₁] [Algebra K₁ L] [Algebra K₀ L] [IsScalarTower K₀ K₁ L]

/- English proof (translation)
The claim follows from `have : Surjective specAlg(K₀, K₁) := ⟨Function.surjective_to_subsingleton _⟩ Flat.epi_of_flat_of_surjective _`.
-/
theorem epi_specAlg : Epi specAlg(K₀, K₁) :=
  have : Surjective specAlg(K₀, K₁) := ⟨Function.surjective_to_subsingleton _⟩
  Flat.epi_of_flat_of_surjective _

/- English proof (translation)
The claim follows from `have := epi_specAlg (K₀ := K₀) (K₁ := K₁) (cancel_epi _).mp h`.
-/
theorem point_ext {Z : Scheme.{u}} {y y' : Spec (.of K₀) ⟶ Z}
    (h : specAlg(K₀, K₁) ≫ y = specAlg(K₀, K₁) ≫ y') : y = y' :=
  have := epi_specAlg (K₀ := K₀) (K₁ := K₁)
  (cancel_epi _).mp h

/- English proof (translation)
Simplify using `only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]`. Use `congr 3`. Use extensionality with `a`. Simplify using `[← IsScalarTower.algebraMap_apply]`.
-/
theorem fixed_of_factor {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (s : L ≃ₐ[K₀] L) :
    Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y =
      specAlg(K₁, L) ≫ specAlg(K₀, K₁) ≫ y := by
  simp only [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp]
  congr 3
  ext a
  simp [← IsScalarTower.algebraMap_apply]

/- English proof (translation)
Take `⟨⟨z, φ⟩, rfl⟩` from `(Scheme.SpecToEquivOfField K₁ Z).symm.surjective x`. Simplify using `only [Scheme.SpecToEquivOfField_symm_apply] at hx ⊢`. Take `⟨ψ, hψ⟩` from `exists_ringHom_of_fixed (K₀ := K₀) (L := L) φ.hom fun s a => by`. Establish `h` using `hx s`. Simplify using `only [← Category.assoc] at h`.

Rewrite `h` using `[cancel_mono, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj]`. Conclude with `congr(($h).hom a)`. Establish `hy : specAlg(K₀, K₁) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Z.fromSpecResidueField z = Spec.map φ ≫ Z.fromSpecResidueField z`. Rewrite using `[← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ]`. Both sides reduce to the same expression.

Conclude with `⟨_, hy, fun y' hy' => point_ext (hy'.trans hy.symm)⟩`.
-/
theorem existsUnique_factor [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x := by
  obtain ⟨⟨z, φ⟩, rfl⟩ := (Scheme.SpecToEquivOfField K₁ Z).symm.surjective x
  simp only [Scheme.SpecToEquivOfField_symm_apply] at hx ⊢
  obtain ⟨ψ, hψ⟩ := exists_ringHom_of_fixed (K₀ := K₀) (L := L) φ.hom fun s a => by
    have h := hx s
    simp only [← Category.assoc] at h
    rw [cancel_mono, ← Spec.map_comp, ← Spec.map_comp, ← Spec.map_comp, Spec.map_inj] at h
    exact congr(($h).hom a)
  have hy : specAlg(K₀, K₁) ≫ Spec.map (CommRingCat.ofHom ψ) ≫ Z.fromSpecResidueField z =
      Spec.map φ ≫ Z.fromSpecResidueField z := by
    rw [← Spec.map_comp_assoc, ← CommRingCat.ofHom_comp, hψ]
    rfl
  exact ⟨_, hy, fun y' hy' => point_ext (hy'.trans hy.symm)⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun ⟨y, hy⟩ s => hy ▸ fixed_of_factor y s, fun h => (existsUnique_factor x h).exists⟩`.
-/
theorem exists_factor_iff [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z) :
    (∃ y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ↔ ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x :=
  ⟨fun ⟨y, hy⟩ s => hy ▸ fixed_of_factor y s, fun h => (existsUnique_factor x h).exists⟩

/- English proof (translation)
The claim follows from `existsUnique_factor (L := L) x fun s => by simpa using hx s`.
-/
theorem existsUnique_factor_of_isAlgClosed [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of L) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L, Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ x = x) :
    ∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, L) ≫ y = x :=
  existsUnique_factor (L := L) x fun s => by simpa using hx s

/- English proof (translation)
Use `⟨fun h => h (Set.mem_univ (IsLocalRing.closedPoint K₁)), fun h p _ => ?_⟩` and prove the remaining obligations. Rewrite using `[Subsingleton.elim p (IsLocalRing.closedPoint K₁)]`. Conclude with `h`.
-/
theorem top_le_preimage_iff_mem {Z : Scheme.{u}} (x : Spec (.of K₁) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ x ⁻¹ᵁ U ↔ x (IsLocalRing.closedPoint K₁) ∈ U := by
  refine ⟨fun h => h (Set.mem_univ (IsLocalRing.closedPoint K₁)), fun h p _ => ?_⟩
  rw [Subsingleton.elim p (IsLocalRing.closedPoint K₁)]
  exact h

/- English proof (translation)
Use `⟨fun h p _ => ?_, fun h p _ => h (Set.mem_univ (specAlg(K₀, K₁) p))⟩` and prove the remaining obligations. Establish `h'` using `h (Set.mem_univ (IsLocalRing.closedPoint K₁))`. Rewrite using `[Subsingleton.elim p (specAlg(K₀, K₁) (IsLocalRing.closedPoint K₁))]`. Conclude with `h'`.
-/
theorem top_le_preimage_comp_iff {Z : Scheme.{u}} (y : Spec (.of K₀) ⟶ Z) (U : Z.Opens) :
    ⊤ ≤ (specAlg(K₀, K₁) ≫ y) ⁻¹ᵁ U ↔ ⊤ ≤ y ⁻¹ᵁ U := by
  refine ⟨fun h p _ => ?_, fun h p _ => h (Set.mem_univ (specAlg(K₀, K₁) p))⟩
  have h' := h (Set.mem_univ (IsLocalRing.closedPoint K₁))
  rw [Subsingleton.elim p (specAlg(K₀, K₁) (IsLocalRing.closedPoint K₁))]
  exact h'

/- English proof (translation)
Establish `: (Spec.map g ≫ y).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso B).hom = y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso A).hom ≫ g`. Rewrite using `[← Scheme.ΓSpecIso_naturality, ← Category.assoc]`. Use `congr 1`. Conclude with `congr(($this).hom f)`.
-/
theorem value_comp {A B : CommRingCat.{u}} (g : A ⟶ B) {Z : Scheme.{u}} (y : Spec A ⟶ Z)
    (U : Z.Opens) (h : ⊤ ≤ y ⁻¹ᵁ U) (h' : ⊤ ≤ (Spec.map g ≫ y) ⁻¹ᵁ U) (f : Γ(Z, U)) :
    (Scheme.ΓSpecIso B).hom ((Spec.map g ≫ y).appLE U ⊤ h' f) =
      g ((Scheme.ΓSpecIso A).hom (y.appLE U ⊤ h f)) := by
  have : (Spec.map g ≫ y).appLE U ⊤ h' ≫ (Scheme.ΓSpecIso B).hom =
      y.appLE U ⊤ h ≫ (Scheme.ΓSpecIso A).hom ≫ g := by
    rw [← Scheme.ΓSpecIso_naturality, ← Category.assoc]
    congr 1
  exact congr(($this).hom f)

/- English proof (translation)
Take `⟨y, rfl⟩` from `(existsUnique_factor x hx).exists`. Conclude with `⟨_, (value_comp _ y U ((top_le_preimage_comp_iff y U).1 h) h f).symm⟩`.
-/
theorem value_mem_range [PerfectField K₀] [IsAlgClosed L] {Z : Scheme.{u}}
    (x : Spec (.of K₁) ⟶ Z)
    (hx : ∀ s : L ≃ₐ[K₀] L,
      Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x)
    (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)) :
    ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈ Set.range (algebraMap K₀ K₁) := by
  obtain ⟨y, rfl⟩ := (existsUnique_factor x hx).exists
  exact ⟨_, (value_comp _ y U ((top_le_preimage_comp_iff y U).1 h) h f).symm⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨GaloisDescent.mem_range_algebraMap_of_forall_algEquiv, fun _ x hx => ⟨existsUnique_factor x hx, value_mem_range x hx⟩⟩`.
-/
theorem defined_over_of_fixed [CharZero K₀] [IsAlgClosed L] :
    (∀ a : L, (∀ s : L ≃ₐ[K₀] L, s a = a) → a ∈ Set.range (algebraMap K₀ L)) ∧
    ∀ (Z : Scheme.{u}) (x : Spec (.of K₁) ⟶ Z),
      (∀ s : L ≃ₐ[K₀] L,
        Spec.map (CommRingCat.ofHom (s : L →+* L)) ≫ specAlg(K₁, L) ≫ x = specAlg(K₁, L) ≫ x) →
      (∃! y : Spec (.of K₀) ⟶ Z, specAlg(K₀, K₁) ≫ y = x) ∧
      ∀ (U : Z.Opens) (h : ⊤ ≤ x ⁻¹ᵁ U) (f : Γ(Z, U)),
        ((Scheme.ΓSpecIso (.of K₁)).hom (x.appLE U ⊤ h f) : K₁) ∈
          Set.range (algebraMap K₀ K₁) :=
  ⟨GaloisDescent.mem_range_algebraMap_of_forall_algEquiv,
    fun _ x hx => ⟨existsUnique_factor x hx, value_mem_range x hx⟩⟩

end Scheme

end GlobalTheory.FixedPoint
