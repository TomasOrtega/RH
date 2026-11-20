import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.UnitLemmaGroup
import ReciprocityTheory.DualLattices.ExistsSmulMemOfMemSpan

noncomputable section

namespace GlobalTheory.UnitLemma

open Polynomial

section Act

variable (O : Type) [CommRing O] (E : Type) [Field E] {A : Type} [CommRing A] [Algebra O A] [Algebra E A]

def stLat (g : A) : Set (Submodule O A) := {L | IsLat O E L ∧ ∀ y ∈ L, g * y ∈ L}

/- English proof (translation)
Replace the relevant objects with their definitions. Prove the components needed by the constructor for the conclusion. Assume the hypotheses and unpack their components. Simplify to obtain the desired conclusion from the available facts. Fix the arbitrary inputs or assume the hypotheses.

Supply the required witnesses or components.
-/
theorem mem_mulLat_iff (t : Aˣ) (L : Submodule O A) (x : A) :
    x ∈ mulLat O (t : A) L ↔ ((t⁻¹ : Aˣ) : A) * x ∈ L := by
  unfold mulLat
  constructor
  · rintro ⟨y, hy, rfl⟩
    simpa [← mul_assoc] using hy
  · intro h
    exact ⟨_, h, by simp [← mul_assoc]⟩

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulLat_one (L : Submodule O A) : mulLat O (1 : A) L = L := by
  simp [mulLat, LinearMap.mulLeft_one]

/- English proof (translation)
Simplify using the standard rewrite rules.
-/
theorem mulLat_mul (a b : A) (L : Submodule O A) : mulLat O (a * b) L = mulLat O a (mulLat O b L) := by
  simp [mulLat, LinearMap.mulLeft_mul, Submodule.map_comp]

variable {O E} in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Fix the arbitrary inputs or assume the hypotheses. Supply the required witnesses or components. Fix the arbitrary inputs or assume the hypotheses. Rewrite the hypotheses and the conclusion using the stated equalities. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Use the resulting assumption.
-/
theorem mulLat_mem_stLat {g : A} (t : Aˣ) {L : Submodule O A} (hL : L ∈ stLat O E g) :
    mulLat O (t : A) L ∈ stLat O E g := by
  refine ⟨⟨hL.1.1.map _, ?_⟩, ?_⟩
  · have himg : ((mulLat O (t : A) L : Submodule O A) : Set A) = (LinearMap.mulLeft E (t : A)) '' (L : Set A) := by
      ext x; simp [mulLat]
    rw [himg, Submodule.span_image, hL.1.2, Submodule.map_top, LinearMap.range_eq_top]
    intro z
    exact ⟨((t⁻¹ : Aˣ) : A) * z, by simp [← mul_assoc]⟩
  · intro x hx
    rw [mem_mulLat_iff] at hx ⊢
    have := hL.2 _ hx
    rwa [mul_left_comm]

instance (g : A) : MulAction Aˣ (stLat O E g) where
  smul t L := ⟨mulLat O (t : A) L, mulLat_mem_stLat t L.2⟩
  one_smul L := Subtype.ext (by change mulLat O ((1 : Aˣ) : A) L = L; rw [Units.val_one]; exact mulLat_one O _)
  mul_smul a b L := Subtype.ext (by change mulLat O ((a * b : Aˣ) : A) L = mulLat O (a : A) (mulLat O (b : A) L); rw [Units.val_mul]; exact mulLat_mul O _ _ _)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem stLat_smul_val (g : A) (t : Aˣ) (L : stLat O E g) :
    ((t • L : stLat O E g) : Submodule O A) = mulLat O (t : A) L := rfl

end Act

section Pair

variable (O : Type) [CommRing O] (E : Type) [Field E] {A₁ A₂ : Type} [CommRing A₁] [CommRing A₂]
  [Algebra O A₁] [Algebra O A₂] [Algebra E A₁] [Algebra E A₂]

def LatPair (g₁ : A₁) (g₂ : A₂) : Type := stLat O E g₁ × stLat O E g₂

instance (g₁ : A₁) (g₂ : A₂) : MulAction (A₁ × A₂)ˣ (LatPair O E g₁ g₂) where
  smul t p := (Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2)
  one_smul p := by
    change (_, _) = p
    rw [map_one, map_one, one_smul, one_smul]
    rfl
  mul_smul a b p := by
    change (_, _) = (_, _)
    rw [map_mul, map_mul, mul_smul, mul_smul]
    rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem latPair_smul (g₁ : A₁) (g₂ : A₂) (t : (A₁ × A₂)ˣ) (p : LatPair O E g₁ g₂) :
    t • p = ((Units.map (MonoidHom.fst A₁ A₂) t • p.1, Units.map (MonoidHom.snd A₁ A₂) t • p.2) :
      LatPair O E g₁ g₂) := rfl

variable [IsDomain O] [IsNoetherianRing O] [Algebra O E] [IsFractionRing O E]
  [IsScalarTower O E A₁] [IsScalarTower O E A₂]

variable {O E} in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Establish an intermediate fact. Extract witnesses or component facts from the available result. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs and assume any hypotheses. A detailed English derivation is pending. Establish an intermediate fact. Simplify to obtain the desired conclusion from the available facts. Establish an intermediate fact.

Rewrite the conclusion using the stated equalities. Rewrite the conclusion using the stated equalities. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact.

Simplify to obtain the desired conclusion from the available facts. A detailed English derivation is pending.
-/
theorem comap_inl_mem_stLat {g₁ : A₁} {g₂ : A₂} {M : Submodule O (A₁ × A₂)}
    (hM : M ∈ stLat O E ((g₁, g₂) : A₁ × A₂)) :
    M.comap (LinearMap.inl O A₁ A₂) ∈ stLat O E g₁ := by
  refine ⟨⟨?_, ?_⟩, ?_⟩
  · haveI := isNoetherian_of_fg_of_noetherian M hM.1.1
    have hle : (M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂) ≤ M := Submodule.map_comap_le _ _
    have h1 : (((M.comap (LinearMap.inl O A₁ A₂)).map (LinearMap.inl O A₁ A₂)).comap M.subtype).FG :=
      IsNoetherian.noetherian _
    have h2 := h1.map M.subtype
    rw [Submodule.map_comap_subtype, inf_eq_right.mpr hle] at h2
    exact Submodule.fg_of_fg_map_injective _ LinearMap.inl_injective h2
  · rw [Submodule.eq_top_iff']
    intro y
    have hy : ((y, 0) : A₁ × A₂) ∈ Submodule.span E (M : Set (A₁ × A₂)) := by rw [hM.1.2]; trivial
    obtain ⟨r, hr, hrM⟩ := ReciprocityTheory.PGsh.L2.SecondCohomologyLattice.exists_smul_mem_of_mem_span M hy
    have hrC : algebraMap O E r ≠ 0 := by
      rw [Ne, ← (algebraMap O E).map_zero]
      exact fun h => hr (IsFractionRing.injective O E h)
    have hmem : r • y ∈ M.comap (LinearMap.inl O A₁ A₂) := by
      simpa [Submodule.mem_comap] using hrM
    have : y = (algebraMap O E r)⁻¹ • (algebraMap O E r • y) := by
      rw [smul_smul, inv_mul_cancel₀ hrC, one_smul]
    rw [this, algebraMap_smul]
    exact Submodule.smul_mem _ _ (Submodule.subset_span hmem)
  · intro y hy
    simp only [Submodule.mem_comap, LinearMap.coe_inl] at hy ⊢
    have := hM.2 _ hy
    simpa using this

variable {O E} in
/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. By extensionality, compare the relevant components. Simplify using the standard rewrite rules. Rewrite the conclusion using the stated equalities.

Assume the hypotheses and unpack their components. Supply the required witnesses or components.
-/
theorem map_snd_mem_stLat {g₁ : A₁} {g₂ : A₂} {M : Submodule O (A₁ × A₂)}
    (hM : M ∈ stLat O E ((g₁, g₂) : A₁ × A₂)) :
    M.map (LinearMap.snd O A₁ A₂) ∈ stLat O E g₂ := by
  refine ⟨⟨hM.1.1.map _, ?_⟩, ?_⟩
  · have himg : ((M.map (LinearMap.snd O A₁ A₂) : Submodule O A₂) : Set A₂) =
        (LinearMap.snd E A₁ A₂) '' (M : Set (A₁ × A₂)) := by
      ext x; simp
    rw [himg, Submodule.span_image, hM.1.2, Submodule.map_top, LinearMap.range_eq_top.mpr LinearMap.snd_surjective]
  · rintro _ ⟨m, hm, rfl⟩
    exact ⟨_, hM.2 m hm, by simp⟩

def latProj (g₁ : A₁) (g₂ : A₂) (M : stLat O E ((g₁, g₂) : A₁ × A₂)) : LatPair O E g₁ g₂ :=
  (⟨_, comap_inl_mem_stLat M.2⟩, ⟨_, map_snd_mem_stLat M.2⟩)

end Pair

end GlobalTheory.UnitLemma
