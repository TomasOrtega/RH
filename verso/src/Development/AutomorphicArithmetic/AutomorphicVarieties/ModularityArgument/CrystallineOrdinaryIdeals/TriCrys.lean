import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.TriDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineExtensionIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrystallineUpperTriangularIffMemFiniteCocycles
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.IsCrysOfInertia
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.CrystallineOrdinaryIdeals.DiagonalizeOfDistinctEigenvaluesStatement
open Formalism.BasicNotions Formalism.BasicNotions.Loc ReciprocityTheory.Gal Module UpperTheory.V.Loc UpperTheory.V.U3 UpperTheory.V.Alg IsLocalRing Polynomial Topology

namespace GlobalTheory

/- English proof (translation)
Introduce `hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκ hI x y z ρ hz hρ hxf hyf`. Establish `hxc : Continuous x` using `hxf.1.1`. Establish `hyc : Continuous y` using `hyf.1.1`. Establish `hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h` using `fun g h => hxf.1.2 g h`. Establish `crκ : ∀ i, IsCr φ (chRep (κ i))` using `fun i => crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i) fun g hg v => by`.

Rewrite using `[chRep_apply, hI g hg i, smul_eq_mul]`. Establish `hext : IsCr φ (ext2 (κ 0) (κ 1) x hx)` using `(UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ (κ 0) (κ 1) (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf`. Establish `hmat : ∀ g h (i j : Fin 3), (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j = ((ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B)) i j` using `fun g h i j => by`. Rewrite using `[map_mul, Units.val_mul]`. Establish `hZ : (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx))`.

Use `⟨hz.prodMk hyc, fun g h => ?_⟩` and prove the remaining obligations. Establish `h02` using `hmat g h 0 2`. Establish `h12` using `hmat g h 1 2`. Rewrite `h02`, `h12` using `[hρ, hρ, hρ]`. Simplify using `[triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12`.

Establish `hu : ((κ 2 g : Bˣ) : B) * (((κ 2 g)⁻¹ : Bˣ) : B) = 1` using `Units.mul_inv _`. Establish `hv : ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B) = 1` using `Units.mul_inv _`. Rewrite using `[twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]`. Use `ext`. Simplify using the standard rewrite rules.

Take the linear combination `((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h02 - ((z (g * h) - z g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((z (g * h) - z g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv`. Simplify using the standard rewrite rules. Take the linear combination `((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h12 - ((y (g * h) - y g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((y (g * h) - y g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 1 g : Bˣ) : B) * y h)) * hv`. Conclude with `(UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2 (GlobalTheory.T.ordinary_lift_local_iso hP φ hφ π hπ e he κ hκ hI x hx hxc hext y z hZ hyf)`.
-/
theorem tri_crys : LocalPublishedTheorems → ∀ {l : ℕ} [Fact l.Prime] {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (φ : G →* GQ l) (hφ : IsOpenEmbedding φ) {E : Type} [Field E] [Algebra ℚ_[l] E] [FiniteDimensional ℚ_[l] E] [Algebra ℤ_[l] E] [IsScalarTower ℤ_[l] ℚ_[l] E] {B : Type} [CommRing B] [Algebra ℚ_[l] B] [Module.Finite ℚ_[l] B] [TopologicalSpace B] [IsModuleTopology ℚ_[l] B] [IsTopologicalRing B] [Algebra ℤ_[l] B] [IsScalarTower ℤ_[l] ℚ_[l] B] [Algebra E B] [IsScalarTower ℚ_[l] E B] (π : B →ₐ[E] E) (hπ : ∀ a, π a = 0 → IsNilpotent a) (e : ℕ), 1 ≤ e → ∀ (κ : Fin 3 → G →* Bˣ), (∀ i, Continuous fun g => (κ i g : B)) → (∀ g, φ g ∈ Iq l → ∀ i, κ i g = cycA l l B (φ g) ^ ((e : ℤ) * wt1 i)) → ∀ (x y z : G → B) (ρ : G →* GL (Fin 3) B), Continuous z → (∀ g, (ρ g : Matrix (Fin 3) (Fin 3) B) = triM (fun i => κ i g) (x g) (y g) (z g)) → x ∈ finiteCocycles φ (chRep (κ 0 / κ 1)) → y ∈ finiteCocycles φ (chRep (κ 1 / κ 2)) → IsCr φ (colRep ρ) := by
  intro hP l _ G _ _ _ φ hφ E _ _ _ _ _ B _ _ _ _ _ _ _ _ _ _ π hπ e he κ hκ hI x y z ρ hz hρ hxf hyf
  have hxc : Continuous x := hxf.1.1
  have hyc : Continuous y := hyf.1.1
  have hx : ∀ g h, x (g * h) = x g + ((κ 0 / κ 1) g : Bˣ) * x h := fun g h => hxf.1.2 g h
  have crκ : ∀ i, IsCr φ (chRep (κ i)) := fun i =>
    crUnr φ hφ (chRep (κ i)) (contAction_chRep (hκ i)) ((e : ℤ) * wt1 i) fun g hg v => by
      rw [chRep_apply, hI g hg i, smul_eq_mul]
  have hext : IsCr φ (ext2 (κ 0) (κ 1) x hx) :=
    (UpperTheory.isCrystalline_extension_iff_mem_finiteCocycles φ hφ (κ 0) (κ 1) (hκ 0) (hκ 1) x hx hxc (crκ 0) (crκ 1)).2 hxf
  have hmat : ∀ g h (i j : Fin 3), (ρ (g * h) : Matrix (Fin 3) (Fin 3) B) i j =
      ((ρ g : Matrix (Fin 3) (Fin 3) B) * (ρ h : Matrix (Fin 3) (Fin 3) B)) i j := fun g h i j => by
    rw [map_mul, Units.val_mul]
  have hZ : (fun g => (z g, y g)) ∈ Z1 (twist (κ 2)⁻¹ (ext2 (κ 0) (κ 1) x hx)) := by
    refine ⟨hz.prodMk hyc, fun g h => ?_⟩
    have h02 := hmat g h 0 2
    have h12 := hmat g h 1 2
    rw [hρ, hρ, hρ] at h02 h12
    simp [triM, Matrix.mul_apply, Fin.sum_univ_three, map_mul, Units.val_mul] at h02 h12

    have hu : ((κ 2 g : Bˣ) : B) * (((κ 2 g)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    have hv : ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B) = 1 := Units.mul_inv _
    rw [twist_apply, characterExtensionRep_apply, MonoidHom.inv_apply]
    ext
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h02 - ((z (g * h) - z g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((z (g * h) - z g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 0 g : Bˣ) : B) * z h + x g * ((κ 1 g : Bˣ) : B) * y h)) * hv
    · simp
      linear_combination ((((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * h12 - ((y (g * h) - y g) * ((κ 2 h : Bˣ) : B) * (((κ 2 h)⁻¹ : Bˣ) : B)) * hu - ((y (g * h) - y g) - (((κ 2 g)⁻¹ : Bˣ) : B) * (((κ 1 g : Bˣ) : B) * y h)) * hv
  exact (UpperTheory.isCrystalline_upperTriangular_iff_mem_finiteCocycles φ hφ κ hκ x y z ρ hxc hyc hz hρ hx hext (crκ 2)).2
    (GlobalTheory.T.ordinary_lift_local_iso hP φ hφ π hπ e he κ hκ hI x hx hxc hext y z hZ hyf)

end GlobalTheory
