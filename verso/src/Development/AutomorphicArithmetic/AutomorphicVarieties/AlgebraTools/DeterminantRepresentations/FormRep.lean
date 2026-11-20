import Development.AutomorphicArithmetic.AutomorphicVarieties.WeilGroupCharacters.UniversalOrdinaryDeterminantRing
import Development.AutomorphicArithmetic.AutomorphicVarieties.AlgebraTools.DeterminantRepresentations.StarApi

open Polynomial Matrix UpperTheory.V UpperTheory.V.W

/- English proof (translation)
Simplify using `[GDet.repAlg]`.
-/
private theorem repAlg_single {G R : Type} [Group G] [CommRing R] {a : ℕ} (ρ : G →* Matrix (Fin a) (Fin a) R)
    (B : Type) [CommRing B] [Algebra R B] (g : G) (b : B) :
    GDet.repAlg ρ B (MonoidAlgebra.single g b) = b • (ρ g).map (algebraMap R B) := by
  simp [GDet.repAlg]

/- English proof (translation)
Establish `e : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g)`. Use `ext`. Simplify using `[GFrame.eps, IsScalarTower.algebraMap_apply O R B]`. Rewrite using `[e, ← map_zpow]`. Both sides reduce to the same expression.
-/
private theorem UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O]
    [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (B : Type) [CommRing B] [Algebra R B]
    [Algebra O B] [IsScalarTower O R B] (g : F.G₀) (k : ℤ) :
    ((F.eps O B g ^ k : Bˣ) : B) = algebraMap R B ((F.eps O R g ^ k : Rˣ) : R) := by
  have e : F.eps O B g = Units.map (algebraMap R B : R →* B) (F.eps O R g) := by
    ext
    simp [GFrame.eps, IsScalarTower.algebraMap_apply O R B]
  rw [e, ← map_zpow]
  rfl

/- English proof (translation)
Introduce `l _ F O _ _ R _ _ n a r P hP`. Establish `h1 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀), (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) = (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B …`. Introduce `B _ _ _ _ y`. Set `ρ' : F.G₀ →* Matrix (Fin a) (Fin a) B` to `(algebraMap R B).mapMatrix.toMonoidHom.comp (mat r)`. Establish `hρ : ∀ g, (mat r g).map (algebraMap R B) = ρ' g` using `fun g => rfl`.

Proceed by induction on `y using MonoidAlgebra.induction_linear with`. Consider the case `zero => simp [GFrame.star]`. Consider the case `add x z hx hz`. Rewrite using `[(UpperTheory.V.AlgebraTools.Det.starApi F O B n).2.2.1, map_add, map_add, Matrix.transpose_add, Matrix.add_mul, Matrix.mul_add, hx, hz]`. Consider the case `single g b`.

Establish `hs : F.star O B n (MonoidAlgebra.single g b) = MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B))`. Simplify using `[GFrame.star, GFrame.starOp]`. Rewrite using `[hs, repAlg_single, repAlg_single, hρ, hρ, UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq F O R B]`. Establish `hF : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) = algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)`. Use `congrArg (fun M : Matrix (Fin a) (Fin a) R => M.map (algebraMap R B)) (hP g)` as an intermediate fact.

Establish `h' : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) = ((((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R)) • (P : Matrix (Fin a) (Fin a) R)).map (algebraMap R B)`. Simplify `this` using `[Matrix.map_mul, Matrix.transpose_map, ρ']`. Rewrite using `[h']`. Use extensionality with `i j`. Simplify using the standard rewrite rules.

Establish `hinv : ρ' (F.conj g) * ρ' (F.conj g)⁻¹ = 1`. Rewrite using `[← map_mul, mul_inv_cancel, map_one]`. Establish `key : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) = algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g)⁻¹)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hinv, Matrix.mul_one]`.

Use `_ = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) * ρ' (F.conj g)⁻¹ := by`. Simplify using `only [Matrix.mul_assoc]`. Use `_ = _ := by rw [hF, Matrix.smul_mul]`. Rewrite using `[Matrix.transpose_smul, Matrix.smul_mul, key, Matrix.mul_smul, smul_smul]`. Establish `hu : ∀ (B : Type) [CommRing B] [Algebra R B], IsUnit ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B))`.

Introduce `B _ _`. Conclude with `(P.isUnit.map (algebraMap R B).mapMatrix)`. Use `⟨h1, ?_, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Use `h1 R y` as an intermediate fact.

Rewrite `this` using `[hy, Matrix.transpose_zero, Matrix.zero_mul]`. Take `⟨u, hu'⟩` from `hu R`. Establish `h2` using `congrArg (fun M => (↑u⁻¹ : Matrix (Fin a) (Fin a) R) * M) this`. Simplify using `only [← hu', Matrix.mul_zero, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2`. Conclude with `h2.symm`.

Introduce `B _ _ _ _ y`. Use `congrArg Matrix.det (h1 B y)` as an intermediate fact. Rewrite `this` using `[Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm]`. Establish `hd` using `(Matrix.isUnit_iff_isUnit_det _).mp (hu B)`. Conclude with `(hd.mul_left_cancel this).symm`.
-/
theorem UpperTheory.V.AlgebraTools.Det.formRep :
    ∀ {l : ℕ} [Fact l.Prime] (F : GFrame l) (O : Type) [CommRing O] [Algebra ℤ_[l] O] (R : Type) [CommRing R] [Algebra O R] (n : ℕ) {a : ℕ} (r : F.G₀ →* GL (Fin a) R) (P : GL (Fin a) R), F.IsForm O n r P →
    (∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y)) ∧
    (∀ y, GDet.repAlg (mat r) R y = 0 → GDet.repAlg (mat r) R (F.star O R n y) = 0) ∧
    ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.ofRep (mat r)).D B (F.star O B n y) = (GDet.ofRep (mat r)).D B y := by
  intro l _ F O _ _ R _ _ n a r P hP
  have h1 : ∀ (B : Type) [CommRing B] [Algebra R B] [Algebra O B] [IsScalarTower O R B] (y : MonoidAlgebra B F.G₀),
      (GDet.repAlg (mat r) B y)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
        (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * GDet.repAlg (mat r) B (F.star O B n y) := by
    intro B _ _ _ _ y
    let ρ' : F.G₀ →* Matrix (Fin a) (Fin a) B := (algebraMap R B).mapMatrix.toMonoidHom.comp (mat r)
    have hρ : ∀ g, (mat r g).map (algebraMap R B) = ρ' g := fun g => rfl
    induction y using MonoidAlgebra.induction_linear with
    | zero => simp [GFrame.star]
    | add x z hx hz =>
      rw [(UpperTheory.V.AlgebraTools.Det.starApi F O B n).2.2.1, map_add, map_add, Matrix.transpose_add, Matrix.add_mul,
        Matrix.mul_add, hx, hz]
    | single g b =>
      have hs : F.star O B n (MonoidAlgebra.single g b) =
          MonoidAlgebra.single (F.conj g)⁻¹ (b * ((F.eps O B g ^ (1 - (n:ℤ)) : Bˣ) : B)) := by
        simp [GFrame.star, GFrame.starOp]
      rw [hs, repAlg_single, repAlg_single, hρ, hρ, UpperTheory.V.AlgebraTools.Det.eps_zpow_algebraMap_eq F O R B]
      have hF : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) • (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) := by
        have := congrArg (fun M : Matrix (Fin a) (Fin a) R => M.map (algebraMap R B)) (hP g)
        have h' : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) =
            ((((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R)) • (P : Matrix (Fin a) (Fin a) R)).map (algebraMap R B) := by
          simpa [Matrix.map_mul, Matrix.transpose_map, ρ'] using this
        rw [h']
        ext i j
        simp
      have hinv : ρ' (F.conj g) * ρ' (F.conj g)⁻¹ = 1 := by
        rw [← map_mul, mul_inv_cancel, map_one]
      have key : (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) =
          algebraMap R B ((F.eps O R g ^ (1 - (n:ℤ)) : Rˣ) : R) •
            ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g)⁻¹) := by
        calc (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)
            = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * (ρ' (F.conj g) * ρ' (F.conj g)⁻¹) := by
              rw [hinv, Matrix.mul_one]
          _ = (ρ' g)ᵀ * (P : Matrix (Fin a) (Fin a) R).map (algebraMap R B) * ρ' (F.conj g) * ρ' (F.conj g)⁻¹ := by
              simp only [Matrix.mul_assoc]
          _ = _ := by rw [hF, Matrix.smul_mul]
      rw [Matrix.transpose_smul, Matrix.smul_mul, key, Matrix.mul_smul, smul_smul]
  have hu : ∀ (B : Type) [CommRing B] [Algebra R B],
      IsUnit ((P : Matrix (Fin a) (Fin a) R).map (algebraMap R B)) := by
    intro B _ _
    exact (P.isUnit.map (algebraMap R B).mapMatrix)
  refine ⟨h1, ?_, ?_⟩
  · intro y hy
    have := h1 R y
    rw [hy, Matrix.transpose_zero, Matrix.zero_mul] at this
    obtain ⟨u, hu'⟩ := hu R
    have h2 := congrArg (fun M => (↑u⁻¹ : Matrix (Fin a) (Fin a) R) * M) this
    simp only [← hu', Matrix.mul_zero, ← Matrix.mul_assoc, Units.inv_mul, Matrix.one_mul] at h2
    exact h2.symm
  · intro B _ _ _ _ y
    have := congrArg Matrix.det (h1 B y)
    rw [Matrix.det_mul, Matrix.det_mul, Matrix.det_transpose, mul_comm] at this
    have hd := (Matrix.isUnit_iff_isUnit_det _).mp (hu B)
    exact (hd.mul_left_cancel this).symm
