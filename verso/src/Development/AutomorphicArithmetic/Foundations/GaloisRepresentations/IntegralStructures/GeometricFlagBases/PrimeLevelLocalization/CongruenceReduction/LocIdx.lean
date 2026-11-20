import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.IntegralStructures.GeometricFlagBases.PrimeLevelLocalization.CongruenceReduction.LevLocAlt
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.Tjcosets

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.UPel.HT GlobalTheory.LKTrip GlobalTheory.LKGeo GlobalTheory.LKDef
open GlobalTheory.LFun (KGL)
open UpperTheory.Gal.CertificateRingHomMap (GUf Plc GLw AfQ sim comp loc SameK IsCen cj)
open UpperTheory.Gal.W2.Seed (Arith Setup)
open UpperTheory.Gal.Int.Geo UpperTheory.Gal.Int.Geo.Pl UpperTheory.Gal.Int.Geo.Pl.Tj
attribute [local instance] Ideal.Quotient.field

noncomputable section

namespace UpperTheory.Gal.Int.Geo.Pl.Tj.LocalIndices

section Lin

variable {κ : Type} [Field κ] {n j : ℕ}

/- English proof (translation)
Establish `hinj : Function.Injective (g : Matrix (Fin n) (Fin n) κ).mulVecLin`. Introduce `x y h`. Use `congrArg ((g⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec h` as an intermediate fact. Simplify `this` using `[Matrix.mulVec_mulVec]`. Conclude with `(Submodule.equivMapOfInjective _ hinj D).finrank_eq.symm`.
-/
private theorem map_finrank (g : GL (Fin n) κ) (D : Submodule κ (Fin n → κ)) :
    Module.finrank κ (D.map (g : Matrix (Fin n) (Fin n) κ).mulVecLin) = Module.finrank κ D := by
  have hinj : Function.Injective (g : Matrix (Fin n) (Fin n) κ).mulVecLin := by
    intro x y h
    have := congrArg ((g⁻¹ : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVec h
    simpa [Matrix.mulVec_mulVec] using this
  exact (Submodule.equivMapOfInjective _ hinj D).finrank_eq.symm

@[reducible] private def actGr (j : ℕ) : MulAction (GL (Fin n) κ) (UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j) where
  smul g D := ⟨D.1.map (g : Matrix (Fin n) (Fin n) κ).mulVecLin, (map_finrank g D.1).trans D.2⟩
  one_smul D := by
    apply Subtype.ext
    show D.1.map ((1 : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVecLin = D.1
    simp
  mul_smul g h D := by
    apply Subtype.ext
    show D.1.map ((g * h : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ).mulVecLin =
      (D.1.map (h : Matrix (Fin n) (Fin n) κ).mulVecLin).map (g : Matrix (Fin n) (Fin n) κ).mulVecLin
    rw [← Submodule.map_comp, Units.val_mul, Matrix.mulVecLin_mul]

/- English proof (translation)
Take `⟨C₁, h₁⟩` from `Submodule.exists_isCompl D₁`. Take `⟨C₂, h₂⟩` from `Submodule.exists_isCompl D₂`. Establish `hc : Module.finrank κ C₁ = Module.finrank κ C₂`. Establish `a₁` using `Submodule.finrank_add_eq_of_isCompl h₁`. Establish `a₂` using `Submodule.finrank_add_eq_of_isCompl h₂`.

Use linear arithmetic over natural numbers and integers. Set `eD : D₁ ≃ₗ[κ] D₂` to `LinearEquiv.ofFinrankEq _ _ h`. Set `eC : C₁ ≃ₗ[κ] C₂` to `LinearEquiv.ofFinrankEq _ _ hc`. Set `e : (Fin n → κ) ≃ₗ[κ] (Fin n → κ)` to `(Submodule.prodEquivOfIsCompl D₁ C₁ h₁).symm.trans ((eD.prodCongr eC).trans (Submodule.prodEquivOfIsCompl D₂ C₂ h₂))`. Establish `he : ∀ x : D₁, e x = eD x`.

Introduce `x`. Simplify using `only [e, LinearEquiv.trans_apply]`. Rewrite using `[Submodule.prodEquivOfIsCompl_symm_apply_left]`. Simplify using the standard rewrite rules. Set `M` to `LinearMap.toMatrix' (e : (Fin n → κ) →ₗ[κ] (Fin n → κ))`.

Set `M'` to `LinearMap.toMatrix' (e.symm : (Fin n → κ) →ₗ[κ] (Fin n → κ))`. Establish `hMM : M * M' = 1`. Simplify using `only [M, M']`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules.

Establish `hMM' : M' * M = 1`. Simplify using `only [M, M']`. Rewrite using `[← LinearMap.toMatrix'_comp]`. Simplify using the standard rewrite rules. Use `⟨⟨M, M', hMM, hMM'⟩, ?_⟩` and prove the remaining obligations.

Establish `hlin : (M.mulVecLin) = (e : (Fin n → κ) →ₗ[κ] (Fin n → κ))`. Simplify using `only [M]`. Rewrite using `[Matrix.mulVecLin, ]`. Conclude with `Matrix.toLin'_toMatrix' _`. Use `show D₁.map M.mulVecLin = D₂`.

Rewrite using `[hlin]`. Apply `le_antisymm` to reduce the goal to its premises. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Use `he ⟨x, hx⟩` as an intermediate fact. Simplify using `only [LinearEquiv.coe_coe]`.

Rewrite using `[this]`. Conclude with `(eD ⟨x, hx⟩).2`. Introduce `y hy`. Use `⟨(eD.symm ⟨y, hy⟩ : D₁), (eD.symm ⟨y, hy⟩).2, ?_⟩` and prove the remaining obligations. Simplify using `only [LinearEquiv.coe_coe]`.

Rewrite using `[he]`. Simplify using the standard rewrite rules.
-/
private theorem exists_gl (D₁ D₂ : Submodule κ (Fin n → κ))
    (h : Module.finrank κ D₁ = Module.finrank κ D₂) :
    ∃ g : GL (Fin n) κ, D₁.map (g : Matrix (Fin n) (Fin n) κ).mulVecLin = D₂ := by
  obtain ⟨C₁, h₁⟩ := Submodule.exists_isCompl D₁
  obtain ⟨C₂, h₂⟩ := Submodule.exists_isCompl D₂
  have hc : Module.finrank κ C₁ = Module.finrank κ C₂ := by
    have a₁ := Submodule.finrank_add_eq_of_isCompl h₁
    have a₂ := Submodule.finrank_add_eq_of_isCompl h₂
    omega
  let eD : D₁ ≃ₗ[κ] D₂ := LinearEquiv.ofFinrankEq _ _ h
  let eC : C₁ ≃ₗ[κ] C₂ := LinearEquiv.ofFinrankEq _ _ hc
  let e : (Fin n → κ) ≃ₗ[κ] (Fin n → κ) :=
    (Submodule.prodEquivOfIsCompl D₁ C₁ h₁).symm.trans
      ((eD.prodCongr eC).trans (Submodule.prodEquivOfIsCompl D₂ C₂ h₂))
  have he : ∀ x : D₁, e x = eD x := by
    intro x
    simp only [e, LinearEquiv.trans_apply]
    rw [Submodule.prodEquivOfIsCompl_symm_apply_left]
    simp
  let M := LinearMap.toMatrix' (e : (Fin n → κ) →ₗ[κ] (Fin n → κ))
  let M' := LinearMap.toMatrix' (e.symm : (Fin n → κ) →ₗ[κ] (Fin n → κ))
  have hMM : M * M' = 1 := by
    simp only [M, M']
    rw [← LinearMap.toMatrix'_comp]
    simp
  have hMM' : M' * M = 1 := by
    simp only [M, M']
    rw [← LinearMap.toMatrix'_comp]
    simp
  refine ⟨⟨M, M', hMM, hMM'⟩, ?_⟩
  have hlin : (M.mulVecLin) = (e : (Fin n → κ) →ₗ[κ] (Fin n → κ)) := by
    simp only [M]
    rw [Matrix.mulVecLin, ]
    exact Matrix.toLin'_toMatrix' _
  show D₁.map M.mulVecLin = D₂
  rw [hlin]
  apply le_antisymm
  · rintro _ ⟨x, hx, rfl⟩
    have := he ⟨x, hx⟩
    simp only [LinearEquiv.coe_coe]
    rw [this]
    exact (eD ⟨x, hx⟩).2
  · intro y hy
    refine ⟨(eD.symm ⟨y, hy⟩ : D₁), (eD.symm ⟨y, hy⟩).2, ?_⟩
    simp only [LinearEquiv.coe_coe]
    rw [he]
    simp

private def stdU (n j : ℕ) (κ : Type) [Field κ] : Submodule κ (Fin n → κ) where
  carrier := {x | ∀ a : Fin n, j ≤ (a : ℕ) → x a = 0}
  add_mem' := by
    intro x y hx hy a ha
    simp [hx a ha, hy a ha]
  zero_mem' := by intro a _; rfl
  smul_mem' := by
    intro c x hx a ha
    simp [hx a ha]

/- English proof (translation)
Set `e : stdU n j κ ≃ₗ[κ] (Fin j → κ)` to `{ toFun := fun x b => x.1 (Fin.castLE hj b) map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl invFun := fun y => ⟨fun a => if h : (a : ℕ) < j then y ⟨a, h⟩ else 0, by`. Introduce `a ha`. Simplify using `[not_lt.2 ha]⟩`. Use `left_inv := by`. Introduce `x`.

Apply `Subtype.ext` to reduce the goal to its premises. Use function extensionality and compare the values at `a`. Distinguish the cases in `h : (a : ℕ) < j`. Simplify using `[h, Fin.castLE]`. Simplify using `[h, x.2 a (not_lt.1 h)]`.

Use `right_inv := by`. Introduce `y`. Use function extensionality and compare the values at `b`. Simplify using `[Fin.castLE] }`. Rewrite using `[e.finrank_eq]`.

Simplify using the standard rewrite rules.
-/
private theorem finrank_stdU (hj : j ≤ n) : Module.finrank κ (stdU n j κ) = j := by
  let e : stdU n j κ ≃ₗ[κ] (Fin j → κ) :=
    { toFun := fun x b => x.1 (Fin.castLE hj b)
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl
      invFun := fun y => ⟨fun a => if h : (a : ℕ) < j then y ⟨a, h⟩ else 0, by
        intro a ha
        simp [not_lt.2 ha]⟩
      left_inv := by
        intro x
        apply Subtype.ext
        funext a
        by_cases h : (a : ℕ) < j
        · simp [h, Fin.castLE]
        · simp [h, x.2 a (not_lt.1 h)]
      right_inv := by
        intro y
        funext b
        simp [Fin.castLE] }
  rw [e.finrank_eq]
  simp

/- English proof (translation)
Introduce and unpack `_ ⟨x, hx, rfl⟩ a ha`. Simplify using `only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `hb : (b : ℕ) < j`. Rewrite using `[hg a b ha hb, zero_mul]`.

Rewrite using `[hx b (not_lt.1 hb), mul_zero]`.
-/
private theorem stdU_map_le (g : GL (Fin n) κ) (j : ℕ)
    (hg : ∀ a b : Fin n, j ≤ (a : ℕ) → (b : ℕ) < j → (g : Matrix (Fin n) (Fin n) κ) a b = 0) :
    (stdU n j κ).map (g : Matrix (Fin n) (Fin n) κ).mulVecLin ≤ stdU n j κ := by
  rintro _ ⟨x, hx, rfl⟩ a ha
  simp only [Matrix.mulVecLin_apply, Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun b _ => ?_
  by_cases hb : (b : ℕ) < j
  · rw [hg a b ha hb, zero_mul]
  · rw [hx b (not_lt.1 hb), mul_zero]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h a b ha hb`. Establish `hmem : (Pi.single b 1 : Fin n → κ) ∈ stdU n j κ`. Introduce `c hc`. Establish `: c ≠ b`.

Introduce and unpack `rfl`. Use linear arithmetic over natural numbers and integers. Simplify using `[this]`. Establish `h2 : (g : Matrix (Fin n) (Fin n) κ).mulVecLin (Pi.single b 1) ∈ stdU n j κ`. Rewrite using `[← h]`.

Conclude with `⟨_, hmem, rfl⟩`. Establish `h3` using `h2 a ha`. Simplify using `using h3`. Introduce `h`. Apply `Submodule.eq_of_le_of_finrank_eq (stdU_map_le g j h)` to reduce the goal to its premises.

Rewrite using `[map_finrank]`.
-/
private theorem map_stdU_iff (g : GL (Fin n) κ) (hj : j ≤ n) :
    (stdU n j κ).map (g : Matrix (Fin n) (Fin n) κ).mulVecLin = stdU n j κ ↔
      ∀ a b : Fin n, j ≤ (a : ℕ) → (b : ℕ) < j → (g : Matrix (Fin n) (Fin n) κ) a b = 0 := by
  constructor
  · intro h a b ha hb
    have hmem : (Pi.single b 1 : Fin n → κ) ∈ stdU n j κ := by
      intro c hc
      have : c ≠ b := by
        rintro rfl
        omega
      simp [this]
    have h2 : (g : Matrix (Fin n) (Fin n) κ).mulVecLin (Pi.single b 1) ∈ stdU n j κ := by
      rw [← h]
      exact ⟨_, hmem, rfl⟩
    have h3 := h2 a ha
    simpa using h3
  · intro h
    apply Submodule.eq_of_le_of_finrank_eq (stdU_map_le g j h)
    rw [map_finrank]

end Lin

section Idx

variable {κ : Type} [Field κ] {n j : ℕ}

private def x0 (n j : ℕ) (κ : Type) [Field κ] (hj : j ≤ n) : UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j :=
  ⟨stdU n j κ, finrank_stdU hj⟩

private def stabS (n j : ℕ) (κ : Type) [Field κ] (hj : j ≤ n) : Subgroup (GL (Fin n) κ) :=
  @MulAction.stabilizer _ _ _ (actGr j) (x0 n j κ hj)

/- English proof (translation)
Rewrite using `[← map_stdU_iff g hj]`. Use `letI := actGr (κ := κ) (n := n) j`. Use `show g • x0 n j κ hj = x0 n j κ hj ↔ _`. Conclude with `⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩`.
-/
private theorem mem_stabS (hj : j ≤ n) (g : GL (Fin n) κ) :
    g ∈ stabS n j κ hj ↔
      ∀ a b : Fin n, j ≤ (a : ℕ) → (b : ℕ) < j → (g : Matrix (Fin n) (Fin n) κ) a b = 0 := by
  rw [← map_stdU_iff g hj]
  letI := actGr (κ := κ) (n := n) j
  show g • x0 n j κ hj = x0 n j κ hj ↔ _
  exact ⟨fun h => congrArg Subtype.val h, fun h => Subtype.ext h⟩

/- English proof (translation)
Use `letI := actGr (κ := κ) (n := n) j`. Establish `: MulAction.IsPretransitive (GL (Fin n) κ) (UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j)`. Use `⟨fun x y => ?_⟩` and prove the remaining obligations. Take `⟨g, hg⟩` from `exists_gl x.1 y.1 (x.2.trans y.2.symm)`. Conclude with `⟨g, Subtype.ext hg⟩`.

Unfold `stabS`. Rewrite using `[MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]`.
-/
private theorem index_stabS (hj : j ≤ n) :
    (stabS n j κ hj).index = Nat.card (UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j) := by
  letI := actGr (κ := κ) (n := n) j
  have : MulAction.IsPretransitive (GL (Fin n) κ) (UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j) := by
    refine ⟨fun x y => ?_⟩
    obtain ⟨g, hg⟩ := exists_gl x.1 y.1 (x.2.trans y.2.symm)
    exact ⟨g, Subtype.ext hg⟩
  unfold stabS
  rw [MulAction.index_stabilizer, MulAction.orbit_eq_univ, Set.ncard_univ]

end Idx

section Loc

open Formalism.UG Formalism.UG.P

variable {L : Type} [Field L] (O : Subring L) [IsLocalRing O] {κ : Type} [Field κ]
  (e : IsLocalRing.ResidueField O ≃+* κ)

private def red (n : ℕ) : GLint (Fin n) O →* GL (Fin n) κ :=
  (Formalism.UG.bc (e : IsLocalRing.ResidueField O →+* κ)).comp (tjcosets_red O n)

/- English proof (translation)
Introduce `x`. Take `⟨k, hk⟩` from `tjcosets_red_surjective O n (Formalism.UG.bc (e.symm : κ →+* IsLocalRing.ResidueField O) x)`. Use `⟨k, ?_⟩` and prove the remaining obligations. Use `show Formalism.UG.bc (e : IsLocalRing.ResidueField O →+* κ) (tjcosets_red O n k) = x`. Rewrite using `[hk]`.

Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `a b`. Rewrite using `[tjcosets_bc_apply, tjcosets_bc_apply]`. Simplify using the standard rewrite rules.
-/
private theorem red_surjective (n : ℕ) : Function.Surjective (red O e n) := by
  intro x
  obtain ⟨k, hk⟩ := tjcosets_red_surjective O n (Formalism.UG.bc (e.symm : κ →+* IsLocalRing.ResidueField O) x)
  refine ⟨k, ?_⟩
  show Formalism.UG.bc (e : IsLocalRing.ResidueField O →+* κ) (tjcosets_red O n k) = x
  rw [hk]
  apply Units.ext
  ext a b
  rw [tjcosets_bc_apply, tjcosets_bc_apply]
  simp

/- English proof (translation)
Use `show ((Formalism.UG.bc (e : IsLocalRing.ResidueField O →+* κ) (tjcosets_red O n (tjcosets_iso n O g)) : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) a b = _`. Rewrite using `[tjcosets_red_iso, tjcosets_bc_apply, tjcosets_bc_apply]`. Both sides reduce to the same expression.
-/
private theorem red_iso_apply (n : ℕ) (g : GL (Fin n) O) (a b : Fin n) :
    ((red O e n (tjcosets_iso n O g) : GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) a b =
      e (IsLocalRing.residue O ((g : Matrix (Fin n) (Fin n) O) a b)) := by
  show ((Formalism.UG.bc (e : IsLocalRing.ResidueField O →+* κ) (tjcosets_red O n (tjcosets_iso n O g)) :
    GL (Fin n) κ) : Matrix (Fin n) (Fin n) κ) a b = _
  rw [tjcosets_red_iso, tjcosets_bc_apply, tjcosets_bc_apply]
  rfl

variable {O}

/- English proof (translation)
Rewrite using `[inv_inv]`. Prove the components needed by the constructor for the conclusion. Introduce `H a b ha hb`. Use `H a b` as an intermediate fact. Rewrite `this` using `[if_neg (by omega), if_pos hb, one_mul, mul_comm]`.

Conclude with `(hmax _).1 this`. Introduce `H a b`. Apply the tactic sequence `by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j`. Rewrite using `[if_pos ha, if_pos hb]`. Establish `: ϖ * (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * ϖ⁻¹ = (((h : Matrix (Fin n) (Fin n) O) a b : O) : L)` using `by field_simp`.

Rewrite using `[this]`. Conclude with `((h : Matrix (Fin n) (Fin n) O) a b).2`. Rewrite using `[if_pos ha, if_neg hb, mul_one]`. Conclude with `O.mul_mem hϖO ((h : Matrix (Fin n) (Fin n) O) a b).2`. Rewrite using `[if_neg ha, if_pos hb, one_mul, mul_comm]`.

Conclude with `(hmax _).2 (H a b (by omega) hb)`. Rewrite using `[if_neg ha, if_neg hb, one_mul, mul_one]`. Conclude with `((h : Matrix (Fin n) (Fin n) O) a b).2`.
-/
private theorem entries_iff (n j : ℕ) (ϖ : L) (hϖ : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0) (h : GL (Fin n) O) :
    (∀ a b : Fin n, (if (a : ℕ) < j then ϖ⁻¹⁻¹ else 1) *
        (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * (if (b : ℕ) < j then ϖ⁻¹ else 1) ∈ O) ↔
      ∀ a b : Fin n, j ≤ (a : ℕ) → (b : ℕ) < j →
        IsLocalRing.residue O ((h : Matrix (Fin n) (Fin n) O) a b) = 0 := by
  rw [inv_inv]
  constructor
  · intro H a b ha hb
    have := H a b
    rw [if_neg (by omega), if_pos hb, one_mul, mul_comm] at this
    exact (hmax _).1 this
  · intro H a b
    by_cases ha : (a : ℕ) < j <;> by_cases hb : (b : ℕ) < j
    · rw [if_pos ha, if_pos hb]
      have : ϖ * (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) * ϖ⁻¹ =
          (((h : Matrix (Fin n) (Fin n) O) a b : O) : L) := by field_simp
      rw [this]; exact ((h : Matrix (Fin n) (Fin n) O) a b).2
    · rw [if_pos ha, if_neg hb, mul_one]
      exact O.mul_mem hϖO ((h : Matrix (Fin n) (Fin n) O) a b).2
    · rw [if_neg ha, if_pos hb, one_mul, mul_comm]
      exact (hmax _).2 (H a b (by omega) hb)
    · rw [if_neg ha, if_neg hb, one_mul, mul_one]
      exact ((h : Matrix (Fin n) (Fin n) O) a b).2

/- English proof (translation)
Use `set d := tjcosets_dG n j ϖ⁻¹ (inv_ne_zero hϖ) with hd`. Establish `hinv : (d⁻¹ * Formalism.UG.bc O.subtype g * d)⁻¹ = d⁻¹ * Formalism.UG.bc O.subtype g⁻¹ * d`. Simplify using `only [map_inv]`. Use `group`. Establish `key : ∀ h : GL (Fin n) O, (∀ a b, ((d⁻¹ * Formalism.UG.bc O.subtype h * d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) ↔ red O e n (tjcosets_iso n O h) ∈ stabS n j κ hj`.

Introduce `h`. Rewrite using `[mem_stabS]`. Simplify using `only [hd, tjcosets_conj_apply, tjcosets_bc_apply, Subring.coe_subtype, red_iso_apply]`. Rewrite using `[entries_iff n j ϖ hϖ hϖO hmax h]`. Simplify using `only [EmbeddingLike.map_eq_zero_iff]`.

Rewrite using `[tjcosets_mem_K_iff, hinv, key g, key g⁻¹, map_inv, map_inv]`. Conclude with `⟨fun h => h.1, fun h => ⟨h, (stabS n j κ hj).inv_mem h⟩⟩`.
-/
private theorem conj_mem_iff (n j : ℕ) (hj : j ≤ n) (ϖ : L) (hϖ : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0) (g : GL (Fin n) O) :
    (tjcosets_dG n j ϖ⁻¹ (inv_ne_zero hϖ))⁻¹ * Formalism.UG.bc O.subtype g * tjcosets_dG n j ϖ⁻¹ (inv_ne_zero hϖ) ∈
        GLint (Fin n) O ↔
      red O e n (tjcosets_iso n O g) ∈ stabS n j κ hj := by
  set d := tjcosets_dG n j ϖ⁻¹ (inv_ne_zero hϖ) with hd
  have hinv : (d⁻¹ * Formalism.UG.bc O.subtype g * d)⁻¹ = d⁻¹ * Formalism.UG.bc O.subtype g⁻¹ * d := by
    simp only [map_inv]; group
  have key : ∀ h : GL (Fin n) O,
      (∀ a b, ((d⁻¹ * Formalism.UG.bc O.subtype h * d : GL (Fin n) L) : Matrix (Fin n) (Fin n) L) a b ∈ O) ↔
        red O e n (tjcosets_iso n O h) ∈ stabS n j κ hj := by
    intro h
    rw [mem_stabS]
    simp only [hd, tjcosets_conj_apply, tjcosets_bc_apply, Subring.coe_subtype, red_iso_apply]
    rw [entries_iff n j ϖ hϖ hϖO hmax h]
    simp only [EmbeddingLike.map_eq_zero_iff]
  rw [tjcosets_mem_K_iff, hinv, key g, key g⁻¹, map_inv, map_inv]
  exact ⟨fun h => h.1, fun h => ⟨h, (stabS n j κ hj).inv_mem h⟩⟩

include e in

/- English proof (translation)
Establish `hEq : ((GLint (Fin n) O).comap (MulAut.conj t).toMonoidHom).subgroupOf (GLint (Fin n) O) = (stabS n j κ hj).comap (red O e n)`. Use extensionality with `k`. Take `⟨g, rfl⟩` from `(tjcosets_iso n O).surjective k`. Rewrite using `[Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_comap, tjcosets_iso_coe, ← conj_mem_iff e n j hj ϖ hϖ hϖO hmax g, ht]`. Simplify using `[MulAut.conj_apply]`.

Rewrite using `[Subgroup.relIndex, hEq, Subgroup.index_comap_of_surjective _ (red_surjective O e n), index_stabS]`.
-/
private theorem relIndex_eq (n j : ℕ) (hj : j ≤ n) (ϖ : L) (hϖ : ϖ ≠ 0) (hϖO : ϖ ∈ O)
    (hmax : ∀ x : O, ϖ⁻¹ * (x : L) ∈ O ↔ IsLocalRing.residue O x = 0) (t : GL (Fin n) L)
    (ht : t = (tjcosets_dG n j ϖ⁻¹ (inv_ne_zero hϖ))⁻¹) :
    ((GLint (Fin n) O).comap (MulAut.conj t).toMonoidHom).relIndex (GLint (Fin n) O) =
      Nat.card (UpperTheory.Gal.crystallineComparison.Gr κ (Fin n → κ) j) := by
  have hEq : ((GLint (Fin n) O).comap (MulAut.conj t).toMonoidHom).subgroupOf (GLint (Fin n) O) =
      (stabS n j κ hj).comap (red O e n) := by
    ext k
    obtain ⟨g, rfl⟩ := (tjcosets_iso n O).surjective k
    rw [Subgroup.mem_subgroupOf, Subgroup.mem_comap, Subgroup.mem_comap, tjcosets_iso_coe,
      ← conj_mem_iff e n j hj ϖ hϖ hϖO hmax g, ht]
    simp [MulAut.conj_apply]
  rw [Subgroup.relIndex, hEq, Subgroup.index_comap_of_surjective _ (red_surjective O e n),
    index_stabS]

end Loc

section Adic

open Formalism.UG Formalism.UG.P

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) [v.asIdeal.IsMaximal]

private def resEquiv : IsLocalRing.ResidueField (Ov F v) ≃+* (𝓞 F ⧸ v.asIdeal) := by
  let φ : 𝓞 F →+* IsLocalRing.ResidueField (v.adicCompletionIntegers F) :=
    (IsLocalRing.residue _).comp (algebraMap (𝓞 F) (v.adicCompletionIntegers F))
  have hmem : ∀ y : v.adicCompletionIntegers F, Valued.v (y : v.adicCompletion F) < 1 →
      y ∈ IsLocalRing.maximalIdeal (v.adicCompletionIntegers F) := fun y hy =>
    (Valuation.mem_maximalIdeal_iff (v := (Valued.v : Valuation (v.adicCompletion F) _))).2 hy
  have hker : ∀ r ∈ v.asIdeal, φ r = 0 := by
    intro r hr
    simp only [φ, RingHom.comp_apply, IsLocalRing.residue_eq_zero_iff]
    apply hmem
    rw [HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
      HeightOneSpectrum.adicCompletion.valued_coe (K := F) (v := v),
      HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_lt_one_iff_mem v r).2 hr
  have hsurj : Function.Surjective φ := by
    intro y
    obtain ⟨x, rfl⟩ := IsLocalRing.residue_surjective y
    obtain ⟨r, hr⟩ := glint_exists_approx v x
    refine ⟨r, ?_⟩
    simp only [φ, RingHom.comp_apply]
    show Ideal.Quotient.mk _ _ = Ideal.Quotient.mk _ _
    rw [Ideal.Quotient.eq]
    apply hmem
    have e : ((algebraMap (𝓞 F) (v.adicCompletionIntegers F) r - x : v.adicCompletionIntegers F) :
        v.adicCompletion F) = -((x : v.adicCompletion F) - algebraMap (𝓞 F) (v.adicCompletion F) r) := by
      rw [AddSubgroupClass.coe_sub, neg_sub, HeightOneSpectrum.algebraMap_adicCompletionIntegers_apply,
        IsScalarTower.algebraMap_apply (𝓞 F) F (v.adicCompletion F),
        HeightOneSpectrum.algebraMap_adicCompletion]
      rfl
    rw [e, Valuation.map_neg]
    exact hr
  let ψ := Ideal.Quotient.lift v.asIdeal φ hker
  have hs : Function.Surjective ψ := Ideal.Quotient.lift_surjective_of_surjective _ _ hsurj
  have hi : Function.Injective ψ := RingHom.injective ψ
  exact (RingEquiv.ofBijective ψ ⟨hi, hs⟩).symm

end Adic

end UpperTheory.Gal.Int.Geo.Pl.Tj.LocalIndices

open UpperTheory.Gal.Int.Geo.Pl.Tj.LocalIndices in
/- English proof (translation)
Introduce `E _ _ _ n w i hi t ht _`. Take `⟨ϖ, hϖ, htv⟩` from `ht`. Establish `hϖ0` using `Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ`. Use `relIndex_eq (O := Formalism.UG.Ov E w) (resEquiv w) n i hi ϖ hϖ0 (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) (Formalism.UG.P.tjcosets_hmax w ϖ hϖ) t ?_` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Rewrite using `[htv]`. Use `show _ = Formalism.UG.diagJ n ϖ⁻¹⁻¹ i`. Rewrite using `[inv_inv]`. Both sides reduce to the same expression.
-/
theorem UpperTheory.Gal.Int.Geo.Pl.Tj.locIdx :
    UpperTheory.Gal.Int.Geo.Pl.Tj.LocIdx := by
  intro E _ _ _ n w i hi t ht _
  obtain ⟨ϖ, hϖ, htv⟩ := ht
  have hϖ0 := Formalism.UG.P.tjcosets_ne_zero w ϖ hϖ
  refine relIndex_eq (O := Formalism.UG.Ov E w) (resEquiv w) n i hi ϖ hϖ0
    (GlobalTheory.LFun.mem_Ov_of_isUnifV hϖ) (Formalism.UG.P.tjcosets_hmax w ϖ hϖ) t ?_
  apply Units.ext
  rw [htv]
  show _ = Formalism.UG.diagJ n ϖ⁻¹⁻¹ i
  rw [inv_inv]
  rfl
