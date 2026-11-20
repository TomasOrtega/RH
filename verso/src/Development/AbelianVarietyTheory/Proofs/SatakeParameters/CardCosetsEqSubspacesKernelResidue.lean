import Mathlib
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.IsIntOv
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FinrankReductionRangeAddCorank
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsLinearEquivMapEqOfFinrankEq

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.NTheta Formalism.IndefR.Datum IsDedekindDomain NumberField Matrix GlobalTheory.SplitHecke
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.SplitHecke.Cosets

open IsLocalRing

variable {O K : Type} [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K]
  [IsFractionRing O K] {p : O}

/- English proof (translation)
Establish `hm : maximalIdeal O = Ideal.span {p}` using `hp.maximalIdeal_eq`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `: ∀ i j, ∃ c, X i j = p * c`. Introduce `i j`.

Establish `h1 : residue O (X i j) = 0` using `congrFun (congrFun h i) j`. Rewrite `h1` using `[residue_eq_zero_iff, hm, Ideal.mem_span_singleton]`. Conclude with `h1`. Use `choose C hC using this`. Conclude with `⟨Matrix.of C, Matrix.ext hC⟩`.

Introduce and unpack `⟨C, rfl⟩`. Use extensionality with `i j`. Establish `: residue O (p * C i j) = 0`. Rewrite using `[residue_eq_zero_iff, hm, Ideal.mem_span_singleton]`. Conclude with `dvd_mul_right _ _`.

Conclude with `this`.
-/
theorem map_res_eq_zero_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    X.map (residue O) = 0 ↔ ∃ C : Matrix (Fin m) (Fin n) O, X = p • C := by
  have hm : maximalIdeal O = Ideal.span {p} := hp.maximalIdeal_eq
  constructor
  · intro h
    have : ∀ i j, ∃ c, X i j = p * c := by
      intro i j
      have h1 : residue O (X i j) = 0 := congrFun (congrFun h i) j
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton] at h1
      exact h1
    choose C hC using this
    exact ⟨Matrix.of C, Matrix.ext hC⟩
  · rintro ⟨C, rfl⟩
    ext i j
    have : residue O (p * C i j) = 0 := by
      rw [residue_eq_zero_iff, hm, Ideal.mem_span_singleton]
      exact dvd_mul_right _ _
    exact this

/- English proof (translation)
Use extensionality with `i j`. Conclude with `IsFractionRing.injective O K (congrFun (congrFun h i) j)`.
-/
theorem map_inj {m n : ℕ} {X Y : Matrix (Fin m) (Fin n) O}
    (h : X.map (algebraMap O K) = Y.map (algebraMap O K)) : X = Y := by
  ext i j
  exact IsFractionRing.injective O K (congrFun (congrFun h i) j)

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
theorem map_smul' {m n : ℕ} (c : O) (X : Matrix (Fin m) (Fin n) O) :
    (c • X).map (algebraMap O K) = algebraMap O K c • X.map (algebraMap O K) := by
  ext i j
  simp

/- English proof (translation)
Establish `h0 : algebraMap O K p ≠ 0`. Introduce `h`. Conclude with `hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))`. Rewrite using `[map_res_eq_zero_iff hp, intM_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨C, hC⟩`. Use `⟨C, map_inj (K := K) ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]`. Introduce and unpack `⟨C, rfl⟩`. Use `⟨C, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]`.
-/
theorem intM_inv_smul_iff (hp : Irreducible p) {m n : ℕ} (X : Matrix (Fin m) (Fin n) O) :
    IntM O ((algebraMap O K p)⁻¹ • X.map (algebraMap O K)) ↔ X.map (residue O) = 0 := by
  have h0 : algebraMap O K p ≠ 0 := by
    intro h
    exact hp.ne_zero (IsFractionRing.injective O K (by rw [h, map_zero]))
  rw [map_res_eq_zero_iff hp, intM_iff]
  constructor
  · rintro ⟨C, hC⟩
    refine ⟨C, map_inj (K := K) ?_⟩
    rw [map_smul', hC, smul_smul, mul_inv_cancel₀ h0, one_smul]
  · rintro ⟨C, rfl⟩
    refine ⟨C, ?_⟩
    rw [map_smul', smul_smul, inv_mul_cancel₀ h0, one_smul]

/- English proof (translation)
Establish `h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) = (A'.map (residue O)) *ᵥ Pi.single j 1`. Introduce `j`. Take `⟨y, hy⟩` from `h ⟨Pi.single j 1, rfl⟩`. Use `choose b hb using fun i => residue_surjective (R := O) (y i)`. Use `⟨b, ?_⟩` and prove the remaining obligations.

Establish `: (fun i => residue O (b i)) = y` using `funext hb`. Rewrite using `[this]`. Conclude with `hy`. Use `choose b hb using h1`. Take `⟨C, hC⟩` from `(map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by`.

Use extensionality with `i j`. Use `congrFun (hb j) i` as an intermediate fact. Rewrite `this` using `[Matrix.mulVec_single_one]`. Simplify using `only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this`. Simplify using `[Matrix.mul_apply, ← this])`.

Conclude with `⟨_, C, by rw [← hC]; abel⟩`.
-/
theorem exists_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O}
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    ∃ B C : Matrix (Fin n) (Fin n) O, A' = A * B + p • C := by
  have h1 : ∀ j, ∃ b : Fin n → O, (A.map (residue O)) *ᵥ (fun i => residue O (b i)) =
      (A'.map (residue O)) *ᵥ Pi.single j 1 := by
    intro j
    obtain ⟨y, hy⟩ := h ⟨Pi.single j 1, rfl⟩
    choose b hb using fun i => residue_surjective (R := O) (y i)
    refine ⟨b, ?_⟩
    have : (fun i => residue O (b i)) = y := funext hb
    rw [this]
    exact hy
  choose b hb using h1
  obtain ⟨C, hC⟩ := (map_res_eq_zero_iff hp (A' - A * Matrix.of fun i j => b j i)).1 (by
    ext i j
    have := congrFun (hb j) i
    rw [Matrix.mulVec_single_one] at this
    simp only [Matrix.mulVec, dotProduct, Matrix.map_apply, Matrix.col_apply] at this
    simp [Matrix.mul_apply, ← this])
  exact ⟨_, C, by rw [← hC]; abel⟩

/- English proof (translation)
Take `⟨B, hB⟩` from `intM_iff.1 h`. Establish `: A' = A * B`. Use `map_inj (K := K) ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]`. Rewrite using `[this, Matrix.map_mul, Matrix.mulVecLin_mul]`.

Conclude with `LinearMap.range_comp_le_range _ _`.
-/
theorem range_le_of_mul {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1) (h : IntM O (a⁻¹ * a').1) :
    LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin := by
  obtain ⟨B, hB⟩ := intM_iff.1 h
  have : A' = A * B := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hA', hB, ← Units.val_mul, mul_inv_cancel_left]
  rw [this, Matrix.map_mul, Matrix.mulVecLin_mul]
  exact LinearMap.range_comp_le_range _ _

/- English proof (translation)
Take `⟨B, C, hBC⟩` from `exists_of_range_le hp h`. Establish `: (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K)`. Rewrite using `[Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add, ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[this]`. Conclude with `(intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))`.
-/
theorem intM_of_range_le (hp : Irreducible p) {n : ℕ} {A A' : Matrix (Fin n) (Fin n) O} {a a' : GL (Fin n) K}
    (hA : A.map (algebraMap O K) = a.1) (hA' : A'.map (algebraMap O K) = a'.1)
    (ha : IntM O (algebraMap O K p • (a⁻¹).1))
    (h : LinearMap.range (A'.map (residue O)).mulVecLin ≤ LinearMap.range (A.map (residue O)).mulVecLin) :
    IntM O (a⁻¹ * a').1 := by
  obtain ⟨B, C, hBC⟩ := exists_of_range_le hp h
  have : (a⁻¹ * a').1 = B.map (algebraMap O K) + (algebraMap O K p • (a⁻¹).1) * C.map (algebraMap O K) := by
    rw [Units.val_mul, ← hA', hBC, Matrix.map_add _ (map_add _), Matrix.map_mul, map_smul', hA, Matrix.mul_add,
      ← Matrix.mul_assoc, ← Units.val_mul, inv_mul_cancel, Units.val_one, Matrix.one_mul, Matrix.mul_smul,
      Matrix.smul_mul]
  rw [this]
  exact (intM_iff.2 ⟨B, rfl⟩).add (ha.mul (intM_iff.2 ⟨C, rfl⟩))

/- English proof (translation)
Take `⟨A, hA⟩` from `intM_iff.1 hk.1`. Take `⟨B, hB⟩` from `intM_iff.1 hk.2`. Establish `: A * B = 1`. Use `map_inj (K := K) ?_` and prove the remaining obligations. Rewrite using `[Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `hu : IsUnit A.det` using `Matrix.isUnit_det_of_right_inverse this`. Use `⟨hu.unit, ?_⟩` and prove the remaining obligations. Rewrite using `[← hA, IsUnit.unit_spec, RingHom.map_det]`. Both sides reduce to the same expression.
-/
theorem GInt.exists_det {n : ℕ} {k : GL (Fin n) K} (hk : GInt O k) : ∃ u : Oˣ, k.1.det = algebraMap O K u := by
  obtain ⟨A, hA⟩ := intM_iff.1 hk.1
  obtain ⟨B, hB⟩ := intM_iff.1 hk.2
  have : A * B = 1 := by
    refine map_inj (K := K) ?_
    rw [Matrix.map_mul, hA, hB, ← Units.val_mul, mul_inv_cancel, Units.val_one,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have hu : IsUnit A.det := Matrix.isUnit_det_of_right_inverse this
  refine ⟨hu.unit, ?_⟩
  rw [← hA, IsUnit.unit_spec, RingHom.map_det]
  rfl

/- English proof (translation)
Use `⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩` and prove the remaining obligations. Use `(h₂.2.mul hα.2.1).mul h₁.2` as an intermediate fact. Rewrite using `[_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]`. Rewrite `this` using `[Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc]`. Then use the resulting hypothesis. Take `⟨u, hu⟩` from `hα.2.2`.

Take `⟨u₁, hu₁⟩` from `GInt.exists_det h₁`. Take `⟨u₂, hu₂⟩` from `GInt.exists_det h₂`. Use `⟨u₁ * u * u₂, ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]`. Use `congr 1`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem hk_mul {n j : ℕ} {α k₁ k₂ : GL (Fin n) K} (hα : Hk O p j α) (h₁ : GInt O k₁) (h₂ : GInt O k₂) :
    Hk O p j (k₁ * α * k₂) := by
  refine ⟨(h₁.1.mul hα.1).mul h₂.1, ?_, ?_⟩
  · have := (h₂.2.mul hα.2.1).mul h₁.2
    rw [_root_.mul_inv_rev, _root_.mul_inv_rev, Units.val_mul, Units.val_mul]
    rwa [Matrix.mul_smul, Matrix.smul_mul, Matrix.mul_assoc] at this
  · obtain ⟨u, hu⟩ := hα.2.2
    obtain ⟨u₁, hu₁⟩ := GInt.exists_det h₁
    obtain ⟨u₂, hu₂⟩ := GInt.exists_det h₂
    refine ⟨u₁ * u * u₂, ?_⟩
    rw [Units.val_mul, Units.val_mul, Matrix.det_mul, Matrix.det_mul, hu, hu₁, hu₂, ← map_mul, ← map_mul]
    congr 1
    push_cast
    ring

omit [IsDomain O] [IsDiscreteValuationRing O] [IsFractionRing O K] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩`.
-/
theorem gInt_map {n : ℕ} (g : GL (Fin n) O) : GInt O (Matrix.GeneralLinearGroup.map (algebraMap O K) g) :=
  ⟨intM_iff.2 ⟨g.1, rfl⟩, by rw [← map_inv]; exact intM_iff.2 ⟨(g⁻¹).1, rfl⟩⟩

/- English proof (translation)
Rewrite using `[← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff, ← Matrix.mulVecLin_mul, Matrix.map_mul]`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Rewrite using `[h, Matrix.mulVecLin_zero]`. Introduce `h`.

Apply `Matrix.toLin'.injective` to reduce the goal to its premises. Rewrite using `[map_zero]`. Conclude with `h`.
-/
theorem cond_iff (hp : Irreducible p) {m n : ℕ} (z : Matrix (Fin m) (Fin n) O) {A : Matrix (Fin n) (Fin n) O}
    {a : Matrix (Fin n) (Fin n) K} (hA : A.map (algebraMap O K) = a) :
    IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * a) ↔
      LinearMap.range (A.map (residue O)).mulVecLin ≤ LinearMap.ker (z.map (residue O)).mulVecLin := by
  rw [← hA, Matrix.smul_mul, ← Matrix.map_mul, intM_inv_smul_iff hp, LinearMap.range_le_ker_iff,
    ← Matrix.mulVecLin_mul, Matrix.map_mul]
  constructor
  · intro h
    rw [h, Matrix.mulVecLin_zero]
  · intro h
    apply Matrix.toLin'.injective
    rw [map_zero]
    exact h

/- English proof (translation)
Introduce `O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR`. Establish `hH : ∀ γ ∈ R, Hk O p j (ρ γ)`. Introduce `γ hγ`. Take `⟨k₁, k₂, h₁, h₂, h⟩` from `hR.1 γ hγ`. Rewrite using `[h]`.

Conclude with `hk_mul hα h₁ h₂`. Use `choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1`. Use `Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin, GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h`. Establish `h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin` using `congrArg Subtype.val h`.

Establish `hG : GInt O ((ρ γ)⁻¹ * ρ γ')`. Use `⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩` and prove the remaining obligations. Rewrite using `[_root_.mul_inv_rev, inv_inv]`. Conclude with `intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le`. Take `⟨k₁, k₂, h₁, h₂, he⟩` from `hR.1 γ' hγ'`.

Establish `hu` using `hR.2 k₁ k₂ h₁ h₂`. Rewrite `hu` using `[← he]`. Conclude with `Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)`. Introduce and unpack `⟨W, hW, hWz⟩`. Take `⟨A₀, hA₀⟩` from `intM_iff.1 hα.1`.

Establish `h0` using `GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀`. Take `⟨g, hg⟩` from `GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)`. Take `⟨γ, ⟨hγ, hG⟩, -⟩` from `hR.2 _ 1 (gInt_map g) gInt_one`. Rewrite `hG` using `[mul_one]`. Establish `hgA : (g.1 * A₀).map (algebraMap O K) = (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1`.

Rewrite using `[Matrix.map_mul, hA₀]`. Both sides reduce to the same expression. Establish `hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W`. Rewrite using `[← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]`. Use `le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)` and prove the remaining obligations.

Use `hG.2` as an intermediate fact. Rewrite `this` using `[_root_.mul_inv_rev, inv_inv]`. Then use the resulting hypothesis. Conclude with `⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩`.
-/
theorem card_cosets : ∀ (O K : Type) [CommRing O] [IsDomain O] [IsDiscreteValuationRing O] [Field K] [Algebra O K] [IsFractionRing O K] (p : O), Irreducible p → ∀ (m n j : ℕ) (ι : Type) (α : GL (Fin n) K) (R : Finset ι) (ρ : ι → GL (Fin n) K) (z : Matrix (Fin m) (Fin n) O), j ≤ n → Hk O p j α → Reps O α R ρ → Nat.card {γ : ι // γ ∈ R ∧ IntM O (((algebraMap O K p)⁻¹ • z.map (algebraMap O K)) * (ρ γ).1)} = Nat.card {W : Submodule (IsLocalRing.ResidueField O) (Fin n → IsLocalRing.ResidueField O) // Module.finrank (IsLocalRing.ResidueField O) W + j = n ∧ W ≤ LinearMap.ker (z.map (IsLocalRing.residue O)).mulVecLin} := by
  intro O K _ _ _ _ _ _ p hp m n j ι α R ρ z hj hα hR
  have hH : ∀ γ ∈ R, Hk O p j (ρ γ) := by
    intro γ hγ
    obtain ⟨k₁, k₂, h₁, h₂, h⟩ := hR.1 γ hγ
    rw [h]
    exact hk_mul hα h₁ h₂
  choose A hA using fun γ (hγ : γ ∈ R) => intM_iff.1 (hH γ hγ).1
  refine Nat.card_eq_of_bijective (fun γ => ⟨LinearMap.range ((A γ.1 γ.2.1).map (residue O)).mulVecLin,
    GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj (hH _ γ.2.1) (hA _ γ.2.1), (cond_iff hp z (hA _ γ.2.1)).1 γ.2.2⟩) ⟨?_, ?_⟩
  · rintro ⟨γ, hγ, hγ1⟩ ⟨γ', hγ', hγ2⟩ h
    have h' : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin =
        LinearMap.range ((A γ' hγ').map (residue O)).mulVecLin := congrArg Subtype.val h
    have hG : GInt O ((ρ γ)⁻¹ * ρ γ') := by
      refine ⟨intM_of_range_le hp (hA γ hγ) (hA γ' hγ') (hH γ hγ).2.1 h'.ge, ?_⟩
      rw [_root_.mul_inv_rev, inv_inv]
      exact intM_of_range_le hp (hA γ' hγ') (hA γ hγ) (hH γ' hγ').2.1 h'.le
    obtain ⟨k₁, k₂, h₁, h₂, he⟩ := hR.1 γ' hγ'
    have hu := hR.2 k₁ k₂ h₁ h₂
    rw [← he] at hu
    exact Subtype.ext (hu.unique ⟨hγ, hG⟩ ⟨hγ', by rw [inv_mul_cancel]; exact gInt_one⟩)
  · rintro ⟨W, hW, hWz⟩
    obtain ⟨A₀, hA₀⟩ := intM_iff.1 hα.1
    have h0 := GlobalTheory.SplitHecke.finrank_range_reduction O K p hp n j _ _ hj hα hA₀
    obtain ⟨g, hg⟩ := GlobalTheory.SplitHecke.exists_gl_map_residue_eq O n (LinearMap.range (A₀.map (residue O)).mulVecLin) W (by omega)
    obtain ⟨γ, ⟨hγ, hG⟩, -⟩ := hR.2 _ 1 (gInt_map g) gInt_one
    rw [mul_one] at hG
    have hgA : (g.1 * A₀).map (algebraMap O K) =
        (Matrix.GeneralLinearGroup.map (algebraMap O K) g * α).1 := by
      rw [Matrix.map_mul, hA₀]
      rfl
    have hr : LinearMap.range ((A γ hγ).map (residue O)).mulVecLin = W := by
      rw [← hg, ← LinearMap.range_comp, ← Matrix.mulVecLin_mul, ← Matrix.map_mul]
      refine le_antisymm (range_le_of_mul hgA (hA γ hγ) ?_) (range_le_of_mul (hA γ hγ) hgA hG.1)
      have := hG.2
      rwa [_root_.mul_inv_rev, inv_inv] at this
    exact ⟨⟨γ, hγ, (cond_iff hp z (hA γ hγ)).2 (hr ▸ hWz)⟩, Subtype.ext hr⟩

end GlobalTheory.SplitHecke.Cosets
