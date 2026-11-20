import Mathlib
import GroundTheory.AutomorphicForms.Reduction
open NumberField MeasureTheory Matrix
open scoped NumberField.AdeleRing Pointwise
open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Global GroundTheory.Global.IdeleGroup

noncomputable section

namespace GlobalTheory.SiegelDiagNormOne

/- English proof (translation)
Introduce `K _ _ n`. Take `⟨t₀, ht₀, hred⟩` from `exists_reduced (K := K)`. Take `⟨D, hD, hDmem⟩` from `exists_isCompact_add_mem (K := K)`. Take `⟨S, hS, hS1, hSmem⟩` from `exists_isCompact_normOneSubgroup K`. Use `set d : ℕ := Module.finrank ℚ K with hd`.

Establish `hd0 : 0 < d` using `Module.finrank_pos`. Use `set FN : Set (AdelicGLn.AdelicGL K n) := unitriangularGL n '' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D) with hFN`. Use `set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi Set.univ fun _ => S) with hFT`. Establish `hFNc : IsCompact FN` using `(isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image (continuous_unitriangularGL n)`. Establish `hFTc : IsCompact FT` using `(isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)`.

Use `⟨FN * FT, hFNc.mul hFTc, ?_, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩`. Conclude with `mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)`. Introduce and unpack `_ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, he, rfl⟩, rfl⟩ i`. Use `⟨e i, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]`. Express the relevant statement in the definitionally equal form `unitriangular p i i * _ = _`. Simplify using `[unitriangular]`. Establish `h1` using `hS1 (he i (Set.mem_univ _))`. Rewrite `h1` using `[normOneSubgroup, SetLike.mem_coe, MonoidHom.mem_ker]`.

Rewrite using `[h1]`. Both sides reduce to the same expression. Take `⟨γ, b, hb, k, hk, hγ, hratio⟩` from `hred n g`. Use `set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB`. Use `set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit with hdU`.

Establish `hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i` using `fun i => IsUnit.unit_spec _`. Use `set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr`. Establish `hrpos : ∀ i, 0 < r i` using `fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _`. Establish `hrd : ∀ i, r i ^ d = ideleModule K (dU i)` using `fun i => Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'`. Establish `heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i))` using `fun i => Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])`.

Establish `hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K` using `fun i => by`. Rewrite using `[normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]`. Use `choose c hc using fun i => hSmem _ (hnorm i)`. Use `set σ : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ`. Use `set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he`.

Use `set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA`. Establish `hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA` using `diagonal_diagUnits n c`. Use `set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu`. Establish `hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j = (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K])`. Introduce `i j`.

Rewrite using `[hu, ← map_inv, ← map_inv]`. Simplify using `only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]`. Both sides reduce to the same expression. Establish `huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K])`. Use `⟨fun i j hij => ?_, fun i => ?_⟩` and prove the remaining obligations.

Rewrite using `[hu_apply, show B i j = 0 from hb hij]`. Simplify using the standard rewrite rules. Rewrite using `[hu_apply, ← hdUv i]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨ν, hν, hνD⟩` from `exists_unitriangular_mul_mem hDmem n _ huu`.

Use `set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL`. Use `set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA`. Establish `hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K])` using `rfl`. Take `⟨d₀, hd₀⟩ : D.Nonempty` from `let ⟨k₀, hk₀⟩ := hDmem 0`. Use the proof step `⟨_, hk₀⟩`.

Use `set p : Fin n → Fin n → 𝔸[K] := fun i j => if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀ with hp`. Establish `hpD : p ∈ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D`. Introduce `i _ j _`. Simplify using `only [hp]`. Use `split_ifs with hij`.

Rewrite using `[Units.val_mul, hνAmat]`. Conclude with `hνD i j hij`. Conclude with `hd₀`. Establish `hνu : νA * u = unitriangularGL n p`. Use `Units.ext ?_` and prove the remaining obligations.

Establish `h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K])`. Rewrite using `[Units.val_mul, hνAmat]`. Conclude with `IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij], fun i => by simp [hν.2 i]⟩ huu`. Rewrite using `[h1.eq_unitriangular]`. Express the relevant statement in the definitionally equal form `unitriangular _ = unitriangular p`.

Use extensionality with `i j`. Simplify using `only [unitriangular, of_apply, hp]`. Apply the tactic sequence `split_ifs <;> rfl`. Establish `hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i))`. Rewrite using `[hδA, ← map_mul, ← map_mul]`.

Use `congr 1`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.mul_apply, hσ, he]`. Use `group`. Use `⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ, ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩, diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩` and prove the remaining obligations.

Establish `h` using `hratio i j hij`. Rewrite `h` using `[← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j]`. Establish `hrj` using `(hrpos j).le`. Establish `hri` using `(hrpos i).le`. Establish `ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀` using `Real.rpow_inv_natCast_pow ht₀.le hd0.ne'`.

Establish `htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹)` using `(Real.rpow_pos_of_pos ht₀ _).le`. Rewrite using `[← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]`. Conclude with `h`. Establish `h1 : δA * b = u * (δA * diagUnits n dU)`. Rewrite using `[hu]`.

Use `group`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, map_mul, hδ, ← hνA]`. Simplify using `only [mul_assoc]`. Use `_ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]`.

Use `_ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]`. Use `_ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by`. Rewrite using `[hdiag]`. Simplify using `only [mul_assoc]`. Use `_ = _ := by rw [hνu]`.
-/
theorem exists_siegelSet_diag_normOne : ∀ (K : Type) [Field K] [NumberField K] (n : ℕ), ∃ ω : Set (AdelicGLn.AdelicGL K n),
    IsCompact ω ∧ ω ⊆ ((adelicBorel (K := K) (n := n) : Subgroup (AdelicGLn.AdelicGL K n)) : Set (AdelicGLn.AdelicGL K n)) ∧
    (∀ b ∈ ω, ∀ i, ∃ u : IdeleGroup K, (b : Matrix (Fin n) (Fin n) 𝔸[K]) i i = u ∧ (ideleModule K u : ℝ) = 1) ∧
    ∃ t : ℝ, 0 < t ∧ ∀ g : AdelicGLn.AdelicGL K n, ∃ γ : GL (Fin n) K,
      AdelicGLn.diagonal K n γ * g ∈ Reduction.siegelSet n ω t := by
  intro K _ _ n
  classical
  obtain ⟨t₀, ht₀, hred⟩ := exists_reduced (K := K)
  obtain ⟨D, hD, hDmem⟩ := exists_isCompact_add_mem (K := K)
  obtain ⟨S, hS, hS1, hSmem⟩ := exists_isCompact_normOneSubgroup K
  set d : ℕ := Module.finrank ℚ K with hd
  have hd0 : 0 < d := Module.finrank_pos
  set FN : Set (AdelicGLn.AdelicGL K n) :=
    unitriangularGL n '' (Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D) with hFN
  set FT : Set (AdelicGLn.AdelicGL K n) := diagUnits n '' (Set.pi Set.univ fun _ => S) with hFT
  have hFNc : IsCompact FN := (isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => hD).image
    (continuous_unitriangularGL n)
  have hFTc : IsCompact FT := (isCompact_univ_pi fun _ => hS).image (continuous_diagUnits n)
  refine ⟨FN * FT, hFNc.mul hFTc, ?_, ?_, t₀ ^ ((d : ℝ)⁻¹), Real.rpow_pos_of_pos ht₀ _, fun g => ?_⟩
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, -, rfl⟩, rfl⟩
    exact mul_mem (unitriangularGL_mem_adelicBorel n p) (diagUnits_mem_adelicBorel n e)
  · rintro _ ⟨x, ⟨p, -, rfl⟩, y, ⟨e, he, rfl⟩, rfl⟩ i
    refine ⟨e i, ?_, ?_⟩
    · rw [Units.val_mul, coe_diagUnits, Matrix.mul_diagonal]
      change unitriangular p i i * _ = _
      simp [unitriangular]
    · have h1 := hS1 (he i (Set.mem_univ _))
      rw [normOneSubgroup, SetLike.mem_coe, MonoidHom.mem_ker] at h1
      rw [h1]
      rfl
  obtain ⟨γ, b, hb, k, hk, hγ, hratio⟩ := hred n g
  set B : Matrix (Fin n) (Fin n) 𝔸[K] := (b : Matrix (Fin n) (Fin n) 𝔸[K]) with hB
  set dU : Fin n → IdeleGroup K := fun i => (isUnit_apply_self_of_mem_adelicBorel hb i).unit
    with hdU
  have hdUv : ∀ i, ((dU i : IdeleGroup K) : 𝔸[K]) = B i i := fun i => IsUnit.unit_spec _
  set r : Fin n → ℝ := fun i => (ideleModule K (dU i) : ℝ) ^ ((d : ℝ)⁻¹) with hr
  have hrpos : ∀ i, 0 < r i := fun i => Real.rpow_pos_of_pos (ideleModule K (dU i)).2 _
  have hrd : ∀ i, r i ^ d = ideleModule K (dU i) := fun i =>
    Real.rpow_inv_natCast_pow (ideleModule K (dU i)).2.le hd0.ne'
  have heqmod : ∀ i, ideleModule K (dU i) = ideleModule K (posIdele (r i) (hrpos i)) := fun i =>
    Subtype.ext (by rw [ideleModule_posIdele, ← hd, hrd i])
  have hnorm : ∀ i, dU i * (posIdele (r i) (hrpos i))⁻¹ ∈ normOneSubgroup K := fun i => by
    rw [normOneSubgroup, MonoidHom.mem_ker, map_mul, map_inv, heqmod i, mul_inv_cancel]
  choose c hc using fun i => hSmem _ (hnorm i)
  set σ : Fin n → IdeleGroup K :=
    fun i => IdeleGroup.diagonal K (c i) * (dU i * (posIdele (r i) (hrpos i))⁻¹) with hσ
  set e : Fin n → IdeleGroup K := fun i => IdeleGroup.diagonal K (c i) with he
  set δA : AdelicGLn.AdelicGL K n := diagUnits n e with hδA
  have hδ : AdelicGLn.diagonal K n (diagUnits n c) = δA := diagonal_diagUnits n c
  set u : AdelicGLn.AdelicGL K n := δA * b * (diagUnits n dU)⁻¹ * δA⁻¹ with hu
  have hu_apply : ∀ i j, (u : Matrix (Fin n) (Fin n) 𝔸[K]) i j =
      (e i : 𝔸[K]) * B i j * (((dU j)⁻¹ : IdeleGroup K) : 𝔸[K]) * (((e j)⁻¹ : IdeleGroup K) : 𝔸[K]) := by
    intro i j
    rw [hu, ← map_inv, ← map_inv]
    simp only [Units.val_mul, hδA, coe_diagUnits, Matrix.mul_diagonal, Matrix.diagonal_mul, Pi.inv_apply]
    rfl
  have huu : IsUnitriangular (u : Matrix (Fin n) (Fin n) 𝔸[K]) := by
    refine ⟨fun i j hij => ?_, fun i => ?_⟩
    · rw [hu_apply, show B i j = 0 from hb hij]
      simp
    · rw [hu_apply, ← hdUv i]
      calc (e i : 𝔸[K]) * (dU i : 𝔸[K]) * (((dU i)⁻¹ : IdeleGroup K) : 𝔸[K]) *
            (((e i)⁻¹ : IdeleGroup K) : 𝔸[K])
          = ((e i * dU i * (dU i)⁻¹ * (e i)⁻¹ : IdeleGroup K) : 𝔸[K]) := by simp [Units.val_mul]
        _ = 1 := by rw [mul_inv_cancel_right, mul_inv_cancel, Units.val_one]
  obtain ⟨ν, hν, hνD⟩ := exists_unitriangular_mul_mem hDmem n _ huu
  set νGL : GL (Fin n) K := GeneralLinearGroup.mkOfDetNeZero ν
    (by rw [hν.det_eq_one]; exact one_ne_zero) with hνGL
  set νA : AdelicGLn.AdelicGL K n := AdelicGLn.diagonal K n νGL with hνA
  have hνAmat : (νA : Matrix (Fin n) (Fin n) 𝔸[K]) = ν.map (algebraMap K 𝔸[K]) := rfl
  obtain ⟨d₀, hd₀⟩ : D.Nonempty := let ⟨k₀, hk₀⟩ := hDmem 0; ⟨_, hk₀⟩
  set p : Fin n → Fin n → 𝔸[K] := fun i j =>
    if i < j then ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) i j else d₀
    with hp
  have hpD : p ∈ Set.pi Set.univ fun _ => Set.pi Set.univ fun _ => D := by
    intro i _ j _
    simp only [hp]
    split_ifs with hij
    · rw [Units.val_mul, hνAmat]
      exact hνD i j hij
    · exact hd₀
  have hνu : νA * u = unitriangularGL n p := by
    refine Units.ext ?_
    have h1 : IsUnitriangular ((νA * u : AdelicGLn.AdelicGL K n) : Matrix (Fin n) (Fin n) 𝔸[K]) := by
      rw [Units.val_mul, hνAmat]
      exact IsUnitriangular.mul ⟨fun i j hij => by simp [hν.1 hij],
        fun i => by simp [hν.2 i]⟩ huu
    rw [h1.eq_unitriangular]
    change unitriangular _ = unitriangular p
    ext i j
    simp only [unitriangular, of_apply, hp]
    split_ifs <;> rfl
  have hdiag : δA * diagUnits n dU = diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) := by
    rw [hδA, ← map_mul, ← map_mul]
    congr 1
    funext i
    simp only [Pi.mul_apply, hσ, he]
    group
  refine ⟨νGL * diagUnits n c * γ, unitriangularGL n p * diagUnits n σ,
    ⟨_, ⟨p, hpD, rfl⟩, _, ⟨σ, fun i _ => hc i, rfl⟩, rfl⟩,
    diagUnits n (fun i => posIdele (r i) (hrpos i)), ⟨r, hrpos, fun i j hij => ?_, rfl⟩, k, hk, ?_⟩
  · have h := hratio i j hij
    rw [← hdUv j, ← hdUv i, adeleAbs_units, adeleAbs_units, ← hrd i, ← hrd j] at h
    have hrj := (hrpos j).le
    have hri := (hrpos i).le
    have ht : (t₀ ^ ((d : ℝ)⁻¹)) ^ d = t₀ := Real.rpow_inv_natCast_pow ht₀.le hd0.ne'
    have htn : 0 ≤ t₀ ^ ((d : ℝ)⁻¹) := (Real.rpow_pos_of_pos ht₀ _).le
    rw [← pow_le_pow_iff_left₀ (mul_nonneg htn hrj) hri hd0.ne', mul_pow, ht]
    exact h
  · have h1 : δA * b = u * (δA * diagUnits n dU) := by
      rw [hu]; group
    calc AdelicGLn.diagonal K n (νGL * diagUnits n c * γ) * g
        = νA * δA * (AdelicGLn.diagonal K n γ * g) := by
          rw [map_mul, map_mul, hδ, ← hνA]; simp only [mul_assoc]
      _ = νA * (δA * b) * k := by rw [hγ]; simp only [mul_assoc]
      _ = νA * u * (δA * diagUnits n dU) * k := by rw [h1]; simp only [mul_assoc]
      _ = (νA * u) * diagUnits n σ * diagUnits n (fun i => posIdele (r i) (hrpos i)) * k := by
          rw [hdiag]; simp only [mul_assoc]
      _ = _ := by rw [hνu]

end GlobalTheory.SiegelDiagNormOne
