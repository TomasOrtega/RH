import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.HodgeTateFromSandwich
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.FormsFin
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.TraceFormulaEigenvalues.TraceFibreCardinality.ResidualAutomorphyOfLinkedEnds
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.EmbAlg
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.GlobNegOne
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.IsScal
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.GlobalUnitaryForms.ScalarTuples.CommOfConj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.LocalHermitianForms.LocalOrbitCounts.FzdLaw

noncomputable section

namespace UpperTheory.V.Z.Sym.Glob

open NumberField IsDedekindDomain Matrix Loc MulAction

/- English proof (translation)
Substitute `h` using the available equality. Substitute `hk` using the available equality. Both sides reduce to the same expression.
-/
private theorem quot_sum_congr {Y : Type} (s s' : Setoid Y) (h : s = s') (k k' : Y → ℂ) (hk : k = k') :
    (∑ᶠ o : Quotient s, k o.out) = ∑ᶠ o : Quotient s', k' o.out := by
  subst h; subst hk; rfl

/- English proof (translation)
Use `letI a : MulAction H (G ⧸ U) := MulAction.compHom _ j`. Use `letI a' : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp e)`. Establish `hs : ∀ (x : H') (y : G ⧸ U), x • y = e x • y` using `fun _ _ => rfl`. Use `quot_sum_congr (orbitRel H' (G ⧸ U)) (orbitRel H (G ⧸ U)) ?_ (fun y => k y / ((H₀.comap e).relIndex (stabilizer H' y) : ℂ)) (fun y => k y / (H₀.relIndex (stabilizer H y) : ℂ)) ?_` and prove the remaining obligations. Use extensionality with `x y`.

Rewrite using `[orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨g, hg⟩`. Conclude with `⟨e g, hg⟩`. Introduce and unpack `⟨g, hg⟩`.

Take `⟨g', rfl⟩` from `he g`. Conclude with `⟨g', hg⟩`. Use function extensionality and compare the values at `y`. Establish `: stabilizer H' y = (stabilizer H y).comap e`. Use extensionality with `x`.

Simplify using `only [mem_stabilizer_iff, Subgroup.mem_comap, hs]`. Rewrite using `[this, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he]`.
-/
private theorem gqOn_surj {H' H G : Type} [Group H'] [Group H] [Group G] (e : H' →* H) (he : Function.Surjective e)
    (j : H →* G) (H₀ : Subgroup H) (U : Subgroup G) (k : G ⧸ U → ℂ) :
    gqOn (j.comp e) (H₀.comap e) U k = gqOn j H₀ U k := by
  letI a : MulAction H (G ⧸ U) := MulAction.compHom _ j
  letI a' : MulAction H' (G ⧸ U) := MulAction.compHom _ (j.comp e)
  have hs : ∀ (x : H') (y : G ⧸ U), x • y = e x • y := fun _ _ => rfl
  refine quot_sum_congr (orbitRel H' (G ⧸ U)) (orbitRel H (G ⧸ U)) ?_
    (fun y => k y / ((H₀.comap e).relIndex (stabilizer H' y) : ℂ)) (fun y => k y / (H₀.relIndex (stabilizer H y) : ℂ)) ?_
  · ext x y
    rw [orbitRel_apply, orbitRel_apply, mem_orbit_iff, mem_orbit_iff]
    constructor
    · rintro ⟨g, hg⟩
      exact ⟨e g, hg⟩
    · rintro ⟨g, hg⟩
      obtain ⟨g', rfl⟩ := he g
      exact ⟨g', hg⟩
  · funext y
    have : stabilizer H' y = (stabilizer H y).comap e := by
      ext x; simp only [mem_stabilizer_iff, Subgroup.mem_comap, hs]
    rw [this, Subgroup.relIndex_comap, Subgroup.map_comap_eq_self_of_surjective he]

section Field

variable {K : Type} [Field K] {Δ : K}

/- English proof (translation)
Establish `e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) = !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0]`. Unfold `DX`. Conclude with `Units.ext_iff`. Rewrite using `[e]`. Prove the components needed by the constructor for the conclusion.

Introduce `h`. Establish `h00` using `congrFun (congrFun h 0) 0`. Establish `h01` using `congrFun (congrFun h 0) 1`. Simplify using `[Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h00 h01`. Conclude with `⟨h00.symm, by rw [h01, neg_neg]⟩`.

Introduce and unpack `⟨h1, h2⟩`. Use extensionality with `i j : 1`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]`.
-/
private theorem mem_DX_k (g : GL (Fin 2) (Lsq K Δ)) : g ∈ DX Δ ↔
    ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 1 = star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 0) ∧
    (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 1 0 = - star ((g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) 0 1)) := by
  have e : g ∈ DX Δ ↔ (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)).map (starRingEnd _) =
      !![0, -1; 1, 0] * (g : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) * !![0, 1; -1, 0] := by
    unfold DX
    exact Units.ext_iff
  rw [e]
  constructor
  · intro h
    have h00 := congrFun (congrFun h 0) 0
    have h01 := congrFun (congrFun h 0) 1
    simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, starRingEnd_apply] at h00 h01
    exact ⟨h00.symm, by rw [h01, neg_neg]⟩
  · rintro ⟨h1, h2⟩
    ext i j : 1
    fin_cases i <;> fin_cases j <;> simp [starRingEnd_apply, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct, h1, h2]

/- English proof (translation)
Take `⟨h1, h2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1)` from `(mem_DX_k _).1 g.2`. Establish `hd : (mt g).det = algebraMap K _ (QuadraticAlgebra.norm (mt g 0 0) + QuadraticAlgebra.norm (mt g 0 1))`. Rewrite using `[Matrix.det_fin_two, h1, h2, map_add, QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_norm_eq_mul_star]`. Expand and normalize the polynomial expressions, which then agree. Use `⟨2 * (mt g 0 0).re, _, ?_, hd, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.trace_fin_two, h1]`. Apply the tactic sequence `ext <;> simp [two_mul]`. Introduce `h`. Rewrite `hd` using `[h, map_zero]`. Conclude with `(Matrix.isUnits_det_units (g : GL (Fin 2) (Lsq K Δ))).ne_zero hd`.
-/
private theorem tr_det_rat (g : DX Δ) : ∃ a b : K, (mt g).trace = algebraMap K _ a ∧ (mt g).det = algebraMap K _ b ∧ b ≠ 0 := by
  obtain ⟨h1, h2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hd : (mt g).det = algebraMap K _ (QuadraticAlgebra.norm (mt g 0 0) + QuadraticAlgebra.norm (mt g 0 1)) := by
    rw [Matrix.det_fin_two, h1, h2, map_add, QuadraticAlgebra.algebraMap_norm_eq_mul_star, QuadraticAlgebra.algebraMap_norm_eq_mul_star]
    ring
  refine ⟨2 * (mt g 0 0).re, _, ?_, hd, ?_⟩
  · rw [Matrix.trace_fin_two, h1]
    ext <;> simp [two_mul]
  · intro h
    rw [h, map_zero] at hd
    exact (Matrix.isUnits_det_units (g : GL (Fin 2) (Lsq K Δ))).ne_zero hd

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem mt_mul (a b : DX Δ) : mt (a * b) = mt a * mt b := rfl

/- English proof (translation)
The claim follows from `Subtype.ext (Units.ext h)`.
-/
private theorem mt_inj {a b : DX Δ} (h : mt a = mt b) : a = b := Subtype.ext (Units.ext h)

/- English proof (translation)
Rewrite using `[mt_mul, Matrix.trace_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
private theorem tr_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).trace = (mt g).trace := by
  rw [mt_mul, Matrix.trace_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

/- English proof (translation)
Rewrite using `[mt_mul, Matrix.det_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]`.
-/
private theorem det_conj (x g : DX Δ) : (mt (x⁻¹ * g * x)).det = (mt g).det := by
  rw [mt_mul, Matrix.det_mul_comm, ← mt_mul, ← mul_assoc, mul_inv_cancel, one_mul]

/- English proof (translation)
Unfold `ZD`. Rewrite using `[Subgroup.mem_subgroupOf, MonoidHom.mem_range]`. Use `exists_congr fun s => ?_` and prove the remaining obligations. Rewrite using `[← Units.val_inj, eq_comm]`. Establish `: ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) s : GL (Fin 2) (Lsq K Δ)) : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = algebraMap K (Lsq K Δ) s • 1`.

Use extensionality with `i j : 1`. Simplify using `[Matrix.diagonal_apply, Matrix.one_apply]`. Rewrite using `[this]`.
-/
private theorem mem_ZD (z : DX Δ) : z ∈ ZD Δ ↔ ∃ s : Kˣ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  unfold ZD
  rw [Subgroup.mem_subgroupOf, MonoidHom.mem_range]
  refine exists_congr fun s => ?_
  rw [← Units.val_inj, eq_comm]
  have : ((((GeneralLinearGroup.scalar (Fin 2)).comp (Units.map (algebraMap K (Lsq K Δ) : K →* Lsq K Δ))) s : GL (Fin 2) (Lsq K Δ)) :
      Matrix (Fin 2) (Fin 2) (Lsq K Δ)) = algebraMap K (Lsq K Δ) s • 1 := by
    ext i j : 1
    simp [Matrix.diagonal_apply, Matrix.one_apply]
  rw [this]

/- English proof (translation)
The claim follows from `(algebraMap K (Lsq K Δ)).injective`.
-/
private theorem alg_inj : Function.Injective (algebraMap K (Lsq K Δ)) := (algebraMap K (Lsq K Δ)).injective

/- English proof (translation)
Rewrite using `[hj z, hz]`. Simplify using `[QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]`.
-/
private theorem one_add {τ : K} {γ : DX Δ} {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j) {z : (Etau K τ)ˣ}
    (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) : mt (j z) = 1 + mt γ := by
  rw [hj z, hz]
  simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one]

/- English proof (translation)
Simplify using `only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem det_one_add (M : Matrix (Fin 2) (Fin 2) (Lsq K Δ)) : (1 + M).det = 1 + M.trace + M.det := by
  simp only [Matrix.det_fin_two, Matrix.trace_fin_two, Matrix.add_apply, Matrix.one_apply]
  simp
  ring

/- English proof (translation)
Rewrite using `[h, det_one_add, Matrix.trace_add, hγ.1, hγ.2, Matrix.trace_one, map_add, map_ofNat]`. Use `⟨by simp, by ring⟩` and prove the remaining obligations.
-/
private theorem tr_det_one_add {τ : K} {γ δ : DX Δ} (hγ : HasTr γ τ) (h : mt δ = 1 + mt γ) :
    (mt δ).trace = algebraMap K _ (2 + τ) ∧ (mt δ).det = algebraMap K _ (2 + τ) := by
  rw [h, det_one_add, Matrix.trace_add, hγ.1, hγ.2, Matrix.trace_one, map_add, map_ofNat]
  refine ⟨by simp, by ring⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `(mem_ZD z).1 hz`. Establish `e : mt δ' = algebraMap K (Lsq K Δ) s • mt (x⁻¹ * δ * x)`. Rewrite using `[h, mt_mul, hs, Matrix.mul_smul, Matrix.mul_one]`. Rewrite `h1'` using `[e, Matrix.trace_smul, tr_conj, h1, smul_eq_mul, ← map_mul]`. Rewrite `h2'` using `[e, Matrix.det_smul, det_conj, h2, Fintype.card_fin, ← map_pow, ← map_mul]`.

Establish `e1` using `alg_inj h1'`. Establish `e2` using `alg_inj h2'`. Establish `hs1 : (s : K) = 1`. Apply `mul_right_cancel₀ hb` to reduce the goal to its premises. Rewrite using `[one_mul]`.

Combine the equalities or inequalities in the displayed calculation. Use `⟨by rw [← e1, hs1, one_mul], mt_inj ?_⟩` and prove the remaining obligations. Rewrite using `[hs, hs1, map_one, one_smul]`. Both sides reduce to the same expression.
-/
private theorem rel_inj {a b : K} (hb : b ≠ 0) {δ δ' x z : DX Δ} (hz : z ∈ ZD Δ)
    (h1 : (mt δ).trace = algebraMap K _ a) (h2 : (mt δ).det = algebraMap K _ a)
    (h1' : (mt δ').trace = algebraMap K _ b) (h2' : (mt δ').det = algebraMap K _ b)
    (h : δ' = x⁻¹ * δ * x * z) : a = b ∧ z = 1 := by
  obtain ⟨s, hs⟩ := (mem_ZD z).1 hz
  have e : mt δ' = algebraMap K (Lsq K Δ) s • mt (x⁻¹ * δ * x) := by
    rw [h, mt_mul, hs, Matrix.mul_smul, Matrix.mul_one]
  rw [e, Matrix.trace_smul, tr_conj, h1, smul_eq_mul, ← map_mul] at h1'
  rw [e, Matrix.det_smul, det_conj, h2, Fintype.card_fin, ← map_pow, ← map_mul] at h2'
  have e1 := alg_inj h1'
  have e2 := alg_inj h2'
  have hs1 : (s : K) = 1 := by
    apply mul_right_cancel₀ hb
    rw [one_mul]
    calc (s : K) * b = s * (s * a) := by rw [e1]
      _ = b := by rw [← e2]; ring
  refine ⟨by rw [← e1, hs1, one_mul], mt_inj ?_⟩
  rw [hs, hs1, map_one, one_smul]
  rfl

/- English proof (translation)
Establish `hd : IsUnit (algebraMap K (Lsq K Δ) s • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ)))`. Rewrite using `[Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]`. Conclude with `(s.isUnit.map _).pow _`. Establish `hm : hd.unit ∈ DX Δ`. Rewrite using `[mem_DX_k, IsUnit.unit_spec]`.

Prove the components needed by the constructor for the conclusion. Apply the tactic sequence `ext <;> simp`. Simplify using the standard rewrite rules. Conclude with `⟨⟨hd.unit, hm⟩, (mem_ZD _).2 ⟨s, rfl⟩, rfl⟩`.
-/
private theorem scal_ex (s : Kˣ) : ∃ z ∈ ZD Δ, mt z = algebraMap K (Lsq K Δ) s • 1 := by
  have hd : IsUnit (algebraMap K (Lsq K Δ) s • (1 : Matrix (Fin 2) (Fin 2) (Lsq K Δ))) := by
    rw [Matrix.isUnit_iff_isUnit_det, Matrix.det_smul, Matrix.det_one, mul_one]
    exact (s.isUnit.map _).pow _
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec]
    constructor
    · ext <;> simp
    · simp
  exact ⟨⟨hd.unit, hm⟩, (mem_ZD _).2 ⟨s, rfl⟩, rfl⟩

/- English proof (translation)
Establish `ha : a ≠ 0`. Introduce and unpack `rfl`. Conclude with `mul_ne_zero hτ hb (by rw [← h]; ring)`. Establish `hs : a / (2 + τ) ≠ 0` using `div_ne_zero ha hτ`. Take `⟨z, hz, hz'⟩` from `scal_ex (Δ := Δ) (Units.mk0 _ hs)`.

Use `set r : K := (2 + τ) / a with hr`. Establish `hra : r * a = 2 + τ` using `by rw [hr]; field_simp`. Establish `hrb : r ^ 2 * b = 2 + τ`. Rewrite using `[hr, div_pow, h]`. Clear the denominators using the available nonvanishing facts.

Use `set M : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := algebraMap K (Lsq K Δ) r • mt g - 1 with hM`. Establish `hM1 : 1 + M = algebraMap K (Lsq K Δ) r • mt g` using `by rw [hM]; abel`. Establish `htr : M.trace = algebraMap K _ τ`. Rewrite using `[hM, Matrix.trace_sub, Matrix.trace_smul, h1, smul_eq_mul, ← map_mul, hra, Matrix.trace_one, map_add, map_ofNat]`. Simplify using the standard rewrite rules.

Establish `hdet : M.det = 1`. Use `det_one_add M` as an intermediate fact. Rewrite `this` using `[hM1, Matrix.det_smul, h2, Fintype.card_fin, ← map_pow, ← map_mul, hrb, htr, map_add, map_ofNat]`. Take the linear combination `-this`. Establish `hd : IsUnit M`.

Rewrite using `[Matrix.isUnit_iff_isUnit_det, hdet]`. Conclude with `isUnit_one`. Take `⟨k1, k2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1)` from `(mem_DX_k _).1 g.2`. Apply the tactic sequence `have hst : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp`. Establish `hm : hd.unit ∈ DX Δ`.

Rewrite using `[mem_DX_k, IsUnit.unit_spec, hM]`. Simplify using `only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, k1, k2, star_sub, star_mul', hst]`. Simplify using the standard rewrite rules. Use `⟨⟨hd.unit, hm⟩, ⟨hdet, htr⟩, z, hz, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `mt g = (1 + M) * mt z`.

Rewrite using `[hM1, hz', Matrix.mul_smul, Matrix.mul_one, smul_smul, ← map_mul, Units.val_mk0]`. Establish `: a / (2 + τ) * r = 1` using `by rw [hr]; field_simp`. Rewrite using `[this, map_one, one_smul]`.
-/
private theorem cover {τ a b : K} {g : DX Δ} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b)
    (hb : b ≠ 0) (hτ : 2 + τ ≠ 0) (h : a ^ 2 = (2 + τ) * b) :
    ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  have ha : a ≠ 0 := by
    rintro rfl
    exact mul_ne_zero hτ hb (by rw [← h]; ring)
  have hs : a / (2 + τ) ≠ 0 := div_ne_zero ha hτ
  obtain ⟨z, hz, hz'⟩ := scal_ex (Δ := Δ) (Units.mk0 _ hs)
  set r : K := (2 + τ) / a with hr
  have hra : r * a = 2 + τ := by rw [hr]; field_simp
  have hrb : r ^ 2 * b = 2 + τ := by
    rw [hr, div_pow, h]; field_simp
  set M : Matrix (Fin 2) (Fin 2) (Lsq K Δ) := algebraMap K (Lsq K Δ) r • mt g - 1 with hM
  have hM1 : 1 + M = algebraMap K (Lsq K Δ) r • mt g := by rw [hM]; abel
  have htr : M.trace = algebraMap K _ τ := by
    rw [hM, Matrix.trace_sub, Matrix.trace_smul, h1, smul_eq_mul, ← map_mul, hra, Matrix.trace_one, map_add, map_ofNat]
    simp
  have hdet : M.det = 1 := by
    have := det_one_add M
    rw [hM1, Matrix.det_smul, h2, Fintype.card_fin, ← map_pow, ← map_mul, hrb, htr, map_add, map_ofNat] at this
    linear_combination -this
  have hd : IsUnit M := by
    rw [Matrix.isUnit_iff_isUnit_det, hdet]
    exact isUnit_one
  obtain ⟨k1, k2⟩ : mt g 1 1 = star (mt g 0 0) ∧ mt g 1 0 = - star (mt g 0 1) := (mem_DX_k _).1 g.2
  have hst : star (algebraMap K (Lsq K Δ) r) = algebraMap K (Lsq K Δ) r := by ext <;> simp
  have hm : hd.unit ∈ DX Δ := by
    rw [mem_DX_k, IsUnit.unit_spec, hM]
    simp only [Matrix.sub_apply, Matrix.smul_apply, smul_eq_mul, k1, k2, star_sub, star_mul', hst]
    simp
  refine ⟨⟨hd.unit, hm⟩, ⟨hdet, htr⟩, z, hz, ?_⟩
  change mt g = (1 + M) * mt z
  rw [hM1, hz', Matrix.mul_smul, Matrix.mul_one, smul_smul, ← map_mul, Units.val_mk0]
  have : a / (2 + τ) * r = 1 := by rw [hr]; field_simp
  rw [this, map_one, one_smul]

/- English proof (translation)
Establish `: (1 + QuadraticAlgebra.omega : Etau K τ) * ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ = 1`. Apply the tactic sequence `ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring`. Conclude with `⟨Units.mkOfMulEqOne _ _ this, rfl⟩`.
-/
private theorem unit_ex {τ : K} (hτ : 2 + τ ≠ 0) : ∃ z : (Etau K τ)ˣ, (z : Etau K τ) = 1 + QuadraticAlgebra.omega := by
  have : (1 + QuadraticAlgebra.omega : Etau K τ) * ⟨(1 + τ) / (2 + τ), -1 / (2 + τ)⟩ = 1 := by
    ext <;> simp [QuadraticAlgebra.re_one, QuadraticAlgebra.im_one] <;> field_simp <;> ring
  exact ⟨Units.mkOfMulEqOne _ _ this, rfl⟩

/- English proof (translation)
Introduce `e` and use `h (by linear_combination (τ - 2) * e)`.
-/
private theorem two_add_ne {τ : K} (h : τ ^ 2 - 4 ≠ 0) : 2 + τ ≠ 0 := fun e => h (by linear_combination (τ - 2) * e)

/- English proof (translation)
Introduce `e`. Establish `h2 : IsIntegral O (2 : K)`. Use `(isIntegral_one (R := O) (B := K)).add (isIntegral_one (R := O) (B := K))` as an intermediate fact. Rewrite `this` using `[one_add_one_eq_two]`. Then use the resulting hypothesis. Establish `: (τ - 2) * (τ + 2) = 0` using `by linear_combination e`.

Break down `mul_eq_zero.1 this with e | e` into its components or cases. Conclude with `h (by rw [sub_eq_zero.1 e]; exact h2)`. Conclude with `h (by rw [eq_neg_of_add_eq_zero_left e]; exact h2.neg)`.
-/
private theorem reg_of_not_int {O : Type} [CommRing O] [Algebra O K] {τ : K} (h : ¬ IsIntegral O τ) : τ ^ 2 - 4 ≠ 0 := by
  intro e
  have h2 : IsIntegral O (2 : K) := by
    have := (isIntegral_one (R := O) (B := K)).add (isIntegral_one (R := O) (B := K))
    rwa [one_add_one_eq_two] at this
  have : (τ - 2) * (τ + 2) = 0 := by linear_combination e
  rcases mul_eq_zero.1 this with e | e
  · exact h (by rw [sub_eq_zero.1 e]; exact h2)
  · exact h (by rw [eq_neg_of_add_eq_zero_left e]; exact h2.neg)

/- English proof (translation)
Apply the tactic sequence `ext <;> simp [lmap]`.
-/
private theorem lmap_alg {K' : Type} [Field K'] (f : K →+* K') (a : K) :
    lmap f Δ (algebraMap K (Lsq K Δ) a) = algebraMap K' (Lsq K' (f Δ)) (f a) := by
  ext <;> simp [lmap]

/- English proof (translation)
Establish `e1 : (mt g').trace = algebraMap K' _ (f a)`. Rewrite using `[hg, ← lmap_alg, ← h1]`. Simplify using `[Matrix.trace_fin_two]`. Establish `e2 : (mt g').det = algebraMap K' _ (f b)`. Rewrite using `[hg, ← lmap_alg, ← h2]`.

Simplify using `[Matrix.det_fin_two]`. Rewrite `h` using `[tr_conj, det_conj, e1, e2, ← map_pow, ← map_mul]`. Establish `e` using `alg_inj h`. Establish `hb' : f b ≠ 0` using `(map_ne_zero f).2 hb`. Rewrite using `[map_sub, map_div₀, map_pow, map_ofNat, e]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem local_tau {K' : Type} [Field K'] (f : K →+* K') {g : DX Δ} {g' y : DX (f Δ)} (hg : mt g' = (mt g).map (lmap f Δ))
    {a b : K} (h1 : (mt g).trace = algebraMap K _ a) (h2 : (mt g).det = algebraMap K _ b) (hb : b ≠ 0) {τ : K'}
    (h : (mt (y⁻¹ * g' * y)).trace ^ 2 = algebraMap K' _ (2 + τ) * (mt (y⁻¹ * g' * y)).det) : f (a ^ 2 / b - 2) = τ := by
  have e1 : (mt g').trace = algebraMap K' _ (f a) := by
    rw [hg, ← lmap_alg, ← h1]
    simp [Matrix.trace_fin_two]
  have e2 : (mt g').det = algebraMap K' _ (f b) := by
    rw [hg, ← lmap_alg, ← h2]
    simp [Matrix.det_fin_two]
  rw [tr_conj, det_conj, e1, e2, ← map_pow, ← map_mul] at h
  have e := alg_inj h
  have hb' : f b ≠ 0 := (map_ne_zero f).2 hb
  rw [map_sub, map_div₀, map_pow, map_ofNat, e]
  field_simp
  ring

/- English proof (translation)
Take `⟨-, h2, h3⟩` from `(embAlg K Δ τ hΔ hτ γ hγ).2.1 j hj`. Establish `hδ` using `one_add hj hz`. Take `⟨t1, t2⟩` from `tr_det_one_add hγ hδ`. Establish `hc : ∀ x, x ∈ (Base.Tw.one B).Cent (j z) ↔ x ∈ j.range` using `fun x => by`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨w, hw, e⟩`. Express the relevant statement in the definitionally equal form `x⁻¹ * j z * x = j z * w at e`. Rewrite `hw` using `[hΓ]`. Establish `e' : j z = x⁻¹ * j z * x * w⁻¹` using `by rw [e, mul_inv_cancel_right]`. Establish `hw1` using `(rel_inj (two_add_ne hτ) (inv_mem hw) t1 t2 t1 t2 e').2`.

Rewrite `e'` using `[hw1, mul_one, mul_assoc, eq_inv_mul_iff_mul_eq]`. Establish `e2` using `congrArg mt e'`. Rewrite `e2` using `[mt_mul, mt_mul, hδ, mul_add, add_mul, mul_one, one_mul, add_right_inj]`. Conclude with `(h2 x).2 (mt_inj e2)`. Introduce and unpack `⟨w, rfl⟩`.

Use `⟨1, one_mem _, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(j w)⁻¹ * j z * j w = j z * 1`. Rewrite using `[← map_inv, ← map_mul, ← map_mul, mul_one, mul_right_comm, inv_mul_cancel, one_mul]`. Set `e : (Etau K τ)ˣ →* (Base.Tw.one B).Cent (j z)` to `j.codRestrict _ fun w => (hc _).2 ⟨w, rfl⟩`. Establish `he : Function.Surjective e` using `fun x => by`.

Take `⟨w, hw⟩` from `(hc x).1 x.2`. Conclude with `⟨w, Subtype.ext hw⟩`. Establish `key` using `gqOn_surj e he (B.ι.comp ((Base.Tw.one B).Cent (j z)).subtype) (B.Γ₀.subgroupOf _) B.U ((Base.Tw.one B).ker f (j z))`. Establish `k2 : (B.Γ₀.subgroupOf ((Base.Tw.one B).Cent (j z))).comap e = scalE τ`. Rewrite using `[← h3, hΓ]`.

Both sides reduce to the same expression. Rewrite `key` using `[k2]`. Unfold `Base.Tw.term`. Rewrite using `[← key]`. Both sides reduce to the same expression.
-/
private theorem term_eq [CharZero K] {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V] (B : Base (DX Δ) G V) (hΓ : B.Γ₀ = ZD Δ)
    (hΔ : Δ ≠ 0) {τ : K} (hτ : τ ^ 2 - 4 ≠ 0) {γ : DX Δ} (hγ : HasTr γ τ) {j : (Etau K τ)ˣ →* DX Δ} (hj : IsEmb τ γ j)
    {z : (Etau K τ)ˣ} (hz : (z : Etau K τ) = 1 + QuadraticAlgebra.omega) (f : G → ℂ) :
    (Base.Tw.one B).term f (j z) = LinearMap.trace ℂ V (B.W (j z)) *
      gqOn (B.ι.comp j) (scalE τ) B.U (fun y => f (y.out⁻¹ * B.ι (j z) * y.out)) := by
  obtain ⟨-, h2, h3⟩ := (embAlg K Δ τ hΔ hτ γ hγ).2.1 j hj
  have hδ := one_add hj hz
  obtain ⟨t1, t2⟩ := tr_det_one_add hγ hδ
  have hc : ∀ x, x ∈ (Base.Tw.one B).Cent (j z) ↔ x ∈ j.range := fun x => by
    constructor
    · rintro ⟨w, hw, e⟩
      change x⁻¹ * j z * x = j z * w at e
      rw [hΓ] at hw
      have e' : j z = x⁻¹ * j z * x * w⁻¹ := by rw [e, mul_inv_cancel_right]
      have hw1 := (rel_inj (two_add_ne hτ) (inv_mem hw) t1 t2 t1 t2 e').2
      rw [hw1, mul_one, mul_assoc, eq_inv_mul_iff_mul_eq] at e'
      have e2 := congrArg mt e'
      rw [mt_mul, mt_mul, hδ, mul_add, add_mul, mul_one, one_mul, add_right_inj] at e2
      exact (h2 x).2 (mt_inj e2)
    · rintro ⟨w, rfl⟩
      refine ⟨1, one_mem _, ?_⟩
      change (j w)⁻¹ * j z * j w = j z * 1
      rw [← map_inv, ← map_mul, ← map_mul, mul_one, mul_right_comm, inv_mul_cancel, one_mul]
  let e : (Etau K τ)ˣ →* (Base.Tw.one B).Cent (j z) := j.codRestrict _ fun w => (hc _).2 ⟨w, rfl⟩
  have he : Function.Surjective e := fun x => by
    obtain ⟨w, hw⟩ := (hc x).1 x.2
    exact ⟨w, Subtype.ext hw⟩
  have key := gqOn_surj e he (B.ι.comp ((Base.Tw.one B).Cent (j z)).subtype) (B.Γ₀.subgroupOf _) B.U ((Base.Tw.one B).ker f (j z))
  have k2 : (B.Γ₀.subgroupOf ((Base.Tw.one B).Cent (j z))).comap e = scalE τ := by
    rw [← h3, hΓ]
    rfl
  rw [k2] at key
  unfold Base.Tw.term
  rw [← key]
  rfl

end Field

section Global

variable {F : Type} [Field F] [NumberField F] {Δ : F} {D : Dat Δ}

/- English proof (translation)
Establish `hfin : (Function.mulSupport fun v => D.fKv t v (g.1 v)).Finite`. Use `(D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 ((rpg _ _).ae g))).subset fun w hw => ?_` and prove the remaining obligations. Assume the negation of the conclusion as `hn`. Rewrite `hn` using `[Set.mem_union, not_or, Set.mem_setOf_eq, not_not]`. Apply `hw` to reduce the goal to its premises.

Use `(fzdLaw (Ov w) (Kv w) (cv w Δ) (hD.off w hn.1) (D.χ w) (hD.chi w).1).2 1 1 (g.1 w) (by simp [IsScal]) hn.2` as an intermediate fact. Establish `hw' : w ∉ D.Sg` using `hn.1`. Rewrite `this` using `[one_mul]`. Simplify using `only [Dat.fKv, if_neg hw', this, map_one, inv_one, Units.val_one]`. Introduce `h0`.

Apply `h` to reduce the goal to its premises. Unfold `Dat.FK`. Use `finprod_eq_zero _ v ?_ hfin` and prove the remaining obligations. Simplify using `only [Dat.fKv, if_pos hv, h0]`.
-/
private theorem supp (hD : D.Ok) (t : Dat.Par F) (g : DA Δ) (h : D.FK t g ≠ 0) (v : Pl F) (hv : v ∈ D.Sg) :
    (D.S v).fK (t v) (g.1 v) ≠ 0 := by
  classical
  have hfin : (Function.mulSupport fun v => D.fKv t v (g.1 v)).Finite := by
    refine (D.Sg.finite_toSet.union (Filter.eventually_cofinite.1 ((rpg _ _).ae g))).subset fun w hw => ?_
    by_contra hn
    rw [Set.mem_union, not_or, Set.mem_setOf_eq, not_not] at hn
    apply hw
    have := (fzdLaw (Ov w) (Kv w) (cv w Δ) (hD.off w hn.1) (D.χ w) (hD.chi w).1).2 1 1 (g.1 w) (by simp [IsScal]) hn.2
    have hw' : w ∉ D.Sg := hn.1
    rw [one_mul] at this
    simp only [Dat.fKv, if_neg hw', this, map_one, inv_one, Units.val_one]
  intro h0
  apply h
  unfold Dat.FK
  refine finprod_eq_zero _ v ?_ hfin
  simp only [Dat.fKv, if_pos hv, h0]

/- English proof (translation)
Use `hD.real` as an intermediate fact. Take `⟨w⟩ : Nonempty (InfinitePlace F)` from `inferInstance`. Conclude with `⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩`.
-/
private theorem real_emb (hD : D.Ok) : Nonempty (F →+* ℝ) := by
  have := hD.real
  obtain ⟨w⟩ : Nonempty (InfinitePlace F) := inferInstance
  exact ⟨InfinitePlace.embedding_of_isReal (IsTotallyReal.isReal w)⟩

/- English proof (translation)
Take `⟨a, b, h1, h2, hb⟩` from `tr_det_rat g`. Establish `hadm : ∀ v ∈ D.Sg, Ind (D.S v).H (cv v (a ^ 2 / b - 2)) (t v)` using `fun v hv => by`. Take `⟨τ, hτ, e⟩` from `(hD.sig v hv).K_supp (t v) (ht v hv) _ (supp hD t _ h v hv)`. Establish `e' : (y⁻¹ * ι g * y).1 v = (y.1 v)⁻¹ * (ι g).1 v * y.1 v` using `rfl`. Rewrite `e` using `[e']`.

Rewrite using `[local_tau (cv v) (hι g v) h1 h2 hb e]`. Conclude with `hτ`. Establish `hreg : (a ^ 2 / b - 2) ^ 2 - 4 ≠ 0`. Take `⟨v, hv⟩` from `hD.ne`. Use `reg_of_not_int ((hD.sig v hv).reg (t v) (ht v hv) _ (hadm v hv)).2` as an intermediate fact.

Introduce `e`. Apply `this` to reduce the goal to its premises. Establish `e2` using `congrArg (cv v) e`. Rewrite `e2` using `[map_sub, map_pow, map_ofNat, map_zero]`. Then use the resulting hypothesis. Take `⟨γ, hγ, r⟩` from `cover h1 h2 hb (two_add_ne hreg) (by field_simp; ring)`.

Conclude with `⟨_, ⟨(embEx F Δ D hD _).2 γ hγ hreg, hadm⟩, γ, hγ, r⟩`.
-/
private theorem cover_glob (hD : D.Ok) {ι : DX Δ →* DA Δ} (hι : IsIotaD ι) {t : Dat.Par F} (ht : D.Cone t) (g : DX Δ) (y : DA Δ)
    (h : D.FK t (y⁻¹ * ι g * y) ≠ 0) :
    ∃ τ, D.Good t τ ∧ ∃ γ : DX Δ, HasTr γ τ ∧ ∃ z ∈ ZD Δ, mt g = (1 + mt γ) * mt z := by
  obtain ⟨a, b, h1, h2, hb⟩ := tr_det_rat g
  have hadm : ∀ v ∈ D.Sg, Ind (D.S v).H (cv v (a ^ 2 / b - 2)) (t v) := fun v hv => by
    obtain ⟨τ, hτ, e⟩ := (hD.sig v hv).K_supp (t v) (ht v hv) _ (supp hD t _ h v hv)
    have e' : (y⁻¹ * ι g * y).1 v = (y.1 v)⁻¹ * (ι g).1 v * y.1 v := rfl
    rw [e'] at e
    rw [local_tau (cv v) (hι g v) h1 h2 hb e]
    exact hτ
  have hreg : (a ^ 2 / b - 2) ^ 2 - 4 ≠ 0 := by
    obtain ⟨v, hv⟩ := hD.ne
    have := reg_of_not_int ((hD.sig v hv).reg (t v) (ht v hv) _ (hadm v hv)).2
    intro e
    apply this
    have e2 := congrArg (cv v) e
    rwa [map_sub, map_pow, map_ofNat, map_zero] at e2
  obtain ⟨γ, hγ, r⟩ := cover h1 h2 hb (two_add_ne hreg) (by field_simp; ring)
  exact ⟨_, ⟨(embEx F Δ D hD _).2 γ hγ hreg, hadm⟩, γ, hγ, r⟩

end Global

end UpperTheory.V.Z.Sym.Glob

open UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Glob in
/- English proof (translation)
Introduce `F _ _ Δ D hD`. Use `⟨∏ v ∈ D.Sg, (D.S v).cK, Finset.prod_pos fun v hv => (hD.sig v hv).cK, ?_⟩` and prove the remaining obligations. Introduce `V _ _ _ ch B hB t ht`. Take `⟨σ⟩` from `real_emb hD`. Establish `hΔ : Δ ≠ 0` using `fun e => by`.

Use `hD.neg σ` as an intermediate fact. Rewrite `this` using `[e, map_zero]`. Conclude with `lt_irrefl _ this`. Establish `hreg : ∀ i : {τ // D.Good t τ}, i.1 ^ 2 - 4 ≠ 0` using `fun i e => by`. Use `i.2.1 σ` as an intermediate fact.

Rewrite `this` using `[e, map_zero]`. Conclude with `lt_irrefl _ this`. Use `choose γ hγ using fun i : {τ // D.Good t τ} => (embEx F Δ D hD i.1).1 i.2.1`. Use `choose j hj using fun i : {τ // D.Good t τ} => (embAlg F Δ i.1 hΔ (hreg i) (γ i) (hγ i)).1`. Use `choose z hz using fun i : {τ // D.Good t τ} => unit_ex (two_add_ne (hreg i))`.

Establish `hδ` using `fun i => one_add (hj i) (hz i)`. Establish `htd` using `fun i => tr_det_one_add (hγ i) (hδ i)`. Take `⟨hfin, htest⟩` from `finK F Δ D hD V ch B hB`. Establish `hι : IsIotaD B.ι` using `hB.ι`. Establish `key` using `(Tf.trace _ _ V B hfin (Base.Tw.one B) (D.FK t) (htest t ht) {τ // D.Good t τ} (fun i => j i (z i)) ?_ ?_).2`.

Rewrite using `[key]`. Establish `e : ∀ i : {τ // D.Good t τ}, (Base.Tw.one B).term (D.FK t) (j i (z i)) = ((∏ v ∈ D.Sg, (D.S v).cK : ℝ) : ℂ) * (ch i.1 * ms i.1 * D.nK i.1)` using `fun i => by`. Rewrite using `[term_eq B hB.Γ₀ hΔ (hreg i) (hγ i) (hj i) (hz i), hB.tr _ _ (htd i).1 (htd i).2, hB.U, gqK F Δ D hD B.ι hι t ht i.1 i.2.1 (γ i) (j i) (hγ i) (hj i) (z i) (hz i)]`. Establish `: one (D.admitted t i.1) = 1` using `if_pos i.2.2`. Rewrite using `[this]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[finsum_congr e, ← mul_finsum, Dat.sumK, finsum_subtype_eq_finsum_cond (f := fun τ => ch τ * ms τ * D.nK τ) (p := D.Good t)]`. Use `congr 1`. Use `finsum_congr fun τ => ?_` and prove the remaining obligations.

Rewrite using `[finsum_eq_if, one]`. Apply the tactic sequence `split_ifs <;> simp`. Introduce and unpack `i i' ⟨x, w, hw, e⟩`. Rewrite `hw` using `[hB.Γ₀]`. Use `(rel_inj (two_add_ne (hreg i')) hw (htd i).1 (htd i).2 (htd i').1 (htd i').2 e).1` as an intermediate fact.

Conclude with `Subtype.ext (add_left_cancel this)`. Introduce and unpack `g ⟨y, hy⟩`. Take `⟨τ, hτ, γ', hγ', w, hw, e⟩` from `cover_glob hD hι ht g y.out hy`. Take `⟨x, hx⟩` from `(embAlg F Δ τ hΔ (hreg ⟨τ, hτ⟩) (γ ⟨τ, hτ⟩) (hγ ⟨τ, hτ⟩)).2.2 γ' hγ'`. Use `⟨⟨τ, hτ⟩, x, w, hB.Γ₀ ▸ hw, mt_inj ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `mt g = mt (x⁻¹ * j ⟨τ, hτ⟩ (z ⟨τ, hτ⟩) * x * w)`. Establish `hx1 : mt x⁻¹ * mt x = 1` using `by rw [← mt_mul, inv_mul_cancel]; rfl`. Rewrite using `[e, hx, mt_mul, mt_mul, mt_mul, mt_mul, mt_mul, hδ, mul_add (mt x⁻¹), add_mul _ _ (mt x), mul_one, hx1]`.
-/
theorem UpperTheory.V.Z.Sym.Glob.sideK :
    UpperTheory.V.Z.Sym.Glob.SideK := by
  classical
  intro F _ _ Δ D hD
  refine ⟨∏ v ∈ D.Sg, (D.S v).cK, Finset.prod_pos fun v hv => (hD.sig v hv).cK, ?_⟩
  intro V _ _ _ ch B hB t ht
  obtain ⟨σ⟩ := real_emb hD
  have hΔ : Δ ≠ 0 := fun e => by
    have := hD.neg σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  have hreg : ∀ i : {τ // D.Good t τ}, i.1 ^ 2 - 4 ≠ 0 := fun i e => by
    have := i.2.1 σ
    rw [e, map_zero] at this
    exact lt_irrefl _ this
  choose γ hγ using fun i : {τ // D.Good t τ} => (embEx F Δ D hD i.1).1 i.2.1
  choose j hj using fun i : {τ // D.Good t τ} => (embAlg F Δ i.1 hΔ (hreg i) (γ i) (hγ i)).1
  choose z hz using fun i : {τ // D.Good t τ} => unit_ex (two_add_ne (hreg i))
  have hδ := fun i => one_add (hj i) (hz i)
  have htd := fun i => tr_det_one_add (hγ i) (hδ i)
  obtain ⟨hfin, htest⟩ := finK F Δ D hD V ch B hB
  have hι : IsIotaD B.ι := hB.ι
  have key := (Tf.trace _ _ V B hfin (Base.Tw.one B) (D.FK t) (htest t ht) {τ // D.Good t τ} (fun i => j i (z i)) ?_ ?_).2
  · rw [key]
    have e : ∀ i : {τ // D.Good t τ}, (Base.Tw.one B).term (D.FK t) (j i (z i)) =
        ((∏ v ∈ D.Sg, (D.S v).cK : ℝ) : ℂ) * (ch i.1 * ms i.1 * D.nK i.1) := fun i => by
      rw [term_eq B hB.Γ₀ hΔ (hreg i) (hγ i) (hj i) (hz i), hB.tr _ _ (htd i).1 (htd i).2, hB.U,
        gqK F Δ D hD B.ι hι t ht i.1 i.2.1 (γ i) (j i) (hγ i) (hj i) (z i) (hz i)]
      have : one (D.admitted t i.1) = 1 := if_pos i.2.2
      rw [this]
      push_cast
      ring
    rw [finsum_congr e, ← mul_finsum, Dat.sumK,
      finsum_subtype_eq_finsum_cond (f := fun τ => ch τ * ms τ * D.nK τ) (p := D.Good t)]
    congr 1
    refine finsum_congr fun τ => ?_
    rw [finsum_eq_if, one]
    split_ifs <;> simp
  · rintro i i' ⟨x, w, hw, e⟩
    rw [hB.Γ₀] at hw
    have := (rel_inj (two_add_ne (hreg i')) hw (htd i).1 (htd i).2 (htd i').1 (htd i').2 e).1
    exact Subtype.ext (add_left_cancel this)
  · rintro g ⟨y, hy⟩
    obtain ⟨τ, hτ, γ', hγ', w, hw, e⟩ := cover_glob hD hι ht g y.out hy
    obtain ⟨x, hx⟩ := (embAlg F Δ τ hΔ (hreg ⟨τ, hτ⟩) (γ ⟨τ, hτ⟩) (hγ ⟨τ, hτ⟩)).2.2 γ' hγ'
    refine ⟨⟨τ, hτ⟩, x, w, hB.Γ₀ ▸ hw, mt_inj ?_⟩
    change mt g = mt (x⁻¹ * j ⟨τ, hτ⟩ (z ⟨τ, hτ⟩) * x * w)
    have hx1 : mt x⁻¹ * mt x = 1 := by rw [← mt_mul, inv_mul_cancel]; rfl
    rw [e, hx, mt_mul, mt_mul, mt_mul, mt_mul, mt_mul, hδ, mul_add (mt x⁻¹), add_mul _ _ (mt x), mul_one, hx1]
