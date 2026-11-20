import PositivityTheory.AutomorphicForms.PublishedInputs.CuspidalContinuity.ArchimedeanCuspidal.VerticalStrips.UnramifiedEulerProductIntegral

noncomputable section

open Matrix GroundTheory.LocalField GroundTheory.Automorphic
open GroundTheory.Automorphic.GLnLocal (integralGL mem_integralGL_iff)
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.RankinSelberg

open Ad3 Ad3.R

def lowT {F : Type} [Field F] (a d : Fˣ) (z : F) : GL (Fin 2) F :=
  ⟨!![(a : F), 0; z, (d : F)], !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)],
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring,
    by
      have ha := a.ne_zero
      have hd := d.ne_zero
      ext i j; fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring⟩

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Establish `e1 : (lowT a d z : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; z, (d : F)]` using `rfl`. Establish `e2 : ((lowT a d z)⁻¹ : GL (Fin 2) F).val = !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)]` using `rfl`. Rewrite using `[mem_integralGL_iff]`. Use `⟨fun i j => ?_, fun i j => ?_⟩` and prove the remaining obligations. Apply the tactic sequence `rw [e1] fin_cases i <;> fin_cases j`.

Conclude with `ha`. Conclude with `zero_mem _`. Conclude with `hz`. Conclude with `hd`. Apply the tactic sequence `rw [e2] fin_cases i <;> fin_cases j`.

Conclude with `ha'`. Conclude with `zero_mem _`. Conclude with `mul_mem (mul_mem (neg_mem hz) ha') hd'`. Conclude with `hd'`.
-/
theorem lowT_mem {a d : Fˣ} {z : F} (ha : (a : F) ∈ 𝒪[F]) (ha' : ((a⁻¹ : Fˣ) : F) ∈ 𝒪[F])
    (hd : (d : F) ∈ 𝒪[F]) (hd' : ((d⁻¹ : Fˣ) : F) ∈ 𝒪[F]) (hz : z ∈ 𝒪[F]) :
    lowT a d z ∈ integralGL F 2 := by
  have e1 : (lowT a d z : Matrix (Fin 2) (Fin 2) F) = !![(a : F), 0; z, (d : F)] := rfl
  have e2 : ((lowT a d z)⁻¹ : GL (Fin 2) F).val =
      !![((a⁻¹ : Fˣ) : F), 0; -z * ((a⁻¹ : Fˣ) : F) * ((d⁻¹ : Fˣ) : F), ((d⁻¹ : Fˣ) : F)] := rfl
  rw [mem_integralGL_iff]
  refine ⟨fun i j => ?_, fun i j => ?_⟩
  · rw [e1]
    fin_cases i <;> fin_cases j
    · exact ha
    · exact zero_mem _
    · exact hz
    · exact hd
  · rw [e2]
    fin_cases i <;> fin_cases j
    · exact ha'
    · exact zero_mem _
    · exact mul_mem (mul_mem (neg_mem hz) ha') hd'
    · exact hd'

/- English proof (translation)
Rewrite using `[← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero, WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers.
-/
private theorem mem_integers_iff_ord_nonneg' {x : F} (hx : x ≠ 0) : x ∈ 𝒪[F] ↔ 0 ≤ ord x := by
  rw [← normalizedValuation_le_one_iff, normalizedValuation_eq_exp_ord hx, ← WithZero.exp_zero,
    WithZero.exp_le_exp]
  omega

/- English proof (translation)
Take `⟨v, hv, rfl⟩` from `Subgroup.mem_map.mp hu`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible 𝒪[F]`. Take `⟨a, ha⟩` from `exists_sub_one_eq_mul hϖ (⟨v, hv⟩ : unitFiltration F (n - 1))`. Establish `hF : ((unitsIncl F v : Fˣ) : F) - 1 = (ϖ : F) ^ (n - 1) * (a : F)`. Rewrite using `[coe_unitsIncl]`.

Use `congrArg Subtype.val ha` as an intermediate fact. Conclude with `this` after adjusting the coercions. Establish `hϖ0 : (ϖ : F) ≠ 0`. Introduce `h`. Apply `hϖ.ne_zero` to reduce the goal to its premises.

Conclude with `Subtype.ext h`. Establish `ha0 : (a : F) ≠ 0`. Introduce `h`. Apply `h1` to reduce the goal to its premises. Rewrite using `[hF, h, mul_zero]`.

Establish `hpow : ∀ k : ℕ, ord ((ϖ : F) ^ k) = k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simp [GroundTheory.LocalField.ord]`. Consider the case `succ k ih`.

Rewrite using `[pow_succ, ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_uniformizer hϖ]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `ha' : 0 ≤ ord (a : F)` using `(mem_integers_iff_ord_nonneg' ha0).mp a.2`. Rewrite using `[hF, ord_mul (pow_ne_zero _ hϖ0) ha0, hpow]`.

Move the coercions through the operations in `[Nat.cast_sub hn]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem le_ord_sub_one {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) : (n : ℤ) - 1 ≤ ord ((u : F) - 1) := by
  obtain ⟨v, hv, rfl⟩ := Subgroup.mem_map.mp hu
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible 𝒪[F]
  obtain ⟨a, ha⟩ := exists_sub_one_eq_mul hϖ (⟨v, hv⟩ : unitFiltration F (n - 1))
  have hF : ((unitsIncl F v : Fˣ) : F) - 1 = (ϖ : F) ^ (n - 1) * (a : F) := by
    rw [coe_unitsIncl]
    have := congrArg Subtype.val ha
    exact_mod_cast this
  have hϖ0 : (ϖ : F) ≠ 0 := by
    intro h
    apply hϖ.ne_zero
    exact Subtype.ext h
  have ha0 : (a : F) ≠ 0 := by
    intro h
    apply h1
    rw [hF, h, mul_zero]
  have hpow : ∀ k : ℕ, ord ((ϖ : F) ^ k) = k := by
    intro k
    induction k with
    | zero => simp [GroundTheory.LocalField.ord]
    | succ k ih =>
      rw [pow_succ, ord_mul (pow_ne_zero _ hϖ0) hϖ0, ih, ord_uniformizer hϖ]
      push_cast
      ring
  have ha' : 0 ≤ ord (a : F) := (mem_integers_iff_ord_nonneg' ha0).mp a.2
  rw [hF, ord_mul (pow_ne_zero _ hϖ0) ha0, hpow]
  push_cast [Nat.cast_sub hn]
  linarith

/- English proof (translation)
Conclude with `(mem_integers_iff_ord_nonneg' u.ne_zero).mpr hu.ge`.
-/
theorem unit_mem_integers {u : Fˣ} (hu : ord (u : F) = 0) : (u : F) ∈ 𝒪[F] := by
  exact (mem_integers_iff_ord_nonneg' u.ne_zero).mpr hu.ge

/- English proof (translation)
Introduce and unpack `rfl`. Simplify using `[GroundTheory.LocalField.ord] at hy`.
-/
theorem ne_zero_of_ord {y : F} (hy : ord y = -1) : y ≠ 0 := by
  rintro rfl
  simp [GroundTheory.LocalField.ord] at hy

/- English proof (translation)
Establish `hy0` using `ne_zero_of_ord hy`. Establish `h0 : ((u : F) - 1) * y⁻¹ ≠ 0` using `mul_ne_zero h1 (inv_ne_zero hy0)`. Establish `hyi : ord y⁻¹ = 1`. Use `ord_units_inv (Units.mk0 y hy0)` as an intermediate fact. Simplify `this` using `[hy]`.

Establish `hz : (n : ℤ) ≤ ord (((u : F) - 1) * y⁻¹)`. Rewrite using `[ord_mul h1 (inv_ne_zero hy0), hyi]`. Combine the linear relations using `[le_ord_sub_one hn hu h1]`. Establish `hpi : ord (((unifUnit F)⁻¹ ^ n : Fˣ) : F) = -n`. Rewrite using `[← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hn0 : (0 : ℤ) ≤ n` using `by positivity`. Prove the components needed by the constructor for the conclusion. Rewrite using `[mem_integers_iff_ord_nonneg' (mul_ne_zero (Units.ne_zero _) h0), ord_mul (Units.ne_zero _) h0, hpi]`. Combine the linear equalities and inequalities to obtain the conclusion.

Rewrite using `[mem_integers_iff_ord_nonneg' h0]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem entry_mem {n : ℕ} (hn : 1 ≤ n) {u : Fˣ} (hu : u ∈ unitFiltrationUnits F (n - 1))
    (h1 : (u : F) - 1 ≠ 0) {y : F} (hy : ord y = -1) :
    (((unifUnit F)⁻¹ ^ n : Fˣ) : F) * (((u : F) - 1) * y⁻¹) ∈ 𝒪[F] ∧ ((u : F) - 1) * y⁻¹ ∈ 𝒪[F] := by
  have hy0 := ne_zero_of_ord hy
  have h0 : ((u : F) - 1) * y⁻¹ ≠ 0 := mul_ne_zero h1 (inv_ne_zero hy0)
  have hyi : ord y⁻¹ = 1 := by
    have := ord_units_inv (Units.mk0 y hy0)
    simpa [hy] using this
  have hz : (n : ℤ) ≤ ord (((u : F) - 1) * y⁻¹) := by
    rw [ord_mul h1 (inv_ne_zero hy0), hyi]
    linarith [le_ord_sub_one hn hu h1]
  have hpi : ord (((unifUnit F)⁻¹ ^ n : Fˣ) : F) = -n := by
    rw [← zpow_natCast, ord_units_zpow, ord_units_inv, ord_unifUnit]
    ring
  have hn0 : (0 : ℤ) ≤ n := by positivity
  constructor
  · rw [mem_integers_iff_ord_nonneg' (mul_ne_zero (Units.ne_zero _) h0), ord_mul (Units.ne_zero _) h0, hpi]
    linarith
  · rw [mem_integers_iff_ord_nonneg' h0]
    linarith

/- English proof (translation)
Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [lowT, Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring`.
-/
theorem lower_torus_conjugate_unipotent {u : Fˣ} {y : F} (hy : y ≠ 0) :
    lowT u 1 (((u : F) - 1) * y⁻¹) * uni2 y = uni2 y * lowT 1 u (((u : F) - 1) * y⁻¹) := by
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [lowT, Ad3.uni2, Matrix.mul_apply, Fin.sum_univ_two] <;> field_simp <;> ring

/- English proof (translation)
Unfold `Ad3.R.U2 Ad3.R.ForF`. Introduce `F _ _ _ _ _ _ ψ _ ω _ hc y hy`. Use `set n := quasiCharConductor ω with hn_def`. Establish `hn : 1 ≤ n` using `hc`. Establish `hnot : ¬ (unitFiltrationUnits F (n - 1) ≤ ω.ker)`.

Introduce `hle`. Establish `: n ≤ n - 1` using `Nat.sInf_le hle`. Use linear arithmetic over natural numbers and integers. Take `⟨u, hu, hωu⟩` from `SetLike.not_le_iff_exists.mp hnot`. Rewrite `hωu` using `[MonoidHom.mem_ker]`.

Establish `h1 : (u : F) - 1 ≠ 0`. Introduce `h`. Apply `hωu` to reduce the goal to its premises. Establish `: u = 1` using `Units.ext (sub_eq_zero.mp h)`. Rewrite using `[this, map_one]`.

Establish `hord : ord (u : F) = 0`. Take `⟨v, -, hv⟩` from `Subgroup.mem_map.mp hu`. Rewrite using `[← hv, coe_unitsIncl]`. Conclude with `ord_unit v`. Establish `hu1 : (u : F) ∈ 𝒪[F]` using `unit_mem_integers hord`.

Establish `hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F]` using `unit_mem_integers (by rw [ord_units_inv, hord, neg_zero])`. Establish `h11 : ((1 : Fˣ) : F) ∈ 𝒪[F]`. Rewrite using `[Units.val_one]`. Conclude with `one_mem _`. Establish `h12 : (((1 : Fˣ)⁻¹ : Fˣ) : F) ∈ 𝒪[F]`.

Rewrite using `[inv_one, Units.val_one]`. Conclude with `one_mem _`. Establish `he` using `entry_mem hn hu h1 hy`. Use `⟨lowT u 1 (((u : F) - 1) * y⁻¹), 1, lowT 1 u (((u : F) - 1) * y⁻¹), u, ?_, ?_, lower_torus_conjugate_unipotent (ne_zero_of_ord hy), ?_⟩` and prove the remaining obligations. Unfold `Ad3.R.GammaZeroLevelMembership`.

Conclude with `⟨lowT_mem hu1 hu2 h11 h12 he.2, he.1, rfl⟩`. Unfold `Ad3.R.GammaZeroLevelMembership`. Conclude with `⟨lowT_mem h11 h12 hu1 hu2 he.2, he.1, rfl⟩`. Rewrite using `[map_one]`. Conclude with `fun h => hωu h.symm`.
-/
theorem unipotent_conj_moves_char : Ad3.R.U2 := by
  unfold Ad3.R.U2 Ad3.R.ForF
  intro F _ _ _ _ _ _ ψ _ ω _ hc y hy
  set n := quasiCharConductor ω with hn_def
  have hn : 1 ≤ n := hc
  have hnot : ¬ (unitFiltrationUnits F (n - 1) ≤ ω.ker) := by
    intro hle
    have : n ≤ n - 1 := Nat.sInf_le hle
    omega
  obtain ⟨u, hu, hωu⟩ := SetLike.not_le_iff_exists.mp hnot
  rw [MonoidHom.mem_ker] at hωu
  have h1 : (u : F) - 1 ≠ 0 := by
    intro h
    apply hωu
    have : u = 1 := Units.ext (sub_eq_zero.mp h)
    rw [this, map_one]
  have hord : ord (u : F) = 0 := by
    obtain ⟨v, -, hv⟩ := Subgroup.mem_map.mp hu
    rw [← hv, coe_unitsIncl]
    exact ord_unit v
  have hu1 : (u : F) ∈ 𝒪[F] := unit_mem_integers hord
  have hu2 : ((u⁻¹ : Fˣ) : F) ∈ 𝒪[F] := unit_mem_integers (by rw [ord_units_inv, hord, neg_zero])
  have h11 : ((1 : Fˣ) : F) ∈ 𝒪[F] := by
    rw [Units.val_one]
    exact one_mem _
  have h12 : (((1 : Fˣ)⁻¹ : Fˣ) : F) ∈ 𝒪[F] := by
    rw [inv_one, Units.val_one]
    exact one_mem _
  have he := entry_mem hn hu h1 hy
  refine ⟨lowT u 1 (((u : F) - 1) * y⁻¹), 1, lowT 1 u (((u : F) - 1) * y⁻¹), u, ?_, ?_,
    lower_torus_conjugate_unipotent (ne_zero_of_ord hy), ?_⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem hu1 hu2 h11 h12 he.2, he.1, rfl⟩
  · unfold Ad3.R.GammaZeroLevelMembership
    exact ⟨lowT_mem h11 h12 hu1 hu2 he.2, he.1, rfl⟩
  · rw [map_one]
    exact fun h => hωu h.symm

end GlobalTheory.CompanionTheory.RankinSelberg
end
