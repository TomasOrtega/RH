import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.StableIffCarrierEq
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsComp
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsLiftAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SeriesConjOfAdm
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlacesInjective
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.UnitaryConjugatorOfSplitIdempotents
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsIntegralIdempotentSplitPlaceCmFiniteAdeles
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.SplitPlaceProjectionEqZeroOfPlaceComponentEqZero
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.FiniteAdelesCmFieldEqZeroOfComponents
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HeckeDoubleCosetOperatorsStandardFacts
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.CmFieldFiniteAdeleTensorEquivMemIntegralAdeles
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ExistsRectangularConjInstanceMatrixStandardPsi
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.MemMaximalCompactOfTrivialOffSplitPair
import Development.AbelianVarietyTheory.Proofs.FlagMeasures.ResidueCmFieldFiniteAdeleTensorEquivEqNatCast
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.ConjugateMaximalCompactMemParahoricLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.UpperLeftBlockEqOneIffOfFullRank
open NumberField IsDedekindDomain ReciprocityTheory.Aut Formalism.AUTREP Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.L2 Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Rows Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Lev GlobalTheory.TypeRec GlobalTheory.TypeVec
attribute [local instance] GlobalTheory.TypeRec.factG Formalism.BasicNotions.Host.cmStar GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.RowLevConj

/- English proof (translation)
Establish `h1 : Filter.Tendsto (fun n : ℕ => (j z) ^ n) Filter.atTop (nhds 0)`. Use `(hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)` as an intermediate fact. Rewrite `this` using `[map_zero]`. Simplify `this` using `[Function.comp_def, map_pow]`. Establish `h2 : {x : v.adicCompletion K | Valued.v x < 1} ∈ nhds (0 : v.adicCompletion K)`.

Establish `: IsOpen {x : v.adicCompletion K | Valued.v x < 1}`. Simplify using `using Valued.isOpen_ball (v.adicCompletion K) 1`. Conclude with `this.mem_nhds (by simp)`. Take `⟨n, hn⟩` from `(h1.eventually h2).exists`. Rewrite `hn` using `[map_pow]`.

Assume the negation of the conclusion as `hc`. Conclude with `absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))`.
-/
theorem val_lt_one_of_cont {K : Type} [Field K] [NumberField K] (v : HeightOneSpectrum (𝓞 K)) {g : ℕ} [Fact g.Prime]
    (j : ℚ_[g] ≃+* v.adicCompletion K) (hj : Continuous j) {z : ℚ_[g]} (hz : ‖z‖ < 1) : Valued.v (j z) < 1 := by
  have h1 : Filter.Tendsto (fun n : ℕ => (j z) ^ n) Filter.atTop (nhds 0) := by
    have := (hj.tendsto 0).comp (tendsto_pow_atTop_nhds_zero_of_norm_lt_one hz)
    rw [map_zero] at this
    simpa [Function.comp_def, map_pow] using this
  have h2 : {x : v.adicCompletion K | Valued.v x < 1} ∈ nhds (0 : v.adicCompletion K) := by
    have : IsOpen {x : v.adicCompletion K | Valued.v x < 1} := by
      simpa using Valued.isOpen_ball (v.adicCompletion K) 1
    exact this.mem_nhds (by simp)
  obtain ⟨n, hn⟩ := (h1.eventually h2).exists
  rw [map_pow] at hn
  by_contra hc
  exact absurd hn (not_lt.2 (one_le_pow₀ (not_lt.1 hc)))

/- English proof (translation)
Use `⟨h.1, fun a b => ?_⟩` and prove the remaining obligations. Rewrite using `[h.2]`. Establish `hk' : PadicInt.toZMod ((y : Matrix (Fin n) (Fin n) ℤ_[g]) a b) = ((GlobalTheory.GLp.red g n y : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b`. Simplify using `[GlobalTheory.GLp.red]`. Use `set c : ℕ := (((GlobalTheory.GLp.red g n y : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc`.

Establish `hmem : (y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p` using `g)) := by`. Rewrite using `[RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]`. Rewrite `hmem` using `[PadicInt.ker_toZMod]`. Establish `hnorm : ‖(y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1` using `PadicInt.mem_nonunits.mp hmem`. Establish `he : (Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y) : Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b - (c : s.v.adicCompletion (maximalRealSubfield L)) = j (((y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g])`.

Simplify using `[GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]`. Rewrite using `[he]`. Conclude with `val_lt_one_of_cont _ j hj (by rw [PadicInt.padic_norm_e_of_padicInt]; exact hnorm)`.
-/
theorem isLift_of_isLiftAt {L : Type} [Field L] [NumberField L] [IsCMField L] {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (hj : Continuous j) (y : GL (Fin n) ℤ_[g]) (x : GAf L n)
    (h : IsLiftAt s j y x) : GlobalTheory.LabPin.IsLift s x (GlobalTheory.GLp.red g n y) := by
  refine ⟨h.1, fun a b => ?_⟩
  rw [h.2]
  have hk' : PadicInt.toZMod ((y : Matrix (Fin n) (Fin n) ℤ_[g]) a b) =
      ((GlobalTheory.GLp.red g n y : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b := by
    simp [GlobalTheory.GLp.red]
  set c : ℕ := (((GlobalTheory.GLp.red g n y : GL (Fin n) (ZMod g)) : Matrix (Fin n) (Fin n) (ZMod g)) a b).val with hc
  have hmem : (y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) ∈ RingHom.ker (PadicInt.toZMod (p := g)) := by
    rw [RingHom.mem_ker, map_sub, hk', map_natCast, hc, ZMod.natCast_zmod_val, sub_self]
  rw [PadicInt.ker_toZMod] at hmem
  have hnorm : ‖(y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g])‖ < 1 := PadicInt.mem_nonunits.mp hmem
  have he : (Matrix.GeneralLinearGroup.map j.toRingHom (GlobalTheory.GLp.inc g n y) :
      Matrix (Fin n) (Fin n) (s.v.adicCompletion (maximalRealSubfield L))) a b - (c : s.v.adicCompletion (maximalRealSubfield L)) =
      j (((y : Matrix (Fin n) (Fin n) ℤ_[g]) a b - (c : ℤ_[g]) : ℤ_[g]) : ℚ_[g]) := by
    simp [GlobalTheory.GLp.inc, Matrix.GeneralLinearGroup.map]
  rw [he]
  exact val_lt_one_of_cont _ j hj (by rw [PadicInt.padic_norm_e_of_padicInt]; exact hnorm)

/- English proof (translation)
Substitute `h` using the available equality. Use `set Z : Matrix (Fin m) (Fin m) R := ((β⁻¹).1 * U).map θ.symm with hZ`. Use `set Z' : Matrix (Fin m) (Fin m) R := (U' * β.1).map θ.symm with hZ'`. Establish `e1 : Z * Z' = 1`. Rewrite using `[hZ, hZ', ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul, Units.inv_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Establish `e2 : Z' * Z = 1` using `mul_eq_one_comm.1 e1`. Take `⟨c, hc, hcj⟩` from `GlobalTheory.unitary_conjugator_of_split_idempotents R σ hσ m m ι ε h1 h2 h3 Z 1 Z' 1 e1 e2 (by simp) (by simp)`. Use `⟨c, hc, fun j x y hy a b => ?_⟩` and prove the remaining obligations. Establish `e3 : (β⁻¹ * y * β).1 = (Z * c.1 * x.1 * ((c⁻¹).1 * Z')).map θ`. Establish `a1 : Z.map θ = (β⁻¹).1 * U`.

Rewrite using `[hZ]`. Use extensionality with `i k`. Conclude with `θ.apply_symm_apply _`. Establish `a2 : Z'.map θ = U' * β.1`. Rewrite using `[hZ']`.

Use extensionality with `i k`. Conclude with `θ.apply_symm_apply _`. Simplify using `only [Units.val_mul, hy, Matrix.map_mul, a1, a2, Matrix.mul_assoc]`. Establish `e4 : ε j • (Z * c.1 * x.1 * ((c⁻¹).1 * Z')) = ε j • x.1`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Use `_ = (ε j * ε j) • x.1 := by`. Rewrite using `[(hcj j).1, (hcj j).2]`. Simplify using `only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]`. Use `_ = ε j • x.1 := by rw [h1]`.

Rewrite using `[e3, Matrix.map_apply, ← map_mul]`. Conclude with `congrArg θ (congrFun (congrFun e4 a) b)`.
-/
theorem exists_conj {R S : Type} [CommRing R] [CommRing S] (θ : R ≃+* S) (σ : R →+* R) (hσ : ∀ a, σ (σ a) = a) {m n : ℕ} (h : m = n)
    {ι : Type} [Fintype ι] (ε : ι → R) (h1 : ∀ j, ε j * ε j = ε j) (h2 : ∀ j, ε j * σ (ε j) = 0)
    (h3 : ∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * σ (ε k) = 0) (β : GL (Fin m) S) (U : Matrix (Fin m) (Fin n) S)
    (U' : Matrix (Fin n) (Fin m) S) (hU : U * U' = 1) (hU' : U' * U = 1) :
    ∃ c : GL (Fin n) R, (c : Matrix (Fin n) (Fin n) R) * conjT σ (c : Matrix (Fin n) (Fin n) R) = 1 ∧
      ∀ (j : ι) (x : GL (Fin n) R) (y : GL (Fin m) S), y.1 = U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' →
        ∀ a b, θ (ε j) * (β⁻¹ * y * β).1 a b = θ (ε j * x.1 (Fin.cast h a) (Fin.cast h b)) := by
  subst h
  set Z : Matrix (Fin m) (Fin m) R := ((β⁻¹).1 * U).map θ.symm with hZ
  set Z' : Matrix (Fin m) (Fin m) R := (U' * β.1).map θ.symm with hZ'
  have e1 : Z * Z' = 1 := by
    rw [hZ, hZ', ← Matrix.map_mul, Matrix.mul_assoc, ← Matrix.mul_assoc U, hU, Matrix.one_mul, Units.inv_mul,
      Matrix.map_one _ (map_zero _) (map_one _)]
  have e2 : Z' * Z = 1 := mul_eq_one_comm.1 e1
  obtain ⟨c, hc, hcj⟩ := GlobalTheory.unitary_conjugator_of_split_idempotents R σ hσ m m ι ε h1 h2 h3 Z 1 Z' 1 e1 e2 (by simp) (by simp)
  refine ⟨c, hc, fun j x y hy a b => ?_⟩
  have e3 : (β⁻¹ * y * β).1 = (Z * c.1 * x.1 * ((c⁻¹).1 * Z')).map θ := by
    have a1 : Z.map θ = (β⁻¹).1 * U := by
      rw [hZ]; ext i k; exact θ.apply_symm_apply _
    have a2 : Z'.map θ = U' * β.1 := by
      rw [hZ']; ext i k; exact θ.apply_symm_apply _
    simp only [Units.val_mul, hy, Matrix.map_mul, a1, a2, Matrix.mul_assoc]
  have e4 : ε j • (Z * c.1 * x.1 * ((c⁻¹).1 * Z')) = ε j • x.1 := by
    calc ε j • (Z * c.1 * x.1 * ((c⁻¹).1 * Z')) = (ε j * ε j) • (Z * c.1 * x.1 * ((c⁻¹).1 * Z')) := by rw [h1]
      _ = (ε j • (Z * c.1)) * x.1 * (ε j • ((c⁻¹).1 * Z')) := by
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul]
      _ = (ε j * ε j) • x.1 := by
        rw [(hcj j).1, (hcj j).2]
        simp only [Matrix.smul_mul, Matrix.mul_smul, smul_smul, Matrix.one_mul, Matrix.mul_one]
      _ = ε j • x.1 := by rw [h1]
  rw [e3, Matrix.map_apply, ← map_mul]
  exact congrArg θ (congrFun (congrFun e4 a) b)

section Idem

variable {L : Type} [Field L] [NumberField L] [IsCMField L]

/- English proof (translation)
Use `choose ε a1 a2 a3 a4 a5 a6 using fun i => GlobalTheory.SplitIdem.exists_idem L (s i)`. Use `⟨ε, a1, a2, fun j k hjk => ⟨?_, ?_⟩, a3, a4, a5⟩` and prove the remaining obligations. Use `GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hv : v = (s j).v`.

Rewrite using `[(a6 k v fun h => hjk (hs (hv.symm.trans h))).1, mul_zero]`. Rewrite using `[(a6 j v hv).1, zero_mul]`. Use `GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hv : v = (s j).v`.

Rewrite using `[(a6 k v fun h => hjk (hs (hv.symm.trans h))).2, mul_zero]`. Rewrite using `[(a6 j v hv).1, zero_mul]`.
-/
theorem exists_idems {ι : Type} (s : ι → SplitPlace L) (hs : Function.Injective fun i => (s i).v) :
    ∃ ε : ι → AL L, (∀ j, ε j * ε j = ε j) ∧ (∀ j, ε j * conjAL L (ε j) = 0) ∧
      (∀ j k, j ≠ k → ε j * ε k = 0 ∧ ε j * conjAL L (ε k) = 0) ∧ (∀ j, ε j ∈ ALint L) ∧ (∀ j, (s j).proj (ε j) = 1) ∧
      ∀ j, compAt L (s j).v (ε j + conjAL L (ε j)) = 1 := by
  choose ε a1 a2 a3 a4 a5 a6 using fun i => GlobalTheory.SplitIdem.exists_idem L (s i)
  refine ⟨ε, a1, a2, fun j k hjk => ⟨?_, ?_⟩, a3, a4, a5⟩
  · refine GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_
    rw [map_mul]
    by_cases hv : v = (s j).v
    · rw [(a6 k v fun h => hjk (hs (hv.symm.trans h))).1, mul_zero]
    · rw [(a6 j v hv).1, zero_mul]
  · refine GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_
    rw [map_mul]
    by_cases hv : v = (s j).v
    · rw [(a6 k v fun h => hjk (hs (hv.symm.trans h))).2, mul_zero]
    · rw [(a6 j v hv).1, zero_mul]

/- English proof (translation)
Use `congrFun (congrFun (hx v hv) a) b` as an intermediate fact. Rewrite `this` using `[Matrix.map_apply]`. Rewrite using `[Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem compAt_sub_one {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))} {x : GA L n} (hx : TrivOutside T x)
    {v : HeightOneSpectrum (𝓞 (maximalRealSubfield L))} (hv : v ∉ T) (a b : Fin n) :
    compAt L v ((x.1.1 - 1) a b) = 0 := by
  have := congrFun (congrFun (hx v hv) a) b
  rw [Matrix.map_apply] at this
  rw [Matrix.sub_apply, map_sub, this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Use `GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Distinguish the cases in `hv : v = s.v`. Substitute `hv` using the available equality. Rewrite using `[sub_sub, map_sub, hε, map_one, sub_self, zero_mul]`.

Rewrite using `[compAt_sub_one hx hv, mul_zero]`.
-/
theorem off_mul_eq_zero {n : ℕ} (s : SplitPlace L) {ε : AL L} (hε : compAt L s.v (ε + conjAL L ε) = 1) {x : GA L n}
    (hx : TrivOutside {s.v} x) (a b : Fin n) : (1 - ε - conjAL L ε) * (x.1.1 - 1) a b = 0 := by
  refine GlobalTheory.AL_eq_zero_of_compAt L _ fun v => ?_
  rw [map_mul]
  by_cases hv : v = s.v
  · subst hv
    rw [sub_sub, map_sub, hε, map_one, sub_self, zero_mul]
  · rw [compAt_sub_one hx hv, mul_zero]

/- English proof (translation)
Use `GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ (compAt_sub_one hx h a b)` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, map_sub, sub_eq_zero]`. Rewrite using `[this, Matrix.one_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
theorem proj_off {n : ℕ} (s s' : SplitPlace L) (h : s'.v ≠ s.v) {x : GA L n} (hx : TrivOutside {s.v} x) (a b : Fin n) :
    s'.proj (x.1.1 a b) = (1 : Matrix (Fin n) (Fin n) _) a b := by
  have := GlobalTheory.SplitProj.proj_eq_zero_of_compAt_eq_zero L s' _ (compAt_sub_one hx h a b)
  rw [Matrix.sub_apply, map_sub, sub_eq_zero] at this
  rw [this, Matrix.one_apply, Matrix.one_apply]
  split_ifs <;> simp

/- English proof (translation)
Introduce `v hv` and use `by have h1 : (((x⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1 simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ …`.
-/
theorem trivOutside_inv {n : ℕ} {T : Set (HeightOneSpectrum (𝓞 (maximalRealSubfield L)))}
    {x : GA L n} (hx : TrivOutside T x) : TrivOutside T x⁻¹ := fun v hv => by
  have h1 : (((x⁻¹ : GA L n) : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) *
      ((x : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 := by simp
  have h2 := congrArg (fun M => Matrix.map M (compAt L v)) h1
  simp only [Matrix.map_mul, hx v hv, mul_one, Matrix.map_one _ (map_zero _) (map_one _)] at h2
  exact h2

/- English proof (translation)
Establish `h1 : Valued.v (((γ.1 a b).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) ≤ 1`. Simplify using `using s.split_le_one (((γ.1 a b).val : ℕ) : 𝓞 L)`. Rewrite using `[← sub_add_cancel ((s.loc n x).1 a b) (((γ.1 a b).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L))]`. Conclude with `(Valuation.map_add _ _ _).trans (max_le (h a b).le h1)`.
-/
theorem loc_le_one {g n : ℕ} (s : SplitPlace L) {x : GAf L n} {γ : GL (Fin n) (ZMod g)} (h : GlobalTheory.LabPin.RedTo s x γ) (a b : Fin n) :
    Valued.v ((s.loc n x).1 a b) ≤ 1 := by
  have h1 : Valued.v (((γ.1 a b).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L)) ≤ 1 := by
    simpa using s.split_le_one (((γ.1 a b).val : ℕ) : 𝓞 L)
  rw [← sub_add_cancel ((s.loc n x).1 a b) (((γ.1 a b).val : ℕ) : s.v.adicCompletion (maximalRealSubfield L))]
  exact (Valuation.map_add _ _ _).trans (max_le (h a b).le h1)

/- English proof (translation)
Establish `h' : IsLiftAt s j y⁻¹ x⁻¹` using `⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩`. Conclude with `GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x h.1 (loc_le_one s (isLift_of_isLiftAt s j hj y x h).2) (loc_le_one s (isLift_of_isLiftAt s j hj _ _ h').2)`.
-/
theorem mem_Umax_of_isLiftAt {g : ℕ} [Fact g.Prime] {n : ℕ} (s : SplitPlace L)
    (j : ℚ_[g] ≃+* s.v.adicCompletion (maximalRealSubfield L)) (hj : Continuous j) (y : GL (Fin n) ℤ_[g]) (x : GAf L n)
    (h : IsLiftAt s j y x) : x ∈ Umax L n := by
  have h' : IsLiftAt s j y⁻¹ x⁻¹ := ⟨trivOutside_inv h.1, by rw [map_inv, h.2, map_inv, map_inv]⟩
  exact GlobalTheory.HeckeStdFacts.mem_Umax_of_loc s x h.1 (loc_le_one s (isLift_of_isLiftAt s j hj y x h).2)
    (loc_le_one s (isLift_of_isLiftAt s j hj _ _ h').2)

end Idem

section Core

variable {D : D7}

/- English proof (translation)
The claim follows from `Formalism.L2.SG.InstExistsPf.rank_eq D`.
-/
theorem rank_zeroth_component_eq (D : D7) : (Yc D 0).rank = D.R.r := Formalism.L2.SG.InstExistsPf.rank_eq D

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hL : IsFrame (F` using `(Formalism.L2.SG.InstExistsPf.instOf D).F) β₀ (Formalism.L2.SG.InstExistsPf.instOf D).L := by`. Rewrite using `[GlobalTheory.RedFrame.Lv_eq]`. Conclude with `hβ`. Establish `e : finE (Yc D 0) k = (Formalism.IndefR.RationalEmbedding.iota D k).2.1` using `Units.ext (GlobalTheory.FixedConjMat.fmat_iota D k).symm`. Establish `hK : (Formalism.IndefR.RationalEmbedding.iota D k).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset`.

Use `GlobalTheory.SplitPairK.mem_kset_of_split (Formalism.L2.SG.InstExistsPf.instOf D) β₀ hL ε h1 h2 h3 _ ?_ ?_ ?_` and prove the remaining obligations. Rewrite `h4` using `[e]`. Conclude with `h4`. Rewrite `h5` using `[e]`. Conclude with `h5`.

Rewrite `h6` using `[e]`. Conclude with `h6`. Take `⟨s0, s1⟩` from `GlobalTheory.KapLevel.kset_stab _ hK _ e`. Conclude with `(GlobalTheory.LevSplit.mem_St_iff β₀ _ hβ _).2 ⟨s0, s1⟩`.
-/
theorem mem_St_of_split (β₀ : GL (Fin (Yc D 0).rank) (EAf D))
    (hβ : IsFrame β₀ (Formalism.L2.Herm.crdLat (Yc D 0) (Yc D 0).L0)) (ε : EAf D) (h1 : ε * ε = ε)
    (h2 : ε * Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) ε = 0) (h3 : ε ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (k : Formalism.L2.Theta.GA D (Yc D 0))
    (h4 : ∀ a b, (1 - ε - Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) ε) * ((finE (Yc D 0) k).1 - 1) a b = 0)
    (h5 : ∀ a b, ε * (β₀⁻¹ * finE (Yc D 0) k * β₀).1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E)
    (h6 : ∀ a b, ε * (β₀⁻¹ * (finE (Yc D 0) k)⁻¹ * β₀).1 a b ∈ Formalism.L2.Herm.intAf D.host.F D.host.E) :
    finE (Yc D 0) k ∈ St β₀ := by
  have hL : IsFrame (F := (Formalism.L2.SG.InstExistsPf.instOf D).F) β₀ (Formalism.L2.SG.InstExistsPf.instOf D).L := by
    rw [GlobalTheory.RedFrame.Lv_eq]; exact hβ
  have e : finE (Yc D 0) k = (Formalism.IndefR.RationalEmbedding.iota D k).2.1 := Units.ext (GlobalTheory.FixedConjMat.fmat_iota D k).symm
  have hK : (Formalism.IndefR.RationalEmbedding.iota D k).2 ∈ (Formalism.L2.SG.InstExistsPf.instOf D).Kset := by
    refine GlobalTheory.SplitPairK.mem_kset_of_split (Formalism.L2.SG.InstExistsPf.instOf D) β₀ hL ε h1 h2 h3 _ ?_ ?_ ?_
    · rw [e] at h4; exact h4
    · rw [e] at h5; exact h5
    · rw [e] at h6; exact h6
  obtain ⟨s0, s1⟩ := GlobalTheory.KapLevel.kset_stab _ hK _ e
  exact (GlobalTheory.LevSplit.mem_St_iff β₀ _ hβ _).2 ⟨s0, s1⟩

/- English proof (translation)
The claim follows from `GlobalTheory.ConjFrame.swapAE_conjAL hF a`.
-/
theorem adeleEquiv_conj (hF : D.host.F = maximalRealSubfield D.host.E) (a : AL D.host.E) :
    GlobalTheory.FixedConj.adeleEquiv D hF (conjAL D.host.E a) =
      Formalism.UG.sigR D.sp.cm.sig (Formalism.L2.Herm.Af D.host.F) (GlobalTheory.FixedConj.adeleEquiv D hF a) :=
  GlobalTheory.ConjFrame.swapAE_conjAL hF a

/- English proof (translation)
Rewrite using `[← map_one θ, ← map_sub, ← map_sub]`. Generalize the expression as in `1 - ε - ε' = e at he ⊢`. Establish `h0 : e • (x.1 - 1) = 0` using `by ext i k; exact he i k`. Establish `h1 : e • ((c * x * c⁻¹ : GL (Fin n) R).1 - 1) = 0`. Establish `: (c * x * c⁻¹ : GL (Fin n) R).1 - 1 = c.1 * (x.1 - 1) * (c⁻¹).1`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]`. Rewrite using `[this, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]`. Establish `h2 : θ e • ((c * x * c⁻¹ : GL (Fin n) R).1.map θ - 1) = 0`. Use extensionality with `i k`. Use `congrArg θ (congrFun (congrFun h1 i) k)` as an intermediate fact.

Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, map_mul, map_sub, Matrix.zero_apply, map_zero, Matrix.one_apply] at this`. Simplify using `only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.zero_apply, Matrix.map_apply, Matrix.one_apply]`. Apply the tactic sequence `split_ifs at this ⊢ <;> simpa using this`. Establish `h3 : θ e • (U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' - 1) = 0`. Establish `: U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' - 1 = U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ - 1) * U'`.

Rewrite using `[Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]`. Rewrite using `[this, ← Matrix.smul_mul, ← Matrix.mul_smul, h2, Matrix.mul_zero, Matrix.zero_mul]`. Conclude with `congrFun (congrFun h3 a) b`.
-/
theorem off_conj {R S : Type} [CommRing R] [CommRing S] (θ : R ≃+* S) {m n : ℕ} (U : Matrix (Fin m) (Fin n) S)
    (U' : Matrix (Fin n) (Fin m) S) (hU : U * U' = 1) (c x : GL (Fin n) R) (ε ε' : R) (he : ∀ a b, (1 - ε - ε') * (x.1 - 1) a b = 0)
    (a b : Fin m) :
    (1 - θ ε - θ ε') * (U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' - 1 : Matrix (Fin m) (Fin m) S) a b = 0 := by
  rw [← map_one θ, ← map_sub, ← map_sub]
  generalize 1 - ε - ε' = e at he ⊢
  have h0 : e • (x.1 - 1) = 0 := by ext i k; exact he i k
  have h1 : e • ((c * x * c⁻¹ : GL (Fin n) R).1 - 1) = 0 := by
    have : (c * x * c⁻¹ : GL (Fin n) R).1 - 1 = c.1 * (x.1 - 1) * (c⁻¹).1 := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, Units.mul_inv, Units.val_mul, Units.val_mul]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, h0, Matrix.mul_zero, Matrix.zero_mul]
  have h2 : θ e • ((c * x * c⁻¹ : GL (Fin n) R).1.map θ - 1) = 0 := by
    ext i k
    have := congrArg θ (congrFun (congrFun h1 i) k)
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, map_mul, map_sub, Matrix.zero_apply, map_zero,
      Matrix.one_apply] at this
    simp only [Matrix.smul_apply, smul_eq_mul, Matrix.sub_apply, Matrix.zero_apply, Matrix.map_apply, Matrix.one_apply]
    split_ifs at this ⊢ <;> simpa using this
  have h3 : θ e • (U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' - 1) = 0 := by
    have : U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ) * U' - 1 = U * ((c * x * c⁻¹ : GL (Fin n) R).1.map θ - 1) * U' := by
      rw [Matrix.mul_sub, Matrix.sub_mul, Matrix.mul_one, hU]
    rw [this, ← Matrix.smul_mul, ← Matrix.mul_smul, h2, Matrix.mul_zero, Matrix.zero_mul]
  exact congrFun (congrFun h3 a) b

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Take `⟨t, -, hfr⟩` from `GlobalTheory.SelfDualFrameConj.frame_conj (Yc D 0) β Λ N hβ`. Take `⟨U, U', hU, hU', hfin⟩` from `GlobalTheory.FixedConjMat.finE_conj_stdPsi D hF PY t hP`. Take `⟨ε, a1, a2, a3, a4, a5, a6⟩` from `exists_idems s hs`. Take `⟨c0, hc0, hc⟩` from `exists_conj (GlobalTheory.FixedConj.adeleEquiv D hF) (conjAL D.host.E) (conjAL_conjAL D.host.E) (rank_zeroth_component_eq D) ε a1 a2 a3 (finE (Yc D 0) t * β) U U' hU hU'`. Set `c : GAf D.host.E D.R.r` to `⟨c0, hc0⟩`.

Establish `hconj : ∀ x : GAf D.host.E D.R.r, (finE (Yc D 0) t * β)⁻¹ * finE (Yc D 0) (MulAut.conj t (PY.ψ x)) * (finE (Yc D 0) t * β) = β⁻¹ * finE (Yc D 0) (PY.ψ x) * β`. Introduce `x`. Rewrite using `[MulAut.conj_apply, map_mul, map_mul, map_inv]`. Use `group`. Establish `hent : ∀ (i : ι) (x : GAf D.host.E D.R.r) (a b : Fin (Yc D 0).rank), GlobalTheory.FixedConj.adeleEquiv D hF (ε i) * ((finE (Yc D 0) t * β)⁻¹ * finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) * (finE (Yc D 0) t * β)).1 a b = GlobalTheory.FixedConj.adeleEquiv D hF (ε i * x.1.1 ( …` using `fun i x a b => hc i x.1 _ (hfin (c * x * c⁻¹)) a b`.

Use `⟨c, fun i x hx hxU => ?_⟩` and prove the remaining obligations. Establish `hSt0 : finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) ∈ St (finE (Yc D 0) t * β)`. Use `mem_St_of_split _ hfr (GlobalTheory.FixedConj.adeleEquiv D hF (ε i)) (by rw [← map_mul, a1]) ?_ (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (a4 i)) _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)` and prove the remaining obligations. Rewrite using `[← adeleEquiv_conj, ← map_mul, a2, map_zero]`. Use `off_conj (GlobalTheory.FixedConj.adeleEquiv D hF) U U' hU c0 x.1 _ _ (off_mul_eq_zero (s i) (a6 i) hx) a b` as an intermediate fact.

Rewrite `this` using `[adeleEquiv_conj]`. Rewrite using `[hfin]`. Conclude with `this`. Rewrite using `[hent]`. Conclude with `GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i) (hxU _ _))`.

Establish `e : (finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))))⁻¹ = finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x⁻¹ * c⁻¹)))`. Rewrite using `[← map_inv, ← map_inv, ← map_inv]`. Use `congr 3`. Use `group`. Rewrite using `[e, hent]`.

Conclude with `GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i) ((Umax D.host.E D.R.r).inv_mem hxU _ _))`. Take `⟨z, hz⟩` from `hSt0`. Establish `hz1 : intGL D.host.F D.host.E _ z = (finE (Yc D 0) t * β)⁻¹ * finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) * (finE (Yc D 0) t * β)`. Rewrite using `[← hz]`. Use `show _ = (finE (Yc D 0) t * β)⁻¹ * ((finE (Yc D 0) t * β) * intGL D.host.F D.host.E _ z * (finE (Yc D 0) t * β)⁻¹) * (finE (Yc D 0) t * β)`.

Use `group`. Establish `hz2 : frGL β z = finE (Yc D 0) (PY.ψ (c * x * c⁻¹))` using `by show β * intGL D.host.F D.host.E _ z * β⁻¹ = _`. Rewrite using `[hz1, hconj]`. Use `group`. Use `⟨⟨z, hz2⟩, fun i' a b m hm => ?_⟩` and prove the remaining obligations.

Rewrite using `[← hz2, redFn_frGL]`. Use `show resS D.host.F (s i').w (z.1 a b) = _`. Establish `r1` using `GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast D hF (s i') (ε i') (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (a4 i')) 1 (a4 i') (by rw [a5]; simp)`. Establish `r2` using `GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast D hF (s i') (ε i' * x.1.1 (Fin.cast (rank_zeroth_component_eq D) a) (Fin.cast (rank_zeroth_component_eq D) b)) (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i') (hxU _ _))) m (mul_mem (a4 i') (hxU _ _)) (by rw [m …`. Rewrite using `[← r2, ← one_mul (resS D.host.F (s i').w (z.1 a b)), ← Nat.cast_one, ← r1, ← map_mul]`.

Use `congr 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `h5` using `hent i' x a b`. Rewrite `h5` using `[← hz1]`. Conclude with `h5`.
-/
theorem core (hF : D.host.F = maximalRealSubfield D.host.E) (PY : principalLevelFrame.RowPsi (Yc D 0) D.R.r) (hP : principalLevelFrame.StdPsi hF PY)
    (β : GL (Fin (Yc D 0).rank) (EAf D)) (Λ : Submodule (𝓞 D.host.E) (Fin (Yc D 0).rank → D.host.E)) (N : ℕ)
    (hβ : IsSDFrame (Yc D 0) β Λ N) {ι : Type} [Fintype ι] (s : ι → SplitPlace D.host.E)
    (hs : Function.Injective fun i => (s i).v) :
    ∃ c : GAf D.host.E D.R.r, ∀ (i : ι) (x : GAf D.host.E D.R.r), TrivOutside {(s i).v} x → x ∈ Umax D.host.E D.R.r →
      finE (Yc D 0) (PY.ψ (c * x * c⁻¹)) ∈ St β ∧
      ∀ (i' : ι) (a b : Fin (Yc D 0).rank) (m : ℕ),
        Valued.v ((s i').proj (x.1.1 (Fin.cast (rank_zeroth_component_eq D) a) (Fin.cast (rank_zeroth_component_eq D) b)) -
          (m : (s i').v.adicCompletion (maximalRealSubfield D.host.E))) < 1 →
        (redFn β (s i').w (finE (Yc D 0) (PY.ψ (c * x * c⁻¹)))).1 a b = (m : kP (s i').w) := by
  obtain ⟨t, -, hfr⟩ := GlobalTheory.SelfDualFrameConj.frame_conj (Yc D 0) β Λ N hβ
  obtain ⟨U, U', hU, hU', hfin⟩ := GlobalTheory.FixedConjMat.finE_conj_stdPsi D hF PY t hP
  obtain ⟨ε, a1, a2, a3, a4, a5, a6⟩ := exists_idems s hs
  obtain ⟨c0, hc0, hc⟩ := exists_conj (GlobalTheory.FixedConj.adeleEquiv D hF) (conjAL D.host.E) (conjAL_conjAL D.host.E) (rank_zeroth_component_eq D)
    ε a1 a2 a3 (finE (Yc D 0) t * β) U U' hU hU'
  let c : GAf D.host.E D.R.r := ⟨c0, hc0⟩
  have hconj : ∀ x : GAf D.host.E D.R.r, (finE (Yc D 0) t * β)⁻¹ * finE (Yc D 0) (MulAut.conj t (PY.ψ x)) * (finE (Yc D 0) t * β) =
      β⁻¹ * finE (Yc D 0) (PY.ψ x) * β := by
    intro x
    rw [MulAut.conj_apply, map_mul, map_mul, map_inv]
    group
  have hent : ∀ (i : ι) (x : GAf D.host.E D.R.r) (a b : Fin (Yc D 0).rank),
      GlobalTheory.FixedConj.adeleEquiv D hF (ε i) * ((finE (Yc D 0) t * β)⁻¹ *
        finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) * (finE (Yc D 0) t * β)).1 a b =
      GlobalTheory.FixedConj.adeleEquiv D hF (ε i * x.1.1 (Fin.cast (rank_zeroth_component_eq D) a) (Fin.cast (rank_zeroth_component_eq D) b)) :=
    fun i x a b => hc i x.1 _ (hfin (c * x * c⁻¹)) a b
  refine ⟨c, fun i x hx hxU => ?_⟩
  have hSt0 : finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) ∈ St (finE (Yc D 0) t * β) := by
    refine mem_St_of_split _ hfr (GlobalTheory.FixedConj.adeleEquiv D hF (ε i)) (by rw [← map_mul, a1]) ?_
      (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (a4 i)) _ (fun a b => ?_) (fun a b => ?_) (fun a b => ?_)
    · rw [← adeleEquiv_conj, ← map_mul, a2, map_zero]
    · have := off_conj (GlobalTheory.FixedConj.adeleEquiv D hF) U U' hU c0 x.1 _ _ (off_mul_eq_zero (s i) (a6 i) hx) a b
      rw [adeleEquiv_conj] at this
      rw [hfin]
      exact this
    · rw [hent]
      exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i) (hxU _ _))
    · have e : (finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))))⁻¹ =
          finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x⁻¹ * c⁻¹))) := by
        rw [← map_inv, ← map_inv, ← map_inv]
        congr 3
        group
      rw [e, hent]
      exact GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i) ((Umax D.host.E D.R.r).inv_mem hxU _ _))
  obtain ⟨z, hz⟩ := hSt0
  have hz1 : intGL D.host.F D.host.E _ z = (finE (Yc D 0) t * β)⁻¹ *
      finE (Yc D 0) (MulAut.conj t (PY.ψ (c * x * c⁻¹))) * (finE (Yc D 0) t * β) := by
    rw [← hz]
    show _ = (finE (Yc D 0) t * β)⁻¹ * ((finE (Yc D 0) t * β) * intGL D.host.F D.host.E _ z * (finE (Yc D 0) t * β)⁻¹) *
      (finE (Yc D 0) t * β)
    group
  have hz2 : frGL β z = finE (Yc D 0) (PY.ψ (c * x * c⁻¹)) := by
    show β * intGL D.host.F D.host.E _ z * β⁻¹ = _
    rw [hz1, hconj]
    group
  refine ⟨⟨z, hz2⟩, fun i' a b m hm => ?_⟩
  rw [← hz2, redFn_frGL]
  show resS D.host.F (s i').w (z.1 a b) = _
  have r1 := GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast D hF (s i') (ε i') (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (a4 i')) 1 (a4 i')
    (by rw [a5]; simp)
  have r2 := GlobalTheory.SplitRes.resS_adeleEquiv_eq_natCast D hF (s i') (ε i' * x.1.1 (Fin.cast (rank_zeroth_component_eq D) a) (Fin.cast (rank_zeroth_component_eq D) b))
    (GlobalTheory.FixedConj.adeleEquiv_mem_intAf D hF _ (mul_mem (a4 i') (hxU _ _))) m (mul_mem (a4 i') (hxU _ _))
    (by rw [map_mul, a5, one_mul]; exact hm)
  rw [← r2, ← one_mul (resS D.host.F (s i').w (z.1 a b)), ← Nat.cast_one, ← r1, ← map_mul]
  congr 1
  apply Subtype.ext
  have h5 := hent i' x a b
  rw [← hz1] at h5
  exact h5

end Core

section Main

variable {D : D7}

/- English proof (translation)
Establish `hr : rTup (L.βY 0) (L.dat0 P) (finE (Yc D 0) κ) = 1` using `h.2.2`. Use `⟨⟨h.1, h.2.1, ?_⟩, ?_⟩` and prove the remaining obligations. Use `show rTup (L.βY 0) (L.dat0 P) (finE (Yc D 0) κ) ∈ (L.dat0 P).P.H`. Rewrite using `[hr]`. Conclude with `Subgroup.one_mem _`.

Unfold `levChi levFn`. Rewrite using `[hr, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]`. Both sides reduce to the same expression. Introduce `PP hP`. Conclude with `absurd hP (Finset.notMem_empty PP)`.

Introduce `PP _`. Conclude with `Finset.prod_eq_one fun c hc => absurd hc (by show c ∉ Finset.range 0; simp)`.
-/
theorem lev_of_lift_one {T : Type} (L : LevCh D T) (P : LevelP L.Pg D.R.r ℂ) (κ : Formalism.L2.Theta.GA D (Yc D 0))
    (h : IsLevelLift (Yc D 0) (L.βY 0) (L.dat0 L.triv) 1 κ) :
    κ ∈ levS _ (L.βY 0) (L.dat0 P) ∧ levChi _ (L.βY 0) (L.dat0 P) κ = 1 := by
  have hr : rTup (L.βY 0) (L.dat0 P) (finE (Yc D 0) κ) = 1 := h.2.2
  refine ⟨⟨h.1, h.2.1, ?_⟩, ?_⟩
  · show rTup (L.βY 0) (L.dat0 P) (finE (Yc D 0) κ) ∈ (L.dat0 P).P.H
    rw [hr]; exact Subgroup.one_mem _
  · unfold levChi levFn
    rw [hr, blockDiagonalExtendByOnePrimeField_one, one_mul, Finset.prod_eq_one, Finset.prod_eq_one, one_mul]
    · rfl
    · intro PP hP
      exact absurd hP (Finset.notMem_empty PP)
    · intro PP _
      exact Finset.prod_eq_one fun c hc => absurd hc (by show c ∉ Finset.range 0; simp)

/- English proof (translation)
Proceed by induction on `hT using Submodule.span_induction with`. Consider the case `mem x hx => rw [hx.lev v κ hκ g, hχ, one_mul]`. Consider the case `zero => rfl`. Consider the case `add x y _ _ hx hy => show x v (g * κ) + y v (g * κ) = x v g + y v g`. Rewrite using `[hx, hy]`.

Consider the case `smul a x _ hx => show a • x v (g * κ) = a • x v g`. Rewrite using `[hx]`.
-/
theorem fixed_of_mem_mult {V : HSp D} {S : D.what₂.Tau → _} {θ} (M : Mult.DSModel V S) (J : Set (Formalism.L2.Theta.GA D V))
    (χ : Formalism.L2.Theta.GA D V → ℂ) {κ : Formalism.L2.Theta.GA D V} (hκ : κ ∈ J) (hχ : χ κ = 1) {Tm : Mult.MMap M}
    (hT : Tm ∈ Mult.Mult θ M J χ) (v : M.Vec) (g : Formalism.L2.Theta.GA D V) : Tm v (g * κ) = Tm v g := by
  induction hT using Submodule.span_induction with
  | mem x hx => rw [hx.lev v κ hκ g, hχ, one_mul]
  | zero => rfl
  | add x y _ _ hx hy => show x v (g * κ) + y v (g * κ) = x v g + y v g; rw [hx, hy]
  | smul a x _ hx => show a • x v (g * κ) = a • x v g; rw [hx]

set_option maxHeartbeats 3200000 in

/- English proof (translation)
Introduce `D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s j hs hj`. Take `⟨plg, iso, hplg, -, -, hpe⟩` from `hP.keep.grp`. Establish `hβ` using `hP.char.base.lev.βY 0 Y.hm`. Establish `hinj` using `GlobalTheory.PlaceInj.splitPlace_v_injective D s hs`. Use `haveI : Fintype (Σ k : Fin 2, D.nd.PlG k) := Fintype.ofEquiv _ plg.symm`.

Take `⟨c, hc⟩` from `core Y.hF Y.PY Y.stdPsi.1 (R.βY 0) _ _ hβ (fun kv : (Σ k : Fin 2, D.nd.PlG k) => s kv.1 kv.2) hinj`. Establish `hA : ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * …`. Introduce `k v y x hx`. Establish `hl` using `isLift_of_isLiftAt (s k v) (j k v) (hj k v) y x hx`. Establish `hU : x ∈ Umax D.host.E D.R.r` using `mem_Umax_of_isLiftAt (s k v) (j k v) (hj k v) y x hx`.

Take `⟨hSt, hred⟩` from `hc ⟨k, v⟩ x hx.1 hU`. Establish `hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r` using `fun a => lt_of_lt_of_eq a.2 (rank_zeroth_component_eq D)`. Use `⟨Y.PY.into _, mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP _ => ?_, fun PP hP => ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[mem_blockTri]`. Introduce `i i' hij`.

It suffices to derive a contradiction. Unfold `blkOf at hij`. Rewrite `hij` using `[if_pos (hr i), if_pos (hr i')]`. Conclude with `lt_irrefl 0 hij`. Conclude with `absurd hP (Finset.notMem_empty PP)`.

Generalize the expression as in `hγ : GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) = γ`. Establish `hval : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (a b : Fin D.R.r), Valued.v ((s kv.1 kv.2).proj (x.1.1 a b) - ((((γ kv).1 a b).val : ℕ) : (s kv.1 kv.2).v.adicCompletion (maximalRealSubfield D.host.E))) < 1`. Introduce `kv a b`. Distinguish the cases in `hkv : kv = ⟨k, v⟩`. Substitute `hkv` using the available equality.

Establish `: γ ⟨k, v⟩ = GlobalTheory.GLp.red (D.host.g k) D.R.r y`. Rewrite using `[← hγ]`. Simplify using `[GlobalTheory.GoodTypes.facHom]`. Rewrite using `[this]`. Conclude with `hl.2 a b`.

Establish `: γ kv = 1`. Rewrite using `[← hγ]`. Simplify using `[GlobalTheory.GoodTypes.facHom, hkv]`. Rewrite using `[this, proj_off (s k v) (s kv.1 kv.2) (fun h => hkv (hinj h)) hx.1, Units.val_one, Matrix.one_apply, Matrix.one_apply]`. Use `split_ifs`.

Rewrite using `[ZMod.val_one]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Use function extensionality and compare the values at `PP`. Take `⟨kv, rfl⟩` from `plg.surjective PP`.

Establish `e1 : cG.symm γ (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (γ kv)`. Use `hpe (R.eG.symm (cG.symm γ)) kv` as an intermediate fact. Simplify `this` using `only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply]`. Use `Eq.trans ?_ e1.symm` and prove the remaining obligations. Apply `Units.ext` to reduce the goal to its premises.

Use `(GlobalTheory.RedFrame.upperLeftBlock_eq_submatrix_of_rank_eq (R.dat0 R.triv).hr (rank_zeroth_component_eq D).le _).trans ?_` and prove the remaining obligations. Use extensionality with `a b`. Establish `h1` using `hred kv (Fin.castLE (R.dat0 R.triv).hr a) (Fin.castLE (R.dat0 R.triv).hr b) _ (hval kv a b)`. Establish `hw : (s kv.1 kv.2).w = (plg kv).1` using `(hs _ _).trans (hplg kv).symm`. Establish `h2 : (redFn (R.βY 0) (plg kv).1 (finE (Yc D 0) (Y.PY.ψ (c * x * c⁻¹)))).1 (Fin.castLE (R.dat0 R.triv).hr a) (Fin.castLE (R.dat0 R.triv).hr b) = ((((γ kv).1 a b).val : ℕ) : kP (plg kv).1)`.

Rewrite using `[← hw]`. Conclude with `h1`. Use `h2.trans ?_` and prove the remaining obligations. Use `show _ = iso kv ((γ kv).1 a b)`. Rewrite using `[← map_natCast (iso kv), ZMod.natCast_zmod_val]`.

Use `⟨c, hA, fun b Tm hT => ?_⟩` and prove the remaining obligations. Simplify using `only [KFix, Submodule.mem_iInf, LinearMap.mem_ker]`. Introduce `k v y x hx`. Establish `h1` using `hA k v y x hx`. Rewrite `h1` using `[MonoidHom.mem_ker.1 y.2, map_one, map_one]`.

Take `⟨h2, h3⟩` from `lev_of_lift_one R.toLevCh (R.toRealDat.levR F.lv2 b) _ h1`. Rewrite using `[LinearMap.sub_apply, sub_eq_zero]`. Apply `MultilinearMap.ext` to reduce the goal to its premises. Introduce `w`. Use function extensionality and compare the values at `g`.

Conclude with `fixed_of_mem_mult (R.MY 0) _ _ h2 h3 hT w g`.
-/
theorem rows_fixed : ∀ {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 I0 T : Type} {A3 : FamIn3 D.what₂.LL G Pl0 I0 (List ℕ) T D.R.m} {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat3 D A3 Ks) (F : Face3 D A3) (cG : G0 R.Pg D.R.r ≃* G0g D.nd) {X0 : BaseLevelRowSide D} (Y : GlobalTheory.Mem.R3.Read (A3 := A3) R.toRealDat F.lv2 X0), GlobalTheory.Mem.R3.Pins R F cG → ∀ (s : ∀ k : Fin 2, D.nd.PlG k → SplitPlace D.host.E) (j : ∀ k v, ℚ_[D.host.g k] ≃+* (s k v).v.adicCompletion (maximalRealSubfield D.host.E)), (∀ k v, (s k v).w = D.naut.plGw k v) → (∀ k v, Continuous (j k v)) → ∃ c : GAf D.host.E D.R.r, (∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r), IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv) (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹))) ∧ ∀ (b : Bool), ∀ Tm ∈ Mult.Mult R.θ (R.MY 0) (levS _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))) (levChi _ (R.βY 0) (R.dat0 (R.toRealDat.levR F.lv2 b))), Tm ∈ KFix D s j ((principalLevelFrame.actM Y.PY (R.MY 0)).comp (MulAut.conj c).toMonoidHom) := by
  intro D G _ _ Pl0 I0 T A3 Ks _ _ _ R F cG X0 Y hP s j hs hj
  obtain ⟨plg, iso, hplg, -, -, hpe⟩ := hP.keep.grp
  have hβ := hP.char.base.lev.βY 0 Y.hm
  have hinj := GlobalTheory.PlaceInj.splitPlace_v_injective D s hs
  haveI : Fintype (Σ k : Fin 2, D.nd.PlG k) := Fintype.ofEquiv _ plg.symm
  obtain ⟨c, hc⟩ := core Y.hF Y.PY Y.stdPsi.1 (R.βY 0) _ _ hβ (fun kv : (Σ k : Fin 2, D.nd.PlG k) => s kv.1 kv.2) hinj
  have hA : ∀ (k : Fin 2) (v : D.nd.PlG k) (y : GL (Fin D.R.r) ℤ_[D.host.g k]) (x : GAf D.host.E D.R.r),
      IsLiftAt (s k v) (j k v) y x → IsLevelLift (Yc D 0) (R.βY 0) (R.dat0 R.triv)
        (cG.symm (GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y))) (Y.PY.ψ (c * x * c⁻¹)) := by
    intro k v y x hx
    have hl := isLift_of_isLiftAt (s k v) (j k v) (hj k v) y x hx
    have hU : x ∈ Umax D.host.E D.R.r := mem_Umax_of_isLiftAt (s k v) (j k v) (hj k v) y x hx
    obtain ⟨hSt, hred⟩ := hc ⟨k, v⟩ x hx.1 hU
    have hr : ∀ a : Fin (Yc D 0).rank, (a : ℕ) < (R.dat0 R.triv).r := fun a => lt_of_lt_of_eq a.2 (rank_zeroth_component_eq D)
    refine ⟨Y.PY.into _, mem_parLev.2 ⟨GlobalTheory.LevSplit.finE_mem_UA _ _, hSt, fun PP _ => ?_, fun PP hP => ?_⟩, ?_⟩
    · rw [mem_blockTri]
      intro i i' hij
      exfalso
      unfold blkOf at hij
      rw [if_pos (hr i), if_pos (hr i')] at hij
      exact lt_irrefl 0 hij
    · exact absurd hP (Finset.notMem_empty PP)
    · generalize hγ : GlobalTheory.GoodTypes.facHom D k v (GlobalTheory.GLp.red (D.host.g k) D.R.r y) = γ
      have hval : ∀ (kv : Σ k : Fin 2, D.nd.PlG k) (a b : Fin D.R.r), Valued.v ((s kv.1 kv.2).proj (x.1.1 a b) -
          ((((γ kv).1 a b).val : ℕ) : (s kv.1 kv.2).v.adicCompletion (maximalRealSubfield D.host.E))) < 1 := by
        intro kv a b
        by_cases hkv : kv = ⟨k, v⟩
        · subst hkv
          have : γ ⟨k, v⟩ = GlobalTheory.GLp.red (D.host.g k) D.R.r y := by
            rw [← hγ]; simp [GlobalTheory.GoodTypes.facHom]
          rw [this]
          exact hl.2 a b
        · have : γ kv = 1 := by
            rw [← hγ]; simp [GlobalTheory.GoodTypes.facHom, hkv]
          rw [this, proj_off (s k v) (s kv.1 kv.2) (fun h => hkv (hinj h)) hx.1, Units.val_one, Matrix.one_apply,
            Matrix.one_apply]
          split_ifs
          · rw [ZMod.val_one]; simp
          · simp
      funext PP
      obtain ⟨kv, rfl⟩ := plg.surjective PP
      have e1 : cG.symm γ (plg kv) = Formalism.UG.bc (iso kv : ZMod (D.host.g kv.1) →+* kP (plg kv).1) (γ kv) := by
        have := hpe (R.eG.symm (cG.symm γ)) kv
        simpa only [MulEquiv.trans_apply, MulEquiv.apply_symm_apply] using this
      refine Eq.trans ?_ e1.symm
      apply Units.ext
      refine (GlobalTheory.RedFrame.upperLeftBlock_eq_submatrix_of_rank_eq (R.dat0 R.triv).hr (rank_zeroth_component_eq D).le _).trans ?_
      ext a b
      have h1 := hred kv (Fin.castLE (R.dat0 R.triv).hr a) (Fin.castLE (R.dat0 R.triv).hr b) _ (hval kv a b)
      have hw : (s kv.1 kv.2).w = (plg kv).1 := (hs _ _).trans (hplg kv).symm
      have h2 : (redFn (R.βY 0) (plg kv).1 (finE (Yc D 0) (Y.PY.ψ (c * x * c⁻¹)))).1 (Fin.castLE (R.dat0 R.triv).hr a)
          (Fin.castLE (R.dat0 R.triv).hr b) = ((((γ kv).1 a b).val : ℕ) : kP (plg kv).1) := by
        rw [← hw]; exact h1
      refine h2.trans ?_
      show _ = iso kv ((γ kv).1 a b)
      rw [← map_natCast (iso kv), ZMod.natCast_zmod_val]
  refine ⟨c, hA, fun b Tm hT => ?_⟩
  simp only [KFix, Submodule.mem_iInf, LinearMap.mem_ker]
  intro k v y x hx
  have h1 := hA k v y x hx
  rw [MonoidHom.mem_ker.1 y.2, map_one, map_one] at h1
  obtain ⟨h2, h3⟩ := lev_of_lift_one R.toLevCh (R.toRealDat.levR F.lv2 b) _ h1
  rw [LinearMap.sub_apply, sub_eq_zero]
  apply MultilinearMap.ext
  intro w
  funext g
  exact fixed_of_mem_mult (R.MY 0) _ _ h2 h3 hT w g

end Main

end GlobalTheory.RowLevConj

end
