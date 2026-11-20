import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdelicUnitriangularMulMemUnipotentTimesIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsUpperUnitriangularEntriesHomeomorphStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsMapEntriesHaarUnitriangularEqSmulPiStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AddHaarMapMulFiniteIdeleOfUniformizerPowersStatement
import GroundTheory.AutomorphicForms.ReductionMeasure
import GroundTheory.GlobalFields.Adele.Topology

noncomputable section

open NumberField IsDedekindDomain Matrix Formalism.UG GlobalTheory.CuspRep MeasureTheory
open scoped ENNReal

namespace GlobalTheory.CellDec.ModulusPf

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Apply `FiniteAdeleRing.ext` to reduce the goal to its premises. Introduce `v`. Express the relevant statement in the definitionally equal form `((ϖ v ^ (m + m') v : (v.adicCompletion E)ˣ) : v.adicCompletion E) = ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m' v : (v.adicCompletion E)ˣ) : v.adicCompletion E)`. Rewrite using `[Finsupp.add_apply, _root_.zpow_add, Units.val_mul]`.
-/
theorem adl_add (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m + m') = GlobalTheory.CellDec.adl ϖ m * GlobalTheory.CellDec.adl ϖ m' := by
  apply Units.ext
  apply FiniteAdeleRing.ext
  intro v
  change ((ϖ v ^ (m + m') v : (v.adicCompletion E)ˣ) : v.adicCompletion E) =
    ((ϖ v ^ m v : (v.adicCompletion E)ˣ) : v.adicCompletion E) * ((ϖ v ^ m' v : (v.adicCompletion E)ˣ) : v.adicCompletion E)
  rw [Finsupp.add_apply, _root_.zpow_add, Units.val_mul]

/- English proof (translation)
Rewrite using `[eq_mul_inv_iff_mul_eq, ← adl_add, sub_add_cancel]`.
-/
theorem adl_sub (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ) (m m' : HeightOneSpectrum (𝓞 E) →₀ ℤ) :
    GlobalTheory.CellDec.adl ϖ (m - m') = GlobalTheory.CellDec.adl ϖ m * (GlobalTheory.CellDec.adl ϖ m')⁻¹ := by
  rw [eq_mul_inv_iff_mul_eq, ← adl_add, sub_add_cancel]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simp`. Consider the case `insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]`.
-/
theorem zpow_sum_real {ι : Type} (q : ℝ) (hq : q ≠ 0) (s : Finset ι) (f : ι → ℤ) :
    ∏ i ∈ s, q ^ f i = q ^ (∑ i ∈ s, f i) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih => rw [Finset.prod_insert ha, Finset.sum_insert ha, ih, zpow_add₀ hq]

/- English proof (translation)
Rewrite using `[GlobalTheory.CellDec.wtS, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2) (by simp) (fun p : Fin n × Fin n => a p.1 - a p.2), Finset.sum_filter, Fintype.sum_prod_type]`.
-/
theorem sum_pairs_eq_wtS {n : ℕ} (a : Fin n → ℤ) :
    ∑ p : {p : Fin n × Fin n // p.1 < p.2}, (a p.1.1 - a p.1.2) = GlobalTheory.CellDec.wtS n a := by
  classical
  rw [GlobalTheory.CellDec.wtS, ← Finset.sum_subtype (Finset.univ.filter fun p : Fin n × Fin n => p.1 < p.2)
    (by simp) (fun p : Fin n × Fin n => a p.1 - a p.2), Finset.sum_filter, Fintype.sum_prod_type]

end GlobalTheory.CellDec.ModulusPf

namespace GlobalTheory.CellDec.ModulusPf

/- English proof (translation)
Introduce `E _ _ n _ _ ν _ ϖ hϖ l A hA`. Use `set t := GlobalTheory.CellDec.tl n ϖ l with ht`. Set `d : Fin n → (AdeleRing (𝓞 E) E)ˣ` to `fun i => finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))`. Establish `htd : t = GlobalTheory.SmGL.diagT (Ad E) (Fin n) d` using `GlobalTheory.CellDec.tl_eq_diagT ϖ l`. Set `φ : GlobalTheory.CellDec.NA E n → GlobalTheory.CellDec.NA E n` to `fun u => ⟨t * u * t⁻¹, GlobalTheory.CellDec.tl_conj_mem ϖ l u.2⟩`.

Establish `hφc : Continuous φ` using `Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _`. Establish `hset : {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = t * (u : GA E n) * t⁻¹} = φ ⁻¹' A`. Use extensionality with `u`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a, ha, h⟩`.

Establish `: φ u = a` using `Subtype.ext h.symm`. Simplify `ha` using `[Set.mem_preimage, this]`. Introduce `hu`. Conclude with `⟨φ u, hu, rfl⟩`. Rewrite using `[hset, ← Measure.map_apply hφc.measurable hA]`.

Set `co : GlobalTheory.CellDec.NA E n → ({p : Fin n × Fin n // p.1 < p.2} → Ad E)` to `fun u p => ((u : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) p.1.1 p.1.2`. Take `⟨e, he⟩` from `GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph (Ad E) n`. Establish `hco : ⇑e = co` using `funext he`. Set `μR : Measure (Ad E)` to `Measure.addHaar`. Take `⟨c, hc⟩` from `GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi (Ad E) n μR ν`.

Set `mm : {p : Fin n × Fin n // p.1 < p.2} → (HeightOneSpectrum (𝓞 E) →₀ ℤ)` to `fun p => Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.1) rfl l - Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.2) rfl l`. Set `a : {p : Fin n × Fin n // p.1 < p.2} → Ad E` to `fun p => ((finId E (GlobalTheory.CellDec.adl ϖ (mm p)) : (Ad E)ˣ) : Ad E)`. Set `S : ({p : Fin n × Fin n // p.1 < p.2} → Ad E) → ({p : Fin n × Fin n // p.1 < p.2} → Ad E)` to `fun x p => a p * x p`. Apply the tactic sequence `have hentry : ∀ (u : GA E n) (i j : Fin n), ((t * u * t⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j = ((d i : Ad E) * (((d j)⁻¹ : (Ad E)ˣ) : Ad E)) * (u : Matrix (Fin n) (Fin n) (Ad E)) i j := by`. Introduce `u i j`.

Rewrite using `[htd, ← map_inv, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul]`. Simplify using `only [Pi.inv_apply]`. Expand and normalize the polynomial expressions, which then agree. Establish `ha : ∀ p, a p = (d p.1.1 : Ad E) * (((d p.1.2)⁻¹ : (Ad E)ˣ) : Ad E)`. Introduce `p`.

Simplify using `only [a, mm, d, adl_sub, map_mul, map_inv, Units.val_mul]`. Establish `hSco : co ∘ φ = S ∘ co`. Use function extensionality and compare the values at `u p`. Simplify using `only [Function.comp_apply, co, S, φ]`. Rewrite using `[hentry, ha]`.

Set `k : {p : Fin n × Fin n // p.1 < p.2} → ℝ≥0∞` to `fun p => ENNReal.ofReal (∏ v ∈ l.support, (qV E v : ℝ) ^ (mm p v))`. Establish `hk : ∀ p, Measure.map (fun x : Ad E => a p * x) μR = k p • μR` using `fun p => GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers E ϖ hϖ (mm p) l.support (fun v hv => by simp [mm, Finsupp.notMem_support_iff.1 hv]) μR`. Use `haveI : ∀ p, SigmaFinite (k p • μR) := fun p => (inferInstance : SigmaFinite ((Real.toNNReal _) • μR))`. Establish `hSm : Measurable S`. Use `measurable_pi_lambda _ fun p => ?_` and prove the remaining obligations.

Conclude with `(measurable_const_mul (a p)).comp (measurable_pi_apply p)`. Establish `hS : Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR`. Establish `h1 : Measure.pi (fun p => k p • μR) = Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR)`. Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.map_apply hSm (MeasurableSet.univ_pi hs)]`.

Rewrite using `[show S ⁻¹' Set.univ.pi s = Set.univ.pi fun p => (fun x : Ad E => a p * x) ⁻¹' s p from Set.preimage_pi Set.univ s fun p (x : Ad E) => a p * x]`. Rewrite using `[Measure.pi_pi]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← hk p, Measure.map_apply (measurable_const_mul _) (hs p)]`. Establish `h2 : Measure.pi (fun p => k p • μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR`.

Use `Measure.pi_eq fun s hs => ?_` and prove the remaining obligations. Rewrite using `[Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]`. Both sides reduce to the same expression. Rewrite using `[← h1, h2]`. Establish `hK : (∏ p, k p) = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l)`.

Simplify using `only [k]`. Rewrite using `[← ENNReal.ofReal_prod_of_nonneg (fun p _ => Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _)]`. Use `congr 1`. Rewrite using `[Finset.prod_comm, GlobalTheory.CellDec.dinv]`. Use `Finset.prod_congr rfl fun v _ => ?_` and prove the remaining obligations.

Establish `hq : (qV E v : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 (by rw [qV, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)`. Rewrite using `[zpow_sum_real _ hq, ← sum_pairs_eq_wtS]`. Use `congr 1`. Establish `key : Measure.map φ ν = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν`. Establish `hem : Measurable e` using `e.continuous.measurable`.

Establish `h3 : Measure.map e (Measure.map φ ν) = Measure.map e (ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν)`. Establish `hc' : Measure.map e ν = c • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR`. Rewrite using `[hco]`. Conclude with `hc`. Rewrite using `[Measure.map_map hem hφc.measurable, hco, hSco, ← Measure.map_map hSm (hco ▸ hem), ← hco, hc', Measure.map_smul, Measure.map_smul, hS, hc', ← hK, smul_comm]`.

Establish `h4` using `congrArg (Measure.map e.toMeasurableEquiv.symm) h3`. Rewrite `h4` using `[show (⇑e : GlobalTheory.CellDec.NA E n → _) = ⇑e.toMeasurableEquiv from rfl, MeasurableEquiv.map_symm_map, MeasurableEquiv.map_symm_map]`. Then use the resulting hypothesis. Rewrite using `[key]`. Both sides reduce to the same expression.
-/
theorem modulus_conj : ∀ (E : Type) [Field E] [NumberField E] (n : ℕ) [MeasurableSpace (GA E n)] [BorelSpace (GA E n)]
    (ν : Measure (GlobalTheory.CellDec.NA E n)) [ν.IsHaarMeasure] (ϖ : ∀ v : HeightOneSpectrum (𝓞 E), (v.adicCompletion E)ˣ),
    (∀ v, IsUnifV E v (ϖ v : v.adicCompletion E)) → ∀ (l : HeightOneSpectrum (𝓞 E) →₀ (Fin n → ℤ))
    (A : Set (GlobalTheory.CellDec.NA E n)), MeasurableSet A →
    ν {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = GlobalTheory.CellDec.tl n ϖ l * (u : GA E n) * (GlobalTheory.CellDec.tl n ϖ l)⁻¹} =
      ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) * ν A := by
  intro E _ _ n _ _ ν _ ϖ hϖ l A hA
  classical
  set t := GlobalTheory.CellDec.tl n ϖ l with ht
  let d : Fin n → (AdeleRing (𝓞 E) E)ˣ := fun i => finId E (GlobalTheory.CellDec.adl ϖ (Finsupp.mapRange (fun x : Fin n → ℤ => x i) rfl l))
  have htd : t = GlobalTheory.SmGL.diagT (Ad E) (Fin n) d := GlobalTheory.CellDec.tl_eq_diagT ϖ l
  let φ : GlobalTheory.CellDec.NA E n → GlobalTheory.CellDec.NA E n := fun u => ⟨t * u * t⁻¹, GlobalTheory.CellDec.tl_conj_mem ϖ l u.2⟩
  have hφc : Continuous φ :=
    Continuous.subtype_mk ((continuous_const.mul continuous_subtype_val).mul continuous_const) _
  have hset : {u : GlobalTheory.CellDec.NA E n | ∃ a ∈ A, (a : GA E n) = t * (u : GA E n) * t⁻¹} = φ ⁻¹' A := by
    ext u
    constructor
    · rintro ⟨a, ha, h⟩
      have : φ u = a := Subtype.ext h.symm
      simpa [Set.mem_preimage, this] using ha
    · intro hu
      exact ⟨φ u, hu, rfl⟩
  rw [hset, ← Measure.map_apply hφc.measurable hA]

  let co : GlobalTheory.CellDec.NA E n → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) :=
    fun u p => ((u : GL (Fin n) (Ad E)) : Matrix (Fin n) (Fin n) (Ad E)) p.1.1 p.1.2
  obtain ⟨e, he⟩ := GlobalTheory.T.exists_upperUnitriangular_entries_homeomorph (Ad E) n
  have hco : ⇑e = co := funext he
  let μR : Measure (Ad E) := Measure.addHaar
  obtain ⟨c, hc⟩ := GlobalTheory.T.exists_map_entries_haar_unitriangular_eq_smul_pi (Ad E) n μR ν
  let mm : {p : Fin n × Fin n // p.1 < p.2} → (HeightOneSpectrum (𝓞 E) →₀ ℤ) := fun p =>
    Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.1) rfl l - Finsupp.mapRange (fun x : Fin n → ℤ => x p.1.2) rfl l
  let a : {p : Fin n × Fin n // p.1 < p.2} → Ad E := fun p => ((finId E (GlobalTheory.CellDec.adl ϖ (mm p)) : (Ad E)ˣ) : Ad E)
  let S : ({p : Fin n × Fin n // p.1 < p.2} → Ad E) → ({p : Fin n × Fin n // p.1 < p.2} → Ad E) := fun x p => a p * x p
  have hentry : ∀ (u : GA E n) (i j : Fin n), ((t * u * t⁻¹ : GA E n) : Matrix (Fin n) (Fin n) (Ad E)) i j =
      ((d i : Ad E) * (((d j)⁻¹ : (Ad E)ˣ) : Ad E)) * (u : Matrix (Fin n) (Fin n) (Ad E)) i j := by
    intro u i j
    rw [htd, ← map_inv, Units.val_mul, Units.val_mul, GlobalTheory.SmGL.val_diagT, GlobalTheory.SmGL.val_diagT, Matrix.mul_diagonal,
      Matrix.diagonal_mul]
    simp only [Pi.inv_apply]
    ring
  have ha : ∀ p, a p = (d p.1.1 : Ad E) * (((d p.1.2)⁻¹ : (Ad E)ˣ) : Ad E) := by
    intro p
    simp only [a, mm, d, adl_sub, map_mul, map_inv, Units.val_mul]
  have hSco : co ∘ φ = S ∘ co := by
    funext u p
    simp only [Function.comp_apply, co, S, φ]
    rw [hentry, ha]
  let k : {p : Fin n × Fin n // p.1 < p.2} → ℝ≥0∞ := fun p => ENNReal.ofReal (∏ v ∈ l.support, (qV E v : ℝ) ^ (mm p v))
  have hk : ∀ p, Measure.map (fun x : Ad E => a p * x) μR = k p • μR := fun p =>
    GlobalTheory.T.addHaar_map_mul_finiteIdeleOfUniformizerPowers E ϖ hϖ (mm p) l.support (fun v hv => by simp [mm, Finsupp.notMem_support_iff.1 hv]) μR
  haveI : ∀ p, SigmaFinite (k p • μR) := fun p => (inferInstance : SigmaFinite ((Real.toNNReal _) • μR))
  have hSm : Measurable S := by
    refine measurable_pi_lambda _ fun p => ?_
    exact (measurable_const_mul (a p)).comp (measurable_pi_apply p)
  have hS : Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) =
      (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
    have h1 : Measure.pi (fun p => k p • μR) = Measure.map S (Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR) := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.map_apply hSm (MeasurableSet.univ_pi hs)]
      rw [show S ⁻¹' Set.univ.pi s = Set.univ.pi fun p => (fun x : Ad E => a p * x) ⁻¹' s p from
        Set.preimage_pi Set.univ s fun p (x : Ad E) => a p * x]
      rw [Measure.pi_pi]
      refine Finset.prod_congr rfl fun p _ => ?_
      rw [← hk p, Measure.map_apply (measurable_const_mul _) (hs p)]
    have h2 : Measure.pi (fun p => k p • μR) = (∏ p, k p) • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
      refine Measure.pi_eq fun s hs => ?_
      rw [Measure.smul_apply, Measure.pi_pi, smul_eq_mul, ← Finset.prod_mul_distrib]
      rfl
    rw [← h1, h2]
  have hK : (∏ p, k p) = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) := by
    simp only [k]
    rw [← ENNReal.ofReal_prod_of_nonneg (fun p _ => Finset.prod_nonneg fun v _ => zpow_nonneg (Nat.cast_nonneg _) _)]
    congr 1
    rw [Finset.prod_comm, GlobalTheory.CellDec.dinv]
    refine Finset.prod_congr rfl fun v _ => ?_
    have hq : (qV E v : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by rw [qV, Ne, Ideal.absNorm_eq_zero_iff]; exact v.ne_bot)
    rw [zpow_sum_real _ hq, ← sum_pairs_eq_wtS]
    congr 1
  have key : Measure.map φ ν = ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν := by
    have hem : Measurable e := e.continuous.measurable
    have h3 : Measure.map e (Measure.map φ ν) = Measure.map e (ENNReal.ofReal (GlobalTheory.CellDec.dinv n l) • ν) := by
      have hc' : Measure.map e ν = c • Measure.pi fun _ : {p : Fin n × Fin n // p.1 < p.2} => μR := by
        rw [hco]; exact hc
      rw [Measure.map_map hem hφc.measurable, hco, hSco, ← Measure.map_map hSm (hco ▸ hem), ← hco, hc',
        Measure.map_smul, Measure.map_smul, hS, hc', ← hK, smul_comm]
    have h4 := congrArg (Measure.map e.toMeasurableEquiv.symm) h3
    rwa [show (⇑e : GlobalTheory.CellDec.NA E n → _) = ⇑e.toMeasurableEquiv from rfl, MeasurableEquiv.map_symm_map,
      MeasurableEquiv.map_symm_map] at h4
  rw [key]
  rfl
end GlobalTheory.CellDec.ModulusPf

end
