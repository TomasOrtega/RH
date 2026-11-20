import Development.WeilBound.RepresentationTheoryGL.RegularisedSiegelWeil.ThetaIdempotents.ThetaCoefficients.SiegelWeilHermitianFormula
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleProjectionsStatement
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.AdelicTupleCompactSetsStatement

noncomputable section

open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open scoped TensorProduct ENNReal

namespace PositivityTheory.Rg.Rsw.L.LatticeFibreBump

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

/- English proof (translation)
Take `⟨k, eK, hK⟩` from `PI.VolStabS.exists_coord_tens F E`. Take `⟨k1, e1, h1⟩` from `PI.VolStabS.exists_coord_pi eK hK (Fin M)`. Take `⟨N, eV, hV⟩` from `PI.VolStabS.exists_coord_pi e1 h1 (Fin n)`. Set `eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ)` to `{ eV.toEquiv with map_add' := hV }`. Take `⟨ρ, hρ⟩` from `(hC.image eV.continuous).isBounded.subset_closedBall 0`.

Set `β : ContDiffBump (0 : Fin N → ℝ)` to `⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩`. Establish `hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ)` using `β.hasCompactSupport.comp_left Complex.ofReal_zero`. Set `f : SchwartzMap (Fin N → ℝ) ℂ` to `hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)`. Use `⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩` and prove the remaining obligations. Use `show ((β (eA Y) : ℝ) : ℂ) = 1`.

Establish `hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn` using `Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)`. Rewrite using `[β.one_of_mem_closedBall hm, Complex.ofReal_one]`.
-/
theorem archBump [IsTotallyReal F] {M n : ℕ} (C : Set (Fin n → Fin M → Ainf F ⊗[F] E)) (hC : IsCompact C) :
    ∃ φ : (Fin n → Fin M → Ainf F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzArch φ ∧ ∀ Y ∈ C, φ Y = 1 := by
  obtain ⟨k, eK, hK⟩ := PI.VolStabS.exists_coord_tens F E
  obtain ⟨k1, e1, h1⟩ := PI.VolStabS.exists_coord_pi eK hK (Fin M)
  obtain ⟨N, eV, hV⟩ := PI.VolStabS.exists_coord_pi e1 h1 (Fin n)
  let eA : (Fin n → Fin M → Ainf F ⊗[F] E) ≃+ (Fin N → ℝ) := { eV.toEquiv with map_add' := hV }
  obtain ⟨ρ, hρ⟩ := (hC.image eV.continuous).isBounded.subset_closedBall 0
  let β : ContDiffBump (0 : Fin N → ℝ) :=
    ⟨max ρ 1, max ρ 1 + 1, lt_max_of_lt_right one_pos, lt_add_one _⟩
  have hs : HasCompactSupport fun z => ((β z : ℝ) : ℂ) := β.hasCompactSupport.comp_left Complex.ofReal_zero
  let f : SchwartzMap (Fin N → ℝ) ℂ := hs.toSchwartzMap (Complex.ofRealCLM.contDiff.comp β.contDiff)
  refine ⟨fun X => f (eA X), ⟨N, eA, eV.continuous, eV.symm.continuous, f, fun _ => rfl⟩, fun Y hY => ?_⟩
  show ((β (eA Y) : ℝ) : ℂ) = 1
  have hm : eA Y ∈ Metric.closedBall (0 : Fin N → ℝ) β.rIn :=
    Metric.closedBall_subset_closedBall (le_max_left ρ 1) (hρ ⟨Y, hY, rfl⟩)
  rw [β.one_of_mem_closedBall hm, Complex.ofReal_one]

omit [NumberField F] [NumberField E] in
/- English proof (translation)
Rewrite using `[← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]`.
-/
theorem repr_natCast_mul' {d : ℕ} (b : Module.Basis (Fin d) F E) {R : Type} [CommRing R]
    [Algebra F R] (N : ℕ) (y : R ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis R b).repr ((N : R ⊗[F] E) * y) k =
      (N : R) * (Algebra.TensorProduct.basis R b).repr y k := by
  rw [← nsmul_eq_mul, map_nsmul, Finsupp.smul_apply, nsmul_eq_mul]

/- English proof (translation)
Establish `: IsModuleTopology (Fv F v) (Fv F v ⊗[F] E)` using `⟨rfl⟩`. Establish `: IsTopologicalRing (Fv F v ⊗[F] E)` using `IsModuleTopology.isTopologicalRing (Fv F v) _`. Use `set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu`. Establish `hNu : (N : Fv F v ⊗[F] E) * u = 1`. Rewrite using `[hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul, mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]`.

Establish `hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i` using `fun c => continuous_pi fun a => continuous_pi fun i => continuous_const.mul ((continuous_apply i).comp (continuous_apply a))`. Establish `heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v`. Use extensionality with `Y`. Prove the components needed by the constructor for the conclusion. Introduce `hY`.

Use `⟨_, hY, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `a i`. Use `show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i`. Rewrite using `[← mul_assoc, mul_comm u, hNu, one_mul]`. Introduce and unpack `⟨Z, hZ, rfl⟩ show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v`.

Simplify `hZ` using `only [← mul_assoc, hNu, one_mul]`. Conclude with `⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩`.
-/
theorem scaled_cpt_open {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hL : IsCompact (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E)) ∧
      IsOpen (latV b v : Set (Fin n → Fin M → Fv F v ⊗[F] E))) :
    IsCompact {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} ∧
      IsOpen {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} := by
  have : IsModuleTopology (Fv F v) (Fv F v ⊗[F] E) := ⟨rfl⟩
  have : IsTopologicalRing (Fv F v ⊗[F] E) := IsModuleTopology.isTopologicalRing (Fv F v) _
  set u : Fv F v ⊗[F] E := algebraMap F _ ((N : F)⁻¹) with hu
  have hNu : (N : Fv F v ⊗[F] E) * u = 1 := by
    rw [hu, ← map_natCast (algebraMap F (Fv F v ⊗[F] E)) N, ← map_mul,
      mul_inv_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have hc : ∀ c : Fv F v ⊗[F] E, Continuous fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => c * Y a i :=
    fun c => continuous_pi fun a => continuous_pi fun i =>
      continuous_const.mul ((continuous_apply i).comp (continuous_apply a))
  have heq : {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} =
      (fun Y : Fin n → Fin M → Fv F v ⊗[F] E => fun a i => u * Y a i) '' latV b v := by
    ext Y
    constructor
    · intro hY
      refine ⟨_, hY, ?_⟩
      funext a i
      show u * ((N : Fv F v ⊗[F] E) * Y a i) = Y a i
      rw [← mul_assoc, mul_comm u, hNu, one_mul]
    · rintro ⟨Z, hZ, rfl⟩
      show (fun a i => (N : Fv F v ⊗[F] E) * (u * Z a i)) ∈ latV b v
      simpa only [← mul_assoc, hNu, one_mul] using hZ
  exact ⟨heq ▸ hL.1.image (hc u), hL.2.preimage (hc _)⟩

omit [NumberField E] in

/- English proof (translation)
Establish `hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F`. Establish `h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹)` using `(evalV F v).commutes _`. Rewrite `hv` using `[h]`. Then use the resulting hypothesis. Establish `hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1`. Rewrite using `[← map_natCast (algebraMap F (Fv F v)) N, ← map_mul, inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]`.

Establish `key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F`. Introduce `c`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Use `mul_mem hw h` as an intermediate fact.

Rewrite `this` using `[← mul_assoc, hwN, one_mul]`. Then use the resulting hypothesis. Conclude with `fun h => mul_mem (natCast_mem _ N) h`. Use extensionality with `Y`. Simplify using `only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]`.
-/
theorem scaled_eq_lat {d n M : ℕ} (b : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F)) (N : ℕ)
    (hN : 0 < N) (hv : (algebraMap F (Af F) ((N : F)⁻¹)) v ∈ v.adicCompletionIntegers F) :
    {Y : Fin n → Fin M → Fv F v ⊗[F] E | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v} = latV b v := by
  have hw : algebraMap F (Fv F v) ((N : F)⁻¹) ∈ v.adicCompletionIntegers F := by
    have h : (algebraMap F (Af F) ((N : F)⁻¹)) v = algebraMap F (Fv F v) ((N : F)⁻¹) :=
      (evalV F v).commutes _
    rwa [h] at hv
  have hwN : algebraMap F (Fv F v) ((N : F)⁻¹) * (N : Fv F v) = 1 := by
    rw [← map_natCast (algebraMap F (Fv F v)) N, ← map_mul,
      inv_mul_cancel₀ (Nat.cast_ne_zero.mpr hN.ne'), map_one]
  have key : ∀ c : Fv F v, (N : Fv F v) * c ∈ v.adicCompletionIntegers F ↔ c ∈ v.adicCompletionIntegers F := by
    intro c
    constructor
    · intro h
      have := mul_mem hw h
      rwa [← mul_assoc, hwN, one_mul] at this
    · exact fun h => mul_mem (natCast_mem _ N) h
  ext Y
  simp only [Set.mem_ofPred_eq, latV, repr_natCast_mul', key]

/- English proof (translation)
Establish `: IsTotallyReal F` using `hCM.1`. Use `⟨fun K hK => ?_⟩` and prove the remaining obligations. Set `b` to `Module.finBasis F E`. Take `⟨N, R, hN, -, hsub⟩` from `(GlobalTheory.T.adelic_tuple_compact_sets F E σ hCM _ b n M).2 K hK`. Take `⟨hcInf, -, -, hlat, -⟩` from `GlobalTheory.T.adelic_tuple_projections F E σ hCM _ b n M`.

Take `⟨φ, hφ, hφ1⟩` from `archBump (projInf '' K) (hK.image hcInf)`. Set `A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E)` to `fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}`. Set `y : Af F` to `algebraMap F (Af F) ((N : F)⁻¹)`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite` using `y.2`. Establish `hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v)` using `fun v => scaled_cpt_open b v N hN (hlat v)`.

Establish `hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v` using `fun v hv => scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))`. Establish `hΦ` using `GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl`. Establish `hint` using `hν _ hΦ`. Establish `h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ}`. Introduce `X hX`.

Establish `e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1`. Unfold `GlobalTheory.CompanionTheory.SiegelND.Coef.pureN`. Rewrite using `[hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]`. Simplify using `[e1]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem finCpt_of_integrable (σ : E →ₐ[F] E) (hCM : IsCMExt F E σ) (M : ℕ) (J : Matrix (Fin M) (Fin M) E)
    (hJ : IsHermND σ J) (n : ℕ) (h2n : 2 * n < M) (ν : Measure (Fin n → Fin M → AF F ⊗[F] E))
    (hν : ∀ Φ : (Fin n → Fin M → AF F ⊗[F] E) → ℂ,
      GlobalTheory.Published.SiegelOneVector.IsSchwartzBruhat (F := F) (E := E) Φ → Integrable Φ ν) :
    IsFiniteMeasureOnCompacts ν := by
  classical
  have : IsTotallyReal F := hCM.1
  refine ⟨fun K hK => ?_⟩
  let b := Module.finBasis F E
  obtain ⟨N, R, hN, -, hsub⟩ := (GlobalTheory.T.adelic_tuple_compact_sets F E σ hCM _ b n M).2 K hK
  obtain ⟨hcInf, -, -, hlat, -⟩ := GlobalTheory.T.adelic_tuple_projections F E σ hCM _ b n M
  obtain ⟨φ, hφ, hφ1⟩ := archBump (projInf '' K) (hK.image hcInf)
  let A : ∀ v : HeightOneSpectrum (𝓞 F), Set (Fin n → Fin M → Fv F v ⊗[F] E) :=
    fun v => {Y | (fun a i => (N : Fv F v ⊗[F] E) * Y a i) ∈ latV b v}
  let y : Af F := algebraMap F (Af F) ((N : F)⁻¹)
  have hfin : {v : HeightOneSpectrum (𝓞 F) | y v ∉ v.adicCompletionIntegers F}.Finite := y.2
  have hA : ∀ v, IsCompact (A v) ∧ IsOpen (A v) := fun v => scaled_cpt_open b v N hN (hlat v)
  have hAl : ∀ v, v ∉ hfin.toFinset → A v = latV b v := fun v hv =>
    scaled_eq_lat b v N hN (not_not.mp fun h => hv (hfin.mem_toFinset.mpr h))
  have hΦ := GlobalTheory.T.factorizable_schwartz_orbital_integral F E σ hCM M J hJ n h2n _ b hfin.toFinset φ A hφ hA hAl
  have hint := hν _ hΦ
  have h1 : K ⊆ {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := by
    intro X hX
    have e1 : GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X = 1 := by
      unfold GlobalTheory.CompanionTheory.SiegelND.Coef.pureN
      rw [hφ1 _ ⟨X, hX, rfl⟩, Set.indicator_of_mem
        (show projFin X ∈ GlobalTheory.CompanionTheory.SiegelND.Coef.boxFN A from fun v => (hsub X hX).1 v), one_mul]
    simp [e1]
  calc ν K ≤ ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := measure_mono h1
    _ = 1 * ν {X | 1 ≤ ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ} := (one_mul _).symm
    _ ≤ ∫⁻ X, ‖GlobalTheory.CompanionTheory.SiegelND.Coef.pureN φ A X‖ₑ ∂ν := mul_meas_ge_le_lintegral₀ hint.1.enorm 1
    _ < ⊤ := hint.2

end PositivityTheory.Rg.Rsw.L.LatticeFibreBump

end
