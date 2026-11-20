import Mathlib
import GroundTheory.LocalFields.LubinTateTower

noncomputable section

open IntermediateField

namespace GroundTheory.LocalField

open ValuativeRel Polynomial Topology

namespace FormalGroup

section Associated

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {L : Type*} [Field L] [ValuativeRel L] [TopologicalSpace L] [IsNonarchimedeanLocalField L]
  [Algebra K L] [ValuativeExtension K L]

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] in

/- English proof (translation)
Set `_ : UniformSpace L` to `IsTopologicalAddGroup.rightUniformSpace L`. Establish `_ : IsUniformAddGroup L` using `isUniformAddGroup_of_addCommGroup`. Set `_ : UniformSpace 𝒪[K]` to `⊥`. Establish `_ : DiscreteUniformity 𝒪[K]` using `⟨rfl⟩`. Establish `hφc : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _] (algebraMap 𝒪[K] 𝒪[L])`.

Rewrite using `[UniformSpace.toTopologicalSpace_bot]`. Conclude with `continuous_bot`. Establish `hev` using `hasEval_of_mem_maximalIdeal (a := fun _ : Unit => a) fun _ => ha`. Use `set ε := MvPowerSeries.eval₂Hom hφc hev`. Establish `hval : (⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ : 𝒪[L]) = ε φ`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[MvPowerSeries.coe_eval₂Hom]`. Conclude with `psEval_eq_eval₂ φ (fun _ => a) fun _ => ha`. Establish `hεX : ε PowerSeries.X = a`. Rewrite using `[MvPowerSeries.coe_eval₂Hom]`.

Conclude with `MvPowerSeries.eval₂_X _ _ _`. Establish `hεC : ∀ c : 𝒪[K], ε (PowerSeries.C c) = algebraMap 𝒪[K] 𝒪[L] c`. Introduce `c`. Rewrite using `[MvPowerSeries.coe_eval₂Hom]`. Conclude with `MvPowerSeries.eval₂_C _ _ _`.

Take `⟨ψ, hψ⟩` from `PowerSeries.X_dvd_iff.mpr h0`. Use `set c := PowerSeries.constantCoeff ψ`. Establish `hc : c = PowerSeries.coeff 1 φ`. Rewrite using `[hψ, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]`. Take `⟨χ, hχ⟩` from `PowerSeries.X_dvd_iff.mpr (show PowerSeries.constantCoeff (ψ - PowerSeries.C c) = 0 by simp [c])`.

Establish `hψ' : ψ = PowerSeries.C c + PowerSeries.X * χ`. Rewrite using `[← hχ]`. Expand and normalize the polynomial expressions, which then agree. Establish `hunit : IsUnit (ε ψ)`. Rewrite using `[hψ', map_add, map_mul, hεX, hεC]`.

Assume the negation of the conclusion as `hnu`. Establish `hm : algebraMap 𝒪[K] 𝒪[L] c + a * ε χ ∈ 𝓂[L]` using `(IsLocalRing.mem_maximalIdeal _).mpr hnu`. Establish `hm' : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L]`. Use `Ideal.sub_mem _ hm (Ideal.mul_mem_right (ε χ) _ ha)` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Then use the resulting hypothesis.

Rewrite `hm'` using `[hc]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).mp hm' (h1.map _)`. Rewrite using `[hval, hψ, map_mul, hεX]`. Conclude with `⟨hunit.unit, rfl⟩`.
-/
theorem associated_psEval {φ : PowerSeries 𝒪[K]} (h0 : PowerSeries.constantCoeff φ = 0)
    (h1 : IsUnit (PowerSeries.coeff 1 φ)) (a : 𝒪[L]) (ha : a ∈ 𝓂[L]) :
    Associated a ⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ := by
  let _ : UniformSpace L := IsTopologicalAddGroup.rightUniformSpace L
  have _ : IsUniformAddGroup L := isUniformAddGroup_of_addCommGroup
  let _ : UniformSpace 𝒪[K] := ⊥
  have _ : DiscreteUniformity 𝒪[K] := ⟨rfl⟩
  have hφc : Continuous[(⊥ : UniformSpace 𝒪[K]).toTopologicalSpace, _]
      (algebraMap 𝒪[K] 𝒪[L]) := by
    rw [UniformSpace.toTopologicalSpace_bot]
    exact continuous_bot
  have hev := hasEval_of_mem_maximalIdeal (a := fun _ : Unit => a) fun _ => ha
  set ε := MvPowerSeries.eval₂Hom hφc hev
  have hval : (⟨psEval φ (fun _ => (a : L)), psEval_mem_integer φ (fun _ => a) fun _ => ha⟩ : 𝒪[L])
      = ε φ := by
    apply Subtype.ext
    rw [MvPowerSeries.coe_eval₂Hom]
    exact psEval_eq_eval₂ φ (fun _ => a) fun _ => ha
  have hεX : ε PowerSeries.X = a := by
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_X _ _ _
  have hεC : ∀ c : 𝒪[K], ε (PowerSeries.C c) = algebraMap 𝒪[K] 𝒪[L] c := by
    intro c
    rw [MvPowerSeries.coe_eval₂Hom]
    exact MvPowerSeries.eval₂_C _ _ _
  obtain ⟨ψ, hψ⟩ := PowerSeries.X_dvd_iff.mpr h0
  set c := PowerSeries.constantCoeff ψ
  have hc : c = PowerSeries.coeff 1 φ := by
    rw [hψ, PowerSeries.coeff_succ_X_mul, PowerSeries.coeff_zero_eq_constantCoeff_apply]
  obtain ⟨χ, hχ⟩ := PowerSeries.X_dvd_iff.mpr
    (show PowerSeries.constantCoeff (ψ - PowerSeries.C c) = 0 by simp [c])
  have hψ' : ψ = PowerSeries.C c + PowerSeries.X * χ := by
    rw [← hχ]
    ring
  have hunit : IsUnit (ε ψ) := by
    rw [hψ', map_add, map_mul, hεX, hεC]
    by_contra hnu
    have hm : algebraMap 𝒪[K] 𝒪[L] c + a * ε χ ∈ 𝓂[L] := (IsLocalRing.mem_maximalIdeal _).mpr hnu
    have hm' : algebraMap 𝒪[K] 𝒪[L] c ∈ 𝓂[L] := by
      have := Ideal.sub_mem _ hm (Ideal.mul_mem_right (ε χ) _ ha)
      rwa [add_sub_cancel_right] at this
    rw [hc] at hm'
    exact (IsLocalRing.mem_maximalIdeal _).mp hm' (h1.map _)
  rw [hval, hψ, map_mul, hεX]
  exact ⟨hunit.unit, rfl⟩

end Associated

section Torsion

variable {K : Type*} [Field K] [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K]
variable {Ω : Type*} [Field Ω] [ValuativeRel Ω] [TopologicalSpace Ω] [IsValuativeTopology Ω]
  [Algebra K Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω]
variable {π : 𝒪[K]} (hπ : Irreducible π) {f g : PowerSeries 𝒪[K]}

/- English proof (translation)
The claim follows from `Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π h)`.
-/
theorem lubinTateTorsion_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateTorsion Ω (hπ := hπ) hf m ≤ lubinTateTorsion Ω (hπ := hπ) hf n :=
  Submodule.torsionBy_le_torsionBy_of_dvd _ _ (pow_dvd_pow π h)

/- English proof (translation)
Rewrite using `[lubinTateField, adjoin_le_iff]`. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Conclude with `val_mem_lubinTateField hπ hf (lubinTateTorsion_mono hπ hf h hx)`.
-/
theorem lubinTateField_mono (hf : IsLubinTateSeries π f) {m n : ℕ} (h : m ≤ n) :
    lubinTateField Ω hπ hf m ≤ lubinTateField Ω hπ hf n := by
  rw [lubinTateField, adjoin_le_iff]
  rintro _ ⟨x, hx, rfl⟩
  exact val_mem_lubinTateField hπ hf (lubinTateTorsion_mono hπ hf h hx)

/- English proof (translation)
The claim follows from `lubinTateField_mono hπ hf n.le_succ`.
-/
theorem lubinTateField_le_succ (hf : IsLubinTateSeries π f) (n : ℕ) :
    lubinTateField Ω hπ hf n ≤ lubinTateField Ω hπ hf (n + 1) :=
  lubinTateField_mono hπ hf n.le_succ

/- English proof (translation)
Rewrite using `[lubinTatePointEquiv_mem_torsion_iff, lubinTatePointEquiv_mem_torsion_iff]`.
-/
theorem lubinTatePointEquiv_primitive_iff (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    (n : ℕ) (x : IdealPoint Ω (lubinTateFormalGroup hπ hg)) :
    (lubinTatePointEquiv hf hg x ∈ lubinTateTorsion Ω hf n ∧
        lubinTatePointEquiv hf hg x ∉ lubinTateTorsion Ω hf (n - 1)) ↔
      (x ∈ lubinTateTorsion Ω hg n ∧ x ∉ lubinTateTorsion Ω hg (n - 1)) := by
  rw [lubinTatePointEquiv_mem_torsion_iff, lubinTatePointEquiv_mem_torsion_iff]

/- English proof (translation)
The claim follows from `aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl) fun h => hl' ((mem_lubinTateTorsion_ltPoly_iff k l).mpr h)`.
-/
theorem aeval_ltEisenstein_of_primitive {k : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (k + 1))
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) k) :
    aeval l.val ((ltEisenstein π k).map (algebraMap 𝒪[K] K)) = 0 :=
  aeval_ltEisenstein_eq_zero ((mem_lubinTateTorsion_ltPoly_iff _ l).mp hl)
    fun h => hl' ((mem_lubinTateTorsion_ltPoly_iff k l).mpr h)

omit [ValuativeRel K] [TopologicalSpace K] [IsNonarchimedeanLocalField K] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] [Algebra.IsAlgebraic K Ω] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨⟨⟨x, hxE⟩, ((valuation_coe_lt_one_iff E ⟨x, hxE⟩).mp hx).le⟩, rfl⟩`.
-/
theorem exists_integer_eq {E : IntermediateField K Ω} {x : Ω} (hxE : x ∈ E)
    (hx : valuation Ω x < 1) : ∃ y : 𝒪[E], ((y : E) : Ω) = x :=
  ⟨⟨⟨x, hxE⟩, ((valuation_coe_lt_one_iff E ⟨x, hxE⟩).mp hx).le⟩, rfl⟩

omit [TopologicalSpace K] [IsNonarchimedeanLocalField K] [ValuativeRel Ω] [TopologicalSpace Ω]
  [IsValuativeTopology Ω] [ValuativeExtension K Ω] in

/- English proof (translation)
Substitute `hE` using the available equality. Establish `hint : IsIntegral K a` using `(Algebra.IsAlgebraic.isAlgebraic a).isIntegral`. Establish `hqm : (p.map (algebraMap 𝒪[K] K)).Monic` using `hpm.map _`. Establish `hmin : minpoly K a = p.map (algebraMap 𝒪[K] K)`. Use `(Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm (minpoly.dvd K a hp) ?_).symm` and prove the remaining obligations.

Rewrite using `[← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective (FaithfulSMul.algebraMap_injective 𝒪[K] K)]`. Use `set pb := adjoin.powerBasis hint`. Establish `hgen : (⟨a, ha⟩ : K⟮a⟯) = pb.gen`. Rewrite using `[adjoin.powerBasis_gen]`. Both sides reduce to the same expression.

Establish `hdim : pb.dim = Module.finrank K K⟮a⟯`. Rewrite using `[adjoin.powerBasis_dim, adjoin.finrank hint]`. Establish `hnorm : Algebra.norm K pb.gen = (-1) ^ Module.finrank K K⟮a⟯ * ((p.coeff 0 : 𝒪[K]) : K)`. Rewrite using `[Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen, minpoly_gen, hmin, coeff_map]`. Both sides reduce to the same expression.

Rewrite using `[hgen]`. Establish `h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1)` using `by simp`. Rewrite using `[neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap, hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]`.
-/
theorem norm_neg_eq_coeff_zero {E : IntermediateField K Ω} {a : Ω} (hE : E = K⟮a⟯) (ha : a ∈ E)
    {p : 𝒪[K][X]} (hpm : p.Monic) (hfin : Module.finrank K E = p.natDegree)
    (hp : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) :
    Algebra.norm K (-(⟨a, ha⟩ : E)) = ((p.coeff 0 : 𝒪[K]) : K) := by
  subst hE
  have hint : IsIntegral K a := (Algebra.IsAlgebraic.isAlgebraic a).isIntegral
  have hqm : (p.map (algebraMap 𝒪[K] K)).Monic := hpm.map _
  have hmin : minpoly K a = p.map (algebraMap 𝒪[K] K) := by
    refine (Polynomial.eq_of_monic_of_dvd_of_natDegree_le (minpoly.monic hint) hqm
      (minpoly.dvd K a hp) ?_).symm
    rw [← adjoin.finrank hint, hfin, natDegree_map_eq_of_injective
      (FaithfulSMul.algebraMap_injective 𝒪[K] K)]
  set pb := adjoin.powerBasis hint
  have hgen : (⟨a, ha⟩ : K⟮a⟯) = pb.gen := by
    rw [adjoin.powerBasis_gen]
    rfl
  have hdim : pb.dim = Module.finrank K K⟮a⟯ := by
    rw [adjoin.powerBasis_dim, adjoin.finrank hint]
  have hnorm : Algebra.norm K pb.gen =
      (-1) ^ Module.finrank K K⟮a⟯ * ((p.coeff 0 : 𝒪[K]) : K) := by
    rw [Algebra.PowerBasis.norm_gen_eq_coeff_zero_minpoly, hdim, adjoin.powerBasis_gen,
      minpoly_gen, hmin, coeff_map]
    rfl
  rw [hgen]
  have h1 : (-1 : K⟮a⟯) = algebraMap K K⟮a⟯ (-1) := by simp
  rw [neg_eq_neg_one_mul, h1, map_mul, Algebra.norm_algebraMap,
    hnorm, ← mul_assoc, ← mul_pow, neg_one_mul, neg_neg, one_pow, one_mul]

/- English proof (translation)
Establish `haE : a ∈ E` using `hx ▸ (x : E).2`. Use `set α : E := ⟨a, haE⟩`. Establish `hgen : K⟮α⟯ = ⊤` using `adjoin_simple_eq_top_of_eq hE`. Establish `hα : aeval α p = 0`. Use `Subtype.val_injective ?_` and prove the remaining obligations.

Establish `h2` using `aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α p`. Simplify using `only [AlgHom.coe_restrictScalars', coe_val] at h2`. Rewrite using `[ZeroMemClass.coe_zero, ← h2]`. Express the relevant statement in the definitionally equal form `aeval a p = 0`. Rewrite using `[← aeval_map_algebraMap K]` and apply the resulting hypothesis.

Use `irreducible_of_isEisensteinAt_root hp hn hα hgen` as an intermediate fact. Use `this` and compare the differences between its conclusion and the goal. Conclude with `Subtype.ext hx`.
-/
theorem irreducible_of_eq_adjoin_of_isEisensteinAt {E : IntermediateField K Ω} [FiniteDimensional K E]
    {a : Ω} (hE : E = K⟮a⟯) {p : 𝒪[K][X]} (hp : p.IsEisensteinAt (IsLocalRing.maximalIdeal 𝒪[K]))
    (hn : 0 < p.natDegree) (ha : aeval a (p.map (algebraMap 𝒪[K] K)) = 0) {x : 𝒪[E]}
    (hx : ((x : E) : Ω) = a) : Irreducible x := by
  have haE : a ∈ E := hx ▸ (x : E).2
  set α : E := ⟨a, haE⟩
  have hgen : K⟮α⟯ = ⊤ := adjoin_simple_eq_top_of_eq hE
  have hα : aeval α p = 0 := by
    refine Subtype.val_injective ?_
    have h2 := aeval_algHom_apply (E.val.restrictScalars 𝒪[K]) α p
    simp only [AlgHom.coe_restrictScalars', coe_val] at h2
    rw [ZeroMemClass.coe_zero, ← h2]
    change aeval a p = 0
    rwa [← aeval_map_algebraMap K]
  have := irreducible_of_isEisensteinAt_root hp hn hα hgen
  convert this
  exact Subtype.ext hx

variable [IsSepClosed Ω]

/- English proof (translation)
The claim follows from `lubinTateField_eq (Ω := Ω) hπ hg hf n ▸ val_mem_lubinTateField hπ hg hx`.
-/
theorem val_mem_lubinTateField_of_mem (hf : IsLubinTateSeries π f) (hg : IsLubinTateSeries π g)
    {n : ℕ} {x : IdealPoint Ω (lubinTateFormalGroup hπ hg)} (hx : x ∈ lubinTateTorsion Ω hg n) :
    x.val ∈ lubinTateField Ω hπ hf n :=
  lubinTateField_eq (Ω := Ω) hπ hg hf n ▸ val_mem_lubinTateField hπ hg hx

/- English proof (translation)
Take `⟨l₀, -, hann, hgen⟩` from `exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n`. Take `⟨b, rfl⟩` from `hgen l hl`. Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k, n = k + 1 := by`. Consider the cases of `n with`. Consider the case `zero => exact absurd hl hl'`.

Consider the case `succ k => exact ⟨k, rfl⟩`. Establish `hb : IsUnit b`. Assume the negation of the conclusion as `hb`. Apply `hl'` to reduce the goal to its premises. Establish `hmem` using `(IsLocalRing.mem_maximalIdeal b).mpr hb`.

Rewrite `hmem` using `[hπ.maximalIdeal_eq, Ideal.mem_span_singleton]`. Take `⟨c, rfl⟩` from `hmem`. Rewrite using `[Nat.add_sub_cancel, mem_lubinTateTorsion, smul_smul, (hann _).mpr]`. Conclude with `Ideal.mem_span_singleton.mpr ⟨c, by ring⟩`. Take `⟨u, rfl⟩` from `hb`.

Use `⟨fun a => ?_, fun m hm => ?_⟩` and prove the remaining obligations. Rewrite using `[smul_smul, hann]`. Conclude with `Ideal.mul_unit_mem_iff_mem _ u.isUnit`. Take `⟨a, rfl⟩` from `hgen m hm`. Conclude with `⟨a * ↑u⁻¹, by rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩`.
-/
theorem primitive_spec (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    (∀ a : 𝒪[K], a • l = 0 ↔ a ∈ Ideal.span {π ^ n}) ∧
      ∀ m ∈ lubinTateTorsion Ω (hπ := hπ) hf n, ∃ a : 𝒪[K], a • l = m := by
  obtain ⟨l₀, -, hann, hgen⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  obtain ⟨b, rfl⟩ := hgen l hl
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  have hb : IsUnit b := by
    by_contra hb
    apply hl'
    have hmem := (IsLocalRing.mem_maximalIdeal b).mpr hb
    rw [hπ.maximalIdeal_eq, Ideal.mem_span_singleton] at hmem
    obtain ⟨c, rfl⟩ := hmem
    rw [Nat.add_sub_cancel, mem_lubinTateTorsion, smul_smul, (hann _).mpr]
    exact Ideal.mem_span_singleton.mpr ⟨c, by ring⟩
  obtain ⟨u, rfl⟩ := hb
  refine ⟨fun a => ?_, fun m hm => ?_⟩
  · rw [smul_smul, hann]
    exact Ideal.mul_unit_mem_iff_mem _ u.isUnit
  · obtain ⟨a, rfl⟩ := hgen m hm
    exact ⟨a * ↑u⁻¹, by rw [smul_smul, mul_assoc, Units.inv_mul, mul_one]⟩

/- English proof (translation)
Take `⟨l, hl, hann, -⟩` from `exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n`. Use `⟨l, hl, fun h => ?_⟩` and prove the remaining obligations. Rewrite `h` using `[mem_lubinTateTorsion, hann, Ideal.mem_span_singleton, pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit]`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_primitive (hf : IsLubinTateSeries π f) {n : ℕ} (hn : 0 < n) :
    ∃ l ∈ lubinTateTorsion Ω (hπ := hπ) hf n, l ∉ lubinTateTorsion Ω (hπ := hπ) hf (n - 1) := by
  obtain ⟨l, hl, hann, -⟩ := exists_generator_lubinTateTorsion (Ω := Ω) (hπ := hπ) hf n
  refine ⟨l, hl, fun h => ?_⟩
  rw [mem_lubinTateTorsion, hann, Ideal.mem_span_singleton,
    pow_dvd_pow_iff hπ.ne_zero hπ.not_isUnit] at h
  omega

/- English proof (translation)
Take `⟨-, hgen⟩` from `primitive_spec hπ hf hl hl'`. Use `le_antisymm ?_ ?_` and prove the remaining obligations. Rewrite using `[lubinTateField, adjoin_le_iff]`. Introduce and unpack `_ ⟨m, hm, rfl⟩`. Take `⟨a, rfl⟩` from `hgen m hm`.

Rewrite using `[lubinTate_smul_val]`. Conclude with `psEval_mem_adjoin_simple _ l.valuation_lt_one`. Rewrite using `[adjoin_simple_le_iff]`. Conclude with `val_mem_lubinTateField hπ hf hl`.
-/
theorem lubinTateField_eq_adjoin_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1)) :
    lubinTateField Ω hπ hf n = K⟮l.val⟯ := by
  obtain ⟨-, hgen⟩ := primitive_spec hπ hf hl hl'
  refine le_antisymm ?_ ?_
  · rw [lubinTateField, adjoin_le_iff]
    rintro _ ⟨m, hm, rfl⟩
    obtain ⟨a, rfl⟩ := hgen m hm
    rw [lubinTate_smul_val]
    exact psEval_mem_adjoin_simple _ l.valuation_lt_one
  · rw [adjoin_simple_le_iff]
    exact val_mem_lubinTateField hπ hf hl

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k, n = k + 1 := by`. Consider the cases of `n with`. Consider the case `zero => exact absurd hl hl'`. Consider the case `succ k => exact ⟨k, rfl⟩`. Rewrite `hl'` using `[Nat.add_sub_cancel]`.

Establish `hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯` using `(lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))`. Establish `hq` using `one_lt_card_residueField' K`. Establish `hdeg : 0 < (ltEisenstein π k).natDegree`. Rewrite using `[(ltEisenstein_monic π k).2]`. Conclude with `Nat.mul_pos (by omega) (pow_pos (by omega) k)`.

Conclude with `irreducible_of_eq_adjoin_of_isEisensteinAt hE (isEisensteinAt_ltEisenstein hπ k) hdeg (aeval_ltEisenstein_of_primitive hπ hl hl') hx`.
-/
theorem irreducible_of_primitive_ltPoly (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  have hq := one_lt_card_residueField' K
  have hdeg : 0 < (ltEisenstein π k).natDegree := by
    rw [(ltEisenstein_monic π k).2]
    exact Nat.mul_pos (by omega) (pow_pos (by omega) k)
  exact irreducible_of_eq_adjoin_of_isEisensteinAt hE (isEisensteinAt_ltEisenstein hπ k) hdeg
    (aeval_ltEisenstein_of_primitive hπ hl hl') hx

/- English proof (translation)
Establish `hg₀ : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K])` using `isLubinTateSeries_ltPoly π`. Take `⟨m, rfl⟩` from `(lubinTatePointEquiv hf hg₀).surjective l`. Use `replace hl := (lubinTatePointEquiv_mem_torsion_iff hf hg₀ n m).mp hl`. Use `replace hl' := fun h => hl' ((lubinTatePointEquiv_mem_torsion_iff hf hg₀ (n - 1) m).mpr h)`. Establish `hmE : m.val ∈ lubinTateField Ω hπ hf n` using `val_mem_lubinTateField_of_mem hπ hf hg₀ hl`.

Take `⟨y, hy⟩` from `exists_integer_eq hmE m.valuation_lt_one`. Establish `hyirr : Irreducible y` using `irreducible_of_primitive_ltPoly hπ hf hl hl' hy`. Establish `hym : y ∈ 𝓂[lubinTateField Ω hπ hf n]` using `hyirr.not_isUnit`. Use `set φ := (lubinTateHom hπ hf hg₀ 1).toPowerSeries`. Establish `hassoc` using `associated_psEval (K := K) (L := lubinTateField Ω hπ hf n) (φ := φ) (lubinTateHom hπ hf hg₀ 1).constantCoeff_eq_zero' (by rw [coeff_one_lubinTateHom]; exact isUnit_one) y hym`.

Establish `hxe : x = ⟨_, psEval_mem_integer φ (fun _ => y) fun _ => hym⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[hx, lubinTatePointEquiv_val]`. Express the relevant statement in the definitionally equal form `psEval φ (fun _ => m.val) = ((psEval φ (fun _ => (y : lubinTateField Ω hπ hf n)) : lubinTateField Ω hπ hf n) : Ω)`.

Rewrite using `[← psEval_coe _ φ (fun _ => (y : lubinTateField Ω hπ hf n)) (fun _ => by rw [hy]; exact m.valuation_lt_one), hy]`. Rewrite using `[hxe]`. Conclude with `hassoc.irreducible hyirr`.
-/
theorem irreducible_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ hf)} (hl : l ∈ lubinTateTorsion Ω hf n)
    (hl' : l ∉ lubinTateTorsion Ω hf (n - 1))
    {x : 𝒪[lubinTateField Ω hπ hf n]} (hx : ((x : lubinTateField Ω hπ hf n) : Ω) = l.val) :
    Irreducible x := by
  have hg₀ : IsLubinTateSeries π (ltPoly π : PowerSeries 𝒪[K]) := isLubinTateSeries_ltPoly π
  obtain ⟨m, rfl⟩ := (lubinTatePointEquiv hf hg₀).surjective l
  replace hl := (lubinTatePointEquiv_mem_torsion_iff hf hg₀ n m).mp hl
  replace hl' := fun h => hl' ((lubinTatePointEquiv_mem_torsion_iff hf hg₀ (n - 1) m).mpr h)
  have hmE : m.val ∈ lubinTateField Ω hπ hf n := val_mem_lubinTateField_of_mem hπ hf hg₀ hl
  obtain ⟨y, hy⟩ := exists_integer_eq hmE m.valuation_lt_one
  have hyirr : Irreducible y := irreducible_of_primitive_ltPoly hπ hf hl hl' hy
  have hym : y ∈ 𝓂[lubinTateField Ω hπ hf n] := hyirr.not_isUnit
  set φ := (lubinTateHom hπ hf hg₀ 1).toPowerSeries
  have hassoc := associated_psEval (K := K) (L := lubinTateField Ω hπ hf n) (φ := φ)
    (lubinTateHom hπ hf hg₀ 1).constantCoeff_eq_zero'
    (by rw [coeff_one_lubinTateHom]; exact isUnit_one) y hym
  have hxe : x = ⟨_, psEval_mem_integer φ (fun _ => y) fun _ => hym⟩ := by
    apply Subtype.ext
    apply Subtype.ext
    rw [hx, lubinTatePointEquiv_val]
    change psEval φ (fun _ => m.val) =
      ((psEval φ (fun _ => (y : lubinTateField Ω hπ hf n)) : lubinTateField Ω hπ hf n) : Ω)
    rw [← psEval_coe _ φ (fun _ => (y : lubinTateField Ω hπ hf n)) (fun _ => by rw [hy]; exact m.valuation_lt_one), hy]
  rw [hxe]
  exact hassoc.irreducible hyirr

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨k, rfl⟩ : ∃ k, n = k + 1 := by`. Consider the cases of `n with`. Consider the case `zero => exact absurd hl hl'`. Consider the case `succ k => exact ⟨k, rfl⟩`. Rewrite `hl'` using `[Nat.add_sub_cancel]`.

Establish `hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯` using `(lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))`. Rewrite using `[norm_neg_eq_coeff_zero hE _ (ltEisenstein_monic π k).1 ?_ (aeval_ltEisenstein_of_primitive hπ hl hl'), coeff_zero_ltEisenstein]`. Rewrite using `[(finrank_and_ramificationIndex_lubinTateField_succ hπ hf k).1, (ltEisenstein_monic π k).2]`.
-/
theorem norm_neg_eq_uniformizer_of_primitive (hf : IsLubinTateSeries π f) {n : ℕ}
    {l : IdealPoint Ω (lubinTateFormalGroup hπ (isLubinTateSeries_ltPoly π))}
    (hl : l ∈ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) n)
    (hl' : l ∉ lubinTateTorsion Ω (isLubinTateSeries_ltPoly π) (n - 1)) :
    Algebra.norm K (-(⟨l.val, val_mem_lubinTateField_of_mem hπ hf (isLubinTateSeries_ltPoly π) hl⟩ :
      lubinTateField Ω hπ hf n)) = (π : K) := by
  obtain ⟨k, rfl⟩ : ∃ k, n = k + 1 := by
    cases n with
    | zero => exact absurd hl hl'
    | succ k => exact ⟨k, rfl⟩
  rw [Nat.add_sub_cancel] at hl'
  have hE : lubinTateField Ω hπ hf (k + 1) = K⟮l.val⟯ :=
    (lubinTateField_eq hπ hf (isLubinTateSeries_ltPoly π) _).trans
      (lubinTateField_eq_adjoin_of_primitive hπ _ hl (by rwa [Nat.add_sub_cancel]))
  rw [norm_neg_eq_coeff_zero hE _ (ltEisenstein_monic π k).1 ?_
    (aeval_ltEisenstein_of_primitive hπ hl hl'), coeff_zero_ltEisenstein]
  rw [(finrank_and_ramificationIndex_lubinTateField_succ hπ hf k).1, (ltEisenstein_monic π k).2]

end Torsion

end FormalGroup

end GroundTheory.LocalField
