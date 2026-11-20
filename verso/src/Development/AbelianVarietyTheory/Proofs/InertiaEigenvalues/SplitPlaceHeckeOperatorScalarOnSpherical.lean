import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsWildInertiaCyclotomicElement
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.GaloisSideTwistedSelmerAuxiliaryPrimes
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SemisimpleOfInjective
import Formalism.LocalToGlobal.NormalizedHeckeFactors.CoverStd
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SphericalHeckeScalarOnSphericalVectors
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RankLeAleph0SmoothIrreducibleUnitaryAdelic
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FiniteDimensionalForms
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.ExistsIntegerUnitSplitPlaceConjugatePrime
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.CmFieldAdeleSplitPlaceSupportIntegral
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.UnitaryFiniteAdelesSplitPlaceDecompositionStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SplitPlaceDoubleCosetOperatorsCommuteSphericalStatement

open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.N Formalism.ConjugateSelfDual ReciprocityTheory.Gal ReciprocityTheory.Aut Formalism.AUTREP Formalism.L2 NumberField IsDedekindDomain Polynomial GlobalTheory.EtaJoin GlobalTheory.CoefDuty
open scoped TensorProduct

noncomputable section

namespace GlobalTheory.HeckeScalarSph

open GlobalTheory.SphLabelOps

variable {L : Type} [Field L] [NumberField L] [IsCMField L] {n : ℕ}

local notation3 "L⁺" => maximalRealSubfield L

/- English proof (translation)
Introduce `w hw`. Establish `: ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L))` using `rfl`. Rewrite using `[this, Matrix.map_mul, hx w hw, hy w hw, mul_one]`.
-/
theorem triv_mul {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x y : GAf L n} (hx : TrivOutside T x)
    (hy : TrivOutside T y) : TrivOutside T (x * y) := by
  intro w hw
  have : ((x * y).1 : Matrix (Fin n) (Fin n) (AL L)) = (x.1 : Matrix (Fin n) (Fin n) (AL L)) * (y.1 : Matrix (Fin n) (Fin n) (AL L)) := rfl
  rw [this, Matrix.map_mul, hx w hw, hy w hw, mul_one]

/- English proof (translation)
Introduce `w hw`. Establish `h1 : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1`. Rewrite using `[← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]`. Both sides reduce to the same expression. Establish `h2` using `congrArg (fun M => M.map (compAt L w)) h1`.

Simplify using `only [Matrix.map_mul, hx w hw, mul_one] at h2`. Rewrite using `[h2, Matrix.map_one _ (map_zero _) (map_one _)]`.
-/
theorem triv_inv {T : Set (HeightOneSpectrum (𝓞 L⁺))} {x : GAf L n} (hx : TrivOutside T x) :
    TrivOutside T x⁻¹ := by
  intro w hw
  have h1 : (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) * (x.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 := by
    rw [← Units.val_mul, ← Subgroup.coe_mul, inv_mul_cancel]
    rfl
  have h2 := congrArg (fun M => M.map (compAt L w)) h1
  simp only [Matrix.map_mul, hx w hw, mul_one] at h2
  rw [h2, Matrix.map_one _ (map_zero _) (map_one _)]

/- English proof (translation)
Introduce `w _`. Conclude with `Matrix.map_one _ (map_zero _) (map_one _)`.
-/
theorem triv_one {T : Set (HeightOneSpectrum (𝓞 L⁺))} : TrivOutside T (1 : GAf L n) := by
  intro w _
  exact Matrix.map_one _ (map_zero _) (map_one _)

def locK (n : ℕ) (v : HeightOneSpectrum (𝓞 L⁺)) : Subgroup (GAf L n) where
  carrier := {κ | κ ∈ Umax L n ∧ TrivOutside {v} κ}
  mul_mem' := fun ha hb => ⟨mul_mem ha.1 hb.1, triv_mul ha.2 hb.2⟩
  one_mem' := ⟨one_mem _, triv_one⟩
  inv_mem' := fun ha => ⟨inv_mem ha.1, triv_inv ha.2⟩

/- English proof (translation)
Take `⟨e, he, he'⟩` from `GlobalTheory.SplitSep.exists_sep L s`. Introduce `i j`. Establish `hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i`. Rewrite using `[GlobalTheory.FinTypCount.inv_val]`. Both sides reduce to the same expression.

Establish `hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L`. Apply `GlobalTheory.mem_ALint_of_supported_at_split L s e he he'` to reduce the goal to its premises. Introduce `w hw`. Use `congrFun (congrFun (hx w (by simpa using hw)) i) j` as an intermediate fact. Simplify using `only [Matrix.map_apply] at this`.

Rewrite using `[map_sub, this]`. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) = ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j` using `rfl`. Rewrite using `[map_sub, e1]`. Use `(Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)` and prove the remaining obligations.

Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`. Establish `e1 : s.proj ((((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) = ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i` using `rfl`. Rewrite using `[map_sub, map_sub, hconj, e1]`. Use `(Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij]`.

Use `add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by` as an intermediate fact. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])`. Simplify using `using this`.
-/
theorem mem_Umax_of_loc (s : SplitPlace L) (x : GAf L n) (hx : TrivOutside {s.v} x)
    (h1 : ∀ i j, Valued.v (((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1)
    (h2 : ∀ i j, Valued.v (((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j) ≤ 1) :
    x ∈ Umax L n := by
  obtain ⟨e, he, he'⟩ := GlobalTheory.SplitSep.exists_sep L s
  intro i j
  have hconj : conjAL L ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
      (((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i := by
    rw [GlobalTheory.FinTypCount.inv_val]
    rfl
  have hz : (x.1 : Matrix (Fin n) (Fin n) (AL L)) i j - (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L := by
    apply GlobalTheory.mem_ALint_of_supported_at_split L s e he he'
    · intro w hw
      have := congrFun (congrFun (hx w (by simpa using hw)) i) j
      simp only [Matrix.map_apply] at this
      rw [map_sub, this]
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((x.1 : Matrix (Fin n) (Fin n) (AL L)) i j) =
          ((s.loc n x : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) i j := rfl
      rw [map_sub, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h1 i j) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
    · have e1 : s.proj ((((x⁻¹ : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) j i) =
          ((s.loc n x⁻¹ : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) (s.v.adicCompletion L⁺)) j i := rfl
      rw [map_sub, map_sub, hconj, e1]
      refine (Valuation.map_sub _ _ _).trans (max_le (h2 j i) ?_)
      by_cases hij : i = j <;> simp [Matrix.one_apply, hij]
  have := add_mem hz (show (1 : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L by
    by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem])
  simpa using this

/- English proof (translation)
Use `⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, rfl⟩`. Conclude with `⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩`. Use `Matrix.map_injective O.subtype_injective ?_` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`. Conclude with `x.mul_inv`. Use `Matrix.map_injective O.subtype_injective ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]`.

Conclude with `x.inv_mul`.
-/
theorem mem_GLint_iff {F : Type} [Field F] {O : Subring F} {x : GL (Fin n) F} :
    x ∈ Formalism.UG.GLint (Fin n) O ↔ (∀ i j, x.1 i j ∈ O) ∧ ∀ i j, (x⁻¹).1 i j ∈ O := by
  refine ⟨?_, fun h => ⟨⟨Matrix.of fun i j => ⟨_, h.1 i j⟩, Matrix.of fun i j => ⟨_, h.2 i j⟩, ?_, ?_⟩, rfl⟩⟩
  · rintro ⟨y, rfl⟩
    exact ⟨fun i j => (y.1 i j).2, fun i j => ((y⁻¹).1 i j).2⟩
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.mul_inv
  · refine Matrix.map_injective O.subtype_injective ?_
    simp only
    rw [Matrix.map_mul, Matrix.map_one _ (map_zero _) (map_one _)]
    exact x.inv_mul

/- English proof (translation)
Establish `key : ALint L ≤ ((s.v.adicCompletionIntegers L⁺).toSubring).comap s.proj`. Rewrite using `[ALint, Subring.closure_le]`. Introduce and unpack `y (⟨o, rfl⟩ | ⟨a, ha, rfl⟩)`. Use `show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring`. Establish `e : s.proj ((o : L) ⊗ₜ[L⁺] (1 : AFplus L)) = s.i (o : L)`.

Simplify using `[SplitPlace.proj]`. Rewrite using `[e]`. Conclude with `s.split_le_one o`. Use `show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring`. Establish `e : s.proj ((1 : L) ⊗ₜ[L⁺] a) = a s.v`.

Simplify using `only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]`. Both sides reduce to the same expression. Rewrite using `[e]`. Conclude with `ha s.v`. Conclude with `key hz`.
-/
theorem proj_mem (s : SplitPlace L) {z : AL L} (hz : z ∈ ALint L) :
    s.proj z ∈ (s.v.adicCompletionIntegers L⁺).toSubring := by
  have key : ALint L ≤ ((s.v.adicCompletionIntegers L⁺).toSubring).comap s.proj := by
    rw [ALint, Subring.closure_le]
    rintro y (⟨o, rfl⟩ | ⟨a, ha, rfl⟩)
    · show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring
      have e : s.proj ((o : L) ⊗ₜ[L⁺] (1 : AFplus L)) = s.i (o : L) := by
        simp [SplitPlace.proj]
      rw [e]
      exact s.split_le_one o
    · show s.proj _ ∈ (s.v.adicCompletionIntegers L⁺).toSubring
      have e : s.proj ((1 : L) ⊗ₜ[L⁺] a) = a s.v := by
        simp only [SplitPlace.proj, AlgHom.toRingHom_eq_coe, RingHom.coe_coe, Algebra.TensorProduct.lift_tmul, map_one, one_mul]
        rfl
      rw [e]
      exact ha s.v
  exact key hz

/- English proof (translation)
Rewrite using `[mem_GLint_iff, ← map_inv]`. Conclude with `⟨fun h => mem_Umax_of_loc s x hx h.1 h.2, fun h => ⟨fun i j => proj_mem s (h i j), fun i j => proj_mem s (inv_mem h i j)⟩⟩`.
-/
theorem loc_mem_GLint_iff (s : SplitPlace L) {x : GAf L n} (hx : TrivOutside {s.v} x) :
    s.loc n x ∈ Formalism.UG.GLint (Fin n) (s.v.adicCompletionIntegers L⁺).toSubring ↔ x ∈ Umax L n := by
  rw [mem_GLint_iff, ← map_inv]
  exact ⟨fun h => mem_Umax_of_loc s x hx h.1 h.2,
    fun h => ⟨fun i j => proj_mem s (h i j), fun i j => proj_mem s (inv_mem h i j)⟩⟩

/- English proof (translation)
Take `⟨-, -, hlift⟩` from `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`. Establish `h0 : ϖ ≠ 0`. Introduce and unpack `rfl`. Establish `: Valued.v (0 : s.v.adicCompletion L⁺) = WithZero.exp (-1 : ℤ)` using `hϖ`. Rewrite `this` using `[map_zero]`.

Conclude with `WithZero.exp_ne_zero this.symm`. Establish `hdet : (Formalism.UG.diagJ n ϖ k).det ≠ 0`. Rewrite using `[Formalism.UG.diagJ, Matrix.det_diagonal]`. Conclude with `Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs; exacts [h0, one_ne_zero]`. Take `⟨α, ⟨hα, eα⟩, -⟩` from `hlift (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)`.

Establish `eα' : ((s.loc n α : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) = Formalism.UG.diagJ n ϖ k`. Rewrite using `[eα]`. Both sides reduce to the same expression. Use `⟨α, hα, fun x => ⟨?_, ?_⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨hx, a, ha, b, hb, e⟩`.

Take `⟨a', ⟨ha', rfl⟩, -⟩` from `hlift a`. Take `⟨b', ⟨hb', rfl⟩, -⟩` from `hlift b`. Use `⟨a', ⟨(loc_mem_GLint_iff s ha').1 ha, ha'⟩, b', ⟨(loc_mem_GLint_iff s hb').1 hb, hb'⟩, ?_⟩` and prove the remaining obligations. Use `(hlift (s.loc n x)).unique ⟨hx, rfl⟩ ⟨triv_mul (triv_mul ha' hα) hb', Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[e, map_mul, map_mul, Units.val_mul, Units.val_mul, eα']`.

Introduce and unpack `⟨a, ha, b, hb, rfl⟩`. Use `⟨triv_mul (triv_mul ha.2 hα) hb.2, _, (loc_mem_GLint_iff s ha.2).2 ha.1, _, (loc_mem_GLint_iff s hb.2).2 hb.1, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, Units.val_mul, Units.val_mul, eα']`.
-/
theorem exists_tSet_eq (s : SplitPlace L) (ϖ : s.v.adicCompletion L⁺) (k : ℕ) (hϖ : IsUnif L s.v ϖ) :
    ∃ α : GAf L n, TrivOutside {s.v} α ∧ ∀ x, x ∈ tSet L n s ϖ k ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * α * k₂ := by
  obtain ⟨-, -, hlift⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  have h0 : ϖ ≠ 0 := by
    rintro rfl
    have : Valued.v (0 : s.v.adicCompletion L⁺) = WithZero.exp (-1 : ℤ) := hϖ
    rw [map_zero] at this
    exact WithZero.exp_ne_zero this.symm
  have hdet : (Formalism.UG.diagJ n ϖ k).det ≠ 0 := by
    rw [Formalism.UG.diagJ, Matrix.det_diagonal]
    exact Finset.prod_ne_zero_iff.2 fun i _ => by split_ifs; exacts [h0, one_ne_zero]
  obtain ⟨α, ⟨hα, eα⟩, -⟩ := hlift (Matrix.GeneralLinearGroup.mkOfDetNeZero _ hdet)
  have eα' : ((s.loc n α : GL (Fin n) (s.v.adicCompletion L⁺)) : Matrix (Fin n) (Fin n) _) = Formalism.UG.diagJ n ϖ k := by
    rw [eα]; rfl
  refine ⟨α, hα, fun x => ⟨?_, ?_⟩⟩
  · rintro ⟨hx, a, ha, b, hb, e⟩
    obtain ⟨a', ⟨ha', rfl⟩, -⟩ := hlift a
    obtain ⟨b', ⟨hb', rfl⟩, -⟩ := hlift b
    refine ⟨a', ⟨(loc_mem_GLint_iff s ha').1 ha, ha'⟩, b', ⟨(loc_mem_GLint_iff s hb').1 hb, hb'⟩, ?_⟩
    refine (hlift (s.loc n x)).unique ⟨hx, rfl⟩ ⟨triv_mul (triv_mul ha' hα) hb', Units.ext ?_⟩
    rw [e, map_mul, map_mul, Units.val_mul, Units.val_mul, eα']
  · rintro ⟨a, ha, b, hb, rfl⟩
    refine ⟨triv_mul (triv_mul ha.2 hα) hb.2, _, (loc_mem_GLint_iff s ha.2).2 ha.1, _, (loc_mem_GLint_iff s hb.2).2 hb.1, ?_⟩
    rw [map_mul, map_mul, Units.val_mul, Units.val_mul, eα']

/- English proof (translation)
Take `⟨m, hm, h⟩` from `GlobalTheory.FinTypCount.exists_denom_matrix (a.1 : Matrix (Fin n) (Fin n) (AL L))`. Take `⟨m', hm', h'⟩` from `GlobalTheory.FinTypCount.exists_denom_matrix ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))`. Use `⟨m' * m, Nat.mul_pos hm' hm, fun κ hκ i j => ?_⟩` and prove the remaining obligations. Use `choose y hy ey using hκ.2`. Use `set A : Matrix (Fin n) (Fin n) (AL L) := (a.1 : Matrix (Fin n) (Fin n) (AL L))`.

Use `set B : Matrix (Fin n) (Fin n) (AL L) := ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))`. Establish `hBA : B * A = 1` using `Units.inv_mul a.1`. Establish `hκe : (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (m' : AL L) • (m : AL L) • Matrix.of y`. Use extensionality with `i j`. Simplify using `only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]`.

Use `ey i j` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Establish `e : (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) = 1 + ((m' : AL L) • B) * Matrix.of y * ((m : AL L) • A)`. Express the relevant statement in the definitionally equal form `B * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) * A = _`.

Rewrite using `[hκe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA]`. Simplify using `only [Matrix.mul_smul, Matrix.smul_mul]`. Rewrite using `[smul_comm]`. Use `show (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L`. Rewrite using `[e, Matrix.add_apply]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]`. Simplify using `only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]`. Conclude with `sum_mem fun l _ => mul_mem (sum_mem fun l' _ => mul_mem (h' i l') (hy l' l)) (h l j)`.
-/
theorem exists_cong_conj (a : GAf L n) : ∃ N : ℕ, 0 < N ∧ ∀ κ, NG.Cong L n N κ → a⁻¹ * κ * a ∈ Umax L n := by
  obtain ⟨m, hm, h⟩ := GlobalTheory.FinTypCount.exists_denom_matrix (a.1 : Matrix (Fin n) (Fin n) (AL L))
  obtain ⟨m', hm', h'⟩ := GlobalTheory.FinTypCount.exists_denom_matrix ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))
  refine ⟨m' * m, Nat.mul_pos hm' hm, fun κ hκ i j => ?_⟩
  choose y hy ey using hκ.2
  set A : Matrix (Fin n) (Fin n) (AL L) := (a.1 : Matrix (Fin n) (Fin n) (AL L))
  set B : Matrix (Fin n) (Fin n) (AL L) := ((a⁻¹ : GAf L n).1 : Matrix (Fin n) (Fin n) (AL L))
  have hBA : B * A = 1 := Units.inv_mul a.1
  have hκe : (κ.1 : Matrix (Fin n) (Fin n) (AL L)) = 1 + (m' : AL L) • (m : AL L) • Matrix.of y := by
    ext i j
    simp only [Matrix.add_apply, Matrix.smul_apply, Matrix.of_apply, smul_eq_mul]
    have := ey i j
    push_cast at this
    linear_combination this
  have e : (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) =
      1 + ((m' : AL L) • B) * Matrix.of y * ((m : AL L) • A) := by
    change B * (κ.1 : Matrix (Fin n) (Fin n) (AL L)) * A = _
    rw [hκe, Matrix.mul_add, Matrix.add_mul, Matrix.mul_one, hBA]
    simp only [Matrix.mul_smul, Matrix.smul_mul]
    rw [smul_comm]
  show (((a⁻¹ * κ * a : GAf L n).1 : GL (Fin n) (AL L)) : Matrix (Fin n) (Fin n) (AL L)) i j ∈ ALint L
  rw [e, Matrix.add_apply]
  refine add_mem ?_ ?_
  · by_cases hij : i = j <;> simp [Matrix.one_apply, hij, Subring.one_mem, Subring.zero_mem]
  · simp only [Matrix.mul_apply, Matrix.smul_apply, smul_eq_mul, Matrix.of_apply]
    exact sum_mem fun l _ => mul_mem (sum_mem fun l' _ => mul_mem (h' i l') (hy l' l)) (h l j)

/- English proof (translation)
Establish `hc : ∀ c ∈ hD.toFinset, ∃ x ∈ D, (x : G ⧸ U) = c` using `fun c hc => by simpa using hc`. Use `choose! r hrD hr using hc`. Use `⟨hD.toFinset.image r, fun γ hγ => ?_, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hγ`. Conclude with `hrD c hc`.

Establish `hm : (x : G ⧸ U) ∈ hD.toFinset` using `hD.mem_toFinset.2 ⟨x, hx, rfl⟩`. Use `⟨r x, ⟨Finset.mem_image.2 ⟨_, hm, rfl⟩, QuotientGroup.eq.1 (hr _ hm)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `γ ⟨hγ, e⟩`. Take `⟨c, hc, rfl⟩` from `Finset.mem_image.1 hγ`. Establish `: c = (x : G ⧸ U)` using `(hr c hc).symm.trans (QuotientGroup.eq.2 e)`.

Rewrite using `[this]`.
-/
theorem exists_reps {G : Type} [Group G] (U : Subgroup G) (D : Set G) (hD : ((fun x : G => (x : G ⧸ U)) '' D).Finite) :
    ∃ R : Finset G, (∀ γ ∈ R, γ ∈ D) ∧ ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ U := by
  classical
  have hc : ∀ c ∈ hD.toFinset, ∃ x ∈ D, (x : G ⧸ U) = c := fun c hc => by simpa using hc
  choose! r hrD hr using hc
  refine ⟨hD.toFinset.image r, fun γ hγ => ?_, fun x hx => ?_⟩
  · obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    exact hrD c hc
  · have hm : (x : G ⧸ U) ∈ hD.toFinset := hD.mem_toFinset.2 ⟨x, hx, rfl⟩
    refine ⟨r x, ⟨Finset.mem_image.2 ⟨_, hm, rfl⟩, QuotientGroup.eq.1 (hr _ hm)⟩, ?_⟩
    rintro γ ⟨hγ, e⟩
    obtain ⟨c, hc, rfl⟩ := Finset.mem_image.1 hγ
    have : c = (x : G ⧸ U) := (hr c hc).symm.trans (QuotientGroup.eq.2 e)
    rw [this]

/- English proof (translation)
Take `⟨N, hN, h⟩` from `exists_cong_conj a`. Take `⟨J, hJ⟩` from `GlobalTheory.AlgFormsFin.exists_cover L n hN`. Use `((J.finite_toSet).image fun j : GAf L n => ((j * a : GAf L n) : GAf L n ⧸ Umax L n)).subset ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨k₁, h₁, k₂, h₂, rfl⟩, rfl⟩`. Take `⟨j, hj, κ, hκ, rfl⟩` from `hJ k₁ h₁.1`.

Use `⟨j, hj, QuotientGroup.eq.2 ?_⟩` and prove the remaining obligations. Use `mul_mem (h κ hκ) h₂.1` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use `group`.
-/
theorem finite_dc (v : HeightOneSpectrum (𝓞 L⁺)) (a : GAf L n) :
    ((fun x : GAf L n => (x : GAf L n ⧸ Umax L n)) '' {x | ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂}).Finite := by
  obtain ⟨N, hN, h⟩ := exists_cong_conj a
  obtain ⟨J, hJ⟩ := GlobalTheory.AlgFormsFin.exists_cover L n hN
  refine ((J.finite_toSet).image fun j : GAf L n => ((j * a : GAf L n) : GAf L n ⧸ Umax L n)).subset ?_
  rintro _ ⟨_, ⟨k₁, h₁, k₂, h₂, rfl⟩, rfl⟩
  obtain ⟨j, hj, κ, hκ, rfl⟩ := hJ k₁ h₁.1
  refine ⟨j, hj, QuotientGroup.eq.2 ?_⟩
  have := mul_mem (h κ hκ) h₂.1
  convert this using 1
  group

/- English proof (translation)
The claim follows from `exists_reps (Umax L n) _ (finite_dc v a)`.
-/
theorem exists_repsU (v : HeightOneSpectrum (𝓞 L⁺)) (a : GAf L n) : ∃ R : Finset (GAf L n),
    (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * a * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n :=
  exists_reps (Umax L n) _ (finite_dc v a)

/- English proof (translation)
Establish `tr : ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂) → TrivOutside {v} x`. Introduce and unpack `_ ⟨k₁, h₁, k₂, h₂, rfl⟩`. Conclude with `triv_mul (triv_mul h₁.2 ha) h₂.2`. Use `⟨h.1, fun x hx => ?_⟩` and prove the remaining obligations. Take `⟨γ, ⟨hγ, e⟩, hu⟩` from `h.2 x hx`.

Conclude with `⟨γ, ⟨hγ, e, triv_mul (triv_inv (tr γ (h.1 γ hγ))) (tr x hx)⟩, fun δ hδ => hu δ ⟨hδ.1, hδ.2.1⟩⟩`.
-/
theorem reps_of_repsU {v : HeightOneSpectrum (𝓞 L⁺)} {a : GAf L n} (ha : TrivOutside {v} a) {R : Finset (GAf L n)}
    (h : (∀ γ ∈ R, ∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, γ = k₁ * a * k₂) ∧
      ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂) → ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n) :
    Reps (locK n v) a R := by
  have tr : ∀ x, (∃ k₁ ∈ locK n v, ∃ k₂ ∈ locK n v, x = k₁ * a * k₂) → TrivOutside {v} x := by
    rintro _ ⟨k₁, h₁, k₂, h₂, rfl⟩
    exact triv_mul (triv_mul h₁.2 ha) h₂.2
  refine ⟨h.1, fun x hx => ?_⟩
  obtain ⟨γ, ⟨hγ, e⟩, hu⟩ := h.2 x hx
  exact ⟨γ, ⟨hγ, e, triv_mul (triv_inv (tr γ (h.1 γ hγ))) (tr x hx)⟩, fun δ hδ => hu δ ⟨hδ.1, hδ.2.1⟩⟩

variable {W : Type} [AddCommGroup W] [Module ℂ W]

def rtHom (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (W : Type) [AddCommGroup W] [Module ℂ W] :
    GAf L n →* Module.End ℂ (GAf L n → W) where
  toFun h := NG.rt L n h
  map_one' := LinearMap.ext fun f => funext fun g => congrArg f (mul_one g)
  map_mul' g h := LinearMap.ext fun f => funext fun x => congrArg f (mul_assoc x g h).symm

/- English proof (translation)
Use function extensionality and compare the values at `g`. Rewrite using `[Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ Umax L n)), Finset.sum_image]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations. Establish `hc : ∃ x ∈ D, (x : GAf L n ⧸ Umax L n) = γ` using `⟨γ, h1 γ hγ, rfl⟩`. Rewrite using `[dif_pos hc]`.

Establish `hu : γ⁻¹ * hc.choose ∈ Umax L n` using `QuotientGroup.eq.1 hc.choose_spec.2.symm`. Use `congrFun (hf _ hu (triv_mul (triv_inv (hD γ (h1 γ hγ))) (hD _ hc.choose_spec.1))) (g * γ)` as an intermediate fact. Use `Eq.trans ?_ this` and prove the remaining obligations. Use `show f _ = f _`. Use `congr 1`.

Use `group`. Introduce `γ hγ δ hδ e`. Conclude with `(h2 δ (h1 δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩`. Introduce `c hc`. Distinguish the cases in `h : ∃ x ∈ D, (x : GAf L n ⧸ Umax L n) = c`.

Take `⟨x, hx, rfl⟩` from `h`. Take `⟨γ, ⟨hγ, e⟩, -⟩` from `h2 x hx`. Conclude with `Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 e⟩)`. Conclude with `absurd (dif_neg h) hc`.
-/
theorem heckeD_eq_sum {v : HeightOneSpectrum (𝓞 L⁺)} {D : Set (GAf L n)} (hD : ∀ x ∈ D, TrivOutside {v} x)
    {R : Finset (GAf L n)} (h1 : ∀ γ ∈ R, γ ∈ D) (h2 : ∀ x ∈ D, ∃! γ, γ ∈ R ∧ γ⁻¹ * x ∈ Umax L n)
    {f : GAf L n → W} (hf : ∀ κ ∈ Umax L n, TrivOutside {v} κ → NG.rt L n κ f = f) :
    NG.heckeD (Umax L n) D f = ∑ γ ∈ R, NG.rt L n γ f := by
  classical
  funext g
  rw [Finset.sum_apply, NG.heckeD, finsum_eq_sum_of_support_subset (s := R.image fun x : GAf L n => (x : GAf L n ⧸ Umax L n)),
    Finset.sum_image]
  · refine Finset.sum_congr rfl fun γ hγ => ?_
    have hc : ∃ x ∈ D, (x : GAf L n ⧸ Umax L n) = γ := ⟨γ, h1 γ hγ, rfl⟩
    rw [dif_pos hc]
    have hu : γ⁻¹ * hc.choose ∈ Umax L n := QuotientGroup.eq.1 hc.choose_spec.2.symm
    have := congrFun (hf _ hu (triv_mul (triv_inv (hD γ (h1 γ hγ))) (hD _ hc.choose_spec.1))) (g * γ)
    refine Eq.trans ?_ this
    show f _ = f _
    congr 1
    group
  · intro γ hγ δ hδ e
    exact (h2 δ (h1 δ hδ)).unique ⟨hγ, QuotientGroup.eq.1 e⟩ ⟨hδ, by rw [inv_mul_cancel]; exact one_mem _⟩
  · intro c hc
    by_cases h : ∃ x ∈ D, (x : GAf L n ⧸ Umax L n) = c
    · obtain ⟨x, hx, rfl⟩ := h
      obtain ⟨γ, ⟨hγ, e⟩, -⟩ := h2 x hx
      exact Finset.mem_coe.2 (Finset.mem_image.2 ⟨γ, hγ, QuotientGroup.eq.2 e⟩)
    · exact absurd (dif_neg h) hc

/- English proof (translation)
Use `haveI := GlobalTheory.FinTypCount.countable_field (L := L)`. Use `choose p _ hp2 hp3 using GlobalTheory.FinTypCount.exists_code (L := L) (n := n) N hN`. Set `Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → W)` to `fun q => if hq : ∃ g, p g = q then NG.rt L n hq.choose f else 0`. Establish `key : ∀ g, NG.rt L n g f = Ψ (p g)`. Introduce `g`.

Establish `hq : ∃ g', p g' = p g` using `⟨g, rfl⟩`. Simplify using `only [Ψ, dif_pos hq]`. Establish `e` using `hq.choose_spec`. Establish `h3` using `hp3 hq.choose`. Rewrite `h3` using `[e]`.

Establish `hc : NG.Cong L n N (g⁻¹ * hq.choose)` using `GlobalTheory.FinTypCount.cong_of_code (hp2 g) (hp3 g) h3`. Use function extensionality and compare the values at `x`. Use `(hf _ hc (x * g)).symm.trans ?_` and prove the remaining obligations. Use `show f _ = f _`. Use `congr 1`.

Use `group`. Use `(Set.countable_range Ψ).mono ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨p g, (key g).symm⟩`.
-/
theorem countable_range_rt {f : GAf L n → W} {N : ℕ} (hN : 0 < N)
    (hf : ∀ κ, NG.Cong L n N κ → ∀ g, f (g * κ) = f g) :
    (Set.range fun h : GAf L n => NG.rt L n h f).Countable := by
  classical
  haveI := GlobalTheory.FinTypCount.countable_field (L := L)
  choose p _ hp2 hp3 using GlobalTheory.FinTypCount.exists_code (L := L) (n := n) N hN
  let Ψ : ℕ × (Fin n → Fin n → L) → (GAf L n → W) := fun q =>
    if hq : ∃ g, p g = q then NG.rt L n hq.choose f else 0
  have key : ∀ g, NG.rt L n g f = Ψ (p g) := by
    intro g
    have hq : ∃ g', p g' = p g := ⟨g, rfl⟩
    simp only [Ψ, dif_pos hq]
    have e := hq.choose_spec
    have h3 := hp3 hq.choose
    rw [e] at h3
    have hc : NG.Cong L n N (g⁻¹ * hq.choose) := GlobalTheory.FinTypCount.cong_of_code (hp2 g) (hp3 g) h3
    funext x
    refine (hf _ hc (x * g)).symm.trans ?_
    show f _ = f _
    congr 1
    group
  refine (Set.countable_range Ψ).mono ?_
  rintro _ ⟨g, rfl⟩
  exact ⟨p g, (key g).symm⟩

/- English proof (translation)
Take `⟨f, hfS, hf0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hS.2.1`. Take `⟨-, N, hN, hfix⟩` from `hS.1.le hfS`. Set `T` to `Submodule.span ℂ (Set.range fun h : GAf L n => NG.rt L n h f)`. Establish `hle : T ≤ S`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations.

Introduce and unpack `_ ⟨h, rfl⟩`. Conclude with `hS.1.stable h f hfS`. Establish `hst : ∀ h, ∀ u ∈ T, NG.rt L n h u ∈ T`. Introduce `h u hu`. Proceed by induction on `hu using Submodule.span_induction with`.

Consider the case `mem x hx`. Take `⟨h', rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨h * h', funext fun x => congrArg f (mul_assoc x h h').symm⟩`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`.

Conclude with `add_mem ha hb`. Consider the case `smul c a _ ha => rw [map_smul]`. Conclude with `Submodule.smul_mem _ c ha`. Establish `hfT : f ∈ T` using `Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩`. Establish `hT : T = S`.

Break down `hS.2.2 T ⟨hle.trans hS.1.le, hst⟩ hle with h | h` into its components or cases. Conclude with `absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0`. Conclude with `h`. Rewrite using `[← hT]`. Conclude with `(rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))`.
-/
theorem rank_le {ρ : Representation ℂ (GQ L n) W} {S : Submodule ℂ (GAf L n → W)} (hS : NG.IsIrrRep ρ S) :
    Module.rank ℂ S ≤ Cardinal.aleph0 := by
  obtain ⟨f, hfS, hf0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hS.2.1
  obtain ⟨-, N, hN, hfix⟩ := hS.1.le hfS
  let T := Submodule.span ℂ (Set.range fun h : GAf L n => NG.rt L n h f)
  have hle : T ≤ S := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨h, rfl⟩
    exact hS.1.stable h f hfS
  have hst : ∀ h, ∀ u ∈ T, NG.rt L n h u ∈ T := by
    intro h u hu
    induction hu using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨h', rfl⟩ := hx
      exact Submodule.subset_span ⟨h * h', funext fun x => congrArg f (mul_assoc x h h').symm⟩
    | zero => simp
    | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
    | smul c a _ ha => rw [map_smul]; exact Submodule.smul_mem _ c ha
  have hfT : f ∈ T := Submodule.subset_span ⟨1, funext fun g => congrArg f (mul_one g)⟩
  have hT : T = S := by
    rcases hS.2.2 T ⟨hle.trans hS.1.le, hst⟩ hle with h | h
    · exact absurd ((Submodule.mem_bot ℂ).1 (h ▸ hfT)) hf0
    · exact h
  rw [← hT]
  exact (rank_span_le _).trans (Cardinal.le_aleph0_iff_set_countable.2 (countable_range_rt hN hfix))

/- English proof (translation)
Introduce `L _ _ _ n a S hS s ϖ k hϖ`. Take `⟨hdec, hcomm, -⟩` from `GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s`. Take `⟨α, hα, hset⟩` from `exists_tSet_eq (n := n) s ϖ k hϖ`. Use `choose R hR using exists_repsU (n := n) s.v`. Establish `hRα` using `reps_of_repsU hα (hR α)`.

Establish `hRtriv : ∀ γ ∈ R α, TrivOutside {s.v} γ` using `fun γ hγ => ((hset γ).2 ((hR α).1 γ hγ)).1`. Set `T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W)` to `∑ γ ∈ R α, rtHom L n a.W γ`. Establish `hT : ∀ x, T x = ∑ γ ∈ R α, rtHom L n a.W γ x` using `fun x => LinearMap.sum_apply _ _ _`. Establish `conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔ ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂` using `⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩, fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by`.

Use `GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v) {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y} (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩) (fun …` and prove the remaining obligations. Introduce `x hx`. Rewrite using `[hT]`. Use `⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sum]`.

Use `hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x) (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])` as an intermediate fact. Simplify `this` using `only [map_mul, Module.End.mul_apply]`. Introduce `b hb x _`. Rewrite using `[hT, hT, map_sum]`. Use `Finset.sum_congr rfl fun γ hγ => ?_` and prove the remaining obligations.

Rewrite using `[← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]`. Introduce `b hb x hx`. Rewrite using `[hT, hT]`. Conclude with `GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b (R α) (R b) hα hb (fun y hy => (hR α).2 y (conv.1 hy)) (fun γ hγ => conv.2 ((hR α).1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy)) (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)`. Use `⟨((s.q : ℂ) ^ (k * (n - 1)))⁻¹ * c, fun f hf hfix => ?_⟩` and prove the remaining obligations.

Establish `e` using `hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩`. Rewrite `e` using `[hT]`. Rewrite using `[NG.tN, heckeD_eq_sum (v := s.v) (R := R α) (fun x hx => hx.1) (fun γ hγ => (hset γ).2 ((hR α).1 γ hγ)) (fun x hx => (hR α).2 x ((hset x).1 hx)) hfix, mul_smul, ← e]`. Both sides reduce to the same expression.
-/
theorem tN_scalar : ∀ (L : Type) [Field L] [NumberField L] [IsCMField L] (n : ℕ) (a : NG.AlgWt L n) (S : Submodule ℂ (GAf L n → a.W)), NG.IsIrrRep a.ρ S → ∀ (s : SplitPlace L) (ϖ : s.v.adicCompletion (maximalRealSubfield L)) (k : ℕ), IsUnif L s.v ϖ → ∃ c : ℂ, ∀ f ∈ S, (∀ κ ∈ Umax L n, TrivOutside {s.v} κ → NG.rt L n κ f = f) → NG.tN (Umax L n) s ϖ k f = c • f := by
  intro L _ _ _ n a S hS s ϖ k hϖ
  classical
  obtain ⟨hdec, hcomm, -⟩ := GlobalTheory.T.unitaryFiniteAdeles_splitPlace_decomposition L n s
  obtain ⟨α, hα, hset⟩ := exists_tSet_eq (n := n) s ϖ k hϖ
  choose R hR using exists_repsU (n := n) s.v
  have hRα := reps_of_repsU hα (hR α)
  have hRtriv : ∀ γ ∈ R α, TrivOutside {s.v} γ := fun γ hγ => ((hset γ).2 ((hR α).1 γ hγ)).1
  let T : (GAf L n → a.W) →ₗ[ℂ] (GAf L n → a.W) := ∑ γ ∈ R α, rtHom L n a.W γ
  have hT : ∀ x, T x = ∑ γ ∈ R α, rtHom L n a.W γ x := fun x => LinearMap.sum_apply _ _ _
  have conv : ∀ {b x : GAf L n}, (∃ k₁ ∈ Umax L n, ∃ k₂ ∈ Umax L n, TrivOutside {s.v} k₁ ∧ TrivOutside {s.v} k₂ ∧ x = k₁ * b * k₂) ↔
      ∃ k₁ ∈ locK n s.v, ∃ k₂ ∈ locK n s.v, x = k₁ * b * k₂ :=
    ⟨fun ⟨k₁, h₁, k₂, h₂, t₁, t₂, e⟩ => ⟨k₁, ⟨h₁, t₁⟩, k₂, ⟨h₂, t₂⟩, e⟩,
      fun ⟨k₁, h₁, k₂, h₂, e⟩ => ⟨k₁, h₁.1, k₂, h₂.1, h₁.2, h₂.2, e⟩⟩
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ x ∈ GlobalTheory.SphScalar.fixS (rtHom L n a.W) S (locK n s.v), T x = c • x := by
    refine GlobalTheory.SphScalar.abs_scalar (rtHom L n a.W) S hS.1.stable
      (fun S' hle hst => hS.2.2 S' ⟨hle.trans hS.1.le, hst⟩ hle) (rank_le hS) (locK n s.v)
      {x | TrivOutside {s.v} x} {y | TrivOutside {s.v}ᶜ y}
      (fun g => by obtain ⟨x, y, hx, hy, e⟩ := hdec g; exact ⟨x, hx, y, hy, e⟩)
      (fun κ hκ b hb => (hcomm κ b hκ.2 hb).eq) R (fun b hb => reps_of_repsU hb (hR b)) T ?_ ?_ ?_
    · intro x hx
      rw [hT]
      refine ⟨S.sum_mem fun γ _ => hS.1.stable γ x hx.1, fun κ hκ => ?_⟩
      rw [map_sum]
      have := hRα.sum_eq hRα hκ (fun g => rtHom L n a.W g x)
        (fun y l hl => by rw [map_mul, Module.End.mul_apply, hx.2 l hl])
      simpa only [map_mul, Module.End.mul_apply] using this
    · intro b hb x _
      rw [hT, hT, map_sum]
      refine Finset.sum_congr rfl fun γ hγ => ?_
      rw [← Module.End.mul_apply, ← map_mul, ← Module.End.mul_apply, ← map_mul, (hcomm γ b (hRtriv γ hγ) hb).eq]
    · intro b hb x hx
      rw [hT, hT]
      exact GlobalTheory.T.splitPlace_doubleCosetOperators_commute_spherical L n a.W s α b (R α) (R b) hα hb (fun y hy => (hR α).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR α).1 γ hγ)) (fun y hy => (hR b).2 y (conv.1 hy))
        (fun γ hγ => conv.2 ((hR b).1 γ hγ)) x (fun κ h1 h2 => hx.2 κ ⟨h1, h2⟩)
  refine ⟨((s.q : ℂ) ^ (k * (n - 1)))⁻¹ * c, fun f hf hfix => ?_⟩
  have e := hc f ⟨hf, fun κ hκ => hfix κ hκ.1 hκ.2⟩
  rw [hT] at e
  rw [NG.tN, heckeD_eq_sum (v := s.v) (R := R α) (fun x hx => hx.1) (fun γ hγ => (hset γ).2 ((hR α).1 γ hγ))
    (fun x hx => (hR α).2 x ((hset x).1 hx)) hfix, mul_smul, ← e]
  rfl

end GlobalTheory.HeckeScalarSph

end
