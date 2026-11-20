import Mathlib
import CompanionTheory.SpectralGeometry.CountingDefinitions.AdelicEulerProducts.IsEulerProd
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityNearOne
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.LocalQuadraticDensityBoundNonzero
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.AdelicAnalysis.RankOneLocalDensityAlmostAll
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CardQuadricUnit
open HeckeCharacterZeroLocus.SiegelWeilU GlobalTheory.CompanionTheory.SW NumberField IsDedekindDomain MeasureTheory Topology
open scoped TensorProduct ENNReal NNReal Matrix

noncomputable section
namespace GlobalTheory.CompanionTheory.SW.UnitVal

open GlobalTheory.CompanionTheory.SW.LGPrim GlobalTheory.CompanionTheory.SW.GBall

/- English proof (translation)
The claim follows from `|N * (q⁻¹) ^ (2 * M - 1) - 1| ≤ 1 / q ^ M := by obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩ have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega have e2 : m + 1 - 1 = m := by omega rw [e1] at h ⊢ rw [e2] at h have hQ : q ^ (2 * m + 1) = q ^ (m + 1) * q ^ m := by rw [← pow_ …`.
-/
theorem real_bound_unit (q N : ℝ) (hq : 0 < q) (M : ℕ) (hM : 1 ≤ M)
    (h : |N - q ^ (2 * M - 1)| ≤ q ^ (M - 1)) :
    |N * (q⁻¹) ^ (2 * M - 1) - 1| ≤ 1 / q ^ M := by
  obtain ⟨m, rfl⟩ : ∃ m, M = m + 1 := ⟨M - 1, by omega⟩
  have e1 : 2 * (m + 1) - 1 = 2 * m + 1 := by omega
  have e2 : m + 1 - 1 = m := by omega
  rw [e1] at h ⊢
  rw [e2] at h
  have hQ : q ^ (2 * m + 1) = q ^ (m + 1) * q ^ m := by rw [← pow_add]; congr 1; omega
  have hQpos : 0 < q ^ (2 * m + 1) := by positivity
  have e3 : N * (q⁻¹) ^ (2 * m + 1) - 1 = (N - q ^ (2 * m + 1)) / q ^ (2 * m + 1) := by
    rw [inv_pow]; field_simp
  rw [e3, abs_div, abs_of_pos hQpos, div_le_iff₀ hQpos]
  have e4 : 1 / q ^ (m + 1) * q ^ (2 * m + 1) = q ^ m := by
    rw [hQ]
    have : q ^ (m + 1) ≠ 0 := by positivity
    field_simp
  rw [e4]
  exact h

variable {F : Type} [Field F] [NumberField F] {v : HeightOneSpectrum (𝓞 F)}

local notation "𝒪" => HeightOneSpectrum.adicCompletionIntegers F v
local notation "𝓴" => IsLocalRing.ResidueField (HeightOneSpectrum.adicCompletionIntegers F v)
local notation "res" => IsLocalRing.residue (HeightOneSpectrum.adicCompletionIntegers F v)

/- English proof (translation)
Establish `hs : s ∈ v.adicCompletionIntegers F` using `mem_int.2 hsu.le`. Establish `hLoc` using `GlobalTheory.T.completion_is_local_ring F v`. Use `haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1`. Use `haveI : BorelSpace (Fv F v) := ⟨rfl⟩`. Take `⟨-, -, -, hcard⟩` from `GlobalTheory.T.standard_local_haar_properties F v lam hlam`.

Establish `hq0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Use `haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)`. Use `letI : Fintype 𝓴 := Fintype.ofFinite _`.

Establish `hcardk : Fintype.card 𝓴 = Ideal.absNorm v.asIdeal`. Rewrite using `[← Nat.card_eq_fintype_card]`. Conclude with `hcard`. Take `⟨BO, rfl⟩ : ∃ BO : Matrix ι ι 𝒪, BO.map phi = B` from `⟨Matrix.of fun i j => ⟨B i j, hBint i j⟩, by ext i j; rfl⟩`. Establish `h20 : (2 : Fv F v) ≠ 0`.

Introduce `h0`. Rewrite `h2` using `[h0, map_zero]`. Conclude with `zero_ne_one h2`. Set `c : 𝒪` to `⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩`. Establish `hc : (c : Fv F v) = 2⁻¹` using `rfl`.

Establish `hc2 : c * 2 = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Establish `e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2` using `map_mul _ _ _`. Establish `e2 : (phi : 𝒪 →+* Fv F v) 2 = 2` using `map_ofNat _ 2`. Establish `e3 : phi c = (2 : Fv F v)⁻¹` using `hc`.

Rewrite `e` using `[e2, e3, inv_mul_cancel₀ h20]`. Conclude with `e`. Establish `hr1 : res c * 2 = 1`. Use `congrArg res hc2` as an intermediate fact. Rewrite `this` using `[map_mul, map_one, map_ofNat]`. Then use the resulting hypothesis.

Establish `hr : res c = 2⁻¹` using `eq_inv_of_mul_eq_one_left hr1`. Establish `hchar : ringChar 𝓴 ≠ 2`. Introduce `h`. Establish `h0 : (2 : 𝓴) = 0`. Use `ringChar.Nat.cast_ringChar (R := 𝓴)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `this` after adjusting the coercions. Rewrite `hr1` using `[h0, mul_zero]`. Conclude with `zero_ne_one hr1`. Establish `hBO : BO.IsSymm`.

Conclude with `Matrix.IsSymm.ext fun i j => Subtype.ext (congrFun (congrFun hBs i) j)`. Establish `hBks : (BO.map res).IsSymm` using `hBO.map _`. Establish `hBkdet : (BO.map res).det ≠ 0`. Introduce `h0`. Establish `e : res BO.det = (BO.map res).det` using `RingHom.map_det res BO`.

Rewrite `h0` using `[← e]`. Establish `h3` using `(res_eq_zero_iff _).1 h0`. Establish `e2 : ((BO.det : 𝒪) : Fv F v) = (BO.map phi).det` using `RingHom.map_det phi BO`. Rewrite `h3` using `[e2, hBdet]`. Conclude with `lt_irrefl _ h3`.

Use `set sb : 𝓴 := res (⟨s, hs⟩ : 𝒪) with hsb`. Establish `hsb0 : sb ≠ 0`. Introduce `h0`. Establish `h1` using `(res_eq_zero_iff (⟨s, hs⟩ : 𝒪)).1 h0`. Conclude with `absurd hsu (ne_of_lt h1)`.

Establish `hcount` using `GlobalTheory.CompanionTheory.SW.QuadricUnit.card_quadric_unit hchar M hM hM1 (BO.map res) hBks hBkdet hsb0`. Set `qk : (ι → 𝓴) → 𝓴` to `fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))`. Set `Fl : Finset (ι → 𝓴)` to `Finset.univ.filter fun y => qk y = sb`. Set `T : Finset (ι → 𝓴)` to `Fl.filter fun y => y ≠ 0`. Establish `hN : Nat.card {x : ι → 𝓴 // (2 : 𝓴)⁻¹ * (x ⬝ᵥ ((BO.map res) *ᵥ x)) = sb} = Fl.card` using `Nat.subtype_card Fl (fun x => by simp [Fl, qk])`.

Rewrite `hcount` using `[hN, hcardk]`. Establish `hTF : T = Fl`. Use `Finset.filter_true_of_mem fun y hy h0 => hsb0 ?_` and prove the remaining obligations. Rewrite `hy` using `[h0]`. Establish `h3` using `(Finset.mem_filter.1 hy).2`.

Rewrite using `[← h3]`. Simplify using `[qk]`. Establish `hqpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ)` using `by exact_mod_cast Nat.pos_of_ne_zero hq0`. Use `⟨(T.card : ℝ≥0) * ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ (2 * M - 1), ?_, fun A hA hAs => ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[hTF]`. Conclude with `real_bound_unit _ _ hqpos M hM1 hcount`. Use `set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf`. Establish `hQc : Continuous Qf`. Use `continuous_const.mul ?_` and prove the remaining obligations.

Conclude with `continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)`. Set `P : (ι → 𝓴) → Set (ι → Fv F v)` to `fun y => {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}`. Set `T0 : Finset (ι → 𝓴)` to `Finset.univ.filter fun y => y ≠ 0`. Establish `hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧ (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} = ⋃ y ∈ T0, P y`. Use extensionality with `x`.

Simplify using `only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h1, h3, h4⟩`. Take `⟨y, hy, h⟩` from `(cover x).1 ⟨h1, h3⟩`. Conclude with `⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩`.

Introduce and unpack `⟨y, hy, h, h4⟩`. Take `⟨h1, h3⟩` from `(cover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩`. Conclude with `⟨h1, h3, h4⟩`. Establish `hball : MeasurableSet {a : Fv F v | Valued.v a < 1}`. Establish `h` using `(Valued.isOpen_ball (Fv F v) 1).measurableSet`.

Simplify `h` using `[Valuation.restrict_lt_iff_lt_embedding]`. Establish `hmeas : ∀ y ∈ T0, MeasurableSet (P y)`. Introduce `y _`. Establish `e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A`. Use extensionality with `x`.

Simplify using `[P]`. Rewrite using `[e]`. Use `(MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)` and prove the remaining obligations. Conclude with `((continuous_apply i).sub continuous_const).measurable hball`. Establish `hdisj : Set.PairwiseDisjoint (↑T0) P`.

Introduce `y _ y' _ hne`. Conclude with `Set.disjoint_left.2 fun x hx hx' => hne (eq_of_close x y y' hx.1 hx'.1)`. Establish `hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) = if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (2 * M - 1)) * lam A else 0`. Introduce `y hy`. Establish `hy0 : y ≠ 0` using `(Finset.mem_filter.1 hy).2`.

Take `⟨hint, hprim⟩` from `(cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩`. Take `⟨a, haQ, har⟩` from `res_Q c hc hr BO y`. Establish `key` using `GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA`. Establish `hkey : (Measure.pi fun _ : ι => lam) (P y) = _` using `key`. Rewrite using `[hkey, hM]`.

Establish `hcl : Valued.v (s - Qf (lf y)) < 1 ↔ qk y = sb`. Use `res_eq_iff (⟨s, hs⟩ : 𝒪) a` as an intermediate fact. Rewrite `this` using `[har]`. Rewrite using `[show Qf (lf y) = (a : Fv F v) from haQ.symm]`. Conclude with `⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩`.

Use `split_ifs with he`. Establish `hlt` using `hcl.2 he`. Establish `: A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A`. Use `Set.inter_eq_left.2 fun z hz => ?_` and prove the remaining obligations. Establish `h5 : Valued.v (z - s) < 1` using `hAs hz`.

Establish `h6` using `Valuation.map_add_lt _ h5 hlt`. Establish `e : z - s + (s - Qf (lf y)) = z - Qf (lf y)` using `by ring`. Rewrite `h6` using `[e]`. Conclude with `h6`. Rewrite using `[this]`.

Establish `: A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅`. Use `Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)` and prove the remaining obligations. Establish `h5 : Valued.v (z - s) < 1` using `hAs hz.1`. Establish `h6 : Valued.v (z - Qf (lf y)) < 1` using `hz.2`. Establish `h7` using `Valuation.map_sub_lt _ h6 h5`.

Establish `e : z - Qf (lf y) - (z - s) = s - Qf (lf y)` using `by ring`. Rewrite `h7` using `[e]`. Conclude with `h7`. Rewrite using `[this, measure_empty, mul_zero]`. Rewrite using `[hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter, Finset.sum_const, nsmul_eq_mul]`.

Establish `hT : T0.filter (fun y => qk y = sb) = T`. Use extensionality with `y`. Simplify using `[T0, T, Fl, and_comm]`. Rewrite using `[hT]`. Establish `hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0` using `by exact_mod_cast hq0`.

Move the coercions through the operations in `[ENNReal.coe_inv hq0']`. Rewrite using `[mul_assoc]`.
-/
theorem core_unit (lam : Measure (Fv F v)) (hlam : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1)
    (ι : Type) [Fintype ι] [DecidableEq ι] (B : Matrix ι ι (Fv F v)) (hBs : B.IsSymm)
    (hBint : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hBdet : Valued.v B.det = 1)
    (M : ℕ) (hM : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v)
    (hsu : Valued.v s = 1) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < 1} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  classical
  have hs : s ∈ v.adicCompletionIntegers F := mem_int.2 hsu.le
  have hLoc := GlobalTheory.T.completion_is_local_ring F v
  haveI : SecondCountableTopology (Fv F v) := hLoc.2.2.1
  haveI : BorelSpace (Fv F v) := ⟨rfl⟩
  obtain ⟨-, -, -, hcard⟩ := GlobalTheory.T.standard_local_haar_properties F v lam hlam
  have hq0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  haveI : Finite 𝓴 := Nat.finite_of_card_ne_zero (by rw [hcard]; exact hq0)
  letI : Fintype 𝓴 := Fintype.ofFinite _
  have hcardk : Fintype.card 𝓴 = Ideal.absNorm v.asIdeal := by
    rw [← Nat.card_eq_fintype_card]; exact hcard
  obtain ⟨BO, rfl⟩ : ∃ BO : Matrix ι ι 𝒪, BO.map phi = B :=
    ⟨Matrix.of fun i j => ⟨B i j, hBint i j⟩, by ext i j; rfl⟩
  have h20 : (2 : Fv F v) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  let c : 𝒪 := ⟨2⁻¹, by show Valued.v ((2 : Fv F v)⁻¹) ≤ 1; rw [map_inv₀, h2, inv_one]⟩
  have hc : (c : Fv F v) = 2⁻¹ := rfl
  have hc2 : c * 2 = 1 := by
    apply Subtype.ext
    have e : (phi : 𝒪 →+* Fv F v) (c * 2) = phi c * phi 2 := map_mul _ _ _
    have e2 : (phi : 𝒪 →+* Fv F v) 2 = 2 := map_ofNat _ 2
    have e3 : phi c = (2 : Fv F v)⁻¹ := hc
    rw [e2, e3, inv_mul_cancel₀ h20] at e
    exact e
  have hr1 : res c * 2 = 1 := by
    have := congrArg res hc2
    rwa [map_mul, map_one, map_ofNat] at this
  have hr : res c = 2⁻¹ := eq_inv_of_mul_eq_one_left hr1
  have hchar : ringChar 𝓴 ≠ 2 := by
    intro h
    have h0 : (2 : 𝓴) = 0 := by
      have := ringChar.Nat.cast_ringChar (R := 𝓴)
      rw [h] at this
      exact_mod_cast this
    rw [h0, mul_zero] at hr1
    exact zero_ne_one hr1
  have hBO : BO.IsSymm := by
    exact Matrix.IsSymm.ext fun i j => Subtype.ext (congrFun (congrFun hBs i) j)
  have hBks : (BO.map res).IsSymm := hBO.map _
  have hBkdet : (BO.map res).det ≠ 0 := by
    intro h0
    have e : res BO.det = (BO.map res).det := RingHom.map_det res BO
    rw [← e] at h0
    have h3 := (res_eq_zero_iff _).1 h0
    have e2 : ((BO.det : 𝒪) : Fv F v) = (BO.map phi).det := RingHom.map_det phi BO
    rw [e2, hBdet] at h3
    exact lt_irrefl _ h3
  set sb : 𝓴 := res (⟨s, hs⟩ : 𝒪) with hsb
  have hsb0 : sb ≠ 0 := by
    intro h0
    have h1 := (res_eq_zero_iff (⟨s, hs⟩ : 𝒪)).1 h0
    exact absurd hsu (ne_of_lt h1)
  have hcount := GlobalTheory.CompanionTheory.SW.QuadricUnit.card_quadric_unit hchar M hM hM1 (BO.map res) hBks hBkdet hsb0
  let qk : (ι → 𝓴) → 𝓴 := fun y => (2 : 𝓴)⁻¹ * (y ⬝ᵥ ((BO.map res) *ᵥ y))
  let Fl : Finset (ι → 𝓴) := Finset.univ.filter fun y => qk y = sb
  let T : Finset (ι → 𝓴) := Fl.filter fun y => y ≠ 0
  have hN : Nat.card {x : ι → 𝓴 // (2 : 𝓴)⁻¹ * (x ⬝ᵥ ((BO.map res) *ᵥ x)) = sb} = Fl.card :=
    Nat.subtype_card Fl (fun x => by simp [Fl, qk])
  rw [hN, hcardk] at hcount
  have hTF : T = Fl := by
    refine Finset.filter_true_of_mem fun y hy h0 => hsb0 ?_
    rw [h0] at hy
    have h3 := (Finset.mem_filter.1 hy).2
    rw [← h3]
    simp [qk]
  have hqpos : (0 : ℝ) < (Ideal.absNorm v.asIdeal : ℝ) := by exact_mod_cast Nat.pos_of_ne_zero hq0
  refine ⟨(T.card : ℝ≥0) * ((Ideal.absNorm v.asIdeal : ℝ≥0)⁻¹) ^ (2 * M - 1), ?_, fun A hA hAs => ?_⟩
  · push_cast
    rw [hTF]
    exact real_bound_unit _ _ hqpos M hM1 hcount
  · set Qf : (ι → Fv F v) → Fv F v := fun x => (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) with hQf
    have hQc : Continuous Qf := by
      refine continuous_const.mul ?_
      exact continuous_id.dotProduct (continuous_const.matrix_mulVec continuous_id)
    let P : (ι → 𝓴) → Set (ι → Fv F v) := fun y =>
      {x | (∀ i, Valued.v (x i - lf y i) < 1) ∧ Qf x ∈ A}
    let T0 : Finset (ι → 𝓴) := Finset.univ.filter fun y => y ≠ 0
    have hS : {x : ι → Fv F v | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
        (∃ i, Valued.v (x i) = 1) ∧ (2 : Fv F v)⁻¹ * (x ⬝ᵥ ((BO.map phi) *ᵥ x)) ∈ A} =
        ⋃ y ∈ T0, P y := by
      ext x
      simp only [Set.mem_setOf_eq, Set.mem_iUnion, exists_prop]
      constructor
      · rintro ⟨h1, h3, h4⟩
        obtain ⟨y, hy, h⟩ := (cover x).1 ⟨h1, h3⟩
        exact ⟨y, Finset.mem_filter.2 ⟨Finset.mem_univ _, hy⟩, h, h4⟩
      · rintro ⟨y, hy, h, h4⟩
        obtain ⟨h1, h3⟩ := (cover x).2 ⟨y, (Finset.mem_filter.1 hy).2, h⟩
        exact ⟨h1, h3, h4⟩
    have hball : MeasurableSet {a : Fv F v | Valued.v a < 1} :=
      by
      have h := (Valued.isOpen_ball (Fv F v) 1).measurableSet
      simpa [Valuation.restrict_lt_iff_lt_embedding] using h
    have hmeas : ∀ y ∈ T0, MeasurableSet (P y) := by
      intro y _
      have e : P y = (⋂ i, (fun x : ι → Fv F v => x i - lf y i) ⁻¹' {a | Valued.v a < 1}) ∩ Qf ⁻¹' A := by
        ext x
        simp [P]
      rw [e]
      refine (MeasurableSet.iInter fun i => ?_).inter (hQc.measurable hA)
      exact ((continuous_apply i).sub continuous_const).measurable hball
    have hdisj : Set.PairwiseDisjoint (↑T0) P := by
      intro y _ y' _ hne
      exact Set.disjoint_left.2 fun x hx hx' => hne (eq_of_close x y y' hx.1 hx'.1)
    have hclass : ∀ y ∈ T0, (Measure.pi fun _ : ι => lam) (P y) =
        if qk y = sb then ((Ideal.absNorm v.asIdeal : ℝ≥0∞)⁻¹ ^ (2 * M - 1)) * lam A else 0 := by
      intro y hy
      have hy0 : y ≠ 0 := (Finset.mem_filter.1 hy).2
      obtain ⟨hint, hprim⟩ := (cover (lf y)).2 ⟨y, hy0, fun i => by simp⟩
      obtain ⟨a, haQ, har⟩ := res_Q c hc hr BO y
      have key := GlobalTheory.T.primitive_vector_quadratic_level_measure F v lam hlam h2 ι (BO.map phi) hBs hBint hBdet (lf y) hint hprim A hA
      have hkey : (Measure.pi fun _ : ι => lam) (P y) = _ := key
      rw [hkey, hM]
      have hcl : Valued.v (s - Qf (lf y)) < 1 ↔ qk y = sb := by
        have := res_eq_iff (⟨s, hs⟩ : 𝒪) a
        rw [har] at this
        rw [show Qf (lf y) = (a : Fv F v) from haQ.symm]
        exact ⟨fun h => (this.2 h).symm, fun h => this.1 h.symm⟩
      split_ifs with he
      · have hlt := hcl.2 he
        have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = A := by
          refine Set.inter_eq_left.2 fun z hz => ?_
          have h5 : Valued.v (z - s) < 1 := hAs hz
          have h6 := Valuation.map_add_lt _ h5 hlt
          have e : z - s + (s - Qf (lf y)) = z - Qf (lf y) := by ring
          rw [e] at h6
          exact h6
        rw [this]
      · have : A ∩ {s' | Valued.v (s' - (2 : Fv F v)⁻¹ * (lf y ⬝ᵥ ((BO.map phi) *ᵥ lf y))) < 1} = ∅ := by
          refine Set.eq_empty_iff_forall_notMem.2 fun z hz => he (hcl.1 ?_)
          have h5 : Valued.v (z - s) < 1 := hAs hz.1
          have h6 : Valued.v (z - Qf (lf y)) < 1 := hz.2
          have h7 := Valuation.map_sub_lt _ h6 h5
          have e : z - Qf (lf y) - (z - s) = s - Qf (lf y) := by ring
          rw [e] at h7
          exact h7
        rw [this, measure_empty, mul_zero]
    rw [hS, measure_biUnion_finset hdisj hmeas, Finset.sum_congr rfl hclass, ← Finset.sum_filter,
      Finset.sum_const, nsmul_eq_mul]
    have hT : T0.filter (fun y => qk y = sb) = T := by
      ext y
      simp [T0, T, Fl, and_comm]
    rw [hT]
    have hq0' : (Ideal.absNorm v.asIdeal : ℝ≥0) ≠ 0 := by exact_mod_cast hq0
    push_cast [ENNReal.coe_inv hq0']
    rw [mul_assoc]

/- English proof (translation)
Take `⟨D, hD, hprim⟩` from `core_unit lam hstd h2 ι B hsym hB hdet M hc hM1 s hsu`. Take `⟨π, hπ⟩` from `exists_unif v`. Use `⟨D, hD, fun A hA hsub => ?_⟩` and prove the remaining obligations. Establish `hball : A ⊆ {z | Valued.v (z - s) < 1}` using `fun z hz => by`. Establish `h3 : Valued.v (z - s) < Valued.v s` using `hsub hz`.

Rewrite `h3` using `[hsu]`. Conclude with `h3`. Rewrite using `[← hprim A hA hball]`. Use `congr 1`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hx, hQ⟩`. Use `⟨hx, ?_, hQ⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hnp`. Establish `h5` using `q_nonprim h2 hB hπ hx hnp`.

Establish `hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) - s) < Valued.v s` using `hsub hQ`. Establish `hv` using `Valuation.map_eq_of_sub_lt Valued.v hlt`. Rewrite `h5` using `[hv, hsu]`. Use `absurd h5 (not_le.2 ?_)` and prove the remaining obligations. Rewrite using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`.

Use linear arithmetic over natural numbers and integers. Introduce and unpack `⟨hx, -, hQ⟩`. Conclude with `⟨hx, hQ⟩`.
-/
theorem density_near_unit {ι : Type} [Fintype ι] [DecidableEq ι] {lam : Measure (Fv F v)}
    (hstd : IsStdV v lam) (h2 : Valued.v (2 : Fv F v) = 1) (B : Matrix ι ι (Fv F v))
    (hsym : B.IsSymm) (hB : ∀ i j, B i j ∈ v.adicCompletionIntegers F) (hdet : Valued.v B.det = 1)
    (M : ℕ) (hc : Fintype.card ι = 2 * M) (hM1 : 1 ≤ M) (s : Fv F v) (hsu : Valued.v s = 1) :
    ∃ D : ℝ≥0, |(D : ℝ) - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M ∧
      ∀ A : Set (Fv F v), MeasurableSet A → A ⊆ {z | Valued.v (z - s) < Valued.v s} →
        (Measure.pi fun _ : ι => lam) {x | (∀ i, x i ∈ v.adicCompletionIntegers F) ∧
          (2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) ∈ A} = (D : ℝ≥0∞) * lam A := by
  obtain ⟨D, hD, hprim⟩ := core_unit lam hstd h2 ι B hsym hB hdet M hc hM1 s hsu
  obtain ⟨π, hπ⟩ := exists_unif v
  refine ⟨D, hD, fun A hA hsub => ?_⟩
  have hball : A ⊆ {z | Valued.v (z - s) < 1} := fun z hz => by
    have h3 : Valued.v (z - s) < Valued.v s := hsub hz
    rw [hsu] at h3
    exact h3
  rw [← hprim A hA hball]
  congr 1
  ext x
  constructor
  · rintro ⟨hx, hQ⟩
    refine ⟨hx, ?_, hQ⟩
    by_contra hnp
    have h5 := q_nonprim h2 hB hπ hx hnp
    have hlt : Valued.v ((2 : Fv F v)⁻¹ * (x ⬝ᵥ (B *ᵥ x)) - s) < Valued.v s := hsub hQ
    have hv := Valuation.map_eq_of_sub_lt Valued.v hlt
    rw [hv, hsu] at h5
    refine absurd h5 (not_le.2 ?_)
    rw [← WithZero.exp_zero, WithZero.exp_lt_exp]
    omega
  · rintro ⟨hx, -, hQ⟩
    exact ⟨hx, hQ⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ h1 d b`. Take `⟨B, hBs, hBd, hBt⟩` from `GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM M J hJ d b`. Take `⟨-, hun⟩` from `GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b`. Establish `hd : d = 2`. Establish `h1` using `Module.finrank_eq_card_basis b`.

Rewrite `h1` using `[hCM.2.2.1, Fintype.card_fin]`. Conclude with `h1.symm`. Establish `hcard : Fintype.card (Fin M × Fin d) = 2 * M`. Rewrite using `[Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hd, mul_comm]`. Establish `hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F`.

Use `Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_` and prove the remaining obligations. Distinguish the cases in `h0 : B i j = 0`. Use `Filter.Eventually.of_forall fun v => ?_` and prove the remaining obligations. Rewrite using `[h0, map_zero]`. Conclude with `zero_mem _`.

Use `(hun _ h0).mono fun v hv => ?_` and prove the remaining obligations. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Conclude with `hv.le`. Use `filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent] with v hv2 hvd hve lam hlam m hm s hsu`. Establish `hv2' : Valued.v (2 : Fv F v) = 1` using `by rwa [map_ofNat] at hv2`.

Establish `hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1`. Establish `h1` using `(algebraMap F (Fv F v)).map_det B`. Rewrite `hvd` using `[h1]`. Conclude with `hvd`. Establish `hs0 : s ≠ 0`.

Introduce `h0`. Rewrite `hsu` using `[h0, map_zero]`. Conclude with `zero_ne_one hsu`. Take `⟨D, hD1, hD⟩` from `density_near_unit hlam hv2' (B.map (algebraMap F (Fv F v))) (hBs.map _) (fun i j => hve i j) hdet M hcard h1 s hsu`. Rewrite using `[GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM M J hJ d b v (B.map (algebraMap F (Fv F v))) (fun x y => hBt (Fv F v) x y) lam hlam m hm s hs0 D hD]`.

Conclude with `hD1`.
-/
theorem density_unit_lattice : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E), IsCMExt F E σ → ∀ (M : ℕ) (J : Matrix (Fin M) (Fin M) E), IsHermND σ J → 1 ≤ M → ∀ (d : ℕ) (b : Module.Basis (Fin d) F E), ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite, ∀ (lam : Measure (Fv F v)), IsStdV v lam → ∀ m, IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b lam 1 M) (coordHerm (Fv F v) σ b lam 1) m → ∀ s : Fv F v, Valued.v s = 1 → |(m (hermScal (Fv F v) σ s) (latV b v)).toReal - 1| ≤ 1 / (Ideal.absNorm v.asIdeal : ℝ) ^ M := by
  intro F E _ _ _ _ _ σ hCM M J hJ h1 d b
  classical
  obtain ⟨B, hBs, hBd, hBt⟩ := GlobalTheory.CompanionTheory.SW.trace_form_coords F E σ hCM M J hJ d b
  obtain ⟨-, hun⟩ := GlobalTheory.CompanionTheory.SW.GoodInt.rational_integral_units F E σ hCM d b
  have hd : d = 2 := by
    have h1 := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at h1
    exact h1.symm
  have hcard : Fintype.card (Fin M × Fin d) = 2 * M := by
    rw [Fintype.card_prod, Fintype.card_fin, Fintype.card_fin, hd, mul_comm]
  have hent : ∀ᶠ v : HeightOneSpectrum (𝓞 F) in Filter.cofinite,
      ∀ i j, algebraMap F (Fv F v) (B i j) ∈ v.adicCompletionIntegers F := by
    refine Filter.eventually_all.2 fun i => Filter.eventually_all.2 fun j => ?_
    by_cases h0 : B i j = 0
    · refine Filter.Eventually.of_forall fun v => ?_
      rw [h0, map_zero]
      exact zero_mem _
    · refine (hun _ h0).mono fun v hv => ?_
      rw [HeightOneSpectrum.mem_adicCompletionIntegers]
      exact hv.le
  filter_upwards [hun 2 two_ne_zero, hun _ hBd, hent] with v hv2 hvd hve lam hlam m hm s hsu
  have hv2' : Valued.v (2 : Fv F v) = 1 := by rwa [map_ofNat] at hv2
  have hdet : Valued.v (B.map (algebraMap F (Fv F v))).det = 1 := by
    have h1 := (algebraMap F (Fv F v)).map_det B
    rw [h1] at hvd
    exact hvd
  have hs0 : s ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hsu
    exact zero_ne_one hsu
  obtain ⟨D, hD1, hD⟩ := density_near_unit hlam hv2' (B.map (algebraMap F (Fv F v)))
    (hBs.map _) (fun i j => hve i j) hdet M hcard h1 s hsu
  rw [GlobalTheory.CompanionTheory.SW.LocGood.local_mass σ hCM M J hJ d b v (B.map (algebraMap F (Fv F v)))
    (fun x y => hBt (Fv F v) x y) lam hlam m hm s hs0 D hD]
  exact hD1

end GlobalTheory.CompanionTheory.SW.UnitVal
