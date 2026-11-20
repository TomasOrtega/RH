import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Formalism.PairingDivisors.StatementH
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IntegralDensEqZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.InducedTypeThetaGenusOnePermutes
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpaceSelfDualPairAtMostLine
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsIntegerMapEqHalfOneAddSqrt
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyInverseHalfDifferent
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsTraceDualFamilyHomLattice

open NumberField Classical Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum
open scoped BigOperators

noncomputable section

namespace GlobalTheory.ThetaInter

open Formalism.L2.Th1.H

def sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : Sesq (VC D N N') :=
  LinearMap.mk₂'ₛₗ (RingHom.id ℂ) (starRingEnd ℂ) (fun z w => Hf D T z w)
    (by intro a b c; simp only [Hf, Pi.add_apply, add_mul, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_assoc, ← Finset.mul_sum, mul_div_assoc])
    (by intro a b c; simp only [Hf, Pi.add_apply, map_add, mul_add, Finset.sum_add_distrib, add_div])
    (by
      intro c a b
      simp only [Hf, Pi.smul_apply, smul_eq_mul, map_mul, mul_left_comm _ (starRingEnd ℂ c), ← Finset.mul_sum,
        mul_div_assoc])

/- English proof (translation)
Introduce `x y`. Express the relevant statement in the definitionally equal form `Hf D T y x = starRingEnd ℂ (Hf D T x y)`. Simplify using `only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]`.
-/
theorem isHerm_sesqOf (D : D7) (T : Tor D) (N N' : ℕ) : IsHerm (sesqOf D T N N') := by
  intro x y
  change Hf D T y x = starRingEnd ℂ (Hf D T x y)
  simp only [Hf, map_div₀, map_sum, map_mul, Complex.conj_ofReal, Complex.conj_conj, mul_comm]

variable {D : D7} {cc : Ideal (𝓞 D.host.K)} {δ : ℂ} {N N' : ℕ}

/- English proof (translation)
Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨c, hc, rfl⟩` from `hw`. Use `AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩` and prove the remaining obligations. Use `push_cast`.

Rewrite using `[map_mul]`. Expand and normalize the polynomial expressions, which then agree. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [mul_add]`. Conclude with `AddSubgroup.add_mem _ ha hb`.

Consider the case `neg a _ ha => rw [mul_neg]`. Conclude with `AddSubgroup.neg_mem _ ha`.
-/
theorem lam_mul_mem (a : 𝓞 D.host.K) {w : ℂ} (hw : w ∈ lamOf D cc δ) :
    D.host.φ₀ (((a : D.host.K) : D.host.E)) * w ∈ lamOf D cc δ := by
  induction hw using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨c, hc, rfl⟩ := hw
    refine AddSubgroup.subset_closure ⟨a * c, cc.mul_mem_left a hc, ?_⟩
    push_cast
    rw [map_mul]
    ring
  | zero => simp
  | add a b _ _ ha hb => rw [mul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [mul_neg]; exact AddSubgroup.neg_mem _ ha

/- English proof (translation)
Break down `hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩` into its components or cases. Use `⟨Set.range b, hb.2, ?_⟩` and prove the remaining obligations. Unfold `LaB`. Use `congr 1`. Use extensionality with `z`.

Simplify using `[tor0]`. Use `⟨YYl D L L', ?_, rfl⟩` and prove the remaining obligations. Take `⟨r, y, y', hy, -, h⟩` from `GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'`. Rewrite using `[eq_top_iff]`. Introduce `x _`.

Rewrite using `[h x]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))`.
-/
theorem klat_gen {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    ∃ S : Set (Matrix (Fin N') (Fin N) D.host.E), Submodule.span D.host.K S = ⊤ ∧
      A = AddSubgroup.closure {z | ∃ w ∈ lamOf D cc δ, ∃ B ∈ S, z = w • embV D (tor0 D cc δ) B} := by
  rcases hA with ⟨r, b, hb, rfl⟩ | ⟨L, L', hL, hL', rfl⟩
  · refine ⟨Set.range b, hb.2, ?_⟩
    unfold LaB
    congr 1
    ext z
    simp [tor0]
  · refine ⟨YYl D L L', ?_, rfl⟩
    obtain ⟨r, y, y', hy, -, h⟩ := GlobalTheory.HomDual.exists_dual_family_hom D (GlobalTheory.exists_trace_dual_family_halfDifferent D) N N' L L' hL hL'
    rw [eq_top_iff]
    intro x _
    rw [h x]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span (hy i))

/- English proof (translation)
Take `⟨S, -, rfl⟩` from `klat_gen hA`. Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem w hw`. Take `⟨w, hw, B, hB, rfl⟩` from `hw`. Conclude with `AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩`.

Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [smul_add]`. Conclude with `AddSubgroup.add_mem _ ha hb`. Consider the case `neg a _ ha => rw [smul_neg]`. Conclude with `AddSubgroup.neg_mem _ ha`.
-/
theorem klat_smul_mem {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) (a : 𝓞 D.host.K)
    {x : VC D N N'} (hx : x ∈ A) : D.host.φ₀ (((a : D.host.K) : D.host.E)) • x ∈ A := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, hB, rfl⟩ := hw
    exact AddSubgroup.subset_closure ⟨_, lam_mul_mem a hw, B, hB, smul_smul _ _ _⟩
  | zero => simp
  | add a b _ _ ha hb => rw [smul_add]; exact AddSubgroup.add_mem _ ha hb
  | neg a _ ha => rw [smul_neg]; exact AddSubgroup.neg_mem _ ha

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Express the relevant statement in the definitionally equal form `embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)`. Rewrite using `[map_mul, h τ k]`.
-/
theorem embV_smul (h : GL3Theta.InducedCMType D) (k : D.host.K) (B : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (k • B) = D.host.φ₀ (k : D.host.E) • embV D (tor0 D cc δ) B := by
  funext τ i j
  change embT D τ ((k : D.host.E) * B i j) = D.host.φ₀ (k : D.host.E) * embT D τ (B i j)
  rw [map_mul, h τ k]

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Conclude with `map_add (embT D τ) _ _`.
-/
theorem embV_add (B B' : Matrix (Fin N') (Fin N) D.host.E) :
    embV D (tor0 D cc δ) (B + B') = embV D (tor0 D cc δ) B + embV D (tor0 D cc δ) B' := by
  funext τ i j
  exact map_add (embT D τ) _ _

/- English proof (translation)
Use function extensionality and compare the values at `τ i j`. Conclude with `map_zero (embT D τ)`.
-/
theorem embV_zero : embV D (tor0 D cc δ) (0 : Matrix (Fin N') (Fin N) D.host.E) = 0 := by
  funext τ i j
  exact map_zero (embT D τ)

/- English proof (translation)
Take `⟨S, -, rfl⟩` from `klat_gen hA`. Establish `hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E)`. Introduce `w hw`. Proceed by induction on `hw using AddSubgroup.closure_induction with`. Consider the case `mem w hw => obtain ⟨c, -, rfl⟩ := hw`.

Conclude with `⟨c, rfl⟩`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `add a b _ _ ha hb`. Take `⟨k, rfl⟩` from `ha`. Take `⟨k', rfl⟩` from `hb`.

Conclude with `⟨k + k', by simp [mul_add]⟩`. Consider the case `neg a _ ha`. Take `⟨k, rfl⟩` from `ha`. Conclude with `⟨-k, by simp⟩`. Proceed by induction on `hx using AddSubgroup.closure_induction with`.

Consider the case `mem w hw`. Take `⟨w, hw, B, -, rfl⟩` from `hw`. Take `⟨k, rfl⟩` from `hl w hw`. Conclude with `⟨k • B, by rw [embV_smul h, smul_smul]⟩`. Consider the case `zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨B, rfl⟩` from `ha`. Take `⟨B', rfl⟩` from `hb`. Conclude with `⟨B + B', by rw [embV_add, smul_add]⟩`. Consider the case `neg a _ ha`.

Take `⟨B, rfl⟩` from `ha`. Conclude with `⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩`.
-/
theorem klat_rat (h : GL3Theta.InducedCMType D) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A)
    {x : VC D N N'} (hx : x ∈ A) : ∃ B, x = δ • embV D (tor0 D cc δ) B := by
  obtain ⟨S, -, rfl⟩ := klat_gen hA
  have hl : ∀ w ∈ lamOf D cc δ, ∃ k : D.host.K, w = δ * D.host.φ₀ (k : D.host.E) := by
    intro w hw
    induction hw using AddSubgroup.closure_induction with
    | mem w hw => obtain ⟨c, -, rfl⟩ := hw; exact ⟨c, rfl⟩
    | zero => exact ⟨0, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨k, rfl⟩ := ha
      obtain ⟨k', rfl⟩ := hb
      exact ⟨k + k', by simp [mul_add]⟩
    | neg a _ ha =>
      obtain ⟨k, rfl⟩ := ha
      exact ⟨-k, by simp⟩
  induction hx using AddSubgroup.closure_induction with
  | mem w hw =>
    obtain ⟨w, hw, B, -, rfl⟩ := hw
    obtain ⟨k, rfl⟩ := hl w hw
    exact ⟨k • B, by rw [embV_smul h, smul_smul]⟩
  | zero => exact ⟨0, by rw [embV_zero, smul_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨B, rfl⟩ := ha
    obtain ⟨B', rfl⟩ := hb
    exact ⟨B + B', by rw [embV_add, smul_add]⟩
  | neg a _ ha =>
    obtain ⟨B, rfl⟩ := ha
    exact ⟨(-1 : D.host.K) • B, by rw [embV_smul h]; simp⟩

/- English proof (translation)
Establish `hA'` using `hA`. Take `⟨S, hS, hAS⟩` from `klat_gen hA'`. Establish `hB : B ∈ Submodule.span D.host.K S` using `hS ▸ Submodule.mem_top`. Proceed by induction on `hB using Submodule.span_induction with`. Consider the case `mem B hB`.

Use `⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩` and prove the remaining obligations. Rewrite using `[hAS]`. Use `AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ, AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩` and prove the remaining obligations. Rewrite using `[← smul_smul, Nat.cast_smul_eq_nsmul]`. Consider the case `zero => exact ⟨1, one_pos, by simp [embV_zero]⟩`.

Consider the case `add a b _ _ ha hb`. Take `⟨m, hm, ha⟩` from `ha`. Take `⟨n, hn, hb⟩` from `hb`. Use `⟨m * n, by positivity, ?_⟩` and prove the remaining obligations. Rewrite using `[embV_add, smul_add, smul_add]`.

Use `A.add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[mul_comm, mul_smul]`. Conclude with `A.nsmul_mem ha _`. Rewrite using `[mul_smul]`. Conclude with `A.nsmul_mem hb _`.

Consider the case `smul k B _ hB`. Take `⟨m, hm, hB⟩` from `hB`. Take `⟨n, hn, hk⟩` from `exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)`. Establish `hk' : IsIntegral ℤ (n.natAbs • k)`. Use `hk k (Finset.mem_singleton_self k)` as an intermediate fact.

Break down `Int.natAbs_eq n with e | e` into its components or cases. Rewrite `this` using `[e]`. Simplify using `using this`. Rewrite `this` using `[e]`. Simplify using `using this.neg`.

Use `⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩` and prove the remaining obligations. Use `klat_smul_mem hA ⟨_, hk'⟩ hB using 1` and compare the differences between its conclusion and the goal. Rewrite using `[embV_smul h]`. Simplify using `only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]`. Use `congr 1`.

Express the relevant statement in the definitionally equal form `_ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _`. Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree.
-/
theorem klat_mul_mem (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A : AddSubgroup (VC D N N')}
    (hA : KLat D (tor0 D cc δ) A) (B : Matrix (Fin N') (Fin N) D.host.E) :
    ∃ m : ℕ, 0 < m ∧ m • (δ • embV D (tor0 D cc δ) B) ∈ A := by
  have hA' := hA
  obtain ⟨S, hS, hAS⟩ := klat_gen hA'
  have hB : B ∈ Submodule.span D.host.K S := hS ▸ Submodule.mem_top
  induction hB using Submodule.span_induction with
  | mem B hB =>
    refine ⟨Ideal.absNorm cc, Nat.pos_of_ne_zero (fun e => hcc (Ideal.absNorm_eq_zero_iff.1 e)), ?_⟩
    rw [hAS]
    refine AddSubgroup.subset_closure ⟨(Ideal.absNorm cc : ℂ) * δ,
      AddSubgroup.subset_closure ⟨_, Ideal.absNorm_mem cc, by simp [mul_comm]⟩, B, hB, ?_⟩
    rw [← smul_smul, Nat.cast_smul_eq_nsmul]
  | zero => exact ⟨1, one_pos, by simp [embV_zero]⟩
  | add a b _ _ ha hb =>
    obtain ⟨m, hm, ha⟩ := ha
    obtain ⟨n, hn, hb⟩ := hb
    refine ⟨m * n, by positivity, ?_⟩
    rw [embV_add, smul_add, smul_add]
    refine A.add_mem ?_ ?_
    · rw [mul_comm, mul_smul]; exact A.nsmul_mem ha _
    · rw [mul_smul]; exact A.nsmul_mem hb _
  | smul k B _ hB =>
    obtain ⟨m, hm, hB⟩ := hB
    obtain ⟨n, hn, hk⟩ := exists_integral_multiples ℤ ℚ ({k} : Finset D.host.K)
    have hk' : IsIntegral ℤ (n.natAbs • k) := by
      have := hk k (Finset.mem_singleton_self k)
      rcases Int.natAbs_eq n with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    refine ⟨m * n.natAbs, Nat.mul_pos hm (Int.natAbs_pos.2 hn), ?_⟩
    convert klat_smul_mem hA ⟨_, hk'⟩ hB using 1
    rw [embV_smul h]
    simp only [← Nat.cast_smul_eq_nsmul ℂ, smul_smul]
    congr 1
    change _ = D.host.φ₀ ((n.natAbs • k : D.host.K) : D.host.E) * _
    simp
    ring

/- English proof (translation)
The claim follows from `finite_quot hfg fun x hx => by obtain ⟨B, rfl⟩ := klat_rat h h₂ hx exact klat_mul_mem h hcc h₁ B`.
-/
theorem klat_finite (h : GL3Theta.InducedCMType D) (hcc : cc ≠ ⊥) {A₁ A₂ : AddSubgroup (VC D N N')}
    (h₁ : KLat D (tor0 D cc δ) A₁) (h₂ : KLat D (tor0 D cc δ) A₂) (hfg : A₂.FG) :
    Finite (A₂ ⧸ A₁.addSubgroupOf A₂) :=
  finite_quot hfg fun x hx => by
    obtain ⟨B, rfl⟩ := klat_rat h h₂ hx
    exact klat_mul_mem h hcc h₁ B

/- English proof (translation)
Take `⟨-, -, h1, h2, h3, h4, h5⟩` from `GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA`. Use `⟨h3, h4, le_antisymm h2 h1, ?_⟩` and prove the remaining obligations. Take `⟨a, ha⟩` from `GlobalTheory.NormSum.exists_integer_map_eq_w0 D`. Use `isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5` and prove the remaining obligations. Use `klat_smul_mem hA a hx` as an intermediate fact.

Rewrite `this` using `[ha]`. Then use the resulting hypothesis.
-/
theorem klat_facts (hc : Crv D cc δ) {A : AddSubgroup (VC D N N')} (hA : KLat D (tor0 D cc δ) A) :
    A.FG ∧ Submodule.span ℝ (A : Set (VC D N N')) = ⊤ ∧ IsSelfDual (sesqOf D (tor0 D cc δ) N N') A ∧
      IsSemiChar (sesqOf D (tor0 D cc δ) N N') A (al D (tor0 D cc δ)) := by
  obtain ⟨-, -, h1, h2, h3, h4, h5⟩ := GlobalTheory.ThetaLine.theta_line D (GlobalTheory.InducedType.induced_type D).1 cc δ hc N N' A hA
  refine ⟨h3, h4, le_antisymm h2 h1, ?_⟩
  obtain ⟨a, ha⟩ := GlobalTheory.NormSum.exists_integer_map_eq_w0 D
  refine isSemiChar_round (isHerm_sesqOf D _ N N') (Real.sqrt D.host.d) h1 (fun x hx => ?_) h5
  have := klat_smul_mem hA a hx
  rwa [ha] at this

end GlobalTheory.ThetaInter

open GlobalTheory.ThetaInter in

/- English proof (translation)
Introduce `D cc δ hc N N' A₁ A₂ h₁ h₂ th hth`. Take `⟨f₁, s₁, d₁, c₁⟩` from `klat_facts hc h₁`. Take `⟨f₂, s₂, d₂, c₂⟩` from `klat_facts hc h₂`. Establish `hH` using `isHerm_sesqOf D (tor0 D cc δ) N N'`. Establish `hψ` using `(GlobalTheory.InducedType.induced_type D).1.1`.

Use `klat_finite hψ hc.1.1 h₁ h₂ f₂` as an intermediate fact. Use `klat_finite hψ hc.1.1 h₂ h₁ f₁` as an intermediate fact. Establish `: (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure` using `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `: (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure` using `MeasureTheory.Measure.pi.isAddHaarMeasure _`. Establish `t₁` using `discrete_of_selfDual hH d₁ f₁`.

Establish `t₂` using `discrete_of_selfDual hH d₂ f₂`. Establish `hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁` using `hth.2`. Conclude with `⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x, ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1, inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩, mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF, inter …`.
-/
theorem GlobalTheory.theta_translation_intertwiner_unitary : ∀ D : D7, IntertwinerUnitary D := by
  intro D cc δ hc N N' A₁ A₂ h₁ h₂ th hth
  obtain ⟨f₁, s₁, d₁, c₁⟩ := klat_facts hc h₁
  obtain ⟨f₂, s₂, d₂, c₂⟩ := klat_facts hc h₂
  have hH := isHerm_sesqOf D (tor0 D cc δ) N N'
  have hψ := (GlobalTheory.InducedType.induced_type D).1.1
  have := klat_finite hψ hc.1.1 h₁ h₂ f₂
  have := klat_finite hψ hc.1.1 h₂ h₁ f₁
  have : (MeasureTheory.volume : MeasureTheory.Measure (Fin N' → Fin N → ℂ)).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have : (MeasureTheory.volume : MeasureTheory.Measure (VC D N N')).IsAddHaarMeasure :=
    MeasureTheory.Measure.pi.isAddHaarMeasure _
  have t₁ := discrete_of_selfDual hH d₁ f₁
  have t₂ := discrete_of_selfDual hH d₂ f₂
  have hF : th ∈ Formalism.L2.Th1.H.fixedBy (sesqOf D (tor0 D cc δ) N N') (al D (tor0 D cc δ)) A₁ := hth.2
  exact ⟨fun x => mean_opU MeasureTheory.volume hH t₁ s₁ c₁ hth.1.continuous hF x,
    ⟨differentiable_inter (H := sesqOf D (tor0 D cc δ) N N') (α := al D (tor0 D cc δ)) A₁ A₂ hth.1,
      inter_mem_fixedBy hH c₁ d₂ c₂ hF⟩,
    mean_inter MeasureTheory.volume hH t₁ s₁ t₂ s₂ d₁ c₁ d₂ c₂ hth.1 hF,
    inter_inter hH d₁ d₂ c₁ hF⟩
