import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.QuotientVanishing.QuotVanish
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IntegralEqSmulIntegralAvg
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsIsometryFlagOfEquiv
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwCentPreservesFlag
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.EqZeroOfCommuteOfSeparable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SecondCountableNilrad
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.KillingFormDiffCartanInvolution
import Development.AbelianVarietyTheory.Definitions.Divisors.T2SpaceGeneralLinearGroup

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc
open scoped ENNReal NNReal

namespace GlobalTheory.CompanionTheory.QuotVan

variable {n : ℕ}

local notation "θc" => thetaR (starRingEnd ℂ) n

/- English proof (translation)
Use `⟨fun g => ?_⟩` and prove the remaining obligations. Establish `h : Measure.modularCharacter g = 1`. Use `hG Measure.modularCharacter (fun z hz => ?_) g` and prove the remaining obligations. Establish `h1` using `Measure.map_right_mul_eq_modularCharacterFun_smul μ z`. Rewrite `h1` using `[show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm, Measure.IsMulLeftInvariant.map_mul_left_eq_self]`.

Take `⟨C, hC, hC1⟩` from `exists_compact_mem_nhds (1 : G)`. Establish `h2` using `congrArg (fun m : Measure G => m C) h1`. Establish `hne : μ C ≠ 0` using `(Measure.measure_pos_of_mem_nhds μ hC1).ne'`. Establish `hnt : μ C ≠ ⊤` using `hC.measure_lt_top.ne`. Simplify using `only [Measure.coe_nnreal_smul_apply] at h2`.

Establish `h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1` using `(ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)`. Conclude with `h3` after adjusting the coercions. Rewrite using `[Measure.map_right_mul_eq_modularCharacterFun_smul μ g, show Measure.modularCharacterFun g = 1 from h, one_smul]`.
-/
theorem isMulRightInvariant_of_center {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [LocallyCompactSpace G] [SecondCountableTopology G] [T2Space G] [MeasurableSpace G] [BorelSpace G]
    (hG : ∀ Δ : G →* ℝ≥0, (∀ g, (∀ h, g * h = h * g) → Δ g = 1) → ∀ g, Δ g = 1)
    (μ : Measure G) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  refine ⟨fun g => ?_⟩
  have h : Measure.modularCharacter g = 1 := by
    refine hG Measure.modularCharacter (fun z hz => ?_) g
    have h1 := Measure.map_right_mul_eq_modularCharacterFun_smul μ z
    rw [show (fun x => x * z) = fun x => z * x from funext fun x => (hz x).symm,
      Measure.IsMulLeftInvariant.map_mul_left_eq_self] at h1
    obtain ⟨C, hC, hC1⟩ := exists_compact_mem_nhds (1 : G)
    have h2 := congrArg (fun m : Measure G => m C) h1
    have hne : μ C ≠ 0 := (Measure.measure_pos_of_mem_nhds μ hC1).ne'
    have hnt : μ C ≠ ⊤ := hC.measure_lt_top.ne
    simp only [Measure.coe_nnreal_smul_apply] at h2
    have h3 : (Measure.modularCharacterFun z : ℝ≥0∞) = 1 :=
      (ENNReal.mul_left_inj hne hnt).1 (by rw [one_mul]; exact h2.symm)
    exact_mod_cast h3
  rw [Measure.map_right_mul_eq_modularCharacterFun_smul μ g,
    show Measure.modularCharacterFun g = 1 from h, one_smul]

/- English proof (translation)
Use `haveI := GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n`. Use `haveI := GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n`. Conclude with `isMulRightInvariant_of_center (fun Δ hc g => GlobalTheory.SplitFlip.hom_eq_one_of_center Δ hc g) μ`.
-/
theorem isMulRightInvariant_GL (n : ℕ) [MeasurableSpace (GL (Fin n) ℂ)] [BorelSpace (GL (Fin n) ℂ)]
    (μ : Measure (GL (Fin n) ℂ)) [μ.IsHaarMeasure] : μ.IsMulRightInvariant := by
  haveI := GlobalTheory.CompanionTheory.LocVan.locallyCompact_GL n
  haveI := GlobalTheory.CompanionTheory.LocVan.secondCountable_GL n
  exact isMulRightInvariant_of_center (fun Δ hc g => GlobalTheory.SplitFlip.hom_eq_one_of_center Δ hc g) μ

def uK (n : ℕ) : Subgroup (GL (Fin n) ℂ) := MonoidHom.eqLocus (thetaR (starRingEnd ℂ) n) (MonoidHom.id _)

/- English proof (translation)
Establish `h` using `GlobalTheory.Tw.isCompact_unitary_GL n`. Use `h using 1` and compare the differences between its conclusion and the goal. Use extensionality with `k`. Simplify using `only [SetLike.mem_coe, Set.mem_setOf_eq, Matrix.mem_unitaryGroup_iff]`. Express the relevant statement in the definitionally equal form `thetaR (starRingEnd ℂ) n k = k ↔ k.val * star k.val = 1`.

Prove the components needed by the constructor for the conclusion. Introduce `hk`. Establish `h1` using `GlobalTheory.CompanionTheory.NilChangeVar.theta_val k`. Rewrite `h1` using `[hk]`. Establish `h2 : star k.val = (k⁻¹ : GL (Fin n) ℂ).val`.

Rewrite using `[Matrix.star_eq_conjTranspose]`. Use `conv_lhs => rw [h1]`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Rewrite using `[h2]`. Conclude with `Units.mul_inv k`.

Introduce `hk`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[GlobalTheory.CompanionTheory.NilChangeVar.theta_val]`. Establish `: (k⁻¹ : GL (Fin n) ℂ).val = star k.val` using `Units.inv_eq_of_mul_eq_one_right hk`. Rewrite using `[this, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]`.
-/
theorem isCompact_uK (n : ℕ) : IsCompact (uK n : Set (GL (Fin n) ℂ)) := by
  have h := GlobalTheory.Tw.isCompact_unitary_GL n
  convert h using 1
  ext k
  simp only [SetLike.mem_coe, Set.mem_setOf_eq, Matrix.mem_unitaryGroup_iff]
  change thetaR (starRingEnd ℂ) n k = k ↔ k.val * star k.val = 1
  constructor
  · intro hk
    have h1 := GlobalTheory.CompanionTheory.NilChangeVar.theta_val k
    rw [hk] at h1
    have h2 : star k.val = (k⁻¹ : GL (Fin n) ℂ).val := by
      rw [Matrix.star_eq_conjTranspose]
      conv_lhs => rw [h1]
      rw [Matrix.conjTranspose_conjTranspose]
    rw [h2]
    exact Units.mul_inv k
  · intro hk
    refine Units.ext ?_
    rw [GlobalTheory.CompanionTheory.NilChangeVar.theta_val]
    have : (k⁻¹ : GL (Fin n) ℂ).val = star k.val := Units.inv_eq_of_mul_eq_one_right hk
    rw [this, Matrix.star_eq_conjTranspose, Matrix.conjTranspose_conjTranspose]

/- English proof (translation)
Establish `hlocus : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (a * b) (b * a)`. Rewrite using `[← Module.End.iSup_maxGenEigenspace_eq_top f]`. Use `iSup_le fun μ x hx => ?_` and prove the remaining obligations. Establish `hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1`. Rewrite using `[LinearMap.finrank_maxGenEigenspace_eq]`.

Conclude with `Polynomial.rootMultiplicity_le_one_of_separable hs μ`. Take `⟨v, hv⟩` from `finrank_le_one_iff.1 hdim`. Establish `key : ∀ c : Module.End ℂ V, Commute f c → ∃ α : ℂ, ∀ y ∈ f.maxGenEigenspace μ, c y = α • y`. Introduce `c hc`. Take `⟨α, hα⟩` from `hv ⟨c v, Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v.2⟩`.

Use `⟨α, fun y hy => ?_⟩` and prove the remaining obligations. Take `⟨β, hβ⟩` from `hv ⟨y, hy⟩`. Establish `hβ' : β • (v : V) = y` using `congrArg Subtype.val hβ`. Establish `hα' : α • (v : V) = c v` using `congrArg Subtype.val hα`. Rewrite using `[← hβ', map_smul, ← hα', smul_comm]`.

Take `⟨α, hα⟩` from `key a ha`. Take `⟨β, hβ⟩` from `key b hb`. Express the relevant statement in the definitionally equal form `(a * b) x = (b * a) x`. Rewrite using `[Module.End.mul_apply, Module.End.mul_apply, hβ x hx, hα x hx, map_smul, map_smul, hα x hx, hβ x hx, smul_comm]`. Conclude with `LinearMap.ext fun x => hlocus (Submodule.mem_top (x := x))`.
-/
theorem commute_of_commute_separable {V : Type} [AddCommGroup V] [Module ℂ V] [FiniteDimensional ℂ V]
    (f a b : Module.End ℂ V) (hs : (LinearMap.charpoly f).Separable) (ha : Commute f a) (hb : Commute f b) :
    a * b = b * a := by
  have hlocus : (⊤ : Submodule ℂ V) ≤ LinearMap.eqLocus (a * b) (b * a) := by
    rw [← Module.End.iSup_maxGenEigenspace_eq_top f]
    refine iSup_le fun μ x hx => ?_
    have hdim : Module.finrank ℂ (f.maxGenEigenspace μ) ≤ 1 := by
      rw [LinearMap.finrank_maxGenEigenspace_eq]
      exact Polynomial.rootMultiplicity_le_one_of_separable hs μ
    obtain ⟨v, hv⟩ := finrank_le_one_iff.1 hdim
    have key : ∀ c : Module.End ℂ V, Commute f c → ∃ α : ℂ, ∀ y ∈ f.maxGenEigenspace μ, c y = α • y := by
      intro c hc
      obtain ⟨α, hα⟩ := hv ⟨c v, Module.End.mapsTo_maxGenEigenspace_of_comm hc μ v.2⟩
      refine ⟨α, fun y hy => ?_⟩
      obtain ⟨β, hβ⟩ := hv ⟨y, hy⟩
      have hβ' : β • (v : V) = y := congrArg Subtype.val hβ
      have hα' : α • (v : V) = c v := congrArg Subtype.val hα
      rw [← hβ', map_smul, ← hα', smul_comm]
    obtain ⟨α, hα⟩ := key a ha
    obtain ⟨β, hβ⟩ := key b hb
    change (a * b) x = (b * a) x
    rw [Module.End.mul_apply, Module.End.mul_apply, hβ x hx, hα x hx, map_smul, map_smul, hα x hx, hβ x hx, smul_comm]
  exact LinearMap.ext fun x => hlocus (Submodule.mem_top (x := x))

/- English proof (translation)
Establish `hs : (LinearMap.charpoly (Matrix.toLin' (d * θc d).val)).Separable`. Rewrite using `[Matrix.charpoly_toLin']` and apply the resulting hypothesis. Establish `cm : ∀ t ∈ twCent θc d, Commute (Matrix.toLin' (d * θc d).val) (Matrix.toLin' t.val)`. Introduce `t ht`. Establish `h` using `GlobalTheory.CompanionTheory.FlagCent.commute_norm (starRingEnd ℂ) (fun x => by simp) ht`.

Express the relevant statement in the definitionally equal form `Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul, ← Units.val_mul, ← Units.val_mul, h]`. Use `commute_of_commute_separable _ _ _ hs (cm a ha) (cm b hb)` as an intermediate fact. Rewrite `this` using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul]`. Conclude with `Units.ext (by simpa using Matrix.toLin'.injective this)`.
-/
theorem twCent_comm {d : GL (Fin n) ℂ} (hd : (d * θc d).val.charpoly.Separable)
    {a b : GL (Fin n) ℂ} (ha : a ∈ twCent θc d) (hb : b ∈ twCent θc d) : a * b = b * a := by
  have hs : (LinearMap.charpoly (Matrix.toLin' (d * θc d).val)).Separable := by
    rwa [Matrix.charpoly_toLin']
  have cm : ∀ t ∈ twCent θc d, Commute (Matrix.toLin' (d * θc d).val) (Matrix.toLin' t.val) := by
    intro t ht
    have h := GlobalTheory.CompanionTheory.FlagCent.commute_norm (starRingEnd ℂ) (fun x => by simp) ht
    change Matrix.toLin' _ * Matrix.toLin' _ = Matrix.toLin' _ * Matrix.toLin' _
    rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul,
      ← Units.val_mul, ← Units.val_mul, h]
  have := commute_of_commute_separable _ _ _ hs (cm a ha) (cm b hb)
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← Matrix.toLin'_mul, ← Matrix.toLin'_mul] at this
  exact Units.ext (by simpa using Matrix.toLin'.injective this)

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Ring

variable {R : Type*} [Ring R]

def lev (p₁ p₂ p₃ a : R) : R := p₁ * a * p₁ + p₂ * a * p₂ + p₃ * a * p₃

/- English proof (translation)
Establish `i1 : p₁ * p₁ = p₁`. Use `congrArg (fun x => p₁ * x) hs` as an intermediate fact. Simplify `this` using `[mul_add, o12, o13]`. Establish `i2 : p₂ * p₂ = p₂`. Use `congrArg (fun x => p₂ * x) hs` as an intermediate fact.

Simplify `this` using `[mul_add, o21, o23]`. Establish `i3 : p₃ * p₃ = p₃`. Use `congrArg (fun x => p₃ * x) hs` as an intermediate fact. Simplify `this` using `[mul_add, o31, o32]`. Establish `e : lev p₁ p₂ p₃ a * lev p₁ p₂ p₃ b = p₁ * a * p₁ * b * p₁ + p₂ * a * p₂ * b * p₂ + p₃ * a * p₃ * b * p₃`.

Simplify using `only [lev, add_mul, mul_add, mul_assoc]`. Simplify using `only [← mul_assoc (p₁) (p₁), ← mul_assoc p₁ p₂, ← mul_assoc p₁ p₃, ← mul_assoc p₂ p₁, ← mul_assoc p₂ p₂, ← mul_assoc p₂ p₃, ← mul_assoc p₃ p₁, ← mul_assoc p₃ p₂, ← mul_assoc p₃ p₃, i1, i2, i3, o12, o13, o21, o23, o31, o32, zero_mul, mul_zero, add_zero, zero_add]`. Establish `key : ∀ p : R, p * p = p → p * a * p₁ * b * p + p * a * p₂ * b * p + p * a * p₃ * b * p = p`. Introduce `p hp`. Combine the equalities or inequalities in the displayed calculation.

Establish `k1` using `key p₁ i1`. Establish `k2` using `key p₂ i2`. Establish `k3` using `key p₃ i3`. Establish `t1 : p₁ * a * p₂ * b * p₁ = 0` using `by simp only [mul_assoc] at b21 ⊢; simp [b21]`. Establish `t2 : p₁ * a * p₃ * b * p₁ = 0` using `by simp only [mul_assoc] at b31 ⊢; simp [b31]`.

Establish `t3 : p₂ * a * p₁ * b * p₂ = 0` using `by rw [a21]; simp`. Establish `t4 : p₂ * a * p₃ * b * p₂ = 0` using `by simp only [mul_assoc] at b32 ⊢; simp [b32]`. Establish `t5 : p₃ * a * p₁ * b * p₃ = 0` using `by rw [a31]; simp`. Establish `t6 : p₃ * a * p₂ * b * p₃ = 0` using `by rw [a32]; simp`. Rewrite `k1` using `[t1, t2, add_zero, add_zero]`.

Rewrite `k2` using `[t3, t4, zero_add, add_zero]`. Rewrite `k3` using `[t5, t6, zero_add, zero_add]`. Rewrite using `[e, k1, k2, k3, hs]`.
-/
theorem lev_mul {p₁ p₂ p₃ a b : R} (hs : p₁ + p₂ + p₃ = 1)
    (o12 : p₁ * p₂ = 0) (o13 : p₁ * p₃ = 0) (o21 : p₂ * p₁ = 0) (o23 : p₂ * p₃ = 0)
    (o31 : p₃ * p₁ = 0) (o32 : p₃ * p₂ = 0) (ab : a * b = 1)
    (a21 : p₂ * a * p₁ = 0) (a31 : p₃ * a * p₁ = 0) (a32 : p₃ * a * p₂ = 0)
    (b21 : p₂ * b * p₁ = 0) (b32 : p₃ * b * p₂ = 0) (b31 : p₃ * b * p₁ = 0) :
    lev p₁ p₂ p₃ a * lev p₁ p₂ p₃ b = 1 := by
  have i1 : p₁ * p₁ = p₁ := by
    have := congrArg (fun x => p₁ * x) hs
    simpa [mul_add, o12, o13] using this
  have i2 : p₂ * p₂ = p₂ := by
    have := congrArg (fun x => p₂ * x) hs
    simpa [mul_add, o21, o23] using this
  have i3 : p₃ * p₃ = p₃ := by
    have := congrArg (fun x => p₃ * x) hs
    simpa [mul_add, o31, o32] using this
  have e : lev p₁ p₂ p₃ a * lev p₁ p₂ p₃ b =
      p₁ * a * p₁ * b * p₁ + p₂ * a * p₂ * b * p₂ + p₃ * a * p₃ * b * p₃ := by
    simp only [lev, add_mul, mul_add, mul_assoc]
    simp only [← mul_assoc (p₁) (p₁), ← mul_assoc p₁ p₂, ← mul_assoc p₁ p₃, ← mul_assoc p₂ p₁,
      ← mul_assoc p₂ p₂, ← mul_assoc p₂ p₃, ← mul_assoc p₃ p₁, ← mul_assoc p₃ p₂, ← mul_assoc p₃ p₃,
      i1, i2, i3, o12, o13, o21, o23, o31, o32, zero_mul, mul_zero, add_zero, zero_add]
  have key : ∀ p : R, p * p = p → p * a * p₁ * b * p + p * a * p₂ * b * p + p * a * p₃ * b * p = p := by
    intro p hp
    calc p * a * p₁ * b * p + p * a * p₂ * b * p + p * a * p₃ * b * p
        = p * a * (p₁ + p₂ + p₃) * b * p := by noncomm_ring
      _ = p * (a * b) * p := by rw [hs]; simp [mul_assoc]
      _ = p := by rw [ab, mul_one, hp]
  have k1 := key p₁ i1
  have k2 := key p₂ i2
  have k3 := key p₃ i3
  have t1 : p₁ * a * p₂ * b * p₁ = 0 := by simp only [mul_assoc] at b21 ⊢; simp [b21]
  have t2 : p₁ * a * p₃ * b * p₁ = 0 := by simp only [mul_assoc] at b31 ⊢; simp [b31]
  have t3 : p₂ * a * p₁ * b * p₂ = 0 := by rw [a21]; simp
  have t4 : p₂ * a * p₃ * b * p₂ = 0 := by simp only [mul_assoc] at b32 ⊢; simp [b32]
  have t5 : p₃ * a * p₁ * b * p₃ = 0 := by rw [a31]; simp
  have t6 : p₃ * a * p₂ * b * p₃ = 0 := by rw [a32]; simp
  rw [t1, t2, add_zero, add_zero] at k1
  rw [t3, t4, zero_add, add_zero] at k2
  rw [t5, t6, zero_add, zero_add] at k3
  rw [e, k1, k2, k3, hs]

/- English proof (translation)
Establish `h : a = (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃)` using `by rw [hs]; simp`. Establish `h2 : (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃) = p₁ * a * p₁ + p₁ * a * p₂ + p₁ * a * p₃ + (p₂ * a * p₁ + p₂ * a * p₂ + p₂ * a * p₃) + (p₃ * a * p₁ + p₃ * a * p₂ + p₃ * a * p₃)` using `by noncomm_ring`. Rewrite `h2` using `[a21, a31, a32]`. Establish `h3` using `h.trans h2`. Simplify using `only [lev]`.

Use `nth_rewrite 1 [h3]`. Normalize the expressions using the abelian group laws.
-/
theorem eq_lev_add {p₁ p₂ p₃ a : R} (hs : p₁ + p₂ + p₃ = 1)
    (a21 : p₂ * a * p₁ = 0) (a31 : p₃ * a * p₁ = 0) (a32 : p₃ * a * p₂ = 0) :
    a - lev p₁ p₂ p₃ a = p₁ * a * p₂ + p₁ * a * p₃ + p₂ * a * p₃ := by
  have h : a = (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃) := by rw [hs]; simp
  have h2 : (p₁ + p₂ + p₃) * a * (p₁ + p₂ + p₃) = p₁ * a * p₁ + p₁ * a * p₂ + p₁ * a * p₃ +
      (p₂ * a * p₁ + p₂ * a * p₂ + p₂ * a * p₃) + (p₃ * a * p₁ + p₃ * a * p₂ + p₃ * a * p₃) := by
    noncomm_ring
  rw [a21, a31, a32] at h2
  have h3 := h.trans h2
  simp only [lev]
  nth_rewrite 1 [h3]
  abel

end Ring

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Levi

variable {n : ℕ}

local notation "Mx" => Matrix (Fin n) (Fin n) ℂ
local notation "Sb" => Submodule ℂ (Fin n → ℂ)

open GlobalTheory.CompanionTheory.FlagCent (mem_img_iff)

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul]`. Simplify using the standard rewrite rules.
-/
theorem mulVec_inv_mulVec (g : GL (Fin n) ℂ) (y : Fin n → ℂ) :
    g.val *ᵥ ((g⁻¹ : GL (Fin n) ℂ).val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp

/- English proof (translation)
Rewrite using `[Matrix.mulVec_mulVec, ← Units.val_mul]`. Simplify using the standard rewrite rules.
-/
theorem inv_mulVec_mulVec (g : GL (Fin n) ℂ) (y : Fin n → ℂ) :
    (g⁻¹ : GL (Fin n) ℂ).val *ᵥ (g.val *ᵥ y) = y := by
  rw [Matrix.mulVec_mulVec, ← Units.val_mul]; simp

/- English proof (translation)
Use extensionality with `y`. Rewrite using `[mem_img_iff]`. Use `⟨fun h => ?_, h₂ y⟩` and prove the remaining obligations. Use `h₁ _ h` as an intermediate fact. Rewrite `this` using `[mulVec_inv_mulVec]`. Then use the resulting hypothesis.
-/
theorem img_eq_of_mapsTo (g : GL (Fin n) ℂ) (W : Sb) (h₁ : ∀ y ∈ W, g.val *ᵥ y ∈ W)
    (h₂ : ∀ y ∈ W, (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W) : img g W = W := by
  ext y
  rw [mem_img_iff]
  refine ⟨fun h => ?_, h₂ y⟩
  have := h₁ _ h
  rwa [mulVec_inv_mulVec] at this

/- English proof (translation)
Rewrite using `[← h]`. Conclude with `⟨y, hy, by rw [Matrix.toLin'_apply]⟩`.
-/
theorem mulVec_mem_of_img (g : GL (Fin n) ℂ) {W : Sb} (h : img g W = W) {y : Fin n → ℂ} (hy : y ∈ W) :
    g.val *ᵥ y ∈ W := by
  rw [← h]
  exact ⟨y, hy, by rw [Matrix.toLin'_apply]⟩

/- English proof (translation)
Rewrite `hy` using `[← h]`. Conclude with `(mem_img_iff g _ y).1 hy`.
-/
theorem inv_mulVec_mem_of_img (g : GL (Fin n) ℂ) {W : Sb} (h : img g W = W) {y : Fin n → ℂ} (hy : y ∈ W) :
    (g⁻¹ : GL (Fin n) ℂ).val *ᵥ y ∈ W := by
  rw [← h] at hy
  exact (mem_img_iff g _ y).1 hy

/- English proof (translation)
Establish `hss : Module.End.IsSemisimple (Matrix.toLin' γ : Module.End ℂ (Fin n → ℂ))`. Use `Module.End.isSemisimple_of_squarefree_aeval_eq_zero (p := LinearMap.charpoly (Matrix.toLin' γ)) ?_ (LinearMap.aeval_self_charpoly _)` and prove the remaining obligations. Rewrite using `[Matrix.charpoly_toLin']`. Conclude with `hs.squarefree`. Take `⟨C, hC, hc⟩` from `Module.End.isSemisimple_iff.1 hss W ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).2 fun x hx => by`.

Simplify `hW x hx)` using `[Matrix.toLin'_apply]`. Use `⟨C, hc, fun x hx => ?_⟩` and prove the remaining obligations. Use `(Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).1 hC x hx` as an intermediate fact. Simplify `this` using `[Matrix.toLin'_apply]`.
-/
theorem exists_stable_compl (γ : Mx) (hs : γ.charpoly.Separable) (W : Sb)
    (hW : ∀ x ∈ W, γ *ᵥ x ∈ W) : ∃ C : Sb, IsCompl W C ∧ ∀ x ∈ C, γ *ᵥ x ∈ C := by
  have hss : Module.End.IsSemisimple (Matrix.toLin' γ : Module.End ℂ (Fin n → ℂ)) := by
    refine Module.End.isSemisimple_of_squarefree_aeval_eq_zero
      (p := LinearMap.charpoly (Matrix.toLin' γ)) ?_ (LinearMap.aeval_self_charpoly _)
    rw [Matrix.charpoly_toLin']
    exact hs.squarefree
  obtain ⟨C, hC, hc⟩ := Module.End.isSemisimple_iff.1 hss W
    ((Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).2 fun x hx => by
      simpa [Matrix.toLin'_apply] using hW x hx)
  refine ⟨C, hc, fun x hx => ?_⟩
  have := (Module.End.mem_invtSubmodule_iff_forall_mem_of_mem (Matrix.toLin' γ)).1 hC x hx
  simpa [Matrix.toLin'_apply] using this

/- English proof (translation)
Take `⟨A, hA, hAs⟩` from `exists_stable_compl γ.val hs W₁ fun x hx => mulVec_mem_of_img γ h₁ hx`. Take `⟨V₃, hV, hVs⟩` from `exists_stable_compl γ.val hs W₂ fun x hx => mulVec_mem_of_img γ h₂ hx`. Establish `st : ∀ C : Sb, (∀ x ∈ C, γ.val *ᵥ x ∈ C) → img γ C = C` using `fun C hC => by`. Use `Submodule.eq_of_le_of_finrank_eq ?_ (GlobalTheory.CompanionTheory.IwaDecomp.finrank_img γ C)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Simplify `hC x hx` using `[Matrix.toLin'_apply]`. Use `⟨A ⊓ W₂, V₃, ?_, ?_, hV.sup_eq_top, hV.inf_eq_bot, st _ fun x hx => ?_, st _ hVs⟩` and prove the remaining obligations. Rewrite using `[← sup_inf_assoc_of_le A hle, hA.sup_eq_top, top_inf_eq]`. Rewrite using `[← inf_assoc, hA.inf_eq_bot, bot_inf_eq]`. Conclude with `⟨hAs x hx.1, mulVec_mem_of_img γ h₂ hx.2⟩`.
-/
theorem exists_levi_spaces (γ : GL (Fin n) ℂ) (hs : γ.val.charpoly.Separable) {W₁ W₂ : Sb} (hle : W₁ ≤ W₂)
    (h₁ : img γ W₁ = W₁) (h₂ : img γ W₂ = W₂) :
    ∃ V₂ V₃ : Sb, W₁ ⊔ V₂ = W₂ ∧ W₁ ⊓ V₂ = ⊥ ∧ W₂ ⊔ V₃ = ⊤ ∧ W₂ ⊓ V₃ = ⊥ ∧
      img γ V₂ = V₂ ∧ img γ V₃ = V₃ := by
  obtain ⟨A, hA, hAs⟩ := exists_stable_compl γ.val hs W₁ fun x hx => mulVec_mem_of_img γ h₁ hx
  obtain ⟨V₃, hV, hVs⟩ := exists_stable_compl γ.val hs W₂ fun x hx => mulVec_mem_of_img γ h₂ hx
  have st : ∀ C : Sb, (∀ x ∈ C, γ.val *ᵥ x ∈ C) → img γ C = C := fun C hC => by
    refine Submodule.eq_of_le_of_finrank_eq ?_ (GlobalTheory.CompanionTheory.IwaDecomp.finrank_img γ C)
    rintro _ ⟨x, hx, rfl⟩
    simpa [Matrix.toLin'_apply] using hC x hx
  refine ⟨A ⊓ W₂, V₃, ?_, ?_, hV.sup_eq_top, hV.inf_eq_bot, st _ fun x hx => ?_, st _ hVs⟩
  · rw [← sup_inf_assoc_of_le A hle, hA.sup_eq_top, top_inf_eq]
  · rw [← inf_assoc, hA.inf_eq_bot, bot_inf_eq]
  · exact ⟨hAs x hx.1, mulVec_mem_of_img γ h₂ hx.2⟩

/- English proof (translation)
Establish `hy : y ∈ W₂ ⊔ V₃` using `by rw [c₂]; trivial`. Take `⟨w, hw, c, hc, rfl⟩` from `Submodule.mem_sup.1 hy`. Rewrite `hw` using `[← c₁]`. Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.1 hw`. Conclude with `⟨a, ha, b, hb, c, hc, rfl⟩`.
-/
theorem exists_sum_along_flag {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (c₂ : W₂ ⊔ V₃ = ⊤) (y : Fin n → ℂ) :
    ∃ a ∈ W₁, ∃ b ∈ V₂, ∃ c ∈ V₃, y = a + b + c := by
  have hy : y ∈ W₂ ⊔ V₃ := by rw [c₂]; trivial
  obtain ⟨w, hw, c, hc, rfl⟩ := Submodule.mem_sup.1 hy
  rw [← c₁] at hw
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.1 hw
  exact ⟨a, ha, b, hb, c, hc, rfl⟩

/- English proof (translation)
Establish `hle₁ : W₁ ≤ W₂` using `c₁ ▸ le_sup_left`. Establish `hle₂ : V₂ ≤ W₂` using `c₁ ▸ le_sup_right`. Establish `h3 : IsCompl V₃ W₂` using `⟨disjoint_iff.2 (by rw [inf_comm]; exact d₂), codisjoint_iff.2 (by rw [sup_comm]; exact c₂)⟩`. Establish `h1 : IsCompl W₁ (V₂ ⊔ V₃)`. Use `⟨Submodule.disjoint_def.2 fun y hy hy' => ?_, codisjoint_iff.2 ?_⟩` and prove the remaining obligations.

Take `⟨b, hb, c, hc, rfl⟩` from `Submodule.mem_sup.1 hy'`. Establish `hcW : c ∈ W₂`. Use `W₂.sub_mem (hle₁ hy) (hle₂ hb)` as an intermediate fact. Simplify using `using this`. Establish `hc0 : c = 0`.

Establish `: c ∈ W₂ ⊓ V₃` using `⟨hcW, hc⟩`. Rewrite `this` using `[d₂]`. Simplify using `using this`. Substitute `hc0` using the available equality. Establish `: b + 0 ∈ W₁ ⊓ V₂` using `⟨hy, by simpa using hb⟩`.

Rewrite `this` using `[d₁]`. Simplify using `using this`. Rewrite using `[← sup_assoc, c₁, c₂]`. Set `E₁` to `W₁.projection (V₂ ⊔ V₃) h1`. Set `E₃` to `V₃.projection W₂ h3`.

Establish `e1 : ∀ a ∈ W₁, E₁ a = a` using `fun a ha => Submodule.projection_apply_left h1 ⟨a, ha⟩`. Establish `e1' : ∀ b ∈ V₂ ⊔ V₃, E₁ b = 0` using `fun b hb => Submodule.projection_apply_of_mem_right h1 hb`. Establish `e3 : ∀ c ∈ V₃, E₃ c = c` using `fun c hc => Submodule.projection_apply_left h3 ⟨c, hc⟩`. Establish `e3' : ∀ b ∈ W₂, E₃ b = 0` using `fun b hb => Submodule.projection_apply_of_mem_right h3 hb`. Establish `m1 : ∀ y, LinearMap.toMatrix' E₁ *ᵥ y = E₁ y` using `fun y => LinearMap.toMatrix'_mulVec E₁ y`.

Establish `m3 : ∀ y, LinearMap.toMatrix' E₃ *ᵥ y = E₃ y` using `fun y => LinearMap.toMatrix'_mulVec E₃ y`. Establish `m2 : ∀ y, (1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃ : Mx) *ᵥ y = y - E₁ y - E₃ y` using `fun y => by`. Rewrite using `[Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, m1, m3]`. Use `⟨LinearMap.toMatrix' E₁, 1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃, LinearMap.toMatrix' E₃, by abel, fun y => ?_, fun y => ?_, fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[m1]`.

Conclude with `Submodule.projection_apply_mem h1 y`. Rewrite using `[m2]`. Take `⟨a, ha, b, hb, c, hc, rfl⟩` from `exists_sum_along_flag c₁ c₂ y`. Establish `f1 : E₁ (a + b + c) = a`. Rewrite using `[map_add, map_add, e1 a ha, e1' b (Submodule.mem_sup_left hb), e1' c (Submodule.mem_sup_right hc), add_zero, add_zero]`.

Establish `f3 : E₃ (a + b + c) = c`. Rewrite using `[map_add, map_add, e3' a (hle₁ ha), e3' b (hle₂ hb), e3 c hc, zero_add, zero_add]`. Rewrite using `[f1, f3, show a + b + c - a - c = b by abel]`. Conclude with `hb`. Rewrite using `[m3]`.

Conclude with `Submodule.projection_apply_mem h3 y`. Rewrite using `[m3]`. Conclude with `e3' y hy`. Rewrite using `[m2, e1 y hy, e3' y (hle₁ hy)]`. Simplify using the standard rewrite rules.

Rewrite using `[m1]`. Conclude with `e1' y (Submodule.mem_sup_left hy)`. Rewrite using `[m1]`. Conclude with `e1' y (Submodule.mem_sup_right hy)`. Rewrite using `[m2, e1' y (Submodule.mem_sup_right hy), e3 y hy]`.

Simplify using the standard rewrite rules.
-/
theorem exists_proj {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) : ∃ P₁ P₂ P₃ : Mx, P₁ + P₂ + P₃ = 1 ∧ (∀ y, P₁ *ᵥ y ∈ W₁) ∧ (∀ y, P₂ *ᵥ y ∈ V₂) ∧
      (∀ y, P₃ *ᵥ y ∈ V₃) ∧ (∀ y ∈ W₂, P₃ *ᵥ y = 0) ∧ (∀ y ∈ W₁, P₂ *ᵥ y = 0) ∧
      (∀ y ∈ V₂, P₁ *ᵥ y = 0) ∧ (∀ y ∈ V₃, P₁ *ᵥ y = 0) ∧ ∀ y ∈ V₃, P₂ *ᵥ y = 0 := by
  have hle₁ : W₁ ≤ W₂ := c₁ ▸ le_sup_left
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have h3 : IsCompl V₃ W₂ := ⟨disjoint_iff.2 (by rw [inf_comm]; exact d₂),
    codisjoint_iff.2 (by rw [sup_comm]; exact c₂)⟩
  have h1 : IsCompl W₁ (V₂ ⊔ V₃) := by
    refine ⟨Submodule.disjoint_def.2 fun y hy hy' => ?_, codisjoint_iff.2 ?_⟩
    · obtain ⟨b, hb, c, hc, rfl⟩ := Submodule.mem_sup.1 hy'
      have hcW : c ∈ W₂ := by
        have := W₂.sub_mem (hle₁ hy) (hle₂ hb)
        simpa using this
      have hc0 : c = 0 := by
        have : c ∈ W₂ ⊓ V₃ := ⟨hcW, hc⟩
        rw [d₂] at this
        simpa using this
      subst hc0
      have : b + 0 ∈ W₁ ⊓ V₂ := ⟨hy, by simpa using hb⟩
      rw [d₁] at this
      simpa using this
    · rw [← sup_assoc, c₁, c₂]
  let E₁ := W₁.projection (V₂ ⊔ V₃) h1
  let E₃ := V₃.projection W₂ h3
  have e1 : ∀ a ∈ W₁, E₁ a = a := fun a ha => Submodule.projection_apply_left h1 ⟨a, ha⟩
  have e1' : ∀ b ∈ V₂ ⊔ V₃, E₁ b = 0 := fun b hb => Submodule.projection_apply_of_mem_right h1 hb
  have e3 : ∀ c ∈ V₃, E₃ c = c := fun c hc => Submodule.projection_apply_left h3 ⟨c, hc⟩
  have e3' : ∀ b ∈ W₂, E₃ b = 0 := fun b hb => Submodule.projection_apply_of_mem_right h3 hb
  have m1 : ∀ y, LinearMap.toMatrix' E₁ *ᵥ y = E₁ y := fun y => LinearMap.toMatrix'_mulVec E₁ y
  have m3 : ∀ y, LinearMap.toMatrix' E₃ *ᵥ y = E₃ y := fun y => LinearMap.toMatrix'_mulVec E₃ y
  have m2 : ∀ y, (1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃ : Mx) *ᵥ y = y - E₁ y - E₃ y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, m1, m3]
  refine ⟨LinearMap.toMatrix' E₁, 1 - LinearMap.toMatrix' E₁ - LinearMap.toMatrix' E₃, LinearMap.toMatrix' E₃,
    by abel, fun y => ?_, fun y => ?_, fun y => ?_, fun y hy => ?_, fun y hy => ?_, fun y hy => ?_,
    fun y hy => ?_, fun y hy => ?_⟩
  · rw [m1]; exact Submodule.projection_apply_mem h1 y
  · rw [m2]
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_sum_along_flag c₁ c₂ y
    have f1 : E₁ (a + b + c) = a := by
      rw [map_add, map_add, e1 a ha, e1' b (Submodule.mem_sup_left hb),
        e1' c (Submodule.mem_sup_right hc), add_zero, add_zero]
    have f3 : E₃ (a + b + c) = c := by
      rw [map_add, map_add, e3' a (hle₁ ha), e3' b (hle₂ hb), e3 c hc, zero_add, zero_add]
    rw [f1, f3, show a + b + c - a - c = b by abel]
    exact hb
  · rw [m3]; exact Submodule.projection_apply_mem h3 y
  · rw [m3]; exact e3' y hy
  · rw [m2, e1 y hy, e3' y (hle₁ hy)]; simp
  · rw [m1]; exact e1' y (Submodule.mem_sup_left hy)
  · rw [m1]; exact e1' y (Submodule.mem_sup_right hy)
  · rw [m2, e1' y (Submodule.mem_sup_right hy), e3 y hy]; simp

end Levi

end GlobalTheory.CompanionTheory.QuotVan
end

noncomputable section

open Matrix MeasureTheory PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D4 PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.QuotVan

section Decomp

variable {n : ℕ}

local notation "Mx" => Matrix (Fin n) (Fin n) ℂ
local notation "Sb" => Submodule ℂ (Fin n → ℂ)

open GlobalTheory.CompanionTheory.NilChangeVar (eq_zero_of_mulVec)

/- English proof (translation)
Take `⟨P₁, P₂, P₃, hs, r₁, r₂, r₃, k₃, k₂, k₁₂, k₁₃, k₂₃⟩` from `exists_proj c₁ d₁ c₂ d₂`. Establish `hle₁ : W₁ ≤ W₂` using `c₁ ▸ le_sup_left`. Establish `hle₂ : V₂ ≤ W₂` using `c₁ ▸ le_sup_right`. Establish `mv : ∀ (A B : Mx) y, (A * B) *ᵥ y = A *ᵥ (B *ᵥ y)` using `fun A B y => (Matrix.mulVec_mulVec _ _ _).symm`. Establish `o12 : P₁ * P₂ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₂ _ (r₂ y)`.

Establish `o13 : P₁ * P₃ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₃ _ (r₃ y)`. Establish `o21 : P₂ * P₁ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₂ _ (r₁ y)`. Establish `o23 : P₂ * P₃ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₂₃ _ (r₃ y)`. Establish `o31 : P₃ * P₁ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₁ (r₁ y))`. Establish `o32 : P₃ * P₂ = 0` using `eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₂ (r₂ y))`.

Establish `tri : ∀ A : Mx, (∀ y ∈ W₁, A *ᵥ y ∈ W₁) → (∀ y ∈ W₂, A *ᵥ y ∈ W₂) → P₂ * A * P₁ = 0 ∧ P₃ * A * P₁ = 0 ∧ P₃ * A * P₂ = 0` using `fun A h₁ h₂ => ⟨eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₂ _ (h₁ _ (r₁ y)), eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (hle₁ (h₁ _ (r₁ y))), eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (h₂ _ (hle₂ (r₂ y)))⟩`. Take `⟨a21, a31, a32⟩` from `tri q.val (fun y hy => mulVec_mem_of_img q hq₁ hy) (fun y hy => mulVec_mem_of_img q hq₂ hy)`. Take `⟨b21, b31, b32⟩` from `tri (q⁻¹ : GL (Fin n) ℂ).val (fun y hy => inv_mulVec_mem_of_img q hq₁ hy) (fun y hy => inv_mulVec_mem_of_img q hq₂ hy)`. Set `L : Mx → Mx` to `lev P₁ P₂ P₃`. Establish `Lv : ∀ A y, L A *ᵥ y = P₁ *ᵥ (A *ᵥ (P₁ *ᵥ y)) + P₂ *ᵥ (A *ᵥ (P₂ *ᵥ y)) + P₃ *ᵥ (A *ᵥ (P₃ *ᵥ y))` using `fun A y => by`.

Simplify using `only [L, lev, Matrix.add_mulVec, mv]`. Establish `L1 : ∀ A, ∀ y ∈ W₁, L A *ᵥ y ∈ W₁` using `fun A y hy => by`. Rewrite using `[Lv, k₂ y hy, k₃ y (hle₁ hy)]`. Simplify using `only [Matrix.mulVec_zero, add_zero]`. Conclude with `r₁ _`.

Establish `L2 : ∀ A, ∀ y ∈ W₂, L A *ᵥ y ∈ W₂` using `fun A y hy => by`. Rewrite using `[Lv, k₃ y hy]`. Simplify using `only [Matrix.mulVec_zero, add_zero]`. Conclude with `W₂.add_mem (hle₁ (r₁ _)) (hle₂ (r₂ _))`. Establish `LV2 : ∀ A, ∀ y ∈ V₂, L A *ᵥ y ∈ V₂` using `fun A y hy => by`.

Rewrite using `[Lv, k₁₂ y hy, k₃ y (hle₂ hy)]`. Simplify using `only [Matrix.mulVec_zero, add_zero, zero_add]`. Conclude with `r₂ _`. Establish `LV3 : ∀ A, ∀ y ∈ V₃, L A *ᵥ y ∈ V₃` using `fun A y hy => by`. Rewrite using `[Lv, k₁₃ y hy, k₂₃ y hy]`.

Simplify using `only [Matrix.mulVec_zero, zero_add]`. Conclude with `r₃ _`. Establish `hmm' : L q.val * L (q⁻¹ : GL (Fin n) ℂ).val = 1` using `lev_mul hs o12 o13 o21 o23 o31 o32 (Units.mul_inv q) a21 a31 a32 b21 b32 b31`. Establish `hm'm : L (q⁻¹ : GL (Fin n) ℂ).val * L q.val = 1` using `lev_mul hs o12 o13 o21 o23 o31 o32 (Units.inv_mul q) b21 b31 b32 a21 a32 a31`. Set `m : GL (Fin n) ℂ` to `⟨L q.val, L (q⁻¹ : GL (Fin n) ℂ).val, hmm', hm'm⟩`.

Establish `hmv : m.val = L q.val` using `rfl`. Establish `hmi : (m⁻¹ : GL (Fin n) ℂ).val = L (q⁻¹ : GL (Fin n) ℂ).val` using `rfl`. Use `⟨q * m⁻¹, m, by group, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Establish `e : (q * m⁻¹).val - 1 = (q.val - L q.val) * L (q⁻¹ : GL (Fin n) ℂ).val`. Rewrite using `[Units.val_mul, hmi, sub_mul, hmm']`.

Establish `hD : q.val - L q.val = P₁ * q.val * P₂ + P₁ * q.val * P₃ + P₂ * q.val * P₃` using `eq_lev_add hs a21 a31 a32`. Establish `Dv : ∀ y, (q.val - L q.val) *ᵥ y = P₁ *ᵥ (q.val *ᵥ (P₂ *ᵥ y)) + P₁ *ᵥ (q.val *ᵥ (P₃ *ᵥ y)) + P₂ *ᵥ (q.val *ᵥ (P₃ *ᵥ y))` using `fun y => by`. Rewrite using `[hD]`. Simplify using `only [Matrix.add_mulVec, mv]`. Rewrite using `[e]`.

Use `⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[mv, Dv]`. Conclude with `W₂.add_mem (W₂.add_mem (hle₁ (r₁ _)) (hle₁ (r₁ _))) (hle₂ (r₂ _))`. Rewrite using `[mv, Dv, k₃ _ (L2 _ y hy)]`. Simplify using `only [Matrix.mulVec_zero, add_zero]`.

Conclude with `r₁ _`. Rewrite using `[mv, Dv, k₃ _ (hle₁ (L1 _ y hy)), k₂ _ (L1 _ y hy)]`. Simplify using the standard rewrite rules. Conclude with `img_eq_of_mapsTo m W₁ (L1 _) (L1 _)`. Conclude with `img_eq_of_mapsTo m W₂ (L2 _) (L2 _)`.

Conclude with `img_eq_of_mapsTo m V₂ (LV2 _) (LV2 _)`. Conclude with `img_eq_of_mapsTo m V₃ (LV3 _) (LV3 _)`.
-/
theorem levi_decomp {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) (q : GL (Fin n) ℂ) (hq₁ : img q W₁ = W₁) (hq₂ : img q W₂ = W₂) :
    ∃ u m : GL (Fin n) ℂ, q = u * m ∧ u.val - 1 ∈ nilrad W₁ W₂ ∧ img m W₁ = W₁ ∧ img m W₂ = W₂ ∧
      img m V₂ = V₂ ∧ img m V₃ = V₃ := by
  obtain ⟨P₁, P₂, P₃, hs, r₁, r₂, r₃, k₃, k₂, k₁₂, k₁₃, k₂₃⟩ := exists_proj c₁ d₁ c₂ d₂
  have hle₁ : W₁ ≤ W₂ := c₁ ▸ le_sup_left
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have mv : ∀ (A B : Mx) y, (A * B) *ᵥ y = A *ᵥ (B *ᵥ y) := fun A B y => (Matrix.mulVec_mulVec _ _ _).symm
  have o12 : P₁ * P₂ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₂ _ (r₂ y)
  have o13 : P₁ * P₃ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₁₃ _ (r₃ y)
  have o21 : P₂ * P₁ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₂ _ (r₁ y)
  have o23 : P₂ * P₃ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₂₃ _ (r₃ y)
  have o31 : P₃ * P₁ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₁ (r₁ y))
  have o32 : P₃ * P₂ = 0 := eq_zero_of_mulVec fun y => by rw [mv]; exact k₃ _ (hle₂ (r₂ y))
  have tri : ∀ A : Mx, (∀ y ∈ W₁, A *ᵥ y ∈ W₁) → (∀ y ∈ W₂, A *ᵥ y ∈ W₂) →
      P₂ * A * P₁ = 0 ∧ P₃ * A * P₁ = 0 ∧ P₃ * A * P₂ = 0 := fun A h₁ h₂ =>
    ⟨eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₂ _ (h₁ _ (r₁ y)),
     eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (hle₁ (h₁ _ (r₁ y))),
     eq_zero_of_mulVec fun y => by rw [mv, mv]; exact k₃ _ (h₂ _ (hle₂ (r₂ y)))⟩
  obtain ⟨a21, a31, a32⟩ := tri q.val (fun y hy => mulVec_mem_of_img q hq₁ hy)
    (fun y hy => mulVec_mem_of_img q hq₂ hy)
  obtain ⟨b21, b31, b32⟩ := tri (q⁻¹ : GL (Fin n) ℂ).val (fun y hy => inv_mulVec_mem_of_img q hq₁ hy)
    (fun y hy => inv_mulVec_mem_of_img q hq₂ hy)
  let L : Mx → Mx := lev P₁ P₂ P₃
  have Lv : ∀ A y, L A *ᵥ y = P₁ *ᵥ (A *ᵥ (P₁ *ᵥ y)) + P₂ *ᵥ (A *ᵥ (P₂ *ᵥ y)) + P₃ *ᵥ (A *ᵥ (P₃ *ᵥ y)) := fun A y => by
    simp only [L, lev, Matrix.add_mulVec, mv]
  have L1 : ∀ A, ∀ y ∈ W₁, L A *ᵥ y ∈ W₁ := fun A y hy => by
    rw [Lv, k₂ y hy, k₃ y (hle₁ hy)]
    simp only [Matrix.mulVec_zero, add_zero]
    exact r₁ _
  have L2 : ∀ A, ∀ y ∈ W₂, L A *ᵥ y ∈ W₂ := fun A y hy => by
    rw [Lv, k₃ y hy]
    simp only [Matrix.mulVec_zero, add_zero]
    exact W₂.add_mem (hle₁ (r₁ _)) (hle₂ (r₂ _))
  have LV2 : ∀ A, ∀ y ∈ V₂, L A *ᵥ y ∈ V₂ := fun A y hy => by
    rw [Lv, k₁₂ y hy, k₃ y (hle₂ hy)]
    simp only [Matrix.mulVec_zero, add_zero, zero_add]
    exact r₂ _
  have LV3 : ∀ A, ∀ y ∈ V₃, L A *ᵥ y ∈ V₃ := fun A y hy => by
    rw [Lv, k₁₃ y hy, k₂₃ y hy]
    simp only [Matrix.mulVec_zero, zero_add]
    exact r₃ _
  have hmm' : L q.val * L (q⁻¹ : GL (Fin n) ℂ).val = 1 :=
    lev_mul hs o12 o13 o21 o23 o31 o32 (Units.mul_inv q) a21 a31 a32 b21 b32 b31
  have hm'm : L (q⁻¹ : GL (Fin n) ℂ).val * L q.val = 1 :=
    lev_mul hs o12 o13 o21 o23 o31 o32 (Units.inv_mul q) b21 b31 b32 a21 a32 a31
  let m : GL (Fin n) ℂ := ⟨L q.val, L (q⁻¹ : GL (Fin n) ℂ).val, hmm', hm'm⟩
  have hmv : m.val = L q.val := rfl
  have hmi : (m⁻¹ : GL (Fin n) ℂ).val = L (q⁻¹ : GL (Fin n) ℂ).val := rfl
  refine ⟨q * m⁻¹, m, by group, ?_, ?_, ?_, ?_, ?_⟩
  · have e : (q * m⁻¹).val - 1 = (q.val - L q.val) * L (q⁻¹ : GL (Fin n) ℂ).val := by
      rw [Units.val_mul, hmi, sub_mul, hmm']
    have hD : q.val - L q.val = P₁ * q.val * P₂ + P₁ * q.val * P₃ + P₂ * q.val * P₃ :=
      eq_lev_add hs a21 a31 a32
    have Dv : ∀ y, (q.val - L q.val) *ᵥ y = P₁ *ᵥ (q.val *ᵥ (P₂ *ᵥ y)) + P₁ *ᵥ (q.val *ᵥ (P₃ *ᵥ y)) +
        P₂ *ᵥ (q.val *ᵥ (P₃ *ᵥ y)) := fun y => by
      rw [hD]; simp only [Matrix.add_mulVec, mv]
    rw [e]
    refine ⟨fun y => ?_, fun y hy => ?_, fun y hy => ?_⟩
    · rw [mv, Dv]
      exact W₂.add_mem (W₂.add_mem (hle₁ (r₁ _)) (hle₁ (r₁ _))) (hle₂ (r₂ _))
    · rw [mv, Dv, k₃ _ (L2 _ y hy)]
      simp only [Matrix.mulVec_zero, add_zero]
      exact r₁ _
    · rw [mv, Dv, k₃ _ (hle₁ (L1 _ y hy)), k₂ _ (L1 _ y hy)]
      simp
  · exact img_eq_of_mapsTo m W₁ (L1 _) (L1 _)
  · exact img_eq_of_mapsTo m W₂ (L2 _) (L2 _)
  · exact img_eq_of_mapsTo m V₂ (LV2 _) (LV2 _)
  · exact img_eq_of_mapsTo m V₃ (LV3 _) (LV3 _)

/- English proof (translation)
Establish `hle₂ : V₂ ≤ W₂` using `c₁ ▸ le_sup_right`. Establish `e : ∀ y, (g.val - 1) *ᵥ y = g.val *ᵥ y - y` using `fun y => by`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec]`. Establish `hz : g.val - 1 = 0` using `eq_zero_of_mulVec fun y => by`. Take `⟨a, ha, b, hb, c, hc, rfl⟩` from `exists_sum_along_flag c₁ c₂ y`.

Establish `f1 : (g.val - 1) *ᵥ a = 0` using `hX.2.2 a ha`. Establish `f2 : (g.val - 1) *ᵥ b = 0`. Establish `m1 : (g.val - 1) *ᵥ b ∈ W₁ ⊓ V₂` using `⟨hX.2.1 b (hle₂ hb), by`. Rewrite using `[e]`. Conclude with `V₂.sub_mem (mulVec_mem_of_img g h₂ hb) hb⟩`.

Rewrite `m1` using `[d₁]`. Simplify using `using m1`. Establish `f3 : (g.val - 1) *ᵥ c = 0`. Establish `m1 : (g.val - 1) *ᵥ c ∈ W₂ ⊓ V₃` using `⟨hX.1 c, by`. Rewrite using `[e]`.

Conclude with `V₃.sub_mem (mulVec_mem_of_img g h₃ hc) hc⟩`. Rewrite `m1` using `[d₂]`. Simplify using `using m1`. Rewrite using `[Matrix.mulVec_add, Matrix.mulVec_add, f1, f2, f3]`. Simplify using the standard rewrite rules.

Conclude with `Units.ext (by simpa [sub_eq_zero] using hz)`.
-/
theorem levi_inf {W₁ W₂ V₂ V₃ : Sb} (c₁ : W₁ ⊔ V₂ = W₂) (d₁ : W₁ ⊓ V₂ = ⊥) (c₂ : W₂ ⊔ V₃ = ⊤)
    (d₂ : W₂ ⊓ V₃ = ⊥) (g : GL (Fin n) ℂ) (hX : g.val - 1 ∈ nilrad W₁ W₂) (h₂ : img g V₂ = V₂)
    (h₃ : img g V₃ = V₃) : g = 1 := by
  have hle₂ : V₂ ≤ W₂ := c₁ ▸ le_sup_right
  have e : ∀ y, (g.val - 1) *ᵥ y = g.val *ᵥ y - y := fun y => by
    rw [Matrix.sub_mulVec, Matrix.one_mulVec]
  have hz : g.val - 1 = 0 := eq_zero_of_mulVec fun y => by
    obtain ⟨a, ha, b, hb, c, hc, rfl⟩ := exists_sum_along_flag c₁ c₂ y
    have f1 : (g.val - 1) *ᵥ a = 0 := hX.2.2 a ha
    have f2 : (g.val - 1) *ᵥ b = 0 := by
      have m1 : (g.val - 1) *ᵥ b ∈ W₁ ⊓ V₂ := ⟨hX.2.1 b (hle₂ hb), by
        rw [e]; exact V₂.sub_mem (mulVec_mem_of_img g h₂ hb) hb⟩
      rw [d₁] at m1
      simpa using m1
    have f3 : (g.val - 1) *ᵥ c = 0 := by
      have m1 : (g.val - 1) *ᵥ c ∈ W₂ ⊓ V₃ := ⟨hX.1 c, by
        rw [e]; exact V₃.sub_mem (mulVec_mem_of_img g h₃ hc) hc⟩
      rw [d₂] at m1
      simpa using m1
    rw [Matrix.mulVec_add, Matrix.mulVec_add, f1, f2, f3]
    simp
  exact Units.ext (by simpa [sub_eq_zero] using hz)

end Decomp

end GlobalTheory.CompanionTheory.QuotVan
end
