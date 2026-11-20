import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.Aa
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.EqAmOfBarEq
import Development.AutomorphicSpectrum.Proofs.MembershipProofs.ThetaDistributionHeisenbergInvariant
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EqZeroOfCoefficientsSeparatingCharactersEqZero
import GroundTheory.GlobalFields.TateThesis.AdelicCharDual

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical ENNReal NNReal
open UpperTheory.ConvolutionTheory.R2.G (FS2 Rw nE row)

/- English proof (translation)
The claim follows from `adeleMeasure_fundamentalSet ℚ`.
-/
private theorem vol_FS : adeleMeasure ℚ (fundamentalSet ℚ) = 1 := adeleMeasure_fundamentalSet ℚ

private instance finFS : IsFiniteMeasure ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) :=
  ⟨by rw [Measure.restrict_apply_univ, vol_FS]; exact ENNReal.one_lt_top⟩

/- English proof (translation)
Take `⟨C, hC, hs⟩` from `Pp.exists_cpt (F := ℚ)`. Conclude with `(hg.continuousOn.integrableOn_compact hC).mono_set hs`.
-/
private theorem int_cont {g : A ℚ → ℂ} (hg : Continuous g) : IntegrableOn g (fundamentalSet ℚ) (adeleMeasure ℚ) := by
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  exact (hg.continuousOn.integrableOn_compact hC).mono_set hs

/- English proof (translation)
The claim follows from `Pp.cont_ψ.comp (continuous_const.mul continuous_id)`.
-/
private theorem cont_psi_mul (a : ℚ) : Continuous fun v : A ℚ => ψ (rt a * v) :=
  Pp.cont_ψ.comp (continuous_const.mul continuous_id)

/- English proof (translation)
Rewrite using `[mul_add, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]`.
-/
private theorem psi_rt_mul_per (a k : ℚ) (v : A ℚ) : ψ (rt a * (rt k + v)) = ψ (rt a * v) := by
  rw [mul_add, Pp.ψ_add, ← map_mul, Pp.ψ_rt, one_mul]

/- English proof (translation)
Use `split_ifs with h`. Substitute `h` using the available equality. Simplify using `[Pp.ψ_rt, ψ, Measure.real, vol_FS]`. Establish `hne : adelicChar ℚ ≠ 1` using `adelicChar_ne_one`. Choose the witnesses or unpack the hypotheses as in `⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Conclude with `hne (DFunLike.ext _ _ fun x => by`. Rewrite using `[AddChar.one_apply]`. Conclude with `Circle.coe_injective (by simpa [ψ] using hc x))`.

Establish `h1` using `Pp.int_add (h := fun v => ψ (rt γ * v)) (fun k x => psi_rt_mul_per γ k x) (rt γ⁻¹ * a)`. Establish `e : ∀ b : A ℚ, ψ (rt γ * (b + rt γ⁻¹ * a)) = ψ a * ψ (rt γ * b)`. Introduce `b`. Rewrite using `[mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h, map_one, one_mul, Pp.ψ_add, mul_comm]`. Simplify using `only [e] at h1`.

Rewrite `h1` using `[integral_const_mul]`. Establish `h3 : (ψ a - 1) * ∫ v in fundamentalSet ℚ, ψ (rt γ * v) ∂(adeleMeasure ℚ) = 0`. Rewrite using `[sub_mul, h1, one_mul, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)`.
-/
private theorem int_psi (γ : ℚ) :
    ∫ v in fundamentalSet ℚ, ψ (rt γ * v) ∂(adeleMeasure ℚ) = if γ = 0 then 1 else 0 := by
  split_ifs with h
  · subst h
    simp [Pp.ψ_rt, ψ, Measure.real, vol_FS]
  · have hne : adelicChar ℚ ≠ 1 := adelicChar_ne_one
    obtain ⟨a, ha⟩ : ∃ a, ψ a ≠ 1 := by
      by_contra hc
      push Not at hc
      exact hne (DFunLike.ext _ _ fun x => by
        rw [AddChar.one_apply]
        exact Circle.coe_injective (by simpa [ψ] using hc x))
    have h1 := Pp.int_add (h := fun v => ψ (rt γ * v)) (fun k x => psi_rt_mul_per γ k x) (rt γ⁻¹ * a)
    have e : ∀ b : A ℚ, ψ (rt γ * (b + rt γ⁻¹ * a)) = ψ a * ψ (rt γ * b) := by
      intro b
      rw [mul_add, ← mul_assoc, ← map_mul, mul_inv_cancel₀ h, map_one, one_mul, Pp.ψ_add, mul_comm]
    simp only [e] at h1
    rw [integral_const_mul] at h1
    have h3 : (ψ a - 1) * ∫ v in fundamentalSet ℚ, ψ (rt γ * v) ∂(adeleMeasure ℚ) = 0 := by
      rw [sub_mul, h1, one_mul, sub_self]
    exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 ha)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Set `χ : AddChar (A ℚ) Circle` to `{ toFun := fun y => adelicChar ℚ (x * y) map_zero_eq_one' := by simp map_add_eq_mul' := fun a b => by rw [mul_add, AddChar.map_add_eq_mul] }`. Establish `hχ : Continuous χ` using `(continuous_adelicChar (K := ℚ)).comp (continuous_const.mul continuous_id)`. Establish `hk : ∀ k : ℚ, χ (algebraMap ℚ (A ℚ) k) = 1` using `fun k => by`.

Use `h k` as an intermediate fact. Use `Circle.coe_injective ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `ψ (x * rt k) = _`. Rewrite using `[mul_comm, this]`. Simplify using the standard rewrite rules.

Take `⟨ξ, hξ, -⟩` from `existsUnique_eq_adelicChar_mul χ hχ hk`. Use `⟨ξ, ?_⟩` and prove the remaining obligations. Establish `h0 : x - rt ξ = 0` using `GlobalTheory.CompanionTheory.AdeleAnn.eq_zero_of_forall_adelicChar_mul fun z => by`. Use `hξ z` as an intermediate fact. Express the relevant statement in the definitionally equal form `adelicChar ℚ (x * z) = adelicChar ℚ (rt ξ * z) at this`.

Rewrite using `[sub_mul, AddChar.map_sub_eq_div, this, div_self']`. Conclude with `(sub_eq_zero.1 h0).symm`. Introduce and unpack `⟨k, rfl⟩ a`. Express the relevant statement in the definitionally equal form `ψ (rt a * rt k) = 1`. Rewrite using `[← map_mul, Pp.ψ_rt]`.
-/
private theorem ker_psi (x : A ℚ) : (∀ a : ℚ, ψ (rt a * x) = 1) ↔ x ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ := by
  constructor
  · intro h
    let χ : AddChar (A ℚ) Circle :=
      { toFun := fun y => adelicChar ℚ (x * y)
        map_zero_eq_one' := by simp
        map_add_eq_mul' := fun a b => by rw [mul_add, AddChar.map_add_eq_mul] }
    have hχ : Continuous χ := (continuous_adelicChar (K := ℚ)).comp (continuous_const.mul continuous_id)
    have hk : ∀ k : ℚ, χ (algebraMap ℚ (A ℚ) k) = 1 := fun k => by
      have := h k
      refine Circle.coe_injective ?_
      change ψ (x * rt k) = _
      rw [mul_comm, this]; simp
    obtain ⟨ξ, hξ, -⟩ := existsUnique_eq_adelicChar_mul χ hχ hk
    refine ⟨ξ, ?_⟩
    have h0 : x - rt ξ = 0 := GlobalTheory.CompanionTheory.AdeleAnn.eq_zero_of_forall_adelicChar_mul fun z => by
      have := hξ z
      change adelicChar ℚ (x * z) = adelicChar ℚ (rt ξ * z) at this
      rw [sub_mul, AddChar.map_sub_eq_div, this, div_self']
    exact (sub_eq_zero.1 h0).symm
  · rintro ⟨k, rfl⟩ a
    change ψ (rt a * rt k) = 1
    rw [← map_mul, Pp.ψ_rt]

/- English proof (translation)
Use `haveI := discreteTopology_principalSubgroup ℚ`. Take `⟨C, hC, hs⟩` from `Pp.exists_cpt (F := ℚ)`. Establish `hcov : ∀ x : A ℚ, ∃ γ ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ, γ + x ∈ C`. Introduce `x`. Take `⟨k, hk, -⟩` from `existsUnique_sub_mem_fundamentalSet ℚ x`.

Use `⟨rt (-k), ⟨-k, rfl⟩, hs ?_⟩` and prove the remaining obligations. Establish `e : rt (-k) + x = x - algebraMap ℚ (A ℚ) k`. Express the relevant statement in the definitionally equal form `algebraMap ℚ (A ℚ) (-k) + x = _`. Rewrite using `[map_neg]`. Normalize the expressions using the abelian group laws.

Rewrite using `[e]`. Conclude with `hk`. Use `GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (A ℚ) (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) C hC hcov ℚ (fun a v => ψ (rt a * v)) cont_psi_mul ?_ ?_ ?_ (fun a x => Pp.norm_ψ _) ker_psi (adeleMeasure ℚ) (fundamentalSet ℚ) inferInstance (isAddFundamentalDomain_fun …` and prove the remaining obligations. Introduce `a x y`. Rewrite using `[mul_add, Pp.ψ_add]`.

Introduce `a b x`. Simplify using `only [map_add, add_mul, Pp.ψ_add]`. Introduce `x`. Simplify using `[ψ]`. Introduce and unpack `_ ⟨k, rfl⟩ x`.

Conclude with `hp k x`.
-/
private theorem eq_zero_of_coeff (Φ : A ℚ → ℂ) (hc : Continuous Φ) (hp : ∀ (k : ℚ) x, Φ (rt k + x) = Φ x)
    (h0 : ∀ a : ℚ, ∫ v in fundamentalSet ℚ, ψ (rt a * v) * Φ v ∂(adeleMeasure ℚ) = 0) : Φ = 0 := by
  haveI := discreteTopology_principalSubgroup ℚ
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  have hcov : ∀ x : A ℚ, ∃ γ ∈ AdeleRing.principalSubgroup (𝓞 ℚ) ℚ, γ + x ∈ C := by
    intro x
    obtain ⟨k, hk, -⟩ := existsUnique_sub_mem_fundamentalSet ℚ x
    refine ⟨rt (-k), ⟨-k, rfl⟩, hs ?_⟩
    have e : rt (-k) + x = x - algebraMap ℚ (A ℚ) k := by
      change algebraMap ℚ (A ℚ) (-k) + x = _
      rw [map_neg]
      abel
    rw [e]
    exact hk
  refine GlobalTheory.SeparatingCharacters.eq_zero_of_coefficients_eq_zero (A ℚ) (AdeleRing.principalSubgroup (𝓞 ℚ) ℚ) C hC hcov ℚ
    (fun a v => ψ (rt a * v)) cont_psi_mul ?_ ?_ ?_ (fun a x => Pp.norm_ψ _) ker_psi (adeleMeasure ℚ) (fundamentalSet ℚ)
    inferInstance (isAddFundamentalDomain_fundamentalSet ℚ) Φ hc ?_ h0
  · intro a x y
    rw [mul_add, Pp.ψ_add]
  · intro a b x
    simp only [map_add, add_mul, Pp.ψ_add]
  · intro x
    simp [ψ]
  · rintro _ ⟨k, rfl⟩ x
    exact hp k x

/- English proof (translation)
Use `set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ) with hcdef`. Establish `hsn : Summable fun α => ‖c α‖` using `hs.norm`. Set `T : ℚ → A ℚ → ℂ` to `fun α v => c α * ψ (-(rt α * v))`. Establish `hTc : ∀ α, Continuous (T α)` using `fun α => continuous_const.mul (Pp.cont_ψ.comp (continuous_const.mul continuous_id).neg)`. Establish `hTn : ∀ α v, ‖T α v‖ = ‖c α‖` using `fun α v => by`.

Simplify using `only [T, norm_mul, Pp.norm_ψ, mul_one]`. Set `G : A ℚ → ℂ` to `fun v => ∑' α, T α v`. Establish `hGc : Continuous G` using `continuous_tsum hTc hsn fun α v => (hTn α v).le`. Establish `hGp : ∀ (k : ℚ) x, G (rt k + x) = G x`. Introduce `k x`.

Use `tsum_congr fun α => ?_` and prove the remaining obligations. Simplify using `only [T]`. Use `congr 1`. Rewrite using `[mul_add, neg_add, Pp.ψ_add, ← map_mul, ← map_neg, Pp.ψ_rt, one_mul]`. Establish `hG0 : HasSum c (G 0)`.

Establish `h1 : Summable fun α => T α 0`. Use `Summable.of_norm ?_` and prove the remaining obligations. Simplify `hsn` using `only [hTn]`. Establish `h2 : HasSum (fun α => T α 0) (G 0)` using `h1.hasSum`. Establish `e : (fun α => T α 0) = c`.

Use function extensionality and compare the values at `α`. Simplify using `[T, ψ]`. Rewrite `h2` using `[e]`. Then use the resulting hypothesis. Establish `hcoef : ∀ β, ∫ v in fundamentalSet ℚ, ψ (rt β * v) * G v ∂(adeleMeasure ℚ) = c β`. Introduce `β`.

Set `Fn : ℚ → A ℚ → ℂ` to `fun α v => ψ (rt β * v) * T α v`. Establish `hFc : ∀ α, Continuous (Fn α)` using `fun α => (cont_psi_mul β).mul (hTc α)`. Establish `hFn : ∀ α v, ‖Fn α v‖ = ‖c α‖` using `fun α v => by`. Simplify using `only [Fn, norm_mul, Pp.norm_ψ, one_mul, hTn]`. Establish `hFi : ∀ α, Integrable (Fn α) ((adeleMeasure ℚ).restrict (fundamentalSet ℚ))` using `fun α => Integrable.of_bound (C := ‖c α‖) (hFc α).aestronglyMeasurable (ae_of_all _ fun v => (hFn α v).le)`.

Establish `hint : ∀ α, ∫ v, ‖Fn α v‖ ∂((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) = ‖c α‖` using `fun α => by`. Simplify using `only [hFn]`. Simplify using `[Measure.real, vol_FS]`. Establish `hsum` using `hasSum_integral_of_summable_integral_norm hFi (by simpa only [hint] using hsn)`. Establish `e1 : ∀ v, ∑' α, Fn α v = ψ (rt β * v) * G v` using `fun v => tsum_mul_left`.

Simplify using `only [e1] at hsum`. Establish `e2 : ∀ α, ∫ v in fundamentalSet ℚ, Fn α v ∂(adeleMeasure ℚ) = if α = β then c β else 0`. Introduce `α`. Establish `e3 : ∀ v, Fn α v = c α * ψ (rt (β - α) * v)` using `fun v => by`. Establish `e4 : rt (β - α) * v = rt β * v + -(rt α * v)`.

Rewrite using `[show rt (β - α) = rt β - rt α from map_sub _ _ _]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `only [Fn, T]`. Rewrite using `[e4, Pp.ψ_add]`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [e3]`. Rewrite using `[integral_const_mul, int_psi]`. Distinguish the cases in `h : α = β`. Substitute `h` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h)), mul_zero]`. Simplify using `only [e2] at hsum`. Conclude with `hsum.unique (hasSum_ite_eq β (c β))`. Establish `hz : (fun v => f v - G v) = 0`. Use `eq_zero_of_coeff _ (hc.sub hGc) (fun k x => by rw [hp, hGp]) fun a => ?_` and prove the remaining obligations.

Establish `hi1 : IntegrableOn (fun v => ψ (rt a * v) * f v) (fundamentalSet ℚ) (adeleMeasure ℚ)` using `int_cont ((cont_psi_mul a).mul hc)`. Establish `hi2 : IntegrableOn (fun v => ψ (rt a * v) * G v) (fundamentalSet ℚ) (adeleMeasure ℚ)` using `int_cont ((cont_psi_mul a).mul hGc)`. Simplify using `only [mul_sub]`. Rewrite using `[integral_sub hi1 hi2, hcoef, sub_self]`. Establish `h0` using `congrFun hz 0`.

Simplify using `only [Pi.zero_apply, sub_eq_zero] at h0`. Rewrite using `[h0]`. Conclude with `hG0`.
-/
private theorem inv_of_summable (f : A ℚ → ℂ) (hc : Continuous f) (hp : ∀ (k : ℚ) x, f (rt k + x) = f x)
    (hs : Summable fun α : ℚ => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ)) :
    HasSum (fun α : ℚ => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ)) (f 0) := by
  set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * f v ∂(adeleMeasure ℚ) with hcdef
  have hsn : Summable fun α => ‖c α‖ := hs.norm
  let T : ℚ → A ℚ → ℂ := fun α v => c α * ψ (-(rt α * v))
  have hTc : ∀ α, Continuous (T α) := fun α =>
    continuous_const.mul (Pp.cont_ψ.comp (continuous_const.mul continuous_id).neg)
  have hTn : ∀ α v, ‖T α v‖ = ‖c α‖ := fun α v => by
    simp only [T, norm_mul, Pp.norm_ψ, mul_one]
  let G : A ℚ → ℂ := fun v => ∑' α, T α v
  have hGc : Continuous G := continuous_tsum hTc hsn fun α v => (hTn α v).le
  have hGp : ∀ (k : ℚ) x, G (rt k + x) = G x := by
    intro k x
    refine tsum_congr fun α => ?_
    simp only [T]
    congr 1
    rw [mul_add, neg_add, Pp.ψ_add, ← map_mul, ← map_neg, Pp.ψ_rt, one_mul]
  have hG0 : HasSum c (G 0) := by
    have h1 : Summable fun α => T α 0 := by
      refine Summable.of_norm ?_
      simpa only [hTn] using hsn
    have h2 : HasSum (fun α => T α 0) (G 0) := h1.hasSum
    have e : (fun α => T α 0) = c := by
      funext α
      simp [T, ψ]
    rwa [e] at h2
  have hcoef : ∀ β, ∫ v in fundamentalSet ℚ, ψ (rt β * v) * G v ∂(adeleMeasure ℚ) = c β := by
    intro β
    let Fn : ℚ → A ℚ → ℂ := fun α v => ψ (rt β * v) * T α v
    have hFc : ∀ α, Continuous (Fn α) := fun α => (cont_psi_mul β).mul (hTc α)
    have hFn : ∀ α v, ‖Fn α v‖ = ‖c α‖ := fun α v => by
      simp only [Fn, norm_mul, Pp.norm_ψ, one_mul, hTn]
    have hFi : ∀ α, Integrable (Fn α) ((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) := fun α =>
      Integrable.of_bound (C := ‖c α‖) (hFc α).aestronglyMeasurable (ae_of_all _ fun v => (hFn α v).le)
    have hint : ∀ α, ∫ v, ‖Fn α v‖ ∂((adeleMeasure ℚ).restrict (fundamentalSet ℚ)) = ‖c α‖ := fun α => by
      simp only [hFn]
      simp [Measure.real, vol_FS]
    have hsum := hasSum_integral_of_summable_integral_norm hFi (by simpa only [hint] using hsn)
    have e1 : ∀ v, ∑' α, Fn α v = ψ (rt β * v) * G v := fun v => tsum_mul_left
    simp only [e1] at hsum
    have e2 : ∀ α, ∫ v in fundamentalSet ℚ, Fn α v ∂(adeleMeasure ℚ) = if α = β then c β else 0 := by
      intro α
      have e3 : ∀ v, Fn α v = c α * ψ (rt (β - α) * v) := fun v => by
        have e4 : rt (β - α) * v = rt β * v + -(rt α * v) := by
          rw [show rt (β - α) = rt β - rt α from map_sub _ _ _]
          ring
        simp only [Fn, T]
        rw [e4, Pp.ψ_add]
        ring
      simp only [e3]
      rw [integral_const_mul, int_psi]
      by_cases h : α = β
      · subst h
        simp
      · rw [if_neg h, if_neg (sub_ne_zero.2 (Ne.symm h)), mul_zero]
    simp only [e2] at hsum
    exact hsum.unique (hasSum_ite_eq β (c β))
  have hz : (fun v => f v - G v) = 0 := by
    refine eq_zero_of_coeff _ (hc.sub hGc) (fun k x => by rw [hp, hGp]) fun a => ?_
    have hi1 : IntegrableOn (fun v => ψ (rt a * v) * f v) (fundamentalSet ℚ) (adeleMeasure ℚ) :=
      int_cont ((cont_psi_mul a).mul hc)
    have hi2 : IntegrableOn (fun v => ψ (rt a * v) * G v) (fundamentalSet ℚ) (adeleMeasure ℚ) :=
      int_cont ((cont_psi_mul a).mul hGc)
    simp only [mul_sub]
    rw [integral_sub hi1 hi2, hcoef, sub_self]
  have h0 := congrFun hz 0
  simp only [Pi.zero_apply, sub_eq_zero] at h0
  rw [h0]
  exact hG0

section Slice

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

/- English proof (translation)
The claim follows from `Pp.cont_n.comp (D.continuous_mkE' continuous_fst continuous_snd)`.
-/
private theorem cont_m : Continuous fun p : A ℚ × A ℚ => gl (nU (D.mkE p.1 p.2)) :=
  Pp.cont_n.comp (D.continuous_mkE' continuous_fst continuous_snd)

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem em_val (g : GL (Fin 2) (A ℚ)) (i j : Fin 2) :
    (UpperTheory.ConvolutionTheory.RankTwoDescent.em E g).val i j = am E (g.val i j) := rfl

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[em_val]`. Express the relevant statement in the definitionally equal form `am E ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) = (!![1, am E b; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem em_nU (b : A ℚ) : UpperTheory.ConvolutionTheory.RankTwoDescent.em E (gl (nU b)) = gl (nU (am E b)) := by
  apply Units.ext
  ext i j
  rw [em_val]
  change am E ((!![1, b; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) = (!![1, am E b; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[em_val]`. Express the relevant statement in the definitionally equal form `am E ((!![(y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) = (!![am E (y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.
-/
private theorem em_aE (y : (A ℚ)ˣ) :
    UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE y) = aE (Units.map (am (F := ℚ) E).toMonoidHom y) := by
  apply Units.ext
  ext i j
  rw [em_val]
  change am E ((!![(y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j) =
    (!![am E (y : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A E)) i j
  fin_cases i <;> fin_cases j <;> simp

private noncomputable def Sl (φ : GL (Fin 2) (A E) → ℂ) (x : GL (Fin 2) (A E)) (v : A ℚ) : ℂ :=
  ∫ b in fundamentalSet ℚ, φ (gl (nU (D.mkE b v)) * x) ∂(adeleMeasure ℚ)

/- English proof (translation)
Simplify using `only [Un.Fb, Sl, em_nU, D.mkE_base]`.
-/
private theorem Fb_eq (φ : GL (Fin 2) (A E) → ℂ) (x : GL (Fin 2) (A E)) : Un.Fb φ x = Sl D φ x 0 := by
  simp only [Un.Fb, Sl, em_nU, D.mkE_base]

/- English proof (translation)
Take `⟨B, hB⟩` from `hb`. Use `continuous_of_dominated (bound := fun _ => B) (fun v => ?_) (fun v => ae_of_all _ fun b => hB _) (integrable_const _) (ae_of_all _ fun b => ?_)` and prove the remaining obligations. Conclude with `(hc.comp (((cont_m D).comp (continuous_id.prodMk continuous_const)).mul continuous_const)).aestronglyMeasurable`. Conclude with `hc.comp (((cont_m D).comp (continuous_const.prodMk continuous_id)).mul continuous_const)`.
-/
private theorem Sl_cont {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (hb : ∃ B : ℝ, ∀ g, ‖φ g‖ ≤ B)
    (x : GL (Fin 2) (A E)) : Continuous (Sl D φ x) := by
  obtain ⟨B, hB⟩ := hb
  refine continuous_of_dominated (bound := fun _ => B) (fun v => ?_)
    (fun v => ae_of_all _ fun b => hB _) (integrable_const _) (ae_of_all _ fun b => ?_)
  · exact (hc.comp (((cont_m D).comp (continuous_id.prodMk continuous_const)).mul continuous_const)).aestronglyMeasurable
  · exact hc.comp (((cont_m D).comp (continuous_const.prodMk continuous_id)).mul continuous_const)

/- English proof (translation)
Simplify using `only [Sl]`. Use `congr 1`. Use function extensionality and compare the values at `b`. Establish `e : D.mkE b (rt k + v) = rt (algebraMap ℚ E 0 + algebraMap ℚ E k * D.θ) + D.mkE b v`. Rewrite using `[← D.mkE_rt, ← D.mkE_add, show (rt 0 : A ℚ) = 0 from map_zero _, zero_add]`.

Rewrite using `[e, hL.per]`.
-/
private theorem Sl_per {φ : GL (Fin 2) (A E) → ℂ} (hL : Pp.Lf φ) (x : GL (Fin 2) (A E)) (k : ℚ) (v : A ℚ) :
    Sl D φ x (rt k + v) = Sl D φ x v := by
  simp only [Sl]
  congr 1
  funext b
  have e : D.mkE b (rt k + v) = rt (algebraMap ℚ E 0 + algebraMap ℚ E k * D.θ) + D.mkE b v := by
    rw [← D.mkE_rt, ← D.mkE_add, show (rt 0 : A ℚ) = 0 from map_zero _, zero_add]
  rw [e, hL.per]

/- English proof (translation)
Use `set ν := (adeleMeasure ℚ).restrict (fundamentalSet ℚ) with hν`. Establish `h1 : (adeleMeasurePi (ι` using `Fin 2) ℚ).restrict (FS2 ℚ) = Measure.pi fun _ : Fin 2 => ν := Measure.restrict_pi_pi _ _`. Rewrite using `[h1]`. Establish `mp` using `measurePreserving_piFinTwo (fun _ : Fin 2 => ν)`. Establish `h2` using `mp.integral_comp' (fun p : A ℚ × A ℚ => H p.1 p.2)`.

Establish `h3 : ∫ u, H (u 0) (u 1) ∂(Measure.pi fun _ : Fin 2 => ν) = ∫ p : A ℚ × A ℚ, H p.1 p.2 ∂(ν.prod ν)` using `h2`. Rewrite using `[h3, integral_prod_symm]`. Take `⟨C, hC, hs⟩` from `Pp.exists_cpt (F := ℚ)`. Rewrite using `[hν, Measure.prod_restrict]`. Conclude with `(hH.continuousOn.integrableOn_compact (hC.prod hC)).mono_set (Set.prod_mono hs hs)`.
-/
private theorem fub (H : A ℚ → A ℚ → ℂ) (hH : Continuous fun p : A ℚ × A ℚ => H p.1 p.2) :
    ∫ u in FS2 ℚ, H (u 0) (u 1) ∂(adeleMeasurePi ℚ) =
      ∫ v in fundamentalSet ℚ, ∫ b in fundamentalSet ℚ, H b v ∂(adeleMeasure ℚ) ∂(adeleMeasure ℚ) := by
  set ν := (adeleMeasure ℚ).restrict (fundamentalSet ℚ) with hν
  have h1 : (adeleMeasurePi (ι := Fin 2) ℚ).restrict (FS2 ℚ) = Measure.pi fun _ : Fin 2 => ν :=
    Measure.restrict_pi_pi _ _
  rw [h1]
  have mp := measurePreserving_piFinTwo (fun _ : Fin 2 => ν)
  have h2 := mp.integral_comp' (fun p : A ℚ × A ℚ => H p.1 p.2)
  have h3 : ∫ u, H (u 0) (u 1) ∂(Measure.pi fun _ : Fin 2 => ν) = ∫ p : A ℚ × A ℚ, H p.1 p.2 ∂(ν.prod ν) := h2
  rw [h3, integral_prod_symm]
  obtain ⟨C, hC, hs⟩ := Pp.exists_cpt (F := ℚ)
  rw [hν, Measure.prod_restrict]
  exact (hH.continuousOn.integrableOn_compact (hC.prod hC)).mono_set (Set.prod_mono hs hs)

/- English proof (translation)
Establish `h` using `fub (fun b v => φ (gl (nU (D.mkE b v)) * x) * ψ (rt α * v)) ((hc.comp ((cont_m D).mul continuous_const)).mul ((cont_psi_mul α).comp continuous_snd))`. Use `Eq.trans ?_ h.symm` and prove the remaining obligations. Use `congr 1`. Use function extensionality and compare the values at `v`. Rewrite using `[Sl, integral_mul_const, mul_comm]`.
-/
private theorem coeff_eq {φ : GL (Fin 2) (A E) → ℂ} (hc : Continuous φ) (x : GL (Fin 2) (A E)) (α : ℚ) :
    ∫ v in fundamentalSet ℚ, ψ (rt α * v) * Sl D φ x v ∂(adeleMeasure ℚ) =
      ∫ u in FS2 ℚ, φ (nE D u * x) * ψ (rt α * u 1) ∂(adeleMeasurePi ℚ) := by
  have h := fub (fun b v => φ (gl (nU (D.mkE b v)) * x) * ψ (rt α * v))
    ((hc.comp ((cont_m D).mul continuous_const)).mul
      ((cont_psi_mul α).comp continuous_snd))
  refine Eq.trans ?_ h.symm
  congr 1
  funext v
  rw [Sl, integral_mul_const, mul_comm]

/- English proof (translation)
Establish `h1 : algebraMap ℚ E (α : ℚ) * algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) = 1`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Establish `h2 : algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ E (α : ℚ) = 1`. Rewrite using `[mul_comm, h1]`. Use `⟨⟨!![algebraMap ℚ E α, 0; 0, 1], !![algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ), 0; 0, 1], ?_, ?_⟩, ?_⟩` and prove the remaining obligations.

Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]`. Apply the tactic sequence `ext i j fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]`. Apply `Units.ext` to reduce the goal to its premises. Use extensionality with `i j`. Rewrite using `[ratGL_apply, em_val]`.

Express the relevant statement in the definitionally equal form `rt ((!![algebraMap ℚ E α, 0; 0, 1] : Matrix (Fin 2) (Fin 2) E) i j) = am E ((!![((IdeleGroup.diagonal ℚ α : (A ℚ)ˣ) : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)`. Rewrite using `[coe_diagonal]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [am_rt]`.
-/
private theorem aE_rat (α : ℚˣ) : ∃ γ : GL (Fin 2) E, ratGL E 2 γ = UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) := by
  have h1 : algebraMap ℚ E (α : ℚ) * algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) = 1 := by
    rw [← map_mul, Units.mul_inv, map_one]
  have h2 : algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ) * algebraMap ℚ E (α : ℚ) = 1 := by
    rw [mul_comm, h1]
  refine ⟨⟨!![algebraMap ℚ E α, 0; 0, 1], !![algebraMap ℚ E ((α⁻¹ : ℚˣ) : ℚ), 0; 0, 1], ?_, ?_⟩, ?_⟩
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h1]
  · ext i j
    fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two, h2]
  · apply Units.ext
    ext i j
    rw [ratGL_apply, em_val]
    change rt ((!![algebraMap ℚ E α, 0; 0, 1] : Matrix (Fin 2) (Fin 2) E) i j) =
      am E ((!![((IdeleGroup.diagonal ℚ α : (A ℚ)ˣ) : A ℚ), 0; 0, 1] : Matrix (Fin 2) (Fin 2) (A ℚ)) i j)
    rw [coe_diagonal]
    fin_cases i <;> fin_cases j <;> simp [am_rt]

end Slice

section Main

variable {E : Type} [Field E] [NumberField E] (D : Dat ℚ E)

open GroundTheory.Automorphic.FourierWhittaker in
/- English proof (translation)
Set `H : (Fin 2 → A ℚ) → ℂ` to `fun u => φ (nE D u * x) * ψ (rt (α : ℚ) * u 1)`. Establish `hper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ y, H (ξ + y) = H y`. Introduce `ξ hξ y`. Take `⟨η, rfl⟩` from `mem_vecLattice.1 hξ`. Establish `e1 : D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1) = rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (y 0) (y 1)`.

Rewrite using `[D.mkE_add, D.mkE_rt]`. Express the relevant statement in the definitionally equal form `φ (gl (nU (D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1))) * x) * ψ (rt (α : ℚ) * (rt (η 1) + y 1)) = φ (gl (nU (D.mkE (y 0) (y 1))) * x) * ψ (rt (α : ℚ) * y 1)`. Rewrite using `[e1, hL.per, psi_rt_mul_per]`. Set `M : GL (Fin 2) ℚ` to `Matrix.GeneralLinearGroup.scalar (Fin 2) α⁻¹`. Establish `key` using `setIntegral_comp_matVec M hper`.

Establish `hmv : ∀ (u : Fin 2 → A ℚ) i, matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u i = rt ((α⁻¹ : ℚˣ) : ℚ) * u i`. Introduce `u i`. Rewrite using `[matVec_apply, Finset.sum_eq_single i]`. Simplify using `[M, Matrix.GeneralLinearGroup.scalar]`. Introduce `j _ hj`.

Simplify using `[M, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Ne.symm hj]`. Simplify using the standard rewrite rules. Take `⟨γ, hγ⟩` from `aE_rat (E := E) α`. Establish `hrα : rt (α : ℚ) * rt ((α⁻¹ : ℚˣ) : ℚ) = (1 : A ℚ)`. Rewrite using `[← map_mul, Units.mul_inv, map_one]`.

Establish `hpt : ∀ u : Fin 2 → A ℚ, φ (nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x)) * ψ (u 1) = H (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u)`. Introduce `u`. Use `set t : (A E)ˣ := Units.map (am (F := ℚ) E).toMonoidHom (IdeleGroup.diagonal ℚ α) with ht`. Establish `htv : (t : A E) = am E (rt (α : ℚ))`. Rewrite using `[ht, Units.coe_map, coe_diagonal]`.

Both sides reduce to the same expression. Use `set w : A E := D.mkE (u 0) (u 1) with hw`. Establish `e1 : D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0) (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1) = am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w`. Rewrite using `[hmv, hmv, hw, D.am_mul_mkE]`. Establish `e2 : (t : A E) * (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w) = w`.

Rewrite using `[htv, ← mul_assoc, ← map_mul, hrα, map_one, one_mul]`. Establish `h3` using `Pp.a_n t (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w)`. Rewrite `h3` using `[e2]`. Establish `e3 : nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) = ratGL E 2 γ * (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x)`. Rewrite using `[hγ, em_aE]`.

Express the relevant statement in the definitionally equal form `gl (nU w) * (aE t * x) = aE t * (gl (nU (D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0) (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1))) * x)`. Rewrite using `[e1, ← mul_assoc, ← mul_assoc, h3]`. Establish `e4 : rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1 = u 1`. Rewrite using `[hmv, ← mul_assoc, hrα, one_mul]`. Express the relevant statement in the definitionally equal form `_ = φ (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x) * ψ (rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1)`.

Rewrite using `[e3, hL.2, e4]`. Simplify using `only [Wo, hpt]`. Conclude with `key`.
-/
private theorem coeff_ne {φ : GL (Fin 2) (A E) → ℂ} (hL : Pp.Lf φ) (x : GL (Fin 2) (A E)) (α : ℚˣ) :
    Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) =
      ∫ u in FS2 ℚ, φ (nE D u * x) * ψ (rt (α : ℚ) * u 1) ∂(adeleMeasurePi ℚ) := by
  let H : (Fin 2 → A ℚ) → ℂ := fun u => φ (nE D u * x) * ψ (rt (α : ℚ) * u 1)
  have hper : ∀ ξ ∈ vecLattice ℚ (Fin 2), ∀ y, H (ξ + y) = H y := by
    intro ξ hξ y
    obtain ⟨η, rfl⟩ := mem_vecLattice.1 hξ
    have e1 : D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1) =
        rt (algebraMap ℚ E (η 0) + algebraMap ℚ E (η 1) * D.θ) + D.mkE (y 0) (y 1) := by
      rw [D.mkE_add, D.mkE_rt]
    change φ (gl (nU (D.mkE (rt (η 0) + y 0) (rt (η 1) + y 1))) * x) * ψ (rt (α : ℚ) * (rt (η 1) + y 1)) =
      φ (gl (nU (D.mkE (y 0) (y 1))) * x) * ψ (rt (α : ℚ) * y 1)
    rw [e1, hL.per, psi_rt_mul_per]
  let M : GL (Fin 2) ℚ := Matrix.GeneralLinearGroup.scalar (Fin 2) α⁻¹
  have key := setIntegral_comp_matVec M hper
  have hmv : ∀ (u : Fin 2 → A ℚ) i, matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u i = rt ((α⁻¹ : ℚˣ) : ℚ) * u i := by
    intro u i
    rw [matVec_apply, Finset.sum_eq_single i]
    · simp [M, Matrix.GeneralLinearGroup.scalar]
    · intro j _ hj
      simp [M, Matrix.GeneralLinearGroup.scalar, Matrix.diagonal_apply, Ne.symm hj]
    · simp
  obtain ⟨γ, hγ⟩ := aE_rat (E := E) α
  have hrα : rt (α : ℚ) * rt ((α⁻¹ : ℚˣ) : ℚ) = (1 : A ℚ) := by
    rw [← map_mul, Units.mul_inv, map_one]
  have hpt : ∀ u : Fin 2 → A ℚ, φ (nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x)) * ψ (u 1) =
      H (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) := by
    intro u
    set t : (A E)ˣ := Units.map (am (F := ℚ) E).toMonoidHom (IdeleGroup.diagonal ℚ α) with ht
    have htv : (t : A E) = am E (rt (α : ℚ)) := by
      rw [ht, Units.coe_map, coe_diagonal]
      rfl
    set w : A E := D.mkE (u 0) (u 1) with hw
    have e1 : D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0) (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1) =
        am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w := by
      rw [hmv, hmv, hw, D.am_mul_mkE]
    have e2 : (t : A E) * (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w) = w := by
      rw [htv, ← mul_assoc, ← map_mul, hrα, map_one, one_mul]
    have h3 := Pp.a_n t (am E (rt ((α⁻¹ : ℚˣ) : ℚ)) * w)
    rw [e2] at h3
    have e3 : nE D u * (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) =
        ratGL E 2 γ * (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x) := by
      rw [hγ, em_aE]
      change gl (nU w) * (aE t * x) = aE t * (gl (nU (D.mkE (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 0)
        (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1))) * x)
      rw [e1, ← mul_assoc, ← mul_assoc, h3]
    have e4 : rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1 = u 1 := by
      rw [hmv, ← mul_assoc, hrα, one_mul]
    change _ = φ (nE D (matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u) * x) *
      ψ (rt (α : ℚ) * matVec (M : Matrix (Fin 2) (Fin 2) ℚ) u 1)
    rw [e3, hL.2, e4]
  simp only [Wo, hpt]
  exact key

end Main

/- English proof (translation)
Introduce `E _ _ D ω φ hA x hs`. Establish `hL : Pp.Lf φ` using `⟨hA.cont, hA.left⟩`. Use `set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * Sl D φ x v ∂(adeleMeasure ℚ) with hcdef`. Establish `hc0 : c 0 = 0`. Simplify using `only [hcdef, coeff_eq D hA.cont x 0]`.

Establish `e : ∀ u : Fin 2 → A ℚ, φ (nE D u * x) * ψ (rt (0 : ℚ) * u 1) = φ (nE D u * x)` using `fun u => by`. Rewrite using `[show (rt 0 : A ℚ) = 0 from map_zero _, zero_mul, ψ_zero, mul_one]`. Simplify using `only [e]`. Conclude with `hA.zero x`. Establish `hcα : ∀ α : ℚˣ, c α = Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x)` using `fun α => by`.

Rewrite using `[coeff_ne D hL x α]`. Conclude with `coeff_eq D hA.cont x α`. Establish `hinj : Function.Injective (Units.val : ℚˣ → ℚ)` using `Units.val_injective`. Establish `hsupp : ∀ q ∉ Set.range (Units.val : ℚˣ → ℚ), c q = 0`. Introduce `q hq`.

Distinguish the cases in `h : q = 0`. Rewrite using `[h, hc0]`. Conclude with `absurd ⟨Units.mk0 q h, rfl⟩ hq`. Establish `hfc : c ∘ (Units.val : ℚˣ → ℚ) = fun α : ℚˣ => Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x)`. Use function extensionality and compare the values at `hcα`.

Establish `hsum : Summable c` using `(hinj.summable_iff hsupp).1 (by rw [hfc]; exact hs)`. Establish `hinv` using `inv_of_summable (Sl D φ x) (Sl_cont D hA.cont hA.bdd x) (Sl_per D hL x) hsum`. Rewrite using `[Fb_eq D, ← hfc]`. Conclude with `(hinj.hasSum_iff hsupp).2 hinv`.
-/
theorem UpperTheory.hasSum_whittaker_diagTorus_rat_eq_unipotentConstantTerm :
    ∀ (E : Type) [Field E] [NumberField E] (D : Dat ℚ E) (ω : HChar ℚ) (φ : GL (Fin 2) (A E) → ℂ), admitted D ω φ → ∀ x : GL (Fin 2) (A E),
        Summable (fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x)) →
        HasSum (fun α : ℚˣ => Wo D φ (em E (aE (IdeleGroup.diagonal ℚ α)) * x)) (Un.Fb φ x) := by
  intro E _ _ D ω φ hA x hs
  have hL : Pp.Lf φ := ⟨hA.cont, hA.left⟩
  set c : ℚ → ℂ := fun α => ∫ v in fundamentalSet ℚ, ψ (rt α * v) * Sl D φ x v ∂(adeleMeasure ℚ) with hcdef
  have hc0 : c 0 = 0 := by
    simp only [hcdef, coeff_eq D hA.cont x 0]
    have e : ∀ u : Fin 2 → A ℚ, φ (nE D u * x) * ψ (rt (0 : ℚ) * u 1) = φ (nE D u * x) := fun u => by
      rw [show (rt 0 : A ℚ) = 0 from map_zero _, zero_mul, ψ_zero, mul_one]
    simp only [e]
    exact hA.zero x
  have hcα : ∀ α : ℚˣ, c α = Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) := fun α => by
    rw [coeff_ne D hL x α]
    exact coeff_eq D hA.cont x α
  have hinj : Function.Injective (Units.val : ℚˣ → ℚ) := Units.val_injective
  have hsupp : ∀ q ∉ Set.range (Units.val : ℚˣ → ℚ), c q = 0 := by
    intro q hq
    by_cases h : q = 0
    · rw [h, hc0]
    · exact absurd ⟨Units.mk0 q h, rfl⟩ hq
  have hfc : c ∘ (Units.val : ℚˣ → ℚ) = fun α : ℚˣ => Wo D φ (UpperTheory.ConvolutionTheory.RankTwoDescent.em E (aE (IdeleGroup.diagonal ℚ α)) * x) :=
    funext hcα
  have hsum : Summable c := (hinj.summable_iff hsupp).1 (by rw [hfc]; exact hs)
  have hinv := inv_of_summable (Sl D φ x) (Sl_cont D hA.cont hA.bdd x) (Sl_per D hL x) hsum
  rw [Fb_eq D, ← hfc]
  exact (hinj.hasSum_iff hsupp).2 hinv
