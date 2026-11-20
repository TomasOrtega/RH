import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.RealDescent.RealLeviDescent.HighestVectorsRegularLine
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.WtRInjective
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.CliffordHighestWeightVectorStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ParthasarathyRaoVaradarajanStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HighestWeightAntitoneOfFiniteDimensionalStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.RangeStable
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsDualLieFamilyStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.InvariantIntertwinesDualStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FiniteWeightsInvariantHomStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ExistsInvariantExtendingStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightsDominatedStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicOfNormBoundStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TraceFactorTensorDecompStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualOperatorCommutesLieStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.DualWeightTraceFormulaStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.HarmonicWeightsCoefficientStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.TwistedTraceWeylCharacterStatement

noncomputable section

open Matrix Finset
open scoped InnerProductSpace
open PositivityTheory.RgBcC PositivityTheory.RgBcC.Real PositivityTheory.RgBcC.RealD GlobalTheory.CompanionTheory.RealCount GlobalTheory.CompanionTheory.RealCountG

namespace GlobalTheory.CompanionTheory.RealCountG

/- English proof (translation)
Take `⟨S, hfd, hvS, -, hKS, -⟩` from `hc.der.2 v`. Establish `hGl : Formalism.REAL.GlRel (kF E1 E2)` using `GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair`. Establish `hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR ν) v` using `hh`. Establish `hanti : Antitone (wtR ν)` using `GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V (kF E1 E2) S (wtR ν) v hGl hfd hKS hvS hv hK`. Establish `hanti' : Antitone ν` using `fun a b hab => by`.

Use `hanti hab` as an intermediate fact. Simplify `this` using `[wtR]`. Take `⟨ι, i1, i2, c, hcl, hconds⟩` from `GlobalTheory.T.parthasarathy_rao_varadarajan n`. Take `⟨w, hw, x, hx, hxh⟩` from `hconds V (kF E1 E2) S ν v hGl hc.pair.unitK hfd hKS hvS hv hK`. Establish `hn` using `GlobalTheory.T.clifford_highest_weight_vector lam V E1 E2 σ A hc ι c hcl _ x hx hxh`.

Conclude with `GlobalTheory.T.harmonic_of_norm_bound lam hl ν hanti' hdom w hw hn`.
-/
theorem hw_harm {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam)
    (V : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] (E1 E2 : Fin n → Fin n → Module.End ℂ V)
    (σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)) (A : V →ₗ[ℂ] V) (hc : IsCoreMod (infOf lam) E1 E2 σ A)
    (ν : Fin n → ℤ) (v : V) (hv : v ≠ 0) (hh : v ∈ hwSp E1 E2 (wtR ν)) (hdom : DomLE (wtR ν) (m0 lam)) :
    ν ∈ harmZ lam := by
  obtain ⟨S, hfd, hvS, -, hKS, -⟩ := hc.der.2 v
  have hGl : Formalism.REAL.GlRel (kF E1 E2) := GlobalTheory.CompanionTheory.RealCount.KHw.glRel_kF hc.pair
  have hK : Formalism.REAL.KHighest (fun _ => true) (kF E1 E2) (wtR ν) v := hh
  have hanti : Antitone (wtR ν) := GlobalTheory.CompanionTheory.RealCount.highestWeight_antitone_of_finiteDimensional_stable V (kF E1 E2) S (wtR ν) v hGl hfd hKS hvS hv hK
  have hanti' : Antitone ν := fun a b hab => by
    have := hanti hab
    simpa [wtR] using this
  obtain ⟨ι, i1, i2, c, hcl, hconds⟩ := GlobalTheory.T.parthasarathy_rao_varadarajan n
  obtain ⟨w, hw, x, hx, hxh⟩ := hconds V (kF E1 E2) S ν v hGl hc.pair.unitK hfd hKS hvS hv hK
  have hn := GlobalTheory.T.clifford_highest_weight_vector lam V E1 E2 σ A hc ι c hcl _ x hx hxh
  exact GlobalTheory.T.harmonic_of_norm_bound lam hl ν hanti' hdom w hw hn

/- English proof (translation)
Establish `hk : ∀ a b (y : V), A (kF E1 E2 a b y) = kF E1 E2 a b (A y)`. Introduce `a b y`. Establish `h1 : A (E1 a b y) = E2 a b (A y)` using `LinearMap.congr_fun (hAE a b) y`. Establish `h2 : A (E2 a b y) = E1 a b (A y)`. Establish `h3 : A (E1 a b (A y)) = E2 a b (A (A y))` using `LinearMap.congr_fun (hAE a b) (A y)`.

Establish `h4 : ∀ u : V, A (A u) = u` using `fun u => LinearMap.congr_fun hA2 u`. Rewrite `h3` using `[h4]`. Rewrite using `[← h3, h4]`. Simplify using `only [kF, LinearMap.add_apply, map_add, h1, h2]`. Normalize the expressions using the abelian group laws.

Introduce `x hx`. Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Rewrite using `[← hk, hx.1 a, map_smul]`. Rewrite using `[← hk, hx.2 a b hab he, map_zero]`.
-/
theorem hw_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {E1 E2 : Fin n → Fin n → Module.End ℂ V} {A : V →ₗ[ℂ] V} (hA2 : A * A = 1) (hAE : ∀ a b, A * E1 a b = E2 a b * A)
    (μ : Fin n → ℝ) : ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := by
  have hk : ∀ a b (y : V), A (kF E1 E2 a b y) = kF E1 E2 a b (A y) := by
    intro a b y
    have h1 : A (E1 a b y) = E2 a b (A y) := LinearMap.congr_fun (hAE a b) y
    have h2 : A (E2 a b y) = E1 a b (A y) := by
      have h3 : A (E1 a b (A y)) = E2 a b (A (A y)) := LinearMap.congr_fun (hAE a b) (A y)
      have h4 : ∀ u : V, A (A u) = u := fun u => LinearMap.congr_fun hA2 u
      rw [h4] at h3
      rw [← h3, h4]
    simp only [kF, LinearMap.add_apply, map_add, h1, h2]
    abel
  intro x hx
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · rw [← hk, hx.1 a, map_smul]
  · rw [← hk, hx.2 a b hab he, map_zero]

/- English proof (translation)
Introduce `t ht k ξ`. Establish `h1 : dualT E T (ξ ∘L E.ρ k⁻¹) = (dualT E T ξ) ∘L E.ρ k⁻¹`. Use extensionality with `y`. Establish `h2` using `congrArg (fun S : E.V →L[ℂ] E.V => ξ (S y)) (hT k⁻¹)`. Simplify using `only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]`.

Conclude with `(h2.symm)`. Establish `h3 : flipA E A T t (ξ ∘L E.ρ k⁻¹) = A (t (dualT E T (ξ ∘L E.ρ k⁻¹)))` using `rfl`. Establish `h4 : flipA E A T t ξ = A (t (dualT E T ξ))` using `rfl`. Rewrite using `[h3, h4, h1, ht k (dualT E T ξ)]`. Conclude with `LinearMap.congr_fun (hAσ k) _`.
-/
theorem flip_stable' {n : ℕ} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {σ : Matrix.unitaryGroup (Fin n) ℂ →* (V →ₗ[ℂ] V)} {A : V →ₗ[ℂ] V} (hAσ : ∀ k, A * σ k = σ k * A)
    (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T) :
    ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := by
  intro t ht k ξ
  have h1 : dualT E T (ξ ∘L E.ρ k⁻¹) = (dualT E T ξ) ∘L E.ρ k⁻¹ := by
    ext y
    have h2 := congrArg (fun S : E.V →L[ℂ] E.V => ξ (S y)) (hT k⁻¹)
    simp only [dualT, ContinuousLinearMap.flip_apply, ContinuousLinearMap.compL_apply, ContinuousLinearMap.comp_apply]
    exact (h2.symm)
  have h3 : flipA E A T t (ξ ∘L E.ρ k⁻¹) = A (t (dualT E T (ξ ∘L E.ρ k⁻¹))) := rfl
  have h4 : flipA E A T t ξ = A (t (dualT E T ξ)) := rfl
  rw [h3, h4, h1, ht k (dualT E T ξ)]
  exact LinearMap.congr_fun (hAσ k) _

/- English proof (translation)
Introduce `ξ hξ`. Establish `hc` using `GlobalTheory.T.dual_operator_commutes_lie E T hT G hG`. Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Use `show G a a (dualT E T ξ) = _`. Rewrite using `[← hc, hξ.1 a, map_smul]`.

Both sides reduce to the same expression. Use `show G a b (dualT E T ξ) = 0`. Rewrite using `[← hc, hξ.2 a b hab he, map_zero]`.
-/
theorem dual_stable' {n : ℕ} (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : ∀ k, T * E.ρ k = E.ρ k * T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) (μ : Fin n → ℝ) :
    ∀ ξ ∈ hwOf G μ, (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) ξ ∈ hwOf G μ := by
  intro ξ hξ
  have hc := GlobalTheory.T.dual_operator_commutes_lie E T hT G hG
  refine ⟨fun a => ?_, fun a b hab he => ?_⟩
  · show G a a (dualT E T ξ) = _
    rw [← hc, hξ.1 a, map_smul]
    rfl
  · show G a b (dualT E T ξ) = 0
    rw [← hc, hξ.2 a b hab he, map_zero]

/- English proof (translation)
Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply, RCLike.star_def]`. Rewrite using `[Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]`.

Simplify using the standard rewrite rules.
-/
theorem diagonal_mem_unitary {n : ℕ} (z : Fin n → ℂ) (hz : ∀ a, ‖z a‖ = 1) :
    (diagonal z : Matrix (Fin n) (Fin n) ℂ) ∈ Matrix.unitaryGroup (Fin n) ℂ := by
  rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
    Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
  congr 1
  funext a
  simp only [Pi.star_apply, RCLike.star_def]
  rw [Complex.mul_conj, Complex.normSq_eq_norm_sq, hz a]
  simp

/- English proof (translation)
Take `⟨F, hF, -, hch⟩` from `GlobalTheory.T.dual_weight_trace_formula E T hT.1 G hG`. Introduce `μ hμ`. Use `(GlobalTheory.T.harmonic_weights_coefficient lam hl F hF (fun ν => trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ))) (fun z hz hinj => ?_) μ hμ).2` and prove the remaining obligations. Establish `hzi : Function.Injective z` using `fun a b h => hinj (by simp only [h])`. Establish `h1` using `hch ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hzi`.

Establish `h2` using `GlobalTheory.T.twisted_trace_weyl_character lam E T hT ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hinj`. Rewrite using `[← h1, h2]`.
-/
theorem dualtr {n : ℕ} (lam : Fin n → ℤ) (hl : Antitone lam) (E : KMod n) (T : E.V →L[ℂ] E.V) (hT : IsLefK lam E T)
    (G : Fin n → Fin n → Module.End ℂ (E.V →L[ℂ] ℂ)) (hG : IsDualFam E G) :
    ∀ μ ∈ harmZ lam, trOn (hwOf G (wtR μ)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)) = 2 ^ n := by
  obtain ⟨F, hF, -, hch⟩ := GlobalTheory.T.dual_weight_trace_formula E T hT.1 G hG
  intro μ hμ
  refine (GlobalTheory.T.harmonic_weights_coefficient lam hl F hF (fun ν => trOn (hwOf G (wtR ν)) (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)))
    (fun z hz hinj => ?_) μ hμ).2
  have hzi : Function.Injective z := fun a b h => hinj (by simp only [h])
  have h1 := hch ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hzi
  have h2 := GlobalTheory.T.twisted_trace_weyl_character lam E T hT ⟨diagonal z, diagonal_mem_unitary z hz⟩ z rfl hinj
  rw [← h1, h2]

/- English proof (translation)
Introduce `n lam hlam E T hT V _ _ E1 E2 σ A hc hfin`. Take `⟨hsp, htop⟩` from `GlobalTheory.T.dual_weights_dominated lam hlam E T hT`. Take `⟨G, hG⟩` from `GlobalTheory.T.exists_dual_lie_family E`. Establish `hint` using `GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hc.der E G hG`. Establish `hmaps : ∀ t ∈ invA σ E, ∀ (μ : Fin n → ℝ), ∀ ξ ∈ hwOf G μ, t ξ ∈ hwSp E1 E2 μ`.

Introduce `t ht μ ξ hξ`. Use `⟨fun a => ?_, fun a b hab he => ?_⟩` and prove the remaining obligations. Rewrite using `[← hint t ht, hξ.1 a, map_smul]`. Rewrite using `[← hint t ht, hξ.2 a b hab he, map_zero]`. Establish `hinj` using `GlobalTheory.T.finite_weights_invariant_hom V E1 E2 σ hc.pair hc.der E G hG hsp (harmZ lam) (fun ν v hv hh hw => hw_harm lam hlam V E1 E2 σ A hc ν v hv hh (htop ν hw))`.

Establish `hext` using `GlobalTheory.T.exists_invariant_extending V E1 E2 σ hc.pair hc.der E G hG (harmZ lam)`. Establish `hA : ∀ μ, ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ` using `hw_stable' hc.Asq hc.AE`. Establish `hF : ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E` using `flip_stable' hc.Aσ E T hT.1`. Establish `hB` using `dual_stable' E T hT.1 G hG`. Establish `htr` using `dualtr lam hlam E T hT G hG`.

Set `ι` to `{μ // μ ∈ harmZ lam}`. Set `W : ι → Type` to `fun i => hwOf G (wtR i.1)`. Set `H : ι → Type` to `fun i => hwSp E1 E2 (wtR i.1)`. Set `b : ∀ i, W i →ₗ[ℂ] W i` to `fun i => (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (p := hwOf G (wtR i.1)) (q := hwOf G (wtR i.1)) (hB _)`. Set `a : ∀ i, H i →ₗ[ℂ] H i` to `fun i => A.restrict (p := hwSp E1 E2 (wtR i.1)) (q := hwSp E1 E2 (wtR i.1)) (hA _)`.

Establish `e3 : ∀ i : ι, LinearMap.trace ℂ (W i) (b i) = 2 ^ n`. Introduce `i`. Use `htr i.1 i.2` as an intermediate fact. Unfold `trOn at this`. Rewrite `this` using `[dif_pos (hB _)]`. Then use the resulting hypothesis.

Use `haveI hWnt : ∀ i, Nontrivial (W i) := by`. Introduce `i`. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Establish `h0 : b i = 0` using `LinearMap.ext fun x => Subsingleton.elim _ _`.

Use `e3 i` as an intermediate fact. Rewrite `this` using `[h0, map_zero]`. Conclude with `(pow_ne_zero n (two_ne_zero : (2 : ℂ) ≠ 0)) this.symm`. Set `R0 : invA σ E →ₗ[ℂ] (∀ i, W i →ₗ[ℂ] H i)` to `{ toFun := fun t i => LinearMap.codRestrict (hwSp E1 E2 (wtR i.1)) (t.1 ∘ₗ (hwOf G (wtR i.1)).subtype) (fun ξ => hmaps t.1 t.2 _ ξ.1 ξ.2) map_add' := fun x y => by funext i; ext ξ; rfl map_smul' := fun c x => by funext i; ext ξ; rfl }`. Establish `hR0 : ∀ (t : invA σ E) (i : ι) (ξ : W i), ((R0 t i ξ : hwSp E1 E2 (wtR i.1)) : V) = t.1 ξ.1` using `fun _ _ _ => rfl`.

Establish `hbij : Function.Bijective R0`. Prove the components needed by the constructor for the conclusion. Use `(injective_iff_map_eq_zero R0).2 fun t ht => ?_` and prove the remaining obligations. Use `Subtype.ext (hinj t.1 t.2 fun μ hμ ξ hξ => ?_)` and prove the remaining obligations. Use `hR0 t ⟨μ, hμ⟩ ⟨ξ, hξ⟩` as an intermediate fact.

Rewrite `this` using `[ht]`. Simplify using `using this.symm`. Introduce `f`. Take `⟨t, ht, hf⟩` from `hext (fun μ => if h : μ ∈ harmZ lam then f ⟨μ, h⟩ else 0)`. Use `⟨⟨t, ht⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Use extensionality with `ξ`. Rewrite using `[hR0]`. Use `hf i.1 i.2 ξ` as an intermediate fact. Rewrite `this` using `[dif_pos i.2]`.

Conclude with `this`. Set `R` to `LinearEquiv.ofBijective R0 hbij`. Set `Fl` to `(flipA E A T).restrict (p := invA σ E) (q := invA σ E) hF`. Establish `hcomp : ∀ x i, R (Fl x) i = a i ∘ₗ R x i ∘ₗ b i`. Introduce `x i`.

Use extensionality with `ξ`. Both sides reduce to the same expression. Use `haveI : FiniteDimensional ℂ (invA σ E) := hfin`. Take `⟨hfd, htrace⟩` from `GlobalTheory.T.trace_factor_tensor_decomp ι (invA σ E) W H R Fl a b hcomp`. Establish `hse : harmSet lam = (harmZ lam).image wtR` using `harmSet_eq lam`.

Use `⟨fun μ hμ => ?_, fun hne => ?_, ?_⟩` and prove the remaining obligations. Rewrite `hμ` using `[hse, Finset.mem_image]`. Take `⟨ν, hν, rfl⟩` from `hμ`. Conclude with `⟨hA _, hfd ⟨ν, hν⟩⟩`. Assume the negation of the conclusion as `hno push_neg at hno`.

Apply `hne` to reduce the goal to its premises. Use `(Submodule.eq_bot_iff _).2 fun t ht => hinj t ht fun μ hμ ξ hξ => ?_` and prove the remaining obligations. Establish `h1` using `hmaps t ht _ ξ hξ`. Establish `hμ' : wtR μ ∈ harmSet lam`. Rewrite using `[hse]`.

Conclude with `Finset.mem_image_of_mem _ hμ`. Rewrite `h1` using `[hno _ hμ']`. Simplify using `using h1`. Establish `e1 : trOn (invA σ E) (flipA E A T) = LinearMap.trace ℂ (invA σ E) Fl`. Unfold `trOn`.

Rewrite using `[dif_pos hF]`. Establish `e2 : ∀ i : ι, trOn (hwSp E1 E2 (wtR i.1)) A = LinearMap.trace ℂ (H i) (a i)`. Introduce `i`. Unfold `trOn`. Rewrite using `[dif_pos (hA _)]`.

Rewrite using `[e1, htrace, hse, Finset.sum_image (fun x _ y _ h => wtR_injective h), Finset.mul_sum, ← Finset.sum_coe_sort (harmZ lam)]`. Use `Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[e3 i, e2 i]`.
-/
theorem countG : CountG := by
  intro n lam hlam E T hT V _ _ E1 E2 σ A hc hfin
  obtain ⟨hsp, htop⟩ := GlobalTheory.T.dual_weights_dominated lam hlam E T hT
  obtain ⟨G, hG⟩ := GlobalTheory.T.exists_dual_lie_family E
  have hint := GlobalTheory.T.invariant_intertwines_dual V σ (kF E1 E2) hc.der E G hG
  have hmaps : ∀ t ∈ invA σ E, ∀ (μ : Fin n → ℝ), ∀ ξ ∈ hwOf G μ, t ξ ∈ hwSp E1 E2 μ := by
    intro t ht μ ξ hξ
    refine ⟨fun a => ?_, fun a b hab he => ?_⟩
    · rw [← hint t ht, hξ.1 a, map_smul]
    · rw [← hint t ht, hξ.2 a b hab he, map_zero]
  have hinj := GlobalTheory.T.finite_weights_invariant_hom V E1 E2 σ hc.pair hc.der E G hG hsp (harmZ lam)
    (fun ν v hv hh hw => hw_harm lam hlam V E1 E2 σ A hc ν v hv hh (htop ν hw))
  have hext := GlobalTheory.T.exists_invariant_extending V E1 E2 σ hc.pair hc.der E G hG (harmZ lam)
  have hA : ∀ μ, ∀ x ∈ hwSp E1 E2 μ, A x ∈ hwSp E1 E2 μ := hw_stable' hc.Asq hc.AE
  have hF : ∀ t ∈ invA σ E, flipA E A T t ∈ invA σ E := flip_stable' hc.Aσ E T hT.1
  have hB := dual_stable' E T hT.1 G hG
  have htr := dualtr lam hlam E T hT G hG
  let ι := {μ // μ ∈ harmZ lam}
  let W : ι → Type := fun i => hwOf G (wtR i.1)
  let H : ι → Type := fun i => hwSp E1 E2 (wtR i.1)
  let b : ∀ i, W i →ₗ[ℂ] W i := fun i =>
    (dualT E T : (E.V →L[ℂ] ℂ) →ₗ[ℂ] (E.V →L[ℂ] ℂ)).restrict (p := hwOf G (wtR i.1)) (q := hwOf G (wtR i.1)) (hB _)
  let a : ∀ i, H i →ₗ[ℂ] H i := fun i => A.restrict (p := hwSp E1 E2 (wtR i.1)) (q := hwSp E1 E2 (wtR i.1)) (hA _)
  have e3 : ∀ i : ι, LinearMap.trace ℂ (W i) (b i) = 2 ^ n := by
    intro i
    have := htr i.1 i.2
    unfold trOn at this
    rwa [dif_pos (hB _)] at this
  haveI hWnt : ∀ i, Nontrivial (W i) := by
    intro i
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have h0 : b i = 0 := LinearMap.ext fun x => Subsingleton.elim _ _
    have := e3 i
    rw [h0, map_zero] at this
    exact (pow_ne_zero n (two_ne_zero : (2 : ℂ) ≠ 0)) this.symm
  let R0 : invA σ E →ₗ[ℂ] (∀ i, W i →ₗ[ℂ] H i) :=
    { toFun := fun t i => LinearMap.codRestrict (hwSp E1 E2 (wtR i.1)) (t.1 ∘ₗ (hwOf G (wtR i.1)).subtype)
        (fun ξ => hmaps t.1 t.2 _ ξ.1 ξ.2)
      map_add' := fun x y => by funext i; ext ξ; rfl
      map_smul' := fun c x => by funext i; ext ξ; rfl }
  have hR0 : ∀ (t : invA σ E) (i : ι) (ξ : W i), ((R0 t i ξ : hwSp E1 E2 (wtR i.1)) : V) = t.1 ξ.1 := fun _ _ _ => rfl
  have hbij : Function.Bijective R0 := by
    constructor
    · refine (injective_iff_map_eq_zero R0).2 fun t ht => ?_
      refine Subtype.ext (hinj t.1 t.2 fun μ hμ ξ hξ => ?_)
      have := hR0 t ⟨μ, hμ⟩ ⟨ξ, hξ⟩
      rw [ht] at this
      simpa using this.symm
    · intro f
      obtain ⟨t, ht, hf⟩ := hext (fun μ => if h : μ ∈ harmZ lam then f ⟨μ, h⟩ else 0)
      refine ⟨⟨t, ht⟩, ?_⟩
      funext i
      ext ξ
      rw [hR0]
      have := hf i.1 i.2 ξ
      rw [dif_pos i.2] at this
      exact this
  let R := LinearEquiv.ofBijective R0 hbij
  let Fl := (flipA E A T).restrict (p := invA σ E) (q := invA σ E) hF
  have hcomp : ∀ x i, R (Fl x) i = a i ∘ₗ R x i ∘ₗ b i := by
    intro x i
    ext ξ
    rfl
  haveI : FiniteDimensional ℂ (invA σ E) := hfin
  obtain ⟨hfd, htrace⟩ := GlobalTheory.T.trace_factor_tensor_decomp ι (invA σ E) W H R Fl a b hcomp
  have hse : harmSet lam = (harmZ lam).image wtR := harmSet_eq lam
  refine ⟨fun μ hμ => ?_, fun hne => ?_, ?_⟩
  · rw [hse, Finset.mem_image] at hμ
    obtain ⟨ν, hν, rfl⟩ := hμ
    exact ⟨hA _, hfd ⟨ν, hν⟩⟩
  · by_contra hno
    push_neg at hno
    apply hne
    refine (Submodule.eq_bot_iff _).2 fun t ht => hinj t ht fun μ hμ ξ hξ => ?_
    have h1 := hmaps t ht _ ξ hξ
    have hμ' : wtR μ ∈ harmSet lam := by
      rw [hse]
      exact Finset.mem_image_of_mem _ hμ
    rw [hno _ hμ'] at h1
    simpa using h1
  · have e1 : trOn (invA σ E) (flipA E A T) = LinearMap.trace ℂ (invA σ E) Fl := by
      unfold trOn; rw [dif_pos hF]
    have e2 : ∀ i : ι, trOn (hwSp E1 E2 (wtR i.1)) A = LinearMap.trace ℂ (H i) (a i) := by
      intro i
      unfold trOn; rw [dif_pos (hA _)]
    rw [e1, htrace, hse, Finset.sum_image (fun x _ y _ h => wtR_injective h), Finset.mul_sum,
      ← Finset.sum_coe_sort (harmZ lam)]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [e3 i, e2 i]

end GlobalTheory.CompanionTheory.RealCountG
