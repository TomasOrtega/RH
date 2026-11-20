import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilDatumProperties
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.SiegelWeilKfourNA

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw
namespace PositivityTheory.SiegelWeilFormula.KSing
variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}
/- English proof (translation)
The claim follows from `_root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good`.
-/
theorem nilpotentMap_add (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∀ a, σ (σ a) = a := _root_.PositivityTheory.SiegelWeilFormula.kfour.sigma_sigma_of_good_k d.ok.good
/- English proof (translation)
The claim follows from `kfour.nb_add h β β'`.
-/
theorem nb_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) (β β' : nA σ d.Y d.b) :
    nb (β + β') = nb β * nb β' :=
  kfour.nb_add h β β'
/- English proof (translation)
The claim follows from `kfour.nb_rat h β hβ`.
-/
theorem nb_rat_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) {β : nA σ d.Y d.b} (hβ : β ∈ nF σ d.Y d.b) :
    nb β ∈ rat2 σ d.Y :=
  kfour.nb_rat h β hβ
/- English proof (translation)
The claim follows from `kfour.nb_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame h`.
-/
theorem continuous_nb_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} (h : IsNMap d.b nb) : Continuous nb :=
  kfour.nb_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame h
/- English proof (translation)
Take `⟨K, hK, hKx⟩` from `kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame`. Use `⟨K, hK, fun β => ?_⟩` and prove the remaining obligations. Take `⟨γ, hγ, hγK⟩` from `hKx β`. Conclude with `⟨-γ, neg_mem hγ, by rwa [sub_neg_eq_add, add_comm]⟩`.
-/
theorem nCocompact_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) : ∃ K : Set (nA σ d.Y d.b), IsCompact K ∧ ∀ β, ∃ l ∈ nF σ d.Y d.b, β - l ∈ K := by
  obtain ⟨K, hK, hKx⟩ := kfour.nF_cocompact (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  refine ⟨K, hK, fun β => ?_⟩
  obtain ⟨γ, hγ, hγK⟩ := hKx β
  exact ⟨-γ, neg_mem hγ, by rwa [sub_neg_eq_add, add_comm]⟩
/- English proof (translation)
The claim follows from `kfour.aesm_of_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame lam 𝓖 hu`.
-/
theorem aesm_of_continuous_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (h : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) {u : nA σ d.Y d.b × (Fin d.n → Fin d.n → ℝ) → ℂ} (hu : Continuous u) :
    AEStronglyMeasurable u ((lam.restrict 𝓖).prod volume) :=
  kfour.aesm_of_continuous (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame lam 𝓖 hu
/- English proof (translation)
Establish `htr : Continuous (Algebra.trace (AF F) (AE F E))` using `IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))`. Conclude with `d.ok.good.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)`.
-/
theorem chi_cont_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) :
    Continuous fun β : nA σ d.Y d.b => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) := by
  have htr : Continuous (Algebra.trace (AF F) (AE F E)) :=
    IsModuleTopology.continuous_of_linearMap (R := AF F) (Algebra.trace (AF F) (AE F E))
  exact d.ok.good.std.1.comp ((htr.comp (continuous_const.matrix_mul continuous_subtype_val).matrix_trace).neg)
/- English proof (translation)
Take `⟨T₀, hT₀⟩` from `(kfour.mem_nF_iff T.1).1 T.2`. Take `⟨l₀, hl₀⟩` from `(kfour.mem_nF_iff l).1 hl`. Rewrite using `[hT₀, hl₀, ← kfour.incM_mul']`. Conclude with `psi_rat d.ok.good.std.2.1 (T₀ * l₀)`.
-/
theorem chi_per_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) {l : nA σ d.Y d.b} (hl : l ∈ nF σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * l.1)))) = 1 := by
  obtain ⟨T₀, hT₀⟩ := (kfour.mem_nF_iff T.1).1 T.2
  obtain ⟨l₀, hl₀⟩ := (kfour.mem_nF_iff l).1 hl
  rw [hT₀, hl₀, ← kfour.incM_mul']
  exact psi_rat d.ok.good.std.2.1 (T₀ * l₀)
/- English proof (translation)
Rewrite using `[AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul]`.
-/
theorem chi_add_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) (T : nF σ d.Y d.b) (β β' : nA σ d.Y d.b) :
    d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * (β + β').1)))) =
      d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) *
        d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β'.1)))) := by
  rw [AddSubgroup.coe_add, Matrix.mul_add, Matrix.trace_add, map_add, neg_add, AddChar.map_add_eq_mul]
set_option maxHeartbeats 800000 in
/- English proof (translation)
Take `⟨hN, hH, hD, -⟩` from `hCD`. Take `⟨iLC, iSC, iT2, iBo⟩` from `kfour.nA_top (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame`. Use `set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1)))) with hχ`. Use `set u : nA σ d.Y d.b → ℂ := fun β => f (nb β * z) * χ β with hu`. Establish `hca : ∀ a b, χ (a + b) = χ a * χ b` using `fun a b => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T a b`.

Establish `hcp : ∀ l ∈ nF σ d.Y d.b, χ l = 1` using `fun l hl => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl`. Establish `hper : ∀ (γ : nF σ d.Y d.b) (x : nA σ d.Y d.b), u (γ +ᵥ x) = u x`. Introduce `γ x`. Use `show f (nb (γ.1 + x) * z) * χ (γ.1 + x) = f (nb x * z) * χ x`. Rewrite using `[hca, hcp _ γ.2, one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN γ.2)]`.

Establish `hc : d.B.ψ (d.tt (T.1.1 * β₁.1)) * χ β₁ = 1`. Simplify using `only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]`. Rewrite using `[← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]`. Establish `e1 : ∀ β, f (nb β * (nb β₁ * z)) * χ β = d.B.ψ (d.tt (T.1.1 * β₁.1)) * u (β₁ + β)`. Introduce `β`.

Simplify using `only [hu]`. Rewrite using `[← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, add_comm β₁ β, hca β β₁]`. Take the linear combination `(-(f (nb (β + β₁) * z) * χ β)) * hc`. Establish `eL : fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * ∫ β in 𝓖, u (β₁ + β) ∂lam`. Unfold `fc`.

Rewrite using `[← integral_const_mul]`. Use `congr 1`. Use function extensionality and compare the values at `β`. Conclude with `e1 β`. Rewrite using `[eL]`.

Use `congr 1`. Establish `hmp` using `measurePreserving_add_left lam β₁`. Establish `hme : MeasurableEmbedding fun β : nA σ d.Y d.b => β₁ + β` using `measurableEmbedding_addLeft β₁`. Establish `hs : (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖) = 𝓖`. Use extensionality with `β`.

Simplify using the standard rewrite rules. Establish `h2 : IsAddFundamentalDomain (nF σ d.Y d.b) ((fun β => -β₁ + β) ⁻¹' 𝓖) lam`. Use `hD.preimage_of_equiv (measurePreserving_add_left lam (-β₁)).quasiMeasurePreserving (e := id) Function.bijective_id fun γ x => ?_` and prove the remaining obligations. Use `show -β₁ + (γ.1 + x) = γ.1 + (-β₁ + x)`. Normalize the expressions using the abelian group laws.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem fc_shift_k (d : _root_.PositivityTheory.SiegelWeilFormula.SD_k σ) {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (T : nF σ d.Y d.b) (β₁ : nA σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * fc d.B.ψ d.b nb lam 𝓖 f T z := by
  obtain ⟨hN, hH, hD, -⟩ := hCD
  obtain ⟨iLC, iSC, iT2, iBo⟩ := kfour.nA_top (_root_.PositivityTheory.SiegelWeilFormula.KSing.nilpotentMap_add d) d.ok.frame
  set χ : nA σ d.Y d.b → ℂ := fun β => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β.1))))
    with hχ
  set u : nA σ d.Y d.b → ℂ := fun β => f (nb β * z) * χ β with hu
  have hca : ∀ a b, χ (a + b) = χ a * χ b := fun a b => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_add_k d T a b
  have hcp : ∀ l ∈ nF σ d.Y d.b, χ l = 1 := fun l hl => _root_.PositivityTheory.SiegelWeilFormula.KSing.chi_per_k d T hl
  have hper : ∀ (γ : nF σ d.Y d.b) (x : nA σ d.Y d.b), u (γ +ᵥ x) = u x := by
    intro γ x
    show f (nb (γ.1 + x) * z) * χ (γ.1 + x) = f (nb x * z) * χ x
    rw [hca, hcp _ γ.2, one_mul, _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, mul_assoc, hinv _ (_root_.PositivityTheory.SiegelWeilFormula.KSing.nb_rat_k d hN γ.2)]
  have hc : d.B.ψ (d.tt (T.1.1 * β₁.1)) * χ β₁ = 1 := by
    simp only [hχ, _root_.PositivityTheory.SiegelWeilFormula.SD_k.tt]
    rw [← AddChar.map_add_eq_mul, add_neg_cancel, AddChar.map_zero_eq_one]
  have e1 : ∀ β, f (nb β * (nb β₁ * z)) * χ β = d.B.ψ (d.tt (T.1.1 * β₁.1)) * u (β₁ + β) := by
    intro β
    simp only [hu]
    rw [← mul_assoc, ← _root_.PositivityTheory.SiegelWeilFormula.KSing.nb_add_k d hN, add_comm β₁ β, hca β β₁]
    linear_combination (-(f (nb (β + β₁) * z) * χ β)) * hc
  have eL : fc d.B.ψ d.b nb lam 𝓖 f T (nb β₁ * z) = d.B.ψ (d.tt (T.1.1 * β₁.1)) * ∫ β in 𝓖, u (β₁ + β) ∂lam := by
    unfold fc
    rw [← integral_const_mul]
    congr 1
    funext β
    exact e1 β
  rw [eL]
  congr 1
  have hmp := measurePreserving_add_left lam β₁
  have hme : MeasurableEmbedding fun β : nA σ d.Y d.b => β₁ + β := measurableEmbedding_addLeft β₁
  have hs : (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖) = 𝓖 := by
    ext β
    simp
  have h2 : IsAddFundamentalDomain (nF σ d.Y d.b) ((fun β => -β₁ + β) ⁻¹' 𝓖) lam := by
    refine hD.preimage_of_equiv (measurePreserving_add_left lam (-β₁)).quasiMeasurePreserving
      (e := id) Function.bijective_id fun γ x => ?_
    show -β₁ + (γ.1 + x) = γ.1 + (-β₁ + x)
    abel
  calc ∫ β in 𝓖, u (β₁ + β) ∂lam
      = ∫ β in (fun β : nA σ d.Y d.b => β₁ + β) ⁻¹' ((fun β => -β₁ + β) ⁻¹' 𝓖), u (β₁ + β) ∂lam := by rw [hs]
    _ = ∫ β in (fun β => -β₁ + β) ⁻¹' 𝓖, u β ∂lam := hmp.setIntegral_preimage_emb hme u _
    _ = ∫ β in 𝓖, u β ∂lam := h2.setIntegral_eq hD hper
end PositivityTheory.SiegelWeilFormula.KSing
end
end
