import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SingularHermitian.AesmOfContinuous

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KSing

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

/- English proof (translation)
Establish `hv : ∀ x, (((nr x : GL (Fin n ⊕ Fin n) ℂ)) : M2 n) = nU (herm x)` using `hnr`. Establish `hi : ∀ x, ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = nU (-herm x)`. Introduce `x`. Establish `h1 : (((nr x : GL (Fin n ⊕ Fin n) ℂ)) : M2 n) * nU (-herm x) = 1`. Rewrite using `[hv]`.

Simplify using `[nU, Matrix.fromBlocks_multiply]`. Combine the equalities or inequalities in the displayed calculation. Establish `hh : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ)`. Unfold `herm`. Use `fun_prop`.

Use `Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _` and prove the remaining obligations. Establish `: (Units.val ∘ fun x => (nr x : GL (Fin n ⊕ Fin n) ℂ)) = fun x => nU (herm x)` using `funext hv`. Rewrite using `[this]`. Unfold `nU`. Conclude with `Continuous.matrix_fromBlocks continuous_const hh continuous_const continuous_const`.

Establish `: (fun x => ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n)) = fun x => nU (-herm x)`. Use function extensionality and compare the values at `hi`. Rewrite using `[this]`. Unfold `nU`. Conclude with `Continuous.matrix_fromBlocks continuous_const hh.neg continuous_const continuous_const`.
-/
theorem cont_nr {n : ℕ} (nr : (Fin n → Fin n → ℝ) → GR n) (hnr : ∀ x, mR (nr x) = nU (herm x)) :
    Continuous nr := by
  have hv : ∀ x, (((nr x : GL (Fin n ⊕ Fin n) ℂ)) : M2 n) = nU (herm x) := hnr
  have hi : ∀ x, ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) = nU (-herm x) := by
    intro x
    have h1 : (((nr x : GL (Fin n ⊕ Fin n) ℂ)) : M2 n) * nU (-herm x) = 1 := by
      rw [hv]
      simp [nU, Matrix.fromBlocks_multiply]
    calc ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n)
        = ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n) *
            ((((nr x : GL (Fin n ⊕ Fin n) ℂ)) : M2 n) * nU (-herm x)) := by rw [h1, mul_one]
      _ = nU (-herm x) := by rw [← mul_assoc, Units.inv_mul, one_mul]
  have hh : Continuous (herm : (Fin n → Fin n → ℝ) → Matrix (Fin n) (Fin n) ℂ) := by
    unfold herm
    fun_prop
  refine Continuous.subtype_mk (Units.continuous_iff.2 ⟨?_, ?_⟩) _
  · have : (Units.val ∘ fun x => (nr x : GL (Fin n ⊕ Fin n) ℂ)) = fun x => nU (herm x) := funext hv
    rw [this]
    unfold nU
    exact Continuous.matrix_fromBlocks continuous_const hh continuous_const continuous_const
  · have : (fun x => ((((nr x : GL (Fin n ⊕ Fin n) ℂ))⁻¹ : GL (Fin n ⊕ Fin n) ℂ) : M2 n)) = fun x => nU (-herm x) :=
      funext hi
    rw [this]
    unfold nU
    exact Continuous.matrix_fromBlocks continuous_const hh.neg continuous_const continuous_const

/- English proof (translation)
Take `⟨K, hK, hKβ⟩` from `nCocompact d`. Take `⟨M, hM⟩` from `(hK.prod hC).exists_bound_of_continuousOn hU.continuousOn`. Use `⟨M, fun β y hy => ?_⟩` and prove the remaining obligations. Take `⟨l, hl, hβl⟩` from `hKβ β`. Establish `e` using `hper (β - l) l hl y`.

Rewrite `e` using `[sub_add_cancel]`. Rewrite using `[e]`. Conclude with `hM _ ⟨hβl, hy⟩`.
-/
theorem bdd_of_per (d : SD σ) {U : nA σ d.Y d.b × d.G → ℂ} (hU : Continuous U)
    (hper : ∀ β, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β + l, y) = U (β, y)) {C : Set d.G} (hC : IsCompact C) :
    ∃ M, ∀ β, ∀ y ∈ C, ‖U (β, y)‖ ≤ M := by
  obtain ⟨K, hK, hKβ⟩ := nCocompact d
  obtain ⟨M, hM⟩ := (hK.prod hC).exists_bound_of_continuousOn hU.continuousOn
  refine ⟨M, fun β y hy => ?_⟩
  obtain ⟨l, hl, hβl⟩ := hKβ β
  have e := hper (β - l) l hl y
  rw [sub_add_cancel] at e
  rw [e]
  exact hM _ ⟨hβl, hy⟩

set_option maxHeartbeats 800000 in

/- English proof (translation)
Use `hG` as an intermediate fact. Use `set χ : nA σ d.Y d.b → ℂ := fun β₀ => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β₀.1)))) with hχ`. Use `set U : nA σ d.Y d.b × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1 with hUdef`. Establish `hnbc` using `continuous_nb d hCD.1`. Establish `hnrc` using `cont_nr nr hnr`.

Establish `hιr : Continuous fun x => R.ι w (nr x) * z` using `((R.cont w).comp hnrc).mul continuous_const`. Establish `hUc : Continuous U` using `(hf.comp ((hnbc.comp continuous_fst).mul continuous_snd)).mul ((chi_cont d T).comp continuous_fst)`. Establish `hUper : ∀ β₀, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β₀ + l, y) = U (β₀, y)`. Introduce `β₀ l hl y`. Simplify using `only [hUdef, hχ]`.

Rewrite using `[chi_add d T β₀ l, chi_per d T hl, mul_one, add_comm, nb_add d hCD.1, mul_assoc, hinv _ (nb_rat d hCD.1 hl)]`. Take `⟨M, hM⟩` from `bdd_of_per d hUc hUper ((hψs.isCompact).image hιr)`. Use `haveI : IsFiniteMeasure (lam.restrict 𝓖) := ⟨by rw [Measure.restrict_apply_univ, hCD.2.2.2]; exact ENNReal.one_lt_top⟩`. Establish `e1 : ∀ β₀ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = U (β₀, R.ι w (nr x) * z) * ψ₀ x`. Introduce `β₀ x`.

Simplify using `only [hUdef]`. Rewrite using `[hβ x, ← mul_assoc, ← nb_add d hCD.1, add_comm, nb_add d hCD.1, show nb β₀ * nb (β x) * z = nb β₀ * (nb (β x) * z) from mul_assoc _ _ _]`. Expand and normalize the polynomial expressions, which then agree. Establish `eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z = ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖)`. Unfold `fc`.

Use `congr 1`. Use function extensionality and compare the values at `β₀`. Rewrite using `[← integral_mul_const]`. Use `congr 1`. Use function extensionality and compare the values at `x`.

Conclude with `e1 β₀ x`. Establish `hcont : Continuous (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) => U (β₀, R.ι w (nr x) * z) * ψ₀ x)` using `(hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)`. Establish `hint : Integrable (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) => U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume)`. Use `Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm)) (aesm_of_continuous d hCD hcont) (Eventually.of_forall fun p => ?_)` and prove the remaining obligations. Use `show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖`.

Rewrite using `[norm_mul]`. Distinguish the cases in `hx : p.2 ∈ tsupport ψ₀`. Conclude with `mul_le_mul_of_nonneg_right (hM p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)`. Rewrite using `[image_eq_zero_of_notMem_tsupport hx]`. Simplify using the standard rewrite rules.

Rewrite using `[eL, integral_integral_swap hint]`. Establish `e2 : ∀ x, ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)))`. Introduce `x`. Rewrite using `[integral_mul_const]`. Establish `: ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z)`.

Rewrite using `[hβ x]`. Both sides reduce to the same expression. Rewrite using `[this, fc_shift d hCD f hinv T (β x) z]`. Expand and normalize the polynomial expressions, which then agree. Repeatedly rewrite using `[e2]`.

Rewrite using `[integral_const_mul]`.
-/
theorem fc_avg (d : SD σ) (R : RD d) (w : InfinitePlace F) (hG : IsTopologicalGroup d.G)
    {nb : nA σ d.Y d.b → d.G} {lam : Measure (nA σ d.Y d.b)} {𝓖 : Set (nA σ d.Y d.b)}
    (hCD : CoefData (σ := σ) (Y := d.Y) d.b nb lam 𝓖) (f : d.G → ℂ) (hf : Continuous f)
    (hinv : ∀ γ ∈ rat2 σ d.Y, ∀ g, f (γ * g) = f g)
    (ψ₀ : (Fin d.n → Fin d.n → ℝ) → ℂ) (hψc : Continuous ψ₀) (hψs : HasCompactSupport ψ₀)
    (nr : (Fin d.n → Fin d.n → ℝ) → GR d.n) (hnr : ∀ x, mR (nr x) = nU (herm x))
    (β : (Fin d.n → Fin d.n → ℝ) → nA σ d.Y d.b) (hβc : Continuous β) (hβ : ∀ x, R.ι w (nr x) = nb (β x))
    (T : nF σ d.Y d.b) (z : d.G) :
    fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      fc d.B.ψ d.b nb lam 𝓖 f T z * ∫ x, ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1)) := by
  have := hG
  set χ : nA σ d.Y d.b → ℂ := fun β₀ => d.B.ψ (-(Algebra.trace (AF F) (AE F E) (Matrix.trace (T.1.1 * β₀.1))))
    with hχ
  set U : nA σ d.Y d.b × d.G → ℂ := fun p => f (nb p.1 * p.2) * χ p.1 with hUdef
  have hnbc := continuous_nb d hCD.1
  have hnrc := cont_nr nr hnr
  have hιr : Continuous fun x => R.ι w (nr x) * z := ((R.cont w).comp hnrc).mul continuous_const
  have hUc : Continuous U :=
    (hf.comp ((hnbc.comp continuous_fst).mul continuous_snd)).mul ((chi_cont d T).comp continuous_fst)
  have hUper : ∀ β₀, ∀ l ∈ nF σ d.Y d.b, ∀ y, U (β₀ + l, y) = U (β₀, y) := by
    intro β₀ l hl y
    simp only [hUdef, hχ]
    rw [chi_add d T β₀ l, chi_per d T hl, mul_one, add_comm, nb_add d hCD.1, mul_assoc, hinv _ (nb_rat d hCD.1 hl)]
  obtain ⟨M, hM⟩ := bdd_of_per d hUc hUper ((hψs.isCompact).image hιr)
  haveI : IsFiniteMeasure (lam.restrict 𝓖) :=
    ⟨by rw [Measure.restrict_apply_univ, hCD.2.2.2]; exact ENNReal.one_lt_top⟩
  have e1 : ∀ β₀ x, f (R.ι w (nr x) * (nb β₀ * z)) * ψ₀ x * χ β₀ = U (β₀, R.ι w (nr x) * z) * ψ₀ x := by
    intro β₀ x
    simp only [hUdef]
    rw [hβ x, ← mul_assoc, ← nb_add d hCD.1, add_comm, nb_add d hCD.1,
      show nb β₀ * nb (β x) * z = nb β₀ * (nb (β x) * z) from mul_assoc _ _ _]
    ring
  have eL : fc d.B.ψ d.b nb lam 𝓖 (fun y => ∫ x, f (R.ι w (nr x) * y) * ψ₀ x) T z =
      ∫ β₀, ∫ x, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂volume ∂(lam.restrict 𝓖) := by
    unfold fc
    congr 1
    funext β₀
    rw [← integral_mul_const]
    congr 1
    funext x
    exact e1 β₀ x
  have hcont : Continuous (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) :=
    (hUc.comp (continuous_fst.prodMk (hιr.comp continuous_snd))).mul (hψc.comp continuous_snd)
  have hint : Integrable (Function.uncurry fun (β₀ : nA σ d.Y d.b) (x : Fin d.n → Fin d.n → ℝ) =>
      U (β₀, R.ι w (nr x) * z) * ψ₀ x) ((lam.restrict 𝓖).prod volume) := by
    refine Integrable.mono' ((integrable_const M).mul_prod (hψc.norm.integrable_of_hasCompactSupport hψs.norm))
      (aesm_of_continuous d hCD hcont) (Eventually.of_forall fun p => ?_)
    show ‖U (p.1, R.ι w (nr p.2) * z) * ψ₀ p.2‖ ≤ M * ‖ψ₀ p.2‖
    rw [norm_mul]
    by_cases hx : p.2 ∈ tsupport ψ₀
    · exact mul_le_mul_of_nonneg_right (hM p.1 _ ⟨p.2, hx, rfl⟩) (norm_nonneg _)
    · rw [image_eq_zero_of_notMem_tsupport hx]
      simp
  rw [eL, integral_integral_swap hint]
  have e2 : ∀ x, ∫ β₀, U (β₀, R.ι w (nr x) * z) * ψ₀ x ∂(lam.restrict 𝓖) =
      fc d.B.ψ d.b nb lam 𝓖 f T z * (ψ₀ x * d.B.ψ (d.tt (T.1.1 * (β x).1))) := by
    intro x
    rw [integral_mul_const]
    have : ∫ β₀, U (β₀, R.ι w (nr x) * z) ∂(lam.restrict 𝓖) = fc d.B.ψ d.b nb lam 𝓖 f T (nb (β x) * z) := by
      rw [hβ x]
      rfl
    rw [this, fc_shift d hCD f hinv T (β x) z]
    ring
  simp_rw [e2]
  rw [integral_const_mul]

end PositivityTheory.SiegelWeilFormula.KSing

end
