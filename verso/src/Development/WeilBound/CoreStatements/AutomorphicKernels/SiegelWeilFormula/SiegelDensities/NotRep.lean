import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.Pieces
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.SiegelDensities.TprodMemNnRealSet

noncomputable section

namespace PositivityTheory.SiegelWeilFormula.Densx

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain MeasureTheory Topology Filter GlobalTheory.CompanionTheory.SW
open scoped TensorProduct ENNReal NNReal

def halfLam (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] : ℝ≥0 := by
  classical
  exact if h : ∃ Λ : ℂ, IsLamLim F E Λ then Real.toNNReal (h.choose.re / 2) else 0

/- English proof (translation)
Establish `h : ∃ Λ : ℂ, IsLamLim F E Λ` using `⟨Λ, hΛ⟩`. Establish `he : h.choose = Λ` using `lamLim_unique h.choose_spec hΛ`. Take `⟨h1, h2⟩` from `lamLim_real hΛ`. Rewrite using `[halfLam, dif_pos h, he, Real.coe_toNNReal _ (by linarith)]`. Use `conv_rhs => rw [h1]`.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem halfLam_spec {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (Λ : ℂ)
    (hΛ : IsLamLim F E Λ) : ((halfLam F E : ℝ) : ℂ) = Λ / 2 := by
  classical
  have h : ∃ Λ : ℂ, IsLamLim F E Λ := ⟨Λ, hΛ⟩
  have he : h.choose = Λ := lamLim_unique h.choose_spec hΛ
  obtain ⟨h1, h2⟩ := lamLim_real hΛ
  rw [halfLam, dif_pos h, he, Real.coe_toNNReal _ (by linarith)]
  conv_rhs => rw [h1]
  push_cast
  ring

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ hM1 hA t ht T hT hdet hT' hne`. Introduce `d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm`. Use `⟨halfLam F E, ?_, fun Λ hΛ => halfLam_spec Λ hΛ⟩` and prove the remaining obligations. Use `haveI : BorelSpace (Ainf F) := ⟨rfl⟩`. Use `haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩`.

Establish `hLinf : IsLocR (Ainf F)` using `GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1`. Establish `hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v)` using `GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F`. Establish `haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R] [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure → (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧ ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure`. Introduce `R _ _ _ _ _ hLoc lam' hl`. Take `⟨_, _, _, _, -⟩` from `hLoc`.

Conclude with `(GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2`. Set `T1 : Matrix (Fin 1) (Fin 1) E` to `fun _ _ => algebraMap F E t`. Establish `hT1 : ∀ a b, σ (T1 b a) = T1 a b` using `fun _ _ => σ.commutes t`. Establish `htE : algebraMap F E t ≠ 0` using `(map_ne_zero _).2 ht`. Establish `hdet1 : T1.det ≠ 0`.

Rewrite using `[Matrix.det_fin_one]`. Conclude with `htE`. Establish `hsw` using `PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) J hJ (by omega) (Or.inr hA) T1 hT1 hdet1`. Take `⟨minf1, hminf1⟩` from `GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Ainf F) hLinf 1 _ _ ((haarOf _ hLinf laminf hinf.1).1 1 (M + 1)) ((haarOf _ hLinf laminf hinf.1).2 1)`. Establish `hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E), IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 (M + 1)) (coordHerm (Fv F v) σ b (lam v) 1) m'` using `fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Fv F v) (hLv v) 1 _ _ ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 (M + 1)) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)`.

Use `choose m1 hm1 using hex`. Establish `hEul` using `hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1`. Establish `hS1 : {X : Fin 1 → Fin (M + 1) → E | gramE σ J X = T1} = ∅`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`.

Introduce `hX`. Conclude with `hne (X 0) (congrFun (congrFun hX 0) 0)`. Establish `hS : {X : Fin (M + 1) → Fin (M + 1) → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅`. Use extensionality with `X`. Simplify using `only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]`.

Introduce `hX`. Apply `hne (X 0)` to reduce the goal to its premises. Simplify `congrFun (congrFun hX 0) 0` using `[gramE, blockOne]`. Establish `hz` using `((GlobalTheory.T.euler_product_measure_zero F E σ hCM d b 1 (M + 1) _ 1 _ _).1 hEul (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))`. Establish `hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨ ∃ v, cfac E v • m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0`.

Break down `hz with h | h | ⟨v, h⟩` into its components or cases. Conclude with `absurd h one_ne_zero`. Conclude with `Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1 minf1 minf hminf1 hminf h)`. Use `Or.inr ⟨v, ?_⟩` and prove the remaining obligations. Rewrite using `[SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1 (m1 v) (m v) (hm1 v) (hm v) h, smul_zero]`.

Establish `hdetB : (blockOne (algebraMap F E t) T).det ≠ 0`. Rewrite using `[((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M T t).1)]`. Conclude with `mul_ne_zero htE hdet`. Take `⟨hfin, hsum⟩` from `hM F E σ hCM (M + 1) (by omega) J hJ (blockOne (algebraMap F E t) T) hT' hdetB d b lam (fun v => hv v) m hm`. Rewrite using `[SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]`.

Conclude with `(GlobalTheory.T.euler_product_measure_zero F E σ hCM d b (M + 1) (M + 1) 0 (halfLam F E) _ _).2.2 hfin hsum hvan`.
-/
theorem notRepC_of (hE1 : PositivityTheory.PfSWUS.HMass.OneVecBinary) (hM : MassCAll) : NotRepC := by
  intro F E _ _ _ _ _ σ hCM M J hJ hM1 hA t ht T hT hdet hT' hne
  intro d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf m hminf hm
  refine ⟨halfLam F E, ?_, fun Λ hΛ => halfLam_spec Λ hΛ⟩
  haveI : BorelSpace (Ainf F) := ⟨rfl⟩
  haveI : ∀ v : HeightOneSpectrum (𝓞 F), BorelSpace (Fv F v) := fun _ => ⟨rfl⟩
  have hLinf : IsLocR (Ainf F) := GlobalTheory.CompanionTheory.SW.isLocR_Ainf F hCM.1
  have hLv : ∀ v : HeightOneSpectrum (𝓞 F), IsLocR (Fv F v) := GlobalTheory.CompanionTheory.SW.LocFv.isLocR_Fv F
  have haarOf : ∀ (R : Type) [CommRing R] [Algebra F R] [TopologicalSpace R] [MeasurableSpace R]
      [BorelSpace R], IsLocR R → ∀ lam' : Measure R, lam'.IsAddHaarMeasure →
      (∀ n' M' : ℕ, (coordW R b lam' n' M').IsAddHaarMeasure) ∧
        ∀ n' : ℕ, (coordHerm R σ b lam' n').IsAddHaarMeasure := by
    intro R _ _ _ _ _ hLoc lam' hl
    obtain ⟨_, _, _, _, -⟩ := hLoc
    exact (GlobalTheory.CompanionTheory.SW.coord_measures_haar F E σ hCM R d b lam' hl).2
  let T1 : Matrix (Fin 1) (Fin 1) E := fun _ _ => algebraMap F E t
  have hT1 : ∀ a b, σ (T1 b a) = T1 a b := fun _ _ => σ.commutes t
  have htE : algebraMap F E t ≠ 0 := (map_ne_zero _).2 ht
  have hdet1 : T1.det ≠ 0 := by
    rw [Matrix.det_fin_one]; exact htE
  have hsw := PositivityTheory.PfSWUS.HMass.one_vec_sw hE1 F E σ hCM (M + 1) J hJ (by omega) (Or.inr hA) T1 hT1 hdet1
  obtain ⟨minf1, hminf1⟩ := GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Ainf F) hLinf 1 _ _
    ((haarOf _ hLinf laminf hinf.1).1 1 (M + 1)) ((haarOf _ hLinf laminf hinf.1).2 1)
  have hex : ∀ v : HeightOneSpectrum (𝓞 F), ∃ m' : HermR (Fv F v) σ 1 → Measure (Fin 1 → Fin (M + 1) → Fv F v ⊗[F] E),
      IsGramFib (Fv F v) σ J 1 (coordW (Fv F v) b (lam v) 1 (M + 1)) (coordHerm (Fv F v) σ b (lam v) 1) m' :=
    fun v => GlobalTheory.T.exists_gram_fiber_measures F E σ hCM (M + 1) J hJ (Fv F v) (hLv v) 1 _ _
      ((haarOf _ (hLv v) (lam v) (hv v).1).1 1 (M + 1)) ((haarOf _ (hLv v) (lam v) (hv v).1).2 1)
  choose m1 hm1 using hex
  have hEul := hsw d b laminf lam hinf hv μ 𝓕 hμ h𝓕 minf1 m1 hminf1 hm1
  have hS1 : {X : Fin 1 → Fin (M + 1) → E | gramE σ J X = T1} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    exact hne (X 0) (congrFun (congrFun hX 0) 0)
  have hS : {X : Fin (M + 1) → Fin (M + 1) → E | gramE σ J X = blockOne (algebraMap F E t) T} = ∅ := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_empty_iff_false, iff_false]
    intro hX
    apply hne (X 0)
    simpa [gramE, blockOne] using congrFun (congrFun hX 0) 0
  have hz := ((GlobalTheory.T.euler_product_measure_zero F E σ hCM d b 1 (M + 1) _ 1 _ _).1 hEul
    (SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS1))
  have hvan : minf (hermOf (Ainf F) σ (blockOne (algebraMap F E t) T) hT') = 0 ∨
      ∃ v, cfac E v • m v (hermOf (Fv F v) σ (blockOne (algebraMap F E t) T) hT') = 0 := by
    rcases hz with h | h | ⟨v, h⟩
    · exact absurd h one_ne_zero
    · exact Or.inl (SwEmpty.fibre_zero_of_one σ hCM J hJ (Ainf F) hLinf b laminf hinf.1 t ht T hT' T1 rfl hT1
        minf1 minf hminf1 hminf h)
    · refine Or.inr ⟨v, ?_⟩
      rw [SwEmpty.fibre_zero_of_one σ hCM J hJ (Fv F v) (hLv v) b (lam v) (hv v).1 t ht T hT' T1 rfl hT1
        (m1 v) (m v) (hm1 v) (hm v) h, smul_zero]
  have hdetB : (blockOne (algebraMap F E t) T).det ≠ 0 := by
    rw [((GlobalTheory.CompanionTheory.SW.BlockAlg.block_alg F E σ hCM M T t).1)]
    exact mul_ne_zero htE hdet
  obtain ⟨hfin, hsum⟩ := hM F E σ hCM (M + 1) (by omega) J hJ (blockOne (algebraMap F E t) T) hT' hdetB d b lam
    (fun v => hv v) m hm
  rw [SwEmpty.thetaMeas_of_empty σ J μ 𝓕 _ hS]
  exact (GlobalTheory.T.euler_product_measure_zero F E σ hCM d b (M + 1) (M + 1) 0 (halfLam F E) _ _).2.2 hfin hsum hvan

end PositivityTheory.SiegelWeilFormula.Densx

end
