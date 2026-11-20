import CompanionTheory.HarishChandraModules.KFiniteAnalyticVectors.AdmissibleSmoothVectors.MapStdPoly
import CompanionTheory.HarishChandraModules.BesselParameterIntegrals.InPCommutatorOfInK

open MeasureTheory Matrix
open scoped ContDiff

noncomputable section

namespace CompanionTheory.D.gk.admitted

open PI.UpqRep

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
Establish `: m ∈ Set.range (coeMatrixAlt ε)` using `by rw [range_coeMatrix]; exact hm`. Conclude with `this`.
-/
theorem exists_elt {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : ∃ g : UJ ε, toM g = m := by
  have : m ∈ Set.range (coeMatrixAlt ε) := by rw [range_coeMatrix]; exact hm
  exact this

/- English proof (translation)
Establish `h1` using `mul_eq_one_comm.1 (coeMatrix_left_inv ε m hm)`. Use `show mᴴᴴ * Jm ε * mᴴ = Jm ε`. Rewrite using `[Matrix.conjTranspose_conjTranspose]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]`.

Use `_ = Jm ε := by rw [h1, Matrix.one_mul]`.
-/
theorem conjTranspose_mem {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ UJset ε) : mᴴ ∈ UJset ε := by
  have h1 := mul_eq_one_comm.1 (coeMatrix_left_inv ε m hm)
  show mᴴᴴ * Jm ε * mᴴ = Jm ε
  rw [Matrix.conjTranspose_conjTranspose]
  calc m * Jm ε * mᴴ = m * (Jm ε * mᴴ * Jm ε) * Jm ε := by
        simp only [Matrix.mul_assoc, Jm_mul_self, Matrix.mul_one]
    _ = Jm ε := by rw [h1, Matrix.one_mul]

/- English proof (translation)
Establish `h1 : mᴴ * m = 1` using `Matrix.mem_unitaryGroup_iff'.1 hm.1`. Use `show mᴴ * Jm ε * m = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hm.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]`.
-/
theorem Kset_sub {m : Matrix (Fin n) (Fin n) ℂ} (hm : m ∈ Kset ε) : m ∈ UJset ε := by
  have h1 : mᴴ * m = 1 := Matrix.mem_unitaryGroup_iff'.1 hm.1
  show mᴴ * Jm ε * m = Jm ε
  rw [Matrix.mul_assoc, ← hm.2, ← Matrix.mul_assoc, h1, Matrix.one_mul]

/- English proof (translation)
The claim follows from `continuous_coeMatrix ε`.
-/
theorem continuous_toM : Continuous (toM : UJ ε → Matrix (Fin n) (Fin n) ℂ) := continuous_coeMatrix ε

def homUJ {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)}
    (hσ : IsURepOn (UJset ε) σ) : UJ ε →* (H →L[ℂ] H) where
  toFun g := σ (toM g)
  map_one' := hσ.1.1
  map_mul' a b := hσ.1.2 _ a.2 _ b.2

def stdU (ε : Fin n → Bool) {U : Matrix (Fin n) (Fin n) ℂ} (hU : U ∈ Matrix.unitaryGroup (Fin n) ℂ) :
    UJ ε →* Matrix (Fin n) (Fin n) ℂ where
  toFun g := Uᴴ * toM g * U
  map_one' := by
    have h1 : Uᴴ * U = 1 := Matrix.mem_unitaryGroup_iff'.1 hU
    show Uᴴ * 1 * U = 1
    rw [Matrix.mul_one, h1]
  map_mul' a b := by
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    show Uᴴ * (toM a * toM b) * U = _
    calc Uᴴ * (toM a * toM b) * U = Uᴴ * toM a * (U * Uᴴ) * toM b * U := by
          rw [h1]; simp only [Matrix.mul_assoc, Matrix.one_mul]
      _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `H _ _ _ σ hσ hirr S _ hS v hv`. Take `⟨U, hU, hiwa⟩` from `h5`. Set `μ : Measure (KG ε)` to `(Measure.haar : Measure (KG ε)).inv`. Establish `hμ : IsFiniteMeasure μ` using `CompactSpace.isFiniteMeasure`. Establish `hsc : SecondCountableTopology (KG ε)` using `TopologicalSpace.Subtype.secondCountableTopology _`.

Establish `hiso : ∀ g u, ‖homUJ hσ g u‖ = ‖u‖` using `fun g u => hσ.2.1 _ g.2 u`. Establish `hc : ∀ u, Continuous fun g => homUJ hσ g u` using `fun u => (hσ.2.2 u).comp_continuous continuous_toM fun g => g.2`. Take `⟨e, E, he, hfin, hE, hEv⟩` from `h4 (KG ε) μ H ((homUJ hσ).comp (KG ε).subtype) (fun k u => hiso k u) (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ k.2 u hu) v hv`. Use `choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)`. Set `Tr : Set (UJ ε)` to `{s | (stdU ε hU s).BlockTriangular id}`.

Establish `hgood : IsGood st Tr (stdU ε hU)`. Use `⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_, Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩` and prove the remaining obligations. Use `show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ`. Rewrite using `[hst]`. Simplify using `[Matrix.mul_assoc]`.

Establish `hinj : Function.Injective (stdU ε hU)`. Introduce `a b hab`. Establish `h1 : U * Uᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hU`. Establish `key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g` using `fun g => by show U * (Uᴴ * toM g * U) * Uᴴ = _`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))`. Establish `hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s`. Introduce `g`. Take `⟨k, hk, s, hs, hg, ht⟩` from `hiwa (toM g) g.2`. Take `⟨k, rfl⟩` from `exists_elt (Kset_sub hk)`.

Take `⟨s, rfl⟩` from `exists_elt hs`. Conclude with `⟨k, hk, s, ht, injective_coeMatrix ε hg⟩`. Establish `hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → UJ ε, stdPoly E (fun i => homUJ hσ (g i)) = 0` using `fun g => h3 (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g (fun ι _ _ ρ hρ E' hE' => h2 (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g) H (homUJ hσ) hc E hE`. Take `⟨hfd, hrk⟩` from `h1 (UJ ε) H (homUJ hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by`. Take `⟨g, rfl⟩` from `exists_elt hg`.

Conclude with `hS' g u hu) E _ hPI`. Use `⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `T hT _ ⟨u, rfl⟩`. Use `⟨T u, ?_⟩` and prove the remaining obligations. Use `show E (T u) = T (E u)`.

Rewrite using `[hE, hE, ← T.integral_comp_comm]`. Use `integral_congr_ae (Filter.Eventually.of_forall fun k => ?_) show e k • σ (toMK k) (T u) = T (e k • σ (toMK k) u)` and prove the remaining obligations. Rewrite using `[map_smul, hT _ k.2]`. Conclude with `(he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)`.
-/
theorem admissible_of_finite_rank (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : Iwa ε) : AdmUJ ε := by
  intro H _ _ _ σ hσ hirr S _ hS v hv
  obtain ⟨U, hU, hiwa⟩ := h5
  let μ : Measure (KG ε) := (Measure.haar : Measure (KG ε)).inv
  have hμ : IsFiniteMeasure μ := CompactSpace.isFiniteMeasure
  have hsc : SecondCountableTopology (KG ε) := TopologicalSpace.Subtype.secondCountableTopology _
  have hiso : ∀ g u, ‖homUJ hσ g u‖ = ‖u‖ := fun g u => hσ.2.1 _ g.2 u
  have hc : ∀ u, Continuous fun g => homUJ hσ g u := fun u =>
    (hσ.2.2 u).comp_continuous continuous_toM fun g => g.2
  obtain ⟨e, E, he, hfin, hE, hEv⟩ := h4 (KG ε) μ H ((homUJ hσ).comp (KG ε).subtype) (fun k u => hiso k u)
    (fun u => (hc u).comp continuous_subtype_val) S (fun k u hu => hS _ k.2 u hu) v hv
  choose st hst using fun g : UJ ε => exists_elt (conjTranspose_mem (m := toM g) g.2)
  let Tr : Set (UJ ε) := {s | (stdU ε hU s).BlockTriangular id}
  have hgood : IsGood st Tr (stdU ε hU) := by
    refine ⟨(continuous_const.matrix_mul continuous_toM).matrix_mul continuous_const, fun g => ?_,
      Fin.val, Fin.val_injective, fun s hs i j hij => hs hij⟩
    show Uᴴ * toM (st g) * U = (Uᴴ * toM g * U)ᴴ
    rw [hst]
    simp [Matrix.mul_assoc]
  have hinj : Function.Injective (stdU ε hU) := by
    intro a b hab
    have h1 : U * Uᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hU
    have key : ∀ g : UJ ε, U * stdU ε hU g * Uᴴ = toM g := fun g => by
      show U * (Uᴴ * toM g * U) * Uᴴ = _
      calc U * (Uᴴ * toM g * U) * Uᴴ = (U * Uᴴ) * toM g * (U * Uᴴ) := by simp only [Matrix.mul_assoc]
        _ = _ := by rw [h1, Matrix.one_mul, Matrix.mul_one]
    exact injective_coeMatrix ε ((key a).symm.trans (hab ▸ key b))
  have hKS : ∀ g : UJ ε, ∃ k ∈ KG ε, ∃ s ∈ Tr, g = k * s := by
    intro g
    obtain ⟨k, hk, s, hs, hg, ht⟩ := hiwa (toM g) g.2
    obtain ⟨k, rfl⟩ := exists_elt (Kset_sub hk)
    obtain ⟨s, rfl⟩ := exists_elt hs
    exact ⟨k, hk, s, ht, injective_coeMatrix ε hg⟩
  have hPI : ∀ g : Fin (Module.finrank ℂ S ^ 2 + 1) → UJ ε, stdPoly E (fun i => homUJ hσ (g i)) = 0 := fun g =>
    h3 (UJ ε) (KG ε) μ st Tr (Fin n) (stdU ε hU) hgood hinj e he _ g
      (fun ι _ _ ρ hρ E' hE' => h2 (UJ ε) (KG ε) μ st Tr hKS e _ _ he hfin (Nat.lt_succ_self _) ι ρ hρ E' hE' g)
      H (homUJ hσ) hc E hE
  obtain ⟨hfd, hrk⟩ := h1 (UJ ε) H (homUJ hσ) hiso (fun S' hcl hS' => hirr S' hcl fun g hg u hu => by
    obtain ⟨g, rfl⟩ := exists_elt hg
    exact hS' g u hu) E _ hPI
  refine ⟨_, hfd, hrk, ⟨v, hEv⟩, ?_⟩
  rintro T hT _ ⟨u, rfl⟩
  refine ⟨T u, ?_⟩
  show E (T u) = T (E u)
  rw [hE, hE, ← T.integral_comp_comm]
  · refine integral_congr_ae (Filter.Eventually.of_forall fun k => ?_)
    show e k • σ (toMK k) (T u) = T (e k • σ (toMK k) u)
    rw [map_smul, hT _ k.2]
  · exact (he.smul ((hc u).comp continuous_subtype_val)).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)

/- English proof (translation)
Take `⟨S, _, hvS, hS⟩` from `hv`. Take `⟨Y, _, -, hvY, hY⟩` from `hA H σ hσ hirr S hS v hvS`. Conclude with `hG n ε H σ hσ Y hY v hvY`.
-/
theorem smooth_of_adm (hA : AdmUJ ε) (hG : GardingFin) {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    [CompleteSpace H] {σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} (hσ : IsURepOn (UJset ε) σ)
    (hirr : IsIrredOn (UJset ε) σ) {v : H} (hv : IsKFin ε σ v) : SmoothOnH (Jm ε) fun g => σ g v := by
  obtain ⟨S, _, hvS, hS⟩ := hv
  obtain ⟨Y, _, -, hvY, hY⟩ := hA H σ hσ hirr S hS v hvS
  exact hG n ε H σ hσ Y hY v hvY

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace in
/- English proof (translation)
Establish `hd` using `(Matrix.isUnit_iff_isUnit_det P).1 hP`. Establish `h1 : P * P⁻¹ = 1` using `Matrix.mul_nonsing_inv P hd`. Establish `h2 : P⁻¹ * P = 1` using `Matrix.nonsing_inv_mul P hd`. Establish `hmem : ∀ g, inUH B g → inUH A (P * g * P⁻¹)`. Introduce `g hg`.

Unfold `inUH at hg ⊢`. Establish `h3 : (P⁻¹)ᴴ * Pᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]`. Combine the equalities or inequalities in the displayed calculation. Simplify using `only [Matrix.conjTranspose_mul, Matrix.mul_assoc]`. Use `_ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) := by rw [hAB, hg, ← hAB]; simp only [Matrix.mul_assoc]`.

Use `_ = A := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]`. Set `L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ` to `{ toFun := fun g => P * g * P⁻¹ map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul] map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }`. Establish `hL : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹` using `(LinearMap.toContinuousLinearMap L).contDiff`. Introduce `g₀ hg₀`. Take `⟨V, F, hV, hgV, hF, hfF⟩` from `h _ (hmem g₀ hg₀)`.

Use `⟨(fun g => P * g * P⁻¹) ⁻¹' V, fun g => F (P * g * P⁻¹), hV.preimage hL.continuous, hgV, hF.comp hL.contDiffOn fun g hg => hg, fun g hg hgB => ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (hfF _ hg (hmem g hgB))` and prove the remaining obligations. Use `show f g = f (P⁻¹ * (P * g * P⁻¹) * P)`. Use `congr 1`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem smoothOnH_conj {E : Type} [NormedAddCommGroup E] [NormedSpace ℂ E] {A B P : Matrix (Fin n) (Fin n) ℂ}
    (hP : IsUnit P) (hAB : Pᴴ * A * P = B) {f : Matrix (Fin n) (Fin n) ℂ → E}
    (h : SmoothOnH A fun g => f (P⁻¹ * g * P)) : SmoothOnH B f := by
  have hd := (Matrix.isUnit_iff_isUnit_det P).1 hP
  have h1 : P * P⁻¹ = 1 := Matrix.mul_nonsing_inv P hd
  have h2 : P⁻¹ * P = 1 := Matrix.nonsing_inv_mul P hd
  have hmem : ∀ g, inUH B g → inUH A (P * g * P⁻¹) := by
    intro g hg
    unfold inUH at hg ⊢
    have h3 : (P⁻¹)ᴴ * Pᴴ = 1 := by rw [← Matrix.conjTranspose_mul, h1, Matrix.conjTranspose_one]
    calc (P * g * P⁻¹)ᴴ * A * (P * g * P⁻¹) = (P⁻¹)ᴴ * (gᴴ * (Pᴴ * A * P) * g) * P⁻¹ := by
          simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
      _ = ((P⁻¹)ᴴ * Pᴴ) * A * (P * P⁻¹) := by rw [hAB, hg, ← hAB]; simp only [Matrix.mul_assoc]
      _ = A := by rw [h3, h1, Matrix.one_mul, Matrix.mul_one]
  let L : Matrix (Fin n) (Fin n) ℂ →ₗ[ℝ] Matrix (Fin n) (Fin n) ℂ :=
    { toFun := fun g => P * g * P⁻¹
      map_add' := fun a b => by rw [Matrix.mul_add, Matrix.add_mul]
      map_smul' := fun c a => by rw [Matrix.mul_smul, Matrix.smul_mul]; rfl }
  have hL : ContDiff ℝ ∞ fun g : Matrix (Fin n) (Fin n) ℂ => P * g * P⁻¹ := (LinearMap.toContinuousLinearMap L).contDiff
  intro g₀ hg₀
  obtain ⟨V, F, hV, hgV, hF, hfF⟩ := h _ (hmem g₀ hg₀)
  refine ⟨(fun g => P * g * P⁻¹) ⁻¹' V, fun g => F (P * g * P⁻¹), hV.preimage hL.continuous, hgV,
    hF.comp hL.contDiffOn fun g hg => hg, fun g hg hgB => ?_⟩
  refine Eq.trans ?_ (hfF _ hg (hmem g hgB))
  show f g = f (P⁻¹ * (P * g * P⁻¹) * P)
  congr 1
  calc g = (P⁻¹ * P) * g * (P⁻¹ * P) := by rw [h2, Matrix.one_mul, Matrix.mul_one]
    _ = _ := by simp only [Matrix.mul_assoc]

/- English proof (translation)
Introduce `k r ε lam H _ _ _ σ _ hσ v hv`. Take `⟨P, hP, hDS⟩` from `hσ`. Take `⟨S, hSf, hvS, hS⟩` from `hv`. Establish `hPP : Pᴴ * P = 1` using `Matrix.mem_unitaryGroup_iff'.1 hP.2`. Establish `hPP' : P * Pᴴ = 1` using `Matrix.mem_unitaryGroup_iff.1 hP.2`.

Establish `hinv : P⁻¹ = Pᴴ` using `Matrix.inv_eq_left_inv hPP`. Use `smoothOnH_conj hP.1.1 hP.1.2 (smooth_of_adm (admissible_of_finite_rank h1 h2 h3 h4 (h5 k r ε P hP)) h6 (σ := fun g => σ (P⁻¹ * g * P)) hDS.2.2.1 hDS.2.2.2.1 ⟨S, hSf, hvS, fun g hg x hx => hS _ ⟨?_, ?_⟩ x hx⟩)` and prove the remaining obligations. Establish `hg' : gᴴ * Jm ε * g = Jm ε` using `Kset_sub hg show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r`. Rewrite using `[hinv, ← hP.1.2]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]`. Use `_ = _ := by rw [hPP', Matrix.mul_one, Matrix.mul_one, hg']`. Rewrite using `[hinv]`. Conclude with `Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hP.2) hg.1) hP.2`.
-/
theorem kFinSmooth_of (h1 : FinOfPI) (h2 : GoodPI) (h3 : Transfer) (h4 : ExistsAvg) (h5 : IwaHpk) (h6 : GardingFin) :
    PI.KFinSmooth := by
  intro k r ε lam H _ _ _ σ _ hσ v hv
  obtain ⟨P, hP, hDS⟩ := hσ
  obtain ⟨S, hSf, hvS, hS⟩ := hv
  have hPP : Pᴴ * P = 1 := Matrix.mem_unitaryGroup_iff'.1 hP.2
  have hPP' : P * Pᴴ = 1 := Matrix.mem_unitaryGroup_iff.1 hP.2
  have hinv : P⁻¹ = Pᴴ := Matrix.inv_eq_left_inv hPP
  refine smoothOnH_conj hP.1.1 hP.1.2 (smooth_of_adm (admissible_of_finite_rank h1 h2 h3 h4 (h5 k r ε P hP)) h6
    (σ := fun g => σ (P⁻¹ * g * P)) hDS.2.2.1 hDS.2.2.2.1 ⟨S, hSf, hvS, fun g hg x hx => hS _ ⟨?_, ?_⟩ x hx⟩)
  · have hg' : gᴴ * Jm ε * g = Jm ε := Kset_sub hg
    show (P⁻¹ * g * P)ᴴ * Hpk k r * (P⁻¹ * g * P) = Hpk k r
    rw [hinv, ← hP.1.2]
    calc (Pᴴ * g * P)ᴴ * (Pᴴ * Jm ε * P) * (Pᴴ * g * P) = Pᴴ * (gᴴ * (P * Pᴴ) * Jm ε * (P * Pᴴ) * g) * P := by
          simp only [Matrix.conjTranspose_mul, Matrix.conjTranspose_conjTranspose, Matrix.mul_assoc]
      _ = _ := by rw [hPP', Matrix.mul_one, Matrix.mul_one, hg']
  · rw [hinv]
    exact Submonoid.mul_mem _ (Submonoid.mul_mem _ (Unitary.star_mem hP.2) hg.1) hP.2

end CompanionTheory.D.gk.admitted
