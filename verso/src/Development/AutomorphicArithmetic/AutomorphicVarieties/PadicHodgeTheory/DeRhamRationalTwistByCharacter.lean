import Development.AutomorphicArithmetic.AutomorphicVarieties.HeckeAlgebras.Distinct
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.WdDefs
import Development.AutomorphicArithmetic.AutomorphicVarieties.PadicHodgeTheory.LocalPublishedTheorems
import Development.AbelianVarietyTheory.PublishedTheorems.AutomorphicForms₂.DeRhamPotSemistable
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.CharAbove
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.WdParameterMonodromyZeroIffPotentiallyCrystallin
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.FiniteDimensionalFilDR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.RepERankOne
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.FontaineParameterTwistPotentiallySemistable
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.DeRhamCharacterTwistIffLocalEmbedding
import Development.AbelianVarietyTheory.Proofs.SatakeParameters.RootsCharpolySmulMatrix
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations Formalism.MainNotions.N GlobalTheory.WeilDeligne GlobalTheory.Pst Polynomial Module Matrix UpperTheory.V.W UpperTheory.V.Hi
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

/- English proof (translation)
Establish `hd : y.lpDim = 1` using `by rw [← WD.charPol_natDegree y s, hy, natDegree_X_sub_C]`. Establish `hc : y.eig s = {c}`. Express the relevant statement in the definitionally equal form `(y.charPol s).roots = _`. Rewrite using `[hy, roots_X_sub_C]`. Establish `h1` using `GlobalTheory.RowTie.EigTwist.eig_lpChar x y s hd c hc`.

Express the relevant statement in the definitionally equal form `((x.lpChar y).charPol s).roots = (x.charPol s).roots.map _ at h1`. Establish `h2 : (x.charPol s).roots = Finset.univ.val.map α`. Rewrite using `[hx, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map α), Multiset.map_map]`. Both sides reduce to the same expression. Rewrite using `[(IsAlgClosed.splits _).eq_prod_roots_of_monic (WD.charPol_monic (x.lpChar y) s), h1, h2, Multiset.map_map, Multiset.map_map]`.

Both sides reduce to the same expression.
-/
private theorem charPol_lpChar {E Ω : Type} [Field E] [NumberField E] [Field Ω] [Algebra E Ω] [IsAlgClosure E Ω]
    {B : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 E)} {h : IsPlaceOver B w} {n : ℕ} (x y : WD h) (s : Weil h)
    (α : Fin n → ℂ) (c : ℂ) (hx : x.charPol s = ∏ j, (X - C (α j))) (hy : y.charPol s = X - C c) :
    (x.lpChar y).charPol s = ∏ j, (X - C (α j * c)) := by
  have hd : y.lpDim = 1 := by rw [← WD.charPol_natDegree y s, hy, natDegree_X_sub_C]
  have hc : y.eig s = {c} := by
    change (y.charPol s).roots = _
    rw [hy, roots_X_sub_C]
  have h1 := GlobalTheory.RowTie.EigTwist.eig_lpChar x y s hd c hc
  change ((x.lpChar y).charPol s).roots = (x.charPol s).roots.map _ at h1
  have h2 : (x.charPol s).roots = Finset.univ.val.map α := by
    rw [hx, ← roots_multiset_prod_X_sub_C (Finset.univ.val.map α), Multiset.map_map]
    rfl
  rw [(IsAlgClosed.splits _).eq_prod_roots_of_monic (WD.charPol_monic (x.lpChar y) s), h1, h2, Multiset.map_map,
    Multiset.map_map]
  rfl

/- English proof (translation)
Introduce `hP F Ω _ _ _ _ _ l _ ι A w h n r r' μ hr hr' hμ he HT c α β h1 h2 O _ _ _ Bw hj`. Take `⟨d1, j1, p1⟩` from `h1 O Bw hj`. Take `⟨d2, j2, p2⟩` from `h2 O Bw hj`. Establish `tw` using `GlobalTheory.TwistAbove.twist_above l _ _ (UpperTheory.V.Loc.tiedP l) F Ω _ O Bw n r r' μ he`. Establish `d3` using `tw.1 d1 d2`.

Use `⟨d3, fun τ L' τ' hτ => tw.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ), fun s => ?_⟩` and prove the remaining obligations. Take `⟨T⟩` from `UpperTheory.V.Loc.tiedP l`. Establish `hdet : Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ`. Use extensionality with `g`. Simplify using `[GlobalTheory.TripleGal.rk1, Matrix.det_unique]`.

Establish `hr'e : r' = Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ))`. Rewrite using `[hdet, GlobalTheory.TwistBridgeDR.twGL_eq]`. Conclude with `MonoidHom.ext fun g => Units.ext (he g)`. Establish `c1` using `Units.continuous_val.comp hr`. Establish `c3` using `Units.continuous_val.comp hr'`.

Establish `c2 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l))`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Establish `: (fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) i j) = fun g => (μ g : Qbar l)`. Use function extensionality and compare the values at `g`. Use `fin_cases i`.

Use `fin_cases j`. Simplify using `[GlobalTheory.TripleGal.rk1]`. Rewrite using `[this]`. Conclude with `Units.continuous_val.comp hμ`. Establish `q1` using `hP.isPstAt T Bw r c1 d1`.

Establish `q2` using `hP.isPstAt T Bw _ c2 d2`. Establish `q3` using `hP.isPstAt T Bw r' c3 d3`. Rewrite `q3` using `[hr'e]`. Rewrite using `[hr'e, GlobalTheory.TwistParamAbove.wdAt_twist l _ _ ⟨T⟩ ι F Ω A w h O Bw hj n r _ c1 c2 q1 q2 q3]`. Conclude with `charPol_lpChar _ _ s _ _ (p1 s) (p2 s)`.
-/
theorem UpperTheory.deRham_rational_twist_by_character :
    GlobalTheory.Published.DeRhamPotSemistable → ∀ {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω] {l : ℕ} [Fact l.Prime] (ι : Qbar l ≃+* ℂ) {A : ValuationSubring Ω} {w : HeightOneSpectrum (𝓞 F)} (h : IsPlaceOver A w) {n : ℕ} (r r' : ↥(Dec (F := F) A) →* GL (Fin n) (Qbar l)) (μ : ↥(Dec (F := F) A) →* (Qbar l)ˣ), Continuous r → Continuous r' → Continuous μ → (∀ g, (r' g : Matrix (Fin n) (Fin n) (Qbar l)) = (μ g : Qbar l) • (r g : Matrix (Fin n) (Fin n) (Qbar l))) → ∀ (HT : (F →+* Qbar l) → Multiset ℤ) (c : (F →+* Qbar l) → ℤ) (α : Fin n → ↥(Weil h) → ℂ) (β : ↥(Weil h) → ℂ), DRat ι h r HT (fun s => ∏ j, (X - C (α j s))) → DRat ι h (GlobalTheory.TripleGal.rk1 μ) (fun τ => {c τ}) (fun s => X - C (β s)) → DRat ι h r' (fun τ => (HT τ).map (· + c τ)) (fun s => ∏ j, (X - C (α j s * β s))) := by
  intro hP F Ω _ _ _ _ _ l _ ι A w h n r r' μ hr hr' hμ he HT c α β h1 h2 O _ _ _ Bw hj
  obtain ⟨d1, j1, p1⟩ := h1 O Bw hj
  obtain ⟨d2, j2, p2⟩ := h2 O Bw hj
  have tw := GlobalTheory.TwistAbove.twist_above l _ _ (UpperTheory.V.Loc.tiedP l) F Ω _ O Bw n r r' μ he
  have d3 := tw.1 d1 d2
  refine ⟨d3, fun τ L' τ' hτ => tw.2.2.2 τ _ _ (j1 τ L' τ' hτ) (j2 τ L' τ' hτ), fun s => ?_⟩
  obtain ⟨T⟩ := UpperTheory.V.Loc.tiedP l
  have hdet : Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ) = μ := by
    ext g
    simp [GlobalTheory.TripleGal.rk1, Matrix.det_unique]
  have hr'e : r' = Formalism.MainNotions.SumRepresentations.At.twGL r (Matrix.GeneralLinearGroup.det.comp (GlobalTheory.TripleGal.rk1 μ)) := by
    rw [hdet, GlobalTheory.TwistBridgeDR.twGL_eq]
    exact MonoidHom.ext fun g => Units.ext (he g)
  have c1 := Units.continuous_val.comp hr
  have c3 := Units.continuous_val.comp hr'
  have c2 : Continuous fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) := by
    refine continuous_matrix fun i j => ?_
    have : (fun g => ((GlobalTheory.TripleGal.rk1 μ g : GL (Fin 1) (Qbar l)) : Matrix (Fin 1) (Fin 1) (Qbar l)) i j) =
        fun g => (μ g : Qbar l) := by
      funext g
      fin_cases i; fin_cases j
      simp [GlobalTheory.TripleGal.rk1]
    rw [this]
    exact Units.continuous_val.comp hμ
  have q1 := hP.isPstAt T Bw r c1 d1
  have q2 := hP.isPstAt T Bw _ c2 d2
  have q3 := hP.isPstAt T Bw r' c3 d3
  rw [hr'e] at q3
  rw [hr'e, GlobalTheory.TwistParamAbove.wdAt_twist l _ _ ⟨T⟩ ι F Ω A w h O Bw hj n r _ c1 c2 q1 q2 q3]
  exact charPol_lpChar _ _ s _ _ (p1 s) (p2 s)
