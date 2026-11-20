import Mathlib
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeGenerator
import Development.AutomorphicArithmetic.DivisorFrames.ExistsExponentialUniformization
import Development.AutomorphicArithmetic.DivisorFrames.HodgeGramEqPiMulHermFormOfExponential
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.HodgeMetricFrameEqRiemannFormAtInteriorPoint
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead

/- English proof (translation)
Use `show q ((spMap ι) (IsLocalRing.closedPoint K')) = q _`. Rewrite using `[Subsingleton.elim ((spMap ι) (IsLocalRing.closedPoint K')) (IsLocalRing.closedPoint K)]`.
-/
private theorem below_map {K K' : Type} [Field K] [Field K'] (ι : K →+* K') {X : Scheme.{0}} (q : Sp K ⟶ X) :
    below (spMap ι ≫ q) = below q := by
  show q ((spMap ι) (IsLocalRing.closedPoint K')) = q _
  rw [Subsingleton.elim ((spMap ι) (IsLocalRing.closedPoint K')) (IsLocalRing.closedPoint K)]

/- English proof (translation)
Rewrite using `[spMap, CommRingCat.ofHom_comp, Spec.map_comp]`.
-/
private theorem sp_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (g.comp f) = spMap g ≫ spMap f := by
  rw [spMap, CommRingCat.ofHom_comp, Spec.map_comp]

/- English proof (translation)
Rewrite using `[← sp_comp]`. Use `congr 1`. Apply the tactic sequence `ext r <;> simp [dualMap, Chart.dualMapR]`.
-/
private theorem dual_comp {R S T : Type} [CommRing R] [CommRing S] [CommRing T] (f : R →+* S) (g : S →+* T) :
    spMap (Chart.dualMapR (g.comp f)) = spMap (dualMap g) ≫ spMap (Chart.dualMapR f) := by
  rw [← sp_comp]
  congr 1
  ext r <;> simp [dualMap, Chart.dualMapR]

/- English proof (translation)
Introduce `D O x y hy K _ _ F ι h hT hH θ σ hG hσ yc hyc f hf τ a b`. Take `⟨jF, yO, ψ, -, h2, h3, h4, h5, h6⟩` from `hT`. Take `⟨Λ, Hm, W, ⟨Q, e, ψ', v', u, χ, ⟨-, p1, p2⟩, -, hAH, hv⟩, hW⟩` from `hH (θ.comp ι)`. Establish `hΨ : IsGrpPullback Q.A O.s.T.Z.t.G (yc.1 ≫ genι O.s.T.Z) (ψ' ≫ F.φ ≫ ψ)`. Use `(IsGrpPullback.comp p1 (IsGrpPullback.comp F.fib h3)).congr ?_ rfl` and prove the remaining obligations.

Rewrite using `[hyc, Category.assoc, ← h2, sp_comp, sp_comp, Category.assoc, Category.assoc]`. Establish `hL : LBIso (O.s.T.Z.t.PP.L.pull (ψ' ≫ F.φ ≫ ψ)) Q.L`. Use `LBIso.trans (pull_isLB O.s.T.Z.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ') Q.isLB ?_ p2` and prove the remaining obligations. Conclude with `h4.chartPull (Geo.Tor.chartPullSame _ _ (fun _ => F.φ ≫ ψ) _ ψ' fun _ => rfl) (Geo.Tor.chartPullPull _ ψ' ψ' rfl)`. Take `⟨exx, hex, hhol, hint, hd⟩` from `UpperTheory.exists_exponential_uniformization _ _ _ O.s.T.Z.t _ Q _ hΨ hL _ u Hm χ hAH`.

Establish `hb : yc.1 (IsLocalRing.closedPoint ℂ) ∉ genBd O.s.T.Z` using `by show below yc.1 ∉ _`. Rewrite using `[hyc, below_map]`. Conclude with `hy`. Use `choose q hq hs _ using fun (t : D.host.E →+* ℂ) (c : Fin (O.S.Dw.mult t)) => UpperTheory.lie_lattice_generator D O K F t c c.2 h5`. Establish `ev : ∀ t c, f.v t c = (v' (q t c)).left ≫ ψ' ≫ F.φ ≫ ψ` using `fun t c => by`.

Establish `e1 : (v' (q t c)).left ≫ ψ' = _` using `(hv (q t c)).1`. Establish `e2` using `h6 (q t c) _ (hq t c)`. Rewrite using `[hf t c, ← Category.assoc, e1, dual_comp, Category.assoc, Category.assoc]`. Conclude with `congrArg (_ ≫ ·) e2`. Rewrite using `[UpperTheory.hodge_gram_eq_pi_mul_hermForm_of_exponential D O x σ hG yc hb _ exx Hm hex hhol hint f (fun t c => W (q t c)) (fun t c => ?_) τ a b, hs, hs, hW]`.

Rewrite using `[ev]`. Use `hd _ _ ((UpperTheory.isTangent_iff_pullback O.s.T.Z.t hΨ _).2 ?_) (hv _).2` and prove the remaining obligations. Rewrite using `[← ev]`. Conclude with `f.tan t c`.
-/
theorem UpperTheory.fibre_hermitian_embedding :
    ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pt O.s), below y.y ∉ genBd O.s.T.Z → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → ∀ (θ : Qb →+* ℂ) (σ : O.κ.c.F →+* ℂ), Formalism.L2.PjFree.GoodEmb O.κ.c σ → σ = θ.comp y.fK → ∀ (yc : GlobalTheory.CxPts (genStr O.s.T.Z) σ), yc.1 = spMap θ ≫ y.y → ∀ f : EigFrame O.s.T.Z σ (yc.1 ≫ genι O.s.T.Z), y.frame.IsMap θ f → ∀ (τ : D.host.E →+* ℂ) (a b : Fin (O.S.Dw.mult τ)), (x.hodge σ).gram yc f τ a b = h.form (θ.comp ι) (stepVec O F τ a) (stepVec O F τ b) := by
  intro D O x y hy K _ _ F ι h hT hH θ σ hG hσ yc hyc f hf τ a b
  obtain ⟨jF, yO, ψ, -, h2, h3, h4, h5, h6⟩ := hT
  obtain ⟨Λ, Hm, W, ⟨Q, e, ψ', v', u, χ, ⟨-, p1, p2⟩, -, hAH, hv⟩, hW⟩ := hH (θ.comp ι)
  have hΨ : IsGrpPullback Q.A O.s.T.Z.t.G (yc.1 ≫ genι O.s.T.Z) (ψ' ≫ F.φ ≫ ψ) := by
    refine (IsGrpPullback.comp p1 (IsGrpPullback.comp F.fib h3)).congr ?_ rfl
    rw [hyc, Category.assoc, ← h2, sp_comp, sp_comp, Category.assoc, Category.assoc]
  have hL : LBIso (O.s.T.Z.t.PP.L.pull (ψ' ≫ F.φ ≫ ψ)) Q.L := by
    refine LBIso.trans (pull_isLB O.s.T.Z.t.PP.isLB _) (pull_isLB F.P₀.isLB ψ') Q.isLB ?_ p2
    exact h4.chartPull (Geo.Tor.chartPullSame _ _ (fun _ => F.φ ≫ ψ) _ ψ' fun _ => rfl)
      (Geo.Tor.chartPullPull _ ψ' ψ' rfl)
  obtain ⟨exx, hex, hhol, hint, hd⟩ := UpperTheory.exists_exponential_uniformization _ _ _ O.s.T.Z.t _ Q _ hΨ hL _ u Hm χ hAH
  have hb : yc.1 (IsLocalRing.closedPoint ℂ) ∉ genBd O.s.T.Z := by
    show below yc.1 ∉ _
    rw [hyc, below_map]
    exact hy
  choose q hq hs _ using fun (t : D.host.E →+* ℂ) (c : Fin (O.S.Dw.mult t)) =>
    UpperTheory.lie_lattice_generator D O K F t c c.2 h5
  have ev : ∀ t c, f.v t c = (v' (q t c)).left ≫ ψ' ≫ F.φ ≫ ψ := fun t c => by
    have e1 : (v' (q t c)).left ≫ ψ' = _ := (hv (q t c)).1
    have e2 := h6 (q t c) _ (hq t c)
    rw [hf t c, ← Category.assoc, e1, dual_comp, Category.assoc, Category.assoc]
    exact congrArg (_ ≫ ·) e2
  rw [UpperTheory.hodge_gram_eq_pi_mul_hermForm_of_exponential D O x σ hG yc hb _ exx Hm hex hhol hint f (fun t c => W (q t c)) (fun t c => ?_) τ a b,
    hs, hs, hW]
  rw [ev]
  refine hd _ _ ((UpperTheory.isTangent_iff_pullback O.s.T.Z.t hΨ _).2 ?_) (hv _).2
  rw [← ev]
  exact f.tan t c
