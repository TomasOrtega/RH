import Mathlib
import Development.AbelianVarietyTheory.Definitions.AutomorphicMembership.ExistsIsHodgeFrameIff

set_option autoImplicit false

noncomputable section

open AlgebraicGeometry CategoryTheory Limits NumberField Matrix
open ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.L2.Pj GlobalTheory GlobalTheory.CxPts GlobalTheory.Toroidal GlobalTheory.LieMet GlobalTheory.GradedNorm GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.ShFam GlobalTheory.ShFam.Pad
open scoped ContDiff ComplexOrder

namespace GlobalTheory.ShFam.InterpSmooth

variable {E' : Type} [NormedAddCommGroup E'] [NormedSpace ℝ E'] {U : Set E'}

/- English proof (translation)
Use `⟨fun h => ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩, fun h => ?_⟩` and prove the remaining obligations. Use `(Complex.ofRealCLM.contDiff.comp_contDiffOn h.1).add ((Complex.ofRealCLM.contDiff.comp_contDiffOn h.2).mul (contDiffOn_const (c := Complex.I)))` as an intermediate fact. Use `this.congr fun v _ => ?_` and prove the remaining obligations. Simplify using `[Complex.re_add_im]`.
-/
theorem contDiffOn_iff_re_im {f : E' → ℂ} : ContDiffOn ℝ ∞ f U ↔
    ContDiffOn ℝ ∞ (fun v => (f v).re) U ∧ ContDiffOn ℝ ∞ (fun v => (f v).im) U := by
  refine ⟨fun h => ⟨Complex.reCLM.contDiff.comp_contDiffOn h, Complex.imCLM.contDiff.comp_contDiffOn h⟩, fun h => ?_⟩
  have := (Complex.ofRealCLM.contDiff.comp_contDiffOn h.1).add
    ((Complex.ofRealCLM.contDiff.comp_contDiffOn h.2).mul (contDiffOn_const (c := Complex.I)))
  refine this.congr fun v _ => ?_
  simp [Complex.re_add_im]

variable {n : ℕ}

def EntSm (A : E' → Matrix (Fin n) (Fin n) ℂ) (U : Set E') : Prop := ∀ a b, ContDiffOn ℝ ∞ (fun v => A v a b) U

/- English proof (translation)
Simplify using `only [Matrix.det_apply']`. Conclude with `ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)`.
-/
theorem det_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) : ContDiffOn ℝ ∞ (fun v => (A v).det) U := by
  simp only [Matrix.det_apply']
  exact ContDiffOn.sum fun σ _ => contDiffOn_const.mul (contDiffOn_prod fun i _ => h _ _)

/- English proof (translation)
Introduce `a b`. Establish `hadj : ContDiffOn ℝ ∞ (fun v => (A v).adjugate a b) U`. Simplify using `only [Matrix.adjugate_apply]`. Use `det_sm (A := fun v => (A v).updateRow b (Pi.single a 1)) fun i k => ?_` and prove the remaining obligations. Distinguish the cases in `hi : i = b`.

Simplify using `only [Matrix.updateRow_apply, hi, ↓reduceIte]`. Conclude with `contDiffOn_const`. Simplify using `only [Matrix.updateRow_apply, hi, ↓reduceIte]`. Conclude with `h _ _`. Use `(((det_sm h).inv h0).mul hadj).congr fun v _ => ?_` and prove the remaining obligations.

Simplify using `only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Pi.inv_apply]`.
-/
theorem inv_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (h : EntSm A U) (h0 : ∀ v ∈ U, (A v).det ≠ 0) :
    EntSm (fun v => (A v)⁻¹) U := by
  intro a b
  have hadj : ContDiffOn ℝ ∞ (fun v => (A v).adjugate a b) U := by
    simp only [Matrix.adjugate_apply]
    refine det_sm (A := fun v => (A v).updateRow b (Pi.single a 1)) fun i k => ?_
    by_cases hi : i = b
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact contDiffOn_const
    · simp only [Matrix.updateRow_apply, hi, ↓reduceIte]
      exact h _ _
  refine (((det_sm h).inv h0).mul hadj).congr fun v _ => ?_
  simp only [Matrix.inv_def, Ring.inverse_eq_inv', Matrix.smul_apply, smul_eq_mul, Pi.inv_apply]

/- English proof (translation)
Introduce `a b` and use `by have hs' : ContDiffOn ℝ ∞ (fun v => ((s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hs have h1 : ContDiffOn ℝ ∞ (fun v => ((1 - s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs) refine ((h1.mul (hA a b)).add (hs'.mul (hB …`.
-/
theorem mix_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) : EntSm (fun v => mix (s v) (A v) (B v)) U := fun a b => by
  have hs' : ContDiffOn ℝ ∞ (fun v => ((s v : ℝ) : ℂ)) U := Complex.ofRealCLM.contDiff.comp_contDiffOn hs
  have h1 : ContDiffOn ℝ ∞ (fun v => ((1 - s v : ℝ) : ℂ)) U :=
    Complex.ofRealCLM.contDiff.comp_contDiffOn (contDiffOn_const.sub hs)
  refine ((h1.mul (hA a b)).add (hs'.mul (hB a b))).congr fun v _ => ?_
  simp only [mix, Matrix.add_apply, Matrix.smul_apply, smul_eq_mul]

/- English proof (translation)
Introduce `a b` and use `(inv_sm hA (fun v hv => (hp v hv).det_pos.ne') b a).congr fun _ _ => rfl`.
-/
theorem dual_sm {A : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hp : ∀ v ∈ U, (A v).PosDef) :
    EntSm (fun v => dualGram (A v)) U :=
  fun a b => (inv_sm hA (fun v hv => (hp v hv).det_pos.ne') b a).congr fun _ _ => rfl

/- English proof (translation)
The claim follows from `dual_sm (mix_sm hs (dual_sm hA hpA) (dual_sm hB hpB)) fun v hv => mix_posDef (hs01 v hv) (dualGram_posDef (hpA v hv)) (dualGram_posDef (hpB v hv))`.
-/
theorem mixDual_sm {s : E' → ℝ} {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hs : ContDiffOn ℝ ∞ s U) (hA : EntSm A U)
    (hB : EntSm B U) (hpA : ∀ v ∈ U, (A v).PosDef) (hpB : ∀ v ∈ U, (B v).PosDef)
    (hs01 : ∀ v ∈ U, s v ∈ Set.Icc (0 : ℝ) 1) : EntSm (fun v => mixDual (s v) (A v) (B v)) U :=
  dual_sm (mix_sm hs (dual_sm hA hpA) (dual_sm hB hpB)) fun v hv =>
    mix_posDef (hs01 v hv) (dualGram_posDef (hpA v hv)) (dualGram_posDef (hpB v hv))

/- English proof (translation)
Distinguish the cases in `hc : c`. Simplify using `only [hc, ↓reduceIte]`. Conclude with `hA`. Simplify using `only [hc, ↓reduceIte]`. Conclude with `hB`.
-/
theorem ite_sm {c : Prop} [Decidable c] {A B : E' → Matrix (Fin n) (Fin n) ℂ} (hA : EntSm A U) (hB : EntSm B U) :
    EntSm (fun v => if c then A v else B v) U := by
  by_cases hc : c
  · simp only [hc, ↓reduceIte]; exact hA
  · simp only [hc, ↓reduceIte]; exact hB

/- English proof (translation)
The claim follows from `congrArg CommRingCat.Hom.hom (Spec.map_injective h)`.
-/
theorem spMap_inj {A B : Type} [CommRing A] [CommRing B] {f g : A →+* B} (h : spMap f = spMap g) : f = g :=
  congrArg CommRingCat.Hom.hom (Spec.map_injective h)

end GlobalTheory.ShFam.InterpSmooth

namespace GlobalTheory.ShFam

open InterpSmooth

/- English proof (translation)
Introduce `D A N j S κ s x σ R hR hH V φ F τ a b hφ`. Use `set P := ptsIn (genStr s.T.Z) σ V.1 with hP`. Use `set Bc := {y : CxPts (genStr s.T.Z) σ | ¬ LiesIn y (genBd s.T.Z)} with hBc`. Establish `hBo : IsOpen Bc` using `isOpen_not_liesIn _`. Establish `hphi : ∀ y (hy : y ∈ P), σ = (evHom hy).comp φ` using `fun y hy => by`.

Establish `e : spMap σ = spMap ((evHom hy).comp φ)`. Rewrite using `[← y.2, ← spMap_evHom hy, Category.assoc, hφ, ← Spec.map_comp]`. Both sides reduce to the same expression. Conclude with `spMap_inj e`. Establish `hfr : ∀ y (hy : y ∈ P), ∃ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), F.IsMap (evHom hy) f` using `fun y hy => F.exists_isMap (evHom hy) (hphi y hy) (by rw [← Category.assoc, spMap_evHom hy])`.

Establish `huniq : ∀ y (hy : y ∈ P) (f f' : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f → F.IsMap (evHom hy) f' → f = f'` using `fun y hy f f' hf hf' => by`. Establish `e : f.v = f'.v` using `funext fun τ => funext fun i => (hf τ i).trans (hf' τ i).symm`. Consider the cases of `f`. Consider the cases of `f'`. Consider the cases of `e`.

Both sides reduce to the same expression. Use `choose g0 hg0r hg0i hg0 using fun a' b' => x.smoothOn_eigMet σ V φ F τ a' b' hφ`. Use `choose g1 hg1r hg1i hg1 using fun a' b' => hH V φ F τ a' b' hφ`. Set `M0` to `fun y => Matrix.of fun a' b' => g0 a' b' y`. Set `M1` to `fun y => Matrix.of fun a' b' => g1 a' b' y`.

Establish `e0 : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMet σ).gram y f τ = M0 y` using `fun y hy f hf => Matrix.ext fun a' b' => hg0 a' b' y (Set.mem_univ y) hy f hf`. Establish `e1 : ∀ y (hy : y ∈ P), y ∈ Bc → ∀ f, F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ = M1 y` using `fun y hy hb f hf => Matrix.ext fun a' b' => hg1 a' b' y hb hy f hf`. Establish `p0 : ∀ y ∈ P, (M0 y).PosDef` using `fun y hy => by`. Take `⟨f, hf⟩` from `hfr y hy`. Conclude with `e0 y hy f hf ▸ (x.eigMet σ).pos y f τ`.

Establish `p1 : ∀ y ∈ P, y ∈ Bc → (M1 y).PosDef` using `fun y hy hb => by`. Take `⟨f, hf⟩` from `hfr y hy`. Conclude with `e1 y hy hb f hf ▸ (x.hodge σ).pos y f τ`. Set `g : CxPts (genStr s.T.Z) σ → ℂ` to `fun y => if hy : y ∈ P then (x.eigMetAt σ (some R)).gram y (hfr y hy).choose τ a b else 0`. Establish `hg : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMetAt σ (some R)).gram y f τ a b = g y` using `fun y hy f hf => by`.

Simplify using `only [g, dif_pos hy]`. Rewrite using `[huniq y hy f _ hf (hfr y hy).choose_spec]`. Use `set W := {y : CxPts (genStr s.T.Z) σ | (∏ i, x.nrm σ i y) ^ 2 < Real.exp (Real.exp 1 - R ^ 3)} with hW`. Establish `hcont : ∀ i, Continuous (x.nrm σ i)` using `fun i => continuous_iff_continuousAt.2 fun y => by`. Take `⟨V', t, f, hy, -, hf, e⟩` from `(x.nrm_div σ i).2 y`.

Establish `ho` using `isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V'.1`. Establish `h1 : ContinuousOn (fun z => √(‖ev (genStr s.T.Z) σ V'.1 t z‖ ^ 2 * Real.exp (-f z))) (ptsIn _ σ V'.1)` using `(((((manifold s.T.Z σ).holoOn_ev V'.1 t).continuousOn ho).norm.pow 2).mul ((hf.continuousOn ho).neg.rexp)).sqrt`. Use `(h1.continuousAt (ho.mem_nhds hy)).congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hy) fun z hz => ?_)` and prove the remaining obligations. Rewrite using `[← e z hz, Real.sqrt_sq ((x.nrm_div σ i).1 z).1]`. Establish `hWo : IsOpen W` using `isOpen_lt ((continuous_finset_prod _ fun i _ => hcont i).pow 2) continuous_const`.

Establish `hWbd : ∀ y, LiesIn y (genBd s.T.Z) → y ∈ W` using `fun y hy => by`. Take `⟨i, hi⟩` from `(x.liesIn_genBd_iff y).1 hy`. Establish `h0 : x.nrm σ i y = 0` using `le_antisymm (not_lt.1 fun h => ((x.nrm_div σ i).pos_iff y).1 h hi) ((x.nrm_div σ i).1 y).1`. Use `show (∏ i, x.nrm σ i y) ^ 2 < _`. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ i) h0]`.

Simplify using `using Real.exp_pos _`. Establish `hW0 : ∀ y ∈ W, x.wt σ R y = 0` using `fun y hy => by`. Distinguish the cases in `hL : LiesIn y (genBd s.T.Z)`. Conclude with `x.wt_eq_zero hR (Or.inl hL)`. Use `x.wt_eq_zero hR (Or.inr ?_)` and prove the remaining obligations.

Establish `hpos : 0 < (∏ i, x.nrm σ i y) ^ 2` using `pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hL i) 2`. Use `(Real.log_lt_iff_lt_exp hpos).2 hy` as an intermediate fact. Simplify using `only [OddPrimesWithRootsOfUnity.r]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hr : (manifold s.T.Z σ).SmoothOn Bc (x.r σ)`.

Use `AnRead.SmoothOn.congr (f := fun y => Real.exp 1 - ∑ i, Real.log (x.nrm σ i y ^ 2)) (fun c => contDiffOn_const.sub (ContDiffOn.sum fun i _ => ((x.nrm_div σ i).smoothOn_log.mono fun y (hy : ¬ LiesIn y (genBd s.T.Z)) hi => hy ((x.liesIn_genBd_iff y).2 ⟨i, hi⟩)) c)) fun y hy => ?_` and prove the remaining obligations. Simplify using `only [OddPrimesWithRootsOfUnity.r]`. Rewrite using `[← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero _ (x.nrm_pos hy i).ne']`. Establish `hw : (manifold s.T.Z σ).SmoothOn Bc (x.wt σ R)`. Use `AnRead.SmoothOn.congr (f := fun y => cutWt x.kap R (x.r σ y)) (fun c => ?_) fun y hy => x.wt_eq hR hy` and prove the remaining obligations.

Establish `h1` using `hr c`. Establish `hpos : ∀ v, 0 < (x.r σ ∘ ((manifold s.T.Z σ).chart c).e.symm) v` using `fun v => lt_of_lt_of_le (Real.exp_pos 1) (x.exp_le_r σ _)`. Establish `hA` using `contDiff_cutoff.1.comp_contDiffOn ((h1.log fun v _ => (hpos v).ne').div_const (Real.log R))`. Establish `hB` using `contDiffOn_const (c := (1 : ℝ)).add ((h1.div_const R).rpow_const_of_ne (p := x.kap) fun v _ => (div_pos (hpos v) (by linarith)).ne')`. Use `(hA.div hB fun v _ => ?_).congr fun v _ => rfl` and prove the remaining obligations.

Conclude with `(add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (div_nonneg (hpos v).le (by linarith)) _)).ne'`. Establish `hgB : ∀ y ∈ P, y ∈ Bc → g y = (if τ (A.H.rt : D.host.E) = A.H.rt0 then mix (x.wt σ R y) (M0 y) (M1 y) else mixDual (x.wt σ R y) (M0 y) (M1 y)) a b` using `fun y hy hb => by`. Take `⟨f, hf⟩` from `hfr y hy`. Rewrite using `[← hg y hy f hf]`. Simplify using `only [ToroidalCompactificationData.eigMetAt, EigMet.interp]`.

Rewrite using `[e0 y hy f hf, e1 y hy hb f hf]`. Establish `hgW : ∀ y ∈ P, y ∈ W → g y = g0 a b y` using `fun y hy hw' => by`. Take `⟨f, hf⟩` from `hfr y hy`. Rewrite using `[← hg y hy f hf, ← hg0 a b y (Set.mem_univ y) hy f hf]`. Conclude with `congrFun (congrFun (EigMet.interp_gram_zero (hs := x.wt_mem R) f (hW0 y hw')) a) b`.

Set `T : Bool → Set (CxPts (genStr s.T.Z) σ)` to `fun β => cond β W Bc`. Establish `key : ∀ β i, ContDiffOn ℝ ∞ (g ∘ ((manifold s.T.Z σ).chart i).e.symm) (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β))`. Introduce `β i`. Establish `sub : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β) ⊆ ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Set.univ ∩ P)` using `fun v hv => ⟨hv.1, hv.2.1⟩`. Establish `s0 : EntSm (fun v => M0 (((manifold s.T.Z σ).chart i).e.symm v)) (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β))` using `fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg0r a' b' i).mono sub, (hg0i a' b' i).mono sub⟩`.

Consider the cases of `β`. Establish `sub1 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T false) ⊆ ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Bc ∩ P)` using `fun v hv => ⟨hv.1, hv.2.2, hv.2.1.2⟩`. Establish `sub2 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T false) ⊆ ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' Bc` using `fun v hv => ⟨hv.1, hv.2.2⟩`. Establish `s1 : EntSm (fun v => M1 (((manifold s.T.Z σ).chart i).e.symm v)) _` using `fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg1r a' b' i).mono sub1, (hg1i a' b' i).mono sub1⟩`. Establish `sw` using `(hw i).mono sub2`.

Establish `hf` using `ite_sm (c := τ (A.H.rt : D.host.E) = A.H.rt0) (mix_sm sw s0 s1) (mixDual_sm sw s0 s1 (fun v hv => p0 _ hv.2.1.2) (fun v hv => p1 _ hv.2.1.2 hv.2.2) fun v _ => x.wt_mem R _) a b`. Use `hf.congr fun v hv => ?_` and prove the remaining obligations. Simplify using `only [Function.comp]`. Rewrite using `[hgB _ hv.2.1.2 hv.2.2]`. Use `(s0 a b).congr fun v hv => ?_` and prove the remaining obligations.

Simplify using `only [Function.comp]`. Conclude with `hgW _ hv.2.1.2 hv.2.2`. Establish `hT : ∀ β, IsOpen (T β)` using `fun β => by cases β; exacts [hBo, hWo]`. Establish `hc : ∀ y ∈ Set.univ ∩ P, ∃ β, y ∈ T β` using `fun y _ => by`. Distinguish the cases in `hL : LiesIn y (genBd s.T.Z)`.

Conclude with `⟨true, hWbd y hL⟩`. Conclude with `⟨false, hL⟩`. Use `⟨g, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).1, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).2, fun y _ hy f hf => hg y hy f hf⟩` and prove the remaining obligations.
-/
theorem ToroidalCompactificationData.smoothOn_eigMetAt_some : ∀ (D : D7) (A : Amb D) (N j : ℕ) (S : Sig A N j) (κ : Lv A) (s : FinalTheorems S κ)
    (x : ToroidalCompactificationData s) (σ : κ.c.F →+* ℂ) (R : ℝ), 2 ≤ R →
    (x.hodge σ).SmoothOn (manifold s.T.Z σ) {y | ¬ LiesIn y (genBd s.T.Z)} →
    (x.eigMetAt σ (some R)).SmoothOn (manifold s.T.Z σ) Set.univ := by
  intro D A N j S κ s x σ R hR hH V φ F τ a b hφ
  classical
  set P := ptsIn (genStr s.T.Z) σ V.1 with hP
  set Bc := {y : CxPts (genStr s.T.Z) σ | ¬ LiesIn y (genBd s.T.Z)} with hBc
  have hBo : IsOpen Bc := isOpen_not_liesIn _

  have hphi : ∀ y (hy : y ∈ P), σ = (evHom hy).comp φ := fun y hy => by
    have e : spMap σ = spMap ((evHom hy).comp φ) := by
      rw [← y.2, ← spMap_evHom hy, Category.assoc, hφ, ← Spec.map_comp]; rfl
    exact spMap_inj e
  have hfr : ∀ y (hy : y ∈ P), ∃ f : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z), F.IsMap (evHom hy) f := fun y hy =>
    F.exists_isMap (evHom hy) (hphi y hy) (by rw [← Category.assoc, spMap_evHom hy])
  have huniq : ∀ y (hy : y ∈ P) (f f' : EigFrame s.T.Z σ (y.1 ≫ genι s.T.Z)), F.IsMap (evHom hy) f →
      F.IsMap (evHom hy) f' → f = f' := fun y hy f f' hf hf' => by
    have e : f.v = f'.v := funext fun τ => funext fun i => (hf τ i).trans (hf' τ i).symm
    cases f; cases f'
    cases e
    rfl

  choose g0 hg0r hg0i hg0 using fun a' b' => x.smoothOn_eigMet σ V φ F τ a' b' hφ
  choose g1 hg1r hg1i hg1 using fun a' b' => hH V φ F τ a' b' hφ
  let M0 := fun y => Matrix.of fun a' b' => g0 a' b' y
  let M1 := fun y => Matrix.of fun a' b' => g1 a' b' y
  have e0 : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMet σ).gram y f τ = M0 y := fun y hy f hf =>
    Matrix.ext fun a' b' => hg0 a' b' y (Set.mem_univ y) hy f hf
  have e1 : ∀ y (hy : y ∈ P), y ∈ Bc → ∀ f, F.IsMap (evHom hy) f → (x.hodge σ).gram y f τ = M1 y :=
    fun y hy hb f hf => Matrix.ext fun a' b' => hg1 a' b' y hb hy f hf
  have p0 : ∀ y ∈ P, (M0 y).PosDef := fun y hy => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e0 y hy f hf ▸ (x.eigMet σ).pos y f τ
  have p1 : ∀ y ∈ P, y ∈ Bc → (M1 y).PosDef := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    exact e1 y hy hb f hf ▸ (x.hodge σ).pos y f τ

  let g : CxPts (genStr s.T.Z) σ → ℂ := fun y =>
    if hy : y ∈ P then (x.eigMetAt σ (some R)).gram y (hfr y hy).choose τ a b else 0
  have hg : ∀ y (hy : y ∈ P) f, F.IsMap (evHom hy) f → (x.eigMetAt σ (some R)).gram y f τ a b = g y :=
    fun y hy f hf => by
      simp only [g, dif_pos hy]
      rw [huniq y hy f _ hf (hfr y hy).choose_spec]

  set W := {y : CxPts (genStr s.T.Z) σ | (∏ i, x.nrm σ i y) ^ 2 < Real.exp (Real.exp 1 - R ^ 3)} with hW
  have hcont : ∀ i, Continuous (x.nrm σ i) := fun i => continuous_iff_continuousAt.2 fun y => by
    obtain ⟨V', t, f, hy, -, hf, e⟩ := (x.nrm_div σ i).2 y
    have ho := isOpen_ptsIn (p := genStr s.T.Z) (σ := σ) V'.1
    have h1 : ContinuousOn (fun z => √(‖ev (genStr s.T.Z) σ V'.1 t z‖ ^ 2 * Real.exp (-f z))) (ptsIn _ σ V'.1) :=
      (((((manifold s.T.Z σ).holoOn_ev V'.1 t).continuousOn ho).norm.pow 2).mul
        ((hf.continuousOn ho).neg.rexp)).sqrt
    refine (h1.continuousAt (ho.mem_nhds hy)).congr (Filter.eventuallyEq_of_mem (ho.mem_nhds hy) fun z hz => ?_)
    rw [← e z hz, Real.sqrt_sq ((x.nrm_div σ i).1 z).1]
  have hWo : IsOpen W := isOpen_lt ((continuous_finset_prod _ fun i _ => hcont i).pow 2) continuous_const
  have hWbd : ∀ y, LiesIn y (genBd s.T.Z) → y ∈ W := fun y hy => by
    obtain ⟨i, hi⟩ := (x.liesIn_genBd_iff y).1 hy
    have h0 : x.nrm σ i y = 0 :=
      le_antisymm (not_lt.1 fun h => ((x.nrm_div σ i).pos_iff y).1 h hi) ((x.nrm_div σ i).1 y).1
    show (∏ i, x.nrm σ i y) ^ 2 < _
    rw [Finset.prod_eq_zero (Finset.mem_univ i) h0]
    simpa using Real.exp_pos _
  have hW0 : ∀ y ∈ W, x.wt σ R y = 0 := fun y hy => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact x.wt_eq_zero hR (Or.inl hL)
    · refine x.wt_eq_zero hR (Or.inr ?_)
      have hpos : 0 < (∏ i, x.nrm σ i y) ^ 2 := pow_pos (Finset.prod_pos fun i _ => x.nrm_pos hL i) 2
      have := (Real.log_lt_iff_lt_exp hpos).2 hy
      simp only [OddPrimesWithRootsOfUnity.r]
      linarith

  have hr : (manifold s.T.Z σ).SmoothOn Bc (x.r σ) := by
    refine AnRead.SmoothOn.congr (f := fun y => Real.exp 1 - ∑ i, Real.log (x.nrm σ i y ^ 2))
      (fun c => contDiffOn_const.sub (ContDiffOn.sum fun i _ => ((x.nrm_div σ i).smoothOn_log.mono
        fun y (hy : ¬ LiesIn y (genBd s.T.Z)) hi => hy ((x.liesIn_genBd_iff y).2 ⟨i, hi⟩)) c)) fun y hy => ?_
    simp only [OddPrimesWithRootsOfUnity.r]
    rw [← Finset.prod_pow, Real.log_prod fun i _ => pow_ne_zero _ (x.nrm_pos hy i).ne']
  have hw : (manifold s.T.Z σ).SmoothOn Bc (x.wt σ R) := by
    refine AnRead.SmoothOn.congr (f := fun y => cutWt x.kap R (x.r σ y)) (fun c => ?_) fun y hy => x.wt_eq hR hy
    have h1 := hr c
    have hpos : ∀ v, 0 < (x.r σ ∘ ((manifold s.T.Z σ).chart c).e.symm) v := fun v =>
      lt_of_lt_of_le (Real.exp_pos 1) (x.exp_le_r σ _)
    have hA := contDiff_cutoff.1.comp_contDiffOn ((h1.log fun v _ => (hpos v).ne').div_const (Real.log R))
    have hB := contDiffOn_const (c := (1 : ℝ)).add ((h1.div_const R).rpow_const_of_ne (p := x.kap)
      fun v _ => (div_pos (hpos v) (by linarith)).ne')
    refine (hA.div hB fun v _ => ?_).congr fun v _ => rfl
    exact (add_pos_of_pos_of_nonneg one_pos (Real.rpow_nonneg (div_nonneg (hpos v).le (by linarith)) _)).ne'

  have hgB : ∀ y ∈ P, y ∈ Bc → g y = (if τ (A.H.rt : D.host.E) = A.H.rt0 then mix (x.wt σ R y) (M0 y) (M1 y)
      else mixDual (x.wt σ R y) (M0 y) (M1 y)) a b := fun y hy hb => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf]
    simp only [ToroidalCompactificationData.eigMetAt, EigMet.interp]
    rw [e0 y hy f hf, e1 y hy hb f hf]

  have hgW : ∀ y ∈ P, y ∈ W → g y = g0 a b y := fun y hy hw' => by
    obtain ⟨f, hf⟩ := hfr y hy
    rw [← hg y hy f hf, ← hg0 a b y (Set.mem_univ y) hy f hf]
    exact congrFun (congrFun (EigMet.interp_gram_zero (hs := x.wt_mem R) f (hW0 y hw')) a) b

  let T : Bool → Set (CxPts (genStr s.T.Z) σ) := fun β => cond β W Bc
  have key : ∀ β i, ContDiffOn ℝ ∞ (g ∘ ((manifold s.T.Z σ).chart i).e.symm)
      (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) := by
    intro β i
    have sub : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β) ⊆
        ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Set.univ ∩ P) :=
      fun v hv => ⟨hv.1, hv.2.1⟩
    have s0 : EntSm (fun v => M0 (((manifold s.T.Z σ).chart i).e.symm v))
        (((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' ((Set.univ ∩ P) ∩ T β)) :=
      fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg0r a' b' i).mono sub, (hg0i a' b' i).mono sub⟩
    cases β
    · have sub1 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' (Bc ∩ P) :=
        fun v hv => ⟨hv.1, hv.2.2, hv.2.1.2⟩
      have sub2 : ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹'
          ((Set.univ ∩ P) ∩ T false) ⊆
          ((manifold s.T.Z σ).chart i).e.target ∩ ((manifold s.T.Z σ).chart i).e.symm ⁻¹' Bc :=
        fun v hv => ⟨hv.1, hv.2.2⟩
      have s1 : EntSm (fun v => M1 (((manifold s.T.Z σ).chart i).e.symm v)) _ :=
        fun a' b' => contDiffOn_iff_re_im.2 ⟨(hg1r a' b' i).mono sub1, (hg1i a' b' i).mono sub1⟩
      have sw := (hw i).mono sub2
      have hf := ite_sm (c := τ (A.H.rt : D.host.E) = A.H.rt0) (mix_sm sw s0 s1)
        (mixDual_sm sw s0 s1 (fun v hv => p0 _ hv.2.1.2) (fun v hv => p1 _ hv.2.1.2 hv.2.2)
          fun v _ => x.wt_mem R _) a b
      refine hf.congr fun v hv => ?_
      simp only [Function.comp]
      rw [hgB _ hv.2.1.2 hv.2.2]
    · refine (s0 a b).congr fun v hv => ?_
      simp only [Function.comp]
      exact hgW _ hv.2.1.2 hv.2.2
  have hT : ∀ β, IsOpen (T β) := fun β => by cases β; exacts [hBo, hWo]
  have hc : ∀ y ∈ Set.univ ∩ P, ∃ β, y ∈ T β := fun y _ => by
    by_cases hL : LiesIn y (genBd s.T.Z)
    · exact ⟨true, hWbd y hL⟩
    · exact ⟨false, hL⟩
  refine ⟨g, AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).1,
    AnRead.smoothOn_of_cover hT hc fun β i => (contDiffOn_iff_re_im.1 (key β i)).2, fun y _ hy f hf => hg y hy f hf⟩

end GlobalTheory.ShFam
