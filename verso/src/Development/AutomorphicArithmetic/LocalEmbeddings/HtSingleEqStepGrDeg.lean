import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.KernelSt
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DemaillyRegularisation
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MatrixLemma
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.AbsoluteSiegel
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.ScholzeWeinsteinB
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.QuasiPlurisubharmonic
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.LieAlgebraMaps
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiFibrationLieLatticeFullStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepLatZero
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.StepIdeal
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IsLocalHomOfAlgebraic
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.IoOfLeOneIff
import Development.AutomorphicArithmetic.DivisorFrames.IdealNormLogHeight
import Development.AutomorphicArithmetic.DivisorFrames.HeightLogNormFormula
import Development.AutomorphicArithmetic.DivisorFrames.CoordinateEigenframeEquation
import Development.AutomorphicArithmetic.DivisorFrames.LieLogEqIdealSupremum
import Development.AutomorphicArithmetic.DivisorFrames.LieLatticeGenerator
import Development.AutomorphicArithmetic.DivisorFrames.FibreHermitianEmbedding

section SlopeTestRemainingChoices

open CategoryTheory AlgebraicGeometry NumberField IsDedekindDomain ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj ReciprocityTheory.GeometryOfNumbersTheory GlobalTheory.Toroidal GlobalTheory.Cartier GlobalTheory.ProjVar GlobalTheory.TrueGeo GlobalTheory.CxPts GlobalTheory.Mean4O GlobalTheory.LieHt GlobalTheory.ShFam GlobalTheory.ShFam.Pad GlobalTheory.LieRead GlobalTheory.ShFam.CoordUniq GlobalTheory.GradedNorm
open scoped ComplexOrder

section Coord

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {O : Type} [CommRing O] {β : O →+* c.F}
  {Z : Model Xo c β} {F : Type} [Field F] [NumberField F] {e : F ≃+* c.F} (Y : FlagCpt Z e)
  {k : Type} [Field k] {φ : c.F →+* k} {x : Sp k ⟶ Z.X} {p : Sp k ⟶ Y.Y.X} {g : EigFrame Z φ x}
  {n : Letter Dw → ℤ} {s : Y.Y.Fn}

/- English proof (translation)
Establish `: CharZero c.F` using `RingHom.charZero c.F.val.toRingHom`. Take `⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩` from `h`. Establish `hl` using `isLocalHom_of_algebraic φ₁ ψ`. Establish `hy : below p = y`. Establish `h0 : p = spMap (Scheme.stalkClosedPointTo p).hom ≫ Y.Y.X.fromSpecStalk (below p)` using `(Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm`.

Conclude with `(stalk_ext inferInstance hl (h0.symm.trans h₁)).1`. Rewrite using `[hy]`. Take `⟨φ₂, f₂, t₂, hT, ht⟩` from `Y.gr_spec y`. Take `⟨u, hu⟩` from `exists_unit_ratio f f₂ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) h₂ hT`. Establish `ht' : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i)` using `fun τ i => (ht τ i).iff_unitAt.2 ⟨u τ i, (u τ i).isUnit, by`.

Rewrite using `[hu _ _ _ _ h₂ hT τ i, Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _)]`. Use the proof step `rfl⟩`. Establish `hE : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z)` using `fun s => by classical`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using CartierDiv.isEqn_zero y`.

Consider the case `insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]`. Conclude with `((ht' _ _).zsmul _).add ih`. Take `⟨r, hru, hr⟩` from `(Base.isEqn_eqn (divOf Y n) y).iff_unitAt.1 (hE Finset.univ)`. Use `⟨_, mul_ne_zero (hru.map ψ).ne_zero (Units.ne_zero _), y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, ?_, rfl⟩` and prove the remaining obligations. Rewrite using `[hr, Units.val_inv_eq_inv_val, div_eq_inv_mul]`.
-/
private theorem exists_coord_gen [CharZero k] [Algebra.IsAlgebraic ℚ k] (n : Letter Dw → ℤ) (h : Y.Carries p g) :
    ∃ a, a ≠ 0 ∧ IsCoord Y p g n (((eqn (divOf Y n) (below p))⁻¹ : Y.Y.Fnˣ) : Y.Y.Fn) a := by
  have : CharZero c.F := RingHom.charZero c.F.val.toRingHom
  obtain ⟨y, ψ, φ₁, f, t, t', h₁, h₂, h₃⟩ := h
  have hl := isLocalHom_of_algebraic φ₁ ψ
  have hy : below p = y := by
    have h0 : p = spMap (Scheme.stalkClosedPointTo p).hom ≫ Y.Y.X.fromSpecStalk (below p) :=
      (Scheme.Spec_stalkClosedPointTo_fromSpecStalk p).symm
    exact (stalk_ext inferInstance hl (h0.symm.trans h₁)).1
  rw [hy]
  obtain ⟨φ₂, f₂, t₂, hT, ht⟩ := Y.gr_spec y
  obtain ⟨u, hu⟩ := exists_unit_ratio f f₂ (IsFractionRing.injective (Y.Y.X.presheaf.stalk y) Y.Y.X.functionField) h₂ hT
  have ht' : ∀ τ i, (Y.gr τ i).IsEqn y (t τ i) := fun τ i => (ht τ i).iff_unitAt.2
    ⟨u τ i, (u τ i).isUnit, by
      rw [hu _ _ _ _ h₂ hT τ i, Units.val_mul, mul_div_cancel_left₀ _ (Units.ne_zero _)]; rfl⟩
  have hE : ∀ s : Finset (Letter Dw), (∑ z ∈ s, n z • Y.gr z.1 z.2).IsEqn y (∏ z ∈ s, t z.1 z.2 ^ n z) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using CartierDiv.isEqn_zero y
    | insert z s hz ih => rw [Finset.sum_insert hz, Finset.prod_insert hz]; exact ((ht' _ _).zsmul _).add ih
  obtain ⟨r, hru, hr⟩ := (Base.isEqn_eqn (divOf Y n) y).iff_unitAt.1 (hE Finset.univ)
  refine ⟨_, mul_ne_zero (hru.map ψ).ne_zero (Units.ne_zero _), y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, ?_, rfl⟩
  rw [hr, Units.val_inv_eq_inv_val, div_eq_inv_mul]

/- English proof (translation)
Take `⟨y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, h₄, rfl⟩` from `h`. Use `⟨y, θ.comp ψ, φ₁, f, t, fun τ i => Units.map θ.toMonoidHom (t' τ i), r, ?_, h₂, ⟨?_, ?_, fun τ i => ?_⟩, h₄, ?_⟩` and prove the remaining obligations. Rewrite using `[h₁, ← Category.assoc, ← Spec.map_comp]`. Both sides reduce to the same expression. Rewrite using `[hx, h₃.1, ← Category.assoc, ← Spec.map_comp]`.

Both sides reduce to the same expression. Rewrite using `[hφ, h₃.2.1]`. Both sides reduce to the same expression. Take `⟨cf, e1, e2, e3⟩` from `h₃.2.2 τ i`. Use `⟨fun a => θ (cf a), congrArg θ e1, fun a ha => (congrArg θ (e2 a ha)).trans (map_zero θ), ?_⟩` and prove the remaining obligations.

Use `GlobalTheory.LatDRFree.comb_map _ θ e3` as an intermediate fact. Simplify using `only [GlobalTheory.GradedPieces.dual_comp] at this`. Rewrite using `[hg τ i, hx]`. Conclude with `this`. Simplify using `only [← map_zpow, ← map_prod, map_mul]`.

Both sides reduce to the same expression.
-/
private theorem coord_map {a : k} (h : IsCoord Y p g n s a) {k' : Type} [Field k'] (θ : k →+* k') {φ' : c.F →+* k'}
    {x' : Sp k' ⟶ Z.X} {g' : EigFrame Z φ' x'} (hg : g.IsMap θ g') (hφ : φ' = θ.comp φ) (hx : x' = spMap θ ≫ x) :
    IsCoord Y (spMap θ ≫ p) g' n s (θ a) := by
  obtain ⟨y, ψ, φ₁, f, t, t', r, h₁, h₂, h₃, h₄, rfl⟩ := h
  refine ⟨y, θ.comp ψ, φ₁, f, t, fun τ i => Units.map θ.toMonoidHom (t' τ i), r, ?_, h₂, ⟨?_, ?_, fun τ i => ?_⟩, h₄, ?_⟩
  · rw [h₁, ← Category.assoc, ← Spec.map_comp]; rfl
  · rw [hx, h₃.1, ← Category.assoc, ← Spec.map_comp]; rfl
  · rw [hφ, h₃.2.1]; rfl
  · obtain ⟨cf, e1, e2, e3⟩ := h₃.2.2 τ i
    refine ⟨fun a => θ (cf a), congrArg θ e1, fun a ha => (congrArg θ (e2 a ha)).trans (map_zero θ), ?_⟩
    have := GlobalTheory.LatDRFree.comb_map _ θ e3
    simp only [GlobalTheory.GradedPieces.dual_comp] at this
    rw [hg τ i, hx]
    exact this
  · simp only [← map_zpow, ← map_prod, map_mul]
    rfl

end Coord

/- English proof (translation)
Introduce `D O x y hy K _ _ F ι h hT hH θ σ hσ yc hyc f hf τ a b`. Distinguish the cases in `hg : GoodEmb O.κ.c σ`. Conclude with `UpperTheory.fibre_hermitian_embedding D O x y hy K F ι h hT hH θ σ hg hσ yc hyc f hf τ a b`. Establish `h1 : GoodEmb O.κ.c ((starRingEnd ℂ).comp σ)` using `by simpa only [goodOf, if_neg hg] using goodEmb_goodOf O.κ.c σ`. Set `y' : GlobalTheory.CxPts (genStr O.s.T.Z) ((starRingEnd ℂ).comp σ)` to `⟨spMap (starRingEnd ℂ) ≫ yc.1, by rw [Category.assoc, yc.2, ← Spec.map_comp]; rfl⟩`.

Establish `hx : y'.1 ≫ genι O.s.T.Z = spMap (starRingEnd ℂ) ≫ yc.1 ≫ genι O.s.T.Z` using `Category.assoc _ _ _`. Take `⟨f', hf'⟩` from `f.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) rfl hx`. Establish `e1` using `UpperTheory.fibre_hermitian_embedding D O x y hy K F ι h hT hH ((starRingEnd ℂ).comp θ) _ h1 (by rw [hσ]; rfl) y' (by simp only [y', hyc]; rw [← Category.assoc, ← Spec.map_comp]; rfl) f' (fun τ i => by rw [hf', hf, GlobalTheory.GradedPieces.dual_comp]) τ a b`. Establish `e2` using `(GlobalTheory.T.semi_fibration_lie_lattice_full K F).2.2.1 h hH (θ.comp ι) (stepVec O F τ a) (stepVec O F τ b)`. Establish `hin : ¬ LiesIn y' (genBd O.s.T.Z)`.

Establish `: y'.1 (IsLocalRing.closedPoint ℂ) = below y.y`. Simplify using `only [y', hyc, ← Category.assoc]`. Conclude with `(Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum Qb) _ _))`. Rewrite using `[LiesIn, this]`. Conclude with `hy`.

Take `⟨g', hg'⟩` from `FinalTheorems.exists_isHodgeFrame_iff.2 hin`. Establish `hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ` using `RingHom.ext Complex.conj_conj`. Establish `hc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _`. Rewrite using `[← Spec.map_comp, ← Spec.map_id]`. Conclude with `congrArg Spec.map (CommRingCat.hom_ext hcc)`.

Take `⟨g, hg₁⟩` from `g'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := yc.1 ≫ genι O.s.T.Z) (RingHom.ext fun _ => (Complex.conj_conj _).symm) (by simp only [y', ← Category.assoc, hc, Category.id_comp])`. Establish `hg₂ : g.IsMap (starRingEnd ℂ) g'` using `fun τ i => by`. Rewrite using `[hg₁, GlobalTheory.GradedPieces.dual_comp, hcc, spMap_dualMap_id, Category.id_comp]`. Establish `e3` using `x.hodge_gram hg' f' τ`. Rewrite `e3` using `[hg₂.co τ hf' hx]`.

Rewrite using `[x.hodge_gram (hg'.conj rfl rfl hg₂) f τ]`. Apply `(starRingEnd ℂ).injective` to reduce the goal to its premises. Rewrite using `[← e2, ← RingHom.comp_assoc, ← e1, e3]`. Simplify using `[Matrix.mul_apply, map_ofNat]`.
-/
private theorem gram_all : ∀ (D : D7) (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pt O.s), below y.y ∉ genBd O.s.T.Z → ∀ (K : Type) [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K)), FibTie O y F ι → F.IsHerm h → ∀ (θ : Qb →+* ℂ) (σ : O.κ.c.F →+* ℂ),  σ = θ.comp y.fK → ∀ (yc : GlobalTheory.CxPts (genStr O.s.T.Z) σ), yc.1 = spMap θ ≫ y.y → ∀ f : EigFrame O.s.T.Z σ (yc.1 ≫ genι O.s.T.Z), y.frame.IsMap θ f → ∀ (τ : D.host.E →+* ℂ) (a b : Fin (O.S.Dw.mult τ)), (x.hodge σ).gram yc f τ a b = h.form (θ.comp ι) (stepVec O F τ a) (stepVec O F τ b) := by
  intro D O x y hy K _ _ F ι h hT hH θ σ hσ yc hyc f hf τ a b
  by_cases hg : GoodEmb O.κ.c σ
  · exact UpperTheory.fibre_hermitian_embedding D O x y hy K F ι h hT hH θ σ hg hσ yc hyc f hf τ a b
  have h1 : GoodEmb O.κ.c ((starRingEnd ℂ).comp σ) := by simpa only [goodOf, if_neg hg] using goodEmb_goodOf O.κ.c σ
  let y' : GlobalTheory.CxPts (genStr O.s.T.Z) ((starRingEnd ℂ).comp σ) :=
    ⟨spMap (starRingEnd ℂ) ≫ yc.1, by rw [Category.assoc, yc.2, ← Spec.map_comp]; rfl⟩
  have hx : y'.1 ≫ genι O.s.T.Z = spMap (starRingEnd ℂ) ≫ yc.1 ≫ genι O.s.T.Z := Category.assoc _ _ _
  obtain ⟨f', hf'⟩ := f.exists_isMap (starRingEnd ℂ) (φ' := (starRingEnd ℂ).comp σ) rfl hx
  have e1 := UpperTheory.fibre_hermitian_embedding D O x y hy K F ι h hT hH ((starRingEnd ℂ).comp θ) _ h1 (by rw [hσ]; rfl) y'
    (by simp only [y', hyc]; rw [← Category.assoc, ← Spec.map_comp]; rfl) f'
    (fun τ i => by rw [hf', hf, GlobalTheory.GradedPieces.dual_comp]) τ a b
  have e2 := (GlobalTheory.T.semi_fibration_lie_lattice_full K F).2.2.1 h hH (θ.comp ι) (stepVec O F τ a) (stepVec O F τ b)
  have hin : ¬ LiesIn y' (genBd O.s.T.Z) := by
    have : y'.1 (IsLocalRing.closedPoint ℂ) = below y.y := by
      simp only [y', hyc, ← Category.assoc]
      exact (Scheme.Hom.comp_apply _ _ _).trans (congrArg _ (Subsingleton.elim (α := PrimeSpectrum Qb) _ _))
    rw [LiesIn, this]; exact hy
  obtain ⟨g', hg'⟩ := FinalTheorems.exists_isHodgeFrame_iff.2 hin
  have hcc : (starRingEnd ℂ).comp (starRingEnd ℂ) = RingHom.id ℂ := RingHom.ext Complex.conj_conj
  have hc : spMap (starRingEnd ℂ) ≫ spMap (starRingEnd ℂ) = 𝟙 _ := by
    rw [← Spec.map_comp, ← Spec.map_id]
    exact congrArg Spec.map (CommRingCat.hom_ext hcc)
  obtain ⟨g, hg₁⟩ := g'.exists_isMap (starRingEnd ℂ) (φ' := σ) (x' := yc.1 ≫ genι O.s.T.Z)
    (RingHom.ext fun _ => (Complex.conj_conj _).symm) (by simp only [y', ← Category.assoc, hc, Category.id_comp])
  have hg₂ : g.IsMap (starRingEnd ℂ) g' := fun τ i => by
    rw [hg₁, GlobalTheory.GradedPieces.dual_comp, hcc, spMap_dualMap_id, Category.id_comp]
  have e3 := x.hodge_gram hg' f' τ
  rw [hg₂.co τ hf' hx] at e3
  rw [x.hodge_gram (hg'.conj rfl rfl hg₂) f τ]
  apply (starRingEnd ℂ).injective
  rw [← e2, ← RingHom.comp_assoc, ← e1, e3]
  simp [Matrix.mul_apply, map_ofNat]

/- English proof (translation)
Establish `e1 (k : Fin (O.S.Dw.mult τ + 1)) : ReciprocityTheory.ChartRestriction.G.FD.lminor M k = (h.gram s fun j : Fin k => stepVec O F τ j).det`. Use `congrArg Matrix.det ?_` and prove the remaining obligations. Use extensionality with `a b`. Conclude with `e _ _`. Establish `p1` using `Complex.pos_iff.1 (lminor_pos hM i.succ)`.

Establish `p2` using `Complex.pos_iff.1 (lminor_pos hM i.castSucc)`. Establish `e2 : stepGrSq O F h τ i s = (ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ).re / (ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc).re`. Rewrite using `[e1, e1]`. Both sides reduce to the same expression. Rewrite using `[e2, grSq, ← Complex.div_ofReal_re]`.

Use `congr 2`. Conclude with `Complex.ext rfl p2.2.symm`.
-/
private theorem grSq_eq {D : D7} (O : Setup D) {K : Type} [Field K] [NumberField K] (F : SemiFib K)
    (h : HermFam K (Fin F.P₀.g → K)) (τ : D.host.E →+* ℂ) (s : K →+* ℂ)
    {M : Matrix (Fin (O.S.Dw.mult τ)) (Fin (O.S.Dw.mult τ)) ℂ} (hM : M.PosDef)
    (e : ∀ a b, M a b = h.form s (stepVec O F τ a) (stepVec O F τ b)) (i : Fin (O.S.Dw.mult τ)) :
    grSq M i = stepGrSq O F h τ i s := by
  have e1 (k : Fin (O.S.Dw.mult τ + 1)) : ReciprocityTheory.ChartRestriction.G.FD.lminor M k =
      (h.gram s fun j : Fin k => stepVec O F τ j).det := by
    refine congrArg Matrix.det ?_
    ext a b
    exact e _ _
  have p1 := Complex.pos_iff.1 (lminor_pos hM i.succ)
  have p2 := Complex.pos_iff.1 (lminor_pos hM i.castSucc)
  have e2 : stepGrSq O F h τ i s = (ReciprocityTheory.ChartRestriction.G.FD.lminor M i.succ).re / (ReciprocityTheory.ChartRestriction.G.FD.lminor M i.castSucc).re := by
    rw [e1, e1]; rfl
  rw [e2, grSq, ← Complex.div_ofReal_re]
  congr 2
  exact Complex.ext rfl p2.2.symm

/- English proof (translation)
Establish `: Algebra.IsAlgebraic ℚ Qb` using `algebraicClosure.isAlgebraic ℚ ℂ`. Take `⟨p, hp, hc, hb⟩` from `liesUnder_basePt O.Φ y`. Rewrite using `[← hb]`. Use `clear hb`. Generalize the expression as in `compPt O.s y = k at p hp hc ⊢`.

Establish `hg : F.P₀.g = (letters O.S.Dw).length`. Take `⟨-, -, -, -, -, -, -, e, -⟩` from `hT`. Conclude with `e`. Take `⟨q, -, -, hfg, ⟨v₀, hv₀, hv₁, hv₂⟩, hset⟩` from `UpperTheory.lie_lattice_generator D O K F τ i hi hg`. Establish `ha : ∃ a ∈ stepIdeal O F τ i, a ≠ 0` using `⟨v₀ q, by rw [← SetLike.mem_coe, hset]; exact ⟨v₀, hv₀, hv₁, rfl⟩, hv₂⟩`.

Take `⟨n, c, hn, hc0, hsup, hidx⟩` from `UpperTheory.ideal_norm_log_height K _ ha.choose hfg ha.choose_spec.1 ha.choose_spec.2`. Establish `hn' : (n : ℝ) ≠ 0` using `Nat.cast_ne_zero.2 hn.ne'`. Take `⟨β, hβ, hco⟩` from `exists_coord_gen (O.Φ.C k) (expo O.S.Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) hc`. Establish `hstr : p ≫ (O.Φ.C k).Y.str = spMap (y.fK.comp O.κ.e.toRingHom)`. Rewrite using `[← (O.Φ.C k).π_str, ← Category.assoc, hp, ← Category.assoc, y.y_over, ← Spec.map_comp]`.

Both sides reduce to the same expression. Establish `key` using `UpperTheory.height_log_norm_formula D.what₂.LL K (cxSt D.what₂.LL) (O.Φ.C k).Y (adlOf (O.Φ.C k) (metsOf x O.Φ k) (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) _ p ι β c (n : ℝ)⁻¹ (fun s => (1 / 2) * Real.log (stepGrSq O F h τ i s)) rfl rfl hstr hβ hc0 …`. Rewrite using `[key, stepGrDeg, dif_pos ha, ← Finset.mul_sum]`. Use `congr 2`. Clear the denominators using the available nonvanishing facts.

Combine the linear equalities and inequalities to obtain the conclusion. Introduce `θ σ z hz`. Establish `hσ : embOf O.κ.e σ = θ.comp y.fK`. Establish `h1` using `((O.Φ.C k).down z).2`. Establish `h2 : ((O.Φ.C k).down z).1 ≫ genStr O.s.T.Z = spMap (θ.comp y.fK)` using `by show (z.1 ≫ _) ≫ _ = _`.

Rewrite using `[hz, Category.assoc, Category.assoc, ← Category.assoc p, hp, y.y_over, ← Spec.map_comp]`. Both sides reduce to the same expression. Conclude with `EigLoc.spMap_inj (h1.symm.trans h2)`. Establish `hd : ((O.Φ.C k).down z).1 = spMap θ ≫ y.y` using `by show z.1 ≫ _ = _`. Rewrite using `[hz, Category.assoc, hp]`.

Establish `hx : ((O.Φ.C k).down z).1 ≫ genι O.s.T.Z = spMap θ ≫ y.y ≫ genι O.s.T.Z` using `by rw [hd, Category.assoc]`. Take `⟨g, hgm⟩` from `y.frame.exists_isMap θ hσ hx`. Establish `h3` using `coord_map _ hco θ hgm hσ hx`. Rewrite `h3` using `[← hz]`. Establish `hpar : parOf (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ) = none`.

Establish `hne : ((Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)).support.Nonempty` using `⟨_, Finsupp.mem_support_iff.2 (by rw [Finsupp.single_eq_same]; exact one_ne_zero)⟩`. Rewrite using `[parOf, dif_pos hne, Finset.mem_singleton.1 (Finsupp.support_single_subset hne.choose_spec)]`. Establish `h4` using `pn_metsOf (x := x) (parOf (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) (g := g) h3`. Establish `hpos` using `(x.hodge (embOf O.κ.e σ)).pos _ g τ`. Establish `h5` using `grSq_eq O F h τ (θ.comp ι) hpos (gram_all D O x y hy K F ι h hT hH θ _ hσ _ hd g hgm τ) ⟨i, hi⟩`.

Establish `h6 : letterOf O.S.Dw (Sum.inl (τ, i)) = some ⟨τ, ⟨i, hi⟩⟩` using `dif_pos hi`. Rewrite using `[Finset.prod_eq_single (⟨τ, ⟨i, hi⟩⟩ : Letter O.S.Dw) (fun b _ hb => by`. Rewrite using `[expo_single, h6, if_neg (fun e => hb (Option.some.inj e).symm), zpow_zero]) (by simp),`. Use the proof step `expo_single, h6, if_pos rfl, zpow_one] at h4`. Use `(congrArg (fun r => Real.log r / 2) h4).trans ?_` and prove the remaining obligations.

Rewrite using `[hpar]`. Establish `h7` using `grSq_pos hpos ⟨i, hi⟩`. Use `show Real.log (_ * grSq ((x.hodge (embOf O.κ.e σ)).gram _ g τ) ⟨i, hi⟩) / 2 = _`. Rewrite using `[Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero θ).2 hβ))) h7.ne', h5, Real.log_pow]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Introduce `v ε θ z hz`. Take `⟨hpr, -, hw⟩` from `ioOf_spec _ v ε`. Use `haveI := Fact.mk hpr`. Use `(UpperTheory.coordinate_eigenframe_equation D O k y p τ i β hi hp hβ hco v ε θ z hz).trans ?_` and prove the remaining obligations.

Rewrite using `[UpperTheory.lie_log_eq_ideal_supremum D O y K F ι hT _ _ τ i hi, hw (θ (ι c))]`. Set `j : K →+* ℂ_[resP v]` to `((ioOf (resP v) ε).comp θ).comp ι`. Set `u : AbsoluteValue K ℝ` to `(NormedField.toAbsoluteValue ℂ_[resP v]).comp j.injective`. Establish `hu : IsNonarchimedean u` using `fun a b => by show ‖j (a + b)‖ ≤ max ‖j a‖ ‖j b‖`. Rewrite using `[map_add]`.

Conclude with `IsUltrametricDist.norm_add_le_max _ _`. Establish `h1` using `congrArg Real.log (hsup u hu)`. Rewrite `h1` using `[Real.log_pow]`. Establish `h2 : Real.log ‖ioOf (resP v) ε (θ (ι c))‖ = n * Real.log (sSup ((fun b => ‖((ioOf (resP v) ε).comp θ) (ι b)‖) '' (stepIdeal O F τ i : Set K)))` using `h1.symm`. Rewrite using `[h2]`.

Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.LieRead.ht_single_eq_stepGrDeg {D : D7} (O : Setup D) (x : ToroidalCompactificationData O.s) (y : Pt O.s) (hy : below y.y ∉ genBd O.s.T.Z)
    {K : Type} [Field K] [NumberField K] (F : SemiFib K) (ι : K →+* Qb) (h : HermFam K (Fin F.P₀.g → K))
    (hT : FibTie O y F ι) (hH : F.IsHerm h) (τ : D.host.E →+* ℂ) (i : ℕ) (hi : i < O.S.Dw.mult τ) :
    (adlOf (O.Φ.C _) (metsOf x O.Φ _) (Finsupp.single (ArIn.ind ∅, none, .inl (τ, i)) 1)).ht (basePt O.Φ y) =
      stepGrDeg O F h τ i := by
  classical
  have : Algebra.IsAlgebraic ℚ Qb := algebraicClosure.isAlgebraic ℚ ℂ
  obtain ⟨p, hp, hc, hb⟩ := liesUnder_basePt O.Φ y
  rw [← hb]
  clear hb
  generalize compPt O.s y = k at p hp hc ⊢
  have hg : F.P₀.g = (letters O.S.Dw).length := by
    obtain ⟨-, -, -, -, -, -, -, e, -⟩ := hT
    exact e
  obtain ⟨q, -, -, hfg, ⟨v₀, hv₀, hv₁, hv₂⟩, hset⟩ := UpperTheory.lie_lattice_generator D O K F τ i hi hg
  have ha : ∃ a ∈ stepIdeal O F τ i, a ≠ 0 :=
    ⟨v₀ q, by rw [← SetLike.mem_coe, hset]; exact ⟨v₀, hv₀, hv₁, rfl⟩, hv₂⟩
  obtain ⟨n, c, hn, hc0, hsup, hidx⟩ := UpperTheory.ideal_norm_log_height K _ ha.choose hfg ha.choose_spec.1 ha.choose_spec.2
  have hn' : (n : ℝ) ≠ 0 := Nat.cast_ne_zero.2 hn.ne'
  obtain ⟨β, hβ, hco⟩ := exists_coord_gen (O.Φ.C k) (expo O.S.Dw (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) hc
  have hstr : p ≫ (O.Φ.C k).Y.str = spMap (y.fK.comp O.κ.e.toRingHom) := by
    rw [← (O.Φ.C k).π_str, ← Category.assoc, hp, ← Category.assoc, y.y_over, ← Spec.map_comp]; rfl
  have key := UpperTheory.height_log_norm_formula D.what₂.LL K (cxSt D.what₂.LL) (O.Φ.C k).Y (adlOf (O.Φ.C k) (metsOf x O.Φ k) (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) _ p ι β c
    (n : ℝ)⁻¹ (fun s => (1 / 2) * Real.log (stepGrSq O F h τ i s)) rfl rfl hstr hβ hc0 ?_ ?_
  · rw [key, stepGrDeg, dif_pos ha, ← Finset.mul_sum]
    congr 2
    field_simp
    linarith
  · intro θ σ z hz
    have hσ : embOf O.κ.e σ = θ.comp y.fK := by
      have h1 := ((O.Φ.C k).down z).2
      have h2 : ((O.Φ.C k).down z).1 ≫ genStr O.s.T.Z = spMap (θ.comp y.fK) := by
        show (z.1 ≫ _) ≫ _ = _
        rw [hz, Category.assoc, Category.assoc, ← Category.assoc p, hp, y.y_over, ← Spec.map_comp]; rfl
      exact EigLoc.spMap_inj (h1.symm.trans h2)
    have hd : ((O.Φ.C k).down z).1 = spMap θ ≫ y.y := by
      show z.1 ≫ _ = _
      rw [hz, Category.assoc, hp]
    have hx : ((O.Φ.C k).down z).1 ≫ genι O.s.T.Z = spMap θ ≫ y.y ≫ genι O.s.T.Z := by rw [hd, Category.assoc]
    obtain ⟨g, hgm⟩ := y.frame.exists_isMap θ hσ hx
    have h3 := coord_map _ hco θ hgm hσ hx
    rw [← hz] at h3
    have hpar : parOf (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ) = none := by
      have hne : ((Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)).support.Nonempty := ⟨_, Finsupp.mem_support_iff.2 (by rw [Finsupp.single_eq_same]; exact one_ne_zero)⟩
      rw [parOf, dif_pos hne, Finset.mem_singleton.1 (Finsupp.support_single_subset hne.choose_spec)]
    have h4 := pn_metsOf (x := x) (parOf (Finsupp.single (ArIn.ind ∅, none, Sum.inl (τ, i)) 1 : Sym D.host.E →₀ ℤ)) (g := g) h3
    have hpos := (x.hodge (embOf O.κ.e σ)).pos _ g τ
    have h5 := grSq_eq O F h τ (θ.comp ι) hpos (gram_all D O x y hy K F ι h hT hH θ _ hσ _ hd g hgm τ) ⟨i, hi⟩
    have h6 : letterOf O.S.Dw (Sum.inl (τ, i)) = some ⟨τ, ⟨i, hi⟩⟩ := dif_pos hi
    rw [Finset.prod_eq_single (⟨τ, ⟨i, hi⟩⟩ : Letter O.S.Dw) (fun b _ hb => by
      rw [expo_single, h6, if_neg (fun e => hb (Option.some.inj e).symm), zpow_zero]) (by simp),
      expo_single, h6, if_pos rfl, zpow_one] at h4
    refine (congrArg (fun r => Real.log r / 2) h4).trans ?_
    rw [hpar]
    have h7 := grSq_pos hpos ⟨i, hi⟩
    show Real.log (_ * grSq ((x.hodge (embOf O.κ.e σ)).gram _ g τ) ⟨i, hi⟩) / 2 = _
    rw [Real.log_mul (pow_ne_zero _ (norm_ne_zero_iff.2 ((map_ne_zero θ).2 hβ))) h7.ne', h5, Real.log_pow]
    push_cast
    ring
  · intro v ε θ z hz
    obtain ⟨hpr, -, hw⟩ := ioOf_spec _ v ε
    haveI := Fact.mk hpr
    refine (UpperTheory.coordinate_eigenframe_equation D O k y p τ i β hi hp hβ hco v ε θ z hz).trans ?_
    rw [UpperTheory.lie_log_eq_ideal_supremum D O y K F ι hT _ _ τ i hi, hw (θ (ι c))]
    let j : K →+* ℂ_[resP v] := ((ioOf (resP v) ε).comp θ).comp ι
    let u : AbsoluteValue K ℝ := (NormedField.toAbsoluteValue ℂ_[resP v]).comp j.injective
    have hu : IsNonarchimedean u := fun a b => by
      show ‖j (a + b)‖ ≤ max ‖j a‖ ‖j b‖
      rw [map_add]; exact IsUltrametricDist.norm_add_le_max _ _
    have h1 := congrArg Real.log (hsup u hu)
    rw [Real.log_pow] at h1
    have h2 : Real.log ‖ioOf (resP v) ε (θ (ι c))‖ = n * Real.log (sSup ((fun b => ‖((ioOf (resP v) ε).comp θ) (ι b)‖) ''
      (stepIdeal O F τ i : Set K))) := h1.symm
    rw [h2]
    field_simp
    ring

end SlopeTestRemainingChoices
