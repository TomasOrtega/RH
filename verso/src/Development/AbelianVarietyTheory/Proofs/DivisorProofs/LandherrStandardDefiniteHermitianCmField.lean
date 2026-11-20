import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CTUnitsLeft
import Development.AbelianVarietyTheory.PublishedTheorems.TwistedTraceFormula.ExistsOrthonormalOfUnimodular
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HeightOneSpectrumPlacesOverFiniteSet
import GroundTheory.GlobalFields.SemilocalAlgebras.Finite
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT GlobalTheory.UnitaryClasses
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

noncomputable section

namespace GlobalTheory.LandherrStd

open GroundTheory.Global.SemiLocal
open scoped GroundTheory.Global.SemiLocal

variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
Rewrite using `[finrank_eq_ramificationIdx_mul_inertiaDeg E v u]`. Conclude with `Nat.mul_pos (Ideal.ramificationIdx_pos u.asIdeal _) (Ideal.inertiaDeg_pos _ _)`.
-/
theorem finrank_pos (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) (u : HeightOneSpectrum (𝓞 E))
    [u.asIdeal.LiesOver v.asIdeal] :
    0 < Module.finrank (v.adicCompletion (maximalRealSubfield E)) (u.adicCompletion E) := by
  rw [finrank_eq_ramificationIdx_mul_inertiaDeg E v u]
  exact Nat.mul_pos (Ideal.ramificationIdx_pos u.asIdeal _) (Ideal.inertiaDeg_pos _ _)

/- English proof (translation)
The claim follows from `(RingHom.map_det f M).symm`.
-/
theorem det_map' {R S : Type*} [CommRing R] [CommRing S] (f : R →+* S) {n : ℕ}
    (M : Matrix (Fin n) (Fin n) R) : (M.map f).det = f M.det :=
  (RingHom.map_det f M).symm

/- English proof (translation)
Use `set Fv := v.adicCompletion (maximalRealSubfield E)`. Use `haveI : CharZero Fv := charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield E) Fv).injective`. Establish `hd0 : d ≠ 0` using `fun h => mul_ne_zero hθ0 hθ0 (hd.symm.trans (by rw [h]; rfl))`. Distinguish the cases in `hsq : IsSquare (algebraMap _ Fv d)`. Conclude with `GlobalTheory.Published.HasseNormSt.of_isSquare ((_root_.map_ne_zero _).2 hd0) hsq _`.

Take `⟨w, hw⟩` from `(GlobalTheory.QNorm.places_over (maximalRealSubfield E) E).2.1 v`. Use `haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩`. Use `set ι := completionMap v w with hιdef`. Establish `hι : ∀ x : maximalRealSubfield E, ι (algebraMap _ Fv x) = algebraMap E (w.adicCompletion E) (x : E)`. Introduce `x`.

Rewrite using `[hιdef, completionMap_algebraMap, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E]`. Both sides reduce to the same expression. Use `set t := algebraMap E (w.adicCompletion E) θ with htdef`. Establish `ht2 : t * t = ι (algebraMap _ Fv d)` using `by rw [hι, hd, map_mul]`. Establish `hnot : ∀ s : Fv, t ≠ ι s`.

Introduce `s hs`. Apply `hsq` to reduce the goal to its premises. Use `⟨s, ι.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← ht2, map_mul, hs]`. Establish `hsm : ∀ (s : Fv) (y : w.adicCompletion E), s • y = ι s * y` using `fun s y => Algebra.smul_def s y`.

Establish `hli : LinearIndependent Fv ![(1 : w.adicCompletion E), t]`. Rewrite using `[LinearIndependent.pair_iff]`. Introduce `s r h`. Rewrite `h` using `[hsm, hsm, mul_one]`. Distinguish the cases in `hr : r = 0`.

Substitute `hr` using the available equality. Rewrite `h` using `[map_zero, zero_mul, add_zero]`. Conclude with `⟨ι.injective (by rw [h, map_zero]), rfl⟩`. It suffices to derive a contradiction. Apply `hnot (-s / r)` to reduce the goal to its premises.

Establish `hr' : ι r ≠ 0` using `(_root_.map_ne_zero ι).2 hr`. Rewrite using `[map_div₀, map_neg]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `h`. Establish `hsum` using `sum_finrank_eq E v`.

Rewrite `hsum` using `[Algebra.IsQuadraticExtension.finrank_eq_two]`. Establish `hle : Module.finrank Fv (w.adicCompletion E) ≤ 2`. Rewrite using `[← hsum]`. Conclude with `Finset.single_le_sum (f := fun u : PlacesOver E v => Module.finrank Fv (u.1.adicCompletion E)) (fun _ _ => Nat.zero_le _) (Finset.mem_univ ⟨w, inferInstance⟩)`. Use `haveI : Module.Finite Fv (w.adicCompletion E) := Module.finite_of_finrank_pos (finrank_pos v w)`.

Establish `hge : 2 ≤ Module.finrank Fv (w.adicCompletion E)`. Simplify using `using hli.fintype_card_le_finrank`. Establish `h2 : Module.finrank Fv (w.adicCompletion E) = 2` using `le_antisymm hle hge`. Establish `hns : ¬ IsSplitAt w`. Introduce and unpack `⟨u, hne, hu⟩`.

Use `haveI : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, ← hu, HeightOneSpectrum.under_asIdeal]⟩`. Establish `hpos` using `finrank_pos v u`. Establish `hne' : (⟨u, inferInstance⟩ : PlacesOver E v) ≠ ⟨w, inferInstance⟩` using `fun h => hne (congrArg Subtype.val h)`. Use `Finset.sum_le_sum_of_subset_of_nonneg (f := fun u : PlacesOver E v => Module.finrank Fv (u.1.adicCompletion E)) (Finset.subset_univ {(⟨u, inferInstance⟩ : PlacesOver E v), ⟨w, inferInstance⟩}) (fun _ _ _ => Nat.zero_le _)` as an intermediate fact. Rewrite `this` using `[Finset.sum_pair hne', hsum]`.

Establish `key : Module.finrank Fv (u.adicCompletion E) + Module.finrank Fv (w.adicCompletion E) ≤ 2` using `this`. Rewrite `key` using `[h2]`. Establish `hpos' : 0 < Module.finrank Fv (u.adicCompletion E)` using `hpos`. Use linear arithmetic over natural numbers and integers. Take `⟨z, hz⟩` from `hloc w hns`.

Establish `hcc` using `((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hns).1`. Establish `hcj : ∀ s : Fv, cj w (ι s) = ι s`. Establish `h` using `(HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer ((GlobalTheory.ConjAtPlace.main E hU w).1.comp (continuous_completionMap v w)) (continuous_completionMap v w) (funext fun x => ?_)`. Conclude with `fun s => congrFun h s`. Simplify using `only [Function.comp_apply]`.

Rewrite using `[← hιdef, hι, hcc]`. Use `congr 1`. Conclude with `(IsCMField.complexConj E).commutes x`. Establish `hct : cj w t = -t` using `by rw [htdef, hcc, hθ, map_neg]`. Set `b` to `basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])`.

Establish `hzb : z = ι (b.repr z 0) + ι (b.repr z 1) * t` using `by conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]`. Simplify using `[b, hsm]`. Take `⟨A, C, hAC⟩ : ∃ A C : Fv, z = ι A + ι C * t` from `⟨_, _, hzb⟩`. Use `⟨A, C, ι.injective ?_⟩` and prove the remaining obligations. Rewrite using `[hι, hz, hAC, map_add, map_mul, hcj, hcj, hct, map_sub, map_mul, map_pow, map_pow, ← ht2]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sq_sub_mul_sq (hU : Unr E) (θ : E) (hθ0 : θ ≠ 0) (hθ : IsCMField.complexConj E θ = -θ)
    (d : maximalRealSubfield E) (hd : (d : E) = θ * θ) (a : maximalRealSubfield E)
    (hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
      algebraMap E (w.adicCompletion E) (a : E) = cj w z * z)
    (v : HeightOneSpectrum (𝓞 (maximalRealSubfield E))) :
    ∃ x y : v.adicCompletion (maximalRealSubfield E),
      algebraMap _ (v.adicCompletion (maximalRealSubfield E)) a =
        x ^ 2 - algebraMap _ (v.adicCompletion (maximalRealSubfield E)) d * y ^ 2 := by
  set Fv := v.adicCompletion (maximalRealSubfield E)
  haveI : CharZero Fv :=
    charZero_of_injective_algebraMap (algebraMap (maximalRealSubfield E) Fv).injective
  have hd0 : d ≠ 0 := fun h => mul_ne_zero hθ0 hθ0 (hd.symm.trans (by rw [h]; rfl))
  by_cases hsq : IsSquare (algebraMap _ Fv d)
  · exact GlobalTheory.Published.HasseNormSt.of_isSquare ((_root_.map_ne_zero _).2 hd0) hsq _
  obtain ⟨w, hw⟩ := (GlobalTheory.QNorm.places_over (maximalRealSubfield E) E).2.1 v
  haveI : w.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, HeightOneSpectrum.under_asIdeal]⟩
  set ι := completionMap v w with hιdef
  have hι : ∀ x : maximalRealSubfield E,
      ι (algebraMap _ Fv x) = algebraMap E (w.adicCompletion E) (x : E) := by
    intro x
    rw [hιdef, completionMap_algebraMap, IsScalarTower.algebraMap_apply (maximalRealSubfield E) E]
    rfl
  set t := algebraMap E (w.adicCompletion E) θ with htdef
  have ht2 : t * t = ι (algebraMap _ Fv d) := by rw [hι, hd, map_mul]
  have hnot : ∀ s : Fv, t ≠ ι s := by
    intro s hs
    apply hsq
    refine ⟨s, ι.injective ?_⟩
    rw [← ht2, map_mul, hs]
  have hsm : ∀ (s : Fv) (y : w.adicCompletion E), s • y = ι s * y := fun s y => Algebra.smul_def s y
  have hli : LinearIndependent Fv ![(1 : w.adicCompletion E), t] := by
    rw [LinearIndependent.pair_iff]
    intro s r h
    rw [hsm, hsm, mul_one] at h
    by_cases hr : r = 0
    · subst hr
      rw [map_zero, zero_mul, add_zero] at h
      exact ⟨ι.injective (by rw [h, map_zero]), rfl⟩
    · exfalso
      apply hnot (-s / r)
      have hr' : ι r ≠ 0 := (_root_.map_ne_zero ι).2 hr
      rw [map_div₀, map_neg]
      field_simp
      linear_combination h
  have hsum := sum_finrank_eq E v
  rw [Algebra.IsQuadraticExtension.finrank_eq_two] at hsum
  have hle : Module.finrank Fv (w.adicCompletion E) ≤ 2 := by
    rw [← hsum]
    exact Finset.single_le_sum (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E)) (fun _ _ => Nat.zero_le _)
      (Finset.mem_univ ⟨w, inferInstance⟩)
  haveI : Module.Finite Fv (w.adicCompletion E) := Module.finite_of_finrank_pos (finrank_pos v w)
  have hge : 2 ≤ Module.finrank Fv (w.adicCompletion E) := by
    simpa using hli.fintype_card_le_finrank
  have h2 : Module.finrank Fv (w.adicCompletion E) = 2 := le_antisymm hle hge
  have hns : ¬ IsSplitAt w := by
    rintro ⟨u, hne, hu⟩
    haveI : u.asIdeal.LiesOver v.asIdeal := ⟨by rw [← hw, ← hu, HeightOneSpectrum.under_asIdeal]⟩
    have hpos := finrank_pos v u
    have hne' : (⟨u, inferInstance⟩ : PlacesOver E v) ≠ ⟨w, inferInstance⟩ :=
      fun h => hne (congrArg Subtype.val h)
    have := Finset.sum_le_sum_of_subset_of_nonneg (f := fun u : PlacesOver E v =>
      Module.finrank Fv (u.1.adicCompletion E))
      (Finset.subset_univ {(⟨u, inferInstance⟩ : PlacesOver E v), ⟨w, inferInstance⟩})
      (fun _ _ _ => Nat.zero_le _)
    rw [Finset.sum_pair hne', hsum] at this
    have key : Module.finrank Fv (u.adicCompletion E) + Module.finrank Fv (w.adicCompletion E) ≤ 2 := this
    rw [h2] at key
    have hpos' : 0 < Module.finrank Fv (u.adicCompletion E) := hpos
    omega
  obtain ⟨z, hz⟩ := hloc w hns
  have hcc := ((GlobalTheory.ConjAtPlace.main E hU w).2.2.2.1 hns).1
  have hcj : ∀ s : Fv, cj w (ι s) = ι s := by
    have h := (HeightOneSpectrum.denseRange_algebraMap (maximalRealSubfield E) v).equalizer
      ((GlobalTheory.ConjAtPlace.main E hU w).1.comp (continuous_completionMap v w))
      (continuous_completionMap v w) (funext fun x => ?_)
    · exact fun s => congrFun h s
    · simp only [Function.comp_apply]
      rw [← hιdef, hι, hcc]
      congr 1
      exact (IsCMField.complexConj E).commutes x
  have hct : cj w t = -t := by rw [htdef, hcc, hθ, map_neg]
  let b := basisOfLinearIndependentOfCardEqFinrank hli (by simp [h2])
  have hzb : z = ι (b.repr z 0) + ι (b.repr z 1) * t := by
    conv_lhs => rw [← b.sum_repr z, Fin.sum_univ_two]
    simp [b, hsm]
  obtain ⟨A, C, hAC⟩ : ∃ A C : Fv, z = ι A + ι C * t := ⟨_, _, hzb⟩
  refine ⟨A, C, ι.injective ?_⟩
  rw [hι, hz, hAC, map_add, map_mul, hcj, hcj, hct, map_sub, map_mul, map_pow, map_pow, ← ht2]
  ring

/- English proof (translation)
Introduce `E _ _ _ hU n H hH hτ hw`. Establish `hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (H a b) = H b a` using `fun a b => by`. Use `congrFun (congrFun hH b) a` as an intermediate fact. Simplify `this` using `[cT, ReciprocityTheory.ChartRestriction.G.FD.cc]`. Establish `hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc ((1 : Matrix (Fin n) (Fin n) E) a b) = (1 : Matrix (Fin n) (Fin n) E) b a`.

Introduce `a b`. Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[ReciprocityTheory.ChartRestriction.G.FD.cc]`. Simplify using `[Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]`.

Establish `hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = Qᵀ * (1 : Matrix (Fin n) (Fin n) E).map τ * Q.map (starRingEnd ℂ)`. Introduce `τ`. Take `⟨Q, hQ, hQe⟩` from `hτ τ`. Use `⟨Q.map (starRingEnd ℂ), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[det_map']`.

Conclude with `(_root_.map_ne_zero _).2 hQ`. Establish `h1 : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Rewrite using `[hQe, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.mul_one, h1]`.

Both sides reduce to the same expression. Establish `hd : H.det ≠ 0`. Take `⟨Q, hQ, hQe⟩` from `hτ (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom`. Introduce `h0`. Establish `h1` using `congrArg Matrix.det hQe`.

Rewrite `h1` using `[det_map', h0, map_zero, Matrix.det_mul]`. Establish `h2 : (cT (starRingEnd ℂ) Q).det = starRingEnd ℂ Q.det`. Unfold `cT`. Rewrite using `[Matrix.det_transpose, det_map']`. Rewrite `h1` using `[h2]`.

Conclude with `mul_ne_zero ((_root_.map_ne_zero _).2 hQ) hQ h1.symm`. Establish `hd1 : (1 : Matrix (Fin n) (Fin n) E).det ≠ 0` using `by simp`. Choose the witnesses or unpack the hypotheses as in `⟨P, hP, hPe⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧ H = Pᵀ * 1 * P.map ReciprocityTheory.ChartRestriction.G.FD.cc := by`. Use `GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E n 1 H hG hG' hd1 hd hs ?_` and prove the remaining obligations. Establish `hm : (1 : Matrix (Fin n) (Fin n) E).det / H.det ∈ maximalRealSubfield E`.

Rewrite using `[← IsCMField.complexConj_eq_self_iff, map_div₀]`. Conclude with `congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')`. Set `a : maximalRealSubfield E` to `⟨_, hm⟩`. Take `⟨θ, h0, hθ⟩` from `GlobalTheory.Published.exists_cc_eq_neg E`. Take `⟨d, hdθ⟩` from `GlobalTheory.Published.exists_sq_real hθ`.

Establish `hd0 : d ≠ 0` using `fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))`. Establish `ha0 : a ≠ 0` using `fun h => div_ne_zero hd1 hd (congrArg Subtype.val h)`. Establish `hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E, algebraMap E (w.adicCompletion E) (a : E) = cj w z * z`. Introduce `w hns`. Take `⟨g, hg⟩` from `hw w hns`.

Establish `h1` using `congrArg Matrix.det hg`. Rewrite `h1` using `[det_map', Matrix.det_mul]`. Establish `h2 : (cT (cj w) g).det = cj w g.det`. Unfold `cT`. Rewrite using `[Matrix.det_transpose, det_map']`.

Rewrite `h1` using `[h2]`. Use `⟨g.det⁻¹, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap E (w.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E).det / H.det) = _`. Rewrite using `[Matrix.det_one, one_div, map_inv₀, h1, map_inv₀, mul_inv]`. Take `⟨x, y, hxy⟩` from `GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0 (fun ρ => by`.

Set `τ` to `ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)`. Establish `h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a` using `ComplexEmbedding.lift_algebraMap_apply E _ a`. Establish `h2 : 0 < (τ (a : E)).re` using `GlobalTheory.Published.Landherr.re_det_div_pos hd1 τ (hs τ)`. Rewrite `h2` using `[h1]`. Conclude with `⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)`.

Use the proof step `(fun v => exists_sq_sub_mul_sq hU θ h0 hθ d hdθ a hloc v)`. Use `⟨x + y * θ, ?_⟩` and prove the remaining obligations. Establish `h1` using `congrArg (Subtype.val : maximalRealSubfield E → E) hxy`. Establish `h2 : IsCMField.complexConj E θ = -θ` using `hθ`. Simplify using `[a, hdθ] at h1`.

Simplify using `only [Matrix.det_one, one_div, ReciprocityTheory.ChartRestriction.G.FD.cc, map_add, map_mul, IsCMField.complexConj_apply_eq_self, h2]`. Take the linear combination `h1`. Establish `hPc : (P.map ReciprocityTheory.ChartRestriction.G.FD.cc).det ≠ 0`. Rewrite using `[show (P.map ReciprocityTheory.ChartRestriction.G.FD.cc) = P.map (IsCMField.complexConj E).toRingEquiv.toRingHom from rfl, det_map']`. Conclude with `(_root_.map_ne_zero _).2 hP`.

Set `u : GL (Fin n) E` to `((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPc)).unit`. Use `⟨u, ?_⟩` and prove the remaining obligations. Establish `hu : (u : Matrix (Fin n) (Fin n) E) = P.map ReciprocityTheory.ChartRestriction.G.FD.cc` using `rfl`. Rewrite using `[hu, hPe, Matrix.mul_one]`. Use `congr 1`.

Use extensionality with `i j`. Simplify using `[cT, ReciprocityTheory.ChartRestriction.G.FD.cc]`.
-/
theorem main : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ (n : ℕ)
    (H : Matrix (Fin n) (Fin n) E), IsHerm (IsCMField.complexConj E).toRingEquiv.toRingHom H →
    (∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧ H.map τ = cT (starRingEnd ℂ) Q * Q) →
    (∀ w : Pl E, ¬ IsSplitAt w → ∃ g : Matrix (Fin n) (Fin n) (w.adicCompletion E),
      H.map (algebraMap E (w.adicCompletion E)) = cT (cj w) g * g) →
    ∃ h : GL (Fin n) E, H = cT (IsCMField.complexConj E).toRingEquiv.toRingHom h.val * h.val := by
  intro E _ _ _ hU n H hH hτ hw
  have hG' : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc (H a b) = H b a := fun a b => by
    have := congrFun (congrFun hH b) a
    simpa [cT, ReciprocityTheory.ChartRestriction.G.FD.cc] using this
  have hG : ∀ a b, ReciprocityTheory.ChartRestriction.G.FD.cc ((1 : Matrix (Fin n) (Fin n) E) a b) =
      (1 : Matrix (Fin n) (Fin n) E) b a := by
    intro a b
    by_cases h : a = b
    · subst h
      simp [ReciprocityTheory.ChartRestriction.G.FD.cc]
    · simp [Matrix.one_apply_ne h, Matrix.one_apply_ne (Ne.symm h), ReciprocityTheory.ChartRestriction.G.FD.cc]
  have hs : ∀ τ : E →+* ℂ, ∃ Q : Matrix (Fin n) (Fin n) ℂ, Q.det ≠ 0 ∧
      H.map τ = Qᵀ * (1 : Matrix (Fin n) (Fin n) E).map τ * Q.map (starRingEnd ℂ) := by
    intro τ
    obtain ⟨Q, hQ, hQe⟩ := hτ τ
    refine ⟨Q.map (starRingEnd ℂ), ?_, ?_⟩
    · rw [det_map']
      exact (_root_.map_ne_zero _).2 hQ
    · have h1 : (Q.map (starRingEnd ℂ)).map (starRingEnd ℂ) = Q := by
        ext i j
        simp
      rw [hQe, Matrix.map_one _ (map_zero τ) (map_one τ), Matrix.mul_one, h1]
      rfl
  have hd : H.det ≠ 0 := by
    obtain ⟨Q, hQ, hQe⟩ := hτ (IsAlgClosed.lift (M := ℂ) (R := ℚ) (S := E)).toRingHom
    intro h0
    have h1 := congrArg Matrix.det hQe
    rw [det_map', h0, map_zero, Matrix.det_mul] at h1
    have h2 : (cT (starRingEnd ℂ) Q).det = starRingEnd ℂ Q.det := by
      unfold cT
      rw [Matrix.det_transpose, det_map']
    rw [h2] at h1
    exact mul_ne_zero ((_root_.map_ne_zero _).2 hQ) hQ h1.symm
  have hd1 : (1 : Matrix (Fin n) (Fin n) E).det ≠ 0 := by simp
  obtain ⟨P, hP, hPe⟩ : ∃ P : Matrix (Fin n) (Fin n) E, P.det ≠ 0 ∧
      H = Pᵀ * 1 * P.map ReciprocityTheory.ChartRestriction.G.FD.cc := by
    refine GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt E n 1 H hG hG' hd1 hd hs ?_
    have hm : (1 : Matrix (Fin n) (Fin n) E).det / H.det ∈ maximalRealSubfield E := by
      rw [← IsCMField.complexConj_eq_self_iff, map_div₀]
      exact congrArg₂ (· / ·) (GlobalTheory.Published.cc_det_of_herm hG) (GlobalTheory.Published.cc_det_of_herm hG')
    let a : maximalRealSubfield E := ⟨_, hm⟩
    obtain ⟨θ, h0, hθ⟩ := GlobalTheory.Published.exists_cc_eq_neg E
    obtain ⟨d, hdθ⟩ := GlobalTheory.Published.exists_sq_real hθ
    have hd0 : d ≠ 0 := fun h => mul_ne_zero h0 h0 (hdθ.symm.trans (congrArg Subtype.val h))
    have ha0 : a ≠ 0 := fun h => div_ne_zero hd1 hd (congrArg Subtype.val h)
    have hloc : ∀ w : Pl E, ¬ IsSplitAt w → ∃ z : w.adicCompletion E,
        algebraMap E (w.adicCompletion E) (a : E) = cj w z * z := by
      intro w hns
      obtain ⟨g, hg⟩ := hw w hns
      have h1 := congrArg Matrix.det hg
      rw [det_map', Matrix.det_mul] at h1
      have h2 : (cT (cj w) g).det = cj w g.det := by
        unfold cT
        rw [Matrix.det_transpose, det_map']
      rw [h2] at h1
      refine ⟨g.det⁻¹, ?_⟩
      change algebraMap E (w.adicCompletion E) ((1 : Matrix (Fin n) (Fin n) E).det / H.det) = _
      rw [Matrix.det_one, one_div, map_inv₀, h1, map_inv₀, mul_inv]
    obtain ⟨x, y, hxy⟩ := GlobalTheory.QNorm.hasseNormSt (maximalRealSubfield E) d a hd0 ha0
      (fun ρ => by
        let τ := ComplexEmbedding.lift E (Complex.ofRealHom.comp ρ)
        have h1 : τ (a : E) = (Complex.ofRealHom.comp ρ) a :=
          ComplexEmbedding.lift_algebraMap_apply E _ a
        have h2 : 0 < (τ (a : E)).re := GlobalTheory.Published.Landherr.re_det_div_pos hd1 τ (hs τ)
        rw [h1] at h2
        exact ⟨√(ρ a), 0, by rw [Real.sq_sqrt (le_of_lt (by simpa using h2))]; ring⟩)
      (fun v => exists_sq_sub_mul_sq hU θ h0 hθ d hdθ a hloc v)
    refine ⟨x + y * θ, ?_⟩
    have h1 := congrArg (Subtype.val : maximalRealSubfield E → E) hxy
    have h2 : IsCMField.complexConj E θ = -θ := hθ
    simp [a, hdθ] at h1
    simp only [Matrix.det_one, one_div, ReciprocityTheory.ChartRestriction.G.FD.cc, map_add, map_mul,
      IsCMField.complexConj_apply_eq_self, h2]
    linear_combination h1
  have hPc : (P.map ReciprocityTheory.ChartRestriction.G.FD.cc).det ≠ 0 := by
    rw [show (P.map ReciprocityTheory.ChartRestriction.G.FD.cc) = P.map (IsCMField.complexConj E).toRingEquiv.toRingHom from rfl,
      det_map']
    exact (_root_.map_ne_zero _).2 hP
  let u : GL (Fin n) E := ((Matrix.isUnit_iff_isUnit_det _).2 (isUnit_iff_ne_zero.2 hPc)).unit
  refine ⟨u, ?_⟩
  have hu : (u : Matrix (Fin n) (Fin n) E) = P.map ReciprocityTheory.ChartRestriction.G.FD.cc := rfl
  rw [hu, hPe, Matrix.mul_one]
  congr 1
  ext i j
  simp [cT, ReciprocityTheory.ChartRestriction.G.FD.cc]

end GlobalTheory.LandherrStd
