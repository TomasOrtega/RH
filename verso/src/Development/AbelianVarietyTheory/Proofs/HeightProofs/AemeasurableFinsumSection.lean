import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.ValuationResidueLemmas
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.AlgebraMapOLInjective
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ArakelovVolumes.UpperBounds.NormOrderStatement
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.HeightTheory.SacSuccAbove
import ReciprocityTheory.SemistableReduction.AlgAll

open NumberField ReciprocityTheory.ChartRestriction.G.T0
open scoped TensorProduct

namespace GlobalTheory

namespace SectionSum

open MvPolynomial MeasureTheory

/- English proof (translation)
Establish `hfs` using `ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K Ω D N x hfg htr hJ`. Set `e : TVar D N ≃ TVar D N` to `Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange j₀).symm`. Establish `key : (ReciprocityTheory.MultiplicativeHeights.sImage (D` using `D) x) = (sImg (D := D) j₀ x) ∘ e := by`. Use function extensionality and compare the values at `p`. Take `⟨i, j⟩` from `p`.

Use `Fin.cases ?_ (fun k => ?_) j` and prove the remaining obligations. Simplify using `[e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]`. Simplify using `[e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]`. Establish `hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D` using `D) x) = Set.range (sImg (D := D) j₀ x) := by`. Rewrite using `[key, EquivLike.range_comp]`.

Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `hind : AlgebraicIndependent K (ReciprocityTheory.MultiplicativeHeights.sImage (D` using `D) x) := hfs.1`. Rewrite `hind` using `[key]`. Establish `h2` using `hind.comp _ e.symm.injective`. Establish `h3 : AlgebraicIndependent K (sImg (D` using `D) j₀ x) := by`.

Simplify `h2` using `[Function.comp_def]`. Conclude with `h3`. Establish `h2` using `hfs.2`. Rewrite `h2` using `[hrange]`. Conclude with `h2`.
-/
theorem sImg_indep_finite (K Ω : Type) [Field K] [CharZero K] [Field Ω] [Algebra K Ω] (D N : ℕ)
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (hfg : (⊤ : IntermediateField K Ω).FG)
    (htr : Algebra.trdeg K Ω = D)
    (hJ : ∃ J : Fin D → Fin N, LinearIndependent Ω fun k => KaehlerDifferential.D K Ω (x (J k))) :
    Function.Injective (sHom (K := K) (D := D) j₀ x) ∧
      FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N) := by
  have hfs := ReciprocityTheory.MultiplicativeHeights.Closed.fieldOfS K Ω D N x hfg htr hJ
  let e : TVar D N ≃ TVar D N :=
    Equiv.prodCongr (Equiv.refl _) (Fin.cycleRange j₀).symm
  have key : (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = (sImg (D := D) j₀ x) ∘ e := by
    funext p
    obtain ⟨i, j⟩ := p
    refine Fin.cases ?_ (fun k => ?_) j
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_zero]
    · simp [e, ReciprocityTheory.MultiplicativeHeights.sImage, sImg, Fin.cycleRange_symm_succ]
  have hrange : Set.range (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) = Set.range (sImg (D := D) j₀ x) := by
    rw [key, EquivLike.range_comp]
  refine ⟨?_, ?_⟩
  · have hind : AlgebraicIndependent K (ReciprocityTheory.MultiplicativeHeights.sImage (D := D) x) := hfs.1
    rw [key] at hind
    have h2 := hind.comp _ e.symm.injective
    have h3 : AlgebraicIndependent K (sImg (D := D) j₀ x) := by
      simpa [Function.comp_def] using h2
    exact h3
  · have h2 := hfs.2
    rw [hrange] at h2
    exact h2

noncomputable def liftS {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    FractionRing (MvPolynomial (TVar D N) K) →+* OmS Ω D N :=
  IsFractionRing.lift (A := MvPolynomial (TVar D N) K)
    (g := (sHom (K := K) (D := D) j₀ x).toRingHom) h

/- English proof (translation)
Rewrite using `[liftS, IsFractionRing.lift_algebraMap]`. Both sides reduce to the same expression.
-/
theorem liftS_algebraMap {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x))
    (q : MvPolynomial (TVar D N) K) :
    liftS h (algebraMap _ _ q) = sHom (K := K) (D := D) j₀ x q := by
  rw [liftS, IsFractionRing.lift_algebraMap]; rfl

/- English proof (translation)
Rewrite using `[IntermediateField.adjoin_toSubfield, liftS, IsFractionRing.lift_fieldRange]`. Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Subfield.closure_le]`. Introduce and unpack `_ ⟨p, rfl⟩`. Proceed by induction on `p using MvPolynomial.induction_on`.

Use `next a =>`. Conclude with `Subfield.subset_closure (Or.inl ⟨a, by simp [sHom]⟩)`. Use `next p q hp hq =>`. Rewrite using `[map_add]`. Conclude with `add_mem hp hq`.

Use `next p i hp =>`. Rewrite using `[map_mul]`. Conclude with `mul_mem hp (Subfield.subset_closure (Or.inr ⟨i, by simp [sHom]⟩))`. Rewrite using `[Subfield.closure_le]`. Introduce and unpack `_ (⟨a, rfl⟩ | ⟨i, rfl⟩)`.

Conclude with `Subfield.subset_closure ⟨MvPolynomial.C a, by simp [sHom]⟩`. Conclude with `Subfield.subset_closure ⟨MvPolynomial.X i, by simp [sHom]⟩`.
-/
theorem liftS_fieldRange {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x)) :
    (liftS h).fieldRange =
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))).toSubfield := by
  rw [IntermediateField.adjoin_toSubfield, liftS, IsFractionRing.lift_fieldRange]
  apply le_antisymm
  · rw [Subfield.closure_le]
    rintro _ ⟨p, rfl⟩
    induction p using MvPolynomial.induction_on
    next a =>
      exact Subfield.subset_closure (Or.inl ⟨a, by simp [sHom]⟩)
    next p q hp hq =>
      rw [map_add]
      exact add_mem hp hq
    next p i hp =>
      rw [map_mul]
      exact mul_mem hp (Subfield.subset_closure (Or.inr ⟨i, by simp [sHom]⟩))
  · rw [Subfield.closure_le]
    rintro _ (⟨a, rfl⟩ | ⟨i, rfl⟩)
    · exact Subfield.subset_closure ⟨MvPolynomial.C a, by simp [sHom]⟩
    · exact Subfield.subset_closure ⟨MvPolynomial.X i, by simp [sHom]⟩

/- English proof (translation)
Use `letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra`. Set `i : FractionRing (MvPolynomial (TVar D N) K) ≃+* (IntermediateField.adjoin K (Set.range (sImg (D` to `D) j₀ x))) := (liftS h).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (liftS_fieldRange h))`. Establish `hc : (algebraMap (IntermediateField.adjoin K (Set.range (sImg (D` using `D) j₀ x))) (OmS Ω D N)).comp i.toRingHom = (RingEquiv.refl (OmS Ω D N)).toRingHom.comp (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)) := by`. Use `RingHom.ext fun y => ?_` and prove the remaining obligations. Use `show ((i y : IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) : OmS Ω D N) = liftS h y`.

Both sides reduce to the same expression. Establish `hrk` using `Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) hc`. Apply `FiniteDimensional.of_finrank_pos` to reduce the goal to its premises. Rewrite using `[hrk]`. Conclude with `Module.finrank_pos`.
-/
theorem liftS_finite {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    {j₀ : Fin (N + 1)} {x : Fin N → Ω} (h : Function.Injective (sHom (K := K) (D := D) j₀ x))
    (hfin : FiniteDimensional (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
        (OmS Ω D N)) :
    letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra
    FiniteDimensional (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := by
  letI : Algebra (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N) := (liftS h).toAlgebra
  let i : FractionRing (MvPolynomial (TVar D N) K) ≃+*
      (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) :=
    (liftS h).rangeRestrictFieldEquiv.trans (RingEquiv.subfieldCongr (liftS_fieldRange h))
  have hc : (algebraMap (IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x)))
      (OmS Ω D N)).comp i.toRingHom =
      (RingEquiv.refl (OmS Ω D N)).toRingHom.comp
        (algebraMap (FractionRing (MvPolynomial (TVar D N) K)) (OmS Ω D N)) := by
    refine RingHom.ext fun y => ?_
    show ((i y : IntermediateField.adjoin K (Set.range (sImg (D := D) j₀ x))) : OmS Ω D N) =
      liftS h y
    rfl
  have hrk := Algebra.finrank_eq_of_equiv_equiv i (RingEquiv.refl _) hc
  apply FiniteDimensional.of_finrank_pos
  rw [hrk]
  exact Module.finrank_pos

/- English proof (translation)
Establish `hm` using `(measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => μ) 0).symm`. Establish `h1` using `hm.quasiMeasurePreserving.ae hp`. Establish `h2` using `Measure.ae_ae_of_ae_prod h1`. Use `haveI : (ae μ).NeBot := ae_neBot.2 hμ`. Take `⟨t₀, ht₀⟩` from `h2.exists`.

Use `⟨t₀, ht₀.mono fun t ht => ?_⟩` and prove the remaining obligations. Simplify `ht` using `[MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv]`.
-/
theorem exists_ae_cons {α : Type} [MeasurableSpace α] (μ : Measure α) [SigmaFinite μ] (hμ : μ ≠ 0)
    (D : ℕ) (p : (Fin (D + 1) → α) → Prop)
    (hp : ∀ᵐ t ∂(Measure.pi fun _ : Fin (D + 1) => μ), p t) :
    ∃ t₀ : α, ∀ᵐ t ∂(Measure.pi fun _ : Fin D => μ), p (Fin.cons t₀ t) := by
  have hm := (measurePreserving_piFinSuccAbove (fun _ : Fin (D + 1) => μ) 0).symm
  have h1 := hm.quasiMeasurePreserving.ae hp
  have h2 := Measure.ae_ae_of_ae_prod h1
  haveI : (ae μ).NeBot := ae_neBot.2 hμ
  obtain ⟨t₀, ht₀⟩ := h2.exists
  refine ⟨t₀, ht₀.mono fun t ht => ?_⟩
  simpa [MeasurableEquiv.piFinSuccAbove_symm_apply, Fin.insertNthEquiv] using ht

/- English proof (translation)
Establish `hC : ∀ a : Ω, algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (C a) = algebraMap Ω (OmS Ω D N) a` using `fun a => by`. Rewrite using `[← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]`. Simplify using `only [sImg, sac_self, sac_succAbove, Fin.succ_ne_zero, if_false, ↓reduceIte, map_neg, map_sum, map_mul, hC]`. Conclude with `neg_add_cancel _`.
-/
theorem sImg_rel {Ω : Type} [Field Ω] {D N : ℕ} (j₀ : Fin (N + 1)) (x : Fin N → Ω) (i : Fin D) :
    sImg (D := D) j₀ x (i.succ, j₀) +
      ∑ k, sImg (D := D) j₀ x (i.succ, j₀.succAbove k) * algebraMap Ω (OmS Ω D N) (x k) = 0 := by
  have hC : ∀ a : Ω, algebraMap (MvPolynomial (SVar D N) Ω) (OmS Ω D N) (C a) =
      algebraMap Ω (OmS Ω D N) a := fun a => by
    rw [← MvPolynomial.algebraMap_eq, ← IsScalarTower.algebraMap_apply]
  simp only [sImg, sac_self, sac_succAbove, Fin.succ_ne_zero, if_false,
    ↓reduceIte, map_neg, map_sum, map_mul, hC]
  exact neg_add_cancel _

/- English proof (translation)
Establish `hX : ∀ P : OmS Ω D N →+* ℂ, (∀ p : MvPolynomial (TVar D N) K, P (sHom (K` using `K) j₀ x p) = eval₂ sg pt p) → ∀ p, P (sImg j₀ x p) = pt p := fun P hP p => by`. Simplify `hP (X p)` using `[sHom]`. Establish `hmaps : Set.MapsTo (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N))) {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K` using `K) j₀ x p) = eval₂ sg pt p} {Q | Q ∈ PT (Ω := Ω) sg ∧ ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by`. Introduce `P hP`. Use `⟨?_, fun i => ?_⟩` and prove the remaining obligations.

Use extensionality with `a`. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[← IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)]`. Use `hP (C a)` as an intermediate fact. Rewrite using `[show sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a by` and apply the resulting hypothesis.

Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `(sHom (K := K) (D := D) j₀ x).commutes a,`. Use the proof step `eval₂_C] at this`. Use `congrArg P (sImg_rel (D := D) j₀ x i)` as an intermediate fact. Simplify `this` using `[map_sum, map_mul, hX P hP]`.

Use `⟨hmaps, ?_, ?_⟩` and prove the remaining obligations. Introduce `P₁ h₁ P₂ h₂ he`. Establish `hm` using `hmaps h₁`. Use `(hext _ hm.1 hm.2).unique ⟨fun a => rfl, hX _ h₁⟩ ⟨fun a => ?_, hX _ h₂⟩` and prove the remaining obligations. Conclude with `(DFunLike.congr_fun he a).symm`.

Introduce and unpack `Q ⟨hQ, hrel⟩`. Take `⟨P, ⟨hP1, hP2⟩, -⟩` from `hext Q hQ hrel`. Use `⟨P, fun p => ?_, RingHom.ext hP1⟩` and prove the remaining obligations. Establish `: P.comp (sHom (K` using `K) (D := D) j₀ x).toRingHom = eval₂Hom sg pt := by`. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `a`. Establish `h1 : sHom (K` using `K) (D := D) j₀ x (C a) = algebraMap K _ a := by`. Rewrite using `[← MvPolynomial.algebraMap_eq]`. Conclude with `(sHom (K := K) (D := D) j₀ x).commutes a`. Simplify using `only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1, coe_eval₂Hom, eval₂_C]`.

Rewrite using `[IsScalarTower.algebraMap_apply K Ω (OmS Ω D N), hP1]`. Conclude with `DFunLike.congr_fun hQ a`. Introduce `q`. Simplify using `[sHom, hP2]`. Conclude with `DFunLike.congr_fun this p`.
-/
theorem bijOn_restrict {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D N : ℕ}
    (j₀ : Fin (N + 1)) (x : Fin N → Ω) (sg : K →+* ℂ) (pt : TVar D N → ℂ)
    (hext : ∀ Q : Ω →+* ℂ, Q ∈ PT (Ω := Ω) sg →
      (∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0) →
      ∃! P : OmS Ω D N →+* ℂ, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = Q a) ∧
        ∀ p, P (sImg j₀ x p) = pt p) :
    Set.BijOn (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
  have hX : ∀ P : OmS Ω D N →+* ℂ,
      (∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p) →
      ∀ p, P (sImg j₀ x p) = pt p := fun P hP p => by
    simpa [sHom] using hP (X p)
  have hmaps : Set.MapsTo (fun P : OmS Ω D N →+* ℂ => P.comp (algebraMap Ω (OmS Ω D N)))
      {P | ∀ p : MvPolynomial (TVar D N) K, P (sHom (K := K) j₀ x p) = eval₂ sg pt p}
      {Q | Q ∈ PT (Ω := Ω) sg ∧
        ∀ i : Fin D, pt (i.succ, j₀) + ∑ k, pt (i.succ, j₀.succAbove k) * Q (x k) = 0} := by
    intro P hP
    refine ⟨?_, fun i => ?_⟩
    · ext a
      simp only [RingHom.comp_apply]
      rw [← IsScalarTower.algebraMap_apply K Ω (OmS Ω D N)]
      have := hP (C a)
      rwa [show sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a by
        rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a,
        eval₂_C] at this
    · have := congrArg P (sImg_rel (D := D) j₀ x i)
      simpa [map_sum, map_mul, hX P hP] using this
  refine ⟨hmaps, ?_, ?_⟩
  · intro P₁ h₁ P₂ h₂ he
    have hm := hmaps h₁
    refine (hext _ hm.1 hm.2).unique ⟨fun a => rfl, hX _ h₁⟩ ⟨fun a => ?_, hX _ h₂⟩
    exact (DFunLike.congr_fun he a).symm
  · rintro Q ⟨hQ, hrel⟩
    obtain ⟨P, ⟨hP1, hP2⟩, -⟩ := hext Q hQ hrel
    refine ⟨P, fun p => ?_, RingHom.ext hP1⟩
    have : P.comp (sHom (K := K) (D := D) j₀ x).toRingHom = eval₂Hom sg pt := by
      apply MvPolynomial.ringHom_ext
      · intro a
        have h1 : sHom (K := K) (D := D) j₀ x (C a) = algebraMap K _ a := by
          rw [← MvPolynomial.algebraMap_eq]; exact (sHom (K := K) (D := D) j₀ x).commutes a
        simp only [RingHom.comp_apply, AlgHom.toRingHom_eq_coe, AlgHom.coe_toRingHom, h1,
          coe_eval₂Hom, eval₂_C]
        rw [IsScalarTower.algebraMap_apply K Ω (OmS Ω D N), hP1]
        exact DFunLike.congr_fun hQ a
      · intro q
        simp [sHom, hP2]
    exact DFunLike.congr_fun this p

end SectionSum

open SectionSum MeasureTheory in

/- English proof (translation)
Introduce `hgen hfib hext K _ _ ι _ Ω _ _ WT _ A _ _ _ _ 𝒜 d c hfg htr hw hJ sg m a Nf h hNf hh`. Take `⟨hinj, hfin⟩` from `sImg_indep_finite K (Ω c) d.D d.N (d.jc c) (d.x c) hfg htr hJ`. Use `letI : Algebra (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N) := (liftS hinj).toAlgebra`. Use `haveI := liftS_finite hinj hfin`. Take `⟨Φ, hΦm, hΦ⟩` from `hfib K (TVar d.D d.N) (OmS (Ω c) d.D d.N) sg m (fun i => algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a i)) Nf hNf`.

Use `haveI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm`. Take `⟨t₀, ht₀⟩` from `exists_ae_cons _ (Measure.toSphere_ne_zero _) d.D _ (hgen K sg (d.D + 1) d.N)`. Set `F : (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) → TVar d.D d.N → ℂ` to `fun t q => ((Fin.cons t₀ t : Fin (d.D + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) q.1 : EuclideanSpace ℂ (Fin (d.N + 1))) q.2`. Establish `hF : Measurable F`. Use `measurable_pi_lambda _ fun q => ?_` and prove the remaining obligations.

Take `⟨i, j⟩` from `q`. Use `Fin.cases ?_ (fun k => ?_) i` and prove the remaining obligations. Simplify using `only [F, Fin.cons_zero]`. Conclude with `measurable_const`. Simplify using `only [F, Fin.cons_succ]`.

Apply `Continuous.measurable` to reduce the goal to its premises. Use `fun_prop`. Use `⟨fun t => Φ (F t), hΦm.comp hF, ?_⟩` and prove the remaining obligations. Use `ht₀.mono fun t ht => ?_` and prove the remaining obligations. Establish `hb` using `bijOn_restrict (K := K) (d.jc c) (d.x c) sg (F t) (fun Q hQ hrel => by`.

Use `letI : Algebra K ℂ := sg.toAlgebra`. Set `φ : Ω c →ₐ[K] ℂ` to `{ Q with commutes' := fun r => DFunLike.congr_fun hQ r }`. Use `hext K (Ω c) ℂ d.D d.N (d.jc c) (d.x c) (F t) φ htr ?_ hrel` and prove the remaining obligations. Rewrite using `[algebraicIndependent_iff]`. Introduce `p hp`.

Assume the negation of the conclusion as `h0`. Conclude with `ht p h0 hp)`. Establish `hST : d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j) = {Q | Q ∈ PT (Ω` using `Ω c) sg ∧ ∀ i : Fin d.D, F t (i.succ, d.jc c) + ∑ k, F t (i.succ, (d.jc c).succAbove k) * Q (d.x c k) = 0} := by`. Use extensionality with `Q`. Simplify using `only [Data.ST, Set.mem_setOf_eq, F, Fin.cons_succ]`.

Use `and_congr_right fun _ => forall_congr' fun i => ?_` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_succAbove _ (d.jc c), ratio_self hw, map_one, mul_one]`. Both sides reduce to the same expression. Use `show _ = Φ (F t)`. Use `beta_reduce`.

Rewrite using `[hΦ (F t) ht, hST]`. Use `symm`. Establish `hset : {P : OmS (Ω c) d.D d.N →+* ℂ | ∀ p : MvPolynomial (TVar d.D d.N) K, P (algebraMap (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N) (algebraMap (MvPolynomial (TVar d.D d.N) K) (FractionRing (MvPolynomial (TVar d.D d.N) K)) p)) = MvPolynomial.eval₂ sg (F t) …` using `K) (d.jc c) (d.x c) p) = MvPolynomial.eval₂ sg (F t) p} := by`. Use extensionality with `P`. Use `forall_congr' fun p => ?_` and prove the remaining obligations.

Rewrite using `[← liftS_algebraMap hinj p]`. Both sides reduce to the same expression. Rewrite using `[hset]`. Use `finsum_mem_eq_of_bijOn _ hb fun P hP => ?_` and prove the remaining obligations. Rewrite using `[hh _ (hb.mapsTo hP).1]`.

Both sides reduce to the same expression.
-/
theorem aemeasurable_finsum_section :
    (∀ (K : Type) [Field K] [Countable K] (sg : K →+* ℂ) (D N : ℕ), ∀ᵐ t ∂(MeasureTheory.Measure.pi fun _ : Fin D => (MeasureTheory.volume : MeasureTheory.Measure (EuclideanSpace ℂ (Fin (N + 1)))).toSphere), ∀ p : MvPolynomial (Fin D × Fin (N + 1)) K, p ≠ 0 → MvPolynomial.eval₂ sg (fun q => (t q.1 : EuclideanSpace ℂ (Fin (N + 1))) q.2) p ≠ 0) → (∀ (K : Type) [Field K] [CharZero K] (σ : Type) [Fintype σ] (L : Type) [Field L] [Algebra (FractionRing (MvPolynomial σ K)) L] [FiniteDimensional (FractionRing (MvPolynomial σ K)) L] (sg : K →+* ℂ) (m : ℕ) (b : Fin m → L) (Nf : (Fin m → ℂ) → ℝ), Measurable Nf → ∃ Φ : (σ → ℂ) → ℝ, Measurable Φ ∧ ∀ t : σ → ℂ, (∀ p : MvPolynomial σ K, p ≠ 0 → MvPolynomial.eval₂ sg t p ≠ 0) → Φ t = ∑ᶠ P ∈ {P : L →+* ℂ | ∀ p : MvPolynomial σ K, P (algebraMap (FractionRing (MvPolynomial σ K)) L (algebraMap (MvPolynomial σ K) (FractionRing (MvPolynomial σ K)) p)) = MvPolynomial.eval₂ sg t p}, Nf (fun i => P (b i))) → (∀ (K Ω L : Type) [Field K] [Field Ω] [Algebra K Ω] [Field L] [Algebra K L] (D N : ℕ) (j₀ : Fin (N + 1)) (x : Fin N → Ω) (τ : TVar D N → L) (φ : Ω →ₐ[K] L), Algebra.trdeg K Ω = D → AlgebraicIndependent K τ → (∀ i : Fin D, τ (i.succ, j₀) + ∑ k, τ (i.succ, j₀.succAbove k) * φ (x k) = 0) → ∃! P : OmS Ω D N →+* L, (∀ a : Ω, P (algebraMap Ω (OmS Ω D N) a) = φ a) ∧ ∀ p, P (sImg j₀ x p) = τ p) → ∀ (K : Type) [Field K] [NumberField K] (ι : Type) [Fintype ι] (Ω : ι → Type) [∀ c, Field (Ω c)] [∀ c, Algebra K (Ω c)] (WT : Type) [AddCommGroup WT] (A : ι → Type) [∀ c, CommRing (A c)] [∀ c, Algebra (Ω c) (A c)] [∀ c, Algebra K (A c)] [∀ c, Algebra (𝓞 K) (A c)] (𝒜 : (c : ι) → WT → Submodule (Ω c) (A c)) (d : Data K ι Ω WT A), ∀ c : ι, (⊤ : IntermediateField K (Ω c)).FG → Algebra.trdeg K (Ω c) = d.D → d.w (d.jc c) c ≠ 0 → (∃ J : Fin d.D → Fin d.N, LinearIndependent (Ω c) fun k => KaehlerDifferential.D K (Ω c) (d.x c (J k))) → ∀ (sg : K →+* ℂ) (m : ℕ) (a : Fin m → Ω c) (Nf : (Fin m → ℂ) → ℝ) (h : (Ω c →+* ℂ) → ℝ), Measurable Nf → (∀ P ∈ PT (Ω := Ω c) sg, h P = Nf (fun i => P (a i))) → AEMeasurable (fun t : Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1 => ∑ᶠ P ∈ d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j), h P) d.sphMeasure := by
  intro hgen hfib hext K _ _ ι _ Ω _ _ WT _ A _ _ _ _ 𝒜 d c hfg htr hw hJ sg m a Nf h hNf hh
  obtain ⟨hinj, hfin⟩ := sImg_indep_finite K (Ω c) d.D d.N (d.jc c) (d.x c) hfg htr hJ
  letI : Algebra (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N) :=
    (liftS hinj).toAlgebra
  haveI := liftS_finite hinj hfin
  obtain ⟨Φ, hΦm, hΦ⟩ := hfib K (TVar d.D d.N) (OmS (Ω c) d.D d.N) sg m
    (fun i => algebraMap (Ω c) (OmS (Ω c) d.D d.N) (a i)) Nf hNf
  haveI : Countable K := Countable.of_equiv _ (Module.finBasis ℚ K).equivFun.toEquiv.symm
  obtain ⟨t₀, ht₀⟩ := exists_ae_cons _ (Measure.toSphere_ne_zero _) d.D _
    (hgen K sg (d.D + 1) d.N)
  let F : (Fin d.D → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) →
      TVar d.D d.N → ℂ := fun t q =>
    ((Fin.cons t₀ t : Fin (d.D + 1) → Metric.sphere (0 : EuclideanSpace ℂ (Fin (d.N + 1))) 1) q.1 :
      EuclideanSpace ℂ (Fin (d.N + 1))) q.2
  have hF : Measurable F := by
    refine measurable_pi_lambda _ fun q => ?_
    obtain ⟨i, j⟩ := q
    refine Fin.cases ?_ (fun k => ?_) i
    · simp only [F, Fin.cons_zero]
      exact measurable_const
    · simp only [F, Fin.cons_succ]
      apply Continuous.measurable
      fun_prop
  refine ⟨fun t => Φ (F t), hΦm.comp hF, ?_⟩
  refine ht₀.mono fun t ht => ?_
  have hb := bijOn_restrict (K := K) (d.jc c) (d.x c) sg (F t) (fun Q hQ hrel => by
    letI : Algebra K ℂ := sg.toAlgebra
    let φ : Ω c →ₐ[K] ℂ := { Q with commutes' := fun r => DFunLike.congr_fun hQ r }
    refine hext K (Ω c) ℂ d.D d.N (d.jc c) (d.x c) (F t) φ htr ?_ hrel
    rw [algebraicIndependent_iff]
    intro p hp
    by_contra h0
    exact ht p h0 hp)
  have hST : d.ST c sg (fun i j => (t i : EuclideanSpace ℂ (Fin (d.N + 1))) j) =
      {Q | Q ∈ PT (Ω := Ω c) sg ∧ ∀ i : Fin d.D, F t (i.succ, d.jc c) +
        ∑ k, F t (i.succ, (d.jc c).succAbove k) * Q (d.x c k) = 0} := by
    ext Q
    simp only [Data.ST, Set.mem_setOf_eq, F, Fin.cons_succ]
    refine and_congr_right fun _ => forall_congr' fun i => ?_
    rw [Fin.sum_univ_succAbove _ (d.jc c), ratio_self hw, map_one, mul_one]
    rfl
  show _ = Φ (F t)
  beta_reduce
  rw [hΦ (F t) ht, hST]
  symm
  have hset : {P : OmS (Ω c) d.D d.N →+* ℂ | ∀ p : MvPolynomial (TVar d.D d.N) K,
      P (algebraMap (FractionRing (MvPolynomial (TVar d.D d.N) K)) (OmS (Ω c) d.D d.N)
        (algebraMap (MvPolynomial (TVar d.D d.N) K) (FractionRing (MvPolynomial (TVar d.D d.N) K)) p))
        = MvPolynomial.eval₂ sg (F t) p} =
      {P | ∀ p : MvPolynomial (TVar d.D d.N) K,
        P (sHom (K := K) (d.jc c) (d.x c) p) = MvPolynomial.eval₂ sg (F t) p} := by
    ext P
    refine forall_congr' fun p => ?_
    rw [← liftS_algebraMap hinj p]
    rfl
  rw [hset]
  refine finsum_mem_eq_of_bijOn _ hb fun P hP => ?_
  rw [hh _ (hb.mapsTo hP).1]
  rfl

end GlobalTheory
