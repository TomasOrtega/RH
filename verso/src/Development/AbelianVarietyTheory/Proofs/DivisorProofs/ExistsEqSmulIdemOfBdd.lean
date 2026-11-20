import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.CuspIso
import Development.AbelianVarietyTheory.Definitions.Divisors.WellChosen
import Development.AbelianVarietyTheory.Definitions.Divisors.P22
import Development.AbelianVarietyTheory.Definitions.Divisors.ToKnownTheoremsOf
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.IsLogCanonicalMultipleCanonical
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GeometricallyConnectedOfIsIsoRestrict
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.DenseInterior
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.CrysToDRBijective
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.MemSuppOnIffIdemMulOfNatural
import Development.AbelianVarietyTheory.Definitions.Foundations.ExistsFlatSecRankZero
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.IsAlgebraicOfNormConst
open CategoryTheory AlgebraicGeometry TopologicalSpace Limits NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.GeometryOfNumbersTheory Formalism.L2.Pj Formalism.BasicNotions
open ReciprocityTheory.ChartRestriction.G.Out (nonzeroLocus)
open GlobalTheory GlobalTheory.CechPic GlobalTheory.Vanishing GlobalTheory.HermTools GlobalTheory.Adelic GlobalTheory.CompHS GlobalTheory.CovTop
open GlobalTheory.AllWt (Psi wtOf cuspOn latOn normOn petOn GoodOn GoodW bergOn framesOn)
open GlobalTheory.FlagMod (FlagCover)
open GlobalTheory.FlagTan (dimFlag)
open GlobalTheory.HSApp
set_option synthInstance.maxHeartbeats 400000

noncomputable section

namespace GlobalTheory.FlatLine

open NumberField IsDedekindDomain AlgebraicGeometry CategoryTheory Limits ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.FD
  Formalism.L2.Pj GlobalTheory.AllWt

/- English proof (translation)
Assume the negation of the conclusion as `hb`. Establish `hb0 : P₀ b ≠ 0` using `fun h0 => hb ((map_eq_zero P₀).1 h0 ▸ isAlgebraic_zero)`. Establish `hpos : 0 < ‖P₀ b‖` using `norm_pos_iff.2 hb0`. Take `⟨N, hN⟩` from `exists_nat_gt (C / ‖P₀ b‖)`. Establish `hN0 : (N : K) ≠ 0`.

Establish `: (0 : ℝ) < N` using `lt_of_le_of_lt (div_nonneg (le_trans (norm_nonneg _) (h P₀)) hpos.le) hN`. Conclude with `(Nat.cast_pos.1 this).ne'` after adjusting the coercions. Establish `hi : AlgebraicIndepOn K id ({b} : Set Ω)` using `algebraicIndependent_unique_type_iff.2 hb`. Take `⟨T, hT, hbas⟩` from `exists_isTranscendenceBasis_superset hi`. Establish `hw : AlgebraicIndependent K fun i : T => P₀ i` using `hbas.1.map' P₀.injective`.

Establish `hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)` using `hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _ (by rw [Polynomial.natDegree_C_mul_X _ hN0]; exact one_ne_zero) (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hN0)`. Use `letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra`. Use `letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)).toRingHom.toAlgebra`. Use `haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1`. Use `haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2`.

Use `haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω := haveI := hbas.isAlgebraic ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω) (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by`. Take `⟨p, rfl⟩` from `hbas.1.aevalEquiv.surjective z`. Simplify using `[RingHom.algebraMap_toAlgebra]))⟩`. Set `Q : Ω →ₐ[MvPolynomial T K] ℂ` to `IsAlgClosed.lift`. Set `P : Ω →ₐ[K] ℂ` to `{ Q.toRingHom with commutes' := fun a => by`.

Use `Q.commutes (MvPolynomial.C a)` as an intermediate fact. Simplify `this }` using `[RingHom.algebraMap_toAlgebra]`. Establish `h1 : P b = (N : ℂ) * P₀ b` using `by show Q b = _`. Use `Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)` as an intermediate fact. Simplify `this` using `[RingHom.algebraMap_toAlgebra, map_natCast]`.

Establish `h2` using `h P`. Rewrite `h2` using `[h1, norm_mul, Complex.norm_natCast]`. Establish `h3 : C < N * ‖P₀ b‖` using `(div_lt_iff₀ hpos).1 hN`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem isAlgebraic_of_norm_bdd {K Ω : Type} [Field K] [CharZero K] [Field Ω] [Algebra K Ω] [Algebra K ℂ]
    (P₀ : Ω →ₐ[K] ℂ) {b : Ω} {C : ℝ} (h : ∀ P : Ω →ₐ[K] ℂ, ‖P b‖ ≤ C) : IsAlgebraic K b := by
  by_contra hb
  have hb0 : P₀ b ≠ 0 := fun h0 => hb ((map_eq_zero P₀).1 h0 ▸ isAlgebraic_zero)
  have hpos : 0 < ‖P₀ b‖ := norm_pos_iff.2 hb0
  obtain ⟨N, hN⟩ := exists_nat_gt (C / ‖P₀ b‖)
  have hN0 : (N : K) ≠ 0 := by
    have : (0 : ℝ) < N := lt_of_le_of_lt (div_nonneg (le_trans (norm_nonneg _) (h P₀)) hpos.le) hN
    exact_mod_cast (Nat.cast_pos.1 this).ne'
  have hi : AlgebraicIndepOn K id ({b} : Set Ω) := algebraicIndependent_unique_type_iff.2 hb
  obtain ⟨T, hT, hbas⟩ := exists_isTranscendenceBasis_superset hi
  have hw : AlgebraicIndependent K fun i : T => P₀ i := hbas.1.map' P₀.injective
  have hw2 : AlgebraicIndependent K fun i : T => Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X) :=
    hw.polynomial_aeval_of_transcendental fun _ => Polynomial.transcendental _
      (by rw [Polynomial.natDegree_C_mul_X _ hN0]; exact one_ne_zero)
      (by rw [Polynomial.leadingCoeff_C_mul_X]; exact mem_nonZeroDivisors_of_ne_zero hN0)
  letI : Algebra (MvPolynomial T K) Ω := (MvPolynomial.aeval fun i : T => (i : Ω)).toRingHom.toAlgebra
  letI : Algebra (MvPolynomial T K) ℂ := (MvPolynomial.aeval fun i : T =>
    Polynomial.aeval (P₀ i) (Polynomial.C (N : K) * Polynomial.X)).toRingHom.toAlgebra
  haveI : FaithfulSMul (MvPolynomial T K) Ω := (faithfulSMul_iff_algebraMap_injective _ _).2 hbas.1
  haveI : FaithfulSMul (MvPolynomial T K) ℂ := (faithfulSMul_iff_algebraMap_injective _ _).2 hw2
  haveI : Algebra.IsAlgebraic (MvPolynomial T K) Ω :=
    haveI := hbas.isAlgebraic
    ⟨fun y => (IsAlgebraic.ringHom_of_comp_eq (f := hbas.1.aevalEquiv.symm.toRingHom) (g := RingHom.id Ω)
      (Algebra.IsAlgebraic.isAlgebraic y) hbas.1.aevalEquiv.symm.injective (RingHom.ext fun z => by
        obtain ⟨p, rfl⟩ := hbas.1.aevalEquiv.surjective z
        simp [RingHom.algebraMap_toAlgebra]))⟩
  let Q : Ω →ₐ[MvPolynomial T K] ℂ := IsAlgClosed.lift
  let P : Ω →ₐ[K] ℂ := { Q.toRingHom with
    commutes' := fun a => by
      have := Q.commutes (MvPolynomial.C a)
      simpa [RingHom.algebraMap_toAlgebra] using this }
  have h1 : P b = (N : ℂ) * P₀ b := by
    show Q b = _
    have := Q.commutes (MvPolynomial.X ⟨b, hT rfl⟩)
    simpa [RingHom.algebraMap_toAlgebra, map_natCast] using this
  have h2 := h P
  rw [h1, norm_mul, Complex.norm_natCast] at h2
  have h3 : C < N * ‖P₀ b‖ := (div_lt_iff₀ hpos).1 hN
  linarith

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : ReciprocityTheory.ChartRestriction.G.Geo.Tor.Host E} {Dw : Datum H}
  {l : Level H} {Xo : Moduli Dw l} {c : Coeff l} {r : ℕ}

/- English proof (translation)
Take `⟨hL, -, h, hA⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c`. Take `⟨⟨P₀⟩, hP⟩` from `GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z`. Establish `hi` using `idem_mem_secZ Z`. Rewrite `hg`, `hi` using `[secZ_zero_eq]`. Establish `key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ ≤ C` using `fun P => by`.

Take `⟨k, x, y', t, hm, ht⟩` from `hP P`. Take `⟨w, -, hw⟩` from `GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0`. Establish `hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z` using `⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩`. Establish `h1` using `hw _ hi`. Establish `h2 : rdU U (idem Z) k x = 1`.

Simplify using `only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]`. Conclude with `evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)`. Establish `h3 : evC h Z (idem Z) = 1` using `evR_idem (liesOn_genFr h Z) (hL.test _ _)`. Rewrite `h1` using `[h2, h3, map_one, mul_one]`. Rewrite using `[← hw g hg, h1]`.

Conclude with `(congrArg norm (one_mul _)).trans_le (hb _ hz)`. Use `letI : Algebra c.F ℂ := σ.toAlgebra`. Take `⟨a, ha⟩` from `hF Z _ (isAlgebraic_of_norm_bdd (K := c.F) (b := evC h Z g) P₀ fun P => key P)`. Use `⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _ (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩` and prove the remaining obligations. Distinguish the cases in `hZ : Z' = Z`.

Substitute `hZ` using the available equality. Establish `h3 : evC h Z' (idem Z') = 1` using `evR_idem (liesOn_genFr h Z') (hL.test _ _)`. Establish `h4` using `evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z') (genFr h Z')`. Establish `h5` using `evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z') (genFr h Z')`. Rewrite using `[sub_eq_add_neg, ← neg_smul]`.

Use `h4.trans ?_` and prove the remaining obligations. Rewrite using `[h5]`. Use `show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0`. Rewrite using `[h3, ← ha, map_neg, mul_one, add_neg_cancel]`. Conclude with `evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))`.
-/
theorem exists_eq_smul_idem_of_bdd {σ : c.F →+* ℂ} (U : Unf Xo c σ r) (hσ : GoodEmb c σ) (hU : IsUnf U)
    (hF : FnAlgClosed Xo c) {Z : Comp Xo c} {g : Rul Xo c} (hg : g ∈ secZ Xo c 0) (hs : g ∈ suppOn Z) {C : ℝ}
    (hb : ∀ z ∈ framesOn U Z, ‖rdU U g z.1 z.2‖ ≤ C) : ∃ a : c.F, g = a • idem Z := by
  obtain ⟨hL, -, h, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas E H Dw l Xo c
  obtain ⟨⟨P₀⟩, hP⟩ := GlobalTheory.GenericReading.embedding_read_at_frame E H Dw l Xo c σ r U hσ hU h Z
  have hi := idem_mem_secZ Z
  rw [secZ_zero_eq] at hg hi
  have key : ∀ P : Om Z →ₐ[c.F] CAt σ, ‖toC (P (evC h Z g))‖ ≤ C := fun P => by
    obtain ⟨k, x, y', t, hm, ht⟩ := hP P
    obtain ⟨w, -, hw⟩ := GlobalTheory.CompBij.rdU_eq_of_reads U h k Z x P y' t hm ht 0 0
    have hz : (⟨k, x.1⟩ : Σ k, Frame (U.X k).Ψ r) ∈ framesOn U Z :=
      ⟨x.2, liesOn_frBor ht (liesOn_frMap hm (liesOn_genFr h Z))⟩
    have h1 := hw _ hi
    have h2 : rdU U (idem Z) k x = 1 := by
      simp only [rdU, LinearMap.coe_mk, AddHom.coe_mk, x.2, dif_pos]
      exact evR_idem (S := CAt σ) hz.2 (haveI : IsReduced (CAt σ) := inferInstanceAs (IsReduced ℂ); hL.test _ _)
    have h3 : evC h Z (idem Z) = 1 := evR_idem (liesOn_genFr h Z) (hL.test _ _)
    rw [h2, h3, map_one, mul_one] at h1
    rw [← hw g hg, h1]
    exact (congrArg norm (one_mul _)).trans_le (hb _ hz)
  letI : Algebra c.F ℂ := σ.toAlgebra
  obtain ⟨a, ha⟩ := hF Z _ (isAlgebraic_of_norm_bdd (K := c.F) (b := evC h Z g) P₀ fun P => key P)
  refine ⟨a, sub_eq_zero.1 (GlobalTheory.Reg.sec_eq_zero_of_generic_values E H Dw l Xo c hL h (hA h) 0 0 _
    (sub_mem hg (Submodule.smul_mem _ _ hi)) fun Z' => ?_)⟩
  by_cases hZ : Z' = Z
  · subst hZ
    have h3 : evC h Z' (idem Z') = 1 := evR_idem (liesOn_genFr h Z') (hL.test _ _)
    have h4 := evalAt_add (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) g ((-a) • idem Z')
      (genFr h Z')
    have h5 := evalAt_smul (K := c.F) (fun S _ _ => FrPt Xo c S) (fun φ y z => FrMap φ y z) (-a) (idem Z')
      (genFr h Z')
    rw [sub_eq_add_neg, ← neg_smul]
    refine h4.trans ?_
    rw [h5]
    show evC h Z' g + algebraMap _ _ (-a) * evC h Z' (idem Z') = 0
    rw [h3, ← ha, map_neg, mul_one, add_neg_cancel]
  · exact evC_eq_zero h hZ (sub_mem hs (Submodule.smul_mem _ _ (idem_mem_suppOn Z)))

end GlobalTheory.FlatLine

namespace GlobalTheory.CovTop

/- English proof (translation)
Introduce `_ D T j Y e o hY _ Z g h hg _ hgi _ _ hB`. Establish `hσ` using `goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom`. Take `⟨C, hC⟩` from `hB _ hσ`. Establish `hs : g ∈ GlobalTheory.AllWt.suppOn Z`. Rewrite using `[← hgi, mul_comm]`.

Conclude with `GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)`. Conclude with `GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by`. Establish `h1` using `(hC z hz).1`. Rewrite `h1` using `[GlobalTheory.FlatLine.homN_zero]`. Then use the resulting hypothesis.
-/
theorem koecher_unit_const : GlobalTheory.CovTop.Hypotheses2 → ∀ (D : D7) (T : Core D) (j : ℕ) (Y : Deep T j) (e : ℕ) (o : ℝ), Y.Good e o → 2 < Module.finrank ℚ D.host.E / 2 → ∀ (Z : Comp Y.d.Xo₂ Y.d.c₂) (g h : Rul Y.d.Xo₂ Y.d.c₂), g ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → h ∈ GlobalTheory.AllWt.secZ Y.d.Xo₂ Y.d.c₂ 0 → GlobalTheory.FlatLine.idem Z * g = g → GlobalTheory.FlatLine.idem Z * h = h → g * h = GlobalTheory.FlatLine.idem Z → (∀ σ, GoodEmb Y.d.c₂ σ → ∃ C : ℝ, ∀ z ∈ framesOn (Y.U σ) Z, GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 g z ≤ C ∧ GlobalTheory.AllWt.homN (Y.U σ) (xiR D) 0 h z ≤ C) → ∃ a : Y.d.c₂.F, g = a • GlobalTheory.FlatLine.idem Z := by
  intro _ D T j Y e o hY _ Z g h hg _ hgi _ _ hB
  have hσ := goodEmb_goodOf Y.d.c₂ Y.d.c₂.F.val.toRingHom
  obtain ⟨C, hC⟩ := hB _ hσ
  have hs : g ∈ GlobalTheory.AllWt.suppOn Z := by
    rw [← hgi, mul_comm]
    exact GlobalTheory.AllWt.mul_mem_suppOn _ (GlobalTheory.FlatLine.idem_mem_suppOn Z)
  exact GlobalTheory.FlatLine.exists_eq_smul_idem_of_bdd (Y.U _) hσ (hY.unf _ hσ) hY.geo hg hs (C := C) fun z hz => by
    have h1 := (hC z hz).1
    rwa [GlobalTheory.FlatLine.homN_zero] at h1

end GlobalTheory.CovTop
