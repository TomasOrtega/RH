import Mathlib
import Formalism.SharpRestriction.GlobalSchurBounds.ThickPlacesCorollaryOfAnyTranslate
import Development.AbelianVarietyTheory.BlockTheory.GlobalSignature.MassFormulaPositivity
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsLocalConjugationSelfDualLatticesHost
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.FiniteNotIsUnitOneAddSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.HasseNormTheoremQuadraticExtension
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsCongrIffTraceFormsIsometricCm

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions.StandardLattice
open scoped Matrix

namespace GlobalTheory.DefiniteMass
open ReciprocityTheory.ChartRestriction.G.FD GlobalTheory.SelfDualGenus GlobalTheory.LocalConjugacy

/- English proof (translation)
Establish `he` using `(Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hh hst).1`. Establish `hg : Formalism.HermitianLatticesTheory.genus h L = Formalism.HermitianLatticesTheory.genus h M` using `Set.ext fun N => and_congr_right fun _ => ⟨he.trans (he.symm hLM), he.trans hLM⟩`. Establish `hc : Formalism.ThetaLiftIndependence.IsClassReps h L = Formalism.ThetaLiftIndependence.IsClassReps h M`. Use function extensionality and compare the values at `s`. Unfold `Formalism.ThetaLiftIndependence.IsClassReps`.

Rewrite using `[hg]`. Unfold `Formalism.HermitianLatticesTheory.mass`. Rewrite using `[hc]`.
-/
theorem mass_eq_of_sameGenus {K V : Type} [Field K] [NumberField K] [StarRing K] [AddCommGroup V] [Module K V]
    [Module (𝓞 K) V] [IsScalarTower (𝓞 K) K V] (h : V →ₗ⋆[K] V →ₗ[K] K) (hh : h.IsSymm)
    (hst : ∀ r : 𝓞 K, star (algebraMap (𝓞 K) K r) ∈ Set.range (algebraMap (𝓞 K) K))
    {L M : Submodule (𝓞 K) V} (hLM : Formalism.HermitianLatticesTheory.SameGenus h L M) :
    Formalism.HermitianLatticesTheory.mass h L = Formalism.HermitianLatticesTheory.mass h M := by
  have he := (Formalism.HermitianLatticesTheory.final_genusBasic (𝓞 K) K V h hh hst).1
  have hg : Formalism.HermitianLatticesTheory.genus h L = Formalism.HermitianLatticesTheory.genus h M :=
    Set.ext fun N => and_congr_right fun _ => ⟨he.trans (he.symm hLM), he.trans hLM⟩
  have hc : Formalism.ThetaLiftIndependence.IsClassReps h L = Formalism.ThetaLiftIndependence.IsClassReps h M := by
    funext s
    unfold Formalism.ThetaLiftIndependence.IsClassReps
    rw [hg]
  unfold Formalism.HermitianLatticesTheory.mass
  rw [hc]

section
variable {E : Type} [Field E] [NumberField E] [IsCMField E]
attribute [local instance] IsCMField.starRing

/- English proof (translation)
The claim follows from `Formalism.L2.Pj.unramBridge_holds E fun P hP => by obtain ⟨θ, t, e1, e2⟩ := hc.2.2 P hP refine ⟨θ, ?_⟩ have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t := RingOfIntegers.ext e1.symm rwa [this]`.
-/
theorem unramified_of_isCMUnram (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) :
    Algebra.Unramified (𝓞 (maximalRealSubfield E)) (𝓞 E) :=
  Formalism.L2.Pj.unramBridge_holds E fun P hP => by
    obtain ⟨θ, t, e1, e2⟩ := hc.2.2 P hP
    refine ⟨θ, ?_⟩
    have : RingOfIntegers.mapRingEquiv (IsCMField.complexConj E : E ≃+* E) θ = t :=
      RingOfIntegers.ext e1.symm
    rwa [this]

/- English proof (translation)
Use `haveI := unramified_of_isCMUnram hc`. Establish `hG : ∀ a b, cc (W.gramᵀ a b) = W.gramᵀ b a` using `fun a b => W.herm.eq (W.frame b) (W.frame a)`. Establish `hd : W.gramᵀ.det ≠ 0`. Rewrite using `[Matrix.det_transpose]`. Conclude with `(GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero`.

Take `⟨P, hP0, hP⟩` from `congr_signMatrix (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt) GlobalTheory.QNorm.hasseNormSt hG hd (isLattice_coordLat W W.L0 W.standardTuple_isLattice) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular) Set.univ (fun _ => Or.inl trivial) W.r …`. Establish `h0` using `hs τ`. Rewrite `h0` using `[hp τ]`. Take `⟨e, Q, hQ⟩` from `h0`. Establish `hJ : Formalism.UG.Jpq W.rank 0 = 1`.

Use extensionality with `i j`. Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[Formalism.UG.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`.

Conclude with `i.elim0`. Rewrite `hQ` using `[hJ]`. Use `⟨Q.1.submatrix e e, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.det_submatrix_equiv_self]`. Conclude with `(Matrix.isUnit_iff_isUnit_det _ |>.1 Q.isUnit).ne_zero`.

Establish `h1` using `congrArg (fun M => (Matrix.submatrix M e e)ᵀ) hQ`. Simplify using `only [Matrix.submatrix_one_equiv, Matrix.transpose_one] at h1`. Rewrite `h1` using `[← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e, Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc]`. Rewrite using `[Published.gram_eq]`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use `congr 2`. Use extensionality with `i j`. Simplify using the standard rewrite rules. Use extensionality with `i j`. Simplify using `[Matrix.diagonal_apply, Matrix.one_apply, sgn]`.

Establish `h1 : signMatrix E W.rank W.rank = 1`. Use extensionality with `i j`. Simplify using `[signMatrix, Matrix.diagonal_apply, Matrix.one_apply]`. Rewrite `hP` using `[h1, Matrix.mul_one]`. Use `⟨W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit)), fun x y => ?_⟩` and prove the remaining obligations.

Rewrite using `[← herm_coord, hP]`. Express the relevant statement in the definitionally equal form `∑ i, cc ((P *ᵥ W.frame.equivFun x) i) * (P *ᵥ W.frame.equivFun y) i = _`. Generalize the expression as in `W.frame.equivFun x = u`. Generalize the expression as in `W.frame.equivFun y = v`. Simplify using `only [herm, cc, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply, Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`. Conclude with `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring`.
-/
theorem exists_isometry (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    ∃ e : W.V ≃ₗ[E] (Fin W.rank → E), ∀ x y, stdForm E W.rank (e x) (e y) = W.hT x y := by
  haveI := unramified_of_isCMUnram hc
  have hG : ∀ a b, cc (W.gramᵀ a b) = W.gramᵀ b a := fun a b => W.herm.eq (W.frame b) (W.frame a)
  have hd : W.gramᵀ.det ≠ 0 := by
    rw [Matrix.det_transpose]; exact (GlobalTheory.IndefiniteRowSideFullHecke.AdelicUnitaryGroups.gram_det_isUnit W).ne_zero
  obtain ⟨P, hP0, hP⟩ := congr_signMatrix (GlobalTheory.LocalQuad.landherr_of_hasseNormSt GlobalTheory.QNorm.hasseNormSt)
    GlobalTheory.QNorm.hasseNormSt hG hd (isLattice_coordLat W W.L0 W.standardTuple_isLattice) (selfDual_coordLat W W.L0 W.baseLattice_isUnimodular)
    Set.univ (fun _ => Or.inl trivial) W.rank fun τ _ => by
      have h0 := hs τ
      rw [hp τ] at h0
      obtain ⟨e, Q, hQ⟩ := h0
      have hJ : Formalism.UG.Jpq W.rank 0 = 1 := by
        ext i j
        rcases i with i | i
        · rcases j with j | j
          · simp [Formalism.UG.Jpq, Matrix.one_apply]
          · exact j.elim0
        · exact i.elim0
      rw [hJ] at hQ
      refine ⟨Q.1.submatrix e e, ?_, ?_⟩
      · rw [Matrix.det_submatrix_equiv_self]
        exact (Matrix.isUnit_iff_isUnit_det _ |>.1 Q.isUnit).ne_zero
      · have h1 := congrArg (fun M => (Matrix.submatrix M e e)ᵀ) hQ
        simp only [Matrix.submatrix_one_equiv, Matrix.transpose_one] at h1
        rw [← Matrix.submatrix_mul_equiv _ _ e e e, ← Matrix.submatrix_mul_equiv _ _ e e e,
          Matrix.transpose_mul, Matrix.transpose_mul, ← Matrix.mul_assoc] at h1
        rw [Published.gram_eq]
        convert h1 using 1
        · congr 2
          ext i j
          simp
        · ext i j
          simp [Matrix.diagonal_apply, Matrix.one_apply, sgn]
  have h1 : signMatrix E W.rank W.rank = 1 := by
    ext i j
    simp [signMatrix, Matrix.diagonal_apply, Matrix.one_apply]
  rw [h1, Matrix.mul_one] at hP
  refine ⟨W.frame.equivFun.trans (Matrix.toLinearEquiv' P (Matrix.invertibleOfIsUnitDet P hP0.isUnit)), fun x y => ?_⟩
  rw [← herm_coord, hP]
  change ∑ i, cc ((P *ᵥ W.frame.equivFun x) i) * (P *ᵥ W.frame.equivFun y) i = _
  generalize W.frame.equivFun x = u
  generalize W.frame.equivFun y = v
  simp only [herm, cc, Matrix.mul_apply, Matrix.mulVec, dotProduct, map_sum, map_mul, Matrix.transpose_apply,
    Matrix.map_apply, Finset.mul_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Finset.sum_comm]
  exact Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring

/- English proof (translation)
Use `le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨j, rfl⟩`. Conclude with `GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod j`. Use `choose a ha using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hx`. Rewrite using `[pi_eq_sum_univ' x]`.

Use `Submodule.sum_mem _ fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← ha j]`. Conclude with `Submodule.smul_mem _ (a j) (Submodule.subset_span ⟨j, rfl⟩)`.
-/
theorem stdLat_eq (n : ℕ) : stdLat E n = GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdMod E n := by
  refine le_antisymm (Submodule.span_le.2 ?_) fun x hx => ?_
  · rintro _ ⟨j, rfl⟩
    exact GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.single_mem_stdMod j
  · choose a ha using GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.mem_stdMod.1 hx
    rw [pi_eq_sum_univ' x]
    refine Submodule.sum_mem _ fun j _ => ?_
    rw [← ha j]
    exact Submodule.smul_mem _ (a j) (Submodule.subset_span ⟨j, rfl⟩)

/- English proof (translation)
Simplify using `[Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_one]`.
-/
theorem mem_dual_iff {V : Type} [AddCommGroup V] [Module E V] [Module (𝓞 E) V] [IsScalarTower (𝓞 E) E V]
    (h : V →ₗ⋆[E] V →ₗ[E] E) (L : Submodule (𝓞 E) V) (x : V) :
    x ∈ Formalism.HermitianLatticesTheory.dual h L ↔ ∀ y ∈ L, ∃ a : 𝓞 E, (a : E) = h y x := by
  simp [Formalism.HermitianLatticesTheory.dual, Formalism.E.hdual, Submodule.mem_one]

/- English proof (translation)
Introduce and unpack `x ⟨s, hs, hx⟩`. Take `⟨k, hk, hkx⟩` from `h _ hx`. Establish `hkP : (k : 𝓞 E) ∉ P` using `fun hkP => by`. Take `⟨a, b, hab⟩` from `((Nat.Prime.coprime_iff_not_dvd hp).2 hk).cast (R := 𝓞 E)`. Conclude with `hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (P.mul_mem_left a hpP) (P.mul_mem_left b hkP)))`.

Establish `hc : (k : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K` using `E) P := by`. Use `Submonoid.subset_closure ⟨hkP, fun t ht => ?_⟩` and prove the remaining obligations. Establish `: t = (k : 𝓞 E)` using `RingOfIntegers.coe_injective (by rw [ht, map_natCast, star_natCast])`. Rewrite using `[this]` and apply the resulting hypothesis. Conclude with `⟨_, mul_mem hc hs, by rwa [mul_smul, Nat.cast_smul_eq_nsmul]⟩`.
-/
theorem loc_le_of_nsmul {V : Type} [AddCommGroup V] [Module (𝓞 E) V] {p : ℕ} (hp : p.Prime)
    {P : Ideal (𝓞 E)} (hP : P.IsMaximal) (hpP : (p : 𝓞 E) ∈ P) {L M : Submodule (𝓞 E) V}
    (h : ∀ x ∈ L, ∃ k : ℕ, ¬ p ∣ k ∧ k • x ∈ M) :
    Formalism.HermitianLatticesTheory.loc (K := E) P L ≤ Formalism.HermitianLatticesTheory.loc (K := E) P M := by
  rintro x ⟨s, hs, hx⟩
  obtain ⟨k, hk, hkx⟩ := h _ hx
  have hkP : (k : 𝓞 E) ∉ P := fun hkP => by
    obtain ⟨a, b, hab⟩ := ((Nat.Prime.coprime_iff_not_dvd hp).2 hk).cast (R := 𝓞 E)
    exact hP.ne_top ((Ideal.eq_top_iff_one _).2 (hab ▸ add_mem (P.mul_mem_left a hpP) (P.mul_mem_left b hkP)))
  have hc : (k : 𝓞 E) ∈ Formalism.HermitianLatticesTheory.hcompl (K := E) P := by
    refine Submonoid.subset_closure ⟨hkP, fun t ht => ?_⟩
    have : t = (k : 𝓞 E) := RingOfIntegers.coe_injective (by rw [ht, map_natCast, star_natCast])
    rwa [this]
  exact ⟨_, mul_mem hc hs, by rwa [mul_smul, Nat.cast_smul_eq_nsmul]⟩

/- English proof (translation)
Use `haveI := unramified_of_isCMUnram hc`. Establish `hf : ∀ x y : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y = stdForm E n y x` using `fun x y => Finset.sum_congr rfl fun i _ => mul_comm _ _`. Establish `hgen` using `GlobalTheory.GenusSelfDual.inGenus_of_selfDual (Λ := ⟨L, hL.fg, hL.span_eq_top⟩) fun x => by`. Simplify `hsd x` using `only [hf]`. Introduce `P hP`.

Use `haveI : P.IsPrime := hP.isPrime`. Take `⟨p, hp, hpP⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P` from `by haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E))`. Take `⟨p, hp⟩` from `CharP.exists (𝓞 E ⧸ P)`. Use `⟨p, (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right (CharP.char_ne_zero_of_finite (𝓞 E ⧸ P) p), ?_⟩` and prove the remaining obligations. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]`.

Take `⟨γ, hγ, h1, h2⟩` from `hgen p hp`. Use `⟨γ, fun x y => by rw [← hf, ← hf]; exact hγ y x, ?_⟩` and prove the remaining obligations. Rewrite using `[gmap_eq_tMap, tMap_loc, stdLat_eq]`. Conclude with `le_antisymm (loc_le_of_nsmul hp hP hpP h2) (loc_le_of_nsmul hp hP hpP h1)`.
-/
theorem sameGenus_stdLat (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) {n : ℕ} (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.IsLattice E L) (hsd : ∀ x, x ∈ L ↔ ∀ y ∈ L, ∃ a : 𝓞 E, (a : E) = stdForm E n y x) :
    Formalism.HermitianLatticesTheory.SameGenus (stdForm E n) (stdLat E n) L := by
  haveI := unramified_of_isCMUnram hc
  have hf : ∀ x y : Fin n → E, GlobalTheory.IndefiniteRowSideFullHecke.AdmissibleHarmonicLattice.stdForm x y = stdForm E n y x := fun x y =>
    Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hgen := GlobalTheory.GenusSelfDual.inGenus_of_selfDual (Λ := ⟨L, hL.fg, hL.span_eq_top⟩) fun x => by
    simpa only [hf] using hsd x
  intro P hP
  haveI : P.IsPrime := hP.isPrime
  obtain ⟨p, hp, hpP⟩ : ∃ p : ℕ, p.Prime ∧ (p : 𝓞 E) ∈ P := by
    haveI : Finite (𝓞 E ⧸ P) := Ideal.finiteQuotientOfFreeOfNeBot P
      (Ring.ne_bot_of_isMaximal_of_not_isField hP (RingOfIntegers.not_isField E))
    obtain ⟨p, hp⟩ := CharP.exists (𝓞 E ⧸ P)
    refine ⟨p, (CharP.char_is_prime_or_zero (𝓞 E ⧸ P) p).resolve_right (CharP.char_ne_zero_of_finite (𝓞 E ⧸ P) p), ?_⟩
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast, CharP.cast_eq_zero]
  obtain ⟨γ, hγ, h1, h2⟩ := hgen p hp
  refine ⟨γ, fun x y => by rw [← hf, ← hf]; exact hγ y x, ?_⟩
  rw [gmap_eq_tMap, tMap_loc, stdLat_eq]
  exact le_antisymm (loc_le_of_nsmul hp hP hpP h2) (loc_le_of_nsmul hp hP hpP h1)

/- English proof (translation)
Apply the tactic sequence `obtain ⟨e, he⟩ := exists_isometry hc W hs hp`. Take `⟨h1, h2, -⟩` from `Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.2.1 W hs hp) W.L0 W.standardTuple_isLattice`. Establish `h3` using `mass_transport e.symm (isoSymm e he) (tMap e W.L0) (by rwa [tMap_symm]) (by rwa [tMap_symm])`. Rewrite `h3` using `[tMap_symm]`. Rewrite using `[← h3]`.

Use `(mass_eq_of_sameGenus _ (stdForm_symm E _) (fun r => ?_) (sameGenus_stdLat hc _ (tMap_lattice e _ W.standardTuple_isLattice) fun x => ?_)).symm` and prove the remaining obligations. Conclude with `⟨IsCMField.ringOfIntegersComplexConj E r, rfl⟩`. Take `⟨x, rfl⟩` from `e.surjective x`. Rewrite using `[mem_tMap, e.symm_apply_apply]`. Use `conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 from W.baseLattice_isUnimodular, mem_dual_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `H _ ⟨y, hy, rfl⟩`. Conclude with `(he y x).symm ▸ H y hy`. Introduce `H y hy`. Conclude with `he y x ▸ H _ ⟨y, hy, rfl⟩`.
-/
theorem mass_eq_std (hc : Formalism.HermitianLatticesTheory.IsCMUnram E) (W : Formalism.BasicNotions.HSpace E) (hs : W.SigOK)
    (hp : ∀ τ : E →+* ℂ, W.sig τ = (W.rank, 0)) :
    Formalism.HermitianLatticesTheory.mass W.hT W.L0 = Formalism.HermitianLatticesTheory.mass (stdForm E W.rank) (stdLat E W.rank) := by
  obtain ⟨e, he⟩ := exists_isometry hc W hs hp
  obtain ⟨h1, h2, -⟩ := Formalism.HermitianLatticesTheory.massBasic _ _ W.hT W.herm
    (GlobalTheory.IndefiniteRowSideFullHecke.MassFormulaPositivity.trace_pos hc.2.1 W hs hp) W.L0 W.standardTuple_isLattice
  have h3 := mass_transport e.symm (isoSymm e he) (tMap e W.L0) (by rwa [tMap_symm]) (by rwa [tMap_symm])
  rw [tMap_symm] at h3
  rw [← h3]
  refine (mass_eq_of_sameGenus _ (stdForm_symm E _) (fun r => ?_)
    (sameGenus_stdLat hc _ (tMap_lattice e _ W.standardTuple_isLattice) fun x => ?_)).symm
  · exact ⟨IsCMField.ringOfIntegersComplexConj E r, rfl⟩
  · obtain ⟨x, rfl⟩ := e.surjective x
    rw [mem_tMap, e.symm_apply_apply]
    conv_lhs => rw [← show Formalism.HermitianLatticesTheory.dual W.hT W.L0 = W.L0 from W.baseLattice_isUnimodular, mem_dual_iff]
    constructor
    · rintro H _ ⟨y, hy, rfl⟩
      exact (he y x).symm ▸ H y hy
    · intro H y hy
      exact he y x ▸ H _ ⟨y, hy, rfl⟩

end

/- English proof (translation)
The claim follows from `haveI : IsCMField D.host.E := D.host.isCMField_hostE fun W hs hp => mass_eq_std (E := D.host.E) D.sp.cm.cmUnram W hs hp`.
-/
theorem mass_eq_massI (D : D7) : letI := D.host.cmStar
    ∀ W : Formalism.BasicNotions.HSpace D.host.E, W.SigOK → (∀ τ : D.host.E →+* ℂ, W.sig τ = (W.rank, 0)) →
      Formalism.HermitianLatticesTheory.mass W.hT W.L0 = massI D W.rank :=
  haveI : IsCMField D.host.E := D.host.isCMField_hostE
  fun W hs hp => mass_eq_std (E := D.host.E) D.sp.cm.cmUnram W hs hp

end GlobalTheory.DefiniteMass
