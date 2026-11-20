import Mathlib
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.EvaluationLawsGenericFramesAtlasHold
import Development.AbelianVarietyTheory.Proofs.GenericRegularity.NaturalRuleValueBaseChangeOfIsReduced
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.FramedPointEvalNaturalWeightScaling
import Development.AbelianVarietyTheory.Definitions.ThetaValues.SWEqSOf
import Development.AbelianVarietyTheory.Definitions.ThetaValues.GamAt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.AdmissibleModuleIffLatticeQuotients
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.TheoremZeroOfReducedInputs
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.SupBoundPageRows
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.LatOfLamSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.PullbackSections.NoCommonZeroSt
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.WeightAlgebra Formalism.MainNotions.DIV.Cons Formalism.MainNotions.Gaps Formalism.L2.Pj GlobalTheory.RunIn ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory.FrameZero

/- English proof (translation)
Take `⟨M, hM, hIM⟩` from `Ideal.exists_le_maximal I hI`. Use `haveI := hM`. Use `letI : Field (A ⧸ M) := Ideal.Quotient.field M`. Use `letI : Algebra K ℂ := σ.toAlgebra`. Use `haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)`.

Set `g : (A ⧸ M) →ₐ[K] ℂ` to `IsAlgClosed.lift`. Set `f : A →ₐ[K] ℂ` to `g.comp (Ideal.Quotient.mkₐ K M)`. Use `⟨⟨(f : A →+* ℂ), fun r => f.commutes r⟩, fun x hx => ?_⟩` and prove the remaining obligations. Use `show g (Ideal.Quotient.mk M x) = 0`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hx), map_zero]`.
-/
theorem exists_complex_point {K A : Type} [Field K] [CommRing A] [Algebra K A] [Algebra.FiniteType K A]
    (σ : K →+* ℂ) (I : Ideal A) (hI : I ≠ ⊤) : ∃ ψ : A →ₐ[K] CAt σ, ∀ x ∈ I, ψ x = 0 := by
  classical
  obtain ⟨M, hM, hIM⟩ := Ideal.exists_le_maximal I hI
  haveI := hM
  letI : Field (A ⧸ M) := Ideal.Quotient.field M
  letI : Algebra K ℂ := σ.toAlgebra
  haveI : Module.Finite K (A ⧸ M) := finite_of_finite_type_of_isJacobsonRing K (A ⧸ M)
  let g : (A ⧸ M) →ₐ[K] ℂ := IsAlgClosed.lift
  let f : A →ₐ[K] ℂ := g.comp (Ideal.Quotient.mkₐ K M)
  refine ⟨⟨(f : A →+* ℂ), fun r => f.commutes r⟩, fun x hx => ?_⟩
  show g (Ideal.Quotient.mk M x) = 0
  rw [Ideal.Quotient.eq_zero_iff_mem.mpr (hIM hx), map_zero]

set_option synthInstance.maxHeartbeats 400000 in

/- English proof (translation)
Introduce `D T h j hj a n m ws hws hz`. Take `⟨hL, -, hG, hA⟩` from `GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c`. Establish `hu` using `(h.toLawsCore.unf j hj T.σ₀ T.good_σ₀).2.2.1`. Introduce `k _ _ _ y`. Assume the negation of the conclusion as `hne`.

Simplify using `only [not_exists, not_not] at hne`. Take `⟨C, ψ, z, t', hψ, hbor⟩` from `hA hG k y`. Establish `hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (ws i) z = 0`. Introduce `i`. Establish `e1` using `GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t' z y hbor`.

Rewrite `e1` using `[hne i]`. Establish `hw : wchar (ex (T.Q.Dw j) a n) t' ≠ 0`. Unfold `wchar`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)`. Conclude with `(mul_eq_zero.mp e1.symm).resolve_left hw`.

Establish `hsm` using `C.sm`. Establish `hI : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≠ ⊤`. Introduce `htop`. Establish `hker : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≤ RingHom.ker ψ`. Rewrite using `[Ideal.span_le]`.

Introduce and unpack `_ ⟨i, rfl⟩`. Rewrite using `[SetLike.mem_coe, RingHom.mem_ker, ← GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ k ψ C.y z hψ]`. Conclude with `hz0 i`. Establish `h1` using `hker (htop ▸ Submodule.mem_top : (1 : C.R) ∈ _)`. Rewrite `h1` using `[RingHom.mem_ker, map_one]`.

Conclude with `one_ne_zero h1`. Take `⟨ψ', hψ'⟩` from `exists_complex_point T.σ₀ _ hI`. Take `⟨z', hz'⟩` from `hL.bc _ _ ψ' C.y`. Take `⟨kk, x, t, hb⟩` from `hu z'`. Take `⟨i, hi⟩` from `hz kk x.1 x.2`.

Apply `hi` to reduce the goal to its premises. Use `haveI : IsDomain (CAt T.σ₀) := inferInstanceAs (IsDomain ℂ)`. Establish `e2` using `GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t _ _ hb`. Establish `e3` using `GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ _ ψ' C.y z' hz'`. Establish `e4 : ψ' (evR (T.Q.Xo j) T.Q.c (ws i) C.y) = 0` using `hψ' _ (Ideal.subset_span ⟨i, rfl⟩)`.

Establish `hw2 : wchar (ex (T.Q.Dw j) a n) t ≠ 0`. Unfold `wchar`. Conclude with `Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)`. Establish `e6 : wchar (ex (T.Q.Dw j) a n) t * evR (T.Q.Xo j) T.Q.c (ws i) ((T.U j T.σ₀).un kk x) = 0`. Rewrite using `[← e2, e3, e4]`.

Establish `e5` using `(mul_eq_zero.mp e6).resolve_left hw2`. Unfold `rdU`. Simplify using `only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, e5]`. Unfold `toC`. Both sides reduce to the same expression.
-/
theorem noCommonZero_of_readings : ∀ (D : D7) (T : Top D) (_h : LawsP T) (j : ℕ) (_hj : InR D j) (a : (D.host.E →+* ℂ) × ℕ → ℕ) (n m : ℕ) (ws : Fin m → T.R j), (∀ i, ws i ∈ sec (T.Q.Xo j) T.Q.c a n) → (∀ k, ∀ x ∈ ((T.U j T.σ₀).X k).dom, ∃ i, rdU (T.U j T.σ₀) (ws i) k x ≠ 0) → NoCommonZero (T.Q.Xo j) T.Q.c ws := by
  intro D T h j hj a n m ws hws hz
  obtain ⟨hL, -, hG, hA⟩ := GlobalTheory.Reg.evLaws_genFr_atlas _ _ _ _ (T.Q.Xo j) T.Q.c
  have hu := (h.toLawsCore.unf j hj T.σ₀ T.good_σ₀).2.2.1
  intro k _ _ _ y
  by_contra hne
  simp only [not_exists, not_not] at hne
  obtain ⟨C, ψ, z, t', hψ, hbor⟩ := hA hG k y
  have hz0 : ∀ i, evR (T.Q.Xo j) T.Q.c (ws i) z = 0 := by
    intro i
    have e1 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t' z y hbor
    rw [hne i] at e1
    have hw : wchar (ex (T.Q.Dw j) a n) t' ≠ 0 := by
      unfold wchar
      exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
    exact (mul_eq_zero.mp e1.symm).resolve_left hw
  have hsm := C.sm
  have hI : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≠ ⊤ := by
    intro htop
    have hker : Ideal.span (Set.range fun i => evR (T.Q.Xo j) T.Q.c (ws i) C.y) ≤ RingHom.ker ψ := by
      rw [Ideal.span_le]
      rintro _ ⟨i, rfl⟩
      rw [SetLike.mem_coe, RingHom.mem_ker,
        ← GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ k ψ C.y z hψ]
      exact hz0 i
    have h1 := hker (htop ▸ Submodule.mem_top : (1 : C.R) ∈ _)
    rw [RingHom.mem_ker, map_one] at h1
    exact one_ne_zero h1
  obtain ⟨ψ', hψ'⟩ := exists_complex_point T.σ₀ _ hI
  obtain ⟨z', hz'⟩ := hL.bc _ _ ψ' C.y
  obtain ⟨kk, x, t, hb⟩ := hu z'
  obtain ⟨i, hi⟩ := hz kk x.1 x.2
  apply hi
  haveI : IsDomain (CAt T.σ₀) := inferInstanceAs (IsDomain ℂ)
  have e2 := GlobalTheory.ArcQ.evR_frBor_of_isDomain hL (hws i) t _ _ hb
  have e3 := GlobalTheory.Reg.evR_baseChange_of_isReduced _ _ _ _ (T.Q.Xo j) T.Q.c hL a n (ws i) (hws i) _ _ ψ' C.y z' hz'
  have e4 : ψ' (evR (T.Q.Xo j) T.Q.c (ws i) C.y) = 0 := hψ' _ (Ideal.subset_span ⟨i, rfl⟩)
  have hw2 : wchar (ex (T.Q.Dw j) a n) t ≠ 0 := by
    unfold wchar
    exact Finset.prod_ne_zero_iff.mpr fun _ _ => pow_ne_zero _ (Units.ne_zero _)
  have e6 : wchar (ex (T.Q.Dw j) a n) t * evR (T.Q.Xo j) T.Q.c (ws i) ((T.U j T.σ₀).un kk x) = 0 := by
    rw [← e2, e3, e4]
  have e5 := (mul_eq_zero.mp e6).resolve_left hw2
  unfold rdU
  simp only [LinearMap.coe_mk, AddHom.coe_mk, dif_pos x.2, e5]
  unfold toC
  rfl

end GlobalTheory.FrameZero
