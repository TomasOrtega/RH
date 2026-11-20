import Mathlib
import Development.AutomorphicSpectrum.Definitions.MetricPeriods.MetricsProjectionFormulaNef
import Development.AutomorphicSpectrum.Proofs.MetricProofs.LogResolutionFunctorialHolomorphicStatement
import Development.WeilBound.CoreStatements.FlagImmersions.BirationalOfClosure
import Development.WeilBound.CoreStatements.FlagImmersions.InteriorUnionEmpty

noncomputable section

namespace RootFieldNumerics.Ref

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo GlobalTheory.CompanionTheory.Ar
open ReciprocityTheory.ChartRestriction.G.AI.I1 (IsBlockMap pullDeg)
open ReciprocityTheory.ChartRestriction.G.AI.I4 (imageZ IsPullHerm)
open ReciprocityTheory.AnForm.M
open GlobalTheory.CompanionTheory.Ar.Chg GlobalTheory.CompanionTheory.Ar.Chg.DegBlock GroundTheory.Heights₂.Heights

/- English proof (translation)
Introduce `hG`. Apply `h` to reduce the goal to its premises. Establish `hk : mConeMap y G = 0` using `hG`. Establish `e : ((MvPolynomial.aeval (R` using `Ω) (fun _ : K => (1 : Ω))).restrictScalars ℤ).comp (mConeMap y) = aeval y := by`. Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises.

Introduce `p`. Simplify using `[mConeMap]`. Use `congrArg (fun f => f G) e` as an intermediate fact. Simplify using `only [AlgHom.comp_apply] at this`. Rewrite using `[← this, hk, map_zero]`.
-/
private theorem not_mem_mCoordIdeal_of_aeval_ne_zero {K : Type} {ι : K → Type} {Ω : Type} [Field Ω]
    (y : (Σ k, ι k) → Ω) (G : MRing ι) (h : aeval y G ≠ 0) : G ∉ mCoordIdeal y := by
  intro hG
  apply h
  have hk : mConeMap y G = 0 := hG
  have e : ((MvPolynomial.aeval (R := Ω) (fun _ : K => (1 : Ω))).restrictScalars ℤ).comp (mConeMap y) = aeval y := by
    apply MvPolynomial.algHom_ext
    intro p
    simp [mConeMap]
  have := congrArg (fun f => f G) e
  simp only [AlgHom.comp_apply] at this
  rw [← this, hk, map_zero]

/- English proof (translation)
Take `⟨c, hc, rfl⟩` from `h`. Conclude with `⟨fun k => c (κ k), fun k => hc _, by funext p; rfl⟩`.
-/
private theorem sameOrbit_comp_blkV {K₀ K : Type} {ι₀ : K₀ → Type} {ι : K → Type} (κ : K₀ → K)
    (bx : ∀ k, ι₀ k ≃ ι (κ k)) {z z₁ : (Σ k, ι k) → ℂ} (h : SameOrbit z₁ z) :
    SameOrbit (fun p => z₁ (blkV κ bx p)) (fun p => z (blkV κ bx p)) := by
  obtain ⟨c, hc, rfl⟩ := h
  exact ⟨fun k => c (κ k), fun k => hc _, by funext p; rfl⟩

/- English proof (translation)
Take `⟨bx, rfl⟩` from `RootFieldNumerics.Ref.Zeros.exists_blkV hv`. Substitute `hJ` using the available equality. Establish `hκ : Function.Injective κ` using `hv.1`. Establish `hyk : ∀ (k : K₀) (a : ι₀ k), y ⟨κ k, bx k a⟩ = (RingHom.id Ω) (y₀ ⟨k, a⟩)` using `fun k a => hy ⟨k, a⟩`. Establish `hrk : Module.finrank Ω Ω = 1` using `Module.finrank_self Ω`.

Establish `hP₀ : (mCoordIdeal y₀).IsPrime` using `RingHom.ker_isPrime _`. Take `⟨G₁, a₁, hG₁, hG₁P, hcount⟩` from `GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_count y₀ y κ bx (RingHom.id Ω) D 1 hκ hyk hA₀ hA hB₀ hB hrk one_pos`. Take `⟨G₃, a₃, hG₃, hG₃P, hloc3⟩` from `GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_local_section y₀ y κ bx (RingHom.id Ω) 1 hyk hP₀ hB₀ hrk one_pos`. Establish `hTop : IsMultiHomogIdeal (⊤ : Ideal (MRing ι))`. Use `⟨{1}, ?_, Ideal.span_singleton_one.symm⟩` and prove the remaining obligations.

Introduce `f hf`. Rewrite `hf` using `[Set.mem_singleton_iff]`. Substitute `hf` using the available equality. Conclude with `⟨0, GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_one'⟩`. Establish `hTopP : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y` using `fun h => not_mem_mCoordIdeal_of_aeval_ne_zero y 1 (by simp) (h Submodule.mem_top)`.

Take `⟨J', -, hJ'h, hJ'P, ⟨R⟩⟩` from `hRes K ι (mCoordIdeal y) ⊤ D hA hTop hTopP`. Choose the witnesses or unpack the hypotheses as in `⟨F₁, hF₁J, hF₁P, a₄, hF₁h⟩ : ∃ F ∈ J', F ∉ mCoordIdeal y ∧ ∃ a, IsMultiHomog F a := by`. Take `⟨S, hS, rfl⟩` from `hJ'h`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`.

Apply `hJ'P` to reduce the goal to its premises. Rewrite using `[Ideal.span_le]`. Introduce `f hf`. Take `⟨a, ha⟩` from `hS f hf`. Assume the negation of the conclusion as `hfP`.

Conclude with `hcon f (Ideal.subset_span hf) hfP a ha`. Establish `halg1 : ∀ α : Ω, letI` using `(RingHom.id Ω).toAlgebra; IsAlgebraic Ω α := by`. Introduce `α`. Use `letI := (RingHom.id Ω).toAlgebra`. Conclude with `isAlgebraic_algebraMap (R := Ω) (A := Ω) α`.

Take `⟨G₄, a₄', hG₄h, hG₄y, hG₄z⟩` from `RootFieldNumerics.Ref.Zeros.zeros_proj y₀ y (RingHom.id Ω) hv hy hB₀ halg1 hF₁h hF₁P`. Establish `hG₄P : G₄ ∉ mCoordIdeal y₀` using `not_mem_mCoordIdeal_of_aeval_ne_zero y₀ G₄ hG₄y`. Establish `hFh` using `GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' hG₁ hG₃) hG₄h`. Establish `hFP : G₁ * G₃ * G₄ ∉ mCoordIdeal y₀`. Introduce `hm`.

Break down `hP₀.mem_or_mem hm with hm | hm` into its components or cases. Break down `hP₀.mem_or_mem hm with hm | hm` into its components or cases. Conclude with `hG₁P hm`. Conclude with `hG₃P hm`. Conclude with `hG₄P hm`.

Set `bk' : Unit → K₀` to `fun _ => k₀`. Set `bx' : ∀ u : Unit, Fin (n + 1) ≃ ι₀ (bk' u)` to `fun _ => ix`. Establish `hv' : IsBlockMap bk' (blkV bk' bx')` using `GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx' (fun a b _ => Subsingleton.elim a b)`. Establish `hy' : ∀ p, y₀ (blkV bk' bx' p) = g ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p)` using `fun p => hyf p.2`. Establish `hBf` using `RootFieldNumerics.Ref.Zeros.birational_of_closure yf hgen`.

Establish `halg2 : ∀ α : Ω, letI` using `g.toAlgebra; IsAlgebraic Ωf α := by`. Use `letI := g.toAlgebra`. Use `haveI : FiniteDimensional Ωf Ω := Module.finite_of_finrank_pos hfin`. Conclude with `fun α => Algebra.IsAlgebraic.isAlgebraic α`. Take `⟨G', b', hG'h, hG'y, hG'z⟩` from `RootFieldNumerics.Ref.Zeros.zeros_proj (fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) y₀ g hv' hy' hBf halg2 hFh hFP`.

Establish `hGh` using `GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_rename' hv' hG'h`. Establish `hGy0 : aeval y₀ (rename (blkV bk' bx') G') ≠ 0`. Rewrite using `[MvPolynomial.aeval_rename]`. Establish `e1 : y₀ ∘ blkV bk' bx' = fun p => g.toIntAlgHom ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p)`. Use function extensionality and compare the values at `hy'`.

Rewrite using `[e1, ← MvPolynomial.comp_aeval_apply]`. Conclude with `(map_ne_zero g).mpr hG'y`. Establish `hGP : rename (blkV bk' bx') G' ∉ mCoordIdeal y₀` using `not_mem_mCoordIdeal_of_aeval_ne_zero y₀ _ hGy0`. Establish `hG2P : rename (blkV κ bx) (rename (blkV bk' bx') G') ∉ mCoordIdeal y`. Apply `not_mem_mCoordIdeal_of_aeval_ne_zero` to reduce the goal to its premises.

Rewrite using `[MvPolynomial.aeval_rename]`. Establish `e2 : y ∘ blkV κ bx = y₀` using `funext hy`. Rewrite using `[e2]`. Conclude with `hGy0`. Establish `hnz : ∀ w ∈ mcPts (mCoordIdeal y₀), eval w (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) ≠ 0 → eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₃) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₄) ≠ 0`.

Introduce `w hw hGw`. Establish `hFw : eval w (map (Int.castRingHom ℂ) (G₁ * G₃ * G₄)) ≠ 0`. Introduce `h0`. Apply `hGw` to reduce the goal to its premises. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']`.

Conclude with `hG'z w hw h0`. Simplify using `only [map_mul, mul_ne_zero_iff] at hFw`. Conclude with `⟨hFw.1.1, hFw.1.2, hFw.2⟩`. Take `⟨h, hh, hho⟩` from `GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K₀ ι₀ K ι κ (blkV κ bx) (mCoordIdeal y₀) (mCoordIdeal y) J' D D R₀ R hv (GlobalTheory.CompanionTheory.Ar.Chg.mCoordIdeal_le_imageZ (RingHom.id Ω) bx hyk)`. Use `haveI := R₀.compact`.

Use `haveI := R₀.t2`. Use `haveI := R.compact`. Use `haveI := R.t2`. Establish `hdeg1` using `GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence K₀ ι₀ K ι (mCoordIdeal y₀) ⊤ (mCoordIdeal y) J' D R₀.X R₀.A R₀ id R h (fun z w => SameOrbit (fun p => z (blkV κ bx p)) w) (rename (blkV bk' bx') G') (rename (blkV κ bx) (rename (blkV bk' bx') G')) _ _ 1 r …`. Introduce `x x₀ hx`.

Simplify using `only [id] at hx`. Substitute `hx` using the available equality. Conclude with `GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x))`. Use the proof step `(by`. Introduce `x x₀ hr`.

Conclude with `R₀.inj x₀ (h x) (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.not_mem_mcPts_top _) (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' hr) (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x …`. Use the proof step `(by`. Introduce `w hw hGw`. Conclude with `hcount w hw (hnz w hw hGw).1)`. Use the proof step `(by`.

Introduce `z hz hzJ w hw hr`. Assume the negation of the conclusion as `hGw`. Apply `(hnz w hw hGw).2.2` to reduce the goal to its premises. Establish `hFz : eval z (map (Int.castRingHom ℂ) F₁) = 0` using `hzJ.2 F₁ hF₁J`. Conclude with `(HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG₄h hr).1 (hG₄z z hz hFz))`.

Use the proof step `(by`. Introduce `z hz w hw hr hGw`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']`. Conclude with `(HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hGh hr).2 hGw)`. Use the proof step `(by`.

Introduce `z hz w₀ hw₀ hr hGw`. Conclude with `hloc3 z hz w₀ hw₀ hr (hnz w₀ hw₀ hGw).2.1)`. Use `set S : Set X := {x | eval (fun p : (Σ _ : Unit, Fin (n + 1)) => pt x p.2) (map (Int.castRingHom ℂ) G') = 0} with hSdef`. Establish `hpre : ∀ x₀ : R₀.X, (eval (R₀.lift x₀ x₀) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0 ↔ π x₀ ∈ S)`. Introduce `x₀`.

Take `⟨a, ha⟩` from `hpt x₀`. Establish `hmem : R₀.lift x₀ x₀ ∈ mcPts (mCoordIdeal y₀)` using `R₀.mem x₀ x₀ (R₀.mem_U x₀)`. Establish `ha0 : a ≠ 0`. Introduce and unpack `rfl`. Take `⟨i, hi⟩` from `hmem.1 k₀`.

Apply `hi` to reduce the goal to its premises. Use `congrFun ha (ix.symm i)` as an intermediate fact. Simplify using `using this`. Rewrite using `[GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']`. Apply `HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h` to reduce the goal to its premises.

Use `⟨fun _ => a, fun _ => ha0, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Use `congrFun ha p.2` as an intermediate fact. Express the relevant statement in the definitionally equal form `R₀.lift x₀ x₀ ⟨k₀, ix p.2⟩ = a * pt (π x₀) p.2`. Simplify using `using this`.

Establish `hNS : id '' {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0} ⊆ π ⁻¹' S`. Introduce and unpack `_ ⟨x₀, hx, rfl⟩`. Conclude with `(hpre x₀).1 hx`. Establish `hint : interior (π ⁻¹' S) = ∅`. Establish `e3 : π ⁻¹' S = {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0}`.

Use extensionality with `x₀`. Conclude with `(hpre x₀).symm`. Rewrite using `[e3]`. Conclude with `HilbertSamuel.AnResNullForm.interior_eq_empty HilbertSamuel.NonvanishingDense.full R₀.toAnRes hA₀ hGh hGP`. Establish `hSan : A.IsAnalyticSubset S`.

Introduce `x`. Take `⟨U, lam, hU, hxU, hlam, hprop⟩` from `hloc x`. Establish `hpoly : ∀ q : MvPolynomial (Σ _ : Unit, Fin (n + 1)) ℂ, A.HoloOn U (fun y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) q)`. Introduce `q`. Proceed by induction on `q using MvPolynomial.induction_on`.

Introduce `j`. Simplify using `only [eval_C]`. Conclude with `analyticOnNhd_const`. Name the introduced variables `p q hp hq`. Introduce `j`.

Simplify using `only [map_add]`. Conclude with `(hp j).add (hq j)`. Name the introduced variables `p i hp`. Introduce `j`. Simplify using `only [map_mul, eval_X]`.

Conclude with `(hp j).mul (hlam i.2 j)`. Use `⟨U, hU, hxU, 1, fun _ y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) (map (Int.castRingHom ℂ) G'), fun _ => hpoly _, ?_⟩` and prove the remaining obligations. Use extensionality with `y`. Simplify using `only [Set.mem_inter_iff, Set.mem_setOf_eq, hSdef]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨hyS, hyU⟩`. Use `⟨hyU, fun _ => ?_⟩` and prove the remaining obligations. Take `⟨a₀, ha₀, he⟩` from `hprop y hyU`. Use `(HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).2 hyS` and prove the remaining obligations. Use function extensionality and compare the values at `p`.

Rewrite using `[he]`. Both sides reduce to the same expression. Introduce and unpack `⟨hyU, hz⟩`. Use `⟨?_, hyU⟩` and prove the remaining obligations. Take `⟨a₀, ha₀, he⟩` from `hprop y hyU`.

Use `(HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).1 (hz 0)` and prove the remaining obligations. Use function extensionality and compare the values at `p`. Rewrite using `[he]`. Both sides reduce to the same expression. Establish `hcomp` using `RootFieldNumerics.Ref.Comp.degree_comp hπ hh hd hdeg hdeg1 hSan hint hNS`.

Conclude with `⟨J', R, h, br ∪ S, hh, fun x => hho x, GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, hcomp⟩`.
-/
theorem exists_res_degree (hRes : ResExistsStatement) {K₀ K : Type} [Fintype K₀] [Fintype K] {ι₀ : K₀ → Type}
    {ι : K → Type} [∀ k, Fintype (ι₀ k)] [∀ k, Fintype (ι k)] {Ω Ωf : Type} [Field Ω] [Field Ωf] [CharZero Ω]
    (y₀ : (Σ k, ι₀ k) → Ω) (y : (Σ k, ι k) → Ω) {κ : K₀ → K} {v : (Σ k, ι₀ k) → Σ k, ι k} (hv : IsBlockMap κ v)
    (hy : ∀ p, y (v p) = y₀ p) {D : ℕ} (hA₀ : IsArithVar (mCoordIdeal y₀) (D + 1))
    (hA : IsArithVar (mCoordIdeal y) (D + 1)) (hB₀ : Birational y₀) (hB : Birational y)
    {J₀ : Ideal (MRing ι₀)} (hJ : J₀ = ⊤) (R₀ : AnLogRes (mCoordIdeal y₀) J₀ D)
    {X : Type} [TopologicalSpace X] [CompactSpace X] [T2Space X] (A : FinHolAtlas D X) (π : R₀.X → X)
    (hπ : HoloMap R₀.A A π) {d : ℕ} (hd : 0 < d) {br : Set X} (hdeg : IsDegreeOff A R₀.A π d br)
    {n : ℕ} (yf : Fin (n + 1) → Ωf)
    (hgen : Subfield.closure (Set.range fun ij : Fin (n + 1) × Fin (n + 1) => yf ij.1 / yf ij.2) = ⊤)
    (g : Ωf →+* Ω) (hfin : letI := g.toAlgebra; 0 < Module.finrank Ωf Ω)
    (k₀ : K₀) (ix : Fin (n + 1) ≃ ι₀ k₀) (hyf : ∀ j, y₀ ⟨k₀, ix j⟩ = g (yf j))
    (pt : X → Fin (n + 1) → ℂ)
    (hpt : ∀ x, ∃ a : ℂ, (fun j => R₀.lift x x ⟨k₀, ix j⟩) = a • pt (π x))
    (hloc : ∀ x : X, ∃ (U : Set X) (lam : X → Fin (n + 1) → ℂ), IsOpen U ∧ x ∈ U ∧
      (∀ j, A.HoloOn U fun y => lam y j) ∧ ∀ y ∈ U, ∃ a₀ : ℂ, a₀ ≠ 0 ∧ lam y = a₀ • pt y) :
    ∃ (J : Ideal (MRing ι)) (R : AnLogRes (mCoordIdeal y) J D) (h : R.X → R₀.X) (br' : Set X),
      HoloMap R.A R₀.A h ∧ (∀ x, SameOrbit (R₀.lift (h x) (h x)) (fun p => R.lift x x (v p))) ∧
      HoloMap R.A A (π ∘ h) ∧ IsDegreeOff A R.A (π ∘ h) d br' := by
  classical
  obtain ⟨bx, rfl⟩ := RootFieldNumerics.Ref.Zeros.exists_blkV hv
  subst hJ
  have hκ : Function.Injective κ := hv.1
  have hyk : ∀ (k : K₀) (a : ι₀ k), y ⟨κ k, bx k a⟩ = (RingHom.id Ω) (y₀ ⟨k, a⟩) := fun k a => hy ⟨k, a⟩
  have hrk : Module.finrank Ω Ω = 1 := Module.finrank_self Ω
  have hP₀ : (mCoordIdeal y₀).IsPrime := RingHom.ker_isPrime _
  obtain ⟨G₁, a₁, hG₁, hG₁P, hcount⟩ := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_count y₀ y κ bx (RingHom.id Ω) D 1
    hκ hyk hA₀ hA hB₀ hB hrk one_pos
  obtain ⟨G₃, a₃, hG₃, hG₃P, hloc3⟩ := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.exists_local_section y₀ y κ bx
    (RingHom.id Ω) 1 hyk hP₀ hB₀ hrk one_pos
  have hTop : IsMultiHomogIdeal (⊤ : Ideal (MRing ι)) := by
    refine ⟨{1}, ?_, Ideal.span_singleton_one.symm⟩
    intro f hf
    rw [Set.mem_singleton_iff] at hf
    subst hf
    exact ⟨0, GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_one'⟩
  have hTopP : ¬ (⊤ : Ideal (MRing ι)) ≤ mCoordIdeal y := fun h =>
    not_mem_mCoordIdeal_of_aeval_ne_zero y 1 (by simp) (h Submodule.mem_top)
  obtain ⟨J', -, hJ'h, hJ'P, ⟨R⟩⟩ := hRes K ι (mCoordIdeal y) ⊤ D hA hTop hTopP
  obtain ⟨F₁, hF₁J, hF₁P, a₄, hF₁h⟩ : ∃ F ∈ J', F ∉ mCoordIdeal y ∧ ∃ a, IsMultiHomog F a := by
    obtain ⟨S, hS, rfl⟩ := hJ'h
    by_contra hcon
    push_neg at hcon
    apply hJ'P
    rw [Ideal.span_le]
    intro f hf
    obtain ⟨a, ha⟩ := hS f hf
    by_contra hfP
    exact hcon f (Ideal.subset_span hf) hfP a ha
  have halg1 : ∀ α : Ω, letI := (RingHom.id Ω).toAlgebra; IsAlgebraic Ω α := by
    intro α
    letI := (RingHom.id Ω).toAlgebra
    exact isAlgebraic_algebraMap (R := Ω) (A := Ω) α
  obtain ⟨G₄, a₄', hG₄h, hG₄y, hG₄z⟩ := RootFieldNumerics.Ref.Zeros.zeros_proj y₀ y (RingHom.id Ω) hv hy hB₀ halg1 hF₁h hF₁P
  have hG₄P : G₄ ∉ mCoordIdeal y₀ := not_mem_mCoordIdeal_of_aeval_ne_zero y₀ G₄ hG₄y
  have hFh := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_mul' hG₁ hG₃) hG₄h
  have hFP : G₁ * G₃ * G₄ ∉ mCoordIdeal y₀ := by
    intro hm
    rcases hP₀.mem_or_mem hm with hm | hm
    · rcases hP₀.mem_or_mem hm with hm | hm
      · exact hG₁P hm
      · exact hG₃P hm
    · exact hG₄P hm
  let bk' : Unit → K₀ := fun _ => k₀
  let bx' : ∀ u : Unit, Fin (n + 1) ≃ ι₀ (bk' u) := fun _ => ix
  have hv' : IsBlockMap bk' (blkV bk' bx') :=
    GlobalTheory.CompanionTheory.Ar.Chg.isBlockMap_blkV bx' (fun a b _ => Subsingleton.elim a b)
  have hy' : ∀ p, y₀ (blkV bk' bx' p) = g ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p) :=
    fun p => hyf p.2
  have hBf := RootFieldNumerics.Ref.Zeros.birational_of_closure yf hgen
  have halg2 : ∀ α : Ω, letI := g.toAlgebra; IsAlgebraic Ωf α := by
    letI := g.toAlgebra
    haveI : FiniteDimensional Ωf Ω := Module.finite_of_finrank_pos hfin
    exact fun α => Algebra.IsAlgebraic.isAlgebraic α
  obtain ⟨G', b', hG'h, hG'y, hG'z⟩ := RootFieldNumerics.Ref.Zeros.zeros_proj
    (fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) y₀ g hv' hy' hBf halg2 hFh hFP
  have hGh := GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_rename' hv' hG'h
  have hGy0 : aeval y₀ (rename (blkV bk' bx') G') ≠ 0 := by
    rw [MvPolynomial.aeval_rename]
    have e1 : y₀ ∘ blkV bk' bx' = fun p => g.toIntAlgHom ((fun p : (Σ _ : Unit, Fin (n + 1)) => yf p.2) p) :=
      funext hy'
    rw [e1, ← MvPolynomial.comp_aeval_apply]
    exact (map_ne_zero g).mpr hG'y
  have hGP : rename (blkV bk' bx') G' ∉ mCoordIdeal y₀ := not_mem_mCoordIdeal_of_aeval_ne_zero y₀ _ hGy0
  have hG2P : rename (blkV κ bx) (rename (blkV bk' bx') G') ∉ mCoordIdeal y := by
    apply not_mem_mCoordIdeal_of_aeval_ne_zero
    rw [MvPolynomial.aeval_rename]
    have e2 : y ∘ blkV κ bx = y₀ := funext hy
    rw [e2]
    exact hGy0
  have hnz : ∀ w ∈ mcPts (mCoordIdeal y₀),
      eval w (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) ≠ 0 →
      eval w (map (Int.castRingHom ℂ) G₁) ≠ 0 ∧ eval w (map (Int.castRingHom ℂ) G₃) ≠ 0 ∧
        eval w (map (Int.castRingHom ℂ) G₄) ≠ 0 := by
    intro w hw hGw
    have hFw : eval w (map (Int.castRingHom ℂ) (G₁ * G₃ * G₄)) ≠ 0 := by
      intro h0
      apply hGw
      rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
      exact hG'z w hw h0
    simp only [map_mul, mul_ne_zero_iff] at hFw
    exact ⟨hFw.1.1, hFw.1.2, hFw.2⟩
  obtain ⟨h, hh, hho⟩ := GlobalTheory.CompanionTheory.Ar.PB.Proj.holoMap_of_blockProj K₀ ι₀ K ι κ (blkV κ bx) (mCoordIdeal y₀)
    (mCoordIdeal y) J' D D R₀ R hv (GlobalTheory.CompanionTheory.Ar.Chg.mCoordIdeal_le_imageZ (RingHom.id Ω) bx hyk)
  haveI := R₀.compact
  haveI := R₀.t2
  haveI := R.compact
  haveI := R.t2
  have hdeg1 := GlobalTheory.CompanionTheory.Ar.PB.CovMap.Deg.isDegreeOff_of_correspondence K₀ ι₀ K ι (mCoordIdeal y₀) ⊤
    (mCoordIdeal y) J' D R₀.X R₀.A R₀ id R h (fun z w => SameOrbit (fun p => z (blkV κ bx p)) w)
    (rename (blkV bk' bx') G') (rename (blkV κ bx) (rename (blkV bk' bx') G')) _ _ 1 rfl hA₀ hA
    (holoMap_id _) (isDegreeOff_id _) hh hGh hGP
    (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.isMultiHomog_rename' hv hGh) hG2P
    (fun z z₁ w w₁ hr hz hw => GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans'
      (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans' (sameOrbit_comp_blkV κ bx hz) hr)
      (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' hw))
    (by
      intro x x₀ hx
      simp only [id] at hx
      subst hx
      exact GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x))
    (by
      intro x x₀ hr
      exact R₀.inj x₀ (h x) (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.not_mem_mcPts_top _)
        (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_trans' (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' hr)
          (GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.sameOrbit_symm' (hho x))))
    (by
      intro w hw hGw
      exact hcount w hw (hnz w hw hGw).1)
    (by
      intro z hz hzJ w hw hr
      by_contra hGw
      apply (hnz w hw hGw).2.2
      have hFz : eval z (map (Int.castRingHom ℂ) F₁) = 0 := hzJ.2 F₁ hF₁J
      exact (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG₄h hr).1 (hG₄z z hz hFz))
    (by
      intro z hz w hw hr hGw
      rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
      exact (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hGh hr).2 hGw)
    (by
      intro z hz w₀ hw₀ hr hGw
      exact hloc3 z hz w₀ hw₀ hr (hnz w₀ hw₀ hGw).2.1)
  set S : Set X := {x | eval (fun p : (Σ _ : Unit, Fin (n + 1)) => pt x p.2) (map (Int.castRingHom ℂ) G') = 0}
    with hSdef
  have hpre : ∀ x₀ : R₀.X, (eval (R₀.lift x₀ x₀) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0
      ↔ π x₀ ∈ S) := by
    intro x₀
    obtain ⟨a, ha⟩ := hpt x₀
    have hmem : R₀.lift x₀ x₀ ∈ mcPts (mCoordIdeal y₀) := R₀.mem x₀ x₀ (R₀.mem_U x₀)
    have ha0 : a ≠ 0 := by
      rintro rfl
      obtain ⟨i, hi⟩ := hmem.1 k₀
      apply hi
      have := congrFun ha (ix.symm i)
      simpa using this
    rw [GlobalTheory.CompanionTheory.Ar.Chg.DegBlock.eval_map_rename']
    apply HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h
    refine ⟨fun _ => a, fun _ => ha0, ?_⟩
    funext p
    have := congrFun ha p.2
    change R₀.lift x₀ x₀ ⟨k₀, ix p.2⟩ = a * pt (π x₀) p.2
    simpa using this
  have hNS : id '' {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0}
      ⊆ π ⁻¹' S := by
    rintro _ ⟨x₀, hx, rfl⟩
    exact (hpre x₀).1 hx
  have hint : interior (π ⁻¹' S) = ∅ := by
    have e3 : π ⁻¹' S = {x : R₀.X | eval (R₀.lift x x) (map (Int.castRingHom ℂ) (rename (blkV bk' bx') G')) = 0} := by
      ext x₀
      exact (hpre x₀).symm
    rw [e3]
    exact HilbertSamuel.AnResNullForm.interior_eq_empty HilbertSamuel.NonvanishingDense.full R₀.toAnRes hA₀ hGh hGP
  have hSan : A.IsAnalyticSubset S := by
    intro x
    obtain ⟨U, lam, hU, hxU, hlam, hprop⟩ := hloc x
    have hpoly : ∀ q : MvPolynomial (Σ _ : Unit, Fin (n + 1)) ℂ,
        A.HoloOn U (fun y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) q) := by
      intro q
      induction q using MvPolynomial.induction_on
      · intro j
        simp only [eval_C]
        exact analyticOnNhd_const
      · rename_i p q hp hq
        intro j
        simp only [map_add]
        exact (hp j).add (hq j)
      · rename_i p i hp
        intro j
        simp only [map_mul, eval_X]
        exact (hp j).mul (hlam i.2 j)
    refine ⟨U, hU, hxU, 1,
      fun _ y => eval (fun p : (Σ _ : Unit, Fin (n + 1)) => lam y p.2) (map (Int.castRingHom ℂ) G'),
      fun _ => hpoly _, ?_⟩
    ext y
    simp only [Set.mem_inter_iff, Set.mem_setOf_eq, hSdef]
    constructor
    · rintro ⟨hyS, hyU⟩
      refine ⟨hyU, fun _ => ?_⟩
      obtain ⟨a₀, ha₀, he⟩ := hprop y hyU
      refine (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).2 hyS
      funext p
      rw [he]
      rfl
    · rintro ⟨hyU, hz⟩
      refine ⟨?_, hyU⟩
      obtain ⟨a₀, ha₀, he⟩ := hprop y hyU
      refine (HilbertSamuel.AnResNullForm.eval_eq_zero_iff_of_sameOrbit hG'h ⟨fun _ => a₀, fun _ => ha₀, ?_⟩).1 (hz 0)
      funext p
      rw [he]
      rfl
  have hcomp := RootFieldNumerics.Ref.Comp.degree_comp hπ hh hd hdeg hdeg1 hSan hint hNS
  exact ⟨J', R, h, br ∪ S, hh, fun x => hho x, GlobalTheory.CompanionTheory.Ar.PB.CovMap.holoMap_comp hh hπ, hcomp⟩

end RootFieldNumerics.Ref
