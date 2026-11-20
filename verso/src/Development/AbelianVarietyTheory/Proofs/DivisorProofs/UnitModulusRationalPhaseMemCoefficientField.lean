import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TraceOfAt
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsNormIsRatScalar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DefiniteSideRealisationsCoefMapDifferRootOfUnityStatement
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RatOfOneMapOverL
import Formalism.LocalToGlobal.IndefiniteReal.FWCentral
import Development.AbelianVarietyTheory.Counterexamples.DegenerateExamples.PlaceExOfSurjective
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdjointIntertwines
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjugateTuplesConjugateResidueLevelsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeries
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ContinuousCoeffBlockAct
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Development.AbelianVarietyTheory.Proofs.CuspFormEvaluations.EmbeddingsDifferOnInteger
import Development.AbelianVarietyTheory.PublishedTheorems.PublishedFoundations.NonemptyAlgHomOfIsRayOfDvd
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.MovedFiniteDatumFourierExpansionChainless
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.MainNotions.DIV.Cons Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx
open Formalism.IndefR.FWT Formalism.IndefR.Datum GlobalTheory.BigTop GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.SeriesTie GlobalTheory.OnCmp
open GlobalTheory.BigOn GlobalTheory.BigOn.Exp Formalism.L2.Theta GlobalTheory.ExportSeries GlobalTheory.ConjTwist GlobalTheory.FlatVecSum GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels
open GlobalTheory.BigOn.Exp.SerBase
open scoped TensorProduct
set_option synthInstance.maxHeartbeats 400000
set_option maxHeartbeats 800000
attribute [local instance] Formalism.BasicNotions.Host.cmStar
set_option autoImplicit false

namespace GlobalTheory.PhaseOneOnto

/- English proof (translation)
Introduce `C hC hL s hs f hf w hw`. Establish `hw' : ∃ w0 ∈ ratVec R j c0 C.σ₂.fieldRange, w = b • w0`. Proceed by induction on `hw using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨v, hv, rfl⟩` from `hx`.

Conclude with `⟨c0 v, Submodule.subset_span ⟨v, hv, rfl⟩, hc v⟩`. Consider the case `zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨x0, hx0, rfl⟩` from `hx`. Take `⟨y0, hy0, rfl⟩` from `hy`.

Conclude with `⟨x0 + y0, add_mem hx0 hy0, (smul_add _ _ _).symm⟩`. Consider the case `smul r x _ hx`. Take `⟨x0, hx0, rfl⟩` from `hx`. Use `⟨r • x0, Submodule.smul_mem _ r hx0, ?_⟩` and prove the remaining obligations. Rewrite using `[Subfield.smul_def, Subfield.smul_def, smul_comm]`.

Take `⟨w0, hw0, rfl⟩` from `hw'`. Take `⟨h1, h2⟩` from `h C hC hL s hs f hf w0 hw0`. Establish `key : ∀ om : GA D (Vc D j) × GA D (Wc D j) →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ), (fun g => b⁻¹ * ph * thetaKO om s g (harmVec R j u (b • w0) f)) = fun g => ph * thetaKO om s g (harmVec R j u w0 f)`. Introduce `om`. Use function extensionality and compare the values at `g`.

Establish `e1 : harmVec R j u (b • w0) f = b • harmVec R j u w0 f`. Unfold `harmVec`. Rewrite using `[map_smul, map_smul]`. Establish `e2 : thetaKO om s g (b • harmVec R j u w0 f) = b * thetaKO om s g (harmVec R j u w0 f)`. Unfold `thetaKO`.

Rewrite using `[map_smul]`. Both sides reduce to the same expression. Rewrite using `[e1, e2]`. Clear the denominators using the available nonvanishing facts. Use `⟨by rw [key]; exact h1, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩` and prove the remaining obligations.

Establish `e` using `congrFun (key (RealDat.ωP R j A.μ0))`. Simplify `(h2 δ δc hδ).1 dd hdd` using `only [e]`. Rewrite using `[key]`. Conclude with `(h2 δ δc hδ).2 om hom`.
-/
theorem isRatPhase_of_smul {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F} {j : Fin D.R.m} {σ : T.Q.c.F →+* ℂ}
    {hV : T.V ((j : ℕ) + 1) σ = Wc D j} {κ : WeightFamilies.Wt D ((j : ℕ) + 1)} {u : ∀ τ, lowT (R.MW j (sg0 D A)) τ}
    {c0 c0' : VsV D j D.what₂.LL →ₛₗ[D.what₂.embLL] (R.cV j).W} {b : ℂ} (hb : b ≠ 0) (hc : ∀ F, c0' F = b • c0 F) {ph : ℂ}
    (h : IsRatPhase T R j hV κ u c0 ph) : IsRatPhase T R j hV κ u c0' (b⁻¹ * ph) := by
  intro C hC hL s hs f hf w hw
  have hw' : ∃ w0 ∈ ratVec R j c0 C.σ₂.fieldRange, w = b • w0 := by
    induction hw using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨v, hv, rfl⟩ := hx
      exact ⟨c0 v, Submodule.subset_span ⟨v, hv, rfl⟩, hc v⟩
    | zero => exact ⟨0, zero_mem _, (smul_zero _).symm⟩
    | add x y _ _ hx hy =>
      obtain ⟨x0, hx0, rfl⟩ := hx
      obtain ⟨y0, hy0, rfl⟩ := hy
      exact ⟨x0 + y0, add_mem hx0 hy0, (smul_add _ _ _).symm⟩
    | smul r x _ hx =>
      obtain ⟨x0, hx0, rfl⟩ := hx
      refine ⟨r • x0, Submodule.smul_mem _ r hx0, ?_⟩
      rw [Subfield.smul_def, Subfield.smul_def, smul_comm]
  obtain ⟨w0, hw0, rfl⟩ := hw'
  obtain ⟨h1, h2⟩ := h C hC hL s hs f hf w0 hw0
  have key : ∀ om : GA D (Vc D j) × GA D (Wc D j) →* Module.End ℂ (WO (Vc D j) (Wc D j) → ℂ),
      (fun g => b⁻¹ * ph * thetaKO om s g (harmVec R j u (b • w0) f)) = fun g => ph * thetaKO om s g (harmVec R j u w0 f) := by
    intro om
    funext g
    have e1 : harmVec R j u (b • w0) f = b • harmVec R j u w0 f := by
      unfold harmVec
      rw [map_smul, map_smul]
    have e2 : thetaKO om s g (b • harmVec R j u w0 f) = b * thetaKO om s g (harmVec R j u w0 f) := by
      unfold thetaKO
      rw [map_smul]
      rfl
    rw [e1, e2]
    field_simp
  refine ⟨by rw [key]; exact h1, fun δ δc hδ => ⟨fun dd hdd => ?_, fun om hom => ?_⟩⟩
  · have e := congrFun (key (RealDat.ωP R j A.μ0))
    simpa only [e] using (h2 δ δc hδ).1 dd hdd
  · rw [key]; exact (h2 δ δc hδ).2 om hom

end GlobalTheory.PhaseOneOnto

namespace GlobalTheory.PhaseOneOnto

open Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.IndefR.Mult ReciprocityTheory.ChartRestriction.G.Geo.Tor

variable {D : D7} {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
  {T : CoreJ D} [Algebra T.Q.c.F D.what₂.LL] {R : RealDat D A T.Q.c.F}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Take `⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩` from `hrow`. Establish `aux1` using `h1 ()`. Take `⟨ze, a1, -, h1⟩` from `aux1`. Establish `aux2` using `(hP.tuple ()).reps`. Take `⟨h, J', -, p2, p3, p4⟩` from `aux2`.

Establish `aux3` using `p2 y`. Take `⟨x, hx⟩` from `aux3`. Establish `e` using `p3 _ x hx`. Establish `aux4` using `h1 x ((p4 x).2 ⟨y, hx⟩)`. Take `⟨⟨f, hf, hf'⟩, h2⟩` from `aux4`.

Establish `hs` using `((mem_cusp _ _ _ _ _ _).1 hf).1`. Establish `h4` using `h2 f hs hf'`. Rewrite `hf` using `[← hn]`. Establish `aux5` using `hC _ _ f hf`. Take `⟨m, as, fs, hfs, hBC⟩` from `aux5`.

Establish `aux6` using `hP.lift.lev z`. Take `⟨k, hk, -⟩` from `aux6`. Establish `h5` using `rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1 (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)`. Use `⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩` and prove the remaining obligations. Establish `h6 : ph * R.thF i A.μ0 (R.jV i A.μ0 y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out * rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2)` using `(congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)`.

Rewrite using `[h6, h5]`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]`. Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Use `show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out * rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))`. Use `show _ * (_ * ((as l : ℂ) * _)) = _`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_comb_base {i : Fin D.R.m} {κ : WeightFamilies.Wt D ((i : ℕ) + 1)} {v : (R.MW i (sg0 D A)).Vec} {ι x₀} {ph : ℂ}
    (hn : κ.n = (Vc D i).rank) (O : OMDat T.toCore R i Unit (fun _ => A.μ0)) (hP : O.Pins κ v ι x₀)
    (hrow : O.OneMapOf κ v (T.cE ((i : ℕ) + 1) O.s0) ph) (y : A.fam.amb.FL i A.μ0) :
    ∃ ze ∈ D.what₂.embLL.toRatAlgHom.fieldRange, ∃ (m : ℕ) (as : Fin m → O.c'.F) (fs : Fin m → T.cuspA ((i : ℕ) + 1) (wtA κ) κ.n),
      ∀ q : AutQ (Wc D i), ph * R.thF i A.μ0 (R.jV i A.μ0 y) v q.out =
        ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) *
          O.phi (T.cE ((i : ℕ) + 1) O.s0) (fs l : T.R ((i : ℕ) + 1)) q.out) := by
  obtain ⟨hE, ⟨-, hC, hA, -, -, z, -, h1⟩, -⟩ := hrow
  have aux1 := h1 ()
  obtain ⟨ze, a1, -, h1⟩ := aux1
  have aux2 := (hP.tuple ()).reps
  obtain ⟨h, J', -, p2, p3, p4⟩ := aux2
  have aux3 := p2 y
  obtain ⟨x, hx⟩ := aux3
  have e := p3 _ x hx
  have aux4 := h1 x ((p4 x).2 ⟨y, hx⟩)
  obtain ⟨⟨f, hf, hf'⟩, h2⟩ := aux4
  have hs := ((mem_cusp _ _ _ _ _ _).1 hf).1
  have h4 := h2 f hs hf'
  rw [← hn] at hf
  have aux5 := hC _ _ f hf
  obtain ⟨m, as, fs, hfs, hBC⟩ := aux5
  have aux6 := hP.lift.lev z
  obtain ⟨k, hk, -⟩ := aux6
  have h5 := rdU_unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c') (hA _ _ z m as fs f ((mem_cusp _ _ _ _ _ _).1 hf).1
    (fun l => ((mem_cusp _ _ _ _ _ _).1 (hfs l)).1) hBC)
  refine ⟨ze, a1, m, as, fun l => ⟨_, (hE z k hk (fs l) (hfs l)).1⟩, fun q => ?_⟩
  have h6 : ph * R.thF i A.μ0 (R.jV i A.μ0 y) v q.out = ze * T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 *
      (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA κ) : ℂ) * (O.mu q.out *
        rdU (unfBC O.hle (T.U ((i : ℕ) + 1)) (inC O.c')) (actLev O.c' O.lev2 z f) (O.dict q.out).1 (O.dict q.out).2) :=
    (congrArg (ph * ·) (congrFun e q)).symm.trans (h4 q)
  rw [h6, h5]
  simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum]
  refine Finset.sum_congr rfl fun l _ => ?_
  show _ = ze * (as l : ℂ) * (_ * (T.cE ((i : ℕ) + 1) O.s0 (O.dict q.out).1 * O.mu q.out *
    rdU (T.U ((i : ℕ) + 1) O.s0) (actLev T.Q.c O.lev2 z (fs l)) (O.dict q.out).1 (O.dict q.out).2))
  show _ * (_ * ((as l : ℂ) * _)) = _
  ring

variable {κ : ∀ i : Fin D.R.m, WeightFamilies.Wt D ((i : ℕ) + 1)} {v₀ : ∀ (i : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (R.MW i σ).Vec}

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hn : (κ i).n = (Vc D i).rank` using `(fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm`. Establish `hev` using `fw.evaluates_of_lUnif hU`. Establish `aux` using `exists_comb_base hn (O i) hpins.2 hrow y`. Take `⟨ze, hze, m, as, fs, hq⟩` from `aux`. Use `⟨m, fun l => ze * (as l : ℂ), fs, fun g => ?_, fun l => ?_⟩` and prove the remaining obligations.

Establish `h1 : ∀ γ ∈ GQ (Wc D i), ∀ g, R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) (γ * g) = R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) g` using `GlobalTheory.TwistField.Read.mult_inv R.θ _ _ _ (hR.thP.thF_mem i A.μ0 _) _`. Establish `h2 : ∀ l, ∀ γ ∈ GQ (Wc D i), ∀ g, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ((i : ℕ) + 1)) (γ * g) = (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ( …` using `fun l γ hγ g => (GlobalTheory.TwistField.Read.ev_base fw hev (O i) (fs l) (γ * g)).symm.trans ((GlobalTheory.TwistField.Read.mult_inv R.θ _ _ _ ((hR.models.HW i _).2.1.le (LinearMap.mem_range_self _ _)) _ γ hγ g).trans (GlobalTheory.TwistField.Read.ev_base fw hev (O i) (fs l) g))`. Conclude with `congrFun (GlobalTheory.TwistField.Read.eq_of_out (Φ := fun g => ph * R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) g) (Ψ := fun g => ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) * (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ((i : ℕ) + 1) …`. Establish `h3 : ((as l : (O i).c'.F) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange` using `hpins.1 ▸ (as l).2`. Conclude with `AlgHom.mem_fieldRange.1 (mul_mem hze h3)`.
-/
theorem expands_thF_jV {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (fw : FWTie T R κ v₀) (hU : R.LUnif) {i : Fin D.R.m}
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (hpins : OMPins T R κ v₀ O i) {ph : ℂ}
    (hrow : (O i).OneMapOf (κ i) (v₀ i (sg0 D A)) (T.cE ((i : ℕ) + 1) (O i).s0) ph) (y : A.fam.amb.FL i A.μ0) :
    ∃ (m : ℕ) (a : Fin m → ℂ) (f : Fin m → T.toCore.cuspA ((i : ℕ) + 1) (wtA (κ i)) (κ i).n),
      Expands (O i) (κ i) (fun g => ph * R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) g) a f ∧
        ∀ k, a k ∈ D.what₂.embLL.fieldRange := by
  have hn : (κ i).n = (Vc D i).rank :=
    (fw.kap i (D.eTau.symm 1)).2.2.trans (D.sp.V_rank ((i : ℕ) + 1) (Nat.le_add_left _ _) i.2).symm
  have hev := fw.evaluates_of_lUnif hU
  have aux := exists_comb_base hn (O i) hpins.2 hrow y
  obtain ⟨ze, hze, m, as, fs, hq⟩ := aux
  refine ⟨m, fun l => ze * (as l : ℂ), fs, fun g => ?_, fun l => ?_⟩
  · have h1 : ∀ γ ∈ GQ (Wc D i), ∀ g, R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) (γ * g) =
        R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) g :=
      GlobalTheory.TwistField.Read.mult_inv R.θ _ _ _ (hR.thP.thF_mem i A.μ0 _) _
    have h2 : ∀ l, ∀ γ ∈ GQ (Wc D i), ∀ g, (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ((i : ℕ) + 1)) (γ * g) =
        (lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ((i : ℕ) + 1)) g := fun l γ hγ g =>
      (GlobalTheory.TwistField.Read.ev_base fw hev (O i) (fs l) (γ * g)).symm.trans
        ((GlobalTheory.TwistField.Read.mult_inv R.θ _ _ _ ((hR.models.HW i _).2.1.le (LinearMap.mem_range_self _ _)) _ γ hγ g).trans
          (GlobalTheory.TwistField.Read.ev_base fw hev (O i) (fs l) g))
    exact congrFun (GlobalTheory.TwistField.Read.eq_of_out
      (Φ := fun g => ph * R.thF i A.μ0 (R.jV i A.μ0 y) (v₀ i (sg0 D A)) g)
      (Ψ := fun g => ∑ l, ze * (as l : ℂ) * ((lieFac (T.Q.Dw ((i : ℕ) + 1)) (xiR D) (wtA (κ i)) : ℂ) *
          (O i).phi (T.cE ((i : ℕ) + 1) (O i).s0) (fs l : T.R ((i : ℕ) + 1)) g))
      (fun γ hγ g => congrArg (ph * ·) (h1 γ hγ g))
      (fun γ hγ g => Finset.sum_congr rfl fun l _ => congrArg (ze * (as l : ℂ) * ·) (h2 l γ hγ g)) hq) g
  · have h3 : ((as l : (O i).c'.F) : ℂ) ∈ D.what₂.embLL.toRatAlgHom.fieldRange := hpins.1 ▸ (as l).2
    exact AlgHom.mem_fieldRange.1 (mul_mem hze h3)

/- English proof (translation)
Use `⟨rfl, fun z => ?_⟩` and prove the remaining obligations. Establish `h1` using `hR.lev.xi A.μ0`. Rewrite `h1` using `[hR.lev.xi_base]`. Rewrite using `[GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 z]`. Simplify using the standard rewrite rules.
-/
theorem conjTup_base {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) (τ : ℂ ≃+* ℂ) : ConjTup R τ A.μ0 A.μ0 := by
  refine ⟨rfl, fun z => ?_⟩
  have h1 := hR.lev.xi A.μ0
  rw [hR.lev.xi_base] at h1
  rw [GlobalTheory.ChrEqUnique.eq_one_of_chrEq h1 z]
  simp

set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `h`. Establish `hZ` using `(GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hR τ A.μ0 A.μ0 (conjTup_base hR τ)).2.2.2 i hfix`. Establish `aux` using `hpins.2.lift.c0`. Take `⟨gramR, c0R, c0L, hT, hB⟩` from `aux`. Establish `aux2` using `GlobalTheory.PlaceValues.ext_val _ _ (R.B.L i A.μ0).pres (hT.mapL i) (hT.coefL i A.μ0) y.1 (Formalism.IndefR.FWT.fin _ h)`.

Take `⟨k, v, hv⟩` from `aux2`. Take `⟨v', hv1, hv'⟩` from `hB v`. Establish `hχ` using `(hZ.2 k.1 k.2 k.2).symm`. Establish `e1 : c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v) = c0L i v`. Use `(hc v' _ ?_).trans hv'` and prove the remaining obligations.

Rewrite using `[hv1, MvPolynomial.map_map, hpins.2.lift.field]`. Both sides reduce to the same expression. Establish `e2` using `(congrFun (hR.models.jV i A.μ0 y) (Formalism.IndefR.FWT.fin _ h)).trans hv`. Establish `key : ∀ χ : ℂ, τ χ = χ → ConjVec i τ (χ • GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v) (χ • GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v)`. Introduce `χ hχ`.

Unfold `ConjVec`. Rewrite using `[Submodule.coe_smul, GlobalTheory.CoefModel.mapVV_coe]`. Use extensionality with `m`. Simplify using `only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.coe_coe, map_mul, hχ]`. Rewrite using `[hτ _ ⟨_, rfl⟩]`.

Establish `e3` using `e2.trans (((map_smul c _ _).trans (congrArg (_ • ·) e1)).symm)`. Conclude with `⟨_, _, key _ hχ, e3, e3⟩`.
-/
theorem conjForm_jV {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) {i : Fin D.R.m}
    (O : ∀ i, OMDat T.toCore R i Unit (fun _ => A.μ0)) (hpins : OMPins T R κ v₀ O i)
    (c : VsV D i ℂ →ₗ[ℂ] (R.cV i).W) (hc : ExtC R i (inC (O i).c') (O i).c0' c) (τ : ℂ ≃+* ℂ) (hfix : FixBase T R i τ)
    (hτ : ∀ z ∈ D.what₂.embLL.fieldRange, τ z = z) (y : A.fam.amb.FL i A.μ0) :
    ConjForm R i τ c A.μ0 A.μ0 (R.jV i A.μ0 y) (R.jV i A.μ0 y) := by
  intro h
  have hZ := (GlobalTheory.T.conjugate_tuples_conjugate_residue_levels D G Pl0 T0 A T R F κ v₀ hR τ A.μ0 A.μ0 (conjTup_base hR τ)).2.2.2 i hfix
  have aux := hpins.2.lift.c0
  obtain ⟨gramR, c0R, c0L, hT, hB⟩ := aux
  have aux2 := GlobalTheory.PlaceValues.ext_val _ _ (R.B.L i A.μ0).pres (hT.mapL i) (hT.coefL i A.μ0) y.1 (Formalism.IndefR.FWT.fin _ h)
  obtain ⟨k, v, hv⟩ := aux2
  obtain ⟨v', hv1, hv'⟩ := hB v
  have hχ := (hZ.2 k.1 k.2 k.2).symm
  have e1 : c (GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v) = c0L i v := by
    refine (hc v' _ ?_).trans hv'
    rw [hv1, MvPolynomial.map_map, hpins.2.lift.field]
    rfl
  have e2 := (congrFun (hR.models.jV i A.μ0 y) (Formalism.IndefR.FWT.fin _ h)).trans hv
  have key : ∀ χ : ℂ, τ χ = χ → ConjVec i τ (χ • GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v)
      (χ • GlobalTheory.CoefModel.mapVV D.what₂.embLL (lamV D i) v) := by
    intro χ hχ
    unfold ConjVec
    rw [Submodule.coe_smul, GlobalTheory.CoefModel.mapVV_coe]
    ext m
    simp only [MvPolynomial.coeff_map, MvPolynomial.coeff_smul, smul_eq_mul, RingHom.coe_coe, map_mul, hχ]
    rw [hτ _ ⟨_, rfl⟩]
  have e3 := e2.trans (((map_smul c _ _).trans (congrArg (_ • ·) e1)).symm)
  exact ⟨_, _, key _ hχ, e3, e3⟩

/- English proof (translation)
Assume the negation of the conclusion as `hn`. Set `ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] ℂ` to `{ toFun := fun U => U v g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }`. Conclude with `hy (GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hR.models.HV i A.μ0).1 (hR.models.HV i A.μ0).2.1 (jVx R i A.μ0) (hR.models.jV i A.μ0) (LinearMap.ker (ev ∘ₗ R.thF i A.μ0)) (fun x => Classical.byContradiction fun h => hn ⟨x, h⟩) y)`.
-/
theorem exists_thF_jV_ne {F : Face D A} (hR : GlobalTheory.Hk3.Core R F) {i : Fin D.R.m} (v : (R.MW i (sg0 D A)).Vec) (g : GA D (Wc D i))
    (y : (R.HV i A.μ0).H) (hy : R.thF i A.μ0 y v g ≠ 0) : ∃ x, R.thF i A.μ0 (R.jV i A.μ0 x) v g ≠ 0 := by
  by_contra hn
  let ev : MMap (R.MW i (sg0 D A)) →ₗ[ℂ] ℂ :=
    { toFun := fun U => U v g, map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl }
  exact hy (GlobalTheory.SecLift.span_of_pres (R.B.L i A.μ0).pres (R.HV i A.μ0).e (hR.models.HV i A.μ0).1 (hR.models.HV i A.μ0).2.1
    (jVx R i A.μ0) (hR.models.jV i A.μ0) (LinearMap.ker (ev ∘ₗ R.thF i A.μ0))
    (fun x => Classical.byContradiction fun h => hn ⟨x, h⟩) y)

end GlobalTheory.PhaseOneOnto

/- English proof (translation)
Introduce `_ _ h3 D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O t j hV hR gramR c0R c0L hFT u hu hphs hcusp ph hph hrat`. Establish `hRF : GlobalTheory.NT.RayField` using `h3`. Establish `hs : sg0 D A3.A = D.what₂.embLL` using `sgAt_mk _ Rl.hv0`. Take `⟨gramR', c0R', c0L', hft', hbc⟩` from `hR.pins.2.lift.c0`. Take `⟨a, ⟨k, hk, hak⟩, hca⟩` from `GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity Rl.B Rl.pl _ Rl.Q (labLL D) _ _ gramR gramR' c0R c0R' c0L c0L' hFT hft' j`.

Establish `ha0 : a ≠ 0` using `fun e => by rw [e, zero_pow hk] at hak; exact zero_ne_one hak`. Establish `hb0 : D.what₂.embLL a ≠ 0` using `(map_ne_zero _).2 ha0`. Take `⟨ph', hph'⟩ : ∃ ph', ph' = (D.what₂.embLL a)⁻¹ * ph` from `⟨_, rfl⟩`. Establish `hph0 : ph' ≠ 0` using `hph' ▸ mul_ne_zero (inv_ne_zero hb0) fun e => by simp [e] at hph`. Establish `hrat' : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L' j) ph'` using `hph' ▸ GlobalTheory.PhaseOneOnto.isRatPhase_of_smul hb0 hca hrat`.

Establish `hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j` using `GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.ChartFree.chartIndep D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hR.core.lev hR.core.grp hR.core.fam hR.core.models hR.core.thP hR.tieIn hR.io O j hR.pins`. Establish `hone : (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) = fun _ => (1 : ℂ)` using `funext fun j => by rw [hphs, map_one]`. Establish `hphase : PhaseTie T Rl.toRealDat κ v₀ O (fun _ => 1) j` using `hone ▸ hR.phase`. Take `⟨cx, hcx⟩` from `NormRat.exists_extC (O j)`. Take `⟨v, x, h, g₀, hv, hx, hh, hg₀⟩` from `NormRat.exists_ser_ne_zero O hR.size hR.core hR.fw hR.io j hR.pins hrow0 hcusp cx hcx u hu`.

Take `⟨m, e, f, hexp, heL⟩` from `NormRat.expands_of_isRatPhase hRF YS O hR.size hR.laws hR.core hR.fw hR.tieIn hR.io hR.guard hR.galois hR.small.val hR.small.ray hR.small.roots hV hR.pins hR.frame hft' hbc hu hrat' cx hcx v hv x hx h hh`. Take `⟨ζ, ⟨nζ, hnζ, hζn⟩, hζ⟩` from `GlobalTheory.ConjRefTup.conjFun_base_root GlobalTheory.ChartFree.chartIndep D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O (fun _ => 1) hR.size hR.core hR.fin hR.fw hR.io hR.guard j hR.pins hphase cx hcx`. Establish `hζ0 : ζ ≠ 0` using `fun e => by rw [e, zero_pow hnζ.ne'] at hζn; exact zero_ne_one hζn`. Establish `hv0 : (fun ρ => ((u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ))) = v₀ j (sg0 D A3.A)` using `funext hu`. Take `⟨fw⟩` from `hR.fw`.

Establish `key : ∀ τ : ℂ ≃+* ℂ, (∀ z ∈ D.what₂.embLL.fieldRange, τ z = z) → τ ph' = ph'`. Introduce `τ hτ`. Establish `hτ0 : ∀ z ∈ (Formalism.L2.Host.embLL0 D).fieldRange, τ z = z`. Introduce and unpack `z ⟨y, rfl⟩`. Conclude with `hτ _ ⟨(y : D.what₂.LL), rfl⟩`.

Establish `hfix` using `NormRat.fixBase_of_fix hRF YS hR.laws hR.core hR.fw hR.tieIn hR.galois hR.small.val hR.small.ray hR.small.roots j τ hτ0`. Take `⟨y, y', hyy, hy⟩` from `GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hR.core hR.fw j Unit (fun _ => A3.A.μ0) (O j) hR.pins.2 cx hcx τ A3.A.μ0 A3.A.μ0 hfix (GlobalTheory.PhaseOneOnto.conjTup_base hR.core τ) h hh x x (NormRat.conjVec_self_of_rat j τ v hv x hx)`. Establish `hy1 : ∀ g, (Rl.thF j A3.A.μ0) y (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g` using `fun g => by have e := (hy u g).1; rwa [hv0] at e`. Establish `hy2 : ∀ g, (Rl.thF j A3.A.μ0) y' (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g` using `fun g => by have e := (hy u g).2; rwa [hv0] at e`. Establish `k1 : τ (ζ * ph'⁻¹) = ζ * ph'⁻¹`.

Use `NormRat.fixed_of_expands (O j) (κ j) τ (hζ τ hfix y y' hyy) (fun g => ?_) (fun g => ?_) hexp (fun k => hτ0 _ (heL k)) (g₀ := g₀) (mul_ne_zero hph0 hg₀)` and prove the remaining obligations. Rewrite using `[hy1 g, mul_one, mul_assoc ζ ph'⁻¹, inv_mul_cancel_left₀ hph0]`. Rewrite using `[hy2 g, mul_one, mul_assoc ζ ph'⁻¹, inv_mul_cancel_left₀ hph0]`. Take `⟨x₀, hx₀⟩` from `GlobalTheory.PhaseOneOnto.exists_thF_jV_ne hR.core (v₀ j (sg0 D A3.A)) g₀ y (by rw [hy1]; exact hg₀)`. Take `⟨n, b, f', hexp', hbL⟩` from `GlobalTheory.PhaseOneOnto.expands_thF_jV hR.core fw hR.unif O hR.pins (hphase hrow0) x₀`.

Establish `k2 : τ ζ = ζ` using `NormRat.fixed_of_expands (O j) (κ j) τ (hζ τ hfix _ _ (GlobalTheory.PhaseOneOnto.conjForm_jV hR.core O hR.pins cx hcx τ hfix hτ x₀)) (fun g => mul_assoc _ _ _) (fun g => mul_assoc _ _ _) hexp' (fun k => hτ _ (hbL k)) (g₀ := g₀) (mul_ne_zero one_ne_zero hx₀)`. Rewrite `k1` using `[map_mul, k2, map_inv₀]`. Conclude with `inv_injective (mul_left_cancel₀ hζ0 k1)`. Take `⟨c, hc⟩` from `GlobalTheory.FixedRoots.mem_of_forall_ringEquiv_fixed D.what₂.embLL.fieldRange ph' key`. Use `⟨a * c, ?_⟩` and prove the remaining obligations.

Rewrite using `[hs, map_mul, hc, hph', ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]`.
-/
theorem GlobalTheory.PhaseOneOnto.phase_mem_coefField : GlobalTheory.Published.CuspRapidDecay → GlobalTheory.Published.GlobalArtinReciprocity → GlobalTheory.Published.RayClassFieldSt →
  ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m)
    (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd)
    (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A)
    (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec)
    (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)) (t : D.ntw.Tw) (j : Fin D.R.m)
    (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), RatHyp T Rl F κ v₀ O t j hV →
  ∀ gramR c0R c0L, Bridge.FamTie Rl.B Rl.pl (Rl.Sb : Set (Pl D.host.E)) Rl.Q (labLL D)
      (fun τ => Bridge.lamRdef (Ptw D) τ) (fun i τ => Bridge.lamLdef (Vc D i).rank ((i : ℕ) + 1) τ) gramR c0R c0L →
  ∀ u : ∀ τ, lowT (Rl.MW j (sg0 D A3.A)) τ, (∀ τ, (u τ : (Rl.MW j (sg0 D A3.A)).sm τ) = v₀ j (sg0 D A3.A) τ) →
  (∀ k, Rl.phs k = 1) → T.cuspA ((j : ℕ) + 1) (wtA (κ j)) (κ j).n ≠ ⊥ →
  ∀ ph : ℂ, ‖ph‖ = 1 → IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L j) ph → ∃ c : D.what₂.LL, sg0 D A3.A c = ph := by
  intro _ _ h3 D Γ _ _ Pl0 I0 T0 A3 T _ Rl cG S YS F κ v₀ O t j hV hR gramR c0R c0L hFT u hu hphs hcusp ph hph hrat
  have hRF : GlobalTheory.NT.RayField := h3
  have hs : sg0 D A3.A = D.what₂.embLL := sgAt_mk _ Rl.hv0

  obtain ⟨gramR', c0R', c0L', hft', hbc⟩ := hR.pins.2.lift.c0
  obtain ⟨a, ⟨k, hk, hak⟩, hca⟩ := GlobalTheory.T.definiteSideRealisations_coefMap_differ_rootOfUnity Rl.B Rl.pl _ Rl.Q (labLL D) _ _ gramR gramR' c0R c0R' c0L c0L' hFT hft' j
  have ha0 : a ≠ 0 := fun e => by rw [e, zero_pow hk] at hak; exact zero_ne_one hak
  have hb0 : D.what₂.embLL a ≠ 0 := (map_ne_zero _).2 ha0
  obtain ⟨ph', hph'⟩ : ∃ ph', ph' = (D.what₂.embLL a)⁻¹ * ph := ⟨_, rfl⟩
  have hph0 : ph' ≠ 0 := hph' ▸ mul_ne_zero (inv_ne_zero hb0) fun e => by simp [e] at hph
  have hrat' : IsRatPhase T Rl.toRealDat j hV (κ j) u (c0L' j) ph' :=
    hph' ▸ GlobalTheory.PhaseOneOnto.isRatPhase_of_smul hb0 hca hrat

  have hrow0 : OneMapRow0 T Rl.toRealDat κ v₀ O j :=
    GlobalTheory.OneMapTies.oneMapRow0_of_ties_base_clauses GlobalTheory.ChartFree.chartIndep D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀
      hR.core.lev hR.core.grp hR.core.fam hR.core.models hR.core.thP hR.tieIn hR.io O j hR.pins
  have hone : (fun j => cj (twAt D.what₂.embLL A3.A.v0) (Rl.phs j)) = fun _ => (1 : ℂ) := funext fun j => by rw [hphs, map_one]
  have hphase : PhaseTie T Rl.toRealDat κ v₀ O (fun _ => 1) j := hone ▸ hR.phase

  obtain ⟨cx, hcx⟩ := NormRat.exists_extC (O j)
  obtain ⟨v, x, h, g₀, hv, hx, hh, hg₀⟩ := NormRat.exists_ser_ne_zero O hR.size hR.core hR.fw hR.io j hR.pins hrow0 hcusp cx hcx u hu
  obtain ⟨m, e, f, hexp, heL⟩ := NormRat.expands_of_isRatPhase hRF YS O hR.size hR.laws hR.core hR.fw hR.tieIn hR.io hR.guard
    hR.galois hR.small.val hR.small.ray hR.small.roots hV hR.pins hR.frame hft' hbc hu hrat' cx hcx v hv x hx h hh

  obtain ⟨ζ, ⟨nζ, hnζ, hζn⟩, hζ⟩ := GlobalTheory.ConjRefTup.conjFun_base_root GlobalTheory.ChartFree.chartIndep D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ O
    (fun _ => 1) hR.size hR.core hR.fin hR.fw hR.io hR.guard j hR.pins hphase cx hcx
  have hζ0 : ζ ≠ 0 := fun e => by rw [e, zero_pow hnζ.ne'] at hζn; exact zero_ne_one hζn
  have hv0 : (fun ρ => ((u ρ : (Rl.MW j (sg0 D A3.A)).sm ρ))) = v₀ j (sg0 D A3.A) := funext hu
  obtain ⟨fw⟩ := hR.fw
  have key : ∀ τ : ℂ ≃+* ℂ, (∀ z ∈ D.what₂.embLL.fieldRange, τ z = z) → τ ph' = ph' := by
    intro τ hτ
    have hτ0 : ∀ z ∈ (Formalism.L2.Host.embLL0 D).fieldRange, τ z = z := by
      rintro z ⟨y, rfl⟩
      exact hτ _ ⟨(y : D.what₂.LL), rfl⟩
    have hfix := NormRat.fixBase_of_fix hRF YS hR.laws hR.core hR.fw hR.tieIn hR.galois hR.small.val hR.small.ray
      hR.small.roots j τ hτ0
    obtain ⟨y, y', hyy, hy⟩ := GlobalTheory.ConjTwist.exists_conjForm_thF_eq_ser D Γ Pl0 T0 A3.A T Rl.toRealDat F κ v₀ hR.core hR.fw j Unit
      (fun _ => A3.A.μ0) (O j) hR.pins.2 cx hcx τ A3.A.μ0 A3.A.μ0 hfix (GlobalTheory.PhaseOneOnto.conjTup_base hR.core τ) h hh x x
      (NormRat.conjVec_self_of_rat j τ v hv x hx)
    have hy1 : ∀ g, (Rl.thF j A3.A.μ0) y (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).1; rwa [hv0] at e
    have hy2 : ∀ g, (Rl.thF j A3.A.μ0) y' (v₀ j (sg0 D A3.A)) g = ser Rl.toRealDat j A3.A.μ0 (Rl.vP j A3.A.μ0) u h (cx x) g :=
      fun g => by have e := (hy u g).2; rwa [hv0] at e
    have k1 : τ (ζ * ph'⁻¹) = ζ * ph'⁻¹ := by
      refine NormRat.fixed_of_expands (O j) (κ j) τ (hζ τ hfix y y' hyy) (fun g => ?_) (fun g => ?_) hexp
        (fun k => hτ0 _ (heL k)) (g₀ := g₀) (mul_ne_zero hph0 hg₀)
      · rw [hy1 g, mul_one, mul_assoc ζ ph'⁻¹, inv_mul_cancel_left₀ hph0]
      · rw [hy2 g, mul_one, mul_assoc ζ ph'⁻¹, inv_mul_cancel_left₀ hph0]
    obtain ⟨x₀, hx₀⟩ := GlobalTheory.PhaseOneOnto.exists_thF_jV_ne hR.core (v₀ j (sg0 D A3.A)) g₀ y (by rw [hy1]; exact hg₀)
    obtain ⟨n, b, f', hexp', hbL⟩ := GlobalTheory.PhaseOneOnto.expands_thF_jV hR.core fw hR.unif O hR.pins (hphase hrow0) x₀
    have k2 : τ ζ = ζ :=
      NormRat.fixed_of_expands (O j) (κ j) τ
        (hζ τ hfix _ _ (GlobalTheory.PhaseOneOnto.conjForm_jV hR.core O hR.pins cx hcx τ hfix hτ x₀))
        (fun g => mul_assoc _ _ _) (fun g => mul_assoc _ _ _) hexp' (fun k => hτ _ (hbL k)) (g₀ := g₀)
        (mul_ne_zero one_ne_zero hx₀)
    rw [map_mul, k2, map_inv₀] at k1
    exact inv_injective (mul_left_cancel₀ hζ0 k1)
  obtain ⟨c, hc⟩ := GlobalTheory.FixedRoots.mem_of_forall_ringEquiv_fixed D.what₂.embLL.fieldRange ph' key
  refine ⟨a * c, ?_⟩
  rw [hs, map_mul, hc, hph', ← mul_assoc, mul_inv_cancel₀ hb0, one_mul]
