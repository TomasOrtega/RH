import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsInertTop
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeStableUnderAction
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaIntegrandIntegrable
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryAdelicCharacterTrivialRatAndSplit
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsPrincipalLevelSubgroupOpen
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.LatHatOpenAndContinuous
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.CompletedLatticeEqAdelicCompletionAndGram
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.NonarchimedeanGroupOfIsCompactIsOpen
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.PrincipalLevelMulArchimedeanMemNhds
open NumberField Matrix Complex IsDedekindDomain
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Dict GlobalTheory.AdTh GlobalTheory.ClsVal
open ReciprocityTheory.ChartRestriction.G.Geo.Tor hiding Level Host
open GlobalTheory.SW hiding Level IsSB
open Formalism.BasicNotions Formalism.MainNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.L2.Pj
open GlobalTheory.ExportSeries (Base Twist Weight PairRep GLR detChar detFam fockGL harm harmLat IsCoefRing finPt series idem)
open scoped TensorProduct Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.SingleDatum
set_option synthInstance.maxHeartbeats 400000

open scoped ComplexOrder Topology
noncomputable section
namespace GlobalTheory.SmoothVac
variable {D : D7}

/- English proof (translation)
Establish `h1 : Formalism.L2.Theta.mt W 1 = 1` using `by simp [Formalism.L2.Theta.mt]`. Rewrite using `[h1, compAt, Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]`.
-/
theorem comm_compAt_one (W : HSp D) (θ : InfFam D) (τ : D.what₂.Tau) (s : Matrix (Fin W.rank) (Fin W.rank) ℂ) :
    s * compAt θ τ (Formalism.L2.Theta.mt W 1) = compAt θ τ (Formalism.L2.Theta.mt W 1) * s := by
  have h1 : Formalism.L2.Theta.mt W 1 = 1 := by simp [Formalism.L2.Theta.mt]
  rw [h1, compAt, Matrix.map_one _ (by simp) (by simp), Matrix.one_mul, Matrix.mul_one]

/- English proof (translation)
Establish `: gramAt D V τ = 1` using `by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]`. Rewrite using `[this]`. Conclude with `⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩`.
-/
theorem isCartanInv_one (V : HSp D) (hV : V.gram = 1) (τ : D.what₂.Tau) : IsCartanInv (gramAt D V τ) 1 := by
  have : gramAt D V τ = 1 := by rw [gramAt, hV, Matrix.map_one _ (map_zero _) (map_one _)]
  rw [this]
  exact ⟨by simp, by simp, by simpa using Matrix.PosDef.one⟩

/- English proof (translation)
Assume the negation of the conclusion as `h`. Use `push_neg at h`. Take `⟨⟨p, hp⟩, hn⟩` from `hf.2.norm`. Use `hn p hp` as an intermediate fact. Establish `h0 : f = 0` using `funext h`.

Rewrite `this` using `[h0]`. Simplify using `[nrm2] at this`.
-/
theorem exists_ne_zero_of_isVacO {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D}
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    {LS : Set (Fin S.rank → D.host.E)} {LT : Set (Fin T.rank → D.host.E)} {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT LS LT f) : ∃ w, f w ≠ 0 := by
  by_contra h
  push_neg at h
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have := hn p hp
  have h0 : f = 0 := funext h
  rw [h0] at this
  simp [nrm2] at this

/- English proof (translation)
Introduce `z hz`. Take `⟨y, hy, e⟩` from `h z hz`. Conclude with `⟨b • y, nsmul_mem hy b, by rw [e, mul_smul]⟩`.
-/
theorem finCong_of_mul_left {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V a k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨b • y, nsmul_mem hy b, by rw [e, mul_smul]⟩

/- English proof (translation)
Introduce `z hz`. Take `⟨y, hy, e⟩` from `h z hz`. Conclude with `⟨a • y, nsmul_mem hy a, by rw [e, mul_comm, mul_smul]⟩`.
-/
theorem finCong_of_mul_right {a b : ℕ} {V : HSp D} {k : GA D V} (h : GlobalTheory.Member.FinCong V (a * b) k) :
    GlobalTheory.Member.FinCong V b k := by
  intro z hz
  obtain ⟨y, hy, e⟩ := h z hz
  exact ⟨a • y, nsmul_mem hy a, by rw [e, mul_comm, mul_smul]⟩

/- English proof (translation)
Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Use `filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β ∅ (continuous_subtype_val (p := fun x => x ∈ Bridge.Gf V)) rfl] with x hh`.

Conclude with `hh.1`.
-/
theorem isOpen_comap_St (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D)) :
    IsOpen (((Formalism.L2.DIV.St β).comap ((Formalism.UG.bc (Lev.swapAE D)).comp (Bridge.Gf V).subtype) :
      Subgroup (Bridge.Gf V)) : Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  filter_upwards [GlobalTheory.ThetaIntegrand.eventually_princ_mat β ∅ (continuous_subtype_val (p := fun x => x ∈ Bridge.Gf V)) rfl]
    with x hh
  exact hh.1

set_option maxHeartbeats 1000000 in

/- English proof (translation)
Use `haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _`. Use `haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩`. Use `haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _`. Use `Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_` and prove the remaining obligations. Take `⟨h1, -, h3, -⟩` from `GlobalTheory.Member.latHat_eq_hat_and_gram D V`.

Take `⟨hop, -, -⟩` from `GlobalTheory.Member.latHat_open_and_continuous D V`. Establish `hc : Continuous fun x : Bridge.Gf V => ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E))` using `Units.continuous_val.comp continuous_subtype_val`. Take `⟨S, hS⟩` from `h3.restrictScalars (R := ℤ)`. Establish `hLS : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ⊆ (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E))`. Introduce `x hx`.

Establish `hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E))` using `by rw [hS]; exact hx`. Rewrite using `[← Submodule.span_int_eq_addSubgroupClosure]`. Conclude with `hx'`. Establish `hU : (⋂ x ∈ S, {k : Bridge.Gf V | ∃ y ∈ latHat V, ((k : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) : Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ GlobalTheory.AdLat.fv D.host.F x - GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : Bridge.Gf V …`. Use `(Filter.biInter_finset_mem S).2 fun x _ => ?_` and prove the remaining obligations.

Establish `hcx` using `GlobalTheory.Member.PrincLevel.continuous_mulVec_sub hc (GlobalTheory.AdLat.fv D.host.F x)`. Use `((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩` and prove the remaining obligations. Use `Filter.mem_of_superset hU fun x hx => ?_` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq] at hx`. Take `⟨g, hg⟩` from `x.2`.

Use `⟨GlobalTheory.LevelNbhd.finPartG V g, ⟨GlobalTheory.LevelNbhd.finPartG_mem_GfC V g, ?_⟩, ?_⟩` and prove the remaining obligations. Unfold `GlobalTheory.Member.FinCong`. Rewrite using `[GlobalTheory.LevelNbhd.finHom_finPartG, hg]`. Rewrite `hx`, the goal using `[h1]`. Conclude with `GlobalTheory.Member.PrincLevel.cong_of_gen _ _ hLS _ N fun s hs => hx s hs`.

Conclude with `Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, GlobalTheory.LevelNbhd.finHom_finPartG, hg])`.
-/
theorem isOpen_map_levelGroup (V : HSp D) {N : ℕ} (hN : 0 < N) :
    IsOpen (((GlobalTheory.Member.PrincLevel.levelGroup V N).map (finHom V).rangeRestrict : Subgroup (Bridge.Gf V)) :
      Set (Bridge.Gf V)) := by
  haveI : Module.Finite D.host.F D.host.E := Module.Finite.of_restrictScalars_finite ℚ _ _
  haveI : IsModuleTopology (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) := ⟨rfl⟩
  haveI : IsTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F ⊗[D.host.F] D.host.E) :=
    IsModuleTopology.isTopologicalRing (GlobalTheoryTheory.GenusMassVolumes.Af D.host.F) _
  refine Subgroup.isOpen_of_mem_nhds _ (g := 1) ?_
  obtain ⟨h1, -, h3, -⟩ := GlobalTheory.Member.latHat_eq_hat_and_gram D V
  obtain ⟨hop, -, -⟩ := GlobalTheory.Member.latHat_open_and_continuous D V
  have hc : Continuous fun x : Bridge.Gf V => ((x : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
      Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :=
    Units.continuous_val.comp continuous_subtype_val
  obtain ⟨S, hS⟩ := h3.restrictScalars (R := ℤ)
  have hLS : (GlobalTheory.Member.latC V : Set (Fin V.rank → D.host.E)) ⊆
      (AddSubgroup.closure (S : Set (Fin V.rank → D.host.E)) : AddSubgroup (Fin V.rank → D.host.E)) := by
    intro x hx
    have hx' : x ∈ Submodule.span ℤ (S : Set (Fin V.rank → D.host.E)) := by rw [hS]; exact hx
    rw [← Submodule.span_int_eq_addSubgroupClosure]
    exact hx'
  have hU : (⋂ x ∈ S, {k : Bridge.Gf V | ∃ y ∈ latHat V,
      ((k : GL (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) :
        Matrix (Fin V.rank) (Fin V.rank) (Af D.host.F ⊗[D.host.F] D.host.E)) *ᵥ GlobalTheory.AdLat.fv D.host.F x -
        GlobalTheory.AdLat.fv D.host.F x = N • y}) ∈ 𝓝 (1 : Bridge.Gf V) := by
    refine (Filter.biInter_finset_mem S).2 fun x _ => ?_
    have hcx := GlobalTheory.Member.PrincLevel.continuous_mulVec_sub hc (GlobalTheory.AdLat.fv D.host.F x)
    refine ((hop N hN).preimage hcx).mem_nhds ⟨0, zero_mem _, by simp⟩
  refine Filter.mem_of_superset hU fun x hx => ?_
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hx
  obtain ⟨g, hg⟩ := x.2
  refine ⟨GlobalTheory.LevelNbhd.finPartG V g, ⟨GlobalTheory.LevelNbhd.finPartG_mem_GfC V g, ?_⟩, ?_⟩
  · unfold GlobalTheory.Member.FinCong
    rw [GlobalTheory.LevelNbhd.finHom_finPartG, hg]
    rw [h1] at hx ⊢
    exact GlobalTheory.Member.PrincLevel.cong_of_gen _ _ hLS _ N fun s hs => hx s hs
  · exact Subtype.ext (by rw [MonoidHom.coe_rangeRestrict, GlobalTheory.LevelNbhd.finHom_finPartG, hg])

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]`. Consider the case `succ m ih`. Establish `e : ((k ^ (m + 1), (1 : GA D W)) : GA D V × GA D W) = (k ^ m, 1) * (k, 1)`.

Rewrite using `[pow_succ, Prod.mk_mul_mk, mul_one]`. Rewrite using `[e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]`.
-/
theorem om_pow_eq {V W : HSp D} (ω : PairRep V W) (k : GA D V) (f : WO V W → ℂ) (c : ℂ) (hc : ω (k, 1) f = c • f) :
    ∀ m : ℕ, ω (k ^ m, 1) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, Prod.mk_one_one, map_one, Module.End.one_apply, one_smul]
  | succ m ih =>
    have e : ((k ^ (m + 1), (1 : GA D W)) : GA D V × GA D W) = (k ^ m, 1) * (k, 1) := by
      rw [pow_succ, Prod.mk_mul_mk, mul_one]
    rw [e, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

end GlobalTheory.SmoothVac
