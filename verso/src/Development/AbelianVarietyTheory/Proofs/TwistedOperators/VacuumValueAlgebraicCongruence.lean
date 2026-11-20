import Mathlib
import Development.AbelianVarietyTheory.Definitions.TwistedInnerProducts.TwistPlacesOffPrimeQZero
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.BottomExistsIntegrable
import Development.AbelianVarietyTheory.Definitions.Divisors.DiscreteSeriesHermitianUnique
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.NormSmall
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.DictAt
import Development.AbelianVarietyTheory.Statements.HeckeThetaIntegrals.ThetaIntegralsAgree
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.WeilTensorModels
import Development.AbelianVarietyTheory.BlockTheory.TwistedDiscreteSeries.CuspAlongSmoothRows
import Development.AbelianVarietyTheory.BlockTheory.DivisorBase.ToricSymbols
import Development.AbelianVarietyTheory.Definitions.Foundations.NormSumPairRankZeroOfCurveCoordNorm
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.HeisOSumSmul
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ExistsRepSuppSplit
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.SqNormIntegralFundamentalDomainEqL2NormSq
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.ApplyAddInfRat
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsNeZeroOfIsVacO
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.LatticeStableUnderAction
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.CompAtMtOfMemGfC
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.L2.DIV
open IsDedekindDomain NumberField GlobalTheory.ChiGrid GlobalTheory.FunObj GlobalTheory.RowTest GlobalTheory.RowClaim
open Formalism.L2.Host (HChar)
open GlobalTheory.IndefiniteRowSideFullHecke.UnitCharTriangle (Tri)
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.RowEx MeasureTheory

noncomputable section

namespace GlobalTheory.LevelVac

variable {D : D7}

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in
open GlobalTheory.VacUnique GlobalTheory.FockCompare in

/- English proof (translation)
Establish `hψ` using `hf.1`. Establish `hθ : IsInfFam θ` using `hf.2.inf`. Establish `hth : IsThetaFunO ψ S T f'` using `hf'.2.theta`. Take `⟨σ, h⟩` from `GlobalTheory.RealLineAt.exists_inverse_chart hθ`. Take `⟨h1, h2, h3⟩` from `GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT`.

Establish `hden` using `GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1`. Establish `hlat` using `hf.2.lat`. Establish `hlat'` using `hf'.2.lat`. Establish `hinf` using `fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) fun _ => True`. Generalize the expression as in `latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ at h1 h2 h3 hden hlat hlat' hinf`.

Use `choose ε hε1 hε2 using h3 f hlat`. Establish `det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' → IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' → (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g`. Introduce `g g' c hg hg' hl hl' hz`. Use function extensionality and compare the values at `w`. Take `⟨γ, z, u, hu, rfl⟩` from `exists_decomp h h2 w`.

Rewrite using `[Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl), apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨⟨p, hp⟩, hn⟩` from `hf.2.norm`. Establish `n1 : nrm2 p.1 p.2 f = 1` using `hn p hp`. Establish `hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0`.

Introduce `h0`. Establish `e` using `det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z`. Rewrite `n1` using `[e]`. Simplify using `[nrm2] at n1`. Take `⟨j1, j2, j3, j4⟩` from `GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT`.

Establish `hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤`. Use `span_piW_ratW_eq_top D θ σ h T S` as an intermediate fact. Simplify `this` using `only [piW_ratW hθ]`. Establish `a1` using `GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock`. Establish `a2` using `GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hf'.2.fock`.

Set `c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ` to `fun v => if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1`. Establish `hc : ∀ v, ‖c v‖ = 1` using `fun v => by`. Simplify using `only [c]`. Use `split_ifs with hv`. Rewrite using `[norm_mul, hψ.1.2.1]`.

Apply the tactic sequence `rcases hε1 _ hv with e | e <;> rw [e] <;> simp`. Conclude with `norm_one`. Establish `law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g → ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) = c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z)`. Introduce `g hg hl v hv z`. Establish `hv' : finRat S T (-v) ∈ Λ` using `(Λ.comap (finRat S T)).neg_mem hv`.

Rewrite using `[apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]`. Simplify using `only [c, dif_pos hv']`. Establish `hli` using `GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E) (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T)) (fun x => by`. Take `⟨N, hN, hx⟩` from `hden x`. Conclude with `⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)`.

Use the proof step `(GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc`. Use the proof step `![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]`. Use the proof step `(fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])`. Use the proof step `(fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])`. Rewrite `hli` using `[LinearIndependent.pair_iff' hne]`.

Use `push_neg at hli`. Take `⟨a, ha⟩` from `hli`. Conclude with `⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩`.
-/
theorem vac_eq_smul {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D}
    {S T : HSp D} {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ}
    {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT) {f f' : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) (hf' : IsVacO ψ θ S T sS sT ΛS ΛT f') : ∃ a : ℂ, f' = a • f := by
  classical
  have hψ := hf.1
  have hθ : IsInfFam θ := hf.2.inf
  have hth : IsThetaFunO ψ S T f' := hf'.2.theta
  obtain ⟨σ, h⟩ := GlobalTheory.RealLineAt.exists_inverse_chart hθ
  obtain ⟨h1, h2, h3⟩ := GlobalTheory.T.self_dual_lattice_pairing_dual D ψ S T ΛS ΛT hψ hΛS hΛT
  have hden := GlobalTheory.T.scaled_finite_matrix_mem_lattice D S T ΛS ΛT hΛS.1 hΛT.1
  have hlat := hf.2.lat
  have hlat' := hf'.2.lat
  have hinf := fun u => latO_inf (u := u) S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E))
    fun _ => True
  generalize latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) = Λ
    at h1 h2 h3 hden hlat hlat' hinf
  choose ε hε1 hε2 using h3 f hlat
  have det : ∀ (g g' : WO S T → ℂ) (c : ℂ), IsThetaFunO ψ S T g → IsThetaFunO ψ S T g' →
      IsLatVac (heisO ψ S T) Λ g → IsLatVac (heisO ψ S T) Λ g' →
      (∀ z, g' (iotaW σ T S z) = c * g (iotaW σ T S z)) → g' = c • g := by
    intro g g' c hg hg' hl hl' hz
    funext w
    obtain ⟨γ, z, u, hu, rfl⟩ := exists_decomp h h2 w
    rw [Pi.smul_apply, smul_eq_mul, hg.quasi, hg'.quasi, apply_real_add h hψ (hinf u hu) (hε2 u hu g hl),
      apply_real_add h hψ (hinf u hu) (hε2 u hu g' hl'), hz]
    ring
  obtain ⟨⟨p, hp⟩, hn⟩ := hf.2.norm
  have n1 : nrm2 p.1 p.2 f = 1 := hn p hp
  have hne : (fun z : RW T S => f (iotaW σ T S z)) ≠ 0 := by
    intro h0
    have e := det f f 0 hf.2.theta hf.2.theta hlat hlat fun z => by rw [zero_mul]; exact congrFun h0 z
    rw [e] at n1
    simp [nrm2] at n1
  obtain ⟨j1, j2, j3, j4⟩ := GlobalTheory.T.realSymplecticForm_alternating_invariant_definite D S T sS sT hS hT
  have hsp : Submodule.span ℝ (Set.range (infRat S T)) = ⊤ := by
    have := span_piW_ratW_eq_top D θ σ h T S
    simpa only [piW_ratW hθ] using this
  have a1 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f hf.2.theta hf.2.fock
  have a2 := GlobalTheory.T.fockVacuum_annihilation_equation_real_coordinates D θ σ h ψ hψ S T sS sT f' hth hf'.2.fock
  let c : Matrix (Fin T.rank) (Fin S.rank) D.host.E → ℂ := fun v =>
    if hv : finRat S T (-v) ∈ Λ then ψ (-symplOH S T (ratW T S v) (finRat S T (-v))) * ε _ hv else 1
  have hc : ∀ v, ‖c v‖ = 1 := fun v => by
    simp only [c]
    split_ifs with hv
    · rw [norm_mul, hψ.1.2.1]
      rcases hε1 _ hv with e | e <;> rw [e] <;> simp
    · exact norm_one
  have law : ∀ g : WO S T → ℂ, IsThetaFunO ψ S T g → IsLatVac (heisO ψ S T) Λ g →
      ∀ v ∈ Λ.comap (finRat S T), ∀ z, g (iotaW σ T S (z + infRat S T v)) =
        c v * Complex.exp (-(Real.pi * Complex.I) * (omO S T z (infRat S T v) : ℂ)) * g (iotaW σ T S z) := by
    intro g hg hl v hv z
    have hv' : finRat S T (-v) ∈ Λ := (Λ.comap (finRat S T)).neg_mem hv
    rw [apply_add_infRat h hψ hg v (hε2 _ hv' g hl) z, ← j2]
    simp only [c, dif_pos hv']
  have hli := GlobalTheory.T.not_linearIndependent_alt (RW T S) (jO S T sS sT) (omO S T) j1 j2 j3 j4 (Matrix (Fin T.rank) (Fin S.rank) D.host.E)
    (infRat S T) (infRat_injective S T) hsp (Λ.comap (finRat S T))
    (fun x => by
      obtain ⟨N, hN, hx⟩ := hden x
      exact ⟨N, hN, by rwa [AddSubgroup.mem_comap, AddMonoidHom.map_nsmul]⟩)
    (GlobalTheory.T.rationalPoints_finitePart_selfDual_lattice_iff D S T ψ Λ hψ hinf h1 h2 hden) c hc
    ![fun z => f (iotaW σ T S z), fun z => f' (iotaW σ T S z)]
    (fun k => by fin_cases k; exacts [a1.1, a2.1]) (fun k => by fin_cases k; exacts [a1.2, a2.2])
    (fun k => by fin_cases k; exacts [law f hf.2.theta hlat, law f' hth hlat'])
  rw [LinearIndependent.pair_iff' hne] at hli
  push_neg at hli
  obtain ⟨a, ha⟩ := hli
  exact ⟨a, det f f' a hf.2.theta hth hlat hlat' fun z => (congrFun ha z).symm⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 800000 in

/- English proof (translation)
Take `⟨N, hN, hK⟩` from `GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (GlobalTheory.SmoothVac.isOpen_comap_St V β)`. Use `⟨N, hN, fun k hk => ?_⟩` and prove the remaining obligations. Establish `hst : Formalism.UG.bc (Lev.swapAE D) (GlobalTheory.ExportSeries.finPt V k).1 ∈ Formalism.L2.DIV.St β` using `hK k hk`. Take `⟨y, hy⟩` from `hst`. Establish `hfin : ((Formalism.UG.bc (Lev.swapAE D) (GlobalTheory.ExportSeries.finPt V k).1 : GL (Fin V.rank) (Lev.EAf D)) : Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) = (Formalism.L2.Theta.mt V k).map (toEAf D)` using `rfl`.

Use `⟨β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y, GlobalTheory.LatKeep.isFrame_mul_intGL hβ y, ?_⟩` and prove the remaining obligations. Rewrite using `[← hfin, ← hy]`. Simplify using `[Formalism.L2.DIV.frGL, MulAut.conj_apply, Matrix.mul_assoc]`.
-/
theorem exists_level_frame (V : HSp D) (β : GL (Fin V.rank) (Lev.EAf D))
    {Λ : Submodule (𝓞 D.host.E) (Fin V.rank → D.host.E)} (hβ : Formalism.L2.DIV.IsFrame β Λ) :
    ∃ N : ℕ, 0 < N ∧ ∀ k : GA D V, GlobalTheory.Member.FinCong V N k → ∃ β' : GL (Fin V.rank) (Lev.EAf D),
      Formalism.L2.DIV.IsFrame β' Λ ∧ β'.val = (Formalism.L2.Theta.mt V k).map (toEAf D) * β.val := by
  obtain ⟨N, hN, hK⟩ := GlobalTheory.SplitRepsOpen.exists_finCong_le D V _ (GlobalTheory.SmoothVac.isOpen_comap_St V β)
  refine ⟨N, hN, fun k hk => ?_⟩
  have hst : Formalism.UG.bc (Lev.swapAE D) (GlobalTheory.ExportSeries.finPt V k).1 ∈ Formalism.L2.DIV.St β := hK k hk
  obtain ⟨y, hy⟩ := hst
  have hfin : ((Formalism.UG.bc (Lev.swapAE D) (GlobalTheory.ExportSeries.finPt V k).1 : GL (Fin V.rank) (Lev.EAf D)) :
      Matrix (Fin V.rank) (Fin V.rank) (Lev.EAf D)) = (Formalism.L2.Theta.mt V k).map (toEAf D) := rfl
  refine ⟨β * Formalism.L2.DIV.intGL D.host.F D.host.E V.rank y, GlobalTheory.LatKeep.isFrame_mul_intGL hβ y, ?_⟩
  rw [← hfin, ← hy]
  simp [Formalism.L2.DIV.frGL, MulAut.conj_apply, Matrix.mul_assoc]

/- English proof (translation)
Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]`. Consider the case `succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]`.
-/
theorem om_pow_eq {G M : Type} [Monoid G] [AddCommGroup M] [Module ℂ M] (ω : G →* Module.End ℂ M) (k : G) (f : M) (c : ℂ)
    (hc : ω k f = c • f) : ∀ m : ℕ, ω (k ^ m) f = c ^ m • f := by
  intro m
  induction m with
  | zero => rw [pow_zero, pow_zero, map_one, Module.End.one_apply, one_smul]
  | succ m ih => rw [pow_succ, map_mul, Module.End.mul_apply, hc, map_smul, ih, smul_smul, pow_succ, mul_comm]

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Establish `hθ : IsInfFam θ` using `hf.2.inf`. Take `⟨N₁, hN₁, hK₁⟩` from `exists_level_frame S βS hβS`. Take `⟨N₂, hN₂, hK₂⟩` from `exists_level_frame T βT hβT`. Establish `hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (N₁ * N₂) k → GlobalTheory.Member.FinCong T (N₁ * N₂) k' → ∃ c : ℂ, om (k, k') f = c • f`. Introduce `k hk k' hk' hc hc'`.

Establish `keep : ∀ g g', GlobalTheory.Member.FinCong S (N₁ * N₂) g → GlobalTheory.Member.FinCong T (N₁ * N₂) g' → ∀ u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True), actO S T g g' u ∈ latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (F …`. Introduce `g g' hg hg' u hu`. Take `⟨b, hb, e⟩` from `hK₁ g (GlobalTheory.SmoothVac.finCong_of_mul_left hg)`. Take `⟨b', hb', e'⟩` from `hK₂ g' (GlobalTheory.SmoothVac.finCong_of_mul_right hg')`. Conclude with `GlobalTheory.AdelicLatMove.actO_mem_latO S T g g' ΛS ΛS ΛT ΛT βS b βT b' hβS hb hβT hb' e e' u hu`.

Use `vac_eq_smul hS hT hΛS hΛT hf (GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ k k' (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk, Matrix.mul_one, Matrix.one_mul]) (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_ …` and prove the remaining obligations. Use `GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u` as an intermediate fact. Rewrite `this` using `[inv_inv, inv_inv]`. Conclude with `this.symm`. Introduce and unpack `⟨u₀, hu₀, rfl⟩`.

Conclude with `keep _ _ hc hc' u₀ hu₀`. Take `⟨w₀, hw₀⟩` from `GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hf`. Establish `hcont : Continuous fun p : GA D S × GA D T => om p f w₀` using `hW.om_cont _ hf.2.theta w₀`. Establish `key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (N₁ * N₂ * n.factorial) k → GlobalTheory.Member.FinCong T (N₁ * N₂ * n.factorial) k' → om (k, k') f = f`. Assume the negation of the conclusion as `hne`.

Use `push_neg at hne`. Use `choose k hk k' hk' hkc hkc' hkne using hne`. Establish `hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om ((k n, k' n) ^ m) f = c • f ∧ ¬ ‖c - 1‖ ≤ 1 / 2`. Introduce `n`. Take `⟨c, hc⟩` from `hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n)) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))`.

Establish `hc1 : c ≠ 1`. Introduce and unpack `rfl`. Conclude with `hkne n (by rw [hc, one_smul])`. Assume the negation of the conclusion as `h`. Simplify using `only [not_exists, not_and, not_not] at h`.

Conclude with `hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m => h m (c ^ m) (om_pow_eq om _ _ c hc m))`. Use `choose m c hmc hc using hpow`. Establish `hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (N₁ * N₂ * n.factorial)` using `fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (N₁ * N₂ * n.factorial) from ⟨hk n, hkc n⟩) _`. Establish `hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (N₁ * N₂ * n.factorial)` using `fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (N₁ * N₂ * n.factorial) from ⟨hk' n, hkc' n⟩) _`. Establish `ht` using `GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1) (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)`.

Establish `ht'` using `GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1) (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2)`. Establish `h2` using `(hcont.tendsto (1, 1)).comp (ht.prodMk_nhds ht')`. Establish `e1 : om ((1 : GA D S), (1 : GA D T)) f w₀ = f w₀` using `by show om 1 f w₀ = _`. Rewrite using `[map_one]`. Both sides reduce to the same expression.

Rewrite `h2` using `[Function.comp_def, e1]`. Establish `hpos : 0 < ‖f w₀‖ / 2` using `half_pos (norm_pos_iff.2 hw₀)`. Take `⟨n, hn⟩` from `(h2.eventually (Metric.ball_mem_nhds _ hpos)).exists`. Establish `e2 : om (k n ^ m n, k' n ^ m n) f = c n • f` using `hmc n`. Rewrite `hn` using `[e2, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul]`.

Use `norm_pos_iff.2 hw₀` as an intermediate fact. Conclude with `hc n (by nlinarith)`. Take `⟨n, hn⟩` from `key`. Conclude with `⟨_, mul_pos (mul_pos hN₁ hN₂) n.factorial_pos, hn⟩`.
-/
theorem exists_level_fix {ψ : AddChar (AF D.host.F) ℂ} {θ : InfFam D} {S T : HSp D} {χS χT : (AE D)ˣ →* Circle}
    {om : GA D S × GA D T →* Module.End ℂ (WO S T → ℂ)} (hW : IsWeilDatumO ψ S T χS χT om)
    {sS : D.what₂.Tau → Matrix (Fin S.rank) (Fin S.rank) ℂ} {sT : D.what₂.Tau → Matrix (Fin T.rank) (Fin T.rank) ℂ}
    (hS : ∀ τ, IsCartanInv (gramAt D S τ) (sS τ)) (hT : ∀ τ, IsCartanInv (gramAt D T τ) (sT τ))
    {ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)} {ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)}
    (hΛS : IsSelfDualC S ΛS) (hΛT : IsSelfDualC T ΛT)
    {βS : GL (Fin S.rank) (Lev.EAf D)} {βT : GL (Fin T.rank) (Lev.EAf D)}
    (hβS : Formalism.L2.DIV.IsFrame βS ΛS) (hβT : Formalism.L2.DIV.IsFrame βT ΛT) {f : WO S T → ℂ}
    (hf : IsVacO ψ θ S T sS sT ΛS ΛT f) :
    ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S N k → GlobalTheory.Member.FinCong T N k' →
      om (k, k') f = f := by
  have hθ : IsInfFam θ := hf.2.inf
  obtain ⟨N₁, hN₁, hK₁⟩ := exists_level_frame S βS hβS
  obtain ⟨N₂, hN₂, hK₂⟩ := exists_level_frame T βT hβT
  have hscal : ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (N₁ * N₂) k → GlobalTheory.Member.FinCong T (N₁ * N₂) k' →
      ∃ c : ℂ, om (k, k') f = c • f := by
    intro k hk k' hk' hc hc'
    have keep : ∀ g g', GlobalTheory.Member.FinCong S (N₁ * N₂) g → GlobalTheory.Member.FinCong T (N₁ * N₂) g' → ∀ u ∈
        latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True),
        actO S T g g' u ∈
          latO S T (ΛS : Set (Fin S.rank → D.host.E)) (ΛT : Set (Fin T.rank → D.host.E)) (fun _ => True) := by
      intro g g' hg hg' u hu
      obtain ⟨b, hb, e⟩ := hK₁ g (GlobalTheory.SmoothVac.finCong_of_mul_left hg)
      obtain ⟨b', hb', e'⟩ := hK₂ g' (GlobalTheory.SmoothVac.finCong_of_mul_right hg')
      exact GlobalTheory.AdelicLatMove.actO_mem_latO S T g g' ΛS ΛS ΛT ΛT βS b βT b' hβS hb hβT hb' e e' u hu
    refine vac_eq_smul hS hT hΛS hΛT hf (GlobalTheory.WeilVacMove.isVacO_om D ψ θ S T χS χT om hW hθ sS sS sT sT _ _ _ _ k k'
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ S hk, Matrix.mul_one, Matrix.one_mul])
      (fun τ => by rw [GlobalTheory.OrientedHeis.compAt_mt_of_mem_GfC θ T hk', Matrix.mul_one, Matrix.one_mul])
      (fun u => ⟨fun hu => ⟨actO S T k⁻¹ k'⁻¹ u, keep _ _ (GlobalTheory.Member.PrincLevel.finCong_inv hc)
        (GlobalTheory.Member.PrincLevel.finCong_inv hc') u hu, ?_⟩, ?_⟩) f hf)
    · have := GlobalTheory.WeilVacMove.actO_inv_actO k⁻¹ k'⁻¹ u
      rw [inv_inv, inv_inv] at this
      exact this.symm
    · rintro ⟨u₀, hu₀, rfl⟩
      exact keep _ _ hc hc' u₀ hu₀
  obtain ⟨w₀, hw₀⟩ := GlobalTheory.SmoothVac.exists_ne_zero_of_isVacO hf
  have hcont : Continuous fun p : GA D S × GA D T => om p f w₀ := hW.om_cont _ hf.2.theta w₀
  have key : ∃ n : ℕ, ∀ k ∈ GfC S, ∀ k' ∈ GfC T, GlobalTheory.Member.FinCong S (N₁ * N₂ * n.factorial) k →
      GlobalTheory.Member.FinCong T (N₁ * N₂ * n.factorial) k' → om (k, k') f = f := by
    by_contra hne
    push_neg at hne
    choose k hk k' hk' hkc hkc' hkne using hne
    have hpow : ∀ n, ∃ m : ℕ, ∃ c : ℂ, om ((k n, k' n) ^ m) f = c • f ∧ ¬ ‖c - 1‖ ≤ 1 / 2 := by
      intro n
      obtain ⟨c, hc⟩ := hscal (k n) (hk n) (k' n) (hk' n) (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc n))
        (GlobalTheory.SmoothVac.finCong_of_mul_left (hkc' n))
      have hc1 : c ≠ 1 := by
        rintro rfl
        exact hkne n (by rw [hc, one_smul])
      by_contra h
      simp only [not_exists, not_and, not_not] at h
      exact hc1 (GlobalTheory.Doubling.eq_one_of_forall_norm_pow_sub_one_le (A := ℂ) fun m =>
        h m (c ^ m) (om_pow_eq om _ _ c hc m))
    choose m c hmc hc using hpow
    have hmem : ∀ n, k n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (N₁ * N₂ * n.factorial) :=
      fun n => pow_mem (show k n ∈ GlobalTheory.Member.PrincLevel.levelGroup S (N₁ * N₂ * n.factorial) from ⟨hk n, hkc n⟩) _
    have hmem' : ∀ n, k' n ^ m n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (N₁ * N₂ * n.factorial) :=
      fun n => pow_mem (show k' n ∈ GlobalTheory.Member.PrincLevel.levelGroup T (N₁ * N₂ * n.factorial) from ⟨hk' n, hkc' n⟩) _
    have ht := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k n ^ m n) (fun n => (hmem n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem n).2)
    have ht' := GlobalTheory.SplitCharTrivial.tendsto_one_of_finCong (k := fun n => k' n ^ m n) (fun n => (hmem' n).1)
      (fun n => GlobalTheory.SmoothVac.finCong_of_mul_right (hmem' n).2)
    have h2 := (hcont.tendsto (1, 1)).comp (ht.prodMk_nhds ht')
    have e1 : om ((1 : GA D S), (1 : GA D T)) f w₀ = f w₀ := by
      show om 1 f w₀ = _
      rw [map_one]
      rfl
    rw [Function.comp_def, e1] at h2
    have hpos : 0 < ‖f w₀‖ / 2 := half_pos (norm_pos_iff.2 hw₀)
    obtain ⟨n, hn⟩ := (h2.eventually (Metric.ball_mem_nhds _ hpos)).exists
    have e2 : om (k n ^ m n, k' n ^ m n) f = c n • f := hmc n
    rw [e2, Pi.smul_apply, smul_eq_mul, dist_eq_norm, ← sub_one_mul, norm_mul] at hn
    have := norm_pos_iff.2 hw₀
    exact hc n (by nlinarith)
  obtain ⟨n, hn⟩ := key
  exact ⟨_, mul_pos (mul_pos hN₁ hN₂) n.factorial_pos, hn⟩

set_option synthInstance.maxHeartbeats 400000 in
set_option maxHeartbeats 1600000 in

/- English proof (translation)
Introduce `D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t`. Establish `hI` using `hX.is`. Take `⟨N, hN, h⟩` from `exists_level_fix (S := GlobalTheory.Grid.neg A) (T := WW) (om := (X.ω t).toSgn true) (hI.weil t) (sS := fun τ => -X.rA.s τ) (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1) (fun τ => (hI.rigW.2.2 τ).1) (GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1) hI.ri …`. Use `⟨N, hN, fun k hk k' hk' hc hc' => ⟨1, isAlgebraic_one, ?_⟩⟩` and prove the remaining obligations. Rewrite using `[one_smul]`.

Conclude with `h ((GlobalTheory.Grid.ofSgn true A).symm k) hk k' hk' hc hc'`.
-/
theorem level_vac_alg : ∀ {D : D7} {T : Type} [Finite T] {L : LevCh D T} {μ₀ : T} {sc : Consts} {G : GridData L sc} {W : G.Weil}
    {i j : Fin D.R.m} {A A' WW : HSp D} {X : Tri T A A' WW}, GlobalTheory.FunPr.Hypotheses₂ → (∀ D, GlobalTheory.NormSum.Inp D) → L.Is μ₀ →
    IsBottomTri W i j X → ∀ (t : T), ∃ N : ℕ, 0 < N ∧ ∀ k ∈ GfC A, ∀ k' ∈ GfC WW, GlobalTheory.Member.FinCong A N k →
      GlobalTheory.Member.FinCong WW N k' → ∃ ζ : ℂ, IsAlgebraic ℚ ζ ∧ X.ω t (k, k') X.vac = ζ • X.vac := by
  intro D T _ L μ₀ sc G W i j A A' WW X _ _ _ hX t
  have hI := hX.is
  obtain ⟨N, hN, h⟩ := exists_level_fix (S := GlobalTheory.Grid.neg A) (T := WW) (om := (X.ω t).toSgn true) (hI.weil t)
    (sS := fun τ => -X.rA.s τ) (fun τ => GlobalTheory.Grid.isCartanInv_sgn true A τ (hI.rigA.2.2 τ).1)
    (fun τ => (hI.rigW.2.2 τ).1) (GlobalTheory.RowTest.isSelfDualC_neg' hI.rigA.1) hI.rigW.1 hI.rigA.2.1 hI.rigW.2.1 hI.isVac
  refine ⟨N, hN, fun k hk k' hk' hc hc' => ⟨1, isAlgebraic_one, ?_⟩⟩
  rw [one_smul]
  exact h ((GlobalTheory.Grid.ofSgn true A).symm k) hk k' hk' hc hc'

end GlobalTheory.LevelVac

end
