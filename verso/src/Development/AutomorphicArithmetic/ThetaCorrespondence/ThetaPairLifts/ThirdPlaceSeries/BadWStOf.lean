import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BadWStOfRegular
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.CohomologicalCsdTempered
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.ShareWSt
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.Realised
import Development.AutomorphicArithmetic.ThetaCorrespondence.ThetaPairLifts.ThirdPlaceSeries.BaseLevelIsWhitStatement

set_option synthInstance.maxHeartbeats 200000

section
open NumberField IsDedekindDomain
open Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Pj Formalism.L2.DIV Formalism.L2.Indef Formalism.L2.Indef.Tree Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Cx Formalism.IndefR.FWT
open GlobalTheory.BigTop GlobalTheory.BigOn GlobalTheory.OntoChain GlobalTheory.RealIndexBound GlobalTheory.OnTies GlobalTheory.ShareOn Formalism.MainNotions.ArithmeticCylinders
set_option autoImplicit false
noncomputable section
namespace GlobalTheory.BadWOn
open Module GlobalTheory.BadCount GlobalTheory.TwistedRepresentationEmbedding GlobalTheory.CovTop ReciprocityTheory.ChartRestriction.G.FD ReciprocityTheory.ChartRestriction.G.AR.Up GlobalTheory.IndefiniteRowSideFullHecke.FrameWeightGapBounds
section Point
variable {D : D7} {L : SizeData₂ D} {hT : GatTies D} {Gi : Formalism.MainNotions.G.Inst D L} {Gl : Formalism.MainNotions.G.LatInst D} {Kc : Formalism.MainNotions.G.Consts}
  {Y : DivX D} {cX : ExtraC} {ex : Extra D L hT Gi Gl Kc Y cX} {Csz : ℝ}
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Take `⟨C, hCf, hact, M, ka, ρ, σ, f, hpull, hequiv, hli, hspan, hlev, hcard, hcase⟩` from `hmod`. Take `⟨lam, ψ, hW, hlam, hhalf⟩` from `_root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip D L hT Gi Gl Kc Y cX ex Csz p hRows`. Take `⟨-, hHex⟩` from `GlobalTheory.T.exists_whittakerDatum_and_halfLevels D ψ hW.1`. Use `choose Hh hHh using hHex`. Set `e : p.P.Gp ≃* G0g D.nd` to `p.R.eG.trans p.cG`.

Set `π : p.P.Gp →* G0g D.nd` to `e.toMonoidHom`. Set `ιs : G0g D.nd →* p.P.Gp` to `e.symm.toMonoidHom`. Set `P : Subgroup (G0g D.nd)` to `p.P.P0.map π`. Set `P' : Subgroup p.P.Gp` to `P.comap π`. Establish `hle : P' ≤ p.P.P0` using `fun g hg => (Subgroup.mem_map_iff_mem e.injective).1 hg`.

Establish `hge : p.P.P0 ≤ P'` using `fun g hg => (Subgroup.mem_map_iff_mem e.injective).2 hg`. Establish `hbot : LevelHyp (GlobalTheory.ShareOn.sub M ⊥)` using `hlev ⊥ ⟨0, fun g hg v => by`. Rewrite `hg` using `[Subgroup.mem_bot]`. Substitute `hg` using the available equality. Introduce `a b`.

Simplify using `only [map_one]`. Use `⟨fun h => ?_, fun h => ?_⟩` and prove the remaining obligations. Conclude with `Matrix.one_apply_ne (ne_of_gt h)`. Substitute `h` using the available equality. Conclude with `Matrix.one_apply_eq a⟩`.

Establish `hP'lev : LevelHyp (GlobalTheory.ShareOn.sub M P')`. Take `⟨k, hk⟩` from `hhalf`. Conclude with `hlev P' ⟨k, fun g hg v => hk g (hle hg) v⟩`. Establish `hHlev : ∀ k, LevelHyp (GlobalTheory.ShareOn.sub M ((Hh k).comap π))` using `fun k => hlev _ ⟨k + 1, fun g hg v => ((hHh k (π g)).1 hg) ⟨k + 1, v⟩ (by simp)⟩`. Establish `hsOf : GlobalTheory.ShareOn.sOf M ≤ T`.

Establish `key : ∀ a b : ℕ, a * (b - a) * 4 ≤ b * b`. Introduce `a b`. Break down `le_total a b with h | h` into its components or cases. Take `⟨q, rfl⟩` from `Nat.exists_eq_add_of_le h`. Rewrite using `[Nat.add_sub_cancel_left]`.

Use polynomial arithmetic with `[sq_nonneg ((a : ℤ) - q)]`. Rewrite using `[Nat.sub_eq_zero_of_le h]`. Simplify using the standard rewrite rules. Establish `hq : M.p0 * (D.R.r - M.p0) ≤ D.R.r * D.R.r / 4` using `(Nat.le_div_iff_mul_le (by norm_num)).2 (key _ _)`. Establish `hX : M.dimX ≤ D.R.f * (D.R.r * D.R.r / 4)`.

Unfold `TwoLevels.dimX`. Rewrite using `[hcard]`. Conclude with `Nat.mul_le_mul_left _ hq`. Unfold `GlobalTheory.ShareOn.sOf`. Use `Nat.mul_le_mul_left (50 * D.R.r ^ 2) hX` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `hc : (M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧ GlobalTheory.ShareOn.sOf M ≤ T ∧ LevelHyp (GlobalTheory.ShareOn.sub M ⊥))`. Break down `hcase with h | ⟨h1, h2, h3⟩` into its components or cases. Conclude with `Or.inl h`. Conclude with `Or.inr ⟨h1, h2, h3, hsOf, hbot⟩`.

Set `A` to `p.R.toRealDat.FW i`. Set `N` to `p.R.toRealDat.nW i`. Set `ρK : Representation D.what₂.LL p.P.Gp (Fin N → D.what₂.LL)` to `GlobalTheory.TwistedRepresentationEmbedding.twist A.ρ A.chi⁻¹`. Set `χM : p.P.Gp →* ℂˣ` to `(Units.map σ.toMonoidHom).comp A.chi⁻¹`. Set `ρM : Representation ℂ p.P.Gp (M.cusp ka)` to `GlobalTheory.TwistedRepresentationEmbedding.twist ρ χM`.

Set `ρE : Representation ℂ p.P.Gp (Fin N → ℂ)` to `GlobalTheory.TwistedRepresentationEmbedding.repE D.what₂.embLL ρK`. Establish `hequivM : ∀ g v, ρM g (f v) = f (ρK g v)`. Introduce `g v`. Rewrite using `[GlobalTheory.TwistedRepresentationEmbedding.twist_apply, GlobalTheory.TwistedRepresentationEmbedding.twist_apply, hequiv, map_smulₛₗ]`. Both sides reduce to the same expression.

Establish `hequivE : ∀ g v, ρE g (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK g v)` using `fun g v => GlobalTheory.TwistedRepresentationEmbedding.repE_embV _ _ _ _`. Set `ψ0' : P' →* D.what₂.LLˣ` to `p.P.ψ0⁻¹.comp (Subgroup.inclusion hle)`. Set `lamM : P' →* ℂˣ` to `(Units.map σ.toMonoidHom).comp ψ0'`. Set `lamb : P' →* ℂˣ` to `lam.comp (π.subgroupComap P)`. Establish `hemb : ∀ k, ∃ n : ℕ, EmbReg ρE ((Hh k).comap π) n ∧ (n : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card P' * finrank ℂ (eig ρM P' lamM)`.

Introduce `k`. Take `⟨n, hn, hb⟩` from `model_bound M ka ρM T (GlobalTheory.TwistedRepresentationEmbedding.isPullRep_twist hpull χM) hc _ P' (hHlev k) hP'lev lamM`. Conclude with `⟨n, GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep D.what₂.LL _ _ p.P.Gp N ρK σ D.what₂.embLL ρM ρE f (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) hli hspan (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.Tw …`. Use `choose n hnE hnb using hemb`. Establish `alg : ∀ (u w : D.what₂.LLˣ) (x y : Fin N → D.what₂.LL), y = ((u * w : D.what₂.LLˣ) : D.what₂.LL) • x ↔ ((u⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • y - ((w : D.what₂.LLˣ) : D.what₂.LL) • x = 0`.

Introduce `u w x y`. Rewrite using `[sub_eq_zero]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Rewrite using `[smul_smul, ← Units.val_mul, inv_mul_cancel_left]`.

Introduce `h`. Rewrite using `[Units.val_mul, mul_smul, ← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]`. Set `aK : P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)` to `fun γ => ρK γ - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id`. Establish `haK : ∀ γ F, aK γ F = (((A.chi γ)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • A.ρ γ F - ((p.P.ψ0⁻¹ ⟨γ, hle γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL) • F` using `fun γ F => rfl`. Establish `hsp : spType p.R.toRealDat p.F.lv2 i = ⨅ γ : P', LinearMap.ker (aK γ)`.

Use extensionality with `F`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker]`. Express the relevant statement in the definitionally equal form `F ∈ A.typeP p.P.P0 p.P.ψ0⁻¹ ↔ _`. Rewrite using `[Formalism.IndefR.Arith.FormsL.mem_typeP]`. Prove the components needed by the constructor for the conclusion.

Introduce `h γ`. Rewrite using `[haK]`. Conclude with `(alg _ _ _ _).1 (h ⟨γ, hle γ.2⟩)`. Introduce `h q`. Use `h ⟨q, hge q.2⟩` as an intermediate fact.

Rewrite `this` using `[haK]`. Conclude with `(alg _ _ _ _).2 this`. Establish `dM : finrank ℂ (eig ρM P' lamM) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)`. Rewrite using `[hsp]`. Use `GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (M.cusp ka) P' σ N f hli hspan aK (fun γ => ρM γ - ((lamM γ : ℂˣ) : ℂ) • LinearMap.id) ?_` and prove the remaining obligations.

Introduce `γ v`. Use `show _ = f (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)`. Rewrite using `[map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivM]`. Both sides reduce to the same expression. Establish `hlamb : ∀ γ : P', ((lamb γ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL)` using `fun γ => hlam ⟨γ, hle γ.2⟩ γ.2`.

Establish `haE : ∀ (γ : P') v, (ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)) (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (aK γ v)`. Introduce `γ v`. Use `show _ = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)`. Rewrite using `[map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivE, hlamb]`. Establish `dE : finrank ℂ (eig ρE P' lamb) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)`.

Rewrite using `[hsp]`. Conclude with `GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) P' D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ …`. Use `haveI : Fintype (G0g D.nd) := Fintype.ofEquiv p.P.Gp e.toEquiv`. Establish `hsumE : Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 = ∑ g : p.P.Gp, D.ntypes.e0.coeff (e g) • ρE g`. Rewrite using `[Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype D.ntypes.e0.coeff (fun a b => b • (ρE.comp ιs) a) (fun a => zero_smul ℂ _)]`.

Conclude with `(Fintype.sum_equiv e.toEquiv (fun g => D.ntypes.e0.coeff (e g) • ρE g) (fun h => D.ntypes.e0.coeff h • (ρE.comp ιs) h) (fun g => by simp [ιs])).symm`. Take `⟨-, -, -, hid, -, -⟩` from `p.grpRecPin`. Establish `hE0 : ∀ v, Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (eGood p.R.toRealDat i v)`. Introduce `v`. Establish `hG : eGood p.R.toRealDat i v = ∑ g : p.P.Gp, (idemOf p.P.A3.A.X).coeff g • ρK g v` using `by show ((∑ g, ((idemOf p.P.A3.A.X).coeff g * ((A.chi g)⁻¹ : D.what₂.LLˣ)) • A.ρ g : (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)) v) = _`.

Rewrite using `[LinearMap.sum_apply]`. Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, mul_smul]`. Both sides reduce to the same expression. Rewrite using `[hsumE, LinearMap.sum_apply, hG, map_sum]`.

Use `Finset.sum_congr rfl fun g _ => ?_` and prove the remaining obligations. Rewrite using `[LinearMap.smul_apply, hequivE, map_smulₛₗ, hid]`. Set `aO : Option P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)` to `fun o => o.elim (eGood p.R.toRealDat i) aK`. Set `aO' : Option P' → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ)` to `fun o => o.elim (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id)`. Establish `dBad : finrank ℂ (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) : Submodule ℂ (Fin N → ℂ)) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL))`.

Establish `h1 : (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) : Submodule ℂ (Fin N → ℂ)) = ⨅ o, LinearMap.ker (aO' o)`. Rewrite using `[iInf_option, inf_comm]`. Both sides reduce to the same expression. Establish `h2 : (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL)) = ⨅ o, LinearMap.ker (aO o)`. Rewrite using `[iInf_option, inf_comm, hsp]`.

Both sides reduce to the same expression. Rewrite using `[h1, h2]`. Use `GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) (Option P') D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.em …` and prove the remaining obligations. Introduce and unpack `(_ | γ) v`. Conclude with `hE0 v`.

Conclude with `haE γ v`. Establish `hsplit : IsSplit π ιs` using `⟨fun g => e.apply_symm_apply g, fun g γ h => by`. Establish `hγ : γ = 1` using `e.injective (h.trans e.map_one.symm)`. Substitute `hγ` using the available equality. Use the proof step `simp⟩`.

Set `ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ` to `fun k => haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩ ZMod.stdAddChar`. Establish `hψ₀ : ∀ k, ψ₀ k ≠ 1`. Introduce `k h`. Use `haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩`. Use `haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩`.

Use `ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero)` as an intermediate fact. Rewrite `this` using `[AddChar.mulShift_one]`. Conclude with `this h`. Establish `hbd : ∀ k, (n k : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card (P.comap π) * finrank ℂ (eig ρE (P.comap π) lamb)`. Introduce `k`.

Rewrite using `[dE, ← dM]`. Conclude with `hnb k`. Take `⟨S, hSbad, hineq⟩` from `GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker D p.P.Gp (Fin N → ℂ) π ιs hsplit ρE P lam ψ hW lamb (fun γ => rfl) Hh hHh n 2 hnE hbd ψ₀ hψ₀`. Establish `hadm` using `GlobalTheory.T.admLq_of_green_of_eSerTie hGr D hRec.eSer`. Establish `hloc : ∀ k, 4 * locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) ≤ del` using `fun k => le_trans (by linarith [GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le D ψ₀ hψ₀ hadm hA hr (fun k => (hg k).1) k (S k) (hSbad k)]) (hg k).2`.

Rewrite `hineq` using `[dBad, dE]`. Unfold `GlobalTheory.ShareOn.BadW`. Establish `h0` using `hloc 0`. Establish `h1` using `hloc 1`. Establish `hd : (0 : ℝ) ≤ finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i)` using `Nat.cast_nonneg _`.

Use `hineq.trans ?_` and prove the remaining obligations. Use the polynomial consequences of the given equalities and inequalities.
-/
theorem badW_of_del_bound_of_T_bound (p : PtAt ex Csz) (i : Fin D.R.m) (T : ℕ) (del : ℝ) (hGr : GlobalTheory.GLq.Green) (hRows : p.PointConditions')
    (hRec : RecTies p) (hmod : ModelAt p i T) (hr : 100 ≤ D.R.r) (hA : TieAdmG D)
    (hg : ∀ k : Fin 2, 2 ^ 12 ≤ D.host.g k ∧ 4 * (3 * (D.R.f : ℝ) / (D.host.g k : ℝ) + 23 * (D.R.f : ℝ) *
      Real.log (D.host.g k : ℝ) / Real.sqrt (D.host.g k : ℝ) + 2 * (D.R.f : ℝ) * (D.R.m : ℝ) *
      (1 / (4 * ((min D.host.q D.host.d : ℕ) : ℝ)) + (1 + Real.log (D.R.r : ℝ)) / ((D.host.g k : ℝ) - 1)) +
      (D.R.r : ℝ) / 2 * (7 / 8 : ℝ) ^ D.R.f + Real.exp (-(D.R.f : ℝ) / (5 * Real.log (D.R.r : ℝ)))) ≤ del)
    (hsT : 2 * D.R.r + 50 * D.R.r ^ 2 * (D.R.f * (D.R.r * D.R.r / 4)) + 2 ≤ T) : BadW p i del := by
  classical
  obtain ⟨C, hCf, hact, M, ka, ρ, σ, f, hpull, hequiv, hli, hspan, hlev, hcard, hcase⟩ := hmod
  obtain ⟨lam, ψ, hW, hlam, hhalf⟩ := _root_.GlobalTheory.T.exists_whittaker_lam_psi_half_unip D L hT Gi Gl Kc Y cX ex Csz p hRows
  obtain ⟨-, hHex⟩ := GlobalTheory.T.exists_whittakerDatum_and_halfLevels D ψ hW.1
  choose Hh hHh using hHex
  let e : p.P.Gp ≃* G0g D.nd := p.R.eG.trans p.cG
  let π : p.P.Gp →* G0g D.nd := e.toMonoidHom
  let ιs : G0g D.nd →* p.P.Gp := e.symm.toMonoidHom
  let P : Subgroup (G0g D.nd) := p.P.P0.map π
  let P' : Subgroup p.P.Gp := P.comap π
  have hle : P' ≤ p.P.P0 := fun g hg => (Subgroup.mem_map_iff_mem e.injective).1 hg
  have hge : p.P.P0 ≤ P' := fun g hg => (Subgroup.mem_map_iff_mem e.injective).2 hg
  have hbot : LevelHyp (GlobalTheory.ShareOn.sub M ⊥) := hlev ⊥ ⟨0, fun g hg v => by
    rw [Subgroup.mem_bot] at hg
    subst hg
    intro a b
    simp only [map_one]
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact Matrix.one_apply_ne (ne_of_gt h)
    · subst h; exact Matrix.one_apply_eq a⟩
  have hP'lev : LevelHyp (GlobalTheory.ShareOn.sub M P') := by
    obtain ⟨k, hk⟩ := hhalf
    exact hlev P' ⟨k, fun g hg v => hk g (hle hg) v⟩
  have hHlev : ∀ k, LevelHyp (GlobalTheory.ShareOn.sub M ((Hh k).comap π)) := fun k => hlev _ ⟨k + 1, fun g hg v =>
    ((hHh k (π g)).1 hg) ⟨k + 1, v⟩ (by simp)⟩
  have hsOf : GlobalTheory.ShareOn.sOf M ≤ T := by
    have key : ∀ a b : ℕ, a * (b - a) * 4 ≤ b * b := by
      intro a b
      rcases le_total a b with h | h
      · obtain ⟨q, rfl⟩ := Nat.exists_eq_add_of_le h
        rw [Nat.add_sub_cancel_left]
        nlinarith [sq_nonneg ((a : ℤ) - q)]
      · rw [Nat.sub_eq_zero_of_le h]; simp
    have hq : M.p0 * (D.R.r - M.p0) ≤ D.R.r * D.R.r / 4 := (Nat.le_div_iff_mul_le (by norm_num)).2 (key _ _)
    have hX : M.dimX ≤ D.R.f * (D.R.r * D.R.r / 4) := by
      unfold TwoLevels.dimX; rw [hcard]; exact Nat.mul_le_mul_left _ hq
    unfold GlobalTheory.ShareOn.sOf
    have := Nat.mul_le_mul_left (50 * D.R.r ^ 2) hX
    omega
  have hc : (M.p0 = 0 ∨ M.p0 = D.R.r) ∨ (0 < M.p0 ∧ M.p0 < D.R.r ∧ GlobalTheory.ShareOn.ArchOn M ka T ∧
      GlobalTheory.ShareOn.sOf M ≤ T ∧ LevelHyp (GlobalTheory.ShareOn.sub M ⊥)) := by
    rcases hcase with h | ⟨h1, h2, h3⟩
    · exact Or.inl h
    · exact Or.inr ⟨h1, h2, h3, hsOf, hbot⟩
  let A := p.R.toRealDat.FW i
  let N := p.R.toRealDat.nW i
  let ρK : Representation D.what₂.LL p.P.Gp (Fin N → D.what₂.LL) := GlobalTheory.TwistedRepresentationEmbedding.twist A.ρ A.chi⁻¹
  let χM : p.P.Gp →* ℂˣ := (Units.map σ.toMonoidHom).comp A.chi⁻¹
  let ρM : Representation ℂ p.P.Gp (M.cusp ka) := GlobalTheory.TwistedRepresentationEmbedding.twist ρ χM
  let ρE : Representation ℂ p.P.Gp (Fin N → ℂ) := GlobalTheory.TwistedRepresentationEmbedding.repE D.what₂.embLL ρK
  have hequivM : ∀ g v, ρM g (f v) = f (ρK g v) := by
    intro g v
    rw [GlobalTheory.TwistedRepresentationEmbedding.twist_apply, GlobalTheory.TwistedRepresentationEmbedding.twist_apply, hequiv, map_smulₛₗ]
    rfl
  have hequivE : ∀ g v, ρE g (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK g v) := fun g v => GlobalTheory.TwistedRepresentationEmbedding.repE_embV _ _ _ _
  let ψ0' : P' →* D.what₂.LLˣ := p.P.ψ0⁻¹.comp (Subgroup.inclusion hle)
  let lamM : P' →* ℂˣ := (Units.map σ.toMonoidHom).comp ψ0'
  let lamb : P' →* ℂˣ := lam.comp (π.subgroupComap P)
  have hemb : ∀ k, ∃ n : ℕ, EmbReg ρE ((Hh k).comap π) n ∧
      (n : ℝ) * Nat.card ((Hh k).comap π) ≤ 2 * Nat.card P' * finrank ℂ (eig ρM P' lamM) := by
    intro k
    obtain ⟨n, hn, hb⟩ := model_bound M ka ρM T (GlobalTheory.TwistedRepresentationEmbedding.isPullRep_twist hpull χM) hc _ P' (hHlev k) hP'lev lamM
    exact ⟨n, GlobalTheory.T.embedsInRegularRepresentationCopies_complexEmbedding_indep D.what₂.LL _ _ p.P.Gp N ρK σ D.what₂.embLL ρM ρE f (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) hli hspan
      (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) hequivM hequivE _ n hn, hb⟩
  choose n hnE hnb using hemb
  have alg : ∀ (u w : D.what₂.LLˣ) (x y : Fin N → D.what₂.LL), y = ((u * w : D.what₂.LLˣ) : D.what₂.LL) • x ↔
      ((u⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • y - ((w : D.what₂.LLˣ) : D.what₂.LL) • x = 0 := by
    intro u w x y
    rw [sub_eq_zero]
    constructor
    · rintro rfl
      rw [smul_smul, ← Units.val_mul, inv_mul_cancel_left]
    · intro h
      rw [Units.val_mul, mul_smul, ← h, smul_smul, ← Units.val_mul, mul_inv_cancel, Units.val_one, one_smul]
  let aK : P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun γ =>
    ρK γ - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • LinearMap.id
  have haK : ∀ γ F, aK γ F = (((A.chi γ)⁻¹ : D.what₂.LLˣ) : D.what₂.LL) • A.ρ γ F -
      ((p.P.ψ0⁻¹ ⟨γ, hle γ.2⟩ : D.what₂.LLˣ) : D.what₂.LL) • F := fun γ F => rfl
  have hsp : spType p.R.toRealDat p.F.lv2 i = ⨅ γ : P', LinearMap.ker (aK γ) := by
    ext F
    simp only [Submodule.mem_iInf, LinearMap.mem_ker]
    change F ∈ A.typeP p.P.P0 p.P.ψ0⁻¹ ↔ _
    rw [Formalism.IndefR.Arith.FormsL.mem_typeP]
    constructor
    · intro h γ
      rw [haK]
      exact (alg _ _ _ _).1 (h ⟨γ, hle γ.2⟩)
    · intro h q
      have := h ⟨q, hge q.2⟩
      rw [haK] at this
      exact (alg _ _ _ _).2 this
  have dM : finrank ℂ (eig ρM P' lamM) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (M.cusp ka) P' σ N f hli hspan aK (fun γ => ρM γ - ((lamM γ : ℂˣ) : ℂ) • LinearMap.id) ?_
    intro γ v
    show _ = f (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivM]
    rfl
  have hlamb : ∀ γ : P', ((lamb γ : ℂˣ) : ℂ) = D.what₂.embLL ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) :=
    fun γ => hlam ⟨γ, hle γ.2⟩ γ.2
  have haE : ∀ (γ : P') v, (ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id : (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ))
      (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (aK γ v) := by
    intro γ v
    show _ = GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (ρK γ v - ((ψ0' γ : D.what₂.LLˣ) : D.what₂.LL) • v)
    rw [map_sub, map_smulₛₗ, LinearMap.sub_apply, LinearMap.smul_apply, LinearMap.id_apply, hequivE, hlamb]
  have dE : finrank ℂ (eig ρE P' lamb) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := by
    rw [hsp]
    exact GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) P' D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _) aK
      (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id) haE
  haveI : Fintype (G0g D.nd) := Fintype.ofEquiv p.P.Gp e.toEquiv
  have hsumE : Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 =
      ∑ g : p.P.Gp, D.ntypes.e0.coeff (e g) • ρE g := by
    rw [Representation.asAlgebraHom_def, MonoidAlgebra.lift_apply, Finsupp.sum_fintype D.ntypes.e0.coeff (fun a b => b • (ρE.comp ιs) a) (fun a => zero_smul ℂ _)]
    exact (Fintype.sum_equiv e.toEquiv (fun g => D.ntypes.e0.coeff (e g) • ρE g)
      (fun h => D.ntypes.e0.coeff h • (ρE.comp ιs) h) (fun g => by simp [ιs])).symm
  obtain ⟨-, -, -, hid, -, -⟩ := p.grpRecPin
  have hE0 : ∀ v, Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0 (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N v) =
      GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N (eGood p.R.toRealDat i v) := by
    intro v
    have hG : eGood p.R.toRealDat i v = ∑ g : p.P.Gp, (idemOf p.P.A3.A.X).coeff g • ρK g v := by
      show ((∑ g, ((idemOf p.P.A3.A.X).coeff g * ((A.chi g)⁻¹ : D.what₂.LLˣ)) • A.ρ g :
        (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL)) v) = _
      rw [LinearMap.sum_apply]
      refine Finset.sum_congr rfl fun g _ => ?_
      rw [LinearMap.smul_apply, mul_smul]
      rfl
    rw [hsumE, LinearMap.sum_apply, hG, map_sum]
    refine Finset.sum_congr rfl fun g _ => ?_
    rw [LinearMap.smul_apply, hequivE, map_smulₛₗ, hid]
  let aO : Option P' → (Fin N → D.what₂.LL) →ₗ[D.what₂.LL] (Fin N → D.what₂.LL) := fun o =>
    o.elim (eGood p.R.toRealDat i) aK
  let aO' : Option P' → (Fin N → ℂ) →ₗ[ℂ] (Fin N → ℂ) := fun o =>
    o.elim (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) (fun γ => ρE γ - ((lamb γ : ℂˣ) : ℂ) • LinearMap.id)
  have dBad : finrank ℂ (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
      Submodule ℂ (Fin N → ℂ)) = finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i ⊓
      LinearMap.ker (eGood p.R.toRealDat i) : Submodule D.what₂.LL (Fin N → D.what₂.LL)) := by
    have h1 : (eig ρE P' lamb ⊓ LinearMap.ker (Representation.asAlgebraHom (ρE.comp ιs) D.ntypes.e0) :
        Submodule ℂ (Fin N → ℂ)) = ⨅ o, LinearMap.ker (aO' o) := by
      rw [iInf_option, inf_comm]; rfl
    have h2 : (spType p.R.toRealDat p.F.lv2 i ⊓ LinearMap.ker (eGood p.R.toRealDat i) :
        Submodule D.what₂.LL (Fin N → D.what₂.LL)) = ⨅ o, LinearMap.ker (aO o) := by
      rw [iInf_option, inf_comm, hsp]; rfl
    rw [h1, h2]
    refine GlobalTheory.T.finrank_iInf_ker_semilinear_standardBasis D.what₂.LL (Fin N → ℂ) (Option P') D.what₂.embLL N (GlobalTheory.TwistedRepresentationEmbedding.embV D.what₂.embLL N) (GlobalTheory.TwistedRepresentationEmbedding.embV_li _ _) (GlobalTheory.TwistedRepresentationEmbedding.embV_span _ _)
      aO aO' ?_
    rintro (_ | γ) v
    · exact hE0 v
    · exact haE γ v
  have hsplit : IsSplit π ιs := ⟨fun g => e.apply_symm_apply g, fun g γ h => by
    have hγ : γ = 1 := e.injective (h.trans e.map_one.symm)
    subst hγ; simp⟩
  let ψ₀ : ∀ k : Fin 2, AddChar (ZMod (D.host.g k)) ℂ := fun k =>
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    ZMod.stdAddChar
  have hψ₀ : ∀ k, ψ₀ k ≠ 1 := by
    intro k h
    haveI : NeZero (D.host.g k) := ⟨(D.host.g_prime k).ne_zero⟩
    haveI : Fact (1 < D.host.g k) := ⟨(D.host.g_prime k).one_lt⟩
    have := ZMod.isPrimitive_stdAddChar (D.host.g k) (one_ne_zero)
    rw [AddChar.mulShift_one] at this
    exact this h
  have hbd : ∀ k, (n k : ℝ) * Nat.card ((Hh k).comap π) ≤
      2 * Nat.card (P.comap π) * finrank ℂ (eig ρE (P.comap π) lamb) := by
    intro k; rw [dE, ← dM]; exact hnb k
  obtain ⟨S, hSbad, hineq⟩ := GlobalTheory.T.bad_part_dim_le_sum_local_shares_whittaker D p.P.Gp (Fin N → ℂ) π ιs hsplit ρE P lam ψ hW lamb (fun γ => rfl) Hh hHh n 2
    hnE hbd ψ₀ hψ₀
  have hadm := GlobalTheory.T.admLq_of_green_of_eSerTie hGr D hRec.eSer
  have hloc : ∀ k, 4 * locShare D (fun k _ => eUk D k (ψ₀ k)) k (S k) ≤ del := fun k =>
    le_trans (by linarith [GlobalTheory.T.weightedIdempotent_localShare_bad_tuples_le D ψ₀ hψ₀ hadm hA hr (fun k => (hg k).1) k (S k) (hSbad k)]) (hg k).2
  rw [dBad, dE] at hineq
  unfold GlobalTheory.ShareOn.BadW
  have h0 := hloc 0
  have h1 := hloc 1
  have hd : (0 : ℝ) ≤ finrank D.what₂.LL (spType p.R.toRealDat p.F.lv2 i) := Nat.cast_nonneg _
  refine hineq.trans ?_
  nlinarith
end Point
/- English proof (translation)
Establish `hGr` using `hG.green`. Use `Closed.imp ((hM.and GlobalTheory.T.badShareSize_bounds_along_family).and GlobalTheory.T.hodgeLineMultiple_le_familyThreshold) ?_` and prove the remaining obligations. Introduce and unpack `eps Fm CH - ⟨⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩, ⟨x3, hx3⟩⟩`. Use `⟨max x1 (max x2 x3), fun x hx hle ι p hp hMore r hr hown i => ?_⟩` and prove the remaining obligations. Establish `h1 : x1 ≤ x` using `(le_max_left _ _).trans hle`.

Establish `h2 : x2 ≤ x` using `((le_max_left _ _).trans (le_max_right _ _)).trans hle`. Establish `h3 : x3 ≤ x` using `((le_max_right _ _).trans (le_max_right _ _)).trans hle`. Take `⟨hr100, hA, -, hg⟩` from `hx2 x hx h2 ι`. Conclude with `_root_.GlobalTheory.BadWOn.badW_of_del_bound_of_T_bound p i _ _ hGr hp hMore.2.2 (hx1 x hx h1 ι p hp hMore r hr hown i) hr100 hA hg (hx3 x hx h3 ι)`.
-/
theorem badWSt_of_greenCuspidal_of_modelSt (hG : GlobalTheory.Published.GreenCuspidal) (hM : _root_.GlobalTheory.ShareOn.ModelStatement) : _root_.GlobalTheory.ShareOn.BadWeightStatement := by
  have hGr := hG.green
  refine Closed.imp ((hM.and GlobalTheory.T.badShareSize_bounds_along_family).and GlobalTheory.T.hodgeLineMultiple_le_familyThreshold) ?_
  rintro eps Fm CH - ⟨⟨⟨x1, hx1⟩, ⟨x2, hx2⟩⟩, ⟨x3, hx3⟩⟩
  refine ⟨max x1 (max x2 x3), fun x hx hle ι p hp hMore r hr hown i => ?_⟩
  have h1 : x1 ≤ x := (le_max_left _ _).trans hle
  have h2 : x2 ≤ x := ((le_max_left _ _).trans (le_max_right _ _)).trans hle
  have h3 : x3 ≤ x := ((le_max_right _ _).trans (le_max_right _ _)).trans hle
  obtain ⟨hr100, hA, -, hg⟩ := hx2 x hx h2 ι
  exact _root_.GlobalTheory.BadWOn.badW_of_del_bound_of_T_bound p i _ _ hGr hp hMore.2.2 (hx1 x hx h1 ι p hp hMore r hr hown i) hr100 hA hg (hx3 x hx h3 ι)
end GlobalTheory.BadWOn
end
end
