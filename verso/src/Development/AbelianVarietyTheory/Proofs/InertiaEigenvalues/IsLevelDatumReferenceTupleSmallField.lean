import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsRatScalarMulIff
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsIsScaleOfChar
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ConjFunBaseRoot
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsGoodCoverGalois
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsConjugateFormsThetaLiftEqThetaSeriesStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HolomorphicSectionsSpanRestrictionStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ClassSumsSpanCuspFormsBaseTupleSecondFieldStatement
import Development.AbelianVarietyTheory.Proofs.DecoratedLatticeProofs.MemOfForallRingEquivFixed
import Formalism.LocalToGlobal.IndefiniteReal.OneMapT
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ThExprUniqOfChartIndep2
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HolomorphicCuspSectionsLeSpanAlgebraicCuspForms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.KapTopLastPosRun
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.EasyInputs
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FinPartConjMem
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IdempotentSumSelfDualFramesBoundStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AdjointFrameMatrixIntegralOfConjugateHalfStatement

open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.L2.DIV Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.FWT Formalism.IndefR.Links IsDedekindDomain NumberField GlobalTheory.ExportSeries Formalism.L2.Pj GlobalTheory.CoverRead GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels GlobalTheory.ConjTwist
open Formalism.L2.Host (embLL0)
open scoped TensorProduct
attribute [local instance] Formalism.BasicNotions.Host.cmStar

set_option autoImplicit false
set_option maxHeartbeats 1600000

noncomputable section

namespace GlobalTheory.RefDatumLev

variable {D : D7}

/- English proof (translation)
Use `Finset.eq_empty_of_forall_notMem fun PP hPP => ?_` and prove the remaining obligations. Establish `h` using `(hL.Q_ram A.μ0 PP).2 (Or.inl hPP)`. Rewrite `h` using `[hL.xi_base]`. Conclude with `h fun x _ => rfl`.
-/
theorem q_base_empty {G : Type} [Group G] [Fintype G] {Pl0 T0 : Type} {A : FamIn D.what₂.LL G Pl0 T0 D.R.m}
    {Ks : Type} [Field Ks] [NumberField Ks] [Algebra Ks D.what₂.LL] (R : RealDat D A Ks) (hL : R.toLevCh.Is A.μ0) :
    R.Q A.μ0 = ∅ := by
  refine Finset.eq_empty_of_forall_notMem fun PP hPP => ?_
  have h := (hL.Q_ram A.μ0 PP).2 (Or.inl hPP)
  rw [hL.xi_base] at h
  exact h fun x _ => rfl

open Classical in
/- English proof (translation)
Take `⟨⟨es, hes, he⟩, hc⟩` from `h`. Use `⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩` and prove the remaining obligations. Introduce `Q hQ`. Take `⟨PP, hPP, rfl⟩` from `Finset.mem_image.1 hQ`. Use `show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)`.

Rewrite using `[Formalism.L2.DIV.conjPl_conjPl]`. Conclude with `GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl`. Rewrite using `[Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by`. Rewrite using `[← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]`. Simplify using `only [Formalism.L2.DIV.conjPl_conjPl]`.

Rewrite using `[he, map_sum]`. Rewrite using `[GlobalTheory.MovedIdem.cA_cA, mul_comm]`. Conclude with `hc`.
-/
theorem isIdemSum_conjPl {e : AE D} {P : Finset (Formalism.L2.DIV.Pl D.host.E)} (h : IsIdemSum e P) :
    IsIdemSum (cA D e) (P.image Formalism.L2.DIV.conjPl) := by
  classical
  obtain ⟨⟨es, hes, he⟩, hc⟩ := h
  refine ⟨⟨fun Q => cA D (es (Formalism.L2.DIV.conjPl Q)), ?_, ?_⟩, ?_⟩
  · intro Q hQ
    obtain ⟨PP, hPP, rfl⟩ := Finset.mem_image.1 hQ
    show Formalism.L2.NTheta.IsIdemAt (cA D (es (Formalism.L2.DIV.conjPl (Formalism.L2.DIV.conjPl PP)))) (Formalism.L2.DIV.conjPl PP)
    rw [Formalism.L2.DIV.conjPl_conjPl]
    exact GlobalTheory.MovedIdem.isIdemAt_conj (hes PP hPP) fun x => Iff.rfl
  · rw [Finset.sum_image (fun a _ b _ (hab : Formalism.L2.DIV.conjPl a = Formalism.L2.DIV.conjPl b) => by
      rw [← Formalism.L2.DIV.conjPl_conjPl a, hab, Formalism.L2.DIV.conjPl_conjPl b])]
    simp only [Formalism.L2.DIV.conjPl_conjPl]
    rw [he, map_sum]
  · rw [GlobalTheory.MovedIdem.cA_cA, mul_comm]; exact hc

/- English proof (translation)
Unfold `frMapAdj`. Rewrite using `[Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul, Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]`.
-/
theorem frMapAdj_add' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (x y : WO S T) :
    frMapAdj S T βS βT (x + y) = frMapAdj S T βS βT x + frMapAdj S T βS βT y := by
  unfold frMapAdj
  rw [Matrix.map_add (cA D) (fun a b => (cA D).map_add a b), Matrix.transpose_add, Matrix.mul_add, Matrix.add_mul,
    Matrix.map_add (toEAf D) (fun a b => (toEAf D).map_add a b), Matrix.mul_add, Matrix.add_mul]

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero`. Rewrite using `[zero_smul, zero_smul]`. Unfold `frMapAdj`. Rewrite using `[Matrix.map_zero (cA D) (cA D).map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul, Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]`.

Consider the case `succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]`.
-/
theorem frMapAdj_nsmul' (S T : HSp D) (βS : GL (Fin S.rank) (EAf D)) (βT : GL (Fin T.rank) (EAf D)) (k : ℕ) (x : WO S T) :
    frMapAdj S T βS βT (k • x) = k • frMapAdj S T βS βT x := by
  induction k with
  | zero =>
    rw [zero_smul, zero_smul]
    unfold frMapAdj
    rw [Matrix.map_zero (cA D) (cA D).map_zero, Matrix.transpose_zero, Matrix.mul_zero, Matrix.zero_mul,
      Matrix.map_zero (toEAf D) (toEAf D).map_zero, Matrix.mul_zero, Matrix.zero_mul]
  | succ n ih => rw [succ_nsmul, succ_nsmul, frMapAdj_add', ih]

/- English proof (translation)
Establish `hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb` using `Ideal.mul_le_left`. Rewrite `hle` using `[T.Q.l.prod]`. Conclude with `hle (Ideal.mem_span_singleton_self _)`.
-/
theorem natM_mem_Mb (T : CoreJ D) : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := by
  have hle : T.Q.l.Mb * T.Q.l.Mb.map (T.Q.H.bar : 𝓞 D.host.E →+* 𝓞 D.host.E) ≤ T.Q.l.Mb := Ideal.mul_le_left
  rw [T.Q.l.prod] at hle
  exact hle (Ideal.mem_span_singleton_self _)

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h i j`. Use `sub_mem (h i j) (nsmul_mem (hN' i j) k)` as an intermediate fact. Rewrite `this` using `[Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_right]`. Then use the resulting hypothesis. Introduce `h i j`.

Rewrite using `[Matrix.add_apply, Matrix.smul_apply]`. Conclude with `add_mem (h i j) (nsmul_mem (hN' i j) k)`.
-/
theorem isIntM_add_nsmul_iff {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN' : IsIntM N') (k : ℕ) :
    IsIntM (N + k • N') ↔ IsIntM N := by
  constructor
  · intro h i j
    have := sub_mem (h i j) (nsmul_mem (hN' i j) k)
    rwa [Matrix.add_apply, Matrix.smul_apply, add_sub_cancel_right] at this
  · intro h i j
    rw [Matrix.add_apply, Matrix.smul_apply]
    exact add_mem (h i j) (nsmul_mem (hN' i j) k)

/- English proof (translation)
Establish `hk0 : ((k : ℕ) : Formalism.L2.DIV.kP PP) = 0`. Rewrite using `[← map_natCast (Ideal.Quotient.mk PP.asIdeal)]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.2 hk`. Use extensionality with `i j`. Establish `h1 : (N + k • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E` using `(isIntM_add_nsmul_iff hN' _).2 hN i j`.

Unfold `redM`. Rewrite using `[dif_pos h1, dif_pos (hN i j)]`. Establish `h2 : (⟨(N + k • N') i j, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) = ⟨N i j, hN i j⟩ + ((k : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N' i j, hN' i j⟩`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]`.

Rewrite using `[h2, map_add, map_mul, map_natCast, hk0, zero_mul, add_zero]`.
-/
theorem redM_add_nsmul (PP : Formalism.L2.DIV.Pl D.host.E) {b a : ℕ} {N N' : Matrix (Fin b) (Fin a) (EAf D)} (hN : IsIntM N)
    (hN' : IsIntM N') (k : ℕ) (hk : ((k : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal) : redM PP (N + k • N') = redM PP N := by
  have hk0 : ((k : ℕ) : Formalism.L2.DIV.kP PP) = 0 := by
    rw [← map_natCast (Ideal.Quotient.mk PP.asIdeal)]
    exact Ideal.Quotient.eq_zero_iff_mem.2 hk
  ext i j
  have h1 : (N + k • N') i j ∈ Formalism.L2.Herm.intAf D.host.F D.host.E := (isIntM_add_nsmul_iff hN' _).2 hN i j
  unfold redM
  rw [dif_pos h1, dif_pos (hN i j)]
  have h2 : (⟨(N + k • N') i j, h1⟩ : Formalism.L2.Herm.intAf D.host.F D.host.E) =
      ⟨N i j, hN i j⟩ + ((k : ℕ) : Formalism.L2.Herm.intAf D.host.F D.host.E) * ⟨N' i j, hN' i j⟩ := by
    apply Subtype.ext
    simp [Matrix.add_apply, Matrix.smul_apply, nsmul_eq_mul]
  rw [h2, map_add, map_mul, map_natCast, hk0, zero_mul, add_zero]

/- English proof (translation)
Unfold `omegaK`. Establish `: (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1)` using `⟨fun hy PP hPP => h PP hPP ▸ hy PP hPP, fun hy PP hPP => (h PP hPP).symm ▸ hy PP hPP⟩`. Distinguish the cases in `hc : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1`. Rewrite using `[if_pos hc, if_pos (this.1 hc)]`. Rewrite using `[if_neg hc, if_neg (fun h' => hc (this.2 h'))]`.
-/
theorem omegaK_congr {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    {y y' : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)}
    (h : ∀ PP ∈ Pg, y PP = y' PP) : omegaK Pg y = omegaK Pg y' := by
  unfold omegaK
  have : (∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1) ↔ (∀ PP ∈ Pg, LowZero a (y' PP) ∧ topL a (y' PP) = 1) :=
    ⟨fun hy PP hPP => h PP hPP ▸ hy PP hPP, fun hy PP hPP => (h PP hPP).symm ▸ hy PP hPP⟩
  by_cases hc : ∀ PP ∈ Pg, LowZero a (y PP) ∧ topL a (y PP) = 1
  · rw [if_pos hc, if_pos (this.1 hc)]
  · rw [if_neg hc, if_neg (fun h' => hc (this.2 h'))]

/- English proof (translation)
Unfold `omegaK`. Use `split_ifs`. Use `exacts [k.one_mem, k.zero_mem]`.
-/
theorem omegaK_mem {a b : ℕ} (Pg : Finset (Formalism.L2.DIV.Pl D.host.E))
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) (k : Subfield ℂ) :
    omegaK Pg y ∈ k := by
  unfold omegaK
  split_ifs
  exacts [k.one_mem, k.zero_mem]

/- English proof (translation)
Unfold `omegaQ`. Rewrite using `[dif_pos (fun PP h => absurd h (Finset.notMem_empty PP))]`. Simplify using the standard rewrite rules.
-/
theorem omegaQ_empty {a b : ℕ} (r : ℕ) (ξ : ∀ PP : Formalism.L2.DIV.Pl D.host.E, (Formalism.L2.DIV.kP PP)ˣ →* ℂˣ) (k : ℤ)
    (y : ∀ PP : Formalism.L2.DIV.Pl D.host.E, Matrix (Fin b) (Fin a) (Formalism.L2.DIV.kP PP)) : omegaQ ∅ r ξ k y = 1 := by
  unfold omegaQ
  rw [dif_pos (fun PP h => absurd h (Finset.notMem_empty PP))]
  simp

/- English proof (translation)
Introduce `D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp`. Establish `hQ0 : Rl.toRealDat.Q A3.A.μ0 = ∅` using `q_base_empty Rl.toRealDat hcore.lev`. Take `⟨-, e, he, hth⟩` from `hcore.thP.vP j A3.A.μ0`. Rewrite `he` using `[hQ0, Finset.union_empty]`. Simplify using `only [hQ0, omegaQ_empty, mul_one] at hth`.

Take `⟨cV, hbV⟩` from `hcore.lev.βV j`. Take `⟨cW, hbW⟩` from `hcore.lev.βW j`. Establish `hsV` using `GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV`. Establish `hsW` using `GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW`. Establish `hfV` using `hbV.1`.

Establish `hfW` using `hbW.1`. Establish `hhalf` using `(hpins.2.tuple ()).half`. Establish `hP2 : ∀ PP ∈ Rl.toRealDat.Pg, ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal` using `fun PP hPP => hhalf.2.2 PP (Or.inl hPP)`. Establish `hMPg : ∀ PP ∈ Rl.toRealDat.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal`. Introduce `PP hPP`.

Establish `h1 : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb` using `natM_mem_Mb T`. Establish `h2 : T.Q.l.Mb ≤ PP.asIdeal`. Rewrite using `[hhalf.1]`. Conclude with `Ideal.prod_le_inf.trans (Finset.inf_le hPP)`. Conclude with `h2 h1`.

Use `⟨Rl.toRealDat.Pg.image Formalism.L2.DIV.conjPl, cA D e, _, isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩` and prove the remaining obligations. Introduce `PP hPP`. Take `⟨P0, hP0, rfl⟩` from `Finset.mem_image.1 hPP`. Use `show Formalism.L2.DIV.starOHom ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal`. Rewrite using `[map_natCast]`.

Conclude with `hMPg P0 hP0`. Introduce `t ht`. Distinguish the cases in `hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)`. Conclude with `⟨GlobalTheory.T.idempotent_sum_self_dual_frames_bound D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩`. Conclude with `absurd (if_neg hc) ht`.

Introduce `u hu hue t`. Establish `hN'` using `GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue`. Establish `hfr : frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) (t + T.Q.l.M • u) = frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t + T.Q.l.M • frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) u`. Rewrite using `[frMapAdj_add', frMapAdj_nsmul']`. Establish `hKu : IsHalf (cA D e) (T.Q.l.M • u)` using `fun a b => by`.

Rewrite using `[Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]`. Establish `hhalf' : IsHalf (cA D e) (t + T.Q.l.M • u) ↔ IsHalf (cA D e) t`. Prove the components needed by the constructor for the conclusion. Introduce `h a b`. Use `h a b` as an intermediate fact.

Rewrite `this` using `[Matrix.add_apply, mul_add, hKu a b]`. Conclude with `add_right_cancel this`. Introduce `h a b`. Rewrite using `[Matrix.add_apply, mul_add, h a b, hKu a b]`. Use `show (if _ then _ else _) = (if _ then _ else _)`.

Rewrite using `[hfr]`. Distinguish the cases in `hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)`. Rewrite using `[if_pos ⟨hhalf'.2 hc.1, (isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]`. Conclude with `omegaK_congr _ fun PP hPP => redM_add_nsmul PP hc.2 hN' _ (hMPg PP hPP)`. Rewrite using `[if_neg, if_neg hc]`.

Introduce `h'`. Conclude with `hc ⟨hhalf'.1 h'.1, (isIntM_add_nsmul_iff hN' _).1 h'.2⟩`. Introduce `t show (if _ then _ else _) ∈ _ split_ifs`. Conclude with `omegaK_mem _ _ _`. Conclude with `Subfield.zero_mem _`.
-/
theorem isLevDatum_ref : ∀ (D : D7) (Γ : Type) [Group Γ] [Fintype Γ] (Pl0 I0 T0 : Type) (A3 : FamIn3 D.what₂.LL Γ Pl0 I0 (List ℕ) T0 D.R.m), GlobalTheory.NT.RayField → ∀ (T : CoreJ D) [Algebra T.Q.c.F D.what₂.LL] (Rl : RealDat3 D A3 T.Q.c.F) (cG : G0 Rl.Pg D.R.r ≃* G0g D.nd) (S : NX.RatDat D.ntw) (YS : NX.NExpRealS Rl cG S) (F : Face D A3.A) (κ : ∀ j : Fin D.R.m, WeightFamilies.Wt D ((j : ℕ) + 1)) (v₀ : ∀ (j : Fin D.R.m) (σ : D.what₂.LL →+* ℂ), (Rl.MW j σ).Vec) (O : ∀ j, OMDat T.toCore Rl.toRealDat j Unit (fun _ => A3.A.μ0)), LawsJ T → GlobalTheory.Hk3.Core Rl.toRealDat F → Nonempty (FWTie T Rl.toRealDat κ v₀) → TieIn T Rl.toRealDat κ v₀ → IoExt Rl.toRealDat → QGuard Rl.toRealDat → IsGalois ℚ D.LL0 → Formalism.L2.Host.ValLL0 D Rl.C → RayIn D (D.host.g 0 * D.host.g 1 * D.host.pde * D.host.pde') (embLL0 D).fieldRange → (∀ (k : Fin 2) (z : ℂ), z ^ (D.host.g k * (D.host.g k - 1)) = 1 → z ∈ (embLL0 D).fieldRange) → ∀ (j : Fin D.R.m) (hV : T.V ((j : ℕ) + 1) T.σ₀ = Wc D j), OMPins T Rl.toRealDat κ v₀ O j → GlobalTheory.IndefiniteRowSideFullHecke.OrthonormalLatticeThetaValues.FramePin T Rl.toRealDat j T.σ₀ hV → GlobalTheory.IndefiniteRowSideFullHecke.RationalRayLevels.IsLevDatum Rl.toRealDat.ψ (Vc D j) (Wc D j) (Rl.toRealDat.ΛV j) (Rl.toRealDat.ΛW j) T.Q.l.M (embLL0 D).fieldRange (Rl.toRealDat.vacP j) (Rl.toRealDat.vP j A3.A.μ0) := by
  intro D Γ _ _ Pl0 I0 T0 A3 hRF T _ Rl cG S YS F κ v₀ O hT hcore hfw hti hio hQ hgal hval hray hroots j hV hpins hfp
  classical
  have hQ0 : Rl.toRealDat.Q A3.A.μ0 = ∅ := q_base_empty Rl.toRealDat hcore.lev
  obtain ⟨-, e, he, hth⟩ := hcore.thP.vP j A3.A.μ0
  rw [hQ0, Finset.union_empty] at he
  simp only [hQ0, omegaQ_empty, mul_one] at hth
  obtain ⟨cV, hbV⟩ := hcore.lev.βV j
  obtain ⟨cW, hbW⟩ := hcore.lev.βW j
  have hsV := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbV
  have hsW := GlobalTheory.Mem.EasyInputs.selfDualOK D _ _ _ _ hbW
  have hfV := hbV.1
  have hfW := hbW.1
  have hhalf := (hpins.2.tuple ()).half
  have hP2 : ∀ PP ∈ Rl.toRealDat.Pg,
      ((D.host.QS * D.host.q * Ideal.absNorm D.host.ccK : ℕ) : 𝓞 D.host.E) ∉ PP.asIdeal :=
    fun PP hPP => hhalf.2.2 PP (Or.inl hPP)
  have hMPg : ∀ PP ∈ Rl.toRealDat.Pg, ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ PP.asIdeal := by
    intro PP hPP
    have h1 : ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ T.Q.l.Mb := natM_mem_Mb T
    have h2 : T.Q.l.Mb ≤ PP.asIdeal := by
      rw [hhalf.1]
      exact Ideal.prod_le_inf.trans (Finset.inf_le hPP)
    exact h2 h1
  refine ⟨Rl.toRealDat.Pg.image Formalism.L2.DIV.conjPl, cA D e, _, isIdemSum_conjPl he, ?_, ?_, ?_, ?_, hth⟩
  · intro PP hPP
    obtain ⟨P0, hP0, rfl⟩ := Finset.mem_image.1 hPP
    show Formalism.L2.DIV.starOHom ((T.Q.l.M : ℕ) : 𝓞 D.host.E) ∈ P0.asIdeal
    rw [map_natCast]
    exact hMPg P0 hP0
  · intro t ht
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · exact ⟨GlobalTheory.T.idempotent_sum_self_dual_frames_bound D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 t hc.1 hc.2, hc.1⟩
    · exact absurd (if_neg hc) ht
  · intro u hu hue t
    have hN' := GlobalTheory.T.adjointFrameMatrix_integral_of_conjugate_half D _ _ _ _ _ _ hsV hsW hfV hfW _ e he hP2 u hu hue
    have hfr : frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) (t + T.Q.l.M • u) =
        frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t +
          T.Q.l.M • frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) u := by
      rw [frMapAdj_add', frMapAdj_nsmul']
    have hKu : IsHalf (cA D e) (T.Q.l.M • u) := fun a b => by
      rw [Matrix.smul_apply, nsmul_eq_mul, mul_left_comm, hue a b]
    have hhalf' : IsHalf (cA D e) (t + T.Q.l.M • u) ↔ IsHalf (cA D e) t := by
      constructor
      · intro h a b
        have := h a b
        rw [Matrix.add_apply, mul_add, hKu a b] at this
        exact add_right_cancel this
      · intro h a b
        rw [Matrix.add_apply, mul_add, h a b, hKu a b]
    show (if _ then _ else _) = (if _ then _ else _)
    rw [hfr]
    by_cases hc : IsHalf (cA D e) t ∧ IsIntM (frMapAdj (Vc D j) (Wc D j) (Rl.toRealDat.βV j) (Rl.toRealDat.βW j) t)
    · rw [if_pos ⟨hhalf'.2 hc.1, (isIntM_add_nsmul_iff hN' _).2 hc.2⟩, if_pos hc]
      exact omegaK_congr _ fun PP hPP => redM_add_nsmul PP hc.2 hN' _ (hMPg PP hPP)
    · rw [if_neg, if_neg hc]
      intro h'
      exact hc ⟨hhalf'.1 h'.1, (isIntM_add_nsmul_iff hN' _).1 h'.2⟩
  · intro t
    show (if _ then _ else _) ∈ _
    split_ifs
    · exact omegaK_mem _ _ _
    · exact Subfield.zero_mem _

end GlobalTheory.RefDatumLev
