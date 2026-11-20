import Mathlib
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.AllRowsRhoX
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.DstarIdxPf
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.IdxProd
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.LocalVolumeIndices.HelpSng
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.BridgeFinK
import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.MassDataXRed

noncomputable section

namespace Formalism.L2.SG.Pf.RhoSurjW

open NumberField IsDedekindDomain Matrix
open scoped TensorProduct
open Formalism.BasicNotions Formalism.L2.SG.HidaSetting Formalism.L2.SG.TypedSets Formalism.L2.SG.AdBridge PI.MassDataKppVolLemmas
  Formalism.L2.SG.Pf.AllRowsRhoX Formalism.L2.SG.AllRowsOf Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.L2.SG.Sub

section Loc

variable {D : D7} (X : HidaSetting D) (hb : AdBridgeIso X.B.I)

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV, map_sub]`.
-/
theorem vecV_sub (v : HeightOneSpectrum (𝓞 X.B.I.F))
    (a b : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (a - b) = PI.FinKW.vecV X.B.I v a - PI.FinKW.vecV X.B.I v b := by
  funext i
  simp [PI.FinKW.vecV, map_sub]

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[PI.FinKW.vecV]`.
-/
theorem vecV_nsmul (v : HeightOneSpectrum (𝓞 X.B.I.F)) (c : ℕ)
    (a : Fin X.B.I.n → X.B.I.E ⊗[X.B.I.F] Formalism.MainNotions.S.Af X.B.I.F) :
    PI.FinKW.vecV X.B.I v (c • a) = c • PI.FinKW.vecV X.B.I v a := by
  funext i
  simp [PI.FinKW.vecV]

/- English proof (translation)
Rewrite using `[X.g_eq]`. Unfold `gOf`. Use `split_ifs`. Conclude with `⟨_, rfl⟩`. Conclude with `⟨D.host.g 0, mul_comm _ _⟩`.
-/
theorem exists_cofactor (p : TypX X) : ∃ c : ℕ, (X.B.g : ℕ) = gOf p * c := by
  rw [X.g_eq]
  unfold gOf
  split_ifs
  · exact ⟨_, rfl⟩
  · exact ⟨D.host.g 0, mul_comm _ _⟩

/- English proof (translation)
Establish `hKf` using `(Bridge_mem_Kf_iff X.B.I hb x).2 hx.1`. Rewrite `hKf` using `[Kf, Subgroup.mem_iInf]`. Use `⟨hKf p.1, ?_⟩` and prove the remaining obligations. Introduce `y hy`. Take `⟨c, hc⟩` from `exists_cofactor X p`.

Take `⟨u, huv, huw⟩` from `PI.FinKW.local_vector_lift X.B.I p.1 y`. Establish `huL : u ∈ X.B.I.Lf` using `PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by`. Distinguish the cases in `hw : w = p.1`. Substitute `hw` using the available equality. Rewrite using `[huv]`.

Conclude with `hy`. Rewrite using `[huw w hw]`. Conclude with `zero_mem _`. Take `⟨z, hzL, hz⟩` from `hx.2 u huL`. Establish `hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x))` using `(toHA_isBridge X.B.I hb (1, x)).2`.

Use `⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩` and prove the remaining obligations. Establish `e` using `congrArg (PI.FinKW.vecV X.B.I p.1) hz`. Rewrite `e` using `[Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul, vecV_nsmul]`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]`. Conclude with `e`.
-/
theorem piV_mem_KgX (x : X.B.I.Gf) (hx : x ∈ X.B.I.Kg X.B.g) (p : TypX X) :
    piV X.B.I p.1 (tf X.B.I hb x) ∈ MassDataIdxSteps.KgX X p := by
  have hKf := (Bridge_mem_Kf_iff X.B.I hb x).2 hx.1
  rw [Kf, Subgroup.mem_iInf] at hKf
  refine ⟨hKf p.1, ?_⟩
  intro y hy
  obtain ⟨c, hc⟩ := exists_cofactor X p
  obtain ⟨u, huv, huw⟩ := PI.FinKW.local_vector_lift X.B.I p.1 y
  have huL : u ∈ X.B.I.Lf := PI.FinKW.memLocFrom_of PI.FinKW.local_vector_injective X.B.I u fun w => by
    by_cases hw : w = p.1
    · subst hw
      rw [huv]
      exact hy
    · rw [huw w hw]
      exact zero_mem _
  obtain ⟨z, hzL, hz⟩ := hx.2 u huL
  have hfx : X.B.I.fmat x = ofHAFin X.B.I (toHA X.B.I hb (1, x)) := (toHA_isBridge X.B.I hb (1, x)).2
  refine ⟨c • PI.FinKW.vecV X.B.I p.1 z, nsmul_mem (PI.FinKW.LocTo.mem_local_lattice_iff X.B.I z hzL p.1) c, ?_⟩
  have e := congrArg (PI.FinKW.vecV X.B.I p.1) hz
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, vecV_sub, hfx, PI.FinKW.vecV_mulVec, huv, Nat.cast_smul_eq_nsmul,
    vecV_nsmul] at e
  rw [Matrix.sub_mulVec, Matrix.one_mulVec, Nat.cast_smul_eq_nsmul, smul_smul, ← hc]
  exact e

end Loc

section Count

variable {D : D7} (X : HidaSetting D)

/- English proof (translation)
Establish `hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) = (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f * (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f`. Rewrite using `[Nat.card_pi, Nat.cast_prod]`. Rewrite using `[← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]`.

Both sides reduce to the same expression. Establish `hG : (Nat.card (G0g D.nd) : ℝ) = (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f * (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f`. Rewrite using `[Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]`. Establish `e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) = (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f` using `fun k => by`. Rewrite using `[Finset.prod_const, Finset.card_univ, D.nd.card_PlG]`.

Both sides reduce to the same expression. Conclude with `congrArg₂ (· * ·) (e 0) (e 1)`. Conclude with `hT.trans hG.symm` after adjusting the coercions.
-/
theorem card_target :
    Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) = Nat.card (G0g D.nd) := by
  classical
  have hT : (Nat.card (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod]
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.prod_typ X (fun g => (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod g)) : ℝ))]
    refine Finset.prod_congr rfl fun p _ => ?_
    rw [← Formalism.L2.SG.Pf.DstarIdxPf.ggC_eq D.R (gOf p)]
    rfl
  have hG : (Nat.card (G0g D.nd) : ℝ) =
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 0))) : ℝ) ^ D.R.f *
      (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g 1))) : ℝ) ^ D.R.f := by
    rw [Nat.card_pi, Nat.cast_prod, Fintype.prod_sigma, Fin.prod_univ_two]
    have e : ∀ k : Fin 2, ∏ _v : D.nd.PlG k, (Nat.card (GL (Fin D.R.r) (ZMod (D.host.g k))) : ℝ) =
        (Nat.card (GL (Fin (D.R.k + D.R.m - 1)) (ZMod (D.host.g k))) : ℝ) ^ D.R.f := fun k => by
      rw [Finset.prod_const, Finset.card_univ, D.nd.card_PlG]
      rfl
    exact congrArg₂ (· * ·) (e 0) (e 1)
  exact_mod_cast hT.trans hG.symm

end Count

/- English proof (translation)
Introduce `D X`. Set `hb : AdBridgeIso X.B.I` to `(Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1`. Establish `hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p`. Introduce `p`. Take `⟨K, hKs, -, -, -⟩` from `Formalism.L2.SG.Pf.MassDataX.stK_holds X p`.

Establish `e : KvS X p = K`. Establish `e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1` using `hKs`. Rewrite using `[KvS, ← e, Subgroup.closure_eq]`. Rewrite using `[e]`. Conclude with `hKs`.

Use `choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)`. Set `ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))` to `(MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)`. Establish `hψ : Function.Surjective ψ`. Introduce `t`. Use `choose a ha using fun p => hρ p (t p)`.

Take `⟨k, hk⟩` from `phiK_surjective X hb single_component_surjective a`. Use `⟨k, funext fun p => ?_⟩` and prove the remaining obligations. Use `show ρ p (phiK X hb k p) = t p`. Rewrite using `[hk]`. Conclude with `ha p`.

Set `ι : KSub X.B.I → KsetSub X.B.I` to `fun x => ⟨x.1, x.2⟩`. Establish `hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y)`. Introduce `x y hxy`. Establish `h1 : rhoX X (x⁻¹ * y) = 1` using `by rw [map_mul, map_inv, hxy, inv_mul_cancel]`. Establish `hg` using `(rhoX_eq_one_iff X _).1 h1`.

Establish `h2 : ψ (ι (x⁻¹ * y)) = 1`. Use function extensionality and compare the values at `p`. Use `show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1`. Conclude with `(hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)`. Establish `h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y` using `rfl`.

Rewrite `h2` using `[h3, map_mul, map_inv, inv_mul_eq_one]`. Conclude with `h2`. Establish `: ∀ k : Fin 2, NeZero (D.host.g k)` using `fun k => ⟨(D.host.g_prime k).ne_zero⟩`. Set `f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)))` to `fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)`. Establish `hf : Function.Surjective f`.

Introduce `t`. Take `⟨k, hk⟩` from `hψ t`. Set `x : KSub X.B.I` to `⟨k.1, k.2⟩`. Set `r : (rhoX X).range` to `⟨rhoX X x, x, rfl⟩`. Conclude with `⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩`.

Establish `hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range`. Rewrite using `[← RhoSurjW.card_target X]`. Conclude with `Nat.card_le_card_of_surjective f hf`. Conclude with `MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)`.
-/
theorem reduction_map_surjective : RhoSurj := by
  intro D X
  classical
  let hb : AdBridgeIso X.B.I := (Formalism.L2.SG.Closed.adelic_isomorphism_statement X.B.I).1
  have hK : ∀ p : TypX X, ((KvS X p : Subgroup _) : Set (MassDataIdxSteps.HAp X p)) = MassDataIdxSteps.KvX X p := by
    intro p
    obtain ⟨K, hKs, -, -, -⟩ := Formalism.L2.SG.Pf.MassDataX.stK_holds X p
    have e : KvS X p = K := by
      have e : (K : Set _) = Kv X.B.I.cm.sig X.B.I.J (lamS X) p.1 := hKs
      rw [KvS, ← e, Subgroup.closure_eq]
    rw [e]
    exact hKs
  choose ρ hρ hker using fun p : TypX X => Formalism.L2.SG.Pf.MassDataX.stRed_holds X p (KvS X p) (hK p)
  let ψ : KsetSub X.B.I →* ∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p)) :=
    (MonoidHom.pi fun p => (ρ p).comp (Pi.evalMonoidHom (fun p => KvS X p) p)).comp (phiK X hb)
  have hψ : Function.Surjective ψ := by
    intro t
    choose a ha using fun p => hρ p (t p)
    obtain ⟨k, hk⟩ := phiK_surjective X hb single_component_surjective a
    refine ⟨k, funext fun p => ?_⟩
    show ρ p (phiK X hb k p) = t p
    rw [hk]
    exact ha p
  let ι : KSub X.B.I → KsetSub X.B.I := fun x => ⟨x.1, x.2⟩
  have hψι : ∀ x y : KSub X.B.I, rhoX X x = rhoX X y → ψ (ι x) = ψ (ι y) := by
    intro x y hxy
    have h1 : rhoX X (x⁻¹ * y) = 1 := by rw [map_mul, map_inv, hxy, inv_mul_cancel]
    have hg := (rhoX_eq_one_iff X _).1 h1
    have h2 : ψ (ι (x⁻¹ * y)) = 1 := by
      funext p
      show ρ p (phiK X hb (ι (x⁻¹ * y)) p) = 1
      exact (hker p _).2 (RhoSurjW.piV_mem_KgX X hb _ hg p)
    have h3 : ι (x⁻¹ * y) = (ι x)⁻¹ * ι y := rfl
    rw [h3, map_mul, map_inv, inv_mul_eq_one] at h2
    exact h2
  have : ∀ k : Fin 2, NeZero (D.host.g k) := fun k => ⟨(D.host.g_prime k).ne_zero⟩
  let f : (rhoX X).range → (∀ p : TypX X, GL (Formalism.FourierDecayAlt.S3.Idx D.R.rS D.R.k) (ZMod (gOf p))) :=
    fun r => ψ (ι (MonoidHom.mem_range.1 r.2).choose)
  have hf : Function.Surjective f := by
    intro t
    obtain ⟨k, hk⟩ := hψ t
    let x : KSub X.B.I := ⟨k.1, k.2⟩
    let r : (rhoX X).range := ⟨rhoX X x, x, rfl⟩
    exact ⟨r, (hψι _ x (MonoidHom.mem_range.1 r.2).choose_spec).trans hk⟩
  have hle : Nat.card (G0g D.nd) ≤ Nat.card (rhoX X).range := by
    rw [← RhoSurjW.card_target X]
    exact Nat.card_le_card_of_surjective f hf
  exact MonoidHom.range_eq_top.1 (Subgroup.eq_top_of_le_card _ hle)

end Formalism.L2.SG.Pf.RhoSurjW
