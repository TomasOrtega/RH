import Mathlib
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.HasShape
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrameAdjointChartBijectiveConjugateHalfStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.GramMapMulInv
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S MeasureTheory IsDedekindDomain NumberField Matrix
open Formalism.L2.Theta Formalism.L2.DIV Formalism.L2.Indef
open Formalism.IndefR.Lev Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.Cx Formalism.IndefR.Links
open scoped TensorProduct InnerProductSpace
attribute [local instance] Formalism.BasicNotions.Host.cmStar
open GlobalTheory.DownLift
open GlobalTheory.DownLift.GenFinite
open GlobalTheory.DownLift.SplitCoef

noncomputable section

set_option maxHeartbeats 800000
set_option synthInstance.maxHeartbeats 400000

namespace GlobalTheory.DownLift.SplitCoef

variable {D : D7}

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]`.
-/
theorem isHalf_sub' {m n : ℕ} {e : AE D} {u v : Mx D m n} (hu : IsHalf e u) (hv : IsHalf e v) : IsHalf e (u - v) :=
  fun i j => by rw [Matrix.sub_apply, mul_sub, hu i j, hv i j]

/- English proof (translation)
Introduce `i j` and use `by rw [Matrix.smul_apply, mul_smul_comm, hu i j]`.
-/
theorem isHalf_nsmul'' {m n : ℕ} {e : AE D} {u : Mx D m n} (hu : IsHalf e u) (k : ℕ) : IsHalf e (k • u) :=
  fun i j => by rw [Matrix.smul_apply, mul_smul_comm, hu i j]

/- English proof (translation)
The claim follows from `(AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_nsmul n x`.
-/
theorem frMapAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    (n : ℕ) (x : WO S T) : frMapAdj S T βS βT (n • x) = n • frMapAdj S T βS βT x :=
  (AddMonoidHom.mk' (frMapAdj S T βS βT) (GlobalTheory.PlaceVec.frMapAdj_add S T βS βT)).map_nsmul n x

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [rdAdj, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.map_apply, Matrix.add_apply, map_add]`.
-/
theorem rdAdj_add (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x + y) = rdAdj S T βS βT φ x + rdAdj S T βS βT φ y := by
  ext i j
  simp only [rdAdj, GlobalTheory.PlaceVec.frMapAdj_add, Matrix.map_apply, Matrix.add_apply, map_add]

/- English proof (translation)
The claim follows from `(AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_nsmul n x`.
-/
theorem rdAdj_nsmul (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (n : ℕ) (x : WO S T) :
    rdAdj S T βS βT φ (n • x) = n • rdAdj S T βS βT φ x :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_nsmul n x

/- English proof (translation)
The claim follows from `(AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_sub x y`.
-/
theorem rdAdj_sub (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D))
    {v : HeightOneSpectrum (𝓞 D.host.F)} (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (x y : WO S T) :
    rdAdj S T βS βT φ (x - y) = rdAdj S T βS βT φ x - rdAdj S T βS βT φ y :=
  (AddMonoidHom.mk' (rdAdj S T βS βT φ) (rdAdj_add S T βS βT φ)).map_sub x y

/- English proof (translation)
Establish `hne : (m : GlobalTheory.SplitHecke.Ov D v) ≠ 0`. Introduce `h`. Establish `h1` using `congrArg (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) h`. Rewrite `h1` using `[map_natCast, map_zero, ← map_natCast (algebraMap D.host.F (Fv D.host.F v))]`. Establish `h2` using `(algebraMap D.host.F (Fv D.host.F v)).injective (h1.trans (map_zero _).symm)`.

Conclude with `hm.ne' (by exact_mod_cast h2)`. Take `⟨N, u, hu⟩` from `IsDiscreteValuationRing.associated_pow_irreducible hne hϖ`. Conclude with `⟨N, (u : GlobalTheory.SplitHecke.Ov D v), hu.symm⟩`.
-/
theorem exists_natCast_dvd_pow (v : HeightOneSpectrum (𝓞 D.host.F)) {ϖ : GlobalTheory.SplitHecke.Ov D v} (hϖ : Irreducible ϖ)
    (m : ℕ) (hm : 0 < m) : ∃ N : ℕ, (m : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N := by
  have hne : (m : GlobalTheory.SplitHecke.Ov D v) ≠ 0 := by
    intro h
    have h1 := congrArg (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) h
    rw [map_natCast, map_zero, ← map_natCast (algebraMap D.host.F (Fv D.host.F v))] at h1
    have h2 := (algebraMap D.host.F (Fv D.host.F v)).injective (h1.trans (map_zero _).symm)
    exact hm.ne' (by exact_mod_cast h2)
  obtain ⟨N, u, hu⟩ := IsDiscreteValuationRing.associated_pow_irreducible hne hϖ
  exact ⟨N, (u : GlobalTheory.SplitHecke.Ov D v), hu.symm⟩

end GlobalTheory.DownLift.SplitCoef

namespace GlobalTheory.DownLift.SplitCoef

/- English proof (translation)
Introduce `D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ`. Take `⟨hsurj, hinj, hint, -⟩` from `GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι he hL`. Take `⟨hsupp, k, hk, hinv, hkΛ⟩` from `hΦ`. Take `⟨K1, hK1, hdown⟩` from `GlobalTheory.PlaceVec.frMapAdj_down S T βS βT`. Take `⟨K2, hK2, hmem⟩` from `GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT`.

Take `⟨L1, hL1, hlat⟩` from `GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg`. Take `⟨L2, hL2, hup⟩` from `GlobalTheory.PlaceVec.frMapAdj_up S T βS βT`. Establish `hce : infPart D (cA D e) = 0` using `GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.SplitScalar.infPart_splitIdem he.1)`. Take `⟨N, hN⟩` from `exists_natCast_dvd_pow v hϖ (k * (K2 * K1) * (L2 * (L1 * k))) (by positivity)`. Establish `hA : ((k * (K2 * K1) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N` using `(Nat.cast_dvd_cast (Dvd.intro _ rfl)).trans hN`.

Establish `hM : ((L2 * (L1 * k) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N` using `(Nat.cast_dvd_cast (Dvd.intro_left _ rfl)).trans hN`. Use `⟨N, ?_, ?_⟩` and prove the remaining obligations. Introduce `x x' hx hx' z hxz`. Take `⟨w, hw⟩` from `hA`. Take `⟨t, ht, hrt⟩` from `hsurj ((w • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))`.

Establish `htI : IsIntM (frMapAdj S T βS βT t)` using `(hint t ht).2 ⟨w • z, hrt⟩`. Establish `h1` using `hdown t htI`. Rewrite `h1` using `[← GlobalTheory.PlaceVec.map_toEAf_nsmul]`. Establish `h0 : (K1 • t).map (infPart D) = 0`. Use extensionality with `i j`.

Rewrite using `[Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← ht i j, map_mul, hce, zero_mul, smul_zero, Matrix.zero_apply]`. Establish `h2` using `hmem _ h0 h1`. Establish `hu : IsHalf (cA D e) (K2 • K1 • t)` using `isHalf_nsmul'' (isHalf_nsmul'' ht _) _`. Establish `key : x' - x = k • (K2 • K1 • t)`. Use `hinj _ _ (isHalf_sub' hx' hx) (isHalf_nsmul'' hu _) ?_` and prove the remaining obligations.

Rewrite using `[rdAdj_sub, hxz, add_sub_cancel_left, rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul, hrt, hw]`. Use extensionality with `i j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Establish `: x' = x + k • (K2 • K1 • t)` using `by rw [← key]; abel`. Rewrite using `[this, hinv _ h2 hu x]`. Introduce `x hx`. Establish `hhalf` using `hsupp x hx`. Establish `h1` using `hlat _ (hkΛ x hx)`.

Rewrite `h1` using `[← GlobalTheory.PlaceVec.map_toEAf_nsmul]`. Establish `h2` using `hup _ h1`. Rewrite `h2` using `[← frMapAdj_nsmul]`. Take `⟨z0, hz0⟩` from `(hint _ (isHalf_nsmul'' (isHalf_nsmul'' (isHalf_nsmul'' hhalf k) L1) L2)).1 h2`. Rewrite `hz0` using `[rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul]`.

Take `⟨w', hw'⟩` from `hM`. Use `⟨w' • z0, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Establish `hij` using `congrFun (congrFun hz0 i) j`. Simplify using `only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at hij ⊢`.

Rewrite using `[hw', map_mul, map_mul, ← hij, map_natCast]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem sbHalf_locConst_cptSupp : ∀ (D : D7) (S T : HSp D) (βS : GL (Fin S.rank) (Formalism.IndefR.Lev.EAf D)) (βT : GL (Fin T.rank) (Formalism.IndefR.Lev.EAf D)) (e : AE D) (PP : Pl D.host.E) (v : HeightOneSpectrum (𝓞 D.host.F)) (φ : Formalism.IndefR.Lev.EAf D →+* Fv D.host.F v) (ι : kP PP ≃+* IsLocalRing.ResidueField (GlobalTheory.SplitHecke.Ov D v)), Formalism.L2.NTheta.IsIdemAt e PP → LevChart e PP v φ ι → ∀ (ΛS : Submodule (𝓞 D.host.E) (Fin S.rank → D.host.E)) (ΛT : Submodule (𝓞 D.host.E) (Fin T.rank → D.host.E)), Submodule.IsLattice D.host.E ΛS → Submodule.IsLattice D.host.E ΛT → ∀ Φ : WO S T → ℂ, IsSBHalf (cA D e) (latH S T ΛS ΛT) Φ → ∀ ϖ : (GlobalTheory.SplitHecke.Ov D v), Irreducible ϖ → ∃ N : ℕ, (∀ x x' : WO S T, IsHalf (cA D e) x → IsHalf (cA D e) x' → ∀ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), rdAdj S T βS βT φ x' = rdAdj S T βS βT φ x + (ϖ ^ N • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) → Φ x' = Φ x) ∧ ∀ x : WO S T, Φ x ≠ 0 → ∃ z : Matrix (Fin S.rank) (Fin T.rank) (GlobalTheory.SplitHecke.Ov D v), algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v) (ϖ ^ N) • rdAdj S T βS βT φ x = z.map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)) := by
  intro D S T βS βT e PP v φ ι he hL ΛS ΛT hS hT Φ hΦ ϖ hϖ
  obtain ⟨hsurj, hinj, hint, -⟩ := GlobalTheory.T.frameAdjoint_chart_bijective_conjugateHalf D S T βS βT e PP v φ ι he hL
  obtain ⟨hsupp, k, hk, hinv, hkΛ⟩ := hΦ
  obtain ⟨K1, hK1, hdown⟩ := GlobalTheory.PlaceVec.frMapAdj_down S T βS βT
  obtain ⟨K2, hK2, hmem⟩ := GlobalTheory.PlaceVec.exists_nsmul_int_mem_latO hS hT
  obtain ⟨L1, hL1, hlat⟩ := GlobalTheory.PlaceVec.exists_nsmul_latO_int (S := S) (T := T) hS.fg hT.fg
  obtain ⟨L2, hL2, hup⟩ := GlobalTheory.PlaceVec.frMapAdj_up S T βS βT
  have hce : infPart D (cA D e) = 0 := GlobalTheory.PlaceVec.infPart_cA (GlobalTheory.SplitScalar.infPart_splitIdem he.1)
  obtain ⟨N, hN⟩ := exists_natCast_dvd_pow v hϖ (k * (K2 * K1) * (L2 * (L1 * k)))
    (by positivity)
  have hA : ((k * (K2 * K1) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro _ rfl)).trans hN
  have hM : ((L2 * (L1 * k) : ℕ) : GlobalTheory.SplitHecke.Ov D v) ∣ ϖ ^ N :=
    (Nat.cast_dvd_cast (Dvd.intro_left _ rfl)).trans hN
  refine ⟨N, ?_, ?_⟩
  · intro x x' hx hx' z hxz
    obtain ⟨w, hw⟩ := hA
    obtain ⟨t, ht, hrt⟩ := hsurj ((w • z).map (algebraMap (GlobalTheory.SplitHecke.Ov D v) (Fv D.host.F v)))
    have htI : IsIntM (frMapAdj S T βS βT t) := (hint t ht).2 ⟨w • z, hrt⟩
    have h1 := hdown t htI
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h0 : (K1 • t).map (infPart D) = 0 := by
      ext i j
      rw [Matrix.map_apply, Matrix.smul_apply, map_nsmul, ← ht i j, map_mul, hce, zero_mul, smul_zero, Matrix.zero_apply]
    have h2 := hmem _ h0 h1
    have hu : IsHalf (cA D e) (K2 • K1 • t) := isHalf_nsmul'' (isHalf_nsmul'' ht _) _
    have key : x' - x = k • (K2 • K1 • t) := by
      refine hinj _ _ (isHalf_sub' hx' hx) (isHalf_nsmul'' hu _) ?_
      rw [rdAdj_sub, hxz, add_sub_cancel_left, rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul, hrt, hw]
      ext i j
      simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul, map_mul, map_natCast]
      push_cast
      ring
    have : x' = x + k • (K2 • K1 • t) := by rw [← key]; abel
    rw [this, hinv _ h2 hu x]
  · intro x hx
    have hhalf := hsupp x hx
    have h1 := hlat _ (hkΛ x hx)
    rw [← GlobalTheory.PlaceVec.map_toEAf_nsmul] at h1
    have h2 := hup _ h1
    rw [← frMapAdj_nsmul] at h2
    obtain ⟨z0, hz0⟩ := (hint _ (isHalf_nsmul'' (isHalf_nsmul'' (isHalf_nsmul'' hhalf k) L1) L2)).1 h2
    rw [rdAdj_nsmul, rdAdj_nsmul, rdAdj_nsmul] at hz0
    obtain ⟨w', hw'⟩ := hM
    refine ⟨w' • z0, ?_⟩
    ext i j
    have hij := congrFun (congrFun hz0 i) j
    simp only [Matrix.map_apply, Matrix.smul_apply, smul_eq_mul, nsmul_eq_mul] at hij ⊢
    rw [hw', map_mul, map_mul, ← hij, map_natCast]
    push_cast
    ring

end GlobalTheory.DownLift.SplitCoef

end
