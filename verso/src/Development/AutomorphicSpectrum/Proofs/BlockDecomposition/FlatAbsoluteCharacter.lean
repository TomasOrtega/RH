import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.FinStable
open NumberField IsDedekindDomain Matrix MeasureTheory Filter Topology
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.SmGL GlobalTheory.DiscSpec GlobalTheory.CompanionTheory.CTFin PositivityTheory.Rg.Rs PositivityTheory.Rg.Rs.InducedTensorMap
open PositivityTheory.Rg.BcB.E PositivityTheory.Rg.BcB.SpectralAccumulation GlobalTheory.CompanionTheory.LimV
open scoped ContDiff

noncomputable section

namespace GlobalTheory.CompanionTheory.LimV

open GlobalTheory.Mem.Chr.CharModel

section

variable {E : Type} [Field E] [NumberField E] [IsTotallyComplex E]

/- English proof (translation)
Establish `: GlobalTheory.Idele.idealOf t = 1`. Rewrite using `[← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]`. Introduce `v`. Establish `e` using `congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)`. Rewrite `e` using `[map_mul, map_one]`.

Establish `a1 : Valued.v ((t : Af E) v) ≤ 1` using `GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v`. Establish `a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1` using `GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v`. Use `le_antisymm a1 ?_` and prove the remaining obligations. Rewrite using `[← e]`. Conclude with `mul_le_of_le_one_right' a2`.

Simplify using `[logFin, this]`.
-/
theorem logFin_eq_zero_of_integral (t : (Af E)ˣ)
    (h1 : (t : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E)
    (h2 : ((t⁻¹ : (Af E)ˣ) : Af E) ∈ GroundTheory.Global.integralFiniteAdeles (𝓞 E) E) : logFin E t = 0 := by
  have : GlobalTheory.Idele.idealOf t = 1 := by
    rw [← GlobalTheory.Idele.smul_one_eq, GlobalTheory.Idele.smul_eq_self_iff t one_ne_zero]
    intro v
    have e := congrArg Valued.v (GlobalTheory.Idele.idele_apply_mul_inv t v)
    rw [map_mul, map_one] at e
    have a1 : Valued.v ((t : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h1 v
    have a2 : Valued.v (((t⁻¹ : (Af E)ˣ) : Af E) v) ≤ 1 := GroundTheory.Global.mem_integralFiniteAdeles.1 h2 v
    refine le_antisymm a1 ?_
    rw [← e]
    exact mul_le_of_le_one_right' a2
  simp [logFin, this]

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)` and prove the remaining obligations.
-/
theorem det_mem_of_entries {R : Type*} [CommRing R] (S : Subring R) {n : ℕ} (M : Matrix (Fin n) (Fin n) R)
    (h : ∀ a b, M a b ∈ S) : M.det ∈ S := by
  rw [Matrix.det_apply']
  refine S.sum_mem fun σ _ => S.mul_mem (intCast_mem S _) (S.prod_mem fun i _ => h _ _)

/- English proof (translation)
Take `⟨h1, h2⟩` from `(GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc`. Use `logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_` and prove the remaining obligations. Rewrite using `[← map_inv]`. Conclude with `det_mem_of_entries _ _ h2`.
-/
theorem logFin_det_of_mem {N : ℕ} {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logFin E (GeneralLinearGroup.det c) = 0 := by
  obtain ⟨h1, h2⟩ := (GroundTheory.Automorphic.AdelicGLn.mem_integralFiniteGL_iff E N).1 hc
  refine logFin_eq_zero_of_integral _ (det_mem_of_entries _ _ h1) ?_
  rw [← map_inv]
  exact det_mem_of_entries _ _ h2

/- English proof (translation)
Establish `h1 : finPart E (finId E u) = u` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(1 : Af E) - 1 + u = u`. Use the proof step `simp)`. Establish `h2 : infPart E (finId E u) = 1` using `Units.ext (by`. Express the relevant statement in the definitionally equal form `(1 : InfiniteAdeleRing E) - 0 + 0 = 1`.

Use the proof step `simp)`. Rewrite using `[logNorm, h1, h2, logInf_one, zero_sub]`.
-/
theorem logNorm_finId (u : (Af E)ˣ) : logNorm E (finId E u) = - logFin E u := by
  have h1 : finPart E (finId E u) = u := Units.ext (by
    change (1 : Af E) - 1 + u = u
    simp)
  have h2 : infPart E (finId E u) = 1 := Units.ext (by
    change (1 : InfiniteAdeleRing E) - 0 + 0 = 1
    simp)
  rw [logNorm, h1, h2, logInf_one, zero_sub]

/- English proof (translation)
Establish `hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E)` using `Matrix.det_of_mem_unitary k.2`. Establish `h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1` using `congrFun (Unitary.star_mul_self_of_mem hd) v`. Establish `h2` using `congrArg norm h`. Rewrite `h2` using `[norm_mul, norm_star, norm_one]`. Conclude with `(mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])`.
-/
theorem norm_det_unitary_at {N : ℕ} (k : Kinf E N) (v : InfinitePlace E) :
    ‖((GeneralLinearGroup.det (Unitary.toUnits k) : (Cinf E)ˣ) : Cinf E) v‖ = 1 := by
  have hd : (k : Matrix (Fin N) (Fin N) (Cinf E)).det ∈ unitary (Cinf E) := Matrix.det_of_mem_unitary k.2
  have h : star ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v) * (k : Matrix (Fin N) (Fin N) (Cinf E)).det v = 1 :=
    congrFun (Unitary.star_mul_self_of_mem hd) v
  have h2 := congrArg norm h
  rw [norm_mul, norm_star, norm_one] at h2
  exact (mul_self_eq_one_iff.1 h2).resolve_right (by linarith [norm_nonneg ((k : Matrix (Fin N) (Fin N) (Cinf E)).det v)])

/- English proof (translation)
Rewrite using `[cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc, Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]`. Simplify using the standard rewrite rules.
-/
theorem logNorm_det_cf (N : ℕ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    logNorm E (GeneralLinearGroup.det (cf N k c)) = 0 := by
  rw [cf, map_mul, logNorm_mul, det_infGL, det_finGL, Model.logNorm_infId, logNorm_finId, logFin_det_of_mem hc,
    Finset.sum_eq_zero fun v _ => by rw [norm_det_unitary_at, Real.log_one, mul_zero]]
  simp

/- English proof (translation)
Apply `Units.ext` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1`. Rewrite using `[logNorm_det_cf N k hc]`. Simplify using the standard rewrite rules.
-/
theorem chiDet_absC_cf (N : ℕ) (w : ℂ) (k : Kinf E N) {c : GL (Fin N) (Af E)} (hc : c ∈ KO E N) :
    chiDet N (GlobalTheory.CuspRep.Model.absC E w) (cf N k c) = 1 := by
  apply Units.ext
  change Complex.exp (w * (logNorm E (GeneralLinearGroup.det (cf N k c)) : ℂ)) = 1
  rw [logNorm_det_cf N k hc]
  simp

end

/- English proof (translation)
Introduce `E _ _ _ N w`. Use `⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]`. Establish `h : absFn (E` using `E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by`. Rewrite using `[mulChi_apply]`.

Simplify using `[absFn, oneFn]`. Rewrite using `[h]`. Conclude with `(mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2`.
-/
theorem absFn_flat : ∀ {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (N : ℕ) (w : ℂ),
    FlatFn (absFn (E := E) N w) := by
  intro E _ _ _ N w
  refine ⟨fun x => Units.ne_zero _, fun x k c hc => ?_, ?_⟩
  · simp only [absFn, map_mul, chiDet_absC_cf N w k hc, mul_one]
  · have h : absFn (E := E) N w = (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).1 := funext fun x => by
      rw [mulChi_apply]
      simp [absFn, oneFn]
    rw [h]
    exact (mulChi N (GlobalTheory.CuspRep.Model.absC E w) (oneFn E N)).2

end GlobalTheory.CompanionTheory.LimV

end
