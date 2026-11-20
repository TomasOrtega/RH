import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.InclLSmulCoord
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BdRpToBdR
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemSpanFiltrationZeroOfIntegralTensorLatticeStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ImageDeRhamEqEisensteinPowMulOfComponentsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.CoordEPowBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.EisensteinPowSmulValueEqSumBasisStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.BreuilKisinValueMulEisensteinPowEqSumStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.MemFilPIffEvPt
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per
open GlobalTheory.BKGal.HatVal
open scoped GlobalTheory.BKGal.HatVal

noncomputable section

namespace GlobalTheory.BKGal.HatVal

variable {l : ℕ} [Fact l.Prime] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [NormedField K] [NormedAlgebra ℚ_[l] K] [Algebra O K] {G : Type} [Group G] [TopologicalSpace G]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [smul_zero, map_zero]`. Consider the case `tmul s x`. Simplify using `only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply, smul_eq_mul, map_mul]`. Consider the case `add x y hx hy => simp only [smul_add, map_add, hx, hy]`.
-/
theorem TWincl_smul' {R R' : Type} [CommRing R] [CommRing R'] [Algebra O R] [Algebra O R'] (f : R →ₐ[O] R')
    (T : LocLat G ℚ_[l] K O) (r : R) (z : TW R T) : TWincl f T (r • z) = f r • TWincl f T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [smul_zero, map_zero]
  | tmul s x =>
    simp only [TWincl, smul_tmul', TensorProduct.map_tmul, AlgHom.toLinearMap_apply, LinearMap.id_apply,
      smul_eq_mul, map_mul]
  | add x y hx hy => simp only [smul_add, map_add, hx, hy]

/- English proof (translation)
Proceed by induction on `z using TensorProduct.induction_on with`. Consider the case `zero => simp only [map_zero]`. Consider the case `tmul s x => rfl`. Consider the case `add x y hx hy => simp only [map_add, hx, hy]`.
-/
theorem TWincl_TWincl {R R' R'' : Type} [CommRing R] [CommRing R'] [CommRing R''] [Algebra O R] [Algebra O R']
    [Algebra O R''] (f : R →ₐ[O] R') (g : R' →ₐ[O] R'') (T : LocLat G ℚ_[l] K O) (z : TW R T) :
    TWincl g T (TWincl f T z) = TWincl (g.comp f) T z := by
  induction z using TensorProduct.induction_on with
  | zero => simp only [map_zero]
  | tmul s x => rfl
  | add x y hx hy => simp only [map_add, hx, hy]

end GlobalTheory.BKGal.HatVal

open GlobalTheory.BKGal.HatVal in

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C`. Use `haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite`. Use `haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K`. Take `⟨ζ, ε, h0, -, hz1, hr⟩` from `GlobalTheory.MemLoc.exists_zeta_eps l`. Establish `he : ε.untilt = 1` using `Subtype.ext (by`.

Use `hr 0` as an intermediate fact. Rewrite `this` using `[h0, map_one]`. Conclude with `this)`. Establish `hE : GlobalTheory.MemLoc.IsEps ε` using `⟨he, fun hh => hz1 (by`. Apply `(algebraMap (Om l) ℂ_[l]).injective` to reduce the goal to its premises.

Rewrite using `[← hr 1, map_one]`. Conclude with `congrArg Subtype.val hh)⟩`. Establish `hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε`. Rewrite using `[← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]`. Establish `hEps : IsEps ε` using `⟨he, _, hδl, hE.2⟩`.

Use `set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ`. Establish `hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0`. Express the relevant statement in the definitionally equal form `(Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0`. Rewrite using `[map_sub, map_one, WittVector.fontaineTheta_teichmuller]`. Introduce `h`.

Apply `hE.2` to reduce the goal to its premises. Rewrite using `[← sub_eq_zero]`. Conclude with `Subtype.ext h`. Establish `hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η)))`. Establish `h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η))`.

Rewrite using `[map_pow]`. Conclude with `((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by`. Rewrite using `[(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]`. Conclude with `hθν)).pow η`. Use `h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)` as an intermediate fact.

Rewrite `this` using `[Algebra.TensorProduct.includeRight_apply]`. Conclude with `this`. Establish `hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))))`. Establish `hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)}`. Rewrite using `[ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]`.

Conclude with `Ideal.subset_span rfl`. Take `⟨w, hw⟩` from `Ideal.mem_span_singleton'.1 hxi`. Establish `hu` using `GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE`. Rewrite `hu` using `[← hw, map_mul, map_mul]`. Establish `h1` using `isUnit_of_mul_isUnit_right hu`.

Use `h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)` as an intermediate fact. Rewrite `this` using `[Algebra.TensorProduct.includeRight_apply]`. Conclude with `this`. Use `choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl`. Take `⟨s, hs, hσv⟩` from `GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc`.

Establish `hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K`. Introduce `j τ`. Establish `h1 : y τ j ∈ invE l e (A O K)` using `mem_tot.1 hy τ j`. Take `⟨n, hn⟩` from `h1`. Establish `h2 : (σ.1 - y) τ j ∈ Rpi O K l e` using `mem_tot.1 hσy τ j`.

Establish `h3 : E K l e ^ η * y τ j ∈ Rpi O K l e`. Establish `: E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j`. Rewrite using `[hs, Pi.sub_apply, Pi.sub_apply]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`.

Conclude with `sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)`. Use `mem_A_of_E_pow_mul_mem l e n h3 ?_` and prove the remaining obligations. Establish `hn' : E K l e ^ n * y τ j ∈ A O K` using `by rwa [coe_EIn] at hn`. Rewrite using `[mul_left_comm]`. Conclude with `mul_mem (pow_mem (E_mem l e _) η) hn'`.

Use `set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef`. Establish `hbv` using `GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)`. Establish `hAS : A O K ≤ invL l (S O K e)` using `le_trans (A_le_S l e) (le_away _ _)`. Use `set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef`. Establish `hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r` using `fun j τ => ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by`.

Rewrite using `[hρdef]`. Simplify using `only [Subalgebra.coe_sub, hs, Pi.sub_apply]`. Use the proof step `ring⟩`. Establish `hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j))` using `fun j => (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))`. Establish `key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) • (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i))`.

Rewrite using `[smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[← sub_smul, ← hiBY j, ← map_sub]`. Both sides reduce to the same expression. Apply `GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C` to reduce the goal to its premises.

Use `set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD`. Take `⟨v, hv⟩` from `hνD.exists_left_inv`. Establish `hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O)` using `AlgHom.ext (iotaO_toB C)`. Establish `hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) = TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j))`. Introduce `j`.

Establish `h1` using `congrArg (TWincl (iotaO O C) T) (hz j)`. Rewrite `h1` using `[TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[map_mul, mul_smul, h1]`. Use `_ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]`.

Use `choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)`. Establish `hE' : dRO l O EAD ^ (H + η) = iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η))`. Rewrite using `[map_pow, iotaO_toB]`. Establish `hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j))` using `by conv_lhs => rw [hE', ← TWincl_smul', key, map_sum] conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations.

Rewrite using `[TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]`. Use `congr 2`. Expand and normalize the polynomial expressions, which then agree. Conclude with `⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩`.
-/
theorem GlobalTheory.BKGal.value_hat_mem_filZero : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e), l ≠ 2 → ∀ (ι : Type) [Fintype ι] [DecidableEq ι] (η H : ℕ) (D : BKDat O K l e a ι η H) (T : LocLat (Gl l) ℚ_[l] K O) (R : GalDat t ϖ (sQ l) D T), ∀ (σ : D.MMl) (y : Vec K a ι) (hy : y ∈ ME D.toPhiMod), σ.1 - y ∈ D.Man → ∀ b₂, IsCrisVal t ϖ D.toPhiMod R.jB (toW t ϖ D.toPhiMod ⟨y, hy⟩) b₂ → ∀ C : GlobalTheory.MemLoc.Core l, R.jB (toBcris t ϖ D.toPhiMod σ) - b₂ ∈ Submodule.span O {w : TW (OB l O) T | ∃ (β : Per.Bcris l) (x : ↥T.L.T), C.ι β ∈ Per.FilD l 0 ∧ w = ((1 : O) ⊗ₜ[ℤ_[l]] β) ⊗ₜ[O] x} := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ hl2 ι _ _ η H D T R σ y hy hσy b₂ hb₂ C
  haveI : FiniteDimensional ℚ_[l] K := (inferInstance : TameDescentExponentData K l e a).finite
  haveI : CompleteSpace K := FiniteDimensional.complete ℚ_[l] K

  obtain ⟨ζ, ε, h0, -, hz1, hr⟩ := GlobalTheory.MemLoc.exists_zeta_eps l
  have he : ε.untilt = 1 := Subtype.ext (by
    have := hr 0
    rw [h0, map_one] at this
    exact this)
  have hE : GlobalTheory.MemLoc.IsEps ε := ⟨he, fun hh => hz1 (by
    apply (algebraMap (Om l) ℂ_[l]).injective
    rw [← hr 1, map_one]
    exact congrArg Subtype.val hh)⟩
  have hδl : ((frobeniusEquiv (Per.Fl l) l).symm ε) ^ l = ε := by
    rw [← frobenius_def, ← frobeniusEquiv_apply, RingEquiv.apply_symm_apply]
  have hEps : IsEps ε := ⟨he, _, hδl, hE.2⟩
  set δ := (frobeniusEquiv (Per.Fl l) l).symm ε with hδ
  have hθν : (Per.θ l (muOf δ) : ℂ_[l]) ≠ 0 := by
    change (Per.θ l (Per.tm δ - 1) : ℂ_[l]) ≠ 0
    rw [map_sub, map_one, WittVector.fontaineTheta_teichmuller]
    intro h
    apply hE.2
    rw [← sub_eq_zero]
    exact Subtype.ext h

  have hνD : IsUnit (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) := by
    have h1 : IsUnit (GlobalTheory.MemLoc.aDp l (muOf δ ^ η)) := by
      rw [map_pow]
      exact ((GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by
        rw [(GlobalTheory.MemLoc.thetaD_props l).2.2.2.1]; exact hθν)).pow η
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdRp l →ₐ[ℤ_[l]] OD l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  have hED : IsUnit (dRO l O (toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)))) := by
    have hxi : GlobalTheory.MemLoc.xi ε ∈ Ideal.span {ϖ.ev a (eis l a e)} := by
      rw [ϖ.span_ev_eis a, GlobalTheory.MemLoc.ker_theta_eq_span_xi hE]
      exact Ideal.subset_span rfl
    obtain ⟨w, hw⟩ := Ideal.mem_span_singleton'.1 hxi
    have hu := GlobalTheory.MemLoc.TiedUnif.isUnit_xi hE
    rw [← hw, map_mul, map_mul] at hu
    have h1 := isUnit_of_mul_isUnit_right hu
    have := h1.map (Algebra.TensorProduct.includeRight : Per.BdR l →ₐ[ℤ_[l]] OdR l O)
    rw [Algebra.TensorProduct.includeRight_apply] at this
    exact this

  choose c hc z hz using GlobalTheory.T.coord_E_pow_basis_alt l a e O K t ϖ ι η H D T R ε δ hEps hδl

  obtain ⟨s, hs, hσv⟩ := GlobalTheory.T.eisensteinPow_smul_value_eq_sum_basis l a e O K t ϖ ι η H D T R σ c hc

  have hYA : ∀ j τ, E K l e ^ η * y τ j ∈ A O K := by
    intro j τ
    have h1 : y τ j ∈ invE l e (A O K) := mem_tot.1 hy τ j
    obtain ⟨n, hn⟩ := h1
    have h2 : (σ.1 - y) τ j ∈ Rpi O K l e := mem_tot.1 hσy τ j
    have h3 : E K l e ^ η * y τ j ∈ Rpi O K l e := by
      have : E K l e ^ η * y τ j = (s j τ : K⟦X⟧) - E K l e ^ η * (σ.1 - y) τ j := by
        rw [hs, Pi.sub_apply, Pi.sub_apply]; ring
      rw [this]
      exact sub_mem (invL_S_le_Rpi l e (s j τ).2) (mul_mem (pow_mem (E_mem l e _) η) h2)
    refine mem_A_of_E_pow_mul_mem l e n h3 ?_
    have hn' : E K l e ^ n * y τ j ∈ A O K := by rwa [coe_EIn] at hn
    rw [mul_left_comm]
    exact mul_mem (pow_mem (E_mem l e _) η) hn'
  set Y : ι → ZMod a → A O K := fun j τ => ⟨_, hYA j τ⟩ with hYdef

  have hbv := GlobalTheory.T.breuilKisin_value_mul_eisensteinPow_eq_sum l a e O K t ϖ ι η H D T R y hy b₂ hb₂ c hc Y (fun _ _ => rfl)
  have hAS : A O K ≤ invL l (S O K e) := le_trans (A_le_S l e) (le_away _ _)
  set ρ : ι → ZMod a → invL l (S O K e) := fun j τ => s j τ - ⟨_, hAS (hYA j τ)⟩ with hρdef
  have hρ : ∀ j τ, ∃ r ∈ Rpi O K l e, (ρ j τ : K⟦X⟧) = E K l e ^ η * r := fun j τ =>
    ⟨(σ.1 - y) τ j, mem_tot.1 hσy τ j, by
      rw [hρdef]
      simp only [Subalgebra.coe_sub, hs, Pi.sub_apply]
      ring⟩
  have hiBY : ∀ j, ϖ.iB t K (fun τ => ⟨_, hAS (hYA j τ)⟩) = toB l O (ϖ.iTot t K (Y j)) := fun j =>
    (PiSys.iB_of_mem t K ϖ (fun τ => ⟨_, A_le_S l e (hYA j τ)⟩)).trans
      (congrArg (toOB l O) (PiSys.iC_of_mem t K ϖ (Y j)))
  have key : toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) ^ (H + η) •
      (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) = ∑ j, ϖ.iB t K (ρ j) • R.jB (fun i => toB l O (c j i)) := by
    rw [smul_sub, hσv, hbv, ← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [← sub_smul, ← hiBY j, ← map_sub]
    rfl

  apply GlobalTheory.T.mem_span_filtrationZero_of_integral_tensorLattice l O K T C
  set EAD := toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e)) with hEAD
  obtain ⟨v, hv⟩ := hνD.exists_left_inv
  have hcomp : (iotaO O C).comp (toB l O) = (dRO l O).comp (toOD l O) := AlgHom.ext (iotaO_toB C)
  have hPsiL : ∀ j, TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) =
      TWincl (dRO l O) T ((v * EAD ^ H) • TWincl (toOD l O) T (z j)) := by
    intro j
    have h1 := congrArg (TWincl (iotaO O C) T) (hz j)
    rw [TWincl_smul', iotaO_toB, TWincl_TWincl, hcomp, ← TWincl_TWincl, TWincl_smul', map_pow] at h1
    calc TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i))
        = dRO l O (v * toOD l O ((1 : O) ⊗ₜ[ℤ_[l]] (muOf δ ^ η))) •
            TWincl (iotaO O C) T (R.jB fun i => toB l O (c j i)) := by rw [hv, map_one, one_smul]
      _ = dRO l O v • TWincl (dRO l O) T (EAD ^ H • TWincl (toOD l O) T (z j)) := by
          rw [map_mul, mul_smul, h1]
      _ = _ := by rw [TWincl_smul', TWincl_smul', map_mul, mul_smul]
  choose z' hz' using fun j => GlobalTheory.T.image_deRham_eq_eisenstein_pow_mul_of_components l a e O K t ϖ C η (ρ j) (hρ j)
  have hE' : dRO l O EAD ^ (H + η) =
      iotaO O C ((toB l O ((1 : O) ⊗ₜ[ℤ_[l]] ϖ.ev a (eis l a e))) ^ (H + η)) := by
    rw [map_pow, iotaO_toB]
  have hmain : dRO l O EAD ^ (H + η) • TWincl (iotaO O C) T (R.jB (toBcris t ϖ D.toPhiMod σ) - b₂) =
      dRO l O EAD ^ (H + η) • TWincl (dRO l O) T (∑ j, (z' j * v) • TWincl (toOD l O) T (z j)) := by
    conv_lhs => rw [hE', ← TWincl_smul', key, map_sum]
    conv_rhs => rw [← map_pow, ← TWincl_smul', Finset.smul_sum, map_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [TWincl_smul', hz' j, hPsiL j, ← TWincl_smul', smul_smul, smul_smul]
    congr 2
    ring
  exact ⟨_, ((hED.pow (H + η)).smul_left_cancel.1 hmain).symm⟩
