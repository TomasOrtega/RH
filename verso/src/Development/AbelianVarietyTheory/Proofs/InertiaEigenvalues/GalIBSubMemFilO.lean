import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.SmulMemFilTOfZero
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.JMemFilPOfApprox
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.AcrisToBcrisMemFiltrationOfLadicApproxStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.ExistsPowMulDescPochhammerEulerEqEisensteinPowStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix GlobalTheory.BKGal.XiFil GlobalTheory.BKGal.TaylorFil
open scoped Formalism.Per

namespace GlobalTheory.BKGal.TaylorFil

/- English proof (translation)
Introduce `l _ C x hx n`. Establish `hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x` using `(congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))`. Establish `h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1`. Rewrite using `[← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]`. Simplify using the standard rewrite rules.

Establish `h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k`. Introduce `k`. Proceed by induction on `k with`. Consider the case `zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1`. Consider the case `succ k ih`.

Rewrite using `[pow_succ]`. Use `(GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)` as an intermediate fact. Simplify using `using this`. Establish `h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n`. Establish `h4` using `congrArg C.j (factorial_mul_dpow x hx n)`.

Rewrite `h4` using `[map_mul, map_natCast, map_pow, hj]`. Rewrite using `[mul_comm, h4, ← alg_mem_FilD_iff, map_pow]`. Conclude with `h2 n`. Establish `hu : IsUnit (n.factorial : Per.BdRp l)` using `(GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)`. Take `⟨v, hv⟩` from `hu.exists_right_inv`.

Establish `h5` using `Ideal.mul_mem_right v _ h3`. Rewrite `h5` using `[mul_assoc, hv, mul_one]`. Then use the resulting hypothesis.
-/
theorem dpowFil : ∀ (l : ℕ) [Fact l.Prime] (C : GlobalTheory.MemLoc.Core l) (x : Per.Ainf l) (hx : Per.θ l x = 0) (n : ℕ), C.j (dpow x hx n) ∈ Per.FilP l n := by
  intro l _ C x hx n
  have hj : C.j (ainfToAcris l x) = GlobalTheory.MemLoc.aDp l x :=
    (congrArg C.j (GlobalTheory.MemLoc.algebraMap_ainf_acris_eq x)).trans
      ((C.j_cris.on0 (algebraMap (Per.Ainf l) (Per.Acris0 l) x)).trans
        (congrArg (algebraMap (Per.AinfP l) (Per.BdRp l)) (Subalgebra.coe_algebraMap _ x)))
  have h1 : GlobalTheory.MemLoc.aDp l x ∈ Per.FilP l 1 := by
    rw [← (GlobalTheory.MemLoc.thetaD_props l).2.1, (GlobalTheory.MemLoc.thetaD_props l).2.2.2.1, hx]
    simp
  have h2 : ∀ k : ℕ, algebraMap (Per.BdRp l) (Per.BdR l) (GlobalTheory.MemLoc.aDp l x) ^ k ∈ Per.FilD l k := by
    intro k
    induction k with
    | zero => simpa using (GlobalTheory.MemLoc.filD_laws l).2.1
    | succ k ih =>
      rw [pow_succ]
      have := (GlobalTheory.MemLoc.filD_laws l).2.2.1 k 1 _ _ ih (by simpa using (alg_mem_FilD_iff 1 _).2 h1)
      simpa using this
  have h3 : C.j (dpow x hx n) * (n.factorial : Per.BdRp l) ∈ Per.FilP l n := by
    have h4 := congrArg C.j (factorial_mul_dpow x hx n)
    rw [map_mul, map_natCast, map_pow, hj] at h4
    rw [mul_comm, h4, ← alg_mem_FilD_iff, map_pow]
    exact h2 n
  have hu : IsUnit (n.factorial : Per.BdRp l) :=
    (GlobalTheory.MemLoc.thetaD_props l).2.2.1 _ (by rw [map_natCast]; exact_mod_cast n.factorial_ne_zero)
  obtain ⟨v, hv⟩ := hu.exists_right_inv
  have h5 := Ideal.mul_mem_right v _ h3
  rwa [mul_assoc, hv, mul_one] at h5

end GlobalTheory.BKGal.TaylorFil

noncomputable section

namespace GlobalTheory.BKGal.TaylorFil

section Main

variable {l : ℕ} [hl : Fact l.Prime] {a e : ℕ} [NeZero a] [NeZero e] {O K : Type} [CommRing O] [Algebra ℤ_[l] O]
  [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K]
  [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]

/- English proof (translation)
Proceed by induction on `j with`. Consider the case `zero => simpa using toOB_mem_filO_zero (O := O) C 1`. Consider the case `succ j ih => rw [pow_succ]`. Simplify using `using mul_mem_filO ih hx`.
-/
theorem pow_mem_filO {C : GlobalTheory.MemLoc.Core l} {x : OB l O} (hx : x ∈ filO O C 1) (j : ℕ) :
    x ^ j ∈ filO O C j := by
  induction j with
  | zero => simpa using toOB_mem_filO_zero (O := O) C 1
  | succ j ih => rw [pow_succ]; simpa using mul_mem_filO ih hx

variable (O K) in

/- English proof (translation)
Establish `hE : Per.θ l (ϖ.teich ^ e + l) = 0`. Rewrite using `[map_add, map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]`. Establish `h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l)`. Establish `: EIn l e (S O K e) = uIn _ ^ e + (l : S O K e)` using `Subtype.ext (by simp [E])`. Rewrite using `[this, map_add, map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add, map_pow, map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]`.

Use `congr 1`. Conclude with `(map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm`. Establish `h2` using `dpowFil l C _ hE 1`. Rewrite `h2` using `[dpow_one]`. Rewrite using `[h1]`.

Simplify using `using toOB_tmul_mem_filO (O := O) h2`.
-/
theorem iS_E_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) :
    toOB l O (ϖ.iS O K (EIn l e _)) ∈ filO O C 1 := by
  have hE : Per.θ l (ϖ.teich ^ e + l) = 0 := by
    rw [map_add, map_pow, ϖ.theta_teich, ϖ.seqO_zero, map_natCast, neg_add_cancel]
  have h1 : ϖ.iS O K (EIn l e _) = (1 : O) ⊗ₜ[ℤ_[l]] ainfToAcris l (ϖ.teich ^ e + l) := by
    have : EIn l e (S O K e) = uIn _ ^ e + (l : S O K e) := Subtype.ext (by simp [E])
    rw [this, map_add, map_pow, ϖ.iS_u O K, map_natCast, PiSys.teichR, toOCr_tmul, map_add, map_pow,
      map_natCast, tmul_add, Algebra.TensorProduct.tmul_pow, one_pow]
    congr 1
    exact (map_natCast (Algebra.TensorProduct.includeRight : Per.Acris l →ₐ[ℤ_[l]] OCr l O) l).symm
  have h2 := dpowFil l C _ hE 1
  rw [dpow_one] at h2
  rw [h1]
  simpa using toOB_tmul_mem_filO (O := O) h2

variable (O) in

/- English proof (translation)
The claim follows from `toOB_tmul_mem_filO (dpowFil l C _ _ i)`.
-/
theorem muDiv_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (g : ↥(GK (ϖ.field a))) (i : ℕ) :
    toOB l O (ϖ.muDiv a O g i) ∈ filO O C i :=
  toOB_tmul_mem_filO (dpowFil l C _ _ i)

/- English proof (translation)
Take `⟨h, hh, k, hk⟩` from `hN`. Take `⟨s, hs⟩` from `hp`. Use `set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def`. Establish `hp₀A : p₀ ∈ A O K` using `by simpa [p₀] using hs`. Set `q : S O K e` to `⟨p₀, A_le_S l e hp₀A⟩`.

Establish `hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩` using `Subtype.ext (by simp [p₀])`. Establish `hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q)`. Rewrite using `[← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]`. Use `set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef`. Establish `hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D`.

Establish `h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p)`. Rewrite using `[map_mul, map_pow, map_natCast]`. Rewrite using `[mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]`. Use `mem_filO_of_pow_mul (s := s) ?_` and prove the remaining obligations. Rewrite using `[hD]`.

Use `mem_filO_of_pow_mul (s := k) ?_` and prove the remaining obligations. Establish `hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D)`. Rewrite using `[map_mul, map_pow, map_natCast]`. Rewrite using `[hk']`. Establish `hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h'`.

Introduce `i hi`. Take `⟨h', hh', he⟩` from `GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow l e O K (p : K⟦X⟧) h k m hh hk i hi`. Use `⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩` and prove the remaining obligations. Establish `h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p`. Establish `h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s)` using `by simp`.

Rewrite using `[hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]`. Rewrite using `[h4, mul_left_comm, he]`. Expand and normalize the polynomial expressions, which then agree. Use `GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_` and prove the remaining obligations. Take `⟨M₀, hM⟩` from `ϖ.taylor_S a O K g q r`.

Take `⟨w, hw⟩` from `hM (max M₀ 1) (le_max_left _ _)`. Establish `hM1 : 0 < max M₀ 1` using `lt_of_lt_of_le one_pos (le_max_right _ _)`. Establish `h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ = ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0, ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩`. Rewrite using `[← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]`. Use `congr 1`.

Rewrite using `[PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]`. Use `congr 1`. Conclude with `Subtype.ext (by simp [descN])`. Use `⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0, ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩` and prove the remaining obligations. Rewrite `hw` using `[h0]`.

Rewrite using `[hDdef]`. Take the linear combination `(l : OCr l O) ^ k * hw`. Rewrite using `[Finset.mul_sum, map_sum]`. Use `Submodule.sum_mem _ fun i hi => ?_` and prove the remaining obligations. Establish `hi1 : 1 ≤ i` using `Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)`.

Take `⟨h', hh', he⟩` from `hdesc i hi1`. Establish `h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ = ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩`. Rewrite using `[← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]`. Use `congr 1`. Conclude with `Subtype.ext (by simpa using he)`.

Rewrite using `[mul_left_comm, h2, map_mul, map_mul, map_pow]`. Establish `h5` using `mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i))) (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))`. Rewrite using `[← mul_assoc]`. Conclude with `filO_anti (by omega) h5`.
-/
theorem gal_iSl_sub_mem (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (g : ↥(GK (ϖ.field a)))
    (p : invL l (S O K e)) (hp : (p : K⟦X⟧) ∈ invL l (A O K))
    (hN : ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (p : K⟦X⟧) = E K l e ^ m * h) :
    galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p ∈ filO O C m := by
  obtain ⟨h, hh, k, hk⟩ := hN
  obtain ⟨s, hs⟩ := hp
  set p₀ : K⟦X⟧ := (l : K⟦X⟧) ^ s * p with hp₀def
  have hp₀A : p₀ ∈ A O K := by simpa [p₀] using hs
  let q : S O K e := ⟨p₀, A_le_S l e hp₀A⟩
  have hq : (l : invL l (S O K e)) ^ s * p = ⟨p₀, le_away _ _ q.2⟩ := Subtype.ext (by simp [p₀])
  have hiq : (l : OB l O) ^ s * ϖ.iSl O K p = toOB l O (ϖ.iS O K q) := by
    rw [← ϖ.iSl_of_mem O K q.2 (le_away _ _ q.2), ← hq, map_mul, map_pow, map_natCast]
  set D := galOCr O g (ϖ.iS O K q) - ϖ.iS O K q with hDdef
  have hD : (l : OB l O) ^ s * (galOB O g (ϖ.iSl O K p) - ϖ.iSl O K p) = toOB l O D := by
    have h3 : (l : OB l O) ^ s * galOB O g (ϖ.iSl O K p) = galOB O g ((l : OB l O) ^ s * ϖ.iSl O K p) := by
      rw [map_mul, map_pow, map_natCast]
    rw [mul_sub, h3, hiq, galOB_toOB, hDdef, map_sub]
  refine mem_filO_of_pow_mul (s := s) ?_
  rw [hD]
  refine mem_filO_of_pow_mul (s := k) ?_
  have hk' : (l : OB l O) ^ k * toOB l O D = toOB l O ((l : OCr l O) ^ k * D) := by
    rw [map_mul, map_pow, map_natCast]
  rw [hk']
  have hdesc : ∀ i, 1 ≤ i → ∃ h' ∈ A O K, (l : K⟦X⟧) ^ k * descN K i p₀ = E K l e ^ (m + 1 - i) * h' := by
    intro i hi
    obtain ⟨h', hh', he⟩ := GlobalTheory.T.exists_pow_mul_descPochhammerEuler_eq_eisenstein_pow l e O K (p : K⟦X⟧) h k m hh hk i hi
    refine ⟨(l : K⟦X⟧) ^ s * h', mul_mem (pow_mem (natCast_mem _ l) s) hh', ?_⟩
    have h4 : descN K i p₀ = (l : K⟦X⟧) ^ s * descN K i p := by
      have h3 : (l : K⟦X⟧) ^ s = PowerSeries.C ((l : K) ^ s) := by simp
      rw [hp₀def, h3, ← smul_eq_C_mul, map_smul, smul_eq_C_mul]
    rw [h4, mul_left_comm, he]
    ring
  refine GlobalTheory.T.acrisToBcris_mem_filtration_of_ladic_approx l O C m _ fun r => ?_
  obtain ⟨M₀, hM⟩ := ϖ.taylor_S a O K g q r
  obtain ⟨w, hw⟩ := hM (max M₀ 1) (le_max_left _ _)
  have hM1 : 0 < max M₀ 1 := lt_of_lt_of_le one_pos (le_max_right _ _)
  have h0 : ∑ i ∈ Finset.range (max M₀ 1), ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
      ϖ.iS O K q + ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
        ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ := by
    rw [← Finset.add_sum_erase _ _ (Finset.mem_range.2 hM1)]
    congr 1
    rw [PiSys.muDiv, dpow_zero, ← Algebra.TensorProduct.one_def, one_mul]
    congr 1
    exact Subtype.ext (by simp [descN])
  refine ⟨(l : OCr l O) ^ k * ∑ i ∈ (Finset.range (max M₀ 1)).erase 0,
    ϖ.muDiv a O g i * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩, (l : OCr l O) ^ k * w, ?_, ?_⟩
  · rw [h0] at hw
    rw [hDdef]
    linear_combination (l : OCr l O) ^ k * hw
  · rw [Finset.mul_sum, map_sum]
    refine Submodule.sum_mem _ fun i hi => ?_
    have hi1 : 1 ≤ i := Nat.pos_of_ne_zero (Finset.ne_of_mem_erase hi)
    obtain ⟨h', hh', he⟩ := hdesc i hi1
    have h2 : (l : OCr l O) ^ k * ϖ.iS O K ⟨descN K i q, descN_mem_S e i q.2⟩ =
        ϖ.iS O K (EIn l e _) ^ (m + 1 - i) * ϖ.iS O K ⟨h', A_le_S l e hh'⟩ := by
      rw [← map_natCast (ϖ.iS O K), ← map_pow, ← map_mul, ← map_pow, ← map_mul]
      congr 1
      exact Subtype.ext (by simpa using he)
    rw [mul_left_comm, h2, map_mul, map_mul, map_pow]
    have h5 := mul_mem_filO (mul_mem_filO (muDiv_mem O ϖ C g i) (pow_mem_filO (iS_E_mem O K ϖ C) (m + 1 - i)))
      (toOB_mem_filO_zero C (ϖ.iS O K ⟨h', A_le_S l e hh'⟩))
    rw [← mul_assoc]
    exact filO_anti (by omega) h5

end Main

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg`. Establish `key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m` using `fun τ => gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)`. Rewrite using `[PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]`. Use `Submodule.sum_mem _ fun τ _ => ?_` and prove the remaining obligations. Establish `hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ` using `(galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))`.

Rewrite using `[map_mul, hid, ← mul_sub]`. Establish `h6` using `mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)`. Rewrite `h6` using `[zero_add]`. Conclude with `h6`.
-/
theorem gal_iB_sub_mem_filO : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (C : GlobalTheory.MemLoc.Core l) (m : ℕ) (f : ZMod a → invL l (S O K e)), (∀ τ, (f τ : K⟦X⟧) ∈ invL l (A O K)) → (∀ τ, ∃ h ∈ A O K, ∃ k : ℕ, (l : K⟦X⟧) ^ k * N K (f τ : K⟦X⟧) = E K l e ^ m * h) → ∀ g : Gl l, sQ l g ∈ GK (ϖ.field a) → galOB O (sQ l g) (ϖ.iB t K f) - ϖ.iB t K f ∈ filO O C m := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ C m f hfA hN g hg
  have key : ∀ τ, galOB O (sQ l g) (ϖ.iSl O K (f τ)) - ϖ.iSl O K (f τ) ∈ filO O C m := fun τ =>
    gal_iSl_sub_mem ϖ C m ⟨sQ l g, hg⟩ (f τ) (hfA τ) (hN τ)
  rw [PiSys.iB, glue_apply, map_sum, ← Finset.sum_sub_distrib]
  refine Submodule.sum_mem _ fun τ _ => ?_
  have hid : galOB O (sQ l g) (idem (constB t) τ) = idem (constB t) τ :=
    (galOB_toOB _ (idem (constC t) τ)).trans (congrArg _ (galOCr_idem t ϖ ⟨sQ l g, hg⟩ τ))
  rw [map_mul, hid, ← mul_sub]
  have h6 := mul_mem_filO (toOB_mem_filO_zero C (idem (constC t) τ)) (key τ)
  rw [zero_add] at h6
  exact h6

end GlobalTheory.BKGal.TaylorFil
