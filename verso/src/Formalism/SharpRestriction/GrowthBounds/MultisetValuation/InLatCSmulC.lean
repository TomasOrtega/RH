import Formalism.SharpRestriction.GrowthBounds.MultisetValuation.ValuationBoundAdd

noncomputable section

namespace Formalism.MainNotions.FormalGroupSystem.Pf

open Formalism.MainNotions.G Formalism.BasicNotions Finset

attribute [local instance] Formalism.MainNotions.G.GAtP.ringO Formalism.MainNotions.G.GAtP.domO Formalism.MainNotions.G.GAtP.dvrO Formalism.MainNotions.G.GAtP.fieldK
  Formalism.MainNotions.G.GAtP.algOK

variable {p : ℕ} [Fact p.Prime] {X : Sys p} (Y : Pend X)

/- English proof (translation)
Unfold `Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢`. Conclude with `AddSubgroup.sum_mem _ h`.
-/
theorem inLatC_sum {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {κ : Type*} (s : Finset κ) (f : κ → XspC (X.Pj j) Y.Kc)
    (h : ∀ k ∈ s, Y.inLatC j g L (f k)) : Y.inLatC j g L (∑ k ∈ s, f k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  exact AddSubgroup.sum_mem _ h

/- English proof (translation)
Unfold `Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢`. Establish `hm` using `AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (XspC (X.Pj j) Y.Kc) b) h`. Rewrite `hm` using `[AddMonoidHom.map_closure]`. Use `AddSubgroup.closure_mono ?_ hm` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩`.

Conclude with `⟨b * a, geC_mul_shift (Y := Y) k ha hb, z, hz, by simp [smul_smul]⟩`.
-/
theorem inLatC_smulC {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (b : Y.Kc) (k : ℤ)
    (hb : b * (p : Y.Kc) ^ k ∈ Y.Oc) {y : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y) :
    Y.inLatC j (g - k) L (b • y) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h ⊢
  have hm := AddSubgroup.mem_map_of_mem (DistribMulAction.toAddMonoidHom (XspC (X.Pj j) Y.Kc) b) h
  rw [AddMonoidHom.map_closure] at hm
  refine AddSubgroup.closure_mono ?_ hm
  rintro _ ⟨_, ⟨a, ha, z, hz, rfl⟩, rfl⟩
  exact ⟨b * a, geC_mul_shift (Y := Y) k ha hb, z, hz, by simp [smul_smul]⟩

/- English proof (translation)
Unfold `Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h`. Proceed by induction on `h using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, z, hz, rfl⟩` from `hx`. Conclude with `⟨Unit, inferInstance, fun _ => a, fun _ => z, fun _ => ha, fun _ => hz, by simp⟩`.

Consider the case `zero`. Conclude with `⟨Empty, inferInstance, Empty.elim, Empty.elim, fun k => k.elim, fun k => k.elim, by simp⟩`. Consider the case `add x y _ _ hx hy`. Take `⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩` from `hx`. Take `⟨κ2, i2, a2, z2, ha2, hz2, rfl⟩` from `hy`.

Use `⟨κ1 ⊕ κ2, inferInstance, Sum.elim a1 a2, Sum.elim z1 z2, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce and unpack `(k | k) exacts [ha1 k, ha2 k]`. Introduce and unpack `(k | k) exacts [hz1 k, hz2 k]`. Rewrite using `[Fintype.sum_sum_type]`. Both sides reduce to the same expression.

Consider the case `neg x _ hx`. Take `⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩` from `hx`. Use `⟨κ1, i1, fun k => -a1 k, z1, fun k => geC_neg (Y := Y) (ha1 k), hz1, ?_⟩` and prove the remaining obligations. Simplify using `[neg_smul]`.
-/
theorem inLatC_rep {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} {y' : XspC (X.Pj j) Y.Kc} (h : Y.inLatC j g L y') :
    ∃ (κ : Type) (_ : Fintype κ) (a : κ → Y.Kc) (z : κ → (X.Pj j).Xsp), (∀ k, Y.geC (a k) g) ∧
      (∀ k, z k ∈ (X.Pj j).HtupW L) ∧ y' = ∑ k, a k • MvPolynomial.map (algebraMap X.G.Kf Y.Kc) (z k) := by
  unfold Formalism.MainNotions.FormalGroupSystem.Pend.inLatC at h
  induction h using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, z, hz, rfl⟩ := hx
    exact ⟨Unit, inferInstance, fun _ => a, fun _ => z, fun _ => ha, fun _ => hz, by simp⟩
  | zero =>
    exact ⟨Empty, inferInstance, Empty.elim, Empty.elim, fun k => k.elim, fun k => k.elim, by simp⟩
  | add x y _ _ hx hy =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    obtain ⟨κ2, i2, a2, z2, ha2, hz2, rfl⟩ := hy
    refine ⟨κ1 ⊕ κ2, inferInstance, Sum.elim a1 a2, Sum.elim z1 z2, ?_, ?_, ?_⟩
    · rintro (k | k)
      exacts [ha1 k, ha2 k]
    · rintro (k | k)
      exacts [hz1 k, hz2 k]
    · rw [Fintype.sum_sum_type]
      rfl
  | neg x _ hx =>
    obtain ⟨κ1, i1, a1, z1, ha1, hz1, rfl⟩ := hx
    refine ⟨κ1, i1, fun k => -a1 k, z1, fun k => geC_neg (Y := Y) (ha1 k), hz1, ?_⟩
    simp [neg_smul]

/- English proof (translation)
Take `⟨κ, _, a, z, ha, hz, hy⟩` from `inLatC_rep Y h`. Take `⟨c, hc, hyc⟩` from `descent_core (K := X.G.Kf) (Kc := Y.Kc) (V := (X.Pj j).Xsp) (Vc := XspC (X.Pj j) Y.Kc) (MvPolynomial.map (algebraMap X.G.Kf Y.Kc)).toAddMonoidHom (by`. Introduce `c v`. Simplify using `only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul, MvPolynomial.map_C])`. Use the proof step `(fun m => MvPolynomial.lcoeff X.G.Kf m) (fun m => MvPolynomial.lcoeff Y.Kc m)`.

Use the proof step `(by intro m v; simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map])`. Use the proof step `(by`. Introduce `v hv`. Use extensionality with `m`. Simplify `hv m)` using `[MvPolynomial.lcoeff_apply]`.

Use the proof step `(RK X) (RK_val Y) (geCgrp Y g)`. Use the proof step `(by`. Introduce `r hr a ha`. Conclude with `geC_mul_Oc Y ha ((mem_RK_iff Y).mp hr))`. Use the proof step `(Finset.univ : Finset κ).card Finset.univ rfl z a (fun k _ => ha k) y hy`.

Rewrite using `[hyc]`. Use `Submodule.sum_mem _ fun k _ => ?_` and prove the remaining obligations. Establish `h1` using `vGeK_of_geC Y (c k) g (hc k (Finset.mem_univ k))`. Unfold `Sys.vGeK at h1`. Rewrite `h1` using `[mem_scale_iff]`.

Take `⟨o, ho, hok⟩` from `h1`. Take `⟨t, rfl⟩` from `mem_intKF.mp ho`. Rewrite using `[mem_scale_iff]`. Use `⟨t • z k, Submodule.smul_mem _ _ (hz k), ?_⟩` and prove the remaining obligations. Rewrite using `[← hok, smul_eq_mul, mul_smul, algebraMap_smul]`.
-/
theorem descent {j : ℕ} {g : ℝ} {L : (X.Pj j).Tup} (y : (X.Pj j).Xsp)
    (h : Y.inLatC j g L (MvPolynomial.map (algebraMap X.G.Kf Y.Kc) y)) :
    y ∈ scale (X.vsc g) ((X.Pj j).HtupW L) := by
  classical
  obtain ⟨κ, _, a, z, ha, hz, hy⟩ := inLatC_rep Y h
  obtain ⟨c, hc, hyc⟩ := descent_core (K := X.G.Kf) (Kc := Y.Kc) (V := (X.Pj j).Xsp) (Vc := XspC (X.Pj j) Y.Kc)
    (MvPolynomial.map (algebraMap X.G.Kf Y.Kc)).toAddMonoidHom
    (by
      intro c v
      simp only [RingHom.toAddMonoidHom_eq_coe, AddMonoidHom.coe_coe, MvPolynomial.smul_eq_C_mul, map_mul,
        MvPolynomial.map_C])
    (fun m => MvPolynomial.lcoeff X.G.Kf m) (fun m => MvPolynomial.lcoeff Y.Kc m)
    (by intro m v; simp [MvPolynomial.lcoeff_apply, MvPolynomial.coeff_map])
    (by
      intro v hv
      ext m
      simpa [MvPolynomial.lcoeff_apply] using hv m)
    (RK X) (RK_val Y) (geCgrp Y g)
    (by
      intro r hr a ha
      exact geC_mul_Oc Y ha ((mem_RK_iff Y).mp hr))
    (Finset.univ : Finset κ).card Finset.univ rfl z a (fun k _ => ha k) y hy
  rw [hyc]
  refine Submodule.sum_mem _ fun k _ => ?_
  have h1 := vGeK_of_geC Y (c k) g (hc k (Finset.mem_univ k))
  unfold Sys.vGeK at h1
  rw [mem_scale_iff] at h1
  obtain ⟨o, ho, hok⟩ := h1
  obtain ⟨t, rfl⟩ := mem_intKF.mp ho
  rw [mem_scale_iff]
  refine ⟨t • z k, Submodule.smul_mem _ _ (hz k), ?_⟩
  rw [← hok, smul_eq_mul, mul_smul, algebraMap_smul]

/- English proof (translation)
Establish `hk : ((m : kb p)) ≠ 0`. Rewrite using `[Ne, CharP.cast_eq_zero_iff (kb p) p]`. Conclude with `hm`. Establish `hu : IsUnit ((m : WW p))`. Apply `WittVector.isUnit_of_coeff_zero_ne_zero` to reduce the goal to its premises.

Establish `hc : WittVector.constantCoeff ((m : WW p)) = (m : kb p)` using `map_natCast _ m`. Express the relevant statement in the definitionally equal form `WittVector.constantCoeff ((m : WW p)) ≠ 0`. Rewrite using `[hc]`. Conclude with `hk`. Take `⟨u, hu⟩` from `hu`.

Establish `h1 : algebraMap (K0 p) Y.Kc (algebraMap (WW p) (K0 p) (↑u⁻¹ : WW p)) * (m : Y.Kc) = 1`. Rewrite using `[← map_natCast (algebraMap (K0 p) Y.Kc), ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul, ← map_mul, ← hu, Units.inv_mul, map_one, map_one]`. Rewrite using `[← eq_inv_of_mul_eq_one_left h1]`. Conclude with `Y.witt_mem_integers_Cp _`.
-/
theorem natInv_mem (m : ℕ) (hm : ¬ p ∣ m) : ((m : Y.Kc))⁻¹ ∈ Y.Oc := by
  have hk : ((m : kb p)) ≠ 0 := by
    rw [Ne, CharP.cast_eq_zero_iff (kb p) p]
    exact hm

  have hu : IsUnit ((m : WW p)) := by
    apply WittVector.isUnit_of_coeff_zero_ne_zero
    have hc : WittVector.constantCoeff ((m : WW p)) = (m : kb p) := map_natCast _ m
    change WittVector.constantCoeff ((m : WW p)) ≠ 0
    rw [hc]
    exact hk
  obtain ⟨u, hu⟩ := hu
  have h1 : algebraMap (K0 p) Y.Kc (algebraMap (WW p) (K0 p) (↑u⁻¹ : WW p)) * (m : Y.Kc) = 1 := by
    rw [← map_natCast (algebraMap (K0 p) Y.Kc), ← map_natCast (algebraMap (WW p) (K0 p)), ← map_mul,
      ← map_mul, ← hu, Units.inv_mul, map_one, map_one]
  rw [← eq_inv_of_mul_eq_one_left h1]
  exact Y.witt_mem_integers_Cp _

/- English proof (translation)
Establish `hpp : p.Prime` using `Fact.out`. Take `⟨e, m, hm, rfl⟩` from `Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hpp.ne_one`. Establish `hm0 : m ≠ 0`. Introduce and unpack `rfl`. Conclude with `hm (dvd_zero p)`.

Establish `he : e ≤ d`. Establish `hv : padicValNat p (p ^ e * m) = e`. Rewrite using `[padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hm0, padicValNat.prime_pow, padicValNat.eq_zero_of_not_dvd hm, add_zero]`. Use linear arithmetic over natural numbers and integers. Establish `hp` using `pKc_ne (Y := Y)`.

Take `⟨k, rfl⟩` from `Nat.exists_eq_add_of_le he`. Establish `key : ((p ^ e * m : ℕ) : Y.Kc)⁻¹ * (p : Y.Kc) ^ (((e + k : ℕ)) : ℤ) = ((m : Y.Kc))⁻¹ * (p : Y.Kc) ^ k`. Rewrite using `[zpow_natCast, pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((p : Y.Kc) ^ e)⁻¹), mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hp)]`. Rewrite using `[key]`. Conclude with `Y.Oc.mul_mem (natInv_mem Y m hm) (Y.Oc.pow_mem (natCast_mem Y.Oc p) _)`.
-/
theorem wt_inv (N d : ℕ) (hpos : 0 < N) (hle : padicValNat p N ≤ d) :
    ((N : Y.Kc))⁻¹ * (p : Y.Kc) ^ ((d : ℕ) : ℤ) ∈ Y.Oc := by
  have hpp : p.Prime := Fact.out
  obtain ⟨e, m, hm, rfl⟩ := Nat.exists_eq_pow_mul_and_not_dvd hpos.ne' p hpp.ne_one
  have hm0 : m ≠ 0 := by
    rintro rfl
    exact hm (dvd_zero p)
  have he : e ≤ d := by
    have hv : padicValNat p (p ^ e * m) = e := by
      rw [padicValNat.mul (pow_ne_zero _ hpp.ne_zero) hm0, padicValNat.prime_pow,
        padicValNat.eq_zero_of_not_dvd hm, add_zero]
    omega
  have hp := pKc_ne (Y := Y)
  obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le he
  have key : ((p ^ e * m : ℕ) : Y.Kc)⁻¹ * (p : Y.Kc) ^ (((e + k : ℕ)) : ℤ) = ((m : Y.Kc))⁻¹ * (p : Y.Kc) ^ k := by
    rw [zpow_natCast, pow_add, Nat.cast_mul, Nat.cast_pow, mul_inv, mul_comm (((p : Y.Kc) ^ e)⁻¹),
      mul_assoc, inv_mul_cancel_left₀ (pow_ne_zero _ hp)]
  rw [key]
  exact Y.Oc.mul_mem (natInv_mem Y m hm) (Y.Oc.pow_mem (natCast_mem Y.Oc p) _)

/- English proof (translation)
Rewrite using `[map_inv₀, map_natCast]`. Conclude with `wt_inv Y _ _ (Y.stab_fin j hj La hLa) (X.dG_spec j hj La.1 La.2 hLa)`.
-/
theorem stab_inv (j : ℕ) (hj : j ≤ X.mm) (La : X.Lt j) (hLa : (X.Pj j).IsLatTup La.2) :
    algebraMap X.G.Kf Y.Kc (((X.stab j La : X.G.Kf))⁻¹) * (p : Y.Kc) ^ ((X.dG j : ℕ) : ℤ) ∈ Y.Oc := by
  rw [map_inv₀, map_natCast]
  exact wt_inv Y _ _ (Y.stab_fin j hj La hLa) (X.dG_spec j hj La.1 La.2 hLa)

end Formalism.MainNotions.FormalGroupSystem.Pf
