import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RamDef
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.ExistsIsometryMemLocalizedAtSingle
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.UnimodularLocalStandard.RepHSmulRight

noncomputable section
open scoped ComplexConjugate

namespace PI.UnitaryGroupMassFormula.UnimodLocStd
open PI.ULS

/- English proof (translation)
Introduce `a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK hld`. Substitute `l` using the available equality. Establish `hK0` using `hK`. Take `⟨hOK, hsd, hθ, -, h2, hdp, hQ, hi₀, -⟩` from `hK0`. Use `set L := cmL a b d ha hd lam hlam with hL`.

Use `set κ := repKappa a b d ha hd lam hlam with hκdef`. Use `set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef`. Use `set f := fvec a b d lam x y i₀ with hf`. Establish `hκ : κ ≠ 0` using `rep_kappa_ne a b d ha hd lam hlam`. Establish `hκc : conj κ = κ` using `kappa_real a b d ha hd lam hlam`.

Establish `hHf : stdH L m f f = κ * (Q : ℂ)` using `rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀`. Establish `hQ0 : (Q : ℂ) ≠ 0`. Establish `: Q ≠ 0` using `fun h => hQ (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hfT : ∀ j ∈ T, f j = 0`.

Introduce `j hj`. Establish `hne : j ≠ i₀` using `fun h => hi₀ (h ▸ hj)`. Simplify using `[hf, fvec, hne]`. Establish `hfmem : f ∈ stdLat L m` using `rep_fvec_mem a b d ha hd lam hlam m x y i₀`. Use `set M := relIdx Λ (stdLat L m) with hMdef`.

Establish `hMf : M • f ∈ Λ`. Establish `h` using `AddSubgroup.nsmul_index_mem (Λ.addSubgroupOf (stdLat L m)) ⟨f, hfmem⟩`. Rewrite `h` using `[AddSubgroup.mem_addSubgroupOf]`. Simplify `h` using `[hMdef, relIdx, AddSubgroup.relIndex]`. Establish `hMc : (M : ℂ) ≠ 0` using `by exact_mod_cast h2`.

Establish `hgf : M • f = (M : ℂ) • f` using `(Nat.cast_smul_eq_nsmul ℂ M f).symm`. Use `set g := M • f with hg`. Establish `hHs : ∀ (α β : ℂ) (u v : m → ℂ), stdH L m (α • u) (β • v) = α * conj β * stdH L m u v`. Introduce `α β u v`. Simplify using `only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]`.

Expand and normalize the polynomial expressions, which then agree. Establish `hgT : ∀ j ∈ T, g j = 0`. Introduce `j hj`. Simplify using `[hgf, hfT j hj]`. Establish `hg0 : g ≠ 0`.

Introduce `h`. Establish `h' : stdH L m g g = 0` using `by rw [h]; simp`. Rewrite `h'` using `[hgf, hHs, hHf]`. Establish `: (M : ℂ) * conj (M : ℂ) * (κ * Q) ≠ 0`. Simplify using `only [map_natCast]`.

Conclude with `mul_ne_zero (mul_ne_zero hMc hMc) (mul_ne_zero hκ hQ0)`. Conclude with `this h'`. Establish `hgS : SatMem d Λ g` using `rep_sat_of_mem d Λ hMf hdp`. Establish `hd1 : ¬ (d : ℤ) ∣ 1`. Introduce `h`.

Use `Int.eq_one_of_dvd_one (by positivity) h` as an intermediate fact. Conclude with `hdp.one_lt.ne' (by exact_mod_cast this)`. Take `⟨y1, hy1S, hy1T, -, p1, q1, hp1, hq1, hy1H⟩` from `hU a b c d ha hd lam hlam m Λ x y T i₀ hK 0 (rep_sat_zero d Λ hdp) (by simp) (Or.inl rfl) g hgS hgT (by simp) hg0`. Establish `hp1c : (p1 : ℂ) ≠ 0`. Establish `: p1 ≠ 0` using `fun h => hp1 (h ▸ dvd_zero _)`.

Conclude with `this` after adjusting the coercions. Establish `hq1c : (q1 : ℂ) ≠ 0`. Establish `: q1 ≠ 0` using `fun h => hq1 (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Take `⟨n', c₂, s', hs', hpair⟩` from `sat_pair hOK hsd hθ hdp hgS hy1S`.

Rewrite `hy1H`, `hpair` using `[← hL, ← hκdef]`. Establish `hs'c : (s' : ℂ) ≠ 0`. Establish `: s' ≠ 0` using `fun h => hs' (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hθc : conj (cmTheta b d) = (b : ℂ) - cmTheta b d`.

Use `rep_theta_add_conj b d` as an intermediate fact. Take the linear combination `this`. Use `set γ0 : ℂ := (q1 : ℂ) * ((n' : ℂ) - c₂ * conj (cmTheta b d)) with hγ0`. Use `set z : m → ℂ := (((p1 * s' : ℤ) : ℂ)) • g - γ0 • y1 with hz`. Establish `hzS : SatMem d Λ z`.

Establish `h1` using `rep_sat_zsmul d Λ hgS (p1 * s')`. Establish `h2` using `rep_sat_elt d Λ hdp hθ hy1S (q1 * n') (q1 * c₂) 1 hd1`. Establish `h3 : ((((q1 * n' : ℤ) : ℂ) - ((q1 * c₂ : ℤ) : ℂ) * conj (cmTheta b d)) / ((1 : ℤ) : ℂ)) = γ0`. Rewrite using `[hγ0]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite `h2` using `[h3]`. Conclude with `rep_sat_sub d Λ hdp h1 h2`. Establish `hzT : ∀ j ∈ T, z j = 0`. Introduce `j hj`.

Simplify using `[hz, hgT j hj, hy1T j hj]`. Establish `hzy : stdH L m z y1 = 0`. Establish `e1 : stdH L m z y1 = ((p1 * s' : ℤ) : ℂ) * stdH L m g y1 - γ0 * stdH L m y1 y1`. Simplify using `only [hz, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]`. Rewrite using `[e1, hpair, hy1H, hγ0]`.

Use `push_cast`. Clear the denominators using the available nonvanishing facts. Expand and normalize the polynomial expressions, which then agree. Distinguish the cases in `hz0 : z = 0`. Use `set r : ℂ := ((p1 * s' : ℤ) : ℂ) * M with hr`.

Establish `hr0 : r ≠ 0`. Rewrite using `[hr]`. Use `push_cast`. Conclude with `mul_ne_zero (mul_ne_zero hp1c hs'c) hMc`. Establish `hrc : conj r = r` using `by rw [hr]; simp`.

Establish `hrf : r • f = γ0 • y1`. Establish `: ((p1 * s' : ℤ) : ℂ) • g = γ0 • y1` using `sub_eq_zero.mp (by rw [← hz]; exact hz0)`. Rewrite `this` using `[hgf, smul_smul]`. Simplify `this` using `[hr]`. Use `set β : ℂ := γ0 / r with hβ`.

Establish `hβN : β * conj β = ((Q * q1 : ℤ) : ℂ) / ((p1 : ℤ) : ℂ)`. Establish `e` using `congrArg (fun v => stdH L m v v) hrf`. Simplify using `only [hHs, hHf, hy1H, hrc] at e`. Clear denominators, using `at e` for the nonvanishing conditions. Rewrite using `[hβ, map_div₀, hrc, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hr0 hr0) hp1c]`.

Use `push_cast`. Take the linear combination `-e`. Establish `hβK : IsK b d β`. Use `⟨q1 * (n' - c₂ * b), q1 * c₂, p1 * s' * M, ?_, ?_⟩` and prove the remaining obligations. Establish `: ((p1 * s' * M : ℤ) : ℂ) ≠ 0` using `by push_cast; exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc`.

Conclude with `this` after adjusting the coercions. Rewrite using `[hβ, hγ0, hθc]`. Establish `: ((p1 * s' * (M : ℤ) : ℤ) : ℂ) = r` using `by rw [hr]; push_cast; ring`. Rewrite using `[this]`. Clear the denominators using the available nonvanishing facts.

Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Establish `hQq : ¬ (d : ℤ) ∣ Q * q1` using `not_dvd_mul' hdp hQ hq1`. Take `⟨s, hs⟩` from `norm_square hOK hβK hQq hp1 hβN`. Take `⟨k, hk⟩` from `hs`.

Use `⟨(s : ℂ) • y1, ⟨rep_sat_zsmul d Λ hy1S s, ?_, k, Q * q1, hQq, ?_⟩⟩` and prove the remaining obligations. Introduce `j hj`. Simplify using `[hy1T j hj]`. Rewrite using `[hHs, hy1H, hHf]`. Establish `hk' : (s : ℂ) ^ 2 * p1 = Q * q1 + d * k`.

Use `congrArg (fun t : ℤ => (t : ℂ)) hk` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Simplify using `only [map_intCast]`. Use `push_cast`.

Clear the denominators using the available nonvanishing facts. Take the linear combination `hk'`. Take `⟨y2, hy2S, hy2T, hy21, p2, q2, hp2, hq2, hy2H⟩` from `hU a b c d ha hd lam hlam m Λ x y T i₀ hK y1 hy1S hy1T (Or.inr ⟨p1, q1, hp1, hq1, by`. Rewrite using `[hy1H]⟩) z hzS hzT hzy hz0`. Rewrite `hy2H` using `[← hL, ← hκdef]`.

Rewrite `hy21` using `[← hL]`. Establish `hp2c : (p2 : ℂ) ≠ 0`. Establish `: p2 ≠ 0` using `fun h => hp2 (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hq2c : (q2 : ℂ) ≠ 0`.

Establish `: q2 ≠ 0` using `fun h => hq2 (h ▸ dvd_zero _)`. Conclude with `this` after adjusting the coercions. Establish `hy12 : stdH L m y1 y2 = 0`. Use `rep_H_conj (L := L) (m := m) y2 y1` as an intermediate fact. Rewrite `this` using `[hy21, map_zero]`.

Conclude with `this.symm`. Establish `hodd : d % 2 = 1`. Use `hOK.2.2.1` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Take `⟨s, t, hst⟩` from `pigeon hdp hodd (p1 * q2) (p2 * q1) (Q * q1 * q2) (not_dvd_mul' hdp hp1 hq2) (not_dvd_mul' hdp hp2 hq1)`.

Take `⟨k, hk⟩` from `hst`. Establish `hQq : ¬ (d : ℤ) ∣ Q * (q1 * q2)` using `not_dvd_mul' hdp hQ (not_dvd_mul' hdp hq1 hq2)`. Use `⟨(s : ℂ) • y1 + (t : ℂ) • y2, ⟨rep_sat_add d Λ hdp (rep_sat_zsmul d Λ hy1S s) (rep_sat_zsmul d Λ hy2S t), ?_, k, Q * (q1 * q2), hQq, ?_⟩⟩` and prove the remaining obligations. Introduce `j hj`. Simplify using `[hy1T j hj, hy2T j hj]`.

Establish `e : stdH L m ((s : ℂ) • y1 + (t : ℂ) • y2) ((s : ℂ) • y1 + (t : ℂ) • y2) = (s : ℂ) ^ 2 * stdH L m y1 y1 + (t : ℂ) ^ 2 * stdH L m y2 y2`. Simplify using `only [map_add, LinearMap.add_apply, hHs, hy12, hy21, map_intCast]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e, hy1H, hy2H, hHf]`. Establish `hk' : (s : ℂ) ^ 2 * (p1 * q2) + (t : ℂ) ^ 2 * (p2 * q1) = Q * q1 * q2 + d * k`.

Use `congrArg (fun t : ℤ => (t : ℂ)) hk` as an intermediate fact. Move the coercions through the operations in `at this`. Take the linear combination `this`. Use `push_cast`. Clear the denominators using the available nonvanishing facts.

Take the linear combination `hk'`.
-/
theorem keyStartRam_of_unit (hU : UnitVecRam) : KeyStartRam := by
  intro a b c d ha hd lam hlam m _ _ Λ l x y T i₀ hK hld
  subst l
  have hK0 := hK
  obtain ⟨hOK, hsd, hθ, -, h2, hdp, hQ, hi₀, -⟩ := hK0
  set L := cmL a b d ha hd lam hlam with hL
  set κ := repKappa a b d ha hd lam hlam with hκdef
  set Q : ℤ := a * x ^ 2 + b * x * y + c * y ^ 2 with hQdef
  set f := fvec a b d lam x y i₀ with hf
  have hκ : κ ≠ 0 := rep_kappa_ne a b d ha hd lam hlam
  have hκc : conj κ = κ := kappa_real a b d ha hd lam hlam
  have hHf : stdH L m f f = κ * (Q : ℂ) := rep_norm_f a b c d ha hd lam hlam m hOK.1 x y i₀
  have hQ0 : (Q : ℂ) ≠ 0 := by
    have : Q ≠ 0 := fun h => hQ (h ▸ dvd_zero _)
    exact_mod_cast this
  have hfT : ∀ j ∈ T, f j = 0 := by
    intro j hj
    have hne : j ≠ i₀ := fun h => hi₀ (h ▸ hj)
    simp [hf, fvec, hne]
  have hfmem : f ∈ stdLat L m := rep_fvec_mem a b d ha hd lam hlam m x y i₀
  set M := relIdx Λ (stdLat L m) with hMdef
  have hMf : M • f ∈ Λ := by
    have h := AddSubgroup.nsmul_index_mem (Λ.addSubgroupOf (stdLat L m)) ⟨f, hfmem⟩
    rw [AddSubgroup.mem_addSubgroupOf] at h
    simpa [hMdef, relIdx, AddSubgroup.relIndex] using h
  have hMc : (M : ℂ) ≠ 0 := by exact_mod_cast h2
  have hgf : M • f = (M : ℂ) • f := (Nat.cast_smul_eq_nsmul ℂ M f).symm
  set g := M • f with hg
  have hHs : ∀ (α β : ℂ) (u v : m → ℂ), stdH L m (α • u) (β • v) = α * conj β * stdH L m u v := by
    intro α β u v
    simp only [map_smul, LinearMap.smul_apply, LinearMap.map_smulₛₗ, smul_eq_mul]
    ring
  have hgT : ∀ j ∈ T, g j = 0 := by
    intro j hj
    simp [hgf, hfT j hj]
  have hg0 : g ≠ 0 := by
    intro h
    have h' : stdH L m g g = 0 := by rw [h]; simp
    rw [hgf, hHs, hHf] at h'
    have : (M : ℂ) * conj (M : ℂ) * (κ * Q) ≠ 0 := by
      simp only [map_natCast]
      exact mul_ne_zero (mul_ne_zero hMc hMc) (mul_ne_zero hκ hQ0)
    exact this h'
  have hgS : SatMem d Λ g := rep_sat_of_mem d Λ hMf hdp
  have hd1 : ¬ (d : ℤ) ∣ 1 := by
    intro h
    have := Int.eq_one_of_dvd_one (by positivity) h
    exact hdp.one_lt.ne' (by exact_mod_cast this)
  obtain ⟨y1, hy1S, hy1T, -, p1, q1, hp1, hq1, hy1H⟩ :=
    hU a b c d ha hd lam hlam m Λ x y T i₀ hK 0 (rep_sat_zero d Λ hdp) (by simp) (Or.inl rfl)
      g hgS hgT (by simp) hg0
  have hp1c : (p1 : ℂ) ≠ 0 := by
    have : p1 ≠ 0 := fun h => hp1 (h ▸ dvd_zero _)
    exact_mod_cast this
  have hq1c : (q1 : ℂ) ≠ 0 := by
    have : q1 ≠ 0 := fun h => hq1 (h ▸ dvd_zero _)
    exact_mod_cast this
  obtain ⟨n', c₂, s', hs', hpair⟩ := sat_pair hOK hsd hθ hdp hgS hy1S
  rw [← hL, ← hκdef] at hy1H hpair
  have hs'c : (s' : ℂ) ≠ 0 := by
    have : s' ≠ 0 := fun h => hs' (h ▸ dvd_zero _)
    exact_mod_cast this
  have hθc : conj (cmTheta b d) = (b : ℂ) - cmTheta b d := by
    have := rep_theta_add_conj b d
    linear_combination this
  set γ0 : ℂ := (q1 : ℂ) * ((n' : ℂ) - c₂ * conj (cmTheta b d)) with hγ0
  set z : m → ℂ := (((p1 * s' : ℤ) : ℂ)) • g - γ0 • y1 with hz
  have hzS : SatMem d Λ z := by
    have h1 := rep_sat_zsmul d Λ hgS (p1 * s')
    have h2 := rep_sat_elt d Λ hdp hθ hy1S (q1 * n') (q1 * c₂) 1 hd1
    have h3 : ((((q1 * n' : ℤ) : ℂ) - ((q1 * c₂ : ℤ) : ℂ) * conj (cmTheta b d)) / ((1 : ℤ) : ℂ)) = γ0 := by
      rw [hγ0]; push_cast; ring
    rw [h3] at h2
    exact rep_sat_sub d Λ hdp h1 h2
  have hzT : ∀ j ∈ T, z j = 0 := by
    intro j hj
    simp [hz, hgT j hj, hy1T j hj]
  have hzy : stdH L m z y1 = 0 := by
    have e1 : stdH L m z y1 = ((p1 * s' : ℤ) : ℂ) * stdH L m g y1 - γ0 * stdH L m y1 y1 := by
      simp only [hz, map_sub, map_smul, LinearMap.sub_apply, LinearMap.smul_apply, smul_eq_mul]
    rw [e1, hpair, hy1H, hγ0]
    push_cast
    field_simp
    ring
  by_cases hz0 : z = 0
  · set r : ℂ := ((p1 * s' : ℤ) : ℂ) * M with hr
    have hr0 : r ≠ 0 := by
      rw [hr]; push_cast
      exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
    have hrc : conj r = r := by rw [hr]; simp
    have hrf : r • f = γ0 • y1 := by
      have : ((p1 * s' : ℤ) : ℂ) • g = γ0 • y1 := sub_eq_zero.mp (by rw [← hz]; exact hz0)
      rw [hgf, smul_smul] at this
      simpa [hr] using this
    set β : ℂ := γ0 / r with hβ
    have hβN : β * conj β = ((Q * q1 : ℤ) : ℂ) / ((p1 : ℤ) : ℂ) := by
      have e := congrArg (fun v => stdH L m v v) hrf
      simp only [hHs, hHf, hy1H, hrc] at e
      field_simp at e
      rw [hβ, map_div₀, hrc, div_mul_div_comm, div_eq_div_iff (mul_ne_zero hr0 hr0) hp1c]
      push_cast
      linear_combination -e
    have hβK : IsK b d β := by
      refine ⟨q1 * (n' - c₂ * b), q1 * c₂, p1 * s' * M, ?_, ?_⟩
      · have : ((p1 * s' * M : ℤ) : ℂ) ≠ 0 := by
          push_cast; exact mul_ne_zero (mul_ne_zero hp1c hs'c) hMc
        exact_mod_cast this
      · rw [hβ, hγ0, hθc]
        have : ((p1 * s' * (M : ℤ) : ℤ) : ℂ) = r := by rw [hr]; push_cast; ring
        rw [this]
        field_simp
        push_cast
        ring
    have hQq : ¬ (d : ℤ) ∣ Q * q1 := not_dvd_mul' hdp hQ hq1
    obtain ⟨s, hs⟩ := norm_square hOK hβK hQq hp1 hβN
    obtain ⟨k, hk⟩ := hs
    refine ⟨(s : ℂ) • y1, ⟨rep_sat_zsmul d Λ hy1S s, ?_, k, Q * q1, hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj]
    · rw [hHs, hy1H, hHf]
      have hk' : (s : ℂ) ^ 2 * p1 = Q * q1 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      simp only [map_intCast]
      push_cast
      field_simp
      linear_combination hk'
  · obtain ⟨y2, hy2S, hy2T, hy21, p2, q2, hp2, hq2, hy2H⟩ :=
      hU a b c d ha hd lam hlam m Λ x y T i₀ hK y1 hy1S hy1T (Or.inr ⟨p1, q1, hp1, hq1, by
        rw [hy1H]⟩) z hzS hzT hzy hz0
    rw [← hL, ← hκdef] at hy2H
    rw [← hL] at hy21
    have hp2c : (p2 : ℂ) ≠ 0 := by
      have : p2 ≠ 0 := fun h => hp2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hq2c : (q2 : ℂ) ≠ 0 := by
      have : q2 ≠ 0 := fun h => hq2 (h ▸ dvd_zero _)
      exact_mod_cast this
    have hy12 : stdH L m y1 y2 = 0 := by
      have := rep_H_conj (L := L) (m := m) y2 y1
      rw [hy21, map_zero] at this
      exact this.symm
    have hodd : d % 2 = 1 := by
      have := hOK.2.2.1
      omega
    obtain ⟨s, t, hst⟩ := pigeon hdp hodd (p1 * q2) (p2 * q1) (Q * q1 * q2)
      (not_dvd_mul' hdp hp1 hq2) (not_dvd_mul' hdp hp2 hq1)
    obtain ⟨k, hk⟩ := hst
    have hQq : ¬ (d : ℤ) ∣ Q * (q1 * q2) := not_dvd_mul' hdp hQ (not_dvd_mul' hdp hq1 hq2)
    refine ⟨(s : ℂ) • y1 + (t : ℂ) • y2,
      ⟨rep_sat_add d Λ hdp (rep_sat_zsmul d Λ hy1S s) (rep_sat_zsmul d Λ hy2S t), ?_, k, Q * (q1 * q2), hQq, ?_⟩⟩
    · intro j hj; simp [hy1T j hj, hy2T j hj]
    · have e : stdH L m ((s : ℂ) • y1 + (t : ℂ) • y2) ((s : ℂ) • y1 + (t : ℂ) • y2) =
          (s : ℂ) ^ 2 * stdH L m y1 y1 + (t : ℂ) ^ 2 * stdH L m y2 y2 := by
        simp only [map_add, LinearMap.add_apply, hHs, hy12, hy21, map_intCast]
        ring
      rw [e, hy1H, hy2H, hHf]
      have hk' : (s : ℂ) ^ 2 * (p1 * q2) + (t : ℂ) ^ 2 * (p2 * q1) = Q * q1 * q2 + d * k := by
        have := congrArg (fun t : ℤ => (t : ℂ)) hk
        push_cast at this
        linear_combination this
      push_cast
      field_simp
      linear_combination hk'

end PI.UnitaryGroupMassFormula.UnimodLocStd
