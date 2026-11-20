import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.DiscriminantPowEightLeSqrt
import Formalism.SharpRestriction.GenusPolyhedralBounds.RelativeIndexClassSets.BaseDegreeAtLiftIndex

noncomputable section

open Formalism.MainNotions.WeightAlgebra Formalism.BasicNotions NumberField IsDedekindDomain Module

namespace Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

variable {D : D7} {L : SizeData₂ D} {P : ParameterChoice' D L}

/- English proof (translation)
Rewrite using `[T.Dp_eq]`. Unfold `WeightFamilies.dimY Ranks.sigW Ranks.r`. Simplify using `[Nat.choose_two_right]`.
-/
theorem dm_eq (T : ParamsT D L P) : WeightFamilies.dimY D D.R.m = T.Dp := by
  rw [T.Dp_eq]
  unfold WeightFamilies.dimY Ranks.sigW Ranks.r
  simp [Nat.choose_two_right]

/- English proof (translation)
Unfold `q0N`. Establish `hT40` using `T.TO_40`. Establish `hTpos : (0 : ℝ) < (T.TO : ℝ)` using `by exact_mod_cast (show 0 < T.TO by omega)`. Establish `hZ' : (1 : ℝ) ≤ zBase L`. Establish `h : (1 : ℝ) ≤ 10 ^ 60` using `by norm_num`.

Combine the linear equalities and inequalities to obtain the conclusion. Establish `hPP : 1 ≤ T.PP`. Rewrite using `[T.PP_eq]`. Conclude with `one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))`. Establish `hbpos : 0 < L.sc.b` using `by unfold Scale.b; exact Real.exp_pos _`.

Establish `h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ)` using `le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'`. Establish `h2` using `mul_self_le_mul_self hTpos.le h1`. Rewrite `h2` using `[← Real.rpow_add hbpos]`. Evaluate the numerical expressions using `at h2`. Establish `hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ)`.

Rewrite using `[le_div_iff₀ hTpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Conclude with `le_trans hq (Nat.le_ceil _)` after adjusting the coercions.
-/
theorem order_le_modulus (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : T.TO ≤ q0N T := by
  unfold q0N
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hZ' : (1 : ℝ) ≤ zBase L := by
    have h : (1 : ℝ) ≤ 10 ^ 60 := by norm_num
    linarith
  have hPP : 1 ≤ T.PP := by
    rw [T.PP_eq]
    exact one_le_mul_of_one_le_of_one_le T.one_le_CP (Real.one_le_rpow hZ' (by linarith [T.eP_ge]))
  have hbpos : 0 < L.sc.b := by unfold Scale.b; exact Real.exp_pos _
  have h1 : (T.TO : ℝ) ≤ L.sc.b ^ (1 / 2 : ℝ) := le_trans (le_mul_of_one_le_right hTpos.le hPP) T.TO_PP'
  have h2 := mul_self_le_mul_self hTpos.le h1
  rw [← Real.rpow_add hbpos] at h2
  norm_num at h2
  have hq : (T.TO : ℝ) ≤ L.sc.b / (T.TO : ℝ) := by
    rw [le_div_iff₀ hTpos]
    linarith
  exact_mod_cast le_trans hq (Nat.le_ceil _)

abbrev runOf (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L) : RunN D where
  T := T.TO
  nW := T.nWn
  nP := T.nP
  Q0 := q0N T
  T_pos := by have := T.TO_40; omega
  nW_even := T.nW_even
  even_nP₂ := T.even_nP₂
  split := T.split
  nP_le_nW := T.nW_lo.2.2
  hQ0 := by
    rw [dm_eq T]
    have := T.TO_nW; have := order_le_modulus T S hZ
    omega

def Kc0 : KAdm := ⟨1, 1, 1, 1, 1, 1, 1, 1, 2⟩

def NonvanishingSectionCondition (T : ParamsT D L P) : KHyp := ⟨10, 20, 1000, 12, T.CP, T.eP, 2⟩

section Run

variable (T : ParamsT D L P) (S : SizesAt L) (hZ : 10 ^ 60 ≤ zBase L)

/- English proof (translation)
Unfold `RunN.Tq Tp`. Simplify using `only [runOf]`. Rewrite using `[dm_eq T]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eTq : ((runOf T S hZ).Tq : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) := by
  unfold RunN.Tq Tp
  dsimp only [runOf]
  rw [dm_eq T]
  push_cast
  ring

/- English proof (translation)
Unfold `RunN.Q`. Use `push_cast`. Combine the linear relations using `[eTq T S hZ]`.
-/
theorem eQ : ((runOf T S hZ).Q : ℝ) = (T.TO : ℝ) + ((T.Dp : ℝ) + 2) + 2 * D.R.r := by
  unfold RunN.Q
  push_cast
  linarith [eTq T S hZ]

/- English proof (translation)
Unfold `RunN.kl`. Use `push_cast`. Rewrite using `[eTq T S hZ]`. Establish `hd : (Dm D : ℝ) = (T.Dp : ℝ)` using `by first`. Consider the case `(unfold Dm; exact_mod_cast dm_eq T)`.

Consider the case `(simp only [Dm]; exact_mod_cast dm_eq T)`. Consider the case `exact_mod_cast dm_eq T`. Rewrite using `[hd]`.
-/
theorem ekl : ((runOf T S hZ).kl : ℝ) =
    ((T.Dp : ℝ) + 2) * T.nWn + 2 * D.R.r + ((T.TO : ℝ) + ((T.Dp : ℝ) + 2)) * (q0N T : ℝ) := by
  unfold RunN.kl
  push_cast
  rw [eTq T S hZ]
  have hd : (Dm D : ℝ) = (T.Dp : ℝ) := by
    first
    | (unfold Dm; exact_mod_cast dm_eq T)
    | (simp only [Dm]; exact_mod_cast dm_eq T)
    | exact_mod_cast dm_eq T
  rw [hd]

/- English proof (translation)
Establish `h` using `T.split`. Unfold `Ranks.nV`. Conclude with `h` after adjusting the coercions.
-/
theorem enV : (D.R.nV : ℝ) = (T.nP : ℝ) + (T.TO : ℝ) * T.nWn := by
  have h := T.split
  unfold Ranks.nV
  exact_mod_cast h

/- English proof (translation)
Use `(rn_of T S hZ).sK ?_` and prove the remaining obligations. Establish `h` using `(runOf T S hZ).ka_size_le`. Rewrite `h` using `[ekl, eTq, eQ, enV T]`. Conclude with `h`.
-/
theorem ka_le : (runOf T S hZ).ka.size ≤ 4 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sK ?_
  have h := (runOf T S hZ).ka_size_le
  rw [ekl, eTq, eQ, enV T] at h
  exact h

/- English proof (translation)
Rewrite using `[ekl T S hZ]`. Establish `hT40` using `T.TO_40`. Establish `hTpos : (0 : ℝ) < (T.TO : ℝ)` using `by exact_mod_cast (show 0 < T.TO by omega)`. Establish `hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ)` using `by unfold q0N; exact Nat.le_ceil _`. Establish `hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ)`.

Rewrite `hq` using `[div_le_iff₀ hTpos]`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `h0 : (0 : ℝ) ≤ (T.Dp : ℝ)` using `by positivity`. Establish `h1 : (0 : ℝ) ≤ (T.nWn : ℝ)` using `by positivity`. Establish `h2 : (0 : ℝ) ≤ (q0N T : ℝ)` using `by positivity`.

Establish `h3 : (0 : ℝ) ≤ (D.R.r : ℝ)` using `by positivity`. Use polynomial arithmetic with `[mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1, mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]`.
-/
theorem b_le_kl : L.sc.b ≤ ((runOf T S hZ).kl : ℝ) := by
  rw [ekl T S hZ]
  have hT40 := T.TO_40
  have hTpos : (0 : ℝ) < (T.TO : ℝ) := by exact_mod_cast (show 0 < T.TO by omega)
  have hq : L.sc.b / (T.TO : ℝ) ≤ (q0N T : ℝ) := by unfold q0N; exact Nat.le_ceil _
  have hq' : L.sc.b ≤ (T.TO : ℝ) * (q0N T : ℝ) := by
    rw [div_le_iff₀ hTpos] at hq
    linarith
  have h0 : (0 : ℝ) ≤ (T.Dp : ℝ) := by positivity
  have h1 : (0 : ℝ) ≤ (T.nWn : ℝ) := by positivity
  have h2 : (0 : ℝ) ≤ (q0N T : ℝ) := by positivity
  have h3 : (0 : ℝ) ≤ (D.R.r : ℝ) := by positivity
  nlinarith [mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h1,
    mul_nonneg (add_nonneg h0 (by norm_num : (0 : ℝ) ≤ 2)) h2]

/- English proof (translation)
The claim follows from `(b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge`.
-/
theorem b_le_ka : L.sc.b ≤ (runOf T S hZ).ka.size := (b_le_kl T S hZ).trans (runOf T S hZ).ka_size_ge

/- English proof (translation)
Use `(rn_of T S hZ).sL ?_` and prove the remaining obligations. Establish `h` using `(runOf T S hZ).wL_size_le`. Rewrite `h` using `[eQ]`. Conclude with `h`.
-/
theorem wL_le : (runOf T S hZ).wL.size * (T.TO : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).sL ?_
  have h := (runOf T S hZ).wL_size_le
  rw [eQ] at h
  exact h

/- English proof (translation)
Use `(rn_of T S hZ).dL ?_` and prove the remaining obligations. Establish `h` using `(runOf T S hZ).DF_wL_le`. Rewrite `h` using `[eQ]`. Conclude with `h`.
-/
theorem dF_le : (DF (runOf T S hZ).wL : ℝ) ≤ 2 * ((D.R.f : ℝ) * D.R.r) * L.sc.b := by
  refine (rn_of T S hZ).dL ?_
  have h := (runOf T S hZ).DF_wL_le
  rw [eQ] at h
  exact h

/- English proof (translation)
Take `⟨Y, h1, -, -, h2⟩` from `P.g_Y`. Conclude with `h1.trans (h2 i).1`.
-/
theorem g_ge (P : ParameterChoice' D L) (i : Fin 2) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (D.host.g i : ℝ) := by
  obtain ⟨Y, h1, -, -, h2⟩ := P.g_Y
  exact h1.trans (h2 i).1

/- English proof (translation)
Unfold `qq`. Use `first`. Consider the case `(rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))`. Consider the case `(push_cast; exact le_min (g_ge P 0) (g_ge P 1))`.
-/
theorem qq_ge (P : ParameterChoice' D L) : ((D.R.k : ℝ) * L.sc.b) ^ 8 ≤ (qq D : ℝ) := by
  unfold qq
  first
  | (rw [Nat.cast_min]; exact le_min (g_ge P 0) (g_ge P 1))
  | (push_cast; exact le_min (g_ge P 0) (g_ge P 1))

/- English proof (translation)
Unfold `WeightFamilies.RRv`. Use `first`. Consider the case `rfl`. Consider the case `simp`.
-/
theorem eRR : WeightFamilies.RRv D 2 = D.host.rdE ^ 2 := by
  unfold WeightFamilies.RRv
  first
  | rfl
  | simp

/- English proof (translation)
Unfold `g0`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem eg0 : (g0 D : ℝ) = 1250 * D.R.r := by
  unfold g0
  push_cast
  ring

/- English proof (translation)
Unfold `WeightFamilies.PPv`. Simplify using the standard rewrite rules.
-/
theorem growth_at_one_eq_zBase : WeightFamilies.PPv D L 1 1 = zBase L := by
  unfold WeightFamilies.PPv
  simp

/- English proof (translation)
Establish `hR` using `rn_of T S hZ`. Establish `hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ)` using `Nat.cast_nonneg _`. Establish `hd` using `dF_le T S hZ`. Establish `hq` using `qq_ge P`. Establish `hq0 : (0 : ℝ) < (qq D : ℝ)` using `lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq`.

Establish `hb` using `hR.h3b hd0 hd hq`. Establish `hx1 : 1 ≤ L.sc.x ^ T.Cp` using `Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg`. Establish `hfk : (D.R.f : ℝ) ≤ D.R.k` using `by exact_mod_cast f_le_k D`. Establish `hmk : (D.R.m : ℝ) ≤ D.R.k`. Use `D.R.m_add_three_le_k` as an intermediate fact.

Conclude with `(by omega : D.R.m ≤ D.R.k)` after adjusting the coercions. Establish `hm0 : (0 : ℝ) < D.R.m`. Use `D.R.two_le_m` as an intermediate fact. Conclude with `(by omega : 0 < D.R.m)` after adjusting the coercions. Use `⟨?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]`. Conclude with `hR.h3a hd0 hd hq`. Rewrite using `[Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]`. Conclude with `hb`. Rewrite using `[Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]`.

Use `le_trans ?_ T.TO_ge` and prove the remaining obligations. Establish `hden : 0 < (D.R.m : ℝ) * L.de2` using `mul_pos hm0 L.thickDensity_pos`. Apply `div_le_div_of_nonneg_right _ hden.le` to reduce the goal to its premises. Establish `hP` using `hR.PP_pos`. Conclude with `le_mul_of_one_le_right (by positivity) hx1`.

Use `show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1`. Rewrite using `[eRR, WeightFamilies.PPv_rec T, eg0]`. Establish `e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) = ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ)` using `by ring`. Rewrite using `[e, div_le_one hq0]`. Conclude with `hb`.

Use `show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2`. Rewrite using `[eRR, WeightFamilies.PPv_rec T]`. Establish `hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4`. Establish `: (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3` using `pow_le_pow_left₀ hm0.le hmk 3`. Combine the equalities or inequalities in the displayed calculation.

Establish `he` using `hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm`. Establish `e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) = ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ)` using `by ring`. Rewrite using `[e, div_le_iff₀ hq0]`. Combine the linear equalities and inequalities to obtain the conclusion. Rewrite using `[dm_eq T]`.

Use `hR.h3f hd0 hd hq` as an intermediate fact. Establish `e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4` using `by ring`. Rewrite `this` using `[e]`. Conclude with `this`.
-/
theorem third_hypothesis_of_params : H3 L (NonvanishingSectionCondition T) T.CP T.eP 2 0 (runOf T S hZ).wL T.TO := by
  have hR := rn_of T S hZ
  have hd0 : (0 : ℝ) ≤ (DF (runOf T S hZ).wL : ℝ) := Nat.cast_nonneg _
  have hd := dF_le T S hZ
  have hq := qq_ge P
  have hq0 : (0 : ℝ) < (qq D : ℝ) := lt_of_lt_of_le (by have := hR.b_pos; have := hR.k1; positivity) hq
  have hb := hR.h3b hd0 hd hq
  have hx1 : 1 ≤ L.sc.x ^ T.Cp := Real.one_le_rpow L.sc.one_lt_alt.le T.Cp_nonneg
  have hfk : (D.R.f : ℝ) ≤ D.R.k := by exact_mod_cast f_le_k D
  have hmk : (D.R.m : ℝ) ≤ D.R.k := by
    have := D.R.m_add_three_le_k
    exact_mod_cast (by omega : D.R.m ≤ D.R.k)
  have hm0 : (0 : ℝ) < D.R.m := by
    have := D.R.two_le_m
    exact_mod_cast (by omega : 0 < D.R.m)
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T]
    exact hR.h3a hd0 hd hq
  · rw [Real.rpow_zero, one_mul, eRR, WeightFamilies.PPv_rec T, eg0]
    exact hb
  · rw [Real.rpow_zero, one_mul, WeightFamilies.PPv_rec T, dm_eq T]
    refine le_trans ?_ T.TO_ge
    have hden : 0 < (D.R.m : ℝ) * L.de2 := mul_pos hm0 L.thickDensity_pos
    apply div_le_div_of_nonneg_right _ hden.le
    have hP := hR.PP_pos
    exact le_mul_of_one_le_right (by positivity) hx1
  · show (T.TO : ℝ) * (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * g0 D ≤ 1
    rw [eRR, WeightFamilies.PPv_rec T, eg0]
    have e : (T.TO : ℝ) * (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) * (1250 * D.R.r) =
        ((T.TO : ℝ) * (1250 * D.R.r) * D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2) / (qq D : ℝ) := by ring
    rw [e, div_le_one hq0]
    exact hb
  · show (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * WeightFamilies.RRv D 2 ^ 2 *
      (WeightFamilies.RRv D 2 * WeightFamilies.PPv D L T.CP T.eP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) ≤ 1 / 2
    rw [eRR, WeightFamilies.PPv_rec T]
    have hfm : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 4 := by
      have : (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) ^ 3 := pow_le_pow_left₀ hm0.le hmk 3
      calc (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 ≤ (D.R.k : ℝ) * (D.R.k : ℝ) ^ 3 :=
            mul_le_mul hfk this (by positivity) (by positivity)
        _ = (D.R.k : ℝ) ^ 4 := by ring
    have he := hR.h3e hd0 hd hq (fm := (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3) (by positivity) hfm
    have e : (D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2 / (qq D : ℝ)) =
        ((D.R.f : ℝ) * (D.R.m : ℝ) ^ 3 * (D.host.rdE ^ 2) ^ 2 *
        (D.host.rdE ^ 2 * T.PP * (DF (runOf T S hZ).wL : ℝ) ^ 2)) / (qq D : ℝ) := by ring
    rw [e, div_le_iff₀ hq0]
    linarith
  · rw [dm_eq T]
    have := hR.h3f hd0 hd hq
    have e : (T.Dp : ℝ) + 2 + 2 = (T.Dp : ℝ) + 4 := by ring
    rw [e] at this
    exact this

end Run

end Formalism.MainNotions.Gaps.EtaleWeightGaps.Num

end
