import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CosetVecEq
open scoped Pointwise
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3
open Formalism.L2.Host (HChar)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples GlobalTheory.FunObj.SqNum GlobalTheory.NormSum GlobalTheory.FunObj.StdDatum
open GlobalTheory.Mem.Col2.SplitChar (finIdl)

noncomputable section

namespace GlobalTheory.FunObj.SqNum.NuCond

open GlobalTheory.Mem.Col2.SplitChar GlobalTheory.Mem.Chr

/- English proof (translation)
Introduce `x hx hle` and use `h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))`.
-/
theorem levelLe_mono {K : Type} [Field K] [NumberField K] {χ : HChar K} {v : HeightOneSpectrum (𝓞 K)} {a b : ℕ}
    (h : χ.LevelLe v a) (hab : a ≤ b) : χ.LevelLe v b :=
  fun x hx hle => h x hx (hle.trans (WithZero.exp_le_exp.2 (neg_le_neg (Nat.cast_le.2 hab))))

variable {D : D7}

/- English proof (translation)
Use `show v.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) ≤ _`. Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le, Ideal.span_singleton_le_iff_mem]`. Conclude with `hb`.
-/
theorem val_le_of_mem_pow {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ} {b : 𝓞 D.host.E} (hb : b ∈ v.asIdeal ^ n) :
    v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ)) := by
  show v.valuation D.host.E (algebraMap (𝓞 D.host.E) D.host.E b) ≤ _
  rw [HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.intValuation_le_pow_iff_dvd, Ideal.dvd_iff_le,
    Ideal.span_singleton_le_iff_mem]
  exact hb

/- English proof (translation)
Proceed by induction on `hy using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨b, hb, s, hs, rfl⟩` from `hx`. Rewrite using `[map_mul, vl_inc]`. Conclude with `(mul_le_of_le_one_right' (vl_le hs v)).trans (h𝔪 b hb)`.

Consider the case `zero => rw [map_zero]`. Conclude with `zero_le'`. Consider the case `add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)`. Consider the case `neg x _ hx => rwa [Valuation.map_neg]`.
-/
theorem vl_le_of_mem_hatId {𝔪 : Ideal (𝓞 D.host.E)} {v : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (h𝔪 : ∀ b ∈ 𝔪, v.valuation D.host.E (b : D.host.E) ≤ WithZero.exp (-(n : ℤ))) {y : AE D} (hy : y ∈ hatId D 𝔪) :
    vl D v y ≤ WithZero.exp (-(n : ℤ)) := by
  induction hy using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hx
    rw [map_mul, vl_inc]
    exact (mul_le_of_le_one_right' (vl_le hs v)).trans (h𝔪 b hb)
  | zero => rw [map_zero]; exact zero_le'
  | add x y _ _ hx hy => exact (Valuation.map_add _ _ _).trans (max_le hx hy)
  | neg x _ hx => rwa [Valuation.map_neg]

/- English proof (translation)
The claim follows from `Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hs)`.
-/
theorem condE_le {T : Type} {L : LevCh D T} (P : Places L) {s : HeightOneSpectrum (𝓞 D.host.F)} (hs : s ∈ P.S0) :
    condE P ≤ (P.w s).asIdeal ^ condExp P s :=
  Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hs)

end GlobalTheory.FunObj.SqNum.NuCond

open GlobalTheory.FunObj.SqNum.NuCond GlobalTheory.Mem.Col2.SplitChar in

/- English proof (translation)
Introduce `D T L sc μ₀ hL G i j N χν hχ u hu hm`. Rewrite using `[hχ]`. Establish `k1 : 1 ≤ D.R.m - (i : ℕ)` using `by omega`. Establish `k2 : D.R.m - (i : ℕ) ≤ D.R.m` using `by omega`. Take `⟨c, hc, hcm, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`.

Take `⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v = if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0` from `⟨_, fun _ => rfl⟩`. Establish `hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v)`. Introduce `v`. Establish `hμ` using `L.C.isMu0 j`. Rewrite using `[show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]`.

Use `Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)` and prove the remaining obligations. Distinguish the cases in `h : v.under (𝓞 D.host.F) ∈ G.pl.S0`. Use `levelLe_mono (hμ.tame v) ?_` and prove the remaining obligations. Rewrite using `[hn v, if_pos h, condExp]`. Apply the tactic sequence `split_ifs <;> omega`.

Use `Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _` and prove the remaining obligations. Rewrite using `[G.pl.mem_S0_of_sum_eq]`. Use `right`. Rewrite using `[S1_mem_OmF]`. Establish `hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal` using `by show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hk`. Use `fin_cases k`. Conclude with `Or.inl hk'`. Conclude with `Or.inr (Or.inl hk')`.

Distinguish the cases in `h : v.under (𝓞 D.host.F) ∈ G.pl.S0`. Distinguish the cases in `h0 : v.under (𝓞 D.host.F) = G.pl.v0`. Rewrite using `[hn v, if_pos h, condExp, if_pos h0]`. Conclude with `(G.ch.lev0 _ k1 k2 v h0).1`. Establish `h1` using `(G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0`.

Rewrite using `[hn v, if_pos h, condExp, if_neg h0]`. Conclude with `(G.ch.lev1 _ k1 k2 v h1).1`. Rewrite using `[hn v, if_neg h]`. Conclude with `Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0`. Establish `hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ))`.

Introduce `v`. Distinguish the cases in `h : v.under (𝓞 D.host.F) ∈ G.pl.S0`. Rewrite using `[hn v, if_pos h]`. Use `vl_le_of_mem_hatId (fun b hb => ?_) hm` and prove the remaining obligations. Establish `hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F)` using `G.pl.w_over _ h`.

Break down `(GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e` into its components or cases. Establish `hb1 : b ∈ condE G.pl` using `Ideal.mul_le_left hb`. Establish `hb2` using `condE_le G.pl h hb1`. Rewrite `hb2` using `[← e]`. Conclude with `val_le_of_mem_pow hb2`.

Establish `hb1 : b ∈ D.host.conj • condE G.pl` using `Ideal.mul_le_right hb`. Rewrite `hb1` using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem]`. Establish `hb2` using `val_le_of_mem_pow (condE_le G.pl h hb1)`. Establish `e2` using `e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)`. Establish `e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E)` using `by show c _ = _`.

Rewrite using `[hc]`. Use `show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _`. Conclude with `AlgEquiv.apply_symm_apply _ _`. Rewrite `e2` using `[e3]`. Rewrite using `[e2]`.

Conclude with `hb2`. Rewrite using `[hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]`. Conclude with `vl_le (sub_mem hu.1 (one_mem _)) v`. Establish `hU` using `finIdl_unit hu`. Use `GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)` and prove the remaining obligations.

Establish `hxu : Formalism.L2.Host.IsUnitAt v x` using `by show Valued.v (x : v.adicCompletion D.host.E) = 1`. Rewrite using `[hx]`. Conclude with `hU v`. Use `(hlev v).inv x hxu ?_` and prove the remaining obligations. Rewrite using `[hx, vl_sub_one]`.

Conclude with `hval v`.
-/
theorem GlobalTheory.FunObj.SqNum.heckeU_nuInv_eq_one_of_cong : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} {μ₀ : T}, L.Is μ₀ → ∀ (G : GridData L sc) (i j : Fin D.R.m) {N : ℕ} (χν : HeckeU D N), (∀ x, χν.f x = (nuH G μ₀ i j)⁻¹.1 (finIdl D x)) → ∀ u, IntU D u → (u : AE D) - 1 ∈ hatId D (condE G.pl * D.host.conj • condE G.pl) → χν.f u = 1 := by
  classical
  intro D T L sc μ₀ hL G i j N χν hχ u hu hm
  rw [hχ]
  have k1 : 1 ≤ D.R.m - (i : ℕ) := by omega
  have k2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  obtain ⟨n, hn⟩ : ∃ n : HeightOneSpectrum (𝓞 D.host.E) → ℕ, ∀ v, n v =
      if v.under (𝓞 D.host.F) ∈ G.pl.S0 then condExp G.pl (v.under (𝓞 D.host.F)) else 0 := ⟨_, fun _ => rfl⟩
  have hlev : ∀ v, (nuH G μ₀ i j).LevelLe v (n v) := by
    intro v
    have hμ := L.C.isMu0 j
    rw [show nuH G μ₀ i j = L.C.mu0 j * L.xiH μ₀ / G.ch.chiH (D.R.m - i) from rfl, hL.xi_base, mul_one, div_eq_mul_inv]
    refine Formalism.L2.Host.HChar.LevelLe.mul ?_ (Formalism.L2.Host.HChar.LevelLe.inv ?_)
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · refine levelLe_mono (hμ.tame v) ?_
        rw [hn v, if_pos h, condExp]
        split_ifs <;> omega
      · refine Formalism.L2.Host.HChar.UnrAt.levelLe (hμ.unr v fun k hk => h ?_) _
        rw [G.pl.mem_S0_of_sum_eq]
        right
        rw [S1_mem_OmF]
        have hk' : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (v.under (𝓞 D.host.F)).asIdeal := by
          show _ ∈ v.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl hk'
        · exact Or.inr (Or.inl hk')
    · by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
      · by_cases h0 : v.under (𝓞 D.host.F) = G.pl.v0
        · rw [hn v, if_pos h, condExp, if_pos h0]
          exact (G.ch.lev0 _ k1 k2 v h0).1
        · have h1 := (G.pl.mem_S0_of_sum_eq.1 h).resolve_left h0
          rw [hn v, if_pos h, condExp, if_neg h0]
          exact (G.ch.lev1 _ k1 k2 v h1).1
      · rw [hn v, if_neg h]
        exact Formalism.L2.Host.HChar.UnrAt.levelLe (G.ch.unr _ k1 k2 v h) 0
  have hval : ∀ v, vl D v ((u : AE D) - 1) ≤ WithZero.exp (-(n v : ℤ)) := by
    intro v
    by_cases h : v.under (𝓞 D.host.F) ∈ G.pl.S0
    · rw [hn v, if_pos h]
      refine vl_le_of_mem_hatId (fun b hb => ?_) hm
      have hw : (G.pl.w (v.under (𝓞 D.host.F))).under (𝓞 D.host.F) = v.under (𝓞 D.host.F) := G.pl.w_over _ h
      rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (G.pl.w (v.under (𝓞 D.host.F))) v).1 hw.symm with e | e
      · have hb1 : b ∈ condE G.pl := Ideal.mul_le_left hb
        have hb2 := condE_le G.pl h hb1
        rw [← e] at hb2
        exact val_le_of_mem_pow hb2
      · have hb1 : b ∈ D.host.conj • condE G.pl := Ideal.mul_le_right hb
        rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem] at hb1
        have hb2 := val_le_of_mem_pow (condE_le G.pl h hb1)
        have e2 := e (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E)
        have e3 : c.toRingEquiv (((D.host.conj⁻¹ • b : 𝓞 D.host.E)) : D.host.E) = (b : D.host.E) := by
          show c _ = _
          rw [hc]
          show D.host.conj (D.host.conj⁻¹ (b : D.host.E)) = _
          exact AlgEquiv.apply_symm_apply _ _
        rw [e3] at e2
        rw [e2]
        exact hb2
    · rw [hn v, if_neg h, Nat.cast_zero, neg_zero, WithZero.exp_zero]
      exact vl_le (sub_mem hu.1 (one_mem _)) v
  have hU := finIdl_unit hu
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j)⁻¹.2.1 (finIdl D u) hU
    (fun w => by rw [finIdl_fst]; rfl) (fun v x hx => ?_)
  have hxu : Formalism.L2.Host.IsUnitAt v x := by
    show Valued.v (x : v.adicCompletion D.host.E) = 1
    rw [hx]
    exact hU v
  refine (hlev v).inv x hxu ?_
  rw [hx, vl_sub_one]
  exact hval v

end
