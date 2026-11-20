import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.FinitePrimesUnder
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.VacuumUnderAdelicPairModulusOne
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ThetaSpanRationalTranslatesVacuum
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ApplyAt0Smul
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaFunctionRationalTranslateMemStatement
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsMovesOfSelfDual
open Formalism.BasicNotions Formalism.IndefR.Links IsDedekindDomain NumberField Polynomial
open scoped Pointwise nonZeroDivisors
open Formalism.L2.Host (HChar embTau)
open GlobalTheory.ChiGrid GlobalTheory.LeafRestExamples
open Formalism.MainNotions Formalism.MainNotions.TaylorLogMetric Formalism.MainNotions.StandardLatticesGL3 GlobalTheory.NormSum GlobalTheory.FunObj GlobalTheory.FunObj.SqNum

noncomputable section

namespace GlobalTheory.NuTrivSq
variable {D : D7}
open GlobalTheory.Mem.Col2.SplitChar in

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, s, hs, rfl⟩` from `hy`. Rewrite using `[map_mul, vl_inc]`. Use `(mul_le_of_le_one_right' (vl_le hs PP)).trans ?_` and prove the remaining obligations.

Rewrite using `[HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `(HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)`. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)`. Consider the case `neg a _ ha => rwa [Valuation.map_neg]`.
-/
theorem vl_le_of_mem_hatId' {I : Ideal (𝓞 D.host.E)} {PP : HeightOneSpectrum (𝓞 D.host.E)} {n : ℕ}
    (hI : I ≤ PP.asIdeal ^ n) {x : AE D} (hx : x ∈ hatId D I) : vl D PP x ≤ WithZero.exp (-(n : ℤ)) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    rw [map_mul, vl_inc]
    refine (mul_le_of_le_one_right' (vl_le hs PP)).trans ?_
    rw [HeightOneSpectrum.valuation_of_algebraMap]
    exact (HeightOneSpectrum.intValuation_le_pow_iff_mem PP b n).2 (hI hb)
  | zero => simp
  | add a b _ _ ha hb => exact (Valuation.map_add _ _ _).trans (max_le ha hb)
  | neg a _ ha => rwa [Valuation.map_neg]

open GlobalTheory.Mem.Col2.SplitChar in

/- English proof (translation)
Proceed by induction on `hx using AddSubgroup.closure_induction with`. Consider the case `mem y hy`. Take `⟨b, hb, s, hs, rfl⟩` from `hy`. Use `AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s, GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]`.

Both sides reduce to the same expression. Consider the case `zero => simp`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`. Consider the case `neg a _ ha => rw [map_neg]`.

Conclude with `neg_mem ha`.
-/
theorem sgA_mem_hatId' {I : Ideal (𝓞 D.host.E)} {x : AE D} (hx : x ∈ hatId D I) :
    sgA D x ∈ hatId D (D.host.conj • I) := by
  induction hx using AddSubgroup.closure_induction with
  | mem y hy =>
    obtain ⟨b, hb, s, hs, rfl⟩ := hy
    refine AddSubgroup.subset_closure ⟨D.host.conj • b, Ideal.smul_mem_pointwise_smul _ _ _ hb, sgA D s,
      GlobalTheory.NormSum.UnramHecke.sgA_mem D hs, ?_⟩
    rw [map_mul, GlobalTheory.Mem.Col2.SplitChar.sgA_inc]
    rfl
  | zero => simp
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | neg a _ ha => rw [map_neg]; exact neg_mem ha

/- English proof (translation)
Establish `h : D.host.conj * D.host.conj = 1` using `AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z`. Rewrite using `[smul_smul, h, one_smul]`.
-/
theorem conj_conj_smul (𝔪 : Ideal (𝓞 D.host.E)) : D.host.conj • D.host.conj • 𝔪 = 𝔪 := by
  have h : D.host.conj * D.host.conj = 1 := AlgEquiv.ext fun z => GlobalTheory.NormSum.UnramHecke.conj_conj D z
  rw [smul_smul, h, one_smul]

open GlobalTheory.Mem.Col2.SplitChar in

/- English proof (translation)
Take `⟨c, hc, hcm, -⟩` from `GlobalTheory.Mem.HostCM.host_cm D.R D.host`. Use `set v := PP.under (𝓞 D.host.F) with hvdef`. Establish `hw : (P.w v).under (𝓞 D.host.F) = v` using `P.under_w hv`. Establish `hle : condE P ≤ (P.w v).asIdeal ^ condExp P v` using `Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)`. Break down `(GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h` into its components or cases.

Rewrite using `[e]`. Conclude with `vl_le_of_mem_hatId' (e ▸ hle) h1`. Establish `e : c.toRingEquiv = D.host.conj.toRingEquiv` using `RingEquiv.ext hc`. Rewrite `h` using `[e]`. Rewrite using `[← GlobalTheory.NormSum.UnramHecke.sgA_sgA D y, vl_sgA h]`.

Establish `h3` using `sgA_mem_hatId' h2`. Rewrite `h3` using `[conj_conj_smul]`. Conclude with `vl_le_of_mem_hatId' hle h3`.
-/
theorem vl_sub_le' {T : Type} {L : LevCh D T} (P : Places L) {y : AE D}
    (h1 : y ∈ hatId D (condE P)) (h2 : y ∈ hatId D (D.host.conj • condE P))
    {PP : HeightOneSpectrum (𝓞 D.host.E)} (hv : PP.under (𝓞 D.host.F) ∈ P.S0) :
    vl D PP y ≤ WithZero.exp (-(condExp P (PP.under (𝓞 D.host.F)) : ℤ)) := by
  obtain ⟨c, hc, hcm, -⟩ := GlobalTheory.Mem.HostCM.host_cm D.R D.host
  set v := PP.under (𝓞 D.host.F) with hvdef
  have hw : (P.w v).under (𝓞 D.host.F) = v := P.under_w hv
  have hle : condE P ≤ (P.w v).asIdeal ^ condExp P v := Ideal.le_of_dvd (Finset.dvd_prod_of_mem _ hv)
  rcases (GlobalTheory.Mem.Chr.under_eq_iff_conjPl c hcm.rank hcm.ne (P.w v) PP).1 (by rw [hw]) with e | h
  · rw [e]
    exact vl_le_of_mem_hatId' (e ▸ hle) h1
  · have e : c.toRingEquiv = D.host.conj.toRingEquiv := RingEquiv.ext hc
    rw [e] at h
    rw [← GlobalTheory.NormSum.UnramHecke.sgA_sgA D y, vl_sgA h]
    have h3 := sgA_mem_hatId' h2
    rw [conj_conj_smul] at h3
    exact vl_le_of_mem_hatId' hle h3

end GlobalTheory.NuTrivSq

open GlobalTheory.Mem.Col2.SplitChar Formalism.L2.Host GlobalTheory.NuTrivSq in

/- English proof (translation)
Introduce `D T L sc G i j μ₀ hL u hu hc1 hc2`. Use `GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j).2.1 (finIdl D u) (finIdl_unit hu) (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_` and prove the remaining obligations. Establish `hunit : IsUnitAt PP x`. Unfold `IsUnitAt`. Rewrite using `[hx]`.

Conclude with `finIdl_unit hu PP`. Establish `hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1)`. Rewrite using `[hx, vl_sub_one]`. Establish `hμ : (L.C.mu0 j).loc PP x = 1`. Distinguish the cases in `hg : ∃ k, OverP D.host (D.host.g k) PP`.

Take `⟨k, hk⟩` from `hg`. Establish `hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0`. Use `G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))` and prove the remaining obligations. Establish `: ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal`. Express the relevant statement in the definitionally equal form `_ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))`.

Rewrite using `[Ideal.mem_comap, map_natCast]`. Conclude with `hk`. Use `fin_cases k`. Conclude with `Or.inl this`. Conclude with `Or.inr (Or.inl this)`.

Use `(L.C.isMu0 j).tame PP x hunit ?_` and prove the remaining obligations. Rewrite using `[hsub]`. Use `(vl_sub_le' G.pl hc1 hc2 hS).trans ?_` and prove the remaining obligations. Apply the tactic sequence `have : 1 ≤ condExp G.pl (PP.under (𝓞 D.host.F)) := by unfold condExp; split_ifs <;> omega`. Conclude with `WithZero.exp_le_exp.2 (by omega)`.

Use `push_neg at hg`. Conclude with `(L.C.isMu0 j).unr PP hg x hunit`. Establish `hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1`. Establish `h1 : 1 ≤ D.R.m - (i : ℕ)` using `by omega`. Establish `h2 : D.R.m - (i : ℕ) ≤ D.R.m` using `by omega`.

Distinguish the cases in `hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0`. Establish `hb` using `vl_sub_le' G.pl hc1 hc2 hS`. Rewrite `hb` using `[← hsub]`. Break down `G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'` into its components or cases. Rewrite `hb` using `[condExp, if_pos h0]`.

Conclude with `(G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)`. Establish `hne : PP.under (𝓞 D.host.F) ≠ G.pl.v0` using `fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')`. Rewrite `hb` using `[condExp, if_neg hne]`. Conclude with `(G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)`. Conclude with `G.ch.unr _ h1 h2 PP hS x hunit`.

Use `show (nuH G μ₀ i j).loc PP x = 1`. Rewrite using `[nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hμ, hχ]`. Simplify using the standard rewrite rules.
-/
theorem GlobalTheory.NuTrivSq.nuH_finIdl_eq_one : ∀ {D : D7} {T : Type} {L : LevCh D T} {sc : Consts} (G : GridData L sc) (i j : Fin D.R.m) {μ₀ : T},
    L.Is μ₀ → ∀ x : (AE D)ˣ, IntU D x → (x : AE D) - 1 ∈ hatId D (condE G.pl) →
      (x : AE D) - 1 ∈ hatId D (D.host.conj • condE G.pl) →
      (nuH G μ₀ i j).1 (GlobalTheory.Mem.Col2.SplitChar.finIdl D x) = 1 := by
  intro D T L sc G i j μ₀ hL u hu hc1 hc2
  refine GlobalTheory.Mem.LocTriv.eq_one_of_local D.host.E _ (nuH G μ₀ i j).2.1 (finIdl D u) (finIdl_unit hu)
    (fun w => by rw [finIdl_fst]; rfl) fun PP x hx => ?_
  have hunit : IsUnitAt PP x := by
    unfold IsUnitAt
    rw [hx]
    exact finIdl_unit hu PP
  have hsub : Valued.v ((x : PP.adicCompletion D.host.E) - 1) = vl D PP ((u : AE D) - 1) := by
    rw [hx, vl_sub_one]
  have hμ : (L.C.mu0 j).loc PP x = 1 := by
    by_cases hg : ∃ k, OverP D.host (D.host.g k) PP
    · obtain ⟨k, hk⟩ := hg
      have hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0 := by
        refine G.pl.mem_S0_of_sum_eq.2 (Or.inr ((S1_mem_OmF D).2 ?_))
        have : ((D.host.g k : ℕ) : 𝓞 D.host.F) ∈ (PP.under (𝓞 D.host.F)).asIdeal := by
          change _ ∈ PP.asIdeal.comap (algebraMap (𝓞 D.host.F) (𝓞 D.host.E))
          rw [Ideal.mem_comap, map_natCast]
          exact hk
        fin_cases k
        · exact Or.inl this
        · exact Or.inr (Or.inl this)
      refine (L.C.isMu0 j).tame PP x hunit ?_
      rw [hsub]
      refine (vl_sub_le' G.pl hc1 hc2 hS).trans ?_
      have : 1 ≤ condExp G.pl (PP.under (𝓞 D.host.F)) := by unfold condExp; split_ifs <;> omega
      exact WithZero.exp_le_exp.2 (by omega)
    · push_neg at hg
      exact (L.C.isMu0 j).unr PP hg x hunit
  have hχ : (G.ch.chiH (D.R.m - i)).loc PP x = 1 := by
    have h1 : 1 ≤ D.R.m - (i : ℕ) := by omega
    have h2 : D.R.m - (i : ℕ) ≤ D.R.m := by omega
    by_cases hS : PP.under (𝓞 D.host.F) ∈ G.pl.S0
    · have hb := vl_sub_le' G.pl hc1 hc2 hS
      rw [← hsub] at hb
      rcases G.pl.mem_S0_of_sum_eq.1 hS with h0 | h1'
      · rw [condExp, if_pos h0] at hb
        exact (G.ch.lev0 _ h1 h2 PP h0).1 x hunit (by simpa using hb)
      · have hne : PP.under (𝓞 D.host.F) ≠ G.pl.v0 := fun e => G.ch.basePlace_not_mem_chiGridBadPlaces (e ▸ h1')
        rw [condExp, if_neg hne] at hb
        exact (G.ch.lev1 _ h1 h2 PP h1').1 x hunit (by simpa using hb)
    · exact G.ch.unr _ h1 h2 PP hS x hunit
  show (nuH G μ₀ i j).loc PP x = 1
  rw [nuH, hL.xi_base, mul_one, div_eq_mul_inv, HChar.loc_mul, HChar.loc_inv, hμ, hχ]
  simp

end
