import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.Entire
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HeckeCharacterRamifiedFinite

open NumberField IsDedekindDomain
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
open UpperTheory.ConvolutionTheory.RankTwoDescent
open HeckeValGen GlobalTheory.HeckeSplit

namespace UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

/- English proof (translation)
Proceed by induction on `c with`. Consider the case `zero => simp`. Consider the case `succ c ih`. Use `push_cast`. Conclude with `Valuation.map_add_le _ ih (by simp)`.
-/
private theorem nat_le_one (v : H.P ℚ) (c : ℕ) : Valued.v (c : H.Kv v) ≤ 1 := by
  induction c with
  | zero => simp
  | succ c ih =>
    push_cast
    exact Valuation.map_add_le _ ih (by simp)

/- English proof (translation)
Take `⟨c, rfl⟩` from `h`. Use `push_cast`. Rewrite using `[map_mul]`. Conclude with `mul_le_of_le_one_right' (nat_le_one v c)`.
-/
private theorem dvd_le (v : H.P ℚ) {a b : ℕ} (h : a ∣ b) : Valued.v (b : H.Kv v) ≤ Valued.v (a : H.Kv v) := by
  obtain ⟨c, rfl⟩ := h
  push_cast
  rw [map_mul]
  exact mul_le_of_le_one_right' (nat_le_one v c)

/- English proof (translation)
Establish `h0 : Ideal.absNorm v.asIdeal ≠ 0`. Rewrite using `[Ne, Ideal.absNorm_eq_zero_iff]`. Conclude with `v.ne_bot`. Use `⟨Ideal.absNorm v.asIdeal ^ n, pow_pos (Nat.pos_of_ne_zero h0) n, ?_⟩` and prove the remaining obligations. Establish `hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n ∈ v.asIdeal ^ n` using `Ideal.pow_mem_pow (Ideal.absNorm_mem _) n`.

Establish `h1` using `(v.intValuation_le_pow_iff_mem _ n).2 hm`. Establish `h3 : Valued.v ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) ≤ WithZero.exp (-(n : ℤ))`. Rewrite using `[HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]`. Conclude with `h1`. Establish `h2 : ((Ideal.absNorm v.asIdeal ^ n : ℕ) : H.Kv v) = ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K)`.

Express the relevant statement in the definitionally equal form `_ = algebraMap K (v.adicCompletion K) _`. Simplify using the standard rewrite rules. Rewrite using `[h2]`. Conclude with `h3`.
-/
private theorem exists_nat {K : Type} [Field K] [NumberField K] (v : H.P K) (n : ℕ) :
    ∃ m : ℕ, 0 < m ∧ Valued.v (m : H.Kv v) ≤ WithZero.exp (-(n : ℤ)) := by
  have h0 : Ideal.absNorm v.asIdeal ≠ 0 := by
    rw [Ne, Ideal.absNorm_eq_zero_iff]
    exact v.ne_bot
  refine ⟨Ideal.absNorm v.asIdeal ^ n, pow_pos (Nat.pos_of_ne_zero h0) n, ?_⟩
  have hm : ((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n ∈ v.asIdeal ^ n :=
    Ideal.pow_mem_pow (Ideal.absNorm_mem _) n
  have h1 := (v.intValuation_le_pow_iff_mem _ n).2 hm
  have h3 : Valued.v ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) ≤
      WithZero.exp (-(n : ℤ)) := by
    rw [HeightOneSpectrum.valuedAdicCompletion_eq_valuation', HeightOneSpectrum.valuation_of_algebraMap]
    exact h1
  have h2 : ((Ideal.absNorm v.asIdeal ^ n : ℕ) : H.Kv v) =
      ((algebraMap (𝓞 K) K (((Ideal.absNorm v.asIdeal : ℕ) : 𝓞 K) ^ n) : K) : v.adicCompletion K) := by
    change _ = algebraMap K (v.adicCompletion K) _
    simp
  rw [h2]
  exact h3

end UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf

open UpperTheory.ConvolutionTheory.RankTwoDescent.ChExPf in
/- English proof (translation)
Introduce `χ`. Use `set S := (GlobalTheory.HCharRam.ram_finite ℚ χ).toFinset with hSdef`. Use `choose n hn using fun v => GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1 v`. Use `choose M hM0 hM using fun v : H.P ℚ => exists_nat v (n v)`. Use `⟨∏ v ∈ S, M v, Finset.prod_pos fun v _ => hM0 v, fun N hN t ht hD => ?_⟩` and prove the remaining obligations.

Establish `key` using `GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 t S (fun v hv => by`. Establish `hu : χ.UnrAt v`. Assume the negation of the conclusion as `hc`. Conclude with `hv ((Set.Finite.mem_toFinset _).2 hc)`. Conclude with `hu _ (ht.2 v))`.

Establish `hinf : infPart ℚ t = 1` using `Units.ext ht.1`. Rewrite using `[key, hinf, map_one, map_one, one_mul]`. Use `Finset.prod_eq_one fun v hv => hn v _ ?_` and prove the remaining obligations. Establish `h1 : Valued.v (H.cp v ((t : A ℚ) - 1)) ≤ Valued.v (N : H.Kv v)` using `(hD v)`. Rewrite `h1` using `[map_sub, map_one]`.

Conclude with `h1.trans ((dvd_le v ((Finset.dvd_prod_of_mem M hv).trans hN)).trans (hM v))`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.chEx_of :
    ChEx := by
  intro χ
  classical
  set S := (GlobalTheory.HCharRam.ram_finite ℚ χ).toFinset with hSdef
  choose n hn using fun v => GlobalTheory.HeckeSplit.exists_level χ.1 χ.2.1 v
  choose M hM0 hM using fun v : H.P ℚ => exists_nat v (n v)
  refine ⟨∏ v ∈ S, M v, Finset.prod_pos fun v _ => hM0 v, fun N hN t ht hD => ?_⟩
  have key := GlobalTheory.HeckeSplit.char_eq_prod_local χ.1 χ.2.1 t S (fun v hv => by
    have hu : χ.UnrAt v := by
      by_contra hc
      exact hv ((Set.Finite.mem_toFinset _).2 hc)
    exact hu _ (ht.2 v))
  have hinf : infPart ℚ t = 1 := Units.ext ht.1
  rw [key, hinf, map_one, map_one, one_mul]
  refine Finset.prod_eq_one fun v hv => hn v _ ?_
  have h1 : Valued.v (H.cp v ((t : A ℚ) - 1)) ≤ Valued.v (N : H.Kv v) := (hD v)
  rw [map_sub, map_one] at h1
  exact h1.trans ((dvd_le v ((Finset.dvd_prod_of_mem M hv).trans hN)).trans (hM v))
