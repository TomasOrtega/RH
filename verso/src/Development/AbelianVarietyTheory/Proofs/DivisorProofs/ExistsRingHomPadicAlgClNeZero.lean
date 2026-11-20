import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsPrimeNotMemForallGtEqMaximalIdealStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsInjectiveNormLeOneOfFinitePadicIntDomainStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsFinitePadicIntDomainEmbeddingStatement

open IsLocalRing

namespace GlobalTheory.CurvePoint

/- English proof (translation)
Introduce `B _ _ _ _ _ hfin h hh`. Use `set p := ringChar (ResidueField B) with hpdef`. Establish `hp0 : p ≠ 0`. Introduce `h0`. Use `haveI : CharP (ResidueField B) 0 := by rw [← h0]; exact ringChar.charP _`.

Use `haveI : CharZero (ResidueField B) := CharP.charP_to_charZero _`. Conclude with `not_finite (ResidueField B)`. Establish `hp : p.Prime` using `(CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right hp0`. Use `haveI hF : Fact p.Prime := ⟨hp⟩`. Establish `hpm : (p : B) ∈ maximalIdeal B`.

Rewrite using `[← residue_eq_zero_iff, map_natCast]`. Conclude with `ringChar.Nat.cast_ringChar`. Establish `hpB : (p : B) ≠ 0` using `Nat.cast_ne_zero.2 hp0`. Take `⟨q, hq, hxq, hmax⟩` from `GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' B (h * p) (mul_ne_zero hh hpB) (Ideal.mul_mem_left _ _ hpm)`. Establish `hhq : h ∉ q` using `fun hq' => hxq (Ideal.mul_mem_right _ _ hq')`.

Establish `hpq : (p : B) ∉ q` using `fun hq' => hxq (Ideal.mul_mem_left _ _ hq')`. Establish `hqm : q ≤ maximalIdeal B` using `le_maximalIdeal hq.ne_top`. Use `set C := B ⧸ q`. Use `haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.2 hq.ne_top`. Use `haveI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective`.

Set `π : B →+* C` to `Ideal.Quotient.mk q`. Establish `hπm : ∀ b ∈ maximalIdeal B, π b ∈ maximalIdeal C`. Introduce `b hb hu`. Take `⟨c, hc⟩` from `hu.exists_right_inv`. Take `⟨c', rfl⟩` from `Ideal.Quotient.mk_surjective c`.

Establish `h1 : b * c' - 1 ∈ q` using `Ideal.Quotient.eq.1 (by simpa [π] using hc)`. Establish `h2 : b * c' - 1 ∈ maximalIdeal B` using `hqm h1`. Establish `h3 : b * c' ∈ maximalIdeal B` using `Ideal.mul_mem_right _ _ hb`. Conclude with `(maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ h3 h2))`. Establish `hmC : ∀ c ∈ maximalIdeal C, ∃ b ∈ maximalIdeal B, π b = c`.

Introduce `c hc`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Use `⟨b, fun hb => hc ?_, rfl⟩` and prove the remaining obligations. Conclude with `hb.map π`. Establish `hfinC : Finite (ResidueField C)`.

Set `f : ResidueField B → ResidueField C` to `Ideal.Quotient.lift (maximalIdeal B) ((residue C).comp π) (fun b hb => by`. Rewrite using `[RingHom.comp_apply, residue_eq_zero_iff]`. Conclude with `hπm b hb)`. Use `Finite.of_surjective f ?_` and prove the remaining obligations. Introduce `y`.

Take `⟨c, rfl⟩` from `residue_surjective y`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Conclude with `⟨residue B b, rfl⟩`. Establish `hpC : (p : C) ≠ 0`. Rewrite using `[← map_natCast π, Ne, Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hpq`. Establish `hpmC : (p : C) ∈ maximalIdeal C` using `by rw [← map_natCast π]; exact hπm _ hpm`. Establish `hdim : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C`. Introduce `P hP hP0`. Use `le_antisymm (le_maximalIdeal hP.ne_top) ?_` and prove the remaining obligations.

Establish `hlt : q < P.comap π`. Use `lt_of_le_of_ne (fun b hb => ?_) (fun he => hP0 ?_)` and prove the remaining obligations. Use `show π b ∈ P`. Rewrite using `[Ideal.Quotient.eq_zero_iff_mem.2 hb]`. Conclude with `P.zero_mem`.

Rewrite using `[eq_bot_iff]`. Introduce `c hc`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective c`. Establish `: b ∈ q` using `he ▸ hc`. Conclude with `(Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 this)`.

Establish `hc` using `hmax _ (Ideal.comap_isPrime π P) hlt`. Introduce `c hc'`. Take `⟨b, hb, rfl⟩` from `hmC c hc'`. Establish `: b ∈ P.comap π` using `hc ▸ hb`. Conclude with `this`.

Choose the witnesses or unpack the hypotheses as in `⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by`. Use `Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)` and prove the remaining obligations. Rewrite using `[Ideal.radical_eq_sInf]`. Use `le_sInf fun P ⟨hle, hP⟩ => ?_` and prove the remaining obligations. Establish `hP0 : P ≠ ⊥` using `fun h0 => hpC (by rw [h0] at hle; exact (Submodule.mem_bot _).1 (hle (Ideal.mem_span_singleton_self _)))`.

Conclude with `(hdim P hP hP0).ge`. Take `⟨D, _, _, _, hDfin, ι, hι⟩` from `GlobalTheory.T.exists_finite_padicInt_domain_embedding p C hfinC hpC hpmC hdim`. Establish `hpD : (p : D) ≠ 0`. Rewrite using `[← map_natCast ι]; exact fun h0 => hpC (hι (by rw [h0, map_zero]))`. Take `⟨φ, hφ, hφ1⟩` from `GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain p D hpD`.

Use `⟨p, hF, (φ.comp ι).comp π, fun b => hφ1 _, fun b hb => ?_, ?_⟩` and prove the remaining obligations. Establish `hc` using `hπm b hb`. Establish `hcN : π b ^ N ∈ Ideal.span {(p : C)}` using `hN (Ideal.pow_mem_pow hc N)`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 hcN`. Establish `key : ‖(φ.comp ι) (π b)‖ ^ N < 1 ^ N`.

Rewrite using `[← norm_pow, ← map_pow, ← hd, map_mul, norm_mul, one_pow, map_natCast]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[one_mul]`. Establish `e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p)` using `by simp`. Rewrite using `[← e, norm_algebraMap']`.

Conclude with `Padic.norm_p_lt_one`. Conclude with `lt_of_pow_lt_pow_left₀ N zero_le_one key`. Introduce `h0`. Apply `hhq` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem]`.

Conclude with `hι (hφ (by simpa using h0))`.
-/
theorem exists_ringHom_padicAlgCl_ne_zero : ∀ (B : Type) [CommRing B] [IsDomain B] [IsLocalRing B] [IsNoetherianRing B] [CharZero B], Finite (ResidueField B) → ∀ h : B, h ≠ 0 → ∃ (p : ℕ) (_ : Fact p.Prime) (χ : B →+* PadicAlgCl p), (∀ b, ‖χ b‖ ≤ 1) ∧ (∀ b ∈ maximalIdeal B, ‖χ b‖ < 1) ∧ χ h ≠ 0 := by
  intro B _ _ _ _ _ hfin h hh

  set p := ringChar (ResidueField B) with hpdef
  have hp0 : p ≠ 0 := by
    intro h0
    haveI : CharP (ResidueField B) 0 := by rw [← h0]; exact ringChar.charP _
    haveI : CharZero (ResidueField B) := CharP.charP_to_charZero _
    exact not_finite (ResidueField B)
  have hp : p.Prime := (CharP.char_is_prime_or_zero (ResidueField B) p).resolve_right hp0
  haveI hF : Fact p.Prime := ⟨hp⟩
  have hpm : (p : B) ∈ maximalIdeal B := by
    rw [← residue_eq_zero_iff, map_natCast]
    exact ringChar.Nat.cast_ringChar
  have hpB : (p : B) ≠ 0 := Nat.cast_ne_zero.2 hp0

  obtain ⟨q, hq, hxq, hmax⟩ := GlobalTheory.T.exists_prime_not_mem_forall_gt_eq_maximalIdeal' B (h * p) (mul_ne_zero hh hpB) (Ideal.mul_mem_left _ _ hpm)
  have hhq : h ∉ q := fun hq' => hxq (Ideal.mul_mem_right _ _ hq')
  have hpq : (p : B) ∉ q := fun hq' => hxq (Ideal.mul_mem_left _ _ hq')
  have hqm : q ≤ maximalIdeal B := le_maximalIdeal hq.ne_top
  set C := B ⧸ q
  haveI : Nontrivial C := Ideal.Quotient.nontrivial_iff.2 hq.ne_top
  haveI : IsLocalRing C := IsLocalRing.of_surjective' (Ideal.Quotient.mk q) Ideal.Quotient.mk_surjective
  let π : B →+* C := Ideal.Quotient.mk q
  have hπm : ∀ b ∈ maximalIdeal B, π b ∈ maximalIdeal C := by
    intro b hb hu
    obtain ⟨c, hc⟩ := hu.exists_right_inv
    obtain ⟨c', rfl⟩ := Ideal.Quotient.mk_surjective c
    have h1 : b * c' - 1 ∈ q := Ideal.Quotient.eq.1 (by simpa [π] using hc)
    have h2 : b * c' - 1 ∈ maximalIdeal B := hqm h1
    have h3 : b * c' ∈ maximalIdeal B := Ideal.mul_mem_right _ _ hb
    exact (maximalIdeal.isMaximal B).ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using Ideal.sub_mem _ h3 h2))
  have hmC : ∀ c ∈ maximalIdeal C, ∃ b ∈ maximalIdeal B, π b = c := by
    intro c hc
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    refine ⟨b, fun hb => hc ?_, rfl⟩
    exact hb.map π
  have hfinC : Finite (ResidueField C) := by
    let f : ResidueField B → ResidueField C :=
      Ideal.Quotient.lift (maximalIdeal B) ((residue C).comp π) (fun b hb => by
        rw [RingHom.comp_apply, residue_eq_zero_iff]; exact hπm b hb)
    refine Finite.of_surjective f ?_
    intro y
    obtain ⟨c, rfl⟩ := residue_surjective y
    obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
    exact ⟨residue B b, rfl⟩
  have hpC : (p : C) ≠ 0 := by
    rw [← map_natCast π, Ne, Ideal.Quotient.eq_zero_iff_mem]; exact hpq
  have hpmC : (p : C) ∈ maximalIdeal C := by rw [← map_natCast π]; exact hπm _ hpm
  have hdim : ∀ P : Ideal C, P.IsPrime → P ≠ ⊥ → P = maximalIdeal C := by
    intro P hP hP0
    refine le_antisymm (le_maximalIdeal hP.ne_top) ?_
    have hlt : q < P.comap π := by
      refine lt_of_le_of_ne (fun b hb => ?_) (fun he => hP0 ?_)
      · show π b ∈ P; rw [Ideal.Quotient.eq_zero_iff_mem.2 hb]; exact P.zero_mem
      · rw [eq_bot_iff]; intro c hc
        obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective c
        have : b ∈ q := he ▸ hc
        exact (Submodule.mem_bot _).2 (Ideal.Quotient.eq_zero_iff_mem.2 this)
    have hc := hmax _ (Ideal.comap_isPrime π P) hlt
    intro c hc'
    obtain ⟨b, hb, rfl⟩ := hmC c hc'
    have : b ∈ P.comap π := hc ▸ hb
    exact this

  obtain ⟨N, hN⟩ : ∃ N : ℕ, maximalIdeal C ^ N ≤ Ideal.span {(p : C)} := by
    refine Ideal.exists_pow_le_of_le_radical_of_fg ?_ (IsNoetherian.noetherian _)
    rw [Ideal.radical_eq_sInf]
    refine le_sInf fun P ⟨hle, hP⟩ => ?_
    have hP0 : P ≠ ⊥ := fun h0 => hpC (by rw [h0] at hle; exact (Submodule.mem_bot _).1 (hle (Ideal.mem_span_singleton_self _)))
    exact (hdim P hP hP0).ge
  obtain ⟨D, _, _, _, hDfin, ι, hι⟩ := GlobalTheory.T.exists_finite_padicInt_domain_embedding p C hfinC hpC hpmC hdim
  have hpD : (p : D) ≠ 0 := by
    rw [← map_natCast ι]; exact fun h0 => hpC (hι (by rw [h0, map_zero]))
  obtain ⟨φ, hφ, hφ1⟩ := GlobalTheory.T.exists_injective_norm_le_one_of_finite_padicInt_domain p D hpD
  refine ⟨p, hF, (φ.comp ι).comp π, fun b => hφ1 _, fun b hb => ?_, ?_⟩
  · have hc := hπm b hb
    have hcN : π b ^ N ∈ Ideal.span {(p : C)} := hN (Ideal.pow_mem_pow hc N)
    obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 hcN
    have key : ‖(φ.comp ι) (π b)‖ ^ N < 1 ^ N := by
      rw [← norm_pow, ← map_pow, ← hd, map_mul, norm_mul, one_pow, map_natCast]
      calc ‖(φ.comp ι) d‖ * ‖(p : PadicAlgCl p)‖ ≤ 1 * ‖(p : PadicAlgCl p)‖ :=
            mul_le_mul_of_nonneg_right (hφ1 _) (norm_nonneg _)
        _ < 1 := by
          rw [one_mul]
          have e : ((p : ℚ_[p]) : PadicAlgCl p) = (p : PadicAlgCl p) := by simp
          rw [← e, norm_algebraMap']; exact Padic.norm_p_lt_one
    exact lt_of_pow_lt_pow_left₀ N zero_le_one key
  · intro h0
    apply hhq
    rw [← Ideal.Quotient.eq_zero_iff_mem]
    exact hι (hφ (by simpa using h0))

end GlobalTheory.CurvePoint
