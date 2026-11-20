import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardKerEqCoker
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInj
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.KerFDelNm
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.PCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.EqHomLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.DatEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CountOrdP
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.TorsionExponentBound
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.ActUPow
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelLCard
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.CardEQ
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.ClassCounting.SelmerOrderCounts.SelInvLe

open NumberField IsDedekindDomain UpperTheory.V UpperTheory.V.KL UpperTheory.V.ZK

/- English proof (translation)
Introduce `L F _ _ _ _ _ hTC l c ν E b B _ ζ γ hL hE hF`. Establish `hl : l.Prime` using `Fact.out`. Take `⟨ha2, hfa, hfN⟩` from `Ct.lte l c ν E hl hL.c_pos hL.c_two hL.c_le hE`. Generalize the expression as in `(1 + l ^ c) ^ E = a at *`. Take `⟨D, hD⟩` from `Ct.datEx L F γ a ha2`.

Establish `hDa` using `hD.a_eq`. Establish `hDn` using `hD.n_eq`. Establish `hI` using `Ct.clFin L F γ a D hD`. Take `⟨hEQf, hEQc⟩` from `Ct.cardEQ L F γ a D hTC hL.gal hL.gen hD`. Take `⟨hClf, hWf, hWc⟩` from `Ct.cardW _ _ D hI hEQf`.

Take `⟨hEHf, hEHc⟩` from `Ct.eqHomLe L F γ a l ν D hl hD hClf`. Use `⟨hEHf, ?_⟩` and prove the remaining obligations. Establish `hlpow : l ^ (ν - c) ≠ 0` using `(pow_pos hl.pos _).ne'`. Establish `hbig : 2 ≤ a ^ l ^ (ν - c)` using `le_trans ha2 (Nat.le_self_pow hlpow a)`. Establish `hN0 : a ^ l ^ (ν - c) - 1 ≠ 0` using `by omega`.

Take `⟨m, hm⟩ : ∃ m, m = ordCompl[l] (a ^ l ^ (ν - c) - 1)` from `⟨_, rfl⟩`. Establish `hNm : a ^ l ^ (ν - c) - 1 = l ^ (ν + E.factorization l) * m`. Establish `h0` using `Nat.ordProj_mul_ordCompl_eq_self (a ^ l ^ (ν - c) - 1) l`. Rewrite `h0` using `[← hm, hfN]`. Conclude with `h0.symm`.

Establish `hmd : ¬ l ∣ m`. Rewrite using `[hm]`. Conclude with `Nat.not_dvd_ordCompl hl hN0`. Establish `hker : ((D.a : ℤ)) ^ D.n - 1 = ((l ^ ν : ℕ) : ℤ) * ((l ^ E.factorization l * m : ℕ) : ℤ)`. Rewrite using `[hDa, hDn, hL.ord]`.

Establish `h1 : 1 ≤ a ^ l ^ (ν - c)` using `by omega`. Establish `key : ((a ^ l ^ (ν - c) - 1 : ℕ) : ℤ) = (a : ℤ) ^ l ^ (ν - c) - 1`. Rewrite using `[Nat.cast_sub h1]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[← key, hNm]`. Use `push_cast`. Expand and normalize the polynomial expressions, which then agree. Take `⟨f, hfnm, hfk⟩` from `Ct.kerF _ _ D (l ^ ν) (l ^ b) _ hker`. Use `haveI := hWf`.

Use `haveI := hEQf`. Use `haveI := hClf`. Establish `hrange` using `Ct.fewLe L F γ a (l ^ b) (l ^ ν) B D hD hF f hfnm hWf`. Take `⟨hSLf, hSLc⟩` from `Ct.selLCard L l hl`. Take `⟨hSIf, hSIc⟩` from `Ct.selInvLe L F l c ν a ζ γ D hl hL hD hSLf`.

Establish `hdvd : (l : ℤ) ∣ (D.a : ℤ) - 1`. Rewrite using `[hDa]`. Establish `hc1` using `hL.c_pos`. Establish `hd : l ∣ a - 1` using `Nat.dvd_of_factorization_pos (by rw [hfa]; omega)`. Establish `h1 : 1 ≤ a` using `by omega`.

Establish `hd'` using `Int.natCast_dvd_natCast.mpr hd`. Rewrite `hd'` using `[Nat.cast_sub h1]`. Simplify using `using hd'`. Establish `htor` using `Ct.selInj _ _ D l hdvd hl.pos hSIf`. Establish `hg : Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ l ^ gens L`.

Use `htor.trans (hSIc.trans ((Nat.mul_le_mul_right _ hSLc).trans (le_of_eq ?_)))` and prove the remaining obligations. Unfold `gens`. Rewrite using `[← pow_add]`. Establish `hp` using `Ct.pCount D.W _ f l (b + E.factorization l) (gens L) (m : ℤ) hl (by exact_mod_cast hmd) (by`. Introduce `w hw`.

Establish `h0` using `hfk w hw`. Use `h0 using 2` and compare the differences between its conclusion and the goal. Use `push_cast`. Use the proof step `ring) hg`. Establish `hEQ0 : Nat.card D.EQ ≠ 0` using `Nat.card_pos.ne'`.

Establish `hCl0 : Nat.card D.ClQ ≠ 0` using `Nat.card_pos.ne'`. Establish `hfW : (Nat.card D.W).factorization l = (Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l`. Rewrite using `[hWc, Nat.factorization_mul hEQ0 hCl0, Finsupp.add_apply]`. Establish `hfEQ : (Nat.card D.EQ).factorization l + (c + E.factorization l) = InfinitePlace.nrComplexPlaces L * (ν + E.factorization l)`. Establish `h0` using `congrArg (fun n => n.factorization l) hEQc`.

Establish `ha1 : a - 1 ≠ 0` using `by omega`. Rewrite `h0` using `[Nat.factorization_mul hEQ0 ha1, Finsupp.add_apply, hfa, hL.ord, Nat.factorization_pow, Finsupp.smul_apply, smul_eq_mul, hfN]`. Conclude with `h0`. Combine the equalities or inequalities in the displayed calculation. Use `Nat.mul_le_mul hEHc ?_` and prove the remaining obligations.

Rewrite using `[← pow_mul]`. Use `Nat.pow_le_pow_right hl.pos ?_` and prove the remaining obligations. Rewrite using `[hfEQ, mul_comm]`. Conclude with `Nat.mul_le_mul_left _ (Nat.le_add_right _ _)`. Use `_ = l ^ ((Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l) * l ^ (c + E.factorization l) := by`.

Rewrite using `[← pow_add, ← pow_add]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree. Use `_ ≤ (Nat.card ↥f.range * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := by`. Use `Nat.mul_le_mul_right _ ?_` and prove the remaining obligations.

Rewrite using `[← hfW]`. Conclude with `hp`. Use `_ ≤ (B * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrange)`. Use `_ = B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l) := by`. Rewrite using `[mul_assoc, ← pow_add, add_assoc]`.
-/
theorem UpperTheory.V.ZK.sCount :
    UpperTheory.V.ZK.SCount := by
  intro L F _ _ _ _ _ hTC l c ν E b B _ ζ γ hL hE hF
  have hl : l.Prime := Fact.out
  obtain ⟨ha2, hfa, hfN⟩ := Ct.lte l c ν E hl hL.c_pos hL.c_two hL.c_le hE
  generalize (1 + l ^ c) ^ E = a at *
  obtain ⟨D, hD⟩ := Ct.datEx L F γ a ha2
  have hDa := hD.a_eq
  have hDn := hD.n_eq
  have hI := Ct.clFin L F γ a D hD
  obtain ⟨hEQf, hEQc⟩ := Ct.cardEQ L F γ a D hTC hL.gal hL.gen hD
  obtain ⟨hClf, hWf, hWc⟩ := Ct.cardW _ _ D hI hEQf
  obtain ⟨hEHf, hEHc⟩ := Ct.eqHomLe L F γ a l ν D hl hD hClf
  refine ⟨hEHf, ?_⟩
  have hlpow : l ^ (ν - c) ≠ 0 := (pow_pos hl.pos _).ne'
  have hbig : 2 ≤ a ^ l ^ (ν - c) := le_trans ha2 (Nat.le_self_pow hlpow a)
  have hN0 : a ^ l ^ (ν - c) - 1 ≠ 0 := by omega
  obtain ⟨m, hm⟩ : ∃ m, m = ordCompl[l] (a ^ l ^ (ν - c) - 1) := ⟨_, rfl⟩
  have hNm : a ^ l ^ (ν - c) - 1 = l ^ (ν + E.factorization l) * m := by
    have h0 := Nat.ordProj_mul_ordCompl_eq_self (a ^ l ^ (ν - c) - 1) l
    rw [← hm, hfN] at h0
    exact h0.symm
  have hmd : ¬ l ∣ m := by
    rw [hm]
    exact Nat.not_dvd_ordCompl hl hN0
  have hker : ((D.a : ℤ)) ^ D.n - 1 = ((l ^ ν : ℕ) : ℤ) * ((l ^ E.factorization l * m : ℕ) : ℤ) := by
    rw [hDa, hDn, hL.ord]
    have h1 : 1 ≤ a ^ l ^ (ν - c) := by omega
    have key : ((a ^ l ^ (ν - c) - 1 : ℕ) : ℤ) = (a : ℤ) ^ l ^ (ν - c) - 1 := by
      rw [Nat.cast_sub h1]
      push_cast
      ring
    rw [← key, hNm]
    push_cast
    ring
  obtain ⟨f, hfnm, hfk⟩ := Ct.kerF _ _ D (l ^ ν) (l ^ b) _ hker
  haveI := hWf
  haveI := hEQf
  haveI := hClf
  have hrange := Ct.fewLe L F γ a (l ^ b) (l ^ ν) B D hD hF f hfnm hWf
  obtain ⟨hSLf, hSLc⟩ := Ct.selLCard L l hl
  obtain ⟨hSIf, hSIc⟩ := Ct.selInvLe L F l c ν a ζ γ D hl hL hD hSLf
  have hdvd : (l : ℤ) ∣ (D.a : ℤ) - 1 := by
    rw [hDa]
    have hc1 := hL.c_pos
    have hd : l ∣ a - 1 := Nat.dvd_of_factorization_pos (by rw [hfa]; omega)
    have h1 : 1 ≤ a := by omega
    have hd' := Int.natCast_dvd_natCast.mpr hd
    rw [Nat.cast_sub h1] at hd'
    simpa using hd'
  have htor := Ct.selInj _ _ D l hdvd hl.pos hSIf
  have hg : Nat.card {w : D.W // (l : ℤ) • w = 0} ≤ l ^ gens L := by
    refine htor.trans (hSIc.trans ((Nat.mul_le_mul_right _ hSLc).trans (le_of_eq ?_)))
    unfold gens
    rw [← pow_add]
  have hp := Ct.pCount D.W _ f l (b + E.factorization l) (gens L) (m : ℤ) hl
    (by exact_mod_cast hmd)
    (by
      intro w hw
      have h0 := hfk w hw
      convert h0 using 2
      push_cast
      ring) hg
  have hEQ0 : Nat.card D.EQ ≠ 0 := Nat.card_pos.ne'
  have hCl0 : Nat.card D.ClQ ≠ 0 := Nat.card_pos.ne'
  have hfW : (Nat.card D.W).factorization l =
      (Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l := by
    rw [hWc, Nat.factorization_mul hEQ0 hCl0, Finsupp.add_apply]
  have hfEQ : (Nat.card D.EQ).factorization l + (c + E.factorization l) =
      InfinitePlace.nrComplexPlaces L * (ν + E.factorization l) := by
    have h0 := congrArg (fun n => n.factorization l) hEQc
    have ha1 : a - 1 ≠ 0 := by omega
    rw [Nat.factorization_mul hEQ0 ha1, Finsupp.add_apply, hfa, hL.ord, Nat.factorization_pow,
      Finsupp.smul_apply, smul_eq_mul, hfN] at h0
    exact h0
  calc Nat.card ↑(EqHom γ a (l ^ ν)) * (l ^ ν) ^ InfinitePlace.nrComplexPlaces L
      ≤ l ^ (Nat.card D.ClQ).factorization l *
          l ^ ((Nat.card D.EQ).factorization l + (c + E.factorization l)) := by
        refine Nat.mul_le_mul hEHc ?_
        rw [← pow_mul]
        refine Nat.pow_le_pow_right hl.pos ?_
        rw [hfEQ, mul_comm]
        exact Nat.mul_le_mul_left _ (Nat.le_add_right _ _)
    _ = l ^ ((Nat.card D.EQ).factorization l + (Nat.card D.ClQ).factorization l) *
          l ^ (c + E.factorization l) := by
        rw [← pow_add, ← pow_add]
        congr 1
        ring
    _ ≤ (Nat.card ↥f.range * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) := by
        refine Nat.mul_le_mul_right _ ?_
        rw [← hfW]
        exact hp
    _ ≤ (B * l ^ ((b + E.factorization l) * gens L)) * l ^ (c + E.factorization l) :=
        Nat.mul_le_mul_right _ (Nat.mul_le_mul_right _ hrange)
    _ = B * l ^ ((b + E.factorization l) * gens L + c + E.factorization l) := by
        rw [mul_assoc, ← pow_add, add_assoc]
