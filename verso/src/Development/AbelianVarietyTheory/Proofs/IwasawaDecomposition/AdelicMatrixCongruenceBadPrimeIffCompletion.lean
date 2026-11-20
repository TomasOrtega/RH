import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.LiftsInvOne
open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC GlobalTheory.Mem.Col2.AdT Matrix
attribute [local instance] GlobalTheory.Mem.Col2.starE Formalism.BasicNotions.Host.cmStar

noncomputable section
namespace GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary

/- English proof (translation)
The claim follows from `HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x`.
-/
theorem vAlg {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (x : E) :
    Valued.v (algebraMap E (P.adicCompletion E) x) = P.valuation E x :=
  HeightOneSpectrum.valuedAdicCompletion_eq_valuation' P x

/- English proof (translation)
Establish `e : ((qOf P : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E))`. Simplify using the standard rewrite rules. Rewrite using `[e, vAlg, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `hmem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 1`. Rewrite using `[pow_one]`.

Conclude with `Ideal.absNorm_mem P.asIdeal`. Establish `h1` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 1).2 hmem`. Establish `h2' : ¬ P.intValuation ((qOf P : ℕ) : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ))` using `fun h => h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 2).1 h)`. Establish `hne : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0`. Establish `: ((qOf P : ℕ) : 𝓞 E) ≠ 0` using `Nat.cast_ne_zero.2 hp.ne_zero`.

Conclude with `(HeightOneSpectrum.intValuation_ne_zero P _ this)`. Rewrite `h1`, `h2'`, the goal using `[← WithZero.exp_log hne]`. Rewrite `h1`, `h2'` using `[WithZero.exp_le_exp]`. Use `congr 1`. Move the coercions through the operations in `at h1 h2'`.

Use linear arithmetic over natural numbers and integers.
-/
theorem v_qOf {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (hp : (qOf P).Prime)
    (h2 : ((qOf P : ℕ) : 𝓞 E) ∉ P.asIdeal ^ 2) :
    Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ) := by
  have e : ((qOf P : ℕ) : P.adicCompletion E) = algebraMap E (P.adicCompletion E) (algebraMap (𝓞 E) E ((qOf P : ℕ) : 𝓞 E)) := by
    simp
  rw [e, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  have hmem : ((qOf P : ℕ) : 𝓞 E) ∈ P.asIdeal ^ 1 := by
    rw [pow_one]
    exact Ideal.absNorm_mem P.asIdeal
  have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 1).2 hmem
  have h2' : ¬ P.intValuation ((qOf P : ℕ) : 𝓞 E) ≤ WithZero.exp (-((2 : ℕ) : ℤ)) := fun h =>
    h2 ((HeightOneSpectrum.intValuation_le_pow_iff_mem P _ 2).1 h)
  have hne : P.intValuation ((qOf P : ℕ) : 𝓞 E) ≠ 0 := by
    have : ((qOf P : ℕ) : 𝓞 E) ≠ 0 := Nat.cast_ne_zero.2 hp.ne_zero
    exact (HeightOneSpectrum.intValuation_ne_zero P _ this)
  rw [← WithZero.exp_log hne] at h1 h2' ⊢
  rw [WithZero.exp_le_exp] at h1 h2'
  congr 1
  push_cast at h1 h2'
  omega

/- English proof (translation)
Establish `hfin : {Q : HeightOneSpectrum (𝓞 E) | ¬ y Q ∈ Q.adicCompletionIntegers E}.Finite` using `Filter.eventually_cofinite.1 y.2`. Use `set S := hfin.toFinset with hS`. Establish `memS : ∀ Q, Q ∈ S ↔ 1 < Valued.v (y Q)`. Introduce `Q`. Rewrite using `[hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]`.

Establish `hPS : P ∉ S` using `fun h => absurd hP (not_le.2 ((memS P).1 h))`. Set `m : HeightOneSpectrum (𝓞 E) → ℕ` to `fun Q => (WithZero.log (Valued.v (y Q))).toNat`. Set `J : Ideal (𝓞 E)` to `∏ Q ∈ S, Q.asIdeal ^ m Q`. Establish `hJ : ¬ J ≤ P.asIdeal`. Introduce `h`.

Take `⟨Q, hQ, hle⟩` from `(Ideal.IsPrime.prod_le P.isPrime).1 h`. Establish `h1 : Q.asIdeal ≤ P.asIdeal`. Distinguish the cases in `hm : m Q = 0`. It suffices to derive a contradiction. Establish `h3` using `(memS Q).1 hQ`.

Establish `hne : Valued.v (y Q) ≠ 0` using `ne_of_gt (lt_trans zero_lt_one h3)`. Rewrite `h3` using `[← WithZero.exp_log hne]`. Establish `h4 : (0 : ℤ) < WithZero.log (Valued.v (y Q))`. Rewrite `h3` using `[← WithZero.exp_zero, WithZero.exp_lt_exp]`. Conclude with `h3`.

Establish `: m Q ≠ 0` using `by show (WithZero.log (Valued.v (y Q))).toNat ≠ 0`. Use linear arithmetic over natural numbers and integers. Conclude with `this hm`. Conclude with `P.isPrime.le_of_pow_le hle`. Establish `h2 : Q = P` using `HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)`.

Conclude with `hPS (h2 ▸ hQ)`. Take `⟨s, hsJ, hsP⟩` from `SetLike.not_le_iff_exists.1 hJ`. Use `⟨s, hsP, fun Q => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, vAlg, HeightOneSpectrum.valuation_of_algebraMap]`. Distinguish the cases in `hQ : Q ∈ S`.

Establish `hsQ : s ∈ Q.asIdeal ^ m Q` using `(Finset.inf_le (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal ^ m Q) hQ) (Ideal.prod_le_inf hsJ)`. Establish `h1` using `(HeightOneSpectrum.intValuation_le_pow_iff_mem Q s (m Q)).2 hsQ`. Establish `hne : Valued.v (y Q) ≠ 0` using `ne_of_gt (lt_trans zero_lt_one ((memS Q).1 hQ))`. Establish `h2 : Valued.v (y Q) ≤ WithZero.exp ((m Q : ℕ) : ℤ)`. Rewrite using `[← WithZero.exp_log hne, WithZero.exp_le_exp]`.

Use `show WithZero.log (Valued.v (y Q)) ≤ ((WithZero.log (Valued.v (y Q))).toNat : ℤ)`. Use linear arithmetic over natural numbers and integers. Combine the equalities or inequalities in the displayed calculation. Establish `h1 : Valued.v (y Q) ≤ 1` using `not_lt.1 fun h => hQ ((memS Q).2 h)`. Conclude with `mul_le_one' (HeightOneSpectrum.intValuation_le_one Q s) h1`.
-/
theorem exists_clear {E : Type} [Field E] [NumberField E] (P : HeightOneSpectrum (𝓞 E)) (y : FiniteAdeleRing (𝓞 E) E)
    (hP : Valued.v (y P) ≤ 1) : ∃ s : 𝓞 E, s ∉ P.asIdeal ∧
      ∀ Q : HeightOneSpectrum (𝓞 E), Valued.v (algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * y Q) ≤ 1 := by
  have hfin : {Q : HeightOneSpectrum (𝓞 E) | ¬ y Q ∈ Q.adicCompletionIntegers E}.Finite :=
    Filter.eventually_cofinite.1 y.2
  set S := hfin.toFinset with hS
  have memS : ∀ Q, Q ∈ S ↔ 1 < Valued.v (y Q) := by
    intro Q
    rw [hS, Set.Finite.mem_toFinset, Set.mem_setOf_eq, HeightOneSpectrum.mem_adicCompletionIntegers, not_le]
  have hPS : P ∉ S := fun h => absurd hP (not_le.2 ((memS P).1 h))
  let m : HeightOneSpectrum (𝓞 E) → ℕ := fun Q => (WithZero.log (Valued.v (y Q))).toNat
  let J : Ideal (𝓞 E) := ∏ Q ∈ S, Q.asIdeal ^ m Q
  have hJ : ¬ J ≤ P.asIdeal := by
    intro h
    obtain ⟨Q, hQ, hle⟩ := (Ideal.IsPrime.prod_le P.isPrime).1 h
    have h1 : Q.asIdeal ≤ P.asIdeal := by
      by_cases hm : m Q = 0
      · exfalso
        have h3 := (memS Q).1 hQ
        have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one h3)
        rw [← WithZero.exp_log hne] at h3
        have h4 : (0 : ℤ) < WithZero.log (Valued.v (y Q)) := by
          rw [← WithZero.exp_zero, WithZero.exp_lt_exp] at h3
          exact h3
        have : m Q ≠ 0 := by
          show (WithZero.log (Valued.v (y Q))).toNat ≠ 0
          omega
        exact this hm
      · exact P.isPrime.le_of_pow_le hle
    have h2 : Q = P := HeightOneSpectrum.ext (Q.isMaximal.eq_of_le P.isPrime.ne_top h1)
    exact hPS (h2 ▸ hQ)
  obtain ⟨s, hsJ, hsP⟩ := SetLike.not_le_iff_exists.1 hJ
  refine ⟨s, hsP, fun Q => ?_⟩
  rw [map_mul, vAlg, HeightOneSpectrum.valuation_of_algebraMap]
  by_cases hQ : Q ∈ S
  · have hsQ : s ∈ Q.asIdeal ^ m Q :=
      (Finset.inf_le (f := fun Q : HeightOneSpectrum (𝓞 E) => Q.asIdeal ^ m Q) hQ) (Ideal.prod_le_inf hsJ)
    have h1 := (HeightOneSpectrum.intValuation_le_pow_iff_mem Q s (m Q)).2 hsQ
    have hne : Valued.v (y Q) ≠ 0 := ne_of_gt (lt_trans zero_lt_one ((memS Q).1 hQ))
    have h2 : Valued.v (y Q) ≤ WithZero.exp ((m Q : ℕ) : ℤ) := by
      rw [← WithZero.exp_log hne, WithZero.exp_le_exp]
      show WithZero.log (Valued.v (y Q)) ≤ ((WithZero.log (Valued.v (y Q))).toNat : ℤ)
      omega
    calc Q.intValuation s * Valued.v (y Q) ≤ WithZero.exp (-((m Q : ℕ) : ℤ)) * WithZero.exp ((m Q : ℕ) : ℤ) :=
          mul_le_mul' h1 h2
      _ = 1 := by rw [← WithZero.exp_add]; simp
  · have h1 : Valued.v (y Q) ≤ 1 := not_lt.1 fun h => hQ ((memS Q).2 h)
    exact mul_le_one' (HeightOneSpectrum.intValuation_le_one Q s) h1

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Conclude with `GlobalTheory.TwU.IsAdIso.val_le (ι := afIso F E) ⟨afIso_tmul_one F E, mem_rInt_iff F E⟩ h`. Introduce `h`. Take `⟨s, hs, hall⟩` from `exists_clear P (afIso F E x) h`.

Use `⟨s, hs, ?_⟩` and prove the remaining obligations. Use `show _ ∈ RInt F E`. Rewrite using `[mem_rInt_iff]`. Introduce `Q`. Establish `e : afIso F E (iA F E (algebraMap (𝓞 E) E s) * x) Q = algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * afIso F E x Q`.

Rewrite using `[map_mul]`. Establish `h2 : afIso F E (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s)` using `afIso_tmul_one F E _`. Rewrite using `[h2]`. Both sides reduce to the same expression. Rewrite using `[e]`.

Conclude with `hall Q`.
-/
theorem intAtA_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (x : AfE F E) :
    IntAtA (F := F) P x ↔ Valued.v (adAt F P x) ≤ 1 := by
  constructor
  · intro h
    exact GlobalTheory.TwU.IsAdIso.val_le (ι := afIso F E) ⟨afIso_tmul_one F E, mem_rInt_iff F E⟩ h
  · intro h
    obtain ⟨s, hs, hall⟩ := exists_clear P (afIso F E x) h
    refine ⟨s, hs, ?_⟩
    show _ ∈ RInt F E
    rw [mem_rInt_iff]
    intro Q
    have e : afIso F E (iA F E (algebraMap (𝓞 E) E s) * x) Q =
        algebraMap E (Q.adicCompletion E) (algebraMap (𝓞 E) E s) * afIso F E x Q := by
      rw [map_mul]
      have h2 : afIso F E (iA F E (algebraMap (𝓞 E) E s)) = algebraMap E _ (algebraMap (𝓞 E) E s) :=
        afIso_tmul_one F E _
      rw [h2]
      rfl
    rw [e]
    exact hall Q

/- English proof (translation)
Rewrite using `[intAtA_iff, map_mul, adAt_inclE, Matrix.sub_apply, map_sub]`. Establish `h1 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s`. Distinguish the cases in `h : r = s`. Substitute `h` using the available equality. Rewrite using `[Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]`.

Rewrite using `[Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]`. Rewrite using `[h1, map_mul, map_inv₀, map_pow, map_natCast, map_inv₀, map_pow, hq]`. Establish `hE : (WithZero.exp (-1 : ℤ) ^ N)⁻¹ = WithZero.exp (N : ℤ)`. Rewrite using `[← WithZero.exp_nsmul, ← WithZero.exp_neg]`. Use `congr 1`.

Simplify using the standard rewrite rules. Rewrite using `[hE]`. Generalize the expression as in `Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) = x`. Establish `hm : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1`. Rewrite using `[← WithZero.exp_add]`.

Simplify using the standard rewrite rules. Prove the components needed by the constructor for the conclusion. Introduce `h`. Combine the equalities or inequalities in the displayed calculation. Introduce `h`.

Combine the equalities or inequalities in the displayed calculation.
-/
theorem entry_iff {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (P : HeightOneSpectrum (𝓞 E)) (hq : Valued.v ((qOf P : ℕ) : P.adicCompletion E) = WithZero.exp (-1 : ℤ))
    {n : ℕ} (N : ℕ) (z : GL (Fin n) (AfE F E)) (r s : Fin n) :
    IntAtA (F := F) P (iA F E (((qOf P : ℕ) : E) ^ N)⁻¹ * ((z : Matrix (Fin n) (Fin n) (AfE F E)) - 1) r s) ↔
      Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) ≤ WithZero.exp (-(N : ℤ)) := by
  rw [intAtA_iff, map_mul, adAt_inclE, Matrix.sub_apply, map_sub]
  have h1 : adAt F P ((1 : Matrix (Fin n) (Fin n) (AfE F E)) r s) = (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s := by
    by_cases h : r = s
    · subst h
      rw [Matrix.one_apply_eq, Matrix.one_apply_eq, map_one]
    · rw [Matrix.one_apply_ne h, Matrix.one_apply_ne h, map_zero]
  rw [h1, map_mul, map_inv₀, map_pow, map_natCast, map_inv₀, map_pow, hq]
  have hE : (WithZero.exp (-1 : ℤ) ^ N)⁻¹ = WithZero.exp (N : ℤ) := by
    rw [← WithZero.exp_nsmul, ← WithZero.exp_neg]
    congr 1
    simp
  rw [hE]
  generalize Valued.v (adAt F P (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.adicCompletion E)) r s) = x
  have hm : WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ) = 1 := by
    rw [← WithZero.exp_add]; simp
  constructor
  · intro h
    calc x = (WithZero.exp (-(N : ℤ)) * WithZero.exp (N : ℤ)) * x := by rw [hm, one_mul]
      _ = WithZero.exp (-(N : ℤ)) * (WithZero.exp (N : ℤ) * x) := mul_assoc _ _ _
      _ ≤ WithZero.exp (-(N : ℤ)) * 1 := mul_le_mul' le_rfl h
      _ = WithZero.exp (-(N : ℤ)) := mul_one _
  · intro h
    calc WithZero.exp (N : ℤ) * x ≤ WithZero.exp (N : ℤ) * WithZero.exp (-(N : ℤ)) := mul_le_mul' le_rfl h
      _ = 1 := by rw [mul_comm, hm]

/- English proof (translation)
Introduce `B X I hI l Z a n N P z`. Establish `hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1`. Use extensionality with `x`. Conclude with `GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x`. Establish `hdeg` using `degOne_of_ok hI a P`.

Establish `hq` using `v_qOf P.1 hdeg.1 hdeg.2`. Use `⟨hseam, hq, ?_⟩` and prove the remaining obligations. Rewrite using `[hseam]`. Establish `i1 : NumberField ↥(I.rec7 l Z).host.F` using `inferInstance`. Establish `i2 : NumberField (I.rec7 l Z).host.E` using `inferInstance`.

Conclude with `forall_congr' fun r => forall_congr' fun s => @entry_iff (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ P.1 hq n N z r s`.
-/
theorem main : ∀ {B : Base} {X : PreX B.toPre} (I : TC B X), I.Ok → ∀ (l : I.Laws) (Z : TC.Later B (I.cols l)) (a : I.ι) (n N : ℕ) (P : SBof I a) (z : GL (Fin n) (AfE (I.rec7 l Z).host.F (I.rec7 l Z).host.E)), GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 ∧ Valued.v ((qOf P.1 : ℕ) : P.1.adicCompletion B.fields.E) = WithZero.exp (-1 : ℤ) ∧ (GlobalTheory.TwU.CongAt (GlobalTheory.TwU.seamP (sm I l Z) P.1) N z ↔ ∀ r s, Valued.v (adAt B.host.F P.1 (z.1 r s) - (1 : Matrix (Fin n) (Fin n) (P.1.adicCompletion B.fields.E)) r s) ≤ WithZero.exp (-(N : ℤ))) := by
  intro B X I hI l Z a n N P z
  have hseam : GlobalTheory.TwU.seamP (sm I l Z) P.1 = P.1 := by
    ext x
    exact GlobalTheory.TwU.mem_seamP (sm I l Z) P.1 x
  have hdeg := degOne_of_ok hI a P
  have hq := v_qOf P.1 hdeg.1 hdeg.2
  refine ⟨hseam, hq, ?_⟩
  rw [hseam]
  have i1 : NumberField ↥(I.rec7 l Z).host.F := inferInstance
  have i2 : NumberField (I.rec7 l Z).host.E := inferInstance
  exact forall_congr' fun r => forall_congr' fun s => @entry_iff (↥(I.rec7 l Z).host.F) (I.rec7 l Z).host.E _ i1 _ i2 _ P.1 hq n N z r s
end GlobalTheory.Mem.Col2.AdT.AdelicValuationDictionary
