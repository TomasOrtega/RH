import Mathlib
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.SetStab
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.RedPEqZeroOfDiv
import Formalism.LocalToGlobal.Columns.TargetChF

noncomputable section

open NumberField IsDedekindDomain Formalism.BasicNotions Formalism.MainNotions Formalism.L2.Col Formalism.L2.DIV Formalism.L2.Ker Formalism.UG Formalism.L2.Forms GlobalTheory.Mem GlobalTheory.Mem.Chr GlobalTheory.Mem.Col2 GlobalTheory.Mem.Col2.TC Matrix

namespace GlobalTheory.Mem.Col2.MemChart.CosetLift

section Local

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `h0 : P.intValuation (m : 𝓞 E) ≠ 0` using `P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)`. Use `⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩` and prove the remaining obligations. Establish `hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1`. Rewrite using `[← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap, HeightOneSpectrum.valuation_of_algebraMap]`. Establish `h1` using `(P.intValuation_le_pow_iff_mem e _).2 he`.

Establish `h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E)` using `by conv_rhs => rw [← WithZero.exp_log h0]`. Rewrite using `[WithZero.exp_le_exp]`. Use linear arithmetic over natural numbers and integers. Conclude with `(div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)`. Take `⟨r, s, hrs⟩` from `P.exists_primeCompl_mul_eq_of_integer _ hv`.

Conclude with `⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩`.
-/
theorem exists_pow_intAt_div (P : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ K : ℕ, ∀ e ∈ P.asIdeal ^ K, Formalism.L2.Col.IntAt P (algebraMap (𝓞 E) E e / (m : E)) := by
  have h0 : P.intValuation (m : 𝓞 E) ≠ 0 := P.intValuation_ne_zero _ (Nat.cast_ne_zero.2 hm)
  refine ⟨(-WithZero.log (P.intValuation (m : 𝓞 E))).toNat, fun e he => ?_⟩
  have hv : P.valuation E (algebraMap (𝓞 E) E e / (m : E)) ≤ 1 := by
    rw [← map_natCast (algebraMap (𝓞 E) E) m, map_div₀, HeightOneSpectrum.valuation_of_algebraMap,
      HeightOneSpectrum.valuation_of_algebraMap]
    have h1 := (P.intValuation_le_pow_iff_mem e _).2 he
    have h2 : WithZero.exp (-((-WithZero.log (P.intValuation (m : 𝓞 E))).toNat : ℤ)) ≤ P.intValuation (m : 𝓞 E) := by
      conv_rhs => rw [← WithZero.exp_log h0]
      rw [WithZero.exp_le_exp]
      omega
    exact (div_le_one₀ (zero_lt_iff.2 h0)).2 (h1.trans h2)
  obtain ⟨r, s, hrs⟩ := P.exists_primeCompl_mul_eq_of_integer _ hv
  exact ⟨r, s, s.2, by rw [mul_comm]; exact hrs⟩

/- English proof (translation)
Use `choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm`. Establish `ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal)`. Introduce `w'`. Distinguish the cases in `hne : w' = w`. Conclude with `⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩`.

Assume the negation of the conclusion as `hc`. Use `hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))` and prove the remaining obligations. Assume the negation of the conclusion as `h'`. Conclude with `hc ⟨t, h', fun _ => h⟩`. Use `choose t ht1 ht2 using ht`.

Use `w.isMaximal` as an intermediate fact. Use `w.isPrime` as an intermediate fact. Establish `he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal` using `w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _`. Take `⟨b, hb⟩` from `Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)`. Take `⟨b, rfl⟩` from `Ideal.Quotient.mk_surjective b`.

Use `⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩` and prove the remaining obligations. Take `⟨c, hc⟩` from `Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'`. Rewrite using `[hc]`. Conclude with `Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)`.
-/
theorem exists_one_intAt_div (T : Finset (HeightOneSpectrum (𝓞 E))) (w : HeightOneSpectrum (𝓞 E)) {m : ℕ} (hm : m ≠ 0) :
    ∃ e : 𝓞 E, Ideal.Quotient.mk w.asIdeal e = 1 ∧
      ∀ w' ∈ T, w' ≠ w → Formalism.L2.Col.IntAt w' (algebraMap (𝓞 E) E e / (m : E)) := by
  classical
  choose K hK using fun w' : HeightOneSpectrum (𝓞 E) => exists_pow_intAt_div w' hm
  have ht : ∀ w' : HeightOneSpectrum (𝓞 E), ∃ t : 𝓞 E, t ∉ w.asIdeal ∧ (w' ≠ w → t ∈ w'.asIdeal) := by
    intro w'
    by_cases hne : w' = w
    · exact ⟨1, Formalism.L2.Col.one_notMem w, fun h => absurd hne h⟩
    · by_contra hc
      refine hne (HeightOneSpectrum.ext (w'.isMaximal.eq_of_le w.isPrime.ne_top fun t h => ?_))
      by_contra h'
      exact hc ⟨t, h', fun _ => h⟩
  choose t ht1 ht2 using ht
  have := w.isMaximal
  have := w.isPrime
  have he0 : (∏ w' ∈ T, t w' ^ K w') ∉ w.asIdeal :=
    w.asIdeal.primeCompl.prod_mem fun w' _ => w.asIdeal.primeCompl.pow_mem (ht1 w') _
  obtain ⟨b, hb⟩ := Ideal.Quotient.exists_inv (Formalism.L2.Col.mk_ne_zero he0)
  obtain ⟨b, rfl⟩ := Ideal.Quotient.mk_surjective b
  refine ⟨(∏ w' ∈ T, t w' ^ K w') * b, by rw [map_mul, hb], fun w' hw' hne => hK w' _ (Ideal.mul_mem_right _ _ ?_)⟩
  obtain ⟨c, hc⟩ := Finset.dvd_prod_of_mem (fun w' => t w' ^ K w') hw'
  rw [hc]
  exact Ideal.mul_mem_right _ _ (Ideal.pow_mem_pow (ht2 w' hne) _)

variable [StarRing E] {n : ℕ} {ST SG : Finset (HeightOneSpectrum (𝓞 E))}

/- English proof (translation)
Use `choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)`. Use `choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1) (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))`. Use `⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩` and prove the remaining obligations. Establish `hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) = algebraMap (𝓞 E) E (e w0)` using `mul_div_cancel₀ _ TopStep.qOf_ne_zero`. Establish `hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1 (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)))` using `fun w => by`.

Distinguish the cases in `h : w = w0`. Rewrite using `[h, hc]`. Conclude with `Formalism.L2.Col.IntAt.coe _ _`. Conclude with `(TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))`. Establish `hx : ∀ w : SG, x w ∈ d.1.at w0.1` using `fun w => Formalism.L2.Col.le_locP _ _ (hxN w)`.

Simplify using `only [Finset.smul_sum, smul_smul]`. Use `⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩` and prove the remaining obligations. Rewrite using `[TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]`. Rewrite using `[TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]`. Introduce `w _ h`.

Rewrite using `[TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _) (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]`. Conclude with `fun h => absurd (Finset.mem_univ _) h`.
-/
theorem exists_vec (d : DecoSet E n ST SG) (v : ∀ w : SG, Fin n → 𝓞 E ⧸ w.1.asIdeal) :
    ∃ y : Sp E n, ∀ w : SG, ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1 ∧
      d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y) = v w := by
  classical
  choose x hxN hxv using fun w : SG => d.2.be_surj w (v w)
  choose e he1 he2 using fun w : SG => exists_one_intAt_div SG w.1 (m := Formalism.L2.Col.qOf w.1)
    (Nat.cast_ne_zero.1 (TopStep.qOf_ne_zero (P := w.1)))
  refine ⟨∑ w : SG, (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E)) • x w, fun w0 => ?_⟩
  have hc : ((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w0) / ((Formalism.L2.Col.qOf w0.1 : ℕ) : E)) =
      algebraMap (𝓞 E) E (e w0) := mul_div_cancel₀ _ TopStep.qOf_ne_zero
  have hi : ∀ w : SG, Formalism.L2.Col.IntAt w0.1
      (((Formalism.L2.Col.qOf w0.1 : ℕ) : E) * (algebraMap (𝓞 E) E (e w) / ((Formalism.L2.Col.qOf w.1 : ℕ) : E))) := fun w => by
    by_cases h : w = w0
    · rw [h, hc]
      exact Formalism.L2.Col.IntAt.coe _ _
    · exact (TopStep.intAt_nat _).mul (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm))
  have hx : ∀ w : SG, x w ∈ d.1.at w0.1 := fun w => Formalism.L2.Col.le_locP _ _ (hxN w)
  simp only [Finset.smul_sum, smul_smul]
  refine ⟨Submodule.sum_mem _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), ?_⟩
  rw [TopStep.be_sum d.2 w0 _ fun w _ => TopStep.smul_mem_locP (hi w) (hx w), Finset.sum_eq_single w0]
  · rw [TopStep.be_smul_int d.2 w0 (hi w0) (hx w0), hc, Formalism.L2.Col.reduction_coe, he1, one_smul, hxv]
  · intro w _ h
    rw [TopStep.be_smul_int d.2 w0 (hi w) (hx w), Formalism.L2.Col.reduction_mul (TopStep.intAt_nat _)
      (he2 w w0.1 w0.2 fun h' => h (Subtype.ext h'.symm)), TopStep.reduction_absNorm_eq_zero, zero_mul, zero_smul]
  · exact fun h => absurd (Finset.mem_univ _) h

/- English proof (translation)
Use extensionality with `v`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Establish `hz' : z - y ∈ d.1.at w.1`. Use `(Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩` as an intermediate fact.

Rewrite `this` using `[h0, zpow_zero, inv_one, one_smul]`. Then use the resulting hypothesis. Establish `e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z = ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y)`. Rewrite using `[← smul_add, add_sub_cancel]`. Rewrite using `[Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'), TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]`. Introduce `hv`.

Conclude with `⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩`.
-/
theorem coset_be (d : DecoSet E n ST SG) (SB : Finset (HeightOneSpectrum (𝓞 E))) (w : SG) (hw : w.1 ∈ SB) (e0 : SB → ℤ)
    (h0 : e0 ⟨w.1, hw⟩ = 0) {y : Sp E n} (hy : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y ∈ d.1.at w.1) :
    {v | ∃ z ∈ {z | z - y ∈ Formalism.L2.Col.locLat SB d.1.N e0}, v = d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z)} =
      {d.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y)} := by
  ext v
  constructor
  · rintro ⟨z, hz, rfl⟩
    have hz' : z - y ∈ d.1.at w.1 := by
      have := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hz ⟨w.1, hw⟩
      rwa [h0, zpow_zero, inv_one, one_smul] at this
    have e : ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • z =
        ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • y + ((Formalism.L2.Col.qOf w.1 : ℕ) : E) • (z - y) := by
      rw [← smul_add, add_sub_cancel]
    rw [Set.mem_singleton_iff, e, d.2.be_add w _ hy _ (TopStep.smul_mem_locP (TopStep.intAt_nat _) hz'),
      TopStep.be_smul_int d.2 w (TopStep.intAt_nat _) hz', TopStep.reduction_absNorm_eq_zero, zero_smul, add_zero]
  · intro hv
    exact ⟨y, by rw [Set.mem_setOf_eq, sub_self]; exact zero_mem _, hv⟩

end Local

/- English proof (translation)
Distinguish the cases in `h : j + 1 = R.m`. Take `⟨y, hy, hY⟩` from `q.mem_ybSet h`. Establish `hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu` using `fun w => Finset.mem_union_left _ w.2`. Establish `hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs` using `fun P => (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩`. Take `⟨y', hy'⟩` from `exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)`.

Use `⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[ysAt_ys_of_eq sel mu cst h]`. Use `⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩` and prove the remaining obligations. Rewrite using `[if_pos (hG' P), _root_.zpow_neg_one, inv_inv]`. Conclude with `(hy' ⟨P.1, hG' P⟩).1`.

Use function extensionality and compare the values at `w`. Establish `h1` using `(Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩`. Rewrite `h1` using `[if_pos w.2, _root_.zpow_neg_one, inv_inv]`. Use `(coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_` and prove the remaining obligations. Rewrite using `[(hy' w).2, MemChart.bar, hY]`.

Conclude with `(coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm`. Establish `hY : q.1.2 = ∅`. Use `q.2` as an intermediate fact. Rewrite `this` using `[ysAt_ys_of_ne sel mu cst h]`. Then use the resulting hypothesis. Use `⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `w`. Simplify using `[MemChart.bar, hY]`.
-/
theorem exists_ptAt_bar_eq {X : Fields} {Pr : Primes X} {R : Ranks} {sel : HeightOneSpectrum (𝓞 X.F) → HeightOneSpectrum (𝓞 X.E)}
    {S : Set ℕ} {mu : Tup X.F X.E X.K S} {cst : LocCst X (rowSG Pr sel mu)} {u : Pr.Word} {j : ℕ}
    (hQ : QE sel (mu : Chr X.F X.E X.K) = ∅) (_hq : ∀ w ∈ Pr.vGs, ((Formalism.L2.Col.qOf w : ℕ) : 𝓞 X.E) ∉ w.asIdeal ^ 2)
    (q : PtAt R sel mu cst u j) (d : DecoSet X.E (R.N j) (Pr.vT u) Pr.vGs) :
    ∃ q' : PtAt R sel mu cst u j, q'.1.1.deco = d ∧ MemChart.bar q' = MemChart.bar q := by
  classical
  by_cases h : j + 1 = R.m
  · obtain ⟨y, hy, hY⟩ := q.mem_ybSet h
    have hG : ∀ w : Pr.vGs, w.1 ∈ rowSG Pr sel mu := fun w => Finset.mem_union_left _ w.2
    have hG' : ∀ P : rowSG Pr sel mu, P.1 ∈ Pr.vGs := fun P =>
      (Finset.mem_union.mp P.2).resolve_right fun h' => chfok_false hQ ⟨P.1, h'⟩
    obtain ⟨y', hy'⟩ := exists_vec d fun w => q.1.1.deco.1.be w (((Formalism.L2.Col.qOf w.1 : ℕ) : X.E) • y)
    refine ⟨⟨(chfokLift hQ d, {z | z - y' ∈ Formalism.L2.Col.locLat (rowSG Pr sel mu) d.1.N
      (fun P => if P.1 ∈ Pr.vGs then 0 else (cst.M : ℤ))}), ?_⟩, rfl, ?_⟩
    · rw [ysAt_ys_of_eq sel mu cst h]
      refine ⟨y', (Formalism.L2.Col.mem_locLat _ _ _ _).2 fun P => ?_, by congr!⟩
      rw [if_pos (hG' P), _root_.zpow_neg_one, inv_inv]
      exact (hy' ⟨P.1, hG' P⟩).1
    · funext w
      have h1 := (Formalism.L2.Col.mem_locLat _ _ _ _).1 hy ⟨w.1, hG w⟩
      rw [if_pos w.2, _root_.zpow_neg_one, inv_inv] at h1
      refine (coset_be d _ w (hG w) _ (if_pos w.2) (hy' w).1).trans ?_
      rw [(hy' w).2, MemChart.bar, hY]
      exact (coset_be q.1.1.deco _ w (hG w) _ (if_pos w.2) h1).symm
  · have hY : q.1.2 = ∅ := by
      have := q.2
      rwa [ysAt_ys_of_ne sel mu cst h] at this
    refine ⟨⟨(chfokLift hQ d, ∅), by rw [ysAt_ys_of_ne sel mu cst h]; rfl⟩, rfl, ?_⟩
    funext w
    simp [MemChart.bar, hY]

end GlobalTheory.Mem.Col2.MemChart.CosetLift
