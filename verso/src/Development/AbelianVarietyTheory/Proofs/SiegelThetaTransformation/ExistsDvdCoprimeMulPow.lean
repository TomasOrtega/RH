import Mathlib
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsWeakOfDatum
import Development.AbelianVarietyTheory.Definitions.SpanningFamilies.IsHeatZero
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR.Datum Formalism.L2.Pj MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker
open GlobalTheory.SW hiding Level
open GlobalTheory.Dict (hx pv)
open ReciprocityTheory.ChartRestriction.G.I2 (polyDeriv)
open scoped TensorProduct ComplexConjugate Real Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.Ker.DCos

/- English proof (translation)
Proceed by induction on `N using Nat.strong_induction_on with`. Consider the case `_ N ih`. Distinguish the cases in `h : N.Coprime M`. Conclude with `⟨N, 0, hN, h, by simp⟩`. Take `⟨N', hN'⟩` from `Nat.gcd_dvd_left N M`.

Establish `hg : 0 < Nat.gcd N M` using `Nat.gcd_pos_of_pos_left _ hN`. Establish `hg1 : 1 < Nat.gcd N M`. Establish `: Nat.gcd N M ≠ 1` using `h`. Use linear arithmetic over natural numbers and integers. Establish `hp : 0 < N'` using `Nat.pos_of_ne_zero (by rintro rfl; omega)`.

Establish `hlt : N' < N`. Combine the equalities or inequalities in the displayed calculation. Take `⟨s, k, hs, hc, hd⟩` from `ih N' hlt hp`. Use `⟨s, k + 1, hs, hc, ?_⟩` and prove the remaining obligations. Rewrite using `[hN', pow_succ, ← mul_assoc, mul_comm]`.

Conclude with `mul_dvd_mul hd (Nat.gcd_dvd_right N M)`.
-/
theorem exists_dvd_coprime_mul_pow (M : ℕ) (N : ℕ) (hN : 0 < N) :
    ∃ s k : ℕ, 0 < s ∧ s.Coprime M ∧ N ∣ s * M ^ k := by
  induction N using Nat.strong_induction_on with
  | _ N ih =>
    by_cases h : N.Coprime M
    · exact ⟨N, 0, hN, h, by simp⟩
    · obtain ⟨N', hN'⟩ := Nat.gcd_dvd_left N M
      have hg : 0 < Nat.gcd N M := Nat.gcd_pos_of_pos_left _ hN
      have hg1 : 1 < Nat.gcd N M := by
        have : Nat.gcd N M ≠ 1 := h
        omega
      have hp : 0 < N' := Nat.pos_of_ne_zero (by rintro rfl; omega)
      have hlt : N' < N := by
        calc N' = 1 * N' := (one_mul _).symm
          _ < Nat.gcd N M * N' := Nat.mul_lt_mul_of_pos_right hg1 hp
          _ = N := hN'.symm
      obtain ⟨s, k, hs, hc, hd⟩ := ih N' hlt hp
      refine ⟨s, k + 1, hs, hc, ?_⟩
      rw [hN', pow_succ, ← mul_assoc, mul_comm]
      exact mul_dvd_mul hd (Nat.gcd_dvd_right N M)

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_same (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1`.
-/
theorem evalV_single_same (F : Type) [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F)) :
    evalV F v (singleV F v 1) = 1 := by
  classical
  exact RestrictedProduct.single_eq_same
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) v 1

/- English proof (translation)
Conclude with `RestrictedProduct.single_eq_of_ne (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h`.
-/
theorem evalV_single_ne (F : Type) [Field F] [NumberField F] (v v' : HeightOneSpectrum (𝓞 F))
    (h : v' ≠ v) : evalV F v' (singleV F v 1) = 0 := by
  classical
  exact RestrictedProduct.single_eq_of_ne
    (fun w : HeightOneSpectrum (𝓞 F) => w.adicCompletionIntegers F) 1 h

/- English proof (translation)
The claim follows from `RestrictedProduct.ext _ _ h`.
-/
theorem af_ext {F : Type} [Field F] [NumberField F] {a b : Af F} (h : ∀ v, evalV F v a = evalV F v b) :
    a = b := RestrictedProduct.ext _ _ h

/- English proof (translation)
Establish `hM0 : (M : F) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Establish `hfin : {v : HeightOneSpectrum (𝓞 F) | (M : 𝓞 F) ∈ v.asIdeal}.Finite`. Establish `h` using `Ideal.finite_factors (I := Ideal.span {(M : 𝓞 F)}) (by simpa using hM.ne')`. Use `h.subset fun v hv => ?_` and prove the remaining obligations. Conclude with `Ideal.dvd_span_singleton.2 hv`.

Establish `e1 : ∀ w ∈ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 1` using `fun w hw => by`. Rewrite using `[map_sum, Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_single_ne F b w hb.symm, evalV_single_same]`. Establish `e0 : ∀ w ∉ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 0` using `fun w hw => by`. Rewrite using `[map_sum, Finset.sum_eq_zero fun b hb => evalV_single_ne F b w fun h => hw (h ▸ hb)]`. Use `⟨hfin.toFinset, fun v hv => by simpa using hv, algebraMap F (Af F) (M : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1), fun w => ?_, ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_sub, map_one, AlgHom.commutes]`. Distinguish the cases in `hw : w ∈ hfin.toFinset`. Rewrite using `[e1 w hw, sub_self, mul_zero]`. Conclude with `zero_mem _`. Rewrite using `[e0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]`.

Establish `h1 : w.valuation F (algebraMap (𝓞 F) F M) = 1` using `(w.valuation_eq_one_iff_notMem (K := F)).2 (by simpa using hw)`. Rewrite `h1` using `[map_natCast]`. Establish `h2 : Valued.v (algebraMap F (Fv F w) (M : F)⁻¹) = w.valuation F (M : F)⁻¹` using `w.valuedAdicCompletion_eq_valuation' _`. Rewrite using `[h2, map_inv₀, h1, inv_one]`. Establish `h2 : algebraMap F (Af F) (M : F)⁻¹ * (M : Af F) = 1`.

Rewrite using `[← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM0, map_one]`. Rewrite using `[mul_right_comm, h2, one_mul, add_sub_cancel]`. Use `af_ext fun w => ?_` and prove the remaining obligations. Rewrite using `[map_mul, map_mul, map_sub, map_one, map_zero]`. Distinguish the cases in `hw : w ∈ hfin.toFinset`.

Rewrite using `[e1 w hw, sub_self, mul_zero, mul_zero]`. Rewrite using `[e0 w hw, zero_mul]`.
-/
theorem exists_idem (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : 0 < M) :
    ∃ P : Finset (HeightOneSpectrum (𝓞 F)), (∀ v ∈ P, (M : 𝓞 F) ∈ v.asIdeal) ∧
      ∃ β ∈ intAf F, ∑ v ∈ P, singleV F v 1 + β * M = 1 ∧ (∑ v ∈ P, singleV F v 1) * β = 0 := by
  classical
  have hM0 : (M : F) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  have hfin : {v : HeightOneSpectrum (𝓞 F) | (M : 𝓞 F) ∈ v.asIdeal}.Finite := by
    have h := Ideal.finite_factors (I := Ideal.span {(M : 𝓞 F)}) (by simpa using hM.ne')
    refine h.subset fun v hv => ?_
    exact Ideal.dvd_span_singleton.2 hv
  have e1 : ∀ w ∈ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 1 := fun w hw => by
    rw [map_sum, Finset.sum_eq_single_of_mem w hw fun b _ hb => evalV_single_ne F b w hb.symm,
        evalV_single_same]
  have e0 : ∀ w ∉ hfin.toFinset, evalV F w (∑ v ∈ hfin.toFinset, singleV F v 1) = 0 := fun w hw => by
    rw [map_sum, Finset.sum_eq_zero fun b hb => evalV_single_ne F b w fun h => hw (h ▸ hb)]
  refine ⟨hfin.toFinset, fun v hv => by simpa using hv,
    algebraMap F (Af F) (M : F)⁻¹ * (1 - ∑ v ∈ hfin.toFinset, singleV F v 1), fun w => ?_, ?_, ?_⟩
  · rw [map_mul, map_sub, map_one, AlgHom.commutes]
    by_cases hw : w ∈ hfin.toFinset
    · rw [e1 w hw, sub_self, mul_zero]
      exact zero_mem _
    · rw [e0 w hw, sub_zero, mul_one, HeightOneSpectrum.mem_adicCompletionIntegers]
      have h1 : w.valuation F (algebraMap (𝓞 F) F M) = 1 :=
        (w.valuation_eq_one_iff_notMem (K := F)).2 (by simpa using hw)
      rw [map_natCast] at h1
      have h2 : Valued.v (algebraMap F (Fv F w) (M : F)⁻¹) = w.valuation F (M : F)⁻¹ :=
        w.valuedAdicCompletion_eq_valuation' _
      rw [h2, map_inv₀, h1, inv_one]
  · have h2 : algebraMap F (Af F) (M : F)⁻¹ * (M : Af F) = 1 := by
      rw [← map_natCast (algebraMap F (Af F)) M, ← map_mul, inv_mul_cancel₀ hM0, map_one]
    rw [mul_right_comm, h2, one_mul, add_sub_cancel]
  · refine af_ext fun w => ?_
    rw [map_mul, map_mul, map_sub, map_one, map_zero]
    by_cases hw : w ∈ hfin.toFinset
    · rw [e1 w hw, sub_self, mul_zero, mul_zero]
    · rw [e0 w hw, zero_mul]

section Generic

variable {R : Type} [CommRing R] {k : ℕ}

def CongH (H : AddSubgroup (Fin k → R)) (M : ℕ) (m : Matrix (Fin k) (Fin k) R) : Prop :=
  (∀ u, u ∈ H ↔ ∃ u₀ ∈ H, u = m *ᵥ u₀) ∧ ∀ u ∈ H, ∃ u' ∈ H, m *ᵥ u - u = M • u'

/- English proof (translation)
Set `cV : (Fin k → R) →+ (Fin k → R)` to `c.toAddMonoidHom.compLeft _`. Establish `cc : ∀ u, cV (cV u) = u` using `fun u => funext fun _ => hc _`. Establish `cm : ∀ u, cV (m *ᵥ u) = m.map c *ᵥ cV u` using `fun u => funext fun i => RingHom.map_mulVec c m u i`. Establish `mem : ∀ {u}, u ∈ H → cV u ∈ H` using `fun {u} hu => hH u hu`. Use `⟨fun u => ⟨fun hu => ?_, ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations.

Take `⟨u₀, h₀, e⟩` from `(h.1 _).1 (mem hu)`. Conclude with `⟨cV u₀, mem h₀, by rw [← cm, ← e, cc]⟩`. Introduce and unpack `⟨u₀, h₀, rfl⟩`. Use `mem ((h.1 _).2 ⟨_, mem h₀, rfl⟩)` as an intermediate fact. Rewrite `this` using `[cm, cc]`. Then use the resulting hypothesis.

Take `⟨u', h', e⟩` from `h.2 _ (mem hu)`. Use `⟨cV u', mem h', ?_⟩` and prove the remaining obligations. Use `congrArg cV e` as an intermediate fact. Rewrite `this` using `[map_sub, cm, cc, map_nsmul]`. Then use the resulting hypothesis.
-/
theorem CongH.conj {H : AddSubgroup (Fin k → R)} {M : ℕ} {m : Matrix (Fin k) (Fin k) R} (c : R →+* R)
    (hc : ∀ z, c (c z) = z) (hH : ∀ u ∈ H, (fun i => c (u i)) ∈ H) (h : CongH H M m) :
    CongH H M (m.map c) := by
  let cV : (Fin k → R) →+ (Fin k → R) := c.toAddMonoidHom.compLeft _
  have cc : ∀ u, cV (cV u) = u := fun u => funext fun _ => hc _
  have cm : ∀ u, cV (m *ᵥ u) = m.map c *ᵥ cV u := fun u => funext fun i => RingHom.map_mulVec c m u i
  have mem : ∀ {u}, u ∈ H → cV u ∈ H := fun {u} hu => hH u hu
  refine ⟨fun u => ⟨fun hu => ?_, ?_⟩, fun u hu => ?_⟩
  · obtain ⟨u₀, h₀, e⟩ := (h.1 _).1 (mem hu)
    exact ⟨cV u₀, mem h₀, by rw [← cm, ← e, cc]⟩
  · rintro ⟨u₀, h₀, rfl⟩
    have := mem ((h.1 _).2 ⟨_, mem h₀, rfl⟩)
    rwa [cm, cc] at this
  · obtain ⟨u', h', e⟩ := h.2 _ (mem hu)
    refine ⟨cV u', mem h', ?_⟩
    have := congrArg cV e
    rwa [map_sub, cm, cc, map_nsmul] at this

/- English proof (translation)
Establish `ha1 : e • a = e • (1 : Matrix (Fin k) (Fin k) R)` using `by ext i j; exact ha i j`. Establish `hb1 : e • b = e • (1 : Matrix (Fin k) (Fin k) R)` using `by ext i j; exact hb i j`. Establish `h2 : e • a' = e • (1 : Matrix (Fin k) (Fin k) R)`. Rewrite using `[← h, ← Matrix.smul_mul, ha1, Matrix.smul_mul, Matrix.one_mul]`. Rewrite using `[← Matrix.mul_smul, hb1, Matrix.mul_smul, Matrix.mul_one, ← Matrix.smul_mul, h2, Matrix.smul_mul, Matrix.one_mul]`.
-/
theorem idem_conj {e : R} {a a' b d : Matrix (Fin k) (Fin k) R} (h : a * a' = 1)
    (ha : ∀ i j, e * a i j = e * (1 : Matrix (Fin k) (Fin k) R) i j)
    (hb : ∀ i j, e * b i j = e * (1 : Matrix (Fin k) (Fin k) R) i j) :
    e • (a' * d * b) = e • d := by
  have ha1 : e • a = e • (1 : Matrix (Fin k) (Fin k) R) := by ext i j; exact ha i j
  have hb1 : e • b = e • (1 : Matrix (Fin k) (Fin k) R) := by ext i j; exact hb i j
  have h2 : e • a' = e • (1 : Matrix (Fin k) (Fin k) R) := by
    rw [← h, ← Matrix.smul_mul, ha1, Matrix.smul_mul, Matrix.one_mul]
  rw [← Matrix.mul_smul, hb1, Matrix.mul_smul, Matrix.mul_one, ← Matrix.smul_mul, h2, Matrix.smul_mul,
    Matrix.one_mul]

/- English proof (translation)
Establish `ha' : a' * a = 1` using `mul_eq_one_comm.1 ha`. Establish `hb' : b' * b = 1` using `mul_eq_one_comm.1 hb`. Establish `hd' : d * d' = 1` using `mul_eq_one_comm.1 hd`. Establish `mA : ∀ u, u ∈ A ↔ a' *ᵥ u ∈ H` using `fun u => by`. Rewrite using `[hA]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u₀, h₀, rfl⟩`. Rewrite using `[Matrix.mulVec_mulVec, ha', Matrix.one_mulVec]` and apply the resulting hypothesis. Introduce `h; exact ⟨_, h, by rw [Matrix.mulVec_mulVec, ha, Matrix.one_mulVec]⟩`. Prove the components needed by the constructor for the conclusion.

Introduce `h u`. Rewrite using `[hB, mA, h]`. Use `exists_congr fun u₀ => and_congr_right fun _ => ⟨?_, fun e => ?_⟩` and prove the remaining obligations. Introduce and unpack `rfl`. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc]`.

Use `congrArg (fun w => (d' * a) *ᵥ w) e` as an intermediate fact. Simplify using `only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this`. Simplify using `only [← Matrix.mul_assoc a, ha, Matrix.one_mul, hd, ← Matrix.mul_assoc d', Matrix.one_mulVec] at this`. Conclude with `this`. Introduce `h u`.

Prove the components needed by the constructor for the conclusion. Introduce `hu`. Establish `h1 : (d' * a) *ᵥ u ∈ B`. Rewrite using `[h, hA]`. Conclude with `⟨u, hu, by rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hd', Matrix.one_mul]⟩`.

Take `⟨u₀, h₀, e⟩` from `(hB _).1 h1`. Use `⟨u₀, h₀, ?_⟩` and prove the remaining obligations. Rewrite using `[← Matrix.mulVec_mulVec, ← e, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd', Matrix.one_mul, ha', Matrix.one_mulVec]`. Introduce and unpack `⟨u₀, h₀, rfl⟩`. Use `(mA _).1 ((h _).1 ((hB _).2 ⟨u₀, h₀, rfl⟩))` as an intermediate fact.

Rewrite `this` using `[Matrix.mulVec_mulVec, Matrix.mulVec_mulVec]`. Then use the resulting hypothesis.
-/
theorem mov_iff {H A B : AddSubgroup (Fin k → R)} {a a' b b' d : Matrix (Fin k) (Fin k) R}
    (ha : a * a' = 1) (hA : ∀ u, u ∈ A ↔ ∃ u₀ ∈ H, u = a *ᵥ u₀)
    (hB : ∀ u, u ∈ B ↔ ∃ u₀ ∈ H, u = b *ᵥ u₀) (hb : b * b' = 1) {d' : Matrix (Fin k) (Fin k) R}
    (hd : d' * d = 1) :
    (∀ u, u ∈ H ↔ ∃ u₀ ∈ H, u = (a' * d * b) *ᵥ u₀) ↔ ∀ u, u ∈ B ↔ d *ᵥ u ∈ A := by
  have ha' : a' * a = 1 := mul_eq_one_comm.1 ha
  have hb' : b' * b = 1 := mul_eq_one_comm.1 hb
  have hd' : d * d' = 1 := mul_eq_one_comm.1 hd
  have mA : ∀ u, u ∈ A ↔ a' *ᵥ u ∈ H := fun u => by
    rw [hA]
    constructor
    · rintro ⟨u₀, h₀, rfl⟩; rwa [Matrix.mulVec_mulVec, ha', Matrix.one_mulVec]
    · intro h; exact ⟨_, h, by rw [Matrix.mulVec_mulVec, ha, Matrix.one_mulVec]⟩
  constructor
  · intro h u
    rw [hB, mA, h]
    refine exists_congr fun u₀ => and_congr_right fun _ => ⟨?_, fun e => ?_⟩
    · rintro rfl; simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc]
    · have := congrArg (fun w => (d' * a) *ᵥ w) e
      simp only [Matrix.mulVec_mulVec, Matrix.mul_assoc] at this
      simp only [← Matrix.mul_assoc a, ha, Matrix.one_mul, hd, ← Matrix.mul_assoc d', Matrix.one_mulVec] at this
      exact this
  · intro h u
    constructor
    · intro hu
      have h1 : (d' * a) *ᵥ u ∈ B := by
        rw [h, hA]
        exact ⟨u, hu, by rw [Matrix.mulVec_mulVec, ← Matrix.mul_assoc, hd', Matrix.one_mul]⟩
      obtain ⟨u₀, h₀, e⟩ := (hB _).1 h1
      refine ⟨u₀, h₀, ?_⟩
      rw [← Matrix.mulVec_mulVec, ← e, Matrix.mulVec_mulVec, Matrix.mul_assoc, ← Matrix.mul_assoc d, hd',
        Matrix.one_mul, ha', Matrix.one_mulVec]
    · rintro ⟨u₀, h₀, rfl⟩
      have := (mA _).1 ((h _).1 ((hB _).2 ⟨u₀, h₀, rfl⟩))
      rwa [Matrix.mulVec_mulVec, Matrix.mulVec_mulVec] at this

variable {E : Type} [Field E] [NumberField E]

/- English proof (translation)
Establish `hb' : ∀ u ∈ H, b • u ∈ H` using `hb`. Establish `hn : ∀ (n : ℤ), ∀ u ∈ H, (n : R) • u ∈ H` using `fun n u hu => by`. Rewrite using `[Int.cast_smul_eq_zsmul]`. Conclude with `H.zsmul_mem hu n`. Establish `hn' : ∀ (n : ℕ), ∀ u ∈ H, (n : R) • u ∈ H` using `fun n u hu => by`.

Simplify using `using hn n u hu`. Establish `he : ∀ u ∈ H, e • u ∈ H` using `fun u hu => by`. Establish `: e = 1 - b * M` using `eq_sub_of_add_eq h1`. Rewrite using `[this, sub_smul, one_smul, mul_smul]`. Conclude with `H.sub_mem hu (hb' _ (hn' _ _ hu))`.

Establish `hz : ∀ u, e • (m *ᵥ u - u) = e • ((δ - 1).map ι *ᵥ u)` using `fun u => by`. Rewrite using `[smul_sub, ← Matrix.smul_mulVec, hm, Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι), Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, Matrix.smul_mulVec]`. Establish `hM0 : (M : E) ≠ 0` using `Nat.cast_ne_zero.2 hM.ne'`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Set `w : Matrix (Fin k) (Fin k) E` to `(M : E)⁻¹ • (δ - 1)`. Choose the witnesses or unpack the hypotheses as in `⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ ((N : E) * w i j) := by`. Take `⟨y, hy, h⟩` from `exists_integral_multiples ℤ ℚ (L := E) (Finset.univ.image fun p : Fin k × Fin k => w p.1 p.2)`. Use `⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩` and prove the remaining obligations. Use `h (w i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)` as an intermediate fact.

Rewrite `this` using `[zsmul_eq_mul]`. Break down `Int.natAbs_eq y with e | e` into its components or cases. Rewrite `this` using `[e]`. Simplify using `using this`. Rewrite `this` using `[e]`.

Simplify using `using this.neg`. Take `⟨s, n, hs, hc, t, ht⟩` from `exists_dvd_coprime_mul_pow M N hN0`. Use `⟨s, hs, hc, (s : E) • w, fun i j => ?_, ?_⟩` and prove the remaining obligations. Establish `hj : (fun i => ι ((Pi.single j 1 : Fin k → E) i)) ∈ H` using `(hstd _).2 (Submodule.subset_span ⟨j, rfl⟩)`. Take `⟨u', hu', e1⟩` from `h _ hj`.

Establish `e2` using `hz (fun i => ι ((Pi.single j 1 : Fin k → E) i))`. Rewrite `e2` using `[e1]`. Establish `e3 : e • (fun i => ι (w i j)) = e • u'`. Use function extensionality and compare the values at `i`. Use `congrFun e2 i` as an intermediate fact.

Rewrite `this` using `[Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← Function.comp_def, ← RingHom.map_mulVec]`. Simplify using `only [Matrix.mulVec_single_one, smul_eq_mul, nsmul_eq_mul, Matrix.col_apply] at this`. Establish `hMi : ι (M : E)⁻¹ * (M : R) = 1`. Rewrite using `[← map_natCast ι, ← map_mul, inv_mul_cancel₀ hM0, map_one]`. Express the relevant statement in the definitionally equal form `e * ι ((M : E)⁻¹ * (δ - 1) i j) = e * u' i`.

Rewrite using `[map_mul]`. Take the linear combination `(-ι (M : E)⁻¹) * this + e * u' i * hMi`. Establish `hNw : (fun i => ι ((N : E) * w i j)) ∈ H` using `(hstd fun i => (N : E) * w i j).2 ((SW.Base.mem_stdL _).2 fun i => hN i j)`. Establish `hpow : ∀ n : ℕ, e + b ^ (n + 1) * (M : R) ^ (n + 1) = 1`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => simpa using h1`. Consider the case `succ n ih => linear_combination (b * M) * ih + h1 - (M : R) * h0`. Establish `hbp : ∀ n : ℕ, ∀ u ∈ H, b ^ n • u ∈ H`. Introduce `n`.

Proceed by induction on `n with`. Consider the case `zero => intro u hu`. Simplify using `using hu`. Consider the case `succ n ih => intro u hu`. Rewrite using `[pow_succ, mul_smul]`.

Conclude with `ih _ (hb' _ hu)`. Establish `ht' : (s : R) * (M : R) ^ n = N * t` using `by exact_mod_cast congrArg (Nat.cast : ℕ → R) ht`. Establish `key : (fun i => ι ((s : E) * w i j)) = (s : R) • e • (fun i => ι (w i j)) + b ^ (n + 1) • ((t * M : ℕ) : R) • (fun i => ι ((N : E) * w i j))`. Use function extensionality and compare the values at `i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Nat.cast_mul]`.

Take the linear combination `(-(s : R) * ι (w i j)) * hpow n + (b ^ (n + 1) * M * ι (w i j)) * ht'`. Establish `: (fun i => ι ((s : E) * w i j)) ∈ H`. Rewrite using `[key, e3]`. Conclude with `H.add_mem (hn' _ _ (he _ hu')) (hbp _ _ (hn' _ _ hNw))`. Conclude with `(SW.Base.mem_stdL _).1 ((hstd fun i => (s : E) * w i j).1 this) i`.

Rewrite using `[smul_comm, smul_smul (M : E), mul_inv_cancel₀ hM0, one_smul]`. Introduce and unpack `⟨s, hs, hc, y, hy, e1⟩ u hu`. Take `⟨p, q, hpq⟩ : IsCoprime (s : ℤ) (M : ℤ)` from `Nat.isCoprime_iff_coprime.2 hc`. Establish `hpq' : (p : R) * s + q * M = 1` using `by exact_mod_cast congrArg (Int.cast : ℤ → R) hpq`. Establish `hzH : m *ᵥ u - u ∈ H` using `H.sub_mem (hmH u hu) hu`.

Establish `e2 : (s : R) • ((δ - 1).map ι *ᵥ u) = (M : R) • (y.map ι *ᵥ u)`. Rewrite using `[← Matrix.smul_mulVec, ← Matrix.smul_mulVec]`. Use `congr 1`. Use extensionality with `i j`. Use `congrArg ι (congrFun (congrFun e1 i) j)` as an intermediate fact.

Simplify using `using this`. Establish `e3` using `hz u`. Generalize the expression as in `m *ᵥ u - u = z at *`. Use `⟨(p : R) • e • (y.map ι *ᵥ u) + (p : R) • (s : R) • b • z + (q : R) • z, H.add_mem (H.add_mem (hn _ _ (he _ (hint y hy u hu))) (hn _ _ (hn' _ _ (hb' _ hzH)))) (hn _ _ hzH), ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `i`.

Establish `a2` using `congrFun e2 i`. Establish `a3` using `congrFun e3 i`. Simplify using `only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at a2 a3 ⊢`. Take the linear combination `(-z i) * hpq' - (p * s * z i) * h1 + (p * s) * a3 + (p * e) * a2`.
-/
theorem cong_iff (ι : E →+* R) {H : AddSubgroup (Fin k → R)} {M : ℕ} (hM : 0 < M) {e b : R}
    (h1 : e + b * M = 1) (h0 : e * b = 0) (hb : ∀ u ∈ H, (fun i => b * u i) ∈ H)
    (hstd : ∀ v : Fin k → E, (fun i => ι (v i)) ∈ H ↔ v ∈ stdL E k)
    (hint : ∀ y : Matrix (Fin k) (Fin k) E, IntM y → ∀ u ∈ H, y.map ι *ᵥ u ∈ H)
    {m : Matrix (Fin k) (Fin k) R} {δ : Matrix (Fin k) (Fin k) E} (hm : e • m = e • δ.map ι)
    (hmH : ∀ u ∈ H, m *ᵥ u ∈ H) :
    (∀ u ∈ H, ∃ u' ∈ H, m *ᵥ u - u = M • u') ↔
      ∃ s : ℕ, 0 < s ∧ s.Coprime M ∧
        ∃ y : Matrix (Fin k) (Fin k) E, IntM y ∧ (s : E) • (δ - 1) = (M : E) • y := by
  have hb' : ∀ u ∈ H, b • u ∈ H := hb
  have hn : ∀ (n : ℤ), ∀ u ∈ H, (n : R) • u ∈ H := fun n u hu => by
    rw [Int.cast_smul_eq_zsmul]; exact H.zsmul_mem hu n
  have hn' : ∀ (n : ℕ), ∀ u ∈ H, (n : R) • u ∈ H := fun n u hu => by
    simpa using hn n u hu
  have he : ∀ u ∈ H, e • u ∈ H := fun u hu => by
    have : e = 1 - b * M := eq_sub_of_add_eq h1
    rw [this, sub_smul, one_smul, mul_smul]
    exact H.sub_mem hu (hb' _ (hn' _ _ hu))
  have hz : ∀ u, e • (m *ᵥ u - u) = e • ((δ - 1).map ι *ᵥ u) := fun u => by
    rw [smul_sub, ← Matrix.smul_mulVec, hm, Matrix.map_sub _ (map_sub ι), Matrix.map_one _ (map_zero ι) (map_one ι),
      Matrix.sub_mulVec, Matrix.one_mulVec, smul_sub, Matrix.smul_mulVec]
  have hM0 : (M : E) ≠ 0 := Nat.cast_ne_zero.2 hM.ne'
  constructor
  · intro h
    let w : Matrix (Fin k) (Fin k) E := (M : E)⁻¹ • (δ - 1)
    obtain ⟨N, hN0, hN⟩ : ∃ N : ℕ, 0 < N ∧ ∀ i j, IsIntegral ℤ ((N : E) * w i j) := by
      obtain ⟨y, hy, h⟩ := exists_integral_multiples ℤ ℚ (L := E)
        (Finset.univ.image fun p : Fin k × Fin k => w p.1 p.2)
      refine ⟨y.natAbs, Int.natAbs_pos.2 hy, fun i j => ?_⟩
      have := h (w i j) (Finset.mem_image.2 ⟨(i, j), Finset.mem_univ _, rfl⟩)
      rw [zsmul_eq_mul] at this
      rcases Int.natAbs_eq y with e | e
      · rw [e] at this; simpa using this
      · rw [e] at this; simpa using this.neg
    obtain ⟨s, n, hs, hc, t, ht⟩ := exists_dvd_coprime_mul_pow M N hN0
    refine ⟨s, hs, hc, (s : E) • w, fun i j => ?_, ?_⟩
    · have hj : (fun i => ι ((Pi.single j 1 : Fin k → E) i)) ∈ H :=
        (hstd _).2 (Submodule.subset_span ⟨j, rfl⟩)
      obtain ⟨u', hu', e1⟩ := h _ hj
      have e2 := hz (fun i => ι ((Pi.single j 1 : Fin k → E) i))
      rw [e1] at e2
      have e3 : e • (fun i => ι (w i j)) = e • u' := by
        funext i
        have := congrFun e2 i
        rw [Pi.smul_apply, Pi.smul_apply, Pi.smul_apply, ← Function.comp_def, ← RingHom.map_mulVec] at this
        simp only [Matrix.mulVec_single_one, smul_eq_mul, nsmul_eq_mul, Matrix.col_apply] at this
        have hMi : ι (M : E)⁻¹ * (M : R) = 1 := by
          rw [← map_natCast ι, ← map_mul, inv_mul_cancel₀ hM0, map_one]
        change e * ι ((M : E)⁻¹ * (δ - 1) i j) = e * u' i
        rw [map_mul]
        linear_combination (-ι (M : E)⁻¹) * this + e * u' i * hMi
      have hNw : (fun i => ι ((N : E) * w i j)) ∈ H :=
        (hstd fun i => (N : E) * w i j).2 ((SW.Base.mem_stdL _).2 fun i => hN i j)
      have hpow : ∀ n : ℕ, e + b ^ (n + 1) * (M : R) ^ (n + 1) = 1 := by
        intro n
        induction n with
        | zero => simpa using h1
        | succ n ih => linear_combination (b * M) * ih + h1 - (M : R) * h0
      have hbp : ∀ n : ℕ, ∀ u ∈ H, b ^ n • u ∈ H := by
        intro n
        induction n with
        | zero => intro u hu; simpa using hu
        | succ n ih => intro u hu; rw [pow_succ, mul_smul]; exact ih _ (hb' _ hu)
      have ht' : (s : R) * (M : R) ^ n = N * t := by exact_mod_cast congrArg (Nat.cast : ℕ → R) ht
      have key : (fun i => ι ((s : E) * w i j)) = (s : R) • e • (fun i => ι (w i j)) +
          b ^ (n + 1) • ((t * M : ℕ) : R) • (fun i => ι ((N : E) * w i j)) := by
        funext i
        simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, map_mul, map_natCast, Nat.cast_mul]
        linear_combination (-(s : R) * ι (w i j)) * hpow n + (b ^ (n + 1) * M * ι (w i j)) * ht'
      have : (fun i => ι ((s : E) * w i j)) ∈ H := by
        rw [key, e3]
        exact H.add_mem (hn' _ _ (he _ hu')) (hbp _ _ (hn' _ _ hNw))
      exact (SW.Base.mem_stdL _).1 ((hstd fun i => (s : E) * w i j).1 this) i
    · rw [smul_comm, smul_smul (M : E), mul_inv_cancel₀ hM0, one_smul]
  · rintro ⟨s, hs, hc, y, hy, e1⟩ u hu
    obtain ⟨p, q, hpq⟩ : IsCoprime (s : ℤ) (M : ℤ) := Nat.isCoprime_iff_coprime.2 hc
    have hpq' : (p : R) * s + q * M = 1 := by exact_mod_cast congrArg (Int.cast : ℤ → R) hpq
    have hzH : m *ᵥ u - u ∈ H := H.sub_mem (hmH u hu) hu
    have e2 : (s : R) • ((δ - 1).map ι *ᵥ u) = (M : R) • (y.map ι *ᵥ u) := by
      rw [← Matrix.smul_mulVec, ← Matrix.smul_mulVec]
      congr 1
      ext i j
      have := congrArg ι (congrFun (congrFun e1 i) j)
      simpa using this
    have e3 := hz u
    generalize m *ᵥ u - u = z at *
    refine ⟨(p : R) • e • (y.map ι *ᵥ u) + (p : R) • (s : R) • b • z + (q : R) • z,
      H.add_mem (H.add_mem (hn _ _ (he _ (hint y hy u hu))) (hn _ _ (hn' _ _ (hb' _ hzH)))) (hn _ _ hzH), ?_⟩
    funext i
    have a2 := congrFun e2 i
    have a3 := congrFun e3 i
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul, nsmul_eq_mul] at a2 a3 ⊢
    linear_combination (-z i) * hpq' - (p * s * z i) * h1 + (p * s) * a3 + (p * e) * a2

end Generic

section Adelic

variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {k : ℕ}

/- English proof (translation)
The claim follows from `AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩`.
-/
theorem tmul_mem {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {x : Fin k → E} (hx : x ∈ L) : (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L :=
  AddSubgroup.subset_closure ⟨a, ha, x, hx, rfl⟩

/- English proof (translation)
Establish `: latHat F E L ≤ (latHat F E L').comap f`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨a, ha, x, hx, rfl⟩`. Conclude with `h a ha x hx`. Conclude with `this hu`.
-/
theorem map_mem_latHat {L L' : Set (Fin k → E)} (f : (Fin k → Af F ⊗[F] E) →+ (Fin k → Af F ⊗[F] E))
    (h : ∀ a ∈ intAf F, ∀ x ∈ L, f (fun i => a ⊗ₜ[F] x i) ∈ latHat F E L') {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E L) : f u ∈ latHat F E L' := by
  have : latHat F E L ≤ (latHat F E L').comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨a, ha, x, hx, rfl⟩
    exact h a ha x hx
  exact this hu

/- English proof (translation)
Use `map_mem_latHat ((AddMonoidHom.mulLeft (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E)).compLeft _) (fun b hb x hx => ?_) hu` and prove the remaining obligations. Establish `: a * b ∈ intAf F` using `fun v => by rw [map_mul]; exact mul_mem (ha v) (hb v)`. Use `tmul_mem this hx using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `(a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E) * b ⊗ₜ[F] x i = _`.

Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem mul_mem_latHat {L : Set (Fin k → E)} {a : Af F} (ha : a ∈ intAf F)
    {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    (fun i => (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E) * u i) ∈ latHat F E L := by
  refine map_mem_latHat ((AddMonoidHom.mulLeft (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E)).compLeft _)
    (fun b hb x hx => ?_) hu
  have : a * b ∈ intAf F := fun v => by rw [map_mul]; exact mul_mem (ha v) (hb v)
  convert tmul_mem this hx using 1
  funext i
  change (a ⊗ₜ[F] (1 : E) : Af F ⊗[F] E) * b ⊗ₜ[F] x i = _
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Use `map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom (fun b hb x hx => ?_) hu` and prove the remaining obligations. Use `tmul_mem hb (h x hx) using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Express the relevant statement in the definitionally equal form `∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j`. Rewrite using `[TensorProduct.tmul_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, one_mul]`.
-/
theorem mulVec_mem_latHat {L L' : Set (Fin k → E)} {δ : Matrix (Fin k) (Fin k) E}
    (h : ∀ v ∈ L, δ *ᵥ v ∈ L') {u : Fin k → Af F ⊗[F] E} (hu : u ∈ latHat F E L) :
    δ.map (inclR (F := F) (Af F)) *ᵥ u ∈ latHat F E L' := by
  refine map_mem_latHat (Matrix.mulVecLin (δ.map (inclR (F := F) (Af F)))).toAddMonoidHom
    (fun b hb x hx => ?_) hu
  convert tmul_mem hb (h x hx) using 1
  funext i
  change ∑ j, ((1 : Af F) ⊗ₜ[F] δ i j : Af F ⊗[F] E) * b ⊗ₜ[F] x j = b ⊗ₜ[F] ∑ j, δ i j * x j
  rw [TensorProduct.tmul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [Algebra.TensorProduct.tmul_mul_tmul, one_mul]

/- English proof (translation)
Use `map_mem_latHat ((sigR (Af F) σ).toAddMonoidHom.compLeft _) (fun b hb x hx => ?_) hu` and prove the remaining obligations. Establish `hx' : (fun i => σ (x i)) ∈ stdL E k`. Rewrite `hx` using `[SetLike.mem_coe]`. Rewrite `hx`, the goal using `[SW.Base.mem_stdL]`. Conclude with `fun a => (hx a).map (σ : E →+* E).toIntAlgHom`.

Conclude with `tmul_mem hb hx'`.
-/
theorem conj_mem_latHat [NumberField E] (σ : E →ₐ[F] E) {u : Fin k → Af F ⊗[F] E}
    (hu : u ∈ latHat F E (stdL E k : Set (Fin k → E))) :
    (fun i => sigR (Af F) σ (u i)) ∈ latHat F E (stdL E k : Set (Fin k → E)) := by
  refine map_mem_latHat ((sigR (Af F) σ).toAddMonoidHom.compLeft _) (fun b hb x hx => ?_) hu
  have hx' : (fun i => σ (x i)) ∈ stdL E k := by
    rw [SetLike.mem_coe] at hx
    rw [SW.Base.mem_stdL] at hx ⊢
    exact fun a => (hx a).map (σ : E →+* E).toIntAlgHom
  exact tmul_mem hb hx'

/- English proof (translation)
Use `congrArg φ h` as an intermediate fact. Rewrite `this` using `[map_mul, map_zero, Matrix.sub_apply, map_sub, mul_sub, sub_eq_zero]`. Rewrite using `[this]`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality.

Simplify using `only [Matrix.one_apply_eq, map_one]`. Simplify using `only [Matrix.one_apply_ne hij, map_zero]`.
-/
theorem idem_sub {R R' : Type} [CommRing R] [CommRing R'] (φ : R →+* R') {ε : R}
    {m : Matrix (Fin k) (Fin k) R} {i j : Fin k} (h : ε * (m - 1) i j = 0) :
    φ ε * φ (m i j) = φ ε * (1 : Matrix (Fin k) (Fin k) R') i j := by
  have := congrArg φ h
  rw [map_mul, map_zero, Matrix.sub_apply, map_sub, mul_sub, sub_eq_zero] at this
  rw [this]
  by_cases hij : i = j
  · subst hij; simp only [Matrix.one_apply_eq, map_one]
  · simp only [Matrix.one_apply_ne hij, map_zero]

end Adelic

end GlobalTheory.Ker.DCos

end
