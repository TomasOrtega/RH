import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.MulDefs
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddLaw
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.AddDbl
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GaloisTorsionConjugacy.WpOnto

noncomputable section

namespace PI.GalTorsConj.W

open Formalism.L2.Th1.F

def Cj1 (M₁ : IntermediateField ℚ ℂ) (ρ₁ : M₁ →ₐ[ℚ] ℂ) (x x' : ℂ) : Prop :=
  ∃ hx : x ∈ M₁, ρ₁ ⟨x, hx⟩ = x'

section cj1

variable {M₁ : IntermediateField ℚ ℂ} {ρ₁ : M₁ →ₐ[ℚ] ℂ}

/- English proof (translation)
Take `⟨hx, rfl⟩` from `h`. Take `⟨hy, rfl⟩` from `k`. Use `⟨M₁.add_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_add]`. Both sides reduce to the same expression.
-/
theorem conj_add_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x + y) (x' + y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.add_mem hx hy, ?_⟩
  rw [← map_add]
  rfl

/- English proof (translation)
Take `⟨hx, rfl⟩` from `h`. Take `⟨hy, rfl⟩` from `k`. Use `⟨M₁.sub_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_sub]`. Both sides reduce to the same expression.
-/
theorem conj_sub_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x - y) (x' - y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.sub_mem hx hy, ?_⟩
  rw [← map_sub]
  rfl

/- English proof (translation)
Take `⟨hx, rfl⟩` from `h`. Take `⟨hy, rfl⟩` from `k`. Use `⟨M₁.mul_mem hx hy, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul]`. Both sides reduce to the same expression.
-/
theorem conj_mul_alt {x x' y y' : ℂ} (h : Cj1 M₁ ρ₁ x x') (k : Cj1 M₁ ρ₁ y y') :
    Cj1 M₁ ρ₁ (x * y) (x' * y') := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hy, rfl⟩ := k
  refine ⟨M₁.mul_mem hx hy, ?_⟩
  rw [← map_mul]
  rfl

/- English proof (translation)
Take `⟨hx, rfl⟩` from `h`. Use `⟨pow_mem hx n, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_pow]`. Both sides reduce to the same expression.
-/
theorem conj_pow_alt {x x' : ℂ} (h : Cj1 M₁ ρ₁ x x') (n : ℕ) : Cj1 M₁ ρ₁ (x ^ n) (x' ^ n) := by
  obtain ⟨hx, rfl⟩ := h
  refine ⟨pow_mem hx n, ?_⟩
  rw [← map_pow]
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨IntermediateField.natCast_mem M₁ n, by rw [show (⟨(n : ℂ), IntermediateField.natCast_mem M₁ n⟩ : M₁) = (n : M₁) from Subtype.ext (by simp), map_natCast]⟩`.
-/
theorem conj_natCast_alt (n : ℕ) : Cj1 M₁ ρ₁ (n : ℂ) (n : ℂ) :=
  ⟨IntermediateField.natCast_mem M₁ n, by
    rw [show (⟨(n : ℂ), IntermediateField.natCast_mem M₁ n⟩ : M₁) = (n : M₁) from
      Subtype.ext (by simp), map_natCast]⟩

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty`. Simplify using `only [Finset.sum_empty]`. Conclude with `⟨M₁.zero_mem, map_zero ρ₁⟩`. Consider the case `insert a s ha ih`.

Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha]`. Conclude with `conj_add_alt (h a (Finset.mem_insert_self a s)) (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem conj_sum_alt {ι : Type*} (s : Finset ι) (f f' : ι → ℂ) (h : ∀ i ∈ s, Cj1 M₁ ρ₁ (f i) (f' i)) :
    Cj1 M₁ ρ₁ (∑ i ∈ s, f i) (∑ i ∈ s, f' i) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    simp only [Finset.sum_empty]
    exact ⟨M₁.zero_mem, map_zero ρ₁⟩
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact conj_add_alt (h a (Finset.mem_insert_self a s))
      (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Take `⟨hx, rfl⟩` from `h`. Take `⟨hx', rfl⟩` from `k`. Both sides reduce to the same expression.
-/
theorem conj_unique_alt {x a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ x b) : a = b := by
  obtain ⟨hx, rfl⟩ := h
  obtain ⟨hx', rfl⟩ := k
  rfl

/- English proof (translation)
Substitute `e` using the available equality. Conclude with `conj_unique_alt h k`.
-/
theorem conj_eq_alt {x y a b : ℂ} (h : Cj1 M₁ ρ₁ x a) (k : Cj1 M₁ ρ₁ y b) (e : x = y) : a = b := by
  subst e
  exact conj_unique_alt h k

/- English proof (translation)
Break down `h with ⟨a, -⟩ | ⟨-, -, hx, hy, e1, e2⟩` into its components or cases. Conclude with `absurd a ht`. Conclude with `⟨⟨hx, e1.symm⟩, ⟨hy, e2.symm⟩⟩`.
-/
theorem conj_weierstrassP {L L' : PeriodPair} {t t' : ℂ} (h : St L L' M₁ ρ₁ t t') (ht : t ∉ L.lattice) :
    Cj1 M₁ ρ₁ (L.weierstrassP t) (L'.weierstrassP t') ∧
      Cj1 M₁ ρ₁ (L.derivWeierstrassP t) (L'.derivWeierstrassP t') := by
  rcases h with ⟨a, -⟩ | ⟨-, -, hx, hy, e1, e2⟩
  · exact absurd a ht
  · exact ⟨⟨hx, e1.symm⟩, ⟨hy, e2.symm⟩⟩

end cj1

/- English proof (translation)
Take `⟨t, n, ht, hn, -⟩` from `mulStableIntegral L c hc`. Establish `hn0 : (0 : ℝ) < (n : ℝ)`. Establish `h1 : (n : ℂ) = (Complex.normSq c : ℂ)` using `by rw [← hn, Complex.mul_conj]`. Establish `h2 : (n : ℝ) = Complex.normSq c` using `by exact_mod_cast h1`. Rewrite using `[h2]`.

Conclude with `Complex.normSq_pos.mpr hc0`. Establish `hn0' : 0 < n` using `by exact_mod_cast hn0`. Use `⟨n.toNat, by omega, ?_⟩` and prove the remaining obligations. Establish `e : ((n.toNat : ℕ) : ℂ) * P = (t : ℤ) • (c * P) - c * (c * P)`. Establish `: ((n.toNat : ℕ) : ℂ) = (n : ℂ)`.

Establish `: ((n.toNat : ℤ)) = n` using `Int.toNat_of_nonneg hn0'.le`. Conclude with `this` after adjusting the coercions. Rewrite using `[this, ← hn, zsmul_eq_mul]`. Establish `hconj : (starRingEnd ℂ) c = (t : ℂ) - c` using `by rw [← ht]; ring`. Rewrite using `[hconj]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`. Conclude with `L.lattice.sub_mem (L.lattice.smul_mem _ hP) (hc _ hP)`.
-/
theorem tors_of_ker {L : PeriodPair} {c P : ℂ} (hc0 : c ≠ 0) (hc : MulStable L c)
    (hP : c * P ∈ L.lattice) : ∃ m : ℕ, 0 < m ∧ (m : ℂ) * P ∈ L.lattice := by
  obtain ⟨t, n, ht, hn, -⟩ := mulStableIntegral L c hc
  have hn0 : (0 : ℝ) < (n : ℝ) := by
    have h1 : (n : ℂ) = (Complex.normSq c : ℂ) := by rw [← hn, Complex.mul_conj]
    have h2 : (n : ℝ) = Complex.normSq c := by exact_mod_cast h1
    rw [h2]
    exact Complex.normSq_pos.mpr hc0
  have hn0' : 0 < n := by exact_mod_cast hn0
  refine ⟨n.toNat, by omega, ?_⟩
  have e : ((n.toNat : ℕ) : ℂ) * P = (t : ℤ) • (c * P) - c * (c * P) := by
    have : ((n.toNat : ℕ) : ℂ) = (n : ℂ) := by
      have : ((n.toNat : ℤ)) = n := Int.toNat_of_nonneg hn0'.le
      exact_mod_cast this
    rw [this, ← hn, zsmul_eq_mul]
    have hconj : (starRingEnd ℂ) c = (t : ℂ) - c := by rw [← ht]; ring
    rw [hconj]
    ring
  rw [e]
  exact L.lattice.sub_mem (L.lattice.smul_mem _ hP) (hc _ hP)

/- English proof (translation)
Introduce `hcz`. Take `⟨Q, hQ, hzQ⟩` from `hS.2.2 z hcz hz`. Establish `h1 : c * (-Q) ∈ L.lattice`. Rewrite using `[mul_neg]`. Conclude with `L.lattice.neg_mem (hS.1 Q hQ).1`.

Establish `h2 : -Q ∉ L.lattice` using `fun h => (hS.1 Q hQ).2 (by simpa using L.lattice.neg_mem h)`. Take `⟨P, hP, hQP⟩` from `hS.2.2 (-Q) h1 h2`. Apply `hzP P hP` to reduce the goal to its premises. Use `L.lattice.sub_mem hzQ hQP` as an intermediate fact. Rewrite `this` using `[show z - Q - (-Q - P) = z + P by ring]`. Then use the resulting hypothesis.
-/
theorem mul_notMem {L : PeriodPair} {c z : ℂ} {S : Finset ℂ} (hS : IsKerReps L c S)
    (hz : z ∉ L.lattice) (hzP : ∀ P ∈ S, z + P ∉ L.lattice) :
    c * z ∉ L.lattice := by
  intro hcz
  obtain ⟨Q, hQ, hzQ⟩ := hS.2.2 z hcz hz
  have h1 : c * (-Q) ∈ L.lattice := by
    rw [mul_neg]; exact L.lattice.neg_mem (hS.1 Q hQ).1
  have h2 : -Q ∉ L.lattice := fun h => (hS.1 Q hQ).2 (by simpa using L.lattice.neg_mem h)
  obtain ⟨P, hP, hQP⟩ := hS.2.2 (-Q) h1 h2
  apply hzP P hP
  have := L.lattice.sub_mem hzQ hQP
  rwa [show z - Q - (-Q - P) = z + P by ring] at this

/- English proof (translation)
Establish `e : veluU L S = {z | z ∉ L.lattice} ∩ ⋂ P ∈ S, {z | z + P ∉ L.lattice}`. Use extensionality with `z`. Simplify using `[veluU]`. Rewrite using `[e]`. Use `IsOpen.inter L.isClosed_lattice.isOpen_compl (isOpen_biInter_finset fun P _ => ?_)` and prove the remaining obligations.

Conclude with `L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)`.
-/
theorem isOpen_veluU (L : PeriodPair) (S : Finset ℂ) : IsOpen (veluU L S) := by
  have e : veluU L S = {z | z ∉ L.lattice} ∩ ⋂ P ∈ S, {z | z + P ∉ L.lattice} := by
    ext z; simp [veluU]
  rw [e]
  refine IsOpen.inter L.isClosed_lattice.isOpen_compl (isOpen_biInter_finset fun P _ => ?_)
  exact L.isClosed_lattice.isOpen_compl.preimage (continuous_id.add continuous_const)

/- English proof (translation)
Introduce `z hz`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Establish `h0 : ContinuousAt L.weierstrassP z` using `(L.analyticOnNhd_weierstrassP z hz.1).continuousAt`. Establish `hs : ContinuousAt (fun z => ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)) z`. Establish `: ∀ P ∈ S, ContinuousAt (fun z => L.weierstrassP (z + P) - L.weierstrassP P) z`.

Introduce `P hP`. Establish `h1 : ContinuousAt L.weierstrassP (z + P)` using `(L.analyticOnNhd_weierstrassP _ (hz.2 P hP)).continuousAt`. Establish `h2 : ContinuousAt (fun z => L.weierstrassP (z + P)) z` using `ContinuousAt.comp (g := L.weierstrassP) (f := fun x => x + P) (x := z) h1 (continuous_add_const P).continuousAt`. Conclude with `h2.sub continuousAt_const`. Conclude with `tendsto_finsetSum S this`.

Conclude with `h0.add hs`.
-/
theorem continuousOn_veluF (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluF L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.weierstrassP z := (L.analyticOnNhd_weierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, (L.weierstrassP (z + P) - L.weierstrassP P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.weierstrassP (z + P) - L.weierstrassP P) z := by
      intro P hP
      have h1 : ContinuousAt L.weierstrassP (z + P) :=
        (L.analyticOnNhd_weierstrassP _ (hz.2 P hP)).continuousAt
      have h2 : ContinuousAt (fun z => L.weierstrassP (z + P)) z :=
        ContinuousAt.comp (g := L.weierstrassP) (f := fun x => x + P) (x := z) h1
          (continuous_add_const P).continuousAt
      exact h2.sub continuousAt_const
    exact tendsto_finsetSum S this
  exact h0.add hs

/- English proof (translation)
Introduce `z hz`. Apply `ContinuousAt.continuousWithinAt` to reduce the goal to its premises. Establish `h0 : ContinuousAt L.derivWeierstrassP z` using `(L.analyticOnNhd_derivWeierstrassP z hz.1).continuousAt`. Establish `hs : ContinuousAt (fun z => ∑ P ∈ S, L.derivWeierstrassP (z + P)) z`. Establish `: ∀ P ∈ S, ContinuousAt (fun z => L.derivWeierstrassP (z + P)) z`.

Introduce `P hP`. Establish `h1 : ContinuousAt L.derivWeierstrassP (z + P)` using `(L.analyticOnNhd_derivWeierstrassP _ (hz.2 P hP)).continuousAt`. Conclude with `ContinuousAt.comp (g := L.derivWeierstrassP) (f := fun x => x + P) (x := z) h1 (continuous_add_const P).continuousAt`. Conclude with `tendsto_finsetSum S this`. Conclude with `h0.add hs`.
-/
theorem continuousOn_veluD (L : PeriodPair) (S : Finset ℂ) :
    ContinuousOn (veluD L S) (veluU L S) := by
  intro z hz
  apply ContinuousAt.continuousWithinAt
  have h0 : ContinuousAt L.derivWeierstrassP z :=
    (L.analyticOnNhd_derivWeierstrassP z hz.1).continuousAt
  have hs : ContinuousAt (fun z => ∑ P ∈ S, L.derivWeierstrassP (z + P)) z := by
    have : ∀ P ∈ S, ContinuousAt (fun z => L.derivWeierstrassP (z + P)) z := by
      intro P hP
      have h1 : ContinuousAt L.derivWeierstrassP (z + P) :=
        (L.analyticOnNhd_derivWeierstrassP _ (hz.2 P hP)).continuousAt
      exact ContinuousAt.comp (g := L.derivWeierstrassP) (f := fun x => x + P) (x := z) h1
        (continuous_add_const P).continuousAt
    exact tendsto_finsetSum S this
  exact h0.add hs

end PI.GalTorsConj.W

end
