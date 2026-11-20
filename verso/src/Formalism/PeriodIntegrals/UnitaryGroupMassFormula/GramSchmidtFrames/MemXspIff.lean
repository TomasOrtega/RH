import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.GramSchmidtFrames.HmSelfRe

open MeasureTheory Formalism.REAL Formalism.QuantumDeterminants Formalism.FourierDecayAlt Formalism.FourierDecayAlt.C6
open Matrix

noncomputable section

namespace PI.UnitaryGroupMassFormula.GsFr
open PI.UnitaryGroupMassFormula.DLm.Gram

def SatOm : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW k r z z' (n * y * n') = omW k r z z' y

def SatOm' : Prop :=
  ∀ (k r : ℕ) (z z' : Fin (2 * r + k + 1) → ℂ), 1 ≤ k → 1 ≤ r → C2.StdZ k r z → C2.StdZ k r z' →
    ∀ y ∈ B.GV k r, 0 < Gf k r z z' y → ∀ n ∈ Nset k r, ∀ n' ∈ Nset k r,
      omW' k r z z' (n * y * n') = omW' k r z z' y

section lemmas

variable {k r : ℕ}

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `hv`. Proceed by induction on `hv using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨a, rfl⟩` from `hx`.

Introduce `i hi`. Simplify using `only [bvec, Pi.single_apply]`. Rewrite using `[if_neg]`. Introduce `h`. Establish `ha` using `a.isLt`.

Rewrite `hi` using `[h]`. Simplify using `only [eI] at hi`. Use linear arithmetic over natural numbers and integers. Consider the case `zero => intro i _`. Both sides reduce to the same expression.

Consider the case `add x y _ _ hx hy => intro i hi`. Simplify using `[hx i hi, hy i hi]`. Consider the case `smul c x _ hx => intro i hi`. Simplify using `[hx i hi]`. Introduce `hv`.

Establish `hsum : v = ∑ a : Fin r, v (eI k r a) • bvec (eI k r a)`. Use function extensionality and compare the values at `i`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]`. Distinguish the cases in `hi : i.val < r`. Rewrite using `[Finset.sum_eq_single ⟨i.val, hi⟩]`.

Establish `he : i = eI k r ⟨i.val, hi⟩` using `by ext; rfl`. Rewrite using `[if_pos he, ← he]`. Introduce `b _ hb`. Rewrite using `[if_neg]`. Introduce `h`.

Apply `hb` to reduce the goal to its premises. Use `ext`. Use `show b.val = i.val`. Establish `h2` using `congrArg Fin.val h`. Simplify using `only [eI] at h2`.

Use linear arithmetic over natural numbers and integers. Simplify using the standard rewrite rules. Rewrite using `[hv i (by omega)]`. Use `(Finset.sum_eq_zero fun b _ => ?_).symm` and prove the remaining obligations. Rewrite using `[if_neg]`.

Introduce `h`. Establish `hb` using `b.isLt`. Rewrite `hi` using `[h]`. Simplify using `only [eI] at hi`. Use linear arithmetic over natural numbers and integers.

Rewrite using `[hsum]`. Conclude with `Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)`.
-/
lemma mem_Xsp_iff (v : Fin (2 * r + k + 1) → ℂ) : v ∈ Xsp k r ↔ ∀ i : Fin (2 * r + k + 1), r ≤ i.val → v i = 0 := by
  constructor
  · intro hv
    induction hv using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨a, rfl⟩ := hx
      intro i hi
      simp only [bvec, Pi.single_apply]
      rw [if_neg]
      intro h
      have ha := a.isLt
      rw [h] at hi
      simp only [eI] at hi
      omega
    | zero => intro i _; rfl
    | add x y _ _ hx hy => intro i hi; simp [hx i hi, hy i hi]
    | smul c x _ hx => intro i hi; simp [hx i hi]
  · intro hv
    have hsum : v = ∑ a : Fin r, v (eI k r a) • bvec (eI k r a) := by
      funext i
      simp only [Finset.sum_apply, Pi.smul_apply, bvec, Pi.single_apply, smul_eq_mul, mul_ite, mul_one, mul_zero]
      by_cases hi : i.val < r
      · rw [Finset.sum_eq_single ⟨i.val, hi⟩]
        · have he : i = eI k r ⟨i.val, hi⟩ := by ext; rfl
          rw [if_pos he, ← he]
        · intro b _ hb
          rw [if_neg]
          intro h
          apply hb
          ext
          show b.val = i.val
          have h2 := congrArg Fin.val h
          simp only [eI] at h2
          omega
        · simp
      · rw [hv i (by omega)]
        refine (Finset.sum_eq_zero fun b _ => ?_).symm
        rw [if_neg]
        intro h
        have hb := b.isLt
        rw [h] at hi
        simp only [eI] at hi
        omega
    rw [hsum]
    exact Submodule.sum_mem _ fun a _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨a, rfl⟩)

/- English proof (translation)
Rewrite `hv`, the goal using `[mem_Xsp_iff]`. Introduce `i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : r ≤ j.val`.

Rewrite using `[hv j hj, mul_zero]`. Use `push_neg at hj`. Establish `h1` using `hn.2.1 ⟨j.val, hj⟩ i (by simp only; omega)`. Establish `hjeq : eI k r ⟨j.val, hj⟩ = j` using `by ext; rfl`. Rewrite `h1` using `[hjeq]`.

Rewrite using `[h1, if_neg (by intro h; rw [h] at hi; omega), zero_mul]`.
-/
lemma N_Xsp {n : B.Mat k r} (hn : n ∈ Nset k r) {v : Fin (2 * r + k + 1) → ℂ} (hv : v ∈ Xsp k r) :
    n *ᵥ v ∈ Xsp k r := by
  rw [mem_Xsp_iff] at hv ⊢
  intro i hi
  simp only [Matrix.mulVec, dotProduct]
  refine Finset.sum_eq_zero fun j _ => ?_
  by_cases hj : r ≤ j.val
  · rw [hv j hj, mul_zero]
  · push_neg at hj
    have h1 := hn.2.1 ⟨j.val, hj⟩ i (by simp only; omega)
    have hjeq : eI k r ⟨j.val, hj⟩ = j := by ext; rfl
    rw [hjeq] at h1
    rw [h1, if_neg (by intro h; rw [h] at hi; omega), zero_mul]

/- English proof (translation)
Rewrite using `[mem_Xsp_iff]`. Introduce `i hi`. Simplify using `only [Pi.sub_apply, Matrix.mulVec, dotProduct]`. Rewrite using `[sub_eq_zero, Finset.sum_eq_single i]`. Distinguish the cases in `hmid : i.val ≤ r + k`.

Rewrite using `[hn.2.2 i i hi hmid hi, if_pos rfl, one_mul]`. Rewrite using `[hu i (Or.inr (by omega)), mul_zero]`. Introduce `j _ hji`. Distinguish the cases in `hj : r ≤ j.val ∧ j.val ≤ r + k`. Rewrite using `[hn.2.2 i j hj.1 hj.2 hi, if_neg (Ne.symm hji), zero_mul]`.

Rewrite using `[hu j (by omega), mul_zero]`. Simplify using the standard rewrite rules.
-/
lemma N_wb {n : B.Mat k r} (hn : n ∈ Nset k r) {u : Fin (2 * r + k + 1) → ℂ} (hu : inWb k r u) :
    n *ᵥ u - u ∈ Xsp k r := by
  rw [mem_Xsp_iff]
  intro i hi
  simp only [Pi.sub_apply, Matrix.mulVec, dotProduct]
  rw [sub_eq_zero, Finset.sum_eq_single i]
  · by_cases hmid : i.val ≤ r + k
    · rw [hn.2.2 i i hi hmid hi, if_pos rfl, one_mul]
    · rw [hu i (Or.inr (by omega)), mul_zero]
  · intro j _ hji
    by_cases hj : r ≤ j.val ∧ j.val ≤ r + k
    · rw [hn.2.2 i j hj.1 hj.2 hi, if_neg (Ne.symm hji), zero_mul]
    · rw [hu j (by omega), mul_zero]
  · simp

end lemmas

/- English proof (translation)
Introduce `k r z z' hk hr hz hz' D0 y hy n hn n' hn'`. Take `⟨hyG, hyP, ⟨t, ht, hom⟩, ⟨t', ht', hom'⟩, hiso⟩` from `hy`. Establish `Nc` using `Formalism.FourierDecayAlt.P.unipotent_radical_closed k r`. Establish `hSn : n ∈ Sset k r z` using `⟨1, one_mem_UW z, n, hn, (one_mul n).symm⟩`. Establish `hSn' : n' ∈ Sset k r z'` using `⟨1, one_mem_UW z', n', hn', (one_mul n').symm⟩`.

Establish `hGV : n * y * n' ∈ B.GV k r`. Establish `h1` using `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn.1 hyG`. Conclude with `Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul h1 hn'.1`. Establish `hGf : Gf k r z z' (n * y * n') = Gf k r z z' y`. Simplify using `only [Gf, Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz.1 hz'.1 n hSn n' hSn' y]`.

Use `⟨hGV, by rw [hGf]; exact hyP, ⟨t, ht, ?_⟩, ⟨t', ht', ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hO k r z z' hk hr hz hz' y hyG hyP n hn n' hn']`. Conclude with `hom`. Rewrite using `[hO' k r z z' hk hr hz hz' y hyG hyP n hn n' hn']`. Conclude with `hom'`.

Introduce `u hu`. Establish `hUw : inWb k r u` using `((D0.isotropic_subspace_eq_primed u).1 hu).1.1`. Take `⟨v, hv, v', hv', he⟩` from `hiso u hu`. Establish `hni` using `Nc.inv_mem n' hn'`. Establish `hnu` using `Nc.unit n' hn'`.

Use `⟨n *ᵥ (u + v) - u, ?_, n'⁻¹ *ᵥ (u + v') - u, ?_, ?_⟩` and prove the remaining obligations. Establish `: n *ᵥ (u + v) - u = (n *ᵥ u - u) + n *ᵥ v` using `by rw [mulVec_add]; abel`. Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (N_wb hn hUw) (N_Xsp hn hv)`. Establish `: n'⁻¹ *ᵥ (u + v') - u = (n'⁻¹ *ᵥ u - u) + n'⁻¹ *ᵥ v'` using `by rw [mulVec_add]; abel`.

Rewrite using `[this]`. Conclude with `Submodule.add_mem _ (N_wb hni hUw) (N_Xsp hni hv')`. Establish `e1 : u + (n'⁻¹ *ᵥ (u + v') - u) = n'⁻¹ *ᵥ (u + v')` using `by abel`. Rewrite using `[e1, ← mulVec_mulVec, ← mulVec_mulVec, show n' *ᵥ (n'⁻¹ *ᵥ (u + v')) = u + v' by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hnu, one_mulVec], he]`. Normalize the expressions using the abelian group laws.
-/
theorem gfSat_of (hO : SatOm) (hO' : SatOm') : GfSat := by
  intro k r z z' hk hr hz hz' D0 y hy n hn n' hn'
  obtain ⟨hyG, hyP, ⟨t, ht, hom⟩, ⟨t', ht', hom'⟩, hiso⟩ := hy
  have Nc := Formalism.FourierDecayAlt.P.unipotent_radical_closed k r
  have hSn : n ∈ Sset k r z := ⟨1, one_mem_UW z, n, hn, (one_mul n).symm⟩
  have hSn' : n' ∈ Sset k r z' := ⟨1, one_mem_UW z', n', hn', (one_mul n').symm⟩
  have hGV : n * y * n' ∈ B.GV k r := by
    have h1 := Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul hn.1 hyG
    exact Formalism.QuantumDeterminants.WeylGroupFacts.uh_mul h1 hn'.1
  have hGf : Gf k r z z' (n * y * n') = Gf k r z z' y := by
    simp only [Gf, Formalism.QuantumDeterminants.diagonal_inverse_holds k r z z' hz.1 hz'.1 n hSn n' hSn' y]
  refine ⟨hGV, by rw [hGf]; exact hyP, ⟨t, ht, ?_⟩, ⟨t', ht', ?_⟩, ?_⟩
  · rw [hO k r z z' hk hr hz hz' y hyG hyP n hn n' hn']; exact hom
  · rw [hO' k r z z' hk hr hz hz' y hyG hyP n hn n' hn']; exact hom'
  · intro u hu
    have hUw : inWb k r u := ((D0.isotropic_subspace_eq_primed u).1 hu).1.1
    obtain ⟨v, hv, v', hv', he⟩ := hiso u hu
    have hni := Nc.inv_mem n' hn'
    have hnu := Nc.unit n' hn'
    refine ⟨n *ᵥ (u + v) - u, ?_, n'⁻¹ *ᵥ (u + v') - u, ?_, ?_⟩
    · have : n *ᵥ (u + v) - u = (n *ᵥ u - u) + n *ᵥ v := by rw [mulVec_add]; abel
      rw [this]
      exact Submodule.add_mem _ (N_wb hn hUw) (N_Xsp hn hv)
    · have : n'⁻¹ *ᵥ (u + v') - u = (n'⁻¹ *ᵥ u - u) + n'⁻¹ *ᵥ v' := by rw [mulVec_add]; abel
      rw [this]
      exact Submodule.add_mem _ (N_wb hni hUw) (N_Xsp hni hv')
    · have e1 : u + (n'⁻¹ *ᵥ (u + v') - u) = n'⁻¹ *ᵥ (u + v') := by abel
      rw [e1, ← mulVec_mulVec, ← mulVec_mulVec,
        show n' *ᵥ (n'⁻¹ *ᵥ (u + v')) = u + v' by rw [mulVec_mulVec, Matrix.mul_nonsing_inv _ hnu, one_mulVec], he]
      abel

end PI.UnitaryGroupMassFormula.GsFr
