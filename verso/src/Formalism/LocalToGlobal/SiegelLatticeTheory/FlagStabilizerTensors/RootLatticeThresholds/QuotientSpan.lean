import Formalism.LocalToGlobal.SiegelLatticeTheory.CokernelGLCounts.RankPointCounts.RootCoordinatesIndex
import Formalism.LocalToGlobal.SiegelLatticeTheory.FlagStabilizerTensors.RootLatticeThresholds.HermitianMatrixIdentities

noncomputable section

open scoped Classical
open MeasureTheory NumberField Matrix Formalism.BasicNotions Formalism.MainNotions.S Formalism.L2.SG.HidaSetting Formalism.L2.SG.LocWSOf

namespace Formalism.L2.SG.QuotientSpan

attribute [local instance] Formalism.BasicNotions.Host.cmStar

variable {D : D7} {X : HidaSetting D} (v : InfinitePlace X.B.I.F) {lam : ℂ} (hl : lam ≠ 0)
  {Q : Matrix (Fin X.B.I.n) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ} {Qi : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin X.B.I.n) ℂ}
  (hT : IsTranspC X v lam D.R.k D.R.rS Q Qi)

abbrev eV (a : Fin D.R.rS) : Fin X.B.I.n → ℂ := rv X.B.I v (X.eR a)

include hT in
/- English proof (translation)
The claim follows from `(hT.2.2.2 a a rfl).1`.
-/
theorem Q_e (a : Fin D.R.rS) :
    Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = lam ^ (D.R.rS - a.val) • eV v a :=
  (hT.2.2.2 a a rfl).1

include hT hl in
/- English proof (translation)
Establish `h` using `congrArg (fun x => Qi *ᵥ x) (Q_e v hT a)`. Simplify using `only [Matrix.mulVec_mulVec, hT.1, Matrix.one_mulVec, Matrix.mulVec_smul] at h`. Rewrite using `[h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]`.
-/
theorem Qi_e (a : Fin D.R.rS) :
    Qi *ᵥ eV v a = (lam ^ (D.R.rS - a.val))⁻¹ • Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 := by
  have h := congrArg (fun x => Qi *ᵥ x) (Q_e v hT a)
  simp only [Matrix.mulVec_mulVec, hT.1, Matrix.one_mulVec, Matrix.mulVec_smul] at h
  rw [h, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]

include hT hl in
/- English proof (translation)
Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx'`. Take `⟨b, hb, rfl⟩` from `hx'`. Rewrite using `[Qi_e v hl hT, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]`. Introduce `h`.

Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Formalism.QuantumDeterminants.eI] at this`. Simplify using `only [Set.mem_setOf_eq] at hb`. Use linear arithmetic over natural numbers and integers. Consider the case `zero => simp`.

Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]`.
-/
theorem Qi_spanLt (a : ℕ) (x : Fin X.B.I.n → ℂ) (hx : x ∈ spanLt (eV (X := X) v) a) (i : Fin (2 * D.R.rS + D.R.k + 1))
    (hi : a ≤ i.val) : (Qi *ᵥ x) i = 0 := by
  induction hx using Submodule.span_induction with
  | mem x hx' =>
    obtain ⟨b, hb, rfl⟩ := hx'
    rw [Qi_e v hl hT, Pi.smul_apply, Pi.single_apply, if_neg, smul_zero]
    intro h
    have := congrArg Fin.val h
    simp only [Formalism.QuantumDeterminants.eI] at this
    simp only [Set.mem_setOf_eq] at hb
    omega
  | zero => simp
  | add x y _ _ hx hy => rw [Matrix.mulVec_add, Pi.add_apply, hx, hy, add_zero]
  | smul c x _ hx => rw [Matrix.mulVec_smul, Pi.smul_apply, hx, smul_zero]

include hT in
/- English proof (translation)
Establish `hw' : w = ∑ i, w i • Pi.single i (1 : ℂ)`. Use extensionality with `j`. Simplify using `[Finset.sum_apply, Pi.single_apply]`. Rewrite using `[hw', Matrix.mulVec_sum]`. Use `Submodule.sum_mem _ fun i _ => ?_` and prove the remaining obligations.

Distinguish the cases in `hi : a ≤ i.val`. Rewrite using `[hw i hi, zero_smul, Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`. Establish `hir : i.val < D.R.rS` using `by omega`. Establish `e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩` using `Fin.ext rfl`.

Rewrite using `[Matrix.mulVec_smul, e, Q_e v hT]`. Use `Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))` and prove the remaining obligations. Simplify using `only [Set.mem_setOf_eq]`. Use linear arithmetic over natural numbers and integers.
-/
theorem Q_spanLt (a : ℕ) (ha : a ≤ D.R.rS) (w : Fin (2 * D.R.rS + D.R.k + 1) → ℂ)
    (hw : ∀ i : Fin (2 * D.R.rS + D.R.k + 1), a ≤ i.val → w i = 0) : Q *ᵥ w ∈ spanLt (eV (X := X) v) a := by
  have hw' : w = ∑ i, w i • Pi.single i (1 : ℂ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  rw [hw', Matrix.mulVec_sum]
  refine Submodule.sum_mem _ fun i _ => ?_
  by_cases hi : a ≤ i.val
  · rw [hw i hi, zero_smul, Matrix.mulVec_zero]
    exact Submodule.zero_mem _
  · have hir : i.val < D.R.rS := by omega
    have e : i = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨i.val, hir⟩ := Fin.ext rfl
    rw [Matrix.mulVec_smul, e, Q_e v hT]
    refine Submodule.smul_mem _ _ (Submodule.smul_mem _ _ (Submodule.subset_span ⟨⟨i.val, hir⟩, ?_, rfl⟩))
    simp only [Set.mem_setOf_eq]
    omega

include hT hl in
/- English proof (translation)
Take `⟨_, hQQi, hH, _⟩` from `hT`. Establish `he : eV v a = (lam ^ (D.R.rS - a.val))⁻¹ • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1)`. Rewrite using `[Q_e v ⟨‹_›, hQQi, hH, ‹_›⟩, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]`. Establish `hy : y = Q *ᵥ (Qi *ᵥ y)` using `by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]`. Use `conv_lhs => rw [he, hy]`.

Unfold `hJ`. Rewrite using `[star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH, Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RootCoordinatesIndex.hpk_eI, smul_eq_mul]`.
-/
theorem hJ_e (a : Fin D.R.rS) (y : Fin X.B.I.n → ℂ) :
    hJ (X.B.I.ε v) (eV v a) y = star ((lam ^ (D.R.rS - a.val))⁻¹) * (Qi *ᵥ y) (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) := by
  obtain ⟨_, hQQi, hH, _⟩ := hT
  have he : eV v a = (lam ^ (D.R.rS - a.val))⁻¹ • (Q *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1) := by
    rw [Q_e v ⟨‹_›, hQQi, hH, ‹_›⟩, smul_smul, inv_mul_cancel₀ (pow_ne_zero _ hl), one_smul]
  have hy : y = Q *ᵥ (Qi *ᵥ y) := by rw [Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]
  conv_lhs => rw [he, hy]
  unfold hJ
  rw [star_smul, smul_dotProduct, ← Formalism.L2.SG.Pf.LTL.star_dot_conjT, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hH,
    Pi.star_single, star_one, single_dotProduct, one_mul, Formalism.L2.SG.RootCoordinatesIndex.hpk_eI, smul_eq_mul]

include hT hl in

/- English proof (translation)
Establish `hQiQ` using `hT.1`. Establish `hQQi` using `hT.2.1`. Establish `hH` using `hT.2.2.1`. Establish `hstar_ne : ∀ a : Fin D.R.rS, star ((lam ^ (D.R.rS - a.val))⁻¹) ≠ 0` using `fun a => star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (hl)))`. Establish `hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j, M i j = (M *ᵥ Pi.single j 1) i` using `fun M i j => by rw [Matrix.mulVec_single_one]; rfl`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨hIe, hIz⟩, hperp⟩`. Use `⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩` and prove the remaining obligations. Use `show (Qi * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Qi * g * Q) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS`. Establish `hQiQ' : (Qi)ᴴ * (Q)ᴴ = 1` using `by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]`.

Rewrite using `[← hH]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hcol (Qi * g * Q) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]`. Establish `h1 : (Qi * g * Q) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 = Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 + lam ^ (D.R.rS - a.val) • (Qi *ᵥ ((g - 1) *ᵥ eV v a))`. Rewrite using `[← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e v hT, Matrix.mulVec_smul, Matrix.mulVec_smul, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e v hl hT, smul_sub, smul_smul, mul_inv_cancel₀ (pow_ne_zero _ (hl)), one_smul]`.

Normalize the expressions using the abelian group laws. Rewrite using `[h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt v hl hT a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]`. Rewrite using `[hcol (Qi * g * Q) i j]`. Establish `horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε v) (eV v b) (Q *ᵥ Pi.single j 1) = 0`. Introduce `b`.

Rewrite using `[hJ_e v hl hT, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, if_neg, mul_zero]`. Introduce `h`. Use `congrArg Fin.val h` as an intermediate fact. Simplify using `only [Formalism.QuantumDeterminants.esI] at this`. Use `b.isLt` as an intermediate fact.

Use linear arithmetic over natural numbers and integers. Establish `h1 : (Qi * g * Q) *ᵥ Pi.single j 1 = Pi.single j 1 + Qi *ᵥ ((g - 1) *ᵥ (Q *ᵥ Pi.single j 1))`. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]`. Simplify using `only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h1, Pi.add_apply, Qi_spanLt v hl hT D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]`. Introduce and unpack `⟨_, hce, hcw⟩`. Establish `hg' : g = Q * (Qi * g * Q) * Qi`. Simplify using `only [← Matrix.mul_assoc]`. Rewrite using `[hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]`.

Use `set m := Qi * g * Q with hm`. Establish `key : ∀ x, (g - 1) *ᵥ x = Q *ᵥ ((m - 1) *ᵥ (Qi *ᵥ x))`. Introduce `x`. Use `conv_lhs => rw [hg']`. Rewrite using `[Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]`.

Establish `hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) → ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0`. Introduce `x hx i hi`. Simplify using `only [Matrix.mulVec, dotProduct]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj1 : j.val < D.R.rS`.

Establish `e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩` using `Fin.ext rfl`. Use `hce ⟨j.val, hj1⟩ i (by simp only; omega)` as an intermediate fact. Rewrite using `[Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]`. Distinguish the cases in `hj2 : j.val ≤ D.R.rS + D.R.k`. Rewrite using `[Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]`.

Establish `hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS` using `by have := j.isLt; omega`. Establish `e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩` using `by ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega`. Rewrite using `[e, hx, mul_zero]`. Use `⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[key, Qi_e v hl hT, Matrix.mulVec_smul, Matrix.mulVec_smul]`.

Use `Submodule.smul_mem _ _ (Q_spanLt v hT a.val a.isLt.le _ fun i hi => ?_)` and prove the remaining obligations. Rewrite using `[Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi, Pi.single_apply, sub_self]`. Rewrite using `[key]`. Use `Q_spanLt v hT D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))` and prove the remaining obligations. Simplify using `only [Formalism.QuantumDeterminants.esI]`.

Use `a.isLt` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Rewrite using `[key]`. Use `Q_spanLt v hT D.R.rS le_rfl _ (hmW _ fun a => ?_)` and prove the remaining obligations. Establish `h1` using `hy a`.

Rewrite `h1` using `[hJ_e v hl hT]`. Conclude with `(mul_eq_zero.1 h1).resolve_left (hstar_ne a)`.
-/
theorem inN_iff (z : Fin X.B.I.n → ℂ) (hz : Formalism.QuantumDeterminants.inWb D.R.k D.R.rS (Qi *ᵥ z))
    (g : Matrix (Fin X.B.I.n) (Fin X.B.I.n) ℂ) (hg : gᴴ * Formalism.REAL.Jm (X.B.I.ε v) * g = Formalism.REAL.Jm (X.B.I.ε v)) :
    InN (X.B.I.ε v) (eV v) z g ↔ Qi * g * Q ∈ Formalism.QuantumDeterminants.Nset D.R.k D.R.rS := by
  have hQiQ := hT.1
  have hQQi := hT.2.1
  have hH := hT.2.2.1
  have hstar_ne : ∀ a : Fin D.R.rS, star ((lam ^ (D.R.rS - a.val))⁻¹) ≠ 0 := fun a =>
    star_ne_zero.2 (inv_ne_zero (pow_ne_zero _ (hl)))
  have hcol : ∀ (M : Matrix (Fin (2 * D.R.rS + D.R.k + 1)) (Fin (2 * D.R.rS + D.R.k + 1)) ℂ) i j,
      M i j = (M *ᵥ Pi.single j 1) i := fun M i j => by rw [Matrix.mulVec_single_one]; rfl
  constructor
  · rintro ⟨⟨hIe, hIz⟩, hperp⟩
    refine ⟨?_, fun a i hai => ?_, fun i j hj1 hj2 hi => ?_⟩
    ·
      show (Qi * g * Q)ᴴ * Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS * (Qi * g * Q) = Formalism.QuantumDeterminants.Hpk D.R.k D.R.rS
      have hQiQ' : (Qi)ᴴ * (Q)ᴴ = 1 := by rw [← Matrix.conjTranspose_mul, hQQi, Matrix.conjTranspose_one]
      rw [← hH]
      calc (Qi * g * Q)ᴴ * ((Q)ᴴ * Formalism.REAL.Jm (X.B.I.ε v) * Q) * (Qi * g * Q)
          = (Q)ᴴ * (gᴴ * ((Qi)ᴴ * (Q)ᴴ) * Formalism.REAL.Jm (X.B.I.ε v) * ((Q * Qi) * g)) *
              Q := by simp only [Matrix.conjTranspose_mul, Matrix.mul_assoc]
        _ = _ := by rw [hQiQ', hQQi, Matrix.mul_one, Matrix.one_mul, hg]
    ·
      rw [hcol (Qi * g * Q) i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a)]
      have h1 : (Qi * g * Q) *ᵥ Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 =
          Pi.single (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a) 1 +
            lam ^ (D.R.rS - a.val) • (Qi *ᵥ ((g - 1) *ᵥ eV v a)) := by
        rw [← Matrix.mulVec_mulVec, ← Matrix.mulVec_mulVec, Q_e v hT, Matrix.mulVec_smul, Matrix.mulVec_smul,
          Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Qi_e v hl hT, smul_sub, smul_smul,
          mul_inv_cancel₀ (pow_ne_zero _ (hl)), one_smul]
        abel
      rw [h1, Pi.add_apply, Pi.smul_apply, Qi_spanLt v hl hT a.val _ (hIe a) i hai, smul_zero, add_zero, Pi.single_apply]
    ·
      rw [hcol (Qi * g * Q) i j]
      have horth : ∀ b : Fin D.R.rS, hJ (X.B.I.ε v) (eV v b) (Q *ᵥ Pi.single j 1) = 0 := by
        intro b
        rw [hJ_e v hl hT, Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Pi.single_apply, if_neg, mul_zero]
        intro h
        have := congrArg Fin.val h
        simp only [Formalism.QuantumDeterminants.esI] at this
        have := b.isLt
        omega
      have h1 : (Qi * g * Q) *ᵥ Pi.single j 1 =
          Pi.single j 1 + Qi *ᵥ ((g - 1) *ᵥ (Q *ᵥ Pi.single j 1)) := by
        rw [Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub]
        simp only [Matrix.mulVec_mulVec, hQiQ, Matrix.one_mulVec, Matrix.mul_assoc]
        abel
      rw [h1, Pi.add_apply, Qi_spanLt v hl hT D.R.rS _ (hperp _ horth) i hi, add_zero, Pi.single_apply]
  · rintro ⟨_, hce, hcw⟩
    have hg' : g = Q * (Qi * g * Q) * Qi := by
      simp only [← Matrix.mul_assoc]
      rw [hQQi, Matrix.one_mul, Matrix.mul_assoc, hQQi, Matrix.mul_one]
    set m := Qi * g * Q with hm
    have key : ∀ x, (g - 1) *ᵥ x = Q *ᵥ ((m - 1) *ᵥ (Qi *ᵥ x)) := by
      intro x
      conv_lhs => rw [hg']
      rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
        Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hQQi, Matrix.one_mulVec]

    have hmW : ∀ x : Fin (2 * D.R.rS + D.R.k + 1) → ℂ, (∀ a, x (Formalism.QuantumDeterminants.esI D.R.k D.R.rS a) = 0) →
        ∀ i : Fin (2 * D.R.rS + D.R.k + 1), D.R.rS ≤ i.val → ((m - 1) *ᵥ x) i = 0 := by
      intro x hx i hi
      simp only [Matrix.mulVec, dotProduct]
      refine Finset.sum_eq_zero fun j _ => ?_
      by_cases hj1 : j.val < D.R.rS
      · have e : j = Formalism.QuantumDeterminants.eI D.R.k D.R.rS ⟨j.val, hj1⟩ := Fin.ext rfl
        have := hce ⟨j.val, hj1⟩ i (by simp only; omega)
        rw [Matrix.sub_apply, e, this, Matrix.one_apply, sub_self, zero_mul]
      · by_cases hj2 : j.val ≤ D.R.rS + D.R.k
        · rw [Matrix.sub_apply, hcw i j (by omega) hj2 hi, Matrix.one_apply, sub_self, zero_mul]
        · have hjr : 2 * D.R.rS + D.R.k - j.val < D.R.rS := by have := j.isLt; omega
          have e : j = Formalism.QuantumDeterminants.esI D.R.k D.R.rS ⟨2 * D.R.rS + D.R.k - j.val, hjr⟩ := by
            ext; simp only [Formalism.QuantumDeterminants.esI]; have := j.isLt; omega
          rw [e, hx, mul_zero]
    refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
    · rw [key, Qi_e v hl hT, Matrix.mulVec_smul, Matrix.mulVec_smul]
      refine Submodule.smul_mem _ _ (Q_spanLt v hT a.val a.isLt.le _ fun i hi => ?_)
      rw [Matrix.sub_mulVec, Matrix.one_mulVec, Pi.sub_apply, ← hcol m i (Formalism.QuantumDeterminants.eI D.R.k D.R.rS a), hce a i hi,
        Pi.single_apply, sub_self]
    · rw [key]
      refine Q_spanLt v hT D.R.rS le_rfl _ (hmW _ (fun a => hz _ (Or.inr ?_)))
      simp only [Formalism.QuantumDeterminants.esI]
      have := a.isLt
      omega
    · rw [key]
      refine Q_spanLt v hT D.R.rS le_rfl _ (hmW _ fun a => ?_)
      have h1 := hy a
      rw [hJ_e v hl hT] at h1
      exact (mul_eq_zero.1 h1).resolve_left (hstar_ne a)

/- English proof (translation)
Establish `hie : ∀ a, hh⁻¹ *ᵥ e a = e a` using `fun a => by conv_lhs => rw [← he a]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `hiz : hh⁻¹ *ᵥ z = z` using `by conv_lhs => rw [← hz]`. Rewrite using `[Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`. Establish `hspan : ∀ k (x : Fin n → ℂ), x ∈ spanLt e k → hh⁻¹ *ᵥ x ∈ spanLt e k`.

Introduce `k x hx`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx'`. Take `⟨b, hb, rfl⟩` from `hx'`. Rewrite using `[hie]`.

Conclude with `Submodule.subset_span ⟨b, hb, rfl⟩`. Consider the case `zero => rw [Matrix.mulVec_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => rw [Matrix.mulVec_add]`. Conclude with `Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => rw [Matrix.mulVec_smul]`. Conclude with `Submodule.smul_mem _ _ hx`. Establish `key : ∀ x, (hh⁻¹ * g * hh - 1) *ᵥ x = hh⁻¹ *ᵥ ((g - 1) *ᵥ (hh *ᵥ x))`. Introduce `x`. Rewrite using `[Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]`.

Establish `horth : ∀ y, (∀ a, hJ ε (e a) y = 0) → ∀ a, hJ ε (e a) (hh *ᵥ y) = 0`. Introduce `y hy a`. Establish `e1 : hJ ε (e a) (hh *ᵥ y) = hJ ε (hh *ᵥ e a) (hh *ᵥ y)` using `by rw [he]`. Rewrite using `[e1]`. Unfold `hJ`.

Rewrite using `[← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hhU]`. Conclude with `hy a`. Take `⟨⟨hIe, hIz⟩, hperp⟩` from `hg`. Use `⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩` and prove the remaining obligations. Rewrite using `[key, he]`.

Conclude with `hspan _ _ (hIe a)`. Rewrite using `[key, hz]`. Conclude with `hspan _ _ hIz`. Rewrite using `[key]`. Conclude with `hspan _ _ (hperp _ (horth y hy))`.
-/
theorem inN_conj {n r' : ℕ} {ε : Fin n → Bool} {e : Fin r' → Fin n → ℂ} {z : Fin n → ℂ}
    {g hh : Matrix (Fin n) (Fin n) ℂ} (hhU : hhᴴ * Formalism.REAL.Jm ε * hh = Formalism.REAL.Jm ε) (hu : IsUnit hh.det)
    (he : ∀ a, hh *ᵥ e a = e a) (hz : hh *ᵥ z = z) (hg : InN ε e z g) : InN ε e z (hh⁻¹ * g * hh) := by
  have hie : ∀ a, hh⁻¹ *ᵥ e a = e a := fun a => by
    conv_lhs => rw [← he a]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hiz : hh⁻¹ *ᵥ z = z := by
    conv_lhs => rw [← hz]
    rw [Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have hspan : ∀ k (x : Fin n → ℂ), x ∈ spanLt e k → hh⁻¹ *ᵥ x ∈ spanLt e k := by
    intro k x hx
    induction hx using Submodule.span_induction with
    | mem x hx' =>
      obtain ⟨b, hb, rfl⟩ := hx'
      rw [hie]
      exact Submodule.subset_span ⟨b, hb, rfl⟩
    | zero => rw [Matrix.mulVec_zero]; exact Submodule.zero_mem _
    | add x y _ _ hx hy => rw [Matrix.mulVec_add]; exact Submodule.add_mem _ hx hy
    | smul c x _ hx => rw [Matrix.mulVec_smul]; exact Submodule.smul_mem _ _ hx
  have key : ∀ x, (hh⁻¹ * g * hh - 1) *ᵥ x = hh⁻¹ *ᵥ ((g - 1) *ᵥ (hh *ᵥ x)) := by
    intro x
    rw [Matrix.sub_mulVec, Matrix.sub_mulVec, Matrix.one_mulVec, Matrix.one_mulVec, Matrix.mulVec_sub,
      Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, Matrix.nonsing_inv_mul _ hu, Matrix.one_mulVec]
  have horth : ∀ y, (∀ a, hJ ε (e a) y = 0) → ∀ a, hJ ε (e a) (hh *ᵥ y) = 0 := by
    intro y hy a
    have e1 : hJ ε (e a) (hh *ᵥ y) = hJ ε (hh *ᵥ e a) (hh *ᵥ y) := by rw [he]
    rw [e1]
    unfold hJ
    rw [← Formalism.L2.SG.HermitianMatrixIdentities.star_dot_conjT' hh, Matrix.mulVec_mulVec, Matrix.mulVec_mulVec, hhU]
    exact hy a
  obtain ⟨⟨hIe, hIz⟩, hperp⟩ := hg
  refine ⟨⟨fun a => ?_, ?_⟩, fun y hy => ?_⟩
  · rw [key, he]; exact hspan _ _ (hIe a)
  · rw [key, hz]; exact hspan _ _ hIz
  · rw [key]; exact hspan _ _ (hperp _ (horth y hy))

end Formalism.L2.SG.QuotientSpan

end
