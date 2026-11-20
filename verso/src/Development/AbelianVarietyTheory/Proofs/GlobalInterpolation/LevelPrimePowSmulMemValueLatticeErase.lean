import Mathlib
import Development.AbelianVarietyTheory.Definitions.GlobalTwisting.FormsStable
import Formalism.LocalRingCardinality.RankBoundMonotoneInDimension
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LClosedeqLemmas
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.NablaLTwist

noncomputable section

namespace GlobalTheory.LvT.KerLat

open MvPolynomial Formalism.GradedWeylDivisibility

def rowZ (r n : ℕ) : Fin r × Fin n → (Fin r → ℤ) := fun v => Pi.single v.1 1

def Shift {R : Type} [CommRing R] {r n : ℕ} (P : Polynomial (MvPolynomial (Fin r × Fin n) R))
    (μ δ : Fin r → ℤ) : Prop :=
  ∀ k : ℕ, IsWeightedHomogeneous (rowZ r n) (P.coeff k) (μ + k • δ)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_mul]`. Use `IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_` and prove the remaining obligations. Establish `hx'` using `Finset.HasAntidiagonal.mem_antidiagonal.mp hx`. Establish `e : μ + μ' + k • δ = (μ + x.1 • δ) + (μ' + x.2 • δ)`.

Rewrite using `[← hx', add_smul]`. Normalize the expressions using the abelian group laws. Rewrite using `[e]`. Conclude with `(hP x.1).mul (hQ x.2)`.
-/
theorem shift_mul {R : Type} [CommRing R] {r n : ℕ}
    {P Q : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ μ' δ : Fin r → ℤ}
    (hP : Shift P μ δ) (hQ : Shift Q μ' δ) : Shift (P * Q) (μ + μ') δ := by
  intro k
  rw [Polynomial.coeff_mul]
  refine IsWeightedHomogeneous.sum _ _ _ fun x hx => ?_
  have hx' := Finset.HasAntidiagonal.mem_antidiagonal.mp hx
  have e : μ + μ' + k • δ = (μ + x.1 • δ) + (μ' + x.2 • δ) := by
    rw [← hx', add_smul]; abel
  rw [e]
  exact (hP x.1).mul (hQ x.2)

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.coeff_one]`. Use `split_ifs with h`. Establish `hk : k = 0` using `by omega`. Substitute `hk` using the available equality.

Simplify using `using isWeightedHomogeneous_one R (rowZ r n)`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem shift_one {R : Type} [CommRing R] {r n : ℕ} (δ : Fin r → ℤ) :
    Shift (1 : Polynomial (MvPolynomial (Fin r × Fin n) R)) 0 δ := by
  intro k
  rw [Polynomial.coeff_one]
  split_ifs with h
  · have hk : k = 0 := by omega
    subst hk
    simpa using isWeightedHomogeneous_one R (rowZ r n)
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Proceed by induction on `e with`. Consider the case `zero => rw [pow_zero, zero_smul]`. Conclude with `shift_one δ`. Consider the case `succ e ih => rw [pow_succ, succ_nsmul]`. Conclude with `shift_mul ih hP`.
-/
theorem shift_pow {R : Type} [CommRing R] {r n : ℕ}
    {P : Polynomial (MvPolynomial (Fin r × Fin n) R)} {μ δ : Fin r → ℤ}
    (hP : Shift P μ δ) (e : ℕ) : Shift (P ^ e) (e • μ) δ := by
  induction e with
  | zero => rw [pow_zero, zero_smul]; exact shift_one δ
  | succ e ih => rw [pow_succ, succ_nsmul]; exact shift_mul ih hP

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using (shift_one (R := R) (r := r) (n := n) δ)`. Consider the case `insert i s his IH`. Rewrite using `[Finset.prod_insert his, Finset.sum_insert his]`. Conclude with `shift_mul (h i (Finset.mem_insert_self _ _)) (IH fun j hj => h j (Finset.mem_insert_of_mem hj))`.
-/
theorem shift_prod {R : Type} [CommRing R] {r n : ℕ} {ι : Type} (s : Finset ι)
    (P : ι → Polynomial (MvPolynomial (Fin r × Fin n) R)) (μ : ι → Fin r → ℤ) (δ : Fin r → ℤ)
    (h : ∀ i ∈ s, Shift (P i) (μ i) δ) : Shift (∏ i ∈ s, P i) (∑ i ∈ s, μ i) δ := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using (shift_one (R := R) (r := r) (n := n) δ)
  | insert i s his IH =>
    rw [Finset.prod_insert his, Finset.sum_insert his]
    exact shift_mul (h i (Finset.mem_insert_self _ _))
      (IH fun j hj => h j (Finset.mem_insert_of_mem hj))

/- English proof (translation)
Introduce `k`. Rewrite using `[Polynomial.algebraMap_apply, Polynomial.coeff_C]`. Use `split_ifs with h`. Substitute `h` using the available equality. Rewrite using `[MvPolynomial.algebraMap_eq]`.

Simplify using `using isWeightedHomogeneous_C (rowZ r n) c`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem shift_algebraMap {R : Type} [CommRing R] {r n : ℕ} (c : R) (δ : Fin r → ℤ) :
    Shift (algebraMap R (Polynomial (MvPolynomial (Fin r × Fin n) R)) c) 0 δ := by
  intro k
  rw [Polynomial.algebraMap_apply, Polynomial.coeff_C]
  split_ifs with h
  · subst h
    rw [MvPolynomial.algebraMap_eq]
    simpa using isWeightedHomogeneous_C (rowZ r n) c
  · exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Introduce `k`. Establish `hX : IsWeightedHomogeneous (rowZ r n) (X v : MvPolynomial (Fin r × Fin n) R) (rowZ r n v)` using `isWeightedHomogeneous_X R _ v`. Establish `hXa : IsWeightedHomogeneous (rowZ r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R) (rowZ r n (a, v.2))` using `isWeightedHomogeneous_X R _ (a, v.2)`. Rewrite using `[Polynomial.coeff_add]`. Use `IsWeightedHomogeneous.add ?_ ?_` and prove the remaining obligations.

Rewrite using `[Polynomial.coeff_C] split_ifs with h`. Substitute `h` using the available equality. Simplify using `using hX`. Conclude with `isWeightedHomogeneous_zero R _ _`. Use `split_ifs with hb`.

Rewrite using `[mul_comm, Polynomial.coeff_C_mul_X] split_ifs with h`. Substitute `h` using the available equality. Establish `e : rowZ r n v + (1 : ℕ) • (Pi.single a 1 - Pi.single b 1 : Fin r → ℤ) = rowZ r n (a, v.2)`. Simplify using `[rowZ, hb]`. Rewrite using `[e]`.

Conclude with `hXa`. Conclude with `isWeightedHomogeneous_zero R _ _`. Rewrite using `[Polynomial.coeff_zero]`. Conclude with `isWeightedHomogeneous_zero R _ _`.
-/
theorem shift_gen {R : Type} [CommRing R] {r n : ℕ} (a b : Fin r) (v : Fin r × Fin n) :
    Shift (Polynomial.C (X v) +
      (if v.1 = b then Polynomial.X * Polynomial.C (X (a, v.2)) else 0) :
        Polynomial (MvPolynomial (Fin r × Fin n) R)) (rowZ r n v) (Pi.single a 1 - Pi.single b 1) := by
  intro k
  have hX : IsWeightedHomogeneous (rowZ r n) (X v : MvPolynomial (Fin r × Fin n) R)
      (rowZ r n v) := isWeightedHomogeneous_X R _ v
  have hXa : IsWeightedHomogeneous (rowZ r n) (X (a, v.2) : MvPolynomial (Fin r × Fin n) R)
      (rowZ r n (a, v.2)) := isWeightedHomogeneous_X R _ (a, v.2)
  rw [Polynomial.coeff_add]
  refine IsWeightedHomogeneous.add ?_ ?_
  · rw [Polynomial.coeff_C]
    split_ifs with h
    · subst h; simpa using hX
    · exact isWeightedHomogeneous_zero R _ _
  · split_ifs with hb
    · rw [mul_comm, Polynomial.coeff_C_mul_X]
      split_ifs with h
      · subst h
        have e : rowZ r n v + (1 : ℕ) • (Pi.single a 1 - Pi.single b 1 : Fin r → ℤ) = rowZ r n (a, v.2) := by
          simp [rowZ, hb]
        rw [e]; exact hXa
      · exact isWeightedHomogeneous_zero R _ _
    · rw [Polynomial.coeff_zero]
      exact isWeightedHomogeneous_zero R _ _

/- English proof (translation)
Unfold `rowGen`. Rewrite using `[aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]`. Use `shift_mul (shift_algebraMap c _) ?_` and prove the remaining obligations. Unfold `Finsupp.prod Finsupp.sum`. Conclude with `shift_prod _ _ _ _ fun v _ => shift_pow (shift_gen a b v) _`.
-/
theorem shift_rowGen_monomial (R : Type) [CommRing R] {r n : ℕ} (a b : Fin r)
    (d : Fin r × Fin n →₀ ℕ) (c : R) :
    Shift (rowGen R a b (monomial d c)) (Finsupp.weight (rowZ r n) d) (Pi.single a 1 - Pi.single b 1) := by
  unfold rowGen
  rw [aeval_monomial, Finsupp.weight_apply, ← zero_add (Finsupp.sum d _)]
  refine shift_mul (shift_algebraMap c _) ?_
  unfold Finsupp.prod Finsupp.sum
  exact shift_prod _ _ _ _ fun v _ => shift_pow (shift_gen a b v) _

/- English proof (translation)
Unfold `rowDiv`. Use `conv => enter [2, 1, 2]`. Rewrite using `[f.as_sum]`. Rewrite using `[map_sum, Polynomial.finsetSum_coeff]`. Use `IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_` and prove the remaining obligations.

Use `shift_rowGen_monomial R a b d (coeff d f) k` as an intermediate fact. Rewrite `this` using `[hf (mem_support_iff.mp hd)]`. Then use the resulting hypothesis.
-/
theorem rowDiv_shift (R : Type) [CommRing R] {r n : ℕ} (H : Fin r → ℤ) (a b : Fin r) (k : ℕ)
    (f : MvPolynomial (Fin r × Fin n) R) (hf : IsWeightedHomogeneous (rowZ r n) f H) :
    IsWeightedHomogeneous (rowZ r n) (rowDiv R a b k f) (H + k • (Pi.single a 1 - Pi.single b 1)) := by
  unfold rowDiv
  conv => enter [2, 1, 2]; rw [f.as_sum]
  rw [map_sum, Polynomial.finsetSum_coeff]
  refine IsWeightedHomogeneous.sum _ _ _ fun d hd => ?_
  have := shift_rowGen_monomial R a b d (coeff d f) k
  rwa [hf (mem_support_iff.mp hd)] at this

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp`. Consider the case `add f g hf hg => simp only [map_add, Pi.add_apply, Nat.cast_add, hf, hg]`. Consider the case `single v c`. Simplify using `[Finsupp.weight_apply, rowZ, rowW, Pi.single_apply, Finsupp.sum_single_index]`.
-/
theorem weight_rowZ {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowZ r n) d a = ((Finsupp.weight (rowW r n) d a : ℕ) : ℤ) := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp
  | add f g hf hg => simp only [map_add, Pi.add_apply, Nat.cast_add, hf, hg]
  | single v c =>
    simp [Finsupp.weight_apply, rowZ, rowW, Pi.single_apply, Finsupp.sum_single_index]

/- English proof (translation)
Proceed by induction on `d using Finsupp.induction_linear with`. Consider the case `zero => simp [rowDeg]`. Consider the case `add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg, rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]`. Consider the case `single v c`. Take `⟨b, s⟩` from `v`.

Distinguish the cases in `h : a = b`. Substitute `h` using the available equality. Simplify using `[Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply]`. Simplify using `[Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply, h, Ne.symm h]`.
-/
theorem weight_rowW {r n : ℕ} (d : Fin r × Fin n →₀ ℕ) (a : Fin r) :
    Finsupp.weight (rowW r n) d a = rowDeg d a := by
  classical
  induction d using Finsupp.induction_linear with
  | zero => simp [rowDeg]
  | add f g hf hg => simp only [map_add, Pi.add_apply, hf, hg, rowDeg, Finsupp.add_apply, Finset.sum_add_distrib]
  | single v c =>
    obtain ⟨b, s⟩ := v
    by_cases h : a = b
    · subst h
      simp [Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply]
    · simp [Finsupp.weight_apply, rowDeg, rowW, Finsupp.sum_single_index, Finsupp.single_apply, h, Ne.symm h]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil`. Use `⟨fun a => (rowNu (r := n) ν a : ℤ), fun d hd => ?_⟩` and prove the remaining obligations. Use `hwRowWeight R n n le_rfl ν hν hd` as an intermediate fact. Use function extensionality and compare the values at `a`.

Rewrite using `[weight_rowZ, this]`. Consider the case `cons x w ih`. Take `⟨H, hH⟩` from `ih`. Conclude with `⟨_, rowDiv_shift R H _ _ _ _ hH⟩`.
-/
theorem word_homog (R : Type) [CommRing R] {n : ℕ} (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin n × Fin n × ℕ)) :
    ∃ H, IsWeightedHomogeneous (rowZ n n) (applyWord R w (hw R le_rfl ν)) H := by
  induction w with
  | nil =>
    refine ⟨fun a => (rowNu (r := n) ν a : ℤ), fun d hd => ?_⟩
    have := hwRowWeight R n n le_rfl ν hν hd
    funext a
    rw [weight_rowZ, this]
  | cons x w ih =>
    obtain ⟨H, hH⟩ := ih
    exact ⟨_, rowDiv_shift R H _ _ _ _ hH⟩

/- English proof (translation)
Distinguish the cases in `h0 : applyWord ℂ w (hw ℂ le_rfl ν) = 0`. Conclude with `⟨0, Nat.zero_le _, by rw [h0]; exact isWeightedHomogeneous_zero _ _ _⟩`. Take `⟨m, hm⟩` from `ne_zero_iff.mp h0`. Take `⟨H, hH⟩` from `word_homog ℂ ν hν w`. Use `⟨Finsupp.weight (rowW n n) m, ?_, fun d hd => ?_⟩` and prove the remaining obligations.

Establish `e : applyWord ℂ w (hw ℂ le_rfl ν) = map (Int.castRingHom ℂ) (applyWord ℤ w (hw ℤ le_rfl ν))`. Rewrite using `[← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Establish `hm' : m ∈ (applyWord ℤ w (hw ℤ le_rfl ν)).support`. Rewrite using `[mem_support_iff]`. Introduce `h`.

Apply `hm` to reduce the goal to its premises. Rewrite using `[e, coeff_map, h, map_zero]`. Establish `hd` using `(dualWeylDominanceZ n n ν le_rfl hν _ (weylLeDual ℤ n n le_rfl ν hν (Submodule.subset_span ⟨w, rfl⟩)) m hm').1 1`. Establish `hs : (Finset.univ.filter fun a : Fin n => a.val < 1) = {⟨0, hn⟩}`. Use extensionality with `a`.

Simplify using `[Fin.ext_iff]`. Rewrite `hd` using `[hs, Finset.sum_singleton, Finset.sum_singleton]`. Rewrite using `[weight_rowW]`. Simplify `hd` using `[rowNu, hn]`. Use function extensionality and compare the values at `a`.

Use `congrFun ((hH hd).trans (hH hm).symm) a` as an intermediate fact. Rewrite `this` using `[weight_rowZ, weight_rowZ]`. Conclude with `this` after adjusting the coercions.
-/
theorem word_weight {n : ℕ} (hn : 0 < n) (ν : Fin n → ℕ) (hν : Antitone ν)
    (w : List (Fin n × Fin n × ℕ)) :
    ∃ μ : Fin n → ℕ, μ ⟨0, hn⟩ ≤ ν ⟨0, hn⟩ ∧
      IsWeightedHomogeneous (rowW n n) (applyWord ℂ w (hw ℂ le_rfl ν)) μ := by
  by_cases h0 : applyWord ℂ w (hw ℂ le_rfl ν) = 0
  · exact ⟨0, Nat.zero_le _, by rw [h0]; exact isWeightedHomogeneous_zero _ _ _⟩
  obtain ⟨m, hm⟩ := ne_zero_iff.mp h0
  obtain ⟨H, hH⟩ := word_homog ℂ ν hν w
  refine ⟨Finsupp.weight (rowW n n) m, ?_, fun d hd => ?_⟩
  · have e : applyWord ℂ w (hw ℂ le_rfl ν) = map (Int.castRingHom ℂ) (applyWord ℤ w (hw ℤ le_rfl ν)) := by
      rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
    have hm' : m ∈ (applyWord ℤ w (hw ℤ le_rfl ν)).support := by
      rw [mem_support_iff]
      intro h
      apply hm
      rw [e, coeff_map, h, map_zero]
    have hd := (dualWeylDominanceZ n n ν le_rfl hν _
      (weylLeDual ℤ n n le_rfl ν hν (Submodule.subset_span ⟨w, rfl⟩)) m hm').1 1
    have hs : (Finset.univ.filter fun a : Fin n => a.val < 1) = {⟨0, hn⟩} := by
      ext a; simp [Fin.ext_iff]
    rw [hs, Finset.sum_singleton, Finset.sum_singleton] at hd
    rw [weight_rowW]
    simpa [rowNu, hn] using hd
  · funext a
    have := congrFun ((hH hd).trans (hH hm).symm) a
    rw [weight_rowZ, weight_rowZ] at this
    exact_mod_cast this

open Formalism.BasicNotions

def roundL (R : Type) [CommRing R] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) R) :
    MvPolynomial (Fin n × Fin n) R →ₗ[R] MvPolynomial (Fin n × Fin n) R :=
  detPow R n g (-lam.detShift) • (Formalism.UG.dwAct R n n g).toLinearMap

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem roundL_coe (R : Type) [CommRing R] (n : ℕ) (lam : DomWeight n) (g : GL (Fin n) R) :
    (fun f => roundL R n lam g f) = roundAct R n lam g := rfl

def dq (K : Type) [CommRing K] {n : ℕ} (hn : 0 < n) (t : Kˣ) : GL (Fin n) K :=
  diagGL K n (Function.update 1 ⟨0, hn⟩ t)

/- English proof (translation)
Establish `hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ k) = Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det k)`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]`. Conclude with `(φ.map_det (k : Matrix (Fin n) (Fin n) R)).symm`. Unfold `roundAct Formalism.UG.dwAct`.

Rewrite using `[smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, ldtwist_map_rowAct, ← map_inv, detPow, detPow, hd, ← map_zpow, Units.coe_map]`. Both sides reduce to the same expression.
-/
theorem roundAct_map {R S : Type} [CommRing R] [CommRing S] (φ : R →+* S) {n : ℕ} (lam : DomWeight n)
    (k : GL (Fin n) R) (g : MvPolynomial (Fin n × Fin n) R) :
    roundAct S n lam (Matrix.GeneralLinearGroup.map φ k) (map φ g) = map φ (roundAct R n lam k g) := by
  have hd : Matrix.GeneralLinearGroup.det (Matrix.GeneralLinearGroup.map φ k) =
      Units.map φ.toMonoidHom (Matrix.GeneralLinearGroup.det k) := by
    apply Units.ext
    rw [Matrix.GeneralLinearGroup.val_det_apply, Units.coe_map, Matrix.GeneralLinearGroup.val_det_apply]
    exact (φ.map_det (k : Matrix (Fin n) (Fin n) R)).symm
  unfold roundAct Formalism.UG.dwAct
  rw [smul_eq_C_mul, smul_eq_C_mul, map_mul, map_C, ldtwist_map_rowAct, ← map_inv, detPow, detPow, hd,
    ← map_zpow, Units.coe_map]
  rfl

/- English proof (translation)
The claim follows from `Submodule.smul_mem _ _ (Formalism.UG.Final.WeylGLStable R n n le_rfl _ _ g hg)`.
-/
theorem roundAct_mem (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight n)
    (k : GL (Fin n) R) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n lam) :
    roundAct R n lam k g ∈ delSq R n lam :=
  Submodule.smul_mem _ _ (Formalism.UG.Final.WeylGLStable R n n le_rfl _ _ g hg)

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨w, rfl⟩` from `hy`. Take `⟨μ, hμ, hh⟩` from `word_weight hn lam.natW (factNatW n lam).1 w`. Use `⟨((T : R) ^ (lam.natW ⟨0, hn⟩ - μ ⟨0, hn⟩)) • applyWord R w (hw R le_rfl lam.natW), Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩), ?_⟩` and prove the remaining obligations.

Establish `hdet : Matrix.GeneralLinearGroup.det (dq ℂ hn t) = t`. Apply `Units.ext` to reduce the goal to its premises. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply]`. Use `show (Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)) : ℂ)).det = _`. Rewrite using `[Matrix.det_diagonal, Finset.prod_eq_single ⟨0, hn⟩]`.

Simplify using the standard rewrite rules. Introduce `b _ hb`. Simplify using `[Function.update_of_ne hb]`. Simplify using the standard rewrite rules. Establish `hinv : (((dq ℂ hn t)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) = Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)⁻¹ : ℂˣ) : ℂ)` using `rfl`.

Establish `hT : (T : ℂ) ≠ 0` using `ht ▸ t.ne_zero`. Simplify using `only`. Rewrite using `[smul_eq_C_mul (a := (T : R) ^ _), map_mul, map_C, ← smul_eq_C_mul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Unfold `roundAct Formalism.UG.dwAct`. Rewrite using `[hinv, rowActDiagWeight ℂ n n _ μ _ hh, smul_smul, smul_smul, detPow, hdet, Finset.prod_eq_single ⟨0, hn⟩]`.

Use `congr 1`. Establish `h2` using `(factNatW n lam).2.1 ⟨0, hn⟩`. Simplify using `only [Function.update_self, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, ht, map_pow, map_natCast]`. Rewrite using `[inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hT, ← zpow_add₀ hT, ← zpow_natCast]`. Use `congr 1`.

Rewrite using `[Nat.cast_sub hμ]`. Use linear arithmetic over natural numbers and integers. Introduce `b _ hb`. Simplify using `[Function.update_of_ne hb]`. Simplify using the standard rewrite rules.

Consider the case `zero`. Use `⟨0, zero_mem _, ?_⟩` and prove the remaining obligations. Rewrite using `[← roundL_coe]`. Simplify using the standard rewrite rules. Consider the case `add y z _ _ hy hz`.

Take `⟨y', hy', ey⟩` from `hy`. Take `⟨z', hz', ez⟩` from `hz`. Use `⟨y' + z', add_mem hy' hz', ?_⟩` and prove the remaining obligations. Rewrite using `[map_add, map_add, ← ey, ← ez, ← roundL_coe]`. Simplify using the standard rewrite rules.

Consider the case `smul a y _ hy`. Take `⟨y', hy', ey⟩` from `hy`. Use `⟨a • y', Submodule.smul_mem _ _ hy', ?_⟩` and prove the remaining obligations. Rewrite using `[smul_eq_C_mul (a := a), smul_eq_C_mul (a := a), map_mul, map_mul, map_C, ← smul_eq_C_mul, ← smul_eq_C_mul, ← ey, ← roundL_coe]`. Simplify using `only [map_smul]`.

Rewrite using `[smul_comm]`.
-/
theorem diag_step {R : Type} [CommRing R] (φ : R →+* ℂ) {n : ℕ} (hn : 0 < n) (lam : DomWeight n) (T : ℕ)
    (t : ℂˣ) (ht : (t : ℂ) = T) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n lam) :
    ∃ g' ∈ delSq R n lam,
      ((T : ℂ) ^ lam.w ⟨0, hn⟩) • roundAct ℂ n lam (dq ℂ hn t) (map φ g) = map φ g' := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨w, rfl⟩ := hy
    obtain ⟨μ, hμ, hh⟩ := word_weight hn lam.natW (factNatW n lam).1 w
    refine ⟨((T : R) ^ (lam.natW ⟨0, hn⟩ - μ ⟨0, hn⟩)) • applyWord R w (hw R le_rfl lam.natW),
      Submodule.smul_mem _ _ (Submodule.subset_span ⟨w, rfl⟩), ?_⟩
    have hdet : Matrix.GeneralLinearGroup.det (dq ℂ hn t) = t := by
      apply Units.ext
      rw [Matrix.GeneralLinearGroup.val_det_apply]
      show (Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)) : ℂ)).det = _
      rw [Matrix.det_diagonal, Finset.prod_eq_single ⟨0, hn⟩]
      · simp
      · intro b _ hb; simp [Function.update_of_ne hb]
      · simp
    have hinv : (((dq ℂ hn t)⁻¹ : GL (Fin n) ℂ) : Matrix (Fin n) (Fin n) ℂ) =
        Matrix.diagonal fun a => (((Function.update (1 : Fin n → ℂˣ) ⟨0, hn⟩ t a : ℂˣ)⁻¹ : ℂˣ) : ℂ) := rfl
    have hT : (T : ℂ) ≠ 0 := ht ▸ t.ne_zero
    simp only
    rw [smul_eq_C_mul (a := (T : R) ^ _), map_mul, map_C, ← smul_eq_C_mul, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
    unfold roundAct Formalism.UG.dwAct
    rw [hinv, rowActDiagWeight ℂ n n _ μ _ hh, smul_smul, smul_smul, detPow, hdet,
      Finset.prod_eq_single ⟨0, hn⟩]
    · congr 1
      have h2 := (factNatW n lam).2.1 ⟨0, hn⟩
      simp only [Function.update_self, Units.val_zpow_eq_zpow_val, Units.val_inv_eq_inv_val, ht, map_pow, map_natCast]
      rw [inv_pow, ← zpow_natCast, ← zpow_neg, ← zpow_add₀ hT, ← zpow_add₀ hT, ← zpow_natCast]
      congr 1
      rw [Nat.cast_sub hμ]
      omega
    · intro b _ hb; simp [Function.update_of_ne hb]
    · simp
  | zero =>
    refine ⟨0, zero_mem _, ?_⟩
    rw [← roundL_coe]; simp
  | add y z _ _ hy hz =>
    obtain ⟨y', hy', ey⟩ := hy
    obtain ⟨z', hz', ez⟩ := hz
    refine ⟨y' + z', add_mem hy' hz', ?_⟩
    rw [map_add, map_add, ← ey, ← ez, ← roundL_coe]
    simp
  | smul a y _ hy =>
    obtain ⟨y', hy', ey⟩ := hy
    refine ⟨a • y', Submodule.smul_mem _ _ hy', ?_⟩
    rw [smul_eq_C_mul (a := a), smul_eq_C_mul (a := a), map_mul, map_mul, map_C, ← smul_eq_C_mul, ← smul_eq_C_mul, ← ey,
      ← roundL_coe]
    simp only [map_smul]
    rw [smul_comm]

section Lattice

variable {q : ℕ} {F : Type} [Field F] {Lc : LocF q F} {n : ℕ}

/- English proof (translation)
Simplify using `only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]`. Use `forall_congr' fun a => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨y, hy⟩`. Rewrite using `[← hy]`. Conclude with `y.2`.
-/
theorem mem_std (x : Fin n → Lc.K) : x ∈ Lc.std n ↔ ∀ a, x a ∈ Lc.O := by
  simp only [LocF.std, Submodule.mem_pi, Set.mem_univ, true_imp_iff, Submodule.mem_one]
  refine forall_congr' fun a => ⟨?_, fun h => ⟨⟨_, h⟩, rfl⟩⟩
  rintro ⟨y, hy⟩
  rw [← hy]; exact y.2

/- English proof (translation)
Rewrite `hx`, the goal using `[mem_std]`. Introduce `a`. Rewrite using `[Matrix.mulVec, dotProduct]`. Conclude with `sum_mem fun b _ => mul_mem (hA a b) (hx b)`.
-/
theorem mulVec_std (A : Matrix (Fin n) (Fin n) Lc.K) (hA : ∀ a b, A a b ∈ Lc.O) (x : Fin n → Lc.K)
    (hx : x ∈ Lc.std n) : A.mulVec x ∈ Lc.std n := by
  rw [mem_std] at hx ⊢
  intro a
  rw [Matrix.mulVec, dotProduct]
  exact sum_mem fun b _ => mul_mem (hA a b) (hx b)

/- English proof (translation)
Rewrite using `[mem_std]`. Introduce `a`. Rewrite using `[Pi.single_apply]`. Use `split_ifs`. Conclude with `one_mem _`.

Conclude with `zero_mem _`.
-/
theorem single_std (b : Fin n) : (Pi.single b 1 : Fin n → Lc.K) ∈ Lc.std n := by
  rw [mem_std]
  intro a
  rw [Pi.single_apply]
  split_ifs
  · exact one_mem _
  · exact zero_mem _

def unip {K : Type} [CommRing K] (N : Matrix (Fin n) (Fin n) K) (hN : N * N = 0) : GL (Fin n) K where
  val := 1 + N
  inv := 1 - N
  val_inv := by rw [add_mul, mul_sub, mul_sub, hN]; simp
  inv_val := by rw [sub_mul, mul_add, mul_add, hN]; simp

/- English proof (translation)
Introduce `x`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec, hh]`. Use `show (1 + N).mulVec x ∈ _ ↔ _`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Use `⟨fun hx => ?_, fun hx => add_mem hx (mulVec_std N hO x hx)⟩` and prove the remaining obligations.

Establish `h2` using `sub_mem hx (mulVec_std N hO _ hx)`. Rewrite `h2` using `[Matrix.mulVec_add, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, add_zero, add_sub_cancel_right]`. Then use the resulting hypothesis.
-/
theorem frame_unip {Λ : Submodule Lc.O (Fin n → Lc.K)} {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h Λ)
    (N : Matrix (Fin n) (Fin n) Lc.K) (hN : N * N = 0) (hO : ∀ a b, N a b ∈ Lc.O) :
    Lc.IsFrame n (h * unip N hN) Λ := by
  intro x
  rw [Units.val_mul, ← Matrix.mulVec_mulVec, hh]
  show (1 + N).mulVec x ∈ _ ↔ _
  rw [Matrix.add_mulVec, Matrix.one_mulVec]
  refine ⟨fun hx => ?_, fun hx => add_mem hx (mulVec_std N hO x hx)⟩
  have h2 := sub_mem hx (mulVec_std N hO _ hx)
  rwa [Matrix.mulVec_add, Matrix.mulVec_mulVec, hN, Matrix.zero_mulVec, add_zero, add_sub_cancel_right] at h2

/- English proof (translation)
Use `p.2.add 0 (zero_mem _) 0 (zero_mem _)` as an intermediate fact. Rewrite `this` using `[add_zero]`. Conclude with `left_eq_add.mp this`.
-/
theorem f_zero (p : LocF.PP Lc n) : p.1.f 0 = 0 := by
  have := p.2.add 0 (zero_mem _) 0 (zero_mem _)
  rw [add_zero] at this
  exact left_eq_add.mp this

/- English proof (translation)
Establish `e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) = ∑ a, x a • (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)`. Use function extensionality and compare the values at `b`. Simplify using `[Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]`. Rewrite using `[e]`. Establish `hm : ∀ a, (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1) ∈ p.1.L` using `fun a => (hh _).2 (single_std a)`.

Proceed by induction on `(Finset.univ : Finset (Fin n)) using Finset.induction_on with`. Consider the case `empty => simpa using f_zero p`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.sum_insert ha, p.2.add _ (Submodule.smul_mem _ _ (hm a)) _ (sum_mem fun b _ => Submodule.smul_mem _ _ (hm b)), p.2.smul _ _ (hm a), ih]`.
-/
theorem f_expand (p : LocF.PP Lc n) {h : GL (Fin n) Lc.K} (hh : Lc.IsFrame n h p.1.L) (x : Fin n → Lc.O) :
    p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec fun a => (x a : Lc.K)) =
      ∑ a, Lc.res (x a) * p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) := by
  have e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) =
      ∑ a, x a • (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1) := by
    funext b
    simp [Matrix.mulVec, dotProduct, Finset.sum_apply, Pi.single_apply, Subring.smul_def, mul_comm]
  rw [e]
  have hm : ∀ a, (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1) ∈ p.1.L :=
    fun a => (hh _).2 (single_std a)
  induction (Finset.univ : Finset (Fin n)) using Finset.induction_on with
  | empty => simpa using f_zero p
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha,
      p.2.add _ (Submodule.smul_mem _ _ (hm a)) _ (sum_mem fun b _ => Submodule.smul_mem _ _ (hm b)),
      p.2.smul _ _ (hm a), ih]

/- English proof (translation)
Take `⟨h, hh⟩` from `p.2.lat`. Distinguish the cases in `h0 : p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single ⟨0, hn⟩ 1)) = 0`. Use `swap`. Conclude with `⟨h, hh, h0⟩`. Establish `hex : ∃ a, p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) ≠ 0`.

Assume the negation of the conclusion as `hc`. Use `push Not at hc`. Take `⟨x, hx⟩` from `p.2.ne`. Establish `hxL : x ∈ p.1.L` using `by_contra fun h' => hx (p.2.off x h')`. Establish `e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (((h⁻¹ : GL (Fin n) Lc.K) : Matrix _ _ _).mulVec x) = x`.

Rewrite using `[Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]`. Establish `hs` using `(mem_std _).1 ((hh _).1 (e.symm ▸ hxL))`. Use `f_expand p hh fun a => ⟨_, hs a⟩` as an intermediate fact. Apply `hx` to reduce the goal to its premises. Rewrite using `[← e]`.

Use `this.trans (Finset.sum_eq_zero fun a _ => by rw [hc a, mul_zero])` and prove the remaining obligations. Take `⟨a, ha⟩` from `hex`. Establish `hne : a ≠ ⟨0, hn⟩` using `fun e => ha (e ▸ h0)`. Establish `hN : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)) * Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K) = 0` using `Matrix.single_mul_single_of_ne _ _ _ _ hne.symm _`. Use `⟨h * unip _ hN, frame_unip hh _ hN fun c d => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[Matrix.single_apply] split_ifs`. Conclude with `one_mem _`. Conclude with `zero_mem _`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Establish `e0 : ((unip _ hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) = 1 + Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)` using `rfl`.

Rewrite using `[e0]`. Establish `e : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)).mulVec (Pi.single ⟨0, hn⟩ 1) = Pi.single a 1`. Use function extensionality and compare the values at `c`. Simplify using `[Matrix.single_apply, Pi.single_apply, eq_comm]`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec, e, Matrix.mulVec_add, p.2.add _ ((hh _).2 (single_std _)) _ ((hh _).2 (single_std _)), h0, zero_add]`.

Conclude with `ha`.
-/
theorem exists_frame_ne (hn : 0 < n) (p : LocF.PP Lc n) : ∃ h : GL (Fin n) Lc.K, Lc.IsFrame n h p.1.L ∧
    p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single ⟨0, hn⟩ 1)) ≠ 0 := by
  obtain ⟨h, hh⟩ := p.2.lat
  by_cases h0 : p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single ⟨0, hn⟩ 1)) = 0
  swap
  · exact ⟨h, hh, h0⟩
  have hex : ∃ a, p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) ≠ 0 := by
    by_contra hc
    push Not at hc
    obtain ⟨x, hx⟩ := p.2.ne
    have hxL : x ∈ p.1.L := by_contra fun h' => hx (p.2.off x h')
    have e : (h : Matrix (Fin n) (Fin n) Lc.K).mulVec (((h⁻¹ : GL (Fin n) Lc.K) : Matrix _ _ _).mulVec x) = x := by
      rw [Matrix.mulVec_mulVec, Units.mul_inv, Matrix.one_mulVec]
    have hs := (mem_std _).1 ((hh _).1 (e.symm ▸ hxL))
    have := f_expand p hh fun a => ⟨_, hs a⟩
    apply hx
    rw [← e]
    refine this.trans (Finset.sum_eq_zero fun a _ => by rw [hc a, mul_zero])
  obtain ⟨a, ha⟩ := hex
  have hne : a ≠ ⟨0, hn⟩ := fun e => ha (e ▸ h0)
  have hN : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)) * Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K) = 0 :=
    Matrix.single_mul_single_of_ne _ _ _ _ hne.symm _
  refine ⟨h * unip _ hN, frame_unip hh _ hN fun c d => ?_, ?_⟩
  · rw [Matrix.single_apply]
    split_ifs
    · exact one_mem _
    · exact zero_mem _
  · rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    have e0 : ((unip _ hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) =
      1 + Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K) := rfl
    rw [e0]
    have e : (Matrix.single a (⟨0, hn⟩ : Fin n) (1 : Lc.K)).mulVec (Pi.single ⟨0, hn⟩ 1) = Pi.single a 1 := by
      funext c
      simp [Matrix.single_apply, Pi.single_apply, eq_comm]
    rw [Matrix.add_mulVec, Matrix.one_mulVec, e, Matrix.mulVec_add,
      p.2.add _ ((hh _).2 (single_std _)) _ ((hh _).2 (single_std _)), h0, zero_add]
    exact ha

/- English proof (translation)
Take `⟨h, hh, h0⟩` from `exists_frame_ne hn p`. Use `set c : Fin n → F := fun a => p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) with hc`. Use `choose b hb using fun a => Lc.res_surj (-c a / c ⟨0, hn⟩)`. Set `N₀ : Matrix (Fin n) (Fin n) Lc.O` to `Matrix.of fun a d => if a = ⟨0, hn⟩ ∧ d ≠ ⟨0, hn⟩ then b d else 0`. Set `N : Matrix (Fin n) (Fin n) Lc.K` to `N₀.map Lc.O.subtype`.

Establish `hN : N * N = 0`. Use extensionality with `a d`. Rewrite using `[Matrix.mul_apply]`. Use `Finset.sum_eq_zero fun e _ => ?_` and prove the remaining obligations. Apply the tactic sequence `by_cases he : e = ⟨0, hn⟩ <;> simp [N, N₀, he]`.

Use `⟨h * unip N hN, c ⟨0, hn⟩, h0, frame_unip hh N hN fun a d => (N₀ a d).2, fun x => ?_⟩` and prove the remaining obligations. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Establish `e : ((unip N hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) = fun a => ((x a + N₀.mulVec x a : Lc.O) : Lc.K)` using `by show (1 + N).mulVec _ = _`. Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Use function extensionality and compare the values at `a`.

Simplify using `[N, Matrix.mulVec, dotProduct]`. Rewrite using `[e, f_expand p hh]`. Use `show ∑ a, Lc.res (x a + N₀.mulVec x a) * c a = _`. Simplify using `only [map_add, add_mul, Finset.sum_add_distrib]`. Establish `h0' : c ⟨0, hn⟩ ≠ 0` using `h0`.

Establish `e2 : ∑ a, Lc.res (N₀.mulVec x a) * c a = ∑ d ∈ Finset.univ.erase ⟨0, hn⟩, -(Lc.res (x d) * c d)`. Rewrite using `[Finset.sum_eq_single ⟨0, hn⟩]`. Rewrite using `[Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul, ← Finset.sum_erase (a := ⟨0, hn⟩) _ (by simp [N₀])]`. Use `Finset.sum_congr rfl fun d hd => ?_` and prove the remaining obligations. Establish `hd'` using `Finset.ne_of_mem_erase hd`.

Simplify using `only [N₀, Matrix.of_apply, true_and, ne_eq, hd', not_false_eq_true, if_true, map_mul, hb]`. Clear the denominators using the available nonvanishing facts. Introduce `a _ ha`. Simplify using `[N₀, Matrix.mulVec, dotProduct, ha]`. Simplify using the standard rewrite rules.

Rewrite using `[e2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n)), Finset.sum_neg_distrib]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_frame_adapted (hn : 0 < n) (p : LocF.PP Lc n) : ∃ (h : GL (Fin n) Lc.K) (c : F), c ≠ 0 ∧
    Lc.IsFrame n h p.1.L ∧ ∀ x : Fin n → Lc.O,
      p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec fun a => (x a : Lc.K)) = Lc.res (x ⟨0, hn⟩) * c := by
  obtain ⟨h, hh, h0⟩ := exists_frame_ne hn p
  set c : Fin n → F := fun a => p.1.f ((h : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single a 1)) with hc
  choose b hb using fun a => Lc.res_surj (-c a / c ⟨0, hn⟩)
  let N₀ : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a d => if a = ⟨0, hn⟩ ∧ d ≠ ⟨0, hn⟩ then b d else 0
  let N : Matrix (Fin n) (Fin n) Lc.K := N₀.map Lc.O.subtype
  have hN : N * N = 0 := by
    ext a d
    rw [Matrix.mul_apply]
    refine Finset.sum_eq_zero fun e _ => ?_
    by_cases he : e = ⟨0, hn⟩ <;> simp [N, N₀, he]
  refine ⟨h * unip N hN, c ⟨0, hn⟩, h0, frame_unip hh N hN fun a d => (N₀ a d).2, fun x => ?_⟩
  rw [Units.val_mul, ← Matrix.mulVec_mulVec]
  have e : ((unip N hN : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (fun a => (x a : Lc.K)) =
      fun a => ((x a + N₀.mulVec x a : Lc.O) : Lc.K) := by
    show (1 + N).mulVec _ = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
    funext a
    simp [N, Matrix.mulVec, dotProduct]
  rw [e, f_expand p hh]
  show ∑ a, Lc.res (x a + N₀.mulVec x a) * c a = _
  simp only [map_add, add_mul, Finset.sum_add_distrib]
  have h0' : c ⟨0, hn⟩ ≠ 0 := h0
  have e2 : ∑ a, Lc.res (N₀.mulVec x a) * c a = ∑ d ∈ Finset.univ.erase ⟨0, hn⟩, -(Lc.res (x d) * c d) := by
    rw [Finset.sum_eq_single ⟨0, hn⟩]
    · rw [Matrix.mulVec, dotProduct, map_sum, Finset.sum_mul, ← Finset.sum_erase (a := ⟨0, hn⟩) _ (by simp [N₀])]
      refine Finset.sum_congr rfl fun d hd => ?_
      have hd' := Finset.ne_of_mem_erase hd
      simp only [N₀, Matrix.of_apply, true_and, ne_eq, hd', not_false_eq_true, if_true, map_mul, hb]
      field_simp
    · intro a _ ha
      simp [N₀, Matrix.mulVec, dotProduct, ha]
    · simp
  rw [e2, ← Finset.add_sum_erase _ _ (Finset.mem_univ (⟨0, hn⟩ : Fin n)), Finset.sum_neg_distrib]
  ring

/- English proof (translation)
Take `⟨h₁, c, hc, hf, hx⟩` from `exists_frame_adapted hn p`. Use `set d := dq Lc.K hn (Units.mk0 _ Lc.q_ne) with hd`. Establish `hdx : ∀ (x : Fin n → Lc.K) a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a = if a = ⟨0, hn⟩ then (q : Lc.K) * x a else x a`. Introduce `x a`. Use `show (Matrix.diagonal _).mulVec x a = _`.

Rewrite using `[Matrix.mulVec_diagonal]`. Use `split_ifs with ha`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne ha]`.

Establish `h2 : ∀ x, ((h₁ * d : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n`. Introduce `x`. Rewrite using `[Units.val_mul, ← Matrix.mulVec_mulVec]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨h3, h4⟩`.

Establish `hs` using `(mem_std _).1 ((hf _).1 h3)`. Establish `h5` using `(hx fun a => ⟨_, hs a⟩).symm.trans h4`. Take `⟨y, hy⟩` from `(Lc.res_ker _).1 ((mul_eq_zero.1 h5).resolve_right hc)`. Rewrite using `[mem_std]`. Introduce `a`.

Distinguish the cases in `ha : a = ⟨0, hn⟩`. Substitute `ha` using the available equality. Simplify using `only [hdx, if_true] at hy`. Rewrite using `[mul_left_cancel₀ Lc.q_ne hy]`. Conclude with `y.2`.

Use `hs a` as an intermediate fact. Rewrite `this` using `[hdx, if_neg ha]`. Then use the resulting hypothesis. Introduce `h3`. Rewrite `h3` using `[mem_std]`. Establish `hs : ∀ a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a ∈ Lc.O`.

Introduce `a`. Rewrite using `[hdx]`. Use `split_ifs`. Conclude with `mul_mem (natCast_mem _ _) (h3 a)`. Conclude with `h3 a`.

Use `⟨(hf _).2 ((mem_std _).2 hs), (hx fun a => ⟨_, hs a⟩).trans ?_⟩` and prove the remaining obligations. Rewrite using `[(Lc.res_ker _).2 ⟨⟨_, h3 ⟨0, hn⟩⟩, by simp [hdx]⟩, zero_mul]`. Establish `key : ∀ g g' : GL (Fin n) Lc.K, (∀ x, (g : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) → (∀ x, (g' : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) → ∀ a b, ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) a b ∈ Lc.O`. Introduce `g g' hg hg' a b`. Establish `h3` using `(hg' _).2 (single_std b)`.

Establish `h4 : ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single b 1) ∈ Lc.std n`. Rewrite using `[← hg, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]`. Conclude with `h3`. Use `(mem_std _).1 h4 a` as an intermediate fact. Simplify using `using this`.

Establish `k1` using `key _ _ h2 hh`. Establish `k2` using `key _ _ hh h2`. Establish `inj : Function.Injective fun A : Matrix (Fin n) (Fin n) Lc.O => A.map Lc.O.subtype` using `Matrix.map_injective Subtype.val_injective`. Set `A : Matrix (Fin n) (Fin n) Lc.O` to `Matrix.of fun a b => ⟨_, k1 a b⟩`. Set `B : Matrix (Fin n) (Fin n) Lc.O` to `Matrix.of fun a b => ⟨_, k2 a b⟩`.

Establish `eA : A.map Lc.O.subtype = (((h₁ * d)⁻¹ * h : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)` using `rfl`. Establish `eB : B.map Lc.O.subtype = ((h⁻¹ * (h₁ * d) : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K)` using `rfl`. Use `⟨h₁, ⟨A, B, inj ?_, inj ?_⟩, hf, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc, mul_inv_cancel_left, inv_mul_cancel, Units.val_one]`.

Simplify using `only`. Rewrite using `[Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc, mul_inv_cancel_left, inv_mul_cancel, Units.val_one]`. Rewrite using `[← mul_assoc, ← inv_mul_eq_iff_eq_mul]`. Apply `Units.ext` to reduce the goal to its premises. Conclude with `eA.symm`.
-/
theorem frame_ker_decomp (hn : 0 < n) (p : LocF.PP Lc n) (h : GL (Fin n) Lc.K)
    (hh : ∀ x, (h : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) :
    ∃ (h₁ : GL (Fin n) Lc.K) (k : GL (Fin n) Lc.O), Lc.IsFrame n h₁ p.1.L ∧
      h = h₁ * (dq Lc.K hn (Units.mk0 _ Lc.q_ne) * Matrix.GeneralLinearGroup.map Lc.O.subtype k) := by
  obtain ⟨h₁, c, hc, hf, hx⟩ := exists_frame_adapted hn p
  set d := dq Lc.K hn (Units.mk0 _ Lc.q_ne) with hd
  have hdx : ∀ (x : Fin n → Lc.K) a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a =
      if a = ⟨0, hn⟩ then (q : Lc.K) * x a else x a := by
    intro x a
    show (Matrix.diagonal _).mulVec x a = _
    rw [Matrix.mulVec_diagonal]
    split_ifs with ha
    · subst ha; simp
    · simp [Function.update_of_ne ha]
  have h2 : ∀ x, ((h₁ * d : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n := by
    intro x
    rw [Units.val_mul, ← Matrix.mulVec_mulVec]
    constructor
    · rintro ⟨h3, h4⟩
      have hs := (mem_std _).1 ((hf _).1 h3)
      have h5 := (hx fun a => ⟨_, hs a⟩).symm.trans h4
      obtain ⟨y, hy⟩ := (Lc.res_ker _).1 ((mul_eq_zero.1 h5).resolve_right hc)
      rw [mem_std]
      intro a
      by_cases ha : a = ⟨0, hn⟩
      · subst ha
        simp only [hdx, if_true] at hy
        rw [mul_left_cancel₀ Lc.q_ne hy]
        exact y.2
      · have := hs a
        rwa [hdx, if_neg ha] at this
    · intro h3
      rw [mem_std] at h3
      have hs : ∀ a, (d : Matrix (Fin n) (Fin n) Lc.K).mulVec x a ∈ Lc.O := by
        intro a
        rw [hdx]
        split_ifs
        · exact mul_mem (natCast_mem _ _) (h3 a)
        · exact h3 a
      refine ⟨(hf _).2 ((mem_std _).2 hs), (hx fun a => ⟨_, hs a⟩).trans ?_⟩
      rw [(Lc.res_ker _).2 ⟨⟨_, h3 ⟨0, hn⟩⟩, by simp [hdx]⟩, zero_mul]
  have key : ∀ g g' : GL (Fin n) Lc.K,
      (∀ x, (g : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) →
      (∀ x, (g' : Matrix (Fin n) (Fin n) Lc.K).mulVec x ∈ p.ker ↔ x ∈ Lc.std n) →
      ∀ a b, ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) a b ∈ Lc.O := by
    intro g g' hg hg' a b
    have h3 := (hg' _).2 (single_std b)
    have h4 : ((g⁻¹ * g' : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K).mulVec (Pi.single b 1) ∈ Lc.std n := by
      rw [← hg, Matrix.mulVec_mulVec, ← Units.val_mul, mul_inv_cancel_left]
      exact h3
    have := (mem_std _).1 h4 a
    simpa using this
  have k1 := key _ _ h2 hh
  have k2 := key _ _ hh h2
  have inj : Function.Injective fun A : Matrix (Fin n) (Fin n) Lc.O => A.map Lc.O.subtype :=
    Matrix.map_injective Subtype.val_injective
  let A : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a b => ⟨_, k1 a b⟩
  let B : Matrix (Fin n) (Fin n) Lc.O := Matrix.of fun a b => ⟨_, k2 a b⟩
  have eA : A.map Lc.O.subtype = (((h₁ * d)⁻¹ * h : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) := rfl
  have eB : B.map Lc.O.subtype = ((h⁻¹ * (h₁ * d) : GL (Fin n) Lc.K) : Matrix (Fin n) (Fin n) Lc.K) := rfl
  refine ⟨h₁, ⟨A, B, inj ?_, inj ?_⟩, hf, ?_⟩
  · simp only
    rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel, Units.val_one]
  · simp only
    rw [Matrix.map_mul, eA, eB, ← Units.val_mul, Matrix.map_one _ (map_zero _) (map_one _), mul_assoc,
      mul_inv_cancel_left, inv_mul_cancel, Units.val_one]
  · rw [← mul_assoc, ← inv_mul_eq_iff_eq_mul]
    apply Units.ext
    exact eA.symm

end Lattice

open Formalism.MainNotions.product_first_zeroth_parts (Ow ten blk IntSpan tenM tenM_apply blk_ten wSh delSq_wSh)

/- English proof (translation)
Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Introduce `r hr`. Use `AddSubgroup.subset_closure ⟨r, Function.update f τ₀ (applyWord ℤ v (hw ℤ le_rfl (lam τ₀).natW)), hr, ?_, ?_⟩` and prove the remaining obligations.

Introduce `τ`. Distinguish the cases in `h : τ = τ₀`. Substitute `h` using the available equality. Rewrite using `[Function.update_self]`. Conclude with `Submodule.subset_span ⟨v, rfl⟩`.

Rewrite using `[Function.update_of_ne h]`. Conclude with `hf τ`. Use `congr 2`. Use function extensionality and compare the values at `τ`. Distinguish the cases in `h : τ = τ₀`.

Substitute `h` using the available equality. Simplify using `only [Function.update_self]`. Rewrite using `[← lclosedeq_applyWord_map, lclosedeq_hw_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Simplify using `only [Function.update_of_ne h]`. Consider the case `zero`.

Introduce `r _`. Rewrite using `[map_zero, ← tenM_apply, MultilinearMap.map_update_zero, smul_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz`. Introduce `r hr`.

Rewrite using `[map_add, ← tenM_apply, MultilinearMap.map_update_add, smul_add, tenM_apply, tenM_apply]`. Conclude with `add_mem (hy r hr) (hz r hr)`. Consider the case `smul a y _ hy`. Introduce `r hr`. Take `⟨s, hs, e⟩` from `hφ a`.

Rewrite using `[smul_eq_C_mul (a := a), map_mul, map_C, ← smul_eq_C_mul, ← tenM_apply, MultilinearMap.map_update_smul, smul_smul, e, ← map_mul, tenM_apply]`. Conclude with `hy _ (mul_mem hr hs)`.
-/
theorem ten_update_mem (D : D7) (w : D.what₂.places.Pl) {n : ℕ} (lam : D.what₂.Tau → DomWeight n)
    {R : Type} [CommRing R] (φ : R →+* ℂ) (hφ : ∀ a, ∃ s ∈ Ow D w, φ a = D.what₂.embLL s)
    [DecidableEq D.what₂.Tau] (f : D.what₂.Tau → MvPolynomial (Fin n × Fin n) ℤ) (hf : ∀ τ, f τ ∈ delSq ℤ n (lam τ))
    (τ₀ : D.what₂.Tau) (g : MvPolynomial (Fin n × Fin n) R) (hg : g ∈ delSq R n (lam τ₀)) :
    ∀ r ∈ Ow D w, D.what₂.embLL r •
      ten (Function.update (fun τ => map (Int.castRingHom ℂ) (f τ)) τ₀ (map φ g)) ∈ IntSpan D w lam := by
  induction hg using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    intro r hr
    refine AddSubgroup.subset_closure ⟨r, Function.update f τ₀ (applyWord ℤ v (hw ℤ le_rfl (lam τ₀).natW)), hr, ?_, ?_⟩
    · intro τ
      by_cases h : τ = τ₀
      · subst h
        rw [Function.update_self]
        exact Submodule.subset_span ⟨v, rfl⟩
      · rw [Function.update_of_ne h]; exact hf τ
    · congr 2
      funext τ
      by_cases h : τ = τ₀
      · subst h
        simp only [Function.update_self]
        rw [← lclosedeq_applyWord_map, lclosedeq_hw_map, ← lclosedeq_applyWord_map, lclosedeq_hw_map]
      · simp only [Function.update_of_ne h]
  | zero =>
    intro r _
    rw [map_zero, ← tenM_apply, MultilinearMap.map_update_zero, smul_zero]
    exact zero_mem _
  | add y z _ _ hy hz =>
    intro r hr
    rw [map_add, ← tenM_apply, MultilinearMap.map_update_add, smul_add, tenM_apply, tenM_apply]
    exact add_mem (hy r hr) (hz r hr)
  | smul a y _ hy =>
    intro r hr
    obtain ⟨s, hs, e⟩ := hφ a
    rw [smul_eq_C_mul (a := a), map_mul, map_C, ← smul_eq_C_mul, ← tenM_apply, MultilinearMap.map_update_smul,
      smul_smul, e, ← map_mul, tenM_apply]
    exact hy _ (mul_mem hr hs)

/- English proof (translation)
Proceed by induction on `hf using Submodule.span_induction with`. Consider the case `mem y hy`. Take `⟨v, rfl⟩` from `hy`. Use `Submodule.subset_span ⟨v, ?_⟩` and prove the remaining obligations. Simplify using `only`.

Rewrite using `[← lclosedeq_applyWord_map, lclosedeq_hw_map]`. Consider the case `zero => rw [map_zero]`. Conclude with `zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`. Conclude with `add_mem hy hz`.

Consider the case `smul a y _ hy`. Rewrite using `[smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]`. Conclude with `Submodule.smul_mem _ _ hy`.
-/
theorem map_int_mem (R : Type) [CommRing R] {n : ℕ} (lam : DomWeight n)
    {f : MvPolynomial (Fin n × Fin n) ℤ} (hf : f ∈ delSq ℤ n lam) : map (Int.castRingHom R) f ∈ delSq R n lam := by
  induction hf using Submodule.span_induction with
  | mem y hy =>
    obtain ⟨v, rfl⟩ := hy
    refine Submodule.subset_span ⟨v, ?_⟩
    simp only
    rw [← lclosedeq_applyWord_map, lclosedeq_hw_map]
  | zero => rw [map_zero]; exact zero_mem _
  | add y z _ _ hy hz => rw [map_add]; exact add_mem hy hz
  | smul a y _ hy =>
    rw [smul_eq_C_mul, map_mul, map_C, ← smul_eq_C_mul]
    exact Submodule.smul_mem _ _ hy

end GlobalTheory.LvT.KerLat

namespace GlobalTheory.LvT

open Formalism.BasicNotions Classical NumberField GlobalTheory.LvT MvPolynomial KerLat
open Formalism.MainNotions.product_first_zeroth_parts (Ow tops wsum ten blk nfAll CSpan IntSpan Nm_succ wSh cTw tenM tenM_apply blk_ten delSq_wSh)

/- English proof (translation)
Introduce `D u X i M Co _ w hw hs V v hv p y hy`. Take `⟨h, hh, z, hz, hy⟩` from `hy`. Establish `hhv` using `hh v`. Rewrite `hhv` using `[if_neg (fun h' => h'.2 hv)]`. Take `⟨h₁, k, hf, hdec⟩` from `frame_ker_decomp (D.R.N_pos i) (p.2 v) (h v) hhv`.

Set `ψ : (M.Lc v).K →+* ℂ` to `D.what₂.embLL.comp (Co.j w v)`. Set `φ : (M.Lc v).O →+* ℂ` to `ψ.comp (M.Lc v).O.subtype`. Establish `hφ : ∀ a, ∃ s ∈ Ow D w, φ a = D.what₂.embLL s` using `fun a => ⟨Co.j w v a, (Co.j_int w hw v a).2 a.2, rfl⟩`. Establish `hT : (X.A.T : ℂ) ≠ 0`. Use `(M.Lc v).q_ne` as an intermediate fact.

Introduce `h0`. Apply `this` to reduce the goal to its premises. Conclude with `(congrArg Nat.cast (Nat.cast_eq_zero.1 h0)).trans Nat.cast_zero`. Establish `hmv0 : ∀ g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K, Co.mv w g (X.fm.tauOf w v) = Matrix.GeneralLinearGroup.map ψ (g v)`. Introduce `g`.

Establish `: ∀ v', v' = v → Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v')) (g v') = Matrix.GeneralLinearGroup.map ψ (g v)`. Introduce and unpack `_ rfl`. Both sides reduce to the same expression. Simplify using `only [PtModel.Coord.mv, hs, if_true]`. Conclude with `this _ (Equiv.symm_apply_apply _ _)`.

Establish `hmv1 : ∀ τ, τ ≠ X.fm.tauOf w v → Co.mv w (Function.update h v h₁) τ = Co.mv w h τ`. Introduce `τ hτ`. Establish `hne : (X.fm.tauOf w).symm τ ≠ v` using `fun e => hτ (by rw [← e, Equiv.apply_symm_apply])`. Simplify using `only [PtModel.Coord.mv, Function.update_of_ne hne]`. Establish `hdq : Matrix.GeneralLinearGroup.map ψ (dq (M.Lc v).K (D.R.N_pos i) (Units.mk0 _ (M.Lc v).q_ne)) = dq ℂ (D.R.N_pos i) (Units.mk0 _ hT)`.

Apply `Units.ext` to reduce the goal to its premises. Use `show (Matrix.diagonal _).map ψ = Matrix.diagonal _`. Rewrite using `[Matrix.diagonal_map (map_zero _)]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Distinguish the cases in `ha : a = ⟨0, D.R.N_pos i⟩`. Substitute `ha` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Function.update_of_ne ha]`. Establish `hmov : ∀ (g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) f, Co.mov w g (ten f) = ten fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ) (f τ)` using `fun g f => blk_ten (fun τ => roundL ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ)) f`.

Establish `key : ∀ z ∈ IntSpan D w (X.fm.lam i), ∃ z' ∈ IntSpan D w (X.fm.lam i), ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • Co.mov w h z = Co.mov w (Function.update h v h₁) z'`. Introduce `z hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem z hz`. Take `⟨r, f, hr, hfm, rfl⟩` from `hz`.

Establish `e0 : delSq (M.Lc v).O _ (PtModel.lamT X i (X.fm.tauOf w v)) = delSq (M.Lc v).O _ (X.fm.lam i (X.fm.tauOf w v))` using `delSq_wSh _ _ _`. Establish `m1` using `map_int_mem (M.Lc v).O _ (hfm (X.fm.tauOf w v))`. Rewrite `m1` using `[← e0]`. Take `⟨g', hg', eg⟩` from `diag_step φ (D.R.N_pos i) _ X.A.T (Units.mk0 _ hT) rfl _ (roundAct_mem _ _ k _ m1)`. Rewrite `hg'` using `[e0]`.

Use `⟨_, ten_update_mem D w (X.fm.lam i) φ hφ f hfm _ g' hg' r hr, ?_⟩` and prove the remaining obligations. Rewrite using `[map_smul, map_smul, smul_comm, hmov, hmov]`. Use `congr 1`. Rewrite using `[← tenM_apply, ← tenM_apply, ← Function.update_eq_self (X.fm.tauOf w v) (fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w h τ) (map (Int.castRingHom ℂ) (f τ))), ← MultilinearMap.map_update_smul]`. Use `congr 1`.

Use function extensionality and compare the values at `τ`. Distinguish the cases in `hτ : τ = X.fm.tauOf w v`. Substitute `hτ` using the available equality. Simplify using `only [Function.update_self]`. Rewrite using `[hmv0, hmv0, Function.update_self, ← eg, ← roundAct_map, map_map, RingHom.ext_int (φ.comp _) (Int.castRingHom ℂ), hdec, map_mul, map_mul, hdq, (factSqActMul ℂ _ _ _ _ _).2, (factSqActMul ℂ _ _ _ _ _).2, ← roundL_coe ℂ _ _ (Matrix.GeneralLinearGroup.map ψ h₁)]`.

Simplify using `only [map_smul]`. Both sides reduce to the same expression. Simplify using `only [Function.update_of_ne hτ, hmv1 τ hτ]`. Consider the case `zero => exact ⟨0, zero_mem _, by simp⟩`. Consider the case `add a b _ _ ha hb`.

Take `⟨a', ha', ea⟩` from `ha`. Take `⟨b', hb', eb⟩` from `hb`. Conclude with `⟨a' + b', add_mem ha' hb', by rw [map_add, map_add, smul_add, ea, eb]⟩`. Consider the case `neg a _ ha`. Take `⟨a', ha', ea⟩` from `ha`.

Conclude with `⟨-a', neg_mem ha', by rw [map_neg, map_neg, smul_neg, ea]⟩`. Take `⟨z', hz', ez⟩` from `key z hz`. Use `⟨Function.update h v h₁, fun v' => ?_, z', hz', by rw [map_smul, hy, ez]⟩` and prove the remaining obligations. Distinguish the cases in `hv' : v' = v`. Substitute `hv'` using the available equality.

Rewrite using `[Function.update_self, if_pos ⟨hs, Finset.notMem_erase _ _⟩]`. Conclude with `hf`. Rewrite using `[Function.update_of_ne hv']`. Use `hh v'` as an intermediate fact. Simplify `this` using `only [Finset.mem_erase, ne_eq, hv', not_false_eq_true, true_and]`.
-/
theorem pow_smul_mem_valB_erase : ∀ (D : D7) (u : D.what₂.Word) (X : Ch D u) (i : ℕ) (M : PtModel X i) (Co : M.Coord), Co.Ok → ∀ w, OverT X w → X.fm.seenP w = true → ∀ (V : Finset X.A.vT) (v : X.A.vT), v ∈ V → ∀ p, ∀ y ∈ Co.valB w V p, ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • y ∈ Co.valB w (V.erase v) p := by
  intro D u X i M Co _ w hw hs V v hv p y hy
  obtain ⟨h, hh, z, hz, hy⟩ := hy
  have hhv := hh v
  rw [if_neg (fun h' => h'.2 hv)] at hhv
  obtain ⟨h₁, k, hf, hdec⟩ := frame_ker_decomp (D.R.N_pos i) (p.2 v) (h v) hhv
  let ψ : (M.Lc v).K →+* ℂ := D.what₂.embLL.comp (Co.j w v)
  let φ : (M.Lc v).O →+* ℂ := ψ.comp (M.Lc v).O.subtype
  have hφ : ∀ a, ∃ s ∈ Ow D w, φ a = D.what₂.embLL s :=
    fun a => ⟨Co.j w v a, (Co.j_int w hw v a).2 a.2, rfl⟩
  have hT : (X.A.T : ℂ) ≠ 0 := by
    have := (M.Lc v).q_ne
    intro h0
    apply this
    exact (congrArg Nat.cast (Nat.cast_eq_zero.1 h0)).trans Nat.cast_zero
  have hmv0 : ∀ g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K,
      Co.mv w g (X.fm.tauOf w v) = Matrix.GeneralLinearGroup.map ψ (g v) := by
    intro g
    have : ∀ v', v' = v → Matrix.GeneralLinearGroup.map (D.what₂.embLL.comp (Co.j w v')) (g v') =
        Matrix.GeneralLinearGroup.map ψ (g v) := by
      rintro _ rfl; rfl
    simp only [PtModel.Coord.mv, hs, if_true]
    exact this _ (Equiv.symm_apply_apply _ _)
  have hmv1 : ∀ τ, τ ≠ X.fm.tauOf w v → Co.mv w (Function.update h v h₁) τ = Co.mv w h τ := by
    intro τ hτ
    have hne : (X.fm.tauOf w).symm τ ≠ v := fun e => hτ (by rw [← e, Equiv.apply_symm_apply])
    simp only [PtModel.Coord.mv, Function.update_of_ne hne]
  have hdq : Matrix.GeneralLinearGroup.map ψ (dq (M.Lc v).K (D.R.N_pos i) (Units.mk0 _ (M.Lc v).q_ne)) =
      dq ℂ (D.R.N_pos i) (Units.mk0 _ hT) := by
    apply Units.ext
    show (Matrix.diagonal _).map ψ = Matrix.diagonal _
    rw [Matrix.diagonal_map (map_zero _)]
    congr 1
    funext a
    by_cases ha : a = ⟨0, D.R.N_pos i⟩
    · subst ha; simp
    · simp [Function.update_of_ne ha]
  have hmov : ∀ (g : ∀ v, GL (Fin (D.R.N i)) (M.Lc v).K) f, Co.mov w g (ten f) =
      ten fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ) (f τ) := fun g f =>
    blk_ten (fun τ => roundL ℂ _ (PtModel.lamT X i τ) (Co.mv w g τ)) f
  have key : ∀ z ∈ IntSpan D w (X.fm.lam i), ∃ z' ∈ IntSpan D w (X.fm.lam i),
      ((X.A.T : ℂ) ^ (PtModel.lamT X i (X.fm.tauOf w v)).w ⟨0, D.R.N_pos i⟩) • Co.mov w h z =
        Co.mov w (Function.update h v h₁) z' := by
    intro z hz
    induction hz using AddSubgroup.closure_induction with
    | mem z hz =>
      obtain ⟨r, f, hr, hfm, rfl⟩ := hz
      have e0 : delSq (M.Lc v).O _ (PtModel.lamT X i (X.fm.tauOf w v)) =
          delSq (M.Lc v).O _ (X.fm.lam i (X.fm.tauOf w v)) := delSq_wSh _ _ _
      have m1 := map_int_mem (M.Lc v).O _ (hfm (X.fm.tauOf w v))
      rw [← e0] at m1
      obtain ⟨g', hg', eg⟩ := diag_step φ (D.R.N_pos i) _ X.A.T (Units.mk0 _ hT) rfl _ (roundAct_mem _ _ k _ m1)
      rw [e0] at hg'
      refine ⟨_, ten_update_mem D w (X.fm.lam i) φ hφ f hfm _ g' hg' r hr, ?_⟩
      rw [map_smul, map_smul, smul_comm, hmov, hmov]
      congr 1
      rw [← tenM_apply, ← tenM_apply, ← Function.update_eq_self (X.fm.tauOf w v)
        (fun τ => roundAct ℂ _ (PtModel.lamT X i τ) (Co.mv w h τ) (map (Int.castRingHom ℂ) (f τ))),
        ← MultilinearMap.map_update_smul]
      congr 1
      funext τ
      by_cases hτ : τ = X.fm.tauOf w v
      · subst hτ
        simp only [Function.update_self]
        rw [hmv0, hmv0, Function.update_self, ← eg, ← roundAct_map, map_map,
          RingHom.ext_int (φ.comp _) (Int.castRingHom ℂ), hdec, map_mul, map_mul, hdq,
          (factSqActMul ℂ _ _ _ _ _).2, (factSqActMul ℂ _ _ _ _ _).2,
          ← roundL_coe ℂ _ _ (Matrix.GeneralLinearGroup.map ψ h₁)]
        simp only [map_smul]
        rfl
      · simp only [Function.update_of_ne hτ, hmv1 τ hτ]
    | zero => exact ⟨0, zero_mem _, by simp⟩
    | add a b _ _ ha hb =>
      obtain ⟨a', ha', ea⟩ := ha
      obtain ⟨b', hb', eb⟩ := hb
      exact ⟨a' + b', add_mem ha' hb', by rw [map_add, map_add, smul_add, ea, eb]⟩
    | neg a _ ha =>
      obtain ⟨a', ha', ea⟩ := ha
      exact ⟨-a', neg_mem ha', by rw [map_neg, map_neg, smul_neg, ea]⟩
  obtain ⟨z', hz', ez⟩ := key z hz
  refine ⟨Function.update h v h₁, fun v' => ?_, z', hz', by rw [map_smul, hy, ez]⟩
  by_cases hv' : v' = v
  · subst hv'
    rw [Function.update_self, if_pos ⟨hs, Finset.notMem_erase _ _⟩]
    exact hf
  · rw [Function.update_of_ne hv']
    have := hh v'
    simpa only [Finset.mem_erase, ne_eq, hv', not_false_eq_true, true_and] using this

end GlobalTheory.LvT
