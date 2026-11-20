import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.TransposeVariables
import Formalism.ThetaLogCoordinates.DualWeylCoordinates.DualWeylProofs.ABridge
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.BideterminantMem
import Formalism.GradedWeylDivisibility.FockSpaceTableaux.LHwrowLemmas

open MvPolynomial

noncomputable section

namespace Formalism.InvariantFactorPaths.ColumnFamilies

open Formalism.GradedWeylDivisibility

def qn_delta (n : ℕ) : MvPolynomial (Fin n × Fin n) ℤ := lpMinor ℤ n (le_refl n) (le_refl n)

/- English proof (translation)
Unfold `qn_delta lpMinor transposeVariables`. Rewrite using `[AlgHom.map_det, ← Matrix.det_transpose]`. Use `congr 1`. Use extensionality with `p q`. Simplify using `[genMat]`.
-/
theorem qn_T_det (n : ℕ) : transposeVariables ℤ n (genMat ℤ n).det = qn_delta n := by
  unfold qn_delta lpMinor transposeVariables
  rw [AlgHom.map_det, ← Matrix.det_transpose]
  congr 1
  ext p q
  simp [genMat]

/- English proof (translation)
Use `set M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) := Matrix.of fun p q : Fin n => X (Fin.castLE (le_refl n) p, Fin.castLE (le_refl n) q) with hM`. Establish `h1 : initMinor ℤ J (le_refl n) = (M.submatrix J id).det` using `rfl`. Distinguish the cases in `hJ : Function.Injective J`. Establish `hb : Function.Bijective J` using `Finite.injective_iff_bijective.mp hJ`. Use `⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤˣ) : ℤ), ?_⟩` and prove the remaining obligations.

Establish `h2` using `Matrix.det_permute (Equiv.ofBijective J hb) M`. Rewrite using `[h1]`. Establish `h3 : M.submatrix J id = M.submatrix (Equiv.ofBijective J hb) id` using `rfl`. Rewrite using `[h3, h2, zsmul_eq_mul]`. Simplify using `[qn_delta, lpMinor, hM]`.

Use `⟨0, ?_⟩` and prove the remaining obligations. Rewrite using `[zero_smul, h1]`. Unfold `Function.Injective at hJ`. Use `push Not at hJ`. Take `⟨p, p', hpp, hne⟩` from `hJ`.

Conclude with `Matrix.det_zero_of_row_eq hne (by funext q; simp [Matrix.submatrix, hpp])`.
-/
theorem qn_full (n : ℕ) (J : Fin n → Fin n) :
    ∃ ε : ℤ, initMinor ℤ J (le_refl n) = ε • qn_delta n := by
  classical
  set M : Matrix (Fin n) (Fin n) (MvPolynomial (Fin n × Fin n) ℤ) :=
    Matrix.of fun p q : Fin n => X (Fin.castLE (le_refl n) p, Fin.castLE (le_refl n) q) with hM
  have h1 : initMinor ℤ J (le_refl n) = (M.submatrix J id).det := rfl
  by_cases hJ : Function.Injective J
  · have hb : Function.Bijective J := Finite.injective_iff_bijective.mp hJ
    refine ⟨((Equiv.Perm.sign (Equiv.ofBijective J hb) : ℤˣ) : ℤ), ?_⟩
    have h2 := Matrix.det_permute (Equiv.ofBijective J hb) M
    rw [h1]
    have h3 : M.submatrix J id = M.submatrix (Equiv.ofBijective J hb) id := rfl
    rw [h3, h2, zsmul_eq_mul]
    simp [qn_delta, lpMinor, hM]
  · refine ⟨0, ?_⟩
    rw [zero_smul, h1]
    unfold Function.Injective at hJ
    push Not at hJ
    obtain ⟨p, p', hpp, hne⟩ := hJ
    exact Matrix.det_zero_of_row_eq hne (by funext q; simp [Matrix.submatrix, hpp])

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `qn_full s J`.
-/
theorem qn_full' (n s : ℕ) (hs : s ≤ n) (J : Fin s → Fin n) (h : s = n) :
    ∃ ε : ℤ, initMinor ℤ J hs = ε • qn_delta n := by
  subst h
  exact qn_full s J

/- English proof (translation)
Rewrite using `[standardMonomialSpanDomain ℤ n n _, Submodule.span_le]`. Introduce and unpack `f ⟨K, sz, hsz, I, hshape, rfl⟩`. Establish `h1 : 0 < shapeDeg sz (lastIdx n)` using `by rw [hshape]; exact Nat.succ_pos _`. Unfold `shapeDeg at h1`. Take `⟨k0, hk0⟩` from `Finset.card_pos.mp h1`.

Establish `hk0' : (lastIdx n).val < sz k0` using `(Finset.mem_filter.mp hk0).2`. Establish `hsz0 : sz k0 = n`. Use `hsz k0` as an intermediate fact. Establish `h2 : (lastIdx n).val = n - 1` using `rfl`. Use linear arithmetic over natural numbers and integers.

Take `⟨ε, hε⟩` from `qn_full' n (sz k0) (hsz k0) (I k0) hsz0`. Establish `hrest : (∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k)) ∈ dualWeyl ℤ n n ν'`. Use `dualWeyl_of_eq (dualWeyl_prod (Finset.univ.erase k0) (fun k => initW n (sz k)) (fun k => initMinor ℤ (I k) (hsz k)) (fun k _ => initMinor_mem (I k) (hsz k))) ?_` and prove the remaining obligations. Establish `h3` using `sum_initW_eq_shapeDeg (n := n) sz`. Rewrite `h3` using `[hshape, ← Finset.add_sum_erase _ _ (Finset.mem_univ k0)]`.

Use function extensionality and compare the values at `t`. Establish `h4` using `congrFun h3 t`. Establish `h5 : initW n (sz k0) t = 1`. Unfold `initW`. Rewrite using `[hsz0, if_pos t.isLt]`.

Rewrite `h4` using `[Pi.add_apply, h5]`. Use linear arithmetic over natural numbers and integers. Use `⟨ε • ∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k), Submodule.smul_mem _ _ hrest, ?_⟩` and prove the remaining obligations. Rewrite using `[LinearMap.mulLeft_apply]`. Unfold `bideterminant`.

Rewrite using `[← Finset.mul_prod_erase _ _ (Finset.mem_univ k0), hε, mul_smul_comm, smul_mul_assoc]`.
-/
theorem qn_divide (n : ℕ) [NeZero n] (ν' : Fin n → ℕ) :
    dualWeyl ℤ n n (fun t => ν' t + 1) ≤
      (dualWeyl ℤ n n ν').map (LinearMap.mulLeft ℤ (qn_delta n)) := by
  classical
  rw [standardMonomialSpanDomain ℤ n n _, Submodule.span_le]
  rintro f ⟨K, sz, hsz, I, hshape, rfl⟩
  have h1 : 0 < shapeDeg sz (lastIdx n) := by rw [hshape]; exact Nat.succ_pos _
  unfold shapeDeg at h1
  obtain ⟨k0, hk0⟩ := Finset.card_pos.mp h1
  have hk0' : (lastIdx n).val < sz k0 := (Finset.mem_filter.mp hk0).2
  have hsz0 : sz k0 = n := by
    have := hsz k0
    have h2 : (lastIdx n).val = n - 1 := rfl
    omega
  obtain ⟨ε, hε⟩ := qn_full' n (sz k0) (hsz k0) (I k0) hsz0
  have hrest : (∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k)) ∈ dualWeyl ℤ n n ν' := by
    refine dualWeyl_of_eq (dualWeyl_prod (Finset.univ.erase k0) (fun k => initW n (sz k))
      (fun k => initMinor ℤ (I k) (hsz k)) (fun k _ => initMinor_mem (I k) (hsz k))) ?_
    have h3 := sum_initW_eq_shapeDeg (n := n) sz
    rw [hshape, ← Finset.add_sum_erase _ _ (Finset.mem_univ k0)] at h3
    funext t
    have h4 := congrFun h3 t
    have h5 : initW n (sz k0) t = 1 := by
      unfold initW
      rw [hsz0, if_pos t.isLt]
    rw [Pi.add_apply, h5] at h4
    omega
  refine ⟨ε • ∏ k ∈ Finset.univ.erase k0, initMinor ℤ (I k) (hsz k), Submodule.smul_mem _ _ hrest, ?_⟩
  rw [LinearMap.mulLeft_apply]
  unfold bideterminant
  rw [← Finset.mul_prod_erase _ _ (Finset.mem_univ k0), hε, mul_smul_comm, smul_mul_assoc]

/- English proof (translation)
Proceed by induction on `N with`. Consider the case `zero => simpa using h`. Consider the case `succ N ih`. Introduce `f hf`. Take `⟨g, hg, rfl⟩` from `qn_divide n (fun t => ν0 t + N) hf`.

Establish `hx` using `Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℤ (qn_delta n)) (ih hg)`. Rewrite `hx` using `[Submodule.map_span]`. Use `Submodule.span_mono ?_ hx` and prove the remaining obligations. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Conclude with `⟨i, by simp only [LinearMap.mulLeft_apply]; ring⟩`.
-/
theorem qn_divideN (n : ℕ) [NeZero n] (ν0 : Fin n → ℕ) {ι : Type} (Q : ι → MvPolynomial (Fin n × Fin n) ℤ)
    (h : dualWeyl ℤ n n ν0 ≤ Submodule.span ℤ (Set.range Q)) (N : ℕ) :
    dualWeyl ℤ n n (fun t => ν0 t + N) ≤ Submodule.span ℤ (Set.range fun i => qn_delta n ^ N * Q i) := by
  induction N with
  | zero => simpa using h
  | succ N ih =>
    intro f hf
    obtain ⟨g, hg, rfl⟩ := qn_divide n (fun t => ν0 t + N) hf
    have hx := Submodule.mem_map_of_mem (f := LinearMap.mulLeft ℤ (qn_delta n)) (ih hg)
    rw [Submodule.map_span] at hx
    refine Submodule.span_mono ?_ hx
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    exact ⟨i, by simp only [LinearMap.mulLeft_apply]; ring⟩

def qn_nu {n : ℕ} [NeZero n] (mu : Fin n → ℤ) : Fin n → ℕ :=
  fun t => (mu t + ((-(mu (lastIdx n))).toNat : ℤ)).toNat

/- English proof (translation)
Establish `h2 : (lastIdx n).val = n - 1` using `rfl`. Use `a.isLt` as an intermediate fact. Conclude with `Fin.le_def.mpr (by omega)`.
-/
theorem qn_le_last {n : ℕ} [NeZero n] (a : Fin n) : a ≤ lastIdx n := by
  have h2 : (lastIdx n).val = n - 1 := rfl
  have := a.isLt
  exact Fin.le_def.mpr (by omega)

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h` using `hmu (qn_le_last t)`. Unfold `qn_nu qa_nu`. Use linear arithmetic over natural numbers and integers.
-/
theorem qn_nu_eq {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    qn_nu mu = fun t => qa_nu mu t + (mu (lastIdx n)).toNat := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu qa_nu
  omega

/- English proof (translation)
Use function extensionality and compare the values at `t`. Establish `h` using `hmu (qn_le_last t)`. Unfold `qn_nu`. Use linear arithmetic over natural numbers and integers.
-/
theorem qn_nu_cast {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    (fun a => ((qn_nu mu a : ℕ) : ℤ)) = fun a => mu a + ((-(mu (lastIdx n))).toNat : ℤ) := by
  funext t
  have h := hmu (qn_le_last t)
  unfold qn_nu
  omega

/- English proof (translation)
Introduce `a b hab`. Establish `h` using `hmu hab`. Unfold `qn_nu`. Use linear arithmetic over natural numbers and integers.
-/
theorem qn_nu_anti {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) : Antitone (qn_nu mu) := by
  intro a b hab
  have h := hmu hab
  unfold qn_nu
  omega

/- English proof (translation)
Rewrite using `[qa_brkPol_eq, map_mul, map_pow, qn_T_det]`. Use `congr 1`. Conclude with `transposeVariables_involutive ℤ n (qa_P ℤ I)`.
-/
theorem qn_T_brkPol {n : ℕ} [NeZero n] (mu : Fin n → ℤ) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) = qn_delta n ^ (mu (lastIdx n)).toNat * qa_P ℤ I := by
  rw [qa_brkPol_eq, map_mul, map_pow, qn_T_det]
  congr 1
  exact transposeVariables_involutive ℤ n (qa_P ℤ I)

/- English proof (translation)
Rewrite using `[qn_T_brkPol]`. Establish `h1 : qn_delta n ∈ dualWeyl ℤ n n (initW n n)` using `initMinor_mem (R := ℤ) (fun p : Fin n => Fin.castLE (le_refl n) p) (le_refl n)`. Use `dualWeyl_of_eq (dualWeyl_mul (dualWeyl_pow h1 (mu (lastIdx n)).toNat) (tableauBideterminant_mem_dualWeyl ℤ hmu I)) ?_` and prove the remaining obligations. Rewrite using `[qn_nu_eq hmu]`. Use function extensionality and compare the values at `t`.

Simplify using `[initW]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem bracket_mem_dualWeyl {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) (I : TIdx mu) :
    transposeVariables ℤ n (brkPol mu I) ∈ dualWeyl ℤ n n (qn_nu mu) := by
  rw [qn_T_brkPol]
  have h1 : qn_delta n ∈ dualWeyl ℤ n n (initW n n) :=
    initMinor_mem (R := ℤ) (fun p : Fin n => Fin.castLE (le_refl n) p) (le_refl n)
  refine dualWeyl_of_eq (dualWeyl_mul (dualWeyl_pow h1 (mu (lastIdx n)).toNat) (tableauBideterminant_mem_dualWeyl ℤ hmu I)) ?_
  rw [qn_nu_eq hmu]
  funext t
  simp [initW]
  ring

/- English proof (translation)
Rewrite using `[qn_nu_eq hmu]`. Simplify using `only [qn_T_brkPol]`. Conclude with `qn_divideN n (qa_nu mu) (fun I : TIdx mu => qa_P ℤ I) (le_of_eq (dualWeyl_eq_span_tableauBideterminant ℤ hmu)) _`.
-/
theorem dualWeyl_le_span_bracket {n : ℕ} [NeZero n] {mu : Fin n → ℤ} (hmu : Dominant mu) :
    dualWeyl ℤ n n (qn_nu mu) ≤ Submodule.span ℤ (Set.range fun I : TIdx mu => transposeVariables ℤ n (brkPol mu I)) := by
  rw [qn_nu_eq hmu]
  simp only [qn_T_brkPol]
  exact qn_divideN n (qa_nu mu) (fun I : TIdx mu => qa_P ℤ I) (le_of_eq (dualWeyl_eq_span_tableauBideterminant ℤ hmu)) _

/- English proof (translation)
Rewrite using `[qn_T_brkPol, map_mul, map_pow]`. Establish `h1 : eval (idFrame ℤ n n) (qn_delta n) = 1` using `eval_idPoint_lpMinor ℤ n (le_refl n) (le_refl n)`. Rewrite using `[h1, one_pow, one_mul]`. Unfold `qa_P`. Rewrite using `[map_prod]`.

Use `Finset.prod_eq_one fun c _ => ?_` and prove the remaining obligations. Establish `h2 : initMinor ℤ (qa_row (canT mu) c) (colH_le mu c) = lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)`. Unfold `initMinor lpMinor`. Use `congr 1`. Use extensionality with `p q`.

Simplify using `[qa_row, qa_can_emb]`. Rewrite using `[h2]`. Conclude with `eval_idPoint_lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)`.
-/
theorem eval_id_bracket_canonical {n : ℕ} [NeZero n] (mu : Fin n → ℤ) :
    eval (idFrame ℤ n n) (transposeVariables ℤ n (brkPol mu (canT mu))) = 1 := by
  rw [qn_T_brkPol, map_mul, map_pow]
  have h1 : eval (idFrame ℤ n n) (qn_delta n) = 1 := eval_idPoint_lpMinor ℤ n (le_refl n) (le_refl n)
  rw [h1, one_pow, one_mul]
  unfold qa_P
  rw [map_prod]
  refine Finset.prod_eq_one fun c _ => ?_
  have h2 : initMinor ℤ (qa_row (canT mu) c) (colH_le mu c) =
      lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c) := by
    unfold initMinor lpMinor
    congr 1
    ext p q
    simp [qa_row, qa_can_emb]
  rw [h2]
  exact eval_idPoint_lpMinor ℤ (colH mu c) (colH_le mu c) (colH_le mu c)

end Formalism.InvariantFactorPaths.ColumnFamilies
