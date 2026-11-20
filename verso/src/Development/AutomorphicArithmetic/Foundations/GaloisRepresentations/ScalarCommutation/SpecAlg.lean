import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ScalarCommutation.TypeSlice
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjOne
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PCertProj
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PProjTrace
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.PTracePow

open Module UpperTheory.Gal.CertificateRingHomMap

namespace UpperTheory.Gal.Spc

private def diag {Q : Type} (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)] :
    (∀ q, End ℂ (W q)) →ₐ[ℂ] End ℂ (∀ q, W q) where
  toFun f := LinearMap.pi fun q => f q ∘ₗ LinearMap.proj q
  map_one' := LinearMap.ext fun _ => funext fun _ => rfl
  map_mul' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  map_zero' := LinearMap.ext fun _ => funext fun _ => rfl
  map_add' _ _ := LinearMap.ext fun _ => funext fun _ => rfl
  commutes' _ := LinearMap.ext fun _ => funext fun _ => rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem diag_apply {Q : Type} (W : Q → Type) [∀ q, AddCommGroup (W q)] [∀ q, Module ℂ (W q)]
    (f : ∀ q, End ℂ (W q)) (x : ∀ q, W q) (q : Q) : diag W f x q = f q (x q) := rfl

end UpperTheory.Gal.Spc

/- English proof (translation)
Unfold `wop Finsupp.sum`. Use `Commute.sum_left _ _ _ fun w _ => (Commute.list_prod_left _ _ ?_).smul_left _` and prove the remaining obligations. Introduce `x hx`. Take `⟨j, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `h j`.
-/
private theorem commute_wop_of_forall_commute {A J : Type} [Ring A] [Algebra ℂ A] (T : J → A) (Z : A)
    (h : ∀ j, Commute (T j) Z) (s : List J →₀ ℂ) : Commute (wop T s) Z := by
  unfold wop Finsupp.sum
  refine Commute.sum_left _ _ _ fun w _ => (Commute.list_prod_left _ _ ?_).smul_left _
  intro x hx
  obtain ⟨j, -, rfl⟩ := List.mem_map.1 hx
  exact h j

/- English proof (translation)
Simplify using `only [wop, Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]`. Both sides reduce to the same expression.
-/
private theorem algHom_map_wop {A B J : Type} [Ring A] [Ring B] [Algebra ℂ A] [Algebra ℂ B]
    (f : A →ₐ[ℂ] B) (T : J → A) (s : List J →₀ ℂ) : f (wop T s) = wop (fun j => f (T j)) s := by
  simp only [wop, Finsupp.sum, map_sum, map_smul, map_list_prod, List.map_map]
  rfl

/- English proof (translation)
Establish `hw : ∀ w : List J, (List.map T w).prod x = (List.map θ w).prod • x`. Introduce `w`. Proceed by induction on `w with`. Consider the case `nil => simp`. Consider the case `cons j w ih => simp [Module.End.mul_apply, ih, h, smul_smul, mul_comm]`.

Simplify using `only [wop, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hw, Finset.sum_smul, smul_smul, smul_eq_mul]`.
-/
private theorem wop_apply_eq_wop_smul_of_apply_eq_smul {M J : Type} [AddCommGroup M] [Module ℂ M] (T : J → End ℂ M) (θ : J → ℂ)
    (x : M) (h : ∀ j, T j x = θ j • x) (s : List J →₀ ℂ) : wop T s x = wop θ s • x := by
  have hw : ∀ w : List J, (List.map T w).prod x = (List.map θ w).prod • x := by
    intro w
    induction w with
    | nil => simp
    | cons j w ih => simp [Module.End.mul_apply, ih, h, smul_smul, mul_comm]
  simp only [wop, Finsupp.sum, LinearMap.sum_apply, LinearMap.smul_apply, hw,
    Finset.sum_smul, smul_smul, smul_eq_mul]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => intro Z _ _`. Simplify using the standard rewrite rules. Consider the case `cons j w ih`. Introduce `Z hZ hZP`.

Establish `hY : ∀ i, Commute (T i) ((List.map T w).prod * Z)` using `fun i => (Commute.list_prod_right _ _ (by`. Introduce `x hx`. Take `⟨k, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `hc i k)).mul_right (hZ i)`. Establish `hYP : Commute ((List.map T w).prod * Z) P` using `(Commute.list_prod_left _ _ (by`.

Introduce `x hx`. Take `⟨k, -, rfl⟩` from `List.mem_map.1 hx`. Conclude with `(hTP k))).mul_left hZP`. Take `⟨N, hN⟩` from `hN j`. Establish `hDY : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) ((List.map T w).prod * Z)` using `(hY j).sub_left (Algebra.commutes _ _)`.

Establish `hDP : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) P` using `(hTP j).sub_left (Algebra.commutes _ _)`. Establish `hnil : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z))`. Establish `h1 : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P)` using `⟨N + 1, by rw [hDP.mul_pow, hP.pow_succ_eq, pow_succ', mul_assoc, hN, mul_zero]⟩`. Conclude with `(Commute.mul_left hDY hYP.symm).isNilpotent_mul_right h1`. Establish `h0` using `(LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero`.

Establish `e1 : (T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z) = T j * ((List.map T w).prod * Z * P) - θ j • ((List.map T w).prod * Z * P)`. Rewrite using `[mul_assoc, ← hYP.eq]`. Simplify using `only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]`. Rewrite `h0` using `[e1, map_sub, map_smul, sub_eq_zero, smul_eq_mul]`. Simplify using `only [List.map_cons, List.prod_cons]`.

Rewrite using `[show T j * (List.map T w).prod * Z * P = T j * ((List.map T w).prod * Z * P) by`. Simplify using `only [mul_assoc], h0, ih Z hZ hZP, mul_assoc]`.
-/
private theorem trace_list_prod_mul_eq_prod_mul_trace_of_pow_sub_mul_zero {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (T : J → End ℂ M) (θ : J → ℂ) (hc : ∀ i j, Commute (T i) (T j)) (P : End ℂ M)
    (hP : IsIdempotentElem P) (hTP : ∀ j, Commute (T j) P)
    (hN : ∀ j, ∃ N : ℕ, (T j - algebraMap ℂ (End ℂ M) (θ j)) ^ N * P = 0) (w : List J) :
    ∀ Z : End ℂ M, (∀ j, Commute (T j) Z) → Commute Z P →
      LinearMap.trace ℂ M ((List.map T w).prod * Z * P) =
        (List.map θ w).prod * LinearMap.trace ℂ M (Z * P) := by
  induction w with
  | nil => intro Z _ _; simp
  | cons j w ih =>
    intro Z hZ hZP
    have hY : ∀ i, Commute (T i) ((List.map T w).prod * Z) := fun i =>
      (Commute.list_prod_right _ _ (by
        intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        exact hc i k)).mul_right (hZ i)
    have hYP : Commute ((List.map T w).prod * Z) P :=
      (Commute.list_prod_left _ _ (by
        intro x hx
        obtain ⟨k, -, rfl⟩ := List.mem_map.1 hx
        exact (hTP k))).mul_left hZP
    obtain ⟨N, hN⟩ := hN j
    have hDY : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) ((List.map T w).prod * Z) :=
      (hY j).sub_left (Algebra.commutes _ _)
    have hDP : Commute (T j - algebraMap ℂ (End ℂ M) (θ j)) P :=
      (hTP j).sub_left (Algebra.commutes _ _)
    have hnil : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z)) := by
      have h1 : IsNilpotent ((T j - algebraMap ℂ (End ℂ M) (θ j)) * P) :=
        ⟨N + 1, by rw [hDP.mul_pow, hP.pow_succ_eq, pow_succ', mul_assoc, hN, mul_zero]⟩
      exact (Commute.mul_left hDY hYP.symm).isNilpotent_mul_right h1
    have h0 := (LinearMap.isNilpotent_trace_of_isNilpotent hnil).eq_zero
    have e1 : (T j - algebraMap ℂ (End ℂ M) (θ j)) * P * ((List.map T w).prod * Z) =
        T j * ((List.map T w).prod * Z * P) - θ j • ((List.map T w).prod * Z * P) := by
      rw [mul_assoc, ← hYP.eq]
      simp only [sub_mul, Algebra.algebraMap_eq_smul_one, smul_mul_assoc, one_mul]
    rw [e1, map_sub, map_smul, sub_eq_zero, smul_eq_mul] at h0
    simp only [List.map_cons, List.prod_cons]
    rw [show T j * (List.map T w).prod * Z * P = T j * ((List.map T w).prod * Z * P) by
      simp only [mul_assoc], h0, ih Z hZ hZP, mul_assoc]

/- English proof (translation)
Establish `hw` using `fun w => trace_list_prod_mul_eq_prod_mul_trace_of_pow_sub_mul_zero T θ hc P hP hTP hN w Z hZ hZP`. Simplify using `only [wop, Finsupp.sum, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hw, smul_eq_mul]`. Conclude with `Finset.sum_congr rfl fun w _ => by ring`.
-/
private theorem trace_wop_mul_eq_wop_mul_trace_of_pow_sub_mul_zero {M J : Type} [AddCommGroup M] [Module ℂ M] [FiniteDimensional ℂ M]
    (T : J → End ℂ M) (θ : J → ℂ) (hc : ∀ i j, Commute (T i) (T j)) (P : End ℂ M)
    (hP : IsIdempotentElem P) (hTP : ∀ j, Commute (T j) P)
    (hN : ∀ j, ∃ N : ℕ, (T j - algebraMap ℂ (End ℂ M) (θ j)) ^ N * P = 0) (Z : End ℂ M)
    (hZ : ∀ j, Commute (T j) Z) (hZP : Commute Z P) (s : List J →₀ ℂ) :
    LinearMap.trace ℂ M (wop T s * Z * P) = wop θ s * LinearMap.trace ℂ M (Z * P) := by
  have hw := fun w => trace_list_prod_mul_eq_prod_mul_trace_of_pow_sub_mul_zero T θ hc P hP hTP hN w Z hZ hZP
  simp only [wop, Finsupp.sum, Finset.sum_mul, map_sum, smul_mul_assoc, map_smul, hw, smul_eq_mul]
  exact Finset.sum_congr rfl fun w _ => by ring

/- English proof (translation)
Establish `idem : e * e = e` using `h.idem`. Establish `eT : ∀ j, e * (T j * e) = T j * e` using `h.eT`. Establish `eu : e * (u * e) = u * e` using `h.eu`. Establish `TT : ∀ i j, T i * (T j * e) = T j * (T i * e)` using `h.TT`. Establish `uT : ∀ j, u * (T j * e) = T j * (u * e)` using `h.uT`.

Use `⟨fun i j => ?_, fun j => ?_, fun j => ?_, ?_, h.inv, idem⟩` and prove the remaining obligations. Use `show T i * e * (T j * e) = T j * e * (T i * e)`. Rewrite using `[mul_assoc, eT, mul_assoc, eT, TT]`. Use `show T j * e * (u * e) = u * e * (T j * e)`. Rewrite using `[mul_assoc, eu, mul_assoc, eT, uT]`.

Use `show T j * e * e = e * (T j * e)`. Rewrite using `[mul_assoc, idem, eT]`. Use `show u * e * e = e * (u * e)`. Rewrite using `[mul_assoc, idem, eu]`.
-/
private theorem commute_mul_and_idempotent_of_rel_mul {A J : Type} [Ring A] {T : J → A} {e u u' : A}
    (h : UpperTheory.Gal.Spc.Rel (fun x1 x2 : A => x1 * x2) T e u u') :
    (∀ i j, Commute (T i * e) (T j * e)) ∧ (∀ j, Commute (T j * e) (u * e)) ∧
      (∀ j, Commute (T j * e) e) ∧ Commute (u * e) e ∧ u' * (u * e) = e ∧ e * e = e := by
  have idem : e * e = e := h.idem
  have eT : ∀ j, e * (T j * e) = T j * e := h.eT
  have eu : e * (u * e) = u * e := h.eu
  have TT : ∀ i j, T i * (T j * e) = T j * (T i * e) := h.TT
  have uT : ∀ j, u * (T j * e) = T j * (u * e) := h.uT
  refine ⟨fun i j => ?_, fun j => ?_, fun j => ?_, ?_, h.inv, idem⟩
  · show T i * e * (T j * e) = T j * e * (T i * e)
    rw [mul_assoc, eT, mul_assoc, eT, TT]
  · show T j * e * (u * e) = u * e * (T j * e)
    rw [mul_assoc, eu, mul_assoc, eT, uT]
  · show T j * e * e = e * (T j * e)
    rw [mul_assoc, idem, eT]
  · show u * e * e = e * (u * e)
    rw [mul_assoc, idem, eu]

/- English proof (translation)
Proceed by induction on `w with`. Consider the case `nil => simp [hX]`. Consider the case `cons j w ih`. Take `⟨h1, h2⟩` from `ih`. Simplify using `only [List.map_cons, List.prod_cons]`.

Prove the components needed by the constructor for the conclusion. Combine the equalities or inequalities in the displayed calculation. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed {A J : Type} [Ring A] (T : J → A) (e : A)
    (eT : ∀ j, e * (T j * e) = T j * e) (X : A) (hX : e * X = X) (w : List J) :
    (List.map T w).prod * X = (List.map (fun j => T j * e) w).prod * X ∧
      e * ((List.map (fun j => T j * e) w).prod * X) = (List.map (fun j => T j * e) w).prod * X := by
  induction w with
  | nil => simp [hX]
  | cons j w ih =>
    obtain ⟨h1, h2⟩ := ih
    simp only [List.map_cons, List.prod_cons]
    constructor
    · calc T j * (List.map T w).prod * X = T j * ((List.map T w).prod * X) := mul_assoc _ _ _
        _ = T j * (e * ((List.map (fun j => T j * e) w).prod * X)) := by rw [h1, h2]
        _ = T j * e * (List.map (fun j => T j * e) w).prod * X := by simp only [mul_assoc]
    · calc e * (T j * e * (List.map (fun j => T j * e) w).prod * X)
          = e * (T j * e) * ((List.map (fun j => T j * e) w).prod * X) := by simp only [mul_assoc]
        _ = T j * e * (List.map (fun j => T j * e) w).prod * X := by rw [eT]; simp only [mul_assoc]

/- English proof (translation)
Simplify using `only [wop, Finsupp.sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]`. Conclude with `⟨Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).1], Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).2]⟩`.
-/
private theorem wop_mul_eq_wop_mul_right_mul_of_left_fixed {A J : Type} [Ring A] [Algebra ℂ A] (T : J → A) (e : A)
    (eT : ∀ j, e * (T j * e) = T j * e) (X : A) (hX : e * X = X) (s : List J →₀ ℂ) :
    wop T s * X = wop (fun j => T j * e) s * X ∧
      e * (wop (fun j => T j * e) s * X) = wop (fun j => T j * e) s * X := by
  simp only [wop, Finsupp.sum, Finset.sum_mul, Finset.mul_sum, smul_mul_assoc, mul_smul_comm]
  exact ⟨Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).1],
    Finset.sum_congr rfl fun w _ => by rw [(list_prod_map_mul_eq_prod_map_mul_right_of_left_fixed T e eT X hX w).2]⟩

/- English proof (translation)
Establish `h1 : ∀ m : ℕ, e * ((u * e) ^ m * e) = (u * e) ^ m * e` using `fun m => by`. Rewrite using `[← mul_assoc, (hc.symm.pow_right m).eq, mul_assoc, idem]`. Use `⟨h1 n, ?_⟩` and prove the remaining obligations. Proceed by induction on `n with`. Consider the case `zero => simp`.

Consider the case `succ m ih`. Rewrite using `[pow_succ', mul_assoc, ih, pow_succ', mul_assoc, mul_assoc, h1 m]`.
-/
private theorem pow_mul_eq_mul_pow_mul_of_idempotent_of_commute {A : Type} [Ring A] (e u : A) (idem : e * e = e)
    (hc : Commute (u * e) e) (n : ℕ) :
    e * ((u * e) ^ n * e) = (u * e) ^ n * e ∧ u ^ n * e = (u * e) ^ n * e := by
  have h1 : ∀ m : ℕ, e * ((u * e) ^ m * e) = (u * e) ^ m * e := fun m => by
    rw [← mul_assoc, (hc.symm.pow_right m).eq, mul_assoc, idem]
  refine ⟨h1 n, ?_⟩
  induction n with
  | zero => simp
  | succ m ih =>
    rw [pow_succ', mul_assoc, ih, pow_succ', mul_assoc, mul_assoc, h1 m]

/- English proof (translation)
Set `b : ∀ q, Basis (Fin (Module.finrank ℂ (W q))) ℂ (W q)` to `fun q => Module.finBasis ℂ (W q)`. Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]`. Simplify using `only [fun q => LinearMap.trace_eq_matrix_trace ℂ (b q) (f q), Matrix.trace, Matrix.diag, LinearMap.toMatrix_apply, Fintype.sum_sigma, Pi.basis_apply, Pi.basis_repr]`. Use `Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[UpperTheory.Gal.Spc.diag_apply, Pi.single_eq_same]`.
-/
private theorem trace_diag_eq_sum_trace {Q : Type} [Fintype Q] (W : Q → Type) [∀ q, AddCommGroup (W q)]
    [∀ q, Module ℂ (W q)] [∀ q, FiniteDimensional ℂ (W q)] (f : ∀ q, End ℂ (W q)) :
    LinearMap.trace ℂ (∀ q, W q) (UpperTheory.Gal.Spc.diag W f) = ∑ q, LinearMap.trace ℂ (W q) (f q) := by
  classical
  let b : ∀ q, Basis (Fin (Module.finrank ℂ (W q))) ℂ (W q) := fun q => Module.finBasis ℂ (W q)
  rw [LinearMap.trace_eq_matrix_trace ℂ (Pi.basis b)]
  simp only [fun q => LinearMap.trace_eq_matrix_trace ℂ (b q) (f q), Matrix.trace, Matrix.diag,
    LinearMap.toMatrix_apply, Fintype.sum_sigma, Pi.basis_apply, Pi.basis_repr]
  refine Finset.sum_congr rfl fun q _ => Finset.sum_congr rfl fun i _ => ?_
  rw [UpperTheory.Gal.Spc.diag_apply, Pi.single_eq_same]

open UpperTheory.Gal.Spc in
/- English proof (translation)
Introduce `Q J _ W _ _ _ T e u u' θ hrel hex`. Take `⟨q0, x0, hx0, hex0, hTx0⟩` from `hex`. Establish `F` using `fun q => commute_mul_and_idempotent_of_rel_mul (hrel q)`. Set `D` to `UpperTheory.Gal.Spc.diag W`. Set `t : J → ∀ q, End ℂ (W q)` to `fun j q => T q j * e q`.

Set `v : ∀ q, End ℂ (W q)` to `fun q => u q * e q`. Establish `hc : ∀ i j, Commute (D (t i)) (D (t j))` using `fun i j => Commute.map (show t i * t j = t j * t i from funext fun q => ((F q).1 i j).eq) D`. Establish `hV : ∀ j, Commute (D (t j)) (D v)` using `fun j => Commute.map (show t j * v = v * t j from funext fun q => ((F q).2.1 j).eq) D`. Establish `hE : ∀ j, Commute (D (t j)) (D e)` using `fun j => Commute.map (show t j * e = e * t j from funext fun q => ((F q).2.2.1 j).eq) D`. Establish `hVE : Commute (D v) (D e)` using `Commute.map (show v * e = e * v from funext fun q => (F q).2.2.2.1.eq) D`.

Establish `hUV : D u' * D v = D e`. Rewrite using `[← map_mul]`. Conclude with `congrArg D (funext fun q => (F q).2.2.2.2.1)`. Establish `hEi : IsIdempotentElem (D e)` using `by show D e * D e = D e`. Rewrite using `[← map_mul]`.

Conclude with `congrArg D (funext fun q => (F q).2.2.2.2.2)`. Take `⟨a, hθa, hPi, hN⟩` from `pProjOne_holds ℂ (End ℂ (∀ q, W q)) J (fun j => D (t j)) hc θ`. Establish `hTP : ∀ j, Commute (D (t j)) (wop (fun j => D (t j)) a)` using `fun j => (commute_wop_of_forall_commute _ _ (fun i => hc i j) a).symm`. Establish `hPE : Commute (wop (fun j => D (t j)) a) (D e)` using `commute_wop_of_forall_commute _ _ hE a`. Establish `hPV : Commute (wop (fun j => D (t j)) a) (D v)` using `commute_wop_of_forall_commute _ _ hV a`.

Establish `hTX : ∀ j, D (t j) (Pi.single q0 x0) = θ j • Pi.single q0 x0`. Introduce `j`. Use function extensionality and compare the values at `q`. Rewrite using `[UpperTheory.Gal.Spc.diag_apply, Pi.smul_apply]`. Distinguish the cases in `hq : q = q0`.

Substitute `hq` using the available equality. Simplify using `only [t, Pi.single_eq_same, Module.End.mul_apply, hex0, hTx0]`. Simplify using `[Pi.single_eq_of_ne hq]`. Establish `hEX : D e (Pi.single q0 x0) = Pi.single q0 x0`. Use function extensionality and compare the values at `q`.

Rewrite using `[UpperTheory.Gal.Spc.diag_apply]`. Distinguish the cases in `hq : q = q0`. Substitute `hq` using the available equality. Simplify using `only [Pi.single_eq_same, hex0]`. Simplify using `[Pi.single_eq_of_ne hq]`.

Establish `hPX : wop (fun j => D (t j)) a (Pi.single q0 x0) = Pi.single q0 x0`. Rewrite using `[wop_apply_eq_wop_smul_of_apply_eq_smul _ θ _ hTX a, hθa, one_smul]`. Establish `hQ0 : wop (fun j => D (t j)) a * D e ≠ 0`. Introduce `h`. Establish `h2` using `congrArg (fun f => f (Pi.single q0 x0)) h`.

Simplify using `only [Module.End.mul_apply, hEX, hPX, LinearMap.zero_apply] at h2`. Conclude with `hx0 (by simpa using congrFun h2 q0)`. Establish `hinj : ∀ x, D v ((wop (fun j => D (t j)) a * D e) x) = 0 → (wop (fun j => D (t j)) a * D e) x = 0`. Introduce `x hx`. Establish `h1 : D e ((wop (fun j => D (t j)) a * D e) x) = (wop (fun j => D (t j)) a * D e) x`.

Rewrite using `[← Module.End.mul_apply, ← mul_assoc, ← hPE.eq, mul_assoc, hEi.eq]`. Combine the equalities or inequalities in the displayed calculation. Take `⟨n, hn1, hn⟩` from `pTracePow_holds ℂ (∀ q, W q) _ (D v) (hPi.mul_of_commute hPE hEi) hQ0 (hPV.mul_left hVE.symm) hinj 1`. Use `⟨n, hn1, a, fun s hs => ?_⟩` and prove the remaining obligations. Establish `key : ∀ q, LinearMap.trace ℂ (W q) (wop (T q) (wmul a s) * (u q ^ n * e q)) = LinearMap.trace ℂ (W q) (wop (fun j => T q j * e q) a * (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q)))`.

Introduce `q`. Establish `h9` using `pow_mul_eq_mul_pow_mul_of_idempotent_of_commute (e q) (u q) (F q).2.2.2.2.2 (F q).2.2.2.1 n`. Establish `eT : ∀ j, e q * (T q j * e q) = T q j * e q` using `(hrel q).eT`. Establish `h8` using `wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h9.1 s`. Rewrite using `[wop_wmul, h9.2, mul_assoc, h8.1, (wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h8.2 a).1]`.

Rewrite using `[Finset.sum_congr rfl fun q _ => key q]`. Establish `ev : ∀ q (r : List J →₀ ℂ), (wop t r) q = wop (fun j => T q j * e q) r` using `fun q r => algHom_map_wop (Pi.evalAlgHom ℂ (fun q => End ℂ (W q)) q) t r`. Rewrite using `[← trace_diag_eq_sum_trace W (fun q => wop (fun j => T q j * e q) a * (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q)))]`. Establish `hD : (fun q => wop (fun j => T q j * e q) a * (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q))) = wop t a * (wop t s * (v ^ n * e))`. Use function extensionality and compare the values at `q`.

Rewrite using `[Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.pow_apply, ev, ev]`. Rewrite using `[hD]`. Use `show LinearMap.trace ℂ _ (D (wop t a * (wop t s * (v ^ n * e)))) ≠ 0`. Rewrite using `[map_mul D, map_mul D, map_mul D, map_pow D, algHom_map_wop D t a, algHom_map_wop D t s, LinearMap.trace_mul_comm ℂ]`. Establish `hZ : ∀ j, Commute (D (t j)) (D v ^ n * D e)` using `fun j => ((hV j).pow_right n).mul_right (hE j)`.

Establish `hZP : Commute (D v ^ n * D e) (wop (fun j => D (t j)) a)` using `(hPV.pow_right n).symm.mul_left hPE.symm`. Rewrite using `[trace_wop_mul_eq_wop_mul_trace_of_pow_sub_mul_zero (fun j => D (t j)) θ hc _ hPi hTP hN (D v ^ n * D e) hZ hZP s]`. Use `mul_ne_zero hs ?_` and prove the remaining obligations. Rewrite using `[LinearMap.trace_mul_comm ℂ, (hVE.pow_left n).eq, ← mul_assoc]` and apply the resulting hypothesis.
-/
theorem UpperTheory.Gal.Spc.specAlg :
    UpperTheory.Gal.Spc.SpecAlg := by
  classical
  intro Q J _ W _ _ _ T e u u' θ hrel hex
  obtain ⟨q0, x0, hx0, hex0, hTx0⟩ := hex
  have F := fun q => commute_mul_and_idempotent_of_rel_mul (hrel q)
  let D := UpperTheory.Gal.Spc.diag W
  let t : J → ∀ q, End ℂ (W q) := fun j q => T q j * e q
  let v : ∀ q, End ℂ (W q) := fun q => u q * e q
  have hc : ∀ i j, Commute (D (t i)) (D (t j)) := fun i j =>
    Commute.map (show t i * t j = t j * t i from funext fun q => ((F q).1 i j).eq) D
  have hV : ∀ j, Commute (D (t j)) (D v) := fun j =>
    Commute.map (show t j * v = v * t j from funext fun q => ((F q).2.1 j).eq) D
  have hE : ∀ j, Commute (D (t j)) (D e) := fun j =>
    Commute.map (show t j * e = e * t j from funext fun q => ((F q).2.2.1 j).eq) D
  have hVE : Commute (D v) (D e) :=
    Commute.map (show v * e = e * v from funext fun q => (F q).2.2.2.1.eq) D
  have hUV : D u' * D v = D e := by
    rw [← map_mul]
    exact congrArg D (funext fun q => (F q).2.2.2.2.1)
  have hEi : IsIdempotentElem (D e) := by
    show D e * D e = D e
    rw [← map_mul]
    exact congrArg D (funext fun q => (F q).2.2.2.2.2)
  obtain ⟨a, hθa, hPi, hN⟩ := pProjOne_holds ℂ (End ℂ (∀ q, W q)) J (fun j => D (t j)) hc θ
  have hTP : ∀ j, Commute (D (t j)) (wop (fun j => D (t j)) a) := fun j =>
    (commute_wop_of_forall_commute _ _ (fun i => hc i j) a).symm
  have hPE : Commute (wop (fun j => D (t j)) a) (D e) := commute_wop_of_forall_commute _ _ hE a
  have hPV : Commute (wop (fun j => D (t j)) a) (D v) := commute_wop_of_forall_commute _ _ hV a
  have hTX : ∀ j, D (t j) (Pi.single q0 x0) = θ j • Pi.single q0 x0 := by
    intro j
    funext q
    rw [UpperTheory.Gal.Spc.diag_apply, Pi.smul_apply]
    by_cases hq : q = q0
    · subst hq
      simp only [t, Pi.single_eq_same, Module.End.mul_apply, hex0, hTx0]
    · simp [Pi.single_eq_of_ne hq]
  have hEX : D e (Pi.single q0 x0) = Pi.single q0 x0 := by
    funext q
    rw [UpperTheory.Gal.Spc.diag_apply]
    by_cases hq : q = q0
    · subst hq
      simp only [Pi.single_eq_same, hex0]
    · simp [Pi.single_eq_of_ne hq]
  have hPX : wop (fun j => D (t j)) a (Pi.single q0 x0) = Pi.single q0 x0 := by
    rw [wop_apply_eq_wop_smul_of_apply_eq_smul _ θ _ hTX a, hθa, one_smul]
  have hQ0 : wop (fun j => D (t j)) a * D e ≠ 0 := by
    intro h
    have h2 := congrArg (fun f => f (Pi.single q0 x0)) h
    simp only [Module.End.mul_apply, hEX, hPX, LinearMap.zero_apply] at h2
    exact hx0 (by simpa using congrFun h2 q0)
  have hinj : ∀ x, D v ((wop (fun j => D (t j)) a * D e) x) = 0 →
      (wop (fun j => D (t j)) a * D e) x = 0 := by
    intro x hx
    have h1 : D e ((wop (fun j => D (t j)) a * D e) x) = (wop (fun j => D (t j)) a * D e) x := by
      rw [← Module.End.mul_apply, ← mul_assoc, ← hPE.eq, mul_assoc, hEi.eq]
    calc (wop (fun j => D (t j)) a * D e) x = D e ((wop (fun j => D (t j)) a * D e) x) := h1.symm
      _ = D u' (D v ((wop (fun j => D (t j)) a * D e) x)) :=
        (congrArg (fun f : End ℂ (∀ q, W q) => f ((wop (fun j => D (t j)) a * D e) x)) hUV).symm
      _ = 0 := by rw [hx, map_zero]
  obtain ⟨n, hn1, hn⟩ := pTracePow_holds ℂ (∀ q, W q) _ (D v) (hPi.mul_of_commute hPE hEi) hQ0
    (hPV.mul_left hVE.symm) hinj 1
  refine ⟨n, hn1, a, fun s hs => ?_⟩
  have key : ∀ q, LinearMap.trace ℂ (W q) (wop (T q) (wmul a s) * (u q ^ n * e q)) =
      LinearMap.trace ℂ (W q) (wop (fun j => T q j * e q) a *
        (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q))) := by
    intro q
    have h9 := pow_mul_eq_mul_pow_mul_of_idempotent_of_commute (e q) (u q) (F q).2.2.2.2.2 (F q).2.2.2.1 n
    have eT : ∀ j, e q * (T q j * e q) = T q j * e q := (hrel q).eT
    have h8 := wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h9.1 s
    rw [wop_wmul, h9.2, mul_assoc, h8.1, (wop_mul_eq_wop_mul_right_mul_of_left_fixed (T q) (e q) eT _ h8.2 a).1]
  rw [Finset.sum_congr rfl fun q _ => key q]
  have ev : ∀ q (r : List J →₀ ℂ), (wop t r) q = wop (fun j => T q j * e q) r := fun q r =>
    algHom_map_wop (Pi.evalAlgHom ℂ (fun q => End ℂ (W q)) q) t r
  rw [← trace_diag_eq_sum_trace W (fun q => wop (fun j => T q j * e q) a *
    (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q)))]
  have hD : (fun q => wop (fun j => T q j * e q) a *
      (wop (fun j => T q j * e q) s * ((u q * e q) ^ n * e q))) = wop t a * (wop t s * (v ^ n * e)) := by
    funext q
    rw [Pi.mul_apply, Pi.mul_apply, Pi.mul_apply, Pi.pow_apply, ev, ev]
  rw [hD]
  show LinearMap.trace ℂ _ (D (wop t a * (wop t s * (v ^ n * e)))) ≠ 0
  rw [map_mul D, map_mul D, map_mul D, map_pow D, algHom_map_wop D t a, algHom_map_wop D t s,
    LinearMap.trace_mul_comm ℂ]
  have hZ : ∀ j, Commute (D (t j)) (D v ^ n * D e) := fun j => ((hV j).pow_right n).mul_right (hE j)
  have hZP : Commute (D v ^ n * D e) (wop (fun j => D (t j)) a) :=
    (hPV.pow_right n).symm.mul_left hPE.symm
  rw [trace_wop_mul_eq_wop_mul_trace_of_pow_sub_mul_zero (fun j => D (t j)) θ hc _ hPi hTP hN (D v ^ n * D e) hZ hZP s]
  refine mul_ne_zero hs ?_
  rwa [LinearMap.trace_mul_comm ℂ, (hVE.pow_left n).eq, ← mul_assoc]
