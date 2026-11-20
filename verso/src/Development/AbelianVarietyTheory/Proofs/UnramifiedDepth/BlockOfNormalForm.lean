import Mathlib
import Formalism.LocalToGlobal.CharacterGerms.ContentLargeFromSupplies
import Formalism.LocalToGlobal.CharacterGerms.ContentZeroAt
import Formalism.LocalToGlobal.CharacterGerms.LatticeInclusionFormsInjective
import Formalism.LocalToGlobal.CharacterGerms.CoeffIterateZero
import Formalism.LocalToGlobal.CharacterGerms.CartesianBoundOnCurves
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ConstantCoeffSubstSame

noncomputable section
open scoped BigOperators
open Classical
open MvPowerSeries Formalism.IncomingBounds Formalism.UnitaryBoundIntegral Formalism.L2.FormalSeriesBounds

namespace GlobalTheory.MinorShiftJet

variable {K : Type} [Field K]

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using VF.Ge.one`. Consider the case `insert a s ha ih`. Rewrite using `[Finset.prod_insert ha]`. Conclude with `(h a (Finset.mem_insert_self a s)).mul_int (ih fun i hi => h i (Finset.mem_insert_of_mem hi))`.
-/
theorem ge_prod {V : VF K} {ι : Type} (s : Finset ι) (f : ι → K) (h : ∀ i ∈ s, V.Ge 0 (f i)) :
    V.Ge 0 (∏ i ∈ s, f i) := by
  induction s using Finset.induction_on with
  | empty => simpa using VF.Ge.one
  | insert a s ha ih =>
    rw [Finset.prod_insert ha]
    exact (h a (Finset.mem_insert_self a s)).mul_int (ih fun i hi => h i (Finset.mem_insert_of_mem hi))

/- English proof (translation)
Rewrite using `[Matrix.det_apply']`. Use `VF.Ge.sum fun σ _ => VF.Ge.mul_int ?_ (ge_prod _ _ fun i _ => h _ _)` and prove the remaining obligations. Apply the tactic sequence `rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]`. Simplify using `using VF.Ge.one`. Simplify using `using VF.Ge.one.neg`.
-/
theorem ge_det {V : VF K} {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ a b, V.Ge 0 (M a b)) :
    V.Ge 0 M.det := by
  rw [Matrix.det_apply']
  refine VF.Ge.sum fun σ _ => VF.Ge.mul_int ?_ (ge_prod _ _ fun i _ => h _ _)
  rcases Int.units_eq_one_or (Equiv.Perm.sign σ) with h1 | h1 <;> rw [h1]
  · simpa using VF.Ge.one
  · simpa using VF.Ge.one.neg

/- English proof (translation)
Establish `hne : M.det ≠ 0`. Introduce `h0`. Rewrite `hd` using `[h0, V.v.map_zero]`. Conclude with `WithTop.top_ne_zero hd`. Establish `hinv : V.Ge 0 (M.det)⁻¹`.

Establish `: V.v (M.det * (M.det)⁻¹) = 0` using `by rw [mul_inv_cancel₀ hne, V.v.map_one]`. Rewrite `this` using `[V.v.map_mul, hd, zero_add]`. Unfold `VF.Ge`. Rewrite using `[this]`. Both sides reduce to the same expression.

Use `⟨fun a b => (M.det)⁻¹ * M.adjugate a b, fun a b => hinv.mul_int ?_, fun c c' => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.adjugate_apply]`. Use `ge_det _ fun x y => ?_` and prove the remaining obligations. Rewrite using `[Matrix.updateRow_apply]`. Use `split_ifs`.

Rewrite using `[Pi.single_apply]`. Use `split_ifs exacts [VF.Ge.one, VF.Ge.zero _]`. Conclude with `h _ _`. Use `congrFun (congrFun (Matrix.mul_adjugate M) c) c'` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply]`.

Simplify using `only [mul_left_comm _ (M.det)⁻¹, ← Finset.mul_sum, this, Matrix.smul_apply, Matrix.one_apply, smul_eq_mul]`. Rewrite using `[← mul_assoc, inv_mul_cancel₀ hne, one_mul]`.
-/
theorem exists_int_inv {V : VF K} {n : ℕ} (M : Matrix (Fin n) (Fin n) K) (h : ∀ a b, V.Ge 0 (M a b))
    (hd : V.v M.det = 0) : ∃ N : Fin n → Fin n → K, (∀ a b, V.Ge 0 (N a b)) ∧
      ∀ c c', ∑ x, M c x * N x c' = if c = c' then 1 else 0 := by
  have hne : M.det ≠ 0 := by
    intro h0; rw [h0, V.v.map_zero] at hd; exact WithTop.top_ne_zero hd
  have hinv : V.Ge 0 (M.det)⁻¹ := by
    have : V.v (M.det * (M.det)⁻¹) = 0 := by rw [mul_inv_cancel₀ hne, V.v.map_one]
    rw [V.v.map_mul, hd, zero_add] at this
    unfold VF.Ge; rw [this]; rfl
  refine ⟨fun a b => (M.det)⁻¹ * M.adjugate a b, fun a b => hinv.mul_int ?_, fun c c' => ?_⟩
  · rw [Matrix.adjugate_apply]
    refine ge_det _ fun x y => ?_
    rw [Matrix.updateRow_apply]
    split_ifs
    · rw [Pi.single_apply]; split_ifs
      exacts [VF.Ge.one, VF.Ge.zero _]
    · exact h _ _
  · have := congrFun (congrFun (Matrix.mul_adjugate M) c) c'
    rw [Matrix.mul_apply] at this
    simp only [mul_left_comm _ (M.det)⁻¹, ← Finset.mul_sum, this, Matrix.smul_apply, Matrix.one_apply,
      smul_eq_mul]
    rw [← mul_assoc, inv_mul_cancel₀ hne, one_mul]

def IntCoeff (V : VF K) {σ : Type} (F : MvPowerSeries σ K) : Prop := ∀ μ, V.Ge 0 (coeff μ F)

/- English proof (translation)
Introduce `μ`. Rewrite using `[coeff_mul]`. Conclude with `VF.Ge.sum fun p _ => (hF _).mul_int (hG _)`.
-/
theorem IntCoeff.mul {V : VF K} {σ : Type} {F G : MvPowerSeries σ K} (hF : IntCoeff V F) (hG : IntCoeff V G) :
    IntCoeff V (F * G) := by
  intro μ
  rw [coeff_mul]
  exact VF.Ge.sum fun p _ => (hF _).mul_int (hG _)

/- English proof (translation)
Introduce `μ`. Rewrite using `[coeff_one]`. Use `split_ifs`. Use `exacts [VF.Ge.one, VF.Ge.zero _]`.
-/
theorem intCoeff_one (V : VF K) {σ : Type} : IntCoeff V (1 : MvPowerSeries σ K) := by
  intro μ
  rw [coeff_one]; split_ifs
  exacts [VF.Ge.one, VF.Ge.zero _]

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => simpa using intCoeff_one V`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul hF`.
-/
theorem IntCoeff.pow {V : VF K} {σ : Type} {F : MvPowerSeries σ K} (hF : IntCoeff V F) (n : ℕ) :
    IntCoeff V (F ^ n) := by
  induction n with
  | zero => simpa using intCoeff_one V
  | succ n ih => rw [pow_succ]; exact ih.mul hF

/- English proof (translation)
Introduce `μ`. Rewrite using `[map_sum]`. Use `VF.Ge.sum fun i _ => ?_` and prove the remaining obligations. Rewrite using `[coeff_smul, coeff_X]`. Use `(hc i).mul_int ?_` and prove the remaining obligations.

Use `split_ifs`. Use `exacts [VF.Ge.one, VF.Ge.zero _]`.
-/
theorem intCoeff_linear {V : VF K} {σ ι : Type} [Fintype ι] (c : ι → K) (hc : ∀ i, V.Ge 0 (c i)) (w : ι → σ) :
    IntCoeff V (∑ i, c i • (X (w i) : MvPowerSeries σ K)) := by
  intro μ
  rw [map_sum]
  refine VF.Ge.sum fun i _ => ?_
  rw [coeff_smul, coeff_X]
  refine (hc i).mul_int ?_
  split_ifs
  exacts [VF.Ge.one, VF.Ge.zero _]

/- English proof (translation)
Establish `: subst b F = rename f (subst a F)`. Rewrite using `[rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (HasSubst.X_comp f)]`. Use `congr 1`. Use function extensionality and compare the values at `s`. Rewrite using `[hb, rename_eq_subst]`.

Rewrite `h` using `[this]`. Establish `hm : m ∈ Set.range (Finsupp.mapDomain f)`. Assume the negation of the conclusion as `hc`. Conclude with `h (coeff_rename_eq_zero f _ hc)`. Take `⟨u, rfl⟩` from `hm`.

Introduce `x hx`. Take `⟨c, _, hc⟩` from `Finset.mem_image.1 (Finsupp.mapDomain_support hx)`. Conclude with `⟨c, hc.symm⟩`.
-/
theorem support_subst_rename {σ ι τ : Type} [Finite σ] [Finite ι] (f : ι → τ) (a : σ → MvPowerSeries ι K)
    (ha : ∀ s, constantCoeff (a s) = 0) (b : σ → MvPowerSeries τ K) (hb : ∀ s, b s = rename f (a s))
    (F : MvPowerSeries σ K) (m : τ →₀ ℕ) (h : coeff m (subst b F) ≠ 0) : ∀ x ∈ m.support, ∃ c, x = f c := by
  have : subst b F = rename f (subst a F) := by
    rw [rename_eq_subst, subst_comp_subst_apply (hasSubst_of_constantCoeff_zero ha) (HasSubst.X_comp f)]
    congr 1
    funext s
    rw [hb, rename_eq_subst]
  rw [this] at h
  have hm : m ∈ Set.range (Finsupp.mapDomain f) := by
    by_contra hc
    exact h (coeff_rename_eq_zero f _ hc)
  obtain ⟨u, rfl⟩ := hm
  intro x hx
  obtain ⟨c, _, hc⟩ := Finset.mem_image.1 (Finsupp.mapDomain_support hx)
  exact ⟨c, hc.symm⟩

/- English proof (translation)
Simplify using `[map_sum]`.
-/
theorem cc_linear {τ ι : Type} [Fintype ι] (c : ι → K) (w : ι → τ) :
    constantCoeff (∑ i, c i • (X (w i) : MvPowerSeries τ K)) = 0 := by
  simp [map_sum]

/- English proof (translation)
Establish `ha : ∀ x, constantCoeff (∑ c, E c x • (X (w c) : MvPowerSeries (PVar n) K)) = 0` using `fun x => cc_linear _ _`. Establish `hs` using `hasSubst_of_constantCoeff_zero ha`. Prove the components needed by the constructor for the conclusion. Introduce `m hm`. Use `support_subst_rename w (fun x => ∑ c, E c x • (X c : MvPowerSeries (Fin n) K)) (fun x => cc_linear (fun c => E c x) id) _ (fun x => ?_) _ m hm` and prove the remaining obligations.

Simplify using `[map_sum]`. Introduce `m hm`. Establish `e1 : ∑ b, B b • t (p b) = ∑ b, B b • (t (p b) - X (p b)) + ∑ b, B b • X (p b)`. Rewrite using `[← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun b _ => by rw [← smul_add, sub_add_cancel]`.

Establish `e2 : ∑ b, B b • (∑ c, E c (p b) • (X (w c) : MvPowerSeries (PVar n) K)) = X (w ρ)`. Simplify using `only [Finset.smul_sum, smul_smul]`. Rewrite using `[Finset.sum_comm]`. Simplify using `only [← Finset.sum_smul, mul_comm (B _), hE]`. Simplify using the standard rewrite rules.

Rewrite using `[e1, ← coe_substAlgHom hs, map_add, map_sum, map_sum]`. Simplify using `only [map_smul, substAlgHom_X]`. Rewrite using `[e2, map_add, map_sum, Finset.sum_eq_zero, zero_add]`. Introduce `b _`. Rewrite using `[coeff_smul, coe_substAlgHom, ordGE_subst _ ha (ht _) m (by omega), mul_zero]`.
-/
theorem diagCoord_subst {n : ℕ} {ι : Type} [Fintype ι] (w : Fin n → PVar n) (ρ : Fin n)
    (t : ι → MvPowerSeries ι K) (ht : ∀ x, OrdGE 2 (t x - X x)) (E : Fin n → ι → K) (p : Fin n → ι)
    (B : Fin n → K) (hE : ∀ c, ∑ b, E c (p b) * B b = if c = ρ then 1 else 0) :
    DiagCoord w ρ (subst (fun x => ∑ c, E c x • (X (w c) : MvPowerSeries (PVar n) K))
      (∑ b, B b • t (p b))) := by
  have ha : ∀ x, constantCoeff (∑ c, E c x • (X (w c) : MvPowerSeries (PVar n) K)) = 0 :=
    fun x => cc_linear _ _
  have hs := hasSubst_of_constantCoeff_zero ha
  constructor
  · intro m hm
    refine support_subst_rename w (fun x => ∑ c, E c x • (X c : MvPowerSeries (Fin n) K))
      (fun x => cc_linear (fun c => E c x) id) _ (fun x => ?_) _ m hm
    simp [map_sum]
  · intro m hm
    have e1 : ∑ b, B b • t (p b) = ∑ b, B b • (t (p b) - X (p b)) + ∑ b, B b • X (p b) := by
      rw [← Finset.sum_add_distrib]
      exact Finset.sum_congr rfl fun b _ => by rw [← smul_add, sub_add_cancel]
    have e2 : ∑ b, B b • (∑ c, E c (p b) • (X (w c) : MvPowerSeries (PVar n) K)) = X (w ρ) := by
      simp only [Finset.smul_sum, smul_smul]
      rw [Finset.sum_comm]
      simp only [← Finset.sum_smul, mul_comm (B _), hE]
      simp
    rw [e1, ← coe_substAlgHom hs, map_add, map_sum, map_sum]
    simp only [map_smul, substAlgHom_X]
    rw [e2, map_add, map_sum, Finset.sum_eq_zero, zero_add]
    intro b _
    rw [coeff_smul, coe_substAlgHom, ordGE_subst _ ha (ht _) m (by omega), mul_zero]

/- English proof (translation)
Take `⟨S, hS⟩` from `sysExists G (fun c x => if x = c then 1 else 0) (fun c x => by split_ifs; exacts [VF.Ge.one, VF.Ge.zero _]) (fun c x h => if_neg fun h' => h (by rw [h'])) (by`. Establish `: (Matrix.of fun c x : I => if x = c then (1 : K) else 0) = 1`. Use extensionality with `c x`. Simplify using `[Matrix.one_apply, eq_comm]`. Rewrite using `[this, Matrix.det_one, V.v.map_one])`.

Take `⟨t, ht, -⟩` from `tExistsUnique G S`. Use `⟨S, t, ht, fun x μ hμ => ?_⟩` and prove the remaining obligations. Rewrite using `[map_sub, sub_eq_zero, coeff_X]`. Establish `h` using `ht.2 x μ`. Establish `hal : ∀ c, S.al c 0 x = if x = c then 1 else 0`.

Introduce `c`. Unfold `Sys.al`. Rewrite using `[(S.curve c).2.1, hS]`. Both sides reduce to the same expression. Rewrite `h` using `[Finset.sum_range_succ', Finset.sum_eq_zero, zero_add]`.

Simplify using `only [hal, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ, if_true] at h`. Rewrite using `[h]`. Introduce `s _`. Use `Finset.sum_eq_zero fun c _ => ?_` and prove the remaining obligations. Rewrite using `[ordGE_pow (ordGE_one_of_const (ht.1 c)) _ μ, mul_zero]`.

Establish `h2` using `V.l_prime.two_le`. Establish `: V.l ≤ V.l ^ (s + 1)` using `Nat.le_self_pow (by omega) _`. Use linear arithmetic over natural numbers and integers.
-/
theorem exists_std_coords {V : VF K} {d : ℕ} {I J : Type} [Fintype I] [Fintype J] (G : Cart V d I J) :
    ∃ (S : Sys G) (t : I → MvPowerSeries I K), S.IsT t ∧ ∀ x, OrdGE 2 (t x - X x) := by
  obtain ⟨S, hS⟩ := sysExists G (fun c x => if x = c then 1 else 0)
    (fun c x => by split_ifs; exacts [VF.Ge.one, VF.Ge.zero _])
    (fun c x h => if_neg fun h' => h (by rw [h']))
    (by
      have : (Matrix.of fun c x : I => if x = c then (1 : K) else 0) = 1 := by
        ext c x; simp [Matrix.one_apply, eq_comm]
      rw [this, Matrix.det_one, V.v.map_one])
  obtain ⟨t, ht, -⟩ := tExistsUnique G S
  refine ⟨S, t, ht, fun x μ hμ => ?_⟩
  rw [map_sub, sub_eq_zero, coeff_X]
  have h := ht.2 x μ
  have hal : ∀ c, S.al c 0 x = if x = c then 1 else 0 := by
    intro c
    unfold Sys.al
    rw [(S.curve c).2.1, hS]; rfl
  rw [Finset.sum_range_succ', Finset.sum_eq_zero, zero_add] at h
  · simp only [hal, pow_zero, pow_one, ite_mul, one_mul, zero_mul, Finset.sum_ite_eq, Finset.mem_univ,
      if_true] at h
    rw [h]
  · intro s _
    refine Finset.sum_eq_zero fun c _ => ?_
    rw [ordGE_pow (ordGE_one_of_const (ht.1 c)) _ μ, mul_zero]
    have h2 := V.l_prime.two_le
    have : V.l ≤ V.l ^ (s + 1) := Nat.le_self_pow (by omega) _
    omega

variable {I : Fin 2 → Type} [∀ g, Fintype (I g)]

/- English proof (translation)
Apply the tactic sequence `fin_cases g <;> decide`.
-/
theorem one_sub_ne (g : Fin 2) : 1 - g ≠ g := by fin_cases g <;> decide

omit [∀ g, Fintype (I g)] in
/- English proof (translation)
Simplify using `[toW]`.
-/
theorem toW_same (g : Fin 2) (u : I g → K) (x : I g) : toW g u ⟨g, x⟩ = u x := by
  simp [toW]

omit [∀ g, Fintype (I g)] in
/- English proof (translation)
Simplify using `[toW, h]`.
-/
theorem toW_ne {g g' : Fin 2} (h : g' ≠ g) (u : I g → K) (x : I g') : toW g u ⟨g', x⟩ = 0 := by
  simp [toW, h]

/- English proof (translation)
Rewrite using `[Fintype.sum_sigma, Finset.sum_eq_single g]`. Simplify using `only [toW_same]`. Introduce `g' _ h`. Simplify using `[toW_ne h]`. Introduce `h`.

Conclude with `absurd (Finset.mem_univ _) h`.
-/
theorem sum_toW {M : Type} [CommRing M] (φ : K →+* M) (g : Fin 2) (u : I g → K) (f : WV I → M) :
    ∑ w, φ (toW g u w) * f w = ∑ x, φ (u x) * f ⟨g, x⟩ := by
  rw [Fintype.sum_sigma, Finset.sum_eq_single g]
  · simp only [toW_same]
  · intro g' _ h
    simp [toW_ne h]
  · intro h; exact absurd (Finset.mem_univ _) h

def rowForm {n : ℕ} (g : Fin 2) (E : Fin n → I g → K) (E' : Fin n → I (1 - g) → K) (ρ : Fin n) (w : WV I) :
    MvPowerSeries (PVar n) K :=
  (∑ c, toW g (E c) w • X (Sum.inl (ρ, c))) + ∑ b, toW (1 - g) (E' b) w • X (Sum.inr (ρ, b))

omit [∀ g, Fintype (I g)] in
/- English proof (translation)
Simplify using `[rowForm, map_sum]`.
-/
theorem cc_rowForm {n : ℕ} (g : Fin 2) (E : Fin n → I g → K) (E' : Fin n → I (1 - g) → K) (ρ : Fin n)
    (w : WV I) : constantCoeff (rowForm g E E' ρ w) = 0 := by
  simp [rowForm, map_sum]

/- English proof (translation)
Use `jetAt0_subst_linear (σ := Fin n × WV I) (τ := PVar n) (fun z => Sum.elim (fun u : Fin n × Fin n => if u.1 = z.1 then toW g (E u.2) z.2 else 0) (fun u : Fin n × Fin n => if u.1 = z.1 then toW (1 - g) (E' u.2) z.2 else 0)) Q G` as an intermediate fact. Use `this using 3` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `z`. Rewrite using `[Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]`. Simplify using `only [Sum.elim_inl, Sum.elim_inr, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq', Finset.mem_univ, if_true, rowForm]`.

Use `congr 1`. Use function extensionality and compare the values at `u`. Rewrite using `[Fintype.sum_prod_type]`. Break down `u with ⟨ρ, c⟩ | ⟨ρ, c⟩` into its components or cases. Use `all_goals`.

Simplify using `only [Sum.elim_inl, Sum.elim_inr, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul, Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]`. Rewrite using `[sum_toW]`.
-/
theorem jetAt0_rowForm {n : ℕ} (g : Fin 2) (E : Fin n → I g → K) (E' : Fin n → I (1 - g) → K)
    (Q : MvPolynomial (PVar n) K) (G : MvPowerSeries (Fin n × WV I) K) :
    jetAt0 Q (subst (fun z : Fin n × WV I => rowForm g E E' z.1 z.2) G) =
      jetAt0 (MvPolynomial.aeval (Sum.elim
        (fun u : Fin n × Fin n => ∑ x, MvPolynomial.C (E u.2 x) * MvPolynomial.X (u.1, (⟨g, x⟩ : WV I)))
        (fun u : Fin n × Fin n => ∑ x, MvPolynomial.C (E' u.2 x) *
          MvPolynomial.X (u.1, (⟨1 - g, x⟩ : WV I)))) Q) G := by
  have := jetAt0_subst_linear (σ := Fin n × WV I) (τ := PVar n) (fun z => Sum.elim
    (fun u : Fin n × Fin n => if u.1 = z.1 then toW g (E u.2) z.2 else 0)
    (fun u : Fin n × Fin n => if u.1 = z.1 then toW (1 - g) (E' u.2) z.2 else 0)) Q G
  convert this using 3
  · funext z
    rw [Fintype.sum_sum_type, Fintype.sum_prod_type, Fintype.sum_prod_type]
    simp only [Sum.elim_inl, Sum.elim_inr, ite_smul, zero_smul, Finset.sum_ite_irrel, Finset.sum_const_zero,
      Finset.sum_ite_eq', Finset.mem_univ, if_true, rowForm]
  · congr 1
    funext u
    rw [Fintype.sum_prod_type]
    rcases u with ⟨ρ, c⟩ | ⟨ρ, c⟩
    all_goals
      simp only [Sum.elim_inl, Sum.elim_inr, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul,
        Finset.sum_ite_irrel, Finset.sum_const_zero, Finset.sum_ite_eq, Finset.mem_univ, if_true]
      rw [sum_toW]

/- English proof (translation)
Establish `hs` using `hasSubst_of_constantCoeff_zero ha`. Unfold `rowCopy`. Rewrite using `[subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun w => by simp) hs]`. Simplify using `only [subst_X hs]`.
-/
theorem subst_rowCopy {n : ℕ} (a : Fin n × WV I → MvPowerSeries (PVar n) K)
    (ha : ∀ z, constantCoeff (a z) = 0) (ρ : Fin n) (F : MvPowerSeries (WV I) K) :
    subst a (rowCopy ρ F) = subst (fun w => a (ρ, w)) F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  unfold rowCopy
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun w => by simp) hs]
  simp only [subst_X hs]

/- English proof (translation)
Establish `hs` using `hasSubst_of_constantCoeff_zero ha`. Unfold `upG`. Rewrite using `[subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun w => by simp) hs]`. Simplify using `only [subst_X hs]`.
-/
theorem subst_upG {τ : Type} (a : WV I → MvPowerSeries τ K)
    (ha : ∀ z, constantCoeff (a z) = 0) (g : Fin 2) (F : MvPowerSeries (I g) K) :
    subst a (upG g F) = subst (fun x => a ⟨g, x⟩) F := by
  have hs := hasSubst_of_constantCoeff_zero ha
  unfold upG
  rw [subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun w => by simp) hs]
  simp only [subst_X hs]

/- English proof (translation)
Introduce `m hm x hx`. Take `⟨c, rfl⟩` from `support_subst_rename (Sum.map (fun c => (ρ, c)) (fun c => (ρ, c)) : Fin n ⊕ Fin n → PVar n) (fun w => (∑ c, toW g (E c) w • X (Sum.inl c)) + ∑ b, toW (1 - g) (E' b) w • X (Sum.inr b)) (fun w => by simp [map_sum]) _ (fun w => by simp [rowForm, map_sum]) h m hm x hx`. Apply the tactic sequence `rcases c with c | c <;> rfl`.
-/
theorem inRow_rowForm {n : ℕ} (g : Fin 2) (E : Fin n → I g → K) (E' : Fin n → I (1 - g) → K) (ρ : Fin n)
    (h : MvPowerSeries (WV I) K) : InRow ρ (subst (rowForm g E E' ρ) h) := by
  intro m hm x hx
  obtain ⟨c, rfl⟩ := support_subst_rename
    (Sum.map (fun c => (ρ, c)) (fun c => (ρ, c)) : Fin n ⊕ Fin n → PVar n)
    (fun w => (∑ c, toW g (E c) w • X (Sum.inl c)) + ∑ b, toW (1 - g) (E' b) w • X (Sum.inr b))
    (fun w => by simp [map_sum]) _ (fun w => by simp [rowForm, map_sum]) h m hm x hx
  rcases c with c | c <;> rfl

/- English proof (translation)
The claim follows from `Sum.map_injective.2 ⟨(Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn), (Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn)⟩`.
-/
theorem embV_injective {n0 n : ℕ} (hn : n0 ≤ n) : Function.Injective (embV hn) :=
  Sum.map_injective.2 ⟨(Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn),
    (Fin.castLE_injective hn).prodMap (Fin.castLE_injective hn)⟩

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[coeff_killCompl, Finsupp.embDomain_eq_mapDomain]`. Both sides reduce to the same expression.
-/
theorem restr_eq_killCompl {n0 n : ℕ} (hn : n0 ≤ n) (G : MvPowerSeries (PVar n) K) :
    restr hn G = killCompl ⟨embV hn, embV_injective hn⟩ G := by
  ext m
  rw [coeff_killCompl, Finsupp.embDomain_eq_mapDomain]; rfl

/- English proof (translation)
Establish `hrange : ∀ c : Fin n, c ∉ Set.range (Fin.castLE hn) → ¬ c.val < n0` using `fun c hc h => hc ⟨⟨c.val, h⟩, rfl⟩`. Rewrite using `[restr_eq_killCompl, Finset.sum_filter, ← Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) (fun ρ => subst (rowForm g E E' (Fin.castLE hn ρ)) h) _ (fun c hc => if_neg (hrange c hc)) (fun ρ => (if_pos ρ.2).symm), map_sum]`. Unfold `hRows`. Use `Finset.sum_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Apply the tactic sequence `have hs : HasSubst (Sum.elim (fun c => (X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) K)) (fun b => X (Sum.inr (ρ, b)))) := hasSubst_of_constantCoeff_zero fun u => by rcases u with u | u <;> simp`.

Unfold `hPullW`. Rewrite using `[killCompl_subst _ (cc_rowForm g E E' _), subst_comp_subst_apply (hasSubst_of_constantCoeff_zero fun w => by simp [map_sum]) hs]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Rewrite using `[← coe_substAlgHom hs]`.

Simplify using `only [rowForm, map_add, map_sum, map_smul, substAlgHom_X, Sum.elim_inl, Sum.elim_inr]`. Use `congr 1`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ (fun c hc => ?_) (fun c => ?_)` and prove the remaining obligations. Rewrite using `[killCompl_X_eq_zero, smul_zero]`.

Introduce and unpack `⟨⟨u1, u2⟩ | u, hu⟩`. Simplify using `only [Function.Embedding.coeFn_mk, embV, Sum.map_inl, Prod.map, Sum.inl.injEq, Prod.mk.injEq] at hu`. Conclude with `hc ⟨u2, hu.2⟩`. Simplify using `[embV] at hu`. Use `congr 1`.

Conclude with `(killCompl_X (e := ⟨embV hn, embV_injective hn⟩) (Sum.inl (ρ, c))).symm`. Use `symm`. Use `Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ (fun c hc => ?_) (fun c => ?_)` and prove the remaining obligations. Rewrite using `[killCompl_X_eq_zero, smul_zero]`. Introduce and unpack `⟨u | ⟨u1, u2⟩, hu⟩`.

Simplify using `[embV] at hu`. Simplify using `only [Function.Embedding.coeFn_mk, embV, Sum.map_inr, Prod.map, Sum.inr.injEq, Prod.mk.injEq] at hu`. Conclude with `hc ⟨u2, hu.2⟩`. Use `congr 1`. Conclude with `(killCompl_X (e := ⟨embV hn, embV_injective hn⟩) (Sum.inr (ρ, c))).symm`.
-/
theorem restr_rows {n0 n : ℕ} (hn : n0 ≤ n) (g : Fin 2) (E : Fin n → I g → K) (E' : Fin n → I (1 - g) → K)
    (h : MvPowerSeries (WV I) K) :
    restr hn (∑ ρ ∈ (Finset.univ : Finset (Fin n)).filter (fun ρ => ρ.val < n0), subst (rowForm g E E' ρ) h) =
      hRows n0 (hPullW h (fun c : Fin n0 => toW g (E (Fin.castLE hn c)))
        (fun b : Fin n0 => toW (1 - g) (E' (Fin.castLE hn b)))) := by
  have hrange : ∀ c : Fin n, c ∉ Set.range (Fin.castLE hn) → ¬ c.val < n0 :=
    fun c hc h => hc ⟨⟨c.val, h⟩, rfl⟩
  rw [restr_eq_killCompl, Finset.sum_filter, ← Fintype.sum_of_injective (Fin.castLE hn)
    (Fin.castLE_injective hn) (fun ρ => subst (rowForm g E E' (Fin.castLE hn ρ)) h) _
    (fun c hc => if_neg (hrange c hc)) (fun ρ => (if_pos ρ.2).symm), map_sum]
  unfold hRows
  refine Finset.sum_congr rfl fun ρ _ => ?_
  have hs : HasSubst (Sum.elim (fun c => (X (Sum.inl (ρ, c)) : MvPowerSeries (PVar n0) K))
      (fun b => X (Sum.inr (ρ, b)))) :=
    hasSubst_of_constantCoeff_zero fun u => by rcases u with u | u <;> simp
  unfold hPullW
  rw [killCompl_subst _ (cc_rowForm g E E' _), subst_comp_subst_apply
    (hasSubst_of_constantCoeff_zero fun w => by simp [map_sum]) hs]
  congr 1
  funext w
  rw [← coe_substAlgHom hs]
  simp only [rowForm, map_add, map_sum, map_smul, substAlgHom_X, Sum.elim_inl, Sum.elim_inr]
  congr 1
  · symm
    refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ (fun c hc => ?_) (fun c => ?_)
    · rw [killCompl_X_eq_zero, smul_zero]
      rintro ⟨⟨u1, u2⟩ | u, hu⟩
      · simp only [Function.Embedding.coeFn_mk, embV, Sum.map_inl, Prod.map, Sum.inl.injEq, Prod.mk.injEq] at hu
        exact hc ⟨u2, hu.2⟩
      · simp [embV] at hu
    · congr 1
      exact (killCompl_X (e := ⟨embV hn, embV_injective hn⟩) (Sum.inl (ρ, c))).symm
  · symm
    refine Fintype.sum_of_injective (Fin.castLE hn) (Fin.castLE_injective hn) _ _ (fun c hc => ?_) (fun c => ?_)
    · rw [killCompl_X_eq_zero, smul_zero]
      rintro ⟨u | ⟨u1, u2⟩, hu⟩
      · simp [embV] at hu
      · simp only [Function.Embedding.coeFn_mk, embV, Sum.map_inr, Prod.map, Sum.inr.injEq, Prod.mk.injEq] at hu
        exact hc ⟨u2, hu.2⟩
    · congr 1
      exact (killCompl_X (e := ⟨embV hn, embV_injective hn⟩) (Sum.inr (ρ, c))).symm

def letterDet (K : Type) [Field K] {n : ℕ} (g : Fin 2) (p : Fin n → I g) : MvPolynomial (Fin n × WV I) K :=
  Matrix.det (Matrix.of fun ρ c : Fin n => MvPolynomial.X (ρ, (⟨g, p c⟩ : WV I)))

/- English proof (translation)
Rewrite using `[letterDet, ← Matrix.det_transpose (Matrix.of A), RingHom.map_det, mul_comm, ← Matrix.det_mul]`. Use `congr 1`. Use `Matrix.ext fun ρ c => ?_` and prove the remaining obligations. Simplify using `only [Matrix.mul_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply, Matrix.transpose_apply, map_sum, Finset.sum_mul]`. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Simplify using `only [mul_ite, mul_one, mul_zero, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul, Finset.sum_ite_eq', Finset.mem_univ, if_true]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_change {n : ℕ} (g : Fin 2) (p : Fin n → I g) (A : Fin n → Fin n → K) :
    Matrix.det (Matrix.of fun ρ c : Fin n =>
      (∑ x : I g, MvPolynomial.C (∑ b, A c b * (if x = p b then (1 : K) else 0) : K) *
        MvPolynomial.X (ρ, (⟨g, x⟩ : WV I)) : MvPolynomial (Fin n × WV I) K)) =
      MvPolynomial.C (Matrix.of A).det * letterDet K g p := by
  rw [letterDet, ← Matrix.det_transpose (Matrix.of A), RingHom.map_det, mul_comm, ← Matrix.det_mul]
  congr 1
  refine Matrix.ext fun ρ c => ?_
  simp only [Matrix.mul_apply, Matrix.of_apply, RingHom.mapMatrix_apply, Matrix.map_apply,
    Matrix.transpose_apply, map_sum, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun b _ => ?_
  simp only [mul_ite, mul_one, mul_zero, apply_ite MvPolynomial.C, map_zero, ite_mul, zero_mul,
    Finset.sum_ite_eq', Finset.mem_univ, if_true]
  ring

/- English proof (translation)
Rewrite using `[V.v.map_mul]`. Conclude with `le_add_of_nonneg_left ha`.
-/
theorem v_le_of_int_mul {V : VF K} {a b : K} (ha : V.Ge 0 a) : V.v b ≤ V.v (a * b) := by
  rw [V.v.map_mul]
  exact le_add_of_nonneg_left ha

variable {V : VF K} {d : ℕ} [NeZero d] {J : Fin 2 → Type} [∀ g, Fintype (J g)]

/- English proof (translation)
Take `⟨-, ⟨-, w, hw, hew⟩, ⟨A, hA, heA⟩, ⟨Y, hY, hYd, hv⟩, -⟩` from `hM`. Use `choose S t hSt hlow using fun g => exists_std_coords (X.G g)`. Take `⟨Ab, Bb, hAb, hBb, hAB, hAA⟩` from `complete_rows V A (fun b c => w (p b) c) hA (fun b c => hw _ _) (fun c c' => by`. Rewrite using `[← hew c c']`. Simplify using `only [heA, Finset.sum_mul]`.

Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Use the proof step `simp) X.n hn le_rfl`. Take `⟨Z, hZ, hYZ⟩` from `exists_int_inv Y hY hYd`. Use `set E : Fin X.n → I g → K := fun c x => ∑ b, Ab c b * if x = p b then 1 else 0 with hE`.

Establish `hEp : ∀ c b, E c (p b) = Ab c b`. Introduce `c b`. Simplify using `[hE, hp.eq_iff]`. Establish `hvp : ∀ c b, v' c (p' b) = Y c b`. Introduce `c b`.

Simplify using `[hv, hp'.eq_iff]`. Establish `hEe : ∀ c, E (Fin.castLE hn c) = e c`. Introduce `c`. Use function extensionality and compare the values at `x`. Rewrite using `[heA]`.

Simplify using `only [hE, hAA]`. Establish `h0 : constantCoeff (X.hL g a (a + (i : ZMod d))) = 0`. Rewrite using `[← coeff_zero_eq_constantCoeff_apply]`. Conclude with `X.hL_axes _ _ _ 0 (Or.inl (by simp))`. Use `⟨S, t, hSt, fun ρ => subst (rowForm g E v' ρ) (X.hL g a (a + (i : ZMod d))), fun ρ => subst (fun x => ∑ c, E c x • (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K)) (∑ b, Bb b ρ • t g (p b)), fun ρ => subst (fun x => ∑ c, v' c x • (MvPowerSeries.X (Sum.inr (ρ, c)) …` and prove the remaining obligations.

Rewrite using `[constantCoeff_subst_same (cc_rowForm g E v' ρ), h0]`. Conclude with `diagCoord_subst _ ρ _ (hlow g) E p _ fun c => by simp only [hEp, hAB]`. Conclude with `diagCoord_subst _ ρ _ (hlow (1 - g)) v' p' _ fun c => by simp only [hvp, hYZ]`. Rewrite using `[restr_rows, ← hR]`. Simplify using `only [hEe]`.

Both sides reduce to the same expression. Establish `hup : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2))` using `hasSubst_of_constantCoeff_zero fun w => by`. Unfold `upG`. Rewrite using `[constantCoeff_subst_same (fun x => by simp)]`. Conclude with `(hSt w.1).1 w.2`.

Set `γ : Fin X.n → MvPowerSeries (WV I) K` to `fun ρ => if ρ.val < n0 then 1 else (∑ b, Bb b ρ • MvPowerSeries.X (⟨g, p b⟩ : WV I)) ^ (V.l ^ i * y) * (∑ b, Z b ρ • MvPowerSeries.X (⟨1 - g, p' b⟩ : WV I)) ^ y`. Use `⟨fun ρ => subst (fun w : WV I => upG w.1 (t w.1 w.2)) (γ ρ), fun ρ => ⟨γ ρ, ?_, rfl⟩, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `IntCoeff V (γ ρ)`. Simplify using `only [γ]`. Use `split_ifs`.

Conclude with `intCoeff_one V`. Conclude with `((intCoeff_linear _ (fun b => hBb b ρ) _).pow _).mul ((intCoeff_linear _ (fun b => hZ b ρ) _).pow _)`. Establish `hσ : ∀ z : Fin X.n × WV I, constantCoeff (rowForm g E v' z.1 z.2) = 0` using `fun z => cc_rowForm _ _ _ _ _`. Establish `hs` using `hasSubst_of_constantCoeff_zero hσ`. Establish `hF : BiF V.l i n0 X.n y (fun ρ => subst (rowForm g E v' ρ) (X.hL g a (a + (i : ZMod d)))) (fun ρ => subst (fun x => ∑ c, E c x • (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K)) (∑ b, Bb b ρ • t g (p b))) (fun ρ => subst (fun x => ∑ c, v' c x • (MvPowerSeries.X (S …`.

Substitute `(fun z : Fin X.n × WV I => rowForm g E v' z.1 z.2) (∏ ρ, (rowCopy ρ (subst (fun w : WV I => upG w.1 (t w.1 w.2)) (γ ρ)) * mvExp (rowCopy ρ (X.hL g a (a + (i : ZMod d)))))) := by` using the available equality. Rewrite using `[← coe_substAlgHom hs, map_prod]`. Unfold `BiF`. Use `Finset.prod_congr rfl fun ρ _ => ?_` and prove the remaining obligations. Establish `hρ` using `hasSubst_of_constantCoeff_zero (cc_rowForm g E v' ρ)`.

Rewrite using `[map_mul, coe_substAlgHom, subst_mvExp hσ _ (by`. Unfold `rowCopy`. Rewrite using `[constantCoeff_subst_same (fun x => by simp), h0]), subst_rowCopy _ hσ, subst_rowCopy _ hσ]`. Use `congr 1`. Express the relevant statement in the definitionally equal form `_ = subst (rowForm g E v' ρ) _`.

Rewrite using `[← coe_substAlgHom hup, ← coe_substAlgHom hρ]`. Simplify using `only [γ]`. Use `split_ifs`. Rewrite using `[map_one, map_one]`. Simplify using `only [map_mul, map_pow, map_sum, map_smul, substAlgHom_X]`.

Simplify using `only [coe_substAlgHom, subst_upG _ (cc_rowForm g E v' ρ)]`. Establish `e1 : (fun x => rowForm g E v' ρ ⟨g, x⟩) = fun x => ∑ c, E c x • (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K)`. Use function extensionality and compare the values at `x`. Simplify using `[rowForm, toW_same, toW_ne (one_sub_ne g).symm]`. Establish `e2 : (fun x => rowForm g E v' ρ ⟨1 - g, x⟩) = fun x => ∑ c, v' c x • (MvPowerSeries.X (Sum.inr (ρ, c)) : MvPowerSeries (PVar X.n) K)`.

Use function extensionality and compare the values at `x`. Simplify using `[rowForm, toW_same, toW_ne (one_sub_ne g)]`. Rewrite using `[e1, e2, ← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun x => cc_linear (fun c => E c x) _), ← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun x => cc_linear (fun c => v' c x) _)]`. Simplify using `only [map_sum, map_smul]`. Rewrite using `[hF, jetAt0_rowForm, map_mul, map_pow, map_pow, detL, detR, AlgHom.map_det, AlgHom.map_det]`.

Establish `d1` using `det_change g p Ab`. Establish `d2` using `det_change (1 - g) p' Y`. Simplify using `only [← hv] at d2`. Establish `d1' : ((MvPolynomial.aeval (Sum.elim (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (E u.2 x) * MvPolynomial.X (u.1, (⟨g, x⟩ : WV I))) (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (v' u.2 x) * MvPolynomial.X (u.1, (⟨1 - g, x⟩ : WV I)))) : MvPolynomial (PVar X.n) K →ₐ[K] _ …`. Rewrite using `[← d1]`.

Use `congr 1`. Use `Matrix.ext fun b c => ?_` and prove the remaining obligations. Simplify using `[hE]`. Establish `d2' : ((MvPolynomial.aeval (Sum.elim (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (E u.2 x) * MvPolynomial.X (u.1, (⟨g, x⟩ : WV I))) (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (v' u.2 x) * MvPolynomial.X (u.1, (⟨1 - g, x⟩ : WV I)))) : MvPolynomial (PVar X.n) K →ₐ[K] _ …`. Rewrite using `[← d2]`.

Use `congr 1`. Use `Matrix.ext fun b c => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[d1', d2', mul_pow, mul_pow, mul_mul_mul_comm, ← map_pow, ← map_pow, ← map_mul, jetAt0_C_mul]`. Conclude with `v_le_of_int_mul (((ge_det _ hAb).pow _).mul_int ((ge_det _ hY).pow _))`.
-/
theorem block_of_normal_form (X : RowData K V d I J) (g : Fin 2) (a : ZMod d) (i : ℕ)
    (p : Fin X.n → I g) (p' : Fin X.n → I (1 - g)) (hp : Function.Injective p) (hp' : Function.Injective p')
    (n0 : ℕ) (e : Fin n0 → I g → K) (v' : Fin X.n → I (1 - g) → K) (Φ : Fin X.n → Fin n0 → K)
    (hM : X.MConcl g a i (fun b x => if x = p b then 1 else 0) (fun b x => if x = p' b then 1 else 0)
      n0 e v' Φ) (hn : n0 ≤ X.n) (h1 : MvPowerSeries (PVar n0) K)
    (hR : hRows n0 (X.hGood g a i hn e v') = hP K V.l i n0 h1) :
    ∃ (S : ∀ g, Sys (X.G g)) (t : ∀ g, I g → MvPowerSeries (I g) K), (∀ g, (S g).IsT (t g)) ∧
      ∃ hr tt tt' : Fin X.n → MvPowerSeries (PVar X.n) K, BiHyp V.l i n0 X.n hn hr tt tt' h1 ∧
        ∀ y : ℕ, ∃ gr : Fin X.n → MvPowerSeries (WV I) K, (∀ ρ, gr ρ ∈ IntGerm V t) ∧
          V.v (ValOf X.hL (letterDet K g p ^ (V.l ^ i * y) * letterDet K (1 - g) p' ^ y)
            (fun _ => some (g, a, a + (i : ZMod d))) gr) ≤
          V.v (jetAt0 (detL K X.n ^ (V.l ^ i * y) * detR K X.n ^ y) (BiF V.l i n0 X.n y hr tt tt')) := by
  obtain ⟨-, ⟨-, w, hw, hew⟩, ⟨A, hA, heA⟩, ⟨Y, hY, hYd, hv⟩, -⟩ := hM
  choose S t hSt hlow using fun g => exists_std_coords (X.G g)
  obtain ⟨Ab, Bb, hAb, hBb, hAB, hAA⟩ := complete_rows V A (fun b c => w (p b) c) hA (fun b c => hw _ _)
    (fun c c' => by
      rw [← hew c c']
      simp only [heA, Finset.sum_mul]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => ?_
      simp) X.n hn le_rfl
  obtain ⟨Z, hZ, hYZ⟩ := exists_int_inv Y hY hYd
  set E : Fin X.n → I g → K := fun c x => ∑ b, Ab c b * if x = p b then 1 else 0 with hE
  have hEp : ∀ c b, E c (p b) = Ab c b := by
    intro c b
    simp [hE, hp.eq_iff]
  have hvp : ∀ c b, v' c (p' b) = Y c b := by
    intro c b
    simp [hv, hp'.eq_iff]
  have hEe : ∀ c, E (Fin.castLE hn c) = e c := by
    intro c; funext x
    rw [heA]; simp only [hE, hAA]
  have h0 : constantCoeff (X.hL g a (a + (i : ZMod d))) = 0 := by
    rw [← coeff_zero_eq_constantCoeff_apply]
    exact X.hL_axes _ _ _ 0 (Or.inl (by simp))
  refine ⟨S, t, hSt, fun ρ => subst (rowForm g E v' ρ) (X.hL g a (a + (i : ZMod d))),
    fun ρ => subst (fun x => ∑ c, E c x • (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K))
      (∑ b, Bb b ρ • t g (p b)),
    fun ρ => subst (fun x => ∑ c, v' c x • (MvPowerSeries.X (Sum.inr (ρ, c)) : MvPowerSeries (PVar X.n) K))
      (∑ b, Z b ρ • t (1 - g) (p' b)), ⟨fun ρ => inRow_rowForm _ _ _ _ _, fun ρ => ?_, fun ρ _ => ?_,
      fun ρ _ => ?_, ?_⟩, fun y => ?_⟩
  · rw [constantCoeff_subst_same (cc_rowForm g E v' ρ), h0]
  · exact diagCoord_subst _ ρ _ (hlow g) E p _ fun c => by simp only [hEp, hAB]
  · exact diagCoord_subst _ ρ _ (hlow (1 - g)) v' p' _ fun c => by simp only [hvp, hYZ]
  · rw [restr_rows, ← hR]
    simp only [hEe]
    rfl
  · have hup : HasSubst (fun w : WV I => upG w.1 (t w.1 w.2)) :=
      hasSubst_of_constantCoeff_zero fun w => by
        unfold upG
        rw [constantCoeff_subst_same (fun x => by simp)]
        exact (hSt w.1).1 w.2
    let γ : Fin X.n → MvPowerSeries (WV I) K := fun ρ => if ρ.val < n0 then 1 else
      (∑ b, Bb b ρ • MvPowerSeries.X (⟨g, p b⟩ : WV I)) ^ (V.l ^ i * y) *
        (∑ b, Z b ρ • MvPowerSeries.X (⟨1 - g, p' b⟩ : WV I)) ^ y
    refine ⟨fun ρ => subst (fun w : WV I => upG w.1 (t w.1 w.2)) (γ ρ), fun ρ => ⟨γ ρ, ?_, rfl⟩, ?_⟩
    · change IntCoeff V (γ ρ)
      simp only [γ]
      split_ifs
      · exact intCoeff_one V
      · exact ((intCoeff_linear _ (fun b => hBb b ρ) _).pow _).mul ((intCoeff_linear _ (fun b => hZ b ρ) _).pow _)
    have hσ : ∀ z : Fin X.n × WV I, constantCoeff (rowForm g E v' z.1 z.2) = 0 := fun z => cc_rowForm _ _ _ _ _
    have hs := hasSubst_of_constantCoeff_zero hσ
    have hF : BiF V.l i n0 X.n y (fun ρ => subst (rowForm g E v' ρ) (X.hL g a (a + (i : ZMod d))))
        (fun ρ => subst (fun x => ∑ c, E c x •
          (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K)) (∑ b, Bb b ρ • t g (p b)))
        (fun ρ => subst (fun x => ∑ c, v' c x •
          (MvPowerSeries.X (Sum.inr (ρ, c)) : MvPowerSeries (PVar X.n) K)) (∑ b, Z b ρ • t (1 - g) (p' b))) =
        subst (fun z : Fin X.n × WV I => rowForm g E v' z.1 z.2)
          (∏ ρ, (rowCopy ρ (subst (fun w : WV I => upG w.1 (t w.1 w.2)) (γ ρ)) *
            mvExp (rowCopy ρ (X.hL g a (a + (i : ZMod d)))))) := by
      rw [← coe_substAlgHom hs, map_prod]
      unfold BiF
      refine Finset.prod_congr rfl fun ρ _ => ?_
      have hρ := hasSubst_of_constantCoeff_zero (cc_rowForm g E v' ρ)
      rw [map_mul, coe_substAlgHom, subst_mvExp hσ _ (by
        unfold rowCopy
        rw [constantCoeff_subst_same (fun x => by simp), h0]), subst_rowCopy _ hσ, subst_rowCopy _ hσ]
      congr 1
      change _ = subst (rowForm g E v' ρ) _
      rw [← coe_substAlgHom hup, ← coe_substAlgHom hρ]
      simp only [γ]
      split_ifs
      · rw [map_one, map_one]
      · simp only [map_mul, map_pow, map_sum, map_smul, substAlgHom_X]
        simp only [coe_substAlgHom, subst_upG _ (cc_rowForm g E v' ρ)]
        have e1 : (fun x => rowForm g E v' ρ ⟨g, x⟩) = fun x => ∑ c, E c x •
            (MvPowerSeries.X (Sum.inl (ρ, c)) : MvPowerSeries (PVar X.n) K) := by
          funext x
          simp [rowForm, toW_same, toW_ne (one_sub_ne g).symm]
        have e2 : (fun x => rowForm g E v' ρ ⟨1 - g, x⟩) = fun x => ∑ c, v' c x •
            (MvPowerSeries.X (Sum.inr (ρ, c)) : MvPowerSeries (PVar X.n) K) := by
          funext x
          simp [rowForm, toW_same, toW_ne (one_sub_ne g)]
        rw [e1, e2,
          ← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun x => cc_linear (fun c => E c x) _),
          ← coe_substAlgHom (hasSubst_of_constantCoeff_zero fun x => cc_linear (fun c => v' c x) _)]
        simp only [map_sum, map_smul]
    rw [hF, jetAt0_rowForm, map_mul, map_pow, map_pow, detL, detR, AlgHom.map_det, AlgHom.map_det]
    have d1 := det_change g p Ab
    have d2 := det_change (1 - g) p' Y
    simp only [← hv] at d2
    have d1' : ((MvPolynomial.aeval (Sum.elim
        (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (E u.2 x) * MvPolynomial.X (u.1, (⟨g, x⟩ : WV I)))
        (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (v' u.2 x) *
          MvPolynomial.X (u.1, (⟨1 - g, x⟩ : WV I)))) : MvPolynomial (PVar X.n) K →ₐ[K] _).mapMatrix
        (Matrix.of fun b c : Fin X.n => MvPolynomial.X (Sum.inl (b, c)))).det =
        MvPolynomial.C (Matrix.of Ab).det * letterDet K g p := by
      rw [← d1]; congr 1; refine Matrix.ext fun b c => ?_; simp [hE]
    have d2' : ((MvPolynomial.aeval (Sum.elim
        (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (E u.2 x) * MvPolynomial.X (u.1, (⟨g, x⟩ : WV I)))
        (fun u : Fin X.n × Fin X.n => ∑ x, MvPolynomial.C (v' u.2 x) *
          MvPolynomial.X (u.1, (⟨1 - g, x⟩ : WV I)))) : MvPolynomial (PVar X.n) K →ₐ[K] _).mapMatrix
        (Matrix.of fun b c : Fin X.n => MvPolynomial.X (Sum.inr (b, c)))).det =
        MvPolynomial.C (Matrix.of Y).det * letterDet K (1 - g) p' := by
      rw [← d2]; congr 1; refine Matrix.ext fun b c => ?_; simp
    rw [d1', d2', mul_pow, mul_pow, mul_mul_mul_comm, ← map_pow, ← map_pow, ← map_mul, jetAt0_C_mul]
    exact v_le_of_int_mul (((ge_det _ hAb).pow _).mul_int ((ge_det _ hY).pow _))

end GlobalTheory.MinorShiftJet
