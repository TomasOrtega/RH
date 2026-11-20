import Mathlib
import Development.WeilBound.RepresentationTheoryGL.DiscreteSeries.DiscreteSeriesCovers.EquivariantSections.EquivSection
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.AdjointInverseTranslate.ConjugatedGeneratorGlRelation

noncomputable section

open Finset Matrix MeasureTheory

namespace GlobalTheory.CompanionTheory.ActEquivK

open ReciprocityTheory.ChartRestriction.DS ReciprocityTheory.ChartRestriction.DS.S7 PositivityTheory.RgDs.K

attribute [local instance] Matrix.normedAddCommGroup Matrix.normedSpace

variable {n : ℕ} {ε : Fin n → Bool}

/- English proof (translation)
The claim follows from `Matrix.inv_eq_left_inv (signature_matrix_sq ε)`.
-/
lemma jm_inv (ε : Fin n → Bool) : (Formalism.REAL.Jm ε)⁻¹ = Formalism.REAL.Jm ε :=
  Matrix.inv_eq_left_inv (signature_matrix_sq ε)

/- English proof (translation)
Use `⟨?_, signature_matrix_sq ε⟩` and prove the remaining obligations. Unfold `Formalism.REAL.Jm`. Rewrite using `[Matrix.diagonal_conjTranspose]`. Use `congr 1`. Use function extensionality and compare the values at `a`.

Apply the tactic sequence `by_cases h : ε a = true <;> simp [h]`.
-/
lemma hinvol (ε : Fin n → Bool) : AAInvW.HInvol (Formalism.REAL.Jm ε) := by
  refine ⟨?_, signature_matrix_sq ε⟩
  unfold Formalism.REAL.Jm
  rw [Matrix.diagonal_conjTranspose]
  congr 1
  funext a
  by_cases h : ε a = true <;> simp [h]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Establish `h1 : Formalism.QuantumDeterminants.hpart1 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart1 ε (Matrix.single a b 1)`. Unfold `Formalism.QuantumDeterminants.hpart1 Formalism.REAL.cpart1`. Rewrite using `[jm_inv]`. Establish `h2 : Formalism.QuantumDeterminants.hpart2 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart2 ε (Matrix.single a b 1)`.

Unfold `Formalism.QuantumDeterminants.hpart2 Formalism.REAL.cpart2`. Rewrite using `[jm_inv]`. Unfold `Formalism.QuantumDeterminants.EabH`. Rewrite using `[h1, h2]`. Both sides reduce to the same expression.
-/
lemma eabH_eq (a b : Fin n) (f : Matrix (Fin n) (Fin n) ℂ → ℂ) :
    Formalism.QuantumDeterminants.EabH (Formalism.REAL.Jm ε) a b f = Formalism.REAL.Eab ε a b f := by
  funext g
  have h1 : Formalism.QuantumDeterminants.hpart1 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart1 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart1 Formalism.REAL.cpart1
    rw [jm_inv]
  have h2 : Formalism.QuantumDeterminants.hpart2 (Formalism.REAL.Jm ε) (Matrix.single a b 1) = Formalism.REAL.cpart2 ε (Matrix.single a b 1) := by
    unfold Formalism.QuantumDeterminants.hpart2 Formalism.REAL.cpart2
    rw [jm_inv]
  unfold Formalism.QuantumDeterminants.EabH
  rw [h1, h2]
  rfl

/- English proof (translation)
Establish `hm : k * k⁻¹ = 1` using `AAInvW.ana_mul_inv (hinvol ε) hk`. Establish `h0 : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε` using `hk`. Use `show (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = Formalism.REAL.Jm ε`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[Matrix.conjTranspose_mul]`.

Simplify using `only [Matrix.mul_assoc]`. Use `_ = Formalism.REAL.Jm ε := by rw [hm]; simp`.
-/
lemma inUJ_inv {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) : Formalism.REAL.inUJ ε k⁻¹ := by
  have hm : k * k⁻¹ = 1 := AAInvW.ana_mul_inv (hinvol ε) hk
  have h0 : kᴴ * Formalism.REAL.Jm ε * k = Formalism.REAL.Jm ε := hk
  show (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = Formalism.REAL.Jm ε
  calc (k⁻¹)ᴴ * Formalism.REAL.Jm ε * k⁻¹ = (k⁻¹)ᴴ * (kᴴ * Formalism.REAL.Jm ε * k) * k⁻¹ := by rw [h0]
    _ = (k * k⁻¹)ᴴ * Formalism.REAL.Jm ε * (k * k⁻¹) := by
        rw [Matrix.conjTranspose_mul]; simp only [Matrix.mul_assoc]
    _ = Formalism.REAL.Jm ε := by rw [hm]; simp

/- English proof (translation)
The claim follows from `AAInvW.smooth_right' n (Formalism.REAL.Jm ε) ℂ f k (hinvol ε) hk hf`.
-/
lemma smooth_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    Formalism.REAL.SmoothOnG ε (fun x => f (x * k)) :=
  AAInvW.smooth_right' n (Formalism.REAL.Jm ε) ℂ f k (hinvol ε) hk hf

/- English proof (translation)
Rewrite using `[← eabH_eq, ← eabH_eq]`. Conclude with `AAInvW.eab_h_local n (Formalism.REAL.Jm ε) ℂ f f' a b g (hinvol ε) h hg`.
-/
lemma eab_local {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (a b : Fin n)
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eab ε a b f g = Formalism.REAL.Eab ε a b f' g := by
  rw [← eabH_eq, ← eabH_eq]
  exact AAInvW.eab_h_local n (Formalism.REAL.Jm ε) ℂ f f' a b g (hinvol ε) h hg

/- English proof (translation)
Simplify using `[Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]`.
-/
lemma eab_zero (a b : Fin n) (g : Matrix (Fin n) (Fin n) ℂ) :
    Formalism.REAL.Eab ε a b (fun _ => (0 : ℂ)) g = 0 := by
  simp [Formalism.REAL.Eab, Formalism.REAL.Ec, Formalism.REAL.Rd]

/- English proof (translation)
Use `AAInvW.eab_h_linear n (Formalism.REAL.Jm ε) ℂ f f' c a b g (hinvol ε) hf hf' hg` as an intermediate fact. Simplify `this` using `only [eabH_eq, smul_eq_mul]`.
-/
lemma eab_lin {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ} (c : ℂ) (a b : Fin n)
    (hf : Formalism.REAL.SmoothOnG ε f) (hf' : Formalism.REAL.SmoothOnG ε f')
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => f x + c * f' x) g =
      Formalism.REAL.Eab ε a b f g + c * Formalism.REAL.Eab ε a b f' g := by
  have := AAInvW.eab_h_linear n (Formalism.REAL.Jm ε) ℂ f f' c a b g (hinvol ε) hf hf' hg
  simpa only [eabH_eq, smul_eq_mul] using this

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using Formalism.REAL.smooth_on_group_const_fun (ε := ε) 0`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Conclude with `Formalism.REAL.smooth_on_group_add (Formalism.REAL.smooth_on_group_const_mul (c i) (hF i)) ih`.
-/
lemma smooth_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) :
    Formalism.REAL.SmoothOnG ε (fun x => ∑ i ∈ s, c i * F i x) := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using Formalism.REAL.smooth_on_group_const_fun (ε := ε) 0
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    exact Formalism.REAL.smooth_on_group_add (Formalism.REAL.smooth_on_group_const_mul (c i) (hF i)) ih

/- English proof (translation)
Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using eab_zero (ε := ε) a b g`. Consider the case `insert i s hi ih`. Simplify using `only [Finset.sum_insert hi]`. Establish `e : (fun x => c i * F i x + ∑ j ∈ s, c j * F j x) = fun x => (∑ j ∈ s, c j * F j x) + c i * F i x` using `funext fun x => add_comm _ _`.

Rewrite using `[e, eab_lin (c i) a b (smooth_sum s c F hF) (hF i) hg, ih, add_comm]`.
-/
lemma eab_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (a b : Fin n) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε a b (F i) g := by
  classical
  induction s using Finset.induction_on with
  | empty => simpa using eab_zero (ε := ε) a b g
  | insert i s hi ih =>
    simp only [Finset.sum_insert hi]
    have e : (fun x => c i * F i x + ∑ j ∈ s, c j * F j x) =
        fun x => (∑ j ∈ s, c j * F j x) + c i * F i x := funext fun x => add_comm _ _
    rw [e, eab_lin (c i) a b (smooth_sum s c F hF) (hF i) hg, ih, add_comm]

/- English proof (translation)
Establish `hJ` using `hinvol ε`. Establish `hmi : k * k⁻¹ = 1` using `AAInvW.ana_mul_inv hJ hk`. Establish `him : k⁻¹ * k = 1` using `AAInvW.ana_inv_mul hJ hk`. Establish `hgk : Formalism.REAL.inUJ ε (g * k)` using `AAInvW.ana_mul hg hk`. Establish `h` using `AAInvW.eab_h_right n (Formalism.REAL.Jm ε) ℂ (fun x => f (x * k)) a b k⁻¹ (g * k) hJ (smooth_right hf hk) (inUJ_inv hk) hgk`.

Establish `e1 : (fun x => (fun y => f (y * k)) (x * k⁻¹)) = f`. Use function extensionality and compare the values at `x`. Use `show f (x * k⁻¹ * k) = f x`. Rewrite using `[Matrix.mul_assoc, him, Matrix.mul_one]`. Establish `e2 : g * k * k⁻¹ = g` using `by rw [Matrix.mul_assoc, hmi, Matrix.mul_one]`.

Establish `e3 : (k⁻¹)⁻¹ = k` using `Matrix.inv_eq_left_inv hmi`. Rewrite `h` using `[e1, e2, e3, eabH_eq]`. Rewrite using `[h, Fintype.sum_prod_type]`. Simplify using `only [eabH_eq, smul_eq_mul]`. Both sides reduce to the same expression.
-/
lemma eab_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f) (a b : Fin n)
    {k g : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eab ε a b f (g * k) =
      ∑ q : Fin n × Fin n, adC k (a, b) q * Formalism.REAL.Eab ε q.1 q.2 (fun x => f (x * k)) g := by
  have hJ := hinvol ε
  have hmi : k * k⁻¹ = 1 := AAInvW.ana_mul_inv hJ hk
  have him : k⁻¹ * k = 1 := AAInvW.ana_inv_mul hJ hk
  have hgk : Formalism.REAL.inUJ ε (g * k) := AAInvW.ana_mul hg hk
  have h := AAInvW.eab_h_right n (Formalism.REAL.Jm ε) ℂ (fun x => f (x * k)) a b k⁻¹ (g * k) hJ
    (smooth_right hf hk) (inUJ_inv hk) hgk
  have e1 : (fun x => (fun y => f (y * k)) (x * k⁻¹)) = f := by
    funext x
    show f (x * k⁻¹ * k) = f x
    rw [Matrix.mul_assoc, him, Matrix.mul_one]
  have e2 : g * k * k⁻¹ = g := by rw [Matrix.mul_assoc, hmi, Matrix.mul_one]
  have e3 : (k⁻¹)⁻¹ = k := Matrix.inv_eq_left_inv hmi
  rw [e1, e2, e3, eabH_eq] at h
  rw [h, Fintype.sum_prod_type]
  simp only [eabH_eq, smul_eq_mul]
  rfl

/- English proof (translation)
Proceed by induction on `w generalizing g with`. Consider the case `nil => exact h g hg`. Consider the case `cons p w ih => exact eab_local p.1 p.2 (fun x hx => ih hx) hg`.
-/
lemma eword_local (w : List (Fin n × Fin n)) {f f' : Matrix (Fin n) (Fin n) ℂ → ℂ}
    (h : ∀ x, Formalism.REAL.inUJ ε x → f x = f' x) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : Formalism.REAL.inUJ ε g) : Formalism.REAL.Eword ε w f g = Formalism.REAL.Eword ε w f' g := by
  induction w generalizing g with
  | nil => exact h g hg
  | cons p w ih => exact eab_local p.1 p.2 (fun x hx => ih hx) hg

/- English proof (translation)
Proceed by induction on `w generalizing g with`. Consider the case `nil => rfl`. Consider the case `cons p w ih => show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w _) g = ∑ i ∈ s, c i * Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (F i)) g`. Rewrite using `[eab_local p.1 p.2 (f' := fun x => ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) x) (fun x hx => ih hx) hg]`. Conclude with `eab_sum s c _ (fun i => Formalism.REAL.smooth_iterated_lie_derivative (hF i) w) p.1 p.2 hg`.
-/
lemma eword_sum {ι : Type*} (s : Finset ι) (c : ι → ℂ) (F : ι → Matrix (Fin n) (Fin n) ℂ → ℂ)
    (hF : ∀ i, Formalism.REAL.SmoothOnG ε (F i)) (w : List (Fin n × Fin n))
    {g : Matrix (Fin n) (Fin n) ℂ} (hg : Formalism.REAL.inUJ ε g) :
    Formalism.REAL.Eword ε w (fun x => ∑ i ∈ s, c i * F i x) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) g := by
  induction w generalizing g with
  | nil => rfl
  | cons p w ih =>
    show Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w _) g =
      ∑ i ∈ s, c i * Formalism.REAL.Eab ε p.1 p.2 (Formalism.REAL.Eword ε w (F i)) g
    rw [eab_local p.1 p.2 (f' := fun x => ∑ i ∈ s, c i * Formalism.REAL.Eword ε w (F i) x)
      (fun x hx => ih hx) hg]
    exact eab_sum s c _ (fun i => Formalism.REAL.smooth_iterated_lie_derivative (hF i) w) p.1 p.2 hg

/- English proof (translation)
Rewrite using `[← Fintype.sum_prod_type']`. Conclude with `(Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm`.
-/
lemma sum_cons {α : Type*} [Fintype α] [DecidableEq α] {l : ℕ} (Φ : (Fin (l + 1) → α) → ℂ) :
    ∑ W, Φ W = ∑ q : α, ∑ w : Fin l → α, Φ (Fin.cons q w) := by
  rw [← Fintype.sum_prod_type']
  exact (Fintype.sum_equiv (Fin.consEquiv (fun _ => α)) _ _ (fun _ => rfl)).symm

/- English proof (translation)
Introduce `l`. Proceed by induction on `l with`. Consider the case `zero`. Introduce `x g hg`. Simplify using `[Formalism.REAL.Eword]`.

Consider the case `succ l ih`. Introduce `x g hg`. Establish `hfk` using `smooth_right hf hk`. Rewrite using `[sum_cons, List.ofFn_succ]`. Use `show Formalism.REAL.Eab ε (x 0).1 (x 0).2 (Formalism.REAL.Eword ε (List.ofFn fun i => x i.succ) f) (g * k) = _`.

Rewrite using `[eab_mul_right (Formalism.REAL.smooth_iterated_lie_derivative hf _) _ _ hk hg]`. Use `Finset.sum_congr rfl fun q _ => ?_` and prove the remaining obligations. Rewrite using `[eab_local q.1 q.2 (f' := fun y => ∑ w : Fin l → Fin n × Fin n, (∏ i, adC k (x i.succ) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) y) (fun y hy => ih _ y hy) hg, eab_sum _ _ _ (fun w => Formalism.REAL.smooth_iterated_lie_derivative hfk _) q.1 q.2 hg, Finset …`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[Fin.prod_univ_succ, List.ofFn_succ]`.

Simplify using `only [Fin.cons_zero, Fin.cons_succ]`. Use `show _ = _ * Formalism.REAL.Eab ε q.1 q.2 (Formalism.REAL.Eword ε (List.ofFn w) _) g`. Expand and normalize the polynomial expressions, which then agree.
-/
lemma eword_mul_right {f : Matrix (Fin n) (Fin n) ℂ → ℂ} (hf : Formalism.REAL.SmoothOnG ε f)
    {k : Matrix (Fin n) (Fin n) ℂ} (hk : Formalism.REAL.inUJ ε k) :
    ∀ (l : ℕ) (x : Fin l → Fin n × Fin n) (g : Matrix (Fin n) (Fin n) ℂ), Formalism.REAL.inUJ ε g →
      Formalism.REAL.Eword ε (List.ofFn x) f (g * k) =
        ∑ w : Fin l → Fin n × Fin n, (∏ i, adC k (x i) (w i)) *
          Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) g := by
  intro l
  induction l with
  | zero =>
    intro x g hg
    simp [Formalism.REAL.Eword]
  | succ l ih =>
    intro x g hg
    have hfk := smooth_right hf hk
    rw [sum_cons, List.ofFn_succ]
    show Formalism.REAL.Eab ε (x 0).1 (x 0).2 (Formalism.REAL.Eword ε (List.ofFn fun i => x i.succ) f) (g * k) = _
    rw [eab_mul_right (Formalism.REAL.smooth_iterated_lie_derivative hf _) _ _ hk hg]
    refine Finset.sum_congr rfl fun q _ => ?_
    rw [eab_local q.1 q.2 (f' := fun y => ∑ w : Fin l → Fin n × Fin n,
        (∏ i, adC k (x i.succ) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (fun y => f (y * k)) y)
      (fun y hy => ih _ y hy) hg,
      eab_sum _ _ _ (fun w => Formalism.REAL.smooth_iterated_lie_derivative hfk _) q.1 q.2 hg, Finset.mul_sum]
    refine Finset.sum_congr rfl fun w _ => ?_
    rw [Fin.prod_univ_succ, List.ofFn_succ]
    simp only [Fin.cons_zero, Fin.cons_succ]
    show _ = _ * Formalism.REAL.Eab ε q.1 q.2 (Formalism.REAL.Eword ε (List.ofFn w) _) g
    ring

/- English proof (translation)
Introduce `n ε lam T Ψ m hP k a`. Establish `hk : Formalism.REAL.inUJ ε (toMK k)` using `(mir_inUJ_iff ε _).2 k.1.2`. Establish `hJ : ∀ v, Formalism.REAL.SmoothOnG ε (jfun Ψ T.w v)` using `fun v => pdA_smooth_clm (pdA_coef T.w v) (f := Ψ) hP.2.2.1`. Establish `hJk : ∀ v y, Formalism.REAL.inUJ ε y → jfun Ψ T.w v (y * toMK k) = jfun Ψ T.w (T.op k v) y`. Introduce `v y hy`.

Use `show inner ℂ T.w (Ψ (y * toMK k) v) = inner ℂ T.w (Ψ y (T.op k v))`. Establish `h1` using `hP.1 1 k y ((mir_inUJ_iff ε _).1 hy)`. Rewrite `h1` using `[pdA_toMK_one, Matrix.one_mul, pdA_op_one, one_mul]`. Rewrite using `[h1]`. Both sides reduce to the same expression.

Unfold `actL`. Rewrite using `[rightRegular_toL2 ε _ (show toMK k ∈ UJset ε from k.1.2)]`. Use `toL2_congr_of_forall_inUJ_eq fun g hg' => ?_` and prove the remaining obligations. Establish `hg : Formalism.REAL.inUJ ε g` using `(mir_inUJ_iff ε _).2 hg'`. Establish `hL : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (a x))) (g * toMK k) = ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (x.2 i) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a x))) g`.

Introduce `x`. Use `(eword_mul_right (hJ (a x)) hk x.1 x.2 g hg).trans (Finset.sum_congr rfl fun w _ => ?_)` and prove the remaining obligations. Rewrite using `[eword_local (List.ofFn w) (f' := jfun Ψ T.w (T.op k (a x))) (fun y hy => hJk _ y hy) hg]`. Establish `hR : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) g = ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x.2 i)) * Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (T.op k (a ⟨x.1, w⟩))) g`. Introduce `x`.

Establish `e : (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) = fun y => ∑ w ∈ (Finset.univ : Finset (Fin x.1 → Fin n × Fin n)), (∏ i, adC (toMK k) (w i) (x.2 i)) * jfun Ψ T.w (T.op k (a ⟨x.1, w⟩)) y`. Use function extensionality and compare the values at `y`. Simplify using `only [rhoA, map_sum, map_smul, inner_sum, inner_smul_right, jfun]`. Rewrite using `[e]`. Conclude with `eword_sum _ _ _ (fun w => hJ _) _ hg`.

Use `show actF T Ψ a (g * toMK k) = actF T Ψ (rhoA T m k a) g`. Unfold `actF`. Rewrite using `[Finset.sum_apply, Finset.sum_apply]`. Simplify using `only [hL, hR]`. Rewrite using `[Fintype.sum_sigma, Fintype.sum_sigma]`.

Use `Finset.sum_congr rfl fun l _ => ?_` and prove the remaining obligations. Conclude with `Finset.sum_comm (s := (Finset.univ : Finset (Fin (l : ℕ) → Fin n × Fin n))) (t := Finset.univ) (f := fun y w => (∏ i, adC (toMK k) (y i) (w i)) * Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a ⟨l, y⟩))) g)`.
-/
theorem actEquiv : ActEquiv := by
  intro n ε lam T Ψ m hP k a
  have hk : Formalism.REAL.inUJ ε (toMK k) := (mir_inUJ_iff ε _).2 k.1.2
  have hJ : ∀ v, Formalism.REAL.SmoothOnG ε (jfun Ψ T.w v) := fun v =>
    pdA_smooth_clm (pdA_coef T.w v) (f := Ψ) hP.2.2.1
  have hJk : ∀ v y, Formalism.REAL.inUJ ε y →
      jfun Ψ T.w v (y * toMK k) = jfun Ψ T.w (T.op k v) y := by
    intro v y hy
    show inner ℂ T.w (Ψ (y * toMK k) v) = inner ℂ T.w (Ψ y (T.op k v))
    have h1 := hP.1 1 k y ((mir_inUJ_iff ε _).1 hy)
    rw [pdA_toMK_one, Matrix.one_mul, pdA_op_one, one_mul] at h1
    rw [h1]
    rfl
  unfold actL
  rw [rightRegular_toL2 ε _ (show toMK k ∈ UJset ε from k.1.2)]
  refine toL2_congr_of_forall_inUJ_eq fun g hg' => ?_
  have hg : Formalism.REAL.inUJ ε g := (mir_inUJ_iff ε _).2 hg'
  have hL : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x) (fun y => inner ℂ T.w (Ψ y (a x))) (g * toMK k) =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (x.2 i) (w i)) *
        Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a x))) g := by
    intro x
    refine (eword_mul_right (hJ (a x)) hk x.1 x.2 g hg).trans (Finset.sum_congr rfl fun w _ => ?_)
    rw [eword_local (List.ofFn w) (f' := jfun Ψ T.w (T.op k (a x))) (fun y hy => hJk _ y hy) hg]
  have hR : ∀ x : Wd n m, Formalism.REAL.Eword ε (ofW x)
        (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) g =
      ∑ w : Fin x.1 → Fin n × Fin n, (∏ i, adC (toMK k) (w i) (x.2 i)) *
        Formalism.REAL.Eword ε (ofW x) (jfun Ψ T.w (T.op k (a ⟨x.1, w⟩))) g := by
    intro x
    have e : (fun y => inner ℂ T.w (Ψ y (rhoA T m k a x))) = fun y =>
        ∑ w ∈ (Finset.univ : Finset (Fin x.1 → Fin n × Fin n)), (∏ i, adC (toMK k) (w i) (x.2 i)) *
          jfun Ψ T.w (T.op k (a ⟨x.1, w⟩)) y := by
      funext y
      simp only [rhoA, map_sum, map_smul, inner_sum, inner_smul_right, jfun]
    rw [e]
    exact eword_sum _ _ _ (fun w => hJ _) _ hg
  show actF T Ψ a (g * toMK k) = actF T Ψ (rhoA T m k a) g
  unfold actF
  rw [Finset.sum_apply, Finset.sum_apply]
  simp only [hL, hR]
  rw [Fintype.sum_sigma, Fintype.sum_sigma]
  refine Finset.sum_congr rfl fun l _ => ?_
  exact Finset.sum_comm (s := (Finset.univ : Finset (Fin (l : ℕ) → Fin n × Fin n))) (t := Finset.univ)
    (f := fun y w => (∏ i, adC (toMK k) (y i) (w i)) *
      Formalism.REAL.Eword ε (List.ofFn w) (jfun Ψ T.w (T.op k (a ⟨l, y⟩))) g)

end GlobalTheory.CompanionTheory.ActEquivK
