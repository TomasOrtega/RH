import Mathlib

open MvPolynomial TensorProduct

noncomputable section

namespace GlobalTheory.InducedPBW

section General

variable {R : Type*} [CommRing R] {ι : Type*} {V : Type*} [AddCommGroup V] [Module R V]

def zv (α : ι →₀ ℕ) : V →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  TensorProduct.mk R (MvPolynomial ι R) V (monomial α 1)

def mulX (i : ι) : Module.End R (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.rTensor V (LinearMap.mulLeft R (X i))

/- English proof (translation)
Simplify using `[mulX, zv, X, monomial_mul]`.
-/
lemma mulX_zv (i : ι) (α : ι →₀ ℕ) (v : V) :
    mulX i (zv (R := R) α v) = zv (Finsupp.single i 1 + α) v := by
  simp [mulX, zv, X, monomial_mul]

def degLt (R : Type*) [CommRing R] (ι : Type*) (V : Type*) [AddCommGroup V] [Module R V] (n : ℕ) :
    Submodule R (MvPolynomial ι R ⊗[R] V) :=
  Submodule.span R {m | ∃ (α : ι →₀ ℕ) (v : V), α.degree < n ∧ m = zv α v}

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨α, v, h, rfl⟩`.
-/
lemma zv_mem {n : ℕ} {α : ι →₀ ℕ} (h : α.degree < n) (v : V) : zv α v ∈ degLt R ι V n :=
  Submodule.subset_span ⟨α, v, h, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.span_mono fun _ ⟨α, v, h1, h2⟩ => ⟨α, v, h1.trans_le h, h2⟩`.
-/
lemma degLt_mono {n m : ℕ} (h : n ≤ m) : degLt R ι V n ≤ degLt R ι V m :=
  Submodule.span_mono fun _ ⟨α, v, h1, h2⟩ => ⟨α, v, h1.trans_le h, h2⟩

/- English proof (translation)
Establish `: degLt R ι V n ≤ N.comap f` using `Submodule.span_le.mpr (by`. Introduce and unpack `_ ⟨α, v, h1, rfl⟩`. Conclude with `h α v h1)`. Conclude with `fun m hm => this hm`.
-/
lemma map_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W) (N : Submodule R W)
    (h : ∀ α v, α.degree < n → f (zv α v) ∈ N) : ∀ m ∈ degLt R ι V n, f m ∈ N := by
  have : degLt R ι V n ≤ N.comap f := Submodule.span_le.mpr (by
    rintro _ ⟨α, v, h1, rfl⟩
    exact h α v h1)
  exact fun m hm => this hm

/- English proof (translation)
Introduce `m hm`. Use `map_degLt (f - f') ⊥ (fun α v hα => by simp [h α v hα]) m hm` as an intermediate fact. Simplify `this` using `[sub_eq_zero]`.
-/
lemma eq_on_degLt {W : Type*} [AddCommGroup W] [Module R W] {n : ℕ}
    (f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W)
    (h : ∀ α v, α.degree < n → f (zv α v) = f' (zv α v)) : ∀ m ∈ degLt R ι V n, f m = f' m := by
  intro m hm
  have := map_degLt (f - f') ⊥ (fun α v hα => by simp [h α v hα]) m hm
  simpa [sub_eq_zero] using this

/- English proof (translation)
Apply `TensorProduct.ext` to reduce the goal to its premises. Apply `(basisMonomials ι R).ext` to reduce the goal to its premises. Introduce `α`. Use extensionality with `v`. Simplify `h α v` using `[zv]`.
-/
lemma ext_zv {W : Type*} [AddCommGroup W] [Module R W]
    {f f' : (MvPolynomial ι R ⊗[R] V) →ₗ[R] W}
    (h : ∀ α v, f (zv α v) = f' (zv α v)) : f = f' := by
  apply TensorProduct.ext
  apply (basisMonomials ι R).ext
  intro α
  ext v
  simpa [zv] using h α v

/- English proof (translation)
Simplify using `[add_comm]`.
-/
lemma degree_single_add (i : ι) (α : ι →₀ ℕ) :
    (Finsupp.single i 1 + α).degree = α.degree + 1 := by
  simp [add_comm]

/- English proof (translation)
The claim follows from `map_degLt _ _ fun α v h => by rw [mulX_zv] exact zv_mem (by rw [degree_single_add]; omega) v`.
-/
lemma mulX_mem {n : ℕ} (i : ι) : ∀ m ∈ degLt R ι V n, mulX i m ∈ degLt R ι V (n + 1) :=
  map_degLt _ _ fun α v h => by
    rw [mulX_zv]
    exact zv_mem (by rw [degree_single_add]; omega) v

variable {g : Type*} [LieRing g] [LieAlgebra R g]

/- English proof (translation)
Use `⟨{ toFun := fun x => TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x) map_add' := ?_, map_smul' := ?_ }, ?_⟩` and prove the remaining obligations. Use `all_goals`. Establish `key : ∀ (x : g) α v, TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x) (zv α v) = D α x v`. Introduce `x α v`. Use `(basisMonomials ι R).constr_basis R (fun α => D α x) α` as an intermediate fact.

Simplify using `only [coe_basisMonomials] at this`. Simplify using `[zv, this]`. Introduce `x y`. Conclude with `ext_zv fun α v => by rw [LinearMap.add_apply, key, key, key]; simp`. Introduce `r x`.

Conclude with `ext_zv fun α v => by rw [LinearMap.smul_apply, key, key]; simp`. Conclude with `key`.
-/
lemma exists_extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V), ∀ x α v, δ x (zv α v) = D α x v := by
  refine ⟨{ toFun := fun x => TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
            map_add' := ?_, map_smul' := ?_ }, ?_⟩
  all_goals
    have key : ∀ (x : g) α v, TensorProduct.lift ((basisMonomials ι R).constr R fun α => D α x)
        (zv α v) = D α x v := by
      intro x α v
      have := (basisMonomials ι R).constr_basis R (fun α => D α x) α
      simp only [coe_basisMonomials] at this
      simp [zv, this]
  · intro x y
    exact ext_zv fun α v => by rw [LinearMap.add_apply, key, key, key]; simp
  · intro r x
    exact ext_zv fun α v => by rw [LinearMap.smul_apply, key, key]; simp
  · exact key

def extend (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := (exists_extend D).choose

/- English proof (translation)
The claim follows from `(exists_extend D).choose_spec x α v`.
-/
lemma extend_zv (D : (ι →₀ ℕ) → g →ₗ[R] V →ₗ[R] (MvPolynomial ι R ⊗[R] V)) (x α v) :
    extend D x (zv α v) = D α x v := (exists_extend D).choose_spec x α v

variable [Fintype ι] [LinearOrder ι] (e : ι → g) (c : ι → g →ₗ[R] R) (act : g →ₗ[R] Module.End R V)

def mulLin : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := ∑ i, (c i).smulRight (mulX i)

omit [LinearOrder ι] in
/- English proof (translation)
Simplify using `[mulLin, LinearMap.sum_apply]`.
-/
lemma mulLin_apply (x : g) (m : MvPolynomial ι R ⊗[R] V) :
    mulLin c x m = ∑ i, c i x • mulX i m := by
  simp [mulLin, LinearMap.sum_apply]

omit [LinearOrder ι] in
/- English proof (translation)
Introduce `m hm`. Rewrite using `[mulLin_apply]`. Conclude with `Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mulX_mem i m hm)`.
-/
lemma mulLin_mem {n : ℕ} (x : g) : ∀ m ∈ degLt R ι V n, mulLin c x m ∈ degLt R ι V (n + 1) := by
  intro m hm
  rw [mulLin_apply]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (mulX_mem i m hm)

def rho (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := mulLin c + δ

omit [LinearOrder ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma rho_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x m) :
    rho c δ x m = mulLin c x m + δ x m := rfl

def strip (s : Finset ι) : g →ₗ[R] g := LinearMap.id - ∑ j ∈ s, (c j).smulRight (e j)

omit [Fintype ι] [LinearOrder ι] in
/- English proof (translation)
Simplify using `[strip, LinearMap.sum_apply]`.
-/
lemma strip_apply (s : Finset ι) (x : g) : strip e c s x = x - ∑ j ∈ s, c j x • e j := by
  simp [strip, LinearMap.sum_apply]

def straighten (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  (LinearMap.mulLeft R (rho c δ (e i)) ∘ₗ δ -
    rho c δ ∘ₗ (LieAlgebra.ad R g (e i))) ∘ₗ strip e c (Finset.univ.filter (· ≤ i))

/- English proof (translation)
Rewrite using `[← lie_skew (strip e c (Finset.univ.filter (· ≤ i)) x), map_neg]`. Simplify using `[straighten, sub_eq_add_neg]`.
-/
lemma straighten_apply (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (x m) :
    straighten e c δ i x m =
      rho c δ (e i) (δ (strip e c (Finset.univ.filter (· ≤ i)) x) m) +
      rho c δ ⁅strip e c (Finset.univ.filter (· ≤ i)) x, e i⁆ m := by
  rw [← lie_skew (strip e c (Finset.univ.filter (· ≤ i)) x), map_neg]
  simp [straighten, sub_eq_add_neg]

def step (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) :
    g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
  extend fun α => if h : α.support.Nonempty then
    (straighten e c δ (α.support.min' h)).compl₂ (zv (α - Finsupp.single (α.support.min' h) 1))
  else (act ∘ₗ strip e c Finset.univ).compr₂ (zv 0)

/- English proof (translation)
Simplify using `[step, extend_zv]`.
-/
lemma step_zero (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (x v) :
    step e c act δ x (zv 0 v) = zv 0 (act (strip e c Finset.univ x) v) := by
  simp [step, extend_zv]

/- English proof (translation)
Establish `hi : i ∈ (Finsupp.single i 1 + J).support` using `by simp`. Establish `hmin : (Finsupp.single i 1 + J).support.min' ⟨i, hi⟩ = i`. Apply `le_antisymm (Finset.min'_le _ _ hi)` to reduce the goal to its premises. Apply `Finset.le_min'` to reduce the goal to its premises. Introduce `j hj`.

Break down `Finset.mem_union.mp (Finsupp.support_add hj) with h1 | h1` into its components or cases. Conclude with `(Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge`. Conclude with `hJ j h1`. Simplify using `[step, extend_zv, hmin]`.
-/
lemma step_succ (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) (i : ι) (J : ι →₀ ℕ)
    (hJ : ∀ j ∈ J.support, i ≤ j) (x v) :
    step e c act δ x (zv (Finsupp.single i 1 + J) v) = straighten e c δ i x (zv J v) := by
  have hi : i ∈ (Finsupp.single i 1 + J).support := by simp
  have hmin : (Finsupp.single i 1 + J).support.min' ⟨i, hi⟩ = i := by
    apply le_antisymm (Finset.min'_le _ _ hi)
    apply Finset.le_min'
    intro j hj
    rcases Finset.mem_union.mp (Finsupp.support_add hj) with h1 | h1
    · exact (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
    · exact hJ j h1
  simp [step, extend_zv, hmin]

omit [Fintype ι] in
/- English proof (translation)
Distinguish the cases in `h : α.support.Nonempty`. Use `right`. Use `⟨α.support.min' h, α - Finsupp.single (α.support.min' h) 1, fun j hj => ?_, ?_⟩` and prove the remaining obligations. Conclude with `Finset.min'_le _ _ (Finsupp.support_tsub hj)`. Rewrite using `[add_comm, tsub_add_cancel_of_le]`.

Rewrite using `[Finsupp.single_le_iff]`. Conclude with `Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (Finset.min'_mem _ h))`. Use `left`. Simplify using `using h`.
-/
lemma exponent_cases (α : ι →₀ ℕ) :
    α = 0 ∨ ∃ (i : ι) (J : ι →₀ ℕ), (∀ j ∈ J.support, i ≤ j) ∧ α = Finsupp.single i 1 + J := by
  by_cases h : α.support.Nonempty
  · right
    refine ⟨α.support.min' h, α - Finsupp.single (α.support.min' h) 1, fun j hj => ?_, ?_⟩
    · exact Finset.min'_le _ _ (Finsupp.support_tsub hj)
    · rw [add_comm, tsub_add_cancel_of_le]
      rw [Finsupp.single_le_iff]
      exact Nat.one_le_iff_ne_zero.mpr (Finsupp.mem_support_iff.mp (Finset.min'_mem _ h))
  · left
    simpa using h

def Pres (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)) : Prop :=
  ∀ n x, ∀ m ∈ degLt R ι V n, δ x m ∈ degLt R ι V n

omit [LinearOrder ι] in
/- English proof (translation)
Introduce `m hm` and use `Submodule.add_mem _ (mulLin_mem c x m hm) (degLt_mono (Nat.le_succ n) (h n x m hm))`.
-/
lemma Pres.rho_mem {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) (n x) :
    ∀ m ∈ degLt R ι V n, rho c δ x m ∈ degLt R ι V (n + 1) := fun m hm =>
  Submodule.add_mem _ (mulLin_mem c x m hm) (degLt_mono (Nat.le_succ n) (h n x m hm))

/- English proof (translation)
Introduce `n x`. Use `map_degLt _ _ fun α v hα => ?_` and prove the remaining obligations. Break down `exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩` into its components or cases. Rewrite using `[step_zero]`. Conclude with `zv_mem hα _`.

Rewrite using `[step_succ e c act δ i J hJ, straighten_apply]`. Rewrite `hα` using `[degree_single_add]`. Establish `hz : zv J v ∈ degLt R ι V (J.degree + 1)` using `zv_mem (by omega) v`. Use `degLt_mono (show J.degree + 1 + 1 ≤ n by omega) (Submodule.add_mem _ ?_ ?_)` and prove the remaining obligations. Conclude with `h.rho_mem c _ _ _ (h _ _ _ hz)`.

Conclude with `h.rho_mem c _ _ _ hz`.
-/
lemma Pres.step {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) :
    Pres (step e c act δ) := by
  intro n x
  refine map_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero]; exact zv_mem hα _
  · rw [step_succ e c act δ i J hJ, straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V (J.degree + 1) := zv_mem (by omega) v
    refine degLt_mono (show J.degree + 1 + 1 ≤ n by omega) (Submodule.add_mem _ ?_ ?_)
    · exact h.rho_mem c _ _ _ (h _ _ _ hz)
    · exact h.rho_mem c _ _ _ hz

/- English proof (translation)
Introduce `x`. Use `eq_on_degLt _ _ fun α v hα => ?_` and prove the remaining obligations. Break down `exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩` into its components or cases. Rewrite using `[step_zero, step_zero]`. Rewrite using `[step_succ e c act δ i J hJ, step_succ e c act δ' i J hJ, straighten_apply, straighten_apply]`.

Rewrite `hα` using `[degree_single_add]`. Establish `hz : zv J v ∈ degLt R ι V n` using `zv_mem (by omega) v`. Simplify using `only [rho_apply]`. Rewrite using `[ha _ _ (h _ _ _ hz), ha _ _ hz, ha _ _ hz]`.
-/
lemma step_agree {δ δ' : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)} (h : Pres δ) {n : ℕ}
    (ha : ∀ x, ∀ m ∈ degLt R ι V n, δ x m = δ' x m) :
    ∀ x, ∀ m ∈ degLt R ι V (n + 1), step e c act δ x m = step e c act δ' x m := by
  intro x
  refine eq_on_degLt _ _ fun α v hα => ?_
  rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
  · rw [step_zero, step_zero]
  · rw [step_succ e c act δ i J hJ, step_succ e c act δ' i J hJ, straighten_apply,
      straighten_apply]
    rw [degree_single_add] at hα
    have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
    simp only [rho_apply]
    rw [ha _ _ (h _ _ _ hz), ha _ _ hz, ha _ _ hz]

/- English proof (translation)
Set `d : ℕ → g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)` to `fun n => (step e c act)^[n] 0`. Establish `hd : ∀ n, d (n + 1) = step e c act (d n)` using `fun n => Function.iterate_succ_apply' _ _ _`. Establish `hp : ∀ n, Pres (d n)`. Introduce `n`. Proceed by induction on `n with`.

Consider the case `zero => intro n x m _`. Simplify using `[d]`. Consider the case `succ n ih => rw [hd]`. Conclude with `ih.step e c act`. Establish `hag : ∀ n k, ∀ x, ∀ m ∈ degLt R ι V n, d n x m = d (n + k) x m`.

Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `k x`. Conclude with `eq_on_degLt _ _ fun α v h => absurd h (Nat.not_lt_zero _)`.

Consider the case `succ n ih`. Introduce `k`. Rewrite using `[show n + 1 + k = (n + k) + 1 by omega, hd, hd]`. Conclude with `step_agree e c act (hp n) (ih k)`. Set `δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)` to `extend fun α => (d (α.degree + 1)).compl₂ (zv α)`.

Establish `hδ : ∀ x α v, δ x (zv α v) = d (α.degree + 1) x (zv α v)`. Introduce `x α v`. Simplify using `[δ, extend_zv]`. Establish `hδn : ∀ n x, ∀ m ∈ degLt R ι V n, d n x m = δ x m`. Introduce `n x`.

Use `eq_on_degLt _ _ fun α v h => ?_` and prove the remaining obligations. Take `⟨k, rfl⟩ : ∃ k, n = α.degree + 1 + k` from `⟨n - (α.degree + 1), by omega⟩`. Rewrite using `[hδ, ← hag _ k x _ (zv_mem (Nat.lt_succ_self _) v)]`. Use `⟨δ, fun n x m hm => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← hδn n x m hm]`.

Conclude with `hp n n x m hm`. Use `ext1 x`. Use `ext_zv fun α v => ?_` and prove the remaining obligations. Rewrite using `[hδ, hd]`. Conclude with `(step_agree e c act (hp _) (hδn _) x _ (zv_mem (Nat.lt_succ_self _) v)).symm`.
-/
lemma exists_fixed : ∃ δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
    Pres δ ∧ step e c act δ = δ := by
  let d : ℕ → g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) := fun n => (step e c act)^[n] 0
  have hd : ∀ n, d (n + 1) = step e c act (d n) := fun n => Function.iterate_succ_apply' _ _ _
  have hp : ∀ n, Pres (d n) := by
    intro n
    induction n with
    | zero => intro n x m _; simp [d]
    | succ n ih => rw [hd]; exact ih.step e c act
  have hag : ∀ n k, ∀ x, ∀ m ∈ degLt R ι V n, d n x m = d (n + k) x m := by
    intro n
    induction n with
    | zero =>
      intro k x
      exact eq_on_degLt _ _ fun α v h => absurd h (Nat.not_lt_zero _)
    | succ n ih =>
      intro k
      rw [show n + 1 + k = (n + k) + 1 by omega, hd, hd]
      exact step_agree e c act (hp n) (ih k)
  let δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V) :=
    extend fun α => (d (α.degree + 1)).compl₂ (zv α)
  have hδ : ∀ x α v, δ x (zv α v) = d (α.degree + 1) x (zv α v) := by
    intro x α v
    simp [δ, extend_zv]
  have hδn : ∀ n x, ∀ m ∈ degLt R ι V n, d n x m = δ x m := by
    intro n x
    refine eq_on_degLt _ _ fun α v h => ?_
    obtain ⟨k, rfl⟩ : ∃ k, n = α.degree + 1 + k := ⟨n - (α.degree + 1), by omega⟩
    rw [hδ, ← hag _ k x _ (zv_mem (Nat.lt_succ_self _) v)]
  refine ⟨δ, fun n x m hm => ?_, ?_⟩
  · rw [← hδn n x m hm]; exact hp n n x m hm
  · ext1 x
    refine ext_zv fun α v => ?_
    rw [hδ, hd]
    exact (step_agree e c act (hp _) (hδn _) x _ (zv_mem (Nat.lt_succ_self _) v)).symm

section Fixed

variable {e c act} {δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V)}
  (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)

include hce

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[strip_apply, hce, hi]`.
-/
lemma strip_e_mem {s : Finset ι} {i : ι} (hi : i ∈ s) : strip e c s (e i) = 0 := by
  simp [strip_apply, hce, hi]

omit [Fintype ι] in
/- English proof (translation)
Simplify using `[strip_apply, hce, hi]`.
-/
lemma c_strip {s : Finset ι} {i : ι} (hi : i ∈ s) (x : g) : c i (strip e c s x) = 0 := by
  simp [strip_apply, hce, hi]

omit hce [Fintype ι] [LinearOrder ι] in
/- English proof (translation)
Rewrite using `[strip_apply, Finset.sum_eq_zero fun j hj => by rw [hx j hj, zero_smul], sub_zero]`.
-/
lemma strip_eq {s : Finset ι} {x : g} (hx : ∀ j ∈ s, c j x = 0) : strip e c s x = x := by
  rw [strip_apply, Finset.sum_eq_zero fun j hj => by rw [hx j hj, zero_smul], sub_zero]

/- English proof (translation)
Simplify using `[mulLin_apply, hce]`.
-/
lemma mulLin_e (i : ι) (m : MvPolynomial ι R ⊗[R] V) : mulLin c (e i) m = mulX i m := by
  simp [mulLin_apply, hce]

variable (hf : step e c act δ = δ)
include hf

/- English proof (translation)
Rewrite using `[rho_apply, mulLin_e hce, mulX_zv, ← hf]`. Break down `exponent_cases α with rfl | ⟨j, J, hJ, rfl⟩` into its components or cases. Rewrite using `[step_zero, strip_e_mem hce (Finset.mem_univ _)]`. Simplify using the standard rewrite rules. Establish `hij : i ≤ j` using `h j (by simp)`.

Rewrite using `[step_succ e c act δ j J hJ, straighten_apply, strip_e_mem hce (by simpa using hij)]`. Simplify using the standard rewrite rules.
-/
lemma rho_e_le (i : ι) (α : ι →₀ ℕ) (h : ∀ j ∈ α.support, i ≤ j) (v : V) :
    rho c δ (e i) (zv α v) = zv (Finsupp.single i 1 + α) v := by
  rw [rho_apply, mulLin_e hce, mulX_zv, ← hf]
  rcases exponent_cases α with rfl | ⟨j, J, hJ, rfl⟩
  · rw [step_zero, strip_e_mem hce (Finset.mem_univ _)]
    simp
  · have hij : i ≤ j := h j (by simp)
    rw [step_succ e c act δ j J hJ, straighten_apply, strip_e_mem hce (by simpa using hij)]
    simp

omit hce hf [Fintype ι] in
/- English proof (translation)
Introduce `k hk`. Break down `Finset.mem_union.mp (Finsupp.support_add hk) with h1 | h1` into its components or cases. Conclude with `hij.trans (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge`. Conclude with `hJ k h1`.
-/
lemma le_support_add {i j : ι} {J : ι →₀ ℕ} (hJ : ∀ k ∈ J.support, i ≤ k) (hij : i ≤ j) :
    ∀ k ∈ (Finsupp.single j 1 + J).support, i ≤ k := by
  intro k hk
  rcases Finset.mem_union.mp (Finsupp.support_add hk) with h1 | h1
  · exact hij.trans (Finset.mem_singleton.mp (Finsupp.support_single_subset h1)).ge
  · exact hJ k h1

/- English proof (translation)
Rewrite using `[rho_e_le hce hf i J hJ, rho_apply c δ x, rho_apply c δ x, map_add]`. Use `conv_lhs => rw [← hf]`. Rewrite using `[step_succ e c act δ i J hJ, straighten_apply, strip_eq (fun j hj => hx j (by simpa using hj)), ← add_assoc]`. Use `congr 2`. Rewrite using `[mulLin_apply, mulLin_apply, map_sum]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ≤ i`. Simplify using `[hx j hj]`. Rewrite using `[map_smul, mulX_zv, mulX_zv, rho_e_le hce hf i _ (le_support_add hJ (not_le.mp hj).le), add_left_comm]`.
-/
lemma comm_high (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g)
    (hx : ∀ j, j ≤ i → c j x = 0) (v : V) :
    rho c δ x (rho c δ (e i) (zv J v)) =
      rho c δ (e i) (rho c δ x (zv J v)) + rho c δ ⁅x, e i⁆ (zv J v) := by
  rw [rho_e_le hce hf i J hJ, rho_apply c δ x, rho_apply c δ x, map_add]
  conv_lhs => rw [← hf]
  rw [step_succ e c act δ i J hJ, straighten_apply,
    strip_eq (fun j hj => hx j (by simpa using hj)), ← add_assoc]
  congr 2
  rw [mulLin_apply, mulLin_apply, map_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  by_cases hj : j ≤ i
  · simp [hx j hj]
  · rw [map_smul, mulX_zv, mulX_zv,
      rho_e_le hce hf i _ (le_support_add hJ (not_le.mp hj).le), add_left_comm]

def defect (c : ι → g →ₗ[R] R) (δ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V))
    (m : MvPolynomial ι R ⊗[R] V) : g →ₗ[R] g →ₗ[R] (MvPolynomial ι R ⊗[R] V) :=
  LinearMap.mk₂ R (fun x y => rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m)
    (by intros; simp only [add_lie, map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [smul_lie, map_smul, LinearMap.smul_apply, smul_sub])
    (by intros; simp only [lie_add, map_add, LinearMap.add_apply]; abel)
    (by intros; simp only [lie_smul, map_smul, LinearMap.smul_apply, smul_sub])

omit hce hf [LinearOrder ι] in
/- English proof (translation)
Both sides reduce to the same expression.
-/
lemma defect_apply (m : MvPolynomial ι R ⊗[R] V) (x y : g) : defect c δ m x y =
    rho c δ x (rho c δ y m) - rho c δ y (rho c δ x m) - rho c δ ⁅x, y⁆ m := rfl

omit hce hf [LinearOrder ι] in
/- English proof (translation)
Rewrite using `[defect_apply, defect_apply, ← lie_skew x y, map_neg, LinearMap.neg_apply]`. Normalize the expressions using the abelian group laws.
-/
lemma defect_swap (m : MvPolynomial ι R ⊗[R] V) (x y : g) :
    defect c δ m x y = - defect c δ m y x := by
  rw [defect_apply, defect_apply, ← lie_skew x y, map_neg, LinearMap.neg_apply]
  abel

/- English proof (translation)
Establish `hx : x = strip e c Finset.univ x + ∑ j, c j x • e j` using `by simp [strip_apply]`. Rewrite using `[hx, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, Finset.sum_eq_zero, add_zero]`. Rewrite using `[defect_apply, comm_high hce hf i J hJ _ fun j _ => c_strip hce (Finset.mem_univ _) x]`. Normalize the expressions using the abelian group laws. Introduce `j _`.

Rewrite using `[map_smul, LinearMap.smul_apply]`. It suffices to establish `h : defect c δ (zv J v) (e j) (e i) = 0 by rw [h, smul_zero]`. Break down `lt_trichotomy i j with h | rfl | h` into its components or cases. Rewrite using `[defect_apply, comm_high hce hf i J hJ _ fun k hk => by`. Rewrite using `[hce, if_neg (hk.trans_lt h).ne]]`.

Normalize the expressions using the abelian group laws. Simplify using `[defect_apply]`. Rewrite using `[defect_swap, defect_apply, comm_high hce hf j J (fun k hk => h.le.trans (hJ k hk)) _ fun k hk => by rw [hce, if_neg (hk.trans_lt h).ne]]`. Normalize the expressions using the abelian group laws.
-/
lemma defect_e (i : ι) (J : ι →₀ ℕ) (hJ : ∀ j ∈ J.support, i ≤ j) (x : g) (v : V) :
    defect c δ (zv J v) x (e i) = 0 := by
  have hx : x = strip e c Finset.univ x + ∑ j, c j x • e j := by simp [strip_apply]
  rw [hx, map_add, LinearMap.add_apply, map_sum, LinearMap.sum_apply, Finset.sum_eq_zero, add_zero]
  · rw [defect_apply, comm_high hce hf i J hJ _ fun j _ => c_strip hce (Finset.mem_univ _) x]
    abel
  · intro j _
    rw [map_smul, LinearMap.smul_apply]
    suffices h : defect c δ (zv J v) (e j) (e i) = 0 by rw [h, smul_zero]
    rcases lt_trichotomy i j with h | rfl | h
    · rw [defect_apply, comm_high hce hf i J hJ _ fun k hk => by
        rw [hce, if_neg (hk.trans_lt h).ne]]
      abel
    · simp [defect_apply]
    · rw [defect_swap, defect_apply, comm_high hce hf j J (fun k hk => h.le.trans (hJ k hk)) _
        fun k hk => by rw [hce, if_neg (hk.trans_lt h).ne]]
      abel

omit hce hf [LinearOrder ι] in
/- English proof (translation)
Establish `h' : ∀ j ∈ s, ∀ x, defect c δ m (e j) x = 0` using `fun j hj x => by`. Rewrite using `[defect_swap, h j hj, neg_zero]`. Rewrite using `[strip_apply e c s y, map_sub, map_sum, Finset.sum_eq_zero fun j hj => by`. Rewrite using `[map_smul, h j hj, smul_zero], sub_zero, strip_apply, map_sub, map_sum,`. Use the proof step `LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_zero fun j hj => by`.

Rewrite using `[map_smul, LinearMap.smul_apply, h' j hj, smul_zero], sub_zero]`.
-/
lemma defect_strip (m : MvPolynomial ι R ⊗[R] V) (s : Finset ι)
    (h : ∀ j ∈ s, ∀ x, defect c δ m x (e j) = 0) (x y : g) :
    defect c δ m x y = defect c δ m (strip e c s x) (strip e c s y) := by
  have h' : ∀ j ∈ s, ∀ x, defect c δ m (e j) x = 0 := fun j hj x => by
    rw [defect_swap, h j hj, neg_zero]
  rw [strip_apply e c s y, map_sub, map_sum, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, h j hj, smul_zero], sub_zero, strip_apply, map_sub, map_sum,
    LinearMap.sub_apply, LinearMap.sum_apply, Finset.sum_eq_zero fun j hj => by
    rw [map_smul, LinearMap.smul_apply, h' j hj, smul_zero], sub_zero]

omit hce in
/- English proof (translation)
Rewrite using `[rho_apply, ← hf, step_zero, strip_eq fun j _ => hx j, mulLin_apply]`. Simplify using `[hx]`.
-/
lemma rho_zero_of_k (x : g) (hx : ∀ j, c j x = 0) (v : V) :
    rho c δ x (zv 0 v) = zv 0 (act x v) := by
  rw [rho_apply, ← hf, step_zero, strip_eq fun j _ => hx j, mulLin_apply]
  simp [hx]

/- English proof (translation)
Establish `lin : ∀ n x y, (∀ α v, α.degree < n → defect c δ (zv α v) x y = 0) → ∀ m ∈ degLt R ι V n, defect c δ m x y = 0`. Introduce `n x y h`. Conclude with `eq_on_degLt (rho c δ x * rho c δ y - rho c δ y * rho c δ x - rho c δ ⁅x, y⁆) 0 h`. Proceed by induction on `n with`. Consider the case `zero => exact fun x y => lin 0 x y fun α v h => absurd h (Nat.not_lt_zero _)`.

Consider the case `succ n ih`. Use `fun x y => lin _ x y fun α v hα => ?_` and prove the remaining obligations. Break down `exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩` into its components or cases. Rewrite using `[defect_strip (e := e) _ Finset.univ fun j _ x => defect_e hce hf j 0 (by simp) x v]`. Establish `hx` using `fun j => c_strip hce (Finset.mem_univ j) x`.

Establish `hy` using `fun j => c_strip hce (Finset.mem_univ j) y`. Rewrite using `[defect_apply, rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy, rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy, rho_zero_of_k hf _ (hK _ _ hx hy), hact _ _ hx hy]`. Simplify using the standard rewrite rules. Rewrite using `[defect_strip (e := e) _ (Finset.univ.filter (· ≤ i)) fun j hj x => defect_e hce hf j _ (fun k hk => (show j ≤ i by simpa using hj).trans (le_support_add hJ le_rfl k hk)) x v]`. Establish `hx : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) x) = 0` using `fun j hj => c_strip hce (by simpa using hj) x`.

Establish `hy : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) y) = 0` using `fun j hj => c_strip hce (by simpa using hj) y`. Generalize the expression as in `strip e c (Finset.univ.filter (· ≤ i)) x = x at hx`. Generalize the expression as in `strip e c (Finset.univ.filter (· ≤ i)) y = y at hy`. Rewrite `hα` using `[degree_single_add]`. Establish `hz : zv J v ∈ degLt R ι V n` using `zv_mem (by omega) v`.

Establish `key : ∀ a b : g, (∀ j, j ≤ i → c j b = 0) → defect c δ (rho c δ b (zv J v)) a (e i) = 0`. Introduce `a b hb`. Establish `: defect c δ (rho c δ b (zv J v)) a (e i) = ∑ j, c j b • defect c δ (mulX j (zv J v)) a (e i) + defect c δ (δ b (zv J v)) a (e i)`. Simplify using `only [defect_apply, rho_apply c δ b, mulLin_apply c b, map_add, map_sum, map_smul, smul_sub, Finset.sum_sub_distrib]`. Normalize the expressions using the abelian group laws.

Rewrite using `[this, ih _ _ _ (hp _ _ _ hz), add_zero]`. Use `Finset.sum_eq_zero fun j _ => ?_` and prove the remaining obligations. Distinguish the cases in `hj : j ≤ i`. Simplify using `[hb j hj]`. Rewrite using `[mulX_zv, defect_e hce hf i _ (le_support_add hJ (not_le.mp hj).le), smul_zero]`.

Establish `k1` using `key x y hy`. Establish `k2` using `key y x hx`. Establish `k3` using `ih x y _ hz`. Establish `k4` using `ih ⁅x, e i⁆ y _ hz`. Establish `k5` using `ih x ⁅y, e i⁆ _ hz`.

Establish `k6` using `ih ⁅x, y⁆ (e i) _ hz`. Establish `k7` using `congrArg (rho c δ x) (defect_e hce hf i J hJ y v)`. Establish `k8` using `congrArg (rho c δ y) (defect_e hce hf i J hJ x v)`. Establish `k9` using `congrArg (rho c δ (e i)) k3`. Establish `jac : ⁅⁅x, y⁆, e i⁆ = ⁅⁅x, e i⁆, y⁆ + ⁅x, ⁅y, e i⁆⁆`.

Rewrite using `[leibniz_lie x y (e i), ← lie_skew y ⁅x, e i⁆]`. Normalize the expressions using the abelian group laws. Rewrite using `[← rho_e_le hce hf i J hJ]`. Simplify using `only [defect_apply, map_sub, map_zero, jac, map_add, LinearMap.add_apply] at *`. Take the linear combination `(norm := abel1) k7 - k8 + k1 - k2 + k9 + k4 + k5 - k6`.
-/
lemma defect_eq_zero (hp : Pres δ)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) (n : ℕ) :
    ∀ x y, ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
  have lin : ∀ n x y, (∀ α v, α.degree < n → defect c δ (zv α v) x y = 0) →
      ∀ m ∈ degLt R ι V n, defect c δ m x y = 0 := by
    intro n x y h
    exact eq_on_degLt (rho c δ x * rho c δ y - rho c δ y * rho c δ x - rho c δ ⁅x, y⁆) 0 h
  induction n with
  | zero => exact fun x y => lin 0 x y fun α v h => absurd h (Nat.not_lt_zero _)
  | succ n ih =>
    refine fun x y => lin _ x y fun α v hα => ?_
    rcases exponent_cases α with rfl | ⟨i, J, hJ, rfl⟩
    · rw [defect_strip (e := e) _ Finset.univ fun j _ x => defect_e hce hf j 0 (by simp) x v]
      have hx := fun j => c_strip hce (Finset.mem_univ j) x
      have hy := fun j => c_strip hce (Finset.mem_univ j) y
      rw [defect_apply, rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ hx, rho_zero_of_k hf _ hy,
        rho_zero_of_k hf _ (hK _ _ hx hy), hact _ _ hx hy]
      simp
    · rw [defect_strip (e := e) _ (Finset.univ.filter (· ≤ i)) fun j hj x =>
        defect_e hce hf j _ (fun k hk => (show j ≤ i by simpa using hj).trans
          (le_support_add hJ le_rfl k hk)) x v]
      have hx : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) x) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) x
      have hy : ∀ j, j ≤ i → c j (strip e c (Finset.univ.filter (· ≤ i)) y) = 0 :=
        fun j hj => c_strip hce (by simpa using hj) y
      generalize strip e c (Finset.univ.filter (· ≤ i)) x = x at hx
      generalize strip e c (Finset.univ.filter (· ≤ i)) y = y at hy
      rw [degree_single_add] at hα
      have hz : zv J v ∈ degLt R ι V n := zv_mem (by omega) v
      have key : ∀ a b : g, (∀ j, j ≤ i → c j b = 0) →
          defect c δ (rho c δ b (zv J v)) a (e i) = 0 := by
        intro a b hb
        have : defect c δ (rho c δ b (zv J v)) a (e i) =
            ∑ j, c j b • defect c δ (mulX j (zv J v)) a (e i) +
              defect c δ (δ b (zv J v)) a (e i) := by
          simp only [defect_apply, rho_apply c δ b, mulLin_apply c b, map_add, map_sum, map_smul,
            smul_sub, Finset.sum_sub_distrib]
          abel
        rw [this, ih _ _ _ (hp _ _ _ hz), add_zero]
        refine Finset.sum_eq_zero fun j _ => ?_
        by_cases hj : j ≤ i
        · simp [hb j hj]
        · rw [mulX_zv, defect_e hce hf i _ (le_support_add hJ (not_le.mp hj).le), smul_zero]
      have k1 := key x y hy
      have k2 := key y x hx
      have k3 := ih x y _ hz
      have k4 := ih ⁅x, e i⁆ y _ hz
      have k5 := ih x ⁅y, e i⁆ _ hz
      have k6 := ih ⁅x, y⁆ (e i) _ hz
      have k7 := congrArg (rho c δ x) (defect_e hce hf i J hJ y v)
      have k8 := congrArg (rho c δ y) (defect_e hce hf i J hJ x v)
      have k9 := congrArg (rho c δ (e i)) k3
      have jac : ⁅⁅x, y⁆, e i⁆ = ⁅⁅x, e i⁆, y⁆ + ⁅x, ⁅y, e i⁆⁆ := by
        rw [leibniz_lie x y (e i), ← lie_skew y ⁅x, e i⁆]; abel
      rw [← rho_e_le hce hf i J hJ]
      simp only [defect_apply, map_sub, map_zero, jac, map_add, LinearMap.add_apply] at *
      linear_combination (norm := abel1) k7 - k8 + k1 - k2 + k9 + k4 + k5 - k6

end Fixed

/- English proof (translation)
Take `⟨δ, hp, hf⟩` from `exists_fixed e c act`. Use `⟨rho c δ, fun x y => ext_zv fun α v => ?_, fun x hx v => rho_zero_of_k hf x hx v, fun n x m hm => by simpa [rho_apply] using hp n x m hm⟩` and prove the remaining obligations. Use `defect_eq_zero hce hf hp hK hact _ x y _ (zv_mem (Nat.lt_succ_self α.degree) v)` as an intermediate fact. Rewrite `this` using `[defect_apply, sub_eq_zero]`. Conclude with `this.symm`.
-/
theorem exists_rep (hce : ∀ i j, c i (e j) = if i = j then 1 else 0)
    (hK : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) → ∀ j, c j ⁅x, y⁆ = 0)
    (hact : ∀ x y, (∀ j, c j x = 0) → (∀ j, c j y = 0) →
      act ⁅x, y⁆ = act x * act y - act y * act x) :
    ∃ ρ : g →ₗ[R] Module.End R (MvPolynomial ι R ⊗[R] V),
      (∀ x y, ρ ⁅x, y⁆ = ρ x * ρ y - ρ y * ρ x) ∧
      (∀ x, (∀ j, c j x = 0) → ∀ v, ρ x (zv 0 v) = zv 0 (act x v)) ∧
      ∀ n x, ∀ m ∈ degLt R ι V n, ρ x m - mulLin c x m ∈ degLt R ι V n := by
  obtain ⟨δ, hp, hf⟩ := exists_fixed e c act
  refine ⟨rho c δ, fun x y => ext_zv fun α v => ?_, fun x hx v => rho_zero_of_k hf x hx v,
    fun n x m hm => by simpa [rho_apply] using hp n x m hm⟩
  have := defect_eq_zero hce hf hp hK hact _ x y _ (zv_mem (Nat.lt_succ_self α.degree) v)
  rw [defect_apply, sub_eq_zero] at this
  exact this.symm

end General

end GlobalTheory.InducedPBW
