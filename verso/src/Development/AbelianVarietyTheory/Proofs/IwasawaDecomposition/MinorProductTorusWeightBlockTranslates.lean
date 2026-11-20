import Mathlib
import Formalism.LocalToGlobal.IndefiniteReal.ExistsChosenExtremalVector
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.MainNotions.S Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.Datum Formalism.IndefR.FWT NumberField Matrix
attribute [local instance] Formalism.BasicNotions.Host.cmStar

namespace GlobalTheory.MinorWeight

/- English proof (translation)
Simplify using `only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Simplify using `only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem det_mul_eq_sum {R : Type} [CommRing R] {k m : ℕ} (A : Matrix (Fin k) (Fin m) R) (B : Matrix (Fin m) (Fin k) R) :
    (A * B).det = ∑ f : Fin k → Fin m, (∏ β, B (f β) β) * (A.submatrix id f).det := by
  simp only [Matrix.det_apply', Matrix.mul_apply, Finset.prod_univ_sum, Finset.mul_sum, Fintype.piFinset_univ]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun f _ => Finset.sum_congr rfl fun σ _ => ?_
  simp only [Finset.prod_mul_distrib, Matrix.submatrix_apply, id]
  ring

/- English proof (translation)
Establish `h1 : ∑ β, f β = ∑ x ∈ Finset.univ.image f, x`. Rewrite using `[Finset.sum_image (fun a _ b _ h => hf h)]`. Establish `h2 : (Finset.univ.image f).card = k`. Rewrite using `[Finset.card_image_of_injective _ hf]`. Simplify using the standard rewrite rules.

Use `set s := Finset.univ.image f`. Establish `h3 : ∑ x ∈ s, x = ∑ β : Fin k, s.orderEmbOfFin h2 β` using `by conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s h2]`. Rewrite using `[Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin h2).injective h)]`. Rewrite using `[h1, h3]`. Use `Finset.sum_le_sum fun β _ => ?_` and prove the remaining obligations.

Establish `hm` using `(s.orderEmbOfFin h2).strictMono`. Take `⟨b, hb⟩` from `β`. Proceed by induction on `b with`. Consider the case `zero => simp`. Consider the case `succ b ih`.

Use `ih (by omega) (Finset.mem_univ _)` as an intermediate fact. Establish `h4 : (s.orderEmbOfFin h2) ⟨b, by omega⟩ < (s.orderEmbOfFin h2) ⟨b + 1, hb⟩` using `hm (by simp [Fin.lt_def])`. Conclude with `Nat.succ_le_of_lt (lt_of_le_of_lt this h4)`.
-/
theorem sum_le_sum_of_injective {k : ℕ} (f : Fin k → ℕ) (hf : Function.Injective f) :
    ∑ β : Fin k, (β : ℕ) ≤ ∑ β, f β := by
  have h1 : ∑ β, f β = ∑ x ∈ Finset.univ.image f, x := by
    rw [Finset.sum_image (fun a _ b _ h => hf h)]
  have h2 : (Finset.univ.image f).card = k := by
    rw [Finset.card_image_of_injective _ hf]; simp
  set s := Finset.univ.image f
  have h3 : ∑ x ∈ s, x = ∑ β : Fin k, s.orderEmbOfFin h2 β := by
    conv_lhs => rw [← Finset.image_orderEmbOfFin_univ s h2]
    rw [Finset.sum_image (fun a _ b _ h => (s.orderEmbOfFin h2).injective h)]
  rw [h1, h3]
  refine Finset.sum_le_sum fun β _ => ?_
  have hm := (s.orderEmbOfFin h2).strictMono
  obtain ⟨b, hb⟩ := β
  induction b with
  | zero => simp
  | succ b ih =>
    have := ih (by omega) (Finset.mem_univ _)
    have h4 : (s.orderEmbOfFin h2) ⟨b, by omega⟩ < (s.orderEmbOfFin h2) ⟨b + 1, hb⟩ := hm (by simp [Fin.lt_def])
    exact Nat.succ_le_of_lt (lt_of_le_of_lt this h4)

variable {D : D7} {m n : ℕ}

def wt (τ : D.what₂.Tau) (s : FVar D m n →₀ ℕ) : ℕ := ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j)

/- English proof (translation)
Simplify using `[wt, mul_add, Finset.sum_add_distrib]`.
-/
theorem wt_add (τ : D.what₂.Tau) (s t : FVar D m n →₀ ℕ) : wt τ (s + t) = wt τ s + wt τ t := by
  simp [wt, mul_add, Finset.sum_add_distrib]

def Filt (τ : D.what₂.Tau) (N : ℕ) (P : MvPolynomial (FVar D m n) ℂ) : Prop := ∀ s ∈ P.support, N ≤ wt τ s

/- English proof (translation)
Introduce `_ _` and use `Nat.zero_le _`.
-/
theorem Filt.bot (τ : D.what₂.Tau) (P : MvPolynomial (FVar D m n) ℂ) : Filt τ 0 P := fun _ _ => Nat.zero_le _

/- English proof (translation)
Introduce `s hs` and use `by simp at hs`.
-/
theorem Filt.zero (τ : D.what₂.Tau) (N : ℕ) : Filt τ N (0 : MvPolynomial (FVar D m n) ℂ) := fun s hs => by simp at hs

/- English proof (translation)
Introduce `s hs` and use `hM.trans (h s hs)`.
-/
theorem Filt.mono {τ : D.what₂.Tau} {N M : ℕ} {P : MvPolynomial (FVar D m n) ℂ} (h : Filt τ N P) (hM : M ≤ N) :
    Filt τ M P := fun s hs => hM.trans (h s hs)

/- English proof (translation)
Introduce `s hs`. Break down `Finset.mem_union.1 (MvPolynomial.support_add hs) with h1 | h1` into its components or cases. Use `exacts [h s h1, h' s h1]`.
-/
theorem Filt.add {τ : D.what₂.Tau} {N : ℕ} {P Q : MvPolynomial (FVar D m n) ℂ} (h : Filt τ N P) (h' : Filt τ N Q) :
    Filt τ N (P + Q) := by
  classical
  intro s hs
  rcases Finset.mem_union.1 (MvPolynomial.support_add hs) with h1 | h1
  exacts [h s h1, h' s h1]

/- English proof (translation)
Introduce `s hs`. Take `⟨a, ha, b, hb, rfl⟩` from `Finset.mem_add.1 (MvPolynomial.support_mul P Q hs)`. Rewrite using `[wt_add]`. Conclude with `Nat.add_le_add (h a ha) (h' b hb)`.
-/
theorem Filt.mul {τ : D.what₂.Tau} {N M : ℕ} {P Q : MvPolynomial (FVar D m n) ℂ} (h : Filt τ N P) (h' : Filt τ M Q) :
    Filt τ (N + M) (P * Q) := by
  classical
  intro s hs
  obtain ⟨a, ha, b, hb, rfl⟩ := Finset.mem_add.1 (MvPolynomial.support_mul P Q hs)
  rw [wt_add]
  exact Nat.add_le_add (h a ha) (h' b hb)

/- English proof (translation)
Simplify using `using (Filt.bot τ P).mul h'`.
-/
theorem Filt.mul_left {τ : D.what₂.Tau} {N : ℕ} (P : MvPolynomial (FVar D m n) ℂ) {Q : MvPolynomial (FVar D m n) ℂ}
    (h' : Filt τ N Q) : Filt τ N (P * Q) := by
  simpa using (Filt.bot τ P).mul h'

/- English proof (translation)
The claim follows from `Finset.sum_induction _ (Filt τ N) (fun _ _ => Filt.add) (Filt.zero τ N) h`.
-/
theorem Filt.sum {τ : D.what₂.Tau} {N : ℕ} {ι : Type} (S : Finset ι) (P : ι → MvPolynomial (FVar D m n) ℂ)
    (h : ∀ i ∈ S, Filt τ N (P i)) : Filt τ N (∑ i ∈ S, P i) :=
  Finset.sum_induction _ (Filt τ N) (fun _ _ => Filt.add) (Filt.zero τ N) h

/- English proof (translation)
Proceed by induction on `S using Finset.induction_on with`. Consider the case `empty => simpa using Filt.bot τ 1`. Consider the case `insert a S ha ih`. Rewrite using `[Finset.sum_insert ha, Finset.prod_insert ha]`. Conclude with `(h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))`.
-/
theorem Filt.prod {τ : D.what₂.Tau} {ι : Type} (S : Finset ι) (N : ι → ℕ) (P : ι → MvPolynomial (FVar D m n) ℂ)
    (h : ∀ i ∈ S, Filt τ (N i) (P i)) : Filt τ (∑ i ∈ S, N i) (∏ i ∈ S, P i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simpa using Filt.bot τ 1
  | insert a S ha ih =>
    rw [Finset.sum_insert ha, Finset.prod_insert ha]
    exact (h a (by simp)).mul (ih fun i hi => h i (by simp [hi]))

/- English proof (translation)
Unfold `varF`. Use `split_ifs with h`. Introduce `s hs`. Rewrite `hs` using `[MvPolynomial.support_X, Finset.mem_singleton]`. Substitute `hs` using the available equality.

Unfold `wt`. Use `le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, h.1⟩ : Fin m)))` and prove the remaining obligations. Use `le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j, h.2⟩ : Fin n)))` and prove the remaining obligations. Simplify using the standard rewrite rules. Conclude with `Filt.zero τ i`.
-/
theorem filt_varF (τ : D.what₂.Tau) (i j : ℕ) : Filt τ i (varF τ i j : MvPolynomial (FVar D m n) ℂ) := by
  classical
  unfold varF
  split_ifs with h
  · intro s hs
    rw [MvPolynomial.support_X, Finset.mem_singleton] at hs
    subst hs
    unfold wt
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨i, h.1⟩ : Fin m)))
    refine le_trans ?_ (Finset.single_le_sum (fun _ _ => Nat.zero_le _) (Finset.mem_univ (⟨j, h.2⟩ : Fin n)))
    simp
  · exact Filt.zero τ i

noncomputable def subs (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) :
    MvPolynomial (FVar D m n) ℂ →ₐ[ℂ] MvPolynomial (FVar D m n) ℂ :=
  MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ))

/- English proof (translation)
Distinguish the cases in `hj : j < n`. Simplify using `[varF, hj, subs, MvPolynomial.smul_eq_C_mul, mul_comm]`. Simplify using `[varF, hj]`.
-/
theorem subs_varF (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (τ : D.what₂.Tau) (i : Fin m) (j : ℕ) :
    subs c (varF τ i j : MvPolynomial (FVar D m n) ℂ) = ∑ b : Fin m, varF τ b j * MvPolynomial.C (c τ b i) := by
  by_cases hj : j < n
  · simp [varF, hj, subs, MvPolynomial.smul_eq_C_mul, mul_comm]
  · simp [varF, hj]

/- English proof (translation)
Distinguish the cases in `hi : i < m`. Use `subs_varF (n := n) c τ ⟨i, hi⟩ j` as an intermediate fact. Simplify using `only at this`. Rewrite using `[this, Finset.sum_eq_single (⟨i, hi⟩ : Fin m)]`. Simplify using `[hc]`.

Introduce `b _ hb`. Simplify using `[hc, Matrix.one_apply_ne hb]`. Simplify using the standard rewrite rules. Simplify using `[varF, hi]`.
-/
theorem subs_varF_of_one (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (τ : D.what₂.Tau) (hc : c τ = 1) (i j : ℕ) :
    subs c (varF τ i j : MvPolynomial (FVar D m n) ℂ) = varF τ i j := by
  by_cases hi : i < m
  · have := subs_varF (n := n) c τ ⟨i, hi⟩ j
    simp only at this
    rw [this, Finset.sum_eq_single (⟨i, hi⟩ : Fin m)]
    · simp [hc]
    · intro b _ hb
      simp [hc, Matrix.one_apply_ne hb]
    · simp
  · simp [varF, hi]

noncomputable def mnr (τ : D.what₂.Tau) (p₀ k : ℕ) (r : Fin k → ℕ) : MvPolynomial (FVar D m n) ℂ :=
  (Matrix.of fun α β : Fin k => (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ)).det

def Good (τ : D.what₂.Tau) (p : ℕ) (P : MvPolynomial (FVar D m n) ℂ) (e : Fin m → ℕ) : Prop :=
  (∀ (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (l : Fin m → ℂ), (∀ ρ, ρ ≠ τ → c ρ = 1) → c τ = Matrix.diagonal l →
    subs c P = (∏ a, l a ^ e a) • P) ∧
  ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ ρ, ρ ≠ τ → c ρ = 1) →
    (∀ a b : Fin m, (b : ℕ) < p → p ≤ (a : ℕ) → c τ b a = 0) → Filt τ (∑ a : Fin m, (a : ℕ) * e a) (subs c P)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, fun c l _ _ => by simp, fun c _ _ => by simpa using Filt.bot τ _⟩`.
-/
theorem good_one (τ : D.what₂.Tau) (p : ℕ) : ∃ e, Good τ p (1 : MvPolynomial (FVar D m n) ℂ) e :=
  ⟨0, fun c l _ _ => by simp, fun c _ _ => by simpa using Filt.bot τ _⟩

/- English proof (translation)
Take `⟨e, h1, h2⟩` from `h`. Take `⟨e', h1', h2'⟩` from `h'`. Use `⟨e + e', fun c l hc hl => ?_, fun c hc hb => ?_⟩` and prove the remaining obligations. Rewrite using `[map_mul, h1 c l hc hl, h1' c l hc hl, smul_mul_smul_comm]`. Simplify using `[pow_add, Finset.prod_mul_distrib]`.

Rewrite using `[map_mul]`. Simplify `(h2 c hc hb).mul (h2' c hc hb)` using `[mul_add, Finset.sum_add_distrib]`.
-/
theorem good_mul {τ : D.what₂.Tau} {p : ℕ} {P Q : MvPolynomial (FVar D m n) ℂ} (h : ∃ e, Good τ p P e)
    (h' : ∃ e, Good τ p Q e) : ∃ e, Good τ p (P * Q) e := by
  obtain ⟨e, h1, h2⟩ := h
  obtain ⟨e', h1', h2'⟩ := h'
  refine ⟨e + e', fun c l hc hl => ?_, fun c hc hb => ?_⟩
  · rw [map_mul, h1 c l hc hl, h1' c l hc hl, smul_mul_smul_comm]
    simp [pow_add, Finset.prod_mul_distrib]
  · rw [map_mul]
    simpa [mul_add, Finset.sum_add_distrib] using (h2 c hc hb).mul (h2' c hc hb)

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => simpa using good_one τ p`. Consider the case `succ k ih => rw [pow_succ]`. Conclude with `good_mul ih h`.
-/
theorem good_pow {τ : D.what₂.Tau} {p : ℕ} {P : MvPolynomial (FVar D m n) ℂ} (h : ∃ e, Good τ p P e) (k : ℕ) :
    ∃ e, Good τ p (P ^ k) e := by
  induction k with
  | zero => simpa using good_one τ p
  | succ k ih => rw [pow_succ]; exact good_mul ih h

/- English proof (translation)
The claim follows from `Finset.prod_induction _ (fun P => ∃ e, Good τ p P e) (fun _ _ => good_mul) (good_one τ p) h`.
-/
theorem good_prod {τ : D.what₂.Tau} {p : ℕ} {ι : Type} (S : Finset ι) (P : ι → MvPolynomial (FVar D m n) ℂ)
    (h : ∀ i ∈ S, ∃ e, Good τ p (P i) e) : ∃ e, Good τ p (∏ i ∈ S, P i) e :=
  Finset.prod_induction _ (fun P => ∃ e, Good τ p P e) (fun _ _ => good_mul) (good_one τ p) h

/- English proof (translation)
Unfold `mnr`. Rewrite using `[AlgHom.map_det]`. Both sides reduce to the same expression.
-/
theorem subs_mnr (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (τ : D.what₂.Tau) (p₀ k : ℕ) (r : Fin k → ℕ) :
    subs c (mnr τ p₀ k r : MvPolynomial (FVar D m n) ℂ) =
      (Matrix.of fun α β : Fin k => subs c (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ)).det := by
  unfold mnr
  rw [AlgHom.map_det]
  rfl

/- English proof (translation)
Use `⟨0, fun c l hc _ => ?_, fun c _ _ => by simpa using Filt.bot τ _⟩` and prove the remaining obligations. Rewrite using `[subs_mnr]`. Simplify using `[subs_varF_of_one c ρ (hc ρ hρ), mnr]`.
-/
theorem good_mnr_ne {τ ρ : D.what₂.Tau} (hρ : ρ ≠ τ) (p p₀ k : ℕ) (r : Fin k → ℕ) :
    ∃ e, Good τ p (mnr ρ p₀ k r : MvPolynomial (FVar D m n) ℂ) e := by
  refine ⟨0, fun c l hc _ => ?_, fun c _ _ => by simpa using Filt.bot τ _⟩
  rw [subs_mnr]
  simp [subs_varF_of_one c ρ (hc ρ hρ), mnr]

/- English proof (translation)
Distinguish the cases in `hk : ∀ β : Fin k, p₀ + β < m`. Use `swap`. Use `push_neg at hk`. Take `⟨β, hβ⟩` from `hk`. Establish `h0 : (mnr τ p₀ k r : MvPolynomial (FVar D m n) ℂ) = 0`.

Unfold `mnr`. Use `Matrix.det_eq_zero_of_column_eq_zero β fun α => ?_` and prove the remaining obligations. Simplify using `[varF, not_lt.2 hβ]`. Rewrite using `[h0]`. Conclude with `⟨0, fun c l _ _ => by simp, fun c _ _ => by simpa using Filt.bot τ _⟩`.

Set `col : Fin k → Fin m` to `fun β => ⟨p₀ + β, hk β⟩`. Establish `hs : ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, ∀ α β : Fin k, subs c (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ) = ∑ b : Fin m, varF τ b (r α) * MvPolynomial.C (c τ b (col β))` using `fun c α β => subs_varF c τ (col β) (r α)`. Use `⟨fun a => ∑ β : Fin k, if col β = a then 1 else 0, fun c l _ hl => ?_, fun c _ hb => ?_⟩` and prove the remaining obligations. Establish `h1 : ∏ a, l a ^ (∑ β : Fin k, if col β = a then 1 else 0) = ∏ β, l (col β)`. Simplify using `only [← Finset.prod_pow_eq_pow_sum]`.

Rewrite using `[Finset.prod_comm]`. Use `Finset.prod_congr rfl fun β _ => ?_` and prove the remaining obligations. Simplify using the standard rewrite rules. Rewrite using `[subs_mnr, h1, MvPolynomial.smul_eq_C_mul, map_prod]`. Unfold `mnr`.

Rewrite using `[← Matrix.det_mul_row]`. Use `congr 1`. Use `ext1 α β`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[hs, Finset.sum_eq_single (col β)]`.

Simplify using `[hl, col, mul_comm]`. Introduce `b _ hb`. Simplify using `[hl, Matrix.diagonal_apply_ne _ hb]`. Simplify using the standard rewrite rules. Establish `h1 : ∑ a : Fin m, (a : ℕ) * (∑ β : Fin k, if col β = a then 1 else 0) = ∑ β : Fin k, (p₀ + β)`.

Simplify using `only [Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun β _ => ?_` and prove the remaining obligations. Simplify using `[col]`. Establish `h2 : (Matrix.of fun α β : Fin k => subs c (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ)) = (Matrix.of fun (α : Fin k) (b : Fin m) => (varF τ b (r α) : MvPolynomial (FVar D m n) ℂ)) * (Matrix.of fun (b : Fin m) (β : Fin k) => (MvPolynomial.C (c τ b (col β)) : MvPolynomial …` using `by ext1 α β`.

Simplify using `only [Matrix.of_apply, Matrix.mul_apply, hs]`. Rewrite using `[subs_mnr, h1, h2, det_mul_eq_sum]`. Use `Filt.sum _ _ fun f _ => ?_` and prove the remaining obligations. Distinguish the cases in `hge : ∀ β, p₀ ≤ (f β : ℕ)`. Use `swap`.

Use `push_neg at hge`. Take `⟨β, hβ⟩` from `hge`. Break down `hp with rfl | rfl` into its components or cases. Use linear arithmetic over natural numbers and integers. Rewrite using `[Finset.prod_eq_zero (Finset.mem_univ β), zero_mul]`.

Conclude with `Filt.zero τ _`. Simplify using `[hb (col β) (f β) hβ (by simp [col])]`. Distinguish the cases in `hinj : Function.Injective f`. Use `swap`. Take `⟨β, β', h, hne⟩` from `Function.not_injective_iff.1 hinj`.

Rewrite using `[Matrix.det_zero_of_column_eq hne (fun α => by simp [h]), mul_zero]`. Conclude with `Filt.zero τ _`. Use `Filt.mul_left _ (Filt.mono (N := ∑ β, (f β : ℕ)) ?_ ?_)` and prove the remaining obligations. Rewrite using `[Matrix.det_apply']`. Use `Filt.sum _ _ fun σ _ => Filt.mul_left _ (Filt.prod _ _ _ fun β _ => ?_)` and prove the remaining obligations.

Simplify using `using filt_varF τ _ _`. Establish `h3` using `sum_le_sum_of_injective (fun β => (f β : ℕ) - p₀) (fun β β' h => hinj (Fin.ext (by`. Use `hge β` as an intermediate fact. Use `hge β'` as an intermediate fact. Simplify using `only at h`.

Use the proof step `omega)))`. Establish `h4 : ∑ β, (f β : ℕ) = ∑ β : Fin k, (p₀ + ((f β : ℕ) - p₀))` using `Finset.sum_congr rfl fun β _ => by have := hge β; omega`. Rewrite using `[h4, Finset.sum_add_distrib, Finset.sum_add_distrib]`. Use linear arithmetic over natural numbers and integers.
-/
theorem good_mnr_self (τ : D.what₂.Tau) (p p₀ k : ℕ) (hp : p₀ = 0 ∨ p₀ = p) (r : Fin k → ℕ) :
    ∃ e, Good τ p (mnr τ p₀ k r : MvPolynomial (FVar D m n) ℂ) e := by
  classical
  by_cases hk : ∀ β : Fin k, p₀ + β < m
  swap
  · push_neg at hk
    obtain ⟨β, hβ⟩ := hk
    have h0 : (mnr τ p₀ k r : MvPolynomial (FVar D m n) ℂ) = 0 := by
      unfold mnr
      refine Matrix.det_eq_zero_of_column_eq_zero β fun α => ?_
      simp [varF, not_lt.2 hβ]
    rw [h0]
    exact ⟨0, fun c l _ _ => by simp, fun c _ _ => by simpa using Filt.bot τ _⟩
  let col : Fin k → Fin m := fun β => ⟨p₀ + β, hk β⟩
  have hs : ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, ∀ α β : Fin k,
      subs c (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ) =
        ∑ b : Fin m, varF τ b (r α) * MvPolynomial.C (c τ b (col β)) := fun c α β => subs_varF c τ (col β) (r α)
  refine ⟨fun a => ∑ β : Fin k, if col β = a then 1 else 0, fun c l _ hl => ?_, fun c _ hb => ?_⟩
  · have h1 : ∏ a, l a ^ (∑ β : Fin k, if col β = a then 1 else 0) = ∏ β, l (col β) := by
      simp only [← Finset.prod_pow_eq_pow_sum]
      rw [Finset.prod_comm]
      refine Finset.prod_congr rfl fun β _ => ?_
      simp
    rw [subs_mnr, h1, MvPolynomial.smul_eq_C_mul, map_prod]
    unfold mnr
    rw [← Matrix.det_mul_row]
    congr 1
    ext1 α β
    simp only [Matrix.of_apply]
    rw [hs, Finset.sum_eq_single (col β)]
    · simp [hl, col, mul_comm]
    · intro b _ hb
      simp [hl, Matrix.diagonal_apply_ne _ hb]
    · simp
  · have h1 : ∑ a : Fin m, (a : ℕ) * (∑ β : Fin k, if col β = a then 1 else 0) = ∑ β : Fin k, (p₀ + β) := by
      simp only [Finset.mul_sum]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun β _ => ?_
      simp [col]
    have h2 : (Matrix.of fun α β : Fin k => subs c (varF τ (p₀ + β) (r α) : MvPolynomial (FVar D m n) ℂ)) =
        (Matrix.of fun (α : Fin k) (b : Fin m) => (varF τ b (r α) : MvPolynomial (FVar D m n) ℂ)) *
        (Matrix.of fun (b : Fin m) (β : Fin k) => (MvPolynomial.C (c τ b (col β)) : MvPolynomial (FVar D m n) ℂ)) := by
      ext1 α β
      simp only [Matrix.of_apply, Matrix.mul_apply, hs]
    rw [subs_mnr, h1, h2, det_mul_eq_sum]
    refine Filt.sum _ _ fun f _ => ?_
    by_cases hge : ∀ β, p₀ ≤ (f β : ℕ)
    swap
    · push_neg at hge
      obtain ⟨β, hβ⟩ := hge
      rcases hp with rfl | rfl
      · omega
      · rw [Finset.prod_eq_zero (Finset.mem_univ β), zero_mul]
        · exact Filt.zero τ _
        · simp [hb (col β) (f β) hβ (by simp [col])]
    by_cases hinj : Function.Injective f
    swap
    · obtain ⟨β, β', h, hne⟩ := Function.not_injective_iff.1 hinj
      rw [Matrix.det_zero_of_column_eq hne (fun α => by simp [h]), mul_zero]
      exact Filt.zero τ _
    refine Filt.mul_left _ (Filt.mono (N := ∑ β, (f β : ℕ)) ?_ ?_)
    · rw [Matrix.det_apply']
      refine Filt.sum _ _ fun σ _ => Filt.mul_left _ (Filt.prod _ _ _ fun β _ => ?_)
      simpa using filt_varF τ _ _
    · have h3 := sum_le_sum_of_injective (fun β => (f β : ℕ) - p₀) (fun β β' h => hinj (Fin.ext (by
        have := hge β; have := hge β'; simp only at h; omega)))
      have h4 : ∑ β, (f β : ℕ) = ∑ β : Fin k, (p₀ + ((f β : ℕ) - p₀)) :=
        Finset.sum_congr rfl fun β _ => by have := hge β; omega
      rw [h4, Finset.sum_add_distrib, Finset.sum_add_distrib]
      omega

/- English proof (translation)
Unfold `delta deltaAt`. Use `good_prod _ _ fun ρ _ => good_mul (good_prod _ _ fun i _ => good_pow ?_ _) (good_prod _ _ fun i _ => good_pow ?_ _)` and prove the remaining obligations. Establish `h : (minorPlus ρ (i + 1) : MvPolynomial (FVar D m n) ℂ) = mnr ρ 0 (i + 1) (fun α => α)`. Simplify using `[minorPlus, mnr]`. Rewrite using `[h]`.

Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Conclude with `good_mnr_self _ _ _ _ (Or.inl rfl) _`. Conclude with `good_mnr_ne hρ _ _ _ _`. Establish `h : (minorMinus ρ (p ρ) (i + 1) : MvPolynomial (FVar D m n) ℂ) = mnr ρ (p ρ) (i + 1) (fun α => n - (i + 1) + α)` using `rfl`.

Rewrite using `[h]`. Distinguish the cases in `hρ : ρ = τ`. Substitute `hρ` using the available equality. Conclude with `good_mnr_self _ _ _ _ (Or.inr rfl) _`. Conclude with `good_mnr_ne hρ _ _ _ _`.
-/
theorem good_delta (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau) :
    ∃ e, Good τ (p τ) (delta p q ap am : MvPolynomial (FVar D m n) ℂ) e := by
  unfold delta deltaAt
  refine good_prod _ _ fun ρ _ => good_mul (good_prod _ _ fun i _ => good_pow ?_ _) (good_prod _ _ fun i _ => good_pow ?_ _)
  · have h : (minorPlus ρ (i + 1) : MvPolynomial (FVar D m n) ℂ) = mnr ρ 0 (i + 1) (fun α => α) := by
      simp [minorPlus, mnr]
    rw [h]
    by_cases hρ : ρ = τ
    · subst hρ; exact good_mnr_self _ _ _ _ (Or.inl rfl) _
    · exact good_mnr_ne hρ _ _ _ _
  · have h : (minorMinus ρ (p ρ) (i + 1) : MvPolynomial (FVar D m n) ℂ) =
        mnr ρ (p ρ) (i + 1) (fun α => n - (i + 1) + α) := rfl
    rw [h]
    by_cases hρ : ρ = τ
    · subst hρ; exact good_mnr_self _ _ _ _ (Or.inr rfl) _
    · exact good_mnr_ne hρ _ _ _ _

/- English proof (translation)
Introduce `_ _ _ p q ap am τ` and use `good_delta p q ap am τ`.
-/
theorem delta_torus_weight : ∀ (D : D7) (m n : ℕ) (p q : D.what₂.Tau → ℕ) (ap am : D.what₂.Tau → ℕ → ℕ) (τ : D.what₂.Tau), ∃ e : Fin m → ℕ, (∀ (c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ) (l : Fin m → ℂ), (∀ ρ, ρ ≠ τ → c ρ = 1) → c τ = Matrix.diagonal l → MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ) = (∏ a, l a ^ e a) • (delta p q ap am : MvPolynomial (FVar D m n) ℂ)) ∧ ∀ c : D.what₂.Tau → Matrix (Fin m) (Fin m) ℂ, (∀ ρ, ρ ≠ τ → c ρ = 1) → (∀ a b : Fin m, (b : ℕ) < p τ → p τ ≤ (a : ℕ) → c τ b a = 0) → ∀ s ∈ (MvPolynomial.aeval (fun v : FVar D m n => ∑ b, c v.1 b v.2.1 • (MvPolynomial.X (v.1, b, v.2.2) : MvPolynomial (FVar D m n) ℂ)) (delta p q ap am : MvPolynomial (FVar D m n) ℂ)).support, ∑ a : Fin m, (a : ℕ) * e a ≤ ∑ a : Fin m, ∑ j : Fin n, (a : ℕ) * s (τ, a, j) :=
  fun _ _ _ p q ap am τ => good_delta p q ap am τ

end GlobalTheory.MinorWeight
