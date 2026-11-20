import Mathlib
import Development.AbelianVarietyTheory.Statements.CuspFrameWeights.EigenfunctionFiniteCoefficients

open MeasureTheory Matrix Finset Formalism.MainNotions.S Formalism.REAL Formalism.QuantumDeterminants GlobalTheory.Dec GlobalTheory.DSId
open scoped InnerProductSpace

noncomputable section

namespace GlobalTheory.LowestKTypeDetermines

variable {n : ℕ} {ε ε' : Fin n → Bool} {H H' : Type} [NormedAddCommGroup H] [InnerProductSpace ℂ H]
  [NormedAddCommGroup H'] [InnerProductSpace ℂ H']
  {σ σ' : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)} {τ : Matrix (Fin n) (Fin n) ℂ → (H' →L[ℂ] H')}

/- English proof (translation)
Establish `hg1 : gᴴ * g = 1` using `(Matrix.mem_unitaryGroup_iff').1 hg.1`. Use `show gᴴ * Jm ε * g = Jm ε`. Rewrite using `[Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]`.
-/
theorem Kset_sub {g : Matrix (Fin n) (Fin n) ℂ} (hg : g ∈ Kset ε) : g ∈ UJset ε := by
  have hg1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
  show gᴴ * Jm ε * g = Jm ε
  rw [Matrix.mul_assoc, ← hg.2, ← Matrix.mul_assoc, hg1, Matrix.one_mul]

/- English proof (translation)
Introduce `g hg v`. Apply `T.injective` to reduce the goal to its premises. Rewrite using `[h g hg]`. Simplify using the standard rewrite rules.
-/
theorem symm_inter (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) :
    ∀ g ∈ UJset ε, ∀ v, T.symm (τ g v) = σ g (T.symm v) := by
  intro g hg v
  apply T.injective
  rw [h g hg]; simp

/- English proof (translation)
Take `⟨T, h⟩` from `h`. Conclude with `⟨T.symm, symm_inter T h⟩`.
-/
theorem uEquiv_symm (h : UEquiv ε σ τ) : UEquiv ε τ σ := by
  obtain ⟨T, h⟩ := h
  exact ⟨T.symm, symm_inter T h⟩

/- English proof (translation)
Take `⟨T, h⟩` from `h`. Take `⟨T', h'⟩` from `h'`. Conclude with `⟨T.trans T', fun g hg v => by simp [h g hg, h' g hg]⟩`.
-/
theorem uEquiv_trans {H'' : Type} [NormedAddCommGroup H''] [InnerProductSpace ℂ H'']
    {υ : Matrix (Fin n) (Fin n) ℂ → (H'' →L[ℂ] H'')} (h : UEquiv ε σ τ) (h' : UEquiv ε τ υ) : UEquiv ε σ υ := by
  obtain ⟨T, h⟩ := h
  obtain ⟨T', h'⟩ := h'
  exact ⟨T.trans T', fun g hg v => by simp [h g hg, h' g hg]⟩

/- English proof (translation)
Introduce `θ hθ`. Rewrite using `[← h _ (Kset_sub hθ), hv θ hθ, map_smul]`.
-/
theorem wt_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ μ v) : IsWtOn (Kset ε) τ μ (T v) := by
  intro θ hθ
  rw [← h _ (Kset_sub hθ), hv θ hθ, map_smul]

/- English proof (translation)
Take `⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩` from `hS`. Use `⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `g hg _ ⟨x, hx, rfl⟩`. Conclude with `⟨σ g x, h2 g hg x hx, h g (Kset_sub hg) x⟩`. Introduce `S' hle hst`.

Break down `h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H')) (by` into its components or cases. Introduce `x hx`. Take `⟨y, hy, e⟩` from `hle hx`. Establish `: y = x` using `T.injective e`. Conclude with `this ▸ hy) (by`.

Introduce `g hg x hx`. Use `show T (σ g x) ∈ S'`. Rewrite using `[h g (Kset_sub hg)]`. Conclude with `hst g hg _ hx) with e | e`. Use `left`.

Rewrite using `[eq_bot_iff]`. Introduce `x hx`. Establish `: T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H')` using `by show T (T.symm x) ∈ S'`. Simplify using `using hx`. Rewrite `this` using `[e]`.

Simplify using `using this`. Use `right`. Use `le_antisymm hle ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Rewrite `hx` using `[← e]`.

Conclude with `hx`. Introduce and unpack `μ _ ⟨x, hx, rfl⟩ h0 hw`. Use `wt_transfer T.symm (symm_inter T h) hw` as an intermediate fact. Use `h5 μ x hx (by rintro rfl; simp at h0) ?_` and prove the remaining obligations. Simplify using `using this`.
-/
theorem ktype_transfer (T : H ≃ₗᵢ[ℂ] H') (h : ∀ g ∈ UJset ε, ∀ v, T (σ g v) = τ g (T v)) {Λ : Fin n → ℝ}
    {S : Submodule ℂ H} (hS : IsKTypeOf ε σ Λ S) :
    IsKTypeOf ε τ Λ (S.map (T.toLinearEquiv : H →ₗ[ℂ] H')) := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  refine ⟨inferInstance, ?_, ?_, ⟨T v, ⟨v, hv, rfl⟩, by simpa using hv0, wt_transfer T h hvw⟩, ?_⟩
  · rintro g hg _ ⟨x, hx, rfl⟩
    exact ⟨σ g x, h2 g hg x hx, h g (Kset_sub hg) x⟩
  · intro S' hle hst
    rcases h3 (S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H')) (by
        intro x hx
        obtain ⟨y, hy, e⟩ := hle hx
        have : y = x := T.injective e
        exact this ▸ hy) (by
        intro g hg x hx
        show T (σ g x) ∈ S'
        rw [h g (Kset_sub hg)]
        exact hst g hg _ hx) with e | e
    · left
      rw [eq_bot_iff]
      intro x hx
      have : T.symm x ∈ S'.comap (T.toLinearEquiv : H →ₗ[ℂ] H') := by
        show T (T.symm x) ∈ S'
        simpa using hx
      rw [e] at this
      simpa using this
    · right
      refine le_antisymm hle ?_
      rintro _ ⟨x, hx, rfl⟩
      rw [← e] at hx
      exact hx
  · rintro μ _ ⟨x, hx, rfl⟩ h0 hw
    have := wt_transfer T.symm (symm_inter T h) hw
    refine h5 μ x hx (by rintro rfl; simp at h0) ?_
    simpa using this

/- English proof (translation)
Take `⟨T, h⟩` from `h`. Take `⟨S, hS⟩` from `hS`. Conclude with `⟨_, ktype_transfer T h hS⟩`.
-/
theorem exists_ktype_of_uEquiv (h : UEquiv ε σ τ) {Λ : Fin n → ℝ} (hS : ∃ S, IsKTypeOf ε σ Λ S) :
    ∃ S, IsKTypeOf ε τ Λ S := by
  obtain ⟨T, h⟩ := h
  obtain ⟨S, hS⟩ := hS
  exact ⟨_, ktype_transfer T h hS⟩

/- English proof (translation)
Establish `hJ : Jm ε = (Jm ε').submatrix s.symm s.symm`. Use extensionality with `i j`. Simplify using `[Jm, Matrix.diagonal_apply, hε]`. Use `⟨?_, ?_⟩` and prove the remaining obligations. Establish `h1 : gᴴ * g = 1` using `(Matrix.mem_unitaryGroup_iff').1 hg.1`.

Rewrite using `[Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix, Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]`. Rewrite using `[hJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg.2]`.
-/
theorem submatrix_mem_Kset (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a)) {g : Matrix (Fin n) (Fin n) ℂ}
    (hg : g ∈ Kset ε') : g.submatrix s.symm s.symm ∈ Kset ε := by
  have hJ : Jm ε = (Jm ε').submatrix s.symm s.symm := by
    ext i j
    simp [Jm, Matrix.diagonal_apply, hε]
  refine ⟨?_, ?_⟩
  · have h1 : gᴴ * g = 1 := (Matrix.mem_unitaryGroup_iff').1 hg.1
    rw [Matrix.mem_unitaryGroup_iff', Matrix.star_eq_conjTranspose, Matrix.conjTranspose_submatrix,
      Matrix.submatrix_mul_equiv, h1, Matrix.submatrix_one_equiv]
  · rw [hJ, Matrix.submatrix_mul_equiv, Matrix.submatrix_mul_equiv, hg.2]

/- English proof (translation)
Introduce `θ hθ`. Establish `e : (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).submatrix s.symm s.symm = Matrix.diagonal fun a => Complex.exp (((θ ∘ s.symm) a : ℂ) * Complex.I)` using `Matrix.submatrix_diagonal_equiv _ _`. Establish `h1` using `submatrix_mem_Kset s hε hθ`. Rewrite `h1` using `[e]`. Rewrite using `[hσ, e, hv _ h1, ← Equiv.sum_comp s]`.

Simplify using the standard rewrite rules.
-/
theorem wt_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hσ : ∀ g, σ' g = σ (g.submatrix s.symm s.symm)) {μ : Fin n → ℝ} {v : H}
    (hv : IsWtOn (Kset ε) σ μ v) : IsWtOn (Kset ε') σ' (μ ∘ s) v := by
  intro θ hθ
  have e : (Matrix.diagonal fun a => Complex.exp ((θ a : ℂ) * Complex.I)).submatrix s.symm s.symm =
      Matrix.diagonal fun a => Complex.exp (((θ ∘ s.symm) a : ℂ) * Complex.I) :=
    Matrix.submatrix_diagonal_equiv _ _
  have h1 := submatrix_mem_Kset s hε hθ
  rw [e] at h1
  rw [hσ, e, hv _ h1, ← Equiv.sum_comp s]
  simp

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `[root, Pi.single_apply]`.
-/
theorem root_comp (s : Equiv.Perm (Fin n)) (a b : Fin n) : root (s a) (s b) ∘ s = root a b := by
  funext i
  simp [root, Pi.single_apply]

/- English proof (translation)
Break down `lt_trichotomy a b with h1 | h1 | h1` into its components or cases. Conclude with `h1`. Conclude with `absurd h (by simp [h1])`. Conclude with `absurd h (not_lt.2 (hs b a h1 he.symm).le)`.
-/
theorem lt_of_perm_lt {s : Equiv.Perm (Fin n)} (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {a b : Fin n}
    (h : s a < s b) (he : ε (s a) = ε (s b)) : a < b := by
  rcases lt_trichotomy a b with h1 | h1 | h1
  · exact h1
  · exact absurd h (by simp [h1])
  · exact absurd h (not_lt.2 (hs b a h1 he.symm).le)

/- English proof (translation)
Take `⟨c, hc, e⟩` from `h`. Use `⟨fun a b => c (s a) (s b), fun a b h => ⟨lt_of_perm_lt hs (hc _ _ h).1 (hc _ _ h).2, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[hε, hε]`. Conclude with `(hc _ _ h).2`. Use function extensionality and compare the values at `i`.

Use `congrFun e (s i)` as an intermediate fact. Simplify using `only [Pi.sub_apply, Finset.sum_apply] at this`. Simplify using `only [Pi.sub_apply, Function.comp_apply, this, Finset.sum_apply]`. Rewrite using `[← Equiv.sum_comp s]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations.

Rewrite using `[← Equiv.sum_comp s]`. Use `Finset.sum_congr rfl fun b _ => ?_` and prove the remaining obligations. Rewrite using `[← root_comp s a b]`. Both sides reduce to the same expression.
-/
theorem cDom_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) {μ Λ : Fin n → ℝ} (h : CDom ε μ Λ) :
    CDom ε' (μ ∘ s) (Λ ∘ s) := by
  obtain ⟨c, hc, e⟩ := h
  refine ⟨fun a b => c (s a) (s b), fun a b h => ⟨lt_of_perm_lt hs (hc _ _ h).1 (hc _ _ h).2, ?_⟩, ?_⟩
  · rw [hε, hε]; exact (hc _ _ h).2
  · funext i
    have := congrFun e (s i)
    simp only [Pi.sub_apply, Finset.sum_apply] at this
    simp only [Pi.sub_apply, Function.comp_apply, this, Finset.sum_apply]
    rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [← Equiv.sum_comp s]
    refine Finset.sum_congr rfl fun b _ => ?_
    rw [← root_comp s a b]
    rfl

/- English proof (translation)
Take `⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩` from `hS`. Establish `hε' : ∀ a, ε a = ε' (s.symm a)` using `fun a => by rw [hε]; simp`. Establish `hσ' : ∀ g, σ g = σ' (g.submatrix s.symm.symm s.symm.symm)` using `fun g => by`. Rewrite using `[hσ]`. Simplify using `[Matrix.submatrix_submatrix]`.

Use `⟨h1, fun g hg x hx => ?_, fun S' hle hst => h3 S' hle fun g hg x hx => ?_, ⟨v, hv, hv0, wt_perm s hε hσ hvw⟩, fun μ x hx h0 hw => ?_⟩` and prove the remaining obligations. Rewrite using `[hσ]`. Conclude with `h2 _ (submatrix_mem_Kset s hε hg) x hx`. Rewrite using `[hσ']`. Conclude with `hst _ (submatrix_mem_Kset s.symm hε' hg) x hx`.

Use `cDom_perm s hε hs (h5 _ x hx h0 (wt_perm s.symm hε' hσ' hw))` as an intermediate fact. Simplify `this` using `[Function.comp_assoc]`.
-/
theorem ktype_perm (s : Equiv.Perm (Fin n)) (hε : ∀ a, ε' a = ε (s a))
    (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b)
    (hσ : ∀ g, σ' g = σ (g.submatrix s.symm s.symm)) {Λ : Fin n → ℝ} {S : Submodule ℂ H}
    (hS : IsKTypeOf ε σ Λ S) : IsKTypeOf ε' σ' (Λ ∘ s) S := by
  obtain ⟨h1, h2, h3, ⟨v, hv, hv0, hvw⟩, h5⟩ := hS
  have hε' : ∀ a, ε a = ε' (s.symm a) := fun a => by rw [hε]; simp
  have hσ' : ∀ g, σ g = σ' (g.submatrix s.symm.symm s.symm.symm) := fun g => by
    rw [hσ]; simp [Matrix.submatrix_submatrix]
  refine ⟨h1, fun g hg x hx => ?_, fun S' hle hst => h3 S' hle fun g hg x hx => ?_,
    ⟨v, hv, hv0, wt_perm s hε hσ hvw⟩, fun μ x hx h0 hw => ?_⟩
  · rw [hσ]; exact h2 _ (submatrix_mem_Kset s hε hg) x hx
  · rw [hσ']; exact hst _ (submatrix_mem_Kset s.symm hε' hg) x hx
  · have := cDom_perm s hε hs (h5 _ x hx h0 (wt_perm s.symm hε' hσ' hw))
    simpa [Function.comp_assoc] using this

/- English proof (translation)
Use function extensionality and compare the values at `a`. Establish `h1 : (univ.filter fun b => a < b ∧ (ε ∘ s) b = (ε ∘ s) a).card = (univ.filter fun b => s a < b ∧ ε b = ε (s a)).card`. Use `Finset.card_equiv s fun b => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]`. Conclude with `⟨fun h => ⟨hs _ _ h.1 h.2.symm, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2.symm, h.2⟩⟩`.

Establish `h2 : (univ.filter fun b => b < a ∧ (ε ∘ s) b = (ε ∘ s) a).card = (univ.filter fun b => b < s a ∧ ε b = ε (s a)).card`. Use `Finset.card_equiv s fun b => ?_` and prove the remaining obligations. Simplify using `only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]`. Conclude with `⟨fun h => ⟨hs _ _ h.1 h.2, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2, h.2⟩⟩`. Simplify using `only [rhoC, Function.comp_apply] at h1 h2 ⊢`.

Rewrite using `[h1, h2]`.
-/
theorem rhoC_perm (s : Equiv.Perm (Fin n)) (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) :
    rhoC (ε ∘ s) = rhoC ε ∘ s := by
  funext a
  have h1 : (univ.filter fun b => a < b ∧ (ε ∘ s) b = (ε ∘ s) a).card =
      (univ.filter fun b => s a < b ∧ ε b = ε (s a)).card := by
    refine Finset.card_equiv s fun b => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun h => ⟨hs _ _ h.1 h.2.symm, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2.symm, h.2⟩⟩
  have h2 : (univ.filter fun b => b < a ∧ (ε ∘ s) b = (ε ∘ s) a).card =
      (univ.filter fun b => b < s a ∧ ε b = ε (s a)).card := by
    refine Finset.card_equiv s fun b => ?_
    simp only [Finset.mem_filter, Finset.mem_univ, true_and, Function.comp_apply]
    exact ⟨fun h => ⟨hs _ _ h.1 h.2, h.2⟩, fun h => ⟨lt_of_perm_lt hs h.1 h.2, h.2⟩⟩
  simp only [rhoC, Function.comp_apply] at h1 h2 ⊢
  rw [h1, h2]

/- English proof (translation)
Use function extensionality and compare the values at `a`. Use `Formalism.REAL.rhoStd n ε a` as an intermediate fact. Simplify using `only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem lowK_add (ε : Fin n → Bool) (lam : Fin n → ℝ) : lowK ε lam + (2 : ℝ) • rhoC ε = lam + Formalism.QuantumDeterminants.rhoStd n := by
  funext a
  have := Formalism.REAL.rhoStd n ε a
  simp only [lowK, Formalism.QuantumDeterminants.rhoStd, Pi.add_apply, Pi.sub_apply, Pi.smul_apply, smul_eq_mul]
  linarith

/- English proof (translation)
Introduce `a b hab`. Establish `h1` using `h hab`. Establish `h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ)` using `by exact_mod_cast hab`. Simplify using `only [Pi.add_apply, Formalism.QuantumDeterminants.rhoStd]`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem strictAnti_add_rho {lam : Fin n → ℝ} (h : StrictAnti lam) : StrictAnti (lam + Formalism.QuantumDeterminants.rhoStd n) := by
  intro a b hab
  have h1 := h hab
  have h2 : ((a : ℕ) : ℝ) < ((b : ℕ) : ℝ) := by exact_mod_cast hab
  simp only [Pi.add_apply, Formalism.QuantumDeterminants.rhoStd]
  linarith

/- English proof (translation)
Use `set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • root a b with hQ`. Establish `hroot : ∀ a b, ∑ i, x i * root a b i = x a - x b`. Introduce `a b`. Simplify using `[root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]`. Establish `hdot : 0 ≤ ∑ i, x i * Q i`.

Establish `: ∑ i, x i * Q i = ∑ a, ∑ b, (c a b : ℝ) * (x a - x b)`. Simplify using `only [hQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← hroot]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Rewrite using `[Finset.sum_comm]`.

Use `Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring` and prove the remaining obligations. Rewrite using `[this]`. Use `Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_` and prove the remaining obligations. Distinguish the cases in `h : c a b = 0`. Simplify using `[h]`.

Conclude with `mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hx (hc a b h).le))`. Establish `: nsq (x + Q) = nsq x + 2 * ∑ i, x i * Q i + nsq Q`. Simplify using `only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]`. Conclude with `Finset.sum_congr rfl fun i _ => by ring`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem nsq_add_cone {x : Fin n → ℝ} (hx : Antitone x) {c : Fin n → Fin n → ℕ} (hc : ∀ a b, c a b ≠ 0 → a < b) :
    nsq x + nsq (∑ a, ∑ b, (c a b : ℝ) • root a b) ≤ nsq (x + ∑ a, ∑ b, (c a b : ℝ) • root a b) := by
  set Q : Fin n → ℝ := ∑ a, ∑ b, (c a b : ℝ) • root a b with hQ
  have hroot : ∀ a b, ∑ i, x i * root a b i = x a - x b := by
    intro a b
    simp [root, mul_sub, Finset.sum_sub_distrib, Pi.single_apply]
  have hdot : 0 ≤ ∑ i, x i * Q i := by
    have : ∑ i, x i * Q i = ∑ a, ∑ b, (c a b : ℝ) * (x a - x b) := by
      simp only [hQ, Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Finset.mul_sum, ← hroot]
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [Finset.sum_comm]
      refine Finset.sum_congr rfl fun b _ => Finset.sum_congr rfl fun i _ => by ring
    rw [this]
    refine Finset.sum_nonneg fun a _ => Finset.sum_nonneg fun b _ => ?_
    by_cases h : c a b = 0
    · simp [h]
    · exact mul_nonneg (Nat.cast_nonneg _) (sub_nonneg.2 (hx (hc a b h).le))
  have : nsq (x + Q) = nsq x + 2 * ∑ i, x i * Q i + nsq Q := by
    simp only [nsq, dot, Pi.add_apply, Finset.mul_sum, ← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by ring
  linarith

/- English proof (translation)
The claim follows from `Finset.sum_nonneg (s := univ) (f := fun i => x i * x i) fun _ _ => mul_self_nonneg _`.
-/
theorem nsq_nonneg (x : Fin n → ℝ) : 0 ≤ nsq x :=
  Finset.sum_nonneg (s := univ) (f := fun i => x i * x i) fun _ _ => mul_self_nonneg _

/- English proof (translation)
Use function extensionality and compare the values at `i`. Use `(Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1 (show ∑ j, x j * x j = 0 from le_antisymm h (nsq_nonneg x)) i (Finset.mem_univ i)` as an intermediate fact. Conclude with `mul_self_eq_zero.1 this`.
-/
theorem eq_zero_of_nsq {x : Fin n → ℝ} (h : nsq x ≤ 0) : x = 0 := by
  funext i
  have := (Finset.sum_eq_zero_iff_of_nonneg (fun j _ => mul_self_nonneg (x j))).1
    (show ∑ j, x j * x j = 0 from le_antisymm h (nsq_nonneg x)) i (Finset.mem_univ i)
  exact mul_self_eq_zero.1 this

/- English proof (translation)
The claim follows from `Equiv.sum_comp s fun a => x a * x a`.
-/
theorem nsq_comp (s : Equiv.Perm (Fin n)) (x : Fin n → ℝ) : nsq (x ∘ s) = nsq x :=
  Equiv.sum_comp s fun a => x a * x a

/- English proof (translation)
Take `⟨⟨c1, c2, c3, c4, c5⟩, -, h1, h2⟩` from `h`. Use `⟨c1, c2, c3, c4, c5, h1.exists, fun μ S hS => ?_⟩` and prove the remaining obligations. Take `⟨c, hc, rfl⟩` from `h2 μ S hS`. Unfold `vNormSq`. Rewrite using `[add_right_comm, lowK_add]`.

Use `nsq_add_cone (strictAnti_add_rho hl.1).antitone hc` as an intermediate fact. Combine the linear relations using `[nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]`.
-/
theorem isDS_of_isHCDS {lam : Fin n → ℝ} (hl : IsHCParam lam) (h : IsHCDS ε lam σ) : IsDS ε lam σ := by
  obtain ⟨⟨c1, c2, c3, c4, c5⟩, -, h1, h2⟩ := h
  refine ⟨c1, c2, c3, c4, c5, h1.exists, fun μ S hS => ?_⟩
  obtain ⟨c, hc, rfl⟩ := h2 μ S hS
  unfold vNormSq
  rw [add_right_comm, lowK_add]
  have := nsq_add_cone (strictAnti_add_rho hl.1).antitone hc
  linarith [nsq_nonneg (∑ a, ∑ b, (c a b : ℝ) • root a b)]

/- English proof (translation)
Take `⟨-, -, -, -, -, ⟨S, hS⟩, hmin⟩` from `hσ`. Take `⟨-, -, h1, h2⟩` from `hτ`. Take `⟨S₁, hS₁⟩` from `exists_ktype_of_uEquiv he ⟨S, ktype_perm (ε' := ε ∘ s) s (fun _ => rfl) hs (fun _ => rfl) hS⟩`. Take `⟨c, hc, e⟩` from `h2 _ _ hS₁`. Take `⟨S₂, hS₂⟩` from `exists_ktype_of_uEquiv (uEquiv_symm he) h1.exists`.

Establish `h3` using `hmin _ _ (ktype_perm (ε := ε ∘ s) (ε' := ε) (σ' := σ) s.symm (fun a => by simp) (fun a b hab h => lt_of_perm_lt hs (by simpa using hab) h) (fun g => by simp [Matrix.submatrix_submatrix]) hS₂)`. Unfold `vNormSq at h3`. Establish `e1 : (lowK (ε ∘ s) mu ∘ s.symm + (2 : ℝ) • rhoC ε) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n`. Rewrite using `[← lowK_add (ε ∘ s), rhoC_perm s hs]`. Use function extensionality and compare the values at `a`.

Simplify using the standard rewrite rules. Establish `e2 : (lam + Formalism.QuantumDeterminants.rhoStd n) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b`. Rewrite using `[← lowK_add (ε ∘ s) mu, add_right_comm, ← e, ← lowK_add ε lam, rhoC_perm s hs]`. Both sides reduce to the same expression. Rewrite `h3` using `[lowK_add, ← nsq_comp s, ← nsq_comp s (_ + (2 : ℝ) • rhoC ε), e1, e2]`.

Establish `h4` using `nsq_add_cone (strictAnti_add_rho hm.1).antitone hc`. Rewrite `e2` using `[eq_zero_of_nsq (x := ∑ a, ∑ b, (c a b : ℝ) • root a b) (by linarith), add_zero]`. Establish `h5 : StrictMono s` using `fun a b hab => by`. Use `strictAnti_add_rho hm.1 hab` as an intermediate fact. Rewrite `this` using `[← e2]`.

Conclude with `(strictAnti_add_rho hl.1).lt_iff_gt.1 this`. Establish `h6 : s = 1`. Use `Subsingleton.elim (h5.orderIsoOfSurjective _ s.surjective) (OrderIso.refl _)` as an intermediate fact. Conclude with `Equiv.ext fun a => DFunLike.congr_fun this a`. Substitute `h6` using the available equality.

Conclude with `⟨rfl, (add_right_cancel (e2 : lam + Formalism.QuantumDeterminants.rhoStd n = mu + Formalism.QuantumDeterminants.rhoStd n)).symm⟩`.
-/
theorem param_eq {lam mu : Fin n → ℝ} (hl : IsHCParam lam) (hm : IsHCParam mu) (hσ : IsDS ε lam σ)
    (s : Equiv.Perm (Fin n)) (hs : ∀ a b, a < b → ε (s a) = ε (s b) → s a < s b) (hτ : IsHCDS (ε ∘ s) mu τ)
    (he : UEquiv (ε ∘ s) (fun g => σ (g.submatrix s.symm s.symm)) τ) : s = 1 ∧ mu = lam := by
  obtain ⟨-, -, -, -, -, ⟨S, hS⟩, hmin⟩ := hσ
  obtain ⟨-, -, h1, h2⟩ := hτ
  obtain ⟨S₁, hS₁⟩ := exists_ktype_of_uEquiv he
    ⟨S, ktype_perm (ε' := ε ∘ s) s (fun _ => rfl) hs (fun _ => rfl) hS⟩
  obtain ⟨c, hc, e⟩ := h2 _ _ hS₁
  obtain ⟨S₂, hS₂⟩ := exists_ktype_of_uEquiv (uEquiv_symm he) h1.exists
  have h3 := hmin _ _ (ktype_perm (ε := ε ∘ s) (ε' := ε) (σ' := σ) s.symm (fun a => by simp)
    (fun a b hab h => lt_of_perm_lt hs (by simpa using hab) h)
    (fun g => by simp [Matrix.submatrix_submatrix]) hS₂)
  unfold vNormSq at h3
  have e1 : (lowK (ε ∘ s) mu ∘ s.symm + (2 : ℝ) • rhoC ε) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n := by
    rw [← lowK_add (ε ∘ s), rhoC_perm s hs]
    funext a
    simp
  have e2 : (lam + Formalism.QuantumDeterminants.rhoStd n) ∘ s = mu + Formalism.QuantumDeterminants.rhoStd n + ∑ a, ∑ b, (c a b : ℝ) • root a b := by
    rw [← lowK_add (ε ∘ s) mu, add_right_comm, ← e, ← lowK_add ε lam, rhoC_perm s hs]
    rfl
  rw [lowK_add, ← nsq_comp s, ← nsq_comp s (_ + (2 : ℝ) • rhoC ε), e1, e2] at h3
  have h4 := nsq_add_cone (strictAnti_add_rho hm.1).antitone hc
  rw [eq_zero_of_nsq (x := ∑ a, ∑ b, (c a b : ℝ) • root a b) (by linarith), add_zero] at e2
  have h5 : StrictMono s := fun a b hab => by
    have := strictAnti_add_rho hm.1 hab
    rw [← e2] at this
    exact (strictAnti_add_rho hl.1).lt_iff_gt.1 this
  have h6 : s = 1 := by
    have := Subsingleton.elim (h5.orderIsoOfSurjective _ s.surjective) (OrderIso.refl _)
    exact Equiv.ext fun a => DFunLike.congr_fun this a
  subst h6
  exact ⟨rfl, (add_right_cancel (e2 : lam + Formalism.QuantumDeterminants.rhoStd n = mu + Formalism.QuantumDeterminants.rhoStd n)).symm⟩

/- English proof (translation)
Take `⟨G, _, _, π, hπ, hex⟩` from `h n`. Use `⟨G ε lam, _, _, π ε lam, hπ ε lam hl, fun H _ _ σ hσ => ?_⟩` and prove the remaining obligations. Take `⟨s, mu, hm, hs, he⟩` from `hex ε H σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1⟩`. Take `⟨rfl, rfl⟩` from `param_eq hl hm hσ s hs (hπ _ _ hm) he`. Conclude with `he`.
-/
theorem exists_model (h : DSClass) (ε : Fin n → Bool) {lam : Fin n → ℝ} (hl : IsHCParam lam) :
    ∃ (G : Type) (_ : NormedAddCommGroup G) (_ : InnerProductSpace ℂ G)
      (π : Matrix (Fin n) (Fin n) ℂ → (G →L[ℂ] G)), IsHCDS ε lam π ∧
      ∀ (H : Type) [NormedAddCommGroup H] [InnerProductSpace ℂ H]
        (σ : Matrix (Fin n) (Fin n) ℂ → (H →L[ℂ] H)), IsDS ε lam σ → UEquiv ε σ π := by
  obtain ⟨G, _, _, π, hπ, hex⟩ := h n
  refine ⟨G ε lam, _, _, π ε lam, hπ ε lam hl, fun H _ _ σ hσ => ?_⟩
  obtain ⟨s, mu, hm, hs, he⟩ := hex ε H σ ⟨hσ.1, hσ.2.1, hσ.2.2.1, hσ.2.2.2.1, hσ.2.2.2.2.1⟩
  obtain ⟨rfl, rfl⟩ := param_eq hl hm hσ s hs (hπ _ _ hm) he
  exact he

/- English proof (translation)
Introduce `n ε lam H _ _ σ H' _ _ σ' hl hσ hσ'`. Take `⟨G, _, _, π, -, key⟩` from `exists_model h ε hl`. Conclude with `uEquiv_trans (key H σ hσ) (uEquiv_symm (key H' σ' hσ'))`.
-/
theorem dsUnique_of_dsClass (h : DSClass) : DSUnique := by
  intro n ε lam H _ _ σ H' _ _ σ' hl hσ hσ'
  obtain ⟨G, _, _, π, -, key⟩ := exists_model h ε hl
  exact uEquiv_trans (key H σ hσ) (uEquiv_symm (key H' σ' hσ'))

/- English proof (translation)
Introduce `n ε lam hl`. Take `⟨G, _, _, π, hπ, -⟩` from `exists_model h ε hl`. Conclude with `⟨G, _, _, π, isDS_of_isHCDS hl hπ⟩`.
-/
theorem dsExists_of_dsClass (h : DSClass) : DSExists := by
  intro n ε lam hl
  obtain ⟨G, _, _, π, hπ, -⟩ := exists_model h ε hl
  exact ⟨G, _, _, π, isDS_of_isHCDS hl hπ⟩

/- English proof (translation)
Introduce `n ε lam H _ _ σ hl hσ μ S hS`. Take `⟨G, _, _, π, hπ, key⟩` from `exists_model h ε hl`. Take `⟨S', hS'⟩` from `exists_ktype_of_uEquiv (key H σ hσ) ⟨S, hS⟩`. Conclude with `hπ.2.2.2 μ S' hS'`.
-/
theorem kTypesAbove_of_dsClass (h : DSClass) : KTypesAbove := by
  intro n ε lam H _ _ σ hl hσ μ S hS
  obtain ⟨G, _, _, π, hπ, key⟩ := exists_model h ε hl
  obtain ⟨S', hS'⟩ := exists_ktype_of_uEquiv (key H σ hσ) ⟨S, hS⟩
  exact hπ.2.2.2 μ S' hS'

/- English proof (translation)
Introduce `n ε lam H _ _ σ hl hσ S S' hS hS'`. Take `⟨G, _, _, π, hπ, key⟩` from `exists_model h ε hl`. Take `⟨T, hT⟩` from `key H σ hσ`. Conclude with `Submodule.map_injective_of_injective (f := (T.toLinearEquiv : H →ₗ[ℂ] G)) T.injective (hπ.2.2.1.unique (ktype_transfer T hT hS) (ktype_transfer T hT hS'))`.
-/
theorem lowKMultOne_of_dsClass (h : DSClass) : LowKMultOne := by
  intro n ε lam H _ _ σ hl hσ S S' hS hS'
  obtain ⟨G, _, _, π, hπ, key⟩ := exists_model h ε hl
  obtain ⟨T, hT⟩ := key H σ hσ
  exact Submodule.map_injective_of_injective (f := (T.toLinearEquiv : H →ₗ[ℂ] G)) T.injective
    (hπ.2.2.1.unique (ktype_transfer T hT hS) (ktype_transfer T hT hS'))

end GlobalTheory.LowestKTypeDetermines
