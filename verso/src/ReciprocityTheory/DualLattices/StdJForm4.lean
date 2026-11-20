import ReciprocityTheory.DualLattices.InvolutionPermApplyZero

noncomputable section

open Matrix

namespace ReciprocityTheory.PGsh.Up

open ReciprocityTheory.PGsh.L2

variable {p : ℕ} [Fact p.Prime] {g : ℕ} {C : Type} [Field C] {v : Valuation C NNReal} {R : Type}
  [CommRing R] [Algebra R C] [Algebra ℤ_[p] R] {O : Type} [CommRing O] [Algebra ℤ_[p] O]
  {σ : O ≃ₐ[ℤ_[p]] O} {cp : R}

/- English proof (translation)
Use `set F := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hF`. Establish `hFa : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], M.map (algebraMap ℤ_[p] R) = F M` using `fun M => rfl`. Establish `hFt : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], (F M)ᵀ = F Mᵀ` using `fun M => rfl`. Set `π2` to `pi2 e π hσ`. Establish `hπ2 : ∀ k, π2 (π2 k) = k` using `involutionPerm_involutive e π hσ horth hS.invol`.

Set `εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R` to `Fin.lastCases (F H.P) (fun i => F (H.ρ (e i)))`. Set `εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R` to `Fin.lastCases H.PL (fun i => H.ρL (e i))`. Set `π' : Equiv.Perm (Fin (m + 1))` to `finSuccEquivLast.symm.permCongr (Equiv.optionCongr π2)`. Establish `hTc : ∀ i : Fin m, εT i.castSucc = F (H.ρ (e i))` using `fun i => by simp [εT]`. Establish `hTl : εT (Fin.last m) = F H.P` using `by simp [εT]`.

Establish `hLc : ∀ i : Fin m, εL i.castSucc = H.ρL (e i)` using `fun i => by simp [εL]`. Establish `hLl : εL (Fin.last m) = H.PL` using `by simp [εL]`. Establish `hπc : ∀ i : Fin m, π' i.castSucc = (π2 i).castSucc` using `fun i => by`. Simplify using `[π', Equiv.permCongr_apply]`. Establish `hπl : π' (Fin.last m) = Fin.last m` using `by simp [π', Equiv.permCongr_apply]`.

Establish `hPρ : ∀ i, H.P * H.ρ (e i) = 0` using `fun i => by rw [H.projectors.2.2.2.1, hPT]`. Establish `hPLρ : ∀ i, H.PL * H.ρL (e i) = 0` using `fun i => by rw [H.projectors.2.2.2.2, hPL]`. Establish `h1 : ∀ i, π' (π' i) = i`. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[hπl, hπl]`. Rewrite using `[hπc, hπc, hπ2]`. Establish `h2 : ∀ i j, εT i * εT j = if i = j then εT i else 0`. Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`.

Rewrite using `[hTl, ← map_mul, H.projectors.1, if_pos rfl]`. Rewrite using `[hTl, hTc, ← map_mul, hPρ, map_zero, if_neg (Fin.castSucc_lt_last j).ne']`. Rewrite using `[hTl, hTc, ← map_mul, hPT, map_zero, if_neg (Fin.castSucc_lt_last i).ne]`. Rewrite using `[hTc, hTc, ← map_mul, ← map_mul, horth]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero, map_zero]`. Establish `h3 : ∑ i, εT i = 1`. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `only [hTc, hTl]`. Rewrite using `[← map_sum F (fun i => H.ρ (e i)), ← map_add, hsT, map_one]`. Establish `h4 : ∀ i j, εL i * εL j = if i = j then εL i else 0`. Introduce `i j`. Apply the tactic sequence `refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j`.

Rewrite using `[hLl, H.projectors.2.1, if_pos rfl]`. Rewrite using `[hLl, hLc, hPLρ, if_neg (Fin.castSucc_lt_last j).ne']`. Rewrite using `[hLl, hLc, hPL, if_neg (Fin.castSucc_lt_last i).ne]`. Rewrite using `[hLc, hLc, ← map_mul, horth]`. Distinguish the cases in `hij : i = j`.

Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Rewrite using `[if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero]`. Establish `h5 : ∑ i, εL i = 1`. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `only [hLc, hLl]`. Conclude with `hsL`. Establish `h6 : ∀ i, H.Ht * εT i = (εL (π' i))ᵀ * H.Ht`. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[hTl, hπl, hLl, ← hFa, H.Ht_equivariant.2]`. Rewrite using `[hTc, hπc, hLc, ← hFa, H.Ht_equivariant.1, involutionPerm_sigma e π hσ i]`. Establish `h7 : ∀ i, (εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) = H.E.map (algebraMap ℤ_[p] R) * εT (π' i)`. Introduce `i`. Use `Fin.lastCases ?_ (fun i => ?_) i` and prove the remaining obligations.

Rewrite using `[hTl, hπl, hTl, hFa, hFt, ← map_mul, ← map_mul, H.projectors.2.2.1]`. Rewrite using `[hTc, hπc, hTc, hFa, hFt, ← map_mul, ← map_mul, H.E_equivariant, involutionPerm_sigma e π hσ i]`. Establish `hu` using `u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π' h1 h2 h3 h4 h5 h6 h7 H.form_eq_alt`. Establish `hB : (∑ i, εL i * H.Bt * εT i) = btP H e`. Rewrite using `[Fin.sum_univ_castSucc]`.

Simplify using `only [hLc, hLl, hTc, hTl, btP, hFa]`. Take `⟨hA, hC, -⟩` from `hu`. Rewrite `hA`, `hC` using `[hB]`. Use `⟨hA, fun i => ?_, ?_⟩` and prove the remaining obligations. Use `hC i.castSucc` as an intermediate fact.

Rewrite `this` using `[hTc, hLc, ← hFa]`. Conclude with `this`. Use `hC (Fin.last m)` as an intermediate fact. Rewrite `this` using `[hTl, hLl, ← hFa]`. Conclude with `this`.
-/
theorem btP_facts (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (btP H e)ᵀ * H.Ht - H.Htᵀ * btP H e = cp • H.E.map (algebraMap ℤ_[p] R) ∧
    (∀ i, btP H e * (H.ρ (e i)).map (algebraMap ℤ_[p] R) = H.ρL (e i) * btP H e) ∧
    btP H e * H.P.map (algebraMap ℤ_[p] R) = H.PL * btP H e := by
  classical
  set F := (algebraMap ℤ_[p] R).mapMatrix (m := Ix g) with hF
  have hFa : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], M.map (algebraMap ℤ_[p] R) = F M := fun M => rfl
  have hFt : ∀ M : Matrix (Ix g) (Ix g) ℤ_[p], (F M)ᵀ = F Mᵀ := fun M => rfl
  let π2 := pi2 e π hσ
  have hπ2 : ∀ k, π2 (π2 k) = k := involutionPerm_involutive e π hσ horth hS.invol
  let εT : Fin (m + 1) → Matrix (Ix g) (Ix g) R :=
    Fin.lastCases (F H.P) (fun i => F (H.ρ (e i)))
  let εL : Fin (m + 1) → Matrix (Fin g) (Fin g) R :=
    Fin.lastCases H.PL (fun i => H.ρL (e i))
  let π' : Equiv.Perm (Fin (m + 1)) := finSuccEquivLast.symm.permCongr (Equiv.optionCongr π2)
  have hTc : ∀ i : Fin m, εT i.castSucc = F (H.ρ (e i)) := fun i => by simp [εT]
  have hTl : εT (Fin.last m) = F H.P := by simp [εT]
  have hLc : ∀ i : Fin m, εL i.castSucc = H.ρL (e i) := fun i => by simp [εL]
  have hLl : εL (Fin.last m) = H.PL := by simp [εL]
  have hπc : ∀ i : Fin m, π' i.castSucc = (π2 i).castSucc := fun i => by
    simp [π', Equiv.permCongr_apply]
  have hπl : π' (Fin.last m) = Fin.last m := by simp [π', Equiv.permCongr_apply]
  have hPρ : ∀ i, H.P * H.ρ (e i) = 0 := fun i => by rw [H.projectors.2.2.2.1, hPT]
  have hPLρ : ∀ i, H.PL * H.ρL (e i) = 0 := fun i => by rw [H.projectors.2.2.2.2, hPL]
  have h1 : ∀ i, π' (π' i) = i := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hπl, hπl]
    · rw [hπc, hπc, hπ2]
  have h2 : ∀ i j, εT i * εT j = if i = j then εT i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hTl, ← map_mul, H.projectors.1, if_pos rfl]
    · rw [hTl, hTc, ← map_mul, hPρ, map_zero, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hTl, hTc, ← map_mul, hPT, map_zero, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hTc, hTc, ← map_mul, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero, map_zero]
  have h3 : ∑ i, εT i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hTc, hTl]
    rw [← map_sum F (fun i => H.ρ (e i)), ← map_add, hsT, map_one]
  have h4 : ∀ i j, εL i * εL j = if i = j then εL i else 0 := by
    intro i j
    refine Fin.lastCases ?_ (fun i => ?_) i <;> refine Fin.lastCases ?_ (fun j => ?_) j
    · rw [hLl, H.projectors.2.1, if_pos rfl]
    · rw [hLl, hLc, hPLρ, if_neg (Fin.castSucc_lt_last j).ne']
    · rw [hLl, hLc, hPL, if_neg (Fin.castSucc_lt_last i).ne]
    · rw [hLc, hLc, ← map_mul, horth]
      by_cases hij : i = j
      · subst hij; simp
      · rw [if_neg hij, if_neg (fun h => hij (Fin.castSucc_injective _ h)), map_zero]
  have h5 : ∑ i, εL i = 1 := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl]
    exact hsL
  have h6 : ∀ i, H.Ht * εT i = (εL (π' i))ᵀ * H.Ht := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hLl, ← hFa, H.Ht_equivariant.2]
    · rw [hTc, hπc, hLc, ← hFa, H.Ht_equivariant.1, involutionPerm_sigma e π hσ i]
  have h7 : ∀ i, (εT i)ᵀ * H.E.map (algebraMap ℤ_[p] R) =
      H.E.map (algebraMap ℤ_[p] R) * εT (π' i) := by
    intro i
    refine Fin.lastCases ?_ (fun i => ?_) i
    · rw [hTl, hπl, hTl, hFa, hFt, ← map_mul, ← map_mul, H.projectors.2.2.1]
    · rw [hTc, hπc, hTc, hFa, hFt, ← map_mul, ← map_mul, H.E_equivariant, involutionPerm_sigma e π hσ i]
  have hu := u1 R g (m + 1) H.Ht H.Bt (H.E.map (algebraMap ℤ_[p] R)) cp εT εL π' h1 h2 h3 h4 h5
    h6 h7 H.form_eq_alt
  have hB : (∑ i, εL i * H.Bt * εT i) = btP H e := by
    rw [Fin.sum_univ_castSucc]
    simp only [hLc, hLl, hTc, hTl, btP, hFa]
  obtain ⟨hA, hC, -⟩ := hu
  rw [hB] at hA hC
  refine ⟨hA, fun i => ?_, ?_⟩
  · have := hC i.castSucc
    rw [hTc, hLc, ← hFa] at this
    exact this
  · have := hC (Fin.last m)
    rw [hTl, hLl, ← hFa] at this
    exact this

/- English proof (translation)
Rewrite using `[Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun a _ => ?_` and prove the remaining obligations. Apply the tactic sequence `simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply] <;> ring`.
-/
private lemma stdJ_form4 {D : Type} [CommRing D] {g : ℕ}
    (M : Matrix (Fin g ⊕ Fin g) (Fin g ⊕ Fin g) D) (i j : Fin g ⊕ Fin g) :
    (Mᵀ * stdJ D g * M) i j =
      ∑ a, (M (Sum.inr a) i * M (Sum.inl a) j - M (Sum.inl a) i * M (Sum.inr a) j) := by
  rw [Matrix.mul_assoc, Matrix.mul_apply, Fintype.sum_sum_type, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun a _ => ?_
  simp [Matrix.mul_apply, stdJ, Fintype.sum_sum_type, Matrix.one_apply] <;> ring

/- English proof (translation)
Take `⟨h1, -, -⟩` from `btP_facts hS H e π horth hσ hsT hPT hsL hPL`. Use extensionality with `i j`. Rewrite using `[stdJ_form4, ← h1, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply, ← Finset.sum_sub_distrib]`. Both sides reduce to the same expression.
-/
theorem phiP_J (hS : HodgeTateSetting p v R O σ cp) (H : HodgeTateDatum p g v R O σ cp) {m : ℕ} (e : Fin m → O)
    (π : Equiv.Perm (Fin m)) (horth : ∀ i j, e i * e j = if i = j then e i else 0)
    (hσ : ∀ i, σ (e i) = e (π i)) (hsT : (∑ i, H.ρ (e i)) + H.P = 1)
    (hPT : ∀ i, H.ρ (e i) * H.P = 0) (hsL : (∑ i, H.ρL (e i)) + H.PL = 1)
    (hPL : ∀ i, H.ρL (e i) * H.PL = 0) :
    (phiP H e)ᵀ * stdJ R g * phiP H e = cp • H.E.map (algebraMap ℤ_[p] R) := by
  obtain ⟨h1, -, -⟩ := btP_facts hS H e π horth hσ hsT hPT hsL hPL
  ext i j
  rw [stdJ_form4, ← h1, Matrix.sub_apply, Matrix.mul_apply, Matrix.mul_apply,
    ← Finset.sum_sub_distrib]
  rfl

end ReciprocityTheory.PGsh.Up
