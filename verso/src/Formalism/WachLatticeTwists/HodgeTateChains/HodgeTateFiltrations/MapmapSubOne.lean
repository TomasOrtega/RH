import Formalism.WachLatticeTwists.HodgeTateChains.StatWChain
import Formalism.WachLatticeTwists.HodgeTateChains.HodgeTateFiltrations.CancelRight

noncomputable section

namespace Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic

open Matrix

/- English proof (translation)
Use extensionality with `i j`. Simplify using the standard rewrite rules.
-/
lemma map_smul_hom {R S : Type} [CommRing R] [CommRing S] (f : R →+* S) (c : R) {r : ℕ}
    (M : Matrix (Fin r) (Fin r) R) : (c • M).map f = f c • M.map f := by
  ext i j; simp

/- English proof (translation)
Proceed by induction on `k with`. Consider the case `zero => intro a ha`. Simplify using `using ha`. Consider the case `succ k ih => intro a ha; exact ih a (h _ (by rw [← mul_assoc, ← pow_succ']; exact ha))`.
-/
lemma pow_nzd {R : Type} [CommRing R] {y : R} (h : ∀ a : R, y * a = 0 → a = 0) (k : ℕ) :
    ∀ a : R, y ^ k * a = 0 → a = 0 := by
  induction k with
  | zero => intro a ha; simpa using ha
  | succ k ih => intro a ha; exact ih a (h _ (by rw [← mul_assoc, ← pow_succ']; exact ha))

/- English proof (translation)
Introduce `ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ u hι hal hA hg hϑ hx hnz`. Use `set R : Matrix (Fin r) (Fin r) AA := (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA) with hR`. Establish `hRι : R.map ι = (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC)`. Use extensionality with `i j`. Simplify using `[hR, hal]`.

Establish `h1 : (A.map gA).map ι = (A.map ι).map (act g)`. Use extensionality with `i j`. Simplify using `[hg]`. Establish `h2 : (A.map ι).map (act g) = (ι (gA (jA x))) ^ M0 • W.Xx.map (act g)`. Rewrite using `[hA]`.

Use extensionality with `i j`. Simplify using `[hg]`. Establish `h3 : (jA x) ^ M0 • (A.map gA * R) = (gA (jA x)) ^ M0 • ((W.Gm g).map jA * A)`. Establish `hinj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι)`. Introduce `M N h`.

Use extensionality with `i j`. Conclude with `hι (congrFun (congrFun h i) j)`. Apply `hinj` to reduce the goal to its premises. Use `show ((jA x) ^ M0 • (A.map gA * R)).map ι = ((gA (jA x)) ^ M0 • ((W.Gm g).map jA * A)).map ι`. Rewrite using `[map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, h1, h2, hRι, Matrix.smul_mul, W.W2, hA, Matrix.mul_smul, map_pow, map_pow, smul_comm]`.

Establish `h4` using `congrArg (fun M : Matrix (Fin r) (Fin r) AA => M.map ϑ) h3`. Simplify using `only [map_smul_hom, Matrix.map_mul, map_pow, hϑ, hx] at h4`. Establish `h5 : (A.map gA).map ϑ = (A.map ϑ).map τ`. Use extensionality with `i j`. Simplify using `[hϑ]`.

Rewrite `h4` using `[h5]`. Establish `h7 : ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ = (ϑ (jA u)) ^ M0 • (((W.Gm g).map jA).map ϑ * A.map ϑ)`. Rewrite using `[map_smul_hom, map_smul_hom, Matrix.smul_mul, map_pow, map_pow]`. Rewrite using `[h7]`. Use extensionality with `i j`.

Establish `h6` using `congrFun (congrFun h4 i) j`. Simplify using `only [Matrix.smul_apply, smul_eq_mul] at h6 ⊢`. Use `sub_eq_zero.1 (pow_nzd hnz M0 _ ?_)` and prove the remaining obligations. Rewrite using `[mul_sub, h6, mul_pow]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem wActU : StatWActU := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ u hι hal hA hg hϑ hx
    hnz
  set R : Matrix (Fin r) (Fin r) AA := (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)
    with hR
  have hRι : R.map ι = (ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] WC) := by
    ext i j; simp [hR, hal]
  have h1 : (A.map gA).map ι = (A.map ι).map (act g) := by
    ext i j; simp [hg]
  have h2 : (A.map ι).map (act g) = (ι (gA (jA x))) ^ M0 • W.Xx.map (act g) := by
    rw [hA]
    ext i j
    simp [hg]

  have h3 : (jA x) ^ M0 • (A.map gA * R) = (gA (jA x)) ^ M0 • ((W.Gm g).map jA * A) := by
    have hinj : Function.Injective (fun M : Matrix (Fin r) (Fin r) AA => M.map ι) := by
      intro M N h
      ext i j
      exact hι (congrFun (congrFun h i) j)
    apply hinj
    show ((jA x) ^ M0 • (A.map gA * R)).map ι = ((gA (jA x)) ^ M0 • ((W.Gm g).map jA * A)).map ι
    rw [map_smul_hom, map_smul_hom, Matrix.map_mul, Matrix.map_mul, h1, h2, hRι, Matrix.smul_mul, W.W2, hA,
      Matrix.mul_smul, map_pow, map_pow, smul_comm]
  have h4 := congrArg (fun M : Matrix (Fin r) (Fin r) AA => M.map ϑ) h3
  simp only [map_smul_hom, Matrix.map_mul, map_pow, hϑ, hx] at h4
  have h5 : (A.map gA).map ϑ = (A.map ϑ).map τ := by
    ext i j; simp [hϑ]
  rw [h5] at h4
  have h7 : ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ
      = (ϑ (jA u)) ^ M0 • (((W.Gm g).map jA).map ϑ * A.map ϑ) := by
    rw [map_smul_hom, map_smul_hom, Matrix.smul_mul, map_pow, map_pow]
  rw [h7]
  ext i j
  have h6 := congrFun (congrFun h4 i) j
  simp only [Matrix.smul_apply, smul_eq_mul] at h6 ⊢
  refine sub_eq_zero.1 (pow_nzd hnz M0 _ ?_)
  rw [mul_sub, h6, mul_pow]
  ring

/- English proof (translation)
Introduce `ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ hι hal hA hg hϑ hx hnz`. Establish `h` using `wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g gA τ 1 hι hal hA hg hϑ (by rw [map_one, map_one, one_mul]; exact hx) hnz`. Rewrite `h` using `[one_pow, one_smul]`. Then use the resulting hypothesis.
-/
theorem wAct : StatWAct := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ A g gA τ hι hal hA hg hϑ hx hnz
  have h := wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g gA τ 1 hι hal hA hg hϑ
    (by rw [map_one, map_one, one_mul]; exact hx) hnz
  rwa [one_pow, one_smul] at h

/- English proof (translation)
Introduce `ℓ OC _ y c k hk hc hl a ha`. Apply `hl` to reduce the goal to its premises. Take `⟨k, rfl⟩ : ∃ k', k = k' + 1` from `⟨k - 1, by omega⟩`. Rewrite using `[← hc, pow_succ]`. Combine the equalities or inequalities in the displayed calculation.
-/
theorem xNzd : StatXNzd := by
  intro ℓ OC _ y c k hk hc hl a ha
  apply hl
  obtain ⟨k, rfl⟩ : ∃ k', k = k' + 1 := ⟨k - 1, by omega⟩
  rw [← hc, pow_succ]
  calc y ^ k * y * c * a = y ^ k * c * (y * a) := by ring
    _ = 0 := by rw [ha, mul_zero]

/- English proof (translation)
Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hij]`.
-/
lemma mapmap_sub_one {As AA OC : Type} [CommRing As] [CommRing AA] [CommRing OC] (jA : As →+* AA)
    (ϑ : AA →+* OC) {r : ℕ} (M : Matrix (Fin r) (Fin r) As) (i j : Fin r) :
    ((M.map jA).map ϑ - 1) i j = (ϑ.comp jA) ((M - 1) i j) := by
  by_cases hij : i = j
  · subst hij; simp
  · simp [hij]

/- English proof (translation)
Introduce `ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ gA τ z ϖ ϖ' s hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl`. Take `⟨A, Y', hA, h1, h2⟩` from `wSandwich' ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c hL hι hx hξ hc`. Establish `hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)` using `Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)`. Use `⟨A, Y', hA, h1, h2, ?_, ?_⟩` and prove the remaining obligations. Conclude with `wAct ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A _ gA τ hι hal hA hgA hϑ hτ (xNzd ℓ OC _ c _ hk hc hl)`.

Introduce `i j`. Rewrite using `[mapmap_sub_one]`. Conclude with `wUm ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W γ σ (ϑ.comp jA) z ϖ ϖ' s (n0 ℓ (M0 + h0)) hfix (hι.comp hj) hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ i j`.
-/
theorem wChain : StatWChain := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ gA τ z ϖ ϖ' s
    hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl
  obtain ⟨A, Y', hA, h1, h2⟩ := wSandwich' ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c
    hL hι hx hξ hc
  have hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)
  refine ⟨A, Y', hA, h1, h2, ?_, ?_⟩
  · exact wAct ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A _ gA τ hι hal hA hgA hϑ hτ
      (xNzd ℓ OC _ c _ hk hc hl)
  · intro i j
    rw [mapmap_sub_one]
    exact wUm ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W γ σ (ϑ.comp jA) z ϖ ϖ' s
      (n0 ℓ (M0 + h0)) hfix (hι.comp hj) hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ i j

/- English proof (translation)
Introduce `ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ actA actO z ϖ ϖ' s hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl hH hu`. Take `⟨A, Y', hA, h1, h2, h3, h4⟩` from `wChain ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c γ σ (actA (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : AA →+* AA) (actO (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : OC →+* OC) z ϖ ϖ' s hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ (hgA _) (hϑ _) hτ hl`. Establish `hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1)` using `Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)`. Establish `hnz` using `xNzd ℓ OC _ c _ hk hc hl`. Establish `hU : ∀ (g : Gg) (u : As), act g (ι (jA x)) = ι (jA (u * x)) → (A.map ϑ).map (actO g) * (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ) = ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ`.

Introduce `g u hgu`. Use `wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g (actA g : AA →+* AA) (actO g : OC →+* OC) u hι hal hA (hgA g) (hϑ g) ?_ hnz` and prove the remaining obligations. Establish `: actA g (jA x) = jA (u * x)` using `hι (by rw [hgA, hgu])`. Use `show actO g (ϑ (jA x)) = _`. Rewrite using `[← hϑ, this, map_mul, map_mul]`.

Use `⟨A, Y', hA, h1, h2, ?_, ?_, ?_, h3, h4⟩` and prove the remaining obligations. Introduce `h hh`. Establish `e` using `hU h 1 (by rw [one_mul]; exact hH h hh x)`. Rewrite `e` using `[one_pow, one_smul, wFix ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W (hι.comp hj) h hh]`. Rewrite using `[e, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]`.

Introduce `g`. Take `⟨u, hgu⟩` from `hu g`. Conclude with `⟨_, hU g u hgu⟩`. Conclude with `wEnd ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A hι hal hA`.
-/
theorem wD : StatWD := by
  intro ℓ _ As AA WC OC _ _ _ _ _ _ jA ι φ Gg _ H act GK _ inc r ρ πs ξ x M0 h0 W ϑ c γ σ actA actO z ϖ ϖ' s
    hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ hgA hϑ hτ hl hH hu
  obtain ⟨A, Y', hA, h1, h2, h3, h4⟩ := wChain ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ c γ σ
    (actA (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : AA →+* AA) (actO (γ ^ (ℓ ^ (s + n0 ℓ (M0 + h0) + 1))) : OC →+* OC)
    z ϖ ϖ' s hL hι hx hξ hc hal hfix hj hσ hσ1 hσ2 hπ hϖ' hz hϖ hzϖ (hgA _) (hϑ _) hτ hl
  have hk : 1 ≤ ℓ ^ n0 ℓ (M0 + h0) * (ℓ - 1) :=
    Nat.mul_pos (pow_pos (Fact.out : ℓ.Prime).pos _) (by have := (Fact.out : ℓ.Prime).two_le; omega)
  have hnz := xNzd ℓ OC _ c _ hk hc hl
  have hU : ∀ (g : Gg) (u : As), act g (ι (jA x)) = ι (jA (u * x)) →
      (A.map ϑ).map (actO g) *
        (((ρ (inc g) : Matrix (Fin r) (Fin r) ℤ_[ℓ])ᵀ.map (algebraMap ℤ_[ℓ] AA)).map ϑ)
          = ((u ^ M0 • W.Gm g).map jA).map ϑ * A.map ϑ := by
    intro g u hgu
    refine wActU ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A g (actA g : AA →+* AA)
      (actO g : OC →+* OC) u hι hal hA (hgA g) (hϑ g) ?_ hnz
    have : actA g (jA x) = jA (u * x) := hι (by rw [hgA, hgu])
    show actO g (ϑ (jA x)) = _
    rw [← hϑ, this, map_mul, map_mul]
  refine ⟨A, Y', hA, h1, h2, ?_, ?_, ?_, h3, h4⟩
  · intro h hh
    have e := hU h 1 (by rw [one_mul]; exact hH h hh x)
    rw [one_pow, one_smul, wFix ℓ As AA WC jA ι φ Gg H act GK inc r ρ πs ξ M0 h0 W (hι.comp hj) h hh] at e
    rw [e, Matrix.map_one _ (map_zero _) (map_one _), Matrix.map_one _ (map_zero _) (map_one _), Matrix.one_mul]
  · intro g
    obtain ⟨u, hgu⟩ := hu g
    exact ⟨_, hU g u hgu⟩
  · exact wEnd ℓ As AA WC OC jA ι φ Gg H act GK inc r ρ πs ξ x M0 h0 W ϑ A hι hal hA

end Formalism.RepresentationBoundsCohomology.TorsionBoundCyclotomic
