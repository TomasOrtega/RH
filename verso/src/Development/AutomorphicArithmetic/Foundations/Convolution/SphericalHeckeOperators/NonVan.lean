import Development.AutomorphicArithmetic.Foundations.Convolution.SphericalHeckeOperators.SymSum

open MeasureTheory GroundTheory.Automorphic GroundTheory.Automorphic.Spherical GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa UpperTheory.ConvolutionTheory.H

namespace UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

variable {n : ℕ}

private def phi : (Fin n → ℕ) →+ (Fin n → ℤ) where
  toFun b i := ∑ k, if i ≤ k then (b k : ℤ) else 0
  map_zero' := by
    funext i
    simp
  map_add' b c := by
    funext i
    simp only [Pi.add_apply]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun k _ => ?_
    split_ifs <;> simp

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma phi_apply (b : Fin n → ℕ) (i : Fin n) :
    phi b i = ∑ k, if i ≤ k then (b k : ℤ) else 0 := rfl

/- English proof (translation)
Rewrite using `[phi_apply]`. Use `Finset.sum_nonneg fun k _ => ?_` and prove the remaining obligations. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma phi_nonneg (b : Fin n → ℕ) (i : Fin n) : 0 ≤ phi b i := by
  rw [phi_apply]
  refine Finset.sum_nonneg fun k _ => ?_
  split_ifs <;> simp

/- English proof (translation)
Rewrite using `[phi_apply, phi_apply]`. Use `Finset.sum_le_sum fun k _ => ?_` and prove the remaining obligations. Distinguish the cases in `h1 : j ≤ k`. Rewrite using `[if_pos h1, if_pos (hij.trans h1)]`. Apply the tactic sequence `rw [if_neg h1] split_ifs <;> simp`.
-/
private lemma phi_anti (b : Fin n → ℕ) {i j : Fin n} (hij : i ≤ j) : phi b j ≤ phi b i := by
  rw [phi_apply, phi_apply]
  refine Finset.sum_le_sum fun k _ => ?_
  by_cases h1 : j ≤ k
  · rw [if_pos h1, if_pos (hij.trans h1)]
  · rw [if_neg h1]
    split_ifs <;> simp

private def chi (w : Fin n → ℂˣ) : Multiplicative (Fin n → ℕ) →* ℂ where
  toFun b := monomialChar (phi (Multiplicative.toAdd b)) w
  map_one' := by simp
  map_mul' b c := by simp [map_add, monomialChar_add]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private lemma chi_apply (w : Fin n → ℂˣ) (b : Fin n → ℕ) :
    chi w (Multiplicative.ofAdd b) = monomialChar (phi b) w := rfl

/- English proof (translation)
Establish `hphi : ∀ i, phi (Pi.single k 1 : Fin n → ℕ) i = if i ≤ k then 1 else 0`. Introduce `i`. Rewrite using `[phi_apply, Finset.sum_eq_single k]`. Simplify using the standard rewrite rules. Introduce `l _ hl`.

Simplify using `[Pi.single_eq_of_ne hl]`. Simplify using the standard rewrite rules. Rewrite using `[chi_apply, monomialChar_apply]`. Establish `hI : Finset.Iic k = Finset.univ.filter (· ≤ k)`. Use `ext`.

Simplify using the standard rewrite rules. Rewrite using `[hI, Finset.prod_filter]`. Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Rewrite using `[hphi]`. Apply the tactic sequence `split_ifs <;> simp`.
-/
private lemma chi_single (w : Fin n → ℂˣ) (k : Fin n) :
    chi w (Multiplicative.ofAdd (Pi.single k 1)) = ∏ i ∈ Finset.Iic k, (w i : ℂ) := by
  have hphi : ∀ i, phi (Pi.single k 1 : Fin n → ℕ) i = if i ≤ k then 1 else 0 := by
    intro i
    rw [phi_apply, Finset.sum_eq_single k]
    · simp
    · intro l _ hl
      simp [Pi.single_eq_of_ne hl]
    · simp
  rw [chi_apply, monomialChar_apply]
  have hI : Finset.Iic k = Finset.univ.filter (· ≤ k) := by
    ext
    simp
  rw [hI, Finset.prod_filter]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [hphi]
  split_ifs <;> simp

/- English proof (translation)
Establish `hp : ∀ k, ∏ i ∈ Finset.Iic k, (w i : ℂ) = ∏ i ∈ Finset.Iic k, (w' i : ℂ)` using `fun k => by`. Rewrite using `[← chi_single, ← chi_single, h]`. Use function extensionality and compare the values at `k`. Proceed by induction on `k using WellFoundedLT.induction with`. Consider the case `ind k ih`.

Establish `hI : Finset.Iic k = insert k (Finset.Iio k)`. Use `ext`. Simplify using `[le_iff_eq_or_lt]`. Establish `h1` using `hp k`. Rewrite `h1` using `[hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)]`.

Establish `e : ∏ i ∈ Finset.Iio k, (w i : ℂ) = ∏ i ∈ Finset.Iio k, (w' i : ℂ)` using `Finset.prod_congr rfl fun i hi => by rw [ih i (Finset.mem_Iio.1 hi)]`. Rewrite `h1` using `[e]`. Establish `ne : ∏ i ∈ Finset.Iio k, (w' i : ℂ) ≠ 0` using `Finset.prod_ne_zero_iff.2 fun i _ => (w' i).ne_zero`. Conclude with `Units.ext (mul_right_cancel₀ ne h1)`.
-/
private lemma chi_injective {w w' : Fin n → ℂˣ} (h : chi w = chi w') : w = w' := by
  have hp : ∀ k, ∏ i ∈ Finset.Iic k, (w i : ℂ) = ∏ i ∈ Finset.Iic k, (w' i : ℂ) := fun k => by
    rw [← chi_single, ← chi_single, h]
  funext k
  induction k using WellFoundedLT.induction with
  | ind k ih =>
    have hI : Finset.Iic k = insert k (Finset.Iio k) := by
      ext
      simp [le_iff_eq_or_lt]
    have h1 := hp k
    rw [hI, Finset.prod_insert (by simp), Finset.prod_insert (by simp)] at h1
    have e : ∏ i ∈ Finset.Iio k, (w i : ℂ) = ∏ i ∈ Finset.Iio k, (w' i : ℂ) :=
      Finset.prod_congr rfl fun i hi => by rw [ih i (Finset.mem_Iio.1 hi)]
    rw [e] at h1
    have ne : ∏ i ∈ Finset.Iio k, (w' i : ℂ) ≠ 0 :=
      Finset.prod_ne_zero_iff.2 fun i _ => (w' i).ne_zero
    exact Units.ext (mul_right_cancel₀ ne h1)

/- English proof (translation)
Rewrite using `[evalAt_single, one_mul, monomialChar_apply, Finset.prod_eq_single i]`. Simplify using the standard rewrite rules. Introduce `j _ hj`. Simplify using `[Pi.single_eq_of_ne hj]`. Simplify using the standard rewrite rules.
-/
private lemma evalAt_varL (w : Fin n → ℂˣ) (i : Fin n) : evalAt w (varL i) = (w i : ℂ) := by
  rw [evalAt_single, one_mul, monomialChar_apply, Finset.prod_eq_single i]
  · simp
  · intro j _ hj
    simp [Pi.single_eq_of_ne hj]
  · simp

/- English proof (translation)
Rewrite using `[dPol, map_prod]`. Use `Finset.prod_congr rfl fun p _ => ?_` and prove the remaining obligations. Rewrite using `[map_sub, map_smul, evalAt_varL, evalAt_varL, smul_eq_mul]`.
-/
private lemma evalAt_dPol (w : Fin n → ℂˣ) (t : ℂ) :
    evalAt w (dPol n t) = ∏ p ∈ pairs n, ((w p.1 : ℂ) - t * (w p.2 : ℂ)) := by
  rw [dPol, map_prod]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [map_sub, map_smul, evalAt_varL, evalAt_varL, smul_eq_mul]

/- English proof (translation)
Rewrite using `[evalAt_dPol, Finset.prod_ne_zero_iff]`. Introduce `p hp h0`. Establish `hij : p.1 < p.2` using `(Finset.mem_filter.1 hp).2`. Establish `e : (w p.1 : ℂ) = t * (w p.2 : ℂ)` using `sub_eq_zero.1 h0`. Establish `h1` using `hw _ _ hij.le`.

Establish `hpos : 0 < ‖(w p.2 : ℂ)‖` using `norm_pos_iff.2 (w p.2).ne_zero`. Rewrite `h1` using `[e, norm_mul]`. Use the polynomial consequences of the given equalities and inequalities.
-/
private lemma evalAt_dPol_ne {t : ℂ} (ht : ‖t‖ < 1) (w : Fin n → ℂˣ)
    (hw : ∀ i j, i ≤ j → ‖(w j : ℂ)‖ ≤ ‖(w i : ℂ)‖) : evalAt w (dPol n t) ≠ 0 := by
  rw [evalAt_dPol, Finset.prod_ne_zero_iff]
  intro p hp h0
  have hij : p.1 < p.2 := (Finset.mem_filter.1 hp).2
  have e : (w p.1 : ℂ) = t * (w p.2 : ℂ) := sub_eq_zero.1 h0
  have h1 := hw _ _ hij.le
  have hpos : 0 < ‖(w p.2 : ℂ)‖ := norm_pos_iff.2 (w p.2).ne_zero
  rw [e, norm_mul] at h1
  nlinarith

/- English proof (translation)
Rewrite using `[symSum, map_sum]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations. Rewrite using `[evalAt_permAct, map_mul, evalAt_single, one_mul]`.
-/
private lemma evalAt_term (z : Fin n → ℂˣ) (a : Fin n → ℤ) (t : ℂ) :
    evalAt z (symSum (monomial a * dPol n t)) =
      ∑ σ : Equiv.Perm (Fin n), monomialChar a (z ∘ σ) * evalAt (z ∘ σ) (dPol n t) := by
  rw [symSum, map_sum]
  refine Finset.sum_congr rfl fun σ _ => ?_
  rw [evalAt_permAct, map_mul, evalAt_single, one_mul]

end UpperTheory.ConvolutionTheory.H.NonVanishingCharacter

open UpperTheory.ConvolutionTheory.H.NonVanishingCharacter in
/- English proof (translation)
Introduce `n t ht z m`. Assume the negation of the conclusion as `hcon`. Use `push_neg at hcon`. Set `s : Fin n → ℤ` to `fun i => (m : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ))`. Establish `hs0 : ∀ i, 0 ≤ s i` using `fun i => by`.

Establish `: ((i : ℕ) : ℤ) ≤ n` using `by exact_mod_cast i.2.le`. Conclude with `mul_nonneg (by positivity) (by linarith)`. Establish `hsgap : ∀ i j : Fin n, i < j → s j + m ≤ s i` using `fun i j hij => by`. Establish `h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ)` using `by exact_mod_cast hij`. Establish `hm : (0 : ℤ) ≤ m` using `by positivity`.

Simplify using `only [s]`. Use the polynomial consequences of the given equalities and inequalities. Set `W : Equiv.Perm (Fin n) → ℂ` to `fun σ => monomialChar s (z ∘ σ) * evalAt (z ∘ σ) (dPol n t)`. Set `Ψ : Equiv.Perm (Fin n) → (Multiplicative (Fin n → ℕ) →* ℂ)` to `fun σ => chi (z ∘ σ)`. Establish `hsum : ∀ b, ∑ σ, W σ * Ψ σ b = 0`.

Introduce `b`. Establish `h0` using `hcon (s + phi (Multiplicative.toAdd b)) (fun i j hij => by`. Use `hsgap i j hij` as an intermediate fact. Use `phi_anti (Multiplicative.toAdd b) hij.le` as an intermediate fact. Simplify using `only [Pi.add_apply]`.

Use the proof step `linarith)`. Use the proof step `(fun i => add_nonneg (hs0 i) (phi_nonneg _ i))`. Rewrite `h0` using `[evalAt_term]`. Rewrite using `[← h0]`. Use `Finset.sum_congr rfl fun σ _ => ?_` and prove the remaining obligations.

Rewrite using `[monomialChar_add]`. Simplify using `only [W, Ψ]`. Express the relevant statement in the definitionally equal form `_ * monomialChar (phi (Multiplicative.toAdd b)) (z ∘ σ) = _`. Expand and normalize the polynomial expressions, which then agree. Establish `hli` using `linearIndependent_monoidHom (Multiplicative (Fin n → ℕ)) ℂ`.

Rewrite `hli` using `[linearIndependent_iff']`. Set `g : (Multiplicative (Fin n → ℕ) →* ℂ) → ℂ` to `fun χ => ∑ σ with Ψ σ = χ, W σ`. Establish `hg : ∑ χ ∈ Finset.univ.image Ψ, g χ • (χ : Multiplicative (Fin n → ℕ) → ℂ) = 0`. Use function extensionality and compare the values at `b`. Simplify using `only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, Finset.sum_mul]`.

Rewrite using `[← hsum b]`. Rewrite using `[← Finset.sum_fiberwise_of_maps_to (g := Ψ) (t := Finset.univ.image Ψ) (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))]`. Conclude with `Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun σ hσ => by`. Rewrite using `[(Finset.mem_filter.1 hσ).2]`. Set `σ₀ : Equiv.Perm (Fin n)` to `Tuple.sort (fun i => -‖(z i : ℂ)‖)`.

Establish `hw : ∀ i j, i ≤ j → ‖((z ∘ σ₀) j : ℂ)‖ ≤ ‖((z ∘ σ₀) i : ℂ)‖` using `fun i j hij => neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖(z i : ℂ)‖) hij)`. Establish `hW : W σ₀ ≠ 0`. Use `mul_ne_zero ?_ (evalAt_dPol_ne ht _ hw)` and prove the remaining obligations. Rewrite using `[monomialChar_apply, Finset.prod_ne_zero_iff]`. Conclude with `fun i _ => Units.ne_zero _`.

Establish `hgz : g (Ψ σ₀) = 0` using `hli _ g hg (Ψ σ₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))`. Establish `hfib : g (Ψ σ₀) = ((Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card : ℂ) * W σ₀`. Simplify using `only [g]`. Rewrite using `[Finset.sum_congr rfl (g := fun _ => W σ₀), Finset.sum_const, nsmul_eq_mul]`. Introduce `σ hσ`.

Establish `he : z ∘ σ = z ∘ σ₀` using `chi_injective (Finset.mem_filter.1 hσ).2`. Simplify using `only [W, he]`. Establish `hc : (Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card ≠ 0` using `Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ σ₀, rfl⟩)`. Rewrite `hgz` using `[hfib]`. Conclude with `(mul_ne_zero (Nat.cast_ne_zero.2 hc) hW) hgz`.
-/
theorem UpperTheory.ConvolutionTheory.H.nonVan :
    ∀ (n : ℕ) (t : ℂ), ‖t‖ < 1 → ∀ (z : Fin n → ℂˣ) (m : ℕ),
      ∃ a : Fin n → ℤ, Gap m a ∧ (∀ i, 0 ≤ a i) ∧ evalAt z (symSum (monomial a * dPol n t)) ≠ 0 := by
  classical
  intro n t ht z m
  by_contra hcon
  push_neg at hcon
  let s : Fin n → ℤ := fun i => (m : ℤ) * ((n : ℤ) - ((i : ℕ) : ℤ))
  have hs0 : ∀ i, 0 ≤ s i := fun i => by
    have : ((i : ℕ) : ℤ) ≤ n := by exact_mod_cast i.2.le
    exact mul_nonneg (by positivity) (by linarith)
  have hsgap : ∀ i j : Fin n, i < j → s j + m ≤ s i := fun i j hij => by
    have h1 : ((i : ℕ) : ℤ) + 1 ≤ ((j : ℕ) : ℤ) := by exact_mod_cast hij
    have hm : (0 : ℤ) ≤ m := by positivity
    simp only [s]
    nlinarith
  let W : Equiv.Perm (Fin n) → ℂ := fun σ => monomialChar s (z ∘ σ) * evalAt (z ∘ σ) (dPol n t)
  let Ψ : Equiv.Perm (Fin n) → (Multiplicative (Fin n → ℕ) →* ℂ) := fun σ => chi (z ∘ σ)
  have hsum : ∀ b, ∑ σ, W σ * Ψ σ b = 0 := by
    intro b
    have h0 := hcon (s + phi (Multiplicative.toAdd b))
      (fun i j hij => by
        have := hsgap i j hij
        have := phi_anti (Multiplicative.toAdd b) hij.le
        simp only [Pi.add_apply]
        linarith)
      (fun i => add_nonneg (hs0 i) (phi_nonneg _ i))
    rw [evalAt_term] at h0
    rw [← h0]
    refine Finset.sum_congr rfl fun σ _ => ?_
    rw [monomialChar_add]
    simp only [W, Ψ]
    change _ * monomialChar (phi (Multiplicative.toAdd b)) (z ∘ σ) = _
    ring
  have hli := linearIndependent_monoidHom (Multiplicative (Fin n → ℕ)) ℂ
  rw [linearIndependent_iff'] at hli
  let g : (Multiplicative (Fin n → ℕ) →* ℂ) → ℂ := fun χ => ∑ σ with Ψ σ = χ, W σ
  have hg : ∑ χ ∈ Finset.univ.image Ψ, g χ • (χ : Multiplicative (Fin n → ℕ) → ℂ) = 0 := by
    funext b
    simp only [Finset.sum_apply, Pi.smul_apply, smul_eq_mul, Pi.zero_apply, g, Finset.sum_mul]
    rw [← hsum b]
    rw [← Finset.sum_fiberwise_of_maps_to (g := Ψ) (t := Finset.univ.image Ψ)
      (fun σ _ => Finset.mem_image_of_mem _ (Finset.mem_univ _))]
    exact Finset.sum_congr rfl fun χ _ => Finset.sum_congr rfl fun σ hσ => by
      rw [(Finset.mem_filter.1 hσ).2]
  let σ₀ : Equiv.Perm (Fin n) := Tuple.sort (fun i => -‖(z i : ℂ)‖)
  have hw : ∀ i j, i ≤ j → ‖((z ∘ σ₀) j : ℂ)‖ ≤ ‖((z ∘ σ₀) i : ℂ)‖ := fun i j hij =>
    neg_le_neg_iff.1 (Tuple.monotone_sort (fun i => -‖(z i : ℂ)‖) hij)
  have hW : W σ₀ ≠ 0 := by
    refine mul_ne_zero ?_ (evalAt_dPol_ne ht _ hw)
    rw [monomialChar_apply, Finset.prod_ne_zero_iff]
    exact fun i _ => Units.ne_zero _
  have hgz : g (Ψ σ₀) = 0 := hli _ g hg (Ψ σ₀) (Finset.mem_image_of_mem _ (Finset.mem_univ _))
  have hfib : g (Ψ σ₀) = ((Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card : ℂ) * W σ₀ := by
    simp only [g]
    rw [Finset.sum_congr rfl (g := fun _ => W σ₀), Finset.sum_const, nsmul_eq_mul]
    intro σ hσ
    have he : z ∘ σ = z ∘ σ₀ := chi_injective (Finset.mem_filter.1 hσ).2
    simp only [W, he]
  have hc : (Finset.univ.filter fun σ => Ψ σ = Ψ σ₀).card ≠ 0 :=
    Finset.card_ne_zero_of_mem (Finset.mem_filter.2 ⟨Finset.mem_univ σ₀, rfl⟩)
  rw [hfib] at hgz
  exact (mul_ne_zero (Nat.cast_ne_zero.2 hc) hW) hgz
