import Mathlib
import Development.WeilBound.RepresentationTheoryGL.ArchimedeanBaseChange.ArchimedeanBaseChangeProof.IsotropicMahlerBounds.LogAbsoluteWedges.LogAbsBasic
open Matrix PositivityTheory.Rg.BcB PositivityTheory.Rg.BcB.D1

open NumberField IsDedekindDomain
open GlobalTheory.CuspRep GlobalTheory.UnitaryBC PositivityTheory.Rg.Tf.Loc

namespace GlobalTheory.CompanionTheory.OnlyStab

section Core

variable {K : Type} [Field K] {n : ℕ}

/- English proof (translation)
Establish `h : (k : ℝ) ≤ n` using `by exact_mod_cast hk`. Establish `h0 : (0 : ℝ) ≤ k` using `Nat.cast_nonneg k`. Unfold `prof`. Conclude with `mul_nonneg (mul_nonneg hτ h0) (by linarith)`.
-/
theorem prof_nonneg {τ : ℝ} (hτ : 0 ≤ τ) {k : ℕ} (hk : k ≤ n) : 0 ≤ prof n τ k := by
  have h : (k : ℝ) ≤ n := by exact_mod_cast hk
  have h0 : (0 : ℝ) ≤ k := Nat.cast_nonneg k
  unfold prof
  exact mul_nonneg (mul_nonneg hτ h0) (by linarith)

/- English proof (translation)
Simplify using `using Submodule.finrank_le W`.
-/
theorem finrank_le_n (W : Submodule K (Fin n → K)) : Module.finrank K W ≤ n := by
  simpa using Submodule.finrank_le W

/- English proof (translation)
Establish `h : (b : ℝ) = 2 * k - a`. Establish `: ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ)` using `by rw [hab]`. Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Unfold `prof`.

Rewrite using `[h]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem prof_second_diff (τ : ℝ) (a b k : ℕ) (hab : a + b = 2 * k) :
    prof n τ a + prof n τ b = 2 * prof n τ k - 2 * τ * ((k : ℝ) - a) ^ 2 := by
  have h : (b : ℝ) = 2 * k - a := by
    have : ((a + b : ℕ) : ℝ) = ((2 * k : ℕ) : ℝ) := by rw [hab]
    push_cast at this
    linarith
  unfold prof
  rw [h]
  ring

/- English proof (translation)
Assume the negation of the conclusion as `hW₀`. Use `push Not at hW₀`. Use `set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ`. Establish `hψb : BddAbove (Set.range ψ)`. Take `⟨B, hB⟩` from `hbdd`.

Use `⟨B, ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨W, rfl⟩`. Establish `h1 : deg' W ≤ B` using `hB ⟨W, rfl⟩`. Establish `h2` using `prof_nonneg (n := n) hτ.le (finrank_le_n W)`. Simplify using `only [hψ]`.

Combine the linear equalities and inequalities to obtain the conclusion. Use `set s : ℝ := ⨆ W, ψ W with hs`. Establish `hle : ∀ W, ψ W ≤ s` using `fun W => le_ciSup hψb W`. Establish `hs0 : 0 < s` using `lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)`. Establish `hε : 0 < min s (τ - D / 2)` using `lt_min hs0 (by linarith)`.

Take `⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W` from `exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])`. Establish `hε1 : min s (τ - D / 2) ≤ s` using `min_le_left _ _`. Establish `hε2 : min s (τ - D / 2) ≤ τ - D / 2` using `min_le_right _ _`. Distinguish the cases in `hg : g W = W`. Establish `h` using `hst W hg`.

Simplify using `only [hψ] at hW`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hsum` using `Submodule.finrank_sup_add_finrank_inf_eq W (g W)`. Rewrite `hsum` using `[hrank W]`. Establish `hne : W ⊓ g W ≠ W` using `fun h => hg (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm`.

Establish `hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W` using `Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)`. Establish `hid` using `prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)`. Establish `hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))`. Establish `: ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W`. Conclude with `hlt` after adjusting the coercions.

Move the coercions through the operations in `at this`. Combine the linear equalities and inequalities to obtain the conclusion. Establish `hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2` using `mul_le_mul_of_nonneg_left (by nlinarith) hτ.le`. Establish `h1` using `hle (W ⊓ g W)`. Establish `h2` using `hle (W ⊔ g W)`.

Establish `h3` using `hsub W (g W)`. Establish `h4` using `hmove W`. Simplify using `only [hψ] at h1 h2 hW`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem core (deg' : Submodule K (Fin n → K) → ℝ) (g : Submodule K (Fin n → K) → Submodule K (Fin n → K))
    (τ D : ℝ) (hτ : 0 < τ) (hD : D < 2 * τ) (hbdd : BddAbove (Set.range deg'))
    (hsub : ∀ W W', deg' W + deg' W' ≤ deg' (W ⊓ W') + deg' (W ⊔ W'))
    (hmove : ∀ W, deg' W - D ≤ deg' (g W))
    (hrank : ∀ W, Module.finrank K (g W) = Module.finrank K W)
    (hst : ∀ W, g W = W → deg' W ≤ prof n τ (Module.finrank K W)) (W₀ : Submodule K (Fin n → K)) :
    deg' W₀ ≤ prof n τ (Module.finrank K W₀) := by
  by_contra hW₀
  push Not at hW₀
  set ψ : Submodule K (Fin n → K) → ℝ := fun W => deg' W - prof n τ (Module.finrank K W) with hψ
  have hψb : BddAbove (Set.range ψ) := by
    obtain ⟨B, hB⟩ := hbdd
    refine ⟨B, ?_⟩
    rintro _ ⟨W, rfl⟩
    have h1 : deg' W ≤ B := hB ⟨W, rfl⟩
    have h2 := prof_nonneg (n := n) hτ.le (finrank_le_n W)
    simp only [hψ]
    linarith
  set s : ℝ := ⨆ W, ψ W with hs
  have hle : ∀ W, ψ W ≤ s := fun W => le_ciSup hψb W
  have hs0 : 0 < s := lt_of_lt_of_le (by simp only [hψ]; linarith) (hle W₀)
  have hε : 0 < min s (τ - D / 2) := lt_min hs0 (by linarith)
  obtain ⟨W, hW⟩ : ∃ W, s - min s (τ - D / 2) < ψ W :=
    exists_lt_of_lt_ciSup (by rw [hs]; linarith [hε])
  have hε1 : min s (τ - D / 2) ≤ s := min_le_left _ _
  have hε2 : min s (τ - D / 2) ≤ τ - D / 2 := min_le_right _ _
  by_cases hg : g W = W
  · have h := hst W hg
    simp only [hψ] at hW
    linarith
  · have hsum := Submodule.finrank_sup_add_finrank_inf_eq W (g W)
    rw [hrank W] at hsum
    have hne : W ⊓ g W ≠ W := fun h => hg
      (Submodule.eq_of_le_of_finrank_le (inf_eq_left.1 h) (by rw [hrank W])).symm
    have hlt : Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) < Module.finrank K W :=
      Submodule.finrank_lt_finrank_of_lt (lt_of_le_of_ne inf_le_left hne)
    have hid := prof_second_diff (n := n) τ (Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)))
      (Module.finrank K (W ⊔ g W : Submodule K (Fin n → K))) (Module.finrank K W) (by omega)
    have hj : (1 : ℝ) ≤ (Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) := by
      have : ((Module.finrank K (W ⊓ g W : Submodule K (Fin n → K)) + 1 : ℕ) : ℝ) ≤ Module.finrank K W := by
        exact_mod_cast hlt
      push_cast at this
      linarith
    have hj2 : τ * 1 ≤ τ * ((Module.finrank K W : ℝ) - Module.finrank K (W ⊓ g W : Submodule K (Fin n → K))) ^ 2 :=
      mul_le_mul_of_nonneg_left (by nlinarith) hτ.le
    have h1 := hle (W ⊓ g W)
    have h2 := hle (W ⊔ g W)
    have h3 := hsub W (g W)
    have h4 := hmove W
    simp only [hψ] at h1 h2 hW
    linarith

end Core

section Global

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {n : ℕ}

/- English proof (translation)
Establish `hinj : Function.Injective (Matrix.toLin' g.val)`. Introduce `a b hab`. Establish `h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b)`. Simplify `congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab` using `[Matrix.toLin'_apply]`. Simplify `h` using `[Matrix.mulVec_mulVec, ← Units.val_mul]`.

Conclude with `LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm`.
-/
theorem finrank_img (g : GL (Fin n) E) (W : Submodule E (Fin n → E)) :
    Module.finrank E (img g W) = Module.finrank E W := by
  have hinj : Function.Injective (Matrix.toLin' g.val) := by
    intro a b hab
    have h : (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ a) = (g⁻¹ : GL (Fin n) E).val *ᵥ (g.val *ᵥ b) := by
      simpa [Matrix.toLin'_apply] using congrArg (fun y => (g⁻¹ : GL (Fin n) E).val *ᵥ y) hab
    simpa [Matrix.mulVec_mulVec, ← Units.val_mul] using h
  exact LinearEquiv.finrank_eq (Submodule.equivMapOfInjective _ hinj W).symm

/- English proof (translation)
The claim follows from `(eq_conjSrc fun x => by rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)] exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm`.
-/
theorem conjSrc_invol (v : HeightOneSpectrum (𝓞 E)) :
    conjSrc (IsCMField.complexConj E).toRingEquiv (conjSrc (IsCMField.complexConj E).toRingEquiv v) = v :=
  (eq_conjSrc fun x => by
    rw [← conjPl_conjSrc (IsCMField.complexConj E).toRingEquiv v ((IsCMField.complexConj E).toRingEquiv x)]
    exact congrArg _ (IsCMField.complexConj_apply_apply E x)).symm

/- English proof (translation)
Establish `key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E), Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x`. Introduce and unpack `_ v rfl f hf h`. Conclude with `congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _`. Use `FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _) ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_` and prove the remaining obligations. Rewrite using `[Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]`.

Conclude with `congrArg _ (IsCMField.complexConj_apply_apply E k)`.
-/
theorem conjFin_invol (x : Af E) :
    conjFin (IsCMField.complexConj E).toRingEquiv (conjFin (IsCMField.complexConj E).toRingEquiv x) = x := by
  have key : ∀ (v w : HeightOneSpectrum (𝓞 E)) (_ : w = v) (f : w.adicCompletion E → v.adicCompletion E),
      Continuous f → (∀ k : E, f (algebraMap E _ k) = algebraMap E _ k) → f (pLoc E w x) = pLoc E v x := by
    rintro _ v rfl f hf h
    exact congrFun ((HeightOneSpectrum.denseRange_algebraMap (K := E) v).equalizer hf continuous_id (funext h)) _
  refine FiniteAdeleRing.ext _ fun v => key v _ (conjSrc_invol v) (conjLoc _ v ∘ conjLoc _ _)
    ((conjLoc_spec _ _).1.comp (conjLoc_spec _ _).1) fun k => ?_
  rw [Function.comp_apply, (conjLoc_spec _ _).2.1, (conjLoc_spec _ _).2.1]
  exact congrArg _ (IsCMField.complexConj_apply_apply E k)

/- English proof (translation)
The claim follows from `(infEq E).symm_apply_apply _`.
-/
theorem pInf_conj (x : Ad E) : pInf E (conjAd E x) = starRingEnd (Cinf E) (pInf E x) :=
  (infEq E).symm_apply_apply _

/- English proof (translation)
The claim follows from `ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)`.
-/
theorem conjAd_invol (x : Ad E) : conjAd E (conjAd E x) = x :=
  ad_ext (by rw [pInf_conj, pInf_conj, starRingEnd_self_apply]) (conjFin_invol _)

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `conjAd E (conjAd E (x.val i j)) = x.val i j`. Conclude with `conjAd_invol _`.
-/
theorem thetaA_invol (x : GA E n) : thetaA E n (thetaA E n x) = x := by
  refine Units.ext ?_
  ext i j
  change conjAd E (conjAd E (x.val i j)) = x.val i j
  exact conjAd_invol _

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Establish `h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹` using `(map_inv _ _).symm`. Rewrite using `[thetaR_val, h]`. Express the relevant statement in the definitionally equal form `algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) = conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))`.

Rewrite using `[conjAd_algebraMap]`. Both sides reduce to the same expression.
-/
theorem ratGL_thetaE (d : GL (Fin n) E) : ratGL E n (thetaE E n d) = thetaA E n (ratGL E n d) := by
  refine Units.ext ?_
  ext i j
  have h : ((ratGL E n d)⁻¹ : GA E n) = ratGL E n d⁻¹ := (map_inv _ _).symm
  rw [thetaR_val, h]
  change algebraMap E (Ad E) (conjE E ((d⁻¹ : GL (Fin n) E).val j i)) =
    conjAd E (algebraMap E (Ad E) ((d⁻¹ : GL (Fin n) E).val j i))
  rw [conjAd_algebraMap]
  rfl

/- English proof (translation)
Simplify using `only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]`. Use `group`.
-/
theorem conj_nrm (x : GA E n) (d : GL (Fin n) E) :
    x⁻¹ * ratGL E n (nrm d) * x =
      twConj (thetaA E n) x (ratGL E n d) * thetaA E n (twConj (thetaA E n) x (ratGL E n d)) := by
  simp only [twConj, nrm, map_mul, map_inv, thetaA_invol, ratGL_thetaE]
  group

end Global

/- English proof (translation)
Establish `ha : 0 ≤ |C₁|` using `abs_nonneg _`. Establish `hb : 0 ≤ |C₂|` using `abs_nonneg _`. Establish `hcc : 0 ≤ |c|` using `abs_nonneg _`. Establish `hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L)` using `by positivity`. Establish `hprod2 : 0 ≤ |C₂| * (1 + L)` using `by positivity`.

Establish `hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ`. Combine the equalities or inequalities in the displayed calculation. Establish `hτ0 : 0 < τ` using `by linarith`. Use `⟨hτ0, ?_, ?_⟩` and prove the remaining obligations. Establish `e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l)` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)`.

Establish `e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|))` using `mul_le_mul_of_nonneg_left (by linarith) ha`. Establish `e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L)`. Establish `: 0 ≤ |C₁| * (1 + |c| * L)` using `by positivity`. Use the polynomial consequences of the given equalities and inequalities. Combine the linear equalities and inequalities to obtain the conclusion.

Establish `h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L)` using `mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)`. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem arith (C₁ C₂ c L l τ : ℝ) (hL0 : 0 ≤ L) (hl0 : 0 ≤ l) (hl : l ≤ 2 * L + |c|)
    (hτ : (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) ≤ τ) :
    0 < τ ∧ C₁ * (1 + l) < 2 * τ ∧ C₂ * (1 + L) ≤ τ := by
  have ha : 0 ≤ |C₁| := abs_nonneg _
  have hb : 0 ≤ |C₂| := abs_nonneg _
  have hcc : 0 ≤ |c| := abs_nonneg _
  have hprod : 0 ≤ |C₁| * (2 + |c|) * (1 + L) := by positivity
  have hprod2 : 0 ≤ |C₂| * (1 + L) := by positivity
  have hτ' : 1 + L + |C₁| * (2 + |c|) * (1 + L) + |C₂| * (1 + L) ≤ τ := by
    calc _ = (1 + |C₁| * (2 + |c|) + |C₂|) * (1 + L) := by ring
      _ ≤ τ := hτ
  have hτ0 : 0 < τ := by linarith
  refine ⟨hτ0, ?_, ?_⟩
  · have e1 : C₁ * (1 + l) ≤ |C₁| * (1 + l) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    have e2 : |C₁| * (1 + l) ≤ |C₁| * (1 + (2 * L + |c|)) := mul_le_mul_of_nonneg_left (by linarith) ha
    have e3 : |C₁| * (1 + (2 * L + |c|)) ≤ |C₁| * (2 + |c|) * (1 + L) := by
      have : 0 ≤ |C₁| * (1 + |c| * L) := by positivity
      nlinarith
    linarith
  · have h3 : C₂ * (1 + L) ≤ |C₂| * (1 + L) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith)
    linarith

/- English proof (translation)
Introduce `hSub hMove hBdd hPair hSize E _ _ _ n`. Take `⟨C₁, h₁⟩` from `hMove E n`. Take `⟨C₂, h₂⟩` from `hPair E n`. Take `⟨-, hnn, hθ, c, hc⟩` from `hSize E n`. Use `⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩` and prove the remaining obligations.

Establish `hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤ 2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c|`. Rewrite using `[conj_nrm]`. Establish `h` using `hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))`. Rewrite `h` using `[hθ]`. Use `le_abs_self c` as an intermediate fact.

Combine the linear equalities and inequalities to obtain the conclusion. Take `⟨hτ0, hD, hC₂⟩` from `arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ`. Prove the components needed by the constructor for the conclusion. Conclude with `fun h W _ => h.1 W`. Introduce `hst`.

Use `⟨fun W => ?_, ?_⟩` and prove the remaining obligations. Conclude with `core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W) (fun W => finrank_img _ W) hst W`. Establish `h` using `(h₂ x d).2`. Use `neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))` as an intermediate fact. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem onlyStable_of : DegSubmod → DegMove → DegBdd → DegPairing → SizeBasic → OnlyStable := by
  intro hSub hMove hBdd hPair hSize E _ _ _ n
  obtain ⟨C₁, h₁⟩ := hMove E n
  obtain ⟨C₂, h₂⟩ := hPair E n
  obtain ⟨-, hnn, hθ, c, hc⟩ := hSize E n
  refine ⟨1 + |C₁| * (2 + |c|) + |C₂|, fun τ x d hτ => ?_⟩
  have hls : logSize (x⁻¹ * ratGL E n (nrm d) * x) ≤
      2 * logSize (twConj (thetaA E n) x (ratGL E n d)) + |c| := by
    rw [conj_nrm]
    have h := hc (twConj (thetaA E n) x (ratGL E n d)) (thetaA E n (twConj (thetaA E n) x (ratGL E n d)))
    rw [hθ] at h
    have := le_abs_self c
    linarith
  obtain ⟨hτ0, hD, hC₂⟩ := arith C₁ C₂ c _ _ τ (hnn _) (hnn _) hls hτ
  constructor
  · exact fun h W _ => h.1 W
  · intro hst
    refine ⟨fun W => ?_, ?_⟩
    · exact core (deg x) (img (nrm d)) τ _ hτ0 hD ((hBdd E n).1 x) (hSub E n x) (fun W => h₁ x (nrm d) W)
        (fun W => finrank_img _ W) hst W
    · have h := (h₂ x d).2
      have := neg_abs_le (deg x (⊤ : Submodule E (Fin n → E)))
      linarith

end GlobalTheory.CompanionTheory.OnlyStab
