import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.AutomorphicRankinSelberg.StripInt

open UpperHalfPlane hiding I
open UpperTheory.V.Af UpperTheory.V.Sd

/- English proof (translation)
Simplify using `only [petersson]`. Rewrite using `[zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul, Complex.ofReal_re, Complex.sq_norm]`.
-/
private lemma pet_re (k : ℕ) (f : ℍ → ℂ) (z : ℍ) :
    (petersson (k : ℤ) f f z).re = Complex.normSq (f z) * z.im ^ k := by
  simp only [petersson]
  rw [zpow_natCast, Complex.conj_mul', ← Complex.ofReal_pow, ← Complex.ofReal_pow, ← Complex.ofReal_mul,
    Complex.ofReal_re, Complex.sq_norm]

/- English proof (translation)
Introduce `hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ`. Assume the negation of the conclusion as `hne`. Establish `hne' : χ * ψ⁻¹ ≠ 1` using `fun e => hne (mul_inv_eq_one.mp e)`. Take `⟨G, hG⟩` from `hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)`. Establish `hNF` using `hNP k L g.f h.f`.

Take `⟨hP1, hP2, -⟩` from `hCP L _ _ G hG`. Take `⟨C, hC⟩` from `hTB L G (hP1 hNF) (hP2 hne')`. Establish `hchar0` using `hPC k L χ χ g.f g.f g.char g.char`. Simplify using `only [mul_inv_cancel] at hchar0`. Take `⟨G0, hG0⟩` from `hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0`.

Establish `hNF0` using `hNP k L g.f g.f`. Take `⟨hQ1, -, hQ3⟩` from `hCP L _ _ G0 hG0`. Establish `hfz : ∃ z, g.f z ≠ 0`. Assume the negation of the conclusion as `hall`. Use `push_neg at hall`.

Establish `h0 : (⇑g.f : ℍ → ℂ) = 0` using `funext hall`. Use `g.one` as an intermediate fact. Rewrite `this` using `[h0]`. Simplify using `[UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this`. Take `⟨z0, hz0⟩` from `hfz`.

Establish `hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re`. Use `⟨z0, ?_⟩` and prove the remaining obligations. Rewrite using `[pet_re]`. Conclude with `mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)`. Establish `hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re`.

Introduce `z`. Rewrite using `[pet_re]`. Conclude with `mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)`. Take `⟨hR1, hR2⟩` from `hQ3 rfl hnn hpos`. Take `⟨s, hs, hM⟩` from `hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)`.

Establish `hs1 : (1 : ℝ) ≤ s` using `hs.1.le`. Establish `e1` using `hTE L _ _ G hG hNF (hP1 hNF) s hs`. Establish `e0` using `hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs`. Take `⟨-, hL1, -⟩` from `hLB L (χ * ψ⁻¹) s hs1`. Take `⟨-, -, hL0⟩` from `hLB L 1 s hs1`.

Establish `hCs` using `hC s hs`. Establish `hcmp` using `hCmp k L hk χ ψ g h hap hχ s hs`. Establish `h2 : ‖(2 : ℂ)‖ = 2` using `by simp`. Rewrite `hCs` using `[e1, norm_mul, norm_mul, h2]`. Establish `hre` using `Complex.re_le_norm (Rs.TT L G0 s)`.

Establish `hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)`. Rewrite using `[e0, norm_mul, norm_mul, h2]`. Establish `hA` using `norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)`. Establish `hB` using `norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)`. Establish `hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C` using `by nlinarith`.

Establish `hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) ≤ 2 * (2 * (7 * (2 * C)))`. Apply `mul_le_mul hL0 _ (by positivity) (by norm_num)` to reduce the goal to its premises. Combine the linear equalities and inequalities to obtain the conclusion. Combine the linear equalities and inequalities to obtain the conclusion.
-/
theorem UpperTheory.V.Af.Rs.core :
    UpperTheory.V.Af.Rs.TBdd → UpperTheory.V.Af.Rs.TTop → UpperTheory.V.Af.Rs.ClsEx → UpperTheory.V.Af.Rs.ClsProp → UpperTheory.V.Af.Rs.TEq → UpperTheory.V.Af.Rs.LBd → UpperTheory.V.Af.Rs.NicePet → UpperTheory.V.Af.Rs.PetChar → UpperTheory.V.Af.Rs.Cmp → UpperTheory.V.Af.Rs.Core := by
  intro hTB hTT hCE hCP hTE hLB hNP hPC hCmp k L _ hk χ ψ g h hap hχ
  by_contra hne
  have hne' : χ * ψ⁻¹ ≠ 1 := fun e => hne (mul_inv_eq_one.mp e)
  obtain ⟨G, hG⟩ := hCE L (χ * ψ⁻¹) (petersson (k : ℤ) h.f g.f) (hPC k L χ ψ g.f h.f g.char h.char)
  have hNF := hNP k L g.f h.f
  obtain ⟨hP1, hP2, -⟩ := hCP L _ _ G hG
  obtain ⟨C, hC⟩ := hTB L G (hP1 hNF) (hP2 hne')
  have hchar0 := hPC k L χ χ g.f g.f g.char g.char
  simp only [mul_inv_cancel] at hchar0
  obtain ⟨G0, hG0⟩ := hCE L 1 (petersson (k : ℤ) g.f g.f) hchar0
  have hNF0 := hNP k L g.f g.f
  obtain ⟨hQ1, -, hQ3⟩ := hCP L _ _ G0 hG0
  have hfz : ∃ z, g.f z ≠ 0 := by
    by_contra hall
    push_neg at hall
    have h0 : (⇑g.f : ℍ → ℂ) = 0 := funext hall
    have := g.one
    rw [h0] at this
    simp [UpperTheory.V.Af.coef, UpperHalfPlane.qExpansion_zero] at this
  obtain ⟨z0, hz0⟩ := hfz
  have hpos : ∃ z, 0 < (petersson (k : ℤ) g.f g.f z).re := by
    refine ⟨z0, ?_⟩
    rw [pet_re]
    exact mul_pos (Complex.normSq_pos.mpr hz0) (pow_pos z0.im_pos k)
  have hnn : ∀ z, 0 ≤ (petersson (k : ℤ) g.f g.f z).re := by
    intro z
    rw [pet_re]
    exact mul_nonneg (Complex.normSq_nonneg _) (pow_nonneg z.im_pos.le k)
  obtain ⟨hR1, hR2⟩ := hQ3 rfl hnn hpos
  obtain ⟨s, hs, hM⟩ := hTT L G0 (hQ1 hNF0) hR1 hR2 (56 * C + 1)
  have hs1 : (1 : ℝ) ≤ s := hs.1.le
  have e1 := hTE L _ _ G hG hNF (hP1 hNF) s hs
  have e0 := hTE L _ _ G0 hG0 hNF0 (hQ1 hNF0) s hs
  obtain ⟨-, hL1, -⟩ := hLB L (χ * ψ⁻¹) s hs1
  obtain ⟨-, -, hL0⟩ := hLB L 1 s hs1
  have hCs := hC s hs
  have hcmp := hCmp k L hk χ ψ g h hap hχ s hs
  have h2 : ‖(2 : ℂ)‖ = 2 := by simp
  rw [e1, norm_mul, norm_mul, h2] at hCs
  have hre := Complex.re_le_norm (Rs.TT L G0 s)
  have hnorm : ‖Rs.TT L G0 s‖ = ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ *
      (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖) := by
    rw [e0, norm_mul, norm_mul, h2]
  have hA := norm_nonneg (Rs.stripI (petersson (k : ℤ) h.f g.f) s)
  have hB := norm_nonneg (Rs.stripI (petersson (k : ℤ) g.f g.f) s)
  have hX : ‖Rs.stripI (petersson (k : ℤ) h.f g.f) s‖ ≤ 2 * C := by nlinarith
  have hY : ‖Rs.Lps (1 : DirichletCharacter ℂ L) s‖ * (2 * ‖Rs.stripI (petersson (k : ℤ) g.f g.f) s‖)
      ≤ 2 * (2 * (7 * (2 * C))) := by
    apply mul_le_mul hL0 _ (by positivity) (by norm_num)
    linarith
  linarith
