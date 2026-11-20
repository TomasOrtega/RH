import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.PsPair
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ResidualChains.RtFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.CoefRes
import Development.AutomorphicArithmetic.AutomorphicVarieties.WeakShimuraTheory.ProjectiveLineFlags.TowerGal

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal IsLocalRing Polynomial UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement UpperTheory.V.Ws GlobalTheory.GalOfCusp

/- English proof (translation)
Evaluate the decidable proposition.
-/
private theorem UpperTheory.V.Ws.P1.condD_roots : ∀ w ∈ roots, ∃ i j : Fin 4, w = wt i j := by
  decide

/- English proof (translation)
Establish `hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹`. Rewrite using `[← h, mul_comm (Φ.χ 0 g) (Φ.χ 3 g), mul_inv_cancel_right]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;> (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)`.
-/
private theorem UpperTheory.V.Ws.P1.condD_rt {O Γ : Type} [CommRing O] [Group Γ] (Φ : Fr O Γ) (g : Γ)
    (h : Φ.χ 0 g * Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g) (i j : Fin 4) : Φ.rt (wt i j) g * Φ.χ j g = Φ.χ i g := by
  have hd : Φ.χ 3 g = Φ.χ 1 g * Φ.χ 2 g * (Φ.χ 0 g)⁻¹ := by
    rw [← h, mul_comm (Φ.χ 0 g) (Φ.χ 3 g), mul_inv_cancel_right]
  fin_cases i <;> fin_cases j <;> simp [Fr.rt, wt, lamW, muW, hd] <;>
    (apply Additive.ofMul.injective; simp only [ofMul_mul, ofMul_inv]; abel)

/- English proof (translation)
Introduce `Ω _ _ _ l _ c D T hfit _ c' h K`. Take `⟨w, hw, hord⟩` from `hfit.1.ord`. Take `⟨i, j, rfl⟩` from `condD_roots w hw`. Use `⟨i, j, fun n hn hn4 heq => ?_⟩` and prove the remaining obligations. Take `⟨g, hgL, hne⟩` from `hord n hn hn4`.

Take `⟨hrange, -, -, -, hres, -⟩` from `P1.towerGal D T`. Rewrite `hgL` using `[← hrange]`. Take `⟨g', hg'⟩` from `hgL`. Use `haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h`. Establish `hΦ : (T.fr ∅).χ 0 g * (T.fr ∅).χ 3 g = (T.fr ∅).χ 1 g * (T.fr ∅).χ 2 g`.

Simplify using `only [Tower.fr, chi, lab]`. Apply the tactic sequence `cases T.pr <;> simp [Raw.ps, Raw.th, mul_comm]`. Establish `hrt` using `condD_rt (T.fr ∅) g hΦ i j`. Establish `hq : resQ T.F g = resQ T.L g'` using `by rw [← hg']; exact (hres g').1`. Establish `hA : (T.fr ∅).χ i g = chi D T.pr i (resQ T.L g')` using `by rw [← hq]; rfl`.

Establish `hB : (T.fr ∅).χ j g = chi D T.pr j (resQ T.L g')` using `by rw [← hq]; rfl`. Rewrite `hrt` using `[hA, hB]`. Establish `hAval : ((chi D T.pr i (resQ T.L g') : (c.O)ˣ) : c.O) = (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O) * (chi D T.pr j (resQ T.L g') : c.O)`. Rewrite using `[← hrt, Units.val_mul]`. Establish `hx : (K.r.chib i (K.V.pr g') / K.r.chib j (K.V.pr g')) ^ n = 1` using `DFunLike.congr_fun heq (K.V.pr g')`.

Establish `hx'` using `congrArg (fun u : (ResidueField c'.O)ˣ => (u : ResidueField c'.O)) hx`. Simplify using `only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one] at hx'`. Rewrite `hx'` using `[K.chib i g', K.chib j g', hAval]`. Establish `hκ : residue c'.O (K.κ g' : c'.O) ≠ 0` using `((K.κ g').isUnit.map (residue _)).ne_zero`. Establish `hBn : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0` using `(((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue _)).ne_zero`.

Simplify using `only [map_mul] at hx'`. Rewrite `hx'` using `[mul_div_mul_left _ _ hκ, mul_div_cancel_right₀ _ hBn]`. Apply `hne` to reduce the goal to its premises. Use `show (residue c.O (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O)) ^ n = 1`. Apply `(ResidueField.map (inc h)).injective` to reduce the goal to its premises.

Rewrite using `[map_pow, map_one, ResidueField.map_residue]`. Conclude with `hx'`.
-/
theorem UpperTheory.V.Ws.P1.condD :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c) (T : Tower D), T.Fit → T.Deep → ∀ (c' : Coef l) (h : c.O ≤ c'.O) (K : Link T c' h), ∃ i j, ∀ n : ℕ, 0 < n → n ≤ 4 → (K.r.chib i / K.r.chib j) ^ n ≠ 1 := by
  intro Ω _ _ _ l _ c D T hfit _ c' h K
  obtain ⟨w, hw, hord⟩ := hfit.1.ord
  obtain ⟨i, j, rfl⟩ := condD_roots w hw
  refine ⟨i, j, fun n hn hn4 heq => ?_⟩
  obtain ⟨g, hgL, hne⟩ := hord n hn hn4
  obtain ⟨hrange, -, -, -, hres, -⟩ := P1.towerGal D T
  rw [← hrange] at hgL
  obtain ⟨g', hg'⟩ := hgL
  haveI : IsLocalHom (inc h) := (P1.coefRes c).2.2.1 c' h
  have hΦ : (T.fr ∅).χ 0 g * (T.fr ∅).χ 3 g = (T.fr ∅).χ 1 g * (T.fr ∅).χ 2 g := by
    simp only [Tower.fr, chi, lab]
    cases T.pr <;> simp [Raw.ps, Raw.th, mul_comm]
  have hrt := condD_rt (T.fr ∅) g hΦ i j
  have hq : resQ T.F g = resQ T.L g' := by rw [← hg']; exact (hres g').1
  have hA : (T.fr ∅).χ i g = chi D T.pr i (resQ T.L g') := by rw [← hq]; rfl
  have hB : (T.fr ∅).χ j g = chi D T.pr j (resQ T.L g') := by rw [← hq]; rfl
  rw [hA, hB] at hrt
  have hAval : ((chi D T.pr i (resQ T.L g') : (c.O)ˣ) : c.O) =
      (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O) * (chi D T.pr j (resQ T.L g') : c.O) := by
    rw [← hrt, Units.val_mul]
  have hx : (K.r.chib i (K.V.pr g') / K.r.chib j (K.V.pr g')) ^ n = 1 :=
    DFunLike.congr_fun heq (K.V.pr g')
  have hx' := congrArg (fun u : (ResidueField c'.O)ˣ => (u : ResidueField c'.O)) hx
  simp only [Units.val_pow_eq_pow_val, Units.val_div_eq_div_val, Units.val_one] at hx'
  rw [K.chib i g', K.chib j g', hAval] at hx'
  have hκ : residue c'.O (K.κ g' : c'.O) ≠ 0 := ((K.κ g').isUnit.map (residue _)).ne_zero
  have hBn : residue c'.O (inc h (chi D T.pr j (resQ T.L g') : c.O)) ≠ 0 :=
    (((chi D T.pr j (resQ T.L g')).isUnit.map (inc h)).map (residue _)).ne_zero
  simp only [map_mul] at hx'
  rw [mul_div_mul_left _ _ hκ, mul_div_cancel_right₀ _ hBn] at hx'
  apply hne
  show (residue c.O (((T.fr ∅).rt (wt i j) g : (c.O)ˣ) : c.O)) ^ n = 1
  apply (ResidueField.map (inc h)).injective
  rw [map_pow, map_one, ResidueField.map_residue]
  exact hx'
