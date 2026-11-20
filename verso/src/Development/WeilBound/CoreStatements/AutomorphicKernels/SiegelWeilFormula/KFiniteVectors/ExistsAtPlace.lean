import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.KFiniteVectors.FirstFrameHalfEqMul

noncomputable section

open scoped TensorProduct NNReal Matrix SchwartzMap Classical Pointwise
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.KK

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

open Matrix

variable {d : SD σ}

/- English proof (translation)
Establish `h` using `d.ok.good.cm`. Use `choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' => if w' = w then V i j else 0`. Use `⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Use `show piInf (d.B.emb w') (x i j) = _`.

Rewrite using `[hz i j w']`. Apply the tactic sequence `split_ifs <;> rfl`.
-/
theorem exists_at_place (w : InfinitePlace F) (V : Matrix (Fin d.m) (Fin d.n) ℂ) :
    ∃ V' : Mx F E d.m d.n, At (evI F) V' ∧ ∀ w', d.cw w' V' = if w' = w then V else 0 := by
  have h := d.ok.good.cm
  choose x hx hz using fun i j => GlobalTheory.CompanionTheory.RealPlaceAdele.exists_adele_piInf σ h d.B.emb fun w' =>
    if w' = w then V i j else 0
  refine ⟨Matrix.of x, fun c hc => Matrix.ext fun i j => hx i j c hc, fun w' => ?_⟩
  ext i j
  show piInf (d.B.emb w') (x i j) = _
  rw [hz i j w']
  split_ifs <;> rfl

/- English proof (translation)
Establish `e1 : V' * tAᵀ * (dg d)ᵀ = V' * (b1 d)ᵀ` using `by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]`. Rewrite using `[mZ, e1, trace_sp, Finset.sum_eq_single w]`. Use `congr 3`. Establish `hX : (X * (b2 d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ`. Rewrite using `[map_mul_incM_transpose_eq]`.

Both sides reduce to the same expression. Establish `hVb : (V' * (b1 d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ`. Rewrite using `[map_mul_incM_transpose_eq]`. Use `hV w` as an intermediate fact. Rewrite `this` using `[if_pos rfl]`.

Rewrite using `[show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]`. Both sides reduce to the same expression. Rewrite using `[hX, hVb]`. Conclude with `trace_form_sign_eq (frame_form R w) (d.cw w X) V`. Introduce `w' _ hw'`.

Establish `hVb : (V' * (b1 d)ᵀ).map (piInf (d.B.emb w')) = 0`. Rewrite using `[map_mul_incM_transpose_eq]`. Use `hV w'` as an intermediate fact. Rewrite `this` using `[if_neg hw']`. Rewrite using `[show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]`.

Rewrite using `[hVb]`. Simplify using the standard rewrite rules. Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`.
-/
theorem mZ_place (R : RD d) (w : InfinitePlace F) (tA : Matrix (Fin d.n) (Fin d.n) (AE F E)) (htA : b1 d = dg d * tA)
    {V' : Mx F E d.m d.n} {V : Matrix (Fin d.m) (Fin d.n) ℂ} (hV : ∀ w', d.cw w' V' = if w' = w then V else 0)
    (X : Mx F E d.m d.n) :
    mZ d (V' * tAᵀ) X = -(2 * ((((R.ε : ℤ) : ℂ)) * trace ((d.cw w X)ᵀ * d.A.J.map (d.B.emb w).1 * V.map star)).re) := by
  have e1 : V' * tAᵀ * (dg d)ᵀ = V' * (b1 d)ᵀ := by rw [htA, Matrix.transpose_mul, Matrix.mul_assoc]
  rw [mZ, e1, trace_sp, Finset.sum_eq_single w]
  · congr 3
    have hX : (X * (b2 d)ᵀ).map (piInf (d.B.emb w)) = d.cw w X * ((d.b.1.map (d.B.emb w).1).toCols₂)ᵀ := by
      rw [map_mul_incM_transpose_eq]; rfl
    have hVb : (V' * (b1 d)ᵀ).map (piInf (d.B.emb w)) = V * ((d.b.1.map (d.B.emb w).1).toCols₁)ᵀ := by
      rw [map_mul_incM_transpose_eq]
      have := hV w
      rw [if_pos rfl] at this
      rw [show V'.map (piInf (d.B.emb w)) = d.cw w V' from rfl, this]
      rfl
    rw [hX, hVb]
    exact trace_form_sign_eq (frame_form R w) (d.cw w X) V
  · intro w' _ hw'
    have hVb : (V' * (b1 d)ᵀ).map (piInf (d.B.emb w')) = 0 := by
      rw [map_mul_incM_transpose_eq]
      have := hV w'
      rw [if_neg hw'] at this
      rw [show V'.map (piInf (d.B.emb w')) = d.cw w' V' from rfl, this, Matrix.zero_mul]
    rw [hVb]
    simp
  · intro h; exact absurd (Finset.mem_univ w) h

/- English proof (translation)
Take `⟨tA, htA⟩` from `first_frame_half_eq_mul (d := d)`. Use `set τ := d.B.emb w`. Use `set fr := (R.fr w).1`. Use `set fi := ((R.fr w)⁻¹).1`. Use `set A := d.A.J.map τ.1`.

Use `set e : ℂ := ((R.ε : ℤ) : ℂ)`. Apply the tactic sequence `have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]`. Establish `hes : star e = e` using `by simp [e]`. Apply the tactic sequence `have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]`. Establish `hfi : fr * fi = 1` using `by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]`.

Establish `hif : fi * fr = 1` using `by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]`. Use `set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)`. Establish `hAP : A * P = 1`. Establish `hA` using `A_eq hfi hz (R.hfr w)`. Rewrite `hA` using `[show d.A.J.map (d.B.emb w).1 = A from rfl]`.

Rewrite using `[hA]`. Simplify using `only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]`. Establish `t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1`. Rewrite using `[Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]`. Rewrite using `[show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 by ext i j; simp [one_apply, apply_ite]]`.

Rewrite using `[Matrix.one_mul, ← transpose_mul, hfi, transpose_one]`. Rewrite using `[t1]`. Establish `hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hs2, one_smul]`.

Establish `key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧ ∀ X, (mZ d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ)`. Introduce `M`. Take `⟨V', hV'a, hV'⟩` from `exists_at_place (d := d) w ((P * M).map star)`. Use `⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩` and prove the remaining obligations. Rewrite using `[mZ_place R w tA htA hV' X]`.

Establish `: (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M`. Rewrite using `[show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP, Matrix.mul_one]`. Rewrite using `[show d.A.J.map (d.B.emb w).1 = A from rfl, this]`. Establish `hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re`. Apply the tactic sequence `rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]`.

Rewrite using `[hre]`. Apply the tactic sequence `rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring`. Establish `hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ), trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1` using `fun c x => by`. Simplify using `only [trace, diag, mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]`. Rewrite using `[Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]`.

Simplify using `only [if_pos rfl, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring`. Take `⟨Z₁, h1, e1⟩` from `key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)`. Take `⟨Z₂, h2, e2⟩` from `key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)`. Establish `hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) = if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1)` using `fun X => by`.

Simplify using `only [evX, MvPolynomial.eval_X, RD.loc, Matrix.map_apply]`. Apply the tactic sequence `split_ifs <;> (try simp only [star_star]) <;> rfl`. Establish `hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ)` using `fun z => by`. Apply the tactic sequence `apply Complex.ext <;> simp`. Establish `hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ)` using `fun z => by`.

Apply the tactic sequence `apply Complex.ext <;> simp`. Use `⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2, fun X => ?_⟩` and prove the remaining obligations. Rewrite using `[hl X, e1 X, e2 X, hM, hM, one_mul]`. Establish `hinv : -(e / 2) * (-(2 * e)) = 1` using `by linear_combination he`. Use `split_ifs`.

Use `conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]`. Take the linear combination `(-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv`. Rewrite using `[hsplit' ((fi * d.cw w X) k.1 k.2.1)]`. Take the linear combination `(-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv`.
-/
theorem var_span' (R : RD d) (w : InfinitePlace F) (k : Fin d.m × Fin d.n × Bool) :
    ∃ (Z₁ Z₂ : Mx F E d.m d.n) (c₁ c₂ : ℂ), At (evI F) Z₁ ∧ At (evI F) Z₂ ∧
      ∀ X, evX (MvPolynomial.X k) (R.loc w X) = c₁ * (mZ d Z₁ X : ℂ) + c₂ * (mZ d Z₂ X : ℂ) := by
  obtain ⟨tA, htA⟩ := first_frame_half_eq_mul (d := d)
  set τ := d.B.emb w
  set fr := (R.fr w).1
  set fi := ((R.fr w)⁻¹).1
  set A := d.A.J.map τ.1
  set e : ℂ := ((R.ε : ℤ) : ℂ)
  have he : e * e = 1 := by rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
  have hes : star e = e := by simp [e]
  have hz : star R.ζ * R.ζ = 1 := by rcases R.hζ with ⟨-, h⟩ | ⟨-, h⟩ <;> rw [h] <;> simp [Complex.ext_iff]
  have hfi : fr * fi = 1 := by simp only [fr, fi]; rw [← Units.val_mul, mul_inv_cancel, Units.val_one]
  have hif : fi * fr = 1 := by simp only [fr, fi]; rw [← Units.val_mul, inv_mul_cancel, Units.val_one]

  set P := (((R.sg w : ℤ) : ℂ) * R.ζ) • (fr.map star * frᵀ)
  have hAP : A * P = 1 := by
    have hA := A_eq hfi hz (R.hfr w)
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl] at hA
    rw [hA]
    simp only [P, Matrix.smul_mul, Matrix.mul_smul, smul_smul]
    have t1 : fiᵀ * fi.map star * (fr.map star * frᵀ) = 1 := by
      rw [Matrix.mul_assoc, ← Matrix.mul_assoc (fi.map star), ← mapStar_mul, hif]
      rw [show (1 : Matrix (Fin d.m) (Fin d.m) ℂ).map star = 1 by ext i j; simp [one_apply, apply_ite]]
      rw [Matrix.one_mul, ← transpose_mul, hfi, transpose_one]
    rw [t1]
    have hs2 : ((R.sg w : ℤ) : ℂ) * R.ζ * (((R.sg w : ℤ) : ℂ) * star R.ζ) = 1 := by
      calc _ = (((R.sg w : ℤ) : ℂ) * ((R.sg w : ℤ) : ℂ)) * (star R.ζ * R.ζ) := by ring
        _ = 1 := by rw [hz, mul_one]; rcases Int.units_eq_one_or (R.sg w) with h | h <;> simp [h]
    rw [hs2, one_smul]

  have key : ∀ M : Matrix (Fin d.m) (Fin d.n) ℂ, ∃ Z : Mx F E d.m d.n, At (evI F) Z ∧
      ∀ X, (mZ d Z X : ℂ) = -(2 * e) * ((trace ((d.cw w X)ᵀ * M)).re : ℂ) := by
    intro M
    obtain ⟨V', hV'a, hV'⟩ := exists_at_place (d := d) w ((P * M).map star)
    refine ⟨V' * tAᵀ, at_mul hV'a _, fun X => ?_⟩
    rw [mZ_place R w tA htA hV' X]
    have : (d.cw w X)ᵀ * A * ((P * M).map star).map star = (d.cw w X)ᵀ * M := by
      rw [show ((P * M).map star).map star = P * M by ext i j; simp only [Matrix.map_apply, star_star], ← Matrix.mul_assoc, Matrix.mul_assoc _ A, hAP,
        Matrix.mul_one]
    rw [show d.A.J.map (d.B.emb w).1 = A from rfl, this]
    have hre : (e * trace ((d.cw w X)ᵀ * M)).re = e.re * (trace ((d.cw w X)ᵀ * M)).re := by
      rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h]
    rw [hre]
    rcases Int.units_eq_one_or R.ε with h | h <;> simp [e, h] <;> ring

  have hM : ∀ (c : ℂ) (x : Matrix (Fin d.m) (Fin d.n) ℂ),
      trace (xᵀ * Matrix.of fun b j => if j = k.2.1 then c * fi k.1 b else 0) = c * (fi * x) k.1 k.2.1 := fun c x => by
    simp only [trace, diag, mul_apply, transpose_apply, of_apply, mul_ite, mul_zero]
    rw [Finset.sum_eq_single k.2.1 (fun j _ hj => by simp [hj]) (by simp)]
    simp only [if_pos rfl, Finset.mul_sum]
    exact Finset.sum_congr rfl fun b _ => by simp only [if_true]; ring
  obtain ⟨Z₁, h1, e1⟩ := key (Matrix.of fun b j => if j = k.2.1 then 1 * fi k.1 b else 0)
  obtain ⟨Z₂, h2, e2⟩ := key (Matrix.of fun b j => if j = k.2.1 then (-Complex.I) * fi k.1 b else 0)
  have hl : ∀ X, evX (MvPolynomial.X k) (R.loc w X) =
      if k.2.2 then (fi * d.cw w X) k.1 k.2.1 else star ((fi * d.cw w X) k.1 k.2.1) := fun X => by
    simp only [evX, MvPolynomial.eval_X, RD.loc, Matrix.map_apply]
    split_ifs <;> (try simp only [star_star]) <;> rfl
  have hsplit : ∀ z : ℂ, z = (z.re : ℂ) + Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  have hsplit' : ∀ z : ℂ, star z = (z.re : ℂ) - Complex.I * ((-Complex.I * z).re : ℂ) := fun z => by
    apply Complex.ext <;> simp
  refine ⟨Z₁, Z₂, -(e / 2) * (if k.2.2 then 1 else 1), -(e / 2) * (if k.2.2 then Complex.I else -Complex.I), h1, h2,
    fun X => ?_⟩
  rw [hl X, e1 X, e2 X, hM, hM, one_mul]
  have hinv : -(e / 2) * (-(2 * e)) = 1 := by linear_combination he
  split_ifs
  · conv_lhs => rw [hsplit ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) - Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv
  · rw [hsplit' ((fi * d.cw w X) k.1 k.2.1)]
    linear_combination (-(((fi * d.cw w X) k.1 k.2.1).re : ℂ) + Complex.I * ((-Complex.I * (fi * d.cw w X) k.1 k.2.1).re : ℂ)) * hinv

end PositivityTheory.SiegelWeilFormula.KK

end
