import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.UnitaryHyperbolicOrbitCount
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.ThFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.IntegralityNearIdentity.ExistsContDiffEventuallyEq

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.Z.Sym.Sig

namespace UpperTheory.V.Z.Sym.Sig

/- English proof (translation)
The claim follows from `UpperTheory.V.Lib.Small.conj_of_roots (fun i => (μ i : k)) (fun _ _ e => hμ (Units.ext e)) N _ (GlobalTheory.SmGL.val_diagT k μ) hroot`.
-/
private theorem exists_conj_diag {k : Type} [Field k] (N : GL (Fin 3) k) (μ : Fin 3 → kˣ)
    (hμ : Function.Injective μ) (hroot : ∀ i, ((N : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot (μ i : k)) :
    ∃ g : GL (Fin 3) k, N = g * diagT k (Fin 3) μ * g⁻¹ :=
  UpperTheory.V.Lib.Small.conj_of_roots (fun i => (μ i : k)) (fun _ _ e => hμ (Units.ext e)) N _ (GlobalTheory.SmGL.val_diagT k μ) hroot

/- English proof (translation)
Establish `hoff : ∀ i j, i ≠ j → (e : Matrix (Fin 3) (Fin 3) k) i j = 0`. Introduce `i j hij`. Establish `h1` using `congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M i j) (congrArg Units.val h)`. Simplify using `only [Units.val_mul, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1`. Establish `h2 : (μ j : k) ≠ μ i` using `fun h' => hij (hμ (Units.ext h')).symm`.

Establish `h3 : (e : Matrix (Fin 3) (Fin 3) k) i j * ((μ j : k) - μ i) = 0`. Rewrite using `[mul_sub, h1]`. Expand and normalize the polynomial expressions, which then agree. Conclude with `(mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)`. Establish `hdiag : (e : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal fun i => (e : Matrix (Fin 3) (Fin 3) k) i i`.

Use extensionality with `i j`. Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[hoff i j hij, Matrix.diagonal_apply_ne _ hij]`.

Establish `hdet : (e : Matrix (Fin 3) (Fin 3) k).det ≠ 0` using `((Matrix.isUnit_iff_isUnit_det _).1 e.isUnit).ne_zero`. Establish `hne : ∀ i, (e : Matrix (Fin 3) (Fin 3) k) i i ≠ 0`. Introduce `i hi`. Apply `hdet` to reduce the goal to its premises. Rewrite using `[hdiag, Matrix.det_diagonal]`.

Conclude with `Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)`. Use `⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩` and prove the remaining obligations. Rewrite using `[val_diagT]`. Simplify using `using hdiag`.
-/
private theorem diag_of_comm {k : Type} [Field k] (μ : Fin 3 → kˣ) (hμ : Function.Injective μ)
    (e : GL (Fin 3) k) (h : e * diagT k (Fin 3) μ = diagT k (Fin 3) μ * e) :
    ∃ u : Fin 3 → kˣ, e = diagT k (Fin 3) u := by
  have hoff : ∀ i j, i ≠ j → (e : Matrix (Fin 3) (Fin 3) k) i j = 0 := by
    intro i j hij
    have h1 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M i j) (congrArg Units.val h)
    simp only [Units.val_mul, val_diagT, Matrix.mul_diagonal, Matrix.diagonal_mul] at h1
    have h2 : (μ j : k) ≠ μ i := fun h' => hij (hμ (Units.ext h')).symm
    have h3 : (e : Matrix (Fin 3) (Fin 3) k) i j * ((μ j : k) - μ i) = 0 := by
      rw [mul_sub, h1]; ring
    exact (mul_eq_zero.1 h3).resolve_right (sub_ne_zero.2 h2)
  have hdiag : (e : Matrix (Fin 3) (Fin 3) k) = Matrix.diagonal fun i => (e : Matrix (Fin 3) (Fin 3) k) i i := by
    ext i j
    by_cases hij : i = j
    · subst hij; simp
    · simp [hoff i j hij, Matrix.diagonal_apply_ne _ hij]
  have hdet : (e : Matrix (Fin 3) (Fin 3) k).det ≠ 0 :=
    ((Matrix.isUnit_iff_isUnit_det _).1 e.isUnit).ne_zero
  have hne : ∀ i, (e : Matrix (Fin 3) (Fin 3) k) i i ≠ 0 := by
    intro i hi
    apply hdet
    rw [hdiag, Matrix.det_diagonal]
    exact Finset.prod_eq_zero (Finset.mem_univ i) (by simpa using hi)
  refine ⟨fun i => Units.mk0 _ (hne i), Units.ext ?_⟩
  rw [val_diagT]
  simpa using hdiag

end UpperTheory.V.Z.Sym.Sig

/- English proof (translation)
Introduce `k _ _ _ _`. Take `⟨-, -, hd, hθ, hΦ, hi, hc⟩` from `thFacts k (Lev.iw k)`. Take `hP` from `(thFacts k (Lev.iw k)).1`. Establish `ht : ∀ u : GL (Fin 3) k, th' k u = Phi k * th k 3 u * (Phi k)⁻¹` using `fun u => rfl`. Establish `hprod : ∀ x y z : kˣ, dg ![x, y, z] * th' k (dg ![x, y, z]) = dg ![x / z, 1, z / x]`.

Introduce `x y z`. Rewrite using `[hd, ← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [div_eq_mul_inv, mul_comm]`.

Use `⟨fun g₀ x y z => ?_, fun δ a ha hch => ?_⟩` and prove the remaining obligations. Rewrite using `[← hprod x y z, ht]`. Simplify using `only [map_mul, map_inv, hθ, hΦ]`. Use `group`. Establish `ha0 : (a : k) ≠ 0` using `a.ne_zero`.

Establish `hgt : 1 < valuation k ((a⁻¹ : kˣ) : k)`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀]`. Conclude with `(one_lt_inv₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 ha0))).2 ha`. Establish `h1 : (a : k) ≠ 1` using `fun h => by rw [h, map_one] at ha; exact lt_irrefl _ ha`. Establish `h2 : ((a⁻¹ : kˣ) : k) ≠ 1` using `fun h => by rw [h, map_one] at hgt; exact lt_irrefl _ hgt`.

Establish `h3 : (a : k) ≠ ((a⁻¹ : kˣ) : k)` using `fun h => by`. Rewrite `hgt` using `[← h]`. Conclude with `lt_asymm ha hgt`. Establish `hμ : Function.Injective (![a, 1, a⁻¹] : Fin 3 → kˣ)`. Introduce `i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> first`. Consider the case `rfl`. Consider the case `(exfalso`. Establish `hij'` using `congrArg Units.val hij`. Simplify using `only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Units.val_one] at hij'`.

Use `first`. Consider the case `exact h1 hij' | exact h1 hij'.symm | exact h2 hij' | exact h2 hij'.symm`. Consider the case `exact h3 hij' | exact h3 hij'.symm)`. Establish `hroot : ∀ i, (((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot (((![a, 1, a⁻¹] : Fin 3 → kˣ) i : kˣ) : k)`. Introduce `i`.

Rewrite using `[hch]`. Apply the tactic sequence `fin_cases i <;> simp [Polynomial.IsRoot]`. Take `⟨g₀, hN⟩` from `exists_conj_diag (δ * th k 3 δ) _ hμ hroot`. Use `set n : GL (Fin 3) k := dg ![a, 1, a⁻¹] with hn`. Use `set e : GL (Fin 3) k := g₀⁻¹ * δ * th k 3 g₀ * (Phi k)⁻¹ with he`.

Establish `hen : e * th' k e = n`. Establish `: e * th' k e = g₀⁻¹ * (δ * th k 3 δ) * g₀`. Rewrite using `[ht, he]`. Simplify using `only [map_mul, map_inv, hθ, hΦ, inv_inv]`. Use `group`.

Rewrite using `[this, hN]`. Simplify using `only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]`. Apply the tactic sequence `try rfl`. Establish `hfix : th' k n = n`. Rewrite using `[hn, hd]`.

Simplify using the standard rewrite rules. Establish `hne : th' k e * e = n`. Use `congrArg (th' k) hen` as an intermediate fact. Rewrite `this` using `[map_mul, hP.invol, hfix]`. Then use the resulting hypothesis. Establish `hcomm : e * n = n * e` using `by nth_rewrite 1 [← hne] nth_rewrite 1 [← hen] group`.

Take `⟨u, hu⟩` from `diag_of_comm _ hμ e hcomm`. Establish `hu' : u = ![u 0, u 1, u 2]`. Apply the tactic sequence `funext i; fin_cases i <;> rfl`. Use `⟨g₀, u 0, u 1, u 2, ?_, ?_⟩` and prove the remaining obligations. Establish `: dg ![u 0, u 1, u 2] = e` using `by rw [hu]; exact congrArg _ hu'.symm`.

Rewrite using `[this, he]`. Use `group`. Establish `h4 : dg ![u 0 / u 2, 1, u 2 / u 0] = n`. Rewrite using `[← hprod, ← hu' , ← hen, hu]`. Establish `h5` using `congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) (congrArg Units.val h4)`.

Simplify using `only [hn, dg, val_diagT] at h5`. Simplify `h5` using `[Units.ext_iff]`.
-/
theorem UpperTheory.V.Z.Sym.Sig.normalG :
    UpperTheory.V.Z.Sym.Sig.NormalG := by
  intro k _ _ _ _
  obtain ⟨-, -, hd, hθ, hΦ, hi, hc⟩ := thFacts k (Lev.iw k)
  obtain hP := (thFacts k (Lev.iw k)).1
  have ht : ∀ u : GL (Fin 3) k, th' k u = Phi k * th k 3 u * (Phi k)⁻¹ := fun u => rfl
  have hprod : ∀ x y z : kˣ, dg ![x, y, z] * th' k (dg ![x, y, z]) = dg ![x / z, 1, z / x] := by
    intro x y z
    rw [hd, ← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [div_eq_mul_inv, mul_comm]
  refine ⟨fun g₀ x y z => ?_, fun δ a ha hch => ?_⟩
  · rw [← hprod x y z, ht]
    simp only [map_mul, map_inv, hθ, hΦ]
    group
  · have ha0 : (a : k) ≠ 0 := a.ne_zero
    have hgt : 1 < valuation k ((a⁻¹ : kˣ) : k) := by
      rw [Units.val_inv_eq_inv_val, map_inv₀]
      exact (one_lt_inv₀ (zero_lt_iff.2 ((valuation k).ne_zero_iff.2 ha0))).2 ha
    have h1 : (a : k) ≠ 1 := fun h => by rw [h, map_one] at ha; exact lt_irrefl _ ha
    have h2 : ((a⁻¹ : kˣ) : k) ≠ 1 := fun h => by rw [h, map_one] at hgt; exact lt_irrefl _ hgt
    have h3 : (a : k) ≠ ((a⁻¹ : kˣ) : k) := fun h => by
      rw [← h] at hgt; exact lt_asymm ha hgt
    have hμ : Function.Injective (![a, 1, a⁻¹] : Fin 3 → kˣ) := by
      intro i j hij
      fin_cases i <;> fin_cases j <;> first
        | rfl
        | (exfalso
           have hij' := congrArg Units.val hij
           simp only [Fin.zero_eta, Fin.mk_one, Fin.reduceFinMk, Matrix.cons_val, Units.val_one] at hij'
           first
             | exact h1 hij' | exact h1 hij'.symm | exact h2 hij' | exact h2 hij'.symm
             | exact h3 hij' | exact h3 hij'.symm)
    have hroot : ∀ i, (((δ * th k 3 δ : GL (Fin 3) k) : Matrix (Fin 3) (Fin 3) k).charpoly).IsRoot
        (((![a, 1, a⁻¹] : Fin 3 → kˣ) i : kˣ) : k) := by
      intro i
      rw [hch]
      fin_cases i <;> simp [Polynomial.IsRoot]
    obtain ⟨g₀, hN⟩ := exists_conj_diag (δ * th k 3 δ) _ hμ hroot
    set n : GL (Fin 3) k := dg ![a, 1, a⁻¹] with hn
    set e : GL (Fin 3) k := g₀⁻¹ * δ * th k 3 g₀ * (Phi k)⁻¹ with he
    have hen : e * th' k e = n := by
      have : e * th' k e = g₀⁻¹ * (δ * th k 3 δ) * g₀ := by
        rw [ht, he]
        simp only [map_mul, map_inv, hθ, hΦ, inv_inv]
        group
      rw [this, hN]
      simp only [mul_assoc, inv_mul_cancel_left, inv_mul_cancel, mul_one]
      try rfl
    have hfix : th' k n = n := by
      rw [hn, hd]
      simp
    have hne : th' k e * e = n := by
      have := congrArg (th' k) hen
      rwa [map_mul, hP.invol, hfix] at this
    have hcomm : e * n = n * e := by
      nth_rewrite 1 [← hne]
      nth_rewrite 1 [← hen]
      group
    obtain ⟨u, hu⟩ := diag_of_comm _ hμ e hcomm
    have hu' : u = ![u 0, u 1, u 2] := by
      funext i; fin_cases i <;> rfl
    refine ⟨g₀, u 0, u 1, u 2, ?_, ?_⟩
    · have : dg ![u 0, u 1, u 2] = e := by rw [hu]; exact congrArg _ hu'.symm
      rw [this, he]
      group
    · have h4 : dg ![u 0 / u 2, 1, u 2 / u 0] = n := by
        rw [← hprod, ← hu' , ← hen, hu]
      have h5 := congrArg (fun M : Matrix (Fin 3) (Fin 3) k => M 0 0) (congrArg Units.val h4)
      simp only [hn, dg, val_diagT] at h5
      simpa [Units.ext_iff] using h5

end
