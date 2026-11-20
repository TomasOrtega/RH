import PositivityTheory.AutomorphicForms.PublishedInputs.HilbertEisenstein.SExpDefs

noncomputable section

open NumberField IsDedekindDomain Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual ReciprocityTheory.Gal Formalism.BasicNotions Formalism.MainNotions.N Polynomial
open GlobalTheory.CuspRep GlobalTheory.HeckeGal GlobalTheory.GalOfCusp UpperTheory.V.Af UpperTheory.V.Base
open scoped Matrix
open MeasureTheory GroundTheory.Global GroundTheory.Global.IdeleGroup UpperTheory.V.Sd UpperTheory.V.Published

namespace UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein

namespace L7

variable {F : Type} [Field F] [NumberField F] [IsTotallyReal F]

open Classical in
/- English proof (translation)
Use function extensionality and compare the values at `B`. Simplify using `only [slice, Phi, Matrix.cons_val_zero, Matrix.cons_val_one, h1]`. Use `congr 1`. Conclude with `if_congr (forall_congr' fun w => by rw [h2 w]) rfl rfl`.
-/
theorem slice_congr (c : HeightOneSpectrum (𝓞 F) → ℕ) {A A' : Ad F}
    (h1 : UpperTheory.V.TR.pInf F A = UpperTheory.V.TR.pInf F A')
    (h2 : ∀ w, Valued.v (pLoc F w (pFin F A)) = Valued.v (pLoc F w (pFin F A'))) :
    slice c A = slice c A' := by
  funext B
  simp only [slice, Phi, Matrix.cons_val_zero, Matrix.cons_val_one, h1]
  congr 1
  exact if_congr (forall_congr' fun w => by rw [h2 w]) rfl rfl

/- English proof (translation)
Use `show (UpperTheory.V.TR.infEq F).symm ((finiteEmbedding w x : IdeleGroup F) : Ad F).1 = 1`. Rewrite using `[coe_finiteEmbedding]`. Conclude with `map_one _`.
-/
theorem pInf_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    UpperTheory.V.TR.pInf F ((finiteEmbedding w x : IdeleGroup F) : Ad F) = 1 := by
  show (UpperTheory.V.TR.infEq F).symm ((finiteEmbedding w x : IdeleGroup F) : Ad F).1 = 1
  rw [coe_finiteEmbedding]
  exact map_one _

/- English proof (translation)
Use `show Valued.v ((((finiteEmbedding w x : IdeleGroup F) : Ad F).2) w') = 1`. Rewrite using `[coe_finiteEmbedding]`. Distinguish the cases in `h : w' = w`. Substitute `h show Valued.v (finiteAdeleSingle w' (x : w'.adicCompletion F) w') = 1` using the available equality. Rewrite using `[finiteAdeleSingle_apply_self]`.

Conclude with `hx`. Use `show Valued.v (finiteAdeleSingle w (x : w.adicCompletion F) w') = 1`. Rewrite using `[finiteAdeleSingle_apply_of_ne h]`. Conclude with `map_one _`.
-/
theorem valued_finiteEmbedding (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) (w' : HeightOneSpectrum (𝓞 F)) :
    Valued.v (pLoc F w' (pFin F ((finiteEmbedding w x : IdeleGroup F) : Ad F))) = 1 := by
  show Valued.v ((((finiteEmbedding w x : IdeleGroup F) : Ad F).2) w') = 1
  rw [coe_finiteEmbedding]
  by_cases h : w' = w
  · subst h
    show Valued.v (finiteAdeleSingle w' (x : w'.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_self]
    exact hx
  · show Valued.v (finiteAdeleSingle w (x : w.adicCompletion F) w') = 1
    rw [finiteAdeleSingle_apply_of_ne h]
    exact map_one _

/- English proof (translation)
Establish `hx' : Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1`. Rewrite using `[Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : w.adicCompletion F) = 1 from hx, inv_one]`. Use `IdeleGroup.norm_eq_one_of_mul_eq_one (b := ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F)) x.mul_inv ?_ ?_` and prove the remaining obligations. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx)`. Conclude with `(HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx')`.
-/
theorem norm_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    ‖(x : w.adicCompletion F)‖ = 1 := by
  have hx' : Valued.v ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F) = 1 := by
    rw [Units.val_inv_eq_inv_val, map_inv₀, show Valued.v (x : w.adicCompletion F) = 1 from hx, inv_one]
  refine IdeleGroup.norm_eq_one_of_mul_eq_one (b := ((x⁻¹ : (w.adicCompletion F)ˣ) : w.adicCompletion F))
    x.mul_inv ?_ ?_
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx)
  · exact (HeightOneSpectrum.mem_adicCompletionIntegers (R := 𝓞 F) F w).2 (le_of_eq hx')

/- English proof (translation)
The claim follows from `Subtype.ext (by rw [ideleModule_finiteEmbedding, norm_unit w x hx]; rfl)`.
-/
theorem ideleModule_finiteEmbedding_unit (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ)
    (hx : IsUnitAt w x) : ideleModule F (finiteEmbedding w x) = 1 :=
  Subtype.ext (by rw [ideleModule_finiteEmbedding, norm_unit w x hx]; rfl)

/- English proof (translation)
Establish `hs : slice c (((σ * finiteEmbedding w x : IdeleGroup F) : Ad F) * Y) = slice c ((σ : Ad F) * Y)`. Use `slice_congr c ?_ ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, map_mul, map_mul, map_mul, pInf_finiteEmbedding, mul_one]`. Introduce `w'`. Simplify using `only [Units.val_mul, map_mul, valued_finiteEmbedding w x hx w', mul_one]`.

Unfold `kern`. Rewrite using `[hs, map_mul, ideleModule_finiteEmbedding_unit w x hx, mul_one, map_zero, smul_zero, smul_zero]`.
-/
theorem kern_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (σ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    kern c Y (σ * finiteEmbedding w x) 0 = kern c Y σ 0 := by
  have hs : slice c (((σ * finiteEmbedding w x : IdeleGroup F) : Ad F) * Y) = slice c ((σ : Ad F) * Y) := by
    refine slice_congr c ?_ ?_
    · rw [Units.val_mul, map_mul, map_mul, map_mul, pInf_finiteEmbedding, mul_one]
    · intro w'
      simp only [Units.val_mul, map_mul, valued_finiteEmbedding w x hx w', mul_one]
  unfold kern
  rw [hs, map_mul, ideleModule_finiteEmbedding_unit w x hx, mul_one, map_zero, smul_zero, smul_zero]

/- English proof (translation)
The claim follows from `ω.2.2 δ`.
-/
theorem omega_diagonal (ω : HChar F) (δ : Fˣ) : ω.1 (diagonal F δ) = 1 := ω.2.2 δ

/- English proof (translation)
Unfold `coefK`. Use `(Equiv.mulLeft δ).tsum_eq (fun a => kern c Y (τ * diagonal F a) ξ)` as an intermediate fact. Rewrite using `[← this]`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[Equiv.coe_mulLeft, map_mul, mul_assoc]`.
-/
theorem coefK_mul_diagonal (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F) (δ : Fˣ) (ξ : F) :
    coefK c Y (τ * diagonal F δ) ξ = coefK c Y τ ξ := by
  unfold coefK
  have := (Equiv.mulLeft δ).tsum_eq (fun a => kern c Y (τ * diagonal F a) ξ)
  rw [← this]
  refine tsum_congr fun a => ?_
  rw [Equiv.coe_mulLeft, map_mul, mul_assoc]

/- English proof (translation)
Unfold `coefK`. Use `tsum_congr fun a => ?_` and prove the remaining obligations. Rewrite using `[mul_right_comm, kern_mul_unit c Y _ w x hx]`.
-/
theorem coefK_mul_unit (c : HeightOneSpectrum (𝓞 F) → ℕ) (Y : Ad F) (τ : IdeleGroup F)
    (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) (hx : IsUnitAt w x) :
    coefK c Y (τ * finiteEmbedding w x) 0 = coefK c Y τ 0 := by
  unfold coefK
  refine tsum_congr fun a => ?_
  rw [mul_right_comm, kern_mul_unit c Y _ w x hx]

/- English proof (translation)
Take `⟨w, hw⟩` from `H.ram`. Use `⟨w, ?_⟩` and prove the remaining obligations. Assume the negation of the conclusion as `hne`. Use `push Not at hne`. Establish `h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x → Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1}` using `fun x hx _ => hne x hx`.

Conclude with `hw (Nat.le_zero.1 ((H.cond w).2 h0))`.
-/
theorem exists_unit (ω : HChar F) (c : HeightOneSpectrum (𝓞 F) → ℕ) (H : Hyp ω c) :
    ∃ (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ), IsUnitAt w x ∧ ω.loc w x ≠ 1 := by
  obtain ⟨w, hw⟩ := H.ram
  refine ⟨w, ?_⟩
  by_contra hne
  push Not at hne
  have h0 : (0 : ℕ) ∈ {n : ℕ | ∀ x : (w.adicCompletion F)ˣ, IsUnitAt w x →
      Valued.v ((x : w.adicCompletion F) - 1) ≤ WithZero.exp (-(n : ℤ)) → ω.loc w x = 1} :=
    fun x hx _ => hne x hx
  exact hw (Nat.le_zero.1 ((H.cond w).2 h0))

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem loc_eq (ω : HChar F) (w : HeightOneSpectrum (𝓞 F)) (x : (w.adicCompletion F)ˣ) :
    ω.1 (finiteEmbedding w x) = ω.loc w x := rfl

end L7

open L7 in
/- English proof (translation)
Introduce `_ _ F _ _ _ ω c H y yf t _`. Use `set Y := yAd y yf`. Take `⟨w, x, hx, hω⟩` from `exists_unit ω c H`. Use `set h : normOneSubgroup F → ℂ := fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ with hdef`. Establish `hh : ∀ (δ : Fˣ) (u : normOneSubgroup F), h (u * diagonalToNormOne F δ) = h u`.

Introduce `δ u`. Establish `e1 : tau t (u * diagonalToNormOne F δ) = tau t u * diagonal F δ`. Simplify using `only [tau, Subgroup.coe_mul, coe_diagonalToNormOne, mul_assoc]`. Simplify using `only [hdef, e1, coefK_mul_diagonal, map_mul, omega_diagonal, mul_one]`. Establish `he1 : ideleModule F (finiteEmbedding w x) = 1` using `ideleModule_finiteEmbedding_unit w x hx`.

Set `e' : normOneSubgroup F` to `⟨finiteEmbedding w x, by rw [normOneSubgroup, MonoidHom.mem_ker]; exact he1⟩`. Establish `hshift : ∀ u, h (e' * u) = ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ * h u`. Introduce `u`. Establish `e2 : tau t (e' * u) = tau t u * finiteEmbedding w x`. Simplify using `only [tau, Subgroup.coe_mul, e']`.

Rewrite using `[mul_comm ((finiteEmbedding w x : IdeleGroup F)) (u : IdeleGroup F), mul_assoc]`. Simplify using `only [hdef, e2, coefK_mul_unit c Y _ w x hx, map_mul, Units.val_mul, mul_inv]`. Expand and normalize the polynomial expressions, which then agree. Establish `hI` using `setIntegral_mul_left_eq hh e'`. Simplify using `only [hshift] at hI`.

Rewrite `hI` using `[integral_const_mul]`. Establish `hne : ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ ≠ 1`. Rewrite using `[Ne, inv_eq_one, loc_eq]`. Introduce `h1`. Conclude with `hω (Units.ext h1)`.

Establish `h3 : (((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ - 1) * ∫ u in normOneFundamentalDomain F, h u ∂normOneMeasure F = 0`. Rewrite using `[sub_mul, one_mul, hI, sub_self]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)`.
-/
theorem null_term_holds : SFin → SKern → SNull := by
  intro _ _ F _ _ _ ω c H y yf t _
  set Y := yAd y yf
  obtain ⟨w, x, hx, hω⟩ := exists_unit ω c H
  set h : normOneSubgroup F → ℂ := fun u => coefK c Y (tau t u) 0 * ((ω.1 (tau t u) : ℂˣ) : ℂ)⁻¹ with hdef
  have hh : ∀ (δ : Fˣ) (u : normOneSubgroup F), h (u * diagonalToNormOne F δ) = h u := by
    intro δ u
    have e1 : tau t (u * diagonalToNormOne F δ) = tau t u * diagonal F δ := by
      simp only [tau, Subgroup.coe_mul, coe_diagonalToNormOne, mul_assoc]
    simp only [hdef, e1, coefK_mul_diagonal, map_mul, omega_diagonal, mul_one]
  have he1 : ideleModule F (finiteEmbedding w x) = 1 := ideleModule_finiteEmbedding_unit w x hx
  let e' : normOneSubgroup F := ⟨finiteEmbedding w x, by rw [normOneSubgroup, MonoidHom.mem_ker]; exact he1⟩
  have hshift : ∀ u, h (e' * u) = ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ * h u := by
    intro u
    have e2 : tau t (e' * u) = tau t u * finiteEmbedding w x := by
      simp only [tau, Subgroup.coe_mul, e']
      rw [mul_comm ((finiteEmbedding w x : IdeleGroup F)) (u : IdeleGroup F), mul_assoc]
    simp only [hdef, e2, coefK_mul_unit c Y _ w x hx, map_mul, Units.val_mul, mul_inv]
    ring
  have hI := setIntegral_mul_left_eq hh e'
  simp only [hshift] at hI
  rw [integral_const_mul] at hI
  have hne : ((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ ≠ 1 := by
    rw [Ne, inv_eq_one, loc_eq]
    intro h1
    exact hω (Units.ext h1)
  have h3 : (((ω.1 (finiteEmbedding w x) : ℂˣ) : ℂ)⁻¹ - 1) *
      ∫ u in normOneFundamentalDomain F, h u ∂normOneMeasure F = 0 := by
    rw [sub_mul, one_mul, hI, sub_self]
  exact (mul_eq_zero.1 h3).resolve_left (sub_ne_zero.2 hne)

end UpperTheory.HilbertEisensteinWeightOne.FourierExpansionEisenstein
