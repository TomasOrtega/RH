import Development.AutomorphicArithmetic.Foundations.Convolution.BlockEvaluation.TruncSpec
import Development.AutomorphicArithmetic.Foundations.Convolution.PolynomialCoefficientBounds.PowSym

open MeasureTheory NumberField IsDedekindDomain MvPolynomial Filter Topology UpperTheory.ConvolutionTheory UpperTheory.ConvolutionTheory.C UpperTheory.ConvolutionTheory.Ci

/- English proof (translation)
Choose the witnesses or unpack the hypotheses as in `⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by`. Proceed by induction on `s using Quotient.inductionOn with`. Consider the case `h l`. Establish `hl : l.length = n` using `by simpa using hs`. Substitute `hl` using the available equality.

Use `⟨l.get, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.univ_val_map, List.ofFn_get]`. Both sides reduce to the same expression. Establish `h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i) = expand f (esymm (Fin n) ℂ (i + 1))`. Rewrite using `[← esymmAlgHom_apply]`.

Use `congrArg Subtype.val ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)` as an intermediate fact. Conclude with `this`. Establish `h2` using `congrArg (aeval a) h1`. Rewrite `h2` using `[← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply]`. Establish `h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f`.

Apply `MvPolynomial.algHom_ext` to reduce the goal to its premises. Introduce `r`. Simplify using the standard rewrite rules. Rewrite `h2` using `[h3]`. Simplify using `only [aeval_esymm_eq_multiset_esymm] at h2`.

Rewrite using `[Multiset.map_map, ← coe_aeval_eq_eval]`. Conclude with `h2`.
-/
private theorem eval_powE {n : ℕ} (f : ℕ) (i : Fin n) (s : Multiset ℂ) (hs : s.card = n) :
    eval (fun j : Fin n => s.esymm (j + 1)) (powE f i) = (s.map (· ^ f)).esymm (i + 1) := by
  obtain ⟨a, rfl⟩ : ∃ a : Fin n → ℂ, s = Finset.univ.val.map a := by
    induction s using Quotient.inductionOn with
    | h l =>
      have hl : l.length = n := by simpa using hs
      subst hl
      refine ⟨l.get, ?_⟩
      rw [Fin.univ_val_map, List.ofFn_get]
      rfl
  have h1 : aeval (fun j : Fin n => esymm (Fin n) ℂ (j + 1)) (powE f i)
      = expand f (esymm (Fin n) ℂ (i + 1)) := by
    rw [← esymmAlgHom_apply]
    have := congrArg Subtype.val
      ((esymmAlgEquiv (Fin n) ℂ (Fintype.card_fin n)).apply_symm_apply
        ⟨expand f (esymm (Fin n) ℂ (i + 1)), fun w => by rw [rename_expand, esymm_isSymmetric]⟩)
    exact this
  have h2 := congrArg (aeval a) h1
  rw [← AlgHom.comp_apply, comp_aeval, ← AlgHom.comp_apply] at h2
  have h3 : (aeval a : MvPolynomial (Fin n) ℂ →ₐ[ℂ] ℂ).comp (expand f) = aeval fun r => a r ^ f := by
    apply MvPolynomial.algHom_ext
    intro r
    simp
  rw [h3] at h2
  simp only [aeval_esymm_eq_multiset_esymm] at h2
  rw [Multiset.map_map, ← coe_aeval_eq_eval]
  exact h2

/- English proof (translation)
Introduce `F E _ _ _ _ _ n x Λ t P hP`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← RingHom.comp_apply]`. Use `hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl` and prove the remaining obligations. Apply `MvPolynomial.ringHom_ext` to reduce the goal to its premises.

Introduce `c`. Simplify using `[val, bcPR]`. Introduce and unpack `(_ | y)`. Simplify using `[val, bcPR]`. Simplify using `[val, bcPR, bcInf]`.

Introduce `y hy _`. Establish `h` using `eval_powE (resDeg F y.1) y.2 _ (hP y hy)`. Simplify using `only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]`. Rewrite using `[hval, bcSat, ← h]`. Establish `hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C) = RingHom.id ℂ`.

Use extensionality with `c`. Simplify using the standard rewrite rules. Rewrite using `[hc]`. Both sides reduce to the same expression. Introduce `y hy`.

Establish `h : bcPR F P = bind₁ (fun x : Pl E × Fin n => (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n)) (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P)`. Rewrite using `[bind₁, aeval_def, eval₂_map]`. Both sides reduce to the same expression. Rewrite `hy` using `[h]`. Take `⟨y', hy', hy2⟩` from `mem_vars_bind₁ _ _ hy`.

Use `⟨y', vars_map _ _ hy', ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `mem_vars_rename _ _ (vars_map _ _ hy2)`. Both sides reduce to the same expression. Introduce `η m`. Simplify using `only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]`.

Rewrite using `[← Polynomial.aeval_algHom_apply]`. Simplify using the standard rewrite rules.
-/
theorem UpperTheory.ConvolutionTheory.Ci.valBc :
    ValBc := by
  classical
  intro F E _ _ _ _ _ n x Λ t P hP
  refine ⟨?_, ?_, ?_⟩
  · rw [← RingHom.comp_apply]
    refine hom_congr_vars (p₁ := P) (p₂ := P) ?_ ?_ rfl
    · apply MvPolynomial.ringHom_ext
      · intro c
        simp [val, bcPR]
      · rintro (_ | y)
        · simp [val, bcPR]
        · simp [val, bcPR, bcInf]
    · intro y hy _
      have h := eval_powE (resDeg F y.1) y.2 _ (hP y hy)
      simp only [val, bcPR, RingHom.comp_apply, eval₂Hom_X', coe_eval₂Hom, eval₂_map, eval₂_rename, eval₂_X]
      rw [hval, bcSat, ← h]
      have hc : ((eval fun o : Option (Ix F n) => o.elim (x : ℂ) fun y => x * (Λ y.1).esymm (y.2 + 1)).comp C)
          = RingHom.id ℂ := by
        ext c
        simp
      rw [hc]
      rfl
  · intro y hy
    have h : bcPR F P = bind₁ (fun x : Pl E × Fin n =>
        (map C (rename (fun i => (x.1.under (𝓞 F), i)) (powE (resDeg F x.1) x.2)) : PR F n))
        (map (rename (Option.map fun x : Ix E n => (x.1.comp (algebraMap F E), x.2))).toRingHom P) := by
      rw [bind₁, aeval_def, eval₂_map]
      rfl
    rw [h] at hy
    obtain ⟨y', hy', hy2⟩ := mem_vars_bind₁ _ _ hy
    refine ⟨y', vars_map _ _ hy', ?_⟩
    obtain ⟨i, -, rfl⟩ := mem_vars_rename _ _ (vars_map _ _ hy2)
    rfl
  · intro η m
    simp only [chebP, bcPR, eval₂Hom_C, RingHom.comp_apply, AlgHom.toRingHom_eq_coe, RingHom.coe_coe]
    rw [← Polynomial.aeval_algHom_apply]
    simp
