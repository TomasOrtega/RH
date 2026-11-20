import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ProjectiveAutomorphicHecke.CyclotomicConjugation.QuadConjAlt
import GroundTheory.AutomorphicForms.StrongApproximationSLDense
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.Conjugation

open NumberField IsDedekindDomain Matrix GlobalTheory.CuspRep GlobalTheory.UnitaryBC GlobalTheory.DefU Formalism.L2.Host GlobalTheory.HeckeGal
open GlobalTheory.SplitPts (conjE)
open GroundTheory.Global.AdeleBaseChange (finiteAdeleMap)
open UpperTheory.Gal.CertificateRingHomMap UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂
open scoped NumberField.AdeleRing

noncomputable section
open GroundTheory.Global GroundTheory.Global.AdeleBaseChange
open scoped Classical
variable {E : Type} [Field E] [NumberField E] [IsCMField E]

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis hd hx`.
-/
private theorem conj_alt_bis {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : conjE E x = -x :=
  _root_.UpperTheory.Reformulated.B.CMConjugationOfSqrtNeg.conj_alt_bis hd hx

/- English proof (translation)
The claim follows from `IsCMField.complexConj_apply_apply E a`.
-/
private theorem conj_conj' (a : E) : conjE E (conjE E a) = a := IsCMField.complexConj_apply_apply E a

/- English proof (translation)
Proceed by induction on `ha using IntermediateField.adjoin_induction with`. Consider the case `mem a h`. Rewrite using `[Set.mem_singleton_iff.1 h, conj_alt_bis hd hx]`. Conclude with `neg_mem (IntermediateField.mem_adjoin_simple_self ℚ x)`. Consider the case `algebraMap q`.

Establish `: conjE E (algebraMap ℚ E q) = algebraMap ℚ E q` using `by simp`. Rewrite using `[this]`. Conclude with `IntermediateField.algebraMap_mem _ q`. Consider the case `add a b _ _ ha hb => rw [map_add]`. Conclude with `add_mem ha hb`.

Consider the case `inv a _ ha => rw [map_inv₀]`. Conclude with `inv_mem ha`. Consider the case `mul a b _ _ ha hb => rw [map_mul]`. Conclude with `mul_mem ha hb`.
-/
private theorem conj_mem {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : E)
    (ha : a ∈ IntermediateField.adjoin ℚ {x}) : conjE E a ∈ IntermediateField.adjoin ℚ {x} := by
  induction ha using IntermediateField.adjoin_induction with
  | mem a h =>
    rw [Set.mem_singleton_iff.1 h, conj_alt_bis hd hx]
    exact neg_mem (IntermediateField.mem_adjoin_simple_self ℚ x)
  | algebraMap q =>
    have : conjE E (algebraMap ℚ E q) = algebraMap ℚ E q := by simp
    rw [this]
    exact IntermediateField.algebraMap_mem _ q
  | add a b _ _ ha hb => rw [map_add]; exact add_mem ha hb
  | inv a _ ha => rw [map_inv₀]; exact inv_mem ha
  | mul a b _ _ ha hb => rw [map_mul]; exact mul_mem ha hb

private def cK {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : Kx x ≃ₐ[ℚ] Kx x :=
  let c0 : Kx x →ₐ[ℚ] Kx x :=
    { toFun := fun a => ⟨conjE E a, conj_mem hd hx a a.2⟩
      map_one' := Subtype.ext (by simp)
      map_mul' := fun a b => Subtype.ext (by simp)
      map_zero' := Subtype.ext (by simp)
      map_add' := fun a b => Subtype.ext (by simp)
      commutes' := fun q => Subtype.ext (by
        change conjE E ((algebraMap ℚ (Kx x) q : Kx x) : E) = ((algebraMap ℚ (Kx x) q : Kx x) : E)
        simp) }
  AlgEquiv.ofAlgHom c0 c0 (AlgHom.ext fun a => Subtype.ext (conj_conj' _))
    (AlgHom.ext fun a => Subtype.ext (conj_conj' _))

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem cK_coe {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (a : Kx x) :
    ((cK hd hx a : Kx x) : E) = conjE E a := rfl

/- English proof (translation)
Establish `hmem : x ∈ IntermediateField.adjoin ℚ {x}` using `IntermediateField.mem_adjoin_simple_self ℚ x`. Set `xk : Kx x` to `⟨x, hmem⟩`. Establish `hxk : xk ^ 2 = algebraMap ℚ (Kx x) (-(d : ℚ))` using `Subtype.ext (by`. Express the relevant statement in the definitionally equal form `x ^ 2 = algebraMap ℚ E (-(d : ℚ))`. Rewrite using `[hx]`.

Use the proof step `simp)`. Establish `hsq : (σ xk) ^ 2 = xk ^ 2` using `by rw [← map_pow, hxk, AlgEquiv.commutes]`. Establish `ext' : ∀ τ : Kx x ≃ₐ[ℚ] Kx x, σ xk = τ xk → σ = τ` using `fun τ h => by`. Establish `: (σ : Kx x →ₐ[ℚ] Kx x) = (τ : Kx x →ₐ[ℚ] Kx x)` using `IntermediateField.adjoin_algHom_ext ℚ (by`. Introduce `a ha`.

Take `rfl : a = x` from `Set.mem_singleton_iff.1 ha`. Conclude with `h)`. Conclude with `AlgEquiv.coe_algHom_injective this`. Break down `sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h` into its components or cases. Conclude with `Or.inl (ext' 1 h)`.

Use `Or.inr (ext' _ (h.trans (Subtype.ext ?_)))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `-x = conjE E x`. Rewrite using `[conj_alt_bis hd hx]`.
-/
private theorem aut_cases {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (σ : Kx x ≃ₐ[ℚ] Kx x) :
    σ = 1 ∨ σ = cK hd hx := by
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  let xk : Kx x := ⟨x, hmem⟩
  have hxk : xk ^ 2 = algebraMap ℚ (Kx x) (-(d : ℚ)) := Subtype.ext (by
    change x ^ 2 = algebraMap ℚ E (-(d : ℚ))
    rw [hx]; simp)
  have hsq : (σ xk) ^ 2 = xk ^ 2 := by rw [← map_pow, hxk, AlgEquiv.commutes]
  have ext' : ∀ τ : Kx x ≃ₐ[ℚ] Kx x, σ xk = τ xk → σ = τ := fun τ h => by
    have : (σ : Kx x →ₐ[ℚ] Kx x) = (τ : Kx x →ₐ[ℚ] Kx x) := IntermediateField.adjoin_algHom_ext ℚ (by
      intro a ha
      obtain rfl : a = x := Set.mem_singleton_iff.1 ha
      exact h)
    exact AlgEquiv.coe_algHom_injective this
  rcases sq_eq_sq_iff_eq_or_eq_neg.1 hsq with h | h
  · exact Or.inl (ext' 1 h)
  · refine Or.inr (ext' _ (h.trans (Subtype.ext ?_)))
    change -x = conjE E x
    rw [conj_alt_bis hd hx]

/- English proof (translation)
Introduce `h`. Establish `hmem : x ∈ IntermediateField.adjoin ℚ {x}` using `IntermediateField.mem_adjoin_simple_self ℚ x`. Establish `h1 : conjE E x = x` using `congrArg (fun σ : Kx x ≃ₐ[ℚ] Kx x => ((σ ⟨x, hmem⟩ : Kx x) : E)) h`. Rewrite `h1` using `[conj_alt_bis hd hx]`. Establish `h0 : x = 0`.

Establish `: (2 : E) * x = 0` using `by linear_combination -h1`. Simplify using `using this`. Rewrite `hx` using `[h0]`. Establish `: (d : E) = 0` using `by simpa using hx.symm`. Conclude with `hd.ne' (by exact_mod_cast this)`.
-/
private theorem cK_ne {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : cK hd hx ≠ 1 := by
  intro h
  have hmem : x ∈ IntermediateField.adjoin ℚ {x} := IntermediateField.mem_adjoin_simple_self ℚ x
  have h1 : conjE E x = x := congrArg (fun σ : Kx x ≃ₐ[ℚ] Kx x => ((σ ⟨x, hmem⟩ : Kx x) : E)) h
  rw [conj_alt_bis hd hx] at h1
  have h0 : x = 0 := by
    have : (2 : E) * x = 0 := by linear_combination -h1
    simpa using this
  rw [h0] at hx
  have : (d : E) = 0 := by simpa using hx.symm
  exact hd.ne' (by exact_mod_cast this)

/- English proof (translation)
Establish `hint : IsIntegral ℚ x` using `Algebra.IsIntegral.isIntegral x`. Establish `hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic` using `Polynomial.monic_X_pow_add_C _ (by norm_num)`. Establish `hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2` using `Polynomial.natDegree_X_pow_add_C`. Establish `hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ))`. Use `Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun q hq => ?_` and prove the remaining obligations.

Establish `hd' : (0 : ℚ) < d` using `by exact_mod_cast hd`. Simplify using `only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq`. Use polynomial arithmetic with `[sq_nonneg q]`. Establish `hmin : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ x` using `minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) hmonic`. Use `IntermediateField.adjoin.finrank hint` as an intermediate fact.

Rewrite `this` using `[← hmin, hdeg]`. Conclude with `this`.
-/
private theorem finrank_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    Module.finrank ℚ (Kx x) = 2 := by
  have hint : IsIntegral ℚ x := Algebra.IsIntegral.isIntegral x
  have hmonic : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).Monic := Polynomial.monic_X_pow_add_C _ (by norm_num)
  have hdeg : (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)).natDegree = 2 := Polynomial.natDegree_X_pow_add_C
  have hirr : Irreducible (Polynomial.X ^ 2 + Polynomial.C (d : ℚ)) := by
    refine Polynomial.irreducible_of_degree_le_three_of_not_isRoot (by rw [hdeg]; simp) fun q hq => ?_
    have hd' : (0 : ℚ) < d := by exact_mod_cast hd
    simp only [Polynomial.IsRoot, Polynomial.eval_add, Polynomial.eval_pow, Polynomial.eval_X, Polynomial.eval_C] at hq
    nlinarith [sq_nonneg q]
  have hmin : Polynomial.X ^ 2 + Polynomial.C (d : ℚ) = minpoly ℚ x :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hx]) hmonic
  have := IntermediateField.adjoin.finrank hint
  rw [← hmin, hdeg] at this
  exact this

/- English proof (translation)
Use extensionality with `σ`. Simplify using `using aut_cases hd hx σ`.
-/
private theorem univ_eq {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) :
    (Finset.univ : Finset (Kx x ≃ₐ[ℚ] Kx x)) = {1, cK hd hx} := by
  ext σ
  simpa using aut_cases hd hx σ

/- English proof (translation)
Use `IsGalois.of_card_aut_eq_finrank ℚ (Kx x) ?_` and prove the remaining obligations. Rewrite using `[finrank_K hd hx, Nat.card_eq_fintype_card, ← Finset.card_univ, univ_eq hd hx, Finset.card_pair (cK_ne hd hx).symm]`.
-/
private theorem isGalois_K {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) : IsGalois ℚ (Kx x) := by
  refine IsGalois.of_card_aut_eq_finrank ℚ (Kx x) ?_
  rw [finrank_K hd hx, Nat.card_eq_fintype_card, ← Finset.card_univ, univ_eq hd hx, Finset.card_pair (cK_ne hd hx).symm]

/- English proof (translation)
Establish `h` using `(GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).equalizer ((continuous_conjFin (conjE E)).comp continuous_finiteAdeleMap) (continuous_finiteAdeleMap (K := ℚ) (L := E)) (funext fun q => ?_)`. Conclude with `congrFun h a`. Simplify using `only [Function.comp_apply]`. Rewrite using `[finiteAdeleMap_algebraMap, conjFin_algebraMap]`. Simplify using the standard rewrite rules.
-/
private theorem conjFin_rat (a : Af ℚ) : conjFin (conjE E) (finiteAdeleMap ℚ E a) = finiteAdeleMap ℚ E a := by
  have h := (GroundTheory.Automorphic.AdelicGLn.denseRange_algebraMap_finiteAdeleRing ℚ).equalizer
    ((continuous_conjFin (conjE E)).comp continuous_finiteAdeleMap)
    (continuous_finiteAdeleMap (K := ℚ) (L := E)) (funext fun q => ?_)
  · exact congrFun h a
  · simp only [Function.comp_apply]
    rw [finiteAdeleMap_algebraMap, conjFin_algebraMap]
    simp

/- English proof (translation)
Set `Φ : 𝔸[Kx x] →+* Af E` to `(finiteAdeleMap (Kx x) E).comp ((RingHom.snd _ _).comp (adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x)).toRingHom)`. Set `Ψ : 𝔸[Kx x] →+* Af E` to `((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).comp (RingHom.snd _ _)`. Establish `h : Φ = Ψ`. Use `adeleRingHom_ext_rat (fun l => ?_) (fun a => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (algebraMap (Kx x) 𝔸[Kx x] l)).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E ((algebraMap (Kx x) 𝔸[Kx x] l).2))`.

Rewrite using `[adeleRingEquiv_algebraMap]`. Express the relevant statement in the definitionally equal form `finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) _) = conjFin (conjE E) (finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) l))`. Rewrite using `[finiteAdeleMap_algebraMap, finiteAdeleMap_algebraMap, conjFin_algebraMap]`. Both sides reduce to the same expression. Express the relevant statement in the definitionally equal form `finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (adeleMap ℚ (Kx x) a)).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E ((adeleMap ℚ (Kx x) a).2))`.

Rewrite using `[adeleRingEquiv_adeleMap_rat]`. Express the relevant statement in the definitionally equal form `finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2))`. Rewrite using `[finiteAdeleMap_finiteAdeleMap, conjFin_rat]`. Conclude with `congrArg (· y) h`.
-/
private theorem fin_conj {d : ℕ} {x : E} (hd : 0 < d) (hx : x ^ 2 = -(d : E)) (y : 𝔸[Kx x]) :
    finiteAdeleMap (Kx x) E ((cK hd hx • y).2) = conjFin (conjE E) (finiteAdeleMap (Kx x) E y.2) := by
  let Φ : 𝔸[Kx x] →+* Af E := (finiteAdeleMap (Kx x) E).comp
    ((RingHom.snd _ _).comp (adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x)).toRingHom)
  let Ψ : 𝔸[Kx x] →+* Af E := ((conjFin (conjE E)).comp (finiteAdeleMap (Kx x) E)).comp (RingHom.snd _ _)
  have h : Φ = Ψ := by
    refine adeleRingHom_ext_rat (fun l => ?_) (fun a => ?_)
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (algebraMap (Kx x) 𝔸[Kx x] l)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((algebraMap (Kx x) 𝔸[Kx x] l).2))
      rw [adeleRingEquiv_algebraMap]
      change finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) _) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (algebraMap (Kx x) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x)) l))
      rw [finiteAdeleMap_algebraMap, finiteAdeleMap_algebraMap, conjFin_algebraMap]
      rfl
    · change finiteAdeleMap (Kx x) E ((adeleRingEquiv ((cK hd hx : Kx x ≃ₐ[ℚ] Kx x) : Kx x ≃+* Kx x) (adeleMap ℚ (Kx x) a)).2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E ((adeleMap ℚ (Kx x) a).2))
      rw [adeleRingEquiv_adeleMap_rat]
      change finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2) =
        conjFin (conjE E) (finiteAdeleMap (Kx x) E (finiteAdeleMap ℚ (Kx x) a.2))
      rw [finiteAdeleMap_finiteAdeleMap, conjFin_rat]
  exact congrArg (· y) h

/- English proof (translation)
Introduce `E _ _ _ d x hd hx z`. Use `haveI := isGalois_K hd hx`. Set `y : IdeleGroup (Kx x)` to `Units.map (MonoidHom.inr (InfiniteAdeleRing (Kx x)) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x))) z`. Establish `h1` using `ideleEmbedding_ideleNorm (K := ℚ) y`. Establish `h2 : (∏ σ : Kx x ≃ₐ[ℚ] Kx x, σ • y) = y * cK hd hx • y`.

Rewrite using `[univ_eq hd hx, Finset.prod_pair (cK_ne hd hx).symm, one_smul]`. Rewrite `h1` using `[h2]`. Establish `h3` using `congrArg (fun u : IdeleGroup (Kx x) => ((u : 𝔸[Kx x]).2)) h1`. Establish `h4 : finiteAdeleMap ℚ (Kx x) ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ) = (z : Af (Kx x)) * ((cK hd hx • (y : 𝔸[Kx x])).2)` using `h3`. Establish `h5` using `congrArg (finiteAdeleMap (Kx x) E) h4`.

Rewrite `h5` using `[finiteAdeleMap_finiteAdeleMap, map_mul, fin_conj]`. Conclude with `h5.symm`.
-/
theorem UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.quadConj :
    UpperTheory.Gal.CertificateRingHomMap.ZetaNonvanishing₂.QuadConj := by
  intro E _ _ _ d x hd hx z
  haveI := isGalois_K hd hx
  let y : IdeleGroup (Kx x) := Units.map (MonoidHom.inr (InfiniteAdeleRing (Kx x)) (FiniteAdeleRing (𝓞 (Kx x)) (Kx x))) z
  have h1 := ideleEmbedding_ideleNorm (K := ℚ) y
  have h2 : (∏ σ : Kx x ≃ₐ[ℚ] Kx x, σ • y) = y * cK hd hx • y := by
    rw [univ_eq hd hx, Finset.prod_pair (cK_ne hd hx).symm, one_smul]
  rw [h2] at h1
  have h3 := congrArg (fun u : IdeleGroup (Kx x) => ((u : 𝔸[Kx x]).2)) h1
  have h4 : finiteAdeleMap ℚ (Kx x) ((fN ℚ (Kx x) z : (Af ℚ)ˣ) : Af ℚ) =
      (z : Af (Kx x)) * ((cK hd hx • (y : 𝔸[Kx x])).2) := h3
  have h5 := congrArg (finiteAdeleMap (Kx x) E) h4
  rw [finiteAdeleMap_finiteAdeleMap, map_mul, fin_conj] at h5
  exact h5.symm

end
