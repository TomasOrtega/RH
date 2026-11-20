import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.CharacterNorms.ThInf

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.RankTwoDescent UpperTheory.ConvolutionTheory.RankTwoDescent.TA
open UpperTheory.ConvolutionTheory.R2.G (FS2 nE)
open scoped Classical

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem gln_val {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E)).val = !![1, b; 0, 1] := rfl

/- English proof (translation)
Rewrite using `[inv_eq_iff_mul_eq_one]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[Units.val_mul, gln_val, gln_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]`.
-/
private theorem nU_inv {E : Type} [Field E] [NumberField E] (b : A E) :
    (gl (nU b) : GL (Fin 2) (A E))⁻¹ = gl (nU (-b)) := by
  rw [inv_eq_iff_mul_eq_one]
  refine Units.ext ?_
  rw [Units.val_mul, gln_val, gln_val]
  ext i j
  fin_cases i <;> fin_cases j <;> simp [Matrix.mul_apply, Fin.sum_univ_two]

/- English proof (translation)
Establish `hv : ∀ g : A E → A E, Continuous g → Continuous fun b : A E => ((gl (nU (g b)) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E))`. Introduce `g hg`. Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact hg | exact continuous_const`. Use `Units.continuous_iff.2 ⟨hv id continuous_id, ?_⟩` and prove the remaining obligations.

Simplify using `only [nU_inv]`. Conclude with `hv _ continuous_neg`.
-/
private theorem cont_n {E : Type} [Field E] [NumberField E] :
    Continuous fun b : A E => (gl (nU b) : GL (Fin 2) (A E)) := by
  have hv : ∀ g : A E → A E, Continuous g →
      Continuous fun b : A E => ((gl (nU (g b)) : GL (Fin 2) (A E)) : Matrix (Fin 2) (Fin 2) (A E)) := by
    intro g hg
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [nU] <;> first | exact hg | exact continuous_const
  refine Units.continuous_iff.2 ⟨hv id continuous_id, ?_⟩
  simp only [nU_inv]
  exact hv _ continuous_neg

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `p ((gl (nU z) : GL (Fin 2) (A E)).val i j) = (1 : Matrix (Fin 2) (Fin 2) S) i j`. Rewrite using `[gln_val]`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [hz]`.
-/
private theorem map_unipotent_eq_one {E S : Type} [Field E] [NumberField E] [CommRing S] (p : A E →+* S) (z : A E) (hz : p z = 0) :
    Matrix.GeneralLinearGroup.map p (gl (nU z)) = 1 := by
  refine Units.ext ?_
  ext i j
  change p ((gl (nU z) : GL (Fin 2) (A E)).val i j) = (1 : Matrix (Fin 2) (Fin 2) S) i j
  rw [gln_val]
  fin_cases i <;> fin_cases j <;> simp [hz]

/- English proof (translation)
Establish `h : pInf E (AdeleBaseChange.adeleMap ℚ E ((0, x) : A ℚ)) = 0`. Express the relevant statement in the definitionally equal form `(infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing ℚ)) = 0`. Rewrite using `[map_zero, map_zero]`. Simplify using `[Dat.mkE, h]`.
-/
private theorem pInf_mk {E : Type} [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (x : FiniteAdeleRing (𝓞 ℚ) ℚ) :
    pInf E (D.mkE 0 ((0, x) : A ℚ)) = 0 := by
  have h : pInf E (AdeleBaseChange.adeleMap ℚ E ((0, x) : A ℚ)) = 0 := by
    change (infEq E).symm (GroundTheory.Global.InfinitePlace.infiniteAdeleRingMap (0 : InfiniteAdeleRing ℚ)) = 0
    rw [map_zero, map_zero]
  simp [Dat.mkE, h]

/- English proof (translation)
Establish `h : Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((0, x) : A ℚ)` using `continuous_const.prodMk continuous_id`. Unfold `Dat.mkE`. Conclude with `continuous_const.add ((AdeleBaseChange.continuous_adeleMap.comp h).mul continuous_const)`.
-/
private theorem cont_mk {E : Type} [Field E] [NumberField E] (D : Dat ℚ E) :
    Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => D.mkE 0 ((0, x) : A ℚ) := by
  have h : Continuous fun x : FiniteAdeleRing (𝓞 ℚ) ℚ => ((0, x) : A ℚ) :=
    continuous_const.prodMk continuous_id
  unfold Dat.mkE
  exact continuous_const.add ((AdeleBaseChange.continuous_adeleMap.comp h).mul continuous_const)

/- English proof (translation)
Introduce `E _ _ _ D f hf C hC`. Set `m : FiniteAdeleRing (𝓞 ℚ) ℚ → GL (Fin 2) (A E)` to `fun x => gl (nU (D.mkE 0 ((0, x) : A ℚ)))`. Establish `hm : Continuous m` using `cont_n.comp (cont_mk D)`. Establish `hm0 : m 0 = 1`. Establish `h0 : D.mkE 0 ((0, 0) : A ℚ) = 0`.

Establish `h : D.mkE 0 ((0, 0) : A ℚ) = D.mkE 0 (0 : A ℚ)` using `rfl`. Rewrite using `[h]`. Unfold `Dat.mkE`. Rewrite using `[map_zero, zero_mul, add_zero]`. Express the relevant statement in the definitionally equal form `gl (nU (D.mkE 0 ((0, 0) : A ℚ))) = 1`.

Rewrite using `[h0]`. Use `Units.ext ?_` and prove the remaining obligations. Rewrite using `[gln_val]`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp`.

Set `Φ : FiniteAdeleRing (𝓞 ℚ) ℚ × GL (Fin 2) (A E) → GL (Fin 2) (Af E)` to `fun p => Matrix.GeneralLinearGroup.map (pFin E) (p.2⁻¹ * m p.1 * p.2)`. Establish `hΦ : Continuous Φ` using `(Continuous.units_map _ (continuous_id.matrix_map continuous_snd)).comp ((continuous_snd.inv.mul (hm.comp continuous_fst)).mul continuous_snd)`. Establish `hO : IsOpen (Φ ⁻¹' {k | finRep E 2 k f = f})` using `hf.level.preimage hΦ`. Establish `hsub : ({0} : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) ×ˢ C ⊆ Φ ⁻¹' {k | finRep E 2 k f = f}`. Introduce and unpack `⟨x, k⟩ ⟨hx, -⟩`.

Establish `hx0 : x = 0` using `hx`. Substitute `hx0` using the available equality. Establish `e : Φ (0, k) = 1`. Express the relevant statement in the definitionally equal form `Matrix.GeneralLinearGroup.map (pFin E) (k⁻¹ * m 0 * k) = 1`. Rewrite using `[hm0, mul_one, inv_mul_cancel, map_one]`.

Express the relevant statement in the definitionally equal form `finRep E 2 (Φ (0, k)) f = f`. Rewrite using `[e, map_one]`. Both sides reduce to the same expression. Take `⟨U, V, hU, hV, h0U, hCV, hUV⟩` from `generalized_tube_lemma isCompact_singleton hC hO hsub`. Establish `h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ U` using `h0U rfl`.

Establish `key : ∀ᶠ d in 𝓝 (0 : FiniteAdeleRing (𝓞 ℚ) ℚ), ∀ z ∈ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), d * z ∈ U` using `(isCompact_integralFiniteAdeles ℚ).eventually_forall_of_forall_eventually fun z _ => (hU.preimage (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using h0)`. Take `⟨n, hn⟩` from `((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists`. Use `⟨n.factorial, n.factorial_pos, fun k hk b hb G => ?_⟩` and prove the remaining obligations. Establish `hx` using `hn b hb`. Establish `hS : finRep E 2 (Φ (_, k)) f = f` using `hUV (Set.mk_mem_prod hx (hCV hk))`.

Establish `hy : finGL E 2 (Φ ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b, k)) = k⁻¹ * m ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) * k`. Use `ga_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[pInf_finGL, map_mul, map_mul, map_unipotent_eq_one _ _ (pInf_mk D _), mul_one, ← map_mul, inv_mul_cancel, map_one]`. Rewrite using `[pFin_finGL]`. Establish `e` using `congrArg (fun ψ : Sm E 2 => ψ.1 (G * k)) hS`.

Express the relevant statement in the definitionally equal form `f.1 (G * k * finGL E 2 _) = f.1 (G * k) at e`. Rewrite `e` using `[hy]`. Rewrite using `[← e]`. Express the relevant statement in the definitionally equal form `f.1 (G * (m _ * k)) = _`. Use `congr 1`.

Use `group`.
-/
theorem UpperTheory.exists_level_unipotent_invariance_automorphicForm :
    ∀ (E : Type) [Field E] [NumberField E] [IsTotallyComplex E] (D : Dat ℚ E) (f : Sm E 2), IsAutForm f →
        ∀ C : Set (GL (Fin 2) (A E)), IsCompact C → ∃ N : ℕ, 0 < N ∧ ∀ k ∈ C, ∀ b : FiniteAdeleRing (𝓞 ℚ) ℚ,
          (∀ v, b v ∈ v.adicCompletionIntegers ℚ) → ∀ G, f.1 (G * (gl (nU (D.mkE 0 ((0, (N : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) : A ℚ))) * k)) = f.1 (G * k) := by
  intro E _ _ _ D f hf C hC
  let m : FiniteAdeleRing (𝓞 ℚ) ℚ → GL (Fin 2) (A E) := fun x => gl (nU (D.mkE 0 ((0, x) : A ℚ)))
  have hm : Continuous m := cont_n.comp (cont_mk D)
  have hm0 : m 0 = 1 := by
    have h0 : D.mkE 0 ((0, 0) : A ℚ) = 0 := by
      have h : D.mkE 0 ((0, 0) : A ℚ) = D.mkE 0 (0 : A ℚ) := rfl
      rw [h]
      unfold Dat.mkE
      rw [map_zero, zero_mul, add_zero]
    change gl (nU (D.mkE 0 ((0, 0) : A ℚ))) = 1
    rw [h0]
    refine Units.ext ?_
    rw [gln_val]
    ext i j
    fin_cases i <;> fin_cases j <;> simp
  let Φ : FiniteAdeleRing (𝓞 ℚ) ℚ × GL (Fin 2) (A E) → GL (Fin 2) (Af E) :=
    fun p => Matrix.GeneralLinearGroup.map (pFin E) (p.2⁻¹ * m p.1 * p.2)
  have hΦ : Continuous Φ :=
    (Continuous.units_map _ (continuous_id.matrix_map continuous_snd)).comp ((continuous_snd.inv.mul (hm.comp continuous_fst)).mul continuous_snd)
  have hO : IsOpen (Φ ⁻¹' {k | finRep E 2 k f = f}) := hf.level.preimage hΦ
  have hsub : ({0} : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)) ×ˢ C ⊆ Φ ⁻¹' {k | finRep E 2 k f = f} := by
    rintro ⟨x, k⟩ ⟨hx, -⟩
    have hx0 : x = 0 := hx
    subst hx0
    have e : Φ (0, k) = 1 := by
      change Matrix.GeneralLinearGroup.map (pFin E) (k⁻¹ * m 0 * k) = 1
      rw [hm0, mul_one, inv_mul_cancel, map_one]
    change finRep E 2 (Φ (0, k)) f = f
    rw [e, map_one]
    rfl
  obtain ⟨U, V, hU, hV, h0U, hCV, hUV⟩ := generalized_tube_lemma isCompact_singleton hC hO hsub
  have h0 : (0 : FiniteAdeleRing (𝓞 ℚ) ℚ) ∈ U := h0U rfl
  have key : ∀ᶠ d in 𝓝 (0 : FiniteAdeleRing (𝓞 ℚ) ℚ),
      ∀ z ∈ (integralFiniteAdeles (𝓞 ℚ) ℚ : Set (FiniteAdeleRing (𝓞 ℚ) ℚ)), d * z ∈ U :=
    (isCompact_integralFiniteAdeles ℚ).eventually_forall_of_forall_eventually fun z _ =>
      (hU.preimage (continuous_fst.mul continuous_snd)).mem_nhds (by simpa using h0)
  obtain ⟨n, hn⟩ := ((GlobalTheory.AdelicFactorial.tendsto_factorial_finiteAdele ℚ).eventually key).exists
  refine ⟨n.factorial, n.factorial_pos, fun k hk b hb G => ?_⟩
  have hx := hn b hb
  have hS : finRep E 2 (Φ (_, k)) f = f := hUV (Set.mk_mem_prod hx (hCV hk))
  have hy : finGL E 2 (Φ ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b, k)) =
      k⁻¹ * m ((n.factorial : FiniteAdeleRing (𝓞 ℚ) ℚ) * b) * k := by
    refine ga_ext ?_ ?_
    · rw [pInf_finGL, map_mul, map_mul, map_unipotent_eq_one _ _ (pInf_mk D _), mul_one, ← map_mul, inv_mul_cancel, map_one]
    · rw [pFin_finGL]
  have e := congrArg (fun ψ : Sm E 2 => ψ.1 (G * k)) hS
  change f.1 (G * k * finGL E 2 _) = f.1 (G * k) at e
  rw [hy] at e
  rw [← e]
  change f.1 (G * (m _ * k)) = _
  congr 1
  group
