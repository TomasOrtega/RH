import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.UnitaryActions.ContinuousQuaternaryQuadraticForm

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host GlobalTheory.CuspRep UpperTheory.V UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open scoped Classical
open UpperTheory.ConvolutionTheory.R2

/- English proof (translation)
Set `m : F → F → E` to `fun u t => algebraMap F E u + algebraMap F E t * D.θ`. Establish `hm : ∀ u t : F, D.mkE (rt u) (rt t) = rt (m u t)` using `D.mkE_rt`. Set `M : Matrix (Fin 2) (Fin 2) E` to `!![m (ξ 1) 0, m (ξ 2) (ξ 3); m (ξ 2) (-ξ 3), m (ξ 0) 0]`. Establish `hM : D.herm (fun i => rt (ξ i)) = M.map (algebraMap E (A E))`. Establish `h0 : (0 : A F) = rt (0 : F)` using `(map_zero _).symm`.

Establish `hn : -(rt (ξ 3) : A F) = rt (-ξ 3)` using `(map_neg _ _).symm`. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Express the relevant statement in the definitionally equal form `D.mkE (rt (ξ 1)) 0 = rt (m (ξ 1) 0)`. Rewrite using `[h0, hm]`.

Conclude with `hm _ _`. Express the relevant statement in the definitionally equal form `D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (m (ξ 2) (-ξ 3))`. Rewrite using `[hn, hm]`. Express the relevant statement in the definitionally equal form `D.mkE (rt (ξ 0)) 0 = rt (m (ξ 0) 0)`. Rewrite using `[h0, hm]`.

Establish `hγ : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E))`. Use extensionality with `i j`. Conclude with `ratGL_apply 2 γ i j`. Establish `hs : D.star2 (ratGL E 2 γ).val = ((γ.val.map D.σ)ᵀ).map (algebraMap E (A E))`. Use extensionality with `i j`.

Rewrite using `[D.conjTransposeGal_apply, ratGL_apply]`. Conclude with `D.bar_rt _`. Set `Y : Matrix (Fin 2) (Fin 2) E` to `γ.val * M * (γ.val.map D.σ)ᵀ`. Establish `hY : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * D.star2 (ratGL E 2 γ).val = Y.map (algebraMap E (A E))`. Rewrite using `[hM, hs, hγ]`.

Simplify using `only [Y, Matrix.map_mul]`. Use `⟨![D.b.repr (Y 1 1) 0, D.b.repr (Y 0 0) 0, D.b.repr (Y 0 1) 0, D.b.repr (Y 0 1) 1], ?_⟩` and prove the remaining obligations. Rewrite using `[D.act_def, hY]`. Use `ext1 i`. Use `fin_cases i`.

Conclude with `D.co_rt _ _`. Conclude with `D.co_rt _ _`. Conclude with `D.co_rt _ _`. Conclude with `D.co_rt _ _`.
-/
private theorem act_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (γ : GL (Fin 2) E) (ξ : Fin 4 → F) :
    ∃ ξ' : Fin 4 → F, D.act (ratGL E 2 γ) (fun i => rt (ξ i)) = fun i => rt (ξ' i) := by
  let m : F → F → E := fun u t => algebraMap F E u + algebraMap F E t * D.θ
  have hm : ∀ u t : F, D.mkE (rt u) (rt t) = rt (m u t) := D.mkE_rt
  let M : Matrix (Fin 2) (Fin 2) E := !![m (ξ 1) 0, m (ξ 2) (ξ 3); m (ξ 2) (-ξ 3), m (ξ 0) 0]
  have hM : D.herm (fun i => rt (ξ i)) = M.map (algebraMap E (A E)) := by
    have h0 : (0 : A F) = rt (0 : F) := (map_zero _).symm
    have hn : -(rt (ξ 3) : A F) = rt (-ξ 3) := (map_neg _ _).symm
    ext i j
    fin_cases i <;> fin_cases j
    · change D.mkE (rt (ξ 1)) 0 = rt (m (ξ 1) 0)
      rw [h0, hm]
    · exact hm _ _
    · change D.mkE (rt (ξ 2)) (-rt (ξ 3)) = rt (m (ξ 2) (-ξ 3))
      rw [hn, hm]
    · change D.mkE (rt (ξ 0)) 0 = rt (m (ξ 0) 0)
      rw [h0, hm]
  have hγ : (ratGL E 2 γ).val = γ.val.map (algebraMap E (A E)) := by
    ext i j; exact ratGL_apply 2 γ i j
  have hs : D.star2 (ratGL E 2 γ).val = ((γ.val.map D.σ)ᵀ).map (algebraMap E (A E)) := by
    ext i j
    rw [D.conjTransposeGal_apply, ratGL_apply]
    exact D.bar_rt _
  let Y : Matrix (Fin 2) (Fin 2) E := γ.val * M * (γ.val.map D.σ)ᵀ
  have hY : (ratGL E 2 γ).val * D.herm (fun i => rt (ξ i)) * D.star2 (ratGL E 2 γ).val =
      Y.map (algebraMap E (A E)) := by
    rw [hM, hs, hγ]
    simp only [Y, Matrix.map_mul]
  refine ⟨![D.b.repr (Y 1 1) 0, D.b.repr (Y 0 0) 0, D.b.repr (Y 0 1) 0, D.b.repr (Y 0 1) 1], ?_⟩
  rw [D.act_def, hY]
  ext1 i
  fin_cases i
  · exact D.co_rt _ _
  · exact D.co_rt _ _
  · exact D.co_rt _ _
  · exact D.co_rt _ _

/- English proof (translation)
Establish `h : ∀ j : Fin 4, ∃ ξ' : Fin 4 → F, D.act (ratGL E 2 γ) (Pi.single j 1) = fun i => rt (ξ' i)` using `fun j => by`. Take `⟨ξ', h⟩` from `act_rat D γ (Pi.single j 1)`. Use `⟨ξ', Eq.trans ?_ h⟩` and prove the remaining obligations. Use `congr 1`. Use `ext1 i`.

Distinguish the cases in `hij : i = j`. Substitute `hij` using the available equality. Simplify using the standard rewrite rules. Simplify using `[Pi.single_eq_of_ne hij]`. Use `choose c hc using h`.

Use `⟨Matrix.of fun i j => c j i, ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `D.act (ratGL E 2 γ) (Pi.single j 1) i = rt (c j i)`. Rewrite using `[hc]`.
-/
private theorem actM_rat {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
    (D : Dat F E) (γ : GL (Fin 2) E) :
    ∃ N : Matrix (Fin 4) (Fin 4) F, D.actM (ratGL E 2 γ) = N.map (algebraMap F (A F)) := by
  have h : ∀ j : Fin 4, ∃ ξ' : Fin 4 → F,
      D.act (ratGL E 2 γ) (Pi.single j 1) = fun i => rt (ξ' i) := fun j => by
    obtain ⟨ξ', h⟩ := act_rat D γ (Pi.single j 1)
    refine ⟨ξ', Eq.trans ?_ h⟩
    congr 1
    ext1 i
    by_cases hij : i = j
    · subst hij; simp
    · simp [Pi.single_eq_of_ne hij]
  choose c hc using h
  refine ⟨Matrix.of fun i j => c j i, ?_⟩
  ext i j
  change D.act (ratGL E 2 γ) (Pi.single j 1) i = rt (c j i)
  rw [hc]

/- English proof (translation)
Introduce `F E _ _ _ _ _ D γ`. Use `haveI := AdeleBaseChange.nontrivial_adeleRing F`. Take `⟨N₀, h₀⟩` from `actM_rat D γ`. Take `⟨N₁, h₁⟩` from `actM_rat D γ⁻¹`. Establish `inj : Function.Injective (algebraMap F (A F))` using `(algebraMap F (A F)).injective`.

Establish `minj : Function.Injective fun X : Matrix (Fin 4) (Fin 4) F => X.map (algebraMap F (A F))` using `Matrix.map_injective inj`. Establish `one : (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F)) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Establish `e₀₁ : N₀ * N₁ = 1` using `minj (by`. Express the relevant statement in the definitionally equal form `(N₀ * N₁).map (algebraMap F (A F)) = (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F))`. Rewrite using `[Matrix.map_mul, ← h₀, ← h₁, ← D.actM_mul, ← map_mul, mul_inv_cancel, map_one, D.actM_one, one])`.

Establish `e₁₀ : N₁ * N₀ = 1` using `minj (by`. Express the relevant statement in the definitionally equal form `(N₁ * N₀).map (algebraMap F (A F)) = (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F))`. Rewrite using `[Matrix.map_mul, ← h₀, ← h₁, ← D.actM_mul, ← map_mul, inv_mul_cancel, map_one, D.actM_one, one])`. Use `⟨⟨N₀, N₁, e₀₁, e₁₀⟩, h₀, fun ξ => ?_⟩` and prove the remaining obligations. Rewrite using `[← D.actM_mulVec, h₀]`.

Use function extensionality and compare the values at `i`. Conclude with `(RingHom.map_mulVec (algebraMap F (A F)) N₀ ξ i).symm`.
-/
theorem UpperTheory.ConvolutionTheory.R2.actRat :
    ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (D : Dat F E) (γ : GL (Fin 2) E),
      ∃ N : GL (Fin 4) F, D.actM (ratGL E 2 γ) = N.val.map (algebraMap F (A F)) ∧
        ∀ ξ : Fin 4 → F, D.act (ratGL E 2 γ) (fun i => rt (ξ i)) = fun i => rt ((N.val *ᵥ ξ) i) := by
  intro F E _ _ _ _ _ D γ
  haveI := AdeleBaseChange.nontrivial_adeleRing F
  obtain ⟨N₀, h₀⟩ := actM_rat D γ
  obtain ⟨N₁, h₁⟩ := actM_rat D γ⁻¹
  have inj : Function.Injective (algebraMap F (A F)) := (algebraMap F (A F)).injective
  have minj : Function.Injective fun X : Matrix (Fin 4) (Fin 4) F => X.map (algebraMap F (A F)) :=
    Matrix.map_injective inj
  have one : (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F)) = 1 :=
    Matrix.map_one _ (map_zero _) (map_one _)
  have e₀₁ : N₀ * N₁ = 1 := minj (by
    change (N₀ * N₁).map (algebraMap F (A F)) = (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F))
    rw [Matrix.map_mul, ← h₀, ← h₁, ← D.actM_mul, ← map_mul, mul_inv_cancel, map_one, D.actM_one, one])
  have e₁₀ : N₁ * N₀ = 1 := minj (by
    change (N₁ * N₀).map (algebraMap F (A F)) = (1 : Matrix (Fin 4) (Fin 4) F).map (algebraMap F (A F))
    rw [Matrix.map_mul, ← h₀, ← h₁, ← D.actM_mul, ← map_mul, inv_mul_cancel, map_one, D.actM_one, one])
  refine ⟨⟨N₀, N₁, e₀₁, e₁₀⟩, h₀, fun ξ => ?_⟩
  rw [← D.actM_mulVec, h₀]
  funext i
  exact (RingHom.map_mulVec (algebraMap F (A F)) N₀ ξ i).symm
