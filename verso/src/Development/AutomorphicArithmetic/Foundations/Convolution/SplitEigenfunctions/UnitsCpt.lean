import Development.AutomorphicArithmetic.Foundations.Convolution.SplitEigenfunctions.ThetaLiftEqAnisotropicPart
import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.IsotypicQuotients.NormWfLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.CmBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.ReductionIdele

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2 UpperTheory.ConvolutionTheory.R2.Ff UpperTheory.ConvolutionTheory.RankTwoDescent
open scoped Classical

open GroundTheory.Automorphic GroundTheory.Automorphic.Reduction GroundTheory.Automorphic.AutomorphicForm

section SlopeTestRemainingChoices

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem vn (q : A F) : (nU q).val = !![1, q; 0, 1] := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem vm (a : (A F)ˣ) : (mD a).val = !![(a : A F), 0; 0, ((a⁻¹ : (A F)ˣ) : A F)] := rfl

/- English proof (translation)
The claim follows from `map_mul _ _ _`.
-/
private theorem gmul (x y : G1 F) : gl (x * y) = gl x * gl y := map_mul _ _ _

/- English proof (translation)
Use `Units.continuous_iff.2 ⟨?_, ?_⟩` and prove the remaining obligations. Apply the tactic sequence `refine continuous_matrix fun i j => ?_ fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`. Establish `e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q))` using `fun q => inv_eq_of_mul_eq_one_right (Units.ext (by`. Apply the tactic sequence `ext i j; fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two]))`. Simplify using `only [e]`.

Use `continuous_matrix fun i j => ?_` and prove the remaining obligations. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop`.
-/
private theorem cont_n : Continuous fun q : A F => gl (nU q) := by
  refine Units.continuous_iff.2 ⟨?_, ?_⟩
  · refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop
  · have e : ∀ q : A F, (gl (nU q))⁻¹ = gl (nU (-q)) := fun q => inv_eq_of_mul_eq_one_right (Units.ext (by
      ext i j; fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two]))
    simp only [e]
    refine continuous_matrix fun i j => ?_
    fin_cases i <;> fin_cases j <;> simp [vn] <;> fun_prop

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h0, h1, h]`.
-/
private theorem tri (Y : GL (Fin 2) (A F)) (t₀ t₁ : (A F)ˣ) (h0 : Y.val 0 0 = t₀) (h1 : Y.val 1 1 = t₁) (h : Y.val 1 0 = 0) :
    Y = gl (nU (Y.val 0 1 * ((t₁⁻¹ : (A F)ˣ) : A F))) * diagUnits 2 ![t₀, t₁] := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h0, h1, h]

/- English proof (translation)
Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]`.
-/
private theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Use `⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap F (A F) (!![1, k; 0, 1] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [vn]`.
-/
private theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Use `⟨Matrix.SpecialLinearGroup.toGL ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩` and prove the remaining obligations. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `algebraMap F (A F) (!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] i j) = _`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Both sides reduce to the same expression.

Simplify using `[vm]`. Simplify using `[vm]`. Both sides reduce to the same expression.
-/
private theorem rat_m (c : Fˣ) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (mD (IdeleGroup.diagonal F c)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![(c : F), 0; 0, ((c⁻¹ : Fˣ) : F)] i j) = _
  fin_cases i <;> fin_cases j
  · rfl
  · simp [vm]
  · simp [vm]
  · rfl

/- English proof (translation)
Set `Q : Set (A F)` to `⋃ i : Fin 2, ((fun β : GL (Fin 2) (A F) => β.val i i) '' C ∪ (fun β : GL (Fin 2) (A F) => (β⁻¹).val i i) '' C)`. Establish `hQ : IsCompact Q` using `isCompact_iUnion fun i => (hC.image (Units.continuous_val.matrix_elem i i)).union (hC.image (Units.continuous_coe_inv.matrix_elem i i))`. Use `⟨Units.embedProduct _ ⁻¹' (Q ×ˢ (MulOpposite.op '' Q)), Units.isClosedEmbedding_embedProduct.isCompact_preimage (hQ.prod (hQ.image MulOpposite.continuous_op)), fun β hβ hb i => ?_⟩` and prove the remaining obligations. Establish `h1 : β.val 1 0 = 0` using `hb (by decide : (0 : Fin 2) < 1)`. Establish `h2 : (β⁻¹).val 1 0 = 0` using `(adelicBorel.inv_mem hb) (by decide : (0 : Fin 2) < 1)`.

Establish `h3 : β.val i i * (β⁻¹).val i i = 1`. Use `congrFun (congrFun β.mul_inv i) i` as an intermediate fact. Rewrite `this` using `[Matrix.mul_apply, Fin.sum_univ_two]`. Use `fin_cases i`. Simplify `this` using `[-Matrix.coe_units_inv, h2]`.

Simplify `this` using `[-Matrix.coe_units_inv, h1]`. Conclude with `⟨⟨β.val i i, (β⁻¹).val i i, h3, by rw [mul_comm]; exact h3⟩, ⟨Set.mem_iUnion.2 ⟨i, Or.inl ⟨β, hβ, rfl⟩⟩, _, Set.mem_iUnion.2 ⟨i, Or.inr ⟨β, hβ, rfl⟩⟩, rfl⟩, rfl⟩`.
-/
private theorem units_cpt {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ U : Set (A F)ˣ, IsCompact U ∧ ∀ β ∈ C, β ∈ adelicBorel (K := F) (n := 2) → ∀ i, ∃ u ∈ U, (u : A F) = β.val i i := by
  let Q : Set (A F) := ⋃ i : Fin 2, ((fun β : GL (Fin 2) (A F) => β.val i i) '' C ∪ (fun β : GL (Fin 2) (A F) => (β⁻¹).val i i) '' C)
  have hQ : IsCompact Q := isCompact_iUnion fun i =>
    (hC.image (Units.continuous_val.matrix_elem i i)).union
      (hC.image (Units.continuous_coe_inv.matrix_elem i i))
  refine ⟨Units.embedProduct _ ⁻¹' (Q ×ˢ (MulOpposite.op '' Q)), Units.isClosedEmbedding_embedProduct.isCompact_preimage
    (hQ.prod (hQ.image MulOpposite.continuous_op)), fun β hβ hb i => ?_⟩
  have h1 : β.val 1 0 = 0 := hb (by decide : (0 : Fin 2) < 1)
  have h2 : (β⁻¹).val 1 0 = 0 := (adelicBorel.inv_mem hb) (by decide : (0 : Fin 2) < 1)
  have h3 : β.val i i * (β⁻¹).val i i = 1 := by
    have := congrFun (congrFun β.mul_inv i) i
    rw [Matrix.mul_apply, Fin.sum_univ_two] at this
    fin_cases i
    · simpa [-Matrix.coe_units_inv, h2] using this
    · simpa [-Matrix.coe_units_inv, h1] using this
  exact ⟨⟨β.val i i, (β⁻¹).val i i, h3, by rw [mul_comm]; exact h3⟩,
    ⟨Set.mem_iUnion.2 ⟨i, Or.inl ⟨β, hβ, rfl⟩⟩, _, Set.mem_iUnion.2 ⟨i, Or.inr ⟨β, hβ, rfl⟩⟩, rfl⟩, rfl⟩

/- English proof (translation)
Take `⟨U, hU, hUm⟩` from `units_cpt (hC.mul (isCompact_maxCompact (K := F) (n := 2)))`. Take `⟨S, hS, hSm⟩` from `exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1`. Take `⟨Q₀, hQ₀, hQ⟩` from `exists_isCompact_forall_exists_sub_mem F`. Establish `hQc` using `hQ₀.prod (isCompact_integralFiniteAdeles F)`. Set `P : A F × (A F)ˣ × (A F)ˣ × (A F)ˣ → GL (Fin 2) (A F)` to `fun p => gl (nU p.1) * diagUnits 2 ![p.2.1 * p.2.2.1, p.2.1⁻¹ * p.2.2.2]`.

Apply the tactic sequence `have hP : Continuous P := (cont_n.comp continuous_fst).mul ((continuous_diagUnits (K := F) 2).comp (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop))`. Use `⟨P '' _, (hQc.prod (hS.prod (hU.prod hU))).image hP, ?_, fun b a k hk s hs hsa => ?_⟩` and prove the remaining obligations. Introduce and unpack `_ ⟨p, -, rfl⟩`. Use `mul_mem ?_ (diagUnits_mem_adelicBorel _ _)` and prove the remaining obligations. Introduce `i j hij`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp_all [vn]`. Take `⟨β, hβ, kk, hkk, rfl⟩` from `exists_adelicBorel_mul_maxCompact (K := F) (n := 2) k`. Establish `hβC` using `(mul_inv_cancel_right β kk) ▸ Set.mul_mem_mul hk (show kk⁻¹ ∈ ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (GL (Fin 2) (A F))) from inv_mem hkk)`. Take `⟨u₀, hu₀, e₀⟩` from `hUm β hβC hβ 0`. Take `⟨u₁, hu₁, e₁⟩` from `hUm β hβC hβ 1`.

Establish `h1 : β.val 1 0 = 0` using `hβ (by decide : (0 : Fin 2) < 1)`. Use `set p : (A F)ˣ := posIdele s hs with hp`. Establish `hm : (IdeleGroup.ideleModule F (a * p⁻¹) : ℝ) = 1`. Establish `: IdeleGroup.ideleModule F a = IdeleGroup.ideleModule F p` using `Subtype.ext (by rw [hp, ideleModule_posIdele, hsa]; rfl)`. Rewrite using `[map_mul, map_inv, this, mul_inv_cancel]`.

Both sides reduce to the same expression. Take `⟨c, hc⟩` from `hSm (a * p⁻¹) hm.ge hm.le`. Use `set g : (A F)ˣ := IdeleGroup.diagonal F c with hg`. Use `set Y := gl (mD g) * (gl (nU b * mD a) * β) with hY`. Establish `hY'` using `tri Y (g * a * u₀) ((g * a)⁻¹ * u₁) (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1, ← e₀, mul_assoc]) (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, ← e₁, mul_assoc, mul_left_comm]) (by sim …`.

Use `set e := Y.val 0 1 * ((((g * a)⁻¹ * u₁)⁻¹ : (A F)ˣ) : A F)`. Take `⟨ξ, hξ⟩` from `hQ e`. Take `⟨γ, hγ⟩` from `rat_n ξ`. Take `⟨γ', hγ'⟩` from `rat_m c`. Use `⟨γ, γ'⁻¹, _, ⟨(e - rt ξ, g * (a * p⁻¹), u₀, u₁), ⟨hξ, hc, hu₀, hu₁⟩, rfl⟩, kk, hkk, ?_⟩` and prove the remaining obligations.

Establish `hd : diagUnits 2 ![g * a * u₀, (g * a)⁻¹ * u₁] = diagUnits 2 ![g * (a * p⁻¹) * u₀, (g * (a * p⁻¹))⁻¹ * u₁] * diagUnits 2 ![p, p⁻¹]`. Rewrite using `[← map_mul]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Apply the tactic sequence `fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]`.

Rewrite using `[map_inv, eq_inv_mul_iff_mul_eq, hγ, hγ', ← hg, ← mul_assoc _ β, ← mul_assoc, ← hY, hY', hd]`. Establish `: gl (nU e) = gl (nU (rt ξ)) * gl (nU (e - rt ξ))` using `by rw [← n_add]; congr 2; ring`. Rewrite using `[this]`. Simplify using `only [P, mul_assoc]`.
-/
private theorem siegel {C : Set (GL (Fin 2) (A F))} (hC : IsCompact C) :
    ∃ ω : Set (GL (Fin 2) (A F)), IsCompact ω ∧ ω ⊆ (adelicBorel (K := F) (n := 2) : Subgroup _) ∧
      ∀ (b : A F) (a : (A F)ˣ), ∀ k ∈ C, ∀ (s : ℝ) (hs : 0 < s), s ^ Module.finrank ℚ F = ab a →
        ∃ γ γ' : GL (Fin 2) F, ∃ y ∈ ω, ∃ kk ∈ maxCompact (K := F) (n := 2), gl (nU b * mD a) * k =
          ratGL F 2 γ' * (ratGL F 2 γ * (y * diagUnits 2 ![posIdele s hs, (posIdele s hs)⁻¹] * kk)) := by
  obtain ⟨U, hU, hUm⟩ := units_cpt (hC.mul (isCompact_maxCompact (K := F) (n := 2)))
  obtain ⟨S, hS, hSm⟩ := exists_isCompact_mul_mem_of_ideleModule_mem_Icc (K := F) one_pos 1
  obtain ⟨Q₀, hQ₀, hQ⟩ := exists_isCompact_forall_exists_sub_mem F
  have hQc := hQ₀.prod (isCompact_integralFiniteAdeles F)
  let P : A F × (A F)ˣ × (A F)ˣ × (A F)ˣ → GL (Fin 2) (A F) := fun p =>
    gl (nU p.1) * diagUnits 2 ![p.2.1 * p.2.2.1, p.2.1⁻¹ * p.2.2.2]
  have hP : Continuous P := (cont_n.comp continuous_fst).mul ((continuous_diagUnits (K := F) 2).comp
    (continuous_pi fun i => by fin_cases i <;> simp <;> fun_prop))
  refine ⟨P '' _, (hQc.prod (hS.prod (hU.prod hU))).image hP, ?_, fun b a k hk s hs hsa => ?_⟩
  · rintro _ ⟨p, -, rfl⟩
    refine mul_mem ?_ (diagUnits_mem_adelicBorel _ _)
    intro i j hij
    fin_cases i <;> fin_cases j <;> simp_all [vn]
  obtain ⟨β, hβ, kk, hkk, rfl⟩ := exists_adelicBorel_mul_maxCompact (K := F) (n := 2) k
  have hβC := (mul_inv_cancel_right β kk) ▸ Set.mul_mem_mul hk (show kk⁻¹ ∈ ((maxCompact (K := F) (n := 2) : Subgroup _) : Set (GL (Fin 2) (A F))) from inv_mem hkk)
  obtain ⟨u₀, hu₀, e₀⟩ := hUm β hβC hβ 0
  obtain ⟨u₁, hu₁, e₁⟩ := hUm β hβC hβ 1
  have h1 : β.val 1 0 = 0 := hβ (by decide : (0 : Fin 2) < 1)
  set p : (A F)ˣ := posIdele s hs with hp
  have hm : (IdeleGroup.ideleModule F (a * p⁻¹) : ℝ) = 1 := by
    have : IdeleGroup.ideleModule F a = IdeleGroup.ideleModule F p :=
      Subtype.ext (by rw [hp, ideleModule_posIdele, hsa]; rfl)
    rw [map_mul, map_inv, this, mul_inv_cancel]; rfl
  obtain ⟨c, hc⟩ := hSm (a * p⁻¹) hm.ge hm.le
  set g : (A F)ˣ := IdeleGroup.diagonal F c with hg
  set Y := gl (mD g) * (gl (nU b * mD a) * β) with hY
  have hY' := tri Y (g * a * u₀) ((g * a)⁻¹ * u₁)
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1, ← e₀, mul_assoc])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, ← e₁, mul_assoc, mul_left_comm])
    (by simp [hY, gmul, vn, vm, Matrix.vecMul, dotProduct, Matrix.mul_apply, Fin.sum_univ_two, h1])
  set e := Y.val 0 1 * ((((g * a)⁻¹ * u₁)⁻¹ : (A F)ˣ) : A F)
  obtain ⟨ξ, hξ⟩ := hQ e
  obtain ⟨γ, hγ⟩ := rat_n ξ
  obtain ⟨γ', hγ'⟩ := rat_m c
  refine ⟨γ, γ'⁻¹, _, ⟨(e - rt ξ, g * (a * p⁻¹), u₀, u₁), ⟨hξ, hc, hu₀, hu₁⟩, rfl⟩, kk, hkk, ?_⟩
  have hd : diagUnits 2 ![g * a * u₀, (g * a)⁻¹ * u₁] =
      diagUnits 2 ![g * (a * p⁻¹) * u₀, (g * (a * p⁻¹))⁻¹ * u₁] * diagUnits 2 ![p, p⁻¹] := by
    rw [← map_mul]
    congr 1
    funext i
    fin_cases i <;> simp [mul_assoc, mul_comm, mul_left_comm]
  rw [map_inv, eq_inv_mul_iff_mul_eq, hγ, hγ', ← hg, ← mul_assoc _ β, ← mul_assoc, ← hY, hY', hd]
  have : gl (nU e) = gl (nU (rt ξ)) * gl (nU (e - rt ξ)) := by rw [← n_add]; congr 2; ring
  rw [this]
  simp only [P, mul_assoc]

/- English proof (translation)
Use `inv_eq_of_mul_eq_one_right ?_` and prove the remaining obligations. Rewrite using `[← posIdeleHom_apply (K := F) ⟨s, hs⟩, ← posIdeleHom_apply (K := F) ⟨s⁻¹, inv_pos.2 hs⟩, ← map_mul, ← map_one (posIdeleHom F)]`. Conclude with `congrArg _ (Subtype.ext (mul_inv_cancel₀ hs.ne'))`.
-/
private theorem pos_inv {s : ℝ} (hs : 0 < s) : (posIdele (K := F) s hs)⁻¹ = posIdele s⁻¹ (inv_pos.2 hs) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← posIdeleHom_apply (K := F) ⟨s, hs⟩, ← posIdeleHom_apply (K := F) ⟨s⁻¹, inv_pos.2 hs⟩, ← map_mul, ← map_one (posIdeleHom F)]
  exact congrArg _ (Subtype.ext (mul_inv_cancel₀ hs.ne'))

/- English proof (translation)
Establish `hp : 0 < s` using `hs₀.trans_le hs`. Establish `h2 : h ^ N ≤ (H * (H * M * τ ^ e)) ^ N * s ^ (e * N)`. Use `(pow_le_pow_left₀ hh h1 N).trans_eq ?_` and prove the remaining obligations. Rewrite using `[pow_mul, ← mul_pow, mul_pow τ]`. Put the polynomial expressions in normal form.

Establish `h3 : s⁻¹ ^ (e * N + d * r) ≤ s₀⁻¹ ^ (e * N + d * r)` using `pow_le_pow_left₀ (by positivity) (inv_anti₀ hs₀ hs) _`. Establish `h4 : 0 ≤ (H * (H * M * τ ^ e)) ^ N`. Assume the negation of the conclusion as `hn`. Conclude with `absurd (h2.trans_lt (mul_neg_of_neg_of_pos (not_le.1 hn) (by positivity))) (not_lt.2 (by positivity))`. Combine the equalities or inequalities in the displayed calculation.

Conclude with `le_abs_self C`. Use `_ = |C| * (H * (H * M * τ ^ e)) ^ N * s⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by`. Rewrite using `[div_eq_mul_inv, mul_pow, pow_add s⁻¹ (e * N), inv_pow (s ^ d), ← pow_mul, inv_pow s (e * N), inv_pow s (d * r)]`. Clear the denominators using the available nonvanishing facts. Use `_ ≤ _ := by gcongr`.
-/
private theorem arith {C H M τ s s₀ h : ℝ} {e N d r : ℕ} (hs₀ : 0 < s₀) (hs : s₀ ≤ s) (hh : 0 ≤ h)
    (h1 : h ≤ H * (H * M * (τ * s) ^ e)) :
    C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N ≤ |C| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
  have hp : 0 < s := hs₀.trans_le hs
  have h2 : h ^ N ≤ (H * (H * M * τ ^ e)) ^ N * s ^ (e * N) := by
    refine (pow_le_pow_left₀ hh h1 N).trans_eq ?_
    rw [pow_mul, ← mul_pow, mul_pow τ]; ring_nf
  have h3 : s⁻¹ ^ (e * N + d * r) ≤ s₀⁻¹ ^ (e * N + d * r) := pow_le_pow_left₀ (by positivity) (inv_anti₀ hs₀ hs) _
  have h4 : 0 ≤ (H * (H * M * τ ^ e)) ^ N := by
    by_contra hn
    exact absurd (h2.trans_lt (mul_neg_of_neg_of_pos (not_le.1 hn) (by positivity))) (not_lt.2 (by positivity))
  calc C * (s⁻¹ / s) ^ (e * N + d * r) * h ^ N
      ≤ |C| * (s⁻¹ / s) ^ (e * N + d * r) * ((H * (H * M * τ ^ e)) ^ N * s ^ (e * N)) := by
        gcongr
        exact le_abs_self C
    _ = |C| * (H * (H * M * τ ^ e)) ^ N * s⁻¹ ^ (e * N + d * r) * (s ^ d)⁻¹ ^ r := by
        rw [div_eq_mul_inv, mul_pow, pow_add s⁻¹ (e * N), inv_pow (s ^ d), ← pow_mul, inv_pow s (e * N), inv_pow s (d * r)]
        field_simp
    _ ≤ _ := by gcongr

end SlopeTestRemainingChoices

set_option maxHeartbeats 800000 in
/- English proof (translation)
Introduce `F _ _ _ π f hf`. Take `⟨ψ, rfl⟩` from `UpperTheory.V.Cm.mem_range_ofCusp.2 (π.cusp f hf)`. Use `⟨⟨ψ.2.1.continuous, (π.cusp _ hf).1.left⟩, fun g => ?_, fun C hC c hc r => ?_⟩` and prove the remaining obligations. Use `letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩`. Rewrite using `[← Pp.int_one (ι := UPos 2 1), ← ψ.2.2 1 one_pos one_lt_two g]`.

Use `integral_congr_ae (Eventually.of_forall fun x => ?_)` and prove the remaining obligations. Establish `: gl (nU (x default)) = unipGL x`. Use `Units.ext ?_` and prove the remaining obligations. Use extensionality with `i j`. Apply the tactic sequence `fin_cases i <;> fin_cases j <;> simp [Pp.vn, unipMatrix, blockEntry_apply]`.

Both sides reduce to the same expression. Simplify using `only [this]`. Both sides reduce to the same expression. Take `⟨ω, hω, hωB, hs⟩` from `siegel hC`. Take `⟨M, hM⟩` from `CuspidalSpectrum.exists_height_le_of_isCompact hω`.

Use `set d := Module.finrank ℚ F`. Establish `hd : d ≠ 0` using `Module.finrank_pos.ne'`. Use `set s₀ := c ^ (d : ℝ)⁻¹`. Establish `hs₀ : 0 < s₀` using `Real.rpow_pos_of_pos hc _`. Take `⟨N, hN⟩` from `CuspidalSpectrum.exists_norm_le_siegel_root ψ.2 hω hωB (pow_pos hs₀ 2) one_pos one_lt_two`.

Use `set e := 2 * Fintype.card (InfinitePlace F)`. Take `⟨B, hB⟩` from `hN (e * N + d * r)`. Use `set τ := 1 + s₀⁻¹ + s₀⁻¹ ^ 2`. Use `set H := heightConst F 2`. Use `⟨|B| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r), fun b a k hk ha => ?_⟩` and prove the remaining obligations.

Use `set s := ab a ^ (d : ℝ)⁻¹`. Establish `h0 : s₀ ≤ s` using `Real.rpow_le_rpow hc.le ha (by positivity)`. Establish `hp : 0 < s` using `hs₀.trans_le h0`. Establish `hsa : s ^ d = ab a` using `Real.rpow_inv_natCast_pow (hc.le.trans ha) hd`. Take `⟨γ, γ', y, hy, kk, hkk, e1⟩` from `hs b a k hk s hp hsa`.

Rewrite using `[e1, (π.cusp _ hf).1.left, (π.cusp _ hf).1.left, ← hsa]`. Apply the tactic sequence `have hρ : ∀ i, 0 < (![s, s⁻¹] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp [hp]`. Establish `e2 : (![posIdele s hp, (posIdele s hp)⁻¹] : Fin 2 → IdeleGroup F) = fun i => posIdele (![s, s⁻¹] i) (hρ i)`. Use function extensionality and compare the values at `i`. Use `fin_cases i`.

Both sides reduce to the same expression. Conclude with `pos_inv hp`. Establish `hi : s⁻¹ ≤ s₀⁻¹` using `inv_anti₀ hs₀ h0`. Establish `h1 : 1 ≤ s₀⁻¹ * s` using `by rw [inv_mul_eq_div, one_le_div hs₀]; exact h0`. Establish `hi0 : 0 < s₀⁻¹` using `inv_pos.2 hs₀`.

Establish `h2 : s₀⁻¹ ≤ s₀⁻¹ ^ 2 * s` using `by nlinarith`. Establish `hL : 1 ≤ τ * s ∧ s ≤ τ * s ∧ s⁻¹ ≤ τ * s`. Apply the tactic sequence `refine ⟨?_, ?_, ?_⟩ <;> simp only [τ] <;> nlinarith`. Establish `h3` using `hB y hy _ hρ (fun i j hij => by`. Take `rfl : i = 0` from `Fin.ext (by have := j.2; simp; omega)`.

Take `rfl : j = 1` from `Fin.ext (by simpa using hij)`. Express the relevant statement in the definitionally equal form `s₀ ^ 2 * s⁻¹ ≤ s`. Rewrite using `[← div_eq_mul_inv, div_le_iff₀ hp]`. Use the proof step `nlinarith) kk hkk _ rfl`. Rewrite using `[e2]`.

Use `h3.trans (arith hs₀ h0 (height_pos _).le ?_)` and prove the remaining obligations. Establish `hH : 0 ≤ H` using `zero_le_one.trans one_le_heightConst`. Use `(height_mul_le _ _).trans ?_` and prove the remaining obligations. Rewrite using `[height_eq_one_of_mem_maxCompact hkk, mul_one]`. Use `mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans ?_) hH` and prove the remaining obligations.

Establish `h5` using `CuspidalSpectrum.height_diagUnits_posIdele_le (K := F) hρ hL.1 (fun i => by fin_cases i`. Conclude with `⟨hL.2.1, hL.2.2⟩`. Conclude with `⟨hL.2.2, by simpa using hL.2.1⟩)`. Conclude with `mul_le_mul (mul_le_mul_of_nonneg_left (hM y hy) hH) h5 (height_pos _).le (mul_nonneg hH ((height_pos _).le.trans (hM y hy)))`.
-/
theorem UpperTheory.ConvolutionTheory.RankTwoDescent.decE :
    DecE := by
  intro F _ _ _ π f hf
  obtain ⟨ψ, rfl⟩ := UpperTheory.V.Cm.mem_range_ofCusp.2 (π.cusp f hf)
  refine ⟨⟨ψ.2.1.continuous, (π.cusp _ hf).1.left⟩, fun g => ?_, fun C hC c hc r => ?_⟩
  · letI : Unique (UPos 2 1) := ⟨⟨⟨(0, 1), by decide⟩⟩, by decide⟩
    rw [← Pp.int_one (ι := UPos 2 1), ← ψ.2.2 1 one_pos one_lt_two g]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    have : gl (nU (x default)) = unipGL x := by
      refine Units.ext ?_
      ext i j
      fin_cases i <;> fin_cases j <;> simp [Pp.vn, unipMatrix, blockEntry_apply]
      rfl
    simp only [this]
    rfl
  obtain ⟨ω, hω, hωB, hs⟩ := siegel hC
  obtain ⟨M, hM⟩ := CuspidalSpectrum.exists_height_le_of_isCompact hω
  set d := Module.finrank ℚ F
  have hd : d ≠ 0 := Module.finrank_pos.ne'
  set s₀ := c ^ (d : ℝ)⁻¹
  have hs₀ : 0 < s₀ := Real.rpow_pos_of_pos hc _
  obtain ⟨N, hN⟩ := CuspidalSpectrum.exists_norm_le_siegel_root ψ.2 hω hωB (pow_pos hs₀ 2) one_pos one_lt_two
  set e := 2 * Fintype.card (InfinitePlace F)
  obtain ⟨B, hB⟩ := hN (e * N + d * r)
  set τ := 1 + s₀⁻¹ + s₀⁻¹ ^ 2
  set H := heightConst F 2
  refine ⟨|B| * (H * (H * M * τ ^ e)) ^ N * s₀⁻¹ ^ (e * N + d * r), fun b a k hk ha => ?_⟩
  set s := ab a ^ (d : ℝ)⁻¹
  have h0 : s₀ ≤ s := Real.rpow_le_rpow hc.le ha (by positivity)
  have hp : 0 < s := hs₀.trans_le h0
  have hsa : s ^ d = ab a := Real.rpow_inv_natCast_pow (hc.le.trans ha) hd
  obtain ⟨γ, γ', y, hy, kk, hkk, e1⟩ := hs b a k hk s hp hsa
  rw [e1, (π.cusp _ hf).1.left, (π.cusp _ hf).1.left, ← hsa]
  have hρ : ∀ i, 0 < (![s, s⁻¹] : Fin 2 → ℝ) i := fun i => by fin_cases i <;> simp [hp]
  have e2 : (![posIdele s hp, (posIdele s hp)⁻¹] : Fin 2 → IdeleGroup F) = fun i => posIdele (![s, s⁻¹] i) (hρ i) := by
    funext i
    fin_cases i
    · rfl
    · exact pos_inv hp
  have hi : s⁻¹ ≤ s₀⁻¹ := inv_anti₀ hs₀ h0
  have h1 : 1 ≤ s₀⁻¹ * s := by rw [inv_mul_eq_div, one_le_div hs₀]; exact h0
  have hi0 : 0 < s₀⁻¹ := inv_pos.2 hs₀
  have h2 : s₀⁻¹ ≤ s₀⁻¹ ^ 2 * s := by nlinarith
  have hL : 1 ≤ τ * s ∧ s ≤ τ * s ∧ s⁻¹ ≤ τ * s := by
    refine ⟨?_, ?_, ?_⟩ <;> simp only [τ] <;> nlinarith
  have h3 := hB y hy _ hρ (fun i j hij => by
    obtain rfl : i = 0 := Fin.ext (by have := j.2; simp; omega)
    obtain rfl : j = 1 := Fin.ext (by simpa using hij)
    change s₀ ^ 2 * s⁻¹ ≤ s
    rw [← div_eq_mul_inv, div_le_iff₀ hp]; nlinarith) kk hkk _ rfl
  rw [e2]
  refine h3.trans (arith hs₀ h0 (height_pos _).le ?_)
  have hH : 0 ≤ H := zero_le_one.trans one_le_heightConst
  refine (height_mul_le _ _).trans ?_
  rw [height_eq_one_of_mem_maxCompact hkk, mul_one]
  refine mul_le_mul_of_nonneg_left ((height_mul_le _ _).trans ?_) hH
  have h5 := CuspidalSpectrum.height_diagUnits_posIdele_le (K := F) hρ hL.1 (fun i => by
    fin_cases i
    · exact ⟨hL.2.1, hL.2.2⟩
    · exact ⟨hL.2.2, by simpa using hL.2.1⟩)
  exact mul_le_mul (mul_le_mul_of_nonneg_left (hM y hy) hH) h5 (height_pos _).le
    (mul_nonneg hH ((height_pos _).le.trans (hM y hy)))
