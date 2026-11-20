import Development.AutomorphicArithmetic.Foundations.Convolution.RealGroupAnalysis.Smooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.AutomorphicForms.FoundBridge
import GroundTheory.AutomorphicForms.CuspidalDiscreteness.CuspFormsSiegel
import GroundTheory.AutomorphicForms.ReductionIdele

open NumberField IsDedekindDomain MeasureTheory Matrix Topology Filter
open Neutral.B1 Formalism.L2.Host Formalism.ConjugateSelfDual GlobalTheory.CuspRep GlobalTheory.GalOfCusp UpperTheory.V UpperTheory.V.Af UpperTheory.V.Published GroundTheory.Global GroundTheory.Automorphic.GJMatrix
open UpperTheory.ConvolutionTheory.R2
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
A detailed English derivation is pending.
-/
private theorem gmul (x y : G1 F) : gl (x * y) = gl x * gl y := map_mul _ _ _

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation. Simplify using the standard rewrite rules.

Reduce the conclusion to the remaining proof obligations. Apply the first step, then apply the next step to every resulting obligation.
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
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem tri (Y : GL (Fin 2) (A F)) (t₀ t₁ : (A F)ˣ) (h0 : Y.val 0 0 = t₀) (h1 : Y.val 1 1 = t₁) (h : Y.val 1 0 = 0) :
    Y = gl (nU (Y.val 0 1 * ((t₁⁻¹ : (A F)ˣ) : A F))) * diagUnits 2 ![t₀, t₁] := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, Matrix.diagonal, h0, h1, h]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem n_add (x y : A F) : gl (nU (x + y)) = gl (nU x) * gl (nU y) := by
  refine Units.ext ?_
  ext i j
  fin_cases i <;> fin_cases j <;> simp [vn, Matrix.mul_apply, Fin.sum_univ_two, add_comm]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation.
-/
private theorem rat_n (k : F) : ∃ γ : GL (Fin 2) F, ratGL F 2 γ = gl (nU (rt k)) := by
  refine ⟨Matrix.SpecialLinearGroup.toGL ⟨!![1, k; 0, 1], by simp [Matrix.det_fin_two]⟩, Units.ext ?_⟩
  ext i j
  change algebraMap F (A F) (!![1, k; 0, 1] i j) = _
  fin_cases i <;> fin_cases j <;> simp [vn]

/- English proof (translation)
Reduce the conclusion to the remaining proof obligations. By extensionality, compare the relevant components. Express the relevant assertion in an equivalent form by its definition. Apply the first step, then apply the next step to every resulting obligation. Both sides reduce to the same expression.

Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Both sides reduce to the same expression.
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
Introduce a local definition for the expression. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Rewrite the indicated hypotheses using the stated equalities. Simplify to obtain the desired conclusion from the available facts. Simplify to obtain the desired conclusion from the available facts.

Supply the required witnesses or components. A detailed English derivation is pending.
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
Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Establish an intermediate fact. Introduce a local definition for the expression.

Apply the first step, then apply the next step to every resulting obligation. Reduce the conclusion to the remaining proof obligations. Assume the hypotheses and unpack their components. Reduce the conclusion to the remaining proof obligations. Fix the arbitrary inputs or assume the hypotheses.

Apply the first step, then apply the next step to every resulting obligation. Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Both sides reduce to the same expression.

Extract witnesses or component facts from the available result. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Reduce the equality to equality of the corresponding arguments. Apply function extensionality and compare values at an arbitrary argument.

Apply the first step, then apply the next step to every resulting obligation. Rewrite the conclusion using the stated equalities. Establish an intermediate fact. Rewrite the conclusion using the stated equalities. Simplify using the standard rewrite rules.

A detailed English derivation is pending.
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
Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. A detailed English derivation is pending.
-/
private theorem pos_inv {s : ℝ} (hs : 0 < s) : (posIdele (K := F) s hs)⁻¹ = posIdele s⁻¹ (inv_pos.2 hs) := by
  refine inv_eq_of_mul_eq_one_right ?_
  rw [← posIdeleHom_apply (K := F) ⟨s, hs⟩, ← posIdeleHom_apply (K := F) ⟨s⁻¹, inv_pos.2 hs⟩, ← map_mul, ← map_one (posIdeleHom F)]
  exact congrArg _ (Subtype.ext (mul_inv_cancel₀ hs.ne'))

/- English proof (translation)
Establish an intermediate fact. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities. Put the polynomial expressions in normal form.

Establish an intermediate fact. Establish an intermediate fact. Assume the negation of the conclusion and derive a contradiction. Chain the equalities or inequalities of the calculation. Rewrite the hypotheses and the conclusion using the stated equalities.

Clear the denominators using the available nonvanishing facts. A detailed English derivation is pending.
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
Fix the arbitrary inputs or assume the hypotheses. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result.

Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Reduce the conclusion to the remaining proof obligations.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Extract witnesses or component facts from the available result. Rewrite the conclusion using the stated equalities.

Apply the first step, then apply the next step to every resulting obligation. Establish an intermediate fact. Apply function extensionality and compare values at an arbitrary argument. Both sides reduce to the same expression. Establish an intermediate fact.

Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Establish an intermediate fact. Apply the first step, then apply the next step to every resulting obligation.

Establish an intermediate fact. Extract witnesses or component facts from the available result. Extract witnesses or component facts from the available result. Express the relevant assertion in an equivalent form by its definition. Rewrite the conclusion using the stated equalities.

Rewrite the conclusion using the stated equalities. Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Reduce the conclusion to the remaining proof obligations. Rewrite the conclusion using the stated equalities.

Reduce the conclusion to the remaining proof obligations. Establish an intermediate fact. Supply the required witnesses or components. Supply the required witnesses or components. A detailed English derivation is pending.
-/
theorem UpperTheory.ConvolutionTheory.R2.decay :
    ∀ (F : Type) [Field F] [NumberField F] [IsTotallyReal F], St.Decay F := by
  intro F _ _ _ π f hf
  obtain ⟨ψ, rfl⟩ := Fb.mem_range_ofCusp.2 (π.cusp f hf)
  refine ⟨ψ.2.1.continuous, fun C hC c hc r => ?_⟩
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
