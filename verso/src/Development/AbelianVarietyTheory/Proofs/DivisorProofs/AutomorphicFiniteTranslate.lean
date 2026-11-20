import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.Gl2LocalToAdelicEmbedding
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.MemSpanCentreTranslates
open scoped TensorProduct NNReal Matrix ComplexConjugate
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.SiegelSet GlobalTheory.IdTorus GlobalTheory.GLTwoHecke
open GlobalTheory.Doubling (absE)
open GlobalTheory.UAut (IsMaxCpt)
open GlobalTheory.StdPar

noncomputable section

namespace GlobalTheory.FinTransl

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]
  {σ : E →ₐ[F] E} {n : ℕ} {J : Matrix (Fin n) (Fin n) E}

/- English proof (translation)
Take `⟨w, τ, Z, -, h⟩` from `hγ`. Take `⟨x, e, -⟩` from `h t`. Rewrite using `[e]`. Conclude with `commute_embArch σ J x (mem_finPts_iff_forall.1 hy w)`.
-/
theorem commute_line_fin {γ : ℝ → GAd σ J} (hγ : IsRealLine σ J γ) (t : ℝ) {y : GAd σ J}
    (hy : y ∈ finPts σ J) : Commute (γ t) y := by
  obtain ⟨w, τ, Z, -, h⟩ := hγ
  obtain ⟨x, e, -⟩ := h t
  rw [e]; exact commute_embArch σ J x (mem_finPts_iff_forall.1 hy w)

/- English proof (translation)
Take `⟨a, rfl⟩` from `(range_ofInf σ J).ge hk`. Take `⟨b, rfl⟩` from `(range_ofFin σ J).ge hy`. Conclude with `commute_ofInf_ofFin σ J a b`.
-/
theorem commute_inf_fin {k y : GAd σ J} (hk : k ∈ infPts σ J) (hy : y ∈ finPts σ J) : Commute k y := by
  obtain ⟨a, rfl⟩ := (range_ofInf σ J).ge hk
  obtain ⟨b, rfl⟩ := (range_ofFin σ J).ge hy
  exact commute_ofInf_ofFin σ J a b

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => rfl`. Consider the case `cons γ l ih`. Rewrite using `[List.foldr_cons, ih (fun γ' h => hl γ' (List.mem_cons_of_mem _ h)), List.foldr_cons]`. Use function extensionality and compare the values at `g`.

Simplify using `only [lineDer]`. Use `congr 1`. Use function extensionality and compare the values at `t`. Rewrite using `[mul_assoc, (hl γ List.mem_cons_self t).eq, ← mul_assoc]`.
-/
theorem foldr_transl {e : GAd σ J} (l : List (ℝ → GAd σ J)) (hl : ∀ γ ∈ l, ∀ t, Commute (γ t) e)
    (f : GAd σ J → ℂ) : l.foldr lineDer (fun y => f (y * e)) = fun y => l.foldr lineDer f (y * e) := by
  induction l with
  | nil => rfl
  | cons γ l ih =>
    rw [List.foldr_cons, ih (fun γ' h => hl γ' (List.mem_cons_of_mem _ h)), List.foldr_cons]
    funext g
    simp only [lineDer]
    congr 1
    funext t
    rw [mul_assoc, (hl γ List.mem_cons_self t).eq, ← mul_assoc]

/- English proof (translation)
Use function extensionality and compare the values at `g`. Simplify using `only [GlobalTheory.UAut.dop, Finsupp.sum]`. Use `Finset.sum_congr rfl fun l hl => ?_` and prove the remaining obligations. Rewrite using `[foldr_transl l (fun γ h t => commute_line_fin (hz.1 l hl γ h) t he)]`.
-/
theorem dop_transl {z : List (ℝ → GAd σ J) →₀ ℂ} (hz : GlobalTheory.UAut.IsCentral σ J z) {e : GAd σ J} (he : e ∈ finPts σ J)
    (f : GAd σ J → ℂ) : GlobalTheory.UAut.dop z (fun y => f (y * e)) = fun y => GlobalTheory.UAut.dop z f (y * e) := by
  funext g
  simp only [GlobalTheory.UAut.dop, Finsupp.sum]
  refine Finset.sum_congr rfl fun l hl => ?_
  rw [foldr_transl l (fun γ h t => commute_line_fin (hz.1 l hl γ h) t he)]

end GlobalTheory.FinTransl

open GlobalTheory.FinTransl in

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ n J r X Y _ _ _ K hK T f h e efin`. Use `⟨fun u hu g => ?_, fun γ hγ hγ' g => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Simplify using `only [mul_assoc]`. Conclude with `h.leftN u hu _`. Simplify using `only [mul_assoc]`.

Conclude with `h.leftM γ hγ hγ' _`. Take `⟨U, hU, hUφ⟩` from `h.level`. Use `⟨U.comap (MulAut.conj e⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩` and prove the remaining obligations. Establish `: ((U.comap (MulAut.conj e⁻¹).toMonoidHom : Subgroup (GAd σ J)) : Set (GAd σ J)) = (fun k => e⁻¹ * k * e⁻¹⁻¹) ⁻¹' (U : Set (GAd σ J))` using `rfl`. Rewrite using `[this]`.

Conclude with `hU.preimage (by fun_prop)`. Establish `hk' : e⁻¹ * k * e ∈ U` using `by simpa using hk`. Establish `hf' : e⁻¹ * k * e ∈ finPts σ J` using `mul_mem (mul_mem (inv_mem efin) hkf) efin`. Use `hUφ _ hk' hf' (g * e)` as an intermediate fact. Simplify `this` using `[mul_assoc]`.

Conclude with `h.cont.comp (continuous_id.mul continuous_const)`. Introduce `k γ hγ g`. Establish `e1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)) = fun t : Fin k → ℝ => f (g * e * (List.ofFn fun i => γ i (t i)).prod)`. Use function extensionality and compare the values at `t`. Establish `hc : Commute (List.ofFn fun i => γ i (t i)).prod e` using `Commute.list_prod_left _ _ fun a ha => by`.

Take `⟨i, rfl⟩` from `List.mem_ofFn.1 ha`. Conclude with `commute_line_fin (hγ i) _ efin`. Rewrite using `[mul_assoc, hc.eq, ← mul_assoc]`. Use `show ContDiff ℝ _ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)`. Rewrite using `[e1]`.

Conclude with `h.smooth k γ hγ (g * e)`. Take `⟨N, hN⟩` from `h.growth`. Use `⟨N, fun l hl => ?_⟩` and prove the remaining obligations. Take `⟨C, hC⟩` from `hN l hl`. Use `⟨max C 0 * (height σ J e : ℝ) ^ N, fun g => ?_⟩` and prove the remaining obligations.

Rewrite using `[foldr_transl l (fun γ h t => commute_line_fin (hl γ h) t efin)]`. Establish `hh : (height σ J (g * e) : ℝ) ≤ (height σ J g : ℝ) * (height σ J e : ℝ)`. Conclude with `height_mul_le σ J g e` after adjusting the coercions. Establish `h0 : (0 : ℝ) ≤ (height σ J (g * e) : ℝ)` using `by positivity`. Combine the equalities or inequalities in the displayed calculation.

Use `h.kfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => f (g * k))).map (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e))) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨⟨k, hk⟩, rfl⟩`. Use `⟨fun g => f (g * k), Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `g`.

Simplify using `only [LinearMap.funLeft_apply, Function.comp]`. Rewrite using `[mul_assoc, mul_assoc, (commute_inf_fin (hK hk) efin).eq]`. Use `h.zfin` as an intermediate fact. Use `Submodule.finiteDimensional_of_le (S₂ := (Submodule.span ℂ {f' | ∃ z, GlobalTheory.UAut.IsCentral σ J z ∧ f' = GlobalTheory.UAut.dop z f}).map (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e))) (Submodule.span_le.2 ?_)` and prove the remaining obligations. Introduce and unpack `_ ⟨z, hz, rfl⟩`.

Use `⟨GlobalTheory.UAut.dop z f, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[dop_transl hz efin]`. Both sides reduce to the same expression.
-/
theorem GlobalTheory.StdPar.isAutOn_mul_finPts : ∀ {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E} {n : ℕ}
    {J : Matrix (Fin n) (Fin n) E} {r : ℕ} {X Y : Matrix (Fin n) (Fin r) E}, IsCMExt F E σ → IsHermND σ J → IsWittFrame σ J X Y →
    ∀ {K : Subgroup (GAd σ J)}, K ≤ infPts σ J → ∀ {T : Finset (Fin r)} {f : GAd σ J → ℂ}, IsAutOn σ J X Y T K f →
      ∀ y ∈ finPts σ J, IsAutOn σ J X Y T K (fun g => f (g * y)) := by
  intro F E _ _ _ _ _ σ n J r X Y _ _ _ K hK T f h e efin
  refine ⟨fun u hu g => ?_, fun γ hγ hγ' g => ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · simp only [mul_assoc]; exact h.leftN u hu _
  · simp only [mul_assoc]; exact h.leftM γ hγ hγ' _
  · obtain ⟨U, hU, hUφ⟩ := h.level
    refine ⟨U.comap (MulAut.conj e⁻¹).toMonoidHom, ?_, fun k hk hkf g => ?_⟩
    · have : ((U.comap (MulAut.conj e⁻¹).toMonoidHom : Subgroup (GAd σ J)) : Set (GAd σ J)) =
          (fun k => e⁻¹ * k * e⁻¹⁻¹) ⁻¹' (U : Set (GAd σ J)) := rfl
      rw [this]
      exact hU.preimage (by fun_prop)
    · have hk' : e⁻¹ * k * e ∈ U := by simpa using hk
      have hf' : e⁻¹ * k * e ∈ finPts σ J := mul_mem (mul_mem (inv_mem efin) hkf) efin
      have := hUφ _ hk' hf' (g * e)
      simpa [mul_assoc] using this
  · exact h.cont.comp (continuous_id.mul continuous_const)
  · intro k γ hγ g
    have e1 : (fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)) =
        fun t : Fin k → ℝ => f (g * e * (List.ofFn fun i => γ i (t i)).prod) := by
      funext t
      have hc : Commute (List.ofFn fun i => γ i (t i)).prod e :=
        Commute.list_prod_left _ _ fun a ha => by
          obtain ⟨i, rfl⟩ := List.mem_ofFn.1 ha
          exact commute_line_fin (hγ i) _ efin
      rw [mul_assoc, hc.eq, ← mul_assoc]
    show ContDiff ℝ _ fun t : Fin k → ℝ => f (g * (List.ofFn fun i => γ i (t i)).prod * e)
    rw [e1]
    exact h.smooth k γ hγ (g * e)
  · obtain ⟨N, hN⟩ := h.growth
    refine ⟨N, fun l hl => ?_⟩
    obtain ⟨C, hC⟩ := hN l hl
    refine ⟨max C 0 * (height σ J e : ℝ) ^ N, fun g => ?_⟩
    rw [foldr_transl l (fun γ h t => commute_line_fin (hl γ h) t efin)]
    have hh : (height σ J (g * e) : ℝ) ≤ (height σ J g : ℝ) * (height σ J e : ℝ) := by
      exact_mod_cast height_mul_le σ J g e
    have h0 : (0 : ℝ) ≤ (height σ J (g * e) : ℝ) := by positivity
    calc ‖l.foldr lineDer f (g * e)‖ ≤ C * (height σ J (g * e) : ℝ) ^ N := hC _
      _ ≤ max C 0 * (height σ J (g * e) : ℝ) ^ N :=
          mul_le_mul_of_nonneg_right (le_max_left _ _) (by positivity)
      _ ≤ max C 0 * ((height σ J g : ℝ) * (height σ J e : ℝ)) ^ N :=
          mul_le_mul_of_nonneg_left (pow_le_pow_left₀ h0 hh N) (le_max_right _ _)
      _ = max C 0 * (height σ J e : ℝ) ^ N * (height σ J g : ℝ) ^ N := by ring
  · have := h.kfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ (Set.range fun k : K => fun g => f (g * k))).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨⟨k, hk⟩, rfl⟩
    refine ⟨fun g => f (g * k), Submodule.subset_span ⟨⟨k, hk⟩, rfl⟩, ?_⟩
    funext g
    simp only [LinearMap.funLeft_apply, Function.comp]
    rw [mul_assoc, mul_assoc, (commute_inf_fin (hK hk) efin).eq]
  · have := h.zfin
    refine Submodule.finiteDimensional_of_le
      (S₂ := (Submodule.span ℂ {f' | ∃ z, GlobalTheory.UAut.IsCentral σ J z ∧ f' = GlobalTheory.UAut.dop z f}).map
        (LinearMap.funLeft ℂ ℂ (fun y : GAd σ J => y * e)))
      (Submodule.span_le.2 ?_)
    rintro _ ⟨z, hz, rfl⟩
    refine ⟨GlobalTheory.UAut.dop z f, Submodule.subset_span ⟨z, hz, rfl⟩, ?_⟩
    rw [dop_transl hz efin]
    rfl
