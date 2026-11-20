import Mathlib
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.RedMFrMapAdjZero
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.LatOEqHatA
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.SelfDualLatticesAtLevel
import Development.AbelianVarietyTheory.Proofs.IwasawaDecomposition.ExistsNsmulIntMemLatO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.AdeleTensorComponentIdempotentSumAddConjEqOne
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.PlaceIdempotentUnderEqOfLiesOver
import Development.AbelianVarietyTheory.Proofs.AdelicLatticeProofs.MemLatOIffExistsActO
import Development.AbelianVarietyTheory.Proofs.TwistedOperators.IdempotentSumAddConjIdempotentConjFixed
import Development.AbelianVarietyTheory.Proofs.SiegelThetaTransformation.CompletedTensorLatticeStrongApproxOpenCompact
open Formalism.BasicNotions Formalism.BasicNotions.TH Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.MainNotions.StandardLattice Formalism.L2.Theta Formalism.IndefR Formalism.IndefR.Datum Formalism.IndefR.Links Formalism.IndefR.Mult Formalism.IndefR.FWT Formalism.L2.Pj
open MeasureTheory IsDedekindDomain NumberField Matrix Complex
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.FD GlobalTheory GlobalTheory.ThFr GlobalTheory.Ker GlobalTheory.AdSpan
open GlobalTheory.SW hiding Level
open scoped TensorProduct ComplexConjugate Classical
attribute [local instance] Formalism.BasicNotions.Host.cmStar

noncomputable section

namespace GlobalTheory.HatPoint

section Gen

variable {F : Type} [Field F] [NumberField F]

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem ev_apply (v : HeightOneSpectrum (𝓞 F)) (x : Af F) : evalV F v x = x v := rfl

/- English proof (translation)
Rewrite using `[GlobalTheory.Ker.MovLev.val_coe]`. Conclude with `v.intValuation_eq_one_iff.2 ht`.
-/
theorem val_coe_one (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    Valued.v (algebraMap F (Af F) (t : F) v) = 1 := by
  rw [GlobalTheory.Ker.MovLev.val_coe]; exact v.intValuation_eq_one_iff.2 ht

/- English proof (translation)
Introduce `h0` and use `by have := val_coe_one t v ht rw [h0, map_zero] at this exact zero_ne_one this`.
-/
theorem coe_ne_zero (t : 𝓞 F) (v : HeightOneSpectrum (𝓞 F)) (ht : t ∉ v.asIdeal) :
    algebraMap F (Af F) (t : F) v ≠ 0 := fun h0 => by
  have := val_coe_one t v ht
  rw [h0, map_zero] at this
  exact zero_ne_one this

/- English proof (translation)
Rewrite `hx`, the goal using `[HeightOneSpectrum.mem_adicCompletionIntegers]`. Rewrite using `[map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]`. Conclude with `hx`.
-/
theorem div_int {v : HeightOneSpectrum (𝓞 F)} {x : v.adicCompletion F} (hx : x ∈ v.adicCompletionIntegers F)
    (t : 𝓞 F) (ht : t ∉ v.asIdeal) : x * (algebraMap F (Af F) (t : F) v)⁻¹ ∈ v.adicCompletionIntegers F := by
  rw [HeightOneSpectrum.mem_adicCompletionIntegers] at hx ⊢
  rw [map_mul, map_inv₀, val_coe_one t v ht, inv_one, mul_one]
  exact hx

def mulG (I : Ideal (𝓞 F)) : AddSubgroup (Af F) :=
  AddSubgroup.closure {x | ∃ t ∈ I, ∃ β ∈ intAf F, x = algebraMap F (Af F) (t : F) * β}

/- English proof (translation)
Distinguish the cases in `h0 : γ = 0`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Choose the witnesses or unpack the hypotheses as in `⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by`. Assume the negation of the conclusion as `H`.

Use `push_neg at H`. Conclude with `h0 (FiniteAdeleRing.ext F fun v => H v)`. Take `⟨t₁, ht₁I, ht₁w⟩` from `(h w₀).resolve_left hw₀`. Establish `ht₁0 : t₁ ≠ 0` using `fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)`. Establish `hspan : Ideal.span {t₁} ≠ 0`.

Rewrite using `[Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]`. Conclude with `ht₁0`. Use `set Z := (Ideal.finite_factors hspan).toFinset with hZdef`. Establish `hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal` using `fun v => by`. Rewrite using `[hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]`.

Establish `h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal` using `fun v => (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩`. Use `choose τ hτI hτ using h'`. Choose the witnesses or unpack the hypotheses as in `⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F, (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by`. Use `⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩` and prove the remaining obligations. Simplify using `only split_ifs with hv`.

Conclude with `zero_mem _`. Conclude with `div_int (hγ v) _ ((hτ v).resolve_left hv)`. Simplify using `only split_ifs with hv`. Rewrite using `[mul_zero, hv]`. Rewrite using `[mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]`.

Establish `hb₁ : ∀ v : HeightOneSpectrum (𝓞 F), (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F` using `fun v => by split_ifs with hv`. Conclude with `zero_mem _`. Conclude with `div_int (hγ v) _ hv`. Take `⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧ ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹` from `⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩`. Establish `hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F` using `fun w v => by split_ifs exacts [hc v, zero_mem _]`.

Establish `hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0` using `fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩`. Use `choose β hβ eβ using hβex`. Establish `e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w`. Use `FiniteAdeleRing.ext F fun v => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)`.

Rewrite using `[map_add, map_sum, map_mul]`. Simplify using `only [map_mul, ev_apply, eβ₁, eβ]`. Distinguish the cases in `hv : t₁ ∈ v.asIdeal`. Establish `hvZ : v ∈ Z` using `(hZ v).2 hv`. Rewrite using `[Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero]) (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']`.

Rewrite using `[Finset.sum_eq_zero (fun w hw => by`. Establish `hne : v ≠ w` using `fun e => hv (e ▸ (hZ w).1 hw)`. Rewrite using `[if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,`. Use `inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]`. Rewrite using `[e]`.

Use `add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)` and prove the remaining obligations. Conclude with `AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩`.
-/
theorem mem_mulG (I : Ideal (𝓞 F)) {γ : Af F} (hγ : γ ∈ intAf F)
    (h : ∀ w : HeightOneSpectrum (𝓞 F), evalV F w γ = 0 ∨ ∃ t ∈ I, t ∉ w.asIdeal) : γ ∈ mulG I := by
  by_cases h0 : γ = 0
  · rw [h0]; exact zero_mem _
  obtain ⟨w₀, hw₀⟩ : ∃ w, γ w ≠ 0 := by
    by_contra H
    push_neg at H
    exact h0 (FiniteAdeleRing.ext F fun v => H v)
  obtain ⟨t₁, ht₁I, ht₁w⟩ := (h w₀).resolve_left hw₀
  have ht₁0 : t₁ ≠ 0 := fun e => ht₁w (e ▸ w₀.asIdeal.zero_mem)
  have hspan : Ideal.span {t₁} ≠ 0 := by
    rw [Ne, Ideal.zero_eq_bot, Ideal.span_singleton_eq_bot]
    exact ht₁0
  set Z := (Ideal.finite_factors hspan).toFinset with hZdef
  have hZ : ∀ v, v ∈ Z ↔ t₁ ∈ v.asIdeal := fun v => by
    rw [hZdef, Set.Finite.mem_toFinset, Set.mem_setOf_eq, Ideal.dvd_span_singleton]
  have h' : ∀ v : HeightOneSpectrum (𝓞 F), ∃ t ∈ I, γ v = 0 ∨ t ∉ v.asIdeal := fun v =>
    (h v).elim (fun e => ⟨0, I.zero_mem, Or.inl e⟩) fun ⟨t, ht, hv⟩ => ⟨t, ht, Or.inr hv⟩
  choose τ hτI hτ using h'
  obtain ⟨c, hc, hc'⟩ : ∃ c : ∀ v : HeightOneSpectrum (𝓞 F), v.adicCompletion F,
      (∀ v, c v ∈ v.adicCompletionIntegers F) ∧ ∀ v, algebraMap F (Af F) (τ v : F) v * c v = γ v := by
    refine ⟨fun v => if γ v = 0 then 0 else γ v * (algebraMap F (Af F) (τ v : F) v)⁻¹, fun v => ?_, fun v => ?_⟩
    · dsimp only
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ ((hτ v).resolve_left hv)
    · dsimp only
      split_ifs with hv
      · rw [mul_zero, hv]
      · rw [mul_comm, mul_assoc, inv_mul_cancel₀ (coe_ne_zero _ _ ((hτ v).resolve_left hv)), mul_one]
  have hb₁ : ∀ v : HeightOneSpectrum (𝓞 F),
      (if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹) ∈ v.adicCompletionIntegers F :=
    fun v => by
      split_ifs with hv
      · exact zero_mem _
      · exact div_int (hγ v) _ hv
  obtain ⟨β₁, hβ₁, eβ₁⟩ : ∃ β₁ : Af F, β₁ ∈ intAf F ∧
      ∀ v, β₁ v = if t₁ ∈ v.asIdeal then 0 else γ v * (algebraMap F (Af F) (t₁ : F) v)⁻¹ :=
    ⟨GlobalTheory.Ker.MovLev.ofInt _ hb₁, fun v => hb₁ v, fun _ => rfl⟩
  have hbw : ∀ w v : HeightOneSpectrum (𝓞 F), (if v = w then c v else 0) ∈ v.adicCompletionIntegers F :=
    fun w v => by
      split_ifs
      exacts [hc v, zero_mem _]
  have hβex : ∀ w : HeightOneSpectrum (𝓞 F), ∃ β : Af F, β ∈ intAf F ∧ ∀ v, β v = if v = w then c v else 0 :=
    fun w => ⟨GlobalTheory.Ker.MovLev.ofInt _ (hbw w), fun v => hbw w v, fun _ => rfl⟩
  choose β hβ eβ using hβex
  have e : γ = algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w := by
    refine FiniteAdeleRing.ext F fun v => ?_
    change evalV F v γ = evalV F v (algebraMap F (Af F) (t₁ : F) * β₁ + ∑ w ∈ Z, algebraMap F (Af F) (τ w : F) * β w)
    rw [map_add, map_sum, map_mul]
    simp only [map_mul, ev_apply, eβ₁, eβ]
    by_cases hv : t₁ ∈ v.asIdeal
    · have hvZ : v ∈ Z := (hZ v).2 hv
      rw [Finset.sum_eq_single v (fun w _ hwv => by rw [if_neg (Ne.symm hwv), mul_zero])
        (fun hn => absurd hvZ hn), if_pos hv, if_pos rfl, mul_zero, zero_add, hc']
    · rw [Finset.sum_eq_zero (fun w hw => by
        have hne : v ≠ w := fun e => hv (e ▸ (hZ w).1 hw)
        rw [if_neg hne, mul_zero]), if_neg hv, add_zero, mul_comm, mul_assoc,
        inv_mul_cancel₀ (coe_ne_zero _ _ hv), mul_one]
  rw [e]
  refine add_mem (AddSubgroup.subset_closure ⟨t₁, ht₁I, β₁, hβ₁, rfl⟩) (sum_mem fun w _ => ?_)
  exact AddSubgroup.subset_closure ⟨τ w, hτI w, β w, hβ w, rfl⟩

/- English proof (translation)
Establish `h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β` using `Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)`. Rewrite using `[h, TensorProduct.smul_tmul, Algebra.smul_def]`.
-/
theorem pairA_mul_tmul {E : Type} [Field E] [Algebra F E] (s : F) (β : Af F) (x : E) :
    pairA F 0 (algebraMap F (Af F) s * β) ⊗ₜ[F] x = pairA F 0 β ⊗ₜ[F] (algebraMap F E s * x) := by
  have h : pairA F 0 (algebraMap F (Af F) s * β) = s • pairA F 0 β :=
    Prod.ext (by change (0 : Ainf F) = s • 0; rw [smul_zero]) (by change _ = s • β; rw [Algebra.smul_def]; rfl)
  rw [h, TensorProduct.smul_tmul, Algebra.smul_def]

end Gen

/- English proof (translation)
Introduce `D S T A hA γ hγ y hy`. Set `I : Ideal (𝓞 D.host.F)` to `{ carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A`. Rewrite using `[map_add, add_smul]`. Conclude with `add_mem ha hb`.

Use the proof step `zero_mem' := by`. Express the relevant statement in the definitionally equal form `algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A`. Rewrite using `[map_zero, zero_smul]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := fun c {x} hx => by`.

Express the relevant statement in the definitionally equal form `algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A`. Rewrite using `[map_mul, mul_smul]`. Conclude with `hA c _ hx }`. Establish `hmem` using `mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩`. Set `f : Af D.host.F →+ WO S T` to `{ toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a map_zero' := Matrix.ext fun a k => by`.

Express the relevant statement in the definitionally equal form `pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0`. Conclude with `TensorProduct.zero_tmul _ _`. Use the proof step `map_add' := fun α β => Matrix.ext fun a k => by`. Express the relevant statement in the definitionally equal form `pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a = pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a`. Rewrite using `[← TensorProduct.add_tmul]`.

Use `congr 1`. Conclude with `Prod.ext (add_zero 0).symm rfl }`. Establish `hle : mulG I ≤ (hatA S T A).comap f`. Use `(AddSubgroup.closure_le _).2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨t, ht, β, hβ, rfl⟩`.

Use `AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩` and prove the remaining obligations. Use `Matrix.ext fun a k => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a = pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a`. Rewrite using `[pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]`. Conclude with `hle hmem`.
-/
theorem mem_hatA_of_div : ∀ (D : D7) (S T : HSp D) (A : AddSubgroup (Matrix (Fin S.rank) (Fin T.rank) D.host.E)), (∀ (c : 𝓞 D.host.F), ∀ y ∈ A, (algebraMap D.host.F D.host.E (c : D.host.F)) • y ∈ A) → ∀ γ ∈ intAf D.host.F, ∀ y : Matrix (Fin S.rank) (Fin T.rank) D.host.E, (∀ w : HeightOneSpectrum (𝓞 D.host.F), evalV D.host.F w γ = 0 ∨ ∃ t : 𝓞 D.host.F, t ∉ w.asIdeal ∧ (algebraMap D.host.F D.host.E (t : D.host.F)) • y ∈ A) → (Matrix.of fun a k => (pairA D.host.F 0 γ) ⊗ₜ[D.host.F] y k a : WO S T) ∈ hatA S T A := by
  intro D S T A hA γ hγ y hy
  let I : Ideal (𝓞 D.host.F) :=
    { carrier := {t | algebraMap D.host.F D.host.E (t : D.host.F) • y ∈ A}
      add_mem' := fun {a b} ha hb => by
        change algebraMap D.host.F D.host.E ((a : D.host.F) + (b : D.host.F)) • y ∈ A
        rw [map_add, add_smul]
        exact add_mem ha hb
      zero_mem' := by
        change algebraMap D.host.F D.host.E (0 : D.host.F) • y ∈ A
        rw [map_zero, zero_smul]
        exact zero_mem _
      smul_mem' := fun c {x} hx => by
        change algebraMap D.host.F D.host.E ((c : D.host.F) * (x : D.host.F)) • y ∈ A
        rw [map_mul, mul_smul]
        exact hA c _ hx }
  have hmem := mem_mulG I hγ fun w => (hy w).imp id fun ⟨t, ht, hA'⟩ => ⟨t, hA', ht⟩
  let f : Af D.host.F →+ WO S T :=
    { toFun := fun α => Matrix.of fun a k => (pairA D.host.F 0 α) ⊗ₜ[D.host.F] y k a
      map_zero' := Matrix.ext fun a k => by
        change pairA D.host.F 0 0 ⊗ₜ[D.host.F] y k a = 0
        exact TensorProduct.zero_tmul _ _
      map_add' := fun α β => Matrix.ext fun a k => by
        change pairA D.host.F 0 (α + β) ⊗ₜ[D.host.F] y k a =
          pairA D.host.F 0 α ⊗ₜ[D.host.F] y k a + pairA D.host.F 0 β ⊗ₜ[D.host.F] y k a
        rw [← TensorProduct.add_tmul]
        congr 1
        exact Prod.ext (add_zero 0).symm rfl }
  have hle : mulG I ≤ (hatA S T A).comap f := by
    refine (AddSubgroup.closure_le _).2 ?_
    rintro _ ⟨t, ht, β, hβ, rfl⟩
    refine AddSubgroup.subset_closure ⟨β, hβ, _, ht, ?_⟩
    refine Matrix.ext fun a k => ?_
    change pairA D.host.F 0 (algebraMap D.host.F (Af D.host.F) (t : D.host.F) * β) ⊗ₜ[D.host.F] y k a =
      pairA D.host.F 0 β ⊗ₜ[D.host.F] (algebraMap D.host.F D.host.E (t : D.host.F) • y) k a
    rw [pairA_mul_tmul, Matrix.smul_apply, smul_eq_mul]
  exact hle hmem

end GlobalTheory.HatPoint

end
