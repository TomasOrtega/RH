import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IsUnifAt
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalConjugationInvolutiveValuationPreservingStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EventuallyIntegralLiftCoprimeDerivativeStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IntegralConjSetLocalUnitaryEqDoubleCosetStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CompactPartCentralizerLeConjIntegralUnitaryStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignFullCharpolyEqOneStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LocalSignKernelCharFactorConjInvariantStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLocalSignEqOneOfIntegralSeparableReductioStatement
open NumberField IsDedekindDomain Matrix Polynomial Filter GlobalTheory.CuspRep GlobalTheory.PRep Formalism.UG Formalism.BasicNotions GlobalTheory.UnitaryBC Formalism.L2.Host GlobalTheory.BCT
open scoped Classical TensorProduct
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField

namespace GlobalTheory.BCT.OrbUnit
open DoubleCoset

/- English proof (translation)
Establish `h1 : rStab (fun _ : H => c) = ⊤`. Use extensionality with `k`. Simplify using `[rStab]`. Unfold `avg`. Rewrite using `[h1, Subgroup.index_top]`.

Use `haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top`. Use `haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun a => Subsingleton.elim _ _⟩`. Rewrite using `[finsum_unique]`. Simplify using the standard rewrite rules.
-/
theorem avg_const {H : Type} [Group H] (c : ℂ) : avg (fun _ : H => c) = c := by
  have h1 : rStab (fun _ : H => c) = ⊤ := by
    ext k; simp [rStab]
  unfold avg
  rw [h1, Subgroup.index_top]
  haveI : Subsingleton (H ⧸ (⊤ : Subgroup H)) := QuotientGroup.subsingleton_quotient_top
  haveI : Unique (H ⧸ (⊤ : Subgroup H)) := ⟨⟨QuotientGroup.mk 1⟩, fun a => Subsingleton.elim _ _⟩
  rw [finsum_unique]
  simp

/- English proof (translation)
Use `set T := twCent (MonoidHom.id G) γ with hT`. Establish `hTle : cptPart T ≤ T`. Unfold `cptPart`. Rewrite using `[Subgroup.closure_le]`. Introduce `t ht`.

Conclude with `ht.1`. Establish `hterm : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G), ((((T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart T) : ℕ) : ℂ) * avg fun k : K => (K : Set G).indicator 1 ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) = if (Quotient.out …`. Introduce `q`. Establish `hconst : (fun k : K => (K : Set G).indicator (1 : G → ℂ) ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k))) = fun _ => if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0`. Use function extensionality and compare the values at `k`.

Establish `he : (Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k) = (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k`. Simplify using `only [MonoidHom.id_apply]`. Use `group`. Rewrite using `[he]`. Distinguish the cases in `hm : (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K`.

Establish `: (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∈ K` using `K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) k.2`. Simplify using `[Set.indicator_of_mem this, hm]`. Establish `: (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∉ K`. Introduce `h`. Apply `hm` to reduce the goal to its premises.

Use `K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)` as an intermediate fact. Simplify `this` using `[mul_assoc]`. Simplify using `[Set.indicator_of_notMem this, hm]`. Rewrite using `[hconst, avg_const]`. Use `split_ifs with hm`.

Rewrite using `[(Subgroup.relIndex_eq_one).2 (le_inf hTle (hcpt _ hm))]`. Simplify using the standard rewrite rules. Simplify using the standard rewrite rules. Rewrite using `[twOrb, finsum_congr hterm]`. Use `split_ifs with hex`.

Take `⟨g₀, hg₀⟩` from `hex`. Establish `hgood : ∀ g : G, g ∈ doubleCoset g₀ (T : Set G) (K : Set G) → g⁻¹ * γ * g ∈ K`. Introduce `g hg`. Take `⟨t, ht, k, hk, rfl⟩` from `mem_doubleCoset.1 hg`. Establish `htc : t * γ = γ * t` using `by simpa [hT, twCent] using ht`.

Establish `: (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * γ * g₀) * k`. Establish `: t⁻¹ * γ * t = γ` using `by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[this]`. Conclude with `K.mul_mem (K.mul_mem (K.inv_mem hk) hg₀) hk`.

Rewrite using `[finsum_eq_single _ (DoubleCoset.mk T K g₀)]`. Rewrite using `[if_pos]`. Take `⟨h, k, hh, hk, he⟩` from `DoubleCoset.mk_out_eq_mul T K g₀`. Apply `hgood` to reduce the goal to its premises. Rewrite using `[he]`.

Conclude with `mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩`. Introduce `q hq`. Rewrite using `[if_neg]`. Introduce `hm`. Apply `hq` to reduce the goal to its premises.

Take `⟨t, ht, k, hk, he⟩` from `horb g₀ (Quotient.out q) hg₀ hm`. Rewrite using `[← DoubleCoset.out_eq' T K q, DoubleCoset.eq]`. Conclude with `⟨t⁻¹, T.inv_mem ht, k⁻¹, K.inv_mem hk, by rw [he]; group⟩`. Use `push_neg at hex`. Rewrite using `[finsum_eq_zero_of_forall_eq_zero]`.

Introduce `q`. Rewrite using `[if_neg (hex _)]`.
-/
theorem twOrb_unit {G : Type} [Group G] [TopologicalSpace G] (K : Subgroup G) (γ : G)
    (horb : ∀ g₁ g₂ : G, g₁⁻¹ * γ * g₁ ∈ K → g₂⁻¹ * γ * g₂ ∈ K →
      ∃ t ∈ twCent (MonoidHom.id G) γ, ∃ k ∈ K, g₂ = t * g₁ * k)
    (hcpt : ∀ g : G, g⁻¹ * γ * g ∈ K →
      cptPart (twCent (MonoidHom.id G) γ) ≤ K.map (MulAut.conj g).toMonoidHom) :
    twOrb (MonoidHom.id G) K γ ((K : Set G).indicator 1) = if ∃ g : G, g⁻¹ * γ * g ∈ K then 1 else 0 := by
  classical
  set T := twCent (MonoidHom.id G) γ with hT
  have hTle : cptPart T ≤ T := by
    unfold cptPart
    rw [Subgroup.closure_le]
    intro t ht; exact ht.1
  have hterm : ∀ q : DoubleCoset.Quotient (T : Set G) (K : Set G),
      ((((T ⊓ K.map (MulAut.conj (Quotient.out q)).toMonoidHom).relIndex (cptPart T) : ℕ) : ℂ) *
        avg fun k : K => (K : Set G).indicator 1 ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
      = if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
    intro q
    have hconst : (fun k : K => (K : Set G).indicator (1 : G → ℂ)
        ((Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)))
        = fun _ => if (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K then 1 else 0 := by
      funext k
      have he : (Quotient.out q * k)⁻¹ * γ * (MonoidHom.id G) (Quotient.out q * k)
          = (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k := by
        simp only [MonoidHom.id_apply]; group
      rw [he]
      by_cases hm : (Quotient.out q)⁻¹ * γ * Quotient.out q ∈ K
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∈ K :=
          K.mul_mem (K.mul_mem (K.inv_mem k.2) hm) k.2
        simp [Set.indicator_of_mem this, hm]
      · have : (k : G)⁻¹ * ((Quotient.out q)⁻¹ * γ * Quotient.out q) * k ∉ K := by
          intro h; apply hm
          have := K.mul_mem (K.mul_mem k.2 h) (K.inv_mem k.2)
          simpa [mul_assoc] using this
        simp [Set.indicator_of_notMem this, hm]
    rw [hconst, avg_const]
    split_ifs with hm
    · rw [(Subgroup.relIndex_eq_one).2 (le_inf hTle (hcpt _ hm))]; simp
    · simp
  rw [twOrb, finsum_congr hterm]
  split_ifs with hex
  · obtain ⟨g₀, hg₀⟩ := hex
    have hgood : ∀ g : G, g ∈ doubleCoset g₀ (T : Set G) (K : Set G) → g⁻¹ * γ * g ∈ K := by
      intro g hg
      obtain ⟨t, ht, k, hk, rfl⟩ := mem_doubleCoset.1 hg
      have htc : t * γ = γ * t := by simpa [hT, twCent] using ht
      have : (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * γ * g₀) * k := by
        have : t⁻¹ * γ * t = γ := by rw [mul_assoc, ← htc, ← mul_assoc, inv_mul_cancel, one_mul]
        calc (t * g₀ * k)⁻¹ * γ * (t * g₀ * k) = k⁻¹ * (g₀⁻¹ * (t⁻¹ * γ * t) * g₀) * k := by group
          _ = _ := by rw [this]
      rw [this]; exact K.mul_mem (K.mul_mem (K.inv_mem hk) hg₀) hk
    rw [finsum_eq_single _ (DoubleCoset.mk T K g₀)]
    · rw [if_pos]
      obtain ⟨h, k, hh, hk, he⟩ := DoubleCoset.mk_out_eq_mul T K g₀
      apply hgood
      rw [he]; exact mem_doubleCoset.2 ⟨h, hh, k, hk, rfl⟩
    · intro q hq
      rw [if_neg]
      intro hm
      apply hq
      obtain ⟨t, ht, k, hk, he⟩ := horb g₀ (Quotient.out q) hg₀ hm
      rw [← DoubleCoset.out_eq' T K q, DoubleCoset.eq]
      exact ⟨t⁻¹, T.inv_mem ht, k⁻¹, K.inv_mem hk, by rw [he]; group⟩
  · push_neg at hex
    rw [finsum_eq_zero_of_forall_eq_zero]
    intro q; rw [if_neg (hex _)]

end GlobalTheory.BCT.OrbUnit

namespace GlobalTheory.BCT.OrbUnit

/- English proof (translation)
Introduce `E _ _ _ _ n _ S _ P hP`. Use `filter_upwards [GlobalTheory.T.eventually_integral_lift_coprime_derivative E P hP.2.2.1] with w hw`. Take `⟨P₀, hmap, hcop⟩` from `hw`. Take `⟨hσσ, hv⟩` from `GlobalTheory.T.localConjugation_involutive_valuation_preserving E w`. Introduce `γ hγ`.

Establish `hγ' : γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E))`. Rewrite using `[hγ, hmap]`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `twOrb_unit (KL n w) γ (GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w hσσ hv P₀ hcop γ hγ') (GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary E n w P₀ hcop γ hγ')`. Rewrite using `[← hγ]`.

Conclude with `GlobalTheory.T.localSign_full_charpoly_eq_one E n w hv γ.1`. Introduce and unpack `Q₁ hQ ⟨g, hg⟩`. Rewrite using `[← GlobalTheory.T.localSign_kernel_charFactor_conj_invariant E n w hv Q₁ γ g]`. Use `GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction E n w hσσ hv P₀ hcop (g⁻¹ * γ * g) ?_ hg Q₁ (by rw [hmap]; exact hQ)` and prove the remaining obligations. Rewrite using `[← hγ']`.

Establish `: ((g⁻¹ * γ * g : UL n w) : GLw n w).val = ((g : GLw n w)⁻¹ : GLw n w).val * (γ : GLw n w).val * (g : GLw n w).val`. Simplify using `only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]`. Rewrite using `[this, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]`.
-/
theorem orbUnit_ae : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E], Unr E → ∀ n : ℕ, 1 ≤ n → ∀ (S : Set (Pl E)), IsSection S → ∀ P ∈ Ell E n, ∀ᶠ w in cofinite, ∀ γ : UL n w, γ.1.val.charpoly = atPl w P → (twOrb (MonoidHom.id _) (KL n w) γ ((KL n w : Set (UL n w)).indicator 1) = if ∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w then 1 else 0) ∧ kapSign n w (atPl w P) γ.1 = 1 ∧ ∀ Q₁ : (w.adicCompletion E)[X], Q₁ ∣ atPl w P → (∃ g : UL n w, g⁻¹ * γ * g ∈ KL n w) → kapSign n w Q₁ γ.1 = 1 := by
  intro E _ _ _ _ n _ S _ P hP
  filter_upwards [GlobalTheory.T.eventually_integral_lift_coprime_derivative E P hP.2.2.1] with w hw
  obtain ⟨P₀, hmap, hcop⟩ := hw
  obtain ⟨hσσ, hv⟩ := GlobalTheory.T.localConjugation_involutive_valuation_preserving E w
  intro γ hγ
  have hγ' : γ.1.val.charpoly = P₀.map (algebraMap (w.adicCompletionIntegers E) (w.adicCompletion E)) := by
    rw [hγ, hmap]
  refine ⟨?_, ?_, ?_⟩
  · exact twOrb_unit (KL n w) γ (GlobalTheory.T.integral_conj_set_localUnitary_eq_doubleCoset E n w hσσ hv P₀ hcop γ hγ') (GlobalTheory.T.compactPart_centralizer_le_conj_integralUnitary E n w P₀ hcop γ hγ')
  · rw [← hγ]; exact GlobalTheory.T.localSign_full_charpoly_eq_one E n w hv γ.1
  · rintro Q₁ hQ ⟨g, hg⟩
    rw [← GlobalTheory.T.localSign_kernel_charFactor_conj_invariant E n w hv Q₁ γ g]
    refine GlobalTheory.T.unitaryLocalSign_eq_one_of_integral_separable_reduction E n w hσσ hv P₀ hcop (g⁻¹ * γ * g) ?_ hg Q₁ (by rw [hmap]; exact hQ)
    rw [← hγ']
    have : ((g⁻¹ * γ * g : UL n w) : GLw n w).val =
        ((g : GLw n w)⁻¹ : GLw n w).val * (γ : GLw n w).val * (g : GLw n w).val := by
      simp only [Subgroup.coe_mul, Subgroup.coe_inv, Units.val_mul]
    rw [this, Matrix.charpoly_mul_comm, ← Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.one_mul]

end GlobalTheory.BCT.OrbUnit
