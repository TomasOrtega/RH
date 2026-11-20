import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FrobeniusPowRootOfUnity
open ReciprocityTheory.DiscreteGroups.LocalClassField GlobalTheory.LKRes GlobalTheory.LKRes.ResSplit

noncomputable section
open scoped TensorProduct

namespace GlobalTheory.LKRes.ResSplit

/- English proof (translation)
Establish `h` using `Nat.one_lt_pow hr.ne' (Fact.out : p.Prime).one_lt`. Use linear arithmetic over natural numbers and integers.
-/
theorem pow_sub_one_ne_zero (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) : p ^ r - 1 ≠ 0 := by
  have h := Nat.one_lt_pow hr.ne' (Fact.out : p.Prime).one_lt
  omega

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Apply `UnramifiedExtensions.Kn_le (Q0 p) bot_le` to reduce the goal to its premises. Introduce `ξ hξ`. Rewrite `hξ` using `[residue_cardinality_base_field]`. Establish `: NeZero (p ^ r - 1)` using `⟨pow_sub_one_ne_zero p hr⟩`.

Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hξ`. Conclude with `pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce and unpack `_ rfl`. Conclude with `hζr`.
-/
theorem Qr_eq_adjoin (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) {ζ : PadicAlgCl p}
    (hζ : IsPrimitiveRoot ζ (p ^ r - 1)) (hζr : ζ ∈ Qr p r) :
    Qr p r = IntermediateField.adjoin ℚ_[p] {ζ} := by
  apply le_antisymm
  · apply UnramifiedExtensions.Kn_le (Q0 p) bot_le
    intro ξ hξ
    rw [residue_cardinality_base_field] at hξ
    have : NeZero (p ^ r - 1) := ⟨pow_sub_one_ne_zero p hr⟩
    obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hξ
    exact pow_mem (IntermediateField.mem_adjoin_simple_self ℚ_[p] ζ) i
  · rw [IntermediateField.adjoin_le_iff]
    rintro _ rfl
    exact hζr

/- English proof (translation)
Establish `hQ` using `Qr_eq_adjoin p hr hζ ζ.2`. Establish `hrank : Module.finrank ℚ_[p] (Qr p r) = r`. Rewrite using `[finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot, mul_one]`. Establish `hint : IsIntegral ℚ_[p] (ζ : PadicAlgCl p)` using `Algebra.IsIntegral.isIntegral _`. Use `set pb := IntermediateField.adjoin.powerBasis hint`.

Establish `hdim : pb.dim = r`. Rewrite using `[← PowerBasis.finrank pb]`. Conclude with `(congrArg (fun L : IntermediateField ℚ_[p] (PadicAlgCl p) => Module.finrank ℚ_[p] L) hQ).symm.trans hrank`. Establish `hb : (b : PadicAlgCl p) ∈ IntermediateField.adjoin ℚ_[p] {(ζ : PadicAlgCl p)}`. Rewrite using `[← hQ]`.

Conclude with `b.2`. Take `⟨f, hf, hy⟩` from `pb.exists_eq_aeval ⟨b, hb⟩`. Rewrite `hf` using `[hdim]`. Establish `h1 : (b : PadicAlgCl p) = Polynomial.aeval (ζ : PadicAlgCl p) f`. Use `congrArg Subtype.val hy` as an intermediate fact.

Rewrite using `[this]`. Use `show IntermediateField.val _ (Polynomial.aeval pb.gen f) = _`. Rewrite using `[← Polynomial.aeval_algHom_apply]`. Both sides reduce to the same expression. Use `⟨fun j => f.coeff j, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[h1, Polynomial.aeval_eq_sum_range' hf, Finset.sum_range]`. Simplify using `[IntermediateField.coe_sum]`.
-/
theorem Qr_span_pow (p : ℕ) [Fact p.Prime] {r : ℕ} (hr : 0 < r) (ζ : Qr p r)
    (hζ : IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1)) (b : Qr p r) :
    ∃ d : Fin r → ℚ_[p], b = ∑ j : Fin r, d j • ζ ^ (j : ℕ) := by
  have hQ := Qr_eq_adjoin p hr hζ ζ.2
  have hrank : Module.finrank ℚ_[p] (Qr p r) = r := by
    rw [finrank_Kn p (Q0 p) inferInstance hr, IntermediateField.finrank_bot, mul_one]
  have hint : IsIntegral ℚ_[p] (ζ : PadicAlgCl p) := Algebra.IsIntegral.isIntegral _
  set pb := IntermediateField.adjoin.powerBasis hint
  have hdim : pb.dim = r := by
    rw [← PowerBasis.finrank pb]
    exact (congrArg (fun L : IntermediateField ℚ_[p] (PadicAlgCl p) => Module.finrank ℚ_[p] L) hQ).symm.trans hrank
  have hb : (b : PadicAlgCl p) ∈ IntermediateField.adjoin ℚ_[p] {(ζ : PadicAlgCl p)} := by
    rw [← hQ]; exact b.2
  obtain ⟨f, hf, hy⟩ := pb.exists_eq_aeval ⟨b, hb⟩
  rw [hdim] at hf
  have h1 : (b : PadicAlgCl p) = Polynomial.aeval (ζ : PadicAlgCl p) f := by
    have := congrArg Subtype.val hy
    rw [this]
    show IntermediateField.val _ (Polynomial.aeval pb.gen f) = _
    rw [← Polynomial.aeval_algHom_apply]
    rfl
  refine ⟨fun j => f.coeff j, ?_⟩
  apply Subtype.ext
  rw [h1, Polynomial.aeval_eq_sum_range' hf, Finset.sum_range]
  simp [IntermediateField.coe_sum]

/- English proof (translation)
Introduce `p _ K r hr ζ hζ x`. Establish `key : ∀ (c : K) (z : Qr p r), inclK p K r c * inclQ p K r z = (c ⊗ₜ[ℚ_[p]] z : K ⊗[ℚ_[p]] Qr p r)`. Introduce `c z`. Use `show (c ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] z) = _`. Rewrite using `[Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]`.

Establish `h : ∀ y : K ⊗[ℚ_[p]] Qr p r, ∃ c : Fin r → K, y = ∑ j : Fin r, (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r)`. Introduce `y`. Proceed by induction on `y using TensorProduct.induction_on with`. Consider the case `zero => exact ⟨0, by simp⟩`. Consider the case `tmul a b`.

Take `⟨d, hd⟩` from `Qr_span_pow p hr ζ hζ b`. Use `⟨fun j => d j • a, ?_⟩` and prove the remaining obligations. Rewrite using `[hd, TensorProduct.tmul_sum]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[TensorProduct.tmul_smul, TensorProduct.smul_tmul']`.

Consider the case `add y z hy hz`. Take `⟨c, hc⟩` from `hy`. Take `⟨c', hc'⟩` from `hz`. Use `⟨c + c', ?_⟩` and prove the remaining obligations. Rewrite using `[hc, hc', ← Finset.sum_add_distrib]`.

Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[Pi.add_apply, TensorProduct.add_tmul]`. Take `⟨c, hc⟩` from `h x`. Use `⟨c, ?_⟩` and prove the remaining obligations. Establish `e : ∀ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) = (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r)`.

Introduce `j`. Rewrite using `[← map_pow, key]`. Rewrite using `[Finset.sum_congr rfl fun j _ => e j]`. Conclude with `hc`.
-/
theorem KQ_eq_sum_pow : ∀ (p : ℕ) [Fact p.Prime] (K : IntermediateField ℚ_[p] (PadicAlgCl p)) (r : ℕ), 0 < r →
    ∀ (ζ : Qr p r), IsPrimitiveRoot (ζ : PadicAlgCl p) (p ^ r - 1) →
    ∀ x : KQ p K r, ∃ c : Fin r → K, x = ∑ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) := by
  intro p _ K r hr ζ hζ x
  have key : ∀ (c : K) (z : Qr p r), inclK p K r c * inclQ p K r z = (c ⊗ₜ[ℚ_[p]] z : K ⊗[ℚ_[p]] Qr p r) := by
    intro c z
    show (c ⊗ₜ[ℚ_[p]] (1 : Qr p r) : K ⊗[ℚ_[p]] Qr p r) * ((1 : K) ⊗ₜ[ℚ_[p]] z) = _
    rw [Algebra.TensorProduct.tmul_mul_tmul, mul_one, one_mul]
  have h : ∀ y : K ⊗[ℚ_[p]] Qr p r, ∃ c : Fin r → K,
      y = ∑ j : Fin r, (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro y
    induction y using TensorProduct.induction_on with
    | zero => exact ⟨0, by simp⟩
    | tmul a b =>
      obtain ⟨d, hd⟩ := Qr_span_pow p hr ζ hζ b
      refine ⟨fun j => d j • a, ?_⟩
      rw [hd, TensorProduct.tmul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [TensorProduct.tmul_smul, TensorProduct.smul_tmul']
    | add y z hy hz =>
      obtain ⟨c, hc⟩ := hy
      obtain ⟨c', hc'⟩ := hz
      refine ⟨c + c', ?_⟩
      rw [hc, hc', ← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [Pi.add_apply, TensorProduct.add_tmul]
  obtain ⟨c, hc⟩ := h x
  refine ⟨c, ?_⟩
  have e : ∀ j : Fin r, inclK p K r (c j) * inclQ p K r ζ ^ (j : ℕ) =
      (c j ⊗ₜ[ℚ_[p]] (ζ ^ (j : ℕ)) : K ⊗[ℚ_[p]] Qr p r) := by
    intro j
    rw [← map_pow, key]
  rw [Finset.sum_congr rfl fun j _ => e j]
  exact hc

end GlobalTheory.LKRes.ResSplit
