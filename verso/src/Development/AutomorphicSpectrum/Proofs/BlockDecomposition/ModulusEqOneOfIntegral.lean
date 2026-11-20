import Mathlib
import Development.WeilBound.CoreStatements.PublishedTheorems.JacquetShalikaBound.FormQuasiInvariantMirabolic

noncomputable section

open MeasureTheory Matrix GroundTheory.Automorphic GroundTheory.Automorphic.GLnLocal GroundTheory.Automorphic.Iwasawa
  GroundTheory.Automorphic.Spherical
open scoped ValuativeRel

namespace GlobalTheory.CompanionTheory.JSBound
open PositivityTheory.JacquetShalikaLocal

variable {F : Type} [Field F] [ValuativeRel F] [TopologicalSpace F] [IsNonarchimedeanLocalField F]

/- English proof (translation)
Introduce `i j`. Take `⟨y, hy, e⟩` from `hA i j`. Use `⟨(uniformizer F : F) ^ (c' - c) * y, Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) hy, ?_⟩` and prove the remaining obligations. Rewrite using `[e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]`.
-/
theorem div_mono {ι : Type} {c c' : ℕ} (h : c ≤ c') {A : Matrix ι ι F} (hA : Div c' A) : Div c A := by
  intro i j
  obtain ⟨y, hy, e⟩ := hA i j
  refine ⟨(uniformizer F : F) ^ (c' - c) * y,
    Subring.mul_mem _ (Subring.pow_mem _ (uniformizer F).2 _) hy, ?_⟩
  rw [e, ← mul_assoc, ← pow_add, Nat.add_sub_cancel' h]

/- English proof (translation)
Set `u : Fˣ` to `Units.mk0 a ha`. Set `g : GL (Fin 1) F` to `Units.map (Matrix.scalar (Fin 1) : F →+* Matrix (Fin 1) (Fin 1) F).toMonoidHom u`. Establish `hg : ∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j = a`. Introduce `i j`. Establish `hi : i = j` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Simplify using `[g, u]`. Establish `hgi : ∀ i j, ((g⁻¹ : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) i j = a⁻¹`. Introduce `i j`. Establish `hi : i = j` using `Subsingleton.elim _ _`.

Substitute `hi` using the available equality. Simplify using `[g, u]`. Establish `key` using `Measures.distribHaarChar_glEquiv g`. Rewrite `key` using `[Measures.distribHaarChar_glEquiv_eq_one (fun i j => by rw [hg]; exact h₁) (fun i j => by rw [hgi]; exact h₂)]`. Establish `hdet : Matrix.GeneralLinearGroup.det g = u`.

Use `ext`. Simplify using `[g, u]`. Rewrite `key` using `[hdet]`. Rewrite using `[show a = (u : F) from rfl, Measures.modulus_units, ← key]`.
-/
theorem modulus_eq_one_of_integral {a : F} (ha : a ≠ 0) (h₁ : a ∈ 𝒪[F]) (h₂ : a⁻¹ ∈ 𝒪[F]) :
    Measures.modulus a = 1 := by
  let u : Fˣ := Units.mk0 a ha
  let g : GL (Fin 1) F := Units.map (Matrix.scalar (Fin 1) : F →+* Matrix (Fin 1) (Fin 1) F).toMonoidHom u
  have hg : ∀ i j, (g : Matrix (Fin 1) (Fin 1) F) i j = a := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have hgi : ∀ i j, ((g⁻¹ : GL (Fin 1) F) : Matrix (Fin 1) (Fin 1) F) i j = a⁻¹ := by
    intro i j
    have hi : i = j := Subsingleton.elim _ _
    subst hi
    simp [g, u]
  have key := Measures.distribHaarChar_glEquiv g
  rw [Measures.distribHaarChar_glEquiv_eq_one (fun i j => by rw [hg]; exact h₁)
    (fun i j => by rw [hgi]; exact h₂)] at key
  have hdet : Matrix.GeneralLinearGroup.det g = u := by
    ext
    simp [g, u]
  rw [hdet] at key
  rw [show a = (u : F) from rfl, Measures.modulus_units, ← key]

/- English proof (translation)
Use `choose y hy hA using hD`. Set `A : Matrix (Fin m) (Fin m) 𝒪[F]` to `Matrix.of fun i j => ⟨y i j, hy i j⟩`. Set `M : Matrix (Fin m) (Fin m) 𝒪[F]` to `1 + (uniformizer F ^ (c + 1)) • A`. Establish `hM : (𝒪[F]).subtype.mapMatrix M = (h : Matrix (Fin m) (Fin m) F)`. Use extensionality with `i j`.

Use `hA i j` as an intermediate fact. Rewrite `this` using `[Matrix.sub_apply, sub_eq_iff_eq_add]`. Rewrite using `[this]`. Simplify using `[M, A, Matrix.one_apply, add_comm]`. Apply the tactic sequence `split_ifs <;> simp`.

Establish `hdet : ((M.det : 𝒪[F]) : F) = (h : Matrix (Fin m) (Fin m) F).det`. Rewrite using `[← hM]`. Conclude with `RingHom.map_det (𝒪[F]).subtype M`. Set `I : Ideal 𝒪[F]` to `Ideal.span {uniformizer F}`. Establish `hq : (Ideal.Quotient.mk I).mapMatrix M = 1`.

Establish `h0 : Ideal.Quotient.mk I (uniformizer F) = 0` using `Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)`. Use extensionality with `i j`. Simplify using `[M, h0, Matrix.one_apply]`. Establish `hone : Ideal.Quotient.mk I M.det = 1`. Rewrite using `[RingHom.map_det, hq, Matrix.det_one]`.

Establish `hmem : M.det - 1 ∈ I`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_sub, hone, map_one, sub_self]`. Take `⟨z, hz⟩` from `Ideal.mem_span_singleton'.1 hmem`. Establish `hv : ValuativeRel.valuation F ((M.det : 𝒪[F]) : F) = 1`. Establish `e : ((M.det : 𝒪[F]) : F) = 1 + (z : F) * (uniformizer F : F)`.

Use `congrArg (fun w : 𝒪[F] => (w : F)) hz` as an intermediate fact. Simplify using `only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this`. Rewrite using `[this]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[e]`.

Use `Valuation.map_one_add_of_lt _ ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Establish `hz1 : ValuativeRel.valuation F (z : F) ≤ 1` using `z.2`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← hdet]`.

Establish `hne : ((M.det : 𝒪[F]) : F) ≠ 0`. Introduce `h0`. Rewrite `hv` using `[h0, map_zero]`. Conclude with `zero_ne_one hv`. Use `modulus_eq_one_of_integral hne ?_ ?_` and prove the remaining obligations.

Conclude with `(Valuation.mem_integer_iff _ _).2 hv.le`. Use `(Valuation.mem_integer_iff _ _).2 ?_` and prove the remaining obligations. Rewrite using `[map_inv₀, hv, inv_one]`.
-/
theorem modulus_det_eq_one {m c : ℕ} (h : GL (Fin m) F)
    (hD : Div (c + 1) ((h : Matrix (Fin m) (Fin m) F) - 1)) :
    Measures.modulus (h : Matrix (Fin m) (Fin m) F).det = 1 := by
  classical
  choose y hy hA using hD
  let A : Matrix (Fin m) (Fin m) 𝒪[F] := Matrix.of fun i j => ⟨y i j, hy i j⟩
  let M : Matrix (Fin m) (Fin m) 𝒪[F] := 1 + (uniformizer F ^ (c + 1)) • A
  have hM : (𝒪[F]).subtype.mapMatrix M = (h : Matrix (Fin m) (Fin m) F) := by
    ext i j
    have := hA i j
    rw [Matrix.sub_apply, sub_eq_iff_eq_add] at this
    rw [this]
    simp [M, A, Matrix.one_apply, add_comm]
    split_ifs <;> simp
  have hdet : ((M.det : 𝒪[F]) : F) = (h : Matrix (Fin m) (Fin m) F).det := by
    rw [← hM]
    exact RingHom.map_det (𝒪[F]).subtype M
  let I : Ideal 𝒪[F] := Ideal.span {uniformizer F}
  have hq : (Ideal.Quotient.mk I).mapMatrix M = 1 := by
    have h0 : Ideal.Quotient.mk I (uniformizer F) = 0 :=
      Ideal.Quotient.eq_zero_iff_mem.2 (Ideal.mem_span_singleton_self _)
    ext i j
    simp [M, h0, Matrix.one_apply]
  have hone : Ideal.Quotient.mk I M.det = 1 := by
    rw [RingHom.map_det, hq, Matrix.det_one]
  have hmem : M.det - 1 ∈ I := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_sub, hone, map_one, sub_self]
  obtain ⟨z, hz⟩ := Ideal.mem_span_singleton'.1 hmem
  have hv : ValuativeRel.valuation F ((M.det : 𝒪[F]) : F) = 1 := by
    have e : ((M.det : 𝒪[F]) : F) = 1 + (z : F) * (uniformizer F : F) := by
      have := congrArg (fun w : 𝒪[F] => (w : F)) hz
      simp only [MulMemClass.coe_mul, AddSubgroupClass.coe_sub, OneMemClass.coe_one] at this
      rw [this]; ring
    rw [e]
    refine Valuation.map_one_add_of_lt _ ?_
    rw [map_mul]
    have hz1 : ValuativeRel.valuation F (z : F) ≤ 1 := z.2
    calc ValuativeRel.valuation F (z : F) * ValuativeRel.valuation F (uniformizer F : F)
        ≤ 1 * ValuativeRel.valuation F (uniformizer F : F) := mul_le_mul_left hz1 _
      _ < 1 := by rw [one_mul]; exact valuation_uniformizer_lt_one F
  rw [← hdet]
  have hne : ((M.det : 𝒪[F]) : F) ≠ 0 := by
    intro h0
    rw [h0, map_zero] at hv
    exact zero_ne_one hv
  refine modulus_eq_one_of_integral hne ?_ ?_
  · exact (Valuation.mem_integer_iff _ _).2 hv.le
  · refine (Valuation.mem_integer_iff _ _).2 ?_
    rw [map_inv₀, hv, inv_one]

/- English proof (translation)
Introduce `i j`. Establish `e : ((col n k y : Matrix (Fin n) (Fin n) F) - 1) i j = cM n k y i j` using `by show ((1 + cM n k y) - 1) i j = _`. Rewrite using `[add_sub_cancel_left]`. Rewrite using `[e]`. Distinguish the cases in `h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1`.

Take `⟨t, ht, e'⟩` from `hy ⟨i, h.2⟩`. Use `⟨t, ht, ?_⟩` and prove the remaining obligations. Simplify using `only [cM, Matrix.of_apply, dif_pos h]`. Conclude with `e'`. Use `⟨0, Subring.zero_mem _, ?_⟩` and prove the remaining obligations.

Simplify using `only [cM, Matrix.of_apply, dif_neg h, mul_zero]`.
-/
theorem div_col {n k c : ℕ} {y : Fin (k + 1) → F}
    (hy : ∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ c * t) :
    Div c ((col n k y : Matrix (Fin n) (Fin n) F) - 1) := by
  intro i j
  have e : ((col n k y : Matrix (Fin n) (Fin n) F) - 1) i j = cM n k y i j := by
    show ((1 + cM n k y) - 1) i j = _
    rw [add_sub_cancel_left]
  rw [e]
  by_cases h : (j : ℕ) = k + 1 ∧ (i : ℕ) < k + 1
  · obtain ⟨t, ht, e'⟩ := hy ⟨i, h.2⟩
    refine ⟨t, ht, ?_⟩
    simp only [cM, Matrix.of_apply, dif_pos h]
    exact e'
  · refine ⟨0, Subring.zero_mem _, ?_⟩
    simp only [cM, Matrix.of_apply, dif_neg h, mul_zero]

/- English proof (translation)
Introduce `h0 h2 h3 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hI u u'`. Take `⟨cu, hcu⟩` from `hρ u`. Take `⟨cv, hcv⟩` from `hρ u'`. Take `⟨hadd, -, -, -, -, hext⟩` from `h3 F μ ψ hψ n k hk`. Establish `hfix : ∀ g : GL (Fin n) F, Div (max cu cv + 1) ((g : Matrix (Fin n) (Fin n) F) - 1) → ρ g u = u ∧ ρ g u' = u'` using `fun g hg => ⟨hcu g (div_mono (by omega) hg), hcv g (div_mono (by omega) hg)⟩`.

Establish `hf1 : ∀ x y : Fin (k + 1) → F, (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (max cu cv + 1) * t) → B u' (ρ (col n k (x + y)) u) = B u' (ρ (col n k x) u)`. Introduce `x y hy`. Rewrite using `[hadd, map_mul, Module.End.mul_apply, (hfix _ (div_col hy)).1]`. Establish `hf2 : ∀ h : GL (Fin (k + 1)) F, Div (max cu cv + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) → ∀ x, B u' (ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u) = B u' (ρ (col n k x) u)`. Introduce `h hh x`.

Take `⟨g, hgP, hdet, hcomm, hdiv⟩` from `hext h`. Take `⟨gu, gu'⟩` from `hfix g (hdiv _ hh)`. Establish `hmod : Measures.modulus (g : Matrix (Fin n) (Fin n) F).det = 1`. Rewrite using `[← hdet]`. Conclude with `modulus_det_eq_one h hh`.

Establish `e : ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u = ρ g (ρ (col n k x) u)`. Use `congrArg (fun a => ρ a u) (hcomm x)` as an intermediate fact. Simplify using `only [map_mul, Module.End.mul_apply, gu] at this`. Conclude with `this.symm`. Establish `q` using `hI.quasi g hgP u' (ρ (col n k x) u)`.

Rewrite `q` using `[gu', hmod]`. Rewrite using `[e, q]`. Simplify using the standard rewrite rules. Establish `hcont : Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u))`. Use `IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)` and prove the remaining obligations.

Establish `hϖ : ((uniformizer F : F) ^ (max cu cv + 1)) ≠ 0`. Use `pow_ne_zero _ fun h => ?_` and prove the remaining obligations. Conclude with `valuation_uniformizer_ne_zero F (by rw [h, map_zero])`. Use `⟨(fun z : Fin (k + 1) → F => ((uniformizer F : F) ^ (max cu cv + 1))⁻¹ • (z - x)) ⁻¹' Measures.box F (Fin (k + 1)), Measures.isOpen_box.preimage (by fun_prop), ?_, ?_⟩` and prove the remaining obligations. Simplify using `using Measures.zero_mem_box`.

Introduce `x' hx'`. Use `hf1 x (x' - x) fun i => ⟨_, Measures.mem_box.1 hx' i, by` as an intermediate fact. Simplify using `[hϖ]⟩`. Simplify using `using this`. Conclude with `⟨hcont, max cu cv, fun g hg => h2 F μ ψ hψ k (max cu cv) (max cu cv + 1) _ hf1 hf2 g hg⟩`.
-/
theorem stability_coefficients : L0 → L2 → ColumnsMirabolic → FormCoefficientStability := by
  intro h0 h2 h3 F _ _ _ _ _ _ μ _ ψ hψ n V _ _ ρ hρ l k B hk hI u u'
  obtain ⟨cu, hcu⟩ := hρ u
  obtain ⟨cv, hcv⟩ := hρ u'
  obtain ⟨hadd, -, -, -, -, hext⟩ := h3 F μ ψ hψ n k hk
  have hfix : ∀ g : GL (Fin n) F, Div (max cu cv + 1) ((g : Matrix (Fin n) (Fin n) F) - 1) →
      ρ g u = u ∧ ρ g u' = u' := fun g hg =>
    ⟨hcu g (div_mono (by omega) hg), hcv g (div_mono (by omega) hg)⟩
  have hf1 : ∀ x y : Fin (k + 1) → F,
      (∀ i, ∃ t ∈ 𝒪[F], y i = (uniformizer F : F) ^ (max cu cv + 1) * t) →
      B u' (ρ (col n k (x + y)) u) = B u' (ρ (col n k x) u) := by
    intro x y hy
    rw [hadd, map_mul, Module.End.mul_apply, (hfix _ (div_col hy)).1]
  have hf2 : ∀ h : GL (Fin (k + 1)) F,
      Div (max cu cv + 1) ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) - 1) →
      ∀ x, B u' (ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u) =
        B u' (ρ (col n k x) u) := by
    intro h hh x
    obtain ⟨g, hgP, hdet, hcomm, hdiv⟩ := hext h
    obtain ⟨gu, gu'⟩ := hfix g (hdiv _ hh)
    have hmod : Measures.modulus (g : Matrix (Fin n) (Fin n) F).det = 1 := by
      rw [← hdet]
      exact modulus_det_eq_one h hh
    have e : ρ (col n k ((h : Matrix (Fin (k + 1)) (Fin (k + 1)) F) *ᵥ x)) u =
        ρ g (ρ (col n k x) u) := by
      have := congrArg (fun a => ρ a u) (hcomm x)
      simp only [map_mul, Module.End.mul_apply, gu] at this
      exact this.symm
    have q := hI.quasi g hgP u' (ρ (col n k x) u)
    rw [gu', hmod] at q
    rw [e, q]
    simp
  have hcont : Continuous (fun x : Fin (k + 1) → F => B u' (ρ (col n k x) u)) := by
    refine IsLocallyConstant.continuous ((IsLocallyConstant.iff_exists_open _).2 fun x => ?_)
    have hϖ : ((uniformizer F : F) ^ (max cu cv + 1)) ≠ 0 := by
      refine pow_ne_zero _ fun h => ?_
      exact valuation_uniformizer_ne_zero F (by rw [h, map_zero])
    refine ⟨(fun z : Fin (k + 1) → F => ((uniformizer F : F) ^ (max cu cv + 1))⁻¹ • (z - x)) ⁻¹'
      Measures.box F (Fin (k + 1)), Measures.isOpen_box.preimage (by fun_prop), ?_, ?_⟩
    · simpa using Measures.zero_mem_box
    · intro x' hx'
      have := hf1 x (x' - x) fun i => ⟨_, Measures.mem_box.1 hx' i, by
        simp [hϖ]⟩
      simpa using this
  exact ⟨hcont, max cu cv, fun g hg => h2 F μ ψ hψ k (max cu cv) (max cu cv + 1) _ hf1 hf2 g hg⟩

end GlobalTheory.CompanionTheory.JSBound
