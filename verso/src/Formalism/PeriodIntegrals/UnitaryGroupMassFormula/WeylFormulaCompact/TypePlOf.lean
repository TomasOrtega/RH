import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.FormulaStep
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeylFormulaCompact.TrivKtype

noncomputable section

namespace PI.WeylForKWork

open PI PI.UpqRep Matrix PI.WeylForKInhab

/- English proof (translation)
Use `⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose, Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Simplify using `only [Pi.star_apply]`.

Rewrite using `[Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]`. Evaluate the numerical expressions. Use `show diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Jm ε = Jm ε * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))`. Unfold `Jm`. Rewrite using `[Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`.

Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `mul_comm _ _`.
-/
private theorem diagonal_exp_mem_Kset {N : ℕ} (ε : Fin N → Bool) (θ : Fin N → ℝ) :
    diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset ε := by
  refine ⟨?_, ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff, Matrix.star_eq_conjTranspose, Matrix.diagonal_conjTranspose,
      Matrix.diagonal_mul_diagonal, ← Matrix.diagonal_one]
    congr 1
    funext a
    simp only [Pi.star_apply]
    rw [Complex.star_def, Complex.mul_conj, Complex.normSq_eq_norm_sq, Complex.norm_exp_ofReal_mul_I]
    norm_num
  · show diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * Jm ε = Jm ε * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))
    unfold Jm
    rw [Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
    congr 1
    funext a
    exact mul_comm _ _

/- English proof (translation)
Introduce `θ _`. Take `⟨θ', h1, h2, h3⟩` from `(hD N ε).2.1 θ`. Use `show σ (iPl ε (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)))) u = _`. Rewrite using `[h3, hu θ' (diagonal_exp_mem_Kset ε θ'), show (∑ a, ν a * θ' a) = ∑ i, ν (ePl ε i) * θ' (ePl ε i) + ∑ j, ν (eMi ε j) * θ' (eMi ε j) from (hD N ε).1 (fun a => ν a * θ' a)]`. Simplify using `only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]`.
-/
private theorem isWtOn_sPl (hD : BlockDiag) {N : ℕ} (ε : Fin N → Bool) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ν : Fin N → ℝ) (u : H)
    (hu : IsWtOn (Kset ε) σ ν u) : IsWtOn (Kset (allPos (nPl ε))) (sPl ε σ) (fun i => ν (ePl ε i)) u := by
  intro θ _
  obtain ⟨θ', h1, h2, h3⟩ := (hD N ε).2.1 θ
  show σ (iPl ε (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)))) u = _
  rw [h3, hu θ' (diagonal_exp_mem_Kset ε θ'),
    show (∑ a, ν a * θ' a) = ∑ i, ν (ePl ε i) * θ' (ePl ε i) + ∑ j, ν (eMi ε j) * θ' (eMi ε j) from
      (hD N ε).1 (fun a => ν a * θ' a)]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, add_zero]

/- English proof (translation)
Introduce `θ _`. Take `⟨θ', h1, h2, h3⟩` from `(hD N ε).2.2 θ`. Use `show σ (iMi ε (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)))) u = _`. Rewrite using `[h3, hu θ' (diagonal_exp_mem_Kset ε θ'), show (∑ a, ν a * θ' a) = ∑ i, ν (ePl ε i) * θ' (ePl ε i) + ∑ j, ν (eMi ε j) * θ' (eMi ε j) from (hD N ε).1 (fun a => ν a * θ' a)]`. Simplify using `only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add]`.
-/
private theorem isWtOn_sMi (hD : BlockDiag) {N : ℕ} (ε : Fin N → Bool) {H : Type}
    [NormedAddCommGroup H] [InnerProductSpace ℂ H]
    (σ : Matrix (Fin N) (Fin N) ℂ → (H →L[ℂ] H)) (ν : Fin N → ℝ) (u : H)
    (hu : IsWtOn (Kset ε) σ ν u) : IsWtOn (Kset (allPos (nMi ε))) (sMi ε σ) (fun j => ν (eMi ε j)) u := by
  intro θ _
  obtain ⟨θ', h1, h2, h3⟩ := (hD N ε).2.2 θ
  show σ (iMi ε (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)))) u = _
  rw [h3, hu θ' (diagonal_exp_mem_Kset ε θ'),
    show (∑ a, ν a * θ' a) = ∑ i, ν (ePl ε i) * θ' (ePl ε i) + ∑ j, ν (eMi ε j) * θ' (eMi ε j) from
      (hD N ε).1 (fun a => ν a * θ' a)]
  simp only [h1, h2, mul_zero, Finset.sum_const_zero, zero_add]

/- English proof (translation)
Introduce `N ε Λ H _ _ σ S hσ hS`. Take `⟨hB1, hB2, hB3, hB4, hB5⟩` from `hB N ε`. Establish `hσP` using `(hB5 H σ hσ).1`. Use `haveI : FiniteDimensional ℂ S := hS.1`. Take `⟨v, hvS, hv0, hvw⟩` from `hS.2.2.2.1`.

Establish `hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S` using `fun h hh u hu => hS.2.1 _ (hB1 h hh) u hu`. Take `⟨X, hXS, hXst, hXirr, x, hxX, hx0, hxw⟩` from `hM (nPl ε) H (sPl ε σ) S (fun i => Λ (ePl ε i)) v hσP hS.1 hstP hvS hv0 (isWtOn_sPl hD ε σ Λ v hvw)`. Use `⟨X, hXS, Submodule.finiteDimensional_of_le hXS, hXst, hXirr, ⟨x, hxX, hx0, hxw⟩, ?_⟩` and prove the remaining obligations. Introduce `μ w hwX hw0 hww`. Set `Wμ : Submodule ℂ H` to `{ carrier := {u | u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) → sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u} add_mem' := fun hx hy …`.

Rewrite using `[map_add, hx.2 θ hθ, hy.2 θ hθ, smul_add]⟩`. Use the proof step `zero_mem' := ⟨S.zero_mem, fun θ _ => by rw [map_zero, smul_zero]⟩`. Use the proof step `smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun θ hθ => by`. Rewrite using `[map_smul, hx.2 θ hθ, smul_comm]⟩ }`. Establish `hmem : ∀ u, u ∈ Wμ ↔ (u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) → sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u)` using `fun u => Iff.rfl`.

Establish `hWst : ∀ θ : Fin N → ℝ, ∀ u ∈ Wμ, σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u ∈ Wμ`. Introduce `θ u hu`. Rewrite `hu`, the goal using `[hmem]`. Use `⟨hS.2.1 _ (diagonal_exp_mem_Kset ε θ) u hu.1, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨φ', -, -, hφ'⟩` from `(hD N ε).2.1 φ`.

Establish `hcomm : iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))`. Rewrite using `[hφ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `mul_comm _ _`.

Establish `hm1` using `hσ.1.2 _ (hB1 _ hφ) _ (diagonal_exp_mem_Kset ε θ)`. Establish `hm2` using `hσ.1.2 _ (diagonal_exp_mem_Kset ε θ) _ (hB1 _ hφ)`. Establish `hu2 : σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) u = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • u` using `hu.2 φ hφ`. Use `show σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) (σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u) = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hm1, hcomm, hm2, ContinuousLinearMap.comp_apply, hu2, map_smul]`.

Establish `hwW : w ∈ Wμ` using `(hmem w).2 ⟨hXS hwX, hww⟩`. Establish `hW0 : Wμ ≠ ⊥`. Introduce `h`. Rewrite `hwW` using `[h]`. Conclude with `hw0 ((Submodule.mem_bot ℂ).1 hwW)`.

Establish `hWS : Wμ ≤ S` using `fun u hu => ((hmem u).1 hu).1`. Use `haveI : FiniteDimensional ℂ Wμ := Submodule.finiteDimensional_of_le hWS`. Take `⟨ν, u, huW, hu0, huw⟩` from `hT N ε H σ Wμ hσ inferInstance hW0 hWst`. Establish `hCD` using `hS.2.2.2.2 ν u (hWS huW) hu0 huw`. Establish `hres` using `(hC N ε ν Λ hCD).1`.

Establish `hμν : μ = fun i => ν (ePl ε i)` using `hW (nPl ε) H (sPl ε σ) μ _ u hu0 ((hmem u).1 huW).2 (isWtOn_sPl hD ε σ ν u huw)`. Rewrite using `[hμν]`. Conclude with `hres`.
-/
theorem typePl_of (hB : Blocks) (hD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) : TypePl := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  have hσP := (hB5 H σ hσ).1
  haveI : FiniteDimensional ℂ S := hS.1
  obtain ⟨v, hvS, hv0, hvw⟩ := hS.2.2.2.1
  have hstP : IsKStableOn (allPos (nPl ε)) (sPl ε σ) S := fun h hh u hu => hS.2.1 _ (hB1 h hh) u hu
  obtain ⟨X, hXS, hXst, hXirr, x, hxX, hx0, hxw⟩ := hM (nPl ε) H (sPl ε σ) S
    (fun i => Λ (ePl ε i)) v hσP hS.1 hstP hvS hv0 (isWtOn_sPl hD ε σ Λ v hvw)
  refine ⟨X, hXS, Submodule.finiteDimensional_of_le hXS, hXst, hXirr, ⟨x, hxX, hx0, hxw⟩, ?_⟩
  intro μ w hwX hw0 hww
  let Wμ : Submodule ℂ H :=
    { carrier := {u | u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) →
          sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u}
      add_mem' := fun hx hy => ⟨S.add_mem hx.1 hy.1, fun θ hθ => by
        rw [map_add, hx.2 θ hθ, hy.2 θ hθ, smul_add]⟩
      zero_mem' := ⟨S.zero_mem, fun θ _ => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun θ hθ => by
        rw [map_smul, hx.2 θ hθ, smul_comm]⟩ }
  have hmem : ∀ u, u ∈ Wμ ↔ (u ∈ S ∧ ∀ θ : Fin (nPl ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nPl ε)) →
      sPl ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u) :=
    fun u => Iff.rfl
  have hWst : ∀ θ : Fin N → ℝ, ∀ u ∈ Wμ, σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u ∈ Wμ := by
    intro θ u hu
    rw [hmem] at hu ⊢
    refine ⟨hS.2.1 _ (diagonal_exp_mem_Kset ε θ) u hu.1, fun φ hφ => ?_⟩
    obtain ⟨φ', -, -, hφ'⟩ := (hD N ε).2.1 φ
    have hcomm : iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) := by
      rw [hφ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact mul_comm _ _
    have hm1 := hσ.1.2 _ (hB1 _ hφ) _ (diagonal_exp_mem_Kset ε θ)
    have hm2 := hσ.1.2 _ (diagonal_exp_mem_Kset ε θ) _ (hB1 _ hφ)
    have hu2 : σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) u = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • u :=
      hu.2 φ hφ
    show σ (iPl ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) (σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u) =
      Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u
    rw [← ContinuousLinearMap.comp_apply, ← hm1, hcomm, hm2, ContinuousLinearMap.comp_apply, hu2, map_smul]
  have hwW : w ∈ Wμ := (hmem w).2 ⟨hXS hwX, hww⟩
  have hW0 : Wμ ≠ ⊥ := by
    intro h
    rw [h] at hwW
    exact hw0 ((Submodule.mem_bot ℂ).1 hwW)
  have hWS : Wμ ≤ S := fun u hu => ((hmem u).1 hu).1
  haveI : FiniteDimensional ℂ Wμ := Submodule.finiteDimensional_of_le hWS
  obtain ⟨ν, u, huW, hu0, huw⟩ := hT N ε H σ Wμ hσ inferInstance hW0 hWst
  have hCD := hS.2.2.2.2 ν u (hWS huW) hu0 huw
  have hres := (hC N ε ν Λ hCD).1
  have hμν : μ = fun i => ν (ePl ε i) :=
    hW (nPl ε) H (sPl ε σ) μ _ u hu0 ((hmem u).1 huW).2 (isWtOn_sPl hD ε σ ν u huw)
  rw [hμν]
  exact hres

/- English proof (translation)
Introduce `N ε Λ H _ _ σ S hσ hS`. Take `⟨hB1, hB2, hB3, hB4, hB5⟩` from `hB N ε`. Establish `hσP` using `(hB5 H σ hσ).2`. Use `haveI : FiniteDimensional ℂ S := hS.1`. Take `⟨v, hvS, hv0, hvw⟩` from `hS.2.2.2.1`.

Establish `hstP : IsKStableOn (allPos (nMi ε)) (sMi ε σ) S` using `fun h hh u hu => hS.2.1 _ (hB2 h hh) u hu`. Take `⟨X, hXS, hXst, hXirr, x, hxX, hx0, hxw⟩` from `hM (nMi ε) H (sMi ε σ) S (fun j => Λ (eMi ε j)) v hσP hS.1 hstP hvS hv0 (isWtOn_sMi hD ε σ Λ v hvw)`. Use `⟨X, hXS, Submodule.finiteDimensional_of_le hXS, hXst, hXirr, ⟨x, hxX, hx0, hxw⟩, ?_⟩` and prove the remaining obligations. Introduce `μ w hwX hw0 hww`. Set `Wμ : Submodule ℂ H` to `{ carrier := {u | u ∈ S ∧ ∀ θ : Fin (nMi ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nMi ε)) → sMi ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u} add_mem' := fun hx hy …`.

Rewrite using `[map_add, hx.2 θ hθ, hy.2 θ hθ, smul_add]⟩`. Use the proof step `zero_mem' := ⟨S.zero_mem, fun θ _ => by rw [map_zero, smul_zero]⟩`. Use the proof step `smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun θ hθ => by`. Rewrite using `[map_smul, hx.2 θ hθ, smul_comm]⟩ }`. Establish `hmem : ∀ u, u ∈ Wμ ↔ (u ∈ S ∧ ∀ θ : Fin (nMi ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nMi ε)) → sMi ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u)` using `fun u => Iff.rfl`.

Establish `hWst : ∀ θ : Fin N → ℝ, ∀ u ∈ Wμ, σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u ∈ Wμ`. Introduce `θ u hu`. Rewrite `hu`, the goal using `[hmem]`. Use `⟨hS.2.1 _ (diagonal_exp_mem_Kset ε θ) u hu.1, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨φ', -, -, hφ'⟩` from `(hD N ε).2.2 φ`.

Establish `hcomm : iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))`. Rewrite using `[hφ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]`. Use `congr 1`. Use function extensionality and compare the values at `a`. Conclude with `mul_comm _ _`.

Establish `hm1` using `hσ.1.2 _ (hB2 _ hφ) _ (diagonal_exp_mem_Kset ε θ)`. Establish `hm2` using `hσ.1.2 _ (diagonal_exp_mem_Kset ε θ) _ (hB2 _ hφ)`. Establish `hu2 : σ (iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) u = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • u` using `hu.2 φ hφ`. Use `show σ (iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) (σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u) = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u`. Rewrite using `[← ContinuousLinearMap.comp_apply, ← hm1, hcomm, hm2, ContinuousLinearMap.comp_apply, hu2, map_smul]`.

Establish `hwW : w ∈ Wμ` using `(hmem w).2 ⟨hXS hwX, hww⟩`. Establish `hW0 : Wμ ≠ ⊥`. Introduce `h`. Rewrite `hwW` using `[h]`. Conclude with `hw0 ((Submodule.mem_bot ℂ).1 hwW)`.

Establish `hWS : Wμ ≤ S` using `fun u hu => ((hmem u).1 hu).1`. Use `haveI : FiniteDimensional ℂ Wμ := Submodule.finiteDimensional_of_le hWS`. Take `⟨ν, u, huW, hu0, huw⟩` from `hT N ε H σ Wμ hσ inferInstance hW0 hWst`. Establish `hCD` using `hS.2.2.2.2 ν u (hWS huW) hu0 huw`. Establish `hres` using `(hC N ε ν Λ hCD).2`.

Establish `hμν : μ = fun j => ν (eMi ε j)` using `hW (nMi ε) H (sMi ε σ) μ _ u hu0 ((hmem u).1 huW).2 (isWtOn_sMi hD ε σ ν u huw)`. Rewrite using `[hμν]`. Conclude with `hres`.
-/
theorem typeMi_of (hB : Blocks) (hD : BlockDiag) (hT : TorusWt) (hW : WtUniq) (hM : MinIrr)
    (hC : CDomRes) : TypeMi := by
  intro N ε Λ H _ _ σ S hσ hS
  obtain ⟨hB1, hB2, hB3, hB4, hB5⟩ := hB N ε
  have hσP := (hB5 H σ hσ).2
  haveI : FiniteDimensional ℂ S := hS.1
  obtain ⟨v, hvS, hv0, hvw⟩ := hS.2.2.2.1
  have hstP : IsKStableOn (allPos (nMi ε)) (sMi ε σ) S := fun h hh u hu => hS.2.1 _ (hB2 h hh) u hu
  obtain ⟨X, hXS, hXst, hXirr, x, hxX, hx0, hxw⟩ := hM (nMi ε) H (sMi ε σ) S
    (fun j => Λ (eMi ε j)) v hσP hS.1 hstP hvS hv0 (isWtOn_sMi hD ε σ Λ v hvw)
  refine ⟨X, hXS, Submodule.finiteDimensional_of_le hXS, hXst, hXirr, ⟨x, hxX, hx0, hxw⟩, ?_⟩
  intro μ w hwX hw0 hww
  let Wμ : Submodule ℂ H :=
    { carrier := {u | u ∈ S ∧ ∀ θ : Fin (nMi ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nMi ε)) →
          sMi ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u}
      add_mem' := fun hx hy => ⟨S.add_mem hx.1 hy.1, fun θ hθ => by
        rw [map_add, hx.2 θ hθ, hy.2 θ hθ, smul_add]⟩
      zero_mem' := ⟨S.zero_mem, fun θ _ => by rw [map_zero, smul_zero]⟩
      smul_mem' := fun c x hx => ⟨S.smul_mem c hx.1, fun θ hθ => by
        rw [map_smul, hx.2 θ hθ, smul_comm]⟩ }
  have hmem : ∀ u, u ∈ Wμ ↔ (u ∈ S ∧ ∀ θ : Fin (nMi ε) → ℝ, diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) ∈ Kset (allPos (nMi ε)) →
      sMi ε σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u = Complex.exp (((∑ a, μ a * θ a : ℝ) : ℂ) * Complex.I) • u) :=
    fun u => Iff.rfl
  have hWst : ∀ θ : Fin N → ℝ, ∀ u ∈ Wμ, σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u ∈ Wμ := by
    intro θ u hu
    rw [hmem] at hu ⊢
    refine ⟨hS.2.1 _ (diagonal_exp_mem_Kset ε θ) u hu.1, fun φ hφ => ?_⟩
    obtain ⟨φ', -, -, hφ'⟩ := (hD N ε).2.2 φ
    have hcomm : iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) * diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) = diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I)) * iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I))) := by
      rw [hφ', Matrix.diagonal_mul_diagonal, Matrix.diagonal_mul_diagonal]
      congr 1
      funext a
      exact mul_comm _ _
    have hm1 := hσ.1.2 _ (hB2 _ hφ) _ (diagonal_exp_mem_Kset ε θ)
    have hm2 := hσ.1.2 _ (diagonal_exp_mem_Kset ε θ) _ (hB2 _ hφ)
    have hu2 : σ (iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) u = Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • u :=
      hu.2 φ hφ
    show σ (iMi ε (diagonal (fun a => Complex.exp ((φ a : ℂ) * Complex.I)))) (σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u) =
      Complex.exp (((∑ a, μ a * φ a : ℝ) : ℂ) * Complex.I) • σ (diagonal (fun a => Complex.exp ((θ a : ℂ) * Complex.I))) u
    rw [← ContinuousLinearMap.comp_apply, ← hm1, hcomm, hm2, ContinuousLinearMap.comp_apply, hu2, map_smul]
  have hwW : w ∈ Wμ := (hmem w).2 ⟨hXS hwX, hww⟩
  have hW0 : Wμ ≠ ⊥ := by
    intro h
    rw [h] at hwW
    exact hw0 ((Submodule.mem_bot ℂ).1 hwW)
  have hWS : Wμ ≤ S := fun u hu => ((hmem u).1 hu).1
  haveI : FiniteDimensional ℂ Wμ := Submodule.finiteDimensional_of_le hWS
  obtain ⟨ν, u, huW, hu0, huw⟩ := hT N ε H σ Wμ hσ inferInstance hW0 hWst
  have hCD := hS.2.2.2.2 ν u (hWS huW) hu0 huw
  have hres := (hC N ε ν Λ hCD).2
  have hμν : μ = fun j => ν (eMi ε j) :=
    hW (nMi ε) H (sMi ε σ) μ _ u hu0 ((hmem u).1 huW).2 (isWtOn_sMi hD ε σ ν u huw)
  rw [hμν]
  exact hres

end PI.WeylForKWork
