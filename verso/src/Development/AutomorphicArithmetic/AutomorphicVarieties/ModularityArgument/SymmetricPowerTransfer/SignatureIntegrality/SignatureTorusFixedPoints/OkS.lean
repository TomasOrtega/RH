import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.IsIntegralLf
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.FinFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.SignatureTorusFixedPoints.Contract
import Development.AutomorphicArithmetic.AutomorphicVarieties.ModularityArgument.SymmetricPowerTransfer.SignatureIntegrality.HodgeTateFromSandwich

noncomputable section

open ValuativeRel Matrix Polynomial GlobalTheory.SmGL GlobalTheory.SplitWeil UpperTheory.V.Hi UpperTheory.V.AlgebraTools UpperTheory.V.Z.Sym UpperTheory.V.Z.Sym.Sig UpperTheory.V.Z.Sym.Loc UpperTheory.V.Z.Sym.Glob

/- English proof (translation)
Introduce `k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht`. Introduce `S`. Take `⟨-, -, -, -, hdt, -⟩` from `eD_facts k O hO h2 Δ s hs hs0`. Take `⟨-, -, -, -, -, hJ⟩` from `finFacts k V`. Establish `key : ∀ y : ↥(DX Δ), S.fS t y ≠ 0 ↔ eD hs y ∈ V.DC ![t, t⁻¹]`.

Introduce `y`. Use `show Glob.one (eD hs y ∈ V.DC ![t, t⁻¹]) ≠ 0 ↔ _`. Unfold `Glob.one`. Apply the tactic sequence `split_ifs with h <;> simp [h]`. Establish `dcL : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, a * g ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹]`.

Introduce `a ha g`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨a', ha', b, hb, e⟩`. Use `⟨a⁻¹ * a', mul_mem (inv_mem ha) ha', b, hb, ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation.

Introduce and unpack `⟨a', ha', b, hb, e⟩`. Conclude with `⟨a * a', mul_mem ha ha', b, hb, by rw [e]; group⟩`. Establish `dcR : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, g * a ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹]`. Introduce `a ha g`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨a', ha', b, hb, e⟩`. Use `⟨a', ha', b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩` and prove the remaining obligations. Combine the equalities or inequalities in the displayed calculation. Introduce and unpack `⟨a', ha', b, hb, e⟩`. Conclude with `⟨a', ha', b * a, mul_mem hb ha, by rw [e]; group⟩`.

Establish `fSdef : ∀ y : ↥(DX Δ), S.fS t y = Glob.one (eD hs y ∈ V.DC ![t, t⁻¹])` using `fun y => rfl`. Use `⟨?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `u hu y`. Establish `hu' : eD hs u ∈ V.J 2` using `hu`. Rewrite using `[fSdef, fSdef, fSdef, map_mul, map_mul, dcL _ hu', dcR _ hu']`.

Conclude with `⟨rfl, rfl⟩`. Establish `horb` using `(hJ 2).1 (dg ![t, t⁻¹])`. Use `Set.Finite.of_finite_image (f := fun x : ↥(SU Δ) ⧸ S.J2.subgroupOf (SU Δ) => ((eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2)) (horb.subset ?_) ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`. Take `⟨a, ha, b, hb, e⟩` from `(key _).1 hx`.

Use `⟨⟨a, ha⟩, ?_⟩` and prove the remaining obligations. Simplify using `only`. Rewrite using `[e]`. Use `show (a : GL (Fin 2) k) • ((dg ![t, t⁻¹] : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2) = _`. Rewrite using `[MulAction.Quotient.smul_mk, QuotientGroup.eq]`.

Simplify `hb` using `[mul_assoc]`. Introduce `x _ y _ hxy`. Establish `h1 : (eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)))⁻¹ * eD hs ((Quotient.out y : ↥(SU Δ)) : ↥(DX Δ)) ∈ V.J 2` using `QuotientGroup.eq.1 hxy`. Rewrite `h1` using `[← map_inv, ← map_mul]`. Establish `h3 : (Quotient.out x)⁻¹ * Quotient.out y ∈ S.J2.subgroupOf (SU Δ)` using `h1`.

Rewrite using `[← Quotient.out_eq x, ← Quotient.out_eq y]`. Conclude with `QuotientGroup.eq.2 h3`. Introduce and unpack `γ τ ⟨hdet, htr⟩ hne`. Establish `hmem` using `(key γ).1 hne`. Establish `hv1 : valuation k (t : k) < 1`.

Establish `ht' : valuation k (t : k) < valuation k ((unif k : kˣ) : k) ^ 2` using `ht`. Use `ht'.trans_le ?_` and prove the remaining obligations. Rewrite using `[GlAx.unif_spec]`. Conclude with `pow_le_one₀ zero_le' (ValuativeRel.uniformizer_lt_one (R := k)).le`. Establish `hprod : valuation k ((t⁻¹ : kˣ) : k) * valuation k (t : k) = 1`.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`. Establish `hlt : valuation k (t : k) < valuation k ((t⁻¹ : kˣ) : k)`. Use `lt_of_not_ge fun hle => ?_` and prove the remaining obligations. Conclude with `(mul_lt_of_le_one_of_lt (hle.trans hv1.le) hv1).ne hprod`. Establish `hd : SDom ![t, t⁻¹]`.

Introduce `i j hij`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `absurd hij (by decide)`. Conclude with `hlt`. Conclude with `absurd hij (by decide)`.

Conclude with `absurd hij (by decide)`. Take `⟨j, -, w, hw, e⟩` from `contract k V 2 (MonoidHom.id _) (pres_id V 2) ![t, t⁻¹] hd _ hmem`. Take `⟨d, hdmem, rfl⟩` from `hw`. Establish `hd0 : d 0 ∈ V.H` using `hdmem 0 (Set.mem_univ _)`. Rewrite `e` using `[MonoidHom.id_apply]`.

Establish `hc : ((j⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (j : Matrix (Fin 2) (Fin 2) k) = diagonal fun i => (((d * ![t, t⁻¹]) i : kˣ) : k)`. Rewrite using `[← Units.val_mul, ← Units.val_mul, e]`. Unfold `dg`. Rewrite using `[← map_mul, val_diagT]`. Establish `hD` using `Matrix.det_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)`.

Establish `hT` using `Matrix.trace_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)`. Rewrite `hD`, `hT` using `[hc]`. Establish `inj` using `(algebraMap k (Lsq k Δ)).injective`. Establish `hdet1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1` using `inj (by rw [← (hdt γ).1, hdet, map_one])`. Establish `htr1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = τ` using `inj (by rw [← (hdt γ).2, htr])`.

Rewrite `hD` using `[hdet1, Matrix.det_diagonal, Fin.prod_univ_two]`. Rewrite `hT` using `[htr1, Matrix.trace_diagonal, Fin.sum_univ_two]`. Simplify using `only [Pi.mul_apply, Units.val_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hD hT`. Establish `hinv : (t * d 0)⁻¹ = d 1 * t⁻¹`. Use `inv_eq_of_mul_eq_one_right (Units.ext ?_)` and prove the remaining obligations.

Simplify using `only [Units.val_mul, Units.val_one]`. Take the linear combination `hD`. Use `⟨d 0, hd0, ?_⟩` and prove the remaining obligations. Rewrite using `[hinv, Units.val_mul, Units.val_mul, ← hT]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem UpperTheory.V.Z.Sym.Sig.okS : UpperTheory.V.Z.Sym.Sig.OkS := by
  intro k _ _ _ _ O _ _ hO h2 Δ s hs hs0 V Ry hR χ hχ t ht
  intro S
  classical
  obtain ⟨-, -, -, -, hdt, -⟩ := eD_facts k O hO h2 Δ s hs hs0
  obtain ⟨-, -, -, -, -, hJ⟩ := finFacts k V
  have key : ∀ y : ↥(DX Δ), S.fS t y ≠ 0 ↔ eD hs y ∈ V.DC ![t, t⁻¹] := by
    intro y
    show Glob.one (eD hs y ∈ V.DC ![t, t⁻¹]) ≠ 0 ↔ _
    unfold Glob.one
    split_ifs with h <;> simp [h]
  have dcL : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, a * g ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹] := by
    intro a ha g
    constructor
    · rintro ⟨a', ha', b, hb, e⟩
      refine ⟨a⁻¹ * a', mul_mem (inv_mem ha) ha', b, hb, ?_⟩
      calc g = a⁻¹ * (a * g) := by group
        _ = a⁻¹ * a' * dg ![t, t⁻¹] * b := by rw [e]; group
    · rintro ⟨a', ha', b, hb, e⟩
      exact ⟨a * a', mul_mem ha ha', b, hb, by rw [e]; group⟩
  have dcR : ∀ a ∈ V.J 2, ∀ g : GL (Fin 2) k, g * a ∈ V.DC ![t, t⁻¹] ↔ g ∈ V.DC ![t, t⁻¹] := by
    intro a ha g
    constructor
    · rintro ⟨a', ha', b, hb, e⟩
      refine ⟨a', ha', b * a⁻¹, mul_mem hb (inv_mem ha), ?_⟩
      calc g = (g * a) * a⁻¹ := by group
        _ = a' * dg ![t, t⁻¹] * (b * a⁻¹) := by rw [e]; group
    · rintro ⟨a', ha', b, hb, e⟩
      exact ⟨a', ha', b * a, mul_mem hb ha, by rw [e]; group⟩
  have fSdef : ∀ y : ↥(DX Δ), S.fS t y = Glob.one (eD hs y ∈ V.DC ![t, t⁻¹]) := fun y => rfl
  refine ⟨?_, ?_, ?_⟩
  · intro u hu y
    have hu' : eD hs u ∈ V.J 2 := hu
    rw [fSdef, fSdef, fSdef, map_mul, map_mul, dcL _ hu', dcR _ hu']
    exact ⟨rfl, rfl⟩
  · have horb := (hJ 2).1 (dg ![t, t⁻¹])
    refine Set.Finite.of_finite_image
      (f := fun x : ↥(SU Δ) ⧸ S.J2.subgroupOf (SU Δ) =>
        ((eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)) : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2))
      (horb.subset ?_) ?_
    · rintro _ ⟨x, hx, rfl⟩
      obtain ⟨a, ha, b, hb, e⟩ := (key _).1 hx
      refine ⟨⟨a, ha⟩, ?_⟩
      dsimp only
      rw [e]
      show (a : GL (Fin 2) k) • ((dg ![t, t⁻¹] : GL (Fin 2) k) : GL (Fin 2) k ⧸ V.J 2) = _
      rw [MulAction.Quotient.smul_mk, QuotientGroup.eq]
      simpa [mul_assoc] using hb
    · intro x _ y _ hxy
      have h1 : (eD hs ((Quotient.out x : ↥(SU Δ)) : ↥(DX Δ)))⁻¹ * eD hs ((Quotient.out y : ↥(SU Δ)) : ↥(DX Δ)) ∈ V.J 2 :=
        QuotientGroup.eq.1 hxy
      rw [← map_inv, ← map_mul] at h1
      have h3 : (Quotient.out x)⁻¹ * Quotient.out y ∈ S.J2.subgroupOf (SU Δ) := h1
      rw [← Quotient.out_eq x, ← Quotient.out_eq y]
      exact QuotientGroup.eq.2 h3
  · rintro γ τ ⟨hdet, htr⟩ hne
    have hmem := (key γ).1 hne
    have hv1 : valuation k (t : k) < 1 := by
      have ht' : valuation k (t : k) < valuation k ((unif k : kˣ) : k) ^ 2 := ht
      refine ht'.trans_le ?_
      rw [GlAx.unif_spec]
      exact pow_le_one₀ zero_le' (ValuativeRel.uniformizer_lt_one (R := k)).le
    have hprod : valuation k ((t⁻¹ : kˣ) : k) * valuation k (t : k) = 1 := by
      rw [← map_mul, Units.inv_mul, map_one]
    have hlt : valuation k (t : k) < valuation k ((t⁻¹ : kˣ) : k) := by
      refine lt_of_not_ge fun hle => ?_
      exact (mul_lt_of_le_one_of_lt (hle.trans hv1.le) hv1).ne hprod
    have hd : SDom ![t, t⁻¹] := by
      intro i j hij
      fin_cases i <;> fin_cases j
      · exact absurd hij (by decide)
      · exact hlt
      · exact absurd hij (by decide)
      · exact absurd hij (by decide)
    obtain ⟨j, -, w, hw, e⟩ := contract k V 2 (MonoidHom.id _) (pres_id V 2) ![t, t⁻¹] hd _ hmem
    obtain ⟨d, hdmem, rfl⟩ := hw
    have hd0 : d 0 ∈ V.H := hdmem 0 (Set.mem_univ _)
    rw [MonoidHom.id_apply] at e
    have hc : ((j⁻¹ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) *
        ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k) * (j : Matrix (Fin 2) (Fin 2) k) =
        diagonal fun i => (((d * ![t, t⁻¹]) i : kˣ) : k) := by
      rw [← Units.val_mul, ← Units.val_mul, e]
      unfold dg
      rw [← map_mul, val_diagT]
    have hD := Matrix.det_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    have hT := Matrix.trace_units_conj' j ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k)
    rw [hc] at hD hT
    have inj := (algebraMap k (Lsq k Δ)).injective
    have hdet1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).det = 1 :=
      inj (by rw [← (hdt γ).1, hdet, map_one])
    have htr1 : ((eD hs γ : GL (Fin 2) k) : Matrix (Fin 2) (Fin 2) k).trace = τ :=
      inj (by rw [← (hdt γ).2, htr])
    rw [hdet1, Matrix.det_diagonal, Fin.prod_univ_two] at hD
    rw [htr1, Matrix.trace_diagonal, Fin.sum_univ_two] at hT
    simp only [Pi.mul_apply, Units.val_mul, Matrix.cons_val_zero, Matrix.cons_val_one, Matrix.head_cons] at hD hT
    have hinv : (t * d 0)⁻¹ = d 1 * t⁻¹ := by
      refine inv_eq_of_mul_eq_one_right (Units.ext ?_)
      simp only [Units.val_mul, Units.val_one]
      linear_combination hD
    refine ⟨d 0, hd0, ?_⟩
    rw [hinv, Units.val_mul, Units.val_mul, ← hT]
    ring

end
