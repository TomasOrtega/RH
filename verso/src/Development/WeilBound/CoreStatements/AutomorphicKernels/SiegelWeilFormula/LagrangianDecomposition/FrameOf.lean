import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.LagrangianDecomposition.SigSig

noncomputable section

open scoped TensorProduct NNReal Matrix Classical
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK.Dbl GlobalTheory.Cont PositivityTheory.Rg.Sw

namespace PositivityTheory.SiegelWeilFormula.Ald

open PositivityTheory.SiegelWeilFormula.Ald.YFA

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {σ : E →ₐ[F] E}

omit [NumberField F] in

/- English proof (translation)
Establish `h2 : (2 : E) ≠ 0` using `two_ne_zero`. Establish `ha : (2 : E)⁻¹ + (σ : E →+* E) (2 : E)⁻¹ = 1`. Rewrite using `[map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]`. Establish `hJ' : (J.map (σ : E →+* E))ᵀ = e₀ • J`. Use extensionality with `i j`.

Simplify using `using hJ i j`. Establish `hT' : (1 : GL (Fin n) E).1ᵀ * J * (1 : GL (Fin n) E).1.map (σ : E →+* E) * T.1.map (σ : E →+* E) = 1`. Establish `: (1 : Matrix (Fin n) (Fin n) E).map (σ : E →+* E) = 1` using `Matrix.map_one _ (map_zero _) (map_one _)`. Simplify `hT` using `[this]`. Use `⟨GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit (2 : E)⁻¹ T, GlobalTheory.ThK.Dbl.Frame.frame_gram (σ : E →+* E) hc he ha hJ' 1 T hT', toCols₁_wit T _⟩` and prove the remaining obligations.
-/
theorem frame_of {n : ℕ} (hc : ∀ z : E, σ (σ z) = z) {J : Matrix (Fin n) (Fin n) E} {e₀ : E} (he : e₀ * e₀ = 1)
    (hJ : ∀ i j, σ (J j i) = e₀ * J i j) (T : GL (Fin n) E) (hT : J * T.1.map σ = 1) :
    ∃ b : GL (Fin n ⊕ Fin n) E, b.1ᵀ * dbl J * b.1.map σ = Matrix.fromBlocks 0 1 (e₀ • 1) 0 ∧
      ∃ t : GL (Fin n) E, b.1.toCols₁ = diagCols (Fin n) * t.1 := by
  have h2 : (2 : E) ≠ 0 := two_ne_zero
  have ha : (2 : E)⁻¹ + (σ : E →+* E) (2 : E)⁻¹ = 1 := by
    rw [map_inv₀, map_ofNat, ← two_mul, mul_inv_cancel₀ h2]
  have hJ' : (J.map (σ : E →+* E))ᵀ = e₀ • J := by
    ext i j
    simpa using hJ i j
  have hT' : (1 : GL (Fin n) E).1ᵀ * J * (1 : GL (Fin n) E).1.map (σ : E →+* E) * T.1.map (σ : E →+* E) = 1 := by
    have : (1 : Matrix (Fin n) (Fin n) E).map (σ : E →+* E) = 1 := Matrix.map_one _ (map_zero _) (map_one _)
    simpa [this] using hT
  refine ⟨GlobalTheory.ThK.Dbl.Frame.two 1 * GlobalTheory.ThK.Dbl.Frame.wit (2 : E)⁻¹ T,
    GlobalTheory.ThK.Dbl.Frame.frame_gram (σ : E →+* E) hc he ha hJ' 1 T hT', toCols₁_wit T _⟩

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d n hN hn`. Establish `hc : ∀ z : E, σ (σ z) = z` using `sig_sig' d.ok.good.cm`. Take `⟨ε, hε⟩` from `d.ok.frame.1`. Establish `hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E)` using `map_intCast σ _`. Break down `d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩` into its components or cases.

Take `⟨ξ, hξ, hσξ⟩` from `GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ d.B d.ok.good`. Establish `hξ' : -ξ ≠ 0` using `neg_ne_zero.2 hξ`. Set `J : Matrix (Fin n) (Fin n) E` to `ξ • 1`. Establish `hJ : ∀ i j, σ (J j i) = (-1) * J i j` using `fun i j => by`. Distinguish the cases in `h : i = j`.

Substitute `h` using the available equality. Simplify using `[J, hσξ]`. Simplify using `[J, Matrix.one_apply, h, Ne.symm h]`. Set `T : GL (Fin n) E` to `⟨(-ξ)⁻¹ • 1, (-ξ) • 1, by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul], by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩`. Establish `hm : T.1.map σ = ξ⁻¹ • 1`.

Use extensionality with `i j`. Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[T, map_inv₀, hσξ]`. Simplify using `[T, Matrix.one_apply, h]`.

Establish `hT : J * T.1.map σ = 1`. Rewrite using `[hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]`. Take `⟨b, hb, hd⟩` from `frame_of hc (by norm_num) hJ T hT`. Establish `hεv : ((ε : ℤ) : E) = -1` using `eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ`. Apply the tactic sequence `refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>`.

Apply the tactic sequence `change b.1ᵀ * dbl J * b.1.map σ = _ try simp only [jeps]`. Rewrite using `[hεv]`. Conclude with `hb`. Set `J : Matrix (Fin n) (Fin n) E` to `1`. Establish `hJ : ∀ i j, σ (J j i) = 1 * J i j` using `fun i j => by`.

Distinguish the cases in `h : i = j`. Substitute `h` using the available equality. Simplify using `[J]`. Simplify using `[J, Matrix.one_apply, h, Ne.symm h]`. Establish `hT : J * (1 : GL (Fin n) E).1.map σ = 1`.

Simplify using `[J, Matrix.map_one _ (map_zero σ) (map_one σ)]`. Take `⟨b, hb, hd⟩` from `frame_of hc (by norm_num) hJ 1 hT`. Establish `hεv : ((ε : ℤ) : E) = 1` using `eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ`. Apply the tactic sequence `refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>`. Apply the tactic sequence `change b.1ᵀ * dbl J * b.1.map σ = _ try simp only [jeps]`.

Rewrite using `[hεv]`. Conclude with `hb`.
-/
theorem yFrame : YFrame := by
  intro F E _ _ _ _ _ σ d n hN hn
  have hc : ∀ z : E, σ (σ z) = z := sig_sig' d.ok.good.cm
  obtain ⟨ε, hε⟩ := d.ok.frame.1
  have hεσ : σ (((ε : ℤ) : E)) = ((ε : ℤ) : E) := map_intCast σ _
  rcases d.ok.sign with ⟨hA, hY⟩ | ⟨hA, hY⟩
  · obtain ⟨ξ, hξ, hσξ⟩ := GlobalTheory.T.exists_ne_zero_conj_neg_of_cmExtension F E σ d.B d.ok.good
    have hξ' : -ξ ≠ 0 := neg_ne_zero.2 hξ
    let J : Matrix (Fin n) (Fin n) E := ξ • 1
    have hJ : ∀ i j, σ (J j i) = (-1) * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J, hσξ]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    let T : GL (Fin n) E := ⟨(-ξ)⁻¹ • 1, (-ξ) • 1,
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, inv_mul_cancel₀ hξ', one_smul],
      by rw [Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ', one_smul]⟩
    have hm : T.1.map σ = ξ⁻¹ • 1 := by
      ext i j
      by_cases h : i = j
      · subst h; simp [T, map_inv₀, hσξ]
      · simp [T, Matrix.one_apply, h]
    have hT : J * T.1.map σ = 1 := by
      rw [hm, Matrix.smul_mul, Matrix.mul_smul, Matrix.one_mul, smul_smul, mul_inv_cancel₀ hξ, one_smul]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ T hT
    have hεv : ((ε : ℤ) : E) = -1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inl ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = -J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb
  · let J : Matrix (Fin n) (Fin n) E := 1
    have hJ : ∀ i j, σ (J j i) = 1 * J i j := fun i j => by
      by_cases h : i = j
      · subst h; simp [J]
      · simp [J, Matrix.one_apply, h, Ne.symm h]
    have hT : J * (1 : GL (Fin n) E).1.map σ = 1 := by
      simp [J, Matrix.map_one _ (map_zero σ) (map_one σ)]
    obtain ⟨b, hb, hd⟩ := frame_of hc (by norm_num) hJ 1 hT
    have hεv : ((ε : ℤ) : E) = 1 :=
      eps_eq (by omega) hc (fun i j => by rw [hY]; ring) hε hεσ
    refine ⟨spcOf F J, b, ε, Or.inr ⟨hA, fun i j => (by simpa using hJ i j : σ (J j i) = J i j)⟩, ⟨⟨ε, ?_⟩, hd⟩, hε, ?_⟩ <;>
      · change b.1ᵀ * dbl J * b.1.map σ = _
        try simp only [jeps]
        rw [hεv]; exact hb

end PositivityTheory.SiegelWeilFormula.Ald

end
