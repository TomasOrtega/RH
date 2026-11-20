import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LayerLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.IvField
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostOdd
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.BchiFacts
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.LossLe
import Development.AutomorphicArithmetic.AutomorphicVarieties.HeightAndVanishing.HostIndex
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.LiftGens
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.H0LocalCardBoundedOfClsKerLeKer
import Development.AutomorphicArithmetic.AutomorphicVarieties.CharacterLevelBounds.FactLeLog
import Formalism.GaloisCohomology.GaloisCohomologyProofs.LdataNonempty

open NumberField IsDedekindDomain Formalism.ConjugateSelfDual Formalism.HC ReciprocityTheory.Gal Formalism.GaloisCohomology UpperTheory.V UpperTheory.V.Base UpperTheory.Top UpperTheory.V.HV

/- English proof (translation)
Establish `h1 : ∀ m : ℕ, 2 * m ≤ 2 ^ (m + 1)`. Introduce `m`. Proceed by induction on `m with`. Consider the case `zero => simp`. Consider the case `succ m ih`.

Establish `h2 : 2 ≤ 2 ^ (m + 1)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[pow_succ 2 (m + 1)]`. Use linear arithmetic over natural numbers and integers. Establish `hNt : 2 ≤ N * t` using `by nlinarith`.

Establish `h2 : 2 ^ (n + 1) ≤ (N * t) ^ (n + 1)` using `Nat.pow_le_pow_left hNt _`. Establish `h3 : N * t ^ 2 ≤ (N * t) ^ 2` using `by nlinarith`. Combine the equalities or inequalities in the displayed calculation. Use `(Finset.mem_Ico.1 he).2` as an intermediate fact. Conclude with `Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this.le)`.

Use `_ = (t - 1) * (n * (2 * N * t)) := by simp [Finset.sum_const, Nat.card_Ico]`. Use `_ ≤ t * (n * (2 * N * t)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)`. Use `_ = (2 * n) * (N * t ^ 2) := by ring`. Use `_ ≤ (N * t) ^ (n + 1) * (N * t) ^ 2 := Nat.mul_le_mul (le_trans (h1 n) h2) h3`. Use `_ = (N * t) ^ (n + 3) := by rw [← pow_add]`.
-/
private theorem sum_le (n N t : ℕ) (hN : 1 ≤ N) (ht : 2 ≤ t) :
    ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ (N * t) ^ (n + 3) := by
  have h1 : ∀ m : ℕ, 2 * m ≤ 2 ^ (m + 1) := by
    intro m
    induction m with
    | zero => simp
    | succ m ih =>
      have h2 : 2 ≤ 2 ^ (m + 1) :=
        calc 2 = 2 ^ 1 := by norm_num
          _ ≤ 2 ^ (m + 1) := Nat.pow_le_pow_right (by norm_num) (by omega)
      rw [pow_succ 2 (m + 1)]
      omega
  have hNt : 2 ≤ N * t := by nlinarith
  have h2 : 2 ^ (n + 1) ≤ (N * t) ^ (n + 1) := Nat.pow_le_pow_left hNt _
  have h3 : N * t ^ 2 ≤ (N * t) ^ 2 := by nlinarith
  calc ∑ e ∈ Finset.Ico 1 t, n * (2 * N * e) ≤ ∑ e ∈ Finset.Ico 1 t, n * (2 * N * t) :=
        Finset.sum_le_sum fun e he => by
          have := (Finset.mem_Ico.1 he).2
          exact Nat.mul_le_mul_left _ (Nat.mul_le_mul_left _ this.le)
    _ = (t - 1) * (n * (2 * N * t)) := by simp [Finset.sum_const, Nat.card_Ico]
    _ ≤ t * (n * (2 * N * t)) := Nat.mul_le_mul_right _ (Nat.sub_le _ _)
    _ = (2 * n) * (N * t ^ 2) := by ring
    _ ≤ (N * t) ^ (n + 1) * (N * t) ^ 2 := Nat.mul_le_mul (le_trans (h1 n) h2) h3
    _ = (N * t) ^ (n + 3) := by rw [← pow_add]

/- English proof (translation)
Introduce `χ l _ j hlB`. Take `⟨hlp, hl2⟩` from `prime_of_mem_Bchi hlB`. Use `⟨l * χ.N * l ^ j + 3, ?_⟩` and prove the remaining obligations. Introduce `h hχ t ht hbig B hLay Ω _ _ _ c ψ hψ hodd`. Use `haveI := c.dvr`.

Use `haveI := c.fin`. Establish `hNpos : 0 < h.N` using `Host.N_pos h`. Establish `hN16` using `(hostIndex h).2.2.1`. Establish `hN2 : 2 ≤ h.N` using `le_trans (by norm_num) (Nat.le_of_dvd hNpos hN16)`. Establish `hbf` using `bchiFacts h t hbig`.

Establish `hlB' : l ∈ Bchi h.chi` using `by rw [hχ]; exact hlB`. Establish `hlq1 : l ≠ h.q1` using `(hbf.1 l hlB').1.ne`. Establish `hld : l ≠ h.d` using `(hbf.1 l hlB').2.ne`. Establish `hcond : ψ.conductor ∣ χ.N`. Use `((hostOdd h c.O ψ hψ).2 l hlp hl2 hlq1 hld hodd).1` as an intermediate fact.

Rewrite using `[← hχ]`. Conclude with `this`. Take `⟨L₀, _, _, L₁, _, _, _, _, _, _, hAb, hLayer, hdeg, hker⟩` from `ivField χ l j hl2 Ω`. Establish `hgal` using `hker c.O h.N ψ hcond`. Take `⟨D⟩` from `ldata_nonempty (F := L₁) (Ω := Ω) l`.

Establish `hVV` using `hLay L₀ hAb L₁ hLayer Ω D`. Establish `hT : Subgroup.closure ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)) : Set (L₁ ≃ₐ[ℚ] L₁)) = ⊤` using `by simp`. Establish `hcard : (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card ≤ l * χ.N * l ^ j`. Rewrite using `[Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]`. Conclude with `hdeg`.

Establish `hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker`. Introduce `σ hσ`. Rewrite `hσ`, the goal using `[MonoidHom.mem_ker]`. Simplify using `[Chr.dirG, hσ]`. Establish `hb : ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e ≤ (h.N * t) ^ (l * χ.N * l ^ j + 3)`.

Combine the equalities or inequalities in the displayed calculation. Use `Chr.nuSum.2 l c.O (fun e => Vlen Ω c e ψ) (fun e => shaLen D (e : ℤ)) (fun e => (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e) t B _ ?_ hVV.2 ?_` and prove the remaining obligations. Introduce `e he1 he2`. Use `⟨hVV.1 e he1 he2, ?_⟩` and prove the remaining obligations. Establish `h1` using `Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N e (Chr.dirG ℚ Ω ψ)`.

Establish `h2` using `Chr.upV ℚ Ω L₁ l c.O D e (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT`. Establish `h3` using `(Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N e (Chr.dirG ℚ Ω ψ) he1.ne' hclsker).2`. Combine the equalities or inequalities in the displayed calculation. Conclude with `hb` after adjusting the coercions.
-/
theorem UpperTheory.V.HV.countIV :
    CountIV := by
  intro χ l _ j hlB
  obtain ⟨hlp, hl2⟩ := prime_of_mem_Bchi hlB
  refine ⟨l * χ.N * l ^ j + 3, ?_⟩
  intro h hχ t ht hbig B hLay Ω _ _ _ c ψ hψ hodd
  haveI := c.dvr
  haveI := c.fin
  have hNpos : 0 < h.N := Host.N_pos h
  have hN16 := (hostIndex h).2.2.1
  have hN2 : 2 ≤ h.N := le_trans (by norm_num) (Nat.le_of_dvd hNpos hN16)
  have hbf := bchiFacts h t hbig
  have hlB' : l ∈ Bchi h.chi := by rw [hχ]; exact hlB
  have hlq1 : l ≠ h.q1 := (hbf.1 l hlB').1.ne
  have hld : l ≠ h.d := (hbf.1 l hlB').2.ne
  have hcond : ψ.conductor ∣ χ.N := by
    have := ((hostOdd h c.O ψ hψ).2 l hlp hl2 hlq1 hld hodd).1
    rw [← hχ]
    exact this
  obtain ⟨L₀, _, _, L₁, _, _, _, _, _, _, hAb, hLayer, hdeg, hker⟩ := ivField χ l j hl2 Ω
  have hgal := hker c.O h.N ψ hcond
  obtain ⟨D⟩ := ldata_nonempty (F := L₁) (Ω := Ω) l
  have hVV := hLay L₀ hAb L₁ hLayer Ω D
  have hT : Subgroup.closure ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)) : Set (L₁ ≃ₐ[ℚ] L₁)) = ⊤ := by simp
  have hcard : (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card ≤ l * χ.N * l ^ j := by
    rw [Finset.card_univ, ← Nat.card_eq_fintype_card, IsGalois.card_aut_eq_finrank]
    exact hdeg
  have hclsker : (Chr.cls ℚ Ω h.N).ker ≤ (Chr.dirG ℚ Ω ψ).ker := by
    intro σ hσ
    rw [MonoidHom.mem_ker] at hσ ⊢
    simp [Chr.dirG, hσ]
  have hb : ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e
      ≤ (h.N * t) ^ (l * χ.N * l ^ j + 3) := by
    calc _ ≤ ∑ e ∈ Finset.Ico 1 t, (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * (2 * h.N * e) :=
          Finset.sum_le_sum fun e he => Nat.mul_le_mul_left _
            (lossLe l h.N 0 e hlp hl2 hN2 (Nat.zero_le _) (Finset.mem_Ico.1 he).1).2
      _ ≤ (h.N * t) ^ ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card + 3) := sum_le _ h.N t (by omega) ht
      _ ≤ _ := Nat.pow_le_pow_right (Nat.mul_pos hNpos (by omega)) (by omega)
  refine Chr.nuSum.2 l c.O (fun e => Vlen Ω c e ψ) (fun e => shaLen D (e : ℤ))
    (fun e => (Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card * LDataCardLeFinrank.nuBound l h.N e) t B _ ?_ hVV.2 ?_
  · intro e he1 he2
    refine ⟨hVV.1 e he1 he2, ?_⟩
    have h1 := Chr.V'_le_V (k := ℚ) (Ω := Ω) l h.N e (Chr.dirG ℚ Ω ψ)
    have h2 := Chr.upV ℚ Ω L₁ l c.O D e (Chr.dirG ℚ Ω ψ) hgal Finset.univ hT
    have h3 := (Chr.H0_local_card_bounded_of_cls_ker_le_ker Ω l c.O h.N e (Chr.dirG ℚ Ω ψ) he1.ne' hclsker).2
    calc Vlen Ω c e ψ ≤ Chr.V l e (Chr.dirG ℚ Ω ψ) := h1
      _ ≤ _ := h2
      _ ≤ shaLen D (e : ℤ) * eO l c.O + ((Finset.univ : Finset (L₁ ≃ₐ[ℚ] L₁)).card : ℕ∞) *
            ((LDataCardLeFinrank.nuBound l h.N e : ℕ∞) * eO l c.O) := by gcongr
      _ = _ := by push_cast; ring
  · exact_mod_cast hb
