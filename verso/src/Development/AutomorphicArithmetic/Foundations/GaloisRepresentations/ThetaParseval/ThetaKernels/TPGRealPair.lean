import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExistsAct1EquivariantNablaSqMapHittingJoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.ExistsAct2EquivariantNablaSqMapHittingJoint
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.JointNe
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.EmbBij
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.BlockDeterminants.ExponentialEntries.FormEx
import Development.AutomorphicArithmetic.AutomorphicVarieties.BuildingsResidueChars.ExistsTensorDualEmbeddingOfHasWeightAt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.SplitStab
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.HalfIndexLattices.IsLatRepL
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GalTPDefs
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.ThetaBasicK
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.ThetaParseval.ThetaKernels.GRPFockOf

set_option synthInstance.maxHeartbeats 200000

section
noncomputable section
open scoped TensorProduct Matrix Classical
open NumberField MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes Formalism.BasicNotions Formalism.BasicNotions.TH GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.FockAlg GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift UpperTheory.TP.RP
/- English proof (translation)
Use `MvPolynomial.algHom_ext fun l => ?_` and prove the remaining obligations. Break down `l with ⟨b | b, c | c⟩` into its components or cases. Simplify using `[rightSub, xv, Matrix.one_apply]`. Conclude with `c.elim0`. Conclude with `b.elim0`.

Conclude with `b.elim0`.
-/
private theorem rightSub_one_pk {n d : ℕ} : (rightSub 1 : PP n d →ₐ[ℂ] PP n d) = AlgHom.id ℂ _ := by
  refine MvPolynomial.algHom_ext fun l => ?_
  rcases l with ⟨b | b, c | c⟩
  · simp [rightSub, xv, Matrix.one_apply]
  · exact c.elim0
  · exact b.elim0
  · exact b.elim0
/- English proof (translation)
Use `LinearMap.ext fun f => ?_` and prove the remaining obligations. Simplify using `[act2, detPow, rightSub_one_pk]`.
-/
private theorem polyAction_one {n d : ℕ} (c : ℤ) : (act2 c (1 : GL (Fin d) ℂ) : Module.End ℂ (PP n d)) = 1 := by
  refine LinearMap.ext fun f => ?_
  simp [act2, detPow, rightSub_one_pk]
/- English proof (translation)
Introduce `T E _ _ _ B n d X W M χX χW om hP hn e e' he he' hnd δ mX mW hXJ hWJ eX eW U lam hU hwt hdom`. Take `⟨Φ, a, b, hinj, hran, ha, hb, h1, h2⟩` from `_root_.UpperTheory.TP.RP.fockOf_k T E B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW`. Establish `hμ : ∀ w, ∃ μ : Fin n → ℕ, ∀ k, (μ k : ℤ) + a w = (lam w).w k` using `fun w => ⟨fun k => ((lam w).w k - a w).toNat, fun k => by`. Establish `h3` using `hdom w k`. Establish `h4` using `ha w`.

Rewrite using `[Int.toNat_of_nonneg (by omega)]`. Use the proof step `omega⟩`. Use `choose μ hμ using hμ`. Establish `hanti : ∀ w, Antitone (μ w)` using `fun w i j hij => by`. Establish `h3` using `(lam w).anti hij`.

Establish `h4` using `hμ w i`. Establish `h5` using `hμ w j`. Use linear arithmetic over natural numbers and integers. Use `choose i₁ hi₁ x₁ hx₁ using fun w => exists_act1_equivariant_nablaSq_map_hitting_joint hnd (lam w) (a w) (μ w) (hμ w)`. Take `⟨ρ, j, hfd, hirr, hρ, hjinj, hjU, hj⟩` from `formEx E n hn _ (fun w => (B.emb w).1) (embBij E B) lam U hU hwt`.

Set `J : ∀ _ : InfinitePlace (maximalRealSubfield E), PP n d` to `fun w => joint hnd (μ w)`. Establish `hJ : ∀ w, J w ≠ 0` using `fun w => jointNe hnd (μ w) (hanti w)`. Establish `hx0 : ∀ w, x₁ w ≠ 0` using `fun w h => hJ w (by show joint hnd (μ w) = 0; rw [← hx₁ w, h, map_zero])`. Set `T₀ : Tens (maximalRealSubfield E) n 0 d 0` to `PiTensorProduct.tprod ℂ J`. Establish `hT₀ : T₀ ≠ 0` using `tprodNe J hJ`.

Set `iV : (⨂[ℂ] w, nablaSq ℂ n (lam w)) →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0` to `PiTensorProduct.map i₁`. Establish `hiV : iV (PiTensorProduct.tprod ℂ x₁) = T₀`. Simplify using `only [iV, T₀, PiTensorProduct.map_tprod, hx₁, J]`. Establish `hmem : ∀ T, Φ T ∈ M.Pol B.ψ B.emb` using `fun T => hran ▸ LinearMap.mem_range_self Φ T`. Establish `hS : UpperTheory.TP.SameType om e U (Φ T₀) (j (PiTensorProduct.tprod ℂ x₁))`.

Use `⟨_, _, _, hfd, ρ, Φ ∘ₗ iV, j, PiTensorProduct.tprod ℂ x₁, hirr, ?_, rfl, hjU, fun k x => ?_, hj⟩` and prove the remaining obligations. Simplify using `only [LinearMap.comp_apply, hiV]`. Establish `e1 : PiTensorProduct.map (fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) (iV x) = iV (ρ k x)`. Rewrite using `[hρ k]`. Establish `e2 : (PiTensorProduct.map fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) ∘ₗ iV = iV ∘ₗ PiTensorProduct.map fun w => GlobalTheory.Branching.sqRep ℂ n (lam w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1)`.

Simplify using `only [iV, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `w`. Conclude with `LinearMap.ext fun y => (hi₁ w _ y).symm`. Conclude with `LinearMap.congr_fun e2 x`.

Use `h1 k.1 k.2 (iV x)` as an intermediate fact. Rewrite `this` using `[e1]`. Conclude with `this`. Use `⟨Φ T₀, hmem _, fun h => hT₀ (hinj (h.trans (map_zero Φ).symm)), j (PiTensorProduct.tprod ℂ x₁), hjU _, fun h => tprodNe x₁ hx0 (hjinj (h.trans (map_zero j).symm)), hS, fun w => ?_⟩` and prove the remaining obligations. Set `lam' : DomWeight d` to `⟨fun k => (if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w, fun p q hpq => by`.

Establish `hle : (p : ℕ) ≤ q` using `hpq`. Simplify using `only`. Distinguish the cases in `h3 : (q : ℕ) < n`. Establish `h4 : (p : ℕ) < n` using `by omega`. Rewrite using `[dif_pos h3, dif_pos h4]`.

Use `hanti w (show (⟨p, h4⟩ : Fin n) ≤ ⟨q, h3⟩ from hle)` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Apply the tactic sequence `rw [dif_neg h3] split_ifs <;> omega⟩`. Use `⟨lam', fun k => ?_, GlobalTheory.DefU.isIrreducible_sqRep d lam', ?_⟩` and prove the remaining obligations. Establish `h3` using `ha w`.

Establish `h4` using `hb w`. Use `show 2 * ((if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w) = _`. Use `split_ifs with hk`. Establish `h5` using `hμ w ⟨k, hk⟩`. Use linear arithmetic over natural numbers and integers.

Use linear arithmetic over natural numbers and integers. Take `⟨i₂, hi₂, x₂, hx₂⟩` from `exists_act2_equivariant_nablaSq_map_hitting_joint hnd lam' (b w) (μ w) (fun k => rfl)`. Set `up : PP n d →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0` to `(PiTensorProduct.tprod ℂ).toLinearMap J w`. Establish `hup : ∀ y, up y = PiTensorProduct.tprod ℂ (Function.update J w y)` using `fun y => rfl`. Use `⟨Φ ∘ₗ up ∘ₗ i₂, fun x => hmem _, ⟨x₂, ?_⟩, fun k hk x => ?_⟩` and prove the remaining obligations.

Simplify using `only [LinearMap.comp_apply, hx₂, hup]`. Use `congr 2`. Conclude with `Function.update_eq_self_iff.2 rfl`. Establish `e1 : PiTensorProduct.map (fun w' => (act2 (b w') (GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k) : Module.End ℂ (PP n d))) (up (i₂ x)) = up (i₂ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x))`. Rewrite using `[hi₂, hup, hup, PiTensorProduct.map_tprod]`.

Use `congr 1`. Use function extensionality and compare the values at `w'`. Distinguish the cases in `hw' : w' = w`. Substitute `hw'` using the available equality. Simplify using the standard rewrite rules.

Rewrite using `[Function.update_of_ne hw', Function.update_of_ne hw']`. Establish `h3` using `(Subgroup.mem_inf.1 hk).2`. Rewrite `h3` using `[Subgroup.mem_iInf]`. Establish `h4` using `h3 (B.emb w').1`. Rewrite `h4` using `[Subgroup.mem_iInf]`.

Establish `h5 : GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k = 1` using `h4 fun h6 => hw' ((embBij E B).1 h6)`. Rewrite using `[h5, polyAction_one]`. Both sides reduce to the same expression. Use `h2 k (Subgroup.mem_inf.1 hk).1 (up (i₂ x))` as an intermediate fact. Rewrite `this` using `[e1]`.

Conclude with `this`.
-/
theorem UpperTheory.TP.realPair_k : _root_.UpperTheory.TP.Tools_k → _root_.UpperTheory.TP.RealPair_k := by
  intro T E _ _ _ B n d X W M χX χW om hP hn e e' he he' hnd δ mX mW hXJ hWJ eX eW U lam hU hwt hdom
  obtain ⟨Φ, a, b, hinj, hran, ha, hb, h1, h2⟩ :=
    _root_.UpperTheory.TP.RP.fockOf_k T E B n d X W M χX χW om hP hn hnd e e' he he' δ mX mW hXJ hWJ eX eW
  have hμ : ∀ w, ∃ μ : Fin n → ℕ, ∀ k, (μ k : ℤ) + a w = (lam w).w k := fun w =>
    ⟨fun k => ((lam w).w k - a w).toNat, fun k => by
      have h3 := hdom w k
      have h4 := ha w
      rw [Int.toNat_of_nonneg (by omega)]
      omega⟩
  choose μ hμ using hμ
  have hanti : ∀ w, Antitone (μ w) := fun w i j hij => by
    have h3 := (lam w).anti hij
    have h4 := hμ w i
    have h5 := hμ w j
    omega
  choose i₁ hi₁ x₁ hx₁ using fun w => exists_act1_equivariant_nablaSq_map_hitting_joint hnd (lam w) (a w) (μ w) (hμ w)
  obtain ⟨ρ, j, hfd, hirr, hρ, hjinj, hjU, hj⟩ :=
    formEx E n hn _ (fun w => (B.emb w).1) (embBij E B) lam U hU hwt
  let J : ∀ _ : InfinitePlace (maximalRealSubfield E), PP n d := fun w => joint hnd (μ w)
  have hJ : ∀ w, J w ≠ 0 := fun w => jointNe hnd (μ w) (hanti w)
  have hx0 : ∀ w, x₁ w ≠ 0 := fun w h => hJ w (by show joint hnd (μ w) = 0; rw [← hx₁ w, h, map_zero])
  let T₀ : Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.tprod ℂ J
  have hT₀ : T₀ ≠ 0 := tprodNe J hJ
  let iV : (⨂[ℂ] w, nablaSq ℂ n (lam w)) →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := PiTensorProduct.map i₁
  have hiV : iV (PiTensorProduct.tprod ℂ x₁) = T₀ := by
    simp only [iV, T₀, PiTensorProduct.map_tprod, hx₁, J]
  have hmem : ∀ T, Φ T ∈ M.Pol B.ψ B.emb := fun T => hran ▸ LinearMap.mem_range_self Φ T
  have hS : UpperTheory.TP.SameType om e U (Φ T₀) (j (PiTensorProduct.tprod ℂ x₁)) := by
    refine ⟨_, _, _, hfd, ρ, Φ ∘ₗ iV, j, PiTensorProduct.tprod ℂ x₁, hirr, ?_, rfl, hjU, fun k x => ?_, hj⟩
    · simp only [LinearMap.comp_apply, hiV]
    · have e1 : PiTensorProduct.map (fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) (iV x) =
          iV (ρ k x) := by
        rw [hρ k]
        have e2 : (PiTensorProduct.map fun w => (act1 (a w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) : Module.End ℂ (PP n d))) ∘ₗ iV =
            iV ∘ₗ PiTensorProduct.map fun w => GlobalTheory.Branching.sqRep ℂ n (lam w) (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k.1) := by
          simp only [iV, ← PiTensorProduct.map_comp]
          congr 1
          funext w
          exact LinearMap.ext fun y => (hi₁ w _ y).symm
        exact LinearMap.congr_fun e2 x
      have := h1 k.1 k.2 (iV x)
      rw [e1] at this
      exact this
  refine ⟨Φ T₀, hmem _, fun h => hT₀ (hinj (h.trans (map_zero Φ).symm)), j (PiTensorProduct.tprod ℂ x₁), hjU _,
    fun h => tprodNe x₁ hx0 (hjinj (h.trans (map_zero j).symm)), hS, fun w => ?_⟩
  let lam' : DomWeight d := ⟨fun k => (if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w, fun p q hpq => by
    have hle : (p : ℕ) ≤ q := hpq
    dsimp only
    by_cases h3 : (q : ℕ) < n
    · have h4 : (p : ℕ) < n := by omega
      rw [dif_pos h3, dif_pos h4]
      have := hanti w (show (⟨p, h4⟩ : Fin n) ≤ ⟨q, h3⟩ from hle)
      omega
    · rw [dif_neg h3]
      split_ifs <;> omega⟩
  refine ⟨lam', fun k => ?_, GlobalTheory.DefU.isIrreducible_sqRep d lam', ?_⟩
  · have h3 := ha w
    have h4 := hb w
    show 2 * ((if hk : (k : ℕ) < n then (μ w ⟨k, hk⟩ : ℤ) else 0) + b w) = _
    split_ifs with hk
    · have h5 := hμ w ⟨k, hk⟩
      omega
    · omega
  obtain ⟨i₂, hi₂, x₂, hx₂⟩ := exists_act2_equivariant_nablaSq_map_hitting_joint hnd lam' (b w) (μ w) (fun k => rfl)
  let up : PP n d →ₗ[ℂ] Tens (maximalRealSubfield E) n 0 d 0 := (PiTensorProduct.tprod ℂ).toLinearMap J w
  have hup : ∀ y, up y = PiTensorProduct.tprod ℂ (Function.update J w y) := fun y => rfl
  refine ⟨Φ ∘ₗ up ∘ₗ i₂, fun x => hmem _, ⟨x₂, ?_⟩, fun k hk x => ?_⟩
  · simp only [LinearMap.comp_apply, hx₂, hup]
    congr 2
    exact Function.update_eq_self_iff.2 rfl
  · have e1 : PiTensorProduct.map (fun w' => (act2 (b w') (GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k) : Module.End ℂ (PP n d))) (up (i₂ x)) =
        up (i₂ (GlobalTheory.Branching.sqRep ℂ d lam' (GlobalTheory.UnitaryBC.cEmb (B.emb w).1 k) x)) := by
      rw [hi₂, hup, hup, PiTensorProduct.map_tprod]
      congr 1
      funext w'
      by_cases hw' : w' = w
      · subst hw'
        simp
      · rw [Function.update_of_ne hw', Function.update_of_ne hw']
        have h3 := (Subgroup.mem_inf.1 hk).2
        rw [Subgroup.mem_iInf] at h3
        have h4 := h3 (B.emb w').1
        rw [Subgroup.mem_iInf] at h4
        have h5 : GlobalTheory.UnitaryBC.cEmb (B.emb w').1 k = 1 := h4 fun h6 => hw' ((embBij E B).1 h6)
        rw [h5, polyAction_one]
        rfl
    have := h2 k (Subgroup.mem_inf.1 hk).1 (up (i₂ x))
    rw [e1] at this
    exact this
end
end
