import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsFockMap
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsUSplittingInl
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockOperatorsLieRepresentationCommute
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchActionReadingsCompatible
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.UnitaryLieElementsGenerateOneParamLines
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CartanEigenOrthonormalFrameExists
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ArchHeisenbergDerivativesExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockToSchrodingerMapExistsOfArchHeisenbergDerivaStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SchwartzFockVacuumLineUniqueOfHeisenbergDerivatiStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FockPolynomialSpaceEqFockImageOfArchLawsStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.OneParamSubgroupGeneratorsExistStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LieScalarStatement

noncomputable section

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.RealLift

namespace GlobalTheory.LineBracket

section Tensor

variable {ι : Type} [Fintype ι] [DecidableEq ι] {V : ι → Type} [∀ i, AddCommGroup (V i)] [∀ i, Module ℂ (V i)]

omit [Fintype ι] in
/- English proof (translation)
Unfold `atPl`. Rewrite using `[Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = w`.

Substitute `hi` using the available equality. Simplify using `[Module.End.mul_eq_comp]`. Simplify using `[Function.update_of_ne hi]`.
-/
theorem atPl_mul_same (w : ι) (L L' : Module.End ℂ (V w)) : atPl w L * atPl w L' = atPl w (L * L') := by
  unfold atPl
  rw [Module.End.mul_eq_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [Module.End.mul_eq_comp]
  · simp [Function.update_of_ne hi]

omit [Fintype ι] in
/- English proof (translation)
Unfold `atPl`. Rewrite using `[Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]`. Use `congr 1`. Use function extensionality and compare the values at `i`. Distinguish the cases in `hi : i = w`.

Substitute `hi` using the available equality. Simplify using `[Function.update_of_ne h]`. Distinguish the cases in `hi' : i = w'`. Substitute `hi'` using the available equality. Simplify using `[Function.update_of_ne hi]`.

Simplify using `[Function.update_of_ne hi, Function.update_of_ne hi']`.
-/
theorem atPl_comm_of_ne {w w' : ι} (h : w ≠ w') (L : Module.End ℂ (V w)) (L' : Module.End ℂ (V w')) :
    atPl w L * atPl w' L' = atPl w' L' * atPl w L := by
  unfold atPl
  rw [Module.End.mul_eq_comp, Module.End.mul_eq_comp, ← PiTensorProduct.map_comp, ← PiTensorProduct.map_comp]
  congr 1
  funext i
  by_cases hi : i = w
  · subst hi; simp [Function.update_of_ne h]
  · by_cases hi' : i = w'
    · subst hi'; simp [Function.update_of_ne hi]
    · simp [Function.update_of_ne hi, Function.update_of_ne hi']

omit [Fintype ι] in
/- English proof (translation)
The claim follows from `(PiTensorProduct.mapMultilinear ℂ V V).map_update_sub (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L L'`.
-/
theorem atPl_sub (w : ι) (L L' : Module.End ℂ (V w)) : atPl w (L - L') = atPl w L - atPl w L' :=
  (PiTensorProduct.mapMultilinear ℂ V V).map_update_sub (fun i => (LinearMap.id : V i →ₗ[ℂ] V i)) w L L'

/- English proof (translation)
Unfold `sumPl`. Rewrite using `[Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun i j => atPl i (L' i) * atPl j (L j)), ← Finset.sum_sub_distrib]`. Use `Finset.sum_congr rfl fun w _ => ?_` and prove the remaining obligations. Rewrite using `[← Finset.sum_sub_distrib, Finset.sum_eq_single w]`. Rewrite using `[atPl_mul_same, atPl_mul_same, atPl_sub]`.

Introduce `w' _ h`. Rewrite using `[atPl_comm_of_ne h.symm, sub_self]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ w) h`.
-/
theorem sumPl_comm (L L' : ∀ w, Module.End ℂ (V w)) :
    sumPl L * sumPl L' - sumPl L' * sumPl L = sumPl fun w => L w * L' w - L' w * L w := by
  unfold sumPl
  rw [Finset.sum_mul_sum, Finset.sum_mul_sum, Finset.sum_comm (f := fun i j => atPl i (L' i) * atPl j (L j)),
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun w _ => ?_
  rw [← Finset.sum_sub_distrib, Finset.sum_eq_single w]
  · rw [atPl_mul_same, atPl_mul_same, atPl_sub]
  · intro w' _ h
    rw [atPl_comm_of_ne h.symm, sub_self]
  · intro h
    exact absurd (Finset.mem_univ w) h

end Tensor

open Formalism.BasicNotions.TH in

/- English proof (translation)
Establish `h1 : Yᴴ * Jm p q = -(Jm p q * Y)` using `eq_neg_of_add_eq_zero_left hY`. Establish `h2 : Zᴴ * Jm p q = -(Jm p q * Z)` using `eq_neg_of_add_eq_zero_left hZ`. Use `show (Y * Z - Z * Y)ᴴ * Jm p q + Jm p q * (Y * Z - Z * Y) = 0`. Rewrite using `[Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2, mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]`. Use `noncomm_ring`.
-/
theorem bracket_mem_upq {p q : ℕ} {Y Z : Mat p q} (hY : Y ∈ upq p q) (hZ : Z ∈ upq p q) : Y * Z - Z * Y ∈ upq p q := by
  have h1 : Yᴴ * Jm p q = -(Jm p q * Y) := eq_neg_of_add_eq_zero_left hY
  have h2 : Zᴴ * Jm p q = -(Jm p q * Z) := eq_neg_of_add_eq_zero_left hZ
  show (Y * Z - Z * Y)ᴴ * Jm p q + Jm p q * (Y * Z - Z * Y) = 0
  rw [Matrix.conjTranspose_sub, Matrix.conjTranspose_mul, Matrix.conjTranspose_mul, sub_mul, mul_assoc, mul_assoc, h1, h2,
    mul_neg, mul_neg, ← mul_assoc, ← mul_assoc, h1, h2]
  noncomm_ring

open Formalism.BasicNotions.TH in

/- English proof (translation)
Rewrite using `[(GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 Y Z, Matrix.trace_sub, Matrix.trace_mul_comm Y Z, sub_self]`. Simplify using `only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]`. Use `module`.
-/
theorem fock_trace_comm (P Q R S : ℕ) (c : ℂ) (Y Z : Mat R S) :
    (fockAct2 P Q R S Y + (c * Y.trace) • 1) * (fockAct2 P Q R S Z + (c * Z.trace) • 1) -
      (fockAct2 P Q R S Z + (c * Z.trace) • 1) * (fockAct2 P Q R S Y + (c * Y.trace) • 1) =
      fockAct2 P Q R S (Y * Z - Z * Y) + (c * (Y * Z - Z * Y).trace) • (1 : Module.End ℂ (Formalism.BasicNotions.TH.Pol P Q R S)) := by
  rw [(GlobalTheory.FockAlg.fock_lie_and_commute P Q R S).2.2.1 Y Z, Matrix.trace_sub, Matrix.trace_mul_comm Y Z, sub_self]
  simp only [mul_add, add_mul, mul_smul_comm, smul_mul_assoc, mul_one, one_mul]
  module

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[incM, piInf, compInf, inclR, infEmb_tmul]`.
-/
theorem incM_map_piInf {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n m : Type}
    (J : Matrix n m E) {w : InfinitePlace F} (τ : EmbOver E w) : (incM F J).map (piInf τ) = J.map τ.1 := by
  ext i j
  simp [incM, piInf, compInf, inclR, infEmb_tmul]

/- English proof (translation)
Introduce `hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair κ hκ δ hδ`. Establish `hb` using `hpair.base`. Establish `hX` using `hpair.herm`. Establish `hW` using `hpair.skew`. Establish `hder : DerEx` using `GlobalTheory.T.archHeisenbergDerivatives_exist`.

Establish `hvl : VacLine` using `GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder`. Establish `hfe : FockEx` using `GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder`. Establish `hpr : PolRange` using `GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl`. Establish `hls : LieScalar` using `GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl`. Establish `hge : GenEx` using `GlobalTheory.T.oneParamSubgroup_generators_exist`.

Establish `hle : LineEx` using `GlobalTheory.RealLift.exists_line_of_upq`. Establish `hfr : FrameEx` using `GlobalTheory.RealLift.frameEx_holds`. Use `choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)`. Use `choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)`. Establish `hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w)` using `fun w => by`.

Rewrite using `[incM_map_piInf, one_smul]`. Conclude with `hA w`. Establish `hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w)` using `fun w => by`. Rewrite using `[incM_map_piInf]`. Conclude with `hC w`.

Establish `fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C` using `⟨one_mul _, hA1, hC1⟩`. Take `⟨Φ, hΦ⟩` from `hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr`. Establish `hr` using `hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ`. Establish `hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om` using `IsUWeilPair.isUSplitting hpair.weil`. Establish `hsp2` using `GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp`.

Take `⟨c, hc⟩` from `hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hsp2`. Take `⟨Y, hY, hYg⟩` from `hge F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 κ hκ`. Take `⟨Z, hZ, hZg⟩` from `hge F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 δ hδ`. Take `⟨ε, hε, hεg⟩` from `hle F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 (fun w => Y w * Z w - Z w * Y w) fun w => bracket_mem_upq (hY w) (hZ w)`. Establish `key : ∀ γ ∈ Lines σ W, ∀ U, IsGen B.emb C γ U → ∀ (T : Tens F r s r' s') (f' : SInf F (Fin n × Fin d)), ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) f' → f' = Φ (sumPl (fun w => Formalism.BasicNotions.TH.fockAct2 r s r' s' (U w) + (c w * (U w).trace) • 1) T)`.

Introduce `γ hγ U hU T f' hf'`. Establish `hSD : SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) _` using `hc γ hγ U hU T`. Conclude with `(GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T) f' _).2.2.1 _ hf' ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T) _ f').1 _ (fun t => map_zero _) hSD)`. Use `⟨ε, hε, fun f hf f₁ f₂ f₁₂ f₂₁ g h₁ h₂ h₁₂ h₂₁ hg => ?_⟩` and prove the remaining obligations. Rewrite `hf` using `[← hr]`.

Take `⟨T, rfl⟩` from `hf`. Take `rfl` from `key κ hκ Y hYg T f₁ h₁`. Take `rfl` from `key δ hδ Z hZg T f₂ h₂`. Take `rfl` from `key δ hδ Z hZg _ f₁₂ h₁₂`. Take `rfl` from `key κ hκ Y hYg _ f₂₁ h₂₁`.

Take `rfl` from `key ε hε _ hεg T g hg`. Rewrite using `[← map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply (sumPl _) (sumPl _) T, ← LinearMap.sub_apply, sumPl_comm]`. Simplify using `only [fock_trace_comm]`.
-/
theorem exists_line_bracket : GlobalTheory.FunPr.Hypotheses₂ → ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (σ : E →ₐ[F] E) (B : Base F E)
    (n d : ℕ) (X : Spc F E n) (W : Spc F E d) (M : Model σ X W) (χX χW : Chr F E) (om : Rep σ X W) (r s r' s' : ℕ),
    IsPair B M χX χW om r s r' s' → ∀ κ ∈ Lines σ W, ∀ δ ∈ Lines σ W, ∃ ε ∈ Lines σ W, ∀ f ∈ M.Pol B.ψ B.emb,
      ∀ f₁ f₂ f₁₂ f₂₁ g : SInf F (Fin n × Fin d),
        ActsD (evI F) (fun t => om (1, κ (Multiplicative.ofAdd t))) f f₁ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f f₂ →
        ActsD (evI F) (fun t => om (1, δ (Multiplicative.ofAdd t))) f₁ f₁₂ →
        ActsD (evI F) (fun t => om (1, κ (Multiplicative.ofAdd t))) f₂ f₂₁ →
        ActsD (evI F) (fun t => om (1, ε (Multiplicative.ofAdd t))) f g → f₂₁ - f₁₂ = g := by
  classical
  intro hP F E _ _ _ _ _ σ B n d X W M χX χW om r s r' s' hpair κ hκ δ hδ
  have hb := hpair.base
  have hX := hpair.herm
  have hW := hpair.skew
  have hder : DerEx := GlobalTheory.T.archHeisenbergDerivatives_exist
  have hvl : VacLine := GlobalTheory.T.schwartzFockVacuumLineUnique_of_heisenberg_derivatives hder
  have hfe : FockEx := GlobalTheory.T.fockToSchrodingerMapExists_of_archHeisenbergDerivatives hder
  have hpr : PolRange := GlobalTheory.T.fockPolynomialSpace_eq_fockImage_of_arch_laws GlobalTheory.RealLift.actsLaws hder hvl
  have hls : LieScalar := GlobalTheory.T.lieScalar_of_prints_derEx_vacLine hP hder hvl
  have hge : GenEx := GlobalTheory.T.oneParamSubgroup_generators_exist
  have hle : LineEx := GlobalTheory.RealLift.exists_line_of_upq
  have hfr : FrameEx := GlobalTheory.RealLift.frameEx_holds
  choose A hA hAθ using fun w => hfr _ _ _ _ _ (hX.sig w) (hX.cartan w)
  choose C hC hCθ using fun w => hfr _ _ _ _ _ (hW.sig w) (hW.cartan w)
  have hA1 : ∀ w, IsFrame ((1 : ℂ) • (incM F X.J).map (piInf (B.emb w))) (A w) := fun w => by
    rw [incM_map_piInf, one_smul]; exact hA w
  have hC1 : ∀ w, IsFrame (Complex.I • (incM F W.J).map (piInf (B.emb w))) (C w) := fun w => by
    rw [incM_map_piInf]; exact hC w
  have fr : Framed B.emb (incM F X.J) (incM F W.J) 1 Complex.I A C := ⟨one_mul _, hA1, hC1⟩
  obtain ⟨Φ, hΦ⟩ := hfe F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C hb.cm hb.std fr
  have hr := hpr F E σ _ _ _ _ _ _ X W M B.ψ B.emb A C Φ hb.cm hb.std fr hAθ hCθ hΦ
  have hsp : IsUSplitting (adeleClass F) B.ψ M.co (actAB (cA σ)) om := IsUWeilPair.isUSplitting hpair.weil
  have hsp2 := GlobalTheory.WeilSchrodinger.isUSplitting_inr hsp
  obtain ⟨c, hc⟩ := hls F E σ _ _ _ _ _ _ _ B.ψ B.emb _ _ M.co 1 Complex.I A C Φ _ hb.cm hb.std fr hΦ hsp2
  obtain ⟨Y, hY, hYg⟩ := hge F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 κ hκ
  obtain ⟨Z, hZ, hZg⟩ := hge F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 δ hδ
  obtain ⟨ε, hε, hεg⟩ := hle F E σ (Fin d) _ _ B.emb (incM F W.J) Complex.I C hb.cm hC1 (fun w => Y w * Z w - Z w * Y w)
    fun w => bracket_mem_upq (hY w) (hZ w)
  have key : ∀ γ ∈ Lines σ W, ∀ U, IsGen B.emb C γ U → ∀ (T : Tens F r s r' s') (f' : SInf F (Fin n × Fin d)),
      ActsD (evI F) (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) f' →
      f' = Φ (sumPl (fun w => Formalism.BasicNotions.TH.fockAct2 r s r' s' (U w) + (c w * (U w).trace) • 1) T) := by
    intro γ hγ U hU T f' hf'
    have hSD : SD (fun t => om (1, γ (Multiplicative.ofAdd t))) (Φ T) _ := hc γ hγ U hU T
    exact (GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T) f' _).2.2.1 _ hf'
      ((GlobalTheory.RealLift.actsLaws F (Fin n × Fin d) (Φ T) _ f').1 _ (fun t => map_zero _) hSD)
  refine ⟨ε, hε, fun f hf f₁ f₂ f₁₂ f₂₁ g h₁ h₂ h₁₂ h₂₁ hg => ?_⟩
  rw [← hr] at hf
  obtain ⟨T, rfl⟩ := hf
  obtain rfl := key κ hκ Y hYg T f₁ h₁
  obtain rfl := key δ hδ Z hZg T f₂ h₂
  obtain rfl := key δ hδ Z hZg _ f₁₂ h₁₂
  obtain rfl := key κ hκ Y hYg _ f₂₁ h₂₁
  obtain rfl := key ε hε _ hεg T g hg
  rw [← map_sub, ← Module.End.mul_apply, ← Module.End.mul_apply (sumPl _) (sumPl _) T, ← LinearMap.sub_apply, sumPl_comm]
  simp only [fock_trace_comm]

end GlobalTheory.LineBracket

end
