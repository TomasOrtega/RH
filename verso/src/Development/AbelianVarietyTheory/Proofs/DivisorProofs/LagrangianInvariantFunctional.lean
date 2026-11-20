import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SiegelWeilAnisotropicHermitian
import Development.AbelianVarietyTheory.Definitions.Divisors.CTSmallCone
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AvgFormApply
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmulIncMLagP
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AdelicStoneVonNeumannLagrangianUniqueness
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsSymplecticBlockGeneratorsLagrangianNormalFStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.CharacterInvariantAdelicFormEqMulEvalZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsStdCharNegOneOfStandardTraceAdelicAddChar
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SiegelThetaSliceIntegrableStatement

open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK

noncomputable section

namespace GlobalTheory.SiegelLagr

/- English proof (translation)
Proceed by induction on `hg using Submonoid.closure_induction with`. Consider the case `mem g hg`. Break down `hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl` into its components or cases. Use `Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks A⁻¹ 0 0 Aᵀ) ?_` and prove the remaining obligations. Rewrite using `[Matrix.fromBlocks_multiply]`.

Simplify using `[Matrix.mul_nonsing_inv _ hA, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA]`. Use `Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks 1 0 C 1) ?_` and prove the remaining obligations. Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Use `Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks 0 (-1) 1 0) ?_` and prove the remaining obligations.

Rewrite using `[Matrix.fromBlocks_multiply]`. Simplify using the standard rewrite rules. Consider the case `one => simp`. Consider the case `mul g h _ _ hg hh => rw [Matrix.det_mul]`. Conclude with `hg.mul hh`.
-/
theorem isUnit_det_of_mem_closure {F : Type} [Field F] {κ : Type} [Fintype κ] [DecidableEq κ]
    {g : Matrix (κ ⊕ κ) (κ ⊕ κ) F} (hg : g ∈ Submonoid.closure (GlobalTheory.AdelicSvN.gens F κ)) : IsUnit g.det := by
  induction hg using Submonoid.closure_induction with
  | mem g hg =>
    rcases hg with (⟨A, hA, rfl⟩ | ⟨C, hC, rfl⟩) | rfl
    · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks A⁻¹ 0 0 Aᵀ) ?_
      rw [Matrix.fromBlocks_multiply]
      simp [Matrix.mul_nonsing_inv _ hA, ← Matrix.transpose_mul, Matrix.nonsing_inv_mul _ hA]
    · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks 1 0 C 1) ?_
      rw [Matrix.fromBlocks_multiply]
      simp
    · refine Matrix.isUnit_det_of_right_inverse (B := Matrix.fromBlocks 0 (-1) 1 0) ?_
      rw [Matrix.fromBlocks_multiply]
      simp
  | one => simp
  | mul g h _ _ hg hh => rw [Matrix.det_mul]; exact hg.mul hh

def firstHalf {F : Type} [Field F] {κ : Type} [Fintype κ] (h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) :
    (κ → F) × (κ → F) →ₗ[F] (κ → F) where
  toFun w := (h *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl
  map_add' w w' := by
    funext i
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Prod.fst_add, Prod.snd_add, Pi.add_apply, mul_add, Finset.sum_add_distrib]
    ring
  map_smul' c w := by
    funext i
    simp only [Function.comp_apply, Matrix.mulVec, dotProduct, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr,
      Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, RingHom.id_apply, mul_add, Finset.mul_sum]
    congr 1 <;> refine Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem firstHalf_apply {F : Type} [Field F] {κ : Type} [Fintype κ] (h : Matrix (κ ⊕ κ) (κ ⊕ κ) F)
    (w : (κ → F) × (κ → F)) : firstHalf h w = (h *ᵥ Sum.elim w.1 w.2) ∘ Sum.inl := rfl

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [GlobalTheory.AdelicSvN.act, GlobalTheory.SiegelConv.extA, GlobalTheory.SiegelConv.ratP, firstHalf_apply, Function.comp_apply, Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Prod.fst_sum, Prod.snd_sum, Finset.sum_apply, Prod.sm …`. Rewrite using `[Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := m)), Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := m))]`. Apply the tactic sequence `congr 1 <;> refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring`.
-/
theorem act_extA_fst {F : Type} [Field F] [NumberField F] {m κ : Type} [Fintype m] [DecidableEq m] [Fintype κ]
    (h : Matrix (κ ⊕ κ) (κ ⊕ κ) F) (A : (m → F) →ₗ[F] (κ → F) × (κ → F)) (t : m → AF F) :
    (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).1 =
      fun i => ∑ j, t j * algebraMap F (AF F) (firstHalf h (A (Pi.single j 1)) i) := by
  funext i
  simp only [GlobalTheory.AdelicSvN.act, GlobalTheory.SiegelConv.extA, GlobalTheory.SiegelConv.ratP, firstHalf_apply, Function.comp_apply,
    Matrix.mulVec, dotProduct, Matrix.map_apply, Fintype.sum_sum_type, Sum.elim_inl, Sum.elim_inr, Prod.fst_sum,
    Prod.snd_sum, Finset.sum_apply, Prod.smul_fst, Prod.smul_snd, Pi.smul_apply, smul_eq_mul, map_sum, map_mul,
    map_add, Finset.mul_sum, mul_add, Finset.sum_add_distrib]
  rw [Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := m)),
    Finset.sum_comm (s := Finset.univ (α := κ)) (t := Finset.univ (α := m))]
  congr 1 <;> refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

/- English proof (translation)
Introduce `F _ _ ψ hψ κ _ _ L hL hdim l hl hi m _ _ A hA μ hμ φ hφ`. Use `letI : MeasurableSpace (m → AF F) := borel _`. Use `haveI : BorelSpace (m → AF F) := ⟨rfl⟩`. Take `⟨g, hg, hgL⟩` from `GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim`. Take `⟨S, hS, hSs, hSa, hSi⟩` from `GlobalTheory.AdelicSvN.realised_of_mem_closure ψ hψ hg`.

Choose the witnesses or unpack the hypotheses as in `⟨c, hc⟩ : ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by`. Take `⟨l', hl', e⟩` from `hSa l hl`. Take `⟨c, hc⟩` from `GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by`. Establish `hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ` using `by funext x; simp [schr]`. Rewrite using `[hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, GlobalTheory.AdelicSvN.act_zero_eq_sum]`.

Conclude with `GlobalTheory.AdelicSvN.inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))`. Conclude with `⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩`. Establish `hdet` using `isUnit_det_of_mem_closure hg`. Use `set h := g⁻¹ with hh`. Establish `hgh : g * h = 1` using `Matrix.mul_nonsing_inv g hdet`.

Take `⟨φ', hφ', rfl⟩` from `hSs φ hφ`. Use `set B : (m → F) →ₗ[F] (κ → F) := firstHalf h ∘ₗ A with hB`. Establish `hBinj : Function.Injective B`. Use `(injective_iff_map_eq_zero B).2 fun s hs => hA s ?_` and prove the remaining obligations. Use `set v : κ ⊕ κ → F := Sum.elim (A s).1 (A s).2`.

Use `set u : κ ⊕ κ → F := h *ᵥ v`. Establish `hu1 : u ∘ Sum.inl = 0` using `hs`. Establish `hu : u = Sum.elim (0 : κ → F) (u ∘ Sum.inr)`. Use function extensionality and compare the values at `k`. Consider the cases of `k with`.

Consider the case `inl i => exact congrFun hu1 i`. Consider the case `inr i => rfl`. Establish `hv : g *ᵥ u = v` using `by rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]`. Use `hgL (u ∘ Sum.inr)` as an intermediate fact. Rewrite `this` using `[← hu, hv]`.

Conclude with `this`. Establish `hint` using `GlobalTheory.T.siegel_theta_slice_integrable F κ m B hBinj μ hμ φ' hφ'`. Establish `e : ∀ t, l (schr ψ (GlobalTheory.SiegelConv.extA A t) (S φ')) = c * schr ψ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)) φ' 0`. Introduce `t`. Establish `ew : GlobalTheory.SiegelConv.extA A t = GlobalTheory.AdelicSvN.act g (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t))`.

Rewrite using `[← GlobalTheory.AdelicSvN.act_mul, hgh, GlobalTheory.AdelicSvN.act_one]`. Rewrite using `[ew, ← hSi _ _ hφ', hc _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'), ← ew]`. Simplify using `only [e]`. Use `Integrable.const_mul ?_ c` and prove the remaining obligations. Establish `hse : Continuous fun p : (κ → AF F) × (κ → AF F) => (Sum.elim p.1 p.2 : κ ⊕ κ → AF F)` using `continuous_pi fun k => by`.

Consider the cases of `k with`. Consider the case `inl i => exact (continuous_apply i).comp continuous_fst`. Consider the case `inr i => exact (continuous_apply i).comp continuous_snd`. Establish `hmv : Continuous fun p : (κ → AF F) × (κ → AF F) => h.map (algebraMap F (AF F)) *ᵥ (Sum.elim p.1 p.2 : κ ⊕ κ → AF F)` using `continuous_const.matrix_mulVec hse`. Establish `hact : Continuous fun p : (κ → AF F) × (κ → AF F) => GlobalTheory.AdelicSvN.act h p` using `(continuous_pi fun i => (continuous_apply (Sum.inl i)).comp hmv).prodMk (continuous_pi fun i => (continuous_apply (Sum.inr i)).comp hmv)`.

Establish `hext : Continuous fun t : m → AF F => GlobalTheory.SiegelConv.extA A t`. Unfold `GlobalTheory.SiegelConv.extA`. Use `fun_prop`. Establish `hcont : Continuous fun t : m → AF F => GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)` using `hact.comp hext`. Establish `e2 : ∀ t, schr ψ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)) φ' 0 = ψ ((0 : κ → AF F) ⬝ᵥ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).2 + ⅟(2 : AF F) * ((GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).1 ⬝ᵥ (GlobalTheory …`.

Introduce `t`. Simplify using `only [schr, zero_add]`. Rewrite using `[act_extA_fst]`. Both sides reduce to the same expression. Simplify using `only [e2]`.

Use `hint.bdd_mul (c := 1) ?_ (ae_of_all _ fun t => (GlobalTheory.StdCharFromIsStd.norm_psi hψ _).le)` and prove the remaining obligations. Use `Continuous.aestronglyMeasurable ?_` and prove the remaining obligations. Use `hψ.1.comp ?_` and prove the remaining obligations. Establish `h1 : Continuous fun t : m → AF F => (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).1` using `continuous_fst.comp hcont`. Establish `h2 : Continuous fun t : m → AF F => (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).2` using `continuous_snd.comp hcont`.

Simplify using `only [dotProduct]`. Use `fun_prop`.
-/
theorem main : ∀ (F : Type) [Field F] [NumberField F] (ψ : AddChar (AF F) ℂ), IsStd ψ →
    ∀ (κ : Type) [Fintype κ] [DecidableEq κ] (L : Submodule F ((κ → F) × (κ → F))),
    (∀ a ∈ L, ∀ b ∈ L, a.1 ⬝ᵥ b.2 = b.1 ⬝ᵥ a.2) → Module.finrank F L = Fintype.card κ →
    ∀ l ∈ (adeleClass F).adm κ,
    (∀ (t : AF F), ∀ w ∈ L, ∀ φ ∈ schA F κ, l (schr ψ (t • GlobalTheory.SiegelConv.ratP w) φ) = l φ) →
    ∀ (m : Type) [Fintype m] [DecidableEq m] (A : (m → F) →ₗ[F] (κ → F) × (κ → F)), (∀ s, A s ∈ L → s = 0) →
    ∀ μ : @Measure (m → AF F) (borel _), GlobalTheory.SiegelAvg.IsHaarB μ →
    ∀ φ ∈ schA F κ, (letI : MeasurableSpace (m → AF F) := borel _;
      Integrable (fun t => l (schr ψ (GlobalTheory.SiegelConv.extA A t) φ)) μ) := by
  intro F _ _ ψ hψ κ _ _ L hL hdim l hl hi m _ _ A hA μ hμ φ hφ
  letI : MeasurableSpace (m → AF F) := borel _
  haveI : BorelSpace (m → AF F) := ⟨rfl⟩
  obtain ⟨g, hg, hgL⟩ := GlobalTheory.T.exists_symplecticBlockGenerators_lagrangian_normal_form F κ L hL hdim
  obtain ⟨S, hS, hSs, hSa, hSi⟩ := GlobalTheory.AdelicSvN.realised_of_mem_closure ψ hψ hg
  obtain ⟨c, hc⟩ : ∃ c : ℂ, ∀ φ ∈ schA F κ, l (S φ) = c * φ 0 := by
    obtain ⟨l', hl', e⟩ := hSa l hl
    obtain ⟨c, hc⟩ := GlobalTheory.T.character_invariant_adelic_form_eq_mul_eval_zero F ψ hψ κ l' hl' (fun y φ hφ => by
      have hm : (fun x => ψ (x ⬝ᵥ y) * φ x) = schr ψ (0, y) φ := by funext x; simp [schr]
      rw [hm, e _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ hφ), e φ hφ, hSi _ φ hφ, GlobalTheory.AdelicSvN.act_zero_eq_sum]
      exact GlobalTheory.AdelicSvN.inv_sum ψ hψ L hL l hi Finset.univ y _ (fun j => hgL _) _ (hS φ hφ))
    exact ⟨c, fun φ hφ => (e φ hφ).symm.trans (hc φ hφ)⟩
  have hdet := isUnit_det_of_mem_closure hg
  set h := g⁻¹ with hh
  have hgh : g * h = 1 := Matrix.mul_nonsing_inv g hdet
  obtain ⟨φ', hφ', rfl⟩ := hSs φ hφ
  set B : (m → F) →ₗ[F] (κ → F) := firstHalf h ∘ₗ A with hB
  have hBinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun s hs => hA s ?_
    set v : κ ⊕ κ → F := Sum.elim (A s).1 (A s).2
    set u : κ ⊕ κ → F := h *ᵥ v
    have hu1 : u ∘ Sum.inl = 0 := hs
    have hu : u = Sum.elim (0 : κ → F) (u ∘ Sum.inr) := by
      funext k; cases k with
      | inl i => exact congrFun hu1 i
      | inr i => rfl
    have hv : g *ᵥ u = v := by rw [Matrix.mulVec_mulVec, hgh, Matrix.one_mulVec]
    have := hgL (u ∘ Sum.inr)
    rw [← hu, hv] at this
    exact this
  have hint := GlobalTheory.T.siegel_theta_slice_integrable F κ m B hBinj μ hμ φ' hφ'
  have e : ∀ t, l (schr ψ (GlobalTheory.SiegelConv.extA A t) (S φ')) =
      c * schr ψ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)) φ' 0 := by
    intro t
    have ew : GlobalTheory.SiegelConv.extA A t = GlobalTheory.AdelicSvN.act g (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)) := by
      rw [← GlobalTheory.AdelicSvN.act_mul, hgh, GlobalTheory.AdelicSvN.act_one]
    rw [ew, ← hSi _ _ hφ', hc _ (GlobalTheory.HeisSchA.schr_mem_schA ψ hψ _ φ' hφ'), ← ew]
  simp only [e]
  refine Integrable.const_mul ?_ c
  have hse : Continuous fun p : (κ → AF F) × (κ → AF F) => (Sum.elim p.1 p.2 : κ ⊕ κ → AF F) :=
    continuous_pi fun k => by
      cases k with
      | inl i => exact (continuous_apply i).comp continuous_fst
      | inr i => exact (continuous_apply i).comp continuous_snd
  have hmv : Continuous fun p : (κ → AF F) × (κ → AF F) =>
      h.map (algebraMap F (AF F)) *ᵥ (Sum.elim p.1 p.2 : κ ⊕ κ → AF F) := continuous_const.matrix_mulVec hse
  have hact : Continuous fun p : (κ → AF F) × (κ → AF F) => GlobalTheory.AdelicSvN.act h p :=
    (continuous_pi fun i => (continuous_apply (Sum.inl i)).comp hmv).prodMk
      (continuous_pi fun i => (continuous_apply (Sum.inr i)).comp hmv)
  have hext : Continuous fun t : m → AF F => GlobalTheory.SiegelConv.extA A t := by
    unfold GlobalTheory.SiegelConv.extA
    fun_prop
  have hcont : Continuous fun t : m → AF F => GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t) := hact.comp hext
  have e2 : ∀ t, schr ψ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)) φ' 0 =
      ψ ((0 : κ → AF F) ⬝ᵥ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).2 + ⅟(2 : AF F) *
        ((GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).1 ⬝ᵥ (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).2)) *
        φ' (fun i => ∑ j, t j * algebraMap F (AF F) (B (Pi.single j 1) i)) := by
    intro t
    simp only [schr, zero_add]
    rw [act_extA_fst]
    rfl
  simp only [e2]
  refine hint.bdd_mul (c := 1) ?_ (ae_of_all _ fun t => (GlobalTheory.StdCharFromIsStd.norm_psi hψ _).le)
  refine Continuous.aestronglyMeasurable ?_
  refine hψ.1.comp ?_
  have h1 : Continuous fun t : m → AF F => (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).1 :=
    continuous_fst.comp hcont
  have h2 : Continuous fun t : m → AF F => (GlobalTheory.AdelicSvN.act h (GlobalTheory.SiegelConv.extA A t)).2 :=
    continuous_snd.comp hcont
  simp only [dotProduct]
  fun_prop

end GlobalTheory.SiegelLagr
