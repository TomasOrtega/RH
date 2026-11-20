import Mathlib
import Development.AbelianVarietyTheory.Definitions.NonGaloisDescent.IsPotential
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.OneSubPhiOntoOfFilZero
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.BhattScholzeCrystallineLattices
import Development.AbelianVarietyTheory.BlockTheory.NonGaloisCusps.ConductorExponents
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.TeichmullerSubOneAinfPropertiesCompatibleRootsStatement
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.FrobeniusIntegralityCoeffTensorAinfVectorStatement
open Formalism Formalism.BasicNotions Formalism.BasicNotions.Loc Formalism.WeaklyAdmissibleFiltrations TensorProduct PowerSeries GlobalTheory.Prism GlobalTheory.BK GlobalTheory.BKReal GlobalTheory.BKGal GlobalTheory.Per Matrix
open scoped Formalism.Per

namespace GlobalTheory.BKGal.LiftStep

/- English proof (translation)
Take `⟨⟨ξ, hξ, hμ⟩, -⟩` from `(GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ`. Establish `h : Associated (ϖ.ev a (eis l a e)) ξ`. Rewrite using `[← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]`. Take `⟨v, hv⟩` from `h`. Use `⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩` and prove the remaining obligations.

Rewrite using `[hμ, ← hv]`. Take the linear combination `(-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul`.
-/
theorem ev_eis_mul_mu {l : ℕ} [Fact l.Prime] (a : ℕ) [NeZero a] {e : ℕ} [NeZero e] (ϖ : PiSys l e)
    {ε δ : OCb l} (hε : IsEps ε) (hδ : δ ^ l = ε) :
    ∃ u : Ainf l, IsUnit u ∧ ϖ.ev a (eis l a e) * muOf δ = u * muOf ε := by
  obtain ⟨⟨ξ, hξ, hμ⟩, -⟩ := (GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ
  have h : Associated (ϖ.ev a (eis l a e)) ξ := by
    rw [← Ideal.span_singleton_eq_span_singleton, hξ, PiSys.span_ev_eis]
  obtain ⟨v, hv⟩ := h
  refine ⟨((v⁻¹ : (Ainf l)ˣ) : Ainf l), Units.isUnit _, ?_⟩
  rw [hμ, ← hv]
  linear_combination (-(ϖ.ev a (eis l a e) * muOf δ)) * v.inv_mul

section Integral

variable {l : ℕ} [hl : Fact l.Prime] {a : ℕ} [NeZero a] {e : ℕ} [NeZero e]
  {O K : Type} [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O]
  [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K]
  (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) {ι : Type} [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι)

/- English proof (translation)
Establish `h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K)))`. Rewrite using `[← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]`. Both sides reduce to the same expression. Rewrite using `[h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]`. Use `congr 1`.
-/
theorem E_pow_mul_iW (n : ℕ) (f : ZMod a → invE l e (A O K)) (hf : ∀ τ, E K l e ^ n * (f τ : K⟦X⟧) ∈ A O K) :
    inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ n * ϖ.iW t K f = inclO l O (ϖ.iTot t K fun τ => ⟨_, hf τ⟩) := by
  have h1 : inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) = ϖ.iW t K (fun _ => EIn l e (invE l e (A O K))) := by
    rw [← ϖ.iTot_E t K, ← ϖ.iW_of_mem t K]
    rfl
  rw [h1, ← map_pow, ← map_mul, ← ϖ.iW_of_mem t K]
  congr 1

/- English proof (translation)
Use `⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩` and prove the remaining obligations. Establish `hm : (fun τ k => P.mx τ k j) ∈ P.L` using `mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩`. Establish `h` using `mem_tot.1 (hL _ hm)`. Conclude with `⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩`. Apply the tactic sequence `have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M := mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]`.

Establish `h` using `fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i`. Use `⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩` and prove the remaining obligations. Simplify `h τ` using `[Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm]`. Establish `h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K` using `fun τ => by simpa using mem_tot.1 hy τ i`. Use `⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩` and prove the remaining obligations.

Rewrite using `[toW_apply]`. Conclude with `(E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm`.
-/
theorem integral (α β : ℕ) (hL : ∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) (hM : ∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) :
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * frobMat t ϖ P i j) ∧
    (∀ i j, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ β * frobMatInv t ϖ P i j) ∧
    ∀ y : ME P, y.1 ∈ P.EM α → ∀ i, ∃ c : OA l O, inclO l O c = inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * toW t ϖ P y i := by
  refine ⟨fun i j => ?_, fun i j => ?_, fun y hy i => ?_⟩
  · have hm : (fun τ k => P.mx τ k j) ∈ P.L := mem_tot.2 fun τ => Submodule.subset_span ⟨j, rfl⟩
    have h := mem_tot.1 (hL _ hm)
    exact ⟨_, (E_pow_mul_iW t ϖ α _ fun τ => h τ i).symm⟩
  · have hm : (fun (_ : ZMod a) (k : ι) => if k = j then (1 : K⟦X⟧) else 0) ∈ P.M :=
      mem_tot.2 fun τ k => by split_ifs <;> simp [Mc, mem_vecs]
    have h := fun τ => P.mem_extc_iff.1 (mem_tot.1 (hM _ hm) τ) i
    refine ⟨_, (E_pow_mul_iW t ϖ β (fun τ => ((P.mat τ)⁻¹ : GL ι (invE l e (A O K))) i j) fun τ => ?_).symm⟩
    simpa [Matrix.mulVec, dotProduct, PhiMod.mxInv, mul_comm] using h τ
  · have h : ∀ τ, E K l e ^ α * (y.1 τ i) ∈ A O K := fun τ => by simpa using mem_tot.1 hy τ i
    refine ⟨ϖ.iTot t K fun τ => ⟨_, h τ⟩, ?_⟩
    rw [toW_apply]
    exact (E_pow_mul_iW t ϖ α (fun τ => ⟨y.1 τ i, mem_tot.1 y.2 τ i⟩) h).symm

end Integral

end GlobalTheory.BKGal.LiftStep

/- English proof (translation)
Use function extensionality and compare the values at `i`. Simplify using `only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN, Finset.mul_sum, ← Finset.sum_add_distrib]`. Use `Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Expand and normalize the polynomial expressions, which then agree.
-/
theorem GlobalTheory.BKGal.LiftStep.alg_step {S ι : Type} [CommRing S] [Fintype ι] (Ui Ew N Mh : S) (α β : ℕ)
    (hMN : Mh = Ui * Ew ^ (β + α) * N) (Xi : Matrix ι ι S) (m y : ι → S) (Yc : ι → ι → S) (yc : ι → S)
    (hY : ∀ i j, Yc i j = Ew ^ β * Xi i j) (hy : ∀ j, yc j = Ew ^ α * y j) :
    Mh • (Xi *ᵥ (m + y)) = (Matrix.of fun i j => Ui * Ew ^ α * Yc i j) *ᵥ (N • m) +
      fun i => Ui * ∑ j, Yc i j * (N * yc j) := by
  funext i
  simp only [Pi.smul_apply, smul_eq_mul, Pi.add_apply, Matrix.mulVec, dotProduct, Matrix.of_apply, hY, hy, hMN,
    Finset.mul_sum, ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

open GlobalTheory.BKGal.LiftStep in

/- English proof (translation)
Introduce `l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀`. Take `⟨u, hu, hEu⟩` from `ev_eis_mul_mu a ϖ hε hδ`. Establish `hfr : WittVector.frobenius (muOf δ) = muOf ε` using `((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.1`. Take `⟨-, hXi, hyI⟩` from `integral t ϖ P α β hL hM`. Use `choose cXi hcXi using hXi`.

Use `choose cy hcy using hyI y hy`. Use `set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui`. Establish `hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ`. Rewrite using `[mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]`. Use `set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw`.

Use `set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN`. Use `set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh`. Use `set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi`. Establish `hMN : Mh = Ui * Ew ^ (β + α) * N`. Rewrite using `[hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow, Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]`.

Establish `hFN : frobOW l O N = Mh`. Rewrite using `[hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]`. Use `set y' := toW t ϖ P y with hy'`. Establish `hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y')`. Establish `h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y'`.

Rewrite using `[← phiW_apply]`. Conclude with `sub_eq_iff_eq_add'.1 hm₀`. Rewrite using `[← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]`. Use `set z : ι → OW l O := N • m₀ with hz`. Establish `hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i))`.

Use function extensionality and compare the values at `i`. Simplify using `only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]`. Use `set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j`. Use `set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)`. Establish `heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i))`.

Rewrite using `[hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j)) (fun j => inclO l O (cy j)) hcXi hcy]`. Use `congr 2`. Use extensionality with `i j`. Express the relevant statement in the definitionally equal form `_ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)`. Rewrite using `[map_mul, map_mul, map_pow]`.

Both sides reduce to the same expression. Use function extensionality and compare the values at `i`. Simplify using `only [w, map_mul, map_sum]`. Both sides reduce to the same expression. Establish `hint` using `GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector l O ι Y w z heq`.

Use `choose c hc using hint`. Use `⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩` and prove the remaining obligations. Rewrite using `[inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]`. Use `congr 1`. Use function extensionality and compare the values at `i`.

Rewrite using `[← frobOW_inclO]`. Conclude with `congrArg _ (hc i)`.
-/
theorem GlobalTheory.BKGal.LiftStep.mu_pow_smul_mem : ∀ (l : ℕ) [Fact l.Prime] (a e : ℕ) [NeZero a] [NeZero e] (O K : Type) [CommRing O] [Algebra ℤ_[l] O] [Module.Free ℤ_[l] O] [Module.Finite ℤ_[l] O] [NormedField K] [IsUltrametricDist K] [Algebra O K] [IsUnitBall O K] [NormedAlgebra ℚ_[l] K] [TameDescentExponentData K l e a] (t : Wq l a →ₐ[ℤ_[l]] O) (ϖ : PiSys l e) (ι : Type) [Fintype ι] [DecidableEq ι] (P : PhiMod O K l e a ι) (T : LocLat (Gl l) ℚ_[l] K O) (I : Ident t ϖ P T) (α β : ℕ), (∀ m ∈ P.L, E K l e ^ α • m ∈ P.M) → (∀ m ∈ P.M, E K l e ^ β • m ∈ P.L) → ∀ ε δ : OCb l, IsEps ε → δ ^ l = ε → ∀ (y : ME P), y.1 ∈ P.EM α → ∀ m₀, phiW t ϖ P m₀ - m₀ = toW t ϖ P y → inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) • m₀ ∈ MA P ∧ inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) • phiW t ϖ P m₀ ∈ LA t ϖ P := by
  intro l _ a e _ _ O K _ _ _ _ _ _ _ _ _ _ t ϖ ι _ _ P T I α β hL hM ε δ hε hδ y hy m₀ hm₀
  classical
  obtain ⟨u, hu, hEu⟩ := ev_eis_mul_mu a ϖ hε hδ
  have hfr : WittVector.frobenius (muOf δ) = muOf ε := ((GlobalTheory.T.teichmullerSubOneAinf_properties_compatibleRoots l).2 ε δ hε hδ).2.1
  obtain ⟨-, hXi, hyI⟩ := integral t ϖ P α β hL hM
  choose cXi hcXi using hXi
  choose cy hcy using hyI y hy
  set ui : Ainf l := ((hu.unit⁻¹ : (Ainf l)ˣ) : Ainf l) with hui
  have hμ : muOf ε = ui * ϖ.ev a (eis l a e) * muOf δ := by
    rw [mul_assoc, hEu, ← mul_assoc, hui, IsUnit.val_inv_mul, one_mul]
  set Ew := inclO l O (1 ⊗ₜ ϖ.ev a (eis l a e)) with hEw
  set N := inclO l O (1 ⊗ₜ (muOf δ ^ (β + α))) with hN
  set Mh := inclO l O (1 ⊗ₜ (muOf ε ^ (β + α))) with hMh
  set Ui := inclO l O (1 ⊗ₜ (ui ^ (β + α))) with hUi
  have hMN : Mh = Ui * Ew ^ (β + α) * N := by
    rw [hMh, hUi, hEw, hN, ← map_pow, ← map_mul, ← map_mul, Algebra.TensorProduct.tmul_pow, one_pow,
      Algebra.TensorProduct.tmul_mul_tmul, Algebra.TensorProduct.tmul_mul_tmul, one_mul, one_mul, hμ, mul_pow, mul_pow]
  have hFN : frobOW l O N = Mh := by
    rw [hN, frobOW_inclO, frobOA_tmul, map_pow, hfr]
  set y' := toW t ϖ P y with hy'
  have hF : (fun i => frobOW l O (m₀ i)) = frobMatInv t ϖ P *ᵥ (m₀ + y') := by
    have h1 : frobMat t ϖ P *ᵥ (fun i => frobOW l O (m₀ i)) = m₀ + y' := by
      rw [← phiW_apply]; exact sub_eq_iff_eq_add'.1 hm₀
    rw [← h1, Matrix.mulVec_mulVec, frobMatInv_mul, Matrix.one_mulVec]
  set z : ι → OW l O := N • m₀ with hz
  have hFz : (fun i => frobOW l O (z i)) = Mh • (fun i => frobOW l O (m₀ i)) := by
    funext i
    simp only [hz, Pi.smul_apply, smul_eq_mul, map_mul, hFN]
  set Y : Matrix ι ι (OA l O) := fun i j => (1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j
  set w : ι → OA l O := fun i => (1 ⊗ₜ (ui ^ (β + α))) * ∑ j, cXi i j * ((1 ⊗ₜ (muOf δ ^ (β + α))) * cy j)
  have heq : (fun i => frobOW l O (z i)) = (Y.map (inclO l O)) *ᵥ z + (fun i => inclO l O (w i)) := by
    rw [hFz, hF, alg_step Ui Ew N Mh α β hMN (frobMatInv t ϖ P) m₀ y' (fun i j => inclO l O (cXi i j))
      (fun j => inclO l O (cy j)) hcXi hcy]
    congr 2
    · ext i j
      change _ = inclO l O ((1 ⊗ₜ (ui ^ (β + α))) * (1 ⊗ₜ ϖ.ev a (eis l a e)) ^ α * cXi i j)
      rw [map_mul, map_mul, map_pow]
      rfl
    · funext i
      simp only [w, map_mul, map_sum]
      rfl
  have hint := GlobalTheory.T.frobenius_integrality_coeffTensorAinf_vector l O ι Y w z heq
  choose c hc using hint
  refine ⟨⟨c, funext fun i => hc i⟩, ⟨fun i => frobOA l O (c i), ?_⟩⟩
  rw [inclL_apply, phiW_apply, ← Matrix.mulVec_smul, ← hFz]
  congr 1
  funext i
  rw [← frobOW_inclO]
  exact congrArg _ (hc i)
