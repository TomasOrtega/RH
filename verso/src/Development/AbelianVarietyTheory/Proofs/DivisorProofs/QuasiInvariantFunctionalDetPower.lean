import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DiffsZeroOfLev
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FullRk
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsEqMulMatIntOrbO
open scoped TensorProduct NNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Filter Topology Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes
open GlobalTheory.WeilM GlobalTheory.AdelicU GlobalTheory.LFun GlobalTheory.IndefiniteRowSideFullHecke.WeilTensorModels GlobalTheory.ThK GlobalTheory.ThK.DescB
attribute [local instance] GlobalTheory.LocalData.complRel GlobalTheory.LocalData.isLocalField
attribute [-instance] Formalism.DoubleCosetMeasures.instMeasGL

namespace GlobalTheory.FullRankCoinv.LeftScale

open GlobalTheory.SplitFlip GlobalTheory.SplitWeil

variable {k : Type} [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k]

/- English proof (translation)
Simplify using `using comp_mem_fullRk (1 : GL (Fin n) k) h hφ`.
-/
theorem comp_right_mem_fullRk {n d : ℕ} (h : GL (Fin d) k) {φ : Matrix (Fin n) (Fin d) k → ℂ}
    (hφ : φ ∈ fullRk k n d) : (fun Y : Matrix (Fin n) (Fin d) k => φ (Y * h.val)) ∈ fullRk k n d := by
  simpa using comp_mem_fullRk (1 : GL (Fin n) k) h hφ

/- English proof (translation)
Use `matInt_comp ν (1 : GL (Fin n) k) h φ` as an intermediate fact. Simplify `this` using `[nabs]`.
-/
theorem matInt_comp_right [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    (h : GL (Fin d) k) (φ : Matrix (Fin n) (Fin d) k → ℂ) :
    ((nabs k (gdet h) ^ n : ℝ) : ℂ) * matInt ν (fun Y : Matrix (Fin n) (Fin d) k => φ (Y * h.val)) = matInt ν φ := by
  have := matInt_comp ν (1 : GL (Fin n) k) h φ
  simpa [nabs] using this

/- English proof (translation)
Take `⟨Y, hY, hYh⟩` from `hY`. Establish `hcan : ∀ Z : Matrix (Fin n) (Fin d) k, Z * h.val * (h⁻¹).val = Z` using `fun Z => by`. Rewrite using `[Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]`. Use `set U : Set (Matrix (Fin n) (Fin d) k) := orbO k n d ∩ (fun Z => Z * (h⁻¹).val) ⁻¹' orbO k n d with hU`. Establish `hUo : IsClopen U` using `hO.inter (hO.preimage (by fun_prop))`.

Establish `hUc : IsCompact U` using `hc.of_isClosed_subset hUo.isClosed Set.inter_subset_left`. Establish `hφ` using `indicator_one_mem_fullRk hUo hUc fun Z hZ => hr Z hZ.1`. Establish `hne` using `matInt_indicator_ne_zero ν hUo.isOpen hUc ⟨Y * h.val, hYh, by simpa [hcan] using hY⟩`. Establish `h1` using `hC _ hφ fun Z hZ => (Set.mem_of_indicator_ne_zero hZ).1`. Establish `h2` using `hC _ (comp_right_mem_fullRk h hφ) fun Z hZ => by`.

Use `(Set.mem_of_indicator_ne_zero hZ).2` as an intermediate fact. Rewrite `this` using `[Set.mem_preimage, hcan]`. Then use the resulting hypothesis. Establish `h3` using `hm _ hφ`. Establish `h4` using `matInt_comp_right ν h (U.indicator fun _ => (1 : ℂ))`. Rewrite `h3` using `[h1, h2, ← h4]`.

Establish `h5 : matInt ν (fun Z : Matrix (Fin n) (Fin d) k => U.indicator (fun _ => (1 : ℂ)) (Z * h.val)) ≠ 0`. Introduce `h0`. Rewrite `h4` using `[h0, mul_zero]`. Conclude with `hne h4.symm`. Establish `h6 : C * matInt ν (fun Z : Matrix (Fin n) (Fin d) k => U.indicator (fun _ => (1 : ℂ)) (Z * h.val)) ≠ 0` using `mul_ne_zero hC0 h5`.

Apply `mul_right_cancel₀ h6` to reduce the goal to its premises. Rewrite using `[h3]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem factor_eq [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    (hO : IsClopen (orbO k n d)) (hc : IsCompact (orbO k n d)) (hr : ∀ Y ∈ orbO k n d, Y.rank = n)
    (Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ) {C : ℂ} (hC0 : C ≠ 0)
    (hC : ∀ φ ∈ fullRk k n d, (∀ Y, φ Y ≠ 0 → Y ∈ orbO k n d) → Λ φ = C * matInt ν φ)
    (h : GL (Fin d) k) (hY : ∃ Y ∈ orbO k n d, Y * h.val ∈ orbO k n d) {m : ℂ}
    (hm : ∀ φ ∈ fullRk k n d, m * Λ (fun Y => φ (Y * h.val)) = Λ φ) :
    m = ((nabs k (gdet h) ^ n : ℝ) : ℂ) := by
  obtain ⟨Y, hY, hYh⟩ := hY
  have hcan : ∀ Z : Matrix (Fin n) (Fin d) k, Z * h.val * (h⁻¹).val = Z := fun Z => by
    rw [Matrix.mul_assoc, ← Units.val_mul, mul_inv_cancel, Units.val_one, Matrix.mul_one]
  set U : Set (Matrix (Fin n) (Fin d) k) := orbO k n d ∩ (fun Z => Z * (h⁻¹).val) ⁻¹' orbO k n d with hU
  have hUo : IsClopen U := hO.inter (hO.preimage (by fun_prop))
  have hUc : IsCompact U := hc.of_isClosed_subset hUo.isClosed Set.inter_subset_left
  have hφ := indicator_one_mem_fullRk hUo hUc fun Z hZ => hr Z hZ.1
  have hne := matInt_indicator_ne_zero ν hUo.isOpen hUc ⟨Y * h.val, hYh, by simpa [hcan] using hY⟩
  have h1 := hC _ hφ fun Z hZ => (Set.mem_of_indicator_ne_zero hZ).1
  have h2 := hC _ (comp_right_mem_fullRk h hφ) fun Z hZ => by
    have := (Set.mem_of_indicator_ne_zero hZ).2
    rwa [Set.mem_preimage, hcan] at this
  have h3 := hm _ hφ
  have h4 := matInt_comp_right ν h (U.indicator fun _ => (1 : ℂ))
  rw [h1, h2, ← h4] at h3
  have h5 : matInt ν (fun Z : Matrix (Fin n) (Fin d) k => U.indicator (fun _ => (1 : ℂ)) (Z * h.val)) ≠ 0 := by
    intro h0; rw [h0, mul_zero] at h4; exact hne h4.symm
  have h6 : C * matInt ν (fun Z : Matrix (Fin n) (Fin d) k => U.indicator (fun _ => (1 : ℂ)) (Z * h.val)) ≠ 0 :=
    mul_ne_zero hC0 h5
  apply mul_right_cancel₀ h6
  rw [h3]; ring

/- English proof (translation)
Take `⟨hO, hc, hr⟩` from `orbO_clopen_compact k n d hnd`. Take `⟨C, hC⟩` from `exists_eq_mul_matInt_orbO k ν n d hO hc hr Λ (invariant_KO k n d Λ hΛ)`. Establish `piece : ∀ h : GL (Fin d) k, ∀ ψ ∈ fullRk k n d, (∀ Y, ψ (Y * h.val) ≠ 0 → Y ∈ orbO k n d) → Λ ψ = C * matInt ν ψ`. Distinguish the cases in `hC0 : C = 0`. Introduce `h ψ hψ hs`.

Take `⟨m, -, hm⟩` from `hΛ h`. Rewrite using `[← hm ψ hψ, hC _ (comp_right_mem_fullRk h hψ) hs, hC0]`. Simplify using the standard rewrite rules. Establish `all : ∀ h : GL (Fin d) k, ∀ φ ∈ fullRk k n d, ((nabs k (gdet h) ^ n : ℝ) : ℂ) * Λ (fun Y => φ (Y * h.val)) = Λ φ`. Use `induction_orbO k n d hnd _ (fun a b ha hb φ hφ => ?_) fun h hY => ?_` and prove the remaining obligations.

Establish `e : ((nabs k (gdet (a * b)) ^ n : ℝ) : ℂ) = ((nabs k (gdet b) ^ n : ℝ) : ℂ) * ((nabs k (gdet a) ^ n : ℝ) : ℂ)`. Simplify using `[nabs, mul_pow, mul_comm]`. Rewrite using `[← hb φ hφ, ← ha _ (comp_right_mem_fullRk b hφ), e, mul_assoc]`. Simplify using `only [Units.val_mul, Matrix.mul_assoc]`. Take `⟨m, -, hm⟩` from `hΛ h`.

Rewrite using `[← factor_eq ν hO hc hr Λ hC0 hC h hY hm]`. Conclude with `hm`. Introduce `h ψ hψ hs`. Rewrite using `[← all h ψ hψ, hC _ (comp_right_mem_fullRk h hψ) hs, ← matInt_comp_right ν h ψ]`. Expand and normalize the polynomial expressions, which then agree.

Use `⟨C, fun φ hφ => ?_⟩` and prove the remaining obligations. Take `⟨s, ψ, rfl, hψ⟩` from `exists_sum_pieces k n d hnd hO φ hφ`. Rewrite using `[map_sum, matInt_sum ν s ψ fun h hh => (hψ h hh).1.1, Finset.mul_sum]`. Conclude with `Finset.sum_congr rfl fun h hh => piece h _ (hψ h hh).1 (hψ h hh).2`.
-/
theorem exists_eq_mul_matInt [MeasurableSpace k] [BorelSpace k] (ν : Measure k) [ν.IsAddHaarMeasure] {n d : ℕ}
    (hnd : n < d) (Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ)
    (hΛ : ∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ φ ∈ fullRk k n d, (m : ℂ) * Λ (fun Y => φ (Y * h.val)) = Λ φ) :
    ∃ C : ℂ, ∀ φ ∈ fullRk k n d, Λ φ = C * matInt ν φ := by
  obtain ⟨hO, hc, hr⟩ := orbO_clopen_compact k n d hnd
  obtain ⟨C, hC⟩ := exists_eq_mul_matInt_orbO k ν n d hO hc hr Λ (invariant_KO k n d Λ hΛ)
  have piece : ∀ h : GL (Fin d) k, ∀ ψ ∈ fullRk k n d, (∀ Y, ψ (Y * h.val) ≠ 0 → Y ∈ orbO k n d) →
      Λ ψ = C * matInt ν ψ := by
    by_cases hC0 : C = 0
    · intro h ψ hψ hs
      obtain ⟨m, -, hm⟩ := hΛ h
      rw [← hm ψ hψ, hC _ (comp_right_mem_fullRk h hψ) hs, hC0]; simp
    have all : ∀ h : GL (Fin d) k, ∀ φ ∈ fullRk k n d,
        ((nabs k (gdet h) ^ n : ℝ) : ℂ) * Λ (fun Y => φ (Y * h.val)) = Λ φ := by
      refine induction_orbO k n d hnd _ (fun a b ha hb φ hφ => ?_) fun h hY => ?_
      · have e : ((nabs k (gdet (a * b)) ^ n : ℝ) : ℂ) =
            ((nabs k (gdet b) ^ n : ℝ) : ℂ) * ((nabs k (gdet a) ^ n : ℝ) : ℂ) := by
          simp [nabs, mul_pow, mul_comm]
        rw [← hb φ hφ, ← ha _ (comp_right_mem_fullRk b hφ), e, mul_assoc]
        simp only [Units.val_mul, Matrix.mul_assoc]
      · obtain ⟨m, -, hm⟩ := hΛ h
        rw [← factor_eq ν hO hc hr Λ hC0 hC h hY hm]
        exact hm
    intro h ψ hψ hs
    rw [← all h ψ hψ, hC _ (comp_right_mem_fullRk h hψ) hs, ← matInt_comp_right ν h ψ]; ring
  refine ⟨C, fun φ hφ => ?_⟩
  obtain ⟨s, ψ, rfl, hψ⟩ := exists_sum_pieces k n d hnd hO φ hφ
  rw [map_sum, matInt_sum ν s ψ fun h hh => (hψ h hh).1.1, Finset.mul_sum]
  exact Finset.sum_congr rfl fun h hh => piece h _ (hψ h hh).1 (hψ h hh).2

/- English proof (translation)
Introduce `k _ _ _ _ n d hnd Λ hΛ g φ hφ`. Use `borelize k`. Use `haveI := SplitWeil.secondCountable k`. Use `haveI := SplitWeil.t2Space k`. Take `⟨C, hC⟩` from `exists_eq_mul_matInt (Measure.addHaar : Measure k) hnd Λ hΛ`.

Establish `hm` using `comp_mem_fullRk (invT g)⁻¹ (1 : GL (Fin d) k) hφ`. Establish `hi` using `matInt_comp (Measure.addHaar : Measure k) (invT g)⁻¹ (1 : GL (Fin d) k) φ`. Establish `hd : gdet (invT g)⁻¹ = gdet g` using `Units.ext (by`. Rewrite using `[Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, invT_inv_val, Matrix.det_transpose])`. Rewrite `hi` using `[hd]`.

Simplify using `only [invT_inv_val, Units.val_one, Matrix.mul_one] at hm hi`. Rewrite using `[hC _ hm, hC _ hφ, ← hi, apow, Complex.cpow_natCast]`. Simplify using `[nabs]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem left_scale : ∀ (k : Type) [Field k] [ValuativeRel k] [TopologicalSpace k] [IsNonarchimedeanLocalField k] (n d : ℕ), n < d →
    ∀ Λ : (Matrix (Fin n) (Fin d) k → ℂ) →ₗ[ℂ] ℂ,
      (∀ h : GL (Fin d) k, ∃ m : ℝ, 0 < m ∧ ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        (m : ℂ) * Λ (fun Y => φ (Y * h.1)) = Λ φ) →
      ∀ (g : GL (Fin n) k), ∀ φ ∈ GlobalTheory.FullRankCoinv.fullRk k n d,
        GlobalTheory.SplitFlip.apow (GlobalTheory.SplitFlip.gdet g) (d : ℂ) * Λ (fun Y => φ ((g.1)ᵀ * Y)) = Λ φ := by
  intro k _ _ _ _ n d hnd Λ hΛ g φ hφ
  borelize k
  haveI := SplitWeil.secondCountable k
  haveI := SplitWeil.t2Space k
  obtain ⟨C, hC⟩ := exists_eq_mul_matInt (Measure.addHaar : Measure k) hnd Λ hΛ
  have hm := comp_mem_fullRk (invT g)⁻¹ (1 : GL (Fin d) k) hφ
  have hi := matInt_comp (Measure.addHaar : Measure k) (invT g)⁻¹ (1 : GL (Fin d) k) φ
  have hd : gdet (invT g)⁻¹ = gdet g := Units.ext (by
    rw [Matrix.GeneralLinearGroup.val_det_apply, Matrix.GeneralLinearGroup.val_det_apply, invT_inv_val,
      Matrix.det_transpose])
  rw [hd] at hi
  simp only [invT_inv_val, Units.val_one, Matrix.mul_one] at hm hi
  rw [hC _ hm, hC _ hφ, ← hi, apow, Complex.cpow_natCast]
  simp [nabs]; ring

end GlobalTheory.FullRankCoinv.LeftScale
