import Mathlib
import GroundTheory.HeightsAndTheta.Heights.HilbertSamuel.StatementsComponentResFibreFinite
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterBridgeB
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.InterFib
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights.HilbertSamuel

open MvPolynomial ReciprocityTheory.ChartRestriction.G.Geo

noncomputable section

namespace ComponentResFibreFinite

variable {K : Type} [Fintype K] [DecidableEq K] {ι : K → Type} [∀ k, Fintype (ι k)]
  {W : Ideal (MvPolynomial (Σ k, ι k) ℂ)} {e : ℕ}

def resW (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) (x : R.R.M) : ((k : K) → ι k) → ℂ :=
  (Ψ (segre (R.pt x)) 0)⁻¹ • segre (R.pt x)

/- English proof (translation)
The claim follows from `R.R.lift_mem (R.idx x) x (R.mem_src_idx x)`.
-/
theorem pt_mem_conePts (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e) (x : R.R.M) :
    R.pt x ∈ ReciprocityTheory.AnForm.R.conePts W :=
  R.R.lift_mem (R.idx x) x (R.mem_src_idx x)

omit [Fintype K] [DecidableEq K] [∀ k, Fintype (ι k)] in

/- English proof (translation)
Assemble the required witnesses or components as `⟨hz.1, fun _ hf => hz.2 _ (hW (Ideal.mem_map_of_mem _ hf))⟩`.
-/
theorem mem_mcPts_of_conePts {P : Ideal (MRing ι)}
    (hW : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W) {z : (Σ k, ι k) → ℂ}
    (hz : z ∈ ReciprocityTheory.AnForm.R.conePts W) : z ∈ mcPts P :=
  ⟨hz.1, fun _ hf => hz.2 _ (hW (Ideal.mem_map_of_mem _ hf))⟩

/- English proof (translation)
Take `⟨k0⟩` from `hK`. Set `c : K → ℂ` to `Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z) 0)⁻¹`. Establish `hc : ∀ k, c k ≠ 0`. Introduce `k`. Distinguish the cases in `hk : k = k0`.

Substitute `hk` using the available equality. Simplify using `[c, h0]`. Simplify using `[c, Function.update_of_ne hk]`. Establish `hpc : ∏ k, c k = (Ψ (segre z) 0)⁻¹`. Simplify using `[c, Finset.prod_update_of_mem (Finset.mem_univ k0)]`.

Use `⟨fun p => c p.1 * z p, mcPts_smul hPh c hc hz, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[segre_smul, hpc]`. Use function extensionality and compare the values at `i`. Use `Fin.cases ?_ (fun i => ?_) i` and prove the remaining obligations. Simplify using `[h0]`.

Simplify using `only [map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]`. Rewrite using `[div_eq_inv_mul]`.
-/
theorem smul_segre_mem_fibre {P : Ideal (MRing ι)} (hK : Nonempty K) (hPh : IsMultiHomogIdeal P)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) {z : (Σ k, ι k) → ℂ} (hz : z ∈ mcPts P)
    (h0 : Ψ (segre z) 0 ≠ 0) :
    (Ψ (segre z) 0)⁻¹ • segre z ∈
      fibre P Ψ (fun i : Fin e => Ψ (segre z) i.succ / Ψ (segre z) 0) := by
  obtain ⟨k0⟩ := hK
  let c : K → ℂ := Function.update (fun _ => (1 : ℂ)) k0 (Ψ (segre z) 0)⁻¹
  have hc : ∀ k, c k ≠ 0 := by
    intro k
    by_cases hk : k = k0
    · subst hk; simp [c, h0]
    · simp [c, Function.update_of_ne hk]
  have hpc : ∏ k, c k = (Ψ (segre z) 0)⁻¹ := by
    simp [c, Finset.prod_update_of_mem (Finset.mem_univ k0)]
  refine ⟨fun p => c p.1 * z p, mcPts_smul hPh c hc hz, ?_, ?_⟩
  · rw [segre_smul, hpc]
  · funext i
    refine Fin.cases ?_ (fun i => ?_) i
    · simp [h0]
    · simp only [map_smul, Pi.smul_apply, smul_eq_mul, Fin.cons_succ]
      rw [div_eq_inv_mul]

/- English proof (translation)
Introduce `x hx x' hx' hw`. Establish `hseg : segre (R.pt x) = (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x')`. Use `congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw` as an intermediate fact. Simplify using `only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this`. Conclude with `this`.

Take `⟨c, hc, hcz⟩` from `sameOrbit_of_segre (pt_mem_conePts R x').1 _ (by simp [hx.2, hx'.2]) hseg`. Conclude with `R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ⟨c, hc, hcz⟩`.
-/
theorem resW_injOn (R : GroundTheory.Heights₂.Heights.IndefiniteRowSideFullHecke.Inter.Res ι W e)
    (Ψ : (((k : K) → ι k) → ℂ) →ₗ[ℂ] (Fin (e + 1) → ℂ)) :
    Set.InjOn (resW R Ψ)
      {x | R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0} := by
  intro x hx x' hx' hw
  have hseg : segre (R.pt x) =
      (Ψ (segre (R.pt x)) 0 * (Ψ (segre (R.pt x')) 0)⁻¹) • segre (R.pt x') := by
    have := congrArg (fun v => Ψ (segre (R.pt x)) 0 • v) hw
    simp only [resW, smul_smul, mul_inv_cancel₀ hx.2, one_smul] at this
    exact this
  obtain ⟨c, hc, hcz⟩ := sameOrbit_of_segre (pt_mem_conePts R x').1 _ (by simp [hx.2, hx'.2]) hseg
  exact R.R.inj (R.idx x) (R.idx x') x (R.mem_src_idx x) x' (R.mem_src_idx x') hx.1 ⟨c, hc, hcz⟩

/- English proof (translation)
Introduce `K _ _ ι _ P e W R Ψ hP hW hΨ y`. Establish `hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W` using `hW.1.2`. Establish `hbad : ∀ x ∉ resBad R Ψ, R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0` using `fun x hx => ⟨fun h => hx (Or.inl (Or.inl h)), fun h => hx (Or.inl (Or.inr h))⟩`. Use `Set.Finite.of_finite_image (f := resW R Ψ) ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((resW_injOn R Ψ).mono fun x hx => hbad x hx.2)` and prove the remaining obligations. Introduce and unpack `_ ⟨x, hx, rfl⟩`.

Use `smul_segre_mem_fibre hP.1 hP.2.1.2.1 Ψ (mem_mcPts_of_conePts hle (pt_mem_conePts R x)) (hbad x hx.2).2` as an intermediate fact. Establish `hy : resProj R Ψ x = y` using `hx.1`. Rewrite using `[← hy]`. Conclude with `this`.
-/
theorem proof : ComponentResFibreFinite.Statement := by
  intro K _ _ ι _ P e W R Ψ hP hW hΨ y
  have hle : P.map (MvPolynomial.map (Int.castRingHom ℂ)) ≤ W := hW.1.2
  have hbad : ∀ x ∉ resBad R Ψ,
      R.pt x ∉ ReciprocityTheory.AnForm.R.conePts R.D ∧ Ψ (segre (R.pt x)) 0 ≠ 0 :=
    fun x hx => ⟨fun h => hx (Or.inl (Or.inl h)), fun h => hx (Or.inl (Or.inr h))⟩
  refine Set.Finite.of_finite_image (f := resW R Ψ)
    ((fibreFinite K ι P e Ψ hP hΨ y).subset ?_) ((resW_injOn R Ψ).mono fun x hx => hbad x hx.2)
  rintro _ ⟨x, hx, rfl⟩
  have := smul_segre_mem_fibre hP.1 hP.2.1.2.1 Ψ
    (mem_mcPts_of_conePts hle (pt_mem_conePts R x)) (hbad x hx.2).2
  have hy : resProj R Ψ x = y := hx.1
  rw [← hy]
  exact this

end ComponentResFibreFinite

end

end GroundTheory.Heights₂.Heights.HilbertSamuel
