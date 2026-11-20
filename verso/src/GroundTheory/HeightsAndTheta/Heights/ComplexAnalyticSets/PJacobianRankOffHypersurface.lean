import Mathlib
import GroundTheory.HeightsAndTheta.Heights.ComplexAnalyticSets.StJacobianRankOffHypersurface
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PFrameJacobianGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PJacobianRankGeneric
import GroundTheory.HeightsAndTheta.Heights.ElementarySymmetric.PConormalGenerationGeneric
set_option maxSynthPendingDepth 1

namespace GroundTheory.Heights₂.Heights

open MvPolynomial

noncomputable section

/- English proof (translation)
Simplify using `[map_sum, Derivation.leibniz, smul_eq_mul, hg]`.
-/
theorem JacobianRankOffHypersurface.eval_pderiv_sum_mul {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (c g : ι → MvPolynomial σ ℂ) (hg : ∀ k, eval w (g k) = 0) (x : σ) :
    eval w (pderiv x (∑ k, c k * g k)) = ∑ k, eval w (c k) * eval w (pderiv x (g k)) := by
  simp [map_sum, Derivation.leibniz, smul_eq_mul, hg]

/- English proof (translation)
Establish `key : (fun x ↦ eval w (pderiv x p)) = (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k)))`. Use function extensionality and compare the values at `x`. Establish `h1` using `congrArg (fun f ↦ eval w (pderiv x f)) hsum`. Simplify using `only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul, map_add, map_mul, hp, zero_mul, add_zero] at h1`. Simplify using `only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]`.

Rewrite using `[inv_mul_cancel_left₀ ha]`. Rewrite using `[key]`. Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))`.
-/
theorem JacobianRankOffHypersurface.grad_mem_span {σ ι : Type*} [Fintype ι] (w : σ → ℂ)
    (a p : MvPolynomial σ ℂ) (c g : ι → MvPolynomial σ ℂ) (hsum : ∑ k, c k * g k = a * p)
    (hg : ∀ k, eval w (g k) = 0) (hp : eval w p = 0) (ha : eval w a ≠ 0) :
    (fun x ↦ eval w (pderiv x p)) ∈
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (g k))) := by
  have key : (fun x ↦ eval w (pderiv x p)) =
      (eval w a)⁻¹ • ∑ k, eval w (c k) • (fun x ↦ eval w (pderiv x (g k))) := by
    funext x
    have h1 := congrArg (fun f ↦ eval w (pderiv x f)) hsum
    simp only [JacobianRankOffHypersurface.eval_pderiv_sum_mul w c g hg x, Derivation.leibniz, smul_eq_mul,
      map_add, map_mul, hp, zero_mul, add_zero] at h1
    simp only [Pi.smul_apply, Finset.sum_apply, smul_eq_mul, h1]
    rw [inv_mul_cancel_left₀ ha]
  rw [key]
  exact Submodule.smul_mem _ _
    (Submodule.sum_mem _ fun k _ ↦ Submodule.smul_mem _ _ (Submodule.subset_span ⟨k, rfl⟩))

/- English proof (translation)
Establish `hw' : ∀ p ∈ Q, eval w p = 0` using `hw`. Simplify using `only [map_mul, mul_ne_zero_iff] at hμ`. Take `⟨⟨hs0, ht0⟩, hδ0⟩` from `hμ`. Establish `heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) = Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k)))`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Submodule.span_le, Set.range_subset_iff]`. Introduce `j`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))`. Conclude with `JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k)) (hw' _ (hqQ j)) hs0`. Rewrite using `[Submodule.span_le, Set.range_subset_iff]`.

Introduce `k`. Take `⟨i, hi⟩` from `hgen (f k) (hfQ k)`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp hi`. Use `JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j)) (hw' _ (hfQ k)) ?_` and prove the remaining obligations. Rewrite using `[map_pow]`.

Conclude with `pow_ne_zero _ ht0`. Rewrite using `[heq, finrank_span_eq_card (hδ w hδ0)]`. Conclude with `hcard`.
-/
theorem JacobianRankOffHypersurface.finrank_of_generators {σ ι : Type*} [Fintype σ] [Fintype ι]
    (Q : Ideal (MvPolynomial σ ℂ)) (d r : ℕ) (q : Fin r → MvPolynomial σ ℂ) (t : MvPolynomial σ ℂ)
    (hqQ : ∀ j, q j ∈ Q) (hgen : ∀ p ∈ Q, ∃ i : ℕ, t ^ i * p ∈ Ideal.span (Set.range q))
    (f : ι → MvPolynomial σ ℂ) (s δ : MvPolynomial σ ℂ) (hfQ : ∀ k, f k ∈ Q)
    (hs : ∀ p ∈ Q, s * p ∈ Ideal.span (Set.range f))
    (hδ : ∀ w : σ → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (f k)))
    (hcard : Fintype.card ι + d = Fintype.card σ) (w : σ → ℂ) (hw : w ∈ IndefiniteRowSideFullHecke.ComplexSets.zeroSetIn Q)
    (hμ : eval w (s * t * δ) ≠ 0) :
    Module.finrank ℂ (Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j)))) + d =
      Fintype.card σ := by
  have hw' : ∀ p ∈ Q, eval w p = 0 := hw
  simp only [map_mul, mul_ne_zero_iff] at hμ
  obtain ⟨⟨hs0, ht0⟩, hδ0⟩ := hμ
  have heq : Submodule.span ℂ (Set.range fun j x ↦ eval w (pderiv x (q j))) =
      Submodule.span ℂ (Set.range fun k x ↦ eval w (pderiv x (f k))) := by
    apply le_antisymm
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro j
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hs (q j) (hqQ j))
      exact JacobianRankOffHypersurface.grad_mem_span w s (q j) c f hc (fun k ↦ hw' _ (hfQ k))
        (hw' _ (hqQ j)) hs0
    · rw [Submodule.span_le, Set.range_subset_iff]
      intro k
      obtain ⟨i, hi⟩ := hgen (f k) (hfQ k)
      obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp hi
      refine JacobianRankOffHypersurface.grad_mem_span w (t ^ i) (f k) c q hc (fun j ↦ hw' _ (hqQ j))
        (hw' _ (hfQ k)) ?_
      rw [map_pow]
      exact pow_ne_zero _ ht0
  rw [heq, finrank_span_eq_card (hδ w hδ0)]
  exact hcard

/- English proof (translation)
Set `b` to `EuclideanSpace.basisFun (Fin n) ℂ`. Take `⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩` from `hF n d J hJ hd b`. Use `⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩` and prove the remaining obligations. Establish `h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card`. Rewrite using `[Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]`.

Establish `h2 : I₀.card ≤ n` using `(Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)`. Use linear arithmetic over natural numbers and integers. Introduce `w hw`. Set `M : Matrix {j // j ∉ I₀} (Fin n) ℂ` to `Matrix.of fun j l ↦ b j l`. Establish `hdet` using `hw`.

Rewrite `hdet` using `[frameJacobianDet, RingHom.map_det]`. Establish `hli` using `Matrix.linearIndependent_rows_of_det_ne_zero hdet`. Establish `hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) = (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k))`. Use function extensionality and compare the values at `k j`. Simplify using `[frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]`.

Rewrite `hli` using `[hrows]`. Conclude with `hli.of_comp _`.
-/
theorem JacobianRankOffHypersurface.exists_fin (hF : FrameJacobianGeneric.Statement) {n d : ℕ}
    (J : Ideal (MvPolynomial (Fin n) ℂ)) (hJ : J.IsPrime) (hd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d) :
    ∃ (I₀ : Finset (Fin n)) (f : {j // j ∉ I₀} → MvPolynomial (Fin n) ℂ) (s δ : MvPolynomial (Fin n) ℂ),
      Fintype.card {j // j ∉ I₀} + d = n ∧ (∀ k, f k ∈ J) ∧ s ∉ J ∧ δ ∉ J ∧
        (∀ p ∈ J, s * p ∈ Ideal.span (Set.range f)) ∧
        ∀ w : Fin n → ℂ, eval w δ ≠ 0 → LinearIndependent ℂ fun k l ↦ eval w (pderiv l (f k)) := by
  classical
  let b := EuclideanSpace.basisFun (Fin n) ℂ
  obtain ⟨I₀, f, s, hcard, hfJ, hsJ, hδJ, hgen⟩ := hF n d J hJ hd b
  refine ⟨I₀, f, s, frameJacobianDet b I₀ f, ?_, hfJ, hsJ, hδJ, hgen, ?_⟩
  · have h1 : Fintype.card {j // j ∉ I₀} = n - I₀.card := by
      rw [Fintype.card_subtype_compl, Fintype.card_fin, Fintype.card_coe]
    have h2 : I₀.card ≤ n := (Finset.card_le_univ I₀).trans_eq (Fintype.card_fin n)
    omega
  · intro w hw
    let M : Matrix {j // j ∉ I₀} (Fin n) ℂ := Matrix.of fun j l ↦ b j l
    have hdet := hw
    rw [frameJacobianDet, RingHom.map_det] at hdet
    have hli := Matrix.linearIndependent_rows_of_det_ne_zero hdet
    have hrows : (fun k ↦ ((eval w).mapMatrix (Matrix.of fun k j : {j // j ∉ I₀} ↦ frameDeriv b j (f k))) k) =
        (Matrix.mulVecLin M) ∘ fun k l ↦ eval w (pderiv l (f k)) := by
      funext k j
      simp [frameDeriv, M, Matrix.mulVec, dotProduct, map_sum]
    rw [hrows] at hli
    exact hli.of_comp _

/- English proof (translation)
Introduce `σ _ Q d r q t hQ hd hqQ htQ hgen`. Use `set n := Fintype.card σ`. Use `set e : σ ≃ Fin n := Fintype.equivFin σ`. Use `set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm`. Use `set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ`.

Establish `hJ : J.IsPrime` using `Ideal.IsPrime.comap _`. Establish `hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p` using `fun x p ↦ by`. Simplify using `[φ, eval_rename]`. Establish `hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d`. Rewrite using `[← hd]`.

Use `(ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm` and prove the remaining obligations. Conclude with `(Ideal.map_symm (I := Q) φ.toRingEquiv).symm`. Take `⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩` from `JacobianRankOffHypersurface.exists_fin hF J hJ hJd`. Establish `hfQ : ∀ k, φ (f k) ∈ Q` using `fun k ↦ Ideal.mem_comap.mp (hfJ k)`. Establish `hsQ : φ s ∉ Q` using `fun h ↦ hsJ (Ideal.mem_comap.mpr h)`.

Establish `hδQ : φ δ ∉ Q` using `fun h ↦ hδJ (Ideal.mem_comap.mpr h)`. Establish `hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k))`. Introduce `p hp`. Establish `hp' : φ.symm p ∈ J` using `Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])`. Take `⟨c, hc⟩` from `Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')`.

Use `Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩` and prove the remaining obligations. Use `congrArg φ hc` as an intermediate fact. Rewrite `this` using `[map_sum, map_mul, AlgEquiv.apply_symm_apply]`. Simplify `this` using `[map_mul]`. Establish `hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 → LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k)))`.

Introduce `w hw`. Rewrite `hw` using `[hφ]`. Establish `hL` using `(hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e) (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))`. Establish `hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) = (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k))`. Use function extensionality and compare the values at `k x`.

Simplify using `only [Function.comp_apply, LinearMap.funLeft_apply]`. Establish `hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k))`. Use `pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)` as an intermediate fact. Rewrite `this` using `[Equiv.symm_apply_apply]`. Conclude with `this`.

Rewrite using `[hx, hφ]`. Rewrite using `[hfam]`. Conclude with `hL`. Establish `hμQ : φ s * t * φ δ ∉ Q`. Introduce `h`.

Break down `hQ.mem_or_mem h with h | h` into its components or cases. Break down `hQ.mem_or_mem h with h | h` into its components or cases. Conclude with `hsQ h`. Conclude with `htQ h`. Conclude with `hδQ h`.

Conclude with `⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦ JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ hcard w hw hμ⟩`.
-/
theorem JacobianRankOffHypersurface.proof_of_frame (hF : FrameJacobianGeneric.Statement) :
    JacobianRankOffHypersurface.Statement := by
  intro σ _ Q d r q t hQ hd hqQ htQ hgen
  set n := Fintype.card σ
  set e : σ ≃ Fin n := Fintype.equivFin σ
  set φ : MvPolynomial (Fin n) ℂ ≃ₐ[ℂ] MvPolynomial σ ℂ := renameEquiv ℂ e.symm
  set J : Ideal (MvPolynomial (Fin n) ℂ) := Q.comap φ
  have hJ : J.IsPrime := Ideal.IsPrime.comap _
  have hφ : ∀ (x : σ → ℂ) (p : MvPolynomial (Fin n) ℂ), eval x (φ p) = eval (x ∘ e.symm) p := fun x p ↦ by
    simp [φ, eval_rename]
  have hJd : ringKrullDim (MvPolynomial (Fin n) ℂ ⧸ J) = d := by
    rw [← hd]
    refine (ringKrullDim_eq_of_ringEquiv (Ideal.quotientEquiv Q J φ.toRingEquiv.symm ?_)).symm
    exact (Ideal.map_symm (I := Q) φ.toRingEquiv).symm
  obtain ⟨I₀, f, s, δ, hcard, hfJ, hsJ, hδJ, hsgen, hlin⟩ :=
    JacobianRankOffHypersurface.exists_fin hF J hJ hJd
  have hfQ : ∀ k, φ (f k) ∈ Q := fun k ↦ Ideal.mem_comap.mp (hfJ k)
  have hsQ : φ s ∉ Q := fun h ↦ hsJ (Ideal.mem_comap.mpr h)
  have hδQ : φ δ ∉ Q := fun h ↦ hδJ (Ideal.mem_comap.mpr h)
  have hs : ∀ p ∈ Q, φ s * p ∈ Ideal.span (Set.range fun k ↦ φ (f k)) := by
    intro p hp
    have hp' : φ.symm p ∈ J := Ideal.mem_comap.mpr (by rwa [AlgEquiv.apply_symm_apply])
    obtain ⟨c, hc⟩ := Ideal.mem_span_range_iff_exists_fun.mp (hsgen _ hp')
    refine Ideal.mem_span_range_iff_exists_fun.mpr ⟨fun k ↦ φ (c k), ?_⟩
    have := congrArg φ hc
    rw [map_sum, map_mul, AlgEquiv.apply_symm_apply] at this
    simpa [map_mul] using this
  have hδ : ∀ w : σ → ℂ, eval w (φ δ) ≠ 0 →
      LinearIndependent ℂ fun k x ↦ eval w (pderiv x (φ (f k))) := by
    intro w hw
    rw [hφ] at hw
    have hL := (hlin _ hw).map' (LinearMap.funLeft ℂ ℂ e)
      (LinearMap.ker_eq_bot.mpr (LinearMap.funLeft_injective_of_surjective _ _ _ e.surjective))
    have hfam : (fun k x ↦ eval w (pderiv x (φ (f k)))) =
        (LinearMap.funLeft ℂ ℂ e) ∘ fun k l ↦ eval (w ∘ e.symm) (pderiv l (f k)) := by
      funext k x
      simp only [Function.comp_apply, LinearMap.funLeft_apply]
      have hx : pderiv x (φ (f k)) = φ (pderiv (e x) (f k)) := by
        have := pderiv_rename (R := ℂ) e.symm.injective (e x) (f k)
        rw [Equiv.symm_apply_apply] at this
        exact this
      rw [hx, hφ]
    rw [hfam]
    exact hL
  have hμQ : φ s * t * φ δ ∉ Q := by
    intro h
    rcases hQ.mem_or_mem h with h | h
    · rcases hQ.mem_or_mem h with h | h
      · exact hsQ h
      · exact htQ h
    · exact hδQ h
  exact ⟨φ s * t * φ δ, hμQ, fun w hw hμ ↦
    JacobianRankOffHypersurface.finrank_of_generators Q d r q t hqQ hgen (fun k ↦ φ (f k)) (φ s) (φ δ) hfQ hs hδ
      hcard w hw hμ⟩

/- English proof (translation)
The claim follows from `JacobianRankOffHypersurface.proof_of_frame (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)`.
-/
theorem JacobianRankOffHypersurface.proof : JacobianRankOffHypersurface.Statement :=
  JacobianRankOffHypersurface.proof_of_frame
    (FrameJacobianGeneric.proof JacobianRankGeneric.proof ConormalGenerationGeneric.proof)

end

end GroundTheory.Heights₂.Heights
