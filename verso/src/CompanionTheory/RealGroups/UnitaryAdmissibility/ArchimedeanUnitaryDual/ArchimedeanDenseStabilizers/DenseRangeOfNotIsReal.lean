import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.BlockTheory.AdelicCMFields.SupportedAtSplit
import CompanionTheory.SpectralGeometry.LocalGlobalProofs.NefEffectiveCones.ExistsNsmulMulVecMemHat
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsAdeleRingTensorEquivInfiniteProdFinite
import Formalism.PeriodIntegrals.OrbitalBoundsConclusion.UJClassFin

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix ComplexOrder MatrixOrder

namespace CompanionTheory.Rg.FlCls

/- English proof (translation)
Establish `hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ)` using `Subfield.isClosed_topologicalClosure _`. Break down `Complex.subfield_eq_of_closed hc with h1 | h1` into its components or cases. It suffices to derive a contradiction. Apply `h` to reduce the goal to its premises. Rewrite using `[ComplexEmbedding.isReal_iff]`.

Use extensionality with `x`. Establish `hx : σ x ∈ σ.fieldRange.topologicalClosure` using `Subfield.le_topologicalClosure _ ⟨x, rfl⟩`. Rewrite `hx` using `[h1]`. Take `⟨r, hr⟩` from `hx`. Rewrite using `[ComplexEmbedding.conjugate_coe_eq, ← hr]`.

Conclude with `Complex.conj_ofReal r`. Establish `: closure (Set.range σ) = Set.univ`. Use `congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1` as an intermediate fact. Conclude with `this`. Conclude with `dense_iff_closure_eq.2 this`.
-/
theorem denseRange_of_not_isReal {K : Type} [Field K] (σ : K →+* ℂ)
    (h : ¬ ComplexEmbedding.IsReal σ) : DenseRange σ := by
  have hc : IsClosed (σ.fieldRange.topologicalClosure : Set ℂ) :=
    Subfield.isClosed_topologicalClosure _
  rcases Complex.subfield_eq_of_closed hc with h1 | h1
  · exfalso
    apply h
    rw [ComplexEmbedding.isReal_iff]
    ext x
    have hx : σ x ∈ σ.fieldRange.topologicalClosure := Subfield.le_topologicalClosure _ ⟨x, rfl⟩
    rw [h1] at hx
    obtain ⟨r, hr⟩ := hx
    rw [ComplexEmbedding.conjugate_coe_eq, ← hr]
    exact Complex.conj_ofReal r
  · have : closure (Set.range σ) = Set.univ := by
      have := congrArg (fun S : Subfield ℂ => (S : Set ℂ)) h1
      exact this
    exact dense_iff_closure_eq.2 this

/- English proof (translation)
Set `e : Fin n ≃ Fin n ⊕ Fin 0` to `(Equiv.sumEmpty (Fin n) (Fin 0)).symm`. Establish `h1 : (J.reindex e e).PosDef`. Simplify using `using h.submatrix (e := e.symm) e.symm.injective`. Establish `hJ : PI.UJClassFin.Jpq n 0 = 1`. Use extensionality with `i j`.

Break down `i with i | i` into its components or cases. Break down `j with j | j` into its components or cases. Simplify using `[PI.UJClassFin.Jpq, Matrix.one_apply]`. Conclude with `j.elim0`. Conclude with `i.elim0`.

Use `set A := J.reindex e e with hA`. Establish `hS : star (CFC.sqrt A) = CFC.sqrt A` using `(CFC.sqrt_nonneg A).isSelfAdjoint`. Establish `hSS : CFC.sqrt A * CFC.sqrt A = A` using `CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg`. Establish `hu : IsUnit (CFC.sqrt A)`. Use `h1.isUnit` as an intermediate fact.

Rewrite `this` using `[← hSS]`. Conclude with `isUnit_of_mul_isUnit_left this`. Take `⟨U, hU⟩` from `hu`. Use `⟨e, U⁻¹, ?_⟩` and prove the remaining obligations. Establish `hc : PI.UJClassFin.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) = star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ)`.

Use extensionality with `i j`. Both sides reduce to the same expression. Establish `hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U`. Rewrite using `[hU, hS, hSS]`. Rewrite using `[hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]`.
-/
theorem hasSignature_of_posDef {n : ℕ} {J : Matrix (Fin n) (Fin n) ℂ} (h : J.PosDef) :
    PI.UJClassFin.HasSignature J n 0 := by
  let e : Fin n ≃ Fin n ⊕ Fin 0 := (Equiv.sumEmpty (Fin n) (Fin 0)).symm
  have h1 : (J.reindex e e).PosDef := by
    simpa using h.submatrix (e := e.symm) e.symm.injective
  have hJ : PI.UJClassFin.Jpq n 0 = 1 := by
    ext i j
    rcases i with i | i
    · rcases j with j | j
      · simp [PI.UJClassFin.Jpq, Matrix.one_apply]
      · exact j.elim0
    · exact i.elim0
  set A := J.reindex e e with hA
  have hS : star (CFC.sqrt A) = CFC.sqrt A := (CFC.sqrt_nonneg A).isSelfAdjoint
  have hSS : CFC.sqrt A * CFC.sqrt A = A := CFC.sqrt_mul_sqrt_self A h1.posSemidef.nonneg
  have hu : IsUnit (CFC.sqrt A) := by
    have := h1.isUnit
    rw [← hSS] at this
    exact isUnit_of_mul_isUnit_left this
  obtain ⟨U, hU⟩ := hu
  refine ⟨e, U⁻¹, ?_⟩
  have hc : PI.UJClassFin.cT (starRingEnd ℂ) ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix _ _ ℂ) =
      star ((U⁻¹ : GL (Fin n ⊕ Fin 0) ℂ) : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) := by
    ext i j; rfl
  have hA2 : A = star (U : Matrix (Fin n ⊕ Fin 0) (Fin n ⊕ Fin 0) ℂ) * U := by
    rw [hU, hS, hSS]
  rw [hJ, hc, ← hA, hA2, ← mul_assoc, ← star_mul, mul_assoc, Units.mul_inv, star_one, one_mul]

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] {n : ℕ}

/- English proof (translation)
Use `hasSignature_of_posDef (J := Gᵀ.map τ) ?_` and prove the remaining obligations. Establish `hH : (Gᵀ.map τ).IsHermitian`. Use extensionality with `i k`. Simplify using `only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]`. Rewrite using `[← hG.2.2.1 i k, hc]`.

Both sides reduce to the same expression. Establish `hd : DenseRange τ`. Use `denseRange_of_not_isReal τ fun hr => hG.2.1 ?_` and prove the remaining obligations. Use extensionality with `x`. Apply `τ.injective` to reduce the goal to its premises.

Rewrite using `[hc]`. Conclude with `RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) x`. Establish `hdn : DenseRange fun (l : Fin n → E) => (fun i => τ (l i))` using `DenseRange.piMap (fun _ : Fin n => hd)`. Establish `hco : ∀ l : Fin n → E, τ (hermE c G l l) = star (fun i => τ (l i)) ⬝ᵥ (Gᵀ.map τ).mulVec (fun i => τ (l i))`. Introduce `l`.

Simplify using `only [hermE, map_sum, map_mul, hc, dotProduct, Matrix.mulVec, Matrix.map_apply, Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum]`. Rewrite using `[Finset.sum_comm]`. Use `Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_` and prove the remaining obligations. Rewrite using `[starRingEnd_apply]`. Expand and normalize the polynomial expressions, which then agree.

Establish `hpsd : (Gᵀ.map τ).PosSemidef`. Use `Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_` and prove the remaining obligations. Rewrite using `[Complex.nonneg_iff]`. Use `⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩` and prove the remaining obligations. Use `hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((Gᵀ.map τ) *ᵥ y)).re) x ?_ ?_` and prove the remaining obligations.

Conclude with `isClosed_le continuous_const (by fun_prop)`. Introduce `l`. Distinguish the cases in `hl : l = 0`. Substitute `hl` using the available equality. Simplify using `[dotProduct]`.

Use `h _ hl` as an intermediate fact. Rewrite `this` using `[hco]`. Conclude with `this.le`. Rewrite using `[hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]`. Introduce `h0`.

Apply `hG.2.2.2` to reduce the goal to its premises. Apply `τ.injective` to reduce the goal to its premises. Rewrite using `[← Matrix.det_transpose, RingHom.map_det, map_zero]`. Conclude with `h0`.
-/
theorem hasSignature (c : E ≃ₐ[F] E) (G : Matrix (Fin n) (Fin n) E) (hG : IsHermForm c G)
    (hc : ∀ (σ : E →+* ℂ) (x : E), σ (c x) = starRingEnd ℂ (σ x)) (τ : E →+* ℂ)
    (h : ∀ x : Fin n → E, x ≠ 0 → 0 < (τ (hermE c G x x)).re) :
    PI.UJClassFin.HasSignature (Gᵀ.map τ) n 0 := by
  refine hasSignature_of_posDef (J := Gᵀ.map τ) ?_
  have hH : (Gᵀ.map τ).IsHermitian := by
    ext i k
    simp only [Matrix.conjTranspose_apply, Matrix.map_apply, Matrix.transpose_apply]
    rw [← hG.2.2.1 i k, hc]; rfl
  have hd : DenseRange τ := by
    refine denseRange_of_not_isReal τ fun hr => hG.2.1 ?_
    ext x
    apply τ.injective
    rw [hc]
    exact RingHom.congr_fun (ComplexEmbedding.isReal_iff.1 hr) x
  have hdn : DenseRange fun (l : Fin n → E) => (fun i => τ (l i)) :=
    DenseRange.piMap (fun _ : Fin n => hd)
  have hco : ∀ l : Fin n → E, τ (hermE c G l l) =
      star (fun i => τ (l i)) ⬝ᵥ (Gᵀ.map τ).mulVec (fun i => τ (l i)) := by
    intro l
    simp only [hermE, map_sum, map_mul, hc, dotProduct, Matrix.mulVec, Matrix.map_apply,
      Matrix.transpose_apply, Pi.star_apply, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    rw [starRingEnd_apply]; ring
  have hpsd : (Gᵀ.map τ).PosSemidef := by
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg hH fun x => ?_
    rw [Complex.nonneg_iff]
    refine ⟨?_, (hH.im_star_dotProduct_mulVec_self x).symm⟩
    refine hdn.induction_on (p := fun y => 0 ≤ (star y ⬝ᵥ ((Gᵀ.map τ) *ᵥ y)).re) x ?_ ?_
    · exact isClosed_le continuous_const (by fun_prop)
    · intro l
      by_cases hl : l = 0
      · subst hl
        simp [dotProduct]
      · have := h _ hl
        rw [hco] at this
        exact this.le
  rw [hpsd.posDef_iff_isUnit, Matrix.isUnit_iff_isUnit_det, isUnit_iff_ne_zero]
  intro h0
  apply hG.2.2.2
  apply τ.injective
  rw [← Matrix.det_transpose, RingHom.map_det, map_zero]
  exact h0

/- English proof (translation)
Take `⟨s, hs⟩` from `hL`. Use `choose f hf r hr using GlobalTheory.CompanionTheory.HatBound.exists_nat_mul_integer E`. Establish `hpos : 0 < ∏ x ∈ s, ∏ i, f (x i)` using `Finset.prod_pos fun x _ => Finset.prod_pos fun i _ => hf _`. Use `set m := ∏ x ∈ s, ∏ i, f (x i) with hm`. Use `⟨m, Nat.cast_ne_zero.2 hpos.ne', fun x hx i => ?_⟩` and prove the remaining obligations.

Establish `e : ((m : 𝓞 F) : F) • x i = (m : E) * x i`. Rewrite using `[Algebra.smul_def]`. Simplify using the standard rewrite rules. Rewrite using `[e]`. Use `clear e`.

Rewrite `hx` using `[← hs]`. Proceed by induction on `hx using Submodule.span_induction with`. Consider the case `mem x hx`. Take `⟨k, hk⟩ : f (x i) ∣ m` from `(Finset.dvd_prod_of_mem (fun i => f (x i)) (Finset.mem_univ i)).trans (Finset.dvd_prod_of_mem (fun x : Fin n → E => ∏ i, f (x i)) hx)`. Establish `: (m : E) * x i = ((k * r (x i) : 𝓞 E) : E)`.

Establish `h7 : ((k * r (x i) : 𝓞 E) : E) = (k : E) * (f (x i) * x i)`. Rewrite using `[← hr (x i)]`. Simplify using the standard rewrite rules. Rewrite using `[h7, hk]`. Use `push_cast`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `(k * r (x i) : 𝓞 E).isIntegral_coe`. Consider the case `zero => simpa using isIntegral_zero`. Consider the case `add x y _ _ hx hy => rw [Pi.add_apply, mul_add]`.

Conclude with `hx.add hy`. Consider the case `smul a x _ hx`. Establish `: (m : E) * (a • x) i = (a : E) * ((m : E) * x i)`. Rewrite using `[Pi.smul_apply, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.

Rewrite using `[this]`. Conclude with `a.isIntegral_coe.mul hx`.
-/
theorem exists_denom (L : Submodule (𝓞 E) (Fin n → E)) (hL : L.FG) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ x ∈ (L : Set (Fin n → E)), ∀ i, IsIntegral ℤ ((c : F) • x i) := by
  classical
  obtain ⟨s, hs⟩ := hL
  choose f hf r hr using GlobalTheory.CompanionTheory.HatBound.exists_nat_mul_integer E
  have hpos : 0 < ∏ x ∈ s, ∏ i, f (x i) := Finset.prod_pos fun x _ => Finset.prod_pos fun i _ => hf _
  set m := ∏ x ∈ s, ∏ i, f (x i) with hm
  refine ⟨m, Nat.cast_ne_zero.2 hpos.ne', fun x hx i => ?_⟩
  have e : ((m : 𝓞 F) : F) • x i = (m : E) * x i := by
    rw [Algebra.smul_def]; simp
  rw [e]
  clear e
  rw [← hs] at hx
  induction hx using Submodule.span_induction with
  | mem x hx =>
    obtain ⟨k, hk⟩ : f (x i) ∣ m := (Finset.dvd_prod_of_mem (fun i => f (x i)) (Finset.mem_univ i)).trans
      (Finset.dvd_prod_of_mem (fun x : Fin n → E => ∏ i, f (x i)) hx)
    have : (m : E) * x i = ((k * r (x i) : 𝓞 E) : E) := by
      have h7 : ((k * r (x i) : 𝓞 E) : E) = (k : E) * (f (x i) * x i) := by
        rw [← hr (x i)]; simp
      rw [h7, hk]; push_cast; ring
    rw [this]
    exact (k * r (x i) : 𝓞 E).isIntegral_coe
  | zero => simpa using isIntegral_zero
  | add x y _ _ hx hy => rw [Pi.add_apply, mul_add]; exact hx.add hy
  | smul a x _ hx =>
    have : (m : E) * (a • x) i = (a : E) * ((m : E) * x i) := by
      rw [Pi.smul_apply, Algebra.smul_def]; ring
    rw [this]
    exact a.isIntegral_coe.mul hx

/- English proof (translation)
Use `choose f hf hf' using fun i : Fin n => GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice L hL (Pi.single i 1)`. Establish `hpos : 0 < ∏ i, f i` using `Finset.prod_pos fun i _ => hf _`. Use `set m := ∏ i, f i with hm`. Use `⟨m, Nat.cast_ne_zero.2 hpos.ne', fun i e he => ?_⟩` and prove the remaining obligations. Take `⟨k, hk⟩ : f i ∣ m` from `Finset.dvd_prod_of_mem f (Finset.mem_univ i)`.

Establish `h1` using `L.smul_mem (⟨e, he⟩ : 𝓞 E) (nsmul_mem (hf' i) k)`. Establish `e2 : (Pi.single i (((m : 𝓞 F) : F) • e) : Fin n → E) = (⟨e, he⟩ : 𝓞 E) • k • f i • (Pi.single i (1 : E) : Fin n → E)`. Use function extensionality and compare the values at `j`. Express the relevant statement in the definitionally equal form `_ = e * (k • f i • (Pi.single i (1 : E) : Fin n → E) j)`. Distinguish the cases in `h : j = i`.

Substitute `h` using the available equality. Simplify using `[hk, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree. Simplify using `[h]`. Rewrite using `[e2]`.

Conclude with `h1`.
-/
theorem exists_single_mem (L : Submodule (𝓞 E) (Fin n → E))
    (hL : Submodule.span E (L : Set (Fin n → E)) = ⊤) :
    ∃ c : 𝓞 F, c ≠ 0 ∧ ∀ i, ∀ e : E, IsIntegral ℤ e →
      Pi.single i ((c : F) • e) ∈ (L : Set (Fin n → E)) := by
  classical
  choose f hf hf' using fun i : Fin n => GlobalTheory.CompanionTheory.HatBound.exists_nsmul_mem_lattice L hL (Pi.single i 1)
  have hpos : 0 < ∏ i, f i := Finset.prod_pos fun i _ => hf _
  set m := ∏ i, f i with hm
  refine ⟨m, Nat.cast_ne_zero.2 hpos.ne', fun i e he => ?_⟩
  obtain ⟨k, hk⟩ : f i ∣ m := Finset.dvd_prod_of_mem f (Finset.mem_univ i)
  have h1 := L.smul_mem (⟨e, he⟩ : 𝓞 E) (nsmul_mem (hf' i) k)
  have e2 : (Pi.single i (((m : 𝓞 F) : F) • e) : Fin n → E) =
      (⟨e, he⟩ : 𝓞 E) • k • f i • (Pi.single i (1 : E) : Fin n → E) := by
    funext j
    change _ = e * (k • f i • (Pi.single i (1 : E) : Fin n → E) j)
    by_cases h : j = i
    · subst h
      simp [hk, Algebra.smul_def]; ring
    · simp [h]
  rw [e2]
  exact h1

end CompanionTheory.Rg.FlCls
