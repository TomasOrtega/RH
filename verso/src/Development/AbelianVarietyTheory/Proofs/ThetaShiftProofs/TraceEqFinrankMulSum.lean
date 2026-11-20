import Mathlib
import Development.AbelianVarietyTheory.Proofs.ToricGeometry.ExistsEquivOfSumEq
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.HostGeneratorPowFourTraceNormModEight

open NumberField

namespace GlobalTheory.HomTrace

/- English proof (translation)
Rewrite using `[(addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).finrank_eq, Module.finrank_linearMap]`. Simplify using the standard rewrite rules.
-/
lemma finrank_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.finrank ℂ (X →+ ℂ) = Module.finrank ℤ X := by
  rw [(addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).finrank_eq, Module.finrank_linearMap]
  simp

/- English proof (translation)
The claim follows from `Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).symm`.
-/
lemma finite_hom (X : Type) [AddCommGroup X] [Module.Free ℤ X] [Module.Finite ℤ X] :
    Module.Finite ℂ (X →+ ℂ) :=
  Module.Finite.equiv (addMonoidHomLequivInt (A := X) (B := ℂ) ℂ).symm

/- English proof (translation)
Establish `: Module.Finite (𝓞 E) X` using `Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X`. Use `set r := Module.finrank (𝓞 E) X with hr`. Take `⟨v, hv⟩` from `exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) hr.le`. Set `j : (Fin r → 𝓞 E) →ₗ[𝓞 E] X` to `Fintype.linearCombination (𝓞 E) v`. Set `F : Submodule (𝓞 E) X` to `Submodule.span (𝓞 E) (Set.range v)`.

Establish `hF : Module.finrank (𝓞 E) F = r` using `by simpa using finrank_span_eq_card hv`. Establish `h0 : Module.finrank (𝓞 E) (X ⧸ F) = 0`. Use `F.finrank_quotient_add_finrank` as an intermediate fact. Use linear arithmetic over natural numbers and integers. Establish `htor : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ ∃ y, j y = n • x`.

Introduce `x`. Rewrite `h0` using `[Module.finrank_eq_zero_iff]`. Take `⟨c, hc, hx⟩` from `h0 (Submodule.Quotient.mk x)`. Take `⟨n, hn, b, hb⟩` from `(Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd (mem_nonZeroDivisors_of_ne_zero hc)`. Use `⟨n, hn, ?_⟩` and prove the remaining obligations.

Rewrite `hx` using `[← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero]`. Establish `h1 : n • x ∈ F`. Rewrite using `[← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul]`. Conclude with `F.smul_mem _ hx`. Rewrite `h1` using `[show F = LinearMap.range j from (Fintype.range_linearCombination _ _).symm]`.

Conclude with `h1`. Set `R : (X →+ ℂ) →ₗ[ℂ] ((Fin r → 𝓞 E) →+ ℂ)` to `{ toFun := fun l => l.comp j.toAddMonoidHom map_add' := fun _ _ => rfl map_smul' := fun _ _ => rfl }`. Establish `hR : ∀ l y, R l y = l (j y)` using `fun _ _ => rfl`. Establish `hinj : Function.Injective R`. Rewrite using `[injective_iff_map_eq_zero]`.

Introduce `l hl`. Use extensionality with `x`. Take `⟨n, hn, y, hy⟩` from `htor x`. Establish `h1 : l (j y) = 0` using `by rw [← hR, hl]; rfl`. Rewrite `h1` using `[hy, map_zsmul, zsmul_eq_mul]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn)`. Use `finite_hom X` as an intermediate fact. Use `finite_hom (Fin r → 𝓞 E)` as an intermediate fact. Establish `hdY : Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) = r * Module.finrank ℚ E`. Rewrite using `[finrank_hom, Module.finrank_pi_fintype]`.

Simplify using `[RingOfIntegers.rank]`. Establish `hdim : Module.finrank ℂ (X →+ ℂ) = Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ)`. Rewrite using `[hdY, finrank_hom, finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank, mul_comm]`. Set `e` to `LinearMap.linearEquivOfInjective R hinj hdim`. Set `g : (E →+* ℂ) → (𝓞 E →* ℂ)` to `fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom`.

Establish `hg : Function.Injective g`. Introduce `φ ψ hφ`. Apply `(EigenSplit.isSplitting_complex E).injective` to reduce the goal to its premises. Use extensionality with `a`. Conclude with `DFunLike.congr_fun hφ a`.

Establish `hli` using `(linearIndependent_monoidHom (𝓞 E) ℂ).comp g hg`. Set `w : Fin r × (E →+* ℂ) → ((Fin r → 𝓞 E) →+ ℂ)` to `fun p => ((p.2.comp (algebraMap (𝓞 E) E)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ => 𝓞 E) p.1)`. Establish `hw : ∀ p y, w p y = p.2 (y p.1 : E)` using `fun _ _ => rfl`. Establish `hwli : LinearIndependent ℂ w`. Rewrite using `[Fintype.linearIndependent_iff]`.

Introduce and unpack `c hc ⟨i, τ⟩`. Use `Fintype.linearIndependent_iff.1 hli (fun φ => c (i, φ)) ?_ τ` and prove the remaining obligations. Use function extensionality and compare the values at `y`. Establish `h1` using `DFunLike.congr_fun hc (Pi.single i y)`. Rewrite `h1` using `[AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i]`.

Simplify `h1` using `[hw, g]`. Introduce `k _ hk`. Simplify using `[hw, Pi.single_eq_of_ne hk]`. Simplify using the standard rewrite rules. Set `b` to `basisOfLinearIndependentOfCardEqFinrank' w hwli (by`.

Rewrite using `[hdY, Fintype.card_prod, Fintype.card_fin, Embeddings.card])`. Set `c` to `b.map e.symm`. Establish `hc : ∀ p, R (c p) = w p` using `fun p => by`. Establish `: e (c p) = b p` using `by simp [c]`. Rewrite using `[← show b p = w p by simp [b], ← this]; rfl`.

Establish `hfc : ∀ p, f (c p) = p.2 (a : E) • c p` using `fun p => by`. Apply `hinj` to reduce the goal to its premises. Use `AddMonoidHom.ext fun y => ?_` and prove the remaining obligations. Rewrite using `[map_smul, hR, hf, ← j.map_smul, ← hR, hc, AddMonoidHom.smul_apply, hw, hw]`. Simplify using the standard rewrite rules.

Rewrite using `[LinearMap.trace_eq_matrix_trace ℂ c]`. Simplify using `[Matrix.trace, LinearMap.toMatrix_apply, hfc, Fintype.sum_prod_type]`.
-/
theorem trace_eq_finrank_mul_sum (E : Type) [Field E] [NumberField E] (X : Type) [AddCommGroup X]
    [Module (𝓞 E) X] [Module.Free ℤ X] [Module.Finite ℤ X] (a : 𝓞 E) (f : (X →+ ℂ) →ₗ[ℂ] (X →+ ℂ))
    (hf : ∀ l x, f l x = l (a • x)) :
    LinearMap.trace ℂ (X →+ ℂ) f = (Module.finrank (𝓞 E) X : ℂ) * ∑ τ : E →+* ℂ, τ (a : E) := by
  classical
  have : Module.Finite (𝓞 E) X := Module.Finite.of_restrictScalars_finite ℤ (𝓞 E) X
  set r := Module.finrank (𝓞 E) X with hr
  obtain ⟨v, hv⟩ := exists_linearIndependent_of_le_finrank (R := 𝓞 E) (M := X) hr.le
  let j : (Fin r → 𝓞 E) →ₗ[𝓞 E] X := Fintype.linearCombination (𝓞 E) v
  let F : Submodule (𝓞 E) X := Submodule.span (𝓞 E) (Set.range v)
  have hF : Module.finrank (𝓞 E) F = r := by simpa using finrank_span_eq_card hv
  have h0 : Module.finrank (𝓞 E) (X ⧸ F) = 0 := by
    have := F.finrank_quotient_add_finrank
    omega
  have htor : ∀ x : X, ∃ n : ℤ, n ≠ 0 ∧ ∃ y, j y = n • x := by
    intro x
    rw [Module.finrank_eq_zero_iff] at h0
    obtain ⟨c, hc, hx⟩ := h0 (Submodule.Quotient.mk x)
    obtain ⟨n, hn, b, hb⟩ := (Algebra.IsAlgebraic.isAlgebraic (R := ℤ) c).exists_nonzero_dvd
      (mem_nonZeroDivisors_of_ne_zero hc)
    refine ⟨n, hn, ?_⟩
    rw [← Submodule.Quotient.mk_smul, Submodule.Quotient.mk_eq_zero] at hx
    have h1 : n • x ∈ F := by
      rw [← algebraMap_smul (𝓞 E) n x, hb, mul_comm, mul_smul]
      exact F.smul_mem _ hx
    rw [show F = LinearMap.range j from (Fintype.range_linearCombination _ _).symm] at h1
    exact h1
  let R : (X →+ ℂ) →ₗ[ℂ] ((Fin r → 𝓞 E) →+ ℂ) :=
    { toFun := fun l => l.comp j.toAddMonoidHom
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  have hR : ∀ l y, R l y = l (j y) := fun _ _ => rfl
  have hinj : Function.Injective R := by
    rw [injective_iff_map_eq_zero]
    intro l hl
    ext x
    obtain ⟨n, hn, y, hy⟩ := htor x
    have h1 : l (j y) = 0 := by rw [← hR, hl]; rfl
    rw [hy, map_zsmul, zsmul_eq_mul] at h1
    exact (mul_eq_zero.1 h1).resolve_left (by exact_mod_cast hn)
  have := finite_hom X
  have := finite_hom (Fin r → 𝓞 E)
  have hdY : Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) = r * Module.finrank ℚ E := by
    rw [finrank_hom, Module.finrank_pi_fintype]
    simp [RingOfIntegers.rank]
  have hdim : Module.finrank ℂ (X →+ ℂ) = Module.finrank ℂ ((Fin r → 𝓞 E) →+ ℂ) := by
    rw [hdY, finrank_hom, finrank_int_eq_mul_of_finite (O := 𝓞 E), RingOfIntegers.rank, mul_comm]
  let e := LinearMap.linearEquivOfInjective R hinj hdim
  let g : (E →+* ℂ) → (𝓞 E →* ℂ) := fun φ => (φ.comp (algebraMap (𝓞 E) E)).toMonoidHom
  have hg : Function.Injective g := by
    intro φ ψ hφ
    apply (EigenSplit.isSplitting_complex E).injective
    ext a
    exact DFunLike.congr_fun hφ a
  have hli := (linearIndependent_monoidHom (𝓞 E) ℂ).comp g hg
  let w : Fin r × (E →+* ℂ) → ((Fin r → 𝓞 E) →+ ℂ) := fun p =>
    ((p.2.comp (algebraMap (𝓞 E) E)).toAddMonoidHom).comp (Pi.evalAddMonoidHom (fun _ => 𝓞 E) p.1)
  have hw : ∀ p y, w p y = p.2 (y p.1 : E) := fun _ _ => rfl
  have hwli : LinearIndependent ℂ w := by
    rw [Fintype.linearIndependent_iff]
    rintro c hc ⟨i, τ⟩
    refine Fintype.linearIndependent_iff.1 hli (fun φ => c (i, φ)) ?_ τ
    funext y
    have h1 := DFunLike.congr_fun hc (Pi.single i y)
    rw [AddMonoidHom.finsetSum_apply, Fintype.sum_prod_type, Finset.sum_eq_single i] at h1
    · simpa [hw, g] using h1
    · intro k _ hk
      simp [hw, Pi.single_eq_of_ne hk]
    · simp
  let b := basisOfLinearIndependentOfCardEqFinrank' w hwli (by
    rw [hdY, Fintype.card_prod, Fintype.card_fin, Embeddings.card])
  let c := b.map e.symm
  have hc : ∀ p, R (c p) = w p := fun p => by
    have : e (c p) = b p := by simp [c]
    rw [← show b p = w p by simp [b], ← this]; rfl
  have hfc : ∀ p, f (c p) = p.2 (a : E) • c p := fun p => by
    apply hinj
    refine AddMonoidHom.ext fun y => ?_
    rw [map_smul, hR, hf, ← j.map_smul, ← hR, hc, AddMonoidHom.smul_apply, hw, hw]
    simp
  rw [LinearMap.trace_eq_matrix_trace ℂ c]
  simp [Matrix.trace, LinearMap.toMatrix_apply, hfc, Fintype.sum_prod_type]

end GlobalTheory.HomTrace
