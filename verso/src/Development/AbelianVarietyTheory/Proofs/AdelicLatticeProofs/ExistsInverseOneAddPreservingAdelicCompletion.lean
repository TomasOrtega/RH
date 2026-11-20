import Mathlib
import Development.AbelianVarietyTheory.Definitions.AdelicHermitianForms.IsHermForm
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.AdelicCompletionRationalPointsAndApproximation

open NumberField IsDedekindDomain GlobalTheory.AdLat GlobalTheory.UnRep
open scoped TensorProduct Matrix

namespace GlobalTheory.UnRep.Nakayama

variable (F : Type) [Field F] [NumberField F]

def intAdeles : Subring (FiniteAdeleRing (𝓞 F) F) where
  carrier := {a | ∀ v, a v ∈ v.adicCompletionIntegers F}
  mul_mem' ha hb v := mul_mem (ha v) (hb v)
  one_mem' v := one_mem (v.adicCompletionIntegers F)
  add_mem' ha hb v := add_mem (ha v) (hb v)
  zero_mem' v := zero_mem (v.adicCompletionIntegers F)
  neg_mem' ha v := neg_mem (ha v)

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable (F : Type) [Field F] [NumberField F] in

/- English proof (translation)
Rewrite using `[Ideal.mem_jacobson_bot]`. Introduce `y`. Establish `hval : ∀ v, Valued.v ((a * y + 1).1 v) = 1`. Introduce `v`. Establish `hy : Valued.v (y.1 v) ≤ 1` using `(y.2 v)`.

Establish `hlt : Valued.v (a.1 v * y.1 v) < 1`. Rewrite using `[map_mul]`. Combine the equalities or inequalities in the displayed calculation. Establish `: (a * y + 1).1 v = 1 + a.1 v * y.1 v`. Simplify using `[add_comm]`.

Rewrite using `[this, Valuation.map_one_add_of_lt _ hlt]`. Set `w : FiniteAdeleRing (𝓞 F) F` to `⟨fun v ↦ ((a * y + 1).1 v)⁻¹, Filter.Eventually.of_forall fun v ↦ by show _ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v, inv_one]⟩`. Establish `hw : w ∈ _root_.GlobalTheory.UnRep.Nakayama.intAdeles F` using `fun v ↦ by show _ ∈ v.adicCompletionIntegers F`. Rewrite using `[HeightOneSpectrum.mem_adicCompletionIntegers]`.

Use `show Valued.v ((a * y + 1).1 v)⁻¹ ≤ 1`. Rewrite using `[map_inv₀, hval v, inv_one]`. Use `isUnit_iff_exists_inv.mpr ⟨⟨w, hw⟩, ?_⟩` and prove the remaining obligations. Apply `Subtype.ext` to reduce the goal to its premises. Apply `RestrictedProduct.ext` to reduce the goal to its premises.

Introduce `v`. Establish `hne : (a * y + 1).1 v ≠ 0`. Introduce `h`. Use `hval v` as an intermediate fact. Rewrite `this` using `[h, map_zero]`.

Conclude with `zero_ne_one this`. Conclude with `mul_inv_cancel₀ hne`.
-/
theorem _root_.GlobalTheory.UnRep.Nakayama.mem_jacobson (a : _root_.GlobalTheory.UnRep.Nakayama.intAdeles F)
    (ha : ∀ v, Valued.v (a.1 v) < 1) :
    a ∈ Ideal.jacobson (⊥ : Ideal (_root_.GlobalTheory.UnRep.Nakayama.intAdeles F)) := by
  rw [Ideal.mem_jacobson_bot]
  intro y
  have hval : ∀ v, Valued.v ((a * y + 1).1 v) = 1 := by
    intro v
    have hy : Valued.v (y.1 v) ≤ 1 := (y.2 v)
    have hlt : Valued.v (a.1 v * y.1 v) < 1 := by
      rw [map_mul]
      calc Valued.v (a.1 v) * Valued.v (y.1 v) ≤ Valued.v (a.1 v) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact ha v
    have : (a * y + 1).1 v = 1 + a.1 v * y.1 v := by
      simp [add_comm]
    rw [this, Valuation.map_one_add_of_lt _ hlt]
  let w : FiniteAdeleRing (𝓞 F) F := ⟨fun v ↦ ((a * y + 1).1 v)⁻¹, Filter.Eventually.of_forall fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers, map_inv₀, hval v, inv_one]⟩
  have hw : w ∈ _root_.GlobalTheory.UnRep.Nakayama.intAdeles F := fun v ↦ by
    show _ ∈ v.adicCompletionIntegers F
    rw [HeightOneSpectrum.mem_adicCompletionIntegers]
    show Valued.v ((a * y + 1).1 v)⁻¹ ≤ 1
    rw [map_inv₀, hval v, inv_one]
  refine isUnit_iff_exists_inv.mpr ⟨⟨w, hw⟩, ?_⟩
  apply Subtype.ext
  apply RestrictedProduct.ext
  intro v
  have hne : (a * y + 1).1 v ≠ 0 := by
    intro h
    have := hval v
    rw [h, map_zero] at this
    exact zero_ne_one this
  exact mul_inv_cancel₀ hne

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable (F : Type) [Field F] [NumberField F] in
/- English proof (translation)
Establish `h` using `(v.valuation_lt_one_iff_mem (K := F) (N : 𝓞 F)).mpr hv`. Establish `h2` using `HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)`. Rewrite `h` using `[← h2]`. Use `h using 2` and compare the differences between its conclusion and the goal. Use `first`.

Consider the case `simp`. Consider the case `norm_cast`. Consider the case `(push_cast; rfl)`.
-/
theorem _root_.GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one (N : ℕ) (v : HeightOneSpectrum (𝓞 F)) (hv : (N : 𝓞 F) ∈ v.asIdeal) :
    Valued.v ((N : ℕ) : v.adicCompletion F) < 1 := by
  have h := (v.valuation_lt_one_iff_mem (K := F) (N : 𝓞 F)).mpr hv
  have h2 := HeightOneSpectrum.valuedAdicCompletion_eq_valuation (K := F) v (N : 𝓞 F)
  rw [← h2] at h
  convert h using 2
  first
  | simp
  | norm_cast
  | (push_cast; rfl)

variable {E : Type} [Field E] [NumberField E] [Algebra F E] {n : ℕ}

end GlobalTheory.UnRep.Nakayama

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.AdLat.hat at hz ⊢`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`. Take `⟨a, ha, y, hy, rfl⟩` from `hx`. Use `AddSubgroup.subset_closure ⟨b * a, fun v ↦ mul_mem (hb v) (ha v), y, hy, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Rewrite using `[smul_add]`.

Conclude with `add_mem hx hy`. Consider the case `neg x _ hx`. Rewrite using `[smul_neg]`. Conclude with `neg_mem hx`.
-/
private lemma integral_tmul_smul_mem_hat {S : Set (Fin n → E)} {b : FiniteAdeleRing (𝓞 F) F}
    (hb : ∀ v, b v ∈ v.adicCompletionIntegers F) {z : Fin n → _root_.GlobalTheory.AdLat.RA F E}
    (hz : z ∈ _root_.GlobalTheory.AdLat.hat F S) :
    (b ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • z ∈ _root_.GlobalTheory.AdLat.hat F S := by
  unfold _root_.GlobalTheory.AdLat.hat at hz ⊢
  induction hz using AddSubgroup.closure_induction with
  | mem x hx =>
    obtain ⟨a, ha, y, hy, rfl⟩ := hx
    refine AddSubgroup.subset_closure ⟨b * a, fun v ↦ mul_mem (hb v) (ha v), y, hy, ?_⟩
    funext i
    simp [Algebra.TensorProduct.tmul_mul_tmul]
  | zero => simp
  | add x y _ _ hx hy =>
    rw [smul_add]
    exact add_mem hx hy
  | neg x _ hx =>
    rw [smul_neg]
    exact neg_mem hx

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
variable {F E : Type} [Field F] [NumberField F] [Field E] [Algebra F E] {n : ℕ} in
/- English proof (translation)
Unfold `_root_.GlobalTheory.AdLat.hat`. Conclude with `AddSubgroup.subset_closure ⟨1, fun v ↦ one_mem (v.adicCompletionIntegers F), x, hx, rfl⟩`.
-/
private lemma one_tmul_mem_hat {S : Set (Fin n → E)} {x : Fin n → E} (hx : x ∈ S) :
    (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ _root_.GlobalTheory.AdLat.hat F S := by
  unfold _root_.GlobalTheory.AdLat.hat
  exact AddSubgroup.subset_closure
    ⟨1, fun v ↦ one_mem (v.adicCompletionIntegers F), x, hx, rfl⟩

open NumberField IsDedekindDomain in
open scoped TensorProduct Matrix in
open NumberField IsDedekindDomain in

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L hLfg hspan N e he hsupp X hX`. Use `set Λ := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hΛ`. Use `set A := _root_.GlobalTheory.UnRep.Nakayama.intAdeles F`. Use `set M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E) := (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X) with hM`. Establish `hsmulA : ∀ (c : A) {z}, z ∈ Λ → c • z ∈ Λ`.

Introduce `c z hz`. Establish `h` using `integral_tmul_smul_mem_hat (F := F) c.2 hz`. Use `h using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `i`. Apply the tactic sequence `simp [Subring.smul_def, Algebra.smul_def] <;> rfl`.

Set `ΛA : Submodule A (Fin n → _root_.GlobalTheory.AdLat.RA F E)` to `{ Λ with smul_mem' := fun c z hz ↦ hsmulA c hz }`. Establish `hmemA : ∀ z, z ∈ ΛA ↔ z ∈ Λ` using `fun z ↦ Iff.rfl`. Take `⟨T, hT⟩` from `hLfg.restrictScalars (R := ℤ)`. Use `set g : (Fin n → E) → (Fin n → _root_.GlobalTheory.AdLat.RA F E) := fun x i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i with hg`. Establish `hTL : ∀ x ∈ T, x ∈ L`.

Introduce `x hx`. Establish `: x ∈ L.restrictScalars ℤ` using `hT ▸ Submodule.subset_span hx`. Conclude with `this`. Establish `hfg : ΛA.FG`. Use `⟨T.image g, le_antisymm ?_ ?_⟩` and prove the remaining obligations.

Rewrite using `[Submodule.span_le]`. Introduce `z hz`. Simplify using `only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz`. Take `⟨x, hx, rfl⟩` from `hz`. Conclude with `one_tmul_mem_hat (hTL x hx)`.

Introduce `z hz`. Express the relevant statement in the definitionally equal form `z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) at hz`. Unfold `_root_.GlobalTheory.AdLat.hat at hz`. Proceed by induction on `hz using AddSubgroup.closure_induction with`. Consider the case `mem x hx`.

Take `⟨b, hb, y, hyL, rfl⟩` from `hx`. Establish `hyT : y ∈ Submodule.span ℤ (T : Set (Fin n → E))`. Rewrite using `[hT]`. Conclude with `hyL`. Use `clear hyL`.

Proceed by induction on `hyT using Submodule.span_induction with`. Consider the case `mem y hy`. Establish `h1 : (fun i ↦ b ⊗ₜ[F] y i) = (⟨b, hb⟩ : A) • g y`. Use function extensionality and compare the values at `i`. Simplify using `[hg, Subring.smul_def, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]`.

Both sides reduce to the same expression. Rewrite using `[h1]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span (by simp; exact ⟨y, hy, rfl⟩))`. Consider the case `zero`. Establish `h0 : (fun i ↦ b ⊗ₜ[F] (0 : Fin n → E) i) = 0`.

Use function extensionality and compare the values at `i`. Simplify using the standard rewrite rules. Rewrite using `[h0]`. Conclude with `zero_mem _`. Consider the case `add y y' _ _ ihy ihy'`.

Establish `h1 : (fun i ↦ b ⊗ₜ[F] (y + y') i) = (fun i ↦ b ⊗ₜ[F] y i) + fun i ↦ b ⊗ₜ[F] y' i`. Use function extensionality and compare the values at `i`. Simplify using `[TensorProduct.tmul_add]`. Rewrite using `[h1]`. Conclude with `add_mem ihy ihy'`.

Consider the case `smul m y _ ihy`. Establish `h1 : (fun i ↦ b ⊗ₜ[F] (m • y) i) = m • fun i ↦ b ⊗ₜ[F] y i`. Use function extensionality and compare the values at `i`. Conclude with `map_zsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E b) m (y i)`. Rewrite using `[h1]`.

Conclude with `zsmul_mem ihy m`. Consider the case `zero => exact zero_mem _`. Consider the case `add x y _ _ hx hy => exact add_mem hx hy`. Consider the case `neg x _ hx => exact neg_mem hx`. Establish `hNe : ∀ v, (N • e) v ∈ v.adicCompletionIntegers F`.

Introduce `v`. Use `show N • e v ∈ _`. Conclude with `nsmul_mem (he v) N`. Use `set a' : A := ⟨N • e, hNe⟩ with ha'`. Establish `hjac : a' ∈ Ideal.jacobson (⊥ : Ideal A)`.

Apply `_root_.GlobalTheory.UnRep.Nakayama.mem_jacobson` to reduce the goal to its premises. Introduce `v`. Use `show Valued.v (N • e v) < 1`. Rewrite using `[nsmul_eq_mul, map_mul]`. Distinguish the cases in `hv : (N : 𝓞 F) ∈ v.asIdeal`.

Establish `h1` using `_root_.GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one F N v hv`. Establish `h2 : Valued.v (e v) ≤ 1` using `(HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (he v)`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[hsupp v hv, map_zero, mul_zero]`. Conclude with `zero_lt_one`.

Establish `hI : Ideal.span {a'} ≤ Ideal.jacobson (⊥ : Ideal A)` using `(Ideal.span_singleton_le_iff_mem _).mpr hjac`. Set `f : (Fin n → _root_.GlobalTheory.AdLat.RA F E) →ₗ[A] (Fin n → _root_.GlobalTheory.AdLat.RA F E)` to `(Matrix.mulVecLin (1 + M)).restrictScalars A`. Establish `hf : ∀ z, f z = z + M *ᵥ z`. Introduce `z`. Use `show (1 + M) *ᵥ z = _`.

Rewrite using `[Matrix.add_mulVec, Matrix.one_mulVec]`. Establish `hMz : ∀ z, M *ᵥ z = a' • (X *ᵥ z)`. Introduce `z`. Rewrite using `[hM, Matrix.smul_mulVec, Matrix.smul_mulVec]`. Use function extensionality and compare the values at `i`.

Use `show (e ⊗ₜ[F] (1 : E)) * (N • (X *ᵥ z) i) = (N • e) • (X *ᵥ z) i`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[mul_smul_comm, smul_mul_assoc]`. Use `_ = ((N • e) ⊗ₜ[F] (1 : E)) * (X *ᵥ z) i := by rw [TensorProduct.smul_tmul']`. Use `_ = ((N • e) • (1 : _root_.GlobalTheory.AdLat.RA F E)) * (X *ᵥ z) i := by`.

Rewrite using `[Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]`. Use `_ = (N • e) • (X *ᵥ z) i := smul_one_mul _ _`. Establish `hle : ΛA ≤ ΛA.map f ⊔ Ideal.span {a'} • ΛA`. Introduce `z hz`. Rewrite using `[Submodule.mem_sup]`.

Use `⟨f z, ⟨z, hz, rfl⟩, -(M *ᵥ z), ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hMz]`. Conclude with `neg_mem (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a') (hX z hz))`. Rewrite using `[hf]`. Normalize the expressions using the abelian group laws.

Establish `hsurj : ∀ z ∈ Λ, ∃ y ∈ Λ, (1 + M) *ᵥ y = z`. Introduce `z hz`. Take `⟨y, hy, hyz⟩` from `Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI hle hz`. Conclude with `⟨y, hy, hyz⟩`. Set `R` to `LinearMap.range (Matrix.mulVecLin (1 + M))`.

Establish `hR : ∀ z ∈ Λ, z ∈ R`. Introduce `z hz`. Take `⟨y, -, hy⟩` from `hsurj z hz`. Conclude with `⟨y, hy⟩`. Set `V : Submodule E (Fin n → E)` to `{ carrier := {x | (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ R} add_mem' := by`.

Introduce `x y hx hy`. Establish `h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x + y) i) = (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) + fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y i`. Use function extensionality and compare the values at `i`. Simplify using `[TensorProduct.tmul_add]`. Use `show _ ∈ R`.

Rewrite using `[h1]`. Conclude with `add_mem hx hy`. Use the proof step `zero_mem' := by`. Establish `h0 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : Fin n → E) i) = 0`. Use function extensionality and compare the values at `i`.

Simplify using the standard rewrite rules. Use `show _ ∈ R`. Rewrite using `[h0]`. Conclude with `zero_mem _`. Use the proof step `smul_mem' := by`.

Introduce `c x hx`. Establish `h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c • x) i) = ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : _root_.GlobalTheory.AdLat.RA F E) • fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i`. Use function extensionality and compare the values at `i`. Simplify using `[Algebra.TensorProduct.tmul_mul_tmul]`. Use `show _ ∈ R`.

Rewrite using `[h1]`. Conclude with `R.smul_mem _ hx }`. Establish `hLV : Submodule.span E (L : Set (Fin n → E)) ≤ V`. Rewrite using `[Submodule.span_le]`. Introduce `x hx`.

Conclude with `hR _ (one_tmul_mem_hat hx)`. Establish `hsingle : ∀ i, (Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E) : Fin n → _) ∈ R`. Introduce `i`. Establish `hi : (Pi.single i (1 : E) : Fin n → E) ∈ V`. Apply `hLV` to reduce the goal to its premises.

Rewrite using `[hspan]`. Conclude with `Submodule.mem_top`. Establish `h1 : (fun j ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (Pi.single i (1 : E) : Fin n → E) j) = Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E)`. Use function extensionality and compare the values at `j`. Distinguish the cases in `hj : j = i`.

Substitute `hj` using the available equality. Simplify using `[Algebra.TensorProduct.one_def]`. Simplify using `[Pi.single_apply, hj]`. Rewrite using `[← h1]`. Conclude with `hi`.

Use `choose w hw using hsingle`. Establish `hW : (1 + M) * Matrix.of (fun r i ↦ w i r) = 1`. Use extensionality with `r i`. Establish `h` using `congrFun (hw i) r`. Simplify using `only [Matrix.mulVecLin_apply] at h`.

Rewrite using `[Matrix.mul_apply, Matrix.one_apply]`. Rewrite `h` using `[Matrix.mulVec, dotProduct]`. Simplify using `only [Matrix.of_apply]`. Rewrite using `[h, Pi.single_apply]`. Use `⟨Matrix.of fun r i ↦ w i r, hW, ?_⟩` and prove the remaining obligations.

Introduce `z hz`. Take `⟨y, hy, rfl⟩` from `hsurj z hz`. Establish `hW' : Matrix.of (fun r i ↦ w i r) * (1 + M) = 1` using `mul_eq_one_comm.mp hW`. Rewrite using `[Matrix.mulVec_mulVec, hW', Matrix.one_mulVec]`. Conclude with `hy`.
-/
theorem _root_.GlobalTheory.UnRep.exists_inverse_one_add_preserving_hat : ∀ (F E : Type) [Field F] [NumberField F]
    [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)), L.FG →
    Submodule.span E (L : Set (Fin n → E)) = ⊤ → ∀ (N : ℕ) (e : FiniteAdeleRing (𝓞 F) F),
    (∀ v, e v ∈ v.adicCompletionIntegers F) →
    (∀ v : HeightOneSpectrum (𝓞 F), (N : 𝓞 F) ∉ v.asIdeal → e v = 0) →
    ∀ X : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
    (∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
      X *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E))) →
    ∃ W : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E),
      (1 + (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X)) * W = 1 ∧
      ∀ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)),
        W *ᵥ z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) := by
  intro F E _ _ _ _ _ n L hLfg hspan N e he hsupp X hX
  classical
  set Λ := _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) with hΛ
  set A := _root_.GlobalTheory.UnRep.Nakayama.intAdeles F
  set M : Matrix (Fin n) (Fin n) (_root_.GlobalTheory.AdLat.RA F E) :=
    (e ⊗ₜ[F] (1 : E) : _root_.GlobalTheory.AdLat.RA F E) • (N • X) with hM

  have hsmulA : ∀ (c : A) {z}, z ∈ Λ → c • z ∈ Λ := by
    intro c z hz
    have h := integral_tmul_smul_mem_hat (F := F) c.2 hz
    convert h using 1
    funext i
    simp [Subring.smul_def, Algebra.smul_def] <;> rfl
  let ΛA : Submodule A (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    { Λ with smul_mem' := fun c z hz ↦ hsmulA c hz }
  have hmemA : ∀ z, z ∈ ΛA ↔ z ∈ Λ := fun z ↦ Iff.rfl

  obtain ⟨T, hT⟩ := hLfg.restrictScalars (R := ℤ)
  set g : (Fin n → E) → (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    fun x i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i with hg
  have hTL : ∀ x ∈ T, x ∈ L := by
    intro x hx
    have : x ∈ L.restrictScalars ℤ := hT ▸ Submodule.subset_span hx
    exact this
  have hfg : ΛA.FG := by
    refine ⟨T.image g, le_antisymm ?_ ?_⟩
    · rw [Submodule.span_le]
      intro z hz
      simp only [Finset.coe_image, Set.mem_image, Finset.mem_coe] at hz
      obtain ⟨x, hx, rfl⟩ := hz
      exact one_tmul_mem_hat (hTL x hx)
    · intro z hz
      change z ∈ _root_.GlobalTheory.AdLat.hat F (L : Set (Fin n → E)) at hz
      unfold _root_.GlobalTheory.AdLat.hat at hz
      induction hz using AddSubgroup.closure_induction with
      | mem x hx =>
        obtain ⟨b, hb, y, hyL, rfl⟩ := hx
        have hyT : y ∈ Submodule.span ℤ (T : Set (Fin n → E)) := by
          rw [hT]
          exact hyL
        clear hyL
        induction hyT using Submodule.span_induction with
        | mem y hy =>
          have h1 : (fun i ↦ b ⊗ₜ[F] y i) = (⟨b, hb⟩ : A) • g y := by
            funext i
            simp [hg, Subring.smul_def, Algebra.smul_def, Algebra.TensorProduct.tmul_mul_tmul]
            rfl
          rw [h1]
          exact Submodule.smul_mem _ _ (Submodule.subset_span (by simp; exact ⟨y, hy, rfl⟩))
        | zero =>
          have h0 : (fun i ↦ b ⊗ₜ[F] (0 : Fin n → E) i) = 0 := by
            funext i
            simp
          rw [h0]
          exact zero_mem _
        | add y y' _ _ ihy ihy' =>
          have h1 : (fun i ↦ b ⊗ₜ[F] (y + y') i) = (fun i ↦ b ⊗ₜ[F] y i) + fun i ↦ b ⊗ₜ[F] y' i := by
            funext i
            simp [TensorProduct.tmul_add]
          rw [h1]
          exact add_mem ihy ihy'
        | smul m y _ ihy =>
          have h1 : (fun i ↦ b ⊗ₜ[F] (m • y) i) = m • fun i ↦ b ⊗ₜ[F] y i := by
            funext i
            exact map_zsmul (TensorProduct.mk F (FiniteAdeleRing (𝓞 F) F) E b) m (y i)
          rw [h1]
          exact zsmul_mem ihy m
      | zero => exact zero_mem _
      | add x y _ _ hx hy => exact add_mem hx hy
      | neg x _ hx => exact neg_mem hx

  have hNe : ∀ v, (N • e) v ∈ v.adicCompletionIntegers F := by
    intro v
    show N • e v ∈ _
    exact nsmul_mem (he v) N
  set a' : A := ⟨N • e, hNe⟩ with ha'
  have hjac : a' ∈ Ideal.jacobson (⊥ : Ideal A) := by
    apply _root_.GlobalTheory.UnRep.Nakayama.mem_jacobson
    intro v
    show Valued.v (N • e v) < 1
    rw [nsmul_eq_mul, map_mul]
    by_cases hv : (N : 𝓞 F) ∈ v.asIdeal
    · have h1 := _root_.GlobalTheory.UnRep.Nakayama.valuation_natCast_lt_one F N v hv
      have h2 : Valued.v (e v) ≤ 1 := (HeightOneSpectrum.mem_adicCompletionIntegers _ _ _).mp (he v)
      calc Valued.v ((N : ℕ) : v.adicCompletion F) * Valued.v (e v)
          ≤ Valued.v ((N : ℕ) : v.adicCompletion F) * 1 := by gcongr
        _ < 1 := by rw [mul_one]; exact h1
    · rw [hsupp v hv, map_zero, mul_zero]
      exact zero_lt_one
  have hI : Ideal.span {a'} ≤ Ideal.jacobson (⊥ : Ideal A) :=
    (Ideal.span_singleton_le_iff_mem _).mpr hjac

  let f : (Fin n → _root_.GlobalTheory.AdLat.RA F E) →ₗ[A] (Fin n → _root_.GlobalTheory.AdLat.RA F E) :=
    (Matrix.mulVecLin (1 + M)).restrictScalars A
  have hf : ∀ z, f z = z + M *ᵥ z := by
    intro z
    show (1 + M) *ᵥ z = _
    rw [Matrix.add_mulVec, Matrix.one_mulVec]
  have hMz : ∀ z, M *ᵥ z = a' • (X *ᵥ z) := by
    intro z
    rw [hM, Matrix.smul_mulVec, Matrix.smul_mulVec]
    funext i
    show (e ⊗ₜ[F] (1 : E)) * (N • (X *ᵥ z) i) = (N • e) • (X *ᵥ z) i
    calc (e ⊗ₜ[F] (1 : E)) * (N • (X *ᵥ z) i) = (N • (e ⊗ₜ[F] (1 : E))) * (X *ᵥ z) i := by
          rw [mul_smul_comm, smul_mul_assoc]
      _ = ((N • e) ⊗ₜ[F] (1 : E)) * (X *ᵥ z) i := by rw [TensorProduct.smul_tmul']
      _ = ((N • e) • (1 : _root_.GlobalTheory.AdLat.RA F E)) * (X *ᵥ z) i := by
          rw [Algebra.TensorProduct.one_def, TensorProduct.smul_tmul', smul_eq_mul, mul_one]
      _ = (N • e) • (X *ᵥ z) i := smul_one_mul _ _
  have hle : ΛA ≤ ΛA.map f ⊔ Ideal.span {a'} • ΛA := by
    intro z hz
    rw [Submodule.mem_sup]
    refine ⟨f z, ⟨z, hz, rfl⟩, -(M *ᵥ z), ?_, ?_⟩
    · rw [hMz]
      exact neg_mem (Submodule.smul_mem_smul (Ideal.mem_span_singleton_self a') (hX z hz))
    · rw [hf]
      abel
  have hsurj : ∀ z ∈ Λ, ∃ y ∈ Λ, (1 + M) *ᵥ y = z := by
    intro z hz
    obtain ⟨y, hy, hyz⟩ := Submodule.le_of_le_smul_of_le_jacobson_bot hfg hI hle hz
    exact ⟨y, hy, hyz⟩

  let R := LinearMap.range (Matrix.mulVecLin (1 + M))
  have hR : ∀ z ∈ Λ, z ∈ R := by
    intro z hz
    obtain ⟨y, -, hy⟩ := hsurj z hz
    exact ⟨y, hy⟩
  let V : Submodule E (Fin n → E) :=
    { carrier := {x | (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) ∈ R}
      add_mem' := by
        intro x y hx hy
        have h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (x + y) i) =
            (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i) + fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] y i := by
          funext i
          simp [TensorProduct.tmul_add]
        show _ ∈ R
        rw [h1]
        exact add_mem hx hy
      zero_mem' := by
        have h0 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (0 : Fin n → E) i) = 0 := by
          funext i
          simp
        show _ ∈ R
        rw [h0]
        exact zero_mem _
      smul_mem' := by
        intro c x hx
        have h1 : (fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (c • x) i) =
            ((1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] c : _root_.GlobalTheory.AdLat.RA F E) •
              fun i ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] x i := by
          funext i
          simp [Algebra.TensorProduct.tmul_mul_tmul]
        show _ ∈ R
        rw [h1]
        exact R.smul_mem _ hx }
  have hLV : Submodule.span E (L : Set (Fin n → E)) ≤ V := by
    rw [Submodule.span_le]
    intro x hx
    exact hR _ (one_tmul_mem_hat hx)
  have hsingle : ∀ i, (Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E) : Fin n → _) ∈ R := by
    intro i
    have hi : (Pi.single i (1 : E) : Fin n → E) ∈ V := by
      apply hLV
      rw [hspan]
      exact Submodule.mem_top
    have h1 : (fun j ↦ (1 : FiniteAdeleRing (𝓞 F) F) ⊗ₜ[F] (Pi.single i (1 : E) : Fin n → E) j) =
        Pi.single i (1 : _root_.GlobalTheory.AdLat.RA F E) := by
      funext j
      by_cases hj : j = i
      · subst hj
        simp [Algebra.TensorProduct.one_def]
      · simp [Pi.single_apply, hj]
    rw [← h1]
    exact hi
  choose w hw using hsingle
  have hW : (1 + M) * Matrix.of (fun r i ↦ w i r) = 1 := by
    ext r i
    have h := congrFun (hw i) r
    simp only [Matrix.mulVecLin_apply] at h
    rw [Matrix.mul_apply, Matrix.one_apply]
    rw [Matrix.mulVec, dotProduct] at h
    simp only [Matrix.of_apply]
    rw [h, Pi.single_apply]
  refine ⟨Matrix.of fun r i ↦ w i r, hW, ?_⟩
  intro z hz
  obtain ⟨y, hy, rfl⟩ := hsurj z hz
  have hW' : Matrix.of (fun r i ↦ w i r) * (1 + M) = 1 := mul_eq_one_comm.mp hW
  rw [Matrix.mulVec_mulVec, hW', Matrix.one_mulVec]
  exact hy
