import Mathlib
import Development.AbelianVarietyTheory.Definitions.Foundations.T2SpaceAdeleRing
import Formalism.SatakeDualWeyl.AdelicIwasawaHecke.CsGlob

open scoped TensorProduct NNReal ENNReal Matrix
open NumberField IsDedekindDomain MeasureTheory Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes GlobalTheory.AdelicU GlobalTheory.Doubling

namespace GlobalTheory.LatticeOnePlaceApprox

/- English proof (translation)
Set `t : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F` to `Pi.single v a`. Establish `ht : ∀ u, t u ∈ u.adicCompletionIntegers F` using `fun u => by`. Distinguish the cases in `e : u = v`. Substitute `e` using the available equality. Simplify `ha` using `[t]`.

Simplify using `[t, e]`. Set `A : FiniteAdeleRing (𝓞 F) F` to `⟨t, Filter.Eventually.of_forall ht⟩`. Take `⟨ρ, w, hw, e⟩` from `Formalism.UG.P.csGlob_intAdApprox F (M : 𝓞 F) (by exact_mod_cast hM) A ht`. Rewrite `e` using `[map_natCast, ← nsmul_eq_mul]`. Establish `h : ∀ u, t u = algebraMap F (u.adicCompletion F) (ρ : F) + M • w u` using `fun u => by`.

Establish `h : A u = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + M • w) u` using `by rw [← e]`. Conclude with `h`. Use `⟨ρ, ⟨-w v, neg_mem (hw v), ?_⟩, fun u hu => ⟨-w u, neg_mem (hw u), ?_⟩⟩` and prove the remaining obligations. Establish `h1 : a = _` using `(Pi.single_eq_same v a).symm.trans (h v)`. Rewrite using `[h1, smul_neg, add_neg_cancel_right]`.

Establish `h1 : (0 : u.adicCompletion F) = _` using `(Pi.single_eq_of_ne hu a).symm.trans (h u)`. Rewrite using `[smul_neg]`. Conclude with `eq_neg_of_add_eq_zero_left h1.symm`.
-/
theorem exists_int (F : Type) [Field F] [NumberField F] (M : ℕ) (hM : M ≠ 0) (v : HeightOneSpectrum (𝓞 F))
    (a : v.adicCompletion F) (ha : a ∈ v.adicCompletionIntegers F) :
    ∃ ρ : 𝓞 F, (∃ w ∈ v.adicCompletionIntegers F, algebraMap F (v.adicCompletion F) (ρ : F) = a + M • w) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → ∃ w ∈ u.adicCompletionIntegers F,
        algebraMap F (u.adicCompletion F) (ρ : F) = M • w := by
  classical
  let t : ∀ u : HeightOneSpectrum (𝓞 F), u.adicCompletion F := Pi.single v a
  have ht : ∀ u, t u ∈ u.adicCompletionIntegers F := fun u => by
    by_cases e : u = v
    · subst e; simpa [t] using ha
    · simp [t, e]
  let A : FiniteAdeleRing (𝓞 F) F := ⟨t, Filter.Eventually.of_forall ht⟩
  obtain ⟨ρ, w, hw, e⟩ := Formalism.UG.P.csGlob_intAdApprox F (M : 𝓞 F) (by exact_mod_cast hM) A ht
  rw [map_natCast, ← nsmul_eq_mul] at e
  have h : ∀ u, t u = algebraMap F (u.adicCompletion F) (ρ : F) + M • w u := fun u => by
    have h : A u = (algebraMap (𝓞 F) (FiniteAdeleRing (𝓞 F) F) ρ + M • w) u := by rw [← e]
    exact h
  refine ⟨ρ, ⟨-w v, neg_mem (hw v), ?_⟩, fun u hu => ⟨-w u, neg_mem (hw u), ?_⟩⟩
  · have h1 : a = _ := (Pi.single_eq_same v a).symm.trans (h v)
    rw [h1, smul_neg, add_neg_cancel_right]
  · have h1 : (0 : u.adicCompletion F) = _ := (Pi.single_eq_of_ne hu a).symm.trans (h u)
    rw [smul_neg]
    exact eq_neg_of_add_eq_zero_left h1.symm

/- English proof (translation)
Introduce `F E _ _ _ _ _ n L M hM v y hy`. Establish `hadd : ∀ (u : HeightOneSpectrum (𝓞 F)) (x x' : Fin n → E), (fun i => (1 : Fv F u) ⊗ₜ[F] (x + x') i) = (fun i => (1 : Fv F u) ⊗ₜ[F] x i) + fun i => (1 : Fv F u) ⊗ₜ[F] x' i` using `fun u x x' =>`. Use function extensionality and compare the values at `fun i => TensorProduct.tmul_add _ _ _`. Establish `hneg : ∀ (u : HeightOneSpectrum (𝓞 F)) (x : Fin n → E), (fun i => (1 : Fv F u) ⊗ₜ[F] (-x) i) = -fun i => (1 : Fv F u) ⊗ₜ[F] x i` using `fun u x =>`. Use function extensionality and compare the values at `fun i => TensorProduct.tmul_neg _ _`.

Establish `hsm : ∀ (u : HeightOneSpectrum (𝓞 F)) (ρ : 𝓞 F) (x : Fin n → E) (i : Fin n), (1 : Fv F u) ⊗ₜ[F] (algebraMap (𝓞 F) (𝓞 E) ρ • x) i = algebraMap F (Fv F u) (ρ : F) ⊗ₜ[F] x i` using `fun u ρ x i => by`. Establish `h1 : (algebraMap (𝓞 F) (𝓞 E) ρ • x) i = (ρ : F) • x i`. Rewrite using `[Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]`. Both sides reduce to the same expression. Rewrite using `[h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]`.

Establish `hn : ∀ (u : HeightOneSpectrum (𝓞 F)) (w : Fv F u) (e : E), (M • w) ⊗ₜ[F] e = M • (w ⊗ₜ[F] e)` using `fun u w e => map_nsmul ((TensorProduct.mk F (Fv F u) E).flip e) M w`. Use `latLoc_induction (p := fun y => ∃ x ∈ L, (∃ z ∈ latLoc F L v, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) = y + M • z) ∧ ∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → ∃ z ∈ latLoc F L u, (fun i => (1 : Fv F u) ⊗ₜ[F] x i) = M • z) (fun a ha x hx => ?_) ?_ ?_ ?_ hy` and prove the remaining obligations. Take `⟨ρ, ⟨w, hw, e⟩, h⟩` from `exists_int F M hM.ne' v a ha`. Use `⟨algebraMap (𝓞 F) (𝓞 E) ρ • x, L.smul_mem _ hx, ⟨_, tmul_mem_latLoc hw hx, funext fun i => ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, e, TensorProduct.add_tmul, hn]`.

Both sides reduce to the same expression. Take `⟨w, hw, e⟩` from `h u hu`. Use `⟨_, tmul_mem_latLoc hw hx, funext fun i => ?_⟩` and prove the remaining obligations. Rewrite using `[hsm, e, hn]`. Both sides reduce to the same expression.

Conclude with `⟨0, zero_mem _, ⟨0, zero_mem _, funext fun i => by simp⟩, fun u _ => ⟨0, zero_mem _, funext fun i => by simp⟩⟩`. Introduce and unpack `y y' ⟨x, hx, ⟨z, hz, e⟩, h⟩ ⟨x', hx', ⟨z', hz', e'⟩, h'⟩`. Use `⟨x + x', add_mem hx hx', ⟨z + z', add_mem hz hz', ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations. Rewrite using `[hadd, e, e', smul_add]`. Normalize the expressions using the abelian group laws.

Take `⟨s, hs, f⟩` from `h u hu`. Take `⟨s', hs', f'⟩` from `h' u hu`. Conclude with `⟨s + s', add_mem hs hs', by rw [hadd, f, f', smul_add]⟩`. Introduce and unpack `y ⟨x, hx, ⟨z, hz, e⟩, h⟩`. Use `⟨-x, neg_mem hx, ⟨-z, neg_mem hz, ?_⟩, fun u hu => ?_⟩` and prove the remaining obligations.

Rewrite using `[hneg, e, smul_neg]`. Normalize the expressions using the abelian group laws. Take `⟨s, hs, f⟩` from `h u hu`. Conclude with `⟨-s, neg_mem hs, by rw [hneg, f, smul_neg]⟩`.
-/
theorem exists_approx : ∀ (F E : Type) [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E] (n : ℕ) (L : Submodule (𝓞 E) (Fin n → E)) (M : ℕ), 0 < M → ∀ (v : HeightOneSpectrum (𝓞 F)), ∀ y ∈ latLoc F L v,
    ∃ x ∈ L, (∃ z ∈ latLoc F L v, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) = y + M • z) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → ∃ z ∈ latLoc F L u, (fun i => (1 : Fv F u) ⊗ₜ[F] x i) = M • z := by
  intro F E _ _ _ _ _ n L M hM v y hy
  have hadd : ∀ (u : HeightOneSpectrum (𝓞 F)) (x x' : Fin n → E), (fun i => (1 : Fv F u) ⊗ₜ[F] (x + x') i) =
      (fun i => (1 : Fv F u) ⊗ₜ[F] x i) + fun i => (1 : Fv F u) ⊗ₜ[F] x' i := fun u x x' =>
    funext fun i => TensorProduct.tmul_add _ _ _
  have hneg : ∀ (u : HeightOneSpectrum (𝓞 F)) (x : Fin n → E), (fun i => (1 : Fv F u) ⊗ₜ[F] (-x) i) =
      -fun i => (1 : Fv F u) ⊗ₜ[F] x i := fun u x =>
    funext fun i => TensorProduct.tmul_neg _ _
  have hsm : ∀ (u : HeightOneSpectrum (𝓞 F)) (ρ : 𝓞 F) (x : Fin n → E) (i : Fin n),
      (1 : Fv F u) ⊗ₜ[F] (algebraMap (𝓞 F) (𝓞 E) ρ • x) i = algebraMap F (Fv F u) (ρ : F) ⊗ₜ[F] x i := fun u ρ x i => by
    have h1 : (algebraMap (𝓞 F) (𝓞 E) ρ • x) i = (ρ : F) • x i := by
      rw [Pi.smul_apply, Algebra.smul_def, Algebra.smul_def]; rfl
    rw [h1, Algebra.algebraMap_eq_smul_one, TensorProduct.smul_tmul]
  have hn : ∀ (u : HeightOneSpectrum (𝓞 F)) (w : Fv F u) (e : E), (M • w) ⊗ₜ[F] e = M • (w ⊗ₜ[F] e) := fun u w e =>
    map_nsmul ((TensorProduct.mk F (Fv F u) E).flip e) M w
  refine latLoc_induction (p := fun y => ∃ x ∈ L,
    (∃ z ∈ latLoc F L v, (fun i => (1 : Fv F v) ⊗ₜ[F] x i) = y + M • z) ∧
      ∀ u : HeightOneSpectrum (𝓞 F), u ≠ v → ∃ z ∈ latLoc F L u, (fun i => (1 : Fv F u) ⊗ₜ[F] x i) = M • z)
    (fun a ha x hx => ?_) ?_ ?_ ?_ hy
  · obtain ⟨ρ, ⟨w, hw, e⟩, h⟩ := exists_int F M hM.ne' v a ha
    refine ⟨algebraMap (𝓞 F) (𝓞 E) ρ • x, L.smul_mem _ hx, ⟨_, tmul_mem_latLoc hw hx, funext fun i => ?_⟩,
      fun u hu => ?_⟩
    · rw [hsm, e, TensorProduct.add_tmul, hn]; rfl
    · obtain ⟨w, hw, e⟩ := h u hu
      refine ⟨_, tmul_mem_latLoc hw hx, funext fun i => ?_⟩
      rw [hsm, e, hn]; rfl
  · exact ⟨0, zero_mem _, ⟨0, zero_mem _, funext fun i => by simp⟩, fun u _ => ⟨0, zero_mem _, funext fun i => by simp⟩⟩
  · rintro y y' ⟨x, hx, ⟨z, hz, e⟩, h⟩ ⟨x', hx', ⟨z', hz', e'⟩, h'⟩
    refine ⟨x + x', add_mem hx hx', ⟨z + z', add_mem hz hz', ?_⟩, fun u hu => ?_⟩
    · rw [hadd, e, e', smul_add]; abel
    · obtain ⟨s, hs, f⟩ := h u hu
      obtain ⟨s', hs', f'⟩ := h' u hu
      exact ⟨s + s', add_mem hs hs', by rw [hadd, f, f', smul_add]⟩
  · rintro y ⟨x, hx, ⟨z, hz, e⟩, h⟩
    refine ⟨-x, neg_mem hx, ⟨-z, neg_mem hz, ?_⟩, fun u hu => ?_⟩
    · rw [hneg, e, smul_neg]; abel
    · obtain ⟨s, hs, f⟩ := h u hu
      exact ⟨-s, neg_mem hs, by rw [hneg, f, smul_neg]⟩

end GlobalTheory.LatticeOnePlaceApprox
