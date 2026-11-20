import Mathlib
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FlatOfEssentiallyEtaleLocalAlgebrasStatement
open IsLocalRing

namespace GlobalTheory

set_option synthInstance.maxHeartbeats 400000 in
/- English proof (translation)
Introduce `R B _ _ _ Q _ ι _ _ C hmono hcov hess i c hc t ht htc`. Take `⟨j, hj⟩` from `hcov t`. Take `⟨k, hik, hjk⟩` from `directed_of (· ≤ ·) i j`. Establish `hck : c ∈ C k` using `hmono hik hc`. Establish `htk : t ∈ C k` using `hmono hjk hj`.

Use `set Qi := Q.comap ((C i).val : C i →ₐ[R] B) with hQi`. Use `set Qk := Q.comap ((C k).val : C k →ₐ[R] B) with hQk`. Set `f : C i →+* C k` to `(Subalgebra.inclusion (hmono hik)).toRingHom`. Establish `hf : Qi = Qk.comap f` using `by ext x; rfl`. Set `g : Localization.AtPrime Qi →+* Localization.AtPrime Qk` to `Localization.localRingHom Qi Qk f hf`.

Use `letI : Algebra (Localization.AtPrime Qi) (Localization.AtPrime Qk) := g.toAlgebra`. Use `haveI : IsScalarTower R (Localization.AtPrime Qi) (Localization.AtPrime Qk) := by`. Use `IsScalarTower.of_algebraMap_eq (fun r => ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `algebraMap R (Localization.AtPrime Qk) r = g (algebraMap R (Localization.AtPrime Qi) r)`. Rewrite using `[IsScalarTower.algebraMap_apply R (C i) (Localization.AtPrime Qi), IsScalarTower.algebraMap_apply R (C k) (Localization.AtPrime Qk)]`.

Simplify using `only [g, Localization.localRingHom_to_map]`. Use `congr 1`. Use `haveI : Module.Flat (Localization.AtPrime Qi) (Localization.AtPrime Qk) := GlobalTheory.T.flat_of_essentiallyEtale_local_algebras R _ _ (hess i) (hess k)`. Use `haveI : IsLocalHom (algebraMap (Localization.AtPrime Qi) (Localization.AtPrime Qk)) := (inferInstance : IsLocalHom g)`. Use `haveI : Module.FaithfullyFlat (Localization.AtPrime Qi) (Localization.AtPrime Qk) := Module.FaithfullyFlat.of_flat_of_isLocalHom`.

Establish `hinj` using `RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr this)`. Establish `h0 : algebraMap (C k) (Localization.AtPrime Qk) ⟨c, hck⟩ = 0`. Rewrite using `[IsLocalization.map_eq_zero_iff Qk.primeCompl]`. Use `⟨⟨⟨t, htk⟩, ht⟩, ?_⟩` and prove the remaining obligations. Conclude with `Subtype.ext htc`.

Establish `h1 : algebraMap (C i) (Localization.AtPrime Qi) ⟨c, hc⟩ = 0`. Apply `hinj` to reduce the goal to its premises. Rewrite using `[map_zero]`. Express the relevant statement in the definitionally equal form `g _ = 0`. Simplify using `only [g, Localization.localRingHom_to_map]`.

Conclude with `h0`. Rewrite `h1` using `[IsLocalization.map_eq_zero_iff Qi.primeCompl]`. Take `⟨⟨⟨s, hs⟩, hsQ⟩, hsc⟩` from `h1`. Conclude with `⟨s, hs, hsQ, congrArg Subtype.val hsc⟩`.
-/
theorem ann_of_directed_essEtale : ∀ (R B : Type) [CommRing R] [CommRing B] [Algebra R B] (Q : Ideal B) [Q.IsPrime] (ι : Type) [Preorder ι] [IsDirected ι (· ≤ ·)] (C : ι → Subalgebra R B), Monotone C → (∀ b : B, ∃ i, b ∈ C i) → (∀ i, (∃ (A : Type) (_ : CommRing A) (_ : Algebra R A) (_ : Algebra.Etale R A) (q : Ideal A) (_ : q.IsPrime), Nonempty (Localization.AtPrime q ≃ₐ[R] Localization.AtPrime (Q.comap ((C i).val : C i →ₐ[R] B))))) → ∀ i, ∀ c ∈ C i, ∀ t : B, t ∉ Q → t * c = 0 → ∃ s ∈ C i, s ∉ Q ∧ s * c = 0 := by
  intro R B _ _ _ Q _ ι _ _ C hmono hcov hess i c hc t ht htc
  obtain ⟨j, hj⟩ := hcov t
  obtain ⟨k, hik, hjk⟩ := directed_of (· ≤ ·) i j
  have hck : c ∈ C k := hmono hik hc
  have htk : t ∈ C k := hmono hjk hj
  set Qi := Q.comap ((C i).val : C i →ₐ[R] B) with hQi
  set Qk := Q.comap ((C k).val : C k →ₐ[R] B) with hQk
  let f : C i →+* C k := (Subalgebra.inclusion (hmono hik)).toRingHom
  have hf : Qi = Qk.comap f := by ext x; rfl
  let g : Localization.AtPrime Qi →+* Localization.AtPrime Qk := Localization.localRingHom Qi Qk f hf
  letI : Algebra (Localization.AtPrime Qi) (Localization.AtPrime Qk) := g.toAlgebra
  haveI : IsScalarTower R (Localization.AtPrime Qi) (Localization.AtPrime Qk) := by
    refine IsScalarTower.of_algebraMap_eq (fun r => ?_)
    change algebraMap R (Localization.AtPrime Qk) r = g (algebraMap R (Localization.AtPrime Qi) r)
    rw [IsScalarTower.algebraMap_apply R (C i) (Localization.AtPrime Qi), IsScalarTower.algebraMap_apply R (C k) (Localization.AtPrime Qk)]
    simp only [g, Localization.localRingHom_to_map]
    congr 1
  haveI : Module.Flat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    GlobalTheory.T.flat_of_essentiallyEtale_local_algebras R _ _ (hess i) (hess k)
  haveI : IsLocalHom (algebraMap (Localization.AtPrime Qi) (Localization.AtPrime Qk)) :=
    (inferInstance : IsLocalHom g)
  haveI : Module.FaithfullyFlat (Localization.AtPrime Qi) (Localization.AtPrime Qk) :=
    Module.FaithfullyFlat.of_flat_of_isLocalHom
  have hinj := RingHom.FaithfullyFlat.injective (RingHom.faithfullyFlat_algebraMap_iff.mpr this)
  have h0 : algebraMap (C k) (Localization.AtPrime Qk) ⟨c, hck⟩ = 0 := by
    rw [IsLocalization.map_eq_zero_iff Qk.primeCompl]
    refine ⟨⟨⟨t, htk⟩, ht⟩, ?_⟩
    exact Subtype.ext htc
  have h1 : algebraMap (C i) (Localization.AtPrime Qi) ⟨c, hc⟩ = 0 := by
    apply hinj
    rw [map_zero]
    change g _ = 0
    simp only [g, Localization.localRingHom_to_map]
    exact h0
  rw [IsLocalization.map_eq_zero_iff Qi.primeCompl] at h1
  obtain ⟨⟨⟨s, hs⟩, hsQ⟩, hsc⟩ := h1
  exact ⟨s, hs, hsQ, congrArg Subtype.val hsc⟩

end GlobalTheory
