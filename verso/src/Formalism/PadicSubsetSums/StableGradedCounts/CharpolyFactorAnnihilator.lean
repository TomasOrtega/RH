import Formalism.PadicSubsetSums.CentralIdempotents.PrimitiveRootFifteenSubOneUnit

open Polynomial

namespace Formalism.IrreducibleCountingLemmas.Z

/- English proof (translation)
Introduce `K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar`. Set `gA : Module.End K A` to `γ₀.restrict hA₀`. Set `gB : Module.End K B` to `c • LinearMap.id`. Set `e : (A × B) ≃ₗ[K] V` to `Submodule.prodEquivOfIsCompl A B hAB`. Establish `hconj : e.conj (gA.prodMap gB) = γ₀`.

Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Take `⟨⟨a, b⟩, rfl⟩` from `e.surjective v`. Rewrite using `[LinearEquiv.conj_apply]`. Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]`.

Simplify using `[e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]`. Establish `hcB : gB.charpoly = (X - C c) ^ t`. Rewrite using `[← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]`. Establish `hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB = Matrix.diagonal (fun _ => c)`. Simplify using `only [gB, map_smul, LinearMap.toMatrix_id]`.

Use extensionality with `i j`. Apply the tactic sequence `by_cases h : i = j <;> simp [h, Matrix.one_apply]`. Rewrite using `[hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]`. Establish `hPA : P = gA.charpoly`. Establish `h1 : γ₀.charpoly = gA.charpoly * gB.charpoly`.

Rewrite using `[← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]`. Rewrite `h1` using `[hchar, hcB]`. Conclude with `mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1`. Establish `hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V)`. Introduce `p`.

Proceed by induction on `p using Polynomial.induction_on with`. Consider the case `C r => intro a`. Simplify using `[Module.algebraMap_end_apply]`. Consider the case `add p q hp hq => intro a`. Simplify using `[hp, hq]`.

Consider the case `monomial n r ih`. Introduce `a`. Rewrite using `[pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X, Module.End.mul_apply, Module.End.mul_apply]`. Rewrite using `[show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]`. Establish `h0 : aeval gA P = 0`.

Rewrite using `[hPA]`. Conclude with `LinearMap.aeval_self_charpoly gA`. Establish `hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0`. Introduce `w hw`. Establish `h2` using `hrestr P ⟨w, hw⟩`.

Rewrite `h2` using `[h0]`. Simplify using `using h2`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `v`. Establish `hv : v ∈ A ⊔ B` using `by rw [hAB.sup_eq_top]; trivial`.

Take `⟨a, ha, b, hb, rfl⟩` from `Submodule.mem_sup.mp hv`. Rewrite using `[Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply, Module.algebraMap_end_apply]`. Establish `h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a`. Rewrite using `[map_add, hB b hb, smul_add]`. Normalize the expressions using the abelian group laws.

Rewrite using `[h3]`. Conclude with `hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))`.
-/
theorem charpolyFactorAnnihilator : CharpolyFactorAnnihilator := by
  intro K V _ _ _ _ A B γ₀ γ c cγ t P hAB hA₀ hA hB₀ hB ht hchar
  classical
  let gA : Module.End K A := γ₀.restrict hA₀
  let gB : Module.End K B := c • LinearMap.id
  let e : (A × B) ≃ₗ[K] V := Submodule.prodEquivOfIsCompl A B hAB

  have hconj : e.conj (gA.prodMap gB) = γ₀ := by
    apply LinearMap.ext
    intro v
    obtain ⟨⟨a, b⟩, rfl⟩ := e.surjective v
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_apply_apply]
    simp [e, gA, gB, Submodule.coe_prodEquivOfIsCompl', hB₀ b b.2]

  have hcB : gB.charpoly = (X - C c) ^ t := by
    rw [← LinearMap.charpoly_toMatrix gB (Module.finBasis K B)]
    have hm : LinearMap.toMatrix (Module.finBasis K B) (Module.finBasis K B) gB =
        Matrix.diagonal (fun _ => c) := by
      simp only [gB, map_smul, LinearMap.toMatrix_id]
      ext i j
      by_cases h : i = j <;> simp [h, Matrix.one_apply]
    rw [hm, Matrix.charpoly_diagonal, Finset.prod_const, Finset.card_univ, Fintype.card_fin, ht]
  have hPA : P = gA.charpoly := by
    have h1 : γ₀.charpoly = gA.charpoly * gB.charpoly := by
      rw [← hconj, LinearEquiv.charpoly_conj, LinearMap.charpoly_prodMap]
    rw [hchar, hcB] at h1
    exact mul_right_cancel₀ (pow_ne_zero _ (X_sub_C_ne_zero c)) h1

  have hrestr : ∀ (p : K[X]) (a : A), (aeval γ₀ p) (a : V) = ((aeval gA p) a : V) := by
    intro p
    induction p using Polynomial.induction_on with
    | C r => intro a; simp [Module.algebraMap_end_apply]
    | add p q hp hq => intro a; simp [hp, hq]
    | monomial n r ih =>
      intro a
      rw [pow_succ, ← mul_assoc, map_mul (aeval γ₀), map_mul (aeval gA), aeval_X, aeval_X,
        Module.End.mul_apply, Module.End.mul_apply]
      rw [show γ₀ (a : V) = ((gA a : A) : V) from rfl, ih]
  have h0 : aeval gA P = 0 := by
    rw [hPA]
    exact LinearMap.aeval_self_charpoly gA
  have hkill : ∀ w ∈ A, (aeval γ₀ P) w = 0 := by
    intro w hw
    have h2 := hrestr P ⟨w, hw⟩
    rw [h0] at h2
    simpa using h2
  apply LinearMap.ext
  intro v
  have hv : v ∈ A ⊔ B := by rw [hAB.sup_eq_top]; trivial
  obtain ⟨a, ha, b, hb, rfl⟩ := Submodule.mem_sup.mp hv
  rw [Module.End.mul_apply, LinearMap.zero_apply, LinearMap.sub_apply,
    Module.algebraMap_end_apply]
  have h3 : γ (a + b) - cγ • (a + b) = γ a - cγ • a := by
    rw [map_add, hB b hb, smul_add]
    abel
  rw [h3]
  exact hkill _ (A.sub_mem (hA a ha) (A.smul_mem cγ ha))

end Formalism.IrreducibleCountingLemmas.Z
