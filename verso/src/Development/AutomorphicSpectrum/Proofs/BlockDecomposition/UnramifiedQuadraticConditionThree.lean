import Mathlib
import Development.WeilBound.CoreStatements.AutomorphicKernels.SiegelWeilFormula.UnramifiedWhittaker.QuadAtOf

noncomputable section

namespace GlobalTheory.CompanionTheory.GunrResCard

open HeckeCharacterZeroLocus.SiegelWeilU NumberField IsDedekindDomain PositivityTheory.PfSWUS.Loc PositivityTheory.SiegelWeilFormula.Gunr
open scoped TensorProduct

variable {F E : Type} [Field F] [NumberField F] [Field E] [NumberField E] [Algebra F E]

def redCoord {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (x : S) (k : Fin d) :
    v.adicCompletionIntegers F ⧸ Ideal.span {ϖ} :=
  Ideal.Quotient.mk _ ⟨(Algebra.TensorProduct.basis (Fv F v) bs).repr x k,
    (show (x : Fv F v ⊗[F] E) ∈ Rv bs v from hS ▸ x.2) k⟩

/- English proof (translation)
Use `set B := Algebra.TensorProduct.basis (Fv F v) bs with hB`. Establish `hsm : ∀ z : Fv F v ⊗[F] E, z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (ϖ : Fv F v) • z`. Introduce `z`. Rewrite using `[Algebra.smul_def, mul_comm]`. Rewrite using `[show lev (⟨_, hϖ⟩ : S) 1 = Ideal.span {(⟨_, hϖ⟩ : S) ^ 1} from rfl, pow_one, Ideal.mem_span_singleton']`.

Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `hk : ∀ k, ∃ t : v.adicCompletionIntegers F, (t : Fv F v) * ϖ = B.repr x k - B.repr y k`. Introduce `k`. Establish `h1` using `congrFun h k`.

Simplify using `only [redCoord] at h1`. Rewrite `h1` using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Take `⟨t, ht⟩` from `h1`. Use `⟨t, ?_⟩` and prove the remaining obligations. Establish `h2` using `congrArg Subtype.val ht`.

Move the coercions through the operations in `at h2`. Conclude with `h2`. Use `choose t ht using hk`. Set `z : Fv F v ⊗[F] E` to `B.equivFun.symm (fun k => (t k : Fv F v))`. Establish `hz : ∀ k, B.repr z k = t k`.

Introduce `k`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hzS : z ∈ S`. Establish `hzR : z ∈ Rv bs v`. Introduce `k`.

Rewrite using `[hz k]`. Conclude with `(t k).2`. Rewrite `hzR` using `[← hS]`. Conclude with `hzR`. Use `⟨⟨z, hzS⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `show z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (x : Fv F v ⊗[F] E) - y`. Rewrite using `[hsm, B.ext_elem_iff]`. Introduce `k`. Rewrite using `[map_smul, Finsupp.smul_apply, smul_eq_mul, hz k, map_sub, Finsupp.sub_apply, mul_comm]`.

Conclude with `ht k`. Introduce and unpack `⟨a, ha⟩`. Establish `hxy : (x : Fv F v ⊗[F] E) - y = (ϖ : Fv F v) • (a : Fv F v ⊗[F] E)`. Rewrite using `[← hsm]`. Conclude with `(congrArg Subtype.val ha).symm`.

Establish `haR : (a : Fv F v ⊗[F] E) ∈ Rv bs v` using `hS ▸ a.2`. Use function extensionality and compare the values at `k`. Simplify using `only [redCoord]`. Rewrite using `[Ideal.Quotient.eq, Ideal.mem_span_singleton']`. Use `⟨⟨B.repr a k, haR k⟩, ?_⟩` and prove the remaining obligations.

Apply `Subtype.ext` to reduce the goal to its premises. Use `push_cast`. Establish `h3` using `congrArg (fun w => B.repr w k) hxy`. Simplify using `only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3`. Rewrite using `[mul_comm, ← h3]`.
-/
theorem redCoord_eq_iff {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) (x y : S) :
    redCoord bs v S hS ϖ x = redCoord bs v S hS ϖ y ↔ x - y ∈ lev (⟨_, hϖ⟩ : S) 1 := by
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  have hsm : ∀ z : Fv F v ⊗[F] E, z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (ϖ : Fv F v) • z := by
    intro z
    rw [Algebra.smul_def, mul_comm]
  rw [show lev (⟨_, hϖ⟩ : S) 1 = Ideal.span {(⟨_, hϖ⟩ : S) ^ 1} from rfl, pow_one,
    Ideal.mem_span_singleton']
  constructor
  · intro h
    have hk : ∀ k, ∃ t : v.adicCompletionIntegers F, (t : Fv F v) * ϖ = B.repr x k - B.repr y k := by
      intro k
      have h1 := congrFun h k
      simp only [redCoord] at h1
      rw [Ideal.Quotient.eq, Ideal.mem_span_singleton'] at h1
      obtain ⟨t, ht⟩ := h1
      refine ⟨t, ?_⟩
      have h2 := congrArg Subtype.val ht
      push_cast at h2
      exact h2
    choose t ht using hk
    let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
    have hz : ∀ k, B.repr z k = t k := by
      intro k
      rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
    have hzS : z ∈ S := by
      have hzR : z ∈ Rv bs v := by
        intro k
        rw [hz k]
        exact (t k).2
      rw [← hS] at hzR
      exact hzR
    refine ⟨⟨z, hzS⟩, ?_⟩
    apply Subtype.ext
    show z * algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ = (x : Fv F v ⊗[F] E) - y
    rw [hsm, B.ext_elem_iff]
    intro k
    rw [map_smul, Finsupp.smul_apply, smul_eq_mul, hz k, map_sub, Finsupp.sub_apply, mul_comm]
    exact ht k
  · rintro ⟨a, ha⟩
    have hxy : (x : Fv F v ⊗[F] E) - y = (ϖ : Fv F v) • (a : Fv F v ⊗[F] E) := by
      rw [← hsm]
      exact (congrArg Subtype.val ha).symm
    have haR : (a : Fv F v ⊗[F] E) ∈ Rv bs v := hS ▸ a.2
    funext k
    simp only [redCoord]
    rw [Ideal.Quotient.eq, Ideal.mem_span_singleton']
    refine ⟨⟨B.repr a k, haR k⟩, ?_⟩
    apply Subtype.ext
    push_cast
    have h3 := congrArg (fun w => B.repr w k) hxy
    simp only [map_sub, Finsupp.sub_apply, map_smul, Finsupp.smul_apply, smul_eq_mul] at h3
    rw [mul_comm, ← h3]

/- English proof (translation)
Introduce `g`. Use `set B := Algebra.TensorProduct.basis (Fv F v) bs with hB`. Use `choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)`. Set `z : Fv F v ⊗[F] E` to `B.equivFun.symm (fun k => (t k : Fv F v))`. Establish `hz : ∀ k, B.repr z k = t k`.

Introduce `k`. Rewrite using `[← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]`. Establish `hzS : z ∈ S`. Establish `hzR : z ∈ Rv bs v`. Introduce `k`.

Rewrite using `[hz k]`. Conclude with `(t k).2`. Rewrite `hzR` using `[← hS]`. Conclude with `hzR`. Use `⟨⟨z, hzS⟩, ?_⟩` and prove the remaining obligations.

Use function extensionality and compare the values at `k`. Simplify using `only [redCoord]`. Rewrite using `[← ht k]`. Use `congr 1`. Conclude with `Subtype.ext (hz k)`.
-/
theorem redCoord_surjective {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) : Function.Surjective (redCoord bs v S hS ϖ) := by
  intro g
  set B := Algebra.TensorProduct.basis (Fv F v) bs with hB
  choose t ht using fun k => Ideal.Quotient.mk_surjective (g k)
  let z : Fv F v ⊗[F] E := B.equivFun.symm (fun k => (t k : Fv F v))
  have hz : ∀ k, B.repr z k = t k := by
    intro k
    rw [← Module.Basis.equivFun_apply, LinearEquiv.apply_symm_apply]
  have hzS : z ∈ S := by
    have hzR : z ∈ Rv bs v := by
      intro k
      rw [hz k]
      exact (t k).2
    rw [← hS] at hzR
    exact hzR
  refine ⟨⟨z, hzS⟩, ?_⟩
  funext k
  simp only [redCoord]
  rw [← ht k]
  congr 1
  exact Subtype.ext (hz k)

/- English proof (translation)
Establish `hsurj` using `Ideal.Quotient.mk_surjective (I := lev (⟨_, hϖ⟩ : S) 1)`. Set `sec` to `Function.surjInv hsurj`. Establish `hsec : ∀ q, Ideal.Quotient.mk _ (sec q) = q` using `Function.surjInv_eq hsurj`. Set `g : S ⧸ lev (⟨_, hϖ⟩ : S) 1 → (Fin d → v.adicCompletionIntegers F ⧸ Ideal.span {ϖ})` to `fun q => redCoord bs v S hS ϖ (sec q)`. Establish `hg : Function.Bijective g`.

Prove the components needed by the constructor for the conclusion. Introduce `q₁ q₂ h`. Rewrite using `[← hsec q₁, ← hsec q₂, Ideal.Quotient.eq]`. Conclude with `(redCoord_eq_iff bs v S hS ϖ hϖ _ _).mp h`. Introduce `w`.

Take `⟨x, hx⟩` from `redCoord_surjective bs v S hS ϖ w`. Use `⟨Ideal.Quotient.mk _ x, ?_⟩` and prove the remaining obligations. Rewrite using `[← hx]`. Apply `(redCoord_eq_iff bs v S hS ϖ hϖ _ _).mpr` to reduce the goal to its premises. Rewrite using `[← Ideal.Quotient.eq, hsec]`.

Rewrite using `[Nat.card_congr (Equiv.ofBijective g hg), Nat.card_fun, Nat.card_fin]`.
-/
theorem card_quot {d : ℕ} (bs : Module.Basis (Fin d) F E) (v : HeightOneSpectrum (𝓞 F))
    (S : Subring (Fv F v ⊗[F] E)) (hS : (S : Set (Fv F v ⊗[F] E)) = Rv bs v)
    (ϖ : v.adicCompletionIntegers F) (hϖ : algebraMap (Fv F v) (Fv F v ⊗[F] E) ϖ ∈ S) :
    Nat.card (S ⧸ lev (⟨_, hϖ⟩ : S) 1) = Nat.card (v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) ^ d := by
  have hsurj := Ideal.Quotient.mk_surjective (I := lev (⟨_, hϖ⟩ : S) 1)
  let sec := Function.surjInv hsurj
  have hsec : ∀ q, Ideal.Quotient.mk _ (sec q) = q := Function.surjInv_eq hsurj
  let g : S ⧸ lev (⟨_, hϖ⟩ : S) 1 → (Fin d → v.adicCompletionIntegers F ⧸ Ideal.span {ϖ}) :=
    fun q => redCoord bs v S hS ϖ (sec q)
  have hg : Function.Bijective g := by
    constructor
    · intro q₁ q₂ h
      rw [← hsec q₁, ← hsec q₂, Ideal.Quotient.eq]
      exact (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mp h
    · intro w
      obtain ⟨x, hx⟩ := redCoord_surjective bs v S hS ϖ w
      refine ⟨Ideal.Quotient.mk _ x, ?_⟩
      rw [← hx]
      apply (redCoord_eq_iff bs v S hS ϖ hϖ _ _).mpr
      rw [← Ideal.Quotient.eq, hsec]
  rw [Nat.card_congr (Equiv.ofBijective g hg), Nat.card_fun, Nat.card_fin]

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ`. Take `⟨hCM, -, hS, -, -, -, -, hcard⟩` from `hQ`. Establish `hd : d = 2`. Rewrite using `[← hCM.2.2.1, Module.finrank_eq_card_basis bs, Fintype.card_fin]`. Substitute `hd` using the available equality.

Rewrite using `[card_quot bs v S hS ϖ hϖ, hcard]`.
-/
theorem q3 : PositivityTheory.SiegelWeilFormula.Gunr.Q3 := by
  intro F E _ _ _ _ _ σ d bs v S σS ϖ hQ hϖ
  obtain ⟨hCM, -, hS, -, -, -, -, hcard⟩ := hQ
  have hd : d = 2 := by
    rw [← hCM.2.2.1, Module.finrank_eq_card_basis bs, Fintype.card_fin]
  subst hd
  rw [card_quot bs v S hS ϖ hϖ, hcard]

end GlobalTheory.CompanionTheory.GunrResCard
