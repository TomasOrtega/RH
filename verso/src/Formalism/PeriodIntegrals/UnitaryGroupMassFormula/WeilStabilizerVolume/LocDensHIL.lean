import Mathlib
import Formalism.PeriodIntegrals.UnitaryGroupMassFormula.WeilStabilizerVolume.LocDensHI
import ReciprocityTheory.Automorphisms.InstMainA
import ReciprocityTheory.ResidueCardinality.ArtinOntoB

noncomputable section

namespace PI.VolStabW

namespace IdxLW

open scoped TensorProduct
open NumberField IsDedekindDomain MeasureTheory Topology Filter Formalism.MainNotions.GlobalTheoryTheory.GenusMassVolumes IsLocalRing

variable {F : Type} [Field F] [NumberField F] (v : HeightOneSpectrum (𝓞 F))

/- English proof (translation)
Rewrite using `[← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]`. Both sides reduce to the same expression.
-/
theorem index_maxIdeal :
    (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup.index = Nat.card (𝓞 F ⧸ v.asIdeal) := by
  rw [← ReciprocityTheory.Bridge.ResidueFieldCardinality.card_residue v]
  rfl

variable {E : Type} [Field E] [Algebra F E] {d : ℕ} (b : Module.Basis (Fin d) F E) (a M : ℕ)

def crdL : latSub b v a M →+ (Fin a × Fin M × Fin d → v.adicCompletionIntegers F) where
  toFun x q := ⟨(Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E)
    q.1 q.2.1) q.2.2, x.2 q.1 q.2.1 q.2.2⟩
  map_zero' := by
    funext q
    apply Subtype.ext
    simp
  map_add' x y := by
    funext q
    apply Subtype.ext
    simp

/- English proof (translation)
Introduce `c`. Set `x : Fin a → Fin M → Fv F v ⊗[F] E` to `fun i j => (Algebra.TensorProduct.basis (Fv F v) b).repr.symm (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))`. Establish `hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k)`. Introduce `i j k`. Simplify using `[x]`.

Use `⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩` and prove the remaining obligations. Use function extensionality and compare the values at `q`. Apply `Subtype.ext` to reduce the goal to its premises. Conclude with `hx q.1 q.2.1 q.2.2`.
-/
theorem crdL_surj : Function.Surjective (crdL v b a M) := by
  intro c
  let x : Fin a → Fin M → Fv F v ⊗[F] E := fun i j =>
    (Algebra.TensorProduct.basis (Fv F v) b).repr.symm
      (Finsupp.equivFunOnFinite.symm fun k => (c (i, j, k) : Fv F v))
  have hx : ∀ i j k, (Algebra.TensorProduct.basis (Fv F v) b).repr (x i j) k = c (i, j, k) := by
    intro i j k
    simp [x]
  refine ⟨⟨x, fun i j k => by rw [hx]; exact (c (i, j, k)).2⟩, ?_⟩
  funext q
  apply Subtype.ext
  exact hx q.1 q.2.1 q.2.2

/- English proof (translation)
Simplify using `[map_smul, Finsupp.smul_apply, smul_eq_mul]`.
-/
theorem crd_smul' (s : Fv F v) (y : Fv F v ⊗[F] E) (k : Fin d) :
    (Algebra.TensorProduct.basis (Fv F v) b).repr (s • y) k =
      s * (Algebra.TensorProduct.basis (Fv F v) b).repr y k := by
  simp [map_smul, Finsupp.smul_apply, smul_eq_mul]

/- English proof (translation)
Establish `hv` using `unifV_val v`. Establish `h0` using `(unifV_spec v).1`. Use extensionality with `x`. Rewrite using `[AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]`. Simplify using `only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]`.

Prove the components needed by the constructor for the conclusion. Introduce `hx q`. Simplify using `only [lamF, mem_smulSub, zero_add, pow_one] at hx`. Take `⟨p, hp, hpx⟩` from `hx`. Use `show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1`.

Rewrite using `[← hpx]`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[crd_smul', map_mul, hv]`. Establish `hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1`. Establish `h` using `hp q.1 q.2.1 q.2.2`.

Rewrite `h` using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Then use the resulting hypothesis. Combine the equalities or inequalities in the displayed calculation. Introduce `hx`. Simplify using `only [lamF, mem_smulSub, zero_add, pow_one]`. Use `⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩` and prove the remaining obligations.

Introduce `i j k`. Rewrite using `[IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]`. Simplify using `only [Pi.smul_apply]`. Rewrite using `[crd_smul', map_mul, map_inv₀, hv]`. Use `ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))` as an intermediate fact.

Combine the equalities or inequalities in the displayed calculation. Rewrite using `[smul_smul, mul_inv_cancel₀ h0, one_smul]`.
-/
theorem addSubgroupOf_eq :
    (lamF b v a M 0).addSubgroupOf (latSub b v a M) =
      (AddSubgroup.pi Set.univ fun _ : Fin a × Fin M × Fin d =>
        (maximalIdeal (v.adicCompletionIntegers F)).toAddSubgroup).comap (crdL v b a M) := by
  have hv := unifV_val v
  have h0 := (unifV_spec v).1
  ext x
  rw [AddSubgroup.mem_addSubgroupOf, AddSubgroup.mem_comap, AddSubgroup.mem_pi]
  simp only [Set.mem_univ, true_implies, Submodule.mem_toAddSubgroup, ReciprocityTheory.Aut.mem_maxIdeal_iff]
  constructor
  · intro hx q
    simp only [lamF, mem_smulSub, zero_add, pow_one] at hx
    obtain ⟨p, hp, hpx⟩ := hx
    show Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
      ((x : Fin a → Fin M → Fv F v ⊗[F] E) q.1 q.2.1) q.2.2) < 1
    rw [← hpx]
    simp only [Pi.smul_apply]
    rw [crd_smul', map_mul, hv]
    have hp' : Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr (p q.1 q.2.1) q.2.2) ≤ 1 := by
      have h := hp q.1 q.2.1 q.2.2
      rwa [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers] at h
    calc WithZero.exp (-1 : ℤ) * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
          (p q.1 q.2.1) q.2.2) ≤ WithZero.exp (-1 : ℤ) * 1 := by gcongr
      _ < 1 := by rw [mul_one]; decide
  · intro hx
    simp only [lamF, mem_smulSub, zero_add, pow_one]
    refine ⟨(unifV v)⁻¹ • (x : Fin a → Fin M → Fv F v ⊗[F] E), ?_, ?_⟩
    · intro i j k
      rw [IsDedekindDomain.HeightOneSpectrum.mem_adicCompletionIntegers]
      simp only [Pi.smul_apply]
      rw [crd_smul', map_mul, map_inv₀, hv]
      have := ReciprocityTheory.Aut.val_le_exp_neg_one_of_lt_one v (hx (i, j, k))
      calc (WithZero.exp (-1 : ℤ))⁻¹ * Valued.v ((Algebra.TensorProduct.basis (Fv F v) b).repr
            ((x : Fin a → Fin M → Fv F v ⊗[F] E) i j) k)
          ≤ (WithZero.exp (-1 : ℤ))⁻¹ * WithZero.exp (-1 : ℤ) := by gcongr; exact this
        _ = 1 := inv_mul_cancel₀ (WithZero.exp_ne_zero)
    · rw [smul_smul, mul_inv_cancel₀ h0, one_smul]

end IdxLW

open IdxLW

/- English proof (translation)
Introduce `F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v`. Establish `: FiniteDimensional F E` using `Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)`. Establish `hd : d = 2`. Use `Module.finrank_eq_card_basis b` as an intermediate fact. Rewrite `this` using `[hCM.2.2.1, Fintype.card_fin]`.

Conclude with `this.symm`. Unfold `AddSubgroup.relIndex`. Rewrite using `[addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M), AddSubgroup.index_pi]`. Simplify using `only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod, Fintype.card_fin]`. Substitute `hd` using the available equality.

Put the polynomial expressions in normal form.
-/
theorem idxL_holds : IdxL := by
  intro F E _ _ _ _ _ σ hCM M J hJ _ _ a _ _ X0 hT _ d b v
  have : FiniteDimensional F E := Module.finite_of_finrank_pos (by rw [hCM.2.2.1]; norm_num)
  have hd : d = 2 := by
    have := Module.finrank_eq_card_basis b
    rw [hCM.2.2.1, Fintype.card_fin] at this
    exact this.symm
  unfold AddSubgroup.relIndex
  rw [addSubgroupOf_eq, AddSubgroup.index_comap_of_surjective _ (crdL_surj v b a M),
    AddSubgroup.index_pi]
  simp only [index_maxIdeal, Finset.prod_const, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  subst hd
  ring_nf

end PI.VolStabW
