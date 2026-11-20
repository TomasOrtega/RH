import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.FaceDSingle
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.MapNsmul
import Development.AutomorphicArithmetic.AutomorphicVarieties.TorsionBoundsChains.Shapiro

open CategoryTheory UpperTheory.V.KH

/- English proof (translation)
Fix the arbitrary inputs or assume the hypotheses. Introduce a local definition for the expression. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules.

Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result. Simplify using the standard rewrite rules. Introduce a local definition for the expression. Reduce the claim to the hypotheses of an applicable result.

Fix the arbitrary inputs or assume the hypotheses. Simplify using the standard rewrite rules. Establish an intermediate fact. Fix the arbitrary inputs or assume the hypotheses. Express the relevant assertion in an equivalent form by its definition.

Simplify using the standard rewrite rules. Expand and normalize the polynomial expressions, which then agree. Establish an intermediate fact. Extract witnesses or component facts from the available result. Prove the components needed by the constructor for the conclusion.

Assume the hypotheses and unpack their components. Establish an intermediate fact. Establish an intermediate fact. Simplify using the standard rewrite rules. Substitute using the available equality.

Both sides reduce to the same expression. Establish an intermediate fact. A detailed English derivation is pending.
-/
theorem UpperTheory.V.KH.kill :
    ∀ (S : Type) [Group S] [Finite S] (j : ℕ) (z : HZ S (j + 1)), Nat.card S • z = 0 := by
  intro S _ _ j z
  classical
  haveI : Fintype S := Fintype.ofFinite S
  let v : S →₀ ℤ := ∑ s : S, Finsupp.single s 1
  have hv : ∀ g : S, perm S S g v = v := by
    intro g
    simp only [v, map_sum, perm_single]
    exact Fintype.sum_equiv (MulAction.toPerm g) _ _ (fun _ => rfl)
  let fi : (Rep.trivial ℤ S ℤ).ρ.IntertwiningMap (permRep S S).ρ :=
    ⟨LinearMap.toSpanSingleton ℤ _ v, fun g => by
      apply LinearMap.ext_ring
      simp [Rep.trivial_ρ, permRep, hv]⟩
  let gi : (permRep S S).ρ.IntertwiningMap (Rep.trivial ℤ S ℤ).ρ :=
    ⟨aug S, fun g => by
      apply Finsupp.lhom_ext
      intro x c
      simp [Rep.trivial_ρ, permRep, perm_single, aug_single]⟩
  have hcomp : ∀ a : Rep.trivial ℤ S ℤ,
      (Rep.Hom.hom (Rep.ofHom gi)) ((Rep.Hom.hom (Rep.ofHom fi)) a) = Nat.card S • a := by
    intro a
    change aug S (a • v) = Nat.card S • a
    simp only [v, map_smul, map_sum, aug_single, Finset.sum_const, Finset.card_univ, smul_eq_mul,
      nsmul_eq_mul, Nat.card_eq_fintype_card, mul_one]
    ring
  have hsub : Subsingleton (groupHomology (permRep S S) (j + 1)) := by
    obtain ⟨e⟩ := shapiro S S (1 : S) (j + 1)
    haveI : Subsingleton (MulAction.stabilizer S (1 : S)) := by
      constructor
      rintro ⟨a, ha⟩ ⟨b, hb⟩
      have ha' : a * 1 = 1 := ha
      have hb' : b * 1 = 1 := hb
      simp only [mul_one] at ha' hb'
      subst ha' hb'
      rfl
    have hz := ModuleCat.isZero_iff_subsingleton.mp
      (isZero_groupHomology_succ_of_subsingleton
        (Rep.trivial ℤ (MulAction.stabilizer S (1 : S)) ℤ) j)
    exact e.injective.subsingleton
  exact mapNsmul S (Rep.trivial ℤ S ℤ) (permRep S S) (Rep.ofHom fi) (Rep.ofHom gi) (Nat.card S) (j + 1) hcomp hsub z
