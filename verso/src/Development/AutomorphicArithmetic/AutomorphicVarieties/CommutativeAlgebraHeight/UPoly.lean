import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebraHeight.FinDefs
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.AevalMulHomog

open TensorProduct IsLocalRing Polynomial UpperTheory.V.W UpperTheory.V.Alg UpperTheory.V.CA

/- English proof (translation)
The claim follows from `_root_.UpperTheory.Reformulated.B.Qk4.aeval_mul_homog hP b x`.
-/
private theorem aeval_mul_homog {n : ℕ} {A G S : Type} [CommRing A] [CommRing S] [Algebra A S]
    {P : MvPolynomial G A} (hP : P.IsHomogeneous n) (b : S) (x : G → S) :
    MvPolynomial.aeval (fun g => b * x g) P = b ^ n * MvPolynomial.aeval x P :=
  _root_.UpperTheory.Reformulated.B.Qk4.aeval_mul_homog hP b x

/- English proof (translation)
Introduce `n A G _ _ _ _ P hP h1 hm`. Use `⟨⟨fun S _ _ => ⟨⟨fun y => MvPolynomial.aeval (fun g => y.coeff g) P, ?_⟩, ?_⟩, ?_, ?_⟩, fun S _ _ y => rfl⟩` and prove the remaining obligations. Establish `h : (fun g => (1 : MonoidAlgebra S G).coeff g) = fun g => Algebra.ofId A S ((Pi.single 1 1 : G → A) g)`. Use function extensionality and compare the values at `g`. Distinguish the cases in `hg : g = 1`.

Substitute `hg` using the available equality. Simplify using `[MonoidAlgebra.one_def]`. Simplify using `[MonoidAlgebra.one_def, hg, Ne.symm hg]`. Rewrite using `[h, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval, h1, map_one]`. Introduce `x y`.

Establish `h` using `congrArg (MvPolynomial.aeval (R := A) (Sum.elim (fun g => x.coeff g) (fun g => y.coeff g))) hm`. Rewrite `h` using `[map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.comp_aeval_apply]`. Use `Eq.trans ?_ h` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval _ P = _`. Use `congr 2`.

Use function extensionality and compare the values at `g`. Simplify using `only [map_sum, map_mul, MvPolynomial.aeval_X, Sum.elim_inl, Sum.elim_inr]`. Rewrite using `[MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]`. Simplify using the standard rewrite rules. Introduce `S T _ _ _ _ f x`.

Express the relevant statement in the definitionally equal form `MvPolynomial.aeval _ P = f (MvPolynomial.aeval _ P)`. Rewrite using `[MvPolynomial.comp_aeval_apply]`. Use `congr 2`. Introduce `S _ _ b x`. Express the relevant statement in the definitionally equal form `MvPolynomial.aeval _ P = b ^ n * (MvPolynomial.aeval _ P)`.

Rewrite using `[← aeval_mul_homog hP]`. Use `congr 2`.
-/
theorem UpperTheory.V.CA.u_poly :
    ∀ {n : ℕ} {A G : Type} [CommRing A] [Group G] [Fintype G] [DecidableEq G] (P : MvPolynomial G A), P.IsHomogeneous n → MvPolynomial.eval (Pi.single 1 1) P = 1 → MvPolynomial.aeval (fun g : G => ∑ a : G, (MvPolynomial.X (Sum.inl a) * MvPolynomial.X (Sum.inr (a⁻¹ * g)) : MvPolynomial (G ⊕ G) A)) P = MvPolynomial.rename Sum.inl P * MvPolynomial.rename Sum.inr P → ∃ D : GDet n A G, ∀ (S : Type) [CommRing S] [Algebra A S] (y : MonoidAlgebra S G), D.D S y = MvPolynomial.aeval (fun g => y.coeff g) P := by
  intro n A G _ _ _ _ P hP h1 hm
  refine ⟨⟨fun S _ _ => ⟨⟨fun y => MvPolynomial.aeval (fun g => y.coeff g) P, ?_⟩, ?_⟩, ?_, ?_⟩, fun S _ _ y => rfl⟩
  · have h : (fun g => (1 : MonoidAlgebra S G).coeff g) =
        fun g => Algebra.ofId A S ((Pi.single 1 1 : G → A) g) := by
      funext g
      by_cases hg : g = 1
      · subst hg; simp [MonoidAlgebra.one_def]
      · simp [MonoidAlgebra.one_def, hg, Ne.symm hg]
    rw [h, ← MvPolynomial.comp_aeval_apply, MvPolynomial.aeval_eq_eval, h1, map_one]
  · intro x y
    have h := congrArg (MvPolynomial.aeval (R := A) (Sum.elim (fun g => x.coeff g) (fun g => y.coeff g))) hm
    rw [map_mul, MvPolynomial.aeval_rename, MvPolynomial.aeval_rename, MvPolynomial.comp_aeval_apply] at h
    refine Eq.trans ?_ h
    change MvPolynomial.aeval _ P = _
    congr 2
    funext g
    simp only [map_sum, map_mul, MvPolynomial.aeval_X, Sum.elim_inl, Sum.elim_inr]
    rw [MonoidAlgebra.coeff_mul_apply_left, Finsupp.sum_fintype]
    simp
  · intro S T _ _ _ _ f x
    change MvPolynomial.aeval _ P = f (MvPolynomial.aeval _ P)
    rw [MvPolynomial.comp_aeval_apply]
    congr 2
  · intro S _ _ b x
    change MvPolynomial.aeval _ P = b ^ n * (MvPolynomial.aeval _ P)
    rw [← aeval_mul_homog hP]
    congr 2
