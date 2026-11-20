import Mathlib

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa7.U2 :
    Type :=
    ↥(@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
        Complex.instStarRing)

@[reducible] noncomputable def UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 :
    MeasurableSpace UpperTheory.Reformulated.B.Gwa7.U2 :=
    @borel UpperTheory.Reformulated.B.Gwa7.U2
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
attribute [local instance] UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2

/- English proof (translation)
Conclude with `(inferInstance : IsTopologicalGroup (Matrix.unitaryGroup (Fin 2) ℂ))`.
-/
theorem UpperTheory.Reformulated.B.Gwa7.aux3 :
    @IsTopologicalGroup
      (↥(@unitary
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Semiring.toMonoid
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@StarRing.toStarMul
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                (@Semiring.toNonUnitalSemiring Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
            (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
                (@Semiring.toNonUnitalSemiring Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
              Complex.instStarRing))))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Monoid.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Semiring.toMonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Monoid.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Semiring.toMonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Monoid.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Semiring.toMonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@unitary
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Semiring.toMonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                  (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
              (@StarRing.toStarMul
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@Semiring.toNonUnitalSemiring Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
                (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
                    (@Semiring.toNonUnitalSemiring Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
                  Complex.instStarRing)))
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      (@Unitary.instGroupSubtypeMemSubmonoidUnitary
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (@Semiring.toMonoid
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@StarRing.toStarMul
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
            Complex.instStarRing))) := by
  exact (inferInstance : IsTopologicalGroup (Matrix.unitaryGroup (Fin 2) ℂ))

/- English proof (translation)
Conclude with `⟨rfl⟩`.
-/
theorem UpperTheory.Reformulated.B.Gwa7.aux4 :
    @BorelSpace UpperTheory.Reformulated.B.Gwa7.U2
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 := by
  exact ⟨rfl⟩

/- English proof (translation)
Use `isCompact_iff_compactSpace.1 ?_` and prove the remaining obligations. Establish `hK : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 => Metric.closedBall (0 : ℂ) 1)` using `isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _`. Use `IsCompact.of_isClosed_subset (X := Matrix (Fin 2) (Fin 2) ℂ) hK (isClosed_unitary (R := Matrix (Fin 2) (Fin 2) ℂ)) ?_` and prove the remaining obligations. Introduce `U hU i _ j _`. Simplify using `using entry_norm_bound_of_unitary hU i j`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.compact_unitary :
    CompactSpace (Matrix.unitaryGroup (Fin 2) ℂ) := by
  refine isCompact_iff_compactSpace.1 ?_
  have hK : IsCompact (Set.pi Set.univ fun _ : Fin 2 => Set.pi Set.univ fun _ : Fin 2 =>
      Metric.closedBall (0 : ℂ) 1) :=
    isCompact_univ_pi fun _ => isCompact_univ_pi fun _ => isCompact_closedBall _ _
  refine IsCompact.of_isClosed_subset (X := Matrix (Fin 2) (Fin 2) ℂ) hK
    (isClosed_unitary (R := Matrix (Fin 2) (Fin 2) ℂ)) ?_
  intro U hU i _ j _
  simpa using entry_norm_bound_of_unitary hU i j

/- English proof (translation)
Conclude with `UpperTheory.Reformulated.B.Gwa7.compact_unitary`.
-/
theorem UpperTheory.Reformulated.B.Gwa7.aux5 :
    @CompactSpace
      (↥(@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
            @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@Field.toCommRing Complex
            (@NormedField.toField Complex
              (@DenselyNormedField.toNormedField Complex (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))
          (@RCLike.toStarRing Complex Complex.instRCLike)))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex
                      (@CommRing.toCommSemiring Complex
                        (@Field.toCommRing Complex
                          (@NormedField.toField Complex
                            (@DenselyNormedField.toNormedField Complex
                              (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                    @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex
                        (@CommRing.toCommSemiring Complex
                          (@Field.toCommRing Complex
                            (@NormedField.toField Complex
                              (@DenselyNormedField.toNormedField Complex
                                (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                      @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex
                        (@CommRing.toCommSemiring Complex
                          (@Field.toCommRing Complex
                            (@NormedField.toField Complex
                              (@DenselyNormedField.toNormedField Complex
                                (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                      @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (fun (a b : Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) ↦
                @LinearOrder.toDecidableEq (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (@Fin.instLinearOrder (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) a b)
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Field.toCommRing Complex
                (@NormedField.toField Complex
                  (@DenselyNormedField.toNormedField Complex (@RCLike.toDenselyNormedField Complex Complex.instRCLike))))
              (@RCLike.toStarRing Complex Complex.instRCLike))
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@NormedField.toNormedCommRing Complex
                      (@DenselyNormedField.toNormedField Complex
                        (@RCLike.toDenselyNormedField Complex Complex.instRCLike)))))))))) := by
  exact UpperTheory.Reformulated.B.Gwa7.compact_unitary

/- English proof (translation)
Conclude with `⟨1⟩`.
-/
theorem UpperTheory.Reformulated.B.Gwa7.aux6 :
    Nonempty UpperTheory.Reformulated.B.Gwa7.U2 := by
  exact ⟨1⟩

noncomputable def UpperTheory.Reformulated.B.Gwa7.μK :
    @MeasureTheory.Measure UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 :=
    @MeasureTheory.Measure.haarMeasure UpperTheory.Reformulated.B.Gwa7.U2
      (@Unitary.instGroupSubtypeMemSubmonoidUnitary
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (@Semiring.toMonoid
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
        (@StarRing.toStarMul
          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
          (@NonUnitalSemiring.toNonUnitalNonAssocSemiring
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Matrix.nonUnitalSemiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing)))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))
          (@Matrix.instStarRing (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
            (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
            (@NonUnitalSemiring.toNonUnitalNonAssocSemiring Complex
              (@Semiring.toNonUnitalSemiring Complex
                (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))))
            Complex.instStarRing)))
      (@instTopologicalSpaceSubtype
        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
        (fun
            (x :
              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
          @Membership.mem
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (@Submonoid
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@MulZeroOneClass.toMulOneClass
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@instMulZeroOneClassOfSemiring
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
            (@SetLike.instMembership
              (@Submonoid
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
              (@Submonoid.instSetLike
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@MulZeroOneClass.toMulOneClass
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@instMulZeroOneClassOfSemiring
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
              Complex.instStarRing)
            x)
        (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
      UpperTheory.Reformulated.B.Gwa7.aux3 UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 UpperTheory.Reformulated.B.Gwa7.aux4
      (@Top.top
        (@TopologicalSpace.PositiveCompacts UpperTheory.Reformulated.B.Gwa7.U2
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex)))))))))
        (@TopologicalSpace.PositiveCompacts.instTopOfCompactSpaceOfNonempty UpperTheory.Reformulated.B.Gwa7.U2
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
          UpperTheory.Reformulated.B.Gwa7.aux5 UpperTheory.Reformulated.B.Gwa7.aux6))

section Algebra
variable {A : Type*} [NormedCommRing A] [NormedAlgebra ℂ A]

/- English proof (translation)
Establish `h1 : HasDerivAt (fun t => φ (f t)) (φ f') 0` using `φ.hasFDerivAt.comp_hasDerivAt 0 hf`. Establish `h2 : (fun t => φ (f t)) = fun _ => (0 : ℂ)` using `funext h`. Rewrite `h1` using `[h2]`. Conclude with `h1.unique (hasDerivAt_const 0 0)`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.deriv_zero (φ : A →L[ℂ] ℂ) {f : ℂ → A} {f' : A}
    (hf : HasDerivAt f f' 0) (h : ∀ t, φ (f t) = 0) : φ f' = 0 := by
  have h1 : HasDerivAt (fun t => φ (f t)) (φ f') 0 := φ.hasFDerivAt.comp_hasDerivAt 0 hf
  have h2 : (fun t => φ (f t)) = fun _ => (0 : ℂ) := funext h
  rw [h2] at h1
  exact h1.unique (hasDerivAt_const 0 0)

/- English proof (translation)
Simplify using `using ((hasDerivAt_id (0 : ℂ)).smul_const y).const_add x`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.line_deriv (x y : A) :
    HasDerivAt (fun t : ℂ => x + t • y) y 0 := by
  simpa using ((hasDerivAt_id (0 : ℂ)).smul_const y).const_add x

/- English proof (translation)
Establish `h1` using `UpperTheory.Reformulated.B.Gwa7.deriv_zero φ (((UpperTheory.Reformulated.B.Gwa7.line_deriv x y).pow (n + 1)).mul_const c) h`. Establish `h2 : ((n + 1 : ℕ) : A) * (x + (0 : ℂ) • y) ^ (n + 1 - 1) * y * c = ((n + 1 : ℕ) : ℂ) • (x ^ n * y * c)`. Simplify using `only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel]`. Expand and normalize the polynomial expressions, which then agree. Rewrite `h1` using `[h2, map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.step_one (φ : A →L[ℂ] ℂ) (x y c : A) (n : ℕ)
    (h : ∀ s : ℂ, φ ((x + s • y) ^ (n + 1) * c) = 0) : φ (x ^ n * y * c) = 0 := by
  have h1 := UpperTheory.Reformulated.B.Gwa7.deriv_zero φ
    (((UpperTheory.Reformulated.B.Gwa7.line_deriv x y).pow (n + 1)).mul_const c) h
  have h2 : ((n + 1 : ℕ) : A) * (x + (0 : ℂ) • y) ^ (n + 1 - 1) * y * c
      = ((n + 1 : ℕ) : ℂ) • (x ^ n * y * c) := by
    simp only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel]
    ring
  rw [h2, map_smul, smul_eq_mul] at h1
  exact (mul_eq_zero.1 h1).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero n))

/- English proof (translation)
Establish `h1` using `UpperTheory.Reformulated.B.Gwa7.deriv_zero φ ((((UpperTheory.Reformulated.B.Gwa7.line_deriv x x').pow (n + 1)).mul (UpperTheory.Reformulated.B.Gwa7.line_deriv y y')).mul_const c) h`. Establish `h2 : (((n + 1 : ℕ) : A) * (x + (0 : ℂ) • x') ^ (n + 1 - 1) * x' * (y + (0 : ℂ) • y') + (x + (0 : ℂ) • x') ^ (n + 1) * y') * c = ((n + 2 : ℕ) : ℂ) • (x ^ (n + 1) * y' * c) - (((n + 1 : ℕ) : ℂ) * κ) • (x ^ n * Δ * c)`. Simplify using `only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel, map_mul] at hΔ ⊢`. Use `push_cast`. Take the linear combination `((n : A) + 1) * x ^ n * c * hΔ`.

Establish `h3` using `h2 ▸ h1`. Rewrite `h3` using `[map_sub, map_smul, map_smul, h', smul_zero, sub_zero, smul_eq_mul]`. Conclude with `(mul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.step_two (φ : A →L[ℂ] ℂ) (x x' y y' c Δ : A) (κ : ℂ) (n : ℕ)
    (hΔ : x' * y = x * y' - κ • Δ)
    (h : ∀ t : ℂ, φ ((x + t • x') ^ (n + 1) * (y + t • y') * c) = 0)
    (h' : φ (x ^ n * Δ * c) = 0) : φ (x ^ (n + 1) * y' * c) = 0 := by
  have h1 := UpperTheory.Reformulated.B.Gwa7.deriv_zero φ
    ((((UpperTheory.Reformulated.B.Gwa7.line_deriv x x').pow (n + 1)).mul
      (UpperTheory.Reformulated.B.Gwa7.line_deriv y y')).mul_const c) h
  have h2 : (((n + 1 : ℕ) : A) * (x + (0 : ℂ) • x') ^ (n + 1 - 1) * x' * (y + (0 : ℂ) • y')
      + (x + (0 : ℂ) • x') ^ (n + 1) * y') * c
      = ((n + 2 : ℕ) : ℂ) • (x ^ (n + 1) * y' * c) - (((n + 1 : ℕ) : ℂ) * κ) • (x ^ n * Δ * c) := by
    simp only [Algebra.smul_def, map_natCast, map_zero, zero_mul, add_zero, Nat.add_sub_cancel,
      map_mul] at hΔ ⊢
    push_cast
    linear_combination ((n : A) + 1) * x ^ n * c * hΔ
  have h3 := h2 ▸ h1
  rw [map_sub, map_smul, map_smul, h', smul_zero, sub_zero, smul_eq_mul] at h3
  exact (mul_eq_zero.1 h3).resolve_left (Nat.cast_ne_zero.2 (Nat.succ_ne_zero _))

private def UpperTheory.Reformulated.B.Gwa7.lin (p q r s : A) (a b c d : ℂ) : A :=
  (a * c) • p + (a * d) • q + (b * c) • r + (b * d) • s

/- English proof (translation)
Consider the cases of `n with`. Consider the case `zero`. Rewrite using `[← h 1 m a' b' c' d']`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Consider the case `succ n`. Establish `key` using `UpperTheory.Reformulated.B.Gwa7.step_two φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d) (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c' d') (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c d) (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c' d') (D m * z) (p …`. Rewrite using `[← key]`. Use `congr 1`. Expand and normalize the polynomial expressions, which then agree.

Simplify using `only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_sub]`. Expand and normalize the polynomial expressions, which then agree. Introduce `t`. Use `UpperTheory.Reformulated.B.Gwa7.step_one φ _ _ _ _ fun u => ?_` and prove the remaining obligations. Rewrite using `[← h (n + 1 + 1) m (a + u * a') (b + u * b') (c + t * c') (d + t * d'), ← mul_assoc]`.

Use `congr 4`. Simplify using `only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_add]`. Expand and normalize the polynomial expressions, which then agree. Rewrite using `[← h n (m + 1) a b c d, hD]`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.mul_lin (φ : A →L[ℂ] ℂ) (p q r s z : A) (D : ℤ → A)
    (hD : ∀ m, D (m + 1) = (p * s - q * r) * D m)
    (h : ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ), φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d ^ n * D m * z) = 0)
    (a' b' c' d' : ℂ) (n : ℕ) (m : ℤ) (a b c d : ℂ) :
    φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d ^ n * D m *
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c' d' * z)) = 0 := by
  cases n with
  | zero =>
    rw [← h 1 m a' b' c' d']
    congr 1
    ring
  | succ n =>
    have key := UpperTheory.Reformulated.B.Gwa7.step_two φ (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c d)
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a b c' d') (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c d)
      (UpperTheory.Reformulated.B.Gwa7.lin p q r s a' b' c' d') (D m * z) (p * s - q * r)
      ((a * b' - b * a') * (c * d' - d * c')) n ?_ ?_ ?_
    · rw [← key]
      congr 1
      ring
    · simp only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_sub]
      ring
    · intro t
      refine UpperTheory.Reformulated.B.Gwa7.step_one φ _ _ _ _ fun u => ?_
      rw [← h (n + 1 + 1) m (a + u * a') (b + u * b') (c + t * c') (d + t * d'), ← mul_assoc]
      congr 4
      simp only [UpperTheory.Reformulated.B.Gwa7.lin, Algebra.smul_def, map_mul, map_add]
      ring
    · rw [← h n (m + 1) a b c d, hD]
      congr 1
      ring

end Algebra

/- English proof (translation)
Distinguish the cases in `h0 : Complex.normSq a + Complex.normSq b = 0`. Establish `ha` using `Complex.normSq_nonneg a`. Establish `hb` using `Complex.normSq_nonneg b`. Establish `ha0 : a = 0` using `Complex.normSq_eq_zero.1 (by linarith)`. Establish `hb0 : b = 0` using `Complex.normSq_eq_zero.1 (by linarith)`.

Conclude with `⟨0, 1, 0, by simp [ha0], by simp [hb0], by simp⟩`. Establish `hpos : 0 ≤ Complex.normSq a + Complex.normSq b` using `add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b) set r : ℝ := Real.sqrt (Complex.normSq a + Complex.normSq b) with hr`. Establish `hrr : r * r = Complex.normSq a + Complex.normSq b` using `Real.mul_self_sqrt hpos`. Establish `hr0 : (r : ℂ) ≠ 0`. Introduce `h`.

Rewrite `h` using `[Complex.ofReal_eq_zero]`. Rewrite `hrr` using `[h]`. Conclude with `h0 (by linarith)`. Establish `hc : (r : ℂ) * r = a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b`. Rewrite using `[Complex.mul_conj, Complex.mul_conj]`.

Conclude with `hrr` after adjusting the coercions. Use `⟨r, a / r, b / r, by field_simp, by field_simp, ?_⟩` and prove the remaining obligations. Rewrite using `[map_div₀, map_div₀, Complex.conj_ofReal]`. Clear the denominators using the available nonvanishing facts. Take the linear combination `-hc`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.unit_vec (a b : ℂ) :
    ∃ r α β : ℂ, a = r * α ∧ b = r * β ∧
      α * (starRingEnd ℂ) α + β * (starRingEnd ℂ) β = 1 := by
  by_cases h0 : Complex.normSq a + Complex.normSq b = 0
  · have ha := Complex.normSq_nonneg a
    have hb := Complex.normSq_nonneg b
    have ha0 : a = 0 := Complex.normSq_eq_zero.1 (by linarith)
    have hb0 : b = 0 := Complex.normSq_eq_zero.1 (by linarith)
    exact ⟨0, 1, 0, by simp [ha0], by simp [hb0], by simp⟩
  · have hpos : 0 ≤ Complex.normSq a + Complex.normSq b :=
      add_nonneg (Complex.normSq_nonneg a) (Complex.normSq_nonneg b)
    set r : ℝ := Real.sqrt (Complex.normSq a + Complex.normSq b) with hr
    have hrr : r * r = Complex.normSq a + Complex.normSq b := Real.mul_self_sqrt hpos
    have hr0 : (r : ℂ) ≠ 0 := by
      intro h
      rw [Complex.ofReal_eq_zero] at h
      rw [h] at hrr
      exact h0 (by linarith)
    have hc : (r : ℂ) * r = a * (starRingEnd ℂ) a + b * (starRingEnd ℂ) b := by
      rw [Complex.mul_conj, Complex.mul_conj]
      exact_mod_cast hrr
    refine ⟨r, a / r, b / r, by field_simp, by field_simp, ?_⟩
    rw [map_div₀, map_div₀, Complex.conj_ofReal]
    field_simp
    linear_combination -hc

private noncomputable def UpperTheory.Reformulated.B.Gwa7.entry (i j : Fin 2) : C(UpperTheory.Reformulated.B.Gwa7.U2, ℂ) :=
  ⟨fun k => k.1 i j, continuous_subtype_val.matrix_elem i j⟩

/- English proof (translation)
The claim follows from `(Unitary.isUnit_coe (U := ⟨_, Matrix.det_of_mem_unitary k.2⟩)).ne_zero`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.det_ne (k : UpperTheory.Reformulated.B.Gwa7.U2) : k.1.det ≠ 0 :=
  (Unitary.isUnit_coe (U := ⟨_, Matrix.det_of_mem_unitary k.2⟩)).ne_zero

private noncomputable def UpperTheory.Reformulated.B.Gwa7.detPow (m : ℤ) : C(UpperTheory.Reformulated.B.Gwa7.U2, ℂ) :=
  ⟨fun k => k.1.det ^ m, continuous_subtype_val.matrix_det.zpow₀ m
    fun k => Or.inl (UpperTheory.Reformulated.B.Gwa7.det_ne k)⟩

/- English proof (translation)
Establish `h1 : star k.1 * k.1 = 1` using `Matrix.mem_unitaryGroup_iff'.1 k.2`. Establish `h2 : star k.1 * (k.1 * k.1.adjugate) = k.1.adjugate`. Rewrite using `[← mul_assoc, h1, one_mul]`. Rewrite `h2` using `[Matrix.mul_adjugate, Matrix.mul_smul, mul_one]`. Rewrite using `[← h2, smul_smul, inv_mul_cancel₀ (UpperTheory.Reformulated.B.Gwa7.det_ne k), one_smul]`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.star_eq (k : UpperTheory.Reformulated.B.Gwa7.U2) :
    star k.1 = (k.1.det)⁻¹ • k.1.adjugate := by
  have h1 : star k.1 * k.1 = 1 := Matrix.mem_unitaryGroup_iff'.1 k.2
  have h2 : star k.1 * (k.1 * k.1.adjugate) = k.1.adjugate := by
    rw [← mul_assoc, h1, one_mul]
  rw [Matrix.mul_adjugate, Matrix.mul_smul, mul_one] at h2
  rw [← h2, smul_smul, inv_mul_cancel₀ (UpperTheory.Reformulated.B.Gwa7.det_ne k), one_smul]

open UpperTheory.Reformulated.B.Gwa7 in
/- English proof (translation)
Apply the tactic sequence `fin_cases i <;> fin_cases j`. Conclude with `⟨1, 0, 1, 0, by simp [lin]⟩`. Conclude with `⟨1, 0, 0, 1, by simp [lin]⟩`. Conclude with `⟨0, 1, 1, 0, by simp [lin]⟩`. Conclude with `⟨0, 1, 0, 1, by simp [lin]⟩`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.entry_lin [CompactSpace U2] (i j : Fin 2) : ∃ a b c d : ℂ,
    entry i j = lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d := by
  fin_cases i <;> fin_cases j
  · exact ⟨1, 0, 1, 0, by simp [lin]⟩
  · exact ⟨1, 0, 0, 1, by simp [lin]⟩
  · exact ⟨0, 1, 1, 0, by simp [lin]⟩
  · exact ⟨0, 1, 0, 1, by simp [lin]⟩

open UpperTheory.Reformulated.B.Gwa7 in
/- English proof (translation)
Establish `h : ∀ k : U2, star (k.1 i j) = (k.1.det)⁻¹ * k.1.adjugate j i` using `fun k => by`. Use `congrFun (congrFun (star_eq k) j) i` as an intermediate fact. Simplify `this` using `[Matrix.star_apply]`. Apply the tactic sequence `fin_cases i <;> fin_cases j`. Use `⟨0, 1, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩` and prove the remaining obligations.

Simplify using `[lin, detPow, entry, Matrix.adjugate_fin_two]`. Use `⟨0, -1, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩` and prove the remaining obligations. Simplify using `[lin, detPow, entry, Matrix.adjugate_fin_two]`. Use `⟨-1, 0, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩` and prove the remaining obligations. Simplify using `[lin, detPow, entry, Matrix.adjugate_fin_two]`.

Use `⟨1, 0, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩` and prove the remaining obligations. Simplify using `[lin, detPow, entry, Matrix.adjugate_fin_two]`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.star_entry_lin [CompactSpace U2] (i j : Fin 2) : ∃ a b c d : ℂ,
    star (entry i j) = detPow (-1) * lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d := by
  have h : ∀ k : U2, star (k.1 i j) = (k.1.det)⁻¹ * k.1.adjugate j i := fun k => by
    have := congrFun (congrFun (star_eq k) j) i
    simpa [Matrix.star_apply] using this
  fin_cases i <;> fin_cases j
  · refine ⟨0, 1, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨0, -1, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨-1, 0, 0, 1, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]
  · refine ⟨1, 0, 1, 0, ContinuousMap.ext fun k => (h k).trans ?_⟩
    simp [lin, detPow, entry, Matrix.adjugate_fin_two]

open UpperTheory.Reformulated.B.Gwa7 in
/- English proof (translation)
Take `⟨r, α, β, rfl, rfl, h⟩` from `unit_vec a b`. Take `⟨s, γ, δ, rfl, rfl, h'⟩` from `unit_vec c d`. Use `⟨r * s, ⟨!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α], ?_⟩, ⟨!![γ, -(starRingEnd ℂ) δ; δ, (starRingEnd ℂ) γ], ?_⟩, fun k => ?_⟩` and prove the remaining obligations. Rewrite using `[Matrix.mem_unitaryGroup_iff]`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>`. Apply the tactic sequence `first | linear_combination h | ring`. Rewrite using `[Matrix.mem_unitaryGroup_iff']`. Use extensionality with `i j`.

Apply the tactic sequence `fin_cases i <;> fin_cases j <;>`. Apply the tactic sequence `simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>`. Apply the tactic sequence `first | linear_combination h' | ring`. Simplify using `[lin, entry, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.lin_eq [CompactSpace U2] (a b c d : ℂ) :
    ∃ (r : ℂ) (l₁ l₂ : U2), ∀ k : U2,
    lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d k = r * (l₁ * k * l₂).1 0 0 := by
  obtain ⟨r, α, β, rfl, rfl, h⟩ := unit_vec a b
  obtain ⟨s, γ, δ, rfl, rfl, h'⟩ := unit_vec c d
  refine ⟨r * s, ⟨!![α, β; -(starRingEnd ℂ) β, (starRingEnd ℂ) α], ?_⟩,
    ⟨!![γ, -(starRingEnd ℂ) δ; δ, (starRingEnd ℂ) γ], ?_⟩, fun k => ?_⟩
  · rw [Matrix.mem_unitaryGroup_iff]
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      first | linear_combination h | ring
  · rw [Matrix.mem_unitaryGroup_iff']
    ext i j
    fin_cases i <;> fin_cases j <;>
      simp [Matrix.mul_apply, Fin.sum_univ_two, Matrix.star_apply] <;>
      first | linear_combination h' | ring
  · simp [lin, entry, Matrix.mul_apply, Fin.sum_univ_two, Matrix.vecMul, dotProduct]
    ring

open UpperTheory.Reformulated.B.Gwa7 in
/- English proof (translation)
Apply the tactic sequence `let P : C(U2, ℂ) → Prop := fun z => ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ), φ (lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d ^ n * detPow m * z) = 0`. Apply the tactic sequence `have hD : ∀ m, detPow (m + 1) = (entry 0 0 * entry 1 1 - entry 0 1 * entry 1 0) * detPow m := by`. Introduce `m`. Use extensionality with `k`. Express the relevant statement in the definitionally equal form `k.1.det ^ (m + 1) = (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) * k.1.det ^ m`.

Rewrite using `[zpow_add_one₀ (det_ne k), ← Matrix.det_fin_two, mul_comm]`. Establish `hD' : ∀ m, detPow m * detPow (-1) = detPow (m + -1)`. Introduce `m`. Use extensionality with `k`. Conclude with `(zpow_add₀ (det_ne k) m (-1)).symm`.

Establish `hD0 : detPow 0 = 1`. Use extensionality with `k`. Conclude with `zpow_zero _`. Apply the tactic sequence `let S : Set C(U2, ℂ) := Set.range fun ij : Fin 2 × Fin 2 => entry ij.1 ij.2`. Establish `hmul : ∀ f ∈ Algebra.adjoin ℂ (S ∪ star S), ∀ z, P z → P (f * z)`.

Introduce `f hf`. Proceed by induction on `hf using Algebra.adjoin_induction with`. Consider the case `mem x hx`. Introduce `z hz`. Break down `hx with ⟨ij, rfl⟩ | ⟨ij, hx⟩` into its components or cases.

Take `⟨a, b, c, d, e⟩` from `entry_lin ij.1 ij.2 dsimp only`. Rewrite using `[e]`. Conclude with `mul_lin φ _ _ _ _ z detPow hD hz a b c d`. Take `⟨a, b, c, d, e⟩` from `star_entry_lin ij.1 ij.2`. Apply the tactic sequence `have hx' : x = star (entry ij.1 ij.2) := by`.

Rewrite using `[← star_star x, ← hx]`. Rewrite using `[hx', e]`. Introduce `n m a' b' c' d'`. Rewrite using `[← mul_lin φ _ _ _ _ z detPow hD hz a b c d n (m + -1) a' b' c' d', ← hD']`. Use `congr 1`.

Expand and normalize the polynomial expressions, which then agree. Consider the case `algebraMap r`. Introduce `z hz n m a b c d`. Rewrite using `[← Algebra.smul_def, mul_smul_comm, map_smul, hz, smul_zero]`. Consider the case `add x y _ _ hx hy`.

Introduce `z hz n m a b c d`. Rewrite using `[add_mul, mul_add, map_add, hx z hz, hy z hz, add_zero]`. Consider the case `mul x y _ _ hx hy`. Introduce `z hz`. Rewrite using `[mul_assoc]`.

Conclude with `hx _ (hy z hz)`. Establish `hsep : (StarAlgebra.adjoin ℂ S).SeparatesPoints`. Introduce `x y hxy`. Assume the negation of the conclusion as `hcon`. Use `hxy (Subtype.ext (Matrix.ext fun i j => ?_))` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Apply the tactic sequence `exact hcon ⟨entry i j, ⟨entry i j, StarAlgebra.subset_adjoin ℂ S ⟨(i, j), rfl⟩, rfl⟩, hne⟩`. Establish `htop` using `ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep`. Establish `hf : f ∈ closure (StarAlgebra.adjoin ℂ S : Set C(U2, ℂ))`. Establish `: f ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure`.

Rewrite using `[htop]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `this`. Use `closure_minimal (t := {f | φ f = 0}) ?_ (isClosed_eq φ.continuous continuous_const) hf` and prove the remaining obligations. Introduce `x hx`.

Use `hmul x hx 1 h 0 0 0 0 0 0` as an intermediate fact. Simplify `this` using `[hD0]`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.functional_zero [CompactSpace U2] (φ : C(U2, ℂ) →L[ℂ] ℂ)
    (h : ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ),
      φ (lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d ^ n * detPow m * 1) = 0)
    (f : C(U2, ℂ)) : φ f = 0 := by
  let P : C(U2, ℂ) → Prop := fun z => ∀ (n : ℕ) (m : ℤ) (a b c d : ℂ),
    φ (lin (entry 0 0) (entry 0 1) (entry 1 0) (entry 1 1) a b c d ^ n * detPow m * z) = 0
  have hD : ∀ m, detPow (m + 1) = (entry 0 0 * entry 1 1 - entry 0 1 * entry 1 0) * detPow m := by
    intro m
    ext k
    change k.1.det ^ (m + 1) = (k.1 0 0 * k.1 1 1 - k.1 0 1 * k.1 1 0) * k.1.det ^ m
    rw [zpow_add_one₀ (det_ne k), ← Matrix.det_fin_two, mul_comm]
  have hD' : ∀ m, detPow m * detPow (-1) = detPow (m + -1) := by
    intro m
    ext k
    exact (zpow_add₀ (det_ne k) m (-1)).symm
  have hD0 : detPow 0 = 1 := by
    ext k
    exact zpow_zero _
  let S : Set C(U2, ℂ) := Set.range fun ij : Fin 2 × Fin 2 => entry ij.1 ij.2
  have hmul : ∀ f ∈ Algebra.adjoin ℂ (S ∪ star S), ∀ z, P z → P (f * z) := by
    intro f hf
    induction hf using Algebra.adjoin_induction with
    | mem x hx =>
      intro z hz
      rcases hx with ⟨ij, rfl⟩ | ⟨ij, hx⟩
      · obtain ⟨a, b, c, d, e⟩ := entry_lin ij.1 ij.2
        dsimp only
        rw [e]
        exact mul_lin φ _ _ _ _ z detPow hD hz a b c d
      · obtain ⟨a, b, c, d, e⟩ := star_entry_lin ij.1 ij.2
        have hx' : x = star (entry ij.1 ij.2) := by
          rw [← star_star x, ← hx]
        rw [hx', e]
        intro n m a' b' c' d'
        rw [← mul_lin φ _ _ _ _ z detPow hD hz a b c d n (m + -1) a' b' c' d', ← hD']
        congr 1
        ring
    | algebraMap r =>
      intro z hz n m a b c d
      rw [← Algebra.smul_def, mul_smul_comm, map_smul, hz, smul_zero]
    | add x y _ _ hx hy =>
      intro z hz n m a b c d
      rw [add_mul, mul_add, map_add, hx z hz, hy z hz, add_zero]
    | mul x y _ _ hx hy =>
      intro z hz
      rw [mul_assoc]
      exact hx _ (hy z hz)
  have hsep : (StarAlgebra.adjoin ℂ S).SeparatesPoints := by
    intro x y hxy
    by_contra hcon
    refine hxy (Subtype.ext (Matrix.ext fun i j => ?_))
    by_contra hne
    exact hcon ⟨entry i j, ⟨entry i j, StarAlgebra.subset_adjoin ℂ S ⟨(i, j), rfl⟩, rfl⟩, hne⟩
  have htop := ContinuousMap.starSubalgebra_topologicalClosure_eq_top_of_separatesPoints _ hsep
  have hf : f ∈ closure (StarAlgebra.adjoin ℂ S : Set C(U2, ℂ)) := by
    have : f ∈ (StarAlgebra.adjoin ℂ S).topologicalClosure := by
      rw [htop]
      trivial
    exact this
  refine closure_minimal (t := {f | φ f = 0}) ?_ (isClosed_eq φ.continuous continuous_const) hf
  intro x hx
  have := hmul x hx 1 h 0 0 0 0 0 0
  simpa [hD0] using this

open UpperTheory.Reformulated.B.Gwa7 MeasureTheory in
/- English proof (translation)
Set `G : C(U2, ℂ)` to `star ⟨g, hg⟩`. Set `φ : C(U2, ℂ) →L[ℂ] ℂ` to `(innerSL ℂ (ContinuousMap.toLp 2 μ ℂ G)).comp (ContinuousMap.toLp 2 μ ℂ)`. Establish `hφ : ∀ f, φ f = ∫ k, f k * g k ∂μ`. Introduce `f`. Use `MeasureTheory.ContinuousMap.inner_toLp (𝕜 := ℂ) μ G f` as an intermediate fact.

Use `this.trans ?_` and prove the remaining obligations. Simplify using `[G]`. Establish `h0 : φ G = 0`. Use `functional_zero φ (fun n m a b c d => ?_) G` and prove the remaining obligations. Take `⟨r, l₁, l₂, e⟩` from `lin_eq a b c d`.

Rewrite using `[hφ, ← mul_zero (r ^ n), ← h n m l₁ l₂, ← integral_const_mul]`. Use `congr 1`. Use extensionality with `k`. Rewrite using `[mul_one, ContinuousMap.mul_apply, ContinuousMap.pow_apply, e]`. Express the relevant statement in the definitionally equal form `_ * k.1.det ^ m * _ = _`.

Expand and normalize the polynomial expressions, which then agree. Establish `h1 : ContinuousMap.toLp 2 μ ℂ G = 0` using `inner_self_eq_zero.1 h0`. Establish `h2 : G = 0` using `ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ (by rw [h1, map_zero])`. Use extensionality with `k`. Simplify `congrArg (fun F : C(U2, ℂ) => F k) h2` using `[G]`.
-/
private theorem UpperTheory.Reformulated.B.Gwa7.main [CompactSpace U2] [BorelSpace U2] (μ : Measure U2)
    [IsFiniteMeasure μ] [μ.IsOpenPosMeasure] {g : U2 → ℂ} (hg : Continuous g)
    (h : ∀ (n : ℕ) (q : ℤ) (l₁ l₂ : U2),
      ∫ k, (l₁ * k * l₂).1 0 0 ^ n * k.1.det ^ q * g k ∂μ = 0) : g = 0 := by
  let G : C(U2, ℂ) := star ⟨g, hg⟩
  let φ : C(U2, ℂ) →L[ℂ] ℂ :=
    (innerSL ℂ (ContinuousMap.toLp 2 μ ℂ G)).comp (ContinuousMap.toLp 2 μ ℂ)
  have hφ : ∀ f, φ f = ∫ k, f k * g k ∂μ := by
    intro f
    have := MeasureTheory.ContinuousMap.inner_toLp (𝕜 := ℂ) μ G f
    refine this.trans ?_
    simp [G]
  have h0 : φ G = 0 := by
    refine functional_zero φ (fun n m a b c d => ?_) G
    obtain ⟨r, l₁, l₂, e⟩ := lin_eq a b c d
    rw [hφ, ← mul_zero (r ^ n), ← h n m l₁ l₂, ← integral_const_mul]
    congr 1
    ext k
    rw [mul_one, ContinuousMap.mul_apply, ContinuousMap.pow_apply, e]
    change _ * k.1.det ^ m * _ = _
    ring
  have h1 : ContinuousMap.toLp 2 μ ℂ G = 0 := inner_self_eq_zero.1 h0
  have h2 : G = 0 := ContinuousMap.toLp_injective (p := 2) (𝕜 := ℂ) μ (by rw [h1, map_zero])
  ext k
  simpa [G] using congrArg (fun F : C(U2, ℂ) => F k) h2

/- English proof (translation)
Introduce `g hg h`. Use `haveI : CompactSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux5`. Use `haveI : BorelSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux4`. Use `haveI : UpperTheory.Reformulated.B.Gwa7.μK.IsHaarMeasure := MeasureTheory.Measure.isHaarMeasure_haarMeasure _`. Conclude with `UpperTheory.Reformulated.B.Gwa7.main UpperTheory.Reformulated.B.Gwa7.μK hg h`.
-/
theorem UpperTheory.Reformulated.B.Gwa7.eq_zero_of_forall_integral_coeff :
    ∀ {g : UpperTheory.Reformulated.B.Gwa7.U2 → Complex},
      @Continuous UpperTheory.Reformulated.B.Gwa7.U2 Complex
          (@instTopologicalSpaceSubtype
            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
            (fun
                (x :
                  Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
              @Membership.mem
                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                (@Submonoid
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@MulZeroOneClass.toMulOneClass
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@instMulZeroOneClassOfSemiring
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                        (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                (@SetLike.instMembership
                  (@Submonoid
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                  (@Submonoid.instSetLike
                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                    (@MulZeroOneClass.toMulOneClass
                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                      (@instMulZeroOneClassOfSemiring
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                          (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                          (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                  Complex.instStarRing)
                x)
            (@instTopologicalSpaceMatrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
              (@UniformSpace.toTopologicalSpace Complex
                (@PseudoMetricSpace.toUniformSpace Complex
                  (@SeminormedRing.toPseudoMetricSpace Complex
                    (@SeminormedCommRing.toSeminormedRing Complex
                      (@NormedCommRing.toSeminormedCommRing Complex
                        (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))))
          (@UniformSpace.toTopologicalSpace Complex
            (@PseudoMetricSpace.toUniformSpace Complex
              (@SeminormedRing.toPseudoMetricSpace Complex
                (@SeminormedCommRing.toSeminormedRing Complex
                  (@NormedCommRing.toSeminormedCommRing Complex
                    (@CommCStarAlgebra.toNormedCommRing Complex instCommCStarAlgebraComplex))))))
          g →
        (∀ (n : Nat) (q : Int) (l₁ l₂ : UpperTheory.Reformulated.B.Gwa7.U2),
            @Eq Complex
              (@MeasureTheory.integral UpperTheory.Reformulated.B.Gwa7.U2 Complex Complex.instNormedAddCommGroup
                (@InnerProductSpace.toNormedSpace Real Complex Real.instRCLike
                  (@NormedAddCommGroup.toSeminormedAddCommGroup Complex Complex.instNormedAddCommGroup)
                  instInnerProductSpaceRealComplex)
                UpperTheory.Reformulated.B.Gwa7.instMeasurableSpaceU2 UpperTheory.Reformulated.B.Gwa7.μK fun (k : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                @HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                  (@HMul.hMul Complex Complex Complex (@instHMul Complex Complex.instMul)
                    (@HPow.hPow Complex Nat Complex
                      (@instHPow Complex Nat
                        (@NPow.toPow Complex (@Monoid.toNPow Complex (@Semiring.toMonoid Complex Complex.instSemiring))))
                      (@Subtype.val
                        (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                          (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                        (fun
                            (x :
                              Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                          @Membership.mem
                            (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                            (@Submonoid
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                            (@SetLike.instMembership
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid.instSetLike
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                            (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                              (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                              Complex.commRing Complex.instStarRing)
                            x)
                        (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                          (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                            (@Submonoid.mul
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@MulZeroOneClass.toMulOneClass
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@instMulZeroOneClassOfSemiring
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                    (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                    (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)))
                          (@HMul.hMul UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2 UpperTheory.Reformulated.B.Gwa7.U2
                            (@instHMul UpperTheory.Reformulated.B.Gwa7.U2
                              (@Submonoid.mul
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))
                                (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                  Complex.commRing Complex.instStarRing)))
                            l₁ k)
                          l₂)
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0)))
                        (@OfNat.ofNat (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) (nat_lit 0)
                          (@Fin.instOfNat (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))
                            (@Nat.instNeZeroSucc (@OfNat.ofNat Nat (nat_lit 1) (instOfNatNat (nat_lit 1)))) (nat_lit 0))))
                      n)
                    (@HPow.hPow Complex Int Complex
                      (@instHPow Complex Int (@ZPow.toPow Complex (@DivInvMonoid.toZPow Complex Complex.instDivInvMonoid)))
                      (@Matrix.det (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex Complex.commRing
                        (@Subtype.val
                          (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                            (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                          (fun
                              (x :
                                Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex) ↦
                            @Membership.mem
                              (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                              (@Submonoid
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@MulZeroOneClass.toMulOneClass
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@instMulZeroOneClassOfSemiring
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      Complex
                                      (@CommSemiring.toSemiring Complex (@CommRing.toCommSemiring Complex Complex.commRing))
                                      (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                              (@SetLike.instMembership
                                (@Submonoid
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))))))
                                (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                  (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                (@Submonoid.instSetLike
                                  (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                    (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                  (@MulZeroOneClass.toMulOneClass
                                    (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                      (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                    (@instMulZeroOneClassOfSemiring
                                      (Matrix (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex)
                                      (@Matrix.semiring (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        Complex
                                        (@CommSemiring.toSemiring Complex
                                          (@CommRing.toCommSemiring Complex Complex.commRing))
                                        (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                        (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))))))))
                              (@Matrix.unitaryGroup (Fin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (instDecidableEqFin (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2))))
                                (Fin.fintype (@OfNat.ofNat Nat (nat_lit 2) (instOfNatNat (nat_lit 2)))) Complex
                                Complex.commRing Complex.instStarRing)
                              x)
                          k))
                      q))
                  (g k))
              (@OfNat.ofNat Complex (nat_lit 0) (@Zero.toOfNat0 Complex Complex.instZero))) →
          @Eq (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) g
            (@OfNat.ofNat (UpperTheory.Reformulated.B.Gwa7.U2 → Complex) (nat_lit 0)
              (@Zero.toOfNat0 (UpperTheory.Reformulated.B.Gwa7.U2 → Complex)
                (@Pi.instZero UpperTheory.Reformulated.B.Gwa7.U2 (fun (a : UpperTheory.Reformulated.B.Gwa7.U2) ↦ Complex) fun (i : UpperTheory.Reformulated.B.Gwa7.U2) ↦
                  Complex.instZero))) := by
  intro g hg h
  haveI : CompactSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux5
  haveI : BorelSpace UpperTheory.Reformulated.B.Gwa7.U2 := UpperTheory.Reformulated.B.Gwa7.aux4
  haveI : UpperTheory.Reformulated.B.Gwa7.μK.IsHaarMeasure :=
    MeasureTheory.Measure.isHaarMeasure_haarMeasure _
  exact UpperTheory.Reformulated.B.Gwa7.main UpperTheory.Reformulated.B.Gwa7.μK hg h
