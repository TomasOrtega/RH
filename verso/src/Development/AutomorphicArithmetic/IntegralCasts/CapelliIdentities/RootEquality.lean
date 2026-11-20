import Mathlib
import Development.AutomorphicArithmetic.AutomorphicVarieties.CommutativeAlgebra.ResMapBijective
import Development.AutomorphicArithmetic.IntegralCasts.CapelliIdentities.CoboundaryCriterion

@[reducible] noncomputable def UpperTheory.Reformulated.B.RootEquality.G.{u_1, u_2} :
    (F : Type u_1) →
      (Ω : Type u_2) →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [@Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
              Type u_2 :=
    fun (F : Type u_1) (Ω : Type u_2) [inst : Field F] [inst_1 : Field Ω]
        [inst_2 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] ↦
      @AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2 inst_2

noncomputable def UpperTheory.Reformulated.B.RootEquality.Dec.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 :
                @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
              @ValuationSubring Ω inst_1 →
                @Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2) :=
    fun {F : Type u_1} {Ω : Type u_2} [inst : Field F] [inst_1 : Field Ω]
        [inst_2 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))]
        (A : @ValuationSubring Ω inst_1) ↦
      @ValuationSubring.decompositionSubgroup F Ω inst inst_1 inst_2 A

noncomputable def UpperTheory.Reformulated.B.RootEquality.IsPlaceOver.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [inst_1 : Field Ω] →
            [@Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
              @ValuationSubring Ω inst_1 →
                @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst) →
                  Prop :=
    fun {F : Type u_1} {Ω : Type u_2} [inst : Field F] [inst_1 : Field Ω]
        [inst_2 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))]
        (A : @ValuationSubring Ω inst_1)
        (v :
          @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
            (@NumberField.instCommRingRingOfIntegers F inst)) ↦
      ∀ (x : @NumberField.RingOfIntegers F inst),
        Iff

          (@LT.lt (@ValuationSubring.ValueGroup Ω inst_1 A)
            (@Preorder.toLT (@ValuationSubring.ValueGroup Ω inst_1 A)
              (@PartialOrder.toPreorder (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@SemilatticeInf.toPartialOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@Lattice.toSemilatticeInf (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DistribLattice.toLattice (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@instDistribLatticeOfLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@LinearOrderedCommMonoidWithZero.toLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                            (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))
            (@DFunLike.coe
              (@Valuation Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))
                (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))
              Ω (fun (x : Ω) ↦ @ValuationSubring.ValueGroup Ω inst_1 A)
              (@Valuation.instFunLike Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1))
                (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))
              (@ValuationSubring.valuation Ω inst_1 A)
              (@DFunLike.coe
                (@RingHom F Ω
                  (@Semiring.toNonAssocSemiring F
                    (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                  (@Semiring.toNonAssocSemiring Ω
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))))
                F (fun (x : F) ↦ Ω)
                (@RingHom.instFunLike F Ω
                  (@Semiring.toNonAssocSemiring F
                    (@CommSemiring.toSemiring F (@Semifield.toCommSemiring F (@Field.toSemifield F inst))))
                  (@Semiring.toNonAssocSemiring Ω
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))))
                (@Algebra.algebraMap F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2)
                (@NumberField.RingOfIntegers.val F inst x)))
            (@OfNat.ofNat (@ValuationSubring.ValueGroup Ω inst_1 A) (nat_lit 1)
              (@One.toOfNat1 (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@InvOneClass.toOne (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@DivInvOneMonoid.toInvOneClass (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DivisionMonoid.toDivInvOneMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DivisionCommMonoid.toDivisionMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@CommGroupWithZero.toDivisionCommMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@LinearOrderedCommGroupWithZero.toCommGroupWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))))))))))
          (@Membership.mem (@NumberField.RingOfIntegers F inst)
            (@Ideal (@NumberField.RingOfIntegers F inst)
              (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                  (@NumberField.instCommRingRingOfIntegers F inst))))
            (@SetLike.instMembership
              (@Ideal (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                    (@NumberField.instCommRingRingOfIntegers F inst))))
              (@NumberField.RingOfIntegers F inst)
              (@Submodule.setLike (@NumberField.RingOfIntegers F inst) (@NumberField.RingOfIntegers F inst)
                (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                  (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)

                    (@NumberField.instCommRingRingOfIntegers F inst)))
                (@Semiring.toAddCommMonoid (@NumberField.RingOfIntegers F inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))
                (@Semiring.toModule (@NumberField.RingOfIntegers F inst)
                  (@CommSemiring.toSemiring (@NumberField.RingOfIntegers F inst)
                    (@CommRing.toCommSemiring (@NumberField.RingOfIntegers F inst)
                      (@NumberField.instCommRingRingOfIntegers F inst))))))
            (@IsDedekindDomain.HeightOneSpectrum.asIdeal (@NumberField.RingOfIntegers F inst)
              (@NumberField.instCommRingRingOfIntegers F inst) v)
            x)

noncomputable def UpperTheory.Reformulated.B.RootEquality.LC :
    {R Γ M : Type} →
      [inst : CommRing R] →
        [inst_1 : Group Γ] →
          [inst_2 : AddCommGroup M] →
            [inst_3 :
                @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@AddCommGroup.toAddCommMonoid M inst_2)] →
              @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2)
                  inst_3 →
                [TopologicalSpace Γ] → Prop :=
    fun {R Γ M : Type} [inst : CommRing R] [inst_1 : Group Γ] [inst_2 : AddCommGroup M]
        [inst_3 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_2)]
        (ρ :
          @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
        [inst_4 : TopologicalSpace Γ] ↦
      ∀ (m : M),
        @IsLocallyConstant Γ M inst_4 fun (g : Γ) ↦
          @DFunLike.coe
            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@RingHom.id R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
            M (fun (x : M) ↦ M)
            (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_2)
              (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
              (@RingHom.id R
                (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
            (@DFunLike.coe
              (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
              Γ
              (fun (x : Γ) ↦
                @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
              (@MonoidHom.instFunLike Γ
                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))

                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                (@MulOneClass.toMulOne Γ
                  (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                (@MulOneClass.toMulOne
                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@RingHom.id R
                      (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                    M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                  (@MulZeroOneClass.toMulOneClass
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                    (@instMulZeroOneClassOfSemiring
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                      (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
              ρ g)
            m

/- English proof (translation)
Conclude with `fun ρ _ _ _ hx hy ↦ ⟨hx.1.add hy.1, fun g h ↦ by`. Simplify using `only [Pi.add_apply, hx.2 g h, hy.2 g h, map_add]`. Use the proof step `abel⟩`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.aux5 :
    ∀ {R Γ M : Type} [inst : CommRing R] [inst_1 : Group Γ] [inst_2 : AddCommGroup M]
      [inst_3 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2)]
      (ρ :
        @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
      [inst_4 : TopologicalSpace Γ] {x y : Γ → M},
      @Membership.mem (Γ → M) (Set (Γ → M)) (@Set.instMembership (Γ → M))
          (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
            And (@IsLocallyConstant Γ M inst_4 z)
              (∀ (g h : Γ),
                @Eq M
                  (z
                    (@HMul.hMul Γ Γ Γ
                      (@instHMul Γ
                        (@MulOne.toMul Γ
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                      g h))
                  (@HAdd.hAdd M M M
                    (@instHAdd M
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                    (z g)
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))

                        M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      (@DFunLike.coe
                        (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        Γ
                        (fun (x : Γ) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                        (@MonoidHom.instFunLike Γ
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                        ρ g)
                      (z h)))))
          x →
        @Membership.mem (Γ → M) (Set (Γ → M)) (@Set.instMembership (Γ → M))

            (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
              And (@IsLocallyConstant Γ M inst_4 z)
                (∀ (g h : Γ),
                  @Eq M
                    (z
                      (@HMul.hMul Γ Γ Γ
                        (@instHMul Γ
                          (@MulOne.toMul Γ
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                        g h))
                    (@HAdd.hAdd M M M
                      (@instHAdd M
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                      (z g)
                      (@DFunLike.coe
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                          inst_3)
                        M (fun (x : M) ↦ M)
                        (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@DFunLike.coe
                          (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          Γ
                          (fun (x : Γ) ↦
                            @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                          (@MonoidHom.instFunLike Γ
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                            (@MulOneClass.toMulOne
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))

                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@MulZeroOneClass.toMulOneClass
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@instMulZeroOneClassOfSemiring
                                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.id R
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                    inst_3 inst_3)
                                  (@Module.End.instSemiring R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          ρ g)
                        (z h)))))
            y →
          @Membership.mem (Γ → M) (Set (Γ → M)) (@Set.instMembership (Γ → M))
            (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
              And (@IsLocallyConstant Γ M inst_4 z)
                (∀ (g h : Γ),
                  @Eq M
                    (z
                      (@HMul.hMul Γ Γ Γ
                        (@instHMul Γ
                          (@MulOne.toMul Γ
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                        g h))
                    (@HAdd.hAdd M M M
                      (@instHAdd M
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                      (z g)
                      (@DFunLike.coe
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                          inst_3)
                        M (fun (x : M) ↦ M)
                        (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@DFunLike.coe
                          (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)

                          Γ
                          (fun (x : Γ) ↦
                            @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                          (@MonoidHom.instFunLike Γ
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                            (@MulOneClass.toMulOne
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@MulZeroOneClass.toMulOneClass
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@instMulZeroOneClassOfSemiring
                                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.id R
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                    inst_3 inst_3)
                                  (@Module.End.instSemiring R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          ρ g)
                        (z h)))))
            (@HAdd.hAdd (Γ → M) (Γ → M) (Γ → M)
              (@instHAdd (Γ → M)
                (@AddZero.toAdd (Γ → M)
                  (@AddZeroClass.toAddZero (Γ → M)
                    (@AddMonoid.toAddZeroClass (Γ → M)
                      (@AddCommMonoid.toAddMonoid (Γ → M)
                        (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2))))))
              x y) := by
  exact fun ρ _ _ _ hx hy ↦ ⟨hx.1.add hy.1, fun g h ↦ by
    simp only [Pi.add_apply, hx.2 g h, hy.2 g h, map_add]; abel⟩

/- English proof (translation)
Conclude with `fun ρ _ ↦ ⟨IsLocallyConstant.const _, fun g h ↦ by simp⟩`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.aux6 :
    ∀ {R Γ M : Type} [inst : CommRing R] [inst_1 : Group Γ] [inst_2 : AddCommGroup M]

      [inst_3 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2)]
      (ρ :
        @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
      [inst_4 : TopologicalSpace Γ],
      And
        (@IsLocallyConstant Γ M inst_4
          (@OfNat.ofNat (Γ → M) (nat_lit 0)
            (@Zero.toOfNat0 (Γ → M)
              (@AddZero.toZero (Γ → M)
                (@AddZeroClass.toAddZero (Γ → M)
                  (@AddMonoid.toAddZeroClass (Γ → M)
                    (@AddCommMonoid.toAddMonoid (Γ → M)
                      (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2))))))))
        (∀ (g h : Γ),
          @Eq M
            (@OfNat.ofNat (Γ → M) (nat_lit 0)
              (@Zero.toOfNat0 (Γ → M)
                (@AddZero.toZero (Γ → M)
                  (@AddZeroClass.toAddZero (Γ → M)
                    (@AddMonoid.toAddZeroClass (Γ → M)
                      (@AddCommMonoid.toAddMonoid (Γ → M)
                        (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2))))))
              (@HMul.hMul Γ Γ Γ
                (@instHMul Γ
                  (@MulOne.toMul Γ
                    (@MulOneClass.toMulOne Γ
                      (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                g h))
            (@HAdd.hAdd M M M
              (@instHAdd M
                (@AddCommMagma.toAdd M
                  (@AddCommSemigroup.toAddCommMagma M
                    (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
              (@OfNat.ofNat (Γ → M) (nat_lit 0)
                (@Zero.toOfNat0 (Γ → M)
                  (@AddZero.toZero (Γ → M)
                    (@AddZeroClass.toAddZero (Γ → M)
                      (@AddMonoid.toAddZeroClass (Γ → M)
                        (@AddCommMonoid.toAddMonoid (Γ → M)
                          (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2))))))
                g)
              (@DFunLike.coe
                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                M (fun (x : M) ↦ M)
                (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)) (@AddCommGroup.toAddCommMonoid M inst_2)
                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                  (@RingHom.id R
                    (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                (@DFunLike.coe
                  (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2)
                    inst_3)

                  Γ
                  (fun (x : Γ) ↦
                    @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                  (@MonoidHom.instFunLike Γ
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                    (@MulOneClass.toMulOne Γ
                      (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                    (@MulOneClass.toMulOne
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                      (@MulZeroOneClass.toMulOneClass
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                          inst_3)
                        (@instMulZeroOneClassOfSemiring
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                          (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                  ρ g)
                (@OfNat.ofNat (Γ → M) (nat_lit 0)
                  (@Zero.toOfNat0 (Γ → M)
                    (@AddZero.toZero (Γ → M)
                      (@AddZeroClass.toAddZero (Γ → M)
                        (@AddMonoid.toAddZeroClass (Γ → M)
                          (@AddCommMonoid.toAddMonoid (Γ → M)
                            (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦
                              @AddCommGroup.toAddCommMonoid M inst_2))))))
                  h)))) := by
  exact fun ρ _ ↦ ⟨IsLocallyConstant.const _, fun g h ↦ by simp⟩

/- English proof (translation)
Conclude with `fun ρ _ c _ hx ↦ ⟨hx.1.comp (fun m ↦ c • m), fun g h ↦ by`. Simplify using `only [Pi.smul_apply, hx.2 g h, map_smul, smul_add]⟩`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.aux7 :
    ∀ {R Γ M : Type} [inst : CommRing R] [inst_1 : Group Γ] [inst_2 : AddCommGroup M]
      [inst_3 :
        @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2)]
      (ρ :
        @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
      [inst_4 : TopologicalSpace Γ] (c : R) {x : Γ → M},
      @Membership.mem (Γ → M) (Set (Γ → M)) (@Set.instMembership (Γ → M))

          (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
            And (@IsLocallyConstant Γ M inst_4 z)
              (∀ (g h : Γ),
                @Eq M
                  (z
                    (@HMul.hMul Γ Γ Γ
                      (@instHMul Γ
                        (@MulOne.toMul Γ
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                      g h))
                  (@HAdd.hAdd M M M
                    (@instHAdd M
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                    (z g)
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      (@DFunLike.coe
                        (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        Γ
                        (fun (x : Γ) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                        (@MonoidHom.instFunLike Γ
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)

                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                        ρ g)
                      (z h)))))
          x →
        @Membership.mem (Γ → M) (Set (Γ → M)) (@Set.instMembership (Γ → M))
          (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
            And (@IsLocallyConstant Γ M inst_4 z)
              (∀ (g h : Γ),
                @Eq M
                  (z
                    (@HMul.hMul Γ Γ Γ
                      (@instHMul Γ
                        (@MulOne.toMul Γ
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                      g h))
                  (@HAdd.hAdd M M M
                    (@instHAdd M
                      (@AddCommMagma.toAdd M
                        (@AddCommSemigroup.toAddCommMagma M
                          (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                    (z g)
                    (@DFunLike.coe
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3)
                      M (fun (x : M) ↦ M)
                      (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                      (@DFunLike.coe
                        (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                        Γ
                        (fun (x : Γ) ↦
                          @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R

                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                        (@MonoidHom.instFunLike Γ
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                            inst_3)
                          (@MulOneClass.toMulOne Γ
                            (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                          (@MulOneClass.toMulOne
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                            (@MulZeroOneClass.toMulOneClass
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@instMulZeroOneClassOfSemiring
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                        ρ g)
                      (z h)))))
          (@HSMul.hSMul R (Γ → M) (Γ → M)
            (@instHSMul R (Γ → M)
              (@SMulZeroClass.toSMul R (Γ → M)
                (@AddZero.toZero (Γ → M)
                  (@AddZeroClass.toAddZero (Γ → M)
                    (@AddMonoid.toAddZeroClass (Γ → M)
                      (@AddCommMonoid.toAddMonoid (Γ → M)
                        (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)))))
                (@DistribSMul.toSMulZeroClass R (Γ → M)
                  (@AddMonoid.toAddZeroClass (Γ → M)
                    (@AddCommMonoid.toAddMonoid (Γ → M)
                      (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)))
                  (@DistribMulAction.toDistribSMul R (Γ → M)
                    (@Semiring.toMonoid R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))
                    (@AddCommMonoid.toAddMonoid (Γ → M)
                      (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2))
                    (@Module.toDistribMulAction R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)

                      (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                        (@AddCommGroup.toAddCommMonoid M inst_2) inst_3))))))
            c x) := by
  exact fun ρ _ c _ hx ↦ ⟨hx.1.comp (fun m ↦ c • m), fun g h ↦ by
    simp only [Pi.smul_apply, hx.2 g h, map_smul, smul_add]⟩

noncomputable def UpperTheory.Reformulated.B.RootEquality.Zl :
    {R Γ M : Type} →
      [inst : CommRing R] →
        [inst_1 : Group Γ] →
          [inst_2 : AddCommGroup M] →
            [inst_3 :
                @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@AddCommGroup.toAddCommMonoid M inst_2)] →
              @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                  (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2)
                  inst_3 →
                [TopologicalSpace Γ] →
                  @Submodule R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                    (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)
                    (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                      (@AddCommGroup.toAddCommMonoid M inst_2) inst_3) :=
    fun {R Γ M : Type} [inst : CommRing R] [inst_1 : Group Γ] [inst_2 : AddCommGroup M]
        [inst_3 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@AddCommGroup.toAddCommMonoid M inst_2)]
        (ρ :
          @Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
            (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1)) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
        [inst_4 : TopologicalSpace Γ] ↦
      @Submodule.mk R (Γ → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
        (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)
        (@Pi.Function.module Γ R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
          (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
        (@AddSubmonoid.mk (Γ → M)
          (@AddMonoid.toAddZeroClass (Γ → M)
            (@AddCommMonoid.toAddMonoid (Γ → M)
              (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)))
          (@AddSubsemigroup.mk (Γ → M)
            (@AddZero.toAdd (Γ → M)
              (@AddZeroClass.toAddZero (Γ → M)
                (@AddMonoid.toAddZeroClass (Γ → M)
                  (@AddCommMonoid.toAddMonoid (Γ → M)
                    (@Pi.addCommMonoid Γ (fun (a : Γ) ↦ M) fun (i : Γ) ↦ @AddCommGroup.toAddCommMonoid M inst_2)))))
            (@Set.ofPred (Γ → M) fun (z : Γ → M) ↦
              And (@IsLocallyConstant Γ M inst_4 z)
                (∀ (g h : Γ),
                  @Eq M
                    (z
                      (@HMul.hMul Γ Γ Γ
                        (@instHMul Γ
                          (@MulOne.toMul Γ
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))))
                        g h))
                    (@HAdd.hAdd M M M
                      (@instHAdd M
                        (@AddCommMagma.toAdd M
                          (@AddCommSemigroup.toAddCommMagma M
                            (@AddCommMonoid.toAddCommSemigroup M (@AddCommGroup.toAddCommMonoid M inst_2)))))
                      (z g)

                      (@DFunLike.coe
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                          inst_3)
                        M (fun (x : M) ↦ M)
                        (@LinearMap.instFunLike R R M M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                          (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3 inst_3
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst)))))
                        (@DFunLike.coe
                          (@Representation R Γ M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                            (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))
                            (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)
                          Γ
                          (fun (x : Γ) ↦
                            @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                          (@MonoidHom.instFunLike Γ
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                              inst_3)
                            (@MulOneClass.toMulOne Γ
                              (@Monoid.toMulOneClass Γ (@DivInvMonoid.toMonoid Γ (@Group.toDivInvMonoid Γ inst_1))))
                            (@MulOneClass.toMulOne
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2) inst_3
                                inst_3)
                              (@MulZeroOneClass.toMulOneClass
                                (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                  (@RingHom.id R
                                    (@Semiring.toNonAssocSemiring R
                                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                  M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)
                                  inst_3 inst_3)
                                (@instMulZeroOneClassOfSemiring
                                  (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@RingHom.id R
                                      (@Semiring.toNonAssocSemiring R
                                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))))
                                    M M (@AddCommGroup.toAddCommMonoid M inst_2) (@AddCommGroup.toAddCommMonoid M inst_2)

                                    inst_3 inst_3)
                                  (@Module.End.instSemiring R M
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst))
                                    (@AddCommGroup.toAddCommMonoid M inst_2) inst_3)))))
                          ρ g)
                        (z h)))))
            (@UpperTheory.Reformulated.B.RootEquality.aux5 R Γ M inst inst_1 inst_2 inst_3 ρ inst_4))
          (@UpperTheory.Reformulated.B.RootEquality.aux6 R Γ M inst inst_1 inst_2 inst_3 ρ inst_4))
        (@UpperTheory.Reformulated.B.RootEquality.aux7 R Γ M inst inst_1 inst_2 inst_3 ρ inst_4)

noncomputable def UpperTheory.Reformulated.B.RootEquality.UnrCount :
    Nat → (D : Type) → [inst : Group D] → [TopologicalSpace D] → @Subgroup D inst → Prop :=
    fun (l : Nat) (D : Type) [inst : Group D] [inst_1 : TopologicalSpace D] (J : @Subgroup D inst) ↦
      ∀ (R M : Type) [inst_2 : CommRing R] [inst_3 : AddCommGroup M]
        [inst_4 :
          @_root_.Module R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
            (@AddCommGroup.toAddCommMonoid M inst_3)]
        [Finite M]
        (ρ :
          @Representation R D M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
            (@DivInvMonoid.toMonoid D (@Group.toDivInvMonoid D inst)) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4),
        @UpperTheory.Reformulated.B.RootEquality.LC R D M inst_2 inst inst_3 inst_4 ρ inst_1 →
          (∀ (m : M),
              @Eq M
                (@HSMul.hSMul Nat M M
                  (@instHSMul Nat M
                    (@NSMul.toSMul M
                      (@AddMonoid.toNSMul M
                        (@SubNegMonoid.toAddMonoid M (@AddGroup.toSubNegMonoid M (@AddCommGroup.toAddGroup M inst_3))))))
                  l m)
                (@OfNat.ofNat M (nat_lit 0)
                  (@Zero.toOfNat0 M
                    (@NegZeroClass.toZero M
                      (@SubNegZeroMonoid.toNegZeroClass M
                        (@SubtractionMonoid.toSubNegZeroMonoid M
                          (@SubtractionCommMonoid.toSubtractionMonoid M
                            (@AddCommGroup.toDivisionAddCommMonoid M inst_3)))))))) →
            (∀ (g : D),
                @Membership.mem D (@Subgroup D inst)
                    (@SetLike.instMembership (@Subgroup D inst) D (@Subgroup.instSetLike D inst)) J g →
                  @Eq
                    (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                      (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                      (@RingHom.id R
                        (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                      M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                    (@DFunLike.coe
                      (@Representation R D M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                        (@DivInvMonoid.toMonoid D (@Group.toDivInvMonoid D inst)) (@AddCommGroup.toAddCommMonoid M inst_3)
                        inst_4)
                      D
                      (fun (x : D) ↦
                        @LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                      (@MonoidHom.instFunLike D

                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        (@MulOneClass.toMulOne D
                          (@Monoid.toMulOneClass D (@DivInvMonoid.toMonoid D (@Group.toDivInvMonoid D inst))))
                        (@MulOneClass.toMulOne
                          (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@RingHom.id R
                              (@Semiring.toNonAssocSemiring R
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                            M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                            inst_4)
                          (@MulZeroOneClass.toMulOneClass
                            (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@RingHom.id R
                                (@Semiring.toNonAssocSemiring R
                                  (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                              M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                              inst_4)
                            (@instMulZeroOneClassOfSemiring
                              (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                                (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                                (@RingHom.id R
                                  (@Semiring.toNonAssocSemiring R
                                    (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                                M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                                inst_4)
                              (@Module.End.instSemiring R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))))
                      ρ g)
                    (@OfNat.ofNat
                      (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                        (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                        (@RingHom.id R
                          (@Semiring.toNonAssocSemiring R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                        M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4 inst_4)
                      (nat_lit 1)
                      (@One.toOfNat1
                        (@LinearMap R R (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@RingHom.id R
                            (@Semiring.toNonAssocSemiring R
                              (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))))
                          M M (@AddCommGroup.toAddCommMonoid M inst_3) (@AddCommGroup.toAddCommMonoid M inst_3) inst_4
                          inst_4)
                        (@Module.End.instOne R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))) →
              And
                (@Set.Finite (D → M)
                  (@Set.ofPred (D → M) fun (z : D → M) ↦
                    And
                      (@Membership.mem (D → M)
                        (@Submodule R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                          (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)

                          (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
                        (@SetLike.instMembership
                          (@Submodule R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                            (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
                          (D → M)
                          (@Submodule.setLike R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                            (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))
                        (@UpperTheory.Reformulated.B.RootEquality.Zl R D M inst_2 inst inst_3 inst_4 ρ inst_1) z)
                      (∀ (g : D),
                        @Membership.mem D (@Subgroup D inst)
                            (@SetLike.instMembership (@Subgroup D inst) D (@Subgroup.instSetLike D inst)) J g →
                          @Eq M (z g)
                            (@OfNat.ofNat M (nat_lit 0)
                              (@Zero.toOfNat0 M
                                (@NegZeroClass.toZero M
                                  (@SubNegZeroMonoid.toNegZeroClass M
                                    (@SubtractionMonoid.toSubNegZeroMonoid M
                                      (@SubtractionCommMonoid.toSubtractionMonoid M
                                        (@AddCommGroup.toDivisionAddCommMonoid M inst_3))))))))))
                (@Eq Nat
                  (@Set.ncard (D → M)
                    (@Set.ofPred (D → M) fun (z : D → M) ↦
                      And
                        (@Membership.mem (D → M)
                          (@Submodule R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                            (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                            (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
                          (@SetLike.instMembership
                            (@Submodule R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                              (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4))
                            (D → M)
                            (@Submodule.setLike R (D → M) (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                              (@Pi.addCommMonoid D (fun (a : D) ↦ M) fun (i : D) ↦ @AddCommGroup.toAddCommMonoid M inst_3)
                              (@Pi.Function.module D R M (@CommSemiring.toSemiring R (@CommRing.toCommSemiring R inst_2))
                                (@AddCommGroup.toAddCommMonoid M inst_3) inst_4)))
                          (@UpperTheory.Reformulated.B.RootEquality.Zl R D M inst_2 inst inst_3 inst_4 ρ inst_1) z)
                        (∀ (g : D),
                          @Membership.mem D (@Subgroup D inst)
                              (@SetLike.instMembership (@Subgroup D inst) D (@Subgroup.instSetLike D inst)) J g →
                            @Eq M (z g)
                              (@OfNat.ofNat M (nat_lit 0)
                                (@Zero.toOfNat0 M
                                  (@NegZeroClass.toZero M
                                    (@SubNegZeroMonoid.toNegZeroClass M
                                      (@SubtractionMonoid.toSubNegZeroMonoid M
                                        (@SubtractionCommMonoid.toSubtractionMonoid M
                                          (@AddCommGroup.toDivisionAddCommMonoid M inst_3))))))))))
                  (Nat.card M))

noncomputable def UpperTheory.Reformulated.B.RootEquality.Inertia.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →

        [inst : Field F] →
          [inst_1 : Field Ω] →
            [inst_2 :
                @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))] →
              @ValuationSubring Ω inst_1 → Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) :=
    fun {F : Type u_1} {Ω : Type u_2} [inst : Field F] [inst_1 : Field Ω]
        [inst_2 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))]
        (A : @ValuationSubring Ω inst_1) ↦
      @Set.ofPred (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) fun (σ : @UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) ↦
        And
          (@Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
            (@Subgroup
              (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                inst_2)
              (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2))
            (@SetLike.instMembership
              (@Subgroup
                (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                  inst_2)
                (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2))
              (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                inst_2)
              (@Subgroup.instSetLike
                (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                  inst_2)
                (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2)))
            (@ValuationSubring.decompositionSubgroup F Ω inst inst_1 inst_2 A) σ)
          (∀ (x : Ω),
            @LE.le (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@Preorder.toLE (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@PartialOrder.toPreorder (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@SemilatticeInf.toPartialOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@Lattice.toSemilatticeInf (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DistribLattice.toLattice (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@instDistribLatticeOfLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommMonoidWithZero.toLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                                (@ValuationSubring.ValueGroup Ω inst_1 A)
                                (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))
                (@DFunLike.coe
                  (@Valuation Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                      (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))
                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))
                  Ω (fun (x : Ω) ↦ @ValuationSubring.ValueGroup Ω inst_1 A)

                  (@Valuation.instFunLike Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1))
                    (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                      (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))
                  (@ValuationSubring.valuation Ω inst_1 A) x)
                (@OfNat.ofNat (@ValuationSubring.ValueGroup Ω inst_1 A) (nat_lit 1)
                  (@One.toOfNat1 (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@InvOneClass.toOne (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DivInvOneMonoid.toInvOneClass (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DivisionMonoid.toDivInvOneMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@DivisionCommMonoid.toDivisionMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@CommGroupWithZero.toDivisionCommMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@LinearOrderedCommGroupWithZero.toCommGroupWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                                (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))))))))) →
              @LT.lt (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@Preorder.toLT (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@PartialOrder.toPreorder (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@SemilatticeInf.toPartialOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@Lattice.toSemilatticeInf (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DistribLattice.toLattice (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@instDistribLatticeOfLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommMonoidWithZero.toLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                                (@ValuationSubring.ValueGroup Ω inst_1 A)
                                (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))
                (@DFunLike.coe
                  (@Valuation Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                      (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))
                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))
                  Ω (fun (x : Ω) ↦ @ValuationSubring.ValueGroup Ω inst_1 A)
                  (@Valuation.instFunLike Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1))
                    (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                      (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))
                  (@ValuationSubring.valuation Ω inst_1 A)
                  (@HSub.hSub Ω Ω Ω
                    (@instHSub Ω
                      (@SubNegMonoid.toSub Ω
                        (@AddGroup.toSubNegMonoid Ω
                          (@AddGroupWithOne.toAddGroup Ω
                            (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))))))
                    (@DFunLike.coe (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) Ω (fun (x : Ω) ↦ Ω)
                      (@AlgEquiv.instFunLike F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                        inst_2 inst_2)
                      σ x)
                    x))
                (@OfNat.ofNat (@ValuationSubring.ValueGroup Ω inst_1 A) (nat_lit 1)
                  (@One.toOfNat1 (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@InvOneClass.toOne (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DivInvOneMonoid.toInvOneClass (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DivisionMonoid.toDivInvOneMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@DivisionCommMonoid.toDivisionMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@CommGroupWithZero.toDivisionCommMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@LinearOrderedCommGroupWithZero.toCommGroupWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)

                                (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))))))))))

/- English proof (translation)
Introduce `F Ω _ _ _ _ A σ τ hσ hτ`. Use `⟨mul_mem hσ.1 hτ.1, fun x hx ↦ ?_⟩` and prove the remaining obligations. Establish `h1` using `hτ.2 x hx`. Establish `h2 : A.valuation (τ x) ≤ 1`. Establish `: τ x = (τ x - x) + x` using `by ring`.

Rewrite using `[this]`. Conclude with `Valuation.map_add_le _ h1.le hx`. Establish `h3` using `hσ.2 _ h2`. Establish `: (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x)`. Rewrite using `[AlgEquiv.mul_apply]`.

Expand and normalize the polynomial expressions, which then agree. Rewrite using `[this]`. Conclude with `Valuation.map_add_lt _ h3 h1`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.aux11.{u_1, u_2} :
    ∀ {F : Type u_1} {Ω : Type u_2} [inst : Field F] [@NumberField F inst] [inst_2 : Field Ω]
      [inst_3 :
        @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))]
      (A : @ValuationSubring Ω inst_2) {σ τ : @UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3},
      @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
          (@Set.instMembership (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
          (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A) σ →
        @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
            (@Set.instMembership (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
            (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A) τ →
          @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
            (@Set.instMembership (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
            (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A)
            (@HMul.hMul (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (@instHMul (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (@MulOne.toMul (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@MulOneClass.toMulOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@Monoid.toMulOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@DivInvMonoid.toMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                        (@Group.toDivInvMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                          (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                            inst_3)))))))
              σ τ) := by
  intro F Ω _ _ _ _ A σ τ hσ hτ
  refine ⟨mul_mem hσ.1 hτ.1, fun x hx ↦ ?_⟩
  have h1 := hτ.2 x hx
  have h2 : A.valuation (τ x) ≤ 1 := by
    have : τ x = (τ x - x) + x := by ring
    rw [this]
    exact Valuation.map_add_le _ h1.le hx
  have h3 := hσ.2 _ h2
  have : (σ * τ) x - x = (σ (τ x) - τ x) + (τ x - x) := by
    rw [AlgEquiv.mul_apply]; ring
  rw [this]
  exact Valuation.map_add_lt _ h3 h1

/- English proof (translation)
Conclude with `fun A ↦ ⟨one_mem _, fun x _ ↦ by simp⟩`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.aux12.{u_1, u_2} :
    ∀ {F : Type u_2} {Ω : Type u_1} [inst : Field F] [inst_1 : Field Ω]
      [inst_2 :
        @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))]
      (A : @ValuationSubring Ω inst_1),
      And
        (@Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
          (@Subgroup
            (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
              inst_2)
            (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2))
          (@SetLike.instMembership
            (@Subgroup
              (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                inst_2)
              (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2))
            (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
              inst_2)
            (@Subgroup.instSetLike
              (@AlgEquiv F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))

                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2
                inst_2)
              (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1))) inst_2)))
          (@ValuationSubring.decompositionSubgroup F Ω inst inst_1 inst_2 A)
          (@OfNat.ofNat (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) (nat_lit 1)
            (@One.toOfNat1 (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
              (@MulOne.toOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                (@MulOneClass.toMulOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                  (@Monoid.toMulOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                    (@DivInvMonoid.toMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                      (@Group.toDivInvMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                        (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                          inst_2)))))))))
        (∀ (x : Ω),
          @LE.le (@ValuationSubring.ValueGroup Ω inst_1 A)
              (@Preorder.toLE (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@PartialOrder.toPreorder (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@SemilatticeInf.toPartialOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@Lattice.toSemilatticeInf (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DistribLattice.toLattice (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@instDistribLatticeOfLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@LinearOrderedCommMonoidWithZero.toLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                              (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))
              (@DFunLike.coe
                (@Valuation Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                    (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))
                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))
                Ω (fun (x : Ω) ↦ @ValuationSubring.ValueGroup Ω inst_1 A)
                (@Valuation.instFunLike Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1))
                  (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                    (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))
                (@ValuationSubring.valuation Ω inst_1 A) x)
              (@OfNat.ofNat (@ValuationSubring.ValueGroup Ω inst_1 A) (nat_lit 1)
                (@One.toOfNat1 (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@InvOneClass.toOne (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DivInvOneMonoid.toInvOneClass (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DivisionMonoid.toDivInvOneMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DivisionCommMonoid.toDivisionMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@CommGroupWithZero.toDivisionCommMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommGroupWithZero.toCommGroupWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))))))))) →
            @LT.lt (@ValuationSubring.ValueGroup Ω inst_1 A)
              (@Preorder.toLT (@ValuationSubring.ValueGroup Ω inst_1 A)
                (@PartialOrder.toPreorder (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@SemilatticeInf.toPartialOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@Lattice.toSemilatticeInf (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DistribLattice.toLattice (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@instDistribLatticeOfLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@LinearOrderedCommMonoidWithZero.toLinearOrder (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                              (@ValuationSubring.ValueGroup Ω inst_1 A)

                              (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))
              (@DFunLike.coe
                (@Valuation Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                    (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A))
                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))
                Ω (fun (x : Ω) ↦ @ValuationSubring.ValueGroup Ω inst_1 A)
                (@Valuation.instFunLike Ω (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1))
                  (@LinearOrderedCommGroupWithZero.toLinearOrderedCommMonoidWithZero
                    (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))
                (@ValuationSubring.valuation Ω inst_1 A)
                (@HSub.hSub Ω Ω Ω
                  (@instHSub Ω
                    (@SubNegMonoid.toSub Ω
                      (@AddGroup.toSubNegMonoid Ω
                        (@AddGroupWithOne.toAddGroup Ω
                          (@Ring.toAddGroupWithOne Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_1)))))))
                  (@DFunLike.coe (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) Ω (fun (x : Ω) ↦ Ω)
                    (@AlgEquiv.instFunLike F Ω Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                      inst_2 inst_2)
                    (@OfNat.ofNat (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2) (nat_lit 1)
                      (@One.toOfNat1 (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                        (@MulOne.toOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                          (@MulOneClass.toMulOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                            (@Monoid.toMulOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                              (@DivInvMonoid.toMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                                (@Group.toDivInvMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_1 inst_2)
                                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                                    (@DivisionSemiring.toSemiring Ω
                                      (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_1)))
                                    inst_2))))))))
                    x)
                  x))
              (@OfNat.ofNat (@ValuationSubring.ValueGroup Ω inst_1 A) (nat_lit 1)
                (@One.toOfNat1 (@ValuationSubring.ValueGroup Ω inst_1 A)
                  (@InvOneClass.toOne (@ValuationSubring.ValueGroup Ω inst_1 A)
                    (@DivInvOneMonoid.toInvOneClass (@ValuationSubring.ValueGroup Ω inst_1 A)
                      (@DivisionMonoid.toDivInvOneMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                        (@DivisionCommMonoid.toDivisionMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                          (@CommGroupWithZero.toDivisionCommMonoid (@ValuationSubring.ValueGroup Ω inst_1 A)
                            (@LinearOrderedCommGroupWithZero.toCommGroupWithZero (@ValuationSubring.ValueGroup Ω inst_1 A)
                              (@ValuationSubring.instLinearOrderedCommGroupWithZeroValueGroup Ω inst_1 A)))))))))) := by
  exact fun A ↦ ⟨one_mem _, fun x _ ↦ by simp⟩

/- English proof (translation)
Introduce `F Ω _ _ _ _ A σ hσ`. Establish `hi` using `inv_mem hσ.1`. Use `⟨hi, fun x hx ↦ ?_⟩` and prove the remaining obligations. Establish `h2 : A.valuation (σ⁻¹ x) ≤ 1`. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`.

Establish `h` using `ValuationSubring.smul_mem_pointwise_smul σ⁻¹ x A hx`. Use `open scoped Pointwise in rw [MulAction.mem_stabilizer_iff.1 hi] at h`. Conclude with `h`. Establish `h3` using `hσ.2 _ h2`. Establish `: σ (σ⁻¹ x) = x` using `σ.apply_symm_apply x`.

Rewrite `h3` using `[this]`. Rewrite using `[Valuation.map_sub_swap]` and apply the resulting hypothesis.
-/
theorem UpperTheory.Reformulated.B.RootEquality.algebra_smulCommClass_complex.{u_1, u_2} :
    ∀ {F : Type u_1} {Ω : Type u_2} [inst : Field F] [@NumberField F inst] [inst_2 : Field Ω]
      [inst_3 :
        @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))]
      (A : @ValuationSubring Ω inst_2) {σ : @UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3},
      @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
          (@Set.instMembership (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
          (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A) σ →
        @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) (Set (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))
          (@Set.instMembership (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3))

          (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A)
          (@Inv.inv (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
            (@InvOneClass.toInv (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (@DivInvOneMonoid.toInvOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (@DivisionMonoid.toDivInvOneMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@Group.toDivisionMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)))))
            σ) := by
  intro F Ω _ _ _ _ A σ hσ
  have hi := inv_mem hσ.1
  refine ⟨hi, fun x hx ↦ ?_⟩
  have h2 : A.valuation (σ⁻¹ x) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    have h := ValuationSubring.smul_mem_pointwise_smul σ⁻¹ x A hx
    open scoped Pointwise in rw [MulAction.mem_stabilizer_iff.1 hi] at h
    exact h
  have h3 := hσ.2 _ h2
  have : σ (σ⁻¹ x) = x := σ.apply_symm_apply x
  rw [this] at h3
  rwa [Valuation.map_sub_swap]

noncomputable def UpperTheory.Reformulated.B.RootEquality.Ine.{u_1, u_2} :
    {F : Type u_1} →
      {Ω : Type u_2} →
        [inst : Field F] →
          [@NumberField F inst] →
            [inst_2 : Field Ω] →
              [inst_3 :
                  @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))] →
                @ValuationSubring Ω inst_2 →
                  @Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3) :=
    fun {F : Type u_1} {Ω : Type u_2} [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field Ω]
        [inst_3 :
          @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))]
        (A : @ValuationSubring Ω inst_2) ↦
      @Subgroup.mk (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
        (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
        (@Submonoid.mk (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
          (@Monoid.toMulOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
            (@DivInvMonoid.toMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (@Group.toDivInvMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                  inst_3))))
          (@Subsemigroup.mk (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
            (@MulOne.toMul (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (@MulOneClass.toMulOne (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (@Monoid.toMulOneClass (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@DivInvMonoid.toMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@Group.toDivInvMonoid (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                        inst_3))))))
            (@UpperTheory.Reformulated.B.RootEquality.Inertia F Ω inst inst_2 inst_3 A) (@UpperTheory.Reformulated.B.RootEquality.aux11 F Ω inst inst_1 inst_2 inst_3 A))
          (@UpperTheory.Reformulated.B.RootEquality.aux12 F Ω inst inst_2 inst_3 A))
        (@UpperTheory.Reformulated.B.RootEquality.algebra_smulCommClass_complex F Ω inst inst_1 inst_2 inst_3 A)

namespace UpperTheory.Reformulated.B.RootEquality

section Grp

variable {R D M : Type} [CommRing R] [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
  [AddCommGroup M] [Module R M] (ρ : Representation R D M)

private def ZK (K : Subgroup D) : Submodule R (D → M) where
  carrier := {z | z ∈ Zl ρ ∧ ∀ g ∈ K, z g = 0}
  add_mem' hx hy := ⟨add_mem hx.1 hy.1, fun g hg ↦ by simp [hx.2 g hg, hy.2 g hg]⟩
  zero_mem' := ⟨zero_mem _, fun _ _ ↦ rfl⟩
  smul_mem' c x hx := ⟨Submodule.smul_mem _ c hx.1, fun g hg ↦ by simp [hx.2 g hg]⟩

private def Fix (K : Subgroup D) : Submodule R M where
  carrier := {m | ∀ g ∈ K, ρ g m = m}
  add_mem' hx hy := fun g hg ↦ by simp [hx g hg, hy g hg]
  zero_mem' := fun _ _ ↦ by simp
  smul_mem' c x hx := fun g hg ↦ by simp [hx g hg]

private def cob : M →ₗ[R] (D → M) where
  toFun b := fun g ↦ ρ g b - b
  map_add' a b := by ext g; simp only [map_add, Pi.add_apply]; abel
  map_smul' c b := by ext g; simp [smul_sub]

omit [TopologicalSpace D] [IsTopologicalGroup D] in
/- English proof (translation)
Introduce `t ht`. Establish `h` using `hm _ (hI.conj_mem' t ht g)`. Establish `e : t * g = g * (g⁻¹ * t * g)` using `by group`. Rewrite using `[← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]`.
-/
private theorem fix_stable (I : Subgroup D) [hI : I.Normal] (g : D) {m : M} (hm : m ∈ Fix ρ I) :
    ρ g m ∈ Fix ρ I := by
  intro t ht
  have h := hm _ (hI.conj_mem' t ht g)
  have e : t * g = g * (g⁻¹ * t * g) := by group
  rw [← Module.End.mul_apply, ← map_mul, e, map_mul, Module.End.mul_apply, h]

omit [IsTopologicalGroup D] in
/- English proof (translation)
Introduce `t ht`. Establish `h1` using `hz.1.2 t g`. Establish `h2` using `hz.1.2 g (g⁻¹ * t * g)`. Establish `e : g * (g⁻¹ * t * g) = t * g` using `by group`. Rewrite `h2` using `[e, hz.2 _ (hI.conj_mem' t ht g), map_zero, add_zero]`.

Rewrite `h1` using `[hz.2 t ht, zero_add]`. Rewrite using `[← h1, h2]`.
-/
private theorem val_mem_fix (I : Subgroup D) [hI : I.Normal] {z : D → M} (hz : z ∈ ZK ρ I)
    (g : D) : z g ∈ Fix ρ I := by
  intro t ht
  have h1 := hz.1.2 t g
  have h2 := hz.1.2 g (g⁻¹ * t * g)
  have e : g * (g⁻¹ * t * g) = t * g := by group
  rw [e, hz.2 _ (hI.conj_mem' t ht g), map_zero, add_zero] at h2
  rw [hz.2 t ht, zero_add] at h1
  rw [← h1, h2]

omit [IsTopologicalGroup D] in
/- English proof (translation)
Set `U : Subgroup D` to `{ carrier := {g | z g = 0} mul_mem' := fun {a b} ha hb ↦ by`. Use `hz.1.2 a b` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq] at ha hb ⊢`. Rewrite using `[this, ha, hb, map_zero, add_zero]`. Use the proof step `one_mem' := hz.2 1 (one_mem _)`.

Use the proof step `inv_mem' := fun {a} ha ↦ by`. Use `hz.1.2 a⁻¹ a` as an intermediate fact. Simplify using `only [Set.mem_setOf_eq] at ha ⊢`. Rewrite `this` using `[inv_mul_cancel, hz.2 1 (one_mem _), ha, map_zero, add_zero]`. Conclude with `this.symm }`.

Establish `hU : U = ⊤` using `ha U (hz.1.1.isOpen_fiber 0) (fun g hg ↦ hz.2 g hg) h0`. Use extensionality with `g`. Establish `: g ∈ U` using `hU ▸ Subgroup.mem_top g`. Conclude with `this`.
-/
private theorem eq_zero_of_dense (I : Subgroup D) (φ : D)
    (ha : ∀ U : Subgroup D, IsOpen (U : Set D) → I ≤ U → φ ∈ U → U = ⊤)
    {z : D → M} (hz : z ∈ ZK ρ I) (h0 : z φ = 0) : z = 0 := by
  let U : Subgroup D :=
    { carrier := {g | z g = 0}
      mul_mem' := fun {a b} ha hb ↦ by
        have := hz.1.2 a b
        simp only [Set.mem_setOf_eq] at ha hb ⊢
        rw [this, ha, hb, map_zero, add_zero]
      one_mem' := hz.2 1 (one_mem _)
      inv_mem' := fun {a} ha ↦ by
        have := hz.1.2 a⁻¹ a
        simp only [Set.mem_setOf_eq] at ha ⊢
        rw [inv_mul_cancel, hz.2 1 (one_mem _), ha, map_zero, add_zero] at this
        exact this.symm }
  have hU : U = ⊤ := ha U (hz.1.1.isOpen_fiber 0) (fun g hg ↦ hz.2 g hg) h0
  ext g
  have : g ∈ U := hU ▸ Subgroup.mem_top g
  exact this

/- English proof (translation)
Set `T : Equiv.Perm M` to `{ toFun := fun y ↦ m + ρ φ y invFun := fun y ↦ ρ φ⁻¹ (y - m) left_inv := fun y ↦ by simp right_inv := fun y ↦ by simp }`. Take `⟨V, hVn, hVo, hIV, hV⟩` from `hc (orderOf T) (orderOf_pos T)`. Establish `hgen : ∀ x : D ⧸ V, x ∈ Subgroup.zpowers (φ : D ⧸ V)`. Establish `h` using `ha ((Subgroup.zpowers (φ : D ⧸ V)).comap (QuotientGroup.mk' V)) (Subgroup.isOpen_mono (H₁ := V) (fun g hg ↦ by`. Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]`.

Conclude with `one_mem _) hVo)`. Use the proof step `(fun g hg ↦ by`. Rewrite using `[Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 (hIV hg)]`. Conclude with `one_mem _)`. Use the proof step `(Subgroup.mem_zpowers _)`.

Introduce `x`. Take `⟨g, rfl⟩` from `QuotientGroup.mk_surjective x`. Establish `: g ∈ (Subgroup.zpowers (φ : D ⧸ V)).comap (QuotientGroup.mk' V)` using `h ▸ Subgroup.mem_top g`. Conclude with `this`. Establish `hdvd : orderOf T ∣ orderOf (φ : D ⧸ V)`.

Apply `hV` to reduce the goal to its premises. Rewrite using `[← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]`. Set `ψ : D →* Equiv.Perm M` to `(monoidHomOfForallMemZpowers hgen hdvd).comp (QuotientGroup.mk' V)`. Establish `hψφ : ψ φ = T` using `monoidHomOfForallMemZpowers_apply_gen hgen hdvd`. Establish `hψV : ∀ g ∈ V, ψ g = 1` using `fun g hg ↦ by`.

Simplify using `only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg, map_one]`. Set `U : Subgroup D` to `{ carrier := {g | ψ g 0 ∈ Fix ρ I ∧ ∀ y ∈ Fix ρ I, ψ g y = ψ g 0 + ρ g y} mul_mem' := fun {a b} ha hb ↦ by`. Establish `h0 : ψ (a * b) 0 = ψ a 0 + ρ a (ψ b 0)`. Rewrite using `[map_mul, Equiv.Perm.mul_apply, ha.2 _ hb.1]`. Use `⟨h0 ▸ add_mem ha.1 (fix_stable ρ I a hb.1), fun y hy ↦ ?_⟩` and prove the remaining obligations.

Rewrite using `[h0, map_mul, Equiv.Perm.mul_apply, hb.2 y hy, ha.2 _ (add_mem hb.1 (fix_stable ρ I b hy)), map_add, map_mul, Module.End.mul_apply, add_assoc]`. Use the proof step `one_mem' := by simp`. Use the proof step `inv_mem' := fun {a} ha ↦ by`. Establish `key : ∀ y ∈ Fix ρ I, ψ a⁻¹ y = ρ a⁻¹ (y - ψ a 0)` using `fun y hy ↦ by`. Rewrite using `[map_inv, Equiv.Perm.inv_eq_iff_eq, ha.2 _ (fix_stable ρ I a⁻¹ (sub_mem hy ha.1))]`.

Simplify using the standard rewrite rules. Use `⟨key 0 (zero_mem _) ▸ fix_stable ρ I a⁻¹ (sub_mem (zero_mem _) ha.1), fun y hy ↦ ?_⟩` and prove the remaining obligations. Rewrite using `[key y hy, key 0 (zero_mem _), map_sub, map_sub, map_zero (ρ a⁻¹)]`. Use `abel }`. Establish `hUo : IsOpen (U : Set D)`.

Apply `Subgroup.isOpen_of_mem_nhds (g := 1)` to reduce the goal to its premises. Establish `h1 : (V : Set D) ∩ ⋂ y : M, {g | ρ g y = y} ∈ nhds (1 : D)`. Use `IsOpen.mem_nhds (hVo.inter (isOpen_iInter_of_finite fun y ↦ (hρ y).isOpen_fiber y)) ?_` and prove the remaining obligations. Conclude with `⟨one_mem V, by simp⟩`. Use `Filter.mem_of_superset h1 fun g hg ↦ ?_` and prove the remaining obligations.

Establish `h2 : ∀ y, ρ g y = y` using `by simpa using hg.2`. Establish `h3` using `hψV g hg.1`. Conclude with `⟨by simp [h3], fun y _ ↦ by simp [h3, h2]⟩`. Establish `hU : U = ⊤` using `ha U hUo (fun g hg ↦ ⟨by simp [hψV g (hIV hg)], fun y hy ↦ by simp [hψV g (hIV hg), hy g hg]⟩) ⟨by simpa [hψφ, T] using hm, fun y _ ↦ by simp [hψφ, T]⟩`. Establish `hall : ∀ g, g ∈ U` using `fun g ↦ hU ▸ Subgroup.mem_top g`.

Use `⟨fun g ↦ ψ g 0, ⟨⟨?_, fun g h ↦ ?_⟩, fun g hg ↦ by simp [hψV g (hIV hg)]⟩, by simp [hψφ, T]⟩` and prove the remaining obligations. Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g`. Establish `h1 : (fun x ↦ g⁻¹ * x) ⁻¹' (V : Set D) ∈ nhds g` using `(hVo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)`. Use `filter_upwards [h1] with x hx`.

Establish `h2 : x = g * (g⁻¹ * x)` using `by group`. Rewrite using `[h2, map_mul, hψV _ hx, mul_one]`. Use `show ψ (g * h) 0 = _`. Rewrite using `[map_mul, Equiv.Perm.mul_apply, (hall g).2 _ (hall h).1]`.
-/
private theorem exists_cocycle [Finite M] (hρ : LC ρ) (I : Subgroup D) [hI : I.Normal] (φ : D)
    (ha : ∀ U : Subgroup D, IsOpen (U : Set D) → I ≤ U → φ ∈ U → U = ⊤)
    (hc : ∀ n : ℕ, 0 < n → ∃ V : Subgroup D, V.Normal ∧ IsOpen (V : Set D) ∧ I ≤ V ∧
      ∀ j : ℕ, φ ^ j ∈ V → n ∣ j)
    {m : M} (hm : m ∈ Fix ρ I) : ∃ z ∈ ZK ρ I, z φ = m := by
  let T : Equiv.Perm M :=
    { toFun := fun y ↦ m + ρ φ y
      invFun := fun y ↦ ρ φ⁻¹ (y - m)
      left_inv := fun y ↦ by simp
      right_inv := fun y ↦ by simp }
  obtain ⟨V, hVn, hVo, hIV, hV⟩ := hc (orderOf T) (orderOf_pos T)
  have hgen : ∀ x : D ⧸ V, x ∈ Subgroup.zpowers (φ : D ⧸ V) := by
    have h := ha ((Subgroup.zpowers (φ : D ⧸ V)).comap (QuotientGroup.mk' V))
      (Subgroup.isOpen_mono (H₁ := V) (fun g hg ↦ by
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 hg]
        exact one_mem _) hVo)
      (fun g hg ↦ by
        rw [Subgroup.mem_comap, QuotientGroup.mk'_apply, (QuotientGroup.eq_one_iff g).2 (hIV hg)]
        exact one_mem _)
      (Subgroup.mem_zpowers _)
    intro x
    obtain ⟨g, rfl⟩ := QuotientGroup.mk_surjective x
    have : g ∈ (Subgroup.zpowers (φ : D ⧸ V)).comap (QuotientGroup.mk' V) :=
      h ▸ Subgroup.mem_top g
    exact this
  have hdvd : orderOf T ∣ orderOf (φ : D ⧸ V) := by
    apply hV
    rw [← QuotientGroup.eq_one_iff, QuotientGroup.mk_pow, pow_orderOf_eq_one]
  let ψ : D →* Equiv.Perm M := (monoidHomOfForallMemZpowers hgen hdvd).comp (QuotientGroup.mk' V)
  have hψφ : ψ φ = T := monoidHomOfForallMemZpowers_apply_gen hgen hdvd
  have hψV : ∀ g ∈ V, ψ g = 1 := fun g hg ↦ by
    simp only [ψ, MonoidHom.comp_apply, QuotientGroup.mk'_apply,
      (QuotientGroup.eq_one_iff g).2 hg, map_one]
  let U : Subgroup D :=
    { carrier := {g | ψ g 0 ∈ Fix ρ I ∧ ∀ y ∈ Fix ρ I, ψ g y = ψ g 0 + ρ g y}
      mul_mem' := fun {a b} ha hb ↦ by
        have h0 : ψ (a * b) 0 = ψ a 0 + ρ a (ψ b 0) := by
          rw [map_mul, Equiv.Perm.mul_apply, ha.2 _ hb.1]
        refine ⟨h0 ▸ add_mem ha.1 (fix_stable ρ I a hb.1), fun y hy ↦ ?_⟩
        rw [h0, map_mul, Equiv.Perm.mul_apply, hb.2 y hy,
          ha.2 _ (add_mem hb.1 (fix_stable ρ I b hy)), map_add, map_mul, Module.End.mul_apply,
          add_assoc]
      one_mem' := by simp
      inv_mem' := fun {a} ha ↦ by
        have key : ∀ y ∈ Fix ρ I, ψ a⁻¹ y = ρ a⁻¹ (y - ψ a 0) := fun y hy ↦ by
          rw [map_inv, Equiv.Perm.inv_eq_iff_eq,
            ha.2 _ (fix_stable ρ I a⁻¹ (sub_mem hy ha.1))]
          simp
        refine ⟨key 0 (zero_mem _) ▸ fix_stable ρ I a⁻¹ (sub_mem (zero_mem _) ha.1),
          fun y hy ↦ ?_⟩
        rw [key y hy, key 0 (zero_mem _), map_sub, map_sub, map_zero (ρ a⁻¹)]
        abel }
  have hUo : IsOpen (U : Set D) := by
    apply Subgroup.isOpen_of_mem_nhds (g := 1)
    have h1 : (V : Set D) ∩ ⋂ y : M, {g | ρ g y = y} ∈ nhds (1 : D) := by
      refine IsOpen.mem_nhds (hVo.inter (isOpen_iInter_of_finite fun y ↦ (hρ y).isOpen_fiber y)) ?_
      exact ⟨one_mem V, by simp⟩
    refine Filter.mem_of_superset h1 fun g hg ↦ ?_
    have h2 : ∀ y, ρ g y = y := by simpa using hg.2
    have h3 := hψV g hg.1
    exact ⟨by simp [h3], fun y _ ↦ by simp [h3, h2]⟩
  have hU : U = ⊤ := ha U hUo
    (fun g hg ↦ ⟨by simp [hψV g (hIV hg)], fun y hy ↦ by simp [hψV g (hIV hg), hy g hg]⟩)
    ⟨by simpa [hψφ, T] using hm, fun y _ ↦ by simp [hψφ, T]⟩
  have hall : ∀ g, g ∈ U := fun g ↦ hU ▸ Subgroup.mem_top g
  refine ⟨fun g ↦ ψ g 0, ⟨⟨?_, fun g h ↦ ?_⟩, fun g hg ↦ by simp [hψV g (hIV hg)]⟩,
    by simp [hψφ, T]⟩
  · rw [IsLocallyConstant.iff_eventually_eq]
    intro g
    have h1 : (fun x ↦ g⁻¹ * x) ⁻¹' (V : Set D) ∈ nhds g :=
      (hVo.preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
    filter_upwards [h1] with x hx
    have h2 : x = g * (g⁻¹ * x) := by group
    rw [h2, map_mul, hψV _ hx, mul_one]
  · show ψ (g * h) 0 = _
    rw [map_mul, Equiv.Perm.mul_apply, (hall g).2 _ (hall h).1]

end Grp

/- English proof (translation)
Introduce `R M _ _ _ _ ρ hρ hM hJ`. Set `ev : ZK ρ I → Fix ρ I` to `fun z ↦ ⟨z.1 φ, val_mem_fix ρ I z.2 φ⟩`. Establish `hev : Function.Bijective ev`. Use `⟨fun z w h ↦ ?_, fun m ↦ ?_⟩` and prove the remaining obligations. Establish `h1 : z.1 φ = w.1 φ` using `congrArg Subtype.val h`.

Use `eq_zero_of_dense ρ I φ ha (sub_mem z.2 w.2) (by simp [h1])` as an intermediate fact. Conclude with `Subtype.ext (sub_eq_zero.1 this)`. Take `⟨z, hz, h⟩` from `exists_cocycle ρ hρ I φ ha hc m.2`. Conclude with `⟨⟨z, hz⟩, Subtype.ext h⟩`. Establish `hfin : Finite (ZK ρ I)` using `Finite.of_injective _ hev.1`.

Establish `hcard : Nat.card (ZK ρ I) = Nat.card (Fix ρ I)` using `Nat.card_eq_of_bijective _ hev`. Establish `hcob : ∀ b, cob ρ b ∈ Zl ρ` using `fun b ↦ ⟨(hρ b).comp (fun y ↦ y - b), fun g h ↦ by simp [cob]⟩`. Set `Φ : (ZK ρ I × M) →ₗ[R] (D → M)` to `(ZK ρ I).subtype.coprod (cob ρ)`. Establish `hrange : LinearMap.range Φ = ZK ρ (I ⊓ χ.ker)`. Apply `le_antisymm` to reduce the goal to its premises.

Introduce and unpack `_ ⟨⟨w, b⟩, rfl⟩`. Use `⟨add_mem w.2.1 (hcob b), fun g hg ↦ ?_⟩` and prove the remaining obligations. Simplify using `[Φ, cob, w.2.2 g hg.1, hJ g hg]`. Introduce `z hz`. Take `⟨b, hb⟩` from `UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime ρ I.subtype (χ.comp I.subtype) hl hM z hz.1.2 (fun u hu ↦ hz.2 u ⟨u.2, hu⟩)`.

Use `⟨(⟨z - cob ρ b, sub_mem hz.1 (hcob b), fun g hg ↦ ?_⟩, b), by simp [Φ]⟩` and prove the remaining obligations. Use `hb ⟨g, hg⟩` as an intermediate fact. Simplify using `only [Subgroup.coe_subtype] at this`. Simplify using `[cob, this]`. Establish `hker : Nat.card (LinearMap.ker Φ) = Nat.card (Fix ρ I)`.

Establish `hmem : ∀ p : LinearMap.ker Φ, p.1.1.1 = - cob ρ p.1.2` using `fun p ↦ eq_neg_of_add_eq_zero_left p.2`. Use `Nat.card_eq_of_bijective (fun p ↦ ⟨p.1.2, fun g hg ↦ ?_⟩) ⟨fun p q h ↦ ?_, fun b ↦ ?_⟩` and prove the remaining obligations. Establish `h1` using `p.1.1.2.2 g hg`. Rewrite `h1` using `[hmem p]`. Establish `h2 : -(ρ g p.1.2 - p.1.2) = 0` using `h1`.

Conclude with `sub_eq_zero.1 (neg_eq_zero.1 h2)`. Establish `h1 : p.1.2 = q.1.2` using `congrArg Subtype.val h`. Conclude with `Subtype.ext (Prod.ext (Subtype.ext (by rw [hmem p, hmem q, h1])) h1)`. Use `⟨⟨(⟨- cob ρ b, neg_mem (hcob b), fun g hg ↦ ?_⟩, b), by simp [Φ]⟩, rfl⟩` and prove the remaining obligations. Simplify using `[cob, b.2 g hg]`.

Establish `h1` using `Submodule.card_eq_card_quotient_mul_card (LinearMap.ker Φ)`. Rewrite `h1` using `[Nat.card_congr Φ.quotKerEquivRange.toEquiv, hrange, hker, Nat.card_prod, hcard]`. Establish `h2 : Nat.card (ZK ρ (I ⊓ χ.ker)) = Nat.card M` using `(Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm`. Establish `h3 : Finite (ZK ρ (I ⊓ χ.ker))` using `Nat.finite_of_card_ne_zero (h2 ▸ Nat.card_pos.ne')`. Conclude with `⟨h3, h2⟩`.
-/
private theorem count {l : ℕ} {D C : Type} [Group D] [TopologicalSpace D] [IsTopologicalGroup D]
    [Group C] [Finite C] (χ : D →* C) (hl : (Nat.card C).Coprime l)
    (I : Subgroup D) [hI : I.Normal] (φ : D)
    (ha : ∀ U : Subgroup D, IsOpen (U : Set D) → I ≤ U → φ ∈ U → U = ⊤)
    (hc : ∀ n : ℕ, 0 < n → ∃ V : Subgroup D, V.Normal ∧ IsOpen (V : Set D) ∧ I ≤ V ∧
      ∀ j : ℕ, φ ^ j ∈ V → n ∣ j) :
    UnrCount l D (I ⊓ χ.ker) := by
  intro R M _ _ _ _ ρ hρ hM hJ
  let ev : ZK ρ I → Fix ρ I := fun z ↦ ⟨z.1 φ, val_mem_fix ρ I z.2 φ⟩
  have hev : Function.Bijective ev := by
    refine ⟨fun z w h ↦ ?_, fun m ↦ ?_⟩
    · have h1 : z.1 φ = w.1 φ := congrArg Subtype.val h
      have := eq_zero_of_dense ρ I φ ha (sub_mem z.2 w.2) (by simp [h1])
      exact Subtype.ext (sub_eq_zero.1 this)
    · obtain ⟨z, hz, h⟩ := exists_cocycle ρ hρ I φ ha hc m.2
      exact ⟨⟨z, hz⟩, Subtype.ext h⟩
  have hfin : Finite (ZK ρ I) := Finite.of_injective _ hev.1
  have hcard : Nat.card (ZK ρ I) = Nat.card (Fix ρ I) := Nat.card_eq_of_bijective _ hev
  have hcob : ∀ b, cob ρ b ∈ Zl ρ := fun b ↦
    ⟨(hρ b).comp (fun y ↦ y - b), fun g h ↦ by simp [cob]⟩
  let Φ : (ZK ρ I × M) →ₗ[R] (D → M) := (ZK ρ I).subtype.coprod (cob ρ)
  have hrange : LinearMap.range Φ = ZK ρ (I ⊓ χ.ker) := by
    apply le_antisymm
    · rintro _ ⟨⟨w, b⟩, rfl⟩
      refine ⟨add_mem w.2.1 (hcob b), fun g hg ↦ ?_⟩
      simp [Φ, cob, w.2.2 g hg.1, hJ g hg]
    · intro z hz
      obtain ⟨b, hb⟩ := UpperTheory.Reformulated.B.CoboundaryCriterion.isCoboundary_of_coprime ρ I.subtype (χ.comp I.subtype) hl hM z
        hz.1.2 (fun u hu ↦ hz.2 u ⟨u.2, hu⟩)
      refine ⟨(⟨z - cob ρ b, sub_mem hz.1 (hcob b), fun g hg ↦ ?_⟩, b), by simp [Φ]⟩
      have := hb ⟨g, hg⟩
      simp only [Subgroup.coe_subtype] at this
      simp [cob, this]
  have hker : Nat.card (LinearMap.ker Φ) = Nat.card (Fix ρ I) := by
    have hmem : ∀ p : LinearMap.ker Φ, p.1.1.1 = - cob ρ p.1.2 := fun p ↦
      eq_neg_of_add_eq_zero_left p.2
    refine Nat.card_eq_of_bijective (fun p ↦ ⟨p.1.2, fun g hg ↦ ?_⟩) ⟨fun p q h ↦ ?_, fun b ↦ ?_⟩
    · have h1 := p.1.1.2.2 g hg
      rw [hmem p] at h1
      have h2 : -(ρ g p.1.2 - p.1.2) = 0 := h1
      exact sub_eq_zero.1 (neg_eq_zero.1 h2)
    · have h1 : p.1.2 = q.1.2 := congrArg Subtype.val h
      exact Subtype.ext (Prod.ext (Subtype.ext (by rw [hmem p, hmem q, h1])) h1)
    · refine ⟨⟨(⟨- cob ρ b, neg_mem (hcob b), fun g hg ↦ ?_⟩, b), by simp [Φ]⟩, rfl⟩
      simp [cob, b.2 g hg]
  have h1 := Submodule.card_eq_card_quotient_mul_card (LinearMap.ker Φ)
  rw [Nat.card_congr Φ.quotKerEquivRange.toEquiv, hrange, hker, Nat.card_prod, hcard] at h1
  have h2 : Nat.card (ZK ρ (I ⊓ χ.ker)) = Nat.card M :=
    (Nat.eq_of_mul_eq_mul_left Nat.card_pos h1).symm
  have h3 : Finite (ZK ρ (I ⊓ χ.ker)) := Nat.finite_of_card_ne_zero (h2 ▸ Nat.card_pos.ne')
  exact ⟨h3, h2⟩

end UpperTheory.Reformulated.B.RootEquality

namespace UpperTheory.Reformulated.B.RootEquality

open NumberField IsDedekindDomain

/- English proof (translation)
Consider the cases of `nonempty_fintype k`. Set `L` to `IntermediateField.adjoin k (S : Set K)`. Establish `: FiniteDimensional k L` using `IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x`. Establish `: Finite L` using `Module.finite_of_finite k`. Take `⟨⟨j, hj⟩, h⟩` from `(FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2 (σ.restrictNormal L)`.

Use `⟨j, fun x hx ↦ ?_⟩` and prove the remaining obligations. Establish `hx' : x ∈ L` using `IntermediateField.subset_adjoin k _ hx`. Establish `h1` using `σ.restrictNormal_commutes L ⟨x, hx'⟩`. Rewrite `h1` using `[← h]`. Simplify using `only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h1`.

Rewrite using `[Nat.card_eq_fintype_card]`. Simplify using `using h1.symm`.
-/
private theorem finfield {k K : Type} [Field k] [Finite k] [Field K] [Algebra k K]
    [Algebra.IsAlgebraic k K] (σ : K ≃ₐ[k] K) (S : Finset K) :
    ∃ j : ℕ, ∀ x ∈ S, σ x = x ^ (Nat.card k ^ j) := by
  cases nonempty_fintype k
  let L := IntermediateField.adjoin k (S : Set K)
  have : FiniteDimensional k L :=
    IntermediateField.finiteDimensional_adjoin fun x _ ↦ Algebra.IsIntegral.isIntegral x
  have : Finite L := Module.finite_of_finite k
  obtain ⟨⟨j, hj⟩, h⟩ := (FiniteField.bijective_frobeniusAlgEquivOfAlgebraic_pow k L).2
    (σ.restrictNormal L)
  refine ⟨j, fun x hx ↦ ?_⟩
  have hx' : x ∈ L := IntermediateField.subset_adjoin k _ hx
  have h1 := σ.restrictNormal_commutes L ⟨x, hx'⟩
  rw [← h] at h1
  simp only [AlgEquiv.coe_pow, FiniteField.coe_frobeniusAlgEquivOfAlgebraic_iterate] at h1
  rw [Nat.card_eq_fintype_card]
  simpa using h1.symm

section NT

variable {F Ω : Type} [Field F] [Field Ω] [Algebra F Ω] (A : ValuationSubring Ω)

open scoped Pointwise in
/- English proof (translation)
Use `show σ • A = A ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h x conv_lhs => rw [← h]`. Conclude with `ValuationSubring.smul_mem_pointwise_smul_iff (g := σ)`. Introduce `h`.

Use extensionality with `x`. Rewrite using `[ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]`. Establish `: σ (σ⁻¹ • x) = x` using `σ.apply_symm_apply x`. Rewrite using `[this]`.
-/
private theorem mem_dec {σ : G F Ω} : σ ∈ Dec A ↔ ∀ x, σ x ∈ A ↔ x ∈ A := by
  show σ • A = A ↔ _
  constructor
  · intro h x
    conv_lhs => rw [← h]
    exact ValuationSubring.smul_mem_pointwise_smul_iff (g := σ)
  · intro h
    ext x
    rw [ValuationSubring.mem_pointwise_smul_iff_inv_smul_mem, ← h]
    have : σ (σ⁻¹ • x) = x := σ.apply_symm_apply x
    rw [this]

/- English proof (translation)
Rewrite using `[← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]`.
-/
private theorem val_lt_iff (x : Ω) : A.valuation x < 1 ↔ x = 0 ∨ x⁻¹ ∉ A := by
  rw [← ValuationSubring.mem_nonunits_iff, ValuationSubring.mem_nonunits_iff_or]

/- English proof (translation)
Rewrite using `[val_lt_iff, val_lt_iff, ← map_inv₀, (mem_dec A).1 h, map_eq_zero]`.
-/
private theorem dec_lt {σ : G F Ω} (h : σ ∈ Dec A) (x : Ω) :
    A.valuation (σ x) < 1 ↔ A.valuation x < 1 := by
  rw [val_lt_iff, val_lt_iff, ← map_inv₀, (mem_dec A).1 h, map_eq_zero]

/- English proof (translation)
Establish `h : IsIntegral A (b : Ω)` using `b.isIntegral_coe.tower_top`. Take `⟨y, hy⟩` from `IsIntegrallyClosed.isIntegral_iff.1 h`. Conclude with `hy ▸ y.2`.
-/
private theorem int_mem (b : 𝓞 Ω) : (b : Ω) ∈ A := by
  have h : IsIntegral A (b : Ω) := b.isIntegral_coe.tower_top
  obtain ⟨y, hy⟩ := IsIntegrallyClosed.isIntegral_iff.1 h
  exact hy ▸ y.2

/- English proof (translation)
The claim follows from `(A.valuation_le_one_iff _).2 (int_mem A b)`.
-/
private theorem int_le (b : 𝓞 Ω) : A.valuation (b : Ω) ≤ 1 :=
  (A.valuation_le_one_iff _).2 (int_mem A b)

private noncomputable def cen : Ideal (𝓞 Ω) :=
  Ideal.comap ((algebraMap (𝓞 Ω) Ω).codRestrict A (int_mem A)) (IsLocalRing.maximalIdeal A)

private instance : (cen A).IsPrime := Ideal.comap_isPrime _ _

/- English proof (translation)
The claim follows from `A.valuation_lt_one_iff _`.
-/
private theorem mem_cen {b : 𝓞 Ω} : b ∈ cen A ↔ A.valuation (b : Ω) < 1 :=
  A.valuation_lt_one_iff _

/- English proof (translation)
Rewrite using `[mem_cen, not_lt]`. Conclude with `⟨fun h ↦ le_antisymm (int_le A b) h, fun h ↦ h.ge⟩`.
-/
private theorem not_mem_cen {b : 𝓞 Ω} : b ∉ cen A ↔ A.valuation (b : Ω) = 1 := by
  rw [mem_cen, not_lt]
  exact ⟨fun h ↦ le_antisymm (int_le A b) h, fun h ↦ h.ge⟩

/- English proof (translation)
Set `L` to `IntermediateField.adjoin F {x}`. Establish `: FiniteDimensional F L` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Establish `: NumberField L` using `NumberField.of_module_finite F L`. Set `f` to `algebraMap (𝓞 L) (𝓞 Ω)`. Set `P : HeightOneSpectrum (𝓞 L)` to `{ asIdeal := (cen A).comap f isPrime := Ideal.comap_isPrime _ _ ne_bot := fun h ↦ by`.

Establish `h1 : (q : 𝓞 L) ∈ (cen A).comap f`. Rewrite using `[Ideal.mem_comap, mem_cen, map_natCast]`. Simplify using `using hq`. Rewrite `h1` using `[h, Ideal.mem_bot]`. Conclude with `hq0 (by exact_mod_cast h1) }`.

Take `⟨n, d, h | h⟩` from `P.exists_primeCompl_mul_eq_or_mul_eq (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : L)`. Conclude with `⟨f n, f d, d.2, congrArg Subtype.val h⟩`. Establish `h1 : x * (f n : Ω) = (f d : Ω)` using `congrArg Subtype.val h`. Use `⟨f d, f n, fun hn ↦ ?_, h1⟩` and prove the remaining obligations. Apply `d.2` to reduce the goal to its premises.

Use `show f d ∈ cen A`. Rewrite `hn`, the goal using `[mem_cen]`. Rewrite using `[← h1, map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 hx) zero_le hn`.
-/
private theorem frac [NumberField F] [Algebra.IsAlgebraic F Ω] {q : ℕ} (hq0 : q ≠ 0)
    (hq : A.valuation (q : Ω) < 1) {x : Ω} (hx : x ∈ A) :
    ∃ b s : 𝓞 Ω, s ∉ cen A ∧ x * s = b := by
  let L := IntermediateField.adjoin F {x}
  have : FiniteDimensional F L :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  have : NumberField L := NumberField.of_module_finite F L
  let f := algebraMap (𝓞 L) (𝓞 Ω)
  let P : HeightOneSpectrum (𝓞 L) :=
    { asIdeal := (cen A).comap f
      isPrime := Ideal.comap_isPrime _ _
      ne_bot := fun h ↦ by
        have h1 : (q : 𝓞 L) ∈ (cen A).comap f := by
          rw [Ideal.mem_comap, mem_cen, map_natCast]
          simpa using hq
        rw [h, Ideal.mem_bot] at h1
        exact hq0 (by exact_mod_cast h1) }
  obtain ⟨n, d, h | h⟩ := P.exists_primeCompl_mul_eq_or_mul_eq
    (⟨x, IntermediateField.mem_adjoin_simple_self F x⟩ : L)
  · exact ⟨f n, f d, d.2, congrArg Subtype.val h⟩
  · have h1 : x * (f n : Ω) = (f d : Ω) := congrArg Subtype.val h
    refine ⟨f d, f n, fun hn ↦ ?_, h1⟩
    apply d.2
    show f d ∈ cen A
    rw [mem_cen] at hn ⊢
    rw [← h1, map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right ((A.valuation_le_one_iff _).2 hx) zero_le hn

/- English proof (translation)
Both sides reduce to the same expression.
-/
private theorem coe_smul (σ : G F Ω) (b : 𝓞 Ω) : ((σ • b : 𝓞 Ω) : Ω) = σ b := rfl

open scoped Pointwise in
/- English proof (translation)
Use `show σ • cen A = cen A ↔ _`. Prove the components needed by the constructor for the conclusion. Introduce `h x conv_lhs => rw [← h]`. Conclude with `Ideal.smul_mem_pointwise_smul_iff`. Introduce `h`.

Use extensionality with `x`. Rewrite using `[Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h, smul_inv_smul]`.
-/
private theorem mem_stab {σ : G F Ω} :
    σ ∈ MulAction.stabilizer (G F Ω) (cen A) ↔ ∀ b, σ • b ∈ cen A ↔ b ∈ cen A := by
  show σ • cen A = cen A ↔ _
  constructor
  · intro h x
    conv_lhs => rw [← h]
    exact Ideal.smul_mem_pointwise_smul_iff
  · intro h
    ext x
    rw [Ideal.mem_pointwise_smul_iff_inv_smul_mem, ← h, smul_inv_smul]

open scoped Pointwise in
/- English proof (translation)
The claim follows from `fun σ h ↦ (mem_stab A).2 fun b ↦ by rw [mem_cen, mem_cen, coe_smul, dec_lt A h]`.
-/
private theorem dec_le_stab : Dec A ≤ MulAction.stabilizer (G F Ω) (cen A) := fun σ h ↦
  (mem_stab A).2 fun b ↦ by rw [mem_cen, mem_cen, coe_smul, dec_lt A h]

open scoped Pointwise in
/- English proof (translation)
Establish `key : ∀ σ ∈ MulAction.stabilizer (G F Ω) (cen A), ∀ x ∈ A, σ x ∈ A`. Introduce `σ h x hx`. Take `⟨b, s, hs, e⟩` from `frac (F := F) A hq0 hq hx`. Establish `h1 : A.valuation (σ s) = 1`. Rewrite using `[← coe_smul, ← not_mem_cen, (mem_stab A).1 h]`.

Conclude with `hs`. Establish `h2` using `int_le A (σ • b)`. Rewrite `h2` using `[coe_smul, ← e, map_mul, map_mul, h1, mul_one]`. Conclude with `(A.valuation_le_one_iff _).1 h2`. Introduce `σ h`.

Use `(mem_dec A).2 fun x ↦ ⟨fun hx ↦ ?_, key σ h x⟩` and prove the remaining obligations. Use `key σ⁻¹ (inv_mem h) _ hx` as an intermediate fact. Rewrite `this` using `[show σ⁻¹ (σ x) = x from σ.symm_apply_apply x]`. Then use the resulting hypothesis.
-/
private theorem stab_le_dec [NumberField F] [Algebra.IsAlgebraic F Ω] {q : ℕ} (hq0 : q ≠ 0)
    (hq : A.valuation (q : Ω) < 1) : MulAction.stabilizer (G F Ω) (cen A) ≤ Dec A := by
  have key : ∀ σ ∈ MulAction.stabilizer (G F Ω) (cen A), ∀ x ∈ A, σ x ∈ A := by
    intro σ h x hx
    obtain ⟨b, s, hs, e⟩ := frac (F := F) A hq0 hq hx
    have h1 : A.valuation (σ s) = 1 := by
      rw [← coe_smul, ← not_mem_cen, (mem_stab A).1 h]; exact hs
    have h2 := int_le A (σ • b)
    rw [coe_smul, ← e, map_mul, map_mul, h1, mul_one] at h2
    exact (A.valuation_le_one_iff _).1 h2
  intro σ h
  refine (mem_dec A).2 fun x ↦ ⟨fun hx ↦ ?_, key σ h x⟩
  have := key σ⁻¹ (inv_mem h) _ hx
  rwa [show σ⁻¹ (σ x) = x from σ.symm_apply_apply x] at this

/- English proof (translation)
Use `⟨h, fun x hx ↦ ?_⟩` and prove the remaining obligations. Take `⟨b, s, hs, e⟩` from `frac (F := F) A hq0 hq ((A.valuation_le_one_iff _).1 hx)`. Establish `h1 : A.valuation (σ s) = 1`. Rewrite using `[← coe_smul, ← not_mem_cen, (mem_stab A).1 (dec_le_stab A h)]`. Conclude with `hs`.

Establish `h2 : (σ x - x) * σ s = (σ b - b) - x * (σ s - s)`. Rewrite using `[← e, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Establish `h3 : A.valuation ((σ x - x) * σ s) < 1`. Rewrite using `[h2]`.

Use `Valuation.map_sub_lt _ (hb b) ?_` and prove the remaining obligations. Rewrite using `[map_mul]`. Conclude with `mul_lt_one_of_nonneg_of_lt_one_right hx zero_le (hb s)`. Rewrite `h3` using `[map_mul, h1, mul_one]`. Then use the resulting hypothesis.
-/
private theorem mem_ine [NumberField F] [Algebra.IsAlgebraic F Ω] {q : ℕ} (hq0 : q ≠ 0)
    (hq : A.valuation (q : Ω) < 1) {σ : G F Ω} (h : σ ∈ Dec A)
    (hb : ∀ b : 𝓞 Ω, A.valuation (σ b - b) < 1) : σ ∈ Ine A := by
  refine ⟨h, fun x hx ↦ ?_⟩
  obtain ⟨b, s, hs, e⟩ := frac (F := F) A hq0 hq ((A.valuation_le_one_iff _).1 hx)
  have h1 : A.valuation (σ s) = 1 := by
    rw [← coe_smul, ← not_mem_cen, (mem_stab A).1 (dec_le_stab A h)]; exact hs
  have h2 : (σ x - x) * σ s = (σ b - b) - x * (σ s - s) := by
    rw [← e, map_mul]; ring
  have h3 : A.valuation ((σ x - x) * σ s) < 1 := by
    rw [h2]
    refine Valuation.map_sub_lt _ (hb b) ?_
    rw [map_mul]
    exact mul_lt_one_of_nonneg_of_lt_one_right hx zero_le (hb s)
  rwa [map_mul, h1, mul_one] at h3

/- English proof (translation)
Establish `: FiniteDimensional F (IntermediateField.adjoin F {x})` using `IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)`. Conclude with `Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {x}).fixingSubgroup) (H₂ := MulAction.stabilizer (G F Ω) x) (fun σ hσ ↦ hσ ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩) (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {x}))`.
-/
private theorem isOpen_fix [Algebra.IsAlgebraic F Ω] (x : Ω) :
    IsOpen {σ : G F Ω | σ x = x} := by
  have : FiniteDimensional F (IntermediateField.adjoin F {x}) :=
    IntermediateField.adjoin.finiteDimensional (Algebra.IsIntegral.isIntegral x)
  exact Subgroup.isOpen_mono (H₁ := (IntermediateField.adjoin F {x}).fixingSubgroup)
    (H₂ := MulAction.stabilizer (G F Ω) x)
    (fun σ hσ ↦ hσ ⟨x, IntermediateField.mem_adjoin_simple_self F x⟩)
    (IntermediateField.fixingSubgroup_isOpen (IntermediateField.adjoin F {x}))

/- English proof (translation)
Rewrite using `[IsLocallyConstant.iff_eventually_eq]`. Introduce `g`. Establish `h1 : (fun σ ↦ g⁻¹ * σ) ⁻¹' {σ : G F Ω | σ x = x} ∈ nhds g` using `((isOpen_fix x).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)`. Use `filter_upwards [h1] with σ hσ`. Establish `h2 : σ = g * (g⁻¹ * σ)` using `by group`.

Establish `h3 : (g⁻¹ * σ) x = x` using `hσ`. Rewrite using `[h2, AlgEquiv.mul_apply, h3]`.
-/
private theorem lc_apply [Algebra.IsAlgebraic F Ω] (x : Ω) :
    IsLocallyConstant fun σ : G F Ω ↦ σ x := by
  rw [IsLocallyConstant.iff_eventually_eq]
  intro g
  have h1 : (fun σ ↦ g⁻¹ * σ) ⁻¹' {σ : G F Ω | σ x = x} ∈ nhds g :=
    ((isOpen_fix x).preimage (continuous_const.mul continuous_id)).mem_nhds (by simp)
  filter_upwards [h1] with σ hσ
  have h2 : σ = g * (g⁻¹ * σ) := by group
  have h3 : (g⁻¹ * σ) x = x := hσ
  rw [h2, AlgEquiv.mul_apply, h3]

/- English proof (translation)
Establish `: (Dec (F` using `F) A : Set (G F Ω)) = ⋂ x : Ω, (fun σ : G F Ω ↦ σ x) ⁻¹' {y | y ∈ A ↔ x ∈ A} := by`. Use extensionality with `σ`. Simplify using `[mem_dec]`. Rewrite using `[this]`. Conclude with `isClosed_iInter fun x ↦ ⟨lc_apply x _ᶜ⟩`.
-/
private theorem dec_closed [Algebra.IsAlgebraic F Ω] :
    IsClosed (Dec (F := F) A : Set (G F Ω)) := by
  have : (Dec (F := F) A : Set (G F Ω)) = ⋂ x : Ω, (fun σ : G F Ω ↦ σ x) ⁻¹' {y | y ∈ A ↔ x ∈ A} := by
    ext σ
    simp [mem_dec]
  rw [this]
  exact isClosed_iInter fun x ↦ ⟨lc_apply x _ᶜ⟩

/- English proof (translation)
Establish `hN0 : N ≠ 0` using `by rintro rfl; simp at hN`. Establish `hy1 : A.valuation y = 1`. Use `congrArg A.valuation hy` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le hN0).1 this`.

Establish `hy0 : y ≠ 0` using `by rintro rfl; simp at hy1`. Take `⟨u, rfl⟩ : ∃ u, x = u * y` from `⟨x / y, by field_simp⟩`. Rewrite `hx` using `[mul_pow, hy, mul_one]`. Rewrite `h` using `[show u * y - y = (u - 1) * y by ring, map_mul, hy1, mul_one]`. Establish `hu1 : A.valuation u = 1`.

Use `congrArg A.valuation hx` as an intermediate fact. Rewrite `this` using `[map_pow, map_one]`. Conclude with `(pow_eq_one_iff_of_nonneg zero_le hN0).1 this`. Establish `hp : ∀ i : ℕ, A.valuation (u ^ i - 1) < 1`. Introduce `i`.

Proceed by induction on `i with`. Consider the case `zero => simp`. Consider the case `succ i ih`. Rewrite using `[show u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) by ring]`. Use `Valuation.map_add_lt _ ?_ h` and prove the remaining obligations.

Rewrite using `[map_mul, hu1, mul_one]` and apply the resulting hypothesis. Establish `h2` using `geom_sum_mul u N`. Rewrite `h2` using `[hx, sub_self, mul_eq_zero, sub_eq_zero]`. Break down `h2 with h2 | h2` into its components or cases. Establish `h3` using `Valuation.map_sum_lt A.valuation (s := Finset.range N) one_ne_zero fun i _ ↦ hp i`.

Simplify using `[Finset.sum_sub_distrib, h2, hN] at h3`. Rewrite using `[h2, one_mul]`.
-/
private theorem root_eq {N : ℕ} (hN : A.valuation (N : Ω) = 1) {x y : Ω} (hx : x ^ N = 1)
    (hy : y ^ N = 1) (h : A.valuation (x - y) < 1) : x = y := by
  have hN0 : N ≠ 0 := by rintro rfl; simp at hN
  have hy1 : A.valuation y = 1 := by
    have := congrArg A.valuation hy
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hN0).1 this
  have hy0 : y ≠ 0 := by rintro rfl; simp at hy1
  obtain ⟨u, rfl⟩ : ∃ u, x = u * y := ⟨x / y, by field_simp⟩
  rw [mul_pow, hy, mul_one] at hx
  rw [show u * y - y = (u - 1) * y by ring, map_mul, hy1, mul_one] at h
  have hu1 : A.valuation u = 1 := by
    have := congrArg A.valuation hx
    rw [map_pow, map_one] at this
    exact (pow_eq_one_iff_of_nonneg zero_le hN0).1 this
  have hp : ∀ i : ℕ, A.valuation (u ^ i - 1) < 1 := by
    intro i
    induction i with
    | zero => simp
    | succ i ih =>
      rw [show u ^ (i + 1) - 1 = (u ^ i - 1) * u + (u - 1) by ring]
      refine Valuation.map_add_lt _ ?_ h
      rwa [map_mul, hu1, mul_one]
  have h2 := geom_sum_mul u N
  rw [hx, sub_self, mul_eq_zero, sub_eq_zero] at h2
  rcases h2 with h2 | h2
  · have h3 := Valuation.map_sum_lt A.valuation (s := Finset.range N) one_ne_zero
      fun i _ ↦ hp i
    simp [Finset.sum_sub_distrib, h2, hN] at h3
  · rw [h2, one_mul]

end NT

end UpperTheory.Reformulated.B.RootEquality

namespace UpperTheory.Reformulated.B.RootEquality

open NumberField IsDedekindDomain

section Fr

variable {F Ω : Type} [Field F] [NumberField F] [Field Ω] [Algebra F Ω] [IsAlgClosure F Ω]
  {A : ValuationSubring Ω} {v : HeightOneSpectrum (𝓞 F)}

omit [NumberField F] [IsAlgClosure F Ω] in
/- English proof (translation)
Assemble the required witnesses or components as `⟨by ext x rw [Ideal.mem_comap, mem_cen] exact (h x).symm⟩`.
-/
private theorem lies (h : IsPlaceOver A v) : (cen A).LiesOver v.asIdeal :=
  ⟨by
    ext x
    rw [Ideal.mem_comap, mem_cen]
    exact (h x).symm⟩

/- English proof (translation)
The claim follows from `v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot`.
-/
private theorem fin_res (v : HeightOneSpectrum (𝓞 F)) : Finite (𝓞 F ⧸ v.asIdeal) :=
  v.asIdeal.finiteQuotientOfFreeOfNeBot v.ne_bot

/- English proof (translation)
Use `fin_res v` as an intermediate fact. Use `v.isPrime` as an intermediate fact. Conclude with `Finite.one_lt_card`.
-/
private theorem one_lt_q (v : HeightOneSpectrum (𝓞 F)) : 1 < Nat.card (𝓞 F ⧸ v.asIdeal) := by
  have := fin_res v
  have := v.isPrime
  exact Finite.one_lt_card

omit [IsAlgClosure F Ω] in
/- English proof (translation)
Use `fin_res v` as an intermediate fact. Establish `h1 : (Nat.card (𝓞 F ⧸ v.asIdeal) : 𝓞 F) ∈ v.asIdeal`. Rewrite using `[← Ideal.Quotient.eq_zero_iff_mem, map_natCast]`. Consider the cases of `nonempty_fintype (𝓞 F ⧸ v.asIdeal)`. Rewrite using `[Nat.card_eq_fintype_card]`.

Conclude with `Nat.cast_card_eq_zero _`. Simplify using `using (h _).2 h1`.
-/
private theorem val_q (h : IsPlaceOver A v) :
    A.valuation (Nat.card (𝓞 F ⧸ v.asIdeal) : Ω) < 1 := by
  have := fin_res v
  have h1 : (Nat.card (𝓞 F ⧸ v.asIdeal) : 𝓞 F) ∈ v.asIdeal := by
    rw [← Ideal.Quotient.eq_zero_iff_mem, map_natCast]
    cases nonempty_fintype (𝓞 F ⧸ v.asIdeal)
    rw [Nat.card_eq_fintype_card]
    exact Nat.cast_card_eq_zero _
  simpa using (h _).2 h1

/- English proof (translation)
Use `⟨fun b hb ↦ ?_⟩` and prove the remaining obligations. Take `⟨x, hx⟩` from `(InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (b : Ω)).2 fun σ ↦ congrArg Subtype.val (hb σ)`. Establish `h1 : IsIntegral ℤ x`. Establish `: IsIntegral ℤ (b : Ω)` using `b.isIntegral_coe`. Rewrite `this` using `[← hx]`.

Conclude with `(isIntegral_algebraMap_iff (algebraMap F Ω).injective).1 this`. Conclude with `⟨⟨x, h1⟩, Subtype.ext hx⟩`.
-/
private theorem invariant : Algebra.IsInvariant (𝓞 F) (𝓞 Ω) (G F Ω) := by
  refine ⟨fun b hb ↦ ?_⟩
  obtain ⟨x, hx⟩ := (InfiniteGalois.mem_range_algebraMap_iff_fixed (k := F) (b : Ω)).2
    fun σ ↦ congrArg Subtype.val (hb σ)
  have h1 : IsIntegral ℤ x := by
    have : IsIntegral ℤ (b : Ω) := b.isIntegral_coe
    rw [← hx] at this
    exact (isIntegral_algebraMap_iff (algebraMap F Ω).injective).1 this
  exact ⟨⟨x, h1⟩, Subtype.ext hx⟩

attribute [local instance] Ideal.Quotient.field in
/- English proof (translation)
Use `lies h` as an intermediate fact. Use `fin_res v` as an intermediate fact. Use `v.isMaximal` as an intermediate fact. Establish `: (cen A).IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal (cen A) v.asIdeal`. Use `invariant (F := F) (Ω := Ω)` as an intermediate fact.

Establish `: SMulCommClass (G F Ω) (𝓞 F) (𝓞 Ω)` using `⟨fun σ a b ↦ Subtype.ext (by show σ (algebraMap F Ω a * b) = algebraMap F Ω a * σ b`. Rewrite using `[map_mul, AlgEquiv.commutes])⟩`. Set `_ : TopologicalSpace (𝓞 Ω)` to `⊥`. Establish `: DiscreteTopology (𝓞 Ω)` using `⟨rfl⟩`. Establish `: ContinuousSMul (G F Ω) (𝓞 Ω)` using `continuousSMul_iff_stabilizer_isOpen.2 fun b ↦ by`.

Use `isOpen_fix (F := F) (b : Ω) using 1` and compare the differences between its conclusion and the goal. Use extensionality with `σ`. Conclude with `⟨fun hσ ↦ congrArg Subtype.val hσ, fun hσ ↦ Subtype.ext hσ⟩`. Consider the cases of `nonempty_fintype (𝓞 F ⧸ v.asIdeal)`. Take `⟨σ, hσ⟩` from `Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G F Ω) v.asIdeal (cen A) (FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (𝓞 Ω ⧸ cen A))`.

Use `⟨σ, stab_le_dec A (one_lt_q v).ne_bot (val_q h) σ.2, fun b ↦ ?_⟩` and prove the remaining obligations. Establish `h1` using `DFunLike.congr_fun hσ (Ideal.Quotient.mk (cen A) b)`. Rewrite `h1` using `[Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic, ← Nat.card_eq_fintype_card]`. Simplify using `only [← map_pow, Ideal.Quotient.eq, mem_cen] at h1`. Conclude with `h1`.
-/
private theorem exists_frob (h : IsPlaceOver A v) : ∃ φ ∈ Dec (F := F) A, ∀ b : 𝓞 Ω,
    A.valuation (φ b - b ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1 := by
  have := lies h
  have := fin_res v
  have := v.isMaximal
  have : (cen A).IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (cen A) v.asIdeal
  have := invariant (F := F) (Ω := Ω)
  have : SMulCommClass (G F Ω) (𝓞 F) (𝓞 Ω) := ⟨fun σ a b ↦ Subtype.ext (by
    show σ (algebraMap F Ω a * b) = algebraMap F Ω a * σ b
    rw [map_mul, AlgEquiv.commutes])⟩
  let _ : TopologicalSpace (𝓞 Ω) := ⊥
  have : DiscreteTopology (𝓞 Ω) := ⟨rfl⟩
  have : ContinuousSMul (G F Ω) (𝓞 Ω) := continuousSMul_iff_stabilizer_isOpen.2 fun b ↦ by
    convert isOpen_fix (F := F) (b : Ω) using 1
    ext σ
    exact ⟨fun hσ ↦ congrArg Subtype.val hσ, fun hσ ↦ Subtype.ext hσ⟩
  cases nonempty_fintype (𝓞 F ⧸ v.asIdeal)
  obtain ⟨σ, hσ⟩ := Ideal.Quotient.stabilizerHom_surjective_of_profinite (G := G F Ω)
    v.asIdeal (cen A)
    (FiniteField.frobeniusAlgEquivOfAlgebraic (𝓞 F ⧸ v.asIdeal) (𝓞 Ω ⧸ cen A))
  refine ⟨σ, stab_le_dec A (one_lt_q v).ne_bot (val_q h) σ.2, fun b ↦ ?_⟩
  have h1 := DFunLike.congr_fun hσ (Ideal.Quotient.mk (cen A) b)
  rw [Ideal.Quotient.stabilizerHom_apply, FiniteField.coe_frobeniusAlgEquivOfAlgebraic,
    ← Nat.card_eq_fintype_card] at h1
  simp only [← map_pow, Ideal.Quotient.eq, mem_cen] at h1
  exact h1

attribute [local instance] Ideal.Quotient.field in
/- English proof (translation)
Use `lies h` as an intermediate fact. Use `fin_res v` as an intermediate fact. Use `v.isMaximal` as an intermediate fact. Establish `: (cen A).IsMaximal` using `Ideal.IsMaximal.of_liesOver_isMaximal (cen A) v.asIdeal`. Establish `: SMulCommClass (G F Ω) (𝓞 F) (𝓞 Ω)` using `⟨fun σ a b ↦ Subtype.ext (by show σ (algebraMap F Ω a * b) = algebraMap F Ω a * σ b`.

Rewrite using `[map_mul, AlgEquiv.commutes])⟩`. Take `⟨j, hj⟩` from `finfield (Ideal.Quotient.stabilizerHom (cen A) v.asIdeal (G F Ω) ⟨g, dec_le_stab A hg⟩) (S.image (Ideal.Quotient.mk (cen A)))`. Use `⟨j, fun b hb ↦ ?_⟩` and prove the remaining obligations. Establish `h1` using `hj _ (Finset.mem_image_of_mem _ hb)`. Rewrite `h1` using `[Ideal.Quotient.stabilizerHom_apply]`.

Simplify using `only [← map_pow, Ideal.Quotient.eq, mem_cen] at h1`. Conclude with `h1`.
-/
private theorem exists_pow (h : IsPlaceOver A v) {g : G F Ω} (hg : g ∈ Dec A) (S : Finset (𝓞 Ω)) :
    ∃ j : ℕ, ∀ b ∈ S, A.valuation (g b - b ^ (Nat.card (𝓞 F ⧸ v.asIdeal) ^ j)) < 1 := by
  classical
  have := lies h
  have := fin_res v
  have := v.isMaximal
  have : (cen A).IsMaximal := Ideal.IsMaximal.of_liesOver_isMaximal (cen A) v.asIdeal
  have : SMulCommClass (G F Ω) (𝓞 F) (𝓞 Ω) := ⟨fun σ a b ↦ Subtype.ext (by
    show σ (algebraMap F Ω a * b) = algebraMap F Ω a * σ b
    rw [map_mul, AlgEquiv.commutes])⟩
  obtain ⟨j, hj⟩ := finfield (Ideal.Quotient.stabilizerHom (cen A) v.asIdeal (G F Ω)
    ⟨g, dec_le_stab A hg⟩) (S.image (Ideal.Quotient.mk (cen A)))
  refine ⟨j, fun b hb ↦ ?_⟩
  have h1 := hj _ (Finset.mem_image_of_mem _ hb)
  rw [Ideal.Quotient.stabilizerHom_apply] at h1
  simp only [← map_pow, Ideal.Quotient.eq, mem_cen] at h1
  exact h1

omit [NumberField F] [IsAlgClosure F Ω] in
/- English proof (translation)
Establish `hφ' : ∀ b : 𝓞 Ω, Ideal.Quotient.mk (cen A) (φ • b) = Ideal.Quotient.mk (cen A) b ^ q` using `fun b ↦ by rw [← map_pow, Ideal.Quotient.eq, mem_cen]; exact hφ b`. Establish `key : Ideal.Quotient.mk (cen A) ((φ ^ j) • b) = Ideal.Quotient.mk (cen A) b ^ (q ^ j)`. Proceed by induction on `j with`. Consider the case `zero => simp`. Consider the case `succ j ih => rw [pow_succ', mul_smul, hφ', ih, ← pow_mul, pow_succ]`.

Rewrite `key` using `[← map_pow, Ideal.Quotient.eq, mem_cen]`. Conclude with `key`.
-/
private theorem frob_pow {q : ℕ} {φ : G F Ω}
    (hφ : ∀ b : 𝓞 Ω, A.valuation (φ b - b ^ q) < 1) (j : ℕ) (b : 𝓞 Ω) :
    A.valuation ((φ ^ j) b - b ^ (q ^ j)) < 1 := by
  have hφ' : ∀ b : 𝓞 Ω, Ideal.Quotient.mk (cen A) (φ • b) = Ideal.Quotient.mk (cen A) b ^ q :=
    fun b ↦ by rw [← map_pow, Ideal.Quotient.eq, mem_cen]; exact hφ b
  have key : Ideal.Quotient.mk (cen A) ((φ ^ j) • b) = Ideal.Quotient.mk (cen A) b ^ (q ^ j) := by
    induction j with
    | zero => simp
    | succ j ih => rw [pow_succ', mul_smul, hφ', ih, ← pow_mul, pow_succ]
  rw [← map_pow, Ideal.Quotient.eq, mem_cen] at key
  exact key

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce `g _`. Establish `: CompactSpace (Dec (F` using `F) A) := isCompact_iff_compactSpace.1 (dec_closed A).isCompact`. Take `⟨σ, hσU, hσ⟩` from `(U.isClosed_of_isOpen hU).isCompact.inter_iInter_nonempty (fun b : 𝓞 Ω ↦ {σ : Dec (F := F) A | A.valuation (σ.1 b - g.1 b) < 1}) (fun b ↦ ⟨(lc_apply (F := F) (b : Ω)).comp_continuous continuous_subtype_val {y | A.valuation (y - g.1 b) < 1}ᶜ⟩) (fun S ↦ by`. Take `⟨j, hj⟩` from `exists_pow h g.2 S`.

Use `⟨φ ^ j, pow_mem hφU j, ?_⟩` and prove the remaining obligations. Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq]`. Introduce `b hb`. Use `Valuation.map_sub_lt _ (frob_pow hφ j b) (hj b hb)` as an intermediate fact. Rewrite using `[sub_sub_sub_cancel_right] at this)` and apply the resulting hypothesis.

Simplify using `only [Set.mem_iInter, Set.mem_setOf_eq] at hσ`. Establish `h1 : g⁻¹ * σ ∈ U` using `hI (mem_ine A (one_lt_q v).ne_bot (val_q h) (g⁻¹ * σ).2 fun b ↦ by`. Rewrite using `[← dec_lt A g.2, map_sub]`. Establish `: g.1 ((g⁻¹ * σ).1 b) = σ.1 b` using `g.1.apply_symm_apply _`. Conclude with `(congrArg (fun y ↦ A.valuation (y - g.1 b) < 1) this).mpr (hσ b))`.

Establish `h2` using `mul_mem hσU (inv_mem h1)`. Simplify using `using h2`.
-/
private theorem dense (h : IsPlaceOver A v) (φ : Dec (F := F) A)
    (hφ : ∀ b : 𝓞 Ω, A.valuation (φ.1 b - b ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1)
    (U : Subgroup (Dec (F := F) A)) (hU : IsOpen (U : Set (Dec (F := F) A)))
    (hI : (Ine A).subgroupOf (Dec A) ≤ U) (hφU : φ ∈ U) : U = ⊤ := by
  rw [eq_top_iff]
  intro g _
  have : CompactSpace (Dec (F := F) A) := isCompact_iff_compactSpace.1 (dec_closed A).isCompact
  obtain ⟨σ, hσU, hσ⟩ := (U.isClosed_of_isOpen hU).isCompact.inter_iInter_nonempty
    (fun b : 𝓞 Ω ↦ {σ : Dec (F := F) A | A.valuation (σ.1 b - g.1 b) < 1})
    (fun b ↦ ⟨(lc_apply (F := F) (b : Ω)).comp_continuous continuous_subtype_val
      {y | A.valuation (y - g.1 b) < 1}ᶜ⟩)
    (fun S ↦ by
      obtain ⟨j, hj⟩ := exists_pow h g.2 S
      refine ⟨φ ^ j, pow_mem hφU j, ?_⟩
      simp only [Set.mem_iInter, Set.mem_setOf_eq]
      intro b hb
      have := Valuation.map_sub_lt _ (frob_pow hφ j b) (hj b hb)
      rwa [sub_sub_sub_cancel_right] at this)
  simp only [Set.mem_iInter, Set.mem_setOf_eq] at hσ
  have h1 : g⁻¹ * σ ∈ U := hI (mem_ine A (one_lt_q v).ne_bot (val_q h) (g⁻¹ * σ).2 fun b ↦ by
    rw [← dec_lt A g.2, map_sub]
    have : g.1 ((g⁻¹ * σ).1 b) = σ.1 b := g.1.apply_symm_apply _
    exact (congrArg (fun y ↦ A.valuation (y - g.1 b) < 1) this).mpr (hσ b))
  have h2 := mul_mem hσU (inv_mem h1)
  simpa using h2

/- English proof (translation)
Establish `hq1` using `one_lt_q v`. Establish `hq` using `val_q h`. Generalize the expression as in `Nat.card (𝓞 F ⧸ v.asIdeal) = q at hφ hq hq1`. Establish `hqn : 1 < q ^ n` using `Nat.one_lt_pow hn.ne' hq1`. Establish `hN : A.valuation ((q ^ n - 1 : ℕ) : Ω) = 1`.

Rewrite using `[Nat.cast_sub hqn.le, Nat.cast_pow, Nat.cast_one, Valuation.map_sub_swap]`. Apply `Valuation.map_one_sub_of_lt` to reduce the goal to its premises. Rewrite using `[map_pow]`. Conclude with `pow_lt_one₀ zero_le hq hn.ne'`. Establish `hN0 : q ^ n - 1 ≠ 0` using `by omega`.

Establish `: NeZero (q ^ n - 1)` using `⟨hN0⟩`. Establish `: IsAlgClosed Ω` using `IsAlgClosure.isAlgClosed F`. Establish `: CharZero Ω` using `charZero_of_injective_algebraMap (algebraMap F Ω).injective`. Take `⟨ζ, hζ⟩` from `HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)`. Establish `hroot : ∀ (σ : G F Ω) (x : Ω), x ^ (q ^ n - 1) = 1 → (σ x) ^ (q ^ n - 1) = 1` using `fun σ x hx ↦ by rw [← map_pow, hx, map_one]`.

Set `V : Subgroup (Dec (F` to `F) A) := { carrier := {σ | ∀ x : Ω, x ^ (q ^ n - 1) = 1 → σ.1 x = x} mul_mem' := fun {a b} ha hb x hx ↦ by show a.1 (b.1 x) = x`. Rewrite using `[hb x hx, ha x hx]`. Use the proof step `one_mem' := fun _ _ ↦ rfl`. Use the proof step `inv_mem' := fun {a} ha x hx ↦ by show a.1.symm x = x`. Rewrite using `[AlgEquiv.symm_apply_eq, ha x hx] }`.

Establish `hint : ∀ x : Ω, x ^ (q ^ n - 1) = 1 → IsIntegral ℤ x` using `fun x hx ↦ IsIntegral.of_pow (Nat.pos_of_ne_zero hN0) (hx ▸ isIntegral_one)`. Use `⟨V, ⟨fun a ha g x hx ↦ ?_⟩, ?_, fun σ hσ x hx ↦ ?_, fun j hj ↦ ?_⟩` and prove the remaining obligations. Use `show g.1 (a.1 (g.1⁻¹ x)) = x`. Rewrite using `[ha _ (hroot _ x hx)]`. Conclude with `g.1.apply_symm_apply x`.

Establish `: (V : Set (Dec (F` using `F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ζ = ζ} := by`. Use extensionality with `σ`. Use `⟨fun hσ ↦ hσ ζ hζ.1, fun hσ x hx ↦ ?_⟩` and prove the remaining obligations. Take `⟨i, -, rfl⟩` from `hζ.eq_pow_of_pow_eq_one hx`. Rewrite using `[map_pow, show σ.1 ζ = ζ from hσ]`.

Rewrite using `[this]`. Conclude with `(isOpen_fix ζ).preimage continuous_subtype_val`. Conclude with `root_eq A hN (hroot _ x hx) hx (hσ.2 x (int_le A ⟨x, hint x hx⟩))`. Establish `h1` using `frob_pow hφ j ⟨ζ, hint ζ hζ.1⟩`. Establish `h2 : (φ.1 ^ j) ζ = ζ` using `hj ζ hζ.1`.

Establish `h3 : ζ = ζ ^ (q ^ j)` using `root_eq A hN hζ.1 (by rw [pow_right_comm, hζ.1, one_pow]) (by`. Express the relevant statement in the definitionally equal form `A.valuation ((φ.1 ^ j) ζ - ζ ^ (q ^ j)) < 1 at h1`. Rewrite using `[h2] at h1)` and apply the resulting hypothesis. Establish `hqj : 1 ≤ q ^ j` using `Nat.one_le_pow _ _ (by omega)`. Establish `h4 : ζ ^ (q ^ j - 1) = 1`.

Establish `h0 : ζ ≠ 0` using `hζ.ne_zero hN0`. Apply `mul_right_cancel₀ h0` to reduce the goal to its premises. Rewrite using `[← pow_succ, Nat.sub_add_cancel hqj, one_mul, ← h3]`. Establish `h5` using `Nat.gcd_eq_left (hζ.2 _ h4)`. Rewrite `h5` using `[Nat.pow_sub_one_gcd_pow_sub_one]`.

Establish `h6 : q ^ n.gcd j = q ^ n`. Establish `: 1 ≤ q ^ n.gcd j` using `Nat.one_le_pow _ _ (by omega)`. Use linear arithmetic over natural numbers and integers. Conclude with `Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective hq1 h6)`.
-/
private theorem levels (h : IsPlaceOver A v) (φ : Dec (F := F) A)
    (hφ : ∀ b : 𝓞 Ω, A.valuation (φ.1 b - b ^ Nat.card (𝓞 F ⧸ v.asIdeal)) < 1)
    (n : ℕ) (hn : 0 < n) : ∃ V : Subgroup (Dec (F := F) A), V.Normal ∧
      IsOpen (V : Set (Dec (F := F) A)) ∧ (Ine A).subgroupOf (Dec A) ≤ V ∧
      ∀ j : ℕ, φ ^ j ∈ V → n ∣ j := by
  have hq1 := one_lt_q v
  have hq := val_q h
  generalize Nat.card (𝓞 F ⧸ v.asIdeal) = q at hφ hq hq1
  have hqn : 1 < q ^ n := Nat.one_lt_pow hn.ne' hq1
  have hN : A.valuation ((q ^ n - 1 : ℕ) : Ω) = 1 := by
    rw [Nat.cast_sub hqn.le, Nat.cast_pow, Nat.cast_one, Valuation.map_sub_swap]
    apply Valuation.map_one_sub_of_lt
    rw [map_pow]
    exact pow_lt_one₀ zero_le hq hn.ne'
  have hN0 : q ^ n - 1 ≠ 0 := by omega
  have : NeZero (q ^ n - 1) := ⟨hN0⟩
  have : IsAlgClosed Ω := IsAlgClosure.isAlgClosed F
  have : CharZero Ω := charZero_of_injective_algebraMap (algebraMap F Ω).injective
  obtain ⟨ζ, hζ⟩ := HasEnoughRootsOfUnity.exists_primitiveRoot Ω (q ^ n - 1)
  have hroot : ∀ (σ : G F Ω) (x : Ω), x ^ (q ^ n - 1) = 1 → (σ x) ^ (q ^ n - 1) = 1 :=
    fun σ x hx ↦ by rw [← map_pow, hx, map_one]
  let V : Subgroup (Dec (F := F) A) :=
    { carrier := {σ | ∀ x : Ω, x ^ (q ^ n - 1) = 1 → σ.1 x = x}
      mul_mem' := fun {a b} ha hb x hx ↦ by
        show a.1 (b.1 x) = x
        rw [hb x hx, ha x hx]
      one_mem' := fun _ _ ↦ rfl
      inv_mem' := fun {a} ha x hx ↦ by
        show a.1.symm x = x
        rw [AlgEquiv.symm_apply_eq, ha x hx] }
  have hint : ∀ x : Ω, x ^ (q ^ n - 1) = 1 → IsIntegral ℤ x := fun x hx ↦
    IsIntegral.of_pow (Nat.pos_of_ne_zero hN0) (hx ▸ isIntegral_one)
  refine ⟨V, ⟨fun a ha g x hx ↦ ?_⟩, ?_, fun σ hσ x hx ↦ ?_, fun j hj ↦ ?_⟩
  · show g.1 (a.1 (g.1⁻¹ x)) = x
    rw [ha _ (hroot _ x hx)]
    exact g.1.apply_symm_apply x
  · have : (V : Set (Dec (F := F) A)) = Subtype.val ⁻¹' {σ : G F Ω | σ ζ = ζ} := by
      ext σ
      refine ⟨fun hσ ↦ hσ ζ hζ.1, fun hσ x hx ↦ ?_⟩
      obtain ⟨i, -, rfl⟩ := hζ.eq_pow_of_pow_eq_one hx
      rw [map_pow, show σ.1 ζ = ζ from hσ]
    rw [this]
    exact (isOpen_fix ζ).preimage continuous_subtype_val
  · exact root_eq A hN (hroot _ x hx) hx (hσ.2 x (int_le A ⟨x, hint x hx⟩))
  · have h1 := frob_pow hφ j ⟨ζ, hint ζ hζ.1⟩
    have h2 : (φ.1 ^ j) ζ = ζ := hj ζ hζ.1
    have h3 : ζ = ζ ^ (q ^ j) := root_eq A hN hζ.1 (by rw [pow_right_comm, hζ.1, one_pow])
      (by
        change A.valuation ((φ.1 ^ j) ζ - ζ ^ (q ^ j)) < 1 at h1
        rwa [h2] at h1)
    have hqj : 1 ≤ q ^ j := Nat.one_le_pow _ _ (by omega)
    have h4 : ζ ^ (q ^ j - 1) = 1 := by
      have h0 : ζ ≠ 0 := hζ.ne_zero hN0
      apply mul_right_cancel₀ h0
      rw [← pow_succ, Nat.sub_add_cancel hqj, one_mul, ← h3]
    have h5 := Nat.gcd_eq_left (hζ.2 _ h4)
    rw [Nat.pow_sub_one_gcd_pow_sub_one] at h5
    have h6 : q ^ n.gcd j = q ^ n := by
      have : 1 ≤ q ^ n.gcd j := Nat.one_le_pow _ _ (by omega)
      omega
    exact Nat.gcd_eq_left_iff_dvd.1 (Nat.pow_right_injective hq1 h6)

omit [IsAlgClosure F Ω] in
/- English proof (translation)
Use `⟨fun a ha g ↦ ⟨(g * a * g⁻¹).2, fun x hx ↦ ?_⟩⟩` and prove the remaining obligations. Establish `h1 : A.valuation (g.1⁻¹ x) ≤ 1`. Rewrite `hx`, the goal using `[ValuationSubring.valuation_le_one_iff]`. Conclude with `((mem_dec A).1 (inv_mem g.2) x).2 hx`. Establish `h2` using `(dec_lt A g.2 _).2 (ha.2 _ h1)`.

Rewrite `h2` using `[map_sub, show g.1 (g.1⁻¹ x) = x from g.1.apply_symm_apply x]`. Conclude with `h2`.
-/
private theorem ine_normal : ((Ine (F := F) A).subgroupOf (Dec A)).Normal := by
  refine ⟨fun a ha g ↦ ⟨(g * a * g⁻¹).2, fun x hx ↦ ?_⟩⟩
  have h1 : A.valuation (g.1⁻¹ x) ≤ 1 := by
    rw [ValuationSubring.valuation_le_one_iff] at hx ⊢
    exact ((mem_dec A).1 (inv_mem g.2) x).2 hx
  have h2 := (dec_lt A g.2 _).2 (ha.2 _ h1)
  rw [map_sub, show g.1 (g.1⁻¹ x) = x from g.1.apply_symm_apply x] at h2
  exact h2

end Fr

end UpperTheory.Reformulated.B.RootEquality

/- English proof (translation)
Introduce `l _ F Ω _ _ _ _ _ A v C _ _ χ h _ hl`. Take `⟨φ, hφ, hφ'⟩` from `UpperTheory.Reformulated.B.RootEquality.exists_frob h`. Use `UpperTheory.Reformulated.B.RootEquality.ine_normal (F := F) (A := A)` as an intermediate fact. Conclude with `UpperTheory.Reformulated.B.RootEquality.count χ hl _ ⟨φ, hφ⟩ (UpperTheory.Reformulated.B.RootEquality.dense h ⟨φ, hφ⟩ hφ') (UpperTheory.Reformulated.B.RootEquality.levels h ⟨φ, hφ⟩ hφ')`.
-/
theorem UpperTheory.Reformulated.B.RootEquality.unrBare :
    ∀ (l : Nat) [Fact (Nat.Prime l)] (F Ω : Type) [inst : Field F] [inst_1 : @NumberField F inst] [inst_2 : Field Ω]
      [inst_3 :
        @Algebra F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))]
      [@IsAlgClosure F Ω (@Field.toCommRing F inst) inst_2 inst_3

          (@Module.Flat.isTorsionFree F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
            (@Semiring.toAddCommMonoid Ω
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))))
            (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
              (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
            (@Module.Flat.instOfIsDedekindDomainOfIsTorsionFree F Ω (@Field.toCommRing F inst)
              (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
              (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
                (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
              (@IsPrincipalIdealRing.isDedekindDomain F (@Field.toCommRing F inst)
                (@IsDomain.of_isSimpleRing F (@Field.toCommRing F inst)
                  (@DivisionRing.isSimpleRing F (@Field.toDivisionRing F inst)))
                (@IsPrincipalIdealRing.of_isSimpleRing F (@Field.toCommRing F inst)
                  (@DivisionRing.isSimpleRing F (@Field.toDivisionRing F inst))))
              (@Module.Flat.isTorsionFree F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                (@AddCommGroup.toAddCommMonoid Ω
                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                (@Module.FaithfullyFlat.toFlat F Ω (@Field.toCommRing F inst)
                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                  (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                  (@Module.FaithfullyFlat.instOfNontrivialOfFree F Ω (@Field.toCommRing F inst)
                    (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                    (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)
                    (@IsLocalRing.toNontrivial Ω
                      (@CommSemiring.toSemiring Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2)))
                      (@UpperTheory.V.Alg.IsCO.toIsLocalRing Ω Ω (@Field.toCommRing Ω inst_2)
                        (@HenselianLocalRing.toIsLocalRing Ω (@Field.toCommRing Ω inst_2) (@Field.henselian Ω inst_2))
                        (@Field.toCommRing Ω inst_2)
                        (@Algebra.id Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2)))
                        (@UpperTheory.V.Alg.IsCO.self Ω (@Field.toCommRing Ω inst_2)
                          (@HenselianLocalRing.toIsLocalRing Ω (@Field.toCommRing Ω inst_2) (@Field.henselian Ω inst_2))
                          (@instIsNoetherianRingOfIsArtinianRing Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))
                            (@instIsArtinianOfIsSemisimpleModuleOfFinite Ω
                              (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                              (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                              (@Semiring.toModule Ω
                                (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                              (@IsSemisimpleRing.isSemisimpleModule Ω
                                (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                (@Semiring.toModule Ω
                                  (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                (@instIsSemisimpleModuleOfIsSimpleModule Ω
                                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                  (@Semiring.toModule Ω
                                    (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                  (@instIsSimpleModule Ω (@Field.toDivisionRing Ω inst_2))))
                              (@Module.Invertible.instFinite Ω Ω (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2))
                                (@AddCommGroup.toAddCommMonoid Ω
                                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                (@Semiring.toModule Ω
                                  (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                (@Module.Invertible.inst Ω (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2))))))
                          (@UpperTheory.V.Alg.IsCO.complete Ω Ω (@Field.toCommRing Ω inst_2)

                            (@HenselianLocalRing.toIsLocalRing Ω (@Field.toCommRing Ω inst_2) (@Field.henselian Ω inst_2))
                            (@Field.toCommRing Ω inst_2)
                            (@Algebra.id Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2)))
                            (@UpperTheory.V.Alg.IsCO.self Ω (@Field.toCommRing Ω inst_2)
                              (@HenselianLocalRing.toIsLocalRing Ω (@Field.toCommRing Ω inst_2) (@Field.henselian Ω inst_2))
                              (@instIsNoetherianRingOfIsArtinianRing Ω
                                (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))
                                (@instIsArtinianOfIsSemisimpleModuleOfFinite Ω
                                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                  (@Semiring.toModule Ω
                                    (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                  (@IsSemisimpleRing.isSemisimpleModule Ω
                                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                    (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                    (@Semiring.toModule Ω
                                      (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                    (@instIsSemisimpleModuleOfIsSimpleModule Ω
                                      (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                      (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                      (@Semiring.toModule Ω
                                        (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                      (@instIsSimpleModule Ω (@Field.toDivisionRing Ω inst_2))))
                                  (@Module.Invertible.instFinite Ω Ω
                                    (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2))
                                    (@AddCommGroup.toAddCommMonoid Ω
                                      (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                    (@Semiring.toModule Ω
                                      (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                    (@Module.Invertible.inst Ω
                                      (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2))))))
                              (@instIsAdicCompleteMaximalIdealOfIsArtinianRing Ω (@Field.toCommRing Ω inst_2)
                                (@instIsArtinianOfIsSemisimpleModuleOfFinite Ω
                                  (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                  (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                  (@Semiring.toModule Ω
                                    (@CommSemiring.toSemiring Ω (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2))))
                                  (@IsSemisimpleRing.isSemisimpleModule Ω
                                    (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                    (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                    (@Semiring.toModule Ω
                                      (@CommSemiring.toSemiring Ω
                                        (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2))))
                                    (@instIsSemisimpleModuleOfIsSimpleModule Ω
                                      (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)) Ω
                                      (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                                      (@Semiring.toModule Ω
                                        (@Ring.toSemiring Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                      (@instIsSimpleModule Ω (@Field.toDivisionRing Ω inst_2))))
                                  (@Module.Invertible.instFinite Ω Ω
                                    (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2))
                                    (@AddCommGroup.toAddCommMonoid Ω
                                      (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2))))
                                    (@Semiring.toModule Ω
                                      (@CommSemiring.toSemiring Ω
                                        (@CommRing.toCommSemiring Ω (@Field.toCommRing Ω inst_2))))
                                    (@Module.Invertible.inst Ω
                                      (@Semifield.toCommSemiring Ω (@Field.toSemifield Ω inst_2)))))
                                (@HenselianLocalRing.toIsLocalRing Ω (@Field.toCommRing Ω inst_2)
                                  (@Field.henselian Ω inst_2))))))))

                    (@Module.Free.of_divisionRing F Ω (@Field.toDivisionRing F inst)
                      (@Ring.toAddCommGroup Ω (@DivisionRing.toRing Ω (@Field.toDivisionRing Ω inst_2)))
                      (@Algebra.toModule F Ω (@CommRing.toCommSemiring F (@Field.toCommRing F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                        inst_3)))))))]
      (A : @ValuationSubring Ω inst_2)
      (v :
        @IsDedekindDomain.HeightOneSpectrum (@NumberField.RingOfIntegers F inst)
          (@NumberField.instCommRingRingOfIntegers F inst))
      (C : Type) [inst_5 : CommGroup C] [Finite C]
      (χ :
        @MonoidHom (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A)) C
          (@MulOneClass.toMulOne (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
            (@Monoid.toMulOneClass (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
              (@DivInvMonoid.toMonoid (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                (@Group.toDivInvMonoid (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                  (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)
                    (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))))))
          (@MulOneClass.toMulOne C
            (@Monoid.toMulOneClass C (@DivInvMonoid.toMonoid C (@Group.toDivInvMonoid C (@CommGroup.toGroup C inst_5)))))),
      @UpperTheory.Reformulated.B.RootEquality.IsPlaceOver F Ω inst inst_2 inst_3 A v →
        @IsOpen (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
            (@instTopologicalSpaceSubtype (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
              (fun (x : @UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) ↦
                @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3))
                  (@SetLike.instMembership
                    (@Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                        inst_3))
                    (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                        inst_3)))
                  (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A) x)
              (@krullTopology F Ω inst inst_2 inst_3))
            (@SetLike.coe
              (@Subgroup (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                  (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A)))
              (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
              (@Subgroup.instSetLike (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                  (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A)))
              (@MonoidHom.ker (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)

                  (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                C
                (@Monoid.toMulOneClass C (@DivInvMonoid.toMonoid C (@Group.toDivInvMonoid C (@CommGroup.toGroup C inst_5))))
                χ)) →
          (Nat.card C).Coprime l →
            @UpperTheory.Reformulated.B.RootEquality.UnrCount l (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
              (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                  (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
              (@instTopologicalSpaceSubtype (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                (fun (x : @UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3) ↦
                  @Membership.mem (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                        (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                        inst_3))
                    (@SetLike.instMembership
                      (@Subgroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                        (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                          inst_3))
                      (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                      (@Subgroup.instSetLike (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                        (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                          (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                          inst_3)))
                    (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A) x)
                (@krullTopology F Ω inst inst_2 inst_3))
              (@Min.min
                (@Subgroup (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                  (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)
                    (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A)))
                (@Subgroup.instMin (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                  (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)
                    (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A)))
                (@Subgroup.subgroupOf (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                  (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                    (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2))) inst_3)
                  (@UpperTheory.Reformulated.B.RootEquality.Ine F Ω inst inst_1 inst_2 inst_3 A) (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                (@MonoidHom.ker (↥(@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                  (@Subgroup.toGroup (@UpperTheory.Reformulated.B.RootEquality.G F Ω inst inst_2 inst_3)
                    (@AlgEquiv.aut F Ω (@Semifield.toCommSemiring F (@Field.toSemifield F inst))
                      (@DivisionSemiring.toSemiring Ω (@Semifield.toDivisionSemiring Ω (@Field.toSemifield Ω inst_2)))
                      inst_3)
                    (@UpperTheory.Reformulated.B.RootEquality.Dec F Ω inst inst_2 inst_3 A))
                  C
                  (@Monoid.toMulOneClass C
                    (@DivInvMonoid.toMonoid C (@Group.toDivInvMonoid C (@CommGroup.toGroup C inst_5))))
                  χ)) := by
  intro l _ F Ω _ _ _ _ _ A v C _ _ χ h _ hl
  obtain ⟨φ, hφ, hφ'⟩ := UpperTheory.Reformulated.B.RootEquality.exists_frob h
  have := UpperTheory.Reformulated.B.RootEquality.ine_normal (F := F) (A := A)
  exact UpperTheory.Reformulated.B.RootEquality.count χ hl _ ⟨φ, hφ⟩ (UpperTheory.Reformulated.B.RootEquality.dense h ⟨φ, hφ⟩ hφ')
    (UpperTheory.Reformulated.B.RootEquality.levels h ⟨φ, hφ⟩ hφ')
