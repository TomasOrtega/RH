import Formalism.LocalToGlobal.ProjectiveLattices.GenSectB

noncomputable section

namespace Formalism.L2.Pj.GenSect

open MvPolynomial
open scoped TensorProduct

variable {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {D m : ℕ}

/- English proof (translation)
Use `show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q`. Rewrite using `[MvPolynomial.aeval_map_algebraMap]`.
-/
theorem psi_kt (x : Fin m → Ω) (j₀ : Fin m) (q : KT K D m) :
    psi x j₀ (ktToΩ K Ω D m q) = aeval (gs x j₀) q := by
  show aeval (gs x j₀) (MvPolynomial.map (algebraMap K Ω) q) = aeval (gs x j₀) q
  rw [MvPolynomial.aeval_map_algebraMap]

/- English proof (translation)
Conclude with `IsLocalization.map_eq _ _`.
-/
theorem algKTR_apply (q : KT K D m) :
    algebraMap (KTf K D m) (RS K Ω D m) (algebraMap (KT K D m) (KTf K D m) q) =
      algebraMap (ΩT Ω D m) (RS K Ω D m) (ktToΩ K Ω D m q) := by
  exact IsLocalization.map_eq _ _

def Phi (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    RS K Ω D m →+* FractionRing (CT Ω D j₀) :=
  IsLocalization.lift (M := KTS K Ω D m)
    (g := (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (psi x j₀).toRingHom) (by
      rintro ⟨s, hs⟩
      obtain ⟨q, hq, rfl⟩ := hs
      refine isUnit_iff_ne_zero.mpr ?_
      show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ (ktToΩ K Ω D m q)) ≠ 0
      rw [psi_kt]
      exact fun h => hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm)))

/- English proof (translation)
The claim follows from `IsLocalization.lift_eq _ _`.
-/
theorem Phi_algebraMap (x : Fin m → Ω) (j₀ : Fin m) (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0)
    (a : ΩT Ω D m) :
    Phi x j₀ hinj (algebraMap (ΩT Ω D m) (RS K Ω D m) a) =
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) :=
  IsLocalization.lift_eq _ _

/- English proof (translation)
The claim follows from `IsLocalization.lift_mk'_spec _ _ _ _`.
-/
theorem Phi_mk'_spec (x : Fin m → Ω) (j₀ : Fin m)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) (a : ΩT Ω D m) (y : KTS K Ω D m)
    (v : FractionRing (CT Ω D j₀)) :
    Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) a y) = v ↔
      algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ a) =
        algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) * v :=
  IsLocalization.lift_mk'_spec _ _ _ _

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Rewrite using `[Is, Ideal.span_le]`. Introduce and unpack `_ ⟨i, rfl⟩`. Simplify using `only [SetLike.mem_coe, RingHom.mem_ker, Phi_algebraMap, psi_sec x j₀ hx₀ i, map_zero]`. Introduce `r hr`.

Rewrite `hr` using `[RingHom.mem_ker]`. Take `⟨⟨a, y⟩, rfl⟩` from `IsLocalization.mk'_surjective (KTS K Ω D m) r`. Simplify using `only at hr ⊢`. Rewrite `hr` using `[Phi_mk'_spec, mul_zero, ← map_zero (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))), (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).eq_iff, psi_eq_zero_iff x j₀ hx₀]`. Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one]`.

Apply `Ideal.mul_mem_right` to reduce the goal to its premises. Establish `hle : Ideal.map (algebraMap (ΩT Ω D m) (RS K Ω D m)) (Ideal.span (Set.range (sec x))) ≤ Is K x`. Rewrite using `[Ideal.map_span, Is]`. Apply `Ideal.span_mono` to reduce the goal to its premises. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`.

Conclude with `⟨i, rfl⟩`. Conclude with `hle (Ideal.mem_map_of_mem _ hr)`.
-/
theorem ker_Phi (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0) :
    Is K x = RingHom.ker (Phi x j₀ hinj) := by
  apply le_antisymm
  · rw [Is, Ideal.span_le]
    rintro _ ⟨i, rfl⟩
    simp only [SetLike.mem_coe, RingHom.mem_ker, Phi_algebraMap, psi_sec x j₀ hx₀ i, map_zero]
  · intro r hr
    rw [RingHom.mem_ker] at hr
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only at hr ⊢
    rw [Phi_mk'_spec, mul_zero, ← map_zero (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))),
      (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).eq_iff,
      psi_eq_zero_iff x j₀ hx₀] at hr
    rw [IsLocalization.mk'_eq_mul_mk'_one]
    apply Ideal.mul_mem_right
    have hle : Ideal.map (algebraMap (ΩT Ω D m) (RS K Ω D m)) (Ideal.span (Set.range (sec x))) ≤ Is K x := by
      rw [Ideal.map_span, Is]
      apply Ideal.span_mono
      rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
      exact ⟨i, rfl⟩
    exact hle (Ideal.mem_map_of_mem _ hr)

/- English proof (translation)
Establish `halg` using `halg_of x j₀ htr hbig`. Establish `hind` using `gs_indep x j₀ hx₀ htr halg`. Establish `hal` using `gs_alg x j₀ hx₀ htr halg`. Establish `hI : Function.Injective (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀)` using `hind`. Establish `hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0` using `fun q hq h => hq (hI (h.trans (map_zero _).symm))`.

Set `χ : KT K D m →+* FractionRing (CT Ω D j₀)` to `(algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀).toRingHom`. Establish `hχ : Function.Injective χ` using `(IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp hI`. Use `letI : Algebra (KT K D m) (FractionRing (CT Ω D j₀)) := χ.toAlgebra`. Use `letI : Algebra (KTf K D m) (FractionRing (CT Ω D j₀)) := (IsFractionRing.lift hχ).toAlgebra`. Use `haveI : IsScalarTower (KT K D m) (KTf K D m) (FractionRing (CT Ω D j₀)) := IsScalarTower.of_algebraMap_eq fun q => (IsFractionRing.lift_algebraMap hχ q).symm`.

Establish `key : ∀ r : KTf K D m, Phi x j₀ hinj (algebraMap (KTf K D m) (RS K Ω D m) r) = IsFractionRing.lift hχ r`. Establish `h : (Phi x j₀ hinj).comp (algebraMap (KTf K D m) (RS K Ω D m)) = IsFractionRing.lift hχ`. Use `IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`. Rewrite using `[algKTR_apply, Phi_algebraMap, psi_kt, IsFractionRing.lift_algebraMap]`.

Both sides reduce to the same expression. Conclude with `fun r => RingHom.congr_fun h r`. Set `ΦK : RS K Ω D m →ₐ[KTf K D m] FractionRing (CT Ω D j₀)` to `{ Phi x j₀ hinj with commutes' := key }`. Establish `hint : ∀ c : CT Ω D j₀, IsIntegral (KTf K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c)`. Introduce `c`.

Use `haveI := hal`. Take `⟨p, hp0, hp⟩` from `Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range (gs (D := D) x j₀))) c`. Set `e` to `hind.aevalEquiv`. Establish `hKT : IsAlgebraic (KT K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c)`. Use `⟨p.map (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m), ?_, ?_⟩` and prove the remaining obligations.

Conclude with `(Polynomial.map_ne_zero_iff e.symm.injective).2 hp0`. Rewrite using `[Polynomial.aeval_def, Polynomial.eval₂_map]`. Establish `hcomp : (algebraMap (KT K D m) (FractionRing (CT Ω D j₀))).comp (e.symm : Algebra.adjoin K (Set.range (gs (D` using `D) x j₀)) →+* KT K D m) = (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp (algebraMap (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀)) := by`. Use `RingHom.ext fun a => ?_` and prove the remaining obligations. Simplify using `only [RingHom.comp_apply]`.

Use `show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (e.symm a)) = _`. Rewrite using `[← hind.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]`. Rewrite using `[hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]`. Conclude with `(hKT.extendScalars (IsFractionRing.injective (KT K D m) (KTf K D m))).isIntegral`. Take `⟨t, ht⟩` from `hfg`.

Set `G : Set (FractionRing (CT Ω D j₀))` to `Set.range (fun v => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (X v)) ∪ (fun ω => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω)) '' (t : Set Ω)`. Use `haveI : Finite G := ((Set.finite_range _).union (t.finite_toSet.image _)).to_subtype`. Set `E'` to `IntermediateField.adjoin (KTf K D m) G`. Use `haveI hfd : FiniteDimensional (KTf K D m) E' := IntermediateField.finiteDimensional_adjoin (by`. Apply the tactic sequence `rintro _ (⟨v, rfl⟩ | ⟨ω, _, rfl⟩) <;> exact hint _)`.

Establish `hK : ∀ k : K, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) ∈ E'`. Introduce `k`. Establish `e1 : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) = algebraMap (KTf K D m) (FractionRing (CT Ω D j₀)) (algebraMap (KT K D m) (KTf K D m) (MvPolynomial.C k))`. Rewrite using `[← IsScalarTower.algebraMap_apply]`. Use `show _ = algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (MvPolynomial.C k))`.

Rewrite using `[MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]`. Rewrite using `[e1]`. Conclude with `E'.algebraMap_mem _`. Establish `hΩ : ∀ ω : Ω, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω) ∈ E'`. Set `θ : Ω →+* FractionRing (CT Ω D j₀)` to `(algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp MvPolynomial.C`.

Set `Si : IntermediateField K Ω` to `Subfield.toIntermediateField (E'.toSubfield.comap θ) (fun k => hK k)`. Establish `hle : IntermediateField.adjoin K (t : Set Ω) ≤ Si`. Rewrite using `[IntermediateField.adjoin_le_iff]`. Introduce `ω hω`. Conclude with `IntermediateField.subset_adjoin (KTf K D m) G (Or.inr ⟨ω, hω, rfl⟩)`.

Introduce `ω`. Establish `hω : ω ∈ IntermediateField.adjoin K (t : Set Ω)`. Rewrite using `[ht]`. Conclude with `IntermediateField.mem_top`. Conclude with `hle hω`.

Establish `hmemC : ∀ c : CT Ω D j₀, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c ∈ E'`. Introduce `c`. Apply `MvPolynomial.induction_on c` to reduce the goal to its premises. Introduce `ω`. Conclude with `hΩ ω`.

Introduce `p q hp hq`. Rewrite using `[map_add]`. Conclude with `add_mem hp hq`. Introduce `p v hp`. Rewrite using `[map_mul]`.

Conclude with `mul_mem hp (IntermediateField.subset_adjoin (KTf K D m) G (Or.inl ⟨v, rfl⟩))`. Establish `hrange : ∀ r : RS K Ω D m, Phi x j₀ hinj r ∈ E'`. Introduce `r`. Take `⟨⟨a, y⟩, rfl⟩` from `IsLocalization.mk'_surjective (KTS K Ω D m) r`. Simplify using `only`.

Rewrite using `[IsLocalization.mk'_eq_mul_mk'_one, map_mul, Phi_algebraMap]`. Use `mul_mem (hmemC _) ?_` and prove the remaining obligations. Establish `hy : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) ≠ 0`. Take `⟨q, hq, hqy⟩` from `y.2`. Rewrite using `[← hqy, psi_kt]`.

Introduce `h`. Conclude with `hinj q (nonZeroDivisors.ne_zero hq) ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm))`. Establish `h1 : Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) (1 : ΩT Ω D m) y) = (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y))⁻¹`. Rewrite using `[Phi_mk'_spec, map_one, map_one, mul_inv_cancel₀ hy]`. Rewrite using `[h1]`.

Conclude with `inv_mem (hmemC _)`. Set `S` to `ΦK.range`. Set `L : S →ₗ[KTf K D m] E'` to `{ toFun := fun s => ⟨s.1, by`. Take `⟨r, hr⟩` from `(AlgHom.mem_range ΦK).1 s.2`. Rewrite using `[← hr]`.

Conclude with `hrange r⟩`. Use the proof step `map_add' := fun _ _ => rfl`. Use the proof step `map_smul' := fun _ _ => rfl }`. Use `haveI : FiniteDimensional (KTf K D m) S := FiniteDimensional.of_injective L (by`. Introduce `a b h`.

Establish `h'` using `congrArg (fun e : E' => (e : FractionRing (CT Ω D j₀))) h`. Conclude with `Subtype.ext h')`. Establish `hSf : IsField S` using `(Algebra.IsIntegral.isField_iff_isField (algebraMap (KTf K D m) S).injective).1 (Field.toIsField _)`. Set `E` to `S.toIntermediateField' hSf`. Set `g : RS K Ω D m →ₐ[KTf K D m] E` to `{ toFun := fun r => ⟨ΦK r, ΦK.mem_range_self r⟩ map_one' := Subtype.ext (map_one ΦK) map_mul' := fun a b => Subtype.ext (map_mul ΦK a b) map_zero' := Subtype.ext (map_zero ΦK) map_add' := fun a b => Subtype.ext (map_add ΦK a b) commutes' := fun r => Subtype.ext (ΦK.commutes r) }`.

Establish `hg : Function.Surjective g`. Introduce and unpack `⟨v, hv⟩`. Take `⟨r, rfl⟩` from `(AlgHom.mem_range ΦK).1 (show v ∈ S from hv)`. Conclude with `⟨r, rfl⟩`. Establish `hker : RingHom.ker g = Is K x`.

Rewrite using `[ker_Phi x j₀ hx₀ hinj]`. Use extensionality with `r`. Simplify using `only [RingHom.mem_ker]`. Prove the components needed by the constructor for the conclusion. Introduce `h`.

Conclude with `congrArg Subtype.val h`. Introduce `h`. Conclude with `Subtype.ext h`. Use `⟨E, inferInstance, inferInstance, ?_, ⟨(Ideal.quotientEquivAlgOfEq (KTf K D m) hker.symm).trans (Ideal.quotientKerAlgEquivOfSurjective hg)⟩⟩` and prove the remaining obligations. Conclude with `FiniteDimensional.of_injective ({ toFun := fun e => (⟨e.1, e.2⟩ : S), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } : E →ₗ[KTf K D m] S) (by`.

Introduce `a b h`. Establish `h'` using `congrArg (fun e : S => (e : FractionRing (CT Ω D j₀))) h`. Conclude with `Subtype.ext h')`.
-/
theorem quotient_generic_section_field [CharZero K] (hfg : (⊤ : IntermediateField K Ω).FG) (htr : Algebra.trdeg K Ω = D)
    (x : Fin m → Ω) (j₀ : Fin m) (hx₀ : x j₀ ≠ 0)
    (hbig : Algebra.trdeg K (IntermediateField.adjoin K (Set.range fun j => x j / x j₀)) = D) :
    ∃ (E : Type) (_ : Field E) (_ : Algebra (KTf K D m) E), FiniteDimensional (KTf K D m) E ∧
      Nonempty ((RS K Ω D m ⧸ Is K x) ≃ₐ[KTf K D m] E) := by
  classical
  have halg := halg_of x j₀ htr hbig
  have hind := gs_indep x j₀ hx₀ htr halg
  have hal := gs_alg x j₀ hx₀ htr halg
  have hI : Function.Injective (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀) := hind
  have hinj : ∀ q : KT K D m, q ≠ 0 → aeval (gs x j₀) q ≠ 0 := fun q hq h =>
    hq (hI (h.trans (map_zero _).symm))
  let χ : KT K D m →+* FractionRing (CT Ω D j₀) :=
    (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
      (aeval (gs x j₀) : KT K D m →ₐ[K] CT Ω D j₀).toRingHom
  have hχ : Function.Injective χ :=
    (IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp hI
  letI : Algebra (KT K D m) (FractionRing (CT Ω D j₀)) := χ.toAlgebra
  letI : Algebra (KTf K D m) (FractionRing (CT Ω D j₀)) := (IsFractionRing.lift hχ).toAlgebra
  haveI : IsScalarTower (KT K D m) (KTf K D m) (FractionRing (CT Ω D j₀)) :=
    IsScalarTower.of_algebraMap_eq fun q => (IsFractionRing.lift_algebraMap hχ q).symm
  have key : ∀ r : KTf K D m, Phi x j₀ hinj (algebraMap (KTf K D m) (RS K Ω D m) r) =
      IsFractionRing.lift hχ r := by
    have h : (Phi x j₀ hinj).comp (algebraMap (KTf K D m) (RS K Ω D m)) = IsFractionRing.lift hχ := by
      refine IsLocalization.ringHom_ext (nonZeroDivisors (KT K D m)) (RingHom.ext fun q => ?_)
      simp only [RingHom.comp_apply]
      rw [algKTR_apply, Phi_algebraMap, psi_kt, IsFractionRing.lift_algebraMap]
      rfl
    exact fun r => RingHom.congr_fun h r
  let ΦK : RS K Ω D m →ₐ[KTf K D m] FractionRing (CT Ω D j₀) :=
    { Phi x j₀ hinj with commutes' := key }
  have hint : ∀ c : CT Ω D j₀,
      IsIntegral (KTf K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
    intro c
    haveI := hal
    obtain ⟨p, hp0, hp⟩ := Algebra.IsAlgebraic.isAlgebraic (R := Algebra.adjoin K (Set.range (gs (D := D) x j₀))) c
    let e := hind.aevalEquiv
    have hKT : IsAlgebraic (KT K D m) (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c) := by
      refine ⟨p.map (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m), ?_, ?_⟩
      · exact (Polynomial.map_ne_zero_iff e.symm.injective).2 hp0
      · rw [Polynomial.aeval_def, Polynomial.eval₂_map]
        have hcomp : (algebraMap (KT K D m) (FractionRing (CT Ω D j₀))).comp
              (e.symm : Algebra.adjoin K (Set.range (gs (D := D) x j₀)) →+* KT K D m) =
            (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp
              (algebraMap (Algebra.adjoin K (Set.range (gs (D := D) x j₀))) (CT Ω D j₀)) := by
          refine RingHom.ext fun a => ?_
          simp only [RingHom.comp_apply]
          show algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (e.symm a)) = _
          rw [← hind.algebraMap_aevalEquiv, AlgEquiv.apply_symm_apply]
        rw [hcomp, ← Polynomial.hom_eval₂, ← Polynomial.aeval_def, hp, map_zero]
    exact (hKT.extendScalars (IsFractionRing.injective (KT K D m) (KTf K D m))).isIntegral
  obtain ⟨t, ht⟩ := hfg
  let G : Set (FractionRing (CT Ω D j₀)) :=
    Set.range (fun v => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (X v)) ∪
      (fun ω => algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω)) '' (t : Set Ω)
  haveI : Finite G := ((Set.finite_range _).union (t.finite_toSet.image _)).to_subtype
  let E' := IntermediateField.adjoin (KTf K D m) G
  haveI hfd : FiniteDimensional (KTf K D m) E' := IntermediateField.finiteDimensional_adjoin (by
    rintro _ (⟨v, rfl⟩ | ⟨ω, _, rfl⟩) <;> exact hint _)
  have hK : ∀ k : K, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))
      (MvPolynomial.C (algebraMap K Ω k)) ∈ E' := by
    intro k
    have e1 : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C (algebraMap K Ω k)) =
        algebraMap (KTf K D m) (FractionRing (CT Ω D j₀))
          (algebraMap (KT K D m) (KTf K D m) (MvPolynomial.C k)) := by
      rw [← IsScalarTower.algebraMap_apply]
      show _ = algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (aeval (gs x j₀) (MvPolynomial.C k))
      rw [MvPolynomial.aeval_C, MvPolynomial.algebraMap_apply]
    rw [e1]
    exact E'.algebraMap_mem _
  have hΩ : ∀ ω : Ω, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (MvPolynomial.C ω) ∈ E' := by
    let θ : Ω →+* FractionRing (CT Ω D j₀) :=
      (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀))).comp MvPolynomial.C
    let Si : IntermediateField K Ω := Subfield.toIntermediateField (E'.toSubfield.comap θ) (fun k => hK k)
    have hle : IntermediateField.adjoin K (t : Set Ω) ≤ Si := by
      rw [IntermediateField.adjoin_le_iff]
      intro ω hω
      exact IntermediateField.subset_adjoin (KTf K D m) G (Or.inr ⟨ω, hω, rfl⟩)
    intro ω
    have hω : ω ∈ IntermediateField.adjoin K (t : Set Ω) := by
      rw [ht]
      exact IntermediateField.mem_top
    exact hle hω
  have hmemC : ∀ c : CT Ω D j₀, algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) c ∈ E' := by
    intro c
    apply MvPolynomial.induction_on c
    · intro ω
      exact hΩ ω
    · intro p q hp hq
      rw [map_add]
      exact add_mem hp hq
    · intro p v hp
      rw [map_mul]
      exact mul_mem hp (IntermediateField.subset_adjoin (KTf K D m) G (Or.inl ⟨v, rfl⟩))
  have hrange : ∀ r : RS K Ω D m, Phi x j₀ hinj r ∈ E' := by
    intro r
    obtain ⟨⟨a, y⟩, rfl⟩ := IsLocalization.mk'_surjective (KTS K Ω D m) r
    dsimp only
    rw [IsLocalization.mk'_eq_mul_mk'_one, map_mul, Phi_algebraMap]
    refine mul_mem (hmemC _) ?_
    have hy : algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y) ≠ 0 := by
      obtain ⟨q, hq, hqy⟩ := y.2
      rw [← hqy, psi_kt]
      intro h
      exact hinj q (nonZeroDivisors.ne_zero hq)
        ((IsFractionRing.injective (CT Ω D j₀) (FractionRing (CT Ω D j₀))) (h.trans (map_zero _).symm))
    have h1 : Phi x j₀ hinj (IsLocalization.mk' (RS K Ω D m) (1 : ΩT Ω D m) y) =
        (algebraMap (CT Ω D j₀) (FractionRing (CT Ω D j₀)) (psi x j₀ y))⁻¹ := by
      rw [Phi_mk'_spec, map_one, map_one, mul_inv_cancel₀ hy]
    rw [h1]
    exact inv_mem (hmemC _)
  let S := ΦK.range
  let L : S →ₗ[KTf K D m] E' :=
    { toFun := fun s => ⟨s.1, by
        obtain ⟨r, hr⟩ := (AlgHom.mem_range ΦK).1 s.2
        rw [← hr]
        exact hrange r⟩
      map_add' := fun _ _ => rfl
      map_smul' := fun _ _ => rfl }
  haveI : FiniteDimensional (KTf K D m) S :=
    FiniteDimensional.of_injective L (by
      intro a b h
      have h' := congrArg (fun e : E' => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')
  have hSf : IsField S :=
    (Algebra.IsIntegral.isField_iff_isField (algebraMap (KTf K D m) S).injective).1 (Field.toIsField _)
  let E := S.toIntermediateField' hSf
  let g : RS K Ω D m →ₐ[KTf K D m] E :=
    { toFun := fun r => ⟨ΦK r, ΦK.mem_range_self r⟩
      map_one' := Subtype.ext (map_one ΦK)
      map_mul' := fun a b => Subtype.ext (map_mul ΦK a b)
      map_zero' := Subtype.ext (map_zero ΦK)
      map_add' := fun a b => Subtype.ext (map_add ΦK a b)
      commutes' := fun r => Subtype.ext (ΦK.commutes r) }
  have hg : Function.Surjective g := by
    rintro ⟨v, hv⟩
    obtain ⟨r, rfl⟩ := (AlgHom.mem_range ΦK).1 (show v ∈ S from hv)
    exact ⟨r, rfl⟩
  have hker : RingHom.ker g = Is K x := by
    rw [ker_Phi x j₀ hx₀ hinj]
    ext r
    simp only [RingHom.mem_ker]
    constructor
    · intro h
      exact congrArg Subtype.val h
    · intro h
      exact Subtype.ext h
  refine ⟨E, inferInstance, inferInstance, ?_, ⟨(Ideal.quotientEquivAlgOfEq (KTf K D m) hker.symm).trans
    (Ideal.quotientKerAlgEquivOfSurjective hg)⟩⟩
  exact FiniteDimensional.of_injective
    ({ toFun := fun e => (⟨e.1, e.2⟩ : S), map_add' := fun _ _ => rfl, map_smul' := fun _ _ => rfl } :
      E →ₗ[KTf K D m] S)
    (by
      intro a b h
      have h' := congrArg (fun e : S => (e : FractionRing (CT Ω D j₀))) h
      exact Subtype.ext h')

end Formalism.L2.Pj.GenSect
