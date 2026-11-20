import Mathlib
import Development.AbelianVarietyTheory.Definitions.CMLattices.IsDiffOf
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.PelStructureDescendsFieldExtension
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.PushInvertible
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsObjOfUniformisedTripleComplex
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.MorphismsSpreadOutToFgSubalgebra
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ExistsPullback
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold

noncomputable section

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace PositivityTheory.HtPt.Kftwo

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Take `⟨R, ψ, ⟨S, rfl⟩, -, h⟩` from `GlobalTheory.Spread.exists_fg_comp_eq (A := Ω) (𝟙 (Sp K)) p (pullback.snd _ _ ≫ x) (by`. Rewrite using `[Category.assoc, hx, pullback.condition])`. Use `⟨S, fun K' hS => ?_⟩` and prove the remaining obligations. Establish `hle : Algebra.adjoin K (S : Set Ω) ≤ K'.toSubalgebra` using `Algebra.adjoin_le hS`. Set `g : Algebra.adjoin K (S : Set Ω) →+* K'` to `(Subalgebra.inclusion hle).toRingHom`.

Use `⟨spMap g ≫ inv (pullback.snd (𝟙 (Sp K)) _) ≫ ψ, ?_⟩` and prove the remaining obligations. Establish `e : spMap K'.val.toRingHom ≫ spMap g = spMap (Algebra.adjoin K (S : Set Ω)).val.toRingHom` using `(Spec.map_comp _ _).symm`. Rewrite using `[← cancel_epi (pullback.snd (𝟙 (Sp K)) (spMap (algebraMap K Ω))), ← h, ← Category.assoc (spMap _), e, ← Category.assoc, ← GlobalTheory.Spread.bcMap_snd, Category.assoc, IsIso.hom_inv_id_assoc]`.
-/
theorem exists_finset_point {K Ω : Type} [Field K] [Field Ω] [Algebra K Ω] {Z : Scheme.{0}} (p : Z ⟶ Sp K)
    [LocallyOfFinitePresentation p] (x : Sp Ω ⟶ Z) (hx : x ≫ p = spMap (algebraMap K Ω)) :
    ∃ S : Finset Ω, ∀ K' : IntermediateField K Ω, (S : Set Ω) ⊆ K' →
      ∃ y : Sp K' ⟶ Z, spMap K'.val.toRingHom ≫ y = x := by
  obtain ⟨R, ψ, ⟨S, rfl⟩, -, h⟩ := GlobalTheory.Spread.exists_fg_comp_eq (A := Ω) (𝟙 (Sp K)) p (pullback.snd _ _ ≫ x) (by
    rw [Category.assoc, hx, pullback.condition])
  refine ⟨S, fun K' hS => ?_⟩
  have hle : Algebra.adjoin K (S : Set Ω) ≤ K'.toSubalgebra := Algebra.adjoin_le hS
  let g : Algebra.adjoin K (S : Set Ω) →+* K' := (Subalgebra.inclusion hle).toRingHom
  refine ⟨spMap g ≫ inv (pullback.snd (𝟙 (Sp K)) _) ≫ ψ, ?_⟩
  have e : spMap K'.val.toRingHom ≫ spMap g = spMap (Algebra.adjoin K (S : Set Ω)).val.toRingHom :=
    (Spec.map_comp _ _).symm
  rw [← cancel_epi (pullback.snd (𝟙 (Sp K)) (spMap (algebraMap K Ω))), ← h, ← Category.assoc (spMap _), e,
    ← Category.assoc, ← GlobalTheory.Spread.bcMap_snd, Category.assoc, IsIso.hom_inv_id_assoc]

/- English proof (translation)
Use `c.fin` as an intermediate fact. Use `set r : c.F := IntermediateField.inclusion c.le (baseKA l).ρ with hr`. Establish `hr2 : r ^ 2 = -(H.d : c.F)` using `by rw [hr, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]`. Establish `hd : (0 : ℚ) < H.d` using `by exact_mod_cast H.d_prime.pos`. Establish `hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)))` using `X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by nlinarith [sq_nonneg b]`.

Establish `hmin : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ r` using `minpoly.eq_of_irreducible_of_monic hirr (by simp [hr2]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)`. Take `⟨φ, hφ⟩` from `IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := c.F) (K := Ω) (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := r) (y := ρ) (by rw [← hmin]; simp [hρ])`. Conclude with `⟨φ.toRingHom, hφ⟩`.
-/
theorem exists_coeff_embedding {l : Level H} (c : Coeff l) {Ω : Type} [Field Ω] [IsAlgClosed Ω] [CharZero Ω] (ρ : Ω)
    (hρ : ρ ^ 2 = -(H.d : Ω)) : ∃ β : c.F →+* Ω, β (IntermediateField.inclusion c.le (baseKA l).ρ) = ρ := by
  have := c.fin
  set r : c.F := IntermediateField.inclusion c.le (baseKA l).ρ with hr
  have hr2 : r ^ 2 = -(H.d : c.F) := by rw [hr, ← map_pow, (baseKA l).ρ_sq, map_neg, map_natCast]
  have hd : (0 : ℚ) < H.d := by exact_mod_cast H.d_prime.pos
  have hirr : Irreducible (Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ))) :=
    X_pow_sub_C_irreducible_of_prime Nat.prime_two fun b hb => by nlinarith [sq_nonneg b]
  have hmin : Polynomial.X ^ 2 - Polynomial.C (-(H.d : ℚ)) = minpoly ℚ r :=
    minpoly.eq_of_irreducible_of_monic hirr (by simp [hr2]) (Polynomial.monic_X_pow_sub_C _ two_ne_zero)
  obtain ⟨φ, hφ⟩ := IntermediateField.exists_algHom_of_splits_of_aeval (F := ℚ) (E := c.F) (K := Ω)
    (fun s => ⟨Algebra.IsIntegral.isIntegral s, IsAlgClosed.splits _⟩) (x := r) (y := ρ) (by rw [← hmin]; simp [hρ])
  exact ⟨φ.toRingHom, hφ⟩

/- English proof (translation)
Establish `hL` using `GlobalTheory.firstFiveLaws.1`. Establish `hM : 0 < l.M` using `lt_of_lt_of_le (by norm_num) l.three_le`. Use `c.fin` as an intermediate fact. Establish `hsm` using `T.ab.smooth`. Take `⟨β, hβ⟩` from `exists_coeff_embedding c ρ hρ`.

Establish `hcard` using `(hL.mulN _ T.pol l.M hM).2.2.2.2 _ (spMap (algebraMap K (AlgebraicClosure K))) (Nat.cast_ne_zero.2 hM.ne')`. Establish `hfin : Finite {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1}` using `Nat.finite_of_card_ne_zero (by erw [hcard]; positivity)`. Use `choose S hS using fun x : {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} => exists_finset_point T.t.G.hom x.1.left (Over.w x.1)`. Set `b` to `Module.finBasis ℚ c.F`. Set `U : Set (AlgebraicClosure K)` to `(⋃ x, (S x : Set (AlgebraicClosure K))) ∪ Set.range fun i => β (b i)`.

Establish `hU : Finite U` using `((Set.finite_iUnion fun x => (S x).finite_toSet).union (Set.finite_range _)).to_subtype`. Set `K'` to `IntermediateField.adjoin K U`. Establish `hfd : FiniteDimensional K K'` using `IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x`. Establish `hβm : ∀ z, β z ∈ K'` using `fun z => by`. Rewrite using `[← b.sum_repr z, map_sum]`.

Use `sum_mem fun i _ => ?_` and prove the remaining obligations. Rewrite using `[Rat.smul_def, map_mul, map_ratCast]`. Conclude with `mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin K U (Or.inr ⟨i, rfl⟩))`. Set `β' : c.F →+* K'` to `β.codRestrict K' hβm`. Set `i : K' →+* AlgebraicClosure K` to `K'.val.toRingHom`.

Establish `hi : spMap (algebraMap K (AlgebraicClosure K)) = spMap i ≫ spMap (algebraMap K K')` using `Spec.map_comp (CommRingCat.ofHom (algebraMap K K')) (CommRingCat.ofHom i)`. Take `⟨T', m, -⟩` from `GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap K K')) T`. Establish `hm : LBIso T'.t.PP.L (T.t.PP.L.pull m.φ)`. Take `⟨w, hw, -⟩` from `m.lin`. Conclude with `⟨w, hw⟩`.

Take `⟨I', -, hI'⟩` from `(GlobalTheory.PELDesc.tate_pull (D := D) T.t.PP.isLB T'.t.PP.isLB m.cart hm T.t.act.act T'.t.act.act m.act _ _ hi).2 I`. Establish `hdet' : DetCond D T'.t.act (spMap i) ρ` using `(GlobalTheory.PELDesc.detCond_pull m.cart _ _ m.act _ _ hi ρ).2 hdet`. Establish `hepi : Epi (spMap i)`. Use `GlobalTheory.FieldBaseChange.flat_spMap i` as an intermediate fact. Use `GlobalTheory.FieldBaseChange.surjective_spMap i` as an intermediate fact.

Use the proof step `Flat.epi_of_flat_of_surjective _`. Establish `hex : ∀ a, ∃ e : 𝟙_ (Over (Sp K')) ⟶ T'.t.G, toUnit (Over.mk (spMap i)) ≫ e = I'.ev l.M a` using `fun a => by`. Take `⟨y, hy⟩` from `hS ⟨I.ev l.M a, (I.onto _ hM _).2 ⟨a, rfl⟩⟩ K' fun z hz => IntermediateField.subset_adjoin K U (Or.inl (Set.mem_iUnion.2 ⟨_, hz⟩))`. Use `replace hy : spMap i ≫ y = (I.ev l.M a).left := hy`. Establish `w : y ≫ T.t.G.hom = 𝟙 _ ≫ spMap (algebraMap K K')`.

Rewrite using `[← cancel_epi (spMap i), ← Category.assoc, hy, Category.id_comp, ← hi]`. Conclude with `Over.w (I.ev l.M a)`. Use `⟨Over.homMk (m.cart.1.lift y _ w) (m.cart.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩` and prove the remaining obligations. Rewrite using `[Over.comp_left, Over.toUnit_left]`. Use `show spMap i ≫ m.cart.1.lift y _ w = _`.

Use `m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations. Rewrite using `[Category.assoc, IsPullback.lift_fst, hy]`. Conclude with `hI' _ _`. Rewrite using `[Category.assoc, IsPullback.lift_snd, Category.comp_id]`. Conclude with `(Over.w (I'.ev l.M a)).symm`.

Use `choose e he using hex`. Establish `inj` using `GlobalTheory.HeckePoint.toUnit_comp_injective (spMap i) T'.t.G`. Take `⟨u, hu, π, hπ, huπ⟩` from `Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)`. Establish `hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La), I'.ev l.M (π • a) = I'.ev l.M a` using `fun a h => by conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I'.add, (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq l.prod hu h), _root_.one_mul]`. Set `κ : KA l →+* K'` to `β'.comp (IntermediateField.inclusion c.le).toRingHom`.

Establish `hsm'` using `T'.ab.smooth`. Set `o : Obj D l (baseKA l) (spMap κ)` to `{ t := T'.t proper := T'.ab.proper ample := T'.ample ktriv := T'.ktriv eta := fun a => e (π • a) eta_add := fun a c => inj (by show toUnit _ ≫ _ = toUnit _ ≫ _`. Rewrite using `[MonObj.comp_mul, he, he, he, smul_add, I'.add])`. Use `eta_ker := fun a h => inj (by show toUnit _ ≫ _ = toUnit _ ≫ _`. Rewrite using `[MonObj.comp_one, he]`.

Conclude with `(I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h))`. Use `etaA := fun _ => 1`. Use `etaA_add := fun _ _ => (_root_.mul_one _).symm`. Use `etaA_ker := fun _ => rfl`. Use `geom := fun k _ _ x δ hx => by`.

Take `⟨φ, rfl⟩ : ∃ φ : K' →+* k, x = spMap φ` from `⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩`. Take `rfl : φ.comp κ = δ` from `congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))`. Choose the witnesses or unpack the hypotheses as in `⟨ψ, rfl⟩ : ∃ ψ : AlgebraicClosure K →+* k, ψ.comp i = φ := by`. Use `letI := φ.toAlgebra`. Conclude with `⟨(IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).toRingHom, RingHom.ext fun z => (IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).commutes z⟩`.

Establish `hx' : spMap (ψ.comp i) = spMap ψ ≫ spMap i` using `Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom ψ)`. Rewrite using `[hx']`. Take `⟨J, hJ⟩` from `(GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T'.pol T'.t.act.act _ k ψ (spMap i)).1 I'`. Use `⟨?_, J, ?_, fun a => ?_, fun a h => ?_⟩` and prove the remaining obligations. Use `(GlobalTheory.detCond_iff_of_field_extension E H D _ T'.t.G _ k ψ (spMap i) T'.t.act ρ hsm').2 hdet'` as an intermediate fact.

Rewrite `this` using `[← hβ]`. Conclude with `this`. Establish `h₁` using `J.ζ_prim _ l.A_pos`. Establish `h₂` using `(baseKA l).ζ_prim`. Rewrite `h₁`, `h₂` using `[hA, IsPrimitiveRoot.one_right_iff]`.

Rewrite using `[hA, h₁, h₂, map_one, Units.val_one]`. Rewrite using `[hA, MonObj.comp_one]`. Conclude with `((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm`. Use `Eq.trans ?_ ((hJ _ hM).2 a).symm` and prove the remaining obligations. Rewrite using `[← hη a h, ← he, ← Category.assoc]`.

Conclude with `congrArg (· ≫ e (π • a)) (toUnit_unique _ _) }`. Take `⟨f, ⟨hf, ⟨n⟩⟩, -⟩` from `Xo.rep _ (spMap κ) inferInstance o`. Establish `hκ : f ≫ Xo.s = spMap β' ≫ spMap (IntermediateField.inclusion c.le).toRingHom` using `hf.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom β'))`. Use `⟨K', hfd, pullback.lift f _ hκ, T'.t, ⟨m⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[pullback.lift_fst]`.

Conclude with `⟨n.toSABMap⟩`.
-/
theorem exists_point {D : Datum H} {l : Level H} (hA : l.A = 1) (Xo : Moduli D l) (c : Coeff l) {K : Type} [Field K]
    [CharZero K] (T : GlobalTheory.CM.PAT H (Sp K)) (ρ : AlgebraicClosure K) (hρ : ρ ^ 2 = -(H.d : AlgebraicClosure K))
    (hdet : DetCond D T.t.act (spMap (algebraMap K (AlgebraicClosure K))) ρ)
    (I : TateIso D (AlgebraicClosure K) (Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G)
      (fun a g => g ≫ T.t.act.act a) (fun n g g' c => Out.WeilIs T.t.G T.t.PP.L n g g' (unitOn c))) :
    ∃ (K' : IntermediateField K (AlgebraicClosure K)) (_ : FiniteDimensional K K') (y : Sp K' ⟶ Xo.XF c)
      (t' : SAB H (Sp K')), Nonempty (SABMap t' T.t (spMap (algebraMap K K'))) ∧
        Nonempty (SABMap t' Xo.univ.t (y ≫ pullback.fst _ _)) := by
  classical
  have hL := GlobalTheory.firstFiveLaws.1
  have hM : 0 < l.M := lt_of_lt_of_le (by norm_num) l.three_le
  have := c.fin
  have hsm := T.ab.smooth
  obtain ⟨β, hβ⟩ := exists_coeff_embedding c ρ hρ
  have hcard := (hL.mulN _ T.pol l.M hM).2.2.2.2 _ (spMap (algebraMap K (AlgebraicClosure K))) (Nat.cast_ne_zero.2 hM.ne')
  have hfin : Finite {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} :=
    Nat.finite_of_card_ne_zero (by erw [hcard]; positivity)
  choose S hS using fun x : {x : Over.mk (spMap (algebraMap K (AlgebraicClosure K))) ⟶ T.t.G // x ^ l.M = 1} =>
    exists_finset_point T.t.G.hom x.1.left (Over.w x.1)
  let b := Module.finBasis ℚ c.F
  let U : Set (AlgebraicClosure K) := (⋃ x, (S x : Set (AlgebraicClosure K))) ∪ Set.range fun i => β (b i)
  have hU : Finite U := ((Set.finite_iUnion fun x => (S x).finite_toSet).union (Set.finite_range _)).to_subtype
  let K' := IntermediateField.adjoin K U
  have hfd : FiniteDimensional K K' :=
    IntermediateField.finiteDimensional_adjoin fun x _ => Algebra.IsIntegral.isIntegral x
  have hβm : ∀ z, β z ∈ K' := fun z => by
    rw [← b.sum_repr z, map_sum]
    refine sum_mem fun i _ => ?_
    rw [Rat.smul_def, map_mul, map_ratCast]
    exact mul_mem (SubfieldClass.ratCast_mem _ _) (IntermediateField.subset_adjoin K U (Or.inr ⟨i, rfl⟩))
  let β' : c.F →+* K' := β.codRestrict K' hβm
  let i : K' →+* AlgebraicClosure K := K'.val.toRingHom
  have hi : spMap (algebraMap K (AlgebraicClosure K)) = spMap i ≫ spMap (algebraMap K K') :=
    Spec.map_comp (CommRingCat.ofHom (algebraMap K K')) (CommRingCat.ofHom i)
  obtain ⟨T', m, -⟩ := GlobalTheory.CM.PAT.exists_pullback E H _ _ (spMap (algebraMap K K')) T
  have hm : LBIso T'.t.PP.L (T.t.PP.L.pull m.φ) := by
    obtain ⟨w, hw, -⟩ := m.lin
    exact ⟨w, hw⟩
  obtain ⟨I', -, hI'⟩ := (GlobalTheory.PELDesc.tate_pull (D := D) T.t.PP.isLB T'.t.PP.isLB m.cart hm T.t.act.act T'.t.act.act m.act
    _ _ hi).2 I
  have hdet' : DetCond D T'.t.act (spMap i) ρ := (GlobalTheory.PELDesc.detCond_pull m.cart _ _ m.act _ _ hi ρ).2 hdet
  have hepi : Epi (spMap i) :=
    have := GlobalTheory.FieldBaseChange.flat_spMap i
    have := GlobalTheory.FieldBaseChange.surjective_spMap i
    Flat.epi_of_flat_of_surjective _
  have hex : ∀ a, ∃ e : 𝟙_ (Over (Sp K')) ⟶ T'.t.G, toUnit (Over.mk (spMap i)) ≫ e = I'.ev l.M a := fun a => by
    obtain ⟨y, hy⟩ := hS ⟨I.ev l.M a, (I.onto _ hM _).2 ⟨a, rfl⟩⟩ K' fun z hz =>
      IntermediateField.subset_adjoin K U (Or.inl (Set.mem_iUnion.2 ⟨_, hz⟩))
    replace hy : spMap i ≫ y = (I.ev l.M a).left := hy
    have w : y ≫ T.t.G.hom = 𝟙 _ ≫ spMap (algebraMap K K') := by
      rw [← cancel_epi (spMap i), ← Category.assoc, hy, Category.id_comp, ← hi]
      exact Over.w (I.ev l.M a)
    refine ⟨Over.homMk (m.cart.1.lift y _ w) (m.cart.1.lift_snd _ _ _), Over.OverMorphism.ext ?_⟩
    rw [Over.comp_left, Over.toUnit_left]
    show spMap i ≫ m.cart.1.lift y _ w = _
    refine m.cart.1.hom_ext ?_ ?_
    · rw [Category.assoc, IsPullback.lift_fst, hy]
      exact hI' _ _
    · rw [Category.assoc, IsPullback.lift_snd, Category.comp_id]
      exact (Over.w (I'.ev l.M a)).symm
  choose e he using hex
  have inj := GlobalTheory.HeckePoint.toUnit_comp_injective (spMap i) T'.t.G
  obtain ⟨u, hu, π, hπ, huπ⟩ := Submodule.mem_sup.1 ((Ideal.eq_top_iff_one _).1 l.coprime)
  have hη : ∀ a ∈ l.Mb.map (H.bar : 𝓞 E →+* 𝓞 E) • (⊤ : Submodule (𝓞 E) D.La),
      I'.ev l.M (π • a) = I'.ev l.M a := fun a h => by
    conv_rhs => rw [← one_smul (𝓞 E) a, ← huπ, add_smul, I'.add,
      (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq l.prod hu h), _root_.one_mul]
  let κ : KA l →+* K' := β'.comp (IntermediateField.inclusion c.le).toRingHom
  have hsm' := T'.ab.smooth
  let o : Obj D l (baseKA l) (spMap κ) :=
    { t := T'.t
      proper := T'.ab.proper
      ample := T'.ample
      ktriv := T'.ktriv
      eta := fun a => e (π • a)
      eta_add := fun a c => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_mul, he, he, he, smul_add, I'.add])
      eta_ker := fun a h => inj (by
        show toUnit _ ≫ _ = toUnit _ ≫ _
        rw [MonObj.comp_one, he]
        exact (I'.ker _ hM _).2 (GlobalTheory.UnifObj.exists_smul_eq ((mul_comm _ _).trans l.prod) hπ h))
      etaA := fun _ => 1
      etaA_add := fun _ _ => (_root_.mul_one _).symm
      etaA_ker := fun _ => rfl
      geom := fun k _ _ x δ hx => by
        obtain ⟨φ, rfl⟩ : ∃ φ : K' →+* k, x = spMap φ := ⟨(Spec.preimage x).hom, (Spec.map_preimage x).symm⟩
        obtain rfl : φ.comp κ = δ :=
          congrArg CommRingCat.Hom.hom (Spec.map_injective ((Spec.map_comp _ _).trans hx))
        obtain ⟨ψ, rfl⟩ : ∃ ψ : AlgebraicClosure K →+* k, ψ.comp i = φ := by
          letI := φ.toAlgebra
          exact ⟨(IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).toRingHom,
            RingHom.ext fun z => (IsAlgClosed.lift (R := K') (S := AlgebraicClosure K) (M := k)).commutes z⟩
        have hx' : spMap (ψ.comp i) = spMap ψ ≫ spMap i := Spec.map_comp (CommRingCat.ofHom i) (CommRingCat.ofHom ψ)
        rw [hx']
        obtain ⟨J, hJ⟩ := (GlobalTheory.TateIsoFieldExt.tateIso_fieldExt hL E H D _ T'.pol T'.t.act.act _ k ψ (spMap i)).1 I'
        refine ⟨?_, J, ?_, fun a => ?_, fun a h => ?_⟩
        · have := (GlobalTheory.detCond_iff_of_field_extension E H D _ T'.t.G _ k ψ (spMap i) T'.t.act ρ hsm').2 hdet'
          rw [← hβ] at this
          exact this
        · have h₁ := J.ζ_prim _ l.A_pos
          have h₂ := (baseKA l).ζ_prim
          rw [hA, IsPrimitiveRoot.one_right_iff] at h₁ h₂
          rw [hA, h₁, h₂, map_one, Units.val_one]
        · rw [hA, MonObj.comp_one]
          exact ((J.ker 1 one_pos a).2 ⟨a, (one_smul _ _).symm⟩).symm
        · refine Eq.trans ?_ ((hJ _ hM).2 a).symm
          rw [← hη a h, ← he, ← Category.assoc]
          exact congrArg (· ≫ e (π • a)) (toUnit_unique _ _) }
  obtain ⟨f, ⟨hf, ⟨n⟩⟩, -⟩ := Xo.rep _ (spMap κ) inferInstance o
  have hκ : f ≫ Xo.s = spMap β' ≫ spMap (IntermediateField.inclusion c.le).toRingHom :=
    hf.trans (Spec.map_comp (CommRingCat.ofHom _) (CommRingCat.ofHom β'))
  refine ⟨K', hfd, pullback.lift f _ hκ, T'.t, ⟨m⟩, ?_⟩
  rw [pullback.lift_fst]
  exact ⟨n.toSABMap⟩

end PositivityTheory.HtPt.Kftwo
