import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ExpandsPullOne
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdExpPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.ProdFam
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TWMain
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.QuadraticAlgebraValuation
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DvrLem
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsRepresentativesModNsmul
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsBoxPullGen
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.RankAndGOfIsPowDeg
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.UniformisationPowerWithoutExpansionStatement
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.SecScalBoxSecGPre
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.IsBoxSecKOfPull
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ImportsBis
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.CrossEq
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.BoxFamLinearIndependent
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.IntegralFamilyOfStrictMin
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.HasBasisOfBasis
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.ExistsTwistBasisOffPrime

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.DVR
attribute [local instance] Over.cartesianMonoidalCategory
open scoped CategoryTheory.Obj

namespace GlobalTheory.UnifPower

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Take `rfl : φ' = fun a => h ≫ φ a` from `funext hφ`. Take `⟨t, ht, s, hs⟩` from `TwistLoc.exists_clear_denominator M H hL φ ε s'`. Use `⟨t, ht, s, fun y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[sval_of s (𝟙 _ ≫ h) y J (fun a => J (𝟙 _ ≫ h ≫ φ a)) (fun a => by rw [Category.assoc])]`. Use `(hs _ (𝟙 _) y _ (hJ.mem (fun a => h ≫ φ a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations.

Rewrite using `[H.w, ← Category.assoc]`. Conclude with `cst_comp _ (algebraMap R Rm) y t`.
-/
theorem exists_clear {R Rm : Type} [CommRing R] [CommRing Rm] [Algebra R Rm] (M : Submonoid R) [IsLocalization M Rm]
    {X Y Y' : Scheme.{0}} {π : Y ⟶ Spec (CommRingCat.of R)} {π' : Y' ⟶ Spec (CommRingCat.of Rm)} {h : Y' ⟶ Y}
    (H : IsPullback h π' π (Spec.map (CommRingCat.ofHom (algebraMap R Rm))))
    [CompactSpace Y] [QuasiSeparatedSpace Y] {L : LB X} (hL : L.IsLB) {K : Type} [Fintype K]
    (φ : K → (Y ⟶ X)) (ε : K → ℤ) (φ' : K → (Y' ⟶ X)) (hφ : ∀ a, φ' a = h ≫ φ a)
    (s' : LB.Sec (LB.LinComb L φ' ε)) :
    ∃ t ∈ M, ∃ s : LB.Sec (LB.LinComb L φ ε), ∀ (y : Y') (J : (Y' ⟶ X) → L.ι), Good L y J →
      sval s (𝟙 _ ≫ h) y J = cst (𝟙 _ ≫ π') y (algebraMap R Rm t) * sval s' (𝟙 _) y J := by
  obtain rfl : φ' = fun a => h ≫ φ a := funext hφ
  obtain ⟨t, ht, s, hs⟩ := TwistLoc.exists_clear_denominator M H hL φ ε s'
  refine ⟨t, ht, s, fun y J hJ => ?_⟩
  rw [sval_of s (𝟙 _ ≫ h) y J (fun a => J (𝟙 _ ≫ h ≫ φ a)) (fun a => by rw [Category.assoc])]
  refine (hs _ (𝟙 _) y _ (hJ.mem (fun a => h ≫ φ a) (𝟙 _))).trans (congrArg₂ (· * ·) ?_ rfl)
  rw [H.w, ← Category.assoc]
  exact cst_comp _ (algebraMap R Rm) y t

variable {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] (D : DegData V (maximalIdeal V))

/- English proof (translation)
Establish `hL` using `D.toPre.P.isLB`. Use `D.toPre.P.isAb.proper` as an intermediate fact. Establish `: CompactSpace D.toPre.P.A.left` using `QuasiCompact.compactSpace_of_compactSpace D.toPre.P.A.hom`. Establish `: QuasiSeparatedSpace D.toPre.P.A.left` using `(quasiSeparated_iff_quasiSeparatedSpace D.toPre.P.A.hom).mp inferInstance`. Establish `hid : jFK (R` using `V) (FractionRing V) ≫ jK V = jK V := (congrArg (· ≫ jK V) (Spec.map_id _ : jFK (R := V) (FractionRing V) = 𝟙 _)).trans (Category.id_comp _)`.

Establish `H₀ : IsPullback (DegPre.prB D.toPre (FractionRing V)).left (fst (TF (R` using `V) (FractionRing V)) D.toPre.P.A).left D.toPre.P.A.hom (jFK (R := V) (FractionRing V) ≫ jK V) := (IsPullback.of_hasPullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).flip`. Rewrite `H₀` using `[hid]`. Take `⟨t, ht, σ, hσ⟩` from `exists_clear (nonZeroDivisors V) H₀ hL (D.toPre.famφB α) (DegPre.famε k) _ (GC.famφ_eq D.toPre (FractionRing V) α) s`. Take `⟨σF, hσF⟩` from `FamInt.exists_pull (D := D) (F := FractionRing V) σ`. Establish `ht0 : algebraMap V (FractionRing V) t ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht`.

Take `⟨r, hr⟩` from `WithTop.ne_top_iff_exists.1 (fun h => inv_ne_zero ht0 ((AddValuation.top_iff v).1 h) : v (algebraMap V (FractionRing V) t)⁻¹ ≠ ⊤)`. Use `⟨r, 1, fun _ => (algebraMap V (FractionRing V) t)⁻¹, fun _ => σ, fun _ => σF, fun _ => hσF, fun _ => hr.le, fun j => ?_⟩` and prove the remaining obligations. Use `(sec_ext_val hL (s' := FamInt.secLin (fun _ : Fin 1 => gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) t)⁻¹) (fun _ => σF)) (fun y J hJ => ?_) j).trans rfl` and prove the remaining obligations. Rewrite using `[SectionScalarValuation.sval_lin (s := FamInt.secLin _ _) (fun _ : Fin 1 => gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) t)⁻¹) (fun _ : Fin 1 => σF) (fun _ => rfl) _ y hJ, Fin.sum_univ_one, ← SectionScalarValuation.secScal_sval hσF _ y hJ, hσ y J hJ, ← _root_.mul_as …`. Establish `e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) t)⁻¹) = cst (𝟙 _ ≫ (fst (TF (R` using `V) (FractionRing V)) D.toPre.P.A).left) y (algebraMap V (FractionRing V) t)⁻¹ := gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _`.

Rewrite using `[e2]`. Use `(_root_.one_mul _).symm.trans (congrArg₂ (· * ·) ?_ rfl)` and prove the remaining obligations. Use `Eq.trans ?_ (TwistLoc.gc_mul _ y _ _)` and prove the remaining obligations. Rewrite using `[inv_mul_cancel₀ ht0, TwistLoc.gc, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]`.
-/
theorem exists_vge (v : AddValuation (FractionRing V) (WithTop ℚ)) {k : ℕ} {α : D.toPre.X}
    (s : LB.Sec (LB.LinComb D.toPre.P.L (DegPre.famφ D.toPre (FractionRing V) α) (DegPre.famε k))) :
    ∃ r : ℚ, VGe D (FractionRing V) v k α s r := by
  have hL := D.toPre.P.isLB
  have := D.toPre.P.isAb.proper
  have : CompactSpace D.toPre.P.A.left := QuasiCompact.compactSpace_of_compactSpace D.toPre.P.A.hom
  have : QuasiSeparatedSpace D.toPre.P.A.left :=
    (quasiSeparated_iff_quasiSeparatedSpace D.toPre.P.A.hom).mp inferInstance
  have hid : jFK (R := V) (FractionRing V) ≫ jK V = jK V :=
    (congrArg (· ≫ jK V) (Spec.map_id _ : jFK (R := V) (FractionRing V) = 𝟙 _)).trans (Category.id_comp _)
  have H₀ : IsPullback (DegPre.prB D.toPre (FractionRing V)).left
      (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left D.toPre.P.A.hom (jFK (R := V) (FractionRing V) ≫ jK V) :=
    (IsPullback.of_hasPullback (TF (R := V) (FractionRing V)).hom D.toPre.P.A.hom).flip
  rw [hid] at H₀
  obtain ⟨t, ht, σ, hσ⟩ := exists_clear (nonZeroDivisors V) H₀ hL (D.toPre.famφB α) (DegPre.famε k) _
    (GC.famφ_eq D.toPre (FractionRing V) α) s
  obtain ⟨σF, hσF⟩ := FamInt.exists_pull (D := D) (F := FractionRing V) σ
  have ht0 : algebraMap V (FractionRing V) t ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors ht
  obtain ⟨r, hr⟩ := WithTop.ne_top_iff_exists.1
    (fun h => inv_ne_zero ht0 ((AddValuation.top_iff v).1 h) : v (algebraMap V (FractionRing V) t)⁻¹ ≠ ⊤)
  refine ⟨r, 1, fun _ => (algebraMap V (FractionRing V) t)⁻¹, fun _ => σ, fun _ => σF, fun _ => hσF,
    fun _ => hr.le, fun j => ?_⟩
  refine (sec_ext_val hL (s' := FamInt.secLin (fun _ : Fin 1 => gF D.toPre (FractionRing V)
    (algebraMap V (FractionRing V) t)⁻¹) (fun _ => σF)) (fun y J hJ => ?_) j).trans rfl
  rw [SectionScalarValuation.sval_lin (s := FamInt.secLin _ _) (fun _ : Fin 1 => gF D.toPre (FractionRing V)
    (algebraMap V (FractionRing V) t)⁻¹) (fun _ : Fin 1 => σF) (fun _ => rfl) _ y hJ, Fin.sum_univ_one,
    ← SectionScalarValuation.secScal_sval hσF _ y hJ, hσ y J hJ, ← _root_.mul_assoc]
  have e2 : gs (𝟙 _) y ⊤ (gF D.toPre (FractionRing V) (algebraMap V (FractionRing V) t)⁻¹) =
      cst (𝟙 _ ≫ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left) y (algebraMap V (FractionRing V) t)⁻¹ :=
    gs_pull _ (fst (TF (R := V) (FractionRing V)) D.toPre.P.A).left y ⊤ trivial _
  rw [e2]
  refine (_root_.one_mul _).symm.trans (congrArg₂ (· * ·) ?_ rfl)
  refine Eq.trans ?_ (TwistLoc.gc_mul _ y _ _)
  rw [inv_mul_cancel₀ ht0, TwistLoc.gc, map_one, gs_eq _ _ ⊤ trivial, map_one, map_one]

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `choose Q hQ using QForm.exists_QVal hϖ D`. Establish `hv` using `FamInt.valOver_ordVal hϖ`. Take `⟨b, hb, -, hsp⟩` from `hU V ϖ hϖ D Q hQ (FractionRing V) (FamInt.ordVal hϖ) hv (Or.inr ⟨1, le_rfl, fun x hx => by`. Take `⟨n, hn⟩` from `hasVal_of_ne_zero hϖ hx`.

Conclude with `⟨n, by rw [Nat.cast_one, div_one]; exact hv x n hn⟩⟩) k hk`. Use `⟨Module.Basis.mk hb fun s _ => ?_⟩` and prove the remaining obligations. Take `⟨-, e, he⟩` from `exists_representatives_mod_nsmul D.toPre.X k hk`. Use `choose r hr using fun i => exists_vge D (FamInt.ordVal hϖ) (s.s (e i))`. Choose the witnesses or unpack the hypotheses as in `⟨n, hn⟩ : ∃ n : ℕ, ∀ i, (Q (e i) : ℚ) / k - r i ≤ n := by`.

Take `⟨m, hm⟩` from `(Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove`. Take `⟨n, hn⟩` from `exists_nat_ge m`. Conclude with `⟨n, fun i => (hm ⟨i, rfl⟩).trans hn⟩`. Establish `h1 : NuGe D Q (FractionRing V) (FamInt.ordVal hϖ) k s (-n)`. Rewrite using `[n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by`.

Take `⟨i, hi, -⟩` from `he χ`. Conclude with `⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]`. Introduce `α hα`. Take `⟨i, -, rfl⟩` from `Finset.mem_image.1 hα`. Conclude with `VGe.mono (hr i) (by linarith [hn i])`.

Establish `hπ : algebraMap V (FractionRing V) ϖ ^ n ≠ 0` using `pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero)`. Establish `h2` using `NuGe.smul Q (q := n) (ζ := algebraMap V (FractionRing V) ϖ ^ n) (le_of_eq (hv (algebraMap V (FractionRing V) ϖ ^ n) n ⟨1, by simp⟩).symm) ((isSmul_iff _ s _).2 rfl) h1`. Rewrite `h2` using `[neg_add_cancel]`. Take `⟨c, -, hc⟩` from `(hsp _).1 h2`. Rewrite using `[← inv_smul_smul₀ hπ s, hc]`.

Conclude with `Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))`.
-/
theorem exists_basis (hU : UUStatement) (k : ℕ) (hk : 1 ≤ k) :
    Nonempty (Module.Basis (Fin (k ^ (D.toPre.rank + D.toPre.P.g))) (FractionRing V)
      (Fam D.toPre (FractionRing V) k)) := by
  classical
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  choose Q hQ using QForm.exists_QVal hϖ D
  have hv := FamInt.valOver_ordVal hϖ
  obtain ⟨b, hb, -, hsp⟩ := hU V ϖ hϖ D Q hQ (FractionRing V) (FamInt.ordVal hϖ) hv
    (Or.inr ⟨1, le_rfl, fun x hx => by
      obtain ⟨n, hn⟩ := hasVal_of_ne_zero hϖ hx
      exact ⟨n, by rw [Nat.cast_one, div_one]; exact hv x n hn⟩⟩) k hk
  refine ⟨Module.Basis.mk hb fun s _ => ?_⟩
  obtain ⟨-, e, he⟩ := exists_representatives_mod_nsmul D.toPre.X k hk
  choose r hr using fun i => exists_vge D (FamInt.ordVal hϖ) (s.s (e i))
  obtain ⟨n, hn⟩ : ∃ n : ℕ, ∀ i, (Q (e i) : ℚ) / k - r i ≤ n := by
    obtain ⟨m, hm⟩ := (Set.finite_range fun i => (Q (e i) : ℚ) / k - r i).bddAbove
    obtain ⟨n, hn⟩ := exists_nat_ge m
    exact ⟨n, fun i => (hm ⟨i, rfl⟩).trans hn⟩
  have h1 : NuGe D Q (FractionRing V) (FamInt.ordVal hϖ) k s (-n) := by
    rw [n1a V ϖ hϖ D Q hQ _ _ hv k hk (Finset.univ.image e) (fun χ => by
      obtain ⟨i, hi, -⟩ := he χ
      exact ⟨e i, Finset.mem_image_of_mem _ (Finset.mem_univ i), hi⟩) s]
    intro α hα
    obtain ⟨i, -, rfl⟩ := Finset.mem_image.1 hα
    exact VGe.mono (hr i) (by linarith [hn i])
  have hπ : algebraMap V (FractionRing V) ϖ ^ n ≠ 0 :=
    pow_ne_zero _ ((map_ne_zero_iff _ (IsFractionRing.injective V (FractionRing V))).mpr hϖ.ne_zero)
  have h2 := NuGe.smul Q (q := n) (ζ := algebraMap V (FractionRing V) ϖ ^ n)
    (le_of_eq (hv (algebraMap V (FractionRing V) ϖ ^ n) n ⟨1, by simp⟩).symm) ((isSmul_iff _ s _).2 rfl) h1
  rw [neg_add_cancel] at h2
  obtain ⟨c, -, hc⟩ := (hsp _).1 h2
  rw [← inv_smul_smul₀ hπ s, hc]
  exact Submodule.smul_mem _ _ (Submodule.sum_mem _ fun i _ =>
    Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩))

/- English proof (translation)
Take `⟨b, hex, huniq⟩` from `GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk`. Use `choose F hF using fun i => (hbij.1 (b i)).exists`. Establish `hlin` using `fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs`. Set `φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k` to `Fintype.linearCombination (FractionRing V) F`. Establish `hinj : Function.Injective φ`.

Introduce `c c' h`. Take `⟨s, hs⟩` from `hex c`. Take `⟨s', hs'⟩` from `hex c'`. Establish `h1 : U.Expands k s (φ c)` using `hlin c s hs`. Establish `h2 : U.Expands k s' (φ c')` using `hlin c' s' hs'`.

Rewrite `h2` using `[← h]`. Take `rfl : s = s'` from `(hbij.2 (φ c)).unique h1 h2`. Conclude with `(huniq s).unique hs hs'`. Establish `hsurj : Function.Surjective φ`. Introduce `x`.

Take `⟨s, hs⟩` from `(hbij.2 x).exists`. Take `⟨c, hc⟩` from `(huniq s).exists`. Conclude with `⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩`. Rewrite using `[← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]`. Simplify using the standard rewrite rules.
-/
theorem finrank_of_expBij (hL : Laws) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (k : ℕ) (hk : 1 ≤ k) (hbij : U.ExpBij k) :
    Module.finrank (FractionRing V) (Fam D.toPre (FractionRing V) k) = k ^ A.g := by
  obtain ⟨b, hex, huniq⟩ := GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk
  choose F hF using fun i => (hbij.1 (b i)).exists
  have hlin := fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs
  let φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k :=
    Fintype.linearCombination (FractionRing V) F
  have hinj : Function.Injective φ := by
    intro c c' h
    obtain ⟨s, hs⟩ := hex c
    obtain ⟨s', hs'⟩ := hex c'
    have h1 : U.Expands k s (φ c) := hlin c s hs
    have h2 : U.Expands k s' (φ c') := hlin c' s' hs'
    rw [← h] at h2
    obtain rfl : s = s' := (hbij.2 (φ c)).unique h1 h2
    exact (huniq s).unique hs hs'
  have hsurj : Function.Surjective φ := by
    intro x
    obtain ⟨s, hs⟩ := (hbij.2 x).exists
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, (hbij.1 s).unique (hlin c s hc) hs⟩
  rw [← (LinearEquiv.ofBijective φ ⟨hinj, hsurj⟩).finrank_eq]
  simp

/- English proof (translation)
Establish `hfun` using `ExpFun.main hL.lemmaB V D A G U k`. Take `⟨b, hex, huniq⟩` from `GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk`. Use `choose F hF using fun i => htot (b i)`. Set `φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k` to `Fintype.linearCombination (FractionRing V) F`. Establish `hlin : ∀ c s, _ → U.Expands k s (φ c)` using `fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs`.

Establish `hsurj : Function.Surjective φ`. Rewrite using `[← LinearMap.range_eq_top, eq_top_iff, ← hB.span_eq_top_of_card_eq_finrank' (hIx.trans hdim.symm), Submodule.span_le]`. Introduce and unpack `_ ⟨a, rfl⟩`. Take `⟨s, hs⟩` from `hon a`. Take `⟨c, hc⟩` from `(huniq s).exists`.

Conclude with `⟨c, hfun s _ _ (hlin c s hc) hs⟩`. Establish `hinj : Function.Injective φ` using `(LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim]; simp)).2 hsurj`. Use `⟨fun s => ?_, fun E => ?_⟩` and prove the remaining obligations. Take `⟨E, hE⟩` from `htot s`. Conclude with `⟨E, hE, fun E' hE' => hfun s _ _ hE' hE⟩`.

Take `⟨c, rfl⟩` from `hsurj E`. Take `⟨s, hs⟩` from `hex c`. Use `⟨s, hlin c s hs, fun s' hs' => SecOps.sec_ext fun j => ?_⟩` and prove the remaining obligations. Take `⟨c', hc'⟩` from `(huniq s').exists`. Take `rfl : c' = c` from `hinj (hfun s' _ _ (hlin c' s' hc') hs')`.

Conclude with `(hc' j).trans (hs j).symm`.
-/
theorem expBij_of_indep (hL : Laws) {A : PolAV (Spec (CommRingCat.of (FractionRing V)))}
    {G : Over (Spec (CommRingCat.of V))} [GrpObj G] [IsCommMonObj G] (U : UnifPre (maximalIdeal V) D A G)
    (k : ℕ) (hk : 1 ≤ k) [Module.Finite (FractionRing V) (Fam D.toPre (FractionRing V) k)]
    (hdim : Module.finrank (FractionRing V) (Fam D.toPre (FractionRing V) k) = k ^ A.g)
    (htot : ∀ s, ∃ E, U.Expands k s E) {Ix : Type} [Fintype Ix] (hIx : Fintype.card Ix = k ^ A.g)
    (B : Ix → Fam D.toPre (FractionRing V) k) (hB : LinearIndependent (FractionRing V) B)
    (hon : ∀ a, ∃ s, U.Expands k s (B a)) : U.ExpBij k := by
  have hfun := ExpFun.main hL.lemmaB V D A G U k
  obtain ⟨b, hex, huniq⟩ := GenericSectionBasis.exists_secK_basis hL.secBaseChange V _ D A G U k hk
  choose F hF using fun i => htot (b i)
  let φ : (Fin (k ^ A.g) → FractionRing V) →ₗ[FractionRing V] Fam D.toPre (FractionRing V) k :=
    Fintype.linearCombination (FractionRing V) F
  have hlin : ∀ c s, _ → U.Expands k s (φ c) :=
    fun c s hs => ExpandsFracLinear.main V _ D A G U k (k ^ A.g) c b F s hF hs
  have hsurj : Function.Surjective φ := by
    rw [← LinearMap.range_eq_top, eq_top_iff, ← hB.span_eq_top_of_card_eq_finrank' (hIx.trans hdim.symm),
      Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨s, hs⟩ := hon a
    obtain ⟨c, hc⟩ := (huniq s).exists
    exact ⟨c, hfun s _ _ (hlin c s hc) hs⟩
  have hinj : Function.Injective φ :=
    (LinearMap.injective_iff_surjective_of_finrank_eq_finrank (by rw [hdim]; simp)).2 hsurj
  refine ⟨fun s => ?_, fun E => ?_⟩
  · obtain ⟨E, hE⟩ := htot s
    exact ⟨E, hE, fun E' hE' => hfun s _ _ hE' hE⟩
  · obtain ⟨c, rfl⟩ := hsurj E
    obtain ⟨s, hs⟩ := hex c
    refine ⟨s, hlin c s hs, fun s' hs' => SecOps.sec_ext fun j => ?_⟩
    obtain ⟨c', hc'⟩ := (huniq s').exists
    obtain rfl : c' = c := hinj (hfun s' _ _ (hlin c' s' hc') hs')
    exact (hc' j).trans (hs j).symm

/- English proof (translation)
Introduce `hL hU V _ _ _ D A G _ _ U j D' A' G' _ _ pD pA pG`. Take `⟨U', wL, hyp⟩` from `GlobalTheory.T.uniformisation_power_without_expansion hL.globalFns V _ j D D' A A' G G' pD pA pG U.toUnifPre`. Establish `key : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k`. Introduce `k hk`. Take `⟨hbox, hspan⟩` from `GenericBoxSpan.main hL V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k hk`.

Establish `hexp` using `ExpandsBoxPre.main V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k`. Establish `hfam` using `BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD (FractionRing V) k`. Take `⟨b⟩` from `exists_basis D hU k hk`. Take `⟨b'⟩` from `exists_basis D' hU k hk`. Use `Module.Finite.of_basis b'` as an intermediate fact.

Establish `e₁ : k ^ (D.toPre.rank + D.toPre.P.g) = k ^ A.g`. Rewrite using `[← finrank_of_expBij D hL U.toUnifPre k hk (U.expand k hk), Module.finrank_eq_card_basis b, Fintype.card_fin]`. Establish `e₂ : A'.g = j * A.g` using `H1.dim_unique _ A'.smoothDim ((PowGrp.powers _ A'.A A.A j pA.toIsPowGrp).2.2.1 A.g A.smoothDim) (eSec A'.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)))`. Establish `e₃ : (k ^ (D.toPre.rank + D.toPre.P.g)) ^ j = k ^ A'.g` using `by rw [e₁, e₂, ← pow_mul, mul_comm]`. Take `⟨r₁, r₂⟩` from `rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD`.

Use `choose B hB using fun a : Fin j → Fin (k ^ (D.toPre.rank + D.toPre.P.g)) => hfam fun i => b (a i)`. Use `expBij_of_indep D' hL U' k hk ?_ (fun s₀ => ?_) (by rw [← e₃]; simp) B (boxFam_linearIndependent V j _ _ pD _ k _ b b.linearIndependent B hB) (fun a => ?_)` and prove the remaining obligations. Rewrite using `[Module.finrank_eq_card_basis b', Fintype.card_fin, r₁, r₂, ← mul_add, ← e₃, ← pow_mul, mul_comm]`. Take `⟨n, c, s, s', hs, hs₀⟩` from `hspan s₀ choose E hE using fun l i => ((U.expand k hk).1 (s l i)).exists choose E' hE' using fun l => hfam (E l)`. Conclude with `⟨_, ExpandsFracLinear.main V _ D' A' G' U' k n c s' E' s₀ (fun l => hexp (s l) (E l) (hE l) (s' l) (E' l) (hs l) (hE' l)) hs₀⟩`.

Use `choose s hs using fun i => ((U.expand k hk).2 (b (a i))).exists`. Take `⟨s', hs'⟩` from `hbox s`. Conclude with `⟨s', hexp s _ hs s' (B a) hs' (hB a)⟩`. Take `⟨h₁, h₂, h₃, h₄, h₅, h₆⟩` from `hyp`. Conclude with `⟨⟨U', key⟩, ⟨⟨⟨⟨h₁, wL, h₂, h₃, h₄⟩, h₅⟩, h₆⟩⟩⟩`.
-/
theorem main : Laws → UUStatement → ∀ (V : Type) [CommRing V] [IsDomain V] [IsDiscreteValuationRing V],
    UnifPowSt3 (I := maximalIdeal V) := by
  intro hL hU V _ _ _ D A G _ _ U j D' A' G' _ _ pD pA pG
  obtain ⟨U', wL, hyp⟩ := GlobalTheory.T.uniformisation_power_without_expansion hL.globalFns V _ j D D' A A' G G' pD pA pG U.toUnifPre
  have key : ∀ k : ℕ, 1 ≤ k → U'.ExpBij k := by
    intro k hk
    obtain ⟨hbox, hspan⟩ := GenericBoxSpan.main hL V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k hk
    have hexp := ExpandsBoxPre.main V _ j D D' A A' G G' pD pA pG U' U.toUnifPre wL hyp k
    have hfam := BoxFamily.exists_isBoxFam hL.globalFns V j D.toPre D'.toPre pD (FractionRing V) k
    obtain ⟨b⟩ := exists_basis D hU k hk
    obtain ⟨b'⟩ := exists_basis D' hU k hk
    have := Module.Finite.of_basis b'
    have e₁ : k ^ (D.toPre.rank + D.toPre.P.g) = k ^ A.g := by
      rw [← finrank_of_expBij D hL U.toUnifPre k hk (U.expand k hk), Module.finrank_eq_card_basis b,
        Fintype.card_fin]
    have e₂ : A'.g = j * A.g :=
      H1.dim_unique _ A'.smoothDim ((PowGrp.powers _ A'.A A.A j pA.toIsPowGrp).2.2.1 A.g A.smoothDim)
        (eSec A'.A (⟨⊥, Ideal.isPrime_bot⟩ : PrimeSpectrum (FractionRing V)))
    have e₃ : (k ^ (D.toPre.rank + D.toPre.P.g)) ^ j = k ^ A'.g := by rw [e₁, e₂, ← pow_mul, mul_comm]
    obtain ⟨r₁, r₂⟩ := rank_and_g_of_isPowDeg V j D.toPre D'.toPre pD
    choose B hB using fun a : Fin j → Fin (k ^ (D.toPre.rank + D.toPre.P.g)) => hfam fun i => b (a i)
    refine expBij_of_indep D' hL U' k hk ?_ (fun s₀ => ?_) (by rw [← e₃]; simp) B
      (boxFam_linearIndependent V j _ _ pD _ k _ b b.linearIndependent B hB) (fun a => ?_)
    · rw [Module.finrank_eq_card_basis b', Fintype.card_fin, r₁, r₂, ← mul_add, ← e₃, ← pow_mul, mul_comm]
    · obtain ⟨n, c, s, s', hs, hs₀⟩ := hspan s₀
      choose E hE using fun l i => ((U.expand k hk).1 (s l i)).exists
      choose E' hE' using fun l => hfam (E l)
      exact ⟨_, ExpandsFracLinear.main V _ D' A' G' U' k n c s' E' s₀
        (fun l => hexp (s l) (E l) (hE l) (s' l) (E' l) (hs l) (hE' l)) hs₀⟩
    · choose s hs using fun i => ((U.expand k hk).2 (b (a i))).exists
      obtain ⟨s', hs'⟩ := hbox s
      exact ⟨s', hexp s _ hs s' (B a) hs' (hB a)⟩
  obtain ⟨h₁, h₂, h₃, h₄, h₅, h₆⟩ := hyp
  exact ⟨⟨U', key⟩, ⟨⟨⟨⟨h₁, wL, h₂, h₃, h₄⟩, h₅⟩, h₆⟩⟩⟩

end GlobalTheory.UnifPower
