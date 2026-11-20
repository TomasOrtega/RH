import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SymTupOne
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaPointNormalisedThetaConstant
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGeneratorThetaConstantsOverAlgClosedExtens
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.ExistsGeneratorOfIsField
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.AllUniformizationLawsHold
import Development.AbelianVarietyTheory.Statements.TorsionEndomorphisms.EndDeterminedOnTorsion
import Development.AbelianVarietyTheory.Statements.PlaceShiftStatements.MinSt2
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.ZM GlobalTheory.ZH GlobalTheory.UMin GlobalTheory.UPoinc GlobalTheory.Ex.OneGen
open scoped CategoryTheory.Obj
attribute [local instance] Over.cartesianMonoidalCategory

noncomputable section
namespace GlobalTheory.UMin

/- English proof (translation)
Establish `hL` using `P.isLB`. Take `⟨α₀, hα₀⟩` from `hLaw.mulPull _ P k`. Establish `e₁ : (snd T' P.A).left ≫ (mulA P.A k).left = (snd T' P.A ^ k).left`. Rewrite using `[← Over.comp_left, MonObj.comp_pow, Category.comp_id]`. Take `⟨α, hα, -⟩` from `exists_gen hL (φ' := ![(snd T' P.A).left, (snd T' P.A ^ k).left]) (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)]) (fun U _ f => by`.

Use `Finset.prod_congr rfl fun i _ => ?_` and prove the remaining obligations. Use `fin_cases i`. Conclude with `congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow k 2).symm`. Conclude with `congrArg (fun q => f q ^ (-1 : ℤ)) e₁)`. Use the proof step `(LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T' P.A).left)`.

Use the proof step `(DVR.pullGen_isGen _ _ _ _ hα₀ _)`. Take `⟨τ, hτ, -⟩` from `exists_gen hL (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) (ε' := fun _ => ((k ^ 2 : ℕ) : ℤ)) (fun U _ f => by`. Rewrite using `[Fintype.prod_unique, Fin.prod_univ_one]`. Conclude with `congrArg₂ (fun q n => f q ^ n) rfl (by simp))`. Use the proof step `(GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T').left) (k ^ 2))`.

Use the proof step `(DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)`. Take `⟨s₁, hs₁⟩` from `ThetaPtExist.exists_isTwistPull hL (mulT P.A T' k) (snd T' P.A ^ k) (lift_snd _ _) ((k ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th`. Take `⟨s₂, hs₂⟩` from `ThetaPtExist.exists_isTwistPull hL (translT P.A U.pt) (translPt P.A U.pt) (lift_snd _ _) ((k ^ 2 : ℕ) : ℤ) ((k ^ 2 : ℕ) : ℤ) U.φ U.isGen s₁`. Take `⟨w, hw⟩` from `ThetaPtExist.exists_isValueAt hL s₂ 1 τ hτ`. Take `⟨e, he⟩` from `exists_thG hL hρ k _ rfl (x := fun _ : Unit => y) (fun _ => hy) (th := th) (α := α) (U := fun _ => U) (s₂ := fun _ => s₂) (w := fun _ => w) hα hτ hs₁ (fun _ => hU) (fun _ => hs₂) (fun _ => hw)`.

Conclude with `⟨_, he ()⟩`.
-/
theorem exists_thG_of_symLift (hLaw : Laws) {S : Scheme.{0}} [IsLocallyNoetherian S] (P : PolAV S)
    {ρ : LB.Gen (P.L.pull (eSec P.A))} (hρ : ρ.IsGen) (k : ℕ) (T' : Over S)
    (th : LB.Sec (LPow P.A P.L ((1 : ℕ) : ℤ) T')) (y : T' ⟶ P.A) (hy : y ^ (k ^ 2) = 1)
    (U : ThetaGrp P.A P.L ((k ^ 2 : ℕ) : ℤ) T') (hU : SymLift P.A P.L ((k ^ 2 : ℕ) : ℤ) (k ^ 2) y U) :
    ∃ c, ThG P.A P.L ρ k th y c := by
  have hL := P.isLB
  obtain ⟨α₀, hα₀⟩ := hLaw.mulPull _ P k
  have e₁ : (snd T' P.A).left ≫ (mulA P.A k).left = (snd T' P.A ^ k).left := by
    rw [← Over.comp_left, MonObj.comp_pow, Category.comp_id]
  obtain ⟨α, hα, -⟩ := exists_gen hL (φ' := ![(snd T' P.A).left, (snd T' P.A ^ k).left])
    (ε' := ![((k ^ 2 : ℕ) : ℤ), -((1 : ℕ) : ℤ)])
    (fun U _ f => by
      refine Finset.prod_congr rfl fun i _ => ?_
      fin_cases i
      · exact congrArg₂ (fun q n => f q ^ n) (Category.comp_id _) (Nat.cast_pow k 2).symm
      · exact congrArg (fun q => f q ^ (-1 : ℤ)) e₁)
    (LB.pullGen P.L ![𝟙 P.A.left, (mulA P.A k).left] ![(k : ℤ) ^ 2, -1] α₀ (snd T' P.A).left)
    (DVR.pullGen_isGen _ _ _ _ hα₀ _)
  obtain ⟨τ, hτ, -⟩ := exists_gen hL (φ' := fun _ : Fin 1 => (1 : T' ⟶ P.A).left) (ε' := fun _ => ((k ^ 2 : ℕ) : ℤ))
    (fun U _ f => by
      rw [Fintype.prod_unique, Fin.prod_univ_one]
      exact congrArg₂ (fun q n => f q ^ n) rfl (by simp))
    (GeneratorPullback.powGen P.L _ _ (LB.pullGen P.L (fun _ : PUnit => eSec P.A) (fun _ => 1) ρ (toUnit T').left) (k ^ 2))
    (DVR.powGen_isGen _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hρ _) _)
  obtain ⟨s₁, hs₁⟩ := ThetaPtExist.exists_isTwistPull hL (mulT P.A T' k) (snd T' P.A ^ k) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((1 : ℕ) : ℤ) α hα th
  obtain ⟨s₂, hs₂⟩ := ThetaPtExist.exists_isTwistPull hL (translT P.A U.pt) (translPt P.A U.pt) (lift_snd _ _)
    ((k ^ 2 : ℕ) : ℤ) ((k ^ 2 : ℕ) : ℤ) U.φ U.isGen s₁
  obtain ⟨w, hw⟩ := ThetaPtExist.exists_isValueAt hL s₂ 1 τ hτ
  obtain ⟨e, he⟩ := exists_thG hL hρ k _ rfl (x := fun _ : Unit => y) (fun _ => hy) (th := th) (α := α)
    (U := fun _ => U) (s₂ := fun _ => s₂) (w := fun _ => w) hα hτ hs₁ (fun _ => hU) (fun _ => hs₂) (fun _ => hw)
  exact ⟨_, he ()⟩

/- English proof (translation)
Introduce `S G _ _ L ρ hL hρ g m K _ x θ p hm hK hP hpm`. Take `⟨P, α, -, hp, w, hw⟩` from `hP`. Establish `hLaw : Laws` using `GlobalTheory.firstFiveLaws.1`. Establish `hL₁` using `P.isLB`. Use `P.isAb.comm` as an intermediate fact.

Take `⟨ρ', hρ', hr⟩` from `exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ`. Set `T` to `baseOver (Sp K)`. Set `τ : T.left ⟶ (Over.mk x).left` to `𝟙 (Sp K)`. Use `haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))`. Establish `hτ : τ ≫ (Over.mk x).hom = T.hom ≫ x` using `rfl`.

Take `⟨q, hq, hqm⟩` from `exists_torsion_down hp τ hτ p hpm`. Set `e` to `(Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm`. Establish `hu : IsUnit (m : Γ(Spec (CommRingCat.of K), ⊤))`. Rewrite using `[← map_natCast e]`. Conclude with `(IsUnit.mk0 _ hK).map e`.

Use `haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))`. Take `⟨z₀⟩ : Nonempty T.left` from `inferInstanceAs (Nonempty (PrimeSpectrum K))`. Take `⟨V, hV, U, hU⟩` from `(hLaw.symLift _ P (m ^ 2) hm.pow (by rw [Nat.cast_pow]; exact hu.pow 2) T q hqm).1 z₀`. Take `rfl : V = ⊤` from `eq_top_iff.2 fun y _ => by rwa [Subsingleton.elim y z₀]`. Set `T' : Over (Sp K)` to `overRes (T := T) ⊤`.

Set `j₀ : T' ⟶ T` to `overResι (T := T) ⊤`. Use `haveI : IsIso j₀.left := inferInstanceAs (IsIso (Sp K).topIso.hom)`. Set `τ' : T'.left ⟶ (Over.mk x).left` to `j₀.left ≫ τ`. Establish `hτ' : τ' ≫ (Over.mk x).hom = T'.hom ≫ x`. Rewrite using `[Category.assoc, hτ, ← Category.assoc, Over.w j₀]`.

Establish `hq' : τ' ≫ p.left = (j₀ ≫ q).left ≫ α`. Rewrite using `[Category.assoc, hq, Over.comp_left, Category.assoc]`. Establish `hqm' : (j₀ ≫ q) ^ (m ^ 2) = 1` using `by rw [← MonObj.comp_pow, hqm, MonObj.comp_one]`. Take `⟨th, hrel⟩` from `GlobalTheory.ThetaPtMove.exists_secRel hp τ' hτ' hw hL hL₁ θ`. Take `⟨c, hc⟩` from `exists_thG_of_symLift hLaw P hρ' m T' th (j₀ ≫ q) hqm' U hU`.

Establish `up` using `ThG.up hp τ' hτ' hw hL hL₁ hr hq' hpm hrel hc`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from (CategoryTheory.inv τ').appTop.hom c), ?_⟩` and prove the remaining obligations. Use `up using 1` and compare the differences between its conclusion and the goal. Conclude with `(Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _`.
-/
theorem exists_thG_of_polFib_field : ∀ (S : Scheme.{0}) (G : Over S) [GrpObj G] [IsCommMonObj G] (L : LB G.left) (ρ : LB.Gen (L.pull (eSec G))), L.IsLB → ρ.IsGen → ∀ (g m : ℕ) (F : Type) [Field F] (x : Sp F ⟶ S) (θ : SecAt G L x) (p : Over.mk x ⟶ G), Odd m → (m : F) ≠ 0 → PolFib G L g x → p ^ (m ^ 2) = 1 → ∃ c : F, ThG G L ρ m θ p (GlobalTheory.ZH.fn c) := by
  intro S G _ _ L ρ hL hρ g m K _ x θ p hm hK hP hpm
  obtain ⟨P, α, -, hp, w, hw⟩ := hP
  have hLaw : Laws := GlobalTheory.firstFiveLaws.1
  have hL₁ := P.isLB
  have := P.isAb.comm
  obtain ⟨ρ', hρ', hr⟩ := exists_rigidificationPullbackCompatibleIso hp hw hL hL₁ hρ
  let T := baseOver (Sp K)
  let τ : T.left ⟶ (Over.mk x).left := 𝟙 (Sp K)
  haveI : IsIso τ := inferInstanceAs (IsIso (𝟙 (Sp K)))
  have hτ : τ ≫ (Over.mk x).hom = T.hom ≫ x := rfl
  obtain ⟨q, hq, hqm⟩ := exists_torsion_down hp τ hτ p hpm
  let e := (Scheme.ΓSpecIso (CommRingCat.of K)).commRingCatIsoToRingEquiv.symm
  have hu : IsUnit (m : Γ(Spec (CommRingCat.of K), ⊤)) := by
    rw [← map_natCast e]
    exact (IsUnit.mk0 _ hK).map e
  haveI : Subsingleton T.left := inferInstanceAs (Subsingleton (PrimeSpectrum K))
  obtain ⟨z₀⟩ : Nonempty T.left := inferInstanceAs (Nonempty (PrimeSpectrum K))
  obtain ⟨V, hV, U, hU⟩ := (hLaw.symLift _ P (m ^ 2) hm.pow (by rw [Nat.cast_pow]; exact hu.pow 2) T q hqm).1 z₀
  obtain rfl : V = ⊤ := eq_top_iff.2 fun y _ => by rwa [Subsingleton.elim y z₀]
  let T' : Over (Sp K) := overRes (T := T) ⊤
  let j₀ : T' ⟶ T := overResι (T := T) ⊤
  haveI : IsIso j₀.left := inferInstanceAs (IsIso (Sp K).topIso.hom)
  let τ' : T'.left ⟶ (Over.mk x).left := j₀.left ≫ τ
  have hτ' : τ' ≫ (Over.mk x).hom = T'.hom ≫ x := by
    rw [Category.assoc, hτ, ← Category.assoc, Over.w j₀]
  have hq' : τ' ≫ p.left = (j₀ ≫ q).left ≫ α := by
    rw [Category.assoc, hq, Over.comp_left, Category.assoc]
  have hqm' : (j₀ ≫ q) ^ (m ^ 2) = 1 := by rw [← MonObj.comp_pow, hqm, MonObj.comp_one]
  obtain ⟨th, hrel⟩ := GlobalTheory.ThetaPtMove.exists_secRel hp τ' hτ' hw hL hL₁ θ
  obtain ⟨c, hc⟩ := exists_thG_of_symLift hLaw P hρ' m T' th (j₀ ≫ q) hqm' U hU
  have up := ThG.up hp τ' hτ' hw hL hL₁ hr hq' hpm hrel hc
  refine ⟨(Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom (show Γ(Sp K, ⊤) from (CategoryTheory.inv τ').appTop.hom c), ?_⟩
  convert up using 1
  exact (Scheme.ΓSpecIso (CommRingCat.of K)).hom_inv_id_apply _

end GlobalTheory.UMin
