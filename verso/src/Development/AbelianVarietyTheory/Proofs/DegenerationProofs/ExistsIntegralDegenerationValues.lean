import Mathlib
import Development.AbelianVarietyTheory.Definitions.Degenerations.AdmissibleBaseOfCompleteDvr
import Development.AbelianVarietyTheory.Definitions.Degenerations.HomExtSt
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.ExistsGeneratorOfBasis
import Development.AbelianVarietyTheory.Proofs.ThetaShiftProofs.ExistsPowEqOfBaseChange
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.RosVal
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.PullFEPf

open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry NumberField
open scoped CategoryTheory.Obj BigOperators
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory GlobalTheory.Ex

noncomputable section
namespace GlobalTheory.ValuesExist
open GlobalTheory.TorusExt GlobalTheory.IndivisibleSection

section Sym
variable {S : Scheme.{0}} {A : Over S} [GrpObj A] [IsCommMonObj A] {L : RigLB A} (c : CubicalStr A L)
  {s : LB.Gen (LB.LinComb L.L (K := Fin 2) ![(ι[A]).left, 𝟙 A.left] ![1, -1])}

/- English proof (translation)
Rewrite using `[Fin.prod_univ_two]`. Simplify using `[Hom.inv_def]`.
-/
theorem prod_sym {T : Over S} (x : T ⟶ A) {U : Type} [CommGroup U] (h : (T.left ⟶ A.left) → U) :
    ∏ k : Fin 2, h (x.left ≫ ![(ι[A]).left, 𝟙 A.left] k) ^ (![1, -1] : Fin 2 → ℤ) k =
      h (x⁻¹).left * (h x.left)⁻¹ := by
  rw [Fin.prod_univ_two]
  simp [Hom.inv_def]

/- English proof (translation)
Use `val_corr hJ hr (toUnit T).left` as an intermediate fact. Rewrite `this` using `[val_one, val_pull hJ]`. Conclude with `this`.
-/
theorem val_sym_one (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) : val s (1 : T ⟶ A).left z J = 1 := by
  have := val_corr hJ hr (toUnit T).left
  rw [val_one, val_pull hJ] at this
  exact this

/- English proof (translation)
Establish `vs : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (r : T ⟶ A ⊗ A) (a : A ⊗ A ⟶ A), val (LB.pullGen L.L _ _ s a.left) r.left z J = val s (r ≫ a).left z J` using `fun hJ r a => val_pull hJ _ _ _`. Establish `v : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (x y : T ⟶ A), val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A * snd A A).left) (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (fst A A)⁻¹ (snd A A)⁻¹)).left)) (lift x y).left z J = val s (x * y).left …` using `fun hJ x y => by`. Apply the tactic sequence `refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (val_cub c _ hJ _ _ _))).trans ?_, ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (vs hJ _ _))) (val_cub c _ hJ _ _ _))).trans ?_⟩ <;>`. Simplify using `only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]`. Rewrite using `[← (v hJ x y).1, ← (v hJ x y).2]`.

Use `gen_unique' L.isLB (fun U _ h => ?_) (A ⊗ A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left (Over.w _) hs (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _) (DVR.pullGen_isGen _ _ _ _ c.isGen _)) (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ …` and prove the remaining obligations. Use `((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_sym _ h))) (prod_cub _ _ _ h))).trans (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_cub _ _ _ h))).symm)` and prove the remaining obligations. Simplify using `only [mul_inv_cancel, _root_.one_mul, mul_inv, mul_comm (snd A A) (fst A A), mul_comm (snd A A)⁻¹ (fst A A)]`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv]`.

Normalize the expressions using the abelian group laws. Use `(v (T := 𝟙_ (Over S)) hI 1 1).1.trans (Eq.trans ?_ (v (T := 𝟙_ (Over S)) hI 1 1).2.symm)` and prove the remaining obligations. Simplify using `only [_root_.mul_one, inv_one, val_sym_one (T := 𝟙_ (Over S)) hr hI]`.
-/
theorem val_sym_mul (hs : Function.Surjective (A ⊗ A).hom.appTop.hom) (hg : s.IsGen)
    (hr : LB.Gen.Corr L.L _ _ _ _ (LB.pullGen L.L _ _ s (eSec A)) (LB.oneGen L.L))
    {T : Over S} {z : T.left} {J} (hJ : Good L.L z J) (x y : T ⟶ A) :
    val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ = val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := by
  have vs : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (r : T ⟶ A ⊗ A) (a : A ⊗ A ⟶ A),
      val (LB.pullGen L.L _ _ s a.left) r.left z J = val s (r ≫ a).left z J := fun hJ r a => val_pull hJ _ _ _
  have v : ∀ {T : Over S} {z : T.left} {J} (_ : Good L.L z J) (x y : T ⟶ A),
      val (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A * snd A A).left)
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (fst A A) (lift (fst A A)⁻¹ (snd A A)⁻¹)).left)) (lift x y).left z J =
        val s (x * y).left z J * cubV c z J x x⁻¹ y⁻¹ ∧
      val (LB.mulGen L.L _ _ _ _ (LB.mulGen L.L _ _ _ _ (LB.pullGen L.L _ _ s (fst A A).left)
        (LB.pullGen L.L _ _ s (snd A A).left))
        (LB.pullGen L.L (thφ A (x3 A)) thε c.t (lift (snd A A) (lift (snd A A)⁻¹ (fst A A))).left)) (lift x y).left z J =
        val s x.left z J * val s y.left z J * cubV c z J y y⁻¹ x := fun hJ x y => by
    refine ⟨((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (vs hJ _ _) (val_cub c _ hJ _ _ _))).trans ?_,
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans
        (congrArg₂ (· * ·) (vs hJ _ _) (vs hJ _ _))) (val_cub c _ hJ _ _ _))).trans ?_⟩ <;>
    simp only [MonObj.comp_mul, GrpObj.comp_inv, lift_fst, lift_snd]
  rw [← (v hJ x y).1, ← (v hJ x y).2]
  refine gen_unique' L.isLB (fun U _ h => ?_) (A ⊗ A).hom (lift (1 : 𝟙_ (Over S) ⟶ A) (1 : 𝟙_ (Over S) ⟶ A)).left
    (Over.w _) hs
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _) (DVR.pullGen_isGen _ _ _ _ c.isGen _))
    (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.mulGen_isGen _ _ _ _ _ _ _ (DVR.pullGen_isGen _ _ _ _ hg _)
      (DVR.pullGen_isGen _ _ _ _ hg _)) (DVR.pullGen_isGen _ _ _ _ c.isGen _)) (fun w I hI => ?_) _ _ z J hJ
  · refine ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) ((Fintype.prod_sum_type _).trans
      (congrArg₂ (· * ·) (prod_sym _ h) (prod_sym _ h))) (prod_cub _ _ _ h))).trans
      (Eq.trans ?_ ((Fintype.prod_sum_type _).trans (congrArg₂ (· * ·) (prod_sym _ h) (prod_cub _ _ _ h))).symm)
    simp only [mul_inv_cancel, _root_.one_mul, mul_inv, mul_comm (snd A A) (fst A A), mul_comm (snd A A)⁻¹ (fst A A)]
    apply Additive.ofMul.injective
    simp only [ofMul_mul, ofMul_inv]
    abel
  · refine (v (T := 𝟙_ (Over S)) hI 1 1).1.trans (Eq.trans ?_ (v (T := 𝟙_ (Over S)) hI 1 1).2.symm)
    simp only [_root_.mul_one, inv_one, val_sym_one (T := 𝟙_ (Over S)) hr hI]
end Sym

section Val
variable {F : Type} [Field F] {X Y : Scheme.{0}} {L : LB X} {K : Type} [Fintype K] {φ : K → (Y ⟶ X)} {ε : K → ℤ}

/- English proof (translation)
Use `(stalkConst z).injective ?_` and prove the remaining obligations. Rewrite using `[← stalkUnits_val, MulEquiv.apply_symm_apply]`. Conclude with `(gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)`.
-/
theorem coe_val (t : LB.Gen (LB.LinComb L φ ε)) (r : Sp F ⟶ Y) {z : Sp F} {J : (Sp F ⟶ X) → L.ι} (hJ : Good L z J) :
    ((stalkUnits z).symm (val t r z J) : F) = vF t r J := by
  refine (stalkConst z).injective ?_
  rw [← stalkUnits_val, MulEquiv.apply_symm_apply]
  exact (gs_unit r z _ (hJ.mem φ r) _).symm.trans (gs_eq_stalkConst r z
    (fun w _ => (Subsingleton.elim (α := PrimeSpectrum F) z w) ▸ hJ.mem φ r) _)
end Val

variable {R : Type} [CommRing R] [IsDomain R] (D : DegPre R)

/- English proof (translation)
Establish `hL` using `D.P.isLB`. Take `⟨b, hb⟩` from `exists_generator D hS`. Take `⟨th, hth⟩` from `exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ)) (fun U _ h => by rw [prod_fam_zero]; simp) b`. Use `⟨th, fun s => ?_⟩` and prove the remaining obligations. Take `⟨s', hs'⟩` from `exists_sec hL (φ' := D.famφB 0) (ε' := DegPre.famε 1) (fun U _ h => by rw [prod_fam_zero]; simp) s`.

Take `⟨a, ha, -⟩` from `hb s'`. Use `⟨a, secIsMul_of_sval hL fun y J hJ => ?_⟩` and prove the remaining obligations. Rewrite using `[← hs' _ _ y J hJ, sval_of_secIsMul ha _ y hJ, hth _ _ y J hJ, Category.id_comp]`.
-/
theorem exists_th (hS : SecBaseChangeSt) [IsLocalRing R] [IsNoetherianRing R] :
    ∃ th : H0 D.P.L 1, ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j := by
  have hL := D.P.isLB
  obtain ⟨b, hb⟩ := exists_generator D hS
  obtain ⟨th, hth⟩ := exists_sec hL (φ' := fun _ : Fin 1 => 𝟙 D.P.A.left) (ε' := fun _ => ((1 : ℕ) : ℤ))
    (fun U _ h => by rw [prod_fam_zero]; simp) b
  refine ⟨th, fun s => ?_⟩
  obtain ⟨s', hs'⟩ := exists_sec hL (φ' := D.famφB 0) (ε' := DegPre.famε 1)
    (fun U _ h => by rw [prod_fam_zero]; simp) s
  obtain ⟨a, ha, -⟩ := hb s'
  refine ⟨a, secIsMul_of_sval hL fun y J hJ => ?_⟩
  rw [← hs' _ _ y J hJ, sval_of_secIsMul ha _ y hJ, hth _ _ y J hJ, Category.id_comp]

variable (F : Type) [Field F] [Algebra (FractionRing R) F]

/- English proof (translation)
Use `haveI := D.P.isAb.proper`. Establish `hE : ValuativeCriterion.Existence D.P.A.hom`. Establish `h : UniversallyClosed D.P.A.hom` using `inferInstance`. Rewrite `h` using `[UniversallyClosed.eq_valuativeCriterion]`. Conclude with `h.1`.

Set `f : R →+* S` to `((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS`. Set `Q : ValuativeCommSq D.P.A.hom` to `{ R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f), commSq := ⟨by`. Use `(Over.w x).trans ?_` and prove the remaining obligations. Use `show Spec.map _ ≫ Spec.map _ = _`. Rewrite using `[← Spec.map_comp, ← Spec.map_comp]`.

Use the proof step `rfl⟩ }`. Take `⟨⟨l, h1, -⟩⟩` from `hE Q`. Conclude with `⟨l, h1⟩`.
-/
theorem exists_ext (S : ValuationSubring F) (hS : ∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S)
    (x : TF (R := R) F ⟶ D.P.A) : ∃ x₀ : Sp S ⟶ D.P.A.left, spMap S.subtype ≫ x₀ = x.left := by
  haveI := D.P.isAb.proper
  have hE : ValuativeCriterion.Existence D.P.A.hom := by
    have h : UniversallyClosed D.P.A.hom := inferInstance
    rw [UniversallyClosed.eq_valuativeCriterion] at h
    exact h.1
  let f : R →+* S := ((algebraMap (FractionRing R) F).comp (algebraMap R _)).codRestrict S hS
  let Q : ValuativeCommSq D.P.A.hom :=
    { R := S, K := F, i₁ := x.left, i₂ := Spec.map (CommRingCat.ofHom f),
      commSq := ⟨by
        refine (Over.w x).trans ?_
        show Spec.map _ ≫ Spec.map _ = _
        rw [← Spec.map_comp, ← Spec.map_comp]
        rfl⟩ }
  obtain ⟨⟨l, h1, -⟩⟩ := hE Q
  exact ⟨l, h1⟩

/- English proof (translation)
Establish `key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ((∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) → ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U j)` using `fun ψ => by`. Distinguish the cases in `h : ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ`. Take `⟨x₀, rfl⟩` from `h`. Take `⟨j, hj⟩` from `exists_chart hL (x₀ (IsLocalRing.closedPoint S))`. Establish `e : x₀ ⁻¹ᵁ L.U j = ⊤` using `DVR.eq_top_of_closedPoint_mem _ hj`.

Conclude with `⟨j, fun w _ => e.ge (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, e.ge⟩⟩`. Take `⟨j, hj⟩` from `exists_chart hL (ψ (IsLocalRing.closedPoint F))`. Conclude with `⟨j, (DVR.eq_top_of_closedPoint_mem (ψ ⁻¹ᵁ L.U j) hj).ge, fun h' => (h h').elim⟩`. Use `choose J h₁ h₂ using key`. Conclude with `⟨J, h₁, h₂⟩`.
-/
theorem exists_gauge (S : ValuationSubring F) {X : Scheme.{0}} {L : LB X} (hL : L.IsLB) :
    ∃ J : (Sp F ⟶ X) → L.ι, (∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ L.U (J ψ)) ∧ ∀ ψ, (∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U (J ψ) := by
  have key : ∀ ψ : Sp F ⟶ X, ∃ j, ⊤ ≤ ψ ⁻¹ᵁ L.U j ∧ ((∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ) →
      ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ ∧ ⊤ ≤ x₀ ⁻¹ᵁ L.U j) := fun ψ => by
    by_cases h : ∃ x₀ : Sp S ⟶ X, spMap S.subtype ≫ x₀ = ψ
    · obtain ⟨x₀, rfl⟩ := h
      obtain ⟨j, hj⟩ := exists_chart hL (x₀ (IsLocalRing.closedPoint S))
      have e : x₀ ⁻¹ᵁ L.U j = ⊤ := DVR.eq_top_of_closedPoint_mem _ hj
      exact ⟨j, fun w _ => e.ge (trivial : spMap S.subtype w ∈ (⊤ : (Sp S).Opens)), fun _ => ⟨x₀, rfl, e.ge⟩⟩
    · obtain ⟨j, hj⟩ := exists_chart hL (ψ (IsLocalRing.closedPoint F))
      exact ⟨j, (DVR.eq_top_of_closedPoint_mem (ψ ⁻¹ᵁ L.U j) hj).ge, fun h' => (h h').elim⟩
  choose J h₁ h₂ using key
  exact ⟨J, h₁, h₂⟩

/- English proof (translation)
Set `z : Sp F` to `IsLocalRing.closedPoint F`. Establish `hJ : Good D.P.L z J` using `fun ψ => good ψ trivial`. Set `e` to `(stalkUnits z).symm`. Establish `C : IsCub (cubV D.cub (T` using `TF (R := R) F) z J) := isCub_cubV D.cub (T := TF (R := R) F) hJ`. Establish `sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom`.

Rewrite using `[← Over.w (snd D.P.A D.P.A)]`. Conclude with `surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2`. Set `ρ : ((Sp F).presheaf.stalk z)ˣ` to `val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J`. Set `p : D.X → ((Sp F).presheaf.stalk z)ˣ` to `fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z J`. Establish `hτ : ∀ a b, val (Z` using `Sp F) (D.tau a b) (jFK (R := R) F) z J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b => (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _))) ((val_inv _ _).tran …`.

Establish `hx : ∀ χ, jFK (R` using `R) F ≫ D.xK χ = (DegPre.cF D F χ).left := fun χ => (Category.assoc _ _ _).symm`. Set `N : NumD F` to `{ A := TF (R := R) F ⟶ D.P.A θ := fun x y u => e (cubV D.cub (T := TF (R := R) F) z J x y u) cub := ⟨fun x y => by rw [C.face, map_one], fun x y u => by rw [C.s01], fun x y u => by rw [C.s12], fun x x' x'' y => by rw [← map_mul, ← map_mul, C.coc]⟩ σ := fun x => e (val D.sym x.lef …`. Rewrite using `[← map_mul, ← map_mul, ← map_mul]`. Conclude with `congrArg e (val_sym_mul D.cub sj D.sym_gen D.sym_rig (T := TF (R := R) F) hJ x y)`. Use `th := fun x => sF th x.left J * ((e ρ)⁻¹ : Fˣ)`.

Use `X := D.X`. Use `c := DegPre.cF D F`. Use `c_add := fun a b => by`. Rewrite using `[DegPre.cF, D.c_add]`. Conclude with `MonObj.comp_mul _ _ _`.

Use `ψ := fun χ => e (p χ * ρ)`. Use `even := fun χ => by`. Establish `h` using `val_corr hJ (he χ) (jFK (R := R) F)`. Rewrite `h` using `[val_mul hJ, val_pull hJ, hx]`. Rewrite using `[← map_mul, mul_right_comm]`.

Conclude with `congrArg (fun q => e (q * ρ)) h`. Use `bimult := fun a a' b => by`. Establish `h` using `((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (val_pull hJ _ _ _))).symm.trans ((val_corr hJ (hb a a' b) (jFK (R := R) F)).trans ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (hτ _ _))))`. Establish `h3 : jFK (R` using `R) F ≫ D.pt3 a a' b = (lift (DegPre.cF D F a) (lift (DegPre.cF D F a') (DegPre.cF D F b))).left := by`. Set `κ : TF (R` to `R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl`.

Use `congrArg CommaMorphism.left (show κ ≫ lift _ (lift _ _) = _ from ?_)` and prove the remaining obligations. Simplify using `only [comp_lift, comp_toUnit_assoc]`. Rewrite `h` using `[h3]`. Simplify using `only [← map_div, ← map_mul]`. Use `congrArg e ?_` and prove the remaining obligations.

Establish `k : ∀ u v w, (u * ρ) / (v * ρ) / (w * ρ) = u * v⁻¹ * w⁻¹ * ρ⁻¹` using `fun u v w => by`. Apply `Additive.ofMul.injective` to reduce the goal to its premises. Simplify using `only [ofMul_mul, ofMul_inv, ofMul_div]`. Normalize the expressions using the abelian group laws. Rewrite using `[k, k, k]`.

Conclude with `h }`. Establish `hρ : (e ρ : F) = vF (L` using `D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom J := coe_val _ _ hJ`. Conclude with `⟨N, { J := J, good := good, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _ c_eq := fun _ => rfl θ_eq := fun x y u => coe_val _ _ hJ σ_eq := fun x => coe_val _ _ hJ th_eq := fun x => by`. Rewrite using `[← hρ]`. Conclude with `Units.inv_mul_cancel_right _ _`.

Use `ψ_eq := fun χ => by`. Rewrite using `[← hρ, ← coe_val _ _ hJ]`. Conclude with `(congrArg Units.val (map_mul e _ _)).trans (Units.val_mul _ _) }, rfl⟩`.
-/
theorem exists_numOf (hG : GlobalFnsSt) (he : D.PsiEven) (hb : D.TauBimult) (th : H0 D.P.L 1)
    (hth : ∀ s : H0 D.P.L 1, ∃ r : R, ∀ j, s.f j = resTop _ (scal D.P.A.hom r) * th.f j)
    (J : (Sp F ⟶ D.P.A.left) → D.P.L.ι) (good : ∀ ψ, ⊤ ≤ ψ ⁻¹ᵁ D.P.L.U (J ψ)) :
    ∃ (N : NumD F) (ν : NumOf D F N), ν.J = J := by
  let z : Sp F := IsLocalRing.closedPoint F
  have hJ : Good D.P.L z J := fun ψ => good ψ trivial
  let e := (stalkUnits z).symm
  have C : IsCub (cubV D.cub (T := TF (R := R) F) z J) := isCub_cubV D.cub (T := TF (R := R) F) hJ
  have sj : Function.Surjective (D.P.A ⊗ D.P.A).hom.appTop.hom := by
    rw [← Over.w (snd D.P.A D.P.A)]
    exact surj_comp (surj_snd hG D.P.isAb _) (hG _ _ D.P.isAb).2
  let ρ : ((Sp F).presheaf.stalk z)ˣ := val (Z := Sp F) (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig (TF (R := R) F).hom z J
  let p : D.X → ((Sp F).presheaf.stalk z)ˣ := fun χ => val (Z := Sp F) (D.psi χ) (jFK (R := R) F) z J
  have hτ : ∀ a b, val (Z := Sp F) (D.tau a b) (jFK (R := R) F) z J = p (a + b) * (p a)⁻¹ * (p b)⁻¹ * ρ⁻¹ := fun a b =>
    (val_mul hJ _ _ _).trans (congrArg₂ (· * ·) ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·)
      ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) rfl (val_inv _ _))) (val_inv _ _)))
      ((val_inv _ _).trans (congrArg (·⁻¹) (val_pull hJ _ _ _))))
  have hx : ∀ χ, jFK (R := R) F ≫ D.xK χ = (DegPre.cF D F χ).left := fun χ => (Category.assoc _ _ _).symm
  let N : NumD F :=
    { A := TF (R := R) F ⟶ D.P.A
      θ := fun x y u => e (cubV D.cub (T := TF (R := R) F) z J x y u)
      cub := ⟨fun x y => by rw [C.face, map_one], fun x y u => by rw [C.s01], fun x y u => by rw [C.s12],
        fun x x' x'' y => by rw [← map_mul, ← map_mul, C.coc]⟩
      σ := fun x => e (val D.sym x.left z J)
      σ_one := (congrArg e (val_sym_one (L := ⟨D.P.L, D.rig, D.P.isLB, D.rig_gen⟩) D.sym_rig
        (T := TF (R := R) F) hJ)).trans (map_one e)
      σ_mul := fun x y => by
        rw [← map_mul, ← map_mul, ← map_mul]
        exact congrArg e (val_sym_mul D.cub sj D.sym_gen D.sym_rig (T := TF (R := R) F) hJ x y)
      th := fun x => sF th x.left J * ((e ρ)⁻¹ : Fˣ)
      X := D.X
      c := DegPre.cF D F
      c_add := fun a b => by
        rw [DegPre.cF, D.c_add]
        exact MonObj.comp_mul _ _ _
      ψ := fun χ => e (p χ * ρ)
      even := fun χ => by
        have h := val_corr hJ (he χ) (jFK (R := R) F)
        rw [val_mul hJ, val_pull hJ, hx] at h
        rw [← map_mul, mul_right_comm]
        exact congrArg (fun q => e (q * ρ)) h
      bimult := fun a a' b => by
        have h := ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (val_pull hJ _ _ _))).symm.trans
          ((val_corr hJ (hb a a' b) (jFK (R := R) F)).trans
            ((val_mul hJ _ _ _).trans (congrArg₂ (· * ·) (hτ _ _) (hτ _ _))))
        have h3 : jFK (R := R) F ≫ D.pt3 a a' b =
            (lift (DegPre.cF D F a) (lift (DegPre.cF D F a') (DegPre.cF D F b))).left := by
          let κ : TF (R := R) F ⟶ TK R := Over.homMk (jFK (R := R) F) rfl
          refine congrArg CommaMorphism.left (show κ ≫ lift _ (lift _ _) = _ from ?_)
          simp only [comp_lift, comp_toUnit_assoc]
        rw [h3] at h
        simp only [← map_div, ← map_mul]
        refine congrArg e ?_
        have k : ∀ u v w, (u * ρ) / (v * ρ) / (w * ρ) = u * v⁻¹ * w⁻¹ * ρ⁻¹ := fun u v w => by
          apply Additive.ofMul.injective
          simp only [ofMul_mul, ofMul_inv, ofMul_div]
          abel
        rw [k, k, k]
        exact h }
  have hρ : (e ρ : F) = vF (L := D.P.L) (φ := fun _ : PUnit => eSec D.P.A) (ε := fun _ => 1) D.rig
    (TF (R := R) F).hom J := coe_val _ _ hJ
  exact ⟨N,
    { J := J, good := good, th := th, th_gen := hth, eA := MulEquiv.refl _, eX := AddEquiv.refl _
      c_eq := fun _ => rfl
      θ_eq := fun x y u => coe_val _ _ hJ
      σ_eq := fun x => coe_val _ _ hJ
      th_eq := fun x => by
        rw [← hρ]
        exact Units.inv_mul_cancel_right _ _
      ψ_eq := fun χ => by
        rw [← hρ, ← coe_val _ _ hJ]
        exact (congrArg Units.val (map_mul e _ _)).trans (Units.val_mul _ _) }, rfl⟩

/- English proof (translation)
Introduce `hL R _ _ _ _ D he hb F _ _ S hS`. Take `⟨th, hth⟩` from `exists_th D hL.secBaseChange`. Take `⟨J, good, hJ⟩` from `exists_gauge F S D.P.isLB`. Take `⟨N, ν, rfl⟩` from `exists_numOf D F hL.globalFns he hb th hth J good`. Conclude with `⟨N, ν, fun x => hJ _ (exists_ext D F S hS x)⟩`.
-/
theorem exists_integral_values : Laws → ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R] [IsNoetherianRing R] (D : DegPre R), D.PsiEven → D.TauBimult → ∀ (F : Type) [Field F] [Algebra (FractionRing R) F] (S : ValuationSubring F), (∀ r : R, algebraMap (FractionRing R) F (algebraMap R _ r) ∈ S) → ∃ (N : NumD F) (ν : NumOf D F N), ν.Integral S := by
  intro hL R _ _ _ _ D he hb F _ _ S hS
  obtain ⟨th, hth⟩ := exists_th D hL.secBaseChange
  obtain ⟨J, good, hJ⟩ := exists_gauge F S D.P.isLB
  obtain ⟨N, ν, rfl⟩ := exists_numOf D F hL.globalFns he hb th hth J good
  exact ⟨N, ν, fun x => hJ _ (exists_ext D F S hS x)⟩

end GlobalTheory.ValuesExist
end
