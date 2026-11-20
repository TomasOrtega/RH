import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.TorMatch
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsGrpPullbackGenMap
import Development.AbelianVarietyTheory.Proofs.UniformizationProofs.TorsionClause
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.IsoFreePerpLabelKernelWeights
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.UnitOnInjectiveOfCommRing
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLinComb
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsIsPELTripleOfDenseFibres
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaOfTranslDiff
import Development.AbelianVarietyTheory.Proofs.AbelianSchemeLawProofs.GlobalFnsHolds
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.WeilPairingMumfordLambdaSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.MemSmulOfForallCharPowEqOneStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.AnForm.R
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.ZH
open scoped CategoryTheory.Obj
open GlobalTheory.Poinc GlobalTheory.Poinc.Eq8 Formalism.L2.Pj
open scoped TensorProduct
attribute [local instance] Over.cartesianMonoidalCategory
open Classical

noncomputable section

namespace GlobalTheory.Poinc.Eq8.Labels

/- English proof (translation)
Establish `hU` using `GlobalTheory.TauFormHom.isGrpPullback_genMap U`. Establish `h' : U'.gen.inv ≫ (Over.pullback (jK R)).map p = π ≫ U.gen.inv`. Rewrite using `[Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]`. Establish `h'' : π.left ≫ U.gen.inv.left = U'.gen.inv.left ≫ ((Over.pullback (jK R)).map p).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, h']`.

Establish `hf : ((Over.pullback (jK R)).map p).left ≫ pullback.fst G.hom (jK R) = pullback.fst G'.hom (jK R) ≫ p.left`. Simplify using `only [Over.pullback_map_left]`. Conclude with `pullback.lift_fst _ _ _`. Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `hU.1.hom_ext ?_ ?_` and prove the remaining obligations.

Rewrite using `[e, Over.comp_left, genMap, genMap]`. Simplify using `only [Category.assoc]`. Rewrite using `[reassoc_of% h'', hf]`. Rewrite using `[Over.w a, Over.w (a' ≫ π)]`.
-/
theorem eq_comp_of_genMap {R : Type} [CommRing R] [IsDomain R] [IsLocalRing R] {D D' : DegData R (maximalIdeal R)}
    {A A' : PolAV (Sp (FractionRing R))} {G G' : Over (Sp R)} [GrpObj G] [IsCommMonObj G] [GrpObj G']
    [IsCommMonObj G'] (U : Unif (maximalIdeal R) D A G) (U' : Unif (maximalIdeal R) D' A' G') (p : G' ⟶ G)
    (π : A'.A ⟶ A.A) (h : (Over.pullback (jK R)).map p ≫ U.gen.hom = U'.gen.hom ≫ π) {T : Over (Sp (FractionRing R))}
    (a : T ⟶ A.A) (a' : T ⟶ A'.A) (e : a.left ≫ genMap U = a'.left ≫ genMap U' ≫ p.left) : a = a' ≫ π := by
  have hU := GlobalTheory.TauFormHom.isGrpPullback_genMap U
  have h' : U'.gen.inv ≫ (Over.pullback (jK R)).map p = π ≫ U.gen.inv := by
    rw [Iso.inv_comp_eq, ← Category.assoc, ← h, Category.assoc, Iso.hom_inv_id, Category.comp_id]
  have h'' : π.left ≫ U.gen.inv.left = U'.gen.inv.left ≫ ((Over.pullback (jK R)).map p).left := by
    rw [← Over.comp_left, ← Over.comp_left, h']
  have hf : ((Over.pullback (jK R)).map p).left ≫ pullback.fst G.hom (jK R) =
      pullback.fst G'.hom (jK R) ≫ p.left := by
    simp only [Over.pullback_map_left]
    exact pullback.lift_fst _ _ _
  apply Over.OverMorphism.ext
  refine hU.1.hom_ext ?_ ?_
  · rw [e, Over.comp_left, genMap, genMap]
    simp only [Category.assoc]
    rw [reassoc_of% h'', hf]
  · rw [Over.w a, Over.w (a' ≫ π)]

/- English proof (translation)
Introduce `S _ P P' pr hpr W hL n T x y hx hy c hc`. Establish `hG` using `GlobalTheory.globalFns_holds`. Establish `hΛ : (abelian₂ P.A P.L).IsLB` using `LB.isLB_linComb P.isLB _ _`. Establish `hM` using `LB.isLB_linComb hΛ (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)`. Establish `hφ : ∀ ab : Fin 8 × Fin 8, IsMonHom (lift (pr ab.1) (pr ab.2))` using `fun ab => by haveI := hpr ab.1 haveI := hpr ab.2 infer_instance`.

Establish `ht : ∀ {z : T ⟶ P'.A}, z ^ n = 1 → ∀ a, (z ≫ pr a) ^ n = 1` using `fun {z} hz a => by haveI := hpr a`. Rewrite using `[← MonObj.pow_comp, hz, MonObj.one_comp]`. Establish `key` using `GlobalTheory.PairingComb.weilIs_linComb hG P'.isAb hΛ (fun ab : Fin 8 × Fin 8 => lift (pr ab.1) (pr ab.2)) hφ (fun ab => W ab.1 ab.2) (n := n) (x := x) (y := y) (fun ab => c ab.1 ab.2 * c ab.2 ab.1) (fun ab => by`. Rewrite using `[comp_lift, comp_lift]`. Conclude with `GlobalTheory.T.weilPairing_mumfordLambda_square S P n T _ _ _ _ (ht hx _) (ht hx _) (ht hy _) (ht hy _) _ _ (hc ab.1 ab.2) (hc ab.2 ab.1))`.

Use `GlobalTheory.PELFamily.weilIs_of_lbIso hG P'.isAb P'.isLB hM ?_ key` and prove the remaining obligations. Use `LBIso.trans P'.isLB hM (pull_isLB hM _) hL ?_` and prove the remaining obligations. Use `GlobalTheory.DescendedPrincipal.lbIso_pull_id hM` as an intermediate fact. Simplify using `using this.symm`.
-/
theorem commutatorPairing_eighthPower_bundle : ∀ (S : Scheme.{0}) [IsLocallyNoetherian S] (P P' : PolAV S) (pr : Fin 8 → (P'.A ⟶ P.A)), (∀ a, IsMonHom (pr a)) → ∀ (W : Matrix (Fin 8) (Fin 8) ℤ), LBIso P'.L (LB.LinComb (abelian₂ P.A P.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (n : ℕ) (T : Over S) (x y : T ⟶ P'.A), x ^ n = 1 → y ^ n = 1 → ∀ (c : Fin 8 → Fin 8 → Γ(T.left, ⊤)ˣ), (∀ a b, WeilIs P.A P.L n (x ≫ pr a) (y ≫ pr b) (c a b)) → WeilIs P'.A P'.L n x y (∏ ab : Fin 8 × Fin 8, (c ab.1 ab.2 * c ab.2 ab.1) ^ W ab.1 ab.2) := by
  intro S _ P P' pr hpr W hL n T x y hx hy c hc
  have hG := GlobalTheory.globalFns_holds
  have hΛ : (abelian₂ P.A P.L).IsLB := LB.isLB_linComb P.isLB _ _
  have hM := LB.isLB_linComb hΛ (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left)
    (fun ab => W ab.1 ab.2)
  have hφ : ∀ ab : Fin 8 × Fin 8, IsMonHom (lift (pr ab.1) (pr ab.2)) := fun ab => by
    haveI := hpr ab.1
    haveI := hpr ab.2
    infer_instance
  have ht : ∀ {z : T ⟶ P'.A}, z ^ n = 1 → ∀ a, (z ≫ pr a) ^ n = 1 := fun {z} hz a => by
    haveI := hpr a
    rw [← MonObj.pow_comp, hz, MonObj.one_comp]
  have key := GlobalTheory.PairingComb.weilIs_linComb hG P'.isAb hΛ (fun ab : Fin 8 × Fin 8 => lift (pr ab.1) (pr ab.2)) hφ
    (fun ab => W ab.1 ab.2) (n := n) (x := x) (y := y) (fun ab => c ab.1 ab.2 * c ab.2 ab.1) (fun ab => by
      rw [comp_lift, comp_lift]
      exact GlobalTheory.T.weilPairing_mumfordLambda_square S P n T _ _ _ _ (ht hx _) (ht hx _) (ht hy _) (ht hy _) _ _ (hc ab.1 ab.2) (hc ab.2 ab.1))
  refine GlobalTheory.PELFamily.weilIs_of_lbIso hG P'.isAb P'.isLB hM ?_ key
  refine LBIso.trans P'.isLB hM (pull_isLB hM _) hL ?_
  have := GlobalTheory.DescendedPrincipal.lbIso_pull_id hM
  simpa using this.symm

/- English proof (translation)
Rewrite using `[Fintype.sum_prod_type]`. Simplify using `only [smul_add, Finset.sum_add_distrib, map_add, map_sum, map_zsmul, Matrix.add_apply, Matrix.transpose_apply, add_smul]`. Use `congr 1`. Conclude with `Finset.sum_comm`.
-/
theorem sum_symmetrised_bilinear_matrix_eq {J X Y : Type} [Fintype J] [AddCommGroup X] [AddCommGroup Y] (W : Matrix J J ℤ) (c : J → (X →+ Y))
    (l : J → X) :
    ∑ ab : J × J, W ab.1 ab.2 • (c ab.1 (l ab.2) + c ab.2 (l ab.1)) =
      ∑ u, c u (∑ w, (W + W.transpose) u w • l w) := by
  rw [Fintype.sum_prod_type]
  simp only [smul_add, Finset.sum_add_distrib, map_add, map_sum, map_zsmul, Matrix.add_apply, Matrix.transpose_apply,
    add_smul]
  congr 1
  exact Finset.sum_comm

/- English proof (translation)
Introduce `R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e he v F _ _ _ k hk q q' a a' hqa hqa' hla`. Use `haveI := hdvr`. Take `⟨hR, hR0⟩` from `id hRb`. Take `⟨-, -, -, hRc⟩` from `id hR`. Use `haveI := hRc`.

Use `haveI := hR0`. Establish `hB` using `D.tau_bimult`. Establish `hB'` using `D'.tau_bimult`. Establish `hk0 : k ≠ 0` using `by rintro rfl; simp at hk`. Establish `hk1 : 1 ≤ k` using `Nat.one_le_iff_ne_zero.2 hk0`.

Establish `hkF : (k : F) ≠ 0`. Establish `h` using `hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))`. Rewrite `h` using `[map_natCast]`. Conclude with `h.ne_zero`. Take `⟨f, ⟨i₁, s₁, q₁, -, w₁⟩, -⟩` from `GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1`.

Take `⟨f', ⟨i₂, -, -, -, w₂⟩, p₂⟩` from `GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1`. Take `rfl : a = f q` from `(i₁ q a).1 hqa`. Take `rfl : a' = f' q'` from `(i₂ q' a').1 hqa'`. Establish `hav : f q = f' q' ≫ pr v` using `eq_comp_of_genMap U U' (pG v) (pr v) (hgen v) _ _ hla`. Establish `hpw : ∀ w, (f' q' ≫ pr w) ^ k = 1` using `fun w => by haveI := hpr w`.

Rewrite using `[← MonObj.pow_comp, p₂, MonObj.one_comp]`. Use `choose qw hqw using fun w => s₁ _ (hpw w)`. Establish `key : ∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ k = 1 → τ (Multiplicative.ofAdd (q.y - e q'.y v)) = 1`. Introduce `τ hτ`. Establish `hτk : ∀ x, τ x ^ k = 1` using `fun x => by`.

Rewrite using `[← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]`. Set `ev : D'.toPre.X →+ D.toPre.X` to `(Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom`. Set `τ' : Multiplicative D'.toPre.X →* Fˣ` to `τ.comp (AddMonoidHom.toMultiplicative ev)`. Establish `hτ' : τ' ^ k = 1` using `MonoidHom.ext fun x => by`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`.

Conclude with `hτk _`. Set `τu : Fin 8 → (Multiplicative D.toPre.X →* Fˣ)` to `fun u => τ'.comp (AddMonoidHom.toMultiplicative (c u))`. Establish `hτu : ∀ u, τu u ^ k = 1` using `fun u => MonoidHom.ext fun x => by`. Rewrite using `[MonoidHom.pow_apply, MonoidHom.one_apply]`. Conclude with `hτk _`.

Take `⟨tT', htT'y, htT'⟩` from `GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB' τ' hτ'`. Use `choose tT htTy htT using fun u => GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB (τu u) (hτu u)`. Establish `hproj : ∀ u, f (tT u) = f' tT' ≫ pr u` using `fun u => eq_comp_of_genMap U U' (pG u) (pr u) (hgen u) _ _ (hc u F (fun _ => rfl) k hk (τu u) τ' (tT u) tT' (f (tT u)) (f' tT') hτ' (fun _ => rfl) (htTy u) (htT u) htT'y htT' ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl))`. Establish `hA : ∀ u w, WeilIs A.A A.L k (f' tT' ≫ pr u) (f' q' ≫ pr w) (unitOn (τ' (Multiplicative.ofAdd (c u (qw w).y))))` using `fun u w => by`. Rewrite using `[← hproj u, ← hqw w]`.

Conclude with `(w₁ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns (tT u) (qw w) (htTy u) (htT u))`. Establish `hA' : WeilIs A'.A A'.L k (f' tT') (f' q') (unitOn (τ' (Multiplicative.ofAdd q'.y)))` using `(w₂ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns tT' q' htT'y htT')`. Establish `hA₂` using `commutatorPairing_eighthPower_bundle _ A A' pr hpr W hL k _ (f' tT') (f' q') (p₂ _) (p₂ _) _ hA`. Establish `hval : (∏ ab : Fin 8 × Fin 8, (unitOn (τ' (Multiplicative.ofAdd (c ab.1 (qw ab.2).y))) * unitOn (τ' (Multiplicative.ofAdd (c ab.2 (qw ab.1).y)))) ^ W ab.1 ab.2) = unitOn (τ' (Multiplicative.ofAdd (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y))))`. Set `ψ : Multiplicative D'.toPre.X →* Γ(Sp F, ⊤)ˣ` to `(Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom).comp τ'`.

Establish `hψ : ∀ x, unitOn (τ' x) = ψ x` using `fun x => rfl`. Simplify using `only [hψ]`. Rewrite using `[← sum_symmetrised_bilinear_matrix_eq W c (fun w => (qw w).y), ofAdd_sum, map_prod]`. Use `Finset.prod_congr rfl fun ab _ => ?_` and prove the remaining obligations. Rewrite using `[ofAdd_zsmul, map_zpow, ofAdd_add, map_mul]`.

Rewrite `hA₂` using `[hval]`. Establish `hu` using `GlobalTheory.weilIs_unique_fieldPoint _ A'.A A'.L A'.isLB F _ k _ _ _ _ hA' hA₂`. Establish `hinv : e (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)) = fun w => (qw w).y`. Use `he (e.symm fun w => (qw w).y)` as an intermediate fact. Rewrite `this` using `[e.apply_symm_apply]`.

Rewrite using `[this, e.apply_symm_apply]`. Establish `h₁ : τ (Multiplicative.ofAdd (e q'.y v)) = τ (Multiplicative.ofAdd (qw v).y)`. Use `hu` as an intermediate fact. Simplify using `only [τ', ev, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd, AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom, hinv] at this`. Conclude with `this`.

Take `⟨z, hz, -⟩` from `(q₁ (qw v) q).1 (by rw [hqw, hav])`. Rewrite using `[ofAdd_sub, map_div, h₁, hz, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, hτk, _root_.mul_one, div_self']`. Take `⟨z, hz⟩` from `GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one _ F k hkF _ key`. Conclude with `⟨z, by rw [← hz]; abel⟩`.
-/
theorem label_proj_eq : ∀ (R : Type) [CommRing R] [IsDomain R] [IsLocalRing R], GlobalTheory.Mum.Base R → IsDiscreteValuationRing R → ∀ (G : Over (Sp R)) [GrpObj G] [IsCommMonObj G], IsSemiAbelian G → ∀ (D : DegData R (maximalIdeal R)) (A : PolAV (Sp (FractionRing R))) (U : Unif (maximalIdeal R) D A G) (G' : Over (Sp R)) [GrpObj G'] [IsCommMonObj G'], IsSemiAbelian G' → ∀ (D' : DegData R (maximalIdeal R)) (A' : PolAV (Sp (FractionRing R))) (U' : Unif (maximalIdeal R) D' A' G') (W : Matrix (Fin 8) (Fin 8) ℤ), IsE8 W → ∀ (pr : Fin 8 → (A'.A ⟶ A.A)), (∀ a, IsMonHom (pr a)) → (∀ (T' : Over (Sp (FractionRing R))) (y : Fin 8 → (T' ⟶ A.A)), ∃! z : T' ⟶ A'.A, ∀ a, z ≫ pr a = y a) → LBIso A'.L (LB.LinComb (abelian₂ A.A A.L) (K := Fin 8 × Fin 8) (fun ab => (lift (pr ab.1) (pr ab.2)).left) (fun ab => W ab.1 ab.2)) → ∀ (pG : Fin 8 → (G' ⟶ G)), (∀ v, IsMonHom (pG v)) → (∀ v, (Over.pullback (jK R)).map (pG v) ≫ U.gen.hom = U'.gen.hom ≫ pr v) → ∀ (c : Fin 8 → (D.toPre.X →+ D'.toPre.X)), (∀ v, TorMatch U U' (RingHom.id R) (pG v).left (c v)) → ∀ e : D'.toPre.X ≃+ (Fin 8 → D.toPre.X), (∀ y, ∑ v, c v (∑ u, (W + W.transpose) v u • e y u) = y) → ∀ v : Fin 8, (∀ (F : Type) [Field F] [IsAlgClosed F] [Algebra (FractionRing R) F] (k : ℕ), IsUnit (k : R) → ∀ (q : QkPt D.toPre F k) (q' : QkPt D'.toPre F k) (a : TFK (R := R) F ⟶ A.A) (a' : TFK (R := R) F ⟶ A'.A), QkToAkU U.toUnifPre F k q a → QkToAkU U'.toUnifPre F k q' a' → a.left ≫ genMap U = a'.left ≫ genMap U' ≫ (pG v).left → ∃ z, q.y = e q'.y v + k • z) := by
  intro R _ _ _ hRb hdvr G _ _ hG D A U G' _ _ hG' D' A' U' W hW pr hpr huniv hL pG hpG hgen c hc e he v F _ _ _ k hk
    q q' a a' hqa hqa' hla
  haveI := hdvr
  obtain ⟨hR, hR0⟩ := id hRb
  obtain ⟨-, -, -, hRc⟩ := id hR
  haveI := hRc
  haveI := hR0
  have hB := D.tau_bimult
  have hB' := D'.tau_bimult
  have hk0 : k ≠ 0 := by rintro rfl; simp at hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 hk0
  have hkF : (k : F) ≠ 0 := by
    have h := hk.map ((algebraMap (FractionRing R) F).comp (algebraMap R (FractionRing R)))
    rw [map_natCast] at h
    exact h.ne_zero
  obtain ⟨f, ⟨i₁, s₁, q₁, -, w₁⟩, -⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D A G hG U F k hk1
  obtain ⟨f', ⟨i₂, -, -, -, w₂⟩, p₂⟩ := GlobalTheory.TorsionIso.torsion_clause R (maximalIdeal R) hR D' A' G' hG' U' F k hk1
  obtain rfl : a = f q := (i₁ q a).1 hqa
  obtain rfl : a' = f' q' := (i₂ q' a').1 hqa'
  have hav : f q = f' q' ≫ pr v := eq_comp_of_genMap U U' (pG v) (pr v) (hgen v) _ _ hla
  have hpw : ∀ w, (f' q' ≫ pr w) ^ k = 1 := fun w => by
    haveI := hpr w
    rw [← MonObj.pow_comp, p₂, MonObj.one_comp]
  choose qw hqw using fun w => s₁ _ (hpw w)
  have key : ∀ τ : Multiplicative D.toPre.X →* Fˣ, τ ^ k = 1 →
      τ (Multiplicative.ofAdd (q.y - e q'.y v)) = 1 := by
    intro τ hτ
    have hτk : ∀ x, τ x ^ k = 1 := fun x => by
      rw [← MonoidHom.pow_apply, hτ, MonoidHom.one_apply]
    let ev : D'.toPre.X →+ D.toPre.X := (Pi.evalAddMonoidHom (fun _ : Fin 8 => D.toPre.X) v).comp e.toAddMonoidHom
    let τ' : Multiplicative D'.toPre.X →* Fˣ := τ.comp (AddMonoidHom.toMultiplicative ev)
    have hτ' : τ' ^ k = 1 := MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    let τu : Fin 8 → (Multiplicative D.toPre.X →* Fˣ) := fun u => τ'.comp (AddMonoidHom.toMultiplicative (c u))
    have hτu : ∀ u, τu u ^ k = 1 := fun u => MonoidHom.ext fun x => by
      rw [MonoidHom.pow_apply, MonoidHom.one_apply]
      exact hτk _
    obtain ⟨tT', htT'y, htT'⟩ := GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB' τ' hτ'
    choose tT htTy htT using fun u => GlobalTheory.ZH.TorusPerp.exists_qkPt_tor (F := F) hB (τu u) (hτu u)
    have hproj : ∀ u, f (tT u) = f' tT' ≫ pr u := fun u =>
      eq_comp_of_genMap U U' (pG u) (pr u) (hgen u) _ _
        (hc u F (fun _ => rfl) k hk (τu u) τ' (tT u) tT' (f (tT u)) (f' tT') hτ' (fun _ => rfl) (htTy u) (htT u)
          htT'y htT' ((i₁ _ _).2 rfl) ((i₂ _ _).2 rfl))
    have hA : ∀ u w, WeilIs A.A A.L k (f' tT' ≫ pr u) (f' q' ≫ pr w)
        (unitOn (τ' (Multiplicative.ofAdd (c u (qw w).y)))) := fun u w => by
      rw [← hproj u, ← hqw w]
      exact (w₁ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns (tT u) (qw w) (htTy u) (htT u))
    have hA' : WeilIs A'.A A'.L k (f' tT') (f' q') (unitOn (τ' (Multiplicative.ofAdd q'.y))) :=
      (w₂ _ _ _).1 (GlobalTheory.ZH.TorusPerp.weilQkIs_tor GlobalTheory.firstFiveLaws.1.globalFns tT' q' htT'y htT')
    have hA₂ := commutatorPairing_eighthPower_bundle _ A A' pr hpr W hL k _ (f' tT') (f' q') (p₂ _) (p₂ _) _ hA
    have hval : (∏ ab : Fin 8 × Fin 8, (unitOn (τ' (Multiplicative.ofAdd (c ab.1 (qw ab.2).y))) *
        unitOn (τ' (Multiplicative.ofAdd (c ab.2 (qw ab.1).y)))) ^ W ab.1 ab.2) =
        unitOn (τ' (Multiplicative.ofAdd (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)))) := by
      let ψ : Multiplicative D'.toPre.X →* Γ(Sp F, ⊤)ˣ :=
        (Units.map (Scheme.ΓSpecIso (CommRingCat.of F)).inv.hom.toMonoidHom).comp τ'
      have hψ : ∀ x, unitOn (τ' x) = ψ x := fun x => rfl
      simp only [hψ]
      rw [← sum_symmetrised_bilinear_matrix_eq W c (fun w => (qw w).y), ofAdd_sum, map_prod]
      refine Finset.prod_congr rfl fun ab _ => ?_
      rw [ofAdd_zsmul, map_zpow, ofAdd_add, map_mul]
    rw [hval] at hA₂
    have hu := GlobalTheory.weilIs_unique_fieldPoint _ A'.A A'.L A'.isLB F _ k _ _ _ _ hA' hA₂
    have hinv : e (∑ u, c u (∑ w, (W + W.transpose) u w • (qw w).y)) = fun w => (qw w).y := by
      have := he (e.symm fun w => (qw w).y)
      rw [e.apply_symm_apply] at this
      rw [this, e.apply_symm_apply]
    have h₁ : τ (Multiplicative.ofAdd (e q'.y v)) = τ (Multiplicative.ofAdd (qw v).y) := by
      have := hu
      simp only [τ', ev, MonoidHom.comp_apply, AddMonoidHom.toMultiplicative_apply_apply, toAdd_ofAdd,
        AddMonoidHom.comp_apply, Pi.evalAddMonoidHom_apply, AddEquiv.coe_toAddMonoidHom, hinv] at this
      exact this
    obtain ⟨z, hz, -⟩ := (q₁ (qw v) q).1 (by rw [hqw, hav])
    rw [ofAdd_sub, map_div, h₁, hz, ofAdd_add, map_mul, ofAdd_nsmul, map_pow, hτk, _root_.mul_one, div_self']
  obtain ⟨z, hz⟩ := GlobalTheory.T.exists_eq_nsmul_of_forall_char_pow_eq_one _ F k hkF _ key
  exact ⟨z, by rw [← hz]; abel⟩

end GlobalTheory.Poinc.Eq8.Labels
