import Mathlib
import ReciprocityTheory.DualLattices.CotangentSurjective
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsTight
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.StepOrderRes
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.NonzeroLocus
import Development.AutomorphicSpectrum.Definitions.CommutativeAlgebra.IsFinFlatSub
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.QuotientByFiniteFlatStatement
import Development.AutomorphicSpectrum.PublishedTheorems.Algebra₂.ZarhinStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.HodgeTateDatumStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.OrdinaryCurveStatement
import Development.AutomorphicSpectrum.Statements.AlgebraStatements.PolarisedFlagStatement
import Development.WeilBound.CoreStatements.HodgeTatePoints.RfTors
open ReciprocityTheory.PGsh.L2 ReciprocityTheory.PGsh.Up GlobalTheory.CompanionTheory.Ar.GR
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi
open ReciprocityTheory.ChartRestriction.G.Chart (sp spMap)
open scoped CategoryTheory.Obj CategoryTheory.MonObj
attribute [local instance] Over.cartesianMonoidalCategory
set_option maxHeartbeats 1000000 in
/- English proof (translation)
Introduce `p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt K`. Use `haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj`. Use `haveI : ValuationRing R := ValuationRing.iff_dvd_total.mpr ⟨fun a b => by`. Break down `le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h` into its components or cases. Conclude with `Or.inr (hv.dvd_of_le h)`.

Conclude with `Or.inl (hv.dvd_of_le h)⟩`. Use `haveI : IsLocalRing R := ValuationRing.isLocalRing R`. Use `haveI : IsBezout R := ValuationRing.instIsBezout`. Use `haveI : Module.Finite R T.A := T.fin`. Use `set I : Ideal T.A := vanIdeal T pt (K : Set N) with hI`.

Establish `hpts : ∀ x : N, pt x ^ p = 1` using `fun x => (hpt.range (pt x)).mpr ⟨x, rfl⟩`. Use `choose ev hev using fun x : N => (T.univ R (pt x) (hpts x)).exists`. Establish `huniq : ∀ (x : N) (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → φ = ev x` using `fun x φ h => (T.univ R (pt x) (hpts x)).unique h (hev x)`. Establish `memI : ∀ a : T.A, a ∈ I ↔ ∀ k ∈ K, ev k a = 0`. Introduce `a`.

Prove the components needed by the constructor for the conclusion. Introduce `ha k hk`. Establish `ha' : ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0` using `ha`. Conclude with `ha' k hk (ev k) (hev k)`. Introduce `ha show ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0`.

Introduce `k hk φ hφ`. Rewrite using `[huniq k φ hφ]`. Conclude with `ha k hk`. Take `⟨evbar, hevbar⟩ : ∃ e : K → ((T.A ⧸ I) →ₐ[R] R), ∀ k, (e k).comp (Ideal.Quotient.mkₐ R I) = ev k` from `⟨fun k => Ideal.Quotient.liftₐ I (ev k) (fun a ha => (memI a).mp ha k k.2), fun k => Ideal.Quotient.liftₐ_comp _ _ _⟩`. Establish `hsep1 : ∀ b : T.A ⧸ I, (∀ k : K, evbar k b = 0) → b = 0`.

Introduce `b hb`. Take `⟨a, rfl⟩` from `Ideal.Quotient.mkₐ_surjective R I b`. Rewrite using `[Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, memI]`. Introduce `k hk`. Establish `h1` using `hb ⟨k, hk⟩`.

Rewrite `h1` using `[← AlgHom.comp_apply, hevbar]`. Conclude with `h1`. Establish `htors : Submodule.torsion R (T.A ⧸ I) = ⊥`. Rewrite using `[eq_bot_iff]`. Introduce `b hb`.

Take `⟨r, hr⟩` from `(Submodule.mem_torsion_iff b).mp hb`. Rewrite using `[Submodule.mem_bot]`. Use `hsep1 b fun k => ?_` and prove the remaining obligations. Establish `h1` using `congrArg (evbar k) hr`. Rewrite `h1` using `[map_zero, Submonoid.smul_def, map_smul, smul_eq_mul]`.

Conclude with `(mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero r)`. Use `haveI : Module.Flat R (T.A ⧸ I) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr htors`. Use `haveI : Module.Finite R (T.A ⧸ I) := Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)`. Use `haveI : Module.Free R (T.A ⧸ I) := Module.free_of_flat_of_isLocalRing`. Establish `h0 : pt 0 = 1` using `mul_left_cancel (a := pt 0) (by rw [_root_.mul_one, ← hpt.add, add_zero])`.

Establish `hneg : ∀ x, pt (-x) = (pt x)⁻¹` using `fun x => eq_inv_of_mul_eq_one_left (by rw [← hpt.add, neg_add_cancel, h0])`. Establish `hE : ∀ k : K, spMap (evbar k) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y = pt k`. Introduce `k`. Rewrite using `[← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hevbar, hev]`. Establish `hpowA : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀` using `R) T.A), (f ≫ T.y) ^ p = 1 := fun f => by rw [← CategoryTheory.MonObj.comp_pow, T.y_p, CategoryTheory.MonObj.comp_one]`.

Establish `hu : (spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1` using `hpowA _`. Establish `hpowc : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀` using `R) (T.A ⧸ I)), (f ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 := fun f => by rw [← CategoryTheory.MonObj.comp_pow, hu, CategoryTheory.MonObj.comp_one]`. Take `⟨Λ, hΛt⟩ : ∃ L : K → K → (TensorProduct R (T.A ⧸ I) (T.A ⧸ I) →ₐ[R] R), ∀ k1 k2 x y, L k1 k2 (TensorProduct.tmul R x y) = evbar k1 x * evbar k2 y` from `⟨fun k1 k2 => Algebra.TensorProduct.lift (evbar k1) (evbar k2) (fun _ _ => Commute.all _ _), fun _ _ _ _ => Algebra.TensorProduct.lift_tmul _ _ _ _ _⟩`. Establish `hΛL : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeLeft = evbar k1` using `fun k1 k2 => AlgHom.ext fun b => by simp [hΛt]`. Establish `hΛR : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeRight = evbar k2` using `fun k1 k2 => AlgHom.ext fun b => by simp [hΛt]`.

Establish `hι : Function.Injective (Pi.algHom R (fun _ : K => R) evbar).toLinearMap`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `b hb`. Conclude with `hsep1 b fun k => by simpa using congrFun hb k`. Establish `key : ∀ (w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) (k1 k2 : K), (Pi.algHom R (fun _ : K => R) evbar).toLinearMap (TensorProduct.piScalarRight R R (T.A ⧸ I) K (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) k2) k1 = Λ k1 k2 w`.

Introduce `w k1 k2`. Proceed by induction on `w using TensorProduct.induction_on with`. Consider the case `zero => simp`. Consider the case `tmul x y => simp [hΛt, TensorProduct.piScalarRight_apply, mul_comm]`. Consider the case `add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]`.

Establish `hsep2 : ∀ w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I), (∀ k1 k2 : K, Λ k1 k2 w = 0) → w = 0`. Introduce `w hw`. Establish `h1 : TensorProduct.piScalarRight R R (T.A ⧸ I) K (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) = 0`. Use function extensionality and compare the values at `k2`. Apply `hι` to reduce the goal to its premises.

Use function extensionality and compare the values at `k1`. Rewrite using `[key, hw]`. Simplify using the standard rewrite rules. Rewrite `h1` using `[LinearEquiv.map_eq_zero_iff]`. Conclude with `(injective_iff_map_eq_zero _).mp (Module.Flat.lTensor_preserves_injective_linearMap _ hι) w h1`.

Use `⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `S _ _ φ φ' hφ`. Establish `e1 : spMap (φ.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y = spMap (φ'.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, Category.assoc, hφ]`. Establish `e2` using `(T.univ S _ (hpowA (spMap (φ.comp (Ideal.Quotient.mkₐ R I))))).unique rfl e1.symm`.

Use `AlgHom.ext fun b => ?_` and prove the remaining obligations. Take `⟨a, rfl⟩` from `Ideal.Quotient.mkₐ_surjective R I b`. Conclude with `DFunLike.congr_fun e2 a`. Introduce `S _ _`. Use `⟨(Algebra.ofId R S).comp (evbar 0), ?_⟩` and prove the remaining obligations.

Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hE]`. Use `show spMap (Algebra.ofId R S) ≫ pt 0 = 1`. Rewrite using `[h0, CategoryTheory.MonObj.comp_one]`. Establish `hm : ((spMap (Algebra.TensorProduct.includeLeft : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) * (spMap (Algebra.TensorProduct.includeRight : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T. …`. Rewrite using `[mul_pow, hpowc, hpowc, _root_.one_mul]`.

Take `⟨ψ0, hψ0⟩` from `(T.univ _ _ hm).exists`. Establish `hψI : ∀ a ∈ I, ψ0 a = 0`. Introduce `a ha`. Use `hsep2 _ fun k1 k2 => ?_` and prove the remaining obligations. Establish `e : spMap ((Λ k1 k2).comp ψ0) ≫ T.y = pt ((k1 : N) + k2)`.

Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.MonObj.comp_mul, ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeLeft), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛL, hE, ← Category.assoc (spMap (Λ …`. Rewrite using `[← AlgHom.comp_apply, huniq _ _ e]`. Conclude with `(memI a).mp ha _ (K.add_mem k1.2 k2.2)`. Introduce `S _ _ φ φ'`. Establish `hLR : (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp Algebra.TensorProduct.includeRight = φ'` using `AlgHom.ext fun b => by simp`.

Use `⟨(Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩` and prove the remaining obligations. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.MonObj.comp_mul]`. Rewrite using `[← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _))) (spMap Algebra.TensorProduct.includeLeft), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Algebra.TensorProduct.lift_comp_includeLeft, ← Category.assoc (spMap (Algebra.TensorProduct.l …`. Establish `hinv : ((spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)⁻¹) ^ p = 1` using `by rw [inv_pow, hu, inv_one]`. Take `⟨ψ0, hψ0⟩` from `(T.univ (T.A ⧸ I) _ hinv).exists`.

Establish `hψI : ∀ a ∈ I, ψ0 a = 0`. Introduce `a ha`. Use `hsep1 _ fun k => ?_` and prove the remaining obligations. Establish `e : spMap ((evbar k).comp ψ0) ≫ T.y = pt (-(k : N))`. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.GrpObj.comp_inv, hE, hneg]`.

Rewrite using `[← AlgHom.comp_apply, huniq _ _ e]`. Conclude with `(memI a).mp ha _ (K.neg_mem k.2)`. Introduce `S _ _ φ`. Use `⟨φ.comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩` and prove the remaining obligations. Rewrite using `[← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.GrpObj.comp_inv, inv_mul_cancel]`.
-/
theorem _root_.GlobalTheory.CompanionTheory.Relay.torsion_points_finite_flat_subgroup : ∀ (p : ℕ) [Fact p.Prime] (C : Type) [Field C] [IsAlgClosed C] [CharZero C] (v : Valuation C NNReal) (R : Type) [CommRing R] [Algebra R C], v.Integers R → v (p : C) < 1 → ∀ (G : Over (Spec (CommRingCat.of R))) [GrpObj G] [IsCommMonObj G], ∀ (T : TorsRep G p) (N : Type) [AddCommGroup N] [Fintype N] [DecidableEq N] (pt : N → (sp (R₀ := R) R ⟶ G)), IsTorsPts G p pt → ∀ K : AddSubgroup N, IsFinFlatSub G (T.A ⧸ vanIdeal T pt K) (spMap (Ideal.Quotient.mkₐ R (vanIdeal T pt K)) ≫ T.y) := by
  classical
  intro p _ C _ _ _ v R _ _ hv hp G _ _ T N _ _ _ pt hpt K
  haveI : IsDomain R := Function.Injective.isDomain (algebraMap R C) hv.hom_inj
  haveI : ValuationRing R := ValuationRing.iff_dvd_total.mpr ⟨fun a b => by
    rcases le_total (v (algebraMap R C a)) (v (algebraMap R C b)) with h | h
    · exact Or.inr (hv.dvd_of_le h)
    · exact Or.inl (hv.dvd_of_le h)⟩
  haveI : IsLocalRing R := ValuationRing.isLocalRing R
  haveI : IsBezout R := ValuationRing.instIsBezout
  haveI : Module.Finite R T.A := T.fin
  set I : Ideal T.A := vanIdeal T pt (K : Set N) with hI
  have hpts : ∀ x : N, pt x ^ p = 1 := fun x => (hpt.range (pt x)).mpr ⟨x, rfl⟩
  choose ev hev using fun x : N => (T.univ R (pt x) (hpts x)).exists
  have huniq : ∀ (x : N) (φ : T.A →ₐ[R] R), spMap φ ≫ T.y = pt x → φ = ev x :=
    fun x φ h => (T.univ R (pt x) (hpts x)).unique h (hev x)
  have memI : ∀ a : T.A, a ∈ I ↔ ∀ k ∈ K, ev k a = 0 := by
    intro a
    constructor
    · intro ha k hk
      have ha' : ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0 := ha
      exact ha' k hk (ev k) (hev k)
    · intro ha
      show ∀ k ∈ (K : Set N), ∀ φ : T.A →ₐ[R] R, spMap φ ≫ T.y = pt k → φ a = 0
      intro k hk φ hφ
      rw [huniq k φ hφ]
      exact ha k hk
  obtain ⟨evbar, hevbar⟩ : ∃ e : K → ((T.A ⧸ I) →ₐ[R] R),
      ∀ k, (e k).comp (Ideal.Quotient.mkₐ R I) = ev k :=
    ⟨fun k => Ideal.Quotient.liftₐ I (ev k) (fun a ha => (memI a).mp ha k k.2),
      fun k => Ideal.Quotient.liftₐ_comp _ _ _⟩
  have hsep1 : ∀ b : T.A ⧸ I, (∀ k : K, evbar k b = 0) → b = 0 := by
    intro b hb
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    rw [Ideal.Quotient.mkₐ_eq_mk, Ideal.Quotient.eq_zero_iff_mem, memI]
    intro k hk
    have h1 := hb ⟨k, hk⟩
    rw [← AlgHom.comp_apply, hevbar] at h1
    exact h1
  have htors : Submodule.torsion R (T.A ⧸ I) = ⊥ := by
    rw [eq_bot_iff]
    intro b hb
    obtain ⟨r, hr⟩ := (Submodule.mem_torsion_iff b).mp hb
    rw [Submodule.mem_bot]
    refine hsep1 b fun k => ?_
    have h1 := congrArg (evbar k) hr
    rw [map_zero, Submonoid.smul_def, map_smul, smul_eq_mul] at h1
    exact (mul_eq_zero.mp h1).resolve_left (nonZeroDivisors.coe_ne_zero r)
  haveI : Module.Flat R (T.A ⧸ I) := (Module.Flat.flat_iff_torsion_eq_bot_of_isBezout).mpr htors
  haveI : Module.Finite R (T.A ⧸ I) :=
    Module.Finite.of_surjective (Ideal.Quotient.mkₐ R I).toLinearMap (Ideal.Quotient.mkₐ_surjective R I)
  haveI : Module.Free R (T.A ⧸ I) := Module.free_of_flat_of_isLocalRing
  have h0 : pt 0 = 1 := mul_left_cancel (a := pt 0) (by rw [_root_.mul_one, ← hpt.add, add_zero])
  have hneg : ∀ x, pt (-x) = (pt x)⁻¹ := fun x =>
    eq_inv_of_mul_eq_one_left (by rw [← hpt.add, neg_add_cancel, h0])
  have hE : ∀ k : K, spMap (evbar k) ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y = pt k := by
    intro k
    rw [← Category.assoc, ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hevbar, hev]
  have hpowA : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) T.A), (f ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, T.y_p, CategoryTheory.MonObj.comp_one]
  have hu : (spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 := hpowA _
  have hpowc : ∀ {X : Over (Spec (CommRingCat.of R))} (f : X ⟶ sp (R₀ := R) (T.A ⧸ I)),
      (f ≫ spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) ^ p = 1 :=
    fun f => by rw [← CategoryTheory.MonObj.comp_pow, hu, CategoryTheory.MonObj.comp_one]
  obtain ⟨Λ, hΛt⟩ : ∃ L : K → K → (TensorProduct R (T.A ⧸ I) (T.A ⧸ I) →ₐ[R] R),
      ∀ k1 k2 x y, L k1 k2 (TensorProduct.tmul R x y) = evbar k1 x * evbar k2 y :=
    ⟨fun k1 k2 => Algebra.TensorProduct.lift (evbar k1) (evbar k2) (fun _ _ => Commute.all _ _),
      fun _ _ _ _ => Algebra.TensorProduct.lift_tmul _ _ _ _ _⟩
  have hΛL : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeLeft = evbar k1 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hΛR : ∀ k1 k2, (Λ k1 k2).comp Algebra.TensorProduct.includeRight = evbar k2 := fun k1 k2 =>
    AlgHom.ext fun b => by simp [hΛt]
  have hι : Function.Injective (Pi.algHom R (fun _ : K => R) evbar).toLinearMap := by
    rw [injective_iff_map_eq_zero]
    intro b hb
    exact hsep1 b fun k => by simpa using congrFun hb k
  have key : ∀ (w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) (k1 k2 : K),
      (Pi.algHom R (fun _ : K => R) evbar).toLinearMap
        (TensorProduct.piScalarRight R R (T.A ⧸ I) K
          (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) k2) k1 =
        Λ k1 k2 w := by
    intro w k1 k2
    induction w using TensorProduct.induction_on with
    | zero => simp
    | tmul x y => simp [hΛt, TensorProduct.piScalarRight_apply, mul_comm]
    | add x y hx hy => simp only [map_add, Pi.add_apply, hx, hy]
  have hsep2 : ∀ w : TensorProduct R (T.A ⧸ I) (T.A ⧸ I), (∀ k1 k2 : K, Λ k1 k2 w = 0) → w = 0 := by
    intro w hw
    have h1 : TensorProduct.piScalarRight R R (T.A ⧸ I) K
        (((Pi.algHom R (fun _ : K => R) evbar).toLinearMap.lTensor (T.A ⧸ I)) w) = 0 := by
      funext k2
      apply hι
      funext k1
      rw [key, hw]
      simp
    rw [LinearEquiv.map_eq_zero_iff] at h1
    exact (injective_iff_map_eq_zero _).mp
      (Module.Flat.lTensor_preserves_injective_linearMap _ hι) w h1
  refine ⟨inferInstance, inferInstance, ?_, ?_, ?_, ?_⟩
  · intro S _ _ φ φ' hφ
    have e1 : spMap (φ.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y =
        spMap (φ'.comp (Ideal.Quotient.mkₐ R I)) ≫ T.y := by
      rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, ← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
        Category.assoc, hφ]
    have e2 := (T.univ S _ (hpowA (spMap (φ.comp (Ideal.Quotient.mkₐ R I))))).unique rfl e1.symm
    refine AlgHom.ext fun b => ?_
    obtain ⟨a, rfl⟩ := Ideal.Quotient.mkₐ_surjective R I b
    exact DFunLike.congr_fun e2 a
  · intro S _ _
    refine ⟨(Algebra.ofId R S).comp (evbar 0), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hE]
    show spMap (Algebra.ofId R S) ≫ pt 0 = 1
    rw [h0, CategoryTheory.MonObj.comp_one]
  · have hm : ((spMap (Algebra.TensorProduct.includeLeft : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y) *
        (spMap (Algebra.TensorProduct.includeRight : (T.A ⧸ I) →ₐ[R] TensorProduct R (T.A ⧸ I) (T.A ⧸ I)) ≫
          spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)) ^ p = 1 := by
      rw [mul_pow, hpowc, hpowc, _root_.one_mul]
    obtain ⟨ψ0, hψ0⟩ := (T.univ _ _ hm).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep2 _ fun k1 k2 => ?_
      have e : spMap ((Λ k1 k2).comp ψ0) ≫ T.y = pt ((k1 : N) + k2) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.MonObj.comp_mul,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeLeft),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛL, hE,
          ← Category.assoc (spMap (Λ k1 k2)) (spMap Algebra.TensorProduct.includeRight),
          ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hΛR, hE, hpt.add]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.add_mem k1.2 k2.2)
    intro S _ _ φ φ'
    have hLR : (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
        Algebra.TensorProduct.includeRight = φ' := AlgHom.ext fun b => by simp
    refine ⟨(Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)).comp
      (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.MonObj.comp_mul]
    rw [← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeLeft),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Algebra.TensorProduct.lift_comp_includeLeft,
      ← Category.assoc (spMap (Algebra.TensorProduct.lift φ φ' (fun _ _ => Commute.all _ _)))
        (spMap Algebra.TensorProduct.includeRight),
      ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, hLR]
  · have hinv : ((spMap (Ideal.Quotient.mkₐ R I) ≫ T.y)⁻¹) ^ p = 1 := by rw [inv_pow, hu, inv_one]
    obtain ⟨ψ0, hψ0⟩ := (T.univ (T.A ⧸ I) _ hinv).exists
    have hψI : ∀ a ∈ I, ψ0 a = 0 := by
      intro a ha
      refine hsep1 _ fun k => ?_
      have e : spMap ((evbar k).comp ψ0) ≫ T.y = pt (-(k : N)) := by
        rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc, hψ0, CategoryTheory.GrpObj.comp_inv,
          hE, hneg]
      rw [← AlgHom.comp_apply, huniq _ _ e]
      exact (memI a).mp ha _ (K.neg_mem k.2)
    intro S _ _ φ
    refine ⟨φ.comp (Ideal.Quotient.liftₐ I ψ0 hψI), ?_⟩
    rw [← ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp, Category.assoc,
      ← Category.assoc (spMap (Ideal.Quotient.liftₐ I ψ0 hψI)), ReciprocityTheory.ChartRestriction.G.Chart.spMap_comp,
      Ideal.Quotient.liftₐ_comp, hψ0, CategoryTheory.GrpObj.comp_inv, inv_mul_cancel]
