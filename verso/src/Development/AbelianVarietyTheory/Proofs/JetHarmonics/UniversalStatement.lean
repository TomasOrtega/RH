import Mathlib
import Development.AbelianVarietyTheory.Definitions.Jets.JetsOnCopiesCompatibleFrames
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.DiscreteValuationRings.TwistBCPf
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.SaturationChartsHolds
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.SurjectiveOfKerLeMapSupSq

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj
attribute [local instance] Over.cartesianMonoidalCategory
namespace GlobalTheory.PowGerm.UnivJets

section Alg
variable {V : Type} [CommRing V]

/- English proof (translation)
Use `first`. Consider the case `exact @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq`. Consider the case `exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq`. Consider the case `(apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)`. Consider the case `(intros; apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)`.

Consider the case `(intros; apply @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> first | assumption | infer_instance)`. Consider the case `(intros; exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq ..)`.
-/
theorem surj_of_sq {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (aug : B →ₐ[V] V) (m : ℕ) (hI : RingHom.ker aug ^ (m + 1) = ⊥) (J : Ideal A)
    (h1 : J.map f ≤ RingHom.ker aug) (h2 : RingHom.ker aug ≤ J.map f ⊔ RingHom.ker aug ^ 2) :
    Function.Surjective f := by
  first
  | exact @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq
  | exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq
  | (apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)
  | (intros; apply _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> assumption)
  | (intros; apply @_root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq <;> first | assumption | infer_instance)
  | (intros; exact _root_.GlobalTheory.SurjectiveOfKerSq.surjective_of_ker_le_map_sup_sq ..)

open Chart (JetR zR jetAug_zR jet_ext jetLift jetLift_zR ker_jetAug_pow zR_mem_ker)

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Introduce `x hx`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`. Establish `hp : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0` using `hx`. Use `Chart.sub_const_mem_span_X (R := V) p` as an intermediate fact.

Rewrite `this` using `[hp, map_zero, sub_zero]`. Conclude with `Ideal.mem_map_of_mem _ this`. Rewrite using `[Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `zR_mem_ker m j`.
-/
theorem ker_aug_eq (κ : Type) (m : ℕ) : RingHom.ker (Chart.jetAug V κ m) =
    (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ V))).map (Ideal.Quotient.mk _) := by
  apply le_antisymm
  · intro x hx
    obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
    have hp : MvPolynomial.aeval (fun _ : κ => (0 : V)) p = 0 := hx
    have := Chart.sub_const_mem_span_X (R := V) p
    rw [hp, map_zero, sub_zero] at this
    exact Ideal.mem_map_of_mem _ this
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
    exact zR_mem_ker m j

/- English proof (translation)
Rewrite using `[ker_aug_eq, Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨j, rfl⟩, rfl⟩`. Conclude with `h j`.
-/
theorem ker_aug_le {κ : Type} {m : ℕ} {K : Ideal (JetR V κ m)} (h : ∀ j, zR m j ∈ K) :
    RingHom.ker (Chart.jetAug V κ m) ≤ K := by
  rw [ker_aug_eq, Ideal.map_span, Ideal.span_le]
  rintro _ ⟨_, ⟨j, rfl⟩, rfl⟩
  exact h j

/- English proof (translation)
Use `haveI : Algebra.IsIntegral V (JetR V κ m) := ⟨fun w => by`. Establish `hw : w - algebraMap V _ (Chart.jetAug V κ m w) ∈ RingHom.ker (Chart.jetAug V κ m)`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes]`. Simplify using the standard rewrite rules. Establish `h0 : (w - algebraMap V _ (Chart.jetAug V κ m w)) ^ (m + 1) = 0`.

Use `Ideal.pow_mem_pow hw (m + 1)` as an intermediate fact. Rewrite `this` using `[ker_jetAug_pow, Ideal.mem_bot]`. Then use the resulting hypothesis. Establish `h1 : IsIntegral V (w - algebraMap V _ (Chart.jetAug V κ m w))` using `IsIntegral.of_pow (Nat.succ_pos m) (by rw [h0]; exact isIntegral_zero)`. Use `h1.add (isIntegral_algebraMap (x := Chart.jetAug V κ m w))` as an intermediate fact. Rewrite using `[sub_add_cancel] at this⟩` and apply the resulting hypothesis.

Conclude with `Algebra.IsIntegral.finite`.
-/
theorem jet_finite (κ : Type) [Finite κ] (m : ℕ) : Module.Finite V (JetR V κ m) := by
  haveI : Algebra.IsIntegral V (JetR V κ m) := ⟨fun w => by
    have hw : w - algebraMap V _ (Chart.jetAug V κ m w) ∈ RingHom.ker (Chart.jetAug V κ m) := by
      rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
      simp
    have h0 : (w - algebraMap V _ (Chart.jetAug V κ m w)) ^ (m + 1) = 0 := by
      have := Ideal.pow_mem_pow hw (m + 1)
      rwa [ker_jetAug_pow, Ideal.mem_bot] at this
    have h1 : IsIntegral V (w - algebraMap V _ (Chart.jetAug V κ m w)) :=
      IsIntegral.of_pow (Nat.succ_pos m) (by rw [h0]; exact isIntegral_zero)
    have := h1.add (isIntegral_algebraMap (x := Chart.jetAug V κ m w))
    rwa [sub_add_cancel] at this⟩
  exact Algebra.IsIntegral.finite

/- English proof (translation)
Use `surj_of_sq f (Chart.jetAug V κ m) m (ker_jetAug_pow κ m) (Ideal.span (Set.range (zR m))) ?_ ?_` and prove the remaining obligations. Rewrite using `[Ideal.map_span, Ideal.span_le]`. Introduce and unpack `_ ⟨_, ⟨i, rfl⟩, rfl⟩`. Use `Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hf i)) (zR_mem_ker (R := V) m (β i))` as an intermediate fact. Rewrite `this` using `[sub_add_cancel]`. Then use the resulting hypothesis.

Use `ker_aug_le fun j => ?_` and prove the remaining obligations. Take `⟨i, rfl⟩` from `hβ j`. Establish `h1 : f (zR m i) ∈ (Ideal.span (Set.range (zR (R` using `V) (κ := σ) m))).map f := Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)`. Use `Ideal.sub_mem _ (Ideal.mem_sup_left (T := RingHom.ker (Chart.jetAug V κ m) ^ 2) h1) (Ideal.mem_sup_right (hf i))` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem surj_of_first_order {σ κ : Type} {m : ℕ} (β : σ → κ) (hβ : Function.Surjective β)
    (f : JetR V σ m →ₐ[V] JetR V κ m)
    (hf : ∀ i, f (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2) : Function.Surjective f := by
  refine surj_of_sq f (Chart.jetAug V κ m) m (ker_jetAug_pow κ m) (Ideal.span (Set.range (zR m))) ?_ ?_
  · rw [Ideal.map_span, Ideal.span_le]
    rintro _ ⟨_, ⟨i, rfl⟩, rfl⟩
    have := Ideal.add_mem _ (Ideal.pow_le_self two_ne_zero (hf i)) (zR_mem_ker (R := V) m (β i))
    rwa [sub_add_cancel] at this
  · refine ker_aug_le fun j => ?_
    obtain ⟨i, rfl⟩ := hβ j
    have h1 : f (zR m i) ∈ (Ideal.span (Set.range (zR (R := V) (κ := σ) m))).map f :=
      Ideal.mem_map_of_mem _ (Ideal.subset_span ⟨i, rfl⟩)
    have := Ideal.sub_mem _ (Ideal.mem_sup_left (T := RingHom.ker (Chart.jetAug V κ m) ^ 2) h1)
      (Ideal.mem_sup_right (hf i))
    rwa [sub_sub_cancel] at this

/- English proof (translation)
Use `⟨?_, surj_of_first_order β β.surjective f hf⟩` and prove the remaining obligations. Set `r : JetR V κ m →ₐ[V] JetR V σ m` to `jetLift V (RingHom.ker (Chart.jetAug V σ m)) (ker_jetAug_pow σ m) (fun k => zR m (β.symm k)) (fun k => zR_mem_ker m _)`. Establish `hr : ∀ k, r (zR m k) = zR m (β.symm k)` using `fun k => jetLift_zR _ _ _ _ k`. Establish `hle : (RingHom.ker (Chart.jetAug V κ m)).map r ≤ RingHom.ker (Chart.jetAug V σ m)`. Rewrite using `[Ideal.map_le_iff_le_comap]`.

Use `ker_aug_le fun j => ?_` and prove the remaining obligations. Rewrite using `[Ideal.mem_comap, hr]`. Conclude with `zR_mem_ker m _`. Establish `hs : Function.Surjective (r.comp f)`. Use `surj_of_first_order id Function.surjective_id _ fun i => ?_` and prove the remaining obligations.

Establish `h1` using `Ideal.mem_map_of_mem r (hf i)`. Rewrite `h1` using `[Ideal.map_pow, map_sub, hr, Equiv.symm_apply_apply]`. Conclude with `Ideal.pow_right_mono hle 2 h1`. Use `haveI := jet_finite (V := V) σ m`. Establish `hi : Function.Injective (r.comp f)` using `OrzechProperty.injective_of_surjective_endomorphism (r.comp f).toLinearMap hs`.

Conclude with `Function.Injective.of_comp (f := r) hi`.
-/
theorem bij_of_first_order {σ κ : Type} [Finite σ] {m : ℕ} (β : σ ≃ κ) (f : JetR V σ m →ₐ[V] JetR V κ m)
    (hf : ∀ i, f (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2) : Function.Bijective f := by
  refine ⟨?_, surj_of_first_order β β.surjective f hf⟩
  let r : JetR V κ m →ₐ[V] JetR V σ m := jetLift V (RingHom.ker (Chart.jetAug V σ m)) (ker_jetAug_pow σ m)
    (fun k => zR m (β.symm k)) (fun k => zR_mem_ker m _)
  have hr : ∀ k, r (zR m k) = zR m (β.symm k) := fun k => jetLift_zR _ _ _ _ k
  have hle : (RingHom.ker (Chart.jetAug V κ m)).map r ≤ RingHom.ker (Chart.jetAug V σ m) := by
    rw [Ideal.map_le_iff_le_comap]
    refine ker_aug_le fun j => ?_
    rw [Ideal.mem_comap, hr]
    exact zR_mem_ker m _
  have hs : Function.Surjective (r.comp f) := by
    refine surj_of_first_order id Function.surjective_id _ fun i => ?_
    have h1 := Ideal.mem_map_of_mem r (hf i)
    rw [Ideal.map_pow, map_sub, hr, Equiv.symm_apply_apply] at h1
    exact Ideal.pow_right_mono hle 2 h1
  haveI := jet_finite (V := V) σ m
  have hi : Function.Injective (r.comp f) :=
    OrzechProperty.injective_of_surjective_endomorphism (r.comp f).toLinearMap hs
  exact Function.Injective.of_comp (f := r) hi

/- English proof (translation)
Establish `h1 : w ∈ Ideal.span (Set.range (zR (R` using `V) (κ := κ) 1)) := ker_aug_le (fun j => Ideal.subset_span (Set.mem_range_self j)) (RingHom.mem_ker.2 hw)`. Take `⟨q, rfl⟩` from `Ideal.mem_span_range_iff_exists_fun.1 h1`. Use `⟨fun k => Chart.jetAug V κ 1 (q k), Finset.sum_congr rfl fun k _ => ?_⟩` and prove the remaining obligations. Establish `hq : q k - algebraMap V _ (Chart.jetAug V κ 1 (q k)) ∈ RingHom.ker (Chart.jetAug V κ 1)`. Rewrite using `[RingHom.mem_ker, map_sub, AlgHom.commutes]`.

Simplify using the standard rewrite rules. Use `Ideal.mul_mem_mul hq (zR_mem_ker (R := V) 1 k)` as an intermediate fact. Rewrite `this` using `[← pow_two, show (2 : ℕ) = 1 + 1 from rfl, ker_jetAug_pow, Ideal.mem_bot, sub_mul, sub_eq_zero]`. Rewrite using `[this, Algebra.smul_def]`.
-/
theorem exists_lin {κ : Type} [Fintype κ] (w : JetR V κ 1) (hw : Chart.jetAug V κ 1 w = 0) :
    ∃ c : κ → V, w = ∑ k, c k • zR 1 k := by
  have h1 : w ∈ Ideal.span (Set.range (zR (R := V) (κ := κ) 1)) :=
    ker_aug_le (fun j => Ideal.subset_span (Set.mem_range_self j)) (RingHom.mem_ker.2 hw)
  obtain ⟨q, rfl⟩ := Ideal.mem_span_range_iff_exists_fun.1 h1
  refine ⟨fun k => Chart.jetAug V κ 1 (q k), Finset.sum_congr rfl fun k _ => ?_⟩
  have hq : q k - algebraMap V _ (Chart.jetAug V κ 1 (q k)) ∈ RingHom.ker (Chart.jetAug V κ 1) := by
    rw [RingHom.mem_ker, map_sub, AlgHom.commutes]
    simp
  have := Ideal.mul_mem_mul hq (zR_mem_ker (R := V) 1 k)
  rw [← pow_two, show (2 : ℕ) = 1 + 1 from rfl, ker_jetAug_pow, Ideal.mem_bot, sub_mul, sub_eq_zero] at this
  rw [this, Algebra.smul_def]

def toFirst (κ : Type) (m : ℕ) : JetR V κ (m + 1) →ₐ[V] JetR V κ 1 :=
  Ideal.Quotient.factorₐ V (Ideal.pow_le_pow_right (by omega))

/- English proof (translation)
Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective w`. Establish `hp : p ∈ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ V))) ^ (1 + 1)` using `Ideal.Quotient.eq_zero_iff_mem.1 hw`. Rewrite using `[ker_aug_eq, ← Ideal.map_pow]`. Conclude with `Ideal.mem_map_of_mem _ hp`.
-/
theorem mem_sq_of_toFirst {κ : Type} {m : ℕ} (w : JetR V κ (m + 1)) (hw : toFirst κ m w = 0) :
    w ∈ RingHom.ker (Chart.jetAug V κ (m + 1)) ^ 2 := by
  obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective w
  have hp : p ∈ (Ideal.span (Set.range (MvPolynomial.X : κ → MvPolynomial κ V))) ^ (1 + 1) :=
    Ideal.Quotient.eq_zero_iff_mem.1 hw
  rw [ker_aug_eq, ← Ideal.map_pow]
  exact Ideal.mem_map_of_mem _ hp

end Alg

section Geo
variable {V : Type} [CommRing V] {G : Over (Spec (CommRingCat.of V))} [GrpObj G]
open Chart (JetR zR jetAug_zR jet_ext ker_jetAug_pow zR_mem_ker jetTruncR dualLift dualLift_zR fstD kerD_sq)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Conclude with `Spec.map_id _`.
-/
theorem spMap_id' (A : Type) [CommRing A] [Algebra V A] : Chart.spMap (AlgHom.id V A) = 𝟙 _ := by
  apply Over.OverMorphism.ext
  exact Spec.map_id _

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem toFirst_zR (κ : Type) (m : ℕ) (j : κ) : toFirst (V := V) κ m (zR (m + 1) j) = zR 1 j := rfl

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem trunc_zR (κ : Type) (m : ℕ) (j : κ) : jetTruncR V κ m (zR (m + 1) j) = zR m j := rfl

/- English proof (translation)
The claim follows from `jet_ext fun j => by rw [AlgHom.comp_apply, trunc_zR, toFirst_zR, toFirst_zR]`.
-/
theorem toFirst_succ (κ : Type) (m : ℕ) :
    toFirst (V := V) κ (m + 1) = (toFirst κ m).comp (jetTruncR V κ (m + 1)) :=
  jet_ext fun j => by rw [AlgHom.comp_apply, trunc_zR, toFirst_zR, toFirst_zR]

/- English proof (translation)
The claim follows from `jet_ext fun j => toFirst_zR κ 0 j`.
-/
theorem toFirst_zero (κ : Type) : toFirst (V := V) κ 0 = AlgHom.id V (JetR V κ 1) :=
  jet_ext fun j => toFirst_zR κ 0 j

omit [GrpObj G] in
/- English proof (translation)
Proceed by induction on `m with`. Consider the case `zero`. Establish `h : Chart.spMap (AlgHom.id V (JetR V κ 1)) ≫ z 1 = z 1` using `by rw [spMap_id', Category.id_comp]`. Conclude with `(congrArg (fun f : JetR V κ 1 →ₐ[V] JetR V κ 1 => Chart.spMap f ≫ z 1) (toFirst_zero κ)).trans h`. Consider the case `succ m ih => rw [toFirst_succ, ← Chart.spMap_comp, Category.assoc, htr, ih]`.
-/
theorem toFirst_comp {κ : Type} (z : ∀ m, Chart.sp (R₀ := V) (JetR V κ m) ⟶ G)
    (htr : ∀ m, Chart.spMap (jetTruncR V κ m) ≫ z (m + 1) = z m) (m : ℕ) :
    Chart.spMap (toFirst κ m) ≫ z (m + 1) = z 1 := by
  induction m with
  | zero =>
    have h : Chart.spMap (AlgHom.id V (JetR V κ 1)) ≫ z 1 = z 1 := by rw [spMap_id', Category.id_comp]
    exact (congrArg (fun f : JetR V κ 1 →ₐ[V] JetR V κ 1 => Chart.spMap f ≫ z 1) (toFirst_zero κ)).trans h
  | succ m ih => rw [toFirst_succ, ← Chart.spMap_comp, Category.assoc, htr, ih]

/- English proof (translation)
Use `choose ψ hψ using fun m => (hx.2.2 _ (Chart.jetAug V κ m) m (ker_jetAug_pow κ m) (z m) (haug m)).exists`. Establish `hψ0 : ∀ m i, Chart.jetAug V κ m (ψ m (zR m i)) = 0` using `fun m i => (AlgHom.congr_fun (hψ m).1 (zR m i)).trans (jetAug_zR m i)`. Establish `htf : ∀ j, (fstD V).comp (t j) = Chart.jetAug V κ 1` using `fun j => jet_ext fun k => by`. Take `⟨k, rfl⟩` from `β.surjective k`. Rewrite using `[AlgHom.comp_apply, ht, jetAug_zR]`.

Apply the tactic sequence `split_ifs <;> rfl`. Establish `h1 : ∀ j, (t j).comp (ψ 1) = dualLift (Pi.single j 1)` using `fun j => by`. Use `(hx.2.2 _ (fstD V) 1 kerD_sq _ (Chart.isTan_dualLift hx (Pi.single j 1))).unique ⟨?_, ?_⟩ ⟨Chart.fstD_comp_dualLift _, rfl⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, htf, (hψ 1).1]`. Rewrite using `[← hdir, ← Chart.spMap_comp, Category.assoc, ← (hψ 1).2]`.

Establish `h2 : ∀ i, ψ 1 (zR 1 i) = zR 1 (β i)` using `fun i => by`. Take `⟨c, hc⟩` from `exists_lin _ (hψ0 1 i)`. Establish `hcj : ∀ j, c (β j) = if j = i then 1 else 0` using `fun j => by`. Establish `e` using `congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (h1 j) (zR 1 i))`. Rewrite `e` using `[AlgHom.comp_apply, hc, dualLift_zR, TrivSqZeroExt.snd_inr, ← β.sum_comp, map_sum, TrivSqZeroExt.snd_sum, Finset.sum_eq_single j]`.

Rewrite `e` using `[map_smul, ht, if_pos rfl, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one, Pi.single_apply]`. Rewrite using `[e]`. Simplify using `only [eq_comm]`. Introduce `k _ hk`. Rewrite using `[map_smul, ht, if_neg hk, smul_zero, TrivSqZeroExt.snd_zero]`.

Introduce `h`. Conclude with `absurd (Finset.mem_univ j) h`. Rewrite using `[hc, ← β.sum_comp, Finset.sum_eq_single i]`. Rewrite using `[hcj, if_pos rfl, one_smul]`. Introduce `k _ hk`.

Rewrite using `[hcj, if_neg hk, zero_smul]`. Introduce `h`. Conclude with `absurd (Finset.mem_univ i) h`. Establish `h3 : ∀ m, (toFirst κ m).comp (ψ (m + 1)) = (ψ 1).comp (toFirst (Fin d) m)` using `fun m => by`. Establish `hp : RingHom.ker (Chart.jetAug V κ 1) ^ (m + 1 + 1) = ⊥` using `le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans (ker_jetAug_pow κ 1).le)`.

Establish `ha : ∀ κ' : Type, (Chart.jetAug V κ' 1).comp (toFirst κ' m) = Chart.jetAug V κ' (m + 1)` using `fun κ' => jet_ext fun k => (jetAug_zR (R := V) 1 k).trans (jetAug_zR (R := V) (m + 1) k).symm`. Use `(hx.2.2 _ (Chart.jetAug V κ 1) (m + 1) hp (z 1) (haug 1)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, ha, (hψ _).1]`. Rewrite using `[← Chart.spMap_comp, Category.assoc, ← (hψ _).2, toFirst_comp z htr]`. Rewrite using `[← AlgHom.comp_assoc, (hψ _).1, ha]`.

Rewrite using `[← Chart.spMap_comp, Category.assoc, toFirst_comp x hx.1, ← (hψ _).2]`. Establish `h4 : ∀ m i, ψ m (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2`. Introduce `m i`. Consider the cases of `m with`. Consider the case `zero`.

Establish `hb : RingHom.ker (Chart.jetAug V κ 0) = ⊥` using `(pow_one _).symm.trans (ker_jetAug_pow κ 0)`. Establish `: ψ 0 (zR 0 i) - zR 0 (β i) ∈ RingHom.ker (Chart.jetAug V κ 0)` using `Ideal.sub_mem _ (hψ0 0 i) (zR_mem_ker 0 _)`. Rewrite `this` using `[hb, Ideal.mem_bot]`. Rewrite using `[this]`. Conclude with `Ideal.zero_mem _`.

Consider the case `succ m`. Apply `mem_sq_of_toFirst` to reduce the goal to its premises. Rewrite using `[map_sub, sub_eq_zero]`. Conclude with `(AlgHom.congr_fun (h3 m) (zR (m + 1) i)).trans (h2 i)`. Set `e` to `AlgEquiv.ofBijective (ψ m) (bij_of_first_order β (ψ m) (h4 m))`.

Establish `he : (e.symm : JetR V κ m →ₐ[V] JetR V (Fin d) m).comp (ψ m) = AlgHom.id V _` using `AlgHom.ext fun w => e.symm_apply_apply w`. Establish `he' : (ψ m).comp (e.symm : JetR V κ m →ₐ[V] JetR V (Fin d) m) = AlgHom.id V _` using `AlgHom.ext fun w => e.apply_symm_apply w`. Take `⟨φ, ⟨hφ1, hφ2⟩, hu⟩` from `hx.2.2 A aug m hA y hy`. Use `⟨φ.comp e.symm, ⟨?_, ?_⟩, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, hφ1, ← (hψ m).1, AlgHom.comp_assoc, he', AlgHom.comp_id]`.

Rewrite using `[(hψ m).2, ← Category.assoc, Chart.spMap_comp, AlgHom.comp_assoc, he, AlgHom.comp_id]`. Conclude with `hφ2`. Introduce and unpack `φ' ⟨h5, h6⟩`. Rewrite `h6` using `[(hψ m).2, ← Category.assoc, Chart.spMap_comp]`. Use `hu (φ'.comp (ψ m)) ⟨by rw [← AlgHom.comp_assoc, h5, (hψ m).1], h6⟩` as an intermediate fact.

Rewrite using `[← this, AlgHom.comp_assoc, he', AlgHom.comp_id]`.
-/
theorem univ_of_dirs {d : ℕ} {κ : Type} [Fintype κ] (β : Fin d ≃ κ)
    {x : ∀ m, Chart.sp (R₀ := V) (JetR V (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (z : ∀ m, Chart.sp (R₀ := V) (JetR V κ m) ⟶ G)
    (htr : ∀ m, Chart.spMap (jetTruncR V κ m) ≫ z (m + 1) = z m)
    (haug : ∀ m, Chart.spMap (Chart.jetAug V κ m) ≫ z m = 1)
    (t : Fin d → (JetR V κ 1 →ₐ[V] DualNumber V))
    (ht : ∀ j k, t j (zR 1 (β k)) = if k = j then DualNumber.eps else 0)
    (hdir : ∀ j, Chart.spMap (t j) ≫ z 1 = Chart.spMap (dualLift (Pi.single j 1)) ≫ x 1)
    (A : Type) [CommRing A] [Algebra V A] (aug : A →ₐ[V] V) (m : ℕ) (hA : RingHom.ker aug ^ (m + 1) = ⊥)
    (y : Chart.sp (R₀ := V) A ⟶ G) (hy : Chart.spMap aug ≫ y = 1) :
    ∃! ψ : JetR V κ m →ₐ[V] A, aug.comp ψ = Chart.jetAug V κ m ∧ y = Chart.spMap ψ ≫ z m := by
  choose ψ hψ using fun m => (hx.2.2 _ (Chart.jetAug V κ m) m (ker_jetAug_pow κ m) (z m) (haug m)).exists
  have hψ0 : ∀ m i, Chart.jetAug V κ m (ψ m (zR m i)) = 0 := fun m i =>
    (AlgHom.congr_fun (hψ m).1 (zR m i)).trans (jetAug_zR m i)
  have htf : ∀ j, (fstD V).comp (t j) = Chart.jetAug V κ 1 := fun j => jet_ext fun k => by
    obtain ⟨k, rfl⟩ := β.surjective k
    rw [AlgHom.comp_apply, ht, jetAug_zR]
    split_ifs <;> rfl
  have h1 : ∀ j, (t j).comp (ψ 1) = dualLift (Pi.single j 1) := fun j => by
    refine (hx.2.2 _ (fstD V) 1 kerD_sq _ (Chart.isTan_dualLift hx (Pi.single j 1))).unique ⟨?_, ?_⟩
      ⟨Chart.fstD_comp_dualLift _, rfl⟩
    · rw [← AlgHom.comp_assoc, htf, (hψ 1).1]
    · rw [← hdir, ← Chart.spMap_comp, Category.assoc, ← (hψ 1).2]
  have h2 : ∀ i, ψ 1 (zR 1 i) = zR 1 (β i) := fun i => by
    obtain ⟨c, hc⟩ := exists_lin _ (hψ0 1 i)
    have hcj : ∀ j, c (β j) = if j = i then 1 else 0 := fun j => by
      have e := congrArg TrivSqZeroExt.snd (AlgHom.congr_fun (h1 j) (zR 1 i))
      rw [AlgHom.comp_apply, hc, dualLift_zR, TrivSqZeroExt.snd_inr, ← β.sum_comp, map_sum, TrivSqZeroExt.snd_sum,
        Finset.sum_eq_single j] at e
      · rw [map_smul, ht, if_pos rfl, TrivSqZeroExt.snd_smul, DualNumber.snd_eps, smul_eq_mul, _root_.mul_one,
          Pi.single_apply] at e
        rw [e]
        simp only [eq_comm]
      · intro k _ hk
        rw [map_smul, ht, if_neg hk, smul_zero, TrivSqZeroExt.snd_zero]
      · intro h; exact absurd (Finset.mem_univ j) h
    rw [hc, ← β.sum_comp, Finset.sum_eq_single i]
    · rw [hcj, if_pos rfl, one_smul]
    · intro k _ hk
      rw [hcj, if_neg hk, zero_smul]
    · intro h; exact absurd (Finset.mem_univ i) h
  have h3 : ∀ m, (toFirst κ m).comp (ψ (m + 1)) = (ψ 1).comp (toFirst (Fin d) m) := fun m => by
    have hp : RingHom.ker (Chart.jetAug V κ 1) ^ (m + 1 + 1) = ⊥ :=
      le_bot_iff.1 ((Ideal.pow_le_pow_right (by omega)).trans (ker_jetAug_pow κ 1).le)
    have ha : ∀ κ' : Type, (Chart.jetAug V κ' 1).comp (toFirst κ' m) = Chart.jetAug V κ' (m + 1) := fun κ' =>
      jet_ext fun k => (jetAug_zR (R := V) 1 k).trans (jetAug_zR (R := V) (m + 1) k).symm
    refine (hx.2.2 _ (Chart.jetAug V κ 1) (m + 1) hp (z 1) (haug 1)).unique ⟨?_, ?_⟩ ⟨?_, ?_⟩
    · rw [← AlgHom.comp_assoc, ha, (hψ _).1]
    · rw [← Chart.spMap_comp, Category.assoc, ← (hψ _).2, toFirst_comp z htr]
    · rw [← AlgHom.comp_assoc, (hψ _).1, ha]
    · rw [← Chart.spMap_comp, Category.assoc, toFirst_comp x hx.1, ← (hψ _).2]
  have h4 : ∀ m i, ψ m (zR m i) - zR m (β i) ∈ RingHom.ker (Chart.jetAug V κ m) ^ 2 := by
    intro m i
    cases m with
    | zero =>
      have hb : RingHom.ker (Chart.jetAug V κ 0) = ⊥ := (pow_one _).symm.trans (ker_jetAug_pow κ 0)
      have : ψ 0 (zR 0 i) - zR 0 (β i) ∈ RingHom.ker (Chart.jetAug V κ 0) :=
        Ideal.sub_mem _ (hψ0 0 i) (zR_mem_ker 0 _)
      rw [hb, Ideal.mem_bot] at this
      rw [this]
      exact Ideal.zero_mem _
    | succ m =>
      apply mem_sq_of_toFirst
      rw [map_sub, sub_eq_zero]
      exact (AlgHom.congr_fun (h3 m) (zR (m + 1) i)).trans (h2 i)
  let e := AlgEquiv.ofBijective (ψ m) (bij_of_first_order β (ψ m) (h4 m))
  have he : (e.symm : JetR V κ m →ₐ[V] JetR V (Fin d) m).comp (ψ m) = AlgHom.id V _ :=
    AlgHom.ext fun w => e.symm_apply_apply w
  have he' : (ψ m).comp (e.symm : JetR V κ m →ₐ[V] JetR V (Fin d) m) = AlgHom.id V _ :=
    AlgHom.ext fun w => e.apply_symm_apply w
  obtain ⟨φ, ⟨hφ1, hφ2⟩, hu⟩ := hx.2.2 A aug m hA y hy
  refine ⟨φ.comp e.symm, ⟨?_, ?_⟩, ?_⟩
  · rw [← AlgHom.comp_assoc, hφ1, ← (hψ m).1, AlgHom.comp_assoc, he', AlgHom.comp_id]
  · rw [(hψ m).2, ← Category.assoc, Chart.spMap_comp, AlgHom.comp_assoc, he, AlgHom.comp_id]
    exact hφ2
  · rintro φ' ⟨h5, h6⟩
    rw [(hψ m).2, ← Category.assoc, Chart.spMap_comp] at h6
    have := hu (φ'.comp (ψ m)) ⟨by rw [← AlgHom.comp_assoc, h5, (hψ m).1], h6⟩
    rw [← this, AlgHom.comp_assoc, he', AlgHom.comp_id]

end Geo

section Conv
variable {V : Type} [CommRing V] {G : Over (Sp V)}

def idAt (A : Type) [CommRing A] [Algebra V A] : Chart.sp (R₀ := V) A ⟶ overAt (𝟙 (Sp V)) A :=
  Over.homMk (𝟙 _) (by simp)

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Simplify using `only [Over.comp_left, idAt, Over.homMk_left, Category.id_comp]`. Both sides reduce to the same expression.
-/
theorem idAt_homAt {A B : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] (f : A →ₐ[V] B)
    (y : overAt (𝟙 (Sp V)) A ⟶ G) :
    idAt B ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) f ≫ y = Chart.spMap f ≫ idAt A ≫ y := by
  apply Over.OverMorphism.ext
  simp only [Over.comp_left, idAt, Over.homMk_left, Category.id_comp]
  rfl

/- English proof (translation)
Apply `Over.OverMorphism.ext` to reduce the goal to its premises. Use `congrArg CommaMorphism.left h` as an intermediate fact. Simplify `this` using `only [Over.comp_left, idAt, Over.homMk_left, Category.id_comp]`.
-/
theorem idAt_inj {A : Type} [CommRing A] [Algebra V A] {y y' : overAt (𝟙 (Sp V)) A ⟶ G}
    (h : idAt A ≫ y = idAt A ≫ y') : y = y' := by
  apply Over.OverMorphism.ext
  have := congrArg CommaMorphism.left h
  simpa only [Over.comp_left, idAt, Over.homMk_left, Category.id_comp] using this

/- English proof (translation)
Use `⟨htr, haug, fun A _ _ aug m hA y hy => ?_⟩` and prove the remaining obligations. Take `⟨ψ, ⟨h1, h2⟩, hu⟩` from `univ_of_dirs (oneCol d) hx (fun m => idAt (Jet V (Fin 1 × Fin d) m) ≫ z m) (fun m => (idAt_homAt (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) (z (m + 1))).symm.trans (congrArg (idAt _ ≫ ·) (htr m))) (fun m => (idAt_homAt (jetAug : Jet V (Fin 1 × Fin d) …`. Rewrite using `[MvPolynomial.aeval_X]`. Simplify using `only [Prod.mk.injEq, true_and])`. Use the proof step `(fun j => (idAt_homAt (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) (z 1)).symm.trans (hdir j))`.

Use `A aug m hA (idAt A ≫ y) (by rw [← idAt_homAt, hy, Chart.comp_one'])`. Use `⟨ψ, ⟨h1, idAt_inj (h2.trans (idAt_homAt (A := Jet V (Fin 1 × Fin d) m) ψ (z m)).symm)⟩, ?_⟩` and prove the remaining obligations. Introduce and unpack `ψ' ⟨h3, h4⟩`. Conclude with `hu ψ' ⟨h3, (congrArg (idAt A ≫ ·) h4).trans (idAt_homAt ψ' (z m))⟩`.
-/
theorem isUnivJ_of_dirs [GrpObj G] {d : ℕ}
    {x : ∀ m, Chart.sp (R₀ := V) (Chart.JetR V (Fin d) m) ⟶ G} (hx : Chart.IsUnivChart G d x)
    (z : JetPts G (Fin 1 × Fin d))
    (htr : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m) ≫ z (m + 1) = z m)
    (haug : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) ≫ z m = 1)
    (hdir : ∀ j, idAt _ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V))
      (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ z 1 =
        Chart.spMap (Chart.dualLift (Pi.single j 1)) ≫ x 1) :
    IsUnivJ G (Fin 1 × Fin d) z := by
  refine ⟨htr, haug, fun A _ _ aug m hA y hy => ?_⟩
  obtain ⟨ψ, ⟨h1, h2⟩, hu⟩ := univ_of_dirs (oneCol d) hx (fun m => idAt (Jet V (Fin 1 × Fin d) m) ≫ z m)
    (fun m => (idAt_homAt (jetTrunc : Jet V (Fin 1 × Fin d) (m + 1) →ₐ[V] Jet V (Fin 1 × Fin d) m)
      (z (m + 1))).symm.trans (congrArg (idAt _ ≫ ·) (htr m)))
    (fun m => (idAt_homAt (jetAug : Jet V (Fin 1 × Fin d) m →ₐ[V] V) (z m)).symm.trans
      (by rw [haug, Chart.comp_one']))
    (fun j => (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V))
    (fun j k => by
      show (MvPolynomial.aeval fun i => if i = ((0 : Fin 1), j) then (DualNumber.eps : DualNumber V) else 0)
        (MvPolynomial.X ((0 : Fin 1), k) : MvPolynomial (Fin 1 × Fin d) V) = _
      rw [MvPolynomial.aeval_X]
      simp only [Prod.mk.injEq, true_and])
    (fun j => (idAt_homAt (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V)
      (z 1)).symm.trans (hdir j))
    A aug m hA (idAt A ≫ y) (by rw [← idAt_homAt, hy, Chart.comp_one'])
  refine ⟨ψ, ⟨h1, idAt_inj (h2.trans (idAt_homAt (A := Jet V (Fin 1 × Fin d) m) ψ (z m)).symm)⟩, ?_⟩
  rintro ψ' ⟨h3, h4⟩
  exact hu ψ' ⟨h3, (congrArg (idAt A ≫ ·) h4).trans (idAt_homAt ψ' (z m))⟩

end Conv

section Main
variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E} {V : Type} [CommRing V] [IsLocalRing V]

open ReciprocityTheory.ChartRestriction.G.Chart (tcoord tan_ext prodPts prodPts_tan) in
open Formalism.L2.Pj.SaturatedCharts in

/- English proof (translation)
Establish `hsm : Smooth t.G.hom` using `t.semi.smooth`. Take `⟨n, x, hx⟩` from `Chart.univChartLoc (R := V) t.G`. Set `D' : Fin d → (Chart.sp (R₀` to `V) (DualNumber V) ⟶ t.G) := fun j => idAt _ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1`. Set `D : Fin d → (Sp (DualNumber V) ⟶ t.G.left)` to `fun j => (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1).left`. Establish `hDo : ∀ j, D j ≫ t.G.hom = spMap (algebraMap V (DualNumber V))` using `fun j => (Over.w (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1)).trans (Category.comp_id _)`.

Establish `hDD : ∀ j, toT t (D j) (hDo j) = D' j` using `fun j => Over.OverMorphism.ext (Category.id_comp _).symm`. Establish `hD't : ∀ j, Chart.IsTan (D' j)` using `fun j => by`. Establish `e1` using `idAt_homAt (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) (xT 1)`. Establish `e2` using `idAt_homAt (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) (xT 1)`. Establish `e3 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ xT 1 = 1` using `hc.zero 1`.

Rewrite `e2` using `[e3, Chart.comp_one', ← fst_comp_jetTan ((0 : Fin 1), j), ← Chart.spMap_comp, Category.assoc, ← e1]`. Conclude with `e2.symm`. Establish `hDt : ∀ j, Chart.IsTan (toT t (D j) (hDo j))` using `fun j => (hDD j).symm ▸ hD't j`. Set `Mv : Fin d → (Fin n → V)` to `fun j => tcoord hx _ (hDt j)`. Set `L : (Fin d → V) →ₗ[V] (Fin n → V)` to `{ toFun := fun a => ∑ j, a j • Mv j map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib] map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }`.

Establish `hL : ∀ a, L a = ∑ j, a j • Mv j` using `fun _ => rfl`. Establish `hLs : ∀ k, L (Pi.single k 1) = Mv k` using `fun k => by`. Rewrite using `[hL]`. Simplify using `[Pi.single_apply]`. Establish `htgo : ∀ k, tg k ≫ t.G.hom = spMap (algebraMap V (DualNumber V))` using `fun k => ((hb1 k).1).trans (Category.comp_id _)`.

Establish `htgt : ∀ k, Chart.IsTan (toT t (tg k) (htgo k))` using `fun k => chartTan_of t (tg k) (hb1 k)`. Establish `htgc : ∀ k, tcoord hx _ (htgt k) = Mv k`. Introduce `k`. Establish `e` using `prodPts_of_combAt t D hDo _ _ (htgo k) (hc.tan k)`. Take `⟨h, hh⟩` from `prodPts_tan hx (Pi.single k (1 : V)) _ hDt`.

Conclude with `((Chart.tcoord_congr hx e _ h).trans hh).trans (hLs k)`. Set `tg' : Fin d → (Chart.sp (R₀` to `V) (DualNumber V) ⟶ t.G) := fun k => toT t (tg k) (htgo k)`. Establish `hpt : ∀ a, ∃ h : Chart.IsTan (prodPts a tg'), tcoord hx _ h = L a` using `fun a => by`. Take `⟨ha, ea⟩` from `prodPts_tan hx a tg' htgt`. Use `⟨ha, ea.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[hL]`. Conclude with `Finset.sum_congr rfl fun k _ => by rw [← htgc k]`. Establish `hLinj : Function.Injective L`. Introduce `a b hab`. Take `⟨ha, ea⟩` from `hpt a`.

Take `⟨hb, eb⟩` from `hpt b`. Establish `heq : prodPts a tg' = prodPts b tg'` using `tan_ext hx ha hb (by rw [ea, eb, hab])`. Establish `hwo : (prodPts a tg').left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))` using `Over.w _`. Establish `hw : toT t (prodPts a tg').left hwo = prodPts a tg'` using `Over.OverMorphism.ext rfl`. Take `⟨a0, _, huniq⟩` from `hb2 _ (tanAt_of t _ hwo (by rw [hw]; exact ha))`.

Conclude with `(huniq a (combAt_of_prodPts t tg htgo a _ hwo hw)).trans (huniq b (combAt_of_prodPts t tg htgo b _ hwo (hw.trans heq))).symm`. Establish `hLsurj : Function.Surjective L`. Introduce `v`. Set `w` to `Chart.tvec (x := x) v`. Establish `hwt : Chart.IsTan w` using `Chart.isTan_tvec hx _`.

Establish `hwo : w.left ≫ t.G.hom = spMap (algebraMap V (DualNumber V))` using `Over.w _`. Establish `hw : toT t w.left hwo = w` using `Over.OverMorphism.ext rfl`. Take `⟨a, ha, -⟩` from `hb2 _ (tanAt_of t _ hwo (by rw [hw]; exact hwt))`. Establish `e : w = prodPts a tg'` using `hw.symm.trans (prodPts_of_combAt t tg htgo a _ hwo ha)`. Take `⟨h, eh⟩` from `hpt a`.

Conclude with `⟨a, eh.symm.trans ((Chart.tcoord_congr hx e hwt h).symm.trans (Chart.tcoord_tvec hx v))⟩`. Set `T` to `LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩`. Use `isUnivJ_of_dirs (Chart.isUnivChart_sub hx T) xT hc.trunc hc.zero fun j => ?_` and prove the remaining obligations. Rewrite using `[← Category.assoc (Chart.spMap _), Chart.spMap_comp, Chart.dualLift_comp_jetSub]`. Establish `e : T.toLinearMap (Pi.single j 1) = Mv j` using `hLs j`.

Rewrite using `[e]`. Conclude with `(hDD j).symm.trans (Chart.tcoord_spec hx _ (hDt j))`.
-/
theorem isUnivJ_of_isChartG (t : SAB H (Sp V)) (d : ℕ) (FT : Fin d → MvPowerSeries (Fin 2 × Fin d) V)
    (act : 𝓞 E → Fin d → MvPowerSeries (Fin 1 × Fin d) V) (tg : Fin d → (Sp (DualNumber V) ⟶ t.G.left))
    (xT : ∀ m, jOG (𝟙 (Sp V)) d m 1 ⟶ t.G)
    (hb1 : ∀ j, IsTanAtG t (𝟙 (Sp V)) (tg j))
    (hb2 : ∀ w, IsTanAtG t (𝟙 (Sp V)) w → ∃! a : Fin d → V, IsCombAtG t (𝟙 (Sp V)) tg a w)
    (hc : IsChartG t (𝟙 (Sp V)) d FT act tg (fun j : Fin d => Pi.single j (1 : V)) xT) :
    IsUnivJ t.G (Fin 1 × Fin d) xT := by
  have hsm : Smooth t.G.hom := t.semi.smooth
  obtain ⟨n, x, hx⟩ := Chart.univChartLoc (R := V) t.G
  let D' : Fin d → (Chart.sp (R₀ := V) (DualNumber V) ⟶ t.G) := fun j => idAt _ ≫ Formalism.L2.Pj.homAt (𝟙 (Sp V))
    (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1
  let D : Fin d → (Sp (DualNumber V) ⟶ t.G.left) := fun j => (Formalism.L2.Pj.homAt (𝟙 (Sp V))
    (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1).left
  have hDo : ∀ j, D j ≫ t.G.hom = spMap (algebraMap V (DualNumber V)) := fun j =>
    (Over.w (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetTan ((0 : Fin 1), j) :
      Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) ≫ xT 1)).trans (Category.comp_id _)
  have hDD : ∀ j, toT t (D j) (hDo j) = D' j := fun j => Over.OverMorphism.ext (Category.id_comp _).symm
  have hD't : ∀ j, Chart.IsTan (D' j) := fun j => by
    have e1 := idAt_homAt (jetTan ((0 : Fin 1), j) : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] DualNumber V) (xT 1)
    have e2 := idAt_homAt (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) (xT 1)
    have e3 : Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V (Fin 1 × Fin d) (0 + 1) →ₐ[V] V) ≫ xT 1 = 1 := hc.zero 1
    rw [e3, Chart.comp_one', ← fst_comp_jetTan ((0 : Fin 1), j), ← Chart.spMap_comp, Category.assoc, ← e1] at e2
    exact e2.symm
  have hDt : ∀ j, Chart.IsTan (toT t (D j) (hDo j)) := fun j => (hDD j).symm ▸ hD't j
  let Mv : Fin d → (Fin n → V) := fun j => tcoord hx _ (hDt j)
  let L : (Fin d → V) →ₗ[V] (Fin n → V) :=
    { toFun := fun a => ∑ j, a j • Mv j
      map_add' := fun a b => by simp only [Pi.add_apply, add_smul, Finset.sum_add_distrib]
      map_smul' := fun r a => by simp only [Pi.smul_apply, smul_eq_mul, mul_smul, Finset.smul_sum, RingHom.id_apply] }
  have hL : ∀ a, L a = ∑ j, a j • Mv j := fun _ => rfl
  have hLs : ∀ k, L (Pi.single k 1) = Mv k := fun k => by
    rw [hL]
    simp [Pi.single_apply]
  have htgo : ∀ k, tg k ≫ t.G.hom = spMap (algebraMap V (DualNumber V)) := fun k =>
    ((hb1 k).1).trans (Category.comp_id _)
  have htgt : ∀ k, Chart.IsTan (toT t (tg k) (htgo k)) := fun k => chartTan_of t (tg k) (hb1 k)
  have htgc : ∀ k, tcoord hx _ (htgt k) = Mv k := by
    intro k
    have e := prodPts_of_combAt t D hDo _ _ (htgo k) (hc.tan k)
    obtain ⟨h, hh⟩ := prodPts_tan hx (Pi.single k (1 : V)) _ hDt
    exact ((Chart.tcoord_congr hx e _ h).trans hh).trans (hLs k)
  let tg' : Fin d → (Chart.sp (R₀ := V) (DualNumber V) ⟶ t.G) := fun k => toT t (tg k) (htgo k)
  have hpt : ∀ a, ∃ h : Chart.IsTan (prodPts a tg'), tcoord hx _ h = L a := fun a => by
    obtain ⟨ha, ea⟩ := prodPts_tan hx a tg' htgt
    refine ⟨ha, ea.trans ?_⟩
    rw [hL]
    exact Finset.sum_congr rfl fun k _ => by rw [← htgc k]
  have hLinj : Function.Injective L := by
    intro a b hab
    obtain ⟨ha, ea⟩ := hpt a
    obtain ⟨hb, eb⟩ := hpt b
    have heq : prodPts a tg' = prodPts b tg' := tan_ext hx ha hb (by rw [ea, eb, hab])
    have hwo : (prodPts a tg').left ≫ t.G.hom = spMap (algebraMap V (DualNumber V)) := Over.w _
    have hw : toT t (prodPts a tg').left hwo = prodPts a tg' := Over.OverMorphism.ext rfl
    obtain ⟨a0, _, huniq⟩ := hb2 _ (tanAt_of t _ hwo (by rw [hw]; exact ha))
    exact (huniq a (combAt_of_prodPts t tg htgo a _ hwo hw)).trans
      (huniq b (combAt_of_prodPts t tg htgo b _ hwo (hw.trans heq))).symm
  have hLsurj : Function.Surjective L := by
    intro v
    let w := Chart.tvec (x := x) v
    have hwt : Chart.IsTan w := Chart.isTan_tvec hx _
    have hwo : w.left ≫ t.G.hom = spMap (algebraMap V (DualNumber V)) := Over.w _
    have hw : toT t w.left hwo = w := Over.OverMorphism.ext rfl
    obtain ⟨a, ha, -⟩ := hb2 _ (tanAt_of t _ hwo (by rw [hw]; exact hwt))
    have e : w = prodPts a tg' := hw.symm.trans (prodPts_of_combAt t tg htgo a _ hwo ha)
    obtain ⟨h, eh⟩ := hpt a
    exact ⟨a, eh.symm.trans ((Chart.tcoord_congr hx e hwt h).symm.trans (Chart.tcoord_tvec hx v))⟩
  let T := LinearEquiv.ofBijective L ⟨hLinj, hLsurj⟩
  refine isUnivJ_of_dirs (Chart.isUnivChart_sub hx T) xT hc.trunc hc.zero fun j => ?_
  rw [← Category.assoc (Chart.spMap _), Chart.spMap_comp, Chart.dualLift_comp_jetSub]
  have e : T.toLinearMap (Pi.single j 1) = Mv j := hLs j
  rw [e]
  exact (hDD j).symm.trans (Chart.tcoord_spec hx _ (hDt j))

end Main

end GlobalTheory.PowGerm.UnivJets

/- English proof (translation)
Introduce `_ _ _ _ H _ _ _ _ _ _ _ C` and use `letI := H.starRing GlobalTheory.PowGerm.UnivJets.isUnivJ_of_isChartG C.I.G _ C.FT C.actT C.tgT C.xT C.tgBasis.1 C.tgBasis.2 C.chartT`.
-/
theorem GlobalTheory.PowGerm.univSt_holds : GlobalTheory.PowGerm.UnivSt := fun _ _ _ _ H _ _ _ _ _ _ _ C =>
  letI := H.starRing
  GlobalTheory.PowGerm.UnivJets.isUnivJ_of_isChartG C.I.G _ C.FT C.actT C.tgT C.xT C.tgBasis.1 C.tgBasis.2 C.chartT
