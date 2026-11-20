import Mathlib
import Development.AbelianVarietyTheory.Definitions.ModuliSpaces.IsGaloisCover
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.HeckeKer
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.IsHolPeriods
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.EigLatBasis
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.UnifUniqSt
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjPull
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ObjRigidClosed
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsSabCancel
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.FormallyUnramifiedOfTangentMapInjective
import Development.AbelianVarietyTheory.Proofs.UnitaryExistence.ExistsMulEquivOfIsGrpPullback
import Development.AbelianVarietyTheory.Proofs.CubicalLineBundles.ProdSurjectiveGeometricPoints
import Development.AbelianVarietyTheory.Proofs.UnramifiedDepth.ExistsLiftOfNil
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.ExistsCompletionPointClosedPointMemOfSmooth

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open scoped CategoryTheory.Obj TensorProduct
open GlobalTheory.ZM

noncomputable section

namespace GlobalTheory.LevelQuotUnram

open GlobalTheory.TangentCrit (dualPt dualBase dualPt_dualBase dualPt_dualBase_assoc)

/- English proof (translation)
Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Establish `key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom`. Introduce `a`. Use extensionality with `d`. Prove the components needed by the constructor for the conclusion.

Introduce `hd`. Assume the negation of the conclusion as `h`. Conclude with `a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))`. Introduce `hd`. Establish `h : d.fst = 0` using `hd`.

Use `a.isPrime.mem_of_pow_mem 2 ?_` and prove the remaining obligations. Apply the tactic sequence `have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]`. Rewrite using `[this]`. Conclude with `a.asIdeal.zero_mem`. Conclude with `PrimeSpectrum.ext ((key a).trans (key b).symm)`.
-/
lemma subsingleton_sp_dual (k : Type) [Field k] : Subsingleton (Sp (DualNumber k)) := by
  refine ⟨fun a b => ?_⟩
  have key : ∀ a : PrimeSpectrum (DualNumber k), a.asIdeal = RingHom.ker (TrivSqZeroExt.fstHom k k k).toRingHom := by
    intro a
    ext d
    constructor
    · intro hd
      by_contra h
      exact a.isPrime.ne_top (Ideal.eq_top_of_isUnit_mem _ hd
        (TrivSqZeroExt.isUnit_iff_isUnit_fst.mpr (IsUnit.mk0 _ h)))
    · intro hd
      have h : d.fst = 0 := hd
      refine a.isPrime.mem_of_pow_mem 2 ?_
      have : d ^ 2 = 0 := by ext1 <;> simp [pow_two, h]
      rw [this]; exact a.asIdeal.zero_mem
  exact PrimeSpectrum.ext ((key a).trans (key b).symm)

/- English proof (translation)
Use `subsingleton_sp_dual k` as an intermediate fact. Use `TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f)) (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h` and prove the remaining obligations. Establish `h₁ : f d.fst = 0` using `by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd`. Establish `h₂ : f d.snd = 0` using `by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd`. Conclude with `TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))`.
-/
lemma dualMap_cancel {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}}
    {g g' : Sp (DualNumber k) ⟶ X} (h : spMap (Chart.dualMapR f) ≫ g = spMap (Chart.dualMapR f) ≫ g') : g = g' := by
  have := subsingleton_sp_dual k
  refine TangentCrit.hom_ext_of_ker_inf (CommRingCat.ofHom (Chart.dualMapR f)) (CommRingCat.ofHom (Chart.dualMapR f))
    (fun z => ⟨IsLocalRing.closedPoint (DualNumber K), Subsingleton.elim _ _⟩) (fun d hd _ => ?_) h h
  have h₁ : f d.fst = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.fst hd
  have h₂ : f d.snd = 0 := by simpa [Chart.dualMapR] using congrArg TrivSqZeroExt.snd hd
  exact TrivSqZeroExt.ext (f.injective (by simpa using h₁)) (f.injective (by simpa using h₂))

/- English proof (translation)
Simplify using `only [constPt, ← Category.assoc]`. Use `congr 1`. Simplify using `only [← Spec.map_comp]`. Use `congr 1`. Apply the tactic sequence `ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]`.
-/
lemma constPt_dualMap {k K : Type} [Field k] [Field K] (f : k →+* K) {X : Scheme.{0}} (x : Sp (DualNumber k) ⟶ X) :
    constPt (spMap (Chart.dualMapR f) ≫ x) = spMap (Chart.dualMapR f) ≫ constPt x := by
  simp only [constPt, ← Category.assoc]
  congr 1
  simp only [← Spec.map_comp]
  congr 1
  ext a <;> simp [Chart.dualMapR, TrivSqZeroExt.algebraMap_eq_inl]

/- English proof (translation)
Use `subsingleton_sp_dual k` as an intermediate fact. Take `⟨_, ⟨U, hU, rfl⟩, hxU, -⟩` from `Y.isBasis_affineOpens.exists_subset_of_mem_open (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ`. Establish `hx : Set.range x ⊆ U`. Introduce and unpack `_ ⟨z, rfl⟩`. Rewrite using `[Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]` and apply the resulting hypothesis.

Use `exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨z, rfl⟩`. Express the relevant statement in the definitionally equal form `π (y z) ∈ U`. Rewrite using `[← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]`. Conclude with `hx ⟨_, rfl⟩`.

Introduce `R A _ _ _ _ _ _ ρ hρ φ`. Use `SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ` and prove the remaining obligations. Establish `h : TrivSqZeroExt.fst d = 0` using `(hρ d).symm.trans hd`. Apply the tactic sequence `exact ⟨2, by ext1 <;> simp [pow_two, h]⟩`.
-/
lemma exists_dual_lift {X Y : Scheme.{0}} (π : X ⟶ Y) [Smooth π] [IsAffineHom π] {k : Type} [Field k]
    (x : Sp (DualNumber k) ⟶ Y) (y : Sp k ⟶ X) (h : y ≫ π = dualPt k ≫ x) :
    ∃ x₂ : Sp (DualNumber k) ⟶ X, dualPt k ≫ x₂ = y ∧ x₂ ≫ π = x := by
  have := subsingleton_sp_dual k
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, -⟩ := Y.isBasis_affineOpens.exists_subset_of_mem_open
    (Set.mem_univ (x (IsLocalRing.closedPoint (DualNumber k)))) isOpen_univ
  have hx : Set.range x ⊆ U := by
    rintro _ ⟨z, rfl⟩
    rwa [Subsingleton.elim z (IsLocalRing.closedPoint (DualNumber k))]
  refine exists_lift_of_smooth_of_isAffineOpen π hU (hU.preimage π) le_rfl _ x y h hx ?_ ?_
  · rintro _ ⟨z, rfl⟩
    change π (y z) ∈ U
    rw [← Scheme.Hom.comp_apply, h, Scheme.Hom.comp_apply]
    exact hx ⟨_, rfl⟩
  · intro R A _ _ _ _ _ _ ρ hρ φ
    refine SmoothNilLift.exists_lift_of_nil ρ (fun c => ⟨TrivSqZeroExt.inl c, hρ _⟩) (fun d hd => ?_) φ
    have h : TrivSqZeroExt.fst d = 0 := (hρ d).symm.trans hd
    exact ⟨2, by ext1 <;> simp [pow_two, h]⟩

variable {E : Type} [Field E] [NumberField E] [IsCMField E] {H : Host E}

/- English proof (translation)
Substitute `h` using the available equality. Conclude with `⟨m, rfl⟩`.
-/
lemma sab_cast {S S' : Scheme.{0}} {t : SAB H S} {t' : SAB H S'} {f g : S' ⟶ S} (m : SABMap t' t f) (h : f = g) :
    ∃ n : SABMap t' t g, n.φ = m.φ := by
  subst h; exact ⟨m, rfl⟩

/- English proof (translation)
Take `⟨e, he⟩` from `exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm`. Establish `h₁ : (e σ).left = σ.left ≫ ν.φ` using `he σ`. Establish `h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left` using `by simp`. Rewrite using `[← h₁, ← h₂]`. Use `congr 1`.

Use `GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n) (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)`. Rewrite using `[h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]`. Rewrite using `[GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]`. Conclude with `(congrArg e hσ).trans (map_one e)`.
-/
lemma torsion_rigid {X : Scheme.{0}} {k : Type} [Field k] (t : SAB H (Sp (DualNumber k))) (t₂ : SAB H X)
    (y : Sp k ⟶ X) (ν : SABMap t t₂ (dualBase k ≫ y)) {n : ℕ} (hn : IsUnit (n : Γ(X, ⊤)))
    (σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ t.G) (τ : 𝟙_ (Over X) ⟶ t₂.G) (hσ : σ ^ n = 1) (hτ : τ ^ n = 1)
    (h : dualPt k ≫ σ.left ≫ ν.φ = y ≫ τ.left) : σ.left ≫ ν.φ = (dualBase k ≫ y) ≫ τ.left := by
  obtain ⟨e, he⟩ := exists_mulEquiv_of_isGrpPullback ν.cart (𝟙 _) (dualBase k ≫ y) (Category.id_comp _).symm
  have h₁ : (e σ).left = σ.left ≫ ν.φ := he σ
  have h₂ : (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ).left = (dualBase k ≫ y) ≫ τ.left := by simp
  rw [← h₁, ← h₂]
  congr 1
  refine GrpTangent.eq_of_tangentMap_injective y (mulN t₂.G n)
    (GrpTangent.tangentMap_pullback_mulN_bijective t₂.G hn y).1 _ _ (Over.OverMorphism.ext ?_) ?_
  · change dualPt k ≫ Over.Hom.left (e σ) = dualPt k ≫ Over.Hom.left (toUnit (Over.mk (dualBase k ≫ y)) ≫ τ)
    rw [h₁, h₂, h, Category.assoc, dualPt_dualBase_assoc]
  · rw [GrpTangent.comp_mulN, GrpTangent.comp_mulN, ← comp_pow, hτ, comp_one, ← map_pow]
    exact (congrArg e hσ).trans (map_one e)

variable {D : Datum H}

section
variable {l : Level H} {B : Type} [CommRing B] {b : Base l B} {S : Scheme.{0}} {s : S ⟶ Sp B} (o : Obj D l b s)

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero`. Use `hf 0 0` as an intermediate fact. Rewrite `this` using `[add_zero]`. Rewrite using `[pow_zero, zero_smul]`.

Conclude with `(mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm`. Consider the case `succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]`.
-/
lemma pow_eq_of_add {L Γ : Type} [AddCommGroup L] [Group Γ] (f : L → Γ) (hf : ∀ a c, f (a + c) = f a * f c)
    (n : ℕ) (a : L) : f a ^ n = f (n • a) := by
  induction n with
  | zero =>
    have := hf 0 0
    rw [add_zero] at this
    rw [pow_zero, zero_smul]
    exact (mul_left_cancel (a := f 0) (by rw [← this, _root_.mul_one])).symm
  | succ n ih => rw [pow_succ, ih, add_smul, one_smul, hf]

/- English proof (translation)
Establish `h` using `Ideal.mem_span_singleton_self (l.M : 𝓞 E)`. Rewrite `h` using `[← l.prod]`. Conclude with `Ideal.mul_le_left h`.
-/
lemma natCast_mem_Mb (l : Level H) : (l.M : 𝓞 E) ∈ l.Mb := by
  have h := Ideal.mem_span_singleton_self (l.M : 𝓞 E)
  rw [← l.prod] at h
  exact Ideal.mul_le_left h

/- English proof (translation)
Rewrite using `[← Nat.cast_smul_eq_nsmul (𝓞 E)]`. Conclude with `Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top`.
-/
lemma nsmul_mem_Mb (l : Level H) (a : D.La) : l.M • a ∈ l.Mb • (⊤ : Submodule (𝓞 E) D.La) := by
  rw [← Nat.cast_smul_eq_nsmul (𝓞 E)]
  exact Submodule.smul_mem_smul (natCast_mem_Mb l) Submodule.mem_top

/- English proof (translation)
Rewrite using `[pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]`.
-/
lemma eta_pow (a : D.La) : o.eta a ^ l.M = 1 := by
  rw [pow_eq_of_add o.eta o.eta_add, o.eta_ker _ (nsmul_mem_Mb l a)]

/- English proof (translation)
Rewrite using `[pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]`.
-/
lemma etaA_pow (a : D.La) : o.etaA a ^ l.A = 1 := by
  rw [pow_eq_of_add o.etaA o.etaA_add, o.etaA_ker]

include b s in
/- English proof (translation)
Simplify using `using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom`.
-/
lemma isUnit_nat {n : ℕ} (hn : 0 < n) : IsUnit (n : Γ(S, ⊤)) := by
  simpa using (b.unit n hn).map ((Scheme.ΓSpecIso (.of B)).inv ≫ s.appTop).hom

end

/- English proof (translation)
Use `Q.fin` as an intermediate fact. Use `Q.etale` as an intermediate fact. Use `Q.onto` as an intermediate fact. Take `⟨y, hy⟩` from `GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)`. Take `⟨x₂, hx₂, hx⟩` from `exists_dual_lift Q.π x y hy.symm`.

Establish `hc : constPt x₂ = dualBase k ≫ y` using `by rw [← hx₂]; rfl`. Establish `hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x` using `by rw [Category.assoc, ← hy]; rfl`. Take `⟨o₀, ⟨r⟩⟩` from `obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s) (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob`. Establish `hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ`. Take `⟨n₁, hn₁⟩` from `ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap`.

Take `⟨n₂, hn₂⟩` from `ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap`. Establish `e : dualPt k ≫ constPt x = dualPt k ≫ x` using `dualPt_dualBase_assoc k _`. Take `⟨n₃, hn₃⟩` from `sab_cast n₂ e`. Rewrite using `[← hn₁, ← hn₂, ← hn₃]`. Use `obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃ fun a => ⟨_, rfl, ?_⟩` and prove the remaining obligations.

Rewrite using `[hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]`. Establish `hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k → z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ`. Introduce `Z z w hz`. Rewrite using `[← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]`. Conclude with `congrArg _ hr`.

Take `⟨o₁, ⟨n₁⟩⟩` from `obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ`. Take `⟨a₁, ha₁⟩` from `ObjMaps.exists_sab_comp Q.m n₁.toSABMap`. Take `⟨a₂, ha₂⟩` from `sab_cast a₁ (hx.trans (Category.id_comp x).symm)`. Take `⟨u, hu⟩` from `ObjMaps.exists_sab_cancel m₁.toSABMap a₂`. Take `⟨a₃, ha₃⟩` from `ObjMaps.exists_sab_comp m₂.toSABMap u`.

Take `⟨a₄, ha₄⟩` from `sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)`. Take `⟨n₂, hn₂⟩` from `ObjMaps.exists_sab_cancel Q.m a₄`. Establish `e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ` using `by rw [← ha₁, ← ha₂, hu]`. Establish `e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ` using `by rw [← hn₂, ha₄, ha₃]`. Establish `key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G, dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ`.

Introduce `σ`. Establish `hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _` using `Over.w σ`. Use `Q.m.cart.1.hom_ext ?_ ?_` and prove the remaining obligations. Use `hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by` as an intermediate fact. Establish `w` using `u.cart.1.w`.

Simplify using `only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢`. Rewrite using `[w, hσ]`. Conclude with `Category.comp_id _)`. Simplify using `only [Category.assoc] at this ⊢`. Rewrite using `[e₁, e₂, this]`.

Establish `w₁` using `n₁.cart.1.w`. Establish `w₂` using `n₂.cart.1.w`. Simplify using `only [Category.assoc]`. Rewrite using `[w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]`. Take `⟨n₃, hn₃⟩` from `sab_cast n₂ hc.symm`.

Establish `h₂ : x₂ = constPt x₂`. Use `Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ≫ n₃.φ = _`. Rewrite using `[hn₃, hc]`. Use `torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega)) _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_` and prove the remaining obligations.

Rewrite using `[key, n₁.eta, reassoc_of% hx₂]`. Express the relevant statement in the definitionally equal form `_ ≫ n₃.φ = _`. Rewrite using `[hn₃, hc]`. Use `torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos) _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_` and prove the remaining obligations. Rewrite using `[key, n₁.etaA, reassoc_of% hx₂]`.

Rewrite using `[← hcπ, ← hc, ← h₂, hx]`.
-/
theorem unram_of_isAlgClosed (hL : Out.Laws) {l l₂ : Level H} (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂)
    (k : Type) [Field k] [IsAlgClosed k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s))
    (m₁ : ObjMap ob Q.univ x) (m₂ : ObjMap ob Q.univ (constPt x)) : x = constPt x := by
  have := Q.fin
  have := Q.etale
  have := Q.onto
  obtain ⟨y, hy⟩ := GeomSurj.exists_lift_of_surjective Q.π (dualPt k ≫ x)
  obtain ⟨x₂, hx₂, hx⟩ := exists_dual_lift Q.π x y hy.symm
  have hc : constPt x₂ = dualBase k ≫ y := by rw [← hx₂]; rfl
  have hcπ : (dualBase k ≫ y) ≫ Q.π = constPt x := by rw [Category.assoc, ← hy]; rfl

  obtain ⟨o₀, ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    (dualPt k ≫ x ≫ Q.s) (dualPt k) rfl rfl (by simp [spMap]) ob
  have hr : r.toSABMap.φ ≫ m₁.toSABMap.φ = r.toSABMap.φ ≫ m₂.toSABMap.φ := by
    obtain ⟨n₁, hn₁⟩ := ObjMaps.exists_sab_comp m₁.toSABMap r.toSABMap
    obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_comp m₂.toSABMap r.toSABMap
    have e : dualPt k ≫ constPt x = dualPt k ≫ x := dualPt_dualBase_assoc k _
    obtain ⟨n₃, hn₃⟩ := sab_cast n₂ e
    rw [← hn₁, ← hn₂, ← hn₃]
    refine obj_rigid_closed hL E H D l _ _ _ _ _ _ _ _ Q.univ o₀ _ (Or.inl inferInstance) n₁ n₃
      fun a => ⟨_, rfl, ?_⟩
    rw [hn₃, hn₂, hn₁, reassoc_of% (r.eta a), reassoc_of% (r.eta a), m₁.eta, m₂.eta, reassoc_of% e]
  have hr' : ∀ {Z : Scheme.{0}} (z : Z ⟶ ob.t.G.left) (w : Z ⟶ Sp k), z ≫ ob.t.G.hom = w ≫ dualPt k →
      z ≫ m₁.toSABMap.φ = z ≫ m₂.toSABMap.φ := by
    intro Z z w hz
    rw [← r.cart.1.lift_fst z w hz, Category.assoc, Category.assoc]
    exact congrArg _ hr

  obtain ⟨o₁, ⟨n₁⟩⟩ := obj_pull E H D l₂ _ _ (baseKA l₂) (baseKA l₂) (RingHom.id _) _ _ Xo₂.s
    (x₂ ≫ Xo₂.s) x₂ rfl rfl (by simp [spMap]) Xo₂.univ
  obtain ⟨a₁, ha₁⟩ := ObjMaps.exists_sab_comp Q.m n₁.toSABMap
  obtain ⟨a₂, ha₂⟩ := sab_cast a₁ (hx.trans (Category.id_comp x).symm)
  obtain ⟨u, hu⟩ := ObjMaps.exists_sab_cancel m₁.toSABMap a₂
  obtain ⟨a₃, ha₃⟩ := ObjMaps.exists_sab_comp m₂.toSABMap u
  obtain ⟨a₄, ha₄⟩ := sab_cast a₃ ((Category.id_comp _).trans hcπ.symm)
  obtain ⟨n₂, hn₂⟩ := ObjMaps.exists_sab_cancel Q.m a₄
  have e₁ : n₁.toSABMap.φ ≫ Q.m.φ = u.φ ≫ m₁.toSABMap.φ := by rw [← ha₁, ← ha₂, hu]
  have e₂ : n₂.φ ≫ Q.m.φ = u.φ ≫ m₂.toSABMap.φ := by rw [← hn₂, ha₄, ha₃]
  have key : ∀ σ : 𝟙_ (Over (Sp (DualNumber k))) ⟶ o₁.t.G,
      dualPt k ≫ σ.left ≫ n₂.φ = dualPt k ≫ σ.left ≫ n₁.toSABMap.φ := by
    intro σ
    have hσ : σ.left ≫ o₁.t.G.hom = 𝟙 _ := Over.w σ
    refine Q.m.cart.1.hom_ext ?_ ?_
    · have := hr' (dualPt k ≫ σ.left ≫ u.φ) (𝟙 _) (by
        have w := u.cart.1.w
        simp only [Category.assoc, Category.id_comp, Category.comp_id] at w ⊢
        rw [w, hσ]
        exact Category.comp_id _)
      simp only [Category.assoc] at this ⊢
      rw [e₁, e₂, this]
    · have w₁ := n₁.cart.1.w
      have w₂ := n₂.cart.1.w
      simp only [Category.assoc]
      rw [w₁, w₂, reassoc_of% hσ, reassoc_of% hσ, dualPt_dualBase_assoc, hx₂]
  obtain ⟨n₃, hn₃⟩ := sab_cast n₂ hc.symm
  have h₂ : x₂ = constPt x₂ := by
    refine Xo₂.unram k x₂ o₁ ⟨n₁⟩ ⟨{ toSABMap := n₃, eta := fun a => ?_, etaA := fun a => ?_ }⟩
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) (by have := l₂.three_le; omega))
        _ _ (eta_pow o₁ a) (eta_pow Xo₂.univ a) ?_
      rw [key, n₁.eta, reassoc_of% hx₂]
    · change _ ≫ n₃.φ = _
      rw [hn₃, hc]
      refine torsion_rigid _ _ y n₂ (isUnit_nat (b := baseKA l₂) (s := Xo₂.s) l₂.A_pos)
        _ _ (etaA_pow o₁ a) (etaA_pow Xo₂.univ a) ?_
      rw [key, n₁.etaA, reassoc_of% hx₂]
  rw [← hcπ, ← hc, ← h₂, hx]

end GlobalTheory.LevelQuotUnram

namespace GlobalTheory

/- English proof (translation)
Introduce and unpack `hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩`. Set `f : k →+* AlgebraicClosure k` to `algebraMap _ _`. Use `LevelQuotUnram.dualMap_cancel f ?_` and prove the remaining obligations. Rewrite using `[← LevelQuotUnram.constPt_dualMap]`. Take `⟨o', ⟨r⟩⟩` from `obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s) ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob`.

Take `⟨n₁, -⟩` from `ObjComp.objMap_comp m₁ r`. Take `⟨n₂, -⟩` from `ObjComp.objMap_comp m₂ r`. Conclude with `LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)`.
-/
theorem levelQuot_unram : Out.Laws → Out.Laws2 → ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (D : Datum H) (l l₂ : Level H) (Xo₂ : Moduli D l₂) (Q : LevelQuot l Xo₂), 1 ≤ D.p + D.q → l.Dvd l₂ → ∀ (k : Type) [Field k] (x : Sp (DualNumber k) ⟶ Q.X) (ob : Obj D l (baseKA l) (x ≫ Q.s)), Nonempty (ObjMap ob Q.univ x) → Nonempty (ObjMap ob Q.univ (constPt x)) → x = constPt x := by
  rintro hL - E _ _ _ H D l l₂ Xo₂ Q - - k _ x ob ⟨m₁⟩ ⟨m₂⟩
  let f : k →+* AlgebraicClosure k := algebraMap _ _
  refine LevelQuotUnram.dualMap_cancel f ?_
  rw [← LevelQuotUnram.constPt_dualMap]
  obtain ⟨o', ⟨r⟩⟩ := obj_pull E H D l _ _ (baseKA l) (baseKA l) (RingHom.id _) _ _ (x ≫ Q.s)
    ((spMap (Chart.dualMapR f) ≫ x) ≫ Q.s) (spMap (Chart.dualMapR f)) rfl rfl (by simp [spMap]) ob
  obtain ⟨n₁, -⟩ := ObjComp.objMap_comp m₁ r
  obtain ⟨n₂, -⟩ := ObjComp.objMap_comp m₂ r
  exact LevelQuotUnram.unram_of_isAlgClosed hL Xo₂ Q _ _ o' n₁ (LevelQuotUnram.constPt_dualMap f x ▸ n₂)

end GlobalTheory
