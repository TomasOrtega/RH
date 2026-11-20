import Mathlib
import Development.AbelianVarietyTheory.Definitions.PlaceAdaptation.AdaptStd
import Development.AbelianVarietyTheory.Proofs.RingsOfIntegers.MvPowerSeriesSubstConstTermsLocalAlgHomSpec
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.UniversalStatement
import Development.AbelianVarietyTheory.Proofs.JetHarmonics.ExistsUniversalJetCoordinatesPullback
import Development.AbelianVarietyTheory.Proofs.HomogeneousIdeals.ExistsUniqueFactorCompletedStalkOfMap
import Formalism.SharpRestriction.Divisibility.GeneratorPowers.ChartDataPf

set_option autoImplicit false
noncomputable section
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor Formalism.L2.Pj Formalism.MainNotions.ModuliIntegralCharts.H1
open ReciprocityTheory.ChartRestriction.G.Geo.Tor.Germ GlobalTheory.PtTie
open ReciprocityTheory.ChartRestriction.G.TB (dAct dLin)
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.PlaceInt

namespace GlobalTheory.PlaceFormPt

section Grp
variable {S S' Z : Scheme.{0}} {G : Over S} [GrpObj G] {G' : Over S'} [GrpObj G']

/- English proof (translation)
Use `show (toUnit T ≫ η[G]).left = _`. Rewrite using `[Over.comp_left, Over.toUnit_left]`.
-/
theorem one_left (T : Over S) : (1 : T ⟶ G).left = T.hom ≫ η[G].left := by
  show (toUnit T ≫ η[G]).left = _
  rw [Over.comp_left, Over.toUnit_left]

/- English proof (translation)
Establish `hb : u' ≫ T'.hom = u ≫ T.hom`. Rewrite using `[← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]`. Set `U : Over.mk (u ≫ T.hom) ⟶ T` to `Over.homMk u rfl`. Set `U' : Over.mk (u ≫ T.hom) ⟶ T'` to `Over.homMk u' hb`. Establish `e1 : U ≫ x = U' ≫ x'` using `Over.OverMorphism.ext hx`.

Establish `e2 : U ≫ y = U' ≫ y'` using `Over.OverMorphism.ext hy`. Establish `: U ≫ (x * y) = U' ≫ (x' * y')` using `by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]`. Conclude with `congrArg (fun k => k.left) this`.
-/
theorem comp_mul_left {T T' : Over S} (x y : T ⟶ G) (x' y' : T' ⟶ G) (u : Z ⟶ T.left) (u' : Z ⟶ T'.left)
    (hx : u ≫ x.left = u' ≫ x'.left) (hy : u ≫ y.left = u' ≫ y'.left) :
    u ≫ (x * y).left = u' ≫ (x' * y').left := by
  have hb : u' ≫ T'.hom = u ≫ T.hom := by
    rw [← Over.w x, ← Over.w x', ← Category.assoc, ← hx, Category.assoc]
  let U : Over.mk (u ≫ T.hom) ⟶ T := Over.homMk u rfl
  let U' : Over.mk (u ≫ T.hom) ⟶ T' := Over.homMk u' hb
  have e1 : U ≫ x = U' ≫ x' := Over.OverMorphism.ext hx
  have e2 : U ≫ y = U' ≫ y' := Over.OverMorphism.ext hy
  have : U ≫ (x * y) = U' ≫ (x' * y') := by rw [MonObj.comp_mul, MonObj.comp_mul, e1, e2]
  exact congrArg (fun k => k.left) this

variable {f : S' ⟶ S} {φ : G'.left ⟶ G.left}

/- English proof (translation)
Rewrite using `[← h.2 T' r r' (pushPt h.1.w r) (pushPt h.1.w r') rfl rfl]`. Conclude with `(Category.id_comp _).symm.trans (comp_mul_left (Z := T'.left) (pushPt h.1.w r) (pushPt h.1.w r') x y (𝟙 T'.left) u ((Category.id_comp _).trans hx) ((Category.id_comp _).trans hy))`.
-/
theorem push_mul_left (h : IsGrpPullback G' G f φ) {T' : Over S'} {T : Over S} (r r' : T' ⟶ G') (x y : T ⟶ G)
    (u : T'.left ⟶ T.left) (hx : r.left ≫ φ = u ≫ x.left) (hy : r'.left ≫ φ = u ≫ y.left) :
    (r * r').left ≫ φ = u ≫ (x * y).left := by
  rw [← h.2 T' r r' (pushPt h.1.w r) (pushPt h.1.w r') rfl rfl]
  exact (Category.id_comp _).symm.trans (comp_mul_left (Z := T'.left) (pushPt h.1.w r) (pushPt h.1.w r') x y
    (𝟙 T'.left) u ((Category.id_comp _).trans hx)
    ((Category.id_comp _).trans hy))

/- English proof (translation)
The claim follows from `(congrArg (fun q => q.left) (map_one (pushHom h T'))).trans (one_left _)`.
-/
theorem push_one_left (h : IsGrpPullback G' G f φ) (T' : Over S') :
    (1 : T' ⟶ G').left ≫ φ = (T'.hom ≫ f) ≫ η[G].left :=
  (congrArg (fun q => q.left) (map_one (pushHom h T'))).trans (one_left _)

end Grp

section Jets
variable {V : Type} [CommRing V] [IsLocalRing V] {G : Over (Sp V)} [GrpObj G] {κ : Type}

/- English proof (translation)
Establish `hx` using `(GlobalTheory.UnivJetBaseChange.isUnivJ_iff z).1 hz`. Take `⟨C⟩` from `Chart.exists_chart G`. Take `⟨k, hk, hqk⟩` from `GlobalTheory.ChartBaseChange.exists_pt_of_aug C (Chart.jetAug V κ m) (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (Chart.ker_jetAug_pow _ m) _ (hx.2.1 m)`. Establish `hqk' : ∀ a, Chart.jetAug V κ m (k a) = Chart.eps C a` using `fun a => AlgHom.congr_fun hqk a`. Use `set I := RingHom.ker (Chart.eps C) with hI`.

Set `aug : (Γ(G.left, C.U) ⧸ I ^ (m + 1)) →ₐ[V] V` to `Ideal.Quotient.liftₐ _ (Chart.eps C) fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha`. Establish `hker : RingHom.ker aug ^ (m + 1) = ⊥`. Establish `hle : RingHom.ker aug ≤ I.map (Ideal.Quotient.mk (I ^ (m + 1)))`. Introduce `x hx`. Take `⟨p, rfl⟩` from `Ideal.Quotient.mk_surjective x`.

Conclude with `Ideal.mem_map_of_mem _ hx`. Rewrite using `[← le_bot_iff, ← Ideal.map_quotient_self (I ^ (m + 1)), Ideal.map_pow]`. Conclude with `Ideal.pow_right_mono hle _`. Take `⟨ψ₀, ⟨ha, hψ₀⟩, -⟩` from `hx.2.2 _ aug m hker (Chart.pt C (Ideal.Quotient.mkₐ V _)) (by`. Rewrite using `[Chart.spMap_pt]`.

Conclude with `GlobalTheory.ChartBaseChange.pt_eps_self C)`. Set `kb : (Γ(G.left, C.U) ⧸ I ^ (m + 1)) →ₐ[V] Chart.JetR V κ m` to `Ideal.Quotient.liftₐ _ k fun a ha => by`. Establish `h1 : I ≤ (RingHom.ker (Chart.jetAug V κ m)).comap k` using `fun b hb => (hqk' b).trans hb`. Establish `h2` using `Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h1 (m + 1) ha)`. Rewrite `h2` using `[Chart.ker_jetAug_pow]`.

Conclude with `h2`. Establish `hkb : (Chart.jetAug V κ m).comp kb = aug` using `Ideal.Quotient.algHom_ext _ (AlgHom.ext hqk')`. Establish `e : kb.comp ψ₀ = AlgHom.id V _`. Use `(hx.2.2 _ (Chart.jetAug V κ m) m (Chart.ker_jetAug_pow _ m) _ (hx.2.1 m)).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩` and prove the remaining obligations. Rewrite using `[← AlgHom.comp_assoc, hkb, ha]`.

Rewrite using `[← Chart.spMap_comp, Category.assoc, ← hψ₀, Chart.spMap_pt]`. Conclude with `hk`. Apply `Over.OverMorphism.ext show _ = Spec.map (𝟙 _) ≫ _` to reduce the goal to its premises. Rewrite using `[Spec.map_id, Category.id_comp]`. Establish `hl : (z m).left = Spec.map (CommRingCat.ofHom k.toRingHom) ≫ C.hU.fromSpec` using `congrArg (fun q => q.left) hk`.

Establish `h1 : Spec.map (CommRingCat.ofHom (ψ.comp k.toRingHom)) = Spec.map (CommRingCat.ofHom (ψ'.comp k.toRingHom))`. Establish `e1 : ∀ χ : Jet V κ m →+* A, spMap χ ≫ (z m).left = Spec.map (CommRingCat.ofHom (χ.comp k.toRingHom)) ≫ C.hU.fromSpec` using `fun χ => (congrArg (spMap χ ≫ ·) hl).trans ((Category.assoc _ _ _).symm.trans (congrArg (· ≫ C.hU.fromSpec) (Spec.map_comp _ _).symm))`. Rewrite using `[← cancel_mono C.hU.fromSpec, ← e1, ← e1, h]`. Establish `h2` using `congrArg CommRingCat.Hom.hom (Spec.map_injective h1)`. Use `RingHom.ext fun b => ?_` and prove the remaining obligations.

Take `⟨p, hp⟩` from `Ideal.Quotient.mk_surjective (ψ₀ b)`. Establish `: k p = b` using `(congrArg kb hp).trans (AlgHom.congr_fun e b)`. Rewrite using `[← this]`. Conclude with `RingHom.congr_fun h2 p`.
-/
theorem jet_mono {z : GlobalTheory.PowGerm.JetPts G κ} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (m : ℕ) {A : Type} [CommRing A]
    (ψ ψ' : Jet V κ m →+* A) (h : spMap ψ ≫ (z m).left = spMap ψ' ≫ (z m).left) : ψ = ψ' := by
  have hx := (GlobalTheory.UnivJetBaseChange.isUnivJ_iff z).1 hz
  obtain ⟨C⟩ := Chart.exists_chart G
  obtain ⟨k, hk, hqk⟩ := GlobalTheory.ChartBaseChange.exists_pt_of_aug C (Chart.jetAug V κ m)
    (fun r => ⟨algebraMap _ _ r, AlgHom.commutes _ r⟩) (Chart.ker_jetAug_pow _ m) _ (hx.2.1 m)
  have hqk' : ∀ a, Chart.jetAug V κ m (k a) = Chart.eps C a := fun a => AlgHom.congr_fun hqk a
  set I := RingHom.ker (Chart.eps C) with hI
  let aug : (Γ(G.left, C.U) ⧸ I ^ (m + 1)) →ₐ[V] V :=
    Ideal.Quotient.liftₐ _ (Chart.eps C) fun a ha => Ideal.pow_le_self (Nat.succ_ne_zero m) ha
  have hker : RingHom.ker aug ^ (m + 1) = ⊥ := by
    have hle : RingHom.ker aug ≤ I.map (Ideal.Quotient.mk (I ^ (m + 1))) := by
      intro x hx
      obtain ⟨p, rfl⟩ := Ideal.Quotient.mk_surjective x
      exact Ideal.mem_map_of_mem _ hx
    rw [← le_bot_iff, ← Ideal.map_quotient_self (I ^ (m + 1)), Ideal.map_pow]
    exact Ideal.pow_right_mono hle _
  obtain ⟨ψ₀, ⟨ha, hψ₀⟩, -⟩ := hx.2.2 _ aug m hker (Chart.pt C (Ideal.Quotient.mkₐ V _)) (by
    rw [Chart.spMap_pt]
    exact GlobalTheory.ChartBaseChange.pt_eps_self C)
  let kb : (Γ(G.left, C.U) ⧸ I ^ (m + 1)) →ₐ[V] Chart.JetR V κ m :=
    Ideal.Quotient.liftₐ _ k fun a ha => by
      have h1 : I ≤ (RingHom.ker (Chart.jetAug V κ m)).comap k := fun b hb => (hqk' b).trans hb
      have h2 := Ideal.le_comap_pow _ (m + 1) (Ideal.pow_right_mono h1 (m + 1) ha)
      rw [Chart.ker_jetAug_pow] at h2
      exact h2
  have hkb : (Chart.jetAug V κ m).comp kb = aug := Ideal.Quotient.algHom_ext _ (AlgHom.ext hqk')
  have e : kb.comp ψ₀ = AlgHom.id V _ := by
    refine (hx.2.2 _ (Chart.jetAug V κ m) m (Chart.ker_jetAug_pow _ m) _ (hx.2.1 m)).unique ⟨?_, ?_⟩ ⟨rfl, ?_⟩
    · rw [← AlgHom.comp_assoc, hkb, ha]
    · rw [← Chart.spMap_comp, Category.assoc, ← hψ₀, Chart.spMap_pt]
      exact hk
    · apply Over.OverMorphism.ext
      show _ = Spec.map (𝟙 _) ≫ _
      rw [Spec.map_id, Category.id_comp]
  have hl : (z m).left = Spec.map (CommRingCat.ofHom k.toRingHom) ≫ C.hU.fromSpec := congrArg (fun q => q.left) hk
  have h1 : Spec.map (CommRingCat.ofHom (ψ.comp k.toRingHom)) = Spec.map (CommRingCat.ofHom (ψ'.comp k.toRingHom)) := by
    have e1 : ∀ χ : Jet V κ m →+* A, spMap χ ≫ (z m).left =
        Spec.map (CommRingCat.ofHom (χ.comp k.toRingHom)) ≫ C.hU.fromSpec := fun χ =>
      (congrArg (spMap χ ≫ ·) hl).trans ((Category.assoc _ _ _).symm.trans
        (congrArg (· ≫ C.hU.fromSpec) (Spec.map_comp _ _).symm))
    rw [← cancel_mono C.hU.fromSpec, ← e1, ← e1, h]
  have h2 := congrArg CommRingCat.Hom.hom (Spec.map_injective h1)
  refine RingHom.ext fun b => ?_
  obtain ⟨p, hp⟩ := Ideal.Quotient.mk_surjective (ψ₀ b)
  have : k p = b := (congrArg kb hp).trans (AlgHom.congr_fun e b)
  rw [← this]
  exact RingHom.congr_fun h2 p

def Coord (z : GlobalTheory.PowGerm.JetPts G κ) (a : Sp V ⟶ G.left) (α : κ → V) : Prop :=
  ∀ m : ℕ, ∃ ψ : Jet V κ m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1),
    (∀ p, ψ (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p)) ∧
    spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ a =
      spMap (ψ : Jet V κ m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (z m).left

def evJ (α : κ → V) (hα : ∀ i, α i ∈ maximalIdeal V) (m : ℕ) : Jet V κ m →ₐ[V] V ⧸ maximalIdeal V ^ (m + 1) :=
  Chart.jetLift V ((maximalIdeal V).map (Ideal.Quotient.mk _)) (by rw [← Ideal.map_pow, Ideal.map_quotient_self])
    (fun i => Ideal.Quotient.mk _ (α i)) fun i => Ideal.mem_map_of_mem _ (hα i)

/- English proof (translation)
The claim follows from `Chart.jetLift_zR _ _ _ _ p`.
-/
theorem evJ_X (α : κ → V) (hα : ∀ i, α i ∈ maximalIdeal V) (m : ℕ) (p : κ) :
    evJ α hα m (Ideal.Quotient.mk _ (MvPolynomial.X p)) = Ideal.Quotient.mk _ (α p) :=
  Chart.jetLift_zR _ _ _ _ p

/- English proof (translation)
Establish `: (evJ α hα m).comp (Ideal.Quotient.mkₐ V _) = (Ideal.Quotient.mkₐ V _).comp (MvPolynomial.aeval α)` using `MvPolynomial.algHom_ext fun p => (evJ_X α hα m p).trans (by rw [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl)`. Conclude with `AlgHom.congr_fun this q`.
-/
theorem evJ_mk (α : κ → V) (hα : ∀ i, α i ∈ maximalIdeal V) (m : ℕ) (q : MvPolynomial κ V) :
    evJ α hα m (Ideal.Quotient.mk _ q) = Ideal.Quotient.mk _ (MvPolynomial.aeval α q) := by
  have : (evJ α hα m).comp (Ideal.Quotient.mkₐ V _) = (Ideal.Quotient.mkₐ V _).comp (MvPolynomial.aeval α) :=
    MvPolynomial.algHom_ext fun p => (evJ_X α hα m p).trans (by rw [AlgHom.comp_apply, MvPolynomial.aeval_X]; rfl)
  exact AlgHom.congr_fun this q

omit [GrpObj G] in
/- English proof (translation)
Use `forall_congr' fun m => ⟨?_, fun h => ⟨_, evJ_X α hα m, h⟩⟩` and prove the remaining obligations. Introduce and unpack `⟨ψ, h1, h2⟩`. Establish `: ψ = evJ α hα m` using `Chart.jet_ext fun p => (h1 p).trans (evJ_X α hα m p).symm`. Rewrite using `[← this]`. Conclude with `h2`.
-/
theorem coord_iff {z : GlobalTheory.PowGerm.JetPts G κ} {a : Sp V ⟶ G.left} {α : κ → V} (hα : ∀ i, α i ∈ maximalIdeal V) :
    Coord z a α ↔ ∀ m, spMap (Ideal.Quotient.mk (maximalIdeal V ^ (m + 1))) ≫ a =
      spMap (evJ α hα m : Jet V κ m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (z m).left := by
  refine forall_congr' fun m => ⟨?_, fun h => ⟨_, evJ_X α hα m, h⟩⟩
  rintro ⟨ψ, h1, h2⟩
  have : ψ = evJ α hα m := Chart.jet_ext fun p => (h1 p).trans (evJ_X α hα m p).symm
  rw [← this]
  exact h2

omit [IsLocalRing V] in
/- English proof (translation)
Rewrite using `[← Category.assoc]`. Conclude with `congrArg (· ≫ k) (Spec.map_comp _ _).symm`.
-/
theorem spMap_homAt {A B D : Type} [CommRing A] [Algebra V A] [CommRing B] [Algebra V B] [CommRing D] [Algebra V D]
    (f : A →ₐ[V] B) (g : B →ₐ[V] D) {X : Scheme.{0}} (k : Sp A ⟶ X) :
    spMap (g : B →+* D) ≫ (Formalism.L2.Pj.homAt (𝟙 (Sp V)) f).left ≫ k = spMap (g.comp f : A →+* D) ≫ k := by
  rw [← Category.assoc]
  exact congrArg (· ≫ k) (Spec.map_comp _ _).symm

/- English proof (translation)
Introduce `m`. Use `⟨(Algebra.ofId V _).comp jetAug, fun p => ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[AlgHom.comp_apply, show jetAug (Ideal.Quotient.mk _ (MvPolynomial.X p) : Jet V κ m) = (0 : V) from Chart.jetAug_zR m p, map_zero, Pi.zero_apply, map_zero]`. Rewrite using `[← spMap_homAt]`. Establish `: (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V κ m →ₐ[V] V)).left ≫ (z m).left = (Spec.map (𝟙 (CommRingCat.of V)) ≫ 𝟙 _) ≫ η[G].left` using `(congrArg (fun q => q.left) (hz.2.1 m)).trans (one_left _)`.

Rewrite using `[this, Spec.map_id, Category.id_comp]`. Conclude with `congrArg (_ ≫ ·) (Category.id_comp _).symm`.
-/
theorem coord_one {z : GlobalTheory.PowGerm.JetPts G κ} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) : Coord z η[G].left 0 := by
  intro m
  refine ⟨(Algebra.ofId V _).comp jetAug, fun p => ?_, ?_⟩
  · rw [AlgHom.comp_apply, show jetAug (Ideal.Quotient.mk _ (MvPolynomial.X p) : Jet V κ m) = (0 : V) from
      Chart.jetAug_zR m p, map_zero, Pi.zero_apply, map_zero]
  · rw [← spMap_homAt]
    have : (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetAug : Jet V κ m →ₐ[V] V)).left ≫ (z m).left =
        (Spec.map (𝟙 (CommRingCat.of V)) ≫ 𝟙 _) ≫ η[G].left :=
      (congrArg (fun q => q.left) (hz.2.1 m)).trans (one_left _)
    rw [this, Spec.map_id, Category.id_comp]
    exact congrArg (_ ≫ ·) (Category.id_comp _).symm

variable [IsAdicComplete (maximalIdeal V) V]

omit [GrpObj G] in
/- English proof (translation)
The claim follows from `GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ((coord_iff hα).1 h m).trans ((coord_iff hα).1 h' m).symm`.
-/
theorem coord_ext {z : GlobalTheory.PowGerm.JetPts G κ} {a a' : Sp V ⟶ G.left} {α : κ → V} (hα : ∀ i, α i ∈ maximalIdeal V)
    (h : Coord z a α) (h' : Coord z a' α) : a = a' :=
  GlobalTheory.hom_ext_of_isHausdorff (maximalIdeal V) fun m => ((coord_iff hα).1 h m).trans ((coord_iff hα).1 h' m).symm

/- English proof (translation)
Use function extensionality and compare the values at `p`. Use `GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal V) fun n => ?_` and prove the remaining obligations. Take `⟨ψ, h1, h2⟩` from `h n`. Take `⟨ψ', h1', h2'⟩` from `h' n`. Use `RingHom.congr_fun (jet_mono hz n _ _ (h2.symm.trans h2')) (Ideal.Quotient.mk _ (MvPolynomial.X p))` as an intermediate fact.

Conclude with `Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 ((h1 p).symm.trans (this.trans (h1' p))))`.
-/
theorem coord_unique {z : GlobalTheory.PowGerm.JetPts G κ} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) {a : Sp V ⟶ G.left} {α α' : κ → V}
    (h : Coord z a α) (h' : Coord z a α') : α = α' := by
  funext p
  refine GlobalTheory.eq_of_forall_sub_mem_ideal_pow (maximalIdeal V) fun n => ?_
  obtain ⟨ψ, h1, h2⟩ := h n
  obtain ⟨ψ', h1', h2'⟩ := h' n
  have := RingHom.congr_fun (jet_mono hz n _ _ (h2.symm.trans h2')) (Ideal.Quotient.mk _ (MvPolynomial.X p))
  exact Ideal.pow_le_pow_right (Nat.le_succ n) (Ideal.Quotient.eq.1 ((h1 p).symm.trans (this.trans (h1' p))))

/- English proof (translation)
Take `⟨g, ⟨h1, h2⟩, -⟩` from `GlobalTheory.existsUnique_over_of_isAdicFamily (I := maximalIdeal V) (𝟙 (Sp V)) G.hom (f := fun m => spMap (evJ α hα m : Jet V κ m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (z m).left) (fun m => by`. Establish `e : (evJ α hα m).comp jetTrunc = (Ideal.Quotient.factorₐ V (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))).comp (evJ α hα (m + 1))` using `Chart.jet_ext fun p => (evJ_X α hα m p).trans (congrArg (Ideal.Quotient.factorₐ V (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))) (evJ_X α hα (m + 1) p)).symm`. Use `show _ = _ ≫ (z m).left`. Rewrite using `[← hz.1 m, Over.comp_left, spMap_homAt, e, ← Category.assoc]`. Conclude with `congrArg (· ≫ (z (m + 1)).left) (Spec.map_comp _ _).symm) (fun m => by`.

Rewrite using `[Category.assoc, Over.w (z m)]`. Use `show _ ≫ spMap _ ≫ 𝟙 _ = _`. Rewrite using `[← Category.assoc, spMap_comp_alg])`. Conclude with `⟨g, h1, (coord_iff hα).2 h2⟩`.
-/
theorem exists_coord {z : GlobalTheory.PowGerm.JetPts G κ} (hz : GlobalTheory.PowGerm.IsUnivJ G κ z) (α : κ → V)
    (hα : ∀ i, α i ∈ maximalIdeal V) : ∃ a : Sp V ⟶ G.left, a ≫ G.hom = 𝟙 _ ∧ Coord z a α := by
  obtain ⟨g, ⟨h1, h2⟩, -⟩ := GlobalTheory.existsUnique_over_of_isAdicFamily (I := maximalIdeal V) (𝟙 (Sp V)) G.hom
    (f := fun m => spMap (evJ α hα m : Jet V κ m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ (z m).left) (fun m => by
      have e : (evJ α hα m).comp jetTrunc =
          (Ideal.Quotient.factorₐ V (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))).comp (evJ α hα (m + 1)) :=
        Chart.jet_ext fun p => (evJ_X α hα m p).trans (congrArg
          (Ideal.Quotient.factorₐ V (Ideal.pow_le_pow_right (Nat.le_succ (m + 1)))) (evJ_X α hα (m + 1) p)).symm
      show _ = _ ≫ (z m).left
      rw [← hz.1 m, Over.comp_left, spMap_homAt, e, ← Category.assoc]
      exact congrArg (· ≫ (z (m + 1)).left) (Spec.map_comp _ _).symm) (fun m => by
      rw [Category.assoc, Over.w (z m)]
      show _ ≫ spMap _ ≫ 𝟙 _ = _
      rw [← Category.assoc, spMap_comp_alg])
  exact ⟨g, h1, (coord_iff hα).2 h2⟩

omit [GrpObj G] in
/- English proof (translation)
Establish `hI` using `GlobalTheory.ne_top_of_isHausdorff (maximalIdeal V)`. Establish `e0 : evJ α hα 0 = evJ α' hα' 0` using `Chart.jet_ext fun p => (evJ_X α hα 0 p).trans ((Ideal.Quotient.eq.2 (by rw [zero_add, pow_one]; exact sub_mem (hα p) (hα' p))).trans (evJ_X α' hα' 0 p).symm)`. Establish `h0 : GlobalTheory.adicLevelι (maximalIdeal V) (0 + 1) ≫ a' = GlobalTheory.adicLevelι (maximalIdeal V) (0 + 1) ≫ a` using `((coord_iff hα').1 h' 0).trans (by rw [← e0]; exact ((coord_iff hα).1 h 0).symm)`. Establish `hx : a' (closedPoint V) = a (closedPoint V)`. Rewrite using `[← GlobalTheory.adicLevelι_closedPoint hI 0]`.

Use `(Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))` and prove the remaining obligations. Rewrite using `[h0]`. Take `⟨φ, hφ, -⟩` from `GlobalTheory.existsUnique_factor_stalk a rfl`. Take `⟨φ', hφ', -⟩` from `GlobalTheory.existsUnique_factor_stalk a' hx`. Establish `: φ = φ'` using `by ext1`.

Use `RingHom.ext fun b => hi ?_` and prove the remaining obligations. Establish `h1 : spMap i ≫ Spec.map φ = spMap i ≫ Spec.map φ'`. Rewrite using `[← cancel_mono (G.left.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', e]`. Rewrite `h1` using `[← Spec.map_comp, ← Spec.map_comp]`. Conclude with `congr($(Spec.map_injective h1).hom b)`.

Rewrite using `[← hφ', ← this, hφ]`.
-/
theorem coord_ext_of_injective {z : GlobalTheory.PowGerm.JetPts G κ} {a a' : Sp V ⟶ G.left} {α α' : κ → V}
    (hα : ∀ i, α i ∈ maximalIdeal V) (hα' : ∀ i, α' i ∈ maximalIdeal V) (h : Coord z a α) (h' : Coord z a' α')
    {K : Type} [CommRing K] (i : V →+* K) (hi : Function.Injective i) (e : spMap i ≫ a = spMap i ≫ a') : a = a' := by
  have hI := GlobalTheory.ne_top_of_isHausdorff (maximalIdeal V)
  have e0 : evJ α hα 0 = evJ α' hα' 0 := Chart.jet_ext fun p => (evJ_X α hα 0 p).trans
    ((Ideal.Quotient.eq.2 (by rw [zero_add, pow_one]; exact sub_mem (hα p) (hα' p))).trans (evJ_X α' hα' 0 p).symm)
  have h0 : GlobalTheory.adicLevelι (maximalIdeal V) (0 + 1) ≫ a' = GlobalTheory.adicLevelι (maximalIdeal V) (0 + 1) ≫ a :=
    ((coord_iff hα').1 h' 0).trans (by rw [← e0]; exact ((coord_iff hα).1 h 0).symm)
  have hx : a' (closedPoint V) = a (closedPoint V) := by
    rw [← GlobalTheory.adicLevelι_closedPoint hI 0]
    refine (Scheme.Hom.comp_apply _ _ _).symm.trans (Eq.trans ?_ (Scheme.Hom.comp_apply _ _ _))
    rw [h0]
  obtain ⟨φ, hφ, -⟩ := GlobalTheory.existsUnique_factor_stalk a rfl
  obtain ⟨φ', hφ', -⟩ := GlobalTheory.existsUnique_factor_stalk a' hx
  have : φ = φ' := by
    ext1
    refine RingHom.ext fun b => hi ?_
    have h1 : spMap i ≫ Spec.map φ = spMap i ≫ Spec.map φ' := by
      rw [← cancel_mono (G.left.fromSpecStalk _), Category.assoc, Category.assoc, hφ, hφ', e]
    rw [← Spec.map_comp, ← Spec.map_comp] at h1
    exact congr($(Spec.map_injective h1).hom b)
  rw [← hφ', ← this, hφ]

omit [IsAdicComplete (maximalIdeal V) V]

/- English proof (translation)
Use `Chart.jet_ext fun s => Eq.trans ?_ (evJ_X δ hδ m s).symm` and prove the remaining obligations. Establish `h1 : jetSubstP m (fun s => psTrunc m (P s)) (Chart.zR m s) = Chart.pj m (P s)` using `(jetMap_zR m _ _ s).trans (mk_psTrunc m _ (hP s)).symm`. Use `(congrArg (evJ _ hχ m) h1).trans ((evJ_mk _ hχ m _).trans ?_)` and prove the remaining obligations. Rewrite using `[e]`. Conclude with `(Ideal.Quotient.eq.2 (GlobalTheory.algHom_sub_aeval_truncTotal_mem χ hχ (m + 1) (P s))).symm`.
-/
theorem evJ_comp_subst {κ' : Type} [Fintype κ'] [DecidableEq κ'] (χ : MvPowerSeries κ' V →ₐ[V] V)
    (hχ : ∀ i, χ (MvPowerSeries.X i) ∈ maximalIdeal V) (P : κ → MvPowerSeries κ' V)
    (hP : ∀ s, MvPowerSeries.constantCoeff (P s) = 0) (δ : κ → V) (hδ : ∀ i, δ i ∈ maximalIdeal V)
    (e : ∀ s, δ s = χ (P s)) (m : ℕ) :
    (evJ _ hχ m).comp (jetSubstP m fun s => psTrunc m (P s)) = evJ δ hδ m := by
  refine Chart.jet_ext fun s => Eq.trans ?_ (evJ_X δ hδ m s).symm
  have h1 : jetSubstP m (fun s => psTrunc m (P s)) (Chart.zR m s) = Chart.pj m (P s) :=
    (jetMap_zR m _ _ s).trans (mk_psTrunc m _ (hP s)).symm
  refine (congrArg (evJ _ hχ m) h1).trans ((evJ_mk _ hχ m _).trans ?_)
  rw [e]
  exact (Ideal.Quotient.eq.2 (GlobalTheory.algHom_sub_aeval_truncTotal_mem χ hχ (m + 1) (P s))).symm

end Jets

section Ops
variable {V : Type} [CommRing V] [IsLocalRing V] {G : Over (Sp V)} [GrpObj G] {d : ℕ}

/- English proof (translation)
Establish `hα : ∀ p : Fin 1 × Fin d, α p.2 ∈ maximalIdeal V` using `fun p => h0 p.2 ▸ hχ _`. Establish `hα' : ∀ p : Fin 1 × Fin d, α' p.2 ∈ maximalIdeal V` using `fun p => h1 p.2 ▸ hχ _`. Use `(coord_iff fun p : Fin 1 × Fin d => hδ p.2).2 fun m => ?_` and prove the remaining obligations. Establish `k1` using `evJ_comp_subst χ hχ (fun p : Fin 1 × Fin d => F p.2) (fun p => hF p.2) (fun p => δ p.2) (fun p => hδ p.2) (fun p => e p.2) m`. Establish `k2` using `spMap_homAt (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) (evJ _ hχ m) (z m).left`.

Rewrite `k2` using `[k1]`. Establish `k3` using `congrArg (fun q : overAt (𝟙 (Sp V)) (Jet V (Fin 2 × Fin d) m) ⟶ G => spMap (evJ _ hχ m : Jet V (Fin 2 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ q.left) (law m)`. Use `Eq.trans ?_ (k3.symm.trans k2)` and prove the remaining obligations. Establish `cp : ∀ (i : Fin 2) (β : Fin d → V) (hβ : ∀ p : Fin 1 × Fin d, β p.2 ∈ maximalIdeal V), (∀ j, β j = χ (MvPowerSeries.X (i, j))) → (evJ _ hχ m).comp (jetCopy d m i) = evJ (fun p => β p.2) hβ m` using `fun i β hβ hb => Chart.jet_ext fun p => (congrArg (evJ _ hχ m) (jetMap_zR m _ (fun _ => X_mem_orig _) p)).trans ((evJ_X _ hχ m _).trans ((congrArg _ (hb p.2).symm).trans (evJ_X _ hβ m p).symm))`. Use `comp_mul_left s s' _ _ _ _ ?_ ?_` and prove the remaining obligations.

Establish `k4` using `spMap_homAt (jetCopy d m (0 : Fin 2)) (evJ _ hχ m) (z m).left`. Rewrite `k4` using `[cp 0 α hα h0]`. Conclude with `((coord_iff hα).1 h m).trans k4.symm`. Establish `k4` using `spMap_homAt (jetCopy d m (1 : Fin 2)) (evJ _ hχ m) (z m).left`. Rewrite `k4` using `[cp 1 α' hα' h1]`.

Conclude with `((coord_iff hα').1 h' m).trans k4.symm`.
-/
theorem coord_mul {z : GlobalTheory.PowGerm.JetPts G (Fin 1 × Fin d)} (F : Fin d → PS V 2 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (law : ∀ m, Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ z m =
      (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (0 : Fin 2)) ≫ z m) *
        (Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetCopy d m (1 : Fin 2)) ≫ z m))
    (χ : PS V 2 d →ₐ[V] V) (hχ : ∀ i, χ (MvPowerSeries.X i) ∈ maximalIdeal V) {α α' δ : Fin d → V}
    (h0 : ∀ j, α j = χ (MvPowerSeries.X (0, j))) (h1 : ∀ j, α' j = χ (MvPowerSeries.X (1, j)))
    (hδ : Small δ) (e : ∀ j, δ j = χ (F j)) (s s' : Over.mk (𝟙 (Sp V)) ⟶ G)
    (h : Coord z s.left fun p => α p.2) (h' : Coord z s'.left fun p => α' p.2) :
    Coord z (s * s').left fun p => δ p.2 := by
  have hα : ∀ p : Fin 1 × Fin d, α p.2 ∈ maximalIdeal V := fun p => h0 p.2 ▸ hχ _
  have hα' : ∀ p : Fin 1 × Fin d, α' p.2 ∈ maximalIdeal V := fun p => h1 p.2 ▸ hχ _
  refine (coord_iff fun p : Fin 1 × Fin d => hδ p.2).2 fun m => ?_
  have k1 := evJ_comp_subst χ hχ (fun p : Fin 1 × Fin d => F p.2) (fun p => hF p.2) (fun p => δ p.2)
    (fun p => hδ p.2) (fun p => e p.2) m
  have k2 := spMap_homAt (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) (evJ _ hχ m) (z m).left
  rw [k1] at k2
  have k3 := congrArg (fun q : overAt (𝟙 (Sp V)) (Jet V (Fin 2 × Fin d) m) ⟶ G =>
    spMap (evJ _ hχ m : Jet V (Fin 2 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ q.left) (law m)
  refine Eq.trans ?_ (k3.symm.trans k2)
  have cp : ∀ (i : Fin 2) (β : Fin d → V) (hβ : ∀ p : Fin 1 × Fin d, β p.2 ∈ maximalIdeal V),
      (∀ j, β j = χ (MvPowerSeries.X (i, j))) → (evJ _ hχ m).comp (jetCopy d m i) = evJ (fun p => β p.2) hβ m :=
    fun i β hβ hb => Chart.jet_ext fun p => (congrArg (evJ _ hχ m) (jetMap_zR m _ (fun _ => X_mem_orig _) p)).trans
      ((evJ_X _ hχ m _).trans ((congrArg _ (hb p.2).symm).trans (evJ_X _ hβ m p).symm))
  refine comp_mul_left s s' _ _ _ _ ?_ ?_
  · have k4 := spMap_homAt (jetCopy d m (0 : Fin 2)) (evJ _ hχ m) (z m).left
    rw [cp 0 α hα h0] at k4
    exact ((coord_iff hα).1 h m).trans k4.symm
  · have k4 := spMap_homAt (jetCopy d m (1 : Fin 2)) (evJ _ hχ m) (z m).left
    rw [cp 1 α' hα' h1] at k4
    exact ((coord_iff hα').1 h' m).trans k4.symm

omit [GrpObj G] in
/- English proof (translation)
Rewrite `h` using `[show (fun p : Fin 1 × Fin d => α p.2) = fun p => χ (MvPowerSeries.X p) from funext h0]`. Use `(coord_iff fun p : Fin 1 × Fin d => hδ p.2).2 fun m => ?_` and prove the remaining obligations. Establish `k1` using `evJ_comp_subst χ hχ (fun p : Fin 1 × Fin d => F p.2) (fun p => hF p.2) (fun p => δ p.2) (fun p => hδ p.2) (fun p => e p.2) m`. Establish `k2` using `spMap_homAt (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) (evJ _ hχ m) (z m).left`. Rewrite `k2` using `[k1]`.

Establish `k3` using `congrArg (fun q : overAt (𝟙 (Sp V)) (Jet V (Fin 1 × Fin d) m) ⟶ G => spMap (evJ _ hχ m : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ q.left) (law m)`. Use `Eq.trans ?_ (k3.trans k2)` and prove the remaining obligations. Conclude with `(Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) ((coord_iff hχ).1 h m)).trans (Category.assoc _ _ _))`.
-/
theorem coord_comp {z : GlobalTheory.PowGerm.JetPts G (Fin 1 × Fin d)} (g : G ⟶ G) (F : Fin d → PS V 1 d)
    (hF : ∀ i, MvPowerSeries.constantCoeff (F i) = 0)
    (law : ∀ m, z m ≫ g =
      Formalism.L2.Pj.homAt (𝟙 (Sp V)) (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) ≫ z m)
    (χ : PS V 1 d →ₐ[V] V) (hχ : ∀ i, χ (MvPowerSeries.X i) ∈ maximalIdeal V) {α δ : Fin d → V}
    (h0 : ∀ p : Fin 1 × Fin d, α p.2 = χ (MvPowerSeries.X p))
    (hδ : Small δ) (e : ∀ j, δ j = χ (F j)) (a : Sp V ⟶ G.left) (h : Coord z a fun p => α p.2) :
    Coord z (a ≫ g.left) fun p => δ p.2 := by
  rw [show (fun p : Fin 1 × Fin d => α p.2) = fun p => χ (MvPowerSeries.X p) from funext h0] at h
  refine (coord_iff fun p : Fin 1 × Fin d => hδ p.2).2 fun m => ?_
  have k1 := evJ_comp_subst χ hχ (fun p : Fin 1 × Fin d => F p.2) (fun p => hF p.2) (fun p => δ p.2)
    (fun p => hδ p.2) (fun p => e p.2) m
  have k2 := spMap_homAt (jetSubstP m fun p : Fin 1 × Fin d => psTrunc m (F p.2)) (evJ _ hχ m) (z m).left
  rw [k1] at k2
  have k3 := congrArg (fun q : overAt (𝟙 (Sp V)) (Jet V (Fin 1 × Fin d) m) ⟶ G =>
    spMap (evJ _ hχ m : Jet V (Fin 1 × Fin d) m →+* V ⧸ maximalIdeal V ^ (m + 1)) ≫ q.left) (law m)
  refine Eq.trans ?_ (k3.trans k2)
  exact (Category.assoc _ _ _).symm.trans ((congrArg (· ≫ g.left) ((coord_iff hχ).1 h m)).trans (Category.assoc _ _ _))

end Ops

/- English proof (translation)
Establish `ha' : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff (a p.1 p.2) ∈ maximalIdeal V` using `fun p => ha _ _`. Take `⟨ψ, hψ⟩` from `exists_algHom_evC (fun p : Fin n × Fin d => a p.1 p.2) ha'`. Set `cc : PS V 0 d →ₐ[V] V` to `{ MvPowerSeries.constantCoeff (σ := Fin 0 × Fin d) (R := V) with commutes' := fun r => MvPowerSeries.constantCoeff_C r }`. Establish `e : ∀ f, (cc.comp ψ) f = MvPowerSeries.constantCoeff (evV a f)` using `fun f => congrArg MvPowerSeries.constantCoeff (evC_eq_algHom _ ha' ψ hψ f).symm`. Use `⟨cc.comp ψ, fun p => congrArg MvPowerSeries.constantCoeff (hψ p), e, fun f hf => ?_⟩` and prove the remaining obligations.

Rewrite using `[e]`. Conclude with `constantCoeff_evC_mem _ ha' f (hf ▸ zero_mem _)`.
-/
theorem exists_eval {V : Type} [CommRing V] [IsLocalRing V] [IsNoetherianRing V] [IsAdicComplete (maximalIdeal V) V]
    {d n : ℕ} (a : Fin n → Pt V 0 d) (ha : ∀ i j, MvPowerSeries.constantCoeff (a i j) ∈ maximalIdeal V) :
    ∃ χ : PS V n d →ₐ[V] V, (∀ p, χ (MvPowerSeries.X p) = MvPowerSeries.constantCoeff (a p.1 p.2)) ∧
      (∀ f, χ f = MvPowerSeries.constantCoeff (evV a f)) ∧
      ∀ f, MvPowerSeries.constantCoeff f = 0 → χ f ∈ maximalIdeal V := by
  have ha' : ∀ p : Fin n × Fin d, MvPowerSeries.constantCoeff (a p.1 p.2) ∈ maximalIdeal V := fun p => ha _ _
  obtain ⟨ψ, hψ⟩ := exists_algHom_evC (fun p : Fin n × Fin d => a p.1 p.2) ha'
  let cc : PS V 0 d →ₐ[V] V := { MvPowerSeries.constantCoeff (σ := Fin 0 × Fin d) (R := V) with
    commutes' := fun r => MvPowerSeries.constantCoeff_C r }
  have e : ∀ f, (cc.comp ψ) f = MvPowerSeries.constantCoeff (evV a f) := fun f =>
    congrArg MvPowerSeries.constantCoeff (evC_eq_algHom _ ha' ψ hψ f).symm
  refine ⟨cc.comp ψ, fun p => congrArg MvPowerSeries.constantCoeff (hψ p), e, fun f hf => ?_⟩
  rw [e]
  exact constantCoeff_evC_mem _ ha' f (hf ▸ zero_mem _)

/- English proof (translation)
Introduce `E _ _ _ H Dw l Xo c _ _ T io y C B hB`. Establish `hz : GlobalTheory.PowGerm.IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT` using `GlobalTheory.PowGerm.UnivJets.isUnivJ_of_isChartG C.I.G _ C.FT C.actT C.tgT C.xT C.tgBasis.1 C.tgBasis.2 C.chartT`. Establish `c1` using `C.I.m1.cart`. Establish `c2` using `C.I.m2.cart`. Establish `ext1 : ∀ {r r' : Sp T.Fr ⟶ C.I.t'.G.left}, r ≫ C.I.t'.G.hom = 𝟙 _ → r' ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m1.φ = r' ≫ C.I.m1.φ → r = r'` using `fun h h' e => c1.1.hom_ext e (h.trans h'.symm)`.

Establish `ext2 : ∀ {r r' : Sp T.Fr ⟶ C.I.t'.G.left}, r ≫ C.I.t'.G.hom = 𝟙 _ → r' ≫ C.I.t'.G.hom = 𝟙 _ → r ≫ C.I.m2.φ = r' ≫ C.I.m2.φ → r = r'` using `fun h h' e => c2.1.hom_ext e (h.trans h'.symm)`. Use `⟨⟨fun _ => zero_mem _, η[C.I.G.G].left, (1 : Over.mk (𝟙 _) ⟶ C.I.t'.G).left, Over.w η[C.I.G.G], Over.w (1 : Over.mk (𝟙 _) ⟶ C.I.t'.G), ?_, ?_, coord_one hz⟩, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Conclude with `(push_one_left c1 _).trans ((congrArg (· ≫ _) (Category.id_comp _)).trans (one_left (G := Xo.univ.t.G) (ptO Xo (xOf y))).symm)`. Conclude with `(push_one_left c2 _).trans (congrArg (· ≫ _) (Category.id_comp _))`. Introduce and unpack `a a' al al' ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ ⟨hs', aV', r', h1', h2', h3', h4', h5'⟩`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `rfl`. Take `rfl` from `ext1 h2 h2' (h3.trans h3'.symm)`. Take `rfl` from `coord_ext_of_injective (z := C.xT) (α := fun p => al p.2) (α' := fun p => al' p.2) (fun p => hs p.2) (fun p => hs' p.2) h5 h5' _ (IsFractionRing.injective T.V T.Fr) (h4.symm.trans h4')`. Use `coord_unique (α := fun p => al p.2) (α' := fun p => al' p.2) hz h5 h5'` as an intermediate fact.

Conclude with `funext fun j => congrFun this (0, j)`. Introduce and unpack `rfl`. Take `rfl` from `coord_ext (z := C.xT) (α := fun p => al p.2) (fun p => hs p.2) h5 h5'`. Take `rfl` from `ext2 h2 h2' (h4.trans h4'.symm)`. Conclude with `Over.OverMorphism.ext (h3.symm.trans h3')`.

Introduce and unpack `a a' al al' δ ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ ⟨hs', aV', r', h1', h2', h3', h4', h5'⟩ hδ`. Take `⟨χ, hX, hf, hm⟩` from `exists_eval (![cpt al, cpt al'] : Fin 2 → Pt T.V 0 _) (by`. Introduce `i j`. Use `fin_cases i`. Conclude with `hs j`.

Conclude with `hs' j)`. Establish `e : ∀ j, δ j = χ (B.G.F j)` using `fun j => (MvPowerSeries.constantCoeff_C (δ j)).symm.trans ((congrArg MvPowerSeries.constantCoeff (congrFun hδ j)).trans (hf _).symm)`. Establish `hδs : Small δ` using `fun j => e j ▸ hm _ (B.G.const j)`. Set `s : Over.mk (𝟙 (Sp T.V)) ⟶ C.I.G.G` to `Over.homMk aV h1`. Set `s' : Over.mk (𝟙 (Sp T.V)) ⟶ C.I.G.G` to `Over.homMk aV' h1'`.

Set `q : Over.mk (𝟙 (Sp T.Fr)) ⟶ C.I.t'.G` to `Over.homMk r h2`. Set `q' : Over.mk (𝟙 (Sp T.Fr)) ⟶ C.I.t'.G` to `Over.homMk r' h2'`. Use `⟨hδs, (s * s').left, (q * q').left, Over.w (s * s'), Over.w (q * q'), ?_, push_mul_left c2 q q' s s' _ h4 h4', ?_⟩` and prove the remaining obligations. Conclude with `(push_mul_left c1 q q' a a' (𝟙 (Sp T.Fr)) (h3.trans (Category.id_comp _).symm) (h3'.trans (Category.id_comp _).symm)).trans (Category.id_comp _)`. Conclude with `coord_mul (z := C.xT) B.G.F B.G.const (hB.1 ▸ C.chartT.law) χ (fun p => hm _ (MvPowerSeries.constantCoeff_X p)) (fun j => ((hX (0, j)).trans (MvPowerSeries.constantCoeff_C _)).symm) (fun j => ((hX (1, j)).trans (MvPowerSeries.constantCoeff_C _)).symm) hδs e s s' h5 h5'`.

Introduce and unpack `a al δ o ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ hδ`. Take `⟨χ, hX, hf, hm⟩` from `exists_eval (![cpt al] : Fin 1 → Pt T.V 0 _) (by`. Introduce `i j`. Use `fin_cases i`. Conclude with `hs j)`.

Establish `e : ∀ j, δ j = χ (B.A.act o j)` using `fun j => (MvPowerSeries.constantCoeff_C (δ j)).symm.trans ((congrArg MvPowerSeries.constantCoeff (congrFun hδ j)).trans (hf _).symm)`. Establish `hδs : Small δ` using `fun j => e j ▸ hm _ (B.A.const o j)`. Use `⟨hδs, aV ≫ (C.I.G.act.act o).left, r ≫ (C.I.t'.act.act o).left, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[Category.assoc, Over.w, h1]`. Rewrite using `[Category.assoc, Over.w, h2]`.

Rewrite using `[Category.assoc, C.I.m1.act o, ← Category.assoc]`. Conclude with `congrArg (· ≫ (Xo.univ.t.act.act o).left) h3`. Rewrite using `[Category.assoc, C.I.m2.act o, ← Category.assoc, ← Category.assoc]`. Conclude with `congrArg (· ≫ (C.I.G.act.act o).left) h4`. Use `coord_comp (z := C.xT) _ (B.A.act o) (B.A.const o) (fun m => ?_) χ (fun p => hm _ (MvPowerSeries.constantCoeff_X p)) (fun p => ?_) hδs e aV h5` and prove the remaining obligations.

Rewrite using `[hB.2.1]`. Conclude with `C.chartT.act m o`. Take `⟨i, j⟩` from `p`. Take `rfl : i = 0` from `Subsingleton.elim _ _`. Conclude with `((hX (0, j)).trans (MvPowerSeries.constantCoeff_C _)).symm`.

Introduce `al hs`. Take `⟨aV, h1, h5⟩` from `exists_coord hz (fun p => al p.2) fun p => hs p.2`. Establish `w : (spMap (algebraMap T.V T.Fr) ≫ aV) ≫ C.I.G.G.hom = 𝟙 _ ≫ spMap (algebraMap T.V T.Fr)`. Rewrite using `[Category.assoc, h1, Category.comp_id, Category.id_comp]`. Establish `h2` using `c2.1.lift_snd _ _ w`.

Conclude with `⟨Over.homMk (c2.1.lift _ _ w ≫ C.I.m1.φ) (by`. Rewrite using `[Category.assoc, c1.1.w, ← Category.assoc, h2]`. Conclude with `Category.id_comp _), hs, aV, c2.1.lift _ _ w, h1, h2, rfl, c2.1.lift_fst _ _ w, h5⟩`.
-/
theorem formPt_spec : ∀ (E : Type) [Field E] [NumberField E] [IsCMField E] (H : Host E) (Dw : Datum H) (l : Level H) (Xo : Moduli Dw l) (c : Coeff l) [StarRing (𝓞 E)], (∀ a : 𝓞 E, star a = H.bar a) → ∀ (T : CDVR) (io : c.F →+* T.Fr) (y : IntFr Xo c T io) (C : IntegralChartA3 Xo c T io y), ∀ B : FB T.V (chD C.ch) (𝓞 E), IsBT C B → (FormPt C 1 0) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (a = a' ↔ al = al')) ∧ (∀ (a a' : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al al' δ : Fin (chD C.ch) → T.V), FormPt C a al → FormPt C a' al' → (cpt δ : Pt T.V 0 (chD C.ch)) = addV B.G.F (cpt al) (cpt al') → FormPt C (a * a') δ) ∧ (∀ (a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G)) (al δ : Fin (chD C.ch) → T.V) (o : 𝓞 E), FormPt C a al → (cpt δ : Pt T.V 0 (chD C.ch)) = compV (B.A.act o) (cpt al) → FormPt C (a ≫ Xo.univ.t.act.act o) δ) ∧ ∀ al : Fin (chD C.ch) → T.V, Small al → ∃ a : (ptO Xo (xOf y) ⟶ Xo.univ.t.G), FormPt C a al := by
  intro E _ _ _ H Dw l Xo c _ _ T io y C B hB
  have hz : GlobalTheory.PowGerm.IsUnivJ C.I.G.G (Fin 1 × Fin (chD C.ch)) C.xT :=
    GlobalTheory.PowGerm.UnivJets.isUnivJ_of_isChartG C.I.G _ C.FT C.actT C.tgT C.xT C.tgBasis.1 C.tgBasis.2 C.chartT
  have c1 := C.I.m1.cart
  have c2 := C.I.m2.cart
  have ext1 : ∀ {r r' : Sp T.Fr ⟶ C.I.t'.G.left}, r ≫ C.I.t'.G.hom = 𝟙 _ → r' ≫ C.I.t'.G.hom = 𝟙 _ →
      r ≫ C.I.m1.φ = r' ≫ C.I.m1.φ → r = r' := fun h h' e => c1.1.hom_ext e (h.trans h'.symm)
  have ext2 : ∀ {r r' : Sp T.Fr ⟶ C.I.t'.G.left}, r ≫ C.I.t'.G.hom = 𝟙 _ → r' ≫ C.I.t'.G.hom = 𝟙 _ →
      r ≫ C.I.m2.φ = r' ≫ C.I.m2.φ → r = r' := fun h h' e => c2.1.hom_ext e (h.trans h'.symm)
  refine ⟨⟨fun _ => zero_mem _, η[C.I.G.G].left, (1 : Over.mk (𝟙 _) ⟶ C.I.t'.G).left, Over.w η[C.I.G.G],
    Over.w (1 : Over.mk (𝟙 _) ⟶ C.I.t'.G), ?_, ?_, coord_one hz⟩, ?_, ?_, ?_, ?_⟩
  · exact (push_one_left c1 _).trans ((congrArg (· ≫ _) (Category.id_comp _)).trans (one_left (G := Xo.univ.t.G) (ptO Xo (xOf y))).symm)
  · exact (push_one_left c2 _).trans (congrArg (· ≫ _) (Category.id_comp _))
  · rintro a a' al al' ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ ⟨hs', aV', r', h1', h2', h3', h4', h5'⟩
    constructor
    · rintro rfl
      obtain rfl := ext1 h2 h2' (h3.trans h3'.symm)
      obtain rfl := coord_ext_of_injective (z := C.xT) (α := fun p => al p.2) (α' := fun p => al' p.2)
        (fun p => hs p.2) (fun p => hs' p.2) h5 h5' _ (IsFractionRing.injective T.V T.Fr) (h4.symm.trans h4')
      have := coord_unique (α := fun p => al p.2) (α' := fun p => al' p.2) hz h5 h5'
      exact funext fun j => congrFun this (0, j)
    · rintro rfl
      obtain rfl := coord_ext (z := C.xT) (α := fun p => al p.2) (fun p => hs p.2) h5 h5'
      obtain rfl := ext2 h2 h2' (h4.trans h4'.symm)
      exact Over.OverMorphism.ext (h3.symm.trans h3')
  · rintro a a' al al' δ ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ ⟨hs', aV', r', h1', h2', h3', h4', h5'⟩ hδ
    obtain ⟨χ, hX, hf, hm⟩ := exists_eval (![cpt al, cpt al'] : Fin 2 → Pt T.V 0 _) (by
      intro i j
      fin_cases i
      · exact hs j
      · exact hs' j)
    have e : ∀ j, δ j = χ (B.G.F j) := fun j => (MvPowerSeries.constantCoeff_C (δ j)).symm.trans
      ((congrArg MvPowerSeries.constantCoeff (congrFun hδ j)).trans (hf _).symm)
    have hδs : Small δ := fun j => e j ▸ hm _ (B.G.const j)
    let s : Over.mk (𝟙 (Sp T.V)) ⟶ C.I.G.G := Over.homMk aV h1
    let s' : Over.mk (𝟙 (Sp T.V)) ⟶ C.I.G.G := Over.homMk aV' h1'
    let q : Over.mk (𝟙 (Sp T.Fr)) ⟶ C.I.t'.G := Over.homMk r h2
    let q' : Over.mk (𝟙 (Sp T.Fr)) ⟶ C.I.t'.G := Over.homMk r' h2'
    refine ⟨hδs, (s * s').left, (q * q').left, Over.w (s * s'), Over.w (q * q'), ?_,
      push_mul_left c2 q q' s s' _ h4 h4', ?_⟩
    · exact (push_mul_left c1 q q' a a' (𝟙 (Sp T.Fr)) (h3.trans (Category.id_comp _).symm)
        (h3'.trans (Category.id_comp _).symm)).trans (Category.id_comp _)
    · exact coord_mul (z := C.xT) B.G.F B.G.const (hB.1 ▸ C.chartT.law) χ (fun p => hm _ (MvPowerSeries.constantCoeff_X p))
        (fun j => ((hX (0, j)).trans (MvPowerSeries.constantCoeff_C _)).symm)
        (fun j => ((hX (1, j)).trans (MvPowerSeries.constantCoeff_C _)).symm) hδs e s s' h5 h5'
  · rintro a al δ o ⟨hs, aV, r, h1, h2, h3, h4, h5⟩ hδ
    obtain ⟨χ, hX, hf, hm⟩ := exists_eval (![cpt al] : Fin 1 → Pt T.V 0 _) (by
      intro i j
      fin_cases i
      exact hs j)
    have e : ∀ j, δ j = χ (B.A.act o j) := fun j => (MvPowerSeries.constantCoeff_C (δ j)).symm.trans
      ((congrArg MvPowerSeries.constantCoeff (congrFun hδ j)).trans (hf _).symm)
    have hδs : Small δ := fun j => e j ▸ hm _ (B.A.const o j)
    refine ⟨hδs, aV ≫ (C.I.G.act.act o).left, r ≫ (C.I.t'.act.act o).left, ?_, ?_, ?_, ?_, ?_⟩
    · rw [Category.assoc, Over.w, h1]
    · rw [Category.assoc, Over.w, h2]
    · rw [Category.assoc, C.I.m1.act o, ← Category.assoc]
      exact congrArg (· ≫ (Xo.univ.t.act.act o).left) h3
    · rw [Category.assoc, C.I.m2.act o, ← Category.assoc, ← Category.assoc]
      exact congrArg (· ≫ (C.I.G.act.act o).left) h4
    · refine coord_comp (z := C.xT) _ (B.A.act o) (B.A.const o) (fun m => ?_) χ
        (fun p => hm _ (MvPowerSeries.constantCoeff_X p)) (fun p => ?_) hδs e aV h5
      · rw [hB.2.1]
        exact C.chartT.act m o
      · obtain ⟨i, j⟩ := p
        obtain rfl : i = 0 := Subsingleton.elim _ _
        exact ((hX (0, j)).trans (MvPowerSeries.constantCoeff_C _)).symm
  · intro al hs
    obtain ⟨aV, h1, h5⟩ := exists_coord hz (fun p => al p.2) fun p => hs p.2
    have w : (spMap (algebraMap T.V T.Fr) ≫ aV) ≫ C.I.G.G.hom = 𝟙 _ ≫ spMap (algebraMap T.V T.Fr) := by
      rw [Category.assoc, h1, Category.comp_id, Category.id_comp]
    have h2 := c2.1.lift_snd _ _ w
    exact ⟨Over.homMk (c2.1.lift _ _ w ≫ C.I.m1.φ) (by
      rw [Category.assoc, c1.1.w, ← Category.assoc, h2]
      exact Category.id_comp _), hs, aV, c2.1.lift _ _ w, h1, h2, rfl, c2.1.lift_fst _ _ w, h5⟩

end GlobalTheory.PlaceFormPt
