import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.StalkLoc
import Development.WeilBound.CoreStatements.HodgeTatePoints.HtatLie
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelExistsUniqueSemilinearStatement

noncomputable section

namespace GlobalTheory.CompanionTheory.HtLink

open PositivityTheory.HtPt.Htat

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.BT hiding genPt
open GlobalTheory.CompanionTheory.Ar.HTTie
open GlobalTheory.CompanionTheory.Ar.HTChart (dual_comp snd_epsMul)

section Alg

variable {A Ω : Type} [CommRing A] [Field Ω] [Algebra A Ω] {L₀ : Type} [AddCommGroup L₀] [Module A L₀]

/- English proof (translation)
Take `⟨s, hs⟩` from `Module.Finite.fg_top (R := A) (M := L₀)`. Establish `key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧ ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b`. Introduce `s`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => exact ⟨1, by simp, by simp, by simp⟩`.

Consider the case `insert b s _ ih`. Take `⟨u, h1, h2, h3⟩` from `ih`. Take `⟨u', a, h1', h2', h3'⟩` from `hB _ (hw b)`. Use `⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2', fun c hc => ?_⟩` and prove the remaining obligations. Break down `Finset.mem_insert.1 hc with rfl | hc` into its components or cases.

Conclude with `⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩`. Take `⟨a', ha'⟩` from `h3 c hc`. Conclude with `⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩`. Take `⟨u, h1, h2, h3⟩` from `key s`. Establish `hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b`.

Introduce `b`. Establish `hb : b ∈ Submodule.span A (s : Set L₀)` using `hs ▸ Submodule.mem_top`. Proceed by induction on `hb using Submodule.span_induction with`. Consider the case `mem c hc => exact h3 c hc`. Consider the case `zero => exact ⟨0, by simp⟩`.

Consider the case `add c d _ _ hc hd`. Take `⟨a, ha⟩` from `hc`. Take `⟨a', ha'⟩` from `hd`. Conclude with `⟨a + a', by rw [map_add, map_add, ha, ha', mul_add]⟩`. Consider the case `smul r c _ hc`.

Take `⟨a, ha⟩` from `hc`. Conclude with `⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩`. Use `choose w₀ hw₀ using hall`. Use `⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩` and prove the remaining obligations. Rewrite using `[map_add, hw₀, hw₀, hw₀, map_add, mul_add]`.

Use `show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)`. Rewrite using `[map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem clear_denom [Module.Finite A L₀] (hinj : Function.Injective (algebraMap A Ω)) (B : Subring Ω)
    (hB : ∀ b ∈ B, ∃ u a : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      algebraMap A Ω u * b = algebraMap A Ω a)
    (w : L₀ →ₗ[A] Ω) (hw : ∀ b, w b ∈ B) :
    ∃ (u : A) (w₀ : Module.Dual A L₀), algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b, algebraMap A Ω (w₀ b) = algebraMap A Ω u * w b := by
  classical
  obtain ⟨s, hs⟩ := Module.Finite.fg_top (R := A) (M := L₀)
  have key : ∀ s : Finset L₀, ∃ u : A, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ B ∧
      ∀ b ∈ s, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro s
    induction s using Finset.induction_on with
    | empty => exact ⟨1, by simp, by simp, by simp⟩
    | insert b s _ ih =>
      obtain ⟨u, h1, h2, h3⟩ := ih
      obtain ⟨u', a, h1', h2', h3'⟩ := hB _ (hw b)
      refine ⟨u * u', by rw [map_mul]; exact mul_ne_zero h1 h1', by rw [map_mul, mul_inv]; exact mul_mem h2 h2',
        fun c hc => ?_⟩
      rcases Finset.mem_insert.1 hc with rfl | hc
      · exact ⟨u * a, by rw [map_mul, map_mul, ← h3']; ring⟩
      · obtain ⟨a', ha'⟩ := h3 c hc
        exact ⟨u' * a', by rw [map_mul, map_mul, ha']; ring⟩
  obtain ⟨u, h1, h2, h3⟩ := key s
  have hall : ∀ b, ∃ a, algebraMap A Ω a = algebraMap A Ω u * w b := by
    intro b
    have hb : b ∈ Submodule.span A (s : Set L₀) := hs ▸ Submodule.mem_top
    induction hb using Submodule.span_induction with
    | mem c hc => exact h3 c hc
    | zero => exact ⟨0, by simp⟩
    | add c d _ _ hc hd =>
      obtain ⟨a, ha⟩ := hc
      obtain ⟨a', ha'⟩ := hd
      exact ⟨a + a', by rw [map_add, map_add, ha, ha', mul_add]⟩
    | smul r c _ hc =>
      obtain ⟨a, ha⟩ := hc
      exact ⟨r * a, by rw [map_mul, map_smul, ha, Algebra.smul_def]; ring⟩
  choose w₀ hw₀ using hall
  refine ⟨u, ⟨⟨w₀, fun a b => hinj ?_⟩, fun r a => hinj ?_⟩, h1, h2, hw₀⟩
  · rw [map_add, hw₀, hw₀, hw₀, map_add, mul_add]
  · show algebraMap A Ω (w₀ (r • a)) = algebraMap A Ω (r * w₀ a)
    rw [map_mul, hw₀, hw₀, map_smul, Algebra.smul_def]; ring

variable {Li : Type} [AddCommGroup Li] [Module Ω Li] [Module A Li] [IsScalarTower A Ω Li]

/- English proof (translation)
Establish `hinj` using `IsFractionRing.injective A Ω`. Set `J : Module.Dual A L₀ → Module.Dual Ω Li` to `fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)`. Establish `hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b)` using `fun w b => hj₀.lift_eq _ b`. Establish `hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w'` using `fun w w' h => hj₀.algHom_ext _ _ h`. Establish `hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e` using `fun a w e => by`.

Rewrite using `[← algebraMap_smul Ω a w]`. Both sides reduce to the same expression. Set `j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li` to `{ toFun := J map_add' := fun w w' => hext _ _ fun b => by simp [hJ] map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }`. Use `⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩` and prove the remaining obligations. Establish `hs : algebraMap A Ω s ≠ 0` using `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2`.

Rewrite using `[Module.End.isUnit_iff]`. Use `⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩` and prove the remaining obligations. Establish `h' : (s : A) • w = (s : A) • w'` using `h`. Rewrite `h'` using `[← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w']`. Conclude with `smul_right_injective _ hs h'`.

Use `show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w`. Rewrite using `[← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]`. Take `⟨u, w₀, h1, -, h3⟩` from `clear_denom hinj ⊤ (fun b _ => by`. Take `⟨a, u, hu, rfl⟩` from `IsFractionRing.div_surjective (A := A) b`. Use `IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu` as an intermediate fact.

Conclude with `⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)`. Use `⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩` and prove the remaining obligations. Use `show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)`. Rewrite using `[hsm, hJ, h3]`. Both sides reduce to the same expression.

Introduce `w w' h`. Use `⟨1, ?_⟩` and prove the remaining obligations. Establish `: w = w'` using `LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)`. Rewrite using `[this]`.
-/
theorem exists_dualBC [IsDomain A] [IsFractionRing A Ω] [Module.Finite A L₀] (j₀ : L₀ →ₗ[A] Li)
    (hj₀ : IsBaseChange Ω j₀) :
    ∃ j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li, IsBaseChange Ω j ∧
      ∀ w b, j w (j₀ b) = algebraMap A Ω (w b) := by
  have hinj := IsFractionRing.injective A Ω
  let J : Module.Dual A L₀ → Module.Dual Ω Li := fun w => hj₀.lift (Algebra.linearMap A Ω ∘ₗ w)
  have hJ : ∀ w b, J w (j₀ b) = algebraMap A Ω (w b) := fun w b => hj₀.lift_eq _ b
  have hext : ∀ w w' : Module.Dual Ω Li, (∀ b, w (j₀ b) = w' (j₀ b)) → w = w' := fun w w' h => hj₀.algHom_ext _ _ h
  have hsm : ∀ (a : A) (w : Module.Dual Ω Li) e, (a • w) e = algebraMap A Ω a * w e := fun a w e => by
    rw [← algebraMap_smul Ω a w]; rfl
  let j : Module.Dual A L₀ →ₗ[A] Module.Dual Ω Li :=
    { toFun := J
      map_add' := fun w w' => hext _ _ fun b => by simp [hJ]
      map_smul' := fun a w => hext _ _ fun b => by simp [hJ, hsm] }
  refine ⟨j, (isLocalizedModule_iff_isBaseChange (nonZeroDivisors A) Ω j).1 ⟨fun s => ?_, fun w => ?_, ?_⟩, hJ⟩
  · have hs : algebraMap A Ω s ≠ 0 := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors s.2
    rw [Module.End.isUnit_iff]
    refine ⟨fun w w' h => ?_, fun w => ⟨(algebraMap A Ω s)⁻¹ • w, ?_⟩⟩
    · have h' : (s : A) • w = (s : A) • w' := h
      rw [← algebraMap_smul Ω, ← algebraMap_smul Ω (s : A) w'] at h'
      exact smul_right_injective _ hs h'
    · show (s : A) • ((algebraMap A Ω s)⁻¹ • w) = w
      rw [← algebraMap_smul Ω, smul_smul, mul_inv_cancel₀ hs, one_smul]
  · obtain ⟨u, w₀, h1, -, h3⟩ := clear_denom hinj ⊤ (fun b _ => by
      obtain ⟨a, u, hu, rfl⟩ := IsFractionRing.div_surjective (A := A) b
      have := IsFractionRing.to_map_ne_zero_of_mem_nonZeroDivisors (K := Ω) hu
      exact ⟨u, a, this, trivial, by field_simp⟩) ((w.restrictScalars A) ∘ₗ j₀) (fun _ => trivial)
    refine ⟨⟨w₀, ⟨u, mem_nonZeroDivisors_of_ne_zero fun h => h1 (by rw [h, map_zero])⟩⟩, hext _ _ fun b => ?_⟩
    show ((u : A) • w) (j₀ b) = J w₀ (j₀ b)
    rw [hsm, hJ, h3]; rfl
  · intro w w' h
    refine ⟨1, ?_⟩
    have : w = w' := LinearMap.ext fun b => hinj (by rw [← hJ, ← hJ]; exact LinearMap.congr_fun h _)
    rw [this]

end Alg

section Geo

variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Spec (CommRingCat.of Ω) ⟶ X}
  {A : Type} [CommRing A] [Algebra A Ω] {x : Spec (CommRingCat.of A) ⟶ X}

/- English proof (translation)
Take `⟨_, hS, -, hg⟩` from `stalk_loc hξ _ hk x hx p q hp hsub`. Establish `hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a` using `RingHom.congr_fun hg`. Use `⟨fun u hu => ?_, ?_⟩` and prove the remaining obligations. Take `⟨t, ht⟩` from `(IsLocalization.map_units (X.presheaf.stalk q.1) (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv`. Establish `h1 : algebraMap A Ω u * genMap ξ q t = 1` using `by rw [← hg', ← map_mul, ht, map_one]`.

Conclude with `⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩`. Introduce and unpack `_ ⟨c, rfl⟩`. Take `⟨⟨a, s⟩, h⟩` from `IsLocalization.surj p.asIdeal.primeCompl c`. Conclude with `⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩`.
-/
theorem regAt_frac (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (p : PrimeSpectrum A) (q : Cpt ξ) (hp : x p = q.1)
    (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) :
    (∀ u ∉ p.asIdeal, algebraMap A Ω u ≠ 0 ∧ (algebraMap A Ω u)⁻¹ ∈ regAt ξ q) ∧
      ∀ b ∈ regAt ξ q, ∃ u a : A, u ∉ p.asIdeal ∧ algebraMap A Ω u * b = algebraMap A Ω a := by
  obtain ⟨_, hS, -, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hg' : ∀ a, genMap ξ q (algebraMap A _ a) = algebraMap A Ω a := RingHom.congr_fun hg
  refine ⟨fun u hu => ?_, ?_⟩
  · obtain ⟨t, ht⟩ := (IsLocalization.map_units (X.presheaf.stalk q.1)
      (⟨u, hu⟩ : p.asIdeal.primeCompl)).exists_right_inv
    have h1 : algebraMap A Ω u * genMap ξ q t = 1 := by rw [← hg', ← map_mul, ht, map_one]
    exact ⟨left_ne_zero_of_mul_eq_one h1, t, (eq_inv_of_mul_eq_one_right h1)⟩
  · rintro _ ⟨c, rfl⟩
    obtain ⟨⟨a, s⟩, h⟩ := IsLocalization.surj p.asIdeal.primeCompl c
    exact ⟨s, a, s.2, by rw [← hg', ← hg', ← h, map_mul, mul_comm]⟩

variable {G : Over X} [GrpObj G] [IsCommMonObj G] [Smooth G.hom] {Li : Type} [AddCommGroup Li] [Module Ω Li]
  (M : LieModel G ξ Li) {L₀ : Type} [AddCommGroup L₀] [Module A L₀] (M₀ : LieModel G x L₀)

omit [IsCommMonObj G] in
/- English proof (translation)
Substitute `hx` using the available equality. Take `⟨j, hj, -⟩` from `GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M`. Establish `hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left` using `fun v => (Category.comp_id _).symm.trans (hj v)`. Set `j₀ : L₀ →ₗ[A] Li` to `{ toFun := j map_add' := j.map_add map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }`. Conclude with `⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩`.
-/
theorem exists_lieBC (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) [Module A Li]
    [IsScalarTower A Ω Li] : ∃ j₀ : L₀ →ₗ[A] Li, IsBaseChange Ω j₀ ∧ ∀ v, (M.pt (j₀ v)).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left := by
  subst hx
  obtain ⟨j, hj, -⟩ := GlobalTheory.T.lie_model_existsUnique_semilinear X G A Ω (algebraMap A Ω) x L₀ Li M₀ M
  have hj' : ∀ v, (M.pt (j v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left :=
    fun v => (Category.comp_id _).symm.trans (hj v)
  let j₀ : L₀ →ₗ[A] Li :=
    { toFun := j
      map_add' := j.map_add
      map_smul' := fun a v => by rw [j.map_smulₛₗ, algebraMap_smul]; rfl }
  exact ⟨j₀, (lie_proj X G A x L₀ M₀).2.2 Ω Li M j₀ hj', hj'⟩

omit [IsCommMonObj G] [Smooth G.hom] in
/- English proof (translation)
Set `ψ` to `LieCarrier.epsHom (algebraMap A O) x _ hzs`. Establish `hleft : (ψ ≫ M₀.pt b).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left` using `rfl`. Use `⟨ψ ≫ M₀.pt b, ?_, ?_⟩` and prove the remaining obligations. Establish `t : _ ≫ (M₀.pt b).left = _` using `M₀.tan b`. Rewrite `t` using `[one_left]`.

Use `show _ ≫ (ψ ≫ M₀.pt b).left = _`. Rewrite using `[hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]`. Simplify using `only [Over.mk_hom]`. Rewrite using `[← Category.assoc, hzs]`. Rewrite using `[hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]`.
-/
theorem tan_ext {O : Type} [CommRing O] [Algebra A O] {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (b : L₀) : ∃ v : epsAt z ⟶ G, IsTanAt G z v ∧
      (M.pt (j₀ b)).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left := by
  let ψ := LieCarrier.epsHom (algebraMap A O) x _ hzs
  have hleft : (ψ ≫ M₀.pt b).left =
      Spec.map (CommRingCat.ofHom (dualMap (algebraMap A O))) ≫ (M₀.pt b).left := rfl
  refine ⟨ψ ≫ M₀.pt b, ?_, ?_⟩
  · have t : _ ≫ (M₀.pt b).left = _ := M₀.tan b
    rw [one_left] at t
    show _ ≫ (ψ ≫ M₀.pt b).left = _
    rw [hleft, one_left, ← Category.assoc, ← spec_comp, dual_fst, spec_comp, Category.assoc, t]
    simp only [Over.mk_hom]
    rw [← Category.assoc, hzs]
  · rw [hleft, hj, ← Category.assoc, ← spec_comp, dual_comp, hg]

/- English proof (translation)
Take `⟨u, hu, b, hub⟩` from `exists_denom lie_proj G S x M₀ hzs v hv`. Establish `hgu : g (algebraMap A O u) = algebraMap A Ω u` using `RingHom.congr_fun hg u`. Use `⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩` and prove the remaining obligations. Rewrite using `[M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc, ← spec_comp, ← spec_comp, dual_eps]`.
-/
theorem tan_denom {O : Type} [CommRing O] [Algebra A O] (S : Submonoid A) [IsLocalization S O]
    {z : Spec (CommRingCat.of O) ⟶ X}
    (hzs : Spec.map (CommRingCat.ofHom (algebraMap A O)) ≫ x = z) (g : O →+* Ω)
    (hg : g.comp (algebraMap A O) = algebraMap A Ω) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (e : Li) (v : epsAt z ⟶ G) (hv : IsTanAt G z v)
    (he' : (M.pt e).left = Spec.map (CommRingCat.ofHom (dualMap g)) ≫ v.left) :
    ∃ u ∈ S, ∃ b, algebraMap A Ω u • e = j₀ b := by
  obtain ⟨u, hu, b, hub⟩ := exists_denom lie_proj G S x M₀ hzs v hv
  have hgu : g (algebraMap A O u) = algebraMap A Ω u := RingHom.congr_fun hg u
  refine ⟨u, hu, b, hgu ▸ M.inj (Over.OverMorphism.ext ?_)⟩
  rw [M.smul, he', hj, ← hg, ← dual_comp, spec_comp, Category.assoc, ← hub, ← Category.assoc, ← Category.assoc,
    ← spec_comp, ← spec_comp, dual_eps]

/- English proof (translation)
Take `⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1` from `hq`. Take `⟨_, hS, hzs, hg⟩` from `stalk_loc hξ _ hk x hx p q hp hsub`. Establish `hlat` using `(lieLat_carrier X G Ω ξ Li M q).1`. Use `⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩` and prove the remaining obligations. Conclude with `tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b`.

Take `⟨v, hv, he'⟩` from `(hlat e).1 he`. Take `⟨u, hu, b, hje⟩` from `tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'`. Take `⟨h1, h2⟩` from `(regAt_frac hξ hk hx p q hp hsub).1 u hu`. Establish `: w e = (algebraMap A Ω u)⁻¹ * w (j₀ b)`. Rewrite using `[← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]`.

Rewrite using `[this]`. Conclude with `mul_mem h2 (h b)`.
-/
theorem mem_omLat_iff (hξ : IsCptGen ξ) (hk : Function.Injective (algebraMap A Ω))
    (hx : Spec.map (CommRingCat.ofHom (algebraMap A Ω)) ≫ x = ξ) (j₀ : L₀ → Li)
    (hj : ∀ v, (M.pt (j₀ v)).left = Spec.map (CommRingCat.ofHom (dualMap (algebraMap A Ω))) ≫ (M₀.pt v).left)
    (q : Cpt ξ) (hq : q.1 ∈ Set.range x) (hsub : ∀ a, algebraMap A Ω a ∈ regAt ξ q) (w : Module.Dual Ω Li) :
    w ∈ M.omLat q ↔ ∀ b, w (j₀ b) ∈ regAt ξ q := by
  obtain ⟨p, hp⟩ : ∃ p : PrimeSpectrum A, x p = q.1 := hq
  obtain ⟨_, hS, hzs, hg⟩ := stalk_loc hξ _ hk x hx p q hp hsub
  have hlat := (lieLat_carrier X G Ω ξ Li M q).1
  refine ⟨fun h b => h _ ((hlat _).2 ?_), fun h e he => ?_⟩
  · exact tan_ext M M₀ hzs (genMap ξ q) hg j₀ hj b
  · obtain ⟨v, hv, he'⟩ := (hlat e).1 he
    obtain ⟨u, hu, b, hje⟩ := tan_denom M M₀ p.asIdeal.primeCompl hzs (genMap ξ q) hg j₀ hj e v hv he'
    obtain ⟨h1, h2⟩ := (regAt_frac hξ hk hx p q hp hsub).1 u hu
    have : w e = (algebraMap A Ω u)⁻¹ * w (j₀ b) := by
      rw [← hje, map_smul, smul_eq_mul, ← _root_.mul_assoc, inv_mul_cancel₀ h1, _root_.one_mul]
    rw [this]
    exact mul_mem h2 (h b)

end Geo

end GlobalTheory.CompanionTheory.HtLink
