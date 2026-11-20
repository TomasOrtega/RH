import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.IndEtOfForallFinset
import Development.AbelianVarietyTheory.Definitions.Divisors.DivisorSupportCondition
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.AlternatingSumThreeTerms
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SmoothSurjectiveCechDescentCohomologyStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.FreeSheafHomValueAtCechNerveSimplexBijectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainClassesBasicPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyOneCechCocycleOfPullbackZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SimplicialCochainCoboundaryOfClassZeroStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecSingleStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.IsLimitWidePullbackConeSpecTensorSquareStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.TripleTensorWidePullbackLimitStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.EtaleCohomologyPullbackEqZeroOfCechOneCocycleStatement
open CategoryTheory Limits AlgebraicGeometry Opposite CochainComplex CochainComplex.HomComplex Simplicial TensorProduct GlobalTheory.EtC GlobalTheory.CechOne

noncomputable section

namespace GlobalTheory.CechOne

variable (A B : Type) [CommRing A] [CommRing B] [Algebra A B]

/- English proof (translation)
Establish `hc0 : ∀ {n : ℕ}, cobd (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) = 0`. Introduce `n`. Simplify using `[cobd]`. Take `⟨x, hx⟩` from `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 1).1 0 hc0`. Establish `h4` using `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 0).2.2.2.1 0 x (by rw [hc0]; exact hx)`.

Rewrite `hx` using `[h4]`. Conclude with `hx`.
-/
theorem isCls_zero (R : Type) [CommRing R] (F : Shv R) (E : Spc) :
    IsCls (0 : (free R).obj (E.obj (op ⦋1⦌)) ⟶ F) (0 : H R E F ((1 : ℕ) : ℤ)) := by
  have hc0 : ∀ {n : ℕ}, cobd (0 : (free R).obj (E.obj (op ⦋n⦌)) ⟶ F) = 0 := by
    intro n; simp [cobd]
  obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 1).1 0 hc0
  have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F E 0).2.2.2.1 0 x (by rw [hc0]; exact hx)
  rw [h4] at hx
  exact hx

/- English proof (translation)
Rewrite `h` using `[sub_add_eq_add_sub, sub_eq_zero]`. Rewrite using `[← h, add_comm]`.
-/
theorem mul_inv_mul_cancel_comm {M : Type*} [AddCommGroup M] {a b c : M} (h : a - b + c = 0) : b = c + a := by
  rw [sub_add_eq_add_sub, sub_eq_zero] at h
  rw [← h, add_comm]

/- English proof (translation)
Rewrite using `[h]`. Normalize the expressions using the abelian group laws.
-/
theorem sub_add_eq_zero_of_eq_add {M : Type*} [AddCommGroup M] {a b c : M} (h : b = c + a) : a - b + c = 0 := by
  rw [h]
  abel

/- English proof (translation)
Unfold both sides. The equivalence is reflexive.
-/
theorem mem_Z1_iff_cocycle (R : Type) [CommRing R] (F : Shv R) (w : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) :
    w ∈ Z1 F A B ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom w +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom w := Iff.rfl

/- English proof (translation)
Establish `hinj` using `(GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 2 _ _ (y2 A B) (hy2 A B) (GlobalTheory.T.triple_tensor_wide_pullback_limit A B).some).1`. Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h2` using `(val_coboundary_second_level A B R F s).symm.trans ((congrArg (fun t => val t (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)) h).trans (val_zero R _ _))`. Conclude with `mul_inv_mul_cancel_comm h2`.

Introduce `h`. Apply `hinj` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) = val 0 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)`. Rewrite using `[val_zero]`. Conclude with `(val_coboundary_second_level A B R F s).trans (sub_add_eq_zero_of_eq_add h)`.
-/
theorem cobd_eq_zero_iff (R : Type) [CommRing R] (F : Shv R) (s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F) :
    cobd s = 0 ↔
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) =
      ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map (AlgHom.id A B)
        (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) +
      ((onRings F).map (CommRingCat.ofHom
        (Algebra.TensorProduct.includeRight : B ⊗[A] B →ₐ[A] B ⊗[A] (B ⊗[A] B)).toRingHom)).hom (val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B)) := by
  have hinj := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 2 _ _ (y2 A B) (hy2 A B) (GlobalTheory.T.triple_tensor_wide_pullback_limit A B).some).1
  constructor
  · intro h
    have h2 := (val_coboundary_second_level A B R F s).symm.trans
      ((congrArg (fun t => val t (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)) h).trans (val_zero R _ _))
    exact mul_inv_mul_cancel_comm h2
  · intro h
    apply hinj
    change val (cobd s) (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B) = val 0 (Spec (CommRingCat.of (B ⊗[A] (B ⊗[A] B)))) (P2 A B)
    rw [val_zero]
    exact (val_coboundary_second_level A B R F s).trans (sub_add_eq_zero_of_eq_add h)

def Rel (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) (x : H R (sp A) F 1) : Prop :=
  ∃ s : (free R).obj ((cech (fB A B)).obj (op ⦋1⦌)) ⟶ F,
    val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) ∧
      IsCls s (pull R (cechAug (fB A B)) F ((1 : ℕ) : ℤ) x)

/- English proof (translation)
Take `⟨s, hs, hx⟩` from `h`. Take `⟨s', hs', hx'⟩` from `h'`. Establish `hss : s = s'` using `(GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).1 (hs.trans hs'.symm)`. Substitute `hss` using the available equality. Use `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).2.2.1 s _ _ hx hx'` as an intermediate fact.

Take `⟨h1, h2⟩` from `smooth_surj A B`. Conclude with `(GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).1 this`.
-/
theorem rel_unique [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x x' : H R (sp A) F 1) (h : Rel A B R F u x) (h' : Rel A B R F u x') : x = x' := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  have hss : s = s' :=
    (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).1 (hs.trans hs'.symm)
  subst hss
  have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).2.2.1 s _ _ hx hx'
  obtain ⟨h1, h2⟩ := smooth_surj A B
  exact (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).1 this

/- English proof (translation)
Take `⟨s, hs⟩` from `(GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).2 (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))`. Establish `hs' : val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))` using `hs`. Establish `hc : cobd s = 0` using `(cobd_eq_zero_iff A B R F s).2 (by rw [hs']; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)`. Take `⟨y, hy⟩` from `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).1 s hc`. Take `⟨h1, h2⟩` from `smooth_surj A B`.

Take `⟨x, hx⟩` from `(GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).2 y`. Conclude with `⟨x, s, hs', hx ▸ hy⟩`.
-/
theorem rel_exists [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    ∃ x, Rel A B R F u x := by
  obtain ⟨s, hs⟩ := (GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 1 _ _ (y1 A B) (hy1 A B) (GlobalTheory.T.isLimit_widePullbackCone_spec_tensorSquare A B).some).2
    (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))
  have hs' : val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := hs
  have hc : cobd s = 0 := (cobd_eq_zero_iff A B R F s).2 (by rw [hs']; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
  obtain ⟨y, hy⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F (cech (fB A B)) 1).1 s hc
  obtain ⟨h1, h2⟩ := smooth_surj A B
  obtain ⟨x, hx⟩ := (GlobalTheory.T.etC_a2 R (fB A B) F ((1 : ℕ) : ℤ)).2 y
  exact ⟨x, s, hs', hx ▸ hy⟩

variable {A B} in
/- English proof (translation)
Take `⟨s, hs, hx⟩` from `h`. Take `⟨s', hs', hx'⟩` from `h'`. Use `⟨s + s', ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[val_add, hs, hs']`. Both sides reduce to the same expression.

Rewrite using `[map_add]`. Conclude with `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.1 s s' _ _ hx hx'`.
-/
theorem rel_add (R : Type) [CommRing R] (F : Shv R) (u u' : Z1 F A B) (x x' : H R (sp A) F 1)
    (h : Rel A B R F u x) (h' : Rel A B R F u' x') : Rel A B R F (u + u') (x + x') := by
  obtain ⟨s, hs, hx⟩ := h
  obtain ⟨s', hs', hx'⟩ := h'
  refine ⟨s + s', ?_, ?_⟩
  · rw [val_add, hs, hs']
    rfl
  · rw [map_add]
    exact (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.1 s s' _ _ hx hx'

/- English proof (translation)
Use `⟨0, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[val_zero]`. Both sides reduce to the same expression. Rewrite using `[map_zero]`. Conclude with `isCls_zero R F _`.
-/
theorem rel_zero (R : Type) [CommRing R] (F : Shv R) : Rel A B R F 0 0 := by
  refine ⟨0, ?_, ?_⟩
  · rw [val_zero]
    rfl
  · rw [map_zero]
    exact isCls_zero R F _

open Classical in

def gam (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) : H R (sp A) F 1 :=
  if Algebra.Etale A B ∧ Module.FaithfullyFlat A B then Classical.epsilon (Rel A B R F u) else 0

/- English proof (translation)
Unfold `gam`. Rewrite using `[if_pos ⟨inferInstance, inferInstance⟩]`. Conclude with `Classical.epsilon_spec (rel_exists A B R F u)`.
-/
theorem gam_spec [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B) :
    Rel A B R F u (gam A B R F u) := by
  unfold gam
  rw [if_pos ⟨inferInstance, inferInstance⟩]
  exact Classical.epsilon_spec (rel_exists A B R F u)

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun h => h ▸ gam_spec A B R F u, fun h => rel_unique A B R F u _ _ (gam_spec A B R F u) h⟩`.
-/
theorem gam_eq [Algebra.Etale A B] [Module.FaithfullyFlat A B] (R : Type) [CommRing R] (F : Shv R) (u : Z1 F A B)
    (x : H R (sp A) F 1) : gam A B R F u = x ↔ Rel A B R F u x :=
  ⟨fun h => h ▸ gam_spec A B R F u, fun h => rel_unique A B R F u _ _ (gam_spec A B R F u) h⟩

def gamHom (R : Type) [CommRing R] (F : Shv R) : Z1 F A B →+ H R (sp A) F 1 where
  toFun := gam A B R F
  map_zero' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F 0 0).2 (rel_zero A B R F)
    · unfold gam
      rw [if_neg h]
  map_add' u u' := by
    by_cases h : Algebra.Etale A B ∧ Module.FaithfullyFlat A B
    · haveI := h.1
      haveI := h.2
      exact (gam_eq A B R F _ _).2 (rel_add R F _ _ _ _ (gam_spec A B R F u) (gam_spec A B R F u'))
    · unfold gam
      rw [if_neg h, if_neg h, if_neg h, add_zero]

/- English proof (translation)
Introduce `R _ F A _`. Use `⟨fun B => gamHom A B R F, ?_⟩` and prove the remaining obligations. Introduce `B _ _ _ _`. Establish `bij0` using `GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 0 _ _ _ _ (GlobalTheory.T.isLimit_widePullbackCone_spec_single A B).some`. Use `⟨?_, ?_, ?_, ?_⟩` and prove the remaining obligations.

Introduce `u`. Express the relevant statement in the definitionally equal form `gam A B R F u = 0 ↔ _`. Rewrite using `[gam_eq]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨s, hs, hx⟩`.

Rewrite `hx` using `[map_zero]`. Take `⟨t, rfl⟩` from `GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ s hx`. Conclude with `⟨val t (Spec (CommRingCat.of B)) (P0 A B), by rw [← hs, val_coboundary_first_level]⟩`. Introduce and unpack `⟨v, hv⟩`. Take `⟨t, ht⟩` from `bij0.2 v`.

Establish `ht' : val t (Spec (CommRingCat.of B)) (P0 A B) = v` using `ht`. Establish `hval : val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B)))`. Rewrite using `[val_coboundary_first_level, ht', hv]`. Establish `hc : cobd (cobd t) = 0` using `(cobd_eq_zero_iff A B R F _).2 (by rw [hval]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)`. Use `⟨cobd t, hval, ?_⟩` and prove the remaining obligations.

Rewrite using `[map_zero]`. Take `⟨x, hx⟩` from `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).1 (cobd t) hc`. Establish `h4` using `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 0).2.2.2.1 t x hx`. Rewrite `hx` using `[h4]`. Conclude with `hx`.

Introduce `x hx`. Take `⟨s, hs, hcls⟩` from `GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero R F _ _ (fB A B) x hx`. Conclude with `⟨⟨val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B), (mem_Z1_iff_cocycle A B R F _).2 ((cobd_eq_zero_iff A B R F s).1 hs)⟩, (gam_eq A B R F _ x).2 ⟨s, rfl, hcls⟩⟩`. Introduce `u`. Take `⟨s, hs, hcls⟩` from `gam_spec A B R F u`.

Conclude with `GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle R F (fB A B) s ((cobd_eq_zero_iff A B R F s).2 (by rw [hs]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)) _ hcls`. Introduce `B' _ _ _ _ φ u u' hu`. Express the relevant statement in the definitionally equal form `gam A B' R F u' = gam A B R F u`. Rewrite using `[gam_eq]`. Take `⟨s, hs, hcls⟩` from `gam_spec A B R F u`.

Use `⟨(free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[val_cech_map_first_level, hs, hu]`. Use `(GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.2.2.2 _ (cechMap (fB A B) (fB A B') _ (spec_algHom φ)) s _ hcls` as an intermediate fact. Rewrite `this` using `[← pull_comp, cechMap_aug]`. Conclude with `this`.
-/
theorem cech1 : ∀ (R : Type) [CommRing R] (F : Shv R) (A : Type) [CommRing A], ∃ γ : ∀ (B : Type) [CommRing B] [Algebra A B], Z1 F A B →+ H R (sp A) F 1, ∀ (B : Type) [CommRing B] [Algebra A B] [Algebra.Etale A B] [Module.FaithfullyFlat A B], (∀ u : Z1 F A B, γ B u = 0 ↔ ∃ v : (onRings F).obj (CommRingCat.of B), (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeRight : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v - ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.includeLeft : B →ₐ[A] B ⊗[A] B).toRingHom)).hom v) ∧ (∀ x : H R (sp A) F 1, pull R (spMap (algebraMap A B)) F 1 x = 0 → ∃ u, γ B u = x) ∧ (∀ u, pull R (spMap (algebraMap A B)) F 1 (γ B u) = 0) ∧ ∀ (B' : Type) [CommRing B'] [Algebra A B'] [Algebra.Etale A B'] [Module.FaithfullyFlat A B'] (φ : B →ₐ[A] B') (u : Z1 F A B) (u' : Z1 F A B'), (u' : (onRings F).obj (CommRingCat.of (B' ⊗[A] B'))) = ((onRings F).map (CommRingCat.ofHom (Algebra.TensorProduct.map φ φ).toRingHom)).hom u → γ B' u' = γ B u := by
  intro R _ F A _
  refine ⟨fun B => gamHom A B R F, ?_⟩
  intro B _ _ _ _
  have bij0 := GlobalTheory.T.freeSheafHomValueAt_cechNerveSimplex_bijective R F _ _ (fB A B) 0 _ _ _ _ (GlobalTheory.T.isLimit_widePullbackCone_spec_single A B).some
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro u
    change gam A B R F u = 0 ↔ _
    rw [gam_eq]
    constructor
    · rintro ⟨s, hs, hx⟩
      rw [map_zero] at hx
      obtain ⟨t, rfl⟩ := GlobalTheory.T.simplicialCochain_coboundary_of_class_zero R F _ s hx
      exact ⟨val t (Spec (CommRingCat.of B)) (P0 A B), by rw [← hs, val_coboundary_first_level]⟩
    · rintro ⟨v, hv⟩
      obtain ⟨t, ht⟩ := bij0.2 v
      have ht' : val t (Spec (CommRingCat.of B)) (P0 A B) = v := ht
      have hval : val (cobd t) (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B) = (u : (onRings F).obj (CommRingCat.of (B ⊗[A] B))) := by
        rw [val_coboundary_first_level, ht', hv]
      have hc : cobd (cobd t) = 0 := (cobd_eq_zero_iff A B R F _).2 (by rw [hval]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)
      refine ⟨cobd t, hval, ?_⟩
      rw [map_zero]
      obtain ⟨x, hx⟩ := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).1 (cobd t) hc
      have h4 := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 0).2.2.2.1 t x hx
      rw [h4] at hx
      exact hx
  · intro x hx
    obtain ⟨s, hs, hcls⟩ := GlobalTheory.T.etaleCohomology_one_cechCocycle_of_pullback_zero R F _ _ (fB A B) x hx
    exact ⟨⟨val s (Spec (CommRingCat.of (B ⊗[A] B))) (P1 A B), (mem_Z1_iff_cocycle A B R F _).2 ((cobd_eq_zero_iff A B R F s).1 hs)⟩, (gam_eq A B R F _ x).2 ⟨s, rfl, hcls⟩⟩
  · intro u
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    exact GlobalTheory.T.etaleCohomologyPullback_eq_zero_of_cechOneCocycle R F (fB A B) s ((cobd_eq_zero_iff A B R F s).2 (by rw [hs]; exact (mem_Z1_iff_cocycle A B R F _).1 u.2)) _ hcls
  · intro B' _ _ _ _ φ u u' hu
    change gam A B' R F u' = gam A B R F u
    rw [gam_eq]
    obtain ⟨s, hs, hcls⟩ := gam_spec A B R F u
    refine ⟨(free R).map ((cechMap (fB A B) (fB A B') _ (spec_algHom φ)).app (op ⦋1⦌)) ≫ s, ?_, ?_⟩
    · rw [val_cech_map_first_level, hs, hu]
    · have := (GlobalTheory.T.simplicialCochain_classes_basic_properties R F _ 1).2.2.2.2 _ (cechMap (fB A B) (fB A B') _ (spec_algHom φ)) s _ hcls
      rw [← pull_comp, cechMap_aug] at this
      exact this

end GlobalTheory.CechOne
