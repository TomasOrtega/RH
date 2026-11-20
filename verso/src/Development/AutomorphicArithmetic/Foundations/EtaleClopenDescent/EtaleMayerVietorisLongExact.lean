import Mathlib
import Development.EtaleCohomology.EtaleSheaves.MayerVietorisSequence
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyLongExactFirstOfInjectiveStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ChosenInjectiveResolutionEtaleSheafPropertiesStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.HypercohomologyPullbackBiprodInlInrBijective

open CategoryTheory Limits CochainComplex CochainComplex.HomComplex GlobalTheory.EtC GlobalTheory.EtC.BiprodCls

namespace UpperTheory.Cb.EtaleMayerVietoris

variable {R : Type} [CommRing R]

/- English proof (translation)
Establish `hl : biprod.lift a (-b) = a ≫ biprod.inl + (-b) ≫ biprod.inr`. Apply the tactic sequence `apply biprod.hom_ext <;> simp`. Establish `h0 : ∀ {P Q : Cx R} (x : CohomologyClass Q I n), cpull (0 : P ⟶ Q) I n x = 0`. Introduce `P Q x`. Establish `h` using `cpull_add (0 : P ⟶ Q) 0 I n x`.

Rewrite `h` using `[add_zero]`. Simplify using `using h`. Establish `hn : ∀ {P Q : Cx R} (f : P ⟶ Q) (x : CohomologyClass Q I n), cpull (-f) I n x = -cpull f I n x`. Introduce `P Q f x`. Establish `h` using `cpull_add f (-f) I n x`.

Rewrite `h` using `[add_neg_cancel, h0]`. Conclude with `eq_neg_of_add_eq_zero_right h.symm`. Rewrite using `[hl, cpull_add, ← cpull_cpull, ← cpull_cpull, hn, sub_eq_add_neg]`.
-/
private theorem cpull_lift_neg {N K L : Cx R} (a : N ⟶ K) (b : N ⟶ L) (I : Cx R) (n : ℤ)
    (y : CohomologyClass (K ⊞ L) I n) :
    cpull (biprod.lift a (-b)) I n y =
      cpull a I n (cpull biprod.inl I n y) - cpull b I n (cpull biprod.inr I n y) := by
  have hl : biprod.lift a (-b) = a ≫ biprod.inl + (-b) ≫ biprod.inr := by
    apply biprod.hom_ext <;> simp
  have h0 : ∀ {P Q : Cx R} (x : CohomologyClass Q I n), cpull (0 : P ⟶ Q) I n x = 0 := by
    intro P Q x
    have h := cpull_add (0 : P ⟶ Q) 0 I n x
    rw [add_zero] at h
    simpa using h
  have hn : ∀ {P Q : Cx R} (f : P ⟶ Q) (x : CohomologyClass Q I n),
      cpull (-f) I n x = -cpull f I n x := by
    intro P Q f x
    have h := cpull_add f (-f) I n x
    rw [add_neg_cancel, h0] at h
    exact eq_neg_of_add_eq_zero_right h.symm
  rw [hl, cpull_add, ← cpull_cpull, ← cpull_cpull, hn, sub_eq_add_neg]

/- English proof (translation)
Rewrite using `[cpull_cpull, biprod.inl_desc]`.
-/
private theorem cpull_inl_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inl I n (cpull (biprod.desc c e) I n z) = cpull c I n z := by
  rw [cpull_cpull, biprod.inl_desc]

/- English proof (translation)
Rewrite using `[cpull_cpull, biprod.inr_desc]`.
-/
private theorem cpull_inr_desc {K L M : Cx R} (c : K ⟶ M) (e : L ⟶ M) (I : Cx R) (n : ℤ)
    (z : CohomologyClass M I n) :
    cpull biprod.inr I n (cpull (biprod.desc c e) I n z) = cpull e I n z := by
  rw [cpull_cpull, biprod.inr_desc]

end UpperTheory.Cb.EtaleMayerVietoris

set_option maxHeartbeats 800000 in
open UpperTheory.Cb.EtaleMayerVietoris in
/- English proof (translation)
Introduce `R _ F`. Take `⟨d0, hex, hnat⟩` from `GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1`. Use `⟨fun a b c e w hS n => d0 _ hS n, ?_, ?_⟩` and prove the remaining obligations. Introduce `N K L M a b c e w hS n`. Establish `hE` using `hex _ hS n`.

Take `⟨hinj, hsurj⟩` from `cpull_biprod_bijective R K L (res R F) n`. Establish `back : ∀ (z : CohomologyClass M (res R F) n) (u : CohomologyClass (K ⊞ L) (res R F) n), cpull biprod.inl (res R F) n u = cpull c (res R F) n z → cpull biprod.inr (res R F) n u = cpull e (res R F) n z → cpull (biprod.desc c e) (res R F) n z = u`. Introduce `z u h1 h2`. Use `hinj (Prod.ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cpull biprod.inl _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inl _ n u`.

Rewrite using `[cpull_inl_desc, h1]`. Express the relevant statement in the definitionally equal form `cpull biprod.inr _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inr _ n u`. Rewrite using `[cpull_inr_desc, h2]`. Use `⟨fun x y => ?_, fun t => ?_, fun z => ?_⟩` and prove the remaining obligations. Take `⟨u, hu⟩` from `hsurj (x, y)`.

Simplify using `only [Prod.mk.injEq] at hu`. Take `⟨hx, hy⟩` from `hu`. Establish `key : HK.pull R a F n x = HK.pull R b F n y ↔ cpull (biprod.lift a (-b)) (res R F) n u = 0`. Rewrite using `[cpull_lift_neg, hx, hy, sub_eq_zero]`. Both sides reduce to the same expression.

Use `key.trans ((hE.1 u).trans ?_)` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz⟩`. Establish `hz' : cpull (biprod.desc c e) (res R F) n z = u` using `hz`. Use `⟨z, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `cpull c (res R F) n z = x`. Rewrite using `[← hx, ← hz', cpull_inl_desc]`. Express the relevant statement in the definitionally equal form `cpull e (res R F) n z = y`. Rewrite using `[← hy, ← hz', cpull_inr_desc]`. Introduce and unpack `⟨z, hzx, hzy⟩`.

Conclude with `⟨z, back z u (hx.trans hzx.symm) (hy.trans hzy.symm)⟩`. Use `(hE.2.1 t).trans ?_` and prove the remaining obligations. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨u, hu⟩`. Establish `hu' : cpull (biprod.lift a (-b)) (res R F) n u = t` using `hu`.

Use `⟨cpull biprod.inl (res R F) n u, cpull biprod.inr (res R F) n u, ?_⟩` and prove the remaining obligations. Rewrite using `[← hu', cpull_lift_neg]`. Both sides reduce to the same expression. Introduce and unpack `⟨x, y, rfl⟩`. Take `⟨u, hu⟩` from `hsurj (x, y)`.

Simplify using `only [Prod.mk.injEq] at hu`. Take `⟨hx, hy⟩` from `hu`. Use `⟨u, ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cpull (biprod.lift a (-b)) (res R F) n u = _`. Rewrite using `[cpull_lift_neg, hx, hy]`.

Both sides reduce to the same expression. Take `⟨hinj1, -⟩` from `cpull_biprod_bijective R K L (res R F) (n + 1)`. Use `Iff.trans ?_ (hE.2.2 z)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `_ ↔ cpull (biprod.desc c e) (res R F) (n + 1) z = 0`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨h1, h2⟩`. Use `hinj1 (Prod.ext ?_ ?_)` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `cpull biprod.inl _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inl _ _ 0`. Rewrite using `[cpull_inl_desc, map_zero]`. Conclude with `h1`.

Express the relevant statement in the definitionally equal form `cpull biprod.inr _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inr _ _ 0`. Rewrite using `[cpull_inr_desc, map_zero]`. Conclude with `h2`. Introduce `h`. Prove the components needed by the constructor for the conclusion.

Express the relevant statement in the definitionally equal form `cpull c (res R F) (n + 1) z = 0`. Rewrite using `[← cpull_inl_desc c e, h, map_zero]`. Express the relevant statement in the definitionally equal form `cpull e (res R F) (n + 1) z = 0`. Rewrite using `[← cpull_inr_desc c e, h, map_zero]`. Introduce `N K L M N' K' L' M' a b c e a' b' c' e' w w' hS hS' φN φK φL φM h1 h2 h3 h4 n t`.

Set `φ : ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c e) w ⟶ ShortComplex.mk (biprod.lift a' (-b')) (biprod.desc c' e') w'` to `{ τ₁ := φN τ₂ := biprod.map φK φL τ₃ := φM comm₁₂ := by`. Apply the tactic sequence `apply biprod.hom_ext <;> simp [h1, h2]`. Use `comm₂₃ := by`. Apply the tactic sequence `apply biprod.hom_ext' <;> simp [h3, h4] }`. Conclude with `hnat _ _ hS hS' φ n t`.
-/
theorem UpperTheory.Cb.etale_mayer_vietoris_long_exact :
    LateralTheory.E.MayerVietorisSequence.LES := by
  intro R _ F
  obtain ⟨d0, hex, hnat⟩ := GlobalTheory.T.hypercohomology_longExact_first_of_injective R (res R F) (GlobalTheory.T.chosenInjectiveResolution_etaleSheaf_properties R F).2.1
  refine ⟨fun a b c e w hS n => d0 _ hS n, ?_, ?_⟩
  · intro N K L M a b c e w hS n
    have hE := hex _ hS n
    obtain ⟨hinj, hsurj⟩ := cpull_biprod_bijective R K L (res R F) n
    have back : ∀ (z : CohomologyClass M (res R F) n) (u : CohomologyClass (K ⊞ L) (res R F) n),
        cpull biprod.inl (res R F) n u = cpull c (res R F) n z →
        cpull biprod.inr (res R F) n u = cpull e (res R F) n z →
        cpull (biprod.desc c e) (res R F) n z = u := by
      intro z u h1 h2
      refine hinj (Prod.ext ?_ ?_)
      · change cpull biprod.inl _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inl _ n u
        rw [cpull_inl_desc, h1]
      · change cpull biprod.inr _ n (cpull (biprod.desc c e) _ n z) = cpull biprod.inr _ n u
        rw [cpull_inr_desc, h2]
    refine ⟨fun x y => ?_, fun t => ?_, fun z => ?_⟩
    · obtain ⟨u, hu⟩ := hsurj (x, y)
      simp only [Prod.mk.injEq] at hu
      obtain ⟨hx, hy⟩ := hu
      have key : HK.pull R a F n x = HK.pull R b F n y ↔
          cpull (biprod.lift a (-b)) (res R F) n u = 0 := by
        rw [cpull_lift_neg, hx, hy, sub_eq_zero]
        rfl
      refine key.trans ((hE.1 u).trans ?_)
      constructor
      · rintro ⟨z, hz⟩
        have hz' : cpull (biprod.desc c e) (res R F) n z = u := hz
        refine ⟨z, ?_, ?_⟩
        · change cpull c (res R F) n z = x
          rw [← hx, ← hz', cpull_inl_desc]
        · change cpull e (res R F) n z = y
          rw [← hy, ← hz', cpull_inr_desc]
      · rintro ⟨z, hzx, hzy⟩
        exact ⟨z, back z u (hx.trans hzx.symm) (hy.trans hzy.symm)⟩
    · refine (hE.2.1 t).trans ?_
      constructor
      · rintro ⟨u, hu⟩
        have hu' : cpull (biprod.lift a (-b)) (res R F) n u = t := hu
        refine ⟨cpull biprod.inl (res R F) n u, cpull biprod.inr (res R F) n u, ?_⟩
        rw [← hu', cpull_lift_neg]
        rfl
      · rintro ⟨x, y, rfl⟩
        obtain ⟨u, hu⟩ := hsurj (x, y)
        simp only [Prod.mk.injEq] at hu
        obtain ⟨hx, hy⟩ := hu
        refine ⟨u, ?_⟩
        change cpull (biprod.lift a (-b)) (res R F) n u = _
        rw [cpull_lift_neg, hx, hy]
        rfl
    · obtain ⟨hinj1, -⟩ := cpull_biprod_bijective R K L (res R F) (n + 1)
      refine Iff.trans ?_ (hE.2.2 z)
      change _ ↔ cpull (biprod.desc c e) (res R F) (n + 1) z = 0
      constructor
      · rintro ⟨h1, h2⟩
        refine hinj1 (Prod.ext ?_ ?_)
        · change cpull biprod.inl _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inl _ _ 0
          rw [cpull_inl_desc, map_zero]
          exact h1
        · change cpull biprod.inr _ _ (cpull (biprod.desc c e) _ _ z) = cpull biprod.inr _ _ 0
          rw [cpull_inr_desc, map_zero]
          exact h2
      · intro h
        constructor
        · change cpull c (res R F) (n + 1) z = 0
          rw [← cpull_inl_desc c e, h, map_zero]
        · change cpull e (res R F) (n + 1) z = 0
          rw [← cpull_inr_desc c e, h, map_zero]
  · intro N K L M N' K' L' M' a b c e a' b' c' e' w w' hS hS' φN φK φL φM h1 h2 h3 h4 n t
    let φ : ShortComplex.mk (biprod.lift a (-b)) (biprod.desc c e) w ⟶
        ShortComplex.mk (biprod.lift a' (-b')) (biprod.desc c' e') w' :=
      { τ₁ := φN
        τ₂ := biprod.map φK φL
        τ₃ := φM
        comm₁₂ := by
          apply biprod.hom_ext <;> simp [h1, h2]
        comm₂₃ := by
          apply biprod.hom_ext' <;> simp [h3, h4] }
    exact hnat _ _ hS hS' φ n t
