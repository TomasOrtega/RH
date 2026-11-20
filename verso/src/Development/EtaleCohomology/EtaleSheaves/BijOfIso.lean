import Development.EtaleCohomology.EtaleSheaves.PushColim
import Development.EtaleCohomology.EtaleSheaves.CokernelKilling.KillCokOf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E3Cut LateralTheory.E.StalkCut LateralTheory.E.DescLocPf
open LateralTheory.E.LeafGhostCut LateralTheory.E.KillCokPf.Asm

namespace LateralTheory.E.KernelLocalization

/- English proof (translation)
Establish `h1 : ∀ x, pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) = x` using `fun x => by`. Rewrite using `[← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]`. Establish `h2 : ∀ x, pull R (sch.map f) F n (pull R (sch.map (inv f)) F n x) = x` using `fun x => by`. Rewrite using `[← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]`. Conclude with `⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩`.
-/
theorem bij_of_iso (R : Type) [CommRing R] (F : Shv R) {X Y : Scheme.{0}} (f : X ⟶ Y) [IsIso f] (n : ℤ) :
    Function.Bijective (pull R (sch.map f) F n) := by
  have h1 : ∀ x, pull R (sch.map (inv f)) F n (pull R (sch.map f) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.inv_hom_id, CategoryTheory.Functor.map_id, pull_id]
  have h2 : ∀ x, pull R (sch.map f) F n (pull R (sch.map (inv f)) F n x) = x := fun x => by
    rw [← pull_comp, ← Functor.map_comp, IsIso.hom_inv_id, CategoryTheory.Functor.map_id, pull_id]
  exact ⟨Function.LeftInverse.injective h1, Function.RightInverse.surjective h2⟩

/- English proof (translation)
Use `(hC R F X n).comp (bij_of_iso R F (Sigma.desc π) n)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `x j`. Simplify using `only [Function.comp]`. Rewrite using `[← pull_comp, ← Functor.map_comp, Sigma.ι_desc]`.
-/
theorem cover_bij (hC : Coprod) (R : Type) [CommRing R] (F : Shv R) {ι : Type} {X : ι → Scheme.{0}} {S : Scheme.{0}}
    (π : ∀ j, X j ⟶ S) [IsIso (Sigma.desc π)] (n : ℤ) :
    Function.Bijective fun (x : H R (sch.obj S) F n) (j : ι) => pull R (sch.map (π j)) F n x := by
  have := (hC R F X n).comp (bij_of_iso R F (Sigma.desc π) n)
  convert this using 1
  funext x j
  simp only [Function.comp]
  rw [← pull_comp, ← Functor.map_comp, Sigma.ι_desc]

abbrev pr {ι : Type} (E : ι → CommRingCat.{0}) (j : ι) : CommRingCat.of (∀ k, E k) ⟶ E j :=
  CommRingCat.ofHom (Pi.evalRingHom (fun k => E k) j)

/- English proof (translation)
Establish `: IsIso (Sigma.desc fun j => Spec.map (pr E j))` using `inferInstanceAs (IsIso (sigmaSpec E))`. Conclude with `cover_bij hC _ _ _ n`.
-/
theorem pi_bij (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) :
    Function.Bijective fun x (j : ι) => PP q i n (pr E j) x := by
  have : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  exact cover_bij hC _ _ _ n

/- English proof (translation)
Establish `h0 : IsIso (Sigma.desc fun j => Spec.map (pr E j))` using `inferInstanceAs (IsIso (sigmaSpec E))`. Use `FinitaryPreExtensive.isIso_sigmaDesc_fst (fun j => Spec.map (pr E j)) (Spec.map ψ) h0` as an intermediate fact. Apply `(cover_bij hC (ZMod q) (tw q i) (fun j => pullback.fst (Spec.map ψ) (Spec.map (pr E j))) n).1` to reduce the goal to its premises. Use function extensionality and compare the values at `j`. Establish `hp` using `isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout ψ (pr E j))`.

Simplify using `only [map_zero]`. Rewrite using `[← hp.isoPullback_inv_fst, Functor.map_comp, pull_comp]`. Express the relevant statement in the definitionally equal form `pull _ _ _ _ (PP q i n _ y) = 0`. Rewrite using `[hy, map_zero]`.
-/
theorem push_inj (hC : Coprod) (q : ℕ) (i n : ℤ) {ι : Type} [Finite ι] (E : ι → CommRingCat.{0}) {Z : CommRingCat.{0}}
    (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (y : H (ZMod q) (sch.obj (Spec Z)) (tw q i) n)
    (hy : ∀ j, PP q i n (pushout.inl ψ (pr E j)) y = 0) : y = 0 := by
  have h0 : IsIso (Sigma.desc fun j => Spec.map (pr E j)) := inferInstanceAs (IsIso (sigmaSpec E))
  have := FinitaryPreExtensive.isIso_sigmaDesc_fst (fun j => Spec.map (pr E j)) (Spec.map ψ) h0
  apply (cover_bij hC (ZMod q) (tw q i) (fun j => pullback.fst (Spec.map ψ) (Spec.map (pr E j))) n).1
  funext j
  have hp := isPullback_SpecMap_of_isPushout _ _ _ _ (IsPushout.of_hasPushout ψ (pr E j))
  simp only [map_zero]
  rw [← hp.isoPullback_inv_fst, Functor.map_comp, pull_comp]
  change pull _ _ _ _ (PP q i n _ y) = 0
  rw [hy, map_zero]

/- English proof (translation)
Establish `hpr : ∀ j, piMap E e ≫ pr E j = e j` using `fun j => by ext a; rfl`. Establish `hw : ∀ j, φ ≫ u ≫ pushout.inl ψ (pr E j) = e j ≫ pushout.inr ψ (pr E j)` using `fun j => by`. Rewrite using `[h.w_assoc, pushout.condition, ← Category.assoc, hpr]`. Establish `hj : ∀ j, RP q i n ψ (pr E j) (pushout.inl ψ (pr E j)) (pushout.inr ψ (pr E j)) pushout.condition (RP q i n φ (piMap E e) u ψ h.w z) = 0` using `fun j => by`. Take `⟨Z', u', ψ', h', h0⟩` from `hz j`.

Rewrite using `[← RP_comp q i n φ _ u ψ h.w _ _ _ _ (e j) _ (hw j) (hpr j) rfl, RP_comp q i n φ (e j) u' ψ' h'.w (𝟙 _) (h'.desc _ _ (hw j)) _ (by simp) (e j) _ (hw j) (by simp) (by simp), h0, map_zero]`. Use `set z' := RP q i n φ (piMap E e) u ψ h.w z`. Establish `hm : 1 + (n - 1) = n` using `by omega`. Establish `hf : fgt _ _ _ n z' = 0`. Apply `(pi_bij hC q i n E).1` to reduce the goal to its premises.

Use function extensionality and compare the values at `j`. Simplify using `only [map_zero]`. Rewrite using `[← fgt_RP q i n ψ (pr E j) _ _ pushout.condition, hj, map_zero]`. Take `⟨y, hy⟩` from `exists_bd _ _ _ (n - 1) n hm z' hf`. Establish `hb : ∀ j, ∃ w, PP q i (n - 1) (pushout.inr ψ (pr E j)) w = PP q i (n - 1) (pushout.inl ψ (pr E j)) y` using `fun j => by`.

Use `range_of_bd _ _ _ (n - 1) n hm _ ?_` and prove the remaining obligations. Rewrite using `[← RP_bd q i (n - 1) n hm ψ (pr E j) _ _ pushout.condition, hy, hj]`. Use `choose w hw' using hb`. Take `⟨a, ha⟩` from `(pi_bij hC q i (n - 1) E).2 w`. Establish `hya : y - PP q i (n - 1) ψ a = 0` using `push_inj hC q i (n - 1) E ψ _ fun j => by`.

Rewrite using `[map_sub, ← PP_comp, pushout.condition, PP_comp, ← hw' j, ← congrFun ha j, sub_self]`. Rewrite using `[← hy, sub_eq_zero.1 hya]`. Conclude with `bd_pull ..`.
-/
theorem rel_pi (hC : Coprod) (q : ℕ) (i n : ℤ) {D Y : CommRingCat.{0}} (φ : D ⟶ Y) {ι : Type} [Finite ι]
    (E : ι → CommRingCat.{0}) (e : ∀ j, D ⟶ E j) (z : HR q i n φ)
    (hz : ∀ j, ∃ (Z : CommRingCat.{0}) (u : Y ⟶ Z) (ψ : E j ⟶ Z) (h : IsPushout φ (e j) u ψ), RP q i n φ (e j) u ψ h.w z = 0)
    {Z : CommRingCat.{0}} (u : Y ⟶ Z) (ψ : CommRingCat.of (∀ k, E k) ⟶ Z) (h : IsPushout φ (piMap E e) u ψ) :
    RP q i n φ (piMap E e) u ψ h.w z = 0 := by
  have hpr : ∀ j, piMap E e ≫ pr E j = e j := fun j => by ext a; rfl
  have hw : ∀ j, φ ≫ u ≫ pushout.inl ψ (pr E j) = e j ≫ pushout.inr ψ (pr E j) := fun j => by
    rw [h.w_assoc, pushout.condition, ← Category.assoc, hpr]
  have hj : ∀ j, RP q i n ψ (pr E j) (pushout.inl ψ (pr E j)) (pushout.inr ψ (pr E j)) pushout.condition
      (RP q i n φ (piMap E e) u ψ h.w z) = 0 := fun j => by
    obtain ⟨Z', u', ψ', h', h0⟩ := hz j
    rw [← RP_comp q i n φ _ u ψ h.w _ _ _ _ (e j) _ (hw j) (hpr j) rfl,
      RP_comp q i n φ (e j) u' ψ' h'.w (𝟙 _) (h'.desc _ _ (hw j)) _ (by simp) (e j) _ (hw j) (by simp) (by simp),
      h0, map_zero]
  set z' := RP q i n φ (piMap E e) u ψ h.w z
  have hm : 1 + (n - 1) = n := by omega
  have hf : fgt _ _ _ n z' = 0 := by
    apply (pi_bij hC q i n E).1
    funext j
    simp only [map_zero]
    rw [← fgt_RP q i n ψ (pr E j) _ _ pushout.condition, hj, map_zero]
  obtain ⟨y, hy⟩ := exists_bd _ _ _ (n - 1) n hm z' hf
  have hb : ∀ j, ∃ w, PP q i (n - 1) (pushout.inr ψ (pr E j)) w = PP q i (n - 1) (pushout.inl ψ (pr E j)) y := fun j => by
    refine range_of_bd _ _ _ (n - 1) n hm _ ?_
    rw [← RP_bd q i (n - 1) n hm ψ (pr E j) _ _ pushout.condition, hy, hj]
  choose w hw' using hb
  obtain ⟨a, ha⟩ := (pi_bij hC q i (n - 1) E).2 w
  have hya : y - PP q i (n - 1) ψ a = 0 := push_inj hC q i (n - 1) E ψ _ fun j => by
    rw [map_sub, ← PP_comp, pushout.condition, PP_comp, ← hw' j, ← congrFun ha j, sub_self]
  rw [← hy, sub_eq_zero.1 hya]
  exact bd_pull ..

/- English proof (translation)
Establish `h' : ∀ x : PrimeSpectrum D, ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧ x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧ ∃ (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ), RP q i n φ' e u ψ h.w z = 0`. Introduce `x`. Take `⟨O, o, Q, hIE, hQ, hQr, hBC⟩` from `hpts x.asIdeal x.isPrime`. Take `⟨E, e, s, Z, u, ψ, h, he, hes, h0⟩` from `relAt hB1 q i n φ' (unit_of d hq) o hIE (fun Z u ψ h => hBC Z (w ≫ u) ψ (hpo.paste_vert h)) z hz`. Use `⟨E, e, he, ⟨⟨Q.comap s.hom, inferInstance⟩, PrimeSpectrum.ext ?_⟩, Z, u, ψ, h, h0⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `(Q.comap s.hom).comap e.hom = _`. Rewrite using `[Ideal.comap_comap, ← CommRingCat.hom_comp, hes, hQr]`. Use `choose E e he hx hY using h'`. Take `⟨s, hs⟩` from `LateralTheory.E.KillCokPf.Lem.finite_subcover E e he hx`. Use `⟨_, piMap (fun k : s => E k.1) (fun k => e k.1), _, _, _, IsPushout.of_hasPushout _ _, LateralTheory.E.KillCokPf.Glue.et_pi _ _ (fun k => he k.1), sps_pi _ _ fun x => ?_, rel_pi hC q i n φ' _ _ z (fun k => hY k.1) _ _ (IsPushout.of_hasPushout _ _)⟩` and prove the remaining obligations.

Take `⟨r, hr, hxr⟩` from `hs x`. Conclude with `⟨⟨r, hr⟩, hxr⟩`.
-/
theorem relKill (hB1 : B1) (hC : Coprod) (q : ℕ) (i n : ℤ) {A Y D Y' : CommRingCat.{0}} (φ : A ⟶ Y) (hq : IsUnit (q : A))
    (d : A ⟶ D) (hpts : LocPts q i φ d) (w : Y ⟶ Y') (φ' : D ⟶ Y') (hpo : IsPushout φ d w φ') (z : HR q i n φ')
    (hz : PP q i n φ' (fgt _ _ _ n z) = 0) :
    ∃ (E : CommRingCat.{0}) (e : D ⟶ E) (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ),
      Et e ∧ SpS e ∧ RP q i n φ' e u ψ h.w z = 0 := by
  have h' : ∀ x : PrimeSpectrum D, ∃ (E : CommRingCat.{0}) (e : D ⟶ E), Et e ∧
      x ∈ Set.range (PrimeSpectrum.comap e.hom) ∧
      ∃ (Z : CommRingCat.{0}) (u : Y' ⟶ Z) (ψ : E ⟶ Z) (h : IsPushout φ' e u ψ), RP q i n φ' e u ψ h.w z = 0 := by
    intro x
    obtain ⟨O, o, Q, hIE, hQ, hQr, hBC⟩ := hpts x.asIdeal x.isPrime
    obtain ⟨E, e, s, Z, u, ψ, h, he, hes, h0⟩ := relAt hB1 q i n φ' (unit_of d hq) o hIE
      (fun Z u ψ h => hBC Z (w ≫ u) ψ (hpo.paste_vert h)) z hz
    refine ⟨E, e, he, ⟨⟨Q.comap s.hom, inferInstance⟩, PrimeSpectrum.ext ?_⟩, Z, u, ψ, h, h0⟩
    change (Q.comap s.hom).comap e.hom = _
    rw [Ideal.comap_comap, ← CommRingCat.hom_comp, hes, hQr]
  choose E e he hx hY using h'
  obtain ⟨s, hs⟩ := LateralTheory.E.KillCokPf.Lem.finite_subcover E e he hx
  refine ⟨_, piMap (fun k : s => E k.1) (fun k => e k.1), _, _, _, IsPushout.of_hasPushout _ _,
    LateralTheory.E.KillCokPf.Glue.et_pi _ _ (fun k => he k.1), sps_pi _ _ fun x => ?_,
    rel_pi hC q i n φ' _ _ z (fun k => hY k.1) _ _ (IsPushout.of_hasPushout _ _)⟩
  obtain ⟨r, hr, hxr⟩ := hs x
  exact ⟨⟨r, hr⟩, hxr⟩

end LateralTheory.E.KernelLocalization
