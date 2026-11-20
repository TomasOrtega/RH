import Mathlib
import Development.EtaleCohomology.EtaleSheaves.LineHigh
import Development.EtaleCohomology.EtaleSheaves.DescIntPf
import Development.AutomorphicArithmetic.CommutativeAlgebra.CohomologyBaseChangeIntegralSurjectiveCech

open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.DescIntPf

/- English proof (translation)
Introduce `hT hH q i A _ _ hq P p hyp`. Establish `neg : ∀ n : ℤ, n < 0 → ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)), RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))`. Introduce `n hn X g`. Use `⟨fun m hm => ?_, fun x y _ => ?_⟩` and prove the remaining obligations. Use `haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj (pullback g (LateralTheory.E.t_E2Cut.cpt A))) m (by omega)`.

Conclude with `fun y => ⟨0, Subsingleton.elim _ _⟩`. Use `haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj X) n hn`. Conclude with `Subsingleton.elim _ _`. Set `C : ℤ → Prop` to `fun n => ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)), (∃ h : X ⟶ P, IsIntegralHom h ∧ g = h ≫ p) → RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))`. Establish `step : ∀ n : ℤ, (∀ m, m < n → C m) → C n`.

Introduce `n ih X g hg`. Take `⟨h, hh, rfl⟩` from `hg`. Take `⟨Y, k, hk, hks, hpb⟩` from `hyp X h hh`. Use `haveI := hk`. Use `haveI := hks`.

Take `⟨U, E, u, a', a, hcomm, ha, ha', hall, h0⟩` from `UpperTheory.cohomology_base_change_integral_surjective_cech hH.b4 q i k (h ≫ p) (LateralTheory.E.t_E2Cut.cpt A) (LateralTheory.E.t_E2Cut.unit_of hq (h ≫ p))`. Establish `hu : RelZS (ZMod q) (tw q i) n u`. Use `hT (ZMod q) (tw q i) u n (fun p' m hm => ?_) ?_` and prove the remaining obligations. Take `⟨L, l, hl, hL⟩` from `hall p'`. Apply `hL m` to reduce the goal to its premises.

Use `haveI := hl`. Use `haveI := hh`. Conclude with `ih m hm (l ≫ h ≫ p) ⟨l ≫ h, inferInstance, by simp [Category.assoc]⟩`. Apply `h0 n` to reduce the goal to its premises. Conclude with `⟨fun m' _ => (hpb m').2, (hpb n).1⟩`.

Conclude with `transfer (ZMod q) (tw q i) u _ a' a hcomm ha ha' n hu`. Establish `all : ∀ n, C n`. Establish `key : ∀ k : ℕ, ∀ n : ℤ, n < k → C n`. Introduce `k`. Proceed by induction on `k with`.

Consider the case `zero`. Introduce `n hn X g _`. Conclude with `neg n (by exact_mod_cast hn) g`. Consider the case `succ k ihk`. Introduce `n hn`.

Distinguish the cases in `hn' : n < k`. Conclude with `ihk n hn'`. Conclude with `step n (fun m hm => ihk m (by push_cast at hn ⊢; omega))`. Introduce `n`. Conclude with `key (n.toNat + 1) n (by omega)`.

Establish `hp : ∃ h : P ⟶ P, IsIntegralHom h ∧ p = h ≫ p` using `⟨𝟙 P, inferInstance, by simp⟩`. Introduce `n`. Conclude with `⟨(all n p hp).2, (all (n + 1) p hp).1 n rfl⟩`.
-/
theorem UpperTheory.descent_of_integral_descent_truncation :
    LateralTheory.E.DescIntPf.EtaleRelativeIsoTruncationFromLevels → LateralTheory.E.t_E2Cut.Desc := by
  intro hT hH q i A _ _ hq P p hyp
  have neg : ∀ n : ℤ, n < 0 → ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A))) := by
    intro n hn X g
    refine ⟨fun m hm => ?_, fun x y _ => ?_⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1
        (sch.obj (pullback g (LateralTheory.E.t_E2Cut.cpt A))) m (by omega)
      exact fun y => ⟨0, Subsingleton.elim _ _⟩
    · haveI := (hH.a9 (ZMod q) (tw q i)).1 (sch.obj X) n hn
      exact Subsingleton.elim _ _
  let C : ℤ → Prop := fun n => ∀ {X : Scheme} (g : X ⟶ Spec (CommRingCat.of A)),
      (∃ h : X ⟶ P, IsIntegralHom h ∧ g = h ≫ p) →
      RelZS (ZMod q) (tw q i) n (sch.map (pullback.fst g (LateralTheory.E.t_E2Cut.cpt A)))
  have step : ∀ n : ℤ, (∀ m, m < n → C m) → C n := by
    intro n ih X g hg
    obtain ⟨h, hh, rfl⟩ := hg
    obtain ⟨Y, k, hk, hks, hpb⟩ := hyp X h hh
    haveI := hk
    haveI := hks
    obtain ⟨U, E, u, a', a, hcomm, ha, ha', hall, h0⟩ :=
      UpperTheory.cohomology_base_change_integral_surjective_cech hH.b4 q i k (h ≫ p) (LateralTheory.E.t_E2Cut.cpt A)
        (LateralTheory.E.t_E2Cut.unit_of hq (h ≫ p))
    have hu : RelZS (ZMod q) (tw q i) n u := by
      refine hT (ZMod q) (tw q i) u n (fun p' m hm => ?_) ?_
      · obtain ⟨L, l, hl, hL⟩ := hall p'
        apply hL m
        haveI := hl
        haveI := hh
        exact ih m hm (l ≫ h ≫ p) ⟨l ≫ h, inferInstance, by simp [Category.assoc]⟩
      · apply h0 n
        exact ⟨fun m' _ => (hpb m').2, (hpb n).1⟩
    exact transfer (ZMod q) (tw q i) u _ a' a hcomm ha ha' n hu
  have all : ∀ n, C n := by
    have key : ∀ k : ℕ, ∀ n : ℤ, n < k → C n := by
      intro k
      induction k with
      | zero =>
        intro n hn X g _
        exact neg n (by exact_mod_cast hn) g
      | succ k ihk =>
        intro n hn
        by_cases hn' : n < k
        · exact ihk n hn'
        · exact step n (fun m hm => ihk m (by push_cast at hn ⊢; omega))
    intro n
    exact key (n.toNat + 1) n (by omega)
  have hp : ∃ h : P ⟶ P, IsIntegralHom h ∧ p = h ≫ p := ⟨𝟙 P, inferInstance, by simp⟩
  intro n
  exact ⟨(all n p hp).2, (all (n + 1) p hp).1 n rfl⟩
