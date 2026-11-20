import Mathlib
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.PerfectoidPullbacks.LocalisationLadders.CriterionTruncation
import Development.WeilBound.CoreStatements.PadicHodgeComparison.EtaleCohomologyComparison.CechPairings.FaceMapCompSuccAboveCastSucc

set_option backward.isDefEq.respectTransparency false
set_option autoImplicit false

noncomputable section

open CategoryTheory CrystallineSemistableComparison CrystallineSemistableComparison.Pb

namespace GlobalTheory.CompanionTheory.LocGr

/- English proof (translation)
Establish `key : ∀ c : CH.H F (n + 1), c = 0`. Introduce `c`. Take `⟨⟨f, hf⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨g, hg⟩` from `(CrystallineSemistableComparison.P.initial F T₀ h).2.2.2 n f hf`. Use `(Submodule.Quotient.mk_eq_zero _).2 ?_` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `f ∈ (CH.cx F).B (n + 1)`. Conclude with `⟨g, hg.trans (one_smul R f)⟩`. Conclude with `⟨fun a b => by rw [key a, key b]⟩`.
-/
theorem H_succ_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] (F : C ⥤ ModuleCat.{0} R) {T₀ : C}
    (h : Limits.IsInitial T₀) (n : ℕ) : Subsingleton (CH.H F (n + 1)) := by
  have key : ∀ c : CH.H F (n + 1), c = 0 := by
    intro c
    obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
    obtain ⟨g, hg⟩ := (CrystallineSemistableComparison.P.initial F T₀ h).2.2.2 n f hf
    refine (Submodule.Quotient.mk_eq_zero _).2 ?_
    change f ∈ (CH.cx F).B (n + 1)
    exact ⟨g, hg.trans (one_smul R f)⟩
  exact ⟨fun a b => by rw [key a, key b]⟩

/- English proof (translation)
Establish `hT : ∀ T, Subsingleton ((gr Fil r).obj T)` using `fun T => by`. Establish `h1 : (Fil (r + 1)).S T = ⊤` using `hF.top _ (by omega) T`. Establish `h2 : Subsingleton (Φ.A.obj T ⧸ (Fil (r + 1)).S T)` using `Ideal.Quotient.subsingleton_iff.2 h1`. Conclude with `⟨fun a b => Subtype.ext (Subsingleton.elim (α := Φ.A.obj T ⧸ (Fil (r + 1)).S T) _ _)⟩`. Establish `hC : Subsingleton (CH.Cn (gr Fil r) 0)` using `⟨fun a b => funext fun s => (hT _).elim _ _⟩`.

Use `⟨fun a b => ?_⟩` and prove the remaining obligations. Take `⟨⟨f, hf⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ a`. Take `⟨⟨g, hg⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ b`. Establish `e : f = g` using `hC.elim f g`. Substitute `e` using the available equality.

Both sides reduce to the same expression.
-/
theorem H_zero_subsingleton {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) {r : ℤ} (hr : r < 0) : Subsingleton (CH.H (gr Fil r) 0) := by
  have hT : ∀ T, Subsingleton ((gr Fil r).obj T) := fun T => by
    have h1 : (Fil (r + 1)).S T = ⊤ := hF.top _ (by omega) T
    have h2 : Subsingleton (Φ.A.obj T ⧸ (Fil (r + 1)).S T) := Ideal.Quotient.subsingleton_iff.2 h1
    exact ⟨fun a b => Subtype.ext (Subsingleton.elim (α := Φ.A.obj T ⧸ (Fil (r + 1)).S T) _ _)⟩
  have hC : Subsingleton (CH.Cn (gr Fil r) 0) := ⟨fun a b => funext fun s => (hT _).elim _ _⟩
  refine ⟨fun a b => ?_⟩
  obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ a
  obtain ⟨⟨g, hg⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ b
  have e : f = g := hC.elim f g
  subst e
  rfl

/- English proof (translation)
Introduce `R _ C _ Φ Fil hF E σ r j`. Establish `hI : Limits.IsInitial E.D` using `E.initial`. Use `⟨fun hr => ?_, fun q hq => ?_⟩` and prove the remaining obligations. Consider the cases of `j with`. Consider the case `zero => exact H_zero_subsingleton hF (by simpa using hr)`.

Consider the case `succ n => exact H_succ_subsingleton _ hI n`. Consider the cases of `j with`. Consider the case `succ n`. Establish `hs` using `H_succ_subsingleton (gr Fil r) hI n`. Use `haveI : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩`.

Use `⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩, fun x _ _ I => isEmptyElim I⟩` and prove the remaining obligations. Unfold `CrystallineSemistableComparison.Pb.Rep`. Use `⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩` and prove the remaining obligations. Establish `e` using `Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)`. Use `Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm` and prove the remaining obligations.

Conclude with `(map_zero _).symm`. Consider the case `zero`. Establish `hq' : r = q` using `by simpa using hq`. Substitute `hq'` using the available equality. Use `haveI : Unique (Idx 0 0) := ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩`.

Establish `hform : ∀ (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0), ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default)`. Introduce `x s`. Rewrite using `[Fintype.sum_unique]`. Simplify using `[Frame.form]`. Use `⟨fun c => ?_, fun x hx hrep I => ?_⟩` and prove the remaining obligations.

Take `⟨⟨f, hf⟩, rfl⟩` from `Submodule.Quotient.mk_surjective _ c`. Take `⟨m, hm⟩` from `(CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf`. Take `⟨m', hm'⟩` from `m`. Take `⟨y, hy, rfl⟩` from `(Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'`. Use `⟨fun _ => y, fun _ => hy, ?_⟩` and prove the remaining obligations.

Unfold `CrystallineSemistableComparison.Pb.Rep`. Use `⟨f, hf, rfl, fun s => ?_⟩` and prove the remaining obligations. Use `Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm` and prove the remaining obligations. Establish `h1` using `congrFun (hm.trans (one_smul R f)) s`. Establish `h2` using `congrArg Subtype.val h1`.

Rewrite using `[show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]`. Conclude with `h2.symm`. Unfold `CrystallineSemistableComparison.Pb.Rep at hrep`. Take `⟨f, hf, h0, hs⟩` from `hrep`. Establish `hf0 : f = 0`.

Establish `h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈ ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0)` using `(Submodule.Quotient.mk_eq_zero _).1 h0.symm`. Conclude with `(Submodule.mem_bot R).1 h3`. Substitute `hf0` using the available equality. Establish `h1` using `(hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))`. Establish `hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D` using `hI.hom_ext _ _`.

Rewrite `h1` using `[hσ]`. Establish `h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default`. Rewrite using `[Φ.A.map_id]`. Both sides reduce to the same expression. Establish `h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0`.

Rewrite using `[← h4]`. Conclude with `h1.symm`. Rewrite using `[Subsingleton.elim I default]`. Conclude with `Ideal.Quotient.eq_zero_iff_mem.1 h5`.
-/
theorem gr_zero : ∀ {R : Type} [CommRing R] {C : Type 1} [Category.{0} C] {Φ : PDF R C} {Fil : ℤ → IdF Φ.A}
    (hF : IsFil Φ Fil) (E : Frame Φ 0) (σ : ∀ T : C, E.D ⟶ T) (r : ℤ) (j : ℕ),
    (r < j → Subsingleton (CH.H (gr Fil r) j)) ∧
    ∀ q : ℕ, r = j + q →
      (∀ c : CH.H (gr Fil r) j, ∃ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) ∧
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) c) ∧
      ∀ x : Idx j 0 → Φ.A.obj E.D, (∀ I, x I ∈ (Fil q).S E.D) →
        Rep (Fil r) (Fil (r + 1)) (fun s => ∑ I : Idx j 0, E.form σ I.1 (x I) s) 0 → ∀ I, x I ∈ (Fil ((q : ℤ) + 1)).S E.D := by
  intro R _ C _ Φ Fil hF E σ r j
  have hI : Limits.IsInitial E.D := E.initial
  refine ⟨fun hr => ?_, fun q hq => ?_⟩
  · cases j with
    | zero => exact H_zero_subsingleton hF (by simpa using hr)
    | succ n => exact H_succ_subsingleton _ hI n
  · cases j with
    | succ n =>
      have hs := H_succ_subsingleton (gr Fil r) hI n
      haveI : IsEmpty (Idx (n + 1) 0) := ⟨fun I => (I.1 0).elim0⟩
      refine ⟨fun c => ⟨fun I => isEmptyElim I, fun I => isEmptyElim I, ?_⟩, fun x _ _ I => isEmptyElim I⟩
      unfold CrystallineSemistableComparison.Pb.Rep
      refine ⟨0, map_zero _, Subsingleton.elim _ _, fun s => ?_⟩
      have e := Fintype.sum_empty (fun I : Idx (n + 1) 0 => E.form σ I.1 (isEmptyElim I) s)
      refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) e).symm
      exact (map_zero _).symm
    | zero =>
      have hq' : r = q := by simpa using hq
      subst hq'
      haveI : Unique (Idx 0 0) := ⟨⟨⟨Fin.elim0, fun a => a.elim0⟩⟩, fun I => Subtype.ext (funext fun a => a.elim0)⟩
      have hform : ∀ (x : Idx 0 0 → Φ.A.obj E.D) (s : ComposableArrows C 0),
          ∑ I : Idx 0 0, E.form σ I.1 (x I) s = (Φ.A.map (σ _)).hom (x default) := by
        intro x s
        rw [Fintype.sum_unique]
        simp [Frame.form]
      refine ⟨fun c => ?_, fun x hx hrep I => ?_⟩
      · obtain ⟨⟨f, hf⟩, rfl⟩ := Submodule.Quotient.mk_surjective _ c
        obtain ⟨m, hm⟩ := (CrystallineSemistableComparison.P.initial (gr Fil (q : ℤ)) E.D hI).2.2.1 f hf
        obtain ⟨m', hm'⟩ := m
        obtain ⟨y, hy, rfl⟩ := (Ideal.mem_map_iff_of_surjective _ Ideal.Quotient.mk_surjective).1 hm'
        refine ⟨fun _ => y, fun _ => hy, ?_⟩
        unfold CrystallineSemistableComparison.Pb.Rep
        refine ⟨f, hf, rfl, fun s => ?_⟩
        refine Eq.trans ?_ (congrArg (Ideal.Quotient.mk _) (hform (fun _ => y) s)).symm
        have h1 := congrFun (hm.trans (one_smul R f)) s
        have h2 := congrArg Subtype.val h1
        rw [show σ (s.obj (Fin.last 0)) = hI.to _ from hI.hom_ext _ _]
        exact h2.symm
      · unfold CrystallineSemistableComparison.Pb.Rep at hrep
        obtain ⟨f, hf, h0, hs⟩ := hrep
        have hf0 : f = 0 := by
          have h3 : (⟨f, hf⟩ : (CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) ∈
              ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).B 0).submoduleOf ((CH.cx (sq (Fil (q : ℤ)) (Fil ((q : ℤ) + 1)))).Z 0) :=
            (Submodule.Quotient.mk_eq_zero _).1 h0.symm
          exact (Submodule.mem_bot R).1 h3
        subst hf0
        have h1 := (hs (ComposableArrows.mk₀ E.D)).trans (congrArg (Ideal.Quotient.mk _) (hform x _))
        have hσ : σ ((ComposableArrows.mk₀ E.D).obj (Fin.last 0)) = 𝟙 E.D := hI.hom_ext _ _
        rw [hσ] at h1
        have h4 : (Φ.A.map (𝟙 E.D)).hom (x default) = x default := by
          rw [Φ.A.map_id]; rfl
        have h5 : Ideal.Quotient.mk ((Fil ((q : ℤ) + 1)).S E.D) (x default) = 0 := by
          rw [← h4]
          exact h1.symm
        rw [Subsingleton.elim I default]
        exact Ideal.Quotient.eq_zero_iff_mem.1 h5

end GlobalTheory.CompanionTheory.LocGr
