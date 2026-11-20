import Mathlib
import Development.WeilBound.CoreStatements.HodgeTatePoints.MhBase
open CategoryTheory Limits AlgebraicGeometry MonoidalCategory CartesianMonoidalCategory MonObj TensorProduct
open GlobalTheory.CompanionTheory.Ar.BT GroundTheory.PAdicHodge

noncomputable section

namespace PositivityTheory.HtPt.Mh

/- English proof (translation)
Introduce `R _ _ T _ _ Γ`. Use `exists_emb Γ _ fun a => ?_` and prove the remaining obligations. Simplify using `using (mem_top_iff Γ a.1).1 a.2 1`.
-/
theorem emb : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T), ∃! j : Γ.G.left ⟶ Spec (CommRingCat.of (Γ.btOrder ⊤)), Γ.IsEmb (Γ.btOrder ⊤) j := by
  intro R _ _ T _ _ Γ
  refine exists_emb Γ _ fun a => ?_
  simpa using (mem_top_iff Γ a.1).1 a.2 1

/- English proof (translation)
Introduce `R _ _ T _ _ Γ R' _ _ _ Γ' F hF A A' ψ hψ j j' hj hj'`. Take `⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩` from `hF.pts`. Use `hom_ext_pt Γ' fun t => ?_` and prove the remaining obligations. Establish `h1 : σ t ≫ j = Spec.map (CommRingCat.ofHom (i.comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom)))`. Take `⟨c, hc⟩` from `Spec.map_surjective (σ t ≫ j)`.

Establish `h2` using `hj.pt t`. Rewrite `h2` using `[← hσ t, Category.assoc, ← hc, ← CommRingCat.ofHom_hom c, spec_comp, ← hki]`. Rewrite using `[← hc, ← CommRingCat.ofHom_hom c]`. Use `congr 2`. Conclude with `RingHom.ext fun a => hk (RingHom.congr_fun (spec_inj h2) a)`.

Rewrite using `[← Category.assoc, ← hσ', Category.assoc, h1, spec_comp, ← Category.assoc, hj'.pt t, spec_comp, ← RingHom.comp_assoc, hki']`. Use `congr 2`. Conclude with `RingHom.ext fun a => congrArg (algebraMap R' (FractionRing R')) (hψ a t).symm`.
-/
theorem emb_square : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (R' : Type) [CommRing R'] [IsDomain R'] [Algebra R R'] (Γ' : QFGroup R' T) (F : Γ'.G.left ⟶ Γ.G.left), Γ'.IsBaseChange Γ (algebraMap R R') F → ∀ (A : Subalgebra R (T → R)) (A' : Subalgebra R' (T → R')) (ψ : A →+* A'), (∀ (a : A) t, (ψ a).1 t = algebraMap R R' (a.1 t)) → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)) (j' : Γ'.G.left ⟶ Spec (CommRingCat.of A')), Γ.IsEmb A j → Γ'.IsEmb A' j' → F ≫ j = j' ≫ Spec.map (CommRingCat.ofHom ψ) := by
  intro R _ _ T _ _ Γ R' _ _ _ Γ' F hF A A' ψ hψ j j' hj hj'
  obtain ⟨B, _, i, k, k', σ, hk, hki, hki', -, hσ, hσ'⟩ := hF.pts
  refine hom_ext_pt Γ' fun t => ?_
  have h1 : σ t ≫ j = Spec.map (CommRingCat.ofHom
      (i.comp ((Pi.evalRingHom (fun _ : T => R) t).comp A.val.toRingHom))) := by
    obtain ⟨c, hc⟩ := Spec.map_surjective (σ t ≫ j)
    have h2 := hj.pt t
    rw [← hσ t, Category.assoc, ← hc, ← CommRingCat.ofHom_hom c, spec_comp, ← hki] at h2
    rw [← hc, ← CommRingCat.ofHom_hom c]
    congr 2
    exact RingHom.ext fun a => hk (RingHom.congr_fun (spec_inj h2) a)
  rw [← Category.assoc, ← hσ', Category.assoc, h1, spec_comp, ← Category.assoc, hj'.pt t, spec_comp,
    ← RingHom.comp_assoc, hki']
  congr 2
  exact RingHom.ext fun a => congrArg (algebraMap R' (FractionRing R')) (hψ a t).symm

/- English proof (translation)
Simplify using `only [valAt, Scheme.Hom.comp_appLE]`. Both sides reduce to the same expression.
-/
theorem valAt_comp {B : Type} [CommRing B] {X Y : Scheme.{0}} (x : Spec (CommRingCat.of B) ⟶ Y) (F : Y ⟶ X)
    (U : X.Opens) (h : ⊤ ≤ (x ≫ F) ⁻¹ᵁ U) (s : Γ(X, U)) :
    valAt (x ≫ F) U h s = valAt x (F ⁻¹ᵁ U) h ((F.app U).hom s) := by
  simp only [valAt, Scheme.Hom.comp_appLE]
  rfl

/- English proof (translation)
Establish `hY` using `isAffineOpen_top (Spec (CommRingCat.of A))`. Take `⟨r, hr, hg⟩` from `hY.exists_basicOpen_le (V := j.opensRange) ⟨j g, g, rfl⟩ trivial`. Set `D` to `(Spec (CommRingCat.of A)).basicOpen r`. Use `j.isIso_app D hr` as an intermediate fact. Take `⟨s', hs'⟩` from `(ConcreteCategory.bijective_of_isIso (j.app D)).2 ((X.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)).op).hom s)`.

Establish `hl` using `hY.isLocalization_basicOpen r`. Take `⟨⟨a, _, n, rfl⟩, ha⟩` from `IsLocalization.surj (Submonoid.powers r) s'`. Set `c` to `(Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom`. Establish `hc : ∀ b, pb j (c b) = j.appTop b` using `fun b => by simp [pb, c]`. Use `⟨c (r ^ (n + 1)), c (r * a), ?_, fun K _ x => ?_⟩` and prove the remaining obligations.

Rewrite using `[map_pow]`. Introduce `h`. Establish `h1` using `(j g).isPrime.mem_of_pow_mem _ h`. Establish `h2 : j g ∈ (Spec (CommRingCat.of A)).basicOpen r` using `hg`. Rewrite `h2` using `[basicOpen_eq_of_affine']`.

Conclude with `h2 h1`. Rewrite using `[hc, hc, ← val_comp, ← val_comp, map_pow, map_mul, pow_succ']`. Distinguish the cases in `h0 : val (x ≫ j) r = 0`. Simplify using `[h0]`. Establish `hx : ⊤ ≤ (x ≫ j) ⁻¹ᵁ D`.

Rewrite using `[Scheme.preimage_basicOpen_top, top_le_iff]`. Apply `Scheme.basicOpen_of_isUnit` to reduce the goal to its premises. Establish `hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((x ≫ j).appTop r))` using `Ne.isUnit h0`. Simplify using `using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Establish `e` using `congrArg (SubOrder.valHom (x ≫ j) D hx) ha`.

Establish `hres : ∀ b, SubOrder.valHom (x ≫ j) D hx (algebraMap Γ(Spec (CommRingCat.of A), ⊤) _ b) = val (x ≫ j) b` using `fun b => (Twhopf.valAt_restrict (x ≫ j) (homOfLE (le_top : D ≤ ⊤)) hx le_top b).trans (valAt_top _ _ _)`. Rewrite `e` using `[map_mul, hres, hres, SubOrder.valHom_apply, valAt_comp]`. Establish `e2 : valAt x (j ⁻¹ᵁ D) hx ((j.app D).hom s') = val x s` using `(congrArg (valAt x (j ⁻¹ᵁ D) hx) hs').trans ((Twhopf.valAt_restrict x (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)) hx le_top s).trans (valAt_top _ _ _))`. Rewrite `e` using `[e2, map_pow]`. Rewrite using `[← e]`.

Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_den_of_open {A : Type} [CommRing A] {X : Scheme.{0}} (j : X ⟶ Spec (CommRingCat.of A))
    [IsOpenImmersion j] (g : X) (s : Γ(X, ⊤)) :
    ∃ u a : A, u ∉ (j g).asIdeal ∧ ∀ (K : Type) [Field K] (x : Spec (CommRingCat.of K) ⟶ X),
      val x (pb j u) * val x s = val x (pb j a) := by
  have hY := isAffineOpen_top (Spec (CommRingCat.of A))
  obtain ⟨r, hr, hg⟩ := hY.exists_basicOpen_le (V := j.opensRange) ⟨j g, g, rfl⟩ trivial
  let D := (Spec (CommRingCat.of A)).basicOpen r
  have := j.isIso_app D hr
  obtain ⟨s', hs'⟩ := (ConcreteCategory.bijective_of_isIso (j.app D)).2
    ((X.presheaf.map (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)).op).hom s)
  have hl := hY.isLocalization_basicOpen r
  obtain ⟨⟨a, _, n, rfl⟩, ha⟩ := IsLocalization.surj (Submonoid.powers r) s'
  let c := (Scheme.ΓSpecIso (CommRingCat.of A)).hom.hom
  have hc : ∀ b, pb j (c b) = j.appTop b := fun b => by simp [pb, c]
  refine ⟨c (r ^ (n + 1)), c (r * a), ?_, fun K _ x => ?_⟩
  · rw [map_pow]
    intro h
    have h1 := (j g).isPrime.mem_of_pow_mem _ h
    have h2 : j g ∈ (Spec (CommRingCat.of A)).basicOpen r := hg
    rw [basicOpen_eq_of_affine'] at h2
    exact h2 h1
  · rw [hc, hc, ← val_comp, ← val_comp, map_pow, map_mul, pow_succ']
    by_cases h0 : val (x ≫ j) r = 0
    · simp [h0]
    have hx : ⊤ ≤ (x ≫ j) ⁻¹ᵁ D := by
      rw [Scheme.preimage_basicOpen_top, top_le_iff]
      apply Scheme.basicOpen_of_isUnit
      have hu : IsUnit ((Scheme.ΓSpecIso (CommRingCat.of K)).hom.hom ((x ≫ j).appTop r)) := Ne.isUnit h0
      simpa using hu.map (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
    have e := congrArg (SubOrder.valHom (x ≫ j) D hx) ha
    have hres : ∀ b, SubOrder.valHom (x ≫ j) D hx (algebraMap Γ(Spec (CommRingCat.of A), ⊤) _ b) = val (x ≫ j) b :=
      fun b => (Twhopf.valAt_restrict (x ≫ j) (homOfLE (le_top : D ≤ ⊤)) hx le_top b).trans (valAt_top _ _ _)
    rw [map_mul, hres, hres, SubOrder.valHom_apply, valAt_comp] at e
    have e2 : valAt x (j ⁻¹ᵁ D) hx ((j.app D).hom s') = val x s :=
      (congrArg (valAt x (j ⁻¹ᵁ D) hx) hs').trans
        ((Twhopf.valAt_restrict x (homOfLE (le_top : j ⁻¹ᵁ D ≤ ⊤)) hx le_top s).trans (valAt_top _ _ _))
    rw [e2, map_pow] at e
    rw [← e]
    ring

/- English proof (translation)
Introduce `R _ _ T _ _ Γ A hA j hj hopen hcov`. Establish `tr` using `Twhopf.translate_mem R T A hA`. Apply `le_antisymm` to reduce the goal to its premises. Introduce `f hf`. Rewrite `hf` using `[mem_top_iff]`.

Set `I : Ideal A` to `{ carrier := {a | a.1 * f ∈ A} add_mem' := fun {a b} ha hb => by`. Express the relevant statement in the definitionally equal form `(a.1 + b.1) * f ∈ A`. Rewrite using `[add_mul]`. Conclude with `A.add_mem ha hb`. Use the proof step `zero_mem' := by`.

Express the relevant statement in the definitionally equal form `(0 : T → R) * f ∈ A`. Rewrite using `[zero_mul]`. Conclude with `A.zero_mem`. Use the proof step `smul_mem' := fun c a ha => by`. Express the relevant statement in the definitionally equal form `(c.1 * a.1) * f ∈ A`.

Rewrite using `[_root_.mul_assoc]`. Conclude with `A.mul_mem c.2 ha }`. Establish `hI : I = ⊤`. Assume the negation of the conclusion as `hne`. Take `⟨P, hP, hIP⟩` from `Ideal.exists_le_maximal I hne`.

Take `⟨t, g, -, hg⟩` from `hcov ⟨P, hP.isPrime⟩`. Take `⟨s, hs⟩` from `hf t`. Take `⟨u, a, hu, hua⟩` from `exists_den_of_open j g s`. Establish `h1 : ∀ h, u.1 h * f (t * h) = a.1 h` using `fun h => by`. Use `hua _ (Γ.pt h).left` as an intermediate fact.

Rewrite `this` using `[val_emb hj, val_emb hj, hs, ← map_mul]`. Conclude with `IsFractionRing.injective R (FractionRing R) this`. Set `u' : A` to `⟨_, tr _ u.2 t⁻¹⟩`. Use `hu ((hg u' u fun h => by simp [u']).1 (hIP ?_))` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `u'.1 * f ∈ A`.

Use `tr _ a.2 t⁻¹ using 1` and compare the differences between its conclusion and the goal. Use function extensionality and compare the values at `h`. Rewrite using `[← h1]`. Simplify using `[u']`. Establish `h1 : (1 : A) ∈ I` using `hI ▸ Submodule.mem_top`.

Establish `h2 : (1 : T → R) * f ∈ A` using `h1`. Rewrite `h2` using `[_root_.one_mul]`. Then use the resulting hypothesis. Introduce `f hf`. Rewrite using `[mem_top_iff]`. Conclude with `fun t => ⟨pb j ⟨_, tr f hf t⟩, fun h => val_emb hj h _⟩`.
-/
theorem char : ∀ (R : Type) [CommRing R] [IsDomain R] (T : Type) [CommGroup T] [Finite T] (Γ : QFGroup R T) (A : Subalgebra R (T → R)), IsHopfOrder A → ∀ (j : Γ.G.left ⟶ Spec (CommRingCat.of A)), Γ.IsEmb A j → IsOpenImmersion j → Γ.TranslatesCover A j ⊤ → Γ.btOrder ⊤ = A := by
  intro R _ _ T _ _ Γ A hA j hj hopen hcov
  have tr := Twhopf.translate_mem R T A hA
  apply le_antisymm
  · intro f hf
    rw [mem_top_iff] at hf
    let I : Ideal A :=
      { carrier := {a | a.1 * f ∈ A}
        add_mem' := fun {a b} ha hb => by
          change (a.1 + b.1) * f ∈ A
          rw [add_mul]
          exact A.add_mem ha hb
        zero_mem' := by
          change (0 : T → R) * f ∈ A
          rw [zero_mul]
          exact A.zero_mem
        smul_mem' := fun c a ha => by
          change (c.1 * a.1) * f ∈ A
          rw [_root_.mul_assoc]
          exact A.mul_mem c.2 ha }
    have hI : I = ⊤ := by
      by_contra hne
      obtain ⟨P, hP, hIP⟩ := Ideal.exists_le_maximal I hne
      obtain ⟨t, g, -, hg⟩ := hcov ⟨P, hP.isPrime⟩
      obtain ⟨s, hs⟩ := hf t
      obtain ⟨u, a, hu, hua⟩ := exists_den_of_open j g s
      have h1 : ∀ h, u.1 h * f (t * h) = a.1 h := fun h => by
        have := hua _ (Γ.pt h).left
        rw [val_emb hj, val_emb hj, hs, ← map_mul] at this
        exact IsFractionRing.injective R (FractionRing R) this
      let u' : A := ⟨_, tr _ u.2 t⁻¹⟩
      refine hu ((hg u' u fun h => by simp [u']).1 (hIP ?_))
      change u'.1 * f ∈ A
      convert tr _ a.2 t⁻¹ using 1
      funext h
      rw [← h1]
      simp [u']
    have h1 : (1 : A) ∈ I := hI ▸ Submodule.mem_top
    have h2 : (1 : T → R) * f ∈ A := h1
    rwa [_root_.one_mul] at h2
  · intro f hf
    rw [mem_top_iff]
    exact fun t => ⟨pb j ⟨_, tr f hf t⟩, fun h => val_emb hj h _⟩

end PositivityTheory.HtPt.Mh
