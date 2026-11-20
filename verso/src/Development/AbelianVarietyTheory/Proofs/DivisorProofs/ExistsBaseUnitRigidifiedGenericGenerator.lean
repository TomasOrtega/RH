import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.ValCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.SemiabelianSchemes.PrecompleteBases.PsbLb

open AlgebraicGeometry CategoryTheory Limits
open ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor

namespace GlobalTheory

/- English proof (translation)
Take `⟨w, hw⟩` from `glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top) (fun y _ => by`. Take `⟨i, hi⟩` from `exists_chart hM (f y)`. Conclude with `TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)`. Use the proof step `(fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by`. Establish `h1` using `gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2`.

Establish `h2` using `gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2`. Use `((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)` and prove the remaining obligations. Rewrite using `[mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]`. Use the proof step `rfl)`. Use `⟨w, fun Z r z j hj => ?_⟩` and prove the remaining obligations.

Establish `e` using `(gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))`. Rewrite using `[e, map_mul, map_inv, inv_mul_cancel_right]`.
-/
theorem rigUnit_exists_ratio {X Y : Scheme.{0}} (M : LB X) (hM : M.IsLB) (f : Y ⟶ X)
    (t t' : LB.Gen (M.pull f)) (ht : t.IsGen) (ht' : t'.IsGen) :
    ∃ w : Γ(Y, ⊤)ˣ, ∀ (Z : Scheme.{0}) (r : Z ⟶ Y) (z : Z) (j : PUnit → M.ι), r z ∈ (M.pull f).U j →
      gm r z ((M.pull f).U j) (t.s j) = gm r z ⊤ w * gm r z ((M.pull f).U j) (t'.s j) := by
  obtain ⟨w, hw⟩ := glue_unit (X := Y) ⊤ (fun j : PUnit → M.ι => (M.pull f).U j) (fun _ => le_top)
    (fun y _ => by
      obtain ⟨i, hi⟩ := exists_chart hM (f y)
      exact TopologicalSpace.Opens.mem_iSup.2 ⟨fun _ => i, mem_pull.2 hi⟩)
    (fun j => t.s j * (t'.s j)⁻¹) (fun i j x hx => by
      have h1 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      have h2 := gen_trans (L := M) (φ := fun _ : PUnit => f) (ε := fun _ => 1) ht' (𝟙 Y) x (j := i) (j' := j) hx.1 hx.2
      refine ((map_mul _ _ _).trans (congrArg₂ (· * ·) h1 ((map_inv _ _).trans (congrArg (·⁻¹) h2)))).trans
        (Eq.trans ?_ ((map_mul _ _ _).trans (congrArg₂ (· * ·) rfl (map_inv _ _))).symm)
      rw [mul_inv, mul_mul_mul_comm, mul_inv_cancel, one_mul]
      rfl)
  refine ⟨w, fun Z r z j hj => ?_⟩
  have e := (gm_res r z (le_top : (M.pull f).U j ≤ ⊤) hj w).symm.trans (congrArg (gm r z _) (hw j))
  rw [e, map_mul, map_inv, inv_mul_cancel_right]

/- English proof (translation)
Introduce `R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H`. Take `⟨w, hw⟩` from `rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig`. Use `haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by`. Use `IsLocalization.epi (nonZeroDivisors R) K` as an intermediate fact. Conclude with `this`.

Use `haveI : Mono (spMap (algebraMap R K)) := by`. Conclude with `inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))`. Establish `hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _`. Rewrite using `[← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA, Category.assoc, he, Category.comp_id, Category.id_comp]`. Set `z : Sp K` to `(⊥ : PrimeSpectrum K)`.

Use `choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)`. Establish `hG : Good M z J` using `hJ`. Establish `hv` using `val_corr hG hcorr (𝟙 _)`. Rewrite `hv` using `[val_pull hG, val_pull hG, Category.id_comp, Category.id_comp, val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]), val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)]`. Establish `hi` using `hJ (spMap (algebraMap R K) ≫ e)`.

Generalize the expression as in `J (spMap (algebraMap R K) ≫ e) = i at hv hi`. Establish `h1` using `H i _ eA z (by`. Establish `: (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i` using `by rw [heA]; exact hi`. Conclude with `this)`. Rewrite `h1` using `[heA, hsnd]`.

Establish `hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i)` using `mem_pull.2 hi`. Establish `h2` using `hw _ (spMap (algebraMap R K)) z (fun _ => i) hm`. Establish `h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) = gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i)` using `(gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)`. Establish `h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val = gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K))`. Establish `h5` using `(congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))`.

Rewrite `h5` using `[Units.val_mul]`. Conclude with `(Units.mul_left_inj _).1 h5`. Use `⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩` and prove the remaining obligations. Set `φ : K →+* (Sp K).presheaf.stalk z` to `((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom`. Apply `φ.injective` to reduce the goal to its premises.

Rewrite `h4` using `[gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial]`. Use `Eq.trans ?_ h4` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _`. Use `congr 1`. Establish `n` using `congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val)) (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))`.

Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n`. Conclude with `n`.
-/
theorem rigUnit_exists : ∀ (R K : Type) [CommRing R] [IsDomain R] [Field K] [Algebra R K] [IsFractionRing R K] (X : Over (Sp R)) (e : Sp R ⟶ X.left), e ≫ X.hom = 𝟙 _ → ∀ (eA : Sp K ⟶ pullback X.hom (spMap (algebraMap R K))), eA ≫ pullback.fst X.hom (spMap (algebraMap R K)) = spMap (algebraMap R K) ≫ e → ∀ (M : LB X.left) (rig : LB.Gen (M.pull e)) (c : LB.Gen (M.pull (pullback.fst X.hom (spMap (algebraMap R K))))), M.IsLB → rig.IsGen → LB.Gen.Corr M _ _ _ _ (LB.pullGen M _ _ c eA) (LB.pullGen M _ _ rig (spMap (algebraMap R K))) → ∀ (a : Kˣ) (u : LB.Gen M), u.IsGen → (∀ (i : M.ι) (Z : Scheme.{0}) (r : Z ⟶ pullback X.hom (spMap (algebraMap R K))) (z : Z), pullback.fst X.hom (spMap (algebraMap R K)) (r z) ∈ M.U i → (gm (r ≫ pullback.fst X.hom (spMap (algebraMap R K))) z (M.U i) (u.s i)).val = gs (r ≫ pullback.snd X.hom (spMap (algebraMap R K))) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) * (gm r z ((M.pull (pullback.fst X.hom (spMap (algebraMap R K)))).U fun _ => i) (c.s fun _ => i)).val) → ∃ b : Rˣ, algebraMap R K (b : R) = (a : K) := by
  intro R K _ _ _ _ _ X e he eA heA M rig c hM hrig hcorr a u hu H
  obtain ⟨w, hw⟩ := rigUnit_exists_ratio M hM e (LB.genPull M u e) rig (LB.isGen_genPull M u hu e) hrig
  haveI : Epi (CommRingCat.ofHom (algebraMap R K)) := by
    have := IsLocalization.epi (nonZeroDivisors R) K
    exact this
  haveI : Mono (spMap (algebraMap R K)) := by
    exact inferInstanceAs (Mono (Scheme.Spec.map (CommRingCat.ofHom (algebraMap R K)).op))
  have hsnd : eA ≫ pullback.snd X.hom (spMap (algebraMap R K)) = 𝟙 _ := by
    rw [← cancel_mono (spMap (algebraMap R K)), Category.assoc, ← pullback.condition, ← Category.assoc, heA,
      Category.assoc, he, Category.comp_id, Category.id_comp]
  let z : Sp K := (⊥ : PrimeSpectrum K)
  choose J hJ using fun χ : Sp K ⟶ X.left => exists_chart hM (χ z)
  have hG : Good M z J := hJ
  have hv := val_corr hG hcorr (𝟙 _)
  rw [val_pull hG, val_pull hG, Category.id_comp, Category.id_comp,
    val_of (L := M) c eA z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => by rw [heA]),
    val_of (L := M) rig _ z J (fun _ => J (spMap (algebraMap R K) ≫ e)) (fun _ => rfl)] at hv
  have hi := hJ (spMap (algebraMap R K) ≫ e)
  generalize J (spMap (algebraMap R K) ≫ e) = i at hv hi
  have h1 := H i _ eA z (by
    have : (eA ≫ pullback.fst X.hom (spMap (algebraMap R K))) z ∈ M.U i := by rw [heA]; exact hi
    exact this)
  rw [heA, hsnd] at h1
  have hm : spMap (algebraMap R K) z ∈ (M.pull e).U (fun _ => i) := mem_pull.2 hi
  have h2 := hw _ (spMap (algebraMap R K)) z (fun _ => i) hm
  have h3 : gm (spMap (algebraMap R K)) z ((M.pull e).U (fun _ => i)) ((LB.genPull M u e).s (fun _ => i)) =
      gm (spMap (algebraMap R K) ≫ e) z (M.U i) (u.s i) :=
    (gm_res _ z _ hm _).trans (gm_pull _ e z _ hi _)
  have h4 : (gm (spMap (algebraMap R K)) z ⊤ w).val =
      gs (𝟙 (Sp K)) z ⊤ ((Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom (a : K)) := by
    have h5 := (congrArg Units.val (h2.symm.trans h3)).trans (h1.trans (congrArg (_ * ·) (congrArg Units.val hv)))
    rw [Units.val_mul] at h5
    exact (Units.mul_left_inj _).1 h5
  refine ⟨Units.map (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom.toMonoidHom w, ?_⟩
  let φ : K →+* (Sp K).presheaf.stalk z :=
    ((Sp K).presheaf.germ ⊤ z trivial).hom.comp (Scheme.ΓSpecIso (CommRingCat.of K)).inv.hom
  apply φ.injective
  rw [gm_val _ z ⊤ trivial, gs_eq _ z ⊤ trivial] at h4
  refine Eq.trans ?_ h4
  change ((Sp K).presheaf.germ ⊤ z trivial).hom _ = ((Sp K).presheaf.germ ⊤ z trivial).hom _
  congr 1
  have n := congrArg (fun q => q.hom ((Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom w.val))
    (Scheme.ΓSpecIso_inv_naturality (CommRingCat.ofHom (algebraMap R K)))
  simp only [CommRingCat.hom_comp, RingHom.comp_apply, CommRingCat.hom_ofHom, Iso.hom_inv_id_apply] at n
  exact n

end GlobalTheory
