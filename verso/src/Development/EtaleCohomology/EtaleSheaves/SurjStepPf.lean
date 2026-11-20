import Development.EtaleCohomology.EtaleSheaves.ZarIndPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry GlobalTheory.EtC LateralTheory.E.t_E2Cut LateralTheory.E.ZLGPf LateralTheory.E.ZarIndPf

namespace LateralTheory.E.SurjStepPf

set_option linter.unusedSimpArgs false

variable {X S : Scheme.{0}}

/- English proof (translation)
Both sides reduce to the same expression.
-/
example (q : ℕ) (E : Spc) (n i : ℤ) : Ht q E n i = H (ZMod q) E (tw q i) n := rfl

/- English proof (translation)
Rewrite using `[Functor.map_comp, pull_comp]`.
-/
theorem pc {R : Type} [CommRing R] {A B C : Scheme.{0}} (f : A ⟶ B) (g : B ⟶ C) (F : Shv R) (n : ℤ) (x : H R (sch.obj C) F n) :
    pull R (sch.map (f ≫ g)) F n x = pull R (sch.map f) F n (pull R (sch.map g) F n x) := by
  rw [Functor.map_comp, pull_comp]

/- English proof (translation)
The claim follows from `(pullback.lift_fst _ _ _).trans (Category.comp_id _)`.
-/
@[reassoc] theorem resO_fst (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : resO p h ≫ pullback.fst p U.ι = pullback.fst p V.ι :=
  (pullback.lift_fst _ _ _).trans (Category.comp_id _)

/- English proof (translation)
The claim follows from `pullback.lift_snd _ _ _`.
-/
@[reassoc] theorem resO_snd (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO p h ≫ pullback.snd p U.ι = pullback.snd p V.ι ≫ S.homOfLE h :=
  pullback.lift_snd _ _ _

/- English proof (translation)
The claim follows from `pullback.lift_fst _ _ _`.
-/
@[reassoc] theorem fO_fst {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.fst p U.ι = pullback.fst (f ≫ p) U.ι ≫ f :=
  pullback.lift_fst _ _ _

/- English proof (translation)
The claim follows from `(pullback.lift_snd _ _ _).trans (Category.comp_id _)`.
-/
@[reassoc] theorem fO_snd {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (U : S.Opens) :
    fO f p U ≫ pullback.snd p U.ι = pullback.snd (f ≫ p) U.ι :=
  (pullback.lift_snd _ _ _).trans (Category.comp_id _)

/- English proof (translation)
Apply the tactic sequence `apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]`.
-/
theorem resO_comp (p : X ⟶ S) {U V W : S.Opens} (h1 : U ≤ V) (h2 : V ≤ W) :
    resO p h1 ≫ resO p h2 = resO p (h1.trans h2) := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

/- English proof (translation)
Apply the tactic sequence `apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]`.
-/
theorem resO_refl (p : X ⟶ S) (U : S.Opens) : resO p (le_refl U) = 𝟙 _ := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

instance (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) : IsOpenImmersion (resO p h) := by
  have : IsOpenImmersion (resO p h ≫ pullback.fst p U.ι) := by rw [resO_fst]; infer_instance
  exact IsOpenImmersion.of_comp (resO p h) (pullback.fst p U.ι)

/- English proof (translation)
Rewrite using `[Scheme.Pullback.range_fst, Scheme.Opens.range_ι]`.
-/
theorem range_fst (p : X ⟶ S) (V : S.Opens) : Set.range (pullback.fst p V.ι) = p ⁻¹' (V : Set S) := by
  rw [Scheme.Pullback.range_fst, Scheme.Opens.range_ι]

/- English proof (translation)
Use extensionality with `z`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨w, rfl⟩`. Rewrite using `[Set.mem_preimage, ← Scheme.Hom.comp_apply, resO_fst, ← range_fst]`. Conclude with `⟨w, rfl⟩`.

Introduce `hz`. Rewrite `hz` using `[Set.mem_preimage, ← range_fst]`. Take `⟨w, hw⟩` from `hz`. Use `⟨w, (pullback.fst p U.ι).isOpenEmbedding.injective ?_⟩` and prove the remaining obligations. Rewrite using `[← Scheme.Hom.comp_apply, resO_fst, hw]`.
-/
theorem range_resO (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    Set.range (resO p h) = pullback.fst p U.ι ⁻¹' (p ⁻¹' (V : Set S)) := by
  ext z
  constructor
  · rintro ⟨w, rfl⟩
    rw [Set.mem_preimage, ← Scheme.Hom.comp_apply, resO_fst, ← range_fst]
    exact ⟨w, rfl⟩
  · intro hz
    rw [Set.mem_preimage, ← range_fst] at hz
    obtain ⟨w, hw⟩ := hz
    refine ⟨w, (pullback.fst p U.ι).isOpenEmbedding.injective ?_⟩
    rw [← Scheme.Hom.comp_apply, resO_fst, hw]

/- English proof (translation)
Rewrite using `[range_resO, range_resO, ← Set.preimage_union, ← Set.preimage_union, Set.eq_univ_iff_forall]`. Introduce `z`. Establish `: pullback.fst p (V ⊔ W).ι z ∈ Set.range (pullback.fst p (V ⊔ W).ι)` using `⟨z, rfl⟩`. Rewrite `this` using `[range_fst]`. Simplify `this` using `[Set.mem_union]`.
-/
theorem cover (p : X ⟶ S) (V W : S.Opens) :
    Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) ∪ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) = Set.univ := by
  rw [range_resO, range_resO, ← Set.preimage_union, ← Set.preimage_union, Set.eq_univ_iff_forall]
  intro z
  have : pullback.fst p (V ⊔ W).ι z ∈ Set.range (pullback.fst p (V ⊔ W).ι) := ⟨z, rfl⟩
  rw [range_fst] at this
  simpa [Set.mem_union] using this

def phi (p : X ⟶ S) (V W : S.Opens) :
    pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) ⟶ overO p (V ⊓ W) :=
  IsOpenImmersion.lift (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))
    (pullback.fst _ _ ≫ resO p le_sup_left) (by
      rintro _ ⟨z, rfl⟩
      rw [range_resO]
      have h1 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_left : V ≤ V ⊔ W)) :=
        ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      have h2 : (pullback.fst _ _ ≫ resO p (le_sup_left : V ≤ V ⊔ W)) z ∈ Set.range (resO p (le_sup_right : W ≤ V ⊔ W)) := by
        rw [pullback.condition]; exact ⟨_, (Scheme.Hom.comp_apply _ _ z).symm⟩
      rw [range_resO] at h1 h2
      exact ⟨h1, h2⟩)

/- English proof (translation)
The claim follows from `IsOpenImmersion.lift_fac _ _ _`.
-/
@[reassoc] theorem phi_fac (p : X ⟶ S) (V W : S.Opens) :
    phi p V W ≫ resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W) = pullback.fst _ _ ≫ resO p le_sup_left :=
  IsOpenImmersion.lift_fac _ _ _

/- English proof (translation)
Rewrite using `[← cancel_mono (resO p (le_sup_left : V ≤ V ⊔ W)), Category.assoc, resO_comp, phi_fac]`.
-/
theorem phi_fst (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_left = pullback.fst _ _ := by
  rw [← cancel_mono (resO p (le_sup_left : V ≤ V ⊔ W)), Category.assoc, resO_comp, phi_fac]

/- English proof (translation)
Rewrite using `[← cancel_mono (resO p (le_sup_right : W ≤ V ⊔ W)), Category.assoc, resO_comp, ← pullback.condition]`. Conclude with `phi_fac p V W`.
-/
theorem phi_snd (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ resO p inf_le_right = pullback.snd _ _ := by
  rw [← cancel_mono (resO p (le_sup_right : W ≤ V ⊔ W)), Category.assoc, resO_comp, ← pullback.condition]
  exact phi_fac p V W

def psi (p : X ⟶ S) (V W : S.Opens) :
    overO p (V ⊓ W) ⟶ pullback (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) :=
  pullback.lift (resO p inf_le_left) (resO p inf_le_right) (by rw [resO_comp, resO_comp])

/- English proof (translation)
Apply `pullback.hom_ext` to reduce the goal to its premises. Rewrite using `[Category.assoc, psi, pullback.lift_fst, phi_fst, Category.id_comp]`. Rewrite using `[Category.assoc, psi, pullback.lift_snd, phi_snd, Category.id_comp]`.
-/
theorem phi_psi (p : X ⟶ S) (V W : S.Opens) : phi p V W ≫ psi p V W = 𝟙 _ := by
  apply pullback.hom_ext
  · rw [Category.assoc, psi, pullback.lift_fst, phi_fst, Category.id_comp]
  · rw [Category.assoc, psi, pullback.lift_snd, phi_snd, Category.id_comp]

/- English proof (translation)
Apply the tactic sequence `apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]`.
-/
theorem fO_res {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) {V U : S.Opens} (h : V ≤ U) :
    resO (f ≫ p) h ≫ fO f p U = fO f p V ≫ resO p h := by
  apply pullback.hom_ext <;> simp only [Category.assoc, resO_fst, resO_snd, fO_fst, fO_snd, resO_fst_assoc, resO_snd_assoc, fO_fst_assoc, fO_snd_assoc, Scheme.homOfLE_homOfLE, Scheme.homOfLE_rfl, Category.comp_id, Category.id_comp]

/- English proof (translation)
Rewrite using `[← cancel_mono (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W)), Category.assoc, Category.assoc, phi_fac, ← fO_res, phi_fac_assoc, fO_res, ← Category.assoc, ← Category.assoc]`. Use `congr 1`. Conclude with `pullback.lift_fst _ _ _`.
-/
theorem phi_nat {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (V W : S.Opens) :
    pullback.map _ _ _ _ (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) ≫ phi p V W =
      phi (f ≫ p) V W ≫ fO f p (V ⊓ W) := by
  rw [← cancel_mono (resO p (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W)), Category.assoc, Category.assoc, phi_fac,
    ← fO_res, phi_fac_assoc, fO_res, ← Category.assoc, ← Category.assoc]
  congr 1
  exact pullback.lift_fst _ _ _

/- English proof (translation)
Assemble the required witnesses or components as `⟨fun z => by have : pullback.fst p U.ι z ∈ Set.range (pullback.fst p U.ι) := ⟨z, rfl⟩ rw [range_fst, h] at this exact this⟩`.
-/
theorem empty_over (p : X ⟶ S) (U : S.Opens) (h : (U : Set S) = ∅) : IsEmpty (overO p U) :=
  ⟨fun z => by
    have : pullback.fst p U.ι z ∈ Set.range (pullback.fst p U.ι) := ⟨z, rfl⟩
    rw [range_fst, h] at this
    exact this⟩

/- English proof (translation)
Take `⟨δ, hδ, hnat⟩` from `hM hH (ZMod q) (tw q i)`. Establish `hX` using `hδ (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover p V W)`. Establish `hY` using `hδ (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W)`. Establish `e1 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ xV) = pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y`. Rewrite using `[← pc, ← fO_res, pc, hV, ← pc, resO_comp]`.

Establish `e2 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ xW) = pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y`. Rewrite using `[← pc, ← fO_res, pc, hW, ← pc, resO_comp]`. Establish `hI` using `hinj (e1.trans e2.symm)`. Take `⟨x0, hx0V, hx0W⟩` from `(hX (m + 1)).1 xV xW (by rw [← phi_fst p V W, ← phi_snd p V W, pc, pc, hI])`. Establish `hzV : pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0`.

Rewrite using `[map_sub, ← pc, fO_res, pc, hx0V, hV, sub_self]`. Establish `hzW : pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0`. Rewrite using `[map_sub, ← pc, fO_res, pc, hx0W, hW, sub_self]`. Take `⟨w', hw'⟩` from `((hY m).2.2 _).1 ⟨hzV, hzW⟩`. Take `⟨u, hu⟩` from `hsurj (pull _ (sch.map (psi (f ≫ p) V W)) _ _ w')`.

Establish `hn` using `hnat (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W)) (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W) (cover p V W) (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_righ …`. Rewrite `hn` using `[← pc, phi_nat, pc, hu, ← pc, phi_psi]`. Rewrite `hn` using `[CategoryTheory.Functor.map_id, pull_id]`. Rewrite `hn` using `[hw']`. Use `⟨x0 - δ _ _ m (pull _ (sch.map (phi p V W)) _ _ u), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_sub, ← hn, sub_sub_cancel]`.
-/
theorem glue (hM : MV) (hH : Hyp) (q : ℕ) {Y : Scheme.{0}} (f : Y ⟶ X) (p : X ⟶ S) (i m : ℤ) (V W : S.Opens)
    (hinj : Function.Injective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) (m + 1)))
    (hsurj : Function.Surjective (pull _ (sch.map (fO f p (V ⊓ W))) (tw q i) m))
    (y : H (ZMod q) (sch.obj (overO (f ≫ p) (V ⊔ W))) (tw q i) (m + 1))
    (xV : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1)) (xW : H (ZMod q) (sch.obj (overO p W)) (tw q i) (m + 1))
    (hV : pull _ (sch.map (fO f p V)) _ _ xV = pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ y)
    (hW : pull _ (sch.map (fO f p W)) _ _ xW = pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ y) :
    ∃ x, pull _ (sch.map (fO f p (V ⊔ W))) _ _ x = y := by
  obtain ⟨δ, hδ, hnat⟩ := hM hH (ZMod q) (tw q i)
  have hX := hδ (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover p V W)
  have hY := hδ (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W)
  have e1 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_left : V ⊓ W ≤ V))) _ _ xV) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hV, ← pc, resO_comp]
  have e2 : pull _ (sch.map (fO f p (V ⊓ W))) _ _ (pull _ (sch.map (resO p (inf_le_right : V ⊓ W ≤ W))) _ _ xW) =
      pull _ (sch.map (resO (f ≫ p) (inf_le_left.trans le_sup_left : V ⊓ W ≤ V ⊔ W))) _ _ y := by
    rw [← pc, ← fO_res, pc, hW, ← pc, resO_comp]
  have hI := hinj (e1.trans e2.symm)
  obtain ⟨x0, hx0V, hx0W⟩ := (hX (m + 1)).1 xV xW (by rw [← phi_fst p V W, ← phi_snd p V W, pc, pc, hI])
  have hzV : pull _ (sch.map (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0V, hV, sub_self]
  have hzW : pull _ (sch.map (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))) _ _ (pull _ (sch.map (fO f p (V ⊔ W))) _ _ x0 - y) = 0 := by
    rw [map_sub, ← pc, fO_res, pc, hx0W, hW, sub_self]
  obtain ⟨w', hw'⟩ := ((hY m).2.2 _).1 ⟨hzV, hzW⟩
  obtain ⟨u, hu⟩ := hsurj (pull _ (sch.map (psi (f ≫ p) V W)) _ _ w')
  have hn := hnat (resO (f ≫ p) (le_sup_left : V ≤ V ⊔ W)) (resO (f ≫ p) (le_sup_right : W ≤ V ⊔ W))
    (resO p (le_sup_left : V ≤ V ⊔ W)) (resO p (le_sup_right : W ≤ V ⊔ W)) (cover (f ≫ p) V W) (cover p V W)
    (fO f p V) (fO f p W) (fO f p (V ⊔ W)) (fO_res f p le_sup_left) (fO_res f p le_sup_right) m
    (pull _ (sch.map (phi p V W)) _ _ u)
  rw [← pc, phi_nat, pc, hu, ← pc, phi_psi] at hn
  rw [CategoryTheory.Functor.map_id, pull_id] at hn
  rw [hw'] at hn
  refine ⟨x0 - δ _ _ m (pull _ (sch.map (phi p V W)) _ _ u), ?_⟩
  rw [map_sub, ← hn, sub_sub_cancel]

/- English proof (translation)
Introduce `hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb hinj U hU y`. Take `⟨m, rfl⟩ : ∃ m, n = m + 1` from `⟨n - 1, by ring⟩`. Establish `hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U` using `by simpa using hb`. Set `Good : S.Opens → Prop` to `fun V => ∃ h : V ≤ U, ∃ x : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1), pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y`. Establish `mono : ∀ V V' : S.Opens, V' ≤ V → Good V → Good V'`.

Introduce and unpack `V V' h ⟨hV, x, hx⟩`. Use `⟨h.trans hV, pull _ (sch.map (resO p h)) _ _ x, ?_⟩` and prove the remaining obligations. Rewrite using `[← pc, ← fO_res, pc, hx, ← pc, resO_comp]`. Establish `union : ∀ V W : S.Opens, IsCompact (V : Set S) → IsCompact (W : Set S) → Good V → Good W → Good (V ⊔ W)`. Introduce and unpack `V W hVc hWc ⟨hV, xV, hxV⟩ ⟨hW, xW, hxW⟩`.

Establish `hIc : IsCompact ((V ⊓ W : S.Opens) : Set S)` using `QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc`. Apply the tactic sequence `obtain ⟨x, hx⟩ := glue hM hH q f p i m V W (hinj _ hIc) (hb' _ hIc).2 (pull _ (sch.map (resO (f ≫ p) (sup_le hV hW))) _ _ y) xV xW (by rw [hxV]; first | rfl | rw [← pc, resO_comp]) (by rw [hxW]; first | rfl | rw [← pc, resO_comp])`. Conclude with `⟨sup_le hV hW, x, by rw [hx]⟩`. Establish `P : (U : Set S) = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ (U : Set S) ⊆ V ∧ Good V`. Use `hU.induction_on (p := fun T : Set S => T = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ T ⊆ V ∧ Good V) (Or.inl rfl) ?_ ?_ ?_` and prove the remaining obligations.

Introduce and unpack `s t hst (h | ⟨V, hVc, htV, hV⟩)`. Conclude with `Or.inl (Set.subset_eq_empty hst h)`. Conclude with `Or.inr ⟨V, hVc, hst.trans htV, hV⟩`. Introduce and unpack `s t (h | h1) (h' | h2)`. Use `left`.

Rewrite using `[h, h', Set.empty_union]`. Use `right`. Rewrite using `[h, Set.empty_union]`. Conclude with `h2`. Use `right`.

Rewrite using `[h', Set.union_empty]`. Conclude with `h1`. Take `⟨V, hVc, hsV, hV⟩` from `h1`. Take `⟨W, hWc, htW, hW⟩` from `h2`. Conclude with `Or.inr ⟨V ⊔ W, by simpa using hVc.union hWc, Set.union_subset_union hsV htW, union V W hVc hWc hV hW⟩`.

Introduce `s hs`. Take `⟨V, hVU, hsV, x, hx⟩` from `(hg s).2 U hs y`. Take `⟨V', hV'aff, hsV', hV'V⟩` from `(TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens S)) hsV`. Conclude with `⟨V', mem_nhdsWithin_of_mem_nhds (V'.isOpen.mem_nhds hsV'), Or.inr ⟨V', hV'aff.isCompact, subset_rfl, mono V V' hV'V ⟨hVU, x, hx⟩⟩⟩`. Break down `P with h | ⟨V, -, hUV, hVU, x, hx⟩` into its components or cases.

Use `empty_over p U h` as an intermediate fact. Conclude with `(pull_bij_of_iso (sch.map (fO f p U)) (tw q i) _).2 y`. Take `rfl : V = U` from `le_antisymm hVU hUV`. Conclude with `⟨x, by rw [hx, resO_refl, CategoryTheory.Functor.map_id, pull_id]⟩`.
-/
theorem SurjStep_of : SurjStep := by
  intro hM hH q Y X S f p _ _ _ _ _ _ hq i n hg hb hinj U hU y
  obtain ⟨m, rfl⟩ : ∃ m, n = m + 1 := ⟨n - 1, by ring⟩
  have hb' : ∀ U : S.Opens, IsCompact (U : Set S) → Bij q i m f p U := by simpa using hb
  let Good : S.Opens → Prop := fun V => ∃ h : V ≤ U, ∃ x : H (ZMod q) (sch.obj (overO p V)) (tw q i) (m + 1),
    pull _ (sch.map (fO f p V)) _ _ x = pull _ (sch.map (resO (f ≫ p) h)) _ _ y
  have mono : ∀ V V' : S.Opens, V' ≤ V → Good V → Good V' := by
    rintro V V' h ⟨hV, x, hx⟩
    refine ⟨h.trans hV, pull _ (sch.map (resO p h)) _ _ x, ?_⟩
    rw [← pc, ← fO_res, pc, hx, ← pc, resO_comp]
  have union : ∀ V W : S.Opens, IsCompact (V : Set S) → IsCompact (W : Set S) → Good V → Good W → Good (V ⊔ W) := by
    rintro V W hVc hWc ⟨hV, xV, hxV⟩ ⟨hW, xW, hxW⟩
    have hIc : IsCompact ((V ⊓ W : S.Opens) : Set S) :=
      QuasiSeparatedSpace.inter_isCompact _ _ V.isOpen hVc W.isOpen hWc
    obtain ⟨x, hx⟩ := glue hM hH q f p i m V W (hinj _ hIc) (hb' _ hIc).2
      (pull _ (sch.map (resO (f ≫ p) (sup_le hV hW))) _ _ y) xV xW
      (by rw [hxV]; first | rfl | rw [← pc, resO_comp]) (by rw [hxW]; first | rfl | rw [← pc, resO_comp])
    exact ⟨sup_le hV hW, x, by rw [hx]⟩
  have P : (U : Set S) = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ (U : Set S) ⊆ V ∧ Good V := by
    refine hU.induction_on (p := fun T : Set S => T = ∅ ∨ ∃ V : S.Opens, IsCompact (V : Set S) ∧ T ⊆ V ∧ Good V)
      (Or.inl rfl) ?_ ?_ ?_
    · rintro s t hst (h | ⟨V, hVc, htV, hV⟩)
      · exact Or.inl (Set.subset_eq_empty hst h)
      · exact Or.inr ⟨V, hVc, hst.trans htV, hV⟩
    · rintro s t (h | h1) (h' | h2)
      · left; rw [h, h', Set.empty_union]
      · right; rw [h, Set.empty_union]; exact h2
      · right; rw [h', Set.union_empty]; exact h1
      · obtain ⟨V, hVc, hsV, hV⟩ := h1
        obtain ⟨W, hWc, htW, hW⟩ := h2
        exact Or.inr ⟨V ⊔ W, by simpa using hVc.union hWc, Set.union_subset_union hsV htW, union V W hVc hWc hV hW⟩
    · intro s hs
      obtain ⟨V, hVU, hsV, x, hx⟩ := (hg s).2 U hs y
      obtain ⟨V', hV'aff, hsV', hV'V⟩ := (TopologicalSpace.Opens.isBasis_iff_nbhd.1 (Scheme.isBasis_affineOpens S)) hsV
      exact ⟨V', mem_nhdsWithin_of_mem_nhds (V'.isOpen.mem_nhds hsV'),
        Or.inr ⟨V', hV'aff.isCompact, subset_rfl, mono V V' hV'V ⟨hVU, x, hx⟩⟩⟩
  rcases P with h | ⟨V, -, hUV, hVU, x, hx⟩
  · have := empty_over p U h
    exact (pull_bij_of_iso (sch.map (fO f p U)) (tw q i) _).2 y
  · obtain rfl : V = U := le_antisymm hVU hUV
    exact ⟨x, by rw [hx, resO_refl, CategoryTheory.Functor.map_id, pull_id]⟩

end LateralTheory.E.SurjStepPf
