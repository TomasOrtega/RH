import Development.EtaleCohomology.TateTwists.EtaleChainsMayerVietorisShortExactOfFree

open CategoryTheory Limits AlgebraicGeometry Opposite GlobalTheory.EtC

namespace LateralTheory.EtaleFoundations.MvFree

/- English proof (translation)
Establish `hp1 : Function.Injective p1` using `fun t t' h => hj t t' ⟨h, hg (by rw [← hc, ← hc, h])⟩`. Establish `hh : Function.Injective (f ∘ p1)` using `hf.comp hp1`. Use `⟨Finsupp.mapDomain_injective hp1, fun p q hpq => ?_⟩` and prove the remaining obligations. Use `set z := Finsupp.mapDomain f p with hz`. Establish `hz' : z = Finsupp.mapDomain g (-q)`.

Establish `h0 : Finsupp.mapDomain g q + Finsupp.mapDomain g (-q) = 0`. Rewrite using `[← Finsupp.mapDomain_add, add_neg_cancel, Finsupp.mapDomain_zero]`. Rewrite using `[hz]`. Conclude with `(eq_neg_of_add_eq_zero_left hpq).trans (eq_neg_of_add_eq_zero_right h0).symm`. Establish `hsupp : (z.support : Set γ) ⊆ Set.range (f ∘ p1)`.

Introduce `x hx`. Establish `h1 : x ∈ Set.range f`. Use `Finsupp.mapDomain_support (f := f) (s := p) (by rw [← hz]; exact hx)` as an intermediate fact. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 this`. Conclude with `⟨a, rfl⟩`.

Establish `h2 : x ∈ Set.range g`. Rewrite `hx` using `[hz']`. Use `Finsupp.mapDomain_support (f := g) (s := -q) hx` as an intermediate fact. Take `⟨a, -, rfl⟩` from `Finset.mem_image.1 this`. Conclude with `⟨a, rfl⟩`.

Take `⟨a, rfl⟩` from `h1`. Take `⟨b, hb⟩` from `h2`. Take `⟨t, ht, -⟩` from `hs a b hb.symm`. Conclude with `⟨t, by simp [ht]⟩`. Use `⟨Finsupp.comapDomain (f ∘ p1) z hh.injOn, ?_, ?_⟩` and prove the remaining obligations.

Apply `Finsupp.mapDomain_injective hf` to reduce the goal to its premises. Rewrite using `[← Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain _ hh _ hsupp]`. Apply `Finsupp.mapDomain_injective hg` to reduce the goal to its premises. Establish `: g ∘ p2 = f ∘ p1` using `funext fun t => (hc t).symm`. Rewrite using `[← Finsupp.mapDomain_comp, this, Finsupp.mapDomain_comapDomain _ hh _ hsupp, hz']`.
-/
theorem finsupp_mv {T α β γ M : Type*} [AddCommGroup M] (p1 : T → α) (p2 : T → β) (f : α → γ) (g : β → γ)
    (hf : Function.Injective f) (hg : Function.Injective g) (hc : ∀ t, f (p1 t) = g (p2 t))
    (hj : ∀ t t', p1 t = p1 t' ∧ p2 t = p2 t' → t = t')
    (hs : ∀ x y, f x = g y → ∃ t, p1 t = x ∧ p2 t = y) :
    Function.Injective (Finsupp.mapDomain (M := M) p1) ∧
    ∀ (p : α →₀ M) (q : β →₀ M), Finsupp.mapDomain f p + Finsupp.mapDomain g q = 0 →
      ∃ c : T →₀ M, Finsupp.mapDomain p1 c = p ∧ Finsupp.mapDomain p2 c = -q := by
  classical
  have hp1 : Function.Injective p1 := fun t t' h =>
    hj t t' ⟨h, hg (by rw [← hc, ← hc, h])⟩
  have hh : Function.Injective (f ∘ p1) := hf.comp hp1
  refine ⟨Finsupp.mapDomain_injective hp1, fun p q hpq => ?_⟩
  set z := Finsupp.mapDomain f p with hz
  have hz' : z = Finsupp.mapDomain g (-q) := by
    have h0 : Finsupp.mapDomain g q + Finsupp.mapDomain g (-q) = 0 := by
      rw [← Finsupp.mapDomain_add, add_neg_cancel, Finsupp.mapDomain_zero]
    rw [hz]; exact (eq_neg_of_add_eq_zero_left hpq).trans (eq_neg_of_add_eq_zero_right h0).symm
  have hsupp : (z.support : Set γ) ⊆ Set.range (f ∘ p1) := by
    intro x hx
    have h1 : x ∈ Set.range f := by
      have := Finsupp.mapDomain_support (f := f) (s := p) (by rw [← hz]; exact hx)
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    have h2 : x ∈ Set.range g := by
      rw [hz'] at hx
      have := Finsupp.mapDomain_support (f := g) (s := -q) hx
      obtain ⟨a, -, rfl⟩ := Finset.mem_image.1 this; exact ⟨a, rfl⟩
    obtain ⟨a, rfl⟩ := h1
    obtain ⟨b, hb⟩ := h2
    obtain ⟨t, ht, -⟩ := hs a b hb.symm
    exact ⟨t, by simp [ht]⟩
  refine ⟨Finsupp.comapDomain (f ∘ p1) z hh.injOn, ?_, ?_⟩
  · apply Finsupp.mapDomain_injective hf
    rw [← Finsupp.mapDomain_comp, Finsupp.mapDomain_comapDomain _ hh _ hsupp]
  · apply Finsupp.mapDomain_injective hg
    have : g ∘ p2 = f ∘ p1 := funext fun t => (hc t).symm
    rw [← Finsupp.mapDomain_comp, this, Finsupp.mapDomain_comapDomain _ hh _ hsupp, hz']

/- English proof (translation)
Rewrite using `[ShortComplex.exact_iff_isZero_homology]`. Apply `Functor.isZero` to reduce the goal to its premises. Introduce `X`. Conclude with `((ShortComplex.exact_iff_isZero_homology _).1 (h X)).of_iso (S.mapHomologyIso ((evaluation C D).obj X)).symm`.
-/
theorem exact_of_eval {C D : Type*} [Category C] [Category D] [Abelian D]
    (S : ShortComplex (C ⥤ D)) (h : ∀ X, (S.map ((evaluation C D).obj X)).Exact) : S.Exact := by
  rw [ShortComplex.exact_iff_isZero_homology]
  apply Functor.isZero
  intro X
  exact ((ShortComplex.exact_iff_isZero_homology _).1 (h X)).of_iso (S.mapHomologyIso ((evaluation C D).obj X)).symm

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations.MvFree

noncomputable def mvIso {C D : Type*} [Category C] [Category D] [Preadditive C] [Preadditive D]
    [HasBinaryBiproducts C] [HasBinaryBiproducts D] (G : C ⥤ D) [G.Additive] {X1 A B X3 : C}
    (a : X1 ⟶ A) (b : X1 ⟶ B) (c : A ⟶ X3) (d : B ⟶ X3)
    (w : biprod.lift a (-b) ≫ biprod.desc c d = 0)
    (w' : biprod.lift (G.map a) (-G.map b) ≫ biprod.desc (G.map c) (G.map d) = 0) :
    (ShortComplex.mk _ _ w).map G ≅ ShortComplex.mk _ _ w' := by
  haveI := preservesBinaryBiproducts_of_preservesBiproducts G
  exact ShortComplex.isoMk (Iso.refl _) (G.mapBiprod A B) (Iso.refl _)
    (by show 𝟙 _ ≫ biprod.lift (G.map a) (-G.map b) = G.map (biprod.lift a (-b)) ≫ (G.mapBiprod A B).hom
        rw [biprod.map_lift_mapBiprod, Functor.map_neg, Category.id_comp])
    (by dsimp; rw [← biprod.mapBiprod_inv_map_desc]; erw [Iso.hom_inv_id_assoc]; simp; exact (Category.comp_id _).symm)

/- English proof (translation)
Establish `h : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂`. Rewrite using `[← e.hom.comm₁₂, ← Category.assoc, ← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁, Category.id_comp]`. Rewrite using `[h]`. Use `infer_instance`.
-/
theorem mono_f_of_iso {C : Type*} [Category C] [HasZeroMorphisms C] {S T : ShortComplex C}
    (e : S ≅ T) [Mono S.f] : Mono T.f := by
  have h : T.f = e.inv.τ₁ ≫ S.f ≫ e.hom.τ₂ := by
    rw [← e.hom.comm₁₂, ← Category.assoc, ← ShortComplex.comp_τ₁, e.inv_hom_id, ShortComplex.id_τ₁,
      Category.id_comp]
  rw [h]; infer_instance

/- English proof (translation)
Establish `e : ∀ w : ↑(A ⊞ B), (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) w) + (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) w) = w` using `fun w => by`. Establish `h` using `ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) w`. Rewrite `h` using `[ConcreteCategory.id_apply]`. Use `conv_rhs => rw [← h]`. Both sides reduce to the same expression.

Rewrite using `[← e z, ← e z', h1, h2]`.
-/
theorem biprod_ext_el {S : Type*} [Ring S] {A B : ModuleCat.{1} S} (z z' : ↑(A ⊞ B))
    (h1 : (biprod.fst : A ⊞ B ⟶ A) z = (biprod.fst : A ⊞ B ⟶ A) z')
    (h2 : (biprod.snd : A ⊞ B ⟶ B) z = (biprod.snd : A ⊞ B ⟶ B) z') :
    z = z' := by
  have e : ∀ w : ↑(A ⊞ B), (biprod.inl : A ⟶ A ⊞ B) ((biprod.fst : A ⊞ B ⟶ A) w) + (biprod.inr : B ⟶ A ⊞ B) ((biprod.snd : A ⊞ B ⟶ B) w) = w :=
    fun w => by
      have h := ConcreteCategory.congr_hom (biprod.total (X := A) (Y := B)) w
      rw [ConcreteCategory.id_apply] at h
      conv_rhs => rw [← h]
      rfl
  rw [← e z, ← e z', h1, h2]

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Establish `: Mono u` using `(ModuleCat.mono_iff_injective u).2 hu`. Establish `: Mono (biprod.lift u (-v) ≫ biprod.fst)` using `by rw [biprod.lift_fst]; infer_instance`. Conclude with `mono_of_mono _ biprod.fst`. Rewrite using `[ShortComplex.moduleCat_exact_iff]`.

Introduce `x2 hx2`. Establish `hx2' : c ((biprod.fst : A ⊞ B ⟶ A) x2) + d ((biprod.snd : A ⊞ B ⟶ B) x2) = 0`. Establish `h : (biprod.desc c d : A ⊞ B ⟶ X3) x2 = 0` using `hx2`. Rewrite `h` using `[biprod.desc_eq]`. Simplify using `using h`.

Take `⟨x, h1, h2⟩` from `hex _ _ hx2'`. Use `⟨x, ?_⟩` and prove the remaining obligations. Apply `biprod_ext_el` to reduce the goal to its premises. Use `dsimp`. Rewrite using `[← ConcreteCategory.comp_apply, biprod.lift_fst, h1]`.

Use `dsimp`. Rewrite using `[← ConcreteCategory.comp_apply, biprod.lift_snd]`. Simplify using `[h2]`.
-/
theorem mc_exact {S : Type*} [Ring S] {X1 A B X3 : ModuleCat.{1} S} (u : X1 ⟶ A) (v : X1 ⟶ B)
    (c : A ⟶ X3) (d : B ⟶ X3) (w : biprod.lift u (-v) ≫ biprod.desc c d = 0)
    (hu : Function.Injective u)
    (hex : ∀ p q, c p + d q = 0 → ∃ x, u x = p ∧ v x = -q) :
    Mono (biprod.lift u (-v)) ∧ (ShortComplex.mk (biprod.lift u (-v)) (biprod.desc c d) w).Exact := by
  constructor
  · have : Mono u := (ModuleCat.mono_iff_injective u).2 hu
    have : Mono (biprod.lift u (-v) ≫ biprod.fst) := by rw [biprod.lift_fst]; infer_instance
    exact mono_of_mono _ biprod.fst
  · rw [ShortComplex.moduleCat_exact_iff]
    intro x2 hx2
    have hx2' : c ((biprod.fst : A ⊞ B ⟶ A) x2) + d ((biprod.snd : A ⊞ B ⟶ B) x2) = 0 := by
      have h : (biprod.desc c d : A ⊞ B ⟶ X3) x2 = 0 := hx2
      rw [biprod.desc_eq] at h
      simpa using h
    obtain ⟨x, h1, h2⟩ := hex _ _ hx2'
    refine ⟨x, ?_⟩
    apply biprod_ext_el
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_fst, h1]
    · dsimp; rw [← ConcreteCategory.comp_apply, biprod.lift_snd]
      simp [h2]

/- English proof (translation)
Establish `hpb` using `(IsPullback.of_hasPullback f g).map ((evaluation _ _).obj X)`. Rewrite `hpb` using `[Types.isPullback_iff]`. Take `⟨hw, hj, hs⟩` from `hpb`. Simplify using `at hw hj hs`. Establish `hf : Function.Injective (f.app X)` using `(mono_iff_injective (f.app X)).1 inferInstance`.

Establish `hg : Function.Injective (g.app X)` using `(mono_iff_injective (g.app X)).1 inferInstance`. Take `⟨hinj, hex⟩` from `finsupp_mv (M := ULift.{1} R) (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.fst f g).app X y.down)) (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.snd f g).app X y.down)) (fun y : ULift.{1} (P.obj X) => ULift.up (f.app X y.down)) (fun y : ULif …`. Take `⟨t, h1, h2⟩` from `hs x.down y.down (congrArg ULift.down h)`. Conclude with `⟨ULift.up t, congrArg ULift.up h1, congrArg ULift.up h2⟩)`. Conclude with `mc_exact _ _ _ _ w hinj (fun p q h => hex p q h)`.
-/
theorem pointwise (R : Type) [CommRing R] {P Q E : PSh} (f : P ⟶ E) (g : Q ⟶ E) [Mono f] [Mono g]
    (X : Scheme.{0}ᵒᵖ) (w) :
    Mono (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X)) ∧
    (ShortComplex.mk (biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X))
      (biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X)) w).Exact := by
  have hpb := (IsPullback.of_hasPullback f g).map ((evaluation _ _).obj X)
  rw [Types.isPullback_iff] at hpb
  obtain ⟨hw, hj, hs⟩ := hpb
  dsimp at hw hj hs
  have hf : Function.Injective (f.app X) := (mono_iff_injective (f.app X)).1 inferInstance
  have hg : Function.Injective (g.app X) := (mono_iff_injective (g.app X)).1 inferInstance
  obtain ⟨hinj, hex⟩ := finsupp_mv (M := ULift.{1} R)
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.fst f g).app X y.down))
    (fun y : ULift.{1} ((pullback f g).obj X) => ULift.up ((pullback.snd f g).app X y.down))
    (fun y : ULift.{1} (P.obj X) => ULift.up (f.app X y.down))
    (fun y : ULift.{1} (Q.obj X) => ULift.up (g.app X y.down))
    (fun x y h => ULift.ext _ _ (hf (congrArg ULift.down h)))
    (fun x y h => ULift.ext _ _ (hg (congrArg ULift.down h)))
    (fun t => congrArg ULift.up (by simpa using ConcreteCategory.congr_hom hw t.down))
    (fun t t' h => ULift.ext _ _ (hj _ _ ⟨congrArg ULift.down h.1, congrArg ULift.down h.2⟩))
    (fun x y h => by
      obtain ⟨t, h1, h2⟩ := hs x.down y.down (congrArg ULift.down h)
      exact ⟨ULift.up t, congrArg ULift.up h1, congrArg ULift.up h2⟩)
  exact mc_exact _ _ _ _ w hinj (fun p q h => hex p q h)

end LateralTheory.EtaleFoundations.MvFree

namespace LateralTheory.EtaleFoundations

open MvFree in
/- English proof (translation)
Introduce `R _ P Q E f g _ _`. Establish `w0 : biprod.lift ((freeP R).map (pullback.fst f g)) (-(freeP R).map (pullback.snd f g)) ≫ biprod.desc ((freeP R).map f) ((freeP R).map g) = 0`. Rewrite using `[biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]`. Set `S` to `ShortComplex.mk _ _ w0`. Establish `hev : ∀ X, Mono ((S.map ((evaluation _ _).obj X)).f) ∧ (S.map ((evaluation _ _).obj X)).Exact`.

Introduce `X`. Establish `w1 : biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X) ≫ biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X) = 0`. Rewrite using `[biprod.lift_desc, Preadditive.neg_comp, ← NatTrans.comp_app, ← NatTrans.comp_app, ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]`. Take `⟨hm, hx⟩` from `pointwise R f g X w1`. Set `e` to `mvIso ((evaluation _ _).obj X) _ _ _ _ w0 w1`.

Conclude with `⟨@mono_f_of_iso _ _ _ _ _ e.symm hm, ShortComplex.exact_of_iso e.symm hx⟩`. Establish `hSm : Mono S.f`. Establish `: ∀ X, Mono (S.f.app X)` using `fun X => (hev X).1`. Conclude with `NatTrans.mono_of_mono_app _`. Establish `hSe : S.Exact` using `exact_of_eval S (fun X => (hev X).2)`.

Set `G` to `presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))`. Establish `w2 : biprod.lift (G.map ((freeP R).map (pullback.fst f g))) (-G.map ((freeP R).map (pullback.snd f g))) ≫ biprod.desc (G.map ((freeP R).map f)) (G.map ((freeP R).map g)) = 0`. Rewrite using `[biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]`. Set `e` to `mvIso G _ _ _ _ w0 w2`. Establish `hGm : Mono ((S.map G).f)` using `(inferInstance : Mono (G.map S.f))`.

Conclude with `⟨mono_f_of_iso e, w2, ShortComplex.exact_of_iso e (hSe.map G)⟩`.
-/
theorem etale_free_presheaf_mayer_vietoris_short_exact_holds : EtaleFreePresheafMayerVietorisShortExact := by
  intro R _ P Q E f g _ _
  have w0 : biprod.lift ((freeP R).map (pullback.fst f g)) (-(freeP R).map (pullback.snd f g)) ≫
      biprod.desc ((freeP R).map f) ((freeP R).map g) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      pullback.condition, add_neg_cancel]
  let S := ShortComplex.mk _ _ w0
  have hev : ∀ X, Mono ((S.map ((evaluation _ _).obj X)).f) ∧ (S.map ((evaluation _ _).obj X)).Exact := by
    intro X
    have w1 : biprod.lift (((freeP R).map (pullback.fst f g)).app X) (-((freeP R).map (pullback.snd f g)).app X) ≫
        biprod.desc (((freeP R).map f).app X) (((freeP R).map g).app X) = 0 := by
      rw [biprod.lift_desc, Preadditive.neg_comp, ← NatTrans.comp_app, ← NatTrans.comp_app,
        ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
    obtain ⟨hm, hx⟩ := pointwise R f g X w1
    let e := mvIso ((evaluation _ _).obj X) _ _ _ _ w0 w1
    exact ⟨@mono_f_of_iso _ _ _ _ _ e.symm hm, ShortComplex.exact_of_iso e.symm hx⟩
  have hSm : Mono S.f := by
    have : ∀ X, Mono (S.f.app X) := fun X => (hev X).1
    exact NatTrans.mono_of_mono_app _
  have hSe : S.Exact := exact_of_eval S (fun X => (hev X).2)
  let G := presheafToSheaf Scheme.etaleTopology.{0} (ModuleCat.{1} (ULift.{1} R))
  have w2 : biprod.lift (G.map ((freeP R).map (pullback.fst f g))) (-G.map ((freeP R).map (pullback.snd f g))) ≫
      biprod.desc (G.map ((freeP R).map f)) (G.map ((freeP R).map g)) = 0 := by
    rw [biprod.lift_desc, Preadditive.neg_comp, ← Functor.map_comp, ← Functor.map_comp,
      ← Functor.map_comp, ← Functor.map_comp, pullback.condition, add_neg_cancel]
  let e := mvIso G _ _ _ _ w0 w2
  have hGm : Mono ((S.map G).f) := (inferInstance : Mono (G.map S.f))
  exact ⟨mono_f_of_iso e, w2, ShortComplex.exact_of_iso e (hSe.map G)⟩

end LateralTheory.EtaleFoundations
