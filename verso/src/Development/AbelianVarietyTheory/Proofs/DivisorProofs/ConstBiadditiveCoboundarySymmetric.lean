import Mathlib
import Development.AbelianVarietyTheory.PublishedTheorems.Divisors₂.GaussManinPeriods
import Development.AbelianVarietyTheory.Definitions.Divisors.EllFamNontrivial
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DpExpEqSumRangeOfVanish
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.DividedPowerFiltration

set_option autoImplicit false

noncomputable section

open Filter Topology TopologicalSpace CategoryTheory GlobalTheory.AnPer GlobalTheory.CatCoh GlobalTheory.Cris TensorProduct

namespace GlobalTheory.AnPer.Charts

variable {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} {K : Charts F}

/- English proof (translation)
Take `⟨k, h1, h2⟩` from `H l T.k`. Set `S : K.Obj` to `{ k := k, C := T.C, J := T.J, nil := T.nil, ρ := T.ρ.comp (sh h1) ρ_cst := fun f ↦ (congrArg T.ρ (sh_cst h1 f)).trans (T.ρ_cst f) }`. Establish `key : ∀ m (h : K.le m T.k T.k), m = 0 → ∀ f, sh h f = f`. Introduce and unpack `m h rfl f`. Conclude with `sh_refl h f`.

Establish `e : (T.ρ.comp (sh h1)).comp (sh h2) = T.ρ` using `RingHom.ext fun f ↦ congrArg T.ρ ((sh_sh h2 h1 (K.le_trans h2 h1) f).trans (key _ _ (neg_add_cancel l) f))`. Set `s : S ⟶ T` to `⟨AlgHom.id _ _, l, h1, fun _ h ↦ h, Relation.ReflTransGen.refl⟩`. Set `s' : T ⟶ S` to `⟨AlgHom.id _ _, -l, h2, fun _ h ↦ h, by`. Express the relevant statement in the definitionally equal form `Close T.J ((T.ρ.comp (sh h1)).comp (sh h2)) T.ρ`. Rewrite using `[e]`.

Conclude with `Relation.ReflTransGen.refl⟩`. Conclude with `⟨S, s, s', rfl, rfl, hom_ext (fun _ ↦ rfl) (neg_add_cancel l)⟩`.
-/
theorem exists_shift_retraction (H : ∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') (l : Λ) (T : K.Obj) :
    ∃ (S : K.Obj) (s : S ⟶ T) (s' : T ⟶ S), s.deg = l ∧ s'.deg = -l ∧ s' ≫ s = 𝟙 T := by
  obtain ⟨k, h1, h2⟩ := H l T.k
  let S : K.Obj :=
    { k := k, C := T.C, J := T.J, nil := T.nil, ρ := T.ρ.comp (sh h1)
      ρ_cst := fun f ↦ (congrArg T.ρ (sh_cst h1 f)).trans (T.ρ_cst f) }
  have key : ∀ m (h : K.le m T.k T.k), m = 0 → ∀ f, sh h f = f := by
    rintro m h rfl f
    exact sh_refl h f
  have e : (T.ρ.comp (sh h1)).comp (sh h2) = T.ρ := RingHom.ext fun f ↦
    congrArg T.ρ ((sh_sh h2 h1 (K.le_trans h2 h1) f).trans (key _ _ (neg_add_cancel l) f))
  let s : S ⟶ T := ⟨AlgHom.id _ _, l, h1, fun _ h ↦ h, Relation.ReflTransGen.refl⟩
  let s' : T ⟶ S := ⟨AlgHom.id _ _, -l, h2, fun _ h ↦ h, by
    change Close T.J ((T.ρ.comp (sh h1)).comp (sh h2)) T.ρ
    rw [e]
    exact Relation.ReflTransGen.refl⟩
  exact ⟨S, s, s', rfl, rfl, hom_ext (fun _ ↦ rfl) (neg_add_cancel l)⟩

/- English proof (translation)
The claim follows from `Hol.ext_fn fun z hz ↦ by obtain ⟨k, hk⟩ := hR.1 (z, 0) hz exact (K.fn_cst k f hk).symm.trans ((congrArg (fun u ↦ Hol.fn u (z, 0)) (h k)).trans (K.fn_cst k f' hk))`.
-/
theorem eq_of_cst_eq (hR : K.Rich) {f f' : Hol F.V} (h : ∀ k, K.cst k f = K.cst k f') : f = f' :=
  Hol.ext_fn fun z hz ↦ by
    obtain ⟨k, hk⟩ := hR.1 (z, 0) hz
    exact (K.fn_cst k f hk).symm.trans ((congrArg (fun u ↦ Hol.fn u (z, 0)) (h k)).trans (K.fn_cst k f' hk))

end GlobalTheory.AnPer.Charts

namespace GlobalTheory.AnPer

/- English proof (translation)
Introduce `I _ g Λ _ F K H1 H2 H3 hR β c hd l m`. Take `⟨γ, hγ⟩` from `H1 c fun T T' T'' φ ψ h h' ↦ by`. Use `hd T T' T'' φ ψ` as an intermediate fact. Rewrite `this` using `[d1_apply, h', map_zero, map_zero]`. Take the linear combination `-this`.

Choose the witnesses or unpack the hypotheses as in `⟨c', hc0, hd'⟩ : ∃ c' : C1 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c' T T' φ = 0) ∧ ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), mp K.Oc ψ (c' T T' φ) - c' T T'' (φ ≫ ψ) + c' T' T'' ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg) := by`. Use `⟨fun T T' φ ↦ c T T' φ - d0 K.Oc γ T T' φ, fun T T' φ h ↦ sub_eq_zero.2 (hγ T T' φ h), fun T T' T'' φ ψ ↦ ?_⟩` and prove the remaining obligations. Establish `e1` using `hd T T' T'' φ ψ`. Establish `e2 : d0 K.Oc γ T T'' (φ ≫ ψ) = mp K.Oc ψ (d0 K.Oc γ T T' φ) + d0 K.Oc γ T' T'' ψ` using `commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc γ φ ψ`. Rewrite `e1` using `[d1_apply]`.

Rewrite using `[map_sub]`. Take the linear combination `e1 + e2`. Use `choose S s s' hs hs' hss using Charts.exists_shift_retraction H3`. Establish `hκ : ∀ (n : Λ) (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = n → c' T T' φ = c' _ T' (s n T')`. Introduce `n T T' φ h`.

Establish `h0 : Charts.Hom.deg (φ ≫ s' n T') = 0` using `by rw [Charts.comp_deg, h, hs', add_neg_cancel]`. Use `hd' _ _ _ (φ ≫ s' n T') (s n T')` as an intermediate fact. Rewrite `this` using `[hc0 _ _ _ h0, h0, Category.assoc, hss, Category.comp_id, map_zero, map_zero, AddMonoidHom.zero_apply, map_zero]`. Take the linear combination `-this`. Establish `hr : ∀ n : Λ, ∃ r : Hol F.V, ∀ T, c' _ T (s n T) = algebraMap (Hol F.V) (K.Oc.obj T) r` using `fun n ↦ H2 (fun T ↦ c' _ T (s n T)) fun T T' φ h ↦ by`.

Use `hd' _ _ _ (s n T) φ` as an intermediate fact. Rewrite `this` using `[hc0 _ _ _ h, h, map_zero, map_zero, hκ n _ _ (s n T ≫ φ) (by rw [Charts.comp_deg, h, hs, add_zero])]`. Take the linear combination `this`. Use `choose r hr using hr`. Establish `main : ∀ (a b : Λ) (T : K.Obj), algebraMap (Hol F.V) (K.Oc.obj T) (β a b) = algebraMap (Hol F.V) (K.Oc.obj T) (r a - r (a + b) + r b)`.

Introduce `a b T`. Use `hd' _ _ _ (s a (S b T)) (s b T)` as an intermediate fact. Rewrite `this` using `[hκ (a + b) _ _ (s a (S b T) ≫ s b T) (by rw [Charts.comp_deg, hs, hs]), hr, hr, hr, hs, hs, AlgHom.commutes]`. Rewrite using `[← this, map_add, map_sub]`. Use `Charts.eq_of_cst_eq hR fun k ↦ ?_` and prove the remaining obligations.

Use `(main l m (K.triv k)).trans (Eq.trans ?_ (main m l (K.triv k)).symm)` and prove the remaining obligations. Use `congr 1`. Rewrite using `[add_comm m l]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem const_biadditive_coboundary_symm : ∀ {I : Type} [Fintype I] {g : ℕ} {Λ : Type} [AddCommGroup Λ] {F : Fam I g Λ} (K : Charts F), (∀ c : C1 K.Oc, (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), φ.deg = 0 → ψ.deg = 0 → c T T'' (φ ≫ ψ) = mp K.Oc ψ (c T T' φ) + c T' T'' ψ) → ∃ γ : C0 K.Oc, ∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c T T' φ = d0 K.Oc γ T T' φ) → (∀ γ : C0 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → mp K.Oc φ (γ T) = γ T') → ∃ r : Hol F.V, ∀ T, γ T = algebraMap (Hol F.V) (K.Oc.obj T) r) → (∀ l k', ∃ k, K.le l k' k ∧ K.le (-l) k k') → K.Rich → ∀ (β : Λ →+ Λ →+ Hol F.V) (c : C1 K.Oc), (∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), d1 K.Oc c T T' T'' φ ψ = algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg)) → ∀ l m, β l m = β m l := by
  intro I _ g Λ _ F K H1 H2 H3 hR β c hd l m
  obtain ⟨γ, hγ⟩ := H1 c fun T T' T'' φ ψ h h' ↦ by
    have := hd T T' T'' φ ψ
    rw [d1_apply, h', map_zero, map_zero] at this
    linear_combination -this
  obtain ⟨c', hc0, hd'⟩ : ∃ c' : C1 K.Oc, (∀ (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = 0 → c' T T' φ = 0) ∧
      ∀ (T T' T'' : K.Obj) (φ : T ⟶ T') (ψ : T' ⟶ T''), mp K.Oc ψ (c' T T' φ) - c' T T'' (φ ≫ ψ) + c' T' T'' ψ =
        algebraMap (Hol F.V) (K.Oc.obj T'') (β φ.deg ψ.deg) := by
    refine ⟨fun T T' φ ↦ c T T' φ - d0 K.Oc γ T T' φ, fun T T' φ h ↦ sub_eq_zero.2 (hγ T T' φ h),
      fun T T' T'' φ ψ ↦ ?_⟩
    have e1 := hd T T' T'' φ ψ
    have e2 : d0 K.Oc γ T T'' (φ ≫ ψ) = mp K.Oc ψ (d0 K.Oc γ T T' φ) + d0 K.Oc γ T' T'' ψ := commAlgFunctorCoboundaryZero_mem_cocyclesOne K.Oc γ φ ψ
    rw [d1_apply] at e1
    rw [map_sub]
    linear_combination e1 + e2
  choose S s s' hs hs' hss using Charts.exists_shift_retraction H3
  have hκ : ∀ (n : Λ) (T T' : K.Obj) (φ : T ⟶ T'), φ.deg = n → c' T T' φ = c' _ T' (s n T') := by
    intro n T T' φ h
    have h0 : Charts.Hom.deg (φ ≫ s' n T') = 0 := by rw [Charts.comp_deg, h, hs', add_neg_cancel]
    have := hd' _ _ _ (φ ≫ s' n T') (s n T')
    rw [hc0 _ _ _ h0, h0, Category.assoc, hss, Category.comp_id, map_zero, map_zero, AddMonoidHom.zero_apply,
      map_zero] at this
    linear_combination -this
  have hr : ∀ n : Λ, ∃ r : Hol F.V, ∀ T, c' _ T (s n T) = algebraMap (Hol F.V) (K.Oc.obj T) r := fun n ↦
    H2 (fun T ↦ c' _ T (s n T)) fun T T' φ h ↦ by
      have := hd' _ _ _ (s n T) φ
      rw [hc0 _ _ _ h, h, map_zero, map_zero,
        hκ n _ _ (s n T ≫ φ) (by rw [Charts.comp_deg, h, hs, add_zero])] at this
      linear_combination this
  choose r hr using hr
  have main : ∀ (a b : Λ) (T : K.Obj), algebraMap (Hol F.V) (K.Oc.obj T) (β a b) =
      algebraMap (Hol F.V) (K.Oc.obj T) (r a - r (a + b) + r b) := by
    intro a b T
    have := hd' _ _ _ (s a (S b T)) (s b T)
    rw [hκ (a + b) _ _ (s a (S b T) ≫ s b T) (by rw [Charts.comp_deg, hs, hs]), hr, hr, hr, hs, hs,
      AlgHom.commutes] at this
    rw [← this, map_add, map_sub]
  refine Charts.eq_of_cst_eq hR fun k ↦ ?_
  refine (main l m (K.triv k)).trans (Eq.trans ?_ (main m l (K.triv k)).symm)
  congr 1
  rw [add_comm m l]
  ring

end GlobalTheory.AnPer
