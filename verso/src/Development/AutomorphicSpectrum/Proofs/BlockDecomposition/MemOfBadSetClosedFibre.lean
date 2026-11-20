import Mathlib
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.UniformVanishing
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.SubsetOfClosedFibre
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.QuasicoherentSupSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.IdealPowerSubobjectSectionsStatement
import Development.AutomorphicSpectrum.Proofs.BlockDecomposition.ArtinReesClosedSystem
open CategoryTheory CategoryTheory.Limits AlgebraicGeometry GroundTheory.Arith.SchemeCoh GlobalTheory.CompanionTheory.GE

set_option autoImplicit false

noncomputable section

namespace GlobalTheory.CompanionTheory.GE.PSupp

/- English proof (translation)
Establish `h` using `hV.fromSpec_app_of_le ⊤ le_top`. Establish `e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _` using `fun i => by`. Rewrite using `[Subsingleton.elim i (𝟙 _)]`. Simplify using the standard rewrite rules. Use `h.trans ?_` and prove the remaining obligations.

Use `erw [e, Category.comp_id]`. Both sides reduce to the same expression.
-/
lemma fromSpec_appTop_eq {X : Scheme.{0}} {V : X.Opens} (hV : IsAffineOpen V) :
    hV.fromSpec.appTop = X.presheaf.map (homOfLE le_top).op ≫ (Scheme.ΓSpecIso Γ(X, V)).inv := by
  have h := hV.fromSpec_app_of_le ⊤ le_top
  have e : ∀ i : (⊤ : (Spec Γ(X, V)).Opens) ⟶ ⊤, (Spec Γ(X, V)).presheaf.map i.op = 𝟙 _ := fun i => by
    rw [Subsingleton.elim i (𝟙 _)]
    simp
  refine h.trans ?_
  erw [e, Category.comp_id]
  rfl

/- English proof (translation)
Establish `key : (Scheme.ΓSpecIso (.of A)).inv ≫ (X ↘ Spec (.of A)).appTop ≫ X.presheaf.map (homOfLE le_top).op = CommRingCat.ofHom (toFunctions (A` using `A) V) := by`. Use extensionality with `r`. Both sides reduce to the same expression. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[Scheme.Hom.comp_appTop, fromSpec_appTop_eq, ← cancel_epi (Scheme.ΓSpecIso (.of A)).inv, ← Scheme.ΓSpecIso_inv_naturality, ← key]`.

Simplify using `only [Category.assoc]`. Both sides reduce to the same expression.
-/
lemma fromSpec_comp_base {A : Type} [CommRing A] {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens}
    (hV : IsAffineOpen V) :
    hV.fromSpec ≫ (X ↘ Spec (.of A)) = Spec.map (CommRingCat.ofHom (toFunctions (A := A) V)) := by
  have key : (Scheme.ΓSpecIso (.of A)).inv ≫ (X ↘ Spec (.of A)).appTop ≫
      X.presheaf.map (homOfLE le_top).op = CommRingCat.ofHom (toFunctions (A := A) V) := by
    ext r
    rfl
  apply ext_of_isAffine
  rw [Scheme.Hom.comp_appTop, fromSpec_appTop_eq,
    ← cancel_epi (Scheme.ΓSpecIso (.of A)).inv, ← Scheme.ΓSpecIso_inv_naturality, ← key]
  simp only [Category.assoc]
  rfl

/- English proof (translation)
Use `set p := hV.primeIdealOf ⟨x, hxV⟩ with hp`. Establish `hpx : hV.fromSpec p = x` using `hV.fromSpec_primeIdealOf ⟨x, hxV⟩`. Establish `hcomp : (X ↘ Spec (.of A)).base x = (Spec.map (CommRingCat.ofHom (toFunctions (A` using `A) V))).base p := by`. Rewrite using `[← fromSpec_comp_base hV, ← hpx]`. Both sides reduce to the same expression.

Establish `hle : Ideal.map (toFunctions (A` using `A) V) I ≤ p.asIdeal := by`. Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `a ha`. Use `hI ha` as an intermediate fact. Rewrite `this` using `[hcomp]`.

Conclude with `this`. Establish `hrp : r ∉ p.asIdeal` using `fun h => p.isPrime.ne_top ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.sub_mem h (hle hr)))`. Rewrite using `[← hV.fromSpec_image_basicOpen r]`. Conclude with `⟨p, hrp, hpx⟩`.
-/
lemma basicOpen_of_sub_one_mem {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A)
    {X : Scheme.{0}} [X.Over (Spec (.of A))] {V : X.Opens} (hV : IsAffineOpen V) {x : X} (hxV : x ∈ V)
    (hI : I ≤ ((X ↘ Spec (.of A)).base x).asIdeal) {r : Γ(X, V)}
    (hr : r - 1 ∈ Ideal.map (toFunctions (A := A) V) I) : x ∈ X.basicOpen r := by
  set p := hV.primeIdealOf ⟨x, hxV⟩ with hp
  have hpx : hV.fromSpec p = x := hV.fromSpec_primeIdealOf ⟨x, hxV⟩
  have hcomp : (X ↘ Spec (.of A)).base x =
      (Spec.map (CommRingCat.ofHom (toFunctions (A := A) V))).base p := by
    rw [← fromSpec_comp_base hV, ← hpx]
    rfl
  have hle : Ideal.map (toFunctions (A := A) V) I ≤ p.asIdeal := by
    rw [Ideal.map_le_iff_le_comap]
    intro a ha
    have := hI ha
    rw [hcomp] at this
    exact this
  have hrp : r ∉ p.asIdeal := fun h => p.isPrime.ne_top
    ((Ideal.eq_top_iff_one _).2 (by simpa using p.asIdeal.sub_mem h (hle hr)))
  rw [← hV.fromSpec_image_basicOpen r]
  exact ⟨p, hrp, hpx⟩

/- English proof (translation)
Introduce `A _ _ I X _ P hP Bb hBq K hK h x hx hI`. Assume the negation of the conclusion as `hxK`. Take `⟨W, ⟨V, hV, rfl⟩, hxV, hVK⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ Kᶜ from hxK) hK.isOpen_compl`. Establish `hV' : IsAffineOpen V` using `hV`. Establish `hdisj : Disjoint (V : Set X) K` using `Set.disjoint_left.2 fun y hy hyK => hVK hy hyK`.

Set `J : Ideal Γ(X, V)` to `Ideal.map (toFunctions (A := A) V) I`. Set `N : Submodule Γ(X, V) Γ(P, V)` to `{ carrier := secs Bb V add_mem' := fun hx hy => GlobalTheory.CompanionTheory.GE.Comb.secs_add hx hy zero_mem' := ⟨0, map_zero _⟩ smul_mem' := fun r _ hx => GlobalTheory.CompanionTheory.GE.Comb.secs_smul r hx }`. Establish `hsum : ∀ m : Γ(P, V), ∃ s ∈ N, ∃ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)), m = s + t`. Introduce `m`. Establish `hm : m ∈ secs (Bb ⊔ powSub I P 1) V` using `by rw [h V hdisj]; trivial`.

Rewrite `hm` using `[(GlobalTheory.T.quasicoherent_sup_sections hP.1 Bb (powSub I P 1) hBq (GlobalTheory.CompanionTheory.GE.Comb.qc_pow I hP.1 1)).2 V hV', GlobalTheory.T.ideal_power_subobject_sections I P hP.1 1 V hV', pow_one]`. Take `⟨s, hs, t, ht, rfl⟩` from `hm`. Conclude with `⟨s, hs, t, ht, rfl⟩`. Use `haveI : Module.Finite Γ(X, V) Γ(P, V) := hP.2 V hV'`. Establish `hfg : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)).FG` using `Module.Finite.fg_top`.

Establish `hle : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)) ≤ J • ⊤`. Introduce `z _`. Take `⟨m, rfl⟩` from `N.mkQ_surjective z`. Take `⟨s, hs, t, ht, rfl⟩` from `hsum m`. Establish `h1 : N.mkQ (s + t) = N.mkQ t`.

Establish `h0 : N.mkQ s = 0` using `(Submodule.Quotient.mk_eq_zero N).2 hs`. Rewrite using `[map_add, h0, zero_add]`. Rewrite using `[h1]`. Establish `h2 : N.mkQ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)).map N.mkQ` using `⟨t, ht, rfl⟩`. Rewrite `h2` using `[Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ]`.

Conclude with `h2`. Take `⟨r, hr1, hr⟩` from `Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤ hfg hle`. Establish `hrN : ∀ m : Γ(P, V), r • m ∈ N` using `fun m => by`. Use `hr (N.mkQ m) trivial` as an intermediate fact. Rewrite `this` using `[← map_smul]`.

Conclude with `(Submodule.Quotient.mk_eq_zero N).1 this`. Establish `hxD : x ∈ X.basicOpen r` using `basicOpen_of_sub_one_mem I hV' hxV hI hr1`. Establish `hD : IsAffineOpen (X.basicOpen r)` using `hV'.basicOpen r`. Use `hx ⟨X.basicOpen r, hD⟩ ?_ hxD` and prove the remaining obligations. Use `Set.eq_univ_of_forall fun m => ?_` and prove the remaining obligations.

Use `haveI : P.IsQuasicoherent := hP.1`. Take `⟨e, m', hm'⟩` from `qcoh_exists_res_eq P hV' r m`. Take `⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le r) r)` from `X.toRingedSpace.isUnit_res_basicOpen r`. Take `⟨b, hb⟩` from `hrN m'`. Establish `h3 : resF P (X.basicOpen_le r) (r • m') ∈ secs Bb (X.basicOpen r)`.

Rewrite using `[← hb]`. Conclude with `⟨resF _ (X.basicOpen_le r) b, (resF_app Bb.arrow (X.basicOpen_le r) b).symm⟩`. Rewrite `h3` using `[resF_smul, hm', ← hu, smul_smul, ← pow_succ']`. Establish `h4` using `GlobalTheory.CompanionTheory.GE.Comb.secs_smul (((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) : Γ(X, X.basicOpen r)) ^ (e + 1)) h3`. Rewrite `h4` using `[smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul]`. Then use the resulting hypothesis.
-/
theorem mem_of_badSet_closedFibre : ∀ {A : Type} [CommRing A] [IsNoetherianRing A] (I : Ideal A) {X : Scheme.{0}} [X.Over (Spec (.of A))] {P : X.Modules}, IsCoherent P → ∀ (Bb : Subobject P), (Bb : X.Modules).IsQuasicoherent → ∀ (K : Set X), IsClosed K → (∀ V : X.Opens, Disjoint (V : Set X) K → secs (Bb ⊔ powSub I P 1) V = Set.univ) → ∀ x ∈ GlobalTheory.CompanionTheory.GE.PSupp.badSet Bb, I ≤ ((X ↘ Spec (.of A)).base x).asIdeal → x ∈ K := by
  intro A _ _ I X _ P hP Bb hBq K hK h x hx hI
  by_contra hxK
  obtain ⟨W, ⟨V, hV, rfl⟩, hxV, hVK⟩ :=
    X.isBasis_affineOpens.exists_subset_of_mem_open (show x ∈ Kᶜ from hxK) hK.isOpen_compl
  have hV' : IsAffineOpen V := hV
  have hdisj : Disjoint (V : Set X) K := Set.disjoint_left.2 fun y hy hyK => hVK hy hyK
  let J : Ideal Γ(X, V) := Ideal.map (toFunctions (A := A) V) I
  let N : Submodule Γ(X, V) Γ(P, V) :=
    { carrier := secs Bb V
      add_mem' := fun hx hy => GlobalTheory.CompanionTheory.GE.Comb.secs_add hx hy
      zero_mem' := ⟨0, map_zero _⟩
      smul_mem' := fun r _ hx => GlobalTheory.CompanionTheory.GE.Comb.secs_smul r hx }
  have hsum : ∀ m : Γ(P, V), ∃ s ∈ N, ∃ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)), m = s + t := by
    intro m
    have hm : m ∈ secs (Bb ⊔ powSub I P 1) V := by rw [h V hdisj]; trivial
    rw [(GlobalTheory.T.quasicoherent_sup_sections hP.1 Bb (powSub I P 1) hBq (GlobalTheory.CompanionTheory.GE.Comb.qc_pow I hP.1 1)).2 V hV',
      GlobalTheory.T.ideal_power_subobject_sections I P hP.1 1 V hV', pow_one] at hm
    obtain ⟨s, hs, t, ht, rfl⟩ := hm
    exact ⟨s, hs, t, ht, rfl⟩
  haveI : Module.Finite Γ(X, V) Γ(P, V) := hP.2 V hV'
  have hfg : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)).FG := Module.Finite.fg_top
  have hle : (⊤ : Submodule Γ(X, V) (Γ(P, V) ⧸ N)) ≤ J • ⊤ := by
    intro z _
    obtain ⟨m, rfl⟩ := N.mkQ_surjective z
    obtain ⟨s, hs, t, ht, rfl⟩ := hsum m
    have h1 : N.mkQ (s + t) = N.mkQ t := by
      have h0 : N.mkQ s = 0 := (Submodule.Quotient.mk_eq_zero N).2 hs
      rw [map_add, h0, zero_add]
    rw [h1]
    have h2 : N.mkQ t ∈ (J • ⊤ : Submodule Γ(X, V) Γ(P, V)).map N.mkQ := ⟨t, ht, rfl⟩
    rw [Submodule.map_smul'', Submodule.map_top, Submodule.range_mkQ] at h2
    exact h2
  obtain ⟨r, hr1, hr⟩ := Submodule.exists_sub_one_mem_and_smul_eq_zero_of_fg_of_le_smul J ⊤ hfg hle
  have hrN : ∀ m : Γ(P, V), r • m ∈ N := fun m => by
    have := hr (N.mkQ m) trivial
    rw [← map_smul] at this
    exact (Submodule.Quotient.mk_eq_zero N).1 this
  have hxD : x ∈ X.basicOpen r := basicOpen_of_sub_one_mem I hV' hxV hI hr1
  have hD : IsAffineOpen (X.basicOpen r) := hV'.basicOpen r
  refine hx ⟨X.basicOpen r, hD⟩ ?_ hxD
  refine Set.eq_univ_of_forall fun m => ?_
  haveI : P.IsQuasicoherent := hP.1
  obtain ⟨e, m', hm'⟩ := qcoh_exists_res_eq P hV' r m
  obtain ⟨u, hu⟩ : IsUnit (resO (X.basicOpen_le r) r) := X.toRingedSpace.isUnit_res_basicOpen r
  obtain ⟨b, hb⟩ := hrN m'
  have h3 : resF P (X.basicOpen_le r) (r • m') ∈ secs Bb (X.basicOpen r) := by
    rw [← hb]
    exact ⟨resF _ (X.basicOpen_le r) b, (resF_app Bb.arrow (X.basicOpen_le r) b).symm⟩
  rw [resF_smul, hm', ← hu, smul_smul, ← pow_succ'] at h3
  have h4 := GlobalTheory.CompanionTheory.GE.Comb.secs_smul (((u⁻¹ : (Γ(X, X.basicOpen r))ˣ) : Γ(X, X.basicOpen r)) ^ (e + 1)) h3
  rwa [smul_smul, ← mul_pow, Units.inv_mul, one_pow, one_smul] at h4

end GlobalTheory.CompanionTheory.GE.PSupp
