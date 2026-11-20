import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ChartPullbacks.BaseChangeKernels.Affine
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.BaseChangeSpan

/- English proof (translation)
Establish `hx : x ∈ Subring.closure (Set.range A ∪ Set.range B)` using `h ▸ Subring.mem_top x`. Proceed by induction on `hx using Subring.closure_induction with`. Consider the case `mem y hy`. Break down `hy with ⟨a, rfl⟩ | ⟨r, rfl⟩` into its components or cases. Conclude with `⟨1, fun _ => a, fun _ => 1, by simp⟩`.

Conclude with `⟨1, fun _ => 1, fun _ => r, by simp⟩`. Consider the case `zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩`. Consider the case `one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩`. Consider the case `add y z _ _ hy hz`. Take `⟨n, a, r, rfl⟩` from `hy`.

Take `⟨m, b, t, rfl⟩` from `hz`. Use `⟨n + m, Fin.append a b, Fin.append r t, ?_⟩` and prove the remaining obligations. Rewrite using `[Fin.sum_univ_add]`. Simplify using `[Fin.append_left, Fin.append_right]`. Consider the case `neg y _ hy`.

Take `⟨n, a, r, rfl⟩` from `hy`. Conclude with `⟨n, fun i => -a i, r, by simp [Finset.sum_neg_distrib]⟩`. Consider the case `mul y z _ _ hy hz`. Take `⟨n, a, r, rfl⟩` from `hy`. Take `⟨m, b, t, rfl⟩` from `hz`.

Use `⟨n * m, fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2, fun k => r (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2, ?_⟩` and prove the remaining obligations. Rewrite using `[← finProdFinEquiv.sum_comp, Finset.sum_mul_sum, ← Finset.sum_product']`. Use `Finset.sum_congr (by simp) fun p _ => ?_` and prove the remaining obligations. Simplify using `only [Equiv.symm_apply_apply, map_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
theorem exists_sum_mul_of_closure {S S' T : Type} [CommRing S] [CommRing S'] [CommRing T]
    (A : S →+* T) (B : S' →+* T) (h : Subring.closure (Set.range A ∪ Set.range B) = ⊤) (x : T) :
    ∃ (n : ℕ) (a : Fin n → S) (r : Fin n → S'), x = ∑ i, A (a i) * B (r i) := by
  have hx : x ∈ Subring.closure (Set.range A ∪ Set.range B) := h ▸ Subring.mem_top x
  induction hx using Subring.closure_induction with
  | mem y hy =>
    rcases hy with ⟨a, rfl⟩ | ⟨r, rfl⟩
    · exact ⟨1, fun _ => a, fun _ => 1, by simp⟩
    · exact ⟨1, fun _ => 1, fun _ => r, by simp⟩
  | zero => exact ⟨0, Fin.elim0, Fin.elim0, by simp⟩
  | one => exact ⟨1, fun _ => 1, fun _ => 1, by simp⟩
  | add y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n + m, Fin.append a b, Fin.append r t, ?_⟩
    rw [Fin.sum_univ_add]
    simp [Fin.append_left, Fin.append_right]
  | neg y _ hy =>
    obtain ⟨n, a, r, rfl⟩ := hy
    exact ⟨n, fun i => -a i, r, by simp [Finset.sum_neg_distrib]⟩
  | mul y z _ _ hy hz =>
    obtain ⟨n, a, r, rfl⟩ := hy
    obtain ⟨m, b, t, rfl⟩ := hz
    refine ⟨n * m, fun k => a (finProdFinEquiv.symm k).1 * b (finProdFinEquiv.symm k).2,
      fun k => r (finProdFinEquiv.symm k).1 * t (finProdFinEquiv.symm k).2, ?_⟩
    rw [← finProdFinEquiv.sum_comp, Finset.sum_mul_sum, ← Finset.sum_product']
    refine Finset.sum_congr (by simp) fun p _ => ?_
    simp only [Equiv.symm_apply_apply, map_mul]
    ring

end GlobalTheory.BaseChangeSpan

namespace GlobalTheory.BaseChangeSpan

/- English proof (translation)
Introduce `R R₁ _ _ ρ P p V hV x`. Establish `sq : IsPullback (pullback.snd p (spMap ρ)) (pullback.fst p (spMap ρ)) (spMap ρ) p` using `(IsPullback.of_hasPullback p (spMap ρ)).flip`. Establish `hle : V ≤ p ⁻¹ᵁ ⊤` using `by simp`. Establish `hleG : (pullback.fst p (spMap ρ)) ⁻¹ᵁ V ≤ (pullback.snd p (spMap ρ)) ⁻¹ᵁ ((spMap ρ) ⁻¹ᵁ ⊤)` using `by simp`. Establish `po` using `ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) hV hle hleG`.

Establish `hcl` using `CommRingCat.closure_range_union_range_eq_top_of_isPushout po`. Establish `htop : (⊤ : (Sp R₁).Opens) ≤ (spMap ρ) ⁻¹ᵁ ⊤` using `by simp`. Establish `hsub : Set.range ((pullback.snd p (spMap ρ)).appLE ((spMap ρ) ⁻¹ᵁ ⊤) _ hleG).hom ⊆ Set.range (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom)`. Introduce and unpack `_ ⟨y, rfl⟩`. Use `⟨(Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom ((Sp R₁).presheaf.map (homOfLE htop).op y), ?_⟩` and prove the remaining obligations.

Rewrite using `[RingHom.comp_apply]`. Express the relevant statement in the definitionally equal form `((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫ (pullback.snd p (spMap ρ)).appLE ⊤ _ le_top).hom ((Sp R₁).presheaf.map (homOfLE htop).op y) = _`. Rewrite using `[Iso.hom_inv_id_assoc, ← CommRingCat.comp_apply]`. Establish `h` using `Scheme.Hom.map_appLE (pullback.snd p (spMap ρ)) (V := (pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top (homOfLE htop).op`. Conclude with `RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) y`.

Take `⟨n, a, r, hx⟩` from `exists_sum_mul_of_closure ((pullback.fst p (spMap ρ)).app V).hom (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom) (by`. Rewrite using `[eq_top_iff, ← hcl]`. Conclude with `Subring.closure_mono (Set.union_subset (hsub.trans Set.subset_union_right) Set.subset_union_left))`. Use `x`. Conclude with `⟨n, a, r, hx⟩`.
-/
theorem sections_preimage_affine_eq_sum : ∀ (R R₁ : Type) [CommRing R] [CommRing R₁] (ρ : R →+* R₁) (P : Scheme.{0}) (p : P ⟶ Sp R) (V : P.Opens), IsAffineOpen V → ∀ x : Γ(pullback p (spMap ρ), (pullback.fst p (spMap ρ)) ⁻¹ᵁ V), ∃ (n : ℕ) (a : Fin n → Γ(P, V)) (r : Fin n → R₁), x = ∑ i, ((pullback.fst p (spMap ρ)).app V).hom (a i) * ((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom ((Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom (r i)) := by
  intro R R₁ _ _ ρ P p V hV x
  have sq : IsPullback (pullback.snd p (spMap ρ)) (pullback.fst p (spMap ρ)) (spMap ρ) p :=
    (IsPullback.of_hasPullback p (spMap ρ)).flip
  have hle : V ≤ p ⁻¹ᵁ ⊤ := by simp
  have hleG : (pullback.fst p (spMap ρ)) ⁻¹ᵁ V ≤
      (pullback.snd p (spMap ρ)) ⁻¹ᵁ ((spMap ρ) ⁻¹ᵁ ⊤) := by simp
  have po := ReciprocityTheory.ChartRestriction.G.Out.GtBCPf.isPushout_appLE sq inferInstance (isAffineOpen_top _) hV hle hleG
  have hcl := CommRingCat.closure_range_union_range_eq_top_of_isPushout po
  have htop : (⊤ : (Sp R₁).Opens) ≤ (spMap ρ) ⁻¹ᵁ ⊤ := by simp
  have hsub : Set.range ((pullback.snd p (spMap ρ)).appLE ((spMap ρ) ⁻¹ᵁ ⊤) _ hleG).hom ⊆
      Set.range (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom) := by
    rintro _ ⟨y, rfl⟩
    refine ⟨(Scheme.ΓSpecIso (CommRingCat.of R₁)).hom.hom ((Sp R₁).presheaf.map (homOfLE htop).op y), ?_⟩
    rw [RingHom.comp_apply]
    change ((Scheme.ΓSpecIso (CommRingCat.of R₁)).hom ≫ (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv ≫
      (pullback.snd p (spMap ρ)).appLE ⊤ _ le_top).hom ((Sp R₁).presheaf.map (homOfLE htop).op y) = _
    rw [Iso.hom_inv_id_assoc, ← CommRingCat.comp_apply]
    have h := Scheme.Hom.map_appLE (pullback.snd p (spMap ρ))
      (V := (pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top (homOfLE htop).op
    exact RingHom.congr_fun (congrArg CommRingCat.Hom.hom h) y
  obtain ⟨n, a, r, hx⟩ := exists_sum_mul_of_closure ((pullback.fst p (spMap ρ)).app V).hom
    (((pullback.snd p (spMap ρ)).appLE ⊤ ((pullback.fst p (spMap ρ)) ⁻¹ᵁ V) le_top).hom.comp
        (Scheme.ΓSpecIso (CommRingCat.of R₁)).inv.hom)
    (by
      rw [eq_top_iff, ← hcl]
      exact Subring.closure_mono (Set.union_subset (hsub.trans Set.subset_union_right)
        Set.subset_union_left))
    x
  exact ⟨n, a, r, hx⟩

end GlobalTheory.BaseChangeSpan
