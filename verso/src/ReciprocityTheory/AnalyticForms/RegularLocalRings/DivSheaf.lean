import ReciprocityTheory.AnalyticForms.RegularLocalRings.DivSheafA

namespace ReciprocityTheory.AnForm.R

open AlgebraicGeometry CategoryTheory

noncomputable section

universe u

section LocGen

variable {W : Scheme.{u}} {ι' : Type*} {V : ι' → W.Opens} {g : ∀ c, Γ(W, V c)}

/- English proof (translation)
Establish `hc : ∀ z : U.1, ∃ t : Γ(W, U), ∃ c, W.basicOpen t ≤ V c ∧ (z : W) ∈ W.basicOpen t`. Introduce `z`. Take `⟨c, hc⟩` from `hV z`. Take `⟨t, ht, hzt⟩` from `U.2.exists_basicOpen_le ⟨(z : W), hc⟩ z.2`. Conclude with `⟨t, c, ht, hzt⟩`.

Use `choose t c ht hzt using hc`. Establish `hm : ∀ z : U.1, ∃ m : ℕ, ∀ y (hy : y ∈ W.basicOpen (t z)), W.presheaf.germ U.1 y (W.basicOpen_le (t z) hy) (s ^ m * a) ∈ dsK V g y` using `fun z => ds_local hg s a ha (c z) (t z) (ht z)`. Use `choose m hm using hm`. Take `⟨F, hF⟩` from `U.2.isCompact.elim_finite_subcover (fun z : U.1 => (W.basicOpen (t z) : Set W)) (fun z => (W.basicOpen (t z)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hzt ⟨y, hy⟩⟩)`. Use `⟨∑ z ∈ F, m z, mem_dsJ.2 fun y hy => ?_⟩` and prove the remaining obligations.

Take `⟨z, hzF, hyz⟩` from `Set.mem_iUnion₂.1 (hF hy)`. Establish `hle : m z ≤ ∑ z ∈ F, m z` using `Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzF`. Establish `h1` using `hm z y hyz`. Rewrite using `[← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]`. Conclude with `Ideal.mul_mem_left _ _ h1`.
-/
lemma ds_core (hV : ∀ x : W, ∃ c, x ∈ V c)
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    {U : W.affineOpens} (s a : Γ(W, U))
    (ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen s → W.presheaf.germ U.1 z hz a ∈ dsK V g z) :
    ∃ m : ℕ, s ^ m * a ∈ dsJ V g U := by
  classical
  have hc : ∀ z : U.1, ∃ t : Γ(W, U), ∃ c, W.basicOpen t ≤ V c ∧ (z : W) ∈ W.basicOpen t := by
    intro z
    obtain ⟨c, hc⟩ := hV z
    obtain ⟨t, ht, hzt⟩ := U.2.exists_basicOpen_le ⟨(z : W), hc⟩ z.2
    exact ⟨t, c, ht, hzt⟩
  choose t c ht hzt using hc
  have hm : ∀ z : U.1, ∃ m : ℕ, ∀ y (hy : y ∈ W.basicOpen (t z)),
      W.presheaf.germ U.1 y (W.basicOpen_le (t z) hy) (s ^ m * a) ∈ dsK V g y :=
    fun z => ds_local hg s a ha (c z) (t z) (ht z)
  choose m hm using hm
  obtain ⟨F, hF⟩ := U.2.isCompact.elim_finite_subcover
    (fun z : U.1 => (W.basicOpen (t z) : Set W))
    (fun z => (W.basicOpen (t z)).isOpen) (fun y hy => Set.mem_iUnion.2 ⟨⟨y, hy⟩, hzt ⟨y, hy⟩⟩)
  refine ⟨∑ z ∈ F, m z, mem_dsJ.2 fun y hy => ?_⟩
  obtain ⟨z, hzF, hyz⟩ := Set.mem_iUnion₂.1 (hF hy)
  have hle : m z ≤ ∑ z ∈ F, m z := Finset.single_le_sum (fun _ _ => Nat.zero_le _) hzF
  have h1 := hm z y hyz
  rw [← Nat.sub_add_cancel hle, pow_add, mul_assoc, map_mul]
  exact Ideal.mul_mem_left _ _ h1

/- English proof (translation)
Apply `le_antisymm` to reduce the goal to its premises. Use `Ideal.map_le_of_le_comap fun b hb => ?_` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `(W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b ∈ dsJ V g (W.affineBasicOpen f)`. Use `mem_dsJ.2 fun y hy => ?_` and prove the remaining obligations. Establish `h1` using `(mem_dsJ.1 hb) y (W.basicOpen_le f hy)`.

Establish `e : W.presheaf.germ (W.affineBasicOpen f).1 y hy ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b) = W.presheaf.germ U.1 y (W.basicOpen_le f hy) b` using `TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) y hy b`. Rewrite using `[e]`. Conclude with `h1`. Introduce `b hb`. Use `letI := (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom.toAlgebra`.

Use `haveI := U.2.isLocalization_basicOpen f`. Take `⟨⟨a, s'⟩, hab⟩` from `IsLocalization.surj (Submonoid.powers f) b`. Take `⟨n, hn⟩` from `s'.2`. Simplify using `only [RingHom.algebraMap_toAlgebra, ← hn] at hab`. Establish `ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen f → W.presheaf.germ U.1 z hz a ∈ dsK V g z`.

Introduce `z hz hzf`. Establish `h1` using `(mem_dsJ.1 hb) z hzf`. Establish `e1 : W.presheaf.germ (W.basicOpen f) z hzf ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom a) = W.presheaf.germ U.1 z hz a` using `TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf a`. Establish `e2 : W.presheaf.germ (W.basicOpen f) z hzf ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ n)) = W.presheaf.germ U.1 z hz (f ^ n)` using `TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf (f ^ n)`. Rewrite using `[← e1, ← hab, map_mul, e2]`.

Conclude with `Ideal.mul_mem_right _ _ h1`. Take `⟨m, hm⟩` from `ds_core hV hg f a ha`. Establish `hx : (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) ∈ (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom` using `Ideal.mem_map_of_mem _ hm`. Establish `hu : IsUnit ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n)))`. Rewrite using `[map_pow]`.

Conclude with `(IsLocalization.Away.algebraMap_isUnit f).pow _`. Establish `heq : b * (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n)) = (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a)`. Rewrite using `[map_mul, ← hab, pow_add, map_mul]`. Expand and normalize the polynomial expressions, which then agree. Take `⟨v, hv⟩` from `hu`.

Establish `hb' : b = (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) * ↑v⁻¹`. Rewrite using `[← heq, ← hv, mul_assoc, Units.mul_inv, mul_one]`. Rewrite using `[hb']`. Conclude with `Ideal.mul_mem_right _ _ hx`.
-/
lemma dsJ_basicOpen (hV : ∀ x : W, ∃ c, x ∈ V c)
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c'))
    (U : W.affineOpens) (f : Γ(W, U)) :
    (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom =
      dsJ V g (W.affineBasicOpen f) := by
  apply le_antisymm
  · refine Ideal.map_le_of_le_comap fun b hb => ?_
    change (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b ∈ dsJ V g (W.affineBasicOpen f)
    refine mem_dsJ.2 fun y hy => ?_
    have h1 := (mem_dsJ.1 hb) y (W.basicOpen_le f hy)
    have e : W.presheaf.germ (W.affineBasicOpen f).1 y hy
        ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom b) =
        W.presheaf.germ U.1 y (W.basicOpen_le f hy) b :=
      TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) y hy b
    rw [e]
    exact h1
  · intro b hb
    letI := (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom.toAlgebra
    haveI := U.2.isLocalization_basicOpen f
    obtain ⟨⟨a, s'⟩, hab⟩ := IsLocalization.surj (Submonoid.powers f) b
    obtain ⟨n, hn⟩ := s'.2
    simp only [RingHom.algebraMap_toAlgebra, ← hn] at hab
    have ha : ∀ z (hz : z ∈ U.1), z ∈ W.basicOpen f →
        W.presheaf.germ U.1 z hz a ∈ dsK V g z := by
      intro z hz hzf
      have h1 := (mem_dsJ.1 hb) z hzf
      have e1 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom a) = W.presheaf.germ U.1 z hz a :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf a
      have e2 : W.presheaf.germ (W.basicOpen f) z hzf
          ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ n)) =
            W.presheaf.germ U.1 z hz (f ^ n) :=
        TopCat.Presheaf.germ_res_apply W.presheaf (homOfLE <| W.basicOpen_le f) z hzf (f ^ n)
      rw [← e1, ← hab, map_mul, e2]
      exact Ideal.mul_mem_right _ _ h1
    obtain ⟨m, hm⟩ := ds_core hV hg f a ha
    have hx : (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) ∈
        (dsJ V g U).map (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom :=
      Ideal.mem_map_of_mem _ hm
    have hu : IsUnit ((W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n))) := by
      rw [map_pow]
      exact (IsLocalization.Away.algebraMap_isUnit f).pow _
    have heq : b * (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ (m + n)) =
        (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) := by
      rw [map_mul, ← hab, pow_add, map_mul]
      ring
    obtain ⟨v, hv⟩ := hu
    have hb' : b = (W.presheaf.map (homOfLE <| W.basicOpen_le f).op).hom (f ^ m * a) * ↑v⁻¹ := by
      rw [← heq, ← hv, mul_assoc, Units.mul_inv, mul_one]
    rw [hb']
    exact Ideal.mul_mem_right _ _ hx

end LocGen

/- English proof (translation)
Use `⟨⟨fun U => dsJ V g U, fun U f => dsJ_basicOpen hV hg U f, _, rfl⟩, fun c x hx => ?_⟩` and prove the remaining obligations. Take `⟨U', hU', hxU', hsub⟩` from `exists_isAffineOpen_mem_and_subset hx`. Rewrite using `[ds_stalkId_eq_map _ ⟨U', hU'⟩ x hxU']`. Express the relevant statement in the definitionally equal form `Ideal.map _ (dsJ V g ⟨U', hU'⟩) = _`. Apply `le_antisymm` to reduce the goal to its premises.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Rewrite using `[Ideal.mem_comap, ← dsK_eq hg c hx]`. Conclude with `(mem_dsJ.1 hf) x hxU'`. Rewrite using `[Ideal.span_le, Set.singleton_subset_iff]`.

Establish `hle : U' ≤ V c` using `hsub`. Establish `hr : W.presheaf.map (homOfLE hle).op (g c) ∈ dsJ V g ⟨U', hU'⟩`. Rewrite using `[mem_dsJ]`. Introduce `y hy`. Rewrite using `[dsK_eq hg c (hsub hy)]`.

Apply `Ideal.subset_span` to reduce the goal to its premises. Simplify using the standard rewrite rules. Establish `e : W.presheaf.germ U' x hxU' (W.presheaf.map (homOfLE hle).op (g c)) = W.presheaf.germ (V c) x hx (g c)` using `by simp`. Rewrite using `[← e]`. Conclude with `Ideal.mem_map_of_mem _ hr`.
-/
theorem exists_idealSheaf_of_locGen {W : Scheme.{0}} {ι' : Type} (V : ι' → W.Opens)
    (hV : ∀ x : W, ∃ c, x ∈ V c) (g : ∀ c, Γ(W, V c))
    (hg : ∀ c c' (x : W) (hx : x ∈ V c) (hx' : x ∈ V c'), ∃ u : (W.presheaf.stalk x)ˣ,
      W.presheaf.germ (V c) x hx (g c) = u * W.presheaf.germ (V c') x hx' (g c')) :
    ∃ G : W.IdealSheafData, ∀ c (x : W) (hx : x ∈ V c),
      FinalTheorems.stalkId G x = Ideal.span {W.presheaf.germ (V c) x hx (g c)} := by
  refine ⟨⟨fun U => dsJ V g U, fun U f => dsJ_basicOpen hV hg U f, _, rfl⟩, fun c x hx => ?_⟩
  obtain ⟨U', hU', hxU', hsub⟩ := exists_isAffineOpen_mem_and_subset hx
  rw [ds_stalkId_eq_map _ ⟨U', hU'⟩ x hxU']
  change Ideal.map _ (dsJ V g ⟨U', hU'⟩) = _
  apply le_antisymm
  · rw [Ideal.map_le_iff_le_comap]
    intro f hf
    rw [Ideal.mem_comap, ← dsK_eq hg c hx]
    exact (mem_dsJ.1 hf) x hxU'
  · rw [Ideal.span_le, Set.singleton_subset_iff]
    have hle : U' ≤ V c := hsub
    have hr : W.presheaf.map (homOfLE hle).op (g c) ∈ dsJ V g ⟨U', hU'⟩ := by
      rw [mem_dsJ]
      intro y hy
      rw [dsK_eq hg c (hsub hy)]
      apply Ideal.subset_span
      simp
    have e : W.presheaf.germ U' x hxU' (W.presheaf.map (homOfLE hle).op (g c)) =
        W.presheaf.germ (V c) x hx (g c) := by simp
    rw [← e]
    exact Ideal.mem_map_of_mem _ hr

/- English proof (translation)
Introduce `x`. Take `⟨U0, hU0, hxU0, -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Use `haveI : IsNoetherianRing Γ(W, U0) := IsLocallyNoetherian.component_noetherian ⟨U0, hU0⟩`. Take `⟨t, ht, hst⟩` from `hG x`. Use `letI := (W.presheaf.germ U0 x hxU0).hom.toAlgebra`.

Use `haveI := hU0.isLocalization_stalk ⟨x, hxU0⟩`. Establish `hI : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) = Ideal.span {t}`. Rewrite using `[← hst, ds_stalkId_eq_map G ⟨U0, hU0⟩ x hxU0]`. Both sides reduce to the same expression. Take `⟨y, ⟨h, hh, rfl⟩, c, hyc⟩` from `ds_gen_of_span ((algebraMap Γ(W, U0) (W.presheaf.stalk x)) '' (G.ideal ⟨U0, hU0⟩ : Set Γ(W, U0))) t ht hI`.

Establish `hmap : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) = Ideal.span {algebraMap Γ(W, U0) (W.presheaf.stalk x) h}`. Rewrite using `[hI, hyc, Ideal.span_singleton_mul_left_unit c.isUnit]`. Establish `hnzd : algebraMap Γ(W, U0) (W.presheaf.stalk x) h ∈ nonZeroDivisors (W.presheaf.stalk x)`. Rewrite using `[hyc]`. Conclude with `mul_mem c.isUnit.mem_nonZeroDivisors ht`.

Take `⟨σ, hσ, hT⟩` from `ds_spread (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal _ h hh hmap hnzd`. Use `letI := (W.presheaf.map (homOfLE <| W.basicOpen_le σ).op).hom.toAlgebra`. Use `haveI := hU0.isLocalization_basicOpen σ`. Take `⟨h1, h2⟩` from `hT Γ(W, W.basicOpen σ)`. Use `⟨W.affineBasicOpen (U := ⟨U0, hU0⟩) σ, algebraMap Γ(W, U0) Γ(W, W.basicOpen σ) h, ?_, h2, ?_⟩` and prove the remaining obligations.

Establish `hu` using `(IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x) (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal σ).2 hσ`. Conclude with `(Scheme.mem_basicOpen W σ x hxU0).2 hu`. Rewrite using `[← G.map_ideal_basicOpen ⟨U0, hU0⟩ σ]`. Conclude with `h1`.
-/
theorem effCartier_of_stalkId {W : Scheme.{0}} [IsNoetherian W] (G : W.IdealSheafData)
    (hG : ∀ x : W, ∃ t ∈ nonZeroDivisors (W.presheaf.stalk x), FinalTheorems.stalkId G x = Ideal.span {t}) :
    FinalTheorems.EffCartier G := by
  intro x
  obtain ⟨U0, hU0, hxU0, -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  haveI : IsNoetherianRing Γ(W, U0) := IsLocallyNoetherian.component_noetherian ⟨U0, hU0⟩
  obtain ⟨t, ht, hst⟩ := hG x
  letI := (W.presheaf.germ U0 x hxU0).hom.toAlgebra
  haveI := hU0.isLocalization_stalk ⟨x, hxU0⟩
  have hI : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {t} := by
    rw [← hst, ds_stalkId_eq_map G ⟨U0, hU0⟩ x hxU0]
    rfl
  obtain ⟨y, ⟨h, hh, rfl⟩, c, hyc⟩ := ds_gen_of_span
    ((algebraMap Γ(W, U0) (W.presheaf.stalk x)) '' (G.ideal ⟨U0, hU0⟩ : Set Γ(W, U0))) t ht hI
  have hmap : (G.ideal ⟨U0, hU0⟩).map (algebraMap Γ(W, U0) (W.presheaf.stalk x)) =
      Ideal.span {algebraMap Γ(W, U0) (W.presheaf.stalk x) h} := by
    rw [hI, hyc, Ideal.span_singleton_mul_left_unit c.isUnit]
  have hnzd : algebraMap Γ(W, U0) (W.presheaf.stalk x) h ∈
      nonZeroDivisors (W.presheaf.stalk x) := by
    rw [hyc]
    exact mul_mem c.isUnit.mem_nonZeroDivisors ht
  obtain ⟨σ, hσ, hT⟩ := ds_spread (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal _ h hh hmap hnzd
  letI := (W.presheaf.map (homOfLE <| W.basicOpen_le σ).op).hom.toAlgebra
  haveI := hU0.isLocalization_basicOpen σ
  obtain ⟨h1, h2⟩ := hT Γ(W, W.basicOpen σ)
  refine ⟨W.affineBasicOpen (U := ⟨U0, hU0⟩) σ, algebraMap Γ(W, U0) Γ(W, W.basicOpen σ) h, ?_, h2, ?_⟩
  · have hu := (IsLocalization.AtPrime.isUnit_to_map_iff (W.presheaf.stalk x)
      (hU0.primeIdealOf ⟨x, hxU0⟩).asIdeal σ).2 hσ
    exact (Scheme.mem_basicOpen W σ x hxU0).2 hu
  · rw [← G.map_ideal_basicOpen ⟨U0, hU0⟩ σ]
    exact h1

/- English proof (translation)
Take `⟨U', hU', hxU', -⟩` from `exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial`. Establish `hxU : x ∈ (⟨U', hU'⟩ : W.affineOpens).1` using `hxU'`. Use `(Scheme.IdealSheafData.mem_support_iff_of_mem hxU).trans ?_` and prove the remaining obligations. Rewrite using `[Scheme.mem_zeroLocus_iff, ds_stalkId_eq_map G _ x hxU]`. Prove the components needed by the constructor for the conclusion.

Introduce `h htop`. Choose the witnesses or unpack the hypotheses as in `⟨f, hf, hu⟩ : ∃ f ∈ G.ideal ⟨U', hU'⟩, IsUnit (W.presheaf.germ U' x hxU' f) := by`. Assume the negation of the conclusion as `hno`. Use `push_neg at hno`. Establish `hle : Ideal.map (W.presheaf.germ U' x hxU').hom (G.ideal ⟨U', hU'⟩) ≤ IsLocalRing.maximalIdeal _`.

Rewrite using `[Ideal.map_le_iff_le_comap]`. Introduce `f hf`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 (hno f hf)`. Rewrite `hle` using `[htop]`. Conclude with `(IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)`.

Conclude with `h f hf ((Scheme.mem_basicOpen _ _ _ _).2 hu)`. Introduce `h f hf hxf`. Apply `h` to reduce the goal to its premises. Conclude with `Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf) ((Scheme.mem_basicOpen _ _ _ hxU).1 hxf)`.
-/
theorem mem_support_iff_stalkId {W : Scheme.{0}} (G : W.IdealSheafData) (x : W) :
    x ∈ (G.support : Set W) ↔ FinalTheorems.stalkId G x ≠ ⊤ := by
  obtain ⟨U', hU', hxU', -⟩ := exists_isAffineOpen_mem_and_subset (x := x) (U := ⊤) trivial
  have hxU : x ∈ (⟨U', hU'⟩ : W.affineOpens).1 := hxU'
  refine (Scheme.IdealSheafData.mem_support_iff_of_mem hxU).trans ?_
  rw [Scheme.mem_zeroLocus_iff, ds_stalkId_eq_map G _ x hxU]
  constructor
  · intro h htop
    obtain ⟨f, hf, hu⟩ : ∃ f ∈ G.ideal ⟨U', hU'⟩, IsUnit (W.presheaf.germ U' x hxU' f) := by
      by_contra hno
      push_neg at hno
      have hle : Ideal.map (W.presheaf.germ U' x hxU').hom (G.ideal ⟨U', hU'⟩) ≤
          IsLocalRing.maximalIdeal _ := by
        rw [Ideal.map_le_iff_le_comap]
        intro f hf
        exact (IsLocalRing.mem_maximalIdeal _).2 (hno f hf)
      rw [htop] at hle
      exact (IsLocalRing.maximalIdeal.isMaximal _).ne_top (top_le_iff.1 hle)
    exact h f hf ((Scheme.mem_basicOpen _ _ _ _).2 hu)
  · intro h f hf hxf
    apply h
    exact Ideal.eq_top_of_isUnit_mem _ (Ideal.mem_map_of_mem _ hf)
      ((Scheme.mem_basicOpen _ _ _ hxU).1 hxf)

end

end ReciprocityTheory.AnForm.R
