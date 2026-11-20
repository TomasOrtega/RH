import Development.EtaleCohomology.EtaleSheaves.NormACPf

noncomputable section
open CategoryTheory Limits AlgebraicGeometry Polynomial Opposite

namespace LateralTheory.E.LocPf

/- English proof (translation)
Introduce `n`. Proceed by induction on `n with`. Consider the case `zero`. Introduce `p hn hp a ha`. Rewrite `ha` using `[eq_one_of_monic_natDegree_zero hp hn, eval₂_one]`.

Conclude with `absurd ha one_ne_zero`. Consider the case `succ n ih`. Introduce `p hn hp a ha`. Establish `: Nontrivial A`. Assume the negation of the conclusion as `hnt`.

Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Rewrite `hn` using `[Subsingleton.elim p 0]`. Simplify using `at hn`. Take `⟨b, hb⟩` from `hA p hp (by omega)`. Establish `e` using `(mul_divByMonic_eq_iff_isRoot (p := p) (a := b)).mpr hb`.

Establish `hq : (p /ₘ (X - C b)).Monic` using `Monic.of_mul_monic_left (monic_X_sub_C b) (by rw [e]; exact hp)`. Establish `hdeg : (p /ₘ (X - C b)).natDegree = n`. Use `(monic_X_sub_C b).natDegree_mul hq` as an intermediate fact. Rewrite `this` using `[e, natDegree_X_sub_C]`. Use linear arithmetic over natural numbers and integers.

Rewrite `ha` using `[← e, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C]`. Break down `mul_eq_zero.mp ha with h | h` into its components or cases. Conclude with `⟨b, (sub_eq_zero.mp h).symm⟩`. Conclude with `ih _ hdeg hq a h`.
-/
theorem root_mem_range {A K : Type} [CommRing A] [CommRing K] [IsDomain K] (hA : GlobalTheory.EtC.AIC A) (φ : A →+* K) :
    ∀ (n : ℕ) (p : A[X]), p.natDegree = n → p.Monic → ∀ a : K, p.eval₂ φ a = 0 → ∃ b, φ b = a := by
  intro n
  induction n with
  | zero =>
    intro p hn hp a ha
    rw [eq_one_of_monic_natDegree_zero hp hn, eval₂_one] at ha
    exact absurd ha one_ne_zero
  | succ n ih =>
    intro p hn hp a ha
    have : Nontrivial A := by
      by_contra hnt; rw [not_nontrivial_iff_subsingleton] at hnt
      rw [Subsingleton.elim p 0] at hn; simp at hn
    obtain ⟨b, hb⟩ := hA p hp (by omega)
    have e := (mul_divByMonic_eq_iff_isRoot (p := p) (a := b)).mpr hb
    have hq : (p /ₘ (X - C b)).Monic := Monic.of_mul_monic_left (monic_X_sub_C b) (by rw [e]; exact hp)
    have hdeg : (p /ₘ (X - C b)).natDegree = n := by
      have := (monic_X_sub_C b).natDegree_mul hq
      rw [e, natDegree_X_sub_C] at this; omega
    rw [← e, eval₂_mul, eval₂_sub, eval₂_X, eval₂_C] at ha
    rcases mul_eq_zero.mp ha with h | h
    · exact ⟨b, (sub_eq_zero.mp h).symm⟩
    · exact ih _ hdeg hq a h

/- English proof (translation)
Introduce `p hp hd`. Take `⟨b, hb⟩` from `IsLocalization.exist_integer_multiples_of_finite M (fun i : Fin (p.natDegree + 1) => p.coeff i)`. Use `set t := algebraMap A B b with ht`. Establish `hlift : p.scaleRoots t ∈ lifts (algebraMap A B)`. Rewrite using `[lifts_iff_coeff_lifts]`.

Introduce `i`. Rewrite using `[coeff_scaleRoots]`. Break down `lt_trichotomy i p.natDegree with h | h | h` into its components or cases. Take `⟨c, hc⟩` from `hb ⟨i, by omega⟩`. Use `⟨c * (b : A) ^ (p.natDegree - i - 1), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_mul, map_pow, hc, Algebra.smul_def, ← ht]`. Rewrite using `[show t ^ (p.natDegree - i) = t * t ^ (p.natDegree - i - 1) by rw [← pow_succ']; congr 1; omega]`. Expand and normalize the polynomial expressions, which then agree. Substitute `h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩` using the available equality. Rewrite using `[coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩`.

Take `⟨q, hqm, hqd, hq⟩` from `lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).mpr hp)`. Take `⟨c, hc⟩` from `hA q hq (by rw [hqd, natDegree_scaleRoots]; exact hd)`. Take `⟨u, hu⟩` from `(IsLocalization.map_units B b).exists_right_inv`. Use `⟨u * algebraMap A B c, ?_⟩` and prove the remaining obligations. Establish `h1 : p = (p.scaleRoots t).scaleRoots u`.

Rewrite using `[← scaleRoots_mul, ht, hu, scaleRoots_one]`. Establish `h2 : (p.scaleRoots t).eval (algebraMap A B c) = 0`. Rewrite using `[← hqm, Polynomial.eval_map, eval₂_at_apply, hc, map_zero]`. Use `conv_lhs => rw [h1]`. Rewrite using `[scaleRoots_eval_mul, h2, mul_zero]`.
-/
theorem aic_of_isLocalization {A B : Type} [CommRing A] [CommRing B] [Algebra A B] (M : Submonoid A)
    [IsLocalization M B] (hA : GlobalTheory.EtC.AIC A) : GlobalTheory.EtC.AIC B := by
  intro p hp hd
  obtain ⟨b, hb⟩ := IsLocalization.exist_integer_multiples_of_finite M (fun i : Fin (p.natDegree + 1) => p.coeff i)
  set t := algebraMap A B b with ht
  have hlift : p.scaleRoots t ∈ lifts (algebraMap A B) := by
    rw [lifts_iff_coeff_lifts]
    intro i
    rw [coeff_scaleRoots]
    rcases lt_trichotomy i p.natDegree with h | h | h
    · obtain ⟨c, hc⟩ := hb ⟨i, by omega⟩
      refine ⟨c * (b : A) ^ (p.natDegree - i - 1), ?_⟩
      rw [map_mul, map_pow, hc, Algebra.smul_def, ← ht]
      rw [show t ^ (p.natDegree - i) = t * t ^ (p.natDegree - i - 1) by rw [← pow_succ']; congr 1; omega]
      ring
    · subst h; rw [hp.coeff_natDegree]; exact ⟨1, by simp⟩
    · rw [coeff_eq_zero_of_natDegree_lt h]; exact ⟨0, by simp⟩
  obtain ⟨q, hqm, hqd, hq⟩ := lifts_and_natDegree_eq_and_monic hlift ((monic_scaleRoots_iff t).mpr hp)
  obtain ⟨c, hc⟩ := hA q hq (by rw [hqd, natDegree_scaleRoots]; exact hd)
  obtain ⟨u, hu⟩ := (IsLocalization.map_units B b).exists_right_inv
  refine ⟨u * algebraMap A B c, ?_⟩
  have h1 : p = (p.scaleRoots t).scaleRoots u := by
    rw [← scaleRoots_mul, ht, hu, scaleRoots_one]
  have h2 : (p.scaleRoots t).eval (algebraMap A B c) = 0 := by
    rw [← hqm, Polynomial.eval_map, eval₂_at_apply, hc, map_zero]
  conv_lhs => rw [h1]
  rw [scaleRoots_eval_mul, h2, mul_zero]

/- English proof (translation)
Use extensionality with `s`. Simplify using the standard rewrite rules.
-/
theorem germ_comp (Z : Scheme.{0}) {W U : Z.Opens} (i : W ≤ U) (x : Z) (hx : x ∈ W) :
    (Z.presheaf.germ W x hx).hom.comp (Z.presheaf.map (homOfLE i).op).hom = (Z.presheaf.germ U x (i hx)).hom := by
  ext s; simp

/- English proof (translation)
Take `⟨V, hV, hzV, hA⟩` from `h z`. Take `⟨f, hle, hzf⟩` from `hV.exists_basicOpen_le (V := U) ⟨z, hz⟩ hzV`. Use `hV.isLocalization_basicOpen f` as an intermediate fact. Conclude with `⟨Z.basicOpen f, hle, hzf, aic_of_isLocalization (Submonoid.powers f) hA⟩`.
-/
theorem exists_small (Z : Scheme.{0}) (h : ∀ z : Z, ∃ U : Z.Opens, IsAffineOpen U ∧ z ∈ U ∧ GlobalTheory.EtC.AIC Γ(Z, U))
    (U : Z.Opens) (z : Z) (hz : z ∈ U) : ∃ W : Z.Opens, W ≤ U ∧ z ∈ W ∧ GlobalTheory.EtC.AIC Γ(Z, W) := by
  obtain ⟨V, hV, hzV, hA⟩ := h z
  obtain ⟨f, hle, hzf⟩ := hV.exists_basicOpen_le (V := U) ⟨z, hz⟩ hzV
  have := hV.isLocalization_basicOpen f
  exact ⟨Z.basicOpen f, hle, hzf, aic_of_isLocalization (Submonoid.powers f) hA⟩

/- English proof (translation)
Introduce `Z hZ h U hU ⟨z0, hz0⟩ p hp hd`. Use `set η := genericPoint Z`. Establish `hη : ∀ W : Z.Opens, (W : Set Z).Nonempty → η ∈ W` using `fun W hW => ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using hW)`. Establish `hηU : η ∈ U` using `hη U ⟨z0, hz0⟩`. Use `choose W hWU hzW hWA using fun z : U => exists_small Z h U z.1 z.2`.

Establish `hηW : ∀ z : U, η ∈ W z` using `fun z => hη _ ⟨z.1, hzW z⟩`. Set `gU` to `(Z.presheaf.germ U η hηU).hom`. Set `res` to `fun z : U => (Z.presheaf.map (homOfLE (hWU z)).op).hom`. Establish `hdom : ∀ z : U, Nontrivial Γ(Z, W z)` using `fun z => by`. Establish `: Nonempty (W z)` using `⟨⟨z.1, hzW z⟩⟩`.

Use `infer_instance`. Set `z0' : U` to `⟨z0, hz0⟩`. Take `⟨b0, hb0⟩` from `hWA z0' (p.map (res z0')) (hp.map _) (by rw [hp.natDegree_map]; exact hd)`. Use `set a := Z.presheaf.germ (W z0') η (hηW z0') b0 with ha_def`. Establish `hroot : p.eval₂ gU a = 0`.

Use `congrArg (Z.presheaf.germ (W z0') η (hηW z0')).hom hb0` as an intermediate fact. Rewrite `this` using `[Polynomial.eval_map, hom_eval₂, germ_comp, map_zero]`. Conclude with `this`. Establish `hc : ∀ z : U, ∃ c, Z.presheaf.germ (W z) η (hηW z) c = a`. Introduce `z`.

Use `root_mem_range (hWA z) (Z.presheaf.germ (W z) η (hηW z)).hom _ (p.map (res z)) rfl (hp.map _) a ?_` and prove the remaining obligations. Rewrite using `[eval₂_map, germ_comp]`. Conclude with `hroot`. Use `choose c hcz using hc`. Take `⟨s1, hs1, -⟩` from `TopCat.Sheaf.existsUnique_gluing' Z.sheaf W U (fun z => homOfLE (hWU z)) (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW _⟩) c (by`.

Introduce `i j`. Apply `germ_injective_of_isIntegral Z (U := W i ⊓ W j) η (show η ∈ W i ⊓ W j from ⟨hηW i, hηW j⟩)` to reduce the goal to its premises. Express the relevant statement in the definitionally equal form `(Z.presheaf.germ _ η _) (Z.presheaf.map _ (c i)) = (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c j))`. Rewrite using `[TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hcz, hcz])`. Take `⟨s, hs⟩ : ∃ s : Γ(Z, U), ∀ i, Z.presheaf.map (homOfLE (hWU i)).op s = c i` from `⟨s1, hs1⟩`.

Establish `hsa : gU s = a`. Use `hs z0'` as an intermediate fact. Rewrite using `[← hcz z0', ← this]`. Express the relevant statement in the definitionally equal form `_ = (Z.presheaf.germ _ η _) (Z.presheaf.map _ s)`. Rewrite using `[TopCat.Presheaf.germ_res_apply]`.

Use `⟨s, germ_injective_of_isIntegral Z η hηU ?_⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `gU (p.eval s) = gU 0`. Rewrite using `[map_zero, ← eval₂_at_apply, hsa, hroot]`.
-/
theorem loc : LateralTheory.E.NormACPf.Loc := by
  intro Z hZ h U hU ⟨z0, hz0⟩ p hp hd
  set η := genericPoint Z
  have hη : ∀ W : Z.Opens, (W : Set Z).Nonempty → η ∈ W := fun W hW =>
    ((genericPoint_spec Z).mem_open_set_iff W.isOpen).mpr (by simpa using hW)
  have hηU : η ∈ U := hη U ⟨z0, hz0⟩
  choose W hWU hzW hWA using fun z : U => exists_small Z h U z.1 z.2
  have hηW : ∀ z : U, η ∈ W z := fun z => hη _ ⟨z.1, hzW z⟩
  let gU := (Z.presheaf.germ U η hηU).hom
  let res := fun z : U => (Z.presheaf.map (homOfLE (hWU z)).op).hom
  have hdom : ∀ z : U, Nontrivial Γ(Z, W z) := fun z => by
    have : Nonempty (W z) := ⟨⟨z.1, hzW z⟩⟩; infer_instance
  let z0' : U := ⟨z0, hz0⟩
  obtain ⟨b0, hb0⟩ := hWA z0' (p.map (res z0')) (hp.map _) (by rw [hp.natDegree_map]; exact hd)
  set a := Z.presheaf.germ (W z0') η (hηW z0') b0 with ha_def
  have hroot : p.eval₂ gU a = 0 := by
    have := congrArg (Z.presheaf.germ (W z0') η (hηW z0')).hom hb0
    rw [Polynomial.eval_map, hom_eval₂, germ_comp, map_zero] at this
    exact this
  have hc : ∀ z : U, ∃ c, Z.presheaf.germ (W z) η (hηW z) c = a := by
    intro z
    refine root_mem_range (hWA z) (Z.presheaf.germ (W z) η (hηW z)).hom _ (p.map (res z)) rfl (hp.map _) a ?_
    rw [eval₂_map, germ_comp]; exact hroot
  choose c hcz using hc
  obtain ⟨s1, hs1, -⟩ := TopCat.Sheaf.existsUnique_gluing' Z.sheaf W U (fun z => homOfLE (hWU z))
    (fun x hx => TopologicalSpace.Opens.mem_iSup.mpr ⟨⟨x, hx⟩, hzW _⟩) c (by
      intro i j
      apply germ_injective_of_isIntegral Z (U := W i ⊓ W j) η (show η ∈ W i ⊓ W j from ⟨hηW i, hηW j⟩)
      change (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c i)) = (Z.presheaf.germ _ η _) (Z.presheaf.map _ (c j))
      rw [TopCat.Presheaf.germ_res_apply, TopCat.Presheaf.germ_res_apply, hcz, hcz])
  obtain ⟨s, hs⟩ : ∃ s : Γ(Z, U), ∀ i, Z.presheaf.map (homOfLE (hWU i)).op s = c i := ⟨s1, hs1⟩
  have hsa : gU s = a := by
    have := hs z0'
    rw [← hcz z0', ← this]
    change _ = (Z.presheaf.germ _ η _) (Z.presheaf.map _ s)
    rw [TopCat.Presheaf.germ_res_apply]
  refine ⟨s, germ_injective_of_isIntegral Z η hηU ?_⟩
  change gU (p.eval s) = gU 0
  rw [map_zero, ← eval₂_at_apply, hsa, hroot]

end LateralTheory.E.LocPf
