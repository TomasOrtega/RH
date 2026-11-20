import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.EntryMem
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AGraded
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WeightAlgebraGeneratedDegreeTwo
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ASmooth
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.QuotientSaturatedSquareTorsionFree
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.FgMapMk
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TorusConjugateCornerEntryEq
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ExistsLiftOfDerivationOnIdeal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.MPrime
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ShaCoc
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.AVal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.Nval
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.TwoIrr
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtLift
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtScale
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtActInternal
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.PtExt
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.ConjTorus
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.WcompMulHomog
import Development.AutomorphicArithmetic.AutomorphicVarieties.SymplecticGSp4.SgnMulSelf
open NumberField IsDedekindDomain Formalism.ConjugateSelfDual ReciprocityTheory.Gal IsLocalRing UpperTheory.V UpperTheory.V.Base UpperTheory.V.Alg UpperTheory.V.HV UpperTheory.V.GradeZeroInterpolatingElement

section Gen

variable {O A K : Type} [CommRing O] [CommRing A] [Algebra O A] (𝒜 : ℤ → Submodule O A) [GradedAlgebra 𝒜]
  [Field K] [Algebra O K]

/- English proof (translation)
Use extensionality with `f`. Proceed by induction on `f using DirectSum.Decomposition.inductionOn 𝒜 with`. Consider the case `zero => simp`. Consider the case `homogeneous f => exact h _ _ f.2`. Consider the case `add a b ha hb => rw [map_add, map_add, ha, hb]`.
-/
private theorem algHom_ext_graded {ξ ξ' : A →ₐ[O] K} (h : ∀ j, ∀ f ∈ 𝒜 j, ξ f = ξ' f) : ξ = ξ' := by
  ext f
  induction f using DirectSum.Decomposition.inductionOn 𝒜 with
  | zero => simp
  | homogeneous f => exact h _ _ f.2
  | add a b ha hb => rw [map_add, map_add, ha, hb]

/- English proof (translation)
Take `⟨s, rfl⟩` from `h`. Take `⟨t, rfl⟩` from `h'`. Use `⟨t * s, algHom_ext_graded 𝒜 fun j f hf => ?_⟩` and prove the remaining obligations. Simplify using `only [act_of_mem 𝒜 _ _ hf, zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]`.
-/
private theorem same_orbit_trans {ξ ξ' ξ'' : A →ₐ[O] K} (h : SameOrbit 𝒜 ξ ξ') (h' : SameOrbit 𝒜 ξ' ξ'') :
    SameOrbit 𝒜 ξ ξ'' := by
  obtain ⟨s, rfl⟩ := h
  obtain ⟨t, rfl⟩ := h'
  refine ⟨t * s, algHom_ext_graded 𝒜 fun j f hf => ?_⟩
  simp only [act_of_mem 𝒜 _ _ hf, zpowersHom_apply, toAdd_ofAdd, mul_zpow, Units.val_mul, mul_assoc]

/- English proof (translation)
Establish `h' : ∃ n, ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ T.card = n`. Take `⟨T, hT⟩` from `h`. Conclude with `⟨_, T, hT, rfl⟩`. Take `⟨T, hT, hc⟩` from `Nat.find_spec h'`. Use `⟨T, hT, fun ξ hξ ξ' hξ' ho => ?_⟩` and prove the remaining obligations.

Assume the negation of the conclusion as `hne`. Use `Nat.find_min h' (m := (T.erase ξ').card) (hc ▸ Finset.card_erase_lt_of_mem hξ') ⟨T.erase ξ', ⟨?_, ?_⟩, rfl⟩` and prove the remaining obligations. Conclude with `fun x hx => hT.1 x (Finset.mem_of_mem_erase hx)`. Introduce `x hx h2`. Take `⟨y, hy, hyx⟩` from `hT.2 x hx h2`.

Distinguish the cases in `e : y = ξ'`. Substitute `e` using the available equality. Conclude with `⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, same_orbit_trans 𝒜 ho hyx⟩`. Conclude with `⟨y, Finset.mem_erase.2 ⟨e, hy⟩, hyx⟩`.
-/
private theorem exists_minimal_orbit_cover (I : Ideal A) (h : ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T) :
    ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ ∀ ξ ∈ T, ∀ ξ' ∈ T, SameOrbit 𝒜 ξ ξ' → ξ = ξ' := by
  classical
  have h' : ∃ n, ∃ T : Finset (A →ₐ[O] K), Covers 𝒜 I T ∧ T.card = n := by
    obtain ⟨T, hT⟩ := h
    exact ⟨_, T, hT, rfl⟩
  obtain ⟨T, hT, hc⟩ := Nat.find_spec h'
  refine ⟨T, hT, fun ξ hξ ξ' hξ' ho => ?_⟩
  by_contra hne
  refine Nat.find_min h' (m := (T.erase ξ').card) (hc ▸ Finset.card_erase_lt_of_mem hξ') ⟨T.erase ξ', ⟨?_, ?_⟩, rfl⟩
  · exact fun x hx => hT.1 x (Finset.mem_of_mem_erase hx)
  · intro x hx h2
    obtain ⟨y, hy, hyx⟩ := hT.2 x hx h2
    by_cases e : y = ξ'
    · subst e
      exact ⟨ξ, Finset.mem_erase.2 ⟨hne, hξ⟩, same_orbit_trans 𝒜 ho hyx⟩
    · exact ⟨y, Finset.mem_erase.2 ⟨e, hy⟩, hyx⟩

end Gen

/- English proof (translation)
Use extensionality with `i j`. Simplify using `only [tconj, wv, Matrix.of_apply, Prod.fst_mul, Prod.snd_mul, mul_zpow, Units.val_mul]`. Expand and normalize the polynomial expressions, which then agree.
-/
private theorem torus_conj_mul {R : Type} [CommRing R] (s t : Rˣ × Rˣ) (X : M4 R) :
    tconj s (tconj t X) = tconj (s * t) X := by
  ext i j
  simp only [tconj, wv, Matrix.of_apply, Prod.fst_mul, Prod.snd_mul, mul_zpow, Units.val_mul]
  ring

/- English proof (translation)
Use extensionality with `i j`. Simplify using `[tconj, wv]`.
-/
private theorem torus_conj_one {R : Type} [CommRing R] (X : M4 R) : tconj 1 X = X := by
  ext i j
  simp [tconj, wv]

/- English proof (translation)
Take `⟨u, hu⟩` from `(grp R).2.2.2.2.2.2.2.2.2.2.2.2 t`. Establish `key : ∀ X ∈ Submodule.span R (Set.range r), (u : M4 R) * X * (u⁻¹ : (M4 R)ˣ) ∈ Submodule.span R (Set.range r')`. Introduce `X hX`. Proceed by induction on `hX using Submodule.span_induction with`. Consider the case `mem x hx`.

Take `⟨g, rfl⟩` from `hx`. Conclude with `Submodule.subset_span ⟨g, by rw [h, hu]⟩`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [mul_add, add_mul]`. Conclude with `add_mem hx hy`.

Consider the case `smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]`. Conclude with `Submodule.smul_mem _ a hx`. Use `eq_top_iff.2 fun X _ => ?_` and prove the remaining obligations. Use `key (((u⁻¹ : (M4 R)ˣ) : M4 R) * X * u) (by rw [show Submodule.span R (Set.range r) = ⊤ from hr]; trivial)` as an intermediate fact. Simplify `this` using `only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one]`.
-/
private theorem irreducible_torus_conjugate {R H : Type} [CommRing R] [Group H] (t : Rˣ × Rˣ) (r r' : H →* M4 R)
    (h : ∀ g, r' g = tconj t (r g)) (hr : Irr r) : Irr r' := by
  obtain ⟨u, hu⟩ := (grp R).2.2.2.2.2.2.2.2.2.2.2.2 t
  have key : ∀ X ∈ Submodule.span R (Set.range r), (u : M4 R) * X * (u⁻¹ : (M4 R)ˣ) ∈ Submodule.span R (Set.range r') := by
    intro X hX
    induction hX using Submodule.span_induction with
    | mem x hx =>
      obtain ⟨g, rfl⟩ := hx
      exact Submodule.subset_span ⟨g, by rw [h, hu]⟩
    | zero => simp
    | add x y _ _ hx hy => rw [mul_add, add_mul]; exact add_mem hx hy
    | smul a x _ hx => rw [mul_smul_comm, smul_mul_assoc]; exact Submodule.smul_mem _ a hx
  refine eq_top_iff.2 fun X _ => ?_
  have := key (((u⁻¹ : (M4 R)ˣ) : M4 R) * X * u) (by rw [show Submodule.span R (Set.range r) = ⊤ from hr]; trivial)
  simpa only [mul_assoc, Units.mul_inv_cancel_left, Units.mul_inv, mul_one] using this

/- English proof (translation)
Establish `h3 : s * L ≤ 2 * S * e`. Use `mul_le_mul_of_nonneg_right (h1.trans h2) hL.le` as an intermediate fact. Establish `e1 : 2 * (S * e / L) * L = 2 * S * e` using `by field_simp`. Rewrite `this` using `[e1]`. Then use the resulting hypothesis. Rewrite using `[div_mul_eq_mul_div, div_le_iff₀ he]`.

Conclude with `h3`.
-/
private theorem real_ratio_bound (s n e L S : ℝ) (he : 0 < e) (hL : 0 < L) (h1 : s ≤ n) (h2 : n ≤ 2 * (S * e / L)) :
    s / e * L ≤ 2 * S := by
  have h3 : s * L ≤ 2 * S * e := by
    have := mul_le_mul_of_nonneg_right (h1.trans h2) hL.le
    have e1 : 2 * (S * e / L) * L = 2 * S * e := by field_simp
    rwa [e1] at this
  rw [div_mul_eq_mul_div, div_le_iff₀ he]
  exact h3

section Pts

variable {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} {D : Raw Ω c}

/- English proof (translation)
Take `⟨s, hs⟩` from `conjTorus D hD _ _ he he' hi hc`. Take `⟨η, hη, hw⟩` from `ptAct D hD M _ ξ (t'⁻¹ * (s * t))`. Establish `e : η = ξ'`. Use `ptExt D hD M h0 _ _ _ (MonoidHom.ext fun g => ?_)` and prove the remaining obligations. Rewrite using `[hη, ← torus_conj_mul, ← torus_conj_mul, ← ht, ← hs, ht', torus_conj_mul, inv_mul_cancel, torus_conj_one]`.

Substitute `e` using the available equality. Use `⟨(t'⁻¹ * (s * t)).2, algHom_ext_graded M.gr fun j f hf => ?_⟩` and prove the remaining obligations. Rewrite using `[act_of_mem M.gr _ _ hf, AlgHom.comp_apply, AlgHom.comp_apply, hw (0, j) _ ((kerA D hD M).2.2 j f hf)]`. Simplify using `only [wv, zpow_zero, one_mul, zpowersHom_apply, toAdd_ofAdd]`.
-/
private theorem same_orbit_of_conjugate_reps (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (h0 : D.Fin0)
    (ξ ξ' : M.SS →ₐ[c.O] PadicAlgCl l) (t t' : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ) (r r' : G ℚ Ω →* M4 (PadicAlgCl l))
    (he : D.EPt r) (he' : D.EPt r') (hi : Irr r) (ht : ∀ g, r g = tconj t (M.rep ξ g))
    (ht' : ∀ g, r' g = tconj t' (M.rep ξ' g)) (hc : IsConj4 r r') :
    SameOrbit M.gr (ξ.comp M.toSS) (ξ'.comp M.toSS) := by
  obtain ⟨s, hs⟩ := conjTorus D hD _ _ he he' hi hc
  obtain ⟨η, hη, hw⟩ := ptAct D hD M _ ξ (t'⁻¹ * (s * t))
  have e : η = ξ' := by
    refine ptExt D hD M h0 _ _ _ (MonoidHom.ext fun g => ?_)
    rw [hη, ← torus_conj_mul, ← torus_conj_mul, ← ht, ← hs, ht', torus_conj_mul, inv_mul_cancel, torus_conj_one]
  subst e
  refine ⟨(t'⁻¹ * (s * t)).2, algHom_ext_graded M.gr fun j f hf => ?_⟩
  rw [act_of_mem M.gr _ _ hf, AlgHom.comp_apply, AlgHom.comp_apply, hw (0, j) _ ((kerA D hD M).2.2 j f hf)]
  simp only [wv, zpow_zero, one_mul, zpowersHom_apply, toAdd_ofAdd]

/- English proof (translation)
Establish `hpt : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, ∃ r : G ℚ Ω →* M4 (PadicAlgCl l), OnS M.eqns.ideal x ∧ TwoSigned M.gr x → ((D.EPt r ∧ Irr r) ∧ D.aVal g r = x a) ∧ ∃ (ξ : M.SS →ₐ[c.O] PadicAlgCl l) (t : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ), ξ.comp M.toSS = x ∧ ∀ g, r g = tconj t (M.rep ξ g)`. Introduce `x`. Distinguish the cases in `hx : OnS M.eqns.ideal x`. Take `⟨ξ, hξ⟩` from `ptLift D hD M x hx`. Take `⟨t, r, hr, hrt⟩` from `ptScale D hD M h0 ξ`.

Use `⟨r, fun h2 => ⟨⟨⟨hr, irreducible_torus_conjugate t _ _ hrt (twoIrr D hD M hL hV h0 hNE ξ (by rw [hξ]; exact h2.2))⟩, ?_⟩, ξ, t, hξ, hrt⟩⟩` and prove the remaining obligations. Rewrite using `[← hξ, AlgHom.comp_apply, ha, Raw.aVal, Raw.aVal, hrt, (grp _).2.2.2.2.2.2.2.2.2.2.2.1]`. Conclude with `⟨1, fun h => absurd h.1 hx⟩`. Use `choose ρ hρ using hpt`. Use `⟨ρ, fun x hx => (hρ x hx).1, fun x x' hx hx' hc => ?_⟩` and prove the remaining obligations.

Take `⟨⟨⟨he, hi⟩, -⟩, ξ, t, hξ, ht⟩` from `hρ x hx`. Take `⟨⟨⟨he', -⟩, -⟩, ξ', t', hξ', ht'⟩` from `hρ x' hx'`. Use `same_orbit_of_conjugate_reps hD M h0 ξ ξ' t t' _ _ he he' hi ht ht' hc` as an intermediate fact. Rewrite `this` using `[hξ, hξ']`. Then use the resulting hypothesis.
-/
private theorem exists_rep_family_from_points (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (g : G ℚ Ω) (a : M.A)
    (ha : ∀ ξ : M.SS →ₐ[c.O] PadicAlgCl l, ξ (M.toSS a) = D.aVal g (M.rep ξ)) :
    ∃ ρ : (M.A →ₐ[c.O] PadicAlgCl l) → (G ℚ Ω →* M4 (PadicAlgCl l)),
      (∀ x, OnS M.eqns.ideal x ∧ TwoSigned M.gr x → (D.EPt (ρ x) ∧ Irr (ρ x)) ∧ D.aVal g (ρ x) = x a) ∧
      ∀ x x', OnS M.eqns.ideal x ∧ TwoSigned M.gr x → OnS M.eqns.ideal x' ∧ TwoSigned M.gr x' →
        IsConj4 (ρ x) (ρ x') → SameOrbit M.gr x x' := by
  have hpt : ∀ x : M.A →ₐ[c.O] PadicAlgCl l, ∃ r : G ℚ Ω →* M4 (PadicAlgCl l), OnS M.eqns.ideal x ∧ TwoSigned M.gr x →
      ((D.EPt r ∧ Irr r) ∧ D.aVal g r = x a) ∧ ∃ (ξ : M.SS →ₐ[c.O] PadicAlgCl l)
        (t : (PadicAlgCl l)ˣ × (PadicAlgCl l)ˣ), ξ.comp M.toSS = x ∧ ∀ g, r g = tconj t (M.rep ξ g) := by
    intro x
    by_cases hx : OnS M.eqns.ideal x
    · obtain ⟨ξ, hξ⟩ := ptLift D hD M x hx
      obtain ⟨t, r, hr, hrt⟩ := ptScale D hD M h0 ξ
      refine ⟨r, fun h2 => ⟨⟨⟨hr, irreducible_torus_conjugate t _ _ hrt (twoIrr D hD M hL hV h0 hNE ξ (by rw [hξ]; exact h2.2))⟩, ?_⟩,
        ξ, t, hξ, hrt⟩⟩
      rw [← hξ, AlgHom.comp_apply, ha, Raw.aVal, Raw.aVal, hrt, (grp _).2.2.2.2.2.2.2.2.2.2.2.1]
    · exact ⟨1, fun h => absurd h.1 hx⟩
  choose ρ hρ using hpt
  refine ⟨ρ, fun x hx => (hρ x hx).1, fun x x' hx hx' hc => ?_⟩
  obtain ⟨⟨⟨he, hi⟩, -⟩, ξ, t, hξ, ht⟩ := hρ x hx
  obtain ⟨⟨⟨he', -⟩, -⟩, ξ', t', hξ', ht'⟩ := hρ x' hx'
  have := same_orbit_of_conjugate_reps hD M h0 ξ ξ' t t' _ _ he he' hi ht ht' hc
  rwa [hξ, hξ'] at this

/- English proof (translation)
Take `⟨h1, h2, h3⟩` from `m1b D hD M hV`. Conclude with `hM c.O (PadicAlgCl l) _ (nval c) M.A M.gr M.x0 (aW D hD M) _ _ _ _ _ M.eqns a ⟨M.one_le, aSmooth D hD M, h1, h2, h3⟩ (m2 D hD M h0) (m3 D hD M hL hV h0) (m4 D hD M hL hV h0 hNE hR) h5`.
-/
private theorem covers_and_cotangent_length_bounds (hD : D.Good) (M : Model D) [GradedAlgebra M.gr] (hM : LemmaM) (hL : Loc.LocalPublishedTheorems) (hV : SoV Ω l)
    (h0 : D.Fin0) (hNE : D.NoEnd) (hR : D.AllIrr D.RigidAt) (a : M.A) (h5 : M5 M.gr (PadicAlgCl l) M.x0 M.eqns.ideal a) :
    (∃ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T) ∧ cotLen M.x0 M.gr (-1) M.eqns.F ≠ ⊤ ∧
    ∀ T : Finset (M.A →ₐ[c.O] PadicAlgCl l), Covers M.gr M.eqns.ideal T → ((cotLen M.x0 M.gr (-1) M.eqns.F).toNat : ℝ) ≤
      2 * ∑ ξ ∈ T, -Real.log ‖ξ a‖ * ((eO l c.O).toNat : ℝ) / Real.log l := by
  obtain ⟨h1, h2, h3⟩ := m1b D hD M hV
  exact hM c.O (PadicAlgCl l) _ (nval c) M.A M.gr M.x0 (aW D hD M) _ _ _ _ _ M.eqns a
    ⟨M.one_le, aSmooth D hD M, h1, h2, h3⟩ (m2 D hD M h0) (m3 D hD M hL hV h0) (m4 D hD M hL hV h0 hNE hR) h5

end Pts

/- English proof (translation)
Introduce `Ω _ _ _ l hl c D hD M hM hM' hL hV hF h0 hNE hR g hA`. Take `⟨inst⟩` from `aGraded D hD M`. Take `⟨a, ha0, hax, ha⟩` from `aElt D hD M g`. Take `⟨ρ, hρ, horb⟩` from `exists_rep_family_from_points hD M hL hV h0 hNE g a ha`. Take `⟨hT, hfin, hle⟩` from `covers_and_cotangent_length_bounds hD M hM hL hV h0 hNE hR a ⟨ha0, hax, fun x hx h2 => by`.

Take `⟨⟨he, hi⟩, hv⟩` from `hρ x ⟨hx, h2⟩`. Rewrite using `[← hv]`. Conclude with `hA _ he hi⟩`. Take `⟨T, hT, hmin⟩` from `exists_minimal_orbit_cover M.gr _ hT`. Establish `hinj : ∀ x ∈ T, ∀ x' ∈ T, IsConj4 (ρ x) (ρ x') → x = x'` using `fun x hx x' hx' hc => hmin x hx x' hx' (horb x x' (hT.1 x hx) (hT.1 x' hx') hc)`.

Use `⟨(shaCoc D hD hF).1, T.image ρ, ?_, ?_, ?_⟩` and prove the remaining obligations. Introduce `r hr`. Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hr`. Conclude with `(hρ x (hT.1 x hx)).1`. Introduce `r hr r' hr' hc`.

Take `⟨x, hx, rfl⟩` from `Finset.mem_image.1 hr`. Take `⟨x', hx', rfl⟩` from `Finset.mem_image.1 hr'`. Rewrite using `[hinj x hx x' hx' hc]`. Establish `e2 : ∑ r ∈ T.image ρ, -Real.log ‖D.aVal g r‖ = ∑ x ∈ T, -Real.log ‖x a‖`. Rewrite using `[Finset.sum_image fun x hx x' hx' e => hinj x hx x' hx' ⟨1, fun g => by`.

Rewrite using `[e, inv_one, Units.val_one, one_mul, mul_one]⟩]`. Conclude with `Finset.sum_congr rfl fun x hx => by rw [(hρ x (hT.1 x hx)).2]`. Rewrite using `[e2]`. Establish `hs` using `hle T hT`. Rewrite `hs` using `[← Finset.sum_div, ← Finset.sum_mul]`.

Take `⟨-, -, -, -, -, e0, e1, -⟩` from `dvrFacts l c.O`. Establish `he : 0 < (eO l c.O).toNat` using `ENat.toNat_pos e0 (ne_top_of_le_ne_top (ENat.coe_ne_top _) e1)`. Conclude with `real_ratio_bound _ _ _ _ _ (Nat.cast_pos.2 he) (Real.log_pos (by exact_mod_cast hl.out.one_lt)) (Nat.cast_le.2 (ENat.toNat_le_toNat (mPrime D hD M hM' hF) hfin)) hs`.
-/
theorem UpperTheory.V.GradeZeroInterpolatingElement.galoisRep_ineq_of_allIrreducible_nonvanishing :
    ∀ {Ω : Type} [Field Ω] [CharZero Ω] [IsAlgClosure ℚ Ω] {l : ℕ} [Fact l.Prime] {c : Coef l} (D : Raw Ω c), D.Good → ∀ M : Model D, LemmaM → LemmaM' → Loc.LocalPublishedTheorems → SoV Ω l → SoFin Ω l → D.Fin0 → D.NoEnd → D.AllIrr D.RigidAt → ∀ g, D.AllIrr (fun r => D.aVal g r ≠ 0) → D.Ineq g := by
  intro Ω _ _ _ l hl c D hD M hM hM' hL hV hF h0 hNE hR g hA
  classical
  obtain ⟨inst⟩ := aGraded D hD M
  obtain ⟨a, ha0, hax, ha⟩ := aElt D hD M g
  obtain ⟨ρ, hρ, horb⟩ := exists_rep_family_from_points hD M hL hV h0 hNE g a ha
  obtain ⟨hT, hfin, hle⟩ := covers_and_cotangent_length_bounds hD M hM hL hV h0 hNE hR a
    ⟨ha0, hax, fun x hx h2 => by
      obtain ⟨⟨he, hi⟩, hv⟩ := hρ x ⟨hx, h2⟩
      rw [← hv]
      exact hA _ he hi⟩
  obtain ⟨T, hT, hmin⟩ := exists_minimal_orbit_cover M.gr _ hT
  have hinj : ∀ x ∈ T, ∀ x' ∈ T, IsConj4 (ρ x) (ρ x') → x = x' := fun x hx x' hx' hc =>
    hmin x hx x' hx' (horb x x' (hT.1 x hx) (hT.1 x' hx') hc)
  refine ⟨(shaCoc D hD hF).1, T.image ρ, ?_, ?_, ?_⟩
  · intro r hr
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    exact (hρ x (hT.1 x hx)).1
  · intro r hr r' hr' hc
    obtain ⟨x, hx, rfl⟩ := Finset.mem_image.1 hr
    obtain ⟨x', hx', rfl⟩ := Finset.mem_image.1 hr'
    rw [hinj x hx x' hx' hc]
  · have e2 : ∑ r ∈ T.image ρ, -Real.log ‖D.aVal g r‖ = ∑ x ∈ T, -Real.log ‖x a‖ := by
      rw [Finset.sum_image fun x hx x' hx' e => hinj x hx x' hx' ⟨1, fun g => by
        rw [e, inv_one, Units.val_one, one_mul, mul_one]⟩]
      exact Finset.sum_congr rfl fun x hx => by rw [(hρ x (hT.1 x hx)).2]
    rw [e2]
    have hs := hle T hT
    rw [← Finset.sum_div, ← Finset.sum_mul] at hs
    obtain ⟨-, -, -, -, -, e0, e1, -⟩ := dvrFacts l c.O
    have he : 0 < (eO l c.O).toNat :=
      ENat.toNat_pos e0 (ne_top_of_le_ne_top (ENat.coe_ne_top _) e1)
    exact real_ratio_bound _ _ _ _ _ (Nat.cast_pos.2 he) (Real.log_pos (by exact_mod_cast hl.out.one_lt))
      (Nat.cast_le.2 (ENat.toNat_le_toNat (mPrime D hD M hM' hF) hfin)) hs
