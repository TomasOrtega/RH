import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.DivCalc
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.ExtensionDescent.ThickTransComp
import Lemmata.MiscLemmasN.Imports

set_option autoImplicit false

noncomputable section

open CategoryTheory CategoryTheory.Limits AlgebraicGeometry TopologicalSpace Opposite

namespace ReciprocityTheory.ChartRestriction.G.DVR

open ReciprocityTheory.ChartRestriction.G.Geo.Tor

/- English proof (translation)
Apply the tactic sequence `first | exact Bl.SecondBlockLemmaO.goal1 .. | (apply Bl.SecondBlockLemmaO.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaO.goal1 <;> assumption)`.
-/
theorem away_fractionRing {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V] {ϖ : V}
    (hϖ : Irreducible ϖ) : IsLocalization.Away ϖ (FractionRing V) := by
  first | exact Bl.SecondBlockLemmaO.goal1 .. | (apply Bl.SecondBlockLemmaO.goal1 <;> assumption) | (intros; apply Bl.SecondBlockLemmaO.goal1 <;> assumption)

/- English proof (translation)
Apply the tactic sequence `unfold gs; split_ifs <;> simp`.
-/
theorem gs_zero' {X Y : Scheme.{0}} (f : Y ⟶ X) (y : Y) (U : X.Opens) : gs f y U 0 = 0 := by
  unfold gs; split_ifs <;> simp

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Set `ϖ' : Γ(Sp V, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ`. Establish `hrange : ∀ t' : Sp V, t' ∈ (Sp V).basicOpen ϖ' → t' ∈ Set.range t.base`. Introduce `t' ht`. Establish `ht' : t' ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V))`.

Use `basicOpen_eq_of_affine (R := CommRingCat.of V) ϖ` as an intermediate fact. Rewrite using `[← this]`. Conclude with `ht`. Establish `hbot : PrimeSpectrum.asIdeal (R` using `V) t' = ⊥ := by`. Assume the negation of the conclusion as `hne`.

Establish `hmax` using `Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime (R := V) t') hne`. Establish `hm` using `IsLocalRing.eq_maximalIdeal hmax`. Apply `(PrimeSpectrum.mem_basicOpen _ _).1 ht'` to reduce the goal to its premises. Rewrite using `[hm]`. Conclude with `(IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit`.

Take `⟨y⟩` from `‹Nonempty T›`. Establish `hle : PrimeSpectrum.asIdeal (R` using `V) t' ≤ PrimeSpectrum.asIdeal (R := V) (t.base y) := by`. Rewrite using `[hbot]`. Conclude with `bot_le`. Establish `hsp : t' ⤳ t.base y` using `(PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hle)`.

Conclude with `hsp.mem_open t.isOpenEmbedding.isOpen_range ⟨y, rfl⟩`. Set `O : X.Opens` to `p ⁻¹ᵁ (Sp V).basicOpen ϖ'`. Set `q` to `IsOpenImmersion.lift t (O.ι ≫ p) (by`. Introduce and unpack `_ ⟨a, rfl⟩`. Conclude with `hrange _ a.2)`.

Set `s : O.toScheme ⟶ pullback p t` to `pullback.lift O.ι q (IsOpenImmersion.lift_fac _ _ _).symm`. Establish `hs : s ≫ pullback.fst p t = O.ι` using `pullback.lift_fst _ _ _`. Establish `hO : ∀ x ∈ W, x ∈ O → gs (𝟙 X) x W d = 0`. Introduce `x hxW hxO`. Establish `hm : (s ≫ pullback.fst p t) ⟨x, hxO⟩ ∈ W` using `by rw [hs]; exact hxW`.

Establish `e1 : gs O.ι ⟨x, hxO⟩ W d = 0`. Rewrite using `[← hs, ← gs_pull s (pullback.fst p t) ⟨x, hxO⟩ W hm, h]`. Conclude with `gs_zero' _ _ _`. Rewrite `e1` using `[gs_stalkMap O.ι ⟨x, hxO⟩ W hxW]`. Establish `: IsIso (O.ι.stalkMap ⟨x, hxO⟩)` using `(IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _`.

Conclude with `(ConcreteCategory.bijective_of_isIso (O.ι.stalkMap ⟨x, hxO⟩)).1 (e1.trans (map_zero _).symm)`. Use `fn_ext fun x hx => ?_` and prove the remaining obligations. Rewrite using `[gs_zero']`. Take `⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩` from `X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2`. Establish `hU' : IsAffineOpen (U : X.Opens)` using `hU`.

Set `g : Γ(X, U)` to `constFn p U ϖ`. Set `dU : Γ(X, U)` to `(X.presheaf.map (homOfLE hUW).op).hom d`. Establish `hgs : ∀ x' ∈ U, gs (𝟙 X) x' U g = cst p x' ϖ` using `fun x' hx' => (gs_constFn p U (𝟙 X) x' hx' ϖ).trans (by rw [Category.id_comp])`. Use `(exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU'.isCompact dU g ?_).elim fun n hn => ?_` and prove the remaining obligations. Use `fn_ext fun x' hx' => ?_` and prove the remaining obligations.

Establish `hx'U : x' ∈ U` using `X.basicOpen_le g hx'`. Establish `hunit : IsUnit (X.presheaf.germ U x' hx'U g)` using `(X.mem_basicOpen g x' hx'U).1 hx'`. Establish `h2 : IsUnit (cst p x' ϖ)`. Rewrite using `[← hgs x' hx'U, gs_eq (𝟙 X) x' U hx'U]`. Conclude with `hunit`.

Establish `h3 : IsUnit (gs (𝟙 (Sp V)) (p x') ⊤ ϖ')`. Rewrite `h2` using `[cst, gs_stalkMap p x' ⊤ trivial]`. Conclude with `(isUnit_map_iff (p.stalkMap x').hom _).1 h2`. Establish `hxO : x' ∈ O` using `by show p x' ∈ (Sp V).basicOpen ϖ'`. Rewrite `h3` using `[gs_eq (𝟙 (Sp V)) (p x') ⊤ trivial]`.

Conclude with `((Sp V).mem_basicOpen ϖ' (p x') trivial).2 h3`. Express the relevant statement in the definitionally equal form `gs (𝟙 X) x' _ ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom dU) = gs (𝟙 X) x' _ 0`. Rewrite using `[gs_zero', gs_res (𝟙 X) x' (X.basicOpen_le g) hx']`. Conclude with `(gs_res (𝟙 X) x' hUW hx'U d).trans (hO x' (hUW hx'U) hxO)`. Establish `e` using `congrArg (gs (𝟙 X) x U) hn`.

Establish `hdU : gs (𝟙 X) x U dU = gs (𝟙 X) x W d` using `gs_res (𝟙 X) x hUW hxU d`. Rewrite `e` using `[gs_zero', gs_mul (𝟙 X) x U hxU, hdU]`. Establish `hpow : gs (𝟙 X) x U (g ^ n) = cst p x ϖ ^ n`. Rewrite using `[gs_eq (𝟙 X) x U hxU, map_pow, map_pow, ← gs_eq (𝟙 X) x U hxU, hgs x hxU]`. Rewrite `e` using `[hpow]`.

Conclude with `((cst_regular p x hϖ.ne_zero).pow n) (e.trans (mul_zero _).symm)`.
-/
theorem eq_zero_of_app_fst_open {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X T : AlgebraicGeometry.Scheme.{0}} (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.Flat p]
    (t : T ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.IsOpenImmersion t] [Nonempty T]
    (W : X.Opens) (d : Γ(X, W)) (h : ((CategoryTheory.Limits.pullback.fst p t).app W).hom d = 0) : d = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  let ϖ' : Γ(Sp V, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of V)).inv.hom ϖ
  have hrange : ∀ t' : Sp V, t' ∈ (Sp V).basicOpen ϖ' → t' ∈ Set.range t.base := by
    intro t' ht
    have ht' : t' ∈ (PrimeSpectrum.basicOpen ϖ : Set (PrimeSpectrum V)) := by
      have := basicOpen_eq_of_affine (R := CommRingCat.of V) ϖ
      rw [← this]; exact ht
    have hbot : PrimeSpectrum.asIdeal (R := V) t' = ⊥ := by
      by_contra hne
      have hmax := Ideal.IsPrime.isMaximal (PrimeSpectrum.isPrime (R := V) t') hne
      have hm := IsLocalRing.eq_maximalIdeal hmax
      apply (PrimeSpectrum.mem_basicOpen _ _).1 ht'
      rw [hm]
      exact (IsLocalRing.mem_maximalIdeal _).2 hϖ.not_isUnit
    obtain ⟨y⟩ := ‹Nonempty T›
    have hle : PrimeSpectrum.asIdeal (R := V) t' ≤ PrimeSpectrum.asIdeal (R := V) (t.base y) := by
      rw [hbot]; exact bot_le
    have hsp : t' ⤳ t.base y := (PrimeSpectrum.le_iff_specializes (R := V) _ _).1 ((PrimeSpectrum.asIdeal_le_asIdeal _ _).1 hle)
    exact hsp.mem_open t.isOpenEmbedding.isOpen_range ⟨y, rfl⟩
  let O : X.Opens := p ⁻¹ᵁ (Sp V).basicOpen ϖ'
  let q := IsOpenImmersion.lift t (O.ι ≫ p) (by
    rintro _ ⟨a, rfl⟩
    exact hrange _ a.2)
  let s : O.toScheme ⟶ pullback p t :=
    pullback.lift O.ι q (IsOpenImmersion.lift_fac _ _ _).symm
  have hs : s ≫ pullback.fst p t = O.ι := pullback.lift_fst _ _ _
  have hO : ∀ x ∈ W, x ∈ O → gs (𝟙 X) x W d = 0 := by
    intro x hxW hxO
    have hm : (s ≫ pullback.fst p t) ⟨x, hxO⟩ ∈ W := by rw [hs]; exact hxW
    have e1 : gs O.ι ⟨x, hxO⟩ W d = 0 := by
      rw [← hs, ← gs_pull s (pullback.fst p t) ⟨x, hxO⟩ W hm, h]
      exact gs_zero' _ _ _
    rw [gs_stalkMap O.ι ⟨x, hxO⟩ W hxW] at e1
    have : IsIso (O.ι.stalkMap ⟨x, hxO⟩) := (IsOpenImmersion.iff_isIso_stalkMap.1 inferInstance).2 _
    exact (ConcreteCategory.bijective_of_isIso (O.ι.stalkMap ⟨x, hxO⟩)).1 (e1.trans (map_zero _).symm)
  refine fn_ext fun x hx => ?_
  rw [gs_zero']
  obtain ⟨_, ⟨U, hU, rfl⟩, hxU, hUW⟩ := X.isBasis_affineOpens.exists_subset_of_mem_open hx W.2
  have hU' : IsAffineOpen (U : X.Opens) := hU
  let g : Γ(X, U) := constFn p U ϖ
  let dU : Γ(X, U) := (X.presheaf.map (homOfLE hUW).op).hom d
  have hgs : ∀ x' ∈ U, gs (𝟙 X) x' U g = cst p x' ϖ := fun x' hx' =>
    (gs_constFn p U (𝟙 X) x' hx' ϖ).trans (by rw [Category.id_comp])
  refine (exists_pow_mul_eq_zero_of_res_basicOpen_eq_zero_of_isCompact X hU'.isCompact dU g ?_).elim
    fun n hn => ?_
  · refine fn_ext fun x' hx' => ?_
    have hx'U : x' ∈ U := X.basicOpen_le g hx'
    have hunit : IsUnit (X.presheaf.germ U x' hx'U g) := (X.mem_basicOpen g x' hx'U).1 hx'
    have h2 : IsUnit (cst p x' ϖ) := by
      rw [← hgs x' hx'U, gs_eq (𝟙 X) x' U hx'U]; exact hunit
    have h3 : IsUnit (gs (𝟙 (Sp V)) (p x') ⊤ ϖ') := by
      rw [cst, gs_stalkMap p x' ⊤ trivial] at h2
      exact (isUnit_map_iff (p.stalkMap x').hom _).1 h2
    have hxO : x' ∈ O := by
      show p x' ∈ (Sp V).basicOpen ϖ'
      rw [gs_eq (𝟙 (Sp V)) (p x') ⊤ trivial] at h3
      exact ((Sp V).mem_basicOpen ϖ' (p x') trivial).2 h3
    change gs (𝟙 X) x' _ ((X.presheaf.map (homOfLE (X.basicOpen_le g)).op).hom dU) = gs (𝟙 X) x' _ 0
    rw [gs_zero', gs_res (𝟙 X) x' (X.basicOpen_le g) hx']
    exact (gs_res (𝟙 X) x' hUW hx'U d).trans (hO x' (hUW hx'U) hxO)
  · have e := congrArg (gs (𝟙 X) x U) hn
    have hdU : gs (𝟙 X) x U dU = gs (𝟙 X) x W d := gs_res (𝟙 X) x hUW hxU d
    rw [gs_zero', gs_mul (𝟙 X) x U hxU, hdU] at e
    have hpow : gs (𝟙 X) x U (g ^ n) = cst p x ϖ ^ n := by
      rw [gs_eq (𝟙 X) x U hxU, map_pow, map_pow, ← gs_eq (𝟙 X) x U hxU, hgs x hxU]
    rw [hpow] at e
    exact ((cst_regular p x hϖ.ne_zero).pow n) (e.trans (mul_zero _).symm)

/- English proof (translation)
Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible V`. Use `away_fractionRing hϖ` as an intermediate fact. Establish `: IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Out.jK V)` using `IsOpenImmersion.of_isLocalization ϖ`. Establish `: Nonempty (Spec (CommRingCat.of (FractionRing V)))` using `⟨IsLocalRing.closedPoint _⟩`. Conclude with `eq_zero_of_app_fst_open p (ReciprocityTheory.ChartRestriction.G.Out.jK V) W d h`.
-/
theorem eq_zero_of_app_fst_jK {V : Type} [CommRing V] [IsDomain V] [IsDiscreteValuationRing V]
    {X : AlgebraicGeometry.Scheme.{0}} (p : X ⟶ ReciprocityTheory.ChartRestriction.G.Geo.Tor.Sp V) [AlgebraicGeometry.Flat p]
    (W : X.Opens) (d : Γ(X, W))
    (h : ((CategoryTheory.Limits.pullback.fst p (ReciprocityTheory.ChartRestriction.G.Out.jK V)).app W).hom d = 0) : d = 0 := by
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible V
  have := away_fractionRing hϖ
  have : IsOpenImmersion (ReciprocityTheory.ChartRestriction.G.Out.jK V) := IsOpenImmersion.of_isLocalization ϖ
  have : Nonempty (Spec (CommRingCat.of (FractionRing V))) := ⟨IsLocalRing.closedPoint _⟩
  exact eq_zero_of_app_fst_open p (ReciprocityTheory.ChartRestriction.G.Out.jK V) W d h

end ReciprocityTheory.ChartRestriction.G.DVR
