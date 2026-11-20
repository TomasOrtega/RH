import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.SubsetSpanBy
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.BaseChangeSendsClosedFibreGenericPointDvrStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.RegularAtPointFunctionFieldMapOfGenericPointCompStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.SemiAbelianDvrClosedFibreStalkUniformiserStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ThetaSpanVanishingEqUniformiserMulStatement
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.LinearlyDisjointFunctionFieldOfFlatBaseChangeStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory GlobalTheory.Cartier GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef
open scoped CategoryTheory.Obj
open GlobalTheory.Desc

namespace GlobalTheory.Desc.GaussBC

/- English proof (translation)
Introduce `X _ R _ p`. Apply `ext_of_isAffine` to reduce the goal to its premises. Rewrite using `[← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp, Scheme.fromSpecStalk_appTop]`. Use extensionality with `r`. Simplify using `[GlobalTheory.Desc.cst, fnOf, Scheme.functionField]`.
-/
theorem gp_comp_eq_spMap_cst : ∀ (X : Scheme.{0}) [IsIntegral X] (R : Type) [CommRing R] (p : X ⟶ Sp R),
    gp X ≫ p = spMap (GlobalTheory.Desc.cst p) := by
  intro X _ R _ p
  apply ext_of_isAffine
  rw [← cancel_mono (Scheme.ΓSpecIso _).hom, Scheme.ΓSpecIso_naturality, Scheme.Hom.comp_appTop, gp,
    Scheme.fromSpecStalk_appTop]
  ext r
  simp [GlobalTheory.Desc.cst, fnOf, Scheme.functionField]

/- English proof (translation)
Introduce `R _ _ X _ p x hx r`. Establish `hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r)` using `regAt_fnOf (U := ⊤) trivial trivial _`. Use `⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩` and prove the remaining obligations. Establish `h1` using `(unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu`. Establish `h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)`.

Rewrite using `[Scheme.Hom.preimage_basicOpen]`. Conclude with `h1`. Establish `h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r)` using `h2`. Rewrite `h3` using `[basicOpen_eq_of_affine, hx]`. Conclude with `(PrimeSpectrum.mem_basicOpen _ _).1 h3 hr`.
-/
theorem cst_regAt_zeroAt : ∀ (R : Type) [CommRing R] [IsLocalRing R] (X : Scheme.{0}) [IsIntegral X] (p : X ⟶ Sp R) (x : X), p x = closedPoint R → ∀ r : R, GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) ∧ (r ∈ maximalIdeal R → GlobalTheory.Cartier.ZeroAt x (GlobalTheory.Desc.cst p r)) := by
  intro R _ _ X _ p x hx r
  have hreg : GlobalTheory.Cartier.RegAt x (GlobalTheory.Desc.cst p r) := regAt_fnOf (U := ⊤) trivial trivial _
  refine ⟨hreg, fun hr => zeroAt_iff.2 ⟨hreg, fun hu => ?_⟩⟩
  have h1 := (unitAt_fnOf_iff (U := ⊤) trivial trivial _).1 hu
  have h2 : x ∈ p ⁻¹ᵁ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := by
    rw [Scheme.Hom.preimage_basicOpen]; exact h1
  have h3 : p x ∈ (Sp R).basicOpen ((Scheme.ΓSpecIso (CommRingCat.of R)).inv r) := h2
  rw [basicOpen_eq_of_affine, hx] at h3
  exact (PrimeSpectrum.mem_basicOpen _ _).1 h3 hr

end GlobalTheory.Desc.GaussBC

namespace GlobalTheory.Desc.GaussBC

section Span

variable {R₁ F₁ : Type} [CommRing R₁] [CommRing F₁] (c : R₁ →+* F₁)

/- English proof (translation)
Assemble the required witnesses or components as `⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩`.
-/
theorem zero_mem_spanBy (T : Set F₁) : (0 : F₁) ∈ spanBy c T := ⟨0, Fin.elim0, Fin.elim0, fun i => i.elim0, by simp⟩

/- English proof (translation)
Take `⟨n, r, t, ht, rfl⟩` from `hv`. Take `⟨m, r', t', ht', rfl⟩` from `hw`. Use `⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩` and prove the remaining obligations. Use `Fin.addCases (fun i => ?_) (fun i => ?_) i` and prove the remaining obligations. Rewrite using `[Fin.append_left]`.

Conclude with `ht i`. Rewrite using `[Fin.append_right]`. Conclude with `ht' i`. Rewrite using `[Fin.sum_univ_add]`. Simplify using the standard rewrite rules.
-/
theorem add_mem_spanBy {T : Set F₁} {v w : F₁} (hv : v ∈ spanBy c T) (hw : w ∈ spanBy c T) :
    v + w ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  obtain ⟨m, r', t', ht', rfl⟩ := hw
  refine ⟨n + m, Fin.append r r', Fin.append t t', fun i => ?_, ?_⟩
  · refine Fin.addCases (fun i => ?_) (fun i => ?_) i
    · rw [Fin.append_left]; exact ht i
    · rw [Fin.append_right]; exact ht' i
  · rw [Fin.sum_univ_add]; simp

/- English proof (translation)
Take `⟨n, r, t, ht, rfl⟩` from `hv`. Conclude with `⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩`.
-/
theorem mul_mem_spanBy {T : Set F₁} {v : F₁} (hv : v ∈ spanBy c T) (d : R₁) : c d * v ∈ spanBy c T := by
  obtain ⟨n, r, t, ht, rfl⟩ := hv
  exact ⟨n, fun i => d * r i, t, ht, by rw [Finset.mul_sum]; simp only [map_mul, _root_.mul_assoc]⟩

/- English proof (translation)
Introduce and unpack `v ⟨n, r, t, ht, rfl⟩`. Conclude with `Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)`.
-/
theorem spanBy_induction {T : Set F₁} (p : F₁ → Prop) (h0 : p 0) (hadd : ∀ a b, p a → p b → p (a + b))
    (hmul : ∀ r, ∀ t ∈ T, p (c r * t)) : ∀ v ∈ spanBy c T, p v := by
  rintro v ⟨n, r, t, ht, rfl⟩
  exact Finset.sum_induction _ p hadd h0 fun i _ => hmul (r i) (t i) (ht i)

end Span

/- English proof (translation)
Proceed by induction on `n with`. Consider the case `zero => rw [pow_zero]`. Conclude with `(unitAt_one x).regAt`. Consider the case `succ n ih => rw [pow_succ]`. Conclude with `ih.mul h`.
-/
theorem regAt_pow {X : Scheme.{0}} [IsIntegral X] {x : X} {f : X.functionField} (h : GlobalTheory.Cartier.RegAt x f) (n : ℕ) :
    GlobalTheory.Cartier.RegAt x (f ^ n) := by
  induction n with
  | zero => rw [pow_zero]; exact (unitAt_one x).regAt
  | succ n ih => rw [pow_succ]; exact ih.mul h

/- English proof (translation)
Introduce `T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'`. Take `⟨ϖ, hϖ⟩` from `IsDiscreteValuationRing.exists_irreducible T`. Establish `hmT` using `hϖ.maximalIdeal_eq`. Establish `hmD : maximalIdeal D = Ideal.span {a ϖ}` using `by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]`. Establish `hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a`.

Take `⟨l, hl1, hl2⟩` from `hff`. Establish `e1` using `gp_comp_eq_spMap_cst H.left T H.hom`. Establish `e2` using `gp_comp_eq_spMap_cst H'.left D H'.hom`. Establish `hl : l = gp H'.left` using `by simpa using hl1`. Establish `key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a)`.

Combine the equalities or inequalities in the displayed calculation. Conclude with `congrArg CommRingCat.Hom.hom (Spec.map_injective key)`. Use `set c := cst H'.hom with hc`. Use `set P := c (a ϖ) with hPdef`. Establish `hP : P = θ (cst H.hom ϖ)` using `by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]`.

Take `⟨hϖ0, hfac⟩` from `GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT`. Establish `hP0 : P ≠ 0` using `by rw [hP]; exact (map_ne_zero θ).2 hϖ0`. Establish `hPz : GlobalTheory.Cartier.ZeroAt y' P` using `(cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)`. Establish `hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u)`. Introduce `u hu`.

Establish `hpt` using `GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'`. Conclude with `GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)`. Establish `hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d)` using `fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1`. Establish `hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t)` using `fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1`. Establish `hmod` using `GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT`.

Use `set S := spanBy c (θ '' regSet y) with hS`. Establish `hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v` using `spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by`. Introduce and unpack `r _ ⟨t, ht, rfl⟩`. Conclude with `(hcreg r).mul (hreg t ht))`. Establish `hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S`.

Introduce `v hv N`. Proceed by induction on `N with`. Consider the case `zero => simpa using hv`. Consider the case `succ N ih => rw [pow_succ', _root_.mul_assoc]`. Conclude with `mul_mem_spanBy c ih _`.

Establish `hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S`. Use `spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_` and prove the remaining obligations. Introduce and unpack `v w ⟨N, hN⟩ ⟨M, hM⟩`. Use `⟨N + M, ?_⟩` and prove the remaining obligations. Use `add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)` as an intermediate fact.

Use `this using 1` and compare the differences between its conclusion and the goal. Expand and normalize the polynomial expressions, which then agree. Introduce and unpack `r _ ⟨u, rfl⟩`. Distinguish the cases in `hu : u = 0`. Conclude with `⟨0, by simpa [hu] using zero_mem_spanBy c _⟩`.

Take `⟨k, w, hw, rfl⟩` from `hfac u hu`. Use `⟨(-k).toNat, ?_⟩` and prove the remaining obligations. Establish `hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ)` using `(Int.toNat_of_nonneg (by omega)).symm`. Establish `e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) = c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w)`. Rewrite using `[hP, map_mul, map_mul, map_zpow₀, map_pow]`.

Establish `hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k = θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat`. Rewrite using `[← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk, zpow_add₀ ((map_ne_zero θ).2 hϖ0)]`. Take the linear combination `(c r * θ w) * hq`. Rewrite using `[e]`. Conclude with `mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r`.

Establish `hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S`. Introduce `N`. Proceed by induction on `N with`. Consider the case `zero => intro t _ h`. Simplify using `using h`.

Consider the case `succ N ih`. Introduce `t ht h`. Rewrite `h` using `[pow_succ', _root_.mul_assoc]`. Take `⟨z₁, hz₁, e⟩` from `hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))`. Establish `: P ^ N * t = z₁` using `mul_left_cancel₀ hP0 e`.

Conclude with `ih t ht (this ▸ hz₁)`. Use `⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩` and prove the remaining obligations. Take `⟨N, hN⟩` from `hQ _ hdv`. Establish `hirr : Irreducible (a ϖ)` using `(IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD`. Take `⟨n, u, rfl⟩` from `IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr`.

Establish `e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v))`. Rewrite using `[hPdef, map_mul, map_pow]`. Establish `: c (↑u⁻¹ : D) * c ↑u = 1` using `by rw [← map_mul, Units.inv_mul, map_one]`. Take the linear combination `(-(c (a ϖ) ^ (N + n) * v)) * this`. Use `⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩` and prove the remaining obligations.

Rewrite using `[map_one, _root_.one_mul]`. Conclude with `hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)`. Take `⟨u, rfl⟩` from `IsLocalRing.notMem_maximalIdeal.1 hs`. Establish `e : v = c (↑u⁻¹ : D) * (c ↑u * v)` using `by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]`. Rewrite using `[e]`.

Conclude with `(hcreg _).mul (hSreg _ hsv)`. Use extensionality with `u`. Use `⟨fun h => ?_, fun h => hreg u h⟩` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `GlobalTheory.Cartier.RegAt y' (θ u) at h`. Express the relevant statement in the definitionally equal form `GlobalTheory.Cartier.RegAt y u`.

Distinguish the cases in `hu : u = 0`. Rewrite using `[hu]`. Conclude with `regAt_zero y`. Take `⟨k, w, hw, rfl⟩` from `hfac u hu`. Break down `le_or_gt 0 k with hk | hk` into its components or cases.

Use `lift k to ℕ using hk`. Rewrite using `[zpow_natCast]`. Conclude with `(regAt_pow (hc0reg ϖ) k).mul hw.regAt`. It suffices to derive a contradiction. Establish `hw0` using `hw.ne_zero`.

Take `⟨hw1, hw2⟩` from `(unitAt_iff hw0).1 hw`. Establish `hθw : GlobalTheory.Cartier.UnitAt y' (θ w)` using `(unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩`. Establish `hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1)` using `Int.toNat_of_nonneg (by omega)`. Establish `e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat`. Rewrite using `[map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0), _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]`.

Establish `hPi : GlobalTheory.Cartier.RegAt y' P⁻¹`. Rewrite using `[e]`. Conclude with `(h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)`. Conclude with `(zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)`. Conclude with `GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩`.
-/
theorem gauss_baseChange : ∀ (T D : Type) [CommRing T] [IsDomain T] [IsDiscreteValuationRing T] [CommRing D] [IsDomain D] [IsDiscreteValuationRing D] (a : T →+* D), a.Flat → (maximalIdeal T).map a = maximalIdeal D → ∀ (H : Over (Sp T)) [GrpObj H] [IsIntegral H.left] (H' : Over (Sp D)) [GrpObj H'] [IsIntegral H'.left] (π : H'.left ⟶ H.left) (θ : H.left.functionField →+* H'.left.functionField), IsSemiAbelian H → IsPullback π H'.hom H.hom (spMap a) → PFF (𝟙 _) π θ → ∀ (y : H.left) (y' : H'.left), H.hom y = closedPoint T → H'.hom y' = closedPoint D → ringKrullDim (H.left.presheaf.stalk y) = 1 → ringKrullDim (H'.left.presheaf.stalk y') = 1 → GaussAt (GlobalTheory.Desc.cst H'.hom) (maximalIdeal D) θ (regSet y) (regSet y') ∧ θ ⁻¹' (regSet y') = regSet y ∧ LinDisj (GlobalTheory.Desc.cst H.hom) (GlobalTheory.Desc.cst H'.hom) θ := by
  intro T D _ _ _ _ _ _ a ha hm H _ _ H' _ _ π θ hH hpb hff y y' hy hy' hdy hdy'
  obtain ⟨ϖ, hϖ⟩ := IsDiscreteValuationRing.exists_irreducible T
  have hmT := hϖ.maximalIdeal_eq
  have hmD : maximalIdeal D = Ideal.span {a ϖ} := by rw [← hm, hmT, Ideal.map_span, Set.image_singleton]

  have hcomp : θ.comp (cst H.hom) = (cst H'.hom).comp a := by
    obtain ⟨l, hl1, hl2⟩ := hff
    have e1 := gp_comp_eq_spMap_cst H.left T H.hom
    have e2 := gp_comp_eq_spMap_cst H'.left D H'.hom
    have hl : l = gp H'.left := by simpa using hl1
    have key : spMap (θ.comp (cst H.hom)) = spMap ((cst H'.hom).comp a) := by
      calc spMap (θ.comp (cst H.hom)) = spMap θ ≫ spMap (cst H.hom) := by simp [spMap, CommRingCat.ofHom_comp]
        _ = spMap θ ≫ gp H.left ≫ H.hom := by rw [e1]
        _ = l ≫ π ≫ H.hom := by rw [← Category.assoc, ← hl2, Category.assoc]
        _ = gp H'.left ≫ H'.hom ≫ spMap a := by rw [hpb.w, hl]
        _ = spMap (cst H'.hom) ≫ spMap a := by rw [← Category.assoc, e2]
        _ = spMap ((cst H'.hom).comp a) := by simp [spMap, CommRingCat.ofHom_comp]
    exact congrArg CommRingCat.Hom.hom (Spec.map_injective key)
  set c := cst H'.hom with hc
  set P := c (a ϖ) with hPdef
  have hP : P = θ (cst H.hom ϖ) := by rw [hPdef, ← RingHom.comp_apply, ← hcomp, RingHom.comp_apply]
  obtain ⟨hϖ0, hfac⟩ := GlobalTheory.T.semiAbelian_dvr_closedFibre_stalk_uniformiser T H hH y hy hdy ϖ hmT
  have hP0 : P ≠ 0 := by rw [hP]; exact (map_ne_zero θ).2 hϖ0
  have hPz : GlobalTheory.Cartier.ZeroAt y' P :=
    (cst_regAt_zeroAt D H'.left H'.hom y' hy' (a ϖ)).2 (by rw [hmD]; exact Ideal.subset_span rfl)
  have hreg : ∀ u, GlobalTheory.Cartier.RegAt y u → GlobalTheory.Cartier.RegAt y' (θ u) := by
    intro u hu
    have hpt := GlobalTheory.T.baseChange_sends_closedFibre_genericPoint_dvr T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy'
    exact GlobalTheory.T.regularAtPoint_functionField_map_of_genericPoint_comp H.left H'.left π θ ⟨_, hff.choose_spec⟩ y' u (hpt ▸ hu)
  have hcreg : ∀ d, GlobalTheory.Cartier.RegAt y' (c d) := fun d => (cst_regAt_zeroAt D H'.left H'.hom y' hy' d).1
  have hc0reg : ∀ t, GlobalTheory.Cartier.RegAt y (cst H.hom t) := fun t => (cst_regAt_zeroAt T H.left H.hom y hy t).1
  have hmod := GlobalTheory.T.thetaSpan_vanishing_eq_uniformiser_mul T D a ha hm H H' π θ hH hpb ⟨_, hff.choose_spec⟩ y y' hy hy' hdy hdy' ϖ hmT
  set S := spanBy c (θ '' regSet y) with hS
  have hSreg : ∀ v ∈ S, GlobalTheory.Cartier.RegAt y' v :=
    spanBy_induction c _ (regAt_zero y') (fun _ _ h h' => h.add h') (by
      rintro r _ ⟨t, ht, rfl⟩; exact (hcreg r).mul (hreg t ht))
  have hSP : ∀ v ∈ S, ∀ N : ℕ, P ^ N * v ∈ S := by
    intro v hv N
    induction N with
    | zero => simpa using hv
    | succ N ih => rw [pow_succ', _root_.mul_assoc]; exact mul_mem_spanBy c ih _

  have hQ : ∀ v ∈ spanBy c (Set.range θ), ∃ N : ℕ, P ^ N * v ∈ S := by
    refine spanBy_induction c _ ⟨0, by simpa using zero_mem_spanBy c _⟩ ?_ ?_
    · rintro v w ⟨N, hN⟩ ⟨M, hM⟩
      refine ⟨N + M, ?_⟩
      have := add_mem_spanBy c (hSP _ hN M) (hSP _ hM N)
      convert this using 1; ring
    · rintro r _ ⟨u, rfl⟩
      by_cases hu : u = 0
      · exact ⟨0, by simpa [hu] using zero_mem_spanBy c _⟩
      obtain ⟨k, w, hw, rfl⟩ := hfac u hu
      refine ⟨(-k).toNat, ?_⟩
      have hk : ((-k).toNat : ℤ) + k = ((((-k).toNat : ℤ) + k).toNat : ℤ) :=
        (Int.toNat_of_nonneg (by omega)).symm
      have e : P ^ (-k).toNat * (c r * θ (cst H.hom ϖ ^ k * w)) =
          c r * θ (cst H.hom ϖ ^ (((-k).toNat : ℤ) + k).toNat * w) := by
        rw [hP, map_mul, map_mul, map_zpow₀, map_pow]
        have hq : θ (cst H.hom ϖ) ^ (-k).toNat * θ (cst H.hom ϖ) ^ k =
            θ (cst H.hom ϖ) ^ (((-k).toNat : ℤ) + k).toNat := by
          rw [← zpow_natCast, ← zpow_natCast _ (((-k).toNat : ℤ) + k).toNat, ← hk,
            zpow_add₀ ((map_ne_zero θ).2 hϖ0)]
        linear_combination (c r * θ w) * hq
      rw [e]
      exact mul_mem_spanBy c (subset_spanBy c (θ '' regSet y) (Set.mem_image_of_mem θ
        (show _ ∈ regSet y from (regAt_pow (hc0reg ϖ) _).mul hw.regAt))) r

  have hB : ∀ (N : ℕ) (t : H'.left.functionField), GlobalTheory.Cartier.RegAt y' t → P ^ N * t ∈ S → t ∈ S := by
    intro N
    induction N with
    | zero => intro t _ h; simpa using h
    | succ N ih =>
      intro t ht h
      rw [pow_succ', _root_.mul_assoc] at h
      obtain ⟨z₁, hz₁, e⟩ := hmod _ h (hPz.mul ((regAt_pow hPz.regAt N).mul ht))
      have : P ^ N * t = z₁ := mul_left_cancel₀ hP0 e
      exact ih t ht (this ▸ hz₁)
  refine ⟨fun v ⟨d, hd0, hdv⟩ => ⟨fun hv => ?_, fun ⟨s, hs, hsv⟩ => ?_⟩, ?_, ?_⟩
  · obtain ⟨N, hN⟩ := hQ _ hdv
    have hirr : Irreducible (a ϖ) := (IsDiscreteValuationRing.irreducible_iff_uniformizer _).2 hmD
    obtain ⟨n, u, rfl⟩ := IsDiscreteValuationRing.eq_unit_mul_pow_irreducible hd0 hirr
    have e : P ^ (N + n) * v = c (↑u⁻¹ : D) * (P ^ N * (c (↑u * a ϖ ^ n) * v)) := by
      rw [hPdef, map_mul, map_pow]
      have : c (↑u⁻¹ : D) * c ↑u = 1 := by rw [← map_mul, Units.inv_mul, map_one]
      linear_combination (-(c (a ϖ) ^ (N + n) * v)) * this
    refine ⟨1, fun h => (maximalIdeal.isMaximal D).ne_top ((Ideal.eq_top_iff_one _).2 h), ?_⟩
    rw [map_one, _root_.one_mul]
    exact hB (N + n) v hv (e ▸ mul_mem_spanBy c hN _)
  · obtain ⟨u, rfl⟩ := IsLocalRing.notMem_maximalIdeal.1 hs
    have e : v = c (↑u⁻¹ : D) * (c ↑u * v) := by rw [← _root_.mul_assoc, ← map_mul, Units.inv_mul, map_one, _root_.one_mul]
    rw [e]; exact (hcreg _).mul (hSreg _ hsv)
  · ext u
    refine ⟨fun h => ?_, fun h => hreg u h⟩
    change GlobalTheory.Cartier.RegAt y' (θ u) at h
    change GlobalTheory.Cartier.RegAt y u
    by_cases hu : u = 0
    · rw [hu]; exact regAt_zero y
    obtain ⟨k, w, hw, rfl⟩ := hfac u hu
    rcases le_or_gt 0 k with hk | hk
    · lift k to ℕ using hk
      rw [zpow_natCast]; exact (regAt_pow (hc0reg ϖ) k).mul hw.regAt
    · exfalso
      have hw0 := hw.ne_zero
      obtain ⟨hw1, hw2⟩ := (unitAt_iff hw0).1 hw
      have hθw : GlobalTheory.Cartier.UnitAt y' (θ w) :=
        (unitAt_iff ((map_ne_zero θ).2 hw0)).2 ⟨hreg w hw1, by rw [← map_inv₀]; exact hreg _ hw2⟩
      have hm1 : ((-(k + 1)).toNat : ℤ) = -(k + 1) := Int.toNat_of_nonneg (by omega)
      have e : P⁻¹ = θ (cst H.hom ϖ ^ k * w) * (θ w)⁻¹ * P ^ (-(k + 1)).toNat := by
        rw [map_mul, map_zpow₀, ← hP, _root_.mul_assoc (P ^ k), mul_inv_cancel₀ ((map_ne_zero θ).2 hw0),
          _root_.mul_one, ← zpow_natCast, hm1, ← zpow_add₀ hP0, show k + -(k + 1) = -1 by ring, zpow_neg_one]
      have hPi : GlobalTheory.Cartier.RegAt y' P⁻¹ := by
        rw [e]; exact (h.mul hθw.inv.regAt).mul (regAt_pow hPz.regAt _)
      exact (zeroAt_iff.1 hPz).2 ((unitAt_iff hP0).2 ⟨hPz.regAt, hPi⟩)
  · exact GlobalTheory.T.linearlyDisjoint_functionField_of_flat_baseChange T D a ha H H' π θ hpb ⟨_, hff.choose_spec⟩

end GlobalTheory.Desc.GaussBC
