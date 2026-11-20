import Mathlib
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LocRatio
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GrGenOfIsFlagVBOn
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.IsExcisionNbhdAway
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.GradedSandwichDegreeBoundStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.RegularFunctionalSpecializesStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.LieModelLocalizationAtPrimeStatement
import Development.AutomorphicSpectrum.Proofs.GeometryProofs.CoordValuationBoundLocalStatement
open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj NumberField TensorProduct Filter Topology Matrix
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Geo ReciprocityTheory.ChartRestriction.G.Geo.Tor ReciprocityTheory.ChartRestriction.G.Semi GlobalTheory.CompanionTheory.Ar
open GlobalTheory.CompanionTheory.Ar.RootHt GroundTheory.Heights₂.Heights

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

/- English proof (translation)
Establish `h1 : IsUnit s` using `hφ.map_nonunit s hu`. Take `⟨u, rfl⟩` from `h1`. Use `⟨(u⁻¹ : Sˣ).1, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[← map_mul, Units.mul_inv, map_one]`. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations.

Rewrite using `[← map_mul, Units.inv_mul, map_one]`.
-/
theorem unit_aux {S R F : Type} [CommRing S] [CommRing R] [Field F] (ψ : S →+* F) (φ : S →+* R) (hφ : IsLocalHom φ)
    (s : S) (hu : IsUnit (φ s)) : ∃ s', φ s * φ s' = 1 ∧ ψ s' = (ψ s)⁻¹ := by
  have h1 : IsUnit s := hφ.map_nonunit s hu
  obtain ⟨u, rfl⟩ := h1
  refine ⟨(u⁻¹ : Sˣ).1, ?_, ?_⟩
  · rw [← map_mul, Units.mul_inv, map_one]
  · refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul, Units.inv_mul, map_one]

section Val
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {R : Type} [CommRing R] [IsLocalRing R] {z : Sp R ⟶ X}

/- English proof (translation)
Take `⟨h1, s, rfl, rfl⟩` from `h`. Take `⟨_, s', rfl, rfl⟩` from `h'`. Conclude with `⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩`.
-/
theorem val_mul {a a' : Ω} {r r' : R} (h : ValAt ξ z a r) (h' : ValAt ξ z a' r') : ValAt ξ z (a * a') (r * r') := by
  obtain ⟨h1, s, rfl, rfl⟩ := h
  obtain ⟨_, s', rfl, rfl⟩ := h'
  exact ⟨h1, s * s', map_mul _ _ _, map_mul _ _ _⟩

/- English proof (translation)
Assemble the required witnesses or components as `⟨h, n, map_natCast _ _, map_natCast _ _⟩`.
-/
theorem val_natCast (h : genPt ξ ⤳ centre z) (n : ℕ) : ValAt ξ z (n : Ω) (n : R) :=
  ⟨h, n, map_natCast _ _, map_natCast _ _⟩

/- English proof (translation)
Take `⟨s, hs⟩` from `ha`. Conclude with `⟨_, h, s, hs, rfl⟩`.
-/
theorem val_of_mem (h : genPt ξ ⤳ centre z) {a : Ω} (ha : a ∈ regAt ξ ⟨centre z, h⟩) : ∃ r, ValAt ξ z a r := by
  obtain ⟨s, hs⟩ := ha
  exact ⟨_, h, s, hs, rfl⟩

/- English proof (translation)
Take `⟨h, s, rfl, rfl⟩` from `hs`. Take `⟨s', h1, h2⟩` from `unit_aux (genMap ξ ⟨centre z, h⟩) (Scheme.stalkClosedPointTo z).hom (Scheme.isLocalHom_stalkClosedPointTo' z) s hu`. Conclude with `⟨_, h1, h, s', h2, rfl⟩`.
-/
theorem val_inv {a : Ω} {r : R} (hs : ValAt ξ z a r) (hu : IsUnit r) : ∃ r', r * r' = 1 ∧ ValAt ξ z a⁻¹ r' := by
  obtain ⟨h, s, rfl, rfl⟩ := hs
  obtain ⟨s', h1, h2⟩ := unit_aux (genMap ξ ⟨centre z, h⟩) (Scheme.stalkClosedPointTo z).hom
    (Scheme.isLocalHom_stalkClosedPointTo' z) s hu
  exact ⟨_, h1, h, s', h2, rfl⟩

/- English proof (translation)
Take `⟨r', h1, h2⟩` from `val_inv hs (isUnit_iff_ne_zero.2 hr)`. Rewrite using `[← eq_inv_of_mul_eq_one_right h1]` and apply the resulting hypothesis.
-/
theorem val_inv₀ {F : Type} [Field F] {z : Sp F ⟶ X} {a : Ω} {r : F} (hs : ValAt ξ z a r) (hr : r ≠ 0) :
    ValAt ξ z a⁻¹ r⁻¹ := by
  obtain ⟨r', h1, h2⟩ := val_inv hs (isUnit_iff_ne_zero.2 hr)
  rwa [← eq_inv_of_mul_eq_one_right h1]

end Val
end GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

section Main
variable {X : Scheme.{0}} {Ω : Type} [Field Ω] {ξ : Sp Ω ⟶ X} {K : Type} [Fintype K] {J : K → Type}
  [∀ k, Fintype (J k)] {y : (Σ k, J k) → Ω} {L : Type} [Field L]

/- English proof (translation)
Establish `h1 : ∀ k, y ⟨k, c₀ k⟩ ≠ 0` using `fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hc₀ k))).1`. Establish `h2 : ∀ k, y ⟨k, c k⟩ ≠ 0` using `fun k => (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).1`. Establish `h3 : ∀ k, ValAt ξ z (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩)` using `fun k => by`. Take `⟨r, hr, e⟩` from `(hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hc₀ k))).2 (c k)`. Rewrite using `[e, mul_div_cancel_right₀ _ (hc₀ k)]` and apply the resulting hypothesis.

Establish `h4 : ∀ (k) (n : ℤ), ValAt ξ z ((y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ n) ((w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ n)` using `fun k n => by`. Establish `hr : w ⟨k, c k⟩ / w ⟨k, c₀ k⟩ ≠ 0` using `div_ne_zero (hc k) (hc₀ k)`. Establish `pw : ∀ (a : Ω) (r : L), ValAt ξ z a r → ∀ n : ℕ, ValAt ξ z (a ^ n) (r ^ n)` using `fun a r h n => by`. Proceed by induction on `n with`. Consider the case `zero => simpa using val_natCast hz 1`.

Consider the case `succ n ih => rw [pow_succ, pow_succ]`. Conclude with `val_mul ih h`. Break down `n with n | n` into its components or cases. Simplify using `using pw _ _ (h3 k) n`. Rewrite using `[zpow_negSucc, zpow_negSucc]`.

Conclude with `val_inv₀ (pw _ _ (h3 k) _) (pow_ne_zero _ hr)`. Establish `h5 : gen y a e₀ c / gen y a e₀ c₀ = ∏ k, (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ a k`. Unfold `gen`. Rewrite using `[mul_div_mul_right _ _ he₀, ← Finset.prod_div_distrib]`. Conclude with `Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm`.

Rewrite using `[h5]`. Establish `pr : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ a k) (∏ k ∈ s, (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ a k)` using `fun s => by classical`. Proceed by induction on `s using Finset.induction_on with`. Consider the case `empty => simpa using val_natCast hz 1`. Consider the case `insert k s hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]`.

Conclude with `val_mul (h4 k _) ih`. Conclude with `pr _`.
-/
theorem val_gen_ratio {z : Sp L ⟶ X} {w : (Σ k, J k) → L} (hw : CoordsAt ξ y z w) (hz : genPt ξ ⤳ centre z)
    (a : K → ℤ) {e₀ : Ω} (he₀ : e₀ ≠ 0) (c c₀ : (k : K) → J k) (hc : ∀ k, w ⟨k, c k⟩ ≠ 0)
    (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0) :
    ValAt ξ z (gen y a e₀ c / gen y a e₀ c₀) (∏ k, (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ a k) := by
  have h1 : ∀ k, y ⟨k, c₀ k⟩ ≠ 0 := fun k => (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hc₀ k))).1
  have h2 : ∀ k, y ⟨k, c k⟩ ≠ 0 := fun k => (hw.2 k (c k) (isUnit_iff_ne_zero.2 (hc k))).1
  have h3 : ∀ k, ValAt ξ z (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) := fun k => by
    obtain ⟨r, hr, e⟩ := (hw.2 k (c₀ k) (isUnit_iff_ne_zero.2 (hc₀ k))).2 (c k)
    rwa [e, mul_div_cancel_right₀ _ (hc₀ k)]
  have h4 : ∀ (k) (n : ℤ), ValAt ξ z ((y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ n) ((w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ n) := fun k n => by
    have hr : w ⟨k, c k⟩ / w ⟨k, c₀ k⟩ ≠ 0 := div_ne_zero (hc k) (hc₀ k)
    have pw : ∀ (a : Ω) (r : L), ValAt ξ z a r → ∀ n : ℕ, ValAt ξ z (a ^ n) (r ^ n) := fun a r h n => by
      induction n with
      | zero => simpa using val_natCast hz 1
      | succ n ih => rw [pow_succ, pow_succ]; exact val_mul ih h
    rcases n with n | n
    · simpa using pw _ _ (h3 k) n
    · rw [zpow_negSucc, zpow_negSucc]
      exact val_inv₀ (pw _ _ (h3 k) _) (pow_ne_zero _ hr)
  have h5 : gen y a e₀ c / gen y a e₀ c₀ = ∏ k, (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ a k := by
    unfold gen
    rw [mul_div_mul_right _ _ he₀, ← Finset.prod_div_distrib]
    exact Finset.prod_congr rfl fun k _ => (div_zpow _ _ _).symm
  rw [h5]
  have pr : ∀ s : Finset K, ValAt ξ z (∏ k ∈ s, (y ⟨k, c k⟩ / y ⟨k, c₀ k⟩) ^ a k)
      (∏ k ∈ s, (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ a k) := fun s => by
    classical
    induction s using Finset.induction_on with
    | empty => simpa using val_natCast hz 1
    | insert k s hk ih => rw [Finset.prod_insert hk, Finset.prod_insert hk]; exact val_mul (h4 k _) ih
  exact pr _

end Main
end GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

/- English proof (translation)
Establish `hξ` using `hcoord.gen`. Establish `hm0 : (m : Ω) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `hmL : (m : L) ≠ 0` using `Nat.cast_ne_zero.2 hm.ne'`. Establish `he₀ : e₀ ≠ 0` using `hdeg.1`. Use `set zA : Sp A ⟶ X := spMap (algebraMap (𝓞 L) A) ≫ z with hzA`.

Establish `hzL : spMap (algebraMap (𝓞 L) L) ≫ z = spMap (algebraMap A L) ≫ zA`. Rewrite using `[hzA, ← Category.assoc, IsScalarTower.algebraMap_eq (𝓞 L) A L]`. Simplify using `only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]`. Take `⟨c, h, hcne, hmax, hin⟩` from `GlobalTheory.T.coord_valuation_bound_local X Ω ξ K J y L w v A zA hgen hcoord hA₁ hA₂ (hzL ▸ hw)`. Take `⟨b, π, κ, hfl, -, hmb, hdual, hreg, hκ0, hκ, hκi, hcls⟩` from `GlobalTheory.T.exists_graded_sandwich_coordinates X Ω ξ K J y G Li M V r b₀ m i a e₀ hb₀ hS hdeg ⟨centre zA, h⟩ c hin`.

Use `set f : Module.Dual Ω Li := (m : Ω) • π i with hfdef`. Establish `hfe : ∀ e, f e = (m : Ω) * π i e` using `fun e => rfl`. Establish `hf : ∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩` using `fun e he => hreg i e he`. Establish `hLz : centre (spMap (algebraMap (𝓞 L) L) ≫ z) ⤳ centre zA`. Rewrite using `[hzL]`.

Conclude with `LieTangent.centre_specializes (algebraMap A L) zA`. Establish `hfL : ∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩` using `fun h' => GlobalTheory.T.regular_functional_specializes X G Ω ξ Li M f ⟨_, h⟩ ⟨_, h'⟩ hξ hLz hf`. Take `⟨g, hg1, hg2⟩` from `GlobalTheory.T.lie_model_localization_at_prime X G Ω ξ Li M L 𝔭 A z B MB f h hξ hf hfL`. Take `⟨kA, hkA⟩` from `val_of_mem h hκ`. Take `⟨kA', hkA'⟩` from `val_of_mem h hκi`.

Establish `hkk : kA * kA' = 1`. Establish `h1` using `val_mul hkA hkA'`. Rewrite `h1` using `[mul_inv_cancel₀ hκ0]`. Establish `h2` using `val_natCast (ξ := ξ) (z := zA) h 1`. Rewrite `h2` using `[Nat.cast_one, Nat.cast_one]`.

Conclude with `LieTangent.valAt_unique hξ h1 h2`. Establish `hvk : v (algebraMap A L kA) = 1`. Establish `h1 : v (algebraMap A L kA) * v (algebraMap A L kA') = 1`. Rewrite using `[← map_mul, ← map_mul, hkk, map_one, map_one]`. Establish `h2` using `hA₁ kA`.

Establish `h3` using `hA₁ kA'`. Use polynomial arithmetic with `[apply_nonneg v (algebraMap A L kA), apply_nonneg v (algebraMap A L kA')]`. Establish `hkL : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap A L kA)`. Rewrite using `[hzL]`. Conclude with `LieTangent.valAt_base hξ (algebraMap A L) hkA`.

Establish `hτ` using `val_gen_ratio hw (hgen _) a he₀ c c₀ hcne hc₀`. Use `set τ : L := ∏ k, (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ a k with hτdef`. Establish `gne : ∀ c' : (k : K) → J k, (∀ k, w ⟨k, c' k⟩ ≠ 0) → gen y a e₀ c' ≠ 0` using `fun c' hc' => mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ => zpow_ne_zero _ (hw.2 k (c' k) (isUnit_iff_ne_zero.2 (hc' k))).1) he₀`. Use `set C : L := (m : L)⁻¹ * algebraMap A L kA * τ with hC`. Establish `hvalm : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (m : Ω)⁻¹ (m : L)⁻¹` using `val_inv₀ (val_natCast (hgen _) m) hmL`.

Establish `key : ∀ (x' : B.carrier) (hx' : x' ∈ F₁) (e : Li) (vv : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G), e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e vv → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' vv → φ ⟨x', hx'⟩ = C * algebraMap A L (g x')`. Introduce `x' hx' e vv hU hv' hl`. Take `⟨h', he⟩` from `(LieModel.exists_valAt_iff M _ e).1 ⟨vv, hv'⟩`. Take `⟨u₀, hu₀⟩` from `val_of_mem h' (hfL h' e he)`. Establish `hg` using `hg1 x' e vv u₀ hv' hl hu₀`.

Choose the witnesses or unpack the hypotheses as in `⟨t, ht⟩ : ∃ t, IsCls b₀ i e t := by`. Establish `hU'` using `hU`. Rewrite `hU'` using `[Flag.step_succ]`. Take `⟨y', hy', z', hz', rfl⟩` from `Submodule.mem_sup.1 hU'`. Take `⟨t, rfl⟩` from `Submodule.mem_span_singleton.1 hz'`.

Conclude with `⟨t, by simpa [IsCls] using hy'⟩`. Establish `e1` using `hcls e t hU ht`. Establish `e2 : t / gen y a e₀ c₀ = (m : Ω)⁻¹ * f e * κ * (gen y a e₀ c / gen y a e₀ c₀)`. Rewrite using `[hfe, ← _root_.mul_assoc, inv_mul_cancel₀ hm0, _root_.one_mul, ← e1, div_mul_div_cancel₀ (gne c hcne)]`. Establish `e3` using `hφ ⟨x', hx'⟩ e vv t _ hU hv' hl ht (e2 ▸ val_mul (val_mul (val_mul hvalm hu₀) hkL) hτ)`.

Rewrite using `[e3, hg, hC]`. Expand and normalize the polynomial expressions, which then agree. Set `gL : B.carrier →ₗ[𝓞 L] L` to `(IsScalarTower.toAlgHom (𝓞 L) A L).toLinearMap ∘ₗ g`. Establish `hgL : ∀ x, gL x = algebraMap A L (g x)` using `fun x => rfl`. Set `D : F₁ →ₗ[𝓞 L] L` to `φ - C • (gL ∘ₗ F₁.subtype)`.

Establish `hD : ∀ x : F₁, D x = φ x - C * algebraMap A L (g x)` using `fun x => rfl`. Establish `hall : ∀ x : F₁, φ x = C * algebraMap A L (g x)`. Introduce and unpack `⟨x, hx⟩`. Take `⟨a₁, ha₁, hsp⟩` from `(hF₁ x).1 hx`. Establish `hind : ∀ y' ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ flagStep Ω b₀ (i + 1), ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G, M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v}, ∃ hy : y' ∈ F₁, D ⟨y', hy⟩ = 0`.

Introduce `y' hy'`. Proceed by induction on `hy' using Submodule.span_induction with`. Consider the case `mem x' hx'`. Take `⟨e, hU, vv, hv', hl⟩` from `hx'`. Establish `hm' : x' ∈ F₁` using `(hF₁ x').2 ⟨1, one_ne_zero, by`.

Rewrite using `[one_smul]`. Conclude with `Submodule.subset_span ⟨e, hU, vv, hv', hl⟩⟩`. Conclude with `⟨hm', by rw [hD, key x' hm' e vv hU hv' hl, sub_self]⟩`. Consider the case `zero => exact ⟨zero_mem _, map_zero D⟩`. Consider the case `add y₁ y₂ _ _ i₁ i₂`.

Take `⟨h₁, e₁⟩` from `i₁`. Take `⟨h₂, e₂⟩` from `i₂`. Use `⟨add_mem h₁ h₂, ?_⟩` and prove the remaining obligations. Establish `: D (⟨y₁, h₁⟩ + ⟨y₂, h₂⟩) = 0` using `by rw [map_add, e₁, e₂, add_zero]`. Conclude with `this`.

Consider the case `smul s y _ i₁`. Take `⟨h₁, e₁⟩` from `i₁`. Use `⟨F₁.smul_mem s h₁, ?_⟩` and prove the remaining obligations. Establish `: D (s • ⟨y, h₁⟩) = 0` using `by rw [map_smul, e₁, smul_zero]`. Conclude with `this`.

Take `⟨hy, e⟩` from `hind _ hsp`. Establish `e' : D (a₁ • ⟨x, hx⟩) = 0` using `e`. Rewrite `e'` using `[map_smul]`. Establish `e''` using `(smul_eq_zero.1 e').resolve_left ha₁`. Rewrite `e''` using `[hD]`.

Conclude with `sub_eq_zero.1 e''`. Establish `hsup : ∀ k, (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, c k⟩)` using `fun k => by haveI : Nonempty (J k) := ⟨c k⟩`. Conclude with `le_antisymm (ciSup_le (hmax k)) (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (c k))`. Establish `hvC : v C = (v (m : L))⁻¹ * locRatio a w c₀ v`. Establish `: v τ = locRatio a w c₀ v`.

Rewrite using `[hτdef, locRatio, map_prod]`. Conclude with `Finset.prod_congr rfl fun k _ => by rw [map_zpow₀, map_div₀, hsup]`. Rewrite using `[hC, map_mul, map_mul, map_inv₀, hvk, this, _root_.mul_one]`. Establish `hvm : v (m : L) ≠ 0` using `(FinitePlace.pos_iff.2 hmL).ne'`. Use `⟨fun x => ?_, ?_⟩` and prove the remaining obligations.

Rewrite using `[hall, map_mul, hvC]`. Conclude with `mul_le_of_le_one_right (hvC ▸ apply_nonneg v C) (hA₁ _)`. Establish `hU : (m : Ω) • b i ∈ flagStep Ω b₀ (i + 1)`. Rewrite using `[← hfl]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp, rfl⟩)`.

Establish `hfm : f ((m : Ω) • b i) = (m : Ω) * (m : Ω)`. Rewrite using `[hfe, map_smul, hdual i i]`. Simplify using the standard rewrite rules. Establish `hval : ValAt ξ zA (f ((m : Ω) • b i)) ((m : A) * (m : A))`. Rewrite using `[hfm]`.

Conclude with `val_mul (val_natCast h m) (val_natCast h m)`. Take `⟨d, n, x, x', vv, hd, hn, hgx, hvv, hl, hnx⟩` from `hg2 _ _ (hmb i) hval`. Establish `hxF : x ∈ F₁` using `(hF₁ x).2 ⟨(n : 𝓞 L), Nat.cast_ne_zero.2 hn, by`. Rewrite using `[hnx]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.smul_mem _ _ hU, vv, hvv, hl⟩)⟩`.

Use `⟨⟨x, hxF⟩, le_of_eq ?_⟩` and prove the remaining obligations. Establish `e4 : algebraMap A L (algebraMap (𝓞 L) A d * ((m : A) * (m : A))) = algebraMap (𝓞 L) L d * ((m : L) * (m : L))`. Simplify using `[IsScalarTower.algebraMap_apply (𝓞 L) A L]`. Rewrite using `[hall, map_mul, hvC, hgx, e4, map_mul, map_mul, hv d hd]`. Clear the denominators using the available nonvanishing facts.
-/
theorem core (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω)
    (hchar : CharZero Ω) (hgen : ∀ q : X, genPt ξ ⤳ q)
    (hcoord : CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩)) (hm : 0 < m)
    (hb₀ : LinearIndependent Ω b₀) (hS : Sandwich M V b₀ m) (hdeg : (V.gr b₀ i).IsDegOn Set.univ y a e₀)
    (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X)
    (hw : CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w) (B : HermitianBundle.{0} L)
    (MB : LieModel G z B.carrier) (F₁ : Submodule (𝓞 L) B.carrier)
    (hF₁ : IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁) (c₀ : (k : K) → J k) (hc₀ : ∀ k, w ⟨k, c₀ k⟩ ≠ 0)
    (φ : F₁ →ₗ[𝓞 L] L)
    (hφ : ∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (x : B.carrier) v →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u)
    (v : FinitePlace L) (𝔭 : Ideal (𝓞 L)) [𝔭.IsPrime] (A : Type) [CommRing A] [IsLocalRing A]
    [Algebra (𝓞 L) A] [IsLocalization.AtPrime A 𝔭] [Algebra A L] [IsScalarTower (𝓞 L) A L]
    (hv : ∀ d : 𝓞 L, d ∉ 𝔭 → v (algebraMap (𝓞 L) L d) = 1)
    (hA₁ : ∀ r : A, v (algebraMap A L r) ≤ 1) (hA₂ : ∀ r : A, v (algebraMap A L r) = 1 → IsUnit r) :
    (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * locRatio a w c₀ v) ∧ ∃ x, v (m : L) * locRatio a w c₀ v ≤ v (φ x) := by
  have hξ := hcoord.gen
  have hm0 : (m : Ω) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have hmL : (m : L) ≠ 0 := Nat.cast_ne_zero.2 hm.ne'
  have he₀ : e₀ ≠ 0 := hdeg.1
  set zA : Sp A ⟶ X := spMap (algebraMap (𝓞 L) A) ≫ z with hzA
  have hzL : spMap (algebraMap (𝓞 L) L) ≫ z = spMap (algebraMap A L) ≫ zA := by
    rw [hzA, ← Category.assoc, IsScalarTower.algebraMap_eq (𝓞 L) A L]
    simp only [spMap, CommRingCat.ofHom_comp, Spec.map_comp]
  obtain ⟨c, h, hcne, hmax, hin⟩ := GlobalTheory.T.coord_valuation_bound_local X Ω ξ K J y L w v A zA hgen hcoord hA₁ hA₂ (hzL ▸ hw)
  obtain ⟨b, π, κ, hfl, -, hmb, hdual, hreg, hκ0, hκ, hκi, hcls⟩ :=
    GlobalTheory.T.exists_graded_sandwich_coordinates X Ω ξ K J y G Li M V r b₀ m i a e₀ hb₀ hS hdeg ⟨centre zA, h⟩ c hin
  set f : Module.Dual Ω Li := (m : Ω) • π i with hfdef
  have hfe : ∀ e, f e = (m : Ω) * π i e := fun e => rfl
  have hf : ∀ e ∈ M.lat ⟨_, h⟩, f e ∈ regAt ξ ⟨_, h⟩ := fun e he => hreg i e he
  have hLz : centre (spMap (algebraMap (𝓞 L) L) ≫ z) ⤳ centre zA := by
    rw [hzL]; exact LieTangent.centre_specializes (algebraMap A L) zA
  have hfL : ∀ h' : genPt ξ ⤳ centre (spMap (algebraMap (𝓞 L) L) ≫ z), ∀ e ∈ M.lat ⟨_, h'⟩, f e ∈ regAt ξ ⟨_, h'⟩ :=
    fun h' => GlobalTheory.T.regular_functional_specializes X G Ω ξ Li M f ⟨_, h⟩ ⟨_, h'⟩ hξ hLz hf
  obtain ⟨g, hg1, hg2⟩ := GlobalTheory.T.lie_model_localization_at_prime X G Ω ξ Li M L 𝔭 A z B MB f h hξ hf hfL
  obtain ⟨kA, hkA⟩ := val_of_mem h hκ
  obtain ⟨kA', hkA'⟩ := val_of_mem h hκi
  have hkk : kA * kA' = 1 := by
    have h1 := val_mul hkA hkA'
    rw [mul_inv_cancel₀ hκ0] at h1
    have h2 := val_natCast (ξ := ξ) (z := zA) h 1
    rw [Nat.cast_one, Nat.cast_one] at h2
    exact LieTangent.valAt_unique hξ h1 h2
  have hvk : v (algebraMap A L kA) = 1 := by
    have h1 : v (algebraMap A L kA) * v (algebraMap A L kA') = 1 := by
      rw [← map_mul, ← map_mul, hkk, map_one, map_one]
    have h2 := hA₁ kA
    have h3 := hA₁ kA'
    nlinarith [apply_nonneg v (algebraMap A L kA), apply_nonneg v (algebraMap A L kA')]
  have hkL : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) κ (algebraMap A L kA) := by
    rw [hzL]; exact LieTangent.valAt_base hξ (algebraMap A L) hkA
  have hτ := val_gen_ratio hw (hgen _) a he₀ c c₀ hcne hc₀
  set τ : L := ∏ k, (w ⟨k, c k⟩ / w ⟨k, c₀ k⟩) ^ a k with hτdef
  have gne : ∀ c' : (k : K) → J k, (∀ k, w ⟨k, c' k⟩ ≠ 0) → gen y a e₀ c' ≠ 0 := fun c' hc' =>
    mul_ne_zero (Finset.prod_ne_zero_iff.2 fun k _ =>
      zpow_ne_zero _ (hw.2 k (c' k) (isUnit_iff_ne_zero.2 (hc' k))).1) he₀
  set C : L := (m : L)⁻¹ * algebraMap A L kA * τ with hC
  have hvalm : ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (m : Ω)⁻¹ (m : L)⁻¹ := val_inv₀ (val_natCast (hgen _) m) hmL
  have key : ∀ (x' : B.carrier) (hx' : x' ∈ F₁) (e : Li) (vv : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G),
      e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e vv → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' vv →
      φ ⟨x', hx'⟩ = C * algebraMap A L (g x') := by
    intro x' hx' e vv hU hv' hl
    obtain ⟨h', he⟩ := (LieModel.exists_valAt_iff M _ e).1 ⟨vv, hv'⟩
    obtain ⟨u₀, hu₀⟩ := val_of_mem h' (hfL h' e he)
    have hg := hg1 x' e vv u₀ hv' hl hu₀
    obtain ⟨t, ht⟩ : ∃ t, IsCls b₀ i e t := by
      have hU' := hU
      rw [Flag.step_succ] at hU'
      obtain ⟨y', hy', z', hz', rfl⟩ := Submodule.mem_sup.1 hU'
      obtain ⟨t, rfl⟩ := Submodule.mem_span_singleton.1 hz'
      exact ⟨t, by simpa [IsCls] using hy'⟩
    have e1 := hcls e t hU ht
    have e2 : t / gen y a e₀ c₀ = (m : Ω)⁻¹ * f e * κ * (gen y a e₀ c / gen y a e₀ c₀) := by
      rw [hfe, ← _root_.mul_assoc, inv_mul_cancel₀ hm0, _root_.one_mul, ← e1, div_mul_div_cancel₀ (gne c hcne)]
    have e3 := hφ ⟨x', hx'⟩ e vv t _ hU hv' hl ht (e2 ▸ val_mul (val_mul (val_mul hvalm hu₀) hkL) hτ)
    rw [e3, hg, hC]
    ring
  let gL : B.carrier →ₗ[𝓞 L] L := (IsScalarTower.toAlgHom (𝓞 L) A L).toLinearMap ∘ₗ g
  have hgL : ∀ x, gL x = algebraMap A L (g x) := fun x => rfl
  let D : F₁ →ₗ[𝓞 L] L := φ - C • (gL ∘ₗ F₁.subtype)
  have hD : ∀ x : F₁, D x = φ x - C * algebraMap A L (g x) := fun x => rfl
  have hall : ∀ x : F₁, φ x = C * algebraMap A L (g x) := by
    rintro ⟨x, hx⟩
    obtain ⟨a₁, ha₁, hsp⟩ := (hF₁ x).1 hx
    have hind : ∀ y' ∈ Submodule.span (𝓞 L) {x' | ∃ e ∈ flagStep Ω b₀ (i + 1), ∃ v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G,
        M.ValAt (spMap (algebraMap (𝓞 L) L) ≫ z) e v ∧ MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) x' v},
        ∃ hy : y' ∈ F₁, D ⟨y', hy⟩ = 0 := by
      intro y' hy'
      induction hy' using Submodule.span_induction with
      | mem x' hx' =>
        obtain ⟨e, hU, vv, hv', hl⟩ := hx'
        have hm' : x' ∈ F₁ := (hF₁ x').2 ⟨1, one_ne_zero, by
          rw [one_smul]; exact Submodule.subset_span ⟨e, hU, vv, hv', hl⟩⟩
        exact ⟨hm', by rw [hD, key x' hm' e vv hU hv' hl, sub_self]⟩
      | zero => exact ⟨zero_mem _, map_zero D⟩
      | add y₁ y₂ _ _ i₁ i₂ =>
        obtain ⟨h₁, e₁⟩ := i₁
        obtain ⟨h₂, e₂⟩ := i₂
        refine ⟨add_mem h₁ h₂, ?_⟩
        have : D (⟨y₁, h₁⟩ + ⟨y₂, h₂⟩) = 0 := by rw [map_add, e₁, e₂, add_zero]
        exact this
      | smul s y _ i₁ =>
        obtain ⟨h₁, e₁⟩ := i₁
        refine ⟨F₁.smul_mem s h₁, ?_⟩
        have : D (s • ⟨y, h₁⟩) = 0 := by rw [map_smul, e₁, smul_zero]
        exact this
    obtain ⟨hy, e⟩ := hind _ hsp
    have e' : D (a₁ • ⟨x, hx⟩) = 0 := e
    rw [map_smul] at e'
    have e'' := (smul_eq_zero.1 e').resolve_left ha₁
    rw [hD] at e''
    exact sub_eq_zero.1 e''
  have hsup : ∀ k, (⨆ i, v (w ⟨k, i⟩)) = v (w ⟨k, c k⟩) := fun k => by
    haveI : Nonempty (J k) := ⟨c k⟩
    exact le_antisymm (ciSup_le (hmax k)) (le_ciSup (f := fun i => v (w ⟨k, i⟩)) (Set.finite_range _).bddAbove (c k))
  have hvC : v C = (v (m : L))⁻¹ * locRatio a w c₀ v := by
    have : v τ = locRatio a w c₀ v := by
      rw [hτdef, locRatio, map_prod]
      exact Finset.prod_congr rfl fun k _ => by rw [map_zpow₀, map_div₀, hsup]
    rw [hC, map_mul, map_mul, map_inv₀, hvk, this, _root_.mul_one]
  have hvm : v (m : L) ≠ 0 := (FinitePlace.pos_iff.2 hmL).ne'
  refine ⟨fun x => ?_, ?_⟩
  · rw [hall, map_mul, hvC]
    exact mul_le_of_le_one_right (hvC ▸ apply_nonneg v C) (hA₁ _)
  · have hU : (m : Ω) • b i ∈ flagStep Ω b₀ (i + 1) := by
      rw [← hfl]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, by simp, rfl⟩)
    have hfm : f ((m : Ω) • b i) = (m : Ω) * (m : Ω) := by
      rw [hfe, map_smul, hdual i i]; simp
    have hval : ValAt ξ zA (f ((m : Ω) • b i)) ((m : A) * (m : A)) := by
      rw [hfm]; exact val_mul (val_natCast h m) (val_natCast h m)
    obtain ⟨d, n, x, x', vv, hd, hn, hgx, hvv, hl, hnx⟩ := hg2 _ _ (hmb i) hval
    have hxF : x ∈ F₁ := (hF₁ x).2 ⟨(n : 𝓞 L), Nat.cast_ne_zero.2 hn, by
      rw [hnx]
      exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, Submodule.smul_mem _ _ hU, vv, hvv, hl⟩)⟩
    refine ⟨⟨x, hxF⟩, le_of_eq ?_⟩
    have e4 : algebraMap A L (algebraMap (𝓞 L) A d * ((m : A) * (m : A))) =
        algebraMap (𝓞 L) L d * ((m : L) * (m : L)) := by
      simp [IsScalarTower.algebraMap_apply (𝓞 L) A L]
    rw [hall, map_mul, hvC, hgx, e4, map_mul, map_mul, hv d hd]
    field_simp

end GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

namespace GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal

/- English proof (translation)
Rewrite using `[← FinitePlace.norm_embedding_eq]`. Conclude with `(FinitePlace.norm_eq_one_iff_notMem L _ d).2 hd`.
-/
theorem place_one (L : Type) [Field L] [NumberField L] (v : FinitePlace L) (d : 𝓞 L)
    (hd : d ∉ (FinitePlace.maximalIdeal v).asIdeal) : v (algebraMap (𝓞 L) L d) = 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact (FinitePlace.norm_eq_one_iff_notMem L _ d).2 hd

/- English proof (translation)
Rewrite using `[← FinitePlace.norm_embedding_eq]`. Conclude with `FinitePlace.norm_le_one L _ d`.
-/
theorem place_le (L : Type) [Field L] [NumberField L] (v : FinitePlace L) (d : 𝓞 L) :
    v (algebraMap (𝓞 L) L d) ≤ 1 := by
  rw [← FinitePlace.norm_embedding_eq]
  exact FinitePlace.norm_le_one L _ d

/- English proof (translation)
Establish `hs : ∀ r : A, ∃ (a s : 𝓞 L), s ∉ (FinitePlace.maximalIdeal v).asIdeal ∧ r * algebraMap (𝓞 L) A s = algebraMap (𝓞 L) A a` using `fun r => by`. Take `⟨⟨a, s⟩, e⟩` from `IsLocalization.surj (FinitePlace.maximalIdeal v).asIdeal.primeCompl r`. Conclude with `⟨a, s, s.2, e⟩`. Establish `hv : ∀ (r : A) (a s : 𝓞 L), s ∉ (FinitePlace.maximalIdeal v).asIdeal → r * algebraMap (𝓞 L) A s = algebraMap (𝓞 L) A a → v (algebraMap A L r) = v (algebraMap (𝓞 L) L a)` using `fun r a s hs' e => by`. Establish `e1` using `congrArg (fun t => v (algebraMap A L t)) e`.

Simplify using `only [map_mul, ← IsScalarTower.algebraMap_apply, place_one L v s hs', _root_.mul_one] at e1`. Conclude with `e1`. Use `⟨fun r => ?_, fun r hr => ?_⟩` and prove the remaining obligations. Take `⟨a, s, h1, h2⟩` from `hs r`. Rewrite using `[hv r a s h1 h2]`.

Conclude with `place_le L v a`. Take `⟨a, s, h1, h2⟩` from `hs r`. Rewrite `hr` using `[hv r a s h1 h2]`. Establish `ha : a ∉ (FinitePlace.maximalIdeal v).asIdeal` using `fun h => by`. Use `(FinitePlace.norm_lt_one_iff_mem L (FinitePlace.maximalIdeal v) a).2 h` as an intermediate fact.

Rewrite `this` using `[FinitePlace.norm_embedding_eq, hr]`. Conclude with `lt_irrefl _ this`. Establish `hu : IsUnit (algebraMap (𝓞 L) A a)` using `IsLocalization.map_units A (⟨a, ha⟩ : (FinitePlace.maximalIdeal v).asIdeal.primeCompl)`. Rewrite `hu` using `[← h2]`. Conclude with `isUnit_of_mul_isUnit_left hu`.
-/
theorem place_local (L : Type) [Field L] [NumberField L] (v : FinitePlace L) (A : Type) [CommRing A]
    [Algebra (𝓞 L) A] [IsLocalization.AtPrime A (FinitePlace.maximalIdeal v).asIdeal] [Algebra A L]
    [IsScalarTower (𝓞 L) A L] :
    (∀ r : A, v (algebraMap A L r) ≤ 1) ∧ ∀ r : A, v (algebraMap A L r) = 1 → IsUnit r := by
  have hs : ∀ r : A, ∃ (a s : 𝓞 L), s ∉ (FinitePlace.maximalIdeal v).asIdeal ∧
      r * algebraMap (𝓞 L) A s = algebraMap (𝓞 L) A a := fun r => by
    obtain ⟨⟨a, s⟩, e⟩ := IsLocalization.surj (FinitePlace.maximalIdeal v).asIdeal.primeCompl r
    exact ⟨a, s, s.2, e⟩
  have hv : ∀ (r : A) (a s : 𝓞 L), s ∉ (FinitePlace.maximalIdeal v).asIdeal →
      r * algebraMap (𝓞 L) A s = algebraMap (𝓞 L) A a → v (algebraMap A L r) = v (algebraMap (𝓞 L) L a) :=
    fun r a s hs' e => by
      have e1 := congrArg (fun t => v (algebraMap A L t)) e
      simp only [map_mul, ← IsScalarTower.algebraMap_apply, place_one L v s hs', _root_.mul_one] at e1
      exact e1
  refine ⟨fun r => ?_, fun r hr => ?_⟩
  · obtain ⟨a, s, h1, h2⟩ := hs r
    rw [hv r a s h1 h2]
    exact place_le L v a
  · obtain ⟨a, s, h1, h2⟩ := hs r
    rw [hv r a s h1 h2] at hr
    have ha : a ∉ (FinitePlace.maximalIdeal v).asIdeal := fun h => by
      have := (FinitePlace.norm_lt_one_iff_mem L (FinitePlace.maximalIdeal v) a).2 h
      rw [FinitePlace.norm_embedding_eq, hr] at this
      exact lt_irrefl _ this
    have hu : IsUnit (algebraMap (𝓞 L) A a) :=
      IsLocalization.map_units A (⟨a, ha⟩ : (FinitePlace.maximalIdeal v).asIdeal.primeCompl)
    rw [← h2] at hu
    exact isUnit_of_mul_isUnit_left hu

/- English proof (translation)
Introduce `X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ hchar hgen hcoord hm hb₀ hS hdeg L _ _ w z hw B MB F₀ F₁ hF₀ hF₁ c₀ hc₀ φ hφ v`. Establish `hle : (FinitePlace.maximalIdeal v).asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 L)` using `Ideal.primeCompl_le_nonZeroDivisors _`. Set `A` to `Localization.subalgebra.ofField L _ hle`. Use `haveI : IsLocalization.AtPrime A (FinitePlace.maximalIdeal v).asIdeal := inferInstanceAs (IsLocalization (FinitePlace.maximalIdeal v).asIdeal.primeCompl A)`. Use `haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (FinitePlace.maximalIdeal v).asIdeal`.

Take `⟨h1, h2⟩` from `place_local L v A`. Conclude with `core X Ω ξ K J y G Li M V r b₀ m i a e₀ hchar hgen hcoord hm hb₀ hS hdeg L w z hw B MB F₁ hF₁ c₀ hc₀ φ hφ v (FinitePlace.maximalIdeal v).asIdeal A (place_one L v) h1 h2`.
-/
theorem coord_size : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Sp Ω ⟶ X) (K : Type) [Fintype K] (J : K → Type)
    [∀ k, Fintype (J k)] (y : (Σ k, J k) → Ω) (G : Over X) [GrpObj G] [IsCommMonObj G] [Smooth G.hom]
    (Li : Type) [AddCommGroup Li] [Module Ω Li] (M : LieModel G ξ Li) (V : Lat ξ Li) (r : ℕ) (b₀ : Fin r → Li)
    (m : ℕ) (i : Fin r) (a : K → ℤ) (e₀ : Ω),
    CharZero Ω → (∀ q : X, genPt ξ ⤳ q) → CoordTie ℤ ξ (fun c' : (k : K) → J k => ∏ k, y ⟨k, c' k⟩) → 0 < m →
    LinearIndependent Ω b₀ → Sandwich M V b₀ m → (V.gr b₀ i).IsDegOn Set.univ y a e₀ →
    ∀ (L : Type) [Field L] [NumberField L] (w : (Σ k, J k) → L) (z : Sp (𝓞 L) ⟶ X),
      CoordsAt ξ y (spMap (algebraMap (𝓞 L) L) ≫ z) w → ∀ (B : HermitianBundle.{0} L) (MB : LieModel G z B.carrier)
      (F₀ F₁ : Submodule (𝓞 L) B.carrier), IsSubFibre M (flagStep Ω b₀ i) z MB F₀ →
      IsSubFibre M (flagStep Ω b₀ (i + 1)) z MB F₁ → ∀ c₀ : (k : K) → J k, (∀ k, w ⟨k, c₀ k⟩ ≠ 0) →
      ∀ φ : F₁ →ₗ[𝓞 L] L, (∀ (x : F₁) (e : Li) (v : epsAt (spMap (algebraMap (𝓞 L) L) ≫ z) ⟶ G) (t : Ω) (u : L),
          e ∈ flagStep Ω b₀ (i + 1) → M.ValAt _ e v → MB.Lifts (algebraMap (𝓞 L) L) (𝟙 G.left) (x : B.carrier) v →
          IsCls b₀ i e t → ValAt ξ (spMap (algebraMap (𝓞 L) L) ≫ z) (t / gen y a e₀ c₀) u → φ x = u) →
        ∀ v : FinitePlace L, (∀ x, v (φ x) ≤ (v (m : L))⁻¹ * locRatio a w c₀ v) ∧
          ∃ x, v (m : L) * locRatio a w c₀ v ≤ v (φ x) := by
  intro X Ω _ ξ K _ J _ y G _ _ _ Li _ _ M V r b₀ m i a e₀ hchar hgen hcoord hm hb₀ hS hdeg L _ _ w z hw B MB F₀ F₁ hF₀ hF₁
    c₀ hc₀ φ hφ v
  have hle : (FinitePlace.maximalIdeal v).asIdeal.primeCompl ≤ nonZeroDivisors (𝓞 L) :=
    Ideal.primeCompl_le_nonZeroDivisors _
  let A := Localization.subalgebra.ofField L _ hle
  haveI : IsLocalization.AtPrime A (FinitePlace.maximalIdeal v).asIdeal :=
    inferInstanceAs (IsLocalization (FinitePlace.maximalIdeal v).asIdeal.primeCompl A)
  haveI : IsLocalRing A := IsLocalization.AtPrime.isLocalRing A (FinitePlace.maximalIdeal v).asIdeal
  obtain ⟨h1, h2⟩ := place_local L v A
  exact core X Ω ξ K J y G Li M V r b₀ m i a e₀ hchar hgen hcoord hm hb₀ hS hdeg L w z hw B MB F₁ hF₁ c₀ hc₀ φ hφ v
    (FinitePlace.maximalIdeal v).asIdeal A (place_one L v) h1 h2

end GlobalTheory.CompanionTheory.Ar.RootHt.FinLocal
