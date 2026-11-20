import Mathlib
import ReciprocityTheory.ReductiveGroups.ArithmeticGeometry.BirationalGeometry.ToroidalCompactification.UniformisationConclusion
import Development.AbelianVarietyTheory.Definitions.AbelianSchemeLaws.FirstCohomologyVanishesSpecOfIsLocalRing
import Development.AbelianVarietyTheory.Definitions.Degenerations.OfDerivationFnOn
import Development.AbelianVarietyTheory.Definitions.Degenerations.PlOrdSomeOfAssociated
import Development.AbelianVarietyTheory.Statements.SemistableTorsion.SemistableFin
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsFrobGBaseChange
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.EqOneOfPowOfClosedPoint
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.FrobeniusOnTorsionStatement
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.SS
noncomputable section
namespace GlobalTheory.SS.SpecialCount

/- English proof (translation)
Establish `inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y`. Introduce `n x y hx hy h`. Use `hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)` as an intermediate fact. Conclude with `mul_inv_eq_one.1 this`. Establish `memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V`.

Introduce `x`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨y, hy, rfl⟩`. Conclude with `⟨y.2, hy⟩`. Introduce and unpack `⟨h, hx⟩`.

Conclude with `⟨⟨x, h⟩, hx, rfl⟩`. Use `⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩` and prove the remaining obligations. Use `hfin n` as an intermediate fact. Use `Nat.card_le_card_of_injective (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_` and prove the remaining obligations. Conclude with `Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))`.

Use `hfin n` as an intermediate fact. Establish `: Finite {x : V // x ^ l ^ n = 1}` using `Finite.of_injective (β := {x : N // x ^ l ^ n = 1}) (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h => Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))`. Establish `tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1}, (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1` using `fun x => Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)`. Use `Nat.card_le_card_of_injective (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by` and prove the remaining obligations. Express the relevant statement in the definitionally equal form `r _ ^ l ^ n = 1`.

Rewrite using `[← map_pow, tor x, map_one])⟩) fun x y h => ?_`. Use `inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)` as an intermediate fact. Conclude with `Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))`. Take `⟨h, hv⟩` from `(memU x).1 hx`. Take `⟨h', e'⟩` from `hφ 1 ⟨x, h⟩`.

Use `inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by` as an intermediate fact. Express the relevant statement in the definitionally equal form `Φ x ^ l ^ n = 1`. Rewrite using `[← map_pow, hn, map_one])) (Subtype.ext (by`. Express the relevant statement in the definitionally equal form `(x ^ e) ^ l ^ n = 1`. Rewrite using `[← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])`.

Conclude with `congrArg Subtype.val this`. Use `choose h e' using fun j => hφ j ⟨x, hx⟩`. Establish `hr` using `hQ (r ⟨x, hx⟩) n (by`. Rewrite using `[← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])`. Use `⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩` and prove the remaining obligations.

Express the relevant statement in the definitionally equal form `r _ ∈ V`. Rewrite using `[map_list_prod, List.map_map]`. Establish `: (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j`. Use function extensionality and compare the values at `j`. Simplify using `only [Function.comp, map_zpow, e']`.

Rewrite using `[this]`. Conclude with `hr`. Rewrite using `[map_list_prod, List.map_map]`. Both sides reduce to the same expression.
-/
theorem transfer {M N : Type} [CommGroup M] [Group N] (H : Subgroup M) (r : H →* N) (Φ : MulAut M)
    (φ : ℕ → N → N) (hφ : ∀ (j : ℕ) (x : H), ∃ h : Φ^[j] x ∈ H, r ⟨_, h⟩ = φ j (r x)) (l e : ℕ)
    (hinj : ∀ n (x : H), x ^ l ^ n = 1 → r x = 1 → x = 1) (V : Subgroup N)
    (hV : ∀ x ∈ V, φ 1 x = x ^ e) (hfin : ∀ n, Finite {x : N // x ^ l ^ n = 1}) (Q : Polynomial ℤ)
    (hQ : ∀ (x : N) n, x ^ l ^ n = 1 →
      ((List.range (Q.natDegree + 1)).map fun j => φ j x ^ Q.coeff j).prod ∈ V) :
    ∃ U : Subgroup M,
      (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ Nat.card {x : N // x ^ l ^ n = 1} ∧
        Nat.card {x : U // x ^ l ^ n = 1} ≤ Nat.card {x : V // x ^ l ^ n = 1}) ∧
      (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → Φ x = x ^ e) ∧
      ∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), (Φ^[j] x) ^ Q.coeff j ∈ U := by
  have inj : ∀ n (x y : H), x ^ l ^ n = 1 → y ^ l ^ n = 1 → r x = r y → x = y := by
    intro n x y hx hy h
    have := hinj n (x * y⁻¹) (by rw [mul_pow, inv_pow, hx, hy]; simp) (by rw [map_mul, map_inv, h]; simp)
    exact mul_inv_eq_one.1 this
  have memU : ∀ x : M, x ∈ (V.comap r).map H.subtype ↔ ∃ h : x ∈ H, r ⟨x, h⟩ ∈ V := by
    intro x
    constructor
    · rintro ⟨y, hy, rfl⟩
      exact ⟨y.2, hy⟩
    · rintro ⟨h, hx⟩
      exact ⟨⟨x, h⟩, hx, rfl⟩
  refine ⟨(V.comap r).map H.subtype, fun n => ⟨?_, ?_⟩, fun n x hx hn => ?_, fun n x hx hn => ?_⟩
  · have := hfin n
    refine Nat.card_le_card_of_injective
      (fun x => ⟨r x.1, by rw [← map_pow, x.2, map_one]⟩) fun x y h => ?_
    exact Subtype.ext (inj n _ _ x.2 y.2 (congrArg Subtype.val h))
  · have := hfin n
    have : Finite {x : V // x ^ l ^ n = 1} :=
      Finite.of_injective (β := {x : N // x ^ l ^ n = 1})
        (fun x => ⟨x.1.1, congrArg Subtype.val x.2⟩) fun x y h =>
          Subtype.ext (Subtype.ext (by exact congrArg (fun z : {x : N // x ^ l ^ n = 1} => z.1) h))
    have tor : ∀ x : {x : (V.comap r).map H.subtype // x ^ l ^ n = 1},
        (⟨x.1.1, ((memU _).1 x.1.2).1⟩ : H) ^ l ^ n = 1 := fun x =>
      Subtype.ext (by exact congrArg (fun z : (V.comap r).map H.subtype => z.1) x.2)
    refine Nat.card_le_card_of_injective
      (fun x => ⟨⟨r ⟨x.1.1, ((memU _).1 x.1.2).1⟩, ((memU _).1 x.1.2).2⟩, Subtype.ext (by
        change r _ ^ l ^ n = 1
        rw [← map_pow, tor x, map_one])⟩) fun x y h => ?_
    have := inj n _ _ (tor x) (tor y) (congrArg (fun z => z.1.1) h)
    exact Subtype.ext (Subtype.ext (by exact congrArg (fun z : H => z.1) this))
  · obtain ⟨h, hv⟩ := (memU x).1 hx
    obtain ⟨h', e'⟩ := hφ 1 ⟨x, h⟩
    have := inj n ⟨_, h'⟩ (⟨x, h⟩ ^ e) (Subtype.ext (by
        change Φ x ^ l ^ n = 1
        rw [← map_pow, hn, map_one])) (Subtype.ext (by
        change (x ^ e) ^ l ^ n = 1
        rw [← pow_mul, mul_comm, pow_mul, hn, one_pow])) (by rw [e', hV _ hv, map_pow])
    exact congrArg Subtype.val this
  · choose h e' using fun j => hφ j ⟨x, hx⟩
    have hr := hQ (r ⟨x, hx⟩) n (by
      rw [← map_pow, show (⟨x, hx⟩ : H) ^ l ^ n = 1 from Subtype.ext hn, map_one])
    refine ⟨((List.range (Q.natDegree + 1)).map fun j => (⟨_, h j⟩ : H) ^ Q.coeff j).prod, ?_, ?_⟩
    · change r _ ∈ V
      rw [map_list_prod, List.map_map]
      have : (r ∘ fun j => (⟨_, h j⟩ : H) ^ Q.coeff j) = fun j => φ j (r ⟨x, hx⟩) ^ Q.coeff j := by
        funext j
        simp only [Function.comp, map_zpow, e']
      rw [this]
      exact hr
    · rw [map_list_prod, List.map_map]
      rfl

/- English proof (translation)
Use `choose f hf hf' using h`. Use `⟨{ toFun := f map_one' := hi (by simp [hf]) map_mul' := fun x y => hi (by simp [hf]) map_zero' := hi (by simp [hf]) map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩` and prove the remaining obligations. Use `(IsLocalRing.residue_eq_zero_iff _).2 (hf' x)` as an intermediate fact. Rewrite `this` using `[map_sub, map_pow, sub_eq_zero]`. Conclude with `this`.
-/
theorem exists_restrict {R Ω : Type} [CommRing R] [IsLocalRing R] [Field Ω] [Algebra R Ω]
    (hi : Function.Injective (algebraMap R Ω)) (q : ℕ) (ψ : Ω →+* Ω)
    (h : ∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ q ∈ IsLocalRing.maximalIdeal R) :
    ∃ σ : R →+* R, (∀ x, algebraMap R Ω (σ x) = ψ (algebraMap R Ω x)) ∧
      ∀ x, IsLocalRing.residue R (σ x) = IsLocalRing.residue R x ^ q := by
  choose f hf hf' using h
  refine ⟨{ toFun := f
            map_one' := hi (by simp [hf])
            map_mul' := fun x y => hi (by simp [hf])
            map_zero' := hi (by simp [hf])
            map_add' := fun x y => hi (by simp [hf]) }, hf, fun x => ?_⟩
  have := (IsLocalRing.residue_eq_zero_iff _).2 (hf' x)
  rw [map_sub, map_pow, sub_eq_zero] at this
  exact this

/- English proof (translation)
The claim follows from `(Spec.map_comp _ _).symm`.
-/
theorem sp_comp {A B C : Type} [CommRing A] [CommRing B] [CommRing C] (f : A →+* B) (g : B →+* C) :
    spMap g ≫ spMap f = spMap (g.comp f) := (Spec.map_comp _ _).symm

/- English proof (translation)
Take `⟨h1, h2, h3, h4, h5⟩` from `h`. Use `⟨inferInstance, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Use `show Smooth (pullback.snd _ _)`. Use `infer_instance`. Use `show IsSeparated (pullback.snd _ _)`.

Use `infer_instance`. Use `show QuasiCompact (pullback.snd _ _)`. Use `infer_instance`. Use `show GeometricallyConnected (pullback.snd _ _)`. Use `infer_instance`.
-/
theorem smConn_pullback {S T : Scheme.{0}} (f : T ⟶ S) (G : Over S) [GrpObj G] (h : SmConn G) :
    SmConn ((Over.pullback f).obj G) := by
  obtain ⟨h1, h2, h3, h4, h5⟩ := h
  refine ⟨inferInstance, ?_, ?_, ?_, ?_⟩
  · show Smooth (pullback.snd _ _); infer_instance
  · show IsSeparated (pullback.snd _ _); infer_instance
  · show QuasiCompact (pullback.snd _ _); infer_instance
  · show GeometricallyConnected (pullback.snd _ _); infer_instance

end GlobalTheory.SS.SpecialCount

namespace GlobalTheory.SS
open SpecialCount

/- English proof (translation)
Introduce `W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ`. Use `haveI : Fact p.Prime := ⟨hp⟩`. Take `⟨σ, hσ, hσ'⟩` from `exists_restrict hi (p ^ r) ψ hψR`. Establish `hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w` using `fun w => hi (by`. Rewrite using `[hσ, ← IsScalarTower.algebraMap_apply, hψW])`.

Take `⟨F, hF, hFx⟩` from `GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R) ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by`. Rewrite using `[RingHom.comp_apply, ← hσ', hσW]) hfin G hG`. Establish `hlp : l ≠ p`. Introduce and unpack `rfl`. Use `hlu.map (IsLocalRing.residue R)` as an intermediate fact.

Rewrite `this` using `[map_natCast, CharP.cast_eq_zero]`. Conclude with `not_isUnit_zero this`. Establish `hq : 2 ≤ p ^ r` using `hp.two_le.trans (Nat.le_self_pow (by omega) p)`. Take `⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩` from `GlobalTheory.T.frobenius_on_torsion_alt _ p l hl hlp _ (smConn_pullback _ G hG) g (by show SmoothOfRelativeDimension g (pullback.snd _ _)`. Conclude with `(smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF`.

Take `⟨H₀, red, hH, hred, hinj⟩` from `GlobalTheory.RedPts.exists_reduction W R Ω hi G hG`. Set `H : Subgroup M` to `H₀.comap θ.toMonoidHom`. Set `κ : H →* H₀` to `(θ.toMonoidHom.subgroupComap H₀)`. Establish `step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F)`. Introduce `x`.

Take `⟨s, hs, hs'⟩` from `(hH _).1 x.2`. Establish `a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R)`. Rewrite using `[Category.assoc, hs, sp_comp]`. Use `congr 1`. Conclude with `RingHom.ext hσW`.

Establish `a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left`. Rewrite using `[hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from RingHom.ext hσ, ← sp_comp, Category.assoc, hs']`. Both sides reduce to the same expression. Establish `hx : Ψ x ∈ H` using `(hH _).2 ⟨_, a1, a2⟩`. Use `⟨hx, ?_⟩` and prove the remaining obligations.

Establish `b1` using `hred (κ ⟨_, hx⟩) _ a1 a2`. Establish `b2` using `hred (κ x) s hs hs'`. Establish `b3` using `hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)`. Use `ext1`. Apply `pullback.hom_ext` to reduce the goal to its premises.

Use `b1.trans (Eq.trans ?_ b3.symm) erw [b2]` and prove the remaining obligations. Rewrite using `[← Category.assoc, ← Category.assoc, sp_comp, sp_comp]`. Use `congr 2`. Conclude with `RingHom.ext hσ'`. Conclude with `(Over.w _).trans (Over.w _).symm`.

Establish `iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F ^ n)`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩`. Consider the case `succ n ih`.

Introduce `x`. Take `⟨h, e⟩` from `step x`. Take `⟨h', e'⟩` from `ih ⟨_, h⟩`. Rewrite using `[pow_succ, pow_succ]`. Use `⟨h', e'.trans ?_⟩` and prove the remaining obligations.

Rewrite using `[e, Category.assoc]`. Both sides reduce to the same expression. Take `⟨U, hU1, hU2, hU3⟩` from `transfer H (red.comp κ) (Ψ ^ m) (fun j x => x ≫ (show _ ⟶ _ from (F ^ m) ^ j)) (fun j x => by`. Establish `e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x`. Rewrite using `[pow_mul]`.

Generalize the expression as in `(x : M) = y`. Proceed by induction on `j generalizing y with`. Consider the case `zero => rfl`. Consider the case `succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]`. Both sides reduce to the same expression.

Rewrite using `[e, ← pow_mul]`. Conclude with `iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by`. Use `hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n) (by rw [← map_pow, hx, map_one]) h` as an intermediate fact. Conclude with `Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V`. Use the proof step `(fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ`.

Use `⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1, (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩` and prove the remaining obligations. Rewrite using `[Nat.cast_pow]`. Conclude with `hroot β hβ`.
-/
theorem frobenius_on_integral_torsion : ∀ (W R Ω : Type) [CommRing W] [CommRing R] [IsDomain R] [IsLocalRing R] [Field Ω] [Algebra W R] [Algebra R Ω] [Algebra W Ω] [IsScalarTower W R Ω], Function.Injective (algebraMap R Ω) → IsAlgClosed (IsLocalRing.ResidueField R) → ∀ (p r l : ℕ), p.Prime → CharP (IsLocalRing.ResidueField R) p → 1 ≤ r → l.Prime → IsUnit (l : R) → (∀ c : IsLocalRing.ResidueField R, ∃ m, 1 ≤ m ∧ c ^ ((p ^ r) ^ m) = c) → ∀ ψ : Ω →+* Ω, (∀ w : W, ψ (algebraMap W Ω w) = algebraMap W Ω w) → (∀ x : R, ∃ y : R, algebraMap R Ω y = ψ (algebraMap R Ω x) ∧ y - x ^ (p ^ r) ∈ IsLocalRing.maximalIdeal R) → ∀ (G : Over (Sp W)) [GrpObj G], SmConn G → ∀ g : ℕ, SmoothOfRelativeDimension g G.hom → ∀ L : LB ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G).left, AmpleCub ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G) L → ∀ (M : Type) [CommGroup M] (θ : M ≃* (Over.mk (spMap (algebraMap W Ω)) ⟶ G)) (Ψ : MulAut M), (∀ x, (θ (Ψ x)).left = spMap ψ ≫ (θ x).left) → ∃ (t a m C : ℕ) (Q : Polynomial ℤ) (H U : Subgroup M), 1 ≤ m ∧ (∀ x, x ∈ H ↔ ∃ s : Sp R ⟶ G.left, s ≫ G.hom = spMap (algebraMap W R) ∧ spMap (algebraMap R Ω) ≫ s = (θ x).left) ∧ (∀ n, Nat.card {x : H // x ^ l ^ n = 1} ≤ C * l ^ (n * (t + 2 * a)) ∧ Nat.card {x : U // x ^ l ^ n = 1} ≤ C * l ^ (n * t)) ∧ (∀ β : ℂ, Polynomial.aeval β Q = 0 → ‖β‖ < (((p ^ r) ^ m : ℕ) : ℝ)) ∧ (∀ n, ∀ x ∈ U, x ^ l ^ n = 1 → (Ψ ^ m) x = x ^ ((p ^ r) ^ m)) ∧ (∀ n, ∀ x ∈ H, x ^ l ^ n = 1 → ∏ j ∈ Finset.range (Q.natDegree + 1), ((Ψ ^ m : MulAut M)^[j] x) ^ Q.coeff j ∈ U) ∧ (g ≤ t + a → Nonempty (TorusExtension ((Over.pullback (spMap ((IsLocalRing.residue R).comp (algebraMap W R)))).obj G))) := by
  intro W R Ω _ _ _ _ _ _ _ _ _ hi hac p r l hp hch hr hl hlu hfin ψ hψW hψR G _ hG g hg L hL M _ θ Ψ hΨ
  haveI : Fact p.Prime := ⟨hp⟩
  obtain ⟨σ, hσ, hσ'⟩ := exists_restrict hi (p ^ r) ψ hψR
  have hσW : ∀ w, σ (algebraMap W R w) = algebraMap W R w := fun w => hi (by
    rw [hσ, ← IsScalarTower.algebraMap_apply, hψW])
  obtain ⟨F, hF, hFx⟩ := GlobalTheory.SS.exists_frobG_baseChange W (IsLocalRing.ResidueField R)
    ((IsLocalRing.residue R).comp (algebraMap W R)) p r hr (fun w => by
      rw [RingHom.comp_apply, ← hσ', hσW]) hfin G hG
  have hlp : l ≠ p := by
    rintro rfl
    have := hlu.map (IsLocalRing.residue R)
    rw [map_natCast, CharP.cast_eq_zero] at this
    exact not_isUnit_zero this
  have hq : 2 ≤ p ^ r := hp.two_le.trans (Nat.le_self_pow (by omega) p)
  obtain ⟨t, a, m, C, Q, V, hm, hroot, hV, hcount, hQ, hT⟩ := GlobalTheory.T.frobenius_on_torsion_alt _ p l hl hlp _
    (smConn_pullback _ G hG) g (by
      show SmoothOfRelativeDimension g (pullback.snd _ _)
      exact (smoothOfRelativeDimension_isStableUnderBaseChange g).of_isPullback
        (IsPullback.of_hasPullback _ _) hg) L hL F (p ^ r) hq hF
  obtain ⟨H₀, red, hH, hred, hinj⟩ := GlobalTheory.RedPts.exists_reduction W R Ω hi G hG
  let H : Subgroup M := H₀.comap θ.toMonoidHom
  let κ : H →* H₀ := (θ.toMonoidHom.subgroupComap H₀)
  have step : ∀ x : H, ∃ h : Ψ x ∈ H, red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F) := by
    intro x
    obtain ⟨s, hs, hs'⟩ := (hH _).1 x.2
    have a1 : (spMap σ ≫ s) ≫ G.hom = spMap (algebraMap W R) := by
      rw [Category.assoc, hs, sp_comp]
      congr 1
      exact RingHom.ext hσW
    have a2 : spMap (algebraMap R Ω) ≫ spMap σ ≫ s = (θ (Ψ x)).left := by
      rw [hΨ, ← Category.assoc, sp_comp, show (algebraMap R Ω).comp σ = ψ.comp (algebraMap R Ω) from
        RingHom.ext hσ, ← sp_comp, Category.assoc, hs']
      rfl
    have hx : Ψ x ∈ H := (hH _).2 ⟨_, a1, a2⟩
    refine ⟨hx, ?_⟩
    have b1 := hred (κ ⟨_, hx⟩) _ a1 a2
    have b2 := hred (κ x) s hs hs'
    have b3 := hFx (red (κ x)) (iterateFrobenius _ p r) (fun c => rfl)
    ext1
    apply pullback.hom_ext
    · refine b1.trans (Eq.trans ?_ b3.symm)
      erw [b2]
      rw [← Category.assoc, ← Category.assoc, sp_comp, sp_comp]
      congr 2
      exact RingHom.ext hσ'
    · exact (Over.w _).trans (Over.w _).symm
  have iter : ∀ (n : ℕ) (x : H), ∃ h : (Ψ ^ n) x ∈ H,
      red (κ ⟨_, h⟩) = red (κ x) ≫ (show _ ⟶ _ from F ^ n) := by
    intro n
    induction n with
    | zero => exact fun x => ⟨x.2, (Category.comp_id _).symm⟩
    | succ n ih =>
      intro x
      obtain ⟨h, e⟩ := step x
      obtain ⟨h', e'⟩ := ih ⟨_, h⟩
      rw [pow_succ, pow_succ]
      refine ⟨h', e'.trans ?_⟩
      rw [e, Category.assoc]
      rfl
  obtain ⟨U, hU1, hU2, hU3⟩ := transfer H (red.comp κ) (Ψ ^ m)
    (fun j x => x ≫ (show _ ⟶ _ from (F ^ m) ^ j)) (fun j x => by
      have e : (Ψ ^ m : MulAut M)^[j] x = (Ψ ^ (m * j)) x := by
        rw [pow_mul]
        generalize (x : M) = y
        induction j generalizing y with
        | zero => rfl
        | succ j ih => rw [pow_succ, Function.iterate_succ_apply, ih]; rfl
      rw [e, ← pow_mul]
      exact iter (m * j) x) l ((p ^ r) ^ m) (fun n x hx h => by
      have := hinj (l ^ n) (κ x) (by rw [Nat.cast_pow]; exact hlu.pow n)
        (by rw [← map_pow, hx, map_one]) h
      exact Subtype.ext (θ.injective ((congrArg Subtype.val this).trans (map_one θ).symm))) V
    (fun x hx => by rw [pow_one]; exact hV x hx) (fun n => (hcount n).1) Q hQ
  refine ⟨t, a, m, C, Q, H, U, hm, fun x => hH _, fun n => ⟨(hU1 n).1.trans (hcount n).2.1,
    (hU1 n).2.trans (hcount n).2.2⟩, fun β hβ => ?_, hU2, hU3, hT⟩
  rw [Nat.cast_pow]
  exact hroot β hβ

end GlobalTheory.SS
end
