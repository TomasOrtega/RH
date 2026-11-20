import Mathlib
import Development.AbelianVarietyTheory.Definitions.Divisors.LamRange
import ReciprocityTheory.AnalyticForms.RegularLocalRings.FinalTheorems
import Development.AbelianVarietyTheory.Proofs.DivisorProofs.ExistsThetaSystemRealisationRegularAtPrime
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ThetaSectionGeneratorPower
import Development.AbelianVarietyTheory.Proofs.DegenerationProofs.ExistsGoodTorsionTranslateGeometricPoint
import Development.AbelianVarietyTheory.Proofs.ModuliProofs.ExistsThetaLevelAbelianSchemeGlueAffineCover

section
open CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj AlgebraicGeometry
open scoped CategoryTheory.Obj
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Geo.Tor GlobalTheory.ZH
open Classical
open ReciprocityTheory.ChartRestriction.G.Out
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.ThetaReal

noncomputable section
namespace GlobalTheory.ThetaSBasis

/- English proof (translation)
Introduce `s` and use `by obtain ⟨r, hr, -⟩ := h s exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩`.
-/
theorem isGenSec_of_isSecBasis {S : Scheme.{0}} (P : PolAV S) {T : Over S} {th : LB.Sec (LPow P.A P.L 1 T)}
    (h : IsSecBasis _ (fun _ : Fin 1 => th)) : IsGenSec P.A P.L 1 th := fun s => by
  obtain ⟨r, hr, -⟩ := h s
  exact ⟨r 0, fun j => (hr j).trans (Fin.sum_univ_one _)⟩

/- English proof (translation)
Establish `: Nonempty (h ''ᵁ ⊤)`. Take `⟨y⟩` from `‹Nonempty Y'›`. Conclude with `⟨⟨h y, y, trivial, rfl⟩⟩`. Introduce `a b e`. Apply `map_injective_of_isIntegral Y (homOfLE (le_top : h ''ᵁ ⊤ ≤ ⊤))` to reduce the goal to its premises.

Establish `e₁` using `h.app_appIso_inv (⊤ : Y.Opens)`. Establish `k` using `fun x => congrArg (fun q => q.hom x) e₁`. Simplify using `only [CommRingCat.hom_comp, RingHom.comp_apply] at k`. Conclude with `(k a).symm.trans ((congrArg _ e).trans (k b))`.
-/
theorem appTop_injective {Y Y' : Scheme.{0}} [IsIntegral Y] (h : Y' ⟶ Y) [IsOpenImmersion h] [Nonempty Y'] :
    Function.Injective h.appTop.hom := by
  have : Nonempty (h ''ᵁ ⊤) := by
    obtain ⟨y⟩ := ‹Nonempty Y'›
    exact ⟨⟨h y, y, trivial, rfl⟩⟩
  intro a b e
  apply map_injective_of_isIntegral Y (homOfLE (le_top : h ''ᵁ ⊤ ≤ ⊤))
  have e₁ := h.app_appIso_inv (⊤ : Y.Opens)
  have k := fun x => congrArg (fun q => q.hom x) e₁
  simp only [CommRingCat.hom_comp, RingHom.comp_apply] at k
  exact (k a).symm.trans ((congrArg _ e).trans (k b))

/- English proof (translation)
Establish `key : ∀ (g : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (Y.basicOpen a)) (g' : Opposite.op (Y.basicOpen a) ⟶ Opposite.op ⊤), (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a`. Introduce `g g'`. Rewrite using `[← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _), CategoryTheory.Functor.map_id, CommRingCat.id_apply]`. Establish `u` using `(Y.toRingedSpace.isUnit_res_basicOpen a).map (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom`. Use `u using 1` and compare the differences between its conclusion and the goal.

Conclude with `(key _ _).symm`.
-/
theorem isUnit_of_basicOpen_eq_top {Y : Scheme.{0}} (a : Γ(Y, ⊤)) (h : Y.basicOpen a = ⊤) :
    IsUnit a := by
  have key : ∀ (g : Opposite.op (⊤ : Y.Opens) ⟶ Opposite.op (Y.basicOpen a)) (g' : Opposite.op (Y.basicOpen a) ⟶ Opposite.op ⊤),
      (Y.presheaf.map g').hom ((Y.presheaf.map g).hom a) = a := by
    intro g g'
    rw [← CommRingCat.comp_apply, ← Functor.map_comp, Subsingleton.elim (g ≫ g') (𝟙 _),
      CategoryTheory.Functor.map_id, CommRingCat.id_apply]
  have u := (Y.toRingedSpace.isUnit_res_basicOpen a).map
    (Y.presheaf.map (homOfLE (le_of_eq h.symm)).op).hom
  convert u using 1
  exact (key _ _).symm

/- English proof (translation)
Set `β : Over.mk x ⟶ baseOver S` to `Over.homMk x (by simp)`. Establish `: IsAffine (baseOver S).left` using `‹IsAffine S›`. Establish `h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0` using `GlobalTheory.ThetaSpan.pullS_ne_zero P hL₂.secBaseChangeAny hth x β`. Take `⟨y, hy, hu⟩` from `GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a`. Use `⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩` and prove the remaining obligations.

Set `p : (Over.mk x).left` to `IsLocalRing.closedPoint K`. Take `⟨J, hJ⟩` from `GlobalTheory.ConstFam.exists_good' P.isLB p`. Establish `q` using `hu p J hJ`. Establish `e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left`. Rewrite using `[← Over.comp_left, ← Over.comp_left, ← hz]`.

Use `congr 1`. Apply the tactic sequence `ext1 <;> simp [ptSecT, β]`. Rewrite `q` using `[VVRank.sv_pullS _ _ _ _ _ _ hJ, e, GlobalTheory.ThetaPtMove.sv_of_isValueAt hv _ p hJ, h0, GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul]`. Conclude with `not_isUnit_zero q`.
-/
theorem exists_good_translate (hL : Laws) (hL₂ : Laws2) {S : Scheme.{0}} [IsAffine S] (P : PolAV S) (K : Type)
    [Field K] [IsAlgClosed K] (x : Sp K ⟶ S) (n : ℕ) (hn : 2 ≤ n) (hK : (n : K) ≠ 0)
    (th : LB.Sec (LPow P.A P.L 1 (baseOver S))) (hth : IsGenSec P.A P.L 1 th) (a : Over.mk x ⟶ P.A) :
    ∃ y : Over.mk x ⟶ P.A, y ^ n = 1 ∧ ∀ (z : baseOver S ⟶ P.A)
      (τ : LB.Gen (LB.LinComb P.L (Y := (baseOver S).left) (K := Fin 1) (fun _ => z.left) (fun _ => 1)))
      (v : Γ((baseOver S).left, ⊤)), (Over.homMk x (by simp) : Over.mk x ⟶ baseOver S) ≫ z = a * y →
        τ.IsGen → IsValueAt P.A P.L 1 th z τ v → v ≠ 0 := by
  let β : Over.mk x ⟶ baseOver S := Over.homMk x (by simp)
  have : IsAffine (baseOver S).left := ‹IsAffine S›
  have h₀ : SecM.ofSec P.A (VVRank.pullS P.A 1 β th) ≠ 0 :=
    GlobalTheory.ThetaSpan.pullS_ne_zero P hL₂.secBaseChangeAny hth x β
  obtain ⟨y, hy, hu⟩ := GlobalTheory.UT.ExactTerm.exists_good_point hL.goodPt hL.polBaseChange P x hn hK _ h₀ a
  refine ⟨y, hy, fun z τ v hz _ hv h0 => ?_⟩
  let p : (Over.mk x).left := IsLocalRing.closedPoint K
  obtain ⟨J, hJ⟩ := GlobalTheory.ConstFam.exists_good' P.isLB p
  have q := hu p J hJ
  have e : (ptSecT P.A (a * y)).left ≫ (β ▷ P.A).left = β.left ≫ (ptSecT P.A z).left := by
    rw [← Over.comp_left, ← Over.comp_left, ← hz]
    congr 1
    ext1 <;> simp [ptSecT, β]
  rw [VVRank.sv_pullS _ _ _ _ _ _ hJ, e, GlobalTheory.ThetaPtMove.sv_of_isValueAt hv _ p hJ, h0,
    GlobalTheory.UT.ExactTerm.gs_zero' β.left p ⊤ trivial, MulZeroClass.zero_mul] at q
  exact not_isUnit_zero q

open VVRank in

/- English proof (translation)
Set `X : Scheme.{0}` to `(baseOver (Sp R)).left`. Establish `haff : IsAffine X` using `inferInstanceAs (IsAffine (Sp R))`. Establish `hint : IsIntegral X` using `inferInstanceAs (IsIntegral (Sp R))`. Set `p : X` to `(⊥ : PrimeSpectrum R)`. Take `⟨V, hV, b, hb⟩` from `hS (Sp R) P N hN p`.

Take `⟨f, hf, hp⟩` from `(isAffineOpen_top X).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial`. Set `W` to `X.basicOpen f`. Set `l : overRes W ⟶ overRes (T` to `baseOver (Sp R)) V := Over.homMk (X.homOfLE hf) (by`. Express the relevant statement in the definitionally equal form `X.homOfLE hf ≫ V.ι ≫ _ = W.ι ≫ _`. Rewrite using `[Scheme.homOfLE_ι_assoc])`.

Establish `hW : IsAffineOpen W` using `(isAffineOpen_top _).basicOpen f`. Establish `: IsAffine (overRes W).left` using `hW`. Take `⟨c, hc⟩` from `exists_basis P N b hb (overRes W) l`. Establish `: Nonempty (overRes W).left` using `⟨⟨p, hp⟩⟩`. Establish `: IsOpenImmersion (overResι W).left` using `inferInstanceAs (IsOpenImmersion W.ι)`.

Set `σ` to `(overResι W).left.appTop.hom`. Establish `hσ : Function.Injective σ` using `appTop_injective (overResι W).left`. Establish `hnt : Nontrivial Γ((overRes W).left, ⊤)` using `⟨⟨1, 0, fun e => one_ne_zero (hσ ((map_one σ).trans (e.trans (map_zero σ).symm)))⟩⟩`. Establish `hfu : IsUnit (σ f)` using `isUnit_of_basicOpen_eq_top _ (by`. Use `(Scheme.preimage_basicOpen_top (overResι W).left f).symm.trans ?_` and prove the remaining obligations.

Conclude with `eq_top_iff.2 fun z _ => z.2)`. Establish `key : ∀ u ∈ Submodule.span Γ(X, ⊤) (Set.range t), pullM P.A P.L N (overResι W) u ∈ Submodule.span Γ((overRes W).left, ⊤) (Set.range fun i => pullM P.A P.L N (overResι W) (t i))`. Introduce `u hu`. Proceed by induction on `hu using Submodule.span_induction with`. Consider the case `mem y hy`.

Take `⟨i, rfl⟩` from `hy`. Conclude with `Submodule.subset_span ⟨i, rfl⟩`. Consider the case `zero => rw [map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add y z _ _ hy hz => rw [map_add]`.

Conclude with `Submodule.add_mem _ hy hz`. Consider the case `smul d y _ hy => rw [LinearMap.map_smulₛₗ]`. Conclude with `Submodule.smul_mem _ _ hy`. Establish `hspanW : ⊤ ≤ Submodule.span Γ((overRes W).left, ⊤) (Set.range fun i => pullM P.A P.L N (overResι W) (t i))`. Introduce `y _`.

Take `⟨n, u, hu⟩` from `EmbPull.exists_pow_extend_secM P N f y`. Establish `h1` using `key u (hspan trivial)`. Rewrite `h1` using `[hu]`. Take `⟨v, hv⟩` from `(hfu.pow n).exists_left_inv`. Establish `h2` using `Submodule.smul_mem _ v h1`.

Rewrite `h2` using `[smul_smul, map_pow, hv, one_smul]`. Then use the resulting hypothesis. Use `haveI : Module.Free Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W)) := Module.Free.of_basis c`. Use `haveI : Module.Finite Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W)) := Module.Finite.of_basis c`. Establish `hfr : Fintype.card κ = Module.finrank Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W))`. Rewrite using `[Module.finrank_eq_card_basis c, hcard, Fintype.card_fin]`.

Establish `hli` using `linearIndependent_of_top_le_span_of_card_eq_finrank hspanW hfr`. Rewrite `hli`, the goal using `[linearIndependent_iff']`. Introduce `s g hg i hi`. Establish `e` using `congrArg (pullM P.A P.L N (overResι W)) hg`. Rewrite `e` using `[map_sum, map_zero]`.

Simplify using `only [LinearMap.map_smulₛₗ] at e`. Conclude with `hσ ((hli s (fun i => σ (g i)) e i hi).trans (map_zero σ).symm)`.
-/
theorem linearIndependent_of_span (hS : SecBaseChangeAnySt) {R : Type} [CommRing R] [IsDomain R]
    (P : PolAV (Sp R)) (N : ℕ) (hN : 1 ≤ N) {κ : Type} [Fintype κ]
    (t : κ → SecM P.A P.L N (baseOver (Sp R))) (hcard : Fintype.card κ = N ^ P.g)
    (hspan : ⊤ ≤ Submodule.span Γ((baseOver (Sp R)).left, ⊤) (Set.range t)) :
    LinearIndependent Γ((baseOver (Sp R)).left, ⊤) t := by
  let X : Scheme.{0} := (baseOver (Sp R)).left
  have haff : IsAffine X := inferInstanceAs (IsAffine (Sp R))
  have hint : IsIntegral X := inferInstanceAs (IsIntegral (Sp R))
  let p : X := (⊥ : PrimeSpectrum R)
  obtain ⟨V, hV, b, hb⟩ := hS (Sp R) P N hN p
  obtain ⟨f, hf, hp⟩ := (isAffineOpen_top X).exists_basicOpen_le (V := V) ⟨p, hV⟩ trivial
  let W := X.basicOpen f
  let l : overRes W ⟶ overRes (T := baseOver (Sp R)) V := Over.homMk (X.homOfLE hf) (by
    change X.homOfLE hf ≫ V.ι ≫ _ = W.ι ≫ _
    rw [Scheme.homOfLE_ι_assoc])
  have hW : IsAffineOpen W := (isAffineOpen_top _).basicOpen f
  have : IsAffine (overRes W).left := hW
  obtain ⟨c, hc⟩ := exists_basis P N b hb (overRes W) l
  have : Nonempty (overRes W).left := ⟨⟨p, hp⟩⟩
  have : IsOpenImmersion (overResι W).left := inferInstanceAs (IsOpenImmersion W.ι)
  let σ := (overResι W).left.appTop.hom
  have hσ : Function.Injective σ := appTop_injective (overResι W).left
  have hnt : Nontrivial Γ((overRes W).left, ⊤) :=
    ⟨⟨1, 0, fun e => one_ne_zero (hσ ((map_one σ).trans (e.trans (map_zero σ).symm)))⟩⟩
  have hfu : IsUnit (σ f) := isUnit_of_basicOpen_eq_top _ (by
    refine (Scheme.preimage_basicOpen_top (overResι W).left f).symm.trans ?_
    exact eq_top_iff.2 fun z _ => z.2)
  have key : ∀ u ∈ Submodule.span Γ(X, ⊤) (Set.range t), pullM P.A P.L N (overResι W) u ∈
      Submodule.span Γ((overRes W).left, ⊤) (Set.range fun i => pullM P.A P.L N (overResι W) (t i)) := by
    intro u hu
    induction hu using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨i, rfl⟩ := hy
      exact Submodule.subset_span ⟨i, rfl⟩
    | zero => rw [map_zero]; exact Submodule.zero_mem _
    | add y z _ _ hy hz => rw [map_add]; exact Submodule.add_mem _ hy hz
    | smul d y _ hy => rw [LinearMap.map_smulₛₗ]; exact Submodule.smul_mem _ _ hy
  have hspanW : ⊤ ≤ Submodule.span Γ((overRes W).left, ⊤)
      (Set.range fun i => pullM P.A P.L N (overResι W) (t i)) := by
    intro y _
    obtain ⟨n, u, hu⟩ := EmbPull.exists_pow_extend_secM P N f y
    have h1 := key u (hspan trivial)
    rw [hu] at h1
    obtain ⟨v, hv⟩ := (hfu.pow n).exists_left_inv
    have h2 := Submodule.smul_mem _ v h1
    rwa [smul_smul, map_pow, hv, one_smul] at h2
  haveI : Module.Free Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W)) := Module.Free.of_basis c
  haveI : Module.Finite Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W)) := Module.Finite.of_basis c
  have hfr : Fintype.card κ = Module.finrank Γ((overRes W).left, ⊤) (SecM P.A P.L N (overRes W)) := by
    rw [Module.finrank_eq_card_basis c, hcard, Fintype.card_fin]
  have hli := linearIndependent_of_top_le_span_of_card_eq_finrank hspanW hfr
  rw [linearIndependent_iff'] at hli ⊢
  intro s g hg i hi
  have e := congrArg (pullM P.A P.L N (overResι W)) hg
  rw [map_sum, map_zero] at e
  simp only [LinearMap.map_smulₛₗ] at e
  exact hσ ((hli s (fun i => σ (g i)) e i hi).trans (map_zero σ).symm)

/- English proof (translation)
Introduce `o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ u s₀ h1 h2 h3 h4 h5 H`. Substitute `hN` using the available equality. Use `haveI : NeZero m := ⟨by omega⟩`. Use `haveI : NeZero (r * m ^ 2) := ⟨by positivity⟩`. Establish `hd : m ∣ r * m ^ 2` using `⟨r * m, by ring⟩`.

Set `π : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → ZMod m)` to `fun a i => ZMod.castHom hd (ZMod m) (a i)`. Set `x : (Fin g ⊕ Fin g → ZMod m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2))` to `fun j i => (((j i).val : ℕ) : ZMod (r * m ^ 2))`. Establish `hπadd : ∀ a b, π (a + b) = π a + π b`. Introduce `a b`. Use function extensionality and compare the values at `i`.

Simplify using `only [π, Pi.add_apply, map_add]`. Establish `hπsub : ∀ a b, π (a - b) = π a - π b`. Introduce `a b`. Use function extensionality and compare the values at `i`. Simplify using `only [π, Pi.sub_apply, map_sub]`.

Establish `hπx : ∀ j, π (x j) = j`. Introduce `j`. Use function extensionality and compare the values at `i`. Simplify using `only [π, x, map_natCast, ZMod.natCast_zmod_val]`. Establish `hx0 : x 0 = 0`.

Use function extensionality and compare the values at `i`. Simplify using `[x]`. Establish `hker : ∀ a, π a = 0 → (r * m) • a = 0`. Introduce `a ha`. Use function extensionality and compare the values at `i`.

Establish `hi : ZMod.castHom hd (ZMod m) (a i) = 0` using `congrFun ha i`. Take `⟨n, hn⟩` from `ZMod.natCast_zmod_surjective (a i)`. Rewrite `hi` using `[← hn, map_natCast, ZMod.natCast_eq_zero_iff]`. Take `⟨c, rfl⟩` from `hi`. Rewrite using `[Pi.smul_apply, ← hn, nsmul_eq_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]`.

Conclude with `⟨c, by ring⟩`. Set `s : (Fin g ⊕ Fin g → ZMod m) → M` to `fun j => u (x j) s₀`. Establish `key : ∀ a, ∃ e : ℕ, u a s₀ = f (ζ ^ e) • s (π a)`. Introduce `a`. Establish `hh : (r * m) • (a - x (π a)) = 0` using `hker _ (by rw [hπsub, hπx, sub_self])`.

Take `⟨e, he⟩` from `h2 (x (π a)) (a - x (π a))`. Use `he s₀` as an intermediate fact. Rewrite `this` using `[h4 _ hh, add_sub_cancel]`. Use `⟨(q - 1) * e, ?_⟩` and prove the remaining obligations. Establish `hq' : (q - 1) * e + e = q * e`.

Take `⟨p, rfl⟩` from `Nat.exists_eq_add_of_le' hq`. Simplify using `[add_mul]`. Simplify using `only [s]`. Rewrite using `[this, smul_smul, ← map_mul, ← pow_add, hq', pow_mul, hζ, one_pow, map_one, one_smul]`. Establish `key2 : ∀ a i, ∃ e : ℕ, u a (s i) = f (ζ ^ e) • s (π a + i)`.

Introduce `a i`. Take `⟨e, he⟩` from `h2 a (x i)`. Take `⟨e', he'⟩` from `key (a + x i)`. Use `⟨e + e', ?_⟩` and prove the remaining obligations. Use `he s₀` as an intermediate fact.

Rewrite `this` using `[he', hπadd, hπx, smul_smul, ← map_mul, ← pow_add]`. Conclude with `this`. Use `choose E hE using key2`. Establish `hspan : ⊤ ≤ Submodule.span A (Set.range s)`. Rewrite using `[← h5, Submodule.span_le]`.

Introduce and unpack `_ ⟨a, rfl⟩`. Take `⟨e, he⟩` from `key a`. Simplify using `only [he]`. Conclude with `Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)`. Establish `hcard : Fintype.card (Fin g ⊕ Fin g → ZMod m) = (m ^ 2) ^ g`.

Simplify using `only [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin]`. Expand and normalize the polynomial expressions, which then agree. Establish `hli : LinearIndependent A s` using `H s hspan`. Set `b : Module.Basis (Fin g ⊕ Fin g → ZMod m) A M` to `Module.Basis.mk hli hspan`. Establish `hb : ∀ i, b i = s i` using `fun i => Module.Basis.mk_apply hli hspan i`.

Set `ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → ZMod m) (Fin g ⊕ Fin g → ZMod m) o` to `fun a l i => if l = π a + i then ζ ^ E a i else 0`. Establish `hρ : ∀ a, (ρ a).map f = LinearMap.toMatrix b b (u a)`. Introduce `a`. Use extensionality with `l i`. Rewrite using `[LinearMap.toMatrix_apply, hb, hE, ← hb, map_smul, Module.Basis.repr_self]`.

Rewrite using `[Matrix.map_apply, Finsupp.smul_apply, smul_eq_mul]`. Distinguish the cases in `h : l = π a + i`. Establish `: ρ a l i = ζ ^ E a i` using `if_pos h`. Rewrite using `[this, h, Finsupp.single_eq_same, _root_.mul_one]`. Establish `: ρ a l i = 0` using `if_neg h`.

Rewrite using `[this, Finsupp.single_eq_of_ne h, mul_zero, map_zero]`. Establish `hinj : Function.Injective (fun X : Matrix (Fin g ⊕ Fin g → ZMod m) (Fin g ⊕ Fin g → ZMod m) o => X.map f)` using `Matrix.map_injective hf`. Establish `hmul : ∀ a c, (ρ a * ρ c).map f = LinearMap.toMatrix b b (u a ∘ₗ u c)`. Introduce `a c`. Rewrite using `[Matrix.map_mul, hρ, hρ, LinearMap.toMatrix_comp b b b]`.

Use `⟨Fin g ⊕ Fin g → ZMod m, inferInstance, ρ, b, 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[hb]; simp only [s, hx0]; exact h1 0 (by simp) _`. Introduce `a ha`. Apply `hinj` to reduce the goal to its premises. Establish `: u a = LinearMap.id` using `LinearMap.ext (h1 a ha)`.

Simplify using `only [hρ, this]`. Use extensionality with `l i`. Simplify using `[Matrix.one_apply, apply_ite f]`. Introduce `a c`. Take `⟨e, he⟩` from `h2 a c`.

Use `⟨e, hinj ?_⟩` and prove the remaining obligations. Establish `: u a ∘ₗ u c = f (ζ ^ e) • u (a + c)` using `LinearMap.ext he`. Simplify using `only [hmul, this, map_smul, ← hρ]`. Use extensionality with `l i`. Simplify using the standard rewrite rules.

Introduce `a c hac`. Apply `hinj` to reduce the goal to its premises. Establish `: u a ∘ₗ u c = u (a + c)` using `LinearMap.ext (h3 a c hac)`. Simplify using `only [hmul, this, hρ]`. Introduce `a i`.

Rewrite using `[hb, hE, Finset.sum_eq_single (π a + i)]`. Simplify using `[ρ, hb]`. Introduce `l _ hl`. Simplify using `[ρ, hl]`. Simplify using the standard rewrite rules.

Introduce `i`. Use `⟨x i, E (x i) 0, fun l => ?_⟩` and prove the remaining obligations. Simplify using `[ρ, hπx]`.
-/
theorem exists_monomial_matrices_of_indep : ∀ (o A M : Type) [CommRing o] [CommRing A] [Nontrivial A] [AddCommGroup M] [Module A M] (f : o →+* A), Function.Injective f → ∀ (g m r N : ℕ), N = m ^ 2 → 1 ≤ m → 1 ≤ r → ∀ (ζ : o) (q : ℕ), 1 ≤ q → ζ ^ q = 1 → ∀ (u : (Fin g ⊕ Fin g → ZMod (r * N)) → M →ₗ[A] M) (s₀ : M), (∀ a, r • a = 0 → ∀ v, u a v = v) → (∀ a b, ∃ e : ℕ, ∀ v, u a (u b v) = f (ζ ^ e) • u (a + b) v) → (∀ a b, r • eStd g _ a b = 0 → ∀ v, u a (u b v) = u (a + b) v) → (∀ a, (r * m) • a = 0 → u a s₀ = s₀) → Submodule.span A (Set.range fun a => u a s₀) = ⊤ → (∀ t : (Fin g ⊕ Fin g → ZMod m) → M, ⊤ ≤ Submodule.span A (Set.range t) → LinearIndependent A t) → ∃ (J : Type) (_ : Fintype J) (ρ : (Fin g ⊕ Fin g → ZMod (r * N)) → Matrix J J o) (s : Module.Basis J A M) (i₀ : J), Fintype.card J = N ^ g ∧ s i₀ = s₀ ∧ (∀ a, r • a = 0 → ρ a = 1) ∧ (∀ a b, ∃ k : ℕ, ρ a * ρ b = ζ ^ k • ρ (a + b)) ∧ (∀ a b, r • eStd g _ a b = 0 → ρ a * ρ b = ρ (a + b)) ∧ (∀ a i, u a (s i) = ∑ l, f (ρ a l i) • s l) ∧ ∀ i, ∃ a, ∃ e : ℕ, ∀ l, ρ a l i₀ = if l = i then ζ ^ e else 0 := by
  intro o A M _ _ _ _ _ f hf g m r N hN hm hr ζ q hq hζ u s₀ h1 h2 h3 h4 h5 H
  subst hN
  haveI : NeZero m := ⟨by omega⟩
  haveI : NeZero (r * m ^ 2) := ⟨by positivity⟩
  have hd : m ∣ r * m ^ 2 := ⟨r * m, by ring⟩
  let π : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → (Fin g ⊕ Fin g → ZMod m) :=
    fun a i => ZMod.castHom hd (ZMod m) (a i)
  let x : (Fin g ⊕ Fin g → ZMod m) → (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) :=
    fun j i => (((j i).val : ℕ) : ZMod (r * m ^ 2))
  have hπadd : ∀ a b, π (a + b) = π a + π b := by
    intro a b; funext i; simp only [π, Pi.add_apply, map_add]
  have hπsub : ∀ a b, π (a - b) = π a - π b := by
    intro a b; funext i; simp only [π, Pi.sub_apply, map_sub]
  have hπx : ∀ j, π (x j) = j := by
    intro j; funext i; simp only [π, x, map_natCast, ZMod.natCast_zmod_val]
  have hx0 : x 0 = 0 := by
    funext i; simp [x]
  have hker : ∀ a, π a = 0 → (r * m) • a = 0 := by
    intro a ha
    funext i
    have hi : ZMod.castHom hd (ZMod m) (a i) = 0 := congrFun ha i
    obtain ⟨n, hn⟩ := ZMod.natCast_zmod_surjective (a i)
    rw [← hn, map_natCast, ZMod.natCast_eq_zero_iff] at hi
    obtain ⟨c, rfl⟩ := hi
    rw [Pi.smul_apply, ← hn, nsmul_eq_mul, ← Nat.cast_mul, Pi.zero_apply, ZMod.natCast_eq_zero_iff]
    exact ⟨c, by ring⟩
  let s : (Fin g ⊕ Fin g → ZMod m) → M := fun j => u (x j) s₀
  have key : ∀ a, ∃ e : ℕ, u a s₀ = f (ζ ^ e) • s (π a) := by
    intro a
    have hh : (r * m) • (a - x (π a)) = 0 := hker _ (by rw [hπsub, hπx, sub_self])
    obtain ⟨e, he⟩ := h2 (x (π a)) (a - x (π a))
    have := he s₀
    rw [h4 _ hh, add_sub_cancel] at this
    refine ⟨(q - 1) * e, ?_⟩
    have hq' : (q - 1) * e + e = q * e := by
      obtain ⟨p, rfl⟩ := Nat.exists_eq_add_of_le' hq
      simp [add_mul]
    simp only [s]
    rw [this, smul_smul, ← map_mul, ← pow_add, hq', pow_mul, hζ, one_pow, map_one, one_smul]
  have key2 : ∀ a i, ∃ e : ℕ, u a (s i) = f (ζ ^ e) • s (π a + i) := by
    intro a i
    obtain ⟨e, he⟩ := h2 a (x i)
    obtain ⟨e', he'⟩ := key (a + x i)
    refine ⟨e + e', ?_⟩
    have := he s₀
    rw [he', hπadd, hπx, smul_smul, ← map_mul, ← pow_add] at this
    exact this
  choose E hE using key2
  have hspan : ⊤ ≤ Submodule.span A (Set.range s) := by
    rw [← h5, Submodule.span_le]
    rintro _ ⟨a, rfl⟩
    obtain ⟨e, he⟩ := key a
    simp only [he]
    exact Submodule.smul_mem _ _ (Submodule.subset_span ⟨_, rfl⟩)
  have hcard : Fintype.card (Fin g ⊕ Fin g → ZMod m) = (m ^ 2) ^ g := by
    simp only [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin]
    ring
  have hli : LinearIndependent A s := H s hspan
  let b : Module.Basis (Fin g ⊕ Fin g → ZMod m) A M := Module.Basis.mk hli hspan
  have hb : ∀ i, b i = s i := fun i => Module.Basis.mk_apply hli hspan i
  let ρ : (Fin g ⊕ Fin g → ZMod (r * m ^ 2)) → Matrix (Fin g ⊕ Fin g → ZMod m) (Fin g ⊕ Fin g → ZMod m) o :=
    fun a l i => if l = π a + i then ζ ^ E a i else 0
  have hρ : ∀ a, (ρ a).map f = LinearMap.toMatrix b b (u a) := by
    intro a
    ext l i
    rw [LinearMap.toMatrix_apply, hb, hE, ← hb, map_smul, Module.Basis.repr_self]
    rw [Matrix.map_apply, Finsupp.smul_apply, smul_eq_mul]
    by_cases h : l = π a + i
    · have : ρ a l i = ζ ^ E a i := if_pos h
      rw [this, h, Finsupp.single_eq_same, _root_.mul_one]
    · have : ρ a l i = 0 := if_neg h
      rw [this, Finsupp.single_eq_of_ne h, mul_zero, map_zero]
  have hinj : Function.Injective (fun X : Matrix (Fin g ⊕ Fin g → ZMod m) (Fin g ⊕ Fin g → ZMod m) o => X.map f) := Matrix.map_injective hf
  have hmul : ∀ a c, (ρ a * ρ c).map f = LinearMap.toMatrix b b (u a ∘ₗ u c) := by
    intro a c
    rw [Matrix.map_mul, hρ, hρ, LinearMap.toMatrix_comp b b b]
  refine ⟨Fin g ⊕ Fin g → ZMod m, inferInstance, ρ, b, 0, hcard, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rw [hb]; simp only [s, hx0]; exact h1 0 (by simp) _
  · intro a ha
    apply hinj
    have : u a = LinearMap.id := LinearMap.ext (h1 a ha)
    simp only [hρ, this]
    ext l i
    simp [Matrix.one_apply, apply_ite f]
  · intro a c
    obtain ⟨e, he⟩ := h2 a c
    refine ⟨e, hinj ?_⟩
    have : u a ∘ₗ u c = f (ζ ^ e) • u (a + c) := LinearMap.ext he
    simp only [hmul, this, map_smul, ← hρ]
    ext l i
    simp
  · intro a c hac
    apply hinj
    have : u a ∘ₗ u c = u (a + c) := LinearMap.ext (h3 a c hac)
    simp only [hmul, this, hρ]
  · intro a i
    rw [hb, hE, Finset.sum_eq_single (π a + i)]
    · simp [ρ, hb]
    · intro l _ hl
      simp [ρ, hl]
    · simp
  · intro i
    refine ⟨x i, E (x i) 0, fun l => ?_⟩
    simp [ρ, hπx]

end GlobalTheory.ThetaSBasis
end
end

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj IsLocalRing
open ReciprocityTheory.ChartRestriction.G ReciprocityTheory.ChartRestriction.G.Semi ReciprocityTheory.ChartRestriction.G.Out ReciprocityTheory.ChartRestriction.G.Geo.Tor
open GlobalTheory.Toroidal GlobalTheory.LocM GlobalTheory.PolFan GlobalTheory.ZM GlobalTheory.SiegelTor GlobalTheory.TorRef GlobalTheory.PolDeg
open scoped CategoryTheory.Obj
open ReciprocityTheory.AnForm.R GlobalTheory.ZH GlobalTheory.Poinc GlobalTheory.Poinc.Sep
attribute [local instance] Over.cartesianMonoidalCategory
open GlobalTheory.UT ReciprocityTheory.ChartRestriction.G.DVR

open Classical GlobalTheory.ThetaReal GlobalTheory.ThetaSBasis in

/- English proof (translation)
Introduce `o Ω _ _ _ _ R fg frac P n k j ze hp ho hk hj hu hS th hth lev`. Take `⟨hL, hL₂⟩` from `GlobalTheory.abelianSchemeLaws_all`. Establish `hgen : IsGenSec P.A P.L 1 th` using `isGenSec_of_isSecBasis P hth`. Use `haveI := isNoetherian_of_fg fg`. Use `haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))`.

Establish `hn2 : 2 ≤ n` using `hp.two_le`. Establish `hn1 : 1 ≤ n` using `by omega`. Establish `hm1 : 1 ≤ n ^ k` using `Nat.one_le_pow _ _ hn1`. Establish `hr1 : 1 ≤ n ^ j` using `Nat.one_le_pow _ _ hn1`. Use `haveI : NeZero (n ^ k) := ⟨by omega⟩`.

Establish `hN2 : 2 ≤ (n ^ k) ^ 2`. Establish `: n ^ 1 ≤ n ^ k` using `Nat.pow_le_pow_right hn1 (by omega)`. Use the polynomial consequences of the given equalities and inequalities. Establish `hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k)` using `by ring`. Establish `hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2` using `hM ▸ Nat.one_le_pow _ _ hn1`.

Establish `hMo : Odd (n ^ j * (n ^ k) ^ 2)` using `hM ▸ ho.pow`. Set `f : o →+* Γ((baseOver (Sp R)).left, ⊤)` to `(Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)`. Establish `hf : Function.Injective f` using `fn_injective.comp (algebraMap_injective R)`. Use `haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial`. Establish `un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤))` using `fun q e hq => by`.

Use `(hu.pow e).map f` as an intermediate fact. Rewrite `this` using `[map_pow, map_natCast]`. Rewrite using `[hq, Nat.cast_pow]`. Conclude with `this`. Establish `prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2)` using `(prim_iff R ze _).1 lev.prim`.

Take `⟨pt, hadd, hbij, hweil, hdiv, -⟩` from `GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt hL _ P _ _ hM1 (un _ _ hM) lev`. Take `⟨h0, hsm⟩` from `pt_nsmul pt hadd`. Take `⟨rig, hrig⟩` from `P.rigid`. Establish `hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ` using `fun a => by`. Take `⟨y, hy, e⟩` from `hdiv a`.

Take `⟨θ, hθ⟩` from `GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy`. Conclude with `GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ`. Use `choose fr hfr using hfr`. Establish `tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1` using `fun a => by`. Rewrite using `[← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]`.

Use `choose U hU using fun a => GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)`. Take `⟨α, hα, hαn⟩` from `GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))`. Take `⟨s₀, hs₀⟩` from `VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _) (b := 1) P.isLB hα th`. Take `⟨u, u₁, u₂, u₃, u₄, u₅⟩` from `exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀`. Establish `hspan` using `GlobalTheory.ThetaSpan.span_translates_mulPull_of_isGenSec hL hL₂ R P (n ^ k) _ rfl hm1 (un _ _ rfl) th hgen α hα s₀ hs₀ _ U (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by`.

Take `⟨a, ha, uniq⟩` from `hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])`. Take `⟨a₀, -, uniq₀⟩` from `hbij K x 1 (one_pow _)`. Establish `e : (n ^ k) ^ 2 • a = 0` using `(uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm`. Take `⟨c, rfl⟩` from `exists_nsmul_eq hM1 a e`. Conclude with `⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)`.

Take `⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩` from `exists_monomial_matrices_of_indep o _ _ f hf P.g (n ^ k) (n ^ j) _ rfl hm1 hr1 ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one u (SecM.ofSec P.A s₀) u₂ (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan (fun t ht => linearIndepe …`. Simplify using `only [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin]`. Use the proof step `ring) ht)`. Use `choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1`. Use `choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists`.

Set `ev : Γ((baseOver (Sp R)).left, ⊤) → R` to `(Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom`. Establish `good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0}` using `fun a => by`. Set `K` to `AlgebraicClosure Ω`. Set `x : Sp K ⟶ Sp R` to `spMap ((algebraMap Ω K).comp R.val.toRingHom)`. Use `ArithBase.char (o := o) (Ω := Ω)` as an intermediate fact.

Take `⟨y, hy, H⟩` from `GlobalTheory.ThetaSBasis.exists_good_translate hL hL₂ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th hgen ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)`. Take `⟨c, hc, -⟩` from `hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy, one_pow])`. Take `⟨a₀, -, uniq₀⟩` from `hbij K x 1 (one_pow _)`. Use `⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩` and prove the remaining obligations. Use `H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_` and prove the remaining obligations.

Establish `e' : ev (v (a + c)) = 0` using `Subtype.ext e`. Conclude with `(fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))`. Set `S : ThetaSys o Ω` to `{ g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim unit := by rw [hM, Nat.cast_pow]; exact hu.pow _ J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃ th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, fr …`. Take `⟨y, -, hy⟩` from `good 0`. Conclude with `⟨_, hy⟩ }`.

Set `ρ' : S.Real` to `{ P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij weil := fun a b c hc => by`. Establish `e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^ (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val)` using `Units.ext ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))`. Rewrite using `[e]`. Conclude with `hweil a b`. Use `rig := rig, rig_gen := hrig, th₁ := th`.

Use `th₁_basis := hth`. Use `fr := fr, fr_tors := hfr`. Use `th_val := fun a => (fn_hom (v a)).symm ▸ hv a`. Use `s := fun i => SecM.toSec P.A (s i)`. Use `s_basis := existsUnique_of_basis s`.

Use `ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)`. Use `i₀ := i₀, α := α, α_gen := hα, α_norm := hαn`. Use `s_zero := by`. Establish `e : SecM.toSec P.A (s i₀) = s₀` using `by rw [hi₀]; rfl`. Conclude with `e ▸ hs₀`.

Use `U := U, U_sym := hU`. Use `U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))`. Use `orbit := ρ₅ }`. Establish `eid : spMap (Subalgebra.inclusion (le_refl R)).toRingHom = 𝟙 (Sp R)`. Rewrite using `[Subalgebra.inclusion_self]`.

Conclude with `Spec.map_id _`. Use `⟨S, ρ', le_refl R, 𝟙 _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩` and prove the remaining obligations. Use `show IsGrpPullback P.A P.A (spMap (Subalgebra.inclusion (le_refl R)).toRingHom) (𝟙 P.A.left)`. Rewrite using `[eid]`. Use `⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩` and prove the remaining obligations.

Set `ρ₀ : Over.mk (T.hom ≫ 𝟙 (Sp R)) ⟶ T` to `Over.homMk (𝟙 T.left) (by simp)`. Establish `ex : x₀ = ρ₀ ≫ x` using `Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Establish `ey : y₀ = ρ₀ ≫ y` using `Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))`. Rewrite using `[ex, ey, ← MonObj.comp_mul]`. Conclude with `(Category.id_comp _).trans (Category.comp_id _).symm`.

Conclude with `GlobalTheory.ThetaAffineGlue.lbIso_pull_id P.isLB`.
-/
theorem GlobalTheory.ThetaSBasis.exists_real_of_secBasis : ∀ (o Ω : Type) [CommRing o] [Field Ω] [Algebra o Ω] [ArithBase o Ω] (R : Subalgebra o Ω), R.FG → (∀ x : Ω, ∃ a ∈ R, ∃ b ∈ R, x = a / b) → ∀ (P : PolAV (Sp R)) (n k j : ℕ) (ze : oˣ), n.Prime → Odd n → 2 ≤ k → 1 ≤ j → IsUnit (n : o) → HypS P.A P.L → ∀ (th : LB.Sec (LPow P.A P.L 1 (baseOver (Sp R)))), IsSecBasis _ (fun _ : Fin 1 => th) → ∀ lev : Out.Level P ((n ^ j * (n ^ k) ^ 2) ^ 2) (unitOn (Units.map (algebraMap o R).toMonoidHom ze)), ∃ (S : ThetaSys o Ω) (ρ : S.Real) (h : R ≤ S.R) (φ : ρ.P.A.left ⟶ P.A.left), S.R = R ∧ ρ.n = n ∧ S.ζ = ze ∧ S.N = (n ^ k) ^ 2 ∧ S.r = n ^ j ∧ S.g = P.g ∧ IsGrpPullback ρ.P.A P.A (spMap (Subalgebra.inclusion h).toRingHom) φ ∧ LBIso ρ.P.L (P.L.pull φ) := by
  intro o Ω _ _ _ _ R fg frac P n k j ze hp ho hk hj hu hS th hth lev
  obtain ⟨hL, hL₂⟩ := GlobalTheory.abelianSchemeLaws_all
  have hgen : IsGenSec P.A P.L 1 th := isGenSec_of_isSecBasis P hth
  haveI := isNoetherian_of_fg fg
  haveI : IsAffine (baseOver (Sp R)).left := inferInstanceAs (IsAffine (Sp R))
  have hn2 : 2 ≤ n := hp.two_le
  have hn1 : 1 ≤ n := by omega
  have hm1 : 1 ≤ n ^ k := Nat.one_le_pow _ _ hn1
  have hr1 : 1 ≤ n ^ j := Nat.one_le_pow _ _ hn1
  haveI : NeZero (n ^ k) := ⟨by omega⟩
  have hN2 : 2 ≤ (n ^ k) ^ 2 := by
    have : n ^ 1 ≤ n ^ k := Nat.pow_le_pow_right hn1 (by omega)
    nlinarith
  have hM : n ^ j * (n ^ k) ^ 2 = n ^ (j + 2 * k) := by ring
  have hM1 : 1 ≤ n ^ j * (n ^ k) ^ 2 := hM ▸ Nat.one_le_pow _ _ hn1
  have hMo : Odd (n ^ j * (n ^ k) ^ 2) := hM ▸ ho.pow
  let f : o →+* Γ((baseOver (Sp R)).left, ⊤) := (Scheme.ΓSpecIso (CommRingCat.of R)).inv.hom.comp (algebraMap o R)
  have hf : Function.Injective f := fn_injective.comp (algebraMap_injective R)
  haveI : Nontrivial Γ((baseOver (Sp R)).left, ⊤) := (fn_injective (R := R)).nontrivial
  have un : ∀ q e : ℕ, q = n ^ e → IsUnit (q : Γ(Sp R, ⊤)) := fun q e hq => by
    have := (hu.pow e).map f
    rw [map_pow, map_natCast] at this
    rw [hq, Nat.cast_pow]
    exact this
  have prim : IsPrimitiveRoot (ze : o) ((n ^ j * (n ^ k) ^ 2) ^ 2) := (prim_iff R ze _).1 lev.prim
  obtain ⟨pt, hadd, hbij, hweil, hdiv, -⟩ := GlobalTheory.T.exists_torsionPoints_of_squareLevel_alt hL _ P _ _ hM1 (un _ _ hM) lev
  obtain ⟨h0, hsm⟩ := pt_nsmul pt hadd
  obtain ⟨rig, hrig⟩ := P.rigid
  have hfr : ∀ a, ∃ τ, IsTorsFrame P rig (n ^ j * (n ^ k) ^ 2) (pt a) τ := fun a => by
    obtain ⟨y, hy, e⟩ := hdiv a
    obtain ⟨θ, hθ⟩ := GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ hMo.pow (un _ ((j + 2 * k) * 2) (by rw [hM, pow_mul])) _ y hy
    exact GlobalTheory.T.exists_isTorsFrame_of_symLift' hL _ P rig hrig _ hMo _ y _ hy e θ hθ
  choose fr hfr using hfr
  have tors : ∀ a, pt (n ^ j • a) ^ ((n ^ k) ^ 2) = 1 := fun a => by
    rw [← hsm, smul_smul, mul_comm ((n ^ k) ^ 2) (n ^ j), nsmul_self, h0]
  choose U hU using fun a => GlobalTheory.T.exists_symLift_of_pow_eq_one hL _ P _ ho.pow.pow (un _ (k * 2) (pow_mul _ _ _).symm) _ _ (tors a)
  obtain ⟨α, hα, hαn⟩ := GlobalTheory.T.exists_normalised_mulPull_iso_origin hL _ P rig hrig (n ^ k) _ rfl (baseOver (Sp R))
  obtain ⟨s₀, hs₀⟩ := VVRank.exists_isTwistPull P.A (ψ := mulT P.A (baseOver (Sp R)) (n ^ k)) (hm := lift_snd _ _)
    (b := 1) P.isLB hα th
  obtain ⟨u, u₁, u₂, u₃, u₄, u₅⟩ := exists_operators hL P rfl ho.pow (un _ _ hM) _ pt hadd hweil U hU hα hs₀
  have hspan := GlobalTheory.ThetaSpan.span_translates_mulPull_of_isGenSec hL hL₂ R P (n ^ k) _ rfl hm1 (un _ _ rfl) th hgen
    α hα s₀ hs₀ _ U
    (fun a => SecM.toSec P.A (u a (SecM.ofSec P.A s₀))) (fun K _ _ x z hz => by
      obtain ⟨a, ha, uniq⟩ := hbij K x z (by rw [mul_comm, pow_mul, hz, one_pow])
      obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
      have e : (n ^ k) ^ 2 • a = 0 := (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, ha, hz])).trans
        (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm
      obtain ⟨c, rfl⟩ := exists_nsmul_eq hM1 a e
      exact ⟨c, by rw [(hU c).pt_eq, ha]⟩) (fun a => (u₁ _ _ _).2 rfl)
  obtain ⟨J, _, ρ, s, i₀, hcard, hi₀, ρ₁, ρ₂, ρ₃, ρ₄, ρ₅⟩ := exists_monomial_matrices_of_indep o _ _ f hf P.g (n ^ k)
    (n ^ j) _ rfl hm1 hr1 ze _ (Nat.one_le_pow _ _ hM1) prim.pow_eq_one u (SecM.ofSec P.A s₀) u₂
    (fun a b => (u₃ a b).imp fun e he v => (he v).trans (congrArg (· • _) (map_pow f _ _).symm)) u₄ u₅ hspan
    (fun t ht => linearIndependent_of_span hL₂.secBaseChangeAny P ((n ^ k) ^ 2) (by omega) t (by
      simp only [Fintype.card_fun, ZMod.card, Fintype.card_sum, Fintype.card_fin]
      ring) ht)
  choose v hv using fun a => ThetaPtExist.exists_isValueAt P.isLB th (pt a) (fr a) (hfr a).2.1
  choose w hw using fun a i => (hL.evVal _ P ((n ^ k) ^ 2) (pt a) (fr a) (hfr a).2.1 (SecM.toSec P.A (s i))).exists
  let ev : Γ((baseOver (Sp R)).left, ⊤) → R := (Scheme.ΓSpecIso (CommRingCat.of R)).hom.hom
  have good : ∀ a, ∃ y, n • y = 0 ∧ a + y ∈ {a | (ev (v a) : Ω) ≠ 0} := fun a => by
    let K := AlgebraicClosure Ω
    let x : Sp K ⟶ Sp R := spMap ((algebraMap Ω K).comp R.val.toRingHom)
    have := ArithBase.char (o := o) (Ω := Ω)
    obtain ⟨y, hy, H⟩ := GlobalTheory.ThetaSBasis.exists_good_translate hL hL₂ P K x n hn2 (Nat.cast_ne_zero.2 (by omega)) th
      hgen ((Over.homMk x (by simp) : Over.mk x ⟶ baseOver (Sp R)) ≫ pt a)
    obtain ⟨c, hc, -⟩ := hbij K x y (by rw [hM, show j + 2 * k = (j + 2 * k - 1) + 1 by omega, pow_succ', pow_mul, hy,
      one_pow])
    obtain ⟨a₀, -, uniq₀⟩ := hbij K x 1 (one_pow _)
    refine ⟨c, (uniq₀ _ (by beta_reduce; rw [hsm, MonObj.comp_pow, hc, hy])).trans
      (uniq₀ _ (by beta_reduce; rw [h0, MonObj.comp_one])).symm, fun e => ?_⟩
    refine H (pt (a + c)) (fr _) (v _) (by rw [hadd, MonObj.comp_mul, hc]) (hfr _).2.1 (hv _) ?_
    have e' : ev (v (a + c)) = 0 := Subtype.ext e
    exact (fn_hom _).symm.trans ((congrArg fn e').trans (map_zero _))
  let S : ThetaSys o Ω :=
    { g := P.g, N := (n ^ k) ^ 2, r := n ^ j, N_ge := hN2, r_pos := hr1, ζ := ze, prim := prim
      unit := by rw [hM, Nat.cast_pow]; exact hu.pow _
      J := J, ne := ⟨i₀⟩, ρ := ρ, ρ_one := ρ₁, ρ_mul := ρ₂, ρ_add := ρ₃
      th := fun a => ev (v a), ev := fun a i => ev (w a i), R := R, fg := fg, frac := frac
      th_mem := fun a => (ev (v a)).2, ev_mem := fun a i => (ev (w a i)).2
      supp := GlobalTheory.T.closure_zmodPow_eq_top_of_meets_torsion_cosets _ n (j + 2 * k) _ hn1 (by omega) hM _ good
      th_ne := by
        obtain ⟨y, -, hy⟩ := good 0
        exact ⟨_, hy⟩ }
  let ρ' : S.Real :=
    { P := P, g_eq := rfl, hypS := hS, n := n, n_prime := hp, n_odd := ho, k := k, two_le := hk, N_eq := rfl
      r_eq := ⟨j, hj, rfl⟩, card := hcard, pt := pt, pt_add := hadd, pt_bij := hbij
      weil := fun a b c hc => by
        have e : unitOn c = unitOn (Units.map (algebraMap o R).toMonoidHom ze) ^
            (n ^ j * (n ^ k) ^ 2 * (eStd P.g _ a b).val) := Units.ext
          ((congrArg fn hc).trans ((map_pow f _ _).trans (Units.val_pow_eq_pow_val (unitOn (Units.map (algebraMap o R).toMonoidHom ze)) _).symm))
        rw [e]
        exact hweil a b
      rig := rig, rig_gen := hrig, th₁ := th
      th₁_basis := hth
      fr := fr, fr_tors := hfr
      th_val := fun a => (fn_hom (v a)).symm ▸ hv a
      s := fun i => SecM.toSec P.A (s i)
      s_basis := existsUnique_of_basis s
      ev_val := fun i a => (congrArg (IsValueAt _ _ _ _ _ _) (fn_hom (w a i))).mpr (hw a i)
      i₀ := i₀, α := α, α_gen := hα, α_norm := hαn
      s_zero := by
        have e : SecM.toSec P.A (s i₀) = s₀ := by rw [hi₀]; rfl
        exact e ▸ hs₀
      U := U, U_sym := hU
      U_act := fun a i σ H => (sum_iff σ s _).2 (((u₁ _ _ _).1 H).symm.trans (ρ₄ a i))
      orbit := ρ₅ }
  have eid : spMap (Subalgebra.inclusion (le_refl R)).toRingHom = 𝟙 (Sp R) := by
    rw [Subalgebra.inclusion_self]
    exact Spec.map_id _
  refine ⟨S, ρ', le_refl R, 𝟙 _, rfl, rfl, rfl, rfl, rfl, rfl, ?_, ?_⟩
  · show IsGrpPullback P.A P.A (spMap (Subalgebra.inclusion (le_refl R)).toRingHom) (𝟙 P.A.left)
    rw [eid]
    refine ⟨IsPullback.of_horiz_isIso ⟨by simp⟩, fun T x y x₀ y₀ hx hy => ?_⟩
    let ρ₀ : Over.mk (T.hom ≫ 𝟙 (Sp R)) ⟶ T := Over.homMk (𝟙 T.left) (by simp)
    have ex : x₀ = ρ₀ ≫ x := Over.OverMorphism.ext (hx.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    have ey : y₀ = ρ₀ ≫ y := Over.OverMorphism.ext (hy.trans ((Category.comp_id _).trans (Category.id_comp _).symm))
    rw [ex, ey, ← MonObj.comp_mul]
    exact (Category.id_comp _).trans (Category.comp_id _).symm
  · exact GlobalTheory.ThetaAffineGlue.lbIso_pull_id P.isLB
