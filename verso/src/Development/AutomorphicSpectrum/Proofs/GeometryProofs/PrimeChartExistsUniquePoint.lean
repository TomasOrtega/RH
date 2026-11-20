import Mathlib
import Development.AutomorphicSpectrum.Definitions.GlobalGeometry.CoordsAt

open AlgebraicGeometry CategoryTheory Limits MonoidalCategory CartesianMonoidalCategory MonObj GlobalTheory.CompanionTheory.Ar

noncomputable section

namespace GlobalTheory.CompanionTheory.Ar.ChartPrimes

variable {X : Scheme.{0}} {Ω : Type} [Field Ω]

def secVal (ξ : Spec (CommRingCat.of Ω) ⟶ X) (V : X.Opens) (hg : genPt ξ ∈ V) : Γ(X, V) →+* Ω :=
  (Scheme.stalkClosedPointTo ξ).hom.comp (X.presheaf.germ V (genPt ξ) hg).hom

variable {ξ : Spec (CommRingCat.of Ω) ⟶ X}

/- English proof (translation)
Express the relevant statement in the definitionally equal form `_ = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f)`. Rewrite using `[← X.presheaf.germ_stalkSpecializes hp p.2]`. Both sides reduce to the same expression.
-/
theorem genMap_germ_eq (V : X.Opens) (hg : genPt ξ ∈ V) (p : Cpt ξ) (hp : p.1 ∈ V) (f : Γ(X, V)) :
    genMap ξ p (X.presheaf.germ V p.1 hp f) = secVal ξ V hg f := by
  change _ = (Scheme.stalkClosedPointTo ξ).hom (X.presheaf.germ V (genPt ξ) hg f)
  rw [← X.presheaf.germ_stalkSpecializes hp p.2]
  rfl

/- English proof (translation)
Prove the components needed by the constructor for the conclusion. Introduce `h`. Establish `h1 : IsUnit (genMap ξ p s)` using `h.map (genMap ξ p)`. Use `⟨h1.ne_zero, ⟨s, rfl⟩, ?_⟩` and prove the remaining obligations. Take `⟨u, rfl⟩` from `h`.

Use `⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ), ?_⟩` and prove the remaining obligations. Use `eq_inv_of_mul_eq_one_left ?_` and prove the remaining obligations. Rewrite using `[← map_mul]`. Simplify using the standard rewrite rules. Introduce and unpack `⟨h0, -, ⟨w, hw⟩⟩`.

Use `IsUnit.of_mul_eq_one w (hinj ?_)` and prove the remaining obligations. Rewrite using `[map_mul, hw, map_one]`. Conclude with `mul_inv_cancel₀ h0`.
-/
theorem isUnit_iff_unitAt (p : Cpt ξ) (hinj : Function.Injective (genMap ξ p))
    (s : X.presheaf.stalk p.1) : IsUnit s ↔ unitAt ξ p (genMap ξ p s) := by
  constructor
  · intro h
    have h1 : IsUnit (genMap ξ p s) := h.map (genMap ξ p)
    refine ⟨h1.ne_zero, ⟨s, rfl⟩, ?_⟩
    obtain ⟨u, rfl⟩ := h
    refine ⟨(u⁻¹ : (X.presheaf.stalk p.1)ˣ), ?_⟩
    refine eq_inv_of_mul_eq_one_left ?_
    rw [← map_mul]
    simp
  · rintro ⟨h0, -, ⟨w, hw⟩⟩
    refine IsUnit.of_mul_eq_one w (hinj ?_)
    rw [map_mul, hw, map_one]
    exact mul_inv_cancel₀ h0

/- English proof (translation)
Express the relevant statement in the definitionally equal form `hU.fromSpec y ∈ (U : Set X)`. Rewrite using `[← hU.range_fromSpec]`. Conclude with `⟨y, rfl⟩`.
-/
theorem fromSpec_mem {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U)) :
    hU.fromSpec y ∈ U := by
  change hU.fromSpec y ∈ (U : Set X)
  rw [← hU.range_fromSpec]
  exact ⟨y, rfl⟩

/- English proof (translation)
Set `ρ` to `secVal ξ U hg`. Set `I : Ideal Γ(X, U)` to `{ carrier := {r | ∃ f, ρ f = ρ r * a} add_mem' := by`. Introduce and unpack `r s ⟨f, hf⟩ ⟨g, hg⟩`. Conclude with `⟨f + g, by rw [map_add, map_add, hf, hg, add_mul]⟩`. Use the proof step `zero_mem' := ⟨0, by simp⟩`.

Use the proof step `smul_mem' := by`. Introduce and unpack `r s ⟨f, hf⟩`. Conclude with `⟨r * f, by rw [smul_eq_mul, map_mul, map_mul, hf, _root_.mul_assoc]⟩ }`. Distinguish the cases in `hI : I = ⊤`. Take `⟨f, hf⟩ : (1 : Γ(X, U)) ∈ I` from `hI ▸ Submodule.mem_top`.

Conclude with `⟨f, by rw [hf, map_one, _root_.one_mul]⟩`. It suffices to derive a contradiction. Take `⟨m, hm, hIm⟩` from `Ideal.exists_le_maximal I hI`. Set `q : PrimeSpectrum Γ(X, U)` to `⟨m, hm.isPrime⟩`. Establish `hq : hU.fromSpec q ∈ U` using `fromSpec_mem hU q`.

Establish `hsp` using `hs _ hq`. Take `⟨σ, hσ⟩` from `ha _ hsp hq`. Establish `hloc` using `hU.isLocalization_stalk' q hq`. Take `⟨⟨r, s⟩, e⟩` from `@IsLocalization.surj _ _ _ _ _ (X.presheaf.algebra_section_stalk ⟨hU.fromSpec q, hq⟩) hloc σ`. Establish `e' : σ * X.presheaf.germ U _ hq s.1 = X.presheaf.germ U _ hq r` using `e`.

Establish `e2` using `congrArg (genMap ξ ⟨_, hsp⟩) e'`. Rewrite `e2` using `[map_mul, hσ, genMap_germ_eq U hg ⟨_, hsp⟩ hq s.1, genMap_germ_eq U hg ⟨_, hsp⟩ hq r]`. Conclude with `s.2 (hIm ⟨r, by rw [← e2, mul_comm]⟩)`.
-/
theorem exists_secVal_eq {U : X.Opens} (hU : IsAffineOpen U) (hg : genPt ξ ∈ U)
    (hs : ∀ q ∈ U, genPt ξ ⤳ q) (a : Ω)
    (ha : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → a ∈ regAt ξ ⟨q, h⟩) :
    ∃ f : Γ(X, U), secVal ξ U hg f = a := by
  let ρ := secVal ξ U hg
  let I : Ideal Γ(X, U) :=
    { carrier := {r | ∃ f, ρ f = ρ r * a}
      add_mem' := by
        rintro r s ⟨f, hf⟩ ⟨g, hg⟩
        exact ⟨f + g, by rw [map_add, map_add, hf, hg, add_mul]⟩
      zero_mem' := ⟨0, by simp⟩
      smul_mem' := by
        rintro r s ⟨f, hf⟩
        exact ⟨r * f, by rw [smul_eq_mul, map_mul, map_mul, hf, _root_.mul_assoc]⟩ }
  by_cases hI : I = ⊤
  · obtain ⟨f, hf⟩ : (1 : Γ(X, U)) ∈ I := hI ▸ Submodule.mem_top
    exact ⟨f, by rw [hf, map_one, _root_.one_mul]⟩
  · exfalso
    obtain ⟨m, hm, hIm⟩ := Ideal.exists_le_maximal I hI
    let q : PrimeSpectrum Γ(X, U) := ⟨m, hm.isPrime⟩
    have hq : hU.fromSpec q ∈ U := fromSpec_mem hU q
    have hsp := hs _ hq
    obtain ⟨σ, hσ⟩ := ha _ hsp hq
    have hloc := hU.isLocalization_stalk' q hq
    obtain ⟨⟨r, s⟩, e⟩ := @IsLocalization.surj _ _ _ _ _
      (X.presheaf.algebra_section_stalk ⟨hU.fromSpec q, hq⟩) hloc σ
    have e' : σ * X.presheaf.germ U _ hq s.1 = X.presheaf.germ U _ hq r := e
    have e2 := congrArg (genMap ξ ⟨_, hsp⟩) e'
    rw [map_mul, hσ, genMap_germ_eq U hg ⟨_, hsp⟩ hq s.1, genMap_germ_eq U hg ⟨_, hsp⟩ hq r] at e2
    exact s.2 (hIm ⟨r, by rw [← e2, mul_comm]⟩)

/- English proof (translation)
Rewrite using `[← X.mem_basicOpen f _ hq, ← PrimeSpectrum.mem_basicOpen]`. Establish `h` using `hU.fromSpec_preimage_basicOpen f`. Express the relevant statement in the definitionally equal form `_ ↔ y ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)`. Rewrite using `[h]`. Both sides reduce to the same expression.
-/
theorem notMem_iff_isUnit_germ {U : X.Opens} (hU : IsAffineOpen U) (y : PrimeSpectrum Γ(X, U))
    (hq : hU.fromSpec y ∈ U) (f : Γ(X, U)) :
    f ∉ y.asIdeal ↔ IsUnit (X.presheaf.germ U (hU.fromSpec y) hq f) := by
  rw [← X.mem_basicOpen f _ hq, ← PrimeSpectrum.mem_basicOpen]
  have h := hU.fromSpec_preimage_basicOpen f
  change _ ↔ y ∈ (hU.fromSpec ⁻¹ᵁ X.basicOpen f)
  rw [h]
  rfl

/- English proof (translation)
Use `⟨hc, fun j => ?_⟩` and prove the remaining obligations. Take `⟨s, hs⟩` from `hξ.bij.2 (x j / x c)`. Use `⟨s, ?_⟩` and prove the remaining obligations. Rewrite using `[← hs]`. Simplify using `only [genMap, TopCat.Presheaf.stalkSpecializes_refl]`.

Both sides reduce to the same expression.
-/
theorem inChart_genPt (hξ : IsCptGen ξ) {κ : Type} (x : κ → Ω) (c : κ) (hc : x c ≠ 0) :
    InChart ξ x c ⟨genPt ξ, specializes_rfl⟩ := by
  refine ⟨hc, fun j => ?_⟩
  obtain ⟨s, hs⟩ := hξ.bij.2 (x j / x c)
  refine ⟨s, ?_⟩
  rw [← hs]
  simp only [genMap, TopCat.Presheaf.stalkSpecializes_refl]
  rfl

end GlobalTheory.CompanionTheory.Ar.ChartPrimes

namespace GlobalTheory.CompanionTheory.Ar

open ChartPrimes in

/- English proof (translation)
Introduce `X Ω _ ξ o _ _ κ x T c hc I hI`. Take `⟨U, hU, hmem⟩` from `T.affine c hc`. Establish `hg : genPt ξ ∈ U` using `(hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩`. Establish `hs : ∀ q ∈ U, genPt ξ ⤳ q` using `fun q hq => by`. Take `⟨h, -⟩` from `(hmem q).1 hq`.

Conclude with `h`. Establish `hin : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → InChart ξ x c ⟨q, h⟩` using `fun q h hq => by`. Take `⟨_, h'⟩` from `(hmem q).1 hq`. Conclude with `h'`. Set `ρ` to `secVal ξ U hg`.

Establish `hρA : ∀ f, ρ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c)` using `fun f => (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq U hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩`. Establish `hsurj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∃ f, ρ f = a` using `fun a ha => exists_secVal_eq hU hg hs a fun q h hq => (T.ring c hc a).1 ha _ (hin q h hq)`. Set `ρ' : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c)` to `ρ.codRestrict _ hρA`. Establish `hρ' : ∀ f, ((ρ' f : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ρ f` using `fun _ => rfl`. Establish `key : ∀ (y : PrimeSpectrum Γ(X, U)) (h : genPt ξ ⤳ hU.fromSpec y) (f : Γ(X, U)), f ∉ y.asIdeal ↔ unitAt ξ ⟨hU.fromSpec y, h⟩ (ρ f)` using `fun y h f => by`.

Establish `hq` using `fromSpec_mem hU y`. Rewrite using `[notMem_iff_isUnit_germ hU y hq f, ← genMap_germ_eq U hg ⟨_, h⟩ hq f]`. Conclude with `isUnit_iff_unitAt ⟨_, h⟩ (T.gen.inj _) _`. Set `y : PrimeSpectrum Γ(X, U)` to `⟨I.comap ρ', inferInstance⟩`. Establish `hy` using `fromSpec_mem hU y`.

Use `⟨⟨hU.fromSpec y, hs _ hy⟩, ⟨hin _ _ hy, fun s => ?_⟩, ?_⟩` and prove the remaining obligations. Take `⟨f, hf⟩` from `hsurj s s.2`. Establish `hfs : ρ' f = s` using `Subtype.ext hf`. Use `key y (hs _ hy) f` as an intermediate fact. Rewrite `this` using `[hf]`.

Rewrite using `[← this, ← hfs]`. Both sides reduce to the same expression. Introduce and unpack `⟨p, hp⟩ ⟨hpc, hpI⟩`. Establish `hpU : p ∈ U` using `(hmem p).2 ⟨hp, hpc⟩`. Take `⟨y', rfl⟩ : ∃ y', hU.fromSpec y' = p` from `⟨_, hU.fromSpec_primeIdealOf ⟨p, hpU⟩⟩`.

Establish `hyy : y' = y` using `PrimeSpectrum.ext (Ideal.ext fun f => not_iff_not.1 ((key y' hp f).trans (hpI (ρ' f)).symm))`. Conclude with `Subtype.ext (congrArg (fun t => hU.fromSpec t) hyy)`.
-/
theorem chart_point_of_prime : ∀ (X : Scheme.{0}) (Ω : Type) [Field Ω] (ξ : Spec (CommRingCat.of Ω) ⟶ X) (o : Type)
    [CommRing o] [Algebra o Ω] (κ : Type) (x : κ → Ω), CoordTie o ξ x → ∀ (c : κ), x c ≠ 0 →
    ∀ I : Ideal (Algebra.adjoin o (Set.range fun j => x j / x c)), I.IsPrime →
    ∃! p : Cpt ξ, InChart ξ x c p ∧ ∀ s : Algebra.adjoin o (Set.range fun j => x j / x c),
      s ∉ I ↔ unitAt ξ p (s : Ω) := by
  intro X Ω _ ξ o _ _ κ x T c hc I hI
  obtain ⟨U, hU, hmem⟩ := T.affine c hc
  have hg : genPt ξ ∈ U := (hmem _).2 ⟨specializes_rfl, inChart_genPt T.gen x c hc⟩
  have hs : ∀ q ∈ U, genPt ξ ⤳ q := fun q hq => by
    obtain ⟨h, -⟩ := (hmem q).1 hq
    exact h
  have hin : ∀ (q : X) (h : genPt ξ ⤳ q), q ∈ U → InChart ξ x c ⟨q, h⟩ := fun q h hq => by
    obtain ⟨_, h'⟩ := (hmem q).1 hq
    exact h'
  let ρ := secVal ξ U hg
  have hρA : ∀ f, ρ f ∈ Algebra.adjoin o (Set.range fun j => x j / x c) := fun f =>
    (T.ring c hc _).2 fun p hp => ⟨_, genMap_germ_eq U hg p ((hmem _).2 ⟨p.2, hp⟩) f⟩
  have hsurj : ∀ a ∈ Algebra.adjoin o (Set.range fun j => x j / x c), ∃ f, ρ f = a := fun a ha =>
    exists_secVal_eq hU hg hs a fun q h hq => (T.ring c hc a).1 ha _ (hin q h hq)
  let ρ' : Γ(X, U) →+* Algebra.adjoin o (Set.range fun j => x j / x c) := ρ.codRestrict _ hρA
  have hρ' : ∀ f, ((ρ' f : Algebra.adjoin o (Set.range fun j => x j / x c)) : Ω) = ρ f := fun _ => rfl

  have key : ∀ (y : PrimeSpectrum Γ(X, U)) (h : genPt ξ ⤳ hU.fromSpec y) (f : Γ(X, U)),
      f ∉ y.asIdeal ↔ unitAt ξ ⟨hU.fromSpec y, h⟩ (ρ f) := fun y h f => by
    have hq := fromSpec_mem hU y
    rw [notMem_iff_isUnit_germ hU y hq f, ← genMap_germ_eq U hg ⟨_, h⟩ hq f]
    exact isUnit_iff_unitAt ⟨_, h⟩ (T.gen.inj _) _
  let y : PrimeSpectrum Γ(X, U) := ⟨I.comap ρ', inferInstance⟩
  have hy := fromSpec_mem hU y
  refine ⟨⟨hU.fromSpec y, hs _ hy⟩, ⟨hin _ _ hy, fun s => ?_⟩, ?_⟩
  · obtain ⟨f, hf⟩ := hsurj s s.2
    have hfs : ρ' f = s := Subtype.ext hf
    have := key y (hs _ hy) f
    rw [hf] at this
    rw [← this, ← hfs]
    rfl
  · rintro ⟨p, hp⟩ ⟨hpc, hpI⟩
    have hpU : p ∈ U := (hmem p).2 ⟨hp, hpc⟩
    obtain ⟨y', rfl⟩ : ∃ y', hU.fromSpec y' = p := ⟨_, hU.fromSpec_primeIdealOf ⟨p, hpU⟩⟩
    have hyy : y' = y := PrimeSpectrum.ext (Ideal.ext fun f => not_iff_not.1 ((key y' hp f).trans (hpI (ρ' f)).symm))
    exact Subtype.ext (congrArg (fun t => hU.fromSpec t) hyy)

end GlobalTheory.CompanionTheory.Ar
