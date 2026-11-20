import Mathlib

open Polynomial IsLocalRing

namespace GlobalTheory.CompanionTheory.Chevalley

variable {Ω L : Type*} [Field Ω] [Field L]

def Functional (G : Subring (Ω × L)) : Prop := ∀ l : L, ((0 : Ω), l) ∈ G → l = 0

/- English proof (translation)
Establish `hub : ∀ c ⊆ {G : Subring (Ω × L) | Functional G}, IsChain (· ≤ ·) c → ∀ y ∈ c, ∃ ub ∈ {G : Subring (Ω × L) | Functional G}, ∀ z ∈ c, z ≤ ub`. Introduce `c hc hch y hy`. Use `⟨sSup c, ?_, fun z hz => le_sSup hz⟩` and prove the remaining obligations. Use `show Functional (sSup c)`. Introduce `l hl`.

Take `⟨s, hs, hls⟩` from `(Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hl`. Conclude with `(hc hs : Functional s) l hls`. Take `⟨m, hm, hmax⟩` from `zorn_le_nonempty₀ _ hub G₀ h₀`. Conclude with `⟨m, hm, hmax⟩`.
-/
theorem exists_maximal_functional (G₀ : Subring (Ω × L)) (h₀ : Functional G₀) :
    ∃ G, G₀ ≤ G ∧ Maximal Functional G := by
  have hub : ∀ c ⊆ {G : Subring (Ω × L) | Functional G}, IsChain (· ≤ ·) c → ∀ y ∈ c,
      ∃ ub ∈ {G : Subring (Ω × L) | Functional G}, ∀ z ∈ c, z ≤ ub := by
    intro c hc hch y hy
    refine ⟨sSup c, ?_, fun z hz => le_sSup hz⟩
    show Functional (sSup c)
    intro l hl
    obtain ⟨s, hs, hls⟩ := (Subring.mem_sSup_of_directedOn ⟨y, hy⟩ hch.directedOn).mp hl
    exact (hc hs : Functional s) l hls
  obtain ⟨m, hm, hmax⟩ := zorn_le_nonempty₀ _ hub G₀ h₀
  exact ⟨m, hm, hmax⟩

def saturation (G : Subring (Ω × L)) (t : Ω × L) (ht : t ∈ G) : Subring (Ω × L) where
  carrier := {u | ∃ n : ℕ, t ^ n * u ∈ G}
  mul_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.mul_mem hn hm
    convert this using 1
    ring
  one_mem' := ⟨0, by simpa using G.one_mem⟩
  add_mem' := by
    rintro u v ⟨n, hn⟩ ⟨m, hm⟩
    refine ⟨n + m, ?_⟩
    have := G.add_mem (G.mul_mem (G.pow_mem ht m) hn) (G.mul_mem (G.pow_mem ht n) hm)
    convert this using 1
    ring
  zero_mem' := ⟨0, by simp [G.zero_mem]⟩
  neg_mem' := by
    rintro u ⟨n, hn⟩
    exact ⟨n, by simpa using G.neg_mem hn⟩

/- English proof (translation)
Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hl (hG.1 l hb)`. Establish `hmem : ∀ u, u ∈ saturation G (b, l) hb ↔ ∃ n : ℕ, (b, l) ^ n * u ∈ G` using `fun u => Iff.rfl`. Establish `hS : Functional (saturation G (b, l) hb)`.

Introduce `m hm`. Take `⟨n, hn⟩` from `(hmem _).mp hm`. Rewrite `hn` using `[Prod.pow_mk, Prod.mk_mul_mk, mul_zero]`. Establish `h0` using `hG.1 _ hn`. Conclude with `(mul_eq_zero.mp h0).resolve_left (pow_ne_zero n hl)`.

Establish `hle : G ≤ saturation G (b, l) hb` using `fun u hu => (hmem u).mpr ⟨0, by simpa using hu⟩`. Apply `hG.2 hS hle` to reduce the goal to its premises. Use `(hmem _).mpr ⟨1, ?_⟩` and prove the remaining obligations. Rewrite using `[pow_one, Prod.mk_mul_mk, mul_inv_cancel₀ hb0, mul_inv_cancel₀ hl]`. Conclude with `G.one_mem`.
-/
theorem inv_mem {G : Subring (Ω × L)} (hG : Maximal Functional G) {b : Ω} {l : L}
    (hb : (b, l) ∈ G) (hl : l ≠ 0) : (b⁻¹, l⁻¹) ∈ G := by
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hb)
  have hmem : ∀ u, u ∈ saturation G (b, l) hb ↔ ∃ n : ℕ, (b, l) ^ n * u ∈ G := fun u => Iff.rfl
  have hS : Functional (saturation G (b, l) hb) := by
    intro m hm
    obtain ⟨n, hn⟩ := (hmem _).mp hm
    rw [Prod.pow_mk, Prod.mk_mul_mk, mul_zero] at hn
    have h0 := hG.1 _ hn
    exact (mul_eq_zero.mp h0).resolve_left (pow_ne_zero n hl)
  have hle : G ≤ saturation G (b, l) hb := fun u hu => (hmem u).mpr ⟨0, by simpa using hu⟩
  apply hG.2 hS hle
  refine (hmem _).mpr ⟨1, ?_⟩
  rw [pow_one, Prod.mk_mul_mk, mul_inv_cancel₀ hb0, mul_inv_cancel₀ hl]
  exact G.one_mem

def p₁ (G : Subring (Ω × L)) : G →+* Ω := (RingHom.fst Ω L).comp G.subtype

def p₂ (G : Subring (Ω × L)) : G →+* L := (RingHom.snd Ω L).comp G.subtype

/- English proof (translation)
Take `⟨⟨b, l⟩, hr⟩` from `r`. Establish `hl : l ≠ 0` using `h`. Establish `hb0 : b ≠ 0`. Introduce and unpack `rfl`. Conclude with `hl (hG.1 l hr)`.

Establish `hinv` using `inv_mem hG hr hl`. Establish `hprod : (⟨(b, l), hr⟩ : G) * ⟨(b⁻¹, l⁻¹), hinv⟩ = 1`. Apply `Subtype.ext` to reduce the goal to its premises. Simplify using `[hb0, hl]`. Conclude with `⟨⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩`.
-/
theorem isUnit_of_p₂_ne_zero {G : Subring (Ω × L)} (hG : Maximal Functional G) (r : G)
    (h : p₂ G r ≠ 0) : IsUnit r := by
  obtain ⟨⟨b, l⟩, hr⟩ := r
  have hl : l ≠ 0 := h
  have hb0 : b ≠ 0 := by
    rintro rfl
    exact hl (hG.1 l hr)
  have hinv := inv_mem hG hr hl
  have hprod : (⟨(b, l), hr⟩ : G) * ⟨(b⁻¹, l⁻¹), hinv⟩ = 1 := by
    apply Subtype.ext
    simp [hb0, hl]
  exact ⟨⟨_, _, hprod, by rw [mul_comm]; exact hprod⟩, rfl⟩

/- English proof (translation)
Establish `: Nontrivial G` using `(p₂ G).domain_nontrivial`. Establish `key : ∀ r : G, r ∈ nonunits G ↔ p₂ G r = 0`. Introduce `r`. Rewrite using `[mem_nonunits_iff]`. Prove the components needed by the constructor for the conclusion.

Introduce `hr`. Assume the negation of the conclusion as `h`. Conclude with `hr (isUnit_of_p₂_ne_zero hG r h)`. Introduce `h hu`. Use `hu.map (p₂ G)` as an intermediate fact.

Rewrite `this` using `[h]`. Conclude with `not_isUnit_zero this`. Use `IsLocalRing.of_nonunits_add ?_` and prove the remaining obligations. Introduce `a b ha hb`. Rewrite `ha`, `hb`, the goal using `[key]`.

Rewrite using `[map_add, ha, hb, add_zero]`.
-/
theorem isLocalRing_of_maximal {G : Subring (Ω × L)} (hG : Maximal Functional G) :
    IsLocalRing G := by
  have : Nontrivial G := (p₂ G).domain_nontrivial
  have key : ∀ r : G, r ∈ nonunits G ↔ p₂ G r = 0 := by
    intro r
    rw [mem_nonunits_iff]
    constructor
    · intro hr
      by_contra h
      exact hr (isUnit_of_p₂_ne_zero hG r h)
    · intro h hu
      have := hu.map (p₂ G)
      rw [h] at this
      exact not_isUnit_zero this
  refine IsLocalRing.of_nonunits_add ?_
  intro a b ha hb
  rw [key] at ha hb ⊢
  rw [map_add, ha, hb, add_zero]

/- English proof (translation)
Establish `hmem : ∀ p, p ∈ I ↔ Submodule.IsPrincipal.generator I ∣ p` using `fun p => Submodule.IsPrincipal.mem_iff_generator_dvd I`. Distinguish the cases in `hf0 : Submodule.IsPrincipal.generator I = 0`. Use `⟨0, fun p hp => ?_⟩` and prove the remaining obligations. Rewrite `hp` using `[hmem, hf0, zero_dvd_iff]`. Rewrite using `[hp, eval₂_zero]`.

Establish `hnu : ¬ IsUnit (Submodule.IsPrincipal.generator I)`. Introduce `hu`. Apply `hI` to reduce the goal to its premises. Rewrite using `[Ideal.eq_top_iff_one, hmem]`. Conclude with `hu.dvd`.

Establish `hdeg : (Submodule.IsPrincipal.generator I).degree ≠ 0`. Introduce `h`. Conclude with `hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)`. Take `⟨ξ, hξ⟩` from `IsAlgClosed.exists_eval₂_eq_zero ι _ hdeg`. Use `⟨ξ, fun p hp => ?_⟩` and prove the remaining obligations.

Take `⟨q, rfl⟩` from `(hmem p).mp hp`. Rewrite using `[eval₂_mul, hξ, zero_mul]`.
-/
theorem exists_common_root [IsAlgClosed L] {k : Type*} [Field k] (ι : k →+* L) (I : Ideal k[X])
    (hI : I ≠ ⊤) : ∃ ξ : L, ∀ p ∈ I, eval₂ ι ξ p = 0 := by
  classical
  have hmem : ∀ p, p ∈ I ↔ Submodule.IsPrincipal.generator I ∣ p :=
    fun p => Submodule.IsPrincipal.mem_iff_generator_dvd I
  by_cases hf0 : Submodule.IsPrincipal.generator I = 0
  · refine ⟨0, fun p hp => ?_⟩
    rw [hmem, hf0, zero_dvd_iff] at hp
    rw [hp, eval₂_zero]
  · have hnu : ¬ IsUnit (Submodule.IsPrincipal.generator I) := by
      intro hu
      apply hI
      rw [Ideal.eq_top_iff_one, hmem]
      exact hu.dvd
    have hdeg : (Submodule.IsPrincipal.generator I).degree ≠ 0 := by
      intro h
      exact hnu (Polynomial.isUnit_iff_degree_eq_zero.mpr h)
    obtain ⟨ξ, hξ⟩ := IsAlgClosed.exists_eval₂_eq_zero ι _ hdeg
    refine ⟨ξ, fun p hp => ?_⟩
    obtain ⟨q, rfl⟩ := (hmem p).mp hp
    rw [eval₂_mul, hξ, zero_mul]

/- English proof (translation)
Establish `hfst : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).1 = eval₂ (p₁ G) x p` using `fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.fst Ω L) (x, ξ)`. Establish `hsnd : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).2 = eval₂ (p₂ G) ξ p` using `fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.snd Ω L) (x, ξ)`. Establish `hS : Functional (Polynomial.eval₂RingHom G.subtype (x, ξ)).range`. Introduce `l hl`. Take `⟨p, hp⟩` from `RingHom.mem_range.mp hl`.

Establish `hp' : eval₂ G.subtype (x, ξ) p = (0, l)` using `hp`. Establish `h1 : eval₂ (p₁ G) x p = 0`. Use `hfst p` as an intermediate fact. Rewrite `this` using `[hp']`. Conclude with `this.symm`.

Establish `h2` using `h p h1`. Use `hsnd p` as an intermediate fact. Rewrite `this` using `[hp']`. Conclude with `this.trans h2`. Establish `hle : G ≤ (Polynomial.eval₂RingHom G.subtype (x, ξ)).range`.

Introduce `t ht`. Conclude with `RingHom.mem_range.mpr ⟨C ⟨t, ht⟩, by simp⟩`. Conclude with `hG.2 hS hle (RingHom.mem_range.mpr ⟨X, by simp⟩)`.
-/
theorem mem_of_relations {G : Subring (Ω × L)} (hG : Maximal Functional G) (x : Ω) (ξ : L)
    (h : ∀ p : Polynomial G, eval₂ (p₁ G) x p = 0 → eval₂ (p₂ G) ξ p = 0) : (x, ξ) ∈ G := by
  have hfst : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).1 = eval₂ (p₁ G) x p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.fst Ω L) (x, ξ)
  have hsnd : ∀ p : Polynomial G, (eval₂ G.subtype (x, ξ) p).2 = eval₂ (p₂ G) ξ p :=
    fun p => Polynomial.hom_eval₂ p G.subtype (RingHom.snd Ω L) (x, ξ)
  have hS : Functional (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro l hl
    obtain ⟨p, hp⟩ := RingHom.mem_range.mp hl
    have hp' : eval₂ G.subtype (x, ξ) p = (0, l) := hp
    have h1 : eval₂ (p₁ G) x p = 0 := by
      have := hfst p
      rw [hp'] at this
      exact this.symm
    have h2 := h p h1
    have := hsnd p
    rw [hp'] at this
    exact this.trans h2
  have hle : G ≤ (Polynomial.eval₂RingHom G.subtype (x, ξ)).range := by
    intro t ht
    exact RingHom.mem_range.mpr ⟨C ⟨t, ht⟩, by simp⟩
  exact hG.2 hS hle (RingHom.mem_range.mpr ⟨X, by simp⟩)

/- English proof (translation)
Establish `hsurj : Function.Surjective (Polynomial.mapRingHom (IsLocalRing.residue G))` using `Polynomial.map_surjective _ IsLocalRing.residue_surjective`. Establish `hJ : Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G)) (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) ≠ ⊤`. Introduce `hJ`. Establish `h1 : (1 : Polynomial (IsLocalRing.ResidueField G)) ∈ Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G)) (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω)))`. Rewrite using `[hJ]`.

Conclude with `Submodule.mem_top`. Take `⟨p, hpI, hp1'⟩` from `(Ideal.mem_map_iff_of_surjective _ hsurj).mp h1`. Establish `hp : eval₂ (p₁ G) (x : Ω) p = 0`. Rewrite `hpI` using `[RingHom.mem_ker, Polynomial.coe_eval₂RingHom]`. Conclude with `hpI`.

Establish `hp1 : Polynomial.map (IsLocalRing.residue G) p = 1` using `hp1'`. Establish `hcomp : V.subtype.comp g = p₁ G` using `RingHom.ext hg`. Establish `h0 : eval₂ g x p = 0`. Apply `Subtype.val_injective` to reduce the goal to its premises. Use `Polynomial.hom_eval₂ p g V.subtype x` as an intermediate fact.

Rewrite `this` using `[hcomp]`. Conclude with `this.trans hp`. Establish `hc : (IsLocalRing.residue V).comp g = (IsLocalRing.ResidueField.map g).comp (IsLocalRing.residue G)`. Use extensionality with `r`. Simplify using the standard rewrite rules.

Establish `h2 : IsLocalRing.residue V (eval₂ g x p) = 1`. Rewrite using `[Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map, hp1, eval₂_one]`. Rewrite `h2` using `[h0, map_zero]`. Conclude with `zero_ne_one h2`. Take `⟨ξ, hξ⟩` from `exists_common_root (IsLocalRing.ResidueField.lift (p₂ G)) _ hJ`.

Use `⟨ξ, mem_of_relations hG (x : Ω) ξ fun p hp => ?_⟩` and prove the remaining obligations. Establish `hpI : p ∈ RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))`. Rewrite using `[RingHom.mem_ker, Polynomial.coe_eval₂RingHom]`. Conclude with `hp`. Use `hξ _ (Ideal.mem_map_of_mem _ hpI)` as an intermediate fact.

Rewrite `this` using `[Polynomial.coe_mapRingHom, Polynomial.eval₂_map, IsLocalRing.ResidueField.lift_comp_residue]`. Conclude with `this`.
-/
theorem exists_mem_of_dominates [IsAlgClosed L] {G : Subring (Ω × L)} (hG : Maximal Functional G)
    [IsLocalRing G] [IsLocalHom (p₂ G)] (V : ValuationSubring Ω) (g : G →+* V)
    (hg : ∀ r, (g r : Ω) = p₁ G r) [IsLocalHom g] (x : V) : ∃ ξ : L, ((x : Ω), ξ) ∈ G := by
  classical
  have hsurj : Function.Surjective (Polynomial.mapRingHom (IsLocalRing.residue G)) :=
    Polynomial.map_surjective _ IsLocalRing.residue_surjective
  have hJ : Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
      (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) ≠ ⊤ := by
    intro hJ
    have h1 : (1 : Polynomial (IsLocalRing.ResidueField G)) ∈ Ideal.map (Polynomial.mapRingHom (IsLocalRing.residue G))
        (RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω))) := by
      rw [hJ]
      exact Submodule.mem_top
    obtain ⟨p, hpI, hp1'⟩ := (Ideal.mem_map_iff_of_surjective _ hsurj).mp h1
    have hp : eval₂ (p₁ G) (x : Ω) p = 0 := by
      rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom] at hpI
      exact hpI
    have hp1 : Polynomial.map (IsLocalRing.residue G) p = 1 := hp1'
    have hcomp : V.subtype.comp g = p₁ G := RingHom.ext hg
    have h0 : eval₂ g x p = 0 := by
      apply Subtype.val_injective
      have := Polynomial.hom_eval₂ p g V.subtype x
      rw [hcomp] at this
      exact this.trans hp
    have hc : (IsLocalRing.residue V).comp g
        = (IsLocalRing.ResidueField.map g).comp (IsLocalRing.residue G) := by
      ext r
      simp
    have h2 : IsLocalRing.residue V (eval₂ g x p) = 1 := by
      rw [Polynomial.hom_eval₂, hc, ← Polynomial.eval₂_map, hp1, eval₂_one]
    rw [h0, map_zero] at h2
    exact zero_ne_one h2
  obtain ⟨ξ, hξ⟩ := exists_common_root (IsLocalRing.ResidueField.lift (p₂ G)) _ hJ
  refine ⟨ξ, mem_of_relations hG (x : Ω) ξ fun p hp => ?_⟩
  have hpI : p ∈ RingHom.ker (Polynomial.eval₂RingHom (p₁ G) (x : Ω)) := by
    rw [RingHom.mem_ker, Polynomial.coe_eval₂RingHom]
    exact hp
  have := hξ _ (Ideal.mem_map_of_mem _ hpI)
  rw [Polynomial.coe_mapRingHom, Polynomial.eval₂_map, IsLocalRing.ResidueField.lift_comp_residue] at this
  exact this

/- English proof (translation)
Establish `hG₀f : Functional (A.subtype.prod φ).range`. Introduce `l hl`. Take `⟨a, ha⟩` from `RingHom.mem_range.mp hl`. Establish `h1 : (a : Ω) = 0` using `congrArg Prod.fst ha`. Establish `h2 : φ a = l` using `congrArg Prod.snd ha`.

Establish `ha0 : a = 0` using `Subtype.ext h1`. Rewrite using `[← h2, ha0, map_zero]`. Take `⟨G, hG₀G, hG⟩` from `exists_maximal_functional _ hG₀f`. Establish `: IsLocalRing G` using `isLocalRing_of_maximal hG`. Establish `: IsLocalHom (p₂ G)` using `⟨fun r hr => isUnit_of_p₂_ne_zero hG r hr.ne_zero⟩`.

Establish `hinj : Function.Injective (p₁ G)`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce and unpack `⟨⟨b, l⟩, hr⟩ h0`. Establish `hb : b = 0` using `h0`. Substitute `hb` using the available equality.

Establish `hl` using `hG.1 l hr`. Substitute `hl` using the available equality. Both sides reduce to the same expression. Set `e : G ≃+* (p₁ G).range` to `RingEquiv.ofBijective (p₁ G).rangeRestrict ⟨fun r s h => hinj (congrArg Subtype.val h), (p₁ G).rangeRestrict_surjective⟩`. Establish `: IsLocalRing (p₁ G).range` using `IsLocalRing.of_surjective' (p₁ G).rangeRestrict (p₁ G).rangeRestrict_surjective`.

Take `⟨V, hV⟩` from `LocalSubring.exists_le_valuationSubring (LocalSubring.mk (p₁ G).range)`. Take `⟨hle, hloc⟩` from `LocalSubring.le_def.mp hV`. Establish `: IsLocalHom (p₁ G).rangeRestrict` using `IsLocalHom.of_surjective _ (p₁ G).rangeRestrict_surjective`. Set `g : G →+* V` to `(Subring.inclusion hle).comp (p₁ G).rangeRestrict`. Establish `: IsLocalHom g` using `⟨fun r hr => IsLocalHom.map_nonunit (f := (p₁ G).rangeRestrict) r (IsLocalHom.map_nonunit (f := Subring.inclusion hle) (self := hloc) ((p₁ G).rangeRestrict r) hr)⟩`.

Establish `hVle : ∀ x ∈ V, x ∈ (p₁ G).range`. Introduce `x hx`. Take `⟨ξ, hξ⟩` from `exists_mem_of_dominates hG V g (fun r => rfl) ⟨x, hx⟩`. Conclude with `RingHom.mem_range.mpr ⟨⟨(x, ξ), hξ⟩, rfl⟩`. Establish `hVle' : V.toSubring ≤ (p₁ G).range` using `fun x hx => hVle x hx`.

Establish `hmem0 : ∀ a : A, ((a : Ω), φ a) ∈ G` using `fun a => hG₀G (RingHom.mem_range.mpr ⟨a, rfl⟩)`. Establish `hAV : ∀ a ∈ A, a ∈ V` using `fun a ha => hle (RingHom.mem_range.mpr ⟨⟨(a, φ ⟨a, ha⟩), hmem0 ⟨a, ha⟩⟩, rfl⟩)`. Set `ψ : V →+* L` to `(p₂ G).comp (e.symm.toRingHom.comp (Subring.inclusion hVle'))`. Use `⟨V, hAV, ψ, fun a => ?_⟩` and prove the remaining obligations. Establish `key : e ⟨((a : Ω), φ a), hmem0 a⟩ = Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩` using `Subtype.ext rfl`.

Establish `hpre : e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩) = ⟨((a : Ω), φ a), hmem0 a⟩`. Rewrite using `[← key, RingEquiv.symm_apply_apply]`. Use `show p₂ G (e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩)) = φ a`. Rewrite using `[hpre]`. Both sides reduce to the same expression.
-/
theorem exists_valuationSubring_extension [IsAlgClosed L] (A : Subring Ω) (φ : A →+* L) :
    ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  classical
  have hG₀f : Functional (A.subtype.prod φ).range := by
    intro l hl
    obtain ⟨a, ha⟩ := RingHom.mem_range.mp hl
    have h1 : (a : Ω) = 0 := congrArg Prod.fst ha
    have h2 : φ a = l := congrArg Prod.snd ha
    have ha0 : a = 0 := Subtype.ext h1
    rw [← h2, ha0, map_zero]
  obtain ⟨G, hG₀G, hG⟩ := exists_maximal_functional _ hG₀f
  have : IsLocalRing G := isLocalRing_of_maximal hG
  have : IsLocalHom (p₂ G) := ⟨fun r hr => isUnit_of_p₂_ne_zero hG r hr.ne_zero⟩
  have hinj : Function.Injective (p₁ G) := by
    rw [injective_iff_map_eq_zero]
    rintro ⟨⟨b, l⟩, hr⟩ h0
    have hb : b = 0 := h0
    subst hb
    have hl := hG.1 l hr
    subst hl
    rfl
  let e : G ≃+* (p₁ G).range := RingEquiv.ofBijective (p₁ G).rangeRestrict
    ⟨fun r s h => hinj (congrArg Subtype.val h), (p₁ G).rangeRestrict_surjective⟩
  have : IsLocalRing (p₁ G).range :=
    IsLocalRing.of_surjective' (p₁ G).rangeRestrict (p₁ G).rangeRestrict_surjective
  obtain ⟨V, hV⟩ := LocalSubring.exists_le_valuationSubring (LocalSubring.mk (p₁ G).range)
  obtain ⟨hle, hloc⟩ := LocalSubring.le_def.mp hV
  have : IsLocalHom (p₁ G).rangeRestrict :=
    IsLocalHom.of_surjective _ (p₁ G).rangeRestrict_surjective
  let g : G →+* V := (Subring.inclusion hle).comp (p₁ G).rangeRestrict
  have : IsLocalHom g := ⟨fun r hr => IsLocalHom.map_nonunit (f := (p₁ G).rangeRestrict) r
    (IsLocalHom.map_nonunit (f := Subring.inclusion hle) (self := hloc) ((p₁ G).rangeRestrict r) hr)⟩
  have hVle : ∀ x ∈ V, x ∈ (p₁ G).range := by
    intro x hx
    obtain ⟨ξ, hξ⟩ := exists_mem_of_dominates hG V g (fun r => rfl) ⟨x, hx⟩
    exact RingHom.mem_range.mpr ⟨⟨(x, ξ), hξ⟩, rfl⟩
  have hVle' : V.toSubring ≤ (p₁ G).range := fun x hx => hVle x hx
  have hmem0 : ∀ a : A, ((a : Ω), φ a) ∈ G := fun a => hG₀G (RingHom.mem_range.mpr ⟨a, rfl⟩)
  have hAV : ∀ a ∈ A, a ∈ V := fun a ha =>
    hle (RingHom.mem_range.mpr ⟨⟨(a, φ ⟨a, ha⟩), hmem0 ⟨a, ha⟩⟩, rfl⟩)
  let ψ : V →+* L := (p₂ G).comp (e.symm.toRingHom.comp (Subring.inclusion hVle'))
  refine ⟨V, hAV, ψ, fun a => ?_⟩
  have key : e ⟨((a : Ω), φ a), hmem0 a⟩ = Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩ := Subtype.ext rfl
  have hpre : e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩) = ⟨((a : Ω), φ a), hmem0 a⟩ := by
    rw [← key, RingEquiv.symm_apply_apply]
  show p₂ G (e.symm (Subring.inclusion hVle' ⟨a.1, hAV a.1 a.2⟩)) = φ a
  rw [hpre]
  rfl

/- English proof (translation)
Introduce `Ω L _ _ _ A φ`. Conclude with `exists_valuationSubring_extension A φ`.
-/
theorem chevalley_extension : ∀ (Ω L : Type) [Field Ω] [Field L] [IsAlgClosed L] (A : Subring Ω)
    (φ : A →+* L), ∃ (V : ValuationSubring Ω) (hAV : ∀ a ∈ A, a ∈ V) (ψ : V →+* L),
      ∀ a : A, ψ ⟨a.1, hAV a.1 a.2⟩ = φ a := by
  intro Ω L _ _ _ A φ
  exact exists_valuationSubring_extension A φ

end GlobalTheory.CompanionTheory.Chevalley
