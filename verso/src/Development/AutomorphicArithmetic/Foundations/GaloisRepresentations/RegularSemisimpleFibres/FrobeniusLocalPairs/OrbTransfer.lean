import Mathlib
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.FrobeniusTwistedHilbertNinetyAlt
import Development.AutomorphicArithmetic.Foundations.GaloisRepresentations.RegularSemisimpleFibres.FrobeniusLocalPairs.CptConj

noncomputable section

open GlobalTheory.BCT

namespace UpperTheory.Gal.InertialTypesAlt.L

/- English proof (translation)
Establish `hS : rStab (fun _ : A => c) = ⊤`. Use extensionality with `k`. Simplify using `[rStab]`. Unfold `avg`. Rewrite using `[hS, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]`.

Use `haveI : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top`. Conclude with `finsum_eq_single (fun _ : A ⧸ (⊤ : Subgroup A) => c) 1 (fun q hq => absurd (Subsingleton.elim q 1) hq)`.
-/
private theorem avg_const_frobenius_local_pairs {A : Type} [Group A] (c : ℂ) : avg (fun _ : A => c) = c := by
  have hS : rStab (fun _ : A => c) = ⊤ := by
    ext k
    simp [rStab]
  unfold avg
  rw [hS, Subgroup.index_top, Nat.cast_one, inv_one, one_mul]
  haveI : Subsingleton (A ⧸ (⊤ : Subgroup A)) := QuotientGroup.subsingleton_quotient_top
  exact finsum_eq_single (fun _ : A ⧸ (⊤ : Subgroup A) => c) 1
    (fun q hq => absurd (Subsingleton.elim q 1) hq)

/- English proof (translation)
Use extensionality with `y`. Simplify using `only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨z, hz, rfl⟩`. Conclude with `S.mul_mem (S.mul_mem hs hz) (S.inv_mem hs)`.

Introduce `hy`. Conclude with `⟨s⁻¹ * y * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs, by group⟩`.
-/
private theorem conj_self {G : Type} [Group G] (S : Subgroup G) {s : G} (hs : s ∈ S) :
    S.map (MulAut.conj s).toMonoidHom = S := by
  ext y
  simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
  constructor
  · rintro ⟨z, hz, rfl⟩
    exact S.mul_mem (S.mul_mem hs hz) (S.inv_mem hs)
  · intro hy
    exact ⟨s⁻¹ * y * s, S.mul_mem (S.mul_mem (S.inv_mem hs) hy) hs, by group⟩

/- English proof (translation)
Establish `hz : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H)`. Rewrite using `[← MonoidHom.map_zpowers, Subgroup.coe_map]`. Rewrite using `[hz, hj.closure_image_eq, hj.isInducing.isCompact_iff]`.
-/
private theorem zpowers_closed {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (t : H) :
    IsCompact (closure (Subgroup.zpowers (j t) : Set G)) ↔ IsCompact (closure (Subgroup.zpowers t : Set H)) := by
  have hz : (Subgroup.zpowers (j t) : Set G) = j '' (Subgroup.zpowers t : Set H) := by
    rw [← MonoidHom.map_zpowers, Subgroup.coe_map]
  rw [hz, hj.closure_image_eq, hj.isInducing.isCompact_iff]

/- English proof (translation)
Unfold `cptPart`. Rewrite using `[MonoidHom.map_closure]`. Use `congr 1`. Use extensionality with `g`. Simplify using `only [Set.mem_setOf_eq, Set.mem_image, Subgroup.mem_map]`.

Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨⟨t, ht, rfl⟩, hc⟩`. Conclude with `⟨t, ⟨ht, (zpowers_closed j hj t).1 hc⟩, rfl⟩`. Introduce and unpack `⟨t, ⟨ht, hc⟩, rfl⟩`. Conclude with `⟨⟨t, ht, rfl⟩, (zpowers_closed j hj t).2 hc⟩`.
-/
private theorem cpt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T : Subgroup H) :
    cptPart (T.map j) = (cptPart T).map j := by
  unfold cptPart
  rw [MonoidHom.map_closure]
  congr 1
  ext g
  simp only [Set.mem_setOf_eq, Set.mem_image, Subgroup.mem_map]
  constructor
  · rintro ⟨⟨t, ht, rfl⟩, hc⟩
    exact ⟨t, ⟨ht, (zpowers_closed j hj t).1 hc⟩, rfl⟩
  · rintro ⟨t, ⟨ht, hc⟩, rfl⟩
    exact ⟨⟨t, ht, rfl⟩, (zpowers_closed j hj t).2 hc⟩

/- English proof (translation)
Establish `h : ((MulAut.conj c).toMonoidHom : G → G) = (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹)`. Use extensionality with `x`. Simplify using `[MulAut.conj_apply]`. Rewrite using `[h]`. Conclude with `Homeomorph.isClosedEmbedding _`.
-/
private theorem conj_closed {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (c : G) :
    Topology.IsClosedEmbedding (MulAut.conj c).toMonoidHom := by
  have h : ((MulAut.conj c).toMonoidHom : G → G) = (Homeomorph.mulLeft c).trans (Homeomorph.mulRight c⁻¹) := by
    ext x
    simp [MulAut.conj_apply]
  rw [h]
  exact Homeomorph.isClosedEmbedding _

private def wt {G : Type} [Group G] [TopologicalSpace G] (T K : Subgroup G) (x : G) : ℕ :=
  (T ⊓ K.map (MulAut.conj x).toMonoidHom).relIndex (cptPart T)

/- English proof (translation)
Unfold `wt`. Establish `hinj : Function.Injective (MulAut.conj t).toMonoidHom` using `(MulAut.conj t).injective`. Establish `hT : T.map (MulAut.conj t).toMonoidHom = T` using `conj_self T ht`. Establish `hKm : K.map (MulAut.conj (t * x * κ)).toMonoidHom = (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom`. Use extensionality with `y`.

Simplify using `only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨k, hk, rfl⟩`. Conclude with `⟨x * (κ * k * κ⁻¹) * x⁻¹, ⟨κ * k * κ⁻¹, K.mul_mem (K.mul_mem hκ hk) (K.inv_mem hκ), rfl⟩, by group⟩`. Introduce and unpack `⟨z, ⟨k, hk, rfl⟩, rfl⟩`.

Conclude with `⟨κ⁻¹ * k * κ, K.mul_mem (K.mul_mem (K.inv_mem hκ) hk) hκ, by group⟩`. Establish `hcpt : (cptPart T).map (MulAut.conj t).toMonoidHom = cptPart T`. Rewrite using `[← cpt_map _ (conj_closed t) T, hT]`. Establish `hI : T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom = (T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom`. Rewrite using `[Subgroup.map_inf_eq _ _ _ hinj, hT]`.

Rewrite using `[hKm]`. Combine the equalities or inequalities in the displayed calculation.
-/
private theorem wt_inv {G : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] (T K : Subgroup G)
    {t κ : G} (ht : t ∈ T) (hκ : κ ∈ K) (x : G) : wt T K (t * x * κ) = wt T K x := by
  unfold wt
  have hinj : Function.Injective (MulAut.conj t).toMonoidHom := (MulAut.conj t).injective
  have hT : T.map (MulAut.conj t).toMonoidHom = T := conj_self T ht
  have hKm : K.map (MulAut.conj (t * x * κ)).toMonoidHom =
      (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    ext y
    simp only [Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨k, hk, rfl⟩
      exact ⟨x * (κ * k * κ⁻¹) * x⁻¹,
        ⟨κ * k * κ⁻¹, K.mul_mem (K.mul_mem hκ hk) (K.inv_mem hκ), rfl⟩, by group⟩
    · rintro ⟨z, ⟨k, hk, rfl⟩, rfl⟩
      exact ⟨κ⁻¹ * k * κ, K.mul_mem (K.mul_mem (K.inv_mem hκ) hk) hκ, by group⟩
  have hcpt : (cptPart T).map (MulAut.conj t).toMonoidHom = cptPart T := by
    rw [← cpt_map _ (conj_closed t) T, hT]
  have hI : T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom =
      (T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom := by
    rw [Subgroup.map_inf_eq _ _ _ hinj, hT]
  rw [hKm]
  calc (T ⊓ (K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex (cptPart T)
      = ((T ⊓ K.map (MulAut.conj x).toMonoidHom).map (MulAut.conj t).toMonoidHom).relIndex
          ((cptPart T).map (MulAut.conj t).toMonoidHom) := by rw [hI, hcpt]
    _ = _ := Subgroup.relIndex_map_map_of_injective _ _ hinj

/- English proof (translation)
Unfold `wt`. Establish `h2 : T₀.map j ⊓ K.map (MulAut.conj (j h)).toMonoidHom = (T₀ ⊓ K₀.map (MulAut.conj h).toMonoidHom).map j`. Use extensionality with `y`. Simplify using `only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]`. Prove the components needed by the constructor for the conclusion.

Introduce and unpack `⟨⟨t, ht, rfl⟩, k, hk, hkt⟩`. Use `⟨t, ⟨ht, h⁻¹ * t * h, (hK _).1 ?_, by group⟩, rfl⟩` and prove the remaining obligations. Establish `: k = j (h⁻¹ * t * h)`. Simplify using `only [map_mul, map_inv, ← hkt]`. Use `group`.

Conclude with `this ▸ hk`. Introduce and unpack `⟨t, ⟨ht, k, hk, rfl⟩, rfl⟩`. Conclude with `⟨⟨_, ht, rfl⟩, j k, (hK k).2 hk, by simp⟩`. Rewrite using `[h2, cpt_map j hj]`. Conclude with `Subgroup.relIndex_map_map_of_injective _ _ hj.injective`.
-/
private theorem wt_map {G H : Type} [Group G] [TopologicalSpace G] [Group H] [TopologicalSpace H]
    (j : H →* G) (hj : Topology.IsClosedEmbedding j) (T₀ : Subgroup H) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (h : H) : wt (T₀.map j) K (j h) = wt T₀ K₀ h := by
  unfold wt
  have h2 : T₀.map j ⊓ K.map (MulAut.conj (j h)).toMonoidHom =
      (T₀ ⊓ K₀.map (MulAut.conj h).toMonoidHom).map j := by
    ext y
    simp only [Subgroup.mem_inf, Subgroup.mem_map, MulEquiv.coe_toMonoidHom, MulAut.conj_apply]
    constructor
    · rintro ⟨⟨t, ht, rfl⟩, k, hk, hkt⟩
      refine ⟨t, ⟨ht, h⁻¹ * t * h, (hK _).1 ?_, by group⟩, rfl⟩
      have : k = j (h⁻¹ * t * h) := by
        simp only [map_mul, map_inv, ← hkt]
        group
      exact this ▸ hk
    · rintro ⟨t, ⟨ht, k, hk, rfl⟩, rfl⟩
      exact ⟨⟨_, ht, rfl⟩, j k, (hK k).2 hk, by simp⟩
  rw [h2, cpt_map j hj]
  exact Subgroup.relIndex_map_map_of_injective _ _ hj.injective

/- English proof (translation)
Substitute `hT` using the available equality. Set `e : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H) → DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G)` to `fun p => DoubleCoset.mk (T₀.map j) K (j (Quotient.out p))`. Establish `hval : ∀ x, F (Quotient.out (DoubleCoset.mk (T₀.map j) K x)) = F x`. Introduce `x`. Take `⟨a, b, ha, hb, hx⟩` from `DoubleCoset.mk_out_eq_mul (T₀.map j) K x`.

Rewrite using `[hx]`. Conclude with `hinv a ha b hb x`. Establish `he' : ∀ h, e (DoubleCoset.mk T₀ K₀ h) = DoubleCoset.mk (T₀.map j) K (j h)`. Introduce `h`. Take `⟨a, b, ha, hb, hab⟩` from `DoubleCoset.mk_out_eq_mul T₀ K₀ h`.

Use `show DoubleCoset.mk (T₀.map j) K (j (Quotient.out (DoubleCoset.mk T₀ K₀ h))) = _`. Rewrite using `[hab, DoubleCoset.eq]`. Use `⟨(j a)⁻¹, (T₀.map j).inv_mem (Subgroup.mem_map_of_mem j ha), (j b)⁻¹, K.inv_mem ((hK b).mpr hb), ?_⟩` and prove the remaining obligations. Simplify using `only [map_mul]`. Use `group`.

Establish `he : Function.Injective e`. Introduce `p p' hpp`. Establish `hpp' : DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)) = DoubleCoset.mk (T₀.map j) K (j (Quotient.out p'))` using `hpp`. Rewrite `hpp'` using `[DoubleCoset.eq]`. Take `⟨a, ha, b, hb, hab⟩` from `hpp'`.

Take `⟨a₀, ha₀, rfl⟩` from `Subgroup.mem_map.mp ha`. Rewrite using `[← DoubleCoset.out_eq' T₀ K₀ p, ← DoubleCoset.out_eq' T₀ K₀ p', DoubleCoset.eq]`. Establish `hjb : j ((a₀ * Quotient.out p)⁻¹ * Quotient.out p') = b`. Rewrite using `[map_mul, map_inv, map_mul, hab]`. Use `group`.

Use `⟨a₀, ha₀, (a₀ * Quotient.out p)⁻¹ * Quotient.out p', ?_, by group⟩` and prove the remaining obligations. Rewrite using `[← hK, hjb]`. Conclude with `hb`. Establish `hsub : Function.support (fun q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) => F (Quotient.out q)) ⊆ Set.range e`. Introduce `q hq`.

Take `⟨h, κ, hκ, hx⟩` from `hsupp _ hq`. Use `⟨DoubleCoset.mk T₀ K₀ h, ?_⟩` and prove the remaining obligations. Rewrite using `[he', ← DoubleCoset.out_eq' (T₀.map j) K q, DoubleCoset.eq]`. Conclude with `⟨1, (T₀.map j).one_mem, κ, hκ, by rw [hx, one_mul]⟩`. Establish `hfull : ∑ᶠ q ∈ Set.range e, F (Quotient.out q) = ∑ᶠ q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G), F (Quotient.out q)`.

Rewrite using `[finsum_mem_def, Set.indicator_eq_self.mpr hsub]`. Rewrite using `[← hfull, finsum_mem_range he]`. Use `finsum_congr (fun p => ?_)` and prove the remaining obligations. Use `show F (Quotient.out (DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)))) = F₀ (Quotient.out p)`. Rewrite using `[hval, hjF]`.
-/
private theorem sum_transfer {G H : Type} [Group G] [Group H] (j : H →* G) (hj : Function.Injective j)
    (T : Subgroup G) (T₀ : Subgroup H) (hT : T = T₀.map j) (K : Subgroup G) (K₀ : Subgroup H)
    (hK : ∀ h, j h ∈ K ↔ h ∈ K₀) (F : G → ℂ) (F₀ : H → ℂ)
    (hinv : ∀ t ∈ T, ∀ κ ∈ K, ∀ x, F (t * x * κ) = F x) (hjF : ∀ h, F (j h) = F₀ h)
    (hsupp : ∀ x, F x ≠ 0 → ∃ h, ∃ κ ∈ K, x = j h * κ) :
    ∑ᶠ q : DoubleCoset.Quotient (T : Set G) (K : Set G), F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H), F₀ (Quotient.out q) := by
  classical
  subst hT
  let e : DoubleCoset.Quotient (T₀ : Set H) (K₀ : Set H) →
      DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) :=
    fun p => DoubleCoset.mk (T₀.map j) K (j (Quotient.out p))
  have hval : ∀ x, F (Quotient.out (DoubleCoset.mk (T₀.map j) K x)) = F x := by
    intro x
    obtain ⟨a, b, ha, hb, hx⟩ := DoubleCoset.mk_out_eq_mul (T₀.map j) K x
    rw [hx]
    exact hinv a ha b hb x
  have he' : ∀ h, e (DoubleCoset.mk T₀ K₀ h) = DoubleCoset.mk (T₀.map j) K (j h) := by
    intro h
    obtain ⟨a, b, ha, hb, hab⟩ := DoubleCoset.mk_out_eq_mul T₀ K₀ h
    show DoubleCoset.mk (T₀.map j) K (j (Quotient.out (DoubleCoset.mk T₀ K₀ h))) = _
    rw [hab, DoubleCoset.eq]
    refine ⟨(j a)⁻¹, (T₀.map j).inv_mem (Subgroup.mem_map_of_mem j ha), (j b)⁻¹,
      K.inv_mem ((hK b).mpr hb), ?_⟩
    simp only [map_mul]
    group
  have he : Function.Injective e := by
    intro p p' hpp
    have hpp' : DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)) =
        DoubleCoset.mk (T₀.map j) K (j (Quotient.out p')) := hpp
    rw [DoubleCoset.eq] at hpp'
    obtain ⟨a, ha, b, hb, hab⟩ := hpp'
    obtain ⟨a₀, ha₀, rfl⟩ := Subgroup.mem_map.mp ha
    rw [← DoubleCoset.out_eq' T₀ K₀ p, ← DoubleCoset.out_eq' T₀ K₀ p', DoubleCoset.eq]
    have hjb : j ((a₀ * Quotient.out p)⁻¹ * Quotient.out p') = b := by
      rw [map_mul, map_inv, map_mul, hab]
      group
    refine ⟨a₀, ha₀, (a₀ * Quotient.out p)⁻¹ * Quotient.out p', ?_, by group⟩
    rw [← hK, hjb]
    exact hb
  have hsub : Function.support
      (fun q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G) =>
        F (Quotient.out q)) ⊆ Set.range e := by
    intro q hq
    obtain ⟨h, κ, hκ, hx⟩ := hsupp _ hq
    refine ⟨DoubleCoset.mk T₀ K₀ h, ?_⟩
    rw [he', ← DoubleCoset.out_eq' (T₀.map j) K q, DoubleCoset.eq]
    exact ⟨1, (T₀.map j).one_mem, κ, hκ, by rw [hx, one_mul]⟩
  have hfull : ∑ᶠ q ∈ Set.range e, F (Quotient.out q) =
      ∑ᶠ q : DoubleCoset.Quotient ((T₀.map j : Subgroup G) : Set G) (K : Set G),
        F (Quotient.out q) := by
    rw [finsum_mem_def, Set.indicator_eq_self.mpr hsub]
  rw [← hfull, finsum_mem_range he]
  refine finsum_congr (fun p => ?_)
  show F (Quotient.out (DoubleCoset.mk (T₀.map j) K (j (Quotient.out p)))) = F₀ (Quotient.out p)
  rw [hval, hjF]

/- English proof (translation)
Introduce `G H _ _ _ _ _ _ _ _ j hj θ K K₀ hK δ γ hT φ f hφ hsupp hφf hθ`. Establish `hconst : ∀ x : G, (avg fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = φ (x⁻¹ * δ * θ x)`. Introduce `x`. Establish `e : (fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = fun _ => φ (x⁻¹ * δ * θ x)`. Use function extensionality and compare the values at `k`.

Rewrite using `[← hφ (k : G) k.2 (x⁻¹ * δ * θ x)]`. Use `congr 1`. Rewrite using `[map_mul]`. Use `group`. Rewrite using `[e, avg_const_frobenius_local_pairs]`.

Establish `hconst₀ : ∀ y : H, (avg fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) = f (y⁻¹ * γ * y)`. Introduce `y`. Establish `e : (fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) = fun _ => f (y⁻¹ * γ * y)`. Use function extensionality and compare the values at `k`. Rewrite using `[MonoidHom.id_apply, ← hφf, ← hφf, ← hφ (j k) ((hK k).2 k.2) ((j y)⁻¹ * δ * θ (j y))]`.

Use `congr 1`. Rewrite using `[map_mul, map_mul]`. Use `group`. Rewrite using `[e, avg_const_frobenius_local_pairs]`. Establish `hinv : ∀ t ∈ twCent θ δ, ∀ κ ∈ K, ∀ x : G, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (t * x * κ) = (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x`.

Introduce `t ht κ hκ x`. Establish `ht' : t * δ = δ * θ t` using `ht`. Establish `e : (t * x * κ)⁻¹ * δ * θ (t * x * κ) = κ⁻¹ * (x⁻¹ * δ * θ x) * θ κ`. Rewrite using `[map_mul, map_mul]`. Combine the equalities or inequalities in the displayed calculation.

Simplify using `only`. Rewrite using `[wt_inv (twCent θ δ) K ht hκ x, e, hφ κ hκ]`. Establish `hjF : ∀ y : H, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (j y) = (fun y => (wt (twCent (MonoidHom.id H) γ) K₀ y : ℂ) * f (y⁻¹ * γ * y)) y`. Introduce `y`. Simplify using `only`.

Rewrite using `[hT, wt_map j hj _ K K₀ hK y, hφf]`. Establish `hsupp' : ∀ x : G, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x ≠ 0 → ∃ y, ∃ κ ∈ K, x = j y * κ`. Introduce `x hx`. Apply `hsupp x` to reduce the goal to its premises. Introduce `h0`.

Apply `hx` to reduce the goal to its premises. Simplify using `only [h0, mul_zero]`. Unfold `twOrb`. Simplify using `only [hconst, hconst₀]`. Conclude with `sum_transfer j hj.injective (twCent θ δ) (twCent (MonoidHom.id H) γ) hT K K₀ hK _ _ hinv hjF hsupp'`.
-/
theorem orbTransfer : OrbTransfer := by
  intro G H _ _ _ _ _ _ _ _ j hj θ K K₀ hK δ γ hT φ f hφ hsupp hφf hθ
  have hconst : ∀ x : G, (avg fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = φ (x⁻¹ * δ * θ x) := by
    intro x
    have e : (fun k : K => φ ((x * k)⁻¹ * δ * θ (x * k))) = fun _ => φ (x⁻¹ * δ * θ x) := by
      funext k
      rw [← hφ (k : G) k.2 (x⁻¹ * δ * θ x)]
      congr 1
      rw [map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hconst₀ : ∀ y : H, (avg fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) =
      f (y⁻¹ * γ * y) := by
    intro y
    have e : (fun k : K₀ => f ((y * k)⁻¹ * γ * MonoidHom.id H (y * k))) = fun _ => f (y⁻¹ * γ * y) := by
      funext k
      rw [MonoidHom.id_apply, ← hφf, ← hφf, ← hφ (j k) ((hK k).2 k.2) ((j y)⁻¹ * δ * θ (j y))]
      congr 1
      rw [map_mul, map_mul]
      group
    rw [e, avg_const_frobenius_local_pairs]
  have hinv : ∀ t ∈ twCent θ δ, ∀ κ ∈ K, ∀ x : G,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (t * x * κ) =
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x := by
    intro t ht κ hκ x
    have ht' : t * δ = δ * θ t := ht
    have e : (t * x * κ)⁻¹ * δ * θ (t * x * κ) = κ⁻¹ * (x⁻¹ * δ * θ x) * θ κ := by
      rw [map_mul, map_mul]
      calc (t * x * κ)⁻¹ * δ * (θ t * θ x * θ κ)
          = κ⁻¹ * x⁻¹ * t⁻¹ * (δ * θ t) * θ x * θ κ := by group
        _ = _ := by rw [← ht']; group
    simp only
    rw [wt_inv (twCent θ δ) K ht hκ x, e, hφ κ hκ]
  have hjF : ∀ y : H,
      (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) (j y) =
      (fun y => (wt (twCent (MonoidHom.id H) γ) K₀ y : ℂ) * f (y⁻¹ * γ * y)) y := by
    intro y
    simp only
    rw [hT, wt_map j hj _ K K₀ hK y, hφf]
  have hsupp' : ∀ x : G, (fun x => (wt (twCent θ δ) K x : ℂ) * φ (x⁻¹ * δ * θ x)) x ≠ 0 →
      ∃ y, ∃ κ ∈ K, x = j y * κ := by
    intro x hx
    apply hsupp x
    intro h0
    apply hx
    simp only [h0, mul_zero]
  unfold twOrb
  simp only [hconst, hconst₀]
  exact sum_transfer j hj.injective (twCent θ δ) (twCent (MonoidHom.id H) γ) hT K K₀ hK _ _
    hinv hjF hsupp'

end UpperTheory.Gal.InertialTypesAlt.L
