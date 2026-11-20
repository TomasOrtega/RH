import Mathlib
import GroundTheory.AutomorphicForms.SmoothRep
import GroundTheory.AutomorphicForms.TensorProductTheorem.Operators
import GroundTheory.AutomorphicForms.TensorProductTheorem.MatrixCoeff

noncomputable section

namespace GroundTheory.Automorphic

namespace RestrictedTensor

open Module Set

variable {G : Type*} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [LocallyCompactSpace G]
  [T2Space G] [TotallyDisconnectedSpace G]
  {V : Type*} [AddCommGroup V] [Module ℂ V] {ρ : Representation ℂ G V}
  {K : Subgroup G}

/- English proof (translation)
Take `⟨N, hNo, hNK, hNu, hnorm, hfin⟩` from `exists_normal_subgroup hKc hKo (U := (stabilizerOf ρ u : Set G)) ((hρ u).mem_nhds (one_mem _))`. Set `_ : Fintype (K ⧸ N.subgroupOf K)` to `Fintype.ofFinite _`. Establish `hu : u ∈ fixedVectors ρ N` using `fun n hn => hNu hn`. Use `set c : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)`. Establish `hc : c ≠ 0`.

Simplify using `only [c, ne_eq, Nat.cast_eq_zero]`. Conclude with `Fintype.card_ne_zero`. Use `set w : V := c⁻¹ • cosetSum ρ K N u`. Establish `hw : w ∈ fixedVectors ρ K` using `Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hu)`. Establish `hdiff : u - w = -(c⁻¹ • ∑ q : K ⧸ N.subgroupOf K, (ρ ((Quotient.out q : K) : G) u - u))`.

Rewrite using `[Finset.sum_sub_distrib, ← cosetSum_apply, Finset.sum_const, Finset.card_univ, smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]`. Simplify using `[w]`. Establish `hspan : u - w ∈ Submodule.span ℂ (range fun k : K => ρ k u - u)`. Rewrite using `[hdiff]`. Use `Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))` and prove the remaining obligations.

Conclude with `Submodule.subset_span ⟨Quotient.out q, rfl⟩`. Establish `hle : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer ρ K`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `sub_mem_coinvariantsKer k.2 u`.

Establish `heq : fixedProj ρ hρ hKc hKo u = ⟨w, hw⟩` using `(fixedProj_eq_iff hρ hKc hKo).2 (hle hspan)`. Rewrite using `[heq]`. Conclude with `hspan`.
-/
theorem sub_fixedProj_mem_span (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (u : V) :
    u - (fixedProj ρ hρ hKc hKo u : V) ∈
      Submodule.span ℂ (range fun k : K => ρ k u - u) := by
  classical
  obtain ⟨N, hNo, hNK, hNu, hnorm, hfin⟩ :=
    exists_normal_subgroup hKc hKo (U := (stabilizerOf ρ u : Set G))
      ((hρ u).mem_nhds (one_mem _))
  let _ : Fintype (K ⧸ N.subgroupOf K) := Fintype.ofFinite _
  have hu : u ∈ fixedVectors ρ N := fun n hn => hNu hn
  set c : ℂ := (Fintype.card (K ⧸ N.subgroupOf K) : ℂ)
  have hc : c ≠ 0 := by
    simp only [c, ne_eq, Nat.cast_eq_zero]
    exact Fintype.card_ne_zero
  set w : V := c⁻¹ • cosetSum ρ K N u
  have hw : w ∈ fixedVectors ρ K :=
    Submodule.smul_mem _ _ (cosetSum_mem_fixedVectors ρ hnorm hu)
  have hdiff : u - w = -(c⁻¹ • ∑ q : K ⧸ N.subgroupOf K,
      (ρ ((Quotient.out q : K) : G) u - u)) := by
    rw [Finset.sum_sub_distrib, ← cosetSum_apply, Finset.sum_const, Finset.card_univ,
      smul_sub, ← Nat.cast_smul_eq_nsmul ℂ, smul_smul, inv_mul_cancel₀ hc, one_smul]
    simp [w]
  have hspan : u - w ∈ Submodule.span ℂ (range fun k : K => ρ k u - u) := by
    rw [hdiff]
    refine Submodule.neg_mem _ (Submodule.smul_mem _ _ (Submodule.sum_mem _ fun q _ => ?_))
    exact Submodule.subset_span ⟨Quotient.out q, rfl⟩
  have hle : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer ρ K := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact sub_mem_coinvariantsKer k.2 u
  have heq : fixedProj ρ hρ hKc hKo u = ⟨w, hw⟩ :=
    (fixedProj_eq_iff hρ hKc hKo).2 (hle hspan)
  rw [heq]
  exact hspan

/- English proof (translation)
Establish `h1` using `sub_fixedProj_mem_span hρ hKc hKo x`. Establish `h2 : Submodule.span ℂ (range fun k : K => ρ k x - x) ≤ X.toSubmodule`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨k, rfl⟩`. Conclude with `X.toSubmodule.sub_mem (X.apply_mem_toSubmodule _ hx) hx`.

Use `X.toSubmodule.sub_mem hx (h2 h1)` as an intermediate fact. Rewrite `this` using `[sub_sub_cancel]`. Then use the resulting hypothesis.
-/
theorem fixedProj_mem (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) (X : Subrepresentation ρ) {x : V} (hx : x ∈ X.toSubmodule) :
    (fixedProj ρ hρ hKc hKo x : V) ∈ X.toSubmodule := by
  have h1 := sub_fixedProj_mem_span hρ hKc hKo x
  have h2 : Submodule.span ℂ (range fun k : K => ρ k x - x) ≤ X.toSubmodule := by
    rw [Submodule.span_le]
    rintro _ ⟨k, rfl⟩
    exact X.toSubmodule.sub_mem (X.apply_mem_toSubmodule _ hx) hx
  have := X.toSubmodule.sub_mem hx (h2 h1)
  rwa [sub_sub_cancel] at this

variable (hρ : IsSmooth ρ) (hKc : IsCompact (K : Set G)) (hKo : IsOpen (K : Set G))

def heckeOp (g : G) : End ℂ (fixedVectors ρ K) :=
  fixedProj ρ hρ hKc hKo ∘ₗ ρ g ∘ₗ (fixedVectors ρ K).subtype

def heckeOps : Set (End ℂ (fixedVectors ρ K)) :=
  range (heckeOp hρ hKc hKo)

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem heckeOp_apply (g : G) (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo g m = fixedProj ρ hρ hKc hKo (ρ g m) :=
  rfl

/- English proof (translation)
Assemble the required witnesses or components as `⟨g, rfl⟩`.
-/
theorem heckeOp_mem_heckeOps (g : G) : heckeOp hρ hKc hKo g ∈ heckeOps hρ hKc hKo :=
  ⟨g, rfl⟩

/- English proof (translation)
Use extensionality with `m`. Rewrite using `[heckeOp_apply, fixedProj_apply_act hρ hKc hKo hg, fixedProj_apply_of_mem hρ hKc hKo m.2, Module.End.one_apply]`.
-/
theorem heckeOp_of_mem {g : G} (hg : g ∈ K) : heckeOp hρ hKc hKo g = 1 := by
  ext m
  rw [heckeOp_apply, fixedProj_apply_act hρ hKc hKo hg, fixedProj_apply_of_mem hρ hKc hKo m.2,
    Module.End.one_apply]

/- English proof (translation)
The claim follows from `heckeOp_of_mem hρ hKc hKo (one_mem K)`.
-/
theorem heckeOp_one : heckeOp hρ hKc hKo 1 = 1 :=
  heckeOp_of_mem hρ hKc hKo (one_mem K)

/- English proof (translation)
Take `⟨u, hu⟩ : ∃ u, u = ρ b m` from `⟨_, rfl⟩`. Establish `hspan` using `sub_fixedProj_mem_span hρ hKc hKo u`. Establish `hkill : ∀ y ∈ Submodule.span ℂ (range fun k : K => ρ k u - u), fixedProj ρ hρ hKc hKo (ρ a y) = 0`. Introduce `y hy`. Proceed by induction on `hy using Submodule.span_induction with`.

Consider the case `mem y hy`. Take `⟨⟨h, hh⟩, rfl⟩` from `hy`. Take `⟨k, hk, hka, hkb⟩` from `hab h hh`. Establish `hk' : k⁻¹ * h ∈ K` using `K.mul_mem (K.inv_mem hk) hh`. Establish `h1 : ρ h u = ρ k u`.

Establish `: ρ (k⁻¹ * h) u = u`. Rewrite using `[hu, ← Module.End.mul_apply, ← map_mul, hkb, map_mul, Module.End.mul_apply, m.2 _ hk']`. Combine the equalities or inequalities in the displayed calculation. Rewrite using `[← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]`. Use `_ = ρ k u := by rw [this]`.

Simplify using `only`. Rewrite using `[h1, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, ← hka, map_mul, Module.End.mul_apply, fixedProj_apply_act hρ hKc hKo hk, sub_self]`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]`. Consider the case `smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]`.

Use `hkill _ hspan` as an intermediate fact. Rewrite `this` using `[map_sub, map_sub, sub_eq_zero]`. Substitute `hu` using the available equality. Rewrite using `[heckeOp_apply, heckeOp_apply, heckeOp_apply, ← this, map_mul, Module.End.mul_apply]`.
-/
theorem heckeOp_mul_apply {a b : G}
    (hab : ∀ h ∈ K, ∃ k ∈ K, k * a = a * k ∧ (k⁻¹ * h) * b = b * (k⁻¹ * h))
    (m : fixedVectors ρ K) :
    heckeOp hρ hKc hKo a (heckeOp hρ hKc hKo b m) = heckeOp hρ hKc hKo (a * b) m := by
  obtain ⟨u, hu⟩ : ∃ u, u = ρ b m := ⟨_, rfl⟩
  have hspan := sub_fixedProj_mem_span hρ hKc hKo u

  have hkill : ∀ y ∈ Submodule.span ℂ (range fun k : K => ρ k u - u),
      fixedProj ρ hρ hKc hKo (ρ a y) = 0 := by
    intro y hy
    induction hy using Submodule.span_induction with
    | mem y hy =>
      obtain ⟨⟨h, hh⟩, rfl⟩ := hy
      obtain ⟨k, hk, hka, hkb⟩ := hab h hh
      have hk' : k⁻¹ * h ∈ K := K.mul_mem (K.inv_mem hk) hh
      have h1 : ρ h u = ρ k u := by
        have : ρ (k⁻¹ * h) u = u := by
          rw [hu, ← Module.End.mul_apply, ← map_mul, hkb, map_mul, Module.End.mul_apply,
            m.2 _ hk']
        calc ρ h u = ρ k (ρ (k⁻¹ * h) u) := by
                rw [← Module.End.mul_apply, ← map_mul, mul_inv_cancel_left]
          _ = ρ k u := by rw [this]
      simp only
      rw [h1, map_sub, map_sub, ← Module.End.mul_apply, ← map_mul, ← hka, map_mul,
        Module.End.mul_apply, fixedProj_apply_act hρ hKc hKo hk, sub_self]
    | zero => simp
    | add x y _ _ hx hy => rw [map_add, map_add, hx, hy, add_zero]
    | smul c x _ hx => rw [map_smul, map_smul, hx, smul_zero]
  have := hkill _ hspan
  rw [map_sub, map_sub, sub_eq_zero] at this
  subst hu
  rw [heckeOp_apply, heckeOp_apply, heckeOp_apply, ← this, map_mul, Module.End.mul_apply]

/- English proof (translation)
Introduce and unpack `_ ⟨g, rfl⟩ m hm`. Rewrite using `[Submodule.mem_comap, heckeOp_apply]`. Conclude with `fixedProj_mem hρ hKc hKo X (X.apply_mem_toSubmodule g hm)`.
-/
theorem isStable_comap (X : Subrepresentation ρ) :
    IsStable (heckeOps hρ hKc hKo) (X.toSubmodule.comap (fixedVectors ρ K).subtype) := by
  rintro _ ⟨g, rfl⟩ m hm
  rw [Submodule.mem_comap, heckeOp_apply]
  exact fixedProj_mem hρ hKc hKo X (X.apply_mem_toSubmodule g hm)

/- English proof (translation)
Use `⟨Submodule.nontrivial_iff_ne_bot.2 hK, fun p hp => ?_⟩` and prove the remaining obligations. Distinguish the cases in `hp0 : p = ⊥`. Conclude with `Or.inl hp0`. Use `right`. Take `⟨m, hm, hm0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hp0`.

Establish `hm0' : (m : V) ≠ 0` using `fun h => hm0 (Subtype.ext h)`. Rewrite using `[eq_top_iff]`. Introduce `m' _`. Establish `hle : Submodule.span ℂ (range fun g => ρ g (m : V)) ≤ p.comap ((fixedProj ρ hρ hKc hKo))`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `hp _ (heckeOp_mem_heckeOps hρ hKc hKo g) m hm`. Use `hle (mem_span_orbit (ρ := ρ) hm0' (m' : V))` as an intermediate fact. Rewrite `this` using `[Submodule.mem_comap]`. Establish `he : fixedProj ρ hρ hKc hKo (m' : V) = m'` using `Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo m'.2)`.

Rewrite `this` using `[he]`. Then use the resulting hypothesis.
-/
theorem isSimpleUnder_heckeOps [ρ.IsIrreducible] (hK : fixedVectors ρ K ≠ ⊥) :
    IsSimpleUnder (heckeOps hρ hKc hKo) := by
  refine ⟨Submodule.nontrivial_iff_ne_bot.2 hK, fun p hp => ?_⟩
  by_cases hp0 : p = ⊥
  · exact Or.inl hp0
  right
  obtain ⟨m, hm, hm0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hp0
  have hm0' : (m : V) ≠ 0 := fun h => hm0 (Subtype.ext h)
  rw [eq_top_iff]
  intro m' _
  have hle : Submodule.span ℂ (range fun g => ρ g (m : V)) ≤
      p.comap ((fixedProj ρ hρ hKc hKo)) := by
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact hp _ (heckeOp_mem_heckeOps hρ hKc hKo g) m hm
  have := hle (mem_span_orbit (ρ := ρ) hm0' (m' : V))
  rw [Submodule.mem_comap] at this
  have he : fixedProj ρ hρ hKc hKo (m' : V) = m' :=
    Subtype.ext (fixedProj_apply_of_mem hρ hKc hKo m'.2)
  rwa [he] at this

omit hρ hKc hKo in

/- English proof (translation)
Establish `hbt : (⊥ : Subrepresentation ρ) ≠ ⊤`. Introduce `h0`. Take `⟨x, hx⟩` from `exists_ne (0 : V)`. Establish `: x ∈ (⊤ : Subrepresentation ρ).toSubmodule` using `Submodule.mem_top`. Rewrite `this` using `[← h0]`.

Conclude with `hx this`. Use `{ exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }` and prove the remaining obligations. Distinguish the cases in `hX : X.toSubmodule = ⊥`. Use `left`. Use extensionality with `x`.

Prove the components needed by the constructor for the conclusion. Introduce `hx`. Establish `: x ∈ X.toSubmodule` using `hx`. Rewrite `this` using `[hX]`. Conclude with `this`.

Introduce `hx`. Establish `: x = 0` using `hx`. Rewrite using `[this]`. Conclude with `X.toSubmodule.zero_mem`. Use `right`.

Take `⟨x, hx, hx0⟩` from `Submodule.exists_mem_ne_zero_of_ne_bot hX`. Use extensionality with `y`. Use `⟨fun _ => Submodule.mem_top, fun _ => ?_⟩` and prove the remaining obligations. Take `⟨K, hKc, hKo, hxK, hyK, hsimple⟩` from `h x y hx0`. Establish `hst` using `isStable_comap hρ hKc hKo X`.

Break down `hsimple.2 _ hst with h0 | h0` into its components or cases. It suffices to derive a contradiction. Establish `: (⟨x, hxK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype` using `hx`. Rewrite `this` using `[h0, Submodule.mem_bot]`. Conclude with `hx0 (congrArg Subtype.val this)`.

Establish `: (⟨y, hyK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype`. Rewrite using `[h0]`. Discharge the goal by the elementary cases of `trivial`. Conclude with `this`.
-/
theorem isIrreducible_of_forall (hρ : IsSmooth ρ) [Nontrivial V]
    (h : ∀ x y : V, x ≠ 0 → ∃ (K : Subgroup G) (hKc : IsCompact (K : Set G))
      (hKo : IsOpen (K : Set G)), x ∈ fixedVectors ρ K ∧ y ∈ fixedVectors ρ K ∧
        IsSimpleUnder (heckeOps hρ hKc hKo)) :
    ρ.IsIrreducible := by
  have hbt : (⊥ : Subrepresentation ρ) ≠ ⊤ := by
    intro h0
    obtain ⟨x, hx⟩ := exists_ne (0 : V)
    have : x ∈ (⊤ : Subrepresentation ρ).toSubmodule := Submodule.mem_top
    rw [← h0] at this
    exact hx this
  refine { exists_pair_ne := ⟨⊥, ⊤, hbt⟩, eq_bot_or_eq_top := fun X => ?_ }
  by_cases hX : X.toSubmodule = ⊥
  · left
    ext x
    constructor
    · intro hx
      have : x ∈ X.toSubmodule := hx
      rw [hX] at this
      exact this
    · intro hx
      have : x = 0 := hx
      rw [this]
      exact X.toSubmodule.zero_mem
  right
  obtain ⟨x, hx, hx0⟩ := Submodule.exists_mem_ne_zero_of_ne_bot hX
  ext y
  refine ⟨fun _ => Submodule.mem_top, fun _ => ?_⟩
  obtain ⟨K, hKc, hKo, hxK, hyK, hsimple⟩ := h x y hx0
  have hst := isStable_comap hρ hKc hKo X
  rcases hsimple.2 _ hst with h0 | h0
  · exfalso
    have : (⟨x, hxK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := hx
    rw [h0, Submodule.mem_bot] at this
    exact hx0 (congrArg Subtype.val this)
  · have : (⟨y, hyK⟩ : fixedVectors ρ K) ∈ X.toSubmodule.comap (fixedVectors ρ K).subtype := by
      rw [h0]; trivial
    exact this

omit hρ hKc hKo in

/- English proof (translation)
Establish `hmem : (fixedProj ρ hρ hKc hKo u : V) ∈ fixedVectors (ρ.comp ι) K'` using `fun k hk => (fixedProj ρ hρ hKc hKo u).2 _ (hK' k hk)`. Establish `h1` using `sub_fixedProj_mem_span hρ hKc hKo u`. Establish `h2 : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer (ρ.comp ι) K'`. Rewrite using `[Submodule.span_le]`. Introduce and unpack `_ ⟨⟨h, hh⟩, rfl⟩`.

Take `⟨k, hk, hkh⟩` from `hu h hh`. Simplify using `only [SetLike.mem_coe]`. Rewrite using `[hkh]`. Conclude with `sub_mem_coinvariantsKer (ρ := ρ.comp ι) hk u`. Use `(fixedProj_eq_iff hρι hK'c hK'o (w := ⟨_, hmem⟩)).2 (h2 h1)` as an intermediate fact.

Rewrite using `[this]`.
-/
theorem fixedProj_comp_eq {L : Type*} [Group L] [TopologicalSpace L] [IsTopologicalGroup L]
    [LocallyCompactSpace L] [T2Space L] [TotallyDisconnectedSpace L] (ι : L →* G)
    (hρ : IsSmooth ρ) (hρι : IsSmooth (ρ.comp ι)) (hKc : IsCompact (K : Set G))
    (hKo : IsOpen (K : Set G)) {K' : Subgroup L} (hK'c : IsCompact (K' : Set L))
    (hK'o : IsOpen (K' : Set L)) (hK' : ∀ k ∈ K', ι k ∈ K) {u : V}
    (hu : ∀ h ∈ K, ∃ k ∈ K', ρ h u = ρ (ι k) u) :
    (fixedProj (ρ.comp ι) hρι hK'c hK'o u : V) = fixedProj ρ hρ hKc hKo u := by
  have hmem : (fixedProj ρ hρ hKc hKo u : V) ∈ fixedVectors (ρ.comp ι) K' :=
    fun k hk => (fixedProj ρ hρ hKc hKo u).2 _ (hK' k hk)
  have h1 := sub_fixedProj_mem_span hρ hKc hKo u
  have h2 : Submodule.span ℂ (range fun k : K => ρ k u - u) ≤ coinvariantsKer (ρ.comp ι) K' := by
    rw [Submodule.span_le]
    rintro _ ⟨⟨h, hh⟩, rfl⟩
    obtain ⟨k, hk, hkh⟩ := hu h hh
    simp only [SetLike.mem_coe]
    rw [hkh]
    exact sub_mem_coinvariantsKer (ρ := ρ.comp ι) hk u
  have := (fixedProj_eq_iff hρι hK'c hK'o (w := ⟨_, hmem⟩)).2 (h2 h1)
  rw [this]

end RestrictedTensor

end GroundTheory.Automorphic
