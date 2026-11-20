import Mathlib
import Development.AbelianVarietyTheory.Proofs.FoundationProofs.HeckeVecMemFixed
import Development.AbelianVarietyTheory.Proofs.InertiaEigenvalues.IsIdempotentElemCharIdem

open Formalism.UG GlobalTheory.PRep GlobalTheory.LFun

namespace GlobalTheory.LGrp.Zonal

open GlobalTheory.LocGL

variable {G V W : Type} [Group G] [TopologicalSpace G] [IsTopologicalGroup G] [AddCommGroup V] [Module ℂ V]
  [AddCommGroup W] [Module ℂ W] {K : Subgroup G}

/- English proof (translation)
Establish `hmem : ∀ c : G ⧸ K, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔ c ∈ (P.finite_cosets_in_doset hK g).toFinset` using `fun c => by`. Rewrite using `[Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]`. Conclude with `⟨fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩, fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩⟩`. Rewrite using `[← idem_of_mem hσ hc (SatCompare.heckeVec_mem_fixed hK (Final.DosetIndMem G K ℂ g) hz)]`. Unfold `heckeVec`.

Rewrite using `[finsum_eq_sum_of_support_subset (s := (P.finite_cosets_in_doset hK g).toFinset), map_sum, Nat.cast_smul_eq_nsmul, ← Finset.sum_const]`. Use `Finset.sum_congr rfl fun c hc' => ?_` and prove the remaining obligations. Establish `h1` using `(hmem c).2 hc'`. Take `⟨a, b, e⟩` from `(Set.Finite.mem_toFinset _).1 hc'`. Rewrite using `[dosetInd, Set.indicator_of_mem h1, Pi.one_apply, one_smul, e, map_mul, map_mul, Module.End.mul_apply, Module.End.mul_apply, mem_fixed.1 hz b b.2, idem_apply_mem hσ hc a.2]`.

Introduce `c hc'`. Assume the negation of the conclusion as `h`. Conclude with `hc' (by show dosetInd ℂ K g c.out • _ = 0`. Rewrite using `[dosetInd, Set.indicator_of_notMem (fun h' => h ((hmem c).1 h')), zero_smul])`.
-/
theorem heckeVec_dosetInd {σ : Representation ℂ G V} (hσ : IsSmooth σ) (hc : IsCompact (K : Set G))
    (hK : IsCommensurated K) {z : V} (hz : z ∈ fixed σ K) (g : G) :
    heckeVec σ K (dosetInd ℂ K g) z =
      ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) • idem hσ hc (σ g z) := by
  have hmem : ∀ c : G ⧸ K, c.out ∈ DoubleCoset.doubleCoset g (K : Set G) (K : Set G) ↔
      c ∈ (P.finite_cosets_in_doset hK g).toFinset := fun c => by
    rw [Set.Finite.mem_toFinset, DoubleCoset.mem_doubleCoset]
    exact ⟨fun ⟨a, ha, b, hb, e⟩ => ⟨⟨a, ha⟩, ⟨b, hb⟩, e⟩, fun ⟨a, b, e⟩ => ⟨a, a.2, b, b.2, e⟩⟩
  rw [← idem_of_mem hσ hc (SatCompare.heckeVec_mem_fixed hK (Final.DosetIndMem G K ℂ g) hz)]
  unfold heckeVec
  rw [finsum_eq_sum_of_support_subset (s := (P.finite_cosets_in_doset hK g).toFinset), map_sum,
    Nat.cast_smul_eq_nsmul, ← Finset.sum_const]
  · refine Finset.sum_congr rfl fun c hc' => ?_
    have h1 := (hmem c).2 hc'
    obtain ⟨a, b, e⟩ := (Set.Finite.mem_toFinset _).1 hc'
    rw [dosetInd, Set.indicator_of_mem h1, Pi.one_apply, one_smul, e, map_mul, map_mul, Module.End.mul_apply,
      Module.End.mul_apply, mem_fixed.1 hz b b.2, idem_apply_mem hσ hc a.2]
  · intro c hc'
    by_contra h
    exact hc' (by
      show dosetInd ℂ K g c.out • _ = 0
      rw [dosetInd, Set.indicator_of_notMem (fun h' => h ((hmem c).1 h')), zero_smul])

omit [TopologicalSpace G] [IsTopologicalGroup G] in

/- English proof (translation)
Use `Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (Set.Finite.mem_toFinset _).2 ?_⟩)` and prove the remaining obligations. Take `⟨u, hu⟩` from `QuotientGroup.mk_out_eq_mul K g`. Conclude with `⟨1, u, by simpa using hu⟩`.
-/
theorem card_ne_zero (hK : IsCommensurated K) (g : G) :
    ((P.finite_cosets_in_doset hK g).toFinset.card : ℂ) ≠ 0 := by
  refine Nat.cast_ne_zero.2 (Finset.card_ne_zero.2 ⟨(g : G ⧸ K), (Set.Finite.mem_toFinset _).2 ?_⟩)
  obtain ⟨u, hu⟩ := QuotientGroup.mk_out_eq_mul K g
  exact ⟨1, u, by simpa using hu⟩

/- English proof (translation)
Proceed by induction on `a using MonoidAlgebra.induction_on with`. Consider the case `of g`. Take `⟨c, ha, hb⟩` from `h g`. Use `⟨c, ?_, ?_⟩` and prove the remaining obligations. Use `show idem hπ hc (π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x) = _`.

Simplify using `using ha`. Use `show idem hρ hc (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g) y) = _`. Simplify using `using hb`. Consider the case `add a b ha hb`. Take `⟨c, h1, h2⟩` from `ha`.

Take `⟨d, h3, h4⟩` from `hb`. Conclude with `⟨c + d, by rw [map_add, map_add, h1, h3, add_smul], by rw [map_add, map_add, h2, h4, add_smul]⟩`. Consider the case `smul r a ha`. Take `⟨c, h1, h2⟩` from `ha`. Conclude with `⟨r * c, by rw [map_smul, map_smul, h1, mul_smul], by rw [map_smul, map_smul, h2, mul_smul]⟩`.
-/
theorem idem_orbitMap {π : Representation ℂ G V} {ρ : Representation ℂ G W} (hπ : IsSmooth π) (hρ : IsSmooth ρ)
    (hc : IsCompact (K : Set G)) {x : V} {y : W}
    (h : ∀ g, ∃ c : ℂ, idem hπ hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y) (a : MonoidAlgebra ℂ G) :
    ∃ c : ℂ, idem hπ hc (orbitMap π x a) = c • x ∧ idem hρ hc (orbitMap ρ y a) = c • y := by
  induction a using MonoidAlgebra.induction_on with
  | of g =>
    obtain ⟨c, ha, hb⟩ := h g
    refine ⟨c, ?_, ?_⟩
    · show idem hπ hc (π.asAlgebraHom (MonoidAlgebra.of ℂ G g) x) = _
      simpa using ha
    · show idem hρ hc (ρ.asAlgebraHom (MonoidAlgebra.of ℂ G g) y) = _
      simpa using hb
  | add a b ha hb =>
    obtain ⟨c, h1, h2⟩ := ha
    obtain ⟨d, h3, h4⟩ := hb
    exact ⟨c + d, by rw [map_add, map_add, h1, h3, add_smul], by rw [map_add, map_add, h2, h4, add_smul]⟩
  | smul r a ha =>
    obtain ⟨c, h1, h2⟩ := ha
    exact ⟨r * c, by rw [map_smul, map_smul, h1, mul_smul], by rw [map_smul, map_smul, h2, mul_smul]⟩

/- English proof (translation)
Establish `h1 : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y` using `fun g => by`. Take `⟨c, ha, hb⟩` from `h _ (Final.DosetIndMem G K ℂ g)`. Rewrite `ha` using `[heckeVec_dosetInd hπ.1 hc hK hx]`. Rewrite `hb` using `[heckeVec_dosetInd hρ hc hK hy]`. Establish `hn` using `card_ne_zero hK g`.

Use `⟨((P.finite_cosets_in_doset hK g).toFinset.card : ℂ)⁻¹ * c, ?_, ?_⟩` and prove the remaining obligations. Rewrite using `[mul_smul, ← ha, inv_smul_smul₀ hn]`. Rewrite using `[mul_smul, ← hb, inv_smul_smul₀ hn]`. Set `T : Subrepresentation π` to `⟨⨅ g, LinearMap.ker (idem hπ.1 hc ∘ₗ π g), fun g v hv => by`. Simplify using `only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢`.

Introduce `g'`. Simplify using `using hv (g' * g)⟩`. Establish `hT : T = ⊥` using `by haveI := hπ.2`. Use `(eq_bot_or_eq_top T).resolve_right fun e => hx0 ?_` and prove the remaining obligations. Establish `: x ∈ T` using `e ▸ trivial`.

Establish `h2 : idem hπ.1 hc (π 1 x) = 0` using `(Submodule.mem_iInf _).1 this 1`. Rewrite `h2` using `[map_one, Module.End.one_apply, idem_of_mem hπ.1 hc hx]`. Then use the resulting hypothesis. Establish `hker : LinearMap.ker (orbitMap ρ y).toLinearMap ≤ LinearMap.ker (orbitMap π x).toLinearMap` using `fun a h0 => by`. Establish `h0' : orbitMap ρ y a = 0` using `h0`. Establish `: orbitMap π x a ∈ T` using `(Submodule.mem_iInf _).2 fun g => by show idem hπ.1 hc (π g (orbitMap π x a)) = 0`.

Take `⟨c, h2, h3⟩` from `idem_orbitMap hπ.1 hρ hc h1 (Representation.leftRegular ℂ G g a)`. Rewrite `h3` using `[(orbitMap ρ y).isIntertwining, h0', map_zero, map_zero]`. Rewrite using `[← (orbitMap π x).isIntertwining, h2, (smul_eq_zero.1 h3.symm).resolve_right hy0, zero_smul]`. Rewrite `this` using `[hT]`. Conclude with `this`.

Set `f : (orbitMap ρ y).range.toSubmodule →ₗ[ℂ] V` to `Submodule.liftQ _ _ hker ∘ₗ (orbitMap ρ y).toLinearMap.quotKerEquivRange.symm.toLinearMap`. Establish `hf : ∀ a h, f ⟨orbitMap ρ y a, h⟩ = orbitMap π x a` using `fun a h => by`. Use `(orbitMap ρ y).toLinearMap.quotKerEquivRange_symm_apply_image a h` as an intermediate fact. Conclude with `(congrArg (Submodule.liftQ _ _ hker) this).trans rfl`. Use `⟨(orbitMap ρ y).range, ⟨f, fun g => LinearMap.ext ?_⟩, fun v => ?_⟩` and prove the remaining obligations.

Introduce and unpack `⟨_, a, rfl⟩`. Establish `e` using `(orbitMap ρ y).isIntertwining _ _ g a`. Establish `e' : (orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩ = ⟨orbitMap ρ y (Representation.leftRegular ℂ G g a), _, rfl⟩` using `Subtype.ext e.symm`. Use `show f ((orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩) = π g (f ⟨orbitMap ρ y a, a, rfl⟩)`. Rewrite using `[e']`.

Conclude with `(hf _ _).trans (((orbitMap π x).isIntertwining _ _ g a).trans (congrArg (π g) (hf _ _).symm))`. Take `⟨a, rfl⟩` from `orbitMap_surjective hπ.2 hx0 v`. Conclude with `⟨⟨_, a, rfl⟩, hf a _⟩`.
-/
theorem isSubquot_of_hecke_eigenvalues (G V W : Type) [Group G] [TopologicalSpace G] [IsTopologicalGroup G]
    [AddCommGroup V] [Module ℂ V] [AddCommGroup W] [Module ℂ W] (π : Representation ℂ G V) (ρ : Representation ℂ G W)
    (K : Subgroup G) (hc : IsCompact (K : Set G)) (hK : IsCommensurated K) (hπ : IsIrrSmooth π) (hρ : IsSmooth ρ)
    (x : V) (hx : x ∈ fixed π K) (hx0 : x ≠ 0) (y : W) (hy : y ∈ fixed ρ K) (hy0 : y ≠ 0)
    (h : ∀ h ∈ Hecke ℂ K, ∃ c : ℂ, heckeVec π K h x = c • x ∧ heckeVec ρ K h y = c • y) : IsSubquot π ρ := by
  have h1 : ∀ g, ∃ c : ℂ, idem hπ.1 hc (π g x) = c • x ∧ idem hρ hc (ρ g y) = c • y := fun g => by
    obtain ⟨c, ha, hb⟩ := h _ (Final.DosetIndMem G K ℂ g)
    rw [heckeVec_dosetInd hπ.1 hc hK hx] at ha
    rw [heckeVec_dosetInd hρ hc hK hy] at hb
    have hn := card_ne_zero hK g
    refine ⟨((P.finite_cosets_in_doset hK g).toFinset.card : ℂ)⁻¹ * c, ?_, ?_⟩
    · rw [mul_smul, ← ha, inv_smul_smul₀ hn]
    · rw [mul_smul, ← hb, inv_smul_smul₀ hn]
  let T : Subrepresentation π :=
    ⟨⨅ g, LinearMap.ker (idem hπ.1 hc ∘ₗ π g), fun g v hv => by
      simp only [Submodule.mem_iInf, LinearMap.mem_ker, LinearMap.comp_apply] at hv ⊢
      intro g'
      simpa using hv (g' * g)⟩
  have hT : T = ⊥ := by
    haveI := hπ.2
    refine (eq_bot_or_eq_top T).resolve_right fun e => hx0 ?_
    have : x ∈ T := e ▸ trivial
    have h2 : idem hπ.1 hc (π 1 x) = 0 := (Submodule.mem_iInf _).1 this 1
    rwa [map_one, Module.End.one_apply, idem_of_mem hπ.1 hc hx] at h2
  have hker : LinearMap.ker (orbitMap ρ y).toLinearMap ≤ LinearMap.ker (orbitMap π x).toLinearMap := fun a h0 => by
    have h0' : orbitMap ρ y a = 0 := h0
    have : orbitMap π x a ∈ T := (Submodule.mem_iInf _).2 fun g => by
      show idem hπ.1 hc (π g (orbitMap π x a)) = 0
      obtain ⟨c, h2, h3⟩ := idem_orbitMap hπ.1 hρ hc h1 (Representation.leftRegular ℂ G g a)
      rw [(orbitMap ρ y).isIntertwining, h0', map_zero, map_zero] at h3
      rw [← (orbitMap π x).isIntertwining, h2,
        (smul_eq_zero.1 h3.symm).resolve_right hy0, zero_smul]
    rw [hT] at this
    exact this
  let f : (orbitMap ρ y).range.toSubmodule →ₗ[ℂ] V :=
    Submodule.liftQ _ _ hker ∘ₗ (orbitMap ρ y).toLinearMap.quotKerEquivRange.symm.toLinearMap
  have hf : ∀ a h, f ⟨orbitMap ρ y a, h⟩ = orbitMap π x a := fun a h => by
    have := (orbitMap ρ y).toLinearMap.quotKerEquivRange_symm_apply_image a h
    exact (congrArg (Submodule.liftQ _ _ hker) this).trans rfl
  refine ⟨(orbitMap ρ y).range, ⟨f, fun g => LinearMap.ext ?_⟩, fun v => ?_⟩
  · rintro ⟨_, a, rfl⟩
    have e := (orbitMap ρ y).isIntertwining _ _ g a
    have e' : (orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩ =
        ⟨orbitMap ρ y (Representation.leftRegular ℂ G g a), _, rfl⟩ := Subtype.ext e.symm
    show f ((orbitMap ρ y).range.toRepresentation g ⟨orbitMap ρ y a, a, rfl⟩) = π g (f ⟨orbitMap ρ y a, a, rfl⟩)
    rw [e']
    exact (hf _ _).trans (((orbitMap π x).isIntertwining _ _ g a).trans (congrArg (π g) (hf _ _).symm))
  · obtain ⟨a, rfl⟩ := orbitMap_surjective hπ.2 hx0 v
    exact ⟨⟨_, a, rfl⟩, hf a _⟩

end GlobalTheory.LGrp.Zonal
