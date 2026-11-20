import Mathlib
import Development.AutomorphicSpectrum.Definitions.JetCones.SymCapRev
import Formalism.RealPlaceAnalysis.ThirdArithmeticHolds
import Formalism.RealPlaceAnalysis.FinalF
import Development.AutomorphicSpectrum.Proofs.JetProofs.EvFirst

open GlobalTheory.CompanionTheory.AlgRepEndIrreducible PI.UpqRep Matrix
open scoped InnerProductSpace

namespace GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap

/- English proof (translation)
Proceed by induction on `l generalizing y with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Establish `ha` using `hl a (by simp)`. Establish `ih'` using `ih (fun x hx => hl x (by simp [hx])) (D a.2 a.1 y)`.

Simplify using `only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons, List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, Prod.fst_swap, Prod.snd_swap]`. Rewrite using `[h _ _ ha, ih']`.
-/
theorem word_adj {n : ℕ} {ε : Fin n → Bool} {V : Type} [NormedAddCommGroup V] [InnerProductSpace ℂ V]
    {D : Fin n → Fin n → Module.End ℂ V} (h : KAdj ε D) (l : List (Fin n × Fin n))
    (hl : ∀ x ∈ l, ε x.1 = ε x.2) (x y : V) :
    ⟪(l.map fun x => D x.1 x.2).prod x, y⟫_ℂ =
      ⟪x, (((l.map Prod.swap).reverse).map fun x => D x.1 x.2).prod y⟫_ℂ := by
  induction l generalizing y with
  | nil => simp
  | cons a l ih =>
    have ha := hl a (by simp)
    have ih' := ih (fun x hx => hl x (by simp [hx])) (D a.2 a.1 y)
    simp only [List.map_cons, List.prod_cons, Module.End.mul_apply, List.reverse_cons,
      List.map_append, List.prod_append, List.map_nil, List.prod_nil, mul_one, Prod.fst_swap,
      Prod.snd_swap]
    rw [h _ _ ha, ih']

/- English proof (translation)
Set `A : G →ₗ[ℂ] V` to `(LinearMap.fst ℂ V V').comp G.subtype`. Establish `hA : Function.Injective A`. Rewrite using `[injective_iff_map_eq_zero]`. Introduce `g hg`. Establish `h1 : g.1.1 = 0` using `hg`.

Conclude with `Subtype.ext (Prod.ext h1 (hG _ g.2 h1))`. Set `U : Submodule ℂ V` to `LinearMap.range A`. Set `e : G ≃ₗ[ℂ] U` to `LinearEquiv.ofInjective A hA`. Set `T : V →ₗ[ℂ] V'` to `((LinearMap.snd ℂ V V').comp G.subtype).comp (e.symm.toLinearMap.comp (U.orthogonalProjectionOnto : V →ₗ[ℂ] U))`. Establish `key : ∀ g ∈ G, ∀ z ∈ Uᗮ, T (g.1 + z) = g.2`.

Introduce `g hg z hz`. Establish `h1 : U.orthogonalProjectionOnto (g.1 + z) = e ⟨g, hg⟩`. Rewrite using `[map_add, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hz, add_zero]`. Conclude with `Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨g, hg⟩)`. Use `show ((e.symm (U.orthogonalProjectionOnto (g.1 + z)) : G) : V × V').2 = g.2`.

Rewrite using `[h1, e.symm_apply_apply]`. Use `⟨T, fun g hg => by simpa using key g hg 0 (zero_mem _), ?_⟩` and prove the remaining obligations. Introduce `a b hab w`. Take `⟨u, hu, z, hz, rfl⟩` from `U.exists_add_mem_mem_orthogonal w`. Take `⟨g, rfl⟩` from `hu`.

Establish `hz' : D a b z ∈ Uᗮ`. Rewrite using `[Submodule.mem_orthogonal]`. Introduce and unpack `_ ⟨g', rfl⟩`. Rewrite using `[← h b a hab.symm]`. Conclude with `(Submodule.mem_orthogonal _ _).1 hz _ ⟨⟨_, hst b a hab.symm _ g'.2⟩, rfl⟩`.

Establish `h1` using `key _ (hst a b hab _ g.2) _ hz'`. Establish `h2` using `key _ g.2 _ hz`. Establish `h3 : A g = g.1.1` using `rfl`. Rewrite using `[h3, h2, map_add]`. Conclude with `h1`.
-/
theorem graph_extend {n : ℕ} {ε : Fin n → Bool} {V V' : Type} [NormedAddCommGroup V]
    [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [AddCommGroup V'] [Module ℂ V']
    {D : Fin n → Fin n → Module.End ℂ V} {D' : Fin n → Fin n → Module.End ℂ V'} (h : KAdj ε D)
    (G : Submodule ℂ (V × V')) (hG : ∀ g ∈ G, g.1 = 0 → g.2 = 0)
    (hst : ∀ a b, ε a = ε b → ∀ g ∈ G, (D a b g.1, D' a b g.2) ∈ G) :
    ∃ T : V →ₗ[ℂ] V', (∀ g ∈ G, T g.1 = g.2) ∧ KMap ε D D' T := by
  let A : G →ₗ[ℂ] V := (LinearMap.fst ℂ V V').comp G.subtype
  have hA : Function.Injective A := by
    rw [injective_iff_map_eq_zero]
    intro g hg
    have h1 : g.1.1 = 0 := hg
    exact Subtype.ext (Prod.ext h1 (hG _ g.2 h1))
  let U : Submodule ℂ V := LinearMap.range A
  let e : G ≃ₗ[ℂ] U := LinearEquiv.ofInjective A hA
  let T : V →ₗ[ℂ] V' := ((LinearMap.snd ℂ V V').comp G.subtype).comp
    (e.symm.toLinearMap.comp (U.orthogonalProjectionOnto : V →ₗ[ℂ] U))
  have key : ∀ g ∈ G, ∀ z ∈ Uᗮ, T (g.1 + z) = g.2 := by
    intro g hg z hz
    have h1 : U.orthogonalProjectionOnto (g.1 + z) = e ⟨g, hg⟩ := by
      rw [map_add, Submodule.orthogonalProjectionOnto_eq_zero_iff.2 hz, add_zero]
      exact Submodule.orthogonalProjectionOnto_mem_subspace_eq_self (e ⟨g, hg⟩)
    show ((e.symm (U.orthogonalProjectionOnto (g.1 + z)) : G) : V × V').2 = g.2
    rw [h1, e.symm_apply_apply]
  refine ⟨T, fun g hg => by simpa using key g hg 0 (zero_mem _), ?_⟩
  intro a b hab w
  obtain ⟨u, hu, z, hz, rfl⟩ := U.exists_add_mem_mem_orthogonal w
  obtain ⟨g, rfl⟩ := hu
  have hz' : D a b z ∈ Uᗮ := by
    rw [Submodule.mem_orthogonal]
    rintro _ ⟨g', rfl⟩
    rw [← h b a hab.symm]
    exact (Submodule.mem_orthogonal _ _).1 hz _ ⟨⟨_, hst b a hab.symm _ g'.2⟩, rfl⟩
  have h1 := key _ (hst a b hab _ g.2) _ hz'
  have h2 := key _ g.2 _ hz
  have h3 : A g = g.1.1 := rfl
  rw [h3, h2, map_add]
  exact h1

/- English proof (translation)
Introduce `n ε V V' _ _ _ _ _ D D' μ v v' hR hR' hA hA' hv hv' hv0`. Establish `vev` using `GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n ε V V' D D' μ v v' hR hR' hA hA' hv hv'`. Set `S : Set (V × V')` to `{g | ∃ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) ∧ g = ((l.map fun x => D x.1 x.2).prod v, (l.map fun x => D' x.1 x.2).prod v')}`. Establish `hin : ∀ g ∈ Submodule.span ℂ S, ∀ g' ∈ Submodule.span ℂ S, ⟪g.1, g'.1⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪g.2, g'.2⟫_ℂ * ⟪v, v⟫_ℂ`. Introduce `g hg g' hg'`.

Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy => simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul, hx, hy]`. Consider the case `smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_assoc, hx]`. Consider the case `mem x hx`.

Proceed by induction on `hg' using Submodule.span_induction with`. Consider the case `zero => simp`. Consider the case `add x y _ _ hx hy`. Simplify using `only [Prod.fst_add, Prod.snd_add, inner_add_right, add_mul, hx, hy]`. Consider the case `smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_assoc, hx]`.

Consider the case `mem y hy`. Take `⟨l, hl, rfl⟩` from `hx`. Take `⟨l', hl', rfl⟩` from `hy`. Use `vev ((l.map Prod.swap).reverse ++ l') (by` as an intermediate fact. Introduce `x hx`.

Break down `List.mem_append.1 hx with hx | hx` into its components or cases. Take `⟨y, hy, rfl⟩` from `List.mem_map.1 (List.mem_reverse.1 hx)`. Conclude with `(hl y hy).symm`. Conclude with `hl' x hx)`. Simplify using `only [List.map_append, List.prod_append, Module.End.mul_apply] at this`.

Simplify using `only`. Rewrite using `[word_adj hA l hl, word_adj hA' l hl, this]`. Take `⟨T, hT, hK⟩` from `graph_extend (D' := D') hA (Submodule.span ℂ S) (by`. Introduce `g hg h0`. Use `hin g hg g hg` as an intermediate fact.

Rewrite `this` using `[h0, inner_zero_left, zero_mul]`. Break down `mul_eq_zero.1 this.symm with h | h` into its components or cases. Conclude with `inner_self_eq_zero.1 h`. Conclude with `absurd (inner_self_eq_zero.1 h) hv0) (by`. Introduce `a b hab g hg`.

Proceed by induction on `hg using Submodule.span_induction with`. Consider the case `zero`. Simplify using `only [Prod.fst_zero, Prod.snd_zero, map_zero]`. Conclude with `Submodule.zero_mem _`. Consider the case `add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy`.

Consider the case `smul c x _ hx => simpa using Submodule.smul_mem _ c hx`. Consider the case `mem x hx`. Take `⟨l, hl, rfl⟩` from `hx`. Use `Submodule.subset_span ⟨(a, b) :: l, ?_, by simp⟩` and prove the remaining obligations. Introduce `x hx`.

Break down `List.mem_cons.1 hx with rfl | hx` into its components or cases. Conclude with `hab`. Conclude with `hl x hx)`. Conclude with `⟨T, hT (v, v') (Submodule.subset_span ⟨[], by simp, by simp⟩), hK⟩`.
-/
theorem hwmap : ∀ (n : ℕ) (ε : Fin n → Bool) (V V' : Type) [NormedAddCommGroup V] [InnerProductSpace ℂ V] [FiniteDimensional ℂ V] [NormedAddCommGroup V'] [InnerProductSpace ℂ V'] (D : Fin n → Fin n → Module.End ℂ V) (D' : Fin n → Fin n → Module.End ℂ V') (μ : Fin n → ℝ) (v : V) (v' : V'), KRel ε D → KRel ε D' → KAdj ε D → KAdj ε D' → Formalism.REAL.KHighest ε D μ v → Formalism.REAL.KHighest ε D' μ v' → v ≠ 0 → ∃ T : V →ₗ[ℂ] V', T v = v' ∧ KMap ε D D' T := by
  intro n ε V V' _ _ _ _ _ D D' μ v v' hR hR' hA hA' hv hv' hv0
  have vev := GlobalTheory.CompanionTheory.AlgRepEndIrreducible.Vev.vev_eq n ε V V' D D' μ v v' hR hR' hA hA' hv hv'
  let S : Set (V × V') := {g | ∃ l : List (Fin n × Fin n), (∀ x ∈ l, ε x.1 = ε x.2) ∧
    g = ((l.map fun x => D x.1 x.2).prod v, (l.map fun x => D' x.1 x.2).prod v')}
  have hin : ∀ g ∈ Submodule.span ℂ S, ∀ g' ∈ Submodule.span ℂ S,
      ⟪g.1, g'.1⟫_ℂ * ⟪v', v'⟫_ℂ = ⟪g.2, g'.2⟫_ℂ * ⟪v, v⟫_ℂ := by
    intro g hg g' hg'
    induction hg using Submodule.span_induction with
    | zero => simp
    | add x y _ _ hx hy => simp only [Prod.fst_add, Prod.snd_add, inner_add_left, add_mul, hx, hy]
    | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_left, mul_assoc, hx]
    | mem x hx =>
      induction hg' using Submodule.span_induction with
      | zero => simp
      | add x y _ _ hx hy =>
        simp only [Prod.fst_add, Prod.snd_add, inner_add_right, add_mul, hx, hy]
      | smul c x _ hx => simp only [Prod.smul_fst, Prod.smul_snd, inner_smul_right, mul_assoc, hx]
      | mem y hy =>
        obtain ⟨l, hl, rfl⟩ := hx
        obtain ⟨l', hl', rfl⟩ := hy
        have := vev ((l.map Prod.swap).reverse ++ l') (by
          intro x hx
          rcases List.mem_append.1 hx with hx | hx
          · obtain ⟨y, hy, rfl⟩ := List.mem_map.1 (List.mem_reverse.1 hx)
            exact (hl y hy).symm
          · exact hl' x hx)
        simp only [List.map_append, List.prod_append, Module.End.mul_apply] at this
        dsimp only
        rw [word_adj hA l hl, word_adj hA' l hl, this]
  obtain ⟨T, hT, hK⟩ := graph_extend (D' := D') hA (Submodule.span ℂ S) (by
    intro g hg h0
    have := hin g hg g hg
    rw [h0, inner_zero_left, zero_mul] at this
    rcases mul_eq_zero.1 this.symm with h | h
    · exact inner_self_eq_zero.1 h
    · exact absurd (inner_self_eq_zero.1 h) hv0) (by
    intro a b hab g hg
    induction hg using Submodule.span_induction with
    | zero =>
      simp only [Prod.fst_zero, Prod.snd_zero, map_zero]
      exact Submodule.zero_mem _
    | add x y _ _ hx hy => simpa using Submodule.add_mem _ hx hy
    | smul c x _ hx => simpa using Submodule.smul_mem _ c hx
    | mem x hx =>
      obtain ⟨l, hl, rfl⟩ := hx
      refine Submodule.subset_span ⟨(a, b) :: l, ?_, by simp⟩
      intro x hx
      rcases List.mem_cons.1 hx with rfl | hx
      · exact hab
      · exact hl x hx)
  exact ⟨T, hT (v, v') (Submodule.subset_span ⟨[], by simp, by simp⟩), hK⟩

end GlobalTheory.CompanionTheory.AlgRepEndIrreducible.HwMap
