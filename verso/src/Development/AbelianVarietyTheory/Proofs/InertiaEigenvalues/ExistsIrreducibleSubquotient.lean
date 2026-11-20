import Development.AbelianVarietyTheory.Definitions.GaloisGeometry.GoodIdempotentFixesOfOnlySeriesOfLabelActs
import Development.AbelianVarietyTheory.PublishedTheorems.GaloisCohomology₂.DepthZeroInertia

namespace GlobalTheory.QuotientGenerator

variable {G V : Type} [Group G] [AddCommGroup V] [Module ℂ V]

def gen (ρ : Representation ℂ G V) (x : V) : Subrepresentation ρ where
  toSubmodule := Submodule.span ℂ (Set.range fun g => ρ g x)
  apply_mem_toSubmodule g v hv := by
    have h : (Submodule.span ℂ (Set.range fun g => ρ g x)).map (ρ g) ≤ Submodule.span ℂ (Set.range fun g => ρ g x) := by
      rw [Submodule.map_span, Submodule.span_le]
      rintro _ ⟨_, ⟨h, rfl⟩, rfl⟩
      exact Submodule.subset_span ⟨g * h, by simp⟩
    exact h ⟨v, hv, rfl⟩

/- English proof (translation)
The claim follows from `Submodule.subset_span ⟨1, by simp⟩`.
-/
theorem self_mem_gen (ρ : Representation ℂ G V) (x : V) : x ∈ (gen ρ x).toSubmodule :=
  Submodule.subset_span ⟨1, by simp⟩

/- English proof (translation)
Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨v, hv⟩ -`. Establish `h : (gen ρ x).toSubmodule ≤ M.toSubmodule.map (gen ρ x).toSubmodule.subtype`. Express the relevant statement in the definitionally equal form `Submodule.span ℂ _ ≤ _`. Rewrite using `[Submodule.span_le]`.

Introduce and unpack `_ ⟨g, rfl⟩`. Conclude with `⟨_, M.apply_mem_toSubmodule g hx, rfl⟩`. Take `⟨w, hw, rfl⟩` from `h hv`. Conclude with `hw`.
-/
theorem eq_top_of_mem (ρ : Representation ℂ G V) (x : V) (M : Subrepresentation (gen ρ x).toRepresentation)
    (hx : (⟨x, self_mem_gen ρ x⟩ : (gen ρ x).toSubmodule) ∈ M.toSubmodule) : M.toSubmodule = ⊤ := by
  rw [eq_top_iff]
  rintro ⟨v, hv⟩ -
  have h : (gen ρ x).toSubmodule ≤ M.toSubmodule.map (gen ρ x).toSubmodule.subtype := by
    change Submodule.span ℂ _ ≤ _
    rw [Submodule.span_le]
    rintro _ ⟨g, rfl⟩
    exact ⟨_, M.apply_mem_toSubmodule g hx, rfl⟩
  obtain ⟨w, hw, rfl⟩ := h hv
  exact hw

/- English proof (translation)
Establish `key` using `zorn_le_nonempty₀ {N : Subrepresentation ρ | x ∉ N.toSubmodule} ?_ ⊥ hx`. Take `⟨m, -, hm⟩` from `key`. Conclude with `⟨m, hm⟩`. Introduce `c hc hch y hy`. Establish `hne : (Subrepresentation.toSubmodule '' c).Nonempty` using `⟨_, y, hy, rfl⟩`.

Establish `hd : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c)`. Introduce and unpack `_ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩`. Take `⟨d, hd, h1, h2⟩` from `hch.directedOn a ha b hb`. Conclude with `⟨_, ⟨d, hd, rfl⟩, h1, h2⟩`. Use `⟨⟨sSup (Subrepresentation.toSubmodule '' c), fun g v hv => ?_⟩, fun h => ?_, fun z hz => ?_⟩` and prove the remaining obligations.

Rewrite `hv`, the goal using `[Submodule.mem_sSup_of_directed hne hd]`. Take `⟨_, ⟨a, ha, rfl⟩, hv⟩` from `hv`. Conclude with `⟨_, ⟨a, ha, rfl⟩, a.apply_mem_toSubmodule g hv⟩`. Take `⟨_, ⟨a, ha, rfl⟩, hv⟩` from `(Submodule.mem_sSup_of_directed hne hd).1 h`. Conclude with `hc ha hv`.

Conclude with `(le_sSup ⟨z, hz, rfl⟩ : z.toSubmodule ≤ sSup (Subrepresentation.toSubmodule '' c))`.
-/
theorem exists_maximal (ρ : Representation ℂ G V) (x : V) (hx : x ≠ 0) :
    ∃ M : Subrepresentation ρ, Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M := by
  have key := zorn_le_nonempty₀ {N : Subrepresentation ρ | x ∉ N.toSubmodule} ?_ ⊥ hx
  · obtain ⟨m, -, hm⟩ := key
    exact ⟨m, hm⟩
  intro c hc hch y hy
  have hne : (Subrepresentation.toSubmodule '' c).Nonempty := ⟨_, y, hy, rfl⟩
  have hd : DirectedOn (· ≤ ·) (Subrepresentation.toSubmodule '' c) := by
    rintro _ ⟨a, ha, rfl⟩ _ ⟨b, hb, rfl⟩
    obtain ⟨d, hd, h1, h2⟩ := hch.directedOn a ha b hb
    exact ⟨_, ⟨d, hd, rfl⟩, h1, h2⟩
  refine ⟨⟨sSup (Subrepresentation.toSubmodule '' c), fun g v hv => ?_⟩, fun h => ?_, fun z hz => ?_⟩
  · rw [Submodule.mem_sSup_of_directed hne hd] at hv ⊢
    obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := hv
    exact ⟨_, ⟨a, ha, rfl⟩, a.apply_mem_toSubmodule g hv⟩
  · obtain ⟨_, ⟨a, ha, rfl⟩, hv⟩ := (Submodule.mem_sSup_of_directed hne hd).1 h
    exact hc ha hv
  · exact (le_sSup ⟨z, hz, rfl⟩ : z.toSubmodule ≤ sSup (Subrepresentation.toSubmodule '' c))

noncomputable def quot (ρ : Representation ℂ G V) (M : Subrepresentation ρ) : Representation ℂ G (V ⧸ M.toSubmodule) :=
  ρ.quotient M.toSubmodule fun g _ hv => M.apply_mem_toSubmodule g hv

/- English proof (translation)
Both sides reduce to the same expression.
-/
theorem quot_mk (ρ : Representation ℂ G V) (M : Subrepresentation ρ) (g : G) (v : V) :
    quot ρ M g (M.toSubmodule.mkQ v) = M.toSubmodule.mkQ (ρ g v) := rfl

/- English proof (translation)
Establish `hx0 : M.toSubmodule.mkQ x ≠ 0` using `fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h)`. Use `haveI : Nontrivial (Subrepresentation (quot ρ M)) := ⟨⟨⊥, ⊤, fun h => hx0 (by`. Establish `h1 : M.toSubmodule.mkQ x ∈ (⊤ : Subrepresentation (quot ρ M)).toSubmodule` using `Submodule.mem_top`. Rewrite `h1` using `[← h]`. Conclude with `h1)⟩⟩`.

Use `⟨fun T => ?_⟩` and prove the remaining obligations. Set `T' : Subrepresentation ρ` to `⟨T.toSubmodule.comap M.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩`. Distinguish the cases in `hx : x ∈ T'.toSubmodule`. Use `right`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises.

Use `eq_top_iff.2 fun w _ => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `M.toSubmodule.mkQ_surjective w`. Establish `: v ∈ T'.toSubmodule` using `by rw [hcyc T' hx]; trivial`. Conclude with `this`. Use `left`.

Establish `hle : M ≤ T'` using `fun v hv => by`. Express the relevant statement in the definitionally equal form `M.toSubmodule.mkQ v ∈ T.toSubmodule`. Establish `: M.toSubmodule.mkQ v = 0` using `(Submodule.Quotient.mk_eq_zero _).2 hv`. Rewrite using `[this]`. Conclude with `zero_mem _`.

Establish `hge : T' ≤ M` using `hM.2 hx hle`. Apply `Subrepresentation.toSubmodule_injective` to reduce the goal to its premises. Use `eq_bot_iff.2 fun w hw => ?_` and prove the remaining obligations. Take `⟨v, rfl⟩` from `M.toSubmodule.mkQ_surjective w`. Conclude with `(Submodule.Quotient.mk_eq_zero _).2 (hge (show v ∈ T' from hw))`.
-/
theorem quot_irreducible (ρ : Representation ℂ G V) (x : V)
    (hcyc : ∀ N : Subrepresentation ρ, x ∈ N.toSubmodule → N.toSubmodule = ⊤) (M : Subrepresentation ρ)
    (hM : Maximal (fun N : Subrepresentation ρ => x ∉ N.toSubmodule) M) : (quot ρ M).IsIrreducible := by
  have hx0 : M.toSubmodule.mkQ x ≠ 0 := fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h)
  haveI : Nontrivial (Subrepresentation (quot ρ M)) := ⟨⟨⊥, ⊤, fun h => hx0 (by
    have h1 : M.toSubmodule.mkQ x ∈ (⊤ : Subrepresentation (quot ρ M)).toSubmodule := Submodule.mem_top
    rw [← h] at h1
    exact h1)⟩⟩
  refine ⟨fun T => ?_⟩
  let T' : Subrepresentation ρ := ⟨T.toSubmodule.comap M.toSubmodule.mkQ, fun g v hv => T.apply_mem_toSubmodule g hv⟩
  by_cases hx : x ∈ T'.toSubmodule
  · right
    apply Subrepresentation.toSubmodule_injective
    refine eq_top_iff.2 fun w _ => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    have : v ∈ T'.toSubmodule := by rw [hcyc T' hx]; trivial
    exact this
  · left
    have hle : M ≤ T' := fun v hv => by
      change M.toSubmodule.mkQ v ∈ T.toSubmodule
      have : M.toSubmodule.mkQ v = 0 := (Submodule.Quotient.mk_eq_zero _).2 hv
      rw [this]
      exact zero_mem _
    have hge : T' ≤ M := hM.2 hx hle
    apply Subrepresentation.toSubmodule_injective
    refine eq_bot_iff.2 fun w hw => ?_
    obtain ⟨v, rfl⟩ := M.toSubmodule.mkQ_surjective w
    exact (Submodule.Quotient.mk_eq_zero _).2 (hge (show v ∈ T' from hw))

/- English proof (translation)
Set `x' : (gen ρ x).toSubmodule` to `⟨x, self_mem_gen ρ x⟩`. Establish `hx' : x' ≠ 0` using `fun h => hx (congrArg Subtype.val h)`. Take `⟨M, hM⟩` from `exists_maximal (gen ρ x).toRepresentation x' hx'`. Use `⟨_, inferInstance, inferInstance, quot _ M, M.toSubmodule.mkQ x', quot_irreducible _ x' (eq_top_of_mem ρ x) M hM, ⟨gen ρ x, ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext fun v => (quot_mk _ M g v).symm⟩, M.toSubmodule.mkQ_surjective⟩, fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _) …` and prove the remaining obligations. Establish `h' : ∑ i ∈ s, c i • (gen ρ x).toRepresentation (f i) x' = b • x'`.

Apply `Subtype.ext` to reduce the goal to its premises. Rewrite using `[AddSubmonoidClass.coe_finsetSum]`. Conclude with `h`. Establish `h2` using `congrArg M.toSubmodule.mkQ h'`. Rewrite `h2` using `[map_sum, map_smul]`.

Simplify `h2` using `only [map_smul, quot_mk]`.
-/
theorem exists_irreducible_subquotient (G V : Type) [Group G] [AddCommGroup V] [Module ℂ V] (ρ : Representation ℂ G V) (x : V)
    (hx : x ≠ 0) :
    ∃ (Y : Type) (_ : AddCommGroup Y) (_ : Module ℂ Y) (τ : Representation ℂ G Y) (y : Y),
      Representation.IsIrreducible τ ∧ GlobalTheory.SmGL.IsSubquotient τ ρ ∧ y ≠ 0 ∧
      ∀ (ι : Type) (s : Finset ι) (f : ι → G) (c : ι → ℂ) (b : ℂ),
        ∑ i ∈ s, c i • ρ (f i) x = b • x → ∑ i ∈ s, c i • τ (f i) y = b • y := by
  let x' : (gen ρ x).toSubmodule := ⟨x, self_mem_gen ρ x⟩
  have hx' : x' ≠ 0 := fun h => hx (congrArg Subtype.val h)
  obtain ⟨M, hM⟩ := exists_maximal (gen ρ x).toRepresentation x' hx'
  refine ⟨_, inferInstance, inferInstance, quot _ M, M.toSubmodule.mkQ x',
    quot_irreducible _ x' (eq_top_of_mem ρ x) M hM,
    ⟨gen ρ x, ⟨M.toSubmodule.mkQ, fun g => LinearMap.ext fun v => (quot_mk _ M g v).symm⟩, M.toSubmodule.mkQ_surjective⟩,
    fun h => hM.1 ((Submodule.Quotient.mk_eq_zero _).1 h), fun ι s f c b h => ?_⟩
  have h' : ∑ i ∈ s, c i • (gen ρ x).toRepresentation (f i) x' = b • x' := by
    apply Subtype.ext
    rw [AddSubmonoidClass.coe_finsetSum]
    exact h
  have h2 := congrArg M.toSubmodule.mkQ h'
  rw [map_sum, map_smul] at h2
  simpa only [map_smul, quot_mk] using h2

end GlobalTheory.QuotientGenerator
