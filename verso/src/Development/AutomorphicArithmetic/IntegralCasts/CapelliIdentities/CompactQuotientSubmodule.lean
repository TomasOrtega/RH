import Mathlib

/- English proof (translation)
Introduce `LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker`. Use `Fintype.ofFinite Q` as an intermediate fact. Set `s : Q → Z` to `Function.invFun f`. Establish `hs : ∀ z : Z, f (s (f z)) = f z` using `fun z => Function.invFun_eq ⟨z, rfl⟩`. Set `v : Q → W` to `fun q => (s q : W)`.

Set `N : Submodule O W` to `Submodule.span O (Set.range v)`. Establish `hNZ : N ≤ Z`. Use `Submodule.span_le.2 ?_` and prove the remaining obligations. Introduce and unpack `_ ⟨q, rfl⟩`. Conclude with `(s q).2`.

Establish `hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w`. Introduce `z hz`. Take `⟨w, hw, e⟩` from `hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])`. Use `⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩` and prove the remaining obligations. Rewrite using `[← e]`.

Simplify using `[v]`. Establish `hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w`. Introduce `n`. Proceed by induction on `n with`. Consider the case `zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩`.

Consider the case `succ n ih`. Introduce `z hz`. Take `⟨a, ha, w, hw, e⟩` from `ih z hz`. Take `⟨b, hb, u, hu, e'⟩` from `hstep w hw`. Use `⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩` and prove the remaining obligations.

Rewrite using `[e, e', smul_add, smul_smul, pow_succ, add_assoc]`. Establish `hcomp : IsCompact (N : Set W)`. Establish `hc : Continuous (fun c : Q → LL => ∑ q, c q • v q)` using `by fun_prop`. Establish `h1` using `(isCompact_univ_pi (fun _ : Q => hK)).image hc`. Use `h1 using 1` and compare the differences between its conclusion and the goal.

Use extensionality with `x`. Simplify using `only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨c, rfl⟩`. Conclude with `⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩`.

Introduce and unpack `⟨c, hc, rfl⟩ choose d hd using fun q => hc q (Set.mem_univ q)`. Conclude with `⟨d, by simp [← hd]⟩`. Establish `hZN : Z ≤ N`. Introduce `z hz`. Assume the negation of the conclusion as `hzN`.

Establish `hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ)` using `hcomp.isClosed.isOpen_compl.preimage (by fun_prop)`. Take `⟨n, hn⟩` from `hsmall _ (hopen.mem_nhds (by simpa using hzN))`. Take `⟨a, ha, w, hw, e⟩` from `hiter n z hz`. Apply `hn w hw` to reduce the goal to its premises. Establish `: z - p ^ n • w = a` using `by rw [e]; simp`.

Simplify `ha` using `[this]`. Rewrite using `[le_antisymm hZN hNZ]`. Conclude with `Submodule.fg_span (Set.finite_range v)`.
-/
theorem UpperTheory.compact_quotient_submodule :
    ∀ {LL O W Q : Type} [Field LL] [CommRing O] [Algebra O LL] [AddCommGroup W] [Module LL W] [Module O W]
        [IsScalarTower O LL W] [TopologicalSpace LL] [TopologicalSpace W] [ContinuousSMul LL W]
        [IsTopologicalAddGroup W] [T2Space W] [AddCommGroup Q] [Module O Q] [Finite Q]
        (Z : Submodule O W) (p : O) (f : Z →ₗ[O] Q),
        IsCompact (Set.range (algebraMap O LL)) →
        (∀ U ∈ nhds (0 : W), ∃ n : ℕ, ∀ z ∈ Z, p ^ n • z ∈ U) →
        (∀ z : Z, f z = 0 → ∃ w ∈ Z, (z : W) = p • w) →
        Z.FG := by
  intro LL O W Q _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ Z p f hK hsmall hker
  classical
  have := Fintype.ofFinite Q
  let s : Q → Z := Function.invFun f
  have hs : ∀ z : Z, f (s (f z)) = f z := fun z => Function.invFun_eq ⟨z, rfl⟩
  let v : Q → W := fun q => (s q : W)
  let N : Submodule O W := Submodule.span O (Set.range v)
  have hNZ : N ≤ Z := by
    refine Submodule.span_le.2 ?_
    rintro _ ⟨q, rfl⟩
    exact (s q).2
  have hstep : ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p • w := by
    intro z hz
    obtain ⟨w, hw, e⟩ := hker (⟨z, hz⟩ - s (f ⟨z, hz⟩)) (by rw [map_sub, hs, sub_self])
    refine ⟨v (f ⟨z, hz⟩), Submodule.subset_span ⟨_, rfl⟩, w, hw, ?_⟩
    rw [← e]
    simp [v]
  have hiter : ∀ n : ℕ, ∀ z ∈ Z, ∃ a ∈ N, ∃ w ∈ Z, z = a + p ^ n • w := by
    intro n
    induction n with
    | zero => exact fun z hz => ⟨0, N.zero_mem, z, hz, by simp⟩
    | succ n ih =>
      intro z hz
      obtain ⟨a, ha, w, hw, e⟩ := ih z hz
      obtain ⟨b, hb, u, hu, e'⟩ := hstep w hw
      refine ⟨a + p ^ n • b, N.add_mem ha (N.smul_mem _ hb), u, hu, ?_⟩
      rw [e, e', smul_add, smul_smul, pow_succ, add_assoc]
  have hcomp : IsCompact (N : Set W) := by
    have hc : Continuous (fun c : Q → LL => ∑ q, c q • v q) := by fun_prop
    have h1 := (isCompact_univ_pi (fun _ : Q => hK)).image hc
    convert h1 using 1
    ext x
    simp only [SetLike.mem_coe, N, Submodule.mem_span_range_iff_exists_fun, Set.mem_image]
    constructor
    · rintro ⟨c, rfl⟩
      exact ⟨fun q => algebraMap O LL (c q), fun q _ => ⟨c q, rfl⟩, by simp⟩
    · rintro ⟨c, hc, rfl⟩
      choose d hd using fun q => hc q (Set.mem_univ q)
      exact ⟨d, by simp [← hd]⟩
  have hZN : Z ≤ N := by
    intro z hz
    by_contra hzN
    have hopen : IsOpen ((fun x : W => z - x) ⁻¹' (N : Set W)ᶜ) :=
      hcomp.isClosed.isOpen_compl.preimage (by fun_prop)
    obtain ⟨n, hn⟩ := hsmall _ (hopen.mem_nhds (by simpa using hzN))
    obtain ⟨a, ha, w, hw, e⟩ := hiter n z hz
    apply hn w hw
    have : z - p ^ n • w = a := by rw [e]; simp
    simpa [this] using ha
  rw [le_antisymm hZN hNZ]
  exact Submodule.fg_span (Set.finite_range v)
