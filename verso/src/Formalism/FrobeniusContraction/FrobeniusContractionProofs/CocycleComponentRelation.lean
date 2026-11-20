import Formalism.FrobeniusContraction.Statement

namespace Formalism.WachCohomologyFacts.PExt

open Formalism.WachCohomologyFacts

variable {O A AA : Type} [CommRing O] [CommRing A] [Algebra O A] [CommRing AA] [Algebra O AA]
  [Algebra A AA] [IsScalarTower O A AA]
variable {V : Type} [AddCommGroup V] [Module AA V] [Module A V] [IsScalarTower A AA V]
  [Module O V] [IsScalarTower O AA V]

def extMap (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) : V × AA →ₗ[O] V × AA where
  toFun p := (f p.1 + g p.2 • w, g p.2)
  map_add' p p' := by
    simp only [Prod.fst_add, Prod.snd_add, map_add, add_smul, Prod.mk_add_mk, Prod.mk.injEq,
      and_true]
    abel
  map_smul' c p := by
    simp only [Prod.smul_fst, Prod.smul_snd, map_smul, RingHom.id_apply, Prod.smul_mk, smul_add,
      smul_assoc]

/- English proof (translation)
Both sides reduce to the same expression.
-/
@[simp] lemma extMap_apply (f : V →ₗ[O] V) (g : AA →ₐ[O] AA) (w : V) (p : V × AA) :
    extMap f g w p = (f p.1 + g p.2 • w, g p.2) := rfl

/- English proof (translation)
Establish `e : (fun w => ((w, (0 : AA)) : V × AA)) '' s = (LinearMap.inl AA V AA) '' s` using `rfl`. Rewrite using `[e, Submodule.span_image, hs]`. Conclude with `⟨v, Submodule.mem_top, rfl⟩`.
-/
lemma span_inl {s : Set V} (hs : Submodule.span AA s = ⊤) (v : V) :
    ((v, (0 : AA)) : V × AA) ∈ Submodule.span AA ((fun w => ((w, (0 : AA)) : V × AA)) '' s) := by
  have e : (fun w => ((w, (0 : AA)) : V × AA)) '' s = (LinearMap.inl AA V AA) '' s := rfl
  rw [e, Submodule.span_image, hs]
  exact ⟨v, Submodule.mem_top, rfl⟩

section

variable {B : Base O A} {E : Amb B AA} {n : ℕ} (W : WachDatum E n V)

def NN (i : ZMod n) : Submodule A (V × AA) := (W.N i).prod (1 : Submodule A AA)

/- English proof (translation)
Rewrite using `[NN, Submodule.mem_prod, Submodule.mem_one]`.
-/
lemma mem_NN (i : ZMod n) (p : V × AA) :
    p ∈ NN W i ↔ p.1 ∈ W.N i ∧ ∃ a0 : A, algebraMap A AA a0 = p.2 := by
  rw [NN, Submodule.mem_prod, Submodule.mem_one]

variable {W}

/- English proof (translation)
Take `⟨v, a⟩` from `p`. Take `⟨m, hm, hzm⟩` from `hz i`. Establish `key : ∀ a0 : A, (algebraMap A AA a0) • z i ∈ W.N i` using `fun a0 => by`. Rewrite using `[algebraMap_smul, hzm]`. Conclude with `(W.N i).smul_mem _ ((W.N i).smul_mem _ hm)`.

Simplify using `only [mem_NN, extMap_apply]`. Prove the components needed by the constructor for the conclusion. Introduce and unpack `⟨hv, a0, rfl⟩`. Use `⟨?_, B.γ a0, (E.γ_ext a0).symm⟩` and prove the remaining obligations. Rewrite using `[E.γ_ext]`.

Conclude with `(W.N i).add_mem ((W.γ_N i v).1 hv) (key _)`. Introduce and unpack `⟨hv, b, hb⟩`. Take `⟨a0, rfl⟩` from `B.γ_bij.2 b`. Establish `ha : a = algebraMap A AA a0` using `E.γ_bij.1 (by rw [E.γ_ext, hb])`. Substitute `ha` using the available equality.

Use `⟨?_, a0, rfl⟩` and prove the remaining obligations. Rewrite `hv` using `[E.γ_ext]`. Use `(W.N i).sub_mem hv (key (B.γ a0))` as an intermediate fact. Rewrite `this` using `[add_sub_cancel_right]`. Conclude with `(W.γ_N i v).2 this`.
-/
lemma ext_γN {z : ZMod n → V} (hz : ∀ j, ∃ m ∈ W.N j, z j = B.X • m) (i : ZMod n) (p : V × AA) :
    p ∈ NN W i ↔ extMap (W.γ i) E.γ (z i) p ∈ NN W i := by
  obtain ⟨v, a⟩ := p
  obtain ⟨m, hm, hzm⟩ := hz i
  have key : ∀ a0 : A, (algebraMap A AA a0) • z i ∈ W.N i := fun a0 => by
    rw [algebraMap_smul, hzm]; exact (W.N i).smul_mem _ ((W.N i).smul_mem _ hm)
  simp only [mem_NN, extMap_apply]
  constructor
  · rintro ⟨hv, a0, rfl⟩
    refine ⟨?_, B.γ a0, (E.γ_ext a0).symm⟩
    rw [E.γ_ext]; exact (W.N i).add_mem ((W.γ_N i v).1 hv) (key _)
  · rintro ⟨hv, b, hb⟩
    obtain ⟨a0, rfl⟩ := B.γ_bij.2 b
    have ha : a = algebraMap A AA a0 := E.γ_bij.1 (by rw [E.γ_ext, hb])
    subst ha
    refine ⟨?_, a0, rfl⟩
    rw [E.γ_ext] at hv
    have := (W.N i).sub_mem hv (key (B.γ a0))
    rw [add_sub_cancel_right] at this
    exact (W.γ_N i v).2 this

/- English proof (translation)
Introduce and unpack `⟨v, a⟩ hp`. Take `⟨hv, a0, rfl⟩` from `(mem_NN W i _).1 hp`. Take `⟨m, hm, hzm⟩` from `hz i`. Take `⟨x', hx', hx⟩` from `W.γ_sub i v hv`. Take `⟨d, hd⟩` from `Ideal.mem_span_singleton'.1 (B.γ_modX a0)`.

Use `⟨(x' + B.γ a0 • m, algebraMap A AA d), (mem_NN W i _).2 ⟨(W.N i).add_mem hx' ((W.N i).smul_mem _ hm), d, rfl⟩, ?_⟩` and prove the remaining obligations. Simplify using `only [extMap_apply, E.γ_ext, Prod.mk_sub_mk, Prod.smul_mk]`. Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only`. Rewrite using `[add_sub_right_comm, hx, hzm, algebraMap_smul, smul_add, smul_smul, smul_smul, mul_comm]`.

Simplify using `only`. Rewrite using `[← map_sub, ← hd, Algebra.smul_def, ← map_mul, mul_comm]`.
-/
lemma ext_γsub {z : ZMod n → V} (hz : ∀ j, ∃ m ∈ W.N j, z j = B.X • m) (i : ZMod n) :
    ∀ p ∈ NN W i, ∃ p' ∈ NN W i, extMap (W.γ i) E.γ (z i) p - p = B.X • p' := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W i _).1 hp
  obtain ⟨m, hm, hzm⟩ := hz i
  obtain ⟨x', hx', hx⟩ := W.γ_sub i v hv
  obtain ⟨d, hd⟩ := Ideal.mem_span_singleton'.1 (B.γ_modX a0)
  refine ⟨(x' + B.γ a0 • m, algebraMap A AA d),
    (mem_NN W i _).2 ⟨(W.N i).add_mem hx' ((W.N i).smul_mem _ hm), d, rfl⟩, ?_⟩
  simp only [extMap_apply, E.γ_ext, Prod.mk_sub_mk, Prod.smul_mk]
  refine Prod.ext ?_ ?_
  · simp only
    rw [add_sub_right_comm, hx, hzm, algebraMap_smul, smul_add, smul_smul, smul_smul, mul_comm]
  · simp only
    rw [← map_sub, ← hd, Algebra.smul_def, ← map_mul, mul_comm]

/- English proof (translation)
Use `set S := Submodule.span AA (Set.range (extMap (W.φ i) E.φ (y (i + 1))))`. Establish `hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' Set.range (W.φ i) ⊆ Set.range (extMap (W.φ i) E.φ (y (i + 1)))`. Introduce and unpack `_ ⟨_, ⟨w, rfl⟩, rfl⟩`. Conclude with `⟨(w, 0), by simp⟩`. Establish `h1 : ∀ v : V, ((v, 0) : V × AA) ∈ S` using `fun v => Submodule.span_mono hsub (span_inl (W.φ_span i) v)`.

Establish `h2 : ((y (i + 1), 1) : V × AA) ∈ S` using `Submodule.subset_span ⟨(0, 1), by simp⟩`. Rewrite using `[eq_top_iff]`. Introduce and unpack `⟨v, a⟩ -`. Use `add_mem (h1 (v - a • y (i + 1))) (S.smul_mem a h2)` as an intermediate fact. Simplify using `using this`.
-/
lemma ext_φspan (y : ZMod n → V) (i : ZMod n) :
    Submodule.span AA (Set.range (extMap (W.φ i) E.φ (y (i + 1)))) = ⊤ := by
  set S := Submodule.span AA (Set.range (extMap (W.φ i) E.φ (y (i + 1))))
  have hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' Set.range (W.φ i) ⊆
      Set.range (extMap (W.φ i) E.φ (y (i + 1))) := by
    rintro _ ⟨_, ⟨w, rfl⟩, rfl⟩
    exact ⟨(w, 0), by simp⟩
  have h1 : ∀ v : V, ((v, 0) : V × AA) ∈ S := fun v =>
    Submodule.span_mono hsub (span_inl (W.φ_span i) v)
  have h2 : ((y (i + 1), 1) : V × AA) ∈ S := Submodule.subset_span ⟨(0, 1), by simp⟩
  rw [eq_top_iff]
  rintro ⟨v, a⟩ -
  have := add_mem (h1 (v - a • y (i + 1))) (S.smul_mem a h2)
  simpa using this

/- English proof (translation)
Introduce and unpack `⟨v, a⟩ hp`. Take `⟨hv, a0, rfl⟩` from `(mem_NN W i _).1 hp`. Take `⟨k1, hk1⟩` from `W.φ_N i v hv`. Use `⟨k1 + k0, (mem_NN W _ _).2 ⟨?_, B.q ^ (k1 + k0) * B.φ a0, ?_⟩⟩` and prove the remaining obligations. Simplify using `only [extMap_apply, E.φ_ext, algebraMap_smul, smul_add, Prod.smul_fst]`.

Use `add_mem ?_ ?_` and prove the remaining obligations. Rewrite using `[pow_add, mul_comm, mul_smul]`. Conclude with `(W.N _).smul_mem _ hk1`. Rewrite using `[smul_comm, pow_add, mul_smul]`. Conclude with `(W.N _).smul_mem _ ((W.N _).smul_mem _ (hk0 _))`.

Simplify using `[extMap_apply, E.φ_ext, Algebra.smul_def]`.
-/
lemma ext_φN {y : ZMod n → V} {k0 : ℕ} (hk0 : ∀ j, B.q ^ k0 • y j ∈ W.N j) (i : ZMod n) :
    ∀ p ∈ NN W i, ∃ k : ℕ, B.q ^ k • extMap (W.φ i) E.φ (y (i + 1)) p ∈ NN W (i + 1) := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W i _).1 hp
  obtain ⟨k1, hk1⟩ := W.φ_N i v hv
  refine ⟨k1 + k0, (mem_NN W _ _).2 ⟨?_, B.q ^ (k1 + k0) * B.φ a0, ?_⟩⟩
  · simp only [extMap_apply, E.φ_ext, algebraMap_smul, smul_add, Prod.smul_fst]
    refine add_mem ?_ ?_
    · rw [pow_add, mul_comm, mul_smul]; exact (W.N _).smul_mem _ hk1
    · rw [smul_comm, pow_add, mul_smul]
      exact (W.N _).smul_mem _ ((W.N _).smul_mem _ (hk0 _))
  · simp [extMap_apply, E.φ_ext, Algebra.smul_def]

/- English proof (translation)
Introduce and unpack `⟨v, a⟩ hp`. Take `⟨hv, a0, rfl⟩` from `(mem_NN W _ _).1 hp`. Use `set S := Submodule.span A (extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA)))`. Establish `hw : B.q ^ k0 • (v - a0 • y (i + 1)) ∈ W.N (i + 1)`. Rewrite using `[smul_sub, smul_comm]`.

Conclude with `sub_mem ((W.N _).smul_mem _ hv) ((W.N _).smul_mem _ (hk0 _))`. Take `⟨k2, hk2⟩` from `W.N_φ i _ hw`. Establish `hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) ⊆ extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA))`. Introduce and unpack `_ ⟨_, ⟨w, hw, rfl⟩, rfl⟩`. Conclude with `⟨(w, 0), (mem_NN W i _).2 ⟨hw, 0, map_zero _⟩, by simp⟩`.

Establish `h1 : ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈ S`. Establish `e : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) = (LinearMap.inl A V AA) '' (W.φ i '' (W.N i : Set V))` using `rfl`. Establish `: ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈ Submodule.span A ((fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)))`. Rewrite using `[e, Submodule.span_image]`. Conclude with `⟨_, hk2, rfl⟩`.

Conclude with `Submodule.span_mono hsub this`. Establish `h2 : ((y (i + 1), 1) : V × AA) ∈ S` using `Submodule.subset_span ⟨(0, 1), (mem_NN W i _).2 ⟨zero_mem _, 1, map_one _⟩, by simp⟩`. Use `⟨k2 + k0, ?_⟩` and prove the remaining obligations. Use `add_mem h1 (S.smul_mem (B.q ^ (k2 + k0) * a0) h2)` as an intermediate fact. Use `this using 1` and compare the differences between its conclusion and the goal.

Use `Prod.ext ?_ ?_` and prove the remaining obligations. Simplify using `only [Prod.fst_add, Prod.smul_mk]`. Rewrite using `[smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, ← pow_add]`. Normalize the expressions using the abelian group laws. Simplify using `[Algebra.smul_def]`.
-/
lemma ext_Nφ {y : ZMod n → V} {k0 : ℕ} (hk0 : ∀ j, B.q ^ k0 • y j ∈ W.N j) (i : ZMod n) :
    ∀ p ∈ NN W (i + 1), ∃ k : ℕ, B.q ^ k • p ∈
      Submodule.span A (extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA))) := by
  rintro ⟨v, a⟩ hp
  obtain ⟨hv, a0, rfl⟩ := (mem_NN W _ _).1 hp
  set S := Submodule.span A (extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA)))
  have hw : B.q ^ k0 • (v - a0 • y (i + 1)) ∈ W.N (i + 1) := by
    rw [smul_sub, smul_comm]
    exact sub_mem ((W.N _).smul_mem _ hv) ((W.N _).smul_mem _ (hk0 _))
  obtain ⟨k2, hk2⟩ := W.N_φ i _ hw
  have hsub : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) ⊆
      extMap (W.φ i) E.φ (y (i + 1)) '' (NN W i : Set (V × AA)) := by
    rintro _ ⟨_, ⟨w, hw, rfl⟩, rfl⟩
    exact ⟨(w, 0), (mem_NN W i _).2 ⟨hw, 0, map_zero _⟩, by simp⟩
  have h1 : ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈ S := by
    have e : (fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V)) =
        (LinearMap.inl A V AA) '' (W.φ i '' (W.N i : Set V)) := rfl
    have : ((B.q ^ k2 • B.q ^ k0 • (v - a0 • y (i + 1)), (0 : AA)) : V × AA) ∈
        Submodule.span A ((fun w => ((w, (0 : AA)) : V × AA)) '' (W.φ i '' (W.N i : Set V))) := by
      rw [e, Submodule.span_image]
      exact ⟨_, hk2, rfl⟩
    exact Submodule.span_mono hsub this
  have h2 : ((y (i + 1), 1) : V × AA) ∈ S :=
    Submodule.subset_span ⟨(0, 1), (mem_NN W i _).2 ⟨zero_mem _, 1, map_one _⟩, by simp⟩
  refine ⟨k2 + k0, ?_⟩
  have := add_mem h1 (S.smul_mem (B.q ^ (k2 + k0) * a0) h2)
  convert this using 1
  refine Prod.ext ?_ ?_
  · simp only [Prod.fst_add, Prod.smul_mk]
    rw [smul_sub, smul_sub, smul_smul, smul_smul, smul_smul, ← pow_add]
    abel
  · simp [Algebra.smul_def]

end

end Formalism.WachCohomologyFacts.PExt
