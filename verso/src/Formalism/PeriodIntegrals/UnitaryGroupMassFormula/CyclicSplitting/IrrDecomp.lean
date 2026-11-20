import Mathlib

set_option autoImplicit false

namespace CycSplitWork

open scoped BigOperators

section

variable {G : Type} [Group G] [Fintype G] {L : Type} [Field L] [CharZero L]

noncomputable def transportRep {V : Type} [AddCommGroup V] [Module L V] {n : ℕ} (e : V ≃ₗ[L] (Fin n → L))
    (σ : Representation L G V) : Representation L G (Fin n → L) where
  toFun g := e.conj (σ g)
  map_one' := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply]
  map_mul' g h := LinearMap.ext fun v => by simp [LinearEquiv.conj_apply]

/- English proof (translation)
Use `show LinearMap.trace L (Fin n → L) (e.conj (σ g)) = LinearMap.trace L V (σ g)`. Conclude with `LinearMap.trace_conj' (σ g) e`.
-/
theorem transportRep_character {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V] {n : ℕ}
    (e : V ≃ₗ[L] (Fin n → L)) (σ : Representation L G V) (g : G) :
    (transportRep e σ).character g = σ.character g := by
  show LinearMap.trace L (Fin n → L) (e.conj (σ g)) = LinearMap.trace L V (σ g)
  exact LinearMap.trace_conj' (σ g) e

/- English proof (translation)
Establish `he : ∀ (g : G) (v : V), e (σ g v) = transportRep e σ g (e v)` using `fun g v => by show _ = (e.conj (σ g)) (e v)`. Simplify using `[LinearEquiv.conj_apply]`. Establish `he' : ∀ (g : G) (x : Fin n → L), e.symm (transportRep e σ g x) = σ g (e.symm x)` using `fun g x => by`. Rewrite using `[LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]`. Set `φ : Subrepresentation (transportRep e σ) ≃o Subrepresentation σ` to `{ toFun := fun U => ⟨U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)), by`.

Introduce `g v hv`. Use `show e (σ g v) ∈ U.toSubmodule`. Rewrite using `[he]`. Conclude with `U.apply_mem_toSubmodule g hv⟩`. Use `invFun := fun W => ⟨W.toSubmodule.comap (e.symm : (Fin n → L) →ₗ[L] V), by`.

Introduce `g x hx`. Use `show e.symm (transportRep e σ g x) ∈ W.toSubmodule`. Rewrite using `[he']`. Conclude with `W.apply_mem_toSubmodule g hx⟩`. Use `left_inv := fun U => Subrepresentation.ext (Submodule.ext fun x => by simp)`.

Use `right_inv := fun W => Subrepresentation.ext (Submodule.ext fun x => by simp)`. Use the proof step `map_rel_iff' := fun {U U'} => by show U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)) ≤ U'.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)) ↔ U.toSubmodule ≤ U'.toSubmodule`. Prove the components needed by the constructor for the conclusion. Introduce `h x hx`. Establish `h1 : e.symm x ∈ U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L))`.

Simplify `hx` using `[Submodule.mem_comap]`. Simplify `h h1` using `[Submodule.mem_comap]`. Introduce `h x hx`. Conclude with `h hx }`. Use `haveI : IsSimpleOrder (Subrepresentation σ) := hσ`.

Conclude with `OrderIso.isSimpleOrder φ`.
-/
theorem transportRep_irreducible {V : Type} [AddCommGroup V] [Module L V] {n : ℕ}
    (e : V ≃ₗ[L] (Fin n → L)) (σ : Representation L G V) (hσ : σ.IsIrreducible) :
    (transportRep e σ).IsIrreducible := by
  have he : ∀ (g : G) (v : V), e (σ g v) = transportRep e σ g (e v) := fun g v => by
    show _ = (e.conj (σ g)) (e v)
    simp [LinearEquiv.conj_apply]
  have he' : ∀ (g : G) (x : Fin n → L), e.symm (transportRep e σ g x) = σ g (e.symm x) := fun g x => by
    rw [LinearEquiv.symm_apply_eq, he, LinearEquiv.apply_symm_apply]
  let φ : Subrepresentation (transportRep e σ) ≃o Subrepresentation σ :=
    { toFun := fun U => ⟨U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)), by
          intro g v hv
          show e (σ g v) ∈ U.toSubmodule
          rw [he]
          exact U.apply_mem_toSubmodule g hv⟩
      invFun := fun W => ⟨W.toSubmodule.comap (e.symm : (Fin n → L) →ₗ[L] V), by
          intro g x hx
          show e.symm (transportRep e σ g x) ∈ W.toSubmodule
          rw [he']
          exact W.apply_mem_toSubmodule g hx⟩
      left_inv := fun U => Subrepresentation.ext (Submodule.ext fun x => by simp)
      right_inv := fun W => Subrepresentation.ext (Submodule.ext fun x => by simp)
      map_rel_iff' := fun {U U'} => by
        show U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)) ≤
            U'.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)) ↔ U.toSubmodule ≤ U'.toSubmodule
        constructor
        · intro h x hx
          have h1 : e.symm x ∈ U.toSubmodule.comap (e : V →ₗ[L] (Fin n → L)) := by
            simpa [Submodule.mem_comap] using hx
          simpa [Submodule.mem_comap] using h h1
        · intro h x hx
          exact h hx }
  haveI : IsSimpleOrder (Subrepresentation σ) := hσ
  exact OrderIso.isSimpleOrder φ

def ListDecomp {V : Type} [AddCommGroup V] [Module L V] (σ : Representation L G V) : Prop :=
  ∃ l : List (Σ d : ℕ, Representation L G (Fin d → L)),
    (∀ x ∈ l, x.2.IsIrreducible) ∧ ∀ g : G, σ.character g = (l.map fun x => x.2.character g).sum

/- English proof (translation)
Set `e` to `Submodule.prodEquivOfIsCompl W.toSubmodule C.toSubmodule hc`. Establish `key : e.symm.conj (σ g) = LinearMap.prodMap (W.toRepresentation g) (C.toRepresentation g)`. Apply `LinearMap.ext` to reduce the goal to its premises. Introduce `x`. Rewrite using `[LinearEquiv.conj_apply]`.

Simplify using `only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm, LinearMap.prodMap_apply]`. Rewrite using `[e.symm_apply_eq]`. Use `show σ g ((x.1 : V) + (x.2 : V)) = ((W.toRepresentation g x.1 : W.toSubmodule) : V) + ((C.toRepresentation g x.2 : C.toSubmodule) : V)`. Rewrite using `[map_add]`. Both sides reduce to the same expression.

Establish `h1 : σ.character g = LinearMap.trace L _ (e.symm.conj (σ g))` using `by show LinearMap.trace L V (σ g) = _`. Rewrite using `[LinearMap.trace_conj']`. Rewrite using `[h1, key, LinearMap.trace_prodMap']`. Both sides reduce to the same expression.
-/
theorem character_eq_add {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (σ : Representation L G V) (W C : Subrepresentation σ) (hc : IsCompl W.toSubmodule C.toSubmodule)
    (g : G) : σ.character g = W.toRepresentation.character g + C.toRepresentation.character g := by
  classical
  let e := Submodule.prodEquivOfIsCompl W.toSubmodule C.toSubmodule hc
  have key : e.symm.conj (σ g) =
      LinearMap.prodMap (W.toRepresentation g) (C.toRepresentation g) := by
    apply LinearMap.ext
    intro x
    rw [LinearEquiv.conj_apply]
    simp only [LinearMap.comp_apply, LinearEquiv.coe_coe, LinearEquiv.symm_symm,
      LinearMap.prodMap_apply]
    rw [e.symm_apply_eq]
    show σ g ((x.1 : V) + (x.2 : V)) =
      ((W.toRepresentation g x.1 : W.toSubmodule) : V) + ((C.toRepresentation g x.2 : C.toSubmodule) : V)
    rw [map_add]
    rfl
  have h1 : σ.character g = LinearMap.trace L _ (e.symm.conj (σ g)) := by
    show LinearMap.trace L V (σ g) = _
    rw [LinearMap.trace_conj']
  rw [h1, key, LinearMap.trace_prodMap']
  rfl

/- English proof (translation)
Rewrite using `[map_mul]`. Both sides reduce to the same expression.
-/
private theorem representation_mul_apply {V : Type} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (g h : G) (x : V) : σ (g * h) x = σ g (σ h x) := by
  rw [map_mul]
  rfl

/- English proof (translation)
Rewrite using `[← representation_mul_apply, mul_inv_cancel, map_one]`. Both sides reduce to the same expression.
-/
private theorem representation_apply_inv_apply {V : Type} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (g : G) (x : V) : σ g (σ g⁻¹ x) = x := by
  rw [← representation_mul_apply, mul_inv_cancel, map_one]
  rfl

/- English proof (translation)
Rewrite using `[← representation_mul_apply, inv_mul_cancel, map_one]`. Both sides reduce to the same expression.
-/
private theorem representation_inv_apply_apply {V : Type} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (g : G) (x : V) : σ g⁻¹ (σ g x) = x := by
  rw [← representation_mul_apply, inv_mul_cancel, map_one]
  rfl

/- English proof (translation)
Take `⟨q, hq⟩` from `Submodule.exists_isCompl W.toSubmodule`. Set `π : V →ₗ[L] V` to `W.toSubmodule.subtype ∘ₗ W.toSubmodule.projectionOnto q hq`. Establish `hπW : ∀ v, π v ∈ W.toSubmodule` using `fun v => (W.toSubmodule.projectionOnto q hq v).2`. Establish `hπfix : ∀ w ∈ W.toSubmodule, π w = w` using `fun w hw => by`. Conclude with `congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨w, hw⟩)`.

Set `A : V →ₗ[L] V` to `((Fintype.card G : L)⁻¹) • ∑ g : G, σ g⁻¹ ∘ₗ π ∘ₗ σ g`. Establish `hA : ∀ v, A v = ((Fintype.card G : L)⁻¹) • ∑ g : G, σ g⁻¹ (π (σ g v))` using `fun v => by`. Rewrite using `[LinearMap.smul_apply, LinearMap.sum_apply]`. Both sides reduce to the same expression. Establish `hAW : ∀ v, A v ∈ W.toSubmodule` using `fun v => by`.

Rewrite using `[hA]`. Conclude with `W.toSubmodule.smul_mem _ (W.toSubmodule.sum_mem fun g _ => W.apply_mem_toSubmodule g⁻¹ (hπW _))`. Establish `hfix : ∀ w ∈ W.toSubmodule, A w = w` using `fun w hw => by`. Rewrite using `[hA]`. Establish `h1 : ∀ g : G, σ g⁻¹ (π (σ g w)) = w` using `fun g => by`.

Rewrite using `[hπfix _ (W.apply_mem_toSubmodule g hw), representation_inv_apply_apply]`. Simplify using `only [h1, Finset.sum_const, Finset.card_univ]`. Establish `hne : (Fintype.card G : L) ≠ 0` using `Nat.cast_ne_zero.mpr Fintype.card_ne_zero`. Rewrite using `[← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hne, one_smul]`. Establish `hequiv : ∀ (h : G) (v : V), A (σ h v) = σ h (A v)` using `fun h v => by`.

Rewrite using `[hA, hA, map_smul, map_sum]`. Use `congr 1`. Use `Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)` and prove the remaining obligations. Simplify using `only [Equiv.coe_mulRight]`. Rewrite using `[mul_inv_rev, representation_mul_apply σ h⁻¹ g⁻¹, representation_mul_apply σ g h, representation_apply_inv_apply]`.

Conclude with `⟨LinearMap.codRestrict W.toSubmodule A hAW, fun w => Subtype.ext (hfix w w.2), fun g v => hequiv g v⟩`.
-/
private theorem subrepresentation_exists_equivariant_projection {V : Type} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (W : Subrepresentation σ) :
    ∃ P : V →ₗ[L] W.toSubmodule, (∀ w : W.toSubmodule, P w = w) ∧
      ∀ (g : G) (v : V), (P (σ g v) : V) = σ g (P v) := by
  classical
  obtain ⟨q, hq⟩ := Submodule.exists_isCompl W.toSubmodule
  let π : V →ₗ[L] V := W.toSubmodule.subtype ∘ₗ W.toSubmodule.projectionOnto q hq
  have hπW : ∀ v, π v ∈ W.toSubmodule := fun v => (W.toSubmodule.projectionOnto q hq v).2
  have hπfix : ∀ w ∈ W.toSubmodule, π w = w := fun w hw => by
    exact congrArg Subtype.val (Submodule.projectionOnto_apply_left hq ⟨w, hw⟩)
  let A : V →ₗ[L] V := ((Fintype.card G : L)⁻¹) • ∑ g : G, σ g⁻¹ ∘ₗ π ∘ₗ σ g
  have hA : ∀ v, A v = ((Fintype.card G : L)⁻¹) • ∑ g : G, σ g⁻¹ (π (σ g v)) := fun v => by
    rw [LinearMap.smul_apply, LinearMap.sum_apply]
    rfl
  have hAW : ∀ v, A v ∈ W.toSubmodule := fun v => by
    rw [hA]
    exact W.toSubmodule.smul_mem _
      (W.toSubmodule.sum_mem fun g _ => W.apply_mem_toSubmodule g⁻¹ (hπW _))
  have hfix : ∀ w ∈ W.toSubmodule, A w = w := fun w hw => by
    rw [hA]
    have h1 : ∀ g : G, σ g⁻¹ (π (σ g w)) = w := fun g => by
      rw [hπfix _ (W.apply_mem_toSubmodule g hw), representation_inv_apply_apply]
    simp only [h1, Finset.sum_const, Finset.card_univ]
    have hne : (Fintype.card G : L) ≠ 0 := Nat.cast_ne_zero.mpr Fintype.card_ne_zero
    rw [← Nat.cast_smul_eq_nsmul L, smul_smul, inv_mul_cancel₀ hne, one_smul]
  have hequiv : ∀ (h : G) (v : V), A (σ h v) = σ h (A v) := fun h v => by
    rw [hA, hA, map_smul, map_sum]
    congr 1
    refine Fintype.sum_equiv (Equiv.mulRight h) _ _ (fun g => ?_)
    simp only [Equiv.coe_mulRight]
    rw [mul_inv_rev, representation_mul_apply σ h⁻¹ g⁻¹, representation_mul_apply σ g h, representation_apply_inv_apply]
  exact ⟨LinearMap.codRestrict W.toSubmodule A hAW, fun w => Subtype.ext (hfix w w.2),
    fun g v => hequiv g v⟩

/- English proof (translation)
Take `⟨P, hP, hPeq⟩` from `subrepresentation_exists_equivariant_projection σ W`. Use `⟨⟨LinearMap.ker P, ?_⟩, LinearMap.isCompl_of_proj hP⟩` and prove the remaining obligations. Introduce `g v hv`. Rewrite `hv`, the goal using `[LinearMap.mem_ker]`. Apply `Subtype.ext` to reduce the goal to its premises.

Rewrite using `[hPeq, hv]`. Simplify using the standard rewrite rules.
-/
private theorem subrepresentation_exists_isCompl_subrepresentation {V : Type} [AddCommGroup V] [Module L V]
    (σ : Representation L G V) (W : Subrepresentation σ) :
    ∃ C : Subrepresentation σ, IsCompl W.toSubmodule C.toSubmodule := by
  obtain ⟨P, hP, hPeq⟩ := subrepresentation_exists_equivariant_projection σ W
  refine ⟨⟨LinearMap.ker P, ?_⟩, LinearMap.isCompl_of_proj hP⟩
  intro g v hv
  rw [LinearMap.mem_ker] at hv ⊢
  apply Subtype.ext
  rw [hPeq, hv]
  simp

/- English proof (translation)
Introduce `n`. Proceed by induction on `n using Nat.strong_induction_on with`. Consider the case `_ n ih`. Introduce `V _ _ _ σ hn`. Distinguish the cases in `h0 : n = 0`.

Substitute `h0 haveI : Subsingleton V := Module.finrank_zero_iff.mp hn` using the available equality. Use `⟨[], by simp, fun g => ?_⟩` and prove the remaining obligations. Establish `hz : σ g = 0` using `LinearMap.ext fun v => Subsingleton.elim _ _`. Use `show LinearMap.trace L V (σ g) = _`. Rewrite using `[hz, map_zero]`.

Simplify using the standard rewrite rules. Distinguish the cases in `hirr : σ.IsIrreducible`. Set `e : V ≃ₗ[L] (Fin n → L)` to `LinearEquiv.ofFinrankEq V (Fin n → L) (by rw [hn, Module.finrank_fin_fun])`. Use `⟨[⟨n, transportRep e σ⟩], ?_, fun g => ?_⟩` and prove the remaining obligations. Introduce `x hx`.

Rewrite `hx` using `[List.mem_singleton]`. Substitute `hx` using the available equality. Conclude with `transportRep_irreducible e σ hirr`. Simplify using `only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]`. Conclude with `(transportRep_character e σ g).symm`.

Use `haveI hV : Nontrivial V := by`. Assume the negation of the conclusion as `hnt`. Rewrite `hnt` using `[not_nontrivial_iff_subsingleton]`. Use `(Module.finrank_zero_iff (R := L)).mpr hnt` as an intermediate fact. Use linear arithmetic over natural numbers and integers.

Establish `hbt : (⊥ : Subrepresentation σ) ≠ ⊤` using `fun h => by`. Establish `h2 : (⊥ : Submodule L V) = ⊤` using `congrArg Subrepresentation.toSubmodule h`. Conclude with `bot_ne_top h2`. Choose the witnesses or unpack the hypotheses as in `⟨W, hW0, hWT⟩ : ∃ W : Subrepresentation σ, W ≠ ⊥ ∧ W ≠ ⊤ := by`. Assume the negation of the conclusion as `hcon`.

Use `push_neg at hcon`. Conclude with `hirr (show IsSimpleOrder (Subrepresentation σ) from { toNontrivial := ⟨⟨⊥, ⊤, hbt⟩⟩ eq_bot_or_eq_top := fun W => by`. Distinguish the cases in `hW : W = ⊥`. Conclude with `Or.inl hW`. Conclude with `Or.inr (hcon W hW) })`.

Take `⟨C, hc⟩` from `subrepresentation_exists_isCompl_subrepresentation σ W`. Establish `hsum` using `Submodule.finrank_add_eq_of_isCompl hc`. Establish `hW0' : W.toSubmodule ≠ ⊥` using `fun h => hW0 (Subrepresentation.ext h)`. Establish `hC0' : C.toSubmodule ≠ ⊥` using `fun h => hWT (Subrepresentation.ext (by`. Use `hc.sup_eq_top` as an intermediate fact.

Rewrite `this` using `[h, sup_bot_eq]`. Conclude with `this))`. Establish `hWpos : Module.finrank L W.toSubmodule ≠ 0` using `fun h => hW0' (Submodule.finrank_eq_zero.mp h)`. Establish `hCpos : Module.finrank L C.toSubmodule ≠ 0` using `fun h => hC0' (Submodule.finrank_eq_zero.mp h)`. Take `⟨lW, hlW, hchW⟩` from `ih (Module.finrank L W.toSubmodule) (by omega) W.toSubmodule W.toRepresentation rfl`.

Take `⟨lC, hlC, hchC⟩` from `ih (Module.finrank L C.toSubmodule) (by omega) C.toSubmodule C.toRepresentation rfl`. Use `⟨lW ++ lC, fun x hx => ?_, fun g => ?_⟩` and prove the remaining obligations. Break down `List.mem_append.mp hx with h | h` into its components or cases. Conclude with `hlW x h`. Conclude with `hlC x h`.

Rewrite using `[character_eq_add σ W C hc g, hchW g, hchC g, List.map_append, List.sum_append]`.
-/
theorem hasIrreducibleDecomposition_of_finrank_eq : ∀ (n : ℕ) (V : Type) [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (σ : Representation L G V), Module.finrank L V = n → ListDecomp σ := by
  intro n
  induction n using Nat.strong_induction_on with
  | _ n ih =>
  intro V _ _ _ σ hn
  by_cases h0 : n = 0
  · subst h0
    haveI : Subsingleton V := Module.finrank_zero_iff.mp hn
    refine ⟨[], by simp, fun g => ?_⟩
    have hz : σ g = 0 := LinearMap.ext fun v => Subsingleton.elim _ _
    show LinearMap.trace L V (σ g) = _
    rw [hz, map_zero]
    simp
  by_cases hirr : σ.IsIrreducible
  · let e : V ≃ₗ[L] (Fin n → L) :=
      LinearEquiv.ofFinrankEq V (Fin n → L) (by rw [hn, Module.finrank_fin_fun])
    refine ⟨[⟨n, transportRep e σ⟩], ?_, fun g => ?_⟩
    · intro x hx
      rw [List.mem_singleton] at hx
      subst hx
      exact transportRep_irreducible e σ hirr
    · simp only [List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
      exact (transportRep_character e σ g).symm
  haveI hV : Nontrivial V := by
    by_contra hnt
    rw [not_nontrivial_iff_subsingleton] at hnt
    have := (Module.finrank_zero_iff (R := L)).mpr hnt
    omega
  have hbt : (⊥ : Subrepresentation σ) ≠ ⊤ := fun h => by
    have h2 : (⊥ : Submodule L V) = ⊤ := congrArg Subrepresentation.toSubmodule h
    exact bot_ne_top h2
  obtain ⟨W, hW0, hWT⟩ : ∃ W : Subrepresentation σ, W ≠ ⊥ ∧ W ≠ ⊤ := by
    by_contra hcon
    push_neg at hcon
    exact hirr (show IsSimpleOrder (Subrepresentation σ) from
      { toNontrivial := ⟨⟨⊥, ⊤, hbt⟩⟩
        eq_bot_or_eq_top := fun W => by
          by_cases hW : W = ⊥
          · exact Or.inl hW
          · exact Or.inr (hcon W hW) })
  obtain ⟨C, hc⟩ := subrepresentation_exists_isCompl_subrepresentation σ W
  have hsum := Submodule.finrank_add_eq_of_isCompl hc
  have hW0' : W.toSubmodule ≠ ⊥ := fun h => hW0 (Subrepresentation.ext h)
  have hC0' : C.toSubmodule ≠ ⊥ := fun h => hWT (Subrepresentation.ext (by
    have := hc.sup_eq_top
    rw [h, sup_bot_eq] at this
    exact this))
  have hWpos : Module.finrank L W.toSubmodule ≠ 0 := fun h => hW0' (Submodule.finrank_eq_zero.mp h)
  have hCpos : Module.finrank L C.toSubmodule ≠ 0 := fun h => hC0' (Submodule.finrank_eq_zero.mp h)
  obtain ⟨lW, hlW, hchW⟩ :=
    ih (Module.finrank L W.toSubmodule) (by omega) W.toSubmodule W.toRepresentation rfl
  obtain ⟨lC, hlC, hchC⟩ :=
    ih (Module.finrank L C.toSubmodule) (by omega) C.toSubmodule C.toRepresentation rfl
  refine ⟨lW ++ lC, fun x hx => ?_, fun g => ?_⟩
  · rcases List.mem_append.mp hx with h | h
    · exact hlW x h
    · exact hlC x h
  · rw [character_eq_add σ W C hc g, hchW g, hchC g, List.map_append, List.sum_append]

/- English proof (translation)
Proceed by induction on `l with`. Consider the case `nil => simp`. Consider the case `cons a l ih`. Rewrite using `[List.map_cons, List.sum_cons, ← ih]`. Use `show ∑ i : Fin (l.length + 1), f ((a :: l).get i) = _`.

Rewrite using `[Fin.sum_univ_succ]`. Both sides reduce to the same expression.
-/
private theorem sum_fin_length_get_eq_map_sum {M : Type} [AddCommMonoid M] {α : Type} (l : List α) (f : α → M) :
    ∑ i : Fin l.length, f (l.get i) = (l.map f).sum := by
  induction l with
  | nil => simp
  | cons a l ih =>
    rw [List.map_cons, List.sum_cons, ← ih]
    show ∑ i : Fin (l.length + 1), f ((a :: l).get i) = _
    rw [Fin.sum_univ_succ]
    rfl

/- English proof (translation)
Take `⟨l, hl, hch⟩` from `hasIrreducibleDecomposition_of_finrank_eq _ V σ rfl`. Use `⟨l.length, fun i => (l.get i).1, fun i => (l.get i).2, fun i => hl _ (by simp), fun g => ?_⟩` and prove the remaining obligations. Rewrite using `[hch g]`. Conclude with `(sum_fin_length_get_eq_map_sum l (fun x => x.2.character g)).symm`.
-/
theorem char_eq_sum_irreducible {V : Type} [AddCommGroup V] [Module L V] [FiniteDimensional L V]
    (σ : Representation L G V) :
    ∃ (r : ℕ) (d : Fin r → ℕ) (τ : (i : Fin r) → Representation L G (Fin (d i) → L)),
      (∀ i, (τ i).IsIrreducible) ∧ ∀ g : G, σ.character g = ∑ i, (τ i).character g := by
  obtain ⟨l, hl, hch⟩ := hasIrreducibleDecomposition_of_finrank_eq _ V σ rfl
  refine ⟨l.length, fun i => (l.get i).1, fun i => (l.get i).2, fun i => hl _ (by simp), fun g => ?_⟩
  rw [hch g]
  exact (sum_fin_length_get_eq_map_sum l (fun x => x.2.character g)).symm

end

end CycSplitWork
